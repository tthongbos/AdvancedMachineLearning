"""Object detection pipeline for the Chess Pieces dataset."""

from __future__ import annotations

# Dùng argparse để nhận command line như prepare, figures, yolo, detr, fasterrcnn.
import argparse
# Dùng json để ghi thống kê và dữ liệu COCO ra file.
import json
# Dùng time để đo thời gian train của Faster R-CNN.
import time
# Dùng dataclass để mô tả một bounding box gọn hơn.
from dataclasses import dataclass
# Dùng Path để xử lý đường dẫn theo kiểu độc lập hệ điều hành.
from pathlib import Path
# Dùng Iterable để chú thích kiểu dữ liệu cho danh sách box.
from typing import Iterable

# Dùng OpenCV để đọc ảnh và vẽ bounding box.
import cv2
# Dùng matplotlib để vẽ biểu đồ và lưu ảnh ra file.
import matplotlib

# Chọn backend không cần giao diện để chạy được trên Kaggle/Colab.
matplotlib.use("Agg")
# Import pyplot sau khi set backend.
import matplotlib.pyplot as plt
# Dùng numpy cho các phép toán mảng và thống kê.
import numpy as np
# Dùng PIL để lấy kích thước ảnh khi xuất COCO.
from PIL import Image


# Ba split chuẩn của dataset.
SPLITS = ("train", "valid", "test")


@dataclass
class BoxRecord:
    """One object annotation in absolute pixel coordinates."""

    image_name: str
    x1: float
    y1: float
    x2: float
    y2: float
    class_id: int


def find_dataset_root(start: Path, dataset_name: str = "416x416_aug_chess_pieces") -> Path:
    """Search upward from the current file until the dataset directory is found."""

    # Duyệt thư mục hiện tại và toàn bộ thư mục cha.
    for parent in [start.resolve(), *start.resolve().parents]:
        # Ghép tên dataset vào từng thư mục đang xét.
        candidate = parent / dataset_name
        # Nếu thư mục tồn tại thì trả về ngay.
        if candidate.exists():
            return candidate
    # Nếu không thấy dataset thì báo lỗi rõ ràng.
    raise FileNotFoundError(f"Cannot find {dataset_name}; pass --dataset explicitly.")


def read_classes(dataset_root: Path) -> list[str]:
    """Read the class list exported by Roboflow."""

    # File _classes.txt nằm trong split train.
    classes_path = dataset_root / "train" / "_classes.txt"
    # Đọc từng dòng, bỏ dòng trống và trả về danh sách tên lớp.
    return [line.strip() for line in classes_path.read_text(encoding="utf-8").splitlines() if line.strip()]


def parse_annotation_line(line: str) -> tuple[str, list[BoxRecord]]:
    """Parse one Roboflow annotation row: image_name x1,y1,x2,y2,class ..."""

    # Tách một dòng annotation thành các phần.
    parts = line.strip().split()
    # Phần đầu là tên ảnh.
    image_name = parts[0]
    # Tạo danh sách box cho ảnh hiện tại.
    records: list[BoxRecord] = []
    # Duyệt từng box dạng x1,y1,x2,y2,class_id.
    for item in parts[1:]:
        # Tách chuỗi thành tọa độ và id lớp.
        x1, y1, x2, y2, class_id = item.split(",")
        # Chuyển sang kiểu số và lưu lại.
        records.append(BoxRecord(image_name, float(x1), float(y1), float(x2), float(y2), int(class_id)))
    # Trả về tên ảnh và danh sách box của ảnh đó.
    return image_name, records


def load_split_annotations(dataset_root: Path, split: str) -> dict[str, list[BoxRecord]]:
    """Load all annotations for one split into a dictionary keyed by image name."""

    # Đường dẫn đến file annotation của split hiện tại.
    annotation_path = dataset_root / split / "_annotations.txt"
    # Tạo dictionary rỗng để lưu box theo tên ảnh.
    annotations: dict[str, list[BoxRecord]] = {}
    # Đọc file theo từng dòng.
    for line in annotation_path.read_text(encoding="utf-8").splitlines():
        # Bỏ qua dòng trống.
        if line.strip():
            # Parse dòng hiện tại thành tên ảnh và box.
            image_name, records = parse_annotation_line(line)
            # Gán danh sách box vào dictionary.
            annotations[image_name] = records
    # Trả về toàn bộ annotation của split.
    return annotations


def dataset_stats(dataset_root: Path) -> dict:
    """Collect image and object counts."""

    # Đọc danh sách lớp để thống kê theo class.
    classes = read_classes(dataset_root)
    # Tạo khung dữ liệu thống kê tổng.
    stats = {"classes": classes, "splits": {}, "total_images": 0, "total_boxes": 0}
    # Duyệt từng split train/valid/test.
    for split in SPLITS:
        # Tải annotation của split hiện tại.
        annotations = load_split_annotations(dataset_root, split)
        # Khởi tạo bộ đếm theo từng lớp.
        class_counts = {name: 0 for name in classes}
        # Biến đếm số box của split.
        box_count = 0
        # Duyệt toàn bộ ảnh trong annotation.
        for records in annotations.values():
            # Duyệt từng box trong ảnh.
            for record in records:
                # Tăng số lượng của lớp tương ứng.
                class_counts[classes[record.class_id]] += 1
                # Tăng tổng số box.
                box_count += 1
        # Lưu thống kê của split hiện tại.
        stats["splits"][split] = {
            "images": len(list((dataset_root / split).glob("*.jpg"))),
            "annotated_images": len(annotations),
            "boxes": box_count,
            "class_counts": class_counts,
        }
        # Cộng dồn số ảnh vào tổng toàn dataset.
        stats["total_images"] += stats["splits"][split]["images"]
        # Cộng dồn số box vào tổng toàn dataset.
        stats["total_boxes"] += box_count
    # Trả về thống kê cuối cùng.
    return stats


def convert_to_yolo(dataset_root: Path, output_root: Path) -> Path:
    """Convert absolute boxes to YOLO txt labels and write data.yaml."""

    # Đọc tên lớp để ghi vào data.yaml.
    classes = read_classes(dataset_root)
    # Tạo thư mục gốc cho dữ liệu YOLO.
    yolo_root = output_root / "chess_yolo"
    # Chuyển từng split sang cấu trúc YOLO.
    for split in SPLITS:
        # Thư mục ảnh YOLO.
        image_out = yolo_root / "images" / split
        # Thư mục nhãn YOLO.
        label_out = yolo_root / "labels" / split
        # Tạo thư mục ảnh nếu chưa có.
        image_out.mkdir(parents=True, exist_ok=True)
        # Tạo thư mục nhãn nếu chưa có.
        label_out.mkdir(parents=True, exist_ok=True)
        # Tải annotation gốc của split.
        annotations = load_split_annotations(dataset_root, split)
        # Duyệt từng ảnh jpg trong split.
        for image_path in (dataset_root / split).glob("*.jpg"):
            # Đọc ảnh để lấy kích thước thật.
            image = cv2.imread(str(image_path))
            # Tách chiều cao và chiều rộng ảnh.
            height, width = image.shape[:2]
            # Copy ảnh sang thư mục YOLO để giữ nguyên dữ liệu gốc.
            (image_out / image_path.name).write_bytes(image_path.read_bytes())
            # Danh sách dòng label YOLO cho ảnh hiện tại.
            rows = []
            # Lấy các box của ảnh, nếu không có thì dùng danh sách rỗng.
            for record in annotations.get(image_path.name, []):
                # Tính tâm box theo trục x.
                cx = ((record.x1 + record.x2) / 2.0) / width
                # Tính tâm box theo trục y.
                cy = ((record.y1 + record.y2) / 2.0) / height
                # Tính chiều rộng box đã chuẩn hóa.
                bw = (record.x2 - record.x1) / width
                # Tính chiều cao box đã chuẩn hóa.
                bh = (record.y2 - record.y1) / height
                # Ghi một dòng theo chuẩn YOLO: class cx cy w h.
                rows.append(f"{record.class_id} {cx:.6f} {cy:.6f} {bw:.6f} {bh:.6f}")
            # Ghi file txt cùng tên với ảnh.
            (label_out / f"{image_path.stem}.txt").write_text("\n".join(rows), encoding="utf-8")
    # Tạo nội dung file data.yaml.
    yaml_text = [
        f"path: {yolo_root.resolve()}",
        "train: images/train",
        "val: images/valid",
        "test: images/test",
        f"nc: {len(classes)}",
        "names:",
        *[f"  {idx}: {name}" for idx, name in enumerate(classes)],
        "",
    ]
    # Đường dẫn file data.yaml.
    data_yaml = yolo_root / "data.yaml"
    # Ghi file cấu hình YOLO ra đĩa.
    data_yaml.write_text("\n".join(yaml_text), encoding="utf-8")
    # Trả về đường dẫn để bước train dùng tiếp.
    return data_yaml


def convert_to_coco(dataset_root: Path, output_root: Path) -> Path:
    """Convert the dataset to COCO json files used by DETR and Faster R-CNN."""

    # Đọc danh sách lớp để tạo category.
    classes = read_classes(dataset_root)
    # Tạo thư mục chứa các file COCO json.
    coco_root = output_root / "chess_coco"
    # Tạo thư mục nếu chưa có.
    coco_root.mkdir(parents=True, exist_ok=True)
    # Duyệt từng split.
    for split in SPLITS:
        # Tải annotation theo từng ảnh.
        annotations_by_image = load_split_annotations(dataset_root, split)
        # Danh sách ảnh theo chuẩn COCO.
        images = []
        # Danh sách annotation theo chuẩn COCO.
        annotations = []
        # Id của annotation, bắt đầu từ 1.
        annotation_id = 1
        # Duyệt từng ảnh và gán id tăng dần.
        for image_id, image_path in enumerate(sorted((dataset_root / split).glob("*.jpg")), start=1):
            # Mở ảnh để lấy kích thước.
            with Image.open(image_path) as image:
                width, height = image.size
            # Thêm metadata ảnh vào danh sách images.
            images.append({"id": image_id, "file_name": image_path.name, "width": width, "height": height})
            # Duyệt từng box của ảnh hiện tại.
            for record in annotations_by_image.get(image_path.name, []):
                # Tính chiều rộng box.
                width_box = record.x2 - record.x1
                # Tính chiều cao box.
                height_box = record.y2 - record.y1
                # Thêm một annotation theo schema COCO.
                annotations.append(
                    {
                        "id": annotation_id,
                        "image_id": image_id,
                        "category_id": record.class_id + 1,
                        "bbox": [record.x1, record.y1, width_box, height_box],
                        "area": width_box * height_box,
                        "iscrowd": 0,
                    }
                )
                # Tăng id để annotation tiếp theo không bị trùng.
                annotation_id += 1
        # Tạo danh sách category.
        categories = [{"id": idx + 1, "name": name} for idx, name in enumerate(classes)]
        # Ghép images, annotations, categories thành payload COCO.
        payload = {"images": images, "annotations": annotations, "categories": categories}
        # Ghi file json cho split hiện tại.
        (coco_root / f"{split}.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    # Trả về thư mục COCO để bước sau dùng tiếp.
    return coco_root


def draw_boxes(image: np.ndarray, boxes: Iterable[BoxRecord], classes: list[str]) -> np.ndarray:
    """Draw annotated bounding boxes on one image."""

    # Tạo bản sao ảnh để không làm thay đổi ảnh gốc.
    output = image.copy()
    # Duyệt từng box cần vẽ.
    for record in boxes:
        # Chọn màu xanh lá cho bounding box.
        color = (30, 180, 60)
        # Vẽ hình chữ nhật từ góc trái trên đến góc phải dưới.
        cv2.rectangle(output, (int(record.x1), int(record.y1)), (int(record.x2), int(record.y2)), color, 2)
        # Ghi tên lớp phía trên box.
        cv2.putText(output, classes[record.class_id], (int(record.x1), max(15, int(record.y1) - 6)), cv2.FONT_HERSHEY_SIMPLEX, 0.45, color, 1)
    # Trả về ảnh đã vẽ box.
    return output


def select_preview_image(dataset_root: Path) -> Path:
    """Pick one image to visualize model predictions."""

    # Ưu tiên ảnh test để minh họa kết quả tổng quát hơn.
    for split in ("test", "valid", "train"):
        # Lấy toàn bộ ảnh trong split hiện tại.
        images = sorted((dataset_root / split).glob("*.jpg"))
        # Nếu split có ảnh thì dùng ảnh đầu tiên.
        if images:
            return images[0]
    # Nếu không có ảnh nào thì báo lỗi để người dùng kiểm tra lại dataset.
    raise FileNotFoundError("No preview image found in train/valid/test splits.")


def save_prediction_image(image_path: Path, boxes: np.ndarray, labels: list[str], scores: list[float], output_path: Path) -> None:
    """Save one prediction visualization to disk."""

    # Đọc ảnh gốc bằng OpenCV.
    image = cv2.imread(str(image_path))
    # Nếu ảnh không đọc được thì dừng sớm.
    if image is None:
        raise FileNotFoundError(f"Cannot read image: {image_path}")
    # Tạo bản sao ảnh để vẽ prediction.
    canvas = image.copy()
    # Duyệt từng box, nhãn và độ tin cậy.
    for box, label, score in zip(boxes, labels, scores):
        # Tách tọa độ hộp dự đoán.
        x1, y1, x2, y2 = map(int, box)
        # Chọn màu xanh dương cho prediction.
        color = (255, 120, 40)
        # Vẽ bounding box lên ảnh.
        cv2.rectangle(canvas, (x1, y1), (x2, y2), color, 2)
        # Ghi nhãn và confidence lên trên box.
        caption = f"{label} {score:.2f}" if score is not None else label
        cv2.putText(canvas, caption, (x1, max(15, y1 - 6)), cv2.FONT_HERSHEY_SIMPLEX, 0.45, color, 1)
    # Tạo thư mục đích nếu chưa có.
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Ghi ảnh prediction ra file.
    cv2.imwrite(str(output_path), canvas)


def export_yolo_prediction(model, dataset_root: Path, figures_dir: Path) -> None:
    """Export one YOLO prediction image after training."""

    # Chọn một ảnh minh họa từ dataset.
    image_path = select_preview_image(dataset_root)
    # Chạy suy luận trên ảnh đã chọn.
    result = model.predict(source=str(image_path), conf=0.25, verbose=False)[0]
    # Dùng ảnh đã annotate sẵn của Ultralytics.
    annotated = result.plot()
    # Lưu ảnh kết quả vào thư mục figures.
    figures_dir.mkdir(parents=True, exist_ok=True)
    cv2.imwrite(str(figures_dir / "yolo_prediction.png"), annotated)


def export_torchvision_prediction(
    model,
    dataset_root: Path,
    figures_dir: Path,
    classes: list[str],
    output_name: str,
    score_threshold: float = 0.5,
) -> None:
    """Export one prediction image for TorchVision-based detectors."""

    # Chọn ảnh minh họa từ dataset.
    image_path = select_preview_image(dataset_root)
    # Mở ảnh dưới dạng RGB.
    image = Image.open(image_path).convert("RGB")
    # Chuyển ảnh sang tensor CxHxW trong khoảng 0..1.
    image_tensor = np.array(image)
    # Chuyển ảnh sang tensor kiểu float để model nhận đầu vào.
    import torch

    tensor = torch.as_tensor(image_tensor, dtype=torch.float32).permute(2, 0, 1) / 255.0
    # Suy luận trên một ảnh duy nhất.
    model.eval()
    with torch.no_grad():
        outputs = model([tensor.to(next(model.parameters()).device)])[0]
    # Lọc các dự đoán có confidence đủ cao.
    scores = outputs["scores"].detach().cpu()
    keep = scores >= score_threshold
    # Lấy box của các dự đoán được giữ lại.
    boxes = outputs["boxes"].detach().cpu().numpy()[keep.numpy()]
    # Lấy id lớp của các dự đoán được giữ lại.
    label_ids = outputs["labels"].detach().cpu().numpy()[keep.numpy()]
    # Chuyển id lớp thành tên lớp.
    labels = [classes[int(label_id) - 1] for label_id in label_ids]
    # Chuyển scores sang list Python.
    kept_scores = scores[keep].tolist()
    # Lưu hình dự đoán ra file.
    save_prediction_image(image_path, boxes, labels, kept_scores, figures_dir / output_name)


def make_figures(dataset_root: Path, figures_dir: Path) -> None:
    """Generate summary figures."""

    # Tạo thư mục lưu hình nếu chưa có.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Lấy thống kê toàn bộ dataset.
    stats = dataset_stats(dataset_root)
    # Lấy danh sách tên lớp.
    classes = stats["classes"]
    # Lấy tên ảnh đầu tiên của train để minh họa.
    first_image_name = next(iter(load_split_annotations(dataset_root, "train")))
    # Tải annotation của train.
    train_annotations = load_split_annotations(dataset_root, "train")
    # Đọc ảnh minh họa.
    image = cv2.imread(str(dataset_root / "train" / first_image_name))
    # Vẽ box ground-truth lên ảnh.
    labeled = draw_boxes(image, train_annotations[first_image_name], classes)
    # Lưu ảnh minh họa.
    cv2.imwrite(str(figures_dir / "sample_ground_truth.png"), labeled)

    # Lấy tên các split.
    split_names = list(stats["splits"].keys())
    # Lấy số ảnh của từng split.
    image_counts = [stats["splits"][split]["images"] for split in split_names]
    # Lấy số box của từng split.
    box_counts = [stats["splits"][split]["boxes"] for split in split_names]
    # Tạo figure cho biểu đồ split.
    plt.figure(figsize=(7, 4))
    # Tạo vị trí cột trên trục x.
    x_positions = np.arange(len(split_names))
    # Vẽ cột số ảnh.
    plt.bar(x_positions - 0.18, image_counts, width=0.36, label="Images")
    # Vẽ cột số box.
    plt.bar(x_positions + 0.18, box_counts, width=0.36, label="Boxes")
    # Gắn nhãn cho từng split.
    plt.xticks(x_positions, split_names)
    # Gắn nhãn trục y.
    plt.ylabel("Count")
    # Gắn tiêu đề biểu đồ.
    plt.title("Chess Pieces split distribution")
    # Hiển thị chú giải.
    plt.legend()
    # Tối ưu layout.
    plt.tight_layout()
    # Lưu biểu đồ split.
    plt.savefig(figures_dir / "split_distribution.png", dpi=160)
    # Đóng figure để giải phóng bộ nhớ.
    plt.close()

    # Tạo vector đếm tổng số box theo lớp.
    total_per_class = np.zeros(len(classes), dtype=int)
    # Cộng dồn box từ từng split.
    for split in SPLITS:
        # Lấy thống kê class của split.
        counts = stats["splits"][split]["class_counts"]
        # Cộng dồn theo đúng thứ tự class.
        total_per_class += np.array([counts[name] for name in classes])
    # Tạo figure cho phân bố lớp.
    plt.figure(figsize=(10, 5))
    # Vẽ biểu đồ cột theo tên lớp.
    plt.bar(classes, total_per_class)
    # Xoay nhãn lớp cho dễ đọc.
    plt.xticks(rotation=55, ha="right")
    # Gắn nhãn trục y.
    plt.ylabel("Bounding boxes")
    # Gắn tiêu đề biểu đồ.
    plt.title("Class distribution")
    # Tối ưu layout.
    plt.tight_layout()
    # Lưu biểu đồ phân bố lớp.
    plt.savefig(figures_dir / "class_distribution.png", dpi=160)
    # Đóng figure.
    plt.close()

    # Ghi thống kê ra JSON để kiểm tra lại sau này.
    (figures_dir / "dataset_stats.json").write_text(json.dumps(stats, indent=2), encoding="utf-8")


class ChessCocoDataset:
    """Minimal PyTorch dataset for Faster R-CNN training."""

    def __init__(self, dataset_root: Path, split: str):
        # Lưu đường dẫn dataset gốc.
        self.dataset_root = dataset_root
        # Lưu tên split hiện tại.
        self.split = split
        # Lấy danh sách ảnh jpg của split.
        self.images = sorted((dataset_root / split).glob("*.jpg"))
        # Tải annotation của split.
        self.annotations = load_split_annotations(dataset_root, split)

    def __len__(self) -> int:
        # Trả về số ảnh để DataLoader biết độ dài dataset.
        return len(self.images)

    def __getitem__(self, index: int):
        # Import torch ở đây để các bước chỉ prepare/figures không bắt buộc torch runtime.
        import torch
        # Lấy đường dẫn ảnh theo index.
        image_path = self.images[index]
        # Mở ảnh và chuyển sang RGB.
        image = Image.open(image_path).convert("RGB")
        # Chuyển ảnh thành tensor CxHxW và chuẩn hóa về 0..1.
        image_tensor = torch.as_tensor(np.array(image), dtype=torch.float32).permute(2, 0, 1) / 255.0
        # Lấy annotation của ảnh hiện tại.
        records = self.annotations.get(image_path.name, [])
        # Chuyển box sang tensor [x1, y1, x2, y2].
        boxes = torch.as_tensor([[r.x1, r.y1, r.x2, r.y2] for r in records], dtype=torch.float32)
        # Chuyển nhãn sang tensor và cộng 1 để background là 0.
        labels = torch.as_tensor([r.class_id + 1 for r in records], dtype=torch.int64)
        # Tạo target dictionary đúng format TorchVision.
        target = {"boxes": boxes, "labels": labels, "image_id": torch.tensor([index])}
        # Trả về một mẫu ảnh và nhãn.
        return image_tensor, target


def collate_detection_batch(batch):
    """Keep images and targets as lists because each image has a different object count."""

    # Detection model cần list ảnh và list target thay vì stack thành tensor.
    return tuple(zip(*batch))


def train_yolo(data_yaml: Path, epochs: int, imgsz: int, project: Path, figures_dir: Path, dataset_root: Path) -> None:
    """Fine-tune a pretrained YOLOv8 nano model."""

    # Import YOLO chỉ khi thật sự train để tránh bắt buộc khi chạy prepare/figures.
    from ultralytics import YOLO

    # Tải mô hình YOLOv8n pretrained.
    model = YOLO("yolov8n.pt")
    # Train YOLO với file data.yaml đã convert.
    model.train(data=str(data_yaml), epochs=epochs, imgsz=imgsz, project=str(project), name="yolo_chess", pretrained=True)
    # Đánh giá mô hình trên test split.
    metrics = model.val(data=str(data_yaml), split="test", imgsz=imgsz)
    # Ghi metrics thô ra file để xem lại nhanh.
    (project / "yolo_metrics.txt").write_text(str(metrics), encoding="utf-8")
    # Xuất một ảnh prediction để dùng trong báo cáo.
    export_yolo_prediction(model, dataset_root, figures_dir)


def train_faster_rcnn(dataset_root: Path, epochs: int, batch_size: int, output_dir: Path, figures_dir: Path) -> None:
    """Fine-tune Faster R-CNN with a ResNet-50 FPN backbone."""

    # Import torch khi bước train này được gọi.
    import torch
    # Import DataLoader để tạo batch dữ liệu.
    from torch.utils.data import DataLoader
    # Import model pretrained và backbone weights.
    from torchvision.models.detection import FasterRCNN_ResNet50_FPN_Weights, fasterrcnn_resnet50_fpn
    # Import predictor để thay head phân loại theo số lớp của dataset.
    from torchvision.models.detection.faster_rcnn import FastRCNNPredictor

    # Chọn GPU nếu có, nếu không dùng CPU.
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    # Đọc danh sách lớp.
    classes = read_classes(dataset_root)
    # Tải mô hình Faster R-CNN pretrained trên COCO.
    model = fasterrcnn_resnet50_fpn(weights=FasterRCNN_ResNet50_FPN_Weights.DEFAULT)
    # Lấy số feature đầu vào của classifier hiện tại.
    in_features = model.roi_heads.box_predictor.cls_score.in_features
    # Thay classifier để khớp với số lớp của dataset.
    model.roi_heads.box_predictor = FastRCNNPredictor(in_features, len(classes) + 1)
    # Đưa mô hình lên device.
    model.to(device)
    # Tạo DataLoader cho tập train.
    train_loader = DataLoader(ChessCocoDataset(dataset_root, "train"), batch_size=batch_size, shuffle=True, collate_fn=collate_detection_batch)
    # Dùng AdamW để fine-tune backbone ổn định hơn.
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-4, weight_decay=1e-4)
    # Tạo thư mục lưu checkpoint.
    output_dir.mkdir(parents=True, exist_ok=True)

    # Lặp qua từng epoch.
    for epoch in range(epochs):
        # Chuyển mô hình sang chế độ train.
        model.train()
        # Biến cộng dồn loss của epoch.
        running_loss = 0.0
        # Ghi thời điểm bắt đầu epoch.
        start = time.perf_counter()
        # Duyệt từng batch ảnh và target.
        for images, targets in train_loader:
            # Đưa từng ảnh lên device.
            images = [image.to(device) for image in images]
            # Đưa từng target tensor lên device.
            targets = [{key: value.to(device) for key, value in target.items()} for target in targets]
            # TorchVision trả về dict loss khi có target.
            losses = model(images, targets)
            # Cộng tất cả loss thành một scalar.
            loss = sum(value for value in losses.values())
            # Xóa gradient cũ.
            optimizer.zero_grad()
            # Lan truyền ngược.
            loss.backward()
            # Cập nhật trọng số.
            optimizer.step()
            # Cộng loss batch vào running loss.
            running_loss += float(loss.detach().cpu())
        # Tính thời gian chạy của epoch.
        elapsed = time.perf_counter() - start
        # In log để theo dõi quá trình train.
        print(f"epoch={epoch + 1} loss={running_loss / max(1, len(train_loader)):.4f} time={elapsed:.1f}s")
    # Lưu weight cuối cùng.
    torch.save(model.state_dict(), output_dir / "faster_rcnn_chess.pth")
    # Xuất một ảnh prediction để dùng trong báo cáo.
    export_torchvision_prediction(model, dataset_root, figures_dir, classes, "faster_rcnn_prediction.png")


def train_detr(dataset_root: Path, epochs: int, batch_size: int, output_dir: Path, figures_dir: Path) -> None:
    """Fine-tune DETR using Hugging Face Transformers."""

    # Import torch trong bước train này.
    import torch
    # Import Dataset để định nghĩa dataset lồng bên trong.
    from torch.utils.data import Dataset
    # Import model, processor và Trainer của Hugging Face.
    from transformers import DetrForObjectDetection, DetrImageProcessor, Trainer, TrainingArguments

    # Đọc danh sách lớp.
    classes = read_classes(dataset_root)
    # Tạo mapping id -> label, bắt đầu từ 1.
    id2label = {idx + 1: name for idx, name in enumerate(classes)}
    # Tạo mapping ngược label -> id.
    label2id = {name: idx for idx, name in id2label.items()}
    # Tải processor pretrained để encode ảnh và annotation.
    processor = DetrImageProcessor.from_pretrained("facebook/detr-resnet-50")

    class DetrChessDataset(Dataset):
        def __init__(self, split: str):
            # Lấy danh sách ảnh của split.
            self.images = sorted((dataset_root / split).glob("*.jpg"))
            # Tải annotation của split.
            self.annotations = load_split_annotations(dataset_root, split)

        def __len__(self) -> int:
            # Trả về số ảnh trong split.
            return len(self.images)

        def __getitem__(self, index: int):
            # Lấy ảnh theo index.
            image_path = self.images[index]
            # Mở ảnh RGB.
            image = Image.open(image_path).convert("RGB")
            # Lấy annotation của ảnh hiện tại.
            records = self.annotations.get(image_path.name, [])
            # Tạo target theo format COCO mà DETR cần.
            target = {
                "image_id": index,
                "annotations": [
                    {
                        "category_id": record.class_id + 1,
                        "bbox": [record.x1, record.y1, record.x2 - record.x1, record.y2 - record.y1],
                        "area": (record.x2 - record.x1) * (record.y2 - record.y1),
                        "iscrowd": 0,
                    }
                    for record in records
                ],
            }
            # Encode ảnh và annotation thành tensor cho DETR.
            encoded = processor(images=image, annotations=target, return_tensors="pt")
            # Bỏ chiều batch vì mỗi sample chỉ là một ảnh.
            return {"pixel_values": encoded["pixel_values"].squeeze(0), "labels": encoded["labels"][0]}

    def collate_fn(batch):
        # Lấy tensor pixel_values của từng sample.
        pixel_values = [item["pixel_values"] for item in batch]
        # Pad ảnh để cùng kích thước.
        encoding = processor.pad(pixel_values, return_tensors="pt")
        # Labels giữ dạng list vì số object mỗi ảnh khác nhau.
        labels = [item["labels"] for item in batch]
        # Trả về đúng format cho Trainer.
        return {"pixel_values": encoding["pixel_values"], "pixel_mask": encoding["pixel_mask"], "labels": labels}

    # Tải DETR pretrained và thay số lớp đầu ra.
    model = DetrForObjectDetection.from_pretrained(
        "facebook/detr-resnet-50",
        num_labels=len(classes) + 1,
        id2label=id2label,
        label2id=label2id,
        ignore_mismatched_sizes=True,
    )
    # Cấu hình train cho Hugging Face Trainer.
    args = TrainingArguments(
        output_dir=str(output_dir),
        per_device_train_batch_size=batch_size,
        per_device_eval_batch_size=batch_size,
        num_train_epochs=epochs,
        learning_rate=1e-4,
        weight_decay=1e-4,
        logging_steps=10,
        eval_strategy="epoch",
        save_strategy="epoch",
        remove_unused_columns=False,
        fp16=torch.cuda.is_available(),
    )
    # Tạo Trainer với train/valid dataset và collate_fn riêng.
    trainer = Trainer(
        model=model,
        args=args,
        train_dataset=DetrChessDataset("train"),
        eval_dataset=DetrChessDataset("valid"),
        data_collator=collate_fn,
        processing_class=processor,
    )
    # Bắt đầu fine-tune DETR.
    trainer.train()
    # Xuất một ảnh prediction để dùng trong báo cáo.
    image_path = select_preview_image(dataset_root)
    image = Image.open(image_path).convert("RGB")
    device = next(model.parameters()).device
    inputs = processor(images=image, return_tensors="pt").to(device)
    with torch.no_grad():
        outputs = model(**inputs)
    target_sizes = torch.tensor([image.size[::-1]], device=device)
    results = processor.post_process_object_detection(outputs, threshold=0.5, target_sizes=target_sizes)[0]
    boxes = results["boxes"].detach().cpu().numpy()
    labels = [model.config.id2label.get(int(label), str(int(label))) for label in results["labels"].detach().cpu().numpy()]
    scores = results["scores"].detach().cpu().tolist()
    save_prediction_image(image_path, boxes, labels, scores, figures_dir / "detr_prediction.png")


def main() -> None:
    """Dispatch command-line actions."""

    # Tạo parser để nhận tham số từ terminal hoặc notebook.
    parser = argparse.ArgumentParser(description="Chess Pieces object detection")
    # Cho phép truyền đường dẫn dataset nếu không đặt đúng chỗ mặc định.
    parser.add_argument("--dataset", type=Path, default=None, help="Path to 416x416_aug_chess_pieces")
    # Chỉ định nơi lưu output sinh ra trong quá trình chạy.
    parser.add_argument("--output", type=Path, default=Path("outputs"), help="Output directory")
    # Chỉ định nơi lưu hình minh chứng cho notebook/báo cáo.
    parser.add_argument("--figures", type=Path, default=Path("../doc/figures"), help="Report figures directory")
    # Số epoch mặc định để chạy nhanh khi kiểm tra.
    parser.add_argument("--epochs", type=int, default=3, help="Small default for quick verification; increase for final runs")
    # Batch size cho DETR và Faster R-CNN.
    parser.add_argument("--batch-size", type=int, default=2, help="Training batch size")
    # Kích thước ảnh đầu vào cho YOLO.
    parser.add_argument("--imgsz", type=int, default=416, help="YOLO image size")
    # Chọn lệnh cần chạy.
    parser.add_argument("command", choices=["prepare", "figures", "yolo", "detr", "fasterrcnn", "all"])
    # Parse tham số từ command line.
    args = parser.parse_args()

    # Nếu không truyền dataset thì tự tìm theo vị trí file.
    dataset_root = args.dataset or find_dataset_root(Path(__file__))
    # Tạo thư mục output nếu chưa tồn tại.
    args.output.mkdir(parents=True, exist_ok=True)

    # Lệnh prepare hoặc all: chuyển đổi dataset sang YOLO và COCO.
    if args.command in {"prepare", "all"}:
        # Chuyển sang YOLO format.
        yolo_yaml = convert_to_yolo(dataset_root, args.output)
        # Chuyển sang COCO json.
        coco_root = convert_to_coco(dataset_root, args.output)
        # In vị trí file YOLO config.
        print(f"YOLO config: {yolo_yaml}")
        # In vị trí thư mục COCO.
        print(f"COCO json: {coco_root}")

    # Lệnh figures hoặc all: sinh ảnh minh chứng.
    if args.command in {"figures", "all"}:
        # Vẽ ảnh ground-truth và biểu đồ.
        make_figures(dataset_root, args.figures)
        # In nơi lưu hình.
        print(f"Figures written to: {args.figures}")

    # Lệnh yolo hoặc all: train YOLO.
    if args.command in {"yolo", "all"}:
        # Cần data.yaml trước khi train YOLO.
        data_yaml = convert_to_yolo(dataset_root, args.output)
        # Train và đánh giá YOLO.
        train_yolo(data_yaml, args.epochs, args.imgsz, args.output, args.figures, dataset_root)

    # Lệnh detr hoặc all: train DETR.
    if args.command in {"detr", "all"}:
        # Train DETR và lưu checkpoint trong output/detr_chess.
        train_detr(dataset_root, args.epochs, args.batch_size, args.output / "detr_chess", args.figures)

    # Lệnh fasterrcnn hoặc all: train Faster R-CNN.
    if args.command in {"fasterrcnn", "all"}:
        # Train Faster R-CNN và lưu weight trong output/faster_rcnn.
        train_faster_rcnn(dataset_root, args.epochs, args.batch_size, args.output / "faster_rcnn", args.figures)


if __name__ == "__main__":
    main()
