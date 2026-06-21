"""TH03 object detection experiments on the Chess Pieces dataset.

The script keeps the notebook short while still making each step reproducible:
prepare the dataset, visualize labels, train YOLO/DETR/Faster R-CNN, and write
small result files that can be copied into the report.
"""

# Bật postponed evaluation để type hint không làm chậm lúc import module.
from __future__ import annotations

# argparse dùng để nhận tham số dòng lệnh như prepare, yolo, detr.
import argparse
# json dùng để ghi thống kê dataset và annotation COCO.
import json
# time dùng để đo thời gian huấn luyện Faster R-CNN theo từng epoch.
import time
# dataclass giúp khai báo cấu trúc BoxRecord gọn và rõ ràng.
from dataclasses import dataclass
# Path giúp xử lý đường dẫn độc lập hệ điều hành.
from pathlib import Path
# Iterable dùng cho type hint danh sách box đầu vào của hàm vẽ.
from typing import Iterable

# OpenCV dùng để đọc ảnh, ghi ảnh và vẽ bounding box.
import cv2
# Matplotlib dùng để sinh biểu đồ minh chứng cho báo cáo.
import matplotlib

# Dùng backend không cần giao diện để chạy được trên Colab/headless server.
matplotlib.use("Agg")
# pyplot cung cấp API vẽ biểu đồ cột.
import matplotlib.pyplot as plt
# NumPy dùng để thao tác mảng ảnh và dữ liệu thống kê.
import numpy as np
# PIL dùng để đọc kích thước ảnh khi xuất định dạng COCO.
from PIL import Image


# Ba split chuẩn của dataset Roboflow đã cung cấp.
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

    # Duyệt thư mục hiện tại và toàn bộ thư mục cha để tìm dataset.
    for parent in [start.resolve(), *start.resolve().parents]:
        # Ghép tên dataset vào từng thư mục đang xét.
        candidate = parent / dataset_name
        # Nếu thư mục tồn tại thì trả về ngay để các bước sau dùng.
        if candidate.exists():
            return candidate
    # Nếu không tìm thấy, báo lỗi rõ ràng và gợi ý truyền --dataset.
    raise FileNotFoundError(f"Cannot find {dataset_name}; pass --dataset explicitly.")


def read_classes(dataset_root: Path) -> list[str]:
    """Read the class list exported by Roboflow."""

    # File _classes.txt trong split train chứa toàn bộ tên lớp.
    classes_path = dataset_root / "train" / "_classes.txt"
    # Đọc từng dòng, bỏ dòng trống và trả về danh sách tên lớp.
    return [line.strip() for line in classes_path.read_text(encoding="utf-8").splitlines() if line.strip()]


def parse_annotation_line(line: str) -> tuple[str, list[BoxRecord]]:
    """Parse one Roboflow annotation row: image_name x1,y1,x2,y2,class ..."""

    # Tách dòng annotation thành tên ảnh và các chuỗi bounding box.
    parts = line.strip().split()
    # Phần tử đầu tiên luôn là tên file ảnh.
    image_name = parts[0]
    # Khởi tạo danh sách box của ảnh hiện tại.
    records: list[BoxRecord] = []
    # Duyệt từng annotation dạng x1,y1,x2,y2,class_id.
    for item in parts[1:]:
        # Tách tọa độ và id lớp từ chuỗi annotation.
        x1, y1, x2, y2, class_id = item.split(",")
        # Chuyển dữ liệu từ chuỗi sang số và lưu vào BoxRecord.
        records.append(BoxRecord(image_name, float(x1), float(y1), float(x2), float(y2), int(class_id)))
    # Trả về tên ảnh kèm toàn bộ box của ảnh đó.
    return image_name, records


def load_split_annotations(dataset_root: Path, split: str) -> dict[str, list[BoxRecord]]:
    """Load all annotations for one split into a dictionary keyed by image name."""

    # Mỗi split có một file _annotations.txt do Roboflow xuất ra.
    annotation_path = dataset_root / split / "_annotations.txt"
    # Dictionary giúp truy xuất nhanh box theo tên ảnh.
    annotations: dict[str, list[BoxRecord]] = {}
    # Đọc file annotation theo từng dòng.
    for line in annotation_path.read_text(encoding="utf-8").splitlines():
        # Bỏ qua dòng trống để tránh lỗi parse.
        if line.strip():
            # Parse dòng thành tên ảnh và danh sách box.
            image_name, records = parse_annotation_line(line)
            # Lưu danh sách box vào dictionary.
            annotations[image_name] = records
    # Trả về toàn bộ annotation của split.
    return annotations


def dataset_stats(dataset_root: Path) -> dict:
    """Collect image and object counts for the report."""

    # Đọc tên lớp để tạo bộ đếm theo lớp.
    classes = read_classes(dataset_root)
    # Khởi tạo cấu trúc thống kê tổng và thống kê từng split.
    stats = {"classes": classes, "splits": {}, "total_images": 0, "total_boxes": 0}
    # Tính thống kê lần lượt cho train, valid và test.
    for split in SPLITS:
        # Tải annotation của split hiện tại.
        annotations = load_split_annotations(dataset_root, split)
        # Mỗi lớp bắt đầu với số lượng box bằng 0.
        class_counts = {name: 0 for name in classes}
        # Biến đếm tổng số box của split.
        box_count = 0
        # Duyệt danh sách box của tất cả ảnh.
        for records in annotations.values():
            # Duyệt từng box trong một ảnh.
            for record in records:
                # Tăng bộ đếm của lớp tương ứng.
                class_counts[classes[record.class_id]] += 1
                # Tăng tổng số box của split.
                box_count += 1
        # Lưu thống kê chi tiết của split hiện tại.
        stats["splits"][split] = {
            "images": len(list((dataset_root / split).glob("*.jpg"))),
            "annotated_images": len(annotations),
            "boxes": box_count,
            "class_counts": class_counts,
        }
        # Cộng dồn số ảnh vào thống kê toàn dataset.
        stats["total_images"] += stats["splits"][split]["images"]
        # Cộng dồn số box vào thống kê toàn dataset.
        stats["total_boxes"] += box_count
    # Trả về dictionary thống kê để ghi JSON và báo cáo.
    return stats


def convert_to_yolo(dataset_root: Path, output_root: Path) -> Path:
    """Convert absolute boxes to YOLO txt labels and write data.yaml."""

    # Đọc danh sách lớp để ghi trường names trong data.yaml.
    classes = read_classes(dataset_root)
    # Tạo thư mục gốc cho dataset theo chuẩn YOLO.
    yolo_root = output_root / "chess_yolo"
    # Xử lý đủ ba split để YOLO có train/val/test.
    for split in SPLITS:
        # Thư mục ảnh theo chuẩn Ultralytics.
        image_out = yolo_root / "images" / split
        # Thư mục nhãn YOLO tương ứng với thư mục ảnh.
        label_out = yolo_root / "labels" / split
        # Tạo thư mục ảnh nếu chưa tồn tại.
        image_out.mkdir(parents=True, exist_ok=True)
        # Tạo thư mục nhãn nếu chưa tồn tại.
        label_out.mkdir(parents=True, exist_ok=True)
        # Tải annotation của split hiện tại.
        annotations = load_split_annotations(dataset_root, split)
        # Duyệt từng ảnh jpg trong split.
        for image_path in (dataset_root / split).glob("*.jpg"):
            # Đọc ảnh để lấy kích thước thật.
            image = cv2.imread(str(image_path))
            # Lấy chiều cao và chiều rộng của ảnh.
            height, width = image.shape[:2]
            # Copy ảnh sang thư mục YOLO để Ultralytics tìm nhãn tự động.
            (image_out / image_path.name).write_bytes(image_path.read_bytes())
            # Mỗi dòng trong file label là một box chuẩn hóa.
            rows = []
            # Duyệt các box của ảnh, nếu ảnh không có box thì dùng danh sách rỗng.
            for record in annotations.get(image_path.name, []):
                # YOLO dùng tâm box theo trục x đã chia cho chiều rộng ảnh.
                cx = ((record.x1 + record.x2) / 2.0) / width
                # YOLO dùng tâm box theo trục y đã chia cho chiều cao ảnh.
                cy = ((record.y1 + record.y2) / 2.0) / height
                # Chiều rộng box được chuẩn hóa về khoảng 0..1.
                bw = (record.x2 - record.x1) / width
                # Chiều cao box được chuẩn hóa về khoảng 0..1.
                bh = (record.y2 - record.y1) / height
                # Ghi một dòng label theo định dạng class cx cy w h.
                rows.append(f"{record.class_id} {cx:.6f} {cy:.6f} {bw:.6f} {bh:.6f}")
            # Ghi file txt có cùng stem với ảnh.
            (label_out / f"{image_path.stem}.txt").write_text("\n".join(rows), encoding="utf-8")
    # Nội dung file data.yaml cho Ultralytics.
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
    # Đường dẫn file cấu hình YOLO.
    data_yaml = yolo_root / "data.yaml"
    # Ghi file data.yaml ra đĩa.
    data_yaml.write_text("\n".join(yaml_text), encoding="utf-8")
    # Trả về đường dẫn để hàm train_yolo dùng ngay.
    return data_yaml


def convert_to_coco(dataset_root: Path, output_root: Path) -> Path:
    """Convert the dataset to COCO json files used by DETR and Faster R-CNN."""

    # COCO cần danh sách category, vì vậy đọc lớp trước.
    classes = read_classes(dataset_root)
    # Tạo thư mục chứa các file train.json, valid.json và test.json.
    coco_root = output_root / "chess_coco"
    # Đảm bảo thư mục COCO tồn tại trước khi ghi file.
    coco_root.mkdir(parents=True, exist_ok=True)
    # Xuất riêng từng split để dễ dùng trong huấn luyện/đánh giá.
    for split in SPLITS:
        # Tải annotation gốc của split.
        annotations_by_image = load_split_annotations(dataset_root, split)
        # Danh sách metadata ảnh theo chuẩn COCO.
        images = []
        # Danh sách annotation box theo chuẩn COCO.
        annotations = []
        # COCO yêu cầu mỗi annotation có id duy nhất.
        annotation_id = 1
        # Gán image_id tăng dần cho từng ảnh.
        for image_id, image_path in enumerate(sorted((dataset_root / split).glob("*.jpg")), start=1):
            # Mở ảnh bằng PIL để lấy kích thước.
            with Image.open(image_path) as image:
                # Lưu width và height đúng theo ảnh sau resize.
                width, height = image.size
            # Thêm thông tin ảnh vào danh sách COCO images.
            images.append({"id": image_id, "file_name": image_path.name, "width": width, "height": height})
            # Duyệt các box thuộc ảnh hiện tại.
            for record in annotations_by_image.get(image_path.name, []):
                # COCO dùng width của box thay vì x2.
                width_box = record.x2 - record.x1
                # COCO dùng height của box thay vì y2.
                height_box = record.y2 - record.y1
                # Thêm một annotation theo đúng schema COCO.
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
                # Tăng id để annotation tiếp theo không trùng.
                annotation_id += 1
        # Category id trong COCO bắt đầu từ 1 để 0 dành cho background.
        categories = [{"id": idx + 1, "name": name} for idx, name in enumerate(classes)]
        # Ghép ba phần chính của COCO json.
        payload = {"images": images, "annotations": annotations, "categories": categories}
        # Ghi file JSON cho split hiện tại.
        (coco_root / f"{split}.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    # Trả về thư mục COCO để các bước sau biết vị trí dữ liệu.
    return coco_root


def draw_boxes(image: np.ndarray, boxes: Iterable[BoxRecord], classes: list[str]) -> np.ndarray:
    """Draw annotated bounding boxes on one image."""

    # Copy ảnh để không thay đổi ảnh gốc.
    output = image.copy()
    # Duyệt từng box cần vẽ.
    for record in boxes:
        # Chọn màu xanh lá cho bounding box minh chứng.
        color = (30, 180, 60)
        # Vẽ hình chữ nhật từ góc trái trên đến góc phải dưới.
        cv2.rectangle(output, (int(record.x1), int(record.y1)), (int(record.x2), int(record.y2)), color, 2)
        # Ghi tên lớp ngay phía trên box.
        cv2.putText(output, classes[record.class_id], (int(record.x1), max(15, int(record.y1) - 6)), cv2.FONT_HERSHEY_SIMPLEX, 0.45, color, 1)
    # Trả về ảnh đã vẽ box.
    return output


def make_figures(dataset_root: Path, figures_dir: Path) -> None:
    """Generate evidence figures for the report."""

    # Tạo thư mục figures trong doc nếu chưa có.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Lấy thống kê dataset để vừa vẽ biểu đồ vừa ghi JSON.
    stats = dataset_stats(dataset_root)
    # Lấy danh sách lớp từ thống kê.
    classes = stats["classes"]
    # Chọn ảnh train đầu tiên để minh họa ground-truth.
    first_image_name = next(iter(load_split_annotations(dataset_root, "train")))
    # Tải annotation train để lấy box của ảnh minh họa.
    train_annotations = load_split_annotations(dataset_root, "train")
    # Đọc ảnh minh họa bằng OpenCV.
    image = cv2.imread(str(dataset_root / "train" / first_image_name))
    # Vẽ box ground-truth lên ảnh.
    labeled = draw_boxes(image, train_annotations[first_image_name], classes)
    # Ghi ảnh minh họa vào thư mục báo cáo.
    cv2.imwrite(str(figures_dir / "sample_ground_truth.png"), labeled)

    # Lấy tên các split để làm nhãn trục x.
    split_names = list(stats["splits"].keys())
    # Lấy số ảnh của từng split.
    image_counts = [stats["splits"][split]["images"] for split in split_names]
    # Lấy số box của từng split.
    box_counts = [stats["splits"][split]["boxes"] for split in split_names]
    # Tạo khung hình biểu đồ split.
    plt.figure(figsize=(7, 4))
    # Tạo vị trí cột trên trục x.
    x_positions = np.arange(len(split_names))
    # Vẽ cột số ảnh lệch trái.
    plt.bar(x_positions - 0.18, image_counts, width=0.36, label="Images")
    # Vẽ cột số box lệch phải.
    plt.bar(x_positions + 0.18, box_counts, width=0.36, label="Boxes")
    # Gán nhãn split cho trục x.
    plt.xticks(x_positions, split_names)
    # Gán nhãn trục y.
    plt.ylabel("Count")
    # Gán tiêu đề biểu đồ.
    plt.title("Chess Pieces split distribution")
    # Hiển thị chú giải Images/Boxes.
    plt.legend()
    # Căn layout để chữ không bị cắt.
    plt.tight_layout()
    # Lưu biểu đồ split.
    plt.savefig(figures_dir / "split_distribution.png", dpi=160)
    # Đóng figure để giải phóng bộ nhớ.
    plt.close()

    # Khởi tạo vector đếm tổng số box theo lớp.
    total_per_class = np.zeros(len(classes), dtype=int)
    # Cộng dồn số box theo lớp từ từng split.
    for split in SPLITS:
        # Lấy dictionary class_counts của split.
        counts = stats["splits"][split]["class_counts"]
        # Chuyển dictionary sang vector đúng thứ tự classes và cộng dồn.
        total_per_class += np.array([counts[name] for name in classes])
    # Tạo khung hình biểu đồ phân bố lớp.
    plt.figure(figsize=(10, 5))
    # Vẽ biểu đồ cột theo tên lớp.
    plt.bar(classes, total_per_class)
    # Xoay nhãn lớp để không đè nhau.
    plt.xticks(rotation=55, ha="right")
    # Gán nhãn trục y.
    plt.ylabel("Bounding boxes")
    # Gán tiêu đề biểu đồ.
    plt.title("Class distribution")
    # Căn layout để nhãn lớp hiển thị đầy đủ.
    plt.tight_layout()
    # Lưu biểu đồ phân bố lớp.
    plt.savefig(figures_dir / "class_distribution.png", dpi=160)
    # Đóng figure để tránh giữ tài nguyên.
    plt.close()

    # Ghi thống kê dạng JSON để báo cáo có số liệu tái kiểm tra được.
    (figures_dir / "dataset_stats.json").write_text(json.dumps(stats, indent=2), encoding="utf-8")


class ChessCocoDataset:
    """Minimal PyTorch dataset for Faster R-CNN training."""

    def __init__(self, dataset_root: Path, split: str):
        # Lưu đường dẫn dataset để __getitem__ đọc ảnh.
        self.dataset_root = dataset_root
        # Lưu tên split để biết đang dùng train/valid/test.
        self.split = split
        # Lấy danh sách ảnh jpg của split.
        self.images = sorted((dataset_root / split).glob("*.jpg"))
        # Tải annotation tương ứng với split.
        self.annotations = load_split_annotations(dataset_root, split)

    def __len__(self) -> int:
        # Trả về số ảnh để DataLoader biết độ dài dataset.
        return len(self.images)

    def __getitem__(self, index: int):
        # Import torch tại đây để các lệnh prepare/figures không cần cài torch.
        import torch

        # Lấy đường dẫn ảnh theo index.
        image_path = self.images[index]
        # Đọc ảnh RGB bằng PIL.
        image = Image.open(image_path).convert("RGB")
        # Chuyển ảnh sang tensor C x H x W và chuẩn hóa về 0..1.
        image_tensor = torch.as_tensor(np.array(image), dtype=torch.float32).permute(2, 0, 1) / 255.0
        # Lấy danh sách annotation của ảnh.
        records = self.annotations.get(image_path.name, [])
        # Chuyển box sang tensor [x1, y1, x2, y2].
        boxes = torch.as_tensor([[r.x1, r.y1, r.x2, r.y2] for r in records], dtype=torch.float32)
        # Chuyển nhãn sang tensor, cộng 1 để 0 là background.
        labels = torch.as_tensor([r.class_id + 1 for r in records], dtype=torch.int64)
        # Tạo target dictionary theo yêu cầu của TorchVision detection models.
        target = {"boxes": boxes, "labels": labels, "image_id": torch.tensor([index])}
        # Trả về một mẫu ảnh và nhãn.
        return image_tensor, target


def collate_detection_batch(batch):
    """Keep images and targets as lists because each image has a different object count."""

    # Detection batch không thể stack target vì mỗi ảnh có số box khác nhau.
    return tuple(zip(*batch))


def train_yolo(data_yaml: Path, epochs: int, imgsz: int, project: Path) -> None:
    """Fine-tune a pretrained YOLOv8 nano model."""

    # Import Ultralytics tại đây để chỉ cần thư viện khi thật sự train YOLO.
    from ultralytics import YOLO

    # Tải checkpoint pretrained YOLOv8 nano.
    model = YOLO("yolov8n.pt")
    # Huấn luyện YOLO trên data.yaml vừa chuyển đổi.
    model.train(data=str(data_yaml), epochs=epochs, imgsz=imgsz, project=str(project), name="yolo_chess", pretrained=True)
    # Đánh giá mô hình trên test split.
    metrics = model.val(data=str(data_yaml), split="test", imgsz=imgsz)
    # Ghi metrics thô để nhóm đưa số liệu vào báo cáo.
    (project / "yolo_metrics.txt").write_text(str(metrics), encoding="utf-8")


def train_faster_rcnn(dataset_root: Path, epochs: int, batch_size: int, output_dir: Path) -> None:
    """Fine-tune Faster R-CNN with a ResNet-50 FPN backbone."""

    # Import torch tại đây để các bước không train vẫn chạy nhẹ.
    import torch
    # DataLoader dùng để tạo batch ảnh/target.
    from torch.utils.data import DataLoader
    # Tải kiến trúc và pretrained weights của Faster R-CNN.
    from torchvision.models.detection import FasterRCNN_ResNet50_FPN_Weights, fasterrcnn_resnet50_fpn
    # FastRCNNPredictor dùng để thay head phân loại theo số lớp chess.
    from torchvision.models.detection.faster_rcnn import FastRCNNPredictor

    # Chọn GPU nếu có, nếu không thì dùng CPU.
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    # Đọc danh sách lớp chess.
    classes = read_classes(dataset_root)
    # Tạo mô hình Faster R-CNN pretrained trên COCO.
    model = fasterrcnn_resnet50_fpn(weights=FasterRCNN_ResNet50_FPN_Weights.DEFAULT)
    # Lấy số đặc trưng đầu vào của classifier hiện tại.
    in_features = model.roi_heads.box_predictor.cls_score.in_features
    # Thay classifier để dự đoán số lớp chess cộng background.
    model.roi_heads.box_predictor = FastRCNNPredictor(in_features, len(classes) + 1)
    # Đưa mô hình lên thiết bị huấn luyện.
    model.to(device)
    # Tạo DataLoader cho tập train.
    train_loader = DataLoader(ChessCocoDataset(dataset_root, "train"), batch_size=batch_size, shuffle=True, collate_fn=collate_detection_batch)
    # AdamW thường ổn định khi fine-tune backbone pretrained.
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-4, weight_decay=1e-4)
    # Tạo thư mục lưu weight đầu ra.
    output_dir.mkdir(parents=True, exist_ok=True)
    # Lặp qua số epoch được truyền từ dòng lệnh.
    for epoch in range(epochs):
        # Chuyển mô hình sang chế độ train.
        model.train()
        # Biến cộng dồn loss để in log.
        running_loss = 0.0
        # Ghi thời điểm bắt đầu epoch.
        start = time.perf_counter()
        # Duyệt từng batch ảnh và target.
        for images, targets in train_loader:
            # Đưa từng ảnh trong batch lên GPU/CPU.
            images = [image.to(device) for image in images]
            # Đưa từng tensor target lên GPU/CPU.
            targets = [{key: value.to(device) for key, value in target.items()} for target in targets]
            # TorchVision trả về dictionary loss khi có target.
            losses = model(images, targets)
            # Cộng tất cả loss thành một scalar để backprop.
            loss = sum(value for value in losses.values())
            # Xóa gradient cũ.
            optimizer.zero_grad()
            # Lan truyền ngược để tính gradient mới.
            loss.backward()
            # Cập nhật trọng số mô hình.
            optimizer.step()
            # Cộng loss của batch vào log epoch.
            running_loss += float(loss.detach().cpu())
        # Tính thời gian chạy của epoch.
        elapsed = time.perf_counter() - start
        # In loss trung bình để theo dõi quá trình fine-tune.
        print(f"epoch={epoch + 1} loss={running_loss / max(1, len(train_loader)):.4f} time={elapsed:.1f}s")
    # Lưu weight cuối cùng để tái sử dụng khi inference.
    torch.save(model.state_dict(), output_dir / "faster_rcnn_chess.pth")


def train_detr(dataset_root: Path, epochs: int, batch_size: int, output_dir: Path) -> None:
    """Fine-tune DETR using Hugging Face Transformers."""

    # Import torch tại đây để không bắt buộc khi chỉ chuẩn bị dữ liệu.
    import torch
    # Dataset base class dùng cho dataset DETR lồng bên dưới.
    from torch.utils.data import Dataset
    # Import mô hình, processor và Trainer từ Hugging Face.
    from transformers import DetrForObjectDetection, DetrImageProcessor, Trainer, TrainingArguments

    # Đọc danh sách lớp chess.
    classes = read_classes(dataset_root)
    # Tạo mapping id sang label, id 0 ngầm dành cho no-object/background.
    id2label = {idx + 1: name for idx, name in enumerate(classes)}
    # Tạo mapping ngược label sang id.
    label2id = {name: idx for idx, name in id2label.items()}
    # Processor xử lý resize/normalize và encode annotation cho DETR.
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
            # Lấy đường dẫn ảnh theo index.
            image_path = self.images[index]
            # Đọc ảnh RGB bằng PIL.
            image = Image.open(image_path).convert("RGB")
            # Lấy các box của ảnh.
            records = self.annotations.get(image_path.name, [])
            # Tạo target theo dạng COCO annotation mà DetrImageProcessor yêu cầu.
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
            # Processor chuyển ảnh và annotation thành tensor DETR.
            encoded = processor(images=image, annotations=target, return_tensors="pt")
            # Bỏ chiều batch vì Dataset chỉ trả về một mẫu.
            return {"pixel_values": encoded["pixel_values"].squeeze(0), "labels": encoded["labels"][0]}

    def collate_fn(batch):
        # Lấy tensor ảnh từ từng mẫu trong batch.
        pixel_values = [item["pixel_values"] for item in batch]
        # Pad ảnh để batch có cùng kích thước tensor.
        encoding = processor.pad(pixel_values, return_tensors="pt")
        # Labels giữ dạng list vì số object mỗi ảnh khác nhau.
        labels = [item["labels"] for item in batch]
        # Trả về đúng key mà DetrForObjectDetection nhận.
        return {"pixel_values": encoding["pixel_values"], "pixel_mask": encoding["pixel_mask"], "labels": labels}

    # Tải checkpoint DETR pretrained và thay số lớp đầu ra.
    model = DetrForObjectDetection.from_pretrained(
        "facebook/detr-resnet-50",
        num_labels=len(classes) + 1,
        id2label=id2label,
        label2id=label2id,
        ignore_mismatched_sizes=True,
    )
    # Cấu hình huấn luyện cho Hugging Face Trainer.
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
    # Khởi tạo Trainer với train/valid dataset và collate_fn tùy biến.
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


def main() -> None:
    """Dispatch command-line actions."""

    # Tạo parser để nhận tham số từ terminal/notebook.
    parser = argparse.ArgumentParser(description="TH03 Chess Pieces object detection")
    # --dataset cho phép chỉ định dataset nếu không đặt ở root repo.
    parser.add_argument("--dataset", type=Path, default=None, help="Path to 416x416_aug_chess_pieces")
    # --output là nơi ghi dữ liệu chuyển đổi và kết quả train.
    parser.add_argument("--output", type=Path, default=Path("outputs"), help="Output directory")
    # --figures là nơi lưu hình minh chứng cho báo cáo.
    parser.add_argument("--figures", type=Path, default=Path("../doc/figures"), help="Report figures directory")
    # --epochs đặt số epoch, mặc định nhỏ để smoke test.
    parser.add_argument("--epochs", type=int, default=3, help="Small default for quick verification; increase for final runs")
    # --batch-size đặt batch size cho DETR/Faster R-CNN.
    parser.add_argument("--batch-size", type=int, default=2, help="Training batch size")
    # --imgsz đặt kích thước ảnh cho YOLO.
    parser.add_argument("--imgsz", type=int, default=416, help="YOLO image size")
    # command chọn tác vụ cần chạy.
    parser.add_argument("command", choices=["prepare", "figures", "yolo", "detr", "fasterrcnn", "all"])
    # Parse tham số dòng lệnh thành object args.
    args = parser.parse_args()

    # Nếu người dùng không truyền --dataset thì tự tìm dataset từ vị trí file.
    dataset_root = args.dataset or find_dataset_root(Path(__file__))
    # Tạo thư mục output nếu chưa có.
    args.output.mkdir(parents=True, exist_ok=True)

    # prepare/all: sinh định dạng YOLO và COCO.
    if args.command in {"prepare", "all"}:
        # Chuyển annotation sang YOLO format.
        yolo_yaml = convert_to_yolo(dataset_root, args.output)
        # Chuyển annotation sang COCO json.
        coco_root = convert_to_coco(dataset_root, args.output)
        # In đường dẫn data.yaml để người chạy dễ kiểm tra.
        print(f"YOLO config: {yolo_yaml}")
        # In đường dẫn COCO json để người chạy dễ kiểm tra.
        print(f"COCO json: {coco_root}")

    # figures/all: sinh hình minh chứng và file thống kê.
    if args.command in {"figures", "all"}:
        # Vẽ hình ground-truth và biểu đồ dataset.
        make_figures(dataset_root, args.figures)
        # In vị trí lưu hình.
        print(f"Figures written to: {args.figures}")

    # yolo/all: fine-tune YOLO.
    if args.command in {"yolo", "all"}:
        # YOLO cần data.yaml nên gọi convert trước khi train.
        data_yaml = convert_to_yolo(dataset_root, args.output)
        # Huấn luyện và đánh giá YOLO.
        train_yolo(data_yaml, args.epochs, args.imgsz, args.output)

    # detr/all: fine-tune DETR.
    if args.command in {"detr", "all"}:
        # Huấn luyện DETR và lưu checkpoint vào output/detr_chess.
        train_detr(dataset_root, args.epochs, args.batch_size, args.output / "detr_chess")

    # fasterrcnn/all: fine-tune Faster R-CNN.
    if args.command in {"fasterrcnn", "all"}:
        # Huấn luyện Faster R-CNN và lưu weight vào output/faster_rcnn.
        train_faster_rcnn(dataset_root, args.epochs, args.batch_size, args.output / "faster_rcnn")


if __name__ == "__main__":
    main()
