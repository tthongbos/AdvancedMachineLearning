# Pipeline phát hiện đối tượng cho bộ dữ liệu cờ vua.
"""Object detection pipeline for the Chess Pieces dataset."""

# Import các thành phần cần cho phần dưới.
from __future__ import annotations

# Import thư viện hỗ trợ.
import argparse
# Import thư viện hỗ trợ.
import json
# Import thư viện hỗ trợ.
import os
# Import thư viện hỗ trợ.
import shutil
# Import thư viện hỗ trợ.
import time
# Import các thành phần cần cho phần dưới.
from dataclasses import dataclass
# Import các thành phần cần cho phần dưới.
from pathlib import Path
# Import các thành phần cần cho phần dưới.
from typing import Iterable

# Import thư viện hỗ trợ.
import cv2
# Import thư viện hỗ trợ.
import matplotlib

# Bật backend Agg.
matplotlib.use("Agg")
# Import thư viện hỗ trợ.
import matplotlib.pyplot as plt
# Import thư viện hỗ trợ.
import numpy as np
# Import các thành phần cần cho phần dưới.
from PIL import Image

# Danh sách split chuẩn của dataset.
SPLITS = ("train", "valid", "test")


@dataclass
# Mỗi record lưu một bbox của một object trong ảnh.
class BoxRecord:
    # Lưu một bbox cùng class của nó.
    """One object annotation in absolute pixel coordinates."""

    # Lưu image_name.
    image_name: str
    # Lưu x1.
    x1: float
    # Lưu y1.
    y1: float
    # Lưu x2.
    x2: float
    # Lưu y2.
    y2: float
    # Lưu class_id.
    class_id: int


# Định nghĩa find_dataset_root.
def find_dataset_root(start: Path, dataset_name: str = "416x416_aug_chess_pieces") -> Path:
    # Duyệt từng phần tử để xử lý.
    for parent in [start.resolve(), *start.resolve().parents]:
        # Lưu candidate.
        candidate = parent / dataset_name
        # Chỉ xử lý khi điều kiện đúng.
        if candidate.exists():
            # Trả về giá trị đã tính.
            return candidate
    # Báo lỗi để dừng sớm.
    raise FileNotFoundError(f"Cannot find {dataset_name}; pass --dataset explicitly.")


# Định nghĩa read_classes.
def read_classes(dataset_root: Path) -> list[str]:
    # Lưu classes_path.
    classes_path = dataset_root / "train" / "_classes.txt"
    # Trả về giá trị đã tính.
    return [line.strip() for line in classes_path.read_text(encoding="utf-8").splitlines() if line.strip()]


# Định nghĩa parse_annotation_line.
def parse_annotation_line(line: str) -> tuple[str, list[BoxRecord]]:
    # Lưu parts.
    parts = line.strip().split()
    # Lưu image_name.
    image_name = parts[0]
    # Lưu records.
    records: list[BoxRecord] = []
    # Duyệt từng phần tử để xử lý.
    for item in parts[1:]:
        # Lưu x1, y1, x2, y2, class_id.
        x1, y1, x2, y2, class_id = item.split(",")
        # Thêm phần tử vào danh sách.
        records.append(BoxRecord(image_name, float(x1), float(y1), float(x2), float(y2), int(class_id)))
    # Trả về giá trị đã tính.
    return image_name, records


# Định nghĩa load_split_annotations.
def load_split_annotations(dataset_root: Path, split: str) -> dict[str, list[BoxRecord]]:
    # Lưu annotation_path.
    annotation_path = dataset_root / split / "_annotations.txt"
    # Lưu annotations.
    annotations: dict[str, list[BoxRecord]] = {}
    # Duyệt từng phần tử để xử lý.
    for line in annotation_path.read_text(encoding="utf-8").splitlines():
        # Chỉ xử lý khi điều kiện đúng.
        if line.strip():
            # Lưu image_name, records.
            image_name, records = parse_annotation_line(line)
            # Lưu value.
            annotations[image_name] = records
    # Trả về giá trị đã tính.
    return annotations


# Định nghĩa dataset_stats.
def dataset_stats(dataset_root: Path) -> dict:
    # Lưu classes.
    classes = read_classes(dataset_root)
    # Lưu stats.
    stats = {"classes": classes, "splits": {}, "total_images": 0, "total_boxes": 0}
    # Duyệt từng phần tử để xử lý.
    for split in SPLITS:
        # Lưu annotations.
        annotations = load_split_annotations(dataset_root, split)
        # Lưu class_counts.
        class_counts = {name: 0 for name in classes}
        # Lưu box_count.
        box_count = 0
        # Duyệt từng phần tử để xử lý.
        for records in annotations.values():
            # Duyệt từng phần tử để xử lý.
            for record in records:
                # Cập nhật value.
                class_counts[classes[record.class_id]] += 1
                # Cập nhật box_count.
                box_count += 1
        # Lưu value.
        stats["splits"][split] = {
            "images": len(list((dataset_root / split).glob("*.jpg"))),
            "annotated_images": len(annotations),
            "boxes": box_count,
            "class_counts": class_counts,
        }
        # Cập nhật value.
        stats["total_images"] += stats["splits"][split]["images"]
        # Cập nhật value.
        stats["total_boxes"] += box_count
    # Trả về giá trị đã tính.
    return stats


# Định nghĩa get_safe_torch_device.
def get_safe_torch_device():
    # Import thư viện hỗ trợ.
    import torch

    # Chỉ xử lý khi điều kiện đúng.
    if not torch.cuda.is_available():
        # Trả về giá trị đã tính.
        return torch.device("cpu")
    # Lưu capability.
    capability = torch.cuda.get_device_capability(0)
    # Chỉ xử lý khi điều kiện đúng.
    if capability[0] < 7:
        # Trả về giá trị đã tính.
        return torch.device("cpu")
    # Handle errors.
    try:
        # Thử cấp phát tensor trên CUDA.
        torch.zeros(1, device="cuda")
        # Trả về giá trị đã tính.
        return torch.device("cuda")
    except Exception:
        # Trả về giá trị đã tính.
        return torch.device("cpu")


# Định nghĩa convert_to_yolo.
def convert_to_yolo(dataset_root: Path, output_root: Path) -> Path:
    # Đọc danh sách class để ghi vào file cấu hình YOLO.
    classes = read_classes(dataset_root)
    # Tạo thư mục gốc cho bộ dữ liệu theo định dạng YOLO.
    yolo_root = output_root / "chess_yolo"
    # Chuyển lần lượt từng split train/valid/test.
    for split in SPLITS:
        # Thư mục lưu ảnh của split hiện tại.
        image_out = yolo_root / "images" / split
        # Thư mục lưu nhãn YOLO của split hiện tại.
        label_out = yolo_root / "labels" / split
        # Tạo sẵn các thư mục đầu ra.
        image_out.mkdir(parents=True, exist_ok=True)
        label_out.mkdir(parents=True, exist_ok=True)
        # Đọc toàn bộ annotation của split hiện tại.
        annotations = load_split_annotations(dataset_root, split)
        # Duyệt từng ảnh để copy sang cấu trúc YOLO và ghi nhãn tương ứng.
        for image_path in (dataset_root / split).glob("*.jpg"):
            # Đọc ảnh gốc để lấy kích thước thật.
            image = cv2.imread(str(image_path))
            # Dùng kích thước ảnh để chuẩn hóa bbox sang [0, 1].
            height, width = image.shape[:2]
            # Copy ảnh sang thư mục images của YOLO.
            (image_out / image_path.name).write_bytes(image_path.read_bytes())
            # Gom từng dòng nhãn YOLO cho ảnh hiện tại.
            rows = []
            # Chuyển từng bbox từ tọa độ tuyệt đối sang format YOLO.
            for record in annotations.get(image_path.name, []):
                # Tính tâm bbox theo trục x.
                cx = ((record.x1 + record.x2) / 2.0) / width
                # Tính tâm bbox theo trục y.
                cy = ((record.y1 + record.y2) / 2.0) / height
                # Tính chiều rộng bbox đã chuẩn hóa.
                bw = (record.x2 - record.x1) / width
                # Tính chiều cao bbox đã chuẩn hóa.
                bh = (record.y2 - record.y1) / height
                # Ghi một dòng theo đúng định dạng class cx cy w h.
                rows.append(f"{record.class_id} {cx:.6f} {cy:.6f} {bw:.6f} {bh:.6f}")
            # Lưu file nhãn cùng tên với ảnh.
            (label_out / f"{image_path.stem}.txt").write_text("\n".join(rows), encoding="utf-8")
    # Tạo nội dung data.yaml để Ultralytics đọc dataset.
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
    # Ghi file cấu hình YOLO ra đĩa.
    data_yaml = yolo_root / "data.yaml"
    data_yaml.write_text("\n".join(yaml_text), encoding="utf-8")
    # Trả về đường dẫn data.yaml vừa tạo.
    return data_yaml


# Định nghĩa convert_to_coco.
def convert_to_coco(dataset_root: Path, output_root: Path) -> Path:
    # Đọc danh sách class để tạo COCO categories.
    classes = read_classes(dataset_root)
    # Tạo thư mục gốc cho dữ liệu COCO.
    coco_root = output_root / "chess_coco"
    # Tạo thư mục đầu ra nếu chưa tồn tại.
    coco_root.mkdir(parents=True, exist_ok=True)
    # Xuất file JSON riêng cho từng split.
    for split in SPLITS:
        # Lấy annotation theo từng ảnh để ghép vào JSON.
        annotations_by_image = load_split_annotations(dataset_root, split)
        # Danh sách ảnh theo chuẩn COCO.
        images = []
        # Danh sách bbox theo chuẩn COCO.
        annotations = []
        # COCO cần id riêng cho từng annotation.
        annotation_id = 1
        # Gán image_id tăng dần cho từng ảnh trong split.
        for image_id, image_path in enumerate(sorted((dataset_root / split).glob("*.jpg")), start=1):
            # Đọc kích thước ảnh để ghi vào metadata COCO.
            with Image.open(image_path) as image:
                width, height = image.size
            # Tạo entry ảnh theo format COCO.
            images.append({"id": image_id, "file_name": image_path.name, "width": width, "height": height})
            # Chuyển từng bbox của ảnh sang format COCO.
            for record in annotations_by_image.get(image_path.name, []):
                # COCO dùng bbox dạng x, y, w, h.
                width_box = record.x2 - record.x1
                height_box = record.y2 - record.y1
                # Thêm annotation vào danh sách của split hiện tại.
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
                # Tăng id cho annotation tiếp theo.
                annotation_id += 1
        # Tạo danh mục class theo chuẩn COCO.
        categories = [{"id": idx + 1, "name": name} for idx, name in enumerate(classes)]
        # Ghép toàn bộ dữ liệu thành một payload JSON.
        payload = {"images": images, "annotations": annotations, "categories": categories}
        # Ghi file JSON của split hiện tại.
        (coco_root / f"{split}.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    # Trả về thư mục chứa các file COCO.
    return coco_root


# Định nghĩa draw_boxes.
def draw_boxes(image: np.ndarray, boxes: Iterable[BoxRecord], classes: list[str]) -> np.ndarray:
    # Lưu output.
    output = image.copy()
    # Duyệt từng phần tử để xử lý.
    for record in boxes:
        # Lưu color.
        color = (30, 180, 60)
        # Vẽ khung bbox.
        cv2.rectangle(output, (int(record.x1), int(record.y1)), (int(record.x2), int(record.y2)), color, 2)
        # Ghi nhãn lên ảnh.
        cv2.putText(output, classes[record.class_id], (int(record.x1), max(15, int(record.y1) - 6)), cv2.FONT_HERSHEY_SIMPLEX, 0.45, color, 1)
    # Trả về giá trị đã tính.
    return output


# Định nghĩa save_prediction_image.
def save_prediction_image(
    image_path: Path,
    boxes: np.ndarray,
    labels: list[str],
    scores: list[float],
    output_path: Path,
    min_score: float = 0.60,
) -> None:
    # Lưu image.
    image = cv2.imread(str(image_path))
    # Chỉ xử lý khi điều kiện đúng.
    if image is None:
        # Báo lỗi để dừng sớm.
        raise FileNotFoundError(f"Cannot read image: {image_path}")
    # Lưu canvas.
    canvas = image.copy()
    # Vẽ tất cả bbox còn lại sau khi đã cắt ngưỡng confidence.
    for box, label, score in zip(boxes, labels, scores):
        if float(score) < min_score:
            continue
        # Lưu x1, y1, x2, y2.
        x1, y1, x2, y2 = map(int, box)
        # Lưu color.
        color = (255, 120, 40)
        # Vẽ khung bbox.
        cv2.rectangle(canvas, (x1, y1), (x2, y2), color, 2)
        # Lưu caption.
        caption = f"{label} {score:.2f}"
        # Ghi nhãn lên ảnh.
        cv2.putText(canvas, caption, (x1, max(18, y1 - 6)), cv2.FONT_HERSHEY_SIMPLEX, 0.5, color, 1, cv2.LINE_AA)
    # Tạo thư mục nếu chưa có.
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Ghi ảnh ra đĩa.
    cv2.imwrite(str(output_path), canvas)


# Định nghĩa save_image_grid.
def save_image_grid(image_paths: list[Path], output_path: Path, captions: list[str] | None = None, ncols: int = 2) -> None:
    # Chỉ xử lý khi điều kiện đúng.
    if not image_paths:
        # Trả về giá trị đã tính.
        return

    # Lưu nrows.
    nrows = int(np.ceil(len(image_paths) / ncols))
    # Tạo figure.
    plt.figure(figsize=(6 * ncols, 5 * nrows))
    # Duyệt từng phần tử để xử lý.
    for idx, image_path in enumerate(image_paths, start=1):
        # Lưu ax.
        ax = plt.subplot(nrows, ncols, idx)
        # Lưu image.
        image = cv2.imread(str(image_path))
        # Chỉ xử lý khi điều kiện đúng.
        if image is None:
            # Tắt trục để ảnh gọn hơn.
            ax.axis("off")
            # Bỏ qua phần tử hiện tại.
            continue
        # Hiển thị ảnh trên subplot.
        ax.imshow(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
        # Tắt trục để ảnh gọn hơn.
        ax.axis("off")
        # Chỉ xử lý khi điều kiện đúng.
        if captions and idx - 1 < len(captions):
            # Đặt tiêu đề cho subplot.
            ax.set_title(captions[idx - 1], fontsize=10)
    # Căn layout cho gọn.
    plt.tight_layout()
    # Tạo thư mục nếu chưa có.
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Lưu hình.
    plt.savefig(output_path, dpi=160)
    # Đóng figure.
    plt.close()


# Định nghĩa select_dataset_sample_images.
def select_dataset_sample_images(dataset_root: Path, count: int = 4) -> list[Path]:
    # Lưu selected.
    selected: list[Path] = []
    # Duyệt từng phần tử để xử lý.
    for split in ("train", "valid", "test"):
        # Lưu images.
        images = sorted((dataset_root / split).glob("*.jpg"))
        # Chỉ xử lý khi điều kiện đúng.
        if images:
            # Thêm phần tử vào danh sách.
            selected.append(images[0])
    # Chỉ xử lý khi điều kiện đúng.
    if len(selected) < count:
        # Duyệt từng phần tử để xử lý.
        for split in ("train", "valid", "test"):
            # Duyệt từng phần tử để xử lý.
            for image in sorted((dataset_root / split).glob("*.jpg")):
                # Chỉ xử lý khi điều kiện đúng.
                if image not in selected:
                    # Thêm phần tử vào danh sách.
                    selected.append(image)
                # Chỉ xử lý khi điều kiện đúng.
                if len(selected) >= count:
                    # Bỏ qua phần tử hiện tại.
                    break
            # Chỉ xử lý khi điều kiện đúng.
            if len(selected) >= count:
                # Bỏ qua phần tử hiện tại.
                break
    # Trả về giá trị đã tính.
    return selected[:count]


# Định nghĩa _box_area.
def _box_area(record: BoxRecord) -> float:
    # Trả về giá trị đã tính.
    return max(0.0, (record.x2 - record.x1) * (record.y2 - record.y1))


# Định nghĩa _image_difficulty_score.
def _image_difficulty_score(records: list[BoxRecord], image_width: int, image_height: int) -> float:
    # Chỉ xử lý khi điều kiện đúng.
    if not records:
        # Trả về giá trị đã tính.
        return 0.0
    # Lưu image_area.
    image_area = float(image_width * image_height) if image_width and image_height else 1.0
    # Lưu mean_area.
    mean_area = sum(_box_area(r) for r in records) / max(1, len(records))
    # Lưu small_object_factor.
    small_object_factor = 1.0 - min(1.0, mean_area / image_area)
    # Trả về giá trị đã tính.
    return float(len(records)) + 2.5 * small_object_factor


# Định nghĩa rank_test_images_by_difficulty.
def rank_test_images_by_difficulty(dataset_root: Path) -> list[Path]:
    # Lưu annotations.
    annotations = load_split_annotations(dataset_root, "test")
    # Lưu image_paths.
    image_paths = sorted((dataset_root / "test").glob("*.jpg"))
    # Lưu scored.
    scored: list[tuple[float, Path]] = []
    # Duyệt từng phần tử để xử lý.
    for image_path in image_paths:
        # Lưu image.
        image = cv2.imread(str(image_path))
        # Chỉ xử lý khi điều kiện đúng.
        if image is None:
            # Bỏ qua phần tử hiện tại.
            continue
        # Lưu height, width.
        height, width = image.shape[:2]
        # Lưu score.
        score = _image_difficulty_score(annotations.get(image_path.name, []), width, height)
        # Thêm phần tử vào danh sách.
        scored.append((score, image_path))
    # Sắp xếp theo độ khó.
    scored.sort(key=lambda item: (item[0], item[1].name))
    # Trả về giá trị đã tính.
    return [image_path for _, image_path in scored]


# Định nghĩa select_comparison_test_images.
def select_comparison_test_images(dataset_root: Path, count: int = 5) -> list[Path]:
    # Lưu ranked.
    ranked = rank_test_images_by_difficulty(dataset_root)
    # Chỉ xử lý khi điều kiện đúng.
    if len(ranked) <= count:
        # Trả về giá trị đã tính.
        return ranked
    # Chỉ xử lý khi điều kiện đúng.
    if count != 5:
        # Trả về giá trị đã tính.
        return ranked[:count]
    # Lưu n.
    n = len(ranked)
    # Lưu easy.
    easy = ranked[:2]
    # Lưu medium_start.
    medium_start = max(2, n // 3)
    # Lưu medium.
    medium = ranked[medium_start : medium_start + 2]
    # Lưu hard.
    hard = ranked[-1:]
    # Lưu picked.
    picked = []
    # Duyệt từng phần tử để xử lý.
    for image in easy + medium + hard:
        # Chỉ xử lý khi điều kiện đúng.
        if image not in picked:
            # Thêm phần tử vào danh sách.
            picked.append(image)
    # Duyệt từng phần tử để xử lý.
    for image in ranked:
        # Chỉ xử lý khi điều kiện đúng.
        if len(picked) >= 5:
            # Bỏ qua phần tử hiện tại.
            break
        # Chỉ xử lý khi điều kiện đúng.
        if image not in picked:
            # Thêm phần tử vào danh sách.
            picked.append(image)
    # Trả về giá trị đã tính.
    return picked[:5]


# Định nghĩa _get_gt_for_image.
def _get_gt_for_image(dataset_root: Path, image_path: Path) -> tuple[np.ndarray, list[str]]:
    # Lưu classes.
    classes = read_classes(dataset_root)
    # Lưu split.
    split = image_path.parent.name
    # Lưu annotations.
    annotations = load_split_annotations(dataset_root, split).get(image_path.name, [])
    # Lưu boxes.
    boxes = np.array([[r.x1, r.y1, r.x2, r.y2] for r in annotations], dtype=np.float32)
    # Lưu labels.
    labels = [classes[r.class_id] for r in annotations]
    # Trả về giá trị đã tính.
    return boxes, labels


# Định nghĩa iou_xyxy.
def iou_xyxy(box_a: np.ndarray, box_b: np.ndarray) -> float:
    # Lưu x1.
    x1 = max(float(box_a[0]), float(box_b[0]))
    # Lưu y1.
    y1 = max(float(box_a[1]), float(box_b[1]))
    # Lưu x2.
    x2 = min(float(box_a[2]), float(box_b[2]))
    # Lưu y2.
    y2 = min(float(box_a[3]), float(box_b[3]))
    # Lưu inter_w.
    inter_w = max(0.0, x2 - x1)
    # Lưu inter_h.
    inter_h = max(0.0, y2 - y1)
    # Lưu inter.
    inter = inter_w * inter_h
    # Lưu area_a.
    area_a = max(0.0, float(box_a[2] - box_a[0])) * max(0.0, float(box_a[3] - box_a[1]))
    # Lưu area_b.
    area_b = max(0.0, float(box_b[2] - box_b[0])) * max(0.0, float(box_b[3] - box_b[1]))
    # Lưu denom.
    denom = area_a + area_b - inter
    # Chỉ xử lý khi điều kiện đúng.
    if denom <= 0:
        # Trả về giá trị đã tính.
        return 0.0
    # Trả về giá trị đã tính.
    return inter / denom


# Định nghĩa match_predictions_to_gt.
def match_predictions_to_gt(
    pred_boxes: np.ndarray,
    pred_labels: list[str],
    pred_scores: list[float],
    gt_boxes: np.ndarray,
    gt_labels: list[str],
    iou_threshold: float = 0.5,
) -> tuple[list[tuple[int, int]], list[int], list[int]]:
    # Chỉ xử lý khi điều kiện đúng.
    if len(pred_boxes) == 0 or len(gt_boxes) == 0:
        # Trả về giá trị đã tính.
        return [], list(range(len(pred_boxes))), list(range(len(gt_boxes)))

    # Lưu order.
    order = np.argsort(-np.asarray(pred_scores))
    # Lưu matched_gt.
    matched_gt: set[int] = set()
    # Lưu matches.
    matches: list[tuple[int, int]] = []
    # Lưu false_pos.
    false_pos: list[int] = []

    # Duyệt từng phần tử để xử lý.
    for pred_idx in order:
        # Lưu best_gt.
        best_gt = -1
        # Lưu best_iou.
        best_iou = 0.0
        # Duyệt từng phần tử để xử lý.
        for gt_idx, gt_box in enumerate(gt_boxes):
            # Chỉ xử lý khi điều kiện đúng.
            if gt_idx in matched_gt:
                # Bỏ qua phần tử hiện tại.
                continue
            # Lưu cur_iou.
            cur_iou = iou_xyxy(pred_boxes[pred_idx], gt_box)
            # Chỉ xử lý khi điều kiện đúng.
            if cur_iou > best_iou:
                # Lưu best_iou.
                best_iou = cur_iou
                # Lưu best_gt.
                best_gt = gt_idx
        # Chỉ xử lý khi điều kiện đúng.
        if best_gt >= 0 and best_iou >= iou_threshold:
            # Đánh dấu GT đã được ghép.
            matched_gt.add(best_gt)
            # Thêm phần tử vào danh sách.
            matches.append((int(pred_idx), int(best_gt)))
        else:
            # Thêm phần tử vào danh sách.
            false_pos.append(int(pred_idx))

    # Lưu false_neg.
    false_neg = [gt_idx for gt_idx in range(len(gt_boxes)) if gt_idx not in matched_gt]
    # Trả về giá trị đã tính.
    return matches, false_pos, false_neg


# Định nghĩa save_confusion_matrix.
def save_confusion_matrix(
    cm: np.ndarray,
    labels: list[str],
    output_path: Path,
    title: str,
) -> None:
    # Tạo thư mục nếu chưa có.
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Tạo figure.
    plt.figure(figsize=(max(8, len(labels) * 0.55), max(6, len(labels) * 0.45)))
    # Hiển thị ảnh trên subplot.
    plt.imshow(cm, interpolation="nearest", cmap="Blues")
    # Đặt tiêu đề.
    plt.title(title)
    # Thêm thanh màu để nhìn rõ mức giá trị trong ma trận.
    plt.colorbar()
    # Lưu tick_marks.
    tick_marks = np.arange(len(labels))
    # Đặt nhãn trục x.
    plt.xticks(tick_marks, labels, rotation=60, ha="right")
    # Đặt nhãn trục y.
    plt.yticks(tick_marks, labels)
    # Đặt nhãn trục x.
    plt.xlabel("Predicted")
    # Đặt nhãn trục y.
    plt.ylabel("Ground truth")
    # Lưu threshold.
    threshold = cm.max() * 0.6 if cm.size and cm.max() > 0 else 0.0
    # Duyệt từng phần tử để xử lý.
    for i in range(cm.shape[0]):
        # Duyệt từng phần tử để xử lý.
        for j in range(cm.shape[1]):
            # Lưu value.
            value = cm[i, j]
            # Chỉ xử lý khi điều kiện đúng.
            if value > 0:
                # Ghi số lượng lên ô tương ứng.
                plt.text(j, i, int(value), ha="center", va="center", color="white" if value > threshold else "black", fontsize=8)
    # Căn layout cho gọn.
    plt.tight_layout()
    # Lưu hình.
    plt.savefig(output_path, dpi=160)
    # Đóng figure.
    plt.close()


# Định nghĩa save_detection_confusion_matrix.
def save_detection_confusion_matrix(
    dataset_root: Path,
    image_paths: list[Path],
    predict_fn,
    classes: list[str],
    output_path: Path,
    iou_threshold: float = 0.5,
    score_threshold: float = 0.3,
) -> None:
    # Lưu labels.
    labels = classes + ["background"]
    # Lưu matrix.
    matrix = np.zeros((len(labels), len(labels)), dtype=int)
    # Lưu class_to_idx.
    class_to_idx = {name: idx for idx, name in enumerate(classes)}
    # Lưu background.
    background = len(classes)

    # Duyệt từng phần tử để xử lý.
    for image_path in image_paths:
        # Lưu gt_boxes, gt_labels.
        gt_boxes, gt_labels = _get_gt_for_image(dataset_root, image_path)
        # Lưu pred_boxes, pred_labels, pred_scores.
        pred_boxes, pred_labels, pred_scores = predict_fn(image_path)
        # Lưu keep.
        keep = [idx for idx, score in enumerate(pred_scores) if score >= score_threshold]
        # Lưu pred_boxes.
        pred_boxes = pred_boxes[keep] if len(keep) else np.zeros((0, 4), dtype=np.float32)
        # Lưu pred_labels.
        pred_labels = [pred_labels[idx] for idx in keep]
        # Lưu pred_scores.
        pred_scores = [pred_scores[idx] for idx in keep]

        # Lưu matches, false_pos, false_neg.
        matches, false_pos, false_neg = match_predictions_to_gt(pred_boxes, pred_labels, pred_scores, gt_boxes, gt_labels, iou_threshold=iou_threshold)

        # Duyệt từng phần tử để xử lý.
        for pred_idx, gt_idx in matches:
            # Lưu gt_label.
            gt_label = gt_labels[gt_idx]
            # Lưu pred_label.
            pred_label = pred_labels[pred_idx]
            # Cập nhật value.
            matrix[class_to_idx.get(gt_label, background), class_to_idx.get(pred_label, background)] += 1
        # Duyệt từng phần tử để xử lý.
        for pred_idx in false_pos:
            # Lưu pred_label.
            pred_label = pred_labels[pred_idx]
            # Cập nhật value.
            matrix[background, class_to_idx.get(pred_label, background)] += 1
        # Duyệt từng phần tử để xử lý.
        for gt_idx in false_neg:
            # Lưu gt_label.
            gt_label = gt_labels[gt_idx]
            # Cập nhật value.
            matrix[class_to_idx.get(gt_label, background), background] += 1

    # Gọi save_confusion_matrix.
    save_confusion_matrix(matrix, labels, output_path, output_path.stem.replace("_", " ").title())


# Định nghĩa save_threshold_metric_curve.
def save_threshold_metric_curve(
    dataset_root: Path,
    image_paths: list[Path],
    predict_fn,
    output_path: Path,
    title: str,
) -> None:
    # Lưu thresholds.
    thresholds = np.linspace(0.05, 0.95, 19)
    # Lưu precisions.
    precisions = []
    # Lưu recalls.
    recalls = []
    # Lưu f1_scores.
    f1_scores = []

    # Duyệt từng phần tử để xử lý.
    for threshold in thresholds:
        # Lưu tp.
        tp = fp = fn = 0
        # Duyệt từng phần tử để xử lý.
        for image_path in image_paths:
            # Lưu gt_boxes, gt_labels.
            gt_boxes, gt_labels = _get_gt_for_image(dataset_root, image_path)
            # Lưu pred_boxes, pred_labels, pred_scores.
            pred_boxes, pred_labels, pred_scores = predict_fn(image_path)
            # Lưu keep.
            keep = [idx for idx, score in enumerate(pred_scores) if score >= threshold]
            # Lưu pred_boxes.
            pred_boxes = pred_boxes[keep] if len(keep) else np.zeros((0, 4), dtype=np.float32)
            # Lưu pred_labels.
            pred_labels = [pred_labels[idx] for idx in keep]
            # Lưu pred_scores.
            pred_scores = [pred_scores[idx] for idx in keep]
            # Lưu matches, false_pos, false_neg.
            matches, false_pos, false_neg = match_predictions_to_gt(pred_boxes, pred_labels, pred_scores, gt_boxes, gt_labels)
            # Cập nhật tp.
            tp += len(matches)
            # Cập nhật fp.
            fp += len(false_pos)
            # Cập nhật fn.
            fn += len(false_neg)
        # Lưu precision.
        precision = tp / max(1, tp + fp)
        # Lưu recall.
        recall = tp / max(1, tp + fn)
        # Lưu f1.
        f1 = (2 * precision * recall) / max(1e-9, precision + recall)
        # Thêm phần tử vào danh sách.
        precisions.append(precision)
        # Thêm phần tử vào danh sách.
        recalls.append(recall)
        # Thêm phần tử vào danh sách.
        f1_scores.append(f1)

    # Tạo thư mục nếu chưa có.
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Tạo figure.
    plt.figure(figsize=(9, 5))
    # Vẽ đường biểu diễn.
    plt.plot(thresholds, precisions, label="Precision")
    # Vẽ đường biểu diễn.
    plt.plot(thresholds, recalls, label="Recall")
    # Vẽ đường biểu diễn.
    plt.plot(thresholds, f1_scores, label="F1")
    # Đặt tiêu đề.
    plt.title(title)
    # Đặt nhãn trục x.
    plt.xlabel("Confidence threshold")
    # Đặt nhãn trục y.
    plt.ylabel("Score")
    # Bật lưới.
    plt.grid(alpha=0.2)
    # Hiển thị chú giải.
    plt.legend()
    # Căn layout cho gọn.
    plt.tight_layout()
    # Lưu hình.
    plt.savefig(output_path, dpi=160)
    # Đóng figure.
    plt.close()


# Định nghĩa save_prediction_sweep.
def save_prediction_sweep(
    image_paths: list[Path],
    predict_fn,
    output_dir: Path,
    prefix: str,
    min_score: float = 0.60,
) -> list[Path]:
    # Tạo thư mục nếu chưa có.
    output_dir.mkdir(parents=True, exist_ok=True)
    # Lưu outputs.
    outputs: list[Path] = []
    # Duyệt từng phần tử để xử lý.
    for idx, image_path in enumerate(image_paths, start=1):
        # Lưu boxes, labels, scores.
        boxes, labels, scores = predict_fn(image_path)
        # Lưu output_path.
        output_path = output_dir / f"{prefix}_prediction_{idx}.png"
        # Gọi save_prediction_image.
        save_prediction_image(image_path, boxes, labels, scores, output_path, min_score=min_score)
        # Thêm phần tử vào danh sách.
        outputs.append(output_path)
    # Trả về giá trị đã tính.
    return outputs


# Định nghĩa save_ground_truth_sweep.
def save_ground_truth_sweep(
    dataset_root: Path,
    image_paths: list[Path],
    output_dir: Path,
    prefix: str = "ground_truth",
) -> list[Path]:
    # Tạo thư mục nếu chưa có.
    output_dir.mkdir(parents=True, exist_ok=True)
    # Lưu classes.
    classes = read_classes(dataset_root)
    # Lưu outputs.
    outputs: list[Path] = []
    # Duyệt từng phần tử để xử lý.
    for idx, image_path in enumerate(image_paths, start=1):
        # Lưu split.
        split = image_path.parent.name
        # Lưu annotations.
        annotations = load_split_annotations(dataset_root, split)
        # Lưu image.
        image = cv2.imread(str(image_path))
        # Chỉ xử lý khi điều kiện đúng.
        if image is None:
            # Bỏ qua phần tử hiện tại.
            continue
        # Lưu labeled.
        labeled = draw_boxes(image, annotations.get(image_path.name, []), classes)
        # Lưu output_path.
        output_path = output_dir / f"{prefix}_{idx}.png"
        # Ghi ảnh ra đĩa.
        cv2.imwrite(str(output_path), labeled)
        # Thêm phần tử vào danh sách.
        outputs.append(output_path)
    # Trả về giá trị đã tính.
    return outputs


# Định nghĩa assemble_report_panels.
def assemble_report_panels(dataset_root: Path, figures_dir: Path) -> None:
    # Tạo thư mục nếu chưa có.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Lưu comparison_images.
    comparison_images = select_comparison_test_images(dataset_root, count=5)
    # Lưu failure_images.
    failure_images = comparison_images[-2:]

    # Lưu yolo_preds.
    yolo_preds = [figures_dir / f"yolo_prediction_{idx}.png" for idx in range(1, len(comparison_images) + 1)]
    # Lưu detr_preds.
    detr_preds = [figures_dir / f"detr_prediction_{idx}.png" for idx in range(1, len(comparison_images) + 1)]
    # Lưu frcnn_preds.
    frcnn_preds = [figures_dir / f"faster_rcnn_prediction_{idx}.png" for idx in range(1, len(comparison_images) + 1)]

    # Chỉ ghép panel khi cả 3 mô hình đã xuất prediction xong.
    if not all(path.exists() for path in yolo_preds + detr_preds + frcnn_preds):
        return

    # Ghép ảnh so sánh giữa 3 mô hình trên cùng một bộ test.
    save_comparison_panels(
        comparison_images,
        {
            "YOLO": yolo_preds,
            "DETR": detr_preds,
            "Third Model": frcnn_preds,
        },
        figures_dir,
        "comparison_case",
    )

    # Lưu ảnh ground-truth cho 2 case khó nhất.
    gt_paths = save_ground_truth_sweep(dataset_root, failure_images, figures_dir, prefix="failure_ground_truth")
    if len(gt_paths) != len(failure_images):
        return

    # Ghép panel lỗi chỉ khi đủ prediction của cả 3 mô hình.
    yolo_failures = [figures_dir / f"yolo_prediction_{comparison_images.index(img) + 1}.png" for img in failure_images]
    detr_failures = [figures_dir / f"detr_prediction_{comparison_images.index(img) + 1}.png" for img in failure_images]
    frcnn_failures = [figures_dir / f"faster_rcnn_prediction_{comparison_images.index(img) + 1}.png" for img in failure_images]
    if not all(path.exists() for path in yolo_failures + detr_failures + frcnn_failures):
        return

    save_failure_panels(
        failure_images,
        gt_paths,
        {
            "YOLO": yolo_failures,
            "DETR": detr_failures,
            "Third Model": frcnn_failures,
        },
        figures_dir,
        "failure_case",
    )


# Định nghĩa copy_if_exists.
def copy_if_exists(src: Path, dst: Path) -> bool:
    # Chỉ xử lý khi điều kiện đúng.
    if not src.exists():
        # Trả về giá trị đã tính.
        return False
    # Tạo thư mục nếu chưa có.
    dst.parent.mkdir(parents=True, exist_ok=True)
    # Sao chép file kết quả.
    shutil.copy2(src, dst)
    # Trả về giá trị đã tính.
    return True


# Định nghĩa copy_yolo_report_artifacts.
def copy_yolo_report_artifacts(run_dir: Path, figures_dir: Path) -> None:
    # Lưu mapping.
    mapping = {
        "results.png": "yolo_training_curve.png",
        "confusion_matrix.png": "yolo_confusion_matrix.png",
        "confusion_matrix_normalized.png": "yolo_confusion_matrix_normalized.png",
        "PR_curve.png": "yolo_PR_curve.png",
        "P_curve.png": "yolo_P_curve.png",
        "R_curve.png": "yolo_R_curve.png",
        "F1_curve.png": "yolo_F1_curve.png",
    }
    # Duyệt từng phần tử để xử lý.
    for src_name, dst_name in mapping.items():
        # Gọi copy_if_exists.
        copy_if_exists(run_dir / src_name, figures_dir / dst_name)


# Định nghĩa save_comparison_panels.
def save_comparison_panels(
    original_paths: list[Path],
    model_prediction_paths: dict[str, list[Path]],
    output_dir: Path,
    prefix: str,
) -> list[Path]:
    # Tạo thư mục nếu chưa có.
    output_dir.mkdir(parents=True, exist_ok=True)
    # Lưu outputs.
    outputs: list[Path] = []
    # Lưu model_names.
    model_names = list(model_prediction_paths.keys())
    # Duyệt từng phần tử để xử lý.
    for idx, original in enumerate(original_paths, start=1):
        # Tạo figure.
        plt.figure(figsize=(16, 4))
        # Lưu panel_paths.
        panel_paths = [original] + [model_prediction_paths[name][idx - 1] for name in model_names]
        # Lưu titles.
        titles = ["Original"] + model_names
        # Duyệt từng phần tử để xử lý.
        for col, (panel_path, title) in enumerate(zip(panel_paths, titles), start=1):
            # Lưu ax.
            ax = plt.subplot(1, len(panel_paths), col)
            # Lưu image.
            image = cv2.imread(str(panel_path))
            # Chỉ xử lý khi điều kiện đúng.
            if image is None:
                # Tắt trục để ảnh gọn hơn.
                ax.axis("off")
                # Bỏ qua phần tử hiện tại.
                continue
            # Hiển thị ảnh trên subplot.
            ax.imshow(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
            # Đặt tiêu đề cho subplot.
            ax.set_title(title)
            # Tắt trục để ảnh gọn hơn.
            ax.axis("off")
        # Căn layout cho gọn.
        plt.tight_layout()
        # Lưu output_path.
        output_path = output_dir / f"{prefix}_{idx}.png"
        # Lưu hình.
        plt.savefig(output_path, dpi=160)
        # Đóng figure.
        plt.close()
        # Thêm phần tử vào danh sách.
        outputs.append(output_path)
    # Trả về giá trị đã tính.
    return outputs


# Định nghĩa save_failure_panels.
def save_failure_panels(
    original_paths: list[Path],
    gt_paths: list[Path],
    model_prediction_paths: dict[str, list[Path]],
    output_dir: Path,
    prefix: str,
) -> list[Path]:
    # Ghép ảnh gốc, GT và dự đoán để soi lỗi của từng mô hình.
    """Save failure case panels with original, ground truth, and model predictions."""

    # Tạo thư mục nếu chưa có.
    output_dir.mkdir(parents=True, exist_ok=True)
    # Lưu outputs.
    outputs: list[Path] = []
    # Lưu model_names.
    model_names = list(model_prediction_paths.keys())
    # Duyệt từng phần tử để xử lý.
    for idx, (orig_path, gt_path) in enumerate(zip(original_paths, gt_paths), start=1):
        # Tạo figure.
        plt.figure(figsize=(18, 4))
        # Lưu panel_paths.
        panel_paths = [orig_path, gt_path] + [model_prediction_paths[name][idx - 1] for name in model_names]
        # Lưu titles.
        titles = ["Original", "Ground Truth"] + model_names
        # Duyệt từng phần tử để xử lý.
        for col, (panel_path, title) in enumerate(zip(panel_paths, titles), start=1):
            # Lưu ax.
            ax = plt.subplot(1, len(panel_paths), col)
            # Lưu image.
            image = cv2.imread(str(panel_path))
            # Chỉ xử lý khi điều kiện đúng.
            if image is None:
                # Tắt trục để ảnh gọn hơn.
                ax.axis("off")
                # Bỏ qua phần tử hiện tại.
                continue
            # Hiển thị ảnh trên subplot.
            ax.imshow(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
            # Đặt tiêu đề cho subplot.
            ax.set_title(title)
            # Tắt trục để ảnh gọn hơn.
            ax.axis("off")
        # Căn layout cho gọn.
        plt.tight_layout()
        # Lưu output_path.
        output_path = output_dir / f"{prefix}_{idx}.png"
        # Lưu hình.
        plt.savefig(output_path, dpi=160)
        # Đóng figure.
        plt.close()
        # Thêm phần tử vào danh sách.
        outputs.append(output_path)
    # Trả về giá trị đã tính.
    return outputs


# Định nghĩa save_detr_training_figures.
def save_detr_training_figures(trainer, figures_dir: Path) -> None:
    # Vẽ loss curve của DETR từ log history của Trainer.

    # Lưu history.
    history = getattr(trainer.state, "log_history", [])
    # Lưu train_steps.
    train_steps: list[float] = []
    # Lưu train_loss.
    train_loss: list[float] = []
    # Lưu eval_epochs.
    eval_epochs: list[float] = []
    # Lưu eval_loss.
    eval_loss: list[float] = []

    # Duyệt từng phần tử để xử lý.
    for row in history:
        # Lưu epoch.
        epoch = row.get("epoch")
        # Lưu step.
        step = row.get("step")
        # Chỉ xử lý khi điều kiện đúng.
        if epoch is None:
            # Bỏ qua phần tử hiện tại.
            continue
        # Chỉ xử lý khi điều kiện đúng.
        if "loss" in row:
            # Thêm phần tử vào danh sách.
            train_steps.append(float(step if step is not None else epoch))
            # Thêm phần tử vào danh sách.
            train_loss.append(float(row["loss"]))
        # Chỉ xử lý khi điều kiện đúng.
        if "eval_loss" in row:
            # Thêm phần tử vào danh sách.
            eval_epochs.append(float(epoch))
            # Thêm phần tử vào danh sách.
            eval_loss.append(float(row["eval_loss"]))

    # Chỉ xử lý khi điều kiện đúng.
    if not train_loss and not eval_loss:
        # Trả về giá trị đã tính.
        return

    # Tạo thư mục nếu chưa có.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Tạo figure.
    plt.figure(figsize=(9, 4.8))
    # Chỉ xử lý khi điều kiện đúng.
    if train_loss:
        # Vẽ đường biểu diễn.
        plt.plot(train_steps, train_loss, marker="o", label="train loss")
    # Chỉ xử lý khi điều kiện đúng.
    if eval_loss:
        # Vẽ đường biểu diễn.
        plt.plot(eval_epochs, eval_loss, marker="s", label="eval loss")
    # Đặt tiêu đề.
    plt.title("DETR training curve")
    # Đặt nhãn trục x.
    plt.xlabel("Training step / epoch")
    # Đặt nhãn trục y.
    plt.ylabel("Loss")
    # Bật lưới.
    plt.grid(alpha=0.2)
    # Hiển thị chú giải.
    plt.legend()
    # Căn layout cho gọn.
    plt.tight_layout()
    # Lưu hình.
    plt.savefig(figures_dir / "detr_training_curve.png", dpi=160)
    # Đóng figure.
    plt.close()


# Định nghĩa save_faster_rcnn_training_figures.
def save_faster_rcnn_training_figures(loss_history: list[float], figures_dir: Path) -> None:
    # Vẽ đường cong loss của Faster R-CNN để đưa vào báo cáo.

    # Chỉ xử lý khi điều kiện đúng.
    if not loss_history:
        # Trả về giá trị đã tính.
        return

    # Tạo thư mục nếu chưa có.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Lưu epochs.
    epochs = list(range(1, len(loss_history) + 1))
    # Tạo figure.
    plt.figure(figsize=(9, 4.8))
    # Vẽ đường biểu diễn.
    plt.plot(epochs, loss_history, marker="o", color="#1f77b4")
    # Đặt tiêu đề.
    plt.title("Faster R-CNN training loss")
    # Đặt nhãn trục x.
    plt.xlabel("Epoch")
    # Đặt nhãn trục y.
    plt.ylabel("Loss")
    # Bật lưới.
    plt.grid(alpha=0.2)
    # Căn layout cho gọn.
    plt.tight_layout()
# Định nghĩa generate_dataset_report_figures.
def generate_dataset_report_figures(dataset_root: Path, figures_dir: Path) -> None:
    # Sinh các hình mô tả dataset để đưa vào báo cáo.

    # Tạo thư mục nếu chưa có.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Đọc danh sách class để gắn nhãn lên ảnh.
    classes = read_classes(dataset_root)
    # Chọn 4 ảnh mẫu từ các split khác nhau.
    sample_images = select_dataset_sample_images(dataset_root, count=4)
    # Danh sách ảnh mẫu đã được vẽ bbox.
    sample_paths: list[Path] = []
    # Chú thích ngắn cho từng ảnh trong grid.
    captions: list[str] = []

    # Vẽ bbox cho từng ảnh mẫu và lưu ra thư mục figures.
    for idx, image_path in enumerate(sample_images, start=1):
        # Xác định split của ảnh để đọc annotation đúng chỗ.
        split = image_path.parent.name
        # Lấy annotation của split hiện tại.
        annotations = load_split_annotations(dataset_root, split)
        # Đọc ảnh gốc để vẽ bbox.
        image = cv2.imread(str(image_path))
        # Bỏ qua nếu ảnh lỗi.
        if image is None:
            continue
        # Chèn bbox và nhãn class lên ảnh.
        labeled = draw_boxes(image, annotations.get(image_path.name, []), classes)
        # Lưu từng ảnh mẫu riêng lẻ để tiện dùng lại trong báo cáo.
        output_path = figures_dir / f"dataset_sample_{idx}.png"
        cv2.imwrite(str(output_path), labeled)
        sample_paths.append(output_path)
        captions.append(f"{split} sample {idx}")

    # Ghép các ảnh mẫu thành một grid gọn cho báo cáo.
    if sample_paths:
        save_image_grid(sample_paths, figures_dir / "dataset_samples_grid.png", captions=captions, ncols=2)


# Định nghĩa predict_yolo_boxes.
def predict_yolo_boxes(model, image_path: Path) -> tuple[np.ndarray, list[str], list[float]]:
    # Dự đoán bbox bằng mô hình YOLO đã fine-tune.

    # Lưu result.
    result = model.predict(source=str(image_path), conf=0.60, verbose=False)[0]
    # Lưu boxes.
    boxes = result.boxes.xyxy.detach().cpu().numpy() if len(result.boxes) else np.zeros((0, 4), dtype=np.float32)
    # Lưu label_ids.
    label_ids = result.boxes.cls.detach().cpu().numpy().astype(int) if len(result.boxes) else np.array([], dtype=int)
    # Lưu scores.
    scores = result.boxes.conf.detach().cpu().tolist() if len(result.boxes) else []
    # Lưu classes.
    classes = model.names
    # Lưu labels.
    labels = [classes[int(label_id)] if isinstance(classes, dict) else classes[int(label_id)] for label_id in label_ids]
    # Trả về giá trị đã tính.
    return boxes, labels, scores


# Định nghĩa predict_torchvision_boxes.
def predict_torchvision_boxes(
    model,
    image_path: Path,
    classes: list[str],
    score_threshold: float = 0.60,
) -> tuple[np.ndarray, list[str], list[float]]:
    # Dự đoán bbox bằng detector của TorchVision.

    # Lưu image.
    image = Image.open(image_path).convert("RGB")
    # Lưu image_tensor.
    image_tensor = np.array(image)
    # Import thư viện hỗ trợ.
    import torch

    # Lưu tensor.
    tensor = torch.as_tensor(image_tensor, dtype=torch.float32).permute(2, 0, 1) / 255.0
    # Gọi eval.
    model.eval()
    # Đọc ảnh bằng context manager để tự đóng file sau khi dùng.
    with torch.no_grad():
        # Lưu outputs.
        outputs = model([tensor.to(next(model.parameters()).device)])[0]
    # Lưu scores.
    scores = outputs["scores"].detach().cpu()
    # Lưu keep.
    keep = scores >= score_threshold
    # Lưu boxes.
    boxes = outputs["boxes"].detach().cpu().numpy()[keep.numpy()]
    # Lưu label_ids.
    label_ids = outputs["labels"].detach().cpu().numpy()[keep.numpy()]
    # Lưu labels.
    labels = [classes[int(label_id) - 1] for label_id in label_ids]
    # Lưu kept_scores.
    kept_scores = scores[keep].tolist()
    # Trả về giá trị đã tính.
    return boxes, labels, kept_scores


# Định nghĩa predict_detr_boxes.
def predict_detr_boxes(model, processor, image_path: Path, score_threshold: float = 0.60) -> tuple[np.ndarray, list[str], list[float]]:
    # Dự đoán bbox bằng DETR.

    # Lưu image.
    image = Image.open(image_path).convert("RGB")
    # Import thư viện hỗ trợ.
    import torch

    # Lưu device.
    device = next(model.parameters()).device
    # Lưu inputs.
    inputs = processor(images=image, return_tensors="pt").to(device)
    # Đọc ảnh bằng context manager để tự đóng file sau khi dùng.
    with torch.no_grad():
        # Lưu outputs.
        outputs = model(**inputs)
    # Lưu target_sizes.
    target_sizes = torch.tensor([image.size[::-1]], device=device)
    # Lưu results.
    results = processor.post_process_object_detection(outputs, threshold=score_threshold, target_sizes=target_sizes)[0]
    # Lưu boxes.
    boxes = results["boxes"].detach().cpu().numpy()
    # Lưu labels.
    labels = [model.config.id2label.get(int(label), str(int(label))) for label in results["labels"].detach().cpu().numpy()]
    # Lưu scores.
    scores = results["scores"].detach().cpu().tolist()
    # Trả về giá trị đã tính.
    return boxes, labels, scores


# Định nghĩa make_figures.
def make_figures(dataset_root: Path, figures_dir: Path) -> None:
    # Tạo toàn bộ hình thống kê dataset cho phần báo cáo.
    figures_dir.mkdir(parents=True, exist_ok=True)
    # Thống kê số ảnh và số bbox của từng split.
    stats = dataset_stats(dataset_root)
    # Lấy danh sách class để phục vụ các biểu đồ phía dưới.
    classes = stats["classes"]
    # Sinh các ảnh mẫu có ground-truth bbox.
    generate_dataset_report_figures(dataset_root, figures_dir)
    # Chọn một ảnh train đầu tiên để minh họa ground truth.
    first_image_name = next(iter(load_split_annotations(dataset_root, "train")))
    # Lấy toàn bộ annotation của tập train.
    train_annotations = load_split_annotations(dataset_root, "train")
    # Đọc ảnh gốc để vẽ ground truth.
    image = cv2.imread(str(dataset_root / "train" / first_image_name))
    # Vẽ bbox ground truth lên ảnh.
    labeled = draw_boxes(image, train_annotations[first_image_name], classes)
    cv2.imwrite(str(figures_dir / "sample_ground_truth.png"), labeled)
    # Vẽ biểu đồ số ảnh và số bbox theo từng split.
    split_names = list(stats["splits"].keys())
    image_counts = [stats["splits"][split]["images"] for split in split_names]
    box_counts = [stats["splits"][split]["boxes"] for split in split_names]
    # Tạo figure.
    plt.figure(figsize=(7, 4))
    # Lưu x_positions.
    x_positions = np.arange(len(split_names))
    # Vẽ cột biểu đồ.
    plt.bar(x_positions - 0.18, image_counts, width=0.36, label="Images")
    # Vẽ cột biểu đồ.
    plt.bar(x_positions + 0.18, box_counts, width=0.36, label="Boxes")
    # Đặt nhãn trục x.
    plt.xticks(x_positions, split_names)
    # Đặt nhãn trục y.
    plt.ylabel("Count")
    # Đặt tiêu đề.
    plt.title("Chess Pieces split distribution")
    # Hiển thị chú giải.
    plt.legend()
    # Căn layout cho gọn.
    plt.tight_layout()
    # Lưu hình.
    plt.savefig(figures_dir / "split_distribution.png", dpi=160)
    # Đóng figure.
    plt.close()
    # Gộp số bbox của từng class trên cả 3 split.
    total_per_class = np.zeros(len(classes), dtype=int)
    for split in SPLITS:
        counts = stats["splits"][split]["class_counts"]
        total_per_class += np.array([counts[name] for name in classes])
    # Tạo figure.
    plt.figure(figsize=(10, 5))
    # Vẽ cột biểu đồ.
    plt.bar(classes, total_per_class)
    # Đặt nhãn trục x.
    plt.xticks(rotation=55, ha="right")
    # Đặt nhãn trục y.
    plt.ylabel("Bounding boxes")
    # Đặt tiêu đề.
    plt.title("Class distribution")
    # Căn layout cho gọn.
    plt.tight_layout()
    # Lưu hình.
    plt.savefig(figures_dir / "class_distribution.png", dpi=160)
    # Đóng figure.
    plt.close()
    # Ghi thống kê dataset ra JSON để dùng lại khi viết báo cáo.
    (figures_dir / "dataset_stats.json").write_text(json.dumps(stats, indent=2), encoding="utf-8")


# Dataset PyTorch dùng cho Faster R-CNN.
class ChessCocoDataset:
    # Trả về ảnh và target theo format mà TorchVision yêu cầu.

    # Định nghĩa __init__.
    def __init__(self, dataset_root: Path, split: str):
        # Lưu dataset_root.
        self.dataset_root = dataset_root
        # Lưu split.
        self.split = split
        # Lưu images.
        self.images = sorted((dataset_root / split).glob("*.jpg"))
        # Lưu annotations.
        self.annotations = load_split_annotations(dataset_root, split)

    # Định nghĩa __len__.
    def __len__(self) -> int:
        # Trả về giá trị đã tính.
        return len(self.images)

    # Định nghĩa __getitem__.
    def __getitem__(self, index: int):
        # Import thư viện hỗ trợ.
        import torch
        # Lưu image_path.
        image_path = self.images[index]
        # Lưu image.
        image = Image.open(image_path).convert("RGB")
        # Lưu image_tensor.
        image_tensor = torch.as_tensor(np.array(image), dtype=torch.float32).permute(2, 0, 1) / 255.0
        # Lưu records.
        records = self.annotations.get(image_path.name, [])
        # Lưu boxes.
        boxes = torch.as_tensor([[r.x1, r.y1, r.x2, r.y2] for r in records], dtype=torch.float32)
        # Lưu labels.
        labels = torch.as_tensor([r.class_id + 1 for r in records], dtype=torch.int64)
        # Lưu target.
        target = {"boxes": boxes, "labels": labels, "image_id": torch.tensor([index])}
        # Trả về giá trị đã tính.
        return image_tensor, target


# Gom batch cho detection vì mỗi ảnh có số bbox khác nhau.
def collate_detection_batch(batch):
    # Trả về giá trị đã tính.
    return tuple(zip(*batch))


# Định nghĩa train_yolo.
def train_yolo(data_yaml: Path, epochs: int, imgsz: int, project: Path, figures_dir: Path, dataset_root: Path) -> None:
    # Ultralytics có thể chạm vào ray nên ta chặn trước để tránh lỗi môi trường.
    import sys

    # Ép ray thành None để YOLO không cố khởi tạo phần phụ trợ không cần thiết.
    sys.modules["ray"] = None
    # Chỉ import YOLO khi thật sự train.
    from ultralytics import YOLO
    # Chọn device an toàn cho máy hiện tại.
    device = get_safe_torch_device()
    # Đọc lại class để dùng cho các bước xuất báo cáo.
    classes = read_classes(dataset_root)
    # Khởi tạo YOLO base model để fine-tune.
    model = YOLO("yolov8n.pt")
    # Train mô hình trên dataset đã chuyển sang format YOLO.
    model.train(
        data=str(data_yaml),
        epochs=epochs,
        imgsz=imgsz,
        project=str(project),
        name="yolo_chess",
        pretrained=True,
        device=device.type,
    )
    # Đánh giá trên tập test để có số liệu tổng hợp.
    metrics = model.val(data=str(data_yaml), split="test", imgsz=imgsz, device=device.type)
    # Lưu log metric để tra cứu nhanh sau khi chạy.
    (project / "yolo_metrics.txt").write_text(str(metrics), encoding="utf-8")
    # Tìm thư mục output thật sự của lần train này.
    run_dir = Path(getattr(getattr(model, "trainer", None), "save_dir", project / "yolo_chess"))
    # Copy các ảnh curve/confusion matrix của YOLO vào thư mục báo cáo.
    copy_yolo_report_artifacts(run_dir, figures_dir)
    # Chọn 5 ảnh test để vẽ prediction mẫu.
    test_images = select_comparison_test_images(dataset_root, count=5)
    # Xuất loạt ảnh dự đoán để so sánh giữa 3 mô hình.
    save_prediction_sweep(
        test_images,
        lambda image_path: predict_yolo_boxes(model, image_path),
        figures_dir,
        "yolo",
        min_score=0.3,
        max_boxes=8,
    )
    # Dùng toàn bộ tập test để tính confusion matrix và metric curve.
    test_all = sorted((dataset_root / "test").glob("*.jpg"))
    # Vẽ confusion matrix trên tập test.
    save_detection_confusion_matrix(
        dataset_root,
        test_all,
        lambda image_path: predict_yolo_boxes(model, image_path),
        classes,
        figures_dir / "yolo_confusion_matrix.png",
    )
    # Vẽ đường precision/recall theo ngưỡng confidence.
    save_threshold_metric_curve(
        dataset_root,
        test_all,
        lambda image_path: predict_yolo_boxes(model, image_path),
        figures_dir / "yolo_eval_curve.png",
        "YOLO evaluation curve",
    )
    # Ghép thêm panel so sánh để báo cáo có đủ ảnh minh họa.
    assemble_report_panels(dataset_root, figures_dir)


# Định nghĩa train_faster_rcnn.
def train_faster_rcnn(dataset_root: Path, epochs: int, batch_size: int, output_dir: Path, figures_dir: Path) -> None:
    # Faster R-CNN dùng PyTorch/TorchVision nên chỉ import khi cần train.
    import torch
    # Loader cho dataset detection.
    from torch.utils.data import DataLoader
    # Model pretrain và weights mặc định của TorchVision.
    from torchvision.models.detection import FasterRCNN_ResNet50_FPN_Weights, fasterrcnn_resnet50_fpn
    # Thay đầu ra classifier cho đúng số class của bài toán.
    from torchvision.models.detection.faster_rcnn import FastRCNNPredictor
    # Chọn device phù hợp với máy hiện tại.
    device = get_safe_torch_device()
    # Đọc danh sách class để cấu hình predictor.
    classes = read_classes(dataset_root)
    # Nạp backbone pretrain rồi fine-tune trên dataset chess.
    model = fasterrcnn_resnet50_fpn(weights=FasterRCNN_ResNet50_FPN_Weights.DEFAULT)
    # Lấy số đặc trưng đầu vào của lớp classifier cũ.
    in_features = model.roi_heads.box_predictor.cls_score.in_features
    # Thay lớp dự đoán cũ bằng lớp mới khớp số class cần học.
    model.roi_heads.box_predictor = FastRCNNPredictor(in_features, len(classes) + 1)
    # Đưa model lên device để train.
    model.to(device)
    # Tạo loader cho tập train.
    train_loader = DataLoader(ChessCocoDataset(dataset_root, "train"), batch_size=batch_size, shuffle=True, collate_fn=collate_detection_batch)
    # AdamW là lựa chọn ổn cho fine-tuning detection.
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-4, weight_decay=1e-4)
    # Tạo nơi lưu weight và figure.
    output_dir.mkdir(parents=True, exist_ok=True)
    # Lưu lịch sử loss để vẽ đường cong train.
    loss_history: list[float] = []
    # Train theo từng epoch.
    for epoch in range(epochs):
        # Bật chế độ train.
        model.train()
        # Cộng dồn loss của các batch trong epoch hiện tại.
        running_loss = 0.0
        # Đo thời gian một epoch chạy mất bao lâu.
        start = time.perf_counter()
        # Duyệt từng batch của tập train.
        for images, targets in train_loader:
            # Đưa ảnh lên đúng device.
            images = [image.to(device) for image in images]
            # Đưa target của từng ảnh lên đúng device.
            targets = [{key: value.to(device) for key, value in target.items()} for target in targets]
            # Forward để lấy các thành phần loss của detector.
            losses = model(images, targets)
            # Cộng các loss con thành một loss tổng.
            loss = sum(value for value in losses.values())
            # Xóa gradient cũ trước bước backward.
            optimizer.zero_grad()
            # Tính gradient cho batch hiện tại.
            loss.backward()
            # Cập nhật trọng số sau khi có gradient.
            optimizer.step()
            # Cộng dồn loss để lấy trung bình cuối epoch.
            running_loss += float(loss.detach().cpu())
        # Tính thời gian chạy của epoch.
        elapsed = time.perf_counter() - start
        # In log ngắn để theo dõi quá trình train.
        print(f"epoch={epoch + 1} loss={running_loss / max(1, len(train_loader)):.4f} time={elapsed:.1f}s")
        # Lưu loss trung bình của epoch.
        loss_history.append(running_loss / max(1, len(train_loader)))
    # Lưu checkpoint sau khi train xong.
    torch.save(model.state_dict(), output_dir / "faster_rcnn_chess.pth")
    # Vẽ đường cong loss để đưa vào báo cáo.
    save_faster_rcnn_training_figures(loss_history, figures_dir)
    # Chọn 5 ảnh test tiêu biểu cho phần so sánh.
    test_images = select_comparison_test_images(dataset_root, count=5)
    # Xuất prediction cho 5 ảnh test đã chọn.
    save_prediction_sweep(
        test_images,
        lambda image_path: predict_torchvision_boxes(model, image_path, classes),
        figures_dir,
        "faster_rcnn",
        min_score=0.3,
        max_boxes=8,
    )
    # Dùng toàn bộ ảnh test để đánh giá định lượng.
    test_all = sorted((dataset_root / "test").glob("*.jpg"))
    # Vẽ confusion matrix trên tập test.
    save_detection_confusion_matrix(
        dataset_root,
        test_all,
        lambda image_path: predict_torchvision_boxes(model, image_path, classes),
        classes,
        figures_dir / "faster_rcnn_confusion_matrix.png",
    )
    # Vẽ đường precision/recall theo ngưỡng confidence.
    save_threshold_metric_curve(
        dataset_root,
        test_all,
        lambda image_path: predict_torchvision_boxes(model, image_path, classes),
        figures_dir / "faster_rcnn_eval_curve.png",
        "Faster R-CNN evaluation curve",
    )
    # Ghép thêm ảnh so sánh cho phần kết quả.
    assemble_report_panels(dataset_root, figures_dir)


# Định nghĩa train_detr.
def train_detr(dataset_root: Path, epochs: int, batch_size: int, output_dir: Path, figures_dir: Path) -> None:
    # DETR cần một số biến môi trường để chạy ổn trên Kaggle/Colab.
    import os
    # Khóa GPU hiển thị về CUDA 0 cho nhất quán.
    os.environ["CUDA_VISIBLE_DEVICES"] = "0"
    # Tắt W&B để tránh hỏi login khi chạy notebook.
    os.environ["WANDB_DISABLED"] = "true"
    # Import torch sau khi set môi trường.
    import torch
    # Dùng Dataset của PyTorch để build dữ liệu cho Trainer.
    from torch.utils.data import Dataset
    # Dùng DETR của Hugging Face để fine-tune trực tiếp.
    from transformers import DetrForObjectDetection, DetrImageProcessor, Trainer, TrainingArguments
    # Đọc danh sách class để map id <-> tên.
    classes = read_classes(dataset_root)
    # Tạo mapping id -> tên class.
    id2label = {idx: name for idx, name in enumerate(classes)}
    # Tạo mapping ngược lại để model ghi nhãn đúng.
    label2id = {name: idx for idx, name in id2label.items()}
    # Chọn device an toàn.
    device = get_safe_torch_device()
    # Processor chịu trách nhiệm resize, normalize và encode bbox.
    processor = DetrImageProcessor.from_pretrained("facebook/detr-resnet-50")

    # Định nghĩa DetrChessDataset.
    class DetrChessDataset(Dataset):
        # Định nghĩa __init__.
        def __init__(self, split: str):
            # Lưu danh sách ảnh của split hiện tại.
            self.images = sorted((dataset_root / split).glob("*.jpg"))
            # Lưu annotation tương ứng với từng ảnh.
            self.annotations = load_split_annotations(dataset_root, split)

        # Định nghĩa __len__.
        def __len__(self) -> int:
            # Trả về giá trị đã tính.
            return len(self.images)

        # Định nghĩa __getitem__.
        def __getitem__(self, index: int):
            # Lấy ảnh theo index.
            image_path = self.images[index]
            # Đọc ảnh RGB để đưa vào processor.
            image = Image.open(image_path).convert("RGB")
            # Lấy kích thước ảnh gốc để clamp bbox.
            image_width, image_height = image.size
            # Lấy các bbox của ảnh hiện tại.
            records = self.annotations.get(image_path.name, [])
            # Loại bỏ bbox lỗi hoặc vượt biên.
            cleaned_annotations = []
            # Chuẩn hóa annotation về format mà DETR mong đợi.
            for record in records:
                # Chặn tọa độ trái/phải trong phạm vi ảnh.
                x1 = max(0.0, min(float(record.x1), float(image_width)))
                y1 = max(0.0, min(float(record.y1), float(image_height)))
                x2 = max(0.0, min(float(record.x2), float(image_width)))
                y2 = max(0.0, min(float(record.y2), float(image_height)))
                # Bỏ qua bbox suy biến.
                if x2 <= x1 or y2 <= y1:
                    continue
                # Lưu bbox theo format x, y, w, h cho processor.
                cleaned_annotations.append(
                    {
                        "category_id": record.class_id,
                        "bbox": [x1, y1, x2 - x1, y2 - y1],
                        "area": (x2 - x1) * (y2 - y1),
                        "iscrowd": 0,
                    }
                )
            # Tạo target theo format của Hugging Face DETR.
            target = {
                "image_id": index,
                "annotations": cleaned_annotations,
            }
            # Processor sẽ tạo tensor đầu vào và label tương ứng.
            encoded = processor(images=image, annotations=target, return_tensors="pt")
            # Trả về một sample gồm ảnh và labels.
            return {"pixel_values": encoded["pixel_values"].squeeze(0), "labels": encoded["labels"][0]}

    # Định nghĩa collate_fn.
    def collate_fn(batch):
        # Tách pixel_values của từng sample ra thành list.
        pixel_values = [item["pixel_values"] for item in batch]
        # Pad tensor để các ảnh có cùng kích thước trong một batch.
        encoding = processor.pad(pixel_values, return_tensors="pt")
        # Gom labels lại thành list để Trainer xử lý.
        labels = [item["labels"] for item in batch]
        # Trả về batch theo format mà Trainer cần.
        return {"pixel_values": encoding["pixel_values"], "pixel_mask": encoding["pixel_mask"], "labels": labels}

    # Nạp DETR pretrain rồi thay head cho đúng số class.
    model = DetrForObjectDetection.from_pretrained(
        "facebook/detr-resnet-50",
        num_labels=len(classes),
        id2label=id2label,
        label2id=label2id,
        ignore_mismatched_sizes=True,
    )
    # Đưa model lên device trước khi train.
    model.to(device)
    # Cấu hình lịch train cho DETR.
    args = TrainingArguments(
        output_dir=str(output_dir),
        per_device_train_batch_size=batch_size,
        per_device_eval_batch_size=batch_size,
        num_train_epochs=epochs,
        learning_rate=1e-4,
        weight_decay=1e-4,
        logging_steps=10,
        evaluation_strategy="epoch",
        save_strategy="epoch",
        remove_unused_columns=False,
        fp16=device.type == "cuda",
        no_cuda=device.type == "cpu",
        report_to=[],
    )
    # Dùng Trainer để chạy train/eval tự động.
    trainer = Trainer(
        model=model,
        args=args,
        train_dataset=DetrChessDataset("train"),
        eval_dataset=DetrChessDataset("valid"),
        data_collator=collate_fn,
    )
    # Chạy fine-tune DETR.
    trainer.train()
    # Vẽ đường cong loss từ log history của Trainer.
    save_detr_training_figures(trainer, figures_dir)
    # Chọn 5 ảnh test tiêu biểu để xuất prediction.
    test_images = select_comparison_test_images(dataset_root, count=5)
    # Xuất prediction cho 5 ảnh test đã chọn.
    save_prediction_sweep(
        test_images,
        lambda image_path: predict_detr_boxes(model, processor, image_path),
        figures_dir,
        "detr",
        min_score=0.3,
        max_boxes=8,
    )
    # Đánh giá trên toàn bộ test set.
    test_all = sorted((dataset_root / "test").glob("*.jpg"))
    # Đọc lại class để dùng cho confusion matrix.
    classes = read_classes(dataset_root)
    # Vẽ confusion matrix trên tập test.
    save_detection_confusion_matrix(
        dataset_root,
        test_all,
        lambda image_path: predict_detr_boxes(model, processor, image_path),
        classes,
        figures_dir / "detr_confusion_matrix.png",
    )
    # Vẽ đường precision/recall theo ngưỡng confidence.
    save_threshold_metric_curve(
        dataset_root,
        test_all,
        lambda image_path: predict_detr_boxes(model, processor, image_path),
        figures_dir / "detr_eval_curve.png",
        "DETR evaluation curve",
    )
    # Ghép thêm panel so sánh để bài báo cáo đầy đủ hơn.
    assemble_report_panels(dataset_root, figures_dir)


# Điểm vào chính của script.
def main() -> None:
    # Điều phối các chế độ chạy từ dòng lệnh.

    # Lưu parser.
    parser = argparse.ArgumentParser(description="Chess Pieces object detection")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("--dataset", type=Path, default=None, help="Path to 416x416_aug_chess_pieces")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("--output", type=Path, default=Path("outputs"), help="Output directory")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("--figures", type=Path, default=Path("../doc/figures"), help="Report figures directory")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("--epochs", type=int, default=3, help="Small default for quick verification; increase for final runs")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("--batch-size", type=int, default=2, help="Training batch size")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("--imgsz", type=int, default=416, help="YOLO image size")
    # Khai báo tham số dòng lệnh.
    parser.add_argument("command", choices=["prepare", "figures", "yolo", "detr", "fasterrcnn", "all"])
    # Lưu args.
    args = parser.parse_args()

    # Tìm root của dataset nếu người dùng không truyền vào.
    dataset_root = args.dataset or find_dataset_root(Path(__file__))
    # Tạo thư mục output chính nếu cần.
    args.output.mkdir(parents=True, exist_ok=True)

    # Chạy bước chuẩn bị dataset cho YOLO/COCO nếu được yêu cầu.
    if args.command in {"prepare", "all"}:
        # Lưu yolo_yaml.
        yolo_yaml = convert_to_yolo(dataset_root, args.output)
        # Lưu coco_root.
        coco_root = convert_to_coco(dataset_root, args.output)
        # In log ra màn hình.
        print(f"YOLO config: {yolo_yaml}")
        # In log ra màn hình.
        print(f"COCO json: {coco_root}")

    # Sinh ảnh thống kê và ảnh mẫu cho báo cáo.
    if args.command in {"figures", "all"}:
        # Gọi make_figures.
        make_figures(dataset_root, args.figures)
        # In log ra màn hình.
        print(f"Figures written to: {args.figures}")

    # Train YOLO và xuất toàn bộ hình liên quan.
    if args.command in {"yolo", "all"}:
        # Lưu data_yaml.
        data_yaml = convert_to_yolo(dataset_root, args.output)
        # Gọi train_yolo.
        train_yolo(data_yaml, args.epochs, args.imgsz, args.output, args.figures, dataset_root)

    # Train DETR.
    if args.command in {"detr", "all"}:
        # Gọi train_detr.
        train_detr(dataset_root, args.epochs, args.batch_size, args.output / "detr_chess", args.figures)

    # Train Faster R-CNN.
    if args.command in {"fasterrcnn", "all"}:
        # Gọi train_faster_rcnn.
        train_faster_rcnn(dataset_root, args.epochs, args.batch_size, args.output / "faster_rcnn", args.figures)


# Chỉ chạy main khi file được gọi trực tiếp.
if __name__ == "__main__":
    main()
