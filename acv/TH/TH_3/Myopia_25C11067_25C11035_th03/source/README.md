# TH03 - Object Detection on Chess Pieces

## Dataset

Place the dataset directory `416x416_aug_chess_pieces` at the repository root, or pass its path with `--dataset`.

Original dataset page: <https://universe.roboflow.com/joseph-nelson/chess-pieces-new>

## Environment

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## Reproduce preprocessing and figures

```bash
python th03_object_detection.py prepare
python th03_object_detection.py figures
```

`prepare` writes temporary YOLO and COCO formatted data under `source/outputs`. This folder can be regenerated and should be removed before creating the final submission zip.

## Train the models

```bash
python th03_object_detection.py yolo --epochs 50 --batch-size 8
python th03_object_detection.py detr --epochs 20 --batch-size 2
python th03_object_detection.py fasterrcnn --epochs 20 --batch-size 2
```

The script uses pretrained weights for all three models:

- YOLO: `yolov8n.pt` through Ultralytics.
- DETR: `facebook/detr-resnet-50` through Hugging Face Transformers.
- Faster R-CNN: `FasterRCNN_ResNet50_FPN_Weights.DEFAULT` through TorchVision.

For a quick CPU smoke test, keep the default `--epochs 3`; for final numbers, run on a CUDA GPU and increase epochs as shown above.
