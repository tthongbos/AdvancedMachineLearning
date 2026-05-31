# TH01 - OpenCV Basic

## Cách chạy

```bash
pip install -r requirements.txt
jupyter notebook xu_ly_anh_co_ban_th01.ipynb
```

## Ảnh đầu vào

Notebook có cell tải ảnh bằng wget:

```bash
wget -q -O data/Lenna.jpg http://www.ess.ic.kanagawa-it.ac.jp/std_img/colorimage/Lenna.jpg
```

Nếu không có Internet, notebook tự dùng `data/anh_mau_fallback.png` để vẫn chạy được.

## Cấu trúc cell

Mỗi mục xử lý chính đều gồm đúng 3 code cell:

1. CELL THỦ CÔNG
2. CELL TỰ ĐỘNG / THƯ VIỆN
3. CELL SO SÁNH

Các mục gồm: open/show, scale, xoay, biến đổi màu, độ sáng và độ tương phản.
