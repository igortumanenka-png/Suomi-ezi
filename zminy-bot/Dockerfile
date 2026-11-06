# Python + Pillow (малювання картинки з графіком) + шрифт DejaVu з українськими літерами.
# Код не копіюється в образ: папка бота підключена в compose.yml, тож оновити bot.py
# можна без перезбирання - достатньо перезапустити контейнер.
FROM python:3.12-slim
RUN apt-get update \
    && apt-get install -y --no-install-recommends fonts-dejavu-core \
    && rm -rf /var/lib/apt/lists/* \
    && pip install --no-cache-dir pillow==11.0.0
WORKDIR /app
CMD ["python", "bot.py"]
