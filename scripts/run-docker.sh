#!/bin/bash
set -e

# Build the image
echo "Building Docker image ziku-dev..."
docker build -t ziku-dev .

# Run the container
echo "Starting Ziku development container..."
# Mount current directory to /app
docker run -it --rm -v "$(pwd):/app" ziku-dev
