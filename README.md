---

# **📄 install.sh (copy & paste)**

```bash
#!/usr/bin/env bash
set -e

echo "𐤈 Nexus Codex — Auto Installer"
echo "Cloning repository..."

REPO="https://github.com/<YOUR-USER>/nexus-theta-codex.git"
TARGET="$HOME/nexus-theta-codex"

git clone "$REPO" "$TARGET"


cd "$TARGET"

echo "Running setup scripts..."
bash setup/init.sh
bash setup/lean-deps.sh
bash setup/hypercodex-build.sh
bash setup/verify.sh

echo "Installation complete."
echo "Launch with: make run"
---

# **📄 install.sh (copy & paste)**

```bash
#!/usr/bin/env bash
set -e

echo "𐤈 Nexus Codex — Auto Installer"
echo "Cloning repository..."

REPO="https://github.com/<YOUR-USER>/nexus-theta-codex.git"
TARGET="$HOME/nexus-theta-codex"

git clone "$REPO" "$TARGET"

cd "$TARGET"

echo "Running setup scripts..."
bash setup/init.sh
bash setup/lean-deps.sh
bash setup/hypercodex-build.sh
bash setup/verify.sh

echo "Installation complete."
echo "Launch with: make run"
.PHONY: all install build run verify

all: install build verify

install:
	bash setup/init.sh
	bash setup/lean-deps.sh

build:
	bash setup/hypercodex-build.sh

run:
	echo "Launching Nexus 𐤈 Hypercodex Engine..."
	node hypercodex/engine.js

verify:
	bash setup/verify.sh