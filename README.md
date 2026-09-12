#!/bin/bash
# auto_commit.sh - Automatically stage, commit, and push updates

echo "Staging changes..."
git add .

echo "Committing with standard message..."
git commit -m "Feat(CGurd/Ternary): automatic update for verified ternary trace theorem and modular architecture"

echo "Pushing to origin main..."
git push origin main

echo "Done! Changes successfully pushed to GitHub."
