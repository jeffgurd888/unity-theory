# If you haven't cloned or initialized it locally yet:
git clone https://github.com/jeffgurd888/unity-theory.git
cd unity-theory

# (If you already have your local folder, just navigate into it)
# cd path/to/unity-theory

# Add the new Lean files for the thermal clock model
# Make sure your folder structure has CGurd/Basic.lean, lean-toolchain, and lakefile.lean as outlined above

git add .
git commit -m "feat(c-gurd): add 2x2 thermal clock model and ternary trace theorem to unity-theory"
git push origin main
