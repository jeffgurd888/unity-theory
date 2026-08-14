# Make sure you are on main and up to date
git checkout main
git pull origin main

# Overwrite / create the three files with the contents above
# (use your editor, or paste into the files)

# Stage everything
git add LICENSE README.md Unity/Thet/BlockKrajewski.lean

# Single commit
git commit -m "Add BlockKrajewski.lean (self-adjoint θ + anticommutation with γ)
Update LICENSE and README with full name, Nexus Research Institute affiliation, and ethical pledge"

# Push
git push origin main