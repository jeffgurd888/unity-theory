

---

### Terminal Commands to Commit and Push

Run these commands in your local `unity-theory` folder to commit and push this updated `README.md` and your Lean files:

```bash
git add README.md CGurd/Basic.lean lakefile.lean lean-toolchain
git commit -m "docs(c-gurd): add comprehensive README unpacking the thermal clock model and Lean 4 formalization"
git push origin main
git clone [https://github.com/jeffgurd888/unity-theory.git](https://github.com/jeffgurd888/unity-theory.git)
cd unity-theory
lake build
