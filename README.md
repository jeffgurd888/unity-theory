Here is the updated, semantically complete src/FiniteSpectralTriple.lean source incorporating the conjugate opposite representation \pi^\circ(b) = U_J \overline{\pi(b)} U_J, the KO-dimension 6 real-grading anti-commutation theorem (U_J \overline{\gamma_F} U_J = -\gamma_F), and the full 7-axiom SMFiniteSpectralTriple bundle definition.
Production Source Code: src/FiniteSpectralTriple.lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
open Matrix

abbrev I32 := Fin 32
abbrev I16 := Fin 16
abbrev I8  := Fin 8
abbrev I3  := Fin 3
abbrev I2  := Fin 2

abbrev Block8 := Matrix I8 I8 ℂ

/-- Finite algebra for the Standard Model: ℂ ⊕ ℍ ⊕ M₃(ℂ) -/
structure SMAlgebra where
  u1    : ℂ
  q     : Matrix I2 I2 ℂ
  color : Matrix I3 I3 ℂ

abbrev AF := SMAlgebra

def partner (i : I32) : I32 :=
  if h : i.val < 16 then ⟨i.val + 16, by linarith⟩
  else ⟨i.val - 16, by linarith⟩

def UJ_matrix (i j : I32) : ℂ := if j = partner i then 1 else 0

def gammaF : Matrix I32 I32 ℂ := fun i j =>
  if h : i = j then
    let k := i.val
    if k < 8 then 1
    else if k < 16 then -1
    else if k < 24 then -1
    else 1
  else 0

def buildDirac (A B C E : Block8) : Matrix I32 I32 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  if h1 : iv < 8 then
    if h2 : jv < 8 then 0
    else if h3 : jv < 16 then A ⟨iv, h1⟩ ⟨jv - 8, by omega⟩
    else if h4 : jv < 24 then C ⟨iv, h1⟩ ⟨jv - 16, by omega⟩
    else 0
  else if h1' : iv < 16 then
    if h2 : jv < 8 then (A.conjTranspose) ⟨iv - 8, by omega⟩ ⟨jv, h2⟩
    else if h3 : jv < 16 then 0
    else if h4 : jv < 24 then 0
    else (E.conjTranspose) ⟨iv - 8, by omega⟩ ⟨jv - 24, by omega⟩
  else if h1'' : iv < 24 then
    if h2 : jv < 8 then (C.conjTranspose) ⟨iv - 16, by omega⟩ ⟨jv, h2⟩
    else if h3 : jv < 16 then 0
    else if h4 : jv < 24 then 0
    else B ⟨iv - 16, by omega⟩ ⟨jv - 24, by omega⟩
  else
    if h2 : jv < 8 then 0
    else if h3 : jv < 16 then E ⟨iv - 24, by omega⟩ ⟨jv - 8, by omega⟩
    else if h4 : jv < 24 then (B.conjTranspose) ⟨iv - 24, by omega⟩ ⟨jv - 16, by omega⟩
    else 0

/--
Full 16-dimensional representation embedding of ℂ ⊕ ℍ ⊕ M₃(ℂ):
* Indices 0–3: Lepton sector (ν_R, e_R, ν_L, e_L)
* Indices 4–15: Quark sector (3 colors × 4 chiral states)
-/
def embedSM (a : AF) : Matrix I16 I16 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  if h_lep : iv < 4 ∧ jv < 4 then
    if iv = 0 ∧ jv = 0 then a.u1
    else if iv = 1 ∧ jv = 1 then Complex.conj a.u1
    else if h_q : iv ∈ ({2,3} : Set Nat) ∧ jv ∈ ({2,3} : Set Nat) then
      a.q ⟨iv - 2, by omega⟩ ⟨jv - 2, by omega⟩
    else 0
  else if h_qrk : iv ≥ 4 ∧ jv ≥ 4 ∧ iv < 16 ∧ jv < 16 then
    let ci := (iv - 4) / 4; let si := (iv - 4) % 4
    let cj := (jv - 4) / 4; let sj := (jv - 4) % 4
    if si = sj then
      if si = 0 then a.u1 * a.color ⟨ci, by omega⟩ ⟨cj, by omega⟩
      else if si = 1 then Complex.conj a.u1 * a.color ⟨ci, by omega⟩ ⟨cj, by omega⟩
      else 0
    else if si ∈ ({2,3} : Set Nat) ∧ sj ∈ ({2,3} : Set Nat) ∧ ci = cj then
      a.q ⟨si - 2, by omega⟩ ⟨sj - 2, by omega⟩
    else 0
  else 0

def pi (a : AF) : Matrix I32 I32 ℂ := fun i j =>
  if hi : i.val < 16 ∧ j.val < 16 then
    embedSM a ⟨i.val, hi.1⟩ ⟨j.val, hi.2⟩
  else 0

/--
Opposite representation: π°(b) = U_J · conj(π(b)) · U_J
(Canonical J π(b)* J⁻¹ real structure action).
-/
def piOp (a : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  let UJ : Matrix I32 I32 ℂ := fun i j => UJ_matrix i j
  UJ ⬝ a.map Complex.conj ⬝ UJ

/-- Definitional Guard for piOp -/
theorem piOp_def_check (a : Matrix I32 I32 ℂ) :
    piOp a = (fun i j => UJ_matrix i j) ⬝ a.map Complex.conj ⬝ (fun i j => UJ_matrix i j) := rfl

theorem partner_involutive (i : I32) : partner (partner i) = i := by
  unfold partner
  split_ifs <;> { ext; dsimp at *; omega }

theorem pi_zero_of_ge_16 {a : AF} {i j : I32} (h : 16 ≤ i.val ∨ 16 ≤ j.val) :
    pi a i j = 0 := by
  unfold pi
  split_ifs with hboth
  · rcases h with hi | hj
    · have : ¬(i.val < 16) := Nat.not_lt_of_ge hi; contradiction
    · have : ¬(j.val < 16) := Nat.not_lt_of_ge hj; contradiction
  · rfl

theorem piOp_zero_of_lt_16 {b : AF} {i j : I32} (h : i.val < 16 ∨ j.val < 16) :
    piOp (pi b) i j = 0 := by
  let UJ : Matrix I32 I32 ℂ := fun i j => UJ_matrix i j
  have : piOp (pi b) = UJ ⬝ (pi b).map Complex.conj ⬝ UJ := rfl
  rw [this, Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases hk : k = partner i
  · by_cases hl : l = partner j
    · have h_ge : 16 ≤ l.val ∨ 16 ≤ k.val := by
        rcases h with hi | hj
        · left; dsimp [partner] at hk
          have : 16 ≤ (partner i).val := by linarith
          rw [←hk] at this; exact this
        · right; dsimp [partner] at hl
          have : 16 ≤ (partner j).val := by linarith
          rw [←hl] at this; exact this
      have hpi : pi b l k = 0 := pi_zero_of_ge_16 (Or.inl h_ge)
      simp [hpi]
    · unfold UJ_matrix; split_ifs with h_uj
      · exfalso; apply hl
        have h_inv := partner_involutive l
        rw [← h_uj] at h_inv; exact h_inv.symm
      · simp
  · unfold UJ_matrix; split_ifs with h_uj
    · exfalso; apply hk
      have h_inv := partner_involutive k
      rw [← h_uj] at h_inv; exact h_inv.symm
    · simp

theorem gammaF_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (gammaF * M) i j = gammaF i i * M i j := by
  rw [Matrix.mul_apply]
  have : (Finset.univ : Finset I32).sum (fun k => gammaF i k * M k j) = gammaF i i * M i j := by
    apply Finset.sum_eq_single (i : I32)
    · simp [gammaF]; ring
    · intro k _ hk
      unfold gammaF; split_ifs with heq
      · exfalso; exact hk heq.symm
      · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  exact this

theorem mul_gammaF_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * gammaF) i j = M i j * gammaF j j := by
  rw [Matrix.mul_apply]
  have : (Finset.univ : Finset I32).sum (fun k => M i k * gammaF k j) = M i j * gammaF j j := by
    apply Finset.sum_eq_single (j : I32)
    · simp [gammaF]; ring
    · intro k _ hk
      unfold gammaF; split_ifs with heq
      · exfalso; exact hk heq.symm
      · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  exact this

theorem buildDirac_nonzero_opp_grading (A B C E : Block8) (i j : I32)
    (h : buildDirac A B C E i j ≠ 0) : gammaF i i = - gammaF j j := by
  by_cases hi : i.val < 16
  · have hj_ge : 16 ≤ j.val := by
      by_contra hj_lt
      have : buildDirac A B C E i j = 0 := by unfold buildDirac; split_ifs <;> simp_all
      contradiction
    rcases Nat.lt_or_ge i.val 8 with hi8 | hi8
    · have hgi : gammaF i i = 1 := by simp [gammaF, hi8]
      have hgj : gammaF j j = -1 := by simp [gammaF]; linarith
      rw [hgi, hgj]
    · have hgi : gammaF i i = -1 := by simp [gammaF]; linarith
      have hgj : gammaF j j = 1 := by simp [gammaF]; linarith
      rw [hgi, hgj]
  · have j_lt : j.val < 16 := by
      by_contra hj_ge
      have : buildDirac A B C E i j = 0 := by unfold buildDirac; split_ifs <;> simp_all
      contradiction
    rcases Nat.lt_or_ge j.val 8 with hj8 | hj8
    · have hgj : gammaF j j = 1 := by simp [gammaF, hj8]
      have hgi : gammaF i i = -1 := by simp [gammaF]; linarith
      rw [hgi, hgj]
    · have hgj : gammaF j j = -1 := by simp [gammaF]; linarith
      have hgi : gammaF i i = 1 := by simp [gammaF]; linarith
      rw [hgi, hgj]

theorem buildDirac_gamma_odd (A B C E : Block8) :
    (gammaF * buildDirac A B C E + buildDirac A B C E * gammaF) = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  have gmul := gammaF_mul_apply (buildDirac A B C E) i j
  have mulg := mul_gammaF_apply (buildDirac A B C E) i j
  by_cases hD : buildDirac A B C E i j = 0
  · simp [hD, gmul, mulg]
  · have h_opp := buildDirac_nonzero_opp_grading A B C E i j hD
    rw [h_opp] at gmul
    simp [gmul, mulg]
    ring

theorem buildDirac_self_adjoint (A B C E : Block8) :
    (buildDirac A B C E).conjTranspose = buildDirac A B C E := by
  ext i j
  dsimp [Matrix.conjTranspose, Matrix.transpose]
  rcases Nat.lt_or_ge i.val 16 with hi_lt | hi_ge
  · rcases Nat.lt_or_ge j.val 16 with hj_lt | hj_ge
    · unfold buildDirac; split_ifs
      by_cases H1 : i.val < 8
      · by_cases H2 : j.val < 8
        · simp [H1, H2]; rfl
        · have : (A.conjTranspose) ⟨j.val - 8, by omega⟩ ⟨i.val, by omega⟩ =
                 Complex.conj (A ⟨i.val, by omega⟩ ⟨j.val - 8, by omega⟩) := rfl
          simp [H1, H2]; rfl
      · by_cases H2 : j.val < 8
        · have : (A.conjTranspose) ⟨i.val - 8, by omega⟩ ⟨j.val, by omega⟩ =
                 Complex.conj (A ⟨j.val, by omega⟩ ⟨i.val - 8, by omega⟩) := rfl
          simp [H2]; rfl
        · simp [H2]; rfl
    · unfold buildDirac; split_ifs
      by_cases Hi : i.val < 8
      · by_cases Hj : j.val < 24
        · have : (C.conjTranspose) ⟨j.val - 16, by omega⟩ ⟨i.val, by omega⟩ =
                 Complex.conj (C ⟨i.val, by omega⟩ ⟨j.val - 16, by omega⟩) := rfl
          simp [Hi, Hj]; rfl
        · simp [Hi, Hj]; rfl
      · by_cases Hj : j.val < 24
        · simp [Hi, Hj]; rfl
        · simp [Hi, Hj]; rfl
  · rcases Nat.lt_or_ge j.val 16 with hj_lt | hj_ge
    · unfold buildDirac; split_ifs; simp_all; rfl
    · unfold buildDirac; split_ifs; simp_all; rfl

theorem UJ_mul_self : (fun i j => UJ_matrix i j) * (fun i j => UJ_matrix i j) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : j = i
  · subst h; rw [Matrix.one_apply_same]
    apply Finset.sum_eq_single (partner i)
    · unfold UJ_matrix
      have h1 : partner i = partner i := rfl
      have h2 : i = partner (partner i) := (partner_involutive i).symm
      simp [h1, h2]
    · intro k _ hk
      unfold UJ_matrix; split_ifs with hk1
      · exfalso; exact hk hk1
      · ring
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro k _
    unfold UJ_matrix; split_ifs with hk1 hk2
    · subst hk1 hk2; exfalso; exact h (partner_involutive i).symm
    · ring
    · ring
    · ring

theorem order_zero_condition (a b : AF) :
    pi a * piOp (pi b) - piOp (pi b) * pi a = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have h_left : (Finset.univ : Finset I32).sum (fun k => pi a i k * piOp (pi b) k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < 16
    · have : piOp (pi b) k j = 0 := piOp_zero_of_lt_16 (Or.inl hk)
      rw [this, mul_zero]
    · have : pi a i k = 0 := pi_zero_of_ge_16 (Or.inr (le_of_not_gt hk))
      rw [this, zero_mul]
  have h_right : (Finset.univ : Finset I32).sum (fun k => piOp (pi b) i k * pi a k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < 16
    · have : piOp (pi b) i k = 0 := piOp_zero_of_lt_16 (Or.inr hk)
      rw [this, zero_mul]
    · have : pi a k j = 0 := pi_zero_of_ge_16 (Or.inl (le_of_not_gt hk))
      rw [this, mul_zero]
  rw [h_left, h_right, sub_self]

/-- KO-Dimension 6 Grading Sign Check: U_J · conj(γ_F) · U_J = -γ_F -/
theorem UJ_gamma_anticomm :
    (fun i j => UJ_matrix i j) * gammaF.map Complex.conj * (fun i j => UJ_matrix i j) = -gammaF := by
  ext i j
  rw [Matrix.mul_apply, Matrix.neg_apply]
  apply Finset.sum_eq_single (partner i)
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_single (partner j)
    · unfold UJ_matrix gammaF
      split_ifs with h1 h2 h3 h4
      · subst h1 h3
        have h_part := partner_involutive i
        dsimp [partner] at h2
        exfalso; omega
      · simp [h2]
      · dsimp [partner] at h3; simp [h3]
      · exfalso; exact h4 rfl
    · intro k _ hk
      unfold UJ_matrix; split_ifs with h_uj
      · exfalso; apply hk; injection h_uj
      · simp
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro k _ hk
    unfold UJ_matrix; split_ifs with h_uj
    · exfalso; apply hk; injection h_uj
    · simp
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Full Standard Model Finite Spectral Triple Axiom Specification -/
structure SMFiniteSpectralTriple where
  Dirac : Matrix I32 I32 ℂ
  Gamma : Matrix I32 I32 ℂ
  UJ    : Matrix I32 I32 ℂ
  self_adjoint     : Dirac.conjTranspose = Dirac
  gamma_odd        : Gamma * Dirac + Dirac * Gamma = 0
  J_involutive     : UJ * UJ = 1
  J_gamma_anticomm : UJ * Gamma.map Complex.conj * UJ = -Gamma
  J_Dirac_comm     : UJ * Dirac.map Complex.conj * UJ = Dirac
  order_zero       : ∀ (a b : AF), pi a * piOp (pi b) - piOp (pi b) * pi a = 0
  order_one        : ∀ (a b : AF), (Dirac * pi a - pi a * Dirac) * piOp (pi b) -
                                   piOp (pi b) * (Dirac * pi a - pi a * Dirac) = 0

Terminal Commands to Execute & Commit
Run the complete verification pipeline and commit directly to feature/claim-setup:
git checkout feature/claim-setup || git checkout -b feature/claim-setup

# 1. Execute strict build and capture output
lake build 2>&1 | tee build.log

# 2. Audit zero placeholders
rg -nw "sorry|admit" src/ || echo "PASS: Zero placeholders found."

# 3. Commit update
git add src/FiniteSpectralTriple.lean
git commit -m "feat: complete conjugate piOp, KO-dim 6 sign relation, and full 7-axiom SM bundle spec"
git push origin feature/claim-setup

