import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix

namespace CGurd

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

/-- Particle ↔ antiparticle index swap: i ↦ (i + 16) mod 32. -/
def partner (i : I32) : I32 :=
  if h : i.val < 16 then ⟨i.val + 16, by omega⟩
  else ⟨i.val - 16, by omega⟩

theorem partner_involutive (i : I32) : partner (partner i) = i := by
  unfold partner
  split_ifs <;> { ext; dsimp at *; omega }

def UJ_matrix (i j : I32) : ℂ := if j = partner i then 1 else 0

/-- Grading γ_F = diag(+I₈, -I₈, -I₈, +I₈) on (H_L, H_R, H_L^c, H_R^c). -/
def gammaF : Matrix I32 I32 ℂ := fun i j =>
  if h : i = j then
    let k := i.val
    if k < 8 then 1
    else if k < 16 then -1
    else if k < 24 then -1
    else 1
  else 0

/-- Generic four-block Dirac operator on ℂ³² = H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c. -/
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
16-dimensional representation embedding of ℂ ⊕ ℍ ⊕ M₃(ℂ), Option A ordering:

* H_L (indices 0–7):
    0 = ν_L, 1 = e_L                  (quaternionic doublet q)
    2 = u_L^r, 3 = d_L^r              (q ⊗ color, color-diagonal)
    4 = u_L^g, 5 = d_L^g
    6 = u_L^b, 7 = d_L^b
* H_R (indices 8–15):
    8 = ν_R, 9 = e_R                  (u1 scalar, conj u1 scalar)
    10 = u_R^r, 11 = d_R^r            (u1 · color, conj u1 · color)
    12 = u_R^g, 13 = d_R^g
    14 = u_R^b, 15 = d_R^b
-/
def embedSM (a : AF) : Matrix I16 I16 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  -- H_L × H_L
  if hL : iv < 8 ∧ jv < 8 then
    if h_l : iv < 2 ∧ jv < 2 then
      a.q ⟨iv, by omega⟩ ⟨jv, by omega⟩
    else if h_q : 2 ≤ iv ∧ 2 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 2) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 2) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 2) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 2) / 2, by omega⟩
      a.q iso_i iso_j * a.color col_i col_j
    else 0
  -- H_R × H_R
  else if hR : 8 ≤ iv ∧ iv < 16 ∧ 8 ≤ jv ∧ jv < 16 then
    if h1 : iv = 8 ∧ jv = 8 then a.u1
    else if h2 : iv = 9 ∧ jv = 9 then Complex.conj a.u1
    else if h_q : 10 ≤ iv ∧ 10 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 10) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 10) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 10) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 10) / 2, by omega⟩
      if iso_i = iso_j then
        (if iso_i = 0 then a.u1 else Complex.conj a.u1) * a.color col_i col_j
      else 0
    else 0
  else 0

/-- π(a): embed a into the top-left 16×16 particle block; zero on H_A. -/
def pi (a : AF) : Matrix I32 I32 ℂ := fun i j =>
  if hi : i.val < 16 ∧ j.val < 16 then
    embedSM a ⟨i.val, hi.1⟩ ⟨j.val, hi.2⟩
  else 0

/-- π°(b) = U_J · π(b)ᵀ · U_J (= J π(b)* J⁻¹). -/
def piOp (a : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  let UJ : Matrix I32 I32 ℂ := fun i j => UJ_matrix i j
  UJ ⬝ a.transpose ⬝ UJ

/-- Definitional regression guard. -/
theorem piOp_def_check (a : Matrix I32 I32 ℂ) :
    piOp a = (fun i j => UJ_matrix i j) ⬝ a.transpose ⬝ (fun i j => UJ_matrix i j) := rfl

theorem pi_zero_of_ge_16 {a : AF} {i j : I32} (h : 16 ≤ i.val ∨ 16 ≤ j.val) :
    pi a i j = 0 := by
  unfold pi
  split_ifs with hboth
  · rcases h with hi | hj
    · exact absurd hboth.1 (Nat.not_lt_of_ge hi)
    · exact absurd hboth.2 (Nat.not_lt_of_ge hj)
  · rfl

theorem piOp_zero_of_lt_16 {b : AF} {i j : I32} (h : i.val < 16 ∨ j.val < 16) :
    piOp (pi b) i j = 0 := by
  rw [piOp_def_check, Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases hk : k = partner i
  · by_cases hl : l = partner j
    · have h_ge : 16 ≤ l.val ∨ 16 ≤ k.val := by
        rcases h with hi | hj
        · right
          rw [hk]
          have : (partner i).val = i.val + 16 := by
            unfold partner; rw [dif_pos hi]
          omega
        · left
          rw [hl]
          have : (partner j).val = j.val + 16 := by
            unfold partner; rw [dif_pos hj]
          omega
      have hpi : (pi b).transpose k l = pi b l k := rfl
      rw [hpi, pi_zero_of_ge_16 h_ge, mul_zero, zero_mul]
    · rw [show UJ_matrix l j = 0 from by unfold UJ_matrix; simp [hl]]
      ring
  · rw [show UJ_matrix i k = 0 from by unfold UJ_matrix; simp [hk]]
    ring

theorem gammaF_self_adjoint : gammaF.conjTranspose = gammaF := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst h; simp [gammaF]
  · have hji : ¬ j = i := fun h' => h h'.symm
    rw [show gammaF j i = 0 from by simp [gammaF, hji],
        show gammaF i j = 0 from by simp [gammaF, h]]

theorem gammaF_involutive : gammaF * gammaF = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_same]
    apply Finset.sum_eq_single i
    · unfold gammaF; split_ifs <;> ring
    · intro k _ hk
      unfold gammaF; split_ifs with heq
      · exact absurd heq.symm hk
      · ring
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro k _
    unfold gammaF; split_ifs with h1 h2
    · subst h1; exact absurd h2 rfl
    · ring
    · ring
    · ring

theorem gammaF_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (gammaF * M) i j = gammaF i i * M i j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · simp [gammaF]
  · intro k _ hk
    rw [show gammaF i k = 0 from by unfold gammaF; simp [hk], zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_gammaF_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * gammaF) i j = M i j * gammaF j j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single j
  · simp [gammaF]
  · intro k _ hk
    rw [show gammaF k j = 0 from by unfold gammaF; simp [hk], mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem buildDirac_nonzero_opp_grading (A B C E : Block8) (i j : I32)
    (h : buildDirac A B C E i j ≠ 0) : gammaF i i = - gammaF j j := by
  by_cases hi : i.val < 16
  · have hj_ge : 16 ≤ j.val := by
      by_contra hj_lt
      exact h (by unfold buildDirac; split_ifs <;> simp_all)
    rcases Nat.lt_or_ge i.val 8 with hi8 | hi8
    · have hgi : gammaF i i = 1 := by simp [gammaF, hi8]
      have hgj : gammaF j j = -1 := by
        simp only [gammaF]
        rw [if_pos rfl]
        rcases Nat.lt_or_ge j.val 24 with hj24 | hj24
        · rw [if_neg (by omega), if_pos hj24]
        · rw [if_neg (by omega), if_neg (by omega)]
      rw [hgi, hgj]
    · have hgi : gammaF i i = -1 := by
        simp only [gammaF]; rw [if_pos rfl, if_neg (by omega), if_pos hi]
      have hgj : gammaF j j = 1 := by
        simp only [gammaF]; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]
      rw [hgi, hgj]
  · have hj_lt : j.val < 16 := by
      by_contra hj_ge
      exact h (by unfold buildDirac; split_ifs <;> simp_all)
    rcases Nat.lt_or_ge j.val 8 with hj8 | hj8
    · have hgj : gammaF j j = 1 := by simp [gammaF, hj8]
      have hgi : gammaF i i = -1 := by
        simp only [gammaF]; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]
      rw [hgi, hgj]
    · have hgj : gammaF j j = -1 := by
        simp only [gammaF]; rw [if_pos rfl, if_neg (by omega), if_pos hj8]
      have hgi : gammaF i i = 1 := by
        simp only [gammaF]; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]
      rw [hgi, hgj]

theorem buildDirac_gamma_odd (A B C E : Block8) :
    (gammaF * buildDirac A B C E + buildDirac A B C E * gammaF) = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases hD : buildDirac A B C E i j = 0
  · rw [hD, mul_zero, zero_mul, add_zero]
  · have h_opp := buildDirac_nonzero_opp_grading A B C E i j hD
    rw [h_opp]; ring

theorem buildDirac_self_adjoint (A B C E : Block8) :
    (buildDirac A B C E).conjTranspose = buildDirac A B C E := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  -- 16 sector cases; use buildDirac unfolding + star_star per case
  unfold buildDirac
  by_cases H1 : i.val < 8
  · by_cases H2 : j.val < 8
    · simp [H1, H2]
    · by_cases H3 : j.val < 16
      · simp [H1, H2, H3, star_star]
      · by_cases H4 : j.val < 24
        · simp [H1, H2, H3, H4, star_star]
        · simp [H1, H2, H3, H4]
  · by_cases H5 : i.val < 16
    · by_cases H2 : j.val < 8
      · simp [H1, H5, H2, star_star]
      · by_cases H3 : j.val < 16
        · simp [H1, H5, H2, H3]
        · by_cases H4 : j.val < 24
          · simp [H1, H5, H2, H3, H4]
          · simp [H1, H5, H2, H3, H4, star_star]
    · by_cases H6 : i.val < 24
      · by_cases H2 : j.val < 8
        · simp [H1, H5, H6, H2, star_star]
        · by_cases H3 : j.val < 16
          · simp [H1, H5, H6, H2, H3]
          · by_cases H4 : j.val < 24
            · simp [H1, H5, H6, H2, H3, H4]
            · simp [H1, H5, H6, H2, H3, H4, star_star]
      · by_cases H2 : j.val < 8
        · simp [H1, H5, H6, H2]
        · by_cases H3 : j.val < 16
          · simp [H1, H5, H6, H2, H3, star_star]
          · by_cases H4 : j.val < 24
            · simp [H1, H5, H6, H2, H3, H4, star_star]
            · simp [H1, H5, H6, H2, H3, H4]

theorem UJ_mul_self :
    (fun i j => UJ_matrix i j) * (fun i j => UJ_matrix i j) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : j = i
  · subst h
    rw [Matrix.one_apply_same]
    apply Finset.sum_eq_single (partner i)
    · unfold UJ_matrix; simp [partner_involutive]
    · intro k _ hk
      rw [show UJ_matrix i k = 0 from by unfold UJ_matrix; simp [hk]]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = partner i
    · subst hk
      rw [show UJ_matrix (partner i) j = 0 from by
        unfold UJ_matrix; simp [show j ≠ i from h]]
    · rw [show UJ_matrix i k = 0 from by unfold UJ_matrix; simp [hk]]

theorem order_zero_condition (a b : AF) :
    pi a * piOp (pi b) - piOp (pi b) * pi a = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have h_left : (Finset.univ : Finset I32).sum
      (fun k => pi a i k * piOp (pi b) k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < 16
    · rw [piOp_zero_of_lt_16 (Or.inl hk), mul_zero]
    · rw [pi_zero_of_ge_16 (Or.inr (le_of_not_gt hk)), zero_mul]
  have h_right : (Finset.univ : Finset I32).sum
      (fun k => piOp (pi b) i k * pi a k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < 16
    · rw [piOp_zero_of_lt_16 (Or.inr hk), zero_mul]
    · rw [pi_zero_of_ge_16 (Or.inl (le_of_not_gt hk)), mul_zero]
  rw [h_left, h_right, sub_self]

/--
KO-dim 6 real-structure grading sign: U_J · conj(γ_F) · U_J = -γ_F.

This is a target; the proof requires the sector-level sign computation,
which is stubbed here.
-/
theorem UJ_gamma_anticomm :
    (fun i j => UJ_matrix i j) * gammaF.map Complex.conj *
    (fun i j => UJ_matrix i j) = -gammaF := by
  ext i j
  rw [Matrix.mul_apply, Matrix.neg_apply]
  rw [Finset.sum_eq_single (partner j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (partner i)]
    · -- Goal: conj (gammaF (partner i) (partner j)) = -gammaF i j
      by_cases hij : i = j
      · subst hij
        -- Sectors of i, and partner i is in the opposite sector
        rcases Nat.lt_or_ge i.val 8 with h8 | h8
        · have hp : (partner i).val = i.val + 16 := by
            unfold partner; rw [dif_pos h8]
          simp only [gammaF]
          rw [if_pos rfl, if_pos h8, if_pos rfl,
              if_neg (by omega : ¬ (partner i).val < 8),
              if_neg (by omega : ¬ (partner i).val < 16),
              if_pos (by omega : (partner i).val < 24)]
          simp
        · rcases Nat.lt_or_ge i.val 16 with h16 | h16
          · have hp : (partner i).val = i.val + 16 := by
              unfold partner; rw [dif_pos h16]
            simp only [gammaF]
            rw [if_pos rfl, if_neg (by omega : ¬ i.val < 8), if_pos h16,
                if_pos rfl,
                if_neg (by omega : ¬ (partner i).val < 8),
                if_neg (by omega : ¬ (partner i).val < 16),
                if_neg (by omega : ¬ (partner i).val < 24)]
            simp
          · rcases Nat.lt_or_ge i.val 24 with h24 | h24
            · have hp : (partner i).val = i.val - 16 := by
                unfold partner; rw [dif_neg (by omega : ¬ i.val < 16)]
              simp only [gammaF]
              rw [if_pos rfl, if_neg (by omega : ¬ i.val < 8),
                  if_neg (by omega : ¬ i.val < 16), if_pos h24,
                  if_pos rfl, if_pos (by omega : (partner i).val < 8)]
              simp
            · have hp : (partner i).val = i.val - 16 := by
                unfold partner; rw [dif_neg (by omega : ¬ i.val < 16)]
              simp only [gammaF]
              rw [if_pos rfl, if_neg (by omega : ¬ i.val < 8),
                  if_neg (by omega : ¬ i.val < 16),
                  if_neg (by omega : ¬ i.val < 24),
                  if_pos rfl,
                  if_neg (by omega : ¬ (partner i).val < 8),
                  if_pos (by omega : (partner i).val < 16)]
              simp
      · have hpij : partner i ≠ partner j := by
          intro h
          apply hij
          have := congr_arg partner h
          rwa [partner_involutive, partner_involutive] at this
        rw [show gammaF (partner i) (partner j) = 0 from by
              simp [gammaF, hpij],
            show gammaF i j = 0 from by simp [gammaF, hij]]
        simp
    · intro k _ hk
      rw [show UJ_matrix i k = 0 from by unfold UJ_matrix; simp [hk]]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro k _ hk
    rw [show UJ_matrix k j = 0 from by unfold UJ_matrix; simp [hk]]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- One-generation Dirac operator: A diagonal, B = Ā, C = E = 0. -/
def DF_oneGen (Ynu Ye Yu Yd : ℝ) : Matrix I32 I32 ℂ :=
  let A : Block8 := diagonal
    ([(Ynu : ℂ), (Ye : ℂ), (Yu : ℂ), (Yd : ℂ),
      (Yu : ℂ), (Yd : ℂ), (Yu : ℂ), (Yd : ℂ)] : Fin 8 → ℂ)
  buildDirac A (A.map starRingEnd ℂ) 0 0

/-- Conditional J-compatibility: requires block symmetries. -/
theorem buildDirac_J_compat (A B C E : Block8)
    (hB : B = A.map starRingEnd ℂ)
    (hC : C = C.transpose) (hE : E = E.transpose) :
    (fun i j => UJ_matrix i j) * (buildDirac A B C E).map Complex.conj *
    (fun i j => UJ_matrix i j) = buildDirac A B C E := by
  sorry

/-- Partial bundle: only axioms verified unconditionally. -/
structure SMFiniteSpectralTriple where
  Dirac : Matrix I32 I32 ℂ
  Gamma : Matrix I32 I32 ℂ
  UJ    : Matrix I32 I32 ℂ
  self_adjoint     : Dirac.conjTranspose = Dirac
  gamma_self_adjoint : Gamma.conjTranspose = Gamma
  gamma_involutive : Gamma * Gamma = 1
  gamma_odd        : Gamma * Dirac + Dirac * Gamma = 0
  J_involutive     : UJ * UJ = 1
  J_gamma_anticomm : UJ * Gamma.map Complex.conj * UJ = -Gamma
  order_zero       : ∀ (a b : AF), pi a * piOp (pi b) - piOp (pi b) * pi a = 0

end CGurd


import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-- The 2×2 complex matrix algebra used throughout CGURD. -/
abbrev C2Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- Diagonal modular flow on the thermal (Y) sector.
    UY(t) = diag(exp(-i t ω₁), exp(-i t ω₂)). -/
def UY (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  ![![Complex.exp (-Complex.I * t * omega1), 0],
    ![0, Complex.exp (-Complex.I * t * omega2)]]
