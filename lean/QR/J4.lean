module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

/-!
# The `J₄` complex

Finite-matrix content of Theorem 5.1 (`thm:transverse_photon`) and the `ℓ = 3` count in
Appendix E: the film-line incidence `M_LF`, its two-dimensional kernel, the Walsh frame of
`V_{3D}`, and the rank-3 octupole constraint `C_{ℓ=3}`. The Frobenius count is
`‖M_LF‖_F² = 12`, so the two-sheet cage plus the monopole port is `25` and the trapped
fraction is `24/25`.
-/

set_option linter.style.header false
set_option linter.unusedSimpArgs false

open Matrix Finset

public section

/-! ## Film-line incidence -/

/-- Incidence of the four tetrahedral lines against the six films
`F₁₂, F₁₃, F₁₄, F₂₃, F₂₄, F₃₄` (`eq:mainM`). -/
def MLF : Matrix (Fin 4) (Fin 6) ℚ :=
  !![1, 1, 1, 0, 0, 0;
     1, 0, 0, 1, 1, 0;
     0, 1, 0, 1, 0, 1;
     0, 0, 1, 0, 1, 1]

/-- Leading `4×4` minor of `MLF`. -/
def MLFminor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 1, 1, 0;
     1, 0, 0, 1;
     0, 1, 0, 1;
     0, 0, 1, 0]

/-- Explicit inverse of the leading minor. Its existence is `rank M_LF = 4`. -/
def MLFminorInv : Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 1/2,  1/2, -1/2, -1/2;
      1/2, -1/2,  1/2, -1/2;
        0,    0,    0,    1;
     -1/2,  1/2,  1/2,  1/2]

/-- Integer generator of the `d_{x²-y²}` kernel direction. -/
def egX2Y2 : Fin 6 → ℚ := ![1, -1, 0, 0, -1, 1]

/-- Integer generator of the `d_{z²}` kernel direction. -/
def egZ2 : Fin 6 → ℚ := ![-1, -1, 2, 2, -1, -1]

theorem MLFminor_inv_left : MLFminor * MLFminorInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MLFminor, MLFminorInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem MLFminor_inv_right : MLFminorInv * MLFminor = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MLFminor, MLFminorInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem MLF_egX2Y2 : MLF.mulVec egX2Y2 = 0 := by
  ext i
  fin_cases i <;> simp [MLF, egX2Y2, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

theorem MLF_egZ2 : MLF.mulVec egZ2 = 0 := by
  ext i
  fin_cases i <;> simp [MLF, egZ2, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

theorem MLF_entry_idem (i : Fin 4) (j : Fin 6) : (MLF i j) ^ 2 = MLF i j := by
  fin_cases i <;> fin_cases j <;> simp [MLF]

theorem MLF_rowSum (j : Fin 6) : ∑ i : Fin 4, MLF i j = 2 := by
  fin_cases j <;> simp [MLF, Fin.sum_univ_four] <;> norm_num

/-- `‖M_LF‖_F² = 12`: twelve line--film attachments on one sheet. -/
theorem MLF_frobenius : ∑ j : Fin 6, ∑ i : Fin 4, (MLF i j) ^ 2 = 12 := by
  simp_rw [MLF_entry_idem]
  simp [MLF_rowSum, Fin.sum_univ_six]
  norm_num

theorem cage_boundary : 2 * 12 + 1 = 25 ∧ (24 : ℚ) / 25 + 1 / 25 = 1 := by norm_num

/-- `1₄ᵀ M_LF = 2 1₆ᵀ`, so every kernel vector is orthogonal to the all-ones vector. -/
theorem MLF_ker_sum_zero (x : Fin 6 → ℚ) (hx : MLF.mulVec x = 0) :
    ∑ j : Fin 6, x j = 0 := by
  have hrows : ∀ i : Fin 4, (MLF.mulVec x) i = 0 := by
    intro i
    simp [hx]
  have hsum : ∑ i : Fin 4, (MLF.mulVec x) i = 0 := by simp [hrows]
  have hinter : ∑ i : Fin 4, (MLF.mulVec x) i = ∑ j : Fin 6, (∑ i : Fin 4, MLF i j) * x j := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hinter, Finset.sum_congr rfl (fun j _ => by rw [MLF_rowSum j])] at hsum
  have h2 : (2 : ℚ) * ∑ j : Fin 6, x j = 0 := by
    simpa [Finset.mul_sum] using hsum
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

theorem MLF_ker_coords (x : Fin 6 → ℚ) (hx : MLF.mulVec x = 0) :
    x 0 = x 5 ∧ x 1 = x 4 ∧ x 2 = -(x 4 + x 5) ∧ x 3 = -(x 4 + x 5) := by
  have row : ∀ i : Fin 4, (MLF.mulVec x) i = 0 := by intro i; simp [hx]
  have h0 := row 0
  have h1 := row 1
  have h2 := row 2
  have h3 := row 3
  simp [MLF, Matrix.mulVec, dotProduct, Fin.sum_univ_six] at h0 h1 h2 h3
  have hx0 : x 0 = x 5 := by linarith
  have hx1 : x 1 = x 4 := by linarith
  have hx2 : x 2 = -(x 4 + x 5) := by linarith
  have hx3 : x 3 = -(x 4 + x 5) := by linarith
  exact ⟨hx0, hx1, hx2, hx3⟩

/-- The two integer kernel vectors span `ker M_LF` (`hyd:eq:eg_basis`). -/
theorem MLF_ker_span (x : Fin 6 → ℚ) (hx : MLF.mulVec x = 0) :
    x = ((x 5 - x 4) / 2) • egX2Y2 + (-(x 4 + x 5) / 2) • egZ2 := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := MLF_ker_coords x hx
  ext i
  fin_cases i <;> simp [egX2Y2, egZ2, hx0, hx1, hx2, hx3] <;> ring

theorem MLF_ker_indep {a b : ℚ} (h : a • egX2Y2 + b • egZ2 = 0) : a = 0 ∧ b = 0 := by
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp [egX2Y2, egZ2] at h0 h1
  constructor <;> linarith

/-- The all-ones matrix `1₄ 1₄ᵀ`. -/
def allOnes4 : Matrix (Fin 4) (Fin 4) ℚ := Matrix.of (fun _ _ => 1)

/-- Gram identity `M_LF M_LFᵀ = 2 I₄ + 1₄ 1₄ᵀ`. -/
theorem MLF_gram :
    MLF * MLF.transpose = (2 : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) + allOnes4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MLF, allOnes4, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply] <;> norm_num

/-! ## Walsh frame of `V_{3D}` -/

def walshX : Fin 4 → ℚ := ![1, 1, -1, -1]
def walshY : Fin 4 → ℚ := ![1, -1, 1, -1]
def walshZ : Fin 4 → ℚ := ![1, -1, -1, 1]

theorem walsh_norm_x : walshX ⬝ᵥ walshX = 4 := by
  simp [walshX, dotProduct, Fin.sum_univ_four]; norm_num

theorem walsh_norm_y : walshY ⬝ᵥ walshY = 4 := by
  simp [walshY, dotProduct, Fin.sum_univ_four]; norm_num

theorem walsh_norm_z : walshZ ⬝ᵥ walshZ = 4 := by
  simp [walshZ, dotProduct, Fin.sum_univ_four]; norm_num

theorem walsh_orth_xy : walshX ⬝ᵥ walshY = 0 := by
  simp [walshX, walshY, dotProduct, Fin.sum_univ_four]

theorem walsh_orth_xz : walshX ⬝ᵥ walshZ = 0 := by
  simp [walshX, walshZ, dotProduct, Fin.sum_univ_four]

theorem walsh_orth_yz : walshY ⬝ᵥ walshZ = 0 := by
  simp [walshY, walshZ, dotProduct, Fin.sum_univ_four]

theorem walsh_sum_x : ∑ i : Fin 4, walshX i = 0 := by simp [walshX, Fin.sum_univ_four]
theorem walsh_sum_y : ∑ i : Fin 4, walshY i = 0 := by simp [walshY, Fin.sum_univ_four]
theorem walsh_sum_z : ∑ i : Fin 4, walshZ i = 0 := by simp [walshZ, Fin.sum_univ_four]

/-- A sum-zero 4-vector is the Walsh combination with coefficients `(a+b)/2`, `(a+c)/2`, `(a+d)/2`
(`eq:mainWalsh`). -/
theorem walsh_reconstruct (a b c d : ℚ) (hsum : a + b + c + d = 0) :
    ![a, b, c, d] =
      ((a + b) / 2) • walshX + ((a + c) / 2) • walshY + ((a + d) / 2) • walshZ := by
  ext i
  fin_cases i <;> simp [walshX, walshY, walshZ] <;> linarith [hsum]

/-- A single tetrahedral line is not Kirchhoff-neutral: its port sum is `1`, while every Walsh
direction and both `e_g` generators sum to `0`. -/
theorem single_line_not_neutral : ∑ i : Fin 4, (![1, 0, 0, 0] : Fin 4 → ℚ) i = 1 := by
  simp [Fin.sum_univ_four]

/-! ## Octupole constraint `C_{ℓ=3}` -/

/-- Dipole-conservation matrix on `Sym³`, ordered
`{xxx, yyy, zzz, xyy, xzz, yxx, yzz, zxx, zyy, xyz}`. -/
def C3 : Matrix (Fin 3) (Fin 10) ℚ :=
  !![1, 0, 0, 1, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 1, 1, 0]

lemma sum_fin10 (f : Fin 10 → ℚ) :
    ∑ i : Fin 10, f i =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem C3_ker_iff (x : Fin 10 → ℚ) :
    C3.mulVec x = 0 ↔
      x 0 = -x 3 - x 4 ∧ x 1 = -x 5 - x 6 ∧ x 2 = -x 7 - x 8 := by
  constructor
  · intro hx
    have row : ∀ i : Fin 3, (C3.mulVec x) i = 0 := by intro i; simp [hx]
    have h0 := row 0
    have h1 := row 1
    have h2 := row 2
    simp [C3, Matrix.mulVec, dotProduct, sum_fin10] at h0 h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;> simp [C3, Matrix.mulVec, dotProduct, sum_fin10, h0, h1, h2] <;> ring

/-- `dim H_ℓ = C(ℓ+2, 2) - C(ℓ, 2) = 2ℓ+1`. -/
theorem harmonic_dimension (ℓ : ℕ) : (ℓ + 2).choose 2 = ℓ.choose 2 + (2 * ℓ + 1) := by
  induction ℓ with
  | zero => decide
  | succ ℓ ih =>
    rw [show ℓ + 1 + 2 = (ℓ + 2) + 1 by ring, Nat.choose_succ_succ' (ℓ + 2) 1,
      Nat.choose_one_right, ih]
    have hnext : (ℓ + 1).choose 2 = ℓ.choose 2 + ℓ := by
      rw [Nat.choose_succ_succ' ℓ 1, Nat.choose_one_right]
      ring
    rw [hnext]
    ring

/-- One sheet of shell `n` holds `∑_{ℓ<n} (2ℓ+1) = n²` angular slots. -/
theorem shell_capacity (n : ℕ) : ∑ ℓ ∈ range n, (2 * ℓ + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

/-- The bilayer doubles the count. -/
theorem bilayer_capacity (n : ℕ) : 2 * ∑ ℓ ∈ range n, (2 * ℓ + 1) = 2 * n ^ 2 := by
  rw [shell_capacity]

end
