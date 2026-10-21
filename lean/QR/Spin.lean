module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import QR.Basic

/-!
# Spin, CHSH, Landé factors, hyperfine arithmetic, and the Schwinger integral

Proposition 2.2 and Theorems 6.10 and 6.12, at the algebraic level: the Tsirelson value
`2√2`, the singlet reduced state `I/2`, `g_J ∈ {2, 2/3, 4/3}` at `g_s = 2`, the hyperfine
factor `5/48`, split as `3/32 + 1/96`, and `∫₀¹ (1-u) du = 1/2`.
-/

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

open Matrix Real intervalIntegral

public section

theorem chsh_tsirelson :
    |(-Real.cos (π / 4)) + Real.cos (3 * π / 4) - Real.cos (π / 4) - Real.cos (π / 4)| =
      2 * √2 := by
  have hcos : Real.cos (3 * π / 4) = -(√2 / 2) := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  rw [hcos, Real.cos_pi_div_four]
  have hsum : |-(√2 / 2) + -(√2 / 2) - √2 / 2 - √2 / 2| = |-(2 * √2)| := by
    congr 1
    ring
  rw [hsum, abs_neg]
  exact abs_of_nonneg (by positivity)

/-- Landé factor at `g_s = 2` and `s(s+1) = 3/4`. -/
def lande (gS ℓ j : ℚ) : ℚ :=
  1 + (gS - 1) * (j * (j + 1) - ℓ * (ℓ + 1) + 3 / 4) / (2 * j * (j + 1))

theorem lande_s (gS : ℚ) (hg : gS = 2) : lande gS 0 (1 / 2) = 2 := by
  rw [hg]
  unfold lande
  norm_num

theorem lande_p_half (gS : ℚ) (hg : gS = 2) : lande gS 1 (1 / 2) = 2 / 3 := by
  rw [hg]
  unfold lande
  norm_num

theorem lande_p_three_halves (gS : ℚ) (hg : gS = 2) : lande gS 1 (3 / 2) = 4 / 3 := by
  rw [hg]
  unfold lande
  norm_num

theorem hfs_bezginov : ((3 : ℚ) / 4 + 1 / 12) * (1 / 8) = 5 / 48 := by
  norm_num

/-- The `2S` contact piece is `3/32` of the `1S` interval and the `2P` piece is `1/96`. -/
theorem hfs_bezginov_split :
    ((3 : ℚ) / 4) * (1 / 8) = 3 / 32 ∧
      (1 / 12) * (1 / 8) = 1 / 96 ∧
      3 / 32 + 1 / 96 = 5 / 48 := by
  norm_num

theorem schwinger_integral : ∫ u in (0 : ℝ)..1, (1 - u) = 1 / 2 := by
  have hid : ∫ u in (0 : ℝ)..1, u = 1 / 2 := by
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      intro x _
      have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      simpa using hpow.div_const 2
    rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
    ring
  have hone : ∫ u in (0 : ℝ)..1, (1 : ℝ) = 1 := by simp
  have hsplit : ∫ u in (0 : ℝ)..1, (1 - u) =
      (∫ u in (0 : ℝ)..1, (1 : ℝ)) - ∫ u in (0 : ℝ)..1, u :=
    integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hsplit, hone, hid]
  ring

/-- Once the one-loop form factor has been reduced to this integral, `a_e = α/(2π)`. -/
theorem schwinger_anomaly {aE α : ℝ}
    (hform : aE = α / Real.pi * (∫ u in (0 : ℝ)..1, (1 - u))) :
    aE = α / (2 * Real.pi) := by
  rw [hform, schwinger_integral]
  ring

/-- Unnormalized singlet `ψ = |01⟩ - |10⟩`. -/
def singlet : Fin 2 → Fin 2 → ℂ
  | 0, 1 => 1
  | 1, 0 => -1
  | _, _ => 0

/-- Partial trace over the first factor. -/
def partialB (ψ : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) : ℂ :=
  ∑ a : Fin 2, star (ψ a i) * ψ a j

theorem singlet_reduced (i j : Fin 2) :
    partialB singlet i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [partialB, singlet, Fin.sum_univ_two, Complex.star_def]

theorem singlet_norm : ∑ a : Fin 2, ∑ b : Fin 2, ‖singlet a b‖ ^ 2 = 2 := by
  simp [singlet, Fin.sum_univ_two]
  norm_num

/-- Normalized on `⟨ψ|ψ⟩ = 2`, the reduced state is `I/2`. -/
theorem singlet_reduced_normalized (i j : Fin 2) :
    partialB singlet i j / 2 = if i = j then (1 / 2 : ℂ) else 0 := by
  rw [singlet_reduced]
  split_ifs <;> norm_num

/-- Sheet projectors `P± = (I ± σ₃)/2` (`eq:weak_chiral_vertex`). -/
noncomputable def chiralPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + !![1, 0; 0, -1])

noncomputable def chiralMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - !![1, 0; 0, -1])

def sigma2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

theorem chiral_projectors_sum : chiralPlus + chiralMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] <;>
    norm_num

theorem chiral_same_sheet : chiralPlus * sigma2 * chiralPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, sigma2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Complex.ext_iff, Complex.I_re, Complex.I_im]

/-- The opposite-sheet vertex is the single matrix entry `P₋ σ₂ P₊ = [[0, 0], [i, 0]]`. -/
theorem chiral_vertex : chiralMinus * sigma2 * chiralPlus = !![0, 0; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralMinus, chiralPlus, sigma2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Complex.ext_iff,
      Complex.I_re, Complex.I_im] ;
    norm_num

end
