module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic

/-!
# Static dipole polarizability

Theorem 6.8 (`thm:diagonal_resolvent`, `eq:polarizability_1s`). The manuscript integrand is
`x⁴ e^{-x}`, and `∫₀^∞ x⁴ e^{-x} dx = 24`. With `d₀₀ = 4√6` and `d₁₀ = 2√6` one gets
`α_E(1s) = 9/2` in units `a₀³`.
-/

set_option linter.style.header false

open MeasureTheory Set Real

public section

theorem integral_x4_exp :
    ∫ x in Ioi (0 : ℝ), x ^ (4 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) = 24 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 4) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_nat_eq_factorial]

theorem dipole_d00 : (24 : ℝ) / √6 = 4 * √6 := by
  rw [div_eq_iff (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 6))]
  have hsq : √6 * √6 = 6 := by rw [← sq, Real.sq_sqrt (by norm_num)]
  have hassoc : 4 * √6 * √6 = 4 * (√6 * √6) := by ring
  rw [hassoc, hsq]
  norm_num

theorem integral_x4_shift :
    ∫ x in Ioi (0 : ℝ), x ^ (4 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) = 24 :=
  integral_x4_exp

theorem integral_x5_exp :
    ∫ x in Ioi (0 : ℝ), x ^ (5 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) = 120 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 5) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_nat_eq_factorial]

/-- `d₁₀ = |4 · 24 - 120| / √24 = 2√6`. -/
theorem dipole_d10 : |(4 * 24 - 120 : ℝ)| / Real.sqrt 24 = 2 * √6 := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt 24 = 2 * √6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num), h4]
  have habs : |(4 * 24 - 120 : ℝ)| = 24 := by norm_num
  rw [habs, hsq, div_eq_iff (by positivity : (2 : ℝ) * √6 ≠ 0)]
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have : 2 * √6 * (2 * √6) = 4 * √6 ^ 2 := by ring
  rw [this, h6]
  norm_num

theorem polarizability_value :
    (2 * (2 : ℝ) / 3) * (1 / (2 * 16)) * (96 + 24 / 2) = 9 / 2 := by
  norm_num

/-- In units `e² = 2`, `ζ = g = 2`, the stencil sum `(2 e² / 3) (1/(2 ζ⁴)) (d₀₀² + d₁₀²/2)`
equals `9/2`. -/
theorem polarizability_1s :
    let d00sq := (4 * √6) ^ 2
    let d10sq := (2 * √6) ^ 2
    (2 * (2 : ℝ) / 3) * (1 / (2 * (2 : ℝ) ^ 4)) * (d00sq / 1 + d10sq / 2) = 9 / 2 := by
  simp only
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h6]
  norm_num

end
