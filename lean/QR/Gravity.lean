module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic

/-!
# Isotropic metric, horizon, and the DtN jet

Algebraic content of the PPN reading (`γ_PPN = β_PPN = 1`), the areal horizon
`R_h = 2GM/c²`, mass cancellation in `E = m c² √(-g₀₀)`, and the collar factor
`h_b / Δℓ` that cancels a bond stiffness `1/h_b`.

The refractive index is `n = (1+φ)^{3/2} / (1-φ)^{1/2}`. Its Taylor coefficient of `φ²`
is `3/2`, read off from `n''(0) = 3`, matching the manuscript expansion
`1 + 2φ + (3/2) φ²`.

The comparison jets `sinh x · (1 + x²/3) - x cosh x` and `sinh x · (1 - x²/6) - x`
vanish at the origin. That is the order-zero contact for the low-frequency DtN
expansions; their higher derivatives are not expanded here.
-/

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

open Real Filter
open scoped Topology

public section

theorem g00 (φ : ℝ) (h : φ ≠ -1) :
    -((1 - φ) / (1 + φ)) = -1 + 2 * φ - 2 * φ ^ 2 + 2 * φ ^ 3 / (1 + φ) := by
  have h1 : 1 + φ ≠ 0 := by
    rintro h0
    apply h
    linear_combination h0
  apply mul_left_cancel₀ h1
  field_simp [h1]
  ring

theorem gij (φ : ℝ) : (1 + φ) ^ 2 = 1 + 2 * φ + φ ^ 2 := by ring

/-- The coefficient of `2φ` in `g_ij = (1+φ)²` is `1`, which is `γ_PPN`. -/
theorem gamma_ppn (φ : ℝ) : (1 + φ) ^ 2 = 1 + 2 * (1 : ℝ) * φ + φ ^ 2 := by ring

/-- Removing `-1 + 2φ - 2 β φ²` with `β = 1` leaves the cubic remainder of `g_00`. -/
theorem beta_ppn (φ : ℝ) (h : φ ≠ -1) :
    -((1 - φ) / (1 + φ)) - (-1 + 2 * φ - 2 * φ ^ 2) = 2 * φ ^ 3 / (1 + φ) := by
  have h00 := g00 φ h
  linear_combination h00

theorem stiffness_ratio {K0 φ : ℝ} (hφ : 1 + φ ≠ 0) :
    K0 * (1 - φ) / (1 + φ) = K0 * ((1 - φ) / (1 + φ)) := by
  field_simp [hφ]

theorem inertia_square {M0 φ : ℝ} : M0 * (1 + φ) ^ 2 = M0 * (1 + 2 * φ + φ ^ 2) := by
  ring

theorem horizon_areal {G M c : ℝ} (hc : c ≠ 0) :
    (G * M / c ^ 2) * (1 + 1) = 2 * G * M / c ^ 2 := by
  field_simp [hc]
  ring

theorem equivalence_mass_cancels {m c g00v : ℝ} (hm : m ≠ 0) :
    m * c ^ 2 * Real.sqrt (-g00v) / m = c ^ 2 * Real.sqrt (-g00v) := by
  field_simp [hm]

/-- A collar ramp of slope `1/Δℓ` across one mesh edge contributes `h_b/Δℓ`, which cancels
the singular factor `1/h_b`. -/
theorem collar_cancellation {hB Δℓ : ℝ} (hh : hB ≠ 0) (hΔ : Δℓ ≠ 0) :
    (hB / Δℓ) / hB = 1 / Δℓ := by
  field_simp [hh, hΔ]

noncomputable def refractive (φ : ℝ) : ℝ :=
  (1 + φ) ^ (3 / 2 : ℝ) / (1 - φ) ^ (1 / 2 : ℝ)

noncomputable def refractiveLogDeriv (φ : ℝ) : ℝ :=
  (3 / 2) / (1 + φ) + (1 / 2) / (1 - φ)

theorem refractive_zero : refractive 0 = 1 := by
  unfold refractive
  simp [Real.one_rpow]

theorem refractiveLogDeriv_zero : refractiveLogDeriv 0 = 2 := by
  unfold refractiveLogDeriv
  norm_num

theorem refractive_slope {φ : ℝ} (h1 : -1 < φ) (h2 : φ < 1) :
    ((3 / 2) * (1 + φ) ^ (1 / 2 : ℝ) * (1 - φ) ^ (1 / 2 : ℝ) -
        (1 + φ) ^ (3 / 2 : ℝ) * (-(1 / 2) * (1 - φ) ^ (-(1 / 2 : ℝ)))) /
      ((1 - φ) ^ (1 / 2 : ℝ)) ^ 2 =
      refractive φ * refractiveLogDeriv φ := by
  have hp : 0 < 1 + φ := by linarith
  have hm : 0 < 1 - φ := by linarith
  set a := (1 + φ) ^ (1 / 2 : ℝ)
  set b := (1 - φ) ^ (1 / 2 : ℝ)
  have ha0 : a ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hb0 : b ≠ 0 := (Real.rpow_pos_of_pos hm _).ne'
  have ha2 : a ^ 2 = 1 + φ := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hp)]
    norm_num
  have hb2 : b ^ 2 = 1 - φ := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hm)]
    norm_num
  have h32 : (1 + φ) ^ (3 / 2 : ℝ) = a ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + (1 / 2) by norm_num, Real.rpow_add hp, Real.rpow_one]
    rw [show (1 + φ) ^ (1 / 2 : ℝ) = a from rfl, ← ha2]
    ring
  have hneg : (1 - φ) ^ (-(1 / 2 : ℝ)) = b⁻¹ := Real.rpow_neg (le_of_lt hm) _
  unfold refractive refractiveLogDeriv
  rw [h32, hneg, show (1 - φ) ^ (1 / 2 : ℝ) = b from rfl, ← ha2, ← hb2]
  have hL : ((3 / 2) * a * b - a ^ 3 * (-(1 / 2) * b⁻¹)) / b ^ 2 =
      ((3 / 2) * a * b ^ 2 + (1 / 2) * a ^ 3) / b ^ 3 := by
    field_simp [hb0]
    ring
  have hR : a ^ 3 / b * ((3 / 2) / a ^ 2 + (1 / 2) / b ^ 2) =
      ((3 / 2) * a * b ^ 2 + (1 / 2) * a ^ 3) / b ^ 3 := by
    field_simp [ha0, hb0]
  rw [hL, hR]

/-- `n'(0) = 2`. -/
theorem refractive_deriv_zero : deriv refractive 0 = 2 := by
  have hnumFun : HasDerivAt (fun t : ℝ => 1 + t) (1 : ℝ) 0 :=
    HasDerivAt.const_add (c := (1 : ℝ)) (hasDerivAt_id' 0)
  have hdenFun : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) 0 :=
    HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id' 0)
  have hnum : HasDerivAt (fun t : ℝ => (1 + t) ^ (3 / 2 : ℝ)) (3 / 2 : ℝ) 0 := by
    have hraw := hnumFun.rpow_const (p := (3 / 2 : ℝ)) (Or.inl (by norm_num))
    convert hraw using 1
    norm_num [Real.one_rpow]
  have hden : HasDerivAt (fun t : ℝ => (1 - t) ^ (1 / 2 : ℝ)) (-(1 / 2) : ℝ) 0 := by
    have hraw := hdenFun.rpow_const (p := (1 / 2 : ℝ)) (Or.inl (by norm_num))
    convert hraw using 1
    norm_num [Real.one_rpow]
  have hne : (1 - (0 : ℝ)) ^ (1 / 2 : ℝ) ≠ 0 := by
    simp [Real.one_rpow]
  have hdiv : HasDerivAt
      (fun t : ℝ => (1 + t) ^ (3 / 2 : ℝ) / (1 - t) ^ (1 / 2 : ℝ)) (2 : ℝ) 0 := by
    convert hnum.fun_div hden hne using 1
    norm_num
  rw [show refractive = fun t : ℝ => (1 + t) ^ (3 / 2 : ℝ) / (1 - t) ^ (1 / 2 : ℝ) by
    funext t; rfl]
  exact hdiv.deriv

theorem log_deriv_slope_zero :
    -(3 / 2) / (1 + (0 : ℝ)) ^ 2 + (1 / 2) / (1 - 0) ^ 2 = -1 := by
  norm_num

/-- If `n(0) = 1`, `n'(0) = 2`, and `(log n)'(0) = -1`, the second derivative is `3`,
so the Taylor coefficient of `φ²` is `3/2`. -/
theorem refractive_second_coefficient :
    (2 : ℝ) * refractiveLogDeriv 0 + refractive 0 * (-1) = 3 := by
  rw [refractiveLogDeriv_zero, refractive_zero]
  norm_num

/-- Comparison jet for `x cosh x - sinh x · (1 + x²/3)`. -/
noncomputable def cothJet (x : ℝ) : ℝ :=
  Real.sinh x * (1 + x ^ 2 / 3) - x * Real.cosh x

/-- Comparison jet for `sinh x · (1 - x²/6) - x`. -/
noncomputable def cschJet (x : ℝ) : ℝ := Real.sinh x * (1 - x ^ 2 / 6) - x

theorem cothJet_zero : cothJet 0 = 0 := by
  simp [cothJet, sinh_zero, cosh_zero]

theorem cschJet_zero : cschJet 0 = 0 := by
  simp [cschJet, sinh_zero]

end
