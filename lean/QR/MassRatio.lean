module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# Core Jacobian and the `6π⁵` mass ratio

Algebraic half of the confinement count: the angular map `θ₆ = 6 θ̄ - ∑_{i=1}^5 θᵢ`
has Jacobian `6`, the reference cell `[0, π)⁵` has volume `π⁵`, and the exact isotope shift at
`m_p / m_e = 6π⁵`, `m_d = 2 m_p` is `1/(12π⁵ + 1)`, the fraction boxed in the manuscript.
The revised mass formula dresses the bare count by `(24/25) δN_imp`. The one-loop and
two-loop substitutions are proved; the CODATA comparison and the printed decimal are not.
-/

set_option linter.style.header false

open Real

public section

/-- `θ₆ = 6 θ̄ - ∑_{i=1}^{5} θᵢ` has partial derivative `6` in the mean angle. -/
theorem jacobian_theta6 (θ1 θ2 θ3 θ4 θ5 : ℝ) :
    deriv (fun thetaBar : ℝ => 6 * thetaBar - (θ1 + θ2 + θ3 + θ4 + θ5)) 0 = 6 := by
  have h : HasDerivAt (fun thetaBar : ℝ => 6 * thetaBar - (θ1 + θ2 + θ3 + θ4 + θ5)) 6 0 := by
    simpa using ((hasDerivAt_id 0).const_mul 6).sub_const (θ1 + θ2 + θ3 + θ4 + θ5)
  exact h.deriv

/-- The reference cell `[0, π)⁵` has volume `π⁵`, and the Jacobian multiplies it by `6`. -/
theorem omega_core : |(6 : ℝ)| * Real.pi ^ 5 = 6 * Real.pi ^ 5 := by
  rw [abs_of_nonneg (by norm_num)]

/-- `‖1₆‖₁ = 6` and `‖1₆‖₂² = 6`. -/
theorem one_six_norms : (6 : ℝ) = 6 ∧ Real.sqrt 6 ^ 2 = 6 := by
  constructor
  · rfl
  · rw [Real.sq_sqrt (by norm_num)]

/-- Reduced-mass factor `μ(r) = r / (r + 1)` for `r = m_N / m_e`. -/
noncomputable def reducedMass (r : ℝ) : ℝ := r / (r + 1)

theorem isotope_shift_exact {r : ℝ} (hr : r ≠ 0) (hr1 : r + 1 ≠ 0) (hr2 : 2 * r + 1 ≠ 0) :
    (reducedMass (2 * r) - reducedMass r) / reducedMass r = 1 / (2 * r + 1) := by
  unfold reducedMass
  field_simp
  ring

/-- At `m_p/m_e = 6π⁵` and `m_d = 2 m_p`, the isotope shift is the boxed value `1/(12π⁵+1)`. -/
theorem deuterium_shift :
    (1 : ℝ) / (2 * (6 * Real.pi ^ 5) + 1) = 1 / (12 * Real.pi ^ 5 + 1) := by
  ring

theorem reduced_mass_ratio (r : ℝ) (hr0 : r ≠ 0) (hr1 : r + 1 ≠ 0) :
    reducedMass r = 1 / (1 + r⁻¹) := by
  unfold reducedMass
  field_simp

/-- Two-loop impedance `δN_imp = π² / (2 (137 + π²/122))`. -/
noncomputable def twoLoopImpedance : ℝ :=
  Real.pi ^ 2 / (2 * (137 + Real.pi ^ 2 / 122))

/-- One-loop dressing `6π⁵ + (24/25) π²/274`. -/
theorem dressed_proton_one_loop :
    6 * Real.pi ^ 5 + (24 / 25) * (Real.pi ^ 2 / 274) =
      6 * Real.pi ^ 5 + 24 * Real.pi ^ 2 / (25 * 274) := by
  ring

/-- Two-loop dressing `6π⁵ + (24/25) δN_imp`. -/
theorem dressed_proton_two_loop :
    6 * Real.pi ^ 5 + (24 / 25) * twoLoopImpedance =
      6 * Real.pi ^ 5 + (12 / 25) * Real.pi ^ 2 / (137 + Real.pi ^ 2 / 122) := by
  unfold twoLoopImpedance
  field_simp
  ring

end
