module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-!
# Port partition and the Feshbach--Schur impedance

`T21` as revised on main: `N_cells(J₄) = 15`, one pinch oscillator, `N_cell = 16`,
`N_tot = 137`, and `N_dyn = 122`. The fundamental Dirichlet mode on `[0,1]` has kinetic
expectation `π²`, and the paper's `ℰ₁` is half of that, `π²/2`. One loop is
`137 + π²/274`. Two loops replace the denominator by `137 + π²/122`. The high-`Q²` running
and the continuum Ward identity stay outside the kernel.
-/

set_option linter.style.header false

open Real intervalIntegral

public section

theorem cell_count_16 : ∑ m ∈ Finset.range (4 + 1), Nat.choose 4 m = 16 := by
  simpa using Nat.sum_range_choose 4

theorem port_total_137 : 120 + 16 + 1 = 137 := by norm_num

theorem integral_id_pi : ∫ x in (0 : ℝ)..Real.pi, x = Real.pi ^ 2 / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi, HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    simpa using hpow.div_const 2
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- `α_EM⁻¹ = 137 + (1/137) ∫₀^π θ dθ = 137 + π²/274`. -/
theorem alpha_inverse_ports :
    (137 : ℝ) + (1 / 137) * (Real.pi ^ 2 / 2) = 137 + Real.pi ^ 2 / 274 := by
  ring

theorem alpha_inverse_from_integral :
    (137 : ℝ) + (1 / 137) * (∫ x in (0 : ℝ)..Real.pi, x) = 137 + Real.pi ^ 2 / 274 := by
  rw [integral_id_pi, alpha_inverse_ports]

/-- Static cells of the `1--4--6--4` complex, plus the core pinch oscillator. -/
theorem static_cells : 1 + 4 + 6 + 4 = 15 := by norm_num

theorem cell_with_pinch : 15 + 1 = 16 := by norm_num

theorem port_total_split : 120 + (15 + 1) + 1 = 137 := by norm_num

/-- Dynamical channels: every interface mode except the `15` static cells. -/
theorem dyn_channels : 137 - 15 = 122 ∧ 120 + 1 + 1 = 122 := by norm_num

theorem integral_cos_double :
    ∫ s in (0 : ℝ)..1, Real.cos (2 * Real.pi * s) = 0 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.sin (2 * Real.pi * s) / (2 * Real.pi))
        (Real.cos (2 * Real.pi * x)) x := by
    intro x _
    have hlin : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
    have hsin := (Real.hasDerivAt_sin (2 * Real.pi * x)).comp x hlin
    have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    exact (hsin.div_const (2 * Real.pi)).congr_deriv (by field_simp [hπ])
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [Real.sin_zero, Real.sin_two_pi]

theorem integral_cos_sq_pi :
    ∫ s in (0 : ℝ)..1, Real.cos (Real.pi * s) ^ 2 = 1 / 2 := by
  have hint : ∀ s, Real.cos (Real.pi * s) ^ 2 =
      1 / 2 + Real.cos (2 * Real.pi * s) / 2 := by
    intro s
    simpa [mul_assoc] using Real.cos_sq (Real.pi * s)
  rw [intervalIntegral.integral_congr (fun s _ => hint s)]
  rw [integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hconst : ∫ s in (0 : ℝ)..1, (1 : ℝ) / 2 = 1 / 2 := by
    simp
  have hcos : ∫ s in (0 : ℝ)..1, Real.cos (2 * Real.pi * s) / 2 = 0 := by
    rw [intervalIntegral.integral_div, integral_cos_double]
    simp
  rw [hconst, hcos]
  ring

/-- `ψ₁(s) = √2 sin(π s)` vanishes at the sheet endpoints. -/
theorem dirichlet_mode_boundary :
    Real.sqrt 2 * Real.sin (Real.pi * 0) = 0 ∧
      Real.sqrt 2 * Real.sin (Real.pi * 1) = 0 := by
  simp [Real.sin_zero, Real.sin_pi]

/-- `ψ₁` is normalized on `[0,1]`. -/
theorem dirichlet_mode_norm :
    ∫ s in (0 : ℝ)..1, (Real.sqrt 2 * Real.sin (Real.pi * s)) ^ 2 = 1 := by
  have hpow : ∀ s, (Real.sqrt 2 * Real.sin (Real.pi * s)) ^ 2 =
      1 - Real.cos (2 * Real.pi * s) := by
    intro s
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsin : Real.sin (Real.pi * s) ^ 2 =
        1 / 2 - Real.cos (2 * Real.pi * s) / 2 := by
      simpa [mul_assoc] using Real.sin_sq_eq_half_sub (Real.pi * s)
    calc
      (Real.sqrt 2 * Real.sin (Real.pi * s)) ^ 2 =
          (Real.sqrt 2) ^ 2 * Real.sin (Real.pi * s) ^ 2 := by ring
      _ = 2 * Real.sin (Real.pi * s) ^ 2 := by rw [hsqrt]
      _ = 1 - Real.cos (2 * Real.pi * s) := by rw [hsin]; ring
  rw [intervalIntegral.integral_congr (fun s _ => hpow s),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hconst : ∫ _s in (0 : ℝ)..1, (1 : ℝ) = 1 := by simp
  rw [hconst, integral_cos_double]
  ring

/-- `ψ₁'(s) = √2 π cos(π s)`. -/
theorem dirichlet_mode_deriv (s : ℝ) :
    HasDerivAt (fun t => Real.sqrt 2 * Real.sin (Real.pi * t))
      (Real.sqrt 2 * Real.pi * Real.cos (Real.pi * s)) s := by
  have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi s := by
    simpa using (hasDerivAt_id s).const_mul Real.pi
  have hsin := (Real.hasDerivAt_sin (Real.pi * s)).comp s hlin
  convert hsin.const_mul (Real.sqrt 2) using 1
  · ext t
    rfl
  · ring

/-- Pointwise, `-ψ₁'' = π² ψ₁`. -/
theorem dirichlet_mode_second_deriv (s : ℝ) :
    HasDerivAt (fun t => Real.sqrt 2 * Real.pi * Real.cos (Real.pi * t))
      (-(Real.pi ^ 2) * (Real.sqrt 2 * Real.sin (Real.pi * s))) s := by
  have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi s := by
    simpa using (hasDerivAt_id s).const_mul Real.pi
  have hcos := (Real.hasDerivAt_cos (Real.pi * s)).comp s hlin
  have hmul := hcos.const_mul (Real.sqrt 2 * Real.pi)
  convert hmul using 1
  · ext t
    rfl
  · ring

/-- `½ ∫ ψ₁ (-ψ₁'') = π²/2`, the eigenvalue form of `ℰ₁`. -/
theorem dirichlet_mode_eigen_energy :
    (1 / 2) * ∫ s in (0 : ℝ)..1,
        (Real.sqrt 2 * Real.sin (Real.pi * s)) *
          (Real.pi ^ 2 * Real.sqrt 2 * Real.sin (Real.pi * s)) =
      Real.pi ^ 2 / 2 := by
  have hpow : ∀ s, (Real.sqrt 2 * Real.sin (Real.pi * s)) *
      (Real.pi ^ 2 * Real.sqrt 2 * Real.sin (Real.pi * s)) =
      Real.pi ^ 2 * (Real.sqrt 2 * Real.sin (Real.pi * s)) ^ 2 := by
    intro s
    ring
  rw [intervalIntegral.integral_congr (fun s _ => hpow s),
    intervalIntegral.integral_const_mul, dirichlet_mode_norm]
  ring

/-- Half the kinetic expectation of `ψ₁` is `π²/2`, which is the paper's `ℰ₁`. -/
theorem dirichlet_mode_energy :
    (1 / 2) * ∫ s in (0 : ℝ)..1,
        (Real.sqrt 2 * Real.pi * Real.cos (Real.pi * s)) ^ 2 =
      Real.pi ^ 2 / 2 := by
  have hpow : ∀ s, (Real.sqrt 2 * Real.pi * Real.cos (Real.pi * s)) ^ 2 =
      2 * Real.pi ^ 2 * Real.cos (Real.pi * s) ^ 2 := by
    intro s
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      (Real.sqrt 2 * Real.pi * Real.cos (Real.pi * s)) ^ 2 =
          (Real.sqrt 2) ^ 2 * Real.pi ^ 2 * Real.cos (Real.pi * s) ^ 2 := by ring
      _ = 2 * Real.pi ^ 2 * Real.cos (Real.pi * s) ^ 2 := by rw [hsqrt]
  rw [intervalIntegral.integral_congr (fun s _ => hpow s),
    intervalIntegral.integral_const_mul, integral_cos_sq_pi]
  ring

theorem sigma_dyn : 2 * (Real.pi ^ 2 / 2) / 122 = Real.pi ^ 2 / 122 := by ring

theorem impedance_expansion {N D a : ℝ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hden : N + a / D ≠ 0) :
    (a / 2) / (N + a / D) =
      a / (2 * N) - a ^ 2 / (2 * N ^ 2 * D) +
        a ^ 3 / (2 * N ^ 2 * D ^ 2 * (N + a / D)) := by
  have hfrac : N + a / D = (N * D + a) / D := by
    field_simp [hD]
  have hsum : N * D + a ≠ 0 := by
    intro h
    rw [hfrac, h, zero_div] at hden
    exact hden rfl
  calc
    (a / 2) / (N + a / D) = (a / 2) * (D / (N * D + a)) := by
      rw [hfrac]
      field_simp [hD, hsum]
    _ = a * D / (2 * (N * D + a)) := by
      field_simp [hsum]
    _ = a / (2 * N) - a ^ 2 / (2 * N ^ 2 * D) +
        a ^ 3 / (2 * N ^ 2 * D * (N * D + a)) := by
      field_simp [hN, hD, hsum]
      set s := D * N + a
      have hs0 : s ≠ 0 := by
        rw [show s = N * D + a by ring]
        exact hsum
      apply mul_right_cancel₀ hs0
      field_simp [hs0]
      ring
    _ = a / (2 * N) - a ^ 2 / (2 * N ^ 2 * D) +
        a ^ 3 / (2 * N ^ 2 * D ^ 2 * ((N * D + a) / D)) := by
      field_simp [hD, hsum]
    _ = a / (2 * N) - a ^ 2 / (2 * N ^ 2 * D) +
        a ^ 3 / (2 * N ^ 2 * D ^ 2 * (N + a / D)) := by
      rw [← hfrac]

theorem two_loop_impedance :
    (Real.pi ^ 2 / 2) / (137 + Real.pi ^ 2 / 122) =
      Real.pi ^ 2 / (2 * 137) - Real.pi ^ 4 / (2 * 137 ^ 2 * 122) +
        Real.pi ^ 6 / (2 * 137 ^ 2 * 122 ^ 2 * (137 + Real.pi ^ 2 / 122)) := by
  have h := impedance_expansion (N := (137 : ℝ)) (D := 122) (a := Real.pi ^ 2)
    (by norm_num) (by norm_num) (by positivity)
  have h2 : (Real.pi ^ 2) ^ 2 = Real.pi ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  have h3 : (Real.pi ^ 2) ^ 3 = Real.pi ^ 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul]
  simpa [h2, h3] using h

/-- The two-loop truncation sits strictly below the closed impedance. -/
theorem two_loop_truncation_below :
    Real.pi ^ 2 / (2 * 137) - Real.pi ^ 4 / (2 * 137 ^ 2 * 122) <
      Real.pi ^ 2 / (2 * (137 + Real.pi ^ 2 / 122)) := by
  have h := two_loop_impedance
  have hpos : 0 < Real.pi ^ 6 /
      (2 * 137 ^ 2 * 122 ^ 2 * (137 + Real.pi ^ 2 / 122)) := by positivity
  have hclosed : (Real.pi ^ 2 / 2) / (137 + Real.pi ^ 2 / 122) =
      Real.pi ^ 2 / (2 * (137 + Real.pi ^ 2 / 122)) := by
    rw [div_div]
  linarith

end
