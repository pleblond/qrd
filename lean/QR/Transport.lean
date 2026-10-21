module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic

/-!
# Variable-stretch transport and the non-Markovian residual

Theorem 2.3 (`thm:variable_stretch`): the integrand cancellation that makes `dQ/dt` a pure
boundary term, and the adiabatic law `ω ∝ 1/τ`. Theorem 4.1 and `eq:nonmarkov_rate_residual`:
the series `−ln(1-p)/p − 1 = ∑_{m≥1} p^m/(m+1)`.
-/

set_option linter.style.header false

open Real

public section

/-- Pointwise cancellation for a real story amplitude obeying the variable-stretch PDE. -/
theorem stretch_integrand {τ τ' J Js Jt : ℝ} (hτ : τ ≠ 0)
    (hJ : Jt = -(1 / τ) * Js - (τ' / (2 * τ)) * J) :
    τ' * J ^ 2 + τ * (2 * J * Jt) = -(2 * J * Js) := by
  rw [hJ]
  field_simp [hτ]
  ring

theorem adiabatic_ratio {Ω0 τ1 τ2 : ℝ} (hΩ : Ω0 ≠ 0) (h1 : τ1 ≠ 0) (h2 : τ2 ≠ 0) :
    (Ω0 / τ2) / (Ω0 / τ1) = τ1 / τ2 := by
  field_simp [hΩ, h1, h2]

theorem adiabatic_chain {Ω0 τ τ' : ℝ} (hτ : τ ≠ 0) :
    -(τ' / τ ^ 2) * Ω0 = -(τ' / τ) * (Ω0 / τ) := by
  field_simp [hτ]

theorem adiabatic_deriv {Ω0 : ℝ} {τ : ℝ → ℝ} {t τ' : ℝ}
    (hτ : HasDerivAt τ τ' t) (h0 : τ t ≠ 0) :
    HasDerivAt (fun s => Ω0 / τ s) ((-Ω0 / (τ t) ^ 2) * τ') t := by
  have hconst : HasDerivAt (fun _ : ℝ => Ω0) 0 t := hasDerivAt_const t Ω0
  exact (hconst.fun_div hτ h0).congr_deriv (by ring)

theorem squeeze_log {τi τf : ℝ} (hi : 0 < τi) (hf : 0 < τf) :
    -((1 / 2) * Real.log (τi / τf)) = (1 / 2) * Real.log (τf / τi) := by
  rw [Real.log_div hi.ne' hf.ne', Real.log_div hf.ne' hi.ne']
  ring

theorem nonmarkov_closed {p : ℝ} (hp0 : p ≠ 0) :
    -Real.log (1 - p) / p - 1 = (-Real.log (1 - p) - p) / p := by
  field_simp [hp0]

/-- `−ln(1-p)/p − 1 = ∑_{m≥0} p^{m+1}/(m+2)`, the tail of the logarithm series. -/
theorem nonmarkov_series {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    -Real.log (1 - p) / p - 1 =
      ∑' m : ℕ, p ^ (m + 1) / ((m : ℝ) + 2) := by
  have habs : |p| < 1 := by
    rw [abs_of_pos hp]
    exact hp1
  let f : ℕ → ℝ := fun n => p ^ (n + 1) / (n + 1 : ℝ)
  have hf : Summable f := (hasSum_pow_div_log_of_abs_lt_one habs).summable
  have hfull : ∑' n, f n = -Real.log (1 - p) :=
    (hasSum_pow_div_log_of_abs_lt_one habs).tsum_eq
  have hsplit : ∑' n, f n = f 0 + ∑' m, f (m + 1) := hf.tsum_eq_zero_add
  have hf0 : f 0 = p := by simp [f]
  have htail : ∑' m, f (m + 1) = -Real.log (1 - p) - p := by
    rw [hsplit, hf0] at hfull
    linarith
  have hterm : ∀ m : ℕ, f (m + 1) = p * (p ^ (m + 1) / ((m : ℝ) + 2)) := by
    intro m
    simp only [f, pow_succ]
    have hden : ((m + 1 : ℕ) + 1 : ℝ) = (m : ℝ) + 2 := by
      push_cast
      ring
    rw [hden]
    ring
  have hfac : ∑' m, f (m + 1) = p * ∑' m : ℕ, p ^ (m + 1) / ((m : ℝ) + 2) := by
    rw [tsum_congr hterm, tsum_mul_left]
  have hne : p ≠ 0 := hp.ne'
  rw [hfac] at htail
  have : ∑' m : ℕ, p ^ (m + 1) / ((m : ℝ) + 2) = (-Real.log (1 - p) - p) / p := by
    field_simp [hne] at htail ⊢
    linarith
  rw [this, nonmarkov_closed hne]

theorem nonmarkov_leading {p : ℝ} (hp : |p| < 1) :
    HasSum (fun n : ℕ => p ^ (n + 1) / (n + 1 : ℝ)) (-Real.log (1 - p)) :=
  hasSum_pow_div_log_of_abs_lt_one hp

end
