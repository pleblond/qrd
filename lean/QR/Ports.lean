module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

/-!
# Bright/dark ports and geometric resolution time

Theorem 2.1 (`thm:story_bright_dark`): the record-port rotation, the resolution probability
`sin² θ`, and the mean resolution time `τ/p`.
-/

set_option linter.style.header false
set_option linter.unusedSimpArgs false

open Matrix Real

public section

/-- Active rotation of the bright/record plane. -/
noncomputable def recordRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem recordRotation_on_bright (θ φ : ℝ) :
    (recordRotation θ).mulVec ![φ, 0] = ![φ * Real.cos θ, φ * Real.sin θ] := by
  ext i
  fin_cases i <;>
    simp [recordRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Weight delivered to the record port is `C · sin² θ` when the bright amplitude squared is `C`
(`eq:record_prob`). -/
theorem record_weight (θ φ : ℝ) :
    ((recordRotation θ).mulVec ![φ, 0]) 1 ^ 2 = φ ^ 2 * Real.sin θ ^ 2 := by
  rw [recordRotation_on_bright]
  simp
  ring

theorem dark_decoupling (d : ℝ) :
    (!![-1] : Matrix (Fin 1) (Fin 1) ℝ).mulVec ![d] = ![-d] := by
  ext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one]

/-- `∑_{k≥0} (k+1) q^k = 1/(1-q)²` for `0 ≤ q < 1`. -/
theorem tsum_trials {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, ((k : ℝ) + 1) * q ^ k = 1 / (1 - q) ^ 2 := by
  have habs : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hmul : Summable (fun n : ℕ => (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one habs).summable
  have hgeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hsplit : ∑' n : ℕ, ((n : ℝ) + 1) * q ^ n =
      ∑' n : ℕ, ((n : ℝ) * q ^ n + q ^ n) := by
    refine tsum_congr fun n => ?_
    ring
  rw [hsplit, hmul.tsum_add hgeom, tsum_coe_mul_geometric_of_norm_lt_one habs,
    tsum_geometric_of_lt_one hq0 hq1]
  field_simp
  ring

/-- A loop of latency `τ` that resolves with probability `p` at each return has mean time `τ/p`. -/
theorem mean_resolution_time {p τ : ℝ} (hp : 0 < p) (hp1 : p < 1) (_hτ : 0 ≤ τ) :
    τ * p * ∑' k : ℕ, ((k : ℝ) + 1) * (1 - p) ^ k = τ / p := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  rw [tsum_trials hq0 hq1]
  field_simp
  ring

/-- Phase coherence of an amplitude vector, as a fraction of the bright weight. -/
noncomputable def phaseCoherence (J : Fin 2 → ℂ) : ℝ :=
  ‖J 0 + J 1‖ ^ 2 / (2 * (‖J 0‖ ^ 2 + ‖J 1‖ ^ 2))

theorem phase_two_port (J : Fin 2 → ℂ) (hC : ‖J 0‖ ^ 2 + ‖J 1‖ ^ 2 ≠ 0) :
    phaseCoherence J = ‖((Real.sqrt 2)⁻¹ : ℂ) * (J 0 + J 1)‖ ^ 2 /
      (‖J 0‖ ^ 2 + ‖J 1‖ ^ 2) := by
  unfold phaseCoherence
  rw [norm_mul]
  have hnorm : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
    rw [show ((Real.sqrt 2)⁻¹ : ℂ) = (Real.sqrt 2 : ℂ)⁻¹ by simp, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hnorm]
  field_simp [hC]
  rw [Real.sq_sqrt (by norm_num)]

end
