module

public import Mathlib.Tactic

/-!
# Relational First Law

Algebraic content of `eq:relational_first_law` and `eq:atomic_pressure_balance`: the bright/dark
split, the latency pressure `E/τ`, the three-dimensional radiation pressure `E/(3V)` when
`V ∝ τ³`, and the vanishing of atomic pressure at `τ = n/g`.
-/

set_option linter.style.header false

public section

theorem bright_dark_split (Q p : ℝ) :
    p * Q + (1 - p) * Q = Q := by
  ring

/-- At fixed story weight, `P_τ = E/τ` when `E = ℏ Ω₀ (τ₀/τ) Q`. -/
theorem latency_pressure {hbar ω0 τ0 Q τ : ℝ} (hτ : τ ≠ 0) :
    hbar * ω0 * (τ0 / τ ^ 2) * Q = (hbar * ω0 * (τ0 / τ) * Q) / τ := by
  field_simp [hτ]

/-- If `V = c τ³` and `dV = 3 V dτ / τ`, then `P_τ dτ = P_{3D} dV` with `P_{3D} = E/(3V)`. -/
theorem radiation_pressure {E V c τ dτ dV : ℝ} (hV : V = c * τ ^ 3) (hτ : τ ≠ 0) (hc : c ≠ 0)
    (hdV : dV = 3 * V * dτ / τ) :
    E / τ * dτ = (E / (3 * V)) * dV := by
  have hVne : V ≠ 0 := by
    rw [hV]
    exact mul_ne_zero hc (pow_ne_zero 3 hτ)
  rw [hdV]
  field_simp [hτ, hVne]

theorem atomic_pressure_root {g n τ : ℝ} (hn : n ≠ 0) (hτ : τ ≠ 0) (hg : g ≠ 0) :
    (1 / (2 * τ ^ 3) - g / (2 * n * τ ^ 2) = 0) ↔ τ = n / g := by
  constructor
  · intro h
    have hprod : n = τ * g := by
      field_simp [hτ, hn] at h
      ring_nf at h
      linarith
    exact (eq_div_iff hg).2 hprod.symm
  · intro h
    rw [h]
    field_simp [hn, hg]
    ring

end
