module

public import Mathlib.Tactic

/-!
# Spherical stencil weights

Proposition 5.2 (`prop:840_stencil`, `eq:840_weights`): the degree-5 Lebedev weights on the
14-direction stencil and the degree-7 weights on the 26-direction stencil.
-/

set_option linter.style.header false

public section

/-- The two moment equations `8 w_L + 6 w_F = 1` and `8 w_L / 9 = 1/15` have the unique
solution `(w_L, w_F) = (3/40, 1/15) = (9/120, 8/120)`. -/
theorem lebedev120_unique (wL wF : ℚ)
    (hsum : 8 * wL + 6 * wF = 1) (h4 : 8 * wL / 9 = 1 / 15) :
    wL = 3 / 40 ∧ wF = 1 / 15 := by
  have hwL : wL = 3 / 40 := by
    have h9 : (9 : ℚ) ≠ 0 := by norm_num
    have : 8 * wL = 9 / 15 := by
      field_simp [h9] at h4
      linarith
    linarith
  refine ⟨hwL, ?_⟩
  have : 6 * wF = 1 - 8 * (3 / 40) := by linarith
  linarith

theorem lebedev120_weights : (3 / 40 : ℚ) = 9 / 120 ∧ (1 / 15 : ℚ) = 8 / 120 := by
  constructor <;> norm_num

theorem port_count_120 : 8 * 9 + 6 * 8 = 120 := by norm_num

/-- The redundant fourth-moment equation is a consequence of the two solved equations. -/
theorem lebedev120_fourth (wL wF : ℚ) (hL : wL = 3 / 40) (hF : wF = 1 / 15) :
    8 * wL / 9 + 2 * wF = 1 / 5 := by
  rw [hL, hF]
  norm_num

/-- Clearing denominators, the degree-7 isotropy conditions are the linear system solved below.
`wF`, `wL`, `wE` are the film, line, and edge-difference weights. -/
theorem lebedev840_unique (wF wL wE : ℚ)
    (h0 : 6 * wF + 8 * wL + 12 * wE = 1)
    (h4 : 2 * wF + (8 / 9) * wL + 2 * wE = 1 / 5)
    (h6 : 2 * wF + (8 / 27) * wL + wE = 1 / 7) :
    wF = 1 / 21 ∧ wL = 9 / 280 ∧ wE = 4 / 105 := by
  have hF : -2 * wF + (8 / 27) * wL = -3 / 35 := by
    linear_combination h4 - 2 * h6
  have hG : -18 * wF + (40 / 9) * wL = -5 / 7 := by
    linear_combination h0 - 12 * h6
  have hL : (16 / 9) * wL = 2 / 35 := by
    linear_combination hG - 9 * hF
  have hwL : wL = 9 / 280 := by
    field_simp at hL
    linarith
  have hwF : wF = 1 / 21 := by
    have : -2 * wF = -3 / 35 - (8 / 27) * (9 / 280) := by
      linear_combination hF - (8 / 27) * hwL
    linarith
  have hwE : wE = 4 / 105 := by
    linear_combination h6 - 2 * hwF - (8 / 27) * hwL
  exact ⟨hwF, hwL, hwE⟩

theorem lebedev840_reduced :
    (1 / 21 : ℚ) = 40 / 840 ∧ (9 / 280 : ℚ) = 27 / 840 ∧ (4 / 105 : ℚ) = 32 / 840 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

theorem port_count_840 : 6 * 40 + 8 * 27 + 12 * 32 = 840 := by norm_num

/-- The cross moment `∑ w u_x^4 u_y^2 = 1/35` holds at the same weights. -/
theorem lebedev840_cross :
    8 * ((9 : ℚ) / 280) / 27 + (4 / 105) / 2 = 1 / 35 := by
  norm_num

/-- The triple moment `∑ w u_x² u_y² u_z² = 1/105` is carried by the eight line vertices. -/
theorem lebedev840_triple : 8 * ((9 : ℚ) / 280) / 27 = 1 / 105 := by
  norm_num

end
