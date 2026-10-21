module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic

/-!
# Helium variational integral and the specific-mass-shift stage

The normalized `m_D = 0` density in the manuscript is `ρ_ζ = (ζ³/2) r² e^{-ζ r}`.
In the coordinate `x = ζ r` this is `(1/2) x² e^{-x} dx`, which integrates to `1`.
The electron-electron bracket printed in Lemma `lem:helium_vee_feshbach` is
`(1/2)(1) - (1/2)(1/4) - (1/4)(2/8) = 5/16`, so `V_ee = (5/16) g ζ` and
`E = -2 (Z - 5/16)²`. The screening constant in that expansion is
`2 (5/16)² = 25/128`. At `Z = 3` the same stationarity condition is `ζ = (43/16) g`.

The evaluated Kronecker sum `ΔE_corr = -0.11974 Ry`, the partial-wave decimals, and the
isoelectronic percentages are not theorems. The normal mass shift is the Coulomb virial
`⟨p₁² + p₂²⟩ = -2 m_e E`. For the specific mass shift, the manuscript's radial identities
`R₀' = -R₀/2` and `x u₀ = √3 f₀⁽¹⁾` are proved for
`R₀(x) = e^{-x/2}/√2`, `u₀(x) = x R₀(x)`, and
`f₀⁽¹⁾(x) = x² e^{-x/2}/√6` (the `j = 0` case of Appendix F).
Sturmian orthogonality in the weight `dx/x` then forces the `L²` overlap with `u₀` to be
`√3` times that weight, so a function orthogonal to `f₀⁽¹⁾` has overlap `0` with `u₀`.
The `j = 0` weight itself is `1`, and the overlap is `√3`.

The manuscript's gradient coefficient `-√3/4` is the `L = 0` contraction of `R₀' = -R₀/2`
with this overlap. The Condon–Shortley coupling gives the opposite sign `+√3/4`; the two
differ by the phase of the coupled `p`-wave. Appendix H writes
`c⁽¹⁾ = -2 ℒ₁⁻¹ v⁽¹⁾`, while Section 7 writes `c = -ℒ₁⁻¹ v`. The verifier solves
`ℒ sol = 2 v` and sets `c = -sol`, which is the appendix factor. Neither resolvent
coefficient is a theorem: `v` is the numerical fluctuation vector.
-/

set_option linter.style.header false

open MeasureTheory Set Real

public section

theorem integral_x_exp :
    ∫ x in Ioi (0 : ℝ), x ^ (1 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) = 1 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

theorem integral_x_exp_two :
    ∫ x in Ioi (0 : ℝ), x ^ (1 : ℝ) * exp (-(2 : ℝ) * x ^ (1 : ℝ)) = 1 / 4 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

theorem integral_x2_exp_two :
    ∫ x in Ioi (0 : ℝ), x ^ (2 : ℝ) * exp (-(2 : ℝ) * x ^ (1 : ℝ)) = 1 / 4 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

/-- `⟨1/x₁₂⟩ = 1/2 ∫ x e^{-x} - 1/2 ∫ x e^{-2x} - 1/4 ∫ x² e^{-2x} = 5/16`. -/
theorem vee_expectation :
    (1 / 2 : ℝ) * (∫ x in Ioi 0, x ^ (1 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ))) -
      (1 / 2) * (∫ x in Ioi 0, x ^ (1 : ℝ) * exp (-(2 : ℝ) * x ^ (1 : ℝ))) -
      (1 / 4) * (∫ x in Ioi 0, x ^ (2 : ℝ) * exp (-(2 : ℝ) * x ^ (1 : ℝ))) = 5 / 16 := by
  rw [integral_x_exp, integral_x_exp_two, integral_x2_exp_two]
  norm_num

noncomputable def heliumEnergy (g Z ζ : ℝ) : ℝ := ζ ^ 2 / 2 - g * (Z - 5 / 16) * ζ

theorem helium_stationary {g Z : ℝ} :
    heliumEnergy g Z (g * (Z - 5 / 16)) = -(g ^ 2) * (Z - 5 / 16) ^ 2 / 2 := by
  unfold heliumEnergy
  ring

theorem helium_g2 (Z : ℝ) :
    heliumEnergy 2 Z (2 * (Z - 5 / 16)) = -2 * (Z - 5 / 16) ^ 2 := by
  unfold heliumEnergy
  ring

theorem helium_Z2 : heliumEnergy 2 2 (2 * (2 - 5 / 16)) = -(729 : ℝ) / 128 := by
  unfold heliumEnergy
  norm_num

/-- Dimensionless density `ρ dx = (1/2) x² e^{-x} dx` integrates to `1`. -/
theorem integral_x2_exp :
    ∫ x in Ioi (0 : ℝ), x ^ (2 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) = 2 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 2) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

theorem helium_density_integral :
    (1 / 2 : ℝ) * (∫ x in Ioi 0, x ^ (2 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ))) = 1 := by
  rw [integral_x2_exp]
  norm_num

/-- The printed grouping `(1/4)·(2/8)` uses `2/8 = ∫ x² e^{-2x} dx`. -/
theorem integral_x2_exp_two_printed :
    ∫ x in Ioi (0 : ℝ), x ^ (2 : ℝ) * exp (-(2 : ℝ) * x ^ (1 : ℝ)) = 2 / 8 := by
  rw [integral_x2_exp_two]
  norm_num

theorem vee_printed_bracket :
    (1 / 2 : ℝ) * 1 - (1 / 2) * (1 / 4) - (1 / 4) * (2 / 8) = 5 / 16 := by
  norm_num

/-- The `1/Z` screening constant subtracted in the `ℓ' = 0` comparison is `25/128`. -/
theorem rs_screening_constant : (2 : ℝ) * (5 / 16) ^ 2 = 25 / 128 := by
  norm_num

theorem helium_energy_expansion (Z : ℝ) :
    -2 * (Z - 5 / 16) ^ 2 = -2 * Z ^ 2 + (5 / 4) * Z - 25 / 128 := by
  ring

/-- Lithium's inner pair sits at `ζ = (43/16) g`. -/
theorem lithium_inner_zeta (g : ℝ) : g * ((3 : ℝ) - 5 / 16) = (43 / 16) * g := by
  ring

/-- Coulomb virial `2⟨T⟩ + ⟨V⟩ = 0` with `E = ⟨T⟩ + ⟨V⟩` gives `⟨p²⟩ = 2 m ⟨T⟩ = -2 m E`. -/
theorem nms_from_virial {T V E m : ℝ} (hvir : 2 * T + V = 0) (hE : E = T + V) :
    2 * m * T = -2 * m * E := by
  have hV : V = -2 * T := by linarith
  have hT : T = -E := by
    rw [hV] at hE
    linarith
  rw [hT]
  ring

/-! ## Specific mass shift, single radial stage -/

/-- Dimensionless `1s` radial function `R₀(x) = e^{-x/2}/√2`. -/
noncomputable def radialS (x : ℝ) : ℝ := exp (-x / 2) / sqrt 2

/-- Reduced radial `u₀(x) = x R₀(x)`. -/
noncomputable def reducedS (x : ℝ) : ℝ := x * radialS x

/-- Terminal `ℓ' = 1` Sturmian `f₀⁽¹⁾(x) = x² e^{-x/2}/√6`. -/
noncomputable def radialP (x : ℝ) : ℝ := x ^ 2 * exp (-x / 2) / sqrt 6

theorem radialS_deriv (x : ℝ) : HasDerivAt radialS (-radialS x / 2) x := by
  unfold radialS
  have hlin := ((hasDerivAt_id x).div_const (2 : ℝ)).neg
  have hdiv := hlin.exp.div_const (sqrt 2)
  convert hdiv using 1
  · ext t
    simp [Pi.neg_apply]
    ring
  · simp [Pi.neg_apply]
    ring_nf

theorem radial_bridge (x : ℝ) : x * reducedS x = sqrt 3 * radialP x := by
  unfold reducedS radialS radialP
  have hsqrt : sqrt 3 / sqrt 6 = 1 / sqrt 2 := by
    rw [div_eq_div_iff (sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 6))
      (sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))]
    rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  calc
    x * (x * (exp (-x / 2) / sqrt 2)) = x ^ 2 * exp (-x / 2) / sqrt 2 := by ring
    _ = x ^ 2 * exp (-x / 2) * (sqrt 3 / sqrt 6) := by
      rw [hsqrt]
      ring
    _ = sqrt 3 * (x ^ 2 * exp (-x / 2) / sqrt 6) := by ring

theorem integral_x3_exp :
    ∫ x in Ioi (0 : ℝ), x ^ (3 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) = 6 := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 3) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

theorem radialP_sturmian_norm :
    ∫ x in Ioi (0 : ℝ), radialP x ^ 2 / x = 1 := by
  have hcongr :
      ∫ x in Ioi (0 : ℝ), radialP x ^ 2 / x =
        (1 / 6) * ∫ x in Ioi (0 : ℝ),
          x ^ (3 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    dsimp
    unfold radialP
    have hx0 : x ≠ 0 := ne_of_gt hx
    rw [rpow_one x]
    have hexp : exp (-x / 2) ^ 2 = exp (-x) := by
      rw [pow_two, ← exp_add]
      congr 1
      ring
    have hsq : sqrt 6 ^ 2 = 6 := sq_sqrt (by norm_num)
    have hexp' : exp (-x) = exp (-1 * x) := by
      congr 1
      ring
    rw [show (x ^ 2 * exp (-x / 2) / sqrt 6) ^ 2 / x =
        x ^ 4 * (exp (-x / 2) ^ 2) / ((sqrt 6) ^ 2 * x) by ring, hexp, hsq, hexp']
    rw [rpow_ofNat x 3]
    field_simp [hx0]
  rw [hcongr, integral_x3_exp]
  norm_num

theorem sms_ground_overlap :
    ∫ x in Ioi (0 : ℝ), radialP x * reducedS x = sqrt 3 := by
  have hcongr :
      ∫ x in Ioi (0 : ℝ), radialP x * reducedS x =
        (1 / sqrt 12) *
          ∫ x in Ioi (0 : ℝ), x ^ (3 : ℝ) * exp (-(1 : ℝ) * x ^ (1 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    dsimp
    unfold radialP reducedS radialS
    rw [rpow_one x]
    have hexp : exp (-x / 2) * exp (-x / 2) = exp (-x) := by
      rw [← exp_add]
      congr 1
      ring
    have hsqrt : sqrt 6 * sqrt 2 = sqrt 12 := by
      rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    have hexp' : exp (-x) = exp (-1 * x) := by
      congr 1
      ring
    rw [show (x ^ 2 * exp (-x / 2) / sqrt 6) * (x * (exp (-x / 2) / sqrt 2)) =
        x ^ 3 * (exp (-x / 2) * exp (-x / 2)) / (sqrt 6 * sqrt 2) by ring,
      hexp, hsqrt, hexp', rpow_ofNat x 3, div_eq_mul_inv]
    ring
  rw [hcongr, integral_x3_exp]
  have hsq : sqrt 12 * sqrt 3 = 6 := by
    rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    norm_num
  have h12 : sqrt 12 ≠ 0 := sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 12)
  field_simp [h12]
  exact hsq.symm

/-- Orthogonality to `f₀⁽¹⁾` in the weight `dx/x` scales the overlap with `u₀` by `√3`. -/
theorem sms_overlap_from_orthogonality {g : ℝ → ℝ}
    (hg : IntegrableOn (fun x => g x * radialP x / x) (Ioi (0 : ℝ))) :
    ∫ x in Ioi (0 : ℝ), g x * reducedS x =
      sqrt 3 * ∫ x in Ioi (0 : ℝ), g x * radialP x / x := by
  have heq : EqOn (fun x => g x * reducedS x)
      (fun x => sqrt 3 * (g x * radialP x / x)) (Ioi 0) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hred : reducedS x = sqrt 3 * radialP x / x := by
      rw [eq_div_iff hx0]
      simpa [mul_comm] using radial_bridge x
    dsimp
    rw [hred]
    ring
  have _hleft : IntegrableOn (fun x => g x * reducedS x) (Ioi 0) := by
    have hright : IntegrableOn (fun x => sqrt 3 * (g x * radialP x / x)) (Ioi 0) := by
      unfold IntegrableOn at hg ⊢
      refine Integrable.congr (hg.smul (sqrt 3)) (ae_of_all _ ?_)
      intro x
      simp [Pi.smul_apply, smul_eq_mul]
    exact hright.congr_fun heq.symm measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul]

end
