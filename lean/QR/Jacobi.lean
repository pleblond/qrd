module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-!
# Discrete Jacobi pencil, Rydberg closure, and isotope shift

Algebraic content of Theorems 6.1 and 6.4 (`thm:discrete_graph_to_jacobi`, `thm:rydberg_closure`),
the reduced-mass isotope identity (`thm:reduced_mass_recoil`), the positive-energy obstruction
(`thm:no_free_electron`), and the boxed Sommerfeld formula (`thm:sommerfeld_dirac`).

Zero leakage in the repaired appendix pair,
`ζ = 2 √(m² c⁴ - E²) / (ℏ c)` and `(ζ/2) ν = Zα E / (ℏ c)`, solves to the boxed spectrum.
The theorem `sommerfeld_algebraic` is that boxed identity.
-/

set_option linter.style.header false

open Real

public section

/-- Bridge count `N_j = r_j (j + 2ℓ + 1) = r_{j+1} (j + 1)`. -/
theorem bridge_count (j ℓ : ℕ) :
    Nat.choose (j + 2 * ℓ) (2 * ℓ) * (j + 2 * ℓ + 1) =
      Nat.choose (j + 2 * ℓ + 1) (2 * ℓ) * (j + 1) := by
  have h := Nat.choose_mul_succ_eq (j + 2 * ℓ) (2 * ℓ)
  have hsub : j + 2 * ℓ + 1 - 2 * ℓ = j + 1 := by omega
  rwa [hsub] at h

/-- Column `j` of the effective bridge matrix has squared norm `d_j = 2j + 2ℓ + 2`. -/
theorem jacobi_diagonal (ℓ j : ℕ) :
    ((j + 2 * ℓ + 1 : ℝ) + ((j + 1 : ℝ))) = (2 * j + 2 * ℓ + 2 : ℝ) := by
  ring

theorem jacobi_diagonal_sqrt (ℓ j : ℕ) :
    Real.sqrt (j + 2 * ℓ + 1) ^ 2 + Real.sqrt (j + 1) ^ 2 =
      (2 * j + 2 * ℓ + 2 : ℝ) := by
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

/-- Off-diagonal overlap of columns `j` and `j+1` is `b_{j+1}`. -/
theorem jacobi_offdiag (ℓ j : ℕ) :
    Real.sqrt (j + 1) * Real.sqrt (j + 1 + 2 * ℓ + 1) =
      Real.sqrt ((j + 1) * (j + 2 * ℓ + 2)) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  ring

/-- Zero exterior leakage kills the coefficient of `K₁` if and only if `ε = -ζ²/4`. -/
theorem zero_leakage_iff {ζ ε b : ℝ} (hb : b ≠ 0) :
    -((ζ ^ 2 / 2) + 2 * ε) * (b / 2) = 0 ↔ ε = -(ζ ^ 2) / 4 := by
  constructor
  · intro h
    have hcoef : (ζ ^ 2 / 2) + 2 * ε = 0 := by
      have hb' : b / 2 ≠ 0 := by
        intro hzero
        apply hb
        linarith
      rcases mul_eq_zero.mp h with hneg | hb0
      · exact neg_eq_zero.mp hneg
      · exact absurd hb0 hb'
    linarith
  · intro h
    rw [h]
    ring

/-- On the terminal stage `K₀ = n`, the diagonal secular equation selects `ζ = 0` or `ζ = g/n`. -/
theorem terminal_scale {ζ g n : ℝ} (hn : n ≠ 0) :
    ζ ^ 2 * n - ζ * g = 0 ↔ ζ = 0 ∨ ζ = g / n := by
  constructor
  · intro h
    have : ζ * (ζ * n - g) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with hz | hrest
    · exact Or.inl hz
    · right
      have hprod : ζ * n = g := by linarith
      exact (eq_div_iff hn).2 hprod
  · intro h
    rcases h with rfl | h
    · ring
    · rw [h]
      field_simp [hn]
      ring

theorem rydberg_energy {g n : ℝ} (hn : n ≠ 0) :
    -((g / n) ^ 2) / 4 = -(g ^ 2) / (4 * n ^ 2) := by
  field_simp [hn]

theorem rydberg_latency {g n : ℝ} (hg : g ≠ 0) (hn : n ≠ 0) :
    (1 : ℝ) / (g / n) = n / g := by
  field_simp [hg, hn]

/-- Single-stage energy `E(τ) = 1/(4τ²) - g/(2 n τ)` (`eq:atomic_pressure_balance`). -/
noncomputable def shellEnergy (g n τ : ℝ) : ℝ := 1 / (4 * τ ^ 2) - g / (2 * n * τ)

/-- The displayed radial pressure `1/(2τ³) - g/(2nτ²)` vanishes exactly at `τ = n/g`. -/
theorem pressure_zero_at_rydberg {g n τ : ℝ} (hn : n ≠ 0) (hτ : τ ≠ 0) (hg : g ≠ 0) :
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

theorem energy_at_rydberg {g n : ℝ} (hn : n ≠ 0) (hg : g ≠ 0) :
    shellEnergy g n (n / g) = -(g ^ 2) / (4 * n ^ 2) := by
  unfold shellEnergy
  field_simp [hn, hg]
  ring

/-- Virial data on the normalized terminal state: `⟨T⟩ = g²/(4n²)`, `⟨V⟩ = -g²/(2n²)`. -/
theorem discrete_virial {g n : ℝ} (hn : n ≠ 0) :
    2 * (g ^ 2 / (4 * n ^ 2)) + (-(g ^ 2) / (2 * n ^ 2)) = 0 := by
  field_simp [hn]
  ring

theorem kinetic_from_matrix {ζ g n : ℝ} (hn : n ≠ 0) (hζ : ζ = g / n) :
    (1 / (2 * n)) * ((ζ ^ 2 / 2) * n) = g ^ 2 / (4 * n ^ 2) := by
  rw [hζ]
  field_simp [hn]
  ring

theorem potential_from_matrix {ζ g n : ℝ} (hn : n ≠ 0) (hζ : ζ = g / n) :
    (1 / (2 * n)) * (-(ζ * g)) = -(g ^ 2) / (2 * n ^ 2) := by
  rw [hζ]
  field_simp [hn]

/-! ## No isolated positive-energy electron -/

/-- With `a = ζ²/2 - 2ε` and `b = -(ζ²/2 + 2ε)`, the Casimir is `-4 ζ² ε`,
as written from `eq:secular_D`. -/
theorem secular_casimir (ζ ε : ℝ) :
    let a := ζ ^ 2 / 2 - 2 * ε
    let b := -(ζ ^ 2 / 2 + 2 * ε)
    a ^ 2 - b ^ 2 = -4 * ζ ^ 2 * ε := by
  intro a b
  ring

theorem no_positive_leakage {ζ ε : ℝ} (hε : 0 < ε) (hζ : ζ ≠ 0) :
    |ζ ^ 2 / 2 - 2 * ε| < ζ ^ 2 / 2 + 2 * ε := by
  have hζsq : 0 < ζ ^ 2 := sq_pos_of_ne_zero hζ
  have hpos : 0 < ζ ^ 2 / 2 + 2 * ε := by positivity
  have hdiff : (ζ ^ 2 / 2 + 2 * ε) ^ 2 - (ζ ^ 2 / 2 - 2 * ε) ^ 2 = 4 * ζ ^ 2 * ε := by ring
  have hlt : (ζ ^ 2 / 2 - 2 * ε) ^ 2 < (ζ ^ 2 / 2 + 2 * ε) ^ 2 := by
    have : 0 < 4 * ζ ^ 2 * ε := by positivity
    linarith
  have hsq : |ζ ^ 2 / 2 - 2 * ε| < |ζ ^ 2 / 2 + 2 * ε| :=
    (sq_lt_sq).mp hlt
  rwa [abs_of_pos hpos] at hsq

theorem positive_energy_blocks_K1 {ζ ε : ℝ} (hε : 0 < ε) :
    ζ ^ 2 / 2 + 2 * ε ≠ 0 := by
  have : 0 < ζ ^ 2 / 2 + 2 * ε := by positivity
  exact ne_of_gt this

/-! ## Sommerfeld boxed formula -/

/-- The boxed spectrum equals `m c² · ν / √(ν² + (Zα)²)` for `ν > 0`. -/
theorem sommerfeld_algebraic {m c ν zα : ℝ} (hν : 0 < ν) :
    m * c ^ 2 * (1 + zα ^ 2 / ν ^ 2) ^ (-(1 / 2 : ℝ)) =
      m * c ^ 2 * ν / Real.sqrt (ν ^ 2 + zα ^ 2) := by
  have hνne : ν ≠ 0 := hν.ne'
  have h1 : 1 + zα ^ 2 / ν ^ 2 = (ν ^ 2 + zα ^ 2) / ν ^ 2 := by
    field_simp [hνne]
  rw [h1]
  have hpos : 0 ≤ (ν ^ 2 + zα ^ 2) / ν ^ 2 := by positivity
  rw [Real.rpow_neg hpos]
  have hdiv : ((ν ^ 2 + zα ^ 2) / ν ^ 2) ^ (1 / 2 : ℝ) =
      (ν ^ 2 + zα ^ 2) ^ (1 / 2 : ℝ) / (ν ^ 2) ^ (1 / 2 : ℝ) :=
    Real.div_rpow (by positivity) (by positivity) (1 / 2)
  rw [hdiv]
  have hνpow : (ν ^ 2) ^ (1 / 2 : ℝ) = ν := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hν.le]
  rw [hνpow, ← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < ν ^ 2 + zα ^ 2)]

/-- Zero leakage `ζ = 2 √(m²c⁴ - E²)/(ℏ c)` and `(ζ/2) ν = Zα E/(ℏ c)`
solve to the boxed Dirac energy. -/
theorem sommerfeld_from_zero_leakage {m c ℏ E ν zα : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hℏ : ℏ ≠ 0) (hE : 0 < E) (hν : 0 < ν) (hbound : E ^ 2 ≤ m ^ 2 * c ^ 4)
    (hleak :
      ((2 / (ℏ * c) * Real.sqrt (m ^ 2 * c ^ 4 - E ^ 2)) / 2) * ν =
        zα * E / (ℏ * c)) :
    E = m * c ^ 2 * (1 + zα ^ 2 / ν ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hℏc : ℏ * c ≠ 0 := mul_ne_zero hℏ hc.ne'
  have hsqrt : Real.sqrt (m ^ 2 * c ^ 4 - E ^ 2) * ν = zα * E := by
    have hhalf :
        (2 / (ℏ * c) * Real.sqrt (m ^ 2 * c ^ 4 - E ^ 2)) / 2 =
          Real.sqrt (m ^ 2 * c ^ 4 - E ^ 2) / (ℏ * c) := by
      field_simp [hℏc]
    rw [hhalf] at hleak
    field_simp [hℏc] at hleak
    linarith
  have hnn : 0 ≤ m ^ 2 * c ^ 4 - E ^ 2 := by linarith
  have hsq : (m ^ 2 * c ^ 4 - E ^ 2) * ν ^ 2 = (zα * E) ^ 2 := by
    have hmul := congrArg (fun t : ℝ => t ^ 2) hsqrt
    rwa [mul_pow, Real.sq_sqrt hnn] at hmul
  have hEsq : E ^ 2 * (ν ^ 2 + zα ^ 2) = m ^ 2 * c ^ 4 * ν ^ 2 := by
    nlinarith [hsq]
  have hpos : 0 < ν ^ 2 + zα ^ 2 := by positivity
  have hdiv : E ^ 2 = m ^ 2 * c ^ 4 * ν ^ 2 / (ν ^ 2 + zα ^ 2) := by
    field_simp [hpos.ne']
    linarith
  have hroot : E = Real.sqrt (m ^ 2 * c ^ 4 * ν ^ 2 / (ν ^ 2 + zα ^ 2)) := by
    rw [← Real.sqrt_sq hE.le]
    exact congrArg Real.sqrt hdiv
  have hnum : Real.sqrt (m ^ 2 * c ^ 4 * ν ^ 2) = m * c ^ 2 * ν := by
    have hm0 : 0 ≤ m ^ 2 := sq_nonneg m
    rw [Real.sqrt_mul (mul_nonneg hm0 (by positivity)), Real.sqrt_mul hm0,
      Real.sqrt_sq hm.le, Real.sqrt_sq hν.le]
    have hc2 : Real.sqrt (c ^ 4) = c ^ 2 := by
      rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg c)]
    rw [hc2]
  rw [hroot, Real.sqrt_div (mul_nonneg (mul_nonneg (sq_nonneg m) (by positivity)) (sq_nonneg ν)),
    hnum]
  symm
  exact sommerfeld_algebraic hν

/-- Binding relative to rest energy, rationalized: `1 - (1+x)^{-1/2} = x / (√(1+x) (√(1+x)+1))`. -/
theorem rydberg_rationalization {x : ℝ} (hx : 0 ≤ x) :
    1 - (1 + x) ^ (-(1 / 2 : ℝ)) =
      x / (Real.sqrt (1 + x) * (Real.sqrt (1 + x) + 1)) := by
  have hpos : 0 < 1 + x := by linarith
  rw [Real.rpow_neg (le_of_lt hpos), Real.sqrt_eq_rpow]
  have hne : (1 + x) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hpos _).ne'
  have hne2 : (1 + x) ^ (1 / 2 : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hne, hne2]
  have : ((1 + x) ^ (1 / 2 : ℝ)) ^ 2 = 1 + x := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hpos)]
    norm_num
  nlinarith [this]

/-- The `2P` fine-structure gap at `n = 2`, `g = 2` is `α²/16` Rydberg.
`ΔE = -(α² g²)/(4 n⁴) (n/(j+1/2) - 3/4)`. -/
def fineStructure (α g n j : ℚ) : ℚ :=
  -(α ^ 2 * g ^ 2) / (4 * n ^ 4) * (n / (j + 1 / 2) - 3 / 4)

theorem fine_structure_2p (α : ℚ) :
    fineStructure α 2 2 (3 / 2) - fineStructure α 2 2 (1 / 2) = α ^ 2 / 16 := by
  unfold fineStructure
  ring

/-- `W_{n0} = g³/(2n³)`. The Bethe logarithm stays outside the proof kernel. -/
noncomputable def lambShift (g n : ℝ) : ℝ := (g / n) ^ 3 / 2

theorem lamb_shift_power {g n : ℝ} (hn : n ≠ 0) :
    lambShift g n = g ^ 3 / (2 * n ^ 3) := by
  unfold lambShift
  field_simp [hn]

/-- `L_n / L_2 = (2/n)³` (`eq:lamb_ratio_law`). -/
theorem lamb_ratio {g n : ℝ} (hn : n ≠ 0) (hg : g ≠ 0) :
    lambShift g n / lambShift g 2 = (2 / n) ^ 3 := by
  unfold lambShift
  field_simp [hn, hg]

/-- Same-shell Stark product `3√3 · 1/√3 = 3`. -/
theorem stark_n2 : (3 : ℝ) * Real.sqrt 3 * (Real.sqrt 3)⁻¹ = 3 := by
  rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

/-- The squeeze generator coefficient in `eq:su11_squeeze` is `θ = log(n_i/n_f)`. -/
theorem dilation_log {ni nf : ℝ} (hi : 0 < ni) (hf : 0 < nf) :
    -((1 / 2) * Real.log (ni / nf)) = (1 / 2) * Real.log (nf / ni) := by
  rw [Real.log_div hi.ne' hf.ne', Real.log_div hf.ne' hi.ne']
  ring

end
