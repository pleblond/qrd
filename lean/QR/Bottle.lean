module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic

/-!
# Magnetic bottle, algebraic core

The canonical identity `A† A = p² + s² q² - ℏ s`, the Cauchy--Schwarz / AM--GM floor
(`eq:RS_s`), the moment comparison used by the spectral window, the constants
`ν ≥ ℏ²/(64 μ H*)`, and the vanishing second difference of the affine coefficient in
Proposition B.1.

The vacuum-subtracted drift inequality `c ≤ E + b √E`, with `b = √(ℏΩ/2)` and
`c = ℏ|α|⟨|s|⟩ / (4 √(2μM))`, inverts to `(ℏΩ/8) (√(1 + 2λ) - 1)²`, where
`λ = |α|⟨|s|⟩ / (Ω √(2μM))`. That is the boxed pinch cost, and its strong-pinch
slope is `ℏ|α| / (4 √(2μM))`. Replacing `2λ` by `λ` still lower-bounds the drift
and is strictly weaker for `λ > 0`.
-/

set_option linter.style.header false

open Real

public section

/-- In a commutative ring the cross terms cancel and no `ℏ` remainder appears. -/
theorem oscillator_commutative {S : Type*} [CommRing S] (q p s : S) :
    (p + s * q) * (p - s * q) = p * p - s * s * q * q := by
  ring

variable {R : Type*} [Ring R]

theorem commutator_cross (q p j s ℏ : R) (hcomm : q * p - p * q = j * ℏ) :
    j * s * (q * p) - j * s * (p * q) = j * s * (j * ℏ) := by
  calc
    j * s * (q * p) - j * s * (p * q) = j * s * (q * p - p * q) := by noncomm_ring
    _ = j * s * (j * ℏ) := by rw [hcomm]

theorem central_square (j s q : R) (hjq : j * q = q * j) (hsq : s * q = q * s)
    (hjs : j * s = s * j) (hjj : j * j = -1) :
    (j * s * q) * (j * s * q) = - (s * s * q * q) := by
  calc
    (j * s * q) * (j * s * q) = j * s * (q * j) * s * q := by noncomm_ring
    _ = j * s * (j * q) * s * q := by rw [hjq]
    _ = j * (s * j) * q * s * q := by noncomm_ring
    _ = j * (j * s) * q * s * q := by rw [hjs]
    _ = j * j * s * (q * s) * q := by noncomm_ring
    _ = j * j * s * (s * q) * q := by rw [hsq]
    _ = (j * j) * (s * s) * (q * q) := by noncomm_ring
    _ = - (s * s * q * q) := by rw [hjj]; noncomm_ring

/-- `A† A = p² + s² q² - ℏ s` when `[q, p] = j ℏ`, `j² = -1`, and `j, s, ℏ` commute
with the factors they pass (`eq:oscillator_ladder_square`). -/
theorem oscillator_identity (q p j s ℏ : R)
    (hcomm : q * p - p * q = j * ℏ) (hjj : j * j = -1)
    (hjq : j * q = q * j) (hjp : j * p = p * j)
    (hsq : s * q = q * s) (hsp : s * p = p * s) (hjs : j * s = s * j)
    (hℏs : ℏ * s = s * ℏ) :
    (p + j * s * q) * (p - j * s * q) = p * p + s * s * q * q - ℏ * s := by
  have hsquare : (j * s * q) * (j * s * q) = -(s * s * q * q) :=
    central_square j s q hjq hsq hjs hjj
  have hcross : j * s * (q * p) - j * s * (p * q) = j * s * (j * ℏ) :=
    commutator_cross q p j s ℏ hcomm
  have hpass : j * p * s = j * s * p := by
    calc
      j * p * s = j * (p * s) := by noncomm_ring
      _ = j * (s * p) := by rw [hsp]
      _ = j * s * p := by noncomm_ring
  have hup : (j * s * q) * p - p * (j * s * q) = j * s * (j * ℏ) := by
    calc
      (j * s * q) * p - p * (j * s * q) = j * s * (q * p) - p * j * s * q := by noncomm_ring
      _ = j * s * (q * p) - j * p * s * q := by rw [hjp]
      _ = j * s * (q * p) - j * s * p * q := by rw [hpass]
      _ = j * s * (q * p) - j * s * (p * q) := by noncomm_ring
      _ = j * s * (j * ℏ) := hcross
  have hcorr : j * s * (j * ℏ) = -(ℏ * s) := by
    calc
      j * s * (j * ℏ) = j * (s * j) * ℏ := by noncomm_ring
      _ = j * (j * s) * ℏ := by rw [hjs]
      _ = (j * j) * (s * ℏ) := by noncomm_ring
      _ = (-1) * (s * ℏ) := by rw [hjj]
      _ = -(s * ℏ) := by noncomm_ring
      _ = -(ℏ * s) := by rw [hℏs]
  calc
    (p + j * s * q) * (p - j * s * q) =
        p * p + ((j * s * q) * p - p * (j * s * q)) - (j * s * q) * (j * s * q) := by
          noncomm_ring
    _ = p * p + j * s * (j * ℏ) - (j * s * q) * (j * s * q) := by rw [hup]
    _ = p * p + -(ℏ * s) - -(s * s * q * q) := by rw [hcorr, hsquare]
    _ = p * p + s * s * q * q - ℏ * s := by noncomm_ring

/-- With `s = μ Ω`, `(1/(2μ)) A†A` is the vacuum-subtracted oscillator. -/
theorem oscillator_energy {μ Ω ℏ p q : ℝ} (hμ : μ ≠ 0) :
    (1 / (2 * μ)) * (p * p + (μ * Ω) * (μ * Ω) * q * q - ℏ * (μ * Ω)) =
      p * p / (2 * μ) + (1 / 2) * μ * Ω ^ 2 * q * q - ℏ * Ω / 2 := by
  field_simp [hμ]

/-- `c / (2 √(2 M μ)) ≤ x²/(2M) + y²/(4μ)` whenever `c ≤ 2xy` and the masses are positive
(`eq:RS_s`). -/
theorem rs_floor {x y c M μ : ℝ} (hc : c ≤ 2 * x * y)
    (hM : 0 < M) (hμ : 0 < μ) :
    c / (2 * Real.sqrt (2 * M * μ)) ≤ x ^ 2 / (2 * M) + y ^ 2 / (4 * μ) := by
  have ha : (0 : ℝ) ≤ 2 * M := by positivity
  have hb : (0 : ℝ) ≤ 4 * μ := by positivity
  have ha2 : Real.sqrt (2 * M) ^ 2 = 2 * M := Real.sq_sqrt ha
  have hb2 : Real.sqrt (4 * μ) ^ 2 = 4 * μ := Real.sq_sqrt hb
  have hpoly : 2 * x * y * Real.sqrt (2 * M) * Real.sqrt (4 * μ) ≤
      x ^ 2 * (4 * μ) + y ^ 2 * (2 * M) := by
    nlinarith [sq_nonneg (x * Real.sqrt (4 * μ) - y * Real.sqrt (2 * M)), ha2, hb2]
  have hden : 0 < (2 * M) * (4 * μ) := by positivity
  have hdiv : 2 * x * y * Real.sqrt (2 * M) * Real.sqrt (4 * μ) / ((2 * M) * (4 * μ)) ≤
      (x ^ 2 * (4 * μ) + y ^ 2 * (2 * M)) / ((2 * M) * (4 * μ)) :=
    div_le_div_of_nonneg_right hpoly (le_of_lt hden)
  have hprod : Real.sqrt (2 * M) * Real.sqrt (4 * μ) = 2 * Real.sqrt (2 * M * μ) := by
    rw [← Real.sqrt_mul ha]
    have : (2 * M) * (4 * μ) = 4 * (2 * M * μ) := by ring
    rw [this, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt4]
  have henergy : x ^ 2 / (2 * M) + y ^ 2 / (4 * μ) =
      (x ^ 2 * (4 * μ) + y ^ 2 * (2 * M)) / ((2 * M) * (4 * μ)) := by
    field_simp
  have hane : Real.sqrt (2 * M) ≠ 0 := by positivity
  have hbne : Real.sqrt (4 * μ) ≠ 0 := by positivity
  have hgeom : 2 * x * y / (Real.sqrt (2 * M) * Real.sqrt (4 * μ)) =
      2 * x * y * Real.sqrt (2 * M) * Real.sqrt (4 * μ) / ((2 * M) * (4 * μ)) := by
    field_simp [hane, hbne]
    rw [ha2, hb2]
    ring
  have hhalf : x * y / Real.sqrt (2 * M * μ) =
      2 * x * y / (Real.sqrt (2 * M) * Real.sqrt (4 * μ)) := by
    rw [hprod]
    field_simp [show Real.sqrt (2 * M * μ) ≠ 0 by positivity]
  have hsqrt : 0 < Real.sqrt (2 * M * μ) := by positivity
  have htwo : 0 < 2 * Real.sqrt (2 * M * μ) := by positivity
  have hc' : c / (2 * Real.sqrt (2 * M * μ)) ≤ x * y / Real.sqrt (2 * M * μ) := by
    rw [div_le_div_iff₀ htwo hsqrt]
    have := mul_le_mul_of_nonneg_right hc (le_of_lt hsqrt)
    linarith
  have hmain : x * y / Real.sqrt (2 * M * μ) ≤ x ^ 2 / (2 * M) + y ^ 2 / (4 * μ) := by
    rw [hhalf, hgeom, henergy]
    exact hdiv
  linarith [hc', hmain]

theorem second_difference_affine (f : ℚ → ℚ) (a b : ℚ) (hf : ∀ n, f n = a + b * n) (n : ℚ) :
    f (n + 1) - 2 * f n + f (n - 1) = 0 := by
  simp only [hf]
  ring

theorem c2_is_affine (n A B C D : ℚ) :
    A + B * (n + 1 / 2) + C * n + D * (n + 1) =
      (A + B * (1 / 2) + D) + (B + C + D) * n := by
  ring

theorem bottle_window_constants {ℏ μ Ω H : ℝ} (hℏ : ℏ ≠ 0) (hμ : μ ≠ 0) (hΩ : Ω ≠ 0)
    (hH : H ≠ 0) :
    (ℏ ^ 2 / (2 * μ)) / (4 * (2 * H / (μ * Ω ^ 2))) = ℏ ^ 2 * Ω ^ 2 / (16 * H) ∧
      4 * (2 * ℏ ^ 2 * H / μ) / (ℏ ^ 2 / (2 * μ)) = 16 * H ∧
      (ℏ ^ 2 / (2 * μ)) / (2 * (16 * H)) = ℏ ^ 2 / (64 * μ * H) := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

/-- `F² ≤ 16 Q D` is exactly `E₋ = F/(4Q) ≤ E₊ = 4D/F`. -/
theorem bottle_window_order {Q F D : ℝ} (hQ : 0 < Q) (hF : 0 < F) (_hD : 0 < D)
    (hbound : F ^ 2 ≤ 16 * Q * D) :
    F / (4 * Q) ≤ 4 * D / F := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem window_tails {Q F D : ℝ} (hQ : Q ≠ 0) (hF : F ≠ 0) (hD : D ≠ 0) :
    (F / (4 * Q)) * Q = F / 4 ∧ D / (4 * D / F) = F / 4 ∧ F - F / 4 - F / 4 = F / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · ring

/-- Nonnegative weights obey `(∑ w E)² ≤ (∑ w) (∑ w E²)`. -/
theorem moment_cauchy {ι : Type*} [Fintype ι] (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hQ : 0 < ∑ i, w i) :
    (∑ i, w i * E i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * E i ^ 2 := by
  classical
  let Q := ∑ i, w i
  let F := ∑ i, w i * E i
  let D := ∑ i, w i * E i ^ 2
  let t := F / Q
  have hnn : 0 ≤ ∑ i, w i * (E i - t) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hterm : ∀ i, w i * (E i - t) ^ 2 = w i * E i ^ 2 - 2 * t * (w i * E i) + t ^ 2 * w i := by
    intro i
    ring
  have hexp : ∑ i, w i * (E i - t) ^ 2 =
      ∑ i, w i * E i ^ 2 - ∑ i, (2 * t * (w i * E i)) + ∑ i, (t ^ 2 * w i) := by
    simp_rw [hterm]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hF : ∑ i, (2 * t * (w i * E i)) = 2 * t * F := by
    simp only [F]
    rw [← Finset.mul_sum]
  have hQsum : ∑ i, (t ^ 2 * w i) = t ^ 2 * Q := by
    simp only [Q]
    rw [← Finset.mul_sum]
  have hvar0 : 0 ≤ D - 2 * t * F + t ^ 2 * Q := by
    rw [hexp, hF, hQsum] at hnn
    simpa [D] using hnn
  have hvar : 0 ≤ D * Q - F ^ 2 := by
    have h0 : 0 ≤ D - 2 * (F / Q) * F + (F / Q) ^ 2 * Q := by simpa [t] using hvar0
    have hrewrite : D - 2 * (F / Q) * F + (F / Q) ^ 2 * Q = D - F ^ 2 / Q := by
      field_simp [hQ.ne']
      ring
    rw [hrewrite] at h0
    have hmul := mul_le_mul_of_nonneg_left h0 (le_of_lt hQ)
    have hcleared : Q * (D - F ^ 2 / Q) = D * Q - F ^ 2 := by
      rw [mul_sub, mul_div_cancel₀ _ hQ.ne']
      ring
    rw [hcleared] at hmul
    simpa using hmul
  have horder : F ^ 2 ≤ Q * D := by
    have hFD : F ^ 2 ≤ D * Q := by linarith
    linarith
  simpa [Q, F, D] using horder

/-- Inversion of `c ≤ E + b √E`. Both sides of the resulting square are nonnegative. -/
theorem drift_inversion {E b c : ℝ} (hb : 0 < b) (hE : 0 ≤ E) (hc : 0 ≤ c)
    (hdrift : c ≤ E + b * Real.sqrt E) :
    (b ^ 2 / 4) * (Real.sqrt (1 + 4 * c / b ^ 2) - 1) ^ 2 ≤ E := by
  have hb0 : 0 ≤ b := le_of_lt hb
  set x := Real.sqrt E
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = E := Real.sq_sqrt hE
  have hdisc : 0 ≤ b ^ 2 + 4 * c := by linarith [sq_nonneg b, hc]
  have hratio : 1 + 4 * c / b ^ 2 = (b ^ 2 + 4 * c) / b ^ 2 := by
    field_simp [hb.ne']
  have hsqrt_ratio :
      Real.sqrt (1 + 4 * c / b ^ 2) = Real.sqrt (b ^ 2 + 4 * c) / b := by
    rw [hratio, Real.sqrt_div hdisc (b ^ 2), Real.sqrt_sq hb0]
  set δ := (b / 2) * (Real.sqrt (1 + 4 * c / b ^ 2) - 1)
  have hδ : δ = (Real.sqrt (b ^ 2 + 4 * c) - b) / 2 := by
    rw [show δ = (b / 2) * (Real.sqrt (1 + 4 * c / b ^ 2) - 1) from rfl, hsqrt_ratio]
    field_simp [hb.ne']
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    have hs : b ≤ Real.sqrt (b ^ 2 + 4 * c) := by
      rw [Real.le_sqrt hb0 hdisc]
      nlinarith [sq_nonneg b]
    linarith
  have hδ_le : δ ≤ x := by
    rw [hδ, div_le_iff₀' (by norm_num : (0 : ℝ) < 2)]
    have htarget : Real.sqrt (b ^ 2 + 4 * c) ≤ 2 * x + b := by
      have hxb : 0 ≤ 2 * x + b := by linarith
      rw [Real.sqrt_le_iff]
      refine ⟨hxb, ?_⟩
      have hsq : (2 * x + b) ^ 2 = b ^ 2 + 4 * (E + b * x) := by
        rw [← hx2]
        ring
      rw [hsq]
      have h4 : 4 * c ≤ 4 * (E + b * x) := by
        simpa [x] using mul_le_mul_of_nonneg_left hdrift (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    linarith
  have hsqle : δ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hδ0 hδ_le 2
  have hδsq : δ ^ 2 =
      (b ^ 2 / 4) * (Real.sqrt (1 + 4 * c / b ^ 2) - 1) ^ 2 := by
    simp only [δ]
    ring
  calc
    (b ^ 2 / 4) * (Real.sqrt (1 + 4 * c / b ^ 2) - 1) ^ 2 = δ ^ 2 := by rw [hδsq]
    _ ≤ x ^ 2 := hsqle
    _ = E := hx2

/-- `b = √(ℏΩ/2)` and `c = ℏ αA / (4 √(2μM))` give `b²/4 = ℏΩ/8`
and `4c/b² = 2λ`. -/
theorem drift_coefficients {ℏ Ω μ M αA : ℝ} (hℏ : 0 < ℏ) (hΩ : 0 < Ω) (hμ : 0 < μ)
    (hM : 0 < M) :
    Real.sqrt (ℏ * Ω / 2) ^ 2 / 4 = ℏ * Ω / 8 ∧
      4 * (ℏ * αA / (4 * Real.sqrt (2 * μ * M))) / Real.sqrt (ℏ * Ω / 2) ^ 2 =
        2 * (αA / (Ω * Real.sqrt (2 * μ * M))) := by
  have hb2 : Real.sqrt (ℏ * Ω / 2) ^ 2 = ℏ * Ω / 2 := Real.sq_sqrt (by positivity)
  constructor
  · rw [hb2]
    ring
  · rw [hb2]
    field_simp

/-- The strong-pinch slope of the boxed floor is `c`. Halving the discriminant gives `c/2`. -/
theorem strong_pinch_slope {ℏ Ω μ M αA : ℝ} (hΩ : Ω ≠ 0)
    (hden : Real.sqrt (2 * μ * M) ≠ 0) :
    (ℏ * Ω / 8) * (2 * (αA / (Ω * Real.sqrt (2 * μ * M)))) =
        ℏ * αA / (4 * Real.sqrt (2 * μ * M)) ∧
      (ℏ * Ω / 8) * (αA / (Ω * Real.sqrt (2 * μ * M))) =
        (ℏ * αA / (4 * Real.sqrt (2 * μ * M))) / 2 := by
  constructor <;> field_simp [hΩ, hden] <;> ring

/-- `(√(1+2λ) - 1)² = (2λ)² / (√(1+2λ) + 1)²`, so the floor is quadratic at `λ = 0`. -/
theorem weak_pinch_square {lam : ℝ} (hlam : 0 ≤ lam) :
    (Real.sqrt (1 + 2 * lam) - 1) ^ 2 =
      (2 * lam) ^ 2 / (Real.sqrt (1 + 2 * lam) + 1) ^ 2 := by
  set s := Real.sqrt (1 + 2 * lam)
  have hs : s ^ 2 = 1 + 2 * lam := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s + 1 ≠ 0 := by linarith
  have hdiff : (s - 1) * (s + 1) = 2 * lam := by
    calc
      (s - 1) * (s + 1) = s ^ 2 - 1 := by ring
      _ = 2 * lam := by rw [hs]; ring
  have hlin : s - 1 = 2 * lam / (s + 1) := by
    rw [← hdiff]
    field_simp [hs1]
  have : (s - 1) ^ 2 = (2 * lam) ^ 2 / (s + 1) ^ 2 := by
    rw [hlin]
    field_simp [hs1]
  simpa [s] using this

/-- The `√(1+λ)` increment is at most the boxed `√(1+2λ)` increment. -/
theorem printed_pinch_is_weaker {lam : ℝ} (hlam : 0 ≤ lam) :
    Real.sqrt (1 + lam) - 1 ≤ Real.sqrt (1 + 2 * lam) - 1 := by
  have h : Real.sqrt (1 + lam) ≤ Real.sqrt (1 + 2 * lam) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

theorem printed_pinch_strict {lam : ℝ} (hlam : 0 < lam) :
    Real.sqrt (1 + lam) - 1 < Real.sqrt (1 + 2 * lam) - 1 := by
  have h : Real.sqrt (1 + lam) < Real.sqrt (1 + 2 * lam) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

/-- Replacing `2λ` by `λ` still follows from the drift inequality, and is the weaker bound. -/
theorem printed_floor_from_drift {E b c : ℝ} (hb : 0 < b) (hE : 0 ≤ E) (hc : 0 ≤ c)
    (hdrift : c ≤ E + b * Real.sqrt E) :
    (b ^ 2 / 4) * (Real.sqrt (1 + 2 * c / b ^ 2) - 1) ^ 2 ≤ E := by
  set lam := 2 * c / b ^ 2
  have hb2 : 0 < b ^ 2 := by positivity
  have hlam : 0 ≤ lam := div_nonneg (by linarith) (le_of_lt hb2)
  have htwice : 1 + 2 * lam = 1 + 4 * c / b ^ 2 := by
    unfold lam
    field_simp [hb.ne']
    ring
  have hsq : (Real.sqrt (1 + lam) - 1) ^ 2 ≤
      (Real.sqrt (1 + 2 * lam) - 1) ^ 2 := by
    have hinc := printed_pinch_is_weaker hlam
    have hbase : 0 ≤ Real.sqrt (1 + lam) - 1 := by
      have hone : (1 : ℝ) ≤ 1 + lam := by linarith
      have : (1 : ℝ) ≤ Real.sqrt (1 + lam) := by
        rw [Real.le_sqrt (by norm_num) (by linarith : 0 ≤ 1 + lam)]
        nlinarith [hone]
      linarith
    exact pow_le_pow_left₀ hbase hinc 2
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ b ^ 2 / 4)
  have hcorrect := drift_inversion hb hE hc hdrift
  calc
    (b ^ 2 / 4) * (Real.sqrt (1 + 2 * c / b ^ 2) - 1) ^ 2 =
        (b ^ 2 / 4) * (Real.sqrt (1 + lam) - 1) ^ 2 := by
      simp [lam]
    _ ≤ (b ^ 2 / 4) * (Real.sqrt (1 + 2 * lam) - 1) ^ 2 := hmul
    _ = (b ^ 2 / 4) * (Real.sqrt (1 + 4 * c / b ^ 2) - 1) ^ 2 := by rw [htwice]
    _ ≤ E := hcorrect

end
