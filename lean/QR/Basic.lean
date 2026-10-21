module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSimpArgs false

/-!
# Bilayer group, Pauli holonomy, and sheet parity

Algebraic core of the `J₂` story group (`eq:mainJ2`), the bilayer Pauli matrices
(`thm:su2_spin_fine`, `eq:su2_holonomy`), and the sheet-parity invariants of the
gyroscopic current.
-/

open Matrix

public section

/-- Sheet bit of a `J₂` element. Addition is the sum in `Fin 2`. -/
abbrev Sheet := Fin 2

/-- Coordinate swap controlled by the sheet bit: the identity on sheet `0` and the
transposition of the two planar coordinates on sheet `1`. -/
def sigmaSheet (b : Sheet) (y : Fin 2 → ℤ) : Fin 2 → ℤ :=
  if b = 0 then y else ![y 1, y 0]

theorem sigmaSheet_zero (y : Fin 2 → ℤ) : sigmaSheet 0 y = y := by
  simp [sigmaSheet]

theorem sigmaSheet_zero_fun : sigmaSheet 0 = id := by
  funext y
  simp [sigmaSheet_zero]

theorem sigmaSheet_add (b : Sheet) (y z : Fin 2 → ℤ) :
    sigmaSheet b (y + z) = sigmaSheet b y + sigmaSheet b z := by
  fin_cases b <;> ext i <;> fin_cases i <;> simp [sigmaSheet]

theorem sigmaSheet_neg (b : Sheet) (y : Fin 2 → ℤ) :
    sigmaSheet b (-y) = -sigmaSheet b y := by
  fin_cases b <;> ext i <;> fin_cases i <;> simp [sigmaSheet]

theorem sigmaSheet_zero_vec (b : Sheet) : sigmaSheet b 0 = 0 := by
  fin_cases b <;> ext i <;> fin_cases i <;> simp [sigmaSheet]

/-- `σ^b ∘ σ^c = σ^{b+c}`. -/
theorem sigmaSheet_comp (b c : Sheet) (y : Fin 2 → ℤ) :
    sigmaSheet b (sigmaSheet c y) = sigmaSheet (b + c) y := by
  fin_cases b <;> fin_cases c <;> ext i <;> fin_cases i <;> simp [sigmaSheet]

theorem sheet_add_self (b : Sheet) : b + b = 0 := by
  fin_cases b <;> decide

/-- An element of the `J₂` bilayer group: a planar integer displacement together with a sheet bit.
Multiplication is `(x, b)(y, c) = (x + σ^b y, b + c)`. -/
structure J2 where
  x : Fin 2 → ℤ
  b : Sheet
  deriving DecidableEq

namespace J2

theorem ext {p q : J2} (hx : p.x = q.x) (hb : p.b = q.b) : p = q := by
  cases p
  cases q
  cases hx
  cases hb
  rfl

instance : Mul J2 where
  mul p q := ⟨p.x + sigmaSheet p.b q.x, p.b + q.b⟩

instance : One J2 where
  one := ⟨0, 0⟩

instance : Inv J2 where
  inv p := ⟨-sigmaSheet p.b p.x, p.b⟩

theorem mul_def (p q : J2) : p * q = ⟨p.x + sigmaSheet p.b q.x, p.b + q.b⟩ := rfl

theorem one_def : (1 : J2) = ⟨0, 0⟩ := rfl

theorem inv_def (p : J2) : p⁻¹ = ⟨-sigmaSheet p.b p.x, p.b⟩ := rfl

instance : Group J2 where
  mul_assoc p q r := by
    apply J2.ext
    · ext i
      simp only [mul_def, sigmaSheet_add, sigmaSheet_comp, add_assoc]
    · simp only [mul_def, add_assoc]
  one_mul p := by
    apply J2.ext
    · ext i
      simp [mul_def, one_def, sigmaSheet_zero]
    · simp [mul_def, one_def]
  mul_one p := by
    apply J2.ext
    · ext i
      simp [mul_def, one_def, sigmaSheet_zero_vec]
    · simp [mul_def, one_def]
  inv_mul_cancel p := by
    apply J2.ext
    · funext i
      simp [mul_def, inv_def, one_def, sigmaSheet_neg]
    · simp [mul_def, inv_def, one_def, sheet_add_self]

/-- Standard basis displacement along the first planar coordinate. -/
def e1 : Fin 2 → ℤ := ![1, 0]

/-- Standard basis displacement along the second planar coordinate. -/
def e2 : Fin 2 → ℤ := ![0, 1]

/-- The eight inverse-closed generators named in the `J₂` presentation. -/
def gen : Fin 8 → J2
  | 0 => ⟨e1, 0⟩
  | 1 => ⟨-e1, 0⟩
  | 2 => ⟨e2, 0⟩
  | 3 => ⟨-e2, 0⟩
  | 4 => ⟨e1, 1⟩
  | 5 => ⟨-e2, 1⟩
  | 6 => ⟨e2, 1⟩
  | 7 => ⟨-e1, 1⟩

theorem gen_inv_closed (i : Fin 8) : ∃ j : Fin 8, (gen i)⁻¹ = gen j := by
  fin_cases i
  · refine ⟨1, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨0, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨3, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨2, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨5, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨4, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨7, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]
  · refine ⟨6, ?_⟩
    apply J2.ext <;> (try (ext k; fin_cases k)) <;> simp [gen, inv_def, e1, e2, sigmaSheet]

theorem e1_pow (n : ℕ) : (⟨e1, 0⟩ : J2) ^ n = ⟨![↑n, 0], 0⟩ := by
  induction n with
  | zero =>
    apply J2.ext
    · ext k
      fin_cases k <;> simp [one_def]
    · simp [one_def]
  | succ n ih =>
    rw [pow_succ, ih]
    apply J2.ext
    · ext k
      fin_cases k <;> simp [mul_def, e1, sigmaSheet]
    · simp [mul_def]

theorem e2_pow (n : ℕ) : (⟨e2, 0⟩ : J2) ^ n = ⟨![0, ↑n], 0⟩ := by
  induction n with
  | zero =>
    apply J2.ext
    · ext k
      fin_cases k <;> simp [one_def]
    · simp [one_def]
  | succ n ih =>
    rw [pow_succ, ih]
    apply J2.ext
    · ext k
      fin_cases k <;> simp [mul_def, e2, sigmaSheet]
    · simp [mul_def]

/-- Every sheet-zero displacement factors through the two commuting translations. -/
theorem sheet0_factor (a b : ℤ) :
    (⟨![a, 0], 0⟩ : J2) * ⟨![0, b], 0⟩ = ⟨![a, b], 0⟩ := by
  apply J2.ext
  · ext k
    fin_cases k <;> simp [mul_def, sigmaSheet]
  · simp [mul_def]

/-- A sheet-one element is a sheet-zero translation followed by the generator `(e₁, 1)`. -/
theorem sheet1_factor (a b : ℤ) :
    (⟨![a - 1, b], 0⟩ : J2) * ⟨e1, 1⟩ = ⟨![a, b], 1⟩ := by
  apply J2.ext
  · ext k
    fin_cases k <;> simp [mul_def, e1, sigmaSheet]
  · simp [mul_def]

theorem gen_generates_sheet0_e1 (n : ℕ) :
    (⟨![↑n, 0], 0⟩ : J2) ∈ Subgroup.closure (Set.range gen) := by
  have hmem : (⟨e1, 0⟩ : J2) ∈ Subgroup.closure (Set.range gen) :=
    Subgroup.subset_closure ⟨0, by simp [gen]⟩
  simpa [e1_pow] using (Subgroup.closure (Set.range gen)).pow_mem hmem n

theorem gen_generates_sheet0_e2 (n : ℕ) :
    (⟨![0, ↑n], 0⟩ : J2) ∈ Subgroup.closure (Set.range gen) := by
  have hmem : (⟨e2, 0⟩ : J2) ∈ Subgroup.closure (Set.range gen) :=
    Subgroup.subset_closure ⟨2, by simp [gen]⟩
  simpa [e2_pow] using (Subgroup.closure (Set.range gen)).pow_mem hmem n

end J2

/-! ## Bilayer Pauli matrices -/

/-- Sheet exchange `σ₁`. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Gyroscopic sheet circulation `σ₂ = i J`. -/
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Sheet grading `σ₃`. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli1_sq : pauli1 * pauli1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli2_sq : pauli2 * pauli2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

theorem pauli3_sq : pauli3 * pauli3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli3, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli1_mul_pauli2 : pauli1 * pauli2 = Complex.I • pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem pauli2_mul_pauli1 : pauli2 * pauli1 = -Complex.I • pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- `σ₃ = -(i/2) [σ₁, σ₂]`, the relation recorded after `eq:SN_scatter`. -/
theorem pauli3_from_commutator :
    pauli3 = (-(Complex.I / 2)) • (pauli1 * pauli2 - pauli2 * pauli1) := by
  rw [pauli1_mul_pauli2, pauli2_mul_pauli1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli3, Matrix.smul_apply, Complex.ext_iff, Complex.I_re, Complex.I_im] <;>
    norm_num

/-- Spinor holonomy `U(n̂, φ) = cos(φ/2) I - i sin(φ/2) (n·σ)`. -/
noncomputable def spinHolonomy (n1 n2 n3 φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (φ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (-Complex.I * Real.sin (φ / 2)) • (n1 • pauli1 + n2 • pauli2 + n3 • pauli3)

/-- A spatial rotation by `2π` acts as `-I` on the bilayer, for every axis (`eq:su2_holonomy`). -/
theorem spinHolonomy_two_pi (n1 n2 n3 : ℝ) :
    spinHolonomy n1 n2 n3 (2 * Real.pi) = -1 := by
  simp [spinHolonomy, Real.cos_pi, Real.sin_pi, Matrix.smul_apply]

/-! ## Sheet parity -/

/-- Gyroscopic current `J = s φ̇ - φ ṡ`. -/
def gyroCurrent (φ s φdot sdot : ℝ) : ℝ := s * φdot - φ * sdot

/-- The current is unchanged when the fields and their time derivatives all flip sign. -/
theorem gyroCurrent_sheet_flip (φ s φdot sdot : ℝ) :
    gyroCurrent (-φ) (-s) (-φdot) (-sdot) = gyroCurrent φ s φdot sdot := by
  simp [gyroCurrent]

/-- Quadratic sheet energy `q² (s² + φ²)`. -/
def sheetEnergy (q φ s : ℝ) : ℝ := q ^ 2 * (s ^ 2 + φ ^ 2)

theorem sheetEnergy_sheet_flip (q φ s : ℝ) :
    sheetEnergy q (-φ) (-s) = sheetEnergy q φ s := by
  simp [sheetEnergy]

/-- `tan` and `sin²` are invariant under a sheet shift of `π`. -/
theorem tan_sheet_shift (θ : ℝ) : Real.tan (θ + Real.pi) = Real.tan θ :=
  Real.tan_add_pi θ

theorem sin_sq_sheet_shift (θ : ℝ) : Real.sin (θ + Real.pi) ^ 2 = Real.sin θ ^ 2 := by
  rw [Real.sin_add_pi]
  ring

end
