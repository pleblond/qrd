module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

/-!
# Unitary contraction, echo fidelity, and causal windows

Theorem 4.1 (`thm:extended_markovian`, `eq:unitary_contract`) and the rectangular-pulse latency
comparison of Proposition A.1.
-/

set_option linter.style.header false
set_option linter.unusedSimpArgs false

open Matrix Real Set

public section

noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt 2) • !![1, 1; 1, -1]

theorem inv_sqrt_two_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← sq, Real.sq_sqrt (by norm_num)]
  norm_num

theorem hadamard_unitary : hadamard.transpose * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, inv_sqrt_two_sq] <;>
    norm_num

theorem hadamard_involution : hadamard * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      inv_sqrt_two_sq] <;>
    norm_num

/-- Coherent population of the equal superposition, before dephasing. -/
noncomputable def plusState : Fin 2 → ℝ := ![1 / Real.sqrt 2, 1 / Real.sqrt 2]

theorem plus_normalized : plusState ⬝ᵥ plusState = 1 := by
  simp [plusState, dotProduct, Fin.sum_univ_two, inv_sqrt_two_sq]
  norm_num

/-- After dephasing in the computational basis each diagonal entry is `1/2`. -/
theorem dephased_population (i : Fin 2) : plusState i ^ 2 = 1 / 2 := by
  fin_cases i <;> simp [plusState, inv_sqrt_two_sq]

theorem contract_probabilities (Λ φ : ℝ) :
    (1 + Λ * Real.cos φ) / 2 + (1 - Λ * Real.cos φ) / 2 = 1 := by
  ring

theorem dark_sheet_lock : (1 + (1 : ℝ) * Real.cos Real.pi) / 2 = 0 := by
  simp [Real.cos_pi]

theorem bright_sheet_lock : (1 - (1 : ℝ) * Real.cos Real.pi) / 2 = 1 := by
  simp [Real.cos_pi]

/-- Readiness time on a shell with `n - ℓ` bridge stages of latency `n/g`. -/
theorem readiness_bound {n ℓ g : ℝ} (hg : g ≠ 0) :
    (n - ℓ) * (n / g) = n * (n - ℓ) / g := by
  field_simp [hg]

/-- Overlap of two pulses of width `T` whose centers differ by `δ`. -/
theorem overlap_factor {T δ : ℝ} (hT : 0 < T) :
    max 0 (T - |δ|) / T = max 0 (1 - |δ| / T) := by
  by_cases h : T ≤ |δ|
  · have hnonpos : T - |δ| ≤ 0 := by linarith
    have hnonpos' : 1 - |δ| / T ≤ 0 := by
      field_simp [hT.ne'] at *
      linarith
    simp [max_eq_left hnonpos, max_eq_left hnonpos', hT.ne']
  · have hpos : 0 ≤ T - |δ| := by linarith
    have hpos' : 0 ≤ 1 - |δ| / T := by
      field_simp [hT.ne']
      linarith
    simp [max_eq_right hpos, max_eq_right hpos']
    field_simp [hT.ne']

/-- Proposition A.1 at latency `3` and reading time `5/2`: both pulses sit inside the causal
past, while their exit windows are disjoint. -/
theorem pulse_latency_windows :
    (Set.Icc (0 : ℝ) 1 ⊆ Set.Icc ((5 : ℝ) / 2 - 3) (5 / 2)) ∧
      (Set.Icc (1 : ℝ) 2 ⊆ Set.Icc (5 / 2 - 3) (5 / 2)) ∧
      Disjoint (Set.Ico (3 : ℝ) 4) (Set.Ico (4 : ℝ) 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp [Set.mem_Icc] at hx ⊢
    constructor <;> linarith
  · intro x hx
    simp [Set.mem_Icc] at hx ⊢
    constructor <;> linarith
  · rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_empty_iff_false, iff_false]
    intro ⟨h1, h2⟩
    linarith

/-- The patch operator on `span{|000⟩, |111⟩}` satisfies `R† R = |000⟩⟨000|`. -/
def patch : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

theorem patch_adjoint_mul : patch.transpose * patch = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [patch, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

theorem patch_mul_adjoint : patch * patch.transpose = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [patch, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

end
