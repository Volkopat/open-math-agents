import Mathlib

/-!
# Trace of the polar factor of a diagonally dominant matrix

Source: https://mathoverflow.net/questions/275818 (Astor, CC BY-SA 3.0).
Credit: @connoranderson

Diagonal dominance means weak row dominance, so singular matrices are allowed.
The proposed bound fails in order two, where a null singular vector can be
reversed. For the nonsingular planar case the trace has an explicit formula
and its sharp infimum over strictly dominant matrices is √2.
-/

namespace OMA.S_mo_275818
open Matrix Finset
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
def orth (Q : Mat) : Prop := Qᵀ*Q=1 ∧ Q*Qᵀ=1
def svd (A U V : Mat) (s : Fin 2 → ℝ) : Prop :=
  orth U ∧ orth V ∧ 0 ≤ s 1 ∧ s 1 ≤ s 0 ∧ A=U*diagonal s*Vᵀ
def admissible (A : Mat) : Prop := ¬ A.IsSymm ∧ (∀ i, 0 < A i i) ∧
  (∀ i j, i≠j → A i j<0) ∧ ∀ i, (∑ j ∈ univ.erase i, |A i j|) ≤ A i i
def strict (A : Mat) : Prop := ∀ i, (∑ j ∈ univ.erase i, |A i j|) < A i i
def witness : Mat := !![7,-7;-1,1]

theorem main :
    (admissible witness ∧ witness.rank = 1 ∧
      ∃ U V U' : Mat, ∃ s : Fin 2 → ℝ, svd witness U V s ∧ svd witness U' V s ∧
        (U*Vᵀ).trace=0 ∧ (U'*Vᵀ).trace=8/5) ∧
    (∀ (A U V : Mat) (s : Fin 2 → ℝ), admissible A → A.det ≠ 0 → svd A U V s →
      (U*Vᵀ).trace = 2*A.trace/Real.sqrt (A.trace^2+(A 1 0-A 0 1)^2) ∧
      Real.sqrt 2 < (U*Vᵀ).trace) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (A U V : Mat) (s : Fin 2 → ℝ),
      admissible A ∧ strict A ∧ A.det ≠ 0 ∧ svd A U V s ∧ (U*Vᵀ).trace < Real.sqrt 2+ε) := by
  sorry
end OMA.S_mo_275818
