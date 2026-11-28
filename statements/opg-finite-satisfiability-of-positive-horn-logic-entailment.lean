import Mathlib

/-!
# Finite satisfiability of positive Horn logic entailment

Source: https://www.openproblemgarden.org/op/finite_satisfiability_of_positive_horn_logic_entailment
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Madelaine–Martin): positive Horn logic `pH` is the fragment of first-order logic built
from atoms with `∃, ∀, ∧, =`. Does the fragment `pH ∧ ¬pH` have the finite model property?
That is: if a sentence `φ ∧ ¬ψ` with `φ, ψ ∈ pH` has a model, does it have a finite model?
(Equivalently, `pH` entailment coincides with finite entailment.) `main` states the positive
answer.

Conventions. A relational signature with relation symbols of type `R` and arities
`ar : R → ℕ` (as in the source's setting, constraint languages: relational, no function
symbols); formulas use variables `ℕ`; structures are nonempty. Atoms are `x = y` and
`r(x₁, …, x_k)`; `pH` formulas are closed under `∧`, `∃ x`, `∀ x`. A sentence is a formula
with no free variables; truth is evaluated under any assignment.
-/

namespace OMA.S_opg_finite_satisfiability_of_positive_horn_logic_entailment

/-- Positive Horn formulas over a relational signature. -/
inductive PH {R : Type} (ar : R → ℕ) : Type
  | eq : ℕ → ℕ → PH ar
  | rel : (r : R) → (Fin (ar r) → ℕ) → PH ar
  | and : PH ar → PH ar → PH ar
  | ex : ℕ → PH ar → PH ar
  | all : ℕ → PH ar → PH ar

variable {R : Type} {ar : R → ℕ}

/-- Free variables. -/
def PH.free : PH ar → Set ℕ
  | .eq x y => {x, y}
  | .rel _ xs => Set.range xs
  | .and φ ψ => φ.free ∪ ψ.free
  | .ex x φ => φ.free \ {x}
  | .all x φ => φ.free \ {x}

/-- A structure for the signature. -/
structure Str (ar : R → ℕ) where
  carrier : Type
  nonempty : Nonempty carrier
  interp : (r : R) → (Fin (ar r) → carrier) → Prop

/-- Satisfaction under an assignment. -/
def PH.sat (M : Str ar) : PH ar → (ℕ → M.carrier) → Prop
  | .eq x y, s => s x = s y
  | .rel r xs, s => M.interp r (s ∘ xs)
  | .and φ ψ, s => φ.sat M s ∧ ψ.sat M s
  | .ex x φ, s => ∃ a, φ.sat M (Function.update s x a)
  | .all x φ, s => ∀ a, φ.sat M (Function.update s x a)

/-- Positive answer: `pH ∧ ¬pH` has the finite model property. -/
theorem main :
    ∀ (R : Type) [Finite R] (ar : R → ℕ) (φ ψ : PH ar), φ.free = ∅ → ψ.free = ∅ →
      (∃ (M : Str ar) (s : ℕ → M.carrier), φ.sat M s ∧ ¬ ψ.sat M s) →
      ∃ (M : Str ar) (_ : Finite M.carrier) (s : ℕ → M.carrier), φ.sat M s ∧ ¬ ψ.sat M s := by
  sorry

end OMA.S_opg_finite_satisfiability_of_positive_horn_logic_entailment
