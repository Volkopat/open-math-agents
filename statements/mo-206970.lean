import Mathlib

/-!
# Is the product of two supermodular functions supermodular?

Source: https://mathoverflow.net/questions/206970
Credit: @JEcon

Call `f : ℝ → ℝ → ℝ` supermodular if for all `x < x'` and `y < y'`,
`f x' y' + f x y ≥ f x' y + f x y'`. The question asks: if `f` and `g` are supermodular,
non-negative and increasing in both arguments, is the product `h = f * g` supermodular?

The question writes the defining inequality with a strict sign. We state both readings: the
weak one (the usual definition of supermodularity) and the strict one (exactly the inequality
written in the question). In both, increasing means monotone (non-decreasing) in each argument.

Formalization notes:
* Functions are of two real variables, as in the question.
* `main` is the conjunction of the weak and the strict statement.
-/

namespace OMA.S_mo_206970

/-- Weak supermodularity of a function of two real variables. -/
def Supermod (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x x' y y' : ℝ, x < x' → y < y' → f x' y + f x y' ≤ f x' y' + f x y

/-- Strict supermodularity, the inequality as written in the question. -/
def StrictSupermod (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x x' y y' : ℝ, x < x' → y < y' → f x' y + f x y' < f x' y' + f x y

/-- Non-negative and non-decreasing in each argument. -/
def NonnegIncr (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, 0 ≤ f x y) ∧ (∀ x x' y, x ≤ x' → f x y ≤ f x' y) ∧ (∀ x y y', y ≤ y' → f x y ≤ f x y')

/-- The product of two non-negative increasing supermodular functions is supermodular, both for
the weak and for the strict notion. -/
theorem main :
    (∀ f g : ℝ → ℝ → ℝ, NonnegIncr f → NonnegIncr g → Supermod f → Supermod g →
      Supermod (fun x y => f x y * g x y)) ∧
    (∀ f g : ℝ → ℝ → ℝ, NonnegIncr f → NonnegIncr g → StrictSupermod f → StrictSupermod g →
      StrictSupermod (fun x y => f x y * g x y)) := by
  sorry

end OMA.S_mo_206970
