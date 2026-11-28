import Mathlib

/-!
# Sign-additive continuous functions on the open orthant have the sign pattern of a linear form

Source: https://mathoverflow.net/questions/412572
Credit: @koolkao

Question (High GPA, MathOverflow 412572, 2021; CC BY-SA 4.0). Let `f` be a continuous function on
`ℝⁿ₊ = (0, +∞)ⁿ` such that the sign of `f(x + y)` is determined by the signs of `f(x)` and
`f(y)`, in the following sense (condition (1)): for `x, y ∈ ℝⁿ₊`,
* `f(x) ≥ 0` and `f(y) ≥ 0` imply `f(x + y) ≥ 0`, and `f(x) ≥ 0` and `f(y) > 0` imply
  `f(x + y) > 0`;
* `f(x) ≤ 0` and `f(y) ≤ 0` imply `f(x + y) ≤ 0`, and `f(x) ≤ 0` and `f(y) < 0` imply
  `f(x + y) < 0`.
Must there exist a linear function `g(x) = c · x` such that `g(x) ≥ 0 ⟺ f(x) ≥ 0`?

`main` states that the answer is yes.

Translation choices:
* `ℝⁿ` is `Fin n → ℝ` with `n ≥ 1` (for `n = 0` the orthant is a single point and a negative
  value of `f` there cannot be matched by a linear form), and `ℝⁿ₊` is
  `orthant n = {x | ∀ i, 0 < x i}`; `f` is a function on all of `ℝⁿ` that is continuous on
  `orthant n` (`ContinuousOn`), and only its values on the orthant matter;
* condition (1) is `SignAdditive f` below, quantified over `x, y ∈ orthant n`; the four
  implications are the source's, with the parenthesised strict versions written out;
* the linear function is `x ↦ ∑ i, c i * x i` for some `c : Fin n → ℝ`, and the equivalence
  `g(x) ≥ 0 ⟺ f(x) ≥ 0` is required for `x ∈ orthant n`;
* the body of the question states a "Hypothesis" in "if and only if" form; the title asks for the
  implication from condition (1) to the existence of `g`, which is what `main` states (the
  reverse implication fails for trivial reasons: `n = 1`, `f(x) = max(0, 1 - x)`, `g = 0`).
-/

namespace OMA.S_mo_412572

/-- The open orthant `(0, +∞)ⁿ`. -/
def orthant (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 < x i}

/-- Condition (1) of the source: the sign of `f(x + y)` is determined by those of `f(x)`, `f(y)`. -/
def SignAdditive {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ orthant n, ∀ y ∈ orthant n,
    (0 ≤ f x → 0 ≤ f y → 0 ≤ f (x + y)) ∧ (0 ≤ f x → 0 < f y → 0 < f (x + y)) ∧
    (f x ≤ 0 → f y ≤ 0 → f (x + y) ≤ 0) ∧ (f x ≤ 0 → f y < 0 → f (x + y) < 0)

/-- A continuous sign-additive function on the open orthant is nonnegative exactly where some
linear form is nonnegative. -/
theorem main :
    ∀ (n : ℕ), 0 < n → ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (orthant n) → SignAdditive f →
      ∃ c : Fin n → ℝ, ∀ x ∈ orthant n, (0 ≤ ∑ i, c i * x i ↔ 0 ≤ f x) := by
  sorry

end OMA.S_mo_412572
