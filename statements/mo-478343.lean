import Mathlib

/-!
# Well-spaced subsets of dense sets of integers

Source: https://mathoverflow.net/questions/478343
Asked by MathOverflow user JustSomeGuy.

For `b > 0`, a subset `I ⊆ {1, ..., n}` is called `b`-good if `#I ≥ b n` and consecutive
elements `ℓ_i < ℓ_{i+1}` of `I` satisfy `ℓ_{i+1} - ℓ_i ≤ 1/b`. The question: fix `a > 0`;
is there always a `b = b(a) > 0` such that for all `n ≥ 1` and every `A ⊆ {1, ..., n}` with
`#A ≥ a n` there is a `b`-good subset `I ⊆ A`?

Translation choices.
* Subsets of `{1, ..., n}` are finsets `A ⊆ Finset.Icc 1 n` of natural numbers.
* Two elements `x < y` of `I` are consecutive when no element of `I` lies strictly between
  them; the gap condition is required for all such pairs (as real numbers).
* `main` is the affirmative answer, for every `a > 0`.
-/

namespace OMA.S_mo_478343

/-- `I` is `b`-good inside `{1, ..., n}`. -/
def Good (b : ℝ) (n : ℕ) (I : Finset ℕ) : Prop :=
  b * n ≤ I.card ∧
    ∀ x ∈ I, ∀ y ∈ I, x < y → (∀ z ∈ I, ¬ (x < z ∧ z < y)) → (y : ℝ) - x ≤ 1 / b

theorem main :
    ∀ a : ℝ, 0 < a → ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → a * n ≤ A.card → ∃ I ⊆ A, Good b n I := by
  sorry

end OMA.S_mo_478343
