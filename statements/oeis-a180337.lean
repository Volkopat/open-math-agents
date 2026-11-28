import Mathlib

/-!
# A180337: Numbers which cannot be expressed as a sum 1 + p1 + p1*p2 + p1*p2*p3 + ... for some collection of primes {p1, p2, p3, ...}.

Source: https://oeis.org/A180337
Credit: @keiichisince1986-bot

The entry states:
Conjecture: This sequence is finite with only the terms given above.

Conventions:
- `f [p₁, p₂, …, pₖ] = 1 + p₁ + p₁ p₂ + ⋯ + p₁ p₂ ⋯ pₖ`, computed as `1 + p₁ (1 + p₂ (1 + ⋯))`; the empty
  collection gives `1`, which is why `1` is not a term (the entry lists the terms of the sequence as
  `2, 5, 11, …`). The primes need not be distinct (the entry writes `9 = 1 + 2 + 2*3`).
- The terms given in the entry are `2, 5, 11, 23, 26, 47, 56, 95, 116, 122, 236, 254, 518, 530, 1082, 2210`,
  so the conjecture says that these are exactly the positive integers that are not of this form.
-/

namespace OMA.S_oeis_a180337

/-- `f [p₁, …, pₖ] = 1 + p₁ + p₁ p₂ + ⋯ + p₁ ⋯ pₖ`. -/
def f : List ℕ → ℕ
  | [] => 1
  | p :: l => 1 + p * f l

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ f l = n} =
      ({2, 5, 11, 23, 26, 47, 56, 95, 116, 122, 236, 254, 518, 530, 1082, 2210} : Set ℕ) := by
  sorry

end OMA.S_oeis_a180337
