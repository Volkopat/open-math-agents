import Mathlib

/-!
# A267124: primitive practical numbers.

Source: https://oeis.org/A267124
Credit: @cjchaffin

A positive integer is practical if every integer `k` with `1 ≤ k ≤ n` is a sum of distinct
positive divisors of `n` (A005153; 1 is practical). A practical number is primitive when it
is squarefree, or when dividing it by any prime factor whose exponent is greater than 1
leaves a number that is no longer practical. Equivalently (and as in the PARI/Python on the
page): it is practical, and `n / p` is not practical whenever `p^2` divides `n`.

Conjecture (on the OEIS page): every odd number, beginning with 3, is the sum of a prime
and a primitive practical number.

Conventions: offset 1 for the sequence of primitive practicals; the conjecture is for odd
`n ≥ 3`.
-/

namespace OMA.S_oeis_a267124

/-- `n` is practical: every `k` in `1, …, n` is a sum of distinct positive divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ ∑ i ∈ s, i = k

/-- A primitive practical number, as defined on A267124. -/
def IsPrimitivePractical (n : ℕ) : Prop :=
  IsPractical n ∧ ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → ¬ IsPractical (n / p)

theorem main : ∀ n : ℕ, Odd n → 3 ≤ n →
    ∃ p m : ℕ, p.Prime ∧ IsPrimitivePractical m ∧ p + m = n := by
  sorry

end OMA.S_oeis_a267124
