import Mathlib

/-!
# A085887: Let r and s be such that r + s = n; a(n) = minimum value of tau(r) + tau(s)

Source: https://oeis.org/A085887
Credit: @xor2k

Formalizes the claims of the OEIS A085887 comment (offset 2), as worded:
a(p+1) = 3 if p is a prime. a(n) = 4 if n is the sum of two primes. For all even numbers > 4,
a(n) = 4 by Goldbach's conjecture.

The three sentences are formalized literally as a conjunction:
1. `a (p + 1) = 3` for every prime `p`;
2. `a n = 4` for every `n` that equals `p + q` with `p`, `q` prime;
3. `a n = 4` for every even `n > 4`.
The phrase by Goldbach's conjecture in the third sentence is the comment's justification; the
Goldbach conjecture itself is not formalized.

Conventions: `r` and `s` range over positive integers with `r + s = n` (as in the entry's example
for a(8), which uses the partitions (1,7), (2,6), (3,5), (4,4)); `tau` is the number of divisors,
`(Nat.divisors r).card`. `a n` is the infimum of the set of values `tau(r) + tau(s)`; for `n ≥ 2`
the set is nonempty and finite, so this is its minimum.
-/

namespace OMA.S_oeis_a085887

/-- `a(n)`: the minimum of `tau(r) + tau(s)` over positive `r`, `s` with `r + s = n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {t : ℕ | ∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ r + s = n ∧
    t = (Nat.divisors r).card + (Nat.divisors s).card}

/-- The three claims of the comment, as worded. -/
theorem main :
    (∀ p : ℕ, p.Prime → a (p + 1) = 3) ∧
    (∀ n : ℕ, (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) → a n = 4) ∧
    (∀ n : ℕ, Even n → 4 < n → a n = 4) := by
  sorry

end OMA.S_oeis_a085887
