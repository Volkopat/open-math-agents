import Mathlib

/-!
# A157996: primes of the form `1 + p₁ + p₂` with `p₁, p₂` nonconsecutive primes

Source: https://oeis.org/A157996
Credit: @jagraj28

A157996 lists the primes that are a sum of `1` and two nonconsecutive primes `p₁` and `p₂` with
`p₂ - p₁ > 2`: `11, 17, 19, 23, 29, 31, 37, …` (`11 = 3 + 7 + 1`, `17 = 5 + 11 + 1`). The entry
records:

  Conjecture: for `n > 1`, `a(n) = prime(n + 5)` (Charles R Greathouse IV, 2012).

Since `prime(7) = 17`, the conjecture says that the terms are exactly `11` followed by all primes
`≥ 17`. `main` states this as a characterization: a number `q` is a term if and only if `q = 11`
or `q` is a prime with `q ≥ 17`. (The primes `2, 3, 5, 7, 13` are not terms: a finite check.)
A search over all primes below `300000` confirms the statement.

Conventions.
* "`p₁` and `p₂` are nonconsecutive primes" means that some prime lies strictly between them.
* `p₂ - p₁ > 2` is written `p₁ + 2 < p₂`; in particular `p₁ < p₂`.
* The offset of the entry is `1` (`a(1) = 11`), and `prime(k)` is the `k`-th prime with
  `prime(1) = 2`.
-/

namespace OMA.S_oeis_a157996

/-- `q` is a term of A157996: a prime `1 + p₁ + p₂` with `p₁ < p₂` primes, `p₂ - p₁ > 2`, and
a prime strictly between `p₁` and `p₂`. -/
def IsTerm (q : ℕ) : Prop :=
  q.Prime ∧ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ + 2 < p₂ ∧
    (∃ r : ℕ, r.Prime ∧ p₁ < r ∧ r < p₂) ∧ q = 1 + p₁ + p₂

/-- Conjecture in OEIS A157996: the terms are `11` and all primes `q ≥ 17`. -/
theorem main : ∀ q : ℕ, IsTerm q ↔ (q = 11 ∨ (q.Prime ∧ 17 ≤ q)) := by
  sorry

end OMA.S_oeis_a157996
