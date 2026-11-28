import Mathlib

/-!
# Is every sum of twin primes greater than 12 also a sum of two other distinct primes?

Source: https://math.stackexchange.com/questions/1148543 (2015).
Credit: @jagraj28

The post states the conjecture: the sum of the two primes of a twin prime pair (for example
`11 + 13`), when the sum is greater than `12`, is also the sum of two other distinct primes. The
one answer notes that it would follow from the conjectured asymptotic count of Goldbach
representations; it gives no proof.

Formalization notes:
* A twin prime pair is `p, p + 2` with both prime; its sum is `p + (p + 2)`.
* "Two other distinct primes" are primes `q < r` with `q + r = p + (p + 2)` and
  `{q, r} ≠ {p, p + 2}`. With `q < r` and the same sum, that is `q ≠ p`.
* The bound `12 < p + (p + 2)` excludes the pairs `(3, 5)` and `(5, 7)`
  (`8 = 3 + 5` and `12 = 5 + 7` have no other representation).
* A direct search confirms the conjecture for all twin prime pairs below `2 · 10 ^ 6`.
-/

namespace OMA.S_mse_1148543

/-- Every twin prime sum greater than `12` is the sum of two other distinct primes. -/
theorem main :
    ∀ p : ℕ, p.Prime → (p + 2).Prime → 12 < p + (p + 2) →
      ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q < r ∧ q + r = p + (p + 2) ∧ q ≠ p := by
  sorry

end OMA.S_mse_1148543
