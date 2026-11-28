import Mathlib

/-!
# A279756: smallest prime p ≥ prime(n) with p ≡ 2 (mod prime(n))

Source: https://oeis.org/A279756

A279756 (offset 1): `a(n)` is the smallest prime `p ≥ prime(n)` such that `p ≡ 2 (mod prime(n))`:
2, 5, 7, 23, 13, 41, 19, 59, 71, 31, …

Conjecture (Thomas Ordowski and Altug Alkan, Dec 18 2016): `a(n) < prime(n)^2` for every `n`.

Since `a(n)` is the smallest prime `p ≥ prime(n)` with `p ≡ 2 (mod prime(n))`, the bound
`a(n) < prime(n)^2` holds exactly when some such prime is smaller than `prime(n)^2`, and the
conjecture is stated in that form. Quantifying over all `n ≥ 1` is the same as quantifying over
all primes `q = prime(n)`, which is how the statement is written.

Conventions: everything is in `ℕ`, and the congruence is `Nat.ModEq`. For `q = 2` the condition
`p ≡ 2 (mod 2)` says that `p` is even, and `a(1) = 2`.
-/

namespace OMA.S_oeis_a279756

theorem main :
    ∀ q : ℕ, Nat.Prime q → ∃ p : ℕ, Nat.Prime p ∧ q ≤ p ∧ p ≡ 2 [MOD q] ∧ p < q ^ 2 := by
  sorry

end OMA.S_oeis_a279756
