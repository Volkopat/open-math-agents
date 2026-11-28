import Mathlib

/-!
# A349537: least m making 33*k^2*(k^3+1), k = 1..n, pairwise distinct modulo m

Source: https://oeis.org/A349537

A349537 (offset 1): `a(n)` is the least positive integer `m` such that the `n` numbers
`33*k^2*(k^3+1)` (`k = 1..n`) are pairwise distinct modulo `m`:
1, 4, 7, 7, 13, 13, 13, 13, 13, 31, 41, 41, 61, …  For example `a(2) = 4` since `66` and `1188`
are incongruent modulo 4, but congruent modulo each of 1, 2 and 3.

Conjecture (Zhi-Wei Sun, Nov 21 2021): `a(n)` is prime for each `n > 2`. The entry notes that
this has been verified for `n` up to `10^4`.

Conventions:
- `IsAdmissible n m` says that `m` is positive and the numbers `33*k^2*(k^3+1)` for
  `1 ≤ k ≤ n` are pairwise incongruent modulo `m`.
- `a(n)` is the least admissible `m`. The statement is: for every `n > 2`, any `m` that is the
  least element (`IsLeast`) of the set of admissible moduli is prime. (Admissible moduli exist,
  for example any `m` larger than all the `n` numbers.)
-/

namespace OMA.S_oeis_a349537

/-- The numbers `33*k^2*(k^3+1)`, `1 ≤ k ≤ n`, are pairwise distinct modulo the positive
integer `m`. -/
def IsAdmissible (n m : ℕ) : Prop :=
  0 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n →
    ¬ (33 * i ^ 2 * (i ^ 3 + 1) ≡ 33 * j ^ 2 * (j ^ 3 + 1) [MOD m])

theorem main :
    ∀ n m : ℕ, 2 < n → IsLeast {m : ℕ | IsAdmissible n m} m → Nat.Prime m := by
  sorry

end OMA.S_oeis_a349537
