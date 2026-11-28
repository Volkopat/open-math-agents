import Mathlib

/-!
# A305502: n = x + y with 0 < x ≤ y such that x^3 + n*y^2 is prime

Source: https://oeis.org/A305502

A305502 (offset 1): `a(n)` is the number of ways to write `n` as `x + y` with `0 < x ≤ y` such
that `x^3 + n*y^2` is prime: 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, …  For example `a(3) = 1`
since `3 = 1 + 2` with `1^3 + 3*2^2 = 13` prime.

Conjecture (Zhi-Wei Sun, Jun 03 2018): `a(n) > 0` for all `n > 1`, and `a(n) = 1` only for
`n = 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 16, 20, 22, 28, 42, 50`. The entry notes that `a(n) > 0`
has been verified for all `n = 2..10^7`.

Both clauses are stated, as a conjunction. The second clause is given as an equivalence:
`a(n) = 1` if and only if `n` is one of the sixteen listed values. (That `a(n) = 1` at the listed
values is a finite computation; the open content is that there are no others.)

Conventions: `a n` is the cardinality (`Set.ncard`) of the finite set of `x` with `0 < x`,
`x ≤ n - x` and `x^3 + n*(n-x)^2` prime, where `y = n - x`; the condition `x ≤ n - x` in `ℕ`
forces `x ≤ n`, so the subtraction is exact. Indexing is the OEIS one (offset 1).
-/

namespace OMA.S_oeis_a305502

/-- A305502: the number of `0 < x ≤ y` with `x + y = n` and `x^3 + n*y^2` prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : ℕ | 0 < x ∧ x ≤ n - x ∧ Nat.Prime (x ^ 3 + n * (n - x) ^ 2)}.ncard

theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔
      n ∈ ({2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 16, 20, 22, 28, 42, 50} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a305502
