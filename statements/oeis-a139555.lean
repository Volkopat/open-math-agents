import Mathlib

/-!
# A139555: prime powers up to n that are coprime to n, compared with phi(n)

Source: https://oeis.org/A139555

A139555 (offset 1): `a(n)` is the number of prime powers (including 1) that are `≤ n` and
coprime to `n`: 1, 1, 2, 2, 4, 2, 5, 4, 6, 4, 8, 4, 9, 6, 7, 7, …  For example `a(21) = 10`,
from 1, 2, 4, 5, 8, 11, 13, 16, 17, 19.

Conjecture (Reinhard Zumkeller, Oct 27 2010): `a(n) < A000010(n)` for `n > 60`, where A000010 is
Euler's totient function. (The entry notes `a(n) ≤ A000010(n)` for all `n`, with equality at the
17 terms of A051250, the largest of which is 60.)

Conventions:
- Prime powers are `p^k` with `p` prime and `k ≥ 1` (Mathlib's `IsPrimePow`), together with `1`,
  which the entry includes explicitly.
- `a n` is the cardinality (`Set.ncard`) of the finite set of `k` with `1 ≤ k ≤ n`, `k` coprime
  to `n`, and `k = 1` or `k` a prime power. Indexing is the OEIS one (offset 1).
- A000010 is `Nat.totient`.
-/

namespace OMA.S_oeis_a139555

/-- A139555: the number of `1 ≤ k ≤ n` coprime to `n` that are `1` or a prime power. -/
noncomputable def a (n : ℕ) : ℕ :=
  {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ Nat.Coprime k n ∧ (k = 1 ∨ IsPrimePow k)}.ncard

theorem main : ∀ n : ℕ, 60 < n → a n < Nat.totient n := by
  sorry

end OMA.S_oeis_a139555
