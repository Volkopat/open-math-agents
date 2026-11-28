import Mathlib

/-!
# A123375: Least k such that the difference between consecutive semiprimes A065516(k) equals n, or 0 if no such k exists

Source: https://oeis.org/A123375
Credit: @jrflga (agent: Claude Code, model claude-fable-5-2)

OEIS comment: a(n) equals least k such that A065516(k) = n, or 0 if no such k exists.
Conjecture: a(n)>0 exists for all n.

The entry has offset 1 and begins `3, 1, 2, 4, 24, 6, 10, 56, 50, 78, 34, 320, ...`.
A001358 lists the semiprimes (products of two primes), with offset 1: `4, 6, 9, 10, 14, 15, ...`.
A065516 lists the differences between consecutive semiprimes, with offset 1:
`A065516(k) = A001358(k+1) - A001358(k)`, beginning `2, 3, 1, 4, 1, 6, 1, 3, 1, 7, ...`.

## Encoding

* `IsSemiprime m` says that `m` is a product of two primes, not necessarily distinct.
* `semiprime k` is `A001358(k)` for `k ≥ 1`, so `semiprime 1 = 4`, `semiprime 2 = 6`,
  `semiprime 3 = 9`. It is `Nat.nth IsSemiprime (k - 1)`, because `Nat.nth` counts from `0`.
  The value `semiprime 0` is junk and is excluded below by `0 < k`.
* `gap k` is `A065516(k)` for `k ≥ 1`. The semiprimes increase, so the natural-number
  subtraction is exact.
* By its definition, `a(n) > 0` holds exactly when some index `k ≥ 1` has `A065516(k) = n`.
  `main` states this for every `n ≥ 1` (the offset of the entry): every positive integer is the
  difference of two consecutive semiprimes.
-/

namespace OMA.S_oeis_a123375

/-- `m` is a semiprime: a product of two primes, not necessarily distinct. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q

/-- The `k`-th semiprime, `A001358(k)`, for `k ≥ 1`. -/
noncomputable def semiprime (k : ℕ) : ℕ :=
  Nat.nth IsSemiprime (k - 1)

/-- The difference between the `(k+1)`-th and the `k`-th semiprime, `A065516(k)`, for `k ≥ 1`. -/
noncomputable def gap (k : ℕ) : ℕ :=
  semiprime (k + 1) - semiprime k

theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ gap k = n := by
  sorry

end OMA.S_oeis_a123375
