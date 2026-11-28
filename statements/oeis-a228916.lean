import Mathlib

/-!
# A228916: Indices of primes in sequence A108300.

Source: https://oeis.org/A228916
Credit: @avivorly

A108300 (offset 0): `u(0) = 1`, `u(1) = 5`, `u(n) = 3 u(n-1) + u(n-2)`: 1, 5, 16, 53, 175, 578, 1909, ...
A228916 (offset 1) lists, in increasing order, the indices `m` such that `u(m)` is prime:
1, 3, 9, 15, 39, 225, 231, 363, 687, ...

Conjecture (Vaclav Kotesovec, Sep 08 2013): for `n > 1`, `a(n)` is a multiple of 3.

Conventions:
- `u` is A108300 with its OEIS offset 0. The entry's program searches the indices `m ≥ 1`; the index
  `m = 0` never qualifies anyway, since `u(0) = 1` is not prime.
- `a n` is the `n`-th such index (offset 1), that is `Nat.nth` (counted from 0) at `n - 1` of the set
  of indices `m` with `u m` prime. If that set had fewer than `n` elements, `Nat.nth` would return 0
  (a multiple of 3), so the statement only constrains the terms that exist, as in the entry.
-/

namespace OMA.S_oeis_a228916

/-- A108300: `u 0 = 1`, `u 1 = 5`, `u (n + 2) = 3 * u (n + 1) + u n`. -/
def u : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 3 * u (n + 1) + u n

/-- A228916 (offset 1): the `n`-th index `m`, in increasing order, such that `u m` is prime. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => (u m).Prime) (n - 1)

theorem main : ∀ n : ℕ, 1 < n → 3 ∣ a n := by
  sorry

end OMA.S_oeis_a228916
