import Mathlib

/-!
# A082090: Length of iteration sequence if function A056239, a pseudo-logarithm is iterated and started at n. Fixed point equals zero for all initial values.

Source: https://oeis.org/A082090
Credit: @esracummings31-blip

Conjecture (Gus Wiseman, Dec 01 2023), second item: the position of last appearance of `k`
is `n = A014221(k-2) = 2^^(k-2)`.

This file states only that item (the other two items, first appearance at A007097(k-2) and
the counts 1, 1, 2, 8, 435, ..., are not stated here).

Conventions.
* A056239(n) is the sum of the prime indices of `n` with multiplicity: the prime index of the
  prime `p` is `π(p)` (so `2 ↦ 1`, `3 ↦ 2`, `5 ↦ 3`, ...), and A056239(1) = 0.
* A082090(n) counts the terms of `n, f(n), f(f(n)), ..., 0` with `f = A056239`, the iteration
  stopping at the first `0` (OEIS example: `127, 31, 11, 5, 3, 2, 1, 0` gives 8). Since
  `f(m) < m` for `m ≥ 1`, `n + 1` steps of fuel always suffice; `lenFuel` implements this.
* `tower j = 2^^j` with `2^^0 = 1`, `2^^(j+1) = 2^(2^^j)` (A014221).
* Offset: A082090 starts at `n = 1`; "position of last appearance of `k`" means
  `A082090 (2^^(k-2)) = k` and no `n > 2^^(k-2)` has `A082090 n = k`, for every `k ≥ 2`.
-/

namespace OMA.S_oeis_a082090

/-- A056239: sum of prime indices of `n`, with multiplicity. -/
def A056239 (n : ℕ) : ℕ := (n.primeFactorsList.map Nat.primeCounting).sum

/-- Number of terms of the iteration `m, f m, f (f m), ...` up to and including the first `0`,
computed with `fuel` steps. -/
def lenFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => if m = 0 then 1 else 1 + lenFuel fuel (A056239 m)

/-- A082090(n). -/
def A082090 (n : ℕ) : ℕ := lenFuel (n + 1) n

/-- A014221: `2^^j`. -/
def tower : ℕ → ℕ
  | 0 => 1
  | j + 1 => 2 ^ tower j

theorem main : ∀ k : ℕ, 2 ≤ k →
    A082090 (tower (k - 2)) = k ∧ ∀ n : ℕ, 1 ≤ n → A082090 n = k → n ≤ tower (k - 2) := by
  sorry

end OMA.S_oeis_a082090
