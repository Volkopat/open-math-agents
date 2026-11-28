import Mathlib

/-!
# A057194: a(1) = 1; a(n+1) = (Product_{k=1..n} a(k)) * Sum_{k=1..n} a(k)

Source: https://oeis.org/A057194
Credit: @xor2k

Formalizes the OEIS A057194 conjecture (Jon Perry, Sep 12 2012):
Conjecture: a(n) < A216151(n) for all n > 1.

Conventions:
* `a` is A057194 with offset 1: `a 1 = 1` and, for `n ≥ 1`,
  `a (n + 1) = (∏_{k=1..n} a k) * ∑_{k=1..n} a k`; the product and sum over `k = 1..n` are written as
  products and sums over `k : Fin n` of `a (k + 1)`. The value `a 0 = 0` is a placeholder outside
  the offset and is never used by the recurrence.
* `b` is A216151 with offset 1: `b 1 = 1`, `b 2 = 2` and, for `n ≥ 2`,
  `b (n + 1) = (∏_{k=1..n} b k) * ∑_{k=1..n} b k`; again `b 0 = 0` is an unused placeholder.
* The claim is stated for every natural number `n > 1`, as in the entry.
-/

namespace OMA.S_oeis_a057194

/-- A057194 (offset 1): `a 1 = 1`, `a (n + 1) = (∏_{k=1..n} a k) * ∑_{k=1..n} a k` for `n ≥ 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (∏ k : Fin (n + 1), a (k + 1)) * ∑ k : Fin (n + 1), a (k + 1)

/-- A216151 (offset 1): `b 1 = 1`, `b 2 = 2`, `b (n + 1) = (∏_{k=1..n} b k) * ∑_{k=1..n} b k`
for `n ≥ 2`. -/
def b : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => (∏ k : Fin (n + 2), b (k + 1)) * ∑ k : Fin (n + 2), b (k + 1)

/-- For all `n > 1`, A057194(n) < A216151(n). -/
theorem main : ∀ n : ℕ, 1 < n → a n < b n := by
  sorry

end OMA.S_oeis_a057194
