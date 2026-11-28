import Mathlib

/-!
# A216151: a(n+1) = (Product_{k=1..n} a(k)) * Sum_{k=1..n} a(k), a(1)=1, a(2)=2

Source: https://oeis.org/A216151
Credit: @xor2k

Formalizes the OEIS A216151 conjecture:
Conjecture: a(n) > A057194(n) for all n > 1.

Conventions:
* `a` is A216151 with offset 1: `a 1 = 1`, `a 2 = 2` and, for `n ≥ 2`,
  `a (n + 1) = (∏_{k=1..n} a k) * ∑_{k=1..n} a k`; the product and sum over `k = 1..n` are written as
  products and sums over `k : Fin n` of `a (k + 1)`. The value `a 0 = 0` is a placeholder outside
  the offset and is never used by the recurrence.
* `b` is A057194 with offset 1: `b 1 = 1` and, for `n ≥ 1`,
  `b (n + 1) = (∏_{k=1..n} b k) * ∑_{k=1..n} b k`; again `b 0 = 0` is an unused placeholder.
* The claim is stated for every natural number `n > 1`, as in the entry.
-/

namespace OMA.S_oeis_a216151

/-- A216151 (offset 1): `a 1 = 1`, `a 2 = 2`, `a (n + 1) = (∏_{k=1..n} a k) * ∑_{k=1..n} a k`
for `n ≥ 2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => (∏ k : Fin (n + 2), a (k + 1)) * ∑ k : Fin (n + 2), a (k + 1)

/-- A057194 (offset 1): `b 1 = 1`, `b (n + 1) = (∏_{k=1..n} b k) * ∑_{k=1..n} b k` for `n ≥ 1`. -/
def b : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (∏ k : Fin (n + 1), b (k + 1)) * ∑ k : Fin (n + 1), b (k + 1)

/-- For all `n > 1`, A216151(n) > A057194(n). -/
theorem main : ∀ n : ℕ, 1 < n → a n > b n := by
  sorry

end OMA.S_oeis_a216151
