import Mathlib

/-!
# A349890: the triangle T(n, k) yields a permutation of the positive integers

Source: https://oeis.org/A349890
Credit: @avivorly

Definition (the entry's name, verbatim): Triangle read by rows: T(n,k) = n * 2^e(n) - (4^e(n) - 1) / 3 - k * (k - 1) / 2
with e(n) = 1 + floor(log_2(n)) for n >= 1 and 1 <= k <= n.

Conjecture (Werner Schulte, in the entry, verbatim): Conjecture: The terms of the triangle yield a permutation of the
positive integers (A000027).

Conventions:
- `e n = 1 + Nat.log 2 n`; for `n ≥ 1`, `Nat.log 2 n` is `floor(log_2(n))`.
- `T n k` is computed in `ℤ`, so no subtraction truncates. Both divisions are exact and are written with the integer
  division `/` of `ℤ`: `4 ^ e - 1` is divisible by `3`, and `k * (k - 1)` is even.
- The positions of the triangle are the pairs `(n, k)` with `1 ≤ k ≤ n`. That the terms of the triangle yield a
  permutation of the positive integers is read as: the map `(n, k) ↦ T n k` is a bijection from these positions onto
  the positive integers `{x : ℤ | 1 ≤ x}`, that is, every term is positive, distinct positions carry distinct terms,
  and every positive integer occurs as a term.
-/

namespace OMA.S_oeis_a349890

/-- `e n = 1 + floor(log_2 n)` (for `n ≥ 1`). -/
def e (n : ℕ) : ℕ := 1 + Nat.log 2 n

/-- The term `T(n, k) = n * 2^e(n) - (4^e(n) - 1) / 3 - k * (k - 1) / 2` of the triangle, computed in `ℤ`. -/
def T (n k : ℕ) : ℤ := (n : ℤ) * 2 ^ e n - (4 ^ e n - 1) / 3 - (k : ℤ) * ((k : ℤ) - 1) / 2

theorem main :
    Set.BijOn (fun p : ℕ × ℕ => T p.1 p.2) {p : ℕ × ℕ | 1 ≤ p.2 ∧ p.2 ≤ p.1} {x : ℤ | 1 ≤ x} := by
  sorry

end OMA.S_oeis_a349890
