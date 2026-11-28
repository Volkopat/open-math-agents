import Mathlib

/-!
# A395726: Array read by ascending antidiagonals: A(n, k) = A(n, k-A002024(k)) + A002024(k) * A(n-1, k) with A(n, 0) = 0^n, A(0, k) = 1.

Source: https://oeis.org/A395726
Credit: @cj-55m (agent: Claude Code, model claude-fable-5-2)

The entry (offset 0; the array starts
  [0] 1, 1, 1, 1, 1, 1, 1, ...
  [1] 0, 1, 2, 3, 4, 5, 6, ...
  [2] 0, 1, 4, 7, 13, 19, 25, ...
  [3] 0, 1, 8, 15, 40, 65, 90, ...)
records in its FORMULA section:

  Conjecture 3: A(n, k) = Sum_{j=1..k} Stirling2(n + f(j) - 1, f(j)) for n > 0.

where, as stated in Conjecture 1 of the same entry, f(n) = A002024(n).

Conventions:
* `f k` is A002024(k) (offset 1: `k` appears `k` times, 1, 2, 2, 3, 3, 3, 4, ...), computed for
  `k ≥ 1` by the formula of the entry's PARI program, `A002024(n) = (sqrtint(8*n-7)+1)\2`.
  The value `f 0 = 0` (truncated subtraction) is never used.
* `A n k` is the array of the entry, rows `n ≥ 0` and columns `k ≥ 0`, defined by the rules of
  the NAME: `A(0, k) = 1`, `A(n, 0) = 0^n` (so `A(n, 0) = 0` for `n ≥ 1`), and
  `A(n, k) = A(n, k - f(k)) + f(k) * A(n-1, k)` for `n ≥ 1`, `k ≥ 1`. The recursion is
  well-founded because `1 ≤ f(k) ≤ k` for `k ≥ 1`.
* `Stirling2` is the Stirling number of the second kind, `Nat.stirlingSecond` in Mathlib.
  In the exponent `n + f(j) - 1` the subtraction is harmless since `n > 0`.
* The statement is Conjecture 3 for all `n > 0` and all `k ≥ 0` (for `k = 0` the sum is empty and
  `A(n, 0) = 0`). Conjectures 1 and 2 of the entry are not part of this statement.
-/

namespace OMA.S_oeis_a395726

/-- A002024 (`k` appears `k` times), for `k ≥ 1`: `(sqrtint(8*k-7)+1)\2`. -/
def f (k : ℕ) : ℕ := (Nat.sqrt (8 * k - 7) + 1) / 2

/-- The array A395726: `A(0, k) = 1`, `A(n, 0) = 0^n`, and
`A(n, k) = A(n, k - f(k)) + f(k) * A(n-1, k)` for `n, k ≥ 1`. -/
def A : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n + 1, k + 1 => A (n + 1) (k + 1 - f (k + 1)) + f (k + 1) * A n (k + 1)
termination_by n k => (n, k)
decreasing_by
  · apply Prod.Lex.right
    have h : 1 ≤ Nat.sqrt (8 * (k + 1) - 7) := Nat.le_sqrt.mpr (by omega)
    have h2 : 1 ≤ f (k + 1) := by
      unfold f
      omega
    omega
  · apply Prod.Lex.left
    omega

/-- Conjecture 3 of A395726: `A(n, k) = Sum_{j=1..k} Stirling2(n + f(j) - 1, f(j))` for `n > 0`. -/
theorem main : ∀ n k : ℕ, 0 < n →
    A n k = ∑ j ∈ Finset.Icc 1 k, Nat.stirlingSecond (n + f j - 1) (f j) := by
  sorry

end OMA.S_oeis_a395726
