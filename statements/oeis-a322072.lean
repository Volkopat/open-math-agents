import Mathlib

/-!
# A322072: Row sums of the triangle A322071.

Source: https://oeis.org/A322072
Credit: @cjchaffin

Conjecture (stated on the OEIS page): the difference `a(n + 1) - a(n)` between two consecutive
terms is not a perfect square except for `n = 1`, `5` and `6`.

Conventions:
- The sequence is given by the displayed formula `a(n) = ∑_{k=1..n} floor(2 * n^k / k^k)`,
  with offset 1 (the data, the b-file, and the Maple, Mathematica, PARI, GAP, Magma and Sage
  programs all start at `n = 1`). The Maxima program also lists `n = 0`, where the sum is empty;
  we start at `n ≥ 1` as in the published sequence. (For completeness, `a(1) - a(0) = 2` is not
  a square, so `n = 0` would not be a further exception.)
- "Perfect square" is Mathlib's `IsSquare`. The three listed indices are exactly the values at
  which the difference is a square (`4`, `25` and `36`), so the claim is written as a biconditional.
- For `n ≥ 1` the sequence is strictly increasing (`a(n + 1) - a(n) ≥ 2`), so the difference is
  the natural-number subtraction used below.
-/

namespace OMA.S_oeis_a322072

/-- Row sums of A322071: `a(n) = ∑_{k=1}^{n} floor(2 * n^k / k^k)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, 2 * n ^ k / k ^ k

theorem main : ∀ n : ℕ, 1 ≤ n → (IsSquare (a (n + 1) - a n) ↔ n = 1 ∨ n = 5 ∨ n = 6) := by
  sorry

end OMA.S_oeis_a322072
