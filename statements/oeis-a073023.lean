import Mathlib

/-!
# A073023: Number of solutions to the equation n^x==1 (mod x), 1<=x<=n.

Source: https://oeis.org/A073023
Credit: @eltociear

`a(n)` is the number of `x` with `1 ≤ x ≤ n` and `n^x ≡ 1 (mod x)` (offset 1; `x = 1` always
counts, since every integer is congruent to `1` modulo `1`). The entry's formula section records
the conjecture

  for `n > 100`, `Sum_{k=1..n} a(k) > n^(3/2)`.

`main` states it with the real power `n ^ (3/2 : ℝ)`.

Remark for reviewers and provers (not part of the statement): computing `a(k)` directly (it
matches the entry's data section) gives `Sum_{k=1..102} a(k) = 1025 < 102^(3/2) ≈ 1030.15`, and
the inequality also fails at `n = 105, 106, 108`. It holds for all other `n` with
`100 < n ≤ 4000`. So the conjecture as printed appears to be false, and `¬ main` should be
provable by computation at `n = 102`.
-/

namespace OMA.S_oeis_a073023

/-- OEIS A073023: the number of `x ∈ [1, n]` with `n ^ x ≡ 1 [MOD x]`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun x => n ^ x ≡ 1 [MOD x])).card

/-- The conjecture in OEIS A073023: for `n > 100`, `∑_{k=1}^n a(k) > n^(3/2)`. -/
theorem main : ∀ n : ℕ, 100 < n →
    (n : ℝ) ^ ((3 : ℝ) / 2) < ((∑ k ∈ Finset.Icc 1 n, a k : ℕ) : ℝ) := by
  sorry

end OMA.S_oeis_a073023
-- ci: re-run check-proof
