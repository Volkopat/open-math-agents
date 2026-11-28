import Mathlib

/-!
# OEIS A005121: ultradissimilarity relations, a triangle recurrence

Source: https://oeis.org/A005121
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ultradissimilarity relations on an `n`-set (equivalently, maximal chains
in the lattice of set partitions of an `n`-set): `1, 1, 4, 32, 436, …` (offset 1). Conjecture
(Mohapatra, 2026): `a(n) = R(n, n)`, where `R(1, 1) = 1`,
`R(n, k) = k ∑_{j=k}^{n-1} R(n-1, j)` for `1 ≤ k < n`, and `R(n, n) = ∑_{j=1}^{n-1} R(n, j)`.

Conventions:
* `a` is given by Lengyel's recurrence quoted in the entry, `a(1) = 1`,
  `a(n) = ∑_{k=1}^{n-1} S(n, k) a(k)` for `n ≥ 2` (`S` = Stirling numbers of the second kind);
  `a 0 = 0` is unused.
* `R n k` is `0` outside `1 ≤ k ≤ n`. `main` is stated for `n ≥ 1`.
-/

namespace OMA.S_oeis_a005121

/-- Ultradissimilarity counts via Lengyel's recurrence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ k : Fin (n + 2), if (k : ℕ) = 0 then 0 else Nat.stirlingSecond (n + 2) k * a k
decreasing_by exact k.isLt

/-- The triangle `R(n, k)` of the conjecture. -/
def R : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, k => if k = 1 then 1 else 0
  | n + 2, k =>
    if 1 ≤ k ∧ k < n + 2 then k * ∑ j ∈ Finset.Icc k (n + 1), R (n + 1) j
    else if k = n + 2 then
      ∑ i ∈ Finset.Icc 1 (n + 1), i * ∑ j ∈ Finset.Icc i (n + 1), R (n + 1) j
    else 0

/-- `a(n) = R(n, n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = R n n := by
  sorry

end OMA.S_oeis_a005121
