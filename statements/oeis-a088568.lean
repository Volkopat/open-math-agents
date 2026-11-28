import Mathlib

/-!
# A088568: 3*n - 2*(partial sums of Kolakoski sequence A000002)

Source: https://oeis.org/A088568
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

It is conjectured that a(n) = o(n), equivalently that the density of 1's and
that of 2's in the Kolakoski sequence A000002 are both equal to 1/2.
-/

namespace OMA.S_oeis_a088568

/-- Predicate characterizing the 0-indexed Kolakoski sequence K : ℕ → ℕ
(starting 1, 2, 2, 1, 1, 2, 1, 2, 2, ...): every term is 1 or 2, K 0 = 1,
and the k-th run has length K k and consists of 1 if k is even and 2 if k is odd. -/
def IsKolakoski (K : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, K n = 1 ∨ K n = 2) ∧
  K 0 = 1 ∧
  ∀ k j : ℕ, j < K k →
    K ((∑ i ∈ Finset.range k, K i) + j) = if k % 2 = 0 then 1 else 2

/-- a(n) = 3 * n - 2 * ∑_{i < n} K(i). -/
def a (K : ℕ → ℕ) (n : ℕ) : ℤ :=
  3 * (n : ℤ) - 2 * ∑ i ∈ Finset.range n, (K i : ℤ)

theorem main :
    ∀ K : ℕ → ℕ, IsKolakoski K →
      Filter.Tendsto (fun n : ℕ => (a K n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a088568
