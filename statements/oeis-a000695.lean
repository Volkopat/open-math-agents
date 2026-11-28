import Mathlib

/-!
# Rooted-tree construction for A000695

Source: https://oeis.org/A000695
Credit: @kyka776

The even step below applies to the leaves specified in John Tyler Rascoe's comment.
The linked illustration fills spare child positions at a vertex that already has
one child at stage four. The written leaf rule gives 14 nodes there for `k = 4`,
and the illustration shows 16. See https://oeis.org/A000695/a000695.jpg.
-/

namespace OMA.S_oeis_a000695

/-- The node count and the leaf counts by depth, listed from greatest depth to
the root. The initial tree consists of a single root. -/
def leafGrowth (k : ℕ) : ℕ → ℕ × List ℕ
  | 0 => (0, [])
  | 1 => (1, [1])
  | n + 2 =>
      let (count, leaves) := leafGrowth k (n + 1)
      if (n + 2) % 2 = 1 then
        (count + 1, 1 :: (leaves.headD 0 - 1) :: leaves.tail)
      else
        -- The cutoff depth is `n + 2 - 2 ^ v₂(n + 2)`.
        let width := 2 ^ (n + 2).factorization 2 - 1
        let eligible := leaves.take width
        (count + (k - 1) * eligible.sum,
          eligible.map (fun x => (k - 1) * x) ++ [0] ++ leaves.drop width)

/-- Rebase the binary digits of the index in base `k`. -/
theorem main : ∀ (k : ℕ), 2 < k → ∀ n : ℕ,
    (leafGrowth k n).1 = Nat.ofDigits k (Nat.digits 2 n) := by
  sorry

end OMA.S_oeis_a000695

