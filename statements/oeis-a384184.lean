import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.OrderOfElement

/-!
# OEIS A384184

Mia Boudreau's conjecture on the order of successive swaps, https://oeis.org/A384184 .
The positions are numbered from zero. The fold processes the positions in increasing
order and records the final position of each token.
-/

namespace OMA.S_oeis_a384184

/-- At step i, swap the positions i and 2i modulo the size of the permutation. -/
def shuffle (size : ℕ) : Equiv.Perm (Fin size) :=
  (List.finRange size).foldl
    (fun perm i => perm.trans (Equiv.swap i (i + i))) (Equiv.refl _)

/-- The order for the sum of two distinct powers of 2. -/
theorem main : ∀ n x : ℕ, n < x →
    orderOf (shuffle (2 ^ n + 2 ^ x)) = 2 ^ n * (x - n) := by
  sorry

end OMA.S_oeis_a384184
