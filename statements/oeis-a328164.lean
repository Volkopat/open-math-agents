import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic

/-!
# OEIS A328164

Source: https://oeis.org/A328164 (Gus Wiseman, conjecture by Vaclav Kotesovec)

Sort the partition in descending order before taking adjacent unsigned
differences. The gcd of an empty list is 0, and zero entries do not affect
the gcd. The reference sequence counts all unrestricted partitions.
-/

namespace OMA.S_oeis_a328164

def qualifies {n : ℕ} (p : n.Partition) : Prop :=
  let parts := p.parts.sort (· ≥ ·)
  ((parts.zipWith (· - ·) parts.tail).foldr Nat.gcd 0) =
    ((parts.map (· - 1)).foldr Nat.gcd 0)

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (qualifies (n := n))).card

def p (n : ℕ) : ℕ := Fintype.card n.Partition

theorem main : Asymptotics.IsEquivalent Filter.atTop
    (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => (p n : ℝ)) := by
  sorry

end OMA.S_oeis_a328164
