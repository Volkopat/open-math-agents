import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Logic.Function.Iterate

/-!
# The least positive integer supporting a given partition depth

Source: Clark Kimberling, OEIS A237685 (February 2014), CC BY-SA 4.0.
https://oeis.org/A237685
The same conjecture occurs in A237750, A237978 and A366063. The sequence and
its original enumeration start at n=1. At each step all copies of the same
part x are replaced simultaneously by their sum. Depth is the first step
where the multiset of parts has no repetitions.
-/

namespace OMA.S_oeis_a237685

def mergeParts (p : Multiset ℕ) : Multiset ℕ :=
  p.dedup.map (fun x => p.count x * x)

def hasDepth (p : Multiset ℕ) (d : ℕ) : Prop :=
  (mergeParts^[d] p).Nodup ∧ ∀ i < d, ¬ (mergeParts^[i] p).Nodup

theorem main : ∀ d : ℕ,
    IsLeast {n : ℕ | 0 < n ∧ ∃ p : Nat.Partition n, hasDepth p.parts d} (2^d) := by
  sorry

end OMA.S_oeis_a237685
