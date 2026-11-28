import Mathlib

/-!
# A113547: labeled set partitions of n by maximin
Source: https://oeis.org/A113547 (R. J. Mathar, Mar 13 2016)

T(n,m) (n >= 1, 1 <= m <= n) is the number of set partitions of {1,...,n} with maximin m, where the
maximin of a partition is the maximum over all blocks of the least element of the block.

Encoding of set partitions. A set partition of {1,...,n} is encoded, as usual, by the list l of
length n whose entry at position i (0-based, i.e. for the element i+1) is the index of the block
containing i+1, the blocks being numbered 1, 2, 3, ... in increasing order of their least elements.
These lists are exactly the restricted growth functions (RGFs): l[0] = 1 and
1 <= l[i] <= 1 + max(l[0..i-1]); the encoding is a bijection between set partitions of {1,...,n}
and RGFs of length n (every entry is at most n). The block containing the element i+1 is the set
of positions carrying the value l[i], so its least element is idxOf(l[i]) + 1, and the maximin of
the partition is the maximum of these values over all elements.

Conjectures (both formalized):
* T(n,3) = A007689(n-3) for n >= 3, where A007689(k) = 2^k + 3^k;
* T(n,4) = 2^(n-4) + 3^(n-3) + 4^(n-4) for n >= 4.
-/

namespace OMA.S_oeis_a113547

/-- The restricted growth condition. -/
def IsRGF (l : List ℕ) : Prop :=
  ∀ i : Fin l.length, 1 ≤ l[i] ∧ l[i] ≤ (l.take i).foldr max 0 + 1

instance (l : List ℕ) : Decidable (IsRGF l) := by unfold IsRGF; infer_instance

/-- Encodings of the set partitions of {1,...,n}. -/
def rgfs (n : ℕ) : Finset (List ℕ) :=
  ((Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).image fun f => List.ofFn f).filter IsRGF

/-- The maximin: the maximum over all elements of the least element of their block. -/
def maximin (l : List ℕ) : ℕ :=
  ((List.range l.length).map fun i => l.idxOf (l.getD i 0) + 1).foldr max 0

/-- T(n,m). -/
def T (n m : ℕ) : ℕ := ((rgfs n).filter fun l => maximin l = m).card

/-- A007689(k) = 2^k + 3^k. -/
def A007689 (k : ℕ) : ℕ := 2 ^ k + 3 ^ k

theorem main :
    (∀ n : ℕ, 3 ≤ n → T n 3 = A007689 (n - 3)) ∧
    (∀ n : ℕ, 4 ≤ n → T n 4 = 2 ^ (n - 4) + 3 ^ (n - 3) + 4 ^ (n - 4)) := by
  sorry

end OMA.S_oeis_a113547
