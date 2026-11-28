import Mathlib

/-!
# Maximal number of sources of an extensional acyclic digraph

OEIS A182220 asks for the largest possible number of sources on n labeled
vertices. Its equivalent descriptions count nonpowers of two and the possible
heights of binary trees. In the height convention used here, the single-node
tree has height zero.
-/
namespace OMA.S_oeis_a182220

/-- A digraph is represented by the set of out-neighbors of each labeled vertex. -/
abbrev Digraph (N : ℕ) := Fin N → Finset (Fin N)

def acyclic {N : ℕ} (D : Digraph N) :=
  ∀ v, ¬ Relation.TransGen (fun x y => y ∈ D x) v v

def sourceCount {N : ℕ} (D : Digraph N) :=
  (Finset.univ \ Finset.univ.biUnion D).card

/-- Distinct nodes of an extensional digraph have distinct out-neighborhoods. -/
def attainable (N : ℕ) : Set ℕ :=
  {k | ∃ D : Digraph N, Function.Injective D ∧ acyclic D ∧ sourceCount D = k}

def treeHeights (n : ℕ) : Set ℕ :=
  {h | ∃ t : BinaryTree Unit, t.numNodes = n ∧ t.height = h+1}

/-- The source also expresses the same integer by a sum of signs of quotients,
the accumulated lengths of binary expansions, and the positions of repeats. -/
def arithmeticDescriptions (n a : ℕ) : Prop :=
  (0<n → a = n - ∑ i ∈ Finset.Icc 1 (n+1), (if 0<n/2^i then 1 else 0)) ∧
  (0<n → a = (∑ i ∈ Finset.range n, i.size) + 1 -
    (∑ i ∈ Finset.range (n+1), i.log2)) ∧
  (a = (n+1)-(n+1).log2 ↔ ∃ e : ℕ, n+1=2^e)

theorem main : ∀ n : ℕ, let a := if n=0 then 1 else n-n.log2
    IsGreatest (attainable (n+1)) a ∧
    {k : ℕ | k ≤ n ∧ ¬ ∃ e : ℕ, k=2^e}.ncard = a ∧
    arithmeticDescriptions n a ∧
    (0<n → treeHeights n = Set.Icc n.log2 (n-1) ∧ (treeHeights n).ncard = a) := by
  sorry

end OMA.S_oeis_a182220
