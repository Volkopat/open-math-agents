import Mathlib

/-!
# Walecki's theorem for hypergraphs: tight Hamiltonian decompositions of `K_n^(k)`

Source: https://en.wikipedia.org/wiki/Hamiltonian_decomposition#Uniform_Hypergraphs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source question: for integers `n` and `k` where `n` divides `binom(n, k)`, does the complete
`k`-uniform hypergraph `K_n^(k)` admit a tight Hamiltonian decomposition? (Bailey–Stevens 2010.)
The affirmative answer is stated.

Conventions:
* `K_n^(k)` has vertex set `Fin n` and edge set all `k`-element subsets of `Fin n`;
* a tight Hamilton cycle is given by a cyclic ordering of all `n` vertices, i.e. a permutation
  `σ` of `Fin n` read cyclically; its edges are the `n` sets of `k` cyclically consecutive
  vertices `{σ(i), σ(i+1), ..., σ(i+k-1)}` (indices mod `n`);
* a tight Hamiltonian decomposition is a finite family of tight Hamilton cycles such that every
  edge of `K_n^(k)` lies in exactly one cycle of the family (so the cycles are pairwise
  edge-disjoint and cover all edges);
* the range is `1 ≤ k < n`. For `k < n` the `n` windows of a cyclic ordering are distinct
  `k`-sets, so tight Hamilton cycles are genuine `k`-uniform cycles; for `k ≥ n` the windows wrap
  around and the notion degenerates (and `n ∣ binom(n, k)` then forces `n = 1` or the empty
  hypergraph). For `k = 2` this is Walecki's theorem (decomposition of `K_n`, `n` odd, into
  Hamiltonian cycles).
-/

namespace OMA.S_wp_walescki_s_theorem_for_hypergraphs

/-- The window of `k` cyclically consecutive vertices starting at position `i` of the cyclic
ordering `σ` of `Fin n`. -/
def window {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.image fun j : Fin k => σ ⟨(i.val + j.val) % n, Nat.mod_lt _ i.pos⟩

/-- The edge set of the tight Hamilton cycle given by the cyclic ordering `σ`. -/
def tightCycleEdges {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image (window k σ)

theorem main : ∀ n k : ℕ, 1 ≤ k → k < n → n ∣ n.choose k →
    ∃ (m : ℕ) (σ : Fin m → Equiv.Perm (Fin n)),
      ∀ s : Finset (Fin n), s.card = k → ∃! c : Fin m, s ∈ tightCycleEdges k (σ c) := by
  sorry

end OMA.S_wp_walescki_s_theorem_for_hypergraphs
