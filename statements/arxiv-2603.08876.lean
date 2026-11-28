import Mathlib

/-!
# Isolated cuts are globally optimal for geometric Max-Cut weights

Nevena Marić, Hierarchical threshold structure in Max-Cut with geometric edge weights,
https://arxiv.org/abs/2603.08876, abstract and Conjecture 5.1, with Definitions 2.1 and 2.3.
Credit: @pyaf

The vertices of K_n are 0, …, n-1 and the edges (i, j), i < j, are ordered lexicographically.
The i-th of the N = n(n-1)/2 edges has weight r^(N-i), i.e. r raised to the number of edges
after it. The cut of S ⊆ [n] consists of the edges with exactly one end in S. The k-isolated
cut is {0, …, k-1} | {k, …, n-1}; the paper's isolated cuts are those with 1 ≤ k ≤ ⌊n/2⌋.
By Theorem 4.10 of the paper this is equivalent to Conjecture 5.1 on every threshold interval.
-/

namespace OMA.S_arxiv_2603_08876

open Finset

def edges (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun e => e.1 < e.2

def laterEdges (n : ℕ) (e : Fin n × Fin n) : ℕ :=
  ((edges n).filter fun f => e.1 < f.1 ∨ (e.1 = f.1 ∧ e.2 < f.2)).card

noncomputable def cutWeight (n : ℕ) (r : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ (edges n).filter (fun e => (e.1 ∈ S ↔ e.2 ∉ S)), r ^ laterEdges n e

def isolatedCut (n k : ℕ) : Finset (Fin n) := univ.filter fun i => i.val < k

theorem main :
    ∀ n : ℕ, 7 ≤ n → ∀ r : ℝ, 1 < r → r < 2 →
      ∃ k, 1 ≤ k ∧ k ≤ n / 2 ∧
        ∀ S : Finset (Fin n), cutWeight n r S ≤ cutWeight n r (isolatedCut n k) := by
  sorry

end OMA.S_arxiv_2603_08876
