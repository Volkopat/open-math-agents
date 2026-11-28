import Mathlib

/-!
# The reverse-reply strategy wins the permutation avoidance game for large n

Henning Ulfarsson, "A Permutation Avoidance Game with Reverse Replies and Monotone Traps",
arXiv:2603.16004, Conjecture 2.9.
Source: https://arxiv.org/abs/2603.16004

The game PAP with pattern length k (Definition 1.1) starts from Sₙ. A position is the set
Avₙ(F) of permutations of length n avoiding every pattern already chosen; a move chooses a pattern
p ∈ Sₖ contained in at least one permutation of the current position, and adds it to F. Normal
play: a player with no legal move loses. In the reverse strategy, Player II answers each move p
of Player I by the reverse pattern pʳ = p(k)⋯p(1). Conjecture 2.9: for every k ≥ 3 there is
n₀(k) such that the reverse strategy is a winning strategy for Player II on Sₙ for all n ≥ n₀(k).

`ReverseWins n k F` says that from the position with chosen set F and Player I to move, every
legal move p of Player I leaves the reverse pʳ legal, and the reverse strategy again wins after
both moves. It is an inductive predicate, so it holds exactly when every play following the
strategy ends with Player I unable to move (a legal pattern never lies in F, so each round
enlarges F and plays are finite). The paper proves the conjecture's conclusion for k = 3, n ≥ 3
(Theorem 2.5) and for k = 4, n ≥ 10, and reports that the strategy fails for k = 4,
5 ≤ n ≤ 9 (Proposition 2.7).

Sanity check: an independent brute-force implementation of this predicate reproduces the paper's
data (k = 3, 3 ≤ n ≤ 6 wins; k = 4: wins at n = 4, fails at n = 5, 6, 7, 8). Literature
searches found no proof for k ≥ 5.
-/

namespace OMA.S_arxiv_2603_16004

/-- The permutation `π` of length `n` contains the pattern `p` of length `k`. -/
def Contains {n k : ℕ} (π : Equiv.Perm (Fin n)) (p : Equiv.Perm (Fin k)) : Prop :=
  ∃ positions : Fin k → Fin n, StrictMono positions ∧
    ∀ i j, π (positions i) < π (positions j) ↔ p i < p j

/-- Choosing `p` is legal after the patterns `F` were chosen: some permutation of length `n`
avoiding all of `F` contains `p`. -/
def Legal (n : ℕ) {k : ℕ} (F : Finset (Equiv.Perm (Fin k))) (p : Equiv.Perm (Fin k)) : Prop :=
  ∃ π : Equiv.Perm (Fin n), (∀ q ∈ F, ¬ Contains π q) ∧ Contains π p

/-- The reverse `p(k)⋯p(1)` of the pattern `p`. -/
def reverse {k : ℕ} (p : Equiv.Perm (Fin k)) : Equiv.Perm (Fin k) :=
  Fin.revPerm.trans p

/-- The reverse strategy wins for Player II from the position with chosen patterns `F`,
Player I to move. -/
inductive ReverseWins (n : ℕ) {k : ℕ} : Finset (Equiv.Perm (Fin k)) → Prop
  | intro (F : Finset (Equiv.Perm (Fin k))) :
      (∀ p, Legal n F p → Legal n (insert p F) (reverse p)) →
      (∀ p, Legal n F p → ReverseWins n (insert (reverse p) (insert p F))) →
      ReverseWins n F

theorem main : ∀ k : ℕ, 3 ≤ k → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ReverseWins n (∅ : Finset (Equiv.Perm (Fin k))) := by
  sorry

end OMA.S_arxiv_2603_16004
