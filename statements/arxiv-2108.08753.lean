import Mathlib

namespace OMA.S_arxiv_2108_08753

/-- Adjacency in Wigderson's parabola graph `Π_p` on vertex set `ZMod p × ZMod p`
(for an odd prime `p`): distinct vertices `(x, y)` and `(z, w)` are adjacent iff
`(x + z)^2 = y + w` in `ZMod p`. -/
def parabolaAdj (p : ℕ) (u v : ZMod p × ZMod p) : Prop :=
  u ≠ v ∧ (u.1 + v.1) ^ 2 = u.2 + v.2

/-- A subset `I` of `ZMod p × ZMod p` is an independent set of the parabola graph `Π_p`
if no two vertices of `I` are adjacent in `Π_p`. -/
def IsParabolaIndep (p : ℕ) (I : Finset (ZMod p × ZMod p)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ parabolaAdj p u v

/-- Conjecture (from an earlier version of Wigderson, arXiv:2108.08753; disproved by
Michael Tait): the `n = p^2`-vertex `C_4`-free parabola graphs `Π_p` (over odd primes `p`)
have independence number `n^{1/2 + o(1)}`, i.e., for every `ε > 0` there exists `C : ℝ`
such that every independent set `I` of `Π_p` satisfies `|I| ≤ C * (p^2)^{1/2 + ε}`. -/
theorem main :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ p : ℕ, Nat.Prime p → 2 < p →
        ∀ I : Finset (ZMod p × ZMod p),
          IsParabolaIndep p I →
          (I.card : ℝ) ≤ C * ((p * p : ℝ) ^ ((1 / 2 : ℝ) + ε)) := by
  sorry

end OMA.S_arxiv_2108_08753
