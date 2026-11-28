import OMAReductions.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1

/- The case k = 6 admits a maximum-cut proof using the established case k = 3.
Separating it leaves even k >= 8, within the k >= 7 range of the strengthened
admissible-cycle theorem in Luo-Ma-Zhao, arXiv:2601.13552, Theorem 1.4. -/

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1

open SimpleGraph

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 6 ≤ G.minDegree → ∃ m ∈ G.cycleLengths, 6 ∣ m

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ},
    8 ≤ k → Even k → ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → k ≤ G.minDegree → ∃ m ∈ G.cycleLengths, k ∣ m

theorem main : H1 → H2 →
    OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1.H1 := by
  intro h1 h2 V _ _ k hk heven G _ hconn hdeg
  by_cases h6 : k = 6
  · subst k
    exact h1 G hconn hdeg
  · have hk8 : 8 ≤ k := by
      obtain ⟨j, hj⟩ := heven
      omega
    exact h2 hk8 heven G hconn hdeg

end OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1
