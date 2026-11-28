import OMAReductions.R_Erdos570_erdos_570_R1

/-!
# Erdős 570 connected targets: finite base and density trichotomy

The connected case of the cycle Ramsey bound is proved differently in three
density regimes.  Very dense targets are handled by cycle-into-clique
bookkeeping, very sparse connected targets by suspended paths and leaf
compression, and the intermediate regime by a random two-partition
neighborhood induction.  A finite Ramsey base covers the bounded-edge cases
that are too small for the square-root scale used in the middle regime.
-/

open SimpleGraph

namespace OMA.R_Erdos570_erdos_570_R1_H1_R1

/-- Finite base: connected targets below the scale threshold.  Since a
connected graph with bounded edge count has bounded order, finitely many
ordinary graph Ramsey numbers suffice here. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ B : ℕ, ∀ (W V : Type) [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    H.Connected →
    H.edgeSet.ncard < ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2 →
    B ≤ Fintype.card V → 2 * H.edgeSet.ncard + (k - 1) / 2 ≤ Fintype.card V →
    ¬ (cycleGraph k ⊑ Gᶜ) → H ⊑ G

/-- Dense connected targets: the host contains enough vertices for the
cycle-clique density argument. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ B : ℕ, ∀ (W V : Type) [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    H.Connected →
    ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2 ≤ H.edgeSet.ncard →
    Fintype.card W <
      2 * (200 * k ^ 2 + 2) * (k * Nat.sqrt (2 * H.edgeSet.ncard)) →
    B ≤ Fintype.card V → 2 * H.edgeSet.ncard + (k - 1) / 2 ≤ Fintype.card V →
    ¬ (cycleGraph k ⊑ Gᶜ) → H ⊑ G

/-- Sparse connected targets: the average degree is close enough to the tree
regime for suspended-path compression and leaf-rich reconstruction. -/
def H3 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ B : ℕ, ∀ (W V : Type) [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    H.Connected →
    ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2 ≤ H.edgeSet.ncard →
    (200 * k ^ 2 + 2 - 1) * H.edgeSet.ncard <
      (200 * k ^ 2 + 2) * Fintype.card W →
    B ≤ Fintype.card V → 2 * H.edgeSet.ncard + (k - 1) / 2 ≤ Fintype.card V →
    ¬ (cycleGraph k ⊑ Gᶜ) → H ⊑ G

/-- Middle-density connected targets: the complementary regime handled by the
random two-partition neighborhood induction. -/
def H4 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ B : ℕ, ∀ (W V : Type) [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    H.Connected →
    ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2 ≤ H.edgeSet.ncard →
    ¬ Fintype.card W <
      2 * (200 * k ^ 2 + 2) * (k * Nat.sqrt (2 * H.edgeSet.ncard)) →
    ¬ (200 * k ^ 2 + 2 - 1) * H.edgeSet.ncard <
      (200 * k ^ 2 + 2) * Fintype.card W →
    B ≤ Fintype.card V → 2 * H.edgeSet.ncard + (k - 1) / 2 ≤ Fintype.card V →
    ¬ (cycleGraph k ⊑ Gᶜ) → H ⊑ G

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos570_erdos_570_R1.H1 := by
  classical
  intro hbase hdense hsparse hmiddle k hk
  obtain ⟨B₁, hB₁⟩ := hbase k hk
  obtain ⟨B₂, hB₂⟩ := hdense k hk
  obtain ⟨B₃, hB₃⟩ := hsparse k hk
  obtain ⟨B₄, hB₄⟩ := hmiddle k hk
  refine ⟨max (max B₁ B₂) (max B₃ B₄), ?_⟩
  intro W V _ _ H G hconn hB hsize hfree
  have hB₁' : B₁ ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hB)
  have hB₂' : B₂ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hB)
  have hB₃' : B₃ ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hB)
  have hB₄' : B₄ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hB)
  by_cases hsmall : H.edgeSet.ncard <
      ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2
  · exact hB₁ W V H G hconn hsmall hB₁' hsize hfree
  · have hlarge : ((200 * k ^ 2 + 2) * (8 * k + 1)) ^ 2 ≤
        H.edgeSet.ncard := Nat.le_of_not_gt hsmall
    by_cases hd : Fintype.card W <
        2 * (200 * k ^ 2 + 2) * (k * Nat.sqrt (2 * H.edgeSet.ncard))
    · exact hB₂ W V H G hconn hlarge hd hB₂' hsize hfree
    · by_cases hs : (200 * k ^ 2 + 2 - 1) * H.edgeSet.ncard <
        (200 * k ^ 2 + 2) * Fintype.card W
      · exact hB₃ W V H G hconn hlarge hs hB₃' hsize hfree
      · exact hB₄ W V H G hconn hlarge hd hs hB₄' hsize hfree

end OMA.R_Erdos570_erdos_570_R1_H1_R1
