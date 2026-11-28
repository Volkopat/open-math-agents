import OMAStatements.S_erdos_132

namespace OMA.R_erdos_132_R1

open Filter
open scoped Classical Topology
open OMA.S_erdos_132 (pairMultiplicity rareDistances minRareCount)

-- Any configuration with at most one rare distance must lie in this range.
def H1 : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ A.card / 2 →
    2 ≤ (rareDistances A).card

-- For each desired lower bound, only a bounded excess over half the number
-- of points needs geometric analysis.
def H2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card + 2 ≤ A.card / 2 + k →
    k ≤ (rareDistances A).card

lemma multiplicity_pos {A : Finset (EuclideanSpace ℝ (Fin 2))} {d : ℝ}
    (hd : d ∈ A.offDiag.image (fun p => dist p.1 p.2)) :
    1 ≤ pairMultiplicity A d := by
  obtain ⟨⟨x, y⟩, hxy, hdist⟩ := Finset.mem_image.mp hd
  have hm := Finset.mem_offDiag.mp hxy
  have hyx : (y, x) ∈ A.offDiag :=
    Finset.mem_offDiag.mpr ⟨hm.2.1, hm.1, hm.2.2.symm⟩
  have hdistinct : (x, y) ≠ (y, x) := fun h => hm.2.2 (congrArg Prod.fst h)
  let F := A.offDiag.filter (fun p => dist p.1 p.2 = d)
  have hfirst : (x, y) ∈ F := Finset.mem_filter.mpr ⟨hxy, hdist⟩
  have hsecond : (y, x) ∈ F :=
    Finset.mem_filter.mpr ⟨hyx, (dist_comm y x).trans hdist⟩
  have hcard : 1 < F.card := Finset.one_lt_card.mpr ⟨_, hfirst, _, hsecond, hdistinct⟩
  change 1 ≤ F.card / 2
  omega

lemma distinct_lt_half_add_rare (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hA : 2 ≤ A.card) :
    (A.offDiag.image (fun p => dist p.1 p.2)).card < A.card / 2 + (rareDistances A).card := by
  let f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun p => dist p.1 p.2
  let D := A.offDiag.image f
  let B := D \ rareDistances A
  have hrare : rareDistances A ⊆ D := Finset.filter_subset _ _
  have hheavy (d : ℝ) (hd : d ∈ B) :
      2 * (A.card + 1) ≤ (A.offDiag.filter (fun p => f p = d)).card := by
    have hd' := Finset.mem_sdiff.mp hd
    have hpos := multiplicity_pos hd'.1
    have hlarge : A.card < pairMultiplicity A d := by
      by_contra! hsmall
      exact hd'.2 (Finset.mem_filter.mpr ⟨hd'.1, hpos, hsmall⟩)
    change A.card < (A.offDiag.filter (fun p => f p = d)).card / 2 at hlarge
    omega
  have hpairs : B.card * (2 * (A.card + 1)) ≤ A.card * (A.card - 1) := by
    calc
      B.card * (2 * (A.card + 1)) = ∑ _d ∈ B, 2 * (A.card + 1) := by simp
      _ ≤ ∑ d ∈ B, (A.offDiag.filter (fun p => f p = d)).card :=
        Finset.sum_le_sum fun d hd => hheavy d hd
      _ = (A.offDiag.filter (fun p => f p ∈ B)).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ A.offDiag.card := Finset.card_filter_le _ _
      _ = A.card * (A.card - 1) := by
        simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]
  have hB : B.card < A.card / 2 := by
    by_contra! hlarge
    have hwidth : A.card - 1 ≤ B.card * 2 := by omega
    have hlt : A.card * (A.card - 1) < (A.card - 1) * (A.card + 1) := by
      rw [mul_comm (A.card - 1)]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by omega)
    have hle := Nat.mul_le_mul_right (A.card + 1) hwidth
    rw [Nat.mul_assoc] at hle
    exact (not_le_of_gt hlt) (hle.trans hpairs)
  have hsplit : B.card + (rareDistances A).card = D.card :=
    Finset.card_sdiff_add_card_eq_card hrare
  change D.card < A.card / 2 + _
  omega

lemma configuration_exists (n : ℕ) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n := by
  let e : ℕ ↪ EuclideanSpace ℝ (Fin 2) :=
    ⟨fun i => WithLp.toLp 2 (fun _ : Fin 2 => (i : ℝ)), by
      intro i j h
      have heq : (i : ℝ) = (j : ℝ) :=
        congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x (0 : Fin 2)) h
      exact_mod_cast heq⟩
  exact ⟨(Finset.range n).map e, by simp⟩

theorem main : H1 → H2 → type_of% @OMA.S_erdos_132.main := by
  intro hsmall hgrowth
  constructor
  · intro A hA
    by_cases hD : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ A.card / 2
    · exact hsmall A hA hD
    · have hcount := distinct_lt_half_add_rare A (by omega)
      omega
  · refine tendsto_atTop.2 (fun b => ?_)
    let k := ⌈b⌉₊
    obtain ⟨N, hN⟩ := hgrowth k
    filter_upwards [eventually_ge_atTop (max N 2)] with n hn
    have hk : k ≤ minRareCount n := by
      unfold minRareCount
      apply le_csInf
      · obtain ⟨A, hA⟩ := configuration_exists n
        exact ⟨(rareDistances A).card, A, hA, rfl⟩
      · rintro j ⟨A, hA, rfl⟩
        by_cases hD :
            (A.offDiag.image (fun p => dist p.1 p.2)).card + 2 ≤ A.card / 2 + k
        · exact hN A (by omega) hD
        · have hcount := distinct_lt_half_add_rare A (by omega)
          omega
    exact (Nat.le_ceil b).trans (by exact_mod_cast hk)

end OMA.R_erdos_132_R1
