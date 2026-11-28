import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

open Finset SimpleGraph
open scoped BigOperators Classical

namespace Erdos151LoneCount

variable {V : Type}

private def Lone (G : SimpleGraph V) (x y : V) : Prop :=
  G.Adj x y ∧ ¬ ∃ z, G.Adj x z ∧ G.Adj y z

private theorem lone_symm {G : SimpleGraph V} {x y : V} (h : Lone G x y) : Lone G y x :=
  ⟨h.1.symm, fun ⟨z, hy, hx⟩ => h.2 ⟨z, hx, hy⟩⟩

/-- In a K₄-free graph a set avoiding the maximal cliques has neither a lone edge nor a triangle. -/
private def Free (G : SimpleGraph V) (F : Finset V) : Prop :=
  (∀ a ∈ F, ∀ b ∈ F, ¬ Lone G a b) ∧
  (∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c))

private theorem indep_no_adj {G : SimpleGraph V} {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) {x y : V} (hx : x ∈ I) (hy : y ∈ I) : ¬ G.Adj x y :=
  fun h => hI hx hy h.ne h

private theorem free_of_indep {G : SimpleGraph V} {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) : Free G I :=
  ⟨fun _ ha _ hb h => indep_no_adj hI ha hb h.1,
   fun _ ha _ hb _ _ h => indep_no_adj hI ha hb h.1⟩

private theorem free_subset {G : SimpleGraph V} {A B : Finset V} (h : A ⊆ B) (hf : Free G B) :
    Free G A :=
  ⟨fun a ha b hb => hf.1 a (h ha) b (h hb),
   fun a ha b hb c hc => hf.2 a (h ha) b (h hb) c (h hc)⟩

/-- An independent set can be added if its only old neighbours lie in the independent part
of the old set, and each such edge belongs to a triangle in the ambient graph. -/
private theorem free_extend {G : SimpleGraph V} {I J B X : Finset V}
    (hB : Free G B) (hsub : B ⊆ I ∪ J)
    (hI : G.IsIndepSet (I : Set V)) (hX : G.IsIndepSet (X : Set V))
    (hl : ∀ x ∈ X, ∀ y ∈ B, y ∈ I → ¬ Lone G x y)
    (hj : ∀ x ∈ X, ∀ y ∈ B, y ∈ J → ¬ G.Adj x y) : Free G (B ∪ X) := by
  have cross (x) (hx : x ∈ X) (y) (hy : y ∈ B) : ¬ Lone G x y := by
    rcases mem_union.mp (hsub hy) with hi | hj'
    · exact hl x hx y hy hi
    · exact fun h => hj x hx y hy hj' h.1
  have tri (x) (hx : x ∈ X) (a) (ha : a ∈ B) (b) (hb : b ∈ B)
      (hxa : G.Adj x a) (hxb : G.Adj x b) : ¬ G.Adj a b := by
    have haI := (mem_union.mp (hsub ha)).resolve_right (fun h => hj x hx a ha h hxa)
    have hbI := (mem_union.mp (hsub hb)).resolve_right (fun h => hj x hx b hb h hxb)
    exact indep_no_adj hI haI hbI
  constructor
  · intro a ha b hb h
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact hB.1 a ha b hb h
    · exact cross b hb a ha (lone_symm h)
    · exact cross a ha b hb h
    · exact indep_no_adj hX ha hb h.1
  · intro a ha b hb c hc ⟨hab, hac, hbc⟩
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb <;>
      rcases mem_union.mp hc with hc | hc
    · exact hB.2 a ha b hb c hc ⟨hab, hac, hbc⟩
    · exact tri c hc a ha b hb hac.symm hbc.symm hab
    · exact tri b hb a ha c hc hab.symm hbc hac
    · exact indep_no_adj hX hb hc hbc
    · exact tri a ha b hb c hc hab hac hbc
    · exact indep_no_adj hX ha hc hac
    · exact indep_no_adj hX ha hb hab
    · exact indep_no_adj hX ha hb hab

private theorem clique_small {G : SimpleGraph V} (hG : G.CliqueFree 4) {A : Finset V}
    (hA : G.IsClique (A : Set V)) : A.card ≤ 3 := by
  by_contra h
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (show 4 ≤ A.card by omega)
  exact hG B (G.isNClique_iff.mpr ⟨IsClique.subset hBA hA, hB⟩)

private theorem clique_insert_of_adj [DecidableEq V] {G : SimpleGraph V} {A : Finset V} {x : V}
    (hA : G.IsClique (A : Set V)) (hx : ∀ y ∈ A, G.Adj x y) :
    G.IsClique ((insert x A : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, mem_insert] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · rw [ha]; exact hx b hb
  · rw [hb]; exact (hx a ha).symm
  · exact hA ha hb hab

private theorem free_neighbors [Fintype V] {G : SimpleGraph V} (hG : G.CliqueFree 4) (v : V) :
    Free G (univ.filter (G.Adj v)) := by
  constructor
  · intro a ha b hb hab
    exact hab.2 ⟨v, (mem_filter.mp ha).2.symm, (mem_filter.mp hb).2.symm⟩
  · intro a ha b hb c hc ⟨hab, hac, hbc⟩
    have hT : G.IsClique (({a,b,c} : Finset V) : Set V) := by
      apply clique_insert_of_adj (clique_insert_of_adj (by simp) ?_) ?_
      · intro y hy
        obtain rfl := mem_singleton.mp hy
        exact hbc
      · intro y hy
        rcases mem_insert.mp hy with rfl | hy
        · exact hab
        · obtain rfl := mem_singleton.mp hy
          exact hac
    have hQ := clique_insert_of_adj hT (x := v) (by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact (mem_filter.mp ha).2
      rcases mem_insert.mp hy with rfl | hy
      · exact (mem_filter.mp hb).2
      obtain rfl := mem_singleton.mp hy
      exact (mem_filter.mp hc).2)
    have hc4 := clique_small hG hQ
    have hne₁ := (mem_filter.mp ha).2.ne
    have hne₂ := (mem_filter.mp hb).2.ne
    have hne₃ := (mem_filter.mp hc).2.ne
    simp [hne₁, hne₂, hne₃, hab.ne, hac.ne, hbc.ne] at hc4

private theorem sum_filter_counts (R : V → V → Prop)
    (hR : ∀ a b, R a b ↔ R b a) (A B : Finset V) :
    (∑ x ∈ A, (B.filter (R x)).card) = ∑ y ∈ B, (A.filter (R y)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [hR x y]

private theorem sum_mem_count {A B : Finset V} (h : B ⊆ A) :
    (∑ x ∈ A, if x ∈ B then (1 : ℕ) else 0) = B.card := by
  have heq : A.filter (· ∈ B) = B := by
    ext x
    exact ⟨fun hx => (mem_filter.mp hx).2, fun hx => mem_filter.mpr ⟨h hx, hx⟩⟩
  rw [← Finset.sum_filter, heq, ← card_eq_sum_ones]

private theorem no_mem_of_card_zero {A : Finset V} (h : A.card = 0) {x : V} : x ∉ A := by
  rw [card_eq_zero.mp h]
  exact notMem_empty x

private theorem disjoint_compl_of_subset [Fintype V] {A B C : Finset V} (hA : A ⊆ C) (hB : B ⊆ Cᶜ) :
    Disjoint A B := Finset.disjoint_left.mpr fun _ hx hy => mem_compl.mp (hB hy) (hA hx)

/-- The lone-edge count follows solely from the cap on sets avoiding maximal cliques. -/
private theorem weighted_count [Fintype V] (G : SimpleGraph V) (hG : G.CliqueFree 4) (D : ℕ)
    (hcap : ∀ F, Free G F → F.card ≤ D) (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    (∑ x : V, (2 - (I.filter (Lone G x)).card)) + (D + 1) * I.card + (D - G.indepNum)
      ≤ (D + 4) * D := by
  let candidates := univ.powerset.filter (fun F => I ⊆ F ∧ Free G F)
  have hcand : candidates.Nonempty := ⟨I, mem_filter.mpr
    ⟨mem_powerset.mpr (subset_univ _), Subset.rfl, free_of_indep hI⟩⟩
  obtain ⟨F, hFm, hFmax⟩ := Finset.exists_max_image candidates Finset.card hcand
  obtain ⟨hIF, hF⟩ := (mem_filter.mp hFm).2
  have hmax (A : Finset V) (hIA : I ⊆ A) (hA : Free G A) : A.card ≤ F.card :=
    hFmax A (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hIA, hA⟩)
  let J := F \ I
  let W := Fᶜ
  let dI (x : V) := (I.filter (Lone G x)).card
  let dJ (x : V) := (J.filter (G.Adj x)).card
  let A (j : V) := W.filter fun x => dI x = 0 ∧ J.filter (G.Adj x) = {j}
  let P (i : V) := W.filter fun x => dJ x = 0 ∧ I.filter (Lone G x) = {i}
  let Z := J.filter fun j => (F.filter (G.Adj j)).card = 0
  have hJ (x : V) (hx : x ∈ J) : x ∈ F := (mem_sdiff.mp hx).1
  have split (x : V) (hx : x ∈ F) : x ∈ I ∪ J := by
    by_cases hi : x ∈ I
    · exact mem_union_left _ hi
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, hi⟩)
  have hFcap := hcap F hF
  have dIzero (x i : V) (hx : dI x = 0) (hi : i ∈ I) : ¬ Lone G x i :=
    fun h => no_mem_of_card_zero hx (mem_filter.mpr ⟨hi, h⟩)
  have dJzero (x j : V) (hx : dJ x = 0) (hj : j ∈ J) : ¬ G.Adj x j :=
    fun h => no_mem_of_card_zero hx (mem_filter.mpr ⟨hj, h⟩)
  have zerocase (x : V) (hx : x ∈ W) (hxi : dI x = 0) : dJ x ≠ 0 := by
    intro hxj
    have hX : G.IsIndepSet ((({x} : Finset V) : Set V)) := by simp
    have hU := free_extend hF split hI hX
      (by intro a ha i _ hi; rw [mem_singleton.mp ha]; exact dIzero x i hxi hi)
      (by intro a ha j _ hj; rw [mem_singleton.mp ha]; exact dJzero x j hxj hj)
    have h := hmax (F ∪ {x}) (fun a ha => mem_union_left _ (hIF ha)) hU
    simp [union_comm F, mem_compl.mp hx] at h
  have hAcard (j : V) (hj : j ∈ J) : (A j).card ≤ 2 := by
    have hadj (x : V) (hx : x ∈ A j) : G.Adj x j := by
      have heq := (mem_filter.mp hx).2.2
      exact (mem_filter.mp (show j ∈ J.filter (G.Adj x) by rw [heq]; simp)).2
    have hAcl : G.IsClique (A j : Set V) := by
      intro x hx y hy hxy
      by_contra hno
      let B := F.erase j
      let X : Finset V := {x,y}
      have hBs : B ⊆ F := erase_subset _ _
      have hXI : G.IsIndepSet (X : Set V) := by
        intro a ha b hb hab
        simp only [X, Finset.mem_coe, mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact (hab (ha.trans hb.symm)).elim
        · rw [ha, hb]; exact hno
        · rw [ha, hb]; exact fun h => hno h.symm
        · exact (hab (ha.trans hb.symm)).elim
      have hXA : X ⊆ A j := by
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact hx
        · obtain rfl := mem_singleton.mp ha; exact hy
      have hU := free_extend (free_subset hBs hF) (fun a ha => split _ (hBs ha)) hI hXI
        (by intro a ha i _ hi; exact dIzero a i (mem_filter.mp (hXA ha)).2.1 hi)
        (by
          intro a ha b hb hbJ hab
          have heq := (mem_filter.mp (hXA ha)).2.2
          have hbj := mem_singleton.mp (heq ▸ mem_filter.mpr ⟨hbJ, hab⟩)
          exact (mem_erase.mp hb).1 hbj)
      have hIB : I ⊆ B := fun a ha => mem_erase.mpr
        ⟨fun he => (mem_sdiff.mp hj).2 (he ▸ ha), hIF ha⟩
      have hle := hmax (B ∪ X) (fun a ha => mem_union_left _ (hIB ha)) hU
      rw [card_union_of_disjoint (disjoint_compl_of_subset hBs (fun a ha => (mem_filter.mp (hXA ha)).1)),
        show B.card = F.card - 1 from card_erase_of_mem (hJ j hj), show X.card = 2 by simp [X, hxy]] at hle
      omega
    have hcl := clique_insert_of_adj hAcl (x := j) (fun x hx => (hadj x hx).symm)
    have h := clique_small hG hcl
    have hjA : j ∉ A j := fun h => mem_compl.mp (mem_filter.mp h).1 (hJ j hj)
    rw [card_insert_of_notMem hjA] at h
    omega
  have hPcard (i : V) (hi : i ∈ I) : (P i).card ≤ D - F.card + 1 := by
    let B := F.erase i
    have hBs : B ⊆ F := erase_subset _ _
    have hPi (x : V) (hx : x ∈ P i) : Lone G x i := by
      have heq := (mem_filter.mp hx).2.2
      exact (mem_filter.mp (show i ∈ I.filter (Lone G x) by rw [heq]; simp)).2
    have hpind : G.IsIndepSet (P i : Set V) := by
      intro x hx y hy _ hxy
      exact (hPi x hx).2 ⟨y, hxy, (hPi y hy).1.symm⟩
    have hU := free_extend (free_subset hBs hF) (fun a ha => split _ (hBs ha)) hI hpind
      (by
        intro a ha b hb hbI hab
        have heq := (mem_filter.mp ha).2.2
        have hbi := mem_singleton.mp (heq ▸ mem_filter.mpr ⟨hbI, hab⟩)
        exact (mem_erase.mp hb).1 hbi)
      (by intro a ha b _ hbJ; exact dJzero a b (mem_filter.mp ha).2.1 hbJ)
    have hle := hcap (B ∪ P i) hU
    rw [card_union_of_disjoint (disjoint_compl_of_subset hBs (fun a ha => (mem_filter.mp ha).1)),
      show B.card = F.card - 1 from card_erase_of_mem (hIF hi)] at hle
    change F.card - 1 + (P i).card ≤ D at hle
    omega
  have hiZ (x : V) (hx : x ∈ Z) (y : V) (hy : y ∈ F) : ¬ G.Adj x y := by
    intro h
    exact no_mem_of_card_zero (mem_filter.mp hx).2 (mem_filter.mpr ⟨hy, h⟩)
  have hIind : I.card + Z.card ≤ G.indepNum := by
    have hU : G.IsIndepSet ((I ∪ Z : Finset V) : Set V) := by
      intro x hx y hy hxy
      rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
      · exact hI hx hy hxy
      · exact fun h => hiZ y hy x (hIF hx) h.symm
      · exact hiZ x hx y (hIF hy)
      · exact hiZ x hx y (hJ _ (mem_filter.mp hy).1)
    have hdis : Disjoint I Z := Finset.disjoint_left.mpr fun _ hi hz =>
      (mem_sdiff.mp (mem_filter.mp hz).1).2 hi
    simpa only [card_union_of_disjoint hdis] using hU.card_le_indepNum
  have hRow (j : V) (hj : j ∈ J) : (W.filter (G.Adj j)).card + (A j).card ≤
      D + 1 + (if j ∈ Z then 1 else 0) := by
    have hdeg := hcap _ (free_neighbors hG j)
    have hpart : (F.filter (G.Adj j)).card + (W.filter (G.Adj j)).card =
        (univ.filter (G.Adj j)).card := by
      rw [← card_union_of_disjoint (disjoint_compl_of_subset (filter_subset _ _) (filter_subset _ _))]
      congr 1
      ext x
      simp only [mem_union, mem_filter, mem_compl, mem_univ, true_and]
      by_cases hx : x ∈ F <;> simp [hx]
    have ha := hAcard j hj
    by_cases hz : j ∈ Z
    · simp only [if_pos hz]; omega
    · simp only [if_neg hz, add_zero];
      have hp : 0 < (F.filter (G.Adj j)).card := by
        by_contra h
        exact hz (mem_filter.mpr ⟨hj, by omega⟩)
      omega
  have hPoint (x : V) (hx : x ∈ W) : 2 - dI x ≤ dJ x +
      (∑ j ∈ J, if x ∈ A j then 1 else 0) + (∑ i ∈ I, if x ∈ P i then 1 else 0) := by
    by_cases hxi : dI x = 0
    · have hp := zerocase x hx hxi
      by_cases hxj : dJ x = 1
      · obtain ⟨j, heq⟩ := card_eq_one.mp hxj
        have hj : j ∈ J := (mem_filter.mp (show j ∈ J.filter (G.Adj x) by rw [heq]; simp)).1
        have hxa : x ∈ A j := mem_filter.mpr ⟨hx, hxi, heq⟩
        have hb : 1 ≤ ∑ j ∈ J, if x ∈ A j then 1 else 0 := by
          simpa only [if_pos hxa] using
            (Finset.single_le_sum (fun j _ => Nat.zero_le (if x ∈ A j then 1 else 0)) hj)
        omega
      · omega
    · by_cases hxi' : dI x = 1
      · by_cases hxj : dJ x = 0
        · obtain ⟨i, heq⟩ := card_eq_one.mp hxi'
          have hi : i ∈ I := (mem_filter.mp (show i ∈ I.filter (Lone G x) by rw [heq]; simp)).1
          have hxp : x ∈ P i := mem_filter.mpr ⟨hx, hxj, heq⟩
          have hb : 1 ≤ ∑ i ∈ I, if x ∈ P i then 1 else 0 := by
            simpa only [if_pos hxp] using
              (Finset.single_le_sum (fun i _ => Nat.zero_le (if x ∈ P i then 1 else 0)) hi)
          omega
        · omega
      · omega
  have hAcount (j : V) : (∑ x ∈ W, if x ∈ A j then 1 else 0) = (A j).card := by
    exact sum_mem_count (filter_subset _ _)
  have hPcount (i : V) : (∑ x ∈ W, if x ∈ P i then 1 else 0) = (P i).card := by
    exact sum_mem_count (filter_subset _ _)
  have hOutside : (∑ x ∈ W, (2 - dI x)) ≤
      J.card * (D + 1) + Z.card + I.card * (D - F.card + 1) := by
    calc
      _ ≤ ∑ x ∈ W, (dJ x + (∑ j ∈ J, if x ∈ A j then 1 else 0) +
          (∑ i ∈ I, if x ∈ P i then 1 else 0)) := Finset.sum_le_sum hPoint
      _ = (∑ j ∈ J, ((W.filter (G.Adj j)).card + (A j).card)) + ∑ i ∈ I, (P i).card := by
        simp only [Finset.sum_add_distrib]
        rw [show (∑ x ∈ W, dJ x) = ∑ j ∈ J, (W.filter (G.Adj j)).card from
          sum_filter_counts G.Adj (fun _ _ => ⟨Adj.symm, Adj.symm⟩) W J]
        rw [Finset.sum_comm (s := W) (t := J), Finset.sum_comm (s := W) (t := I)]
        simp only [hAcount, hPcount]
      _ ≤ (∑ j ∈ J, (D + 1 + (if j ∈ Z then 1 else 0))) + ∑ i ∈ I, (D - F.card + 1) :=
        Nat.add_le_add (Finset.sum_le_sum hRow) (Finset.sum_le_sum hPcard)
      _ = _ := by
        rw [Finset.sum_add_distrib, sum_mem_count (show Z ⊆ J from filter_subset _ _)]
        simp [Nat.mul_comm]
  have hInside : (∑ x ∈ F, (2 - dI x)) = 2 * F.card := by
    calc
      _ = ∑ _x ∈ F, (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hz : I.filter (Lone G x) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hF.1 x hx y (hIF (mem_filter.mp hy).1) (mem_filter.mp hy).2
        simp [dI, hz]
      _ = _ := by simp [Nat.mul_comm]
  have hW : (∑ x : V, (2 - dI x)) = 2 * F.card + ∑ x ∈ W, (2 - dI x) := by
    rw [← hInside]
    exact (Finset.sum_compl_add_sum F _).symm.trans (Nat.add_comm _ _)
  have hIFcard := card_le_card hIF
  let gap := D - F.card
  have hGsplit : D = I.card + J.card + gap := by
    have hj := card_sdiff_of_subset hIF
    change J.card = F.card - I.card at hj
    dsimp [gap]
    omega
  have hJsplit : F.card = I.card + J.card := by
    have hj := card_sdiff_of_subset hIF
    change J.card = F.card - I.card at hj
    omega
  have hprod : I.card * gap ≤ (D+3) * gap :=
    Nat.mul_le_mul_right _ (by omega)
  have hAlpha : G.indepNum ≤ D := by
    apply csSup_le'
    show ∀ k ∈ {k : ℕ | ∃ s, G.IsNIndepSet k s}, k ≤ D
    intro k hk
    obtain ⟨s, hs⟩ := hk
    rw [← hs.card_eq]
    exact hcap s (free_of_indep hs.isIndepSet)
  have hBudget : (D + 4) * D = (D+1) * I.card + J.card * (D+1) + (D+3) * gap +
      2 * I.card + 2 * J.card + D := by
    calc
      _ = (D+1) * (I.card + J.card + gap) + 2 * (I.card + J.card + gap) + D := by
        rw [← hGsplit]; ring
      _ = _ := by ring
  change (∑ x ∈ W, (2 - dI x)) ≤ J.card * (D + 1) + Z.card + I.card * (gap + 1) at hOutside
  rw [Nat.mul_add I.card gap 1, Nat.mul_one] at hOutside
  change (∑ x : V, (2 - dI x)) + (D + 1) * I.card + (D - G.indepNum) ≤ _
  rw [hW, hBudget, hJsplit, Nat.mul_add]
  omega

end Erdos151LoneCount

namespace Erdos151LoneCount

private theorem free_compl_transversal {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)}
    (hU : Free G U) : G.IsCliqueTransversal Uᶜ := by
  intro s hs
  by_contra hmiss
  have hsU : s ⊆ U := by
    intro x hx
    by_contra hxU
    exact hmiss ⟨x, hx, Finset.mem_compl.mpr hxU⟩
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (show 1 < s.card by
    have := hs.2
    omega)
  have hadj : G.Adj a b := hs.1.1 ha hb hab
  have heq : s = {a,b} := by
    apply Subset.antisymm
    · intro z hz
      by_contra he
      have hza : z ≠ a := fun h => he (Finset.mem_insert.mpr (Or.inl h))
      have hzb : z ≠ b := fun h => he (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
      exact hU.2 a (hsU ha) b (hsU hb) z (hsU hz)
        ⟨hadj, hs.1.1 ha hz hza.symm, hs.1.1 hb hz hzb.symm⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ha
      · obtain rfl := Finset.mem_singleton.mp hz
        exact hb
  have hl : Lone G a b := by
    refine ⟨hadj, ?_⟩
    rintro ⟨z, haz, hbz⟩
    have hzi : z ∉ s := by simp [heq, haz.ne', hbz.ne']
    have hins : G.IsClique ((insert z s : Finset (Fin n)) : Set (Fin n)) :=
      clique_insert_of_adj hs.1.1 (by
        intro t ht
        rw [heq] at ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact haz.symm
        · obtain rfl := Finset.mem_singleton.mp ht
          exact hbz.symm)
    have h := hs.1.2 hins (Finset.subset_insert _ _)
    exact hzi (h (Finset.mem_insert_self _ _))
  exact hU.1 a (hsU ha) b (hsU hb) hl

end Erdos151LoneCount

open Erdos151LoneCount in
/-- Double-count the incidences of lone edges after a maximum extension of the independent set. -/
theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H2_R1.H1 := by
  classical
  unfold OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H2_R1.H1
  intro n G hG D hD
  dsimp only
  intro I hI
  let d (x : Fin n) := (I.filter (Lone G x)).card
  have hcap (U : Finset (Fin n)) (hU : Free G U) : U.card ≤ D := by
    have hτ : G.cliqueTransversalNumber ≤ Uᶜ.card := csInf_le' ⟨_, free_compl_transversal hU, rfl⟩
    rw [Finset.card_compl, Fintype.card_fin] at hτ
    have hu : U.card ≤ n := by simpa using (Finset.card_le_univ U)
    omega
  have hw := weighted_count G hG D hcap I hI
  have hcol : (∑ x : Fin n, d x) = ∑ x ∈ I, (univ.filter (Lone G x)).card :=
    sum_filter_counts (Lone G) (fun _ _ => ⟨lone_symm, lone_symm⟩) univ I
  have hbalance : 2 * n + (∑ x : Fin n, (d x - 2)) =
      (∑ x : Fin n, d x) + ∑ x : Fin n, (2 - d x) := by
    calc
      _ = ∑ x : Fin n, (2 + (d x - 2)) := by simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ = ∑ x : Fin n, (d x + (2 - d x)) := by
        apply Finset.sum_congr rfl
        intro x _
        omega
      _ = _ := Finset.sum_add_distrib
  change (∑ x : Fin n, (2 - d x)) + (D+1) * I.card + (D - G.indepNum) ≤ (D+4) * D at hw
  have hfilter (S : Finset (Fin n)) (x : Fin n)
      (hdec : DecidablePred (fun y => G.Adj x y ∧ ¬ ∃ z, G.Adj x z ∧ G.Adj y z)) :
      @Finset.filter _ (fun y => G.Adj x y ∧ ¬ ∃ z, G.Adj x z ∧ G.Adj y z) hdec S =
        S.filter (Lone G x) := by
    ext y
    simp only [Finset.mem_filter, Lone]
  simp only [hfilter]
  change 2 * n + (D+1) * I.card + (D - G.indepNum) + (∑ x : Fin n, (d x - 2)) ≤
    (D+4) * D + ∑ x ∈ I, (univ.filter (Lone G x)).card
  omega
