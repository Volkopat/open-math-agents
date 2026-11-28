import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1
import Mathlib

/-! McKay-Min degree reduction for R(3,8) <= 28 (8 <= Erdos151.H 28):
Every triangle-free 28-vertex graph with no independent set of size 8 has
maximum degree <= 7, and via R(3,7) <= 23 (H1) has minimum degree >= 5,
splitting into the degree-5 branch (H2, whose non-neighborhood is a (3,7,22)-graph)
and the minimum-degree >= 6 branch (H3). -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1

/-- Upper bound R(3,7) <= 23. -/
def H1 : Prop :=
  7 ≤ Erdos151.H 23

/-- Degree-5 branch: no triangle-free 28-vertex graph with degrees in {5,6,7}
and at least one vertex of degree 5 avoids an independent set of size 8. -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 28), G.CliqueFree 3 →
    (∀ v : Fin 28, 5 ≤ (univ.filter (G.Adj v)).card ∧ (univ.filter (G.Adj v)).card ≤ 7) →
    (∃ v : Fin 28, (univ.filter (G.Adj v)).card = 5) →
    ∃ s, G.IsNIndepSet 8 s

/-- Minimum-degree >= 6 branch: no triangle-free 28-vertex graph with all degrees
in {6,7} avoids an independent set of size 8. -/
def H3 : Prop :=
  ∀ G : SimpleGraph (Fin 28), G.CliqueFree 3 →
    (∀ v : Fin 28, 6 ≤ (univ.filter (G.Adj v)).card ∧ (univ.filter (G.Adj v)).card ≤ 7) →
    ∃ s, G.IsNIndepSet 8 s

section Proof

private theorem H_attained_aux {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  classical
  let S : Set ℕ := {k | ∀ Q : SimpleGraph (Fin n), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet k s}
  have hne : S.Nonempty := ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
  have hfin : S.Finite := (Set.finite_Iic n).subset fun k hk => by
    obtain ⟨s, hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  exact hne.csSup_mem hfin F hF

private theorem indep_of_subset_nbr {n k : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3)
    (v : Fin n) (hk : k ≤ (univ.filter (G.Adj v)).card) :
    ∃ s, G.IsNIndepSet k s := by
  classical
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hk
  refine ⟨s, ?_, hsc⟩
  intro x hx y hy hne hadj
  have hxv : G.Adj v x := (Finset.mem_filter.mp (hs hx)).2
  have hyv : G.Adj v y := (Finset.mem_filter.mp (hs hy)).2
  exact hG {v, x, y} (SimpleGraph.is3Clique_iff.mpr ⟨v, x, y, hxv, hyv, hadj, rfl⟩)

private theorem indep_from_nonnbr {n k m : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3)
    (hHm : k ≤ Erdos151.H m) (v : Fin n)
    (hm : m ≤ (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card) :
    ∃ s, G.IsNIndepSet (k + 1) s := by
  classical
  let M := univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
  obtain ⟨T, hTM, hTc⟩ := Finset.exists_subset_card_eq hm
  let e : Fin m ≃ T := (Fintype.equivFinOfCardEq (by simp [hTc])).symm
  let Q : SimpleGraph (Fin m) :=
    { Adj := fun i j => G.Adj (e i).val (e j).val
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => G.irrefl h⟩ }
  have hQ : Q.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hG {(e a).val, (e b).val, (e c).val}
      (SimpleGraph.is3Clique_iff.mpr ⟨(e a).val, (e b).val, (e c).val, hab, hac, hbc, rfl⟩)
  obtain ⟨I0, hI0⟩ := H_attained_aux Q hQ
  have hkI : k ≤ I0.card := hHm.trans_eq hI0.card_eq.symm
  obtain ⟨I, hII0, hIc⟩ := Finset.exists_subset_card_eq hkI
  let S : Finset (Fin n) := I.image (fun i => (e i).val)
  have hvS : v ∉ S := by
    intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have hmem : (e i).val ∈ M := hTM (e i).property
    exact ((Finset.mem_filter.mp hmem).2.1) hi
  have hScard : S.card = k := by
    rw [Finset.card_image_of_injective _ (fun i j hij => e.injective (Subtype.ext hij)), hIc]
  refine ⟨insert v S, ?_, ?_⟩
  · intro x hx y hy hxy hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
    rcases hx with rfl | hxS <;> rcases hy with rfl | hyS
    · exact hxy rfl
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyS
      exact (Finset.mem_filter.mp (hTM (e j).property)).2.2 hadj
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxS
      exact (Finset.mem_filter.mp (hTM (e i).property)).2.2 hadj.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxS
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hyS
      have hij : i ≠ j := fun h => hxy (by rw [h])
      exact hI0.isIndepSet (hII0 hi) (hII0 hj) hij hadj
  · rw [Finset.card_insert_of_notMem hvS, hScard]

private theorem nonnbr_card {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card +
      (univ.filter (G.Adj v)).card + 1 = n := by
  classical
  let N := univ.filter (G.Adj v)
  let M := univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
  have hdisj1 : Disjoint M N := by
    rw [Finset.disjoint_left]
    intro u huM huN
    exact (Finset.mem_filter.mp huM).2.2 (Finset.mem_filter.mp huN).2
  have hvMN : v ∉ M ∪ N := by
    intro hv
    rcases Finset.mem_union.mp hv with hvM | hvN
    · exact (Finset.mem_filter.mp hvM).2.1 rfl
    · exact G.irrefl (Finset.mem_filter.mp hvN).2
  have huniv : insert v (M ∪ N) = (Finset.univ : Finset (Fin n)) := by
    ext u
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true, M, N]
    by_cases huv : u = v
    · exact Or.inl huv
    · by_cases hadj : G.Adj v u
      · exact Or.inr (Or.inr hadj)
      · exact Or.inr (Or.inl ⟨huv, hadj⟩)
  have hcard : (insert v (M ∪ N)).card = n := by
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_insert_of_notMem hvMN, Finset.card_union_of_disjoint hdisj1] at hcard
  omega

theorem main : H1 → H2 → H3 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1.H2 := by
  classical
  intro h1 h2 h3
  change 8 ≤ sSup {k | ∀ G : SimpleGraph (Fin 28), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hbdd : BddAbove {k | ∀ G : SimpleGraph (Fin 28), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s} := by
    refine ⟨28, fun k hk => ?_⟩
    obtain ⟨s, hs⟩ := hk (⊥ : SimpleGraph (Fin 28)) (fun t ht => by
      obtain ⟨a, b, _, hab, _, _, -⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hab)
    simpa [hs.card_eq] using Finset.card_le_univ s
  apply le_csSup hbdd
  intro G hG
  by_cases hhi : ∃ v : Fin 28, 8 ≤ (univ.filter (G.Adj v)).card
  · obtain ⟨v, hv⟩ := hhi
    exact indep_of_subset_nbr G hG v hv
  · push_neg at hhi
    by_cases hlo : ∃ v : Fin 28, (univ.filter (G.Adj v)).card ≤ 4
    · obtain ⟨v, hv⟩ := hlo
      have hM : 23 ≤ (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card := by
        have hsum := nonnbr_card G v
        omega
      exact indep_from_nonnbr G hG h1 v hM
    · push_neg at hlo
      have hdeg : ∀ v : Fin 28, 5 ≤ (univ.filter (G.Adj v)).card ∧ (univ.filter (G.Adj v)).card ≤ 7 := by
        intro v
        have h1' := hlo v
        have h2' := hhi v
        omega
      by_cases h5 : ∃ v : Fin 28, (univ.filter (G.Adj v)).card = 5
      · exact h2 G hG hdeg h5
      · push_neg at h5
        refine h3 G hG (fun v => ?_)
        have hv := hdeg v
        have hv5 := h5 v
        omega

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1
