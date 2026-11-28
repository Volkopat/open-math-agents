import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H1_R1
import Mathlib

-- Reduction Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1.H1.R1.H3.R1 of step Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1.H1.R1.H3

/-!
Tightened full-neighborhood safe-outsider reduction for the residual `H(n) = 12` case
on `53 <= n <= 58`. Using private lone-neighbor caps on `N_G(v)` to improve `U(8,3) <= 16`
and `U(9,2) <= 10`, this closes `n = 58` unconditionally, closes `n = 57` completely via
equality extraction and disjoint core-neighborhood counting, and tightens `n = 56` to a
full-degree-11 vertex with at least three lone edges.
-/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H1_R1_H3_R1

/-- Bikov 7-vertex link-extension lemma for triangle-free edge-coloured links. -/
def H1 : Prop :=
  ∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)

/-- Residual n = 56 case with a full-degree-11 vertex having at least three lone edges. -/
def H2 : Prop :=
  Erdos151.H 56 = 12 →
    ∀ G : SimpleGraph (Fin 56), G.CliqueFree 4 →
      (∀ v, (univ.filter (G.Adj v)).card ≤ 11) →
      (∃ v : Fin 56, (univ.filter (G.Adj v)).card = 11 ∧
        3 ≤ (univ.filter fun w => G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w).card) →
      cliqueTransversalNumber G ≤ 56 - 12

/-- Residual H(n) = 12 case on 53 <= n <= 55 with a full-degree-11 vertex having
at least two lone edges (or at least one lone edge at order 53). -/
def H3 : Prop :=
  ∀ n, Erdos151.H n = 12 → 53 ≤ n → n ≤ 55 →
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
      (∀ v, (univ.filter (G.Adj v)).card ≤ 11) →
      (∃ v : Fin n, (univ.filter (G.Adj v)).card = 11 ∧
        (if n = 53 then 1 else 2) ≤
          (univ.filter fun w => G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w).card) →
      cliqueTransversalNumber G ≤ n - 12

section Proof

-- ============================================================================
-- Section 1: Basic free sets, transversals, and good edge colourings
-- ============================================================================

private lemma transversal_le_of_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hk : k ≤ S.card)
    (hfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ K ⊆ S) :
    G.cliqueTransversalNumber ≤ n - k := by
  classical
  have hT : G.IsCliqueTransversal Sᶜ := by
    intro K hK
    by_contra! h
    apply hfree K hK
    intro x hx
    exact not_not.mp (by simpa only [mem_compl] using h x hx)
  have hle : G.cliqueTransversalNumber ≤ Sᶜ.card := csInf_le' ⟨Sᶜ, hT, rfl⟩
  rw [card_compl, Fintype.card_fin] at hle
  exact hle.trans (Nat.sub_le_sub_left hk n)

private lemma free_of_subset {V : Type*} {G : SimpleGraph V} {S T : Finset V}
    (hST : S ⊆ T) (hT : ∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ T) :
    ∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ S :=
  fun K hK hKS => hT K hK (hKS.trans hST)

private lemma free_of_indep {V : Type*} {G : SimpleGraph V} {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) :
    ∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ I := by
  intro K hK hKI
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hK.2
  exact hI (hKI ha) (hKI hb) hab (hK.1.1 ha hb hab)

private lemma free_of_neighbor_subset {V : Type*} {G : SimpleGraph V} {v : V} {S : Finset V}
    (hS : ∀ u ∈ S, G.Adj v u) :
    ∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ S := by
  classical
  intro K hK hKS
  have hcl : G.IsClique (↑(insert v K) : Set V) := by
    rw [coe_insert]
    exact hK.1.1.insert (fun u hu _ => hS u (hKS hu))
  have hv : v ∈ K := hK.1.2 hcl (subset_insert v K) (mem_insert_self v K)
  exact G.irrefl (hS v (hKS hv))

private lemma not_four_clique {V : Type*} {G : SimpleGraph V} (hG : G.CliqueFree 4)
    {v a b c : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
  classical
  apply hG {v, a, b, c}
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact hva
    · exact hvb
    · exact hvc
    · exact hva.symm
    · exact (hxy rfl).elim
    · exact hab
    · exact hac
    · exact hvb.symm
    · exact hab.symm
    · exact (hxy rfl).elim
    · exact hbc
    · exact hvc.symm
    · exact hac.symm
    · exact hbc.symm
    · exact (hxy rfl).elim
  · have hv1 : v ∉ ({a, b, c} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨hva.ne, hvb.ne, hvc.ne⟩
    have ha1 : a ∉ ({b, c} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨hab.ne, hac.ne⟩
    rw [card_insert_of_notMem hv1, card_insert_of_notMem ha1, card_pair hbc.ne]

private lemma free_iff_no_tri_no_lone {V : Type*} {G : SimpleGraph V}
    (hG : G.CliqueFree 4) (S : Finset V) :
    (∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ S) ↔
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c)) ∧
      (∀ a ∈ S, ∀ b ∈ S, G.Adj a b → ∃ z, G.Adj z a ∧ G.Adj z b) := by
  classical
  constructor
  · intro hfree
    refine ⟨?_, ?_⟩
    · intro a ha b hb c hc ⟨hab, hac, hbc⟩
      have h3 : G.IsNClique 3 {a, b, c} :=
        is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩
      have hmax : Maximal (fun t : Finset V => G.IsClique (t : Set V)) {a, b, c} := by
        refine ⟨h3.1, ?_⟩
        intro t ht hsub x hx
        by_contra hx3
        have ha' : a ∈ t := hsub (by simp)
        have hb' : b ∈ t := hsub (by simp)
        have hc' : c ∈ t := hsub (by simp)
        have hxa : x ≠ a := fun h => hx3 (by simp [h])
        have hxb : x ≠ b := fun h => hx3 (by simp [h])
        have hxc : x ≠ c := fun h => hx3 (by simp [h])
        exact not_four_clique hG (ht hx ha' hxa) (ht hx hb' hxb) (ht hx hc' hxc) hab hac hbc
      apply hfree {a, b, c} ⟨hmax, by rw [h3.2]; omega⟩
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · intro a ha b hb hab
      by_contra! hlone
      have h2 : G.IsClique (({a, b} : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · exact hab
        · exact hab.symm
        · exact (hxy rfl).elim
      have hmax : Maximal (fun t : Finset V => G.IsClique (t : Set V)) {a, b} := by
        refine ⟨h2, ?_⟩
        intro t ht hsub x hx
        by_contra hx2
        have hxa : x ≠ a := fun h => hx2 (by simp [h])
        have hxb : x ≠ b := fun h => hx2 (by simp [h])
        have ha' : a ∈ t := hsub (by simp)
        have hb' : b ∈ t := hsub (by simp)
        exact hlone x (ht hx ha' hxa) (ht hx hb' hxb)
      apply hfree {a, b} ⟨hmax, by rw [card_pair hab.ne]⟩
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
  · rintro ⟨htri, hlone⟩ K hK hKS
    by_cases h3 : 3 ≤ K.card
    · obtain ⟨t, htK, ht3⟩ := exists_subset_card_eq h3
      have hcl : G.IsNClique 3 t :=
        ⟨fun x hx y hy hxy => hK.1.1 (htK hx) (htK hy) hxy, ht3⟩
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hcl
      exact htri a (hKS (htK (by simp))) b (hKS (htK (by simp))) c (hKS (htK (by simp)))
        ⟨hab, hac, hbc⟩
    · have h2 : K.card = 2 := by have := hK.2; omega
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
      have hadj : G.Adj a b := hK.1.1 (by simp) (by simp) hab
      obtain ⟨z, hza, hzb⟩ := hlone a (hKS (by simp)) b (hKS (by simp)) hadj
      have hcl : G.IsClique (↑(insert z ({a, b} : Finset V)) : Set V) := by
        rw [coe_insert]
        apply hK.1.1.insert
        intro u hu _
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · exact hza
        · exact hzb
      have hz : z ∈ ({a, b} : Finset V) :=
        hK.1.2 hcl (subset_insert z ({a, b} : Finset V)) (mem_insert_self z ({a, b} : Finset V))
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact G.irrefl hza
      · exact G.irrefl hzb

private lemma H_attained {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ Q : SimpleGraph (Fin n), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet k s}
  have hne : sizes.Nonempty := ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
  have hfin : sizes.Finite := (Set.finite_Iic n).subset fun k hk => by
    obtain ⟨s, hs⟩ := hk F hF
    simpa [hs.card_eq] using card_le_univ s
  exact hne.csSup_mem hfin F hF

private lemma bound_of_good_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Sym2 (Fin n) → Bool)
    (hc : ∀ t : Finset (Fin n), G.IsNClique 3 t →
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = true) ∧
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = false)) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ (c s(x, y) = true ∨ ¬ ∃ z, G.Adj z x ∧ G.Adj z y)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim
      (fun ht => Or.inl (by rwa [Sym2.eq_swap]))
      (fun hl => Or.inr (fun ⟨z, hzy, hzx⟩ => hl ⟨z, hzx, hzy⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hF : F.CliqueFree 3 := by
    intro t ht
    have htG : G.IsNClique 3 t := ⟨fun x hx y hy hxy => (ht.1 hx hy hxy).1, ht.2⟩
    obtain ⟨a, ha, b, hb, hab, hfalse⟩ := (hc t htG).2
    have hFab := ht.1 ha hb hab
    have htri : ∃ z, G.Adj z a ∧ G.Adj z b := by
      have hne : ¬ t ⊆ {a, b} := by
        intro hsub
        have := card_le_card hsub
        rw [ht.2, card_pair hab] at this
        omega
      obtain ⟨z, hz, hz2⟩ := not_subset.mp hne
      have hza : z ≠ a := fun h => hz2 (by simp [h])
      have hzb : z ≠ b := fun h => hz2 (by simp [h])
      exact ⟨z, (ht.1 hz ha hza).1, (ht.1 hz hb hzb).1⟩
    have htrue : c s(a, b) = true := hFab.2.resolve_right (fun h => h htri)
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  obtain ⟨I, hI⟩ := H_attained F hF
  apply transversal_le_of_free G I hI.card_eq.ge
  intro K hK hKI
  by_cases h3 : 3 ≤ K.card
  · obtain ⟨t, htK, ht3⟩ := exists_subset_card_eq h3
    have htG : G.IsNClique 3 t := ⟨fun x hx y hy hxy => hK.1.1 (htK hx) (htK hy) hxy, ht3⟩
    obtain ⟨a, ha, b, hb, hab, htrue⟩ := (hc t htG).1
    exact hI.isIndepSet (hKI (htK ha)) (hKI (htK hb)) hab ⟨htG.1 ha hb hab, Or.inl htrue⟩
  · have h2 : K.card = 2 := by have := hK.2; omega
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
    have hadj : G.Adj a b := hK.1.1 (by simp) (by simp) hab
    have hlone : ¬ ∃ z, G.Adj z a ∧ G.Adj z b := by
      rintro ⟨z, hza, hzb⟩
      have hcl : G.IsClique (↑(insert z ({a, b} : Finset (Fin n))) : Set (Fin n)) := by
        rw [coe_insert]
        apply hK.1.1.insert
        intro u hu _
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · exact hza
        · exact hzb
      have hz : z ∈ ({a, b} : Finset (Fin n)) :=
        hK.1.2 hcl (subset_insert z ({a, b} : Finset (Fin n))) (mem_insert_self z ({a, b} : Finset (Fin n)))
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact G.irrefl hza
      · exact G.irrefl hzb
    exact hI.isIndepSet (hKI (by simp)) (hKI (by simp)) hab ⟨hadj, Or.inr hlone⟩

-- ============================================================================
-- Section 2: Minimal edge-Folkman core density and minimum degree >= 8
-- ============================================================================

private lemma has_both_signs {E : Type*} (s : Finset E) (z : E → ℚ)
    (htot : ∑ i ∈ s, z i = 0) (hnz : ∃ i ∈ s, z i ≠ 0) :
    (∃ i ∈ s, 0 < z i) ∧ ∃ j ∈ s, z j < 0 := by
  obtain ⟨i, hi, hne⟩ := hnz
  constructor
  · by_contra! hle
    have hneg : ∑ j ∈ s, -z j = 0 := by simp [htot]
    have h0 := (sum_eq_zero_iff_of_nonneg (fun j hj => neg_nonneg.mpr (hle j hj))).mp hneg i hi
    exact hne (neg_eq_zero.mp h0)
  · by_contra! hge
    exact hne ((sum_eq_zero_iff_of_nonneg hge).mp htot i hi)

private lemma hypergraph_density {E T : Type*} [Fintype E] [Fintype T] (row : T → Finset E)
    (hram : ¬ ∃ c : E → Bool, ∀ t, (∃ i ∈ row t, c i = true) ∧ ∃ j ∈ row t, c j = false)
    (hmin : ∀ e : E, ∃ c : E → Bool, ∀ t, e ∉ row t →
      (∃ i ∈ row t, c i = true) ∧ ∃ j ∈ row t, c j = false) :
    Fintype.card E ≤ Fintype.card T := by
  classical
  let A : (E → ℚ) →ₗ[ℚ] (T → ℚ) :=
    { toFun := fun f t => ∑ i ∈ row t, f i
      map_add' := by intros; ext; simp [Finset.sum_add_distrib]
      map_smul' := by intros; ext; simp [Finset.mul_sum] }
  have htriv : ∀ z, A z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := by
      by_contra! hall
      exact hne (funext hall)
    obtain ⟨c, hc⟩ := hmin e
    let c' (i : E) : Bool := if z i = 0 then c i else decide (0 < z i)
    apply hram
    refine ⟨c', fun t => ?_⟩
    by_cases h0 : ∀ i ∈ row t, z i = 0
    · obtain ⟨⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩ := hc t (fun h => he (h0 e h))
      exact ⟨⟨i, hi, by simp [c', h0 i hi, hci]⟩, ⟨j, hj, by simp [c', h0 j hj, hcj]⟩⟩
    · push Not at h0
      obtain ⟨⟨i, hi, hpos⟩, ⟨j, hj, hneg⟩⟩ := has_both_signs (row t) z (congrFun hz t) h0
      exact ⟨⟨i, hi, by simp [c', hpos.ne', hpos]⟩, ⟨j, hj, by simp [c', hneg.ne, hneg.not_gt]⟩⟩
  have hinj : Function.Injective A := fun x y hxy =>
    sub_eq_zero.mp (htriv (x - y) (by simp [map_sub, hxy]))
  simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hinj

private lemma minimal_core_props {n : ℕ} (hlink : H1) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (harrow : ¬ ∃ c : Sym2 (Fin n) → Bool, ∀ t : Finset (Fin n), G.IsNClique 3 t →
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = true) ∧
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = false)) :
    ∃ C : SimpleGraph (Fin n), C ≤ G ∧
      (∃ u v, C.Adj u v) ∧
      (∀ a b, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b) ∧
      (C.edgeFinset.card ≤ (C.cliqueFinset 3).card) ∧
      (∀ v, 0 < C.degree v → 8 ≤ C.degree v) := by
  classical
  let Good (D : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Bool) : Prop :=
    ∀ t : Finset (Fin n), D.IsNClique 3 t →
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = true) ∧
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = false)
  let Arr (D : SimpleGraph (Fin n)) : Prop := ¬ ∃ c, Good D c
  obtain ⟨C, hCG, hmin⟩ := exists_minimal_le_of_wellFoundedLT Arr G harrow
  have hC4 : C.CliqueFree 4 := hG.anti hCG
  have hbelow : ∀ D < C, ∃ c, Good D c := by
    intro D hlt
    by_contra hnc
    exact hlt.not_ge (hmin.2 hnc hlt.le)
  have hedge : ∃ u v, C.Adj u v := by
    by_contra! hno
    apply hmin.1
    refine ⟨fun _ => false, fun t ht => ?_⟩
    obtain ⟨a, b, _, hab, _⟩ := is3Clique_iff.mp ht
    exact (hno a b hab).elim
  have hdelE : ∀ e ∈ C.edgeSet, ∃ c, Good (C.deleteEdges {e}) c := by
    intro e he
    apply hbelow (C.deleteEdges {e})
    refine lt_of_le_of_ne (C.deleteEdges_le _) ?_
    intro heq
    have hnot : e ∉ (C.deleteEdges {e}).edgeSet := by simp [SimpleGraph.edgeSet_deleteEdges]
    rw [heq] at hnot
    exact hnot he
  have htri : ∀ a b, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b := by
    intro a b hab
    obtain ⟨c, hc⟩ := hdelE s(a, b) hab
    by_contra! hno
    apply hmin.1
    refine ⟨c, fun t ht => hc t ⟨?_, ht.2⟩⟩
    intro x hx y hy hxy
    refine SimpleGraph.deleteEdges_adj.mpr ⟨ht.1 hx hy hxy, ?_⟩
    intro heq
    change s(x, y) = s(a, b) at heq
    have hne : ¬ t ⊆ {a, b} := by
      intro hsub
      have := card_le_card hsub
      rw [ht.2, card_pair hab.ne] at this
      omega
    obtain ⟨z, hz, hz2⟩ := not_subset.mp hne
    have hza : z ≠ a := fun h => hz2 (by simp [h])
    have hzb : z ≠ b := fun h => hz2 (by simp [h])
    have hmem : a ∈ t ∧ b ∈ t := by
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hx, hy⟩
      · exact ⟨hy, hx⟩
    exact hno z (ht.1 hz hmem.1 hza) (ht.1 hz hmem.2 hzb)
  have hdens : C.edgeFinset.card ≤ (C.cliqueFinset 3).card := by
    let E := {e : Sym2 (Fin n) // e ∈ C.edgeFinset}
    let T := {t : Finset (Fin n) // t ∈ C.cliqueFinset 3}
    let pairs (t : Finset (Fin n)) : Finset (Sym2 (Fin n)) := t.sym2.filter (fun e => ¬ e.IsDiag)
    let row (t : T) : Finset E := (pairs t.val).subtype (· ∈ C.edgeFinset)
    have hmem_pairs : ∀ {t : Finset (Fin n)} {a b : Fin n},
        s(a, b) ∈ pairs t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := by
      intro t a b; simp [pairs, and_assoc]
    have hpairs_edge : ∀ (t : T) {e : Sym2 (Fin n)}, e ∈ pairs t.val → e ∈ C.edgeFinset := by
      intro t e he
      induction e using Sym2.inductionOn with
      | _ a b =>
        obtain ⟨ha, hb, hab⟩ := hmem_pairs.mp he
        have ht3 : C.IsNClique 3 t.val := (C.mem_cliqueFinset_iff).mp t.property
        exact C.mem_edgeFinset.mpr (ht3.1 ha hb hab)
    have hram : ¬ ∃ c : E → Bool, ∀ t : T,
        (∃ i ∈ row t, c i = true) ∧ ∃ j ∈ row t, c j = false := by
      rintro ⟨c, hc⟩
      apply hmin.1
      refine ⟨fun e => if h : e ∈ C.edgeFinset then c ⟨e, h⟩ else false, fun t ht => ?_⟩
      let t' : T := ⟨t, C.mem_cliqueFinset_iff.mpr ht⟩
      obtain ⟨⟨⟨e, he⟩, her, hce⟩, ⟨⟨f, hf⟩, hfr, hcf⟩⟩ := hc t'
      have hep : e ∈ pairs t := Finset.mem_subtype.mp her
      have hfp : f ∈ pairs t := Finset.mem_subtype.mp hfr
      constructor
      · induction e using Sym2.inductionOn with
        | _ a b =>
          obtain ⟨ha, hb, hab⟩ := hmem_pairs.mp hep
          exact ⟨a, ha, b, hb, hab, by simpa [he] using hce⟩
      · induction f using Sym2.inductionOn with
        | _ a b =>
          obtain ⟨ha, hb, hab⟩ := hmem_pairs.mp hfp
          exact ⟨a, ha, b, hb, hab, by simpa [hf] using hcf⟩
    have hmine : ∀ e : E, ∃ c : E → Bool, ∀ t : T, e ∉ row t →
        (∃ i ∈ row t, c i = true) ∧ ∃ j ∈ row t, c j = false := by
      intro e
      obtain ⟨c, hc⟩ := hdelE e.val (C.mem_edgeFinset.mp e.property)
      refine ⟨fun x => c x.val, fun t hnot => ?_⟩
      have ht3 : C.IsNClique 3 t.val := C.mem_cliqueFinset_iff.mp t.property
      have hsurv : (C.deleteEdges {e.val}).IsNClique 3 t.val := by
        refine ⟨?_, ht3.2⟩
        intro a ha b hb hab
        refine SimpleGraph.deleteEdges_adj.mpr ⟨ht3.1 ha hb hab, ?_⟩
        intro heq
        change s(a, b) = e.val at heq
        apply hnot
        refine Finset.mem_subtype.mpr ?_
        rw [← heq]
        exact hmem_pairs.mpr ⟨ha, hb, hab⟩
      obtain ⟨⟨a, ha, b, hb, hab, htrue⟩, ⟨a', ha', b', hb', hab', hfalse⟩⟩ := hc t.val hsurv
      have hp1 : s(a, b) ∈ pairs t.val := hmem_pairs.mpr ⟨ha, hb, hab⟩
      have hp2 : s(a', b') ∈ pairs t.val := hmem_pairs.mpr ⟨ha', hb', hab'⟩
      exact ⟨⟨⟨s(a, b), hpairs_edge t hp1⟩, Finset.mem_subtype.mpr hp1, htrue⟩,
             ⟨⟨s(a', b'), hpairs_edge t hp2⟩, Finset.mem_subtype.mpr hp2, hfalse⟩⟩
    have hcard := hypergraph_density row hram hmine
    have hEcard : Fintype.card E = C.edgeFinset.card := Fintype.card_coe C.edgeFinset
    have hTcard : Fintype.card T = (C.cliqueFinset 3).card := Fintype.card_coe (C.cliqueFinset 3)
    omega
  have hdeg : ∀ v, 0 < C.degree v → 8 ≤ C.degree v := by
    intro v hv
    by_contra! hlt
    obtain ⟨u0, hu0⟩ := (C.degree_pos_iff_exists_adj v).mp hv
    obtain ⟨c, hc⟩ := hbelow (C.deleteIncidenceSet v) (by
      refine lt_of_le_of_ne (C.deleteIncidenceSet_le _) ?_
      intro heq
      have hbad : (C.deleteIncidenceSet v).Adj v u0 := by rwa [heq]
      exact (SimpleGraph.deleteIncidenceSet_adj.mp hbad).2.1 rfl)
    let N := C.neighborFinset v
    let k := N.card
    have hk : k ≤ 7 := by
      have : k = C.degree v := C.card_neighborFinset_eq_degree v
      omega
    let eqv : Fin k ≃ N := (Fintype.equivFinOfCardEq (Fintype.card_coe N)).symm
    let L : SimpleGraph (Fin k) := {
      Adj := fun i j => C.Adj (eqv i).val (eqv j).val
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => C.irrefl h⟩ }
    have hL3 : L.CliqueFree 3 := by
      intro t ht
      obtain ⟨i, j, l, hij, hil, hjl, rfl⟩ := is3Clique_iff.mp ht
      exact not_four_clique hC4
        ((C.mem_neighborFinset v _).mp (eqv i).property)
        ((C.mem_neighborFinset v _).mp (eqv j).property)
        ((C.mem_neighborFinset v _).mp (eqv l).property)
        hij hil hjl
    let colEdge (i j : Fin k) : Bool := c s((eqv i).val, (eqv j).val)
    have hsym : ∀ i j, colEdge i j = colEdge j i := fun i j => by simp [colEdge, Sym2.eq_swap]
    obtain ⟨d, hd⟩ := hlink k L hk hL3 colEdge hsym
    let colOf (x : Fin n) : Bool := if hx : x ∈ N then d (eqv.symm ⟨x, hx⟩) else false
    let c' : Sym2 (Fin n) → Bool := Sym2.lift ⟨fun x y =>
      if x = v then colOf y else if y = v then colOf x else c s(x, y), by
      intro x y
      by_cases hx : x = v <;> by_cases hy : y = v
      · simp [hx, hy]
      · simp [hx, hy]
      · simp [hx, hy]
      · simp [hx, hy, Sym2.eq_swap]⟩
    apply hmin.1
    refine ⟨c', fun t ht => ?_⟩
    by_cases hvt : v ∈ t
    · have hcard : (t.erase v).card = 2 := by rw [card_erase_of_mem hvt, ht.2]
      obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp hcard
      have hav_ne : a ≠ v := (mem_erase.mp (by rw [heq]; simp)).1
      have hbv_ne : b ≠ v := (mem_erase.mp (by rw [heq]; simp)).1
      have htab : t = {v, a, b} := by rw [← insert_erase hvt, heq]
      subst htab
      have hva : C.Adj v a := ht.1 (by simp) (by simp) hav_ne.symm
      have hvb : C.Adj v b := ht.1 (by simp) (by simp) hbv_ne.symm
      have hab' : C.Adj a b := ht.1 (by simp) (by simp) hab
      have haN : a ∈ N := (C.mem_neighborFinset v a).mpr hva
      have hbN : b ∈ N := (C.mem_neighborFinset v b).mpr hvb
      let i := eqv.symm ⟨a, haN⟩
      let j := eqv.symm ⟨b, hbN⟩
      have heqvi : (eqv i).val = a := by simp [i]
      have heqvj : (eqv j).val = b := by simp [j]
      have hLij : L.Adj i j := by change C.Adj (eqv i).val (eqv j).val; rw [heqvi, heqvj]; exact hab'
      have hnot := hd i j hLij
      have hcva : c' s(v, a) = d i := by simp [c', colOf, haN, i]
      have hcvb : c' s(v, b) = d j := by simp [c', colOf, hbN, j]
      have hcab : c' s(a, b) = colEdge i j := by
        simp [c', hav_ne, hbv_ne, colEdge, heqvi, heqvj]
      cases h1 : d i <;> cases h2 : d j <;> cases h3 : colEdge i j
      · exact (hnot ⟨by rw [h1, h3], by rw [h2, h3]⟩).elim
      · exact ⟨⟨a, by simp, b, by simp, hab, by rw [hcab, h3]⟩,
               ⟨v, by simp, a, by simp, hva.ne, by rw [hcva, h1]⟩⟩
      · exact ⟨⟨v, by simp, b, by simp, hvb.ne, by rw [hcvb, h2]⟩,
               ⟨v, by simp, a, by simp, hva.ne, by rw [hcva, h1]⟩⟩
      · exact ⟨⟨v, by simp, b, by simp, hvb.ne, by rw [hcvb, h2]⟩,
               ⟨v, by simp, a, by simp, hva.ne, by rw [hcva, h1]⟩⟩
      · exact ⟨⟨v, by simp, a, by simp, hva.ne, by rw [hcva, h1]⟩,
               ⟨v, by simp, b, by simp, hvb.ne, by rw [hcvb, h2]⟩⟩
      · exact ⟨⟨v, by simp, a, by simp, hva.ne, by rw [hcva, h1]⟩,
               ⟨v, by simp, b, by simp, hvb.ne, by rw [hcvb, h2]⟩⟩
      · exact ⟨⟨v, by simp, a, by simp, hva.ne, by rw [hcva, h1]⟩,
               ⟨a, by simp, b, by simp, hab, by rw [hcab, h3]⟩⟩
      · exact (hnot ⟨by rw [h1, h3], by rw [h2, h3]⟩).elim
    · have hsurv : (C.deleteIncidenceSet v).IsNClique 3 t := by
        refine ⟨?_, ht.2⟩
        intro a ha b hb hab
        exact SimpleGraph.deleteIncidenceSet_adj.mpr
          ⟨ht.1 ha hb hab, fun h => hvt (h ▸ ha), fun h => hvt (h ▸ hb)⟩
      obtain ⟨⟨a, ha, b, hb, hab, htrue⟩, ⟨a', ha', b', hb', hab', hfalse⟩⟩ := hc t hsurv
      have hav : a ≠ v := fun h => hvt (h ▸ ha)
      have hbv : b ≠ v := fun h => hvt (h ▸ hb)
      have hav' : a' ≠ v := fun h => hvt (h ▸ ha')
      have hbv' : b' ≠ v := fun h => hvt (h ▸ hb')
      exact ⟨⟨a, ha, b, hb, hab, by simp [c', hav, hbv, htrue]⟩,
             ⟨a', ha', b', hb', hab', by simp [c', hav', hbv', hfalse]⟩⟩
  exact ⟨C, hCG, hedge, htri, hdens, hdeg⟩

-- ============================================================================
-- Section 3: Exact Core-Averaged Safe-Outsider Identity
-- ============================================================================

private lemma sum_link_eq_six_tri {n : ℕ} (C : SimpleGraph (Fin n)) :
    (∑ v : Fin n, ∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) =
      6 * (C.cliqueFinset 3).card := by
  classical
  have hstep : ∀ v : Fin n,
      (∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) =
        2 * ((C.cliqueFinset 3).filter (fun t => v ∈ t)).card := by
    intro v
    let P := (C.neighborFinset v ×ˢ C.neighborFinset v).filter (fun p => C.Adj p.1 p.2)
    have hP : P.card = ∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.card_filter]
    rw [← hP]
    let f : Fin n × Fin n → Finset (Fin n) := fun p => {v, p.1, p.2}
    have hmaps : ∀ p ∈ P, f p ∈ (C.cliqueFinset 3).filter (fun t => v ∈ t) := by
      intro ⟨a, b⟩ hp
      simp only [P, mem_filter, mem_product, C.mem_neighborFinset] at hp
      refine mem_filter.mpr ⟨C.mem_cliqueFinset_iff.mpr ?_, by simp [f]⟩
      exact is3Clique_triple_iff.mpr ⟨hp.1.1, hp.1.2, hp.2⟩
    have hfib : ∀ t ∈ (C.cliqueFinset 3).filter (fun t => v ∈ t),
        (P.filter (fun p => f p = t)).card = 2 := by
      intro t ht
      obtain ⟨ht3, hvt⟩ := mem_filter.mp ht
      have hcl := C.mem_cliqueFinset_iff.mp ht3
      have hcard : (t.erase v).card = 2 := by rw [card_erase_of_mem hvt, hcl.2]
      obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp hcard
      have ht_eq : t = {v, a, b} := by rw [← insert_erase hvt, heq]
      have hva : C.Adj v a := hcl.1 hvt (by rw [ht_eq]; simp) (by
        intro h; have : a ∈ t.erase v := by rw [heq]; simp
        exact (mem_erase.mp this).1 h.symm)
      have hvb : C.Adj v b := hcl.1 hvt (by rw [ht_eq]; simp) (by
        intro h; have : b ∈ t.erase v := by rw [heq]; simp
        exact (mem_erase.mp this).1 h.symm)
      have hab' : C.Adj a b := hcl.1 (by rw [ht_eq]; simp) (by rw [ht_eq]; simp) hab
      have hset : P.filter (fun p => f p = t) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp only [P, f, mem_filter, mem_product, C.mem_neighborFinset, mem_insert, mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨⟨hvx, hvy⟩, hxy⟩, hfeq⟩
          have hx : x ∈ ({a, b} : Finset (Fin n)) := by
            have hx1 : x ∈ t := by rw [← hfeq]; simp
            have hx2 : x ∈ t.erase v := mem_erase.mpr ⟨hvx.ne.symm, hx1⟩
            rwa [heq] at hx2
          have hy : y ∈ ({a, b} : Finset (Fin n)) := by
            have hy1 : y ∈ t := by rw [← hfeq]; simp
            have hy2 : y ∈ t.erase v := mem_erase.mpr ⟨hvy.ne.symm, hy1⟩
            rwa [heq] at hy2
          simp only [mem_insert, mem_singleton] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact (C.irrefl hxy).elim
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact (C.irrefl hxy).elim
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨⟨⟨hva, hvb⟩, hab'⟩, ht_eq.symm⟩
          · refine ⟨⟨⟨hvb, hva⟩, hab'.symm⟩, ?_⟩
            rw [ht_eq]; ext z; simp [or_comm]
      rw [hset, card_pair]
      intro h
      exact hab (Prod.mk.inj h).1
    have hcnt := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hcnt, Finset.sum_congr rfl hfib]
    simp [mul_comm]
  simp_rw [hstep, ← Finset.mul_sum]
  have hsum3 : (∑ v : Fin n, ((C.cliqueFinset 3).filter (fun t => v ∈ t)).card) =
      3 * (C.cliqueFinset 3).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have h3 : ∀ t ∈ C.cliqueFinset 3, (∑ v : Fin n, if v ∈ t then 1 else 0) = 3 := by
      intro t ht
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact (C.mem_cliqueFinset_iff.mp ht).2
    rw [Finset.sum_congr rfl h3]
    simp [mul_comm]
  rw [hsum3]
  omega


-- ============================================================================
-- Section 4: Elementary small Ramsey bounds & free sets on 6 and 9 vertices
-- ============================================================================

private lemma indep_two_of_K4_free {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (A : Finset V) (hA : 4 ≤ A.card) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = 2 := by
  classical
  by_contra! hno
  obtain ⟨S, hSA, hS4⟩ := exists_subset_card_eq hA
  apply hG S
  refine ⟨?_, hS4⟩
  intro x hx y hy hxy
  by_contra hna
  apply hno {x, y}
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl <;> exact hSA ‹_›
  · intro u hu v hv huv hadj
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact huv rfl
    · exact hna hadj
    · exact hna hadj.symm
    · exact huv rfl
  · exact card_pair hxy

private lemma indep_two_of_K3_free_on {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (h3 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c))
    (hA : 3 ≤ A.card) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = 2 := by
  classical
  obtain ⟨S, hSA, hS3⟩ := exists_subset_card_eq hA
  obtain ⟨a, S', haS', heqS, hS'2⟩ := Finset.card_eq_succ.mp hS3
  obtain ⟨b, c, hbc, rfl⟩ := card_eq_two.mp hS'2
  have haS : a ∈ A := hSA (by rw [← heqS]; simp)
  have hbS : b ∈ A := hSA (by rw [← heqS]; simp)
  have hcS : c ∈ A := hSA (by rw [← heqS]; simp)
  have hab_ne : a ≠ b := fun h => haS' (by simp [h])
  have hac_ne : a ≠ c := fun h => haS' (by simp [h])
  by_cases hab : G.Adj a b
  · by_cases hac : G.Adj a c
    · by_cases hbc' : G.Adj b c
      · exact (h3 a haS b hbS c hcS ⟨hab, hac, hbc'⟩).elim
      · refine ⟨{b, c}, fun x hx => ?_, fun u hu v hv huv hadj => ?_, card_pair hbc⟩
        · simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
        · simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact huv rfl
          · exact hbc' hadj
          · exact hbc' hadj.symm
          · exact huv rfl
    · refine ⟨{a, c}, fun x hx => ?_, fun u hu v hv huv hadj => ?_, card_pair hac_ne⟩
      · simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
      · simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact huv rfl
        · exact hac hadj
        · exact hac hadj.symm
        · exact huv rfl
  · refine ⟨{a, b}, fun x hx => ?_, fun u hu v hv huv hadj => ?_, card_pair hab_ne⟩
    · simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    · simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact huv rfl
      · exact hab hadj
      · exact hab hadj.symm
      · exact huv rfl

private lemma indep_three_of_K3_free_on {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (h3 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c))
    (hA : 6 ≤ A.card) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = 3 := by
  classical
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < A.card)
  let N := A.filter (G.Adj v)
  let M := (A.erase v).filter (fun u => ¬ G.Adj v u)
  have hpart : N.card + M.card = A.card - 1 := by
    have hdis : Disjoint N M := disjoint_left.mpr fun x h1 h2 => (mem_filter.mp h2).2 (mem_filter.mp h1).2
    have hunion : N ∪ M = A.erase v := by
      ext x
      simp only [N, M, mem_union, mem_filter, mem_erase]
      constructor
      · rintro (⟨hx, hxv⟩ | ⟨⟨hxv, hx⟩, _⟩)
        · exact ⟨hxv.ne.symm, hx⟩
        · exact ⟨hxv, hx⟩
      · rintro ⟨hne, hx⟩
        by_cases h : G.Adj v x
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨⟨hne, hx⟩, h⟩
    rw [← card_union_of_disjoint hdis, hunion, card_erase_of_mem hv]
  by_cases hN : 3 ≤ N.card
  · obtain ⟨I, hIN, hI3⟩ := exists_subset_card_eq hN
    refine ⟨I, hIN.trans (filter_subset _ _), ?_, hI3⟩
    intro x hx y hy hxy hadj
    have hx' := mem_filter.mp (hIN hx)
    have hy' := mem_filter.mp (hIN hy)
    exact h3 v hv x hx'.1 y hy'.1 ⟨hx'.2, hy'.2, hadj⟩
  · have hM : 3 ≤ M.card := by omega
    have hM3 : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) :=
      fun a ha b hb c hc => h3 a (erase_subset v A (filter_subset _ _ ha))
        b (erase_subset v A (filter_subset _ _ hb)) c (erase_subset v A (filter_subset _ _ hc))
    obtain ⟨J, hJM, hJi, hJ2⟩ := indep_two_of_K3_free_on G M hM3 hM
    have hvJ : v ∉ J := fun h => (mem_erase.mp (mem_filter.mp (hJM h)).1).1 rfl
    refine ⟨insert v J, insert_subset_iff.mpr ⟨hv, hJM.trans ((filter_subset _ _).trans (erase_subset _ _))⟩,
      ?_, by rw [card_insert_of_notMem hvJ, hJ2]⟩
    intro x hx y hy hxy hadj
    simp only [coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact (mem_filter.mp (hJM hy)).2 hadj
    · exact (mem_filter.mp (hJM hx)).2 hadj.symm
    · exact hJi hx hy hxy hadj

private lemma indep_four_of_K3_free_on {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (h3 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c))
    (hA : 9 ≤ A.card) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = 4 := by
  classical
  obtain ⟨S, hSA, hS9⟩ := exists_subset_card_eq hA
  have hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) :=
    fun a ha b hb c hc => h3 a (hSA ha) b (hSA hb) c (hSA hc)
  by_cases h4 : ∃ v ∈ S, 4 ≤ (S.filter (G.Adj v)).card
  · obtain ⟨v, hv, hdv⟩ := h4
    obtain ⟨I, hIN, hI4⟩ := exists_subset_card_eq hdv
    refine ⟨I, hIN.trans ((filter_subset _ _).trans hSA), ?_, hI4⟩
    intro x hx y hy hxy hadj
    have hx' := mem_filter.mp (hIN hx)
    have hy' := mem_filter.mp (hIN hy)
    exact hS3 v hv x hx'.1 y hy'.1 ⟨hx'.2, hy'.2, hadj⟩
  · push Not at h4
    have hex : ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2 := by
      by_contra! hge3
      have hall3 : ∀ v ∈ S, (S.filter (G.Adj v)).card = 3 := fun v hv => by
        have := h4 v hv; have := hge3 v hv; omega
      have hsum : (∑ v ∈ S, (S.filter (G.Adj v)).card) = 27 := by
        rw [sum_congr rfl hall3]; simp [hS9]
      let E := (S ×ˢ S).filter (fun p => G.Adj p.1 p.2)
      have hEcard : E.card = ∑ v ∈ S, (S.filter (G.Adj v)).card := by
        rw [card_filter, sum_product]
        exact sum_congr rfl fun v _ => by rw [card_filter]
      have heven : Even E.card := by
        let H := G.induce (S : Set V)
        have hEq : E.card = ∑ v : S, H.degree v := by
          rw [hEcard]
          rw [← Finset.sum_attach S (fun v => (S.filter (G.Adj v)).card)]
          apply sum_congr rfl
          intro v _
          rw [← H.card_neighborFinset_eq_degree v]
          refine Finset.card_bij (fun x hx => ⟨x, (mem_filter.mp hx).1⟩) ?_ ?_ ?_
          · intro x hx; exact (H.mem_neighborFinset v ⟨x, (mem_filter.mp hx).1⟩).mpr (mem_filter.mp hx).2
          · intro x1 _ x2 _ h; exact congrArg Subtype.val h
          · intro y hy
            exact ⟨y.val, mem_filter.mpr ⟨y.property, (H.mem_neighborFinset v y).mp hy⟩, rfl⟩
        have hdegSum : ∑ v : S, H.degree v = 2 * H.edgeFinset.card :=
          SimpleGraph.sum_degrees_eq_twice_card_edges H
        rw [hEq, hdegSum]
        exact ⟨H.edgeFinset.card, by ring⟩
      rw [hEcard, hsum] at heven
      obtain ⟨r, hr⟩ := heven
      omega
    obtain ⟨v, hv, hdv⟩ := hex
    let M := (S.erase v).filter (fun u => ¬ G.Adj v u)
    have hMcard : 6 ≤ M.card := by
      have hdis : Disjoint (S.filter (G.Adj v)) M :=
        disjoint_left.mpr fun x h1 h2 => (mem_filter.mp h2).2 (mem_filter.mp h1).2
      have hunion : (S.filter (G.Adj v)) ∪ M = S.erase v := by
        ext x
        simp only [M, mem_union, mem_filter, mem_erase]
        constructor
        · rintro (⟨hx, hxv⟩ | ⟨⟨hne, hx⟩, _⟩)
          · exact ⟨hxv.ne.symm, hx⟩
          · exact ⟨hne, hx⟩
        · rintro ⟨hne, hx⟩
          by_cases h : G.Adj v x
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨⟨hne, hx⟩, h⟩
      have htot := card_union_of_disjoint hdis
      rw [hunion, card_erase_of_mem hv, hS9] at htot
      omega
    have hM3 : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) :=
      fun a ha b hb c hc => hS3 a (erase_subset v S (filter_subset _ _ ha))
        b (erase_subset v S (filter_subset _ _ hb)) c (erase_subset v S (filter_subset _ _ hc))
    obtain ⟨J, hJM, hJi, hJ3⟩ := indep_three_of_K3_free_on G M hM3 hMcard
    have hvJ : v ∉ J := fun h => (mem_erase.mp (mem_filter.mp (hJM h)).1).1 rfl
    refine ⟨insert v J, insert_subset_iff.mpr ⟨hSA hv, hJM.trans ((filter_subset _ _).trans ((erase_subset _ _).trans hSA))⟩,
      ?_, by rw [card_insert_of_notMem hvJ, hJ3]⟩
    intro x hx y hy hxy hadj
    simp only [coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact (mem_filter.mp (hJM hy)).2 hadj
    · exact (mem_filter.mp (hJM hx)).2 hadj.symm
    · exact hJi hx hy hxy hadj

private lemma indep_three_of_K4_free {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (A : Finset V) (hA : 9 ≤ A.card) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = 3 := by
  classical
  obtain ⟨S, hSA, hS9⟩ := exists_subset_card_eq hA
  by_cases h6 : ∃ v ∈ S, 6 ≤ (S.filter (G.Adj v)).card
  · obtain ⟨v, hv, hdv⟩ := h6
    let N := S.filter (G.Adj v)
    have hN3 : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := fun a ha b hb c hc ⟨hab, hac, hbc⟩ =>
      not_four_clique hG (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2 hab hac hbc
    obtain ⟨I, hIN, hIi, hI3⟩ := indep_three_of_K3_free_on G N hN3 hdv
    exact ⟨I, hIN.trans ((filter_subset _ _).trans hSA), hIi, hI3⟩
  · push Not at h6
    have hex : ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 4 := by
      by_contra! hge5
      have hall5 : ∀ v ∈ S, (S.filter (G.Adj v)).card = 5 := fun v hv => by
        have := h6 v hv; have := hge5 v hv; omega
      have hsum : (∑ v ∈ S, (S.filter (G.Adj v)).card) = 45 := by
        rw [sum_congr rfl hall5]; simp [hS9]
      let H := G.induce (S : Set V)
      have hEq : (∑ v ∈ S, (S.filter (G.Adj v)).card) = ∑ v : S, H.degree v := by
        rw [← Finset.sum_attach S (fun v => (S.filter (G.Adj v)).card)]
        apply sum_congr rfl
        intro v _
        rw [← H.card_neighborFinset_eq_degree v]
        refine Finset.card_bij (fun x hx => ⟨x, (mem_filter.mp hx).1⟩) ?_ ?_ ?_
        · intro x hx; exact (H.mem_neighborFinset v ⟨x, (mem_filter.mp hx).1⟩).mpr (mem_filter.mp hx).2
        · intro x1 _ x2 _ h; exact congrArg Subtype.val h
        · intro y hy
          exact ⟨y.val, mem_filter.mpr ⟨y.property, (H.mem_neighborFinset v y).mp hy⟩, rfl⟩
      have hdegSum : ∑ v : S, H.degree v = 2 * H.edgeFinset.card :=
        SimpleGraph.sum_degrees_eq_twice_card_edges H
      rw [hEq, hdegSum] at hsum
      omega
    obtain ⟨v, hv, hdv⟩ := hex
    let M := (S.erase v).filter (fun u => ¬ G.Adj v u)
    have hMcard : 4 ≤ M.card := by
      have hdis : Disjoint (S.filter (G.Adj v)) M :=
        disjoint_left.mpr fun x h1 h2 => (mem_filter.mp h2).2 (mem_filter.mp h1).2
      have hunion : (S.filter (G.Adj v)) ∪ M = S.erase v := by
        ext x
        simp only [M, mem_union, mem_filter, mem_erase]
        constructor
        · rintro (⟨hx, hxv⟩ | ⟨⟨hne, hx⟩, _⟩)
          · exact ⟨hxv.ne.symm, hx⟩
          · exact ⟨hne, hx⟩
        · rintro ⟨hne, hx⟩
          by_cases h : G.Adj v x
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨⟨hne, hx⟩, h⟩
      have htot := card_union_of_disjoint hdis
      rw [hunion, card_erase_of_mem hv, hS9] at htot
      omega
    obtain ⟨J, hJM, hJi, hJ2⟩ := indep_two_of_K4_free G hG M hMcard
    have hvJ : v ∉ J := fun h => (mem_erase.mp (mem_filter.mp (hJM h)).1).1 rfl
    refine ⟨insert v J, insert_subset_iff.mpr ⟨hSA hv, hJM.trans ((filter_subset _ _).trans ((erase_subset _ _).trans hSA))⟩,
      ?_, by rw [card_insert_of_notMem hvJ, hJ2]⟩
    intro x hx y hy hxy hadj
    simp only [coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact (mem_filter.mp (hJM hy)).2 hadj
    · exact (mem_filter.mp (hJM hx)).2 hadj.symm
    · exact hJi hx hy hxy hadj

private lemma indep_four_of_K4_free {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (A : Finset V) (hA : 18 ≤ A.card) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = 4 := by
  classical
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < A.card)
  let N := A.filter (G.Adj v)
  let M := (A.erase v).filter (fun u => ¬ G.Adj v u)
  have hpart : N.card + M.card = A.card - 1 := by
    have hdis : Disjoint N M := disjoint_left.mpr fun x h1 h2 => (mem_filter.mp h2).2 (mem_filter.mp h1).2
    have hunion : N ∪ M = A.erase v := by
      ext x
      simp only [N, M, mem_union, mem_filter, mem_erase]
      constructor
      · rintro (⟨hx, hxv⟩ | ⟨⟨hne, hx⟩, _⟩)
        · exact ⟨hxv.ne.symm, hx⟩
        · exact ⟨hne, hx⟩
      · rintro ⟨hne, hx⟩
        by_cases h : G.Adj v x
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨⟨hne, hx⟩, h⟩
    rw [← card_union_of_disjoint hdis, hunion, card_erase_of_mem hv]
  by_cases hN : 9 ≤ N.card
  · have hN3 : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := fun a ha b hb c hc ⟨hab, hac, hbc⟩ =>
      not_four_clique hG (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2 hab hac hbc
    obtain ⟨I, hIN, hIi, hI4⟩ := indep_four_of_K3_free_on G N hN3 hN
    exact ⟨I, hIN.trans (filter_subset _ _), hIi, hI4⟩
  · have hM : 9 ≤ M.card := by omega
    obtain ⟨J, hJM, hJi, hJ3⟩ := indep_three_of_K4_free G hG M hM
    have hvJ : v ∉ J := fun h => (mem_erase.mp (mem_filter.mp (hJM h)).1).1 rfl
    refine ⟨insert v J, insert_subset_iff.mpr ⟨hv, hJM.trans ((filter_subset _ _).trans (erase_subset _ _))⟩,
      ?_, by rw [card_insert_of_notMem hvJ, hJ3]⟩
    intro x hx y hy hxy hadj
    simp only [coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact (mem_filter.mp (hJM hy)).2 hadj
    · exact (mem_filter.mp (hJM hx)).2 hadj.symm
    · exact hJi hx hy hxy hadj

private lemma free_three_of_six {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (W : Finset V) (hW : 6 ≤ W.card) :
    ∃ T ⊆ W, (∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 3 := by
  classical
  by_cases htri : ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := htri
    have h3card : ({a, b, c} : Finset V).card = 3 := by
      have ha' : a ∉ ({b, c} : Finset V) := by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨hab.ne, hac.ne⟩
      rw [card_insert_of_notMem ha', card_pair hbc.ne]
    have hrem : 0 < (W \ {a, b, c}).card := by
      have hsub : {a, b, c} ⊆ W := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      rw [card_sdiff_of_subset hsub, h3card]; omega
    obtain ⟨d, hd⟩ := card_pos.mp hrem
    obtain ⟨hdW, hd3⟩ := mem_sdiff.mp hd
    simp only [mem_insert, mem_singleton, not_or] at hd3
    obtain ⟨hda, hdb, hdc⟩ := hd3
    have hnotall : ¬ (G.Adj d a ∧ G.Adj d b ∧ G.Adj d c) := fun ⟨h1, h2, h3⟩ =>
      not_four_clique hG h1 h2 h3 hab hac hbc
    have hnotri3 : ∀ p q r : V, ¬ G.Adj p r →
        ∀ u ∈ ({p, q, r} : Finset V), ∀ v ∈ ({p, q, r} : Finset V), ∀ w ∈ ({p, q, r} : Finset V),
          ¬ (G.Adj u v ∧ G.Adj u w ∧ G.Adj v w) := by
      intro p q r hnpr u hu v hv w hw ⟨huv, huw, hvw⟩
      simp only [mem_insert, mem_singleton] at hu hv hw
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> first | exact G.irrefl huv | exact G.irrefl huw | exact G.irrefl hvw | exact hnpr huv | exact hnpr huv.symm | exact hnpr huw | exact hnpr huw.symm | exact hnpr hvw | exact hnpr hvw.symm
    have hmake : ∀ x y z : V, x ∈ W → y ∈ W → z ∈ W →
        G.Adj x y → G.Adj x z → G.Adj y z →
        d ≠ x → d ≠ y → d ≠ z → ¬ G.Adj d x →
        ∃ T ⊆ W, (∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 3 := by
      intro x y z hx hy hz hxy hxz hyz hdx hdy hdz hndx
      by_cases hdy_adj : G.Adj d y
      · by_cases hdz_adj : G.Adj d z
        · refine ⟨{d, y, x}, ?_, (free_iff_no_tri_no_lone hG _).mpr ⟨hnotri3 d y x hndx, ?_⟩, ?_⟩
          · intro u hu; simp only [mem_insert, mem_singleton] at hu
            rcases hu with rfl | rfl | rfl <;> assumption
          · intro u hu v hv huv
            simp only [mem_insert, mem_singleton] at hu hv
            rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
            · exact (G.irrefl huv).elim
            · exact ⟨z, hdz_adj.symm, hyz.symm⟩
            · exact (hndx huv).elim
            · exact ⟨z, hyz.symm, hdz_adj.symm⟩
            · exact (G.irrefl huv).elim
            · exact ⟨z, hyz.symm, hxz.symm⟩
            · exact (hndx huv.symm).elim
            · exact ⟨z, hxz.symm, hyz.symm⟩
            · exact (G.irrefl huv).elim
          · have hd' : d ∉ ({y, x} : Finset V) := by
              simp only [mem_insert, mem_singleton, not_or]; exact ⟨hdy, hdx⟩
            rw [card_insert_of_notMem hd', card_pair hxy.ne.symm]
        · refine ⟨{d, z, x}, ?_, (free_iff_no_tri_no_lone hG _).mpr ⟨hnotri3 d z x hndx, ?_⟩, ?_⟩
          · intro u hu; simp only [mem_insert, mem_singleton] at hu
            rcases hu with rfl | rfl | rfl <;> assumption
          · intro u hu v hv huv
            simp only [mem_insert, mem_singleton] at hu hv
            rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
            · exact (G.irrefl huv).elim
            · exact (hdz_adj huv).elim
            · exact (hndx huv).elim
            · exact (hdz_adj huv.symm).elim
            · exact (G.irrefl huv).elim
            · exact ⟨y, hyz, hxy.symm⟩
            · exact (hndx huv.symm).elim
            · exact ⟨y, hxy.symm, hyz⟩
            · exact (G.irrefl huv).elim
          · have hd' : d ∉ ({z, x} : Finset V) := by
              simp only [mem_insert, mem_singleton, not_or]; exact ⟨hdz, hdx⟩
            rw [card_insert_of_notMem hd', card_pair hxz.ne.symm]
      · refine ⟨{d, y, x}, ?_, (free_iff_no_tri_no_lone hG _).mpr ⟨hnotri3 d y x hndx, ?_⟩, ?_⟩
        · intro u hu; simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl | rfl <;> assumption
        · intro u hu v hv huv
          simp only [mem_insert, mem_singleton] at hu hv
          rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
          · exact (G.irrefl huv).elim
          · exact (hdy_adj huv).elim
          · exact (hndx huv).elim
          · exact (hdy_adj huv.symm).elim
          · exact (G.irrefl huv).elim
          · exact ⟨z, hyz.symm, hxz.symm⟩
          · exact (hndx huv.symm).elim
          · exact ⟨z, hxz.symm, hyz.symm⟩
          · exact (G.irrefl huv).elim
        · have hd' : d ∉ ({y, x} : Finset V) := by
            simp only [mem_insert, mem_singleton, not_or]; exact ⟨hdy, hdx⟩
          rw [card_insert_of_notMem hd', card_pair hxy.ne.symm]
    by_cases h1 : G.Adj d a
    · by_cases h2 : G.Adj d b
      · exact hmake c a b hc ha hb hac.symm hbc.symm hab hdc hda hdb (fun h3 => hnotall ⟨h1, h2, h3⟩)
      · exact hmake b a c hb ha hc hab.symm hbc hac hdb hda hdc h2
    · exact hmake a b c ha hb hc hab hac hbc hda hdb hdc h1
  · push Not at htri
    obtain ⟨I, hIW, hIi, hI3⟩ := indep_three_of_K3_free_on G W (fun a ha b hb c hc ⟨h1, h2, h3⟩ => htri a ha b hb c hc h1 h2 h3) hW
    exact ⟨I, hIW, free_of_indep hIi, hI3⟩

private lemma free_four_of_nine {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (W : Finset V) (hW : 9 ≤ W.card) :
    ∃ T ⊆ W, (∀ K : Finset V, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 4 := by
  classical
  by_cases hdeg4 : ∃ v ∈ W, 4 ≤ (W.filter (G.Adj v)).card
  · obtain ⟨v, _, hdv⟩ := hdeg4
    obtain ⟨T, hTN, hT4⟩ := exists_subset_card_eq hdv
    exact ⟨T, hTN.trans (filter_subset _ _),
      free_of_neighbor_subset (fun u hu => (mem_filter.mp (hTN hu)).2), hT4⟩
  · push Not at hdeg4
    by_cases htri : ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
    · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := htri
      let Na := W.filter (G.Adj a)
      let D := Na.erase c
      have hcNa : c ∈ Na := mem_filter.mpr ⟨hc, hac⟩
      have hNa_le : Na.card ≤ 3 := by dsimp only [Na]; have := hdeg4 a ha; omega
      have hD_le : D.card ≤ 2 := by dsimp only [D]; rw [card_erase_of_mem hcNa]; omega
      let W' := W \ insert a D
      have hW'card : 6 ≤ W'.card := by
        dsimp only [W']
        have h1 : (insert a D).card ≤ 3 := (card_insert_le a D).trans (by omega)
        have h2 := card_sdiff_add_card_inter W (insert a D)
        have h3 : (W ∩ insert a D).card ≤ (insert a D).card := card_le_card inter_subset_right
        omega
      obtain ⟨T', hT'W', hT'free, hT'3⟩ := free_three_of_six G hG W' hW'card
      have haT' : a ∉ T' := fun h => (mem_sdiff.mp (hT'W' h)).2 (mem_insert_self a D)
      have hT'props := (free_iff_no_tri_no_lone hG T').mp hT'free
      have hT'_adj_a : ∀ x ∈ T', G.Adj a x → x = c := by
        intro x hx hax
        have hxW' := mem_sdiff.mp (hT'W' hx)
        have hxNa : x ∈ Na := mem_filter.mpr ⟨hxW'.1, hax⟩
        by_contra hne
        exact hxW'.2 (mem_insert_of_mem (mem_erase.mpr ⟨hne, hxNa⟩))
      refine ⟨insert a T', insert_subset_iff.mpr ⟨ha, hT'W'.trans sdiff_subset⟩,
        (free_iff_no_tri_no_lone hG _).mpr ⟨?_, ?_⟩, by rw [card_insert_of_notMem haT', hT'3]⟩
      · intro x hx y hy z hz ⟨hxy, hxz, hyz⟩
        rcases mem_insert.mp hx with hxa | hx <;>
        rcases mem_insert.mp hy with hya | hy <;>
        rcases mem_insert.mp hz with hza | hz
        · rw [hxa, hya] at hxy; exact G.irrefl hxy
        · rw [hxa, hya] at hxy; exact G.irrefl hxy
        · rw [hxa, hza] at hxz; exact G.irrefl hxz
        · rw [hxa] at hxy hxz
          have h1 := hT'_adj_a y hy hxy
          have h2 := hT'_adj_a z hz hxz
          rw [h1, h2] at hyz; exact G.irrefl hyz
        · rw [hya, hza] at hyz; exact G.irrefl hyz
        · rw [hya] at hxy hyz
          have h1 := hT'_adj_a x hx hxy.symm
          have h2 := hT'_adj_a z hz hyz
          rw [h1, h2] at hxz; exact G.irrefl hxz
        · rw [hza] at hxz hyz
          have h1 := hT'_adj_a x hx hxz.symm
          have h2 := hT'_adj_a y hy hyz.symm
          rw [h1, h2] at hxy; exact G.irrefl hxy
        · exact hT'props.1 x hx y hy z hz ⟨hxy, hxz, hyz⟩
      · intro x hx y hy hxy
        rcases mem_insert.mp hx with hxa | hx <;> rcases mem_insert.mp hy with hya | hy
        · rw [hxa, hya] at hxy; exact (G.irrefl hxy).elim
        · rw [hxa] at hxy ⊢
          have hyc := hT'_adj_a y hy hxy; rw [hyc]; exact ⟨b, hab.symm, hbc⟩
        · rw [hya] at hxy ⊢
          have hxc := hT'_adj_a x hx hxy.symm; rw [hxc]; exact ⟨b, hbc, hab.symm⟩
        · exact hT'props.2 x hx y hy hxy
    · push Not at htri
      obtain ⟨I, hIW, hIi, hI4⟩ := indep_four_of_K3_free_on G W
        (fun a ha b hb c hc ⟨h1, h2, h3⟩ => htri a ha b hb c hc h1 h2 h3) hW
      exact ⟨I, hIW, free_of_indep hIi, hI4⟩

-- ============================================================================
-- Section 5: Partition-Compatibility Lemma and exact U(1), U(2), U(3), U(4)
-- ============================================================================

private lemma compatible_union_free {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (v : Fin n) (S T : Finset (Fin n))
    (hSv : ∀ u ∈ S, G.Adj v u)
    (hTfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ K ⊆ T)
    (hsafe : ∀ x ∈ T, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
    (hcompat : ∀ x ∈ T, ∀ y ∈ T, G.Adj x y → ∀ u ∈ S, G.Adj x u → ¬ G.Adj y u) :
    ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ K ⊆ S ∪ T := by
  classical
  have hSprops := (free_iff_no_tri_no_lone hG S).mp (free_of_neighbor_subset hSv)
  have hTprops := (free_iff_no_tri_no_lone hG T).mp hTfree
  refine (free_iff_no_tri_no_lone hG (S ∪ T)).mpr ⟨?_, ?_⟩
  · intro a ha b hb c hc ⟨hab, hac, hbc⟩
    rcases mem_union.mp ha with ha | ha <;>
    rcases mem_union.mp hb with hb | hb <;>
    rcases mem_union.mp hc with hc | hc
    · exact hSprops.1 a ha b hb c hc ⟨hab, hac, hbc⟩
    · exact (hsafe c hc).1 ⟨ha, hac.symm⟩ ⟨hb, hbc.symm⟩ hab.ne hab
    · exact (hsafe b hb).1 ⟨ha, hab.symm⟩ ⟨hc, hbc⟩ hac.ne hac
    · exact hcompat b hb c hc hbc a ha hab.symm hac.symm
    · exact (hsafe a ha).1 ⟨hb, hab⟩ ⟨hc, hac⟩ hbc.ne hbc
    · exact hcompat a ha c hc hac b hb hab hbc.symm
    · exact hcompat a ha b hb hab c hc hac hbc
    · exact hTprops.1 a ha b hb c hc ⟨hab, hac, hbc⟩
  · intro a ha b hb hab
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact hSprops.2 a ha b hb hab
    · obtain ⟨z, hz1, hz2⟩ := (hsafe b hb).2 a ha hab.symm
      exact ⟨z, hz2, hz1⟩
    · exact (hsafe a ha).2 b hb hab
    · exact hTprops.2 a ha b hb hab

private lemma partition_compatible_U34 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (v : Fin n) (S A : Finset (Fin n))
    (hSv : ∀ u ∈ S, G.Adj v u)
    (hdis : Disjoint S A)
    (hsafe : ∀ x ∈ A, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
    (hpartCap : ∀ u ∈ S, (A.filter (G.Adj u)).card ≤ 9) :
    (2 * A.card > (∑ u ∈ S, (A.filter (G.Adj u)).card) + 11 →
      ∃ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) ∧ S.card + 3 ≤ U.card) ∧
    (2 * A.card > (∑ u ∈ S, (A.filter (G.Adj u)).card) + 19 →
      ∃ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) ∧ S.card + 4 ≤ U.card) := by
  classical
  let Z := A.filter (fun x => (S.filter (G.Adj x)).card = 0)
  let P1 := A.filter (fun x => (S.filter (G.Adj x)).card = 1)
  have hsumE : (∑ u ∈ S, (A.filter (G.Adj u)).card) = ∑ x ∈ A, (S.filter (G.Adj x)).card := by
    simp_rw [card_filter]; rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun u _ => by simp [G.adj_comm]
  have h2ZP1 : 2 * A.card ≤ (∑ u ∈ S, (A.filter (G.Adj u)).card) + 2 * Z.card + P1.card := by
    rw [hsumE]
    have hpt : ∀ x ∈ A, 2 ≤ (S.filter (G.Adj x)).card +
        (if (S.filter (G.Adj x)).card = 0 then 2 else 0) +
        (if (S.filter (G.Adj x)).card = 1 then 1 else 0) := by
      intro x _; split_ifs <;> omega
    have htot := sum_le_sum hpt
    simp only [sum_add_distrib, sum_const, smul_eq_mul] at htot
    have hZ : (∑ x ∈ A, if (S.filter (G.Adj x)).card = 0 then 2 else 0) = 2 * Z.card := by
      rw [← Finset.sum_filter]; simp [Z, mul_comm]
    have hP1 : (∑ x ∈ A, if (S.filter (G.Adj x)).card = 1 then 1 else 0) = P1.card := by
      rw [← Finset.sum_filter]; simp [P1]
    rw [hZ, hP1] at htot
    omega
  have hdisZP1 : Disjoint Z P1 :=
    disjoint_left.mpr fun x h1 h2 => by have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
  have hZP1_le_A : Z.card + P1.card ≤ A.card := by
    rw [← card_union_of_disjoint hdisZP1]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  -- Partition P1 by unique neighbor in S
  let Pu (u : Fin n) := P1.filter (G.Adj u)
  have hPu_dis : (S : Set (Fin n)).PairwiseDisjoint Pu := by
    intro u hu w hw huw
    refine Finset.disjoint_left.mpr fun x hxu hxw => huw ?_
    have h1 := (mem_filter.mp hxu).2
    have h2 := (mem_filter.mp hxw).2
    have hx1 := (mem_filter.mp (mem_filter.mp hxu).1).2
    exact card_le_one_iff.mp hx1.le (mem_filter.mpr ⟨hu, h1.symm⟩) (mem_filter.mpr ⟨hw, h2.symm⟩)
  have hP1_biUnion : S.biUnion Pu = P1 := by
    ext x
    simp only [Pu, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨u, _, hxP1, _⟩; exact hxP1
    · intro hxP1
      have hcard1 := (mem_filter.mp hxP1).2
      obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (S.filter (G.Adj x)).card)
      obtain ⟨huS, hxu⟩ := mem_filter.mp hu
      exact ⟨u, huS, hxP1, hxu.symm⟩
  have hP1_sum : P1.card = ∑ u ∈ S, (Pu u).card := by
    rw [← hP1_biUnion, card_biUnion hPu_dis]
  -- For each u ∈ S, Pu u is triangle-free of size <= 9, so pick independent E_u with 3*|Pu u| <= 8*|E_u|
  have hexE : ∀ u ∈ S, ∃ E ⊆ Pu u, G.IsIndepSet (E : Set (Fin n)) ∧ 3 * (Pu u).card ≤ 8 * E.card := by
    intro u hu
    have hle9 : (Pu u).card ≤ 9 :=
      (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hpartCap u hu)
    have h3 : ∀ a ∈ Pu u, ∀ b ∈ Pu u, ∀ c ∈ Pu u, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := fun a ha b hb c hc ⟨hab, hac, hbc⟩ =>
      not_four_clique hG (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2 hab hac hbc
    by_cases h9 : 9 ≤ (Pu u).card
    · obtain ⟨E, hE, hEi, hEc⟩ := indep_four_of_K3_free_on G (Pu u) h3 h9
      exact ⟨E, hE, hEi, by omega⟩
    · by_cases h6 : 6 ≤ (Pu u).card
      · obtain ⟨E, hE, hEi, hEc⟩ := indep_three_of_K3_free_on G (Pu u) h3 h6
        exact ⟨E, hE, hEi, by omega⟩
      · by_cases h3c : 3 ≤ (Pu u).card
        · obtain ⟨E, hE, hEi, hEc⟩ := indep_two_of_K3_free_on G (Pu u) h3 h3c
          exact ⟨E, hE, hEi, by omega⟩
        · by_cases h1 : 1 ≤ (Pu u).card
          · obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (Pu u).card)
            refine ⟨{x}, singleton_subset_iff.mpr hx, ?_, by simp; omega⟩
            rw [← SimpleGraph.isClique_compl, coe_singleton]
            exact SimpleGraph.isClique_singleton x
          · exact ⟨∅, empty_subset _, by simp, by simp only [card_empty, mul_zero]; omega⟩
  choose E hEPu hEi hEcard using hexE
  let Eall := S.biUnion fun u => if hu : u ∈ S then E u hu else ∅
  have hEdis : (S : Set (Fin n)).PairwiseDisjoint (fun u => if hu : u ∈ S then E u hu else ∅) := by
    intro u hu w hw huw
    have hu' : u ∈ S := hu
    have hw' : w ∈ S := hw
    change Disjoint (if hu : u ∈ S then E u hu else ∅) (if hw : w ∈ S then E w hw else ∅)
    rw [dif_pos hu', dif_pos hw']
    exact (hPu_dis hu hw huw).mono (hEPu u hu') (hEPu w hw')
  have hEall_sub_P1 : Eall ⊆ P1 := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := mem_biUnion.mp hx
    simp only [hu, ↓reduceDIte] at hxu
    exact (filter_subset _ _) (hEPu u hu hxu)
  have hEall_card : 3 * P1.card ≤ 8 * Eall.card := by
    rw [hP1_sum, card_biUnion hEdis, mul_sum, mul_sum]
    refine sum_le_sum fun u hu => ?_
    simp only [hu, ↓reduceDIte]
    exact hEcard u hu
  let W := Z ∪ Eall
  have hW_sub_A : W ⊆ A := union_subset (filter_subset _ _) (hEall_sub_P1.trans (filter_subset _ _))
  have hW_card : W.card = Z.card + Eall.card :=
    card_union_of_disjoint (hdisZP1.mono_right hEall_sub_P1)
  have hW_compat : ∀ x ∈ W, ∀ y ∈ W, G.Adj x y → ∀ u ∈ S, G.Adj x u → ¬ G.Adj y u := by
    intro x hx y hy hxy u hu hxu hyu
    have hxZ : x ∉ Z := fun hxZ => by
      have h0 := (mem_filter.mp hxZ).2
      have hpos : 0 < (S.filter (G.Adj x)).card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hxu⟩⟩
      omega
    have hyZ : y ∉ Z := fun hyZ => by
      have h0 := (mem_filter.mp hyZ).2
      have hpos : 0 < (S.filter (G.Adj y)).card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hyu⟩⟩
      omega
    have hxE : x ∈ Eall := (mem_union.mp hx).resolve_left hxZ
    have hyE : y ∈ Eall := (mem_union.mp hy).resolve_left hyZ
    obtain ⟨ux, hux, hxux⟩ := mem_biUnion.mp hxE
    obtain ⟨uy, huy, hyuy⟩ := mem_biUnion.mp hyE
    simp only [hux, ↓reduceDIte] at hxux
    simp only [huy, ↓reduceDIte] at hyuy
    have hux_eq : ux = u := by
      have h1 := (mem_filter.mp (hEPu ux hux hxux)).2
      have hx1 := (mem_filter.mp (mem_filter.mp (hEPu ux hux hxux)).1).2
      exact card_le_one_iff.mp hx1.le (mem_filter.mpr ⟨hux, h1.symm⟩) (mem_filter.mpr ⟨hu, hxu⟩)
    have huy_eq : uy = u := by
      have h1 := (mem_filter.mp (hEPu uy huy hyuy)).2
      have hy1 := (mem_filter.mp (mem_filter.mp (hEPu uy huy hyuy)).1).2
      exact card_le_one_iff.mp hy1.le (mem_filter.mpr ⟨huy, h1.symm⟩) (mem_filter.mpr ⟨hu, hyu⟩)
    have huxy : ux = uy := hux_eq.trans huy_eq.symm
    subst huxy
    exact hEi ux hux hxux hyuy hxy.ne hxy
  constructor
  · intro hgt
    by_cases hA9 : 9 ≤ A.card
    · obtain ⟨I, hIA, hIi, hI3⟩ := indep_three_of_K4_free G hG A hA9
      refine ⟨S ∪ I, compatible_union_free G hG v S I hSv (free_of_indep hIi)
        (fun x hx => hsafe x (hIA hx)) (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim), ?_⟩
      rw [card_union_of_disjoint (hdis.mono_right hIA), hI3]
    · have hW6 : 6 ≤ W.card := by omega
      obtain ⟨T, hTW, hTfree, hT3⟩ := free_three_of_six G hG W hW6
      refine ⟨S ∪ T, compatible_union_free G hG v S T hSv hTfree
        (fun x hx => hsafe x (hW_sub_A (hTW hx)))
        (fun x hx y hy => hW_compat x (hTW hx) y (hTW hy)), ?_⟩
      rw [card_union_of_disjoint (hdis.mono_right (hTW.trans hW_sub_A)), hT3]
  · intro hgt
    by_cases hA18 : 18 ≤ A.card
    · obtain ⟨I, hIA, hIi, hI4⟩ := indep_four_of_K4_free G hG A hA18
      refine ⟨S ∪ I, compatible_union_free G hG v S I hSv (free_of_indep hIi)
        (fun x hx => hsafe x (hIA hx)) (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim), ?_⟩
      rw [card_union_of_disjoint (hdis.mono_right hIA), hI4]
    · have hW9 : 9 ≤ W.card := by omega
      obtain ⟨T, hTW, hTfree, hT4⟩ := free_four_of_nine G hG W hW9
      refine ⟨S ∪ T, compatible_union_free G hG v S T hSv hTfree
        (fun x hx => hsafe x (hW_sub_A (hTW hx)))
        (fun x hx y hy => hW_compat x (hTW hx) y (hTW hy)), ?_⟩
      rw [card_union_of_disjoint (hdis.mono_right (hTW.trans hW_sub_A)), hT4]

private lemma extend_two_of_gt_four {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (v : Fin n) (S A : Finset (Fin n))
    (hSv : ∀ u ∈ S, G.Adj v u)
    (hdis : Disjoint S A)
    (hsafe : ∀ x ∈ A, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
    (hgt : 2 * A.card > (∑ u ∈ S, (A.filter (G.Adj u)).card) + 4) :
    ∃ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) ∧ S.card + 2 ≤ U.card := by
  classical
  by_cases hA4 : 4 ≤ A.card
  · obtain ⟨I, hIA, hIi, hI2⟩ := indep_two_of_K4_free G hG A hA4
    refine ⟨S ∪ I, compatible_union_free G hG v S I hSv (free_of_indep hIi)
      (fun x hx => hsafe x (hIA hx)) (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim), ?_⟩
    rw [card_union_of_disjoint (hdis.mono_right hIA), hI2]
  · have hA3 : A.card = 3 := by omega
    have hE_le1 : (∑ u ∈ S, (A.filter (G.Adj u)).card) ≤ 1 := by omega
    obtain ⟨a, S', haS', heqA, hS'2⟩ := Finset.card_eq_succ.mp hA3
    obtain ⟨b, c, hbc, rfl⟩ := card_eq_two.mp hS'2
    have hAeq : A = {a, b, c} := heqA.symm
    have hab_ne : a ≠ b := fun h => haS' (by simp [h])
    have hac_ne : a ≠ c := fun h => haS' (by simp [h])
    have haA : a ∈ A := by rw [hAeq]; simp
    have hbA : b ∈ A := by rw [hAeq]; simp
    have hcA : c ∈ A := by rw [hAeq]; simp
    -- Either A has a non-edge (independent pair -> done) or A is K3 (every edge in a triangle, and e(S,A)<=1 => some pair shares no S-neighbor!)
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · by_cases h3 : G.Adj b c
        · -- A is a triangle {a,b,c}, and total crossing edges <= 1, so no u ∈ S sees 2 vertices of A!
          have hno2 : ∀ u ∈ S, ¬ (G.Adj a u ∧ G.Adj b u) := by
            intro u hu ⟨hau, hbu⟩
            have h2u : 2 ≤ (A.filter (G.Adj u)).card := by
              have hsub : ({a, b} : Finset (Fin n)) ⊆ A.filter (G.Adj u) := by
                intro x hx; simp only [mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact mem_filter.mpr ⟨haA, hau.symm⟩
                · exact mem_filter.mpr ⟨hbA, hbu.symm⟩
              have := card_le_card hsub; rwa [card_pair hab_ne] at this
            have hle := single_le_sum (f := fun u => (A.filter (G.Adj u)).card) (fun _ _ => Nat.zero_le _) hu
            omega
          have hTfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ K ⊆ ({a, b} : Finset (Fin n)) := by
            refine (free_iff_no_tri_no_lone hG {a, b}).mpr ⟨?_, ?_⟩
            · intro x hx y hy z hz ⟨hxy, hxz, hyz⟩
              simp only [mem_insert, mem_singleton] at hx hy hz
              rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
              all_goals first | exact G.irrefl hxy | exact G.irrefl hxz | exact G.irrefl hyz
            · intro x hx y hy hxy
              simp only [mem_insert, mem_singleton] at hx hy
              rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact (G.irrefl hxy).elim
              · exact ⟨c, h2.symm, h3.symm⟩
              · exact ⟨c, h3.symm, h2.symm⟩
              · exact (G.irrefl hxy).elim
          have hTsub : ({a, b} : Finset (Fin n)) ⊆ A := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
          refine ⟨S ∪ {a, b}, compatible_union_free G hG v S {a, b} hSv hTfree
            (fun x hx => hsafe x (hTsub hx)) ?_, ?_⟩
          · intro x hx y hy hxy u hu hxu hyu
            simp only [mem_insert, mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact G.irrefl hxy
            · exact hno2 u hu ⟨hxu, hyu⟩
            · exact hno2 u hu ⟨hyu, hxu⟩
            · exact G.irrefl hxy
          · rw [card_union_of_disjoint (hdis.mono_right hTsub), card_pair hab_ne]
        · have hIi : G.IsIndepSet (({b, c} : Finset (Fin n)) : Set (Fin n)) := by
            intro x hx y hy hxy hadj
            simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact hxy rfl
            · exact h3 hadj
            · exact h3 hadj.symm
            · exact hxy rfl
          have hIsub : ({b, c} : Finset (Fin n)) ⊆ A := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
          refine ⟨S ∪ {b, c}, compatible_union_free G hG v S {b, c} hSv (free_of_indep hIi)
            (fun x hx => hsafe x (hIsub hx)) (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim), ?_⟩
          rw [card_union_of_disjoint (hdis.mono_right hIsub), card_pair hbc]
      · have hIi : G.IsIndepSet (({a, c} : Finset (Fin n)) : Set (Fin n)) := by
          intro x hx y hy hxy hadj
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact hxy rfl
          · exact h2 hadj
          · exact h2 hadj.symm
          · exact hxy rfl
        have hIsub : ({a, c} : Finset (Fin n)) ⊆ A := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
        refine ⟨S ∪ {a, c}, compatible_union_free G hG v S {a, c} hSv (free_of_indep hIi)
          (fun x hx => hsafe x (hIsub hx)) (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim), ?_⟩
        rw [card_union_of_disjoint (hdis.mono_right hIsub), card_pair hac_ne]
    · have hIi : G.IsIndepSet (({a, b} : Finset (Fin n)) : Set (Fin n)) := by
        intro x hx y hy hxy hadj
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact hxy rfl
        · exact h1 hadj
        · exact h1 hadj.symm
        · exact hxy rfl
      have hIsub : ({a, b} : Finset (Fin n)) ⊆ A := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
      refine ⟨S ∪ {a, b}, compatible_union_free G hG v S {a, b} hSv (free_of_indep hIi)
        (fun x hx => hsafe x (hIsub hx)) (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim), ?_⟩
      rw [card_union_of_disjoint (hdis.mono_right hIsub), card_pair hab_ne]


-- ============================================================================
-- Section 6: Exact full-neighborhood safe-outsider bounds U(9,2)<=10, U(8,3)<=16
-- ============================================================================

private lemma lone_nbhd_indep {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n)
    (B : Finset (Fin n))
    (hB : ∀ x ∈ B, G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x) :
    G.IsIndepSet (B : Set (Fin n)) := by
  intro x hx y hy _ hxy
  exact (hB x hx).2 ⟨y, (hB y hy).1.symm, hxy.symm⟩

private lemma full_nbhd_disj_lone {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (S L : Finset (Fin n))
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w) :
    (∀ w ∈ L, ∀ u ∈ S, ¬ G.Adj w u) ∧ (∀ w1 ∈ L, ∀ w2 ∈ L, ¬ G.Adj w1 w2) := by
  refine ⟨fun w hw u hu hwu => (hL w hw).2 ⟨u, (hS u hu).symm, hwu.symm⟩,
    fun w1 hw1 w2 hw2 h12 => (hL w1 hw1).2 ⟨w2, (hL w2 hw2).1.symm, h12.symm⟩⟩

private lemma safe_for_union_lone {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (S L : Finset (Fin n)) (x : Fin n)
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w)
    (hxS : G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
    (hxL : ∀ w ∈ L, G.Adj x w → ∃ z, G.Adj z x ∧ G.Adj z w) :
    G.IsIndepSet {a | a ∈ S ∪ L ∧ G.Adj x a} ∧
      ∀ a ∈ S ∪ L, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a := by
  have hno := full_nbhd_disj_lone G v S L hS hL
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab hadj
    rcases mem_union.mp ha.1 with haS | haL <;> rcases mem_union.mp hb.1 with hbS | hbL
    · exact hxS.1 ⟨haS, ha.2⟩ ⟨hbS, hb.2⟩ hab hadj
    · exact hno.1 b hbL a haS hadj.symm
    · exact hno.1 a haL b hbS hadj
    · exact hno.2 a haL b hbL hadj
  · intro a ha hxa
    rcases mem_union.mp ha with haS | haL
    · exact hxS.2 a haS hxa
    · exact hxL a haL hxa

private lemma Bstar_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S L : Finset (Fin n))
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w)
    (hdisSL : Disjoint S L)
    (hcard11 : S.card + L.card = 11)
    (w : Fin n) (hwL : w ∈ L)
    (B : Finset (Fin n))
    (hBdis : Disjoint (S ∪ L) B)
    (hBlone : ∀ x ∈ B, G.Adj w x ∧ ¬ ∃ z, G.Adj z w ∧ G.Adj z x)
    (hBsafeS : ∀ x ∈ B, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
    (hBsafeL : ∀ x ∈ B, ∀ w' ∈ L.erase w, G.Adj x w' → ∃ z, G.Adj z x ∧ G.Adj z w') :
    B.card ≤ 1 := by
  classical
  let S' := S ∪ L.erase w
  have hS'v : ∀ u ∈ S', G.Adj v u := by
    intro u hu
    rcases mem_union.mp hu with h1 | h2
    · exact hS u h1
    · exact (hL u (erase_subset w L h2)).1
  have hS'card : S'.card = 10 := by
    rw [card_union_of_disjoint (hdisSL.mono_right (erase_subset w L)), card_erase_of_mem hwL]
    have hwpos : 0 < L.card := card_pos.mpr ⟨w, hwL⟩
    omega
  have hBi : G.IsIndepSet (B : Set (Fin n)) := lone_nbhd_indep G w B hBlone
  have hUfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ K ⊆ S' ∪ B :=
    compatible_union_free G hG v S' B hS'v (free_of_indep hBi)
      (fun x hx => safe_for_union_lone G v S (L.erase w) x hS
        (fun w' hw' => hL w' (erase_subset w L hw')) (hBsafeS x hx) (hBsafeL x hx))
      (fun x hx y hy hxy => (hBi hx hy hxy.ne hxy).elim)
  have hdis' : Disjoint S' B := hBdis.mono_left (union_subset_union_right (erase_subset w L))
  have hle := hno12 (S' ∪ B) hUfree
  rw [card_union_of_disjoint hdis', hS'card] at hle
  omega

private lemma Bstar_core_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S L : Finset (Fin n))
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w)
    (hdisSL : Disjoint S L)
    (hcard11 : S.card + L.card = 11)
    (u : Fin n) (huS : u ∈ S)
    (B : Finset (Fin n))
    (hBdis : Disjoint (S ∪ L) B)
    (hBlone : ∀ x ∈ B, G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x)
    (hBnoS : ∀ x ∈ B, ∀ a ∈ S.erase u, ¬ G.Adj x a)
    (hBsafeL : ∀ x ∈ B, ∀ w ∈ L, G.Adj x w → ∃ z, G.Adj z x ∧ G.Adj z w) :
    B.card ≤ 1 := by
  classical
  let S' := S.erase u ∪ L
  have hS'v : ∀ a ∈ S', G.Adj v a := by
    intro a ha
    rcases mem_union.mp ha with h1 | h2
    · exact hS a (erase_subset u S h1)
    · exact (hL a h2).1
  have hS'card : S'.card = 10 := by
    rw [card_union_of_disjoint (hdisSL.mono_left (erase_subset u S)), card_erase_of_mem huS]
    have hupos : 0 < S.card := card_pos.mpr ⟨u, huS⟩
    omega
  have hBi : G.IsIndepSet (B : Set (Fin n)) := lone_nbhd_indep G u B hBlone
  have hsafe : ∀ x ∈ B, G.IsIndepSet {a | a ∈ S' ∧ G.Adj x a} ∧
      ∀ a ∈ S', G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a := by
    intro x hx
    refine safe_for_union_lone G v (S.erase u) L x
      (fun a ha => hS a (erase_subset u S ha)) hL ?_ (hBsafeL x hx)
    refine ⟨?_, ?_⟩
    · intro a ha _ _ _ _
      exact (hBnoS x hx a ha.1 ha.2).elim
    · intro a ha hxa
      exact (hBnoS x hx a ha hxa).elim
  have hUfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ K ⊆ S' ∪ B :=
    compatible_union_free G hG v S' B hS'v (free_of_indep hBi) hsafe
      (fun x hx y hy hxy => (hBi hx hy hxy.ne hxy).elim)
  have hdis' : Disjoint S' B := hBdis.mono_left (union_subset_union_left (erase_subset u S))
  have hle := hno12 (S' ∪ B) hUfree
  rw [card_union_of_disjoint hdis', hS'card] at hle
  omega

private lemma safe_indep_card_le {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S I : Finset (Fin n))
    (hSv : ∀ u ∈ S, G.Adj v u)
    (hdis : Disjoint S I)
    (hIi : G.IsIndepSet (I : Set (Fin n)))
    (hsafe : ∀ x ∈ I, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) :
    S.card + I.card ≤ 11 := by
  have hUfree := compatible_union_free G hG v S I hSv (free_of_indep hIi) hsafe
    (fun x hx y hy hxy => (hIi hx hy hxy.ne hxy).elim)
  have hle := hno12 (S ∪ I) hUfree
  rwa [card_union_of_disjoint hdis] at hle

private lemma AT_has_lone_to_L {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S L : Finset (Fin n))
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w)
    (hdisSL : Disjoint S L)
    (hcard11 : S.card + L.card = 11)
    (x : Fin n) (hxS : x ∉ S) (hxL : x ∉ L)
    (hsafeS : G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) :
    ∃ w ∈ L, G.Adj w x ∧ ¬ ∃ z, G.Adj z w ∧ G.Adj z x := by
  by_contra! hnone
  have hxL' : ∀ w ∈ L, G.Adj x w → ∃ z, G.Adj z x ∧ G.Adj z w := by
    intro w hw hxw
    obtain ⟨z, hzw, hzx⟩ := hnone w hw hxw.symm
    exact ⟨z, hzx, hzw⟩
  have hIi : G.IsIndepSet (({x} : Finset (Fin n)) : Set (Fin n)) := by
    rw [← SimpleGraph.isClique_compl, coe_singleton]
    exact SimpleGraph.isClique_singleton x
  have hUfree := compatible_union_free G hG v (S ∪ L) {x}
    (fun u hu => (mem_union.mp hu).elim (hS u) (fun h => (hL u h).1))
    (free_of_indep hIi)
    (fun y hy => by
      rw [mem_singleton.mp hy]
      exact safe_for_union_lone G v S L x hS hL hsafeS hxL')
    (fun y hy z hz hyz => (hIi hy hz hyz.ne hyz).elim)
  have hdis : Disjoint (S ∪ L) {x} :=
    disjoint_singleton_right.mpr (by simp [hxS, hxL])
  have hle := hno12 ((S ∪ L) ∪ {x}) hUfree
  rw [card_union_of_disjoint hdis, card_union_of_disjoint hdisSL, card_singleton] at hle
  omega

private lemma U_nine_two_le_ten {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S L A : Finset (Fin n))
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w)
    (hdisSL : Disjoint S L)
    (hScard : S.card = 9) (hLcard : L.card = 2)
    (hLA : L ⊆ A)
    (hdisSA : Disjoint S A)
    (hsafe : ∀ x ∈ A, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) :
    A.card ≤ 5 := by
  classical
  obtain ⟨w1, w2, hw12, hLeq⟩ := card_eq_two.mp hLcard
  have hw1L : w1 ∈ L := by rw [hLeq]; simp
  have hw2L : w2 ∈ L := by rw [hLeq]; simp
  let AT := A \ L
  let B1 := AT.filter (fun x => (G.Adj w1 x ∧ ¬ ∃ z, G.Adj z w1 ∧ G.Adj z x) ∧
    ¬ (G.Adj w2 x ∧ ¬ ∃ z, G.Adj z w2 ∧ G.Adj z x))
  let N2 := AT.filter (fun x => G.Adj w2 x ∧ ¬ ∃ z, G.Adj z w2 ∧ G.Adj z x)
  have hATsub : AT ⊆ B1 ∪ N2 := by
    intro x hx
    have hxA : x ∈ A := (mem_sdiff.mp hx).1
    have hxL : x ∉ L := (mem_sdiff.mp hx).2
    have hxS : x ∉ S := disjoint_right.mp hdisSA hxA
    obtain ⟨w, hwL, hwx⟩ := AT_has_lone_to_L G hG hno12 v S L hS hL hdisSL (by omega) x hxS hxL (hsafe x hxA)
    by_cases h2 : G.Adj w2 x ∧ ¬ ∃ z, G.Adj z w2 ∧ G.Adj z x
    · exact mem_union_right _ (mem_filter.mpr ⟨hx, h2⟩)
    · have hw1 : w = w1 := by
        rw [hLeq] at hwL; simp only [mem_insert, mem_singleton] at hwL
        rcases hwL with rfl | rfl
        · rfl
        · exact (h2 hwx).elim
      subst hw1
      exact mem_union_left _ (mem_filter.mpr ⟨hx, hwx, h2⟩)
  have hB1 : B1.card ≤ 1 := by
    refine Bstar_card_le_one G hG hno12 v S L hS hL hdisSL (by omega) w1 hw1L B1 ?_ ?_ ?_ ?_
    · refine disjoint_union_left.mpr ⟨hdisSA.mono_right ((filter_subset _ _).trans sdiff_subset),
        disjoint_left.mpr fun y hyL hyB => (mem_sdiff.mp (mem_filter.mp hyB).1).2 hyL⟩
    · exact fun x hx => (mem_filter.mp hx).2.1
    · exact fun x hx => hsafe x (mem_sdiff.mp (mem_filter.mp hx).1).1
    · intro x hx w' hw' hxw'
      have hw'2 : w' = w2 := by
        have h1 := mem_erase.mp hw'
        rw [hLeq] at h1
        simp only [mem_insert, mem_singleton] at h1
        rcases h1.2 with rfl | rfl
        · exact (h1.1 rfl).elim
        · rfl
      subst hw'2
      by_contra hno
      exact (mem_filter.mp hx).2.2 ⟨hxw'.symm, fun ⟨z, hz1, hz2⟩ => hno ⟨z, hz2, hz1⟩⟩
  have hN2 : N2.card ≤ 2 := by
    have hle := safe_indep_card_le G hG hno12 v S N2 hS
      (hdisSA.mono_right ((filter_subset _ _).trans sdiff_subset))
      (lone_nbhd_indep G w2 N2 (fun x hx => (mem_filter.mp hx).2))
      (fun x hx => hsafe x (mem_sdiff.mp (mem_filter.mp hx).1).1)
    omega
  have hATle : AT.card ≤ 3 := (card_le_card hATsub).trans ((card_union_le B1 N2).trans (by omega))
  have hsplit : AT.card + L.card = A.card := card_sdiff_add_card_eq_card hLA
  omega

private lemma U_eight_three_props {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S L A : Finset (Fin n))
    (hS : ∀ u ∈ S, G.Adj v u)
    (hL : ∀ w ∈ L, G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w)
    (hdisSL : Disjoint S L)
    (hScard : S.card = 8) (hLcard : L.card = 3)
    (hLA : L ⊆ A)
    (hdisSA : Disjoint S A)
    (hsafe : ∀ x ∈ A, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) :
    A.card ≤ 9 ∧
    2 * A.card ≤ (∑ u ∈ S, (A.filter (G.Adj u)).card) + 16 ∧
    ((∃ x ∈ A \ L, ∀ w ∈ L, G.Adj w x ∧ ¬ ∃ z, G.Adj z w ∧ G.Adj z x) → A.card ≤ 8) := by
  classical
  let AT := A \ L
  let lone (a b : Fin n) : Prop := G.Adj a b ∧ ¬ ∃ z, G.Adj z a ∧ G.Adj z b
  let degL (x : Fin n) : ℕ := (L.filter (fun w => lone w x)).card
  have hpos : ∀ x ∈ AT, 1 ≤ degL x := by
    intro x hx
    have hxA : x ∈ A := (mem_sdiff.mp hx).1
    have hxL : x ∉ L := (mem_sdiff.mp hx).2
    have hxS : x ∉ S := disjoint_right.mp hdisSA hxA
    obtain ⟨w, hwL, hwx⟩ := AT_has_lone_to_L G hG hno12 v S L hS hL hdisSL (by omega) x hxS hxL (hsafe x hxA)
    exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hwL, hwx⟩⟩
  let B1 := AT.filter (fun x => degL x = 1)
  let Q := AT.filter (fun x => 2 ≤ degL x)
  have hATcard : AT.card = B1.card + Q.card := by
    have hdis : Disjoint B1 Q :=
      disjoint_left.mpr fun x h1 h2 => by have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
    rw [← card_union_of_disjoint hdis]
    congr 1
    ext x
    simp only [B1, Q, mem_union, mem_filter]
    constructor
    · intro hx
      have := hpos x hx
      by_cases h1 : degL x = 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, by omega⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hB1w : ∀ w ∈ L, (B1.filter (fun x => lone w x)).card ≤ 1 := by
    intro w hwL
    refine Bstar_card_le_one G hG hno12 v S L hS hL hdisSL (by omega) w hwL (B1.filter (fun x => lone w x)) ?_ ?_ ?_ ?_
    · refine disjoint_union_left.mpr ⟨hdisSA.mono_right (((filter_subset _ _).trans (filter_subset _ _)).trans sdiff_subset),
        disjoint_left.mpr fun y hyL hyB => (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hyB).1).1).2 hyL⟩
    · exact fun x hx => (mem_filter.mp hx).2
    · exact fun x hx => hsafe x (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
    · intro x hx w' hw' hxw'
      by_contra hno
      have hlw' : lone w' x := ⟨hxw'.symm, fun ⟨z, hz1, hz2⟩ => hno ⟨z, hz2, hz1⟩⟩
      have hlw : lone w x := (mem_filter.mp hx).2
      have hdeg1 : degL x = 1 := (mem_filter.mp (mem_filter.mp hx).1).2
      have hne : w' ≠ w := (mem_erase.mp hw').1
      have hw'L : w' ∈ L := erase_subset w L hw'
      exact hne (card_le_one_iff.mp hdeg1.le (mem_filter.mpr ⟨hw'L, hlw'⟩) (mem_filter.mpr ⟨hwL, hlw⟩))
  have hNw : ∀ w ∈ L, (AT.filter (fun x => lone w x)).card ≤ 3 := by
    intro w hwL
    have hle := safe_indep_card_le G hG hno12 v S (AT.filter (fun x => lone w x)) hS
      (hdisSA.mono_right ((filter_subset _ _).trans sdiff_subset))
      (lone_nbhd_indep G w _ (fun x hx => (mem_filter.mp hx).2))
      (fun x hx => hsafe x (mem_sdiff.mp (mem_filter.mp hx).1).1)
    omega
  have hsumB1 : B1.card = ∑ w ∈ L, (B1.filter (fun x => lone w x)).card := by
    have h1 : B1.card = ∑ x ∈ B1, degL x := by
      trans ∑ _x ∈ B1, 1
      · simp
      · exact sum_congr rfl fun x hx => ((mem_filter.mp hx).2).symm
    rw [h1]
    simp_rw [degL, card_filter]
    rw [sum_comm]
  have hB1le3 : B1.card ≤ 3 := by
    rw [hsumB1]
    calc ∑ w ∈ L, (B1.filter (fun x => lone w x)).card
      _ ≤ ∑ _w ∈ L, 1 := sum_le_sum hB1w
      _ = 3 := by simp [hLcard]
  have hsumAT : (∑ x ∈ AT, degL x) ≤ 9 := by
    have hswap : (∑ x ∈ AT, degL x) = ∑ w ∈ L, (AT.filter (fun x => lone w x)).card := by
      simp_rw [degL, card_filter]; rw [sum_comm]
    rw [hswap]
    calc ∑ w ∈ L, (AT.filter (fun x => lone w x)).card
      _ ≤ ∑ _w ∈ L, 3 := sum_le_sum hNw
      _ = 9 := by simp [hLcard]
  have hsumSplit : (∑ x ∈ AT, degL x) = B1.card + ∑ x ∈ Q, degL x := by
    have hdis : Disjoint B1 Q :=
      disjoint_left.mpr fun x h1 h2 => by have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
    have hunion : B1 ∪ Q = AT := by
      ext x; simp only [B1, Q, mem_union, mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        have := hpos x hx
        by_cases h1 : degL x = 1
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr ⟨hx, by omega⟩
    rw [← hunion, sum_union hdis]
    congr 1
    trans ∑ _x ∈ B1, 1
    · exact sum_congr rfl fun x hx => (mem_filter.mp hx).2
    · simp
  have hQbound : 2 * Q.card + ∑ x ∈ Q, (degL x - 2) = ∑ x ∈ Q, degL x := by
    have hpt : ∀ x ∈ Q, 2 + (degL x - 2) = degL x := fun x hx => by have := (mem_filter.mp hx).2; omega
    rw [← sum_congr rfl hpt, sum_add_distrib, sum_const, smul_eq_mul, mul_comm]
  have hmain : 2 * AT.card + ∑ x ∈ Q, (degL x - 2) ≤ 12 := by omega
  have hAcard_eq : A.card = AT.card + 3 := by
    have : AT.card + L.card = A.card := card_sdiff_add_card_eq_card hLA
    omega
  have hAle9 : A.card ≤ 9 := by omega
  refine ⟨hAle9, ?_, ?_⟩
  · by_cases hA9 : A.card = 9
    · by_contra! hlt
      have hE_le1 : (∑ u ∈ S, (A.filter (G.Adj u)).card) ≤ 1 := by omega
      have hcompat : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → ∀ u ∈ S, G.Adj x u → ¬ G.Adj y u := by
        intro x hx y hy hxy u hu hxu hyu
        have h2u : 2 ≤ (A.filter (G.Adj u)).card := by
          have hsub : ({x, y} : Finset (Fin n)) ⊆ A.filter (G.Adj u) := by
            intro z hz; simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact mem_filter.mpr ⟨hx, hxu.symm⟩
            · exact mem_filter.mpr ⟨hy, hyu.symm⟩
          have := card_le_card hsub
          rwa [card_pair hxy.ne] at this
        have hle := single_le_sum (f := fun u => (A.filter (G.Adj u)).card) (fun _ _ => Nat.zero_le _) hu
        omega
      obtain ⟨T, hTA, hTfree, hT4⟩ := free_four_of_nine G hG A (by omega)
      have hUfree := compatible_union_free G hG v S T hS hTfree
        (fun x hx => hsafe x (hTA hx)) (fun x hx y hy => hcompat x (hTA hx) y (hTA hy))
      have hle := hno12 (S ∪ T) hUfree
      rw [card_union_of_disjoint (hdisSA.mono_right hTA), hScard, hT4] at hle
      omega
    · omega
  · rintro ⟨x, hxAT, hxall⟩
    have hx3 : degL x = 3 := by
      have heq : L.filter (fun w => lone w x) = L := filter_true_of_mem fun w hw => hxall w hw
      dsimp only [degL]; rw [heq, hLcard]
    have hxQ : x ∈ Q := mem_filter.mpr ⟨hxAT, by omega⟩
    have hge1 : 1 ≤ ∑ y ∈ Q, (degL y - 2) := by
      have := single_le_sum (f := fun y => degL y - 2) (fun _ _ => Nat.zero_le _) hxQ
      omega
    omega

-- ============================================================================
-- Section 7: Core-averaged bound with slack, closing n = 58, n = 57, and
-- tightening n = 56 to loneDeg >= 3
-- ============================================================================

private lemma core_averaged_outsider_with_slack {n : ℕ} (G C : SimpleGraph (Fin n))
    (hCG : C ≤ G) (hdens : C.edgeFinset.card ≤ (C.cliqueFinset 3).card)
    (Vc : Finset (Fin n)) (hVc : Vc = univ.filter (fun v : Fin n => 0 < C.degree v))
    (loneDeg : Fin n → ℕ)
    (hloneDeg : ∀ u, loneDeg u = (univ.filter fun w => G.Adj u w ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z w).card)
    (A : Fin n → Finset (Fin n))
    (hA : ∀ v, A v = (insert v (C.neighborFinset v))ᶜ.filter (fun x =>
      G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
      ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)) :
    (∑ v ∈ Vc, (2 * n + 2 * C.degree v +
      ∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card)) +
    (∑ v ∈ Vc, ∑ x ∈ (insert v (C.neighborFinset v))ᶜ \ A v,
      (((C.neighborFinset v).filter (G.Adj x)).card +
        ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2)) +
    (∑ v ∈ Vc, ∑ u ∈ C.neighborFinset v,
      (loneDeg u - ((insert v (C.neighborFinset v))ᶜ.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card)) ≤
      ∑ v ∈ Vc, (2 * (A v).card + 2 + C.degree v * (G.degree v + loneDeg v)) := by
  classical
  have hper : ∀ v : Fin n,
      2 * n + (∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) +
        (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) +
        (∑ x ∈ (insert v (C.neighborFinset v))ᶜ \ A v,
          (((C.neighborFinset v).filter (G.Adj x)).card +
            ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2)) +
        (∑ u ∈ C.neighborFinset v,
          (loneDeg u - ((insert v (C.neighborFinset v))ᶜ.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card)) ≤
      2 * (A v).card + C.degree v + 2 +
        ∑ u ∈ C.neighborFinset v, (G.degree u + loneDeg u) := by
    intro v
    let S := C.neighborFinset v
    let X := (insert v S)ᶜ
    let B := X \ A v
    have hAX : A v ⊆ X := by rw [hA v]; exact filter_subset _ _
    have hBX : B ⊆ X := sdiff_subset
    have hunsafe : ∀ x ∈ B,
        2 ≤ (S.filter (G.Adj x)).card +
          (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card := by
      intro x hx
      have hxX : x ∈ X := (mem_sdiff.mp hx).1
      have hbad : ¬ (G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
          ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) := by
        intro hok
        apply (mem_sdiff.mp hx).2
        rw [hA v]
        exact mem_filter.mpr ⟨hxX, hok⟩
      by_cases hl : ∃ a ∈ S, G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a
      · obtain ⟨a, ha, hadj, hlone⟩ := hl
        have h1 : 0 < (S.filter (G.Adj x)).card := card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hadj⟩⟩
        have h2 : 0 < (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card :=
          card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hadj, hlone⟩⟩
        omega
      · by_contra! hlt
        apply hbad
        refine ⟨?_, ?_⟩
        · intro a ha b hb hab _
          have hle1 : (S.filter (G.Adj x)).card ≤ 1 := by omega
          exact hab (card_le_one_iff.mp hle1 (mem_filter.mpr ha) (mem_filter.mpr hb))
        · intro a ha hadj
          by_contra hnone
          exact hl ⟨a, ha, hadj, hnone⟩
    have hBbound : 2 * B.card +
        (∑ x ∈ B, ((S.filter (G.Adj x)).card +
          (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2)) ≤
        (∑ u ∈ S, (B.filter (G.Adj u)).card) +
        (∑ u ∈ S, (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card) := by
      have hpt : ∀ x ∈ B, 2 + ((S.filter (G.Adj x)).card +
          (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2) =
          (S.filter (G.Adj x)).card +
          (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card := fun x hx => by
        have := hunsafe x hx; omega
      calc
        2 * B.card + (∑ x ∈ B, ((S.filter (G.Adj x)).card +
            (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2))
          = ∑ x ∈ B, (2 + ((S.filter (G.Adj x)).card +
              (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2)) := by
            rw [sum_add_distrib, sum_const, smul_eq_mul, mul_comm]
        _ = ∑ x ∈ B, ((S.filter (G.Adj x)).card +
              (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card) :=
            sum_congr rfl hpt
        _ = (∑ x ∈ B, (S.filter (G.Adj x)).card) +
            (∑ x ∈ B, (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card) :=
            sum_add_distrib
        _ ≤ (∑ x ∈ B, (S.filter (G.Adj x)).card) +
            (∑ x ∈ X, (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card) :=
            Nat.add_le_add_left (sum_le_sum_of_subset_of_nonneg hBX (fun _ _ _ => Nat.zero_le _)) _
        _ = (∑ u ∈ S, (B.filter (G.Adj u)).card) +
            (∑ u ∈ S, (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card) := by
            congr 1
            · simp_rw [card_filter]; rw [sum_comm]
              exact sum_congr rfl fun u _ => sum_congr rfl fun x _ => by simp [G.adj_comm]
            · simp_rw [card_filter]; rw [sum_comm]
              refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
              have hiff : (G.Adj x u ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z u) ↔
                  (G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x) := by
                constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, fun ⟨z, hz1, hz2⟩ => h2 ⟨z, hz2, hz1⟩⟩
              exact if_congr hiff rfl rfl
    have hpart : (∑ u ∈ S, (B.filter (G.Adj u)).card) + (∑ u ∈ S, ((A v).filter (G.Adj u)).card) =
        ∑ u ∈ S, (X.filter (G.Adj u)).card := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro u _
      have hdis : Disjoint (B.filter (G.Adj u)) ((A v).filter (G.Adj u)) :=
        Finset.disjoint_left.mpr fun x h1 h2 => (mem_sdiff.mp (mem_filter.mp h1).1).2 (mem_filter.mp h2).1
      rw [← card_union_of_disjoint hdis, ← filter_union, sdiff_union_of_subset hAX]
    have hcap : ∀ u ∈ S,
        (X.filter (G.Adj u)).card + (S.filter (C.Adj u)).card + 1 ≤ G.degree u ∧
        (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card ≤ loneDeg u := by
      intro u hu
      have huv : G.Adj u v := hCG ((C.mem_neighborFinset v u).mp hu).symm
      constructor
      · have hdis1 : Disjoint (X.filter (G.Adj u)) (S.filter (C.Adj u)) := by
          apply Finset.disjoint_left.mpr
          intro x hx1 hx2
          exact (mem_compl.mp (mem_filter.mp hx1).1) (mem_insert_of_mem (mem_filter.mp hx2).1)
        have hnv : v ∉ (X.filter (G.Adj u)) ∪ (S.filter (C.Adj u)) := by
          intro hv
          rcases mem_union.mp hv with h1 | h2
          · exact (mem_compl.mp (mem_filter.mp h1).1) (mem_insert_self _ _)
          · exact C.notMem_neighborFinset_self v (mem_filter.mp h2).1
        have hsub : insert v ((X.filter (G.Adj u)) ∪ (S.filter (C.Adj u))) ⊆ G.neighborFinset u := by
          intro x hx
          apply (G.mem_neighborFinset u x).mpr
          rcases mem_insert.mp hx with rfl | hx
          · exact huv
          · rcases mem_union.mp hx with h1 | h2
            · exact (mem_filter.mp h1).2
            · exact hCG (mem_filter.mp h2).2
        have hle := card_le_card hsub
        rw [card_insert_of_notMem hnv, card_union_of_disjoint hdis1, G.card_neighborFinset_eq_degree] at hle
        omega
      · rw [hloneDeg u]
        exact card_le_card (filter_subset_filter _ (subset_univ X))
    have hsumcap : (∑ u ∈ S, (X.filter (G.Adj u)).card) +
        (∑ u ∈ S, (S.filter (C.Adj u)).card) + S.card +
        (∑ u ∈ S, (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card) +
        (∑ u ∈ S, (loneDeg u - (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card)) ≤
        ∑ u ∈ S, (G.degree u + loneDeg u) := by
      have h1 : (∑ u ∈ S, ((X.filter (G.Adj u)).card + (S.filter (C.Adj u)).card + 1 +
          (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card +
          (loneDeg u - (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card))) ≤
          ∑ u ∈ S, (G.degree u + loneDeg u) :=
        sum_le_sum fun u hu => by have := hcap u hu; omega
      simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] using h1
    have hXcard : X.card + (S.card + 1) = n := by
      have hvS : v ∉ S := C.notMem_neighborFinset_self v
      change (insert v S)ᶜ.card + (S.card + 1) = n
      rw [← card_insert_of_notMem hvS, card_compl_add_card, Fintype.card_fin]
    have hAB : B.card + (A v).card = X.card := card_sdiff_add_card_eq_card hAX
    have hScard : S.card = C.degree v := C.card_neighborFinset_eq_degree v
    dsimp only [S, X, B] at hBbound hpart hsumcap hXcard hScard hAB
    omega
  have hsum_per := sum_le_sum (s := Vc) fun v _ => hper v
  simp only [sum_add_distrib] at hsum_per
  have hlink_Vc : (∑ v ∈ Vc, ∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) =
      ∑ v : Fin n, ∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card := by
    apply sum_subset (subset_univ Vc)
    intro v _ hv
    have h0 : C.degree v = 0 := by
      rw [hVc] at hv
      simp only [mem_filter, mem_univ, true_and, not_lt] at hv
      omega
    have he : C.neighborFinset v = ∅ := card_eq_zero.mp (by rw [C.card_neighborFinset_eq_degree]; exact h0)
    simp [he]
  have hdeg_Vc : (∑ v ∈ Vc, C.degree v) = ∑ v : Fin n, C.degree v := by
    apply sum_subset (subset_univ Vc)
    intro v _ hv
    rw [hVc] at hv
    simp only [mem_filter, mem_univ, true_and, not_lt] at hv
    omega
  have hlink_ge : 3 * ∑ v ∈ Vc, C.degree v ≤
      ∑ v ∈ Vc, ∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card := by
    rw [hlink_Vc, sum_link_eq_six_tri, hdeg_Vc, C.sum_degrees_eq_twice_card_edges]
    omega
  have hswap : ∀ f : Fin n → ℕ,
      (∑ v ∈ Vc, ∑ u ∈ C.neighborFinset v, f u) = ∑ v ∈ Vc, C.degree v * f v := by
    intro f
    have hfull : (∑ v ∈ Vc, ∑ u ∈ C.neighborFinset v, f u) =
        ∑ v : Fin n, ∑ u ∈ C.neighborFinset v, f u := by
      apply sum_subset (subset_univ Vc)
      intro v _ hv
      have h0 : C.degree v = 0 := by
        rw [hVc] at hv
        simp only [mem_filter, mem_univ, true_and, not_lt] at hv; omega
      have he : C.neighborFinset v = ∅ := card_eq_zero.mp (by rw [C.card_neighborFinset_eq_degree]; exact h0)
      simp [he]
    rw [hfull]
    have h1 : (∑ v : Fin n, ∑ u ∈ C.neighborFinset v, f u) = ∑ u : Fin n, C.degree u * f u := by
      have hN : ∀ v : Fin n, C.neighborFinset v = univ.filter (C.Adj v) := fun v => by ext; simp
      simp_rw [hN, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      have h2 : (∑ v : Fin n, if C.Adj v u then f u else 0) =
          ∑ _v ∈ C.neighborFinset u, f u := by
        rw [hN, sum_filter]
        exact sum_congr rfl fun v _ => by simp [C.adj_comm]
      rw [h2, sum_const, smul_eq_mul, C.card_neighborFinset_eq_degree]
    rw [h1]
    symm
    apply sum_subset (subset_univ Vc)
    intro v _ hv
    have h0 : C.degree v = 0 := by
      rw [hVc] at hv
      simp only [mem_filter, mem_univ, true_and, not_lt] at hv; omega
    simp [h0]
  rw [hswap (fun u => G.degree u), hswap loneDeg] at hsum_per
  simp only [mul_add, sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum] at hsum_per ⊢
  omega

private lemma free_four_from_two_isolated_plus_three {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (u1 u2 y1 y2 y3 : Fin n)
    (hu12 : u1 ≠ u2) (hnu12 : ¬ G.Adj u1 u2)
    (hy12 : y1 ≠ y2) (hy13 : y1 ≠ y3) (hy23 : y2 ≠ y3)
    (hu1y : u1 ≠ y1 ∧ u1 ≠ y2 ∧ u1 ≠ y3)
    (hu2y : u2 ≠ y1 ∧ u2 ≠ y2 ∧ u2 ≠ y3)
    (hnu1y : ¬ G.Adj u1 y1 ∧ ¬ G.Adj u1 y2 ∧ ¬ G.Adj u1 y3)
    (hnu2y : ¬ G.Adj u2 y1 ∧ ¬ G.Adj u2 y2 ∧ ¬ G.Adj u2 y3) :
    ∃ T : Finset (Fin n), T ⊆ {u1, u2, y1, y2, y3} ∧
      (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 4 := by
  classical
  have hmk : ∀ a b : Fin n, a ∈ ({y1, y2, y3} : Finset (Fin n)) → b ∈ ({y1, y2, y3} : Finset (Fin n)) →
      a ≠ b → (¬ G.Adj a b ∨ ∃ z, G.Adj z a ∧ G.Adj z b) →
      ∃ T : Finset (Fin n), T ⊆ {u1, u2, y1, y2, y3} ∧
        (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 4 := by
    intro a b ha hb hab hok
    have ha_ne : a ≠ u1 ∧ a ≠ u2 := by
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨hu1y.1.symm, hu2y.1.symm⟩
      · exact ⟨hu1y.2.1.symm, hu2y.2.1.symm⟩
      · exact ⟨hu1y.2.2.symm, hu2y.2.2.symm⟩
    have hb_ne : b ≠ u1 ∧ b ≠ u2 := by
      simp only [mem_insert, mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨hu1y.1.symm, hu2y.1.symm⟩
      · exact ⟨hu1y.2.1.symm, hu2y.2.1.symm⟩
      · exact ⟨hu1y.2.2.symm, hu2y.2.2.symm⟩
    have hna : ¬ G.Adj u1 a ∧ ¬ G.Adj u2 a := by
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨hnu1y.1, hnu2y.1⟩
      · exact ⟨hnu1y.2.1, hnu2y.2.1⟩
      · exact ⟨hnu1y.2.2, hnu2y.2.2⟩
    have hnb : ¬ G.Adj u1 b ∧ ¬ G.Adj u2 b := by
      simp only [mem_insert, mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨hnu1y.1, hnu2y.1⟩
      · exact ⟨hnu1y.2.1, hnu2y.2.1⟩
      · exact ⟨hnu1y.2.2, hnu2y.2.2⟩
    refine ⟨{u1, u2, a, b}, ?_, (free_iff_no_tri_no_lone hG _).mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx ha hb ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inr hb)
    · intro x hx y hy z hz ⟨hxy, hxz, hyz⟩
      simp only [mem_insert, mem_singleton] at hx hy hz
      rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl <;>
      first
        | exact G.irrefl hxy | exact G.irrefl hxz | exact G.irrefl hyz
        | exact hnu12 hxy | exact hnu12 hxy.symm | exact hnu12 hxz | exact hnu12 hxz.symm | exact hnu12 hyz | exact hnu12 hyz.symm
        | exact hna.1 hxy | exact hna.1 hxy.symm | exact hna.1 hxz | exact hna.1 hxz.symm | exact hna.1 hyz | exact hna.1 hyz.symm
        | exact hna.2 hxy | exact hna.2 hxy.symm | exact hna.2 hxz | exact hna.2 hxz.symm | exact hna.2 hyz | exact hna.2 hyz.symm
        | exact hnb.1 hxy | exact hnb.1 hxy.symm | exact hnb.1 hxz | exact hnb.1 hxz.symm | exact hnb.1 hyz | exact hnb.1 hyz.symm
        | exact hnb.2 hxy | exact hnb.2 hxy.symm | exact hnb.2 hxz | exact hnb.2 hxz.symm | exact hnb.2 hyz | exact hnb.2 hyz.symm
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
      all_goals first
        | exact (G.irrefl hxy).elim
        | exact (hnu12 hxy).elim | exact (hnu12 hxy.symm).elim
        | exact (hna.1 hxy).elim | exact (hna.1 hxy.symm).elim
        | exact (hna.2 hxy).elim | exact (hna.2 hxy.symm).elim
        | exact (hnb.1 hxy).elim | exact (hnb.1 hxy.symm).elim
        | exact (hnb.2 hxy).elim | exact (hnb.2 hxy.symm).elim
        | exact hok.elim (fun h => (h hxy).elim) id
        | exact hok.elim (fun h => (h hxy.symm).elim) (fun ⟨z, hz1, hz2⟩ => ⟨z, hz2, hz1⟩)
    · have h1 : u1 ∉ ({u2, a, b} : Finset (Fin n)) := by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨hu12, ha_ne.1.symm, hb_ne.1.symm⟩
      have h2 : u2 ∉ ({a, b} : Finset (Fin n)) := by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨ha_ne.2.symm, hb_ne.2.symm⟩
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_pair hab]
  by_cases h12 : G.Adj y1 y2
  · by_cases h13 : G.Adj y1 y3
    · by_cases h23 : G.Adj y2 y3
      · exact hmk y1 y2 (by simp) (by simp) hy12 (Or.inr ⟨y3, h13.symm, h23.symm⟩)
      · exact hmk y2 y3 (by simp) (by simp) hy23 (Or.inl h23)
    · exact hmk y1 y3 (by simp) (by simp) hy13 (Or.inl h13)
  · exact hmk y1 y2 (by simp) (by simp) hy12 (Or.inl h12)

private lemma nodup_of_toFinset_card_eq {α : Type*} [DecidableEq α] :
    ∀ (l : List α), l.toFinset.card = l.length → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    simp only [List.toFinset_cons, List.length_cons] at h
    by_cases ha : a ∈ t.toFinset
    · rw [insert_eq_of_mem ha] at h
      have hle := List.toFinset_card_le t
      omega
    · rw [card_insert_of_notMem ha] at h
      exact List.nodup_cons.mpr ⟨fun hm => ha (List.mem_toFinset.mpr hm),
        nodup_of_toFinset_card_eq t (by omega)⟩

private lemma free_four_caseB {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (w1 w2 w3 u1 u2 u3 y1 y2 : Fin n)
    (hcard8 : ({w1, w2, w3, u1, u2, u3, y1, y2} : Finset (Fin n)).card = 8)
    (hw12_nadj : ¬ G.Adj w1 w2)
    (hu1_iso : ¬ G.Adj u1 u2 ∧ ¬ G.Adj u1 u3 ∧ ¬ G.Adj u1 y1 ∧ ¬ G.Adj u1 y2)
    (hu23_notlone : G.Adj u2 u3 → ∃ z, G.Adj z u2 ∧ G.Adj z u3)
    (hw12_u3 : ¬ G.Adj w1 u3 ∧ ¬ G.Adj w2 u3)
    (hu2_lone_w : (G.Adj w1 u2 ∧ ¬ ∃ z, G.Adj z w1 ∧ G.Adj z u2) ∧
                  (G.Adj w2 u2 ∧ ¬ ∃ z, G.Adj z w2 ∧ G.Adj z u2))
    (hu3_lone_w3 : G.Adj w3 u3 ∧ ¬ ∃ z, G.Adj z w3 ∧ G.Adj z u3)
    (hu3_y_lone : (G.Adj u3 y1 → ¬ ∃ z, G.Adj z u3 ∧ G.Adj z y1) ∧
                  (G.Adj u3 y2 → ¬ ∃ z, G.Adj z u3 ∧ G.Adj z y2))
    (hy_hits_w : (∀ y ∈ ({y1, y2} : Finset (Fin n)),
      G.Adj w1 y ∨ G.Adj w2 y ∨ G.Adj w3 y)) :
    ∃ T : Finset (Fin n), T ⊆ {w1, w2, w3, u1, u2, u3, y1, y2} ∧
      (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 4 := by
  classical
  -- Extract pairwise distinctness from card = 8
  have hne : ∀ a b : Fin n, a ≠ b → a ∈ ({w1, w2, w3, u1, u2, u3, y1, y2} : Finset (Fin n)) →
      b ∈ ({w1, w2, w3, u1, u2, u3, y1, y2} : Finset (Fin n)) → True := fun _ _ _ _ _ => trivial
  have hpair_ne : ∀ (S : Finset (Fin n)), S ⊆ {w1, w2, w3, u1, u2, u3, y1, y2} →
      ∀ (a b c d : Fin n), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)).card = 4 := by
    intro _ _ a b c d hab hac had hbc hbd hcd
    have h1 : a ∉ ({b, c, d} : Finset (Fin n)) := by simp [hab, hac, had]
    have h2 : b ∉ ({c, d} : Finset (Fin n)) := by simp [hbc, hbd]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_pair hcd]
  -- Helper: from card = 8 of 8 elements, extract all pairwise inequalities
  have hnodup : [w1, w2, w3, u1, u2, u3, y1, y2].Nodup := by
    apply nodup_of_toFinset_card_eq
    have hset : ([w1, w2, w3, u1, u2, u3, y1, y2] : List (Fin n)).toFinset =
        {w1, w2, w3, u1, u2, u3, y1, y2} := by
      ext x; simp [or_assoc]
    rw [hset, hcard8]
    rfl
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnodup
  rcases hnodup with ⟨⟨hw1w2, hw1w3, hw1u1, hw1u2, hw1u3, hw1y1, hw1y2⟩,
    ⟨hw2w3, hw2u1, hw2u2, hw2u3, hw2y1, hw2y2⟩,
    ⟨hw3u1, hw3u2, hw3u3, hw3y1, hw3y2⟩,
    ⟨hu1u2, hu1u3, hu1y1, hu1y2⟩,
    ⟨hu2u3, hu2y1, hu2y2⟩,
    ⟨hu3y1, hu3y2⟩,
    hy1y2⟩
  -- No y in {y1, y2} is adjacent to both u2 and u3
  have hnot_both : ∀ y ∈ ({y1, y2} : Finset (Fin n)), ¬ (G.Adj u2 y ∧ G.Adj u3 y) := by
    intro y hy ⟨hu2y, hu3y⟩
    rcases hy_hits_w y hy with h1 | h2 | h3
    · exact hu2_lone_w.1.2 ⟨y, h1.symm, hu2y.symm⟩
    · exact hu2_lone_w.2.2 ⟨y, h2.symm, hu2y.symm⟩
    · exact hu3_lone_w3.2 ⟨y, h3.symm, hu3y.symm⟩
  -- Helper: if y in {y1, y2} has no edges to u2 and u3, {u1, u2, u3, y} is free
  have hfree_u123 : ∀ y : Fin n, y ∈ ({y1, y2} : Finset (Fin n)) →
      ¬ G.Adj u2 y → ¬ G.Adj u3 y →
      ∃ T : Finset (Fin n), T ⊆ {w1, w2, w3, u1, u2, u3, y1, y2} ∧
        (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 4 := by
    intro y hy hnu2y hnu3y
    have hu1y_nadj : ¬ G.Adj u1 y := by
      simp only [mem_insert, mem_singleton] at hy; rcases hy with rfl | rfl; exact hu1_iso.2.2.1; exact hu1_iso.2.2.2
    have hne_y : u1 ≠ y ∧ u2 ≠ y ∧ u3 ≠ y := by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl; exact ⟨hu1y1, hu2y1, hu3y1⟩; exact ⟨hu1y2, hu2y2, hu3y2⟩
    refine ⟨{u1, u2, u3, y}, ?_, (free_iff_no_tri_no_lone hG _).mpr ⟨?_, ?_⟩,
      hpair_ne _ subset_rfl u1 u2 u3 y hu1u2 hu1u3 hne_y.1 hu2u3 hne_y.2.1 hne_y.2.2⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx hy ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · right; right; right; left; rfl
      · right; right; right; right; left; rfl
      · right; right; right; right; right; left; rfl
      · rcases hy with rfl | rfl <;> simp
    · intro a ha b hb c hc ⟨hab, hac, hbc⟩
      simp only [mem_insert, mem_singleton] at ha hb hc
      rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      first
        | exact G.irrefl hab | exact G.irrefl hac | exact G.irrefl hbc
        | exact hu1_iso.1 hab | exact hu1_iso.1 hab.symm | exact hu1_iso.1 hac | exact hu1_iso.1 hac.symm | exact hu1_iso.1 hbc | exact hu1_iso.1 hbc.symm
        | exact hu1_iso.2.1 hab | exact hu1_iso.2.1 hab.symm | exact hu1_iso.2.1 hac | exact hu1_iso.2.1 hac.symm | exact hu1_iso.2.1 hbc | exact hu1_iso.2.1 hbc.symm
        | exact hu1y_nadj hab | exact hu1y_nadj hab.symm | exact hu1y_nadj hac | exact hu1y_nadj hac.symm | exact hu1y_nadj hbc | exact hu1y_nadj hbc.symm
        | exact hnu2y hab | exact hnu2y hab.symm | exact hnu2y hac | exact hnu2y hac.symm | exact hnu2y hbc | exact hnu2y hbc.symm
        | exact hnu3y hab | exact hnu3y hab.symm | exact hnu3y hac | exact hnu3y hac.symm | exact hnu3y hbc | exact hnu3y hbc.symm
    · intro a ha b hb hab
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      all_goals first
        | exact (G.irrefl hab).elim
        | exact (hu1_iso.1 hab).elim | exact (hu1_iso.1 hab.symm).elim
        | exact (hu1_iso.2.1 hab).elim | exact (hu1_iso.2.1 hab.symm).elim
        | exact (hu1y_nadj hab).elim | exact (hu1y_nadj hab.symm).elim
        | exact (hnu2y hab).elim | exact (hnu2y hab.symm).elim
        | exact (hnu3y hab).elim | exact (hnu3y hab.symm).elim
        | exact hu23_notlone hab
        | exact (let ⟨z, h1, h2⟩ := hu23_notlone hab.symm; ⟨z, h2, h1⟩)
  -- Helper: if y in {y1, y2} is adjacent to u2 (hence not u3, not w1, not w2), {w1, w2, u3, y} is indep
  have hindep_w12u3 : ∀ y : Fin n, y ∈ ({y1, y2} : Finset (Fin n)) → G.Adj u2 y →
      ∃ T : Finset (Fin n), T ⊆ {w1, w2, w3, u1, u2, u3, y1, y2} ∧
        (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ T) ∧ T.card = 4 := by
    intro y hy hu2y
    have hnu3y : ¬ G.Adj u3 y := fun h => hnot_both y hy ⟨hu2y, h⟩
    have hnw1y : ¬ G.Adj w1 y := fun h => hu2_lone_w.1.2 ⟨y, h.symm, hu2y.symm⟩
    have hnw2y : ¬ G.Adj w2 y := fun h => hu2_lone_w.2.2 ⟨y, h.symm, hu2y.symm⟩
    have hne_y : w1 ≠ y ∧ w2 ≠ y ∧ u3 ≠ y := by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl; exact ⟨hw1y1, hw2y1, hu3y1⟩; exact ⟨hw1y2, hw2y2, hu3y2⟩
    refine ⟨{w1, w2, u3, y}, ?_, free_of_indep ?_,
      hpair_ne _ subset_rfl w1 w2 u3 y hw1w2 hw1u3 hne_y.1 hw2u3 hne_y.2.1 hne_y.2.2⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx hy ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · right; right; right; right; right; left; rfl
      · rcases hy with rfl | rfl <;> simp
    · intro a ha b hb _ hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
        | exact G.irrefl hab
        | exact hw12_nadj hab | exact hw12_nadj hab.symm
        | exact hw12_u3.1 hab | exact hw12_u3.1 hab.symm
        | exact hw12_u3.2 hab | exact hw12_u3.2 hab.symm
        | exact hnw1y hab | exact hnw1y hab.symm
        | exact hnw2y hab | exact hnw2y hab.symm
        | exact hnu3y hab | exact hnu3y hab.symm
  by_cases h21 : G.Adj u2 y1
  · exact hindep_w12u3 y1 (by simp) h21
  · by_cases h22 : G.Adj u2 y2
    · exact hindep_w12u3 y2 (by simp) h22
    · by_cases h31 : G.Adj u3 y1
      · by_cases h32 : G.Adj u3 y2
        · -- Both y1, y2 adjacent to u3 (lone), so y1, y2 nonadjacent -> {u1, u2, y1, y2} indep!
          have hny12 : ¬ G.Adj y1 y2 := fun h => hu3_y_lone.1 h31 ⟨y2, h32.symm, h.symm⟩
          refine ⟨{u1, u2, y1, y2}, ?_, free_of_indep ?_,
            hpair_ne _ subset_rfl u1 u2 y1 y2 hu1u2 hu1y1 hu1y2 hu2y1 hu2y2 hy1y2⟩
          · intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢
            rcases hx with rfl | rfl | rfl | rfl <;> simp
          · intro a ha b hb _ hab
            simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
            rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
            first
              | exact G.irrefl hab
              | exact hu1_iso.1 hab | exact hu1_iso.1 hab.symm
              | exact hu1_iso.2.2.1 hab | exact hu1_iso.2.2.1 hab.symm
              | exact hu1_iso.2.2.2 hab | exact hu1_iso.2.2.2 hab.symm
              | exact h21 hab | exact h21 hab.symm
              | exact h22 hab | exact h22 hab.symm
              | exact hny12 hab | exact hny12 hab.symm
        · exact hfree_u123 y2 (by simp) h22 h32
      · exact hfree_u123 y1 (by simp) h21 h31

private lemma zero_edges_union_free {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (v : Fin n) (S T : Finset (Fin n))
    (hSv : ∀ u ∈ S, G.Adj v u)
    (hScard : S.card = 8)
    (hTfree : ∀ K, G.IsBigMaximalClique K → ¬ K ⊆ T)
    (hTcard : T.card = 4)
    (hno : ∀ x ∈ T, ∀ u ∈ S, ¬ G.Adj x u)
    (hdis : Disjoint S T) : False := by
  have hUfree := compatible_union_free G hG v S T hSv hTfree
    (fun x hx => ⟨fun a ha _ _ _ _ => (hno x hx a ha.1 ha.2).elim,
      fun a ha hxa => (hno x hx a ha hxa).elim⟩)
    (fun x hx _ _ _ u hu hxu _ => hno x hx u hu hxu)
  have hle := hno12 (S ∪ T) hUfree
  rw [card_union_of_disjoint hdis, hScard, hTcard] at hle
  omega

set_option maxHeartbeats 800000 in
private lemma close_n57 (G C : SimpleGraph (Fin 57)) (hG : G.CliqueFree 4) (hCG : C ≤ G)
    (hno12 : ∀ U : Finset (Fin 57), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11)
    (hdeg11 : ∀ v : Fin 57, G.degree v ≤ 11)
    (hCtri : ∀ a b, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b)
    (Vc : Finset (Fin 57)) (hVc : Vc = univ.filter (fun v : Fin 57 => 0 < C.degree v))
    (hVcne : Vc.Nonempty)
    (A : Fin 57 → Finset (Fin 57))
    (hA : ∀ v, A v = (insert v (C.neighborFinset v))ᶜ.filter (fun x =>
      G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
      ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a))
    (hc8 : ∀ v ∈ Vc, C.degree v = 8)
    (hg11 : ∀ v ∈ Vc, G.degree v = 11)
    (hl3 : ∀ v ∈ Vc, (univ.filter fun w => G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w).card = 3)
    (hAeq : ∀ v ∈ Vc, 2 * (A v).card = (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + 16)
    (hBeq : ∀ v ∈ Vc, ∀ x ∈ (insert v (C.neighborFinset v))ᶜ \ A v,
      ((C.neighborFinset v).filter (G.Adj x)).card +
        ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card = 2)
    (hXeq : ∀ v ∈ Vc, ∀ u ∈ C.neighborFinset v,
      ((insert v (C.neighborFinset v))ᶜ.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card =
        (univ.filter fun w => G.Adj u w ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z w).card) :
    False := by
  classical
  let lone (a b : Fin 57) : Prop := G.Adj a b ∧ ¬ ∃ z, G.Adj z a ∧ G.Adj z b
  have hlone_symm : ∀ a b, lone a b ↔ lone b a := fun a b =>
    ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun ⟨z, hz1, hz2⟩ => h2 ⟨z, hz2, hz1⟩⟩,
     fun ⟨h1, h2⟩ => ⟨h1.symm, fun ⟨z, hz1, hz2⟩ => h2 ⟨z, hz2, hz1⟩⟩⟩
  let L (v : Fin 57) : Finset (Fin 57) := univ.filter (lone v)
  have hS_sub_Vc : ∀ v ∈ Vc, ∀ u ∈ C.neighborFinset v, u ∈ Vc := by
    intro v _ u hu
    rw [hVc]
    exact mem_filter.mpr ⟨mem_univ _, (C.degree_pos_iff_exists_adj u).mpr ⟨v, ((C.mem_neighborFinset v u).mp hu).symm⟩⟩
  have hdisSL : ∀ v ∈ Vc, Disjoint (C.neighborFinset v) (L v) := by
    intro v _
    refine disjoint_left.mpr fun w hwC hwL => ?_
    obtain ⟨z, hzv, hzw⟩ := hCtri v w ((C.mem_neighborFinset v w).mp hwC)
    exact (mem_filter.mp hwL).2.2 ⟨z, hCG hzv, hCG hzw⟩
  have hN_eq : ∀ v ∈ Vc, C.neighborFinset v ∪ L v = G.neighborFinset v := by
    intro v hv
    refine eq_of_subset_of_card_le ?_ ?_
    · intro w hw
      apply (G.mem_neighborFinset v w).mpr
      rcases mem_union.mp hw with h1 | h2
      · exact hCG ((C.mem_neighborFinset v w).mp h1)
      · exact (mem_filter.mp h2).2.1
    · rw [card_union_of_disjoint (hdisSL v hv), C.card_neighborFinset_eq_degree,
        G.card_neighborFinset_eq_degree, hc8 v hv, hg11 v hv, hl3 v hv]
  have hAdj_iff : ∀ v ∈ Vc, ∀ x : Fin 57, G.Adj v x ↔ C.Adj v x ∨ lone v x := by
    intro v hv x
    constructor
    · intro h
      have hx : x ∈ C.neighborFinset v ∪ L v := by
        rw [hN_eq v hv]; exact (G.mem_neighborFinset v x).mpr h
      rcases mem_union.mp hx with h1 | h2
      · exact Or.inl ((C.mem_neighborFinset v x).mp h1)
      · exact Or.inr (mem_filter.mp h2).2
    · rintro (h | h)
      · exact hCG h
      · exact h.1
  have hLA : ∀ v ∈ Vc, L v ⊆ A v := by
    intro v hv w hw
    have hlw : lone v w := (mem_filter.mp hw).2
    have hnw : ∀ u ∈ C.neighborFinset v, ¬ G.Adj w u := fun u hu hwu =>
      hlw.2 ⟨u, (hCG ((C.mem_neighborFinset v u).mp hu)).symm, hwu.symm⟩
    rw [hA v]
    refine mem_filter.mpr ⟨mem_compl.mpr ?_, ?_, ?_⟩
    · intro hmem
      rcases mem_insert.mp hmem with rfl | hS
      · exact G.irrefl hlw.1
      · exact (disjoint_left.mp (hdisSL v hv) hS) hw
    · intro a ha _ _ _ _; exact (hnw a ha.1 ha.2).elim
    · intro a ha hwa; exact (hnw a ha hwa).elim
  -- Step 1: No lone edges inside Vc (sum_{w in L v} |L w| >= 26 > 25)
  have hL_not_Vc : ∀ v ∈ Vc, ∀ w ∈ L v, w ∉ Vc := by
    intro v hv w0 hw0 hw0Vc
    let S := C.neighborFinset v
    let X := (insert v S)ᶜ
    let B := X \ A v
    let AT := A v \ L v
    have hSsub : ∀ u ∈ S, G.Adj v u := fun u hu => hCG ((C.mem_neighborFinset v u).mp hu)
    have hLprop : ∀ w ∈ L v, lone v w := fun w hw => (mem_filter.mp hw).2
    have hScard : S.card = 8 := by rw [C.card_neighborFinset_eq_degree, hc8 v hv]
    have hLcard : (L v).card = 3 := hl3 v hv
    let B1u (u : Fin 57) := B.filter (lone u)
    have hB1u_eq : ∀ u ∈ S, B1u u = X.filter (lone u) := by
      intro u hu
      ext x
      simp only [B1u, B, mem_filter, mem_sdiff]
      constructor
      · rintro ⟨⟨hxX, _⟩, hux⟩; exact ⟨hxX, hux⟩
      · rintro ⟨hxX, hux⟩
        refine ⟨⟨hxX, fun hxA => ?_⟩, hux⟩
        rw [hA v] at hxA
        obtain ⟨z, hzx, hzu⟩ := (mem_filter.mp hxA).2.2 u hu hux.1.symm
        exact hux.2 ⟨z, hzu, hzx⟩
    have hB1u_card : ∀ u ∈ S, (B1u u).card = 3 := by
      intro u hu
      rw [hB1u_eq u hu, hXeq v hv u hu]
      exact hl3 u (hS_sub_Vc v hv u hu)
    have hB1_dis : (S : Set (Fin 57)).PairwiseDisjoint B1u := by
      intro u1 hu1 u2 hu2 hne
      refine disjoint_left.mpr fun x hx1 hx2 => hne ?_
      have hxB : x ∈ B := (mem_filter.mp hx1).1
      have h1 : lone x u1 := (hlone_symm u1 x).mp (mem_filter.mp hx1).2
      have h2 : lone x u2 := (hlone_symm u2 x).mp (mem_filter.mp hx2).2
      have hpair_sub : ({u1, u2} : Finset (Fin 57)) ⊆ S.filter (lone x) := by
        intro z hz; simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_filter.mpr ⟨hu1, h1⟩
        · exact mem_filter.mpr ⟨hu2, h2⟩
      have hge2 : 2 ≤ (S.filter (lone x)).card := by
        have := card_le_card hpair_sub; rwa [card_pair hne] at this
      have hge2' : 2 ≤ (S.filter (G.Adj x)).card :=
        hge2.trans (card_le_card fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩)
      have heq2 := hBeq v hv x hxB
      dsimp only [S, lone] at hge2 hge2'
      omega
    have hB1u_noS : ∀ u ∈ S, ∀ x ∈ B1u u, ∀ a ∈ S.erase u, ¬ G.Adj x a := by
      intro u hu x hx a ha hxa
      have hxB : x ∈ B := (mem_filter.mp hx).1
      have hux : lone x u := (hlone_symm u x).mp (mem_filter.mp hx).2
      have hau : a ≠ u := (mem_erase.mp ha).1
      have haS : a ∈ S := erase_subset u S ha
      have h1 : 1 ≤ (S.filter (lone x)).card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hux⟩⟩
      have h2 : 2 ≤ (S.filter (G.Adj x)).card := by
        have hsub : ({a, u} : Finset (Fin 57)) ⊆ S.filter (G.Adj x) := by
          intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact mem_filter.mpr ⟨haS, hxa⟩
          · exact mem_filter.mpr ⟨hu, hux.1⟩
        have := card_le_card hsub; rwa [card_pair hau] at this
      have heq2 := hBeq v hv x hxB
      dsimp only [S, lone] at h1 h2
      omega
    have hB1u_hit : ∀ u ∈ S, 2 ≤ ((B1u u).filter fun x => ∃ w ∈ L v, lone w x).card := by
      intro u hu
      let good := (B1u u).filter fun x => ∃ w ∈ L v, lone w x
      let bad := (B1u u).filter fun x => ¬ ∃ w ∈ L v, lone w x
      have hsum : good.card + bad.card = (B1u u).card :=
        card_filter_add_card_filter_not (s := B1u u) (p := fun x => ∃ w ∈ L v, lone w x)
      have hbad_le1 : bad.card ≤ 1 := by
        refine Bstar_core_card_le_one G hG hno12 v S (L v) hSsub hLprop (hdisSL v hv) (by omega) u hu bad ?_ ?_ ?_ ?_
        · refine disjoint_union_left.mpr ⟨disjoint_left.mpr fun y hyS hyb =>
              (mem_compl.mp (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hyb).1).1).1) (mem_insert_of_mem hyS),
            disjoint_left.mpr fun y hyL hyb =>
              (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hyb).1).1).2 (hLA v hv hyL)⟩
        · exact fun x hx => (mem_filter.mp (mem_filter.mp hx).1).2
        · exact fun x hx => hB1u_noS u hu x (mem_filter.mp hx).1
        · intro x hx w hw hxw
          by_contra hno
          exact (mem_filter.mp hx).2 ⟨w, hw, hxw.symm, fun ⟨z, hz1, hz2⟩ => hno ⟨z, hz2, hz1⟩⟩
      have h3 := hB1u_card u hu
      dsimp only [good] at hsum
      omega
    let B1all := S.biUnion B1u
    have hB1all_sum : 16 ≤ ∑ x ∈ B1all, ((L v).filter (fun w => lone w x)).card := by
      rw [sum_biUnion hB1_dis]
      calc 16 = ∑ _u ∈ S, 2 := by simp [hScard]
        _ ≤ ∑ u ∈ S, ((B1u u).filter fun x => ∃ w ∈ L v, lone w x).card := sum_le_sum hB1u_hit
        _ ≤ ∑ u ∈ S, ∑ x ∈ B1u u, ((L v).filter (fun w => lone w x)).card := by
          refine sum_le_sum fun u _ => ?_
          rw [card_filter]
          refine sum_le_sum fun x _ => ?_
          split_ifs with h
          · obtain ⟨w, hw, hwx⟩ := h
            exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hw, hwx⟩⟩
          · exact Nat.zero_le _
    -- AT sum >= 7
    have hATcard : 5 ≤ AT.card := by
      have hA8 : 8 ≤ (A v).card := by have := hAeq v hv; omega
      have hsplit : AT.card + (L v).card = (A v).card := card_sdiff_add_card_eq_card (hLA v hv)
      omega
    have hdisSA : Disjoint S (A v) := disjoint_left.mpr fun u hu hAv => by
      rw [hA v] at hAv; exact (mem_compl.mp (mem_filter.mp hAv).1) (mem_insert_of_mem hu)
    have hATpos : ∀ x ∈ AT, 1 ≤ ((L v).filter (fun w => lone w x)).card := by
      intro x hx
      have hxA := (mem_sdiff.mp hx).1
      have hxL := (mem_sdiff.mp hx).2
      have hxS := disjoint_right.mp hdisSA hxA
      rw [hA v] at hxA
      obtain ⟨w, hwL, hwx⟩ := AT_has_lone_to_L G hG hno12 v S (L v) hSsub hLprop (hdisSL v hv) (by omega)
        x hxS hxL (mem_filter.mp hxA).2
      exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hwL, hwx⟩⟩
    let AT1 := AT.filter (fun x => ((L v).filter (fun w => lone w x)).card = 1)
    have hAT1_le3 : AT1.card ≤ 3 := by
      have h1 : AT1.card = ∑ w ∈ L v, (AT1.filter (fun x => lone w x)).card := by
        have hstep : AT1.card = ∑ x ∈ AT1, ((L v).filter (fun w => lone w x)).card := by
          trans ∑ _x ∈ AT1, 1
          · simp
          · exact sum_congr rfl fun x hx => ((mem_filter.mp hx).2).symm
        rw [hstep]; simp_rw [card_filter]; rw [sum_comm]
      rw [h1]
      calc ∑ w ∈ L v, (AT1.filter (fun x => lone w x)).card
        _ ≤ ∑ _w ∈ L v, 1 := sum_le_sum fun w hwL => by
            refine Bstar_card_le_one G hG hno12 v S (L v) hSsub hLprop (hdisSL v hv) (by omega)
              w hwL (AT1.filter (fun x => lone w x)) ?_ ?_ ?_ ?_
            · refine disjoint_union_left.mpr ⟨hdisSA.mono_right (((filter_subset _ _).trans (filter_subset _ _)).trans sdiff_subset),
                disjoint_left.mpr fun y hyL hyB => (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hyB).1).1).2 hyL⟩
            · exact fun x hx => (mem_filter.mp hx).2
            · intro x hx
              have hxA := (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
              rw [hA v] at hxA; exact (mem_filter.mp hxA).2
            · intro x hx w' hw' hxw'
              by_contra hno
              have hlw' : lone w' x := ⟨hxw'.symm, fun ⟨z, hz1, hz2⟩ => hno ⟨z, hz2, hz1⟩⟩
              have hlw : lone w x := (mem_filter.mp hx).2
              have hdeg1 : ((L v).filter (fun w => lone w x)).card = 1 := (mem_filter.mp (mem_filter.mp hx).1).2
              exact (mem_erase.mp hw').1 (card_le_one_iff.mp hdeg1.le
                (mem_filter.mpr ⟨erase_subset w (L v) hw', hlw'⟩) (mem_filter.mpr ⟨hwL, hlw⟩))
        _ = 3 := by simp [hLcard]
    have hATsum : 7 ≤ ∑ x ∈ AT, ((L v).filter (fun w => lone w x)).card := by
      have hpt : ∀ x ∈ AT, 2 ≤ ((L v).filter (fun w => lone w x)).card +
          (if ((L v).filter (fun w => lone w x)).card = 1 then 1 else 0) := fun x hx => by
        have := hATpos x hx; split_ifs <;> omega
      have htot := sum_le_sum hpt
      rw [sum_add_distrib, sum_const, smul_eq_mul, mul_comm, ← sum_filter] at htot
      have hAT1eq : (∑ _x ∈ AT1, (1 : ℕ)) = AT1.card := by simp
      change 2 * AT.card ≤ (∑ x ∈ AT, ((L v).filter (fun w => lone w x)).card) + ∑ _x ∈ AT1, 1 at htot
      rw [hAT1eq] at htot
      omega
    -- Combine disjoint sets {v}, B1all, AT
    have hdis_v_B1 : v ∉ B1all := fun hvB => by
      obtain ⟨u, _, hxu⟩ := mem_biUnion.mp hvB
      exact (mem_compl.mp (mem_sdiff.mp (mem_filter.mp hxu).1).1) (mem_insert_self v S)
    have hdis_v_AT : v ∉ AT := fun hvA => by
      have h1 := (mem_sdiff.mp hvA).1; rw [hA v] at h1
      exact (mem_compl.mp (mem_filter.mp h1).1) (mem_insert_self v S)
    have hdis_B1_AT : Disjoint B1all AT := disjoint_left.mpr fun x hxB hxAT => by
      obtain ⟨u, _, hxu⟩ := mem_biUnion.mp hxB
      exact (mem_sdiff.mp (mem_filter.mp hxu).1).2 (mem_sdiff.mp hxAT).1
    have hsum_ge26 : 26 ≤ ∑ w ∈ L v, (L w).card := by
      let U3 := insert v (B1all ∪ AT)
      have h1 : (∑ x ∈ U3, ((L v).filter (fun w => lone w x)).card) ≤ ∑ w ∈ L v, (L w).card := by
        simp_rw [card_filter]
        rw [sum_comm]
        refine sum_le_sum fun w _ => ?_
        rw [← card_filter]
        exact card_le_card (filter_subset_filter _ (subset_univ U3))
      have h2 : (∑ x ∈ U3, ((L v).filter (fun w => lone w x)).card) =
          ((L v).filter (fun w => lone w v)).card +
          (∑ x ∈ B1all, ((L v).filter (fun w => lone w x)).card) +
          (∑ x ∈ AT, ((L v).filter (fun w => lone w x)).card) := by
        dsimp only [U3]
        rw [sum_insert (by simp [hdis_v_B1, hdis_v_AT]), sum_union hdis_B1_AT, add_assoc]
      have hv3 : ((L v).filter (fun w => lone w v)).card = 3 := by
        rw [filter_true_of_mem (fun w hw => (hlone_symm v w).mp (mem_filter.mp hw).2), hLcard]
      omega
    have hsum_le25 : (∑ w ∈ L v, (L w).card) ≤ 25 := by
      rw [← sum_erase_add _ _ hw0]
      have h0 : (L w0).card = 3 := hl3 w0 hw0Vc
      have hrest : (∑ w ∈ (L v).erase w0, (L w).card) ≤ 22 := by
        calc ∑ w ∈ (L v).erase w0, (L w).card
          _ ≤ ∑ _w ∈ (L v).erase w0, 11 := sum_le_sum fun w _ => by
              have hsub : L w ⊆ G.neighborFinset w := fun z hz =>
                (G.mem_neighborFinset w z).mpr (mem_filter.mp hz).2.1
              have hle := card_le_card hsub
              rw [G.card_neighborFinset_eq_degree] at hle
              exact hle.trans (hdeg11 w)
          _ = 22 := by rw [sum_const, smul_eq_mul, card_erase_of_mem hw0, hLcard]
      omega
    omega
  -- Step 2: Bounds on m = Vc.card -> m = 27 or m = 28
  let O := Vcᶜ
  have hmO : Vc.card + O.card = 57 := by
    change Vc.card + Vcᶜ.card = 57
    rw [add_comm, card_compl_add_card, Fintype.card_fin]
  have hAdj_O_lone : ∀ v ∈ Vc, ∀ x ∈ O, G.Adj v x ↔ lone v x := by
    intro v hv x hx
    constructor
    · intro h
      rcases (hAdj_iff v hv x).mp h with hC | hl
      · exact ((mem_compl.mp hx) (hS_sub_Vc v hv x ((C.mem_neighborFinset v x).mpr hC))).elim
      · exact hl
    · exact fun hl => hl.1
  -- For any v in Vc, (A v cap O).card = O.card - 24 and 25 <= Vc.card <= 30
  have hAO_card : ∀ v ∈ Vc, (A v ∩ O).card + 24 = O.card ∧
      (∑ u ∈ C.neighborFinset v, ((A v ∩ O).filter (G.Adj u)).card) = 0 := by
    intro v hv
    let S := C.neighborFinset v
    let X := (insert v S)ᶜ
    let B := X \ A v
    let B1u (u : Fin 57) := B.filter (lone u)
    have hB1u_eq : ∀ u ∈ S, B1u u = X.filter (lone u) := by
      intro u hu; ext x; simp only [B1u, B, mem_filter, mem_sdiff]
      constructor
      · rintro ⟨⟨hxX, _⟩, hux⟩; exact ⟨hxX, hux⟩
      · rintro ⟨hxX, hux⟩
        refine ⟨⟨hxX, fun hxA => ?_⟩, hux⟩
        rw [hA v] at hxA
        obtain ⟨z, hzx, hzu⟩ := (mem_filter.mp hxA).2.2 u hu hux.1.symm
        exact hux.2 ⟨z, hzu, hzx⟩
    have hB1_dis : (S : Set (Fin 57)).PairwiseDisjoint B1u := by
      intro u1 hu1 u2 hu2 hne
      refine disjoint_left.mpr fun x hx1 hx2 => hne ?_
      have hxB := (mem_filter.mp hx1).1
      have h1 : lone x u1 := (hlone_symm u1 x).mp (mem_filter.mp hx1).2
      have h2 : lone x u2 := (hlone_symm u2 x).mp (mem_filter.mp hx2).2
      have hge2 : 2 ≤ (S.filter (lone x)).card := by
        have hsub : ({u1, u2} : Finset (Fin 57)) ⊆ S.filter (lone x) := by
          intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact mem_filter.mpr ⟨hu1, h1⟩
          · exact mem_filter.mpr ⟨hu2, h2⟩
        have := card_le_card hsub; rwa [card_pair hne] at this
      have hge2' : 2 ≤ (S.filter (G.Adj x)).card :=
        hge2.trans (card_le_card fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩)
      have heq2 := hBeq v hv x hxB
      dsimp only [S, lone] at hge2 hge2'
      omega
    have hB1all_card : (S.biUnion B1u).card = 24 := by
      rw [card_biUnion hB1_dis]
      have hpt : ∀ u ∈ S, (B1u u).card = 3 := fun u hu => by
        rw [hB1u_eq u hu, hXeq v hv u hu]; exact hl3 u (hS_sub_Vc v hv u hu)
      rw [sum_congr rfl hpt, sum_const, smul_eq_mul, C.card_neighborFinset_eq_degree, hc8 v hv]
    have hB1_eq_BO : S.biUnion B1u = B ∩ O := by
      ext x
      simp only [mem_biUnion, mem_inter, B1u, mem_filter]
      constructor
      · rintro ⟨u, hu, hxB, hux⟩
        exact ⟨hxB, mem_compl.mpr (hL_not_Vc u (hS_sub_Vc v hv u hu) x (mem_filter.mpr ⟨mem_univ _, hux⟩))⟩
      · rintro ⟨hxB, hxO⟩
        have hge2 := hBeq v hv x hxB
        have hpos : 0 < (S.filter (G.Adj x)).card := by
          by_contra! h0
          have h0' : (S.filter (lone x)).card = 0 := by
            have := card_le_card (show S.filter (lone x) ⊆ S.filter (G.Adj x) from
              fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩)
            omega
          dsimp only [S, lone] at h0 h0'
          omega
        obtain ⟨u, hu⟩ := card_pos.mp hpos
        obtain ⟨huS, hxu⟩ := mem_filter.mp hu
        exact ⟨u, huS, hxB, (hAdj_O_lone u (hS_sub_Vc v hv u huS) x hxO).mp hxu.symm⟩
    have hO_sub_X : O ⊆ X := by
      intro x hx
      refine mem_compl.mpr fun hmem => ?_
      rcases mem_insert.mp hmem with rfl | hS
      · exact (mem_compl.mp hx) hv
      · exact (mem_compl.mp hx) (hS_sub_Vc v hv x hS)
    have hO_part : (A v ∩ O).card + (B ∩ O).card = O.card := by
      have hdis : Disjoint (A v ∩ O) (B ∩ O) := disjoint_left.mpr fun x h1 h2 =>
        (mem_sdiff.mp (mem_inter.mp h2).1).2 (mem_inter.mp h1).1
      rw [← card_union_of_disjoint hdis]
      congr 1; ext x; simp only [B, mem_union, mem_inter, mem_sdiff]
      constructor
      · rintro (⟨_, hxO⟩ | ⟨_, hxO⟩) <;> exact hxO
      · intro hxO
        by_cases hxA : x ∈ A v
        · exact Or.inl ⟨hxA, hxO⟩
        · exact Or.inr ⟨⟨hO_sub_X hxO, hxA⟩, hxO⟩
    constructor
    · rw [← hB1all_card, hB1_eq_BO]; exact hO_part
    · refine sum_eq_zero fun u hu => card_eq_zero.mpr (filter_eq_empty_iff.mpr fun x hx hux => ?_)
      obtain ⟨hxA, hxO⟩ := mem_inter.mp hx
      have hlu := (hAdj_O_lone u (hS_sub_Vc v hv u hu) x hxO).mp hux
      rw [hA v] at hxA
      obtain ⟨z, hzx, hzu⟩ := (mem_filter.mp hxA).2.2 u hu hux.symm
      exact hlu.2 ⟨z, hzu, hzx⟩
  -- Extract 25 <= Vc.card <= 30
  have hm_bounds : 25 ≤ Vc.card ∧ Vc.card ≤ 30 := by
    obtain ⟨v0, hv0⟩ := hVcne
    have hAO := hAO_card v0 hv0
    have hL_sub_AO : L v0 ⊆ A v0 ∩ O := fun w hw =>
      mem_inter.mpr ⟨hLA v0 hv0 hw, mem_compl.mpr (hL_not_Vc v0 hv0 w hw)⟩
    have hAO_ge3 : 3 ≤ (A v0 ∩ O).card := by
      have := card_le_card hL_sub_AO; rwa [hl3 v0 hv0] at this
    have hle30 : Vc.card ≤ 30 := by omega
    have hS0 : ∀ u ∈ C.neighborFinset v0, G.Adj v0 u := fun u hu => hCG ((C.mem_neighborFinset v0 u).mp hu)
    have hdis0 : Disjoint (C.neighborFinset v0) (A v0) := disjoint_left.mpr fun u hu hAv => by
      rw [hA v0] at hAv; exact (mem_compl.mp (mem_filter.mp hAv).1) (mem_insert_of_mem hu)
    have hU83 := U_eight_three_props G hG hno12 v0 (C.neighborFinset v0) (L v0) (A v0)
      hS0 (fun w hw => (mem_filter.mp hw).2) (hdisSL v0 hv0)
      (by rw [C.card_neighborFinset_eq_degree, hc8 v0 hv0]) (hl3 v0 hv0)
      (hLA v0 hv0) hdis0 (fun x hx => by rw [hA v0] at hx; exact (mem_filter.mp hx).2)
    have hAsplit : (A v0).card = (A v0 ∩ O).card + (A v0 ∩ Vc).card := by
      have hdis : Disjoint (A v0 ∩ O) (A v0 ∩ Vc) := disjoint_left.mpr fun x h1 h2 =>
        (mem_compl.mp (mem_inter.mp h1).2) (mem_inter.mp h2).2
      rw [← card_union_of_disjoint hdis]
      congr 1; ext x; simp only [O, mem_union, mem_inter, mem_compl]
      tauto
    have heq0 := hAeq v0 hv0
    have hge25 : 25 ≤ Vc.card := by
      by_cases hA9 : (A v0).card = 9
      · have hE2 : (∑ u ∈ C.neighborFinset v0, ((A v0).filter (G.Adj u)).card) = 2 := by omega
        have hex : ∃ u ∈ C.neighborFinset v0, 0 < ((A v0).filter (G.Adj u)).card := by
          by_contra! h0
          have : (∑ u ∈ C.neighborFinset v0, ((A v0).filter (G.Adj u)).card) = 0 :=
            sum_eq_zero fun u hu => Nat.eq_zero_of_le_zero (h0 u hu)
          omega
        obtain ⟨u, hu, hpos⟩ := hex
        obtain ⟨x, hx⟩ := card_pos.mp hpos
        obtain ⟨hxA, hux⟩ := mem_filter.mp hx
        have hxVc : x ∈ Vc := by
          by_contra hxO
          have hlu := (hAdj_O_lone u (hS_sub_Vc v0 hv0 u hu) x (mem_compl.mpr hxO)).mp hux
          rw [hA v0] at hxA
          obtain ⟨z, hzx, hzu⟩ := (mem_filter.mp hxA).2.2 u hu hux.symm
          exact hlu.2 ⟨z, hzu, hzx⟩
        have hposAVc : 1 ≤ (A v0 ∩ Vc).card := card_pos.mpr ⟨x, mem_inter.mpr ⟨hxA, hxVc⟩⟩
        omega
      · omega
    exact ⟨hge25, hle30⟩
  -- Step 3: For every x in O, Lc x = Vc.filter (lone x) has 9 * |Lc x| <= m
  let Lc (x : Fin 57) : Finset (Fin 57) := Vc.filter (lone x)
  have hLc_disj_N : ∀ x ∈ O, ∀ u1 ∈ Lc x, ∀ u2 ∈ Lc x, u1 ≠ u2 →
      Disjoint (C.neighborFinset u1) (C.neighborFinset u2) := by
    intro x hxO u1 hu1 u2 hu2 hne
    refine disjoint_left.mpr fun v hv1 hv2 => ?_
    have hvVc : v ∈ Vc := hS_sub_Vc u1 (mem_filter.mp hu1).1 v hv1
    have hu1S : u1 ∈ C.neighborFinset v := (C.mem_neighborFinset v u1).mpr ((C.mem_neighborFinset u1 v).mp hv1).symm
    have hu2S : u2 ∈ C.neighborFinset v := (C.mem_neighborFinset v u2).mpr ((C.mem_neighborFinset u2 v).mp hv2).symm
    have hxB : x ∈ (insert v (C.neighborFinset v))ᶜ \ A v := by
      refine mem_sdiff.mpr ⟨mem_compl.mpr ?_, fun hxA => ?_⟩
      · intro hmem
        rcases mem_insert.mp hmem with rfl | hS
        · exact (mem_compl.mp hxO) hvVc
        · exact (mem_compl.mp hxO) (hS_sub_Vc v hvVc x hS)
      · rw [hA v] at hxA
        have hl1 := (mem_filter.mp hu1).2
        obtain ⟨z, hzx, hzu⟩ := (mem_filter.mp hxA).2.2 u1 hu1S hl1.1
        exact hl1.2 ⟨z, hzx, hzu⟩
    have hge2 : 2 ≤ ((C.neighborFinset v).filter (lone x)).card := by
      have hsub : ({u1, u2} : Finset (Fin 57)) ⊆ (C.neighborFinset v).filter (lone x) := by
        intro z hz; simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_filter.mpr ⟨hu1S, (mem_filter.mp hu1).2⟩
        · exact mem_filter.mpr ⟨hu2S, (mem_filter.mp hu2).2⟩
      have := card_le_card hsub; rwa [card_pair hne] at this
    have hge2' : 2 ≤ ((C.neighborFinset v).filter (G.Adj x)).card :=
      hge2.trans (card_le_card fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩)
    have heq2 := hBeq v hvVc x hxB
    dsimp only [lone] at hge2
    omega
  have h9k_le_m : ∀ x ∈ O, 9 * (Lc x).card ≤ Vc.card := by
    intro x hxO
    have hdis_all : Disjoint (Lc x) ((Lc x).biUnion (fun u => C.neighborFinset u)) := by
      refine disjoint_left.mpr fun u hu hbi => ?_
      obtain ⟨w, hw, huw⟩ := mem_biUnion.mp hbi
      have hlu := (mem_filter.mp hu).2
      have hlw := (mem_filter.mp hw).2
      have hCwu := (C.mem_neighborFinset w u).mp huw
      exact hlu.2 ⟨w, hlw.1.symm, hCG hCwu⟩
    have hsub : Lc x ∪ (Lc x).biUnion (fun u => C.neighborFinset u) ⊆ Vc := union_subset (filter_subset _ _)
      (biUnion_subset.mpr fun u hu => fun z hz => hS_sub_Vc u (mem_filter.mp hu).1 z hz)
    have hle := card_le_card hsub
    rw [card_union_of_disjoint hdis_all,
      card_biUnion (fun u1 hu1 u2 hu2 hne => hLc_disj_N x hxO u1 hu1 u2 hu2 hne)] at hle
    have hsum8 : (∑ u ∈ Lc x, (C.neighborFinset u).card) = 8 * (Lc x).card := by
      have hpt : ∀ u ∈ Lc x, (C.neighborFinset u).card = 8 := fun u hu => by
        rw [C.card_neighborFinset_eq_degree, hc8 u (mem_filter.mp hu).1]
      rw [sum_congr rfl hpt, sum_const, smul_eq_mul, mul_comm]
    omega
  -- Double count lone edges between Vc and O
  have hsum_Lc : (∑ x ∈ O, (Lc x).card) = 3 * Vc.card := by
    have h1 : (∑ x ∈ O, (Lc x).card) = ∑ v ∈ Vc, (O.filter (lone v)).card := by
      simp_rw [Lc, card_filter]; rw [sum_comm]
      exact sum_congr rfl fun v _ => sum_congr rfl fun x _ => if_congr (hlone_symm x v) rfl rfl
    rw [h1]
    have hpt : ∀ v ∈ Vc, (O.filter (lone v)).card = 3 := by
      intro v hv
      have heq : O.filter (lone v) = L v := by
        ext x; simp only [O, L, mem_filter, mem_univ, true_and, mem_compl]
        exact ⟨And.right, fun h => ⟨hL_not_Vc v hv x (mem_filter.mpr ⟨mem_univ _, h⟩), h⟩⟩
      rw [heq]; exact hl3 v hv
    rw [sum_congr rfl hpt, sum_const, smul_eq_mul, mul_comm]
  have hm_27_28 : Vc.card = 27 ∨ Vc.card = 28 := by
    by_cases h26 : Vc.card ≤ 26
    · have hle2 : ∀ x ∈ O, (Lc x).card ≤ 2 := fun x hx => by have := h9k_le_m x hx; omega
      have hsum_le : (∑ x ∈ O, (Lc x).card) ≤ 2 * O.card := by
        calc ∑ x ∈ O, (Lc x).card ≤ ∑ _x ∈ O, 2 := sum_le_sum hle2
          _ = 2 * O.card := by simp [mul_comm]
      omega
    · by_cases h29 : 29 ≤ Vc.card
      · have hle3 : ∀ x ∈ O, (Lc x).card ≤ 3 := fun x hx => by have := h9k_le_m x hx; omega
        have hsum_le : (∑ x ∈ O, (Lc x).card) ≤ 3 * O.card := by
          calc ∑ x ∈ O, (Lc x).card ≤ ∑ _x ∈ O, 3 := sum_le_sum hle3
            _ = 3 * O.card := by simp [mul_comm]
        omega
      · omega
  -- Step 4: Find v in Vc with all 3 lone neighbors w in L v having (Lc w).card = 3
  have hLc_le3 : ∀ x ∈ O, (Lc x).card ≤ 3 := fun x hx => by have := h9k_le_m x hx; omega
  have hex_good_v : ∃ v ∈ Vc, ∀ w ∈ L v, (Lc w).card = 3 := by
    let BadV := Vc.filter (fun v => ∃ w ∈ L v, (Lc w).card ≤ 2)
    have hBad_le : BadV.card ≤ 6 * (57 - 2 * Vc.card) := by
      have h1 : BadV.card ≤ ∑ v ∈ Vc, ((L v).filter (fun w => (Lc w).card ≤ 2)).card := by
        calc BadV.card = ∑ _v ∈ BadV, 1 := by simp
          _ ≤ ∑ v ∈ BadV, ((L v).filter (fun w => (Lc w).card ≤ 2)).card := sum_le_sum fun v hv => by
              obtain ⟨w, hwL, hwk⟩ := (mem_filter.mp hv).2
              exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hwL, hwk⟩⟩
          _ ≤ ∑ v ∈ Vc, ((L v).filter (fun w => (Lc w).card ≤ 2)).card :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      have h2 : (∑ v ∈ Vc, ((L v).filter (fun w => (Lc w).card ≤ 2)).card) =
          ∑ w ∈ O.filter (fun x => (Lc x).card ≤ 2), (Lc w).card := by
        have hL_eq : ∀ v ∈ Vc, ((L v).filter (fun w => (Lc w).card ≤ 2)).card =
            ((O.filter (fun x => (Lc x).card ≤ 2)).filter (lone v)).card := by
          intro v hv; congr 1; ext w
          simp only [L, O, mem_filter, mem_univ, true_and, mem_compl]
          constructor
          · rintro ⟨hvw, hwk⟩; exact ⟨⟨hL_not_Vc v hv w (mem_filter.mpr ⟨mem_univ _, hvw⟩), hwk⟩, hvw⟩
          · rintro ⟨⟨_, hwk⟩, hvw⟩; exact ⟨hvw, hwk⟩
        rw [sum_congr rfl hL_eq]
        simp_rw [Lc, card_filter]; rw [sum_comm]
        exact sum_congr rfl fun w _ => sum_congr rfl fun v _ => if_congr (hlone_symm v w) rfl rfl
      have h3 : (∑ w ∈ O.filter (fun x => (Lc x).card ≤ 2), (Lc w).card) ≤
          ∑ w ∈ O, 2 * (3 - (Lc w).card) := by
        calc ∑ w ∈ O.filter (fun x => (Lc x).card ≤ 2), (Lc w).card
          _ ≤ ∑ w ∈ O.filter (fun x => (Lc x).card ≤ 2), 2 * (3 - (Lc w).card) :=
              sum_le_sum fun w hw => by have := (mem_filter.mp hw).2; omega
          _ ≤ ∑ w ∈ O, 2 * (3 - (Lc w).card) :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      have h4 : (∑ w ∈ O, 2 * (3 - (Lc w).card)) = 6 * (57 - 2 * Vc.card) := by
        rw [← mul_sum]
        have hsub_sum : (∑ w ∈ O, (3 - (Lc w).card)) + (∑ w ∈ O, (Lc w).card) = 3 * O.card := by
          rw [← sum_add_distrib]
          have hpt : ∀ w ∈ O, (3 - (Lc w).card) + (Lc w).card = 3 := fun w hw => by
            have := hLc_le3 w hw; omega
          rw [sum_congr rfl hpt, sum_const, smul_eq_mul, mul_comm]
        omega
      omega
    have hlt : BadV.card < Vc.card := by omega
    have hne : (Vc \ BadV).Nonempty := by
      refine card_pos.mp ?_
      have hsub : BadV ⊆ Vc := filter_subset _ _
      rw [card_sdiff_of_subset hsub]
      exact Nat.sub_pos_of_lt hlt
    obtain ⟨v, hv⟩ := hne
    obtain ⟨hvVc, hvnot⟩ := mem_sdiff.mp hv
    refine ⟨v, hvVc, fun w hw => ?_⟩
    have hwO : w ∈ O := mem_compl.mpr (hL_not_Vc v hvVc w hw)
    have hle := hLc_le3 w hwO
    by_contra hne3
    exact hvnot (mem_filter.mpr ⟨hvVc, w, hw, by omega⟩)
  -- Step 5: Analyze the chosen v in Vc with all 3 lone neighbors of degree 3 into Vc
  obtain ⟨v, hvVc, hv3⟩ := hex_good_v
  let S := C.neighborFinset v
  have hSsub : ∀ u ∈ S, G.Adj v u := fun u hu => hCG ((C.mem_neighborFinset v u).mp hu)
  have hScard : S.card = 8 := by rw [C.card_neighborFinset_eq_degree, hc8 v hvVc]
  have hLcard : (L v).card = 3 := hl3 v hvVc
  let Z := (A v).filter (fun x => (S.filter (G.Adj x)).card = 0)
  let U := Z ∩ Vc
  let Y := (A v ∩ O) \ L v
  have hZ_noS : ∀ x ∈ Z, ∀ u ∈ S, ¬ G.Adj x u := fun x hx u hu hxu => by
    have h0 := (mem_filter.mp hx).2
    have hpos : 0 < (S.filter (G.Adj x)).card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hxu⟩⟩
    omega
  have hZ_disS : Disjoint S Z := disjoint_left.mpr fun u hu hZ => by
    have hxA := (mem_filter.mp hZ).1; rw [hA v] at hxA
    exact (mem_compl.mp (mem_filter.mp hxA).1) (mem_insert_of_mem hu)
  have hAO := hAO_card v hvVc
  have hAO_sub_Z : A v ∩ O ⊆ Z := by
    intro x hx
    refine mem_filter.mpr ⟨(mem_inter.mp hx).1, card_eq_zero.mpr (filter_eq_empty_iff.mpr fun u hu hxu => ?_)⟩
    have h0 : ((A v ∩ O).filter (G.Adj u)).card = 0 := by
      have := hAO.2; exact (sum_eq_zero_iff.mp this) u hu
    have hpos : 0 < ((A v ∩ O).filter (G.Adj u)).card := card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, hxu.symm⟩⟩
    omega
  have hY_sub_Z : Y ⊆ Z := sdiff_subset.trans hAO_sub_Z
  have hL_sub_AO : L v ⊆ A v ∩ O := fun w hw =>
    mem_inter.mpr ⟨hLA v hvVc hw, mem_compl.mpr (hL_not_Vc v hvVc w hw)⟩
  have hL_sub_Z : L v ⊆ Z := hL_sub_AO.trans hAO_sub_Z
  have hYcard : Y.card = 30 - Vc.card := by
    have hsplit : Y.card + (L v).card = (A v ∩ O).card := card_sdiff_add_card_eq_card hL_sub_AO
    have := hAO.1
    omega
  have hU83 := U_eight_three_props G hG hno12 v S (L v) (A v)
    hSsub (fun w hw => (mem_filter.mp hw).2) (hdisSL v hvVc) hScard hLcard
    (hLA v hvVc) (disjoint_left.mpr fun u hu hAv => by rw [hA v] at hAv; exact (mem_compl.mp (mem_filter.mp hAv).1) (mem_insert_of_mem hu))
    (fun x hx => by rw [hA v] at hx; exact (mem_filter.mp hx).2)
  have hAsplit : (A v).card = (A v ∩ O).card + (A v ∩ Vc).card := by
    have hdis : Disjoint (A v ∩ O) (A v ∩ Vc) := disjoint_left.mpr fun x h1 h2 =>
      (mem_compl.mp (mem_inter.mp h1).2) (mem_inter.mp h2).2
    rw [← card_union_of_disjoint hdis]
    congr 1; ext x; simp only [O, mem_union, mem_inter, mem_compl]; tauto
  have hU_le : U.card ≤ Vc.card - 25 := by
    have hUsub : U ⊆ A v ∩ Vc := fun x hx => mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hx).1).1, (mem_inter.mp hx).2⟩
    have hAO1 := hAO.1
    by_cases hA9 : (A v).card = 9
    · have hE2 : (∑ u ∈ S, ((A v).filter (G.Adj u)).card) = 2 := by
        have := hAeq v hvVc
        dsimp only [S]
        omega
      have hex : ∃ u ∈ S, 0 < ((A v).filter (G.Adj u)).card := by
        by_contra! h0
        have : (∑ u ∈ S, ((A v).filter (G.Adj u)).card) = 0 :=
          sum_eq_zero fun u hu => Nat.eq_zero_of_le_zero (h0 u hu)
        omega
      obtain ⟨u, hu, hpos⟩ := hex
      obtain ⟨x, hx⟩ := card_pos.mp hpos
      obtain ⟨hxA, hux⟩ := mem_filter.mp hx
      have hxVc : x ∈ Vc := by
        by_contra hxO
        have hlu := (hAdj_O_lone u (hS_sub_Vc v hvVc u hu) x (mem_compl.mpr hxO)).mp hux
        rw [hA v] at hxA
        obtain ⟨z, hzx, hzu⟩ := (mem_filter.mp hxA).2.2 u hu hux.symm
        exact hlu.2 ⟨z, hzu, hzx⟩
      have hxnotU : x ∉ U := fun hxU => hZ_noS x (mem_inter.mp hxU).1 u hu hux.symm
      have hssub : U ⊂ A v ∩ Vc := Finset.ssubset_iff_subset_ne.mpr ⟨hUsub, fun heq => hxnotU (heq ▸ mem_inter.mpr ⟨hxA, hxVc⟩)⟩
      have hlt := card_lt_card hssub
      omega
    · have hle := card_le_card hUsub
      omega
  -- For every w in L v, (Lc w).erase v subset U
  have hLc_sub_U : ∀ w ∈ L v, (Lc w).erase v ⊆ U := by
    intro w hw u hu
    obtain ⟨huv, huLc⟩ := mem_erase.mp hu
    obtain ⟨huVc, hwu⟩ := mem_filter.mp huLc
    have hwO : w ∈ O := mem_compl.mpr (hL_not_Vc v hvVc w hw)
    have hvLc : v ∈ Lc w := mem_filter.mpr ⟨hvVc, (hlone_symm v w).mp (mem_filter.mp hw).2⟩
    have hdisN := hLc_disj_N w hwO u huLc v hvLc huv
    have hu_not_S : u ∉ S := fun huS => (mem_filter.mp hvLc).2.2 ⟨u, hwu.1.symm, (hCG ((C.mem_neighborFinset v u).mp huS)).symm⟩
    have hu_noS : ∀ a ∈ S, ¬ G.Adj u a := by
      intro a ha hua
      rcases (hAdj_iff u huVc a).mp hua with hC | hl
      · exact disjoint_left.mp hdisN ((C.mem_neighborFinset u a).mpr hC) ha
      · exact hL_not_Vc u huVc a (mem_filter.mpr ⟨mem_univ _, hl⟩) (hS_sub_Vc v hvVc a ha)
    refine mem_inter.mpr ⟨mem_filter.mpr ⟨?_, card_eq_zero.mpr (filter_eq_empty_iff.mpr hu_noS)⟩, huVc⟩
    rw [hA v]
    refine mem_filter.mpr ⟨mem_compl.mpr (fun h => (mem_insert.mp h).elim huv hu_not_S), ?_, ?_⟩
    · intro a ha _ _ _ _; exact (hu_noS a ha.1 ha.2).elim
    · intro a ha hua; exact (hu_noS a ha hua).elim
  -- Extract w1, w2, w3 of L v
  obtain ⟨w1, L', hw1L', hLeq1, hL'2⟩ := card_eq_succ.mp hLcard
  obtain ⟨w2, w3, hw23, rfl⟩ := card_eq_two.mp hL'2
  have hw12 : w1 ≠ w2 := fun h => hw1L' (by simp [h])
  have hw13 : w1 ≠ w3 := fun h => hw1L' (by simp [h])
  have hLeq : L v = {w1, w2, w3} := hLeq1.symm
  have hw1L : w1 ∈ L v := by rw [hLeq]; simp
  have hw2L : w2 ∈ L v := by rw [hLeq]; simp
  have hw3L : w3 ∈ L v := by rw [hLeq]; simp
  have hv_mem_Lc : ∀ w ∈ L v, v ∈ Lc w := fun w hw =>
    mem_filter.mpr ⟨hvVc, (hlone_symm v w).mp (mem_filter.mp hw).2⟩
  have hPcard : ∀ w ∈ L v, ((Lc w).erase v).card = 2 := fun w hw => by
    rw [card_erase_of_mem (hv_mem_Lc w hw), hv3 w hw]
  have hU_ge2 : 2 ≤ U.card := by
    have := card_le_card (hLc_sub_U w1 hw1L)
    rwa [hPcard w1 hw1L] at this
  -- Split on U.card = 2 vs U.card = 3
  by_cases hU2 : U.card = 2
  · obtain ⟨u1, u2, hu12, hUeq⟩ := card_eq_two.mp hU2
    have hPeqU : ∀ w ∈ L v, (Lc w).erase v = U := fun w hw =>
      eq_of_subset_of_card_le (hLc_sub_U w hw) (by rw [hPcard w hw, hU2])
    have hu1U : u1 ∈ U := by rw [hUeq]; simp
    have hu2U : u2 ∈ U := by rw [hUeq]; simp
    have hu1_all : ∀ w ∈ L v, lone w u1 := fun w hw => by
      have : u1 ∈ (Lc w).erase v := by rw [hPeqU w hw]; exact hu1U
      exact (mem_filter.mp (mem_erase.mp this).2).2
    have hu2_all : ∀ w ∈ L v, lone w u2 := fun w hw => by
      have : u2 ∈ (Lc w).erase v := by rw [hPeqU w hw]; exact hu2U
      exact (mem_filter.mp (mem_erase.mp this).2).2
    have hu1_AT : u1 ∈ A v \ L v := mem_sdiff.mpr ⟨(mem_filter.mp (mem_inter.mp hu1U).1).1,
      fun h => hL_not_Vc v hvVc u1 h (mem_inter.mp hu1U).2⟩
    have hA_le8 : (A v).card ≤ 8 := hU83.2.2 ⟨u1, hu1_AT, hu1_all⟩
    have hE0 : (∑ u ∈ S, ((A v).filter (G.Adj u)).card) = 0 := by
      have := hAeq v hvVc
      dsimp only [S]
      omega
    have hZeqA : Z = A v := by
      ext x; simp only [Z, mem_filter]
      refine ⟨And.left, fun hx => ⟨hx, card_eq_zero.mpr (filter_eq_empty_iff.mpr fun u hu hxu => ?_)⟩⟩
      have h0 := (sum_eq_zero_iff.mp hE0) u hu
      have hpos : 0 < ((A v).filter (G.Adj u)).card := card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, hxu.symm⟩⟩
      omega
    have hm27 : Vc.card = 27 := by
      have hUeqAVc : U = A v ∩ Vc := by dsimp only [U]; rw [hZeqA]
      rw [← hUeqAVc] at hAsplit
      have hAO1 := hAO.1
      have := hAeq v hvVc
      dsimp only [S] at hE0
      omega
    have hY3 : Y.card = 3 := by omega
    obtain ⟨y1, Y', hy1Y', hYeq1, hY'2⟩ := card_eq_succ.mp hY3
    obtain ⟨y2, y3, hy23, rfl⟩ := card_eq_two.mp hY'2
    have hy12 : y1 ≠ y2 := fun h => hy1Y' (by simp [h])
    have hy13 : y1 ≠ y3 := fun h => hy1Y' (by simp [h])
    have hYeq : Y = {y1, y2, y3} := hYeq1.symm
    have hLu1_eq : L u1 = L v := by
      refine eq_of_subset_of_card_le (fun w hw => ?_) (by rw [hl3 u1 (mem_inter.mp hu1U).2, hLcard])
      -- Wait: L v subset L u1! Let's prove symm direction
      by_contra hwL
      have hsub : L v ⊆ L u1 := fun w' hw' => mem_filter.mpr ⟨mem_univ _, (hlone_symm w' u1).mp (hu1_all w' hw')⟩
      have heq := eq_of_subset_of_card_le hsub (by rw [hl3 u1 (mem_inter.mp hu1U).2, hLcard])
      exact hwL (heq ▸ hw)
    have hLu2_eq : L u2 = L v := by
      have hsub : L v ⊆ L u2 := fun w' hw' => mem_filter.mpr ⟨mem_univ _, (hlone_symm w' u2).mp (hu2_all w' hw')⟩
      exact (eq_of_subset_of_card_le hsub (by rw [hl3 u2 (mem_inter.mp hu2U).2, hLcard])).symm
    have hu_nadj_Y : ∀ u ∈ ({u1, u2} : Finset (Fin 57)), L u = L v → u ∈ Vc →
        ∀ y ∈ Y, u ≠ y ∧ ¬ G.Adj u y := by
      intro u _ hLu huVc y hy
      have hyO : y ∈ O := (mem_inter.mp (mem_sdiff.mp hy).1).2
      have hyL : y ∉ L v := (mem_sdiff.mp hy).2
      refine ⟨fun heq => (mem_compl.mp hyO) (heq ▸ huVc), fun huy => ?_⟩
      have hlu := (hAdj_O_lone u huVc y hyO).mp huy
      have hyLu : y ∈ L u := mem_filter.mpr ⟨mem_univ _, hlu⟩
      rw [hLu] at hyLu
      exact hyL hyLu
    have hnu12 : ¬ G.Adj u1 u2 := fun h => (hu1_all w1 hw1L).2 ⟨u2, (hu2_all w1 hw1L).1.symm, h.symm⟩
    have hy1Y : y1 ∈ Y := by rw [hYeq]; simp
    have hy2Y : y2 ∈ Y := by rw [hYeq]; simp
    have hy3Y : y3 ∈ Y := by rw [hYeq]; simp
    have hu1_y1 := hu_nadj_Y u1 (by simp) hLu1_eq (mem_inter.mp hu1U).2 y1 hy1Y
    have hu1_y2 := hu_nadj_Y u1 (by simp) hLu1_eq (mem_inter.mp hu1U).2 y2 hy2Y
    have hu1_y3 := hu_nadj_Y u1 (by simp) hLu1_eq (mem_inter.mp hu1U).2 y3 hy3Y
    have hu2_y1 := hu_nadj_Y u2 (by simp) hLu2_eq (mem_inter.mp hu2U).2 y1 hy1Y
    have hu2_y2 := hu_nadj_Y u2 (by simp) hLu2_eq (mem_inter.mp hu2U).2 y2 hy2Y
    have hu2_y3 := hu_nadj_Y u2 (by simp) hLu2_eq (mem_inter.mp hu2U).2 y3 hy3Y
    obtain ⟨T, hTsub, hTfree, hT4⟩ := free_four_from_two_isolated_plus_three G hG u1 u2 y1 y2 y3
      hu12 hnu12 hy12 hy13 hy23 ⟨hu1_y1.1, hu1_y2.1, hu1_y3.1⟩ ⟨hu2_y1.1, hu2_y2.1, hu2_y3.1⟩
      ⟨hu1_y1.2, hu1_y2.2, hu1_y3.2⟩ ⟨hu2_y1.2, hu2_y2.2, hu2_y3.2⟩
    have hTZ : T ⊆ Z := by
      intro x hx
      have hx5 := hTsub hx
      simp only [mem_insert, mem_singleton] at hx5
      rcases hx5 with rfl | rfl | rfl | rfl | rfl
      · exact (mem_inter.mp hu1U).1
      · exact (mem_inter.mp hu2U).1
      · exact hY_sub_Z hy1Y
      · exact hY_sub_Z hy2Y
      · exact hY_sub_Z hy3Y
    exact zero_edges_union_free G hG hno12 v S T hSsub hScard hTfree hT4
      (fun x hx => hZ_noS x (hTZ hx)) (hZ_disS.mono_right hTZ)
  · -- U.card = 3, hence Vc.card = 28 and Y.card = 2!
    have hm28 : Vc.card = 28 := by
      rcases hm_27_28 with h27 | h28
      · exfalso; exact absurd (hU_le.trans (by rw [h27])) (by omega)
      · exact h28
    have hU3 : U.card = 3 := by
      have : U.card ≤ 3 := by rw [hm28] at hU_le; exact hU_le
      omega
    have hY2 : Y.card = 2 := by rw [hYcard, hm28]
    obtain ⟨y1, y2, hy12, hYeq⟩ := card_eq_two.mp hY2
    have hy1Y : y1 ∈ Y := by rw [hYeq]; simp
    have hy2Y : y2 ∈ Y := by rw [hYeq]; simp
    -- For each w in L v, U \ (Lc w).erase v has card 1 -> unique missing element!
    have hex_miss : ∀ w ∈ L v, ∃ m ∈ U, (Lc w).erase v = U.erase m := by
      intro w hw
      have hsub := hLc_sub_U w hw
      have hdiff : (U \ (Lc w).erase v).card = 1 := by
        rw [card_sdiff_of_subset hsub, hU3, hPcard w hw]
      obtain ⟨m, hm⟩ := card_eq_one.mp hdiff
      have hmU : m ∈ U := (mem_sdiff.mp (by rw [hm]; simp)).1
      refine ⟨m, hmU, eq_of_subset_of_card_le ?_ (by rw [card_erase_of_mem hmU, hU3, hPcard w hw])⟩
      intro u hu
      refine mem_erase.mpr ⟨fun heq => ?_, hsub hu⟩
      have hm_not : m ∉ (Lc w).erase v := (mem_sdiff.mp (by rw [hm]; simp)).2
      exact hm_not (heq ▸ hu)
    obtain ⟨m1, hm1U, hP1⟩ := hex_miss w1 hw1L
    obtain ⟨m2, hm2U, hP2⟩ := hex_miss w2 hw2L
    obtain ⟨m3, hm3U, hP3⟩ := hex_miss w3 hw3L
    -- Helper: kill case B when wa, wb miss uc and wc misses ub (with ub != uc)
    have hkillB : ∀ (wa wb wc ua ub uc : Fin 57),
        L v = {wa, wb, wc} → wa ≠ wb → wa ≠ wc → wb ≠ wc →
        U = {ua, ub, uc} → ua ≠ ub → ua ≠ uc → ub ≠ uc →
        (Lc wa).erase v = U.erase uc → (Lc wb).erase v = U.erase uc → (Lc wc).erase v = U.erase ub →
        False := by
      intro wa wb wc ua ub uc hLeq' hwab hwac hwbc hUeq' huab huac hubc hPa hPb hPc
      have hwaL : wa ∈ L v := by rw [hLeq']; simp
      have hwbL : wb ∈ L v := by rw [hLeq']; simp
      have hwcL : wc ∈ L v := by rw [hLeq']; simp
      have huaU : ua ∈ U := by rw [hUeq']; simp
      have hubU : ub ∈ U := by rw [hUeq']; simp
      have hucU : uc ∈ U := by rw [hUeq']; simp
      have huaVc : ua ∈ Vc := (mem_inter.mp huaU).2
      have hubVc : ub ∈ Vc := (mem_inter.mp hubU).2
      have hucVc : uc ∈ Vc := (mem_inter.mp hucU).2
      have hwa_ua : lone wa ua := (mem_filter.mp (mem_erase.mp (by rw [hPa]; exact mem_erase.mpr ⟨huac, huaU⟩)).2).2
      have hwb_ua : lone wb ua := (mem_filter.mp (mem_erase.mp (by rw [hPb]; exact mem_erase.mpr ⟨huac, huaU⟩)).2).2
      have hwc_ua : lone wc ua := (mem_filter.mp (mem_erase.mp (by rw [hPc]; exact mem_erase.mpr ⟨huab, huaU⟩)).2).2
      have hwa_ub : lone wa ub := (mem_filter.mp (mem_erase.mp (by rw [hPa]; exact mem_erase.mpr ⟨hubc, hubU⟩)).2).2
      have hwb_ub : lone wb ub := (mem_filter.mp (mem_erase.mp (by rw [hPb]; exact mem_erase.mpr ⟨hubc, hubU⟩)).2).2
      have hwc_uc : lone wc uc := (mem_filter.mp (mem_erase.mp (by rw [hPc]; exact mem_erase.mpr ⟨hubc.symm, hucU⟩)).2).2
      have hLua_eq : L ua = L v := by
        have hsub : L v ⊆ L ua := by
          intro w hw; rw [hLeq'] at hw; simp only [mem_insert, mem_singleton] at hw
          rcases hw with h | h | h
          · rw [h]; exact mem_filter.mpr ⟨mem_univ _, (hlone_symm wa ua).mp hwa_ua⟩
          · rw [h]; exact mem_filter.mpr ⟨mem_univ _, (hlone_symm wb ua).mp hwb_ua⟩
          · rw [h]; exact mem_filter.mpr ⟨mem_univ _, (hlone_symm wc ua).mp hwc_ua⟩
        exact (eq_of_subset_of_card_le hsub (by rw [hl3 ua huaVc, hLcard])).symm
      have hwab_nadj : ¬ G.Adj wa wb := fun h => (mem_filter.mp hwaL).2.2 ⟨wb, (mem_filter.mp hwbL).2.1.symm, h.symm⟩
      have hua_nadj_ub : ¬ G.Adj ua ub := fun h => hwa_ua.2 ⟨ub, hwa_ub.1.symm, h.symm⟩
      have hua_nadj_uc : ¬ G.Adj ua uc := fun h => hwc_ua.2 ⟨uc, hwc_uc.1.symm, h.symm⟩
      have hua_nadj_y : ∀ y ∈ Y, ¬ G.Adj ua y := fun y hy huy => by
        have hyO := (mem_inter.mp (mem_sdiff.mp hy).1).2
        have hlu := (hAdj_O_lone ua huaVc y hyO).mp huy
        have : y ∈ L ua := mem_filter.mpr ⟨mem_univ _, hlu⟩
        rw [hLua_eq] at this
        exact (mem_sdiff.mp hy).2 this
      have hubc_notlone : G.Adj ub uc → ∃ z, G.Adj z ub ∧ G.Adj z uc := fun h => by
        by_contra hno
        exact hL_not_Vc ub hubVc uc (mem_filter.mpr ⟨mem_univ _, h, hno⟩) hucVc
      have hwa_uc : ¬ G.Adj wa uc := fun h => by
        have hwaO : wa ∈ O := mem_compl.mpr (hL_not_Vc v hvVc wa hwaL)
        have hlu := (hlone_symm uc wa).mp ((hAdj_O_lone uc hucVc wa hwaO).mp h.symm)
        have huc_in : uc ∈ (Lc wa).erase v := mem_erase.mpr ⟨fun heq => by
          have : v ∈ U := heq ▸ hucU
          have h1 := (mem_filter.mp (mem_inter.mp this).1).1; rw [hA v] at h1
          exact (mem_compl.mp (mem_filter.mp h1).1) (mem_insert_self v S), mem_filter.mpr ⟨hucVc, hlu⟩⟩
        rw [hPa] at huc_in
        exact (mem_erase.mp huc_in).1 rfl
      have hwb_uc : ¬ G.Adj wb uc := fun h => by
        have hwbO : wb ∈ O := mem_compl.mpr (hL_not_Vc v hvVc wb hwbL)
        have hlu := (hlone_symm uc wb).mp ((hAdj_O_lone uc hucVc wb hwbO).mp h.symm)
        have huc_in : uc ∈ (Lc wb).erase v := mem_erase.mpr ⟨fun heq => by
          have : v ∈ U := heq ▸ hucU
          have h1 := (mem_filter.mp (mem_inter.mp this).1).1; rw [hA v] at h1
          exact (mem_compl.mp (mem_filter.mp h1).1) (mem_insert_self v S), mem_filter.mpr ⟨hucVc, hlu⟩⟩
        rw [hPb] at huc_in
        exact (mem_erase.mp huc_in).1 rfl
      have huc_y_lone : (G.Adj uc y1 → ¬ ∃ z, G.Adj z uc ∧ G.Adj z y1) ∧
          (G.Adj uc y2 → ¬ ∃ z, G.Adj z uc ∧ G.Adj z y2) :=
        ⟨fun h => ((hAdj_O_lone uc hucVc y1 (mem_inter.mp (mem_sdiff.mp hy1Y).1).2).mp h).2,
         fun h => ((hAdj_O_lone uc hucVc y2 (mem_inter.mp (mem_sdiff.mp hy2Y).1).2).mp h).2⟩
      have hy_hits_w : ∀ y ∈ ({y1, y2} : Finset (Fin 57)), G.Adj wa y ∨ G.Adj wb y ∨ G.Adj wc y := by
        intro y hy
        have hyY : y ∈ Y := by rw [hYeq]; exact hy
        have hyA := (mem_inter.mp (mem_sdiff.mp hyY).1).1
        have hyL := (mem_sdiff.mp hyY).2
        have hyS := disjoint_right.mp hZ_disS (hY_sub_Z hyY)
        rw [hA v] at hyA
        obtain ⟨w, hwL, hwy⟩ := AT_has_lone_to_L G hG hno12 v S (L v) hSsub (fun w hw => (mem_filter.mp hw).2)
          (hdisSL v hvVc) (by omega) y hyS hyL (mem_filter.mp hyA).2
        rw [hLeq'] at hwL; simp only [mem_insert, mem_singleton] at hwL
        rcases hwL with rfl | rfl | rfl
        · exact Or.inl hwy.1
        · exact Or.inr (Or.inl hwy.1)
        · exact Or.inr (Or.inr hwy.1)
      have hEq8 : ({wa, wb, wc, ua, ub, uc, y1, y2} : Finset (Fin 57)) = L v ∪ U ∪ Y := by
        rw [hLeq', hUeq', hYeq]; ext x
        simp only [mem_union, mem_insert, mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · exact Or.inl (Or.inl (Or.inl rfl))
          · exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
          · exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))
          · exact Or.inl (Or.inr (Or.inl rfl))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · rintro (((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl)) <;> simp
      have h8card : ({wa, wb, wc, ua, ub, uc, y1, y2} : Finset (Fin 57)).card = 8 := by
        have hdisLU : Disjoint (L v) U := disjoint_left.mpr fun w hw hU =>
          hL_not_Vc v hvVc w hw (mem_inter.mp hU).2
        have hdisLUY : Disjoint (L v ∪ U) Y := disjoint_union_left.mpr ⟨
          disjoint_left.mpr fun w hw hY => (mem_sdiff.mp hY).2 hw,
          disjoint_left.mpr fun u hu hY => (mem_compl.mp (mem_inter.mp (mem_sdiff.mp hY).1).2) (mem_inter.mp hu).2⟩
        rw [hEq8, card_union_of_disjoint hdisLUY, card_union_of_disjoint hdisLU, hLcard, hU3, hY2]
      obtain ⟨T, hTsub, hTfree, hT4⟩ := free_four_caseB G hG wa wb wc ua ub uc y1 y2 h8card
        hwab_nadj ⟨hua_nadj_ub, hua_nadj_uc, hua_nadj_y y1 hy1Y, hua_nadj_y y2 hy2Y⟩
        hubc_notlone ⟨hwa_uc, hwb_uc⟩ ⟨hwa_ub, hwb_ub⟩ hwc_uc
        huc_y_lone hy_hits_w
      have hTZ : T ⊆ Z := by
        intro x hx
        have hx8 : x ∈ L v ∪ U ∪ Y := hEq8 ▸ hTsub hx
        rcases mem_union.mp hx8 with h1 | hY
        · rcases mem_union.mp h1 with hL | hU
          · exact hL_sub_Z hL
          · exact (mem_inter.mp hU).1
        · exact hY_sub_Z hY
      exact zero_edges_union_free G hG hno12 v S T hSsub hScard hTfree hT4
        (fun x hx => hZ_noS x (hTZ hx)) (hZ_disS.mono_right hTZ)
    -- Case analysis on equality among m1, m2, m3 in U (card 3)
    by_cases h12 : m1 = m2
    · by_cases h13 : m1 = m3
      · -- m1 = m2 = m3: m1 has NO lone edge to L v -> contradicts AT_has_lone_to_L!
        have hm1A := (mem_filter.mp (mem_inter.mp hm1U).1).1
        have hm1L : m1 ∉ L v := fun h => hL_not_Vc v hvVc m1 h (mem_inter.mp hm1U).2
        have hm1S := disjoint_right.mp hZ_disS (mem_inter.mp hm1U).1
        rw [hA v] at hm1A
        obtain ⟨w, hwL, hwm1⟩ := AT_has_lone_to_L G hG hno12 v S (L v) hSsub (fun w hw => (mem_filter.mp hw).2)
          (hdisSL v hvVc) (by omega) m1 hm1S hm1L (mem_filter.mp hm1A).2
        have hm1_ne_v : m1 ≠ v := fun heq => by
          rw [heq] at hm1A; exact (mem_compl.mp (mem_filter.mp hm1A).1) (mem_insert_self v S)
        have hm1_in : m1 ∈ (Lc w).erase v := mem_erase.mpr ⟨hm1_ne_v, mem_filter.mpr ⟨(mem_inter.mp hm1U).2, hwm1⟩⟩
        rw [hLeq] at hwL; simp only [mem_insert, mem_singleton] at hwL
        rcases hwL with rfl | rfl | rfl
        · rw [hP1] at hm1_in; exact (mem_erase.mp hm1_in).1 rfl
        · rw [hP2, ← h12] at hm1_in; exact (mem_erase.mp hm1_in).1 rfl
        · rw [hP3, ← h13] at hm1_in; exact (mem_erase.mp hm1_in).1 rfl
      · -- m1 = m2 != m3 -> Case B with wa=w1, wb=w2, wc=w3, ub=m3, uc=m1!
        have hrem1 : ((U.erase m1).erase m3).card = 1 := by
          rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm h13, hm3U⟩), card_erase_of_mem hm1U, hU3]
        obtain ⟨u0, hu0eq⟩ := card_eq_one.mp hrem1
        have hu0mem : u0 ∈ (U.erase m1).erase m3 := by rw [hu0eq]; simp
        have hu03 : u0 ≠ m3 := (mem_erase.mp hu0mem).1
        have hu01 : u0 ≠ m1 := (mem_erase.mp (mem_erase.mp hu0mem).2).1
        have hUeq' : U = {u0, m3, m1} := by
          ext x; simp only [mem_insert, mem_singleton]
          constructor
          · intro hx
            by_cases hx1 : x = m1; · exact Or.inr (Or.inr hx1)
            by_cases hx3 : x = m3; · exact Or.inr (Or.inl hx3)
            have : x ∈ ({u0} : Finset (Fin 57)) := by rw [← hu0eq]; exact mem_erase.mpr ⟨hx3, mem_erase.mpr ⟨hx1, hx⟩⟩
            exact Or.inl (mem_singleton.mp this)
          · rintro (rfl | rfl | rfl)
            · exact erase_subset m1 U (erase_subset m3 _ hu0mem)
            · exact hm3U
            · exact hm1U
        exact hkillB w1 w2 w3 u0 m3 m1 hLeq hw12 hw13 hw23 hUeq' hu03 hu01 (Ne.symm h13) hP1 (h12 ▸ hP2) hP3
    · by_cases h13 : m1 = m3
      · -- m1 = m3 != m2 -> Case B with wa=w1, wb=w3, wc=w2, ub=m2, uc=m1!
        have hrem1 : ((U.erase m1).erase m2).card = 1 := by
          rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm h12, hm2U⟩), card_erase_of_mem hm1U, hU3]
        obtain ⟨u0, hu0eq⟩ := card_eq_one.mp hrem1
        have hu0mem : u0 ∈ (U.erase m1).erase m2 := by rw [hu0eq]; simp
        have hu02 : u0 ≠ m2 := (mem_erase.mp hu0mem).1
        have hu01 : u0 ≠ m1 := (mem_erase.mp (mem_erase.mp hu0mem).2).1
        have hUeq' : U = {u0, m2, m1} := by
          ext x; simp only [mem_insert, mem_singleton]
          constructor
          · intro hx
            by_cases hx1 : x = m1; · exact Or.inr (Or.inr hx1)
            by_cases hx2 : x = m2; · exact Or.inr (Or.inl hx2)
            have : x ∈ ({u0} : Finset (Fin 57)) := by rw [← hu0eq]; exact mem_erase.mpr ⟨hx2, mem_erase.mpr ⟨hx1, hx⟩⟩
            exact Or.inl (mem_singleton.mp this)
          · rintro (rfl | rfl | rfl)
            · exact erase_subset m1 U (erase_subset m2 _ hu0mem)
            · exact hm2U
            · exact hm1U
        have hLeq' : L v = {w1, w3, w2} := by rw [hLeq]; ext x; simp [or_comm, or_left_comm]
        exact hkillB w1 w3 w2 u0 m2 m1 hLeq' hw13 hw12 hw23.symm hUeq' hu02 hu01 (Ne.symm h12) hP1 (h13 ▸ hP3) hP2
      · by_cases h23 : m2 = m3
        · -- m2 = m3 != m1 -> Case B with wa=w2, wb=w3, wc=w1, ub=m1, uc=m2!
          have hrem1 : ((U.erase m2).erase m1).card = 1 := by
            rw [card_erase_of_mem (mem_erase.mpr ⟨h12, hm1U⟩), card_erase_of_mem hm2U, hU3]
          obtain ⟨u0, hu0eq⟩ := card_eq_one.mp hrem1
          have hu0mem : u0 ∈ (U.erase m2).erase m1 := by rw [hu0eq]; simp
          have hu01 : u0 ≠ m1 := (mem_erase.mp hu0mem).1
          have hu02 : u0 ≠ m2 := (mem_erase.mp (mem_erase.mp hu0mem).2).1
          have hUeq' : U = {u0, m1, m2} := by
            ext x; simp only [mem_insert, mem_singleton]
            constructor
            · intro hx
              by_cases hx2 : x = m2; · exact Or.inr (Or.inr hx2)
              by_cases hx1 : x = m1; · exact Or.inr (Or.inl hx1)
              have : x ∈ ({u0} : Finset (Fin 57)) := by rw [← hu0eq]; exact mem_erase.mpr ⟨hx1, mem_erase.mpr ⟨hx2, hx⟩⟩
              exact Or.inl (mem_singleton.mp this)
            · rintro (rfl | rfl | rfl)
              · exact erase_subset m2 U (erase_subset m1 _ hu0mem)
              · exact hm1U
              · exact hm2U
          have hLeq' : L v = {w2, w3, w1} := by rw [hLeq]; ext x; simp [or_comm, or_left_comm]
          exact hkillB w2 w3 w1 u0 m1 m2 hLeq' hw23 hw12.symm hw13.symm hUeq' hu01 hu02 h12 hP2 (h23 ▸ hP3) hP1
        · -- m1, m2, m3 ALL DISTINCT -> Case A: {v, m1, m2, m3} + 4 disjoint 8-sets => 36 <= 28!
          have hUeq' : U = {m1, m2, m3} := by
            refine (eq_of_subset_of_card_le ?_ ?_).symm
            · intro x hx; simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            · have hm1' : m1 ∉ ({m2, m3} : Finset (Fin 57)) := by simp [h12, h13]
              rw [card_insert_of_notMem hm1', card_pair h23, hU3]
          let Q4 : Finset (Fin 57) := {v, m1, m2, m3}
          have hv_not_U : v ∉ U := fun hvU => by
            have h1 := (mem_filter.mp (mem_inter.mp hvU).1).1; rw [hA v] at h1
            exact (mem_compl.mp (mem_filter.mp h1).1) (mem_insert_self v S)
          have hQ4card : Q4.card = 4 := by
            have h1 : v ∉ ({m1, m2, m3} : Finset (Fin 57)) := by rwa [← hUeq']
            have h2 : m1 ∉ ({m2, m3} : Finset (Fin 57)) := by simp [h12, h13]
            rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_pair h23]
          have hpair_share : ∀ a ∈ Q4, ∀ b ∈ Q4, a ≠ b → ∃ w ∈ L v, a ∈ Lc w ∧ b ∈ Lc w := by
            intro a ha b hb hab
            have h21 : m2 ≠ m1 := Ne.symm h12
            have h31 : m3 ≠ m1 := Ne.symm h13
            have h32 : m3 ≠ m2 := Ne.symm h23
            simp only [Q4, mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
            · exact (hab rfl).elim
            · exact ⟨w2, hw2L, hv_mem_Lc w2 hw2L, (mem_erase.mp (by rw [hP2]; exact mem_erase.mpr ⟨h12, hm1U⟩)).2⟩
            · exact ⟨w1, hw1L, hv_mem_Lc w1 hw1L, (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h21, hm2U⟩)).2⟩
            · exact ⟨w1, hw1L, hv_mem_Lc w1 hw1L, (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h31, hm3U⟩)).2⟩
            · exact ⟨w2, hw2L, (mem_erase.mp (by rw [hP2]; exact mem_erase.mpr ⟨h12, hm1U⟩)).2, hv_mem_Lc w2 hw2L⟩
            · exact (hab rfl).elim
            · exact ⟨w3, hw3L, (mem_erase.mp (by rw [hP3]; exact mem_erase.mpr ⟨h13, hm1U⟩)).2,
                (mem_erase.mp (by rw [hP3]; exact mem_erase.mpr ⟨h23, hm2U⟩)).2⟩
            · exact ⟨w2, hw2L, (mem_erase.mp (by rw [hP2]; exact mem_erase.mpr ⟨h12, hm1U⟩)).2,
                (mem_erase.mp (by rw [hP2]; exact mem_erase.mpr ⟨h32, hm3U⟩)).2⟩
            · exact ⟨w1, hw1L, (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h21, hm2U⟩)).2, hv_mem_Lc w1 hw1L⟩
            · exact ⟨w3, hw3L, (mem_erase.mp (by rw [hP3]; exact mem_erase.mpr ⟨h23, hm2U⟩)).2,
                (mem_erase.mp (by rw [hP3]; exact mem_erase.mpr ⟨h13, hm1U⟩)).2⟩
            · exact (hab rfl).elim
            · exact ⟨w1, hw1L, (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h21, hm2U⟩)).2,
                (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h31, hm3U⟩)).2⟩
            · exact ⟨w1, hw1L, (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h31, hm3U⟩)).2, hv_mem_Lc w1 hw1L⟩
            · exact ⟨w2, hw2L, (mem_erase.mp (by rw [hP2]; exact mem_erase.mpr ⟨h32, hm3U⟩)).2,
                (mem_erase.mp (by rw [hP2]; exact mem_erase.mpr ⟨h12, hm1U⟩)).2⟩
            · exact ⟨w1, hw1L, (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h31, hm3U⟩)).2,
                (mem_erase.mp (by rw [hP1]; exact mem_erase.mpr ⟨h21, hm2U⟩)).2⟩
            · exact (hab rfl).elim
          have hQ4_Vc : Q4 ⊆ Vc := by
            intro x hx; simp only [Q4, mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact hvVc
            · exact (mem_inter.mp hm1U).2
            · exact (mem_inter.mp hm2U).2
            · exact (mem_inter.mp hm3U).2
          have hQ4_dis_N : Disjoint Q4 (Q4.biUnion (fun a => C.neighborFinset a)) := by
            refine disjoint_left.mpr fun a ha hbi => ?_
            obtain ⟨b, hb, hab⟩ := mem_biUnion.mp hbi
            have hne : a ≠ b := ((C.mem_neighborFinset b a).mp hab).ne.symm
            obtain ⟨w, _, haw, hbw⟩ := hpair_share a ha b hb hne
            exact (mem_filter.mp haw).2.2 ⟨b, (mem_filter.mp hbw).2.1.symm, hCG ((C.mem_neighborFinset b a).mp hab)⟩
          have hQ4_pw : (Q4 : Set (Fin 57)).PairwiseDisjoint (fun a => C.neighborFinset a) := by
            intro a ha b hb hne
            obtain ⟨w, hwL, haw, hbw⟩ := hpair_share a ha b hb hne
            exact hLc_disj_N w (mem_compl.mpr (hL_not_Vc v hvVc w hwL)) a haw b hbw hne
          have hsub : Q4 ∪ Q4.biUnion (fun a => C.neighborFinset a) ⊆ Vc :=
            union_subset hQ4_Vc (biUnion_subset.mpr fun a ha z hz => hS_sub_Vc a (hQ4_Vc ha) z hz)
          have hle := card_le_card hsub
          rw [card_union_of_disjoint hQ4_dis_N, card_biUnion hQ4_pw, hQ4card] at hle
          have hsum32 : (∑ a ∈ Q4, (C.neighborFinset a).card) = 32 := by
            have hpt : ∀ a ∈ Q4, (C.neighborFinset a).card = 8 := fun a ha => by
              rw [C.card_neighborFinset_eq_degree, hc8 a (hQ4_Vc ha)]
            rw [sum_congr rfl hpt, sum_const, smul_eq_mul, hQ4card]
          omega

-- ============================================================================
-- Section 8: Main reduction theorem
-- ============================================================================

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H1_R1.H3 := by
  intro hlink h56 h55 n hHeq hn53 hn58 G hG hdeg hvert
  by_cases hn55 : n ≤ 55
  · exact h55 n hHeq hn53 hn55 G hG hdeg hvert
  have hdeg11 : ∀ v : Fin n, G.degree v ≤ 11 := by
    intro v
    have hv := hdeg v
    rw [← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree] at hv
    exact hv
  by_cases hcol : ∃ c : Sym2 (Fin n) → Bool, ∀ t : Finset (Fin n), G.IsNClique 3 t →
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = true) ∧
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = false)
  · obtain ⟨c, hc⟩ := hcol
    simpa [hHeq] using bound_of_good_coloring G c hc
  by_cases hfree12 : ∃ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) ∧ 12 ≤ U.card
  · obtain ⟨U, hUfree, hU12⟩ := hfree12
    exact transversal_le_of_free G U hU12 hUfree
  have hno12 : ∀ U : Finset (Fin n), (∀ K, G.IsBigMaximalClique K → ¬ K ⊆ U) → U.card ≤ 11 := by
    intro U hUfree
    by_contra! hgt
    exact hfree12 ⟨U, hUfree, hgt⟩
  obtain ⟨C, hCG, ⟨u0, v0, huv0⟩, hCtri, hCdens, hCdeg⟩ := minimal_core_props hlink G hG hcol
  let Vc := univ.filter (fun v : Fin n => 0 < C.degree v)
  have hVcne : Vc.Nonempty := ⟨u0, mem_filter.mpr ⟨mem_univ _, (C.degree_pos_iff_exists_adj u0).mpr ⟨v0, huv0⟩⟩⟩
  let loneDeg (u : Fin n) := (univ.filter fun w => G.Adj u w ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z w).card
  let A (v : Fin n) := (insert v (C.neighborFinset v))ᶜ.filter (fun x =>
    G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
    ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
  let Uval (c l : ℕ) : ℕ :=
    if c = 8 then (if l = 3 then 16 else 19)
    else if c = 9 then (if l = 2 then 10 else 11)
    else if c = 10 then 4 else 0
  have hcl_le_g : ∀ v : Fin n, C.degree v + loneDeg v ≤ G.degree v := by
    intro v
    have hdis : Disjoint (C.neighborFinset v)
        (univ.filter fun w => G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w) := by
      refine disjoint_left.mpr fun w hwC hwL => ?_
      obtain ⟨z, hzv, hzw⟩ := hCtri v w ((C.mem_neighborFinset v w).mp hwC)
      exact (mem_filter.mp hwL).2.2 ⟨z, hCG hzv, hCG hzw⟩
    have hsub : C.neighborFinset v ∪
        (univ.filter fun w => G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w) ⊆ G.neighborFinset v := by
      intro w hw
      apply (G.mem_neighborFinset v w).mpr
      rcases mem_union.mp hw with h1 | h2
      · exact hCG ((C.mem_neighborFinset v w).mp h1)
      · exact (mem_filter.mp h2).2.1
    have hle := card_le_card hsub
    rw [card_union_of_disjoint hdis, C.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hle
    exact hle
  -- Prove per-vertex tightened safe-outsider bound 2 * |A v| <= e(S, A v) + Uval (C.degree v) (loneDeg v)
  have hUbound : ∀ v ∈ Vc,
      2 * (A v).card ≤ (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) +
        Uval (C.degree v) (loneDeg v) := by
    intro v hvVc
    have hvpos : 0 < C.degree v := (mem_filter.mp hvVc).2
    have hcv8 : 8 ≤ C.degree v := hCdeg v hvpos
    have hcv11 : C.degree v ≤ 11 := (C.degree_le_of_le (v := v) hCG).trans (hdeg11 v)
    let S := C.neighborFinset v
    let L := univ.filter fun w => G.Adj v w ∧ ¬ ∃ z, G.Adj z v ∧ G.Adj z w
    have hSv : ∀ u ∈ S, G.Adj v u := fun u hu => hCG ((C.mem_neighborFinset v u).mp hu)
    have hdis : Disjoint S (A v) := disjoint_left.mpr fun u hu hAv =>
      (mem_compl.mp (mem_filter.mp hAv).1) (mem_insert_of_mem hu)
    have hsafe : ∀ x ∈ A v, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
        ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a := fun x hx => (mem_filter.mp hx).2
    have hdisSL : Disjoint S L := disjoint_left.mpr fun w hwC hwL => by
      obtain ⟨z, hzv, hzw⟩ := hCtri v w ((C.mem_neighborFinset v w).mp hwC)
      exact (mem_filter.mp hwL).2.2 ⟨z, hCG hzv, hCG hzw⟩
    have hLA : L ⊆ A v := by
      intro w hw
      have hlw := (mem_filter.mp hw).2
      have hnw : ∀ u ∈ S, ¬ G.Adj w u := fun u hu hwu =>
        hlw.2 ⟨u, (hSv u hu).symm, hwu.symm⟩
      refine mem_filter.mpr ⟨mem_compl.mpr ?_, fun a ha _ _ _ _ => (hnw a ha.1 ha.2).elim,
        fun a ha hwa => (hnw a ha hwa).elim⟩
      intro hmem
      rcases mem_insert.mp hmem with rfl | hS
      · exact G.irrefl hlw.1
      · exact (disjoint_left.mp hdisSL hS) hw
    have hpartCap : ∀ u ∈ S, ((A v).filter (G.Adj u)).card ≤ 9 := by
      intro u hu
      have huvC : C.Adj v u := (C.mem_neighborFinset v u).mp hu
      obtain ⟨w, hwu, hwv⟩ := hCtri u v huvC.symm
      have hwS : w ∈ S := (C.mem_neighborFinset v w).mpr hwv.symm
      have hvw : v ≠ w := hwv.ne.symm
      have hvA : v ∉ (A v).filter (G.Adj u) := fun h =>
        (mem_compl.mp (mem_filter.mp (mem_filter.mp h).1).1) (mem_insert_self v S)
      have hwA : w ∉ (A v).filter (G.Adj u) := fun h =>
        (mem_compl.mp (mem_filter.mp (mem_filter.mp h).1).1) (mem_insert_of_mem hwS)
      have hsub : insert v (insert w ((A v).filter (G.Adj u))) ⊆ G.neighborFinset u := by
        intro x hx
        apply (G.mem_neighborFinset u x).mpr
        rcases mem_insert.mp hx with rfl | hx
        · exact hCG huvC.symm
        · rcases mem_insert.mp hx with rfl | hx
          · exact hCG hwu.symm
          · exact (mem_filter.mp hx).2
      have hle := card_le_card hsub
      rw [card_insert_of_notMem (by simp [hvw, hvA]), card_insert_of_notMem hwA,
        G.card_neighborFinset_eq_degree] at hle
      have := hdeg11 u
      omega
    have hpc := partition_compatible_U34 G hG v S (A v) hSv hdis hsafe hpartCap
    have hScard : S.card = C.degree v := C.card_neighborFinset_eq_degree v
    have hcases : C.degree v = 8 ∨ C.degree v = 9 ∨ C.degree v = 10 ∨ C.degree v = 11 := by omega
    rcases hcases with h8 | h9 | h10 | h11
    · by_cases hl3 : loneDeg v = 3
      · simp only [Uval, h8, hl3, ↓reduceIte]
        exact (U_eight_three_props G hG hno12 v S L (A v) hSv (fun w hw => (mem_filter.mp hw).2)
          hdisSL (by omega) hl3 hLA hdis hsafe).2.1
      · simp only [Uval, h8, hl3, ↓reduceIte]
        by_contra! hgt
        obtain ⟨U, hUfree, hUcard⟩ := hpc.2 hgt
        have := hno12 U hUfree; omega
    · by_cases hl2 : loneDeg v = 2
      · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, hl2, ↓reduceIte]
        have hle5 := U_nine_two_le_ten G hG hno12 v S L (A v) hSv (fun w hw => (mem_filter.mp hw).2)
          hdisSL (by omega) hl2 hLA hdis hsafe
        omega
      · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, hl2, ↓reduceIte]
        by_contra! hgt
        obtain ⟨U, hUfree, hUcard⟩ := hpc.1 hgt
        have := hno12 U hUfree; omega
    · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte]
      by_contra! hgt
      obtain ⟨U, hUfree, hUcard⟩ := extend_two_of_gt_four G hG v S (A v) hSv hdis hsafe hgt
      have := hno12 U hUfree; omega
    · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
        show (11 : ℕ) ≠ 10 by omega, ↓reduceIte]
      by_contra! hgt
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (A v).card)
      have hIi : G.IsIndepSet (({x} : Finset (Fin n)) : Set (Fin n)) := by
        rw [← SimpleGraph.isClique_compl, coe_singleton]
        exact SimpleGraph.isClique_singleton x
      have hUfree := compatible_union_free G hG v S {x} hSv (free_of_indep hIi)
        (fun y hy => by rw [mem_singleton.mp hy]; exact hsafe x hx)
        (fun y hy z hz hyz => (hIi hy hz hyz.ne hyz).elim)
      have hle := hno12 (S ∪ {x}) hUfree
      rw [card_union_of_disjoint (hdis.mono_right (singleton_subset_iff.mpr hx)), card_singleton, hScard, h11] at hle
      omega
  have havg := core_averaged_outsider_with_slack G C hCG hCdens Vc rfl loneDeg (fun _ => rfl) A (fun _ => rfl)
  have hsumU : (∑ v ∈ Vc, 2 * (A v).card) ≤
      ∑ v ∈ Vc, ((∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + Uval (C.degree v) (loneDeg v)) :=
    sum_le_sum hUbound
  -- Per-vertex upper bound on Uval + 2 + c*(dG + l) - 2*c
  have hper_le : ∀ v ∈ Vc,
      Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v) ≤
        114 + 2 * C.degree v := by
    intro v hv
    have hcv8 : 8 ≤ C.degree v := hCdeg v (mem_filter.mp hv).2
    have hgv11 : G.degree v ≤ 11 := hdeg11 v
    have hcl := hcl_le_g v
    have hcases : C.degree v = 8 ∨ C.degree v = 9 ∨ C.degree v = 10 ∨ C.degree v = 11 := by omega
    rcases hcases with h8 | h9 | h10 | h11
    · simp only [Uval, h8, ↓reduceIte]; split_ifs <;> omega
    · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, ↓reduceIte]; split_ifs <;> omega
    · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte]; omega
    · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
        show (11 : ℕ) ≠ 10 by omega, ↓reduceIte]; omega
  -- Split on n = 58, n = 57, n = 56
  have hn_cases : n = 56 ∨ n = 57 ∨ n = 58 := by omega
  rcases hn_cases with rfl | rfl | rfl
  · -- n = 56: some v in Vc has C.degree v = 8, G.degree v = 11, loneDeg v = 3 -> H2!
    have hexv : ∃ v ∈ Vc, 2 * 56 + 2 * C.degree v ≤
        Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v) := by
      by_contra! hgtall
      have hstrict := Finset.sum_lt_sum_of_nonempty hVcne hgtall
      simp only [sum_add_distrib] at havg hsumU hstrict
      omega
    obtain ⟨v, hv, hvin⟩ := hexv
    have hcv8 : 8 ≤ C.degree v := hCdeg v (mem_filter.mp hv).2
    have hgv11 : G.degree v ≤ 11 := hdeg11 v
    have hcl := hcl_le_g v
    have hvcond : (univ.filter (G.Adj v)).card = 11 ∧ 3 ≤ loneDeg v := by
      rw [← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
      have hcases : C.degree v = 8 ∨ C.degree v = 9 ∨ C.degree v = 10 ∨ C.degree v = 11 := by omega
      rcases hcases with h8 | h9 | h10 | h11
      · simp only [Uval, h8, ↓reduceIte] at hvin; split_ifs at hvin <;> omega
      · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, ↓reduceIte] at hvin; split_ifs at hvin <;> omega
      · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte] at hvin; omega
      · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
          show (11 : ℕ) ≠ 10 by omega, ↓reduceIte] at hvin; omega
    exact h56 hHeq G hG hdeg ⟨v, hvcond⟩
  · -- n = 57: all inequalities in core_averaged_outsider_with_slack hold with EQUALITY!
    exfalso
    have hsum_le114 : (∑ v ∈ Vc, (Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v))) ≤
        ∑ v ∈ Vc, (114 + 2 * C.degree v) := sum_le_sum hper_le
    simp only [sum_add_distrib] at havg hsumU hsum_le114
    have h57_114 : (∑ _v ∈ Vc, 2 * 57) = ∑ _v ∈ Vc, 114 := rfl
    rw [h57_114] at havg
    have h114_eq : (∑ v ∈ Vc, (Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v))) =
        ∑ v ∈ Vc, (114 + 2 * C.degree v) := by
      simp only [sum_add_distrib]
      omega
    have hper_eq : ∀ v ∈ Vc,
        Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v) =
          114 + 2 * C.degree v := by
      intro v hv
      by_contra hne
      have hlt : Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v) <
          114 + 2 * C.degree v := lt_of_le_of_ne (hper_le v hv) hne
      have hsum_lt := sum_lt_sum hper_le ⟨v, hv, hlt⟩
      simp only [sum_add_distrib] at hsum_lt h114_eq
      omega
    have hc8 : ∀ v ∈ Vc, C.degree v = 8 := by
      intro v hv
      have h1 := hper_eq v hv; have hcv8 := hCdeg v (mem_filter.mp hv).2; have hgv11 := hdeg11 v; have hcl := hcl_le_g v
      have hcases : C.degree v = 8 ∨ C.degree v = 9 ∨ C.degree v = 10 ∨ C.degree v = 11 := by omega
      rcases hcases with h8 | h9 | h10 | h11
      · exact h8
      · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, ↓reduceIte] at h1; split_ifs at h1 <;> omega
      · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte] at h1; omega
      · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
          show (11 : ℕ) ≠ 10 by omega, ↓reduceIte] at h1; omega
    have hgl : ∀ v ∈ Vc, G.degree v = 11 ∧ loneDeg v = 3 := by
      intro v hv
      have h1 := hper_eq v hv; have h8 := hc8 v hv; have hgv11 := hdeg11 v; have hcl := hcl_le_g v
      simp only [Uval, h8, ↓reduceIte] at h1
      split_ifs at h1 <;> omega
    have hUeq_sum : (∑ v ∈ Vc, 2 * (A v).card) =
        ∑ v ∈ Vc, ((∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + Uval (C.degree v) (loneDeg v)) := by
      simp only [sum_add_distrib] at hsumU ⊢
      omega
    have hAeq : ∀ v ∈ Vc, 2 * (A v).card =
        (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + 16 := by
      intro v hv
      have heqv : 2 * (A v).card =
          (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + Uval (C.degree v) (loneDeg v) := by
        by_contra hne
        have hlt := lt_of_le_of_ne (hUbound v hv) hne
        have hsum_lt := sum_lt_sum hUbound ⟨v, hv, hlt⟩
        omega
      rw [hc8 v hv, (hgl v hv).2] at heqv
      simpa only [Uval, ↓reduceIte] using heqv
    have hBslack0 : (∑ v ∈ Vc, ∑ x ∈ (insert v (C.neighborFinset v))ᶜ \ A v,
        (((C.neighborFinset v).filter (G.Adj x)).card +
          ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card - 2)) = 0 := by
      omega
    have hXslack0 : (∑ v ∈ Vc, ∑ u ∈ C.neighborFinset v,
        (loneDeg u - ((insert v (C.neighborFinset v))ᶜ.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card)) = 0 := by
      omega
    have hBeq : ∀ v ∈ Vc, ∀ x ∈ (insert v (C.neighborFinset v))ᶜ \ A v,
        ((C.neighborFinset v).filter (G.Adj x)).card +
          ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card = 2 := by
      intro v hv x hx
      have h0 := (sum_eq_zero_iff.mp ((sum_eq_zero_iff.mp hBslack0) v hv)) x hx
      have hge2 : 2 ≤ ((C.neighborFinset v).filter (G.Adj x)).card +
          ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card := by
        have hxX := (mem_sdiff.mp hx).1
        have hbad : ¬ (G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
            ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) := fun hok =>
          (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨hxX, hok⟩)
        by_cases hl : ∃ a ∈ C.neighborFinset v, G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a
        · obtain ⟨a, ha, hadj, hlone⟩ := hl
          have h1 : 0 < ((C.neighborFinset v).filter (G.Adj x)).card := card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hadj⟩⟩
          have h2 : 0 < ((C.neighborFinset v).filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card :=
            card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hadj, hlone⟩⟩
          omega
        · by_contra! hlt
          apply hbad
          refine ⟨fun a ha b hb hab _ => hab (card_le_one_iff.mp (by omega) (mem_filter.mpr ha) (mem_filter.mpr hb)),
            fun a ha hadj => by by_contra hnone; exact hl ⟨a, ha, hadj, hnone⟩⟩
      omega
    have hXeq : ∀ v ∈ Vc, ∀ u ∈ C.neighborFinset v,
        ((insert v (C.neighborFinset v))ᶜ.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card =
          loneDeg u := by
      intro v hv u hu
      have h0 := (sum_eq_zero_iff.mp ((sum_eq_zero_iff.mp hXslack0) v hv)) u hu
      have hle : ((insert v (C.neighborFinset v))ᶜ.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card ≤
          loneDeg u := card_le_card (filter_subset_filter _ (subset_univ _))
      omega
    exact close_n57 G C hG hCG hno12 hdeg11 hCtri Vc rfl hVcne A (fun _ => rfl)
      hc8 (fun v hv => (hgl v hv).1) (fun v hv => (hgl v hv).2) hAeq hBeq hXeq
  · -- n = 58: strict inequality for every v in Vc!
    exfalso
    have hstrict := Finset.sum_lt_sum_of_nonempty hVcne (fun v hv => by have := hper_le v hv; omega :
      ∀ v ∈ Vc, Uval (C.degree v) (loneDeg v) + 2 + C.degree v * (G.degree v + loneDeg v) < 2 * 58 + 2 * C.degree v)
    simp only [sum_add_distrib] at havg hsumU hstrict
    omega

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H1_R1_H3_R1
