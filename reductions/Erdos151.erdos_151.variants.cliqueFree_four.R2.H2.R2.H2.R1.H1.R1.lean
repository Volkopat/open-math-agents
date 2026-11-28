import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1
import Mathlib

-- Reduction Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1.H1.R1 of step Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1.H1
-- Credit: @tameraktasTU

/-!
Exact degree- and lone-degree-sensitive core-averaged safe-outsider reduction for
`H(n) >= 12`, combining the Partition-Compatibility Lemma with elementary small Ramsey
bounds `R(3,3) <= 6`, `R(3,4) <= 9`, `R(4,3) <= 9`, `R(4,4) <= 18` and free-set
existence on 6 and 9 vertices. This closes `H(n) = 12` for all `n >= 59`, and narrows
`53 <= n <= 58` to graphs containing a full-degree-11 vertex with at least two lone
edges (or at least one lone edge at order 53).
-/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H1_R1

/-- Bikov 7-vertex link-extension lemma for triangle-free edge-coloured links. -/
def H1 : Prop :=
  ∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)

/-- Ramsey lower bound R(3, 12) >= 53. -/
def H2 : Prop :=
  ∀ n, 12 ≤ Erdos151.H n → 53 ≤ n

/-- Residual H(n) = 12 core on 53 <= n <= 58 with a full-degree-11 vertex having
at least two lone edges (or at least one lone edge at order 53). -/
def H3 : Prop :=
  ∀ n, Erdos151.H n = 12 → 53 ≤ n → n ≤ 58 →
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

private lemma core_averaged_outsider_bound {n : ℕ} (G C : SimpleGraph (Fin n))
    (hCG : C ≤ G) (hdens : C.edgeFinset.card ≤ (C.cliqueFinset 3).card)
    (Vc : Finset (Fin n)) (hVc : Vc = univ.filter (fun v : Fin n => 0 < C.degree v))
    (loneDeg : Fin n → ℕ)
    (hloneDeg : ∀ u, loneDeg u = (univ.filter fun w => G.Adj u w ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z w).card)
    (A : Fin n → Finset (Fin n))
    (hA : ∀ v, A v = (insert v (C.neighborFinset v))ᶜ.filter (fun x =>
      G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
      ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)) :
    (∑ v ∈ Vc, (2 * n + 2 * C.degree v +
      ∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card)) ≤
      ∑ v ∈ Vc, (2 * (A v).card + 2 + C.degree v * (G.degree v + loneDeg v)) := by
  classical
  have hper : ∀ v : Fin n,
      2 * n + (∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) +
        (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) ≤
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
    have hBbound : 2 * B.card ≤
        (∑ u ∈ S, (B.filter (G.Adj u)).card) +
        (∑ u ∈ S, (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card) := by
      calc
        2 * B.card = ∑ _x ∈ B, 2 := by simp [mul_comm]
        _ ≤ ∑ x ∈ B, ((S.filter (G.Adj x)).card +
              (S.filter fun a => G.Adj x a ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z a).card) :=
            sum_le_sum hunsafe
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
        (∑ u ∈ S, (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card) ≤
        ∑ u ∈ S, (G.degree u + loneDeg u) := by
      have h1 : (∑ u ∈ S, ((X.filter (G.Adj u)).card + (S.filter (C.Adj u)).card + 1 +
          (X.filter fun x => G.Adj u x ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z x).card)) ≤
          ∑ u ∈ S, (G.degree u + loneDeg u) :=
        sum_le_sum fun u hu => by have := hcap u hu; omega
      simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] using h1
    have hXcard : X.card + (S.card + 1) = n := by
      have hvS : v ∉ S := C.notMem_neighborFinset_self v
      change (insert v S)ᶜ.card + (S.card + 1) = n
      rw [← card_insert_of_notMem hvS, card_compl_add_card, Fintype.card_fin]
    have hAB : B.card + (A v).card = X.card := card_sdiff_add_card_eq_card hAX
    have hScard : S.card = C.degree v := C.card_neighborFinset_eq_degree v
    dsimp only [S] at hBbound hpart hsumcap hXcard hScard
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
-- Section 6: Main reduction theorem
-- ============================================================================

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1.H1 := by
  intro hlink hR53 hRes n hHeq G hG hdeg _
  have hH12 : 12 ≤ Erdos151.H n := by omega
  rw [hHeq]
  have hdeg11 : ∀ v : Fin n, G.degree v ≤ 11 := by
    intro v
    have hv := hdeg v
    rw [hHeq, ← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree] at hv
    omega
  by_cases hcol : ∃ c : Sym2 (Fin n) → Bool, ∀ t : Finset (Fin n), G.IsNClique 3 t →
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = true) ∧
      (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ c s(a, b) = false)
  · obtain ⟨c, hc⟩ := hcol
    simpa [hHeq] using bound_of_good_coloring G c hc
  obtain ⟨C, hCG, ⟨u0, v0, huv0⟩, hCtri, hCdens, hCdeg⟩ := minimal_core_props hlink G hG hcol
  let Vc := univ.filter (fun v : Fin n => 0 < C.degree v)
  let loneDeg (u : Fin n) := (univ.filter fun w => G.Adj u w ∧ ¬ ∃ z, G.Adj z u ∧ G.Adj z w).card
  let A (v : Fin n) := (insert v (C.neighborFinset v))ᶜ.filter (fun x =>
    G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
    ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)
  let Uval (c : ℕ) : ℕ := if c = 8 then 19 else if c = 9 then 11 else if c = 10 then 4 else 0
  by_cases hext : ∃ v ∈ Vc,
      2 * (A v).card > (∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + Uval (C.degree v)
  · obtain ⟨v, hvVc, hgt⟩ := hext
    have hvpos : 0 < C.degree v := (mem_filter.mp hvVc).2
    have hcv8 : 8 ≤ C.degree v := hCdeg v hvpos
    have hcv11 : C.degree v ≤ 11 := (C.degree_le_of_le (v := v) hCG).trans (hdeg11 v)
    let S := C.neighborFinset v
    have hSv : ∀ u ∈ S, G.Adj v u := fun u hu => hCG ((C.mem_neighborFinset v u).mp hu)
    have hdis : Disjoint S (A v) := disjoint_left.mpr fun u hu hA =>
      (mem_compl.mp (mem_filter.mp hA).1) (mem_insert_of_mem hu)
    have hsafe : ∀ x ∈ A v, G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
        ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a := fun x hx => (mem_filter.mp hx).2
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
    · simp only [Uval, h8, ↓reduceIte] at hgt
      obtain ⟨U, hUfree, hUcard⟩ := hpc.2 hgt
      exact transversal_le_of_free G U (by omega) hUfree
    · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, ↓reduceIte] at hgt
      obtain ⟨U, hUfree, hUcard⟩ := hpc.1 hgt
      exact transversal_le_of_free G U (by omega) hUfree
    · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte] at hgt
      obtain ⟨U, hUfree, hUcard⟩ := extend_two_of_gt_four G hG v S (A v) hSv hdis hsafe hgt
      exact transversal_le_of_free G U (by omega) hUfree
    · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
        show (11 : ℕ) ≠ 10 by omega, ↓reduceIte] at hgt
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (A v).card)
      have hIi : G.IsIndepSet (({x} : Finset (Fin n)) : Set (Fin n)) := by
        rw [← SimpleGraph.isClique_compl, coe_singleton]
        exact SimpleGraph.isClique_singleton x
      have hUfree := compatible_union_free G hG v S {x} hSv (free_of_indep hIi)
        (fun y hy => by rw [mem_singleton.mp hy]; exact hsafe x hx)
        (fun y hy z hz hyz => (hIi hy hz hyz.ne hyz).elim)
      have hUcard : (S ∪ {x}).card = 12 := by
        rw [card_union_of_disjoint (hdis.mono_right (singleton_subset_iff.mpr hx)), card_singleton, hScard, h11]
      exact transversal_le_of_free G (S ∪ {x}) (by omega) hUfree
  · push Not at hext
    have havg := core_averaged_outsider_bound G C hCG hCdens Vc rfl loneDeg (fun _ => rfl) A (fun _ => rfl)
    have hsumU : (∑ v ∈ Vc, 2 * (A v).card) ≤
        ∑ v ∈ Vc, ((∑ u ∈ C.neighborFinset v, ((A v).filter (G.Adj u)).card) + Uval (C.degree v)) :=
      sum_le_sum fun v hv => hext v hv
    have htot : (∑ v ∈ Vc, (2 * n + 2 * C.degree v)) ≤
        ∑ v ∈ Vc, (Uval (C.degree v) + 2 + C.degree v * (G.degree v + loneDeg v)) := by
      simp only [sum_add_distrib] at havg hsumU ⊢
      omega
    have hVcne : Vc.Nonempty := ⟨u0, mem_filter.mpr ⟨mem_univ _, (C.degree_pos_iff_exists_adj u0).mpr ⟨v0, huv0⟩⟩⟩
    have hexv : ∃ v ∈ Vc, 2 * n + 2 * C.degree v ≤
        Uval (C.degree v) + 2 + C.degree v * (G.degree v + loneDeg v) := by
      by_contra! hgtall
      have hstrict := Finset.sum_lt_sum_of_nonempty hVcne hgtall
      omega
    obtain ⟨v, hvVc, hvin⟩ := hexv
    have hvpos : 0 < C.degree v := (mem_filter.mp hvVc).2
    have hcv8 : 8 ≤ C.degree v := hCdeg v hvpos
    have hgv11 : G.degree v ≤ 11 := hdeg11 v
    have hcl_le_g : C.degree v + loneDeg v ≤ G.degree v := by
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
    have hn53 : 53 ≤ n := hR53 n hH12
    have hn58 : n ≤ 58 := by
      have hcases : C.degree v = 8 ∨ C.degree v = 9 ∨ C.degree v = 10 ∨ C.degree v = 11 := by omega
      rcases hcases with h8 | h9 | h10 | h11
      · simp only [Uval, h8, ↓reduceIte] at hvin; omega
      · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, ↓reduceIte] at hvin; omega
      · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte] at hvin; omega
      · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
          show (11 : ℕ) ≠ 10 by omega, ↓reduceIte] at hvin; omega
    have hdeg11_filter : ∀ w : Fin n, (univ.filter (G.Adj w)).card ≤ 11 := fun w => by
      rw [← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
      exact hdeg11 w
    have hvcond : (univ.filter (G.Adj v)).card = 11 ∧ (if n = 53 then 1 else 2) ≤ loneDeg v := by
      rw [← SimpleGraph.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
      have hcases : C.degree v = 8 ∨ C.degree v = 9 ∨ C.degree v = 10 ∨ C.degree v = 11 := by omega
      rcases hcases with h8 | h9 | h10 | h11
      · simp only [Uval, h8, ↓reduceIte] at hvin; split_ifs <;> omega
      · simp only [Uval, h9, show (9 : ℕ) ≠ 8 by omega, ↓reduceIte] at hvin; split_ifs <;> omega
      · simp only [Uval, h10, show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte] at hvin
        split_ifs <;> omega
      · simp only [Uval, h11, show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega,
          show (11 : ℕ) ≠ 10 by omega, ↓reduceIte] at hvin
        split_ifs <;> omega
    exact hRes n hHeq hn53 hn58 G hG hdeg11_filter ⟨v, hvcond⟩

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H1_R1
