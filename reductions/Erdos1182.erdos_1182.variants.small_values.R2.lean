import FormalConjectures.ErdosProblems.«1182»
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The small triangle-good tables

The four inputs concern covering sparse graphs, extending a finite list of
maximal triangle-free Ramsey graphs, and bounding common blue subgraphs in
fixed families on 15, 17, 21 and 23 vertices. The ten-vertex upper bound uses four
explicit triangle-free hosts. The families for 11 and 12 vertices contain eight
and ten hosts, respectively. Their edge bounds are left as finite hypotheses. The
templates are those of Brandt, Brinkmann and Harmuth (1998). The finite
certificates for low orders are checked in Lean. For positive host order,
BBHFinite.certificate_of_universal proves that every universally contained
template admits an extension certificate.

This uses work by @Tchikrazi (#4963), @marcusbuffett (#5999), @physbuzz
(#8048, #8675, #8892), and @dasante78 (#12188, #12433). The low-order dense
table was also certified by @justusklocke-cloud (#13203), and @Medrov
independently certified the seven-vertex sparse case in #14701. -/

/- # The sparse and dense triangle-good tables -/

/- Reduction of the small values table. The tree Ramsey and F lower-bound lemmas below are adapted from @Genbox, PR #104. The n = 2 computations are discharged here; the remaining finite graph classifications are hypotheses. -/

open SimpleGraph

lemma OMA.tree_copy_of_degree {V : Type} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Type) [Fintype U] (T : SimpleGraph U)
    (hT : T.IsTree) (hd : ∀ v, Fintype.card U - 1 ≤ H.degree v) : T ⊑ H := by
  classical
  have hall (k : ℕ) : ∀ (A : Type) [Fintype A] (G : SimpleGraph A),
      Fintype.card A = k → G.IsTree → (∀ v, k - 1 ≤ H.degree v) → G ⊑ H := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro A _ G hcard hG hdeg
      by_cases hk : k ≤ 1
      · let : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (hcard.trans_le hk)
        obtain ⟨w⟩ := ‹Nonempty V›
        refine ⟨⟨⟨fun _ => w, ?_⟩, ?_⟩⟩
        · intro a b hab
          exact (hab.ne (Subsingleton.elim a b)).elim
        · intro a b _
          exact Subsingleton.elim a b
      have hk' : 1 < k := by omega
      let : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hk')
      obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      let S : Set A := {v}ᶜ
      have hS : (G.induce S).IsTree :=
        ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv, hG.isAcyclic.induce S⟩
      have hS_card : Fintype.card S = k - 1 := by
        change Fintype.card (({v} : Set A)ᶜ : Set A) = k - 1
        rw [Fintype.card_compl_set, hcard]
        simp
      obtain ⟨f⟩ := ih (Fintype.card S) (by omega) S (G.induce S) rfl hS
        (fun w => (Nat.sub_le _ _).trans (hS_card.symm ▸ hdeg w))
      let u' : S := ⟨u, hu.ne.symm⟩
      let used : Finset V := Finset.univ.image (fun a : S => f a)
      have hused : used.card = Fintype.card S := by
        calc
          used.card = (Finset.univ : Finset S).card :=
            Finset.card_image_of_injective _ f.injective
          _ = _ := Finset.card_univ
      have hcenter : f u' ∈ used := Finset.mem_image.mpr ⟨u', Finset.mem_univ _, rfl⟩
      let N := H.neighborFinset (f u')
      have hN : N.card = H.degree (f u') := H.card_neighborFinset_eq_degree _
      have hNself : f u' ∉ N := H.notMem_neighborFinset_self _
      have hlarge : used.card < (insert (f u') N).card := by
        rw [Finset.card_insert_of_notMem hNself, hused, hS_card, hN]
        exact Nat.lt_succ_of_le (hdeg _)
      obtain ⟨w, hw, hnew⟩ := Finset.exists_mem_notMem_of_card_lt_card hlarge
      have hwN : w ∈ N := (Finset.mem_insert.mp hw).resolve_left
        (fun h => hnew (h.symm ▸ hcenter))
      have hwadj : H.Adj (f u') w := (H.mem_neighborFinset _ _).mp hwN
      let g (a : A) : V := if ha : a = v then w else f ⟨a, ha⟩
      have gv : g v = w := by simp [g]
      have gn (a : A) (ha : a ≠ v) : g a = f ⟨a, ha⟩ := by simp [g, ha]
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro a b hab
        by_cases ha : a = v
        · subst a
          have hbu : b = u := huniq b hab
          rw [hbu, gv, gn u hu.ne.symm]
          exact hwadj.symm
        · by_cases hb : b = v
          · subst b
            have hau : a = u := huniq a hab.symm
            rw [hau, gn u hu.ne.symm, gv]
            exact hwadj
          · rw [gn a ha, gn b hb]
            exact f.toHom.map_adj (show (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      · intro a b heq
        change g a = g b at heq
        by_cases ha : a = v
        · by_cases hb : b = v
          · exact ha.trans hb.symm
          · subst a
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _,
              by simpa only [gv, gn b hb] using heq.symm⟩
        · by_cases hb : b = v
          · subst b
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _,
              by simpa only [gv, gn a ha] using heq⟩
          · rw [gn a ha, gn b hb] at heq
            exact congrArg Subtype.val (f.injective heq)
  exact hall (Fintype.card U) U T rfl hT hd

lemma OMA.tree_ramsey_upper (n : ℕ) (hn : 2 ≤ n) {T : SimpleGraph (Fin n)}
    (hT : T.IsTree) (C : SimpleGraph (Fin (2 * n - 1))) :
    (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ := by
  classical
  by_cases htri : (⊤ : SimpleGraph (Fin 3)) ⊑ C
  · exact Or.inl htri
  right
  have hcf : C.CliqueFree 3 := by
    by_contra hc
    exact htri (by simpa only [completeGraph_eq_top] using
      (not_cliqueFree_iff_top_isContained 3).mp hc)
  by_cases hdegree : ∀ v, n - 1 ≤ Cᶜ.degree v
  · have : Nonempty (Fin (2 * n - 1)) := ⟨⟨0, by omega⟩⟩
    exact OMA.tree_copy_of_degree Cᶜ (Fin n) T hT (by simpa using hdegree)
  push Not at hdegree
  obtain ⟨v, hv⟩ := hdegree
  let S := C.neighborFinset v
  have hcard : n ≤ Fintype.card S := by
    have h := C.degree_compl v
    rw [Fintype.card_fin] at h
    rw [Fintype.card_coe, C.card_neighborFinset_eq_degree]
    omega
  have hclique : Cᶜ.IsClique (S : Set (Fin (2 * n - 1))) := by
    rw [isClique_compl]
    simpa only [S, coe_neighborFinset] using isIndepSet_neighborSet_of_triangleFree C hcf v
  let f : Fin n ↪ S := (Fin.castLEEmb hcard).trans (Fintype.equivFin S).symm.toEmbedding
  refine ⟨⟨⟨fun a => (f a).val, ?_⟩, ?_⟩⟩
  · intro a b hab
    exact hclique (f a).property (f b).property
      (fun he => hab.ne (f.injective (Subtype.ext he)))
  · intro a b he
    exact f.injective (Subtype.ext he)

lemma OMA.tree_ramsey_lower_witness (n N : ℕ) (hn : 2 ≤ n) (hN : N < 2 * n - 1)
    (T : SimpleGraph (Fin n)) (hT : T.Connected) :
    ∃ C : SimpleGraph (Fin N), ¬ ((⊤ : SimpleGraph (Fin 3)) ⊑ C) ∧ ¬ (T ⊑ Cᶜ) := by
  classical
  let color (v : Fin N) : Bool := decide (v.val < n - 1)
  let C : SimpleGraph (Fin N) := (⊤ : SimpleGraph Bool).comap color
  refine ⟨C, ?_, ?_⟩
  · rintro ⟨f⟩
    have hinj : Function.Injective (fun i : Fin 3 => color (f i)) := by
      intro i j he
      by_contra hij
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj i j := hij
      have himg : C.Adj (f i) (f j) := f.toHom.map_adj hadj
      exact himg he
    have hcard := Fintype.card_le_of_injective _ hinj
    norm_num at hcard
  · rintro ⟨f⟩
    have hlab (i j : Fin n) : color (f i) = color (f j) := by
      obtain ⟨w⟩ := hT.preconnected i j
      induction w with
      | nil => rfl
      | cons h _ ih =>
        exact (not_ne_iff.mp (f.toHom.map_adj h).2).trans ih
    have hclass (i j : Fin n) : ((f i).val < n - 1) ↔ ((f j).val < n - 1) :=
      decide_eq_decide.mp (hlab i j)
    let g (i : Fin n) : Fin (n - 1) :=
      ⟨if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1), by
        have hi := (f i).isLt
        split <;> omega⟩
    have hg : Function.Injective g := by
      intro i j he
      have heq := congrArg Fin.val he
      change (if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1)) =
        (if (f j).val < n - 1 then (f j).val else (f j).val - (n - 1)) at heq
      apply f.injective
      change f i = f j
      apply Fin.ext
      by_cases hi : (f i).val < n - 1
      · simpa only [if_pos hi, if_pos ((hclass i j).mp hi)] using heq
      · have hj : ¬ (f j).val < n - 1 := fun h => hi ((hclass i j).mpr h)
        simp only [if_neg hi, if_neg hj] at heq
        omega
    have hcard := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hcard
    omega

lemma OMA.tree_triangle_good (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : Erdos1182.IsTriangleGood T := by
  unfold Erdos1182.IsTriangleGood graphRamsey
  let good : Set ℕ := {N | ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ}
  change sInf good = 2 * n - 1
  have h : 2 * n - 1 ∈ good := OMA.tree_ramsey_upper n hn (T := T) hT
  apply le_antisymm (Nat.sInf_le h)
  refine le_csInf ⟨2 * n - 1, h⟩ ?_
  intro N hN
  by_contra! hlt
  obtain ⟨C, hC1, hC2⟩ := OMA.tree_ramsey_lower_witness n N hn hlt T hT.connected
  change ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ at hN
  exact (hN C).elim hC1 hC2

theorem OMA.f_ge_pred : type_of% @Erdos1182.erdos_1182.variants.F_ge_pred := by
  classical
  intro n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply Erdos1182.le_F
  · have htop := (connected_top (V := Fin n)).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at htop
    have hcard : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
      rw [Set.ncard_eq_toFinset_card']
      change (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2
      rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    change n ≤ (⊤ : SimpleGraph (Fin n)).edgeSet.ncard + 1 at htop
    rw [hcard] at htop
    omega
  · intro T hconn hbound
    have hmin := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at hmin
    apply OMA.tree_triangle_good n hn T
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_fin, Nat.card_coe_set_eq]
    omega
lemma OMA.F_two : Erdos1182.F 2 = 1 := by
  apply le_antisymm
  · unfold Erdos1182.F
    apply csSup_le'
    intro q hq
    simpa using hq.1
  · have h := OMA.f_ge_pred (n := 2) (by omega)
    simpa using h

lemma OMA.f_two : Erdos1182.f 2 = 1 := by
  classical
  apply le_antisymm
  · unfold Erdos1182.f
    apply csSup_le'
    intro q hq
    obtain ⟨G, hconn, heq, hgood⟩ := hq
    rw [← heq]
    have h := (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))
    rw [Fintype.card_fin] at h
    rw [Set.ncard_eq_toFinset_card']
    change G.edgeFinset.card ≤ 1
    simpa using h
  · unfold Erdos1182.f
    apply le_csSup
    · exact ⟨1, by
        intro q hq
        obtain ⟨G, _, heq, _⟩ := hq
        rw [← heq]
        have h := (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))
        rw [Fintype.card_fin] at h
        rw [Set.ncard_eq_toFinset_card']
        change G.edgeFinset.card ≤ 1
        simpa using h⟩
    · refine ⟨(⊤ : SimpleGraph (Fin 2)), connected_top, ?_, ?_⟩
      · rw [Set.ncard_eq_toFinset_card']
        change (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1
        rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
        decide
      · apply OMA.tree_triangle_good 2 (by omega)
        apply isTree_iff_connected_and_card.mpr
        constructor
        · exact connected_top
        · rw [Nat.card_fin, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
          change 2 = (⊤ : SimpleGraph (Fin 2)).edgeFinset.card + 1
          rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
          decide


namespace SmallTable.Root

/- The upper bound at three vertices and the other small values of F. -/


/- The small values of f for graphs on at least three vertices. -/


theorem combine : (Erdos1182.F 3 ≤ 2 ∧ Erdos1182.F 4 = 5 ∧ Erdos1182.F 5 = 7 ∧
  Erdos1182.F 6 = 8 ∧ Erdos1182.F 7 = 11 ∧ Erdos1182.F 8 = 11 ∧
  Erdos1182.F 9 = 16 ∧ Erdos1182.F 10 = 18 ∧ Erdos1182.F 11 = 23 ∧ Erdos1182.F 12 = 23) → (Erdos1182.f 3 = 2 ∧ Erdos1182.f 4 = 5 ∧ Erdos1182.f 5 = 8 ∧
  Erdos1182.f 6 = 12 ∧ Erdos1182.f 7 = 16 ∧ Erdos1182.f 8 = 20 ∧
  Erdos1182.f 9 = 27 ∧ Erdos1182.f 10 = 33 ∧ Erdos1182.f 11 = 41 ∧ Erdos1182.f 12 = 49) → type_of% @Erdos1182.erdos_1182.variants.small_values := by
  intro h1 h2
  rcases h1 with ⟨h3, hrest⟩
  have hlower : 2 ≤ Erdos1182.F 3 := by
    have h := OMA.f_ge_pred (n := 3) (by omega)
    simpa using h
  exact ⟨⟨OMA.F_two, le_antisymm h3 hlower, hrest⟩, ⟨OMA.f_two, h2⟩⟩

end SmallTable.Root

/- Sparse thresholds for triangle-good connected graphs. The upper bound at
every order uses an explicit obstruction. Each assignment of a source
vertex to a twin class consumes one occurrence of that class. The lower
bounds are reduced to coverings by dense spanning templates. The templates
of orders ten through twelve are the covering lists drawn on pp. 18–19 of
Brandt, Brinkmann and Harmuth (1998). -/
namespace SmallTable.Sparse
open SimpleGraph Finset


/- Cover every connected sparse graph of the specified size by one
of the tabulated dense graphs on the same vertices. -/


/- Embed each of the explicitly listed dense templates in the complement
of every triangle-free host of the critical order. -/


lemma eraseTail {A : Type} [DecidableEq A] {x : A} {xs ys : List A}
    (h : (x::xs).Subperm ys) : xs.Subperm (ys.erase x) := by
  apply List.subperm_iff_count.mpr
  intro a
  have ha := List.subperm_iff_count.mp h a
  by_cases he : a = x
  · subst a
    simp only [List.count_cons_self,List.count_erase_self] at *
    omega
  · simpa [List.count_cons,List.count_erase_of_ne he,he,Ne.symm he] using ha

theorem search_complete {V A : Type} [DecidableEq A] (edge : V → V → Bool) (red : A → A → Bool)
    (colors : List A) (allColors : ∀ c, c ∈ colors) (label : V → A)
    (valid : ∀ v w, edge v w = true → red (label v) (label w) = false)
    (order : List V) (used : List (V × A)) (supply : List A)
    (prior : ∀ p ∈ used, p.2=label p.1) (enough : (order.map label).Subperm supply) :
    (order.foldr (fun v cont seen stock => colors.any (fun c =>
      stock.contains c && (seen.all fun p => !(edge v p.1 && red c p.2)) &&
        cont ((v,c)::seen) (stock.erase c))) (fun _ _ => true)) used supply=true := by
  induction order generalizing used supply with
  | nil => rfl
  | cons v vs ih =>
    apply List.any_eq_true.mpr
    refine ⟨label v,allColors _,?_⟩
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_,?_⟩,?_⟩
    · apply List.contains_iff_mem.mpr
      obtain ⟨l,hp,hs⟩ := enough
      exact hs.subset (hp.mem_iff.mpr (by simp))
    · apply List.all_eq_true.mpr
      intro p hp
      rw [prior p hp]
      cases he : edge v p.1 with
      | false => simp
      | true => simp [valid _ _ he]
    · apply ih _ _ _ (eraseTail enough)
      intro p hp
      rcases List.mem_cons.mp hp with rfl|h
      · rfl
      · exact prior p h
theorem excludes {n h t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : SimpleGraph (Fin t)) [DecidableRel R.Adj] (group : Fin h → Fin t)
    (check : ((List.finRange n).foldr (fun v cont seen stock => (List.finRange t).any (fun c =>
      stock.contains c && (seen.all fun p => !(decide (G.Adj v p.1) && decide (R.Adj c p.2))) &&
        cont ((v,c)::seen) (stock.erase c))) (fun _ _ => true)) ([] : List (Fin n × Fin t)) ((List.finRange h).map group) = false) :
    ¬ G ⊑ (R.comap group)ᶜ := by
  rintro ⟨e⟩
  let label (i : Fin n) := group (e i)
  have enoughVertices : ((List.finRange n).map (fun v => e v)).Subperm (List.finRange h) :=
    ((List.nodup_finRange _).map e.injective).subperm (by intro x _; simp)
  obtain ⟨l,hp,hs⟩ := enoughVertices
  have en : ((List.finRange n).map label).Subperm ((List.finRange h).map group) := by
    refine ⟨l.map group,?_,hs.map group⟩
    simpa [List.map_map,label,Function.comp_def] using hp.map group
  have ok := search_complete (fun i j => decide (G.Adj i j)) (fun i j => decide (R.Adj i j))
    (List.finRange t) (by simp) label (by
      intro i j hij
      apply decide_eq_false
      exact (e.toHom.map_rel' (of_decide_eq_true hij)).2) (List.finRange n) [] _ (by simp) en
  exact Bool.noConfusion (ok.symm.trans check)

lemma forces_copy {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (good : Erdos1182.IsTriangleGood G)
    (C : SimpleGraph (Fin (2*n-1))) (ht : C.CliqueFree 3) : G ⊑ Cᶜ := by
  classical
  let S : Set ℕ := {m | ∀ B : SimpleGraph (Fin m), (⊤ : SimpleGraph (Fin 3)) ⊑ B ∨ G ⊑ Bᶜ}
  change sInf S = 2*n-1 at good
  have ne : S.Nonempty := by
    by_contra hs
    rw [Set.not_nonempty_iff_eq_empty.mp hs,Nat.sInf_empty] at good
    omega
  have hit := Nat.sInf_mem ne
  rw [good] at hit
  exact (hit C).resolve_left (by simpa only [← completeGraph_eq_top,← not_cliqueFree_iff_top_isContained] using not_not_intro ht)

lemma blocks_upper {n q : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (gc : G.Connected)
    (size : G.edgeSet.ncard=q+1) (C : SimpleGraph (Fin (2*n-1))) (tr : C.CliqueFree 3)
    (no : ¬ G ⊑ Cᶜ) : Erdos1182.F n ≤ q := by
  unfold Erdos1182.F
  apply csSup_le'
  rintro z ⟨_,hz⟩
  by_contra! hlt
  exact no (forces_copy hn G (hz G gc (by omega)) C tr)

lemma triangle_free_comap {h t : ℕ} (R : SimpleGraph (Fin t)) (group : Fin h → Fin t)
    (tr : ∀ i j k, R.Adj i j → R.Adj i k → ¬R.Adj j k) : (R.comap group).CliqueFree 3 := by
  intro S hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact tr (group a) (group b) (group c) hab hac hbc

lemma radius {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (ball : ∀ w, v=w ∨ G.Adj v w ∨ ∃ k, G.Adj v k ∧ G.Adj k w) : G.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨v,?_⟩
  intro w
  rcases ball w with h|a|⟨k,b,c⟩
  · subst w; exact Reachable.refl _
  · exact a.reachable
  · exact b.reachable.trans c.reachable

lemma edgeNumber {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.edgeSet.ncard=G.edgeFinset.card := Set.ncard_eq_toFinset_card' _

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper3 : Erdos1182.F 3 ≤ 2 := by
  let G : SimpleGraph (Fin 3) := 
    { Adj := fun i j => i≠j ∧ (38 : ℕ).testBit ((min i j).val*3+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 5 → Fin 5 := ![0, 1, 2, 3, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper4 : Erdos1182.F 4 ≤ 5 := by
  let G : SimpleGraph (Fin 4) := 
    { Adj := fun i j => i≠j ∧ (2254 : ℕ).testBit ((min i j).val*4+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 7 → Fin 5 := ![0, 1, 2, 3, 3, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper5 : Erdos1182.F 5 ≤ 7 := by
  let G : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (533150 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 9 → Fin 5 := ![0, 1, 1, 2, 2, 3, 3, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper6 : Erdos1182.F 6 ≤ 8 := by
  let G : SimpleGraph (Fin 6) := 
    { Adj := fun i j => i≠j ∧ (545360154 : ℕ).testBit ((min i j).val*6+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 11) := 
    { Adj := fun i j => i≠j ∧ (649195563651347488628968623064480 : ℕ).testBit ((min i j).val*11+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 11 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper7 : Erdos1182.F 7 ≤ 11 := by
  let G : SimpleGraph (Fin 7) := 
    { Adj := fun i j => i≠j ∧ (235277854 : ℕ).testBit ((min i j).val*7+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 13) := 
    { Adj := fun i j => i≠j ∧ (45674713929892103111903021731849029443312095648 : ℕ).testBit ((min i j).val*13+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 13 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  apply blocks_upper (by decide) G (radius G 3 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper8 : Erdos1182.F 8 ≤ 11 := by
  let G : SimpleGraph (Fin 8) := 
    { Adj := fun i j => i≠j ∧ (36099853235266634 : ℕ).testBit ((min i j).val*8+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 15 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper9 : Erdos1182.F 9 ≤ 16 := by
  let G : SimpleGraph (Fin 9) := 
    { Adj := fun i j => i≠j ∧ (2363493607849974646870 : ℕ).testBit ((min i j).val*9+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 17 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper10 : Erdos1182.F 10 ≤ 18 := by
  let G : SimpleGraph (Fin 10) := 
    { Adj := fun i j => i≠j ∧ (619272841609893681163702414 : ℕ).testBit ((min i j).val*10+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 19 → Fin 5 := ![0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper11 : Erdos1182.F 11 ≤ 23 := by
  let G : SimpleGraph (Fin 11) := 
    { Adj := fun i j => i≠j ∧ (649354097366536385312813346898726 : ℕ).testBit ((min i j).val*11+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 21 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper12 : Erdos1182.F 12 ≤ 23 := by
  let G : SimpleGraph (Fin 12) := 
    { Adj := fun i j => i≠j ∧ (2722923671064814990385729468407340106006 : ℕ).testBit ((min i j).val*12+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 23 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

theorem cover {n q : ℕ} [NeZero n] (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (place : ℕ → Fin n → Fin n)
    (rows : List (ℕ × List (Sym2 (Fin n)))) (maps : rows.all (fun r => decide (Function.Injective (place r.1) ∧ ∀ i j : Fin n, i≠j → ¬ T.Adj (place r.1 i) (place r.1 j) → s(i,j) ∈ r.2))=true)
    (sets : (((⊤ : SimpleGraph (Fin n)).edgeFinset.powersetCard q).filter
      (fun S => !(rows.any (fun r => r.2.all (fun e => decide (e ∉ S)))))) = ∅)
    (hq : q≤n.choose 2) (G : SimpleGraph (Fin n)) (small : G.edgeSet.ncard≤q) : G ⊑ T := by
  classical
  have ecount : G.edgeSet.ncard=G.edgeFinset.card := Set.ncard_eq_toFinset_card' _
  obtain ⟨W,hGW,hWT,hw⟩ := Finset.exists_subsuperset_card_eq (edgeFinset_mono (show G ≤ ⊤ from le_top))
    (ecount ▸ small) (by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin]; exact hq)
  have yes : rows.any (fun r => r.2.all (fun e => decide (e ∉ W))) = true := by
    by_contra! no
    have mem : W ∈ (((⊤ : SimpleGraph (Fin n)).edgeFinset.powersetCard q).filter
        (fun S => !(rows.any (fun r => r.2.all (fun e => decide (e ∉ S)))))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hWT,hw⟩,by simpa using no⟩
    rw [sets] at mem
    simp at mem
  obtain ⟨r,hr,hdis⟩ := List.any_eq_true.mp yes
  have ok := of_decide_eq_true (List.all_eq_true.mp maps r hr)
  refine ⟨⟨⟨place r.1,?_⟩,ok.1⟩⟩
  intro i j h
  by_contra hh
  exact (of_decide_eq_true (List.all_eq_true.mp hdis _ (ok.2 i j h.ne hh))) (hGW (SimpleGraph.mem_edgeFinset.mpr h))


set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem placed4 (G : SimpleGraph (Fin 4)) (h : G.edgeSet.ncard ≤ 5) :
    ∃ e : Fin 4 ↪ Fin 4, ∀ i j, G.Adj i j → (2048 : ℕ).testBit ((min (e i) (e j)).val*4+(max (e i) (e j)).val)=false := by
  let R : SimpleGraph (Fin 4) := 
    { Adj := fun i j => i≠j ∧ (2048 : ℕ).testBit ((min i j).val*4+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let place (code : ℕ) (i : Fin 4) := Fin.ofNat 4 ((code >>> (4*i.val))%16)
  let rows : List (ℕ × List (Sym2 (Fin 4))) := [(12816,[s(2,3)]),
  (12576,[s(1,3)]),
  (4896,[s(1,2)]),
  (12546,[s(0,3)]),
  (4866,[s(0,2)]),
  (4146,[s(0,1)])]
  obtain ⟨f⟩ := cover Rᶜ place rows (by decide +kernel) (by decide +kernel) (by decide) G h
  refine ⟨f.toEmbedding,fun i j hij => ?_⟩
  have hno := (f.toHom.map_rel' hij).2
  exact Bool.eq_false_iff.mpr (fun he => hno ⟨f.injective.ne hij.ne,he⟩)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem placed5 (G : SimpleGraph (Fin 5)) (h : G.edgeSet.ncard ≤ 7) :
    ∃ e : Fin 5 ↪ Fin 5, ∀ i j, G.Adj i j → (540672 : ℕ).testBit ((min (e i) (e j)).val*5+(max (e i) (e j)).val)=false := by
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (540672 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let place (code : ℕ) (i : Fin 5) := Fin.ofNat 5 ((code >>> (4*i.val))%16)
  let rows : List (ℕ × List (Sym2 (Fin 5))) := [(274960,[s(2,4),s(3,4)]),
  (82720,[s(1,3),s(2,3)]),
  (201280,[s(1,2),s(1,4)]),
  (205060,[s(0,3),s(0,4)]),
  (66340,[s(0,1),s(0,2)]),
  (213520,[s(2,3),s(3,4)]),
  (205840,[s(2,3),s(2,4)]),
  (213280,[s(1,3),s(3,4)]),
  (266290,[s(0,4),s(1,4)]),
  (66610,[s(0,2),s(1,2)]),
  (66370,[s(0,1),s(1,2)]),
  (81970,[s(0,3),s(1,3)]),
  (200770,[s(0,1),s(1,4)]),
  (213250,[s(0,3),s(3,4)]),
  (267010,[s(0,4),s(2,4)]),
  (82690,[s(0,3),s(2,3)]),
  (267040,[s(1,4),s(2,4)]),
  (274690,[s(0,4),s(3,4)]),
  (201760,[s(1,2),s(2,4)]),
  (201730,[s(0,2),s(2,4)]),
  (78850,[s(0,2),s(2,3)]),
  (77890,[s(0,1),s(1,3)]),
  (274720,[s(1,4),s(3,4)]),
  (78880,[s(1,2),s(2,3)]),
  (205120,[s(1,3),s(1,4)]),
  (78400,[s(1,2),s(1,3)]),
  (201220,[s(0,2),s(0,4)]),
  (78340,[s(0,2),s(0,3)]),
  (200740,[s(0,1),s(0,4)]),
  (77860,[s(0,1),s(0,3)])]
  obtain ⟨f⟩ := cover Rᶜ place rows (by decide +kernel) (by decide +kernel) (by decide) G h
  refine ⟨f.toEmbedding,fun i j hij => ?_⟩
  have hno := (f.toHom.map_rel' hij).2
  exact Bool.eq_false_iff.mpr (fun he => hno ⟨f.injective.ne hij.ne,he⟩)

lemma sufficient {n : ℕ} (hn : 2≤n) (G : SimpleGraph (Fin n)) (gc : G.Connected)
    (all : ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 → G ⊑ Cᶜ) : Erdos1182.IsTriangleGood G := by
  classical
  let S : Set ℕ := {m | ∀ C : SimpleGraph (Fin m), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ G ⊑ Cᶜ}
  change sInf S=2*n-1
  have hm : 2*n-1 ∈ S := by
    intro C
    by_cases ht : C.CliqueFree 3
    · exact Or.inr (all C ht)
    · exact Or.inl (by simpa only [completeGraph_eq_top] using (not_cliqueFree_iff_top_isContained 3).mp ht)
  apply le_antisymm (Nat.sInf_le hm)
  apply le_csInf ⟨_,hm⟩
  intro m hh
  by_contra! hl
  obtain ⟨C,ht,no⟩ := OMA.tree_ramsey_lower_witness n m hn hl G gc
  exact (hh C).elim ht no

lemma enlarge {n q : ℕ} (G : SimpleGraph (Fin n)) (lo : G.edgeSet.ncard≤q) (hi : q≤n.choose 2) :
    ∃ D : SimpleGraph (Fin n), G≤D ∧ D.edgeSet.ncard=q := by
  classical
  obtain ⟨W,hG,hT,hq⟩ := Finset.exists_subsuperset_card_eq (edgeFinset_mono (show G≤⊤ from le_top))
    ((Set.ncard_eq_toFinset_card' _ : G.edgeSet.ncard=G.edgeFinset.card) ▸ lo)
    (by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin]; exact hi)
  let D := fromEdgeSet (W : Set (Sym2 (Fin n)))
  have eD : D.edgeSet = (W : Set (Sym2 (Fin n))) := by
    rw [show D.edgeSet=_ from edgeSet_fromEdgeSet (W : Set (Sym2 (Fin n)))]
    ext e
    refine ⟨And.left,fun he => ⟨he,?_⟩⟩
    exact (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hT he))
  refine ⟨D,edgeSet_subset_edgeSet.mp ?_,by simpa [eD] using hq⟩
  rw [eD]
  exact fun e he => hG (SimpleGraph.mem_edgeFinset.mpr he)

lemma lower (baseSix : ∀ G : SimpleGraph (Fin 6), G.edgeSet.ncard = 8 →
    ∃ e : Fin 6 ↪ Fin 6, ∀ i j, G.Adj i j → (541065248 : ℕ).testBit ((min (e i) (e j)).val*6+(max (e i) (e j)).val)=false) (a : (∀ k : Fin 6,
  let n := k.val+7
  let q := (![11,11,16,18,23,23] : Fin 6 → ℕ) k
  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q →
    ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val) = false)) (b : (∀ k : Fin 9,
  let n := k.val+4
  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k
  ∀ m ∈ masks, ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ e : Fin n ↪ Fin (2*n-1), ∀ i j, i≠j → m.testBit ((min (i) (j)).val*n+(max (i) (j)).val) = false → ¬ C.Adj (e i) (e j))) (k : Fin 9) :
    (![5,7,8,11,11,16,18,23,23] : Fin 9 → ℕ) k ≤ Erdos1182.F (k.val+4) := by
  let n := k.val+4
  let q := (![5,7,8,11,11,16,18,23,23] : Fin 9 → ℕ) k
  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k
  have hi : q≤n.choose 2 := by fin_cases k <;> decide
  apply Erdos1182.le_F hi
  intro G gc ge
  apply sufficient (by dsimp [n]; omega) G gc
  intro C ht
  have placement : ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val)=false := by
    fin_cases k
    · exact ⟨2048,by decide,placed4 G ge⟩
    · exact ⟨540672,by decide,placed5 G ge⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨e,he⟩ := baseSix D eq
      exact ⟨541065248,by decide,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 0 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 1 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 2 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 3 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 4 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 5 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
  obtain ⟨m,hm,e,he⟩ := placement
  obtain ⟨f,hf⟩ := b k m hm C ht
  refine ⟨⟨⟨fun i => f (e i),?_⟩,f.injective.comp e.injective⟩⟩
  intro i j hij
  exact ⟨(f.injective.comp e.injective).ne hij.ne,hf _ _ (e.injective.ne hij.ne) (he _ _ hij)⟩

theorem combine : (∀ G : SimpleGraph (Fin 6), G.edgeSet.ncard = 8 →
    ∃ e : Fin 6 ↪ Fin 6, ∀ i j, G.Adj i j → (541065248 : ℕ).testBit ((min (e i) (e j)).val*6+(max (e i) (e j)).val)=false) → (∀ k : Fin 6,
  let n := k.val+7
  let q := (![11,11,16,18,23,23] : Fin 6 → ℕ) k
  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q →
    ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val) = false) → (∀ k : Fin 9,
  let n := k.val+4
  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k
  ∀ m ∈ masks, ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ e : Fin n ↪ Fin (2*n-1), ∀ i j, i≠j → m.testBit ((min (i) (j)).val*n+(max (i) (j)).val) = false → ¬ C.Adj (e i) (e j)) → (Erdos1182.F 3 ≤ 2 ∧ Erdos1182.F 4 = 5 ∧ Erdos1182.F 5 = 7 ∧
  Erdos1182.F 6 = 8 ∧ Erdos1182.F 7 = 11 ∧ Erdos1182.F 8 = 11 ∧
  Erdos1182.F 9 = 16 ∧ Erdos1182.F 10 = 18 ∧ Erdos1182.F 11 = 23 ∧ Erdos1182.F 12 = 23) := by
  intro baseSix a b
  exact ⟨upper3,le_antisymm upper4 (lower baseSix a b 0),le_antisymm upper5 (lower baseSix a b 1),le_antisymm upper6 (lower baseSix a b 2),le_antisymm upper7 (lower baseSix a b 3),le_antisymm upper8 (lower baseSix a b 4),le_antisymm upper9 (lower baseSix a b 5),le_antisymm upper10 (lower baseSix a b 6),le_antisymm upper11 (lower baseSix a b 7),le_antisymm upper12 (lower baseSix a b 8)⟩
end SmallTable.Sparse

/- The table of Brandt, Brinkmann and Harmuth (1998, Table 2) is an
extremum over connected graphs. For the lower certificates one need only
test complements of maximal triangle-free hosts. For the upper certificates
one need only exclude connected graphs with exactly one edge above the
tabulated number: a spanning tree extends to any intermediate edge count. -/
namespace SmallTable.Dense

open SimpleGraph Erdos1182

/- Dense witnesses embedded in every complement of a maximal triangle-free host. -/


/- A triangle-free blocking host at the first forbidden edge count. -/


lemma good_iff {n : ℕ} (hn : 2≤n) {G : SimpleGraph (Fin n)} (hc : G.Connected) :
    IsTriangleGood G ↔ ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 → G ⊑ Cᶜ := by
  classical
  let S : Set ℕ := {m | ∀ C : SimpleGraph (Fin m), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ G ⊑ Cᶜ}
  change sInf S = 2*n-1 ↔ _
  constructor
  · intro h C ht
    have hne : S.Nonempty := by
      by_contra hs
      rw [Set.not_nonempty_iff_eq_empty.mp hs, Nat.sInf_empty] at h
      omega
    have hmem := Nat.sInf_mem hne
    rw [h] at hmem
    exact (hmem C).resolve_left (by simpa only [← completeGraph_eq_top,
      ← not_cliqueFree_iff_top_isContained] using not_not_intro ht)
  · intro h
    have hm : 2*n-1 ∈ S := by
      intro C
      by_cases ht : C.CliqueFree 3
      · exact Or.inr (h C ht)
      · exact Or.inl (by simpa only [completeGraph_eq_top] using (not_cliqueFree_iff_top_isContained 3).mp ht)
    apply le_antisymm (Nat.sInf_le hm)
    apply le_csInf ⟨_,hm⟩
    intro m hmem
    by_contra! hlt
    obtain ⟨C, ht, hg⟩ := OMA.tree_ramsey_lower_witness n m hn hlt G hc
    exact (hmem C).elim ht hg

lemma intermediate {n q : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (hq : n-1≤q) (hm : q≤G.edgeSet.ncard) :
    ∃ B : SimpleGraph (Fin n), B≤G ∧ B.Connected ∧ B.edgeSet.ncard=q := by
  classical
  obtain ⟨T, hTG, ht⟩ := hc.exists_isTree_le
  have tcard := ht.card_edgeFinset
  rw [Fintype.card_fin] at tcard
  have hcard (D : SimpleGraph (Fin n)) : D.edgeSet.ncard = D.edgeFinset.card :=
    Set.ncard_eq_toFinset_card' _
  obtain ⟨W, hTW, hWG, hw⟩ := Finset.exists_subsuperset_card_eq (edgeFinset_mono hTG)
    (show T.edgeFinset.card≤q by omega) (by simpa only [hcard] using hm)
  let B := fromEdgeSet (W : Set (Sym2 (Fin n)))
  have wG : (W : Set (Sym2 (Fin n))) ⊆ G.edgeSet := fun e he => by
    have := hWG he
    simpa using this
  have eB : B.edgeSet = (W : Set (Sym2 (Fin n))) := by
    rw [show B.edgeSet = _ from edgeSet_fromEdgeSet (W : Set (Sym2 (Fin n)))]
    ext e
    exact ⟨And.left,fun he => ⟨he,G.not_isDiag_of_mem_edgeSet (wG he)⟩⟩
  have hTB : T ≤ B := by
    apply edgeSet_subset_edgeSet.mp
    rw [eB]
    intro e he
    exact hTW (by simpa using he)
  refine ⟨B, edgeSet_subset_edgeSet.mp (eB ▸ wG), ht.connected.mono hTB, ?_⟩
  simpa [eB] using hw

lemma table_entry (hlo : (∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard = q ∧
    ∀ C : SimpleGraph (Fin (2*n-1)), Maximal (fun B => B.CliqueFree 3) C → G ⊑ Cᶜ)) (hhi : (∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q+1 →
    ∃ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ)) (k : Fin 9) :
    f (k.val+4) = (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k := by
  classical
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hq : n-1≤q+1 := by fin_cases k <;> decide
  obtain ⟨G,hc,he,hg⟩ := hlo k
  apply le_antisymm
  · unfold f
    apply csSup_le'
    rintro z ⟨B,hcB,hed,good⟩
    change z≤q
    by_contra! hz
    obtain ⟨T,hTB,hcT,hsize⟩ := intermediate hcB hq (by omega)
    obtain ⟨C,ht,hmiss⟩ := hhi k T hcT hsize
    exact hmiss (((good_iff hn hcB).mp good C ht).mono_left hTB)
  · unfold f
    apply le_csSup
    · refine ⟨n.choose 2, ?_⟩
      rintro z ⟨B,_,rfl,_⟩
      rw [Set.ncard_eq_toFinset_card']
      change B.edgeFinset.card ≤ n.choose 2
      simpa only [Fintype.card_fin] using B.card_edgeFinset_le_card_choose_two
    · refine ⟨G,hc,he,(good_iff hn hc).mpr ?_⟩
      intro C ht
      let S : Set (SimpleGraph (Fin (2*n-1))) := {B | B.CliqueFree 3}
      obtain ⟨B,hCB,hmax⟩ := S.toFinite.exists_le_maximal (show C∈S from ht)
      exact (hg B hmax).mono_right (compl_le_compl hCB)

lemma base : f 3 = 2 := by
  classical
  let C := cycleGraph 5
  have ban (G : SimpleGraph (Fin 5))
      (h : ∀ a b c, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c)) :
      ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G := by
    rintro ⟨e⟩
    exact h (e 0) (e 1) (e 2) ⟨e.toHom.map_rel (by decide),e.toHom.map_rel (by decide),
      e.toHom.map_rel (by decide)⟩
  have t : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ C := ban C (by decide +kernel)
  have u : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ Cᶜ := ban Cᶜ (by decide +kernel)
  have ecard (G : SimpleGraph (Fin 3)) : G.edgeSet.ncard = G.edgeFinset.card :=
    Set.ncard_eq_toFinset_card' _
  have topcard : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]; decide
  apply le_antisymm
  · unfold f
    apply csSup_le'
    rintro q ⟨G,hc,he,hg⟩
    by_contra! hq
    have hsub := edgeFinset_mono (show G ≤ ⊤ from le_top)
    have htop : G = ⊤ := edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le hsub (by rw [topcard,←ecard,he]; omega))
    subst G
    exact u ((good_iff (by decide) hc).mp hg C (by
      by_contra h; exact t (by simpa only [completeGraph_eq_top] using (not_cliqueFree_iff_top_isContained 3).mp h)))
  · obtain ⟨T,_,hT⟩ := (connected_top : (⊤ : SimpleGraph (Fin 3)).Connected).exists_isTree_le
    unfold f
    apply le_csSup
    · refine ⟨3, ?_⟩
      rintro z ⟨G, _,rfl,_⟩
      simpa only [ecard,←topcard] using Finset.card_le_card (edgeFinset_mono (show G≤⊤ from le_top))
    · refine ⟨T,hT.connected,?_,OMA.tree_triangle_good 3 (by decide) T hT⟩
      have he := hT.card_edgeFinset
      rw [Fintype.card_fin] at he
      rw [ecard]; omega

theorem combine : (∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard = q ∧
    ∀ C : SimpleGraph (Fin (2*n-1)), Maximal (fun B => B.CliqueFree 3) C → G ⊑ Cᶜ) → (∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q+1 →
    ∃ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ) → (Erdos1182.f 3 = 2 ∧ Erdos1182.f 4 = 5 ∧ Erdos1182.f 5 = 8 ∧
  Erdos1182.f 6 = 12 ∧ Erdos1182.f 7 = 16 ∧ Erdos1182.f 8 = 20 ∧
  Erdos1182.f 9 = 27 ∧ Erdos1182.f 10 = 33 ∧ Erdos1182.f 11 = 41 ∧ Erdos1182.f 12 = 49) := by
  intro hl hu
  exact ⟨base,table_entry hl hu 0,table_entry hl hu 1,table_entry hl hu 2,
    table_entry hl hu 3,table_entry hl hu 4,table_entry hl hu 5,table_entry hl hu 6,
    table_entry hl hu 7,table_entry hl hu 8⟩
end SmallTable.Dense

/- Explicit candidates for the dense triangle-good graphs in Table 2 of
Brandt, Brinkmann and Harmuth (1998). An upper-triangular bit matrix marks
the missing edges. Orders 9 through 12 use the graphs drawn on pp. 17–19.
For each order the proof checks the edge count and gives a path of length
at most two between every pair. The remaining tasks concern only whether
the prescribed edge pattern occurs in every triangle-free host complement. -/
namespace SmallTable.Witness

open SimpleGraph

/- Complement embeddings for the specified patterns of orders 4 through 6. -/


/- Complement embeddings for the specified patterns of orders 7 through 8. -/


/- Complement embeddings for the specified patterns of orders 9 through 10. -/


/- Complement embeddings for the specified patterns of orders 11 through 12. -/


lemma sizes_and_paths : ∀ k : Fin 9,
  let n := k.val+4
  let m := (![2048,540672,541065248,8757838336,36169948434793600,2251801971660822,618970019714747783169716278,158495020111019088292975255562,14855280693082744087392632874] : Fin 9 → ℕ) k
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => i ≠ j ∧ m.testBit ((min i j).val*n+(max i j).val) = false
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (_ ∧ _))
  (∀ i j : Fin n, i=j ∨ G.Adj i j ∨ ∃ v, G.Adj i v ∧ G.Adj v j) ∧
  G.edgeFinset.card = (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k := by decide

theorem combine : (∀ t : Fin 3,
  let n := t.val+4
  let m := (![2048,540672,541065248] : Fin 3 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)) → (∀ t : Fin 2,
  let n := t.val+7
  let m := (![8757838336,36169948434793600] : Fin 2 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)) → (∀ t : Fin 2,
  let n := t.val+9
  let m := (![2251801971660822,618970019714747783169716278] : Fin 2 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)) → (∀ t : Fin 2,
  let n := t.val+11
  let m := (![158495020111019088292975255562,14855280693082744087392632874] : Fin 2 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)) → (∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard = q ∧
    ∀ C : SimpleGraph (Fin (2*n-1)), Maximal (fun B => B.CliqueFree 3) C → G ⊑ Cᶜ) := by
  intro a b c d k
  let n := k.val+4
  let m := (![2048,540672,541065248,8757838336,36169948434793600,2251801971660822,618970019714747783169716278,158495020111019088292975255562,14855280693082744087392632874] : Fin 9 → ℕ) k
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => i ≠ j ∧ m.testBit ((min i j).val*n+(max i j).val) = false
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  letI : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (_ ∧ _))
  obtain ⟨paths,card⟩ := sizes_and_paths k
  have conv : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card G.edgeSet]
    congr 1
    ext e
    simp [SimpleGraph.edgeFinset]
  refine ⟨G,⟨fun i j => ?_⟩,conv.trans card,?_⟩
  · rcases paths i j with h|h|⟨v,hi,hj⟩
    · subst j; exact Reachable.refl _
    · exact h.reachable
    · exact hi.reachable.trans hj.reachable
  intro C hC
  have embeds : ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j) := by
    fin_cases k
    · exact a 0 C hC.1
    · exact a 1 C hC.1
    · exact a 2 C hC.1
    · exact b 0 C hC.1
    · exact b 1 C hC.1
    · exact c 0 C hC.1
    · exact c 1 C hC.1
    · exact d 0 C hC.1
    · exact d 1 C hC.1
  obtain ⟨f,hf⟩ := embeds
  refine ⟨⟨⟨f,?_⟩,f.injective⟩⟩
  intro i j hij
  refine ⟨f.injective.ne hij.ne,?_⟩
  rcases lt_or_gt_of_ne hij.ne with h|h
  · exact hf i j h (by simpa [min_eq_left h.le,max_eq_right h.le] using hij.2)
  · exact fun e => hf j i h (by simpa [min_eq_right h.le,max_eq_left h.le] using hij.2) e.symm

end SmallTable.Witness

/- Upper certificates for the dense triangle-good graphs in Brandt,
Brinkmann and Harmuth (1998), Table 2. For orders four through six a
single explicit triangle-free host bounds the edge count on every image
of the vertices. Two incompatible squared-degree sums settle order seven.
For orders eight and nine we specify finite host
families: a common graph embeds in the intersection of the complement
graphs pulled back along its vertex placements. This turns each upper
bound into a finite maximum-edge computation on a fixed vertex set. -/
namespace SmallTable.Blockers

open SimpleGraph Finset

/- A common edge bound for the 2 specified hosts on 15 vertices. -/


/- A common edge bound for the 3 specified hosts on 17 vertices. -/


/- Finite obstruction families for the final three orders. -/


theorem density {n h q : ℕ} (G : SimpleGraph (Fin n)) (C : SimpleGraph (Fin h))
    [DecidableRel C.Adj]
    (bounds : ∀ S ∈ (univ : Finset (Fin h)).powersetCard n,
       (Cᶜ.edgeFinset ∩ S.sym2).card ≤ q)
    (count : q < G.edgeSet.ncard) : ¬ G ⊑ Cᶜ := by
  classical
  rintro ⟨e⟩
  let f := e.toEmbedding
  let S := (univ : Finset (Fin n)).map f
  have hs : S ∈ (univ : Finset (Fin h)).powersetCard n := by simp [S]
  have inc : G.edgeFinset.map f.sym2Map ⊆ Cᶜ.edgeFinset ∩ S.sym2 := by
    apply Finset.subset_inter
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
      exact SimpleGraph.mem_edgeFinset.mpr (e.mapEdgeSet ⟨y,SimpleGraph.mem_edgeFinset.mp hy⟩).property
    · change G.edgeFinset.map f.sym2Map ⊆ (univ.map f).sym2
      rw [Finset.sym2_map]
      exact Finset.map_subset_map.mpr (by simp)
  have bound := (Finset.card_le_card inc).trans (bounds S hs)
  rw [Finset.card_map] at bound
  have eq : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card G.edgeSet]
    congr 1
    ext x
    simp [SimpleGraph.edgeFinset]
  omega

theorem triangleFree {h : ℕ} (C : SimpleGraph (Fin h))
    (ht : ∀ i j l, C.Adj i j → C.Adj i l → ¬C.Adj j l) : C.CliqueFree 3 := by
  intro S hS
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hS
  exact ht x y z hxy hxz hyz


lemma common {n h r q : ℕ} (C : Fin r → SimpleGraph (Fin h)) (tri : ∀ a, (C a).CliqueFree 3)
    (cap : ∀ f : Fin r → Fin n ↪ Fin h,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ q)
    (G : SimpleGraph (Fin n)) (gc : G.Connected) (ge : q < G.edgeSet.ncard) :
    ∃ B : SimpleGraph (Fin h), B.CliqueFree 3 ∧ ¬ G ⊑ Bᶜ := by
  classical
  by_contra! no
  let e (a) : G.Copy (C a)ᶜ := Classical.choice (no (C a) (tri a))
  let f (a) := (e a).toEmbedding
  let D := ⨅ a, (C a)ᶜ.comap (f a)
  have sub : G ≤ D := le_iInf fun a i j hij => (e a).toHom.map_rel' hij
  have ecount := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono sub)
  exact (Nat.not_le_of_lt ge) (ecount.trans (cap f (SimpleGraph.Connected.mono sub gc)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem upper4 (G : SimpleGraph (Fin 4)) (hc : 5 < G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin 7), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let C : SimpleGraph (Fin 7) :=
    { Adj := fun i j => i ≠ j ∧ (8657448036 : ℕ).testBit ((min i j).val*7+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  refine ⟨C,triangleFree C (by decide),density G C ?_ hc⟩
  let candidates := (univ : Finset (Fin 7)).powersetCard 4
  have check : candidates.filter (fun S => 5 < (Cᶜ.edgeFinset ∩ S.sym2).card) = ∅ := by decide +kernel
  intro S hs
  exact le_of_not_gt <| fun bad => by
    have hmem : S ∈ candidates.filter (fun T => 5 < (Cᶜ.edgeFinset ∩ T.sym2).card) :=
      Finset.mem_filter.mpr ⟨hs,bad⟩
    simpa only [check,Finset.notMem_empty] using hmem

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem upper5 (G : SimpleGraph (Fin 5)) (hc : 8 < G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin 9), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let C : SimpleGraph (Fin 9) :=
    { Adj := fun i j => i ≠ j ∧ (2365794947265971925092 : ℕ).testBit ((min i j).val*9+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  refine ⟨C,triangleFree C (by decide),density G C ?_ hc⟩
  let candidates := (univ : Finset (Fin 9)).powersetCard 5
  have check : candidates.filter (fun S => 8 < (Cᶜ.edgeFinset ∩ S.sym2).card) = ∅ := by decide +kernel
  intro S hs
  exact le_of_not_gt <| fun bad => by
    have hmem : S ∈ candidates.filter (fun T => 8 < (Cᶜ.edgeFinset ∩ T.sym2).card) :=
      Finset.mem_filter.mpr ⟨hs,bad⟩
    simpa only [check,Finset.notMem_empty] using hmem

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem upper6 (G : SimpleGraph (Fin 6)) (hc : 12 < G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin 11), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let C : SimpleGraph (Fin 11) :=
    { Adj := fun i j => i ≠ j ∧ (649195563651347488628968623064480 : ℕ).testBit ((min i j).val*11+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  refine ⟨C,triangleFree C (by decide),density G C ?_ hc⟩
  let candidates := (univ : Finset (Fin 11)).powersetCard 6
  have check : candidates.filter (fun S => 12 < (Cᶜ.edgeFinset ∩ S.sym2).card) = ∅ := by decide +kernel
  intro S hs
  exact le_of_not_gt <| fun bad => by
    have hmem : S ∈ candidates.filter (fun T => 12 < (Cᶜ.edgeFinset ∩ T.sym2).card) :=
      Finset.mem_filter.mpr ⟨hs,bad⟩
    simpa only [check,Finset.notMem_empty] using hmem
theorem saturated {n h q : ℕ} (G : SimpleGraph (Fin n)) (B : SimpleGraph (Fin h))
    [DecidableRel B.Adj] (e : G.Copy B) (gsize : G.edgeSet.ncard = q)
    (bound : ∀ S ∈ (univ : Finset (Fin h)).powersetCard n, (B.edgeFinset ∩ S.sym2).card ≤ q) :
    ∃ S ∈ (univ : Finset (Fin h)).powersetCard n, (B.edgeFinset ∩ S.sym2).card = q ∧ Nonempty (G ≃g B.induce (S : Set (Fin h))) := by
  classical
  let f := e.toEmbedding
  let S := (univ : Finset (Fin n)).map f
  have hs : S ∈ (univ : Finset (Fin h)).powersetCard n := by simp [S]
  let fn (i : Fin n) : (S : Set (Fin h)) := ⟨f i,mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩
  have fb : Function.Bijective fn := by
    constructor
    · intro i j eq
      exact f.injective (congrArg Subtype.val eq)
    · intro v
      obtain ⟨i,_,eq⟩ := mem_map.mp v.prop
      exact ⟨i,Subtype.ext eq⟩
  let σ := Equiv.ofBijective fn fb
  let T := B.induce (S : Set (Fin h))
  let D := T.comap σ
  let iso : D ≃g T := SimpleGraph.Iso.comap σ T
  have dcard : D.edgeFinset.card = (B.edgeFinset ∩ S.sym2).card := by
    calc
      _ = T.edgeFinset.card := iso.card_edgeFinset_eq
      _ = _ := by rw [← B.filter_edgeFinset_toFinset_subset, B.card_filter_edgeFinset_toFinset_subset]
  have sub : G ≤ D := fun _ _ h => e.toHom.map_rel' h
  have gc : G.edgeFinset.card = q := by
    convert gsize using 1
    rw [Set.ncard_eq_toFinset_card G.edgeSet]
    congr 1
    ext v
    simp [SimpleGraph.edgeFinset]
  have eql : G = D := SimpleGraph.edgeFinset_inj.mp <| Finset.eq_of_subset_of_card_le
    (edgeFinset_mono sub) (by rw [gc,dcard]; exact bound S hs)
  refine ⟨S,hs,?_,?_⟩
  · exact le_antisymm (bound S hs) (gc ▸ ((Finset.card_le_card (edgeFinset_mono sub)).trans_eq dcard))
  · exact ⟨eql ▸ iso⟩

lemma sq_eq {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (B : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel B.Adj] (e : G ≃g B) :
    (∑ v, G.degree v ^ 2) = ∑ w, B.degree w ^ 2 := by
  calc
    _ = ∑ i, B.degree (e i)^2 := by simp
    _ = _ := e.toEquiv.sum_comp (fun i => B.degree i ^ 2)

lemma measures {h : ℕ} (B : SimpleGraph (Fin h)) [DecidableRel B.Adj] (S : Finset (Fin h)) :
    (∑ v ∈ S, (S.filter (B.Adj v)).card) = 2*(B.edgeFinset ∩ S.sym2).card ∧
    (∑ v ∈ S, (S.filter (B.Adj v)).card ^ 2) = ∑ v : S, (B.induce (S : Set (Fin h))).degree v ^ 2 := by
  let D := B.induce (S : Set (Fin h))
  have degree (v : S) : D.degree v = (S.filter (B.Adj v.val)).card := by
    let eqv : D.neighborSet v ≃ {x // x ∈ S.filter (B.Adj v.val)} :=
      { toFun := fun w => ⟨w.1.1,Finset.mem_filter.mpr ⟨w.1.2,w.2⟩⟩
        invFun := fun w => ⟨⟨w.1,(Finset.mem_filter.mp w.2).1⟩,(Finset.mem_filter.mp w.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (D.card_neighborSet_eq_degree v).symm.trans ((Fintype.card_congr eqv).trans (Fintype.card_coe _))
  constructor
  · calc
      _ = ∑ v : S, (S.filter (B.Adj v.val)).card := (Finset.sum_coe_sort S _).symm
      _ = ∑ v : S, D.degree v := Finset.sum_congr rfl (fun v _ => (degree v).symm)
      _ = 2*D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
      _ = _ := by rw [← B.filter_edgeFinset_toFinset_subset,B.card_filter_edgeFinset_toFinset_subset]
  · calc
      _ = ∑ v : S, (S.filter (B.Adj v.val)).card^2 := (Finset.sum_coe_sort S _).symm
      _ = _ := Finset.sum_congr rfl (fun v _ => congrArg (·^2) (degree v).symm)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
lemma leftData :
  let leftHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45674714610467219645711623535978988764196899492 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel leftHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let B := leftHostᶜ
  let bad (S : Finset (Fin 13)) :=
    let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
    !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) = 172)))
  ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
lemma rightData :
  let rightHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45677501523083455278743916298545253931614405028 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel rightHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let B := rightHostᶜ
  let bad (S : Finset (Fin 13)) :=
    let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
    !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) ≤ 170)))
  ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 16000000 in
theorem upperSeven (G : SimpleGraph (Fin 7)) (hg : G.edgeSet.ncard = 17) :
    ∃ C : SimpleGraph (Fin 13), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let leftHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45674714610467219645711623535978988764196899492 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel leftHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  have leftBound : ∀ S ∈ (univ : Finset (Fin 13)).powersetCard 7,
      let B := leftHostᶜ
      let v := (B.edgeFinset ∩ S.sym2).card
      v < 17 ∨ (v = 17 ∧ (∑ v, (B.induce (S : Set (Fin 13))).degree v ^ 2) = 172) := by
    let B := leftHostᶜ
    let bad (S : Finset (Fin 13)) :=
      let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
      !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) = 172)))
    have check : ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := leftData
    intro S hs
    have allowed : bad S = false := by
      by_contra! hy
      have hx : S ∈ ((univ : Finset (Fin 13)).powersetCard 7).filter (fun T => bad T=true) :=
        Finset.mem_filter.mpr ⟨hs,by simpa using hy⟩
      simp [check] at hx
    have ⟨total,moment⟩ := measures B S
    simp only [bad,Bool.not_eq_false',decide_eq_true_eq,total,moment] at allowed
    rcases allowed with small|⟨tight,hval⟩
    · left; change (B.edgeFinset ∩ S.sym2).card < 17; omega
    · right; exact ⟨by change (B.edgeFinset ∩ S.sym2).card = 17; omega,hval⟩
  let rightHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45677501523083455278743916298545253931614405028 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel rightHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  have rightBound : ∀ S ∈ (univ : Finset (Fin 13)).powersetCard 7,
      let B := rightHostᶜ
      let v := (B.edgeFinset ∩ S.sym2).card
      v < 17 ∨ (v = 17 ∧ (∑ v, (B.induce (S : Set (Fin 13))).degree v ^ 2) ≤ 170) := by
    let B := rightHostᶜ
    let bad (S : Finset (Fin 13)) :=
      let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
      !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) ≤ 170)))
    have check : ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := rightData
    intro S hs
    have allowed : bad S = false := by
      by_contra! hy
      have hx : S ∈ ((univ : Finset (Fin 13)).powersetCard 7).filter (fun T => bad T=true) :=
        Finset.mem_filter.mpr ⟨hs,by simpa using hy⟩
      simp [check] at hx
    have ⟨total,moment⟩ := measures B S
    simp only [bad,Bool.not_eq_false',decide_eq_true_eq,total,moment] at allowed
    rcases allowed with small|⟨tight,hval⟩
    · left; change (B.edgeFinset ∩ S.sym2).card < 17; omega
    · right; exact ⟨by change (B.edgeFinset ∩ S.sym2).card = 17; omega,hval⟩
  classical
  by_cases hl : G ⊑ leftHostᶜ
  · refine ⟨rightHost,triangleFree rightHost (by decide),?_⟩
    rintro ⟨r⟩
    obtain ⟨l⟩ := hl
    obtain ⟨S,hs,sc,⟨iso⟩⟩ := saturated G leftHostᶜ l hg
      (fun s h => (leftBound s h).elim Nat.le_of_lt (fun z => z.1.le))
    obtain ⟨T,ht,tc,⟨iso'⟩⟩ := saturated G rightHostᶜ r hg
      (fun s h => (rightBound s h).elim Nat.le_of_lt (fun z => z.1.le))
    have h₁ := ((leftBound S hs).resolve_left (by omega)).2
    have h₂ := ((rightBound T ht).resolve_left (by omega)).2
    have x := sq_eq _ _ iso
    have y := sq_eq _ _ iso'
    omega
  · exact ⟨leftHost,triangleFree leftHost (by decide),hl⟩

end SmallTable.Blockers

/- # Finite certificates for triangle-free hosts -/

namespace BBHFinite
open SimpleGraph

theorem saturation_witness {A : Type*} [DecidableEq A] {P : SimpleGraph A}
    (hm : Maximal (fun D : SimpleGraph A => D.CliqueFree 3) P)
    {i j : A} (ne : i≠j) (no : ¬P.Adj i j) : ∃ z, P.Adj i z ∧ P.Adj j z := by
  obtain ⟨s,hx,hy,ci,cj⟩ := exists_of_maximal_cliqueFree_not_adj (n:=2) hm ne no
  have hcard := ci.card_eq
  rw [Finset.card_insert_of_notMem hx] at hcard
  have one : s.card=1 := by omega
  obtain ⟨z,rfl⟩ := Finset.card_eq_one.mp one
  have iz : i≠z := by simpa using hx
  have jz : j≠z := by simpa using hy
  exact ⟨z, ci.1 (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) iz,
    cj.1 (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) jz⟩

theorem saturated_parent {k : ℕ} {V : Type*} (G : SimpleGraph V) (H : SimpleGraph (Fin (k+1)))
    (hm : Maximal (fun D : SimpleGraph (Fin (k+1)) => D.CliqueFree 3) H)
    (avoid : ¬ G ⊑ Hᶜ) :
    ∃ (P : SimpleGraph (Fin k)) (S : Finset (Fin k)),
      Maximal (fun D : SimpleGraph (Fin k) => D.CliqueFree 3) P ∧
      (¬ G ⊑ Pᶜ) ∧ (∀ j, j∉S → ∃ i∈S,P.Adj i j) ∧
      (∀ i, i∈S ↔ H.Adj 0 i.succ) ∧
      (∀ i j, H.Adj i.succ j.succ ↔ P.Adj i j ∧ ¬(i∈S ∧ j∈S)) := by
  classical
  let B := H.comap Fin.succ
  let f : Fin k ↪ Fin (k+1) := ⟨Fin.succ,Fin.succ_injective _⟩
  have sub : B ↪g H := SimpleGraph.Embedding.comap f H
  have ht : B.CliqueFree 3 := hm.1.comap ⟨sub.toCopy⟩
  let fam : Set (SimpleGraph (Fin k)) := {D | D.CliqueFree 3}
  obtain ⟨P,hBP,hmP⟩ := fam.toFinite.exists_le_maximal (show B∈fam from ht)
  let S := Finset.univ.filter (fun i : Fin k => H.Adj 0 i.succ)
  have mem (i : Fin k) : i∈S ↔ H.Adj 0 i.succ := by simp [S]
  refine ⟨P,S,hmP,fun e => avoid ((e.mono_right (compl_le_compl hBP)).trans
    ⟨(SimpleGraph.Embedding.complEquiv sub).toCopy⟩),?_,mem,?_⟩
  · intro j notin
    have hne : (0 : Fin (k+1)) ≠ j.succ := Fin.ne_of_lt (Fin.succ_pos _)
    obtain ⟨z,zero,jz⟩ := saturation_witness hm hne (fun hj => notin ((mem j).mpr hj))
    refine Fin.cases ?_ (fun i z0 ji => ?_) z zero jz
    · exact fun h => (h.ne rfl).elim
    · exact ⟨i,(mem i).mpr z0, hBP (show B.Adj i j from ji.symm)⟩
  · intro i j
    constructor
    · intro e
      exact ⟨hBP (show B.Adj i j from e), fun ⟨hi,hj⟩ =>
        (H.isIndepSet_neighborSet_of_triangleFree hm.1 0
          ((mem i).mp hi) ((mem j).mp hj) e.ne) e⟩
    · rintro ⟨e,ns⟩
      by_contra no
      obtain ⟨z,iz,jz⟩ := saturation_witness hm (fun h => e.ne (Fin.succ_injective _ h)) no
      refine Fin.cases ?_ (fun l il jl => ?_) z iz jz
      · exact fun h h' => ns ⟨(mem i).mpr h.symm,(mem j).mpr h'.symm⟩
      · exact P.isIndepSet_neighborSet_of_triangleFree hmP.1 l
          (hBP (show B.Adj l i from il.symm)) (hBP (show B.Adj l j from jl.symm)) e.ne e

theorem mask_of_set {k : ℕ} (U : Finset (Fin k)) :
    ∃ w < 2^k, ∀ x : Fin k, w.testBit x.val = true ↔ x∈U := by
  induction U using Finset.induction_on with
  | empty => exact ⟨0,Nat.two_pow_pos _,by simp⟩
  | @insert a U fresh ih =>
    obtain ⟨w,_,ew⟩ := ih
    refine ⟨(w ||| 2^a.val)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _),fun x => ?_⟩
    simp only [Nat.testBit_mod_two_pow,decide_eq_true x.isLt,Bool.true_and,
      Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq, Finset.mem_insert,
      ew x,Fin.ext_iff]
    aesop

/-- Certified maximal triangle-free extension tables suffice for the prescribed
complementary embedding. All possible neighborhoods are covered, including
expansions that remove old edges and children relabeled by a permutation. -/
theorem covers {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (cert :
    let edge := fun (p i j : ℕ) => i≠j ∧ p.testBit (max i j * (max i j-1)/2 + min i j) = true
    ∃ A : ℕ → List ℕ, 0∈A 0 ∧ A N=[] ∧ ∀ k<N, ∀ p∈A k, ∀ s : Fin (2^k),
      let S := fun i : ℕ => s.val.testBit i = true
      let E := fun i j : Fin (k+1) =>
        if i.val=0 then j.val≠0 ∧ S (j.val-1) else if j.val=0 then S (i.val-1)
        else edge p (i.val-1) (j.val-1) ∧ ¬(S (i.val-1) ∧ S (j.val-1))
      (∃ v : Fin k, ¬S v.val ∧ ∀ u : Fin k, S u.val → ¬edge p u.val v.val) ∨
      (∃ x y, x≠y ∧ ¬E x y ∧ ∀ z, ¬(E x z ∧ E y z)) ∨
      (∃ f : Fin n ↪ Fin (k+1), ∀ x y, G.Adj x y → ¬E (f x) (f y)) ∨
      ∃ b∈A (k+1), ∃ f : Fin (k+1) ≃ Fin (k+1), ∀ x y, E x y ↔ edge b (f x).val (f y).val
    ) : ∀ H : SimpleGraph (Fin N), H.CliqueFree 3 → G ⊑ Hᶜ := by
  classical
  let edge (p i j : ℕ) := i≠j ∧ p.testBit (max i j * (max i j-1)/2 + min i j) = true
  obtain ⟨A,init,finalRow,steps⟩ := cert
  have classify (k : ℕ) (bound : k≤N) (H : SimpleGraph (Fin k))
      (hm : Maximal (fun D : SimpleGraph (Fin k) => D.CliqueFree 3) H) (avoid : ¬ G ⊑ Hᶜ) :
      ∃ b∈A k, ∃ e : Fin k ≃ Fin k, ∀ x y,H.Adj x y ↔ edge b (e x).val (e y).val := by
    induction k with
    | zero => exact ⟨0,init,Equiv.refl _,fun x => Fin.elim0 x⟩
    | succ k ih =>
      obtain ⟨P,S,hP,noP,dom,mem,old⟩ := saturated_parent G H hm avoid
      obtain ⟨p,hp,e,code⟩ := ih (Nat.le_of_succ_le bound) P hP noP
      obtain ⟨w,hw,enc⟩ := mask_of_set (S.map e.toEmbedding)
      have mask (i : Fin k) : w.testBit (e i).val = true ↔ i∈S :=
        (enc (e i)).trans (Finset.mem_map' ..)
      let R (i j : Fin (k+1)) :=
        if i.val=0 then j.val≠0 ∧ w.testBit (j.val-1) = true else
          if j.val=0 then w.testBit (i.val-1) = true else
          edge p (i.val-1) (j.val-1) ∧ ¬(w.testBit (i.val-1) = true ∧ w.testBit (j.val-1) = true)
      let f := (finSuccEquiv k).trans (e.optionCongr.trans (finSuccEquiv k).symm)
      have f0 : f 0=0 := (finSuccEquiv k).injective (by simp [f])
      have fs (i : Fin k) : f i.succ = (e i).succ :=
        (finSuccEquiv k).injective (by simp [f])
      have lift (x y : Fin (k+1)) : H.Adj x y ↔ R (f x) (f y) := by
        revert y
        refine Fin.cases ?_ (fun i => ?_) x
        · intro y
          refine Fin.cases ?_ (fun j => ?_) y
          · simp [f0,R]
          · simpa [f0,fs,R,mask] using (mem j).symm
        · intro y
          refine Fin.cases ?_ (fun j => ?_) y
          · rw [H.adj_comm]
            simpa [f0,fs,R,mask] using (mem i).symm
          · simpa only [fs,R,Fin.val_succ,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,
              mask,←code] using old i j
      have back (x y : Fin (k+1)) : H.Adj (f.symm x) (f.symm y) ↔ R x y := by
        simpa using lift (f.symm x) (f.symm y)
      rcases steps k bound p hp ⟨w,hw⟩ with ⟨v,none,unhit⟩|⟨x,y,ne,miss,empty⟩|⟨g,hit⟩|⟨b,hb,g,hg⟩
      · have nv : e.symm v∉S := fun hv => none (by simpa using (mask _).mpr hv)
        obtain ⟨i,hi,iv⟩ := dom (e.symm v) nv
        exact (unhit (e i) ((mask i).mpr hi) (by simpa using (code _ _).mp iv)).elim
      · change ∀ z, ¬(R x z ∧ R y z) at empty
        obtain ⟨z,xz,yz⟩ := saturation_witness hm (f.symm.injective.ne ne)
          (fun a => miss ((back x y).mp a))
        exact (empty (f z) ⟨by simpa using (lift _ z).mp xz,by simpa using (lift _ z).mp yz⟩).elim
      · let h := g.trans f.symm.toEmbedding
        let hom : G →g Hᶜ :=
          { toFun := h
            map_rel' := fun {i j} a => ⟨h.injective.ne a.ne,
              fun adj => hit i j a ((back (g i) (g j)).mp adj)⟩ }
        exact (avoid ⟨hom.toCopy h.injective⟩).elim
      · exact ⟨b,hb,f.trans g,fun x y => (lift x y).trans (hg (f x) (f y))⟩
  intro H ht
  let fam : Set (SimpleGraph (Fin N)) := {D | D.CliqueFree 3}
  obtain ⟨P,leP,hm⟩ := fam.toFinite.exists_le_maximal (show H∈fam from ht)
  by_contra miss
  obtain ⟨_,hb,_⟩ := classify N le_rfl P hm (fun h => miss (h.mono_right (compl_le_compl leP)))
  simp [finalRow] at hb

end BBHFinite

namespace BBHFinite
open SimpleGraph

/-- A finite prepared witness for each expansion can be decoded using four
bits per vertex. The three target templates have at most eleven host vertices. -/
theorem template (n N q : ℕ) (A : ℕ → List ℕ) (init : 0∈A 0) (finalRow : A N=[])
    (tests :
    ∀ k<N, ∀ p∈A k, ∃ select : ℕ → ℕ, ∀ s : Fin (2^k),
      let edge (b i j : ℕ) := i≠j ∧ b.testBit (max i j * (max i j-1)/2 + min i j) = true
      let S (i : ℕ) := s.val.testBit i = true
      let E (i j : Fin (k+1)) :=
        if i.val=0 then j.val≠0 ∧ S (j.val-1) else if j.val=0 then S (i.val-1)
        else edge p (i.val-1) (j.val-1) ∧ ¬(S (i.val-1) ∧ S (j.val-1))
      let u := select s.val
      let d := u/4
      let v (w i : ℕ) : Fin (k+1) := ⟨((w >>> (4*i))%16)%(k+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
      (match u%4 with
      | 0 => if d<k then decide (¬S d ∧ ∀ x : Fin k, S x.val → ¬edge p x.val d) else false
      | 1 => let a := v d 0; let b := v d 1
             decide (a≠b ∧ ¬E a b ∧ ∀ z, ¬(E a z ∧ E b z))
      | 2 => let f (i : Fin n) := v d i.val
             decide ((∀ i j, f i=f j → i=j) ∧
               ∀ i j : Fin n, i≠j → q.testBit (min i.val j.val*n+max i.val j.val)=false → ¬E (f i) (f j))
      | _ => let f (i : Fin (k+1)) := v (d/16) i.val; let b := (A (k+1)).getD (d%16) 0
             decide (b∈A (k+1) ∧ (∀ x y,f x=f y → x=y) ∧ ∀ x y,E x y ↔ edge b (f x).val (f y).val)) = true
    ) (C : SimpleGraph (Fin N)) (ht : C.CliqueFree 3) :
    ∃ f : Fin n ↪ Fin N, ∀ i j, i<j → q.testBit (i.val*n+j.val)=false → ¬C.Adj (f i) (f j) := by
  classical
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => i≠j ∧ q.testBit (min i.val j.val*n+max i.val j.val)=false
      symm := ⟨fun {i j} g => ⟨Ne.symm g.1, by rw [min_comm,max_comm];exact g.2⟩⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
  have found := BBHFinite.covers G N (by
    refine ⟨A,init,finalRow,?_⟩
    intro k hk p hp s
    obtain ⟨select,valid⟩ := tests k hk p hp
    have proof := valid s
    dsimp only at proof
    generalize val : select s.val = u at proof
    split at proof
    · split at proof
      · rename_i lo
        exact Or.inl ⟨⟨u/4,lo⟩,of_decide_eq_true proof⟩
      · contradiction
    · exact Or.inr (Or.inl ⟨_,_,of_decide_eq_true proof⟩)
    · obtain ⟨inj,hom⟩ := of_decide_eq_true proof
      exact Or.inr (Or.inr (Or.inl ⟨⟨_,inj⟩,fun i j h => hom i j h.1 h.2⟩))
    · obtain ⟨hb,inj,r⟩ := of_decide_eq_true proof
      exact Or.inr (Or.inr (Or.inr ⟨_,hb,Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj),
        fun x y => r x y⟩))) C ht
  obtain ⟨f⟩ := found
  refine ⟨f.toEmbedding,fun i j ij keep => ?_⟩
  have adj : G.Adj i j := ⟨ij.ne,by simpa only [min_eq_left (show i.val≤j.val from ij.le),max_eq_right (show i.val≤j.val from ij.le)] using keep⟩
  exact (f.toHom.map_rel adj).2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem template4 (C : SimpleGraph (Fin 7)) (ht : C.CliqueFree 3) :
    ∃ f : Fin 4 ↪ Fin 7, ∀ i j, i<j → (2048 : ℕ).testBit (i.val*4+j.val)=false → ¬C.Adj (f i) (f j) := by
  let A := fun k => ([[0], [0], [1], [6], [51, 56], [787, 504], [15243], []] : List (List ℕ)).getD k []
  apply template 4 7 2048 A (by decide) (by decide) ?_ C ht
  intro k hk
  interval_cases k
  · intro p hp
    change p ∈ [0] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => 3, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [0] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 1027] : List ℕ).getD ((0x2 >>> (1*s))%2) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [1] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 18435, 33795, 16515] : List ℕ).getD ((0xe4 >>> (2*s))%4) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [6] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 4, 820227, 820231, 133, 540871] : List ℕ).getD ((0xb23408 >>> (3*s))%8) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [51, 56] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 17597443, 4, 17351683, 9487367, 261, 17320967, 9456643, 201, 8719363, 68742] : List ℕ).getD ((0xc7aba98076543210 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 17318087, 51266, 133, 197, 68742] : List ℕ).getD ((0xf6ed6c608408 >>> (3*s))%8) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [787, 504] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 16, 4, 86082, 261, 85122, 201, 34114, 325, 67778, 50434, 269, 68742] : List ℕ).getD ((0xe68a86d06d848cb0a689827065143210 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 353141763, 16, 16586, 32966, 68742, 49286, 67782, 66762, 337, 12, 85126, 84166, 83146, 51266, 133, 197] : List ℕ).getD ((0x3c632946305bdc8698ac5a928398a41802010020 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [15243] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 16, 8, 33038, 4, 49418, 12, 66762, 65738, 50442, 34062, 103490, 325, 20, 82310, 100678, 101702, 85126, 102726, 86150, 86214, 389, 98630, 84358, 85382, 101510, 86406, 102534, 102598, 68738, 201, 86218, 265, 85258, 84238, 68742] : List ℕ).getD ((0x8cc7a27a180881f7857837403157166d66966566165d604054c50e4ce48e44e40e3ce34030b2842422041c61440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem template5 (C : SimpleGraph (Fin 9)) (ht : C.CliqueFree 3) :
    ∃ f : Fin 5 ↪ Fin 9, ∀ i j, i<j → (540672 : ℕ).testBit (i.val*5+j.val)=false → ¬C.Adj (f i) (f j) := by
  let A := fun k => ([[0], [0], [1], [6], [51, 56], [787, 504, 960], [15169, 15243, 16320], [946323, 507840], [60117131, 63928395], []] : List (List ℕ)).getD k []
  apply template 5 9 540672 A (by decide) (by decide) ?_ C ht
  intro k hk
  interval_cases k
  · intro p hp
    change p ∈ [0] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => 3, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [0] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 1027] : List ℕ).getD ((0x2 >>> (1*s))%2) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [1] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 18435, 33795, 16515] : List ℕ).getD ((0xe4 >>> (2*s))%4) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [6] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 4, 820227, 820231, 133, 540871] : List ℕ).getD ((0xb23408 >>> (3*s))%8) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [51, 56] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 17597443, 4, 17351683, 9487367, 261, 17320967, 9456643, 201, 8719363, 13123851] : List ℕ).getD ((0xc7aba98076543210 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 17318087, 17597451, 133, 197, 13123851] : List ℕ).getD ((0xf6ed6c608408 >>> (3*s))%8) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [787, 504, 960] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 16, 4, 68488323, 261, 88133763, 201, 223363203, 325, 340529283, 348455043, 269, 1379462] : List ℕ).getD ((0xe68a86d06d848cb0a689827065143210 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 353141767, 16, 353141763, 353126403, 272681283, 352634883, 273418563, 273449283, 337, 12, 290227203, 290211843, 83937603, 289720323, 84674883, 84705603, 353141771, 133, 197, 1379462] : List ℕ).getD ((0xb5295ad2935ca307b9ac5a928398a41802010020 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 348668171, 1099842, 133, 197, 261, 1379462] : List ℕ).getD ((0x96677668866776654010201030102010 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [15169, 15243, 16320] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · refine ⟨fun s => ([0, 8, 12, 2442396867, 4455678147, 329, 4, 20, 1641538, 197, 261, 389, 1379458, 16, 201, 265, 591042, 1379462] : List ℕ).getD ((0x8a5c94b92a525c94b9302adc0739e07bdc0735805a4a64a926525464a0e629060084201084008420 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 16, 8, 6795592707, 4, 6795346947, 12, 6787481667, 6787482627, 6795345987, 6795591747, 3381986311, 325, 20, 4455681027, 2442398787, 4454697987, 2441169987, 6451942467, 1624390, 4435037187, 2417577027, 6459806787, 1640774, 6460052547, 1641798, 389, 2442415107, 4455664707, 2441432067, 4454435907, 412144707, 1362310, 2421771267, 4430842947, 420009027, 1378694, 420254787, 1379718, 6791122951, 4522772547, 201, 4521543747, 1152202, 265, 4497950787, 890122, 627982, 1379462] : List ℕ).getD ((0xc0ca6fa6eb2db2ba6aa689c031a9a59238a181f79d71b04068c6585d65544d24503ce34030b2842422041c61440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 6791119111, 20, 327882, 590022, 1379462, 852102, 1378502, 51462, 1097862, 1362182, 67782, 68742, 1377482, 405, 16, 1641606, 1640646, 1624326, 1639626, 1099842, 133, 197, 261] : List ℕ).getD ((0x46319ce31ad6319ce3178da8f9baac9ae8999cd28c14f439ac42d4941cc520020100201802010020 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [946323, 507840] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 20, 4, 1658946, 261, 16, 201, 325, 907394, 640386, 389, 24, 71208635395, 70956977155, 393, 453, 38996380675, 38744722435, 457, 610498, 869634, 269, 333, 1379462] : List ℕ).getD ((0xc990c41ae035d17427004991841ae035d0445aa06191141a8032511426604991141a403450418c608990c41a003250c425e04990c419c0331046b5a06190b409403242140820498e7408e03142418820 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 127054676999, 20, 327882, 590022, 1379462, 852102, 1378502, 51462, 1097862, 1362182, 67782, 68742, 1377482, 405, 16, 1641606, 1640646, 1624326, 1639626, 24, 469, 1903750, 1902790, 1886470, 1901770, 1099842, 133, 197, 261] : List ℕ).getD ((0x21e79f7de7a081e79f7de79d45650f4ce54c4cb5094c719245028f20e34c20b28920718561c68f64e6cc64b68964719261028f20e34c20b28920719745650f4ce54c4cb5094c719245028f20e34c20b2892071851000400800400c0040080040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [60117131, 63928395] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · refine ⟨fun s => ([0, 16, 8, 20, 4, 12, 325, 1692738, 24, 201, 389, 923778, 1972290, 28, 644290, 2217026, 2165890, 461, 918978, 1937734, 453, 1448002, 265, 401, 1641602, 2199682, 393, 517, 269, 337, 521, 1378498, 1921218, 333, 1658114, 1411330, 1187018, 1379462] : List ℕ).getD ((0x94624a2465a158625d2468401a126125d59d5a12612575c028625724659758625d24674019d25d25d59d5a426326260050624a24672170625d2468401a124425d7047212442607c028625b24671e70620824620019d2440c30c47072040c30c06c624a24659a58624a24668018a24a25459158a24a34d34028625724258258625924260019704124204259504134204050624a2464d244524524540018a24424f38418524434534028624c2422c22852052422001870440c20441850440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 20, 8, 606478, 4, 868618, 12, 348362, 1130698, 347402, 68938, 16, 1377482, 1376458, 331082, 85258, 1131722, 86218, 869642, 607502, 2218050, 389, 24, 1704390, 662918, 925062, 1886598, 1187206, 1902982, 1904006, 1641606, 1449350, 1919366, 1920390, 1657990, 1921414, 1659014, 1659078, 453, 1966470, 661958, 924102, 1624518, 1186246, 1640902, 1641926, 1903750, 1448390, 1657286, 1658310, 1920134, 1659334, 1921158, 1921222, 28, 121350, 2214278, 2215302, 1936518, 2216326, 1937542, 1937606, 2217350, 1938566, 1938630, 1938694, 517, 2212230, 645638, 907782, 1624582, 1169926, 1640966, 1641990, 2165894, 1432070, 1657350, 1658374, 2182278, 1659398, 2183302, 2183366, 137670, 1968518, 1969542, 2198662, 1970566, 2199686, 2199750, 1971590, 2200710, 2200774, 2200838, 138630, 1706438, 1707462, 2215046, 1708486, 2216070, 2216134, 1709510, 2217094, 2217158, 2217222, 1379458, 201, 1659082, 265, 1658122, 329, 1641802, 1657102, 1379462] : List ℕ).getD ((0xe0574efd3b3591d7ab48fd3bb68ddbab48ad3b3588d7ab485d20f4002a99add69773dd657735dcb7725d5d771ddc5770ddc176fddbd740804c552d2494ae52454add2b54acd23d4ac52af4ab52ab4aa52a748b002b0a8c3a10e7c39d0e6c3990e5c3950e4c3910e3c38d0e2c3890c08084552b748de0b744de0377eddf373cddeb778dddb774ddcb770ddb002a99aa7689d9a7649d8a7609d7a75c9d6a7589d5a7549d4a7509c0804c55297485d197445d097405cf973c5ce97385cd97345cc97305cb002a50984240888420187841c08684182c50412084040e182840608080 >>> (7*s))%128) 0, ?_⟩
      decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem template6 (C : SimpleGraph (Fin 11)) (ht : C.CliqueFree 3) :
    ∃ f : Fin 6 ↪ Fin 11, ∀ i j, i<j → (541065248 : ℕ).testBit (i.val*6+j.val)=false → ¬C.Adj (f i) (f j) := by
  let A := fun k => ([[0], [0], [1], [6], [51, 56], [787, 504, 960], [15169, 31744, 15243, 16320], [946323, 514624, 1012737, 1047552, 507840], [57925920, 127797387, 63927297, 60117131, 66059264, 63928395], [4154330304, 8116958209, 4086633664, 16233924755, 8387558400], [2094048417867, 20072748419211, 4277382612043], []] : List (List ℕ)).getD k []
  apply template 6 11 541065248 A (by decide) (by decide) ?_ C ht
  intro k hk
  interval_cases k
  · intro p hp
    change p ∈ [0] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => 3, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [0] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 1027] : List ℕ).getD ((0x2 >>> (1*s))%2) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [1] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 18435, 33795, 16515] : List ℕ).getD ((0xe4 >>> (2*s))%4) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [6] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl
    · refine ⟨fun s => ([0, 4, 820227, 820231, 133, 540871] : List ℕ).getD ((0xb23408 >>> (3*s))%8) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [51, 56] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 17597443, 4, 17351683, 9487367, 261, 17320967, 9456643, 201, 8719363, 13123851] : List ℕ).getD ((0xc7aba98076543210 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 17318087, 17597451, 133, 197, 13123851] : List ℕ).getD ((0xf6ed6c608408 >>> (3*s))%8) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [787, 504, 960] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 16, 4, 68488323, 261, 88133763, 201, 223363203, 325, 340529283, 348455043, 269, 281559367] : List ℕ).getD ((0xe68a86d06d848cb0a689827065143210 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 353141771, 16, 353141763, 353126403, 272681283, 352634883, 273418563, 273449283, 337, 12, 290227203, 290211843, 83937603, 289720323, 84674883, 84705603, 353141775, 133, 197, 281559367] : List ℕ).getD ((0xb5295ad2935ca307b9ac5a928398a41802010020 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 348668175, 353141767, 133, 197, 261, 281559367] : List ℕ).getD ((0x96677668866776654010201030102010 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [15169, 31744, 15243, 16320] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl
    · refine ⟨fun s => ([0, 8, 12, 2442396867, 4455678147, 329, 4, 20, 5780081671, 197, 261, 389, 6786699271, 16, 201, 265, 6795575435, 26544206] : List ℕ).getD ((0x8a5c94b92a525c94b9302adc0739e07bdc0735805a4a64a926525464a0e629060084201084008420 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 16, 6724010319, 22070282, 133, 197, 261, 325, 26544206] : List ℕ).getD ((0xb77887799778877aa77887799778877650102010301020104010201030102010 >>> (4*s))%16) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 16, 8, 6795592707, 4, 6795346947, 12, 6787481667, 6787482627, 6795345987, 6795591747, 3381986323, 325, 20, 4455681027, 2442398787, 4454697987, 2441169987, 6451942467, 5587353991, 4435037187, 2417577027, 6459806787, 5579489671, 6460052547, 5578752391, 389, 2442415107, 4455664707, 2441432067, 4454435907, 412144707, 3574088071, 2421771267, 4430842947, 420009027, 3566223751, 420254787, 3565486471, 6791122963, 4522772547, 201, 4521543747, 2236354951, 265, 4497950787, 2228490631, 2227261831, 26544206] : List ℕ).getD ((0xc0ca6fa6eb2db2ba6aa689c031a9a59238a181f79d71b04068c6585d65544d24503ce34030b2842422041c61440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 6791119123, 20, 6795592715, 6795577355, 6786695431, 6795085835, 6787186951, 6724010311, 5436918155, 6783289355, 6791119111, 6720078151, 5452646795, 6719586631, 5453384075, 5453414795, 405, 16, 5788959755, 5788944395, 5780062471, 5788452875, 5780553991, 4710744391, 1410386315, 5776656395, 5784486151, 4706812231, 1426114955, 4706320711, 1426852235, 1426882955, 6795592719, 133, 197, 261, 26544206] : List ℕ).getD ((0xa259669a59679e59669a59645238a181f79d71b69961759551349140f38d30b2892071851000400800400c0040080040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [946323, 514624, 1012737, 1047552, 507840] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · refine ⟨fun s => ([0, 12, 8, 20, 4, 72286569475, 261, 16, 201, 325, 90689552519, 72436957323, 389, 24, 71208635407, 70956977167, 393, 453, 38996380687, 38744722447, 457, 127054659719, 126982897803, 269, 333, 26544206] : List ℕ).getD ((0xc990c41ae035d17427004991841ae035d0445aa06191141a8032511426604991141a403450418c608990c41a003250c425e04990c419c0331046b5a06190b409403242140820498e7408e03142418820 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 121346787719, 126035738755, 389, 401, 127054122115, 329, 333, 24, 469, 16, 20, 197, 133, 265, 26018826, 261, 22071302, 26544206] : List ℕ).getD ((0xac20f7c2139c20f7c2094c20f7c2118c20f7c2143420f7c2139c20f7c2126420f7c1ce8b60d7b5cd6192952929399295292b4814048100180601806031c2110821314211082120020100201802010020 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 8, 12, 16, 93697082763, 125909352843, 393, 4, 24, 8736962, 197, 261, 325, 453, 4804802, 20, 201, 265, 329, 9767942, 26544206] : List ℕ).getD ((0xa2a0a5414b5aa0a5414c62a0a5414b5aa0a5415333600842208c6008424094a00842208c60083dc06a8c752d475a967531476298752d475a967525073148008420108400842018c60084201084008420 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 16, 126983094611, 24, 5573762, 9768002, 610502, 13961282, 872582, 872522, 22612046, 18139202, 1133702, 1133642, 26544206, 1132622, 26545226, 26545286, 22071362, 1379462, 1379402, 26298446, 1378382, 26299466, 26299526, 21039182, 26038346, 26038406, 25776326, 473, 20, 22874190, 30738510, 30739530, 30739590, 30492750, 30493770, 30493830, 30232650, 30232710, 29970630, 22070282, 133, 197, 261, 325] : List ℕ).getD ((0x46db6ebadb6fbedb6ebadb70c2db6ebadb6fbedb6ebadb6c82592b8eaa5c8a89d99975958e59128d03ce88c2ca2481e18144df45e75c35b6996175954544d24503ce34c2ca2481c61400400800400c00400800401000400800400c0040080040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 127054677015, 20, 127054677003, 127054661643, 126790715399, 127054170123, 126790469639, 126790438919, 126706829643, 127042373643, 126782605319, 126782574599, 126718626123, 126781837319, 126719117643, 126719133003, 405, 16, 126048044043, 126048028683, 121757550599, 126047537163, 121757304839, 121757274119, 120667031883, 126035740683, 121749440519, 121749409799, 120678828363, 121748672519, 120679319883, 120679335243, 24, 93835788363, 93835757643, 107597021635, 93835020363, 107596775875, 107596745155, 26298446, 93819291723, 107581047235, 107581016515, 26036306, 107579787715, 25775186, 25513106, 469, 93835789323, 93835773963, 25120786439, 93835282443, 25120540679, 25120509959, 7924140363, 93823485963, 25112676359, 25112645639, 7935936843, 25111908359, 7936428363, 7936443723, 126048043083, 126048012363, 75384766915, 126047275083, 75384521155, 75384490435, 30492750, 126031546443, 75368792515, 75368761795, 30230610, 75367532995, 29969490, 29707410, 127054676043, 127054645323, 72364868035, 127053908043, 72364622275, 72364591555, 30509134, 127038179403, 72348893635, 72348862915, 30246994, 72347634115, 29985874, 29723794, 127054677011, 133, 197, 261, 26544206] : List ℕ).getD ((0xc57efe0c17efe1c37efe0c17efde2976e5bb566c57ad56a53a546815293e74d992e549911e345890e105670603f7cf5e3b74e5c376cd5a1566c98b05eb96ac56a94a84e992a4288d121407cf1d386cd19305cb15284c911203c70d182c509101c3050800080040008006000800400080 >>> (7*s))%128) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [57925920, 127797387, 63927297, 60117131, 66059264, 63928395] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
    · refine ⟨fun s => ([0, 4, 8, 20, 16, 22612046, 12, 18434126, 1515545182467, 525, 2292650098947, 13994066, 465, 13731926, 469, 537, 28, 201, 197, 389, 34180102, 24, 265, 261, 325, 29970438, 26264586, 133, 26544206] : List ℕ).getD ((0xe6f7296f77bef7296f78c6f7296f77bef7296f739ef7296f77bef7296f78c6f7296f77bef7296f7a65ed74ded7bdaf8bdaf8c5ed7c5ed7bdaf9108427ded74ded5bdaf8bdaf5c5ed7c5ed518c63108424ca329465364a329465374a329465364a30946509ca32946549ca32318c69ca32210849ca30318c660020780207002068020600205802050020100204802040020380203002028020200201802010020 >>> (5*s))%32) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 16, 8, 24, 4, 12, 265, 201, 2030602159107, 325, 20, 389, 2032874840067, 1160137425031, 453, 28, 12917058, 17094978, 21598402, 2305462227275, 2287275725195, 25776322, 2304455594315, 2288282358155, 457, 517, 1790066151755, 1514181611915, 1789059518795, 1515188244875, 521, 25775122, 5346318, 333, 337, 397, 26544206] : List ℕ).getD ((0x9091ce1c91a11891e21c98402611e11e21a21a11e11cb8c02c91e31c91a11891e21c98402611c41e21841a11c41e07c03891d91c919e1891de1c978024b1d91cb19d18b1dc1cb5402c91d91c919b1891da1c94802591c41d11841901c40c30c06491ce1c91981891d81c960024b1ce1cb19718b1d61cb5402c91ce1c91941891d31c948024e1c41d11841901c43cf3c03891cd1c21821851c51c230024b0411c20421850451c20402c928a1c22821852851c22802480441c20441850440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 8, 12, 16, 2326006350151, 1445824315599, 393, 4, 24, 8736962, 197, 261, 325, 453, 28, 20, 4248842, 4265162, 10309830, 4280522, 10294470, 10278150, 473, 517, 10571974, 10556614, 10540294, 537, 4804802, 201, 265, 329, 9767942, 26544206] : List ℕ).getD ((0x84a74a29d28b2ca74a29d28c30a74a29d28b2ca74a29d2a018d74075d78079e74075d7c07df74075d78079e74074f70034a18a28b28b2ca2ca28c28c30a30a28b28b2ca2ca2972081976c01976801976401974c019760019744019740018f2005ca18a28b28b2ca2ca28c28c30a30a28b28b2ca2ca28d38e18d58018d54018d50018d4c018d48018d44018d40018f38034a18728b2872ca2c728c28730a30728b2872ca2c72892071851000410400820800410400c30c0041040082080041040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 16, 8, 20, 4, 12, 325, 26608670, 24, 201, 389, 656615952395, 10330118, 28, 1692439793675, 14769158, 2032874840075, 461, 571601685515, 1771755078155, 453, 913177641995, 265, 401, 34441234, 5380106, 393, 517, 1433605899275, 269, 337, 521, 29969426, 5362702, 333, 22597642, 2275398211595, 1239573387275, 608103043595, 26544206] : List ℕ).getD ((0x9c624a2465a258625e2468801a226225e59e5a22622575c028625724659758625e24678019e25e25e59e5a62652648c050624a24676274625e2468801a224425e74476224426180028625b24675f74620824620019e2440c30c475c2040c30c06c624a24659a58624a24668018a24a25459158a24a34d34028625724258258625924260019704124204259504134204050624a2464d244524524540018a24424f38418524434534028624c2422c22852052422001870440c20441850440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 16, 2326006350163, 24, 5573762, 9768002, 610502, 13961282, 872582, 872522, 22612046, 18139202, 1133702, 1133642, 26544206, 1132622, 26545226, 26545286, 22071362, 1379462, 1379402, 26298446, 1378382, 26299466, 26299526, 21039182, 26038346, 26038406, 25776326, 473, 20, 22874190, 30738510, 30739530, 30739590, 30492750, 30493770, 30493830, 30232650, 30232710, 29970630, 28, 537, 23136334, 34932814, 34933834, 34933894, 34687054, 34688074, 34688134, 34426954, 34427014, 34164934, 22070282, 133, 197, 261, 325] : List ℕ).getD ((0x479e7aeb9e7bef9e7aeb9e7cf39e7aeb9e7bef9e7aeb9e7882592b8eaa5c8a89d99975958e59128d03ce88c2ca2481e18144df45e75c35b6996175954544d24503ce34c2ca2481c6b71c37bf6d5cbb4cd9c97595bf1c12bd03ceb8c2ca2481e1b544df45e75c35b6996175954544d24503ce34c2ca2481ec82592b8eaa5c8a89d99975958e59128d03ce88c2ca2481e18144df45e75c35b6996175954544d24503ce34c2ca2481c61400400800400c00400800401000400800400c0040080040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 20, 8, 2326077932559, 4, 2326077686799, 12, 1153766605831, 2326069822479, 1153762673671, 1153762182151, 16, 2325881077839, 2325881078799, 1153636844551, 1153636353031, 2326069821519, 1153624556551, 2326077685839, 2326077931599, 1153766605843, 389, 24, 1445824318479, 2326006354951, 1445823089679, 2326006109191, 1152692865031, 2028651446787, 1445799496719, 2325998244871, 1152688932871, 2028647514627, 1152688441351, 2028647023107, 2319438633039, 22613126, 1445359094799, 2325809501191, 1152563103751, 2028521685507, 1152562612231, 2028521193987, 2319627376719, 18435206, 1152550815751, 2028509397507, 2319635241039, 14241926, 2319635486799, 10047686, 453, 1413612063759, 2309900227591, 1413610834959, 2309899981831, 1120480610311, 1948120809987, 1413587241999, 2309892117511, 1120476678151, 1948116877827, 1120476186631, 1948116386307, 2206695741519, 22875270, 1413146840079, 2309703373831, 1120350849031, 1947991048707, 1120350357511, 1947990557187, 2206884485199, 18697350, 1120338561031, 1947978760707, 2206892349519, 14504070, 2206892595279, 10309830, 28, 2307752745991, 640517934159, 2307752500231, 640516459599, 1428571820547, 34461770, 2307744635911, 640488934479, 1428552159747, 34723914, 1428550685187, 34723918, 30772370, 31000654, 2307555892231, 639985617999, 1428174672387, 34986058, 1428173197827, 34986062, 30510230, 31017038, 1428145672707, 34986066, 30249110, 31017042, 29987030, 31018066, 517, 640517950479, 1794504152071, 640516721679, 1794503906311, 347386497031, 401932583427, 640493128719, 1794496041991, 347382564871, 401928651267, 347382073351, 401928159747, 145111439439, 23137414, 640052726799, 1794307298311, 347256735751, 401802822147, 347256244231, 401802330627, 145300183119, 18959494, 347244447751, 401790534147, 145308047439, 14766214, 145308293199, 10571974, 1792356670471, 1413612047439, 1792356424711, 1413610572879, 913175745027, 30283850, 1792348560391, 1413583047759, 913156084227, 30545994, 913154609667, 30545998, 34966674, 35194958, 1792159816711, 1413079731279, 912778596867, 30808138, 912777122307, 30808142, 34704534, 35211342, 912749597187, 30808146, 34443414, 35211346, 34181334, 35212370, 1744038288391, 1445824302159, 1744038042631, 1445822827599, 864857362947, 26090570, 1744030178311, 1445795302479, 864837702147, 26352714, 864836227587, 26352718, 34983058, 35457102, 1743841434631, 1445291985999, 864460214787, 26614858, 864458740227, 26614862, 34720918, 35473486, 864431215107, 26614866, 34459798, 35473490, 34197718, 35474514, 2326006354963, 1446898042959, 201, 1446896568399, 5119370, 265, 1446869043279, 5381514, 5381518, 329, 1446365726799, 5643658, 5643662, 5643666, 26544206] : List ℕ).getD ((0xd015c46bc469c7cfc765c4cec4cdcbcccb5dc4cac4c9c7c8c7c6c4c5c4c3c2001533c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a601003315a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a1600156d898887868584838281807f7e7d7c7b7a797877767574737271706f6e01006d156c6b6a696867666564636261605f5e5d5c5b5a595857565554535251500015334f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534010033153231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a1918171600151413041202110410060f040e020d040c0b0a04090208040706050403020100 >>> (8*s))%256) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [4154330304, 8116958209, 4086633664, 16233924755, 8387558400] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · refine ⟨fun s => ([0, 4, 8, 12, 41908496532483, 20, 25776326, 25514186, 597, 16, 21598406, 21336266, 601, 38411270, 453, 457, 28, 34719822, 34457682, 605, 32, 5804226, 9982146, 14747714, 18925634, 5542082, 9720002, 517, 24, 30541902, 30279762, 609, 14485570, 18663490, 38900750, 333, 337, 397, 201, 197, 261, 18662410, 133, 18924554, 21564422, 26544206] : List ℕ).getD ((0xb6aaa79eaaa8a2aaa79eaaa38e79a79e69e8a279a79e69e59679a79e69e8a279a79e69e38e79a79e69e8a279a79e69ec3aaaa79eaaa8a2aaa79eaa9b2279a79e69e8a279a79e69e93279a79e69e8a279a79e69e92279a79e69e8a279a771c71c6eaaa79eaaa8a2aaa79eaa8e2279a79e69e8a279a79e69eb3279a79e69e8a279a79e69eb2279a79e69e8a279a74104103aaaa79eaaa8a2aaa79eaaa92279899e69c9a279899e69c93279859e69c5a279859e69c52279899e69c9a2798971c70920e3ce8e38e39249248e38d48e38e39249248e38e39659549659658e38e39249248e38d48c00409000408c004088004038f39b38f39b38f39b38f39431f7df31e7a131d76031a65421f7df21e7a121d7602165547c00407800407400407000406ce3ce6ce3ce6ce3ce6ce3d43134d331249831145731a6542134d32124982114572165544c004048004044004040004038f38d0820820c30c308208230b2890820820c30c30820822071850820820c30c30820821000400800400c0040080040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 8, 12, 16, 38410270, 6184986, 393, 4, 28, 24, 457, 8443142, 8459462, 5853386, 8474822, 5838026, 5821706, 537, 20, 6115530, 6100170, 6083850, 541, 8736962, 197, 261, 325, 517, 32, 4248842, 4265162, 10571974, 4280522, 10556614, 10540294, 13128962, 17323202, 21516482, 581, 10834118, 10818758, 10802438, 601, 4804802, 201, 265, 329, 9767942, 26544206] : List ℕ).getD ((0xc18b1862c619658b1862c61a698b1862c619658b1862c62f19bb2cb2cb6db6db2cb2cbaebaeb2cb2cb6db6db2cb1229229bb2cb2cb6db6db2cb2cbaebaeb2cb2cb6db6db2cb0918919bb00b2cb40b6db00b2cb80baeb00b2cb40b6db00b12ac06d819861961965865861a61a6986986196196586586262081962961a62a91a62a81a62a51a62a71a62a41a62a31922122911912a61a92a61a82a61a52a61a72a61a42a61a32892091a6a801a6a401a6a001a68001a69c01a67801a674019220099819861961965865861a61a69869861961965865861b71c19b29119b2a219b2a119b2a519b29f19b2a419b2a319271229b19629b1a229b1a129b1a529b19f29b1a429b1a328970919b44019b88019b84019b80019b7c019b78019b7401927006d818761960765864761a60769868761960765864761720719628719528719428718e28719328718c28718b28719220729118729018728f18728e18728d18728c18728b1872892071851000410400820800410400c30c0041040082080041040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 35496982, 27041798, 405, 469, 23124998, 461, 31507466, 453, 23140362, 393, 401, 27330566, 16, 28, 32, 517, 27071502, 333, 337, 20, 24, 22875142, 22597642, 597, 11088838809607, 261, 11121027548167, 201, 133, 197, 30458890, 265, 18924554, 269, 26019846, 26544206] : List ℕ).getD ((0x9e082186081d7608218608155617e185f85d7617e185f84d36081f7e081d76081f7e081555d7df7df8dd7637df7df7662e082186081d7608218608155617e185f85d7617e185f8621a081f7d78177606187d761755d7df7d79577656187d76174e082186081d76082186080d1a17d085f8507617d045145036081f7e081d76081f7e082435d7d07df8d07637d04514502e082186081d7608218608221a17d085f8507617d04514501a081f7d78177606187d76176dd7d07d779075c6104576106cb34d55555559659655555255555559659655555538e35234d38e5555555965965555525405405805805405403406802c92c95555555965965555525550415960415550411990411871935575575966185576175400405800405400405000404cb34d24b34d38e34d38e35218b35018b35038e35045145034d38e08208234d18f0820823403800800803403000800802c92c92c72ca0c30c30c30c31890411880410c30410c30411871850820820c30c30820821000400800400c0040080040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 12, 8, 24, 4, 12948738, 261, 16, 201, 325, 20, 389, 4874690, 10886150, 453, 28, 4266318, 4282638, 14521606, 4297998, 14506246, 14489926, 457, 517, 14783750, 14768390, 14752070, 521, 32, 35246166, 34984026, 34722906, 581, 15045894, 15030534, 15014214, 585, 39440470, 39178330, 38917210, 39456854, 39194714, 38933594, 5084418, 14241798, 269, 333, 397, 26544206] : List ℕ).getD ((0xc0620e206b401ad22d209b8024622e206b401ad22d20bbc02c622f206b401ad22d209b8024622e206b401ad20422cac03862172066c0189217209a80246217206a4018b21720b4c02c6217206a001892172094402462172064001972040c30c05c620e20658018920e2099c024620e20698018b20e20b4c02c620e20694018920e20944024620e20640018e2043cf3c03862202069001892202098c024622020688018b22020b4c02c62202068401892202094402462202064001a02040c30c080620e20658018920e2097c024620e20678018b20e20b4c02c620e20674018920e20944024620e20640018e20471c7003862172066c018921720968024621720664018b21720b4c02c62172066001892172094402462172064001972040c30c05c620e20658018920e20954024620e20650018b20e20b4c02c620e20648018920e20944024620e20640018e2043cf3c038620d2023001890412020402461c72021c018b0412020402c628a2022801890412020402461c72021c01850440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 4, 8, 12, 16, 41908496532491, 24, 5573762, 9768002, 610502, 13961282, 872582, 872522, 22612046, 18139202, 1133702, 1133642, 26544206, 1132622, 26545226, 26545286, 22071362, 1379462, 1379402, 26298446, 1378382, 26299466, 26299526, 21039182, 26038346, 26038406, 25776326, 473, 20, 22874190, 30738510, 30739530, 30739590, 30492750, 30493770, 30493830, 30232650, 30232710, 29970630, 28, 537, 23136334, 34932814, 34933834, 34933894, 34687054, 34688074, 34688134, 34426954, 34427014, 34164934, 32, 601, 23398478, 39127118, 39128138, 39128198, 38881358, 38882378, 38882438, 38621258, 38621318, 38359238, 22070282, 133, 197, 261, 325] : List ℕ).getD ((0x23162c68d162c78f162c68d162c891162c68d162c78f162c68d162c4409522b46a949c44a13994c5cb154695212464078e443058a12203a1405099f2278e9c1a6cd19305cb152250992224078e1a3058a12203865ac58375ed9a9c5cd1999645cb155ec58125e4078e5c3058a12203a15a5099f2278e9c1a6cd19305cb152250992224078e1a3058a12203ac409522b46a949c44a13994c5cb154695212464078e443058a12203a1405099f2278e9c1a6cd19305cb152250992224078e1a3058a122038672f5e43770a09c7501f997c5cb1576f5e12764078e743058a12203a1725099f2278e9c1a6cd19305cb152250992224078e1a3058a12203b8409522b46a949c44a13994c5cb154695212464078e443058a12203a1405099f2278e9c1a6cd19305cb152250992224078e1a3058a12203865ac58375ed9a9c5cd1999645cb155ec58125e4078e5c3058a12203a15a5099f2278e9c1a6cd19305cb152250992224078e1a3058a12203ac409522b46a949c44a13994c5cb154695212464078e443058a12203a1405099f2278e9c1a6cd19305cb152250992224078e1a3058a12203860a000800400080060008004000800800080040008006000800400080 >>> (7*s))%128) 0, ?_⟩
      decide +kernel
  · intro p hp
    change p ∈ [2094048417867, 20072748419211, 4277382612043] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · refine ⟨fun s => ([0, 20, 8, 28, 4, 12, 19488130, 16, 389, 23666050, 517, 35554330, 24, 10278146, 14456066, 453, 42588242, 42850386, 42588246, 42850390, 31884322, 10016002, 14193922, 42572882, 42835026, 42572886, 42835030, 27690018, 36, 521, 525, 39192590, 38930446, 11165702, 32, 19221634, 43147338, 43147342, 39748634, 23399554, 43409482, 43409486, 581, 27650114, 30054498, 30316642, 44161106, 39454802, 39455826, 44161110, 39454806, 39455830, 31828034, 25861218, 26123362, 44145746, 39716946, 39717970, 44145750, 39716950, 39717974, 585, 18959490, 43131978, 43131982, 23137410, 43394122, 43394126, 27387970, 30054502, 30316646, 44423250, 35276882, 35277906, 44423254, 35276886, 35277910, 31565890, 25861222, 26123366, 44407890, 35539026, 35540050, 44407894, 35539030, 35540054, 30248982, 29986838, 19519494, 401, 405, 465, 645, 43277698, 269, 265, 665, 329, 43015554, 673, 42832022, 42569942, 42833042, 42570962, 42848406, 42586326, 42849426, 42587346, 23136270, 201, 39193746, 38931606, 23398414, 39725146, 39463006, 35015826, 34753686, 35547226, 35285086, 26038282, 26544206] : List ℕ).getD ((0xf02368ada2af8abe236d9db670d9c2236dadb6afdabe236d9db66c801166fd9bd66fd9bf6af5abf6b0dac366fd9bd66fd9be3ef5bbf6ed801e22fdbbd6efdbbe22f59bf670d9c222fdabd6afdabe22f59bf66c801166fd9bd66fd9bf6af5abf6b0dac366fd9bd66fd9bf82f57bf5bb80142369eda76faabe2369eda770bdc22369eda76fbdbe2369eda75e80103efaabcaafaabe3ef76bfdb0f6c23eff6bddaff6be3ef76bfdb6001e22faabcaafaabe22f75bfd70f5c222ff5bdd6ff5be22f75bfd760010aafaabcaafaabf82f74bfd30c1c382ff3bdcefbe060c183060c180542368ada2af8abe2369dda7b09dc22369dda7af9dbe2369dda78e80103ef8abc2af8abe3ef72bfcb0f2c23eff2bdcaff2be3ef72bfcb8001e22f8abc2af8abe22f71bfc70f1c222ff1bdc6ff1be22f71bfc7800102af8abc2af8abf82f6fbfbf0a7c382feebdbafa344891224489100142369eda76fe3be2369eda770a0c22369eda76f9fbe2369eda77600103efe3bd8c081be3ef6bbfa8081c23efe9bda0081be3ef16be540801e22fe3bd8c60cbe22f67bf9860cc222fe5bd9060cbe22f0ebe346001172fe3bd8c081bf82f62bf88081c382fddbd74081060c183060c080b820e8a3c28e8ab222cd9b366cd9b422d5ab56ad5ab222cd9b364e001166cd9b366cd9116ad5ab56ad5a1166cd9b366cd9103eddbb76ce001e22ddbb76eddbb222cd9b366cd9b422d5ab56ad5ab222cd9b364e001166c84b20ac84116ad04b40ad041166c84b20ac841162b84ac08e00142051e147452a3a20f1e3a75ebd3a20f1e3a75ebd3a20f1e3a74e00103c52a14a852a103eacda9369cd103e94da33684d103e7cd9d34e001e2052a14a852a1e2264497125441e224c491123c41e223448b10e0010a85041408504102e184840a084102e0047e09f04060c18406081805420e8a3c28e8a7a20e9d3c78e9d7a20e9d3c78e9d7a20e9d3c78e00103d50a542950a103de3476d1d34103dcb470d1bb4103db346ad0e001e2150a542950a1e219ab64ad8ab1e2182b5ead72b1e216ab58ace0010295045409504109948450093841099284480918444891044409100142051e14745213a14f053a150053a1cf073a1cf873a14f053a14e00103c51b146c0811014d053214085101cc072e1c0871014b052a140801e20514145060c1e1498524146051e1c887201c6071e147051a14600102c504140808410144841208084101c3040c0808406141840608080 >>> (7*s))%128) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 16, 8, 24, 4, 12, 28, 31556630, 325, 20, 36, 389, 32, 31524878, 201, 265, 36324382, 453, 333, 40502294, 517, 401, 44418074, 465, 581, 337, 31622166, 43648022, 44107790, 42846226, 32080918, 645, 397, 35537946, 589, 38930446, 39945238, 39175194, 31787022, 26544206] : List ℕ).getD ((0x9c83913883d23c83993884802123923993d93d239238b8002c83a03883d23c83993884802123843993c43d23843975c04483973883e03c83993886402193993993d93cb39538b8002c83a03883d53c83993886402193843993c43e03843a28805083913883d23c83993884802123923993d93d239238b8002c83a03883d23c83993884802123843993c43d23843a28804483983883e03c83993886402193990c30c33cb39f0c30c02c83a03883d81861861861802193840c30c41861840c30c06083913883d23c839538848021239238b3e03d239238b8002c83a03883d23c83a03884802123843953c43d23843975c04483973883e03c839538880020b04138b0413cb04138b0402c83a03883d53c83a03889802200443950443e00443a50405083913883d23c538538548021239238b3e03c53853858002c83a03883d23c53853854802123843a43c43c53843858c04483a23883e03c538538580020b0410c30413c50450c50402c83a03883e11851851851802200440c30441850440c50407c83913883d23c83993884802123923993d93d239238b5402c83953883d23c83993884802123843993c43d23843975c04483973823c23c83993826402193993823c23cb3953825402c83953823c23c83993826402193843823c43de3843827405083913883d23c83993884802123923993d93d239238b7002c82493882493c82493882402122443992443d224439b2404483983823c23c83993826402193990c20c23cb39a0c20c02c82493822421862491822402192440c22441862440c22406083913883d23c839538848021239238b3d430c30c30c3002c839528a28a3c839128a28021238428a28430c30430c3004483973823c23c839538254020b04138204230c0413020402c83952822823c839628228021504428204430c0443020405083913883d23c538538548021239238b3d33053053053002c824928a2493c524528524021224428a2443052443052404483903823c23c538538234020b0410c20423050450c20402c82492822421852451822402070440c20441850440c2040 >>> (6*s))%64) 0, ?_⟩
      decide +kernel
    · refine ⟨fun s => ([0, 24, 8, 10047682, 4, 14241922, 12, 890122, 18435202, 1152202, 1152142, 16, 25513106, 22613122, 1413322, 1413262, 5852306, 1412242, 5853326, 5853386, 20, 26545286, 26545282, 1659082, 1659022, 5606546, 1658002, 5607566, 5607626, 22613126, 25250962, 5346446, 5346506, 18435206, 5084426, 14241926, 10047686, 44434462, 453, 28, 32137282, 22875270, 18697350, 14504070, 10309830, 30738510, 18713734, 14520454, 10326214, 31000654, 14521478, 10327238, 31017038, 10327302, 31017042, 31018066, 517, 36330562, 23137414, 18959494, 14766214, 10571974, 34932814, 18975878, 14782598, 10588358, 35194958, 14783622, 10589382, 35211342, 10589446, 35211346, 35212370, 32, 2270302, 42622050, 42884194, 38673482, 43146338, 38935626, 38935630, 35457102, 43408482, 39197770, 39197774, 35473486, 39197778, 35473490, 35474514, 43670626, 39459914, 39459918, 35489870, 39459922, 35489874, 35490898, 39459926, 35489878, 35490902, 35491926, 581, 40508482, 23399558, 19221638, 15028358, 10834118, 39127118, 19238022, 15044742, 10850502, 39389262, 15045766, 10851526, 39405646, 10851590, 39405650, 39406674, 2531422, 11164770, 15359074, 34495562, 19553378, 34757706, 34757710, 39651406, 23747682, 35019850, 35019854, 39667790, 35019858, 39667794, 39668818, 27941986, 35281994, 35281998, 39684174, 35282002, 39684178, 39685202, 35282006, 39684182, 39685206, 39686230, 2530402, 11165790, 15360094, 30302282, 19554398, 30564426, 30564430, 39913550, 23748702, 30826570, 30826574, 39929934, 30826578, 39929938, 39930962, 27943006, 31088714, 31088718, 39946318, 31088722, 39946322, 39947346, 31088726, 39946326, 39947350, 39948374, 36, 44440650, 44440654, 39962702, 44440658, 39962706, 39963730, 27085970, 44440662, 39962710, 39963734, 31018130, 39964758, 31019150, 31019210, 44440666, 39962714, 39963738, 30772370, 39964762, 30773390, 30773450, 39965786, 30512270, 30512330, 30250250, 645, 44440642, 23661702, 19483782, 15290502, 11096262, 43321422, 19500166, 15306886, 11112646, 43583566, 15307910, 11113670, 43599950, 11113734, 43599954, 43600978, 2777182, 10919010, 15113314, 34511946, 19307618, 34774090, 34774094, 43845710, 23501922, 35036234, 35036238, 43862094, 35036242, 43862098, 43863122, 27696226, 35298378, 35298382, 43878478, 35298386, 43878482, 43879506, 35298390, 43878486, 43879510, 43880534, 2776162, 10920030, 15114334, 30318666, 19308638, 30580810, 30580814, 44107854, 23502942, 30842954, 30842958, 44124238, 30842962, 44124242, 44125266, 27697246, 31105098, 31105102, 44140622, 31105106, 44140626, 44141650, 31105110, 44140630, 44141654, 44142678, 40508490, 40508494, 44157006, 40508498, 44157010, 44158034, 40508502, 44157014, 44158038, 44159062, 40508506, 44157018, 44158042, 44159066, 44160090, 42097762, 10658910, 14853214, 30319690, 19047518, 30581834, 30581838, 44369998, 23241822, 30843978, 30843982, 44386382, 30843986, 44386386, 44387410, 27436126, 31106122, 31106126, 44402766, 31106130, 44402770, 44403794, 31106134, 44402774, 44403798, 44404822, 36330570, 36330574, 44419150, 36330578, 44419154, 44420178, 36330582, 44419158, 44420182, 44421206, 36330586, 44419162, 44420186, 44421210, 44422234, 32137290, 32137294, 44435534, 32137298, 44435538, 44436562, 27348114, 32137302, 44435542, 44436566, 35212434, 44437590, 35213454, 35213514, 32137306, 44435546, 44436570, 34966674, 44437594, 34967694, 34967754, 44438618, 34706574, 34706634, 34444554, 26544142, 201, 44436638, 265, 44437662, 329, 44438686, 393, 44439710, 26544206] : List ℕ).getD ((0xb109ab4b7ad2dab8c2ae2d2b4c1ad302bc1eaf2c2b4bead2f6b81aae2eeb418ad586c016b02d2b4b7ad2dab811ae2d2b40fad57ebc0daf2c2b40aad576b808ae56eb405ad00eb200130e0914d23d31515822d294f575355aaa1e21519495451d4ea41a50d46a018a785e9c161f5293b4d4e53296114d52a920fa403a8e0d4b51a8a0aa20268608a101e8205a000c02001c0986eb71b2d91cc21a2d11ac1463027e1e18ac114be44af67c1a43aee7a189e05e761616ad106b7412da7411402d2720f9c03a6e0d3e2c26c0a9a82668089981e64059880c4e0013190e91739c5e611738c5e5f179745e5b173745e591795c5e551794c5e511793c5e4d173545e4b179245e47179145e43179045e3f178f45e3b178e45e37178d45e33178c45c0200320986eb71b2d8c6c21a2d0c4c130b022c1e18ac0bebe2f2f62a1a2e2ee28188985e241616ad0b0b72bada22112aad2200f8783a1c0d28ac21a0a8602616088501e12058400c9200130e090ee23bba0eee22bba0cee82bba08ee213ba06ee813ba02ee803b9feee7f3b9faee1f3b9f8ee7dbb9f4ee7cbb9f0ee7bbb9ecee7abb9e8ee79bb9e4ee78bb9e0ee77bb802001c0986ed41b351dad41a351d8d475b51d4d418b51d2d474351ced473351cad472351c6d416b51c4d470b51c0d46fb51bcd46eb51b8d46db51b4d46cb51b0d46bb51acd46ab504e001330da6c469311a2c4683119ec4673103cc466b1198c465b1034c46531030c40bb102cc464b1190c463b1022c4633101ec4073101ac462b1014c404b1010c403b100ac401b100200618986eb71b2d8c6c21a2d0c4c130b017e1e18ac0bebe2f2f5781a2e2ed74185c85d701616ad0b0b72bad96a112aad1660f59039620d28ac15e0a570255a085601d56055500d5200130e0908f23a3d508f22a3d4e8f5323d4a8f2123d488f51a3d448f50a3d408f4fa3d3c8f1f23d3a8f4e23d368f4d23d328f4c23d2e8f4b23d2a8f4a23d268f4923d228f4823c02001c0986e751b1d51c751a1d51a75461d51675189d51475449d51075439d50c75429d50875169d50675411d50275401d4fe753f1d4fa753e1d4f6753d1d4f2753c1d4ee753b1d44e0013190e86539994e46538994e065379943c6537194da653619434653599430650b9942c6535194d265341942265339941e65071941a65331941465049941065039940a65019940200320986e4a1b128c64a1a128c44a30928c04a18928be4a2f128ba4a2e128b64a2d128b24a16928b04a2b928ac4a2a928a84a29928a44a28928a04a279289c4a26928984a259289200130e09039238e48c39228e48839218e43c39210e48239200e434391f8e430390b8e42c391f0e47a391e0e422391d8e41e39070e41a391d0e41439048e41039038e40a39018e402001c0986e281b0a06a281a0a06628190a03c28188a06028178a03428170a030280b8a02c28168a05828158a02228150a01e28070a01a28148a01428048a01028038a00a28018a04e001309448041180844041081840040f8083c040e82c38040d80834040c81830040b8082c040a8502604090082204080181e04070081a040602c1404048081004038180a04018080200 >>> (9*s))%512) 0, ?_⟩
      decide +kernel

end BBHFinite

open Finset SimpleGraph
namespace SmallCover.Seven

theorem seven_connected_cut {V : Type*} {G : SimpleGraph V} (h : G.Connected)
    (b : V → Bool) (h0 : ∃ i, b i = false) (h1 : ∃ i, b i = true) :
    ∃ i j, G.Adj i j ∧ b i ≠ b j := by
  classical
  by_contra! hsame
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  have along {i j : V} (w : G.Walk i j) : b i = b j := by
    induction w with
    | nil => rfl
    | cons he _ ih => exact (hsame _ _ he).trans ih
  obtain ⟨w⟩ := h.preconnected u v
  simpa [hu, hv] using along w

/-- Encode the edge set in the triangular positions of the binary expansion. -/
theorem encoding_spec {n : ℕ} (A : SimpleGraph (Fin n)) :
    ∃ x : ℕ, x < 2^n.choose 2 ∧
      (∀ i j : Fin n, i<j → (x.testBit (j.val.choose 2+i.val)=true ↔ A.Adj i j)) ∧
      A.edgeSet.ncard = ((Finset.range (n.choose 2)).filter fun i => x.testBit i).card := by
  let addr (i j : ℕ) := j.choose 2 + i


  have addr_lt_next {i j : ℕ} (h : i < j) : addr i j < (j+1).choose 2 := by
    change j.choose 2 + i < (j+1).choose 2
    rw [Nat.choose_succ_succ' j 1, Nat.choose_one_right]
    change j.choose 2+i < j+j.choose 2
    omega

  have addr_inj {i j k l : ℕ} (h : i<j) (h' : k<l) (e : addr i j = addr k l) :
      i=k ∧ j=l := by
    have row : j=l := by
      rcases lt_trichotomy j l with hj | hj | hj
      · have x := (addr_lt_next h).trans_le (Nat.choose_le_choose 2 hj)
        unfold addr at e x
        omega
      · exact hj
      · have x := (addr_lt_next h').trans_le (Nat.choose_le_choose 2 hj)
        unfold addr at e x
        omega
    subst l
    exact ⟨Nat.add_left_cancel e,rfl⟩

  let upperEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
    classical exact univ.filter fun p => p.1 < p.2 ∧ G.Adj p.1 p.2

  let edgeIndices {n} (G : SimpleGraph (Fin n)) : Finset ℕ :=
    (upperEdges G).image (fun p => addr p.1 p.2)

  let encode {n} (G : SimpleGraph (Fin n)) : ℕ :=
    ∑ a ∈ edgeIndices G, 2 ^ a

  have upperEdges_mem {n} {G : SimpleGraph (Fin n)} {p : Fin n × Fin n} :
      p ∈ upperEdges G ↔ p.1<p.2 ∧ G.Adj p.1 p.2 := by
    classical simp [upperEdges]

  have bit_iff_mem {n} (G : SimpleGraph (Fin n)) (a : ℕ) :
      (encode G).testBit a = true ↔ a ∈ edgeIndices G := by
    rw [← Nat.mem_bitIndices, ← List.mem_toFinset]
    simp [encode]

  have encode_bit {n} (G : SimpleGraph (Fin n)) {i j : Fin n} (h : i<j) :
      (encode G).testBit (addr i j) = true ↔ G.Adj i j := by
    rw [bit_iff_mem]
    constructor
    · intro hm
      obtain ⟨⟨a,b⟩, hab, eq⟩ := mem_image.mp hm
      obtain ⟨lo, adj⟩ := upperEdges_mem.mp hab
      obtain ⟨e₁,e₂⟩ := addr_inj lo h eq
      rwa [← Fin.ext e₁, ← Fin.ext e₂]
    · intro hij
      exact mem_image.mpr ⟨(i,j), upperEdges_mem.mpr ⟨h,hij⟩, rfl⟩

  have indices_in_range {n} (G : SimpleGraph (Fin n)) : edgeIndices G ⊆ range (n.choose 2) := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr ((addr_lt_next (upperEdges_mem.mp hp).1).trans_le
      (Nat.choose_le_choose 2 p.2.isLt))

  have encode_lt {n} (G : SimpleGraph (Fin n)) : encode G < 2 ^ n.choose 2 := by
    have h : ∀ t : ℕ, (∑ k ∈ range t, 2 ^ k) + 1 = 2 ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [sum_range_succ, pow_succ]; omega
    have b := Finset.sum_le_sum_of_subset_of_nonneg (indices_in_range G)
      (f := fun k => (2:ℕ)^k) (fun _ _ _ => Nat.zero_le _)
    change (∑ k ∈ edgeIndices G, 2 ^ k) < _
    have := h (n.choose 2)
    omega

  have edgeIndices_card {n} (G : SimpleGraph (Fin n)) : (edgeIndices G).card = (upperEdges G).card := by
    apply card_image_of_injOn
    intro a ha b hb e
    obtain ⟨e₁,e₂⟩ := addr_inj (upperEdges_mem.mp ha).1 (upperEdges_mem.mp hb).1 e
    exact Prod.ext (Fin.ext e₁) (Fin.ext e₂)

  have upperEdges_card {n} (G : SimpleGraph (Fin n)) : (upperEdges G).card = G.edgeSet.ncard := by
    classical
    let f (p : Fin n × Fin n) := s(p.1,p.2)
    have img : (upperEdges G).image f = G.edgeFinset := by
      ext x
      induction x using Sym2.inductionOn with
      | _ a b =>
        constructor
        · intro h
          obtain ⟨p,hp,e⟩ := mem_image.mp h
          rw [← e]
          exact (SimpleGraph.mem_edgeFinset.mpr (upperEdges_mem.mp hp).2)
        · intro h
          have adj : G.Adj a b := by simpa using h
          rcases lt_trichotomy a b with lt|eq|gt
          · exact mem_image.mpr ⟨(a,b), upperEdges_mem.mpr ⟨lt,adj⟩,rfl⟩
          · exact (adj.ne eq).elim
          · exact mem_image.mpr ⟨(b,a), upperEdges_mem.mpr ⟨gt,adj.symm⟩,Sym2.eq_swap⟩
    have inject : Set.InjOn f (upperEdges G : Set _) := by
      rintro ⟨a,b⟩ ha ⟨c,d⟩ hc e
      have hab : a < b := (upperEdges_mem.mp ha).1
      have hcd : c < d := (upperEdges_mem.mp hc).1
      rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · rfl
      · exact (hab.not_gt hcd).elim
    calc
      _ = ((upperEdges G).image f).card := (card_image_of_injOn inject).symm
      _ = G.edgeFinset.card := congrArg Finset.card img
      _ = G.edgeSet.ncard := by rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]

  have encode_count {n} (G : SimpleGraph (Fin n)) :
      G.edgeSet.ncard = ((range (n.choose 2)).filter (fun i => (encode G).testBit i)).card := by
    have eq : (range (n.choose 2)).filter (fun i => (encode G).testBit i) = edgeIndices G := by
      ext i
      simp only [mem_filter, bit_iff_mem]
      exact ⟨And.right, fun h => ⟨indices_in_range G h,h⟩⟩
    rw [eq, edgeIndices_card, upperEdges_card]
  exact ⟨encode A, encode_lt A, fun _ _ h => encode_bit A h, encode_count A⟩

/-- A bitwise cover of the exact-cardinality layer supplies one mask disjoint from any encoded member. -/
theorem covers_spec (k q z : ℕ) (ms : List ℕ) (hz : z<2^k)
    (hq : ((Finset.range k).filter fun i => z.testBit i=true).card=q) :
    let join (w a b : ℕ) := a % 2^w ||| (b <<< w)
    let free : ℕ → ℕ → ℕ := Nat.rec (fun _ => 1) (fun k rec mask =>
      let low := rec mask
      join (2^k) low (if mask.testBit k then 0 else low))
    let exactSize : ℕ → ℕ → ℕ := Nat.rec (fun q => if q=0 then 1 else 0) (fun k rec q =>
      join (2^k) (rec q) (if q=0 then 0 else rec (q-1)))
    exactSize k q &&& ms.foldr (fun m acc => free k m ||| acc) 0 = exactSize k q →
      ∃ m ∈ ms, ∀ i < k, z.testBit i=true → m.testBit i=false := by
  intro join free exactSize verified
  have join_bit (width a b i : ℕ) :
      (join width a b).testBit i =
        if i < width then a.testBit i else b.testBit (i-width) := by
    by_cases h : i < width <;> simp [join,h,Nat.not_le.mpr, show (width ≤ i) ↔ ¬ i<width by omega]

  have free_zero (m : ℕ) : free 0 m = 1 := rfl
  have free_succ (k m : ℕ) : free (k+1) m =
      join (2^k) (free k m) (if m.testBit k then 0 else free k m) := rfl

  have size_zero (q : ℕ) : exactSize 0 q = (if q=0 then 1 else 0) := rfl
  have size_succ (k q : ℕ) : exactSize (k+1) q =
      join (2^k) (exactSize k q) (if q=0 then 0 else exactSize k (q-1)) := rfl

  let count (k x : ℕ) := ((Finset.range k).filter (fun i => x.testBit i = true)).card

  have count_succ (k x : ℕ) : count (k+1) x = count k x + (if x.testBit k then 1 else 0) := by
    classical
    by_cases h : x.testBit k <;> simp [count,Finset.range_add_one,Finset.filter_insert,h,Finset.mem_filter]

  have count_high (k t : ℕ) : count k (2^k+t) = count k t := by
    unfold count
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    constructor <;> rintro ⟨hi, bit⟩
    · exact ⟨hi, by rwa [Nat.testBit_two_pow_add_gt hi] at bit⟩
    · exact ⟨hi, by rwa [Nat.testBit_two_pow_add_gt hi]⟩

  have size_correct (k q z : ℕ) (hz : z < 2^k) :
      (exactSize k q).testBit z = true ↔ count k z = q := by
    induction k generalizing q z with
    | zero =>
      have e : z=0 := by simpa using hz
      subst z
      rw [size_zero]
      change ((if q=0 then 1 else 0) : ℕ).testBit 0 = true ↔ 0=q
      cases q <;> simp
    | succ k ih =>
      rw [size_succ,join_bit,count_succ]
      by_cases low : z < 2^k
      · simp only [if_pos low, Nat.testBit_lt_two_pow low, Bool.false_eq_true, if_false, add_zero]
        exact ih _ _ low
      · have span : z < 2^k + 2^k := by simpa only [pow_succ,Nat.mul_two] using hz
        set t := z - 2^k
        have ht : t < 2^k := by dsimp [t]; omega
        have eq : z = 2^k+t := by dsimp [t]; omega
        have bit : z.testBit k = true := by rw [eq,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow ht]; rfl
        rw [if_neg low,bit,if_pos rfl,eq,count_high]
        by_cases hq : q=0
        · simp [hq]
        · rw [if_neg hq,ih _ _ ht]
          omega

  have free_correct (k m z : ℕ) (hz : z < 2^k) :
      (free k m).testBit z = true ↔ ∀ i < k, z.testBit i = true → m.testBit i = false := by
    induction k generalizing z with
    | zero =>
      have e : z=0 := by simpa using hz
      subst z
      rw [free_zero]
      simp
    | succ k ih =>
      rw [free_succ,join_bit]
      by_cases low : z < 2^k
      · rw [if_pos low,ih _ low]
        constructor
        · intro h i hi
          obtain hlt | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
          · exact h i hlt
          · simp [Nat.testBit_lt_two_pow low]
        · exact fun h i hi => h i (Nat.lt_succ_of_lt hi)
      · have span : z < 2^k + 2^k := by simpa only [pow_succ,Nat.mul_two] using hz
        set t := z - 2^k
        have ht : t < 2^k := by dsimp [t]; omega
        have eq : z = 2^k+t := by dsimp [t]; omega
        have bit : z.testBit k = true := by rw [eq,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow ht]; rfl
        rw [if_neg low]
        cases hm : m.testBit k with
        | true => simp only [if_true, Nat.zero_testBit, Bool.false_eq_true, false_iff]
                  exact fun h => by simpa [hm] using h k (by omega) bit
        | false =>
          simp only [Bool.false_eq_true,if_false]
          change (free k m).testBit t = true ↔ _
          rw [ih _ ht]
          constructor
          · intro h i hi hz'
            obtain hlt | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
            · exact h i hlt (by simpa only [eq,Nat.testBit_two_pow_add_gt hlt] using hz')
            · exact hm
          · intro h i hi ht'
            exact h i (Nat.lt_succ_of_lt hi) (by simpa only [eq,Nat.testBit_two_pow_add_gt hi] using ht')

  let union (k : ℕ) (ms : List ℕ) := ms.foldr (fun m rest => free k m ||| rest) 0

  have union_correct (k z : ℕ) (ms : List ℕ) (hz : z < 2^k) :
      (union k ms).testBit z = true ↔
        ∃ m ∈ ms, ∀ i < k, z.testBit i = true → m.testBit i = false := by
    induction ms with
    | nil => simp [union]
    | cons h t ih =>
      change (free k h ||| union k t).testBit z = true ↔ _
      simp [Nat.testBit_or, free_correct k h z hz, ih]

  have covers (k q z : ℕ) (ms : List ℕ) (hz : z < 2^k) (hq : count k z=q)
      (verified : exactSize k q &&& union k ms = exactSize k q) :
      ∃ m ∈ ms, ∀ i < k, z.testBit i = true → m.testBit i = false := by
    apply (union_correct k z ms hz).mp
    have bit := (size_correct k q z hz).mpr hq
    have test := congrArg (fun b : ℕ => b.testBit z) verified
    simpa only [Nat.testBit_and,bit,Bool.true_and] using test
  exact covers k q z ms hz hq verified

end SmallCover.Seven

open Finset SimpleGraph
namespace SmallCover.Six
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem placed6 (G : SimpleGraph (Fin 6)) (h : G.edgeSet.ncard ≤ 8) :
    ∃ e : Fin 6 ↪ Fin 6, ∀ i j, G.Adj i j →
      (541065248 : ℕ).testBit ((min (e i) (e j)).val*6+(max (e i) (e j)).val)=false := by
  obtain ⟨z,bound,bits,count⟩ := SmallCover.Seven.encoding_spec G
  let image (p : ℕ) (i : Fin 6) : Fin 6 := ⟨p / 6^i.val % 6, Nat.mod_lt _ (by decide)⟩
  let addr (i j : Fin 6) := j.val.choose 2+i.val
  let code (i j : Fin 6) := (min i j).val*6+(max i j).val
  let good (r : ℕ × ℕ) := decide (
    (∀ i j : Fin 6, i<j → image r.1 i ≠ image r.1 j) ∧
    ∀ i j : Fin 6, i<j → (541065248 : ℕ).testBit (code (image r.1 i) (image r.1 j))=true →
      r.2.testBit (addr i j)=true)
  let rs : List (ℕ × ℕ) := [(44790,17920),
    (34890,12296),
    (22830,352),
    (26340,2054),
    (22740,208),
    (21090,385),
    (17850,49),
    (35610,20482),
    (43705,10752),
    (41850,5124),
    (42160,3080),
    (16750,522),
    (19645,164),
    (6970,16449),
    (41590,9218),
    (16405,276),
    (43345,6400),
    (38305,24704),
    (24565,4640),
    (17530,13),
    (39625,18448),
    (22090,577),
    (7210,16456),
    (7285,16672),
    (4510,4162),
    (27040,1048),
    (34410,10241),
    (22165,644),
    (17910,50),
    (30685,8960),
    (43260,3200),
    (16270,137),
    (26965,8228),
    (16990,19),
    (21150,386),
    (34885,12304),
    (27060,2072),
    (22720,200),
    (20490,546),
    (43240,3136),
    (29665,16912),
    (42270,5152),
    (41820,3076)]
  have checked : rs.all good = true := by decide +kernel
  obtain ⟨d,hd,avoid⟩ := SmallCover.Seven.covers_spec 15 G.edgeSet.ncard z (rs.map Prod.snd)
    bound count.symm (by
      generalize eq : G.edgeSet.ncard = q at *
      interval_cases q <;> decide +kernel)
  obtain ⟨⟨p,d⟩,mem,rfl⟩ := List.mem_map.mp hd
  have ok := List.all_eq_true.mp checked (p,d) mem
  change decide (_ ∧ _) = true at ok
  obtain ⟨inj,placed⟩ := of_decide_eq_true ok
  let e : Fin 6 ↪ Fin 6 := ⟨image p, fun i j eq => by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact inj i j lt eq
    · exact inj j i gt eq.symm⟩
  refine ⟨e, ?_⟩
  have forward {i j : Fin 6} (lt : i<j) (edge : G.Adj i j) :
      (541065248 : ℕ).testBit (code (e i) (e j)) = false := by
    have rank : addr i j < 15 := by
      apply Nat.lt_of_lt_of_le _ (Nat.choose_le_choose 2 j.isLt)
      change j.val.choose 2 + i.val < (j.val+1).choose 2
      rw [Nat.choose_succ_succ' j.val 1,Nat.choose_one_right]
      change j.val.choose 2 + i.val < j.val + j.val.choose 2
      omega
    have absent := avoid (addr i j) rank ((bits i j lt).mpr edge)
    cases zbit : (541065248 : ℕ).testBit (code (e i) (e j)) with
    | false => rfl
    | true => have present := placed i j lt zbit; simp [absent] at present
  intro i j edge
  rcases lt_or_gt_of_ne edge.ne with lt|gt
  · exact forward lt edge
  · simpa only [code,min_comm (e j) (e i),max_comm (e j) (e i)] using forward gt edge.symm
end SmallCover.Six

open Finset SimpleGraph
namespace SmallCover.Seven
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 32000 in
theorem certified_rows (z : ℕ) (bound : z<2^21)
    (size : ((Finset.range 21).filter fun i => z.testBit i=true).card=11) :
    let addr (i j : ℕ) := j.choose 2+i
    let digit (p : ℕ) (i : Fin 7) : Fin 7 :=
      ⟨p / 7^i.val % 7, Nat.mod_lt _ (by decide)⟩
    let templateIndex (i j : Fin 7) := (min i j).val * 7 + (max i j).val
    let rowOK (r : ℕ × ℕ × ℕ) : Bool :=
      let (t,p,d) := r
      if t=0 then
        decide ((∃ i : Fin 7, p.testBit i=false) ∧ (∃ j : Fin 7, p.testBit j=true) ∧
          ∀ i j : Fin 7, i<j → p.testBit i ≠ p.testBit j → d.testBit (addr i j)=true)
      else
        decide ((t=8757838336 ∨ t=33688088) ∧
          (∀ i j : Fin 7, i<j → digit p i ≠ digit p j) ∧
          ∀ i j : Fin 7, i<j → t.testBit (templateIndex (digit p i) (digit p j))=true →
            d.testBit (addr i j)=true)
    ∃ r : ℕ × ℕ × ℕ, rowOK r = true ∧ ∀ i<21, z.testBit i=true → r.2.2.testBit i=false := by
  intro addr digit templateIndex rowOK
  let block0 : List (ℕ × ℕ × ℕ) := [
    (0,1,33867),
    (0,2,67733),
    (0,3,101598),
    (0,4,135462),
    (0,5,169325),
    (0,6,203187),
    (0,8,270904),
    (0,9,304755),
    (0,10,338605),
    (0,12,406302),
    (0,16,541632),
    (0,17,575371),
    (0,18,609109),
    (0,20,676582),
    (0,24,811512),
    (0,31,1047552),
    (0,32,1080320),
    (0,33,1112139),
    (0,34,1143957),
    (0,36,1207590),
    (0,40,1334840),
    (0,47,1557440),
    (0,48,1589184),
    (0,55,1811000),
    (0,59,1937702),
    (0,61,2001045),
    (0,62,2032715),
    (0,63,2064384),
    (8757838336,518295,592912),
    (8757838336,521991,1189896)]

  let block1 : List (ℕ × ℕ × ℕ) := [
    (8757838336,443451,925760),
    (8757838336,520479,398592),
    (8757838336,95859,16677),
    (8757838336,365877,459016),
    (8757838336,424311,1155200),
    (8757838336,485955,196760),
    (8757838336,220425,34853),
    (8757838336,768861,1053960),
    (8757838336,780927,544912),
    (8757838336,199059,149524),
    (8757838336,785961,151592),
    (33688088,161943,1581856),
    (8757838336,660933,1051268),
    (8757838336,644931,289024),
    (33688088,767733,22722),
    (8757838336,75063,20680),
    (33688088,396495,1836608),
    (8757838336,653151,84994),
    (33688088,44553,797312),
    (8757838336,398469,1836288),
    (8757838336,579573,672264),
    (33688088,778515,11841),
    (8757838336,499725,590853),
    (8757838336,483135,655374),
    (8757838336,330057,410128),
    (8757838336,597585,66242),
    (8757838336,63867,11780),
    (8757838336,436395,1712130),
    (8757838336,463983,1605896),
    (33688088,107091,328112)]

  let block2 : List (ℕ × ℕ × ℕ) := [
    (8757838336,363159,622864),
    (8757838336,661605,1057440),
    (8757838336,488721,394264),
    (8757838336,736227,132642),
    (8757838336,655941,1050661),
    (8757838336,229161,41608),
    (33688088,485763,1247280),
    (8757838336,669999,1050758),
    (8757838336,425265,1642560),
    (8757838336,131343,33301),
    (8757838336,94809,16946),
    (8757838336,616737,525457),
    (8757838336,607323,133131),
    (8757838336,793803,41226),
    (8757838336,435303,1837064),
    (8757838336,791463,139301),
    (33688088,473877,1708576),
    (33688088,111051,557649),
    (8757838336,83415,9285),
    (33688088,37581,414240),
    (33688088,712323,9432),
    (8757838336,131169,131595),
    (33688088,109887,590211),
    (8757838336,797685,528784),
    (8757838336,193899,155968),
    (8757838336,690621,266277),
    (33688088,578103,229700),
    (8757838336,594495,262545),
    (33688088,761391,26705),
    (8757838336,485871,196904)]

  let block3 : List (ℕ × ℕ × ℕ) := [
    (8757838336,60699,21640),
    (33688088,463653,852545),
    (8757838336,432909,1392648),
    (33688088,161199,1574472),
    (33688088,577305,426592),
    (8757838336,781263,545296),
    (33688088,520401,235521),
    (8757838336,99681,4657),
    (33688088,71811,1132804),
    (8757838336,61851,22020),
    (33688088,199407,1189908),
    (8757838336,197025,148483),
    (8757838336,109965,16737),
    (8757838336,95805,16462),
    (8757838336,689649,133133),
    (33688088,752571,9269),
    (8757838336,212001,278673),
    (8757838336,506085,399362),
    (8757838336,575655,296194),
    (8757838336,80223,17434),
    (8757838336,63939,14850),
    (8757838336,399951,1346048),
    (8757838336,766851,1073416),
    (8757838336,310059,575744),
    (33688088,716259,18864),
    (33688088,782145,19780),
    (8757838336,248751,197137),
    (33688088,254397,1085762),
    (8757838336,603513,65836),
    (8757838336,331005,114760)]

  let block4 : List (ℕ × ℕ × ℕ) := [
    (8757838336,435513,1839112),
    (8757838336,716439,33112),
    (33688088,338073,98694),
    (8757838336,716787,262929),
    (8757838336,500409,598036),
    (33688088,200151,1315874),
    (8757838336,107565,1250),
    (33688088,785961,7212),
    (33688088,344967,590424),
    (8757838336,577965,296128),
    (33688088,752955,6201),
    (8757838336,30165,1208),
    (8757838336,443211,827648),
    (8757838336,249579,98580),
    (33688088,167583,1180679),
    (8757838336,660591,1050820),
    (33688088,522009,1662992),
    (8757838336,766179,1067265),
    (8757838336,400653,1377408),
    (8757838336,598989,524844),
    (8757838336,61041,28808),
    (8757838336,570081,1311249),
    (8757838336,631995,536836),
    (33688088,573315,688389),
    (8757838336,170403,44036),
    (33688088,519681,435232),
    (33688088,494289,1261700),
    (8757838336,126513,33504),
    (8757838336,447285,835600),
    (33688088,572199,721072)]

  let block5 : List (ℕ × ℕ × ℕ) := [
    (8757838336,369279,720929),
    (8757838336,800025,147722),
    (8757838336,758241,1054753),
    (33688088,388851,1705218),
    (8757838336,535677,1197057),
    (8757838336,421983,1155074),
    (8757838336,798567,533124),
    (8757838336,199551,39041),
    (8757838336,80013,17449),
    (8757838336,717369,131843),
    (8757838336,432321,1261570),
    (33688088,781047,22280),
    (8757838336,92913,9025),
    (8757838336,365961,458888),
    (8757838336,563907,1573505),
    (8757838336,458865,1638468),
    (33688088,488409,1646736),
    (8757838336,169707,76832),
    (8757838336,648753,546848),
    (33688088,536121,1257488),
    (8757838336,91797,4560),
    (8757838336,503643,331908),
    (33688088,254439,1083585),
    (33688088,107103,295272),
    (33688088,798015,910),
    (33688088,511719,870912),
    (8757838336,288051,1091588),
    (8757838336,640107,273412),
    (8757838336,95817,16534),
    (33688088,774411,26129)]

  let block6 : List (ℕ × ℕ × ℕ) := [
    (8757838336,690531,264211),
    (33688088,584199,229425),
    (33688088,746919,19236),
    (8757838336,315573,352264),
    (8757838336,474315,393304),
    (33688088,584577,360492),
    (33688088,506943,836616),
    (8757838336,499551,561155),
    (33688088,785865,7209),
    (33688088,297627,1099968),
    (8757838336,87681,4280),
    (33688088,785487,13331),
    (33688088,112269,557254),
    (33688088,729435,20615),
    (8757838336,600063,524579),
    (8757838336,560517,1311496),
    (8757838336,109671,16993),
    (8757838336,718791,33050),
    (8757838336,126489,66272),
    (8757838336,74343,5320),
    (33688088,369195,1247235),
    (33688088,340473,590087),
    (8757838336,33105,1302),
    (8757838336,402375,1836048),
    (8757838336,228363,35201),
    (8757838336,331149,213280),
    (8757838336,658947,1056856),
    (8757838336,331143,180512),
    (8757838336,560553,1311504),
    (8757838336,517545,796704)]

  let block7 : List (ℕ × ℕ × ℕ) := [
    (8757838336,82797,10786),
    (33688088,467271,426012),
    (33688088,345831,164680),
    (8757838336,560763,1311392),
    (8757838336,489261,299011),
    (8757838336,714723,524897),
    (8757838336,442023,725056),
    (8757838336,573219,295941),
    (8757838336,484779,589846),
    (33688088,246261,320064),
    (33688088,57555,1132609),
    (8757838336,301749,1138720),
    (8757838336,620949,266388),
    (8757838336,347025,336640),
    (33688088,716271,17768),
    (33688088,263067,1327688),
    (33688088,301749,1123352),
    (8757838336,438447,368642),
    (8757838336,448749,933892),
    (8757838336,555285,1081363),
    (8757838336,465873,1147010),
    (33688088,476733,1385088),
    (33688088,786261,11308),
    (8757838336,607287,66598),
    (8757838336,690327,139313),
    (33688088,107199,393576),
    (8757838336,439707,231488),
    (8757838336,94977,16945),
    (8757838336,248769,164361),
    (8757838336,437541,233488)]

  let block8 : List (ℕ × ℕ × ℕ) := [
    (8757838336,220383,36886),
    (33688088,519699,471056),
    (8757838336,452865,925700),
    (33688088,758241,22787),
    (33688088,781263,20048),
    (8757838336,749367,36160),
    (8757838336,663657,1065736),
    (8757838336,637497,141856),
    (33688088,111399,590040),
    (8757838336,505527,402448),
    (8757838336,88713,4181),
    (8757838336,535131,1582082),
    (8757838336,396495,1705088),
    (33688088,301509,1126448),
    (33688088,340095,655914),
    (8757838336,800661,279074),
    (8757838336,781257,545288),
    (8757838336,537237,1331202),
    (8757838336,210363,140096),
    (33688088,729141,24729),
    (8757838336,312033,578048),
    (33688088,191889,1579268),
    (33688088,305247,616464),
    (8757838336,785193,50181),
    (8757838336,656643,1056818),
    (33688088,800667,748),
    (33688088,200235,1313809),
    (8757838336,432957,1392672),
    (8757838336,109971,16801),
    (33688088,779007,15120)]

  let block9 : List (ℕ × ℕ × ℕ) := [
    (33688088,201117,1182725),
    (8757838336,479607,786626),
    (8757838336,792543,36995),
    (8757838336,660051,1050900),
    (8757838336,650391,550916),
    (8757838336,583809,591881),
    (8757838336,658857,1050122),
    (8757838336,757941,1057825),
    (8757838336,301533,1105936),
    (8757838336,623127,140336),
    (8757838336,444039,921664),
    (33688088,736179,12315),
    (33688088,714015,21258),
    (8757838336,76455,24961),
    (8757838336,329979,344584),
    (33688088,492537,1359944),
    (8757838336,83505,12547),
    (33688088,800373,498),
    (33688088,244203,582152),
    (8757838336,519897,403968),
    (33688088,253809,1090120),
    (8757838336,114285,1549),
    (8757838336,525237,1316096),
    (8757838336,455247,1343506),
    (33688088,782055,21889),
    (33688088,459975,917680),
    (8757838336,767697,1067524),
    (8757838336,559821,1081921),
    (8757838336,316737,184352),
    (8757838336,320895,172068)]

  let block10 : List (ℕ × ℕ × ℕ) := [
    (8757838336,338073,100388),
    (8757838336,458115,1245344),
    (8757838336,198219,90160),
    (8757838336,28437,2627),
    (8757838336,447567,933896),
    (8757838336,427281,1839168),
    (33688088,109005,590473),
    (8757838336,735765,263320),
    (8757838336,535509,1131522),
    (8757838336,225969,49348),
    (8757838336,44535,10000),
    (33688088,537243,1152004),
    (8757838336,713673,524620),
    (33688088,111219,557416),
    (8757838336,572553,335882),
    (8757838336,714939,524690),
    (33688088,76599,1591556),
    (33688088,263919,1196420),
    (33688088,573963,852244),
    (8757838336,25647,2784),
    (8757838336,650427,552962),
    (8757838336,563997,1573636),
    (8757838336,648657,543752),
    (8757838336,695409,266592),
    (8757838336,113739,1306),
    (33688088,301869,1087493),
    (33688088,435303,1446920),
    (8757838336,630735,281344),
    (8757838336,648633,543760),
    (8757838336,533763,1582112)]

  let block11 : List (ℕ × ℕ × ℕ) := [
    (33688088,62343,1591361),
    (8757838336,202953,36920),
    (8757838336,478431,655560),
    (8757838336,179433,52736),
    (8757838336,80565,24617),
    (8757838336,648579,546817),
    (8757838336,782091,548930),
    (33688088,82395,1120304),
    (33688088,503541,1214467),
    (8757838336,83457,9286),
    (33688088,781065,23200),
    (8757838336,381369,689664),
    (8757838336,569157,1114246),
    (8757838336,304839,103432),
    (33688088,729249,18503),
    (8757838336,639333,72712),
    (33688088,797847,909),
    (8757838336,785487,50193),
    (8757838336,757773,1057810),
    (8757838336,516375,661506),
    (8757838336,90369,8610),
    (33688088,575655,622851),
    (8757838336,299109,1123840),
    (33688088,310035,616960),
    (33688088,45531,560320),
    (33688088,728901,24756),
    (8757838336,447225,704520),
    (33688088,578751,852740),
    (8757838336,636483,134276),
    (8757838336,99879,8269)]

  let block12 : List (ℕ × ℕ × ℕ) := [
    (8757838336,388263,1442832),
    (33688088,253797,1122960),
    (33688088,719337,9261),
    (33688088,303189,354432),
    (33688088,250281,300066),
    (8757838336,398175,1705472),
    (33688088,785835,7196),
    (33688088,219453,327881),
    (8757838336,45459,5536),
    (8757838336,579021,606280),
    (33688088,712629,6342),
    (8757838336,663375,1065552),
    (8757838336,179493,153088),
    (8757838336,669945,1049669),
    (8757838336,794937,37058),
    (8757838336,594315,131696),
    (8757838336,523707,1182784),
    (33688088,167415,1115143),
    (33688088,304671,185408),
    (33688088,776391,22050),
    (33688088,109551,787210),
    (8757838336,372045,427012),
    (33688088,779793,7554),
    (33688088,337599,164456),
    (8757838336,75105,18760),
    (8757838336,33141,2147),
    (33688088,774063,19544),
    (8757838336,433167,1458192),
    (8757838336,334797,297488),
    (33688088,800289,497)]

  let block13 : List (ℕ × ℕ × ℕ) := [
    (8757838336,357681,360516),
    (33688088,734037,18755),
    (33688088,262029,1131152),
    (8757838336,170109,39952),
    (33688088,716367,20840),
    (8757838336,654495,287746),
    (8757838336,425307,1706048),
    (8757838336,732567,35137),
    (8757838336,300357,1101828),
    (8757838336,60657,19720),
    (8757838336,623325,267273),
    (8757838336,82161,6410),
    (33688088,571917,819298),
    (8757838336,364377,688644),
    (33688088,583551,360462),
    (8757838336,569199,1179909),
    (33688088,297393,1134976),
    (8757838336,133695,32945),
    (8757838336,513423,804096),
    (33688088,455421,852489),
    (8757838336,108621,16716),
    (8757838336,55155,11332),
    (33688088,800577,881),
    (8757838336,99333,4186),
    (33688088,247119,217472),
    (8757838336,555729,1310748),
    (8757838336,670719,1052976),
    (8757838336,63351,14600),
    (8757838336,643323,144448),
    (33688088,348363,98358)]

  let block14 : List (ℕ × ℕ × ℕ) := [
    (33688088,773589,26788),
    (33688088,306285,812040),
    (8757838336,318213,340480),
    (33688088,504747,930048),
    (33688088,32175,108553),
    (8757838336,170361,46084),
    (33688088,733173,24930),
    (8757838336,620931,266314),
    (8757838336,426705,1613952),
    (8757838336,573225,329731),
    (33688088,460215,819352),
    (8757838336,483591,557082),
    (8757838336,522033,1126408),
    (33688088,339951,557610),
    (33688088,114285,294957),
    (33688088,711315,3665),
    (33688088,790821,350),
    (33688088,486783,1213445),
    (33688088,318717,203777),
    (8757838336,630447,281152),
    (33688088,317457,406530),
    (8757838336,367089,360578),
    (8757838336,658587,1051153),
    (8757838336,741429,35874),
    (33688088,114087,393267),
    (8757838336,63909,13828),
    (8757838336,670323,1049698),
    (33688088,49551,399408),
    (33688088,338775,557354),
    (33688088,775647,26900)]

  let block15 : List (ℕ × ℕ × ℕ) := [
    (33688088,287421,1106440),
    (33688088,307251,609281),
    (8757838336,329253,114820),
    (8757838336,434841,1642497),
    (8757838336,633531,527432),
    (8757838336,330267,344608),
    (8757838336,670635,1050800),
    (8757838336,230673,36998),
    (33688088,757233,28938),
    (8757838336,525723,1188928),
    (8757838336,447315,868360),
    (33688088,57513,1200194),
    (8757838336,64107,14849),
    (33688088,723663,10441),
    (8757838336,670587,1050776),
    (8757838336,220047,36914),
    (33688088,199545,1123337),
    (8757838336,559965,1180420),
    (8757838336,344751,573968),
    (8757838336,186171,77848),
    (8757838336,496701,591424),
    (33688088,340179,590361),
    (8757838336,758235,1053729),
    (8757838336,368271,917516),
    (33688088,307167,676866),
    (8757838336,129093,131717),
    (8757838336,769743,1058306),
    (8757838336,216267,35078),
    (33688088,523335,1624065),
    (33688088,749721,10945)]

  let block16 : List (ℕ × ℕ × ℕ) := [
    (8757838336,575577,329793),
    (8757838336,94107,16549),
    (8757838336,397923,1639936),
    (8757838336,716451,65944),
    (33688088,734919,6187),
    (8757838336,536361,1204240),
    (33688088,106947,328273),
    (8757838336,71661,10309),
    (8757838336,662385,1049928),
    (33688088,752739,9270),
    (33688088,348519,294935),
    (8757838336,583905,591908),
    (8757838336,775785,38017),
    (8757838336,127143,33604),
    (33688088,574677,721444),
    (33688088,572391,622744),
    (8757838336,220419,66595),
    (33688088,465921,458771),
    (8757838336,432831,1261584),
    (33688088,749271,7072),
    (8757838336,65403,21516),
    (8757838336,578103,397632),
    (33688088,746943,18210),
    (8757838336,599979,524435),
    (8757838336,594723,262346),
    (33688088,191775,1578050),
    (33688088,791421,670),
    (8757838336,321021,106516),
    (8757838336,28269,4675),
    (33688088,247143,184640)]

  let block17 : List (ℕ × ℕ × ℕ) := [
    (8757838336,660663,1050177),
    (8757838336,435171,1609736),
    (33688088,762735,26712),
    (33688088,506805,938016),
    (8757838336,793389,264280),
    (33688088,225207,655431),
    (8757838336,76749,21121),
    (8757838336,559239,1179746),
    (8757838336,656133,1050637),
    (33688088,230625,196635),
    (33688088,769791,14362),
    (8757838336,639675,79880),
    (8757838336,454407,1146892),
    (8757838336,558165,1311016),
    (8757838336,569403,1114249),
    (8757838336,383847,361600),
    (33688088,82587,1117208),
    (8757838336,434253,1392641),
    (8757838336,523749,1119296),
    (33688088,727737,20586),
    (8757838336,696831,147784),
    (8757838336,489645,197666),
    (8757838336,131007,32952),
    (33688088,502521,1253396),
    (33688088,288051,1099905),
    (8757838336,397935,1610240),
    (33688088,49953,199686),
    (33688088,402351,1443888),
    (8757838336,26301,1860),
    (8757838336,446949,638992)]

  let block18 : List (ℕ × ℕ × ℕ) := [
    (8757838336,99675,4649),
    (8757838336,785289,151557),
    (8757838336,320571,331816),
    (8757838336,556797,1081358),
    (8757838336,594513,262473),
    (8757838336,309987,610368),
    (8757838336,644883,288832),
    (8757838336,114327,1550),
    (8757838336,321597,102410),
    (8757838336,752907,69136),
    (8757838336,186903,74755),
    (8757838336,357279,229536),
    (8757838336,506019,300033),
    (8757838336,434343,1458180),
    (8757838336,484725,557069),
    (8757838336,643791,88128),
    (33688088,368247,1445908),
    (33688088,32721,307210),
    (8757838336,349377,336160),
    (33688088,574101,819337),
    (8757838336,563901,1573441),
    (8757838336,699825,533028),
    (8757838336,606615,263206),
    (8757838336,782139,549122),
    (33688088,751731,3126),
    (33688088,742143,17706),
    (33688088,363543,1851536),
    (8757838336,320685,297008),
    (8757838336,690615,266275),
    (8757838336,478773,656008)]

  let block19 : List (ℕ × ℕ × ℕ) := [
    (8757838336,76449,24897),
    (33688088,231885,327723),
    (33688088,264015,1097921),
    (8757838336,724635,66597),
    (8757838336,660093,1052836),
    (8757838336,369195,720914),
    (8757838336,439599,233600),
    (33688088,475179,1640708),
    (33688088,301533,1093672),
    (8757838336,478743,655952),
    (8757838336,349665,168480),
    (33688088,245577,312896),
    (8757838336,517257,796680),
    (8757838336,653625,153616),
    (8757838336,364407,721410),
    (8757838336,533505,1579040),
    (33688088,49467,333872),
    (8757838336,180399,40064),
    (8757838336,187119,38946),
    (8757838336,91113,4308),
    (8757838336,489723,165897),
    (33688088,577515,361040),
    (8757838336,25941,2528),
    (33688088,455271,918036),
    (8757838336,640851,79874),
    (8757838336,87705,4216),
    (8757838336,46887,9520),
    (33688088,485469,1378340),
    (8757838336,384015,427264),
    (33688088,223515,655540)]

  let block20 : List (ℕ × ℕ × ℕ) := [
    (33688088,579579,623184),
    (33688088,476523,1450752),
    (8757838336,689979,132122),
    (8757838336,228279,37250),
    (33688088,579381,721568),
    (8757838336,304401,208898),
    (8757838336,82239,5201),
    (8757838336,748335,543264),
    (33688088,475935,1446656),
    (8757838336,180291,72960),
    (8757838336,760125,1057872),
    (8757838336,506001,333825),
    (8757838336,799605,82051),
    (33688088,518871,363528),
    (8757838336,574101,164993),
    (8757838336,446727,737282),
    (8757838336,724335,34857),
    (8757838336,183885,58384),
    (33688088,105087,98691),
    (33688088,712155,9576),
    (33688088,224703,786538),
    (33688088,733257,24785),
    (8757838336,716613,262794),
    (8757838336,446655,638980),
    (8757838336,447237,737296),
    (8757838336,793557,266344),
    (8757838336,657651,1050646),
    (33688088,709203,6932),
    (8757838336,338061,99362),
    (8757838336,637791,268576)]

  let block21 : List (ℕ × ℕ × ℕ) := [
    (33688088,109677,787081),
    (8757838336,499575,657414),
    (33688088,300399,1091601),
    (8757838336,316659,215056),
    (8757838336,648411,546818),
    (8757838336,400233,1443328),
    (8757838336,381999,230656),
    (8757838336,455631,1245202),
    (33688088,153597,1115329),
    (8757838336,537147,1328129),
    (33688088,434691,1452036),
    (8757838336,657597,1049613),
    (8757838336,30495,2571),
    (8757838336,335121,106568),
    (8757838336,642459,273536),
    (8757838336,576495,165056),
    (33688088,45351,596352),
    (8757838336,768525,1053953),
    (8757838336,329031,180289),
    (8757838336,699525,528680),
    (8757838336,734925,66821),
    (33688088,133899,199683),
    (33688088,732567,19017),
    (33688088,774945,19526),
    (33688088,753039,6202),
    (8757838336,615825,528944),
    (8757838336,699051,525393),
    (8757838336,483477,655404),
    (8757838336,467217,1344002),
    (8757838336,47085,5641)]

  let block22 : List (ℕ × ℕ × ℕ) := [
    (8757838336,656007,1052686),
    (8757838336,732489,132482),
    (8757838336,477207,295233),
    (8757838336,773733,71689),
    (8757838336,388599,1246224),
    (8757838336,359451,917584),
    (33688088,359217,1843488),
    (8757838336,109839,16594),
    (8757838336,768693,1051784),
    (33688088,778419,15108),
    (33688088,251151,206896),
    (33688088,113709,196653),
    (8757838336,251595,164116),
    (8757838336,460509,1704096),
    (8757838336,347529,199296),
    (33688088,107175,393648),
    (8757838336,741135,35880),
    (8757838336,613671,263872),
    (8757838336,30375,1574),
    (8757838336,443457,925824),
    (8757838336,792549,69701),
    (8757838336,574107,198721),
    (8757838336,562815,1573640),
    (8757838336,714603,525074),
    (8757838336,533673,1579024),
    (8757838336,47295,3594),
    (8757838336,614973,525445),
    (8757838336,600015,524366),
    (8757838336,670239,1049681),
    (8757838336,615531,532772)]

  let block23 : List (ℕ × ℕ × ℕ) := [
    (8757838336,797847,526984),
    (8757838336,94293,16467),
    (8757838336,555477,1179698),
    (8757838336,516585,600065),
    (8757838336,572727,401425),
    (8757838336,502875,329224),
    (8757838336,580365,802881),
    (8757838336,598947,524828),
    (33688088,748329,18072),
    (8757838336,570165,1311266),
    (8757838336,211413,147589),
    (8757838336,570075,1311241),
    (8757838336,315855,319520),
    (8757838336,791457,139299),
    (8757838336,330021,410120),
    (33688088,396555,1712896),
    (8757838336,645135,290880),
    (8757838336,798555,533058),
    (8757838336,562533,1573456),
    (8757838336,193935,156032),
    (8757838336,774957,75782),
    (8757838336,752937,38408),
    (8757838336,606549,266261),
    (8757838336,750177,272000),
    (8757838336,762741,1073312),
    (8757838336,248541,327976),
    (8757838336,630489,283200),
    (33688088,339939,590388),
    (8757838336,458103,1212512),
    (8757838336,557199,1179782)]

  let block24 : List (ℕ × ℕ × ℕ) := [
    (8757838336,90189,2672),
    (8757838336,217149,35352),
    (8757838336,71511,12422),
    (8757838336,32769,1330),
    (8757838336,400239,1444352),
    (8757838336,424671,1345600),
    (8757838336,182343,80128),
    (8757838336,496341,788672),
    (8757838336,569499,1114276),
    (8757838336,62337,25857),
    (8757838336,212289,278676),
    (8757838336,766641,1073288),
    (8757838336,426783,1646848),
    (8757838336,778191,71872),
    (8757838336,212337,82456),
    (8757838336,516603,566273),
    (33688088,480117,1622145),
    (8757838336,381975,231680),
    (8757838336,637491,140832),
    (8757838336,422193,1220609),
    (8757838336,669987,1049670),
    (8757838336,526077,1197184),
    (8757838336,614523,134016),
    (8757838336,569793,1114288),
    (33688088,107535,196933),
    (33688088,774261,27172),
    (8757838336,494871,657600),
    (8757838336,606297,133176),
    (8757838336,197049,86022),
    (8757838336,639225,138256)]

  let block25 : List (ℕ × ℕ × ℕ) := [
    (8757838336,81411,18454),
    (8757838336,297417,1106048),
    (8757838336,592335,262229),
    (33688088,536145,1224712),
    (33688088,318657,105474),
    (8757838336,750393,273152),
    (8757838336,480117,656001),
    (33688088,74271,1185088),
    (33688088,368835,1450004),
    (8757838336,799653,82054),
    (8757838336,670923,1057297),
    (8757838336,299187,1190400),
    (33688088,45363,562496),
    (8757838336,486789,327811),
    (8757838336,133359,33308),
    (33688088,750177,10080),
    (8757838336,128613,33448),
    (8757838336,455415,1343521),
    (8757838336,569733,1081432),
    (8757838336,774237,272394),
    (8757838336,106905,8804),
    (8757838336,129285,33413),
    (8757838336,94173,16654),
    (8757838336,663159,1065376),
    (8757838336,357009,360544),
    (8757838336,475023,295043),
    (8757838336,799641,49222),
    (8757838336,645141,290944),
    (8757838336,670341,1050788),
    (8757838336,210567,74624)]

  let block26 : List (ℕ × ℕ × ℕ) := [
    (33688088,300333,1126436),
    (8757838336,774405,274441),
    (8757838336,603891,131633),
    (8757838336,210975,35520),
    (8757838336,558369,1310896),
    (8757838336,364869,852225),
    (8757838336,777261,75841),
    (33688088,749295,5984),
    (8757838336,126891,33232),
    (8757838336,761391,1067076),
    (8757838336,793725,73809),
    (8757838336,513171,803968),
    (8757838336,329595,344196),
    (8757838336,556809,1114134),
    (8757838336,716367,131496),
    (8757838336,47151,6690),
    (8757838336,599181,524841),
    (33688088,297465,1197376),
    (8757838336,366417,360962),
    (8757838336,94149,16662),
    (8757838336,477273,393602),
    (33688088,303063,422144),
    (8757838336,796113,41160),
    (8757838336,653199,88066),
    (8757838336,297129,1198592),
    (8757838336,730179,525508),
    (8757838336,533751,1583112),
    (8757838336,517539,795680),
    (8757838336,712251,131440),
    (8757838336,439251,462849)]

  let block27 : List (ℕ × ℕ × ℕ) := [
    (8757838336,583605,659461),
    (8757838336,70947,12376),
    (33688088,251259,176168),
    (8757838336,500481,787480),
    (8757838336,317115,170240),
    (8757838336,30081,1336),
    (8757838336,561543,1081672),
    (8757838336,639591,145416),
    (8757838336,184095,58400),
    (8757838336,447033,704544),
    (8757838336,714891,524498),
    (8757838336,334965,299552),
    (8757838336,437565,233480),
    (8757838336,777387,143426),
    (8757838336,734919,35075),
    (8757838336,616815,528458),
    (8757838336,212361,49688),
    (8757838336,513141,804928),
    (8757838336,182331,46336),
    (33688088,798021,854),
    (8757838336,577515,401984),
    (8757838336,664743,1065537),
    (8757838336,734121,37442),
    (8757838336,525273,1317120),
    (8757838336,614967,526403),
    (33688088,576609,459396),
    (8757838336,695283,264400),
    (8757838336,111609,8866),
    (8757838336,516405,660484),
    (8757838336,690243,73778)]

  let block28 : List (ℕ × ℕ × ℕ) := [
    (8757838336,780459,542978),
    (8757838336,795957,266848),
    (8757838336,592143,262421),
    (8757838336,109005,17036),
    (8757838336,496629,788864),
    (8757838336,381117,624128),
    (8757838336,559929,1180418),
    (8757838336,620697,133680),
    (8757838336,620847,264265),
    (8757838336,573273,329734),
    (8757838336,244455,557472),
    (8757838336,556755,1081357),
    (8757838336,479823,786817),
    (8757838336,746943,541956),
    (8757838336,49911,5396),
    (8757838336,656349,1052716),
    (8757838336,112317,4867),
    (8757838336,213363,81993),
    (8757838336,479991,590594),
    (8757838336,56853,25760),
    (8757838336,200559,45576),
    (8757838336,778107,137536),
    (8757838336,432273,1163266),
    (8757838336,297963,1087744),
    (8757838336,363183,622856),
    (8757838336,558033,1114644),
    (8757838336,366435,426500),
    (8757838336,192411,51520),
    (8757838336,660351,1051009),
    (8757838336,663123,1065312)]

  let block29 : List (ℕ × ℕ × ℕ) := [
    (8757838336,516519,560130),
    (8757838336,251343,98480),
    (8757838336,496425,790848),
    (8757838336,105177,2149),
    (8757838336,670917,1057289),
    (8757838336,92679,8900),
    (8757838336,446973,638984),
    (8757838336,56883,26720),
    (8757838336,434289,1359874),
    (8757838336,483771,786482),
    (8757838336,194397,86656),
    (8757838336,129579,33169),
    (8757838336,696501,147841),
    (8757838336,95769,16531),
    (8757838336,369273,688161),
    (8757838336,620991,264484),
    (8757838336,182163,44160),
    (8757838336,536013,1197064),
    (8757838336,533331,1579009),
    (8757838336,653277,152577),
    (8757838336,321567,165924),
    (8757838336,714555,524882),
    (8757838336,88119,8331),
    (8757838336,790791,133164),
    (8757838336,484767,557070),
    (8757838336,229911,132674),
    (8757838336,624093,70692),
    (8757838336,451599,724993),
    (8757838336,316743,217120),
    (8757838336,463995,1638672)]

  let rows : List (ℕ × ℕ × ℕ) := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23 ++ block24 ++ block25 ++ block26 ++ block27 ++ block28 ++ block29

  let forbidden := rows.map (fun r => r.2.2)
  have valid : rows.all rowOK = true := by decide +kernel
  obtain ⟨m,hm,avoid⟩ := covers_spec 21 11 z forbidden bound size (by decide +kernel)
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
  exact ⟨r, List.all_eq_true.mp valid r hr, avoid⟩

end SmallCover.Seven

open Finset SimpleGraph
namespace SmallCover.Seven
theorem seven_sparse (G : SimpleGraph (Fin 7)) (gc : G.Connected) (size : G.edgeSet.ncard=11) :
    ∃ m ∈ ([8757838336,33688088] : List ℕ), ∃ e : Fin 7 ↪ Fin 7,
      ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*7+(max (e i) (e j)).val)=false := by
  obtain ⟨z,bound,bits,count⟩ := encoding_spec G
  let addr (i j : ℕ) := j.choose 2+i
  let digit (p : ℕ) (i : Fin 7) : Fin 7 :=
    ⟨p / 7^i.val % 7, Nat.mod_lt _ (by decide)⟩

  let templateIndex (i j : Fin 7) := (min i j).val * 7 + (max i j).val

  let rowOK (r : ℕ × ℕ × ℕ) : Bool :=
    let (t,p,d) := r
    if t=0 then
      decide ((∃ i : Fin 7, p.testBit i=false) ∧ (∃ j : Fin 7, p.testBit j=true) ∧
        ∀ i j : Fin 7, i<j → p.testBit i ≠ p.testBit j → d.testBit (addr i j)=true)
    else
      decide ((t=8757838336 ∨ t=33688088) ∧
        (∀ i j : Fin 7, i<j → digit p i ≠ digit p j) ∧
        ∀ i j : Fin 7, i<j → t.testBit (templateIndex (digit p i) (digit p j))=true →
          d.testBit (addr i j)=true)
  obtain ⟨r,valid,avoid⟩ := certified_rows z bound (count ▸ size)
  change rowOK r = true at valid
  have rank_bound {i j : Fin 7} (h : i < j) : addr i j < 21 := by
    apply Nat.lt_of_lt_of_le _ (Nat.choose_le_choose 2 j.isLt)
    change j.val.choose 2+i.val < (j.val+1).choose 2
    rw [Nat.choose_succ_succ' j.val 1,Nat.choose_one_right]
    change j.val.choose 2 + i.val < j.val + j.val.choose 2
    omega
  obtain ⟨t,p,d⟩ := r
  have absent {i j : Fin 7} (hij : i<j) (hG : G.Adj i j) :
      d.testBit (addr i j) = false :=
    avoid _ (rank_bound hij)
      ((bits i j hij).mpr hG)
  by_cases cut : t=0
  · simp only [rowOK,cut,if_true,decide_eq_true_eq] at valid
    obtain ⟨h0,h1,hmask⟩ := valid
    obtain ⟨i,j,hG,hne⟩ := seven_connected_cut gc (fun k : Fin 7 => p.testBit k) h0 h1
    exfalso
    rcases lt_or_gt_of_ne hG.ne with lt|gt
    · have := hmask i j lt hne
      simp [absent lt hG] at this
    · have := hmask j i gt (Ne.symm hne)
      simp [absent gt hG.symm] at this
  · simp only [rowOK,cut,if_false,decide_eq_true_eq] at valid
    obtain ⟨ht,hinj,hm⟩ := valid
    let e : Fin 7 ↪ Fin 7 := ⟨digit p, by
      intro i j eq
      by_contra ne
      rcases lt_or_gt_of_ne ne with lt|gt
      · exact hinj i j lt eq
      · exact hinj j i gt eq.symm⟩
    refine ⟨t, by simpa using ht, e, ?_⟩
    have forward {i j : Fin 7} (lt : i<j) (hG : G.Adj i j) :
        t.testBit (templateIndex (e i) (e j)) = false := by
      cases bit : t.testBit (templateIndex (e i) (e j)) with
      | false => rfl
      | true =>
        have h := hm i j lt bit
        simp [absent lt hG] at h
    intro i j hG
    rcases lt_or_gt_of_ne hG.ne with lt|gt
    · exact forward lt hG
    · simpa only [templateIndex,min_comm (e j) (e i),max_comm (e j) (e i)] using
        forward gt hG.symm
end SmallCover.Seven

namespace SmallEight

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
theorem eight_certificate (k : Fin 8) :
    let addr (i j : ℕ) := j.choose 2 + i
    let digit (p : ℕ) (i : Fin 8) : Fin 8 := ⟨p / 8 ^ i.val % 8, Nat.mod_lt _ (by decide)⟩

    let templateIndex (i j : Fin 8) := (min i j).val * 8 + (max i j).val

    let forbidden (k d : ℕ) (i j : Fin 8) : Bool :=
      if j.val=7 then decide (k ≤ i.val) else d.testBit (addr i j)

    let rowOK (k : ℕ) (r : ℕ × ℕ × ℕ) : Bool :=
      let (t,p,d) := r
      if t=0 then
        decide ((∃ i : Fin 8, p.testBit i=false) ∧ (∃ j : Fin 8, p.testBit j=true) ∧
          ∀ i j : Fin 8, i<j → p.testBit i ≠ p.testBit j → forbidden k d i j=true)
      else
        decide ((t=36169948434793600 ∨ t=70781333153792) ∧
          (∀ i j : Fin 8, i<j → digit p i ≠ digit p j) ∧
          ∀ i j : Fin 8, i<j → t.testBit (templateIndex (digit p i) (digit p j))=true →
            forbidden k d i j=true)
    let join (width a b : ℕ) := a % 2^width ||| (b <<< width)
    let free : ℕ → ℕ → ℕ := Nat.rec (fun _ => 1) (fun u rec mask =>
      let low := rec mask
      join (2^u) low (if mask.testBit u then 0 else low))
    let exactSize : ℕ → ℕ → ℕ := Nat.rec (fun q => if q=0 then 1 else 0) (fun u rec q =>
      join (2^u) (rec q) (if q=0 then 0 else rec (q-1)))
    ∃ rs : List (ℕ × ℕ × ℕ), rs.all (rowOK k) = true ∧
      exactSize 21 (11-k.val) &&&
        (rs.map (fun r => r.2.2)).foldr (fun m rest => free 21 m ||| rest) 0 =
          exactSize 21 (11-k.val) := by
  intro addr digit templateIndex forbidden rowOK join free exactSize
  fin_cases k
  · let rs : List (ℕ × ℕ × ℕ) := [
    (0,127,0)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (70781333153792,12380179,1561), (70781333153792,9429329,98566), (36169948434793600,13301848,157760), (70781333153792,9042544,1314864), (70781333153792,11063024,659840), (70781333153792,9425969,295616), (36169948434793600,15407427,533538), (36169948434793600,15938601,1130632), (70781333153792,10908051,39937), (70781333153792,11474400,854032), (70781333153792,12527816,8996), (36169948434793600,15926617,1181708), (36169948434793600,13136669,278595), (36169948434793600,15754347,589921), (70781333153792,10347176,12436), (36169948434793600,14765387,2826), (36169948434793600,15420097,53792), (36169948434793600,14500185,394500), (36169948434793600,14435533,1081426), (36169948434793600,13825553,1073409), (36169948434793600,13354509,70728), (70781333153792,9167081,196739), (70781333153792,9954945,688168), (70781333153792,11606000,1384960)] ++ [
    (70781333153792,10429160,2480), (36169948434793600,13719097,525956), (36169948434793600,14753123,16414), (70781333153792,9809345,836608), (70781333153792,10193561,262189), (70781333153792,10907288,88068), (36169948434793600,16321305,197680), (36169948434793600,16419025,405505), (70781333153792,9219056,1581584), (36169948434793600,15264515,1048936), (70781333153792,10908723,44040), (70781333153792,9924761,1212421), (70781333153792,9125697,659522), (36169948434793600,14894187,17569), (36169948434793600,13267688,264388), (70781333153792,9415721,557201), (36169948434793600,13162968,1049474), (70781333153792,9395841,180544), (36169948434793600,14895769,18962), (70781333153792,10057257,75785), (36169948434793600,14054929,1835265), (70781333153792,8968120,811264), (36169948434793600,14428393,1114196), (70781333153792,11764851,360458)] ++ [
    (70781333153792,10342577,5568), (36169948434793600,15419971,149000), (70781333153792,11140360,1185824), (36169948434793600,13721176,529032), (70781333153792,8891120,394000), (36169948434793600,13825665,1073282), (36169948434793600,13253576,74274), (36169948434793600,14506184,559872), (36169948434793600,14887019,9489), (70781333153792,12390707,5190), (70781333153792,12527627,8777), (36169948434793600,13291201,61456), (70781333153792,10973347,34823), (36169948434793600,15933995,1115649), (36169948434793600,12724173,132234), (70781333153792,9133656,606468), (70781333153792,10909360,276512), (70781333153792,9042481,1311768), (36169948434793600,13825112,1067104), (70781333153792,9827377,369664), (36169948434793600,15851857,675841), (70781333153792,11136608,1120384), (36169948434793600,15935297,1187936), (36169948434793600,15224041,33444)] ++ [
    (70781333153792,9954392,917524), (36169948434793600,13741672,67864), (70781333153792,9383745,561410), (36169948434793600,12744333,525388), (36169948434793600,14894313,20620), (70781333153792,10421481,2099), (36169948434793600,15418179,279810), (70781333153792,11476640,722948), (70781333153792,9425297,98752), (36169948434793600,13711992,266769), (70781333153792,11331768,1442336), (70781333153792,9164337,786632), (36169948434793600,16425731,169472), (36169948434793600,12677917,532547), (70781333153792,10833368,84608), (70781333153792,10874640,1054980), (70781333153792,11640496,1265664), (70781333153792,10042312,286864), (70781333153792,9906113,1606152), (70781333153792,12121312,69684), (70781333153792,10235113,403), (36169948434793600,13727560,133472), (70781333153792,9925832,1376292), (70781333153792,9272193,1089576)] ++ [
    (36169948434793600,14038472,1703954), (70781333153792,11148851,1084480), (36169948434793600,13253240,139793), (70781333153792,9140033,397322), (70781333153792,10412752,26660), (36169948434793600,15401827,265222), (70781333153792,10238641,376), (70781333153792,10343473,9920), (36169948434793600,13702717,49165), (36169948434793600,16433305,608258), (36169948434793600,15946777,1575048), (70781333153792,10048248,545312), (36169948434793600,13709437,36945), (70781333153792,9428104,197504), (70781333153792,12455051,13315), (70781333153792,11246851,163938), (70781333153792,12403083,17729), (36169948434793600,13905689,467008), (70781333153792,10324657,5176), (70781333153792,9269617,1085446), (70781333153792,9157960,655524), (36169948434793600,13874497,137480), (70781333153792,11596179,230401), (36169948434793600,13662929,279073)] ++ [
    (36169948434793600,13240297,35092), (70781333153792,11408824,1847296), (70781333153792,11777136,852736), (36169948434793600,13709801,66724), (70781333153792,10865848,1069824), (36169948434793600,14550221,558098), (36169948434793600,13239037,263299), (36169948434793600,12744529,528673), (70781333153792,10422993,8222), (70781333153792,11662728,1452032), (70781333153792,10962371,49736), (36169948434793600,12655069,147467), (70781333153792,12198872,1067152), (36169948434793600,14592193,1126464), (36169948434793600,14562345,198792), (36169948434793600,12738201,279170), (70781333153792,10212377,524881), (36169948434793600,15423681,45824), (36169948434793600,16324931,311330), (36169948434793600,13726041,132868), (70781333153792,9395729,114880), (36169948434793600,12668509,266313), (70781333153792,8891624,197008), (36169948434793600,13733545,68114)] ++ [
    (36169948434793600,13733713,135713), (36169948434793600,13170920,1048788), (36169948434793600,13655705,533122), (36169948434793600,12724985,73840), (70781333153792,12111491,525634), (70781333153792,11739896,1704224), (70781333153792,10301865,18501), (70781333153792,9926161,1146904), (36169948434793600,13353816,267524), (70781333153792,9383465,559233), (70781333153792,10203305,65861), (36169948434793600,16425227,169088), (36169948434793600,13343512,533552), (70781333153792,12219459,1057802), (36169948434793600,15256619,1049225), (70781333153792,9942065,361024), (70781333153792,11003139,33066), (36169948434793600,14139601,1712129), (70781333153792,12429424,29200), (36169948434793600,14485709,559114), (36169948434793600,14435421,1081441), (36169948434793600,13653465,528776), (36169948434793600,16337601,656928), (70781333153792,12534480,16804)] ++ [
    (36169948434793600,14894425,18700), (36169948434793600,14037177,1638418), (36169948434793600,13965560,475137), (70781333153792,9084152,1204480), (70781333153792,10974880,264244), (70781333153792,11241867,294953), (36169948434793600,13979161,853024), (36169948434793600,13727301,37064), (70781333153792,10155201,1057826), (36169948434793600,12671225,67456), (70781333153792,9934736,721424), (70781333153792,8845200,1316880), (36169948434793600,14559769,401488), (36169948434793600,12822873,1052772), (70781333153792,10280144,21124), (36169948434793600,13239933,132233), (36169948434793600,13291033,59424), (36169948434793600,12654845,81931), (36169948434793600,13353501,267329), (70781333153792,11333392,1245444), (70781333153792,9131969,802888), (70781333153792,10833347,50752), (70781333153792,10282216,6320), (70781333153792,10910928,145412)] ++ [
    (70781333153792,10199385,131459), (70781333153792,10442369,16744), (70781333153792,9125480,592132), (70781333153792,12452531,7178), (70781333153792,10197712,262932), (70781333153792,9415784,655508), (70781333153792,10413585,19480), (70781333153792,11069240,401696), (70781333153792,11771011,426050), (70781333153792,10857784,1069344), (70781333153792,11658696,1845248), (70781333153792,10841635,35969), (36169948434793600,12666829,133194), (36169948434793600,13861981,50209), (70781333153792,10006248,72064), (36169948434793600,14895755,17932), (70781333153792,9762704,1253392), (70781333153792,11595395,689154), (70781333153792,12445832,14880), (70781333153792,12132099,136258), (36169948434793600,13250937,37140), (36169948434793600,14428365,1081482), (70781333153792,9407825,98342), (70781333153792,9346232,684032)] ++ [
    (70781333153792,11414984,1662976), (70781333153792,11245955,295016), (70781333153792,9794288,1380384), (70781333153792,11331040,1376400), (70781333153792,9931929,425989), (36169948434793600,13267485,263489), (70781333153792,11644360,1853440), (36169948434793600,14894929,24865), (70781333153792,10333064,18992), (36169948434793600,14054600,1704016), (36169948434793600,14034489,1376324), (36169948434793600,12679261,528457), (36169948434793600,16263961,196720), (70781333153792,12393731,5218), (70781333153792,12174792,551424), (70781333153792,9907912,1638660), (70781333153792,10201793,262922), (70781333153792,10993843,33218), (36169948434793600,13355608,140816), (36169948434793600,13807192,1059080), (36169948434793600,13725789,37441), (70781333153792,11766867,360451), (36169948434793600,14885731,3590), (36169948434793600,16404689,1196289)] ++ [
    (36169948434793600,15362627,155720), (70781333153792,12519563,8235), (70781333153792,11629107,1147912), (36169948434793600,13751752,540946), (70781333153792,12153568,71716), (70781333153792,10025680,274452), (36169948434793600,12667641,67120), (70781333153792,9825872,727040), (70781333153792,12533843,16579), (36169948434793600,12724201,133204), (36169948434793600,13251525,263238), (70781333153792,10840536,76304), (70781333153792,10272080,20644), (36169948434793600,13911513,725000), (70781333153792,11147192,1323520), (70781333153792,9166024,656004), (70781333153792,11631683,1344514), (36169948434793600,16427033,337984), (70781333153792,11003664,262452), (70781333153792,9937816,917648), (70781333153792,10844547,42024), (70781333153792,9748368,1261696), (70781333153792,10296216,10912), (70781333153792,12130552,274720)] ++ [
    (36169948434793600,13717753,525712), (36169948434793600,12743773,525409), (70781333153792,11170355,1084424), (70781333153792,9115624,330368), (70781333153792,9140761,335881), (70781333153792,12424608,26644), (70781333153792,12142200,549408), (70781333153792,9139753,329737), (70781333153792,10234609,794), (70781333153792,11069688,397856), (70781333153792,10071873,148738), (36169948434793600,13124573,266307), (36169948434793600,15422211,267584), (36169948434793600,14428505,1179748), (70781333153792,9117528,201088), (70781333153792,10137288,1067268), (36169948434793600,12722941,67075), (70781333153792,9264689,1097920), (70781333153792,12141507,541768), (70781333153792,12465544,29312), (70781333153792,9270184,1312788), (70781333153792,9425584,394112), (70781333153792,12379171,1177), (36169948434793600,12666745,66852)] ++ [
    (70781333153792,11626104,1843232), (70781333153792,9427985,99008), (70781333153792,11597712,466960), (70781333153792,10895024,547072), (36169948434793600,13259736,278914), (70781333153792,9380840,788624), (70781333153792,11166456,1200160), (70781333153792,11214371,100417), (70781333153792,9425073,164288), (70781333153792,9133593,606273), (36169948434793600,13646801,266785), (36169948434793600,13871704,271632)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (70781333153792,9428104,197504), (70781333153792,9131969,802888), (70781333153792,10155201,1057826), (36169948434793600,13240297,35092), (36169948434793600,16419025,405505), (36169948434793600,16392537,1118276), (70781333153792,10333064,18992), (70781333153792,11595395,689154), (36169948434793600,15946777,1575048), (36169948434793600,12744529,528673), (70781333153792,10840515,42504), (36169948434793600,15421987,265408), (36169948434793600,14753123,16414), (36169948434793600,13825553,1073409), (36169948434793600,16263961,196720), (36169948434793600,15231321,33444), (36169948434793600,16418969,337922), (70781333153792,10956547,37186), (70781333153792,9082808,1331712), (70781333153792,9133768,671876), (36169948434793600,13240269,66826), (70781333153792,12457368,14480), (36169948434793600,15926617,1181708), (36169948434793600,15755929,786578)] ++ [
    (70781333153792,9035201,1574464), (70781333153792,10091137,267304), (70781333153792,9781121,1228864), (36169948434793600,12745425,533025), (70781333153792,10201800,262932), (70781333153792,9825928,727040), (36169948434793600,13709801,66724), (70781333153792,11069240,401696), (36169948434793600,13727301,37064), (36169948434793600,16404633,1130626), (36169948434793600,14765387,2826), (36169948434793600,13643497,73812), (70781333153792,9809345,836608), (36169948434793600,16385355,1085458), (36169948434793600,14557928,100868), (36169948434793600,13254213,132184), (36169948434793600,14054929,1835265), (70781333153792,10304385,24680), (36169948434793600,13733713,135713), (70781333153792,10071873,148738), (70781333153792,9272193,1089576), (36169948434793600,14899409,13057), (70781333153792,10833816,84352), (36169948434793600,13251525,263238)] ++ [
    (70781333153792,9268168,1122832), (36169948434793600,14773017,1456), (70781333153792,9166017,655938), (36169948434793600,13291201,61456), (36169948434793600,14036680,1441928), (36169948434793600,14562373,99424), (36169948434793600,14895755,17932), (36169948434793600,13643469,41098), (70781333153792,9925832,1376292), (70781333153792,12132120,137348), (36169948434793600,14571137,606722), (36169948434793600,13170920,1048788), (70781333153792,10155656,1054768), (36169948434793600,14139601,1712129), (70781333153792,9954945,688168), (70781333153792,11069912,330256), (36169948434793600,14562625,200968), (70781333153792,11408824,1847296), (36169948434793600,14885731,3590), (70781333153792,12294275,262250), (36169948434793600,16434201,608264), (70781333153792,10042312,286864), (36169948434793600,16425227,169088), (70781333153792,10304833,20578)] ++ [
    (36169948434793600,14506184,559872), (70781333153792,12365080,2468), (70781333153792,11256728,590224), (36169948434793600,13662929,279073), (36169948434793600,14550669,558092), (70781333153792,11771011,426050), (36169948434793600,16321305,197680), (36169948434793600,13751752,540946), (36169948434793600,13710312,73862), (36169948434793600,13354509,70728), (36169948434793600,13871809,272480), (36169948434793600,13727560,133472), (36169948434793600,13246184,526364), (70781333153792,10907288,88068), (70781333153792,10833347,50752), (70781333153792,9401665,299042), (36169948434793600,12724173,132234), (70781333153792,9906113,1606152), (36169948434793600,16427019,304256), (70781333153792,12137272,152320), (36169948434793600,14435533,1081426), (36169948434793600,13805512,1060994), (36169948434793600,13267688,264388), (70781333153792,11631683,1344514)] ++ [
    (36169948434793600,12724201,133204), (70781333153792,8968120,811264), (36169948434793600,16404689,1196289), (36169948434793600,14500549,106562), (36169948434793600,14895769,18962), (36169948434793600,13661417,82060), (70781333153792,10083969,529728), (70781333153792,11629464,1247248), (36169948434793600,14894425,18700), (70781333153792,11258968,590468), (36169948434793600,15851857,675841), (70781333153792,9116408,402176), (36169948434793600,14898275,3296), (70781333153792,10907267,54274), (70781333153792,9140936,401428), (70781333153792,11003160,65844), (70781333153792,12195267,1057864), (70781333153792,11062744,592512), (36169948434793600,13741672,67864), (36169948434793600,14599368,1101840), (36169948434793600,13759816,135504), (36169948434793600,12666857,132244), (70781333153792,10962371,49736), (70781333153792,9907912,1638660)] ++ [
    (36169948434793600,14550221,558098), (70781333153792,12371331,1864), (36169948434793600,14562345,198792), (70781333153792,10155208,1058852), (36169948434793600,14038472,1703954), (36169948434793600,16275609,328322), (36169948434793600,13353704,265348), (36169948434793600,13268521,35216), (70781333153792,9344440,815104), (70781333153792,11245955,295016), (70781333153792,11074840,198692), (70781333153792,11003139,33066), (70781333153792,9092552,1583232), (70781333153792,12305475,524874), (36169948434793600,16427033,337984), (36169948434793600,13646801,266785), (36169948434793600,12729297,139809), (36169948434793600,15421539,134336), (70781333153792,11760728,1376276), (70781333153792,10057544,143380), (36169948434793600,13359304,83712), (36169948434793600,13712937,66736), (36169948434793600,13805505,1060932), (70781333153792,10964611,49474)] ++ [
    (70781333153792,10312904,21124), (70781333153792,12197507,1053762), (70781333153792,9938817,688648), (36169948434793600,13759529,67976), (70781333153792,11331768,1442336), (70781333153792,10856888,1073696), (36169948434793600,16433305,608258), (70781333153792,9140929,401418), (36169948434793600,12744333,525388), (70781333153792,9395841,180544), (36169948434793600,13160168,1048732), (36169948434793600,16406033,1327617), (36169948434793600,16418059,168976), (36169948434793600,15403801,38960), (70781333153792,10058433,274442), (70781333153792,10857784,1069344), (36169948434793600,13882561,542984), (70781333153792,12130552,274720), (70781333153792,12198872,1067152), (70781333153792,9157953,655458), (70781333153792,9370760,210944), (36169948434793600,13758605,34372), (36169948434793600,13758633,68226), (70781333153792,9140033,397322)] ++ [
    (70781333153792,12393731,5218), (36169948434793600,15421707,70976), (70781333153792,9401672,331812), (70781333153792,9043265,1180706), (36169948434793600,14054600,1704016), (70781333153792,10043208,151684), (70781333153792,10048248,545312), (70781333153792,10995096,66448), (70781333153792,11219768,660224), (36169948434793600,13809089,1069068), (36169948434793600,14435561,1114252), (36169948434793600,12727757,132178), (70781333153792,10833368,84608), (70781333153792,10844547,42024), (70781333153792,11474232,921632), (70781333153792,11626104,1843232), (36169948434793600,13645261,36946), (70781333153792,9039688,1181956), (70781333153792,12527704,8852), (36169948434793600,12743913,526476), (70781333153792,9415560,590384), (70781333153792,9265032,1130880), (70781333153792,10137281,1066242), (70781333153792,11256707,557384)] ++ [
    (70781333153792,10304392,24752), (70781333153792,8840888,1331232), (70781333153792,11607288,1446144), (70781333153792,9368968,342016), (36169948434793600,15231587,131288)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (70781333153792,9131969,802888), (36169948434793600,16321305,197680), (36169948434793600,14899409,13057), (36169948434793600,15945881,1575042), (36169948434793600,16386699,1089548), (36169948434793600,16339211,166208), (36169948434793600,16275609,328322), (36169948434793600,15928017,1314849), (70781333153792,10905048,92176), (36169948434793600,14895755,17932), (36169948434793600,14772835,4312), (70781333153792,11223800,672032), (70781333153792,9035201,1574464), (36169948434793600,16425227,169088), (36169948434793600,15231769,33200), (36169948434793600,13761160,270916), (36169948434793600,16418073,202760), (36169948434793600,14599697,1204225), (36169948434793600,16425059,101632), (36169948434793600,14895769,18962), (36169948434793600,15231755,65896), (70781333153792,9364929,320512), (36169948434793600,14898275,3296), (36169948434793600,14054929,1835265)] ++ [
    (36169948434793600,16272025,590354), (70781333153792,9823352,929792), (36169948434793600,14887523,3352), (36169948434793600,16404633,1130626), (36169948434793600,14550669,558092), (36169948434793600,13882897,545281), (36169948434793600,15403801,38960), (70781333153792,9909368,1442560), (36169948434793600,15755929,786578), (36169948434793600,14898443,5456), (36169948434793600,16263947,164008), (36169948434793600,16418969,337922), (70781333153792,11062744,592512), (70781333153792,12195064,1061152), (70781333153792,9264577,1098304), (36169948434793600,13733713,135713), (36169948434793600,15927947,1311756), (36169948434793600,14838481,24865), (36169948434793600,13873293,42052), (36169948434793600,16433305,608258), (36169948434793600,15231587,131288), (36169948434793600,16321123,102424), (36169948434793600,16339043,102592), (36169948434793600,16386769,1187873)] ++ [
    (70781333153792,9103304,1329168), (36169948434793600,16339225,198016), (36169948434793600,14898457,6536), (36169948434793600,16275595,295492), (70781333153792,12195267,1057864), (36169948434793600,14838425,24722), (36169948434793600,13875841,272898), (70781333153792,10955224,74384), (36169948434793600,13862737,151585), (36169948434793600,15755985,786721), (36169948434793600,14571025,672257), (36169948434793600,15945937,1577217), (36169948434793600,13741609,67696), (36169948434793600,14887691,5288), (70781333153792,10890488,160000), (36169948434793600,13354565,134216), (36169948434793600,16425241,202816), (36169948434793600,13825672,1073220), (70781333153792,9809345,836608), (36169948434793600,16263779,98584), (36169948434793600,13647501,41036), (70781333153792,9906113,1606152), (70781333153792,12195288,1058960), (36169948434793600,16404689,1196289)] ++ [
    (36169948434793600,13354509,70728), (70781333153792,10955000,140064), (36169948434793600,10134075,101892), (36169948434793600,13759816,135504), (36169948434793600,10349185,876546), (70781333153792,5161968,813184), (36169948434793600,14141057,1837058), (36169948434793600,14436009,1114258), (70781333153792,5036528,1327760), (36169948434793600,10442369,1647106), (70781333153792,4638704,1329792), (36169948434793600,9116219,527388), (36169948434793600,16418059,168976), (36169948434793600,13354824,70944), (70781333153792,12109272,526992), (70781333153792,9393272,410368), (36169948434793600,16263961,196720), (70781333153792,10840515,42504), (36169948434793600,12730025,264338), (36169948434793600,10048248,205185), (70781333153792,5032944,1581712), (36169948434793600,14562373,99424), (36169948434793600,16433361,675841), (36169948434793600,13753992,541196)] ++ [
    (36169948434793600,12744333,525388), (70781333153792,9268168,1122832), (36169948434793600,16321291,165928), (36169948434793600,14773003,2408), (36169948434793600,13758633,68226), (70781333153792,5151216,813072), (70781333153792,5133240,1331968), (70781333153792,11739896,1704224), (36169948434793600,14599816,1105924), (36169948434793600,15421721,39296), (36169948434793600,10435089,1458689), (36169948434793600,15421539,134336), (36169948434793600,12729997,263244), (70781333153792,5032902,1581640), (70781333153792,5036472,1327904), (70781333153792,10042312,286864), (36169948434793600,13759557,34016), (36169948434793600,13741672,67864), (70781333153792,10840312,143904), (36169948434793600,13713217,132400), (36169948434793600,14040593,1835041), (36169948434793600,13874245,35936), (70781333153792,11736515,1343560), (70781333153792,12198648,1069344)] ++ [
    (70781333153792,5419974,1615360), (70781333153792,5556166,1614400), (70781333153792,10833368,84608), (36169948434793600,13874497,137480), (36169948434793600,13811329,1073170), (36169948434793600,14563969,336386), (36169948434793600,13870696,68880), (70781333153792,12101880,267040)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (36169948434793600,13874497,137480), (36169948434793600,13758605,34372), (36169948434793600,16418969,337922), (36169948434793600,16274531,98528), (36169948434793600,13875729,274945), (36169948434793600,16418059,168976), (36169948434793600,13874280,68768), (36169948434793600,16275665,393985), (36169948434793600,14898443,5456), (36169948434793600,14899353,10882), (36169948434793600,10081337,1130636), (36169948434793600,16274699,164176), (36169948434793600,16418955,304132), (36169948434793600,9392593,1577249), (36169948434793600,16275609,328322), (36169948434793600,9395848,1581580), (36169948434793600,10138695,574497), (36169948434793600,10139080,675858), (36169948434793600,10155656,811076), (36169948434793600,9393167,1573970), (36169948434793600,16274713,197000), (70781333153792,5135921,1099968), (36169948434793600,10138744,608289), (36169948434793600,10083969,1327634)] ++ [
    (36169948434793600,16418073,202760), (36169948434793600,10081729,1196300), (36169948434793600,14898457,6536), (36169948434793600,16417891,101408), (36169948434793600,14898275,3296), (36169948434793600,13873489,143617), (36169948434793600,16275595,295492), (70781333153792,5135816,1139328), (36169948434793600,9392313,1575058), (70781333153792,5365185,1836608), (36169948434793600,14899339,9796), (70781333153792,5164936,612608), (36169948434793600,16419025,405505), (70781333153792,5135809,1106496), (36169948434793600,10137743,574476), (70781333153792,5620664,942336), (36169948434793600,4332923,77854), (36169948434793600,4591083,10541), (70781333153792,5422662,1611008), (36169948434793600,10155201,675976), (36169948434793600,5248943,197683), (36169948434793600,5905963,1345585), (70781333153792,5362616,1712896), (70781333153792,6868526,592065)] ++ [
    (36169948434793600,10080399,1097804), (36169948434793600,779037,279939), (36169948434793600,760221,529453), (36169948434793600,5302248,590614), (36169948434793600,5819947,819377), (70781333153792,5649336,1462784), (36169948434793600,4613679,19027), (36169948434793600,4671464,28822), (70781333153792,5652080,1263872), (70781333153792,5620678,843840), (36169948434793600,5279099,393374), (70781333153792,5365192,1837696), (36169948434793600,14899409,13057), (36169948434793600,5250973,172077), (36169948434793600,6232835,1381416), (36169948434793600,5830685,852297), (36169948434793600,10442257,1712641), (36169948434793600,10081400,1130657), (36169948434793600,4476255,1822), (70781333153792,13824083,1153027), (70781333153792,5365633,1705280), (36169948434793600,10141320,811020), (70781333153792,5623345,640128), (36169948434793600,2042649,1316976)] ++ [
    (70781333153792,14140994,688744), (70781333153792,5652038,1230080), (36169948434793600,2042061,1093770), (36169948434793600,4682027,22149), (36169948434793600,779051,280901), (70781333153792,14571074,25960), (36169948434793600,14563857,401921), (36169948434793600,10133599,101640), (70781333153792,6868848,659844), (36169948434793600,4672472,23090), (36169948434793600,10441753,1706120), (36169948434793600,5816573,720979), (70781333153792,6696872,88196), (36169948434793600,9393608,1577234), (70781333153792,13883009,917864), (36169948434793600,1811243,1214981), (36169948434793600,2041963,1123601), (36169948434793600,14562317,164944), (0,16,541632), (70781333153792,5623233,837120), (36169948434793600,5303851,590449), (36169948434793600,14561421,296004), (36169948434793600,9131577,43652), (70781333153792,5133240,1331968)] ++ [
    (36169948434793600,10441795,1639520), (36169948434793600,6000995,1159174), (36169948434793600,13761041,271105), (70781333153792,5133254,1328704), (70781333153792,5651912,1400960), (36169948434793600,10048199,172353), (36169948434793600,5250399,394270), (36169948434793600,13758633,68226), (0,32,1080320), (0,64,2064384), (70781333153792,5136257,1102144), (36169948434793600,9130191,70984), (36169948434793600,9131591,140865), (36169948434793600,10133711,169096), (36169948434793600,9130079,134344), (70781333153792,5135984,1198464), (36169948434793600,10137113,338016), (36169948434793600,9133656,141960), (36169948434793600,10155649,811138), (70781333153792,14141008,721584), (36169948434793600,4483325,2955)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (0,32,1080320), (0,64,2064384), (36169948434793600,10126431,101472), (36169948434793600,10155201,675976), (36169948434793600,10135160,338177), (36169948434793600,10129035,304644), (36169948434793600,10137785,608274), (36169948434793600,10137281,405584), (36169948434793600,10134215,169473), (36169948434793600,10141201,811041), (36169948434793600,4476255,1822), (36169948434793600,10126809,203016), (36169948434793600,4255587,262886), (36169948434793600,10155019,574736), (36169948434793600,2042061,1093770), (36169948434793600,4254691,131576), (36169948434793600,2049131,1131681), (36169948434793600,4612335,18765), (36169948434793600,1821393,1712673), (36169948434793600,1820301,1836108), (36169948434793600,5300701,557475), (36169948434793600,10134488,203266), (36169948434793600,2049677,1105996), (36169948434793600,1824977,1458945)] ++ [
    (36169948434793600,2042649,1316976), (36169948434793600,10135055,304258), (36169948434793600,4671464,28822), (36169948434793600,760221,529453), (36169948434793600,6088901,623370), (36169948434793600,4246767,33453), (36169948434793600,780395,150097), (36169948434793600,2041963,1123601), (70781333153792,14037968,1395328), (36169948434793600,5279099,393374), (36169948434793600,4619461,9954), (36169948434793600,1918581,102616), (36169948434793600,10139080,675858), (36169948434793600,10155096,608352), (36169948434793600,4603207,13067), (70781333153792,13824209,1248262), (36169948434793600,10126795,169232), (36169948434793600,1820497,1839393), (36169948434793600,10155656,811076), (70781333153792,13824083,1153027), (36169948434793600,4254187,131925), (36169948434793600,10154123,574980), (36169948434793600,1920233,329380), (36169948434793600,4483325,2955)] ++ [
    (36169948434793600,2053219,1576160), (36169948434793600,10129049,338434), (36169948434793600,4675832,15233), (70781333153792,14034552,1729056), (36169948434793600,10137288,405640), (70781333153792,3075716,185410), (36169948434793600,10137155,304400), (36169948434793600,4615128,25010), (36169948434793600,5816573,720979), (70781333153792,14034888,1663504), (70781333153792,14055048,1257520), (36169948434793600,10133627,101648), (36169948434793600,6081733,361058), (36169948434793600,779037,279939), (36169948434793600,4591083,10541), (36169948434793600,10137176,338184), (36169948434793600,1823843,1163488), (36169948434793600,4602941,9813), (36169948434793600,4246879,33566), (36169948434793600,5302248,590614), (36169948434793600,1812573,1377545), (36169948434793600,10155075,574624), (36169948434793600,10134467,169476), (36169948434793600,4613679,19027)] ++ [
    (36169948434793600,10135489,405572), (36169948434793600,10154193,676353), (70781333153792,14036568,1722500), (70781333153792,3532984,930336), (36169948434793600,10133599,101640), (36169948434793600,10155649,811138), (36169948434793600,5304131,655986), (36169948434793600,10154137,608770), (70781333153792,3078194,306200), (36169948434793600,5802475,426261), (36169948434793600,4590943,12382), (36169948434793600,5300477,557459), (36169948434793600,10133711,169096), (36169948434793600,10139073,675852), (36169948434793600,10137113,338016), (36169948434793600,10129105,406017), (36169948434793600,10141320,811020), (36169948434793600,4684008,28884), (36169948434793600,4684547,22184), (36169948434793600,5279659,197171), (36169948434793600,4614085,18190)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (0,64,2064384), (36169948434793600,4613679,19027), (36169948434793600,4589501,5293), (36169948434793600,4676035,14148), (36169948434793600,4615128,25010), (36169948434793600,1975925,101656), (36169948434793600,2042201,1189988), (36169948434793600,1992529,676385), (36169948434793600,2042061,1093770), (36169948434793600,1908067,409630), (36169948434793600,1920233,329380), (36169948434793600,2042649,1316976), (36169948434793600,4483325,2955), (36169948434793600,1992333,574988), (36169948434793600,2041963,1123601), (36169948434793600,1991913,608524), (36169948434793600,1927275,594513), (36169948434793600,1925987,663750), (36169948434793600,2053219,1576160), (36169948434793600,2040605,1088003), (36169948434793600,1993425,811297), (36169948434793600,1918581,102616), (36169948434793600,1991885,574738), (36169948434793600,4677400,15240)] ++ [
    (36169948434793600,1908011,344109), (36169948434793600,1920345,395028), (36169948434793600,1907115,213043), (36169948434793600,1975211,203267), (36169948434793600,4684008,28884), (36169948434793600,4705477,11874), (36169948434793600,2049369,1198348), (36169948434793600,2049131,1131681), (36169948434793600,1992011,675922), (36169948434793600,4476829,8557), (36169948434793600,4674019,7648), (36169948434793600,4675783,14145), (36169948434793600,1918889,198064), (36169948434793600,2049677,1105996), (36169948434793600,4655581,14603), (36169948434793600,4483549,5003), (36169948434793600,1992361,608786), (36169948434793600,1977577,338020), (36169948434793600,4702453,11462), (36169948434793600,4703797,7384), (36169948434793600,4673067,25777), (36169948434793600,4602941,9813), (36169948434793600,4682027,22149), (36169948434793600,2049355,1197330)] ++ [
    (36169948434793600,4683973,28874), (36169948434793600,4591349,3614), (36169948434793600,4483899,2552), (36169948434793600,4676056,15234), (36169948434793600,4603256,13077), (36169948434793600,4683819,26001), (36169948434793600,4671464,28822), (36169948434793600,4591083,10541), (36169948434793600,4684547,22184), (36169948434793600,4619461,9954), (36169948434793600,4655595,13589), (36169948434793600,4614008,21157)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩
  · let rs : List (ℕ × ℕ × ℕ) := [
    (70781333153792,16302314,596419), (70781333153792,15827882,1287189), (70781333153792,15263941,431720), (70781333153792,16307984,680372), (70781333153792,15100442,355849), (70781333153792,15940106,1876184), (70781333153792,15602034,1613062), (70781333153792,14785190,23101), (70781333153792,16188683,1511467), (70781333153792,15684256,478084), (70781333153792,16270989,557939), (70781333153792,14899402,25326), (70781333153792,16131976,1798672), (70781333153792,16032163,1770693), (70781333153792,14858417,16240), (70781333153792,15230796,426334), (70781333153792,15605877,1723459), (70781333153792,15057077,1102275), (70781333153792,15338078,1387564), (70781333153792,15238965,435239), (70781333153792,16114784,997520), (70781333153792,15918658,1889320), (70781333153792,15486289,623526), (70781333153792,14833553,31192)] ++ [
    (70781333153792,15026739,321232), (70781333153792,14752668,11947), (70781333153792,15418179,708968), (70781333153792,16026850,1413143), (70781333153792,15342278,1455880), (70781333153792,15356019,1625474), (70781333153792,15493793,230076), (70781333153792,15486093,721739), (70781333153792,15602090,1612933), (70781333153792,15156778,346825), (70781333153792,15755915,950835), (70781333153792,14837067,29997), (70781333153792,14854028,24154), (70781333153792,15647856,948864), (70781333153792,15665825,239676), (70781333153792,14891660,9722), (70781333153792,14758772,22119), (70781333153792,15081710,220545), (70781333153792,15685761,451424), (70781333153792,15152172,593497), (70781333153792,15226484,819689), (70781333153792,14889644,3927), (70781333153792,16147096,1988628), (70781333153792,15141658,340015)] ++ [
    (70781333153792,14765289,23443), (70781333153792,15534449,1355830), (70781333153792,14763889,29582), (70781333153792,16041494,1680080), (70781333153792,15418200,741808), (70781333153792,16016028,950359), (70781333153792,14723870,11182), (70781333153792,14802186,8162)]
    exact ⟨rs, by decide +kernel, by decide +kernel⟩

end SmallEight

namespace SmallEight

theorem normalize_last {n : ℕ} (G : SimpleGraph (Fin (n+1))) :
    ∃ (e : Equiv.Perm (Fin (n+1))) (k : Fin (n+1)), e (Fin.last n) = Fin.last n ∧
      ∀ i : Fin n, G.Adj (e i.castSucc) (e (Fin.last n)) ↔ i.val<k.val := by
  classical
  let P (i : Fin n) := G.Adj i.castSucc (Fin.last n)
  let k := Fintype.card {i : Fin n // P i}
  have small : k≤n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (Subtype.val : {i : Fin n // P i} → Fin n) Subtype.val_injective
  let first : {i : Fin n // i.val<k} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val,i.property⟩
      invFun := fun i => ⟨⟨i.val,i.isLt.trans_le small⟩,i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let front := first.trans (Fintype.equivFin {i : Fin n // P i}).symm
  let f : Equiv.Perm (Fin n) := front.extendSubtype
  have hit (i : Fin n) : P (f i) ↔ i.val<k := by
    constructor
    · intro hx
      by_contra miss
      exact front.extendSubtype_not_mem i miss hx
    · exact front.extendSubtype_mem i
  let e : Equiv.Perm (Fin (n+1)) := finSumFinEquiv.symm.trans
    ((Equiv.sumCongr f (Equiv.refl (Fin 1))).trans finSumFinEquiv)
  have fixed : e (Fin.last n) = Fin.last n := by simp [e]; rfl
  refine ⟨e,⟨k,Nat.lt_succ_of_le small⟩,fixed,?_⟩
  intro i
  have he : e i.castSucc=(f i).castSucc := by simp [e]; rfl
  rw [he,fixed]
  exact hit i

theorem low_bit (x i : ℕ) (hi : i<21) :
    (x % 2^21).testBit i = x.testBit i := by
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

theorem low_count_mask (x : ℕ) (k : Fin 8)
    (norm : ∀ i<7, x.testBit (21+i) = decide (i<k.val))
    (edges : ((Finset.range 28).filter fun i => x.testBit i = true).card=11) :
    ((Finset.range 21).filter (fun i => (x % 2^21).testBit i=true)).card = 11-k.val := by
  let count (k x : ℕ) := ((Finset.range k).filter (fun i => x.testBit i = true)).card
  have count_succ (k x : ℕ) : count (k+1) x = count k x + (if x.testBit k then 1 else 0) := by
    classical
    by_cases h : x.testBit k <;> simp [count,Finset.range_add_one,Finset.filter_insert,h,Finset.mem_filter]
  have tail (t : ℕ) (ht : t≤7) :
      count (21+t) x = count 21 x + min t k.val := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.add_succ,count_succ,ih (by omega),norm _ (by omega)]
      by_cases h : t<k.val
      · simp [h, Nat.min_eq_left (Nat.le_of_lt h),Nat.add_assoc]
      · simp [h,Nat.min_eq_right (Nat.le_of_not_lt h),Nat.min_eq_right (by omega : k.val≤t+1)]
  have allCount : count 28 x=11 := edges
  have allTail := tail 7 (by omega)
  rw [Nat.min_eq_right (by omega : k.val≤7), allCount] at allTail
  have low : count 21 (x % 2^21)=count 21 x := by
    unfold count
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases hi : i<21
    · rw [low_bit _ _ hi]
    · simp [hi]
  change count 21 (x % 2^21) = 11-k.val
  omega


theorem row_witness (G : SimpleGraph (Fin 8)) (conn : G.Connected) (k : ℕ)
    (norm : ∀ i : Fin 7, G.Adj i.castSucc (Fin.last 7) ↔ i.val<k)
    (x : ℕ) (bitSpec : ∀ i j : Fin 8, i<j → (x.testBit (j.val.choose 2+i.val)=true ↔ G.Adj i j))
    (r : ℕ × ℕ × ℕ) (avoid : ∀ idx<21, x.testBit idx=true → r.2.2.testBit idx=false) :
    let addr (i j : ℕ) := j.choose 2 + i
    let digit (p : ℕ) (i : Fin 8) : Fin 8 := ⟨p / 8 ^ i.val % 8, Nat.mod_lt _ (by decide)⟩

    let templateIndex (i j : Fin 8) := (min i j).val * 8 + (max i j).val

    let forbidden (k d : ℕ) (i j : Fin 8) : Bool :=
      if j.val=7 then decide (k ≤ i.val) else d.testBit (addr i j)

    let rowOK (k : ℕ) (r : ℕ × ℕ × ℕ) : Bool :=
      let (t,p,d) := r
      if t=0 then
        decide ((∃ i : Fin 8, p.testBit i=false) ∧ (∃ j : Fin 8, p.testBit j=true) ∧
          ∀ i j : Fin 8, i<j → p.testBit i ≠ p.testBit j → forbidden k d i j=true)
      else
        decide ((t=36169948434793600 ∨ t=70781333153792) ∧
          (∀ i j : Fin 8, i<j → digit p i ≠ digit p j) ∧
          ∀ i j : Fin 8, i<j → t.testBit (templateIndex (digit p i) (digit p j))=true →
            forbidden k d i j=true)
    rowOK k r=true → ∃ m ∈ ([36169948434793600,70781333153792] : List ℕ), ∃ e : Fin 8 ↪ Fin 8,
      ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*8+(max (e i) (e j)).val)=false := by
  intro addr digit templateIndex forbidden rowOK valid
  obtain ⟨t,p,d⟩ := r
  have absent {i j : Fin 8} (hij : i<j) (hG : G.Adj i j) : forbidden k d i j=false := by
    dsimp only [forbidden]
    split
    next h =>
      have hj : j=Fin.last 7 := Fin.ext h
      have hi : i.val<7 := lt_of_lt_of_eq hij h
      have right := (norm ⟨i.val,hi⟩).mp (hj ▸ hG)
      simpa only [decide_eq_false_iff_not,not_le] using right
    next h =>
      have nbound : j.val.choose 2+i.val < (j.val+1).choose 2 := by
        rw [Nat.choose_succ_succ' j.val 1, Nat.choose_one_right]
        change j.val.choose 2+i.val<j.val+j.val.choose 2
        omega
      have low : j.val+1≤7 := by have := j.isLt; omega
      exact avoid _ (nbound.trans_le (Nat.choose_le_choose 2 low))
        ((bitSpec i j hij).mpr hG)
  by_cases cut : t=0
  · simp only [rowOK,cut,if_true,decide_eq_true_eq] at valid
    obtain ⟨h0,h1,hmask⟩ := valid
    obtain ⟨i,j,hG,hne⟩ := SmallCover.Seven.seven_connected_cut conn (fun z : Fin 8 => p.testBit z) h0 h1
    exfalso
    rcases lt_or_gt_of_ne hG.ne with lt|gt
    · have := hmask i j lt hne
      simp [absent lt hG] at this
    · have := hmask j i gt (Ne.symm hne)
      simp [absent gt hG.symm] at this
  · simp only [rowOK,cut,if_false,decide_eq_true_eq] at valid
    obtain ⟨ht,hinj,hm⟩ := valid
    let e : Fin 8 ↪ Fin 8 := ⟨digit p, by
      intro i j eq
      by_contra ne
      rcases lt_or_gt_of_ne ne with lt|gt
      · exact hinj i j lt eq
      · exact hinj j i gt eq.symm⟩
    refine ⟨t, by simpa using ht, e, ?_⟩
    have forward {i j : Fin 8} (lt : i<j) (hG : G.Adj i j) :
        t.testBit (templateIndex (e i) (e j)) = false := by
      cases bit : t.testBit (templateIndex (e i) (e j)) with
      | false => rfl
      | true =>
        have h := hm i j lt bit
        simp [absent lt hG] at h
    intro i j hG
    rcases lt_or_gt_of_ne hG.ne with lt|gt
    · exact forward lt hG
    · simpa only [templateIndex,min_comm (e j) (e i),max_comm (e j) (e i)] using forward gt hG.symm


theorem eight_sparse (G : SimpleGraph (Fin 8)) (conn : G.Connected) (edges : G.edgeSet.ncard=11) :
    ∃ m ∈ ([36169948434793600,70781333153792] : List ℕ), ∃ e : Fin 8 ↪ Fin 8,
  ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*8+(max (e i) (e j)).val)=false := by
  obtain ⟨f,k,_,nf⟩ := normalize_last (n:=7) G
  let H := G.comap f
  let iso : H ≃g G := SimpleGraph.Iso.comap f G
  have hconn := iso.connected_iff.mpr conn
  have card : H.edgeSet.ncard=11 := by
    classical
    have h := iso.card_edgeFinset_eq
    simp only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
    exact h.trans edges
  obtain ⟨x,_,bits,edge_count⟩ := SmallCover.Seven.encoding_spec H
  have cutbit (i : ℕ) (hi : i<7) : x.testBit (21+i)=decide (i<k.val) := by
    have hit := (bits _ _ (Fin.castSucc_lt_last (⟨i,hi⟩ : Fin 7))).trans (nf ⟨i,hi⟩)
    change x.testBit (21+i)=true ↔ i<k.val at hit
    by_cases lt : i<k.val <;> simp_all
  have qty : ((Finset.range 28).filter fun i => x.testBit i=true).card=11 :=
    edge_count.symm.trans card
  let z := x % 2^21
  have cnt := low_count_mask x k cutbit qty
  let addr (i j : ℕ) := j.choose 2 + i
  let digit (p : ℕ) (i : Fin 8) : Fin 8 := ⟨p / 8 ^ i.val % 8, Nat.mod_lt _ (by decide)⟩

  let templateIndex (i j : Fin 8) := (min i j).val * 8 + (max i j).val

  let forbidden (k d : ℕ) (i j : Fin 8) : Bool :=
    if j.val=7 then decide (k ≤ i.val) else d.testBit (addr i j)

  let rowOK (k : ℕ) (r : ℕ × ℕ × ℕ) : Bool :=
    let (t,p,d) := r
    if t=0 then
      decide ((∃ i : Fin 8, p.testBit i=false) ∧ (∃ j : Fin 8, p.testBit j=true) ∧
        ∀ i j : Fin 8, i<j → p.testBit i ≠ p.testBit j → forbidden k d i j=true)
    else
      decide ((t=36169948434793600 ∨ t=70781333153792) ∧
        (∀ i j : Fin 8, i<j → digit p i ≠ digit p j) ∧
        ∀ i j : Fin 8, i<j → t.testBit (templateIndex (digit p i) (digit p j))=true →
          forbidden k d i j=true)
  let join (width a b : ℕ) := a % 2^width ||| (b <<< width)
  let free : ℕ → ℕ → ℕ := Nat.rec (fun _ => 1) (fun u rec mask =>
    let low := rec mask
    join (2^u) low (if mask.testBit u then 0 else low))
  let exactSize : ℕ → ℕ → ℕ := Nat.rec (fun q => if q=0 then 1 else 0) (fun u rec q =>
    join (2^u) (rec q) (if q=0 then 0 else rec (q-1)))
  obtain ⟨rs,valid,covered⟩ := eight_certificate k
  let ds := rs.map (fun r => r.2.2)
  have covered' : exactSize 21 (11-k.val) &&& ds.foldr (fun m a => free 21 m ||| a) 0 =
      exactSize 21 (11-k.val) := covered
  obtain ⟨d,hd,avoid⟩ := SmallCover.Seven.covers_spec 21 (11-k.val) z ds
    (Nat.mod_lt _ (by decide)) cnt covered'
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hd
  have goodr : rowOK k r = true := (List.all_eq_true.mp valid) _ hr
  obtain ⟨m,hm,e,good⟩ := row_witness H hconn k nf x bits r
    (fun i lt h => avoid i lt (by simpa only [z,low_bit _ _ lt] using h)) goodr
  refine ⟨m,hm,f.symm.toEmbedding.trans e,?_⟩
  intro i j hG
  apply good
  change G.Adj (f (f.symm i)) (f (f.symm j))
  simpa using hG

end SmallEight

open SimpleGraph Finset
namespace E1182Ten
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem first_host :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ∀ (D : SimpleGraph (Fin 10)) (edge : D.edgeSet.ncard = 11)
    (f : Fin 10 ↪ Fin 19)
    (copy : ∀ i j, (codeGraph 19 58280177927389562003304118167894045837298871419233698940907216524622014388169689497720).Adj (f i) (f j) → D.Adj i j),
    ∃ m ∈ [61500,58777656,1080899112137670672], codeGraph 10 m ⊑ D := by
  intro codeGraph
  let inst0 (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
    fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  let firstClass (i : Fin 19) : Fin 5 :=
    if i.val < 3 then 0 else if i.val < 7 then 1 else if i.val < 11 then 2
      else if i.val < 15 then 3 else 4

  let classNext (c : Fin 5) := c + 1

  let classAdj (c d : Fin 5) : Prop := classNext c = d ∨ classNext d = c

  let inst1 (c d : Fin 5) : Decidable (classAdj c d) := inferInstanceAs (Decidable (_ ∨ _))

  let seedSizes (a b c d e : ℕ) : Fin 5 → ℕ := ![a,b,c,d,e]

  let hostMask : ℕ := 58280177927389562003304118167894045837298871419233698940907216524622014388169689497720



  have first_adj : ∀ x y : Fin 19,
      classAdj (firstClass x) (firstClass y) ↔ (codeGraph 19 hostMask).Adj x y := by decide

  have host_sizes : ∀ i : Fin 5,
      Fintype.card {v : Fin 19 // firstClass v = i} = seedSizes 3 4 4 4 4 i := by decide

  let Slots (k : Fin 5 → ℕ) := (i : Fin 5) × Fin (k i)

  let EdgeSlots (k : Fin 5 → ℕ) := (i : Fin 5) × Fin (k i) × Fin (k (classNext i))

  have slot_edge_bound (k : Fin 5 → ℕ) (D : SimpleGraph (Fin 10))
      (u : Slots k ↪ Fin 10)
      (adj : ∀ x y : Slots k, classAdj x.1 y.1 → D.Adj (u x) (u y)) :
      ∑ i, k i * k (classNext i) ≤ D.edgeSet.ncard := by
    classical
    let g : EdgeSlots k → D.edgeSet := fun ⟨i,a,b⟩ =>
      ⟨s(u ⟨i,a⟩, u ⟨classNext i,b⟩), adj _ _ (Or.inl rfl)⟩
    have inj : Function.Injective g := by
      rintro ⟨i,a,b⟩ ⟨j,c,d⟩ he
      replace he := congrArg Subtype.val he
      change s(u ⟨i,a⟩, u ⟨classNext i,b⟩) = s(u ⟨j,c⟩, u ⟨classNext j,d⟩) at he
      rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have ea := u.injective ha
        have eb := u.injective hb
        have ij : i = j := congrArg Sigma.fst ea
        subst j
        simp only [Slots, Sigma.mk.inj_iff, heq_eq_eq, true_and] at ea eb
        subst c
        subst d
        rfl
      · have h₁ : i = classNext j := congrArg Sigma.fst (u.injective ha)
        have h₂ : classNext i = j := congrArg Sigma.fst (u.injective hb)
        have cyc : ∀ z : Fin 5, classNext (classNext z) ≠ z := by decide
        exact False.elim (cyc i (h₂ ▸ h₁.symm))
    have bound := Fintype.card_le_of_injective _ inj
    rw [Set.fintypeCard_eq_ncard] at bound
    simpa [EdgeSlots, Fintype.card_sigma, Fintype.card_prod] using bound

  have first_host_slots (D : SimpleGraph (Fin 10)) (f : Fin 10 ↪ Fin 19)
      (copy : ∀ i j, (codeGraph 19 58280177927389562003304118167894045837298871419233698940907216524622014388169689497720).Adj (f i) (f j) → D.Adj i j) :
      ∃ (k : Fin 5 → ℕ) (u : Slots k ↪ Fin 10),
        (∀ i, k i ≤ seedSizes 3 4 4 4 4 i) ∧ ∑ i, k i = 10 ∧
        (∑ i, k i * k (classNext i) ≤ D.edgeSet.ncard) ∧
        (∀ x y : Slots k, classAdj x.1 y.1 → D.Adj (u x) (u y)) := by
    let color : Fin 10 → Fin 5 := fun i => firstClass (f i)
    let k : Fin 5 → ℕ := fun i => Fintype.card {v // color v = i}
    let slots : Slots k ≃ Fin 10 := (Equiv.sigmaCongrRight
      (fun i => (Fintype.equivFin {v // color v = i}).symm)).trans (Equiv.sigmaFiberEquiv color)
    have colors (x : Slots k) : color (slots x) = x.1 :=
      ((Fintype.equivFin {v // color v = x.1}).symm x.2).property
    have adj (x y : Slots k) (h : classAdj x.1 y.1) : D.Adj (slots x) (slots y) := by
      apply copy
      apply (first_adj _ _).mp
      change classAdj (color (slots x)) (color (slots y))
      rwa [colors,colors]
    refine ⟨k, slots.toEmbedding, ?_, ?_, slot_edge_bound k D slots.toEmbedding adj, adj⟩
    · intro i
      let mapColor : {v // color v = i} ↪ {v // firstClass v = i} :=
        ⟨fun v => ⟨f v, v.property⟩, fun x y h => Subtype.ext (f.injective (congrArg Subtype.val h))⟩
      rw [←host_sizes]
      exact Fintype.card_le_of_injective _ mapColor.injective
    · simpa [Slots, Fintype.card_sigma] using Fintype.card_congr slots

  let seedMasks : List ℕ := [61500,58777656,1080899112137670672]

  let HasSeed (k : Fin 5 → ℕ) : Prop :=
    ∃ m ∈ seedMasks, ∃ e : Fin 10 ↪ Slots k, ∀ i j, (codeGraph 10 m).Adj i j →
      classAdj (e i).1 (e j).1

  let sparseProfiles : List (Fin 5 → ℕ) := [
    seedSizes 0 2 4 0 4,
    seedSizes 0 3 3 0 4,
    seedSizes 0 4 0 2 4,
    seedSizes 0 4 0 3 3,
    seedSizes 0 4 0 4 2,
    seedSizes 0 4 1 1 4,
    seedSizes 0 4 2 0 4,
    seedSizes 1 1 4 0 4,
    seedSizes 1 4 0 4 1,
    seedSizes 2 0 4 0 4,
    seedSizes 2 4 0 4 0,
    seedSizes 3 0 4 0 3,
    seedSizes 3 3 0 4 0]



  have count_cases :
      ∀ (a : Fin 4) (b c d e : Fin 5), a.val+b.val+c.val+d.val+e.val = 10 →
      a.val*b.val+b.val*c.val+c.val*d.val+d.val*e.val+e.val*a.val ≤ 11 →
      seedSizes a.val b.val c.val d.val e.val ∈ sparseProfiles := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide


  have profile_0 : HasSeed (seedSizes 0 2 4 0 4) := by
    let push : Fin 10 → Slots (seedSizes 0 2 4 0 4) := ![
      ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨2, ⟨0, by decide⟩⟩, ⟨2, ⟨1, by decide⟩⟩, ⟨2, ⟨2, by decide⟩⟩, ⟨2, ⟨3, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩]
    exact ⟨61500, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_1 : HasSeed (seedSizes 0 3 3 0 4) := by
    let push : Fin 10 → Slots (seedSizes 0 3 3 0 4) := ![
      ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨2, ⟨0, by decide⟩⟩, ⟨2, ⟨1, by decide⟩⟩, ⟨2, ⟨2, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩]
    exact ⟨58777656, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_2 : HasSeed (seedSizes 0 4 0 2 4) := by
    let push : Fin 10 → Slots (seedSizes 0 4 0 2 4) := ![
      ⟨3, ⟨0, by decide⟩⟩, ⟨3, ⟨1, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩]
    exact ⟨61500, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_3 : HasSeed (seedSizes 0 4 0 3 3) := by
    let push : Fin 10 → Slots (seedSizes 0 4 0 3 3) := ![
      ⟨3, ⟨0, by decide⟩⟩, ⟨3, ⟨1, by decide⟩⟩, ⟨3, ⟨2, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩]
    exact ⟨58777656, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_4 : HasSeed (seedSizes 0 4 0 4 2) := by
    let push : Fin 10 → Slots (seedSizes 0 4 0 4 2) := ![
      ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨3, ⟨0, by decide⟩⟩, ⟨3, ⟨1, by decide⟩⟩, ⟨3, ⟨2, by decide⟩⟩, ⟨3, ⟨3, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩]
    exact ⟨61500, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_5 : HasSeed (seedSizes 0 4 1 1 4) := by
    let push : Fin 10 → Slots (seedSizes 0 4 1 1 4) := ![
      ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩, ⟨2, ⟨0, by decide⟩⟩, ⟨3, ⟨0, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩]
    exact ⟨1080899112137670672, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_6 : HasSeed (seedSizes 0 4 2 0 4) := by
    let push : Fin 10 → Slots (seedSizes 0 4 2 0 4) := ![
      ⟨2, ⟨0, by decide⟩⟩, ⟨2, ⟨1, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩]
    exact ⟨61500, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_7 : HasSeed (seedSizes 1 1 4 0 4) := by
    let push : Fin 10 → Slots (seedSizes 1 1 4 0 4) := ![
      ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩, ⟨0, ⟨0, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨2, ⟨0, by decide⟩⟩, ⟨2, ⟨1, by decide⟩⟩, ⟨2, ⟨2, by decide⟩⟩, ⟨2, ⟨3, by decide⟩⟩]
    exact ⟨1080899112137670672, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_8 : HasSeed (seedSizes 1 4 0 4 1) := by
    let push : Fin 10 → Slots (seedSizes 1 4 0 4 1) := ![
      ⟨3, ⟨0, by decide⟩⟩, ⟨3, ⟨1, by decide⟩⟩, ⟨3, ⟨2, by decide⟩⟩, ⟨3, ⟨3, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨0, ⟨0, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩]
    exact ⟨1080899112137670672, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_9 : HasSeed (seedSizes 2 0 4 0 4) := by
    let push : Fin 10 → Slots (seedSizes 2 0 4 0 4) := ![
      ⟨0, ⟨0, by decide⟩⟩, ⟨0, ⟨1, by decide⟩⟩, ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨4, ⟨3, by decide⟩⟩, ⟨2, ⟨0, by decide⟩⟩, ⟨2, ⟨1, by decide⟩⟩, ⟨2, ⟨2, by decide⟩⟩, ⟨2, ⟨3, by decide⟩⟩]
    exact ⟨61500, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_10 : HasSeed (seedSizes 2 4 0 4 0) := by
    let push : Fin 10 → Slots (seedSizes 2 4 0 4 0) := ![
      ⟨0, ⟨0, by decide⟩⟩, ⟨0, ⟨1, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨1, ⟨3, by decide⟩⟩, ⟨3, ⟨0, by decide⟩⟩, ⟨3, ⟨1, by decide⟩⟩, ⟨3, ⟨2, by decide⟩⟩, ⟨3, ⟨3, by decide⟩⟩]
    exact ⟨61500, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_11 : HasSeed (seedSizes 3 0 4 0 3) := by
    let push : Fin 10 → Slots (seedSizes 3 0 4 0 3) := ![
      ⟨4, ⟨0, by decide⟩⟩, ⟨4, ⟨1, by decide⟩⟩, ⟨4, ⟨2, by decide⟩⟩, ⟨0, ⟨0, by decide⟩⟩, ⟨0, ⟨1, by decide⟩⟩, ⟨0, ⟨2, by decide⟩⟩, ⟨2, ⟨0, by decide⟩⟩, ⟨2, ⟨1, by decide⟩⟩, ⟨2, ⟨2, by decide⟩⟩, ⟨2, ⟨3, by decide⟩⟩]
    exact ⟨58777656, by decide, ⟨push, by decide⟩, by decide⟩


  have profile_12 : HasSeed (seedSizes 3 3 0 4 0) := by
    let push : Fin 10 → Slots (seedSizes 3 3 0 4 0) := ![
      ⟨0, ⟨0, by decide⟩⟩, ⟨0, ⟨1, by decide⟩⟩, ⟨0, ⟨2, by decide⟩⟩, ⟨1, ⟨0, by decide⟩⟩, ⟨1, ⟨1, by decide⟩⟩, ⟨1, ⟨2, by decide⟩⟩, ⟨3, ⟨0, by decide⟩⟩, ⟨3, ⟨1, by decide⟩⟩, ⟨3, ⟨2, by decide⟩⟩, ⟨3, ⟨3, by decide⟩⟩]
    exact ⟨58777656, by decide, ⟨push, by decide⟩, by decide⟩

  have profile_has_seed (k : Fin 5 → ℕ)
      (cap : ∀ i, k i ≤ seedSizes 3 4 4 4 4 i)
      (total : ∑ i, k i = 10) (edge : ∑ i, k i * k (classNext i) ≤ 11) : HasSeed k := by
    let a : Fin 4 := ⟨k 0, Nat.lt_succ_of_le (cap 0)⟩
    let b : Fin 5 := ⟨k 1, Nat.lt_succ_of_le (cap 1)⟩
    let c : Fin 5 := ⟨k 2, Nat.lt_succ_of_le (cap 2)⟩
    let d : Fin 5 := ⟨k 3, Nat.lt_succ_of_le (cap 3)⟩
    let e : Fin 5 := ⟨k 4, Nat.lt_succ_of_le (cap 4)⟩
    have members := count_cases a b c d e
    have ht : a.val+b.val+c.val+d.val+e.val = 10 := by
      simpa [a,b,c,d,e, Fin.sum_univ_succ, add_assoc] using total
    have he : a.val*b.val+b.val*c.val+c.val*d.val+d.val*e.val+e.val*a.val ≤ 11 := by
      simpa [a,b,c,d,e, Fin.sum_univ_succ, classNext, add_assoc] using edge
    have ks : seedSizes a.val b.val c.val d.val e.val = k := by
      funext i
      fin_cases i <;> rfl
    have hm := ks ▸ members ht he
    simp only [sparseProfiles, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact profile_0
    · exact profile_1
    · exact profile_2
    · exact profile_3
    · exact profile_4
    · exact profile_5
    · exact profile_6
    · exact profile_7
    · exact profile_8
    · exact profile_9
    · exact profile_10
    · exact profile_11
    · exact profile_12
  intro D edge f copy
  obtain ⟨k,u,cap,total,bound,adj⟩ := first_host_slots D f copy
  obtain ⟨m,hm,p,hp⟩ := profile_has_seed k cap total (edge ▸ bound)
  exact ⟨m, hm, ⟨⟨⟨u ∘ p, fun h => adj _ _ (hp _ _ h)⟩, u.injective.comp p.injective⟩⟩⟩
end E1182Ten

open SimpleGraph Finset
namespace E1182Ten
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem classified :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  let layer11 : List ℕ := [58777662,58777722,125886522,17238646842,68778254394,147573952589735190586,58777848,58843256,58908792,68778254456,137497731192,147573952589735190648,302231454903657352454264,442721857769088016440,618970167216642727184752696,619575073424768563045991038,619575073424768563045995070,619575073424768563046023742,619575073424768563046056510,619575073424768563046515262,619575073496826157083918910,619575220998721152722403902,619575073424768563046003230,619575073424768563046027806,619575073424768580225864222,619575073424768597405733406,619575073496826157083922974,619575073424768563046089246,619575073424768563113132574,61694,127102,192638,8450174,67170430,134279294,147573952589676474494,302231454903657293738110,25227326,75558974,35184380538942,70368752627774,147573952589684863038,201388094,68786647102,137506123838,147573952589743583294,302231454903657360846910,442721857769029300286,618970167216642727126036542,61948,127228,323836,8450300,67170556,268497148,147573952589676474620,295147905179352887548,618970019642690137449623804,8515708,134344828,302231454903657293803644,8581244,67301500,268628092,147573952589676605564,295147905179353018492,618970019642690137449754748,25227388,75559036,142667900,35184380539004,70368752627836,140737496805500,147573952589684863100,302231454903657302126716,201388156,68786647164,137506123900,147573952589743583356,302231454903657360846972,402714748,137573232764,275012186236,147573952589810692220,295147905179487105148,302231454903657427955836,618970019642690137583841404,442721857769029300348,302379028856246970151036,618970167216642727126036604,906694364710971881091196,92336188,17205096508,34384965692,68744704060,72057594063155260,147573952589701640252,209776700,68795035708,137514512444,35184447647804,70368819736636,140737563914300,147573952589751971900,302231454903657369235516,147573987774056951868,211106240983100,72127962790555708,144185556828483644,147574022958429040700,302231454974026046304316,442721857769037688892,618970167216642727134425148,469823548,68920864828,275079295036,147573952589877801020,295147905179554213948,618970019642690137650950204,140806275002428,147573952658463060028,302231454903726080323644,281612482834492,147573952727182536764,295147905316858949692,618970019642690274955685948,442721857769096409148,302379028856247037259836,618970167216642727193145404,906694364710971948199996,1033017668127734951996,302674176761426322976828,604905631665083616653372]
  ∀ (D : SimpleGraph (Fin 10)) (edge : D.edgeSet.ncard = 11)
    (_seed : ∃ e ∈ [61500,58777656,1080899112137670672], codeGraph 10 e ⊑ D),
    ∃ e ∈ layer11, Nonempty (codeGraph 10 e ≃g D) := by
  intro codeGraph layer11
  let inst0 (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
    fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have pullback_size {n : ℕ} (D : SimpleGraph (Fin n)) (b : Fin n ≃ Fin n) :
      (D.comap b).edgeSet.ncard = D.edgeSet.ncard := by
    exact Nat.card_congr (SimpleGraph.Iso.comap b D).mapEdgeSet

  have strict_edge {n : ℕ} {A D : SimpleGraph (Fin n)} (sub : A ⊑ D)
      (hsize : A.edgeSet.ncard < D.edgeSet.ncard) :
      ∃ (f : A.Copy D) (i j : Fin n), i < j ∧ ¬ A.Adj i j ∧ D.Adj (f i) (f j) := by
    obtain ⟨f⟩ := sub
    let b : Fin n ≃ Fin n := Equiv.ofBijective f f.injective.bijective_of_finite
    have need : ∃ i j, ¬ A.Adj i j ∧ D.Adj (f i) (f j) := by
      by_contra! h
      have eq : A = D.comap b := by
        ext i j
        exact ⟨f.toHom.map_rel',fun hd => Classical.byContradiction (fun no => h i j no hd)⟩
      have := pullback_size D b
      rw [←eq] at this
      omega
    obtain ⟨i,j,hn,hy⟩ := need
    by_cases lt : i < j
    · exact ⟨f,i,j,lt,hn,hy⟩
    · exact ⟨f,j,i,lt_of_le_of_ne (le_of_not_gt lt) (fun h => hy.ne (congrArg f h.symm)),
        fun h => hn h.symm,hy.symm⟩

  let pos10 (w : ℕ) (i : Fin 10) : Fin 10 :=
    ⟨((w >>> (4*i.val)) % 16) % 10,Nat.mod_lt _ (by decide)⟩

  let rowEntry (r : ℕ) (i j : Fin 10) : ℕ := (r >>> (48*(10*i.val+j.val))) % 2^48

  let validEntry (s : ℕ) (targets : List ℕ) (r : ℕ) (i j : Fin 10) : Prop :=
    let w := rowEntry r i j
    let k := w >>> 40
    let p := pos10 w
    k < targets.length ∧ (∀ u v : Fin 10, p u = p v → u=v) ∧
      ∀ u v : Fin 10, (codeGraph 10 (targets[k]!)).Adj u v →
        (codeGraph 10 s).Adj (p u) (p v) ∨ (p u=i ∧ p v=j) ∨ (p u=j ∧ p v=i)

  let inst1 (s : ℕ) (targets : List ℕ) (r : ℕ) (i j : Fin 10) :
      Decidable (validEntry s targets r i j) := by unfold validEntry; infer_instance

  let rowValid (s : ℕ) (targets : List ℕ) (r : ℕ) : Prop :=
    ∀ i j : Fin 10, i < j → ¬ (codeGraph 10 s).Adj i j → validEntry s targets r i j

  let inst2 (s : ℕ) (targets : List ℕ) (r : ℕ) : Decidable (rowValid s targets r) := by
    unfold rowValid; infer_instance

  have advance {s r : ℕ} {targets : List ℕ} {D : SimpleGraph (Fin 10)}
      (hsub : codeGraph 10 s ⊑ D) (small : (codeGraph 10 s).edgeSet.ncard < D.edgeSet.ncard)
      (table : rowValid s targets r) : ∃ t ∈ targets, codeGraph 10 t ⊑ D := by
    obtain ⟨f,i,j,lt,no,yes⟩ := strict_edge hsub small
    obtain ⟨bound,inj,edges⟩ := table i j lt no
    let w := rowEntry r i j
    let k := w >>> 40
    let p := pos10 w
    have goodmem : targets[k]! ∈ targets := by
      rw [getElem!_pos targets k bound]
      exact List.getElem_mem _
    refine ⟨_,goodmem,⟨⟨⟨fun a => f (p a),?_⟩,f.injective.comp inj⟩⟩⟩
    intro u v huv
    rcases edges u v huv with hh | ⟨he,hf⟩ | ⟨he,hf⟩
    · exact f.toHom.map_rel' hh
    · change D.Adj (f (pos10 w u)) (f (pos10 w v))
      simpa only [show pos10 w u=i from he,show pos10 w v=j from hf] using yes
    · change D.Adj (f (pos10 w u)) (f (pos10 w v))
      simpa only [show pos10 w u=j from he,show pos10 w v=i from hf] using yes.symm

  have exact_copy {n : ℕ} {A D : SimpleGraph (Fin n)} (sub : A ⊑ D)
      (size : A.edgeSet.ncard = D.edgeSet.ncard) : Nonempty (A ≃g D) := by
    obtain ⟨f⟩ := sub
    let b : Fin n ≃ Fin n := Equiv.ofBijective f f.injective.bijective_of_finite
    have le : A ≤ D.comap b := fun _ _ h => f.toHom.map_rel' h
    have sie := pullback_size D b
    have eq : A = D.comap b := by
      apply le_antisymm le
      by_contra hn
      have hlt : A < D.comap b := lt_of_le_not_ge le hn
      have := Set.ncard_lt_ncard (SimpleGraph.edgeSet_strict_mono hlt)
      omega
    exact ⟨eq ▸ SimpleGraph.Iso.comap b D⟩

  let layer8 : List ℕ := [61500]
  let layer9 : List ℕ := [58777656,1080899112137670672,61502,61564,8450108,67170364,147573952589676474428]
  let layer10 : List ℕ := [58777658,58777720,147573952589735190584,1080899112137670674,1080899112137670704,1080899112137670736,61566,8450110,67170366,147573952589676474430,61692,127100,192636,8450172,67170428,134279292,147573952589676474492,302231454903657293738108,25227324,75558972,35184380538940,70368752627772,147573952589684863036,201388092,68786647100,137506123836,147573952589743583292,302231454903657360846908,442721857769029300284,618970167216642727126036540]

  let cert8 : List ℕ := [0x67698543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068697543210069687543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068796543210069786543210069876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000058769432510059768432510059867432510059876432510000000000000000000000000000000000000000000000000000000000000000000000000058769532410059768532410059867532410059876532410049876325410000000000000000000000000000000000000000000000000000000000000058769542310059768542310059867542310059876542310049876425310049876524310000000000000000000000000000000000000000000000000058769543210059768543210059867543210059876543210049876435210049876534210049876543210000000000000000000000000000000000000038769543201039768543201039867543201039876543201000000000000000000000000000000000000000000000000000000000000000000000000038769543210039768543210039867543210039876543210000000000000000000000000000000000000000000000000029876543210000000000000]
  let cert9 : List ℕ := [0x27698543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028697543210029687543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028796543210029786543210029876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000018769210435019768210435019867210435019876210435000000000000000000000000000000000000000000000000000000000000000000000000018769210534019768210534019867210534019876210534009876210354000000000000000000000000000000000000000000000000000000000000018769210543019768210543019867210543019876210543009876210453009876210543000000000000000000000000000000000000000000000000018769543102019768543102019867543102019876543102000000000000000000000000000000000000000000000000000000000000000000000000018769543201019768543201019867543201019876543201000000000000000000000000000000000000009876543021000000000000000000000000018769543210019768543210019867543210019876543210000000000000000000000000000000000000009876543120009876543210000000000000,0x33210457698000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033210458697033210459687000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033210458796033210459786033210459876000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000043210458769043210459768043210459867043210459876000000000000000000000000000000000000000000000000000000000000000000000000058769542103059768542103059867542103059876542103049876542103000000000000000000000000000000000000000000000000000000000000058769543102059768543102059867543102059876543102049876543102000000000000039876541032000000000000000000000000000000000000058769543201059768543201059867543201059876543201049876543201000000000000039876542031039876543021000000000000000000000000058769543210059768543210059867543210059876543210049876543210000000000000039876542130039876543120039876543210000000000000,0x97698543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000098697543210099687543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000098796543210099786543210099876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000088769432510089768432510089867432510089876432510000000000000000000000000000000000000000000000000000000000000000000000000088769532410089768532410089867532410089876532410079876325410000000000000000000000000000000000000000000000000000000000000088769542310089768542310089867542310089876542310079876425310079876524310000000000000000000000000000000000000000000000000088769543210089768543210089867543210089876543210079876435210079876534210079876543210000000000000000000000000000000000000068769543201069768543201069867543201069876543201000000000000000000000000000000000000000000000000000000000000000000000000068769543210069768543210069867543210069876543210000000000000000000000000000000000000000000000000000000000000000000000000,0x1179865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001189765432101198765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001087965432101097865432101098765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000f87964325100f97864325100f98764325100e98764325100000000000000000000000000000000000000000000000000000000000000000000000000f87965324100f97865324100f98765324100e98765324100d98763254100000000000000000000000000000000000000000000000000000000000000f87965423100f97865423100f98765423100e98765423100d98764253100d98765243100000000000000000000000000000000000000000000000000f87965432100f97865432100f98765432100e98765432100d98764352100d98765342100d98765432100000000000000000000000000000000000000c87965432100c97865432100c98765432100b98765432100000000000000000000000000000000000000000000000000000000000000000000000000a87965432100a97865432100a9876543210000000000000000000000000000000000000000000000000000000000000069876543210000000000000,0x1676985432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001686975432101696875432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001687965432101697865432101698765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000001587694532101597684532101598674532101598764532100000000000000000000000000000000000000000000000000000000000000000000000001587695432101597685432101598675432101598765432101498765432100000000000000000000000000000000000000000000000000000000000001387695423101397685423101398675423101398765423101298764523101298765423100000000000000000000000000000000000000000000000001387695432101397685432101398675432101398765432101298764532101298765432100000000000000000000000000000000000000000000000000d87695432010d97685432010d98675432010d98765432010000000000000000000000000000000000000000000000000000000000000000000000000d87695432100d97685432100d98675432100d9876543210000000000000000000000000000000000000000000000000079876543210000000000000,0x1b79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b89765432101b98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a87965432101a97865432101a98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000001987964352101997864352101998764352101898764352100000000000000000000000000000000000000000000000000000000000000000000000001987965342101997865342101998765342101898765342101598763254100000000000000000000000000000000000000000000000000000000000001987965432101997865432101998765432101898765432101598764253101598765243100000000000000000000000000000000000000000000000001787965432101797865432101798765432100000000000001398764352101398765342101398765432100000000000000000000000000000000000000f87695432010f97685432010f98675432010e98765432010000000000000000000000000000000000000000000000000000000000000000000000000f87695432100f97685432100f98675432100e9876543210000000000000000000000000000000000000000000000000089876543210000000000000,0x1d98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c89675432101c98675432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c89765432101c98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b87694325101b97684325101a98674325101a98764325100000000000000000000000000000000000000000000000000000000000000000000000001b87695324101b97685324101a98675324101a98765324101698763254100000000000000000000000000000000000000000000000000000000000001b87695423101b97685423101a98675423101a98765423101698764253101698765243100000000000000000000000000000000000000000000000001b87695432101b97685432101a98675432101a9876543210169876435210169876534210169876543210000000000000000000000000000000000000118769543201119768543201109867543201109876543201000000000000000000000000000000000000000000000000000000000000000000000000118769543210119768543210109867543210109876543210000000000000000000000000000000000000000000000000099876543210000000000000]
  let cert10 : List ℕ := [0x57698543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058697543210059687543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058796543210059786543210059876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000048769435210049768435210049867435210049876435210000000000000000000000000000000000000000000000000000000000000000000000000048769534210049768534210049867534210049876534210039876354210000000000000000000000000000000000000000000000000000000000000048769543210049768543210049867543210049876543210039876453210039876543210000000000000000000000000000000000000000000000000028769543210029768543210029867543210029876543210000000000000000000000000000000000000000000000000000000000000000000000000018769543201019768543201019867543201019876543201000000000000000000000000000000000000009876543201000000000000000000000000018769543210019768543210019867543210019876543210000000000000000000000000000000000000009876543210000000000000000000000000,0xc79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c89765432100c98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b87965432100b97865432100b98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000a87964352100a97864352100a98764352100998764352100000000000000000000000000000000000000000000000000000000000000000000000000a87965342100a97865342100a98765342100998765342100498762103540000000000000000000000000000000000000000000000000000000000000a87965432100a97865432100a9876543210099876543210049876210453049876210543000000000000000000000000000000000000000000000000088796543120089786543120089876543120079876543120000000000000000000000000000000000000000000000000000000000000000000000000088796543210089786543210089876543210079876543210000000000000000000000000000000000000029876543021000000000000000000000000068796543210069786543210069876543210000000000000000000000000000000000000000000000000019876543120019876543210000000000000,0xe98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d89675432100d98675432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d89765432100d98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c87692104350c97682104350b98672104350b98762104350000000000000000000000000000000000000000000000000000000000000000000000000c87692105340c97682105340b98672105340b98762105340598762103540000000000000000000000000000000000000000000000000000000000000c87692105430c97682105430b98672105430b98762105430598762104530598762105430000000000000000000000000000000000000000000000000c87695431020c97685431020b98675431020b98765431020000000000000000000000000000000000000000000000000000000000000000000000000c87695432010c97685432010b98675432010b98765432010000000000000000000000000000000000000598765430210000000000000000000000000c87695432100c97685432100b98675432100b9876543210000000000000000000000000000000000000059876543120059876543210000000000000,0x1a57698321040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a58697321041a59687321040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a58796321041a59786321041a5987632104000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000105876932104105976832104105986732104105987632104000000000000000000000000000000000000000000000000000000000000000000000000195876923104195976823104195986723104195987623104154210398765000000000000000000000000000000000000000000000000000000000000195876932104195976832104195986732104195987632104154310298765000000000000185987632104000000000000000000000000000000000000175876932014175976832014175986732014175987632014144320198765000000000000165987623014165987632014000000000000000000000000175876932104175976832104175986732104175987632104144321098765000000000000165987623104165987632104000000000000000000000000,0x1043210769850000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001043210869751043210968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001043210879651043210978651043210987650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001358769321041359768321041359867321041359876321040000000000000000000000000000000000000000000000000000000000000000000000001242130876951242130976851242130986751242130987650f42130987650000000000000000000000000000000000000000000000000000000000001243120876951243120976851243120986751243120987650f43120987650000000000001541320987650000000000000000000000000000000000001243210876951243210976851243210986751243210987650f4321098765000000000000154231098765154321098765000000000000000000000000114321087695114321097685114321098675114321098765000000000000000000000000144213098765144312098765144321098765000000000000,0x1943210769850000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001943210869751943210968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001743210879651743210978651743210987650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001258769321041259768321041259867321041159876321040000000000000000000000000000000000000000000000000000000000000000000000001c58796213041c59786213041c59876213041b42130987651242103987650000000000000000000000000000000000000000000000000000000000001c58796312041c59786312041c59876312041b43120987651243102987650000000000001959876103240000000000000000000000000000000000001c58796321041c59786321041c59876321041b43210987651243201987650000000000001959876203141959876302140000000000000000000000001b58796321041b59786321041b5987632104000000000000114321098765000000000000175987621304175987631204175987632104000000000000,0x2479865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002489765432102498765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002387965432102397865432102398765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000002287964325102297864325102298764325102198764325100000000000000000000000000000000000000000000000000000000000000000000000002287965324102297865324102298765324102198765324102098763254100000000000000000000000000000000000000000000000000000000000002287965423102297865423102298765423102198765423102098764253102098765243100000000000000000000000000000000000000000000000002287965432102297865432102298765432102198765432102098764352102098765342102098765432100000000000000000000000000000000000001f87965432101f97865432101f98765432101e98765432100000000000000000000000000000000000000000000000000000000000000000000000001d87965432101d97865432101d9876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x297698543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000298697543210299687543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000298796543210299786543210299876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000288769453210289768453210289867453210289876453210000000000000000000000000000000000000000000000000000000000000000000000000288769543210289768543210289867543210289876543210279876543210000000000000000000000000000000000000000000000000000000000000268769542310269768542310269867542310269876542310259876452310259876542310000000000000000000000000000000000000000000000000268769543210269768543210269867543210269876543210259876453210259876543210000000000000000000000000000000000000000000000000208769543201209768543201209867543201209876543201000000000000000000000000000000000000000000000000000000000000000000000000208769543210209768543210209867543210209876543210000000000000000000000000000000000000000000000000000000000000000000000000,0x2e79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002e89765432102e98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002d87965432102d97865432102d98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000002c87964352102c97864352102c98764352102b98764352100000000000000000000000000000000000000000000000000000000000000000000000002c87965342102c97865342102c98765342102b98765342102898763254100000000000000000000000000000000000000000000000000000000000002c87965432102c97865432102c98765432102b98765432102898764253102898765243100000000000000000000000000000000000000000000000002a87965432102a97865432102a9876543210000000000000269876435210269876534210269876543210000000000000000000000000000000000000228769543201229768543201229867543201219876543201000000000000000000000000000000000000000000000000000000000000000000000000228769543210229768543210229867543210219876543210000000000000000000000000000000000000000000000000000000000000000000000000,0x3098765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002f89675432102f98675432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002f89765432102f98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002e87694325102e97684325102d98674325102d98764325100000000000000000000000000000000000000000000000000000000000000000000000002e87695324102e97685324102d98675324102d98765324102998763254100000000000000000000000000000000000000000000000000000000000002e87695423102e97685423102d98675423102d98765423102998764253102998765243100000000000000000000000000000000000000000000000002e87695432102e97685432102d98675432102d9876543210299876435210299876534210299876543210000000000000000000000000000000000000248769543201249768543201239867543201239876543201000000000000000000000000000000000000000000000000000000000000000000000000248769543210249768543210239867543210239876543210000000000000000000000000000000000000000000000000000000000000000000000000,0x3998765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003889675432103898675432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003889765432103898765432103798765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000003689764325103698764325103598674325103598764325100000000000000000000000000000000000000000000000000000000000000000000000003689765324103698765324103598675324103598765324103498763254100000000000000000000000000000000000000000000000000000000000003689765423103698765423103598675423103598765423103498764253103498765243100000000000000000000000000000000000000000000000003689765432103698765432103598675432103598765432103498764352103498765342103498765432100000000000000000000000000000000000003389765432103398765432103298675432103298765432100000000000000000000000000000000000000000000000000000000000000000000000003189765432103198765432100000000000000000000000000000000000000000000000000000000000000000000000001d9876543210000000000000,0x3c79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c89765432103c98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003b87954326103b97854326103b98754326100000000000000000000000000000000000000000000000000000000000000000000000000000000000003b87964325103b97864325103b98764325103a98743265100000000000000000000000000000000000000000000000000000000000000000000000003b87965324103b97865324103b98765324103a98753264103a98763254100000000000000000000000000000000000000000000000000000000000003b87965423103b97865423103b98765423103a98754263103a98764253103a98765243100000000000000000000000000000000000000000000000003b87965432103b97865432103b98765432103a98754362103a98764352103a98765342103a98765432100000000000000000000000000000000000003287965432013297865432013298765432010000000000000000000000000000000000000000000000000000000000000000000000000000000000003287965432103297865432103298765432100000000000000000000000000000000000000000000000000000000000001e9876543210000000000000,0x4298765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004189675432014198675432010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004189765432104198765432104098765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000003f89764325103f98764325103e98674325013e98764325100000000000000000000000000000000000000000000000000000000000000000000000003f89765324103f98765324103e98675324013e98765324103d98763254100000000000000000000000000000000000000000000000000000000000003f89765423103f98765423103e98675423013e98765423103d98764253103d98765243100000000000000000000000000000000000000000000000003f89765432103f98765432103e98675432013e98765432103d98764352103d98765342103d98765432100000000000000000000000000000000000003386975432013396875432010000000000003298765432010000000000000000000000000000000000000000000000000000000000000000000000003387965432103397865432103298675432100000000000000000000000000000000000000000000000000000000000001f9876543210000000000000,0x4a79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004a89765432104a98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004987965432104997865432104998765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000004887964532104897864532104898764532104798764532100000000000000000000000000000000000000000000000000000000000000000000000004887965432104897865432104898765432104798765432104698765432100000000000000000000000000000000000000000000000000000000000004587965423104597865423104598765423104498765423104398764523104398765423100000000000000000000000000000000000000000000000004587965432104597865432104598765432104498765432104398764532104398765432100000000000000000000000000000000000000000000000003d87965432103d97865432103d98765432103a9876543210000000000000000000000000000000000000000000000000000000000000000000000000348796543210349786543210349876543210000000000000000000000000000000000000000000000000000000000000209876543210000000000000,0x4f79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004f89765432104f98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e87965432104e97865432104e98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000004d87964352104d97864352104d98764352104c98764352100000000000000000000000000000000000000000000000000000000000000000000000004d87965342104d97865342104d98765342104c98765342104798763254100000000000000000000000000000000000000000000000000000000000004d87965432104d97865432104d98765432104c98765432104798764253104798765243100000000000000000000000000000000000000000000000004b87965432104b97865432104b98765432100000000000004498764352104498765342104498765432100000000000000000000000000000000000003e87965432103e97865432103e98765432103a9875436210000000000000000000000000000000000000000000000000000000000000000000000000358796543210359786543210359876543210000000000000000000000000000000000000000000000000000000000000219876543210000000000000,0x5698765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005589765432105598765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005489765432105498765432105398765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000005289764352105298764352105198764352104d98764325100000000000000000000000000000000000000000000000000000000000000000000000005289765342105298765342105198765342104d98765324104898763254100000000000000000000000000000000000000000000000000000000000005289765432105298765432105198765432104d98765423104898764253104898765243100000000000000000000000000000000000000000000000005089765432105098765432100000000000004b98765432104598764352104598765342104598765432100000000000000000000000000000000000003f87965432103f97865432103e98675432013b9876543210000000000000000000000000000000000000000000000000000000000000000000000000368796543210369786543210359867543210000000000000000000000000000000000000000000000000000000000000229876543210000000000000,0x5998765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005889765432105898765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005789765432105798765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005487964325105497864325105398764325104e98764325100000000000000000000000000000000000000000000000000000000000000000000000005487965324105497865324105398765324104e98765324104998763254100000000000000000000000000000000000000000000000000000000000005487965423105497865423105398765423104e98765423104998764253104998765243100000000000000000000000000000000000000000000000005487965432105497865432105398765432104e98765432104998764352104998765342104998765432100000000000000000000000000000000000004187965432104197865432104098765432103b9875432610000000000000000000000000000000000000000000000000000000000000000000000000388796543210389786543210379876543210000000000000000000000000000000000000000000000000000000000000239876543210000000000000,0x5a97865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005a98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005987965432105897865432105898765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000005687964325105597864325105598764325104f98764325100000000000000000000000000000000000000000000000000000000000000000000000005687965324105597865324105598765324104f98765324104a98763254100000000000000000000000000000000000000000000000000000000000005687965423105597865423105598765423104f98765423104a98764253104a98765243100000000000000000000000000000000000000000000000005687965432105597865432105598765432104f98765432104a98764352104a98765342104a98765432100000000000000000000000000000000000004287965432104197685432014198675432013c9876543210000000000000000000000000000000000000000000000000000000000000000000000000398796543210389768543210389867543210000000000000000000000000000000000000000000000000000000000000249876543210000000000000,0x6076985432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006086975432106096875432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006087965432106097865432106098765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000005f87695432105f97685432105f98675432105f98765432100000000000000000000000000000000000000000000000000000000000000000000000005e87695342105e97685342105e98675342105e98765342105d98765342100000000000000000000000000000000000000000000000000000000000005e87695432105e97685432105e98675432105e98765432105d98765432105c98765432100000000000000000000000000000000000000000000000005b87695432105b97685432105b98675432105b9876543210009876543102000000000000000000000000000000000000000000000000000000000000438769543201439768543201439867543201439876543201000000000000000000000000000000000000000000000000000000000000000000000000438769543210439768543210439867543210439876543210000000000000000000000000000000000000000000000000259876543210000000000000,0x6879865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006889765432106898765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006787965432106797865432106798765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000006687964532106697864532106698764532106598764532100000000000000000000000000000000000000000000000000000000000000000000000006687965432106697865432106698765432106598765432106498765432100000000000000000000000000000000000000000000000000000000000006387965432106397865432106398765432106298765432105e98764523105e98765423100000000000000000000000000000000000000000000000006187965432106197865432106198765432100000000000005b98764532105b9876543210000000000000000000000000000000000000000000000000458769543201459768543201459867543201449876543201000000000000000000000000000000000000000000000000000000000000000000000000458769543210459768543210459867543210449876543210000000000000000000000000000000000000000000000000269876543210000000000000,0x6976985432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006986975432106996875432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006987965432106997865432106998765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000006487693245106497683245106498673245106498763245100000000000000000000000000000000000000000000000000000000000000000000000006487693254106497683254106498673254106498763254100000000000000000000000000000000000000000000000000000000000000000000000006487695423106497685423106498675423106498765423105d98764253105d98765243100000000000000000000000000000000000000000000000006487695432106497685432106498675432106498765432105d98764352105d9876534210000000000000000000000000000000000000000000000000468769543201469768543201469867543201469876543201000000000000000000000000000000000000000000000000000000000000000000000000468769543210469768543210469867543210469876543210000000000000000000000000000000000000000000000000279876543210000000000000,0x6e79865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006e89765432106e98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006d87965432106d97865432106d98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000006c87965432106c97865432106c98765432106b98765432100000000000000000000000000000000000000000000000000000000000000000000000006a87965432106a97865432106a98765432100000000000006498763254100000000000000000000000000000000000000000000000000000000000006687695423106697685423106698675423106598765423105f98764523105e98765243100000000000000000000000000000000000000000000000006687695432106697685432106698675432106598765432105f98764532105e9876534210000000000000000000000000000000000000000000000000488769543201489768543201489867543201479876543201000000000000000000000000000000000000000000000000000000000000000000000000488769543210489768543210489867543210479876543210000000000000000000000000000000000000000000000000289876543210000000000000,0x7098765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006f89675432106f98675432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006f89765432106f98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006e87694532106e97684532106d98674532106d98764532100000000000000000000000000000000000000000000000000000000000000000000000006e87695432106e97685432106d98675432106d98765432106998765432100000000000000000000000000000000000000000000000000000000000006887695423106897685423106798675423106798765423106098764523106098765423100000000000000000000000000000000000000000000000006887695432106897685432106798675432106798765432106098764532106098765432100000000000000000000000000000000000000000000000004a87695432014a97685432014998675432014998765432010000000000000000000000000000000000000000000000000000000000000000000000004a87695432104a9768543210499867543210499876543210000000000000000000000000000000000000000000000000299876543210000000000000,0x7698765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007589675432107598675432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007589765432107598765432107498765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000007389764352107398764352107298674352107298764352100000000000000000000000000000000000000000000000000000000000000000000000007389765342107398765342107298675342107298765342106a98763254100000000000000000000000000000000000000000000000000000000000007389765432107398765432107298675432107298765432106a98764253106a98765243100000000000000000000000000000000000000000000000007189765432107198765432100000000000000000000000006198764352106198765342106198765432100000000000000000000000000000000000005087695432015097685432014b98675432014b98765432010000000000000000000000000000000000000000000000000000000000000000000000005087695432105097685432104b98675432104b98765432100000000000000000000000000000000000000000000000002a9876543210000000000000,0x7979865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007989765432107998765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007887965432107897865432107898765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000007787964532107797864532107798764532100798745326100000000000000000000000000000000000000000000000000000000000000000000000007787965432107797865432107798765432100798754326106b98763254100000000000000000000000000000000000000000000000000000000000007287965423107297865423107298765423100000000000006598764253106598765243100000000000000000000000000000000000000000000000007287965432107297865432107298765432100000000000006598764352106598765342106298765432100000000000000000000000000000000000005187695432015197685432015198675432014c98765432010000000000000000000000000000000000000000000000000000000000000000000000005187695432105197685432105198675432104c98765432100000000000000000000000000000000000000000000000002b9876543210000000000000,0x7d98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007c89675423107c98675423100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007c89765432107c98765432107b98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000007a89764532107a98764532107798674253107798764352100000000000000000000000000000000000000000000000000000000000000000000000007a89765432107a98765432107798675243107798765342106c98763254100000000000000000000000000000000000000000000000000000000000007386975423107396875423100000000000007298765423106698674253106698675243100000000000000000000000000000000000000000000000007387965432107397865432107298675432100000000000006698764352106698765342106398765432100000000000000000000000000000000000005287695432015297685432014d98675423014d98765432010000000000000000000000000000000000000000000000000000000000000000000000005287695432105297685432104d98675423104d98765432100000000000000000000000000000000000000000000000002c9876543210000000000000,0x8098765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f89765432107f98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007e89765432107e98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007c87964352107c97864352107b98764352107898764352100000000000000000000000000000000000000000000000000000000000000000000000007c87965342107c97865342107b98765342107898765342106d98763254100000000000000000000000000000000000000000000000000000000000007c87965432107c97865432107b98765432107898765432106d98764253106d98765243100000000000000000000000000000000000000000000000007587965432107597865432107498765432100000000000006798764352106798765342106798765432100000000000000000000000000000000000005587695432015597685432015398675432014e98765432010000000000000000000000000000000000000000000000000000000000000000000000005587695432105597685432105398675432104e98765432100000000000000000000000000000000000000000000000002d9876543210000000000000,0x8197865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008198765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008087965432107f97865432107f98765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000007d87964352107c97684325107c98674325107998764352100000000000000000000000000000000000000000000000000000000000000000000000007d87965342107c97685324107c98675324107998765342106e98763254100000000000000000000000000000000000000000000000000000000000007d87965432107c97685423107c98675423107998765432106e98764253106e98765243100000000000000000000000000000000000000000000000007687965432107597685432107598675432100000000000006898764352106898765342106898765432100000000000000000000000000000000000005687695432015497685432015498675432014f98765432010000000000000000000000000000000000000000000000000000000000000000000000005687695432105497685432105498675432104f98765432100000000000000000000000000000000000000000000000002e9876543210000000000000,0x8497865432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008498765432108398765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008298765432100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008187694325107f97684325107f98674325107e98764325100000000000000000000000000000000000000000000000000000000000000000000000008187695324107f97685324107f98675324107e98765324106f98763254100000000000000000000000000000000000000000000000000000000000008187695423107f97685423107f98675423107e98765423106f98764253106f98765243100000000000000000000000000000000000000000000000008187695432107f97685432107f98675432107e98765432106f98764352106f98765342106f98765432100000000000000000000000000000000000005a87695432015897685432015898675432015798765432010000000000000000000000000000000000000000000000000000000000000000000000005a87695432105897685432105898675432105798765432100000000000000000000000000000000000000000000000002f9876543210000000000000,0x848697543210849687543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000848796543210849786543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000807689432510807698432510809867432510809876432510000000000000000000000000000000000000000000000000000000000000000000000000807689532410807698532410809867532410809876532410709876325410000000000000000000000000000000000000000000000000000000000000807689542310807698542310809867542310809876542310709876425310709876524310000000000000000000000000000000000000000000000000807689543210807698543210809867543210809876543210709876435210709876534210709876543210000000000000000000000000000000000000597689543201597698543201599867543201599876543201000000000000000000000000000000000000000000000000000000000000000000000000597689543210597698543210599867543210599876543210000000000000000000000000000000000000000000000000309876543210000000000000]

  let checkedLayer (k : ℕ) (xs targets certs : List ℕ) : Prop :=
    ∀ i : Fin xs.length, let e := xs[i.val]
      (codeGraph 10 e).edgeFinset.card = k ∧ rowValid e targets certs[i.val]!

  let inst3 (k : ℕ) (xs targets certs : List ℕ) : Decidable (checkedLayer k xs targets certs) := by
    unfold checkedLayer
    infer_instance

  have step_layer {k : ℕ} {xs targets certs : List ℕ} {D : SimpleGraph (Fin 10)}
      (check : checkedLayer k xs targets certs) (more : k < D.edgeSet.ncard)
      (embedded : ∃ e ∈ xs, codeGraph 10 e ⊑ D) :
      ∃ t ∈ targets, codeGraph 10 t ⊑ D := by
    obtain ⟨e,mem,copy⟩ := embedded
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem mem
    obtain ⟨card,valid⟩ := check ⟨i,hi⟩
    apply advance copy _ valid
    rw [Set.ncard_eq_toFinset_card']
    exact card.trans_lt more


  let rowOK (k : ℕ) (xs targets certs : List ℕ) (index : ℕ) : Prop :=
    (codeGraph 10 xs[index]!).edgeFinset.card = k ∧
      (targets ≠ [] → rowValid xs[index]! targets certs[index]!)

  let rowsOK (k : ℕ) (xs targets certs : List ℕ) (start count : ℕ) : Prop :=
    ∀ i : Fin count, rowOK k xs targets certs (start+i.val)

  let inst4 (k : ℕ) (xs targets certs : List ℕ) (s n : ℕ) : Decidable (rowsOK k xs targets certs s n) := by
    unfold rowsOK rowOK
    infer_instance

  have join_rows {k : ℕ} {xs targets certs : List ℕ} {s a b : ℕ}
      (l : rowsOK k xs targets certs s a) (r : rowsOK k xs targets certs (s+a) b) :
      rowsOK k xs targets certs s (a+b) := by
    intro i
    by_cases hi : i.val < a
    · exact l ⟨i.val,hi⟩
    · have hi' := i.isLt
      have v := r ⟨i.val-a, by omega⟩
      change rowOK k xs targets certs (s+a+(i.val-a)) at v
      rwa [show s+a+(i.val-a)=s+i.val by omega] at v

  have checked_of_rows {k : ℕ} {xs targets certs : List ℕ} (ne : targets ≠ [])
      (ch : rowsOK k xs targets certs 0 xs.length) : checkedLayer k xs targets certs := by
    intro i
    have h := ch i
    change rowOK k xs targets certs (0+i.val) at h
    unfold rowOK at h
    rw [Nat.zero_add,getElem!_pos xs i.val i.isLt] at h
    exact ⟨h.1,h.2 ne⟩

  have piece8_0 : rowsOK 8 layer8 layer9 cert8 0 1 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer8,layer9,cert8]; decide +kernel
  have piece9_0 : rowsOK 9 layer9 layer10 cert9 0 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer9,layer10,cert9]; decide +kernel
  have piece9_2 : rowsOK 9 layer9 layer10 cert9 2 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer9,layer10,cert9]; decide +kernel
  have piece9_4 : rowsOK 9 layer9 layer10 cert9 4 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer9,layer10,cert9]; decide +kernel
  have piece9_6 : rowsOK 9 layer9 layer10 cert9 6 1 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer9,layer10,cert9]; decide +kernel
  have piece10_0 : rowsOK 10 layer10 layer11 cert10 0 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_2 : rowsOK 10 layer10 layer11 cert10 2 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_4 : rowsOK 10 layer10 layer11 cert10 4 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_6 : rowsOK 10 layer10 layer11 cert10 6 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_8 : rowsOK 10 layer10 layer11 cert10 8 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_10 : rowsOK 10 layer10 layer11 cert10 10 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_12 : rowsOK 10 layer10 layer11 cert10 12 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_14 : rowsOK 10 layer10 layer11 cert10 14 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_16 : rowsOK 10 layer10 layer11 cert10 16 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_18 : rowsOK 10 layer10 layer11 cert10 18 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_20 : rowsOK 10 layer10 layer11 cert10 20 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_22 : rowsOK 10 layer10 layer11 cert10 22 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_24 : rowsOK 10 layer10 layer11 cert10 24 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_26 : rowsOK 10 layer10 layer11 cert10 26 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece10_28 : rowsOK 10 layer10 layer11 cert10 28 2 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer10,layer11,cert10]; decide +kernel
  have piece11_0 : rowsOK 11 layer11 [] [] 0 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_11 : rowsOK 11 layer11 [] [] 11 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_22 : rowsOK 11 layer11 [] [] 22 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_33 : rowsOK 11 layer11 [] [] 33 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_44 : rowsOK 11 layer11 [] [] 44 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_55 : rowsOK 11 layer11 [] [] 55 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_66 : rowsOK 11 layer11 [] [] 66 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_77 : rowsOK 11 layer11 [] [] 77 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_88 : rowsOK 11 layer11 [] [] 88 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_99 : rowsOK 11 layer11 [] [] 99 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_110 : rowsOK 11 layer11 [] [] 110 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_121 : rowsOK 11 layer11 [] [] 121 11 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel
  have piece11_132 : rowsOK 11 layer11 [] [] 132 1 := by apply of_decide_eq_true; dsimp only [inst4,inst3,inst2,inst1,inst0,rowsOK,rowOK,rowValid,validEntry,pos10,rowEntry,codeGraph,layer11]; decide +kernel

  have allRows8 : rowsOK 8 layer8 layer9 cert8 0 1 := piece8_0
  have good8 : checkedLayer 8 layer8 layer9 cert8 := checked_of_rows (by decide) allRows8
  have allRows9 : rowsOK 9 layer9 layer10 cert9 0 7 := (join_rows (s:=0) (a:=2) (b:=5) piece9_0 (join_rows (s:=2) (a:=2) (b:=3) piece9_2 (join_rows (s:=4) (a:=2) (b:=1) piece9_4 piece9_6)))
  have good9 : checkedLayer 9 layer9 layer10 cert9 := checked_of_rows (by decide) allRows9
  have allRows10 : rowsOK 10 layer10 layer11 cert10 0 30 := (join_rows (s:=0) (a:=2) (b:=28) piece10_0 (join_rows (s:=2) (a:=2) (b:=26) piece10_2 (join_rows (s:=4) (a:=2) (b:=24) piece10_4 (join_rows (s:=6) (a:=2) (b:=22) piece10_6 (join_rows (s:=8) (a:=2) (b:=20) piece10_8 (join_rows (s:=10) (a:=2) (b:=18) piece10_10 (join_rows (s:=12) (a:=2) (b:=16) piece10_12 (join_rows (s:=14) (a:=2) (b:=14) piece10_14 (join_rows (s:=16) (a:=2) (b:=12) piece10_16 (join_rows (s:=18) (a:=2) (b:=10) piece10_18 (join_rows (s:=20) (a:=2) (b:=8) piece10_20 (join_rows (s:=22) (a:=2) (b:=6) piece10_22 (join_rows (s:=24) (a:=2) (b:=4) piece10_24 (join_rows (s:=26) (a:=2) (b:=2) piece10_26 piece10_28))))))))))))))
  have good10 : checkedLayer 10 layer10 layer11 cert10 := checked_of_rows (by decide) allRows10
  have allRows11 : rowsOK 11 layer11 [] [] 0 133 := (join_rows (s:=0) (a:=11) (b:=122) piece11_0 (join_rows (s:=11) (a:=11) (b:=111) piece11_11 (join_rows (s:=22) (a:=11) (b:=100) piece11_22 (join_rows (s:=33) (a:=11) (b:=89) piece11_33 (join_rows (s:=44) (a:=11) (b:=78) piece11_44 (join_rows (s:=55) (a:=11) (b:=67) piece11_55 (join_rows (s:=66) (a:=11) (b:=56) piece11_66 (join_rows (s:=77) (a:=11) (b:=45) piece11_77 (join_rows (s:=88) (a:=11) (b:=34) piece11_88 (join_rows (s:=99) (a:=11) (b:=23) piece11_99 (join_rows (s:=110) (a:=11) (b:=12) piece11_110 (join_rows (s:=121) (a:=11) (b:=1) piece11_121 piece11_132))))))))))))
  have good11 : ∀ i : Fin layer11.length, (codeGraph 10 layer11[i.val]).edgeFinset.card = 11 := by
    intro i
    have h := allRows11 i
    change rowOK 11 layer11 [] [] (0+i.val) at h
    unfold rowOK at h
    rw [Nat.zero_add,getElem!_pos layer11 i.val i.isLt] at h
    exact h.1
  intro D edge seed
  obtain ⟨s,hs,sub⟩ := seed
  have after9 : ∃ e ∈ layer9, codeGraph 10 e ⊑ D := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact step_layer good8 (by omega) ⟨61500,by decide,sub⟩
    · exact ⟨58777656,by decide,sub⟩
    · exact ⟨1080899112137670672,by decide,sub⟩
  obtain ⟨e,he,copy⟩ := step_layer good10 (by omega) (step_layer good9 (by omega) after9)
  refine ⟨e,he,exact_copy copy ?_⟩
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem he
  rw [edge,Set.ncard_eq_toFinset_card']
  exact good11 ⟨i,hi⟩
end E1182Ten

open SimpleGraph Finset
namespace E1182Ten
set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem host_family :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  let layer11 : List ℕ := [58777662,58777722,125886522,17238646842,68778254394,147573952589735190586,58777848,58843256,58908792,68778254456,137497731192,147573952589735190648,302231454903657352454264,442721857769088016440,618970167216642727184752696,619575073424768563045991038,619575073424768563045995070,619575073424768563046023742,619575073424768563046056510,619575073424768563046515262,619575073496826157083918910,619575220998721152722403902,619575073424768563046003230,619575073424768563046027806,619575073424768580225864222,619575073424768597405733406,619575073496826157083922974,619575073424768563046089246,619575073424768563113132574,61694,127102,192638,8450174,67170430,134279294,147573952589676474494,302231454903657293738110,25227326,75558974,35184380538942,70368752627774,147573952589684863038,201388094,68786647102,137506123838,147573952589743583294,302231454903657360846910,442721857769029300286,618970167216642727126036542,61948,127228,323836,8450300,67170556,268497148,147573952589676474620,295147905179352887548,618970019642690137449623804,8515708,134344828,302231454903657293803644,8581244,67301500,268628092,147573952589676605564,295147905179353018492,618970019642690137449754748,25227388,75559036,142667900,35184380539004,70368752627836,140737496805500,147573952589684863100,302231454903657302126716,201388156,68786647164,137506123900,147573952589743583356,302231454903657360846972,402714748,137573232764,275012186236,147573952589810692220,295147905179487105148,302231454903657427955836,618970019642690137583841404,442721857769029300348,302379028856246970151036,618970167216642727126036604,906694364710971881091196,92336188,17205096508,34384965692,68744704060,72057594063155260,147573952589701640252,209776700,68795035708,137514512444,35184447647804,70368819736636,140737563914300,147573952589751971900,302231454903657369235516,147573987774056951868,211106240983100,72127962790555708,144185556828483644,147574022958429040700,302231454974026046304316,442721857769037688892,618970167216642727134425148,469823548,68920864828,275079295036,147573952589877801020,295147905179554213948,618970019642690137650950204,140806275002428,147573952658463060028,302231454903726080323644,281612482834492,147573952727182536764,295147905316858949692,618970019642690274955685948,442721857769096409148,302379028856247037259836,618970167216642727193145404,906694364710971948199996,1033017668127734951996,302674176761426322976828,604905631665083616653372]
  let extraMasks : List ℕ := [4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970,12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514]
  (∀ e ∈ layer11, ∃ m ∈ extraMasks, ¬ (codeGraph 10 e)ᶜ ⊑ (codeGraph 19 m)ᶜ) →
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    (∀ a, (codeGraph 19 (masks a)).CliqueFree 3) ∧
    ∀ f : Fin r → Fin 10 ↪ Fin 19,
      (⨅ a, (codeGraph 19 (masks a))ᶜ.comap (f a)).edgeSet.ncard ≤ 33 := by
  intro codeGraph layer11 extraMasks blocked
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
    fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  let seedMask : ℕ := 58280177927389562003304118167894045837298871419233698940907216524622014388169689497720
  let hostMasks : List ℕ := seedMask :: extraMasks

  have host_triangle_free : ∀ m ∈ hostMasks, (codeGraph 19 m).CliqueFree 3 := by
    have raw : ∀ a : Fin hostMasks.length, ∀ i j k : Fin 19,
        (codeGraph 19 hostMasks[a.val]).Adj i j → (codeGraph 19 hostMasks[a.val]).Adj i k →
        ¬ (codeGraph 19 hostMasks[a.val]).Adj j k := by apply of_decide_eq_true; dsimp only [instGraph,codeGraph,hostMasks,seedMask,extraMasks]; decide +kernel
    intro m hm S hS
    obtain ⟨a,ha,rfl⟩ := List.getElem_of_mem hm
    obtain ⟨i,j,k,hij,hik,hjk,_⟩ := SimpleGraph.is3Clique_iff.mp hS
    exact raw ⟨a,ha⟩ i j k hij hik hjk

  have trim_edges {n q : ℕ} (G : SimpleGraph (Fin n)) (count : q ≤ G.edgeSet.ncard) :
      ∃ B : SimpleGraph (Fin n), B ≤ G ∧ B.edgeSet.ncard = q := by
    classical
    rw [Set.ncard_eq_toFinset_card'] at count
    obtain ⟨W,sub,hw⟩ := Finset.exists_subset_card_eq count
    let B := fromEdgeSet (W : Set (Sym2 (Fin n)))
    have inG : (W : Set (Sym2 (Fin n))) ⊆ G.edgeSet := fun e he => by
      have := sub he
      simpa using this
    have eq : B.edgeSet = (W : Set (Sym2 (Fin n))) := by
      rw [show B.edgeSet = _ from edgeSet_fromEdgeSet _]
      ext e
      exact ⟨And.left,fun he => ⟨he,G.not_isDiag_of_mem_edgeSet (inG he)⟩⟩
    exact ⟨B,edgeSet_subset_edgeSet.mp (eq ▸ inG),by simpa [eq] using hw⟩

  have red_size (G : SimpleGraph (Fin 10)) (size : G.edgeSet.ncard = 34) :
      Gᶜ.edgeSet.ncard = 11 := by
    classical
    have dis : Disjoint G.edgeSet Gᶜ.edgeSet := disjoint_edgeSet.mpr disjoint_compl_right
    have edge := Set.ncard_union_eq dis (Set.toFinite _) (Set.toFinite _)
    have topSize : (⊤ : SimpleGraph (Fin 10)).edgeSet.ncard = 45 := by
      calc
        _ = (⊤ : SimpleGraph (Fin 10)).edgeFinset.card := Set.ncard_eq_toFinset_card' _
        _ = (Fintype.card (Fin 10)).choose 2 := card_edgeFinset_top_eq_card_choose_two
        _ = 45 := by decide
    rw [←edgeSet_sup,sup_compl_eq_top,topSize] at edge
    omega

  have ten_obstruction_of_classification
      (classify : ∀ D : SimpleGraph (Fin 10), D.edgeSet.ncard = 11 →
        (∃ e ∈ [61500,58777656,1080899112137670672], codeGraph 10 e ⊑ D) →
        ∃ e ∈ layer11, Nonempty (codeGraph 10 e ≃g D))
      (blocked : ∀ e ∈ layer11, ∃ m ∈ extraMasks, ¬ (codeGraph 10 e)ᶜ ⊑ (codeGraph 19 m)ᶜ)
      (G : SimpleGraph (Fin 10)) (edge : G.edgeSet.ncard = 34) :
      ∃ m ∈ hostMasks, ¬ G ⊑ (codeGraph 19 m)ᶜ := by
    classical
    by_contra! h
    obtain ⟨f⟩ := h seedMask List.mem_cons_self
    have hred := red_size G edge
    have pull : ∀ i j, (codeGraph 19 seedMask).Adj (f i) (f j) → Gᶜ.Adj i j := by
      intro i j hr
      refine ⟨fun heq => hr.ne (congrArg f heq),fun hg => ?_⟩
      exact (f.toHom.map_rel' hg).2 hr
    obtain ⟨e,he,⟨iso⟩⟩ := classify Gᶜ hred (E1182Ten.first_host Gᶜ hred f.toEmbedding pull)
    obtain ⟨m,hm,forbid⟩ := blocked e he
    have lift : (codeGraph 10 e)ᶜ ⊑ G := by
      let emb := SimpleGraph.Embedding.complEquiv iso.toEmbedding
      simpa using emb.isContained
    exact forbid (lift.trans (h m (List.mem_cons_of_mem seedMask hm)))

  have ten_common_of_obstruction
      (obs : ∀ G : SimpleGraph (Fin 10), G.edgeSet.ncard = 34 →
        ∃ m ∈ hostMasks, ¬ G ⊑ (codeGraph 19 m)ᶜ) :
      ∃ (r : ℕ) (masks : Fin r → ℕ),
        (∀ a, (codeGraph 19 (masks a)).CliqueFree 3) ∧
        ∀ f : Fin r → Fin 10 ↪ Fin 19,
          (⨅ a, (codeGraph 19 (masks a))ᶜ.comap (f a)).edgeSet.ncard ≤ 33 := by
    classical
    refine ⟨hostMasks.length, (fun a => hostMasks[a.val]), fun a => host_triangle_free _ (List.getElem_mem _), ?_⟩
    intro f
    let D := ⨅ (a : Fin hostMasks.length), (codeGraph 19 hostMasks[a.val])ᶜ.comap (f a)
    change D.edgeSet.ncard ≤ 33
    by_contra! gt
    obtain ⟨G,sub,edge⟩ := trim_edges D (q:=34) (by omega)
    obtain ⟨m,hm,no⟩ := obs G edge
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hm
    let a : Fin hostMasks.length := ⟨i,hi⟩
    exact no (isContained_iff_exists_le_comap.mpr ⟨f a,sub.trans (iInf_le _ a)⟩)
  exact ten_common_of_obstruction (ten_obstruction_of_classification E1182Ten.classified blocked)
end E1182Ten

open SimpleGraph Finset
namespace E1182TenBlock
theorem sorted_copy {n m : ℕ} {S : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (b : Fin n → ℕ)
    (twins : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' → b i = b i' → b j = b j' →
      S.Adj i j → S.Adj i' j')
    (copy : S ⊑ H) : ∃ e : S.Copy H, ∀ i j, b i = b j → i < j → e i < e j := by
  classical
  obtain ⟨f⟩ := copy
  let cell (t : ℕ) := Finset.univ.filter fun i : Fin n => b i = t
  let target (t : ℕ) := (cell t).map f.toEmbedding
  let p (t : ℕ) : cell t ≃o target t :=
    ((cell t).orderIsoOfFin rfl).symm.trans ((target t).orderIsoOfFin (Finset.card_map _))
  let v (i : Fin n) : Fin m := (p (b i) ⟨i,by simp [cell]⟩).val
  have value (i : Fin n) (t : ℕ) (hi : b i = t) :
      v i = (p t ⟨i,by simp [cell,hi]⟩).val := by subst t; rfl
  have increasing (i j : Fin n) (same : b i = b j) (lt : i < j) : v i < v j := by
    rw [value i (b j) same,value j (b j) rfl]
    exact (p (b j)).strictMono lt
  have inverse (i : Fin n) : ∃ u : Fin n, b u = b i ∧ f u = v i := by
    have mem : v i ∈ target (b i) := (p (b i) ⟨i,by simp [cell]⟩).property
    obtain ⟨u,hu,eq⟩ := Finset.mem_map.mp mem
    exact ⟨u,(Finset.mem_filter.mp hu).2,eq⟩
  have inj : Function.Injective v := by
    intro i j eq
    obtain ⟨a,ha,hai⟩ := inverse i
    obtain ⟨c,hc,hcj⟩ := inverse j
    have h : a = c := f.injective (hai.trans (eq.trans hcj.symm))
    have same : b i = b j := ha.symm.trans ((congrArg b h).trans hc)
    rcases lt_trichotomy i j with lt | yes | gt
    · exact ((increasing i j same lt).ne eq).elim
    · exact yes
    · exact ((increasing j i same.symm gt).ne eq.symm).elim
  refine ⟨⟨⟨v,?_⟩,inj⟩,increasing⟩
  intro i j adj
  obtain ⟨a,ha,hai⟩ := inverse i
  obtain ⟨c,hc,hcj⟩ := inverse j
  have ne : a ≠ c := fun eq => adj.ne (inj (hai.symm.trans ((congrArg f eq).trans hcj)))
  rw [←hai,←hcj]
  exact f.toHom.map_rel' (twins i j a c adj.ne ne ha.symm hc.symm adj)

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem ruledOutFromClasses {n m : ℕ} {S : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (edges tags colours apart joined high : List ℕ) (full : ℕ) (ds : List (Fin n × ℕ))
      (pattern : ∀ i j : Fin n, edges[i.val]!.testBit j.val = true → S.Adj i j)
      (twins : ∀ i j a b : Fin n, i≠j → a≠b → tags[i.val]! = tags[a.val]! →
        tags[j.val]! = tags[b.val]! → S.Adj i j → S.Adj a b)
      (all : ∀ v : Fin m, full.testBit colours[v.val]! = true)
      (other : ∀ u v : Fin m, colours[u.val]! ≠ colours[v.val]! →
        (apart[colours[u.val]!]!).testBit colours[v.val]! = true)
      (blue : ∀ u v : Fin m, H.Adj u v →
        (joined[colours[u.val]!]!).testBit colours[v.val]! = true)
      (higher : ∀ u v : Fin m, u < v → (high[colours[u.val]!]!).testBit colours[v.val]! = true)
      (nd : (ds.map Prod.fst).Nodup)
      (initial : ∀ u ∈ ds, ∀ j : Fin m, u.2.testBit colours[j.val]! = true) :
  let consumeDomains {n : ℕ} (allowed : Fin n → Fin n → ℕ → ℕ) (apart : List ℕ)
      (i : Fin n) (v : ℕ) (remaining : List ℕ) (ds : List (Fin n × ℕ)) :=
    ds.map fun u => (u.1, let mask := u.2 &&& allowed i u.1 v
                          if remaining.contains v then mask else mask &&& apart[v]!)

  let capSearch {n : ℕ} (allowed : Fin n → Fin n → ℕ → ℕ) (apart : List ℕ)
      (k : ℕ) (ds : List (Fin n × ℕ)) (supply : List ℕ) : Bool :=
    Nat.rec (motive := fun _ => List (Fin n × ℕ) → List ℕ → Bool) (fun _ _ => true)
      (fun _ rec current available => match current with
        | [] => true
        | (i,domain)::t => domain.bitIndices.any fun v =>
          available.contains v && (let remaining := available.erase v
                                   let next := consumeDomains allowed apart i v remaining t
                                   next.all (fun u => u.2 != 0) && rec next remaining)) k ds supply

  let classMask {n : ℕ} (edges twins joined high : List ℕ) (full : ℕ)
      (i j : Fin n) (v : ℕ) : ℕ :=
    let mask := if edges[i.val]!.testBit j.val then joined[v]! else full
    if twins[i.val]! = twins[j.val]! ∧ i < j then mask &&& high[v]! else mask
  (block : capSearch (classMask edges tags joined high full) apart ds.length ds
    ((List.finRange m).map fun x => colours[x.val]!) = false) → ¬ S ⊑ H := by
  intro consumeDomains capSearch classMask block
  have capSearch_complete {n : ℕ} (f : Fin n → ℕ) (allowed : Fin n → Fin n → ℕ → ℕ)
      (apart : List ℕ) (distinct : ∀ i j, f i ≠ f j → (apart[f i]!).testBit (f j) = true)
      (consistent : ∀ i j, i ≠ j → (allowed i j (f i)).testBit (f j) = true)
      (k : ℕ) (ds : List (Fin n × ℕ)) (supply : List ℕ)
      (nodup : (ds.map Prod.fst).Nodup)
      (enough : ∀ c, (ds.map (fun u => f u.1)).count c ≤ supply.count c)
      (valid : ∀ u ∈ ds, u.2.testBit (f u.1) = true) :
      capSearch allowed apart k ds supply = true := by
    induction k generalizing ds supply with
    | zero => rfl
    | succ k ih =>
      cases ds with
      | nil => rfl
      | cons q t =>
        obtain ⟨i,d⟩ := q
        let v := f i
        let remaining := supply.erase v
        let next := consumeDomains allowed apart i v remaining t
        simp only [List.map_cons,List.nodup_cons] at nodup
        have count_le (c : ℕ) : (t.map (fun u => f u.1)).count c ≤ remaining.count c := by
          have h := enough c
          change (v :: t.map (fun u => f u.1)).count c ≤ supply.count c at h
          by_cases eq : v=c
          · subst c
            rw [List.count_cons_self] at h
            simpa only [remaining,List.count_erase_self] using Nat.le_sub_one_of_lt h
          · change _ ≤ (supply.erase v).count c
            simpa [List.count_cons, eq, Ne.symm eq] using h
        have hv : v ∈ supply := by
          apply List.count_pos_iff.mp
          have h := enough v
          change (v :: t.map (fun u => f u.1)).count v ≤ supply.count v at h
          rw [List.count_cons_self] at h
          exact (Nat.zero_lt_succ _).trans_le h
        have good : ∀ u ∈ next, u.2.testBit (f u.1) = true := by
          intro u hu
          obtain ⟨⟨j,s⟩,ht,rfl⟩ := List.mem_map.mp hu
          have hj : i ≠ j := by
            intro e
            exact nodup.1 (List.mem_map.mpr ⟨(j,s),ht,e.symm⟩)
          have hd : s.testBit (f j)=true := valid (j,s) (List.mem_cons_of_mem _ ht)
          have hc := consistent i j hj
          change (if remaining.contains v then (s &&& allowed i j v) else (s &&& allowed i j v &&& apart[v]!)).testBit (f j) = true
          by_cases live : remaining.contains v = true
          · rw [if_pos live,Nat.testBit_and,hd,hc]; rfl
          · have diff : v ≠ f j := by
              intro eq
              have mem : f j ∈ t.map (fun u => f u.1) := List.mem_map.mpr ⟨(j,s),ht,rfl⟩
              have pos := (List.count_pos_iff.mpr mem).trans_le (count_le (f j))
              exact live (List.contains_iff_mem.mpr (eq ▸ List.count_pos_iff.mp pos))
            rw [if_neg live,Nat.testBit_and,Nat.testBit_and,hd,hc,distinct i j diff]; rfl
        have fst : next.map Prod.fst = t.map Prod.fst := by
          simp [next,consumeDomains,List.map_map,Function.comp_def]
        have imgs : next.map (fun u => f u.1) = t.map (fun u => f u.1) := by
          simp [next,consumeDomains,List.map_map,Function.comp_def]
        have nz : next.all (fun u => u.2 != 0) = true := by
          apply List.all_eq_true.mpr
          intro u hu
          apply bne_iff_ne.mpr
          intro e
          have h := good u hu
          simp [e] at h
        apply List.any_eq_true.mpr
        refine ⟨v,Nat.mem_bitIndices.mpr (valid (i,d) List.mem_cons_self),?_⟩
        change (supply.contains v && (next.all _ && capSearch allowed apart k next remaining))=true
        rw [List.contains_iff_mem.mpr hv,nz,ih next remaining (fst ▸ nodup.2) (imgs ▸ count_le) good]
        rfl

  have ruledOut {n m : ℕ} {S : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
      (edges tags colours apart joined high : List ℕ) (full : ℕ) (ds : List (Fin n × ℕ))
      (pattern : ∀ i j : Fin n, edges[i.val]!.testBit j.val = true → S.Adj i j)
      (twins : ∀ i j a b : Fin n, i≠j → a≠b → tags[i.val]! = tags[a.val]! →
        tags[j.val]! = tags[b.val]! → S.Adj i j → S.Adj a b)
      (all : ∀ v : Fin m, full.testBit colours[v.val]! = true)
      (other : ∀ u v : Fin m, colours[u.val]! ≠ colours[v.val]! →
        (apart[colours[u.val]!]!).testBit colours[v.val]! = true)
      (blue : ∀ u v : Fin m, H.Adj u v →
        (joined[colours[u.val]!]!).testBit colours[v.val]! = true)
      (higher : ∀ u v : Fin m, u < v → (high[colours[u.val]!]!).testBit colours[v.val]! = true)
      (nd : (ds.map Prod.fst).Nodup)
      (initial : ∀ u ∈ ds, ∀ j : Fin m, u.2.testBit colours[j.val]! = true)
      (block : capSearch (classMask edges tags joined high full) apart ds.length ds
        ((List.finRange m).map fun x => colours[x.val]!) = false) : ¬ S ⊑ H := by
    intro embed
    obtain ⟨e,sort⟩ := sorted_copy (fun i => tags[i.val]!) twins embed
    let f (i : Fin n) := colours[(e i).val]!
    have agree (i j : Fin n) (_ne : i≠j) :
        (classMask edges tags joined high full i j (f i)).testBit (f j) = true := by
      have a : (if edges[i.val]!.testBit j.val then joined[f i]! else full).testBit (f j) = true := by
        split
        next h => exact blue (e i) (e j) (e.toHom.map_rel' (pattern i j h))
        next => exact all _
      dsimp only [classMask]
      split
      next cond => exact (Nat.testBit_and ..).trans (by rw [a, higher _ _ (sort i j cond.1 cond.2)]; rfl)
      next => exact a
    have used : ((ds.map Prod.fst).map e).Subperm (List.finRange m) :=
      (nd.map e.injective).subperm (by intro x _; simp)
    obtain ⟨t,perm,sub⟩ := List.subperm_iff.mp used
    let c (x : Fin m) := colours[x.val]!
    have projected : (((ds.map Prod.fst).map e).map c).Subperm ((List.finRange m).map c) :=
      List.subperm_iff.mpr ⟨t.map c,perm.map c,sub.map c⟩
    have enough := List.subperm_iff_count.mp projected
    have ok := capSearch_complete f _ apart (fun i j h => other (e i) (e j) h)
      agree ds.length ds ((List.finRange m).map c) nd
      (by simpa [f,c,List.map_map,Function.comp_def] using enough)
      (fun u hu => initial u hu (e u.1))
    rw [block] at ok
    contradiction
  exact ruledOut edges tags colours apart joined high full ds pattern twins all other blue higher nd initial block

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem negative0 :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ¬ ((codeGraph 10 72092898795057278) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have reject : ¬ ((codeGraph 10 72092898795057278) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
    let edges : List ℕ := [126,125,123,119,47,95,47,0,0,0]
    let tags : List ℕ := [0,0,0,0,4,0,4,7,7,7]
    let colours : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
    let apart : List ℕ := [524286,524285,524283,524279,524271,524255,524223,524159,524031,523775,523263,522239,520191,516095,507903,491519,458751,393215,262143]
    let joined : List ℕ := [226879,194927,236791,421723,480989,245671,448990,499700,457706,489401,470717,437742,250871,388907,389979,391654,390837,139263,389080]
    let high : List ℕ := [524287,524286,524284,524280,524272,524256,524224,524160,524032,523776,523264,522240,520192,516096,507904,491520,458752,393216,262144]
    let ds : List (Fin 10 × ℕ) := [(0,524287),(1,524287),(2,524287),(3,524287),(4,524287),(5,524287),(6,524287)]
    apply ruledOutFromClasses edges tags colours apart joined high 524287 ds
    all_goals
      apply of_decide_eq_true
      dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]
      decide +kernel
  exact reject

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem negative1 :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ¬ ((codeGraph 10 147646080741630210238) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have reject : ¬ ((codeGraph 10 147646080741630210238) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
    let edges : List ℕ := [190,189,187,183,79,79,176,79,0,0]
    let tags : List ℕ := [0,0,0,0,4,4,6,4,8,8]
    let colours : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
    let apart : List ℕ := [524286,524285,524283,524279,524271,524255,524223,524159,524031,523775,523263,522239,520191,516095,507903,491519,458751,393215,262143]
    let joined : List ℕ := [226879,194927,236791,421723,480989,245671,448990,499700,457706,489401,470717,437742,250871,388907,389979,391654,390837,139263,389080]
    let high : List ℕ := [524287,524286,524284,524280,524272,524256,524224,524160,524032,523776,523264,522240,520192,516096,507904,491520,458752,393216,262144]
    let ds : List (Fin 10 × ℕ) := [(0,524287),(1,524287),(2,524287),(3,524287),(4,524287),(5,524287),(6,524287),(7,524287)]
    apply ruledOutFromClasses edges tags colours apart joined high 524287 ds
    all_goals
      apply of_decide_eq_true
      dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]
      decide +kernel
  exact reject

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem negative2 :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ¬ ((codeGraph 10 906694869889269721329788) ⊑ (codeGraph 19 12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have reject : ¬ ((codeGraph 10 906694869889269721329788) ⊑ (codeGraph 19 24444478340170996362562651254270179478123593088051851749947838762361501635629144562684923660)ᶜ) := by
    let edges : List ℕ := [124,124,1011,1011,719,463,63,828,172,156]
    let tags : List ℕ := [0,0,2,2,4,5,6,7,8,9]
    let colours : List ℕ := [0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,9,9]
    let apart : List ℕ := [1022,1021,1019,1015,1007,991,959,895,767,511]
    let joined : List ℕ := [973,954,885,747,502,638,253,475,919,815]
    let high : List ℕ := [1023,1022,1020,1016,1008,992,960,896,768,512]
    let ds : List (Fin 10 × ℕ) := [(0,1023),(1,1023),(2,1023),(3,1023),(4,1023),(5,1023),(6,1023),(7,1023),(8,1023),(9,1023)]
    apply ruledOutFromClasses edges tags colours apart joined high 1023 ds
    case block =>
      apply List.any_eq_false.mpr
      intro v hv
      have bound : ∀ w ∈ (1023 : ℕ).bitIndices, w < 10 := by decide
      have vr := bound v hv
      interval_cases v <;> (apply of_decide_eq_true; dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]; decide +kernel)
    all_goals
      apply of_decide_eq_true
      dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]
      decide +kernel
  let labels : List ℕ := [0,2,4,6,8,10,12,14,16,17,7,1,15,5,11,9,13,18,3]
  let f (i : Fin 19) := Fin.ofNat 19 labels[i.val]!
  have inj : Function.Injective f := by apply of_decide_eq_true; dsimp only [instGraph,codeGraph,f,labels]; decide +kernel
  have adj : ∀ i j : Fin 19, (codeGraph 19 12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514)ᶜ.Adj i j →
      (codeGraph 19 24444478340170996362562651254270179478123593088051851749947838762361501635629144562684923660)ᶜ.Adj (f i) (f j) := by apply of_decide_eq_true; dsimp only [instGraph,codeGraph,f,labels]; decide +kernel
  let relabel : Copy (codeGraph 19 12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514)ᶜ (codeGraph 19 24444478340170996362562651254270179478123593088051851749947838762361501635629144562684923660)ᶜ :=
    ⟨⟨f,fun {_ _} h => adj _ _ h⟩,inj⟩
  rintro ⟨e⟩
  exact reject ⟨relabel.comp e⟩

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem negative3 :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ¬ ((codeGraph 10 302526891320962913136894) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have reject : ¬ ((codeGraph 10 302526891320962913136894) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
    let edges : List ℕ := [254,253,251,263,263,263,263,263,248,0]
    let tags : List ℕ := [0,0,0,3,3,3,3,3,8,9]
    let colours : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
    let apart : List ℕ := [524286,524285,524283,524279,524271,524255,524223,524159,524031,523775,523263,522239,520191,516095,507903,491519,458751,393215,262143]
    let joined : List ℕ := [226879,194927,236791,421723,480989,245671,448990,499700,457706,489401,470717,437742,250871,388907,389979,391654,390837,139263,389080]
    let high : List ℕ := [524287,524286,524284,524280,524272,524256,524224,524160,524032,523776,523264,522240,520192,516096,507904,491520,458752,393216,262144]
    let ds : List (Fin 10 × ℕ) := [(0,524287),(1,524287),(2,524287),(3,524287),(4,524287),(5,524287),(6,524287),(7,524287),(8,524287)]
    apply ruledOutFromClasses edges tags colours apart joined high 524287 ds
    case block =>
      apply List.any_eq_false.mpr
      intro v hv
      have bound : ∀ w ∈ (524287 : ℕ).bitIndices, w < 19 := by decide
      have vr := bound v hv
      interval_cases v <;> (apply of_decide_eq_true; dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]; decide +kernel)
    all_goals
      apply of_decide_eq_true
      dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]
      decide +kernel
  exact reject

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem negative4 :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ¬ ((codeGraph 10 257958342910) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have reject : ¬ ((codeGraph 10 257958342910) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ) := by
    let edges : List ℕ := [254,253,251,247,15,15,15,15,0,0]
    let tags : List ℕ := [0,0,0,0,4,4,4,4,8,8]
    let colours : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
    let apart : List ℕ := [524286,524285,524283,524279,524271,524255,524223,524159,524031,523775,523263,522239,520191,516095,507903,491519,458751,393215,262143]
    let joined : List ℕ := [226879,194927,236791,421723,480989,245671,448990,499700,457706,489401,470717,437742,250871,388907,389979,391654,390837,139263,389080]
    let high : List ℕ := [524287,524286,524284,524280,524272,524256,524224,524160,524032,523776,523264,522240,520192,516096,507904,491520,458752,393216,262144]
    let ds : List (Fin 10 × ℕ) := [(0,524287),(1,524287),(2,524287),(3,524287),(4,524287),(5,524287),(6,524287),(7,524287)]
    apply ruledOutFromClasses edges tags colours apart joined high 524287 ds
    all_goals
      apply of_decide_eq_true
      dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]
      decide +kernel
  exact reject

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem negative5 :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ¬ ((codeGraph 10 147790336667127378172) ⊑ (codeGraph 19 12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))
  have reject : ¬ ((codeGraph 10 147790336667127378172) ⊑ (codeGraph 19 58280177927389561922424847023594801385086647453668247069770971250404919578473562998300)ᶜ) := by
    let edges : List ℕ := [252,252,123,183,207,207,183,123,0,0]
    let tags : List ℕ := [0,0,2,3,4,4,3,2,8,8]
    let colours : List ℕ := [0,0,1,1,1,2,2,3,3,4,4,5,6,6,7,8,8,9,9]
    let apart : List ℕ := [1022,1021,1019,1015,1007,991,959,895,767,511]
    let joined : List ℕ := [749,922,885,715,502,501,253,251,822,783]
    let high : List ℕ := [1023,1022,1020,1016,1008,992,960,896,768,512]
    let ds : List (Fin 10 × ℕ) := [(0,1023),(1,1023),(2,1023),(3,1023),(4,1023),(5,1023),(6,1023),(7,1023)]
    apply ruledOutFromClasses edges tags colours apart joined high 1023 ds
    all_goals
      apply of_decide_eq_true
      dsimp only [instGraph,codeGraph,edges,tags,colours,apart,joined,high,ds]
      decide +kernel
  let labels : List ℕ := [0,2,5,7,9,11,12,14,15,17,10,3,4,1,18,6,16,13,8]
  let f (i : Fin 19) := Fin.ofNat 19 labels[i.val]!
  have inj : Function.Injective f := by apply of_decide_eq_true; dsimp only [instGraph,codeGraph,f,labels]; decide +kernel
  have adj : ∀ i j : Fin 19, (codeGraph 19 12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970)ᶜ.Adj i j →
      (codeGraph 19 58280177927389561922424847023594801385086647453668247069770971250404919578473562998300)ᶜ.Adj (f i) (f j) := by apply of_decide_eq_true; dsimp only [instGraph,codeGraph,f,labels]; decide +kernel
  let relabel : Copy (codeGraph 19 12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970)ᶜ (codeGraph 19 58280177927389561922424847023594801385086647453668247069770971250404919578473562998300)ᶜ :=
    ⟨⟨f,fun {_ _} h => adj _ _ h⟩,inj⟩
  rintro ⟨e⟩
  exact reject ⟨relabel.comp e⟩

set_option maxRecDepth 90000 in
set_option maxHeartbeats 0 in
theorem seed_blocked :
  let codeGraph (n mask : ℕ) : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ mask.testBit (min x.val y.val*n + max x.val y.val) = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [min_comm y.val, max_comm y.val] using h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
  ∀ e : ℕ, e ∈ [58777662,58777722,125886522,17238646842,68778254394,147573952589735190586,58777848,58843256,58908792,68778254456,137497731192,147573952589735190648,302231454903657352454264,442721857769088016440,618970167216642727184752696,619575073424768563045991038,619575073424768563045995070,619575073424768563046023742,619575073424768563046056510,619575073424768563046515262,619575073496826157083918910,619575220998721152722403902,619575073424768563046003230,619575073424768563046027806,619575073424768580225864222,619575073424768597405733406,619575073496826157083922974,619575073424768563046089246,619575073424768563113132574,61694,127102,192638,8450174,67170430,134279294,147573952589676474494,302231454903657293738110,25227326,75558974,35184380538942,70368752627774,147573952589684863038,201388094,68786647102,137506123838,147573952589743583294,302231454903657360846910,442721857769029300286,618970167216642727126036542,61948,127228,323836,8450300,67170556,268497148,147573952589676474620,295147905179352887548,618970019642690137449623804,8515708,134344828,302231454903657293803644,8581244,67301500,268628092,147573952589676605564,295147905179353018492,618970019642690137449754748,25227388,75559036,142667900,35184380539004,70368752627836,140737496805500,147573952589684863100,302231454903657302126716,201388156,68786647164,137506123900,147573952589743583356,302231454903657360846972,402714748,137573232764,275012186236,147573952589810692220,295147905179487105148,302231454903657427955836,618970019642690137583841404,442721857769029300348,302379028856246970151036,618970167216642727126036604,906694364710971881091196,92336188,17205096508,34384965692,68744704060,72057594063155260,147573952589701640252,209776700,68795035708,137514512444,35184447647804,70368819736636,140737563914300,147573952589751971900,302231454903657369235516,147573987774056951868,211106240983100,72127962790555708,144185556828483644,147574022958429040700,302231454974026046304316,442721857769037688892,618970167216642727134425148,469823548,68920864828,275079295036,147573952589877801020,295147905179554213948,618970019642690137650950204,140806275002428,147573952658463060028,302231454903726080323644,281612482834492,147573952727182536764,295147905316858949692,618970019642690274955685948,442721857769096409148,302379028856247037259836,618970167216642727193145404,906694364710971948199996,1033017668127734951996,302674176761426322976828,604905631665083616653372] →
    ∃ c ∈ [4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970,12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514], ¬ ((codeGraph 10 e)ᶜ ⊑ (codeGraph 19 c)ᶜ) := by
  intro codeGraph
  let instGraph (n mask : ℕ) : DecidableRel (codeGraph n mask).Adj :=
      fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))

  have blocked_via_patterns
  (h0 : ¬ ((codeGraph 10 72092898795057278) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ))
      (h1 : ¬ ((codeGraph 10 147646080741630210238) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ))
      (h2 : ¬ ((codeGraph 10 906694869889269721329788) ⊑ (codeGraph 19 12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514)ᶜ))
      (h3 : ¬ ((codeGraph 10 302526891320962913136894) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ))
      (h4 : ¬ ((codeGraph 10 257958342910) ⊑ (codeGraph 19 4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632)ᶜ))
      (h5 : ¬ ((codeGraph 10 147790336667127378172) ⊑ (codeGraph 19 12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970)ᶜ))
      (e : ℕ) (he : e ∈ [58777662,58777722,125886522,17238646842,68778254394,147573952589735190586,58777848,58843256,58908792,68778254456,137497731192,147573952589735190648,302231454903657352454264,442721857769088016440,618970167216642727184752696,619575073424768563045991038,619575073424768563045995070,619575073424768563046023742,619575073424768563046056510,619575073424768563046515262,619575073496826157083918910,619575220998721152722403902,619575073424768563046003230,619575073424768563046027806,619575073424768580225864222,619575073424768597405733406,619575073496826157083922974,619575073424768563046089246,619575073424768563113132574,61694,127102,192638,8450174,67170430,134279294,147573952589676474494,302231454903657293738110,25227326,75558974,35184380538942,70368752627774,147573952589684863038,201388094,68786647102,137506123838,147573952589743583294,302231454903657360846910,442721857769029300286,618970167216642727126036542,61948,127228,323836,8450300,67170556,268497148,147573952589676474620,295147905179352887548,618970019642690137449623804,8515708,134344828,302231454903657293803644,8581244,67301500,268628092,147573952589676605564,295147905179353018492,618970019642690137449754748,25227388,75559036,142667900,35184380539004,70368752627836,140737496805500,147573952589684863100,302231454903657302126716,201388156,68786647164,137506123900,147573952589743583356,302231454903657360846972,402714748,137573232764,275012186236,147573952589810692220,295147905179487105148,302231454903657427955836,618970019642690137583841404,442721857769029300348,302379028856246970151036,618970167216642727126036604,906694364710971881091196,92336188,17205096508,34384965692,68744704060,72057594063155260,147573952589701640252,209776700,68795035708,137514512444,35184447647804,70368819736636,140737563914300,147573952589751971900,302231454903657369235516,147573987774056951868,211106240983100,72127962790555708,144185556828483644,147574022958429040700,302231454974026046304316,442721857769037688892,618970167216642727134425148,469823548,68920864828,275079295036,147573952589877801020,295147905179554213948,618970019642690137650950204,140806275002428,147573952658463060028,302231454903726080323644,281612482834492,147573952727182536764,295147905316858949692,618970019642690274955685948,442721857769096409148,302379028856247037259836,618970167216642727193145404,906694364710971948199996,1033017668127734951996,302674176761426322976828,604905631665083616653372]) :
      ∃ c ∈ [4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970,12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514], ¬ ((codeGraph 10 e)ᶜ ⊑ (codeGraph 19 c)ᶜ) := by
    let patterns : List ℕ := [72092898795057278,147646080741630210238,906694869889269721329788,302526891320962913136894,257958342910,147790336667127378172]
    let mats : List ℕ := [4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,12815930363669365891600092140750539518217499177757377408917144300401324135455101653909173508030514,4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,4479493756337828422381768076222663975448198329188301774237696156955172576037144452142741750559459805632,12815938511828812536218087847244909534200620914327746814503801336510447893155006986723115497757970]
    let rs : List (ℕ × ℕ × ℕ) := [(58777662,0,141892805955),
      (58777722,0,141892805955),
      (125886522,0,141892805955),
      (17238646842,0,361608808290),
      (68778254394,0,361608808290),
      (147573952589735190586,0,141861225795),
      (58777848,0,141892805955),
      (58843256,0,141892805955),
      (58908792,0,141892805955),
      (68778254456,0,361692694305),
      (137497731192,0,361692694305),
      (147573952589735190648,0,141861225795),
      (302231454903657352454264,0,141878060355),
      (442721857769088016440,1,362982838800),
      (618970167216642727184752696,2,361592550945),
      (619575073424768563045991038,0,652958122785),
      (619575073424768563045995070,0,627206214705),
      (619575073424768563046023742,0,640091112225),
      (619575073424768563046056510,0,644385030945),
      (619575073424768563046515262,0,652958122785),
      (619575073496826157083918910,0,644385030945),
      (619575220998721152722403902,0,652958122785),
      (619575073424768563046003230,0,622911247410),
      (619575073424768563046027806,0,622911247410),
      (619575073424768580225864222,0,627140949585),
      (619575073424768597405733406,0,627157726785),
      (619575073496826157083922974,0,627174634545),
      (619575073424768563046089246,0,622911247410),
      (619575073424768563113132574,0,640059339825),
      (61694,0,622911247410),
      (127102,0,622911247410),
      (192638,0,622911247410),
      (8450174,0,210612282690),
      (67170430,0,416770708530),
      (134279294,0,485489136690),
      (147573952589676474494,0,485489136690),
      (302231454903657293738110,0,622911247410),
      (25227326,0,141892805955),
      (75558974,0,141892805955),
      (35184380538942,0,210547017570),
      (70368752627774,0,210563794770),
      (147573952589684863038,0,210580702530),
      (201388094,0,141892805955),
      (68786647102,0,416770708530),
      (137506123838,0,416738936130),
      (147573952589743583294,0,416770708530),
      (302231454903657360846910,0,416755962930),
      (442721857769029300286,0,416770708530),
      (618970167216642727126036542,0,485489136690),
      (61948,0,622911247410),
      (127228,0,622911247410),
      (323836,0,622911247410),
      (8450300,0,210612282690),
      (67170556,0,416770708530),
      (268497148,0,554208547890),
      (147573952589676474620,0,485489136690),
      (295147905179352887548,0,554208547890),
      (618970019642690137449623804,0,622911247410),
      (8515708,0,210612282690),
      (134344828,0,485489136690),
      (302231454903657293803644,0,622911247410),
      (8581244,0,210612282690),
      (67301500,0,416770708530),
      (268628092,0,554208547890),
      (147573952589676605564,0,485489136690),
      (295147905179353018492,0,554208547890),
      (618970019642690137449754748,0,622911247410),
      (25227388,0,141892805955),
      (75559036,0,141892805955),
      (142667900,0,141892805955),
      (35184380539004,0,210547017570),
      (70368752627836,0,210563794770),
      (140737496805500,0,210580571730),
      (147573952589684863100,0,210580702530),
      (302231454903657302126716,0,210597537090),
      (201388156,0,141892805955),
      (68786647164,0,416770708530),
      (137506123900,0,416738936130),
      (147573952589743583356,0,416770708530),
      (302231454903657360846972,0,416755962930),
      (402714748,0,141892805955),
      (137573232764,0,485489136690),
      (275012186236,0,485475181890),
      (147573952589810692220,0,485489136690),
      (295147905179487105148,0,485475374130),
      (302231454903657427955836,0,485489136690),
      (618970019642690137583841404,0,485489136690),
      (442721857769029300348,0,416770708530),
      (302379028856246970151036,0,485489136690),
      (618970167216642727126036604,0,485489136690),
      (906694364710971881091196,0,622911247410),
      (92336188,0,141892805955),
      (17205096508,0,279232808805),
      (34384965692,0,141827475300),
      (68744704060,0,141844252500),
      (72057594063155260,0,141844383555),
      (147573952589701640252,0,141861225795),
      (209776700,0,141892805955),
      (68795035708,0,416671762260),
      (137514512444,0,141861029460),
      (35184447647804,0,141827540835),
      (70368819736636,0,141844318035),
      (140737563914300,0,141861094995),
      (147573952589751971900,0,141861225795),
      (302231454903657369235516,0,141878060355),
      (147573987774056951868,3,374788393350),
      (211106240983100,0,279232808805),
      (72127962790555708,0,416671762260),
      (144185556828483644,4,361617201270),
      (147574022958429040700,0,416671762260),
      (302231454974026046304316,3,310632319350),
      (442721857769037688892,0,416671762260),
      (618970167216642727134425148,5,70189081650),
      (469823548,0,141892805955),
      (68920864828,0,416738870595),
      (275079295036,0,141877802580),
      (147573952589877801020,0,485441570115),
      (295147905179554213948,0,141877998915),
      (618970019642690137650950204,0,141892805955),
      (140806275002428,0,416739001650),
      (147573952658463060028,0,416770708530),
      (302231454903726080323644,0,416755962930),
      (281612482834492,5,70742524770),
      (147573952727182536764,0,416738936130),
      (295147905316858949692,0,416738936130),
      (618970019642690274955685948,5,70692389730),
      (442721857769096409148,0,416770708530),
      (302379028856247037259836,0,416755962930),
      (618970167216642727193145404,0,416770708530),
      (906694364710971948199996,0,485441570115),
      (1033017668127734951996,0,416770708530),
      (302674176761426322976828,0,554178073650),
      (604905631665083616653372,0,416771691570)]
    let image (w : ℕ) (i : Fin 10) : Fin 10 := Fin.ofNat 10 (w / 16^i.val % 16)
    let ok (r : ℕ × ℕ × ℕ) : Bool :=
      let f := image r.2.2
      let t := r.2.1
      decide (t < 6 ∧ Function.Injective f ∧
        ∀ i j : Fin 10, (codeGraph 10 patterns[t]!).Adj i j → (codeGraph 10 r.1)ᶜ.Adj (f i) (f j))
    have checks : rs.all ok = true := by apply of_decide_eq_true; dsimp only [instGraph,codeGraph,rs,ok,image,patterns]; decide +kernel
    have eq : rs.map Prod.fst = [58777662,58777722,125886522,17238646842,68778254394,147573952589735190586,58777848,58843256,58908792,68778254456,137497731192,147573952589735190648,302231454903657352454264,442721857769088016440,618970167216642727184752696,619575073424768563045991038,619575073424768563045995070,619575073424768563046023742,619575073424768563046056510,619575073424768563046515262,619575073496826157083918910,619575220998721152722403902,619575073424768563046003230,619575073424768563046027806,619575073424768580225864222,619575073424768597405733406,619575073496826157083922974,619575073424768563046089246,619575073424768563113132574,61694,127102,192638,8450174,67170430,134279294,147573952589676474494,302231454903657293738110,25227326,75558974,35184380538942,70368752627774,147573952589684863038,201388094,68786647102,137506123838,147573952589743583294,302231454903657360846910,442721857769029300286,618970167216642727126036542,61948,127228,323836,8450300,67170556,268497148,147573952589676474620,295147905179352887548,618970019642690137449623804,8515708,134344828,302231454903657293803644,8581244,67301500,268628092,147573952589676605564,295147905179353018492,618970019642690137449754748,25227388,75559036,142667900,35184380539004,70368752627836,140737496805500,147573952589684863100,302231454903657302126716,201388156,68786647164,137506123900,147573952589743583356,302231454903657360846972,402714748,137573232764,275012186236,147573952589810692220,295147905179487105148,302231454903657427955836,618970019642690137583841404,442721857769029300348,302379028856246970151036,618970167216642727126036604,906694364710971881091196,92336188,17205096508,34384965692,68744704060,72057594063155260,147573952589701640252,209776700,68795035708,137514512444,35184447647804,70368819736636,140737563914300,147573952589751971900,302231454903657369235516,147573987774056951868,211106240983100,72127962790555708,144185556828483644,147574022958429040700,302231454974026046304316,442721857769037688892,618970167216642727134425148,469823548,68920864828,275079295036,147573952589877801020,295147905179554213948,618970019642690137650950204,140806275002428,147573952658463060028,302231454903726080323644,281612482834492,147573952727182536764,295147905316858949692,618970019642690274955685948,442721857769096409148,302379028856247037259836,618970167216642727193145404,906694364710971948199996,1033017668127734951996,302674176761426322976828,604905631665083616653372] := by rfl
    have mem : e ∈ rs.map Prod.fst := eq ▸ he
    obtain ⟨⟨d,t,w⟩,inlist,rfl⟩ := List.mem_map.mp mem
    have h := List.all_eq_true.mp checks (d,t,w) inlist
    change decide (_ ∧ _ ∧ _) = true at h
    obtain ⟨bound,inj,edges⟩ := of_decide_eq_true h
    have embedding : (codeGraph 10 patterns[t]!) ⊑ (codeGraph 10 d)ᶜ :=
      ⟨⟨⟨image w,fun {_ _} h => edges _ _ h⟩,inj⟩⟩
    change t < 6 at bound
    refine ⟨mats[t]!,?_,?_⟩
    · interval_cases t <;> decide +kernel
    · rintro ⟨f⟩
      obtain ⟨g⟩ := embedding
      have bad : (codeGraph 10 patterns[t]!) ⊑ (codeGraph 19 mats[t]!)ᶜ := ⟨f.comp g⟩
      interval_cases t
      all_goals first | exact h0 bad | exact h1 bad | exact h2 bad | exact h3 bad | exact h4 bad | exact h5 bad
  exact blocked_via_patterns negative0 negative1 negative2 negative3 negative4 negative5

end E1182TenBlock

open SimpleGraph
namespace E1182Ten

theorem ten :
    ∃ (r : ℕ) (masks : Fin r → ℕ),
      let C (a : Fin r) : SimpleGraph (Fin 19) :=
        { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val * 19 + (max i j).val) = true
          symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [min_comm j i,max_comm j i] using h.2⟩⟩
          loopless := ⟨by simp⟩ }
      (∀ a, (C a).CliqueFree 3) ∧
      ∀ f : Fin r → Fin 10 ↪ Fin 19, (⨅ a, (C a)ᶜ.comap (f a)).edgeSet.ncard ≤ 33 :=
  E1182Ten.host_family E1182TenBlock.seed_blocked

end E1182Ten

/- # Bounds from given finite graph families -/

namespace SmallTable.Blockers
open SimpleGraph Finset
theorem combineFamilies : (let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)
  let C (a : Fin 2) : SimpleGraph (Fin 15) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 2 → Fin 8 ↪ Fin 15,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 20) → (let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)
  let C (a : Fin 3) : SimpleGraph (Fin 17) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 3 → Fin 9 ↪ Fin 17,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 27) → (∀ t : Fin 3,
  let n := t.val+10
  let h := 2*n-1
  let q := (![33,41,49] : Fin 3 → ℕ) t
  ∃ (r : ℕ) (C : Fin r → SimpleGraph (Fin h)),
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin n ↪ Fin h,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ q) → (∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q+1 →
    ∃ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ) := by
  intro b c d k
  fin_cases k <;> dsimp only <;> intro G gc ge
  · exact upper4 G (by rw [ge]; exact Nat.lt_succ_self _)
  · exact upper5 G (by rw [ge]; exact Nat.lt_succ_self _)
  · exact upper6 G (by rw [ge]; exact Nat.lt_succ_self _)
  · exact upperSeven G ge
  · let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)
    let C (a : Fin 2) : SimpleGraph (Fin 15) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    have tr : ∀ t : Fin 2, ∀ i j l : Fin 15, (i ≠ j ∧ ((![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ) t).testBit ((min i j).val*15+(max i j).val) = true) → (i ≠ l ∧ ((![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ) t).testBit ((min i l).val*15+(max i l).val) = true) → ¬ (j ≠ l ∧ ((![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ) t).testBit ((min j l).val*15+(max j l).val) = true) := by decide
    exact common C (fun t => triangleFree _ (tr t)) b G gc (by rw [ge]; exact Nat.lt_succ_self _)
  · let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)
    let C (a : Fin 3) : SimpleGraph (Fin 17) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    have tr : ∀ t : Fin 3, ∀ i j l : Fin 17, (i ≠ j ∧ ((![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ) t).testBit ((min i j).val*17+(max i j).val) = true) → (i ≠ l ∧ ((![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ) t).testBit ((min i l).val*17+(max i l).val) = true) → ¬ (j ≠ l ∧ ((![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ) t).testBit ((min j l).val*17+(max j l).val) = true) := by decide
    exact common C (fun t => triangleFree _ (tr t)) c G gc (by rw [ge]; exact Nat.lt_succ_self _)
  · obtain ⟨r,m,tr,lim⟩ := d 0
    exact common _ tr lim G gc ((Nat.lt_succ_self 33).trans_eq ge.symm)
  · obtain ⟨r,m,tr,lim⟩ := d 1
    exact common _ tr lim G gc ((Nat.lt_succ_self 41).trans_eq ge.symm)
  · obtain ⟨r,m,tr,lim⟩ := d 2
    exact common _ tr lim G gc ((Nat.lt_succ_self 49).trans_eq ge.symm)
end SmallTable.Blockers

/- # Triangle-free obstructions on 21 and 23 vertices -/

namespace FixedRamseyHosts
open SimpleGraph

lemma tri {n : ℕ} (m : ℕ) (row : Fin n → ℕ)
    (checked : ∀ i j : Fin n, i ≠ j → m.testBit ((max i j).val.choose 2+(min i j).val)=true →
      (row i).testBit j.val = true ∧ (row i &&& row j) = 0) :
    let G : SimpleGraph (Fin n) := { Adj := fun i j => i ≠ j ∧ (m).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  intro G
  intro S clique
  obtain ⟨i,j,k,ij,ik,jk,_⟩ := SimpleGraph.is3Clique_iff.mp clique
  have h := congrArg (fun x : ℕ => x.testBit k.val) (checked i j ij.1 ij.2).2
  simp [Nat.testBit_and,(checked i k ik.1 ik.2).1,(checked j k jk.1 jk.2).1] at h

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_0 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x3c03c78079e01ef00ff00f1e007803c03c00781e0f0f01e7bfc0 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x3c03c78079e01ef00ff00f1e007803c03c00781e0f0f01e7bfc0 (![2031856,2031856,2031856,2031856,3855,3855,3855,3855,61680,61680,61680,61680,2035456,2035456,2035456,2035456,61455,61455,61455,61455,61455] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_1 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x1300c9300ca601898064c034c02980260130130260984c4c9a512 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x1300c9300ca601898064c034c02980260130130260984c4c9a512 (![622692,1245384,393617,787234,1574468,1051785,6419,12838,25676,51352,102704,205408,410816,821632,1643264,1189377,281603,563206,1126412,155673,311346] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_2 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x14618714a110c3142298116d102a2148904630c2494281d0a4873 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x14618714a110c3142298116d102a2148904630c2494281d0a4873 (![1212694,606761,74825,399494,333921,1189010,1589908,33128,595585,403778,280868,1607192,1073432,561700,169026,354433,1212694,606761,1607192,403778,333921] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_3 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x8c114a884942464b2022a4a428261306320822e4a4ad013060e4 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x8c114a884942464b2022a4a428261306320822e4a4ad013060e4 (![1838224,283156,1149962,533156,41251,459864,1067808,86281,918736,230474,29477,143429,1608834,1379352,689346,283156,533156,1067808,41251,86281,143429] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_4 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x2a0350a80582183162129c0f8001d0086405013a94461515060a0 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x2a0350a80582183162129c0f8001d0086405013a94461515060a0 (![928000,528016,1055496,533668,1061154,149592,1377824,1392650,82965,155718,164170,98343,950292,98841,557984,1080320,666048,1119777,4289,1134603,688340] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_5 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x320c9a068340d092240b020b03304c45222a22864d0684810665 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x320c9a068340d092240b020b03304c45222a22864d0684810665 (![51250,1119301,141450,282900,1582601,1443201,789250,561700,106600,213200,51250,1119301,141450,282900,1582601,1443201,789250,561700,106600,213200,51250] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_6 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0x9848e6152078149c905b20421622c0a5011422e4a4ad017060e4 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x9848e6152078149c905b20421622c0a5011422e4a4ad017060e4 (![1088656,1344148,539658,311972,155939,1639512,23328,663819,1148112,599114,410405,458821,458821,1344148,1639512,663819,23328,1088656,539658,311972,155939] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_21_7 :
    let G : SimpleGraph (Fin 21) := { Adj := fun i j => i ≠ j ∧ (0xb1f00c9911c54838254c9410328059521341a10461915172e0a4 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0xb1f00c9911c54838254c9410328059521341a10461915172e0a4 (![182208,543892,459082,58020,103202,918616,1062949,1380363,1583125,1837081,1126435,230210,672976,394568,1380363,1837081,543892,1062949,58020,103202,182208] : Fin 21 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_0 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x1f0078f803cf803df007fc01e1f001f003e00f807c003c0781e0f0f01e7bfc0 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x1f0078f803cf803df007fc01e1f001f003e00f807c003c0781e0f0f01e7bfc0 (![8126704,8126704,8126704,8126704,7951,7951,7951,7951,254192,254192,254192,254192,254192,8134400,8134400,8134400,8134400,8134400,253967,253967,253967,253967,253967] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_1 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x15402ad500aaa8056a8055500b5402aa01aa015405502a82a855154aaab556ad : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x15402ad500aaa8056a8055500b5402aa01aa015405502a82a855154aaab556ad (![5570730,2752853,5505706,2622805,5245610,2102613,4205226,21845,43690,87380,174760,349520,699040,1398080,2796160,5592320,2796033,5592066,2795525,5591050,2793493,5586986,2785365] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_2 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x980192600653003130032600698014c004c00980260130130260984c4c9a512 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x980192600653003130032600698014c004c00980260130130260984c4c9a512 (![2490468,4980936,1573265,3146530,6293060,4197513,6419,12838,25676,51352,102704,205408,410816,821632,1643264,3286528,6573056,4757505,1126403,2252806,4505612,622617,1245234] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_3 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x914a1386185108a4308c1022c86188168d102a2148904630c2494281d0a4873 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x914a1386185108a4308c1022c86188168d102a2148904630c2494281d0a4873 (![3178774,4473385,271433,1775750,923745,3220626,6374036,33128,5052033,1190210,149796,6325784,2122008,4756004,1610818,485505,33128,6325784,3178774,2122008,4473385,923745,1190210] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_4 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0xa0c30e8a50821862a114d022c16819442d102a2148904630c2494281d0a4873 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0xa0c30e8a50821862a114d022c16819442d102a2148904630c2494281d0a4873 (![4882710,2441769,271433,1579142,1316961,4727954,6374036,164200,2365057,1714498,1263908,6325784,4415768,2134564,562242,1403009,562242,2365057,4882710,2441769,6325784,1714498,1316961] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_5 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x6c30c4d0a51091253440c310c81681861d102a2148904630c2494281d0a4873 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x6c30c4d0a51091253440c310c81681861d102a2148904630c2494281d0a4873 (![1671446,279081,2368585,5380230,6297697,205970,1262228,2916712,136833,6302018,5261604,886296,352536,1610276,2659394,4352129,6297697,2916712,5380230,4352129,2368585,1262228,886296] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_6 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x660a992805aa22340c0808a41024c50724808545904048a115126182d64418 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x660a992805aa22340c0808a41024c50724808545904048a115126182d64418 (![6889512,334472,4391616,1066307,4460960,149073,305196,1590294,592408,2138406,4530344,7340354,188434,1054273,6361256,5837376,50439,3674148,3671122,426369,436360,412161,52245] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_7 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0xa1106c0984e4408060650a165e02a01953428300c30140455959a04a01a8204 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0xa1106c0984e4408060650a165e02a01953428300c30140455959a04a01a8204 (![6379584,3016964,4293698,4853008,2457672,1445440,532789,863744,70218,6341024,2117804,32939,1352961,6426816,919041,662036,1180053,122922,4214962,1097930,6885408,1058323,1319437] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_8 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x1852522525259494b494925252252594949293252494a4a64a49525929324a65 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x1852522525259494b494925252252594949293252494a4a64a49525929324a65 (![2527890,1582373,4409930,2397332,1648937,4608594,3187876,4802889,2527890,1582373,4409930,2397332,1648937,4608594,3187876,4802889,2397332,1582373,1648937,2527890,4608594,4802889,3187876] : Fin 23 → ℕ)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma free_23_9 :
    let G : SimpleGraph (Fin 23) := { Adj := fun i j => i ≠ j ∧ (0x1ac0b4290a509aa0494a14350d81681681d502a2140904620c2496881d0a4873 : ℕ).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
    G.CliqueFree 3 := by
  apply tri 0x1ac0b4290a509aa0494a14350d81681681d502a2140904620c2496881d0a4873 (![1147158,802857,2368585,4332166,2103393,4335250,4866708,3506536,4855425,3506536,84260,1868824,352536,1609764,3183682,4352641,4855425,3506536,4332166,2173250,4352641,4866708,3506536] : Fin 23 → ℕ)
  decide +kernel

theorem families_free : ∀ t : Fin 2,
  let n := t.val+11
  let h := 2*n-1
  let ms := (![[0x3c03c78079e01ef00ff00f1e007803c03c00781e0f0f01e7bfc0,0x1300c9300ca601898064c034c02980260130130260984c4c9a512,0x14618714a110c3142298116d102a2148904630c2494281d0a4873,0x8c114a884942464b2022a4a428261306320822e4a4ad013060e4,0x2a0350a80582183162129c0f8001d0086405013a94461515060a0,0x320c9a068340d092240b020b03304c45222a22864d0684810665,0x9848e6152078149c905b20421622c0a5011422e4a4ad017060e4,0xb1f00c9911c54838254c9410328059521341a10461915172e0a4],[0x1f0078f803cf803df007fc01e1f001f003e00f807c003c0781e0f0f01e7bfc0,0x15402ad500aaa8056a8055500b5402aa01aa015405502a82a855154aaab556ad,0x980192600653003130032600698014c004c00980260130130260984c4c9a512,0x914a1386185108a4308c1022c86188168d102a2148904630c2494281d0a4873,0xa0c30e8a50821862a114d022c16819442d102a2148904630c2494281d0a4873,0x6c30c4d0a51091253440c310c81681861d102a2148904630c2494281d0a4873,0x660a992805aa22340c0808a41024c50724808545904048a115126182d64418,0xa1106c0984e4408060650a165e02a01953428300c30140455959a04a01a8204,0x1852522525259494b494925252252594949293252494a4a64a49525929324a65,0x1ac0b4290a509aa0494a14350d81681681d502a2140904620c2496881d0a4873]] : Fin 2 → List ℕ) t
  let C (a : Fin ms.length) : SimpleGraph (Fin h) := { Adj := fun i j => i ≠ j ∧ (ms[a.val]).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
  ∀ a, (C a).CliqueFree 3 := by
  intro t
  fin_cases t
  · dsimp only
    intro a
    change Fin 8 at a
    fin_cases a
    · exact free_21_0
    · exact free_21_1
    · exact free_21_2
    · exact free_21_3
    · exact free_21_4
    · exact free_21_5
    · exact free_21_6
    · exact free_21_7
  · dsimp only
    intro a
    change Fin 10 at a
    fin_cases a
    · exact free_23_0
    · exact free_23_1
    · exact free_23_2
    · exact free_23_3
    · exact free_23_4
    · exact free_23_5
    · exact free_23_6
    · exact free_23_7
    · exact free_23_8
    · exact free_23_9

end FixedRamseyHosts

namespace BBHFinite
open SimpleGraph

/-- A universal Ramsey containment supplies a finite extension certificate.
At each nonterminal level use all triangle-free labelled masks. -/
theorem certificate_of_universal {n N : ℕ} (pos : 0 < N) (G : SimpleGraph (Fin n))
    (universal : ∀ C : SimpleGraph (Fin N), C.CliqueFree 3 → G ⊑ Cᶜ) :
    let edge := fun (p i j : ℕ) => i≠j ∧ p.testBit (max i j * (max i j-1)/2 + min i j) = true
    ∃ A : ℕ → List ℕ, 0∈A 0 ∧ A N=[] ∧ ∀ k<N, ∀ p∈A k, ∀ s : Fin (2^k),
      let S := fun i : ℕ => s.val.testBit i = true
      let E := fun i j : Fin (k+1) =>
        if i.val=0 then j.val≠0 ∧ S (j.val-1) else if j.val=0 then S (i.val-1)
        else edge p (i.val-1) (j.val-1) ∧ ¬(S (i.val-1) ∧ S (j.val-1))
      (∃ v : Fin k, ¬S v.val ∧ ∀ u : Fin k, S u.val → ¬edge p u.val v.val) ∨
      (∃ x y, x≠y ∧ ¬E x y ∧ ∀ z, ¬(E x z ∧ E y z)) ∨
      (∃ f : Fin n ↪ Fin (k+1), ∀ x y, G.Adj x y → ¬E (f x) (f y)) ∨
      ∃ b∈A (k+1), ∃ f : Fin (k+1) ≃ Fin (k+1), ∀ x y, E x y ↔ edge b (f x).val (f y).val := by
  classical
  intro edge
  have esymm (p i j : ℕ) : edge p i j ↔ edge p j i := by
    simp only [edge,min_comm j i,max_comm j i]
    exact and_congr ne_comm Iff.rfl
  let free (k p : ℕ) := ∀ i j z : Fin k, edge p i.val j.val → edge p i.val z.val → ¬ edge p j.val z.val
  let A (k : ℕ) : List ℕ :=
    if k < N then ((Finset.range (2 ^ k.choose 2)).filter (free k)).toList else []
  have mem {k p : ℕ} (h : k < N) : p ∈ A k ↔ p < 2 ^ k.choose 2 ∧ free k p := by
    simp [A,h]
  refine ⟨A,(mem pos).mpr ⟨by decide,fun i => Fin.elim0 i⟩,by simp [A],?_⟩
  intro k hk p hp s S E
  have old := ((mem hk).mp hp).2
  have sym (x y : Fin (k+1)) : E x y ↔ E y x := by
    cases x using Fin.cases <;> cases y using Fin.cases <;>
      simp only [E,Fin.val_zero,Fin.val_succ,Nat.add_one_ne_zero,if_true,if_false,
        Nat.add_sub_cancel,ne_eq,not_false_eq_true,true_and]
    next i j => rw [esymm p i.val j.val]; tauto
  have loop (x : Fin (k+1)) : ¬ E x x := by
    cases x using Fin.cases <;> simp [E,edge]
  have noTriangle (x y z : Fin (k+1)) : E x y → E x z → ¬ E y z := by
    cases x using Fin.cases <;> cases y using Fin.cases <;> cases z using Fin.cases <;>
      simp only [E,Fin.val_zero,Fin.val_succ,Nat.add_one_ne_zero,if_true,if_false,
        Nat.add_sub_cancel,ne_eq,not_false_eq_true,not_true_eq_false,true_and,false_and,
        false_implies,not_false_eq_true]
    all_goals first | tauto | exact fun a b c => old _ _ _ a.1 b.1 c.1
  let C : SimpleGraph (Fin (k+1)) := ⟨E,⟨fun i j => (sym i j).mp⟩,⟨loop⟩⟩
  by_cases terminal : k+1 = N
  · subst N
    have ht : C.CliqueFree 3 := by
      by_contra fail
      obtain ⟨g⟩ := (not_cliqueFree_iff_top_isContained 3).mp fail
      exact noTriangle (g 0) (g 1) (g 2)
        (g.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide))
        (g.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by decide))
        (g.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide))
    obtain ⟨f⟩ := universal C ht
    exact Or.inr (Or.inr (Or.inl ⟨f.toEmbedding,fun _ _ h => (f.toHom.map_rel' h).2⟩))
  · obtain ⟨b,small,bits,_⟩ := SmallCover.Seven.encoding_spec C
    have asc (i j : Fin (k+1)) (lt : i < j) : E i j ↔ edge b i.val j.val := by
      change C.Adj i j ↔ i.val ≠ j.val ∧ b.testBit _ = true
      rw [max_eq_right (show i.val ≤ j.val from lt.le), min_eq_left (show i.val ≤ j.val from lt.le),
        ←Nat.choose_two_right, bits i j lt]
      exact ⟨fun h => ⟨Nat.ne_of_lt lt,h⟩,And.right⟩
    have enc (i j : Fin (k+1)) : E i j ↔ edge b i.val j.val := by
      rcases lt_trichotomy i j with ij|rfl|ji
      · exact asc i j ij
      · simp [edge,loop]
      · exact (sym i j).trans ((asc j i ji).trans (esymm b j.val i.val))
    have safe : free (k+1) b := fun i j z ij iz jz =>
      noTriangle i j z ((enc i j).mpr ij) ((enc i z).mpr iz) ((enc j z).mpr jz)
    exact Or.inr (Or.inr (Or.inr ⟨b,(mem (by omega)).mpr ⟨small,safe⟩,Equiv.refl _,enc⟩))

end BBHFinite

open SimpleGraph Finset

namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R2

def H1 : Prop := ∀ k : Fin 4,
  let n := k.val+9
  let q := (![16,18,23,23] : Fin 4 → ℕ) k
  let masks := (![[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 4 → List ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q →
    ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val) = false

def H2 : Prop := ∀ k : Fin 6,
  let n := k.val+7
  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k
  ∀ m ∈ masks,
    let N := 2*n-1
    let G : SimpleGraph (Fin n) := { Adj := fun i j => i ≠ j ∧ m.testBit ((min i j).val*n+(max i j).val) = false, symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩, loopless := ⟨by simp⟩ }
    let edge := fun (p i j : ℕ) => i≠j ∧ p.testBit (max i j * (max i j-1)/2 + min i j) = true
    ∃ A : ℕ → List ℕ, 0∈A 0 ∧ A N=[] ∧ ∀ k<N, ∀ p∈A k, ∀ s : Fin (2^k),
      let S := fun i : ℕ => s.val.testBit i = true
      let E := fun i j : Fin (k+1) =>
        if i.val=0 then j.val≠0 ∧ S (j.val-1) else if j.val=0 then S (i.val-1)
        else edge p (i.val-1) (j.val-1) ∧ ¬(S (i.val-1) ∧ S (j.val-1))
      (∃ v : Fin k, ¬S v.val ∧ ∀ u : Fin k, S u.val → ¬edge p u.val v.val) ∨
      (∃ x y, x≠y ∧ ¬E x y ∧ ∀ z, ¬(E x z ∧ E y z)) ∨
      (∃ f : Fin n ↪ Fin (k+1), ∀ x y, G.Adj x y → ¬E (f x) (f y)) ∨
      ∃ b∈A (k+1), ∃ f : Fin (k+1) ≃ Fin (k+1), ∀ x y, E x y ↔ edge b (f x).val (f y).val

def H3 : Prop := (let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)
  let C (a : Fin 2) : SimpleGraph (Fin 15) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 2 → Fin 8 ↪ Fin 15,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 20) ∧ (let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)
  let C (a : Fin 3) : SimpleGraph (Fin 17) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 3 → Fin 9 ↪ Fin 17,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 27)

def H4 : Prop := ∀ t : Fin 2,
  let n := t.val+11
  let h := 2*n-1
  let ms := (![[0x3c03c78079e01ef00ff00f1e007803c03c00781e0f0f01e7bfc0,0x1300c9300ca601898064c034c02980260130130260984c4c9a512,0x14618714a110c3142298116d102a2148904630c2494281d0a4873,0x8c114a884942464b2022a4a428261306320822e4a4ad013060e4,0x2a0350a80582183162129c0f8001d0086405013a94461515060a0,0x320c9a068340d092240b020b03304c45222a22864d0684810665,0x9848e6152078149c905b20421622c0a5011422e4a4ad017060e4,0xb1f00c9911c54838254c9410328059521341a10461915172e0a4],[0x1f0078f803cf803df007fc01e1f001f003e00f807c003c0781e0f0f01e7bfc0,0x15402ad500aaa8056a8055500b5402aa01aa015405502a82a855154aaab556ad,0x980192600653003130032600698014c004c00980260130130260984c4c9a512,0x914a1386185108a4308c1022c86188168d102a2148904630c2494281d0a4873,0xa0c30e8a50821862a114d022c16819442d102a2148904630c2494281d0a4873,0x6c30c4d0a51091253440c310c81681861d102a2148904630c2494281d0a4873,0x660a992805aa22340c0808a41024c50724808545904048a115126182d64418,0xa1106c0984e4408060650a165e02a01953428300c30140455959a04a01a8204,0x1852522525259494b494925252252594949293252494a4a64a49525929324a65,0x1ac0b4290a509aa0494a14350d81681681d502a2140904620c2496881d0a4873]] : Fin 2 → List ℕ) t
  let C (a : Fin ms.length) : SimpleGraph (Fin h) := { Adj := fun i j => i ≠ j ∧ (ms[a.val]).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
  ∀ f : Fin ms.length → Fin n ↪ Fin h, let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ (![41,49] : Fin 2 → ℕ) t

lemma explicit_hosts (cap : H4) : ∀ t : Fin 2,
  let n := t.val+11
  let h := 2*n-1
  let q := (![41,49] : Fin 2 → ℕ) t
  ∃ (r : ℕ) (C : Fin r → SimpleGraph (Fin h)),
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin n ↪ Fin h,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ q := by
  intro t
  let n := t.val+11
  let h := 2*n-1
  let ms := (![[0x3c03c78079e01ef00ff00f1e007803c03c00781e0f0f01e7bfc0,0x1300c9300ca601898064c034c02980260130130260984c4c9a512,0x14618714a110c3142298116d102a2148904630c2494281d0a4873,0x8c114a884942464b2022a4a428261306320822e4a4ad013060e4,0x2a0350a80582183162129c0f8001d0086405013a94461515060a0,0x320c9a068340d092240b020b03304c45222a22864d0684810665,0x9848e6152078149c905b20421622c0a5011422e4a4ad017060e4,0xb1f00c9911c54838254c9410328059521341a10461915172e0a4],[0x1f0078f803cf803df007fc01e1f001f003e00f807c003c0781e0f0f01e7bfc0,0x15402ad500aaa8056a8055500b5402aa01aa015405502a82a855154aaab556ad,0x980192600653003130032600698014c004c00980260130130260984c4c9a512,0x914a1386185108a4308c1022c86188168d102a2148904630c2494281d0a4873,0xa0c30e8a50821862a114d022c16819442d102a2148904630c2494281d0a4873,0x6c30c4d0a51091253440c310c81681861d102a2148904630c2494281d0a4873,0x660a992805aa22340c0808a41024c50724808545904048a115126182d64418,0xa1106c0984e4408060650a165e02a01953428300c30140455959a04a01a8204,0x1852522525259494b494925252252594949293252494a4a64a49525929324a65,0x1ac0b4290a509aa0494a14350d81681681d502a2140904620c2496881d0a4873]] : Fin 2 → List ℕ) t
  let C (a : Fin ms.length) : SimpleGraph (Fin h) := { Adj := fun i j => i ≠ j ∧ (ms[a.val]).testBit ((max i j).val.choose 2+(min i j).val)=true, symm := ⟨fun i j e => ⟨e.1.symm,by simpa only [min_comm j i,max_comm j i] using e.2⟩⟩, loopless := ⟨fun i e => e.1 rfl⟩ }
  exact ⟨ms.length,C,FixedRamseyHosts.families_free t,cap t⟩


lemma from_census (dense : H2) (k : Fin 6) :
  let n := k.val+7
  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k
  ∀ m ∈ masks, ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ e : Fin n ↪ Fin (2*n-1), ∀ i j, i ≠ j →
      m.testBit ((min i j).val*n+(max i j).val) = false → ¬ C.Adj (e i) (e j) := by
  let n := k.val+7
  dsimp only
  intro m hm C ht
  let G : SimpleGraph (Fin n) := { Adj := fun i j => i ≠ j ∧ m.testBit ((min i j).val*n+(max i j).val) = false, symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩, loopless := ⟨by simp⟩ }
  obtain ⟨f⟩ := BBHFinite.covers G (2*n-1) (dense k m hm) C ht
  exact ⟨f.toEmbedding, fun i j ne bit => (f.toHom.map_rel' (show G.Adj i j from ⟨ne,bit⟩)).2⟩

lemma symmetric_mask {n h m : ℕ} {C : SimpleGraph (Fin h)}
    (p : ∃ f : Fin n ↪ Fin h, ∀ i j, i < j → m.testBit (i.val*n+j.val) = false → ¬C.Adj (f i) (f j)) :
    ∃ e : Fin n ↪ Fin h, ∀ i j, i ≠ j → m.testBit ((min i j).val*n+(max i j).val) = false → ¬ C.Adj (e i) (e j) := by
  obtain ⟨f,hf⟩ := p
  refine ⟨f,?_⟩
  intro i j ne bit
  rcases lt_or_gt_of_ne ne with a|a
  · exact hf i j a (by simpa only [min_eq_left a.le,max_eq_right a.le] using bit)
  · exact fun e => hf j i a (by simpa only [min_eq_right a.le,max_eq_left a.le] using bit) e.symm

lemma assemble
    (baseSix : ∀ G : SimpleGraph (Fin 6), G.edgeSet.ncard = 8 →
    ∃ e : Fin 6 ↪ Fin 6, ∀ i j, G.Adj i j → (541065248 : ℕ).testBit ((min (e i) (e j)).val*6+(max (e i) (e j)).val)=false)
    (seven : ∀ G : SimpleGraph (Fin 7), G.Connected → G.edgeSet.ncard=11 →
    ∃ m ∈ ([8757838336, 33688088] : List ℕ), ∃ e : Fin 7 ↪ Fin 7, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*7+(max (e i) (e j)).val) = false)
    (eight : ∀ G : SimpleGraph (Fin 8), G.Connected → G.edgeSet.ncard=11 →
    ∃ m ∈ ([36169948434793600, 70781333153792] : List ℕ), ∃ e : Fin 8 ↪ Fin 8, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*8+(max (e i) (e j)).val) = false)
    (baseGood : ∀ t : Fin 3,
  let n := t.val+4
  let m := (![2048,540672,541065248] : Fin 3 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j))
    (ten : ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 19) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*19+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin 10 ↪ Fin 19,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ 33) :
    H1 → H2 → H3 → H4 → type_of% @Erdos1182.erdos_1182.variants.small_values := by
  intro sparse dense known caps
  have sparseAll : ∀ k : Fin 6,
  let n := k.val+7
  let q := (![11,11,16,18,23,23] : Fin 6 → ℕ) k
  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q →
    ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val) = false := by
    intro k
    fin_cases k
    · exact seven
    · exact eight
    · exact sparse 0
    · exact sparse 1
    · exact sparse 2
    · exact sparse 3
  have goodAll : ∀ k : Fin 9,
  let n := k.val+4
  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k
  ∀ m ∈ masks, ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ e : Fin n ↪ Fin (2*n-1), ∀ i j, i≠j → m.testBit ((min (i) (j)).val*n+(max (i) (j)).val) = false → ¬ C.Adj (e i) (e j) := by
    intro k
    fin_cases k
    · dsimp only
      intro m hm C ht
      have eq : m = 2048 := by simpa using hm
      subst m
      exact symmetric_mask (baseGood 0 C ht)
    · dsimp only
      intro m hm C ht
      have eq : m = 540672 := by simpa using hm
      subst m
      exact symmetric_mask (baseGood 1 C ht)
    · dsimp only
      intro m hm C ht
      have eq : m = 541065248 := by simpa using hm
      subst m
      exact symmetric_mask (baseGood 2 C ht)
    · exact from_census dense 0
    · exact from_census dense 1
    · exact from_census dense 2
    · exact from_census dense 3
    · exact from_census dense 4
    · exact from_census dense 5
  apply SmallTable.Root.combine
  · exact SmallTable.Sparse.combine baseSix sparseAll goodAll
  · apply SmallTable.Dense.combine
    · apply SmallTable.Witness.combine baseGood
      · intro t
        fin_cases t
        · dsimp only
          intro C ht
          obtain ⟨e,he⟩ := goodAll 3 8757838336 (by decide) C ht
          refine ⟨e, fun a b hab bit => he a b hab.ne ?_⟩
          change (8757838336 : ℕ).testBit (a.val*7+b.val) = false at bit
          rw [min_eq_left hab.le,max_eq_right hab.le]
          exact bit
        · dsimp only
          intro C ht
          obtain ⟨e,he⟩ := goodAll 4 36169948434793600 (by decide) C ht
          refine ⟨e, fun a b hab bit => he a b hab.ne ?_⟩
          change (36169948434793600 : ℕ).testBit (a.val*8+b.val) = false at bit
          rw [min_eq_left hab.le,max_eq_right hab.le]
          exact bit
      · intro t
        fin_cases t
        · dsimp only
          intro C ht
          obtain ⟨e,he⟩ := goodAll 5 2251801971660822 (by decide) C ht
          refine ⟨e, fun a b hab bit => he a b hab.ne ?_⟩
          change (2251801971660822 : ℕ).testBit (a.val*9+b.val) = false at bit
          rw [min_eq_left hab.le,max_eq_right hab.le]
          exact bit
        · dsimp only
          intro C ht
          obtain ⟨e,he⟩ := goodAll 6 618970019714747783169716278 (by decide) C ht
          refine ⟨e, fun a b hab bit => he a b hab.ne ?_⟩
          change (618970019714747783169716278 : ℕ).testBit (a.val*10+b.val) = false at bit
          rw [min_eq_left hab.le,max_eq_right hab.le]
          exact bit
      · intro t
        fin_cases t
        · dsimp only
          intro C ht
          obtain ⟨e,he⟩ := goodAll 7 158495020111019088292975255562 (by decide) C ht
          refine ⟨e, fun a b hab bit => he a b hab.ne ?_⟩
          change (158495020111019088292975255562 : ℕ).testBit (a.val*11+b.val) = false at bit
          rw [min_eq_left hab.le,max_eq_right hab.le]
          exact bit
        · dsimp only
          intro C ht
          obtain ⟨e,he⟩ := goodAll 8 14855280693082744087392632874 (by decide) C ht
          refine ⟨e, fun a b hab bit => he a b hab.ne ?_⟩
          change (14855280693082744087392632874 : ℕ).testBit (a.val*12+b.val) = false at bit
          rw [min_eq_left hab.le,max_eq_right hab.le]
          exact bit
    · apply SmallTable.Blockers.combineFamilies known.1 known.2
      intro t
      fin_cases t
      · obtain ⟨r,m,tr,cap⟩ := ten
        exact ⟨r,_,tr,cap⟩
      · exact explicit_hosts caps 0
      · exact explicit_hosts caps 1

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R2

namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R2

theorem upper_ten : Erdos1182.f 10 ≤ 33 := by
  classical
  obtain ⟨r,m,tri,cap⟩ := E1182Ten.ten
  unfold Erdos1182.f
  apply csSup_le'
  rintro k ⟨G,hc,rfl,good⟩
  by_contra! high
  obtain ⟨C,ht,miss⟩ := SmallTable.Blockers.common _ tri (fun f _ => cap f) G hc high
  exact miss ((SmallTable.Dense.good_iff (by decide) hc).mp good C ht)



theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos1182.erdos_1182.variants.small_values := by
  apply assemble (fun G h => SmallCover.Six.placed6 G h.le) SmallCover.Seven.seven_sparse SmallEight.eight_sparse
  · intro t
    fin_cases t
    · exact BBHFinite.template4
    · exact BBHFinite.template5
    · exact BBHFinite.template6
  · obtain ⟨r,m,tri,bounds⟩ := E1182Ten.ten
    exact ⟨r,m,tri,fun f _ => bounds f⟩

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R2
