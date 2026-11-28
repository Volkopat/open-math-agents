import OMAReductions.R_Erdos151_erdos_151_R1
import Mathlib

/-!
In a smallest counterexample, deleting a vertex separator of size c cannot
leave nonadjacent sides of orders a and b with c at most both H a and H b.
The constructive Ramsey inequality H (a + b + c) ≤ H a + H b permits
us to omit the separator and join the two clique-avoiding sets obtained
on the smaller sides.
-/

namespace OMA.R_Erdos151_erdos_151_R1_H1_R1

open Finset SimpleGraph
open scoped Classical

/-- The finite range of Ramsey thresholds through twelve. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    Erdos151.H (n + 1) ≤ 12 →
    Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∀ A B : Finset (Fin (n + 1)), A ∪ B = univ → A.card < n + 1 →
      B.card < n + 1 →
      (A ∩ B).card ≤ min (Erdos151.H (A \ B).card) (Erdos151.H (B \ A).card) →
      ∃ x ∈ A \ B, ∃ y ∈ B \ A, G.Adj x y) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

/-- The remaining Ramsey thresholds, with the same separation and degree conditions. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    13 ≤ Erdos151.H (n + 1) →
    Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∀ A B : Finset (Fin (n + 1)), A ∪ B = univ → A.card < n + 1 →
      B.card < n + 1 →
      (A ∩ B).card ≤ min (Erdos151.H (A \ B).card) (Erdos151.H (B \ A).card) →
      ∃ x ∈ A \ B, ∃ y ∈ B \ A, G.Adj x y) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

section Proof

open OMA.R_Erdos151_erdos_151_R1 (exists_indep_H H_le bound_of_hitting transversal_delete)

private lemma cliqueFree_comap_embedding {V W : Type*} (G : SimpleGraph V)
    (e : W ↪ V) {k : ℕ} (hG : G.CliqueFree k) : (G.comap e).CliqueFree k := by
  intro s hs
  apply hG (s.map e)
  refine ⟨?_, by rw [card_map, hs.card_eq]⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
  exact hs.isClique ha hb (fun h => hxy (congrArg e h))

private lemma extremal_triangle_free (n : ℕ) :
    ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ s : Finset (Fin n), F.IsIndepSet s → s.card ≤ Erdos151.H n := by
  let sizes : Set ℕ :=
    {k | ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s}
  have hsizes : BddAbove sizes := by
    refine ⟨n, ?_⟩
    intro k hk
    obtain ⟨s, hs⟩ := hk ⊥ (cliqueFree_bot (by norm_num))
    simpa [hs.card_eq] using card_le_univ s
  have hnot : Erdos151.H n + 1 ∉ sizes := by
    intro h
    have hle : Erdos151.H n + 1 ≤ Erdos151.H n := le_csSup hsizes h
    omega
  change ¬ (∀ F : SimpleGraph (Fin n), F.CliqueFree 3 →
    ∃ s, F.IsNIndepSet (Erdos151.H n + 1) s) at hnot
  push Not at hnot
  obtain ⟨F, hF, hsmall⟩ := hnot
  refine ⟨F, hF, ?_⟩
  intro s hs
  by_contra! h
  obtain ⟨t, hts, hcard⟩ := exists_subset_card_eq (show Erdos151.H n + 1 ≤ s.card by omega)
  refine hsmall t ⟨?_, hcard⟩
  intro x hx y hy hne
  exact hs (hts hx) (hts hy) hne

private lemma independent_embedding {n c : ℕ} (F : SimpleGraph (Fin n))
    (hF : F.CliqueFree 3) (hc : c ≤ Erdos151.H n) :
    ∃ e : Fin c ↪ Fin n, ∀ i j, ¬ F.Adj (e i) (e j) := by
  obtain ⟨s, hs⟩ := exists_indep_H n F hF
  obtain ⟨u, hus, hu⟩ := exists_subset_card_eq (hc.trans_eq hs.card_eq.symm)
  let eq : Fin c ≃ u := (equivFinOfCardEq hu).symm
  let e : Fin c ↪ Fin n := eq.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, fun i j h => ?_⟩
  exact hs.isIndepSet (hus (eq i).property) (hus (eq j).property) h.ne h

set_option maxHeartbeats 1000000 in
/-- The triangle-free instance of the Ramsey construction of Xu, Xie and
Radziszowski. Add c vertices representing independent sets in two extremal
graphs, and match the paired representatives by cross edges. -/
lemma H_expand_add_le (a b c : ℕ) (hca : c ≤ Erdos151.H a) (hcb : c ≤ Erdos151.H b) :
    Erdos151.H (a + b + c) ≤ Erdos151.H a + Erdos151.H b := by
  obtain ⟨A, hA, hAsmall⟩ := extremal_triangle_free a
  obtain ⟨B, hB, hBsmall⟩ := extremal_triangle_free b
  obtain ⟨ea, ha⟩ := independent_embedding A hA hca
  obtain ⟨eb, hb⟩ := independent_embedding B hB hcb
  let X := (Fin a ⊕ Fin b) ⊕ Fin c
  let matched (x : Fin a) (y : Fin b) := ∃ i : Fin c, ea i = x ∧ eb i = y
  let adj : X → X → Prop := fun p q =>
    match p, q with
    | .inl (.inl x), .inl (.inl y) => A.Adj x y
    | .inl (.inr x), .inl (.inr y) => B.Adj x y
    | .inl (.inl x), .inl (.inr y) | .inl (.inr y), .inl (.inl x) => matched x y
    | .inl (.inl x), .inr i | .inr i, .inl (.inl x) => A.Adj x (ea i)
    | .inl (.inr y), .inr i | .inr i, .inl (.inr y) => B.Adj y (eb i)
    | .inr _, .inr _ => False
  let F : SimpleGraph X :=
    { Adj := adj
      symm := ⟨by
        rintro ((x | x) | x) ((y | y) | y) h
        all_goals first | exact h | exact A.adj_symm h | exact B.adj_symm h⟩
      loopless := ⟨by
        rintro ((x | x) | x) h
        · exact A.irrefl h
        · exact B.irrefl h
        · exact h⟩ }
  have noA (x y z : Fin a) (xy : A.Adj x y) (xz : A.Adj x z) (yz : A.Adj y z) : False :=
    hA _ (is3Clique_triple_iff.mpr ⟨xy, xz, yz⟩)
  have noB (x y z : Fin b) (xy : B.Adj x y) (xz : B.Adj x z) (yz : B.Adj y z) : False :=
    hB _ (is3Clique_triple_iff.mpr ⟨xy, xz, yz⟩)
  have noPairA (x y : Fin a) (z : Fin b) (xy : A.Adj x y)
      (xz : matched x z) (yz : matched y z) : False := by
    obtain ⟨i, rfl, hi⟩ := xz
    obtain ⟨j, rfl, hj⟩ := yz
    have hij := eb.injective (hi.trans hj.symm)
    exact A.irrefl (hij ▸ xy)
  have noPairB (x y : Fin b) (z : Fin a) (xy : B.Adj x y)
      (xz : matched z x) (yz : matched z y) : False := by
    obtain ⟨i, hi, rfl⟩ := xz
    obtain ⟨j, hj, rfl⟩ := yz
    have hij := ea.injective (hi.trans hj.symm)
    exact B.irrefl (hij ▸ xy)
  have noCross (x : Fin a) (y : Fin b) (i : Fin c) (hxy : matched x y)
      (hxi : A.Adj x (ea i)) : False := by
    obtain ⟨j, rfl, rfl⟩ := hxy
    exact ha j i hxi
  have hF : F.CliqueFree 3 := by
    intro s hs
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.mp hs
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      rcases z with ((z | z) | z) <;> dsimp [F, adj] at hxy hxz hyz
    all_goals first
      | contradiction
      | exact noA _ _ _ hxy hxz hyz
      | exact noA _ _ _ hxz hxy hyz
      | exact noA _ _ _ hyz hxy hxz
      | exact noB _ _ _ hxy hxz hyz
      | exact noB _ _ _ hxz hxy hyz
      | exact noB _ _ _ hyz hxy hxz
      | exact noPairA _ _ _ hxy hxz hyz
      | exact noPairA _ _ _ hxz hxy hyz
      | exact noPairA _ _ _ hyz hxy hxz
      | exact noPairB _ _ _ hxy hxz hyz
      | exact noPairB _ _ _ hxz hxy hyz
      | exact noPairB _ _ _ hyz hxy hxz
      | exact noCross _ _ _ hxy hxz
      | exact noCross _ _ _ hxz hxy
      | exact noCross _ _ _ hxy hyz
      | exact noCross _ _ _ hxz hyz
      | exact noCross _ _ _ hyz hxy
      | exact noCross _ _ _ hyz hxz
  let e₁ : (Fin a ⊕ Fin b) ≃ Fin (a + b) := finSumFinEquiv
  let e₂ : Fin (a + b) ⊕ Fin c ≃ Fin (a + b + c) := finSumFinEquiv
  let e : Fin (a + b + c) ≃ X := ((e₁.sumCongr (Equiv.refl (Fin c))).trans e₂).symm
  obtain ⟨s, hs⟩ := exists_indep_H (a + b + c) (F.comap e)
    (cliqueFree_comap_embedding _ e.toEmbedding hF)
  let t := s.map e.toEmbedding
  have ht : F.IsIndepSet t := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    exact hs.isIndepSet hu hv (fun h => hxy (congrArg e h))
  let l := t.toLeft.toLeft
  let r := t.toLeft.toRight
  let extras := t.toRight
  let el := extras.filter (fun i => ea i ∉ l)
  let er := extras \ el
  let left := l ∪ el.map ea
  let right := r ∪ er.map eb
  have hl (x : Fin a) (hx : x ∈ l) : Sum.inl (Sum.inl x) ∈ t := by
    simpa only [l, mem_toLeft] using hx
  have hr (x : Fin b) (hx : x ∈ r) : Sum.inl (Sum.inr x) ∈ t := by
    simpa only [r, mem_toRight, mem_toLeft] using hx
  have he (i : Fin c) (hi : i ∈ extras) : Sum.inr i ∈ t := mem_toRight.mp hi
  have hdL : Disjoint l (el.map ea) := by
    refine disjoint_left.mpr ?_
    intro x hx hxmap
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hxmap
    exact (mem_filter.mp hi).2 hx
  have hdR : Disjoint r (er.map eb) := by
    refine disjoint_left.mpr ?_
    intro y hy hymap
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hymap
    have hil : ea i ∈ l := by
      by_contra hn
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨(mem_sdiff.mp hi).1, hn⟩)
    exact ht (hl _ hil) (hr _ hy) (by
      intro heq
      have heq' : (Sum.inl (ea i) : Fin a ⊕ Fin b) = Sum.inr (eb i) := Sum.inl.inj heq
      cases heq')
      (show matched (ea i) (eb i) from ⟨i, rfl, rfl⟩)
  have hindL : A.IsIndepSet left := by
    intro x hx y hy hne hadj
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact ht (hl _ hx) (hl _ hy) (fun e => hne (Sum.inl.inj (Sum.inl.inj e))) hadj
    · obtain ⟨i, hi, rfl⟩ := mem_map.mp hy
      exact ht (hl _ hx) (he i (mem_filter.mp hi).1) (by simp) hadj
    · obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      exact ht (hl _ hy) (he i (mem_filter.mp hi).1) (by simp) (A.adj_symm hadj)
    · obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      obtain ⟨j, _, rfl⟩ := mem_map.mp hy
      exact ha i j hadj
  have hindR : B.IsIndepSet right := by
    intro x hx y hy hne hadj
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact ht (hr _ hx) (hr _ hy) (fun e => hne (Sum.inr.inj (Sum.inl.inj e))) hadj
    · obtain ⟨i, hi, rfl⟩ := mem_map.mp hy
      exact ht (hr _ hx) (he i (mem_sdiff.mp hi).1) (by simp) hadj
    · obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      exact ht (hr _ hy) (he i (mem_sdiff.mp hi).1) (by simp) (B.adj_symm hadj)
    · obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      obtain ⟨j, _, rfl⟩ := mem_map.mp hy
      exact hb i j hadj
  have hcl : left.card = l.card + el.card := by
    change (l ∪ el.map ea).card = _
    rw [card_union_of_disjoint hdL, card_map]
  have hcr : right.card = r.card + er.card := by
    change (r ∪ er.map eb).card = _
    rw [card_union_of_disjoint hdR, card_map]
  have hec : er.card + el.card = extras.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have hparts : l.card + r.card = t.toLeft.card := card_toLeft_add_card_toRight
  have htotal : t.toLeft.card + extras.card = t.card := card_toLeft_add_card_toRight
  have hcard : t.card = Erdos151.H (a + b + c) := by simp [t, hs.card_eq]
  have hleft := hAsmall _ hindL
  have hright := hBsmall _ hindR
  omega

/-- Pull back an ambient maximal clique wholly contained in an induced subgraph.
The argument is adapted from the pullback lemma in reduction R2 by sun-jiao. -/
private lemma pullback_big_clique {m n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin m ↪ Fin n)
    (t : Finset (Fin n)) (ht : G.IsBigMaximalClique t)
    (hr : ∀ x ∈ t, ∃ i, e i = x) :
    (G.comap e).IsBigMaximalClique (t.preimage e e.injective.injOn) := by
  let u := t.preimage e e.injective.injOn
  have heq : u.map e = t := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      exact mem_preimage.mp hi
    · intro hx
      obtain ⟨i, rfl⟩ := hr x hx
      exact mem_map.mpr ⟨i, mem_preimage.mpr hx, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    exact ht.1.1 (mem_preimage.mp hi) (mem_preimage.mp hj) (e.injective.ne hij)
  · intro w hw huw j hj
    have hc : G.IsClique (↑(w.map e) : Set (Fin n)) := by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_map.mp hy
      exact hw hi hk (fun h => hxy (congrArg e h))
    have hsub : t ⊆ w.map e := by
      rw [← heq]
      exact map_subset_map.mpr huw
    exact mem_preimage.mpr (ht.1.2 hc hsub (mem_map.mpr ⟨j, hj, rfl⟩))
  · have h := ht.2
    rwa [← heq, card_map] at h

private lemma free_set_on {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (hG : G.CliqueFree 4)
    (hbound : ∀ J : SimpleGraph (Fin U.card), J.CliqueFree 4 →
      cliqueTransversalNumber J ≤ U.card - Erdos151.H U.card) :
    ∃ S : Finset (Fin n), S ⊆ U ∧ Erdos151.H U.card ≤ S.card ∧
      ∀ t, G.IsBigMaximalClique t → ¬ t ⊆ S := by
  let eq : Fin U.card ≃ U := (Finset.equivFin U).symm
  let e : Fin U.card ↪ Fin n := eq.toEmbedding.trans (Function.Embedding.subtype _)
  let J := G.comap e
  have hJ := hbound J (cliqueFree_comap_embedding G e hG)
  have hne : {k | ∃ T : Finset (Fin U.card), J.IsCliqueTransversal T ∧ T.card = k}.Nonempty :=
    ⟨univ.card, univ, fun t ht => by
      obtain ⟨a, -, ha, -⟩ := one_lt_card_iff.mp ht.2
      exact ⟨a, ha, mem_univ a⟩, rfl⟩
  obtain ⟨T, hT, hTcard⟩ := Nat.sInf_mem hne
  change T.card = cliqueTransversalNumber J at hTcard
  have hS := H_le U.card
  refine ⟨Tᶜ.map e, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    exact (eq i).property
  · rw [card_map, card_compl, Fintype.card_fin]
    omega
  · intro t ht hsub
    have hr : ∀ x ∈ t, ∃ i, e i = x := by
      intro x hx
      obtain ⟨i, _, hi⟩ := mem_map.mp (hsub hx)
      exact ⟨i, hi⟩
    obtain ⟨i, hi, hiT⟩ := hT _ (pullback_big_clique G e t ht hr)
    obtain ⟨j, hj, he⟩ := mem_map.mp (hsub (mem_preimage.mp hi))
    have hji : j = i := e.injective he
    subst j
    exact (mem_compl.mp hj) hiT

private lemma bound_of_free_set {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : Erdos151.H n ≤ S.card)
    (hfree : ∀ t, G.IsBigMaximalClique t → ¬ t ⊆ S) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  have hT : G.IsCliqueTransversal Sᶜ := by
    intro t ht
    by_contra! h
    exact hfree t ht fun x hx => by simpa using h x hx
  have h := csInf_le' (show Sᶜ.card ∈ {k | ∃ T, G.IsCliqueTransversal T ∧ T.card = k}
    from ⟨Sᶜ, hT, rfl⟩)
  change cliqueTransversalNumber G ≤ Sᶜ.card at h
  rw [card_compl, Fintype.card_fin] at h
  exact h.trans (Nat.sub_le_sub_left hS n)

private lemma neighborhood_bound {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hv : Erdos151.H n ≤ (univ.filter (G.Adj v)).card) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  refine bound_of_free_set G _ hv ?_
  intro t ht hsub
  have hAdj (w : Fin n) (hw : w ∈ t) : G.Adj v w := (mem_filter.mp (hsub hw)).2
  have hc : G.IsClique (↑(insert v t) : Set (Fin n)) := by
    rw [coe_insert]
    exact ht.1.1.insert (fun w hw _ => hAdj w hw)
  exact G.irrefl (hAdj v (ht.1.2 hc (subset_insert _ _) (mem_insert_self _ _)))

/-- If the separator is small compared with both sides, omit it entirely. -/
lemma bound_of_ramsey_separator {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (A B : Finset (Fin n))
    (hcover : A ∪ B = univ) (ha : A.card < n) (hb : B.card < n)
    (hinter : (A ∩ B).card ≤ min (Erdos151.H (A \ B).card) (Erdos151.H (B \ A).card))
    (hcross : ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y)
    (ih : ∀ m < n, ∀ J : SimpleGraph (Fin m), J.CliqueFree 4 →
      cliqueTransversalNumber J ≤ m - Erdos151.H m) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  have hAB : (A \ B).card < n := (card_le_card sdiff_subset).trans_lt ha
  have hBA : (B \ A).card < n := (card_le_card sdiff_subset).trans_lt hb
  obtain ⟨S, hSA, hSc, hS⟩ := free_set_on G (A \ B) hG (ih _ hAB)
  obtain ⟨T, hTB, hTc, hT⟩ := free_set_on G (B \ A) hG (ih _ hBA)
  have hA := card_sdiff_add_card_inter A B
  have hB := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hB
  have hn := card_union_add_card_inter A B
  rw [hcover, card_univ, Fintype.card_fin] at hn
  have hn' : (A \ B).card + (B \ A).card + (A ∩ B).card = n := by omega
  have hH := H_expand_add_le (A \ B).card (B \ A).card (A ∩ B).card
    (hinter.trans (min_le_left _ _)) (hinter.trans (min_le_right _ _))
  rw [hn'] at hH
  have hdisj : Disjoint S T := by
    refine disjoint_left.mpr ?_
    intro x hxs hxt
    exact (mem_sdiff.mp (hSA hxs)).2 (mem_sdiff.mp (hTB hxt)).1
  refine bound_of_free_set G (S ∪ T) ?_ ?_
  · rw [card_union_of_disjoint hdisj]
    omega
  · intro t ht hsub
    by_cases htS : t ⊆ S
    · exact hS t ht htS
    · obtain ⟨y, hyt, hyS⟩ := not_subset.mp htS
      have hyT := (mem_union.mp (hsub hyt)).resolve_left hyS
      apply hT t ht
      intro x hxt
      by_contra hxT
      have hxS := (mem_union.mp (hsub hxt)).resolve_right hxT
      have hxy : x ≠ y := fun heq => hyS (heq ▸ hxS)
      exact hcross x (hSA hxS) y (hTB hyT) (ht.1.1 hxt hyt hxy)

private lemma all_orders (h1 : H1) (h2 : H2) (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) : cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine bound_of_free_set G ∅ (by simpa using H_le 0) ?_
      intro t ht _
      obtain ⟨a, -, ha, -⟩ := one_lt_card_iff.mp ht.2
      exact a.elim0
    | succ n =>
      by_cases hjump : Erdos151.H n < Erdos151.H (n + 1)
      swap
      · have hsmall := ih n (by omega) (G.comap (Fin.castSucc : Fin n → Fin (n + 1)))
          (cliqueFree_comap_embedding G Fin.castSuccEmb hG)
        have hdel := transversal_delete n G
        have hn := H_le n
        omega
      by_cases hhit : ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
        ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v
      · obtain ⟨F, hF, hit⟩ := hhit
        exact bound_of_hitting (n + 1) G F hF hit
      by_cases hdeg : ∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)
      swap
      · push Not at hdeg
        obtain ⟨v, hv⟩ := hdeg
        exact neighborhood_bound G v hv
      by_cases hsep : ∀ A B : Finset (Fin (n + 1)), A ∪ B = univ →
        A.card < n + 1 → B.card < n + 1 →
        (A ∩ B).card ≤ min (Erdos151.H (A \ B).card) (Erdos151.H (B \ A).card) →
        ∃ x ∈ A \ B, ∃ y ∈ B \ A, G.Adj x y
      · by_cases hthreshold : Erdos151.H (n + 1) ≤ 12
        · exact h1 n G hthreshold hjump hG hdeg hhit hsep
        · exact h2 n G (by omega) hjump hG hdeg hhit hsep
      · push Not at hsep
        obtain ⟨A, B, hcover, ha, hb, hinter, hcross⟩ := hsep
        exact bound_of_ramsey_separator G hG A B hcover ha hb hinter hcross ih

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_R1.H1 := by
  intro h1 h2 n G _ hG _
  exact all_orders h1 h2 (n + 1) G hG

end Proof

end OMA.R_Erdos151_erdos_151_R1_H1_R1
