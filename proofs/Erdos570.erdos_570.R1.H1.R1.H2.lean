import OMAReductions.R_Erdos570_erdos_570_R1_H1_R1
import Mathlib

/-!
# Dense connected targets for Erdős Problem 570

For every `k ≥ 3` and every `C_k`-free graph `R` on `N` vertices, each neighborhood `R[N(v)]`
is `P_{k-1}`-free and hence `(k - 3)`-degenerate. Consequently either some neighborhood already
contains an independent set of size `n`, or `R` has maximum degree `< (k - 2) * n` and at most
`(k - 3) * N * d / 3` triangles. Deleting one vertex per triangle after random vertex sampling
produces a triangle-free induced subgraph to which Shearer's bound applies, showing
`R(C_k, K_n) = o(n^2)` and settling the dense regime `H2`.
-/

namespace Erdos570DenseH2

open SimpleGraph Finset

/- ### Part 1: Basic graph helpers and independent sets -/

private lemma isContained_compl_of_indepSet {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (R : SimpleGraph V) (I : Finset V)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) (hcard : Fintype.card W ≤ I.card) :
    H ⊑ Rᶜ := by
  have hle : Fintype.card W ≤ Fintype.card I := by simpa using hcard
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  refine ⟨⟨⟨fun w => (f w).1, ?_⟩, ?_⟩⟩
  · intro x y hxy
    have hne : (f x).1 ≠ (f y).1 := fun h => hxy.ne (f.injective (Subtype.ext h))
    exact ⟨hne, hind _ (f x).2 _ (f y).2⟩
  · intro x y h
    exact f.injective (Subtype.ext h)

private lemma isContained_induce_mono {V : Type} (R : SimpleGraph V) {S T : Finset V}
    (hsub : S ⊆ T) : R.induce (S : Set V) ⊑ R.induce (T : Set V) := by
  refine ⟨⟨⟨fun x => ⟨x.1, hsub x.2⟩, fun h => h⟩, ?_⟩⟩
  intro a b h
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

private lemma copy_of_chain {V : Type*} {G : SimpleGraph V} {p : List V}
    (nd : p.Nodup) (chain : p.IsChain G.Adj) {k : ℕ} (hk : k ≤ p.length) :
    pathGraph k ⊑ G := by
  let f (i : Fin k) := p.get (Fin.castLE hk i)
  have inj : Function.Injective f := by
    intro i j h
    have h' := nd.get_inj_iff.mp h
    exact Fin.ext (congrArg (fun a : Fin p.length => a.val) h')
  refine ⟨⟨⟨f, ?_⟩, inj⟩⟩
  intro i j hij
  have step (a b : Fin k) (hab : a.val + 1 = b.val) : G.Adj (f a) (f b) := by
    have h := (List.isChain_iff_getElem.mp chain) a.val (by omega : a.val + 1 < p.length)
    simpa [f, List.get_eq_getElem, hab] using h
  rcases pathGraph_adj.mp hij with h | h
  · exact step i j h
  · exact (step j i h).symm

private lemma close_path {V : Type} (R : SimpleGraph V) (v : V) (l : ℕ)
    (h : pathGraph (l + 1) ⊑ R.induce (R.neighborSet v)) : cycleGraph (l + 2) ⊑ R := by
  classical
  obtain ⟨p⟩ := h
  let f : Fin (l + 2) → V := Fin.cases v (fun i => (p i).val)
  have adj (i : Fin (l + 1)) : R.Adj v (p i).val := (p i).property
  have consecutive (i j : Fin (l + 1)) (h : (i.succ - j.succ).val = 1) : j.val + 1 = i.val := by
    by_cases hle : j.succ ≤ i.succ
    · rw [Fin.sub_val_of_le hle] at h
      simp only [Fin.val_succ] at h
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
      simp only [Fin.val_succ] at h
      omega
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro a b hab
    refine Fin.cases (motive := fun a => ∀ b, (cycleGraph (l + 2)).Adj a b → R.Adj (f a) (f b))
      (fun b => ?_) (fun i b => ?_) a b hab
    · refine Fin.cases (fun h => False.elim (h.ne rfl)) (fun j _ => adj j) b
    · refine Fin.cases (fun _ => (adj i).symm) (fun j h => ?_) b
      apply p.toHom.map_adj
      apply pathGraph_adj.mpr
      exact (cycleGraph_adj'.mp h).elim
        (fun e => Or.inr (consecutive i j e)) (fun e => Or.inl (consecutive j i e))
  · intro a b eq
    refine Fin.cases (motive := fun a => ∀ b, f a = f b → a = b)
      (fun b => ?_) (fun i b => ?_) a b eq
    · exact Fin.cases (fun _ => rfl) (fun j e => False.elim ((adj j).ne e)) b
    · exact Fin.cases (fun e => False.elim ((adj i).ne e.symm))
        (fun j e => congrArg Fin.succ (p.injective (Subtype.ext e))) b

private lemma no_path_in_neighborFinset {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hfree : ¬ cycleGraph k ⊑ R) (v : V) :
    ¬ pathGraph (k - 1) ⊑ R.induce ((R.neighborFinset v : Finset V) : Set V) := by
  intro hp
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
  have hset : ((R.neighborFinset v : Finset V) : Set V) = R.neighborSet v := by
    ext x; simp [SimpleGraph.mem_neighborSet]
  rw [show l + 2 - 1 = l + 1 by omega, hset] at hp
  exact hfree (close_path R v l hp)

/- ### Part 2: Degeneracy, directed edge count, and independent sets in path-free sets -/

private def degIn {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (u : V) : ℕ :=
  (R.neighborFinset u ∩ S).card

private def dirEdges {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) : ℕ :=
  ∑ u ∈ S, degIn R S u

private def ordTriangles {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ R.neighborFinset u ∩ S, (R.neighborFinset v ∩ (R.neighborFinset u ∩ S)).card

private lemma exists_low_deg_of_no_path {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (hS : S.Nonempty)
    {r : ℕ} (hr : 1 ≤ r) (hfree : ¬ pathGraph (r + 1) ⊑ R.induce (S : Set V)) :
    ∃ u ∈ S, degIn R S u < r := by
  by_contra h
  push Not at h
  have build : ∀ m : ℕ, 1 ≤ m → m ≤ r + 1 →
      ∃ p : List V, p.length = m ∧ p.Nodup ∧ p.IsChain R.Adj ∧ ∀ x ∈ p, x ∈ S := by
    intro m hm1 hmr
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      · subst hm0
        obtain ⟨u, hu⟩ := hS
        exact ⟨[u], rfl, List.nodup_singleton u, by simp, fun x hx => by
          simp only [List.mem_singleton] at hx; exact hx ▸ hu⟩
      · obtain ⟨p, hlen, hnd, hch, hsub⟩ := ih (by omega) (by omega)
        cases p with
        | nil => simp at hlen; omega
        | cons v tail =>
          have hvS : v ∈ S := hsub v (List.mem_cons_self ..)
          have hdeg : r ≤ (R.neighborFinset v ∩ S).card := h v hvS
          have htail : tail.toFinset.card < r := by
            have h1 : tail.toFinset.card ≤ tail.length := List.toFinset_card_le tail
            simp only [List.length_cons] at hlen
            omega
          have hdiff : ((R.neighborFinset v ∩ S) \ tail.toFinset).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            have hsub' : R.neighborFinset v ∩ S ⊆ tail.toFinset := Finset.sdiff_eq_empty_iff_subset.mp hemp
            have := Finset.card_le_card hsub'
            omega
          obtain ⟨w, hw⟩ := hdiff
          rw [Finset.mem_sdiff, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
            List.mem_toFinset] at hw
          have hwv : w ≠ v := hw.1.1.ne'
          have hwnot : w ∉ v :: tail := by
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | ht
            · exact hwv rfl
            · exact hw.2 ht
          refine ⟨w :: v :: tail, by simp [hlen], List.nodup_cons.mpr ⟨hwnot, hnd⟩,
            List.isChain_cons_cons.mpr ⟨hw.1.1.symm, hch⟩, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hrest
          · exact hw.1.2
          · exact hsub x hrest
  obtain ⟨p, hlen, hnd, hch, hsub⟩ := build (r + 1) (by omega) le_rfl
  let pS : List (S : Set V) := p.pmap (fun x hx => ⟨x, hx⟩) hsub
  have hpS_len : pS.length = r + 1 := by simp [pS, hlen]
  have hpS_nd : pS.Nodup := by
    refine List.Nodup.pmap (fun a _ b _ h => congrArg Subtype.val h) hnd
  have hpS_ch : pS.IsChain (R.induce (S : Set V)).Adj := by
    rw [List.isChain_iff_getElem] at hch ⊢
    intro i hi
    have hi' : i + 1 < p.length := by simpa [pS] using hi
    have := hch i hi'
    simpa [pS, SimpleGraph.induce_adj] using this
  exact hfree (copy_of_chain hpS_nd hpS_ch hpS_len.ge)

private lemma dirEdges_erase {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) {u : V} (hu : u ∈ S) :
    dirEdges R S = dirEdges R (S.erase u) + 2 * degIn R S u := by
  unfold dirEdges degIn
  rw [← Finset.add_sum_erase _ _ hu]
  have hdiff : ∑ x ∈ S.erase u, (R.neighborFinset x ∩ S).card =
      ∑ x ∈ S.erase u, (R.neighborFinset x ∩ S.erase u).card +
      ∑ x ∈ S.erase u, (if R.Adj x u then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hadj : R.Adj x u
    · have hmem : u ∈ R.neighborFinset x ∩ S := by
        simp [SimpleGraph.mem_neighborFinset, hadj, hu]
      have heq : R.neighborFinset x ∩ S.erase u = (R.neighborFinset x ∩ S).erase u := by
        ext y; simp [Finset.mem_erase, Finset.mem_inter]; tauto
      rw [if_pos hadj, heq, Finset.card_erase_add_one hmem]
    · have heq : R.neighborFinset x ∩ S.erase u = R.neighborFinset x ∩ S := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun hyu => hadj (hyu ▸ h1), h2⟩
      rw [if_neg hadj, heq, add_zero]
  have hsum_adj : ∑ x ∈ S.erase u, (if R.Adj x u then 1 else 0) = (R.neighborFinset u ∩ S).card := by
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hxS⟩, hxu⟩; exact ⟨hxu.symm, hxS⟩
    · rintro ⟨hux, hxS⟩; exact ⟨⟨hux.ne', hxS⟩, hux.symm⟩
  rw [hdiff, hsum_adj]
  omega

private lemma dirEdges_le_of_no_path {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] {r : ℕ} (hr : 1 ≤ r) :
    ∀ S : Finset V, ¬ pathGraph (r + 1) ⊑ R.induce (S : Set V) →
      dirEdges R S ≤ 2 * (r - 1) * S.card := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    intro hfree
    rw [← hcard]
    by_cases hS : S.Nonempty
    · obtain ⟨u, huS, hdeg⟩ := exists_low_deg_of_no_path R S hS hr hfree
      have hfree' : ¬ pathGraph (r + 1) ⊑ R.induce ((S.erase u : Finset V) : Set V) :=
        fun hp => hfree (hp.trans (isContained_induce_mono R (Finset.erase_subset u S)))
      have hcard' : (S.erase u).card < m := by
        rw [Finset.card_erase_of_mem huS, hcard]; have := Finset.card_pos.mpr hS; omega
      have hih := ih (S.erase u).card hcard' (S.erase u) rfl hfree'
      rw [dirEdges_erase R S huS]
      have hcs : S.card = (S.erase u).card + 1 := (Finset.card_erase_add_one huS).symm
      rw [hcs, mul_add, mul_one]
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      simp [dirEdges]

private lemma indep_of_no_path {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] {r : ℕ} (hr : 1 ≤ r) :
    ∀ S : Finset V, ¬ pathGraph (r + 1) ⊑ R.induce (S : Set V) →
      ∃ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) ∧ S.card ≤ r * I.card := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    intro hfree
    by_cases hS : S.Nonempty
    · obtain ⟨u, huS, hdeg⟩ := exists_low_deg_of_no_path R S hS hr hfree
      let S' : Finset V := S \ insert u (R.neighborFinset u ∩ S)
      have hS'sub : S' ⊆ S := Finset.sdiff_subset
      have hfree' : ¬ pathGraph (r + 1) ⊑ R.induce ((S' : Finset V) : Set V) :=
        fun hp => hfree (hp.trans (isContained_induce_mono R hS'sub))
      have hdel_sub : insert u (R.neighborFinset u ∩ S) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hmem
        · exact huS
        · exact (Finset.mem_inter.mp hmem).2
      have hdel_card : (insert u (R.neighborFinset u ∩ S)).card ≤ r := by
        have hnot : u ∉ R.neighborFinset u ∩ S := by simp [SimpleGraph.mem_neighborFinset]
        rw [Finset.card_insert_of_notMem hnot]
        exact hdeg
      have hS'_card : S'.card = S.card - (insert u (R.neighborFinset u ∩ S)).card :=
        Finset.card_sdiff_of_subset hdel_sub
      have hdel_le : (insert u (R.neighborFinset u ∩ S)).card ≤ S.card := Finset.card_le_card hdel_sub
      have hpos : 0 < (insert u (R.neighborFinset u ∩ S)).card :=
        Finset.card_pos.mpr ⟨u, Finset.mem_insert_self _ _⟩
      have hlt : S'.card < m := by omega
      obtain ⟨I', hI'sub, hI'ind, hI'card⟩ := ih S'.card hlt S' rfl hfree'
      have hu_not_I' : u ∉ I' := by
        intro huI'
        have := hI'sub huI'
        simp [S'] at this
      refine ⟨insert u I', ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxI'
        · exact huS
        · exact hS'sub (hI'sub hxI')
      · intro x hx y hy hadj
        rcases Finset.mem_insert.mp hx with rfl | hxI' <;>
        rcases Finset.mem_insert.mp hy with rfl | hyI'
        · exact hadj.ne rfl
        · have hyS' := hI'sub hyI'
          simp only [S', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
            SimpleGraph.mem_neighborFinset] at hyS'
          exact hyS'.2 (Or.inr ⟨hadj, hyS'.1⟩)
        · have hxS' := hI'sub hxI'
          simp only [S', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
            SimpleGraph.mem_neighborFinset] at hxS'
          exact hxS'.2 (Or.inr ⟨hadj.symm, hxS'.1⟩)
        · exact hI'ind x hxI' y hyI' hadj
      · rw [← hcard, Finset.card_insert_of_notMem hu_not_I', mul_add, mul_one]
        omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      refine ⟨∅, Subset.rfl, by simp, ?_⟩
      rw [← hcard]; simp

private lemma ordTriangles_le_of_no_cycle {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hfree : ¬ cycleGraph k ⊑ R) :
    ordTriangles R Finset.univ ≤ 2 * (k - 3) * dirEdges R Finset.univ := by
  unfold ordTriangles dirEdges degIn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have h1 : ∑ u ∈ R.neighborFinset v ∩ Finset.univ,
      (R.neighborFinset u ∩ (R.neighborFinset v ∩ Finset.univ)).card =
      dirEdges R (R.neighborFinset v) := by
    simp [dirEdges, degIn]
  rw [h1]
  have hnp := no_path_in_neighborFinset R hk hfree v
  have hnp' : ¬ pathGraph (k - 2 + 1) ⊑ R.induce ((R.neighborFinset v : Finset V) : Set V) := by
    rwa [show k - 2 + 1 = k - 1 by omega]
  have h2 := dirEdges_le_of_no_path R (r := k - 2) (by omega) (R.neighborFinset v) hnp'
  simpa [show k - 2 - 1 = k - 3 by omega] using h2

/- ### Part 3: Greedy / Turán independent set bound -/

private lemma greedy_indep_bound {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (hS : S.Nonempty) :
    ∃ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) ∧
      (S.card : ℝ) ^ 2 ≤ (I.card : ℝ) * ((dirEdges R S : ℝ) + (S.card : ℝ)) := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    obtain ⟨u, huS, humin⟩ := Finset.exists_min_image S (degIn R S) hS
    let B : Finset V := insert u (R.neighborFinset u ∩ S)
    have hBsub : B ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hm
      · exact huS
      · exact (Finset.mem_inter.mp hm).2
    have hu_not_N : u ∉ R.neighborFinset u ∩ S := by simp [SimpleGraph.mem_neighborFinset]
    have hBcard : B.card = degIn R S u + 1 := by
      simp [B, degIn, Finset.card_insert_of_notMem hu_not_N]
    let S' : Finset V := S \ B
    have hS'sub : S' ⊆ S := Finset.sdiff_subset
    have hcard_split : S'.card + B.card = S.card := by
      rw [Finset.card_sdiff_of_subset hBsub]
      have := Finset.card_le_card hBsub
      omega
    have hdir_drop : dirEdges R S' + B.card * degIn R S u ≤ dirEdges R S := by
      have h1 : dirEdges R S = ∑ x ∈ B, degIn R S x + ∑ x ∈ S', degIn R S x := by
        unfold dirEdges
        have hdisj : Disjoint B S' := Finset.disjoint_sdiff
        have hunion : B ∪ S' = S := Finset.union_sdiff_of_subset hBsub
        rw [← Finset.sum_union hdisj, hunion]
      have h2 : B.card * degIn R S u ≤ ∑ x ∈ B, degIn R S x := by
        calc B.card * degIn R S u = ∑ _x ∈ B, degIn R S u := by simp
          _ ≤ ∑ x ∈ B, degIn R S x := Finset.sum_le_sum fun x hx => humin x (hBsub hx)
      have h3 : dirEdges R S' ≤ ∑ x ∈ S', degIn R S x := by
        unfold dirEdges degIn
        refine Finset.sum_le_sum fun x _ => Finset.card_le_card (Finset.inter_subset_inter_left hS'sub)
      omega
    by_cases hS' : S'.Nonempty
    · have hlt : S'.card < m := by omega
      obtain ⟨I', hI'sub, hI'ind, hI'bound⟩ := ih S'.card hlt S' hS' rfl
      have hu_not_I' : u ∉ I' := by
        intro hm
        have := hI'sub hm
        simp [S', B] at this
      refine ⟨insert u I', ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hm
        · exact huS
        · exact hS'sub (hI'sub hm)
      · intro x hx y hy hadj
        rcases Finset.mem_insert.mp hx with rfl | hxI' <;>
        rcases Finset.mem_insert.mp hy with rfl | hyI'
        · exact hadj.ne rfl
        · have hyS' := hI'sub hyI'
          simp only [S', B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
            SimpleGraph.mem_neighborFinset] at hyS'
          exact hyS'.2 (Or.inr ⟨hadj, hyS'.1⟩)
        · have hxS' := hI'sub hxI'
          simp only [S', B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
            SimpleGraph.mem_neighborFinset] at hxS'
          exact hxS'.2 (Or.inr ⟨hadj.symm, hxS'.1⟩)
        · exact hI'ind x hxI' y hyI' hadj
      · rw [← hcard, Finset.card_insert_of_notMem hu_not_I']
        have hI'pos : (0 : ℝ) < (I'.card : ℝ) := by
          have hS'pos : (0 : ℝ) < (S'.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS')
          by_contra hle
          push Not at hle
          have h0 : (I'.card : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
          rw [h0, zero_mul] at hI'bound
          nlinarith
        have hcs : ((S'.card : ℝ) + (B.card : ℝ)) ^ 2 * (I'.card : ℝ) ≤
            ((I'.card : ℝ) + 1) * ((S'.card : ℝ) ^ 2 + (I'.card : ℝ) * (B.card : ℝ) ^ 2) := by
          have : 0 ≤ ((S'.card : ℝ) - (I'.card : ℝ) * (B.card : ℝ)) ^ 2 := sq_nonneg _
          nlinarith
        have hsplitR : (S.card : ℝ) = (S'.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard_split.symm
        have hdropR : (dirEdges R S' : ℝ) + (S'.card : ℝ) + (B.card : ℝ) ^ 2 ≤
            (dirEdges R S : ℝ) + (S.card : ℝ) := by
          have hd : (dirEdges R S' : ℝ) + (B.card : ℝ) * (degIn R S u : ℝ) ≤ (dirEdges R S : ℝ) := by
            exact_mod_cast hdir_drop
          have hb : (B.card : ℝ) = (degIn R S u : ℝ) + 1 := by exact_mod_cast hBcard
          nlinarith
        have hcomb : (S'.card : ℝ) ^ 2 + (I'.card : ℝ) * (B.card : ℝ) ^ 2 ≤
            (I'.card : ℝ) * ((dirEdges R S : ℝ) + (S.card : ℝ)) := by
          nlinarith
        have hstep : (S.card : ℝ) ^ 2 * (I'.card : ℝ) ≤
            (((I'.card : ℝ) + 1) * ((dirEdges R S : ℝ) + (S.card : ℝ))) * (I'.card : ℝ) := by
          rw [hsplitR]
          have hmul : ((I'.card : ℝ) + 1) * ((S'.card : ℝ) ^ 2 + (I'.card : ℝ) * (B.card : ℝ) ^ 2) ≤
              ((I'.card : ℝ) + 1) * ((I'.card : ℝ) * ((dirEdges R S : ℝ) + ((S'.card : ℝ) + (B.card : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rwa [← hsplitR]
          linarith
        have hres := le_of_mul_le_mul_right hstep hI'pos
        simpa [Nat.cast_add, Nat.cast_one] using hres
    · rw [Finset.not_nonempty_iff_eq_empty] at hS'
      have hSB : S.card = B.card := by simp [hS'] at hcard_split; omega
      refine ⟨{u}, Finset.singleton_subset_iff.mpr huS, ?_, ?_⟩
      · intro x hx y hy hadj
        simp only [Finset.mem_singleton] at hx hy
        exact hadj.ne (hx.trans hy.symm)
      · rw [← hcard]
        simp only [Finset.card_singleton, Nat.cast_one, one_mul]
        have hd : (B.card : ℝ) * (degIn R S u : ℝ) ≤ (dirEdges R S : ℝ) := by
          have : B.card * degIn R S u ≤ dirEdges R S := by omega
          exact_mod_cast this
        have hb : (B.card : ℝ) = (degIn R S u : ℝ) + 1 := by exact_mod_cast hBcard
        have hs : (S.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hSB
        nlinarith

/- ### Part 4: Shearer's function via its integral representation -/

private noncomputable def shearerF (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) / (1 - t + x * t)

private noncomputable def shearerF' (x : ℝ) : ℝ :=
  - ∫ t in (0 : ℝ)..1, (t * (1 - t)) / (1 - t + x * t) ^ 2

private lemma denom_pos {x t : ℝ} (hx : 0 < x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < 1 - t + x * t := by
  by_cases ht : t = 0
  · subst ht; norm_num
  · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    nlinarith

private lemma denom_ne_zero {x t : ℝ} (hx : 0 < x) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    1 - t + x * t ≠ 0 := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact ne_of_gt (denom_pos hx ht.1 ht.2)

private lemma shearerF_zero : shearerF 0 = 1 := by
  unfold shearerF
  have h2 : ∫ t in (0 : ℝ)..1, (1 - t) / (1 - t + 0 * t) = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne1 : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne1] with t ht _
    have hsub : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    simp [div_self hsub]
  rw [h2]
  simp

private lemma shearerF'_nonpos {x : ℝ} (hx : 0 < x) : shearerF' x ≤ 0 := by
  unfold shearerF'
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (t * (1 - t)) / (1 - t + x * t) ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    have hden : 0 < (1 - t + x * t) ^ 2 := sq_pos_of_pos (denom_pos hx ht.1 ht.2)
    have hnum : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
    exact div_nonneg hnum hden.le
  linarith

private lemma shearerF_ode {x : ℝ} (hx : 0 < x) :
    (x + 1) * shearerF x + (x ^ 2 - x) * shearerF' x = 1 := by
  unfold shearerF shearerF'
  have hc1 : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + x * t)) (Set.uIcc 0 1) := by
    refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hx ht)
    exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
  have hc2 : ContinuousOn (fun t : ℝ => (t * (1 - t)) / (1 - t + x * t) ^ 2) (Set.uIcc 0 1) := by
    refine ContinuousOn.div (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn ?_
      (fun t ht => pow_ne_zero 2 (denom_ne_zero hx ht))
    exact (((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).pow 2).continuousOn
  have hi1 : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 - t + x * t)) MeasureTheory.volume 0 1 :=
    hc1.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => (t * (1 - t)) / (1 - t + x * t) ^ 2) MeasureTheory.volume 0 1 :=
    hc2.intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, mul_neg, ← neg_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
  let H : ℝ → ℝ := fun t => t + x * t * (1 - t) / (1 - t + x * t)
  have hHderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt H ((x + 1) * ((1 - t) / (1 - t + x * t)) +
        -(x ^ 2 - x) * (t * (1 - t) / (1 - t + x * t) ^ 2)) t := by
    intro t ht
    have hden : 1 - t + x * t ≠ 0 := denom_ne_zero hx ht
    have hsub1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id' t).const_sub (1 : ℝ)
    have hmulx : HasDerivAt (fun s : ℝ => x * s) x t := by
      simpa using (hasDerivAt_id' t).const_mul x
    have hd_num : HasDerivAt (fun s : ℝ => x * s * (1 - s)) (x * (1 - t) + x * t * (-1)) t :=
      hmulx.mul hsub1
    have hd_den : HasDerivAt (fun s : ℝ => 1 - s + x * s) (-1 + x) t :=
      hsub1.add hmulx
    have hq : HasDerivAt H
        (1 + ((x * (1 - t) + x * t * (-1)) * (1 - t + x * t) - x * t * (1 - t) * (-1 + x)) /
          (1 - t + x * t) ^ 2) t :=
      (hasDerivAt_id' t).add (hd_num.div hd_den hden)
    convert hq using 1
    field_simp [hden]
    ring
  have hint_comb : IntervalIntegrable
      (fun t => (x + 1) * ((1 - t) / (1 - t + x * t)) +
        -(x ^ 2 - x) * (t * (1 - t) / (1 - t + x * t) ^ 2)) MeasureTheory.volume 0 1 :=
    (hi1.const_mul _).add (hi2.const_mul _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hHderiv hint_comb]
  simp [H]

private lemma shearerF_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    shearerF x + shearerF' x * (y - x) ≤ shearerF y := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [shearerF_zero]
    unfold shearerF shearerF'
    have hc1 : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + x * t)) (Set.uIcc 0 1) := by
      refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hx ht)
      exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
    have hc2 : ContinuousOn (fun t : ℝ => (t * (1 - t)) / (1 - t + x * t) ^ 2) (Set.uIcc 0 1) := by
      refine ContinuousOn.div (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn ?_
        (fun t ht => pow_ne_zero 2 (denom_ne_zero hx ht))
      exact (((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).pow 2).continuousOn
    have hi1 : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 - t + x * t)) MeasureTheory.volume 0 1 :=
      hc1.intervalIntegrable
    have hi2 : IntervalIntegrable (fun t : ℝ => (t * (1 - t)) / (1 - t + x * t) ^ 2) MeasureTheory.volume 0 1 :=
      hc2.intervalIntegrable
    have hmul : - (∫ t in (0 : ℝ)..1, t * (1 - t) / (1 - t + x * t) ^ 2) * (0 - x) =
        ∫ t in (0 : ℝ)..1, x * (t * (1 - t) / (1 - t + x * t) ^ 2) := by
      rw [intervalIntegral.integral_const_mul]; ring
    rw [hmul, ← intervalIntegral.integral_add hi1 (hi2.const_mul x)]
    have hmono : ∫ t in (0 : ℝ)..1, ((1 - t) / (1 - t + x * t) + x * (t * (1 - t) / (1 - t + x * t) ^ 2)) ≤
        ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on zero_le_one (hi1.add (hi2.const_mul x))
        (intervalIntegrable_const (μ := MeasureTheory.volume)) fun t ht => ?_
      have hden : 0 < 1 - t + x * t := denom_pos hx ht.1 ht.2
      have hden2 : 0 < (1 - t + x * t) ^ 2 := sq_pos_of_pos hden
      have hnum : (1 - t) * (1 - t + x * t) + x * (t * (1 - t)) ≤ (1 - t + x * t) ^ 2 := by
        have : 0 ≤ (x * t) ^ 2 := sq_nonneg _
        nlinarith
      have heq : (1 - t) / (1 - t + x * t) + x * (t * (1 - t) / (1 - t + x * t) ^ 2) =
          ((1 - t) * (1 - t + x * t) + x * (t * (1 - t))) / (1 - t + x * t) ^ 2 := by
        field_simp [hden.ne']
      rw [heq, div_le_one hden2]
      exact hnum
    have h1eq : (∫ _t in (0 : ℝ)..1, (1 : ℝ)) = 1 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    linarith
  · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    unfold shearerF shearerF'
    have hc1 : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + x * t)) (Set.uIcc 0 1) := by
      refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hx ht)
      exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
    have hc2 : ContinuousOn (fun t : ℝ => (t * (1 - t)) / (1 - t + x * t) ^ 2) (Set.uIcc 0 1) := by
      refine ContinuousOn.div (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn ?_
        (fun t ht => pow_ne_zero 2 (denom_ne_zero hx ht))
      exact (((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).pow 2).continuousOn
    have hcy : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + y * t)) (Set.uIcc 0 1) := by
      refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hyp ht)
      exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
    have hi1 : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 - t + x * t)) MeasureTheory.volume 0 1 :=
      hc1.intervalIntegrable
    have hi2 : IntervalIntegrable (fun t : ℝ => (t * (1 - t)) / (1 - t + x * t) ^ 2) MeasureTheory.volume 0 1 :=
      hc2.intervalIntegrable
    have hiy : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 - t + y * t)) MeasureTheory.volume 0 1 :=
      hcy.intervalIntegrable
    have hmul : - (∫ t in (0 : ℝ)..1, t * (1 - t) / (1 - t + x * t) ^ 2) * (y - x) =
        ∫ t in (0 : ℝ)..1, (-(y - x)) * (t * (1 - t) / (1 - t + x * t) ^ 2) := by
      rw [intervalIntegral.integral_const_mul]; ring
    rw [hmul, ← intervalIntegral.integral_add hi1 (hi2.const_mul _)]
    refine intervalIntegral.integral_mono_on zero_le_one (hi1.add (hi2.const_mul _)) hiy fun t ht => ?_
    have hax : 0 < 1 - t + x * t := denom_pos hx ht.1 ht.2
    have hay : 0 < 1 - t + y * t := denom_pos hyp ht.1 ht.2
    have hsub : 0 ≤ (1 - t) / (1 - t + y * t) -
        ((1 - t) / (1 - t + x * t) + -(y - x) * (t * (1 - t) / (1 - t + x * t) ^ 2)) := by
      set ax : ℝ := 1 - t + x * t with hax_def
      set ay : ℝ := 1 - t + y * t with hay_def
      have hid : (1 - t) / ay - ((1 - t) / ax + -(y - x) * (t * (1 - t) / ax ^ 2)) =
          (1 - t) * ((y - x) * t) ^ 2 / (ax ^ 2 * ay) := by
        have hmul : ((1 - t) / ay - ((1 - t) / ax + -(y - x) * (t * (1 - t) / ax ^ 2))) * (ax ^ 2 * ay) =
            (1 - t) * ((y - x) * t) ^ 2 := by
          have h1 : (1 - t) / ay * (ax ^ 2 * ay) = (1 - t) * ax ^ 2 := by
            rw [div_mul_eq_mul_div, ← mul_assoc, mul_div_cancel_right₀ _ hay.ne']
          have h2 : (1 - t) / ax * (ax ^ 2 * ay) = (1 - t) * ax * ay := by
            rw [sq, div_mul_eq_mul_div]
            have : (1 - t) * (ax * ax * ay) / ax = (1 - t) * ax * ay := by
              have : (1 - t) * (ax * ax * ay) = ((1 - t) * ax * ay) * ax := by ring
              rw [this, mul_div_cancel_right₀ _ hax.ne']
            exact this
          have h3 : (-(y - x) * (t * (1 - t) / ax ^ 2)) * (ax ^ 2 * ay) = -(y - x) * t * (1 - t) * ay := by
            have : (-(y - x) * (t * (1 - t) / ax ^ 2)) * (ax ^ 2 * ay) =
                (-(y - x) * ay) * ((t * (1 - t)) / ax ^ 2 * ax ^ 2) := by ring
            rw [this, div_mul_cancel₀ _ (pow_ne_zero 2 hax.ne')]
            ring
          calc ((1 - t) / ay - ((1 - t) / ax + -(y - x) * (t * (1 - t) / ax ^ 2))) * (ax ^ 2 * ay)
              = (1 - t) / ay * (ax ^ 2 * ay) - (1 - t) / ax * (ax ^ 2 * ay) -
                  (-(y - x) * (t * (1 - t) / ax ^ 2)) * (ax ^ 2 * ay) := by ring
            _ = (1 - t) * ax ^ 2 - (1 - t) * ax * ay - (-(y - x) * t * (1 - t) * ay) := by rw [h1, h2, h3]
            _ = (1 - t) * ((y - x) * t) ^ 2 := by rw [hax_def, hay_def]; ring
        exact (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hax.ne') hay.ne')).mpr hmul
      rw [hid]
      apply div_nonneg
      · exact mul_nonneg (by linarith [ht.2]) (sq_nonneg _)
      · positivity
    linarith

private lemma shearerF_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    shearerF y ≤ shearerF x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  unfold shearerF
  have hcx : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + x * t)) (Set.uIcc 0 1) := by
    refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hx ht)
    exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
  have hcy : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + y * t)) (Set.uIcc 0 1) := by
    refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hy ht)
    exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
  refine intervalIntegral.integral_mono_on zero_le_one hcy.intervalIntegrable hcx.intervalIntegrable fun t ht => ?_
  have hax : 0 < 1 - t + x * t := denom_pos hx ht.1 ht.2
  have hle : 1 - t + x * t ≤ 1 - t + y * t := by nlinarith [ht.1]
  exact div_le_div_of_nonneg_left (by linarith [ht.2]) hax hle

private lemma shearerF_lower {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x - 1) / x ≤ shearerF x := by
  have hxp : 0 < x := by linarith
  unfold shearerF
  have hcx : ContinuousOn (fun t : ℝ => (1 - t) / (1 - t + x * t)) (Set.uIcc 0 1) := by
    refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht => denom_ne_zero hxp ht)
    exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
  have hcl : ContinuousOn (fun t : ℝ => 1 / (1 + x * t) - 1 / x) (Set.uIcc 0 1) := by
    refine ContinuousOn.sub ?_ continuousOn_const
    refine ContinuousOn.div continuousOn_const
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    nlinarith [ht.1]
  have hint_l : ∫ t in (0 : ℝ)..1, (1 / (1 + x * t) - 1 / x) = (Real.log (1 + x) - 1) / x := by
    let F : ℝ → ℝ := fun t => Real.log (1 + x * t) / x - t / x
    have hFderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (1 / (1 + x * t) - 1 / x) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hp : 0 < 1 + x * t := by nlinarith [ht.1]
      have h1 : HasDerivAt (fun s : ℝ => 1 + x * s) x t := by
        simpa using ((hasDerivAt_id' t).const_mul x).const_add (1 : ℝ)
      have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + x * s)) (x / (1 + x * t)) t :=
        h1.log hp.ne'
      have h3 : HasDerivAt (fun s : ℝ => Real.log (1 + x * s) / x) ((x / (1 + x * t)) / x) t :=
        h2.div_const x
      have h4 : HasDerivAt (fun s : ℝ => s / x) (1 / x) t := (hasDerivAt_id' t).div_const x
      have hsub : HasDerivAt F ((x / (1 + x * t)) / x - 1 / x) t := h3.sub h4
      convert hsub using 1
      field_simp [hxp.ne', hp.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv hcl.intervalIntegrable]
    simp only [F, mul_one, mul_zero, add_zero, Real.log_one, zero_div, sub_zero]
    ring
  have hmono : ∫ t in (0 : ℝ)..1, (1 / (1 + x * t) - 1 / x) ≤
      ∫ t in (0 : ℝ)..1, (1 - t) / (1 - t + x * t) := by
    refine intervalIntegral.integral_mono_on zero_le_one hcl.intervalIntegrable hcx.intervalIntegrable fun t ht => ?_
    have ha : 0 < 1 - t + x * t := denom_pos hxp ht.1 ht.2
    have hb : 0 < 1 + x * t := by nlinarith [ht.1]
    have h1 : 1 / (1 + x * t) - 1 / x ≤ (1 - t) / (1 + x * t) := by
      have hid : (1 - t) / (1 + x * t) - (1 / (1 + x * t) - 1 / x) = 1 / (x * (1 + x * t)) := by
        calc (1 - t) / (1 + x * t) - (1 / (1 + x * t) - 1 / x)
            = 1 / x - t / (1 + x * t) := by ring
          _ = (1 * (1 + x * t) - x * t) / (x * (1 + x * t)) := div_sub_div 1 t hxp.ne' hb.ne'
          _ = 1 / (x * (1 + x * t)) := by ring
      have hpos : 0 ≤ 1 / (x * (1 + x * t)) := by positivity
      linarith
    have h2 : (1 - t) / (1 + x * t) ≤ (1 - t) / (1 - t + x * t) :=
      div_le_div_of_nonneg_left (by linarith [ht.2]) ha (by linarith [ht.1])
    exact h1.trans h2
  have hlog : Real.log x ≤ Real.log (1 + x) := Real.log_le_log hxp (by linarith)
  have hdiv : (Real.log x - 1) / x ≤ (Real.log (1 + x) - 1) / x :=
    div_le_div_of_nonneg_right (by linarith) hxp.le
  linarith

/- ### Part 5: Shearer's triangle-free independent set theorem -/

private lemma dirEdges_remove_closed_nbhd {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (htf : ordTriangles R S = 0)
    {v : V} (hv : v ∈ S) :
    dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) +
      2 * ∑ w ∈ R.neighborFinset v ∩ S, degIn R S w = dirEdges R S := by
  let B : Finset V := insert v (R.neighborFinset v ∩ S)
  let Sv : Finset V := S \ B
  have hBsub : B ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hm
    · exact hv
    · exact (Finset.mem_inter.mp hm).2
  have hnot_adj_N : ∀ w₁ ∈ R.neighborFinset v ∩ S, ∀ w₂ ∈ R.neighborFinset v ∩ S, ¬ R.Adj w₁ w₂ := by
    intro w₁ hw₁ w₂ hw₂ hadj
    have hzero : (R.neighborFinset w₁ ∩ (R.neighborFinset v ∩ S)).card = 0 := by
      unfold ordTriangles at htf
      have h1 := Finset.sum_eq_zero_iff.mp htf v hv
      exact Finset.sum_eq_zero_iff.mp h1 w₁ hw₁
    have hmem : w₂ ∈ R.neighborFinset w₁ ∩ (R.neighborFinset v ∩ S) := by
      simp [SimpleGraph.mem_neighborFinset, hadj, hw₂]
    have hpos := Finset.card_pos.mpr ⟨w₂, hmem⟩
    omega
  have hSv_B : dirEdges R S = ∑ x ∈ Sv, degIn R Sv x +
      ∑ x ∈ Sv, (R.neighborFinset x ∩ B).card + ∑ x ∈ B, degIn R S x := by
    unfold dirEdges
    have hunion : B ∪ Sv = S := Finset.union_sdiff_of_subset hBsub
    have hdisj : Disjoint B Sv := Finset.disjoint_sdiff
    rw [← hunion, Finset.sum_union hdisj, add_comm (∑ x ∈ B, _)]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold degIn
    rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
      (hdisj.mono Finset.inter_subset_right Finset.inter_subset_right), add_comm]
  have hcross : ∑ x ∈ Sv, (R.neighborFinset x ∩ B).card =
      ∑ w ∈ R.neighborFinset v ∩ S, (R.neighborFinset w ∩ Sv).card := by
    have hL : ∑ x ∈ Sv, (R.neighborFinset x ∩ B).card =
        ∑ x ∈ Sv, ∑ y ∈ B, if R.Adj x y then 1 else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1; ext y; simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hL, Finset.sum_comm]
    have hv_not_N : v ∉ R.neighborFinset v ∩ S := by simp [SimpleGraph.mem_neighborFinset]
    rw [show B = insert v (R.neighborFinset v ∩ S) from rfl, Finset.sum_insert hv_not_N]
    have hv_zero : ∑ x ∈ Sv, (if R.Adj x v then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx' : x ∉ R.neighborFinset v ∩ S := fun hm =>
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hm)
      have hna : ¬ R.Adj x v := by
        intro hadj
        apply hx'
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hadj.symm, (Finset.mem_sdiff.mp hx).1⟩
      simp [hna]
    rw [hv_zero, zero_add]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1; ext x; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
  have hdeg_w : ∀ w ∈ R.neighborFinset v ∩ S,
      degIn R S w = 1 + (R.neighborFinset w ∩ Sv).card := by
    intro w hw
    unfold degIn
    have hunion : B ∪ Sv = S := Finset.union_sdiff_of_subset hBsub
    have hdisj : Disjoint B Sv := Finset.disjoint_sdiff
    rw [← hunion, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
      (hdisj.mono Finset.inter_subset_right Finset.inter_subset_right)]
    congr 1
    have hvw : R.Adj v w := (SimpleGraph.mem_neighborFinset R v w).mp (Finset.mem_inter.mp hw).1
    have hsingle : R.neighborFinset w ∩ B = {v} := by
      ext z
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton,
        B, Finset.mem_insert]
      constructor
      · rintro ⟨hwz, rfl | hzN⟩
        · rfl
        · have hzN' : z ∈ R.neighborFinset v ∩ S := by
            rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact hzN
          exact False.elim (hnot_adj_N w hw z hzN' hwz)
      · rintro rfl
        exact ⟨hvw.symm, Or.inl rfl⟩
    rw [hsingle, Finset.card_singleton]
  have hsumB : ∑ x ∈ B, degIn R S x = degIn R S v + ∑ w ∈ R.neighborFinset v ∩ S, degIn R S w := by
    have hv_not_N : v ∉ R.neighborFinset v ∩ S := by simp [SimpleGraph.mem_neighborFinset]
    exact Finset.sum_insert hv_not_N
  have hsum_w : ∑ w ∈ R.neighborFinset v ∩ S, degIn R S w =
      degIn R S v + ∑ w ∈ R.neighborFinset v ∩ S, (R.neighborFinset w ∩ Sv).card := by
    calc ∑ w ∈ R.neighborFinset v ∩ S, degIn R S w
        = ∑ w ∈ R.neighborFinset v ∩ S, (1 + (R.neighborFinset w ∩ Sv).card) :=
          Finset.sum_congr rfl hdeg_w
      _ = (R.neighborFinset v ∩ S).card + ∑ w ∈ R.neighborFinset v ∩ S, (R.neighborFinset w ∩ Sv).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = degIn R S v + ∑ w ∈ R.neighborFinset v ∩ S, (R.neighborFinset w ∩ Sv).card := rfl
  change dirEdges R Sv + 2 * ∑ w ∈ R.neighborFinset v ∩ S, degIn R S w = dirEdges R S
  unfold dirEdges at hSv_B ⊢
  omega

private lemma shearer_sum_identities {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (htf : ordTriangles R S = 0)
    (hS : S.Nonempty) (d : ℝ) (hd : d = (dirEdges R S : ℝ) / (S.card : ℝ)) :
    (∑ v ∈ S, (degIn R S v : ℝ) = (S.card : ℝ) * d) ∧
    (∑ v ∈ S, (dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) =
      (S.card : ℝ) ^ 2 * d - 2 * ∑ w ∈ S, (degIn R S w : ℝ) ^ 2) ∧
    ((S.card : ℝ) * d ^ 2 ≤ ∑ w ∈ S, (degIn R S w : ℝ) ^ 2) := by
  have hm_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hsum_deg : ∑ v ∈ S, (degIn R S v : ℝ) = (S.card : ℝ) * d := by
    have h1 : (∑ v ∈ S, (degIn R S v : ℝ)) = (dirEdges R S : ℝ) := by
      unfold dirEdges; push_cast; rfl
    rw [h1, hd]
    field_simp [hm_pos.ne']
  have hsum_rem : ∑ v ∈ S, (dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) =
      (S.card : ℝ) ^ 2 * d - 2 * ∑ w ∈ S, (degIn R S w : ℝ) ^ 2 := by
    have h1 : ∀ v ∈ S, (dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) =
        (dirEdges R S : ℝ) - 2 * ∑ w ∈ R.neighborFinset v ∩ S, (degIn R S w : ℝ) := by
      intro v hv
      have hnat := dirEdges_remove_closed_nbhd R S htf hv
      have hR : (dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) +
          2 * ∑ w ∈ R.neighborFinset v ∩ S, (degIn R S w : ℝ) = (dirEdges R S : ℝ) := by
        exact_mod_cast hnat
      linarith
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    have hdbl : ∑ v ∈ S, ∑ w ∈ R.neighborFinset v ∩ S, (degIn R S w : ℝ) =
        ∑ w ∈ S, (degIn R S w : ℝ) ^ 2 := by
      have hL : ∑ v ∈ S, ∑ w ∈ R.neighborFinset v ∩ S, (degIn R S w : ℝ) =
          ∑ v ∈ S, ∑ w ∈ S, if R.Adj v w then (degIn R S w : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_filter]
        congr 1; ext w; simp [SimpleGraph.mem_neighborFinset, and_comm]
      rw [hL, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, sq]
      congr 1
      have hcnt : (S.filter (fun v => R.Adj v w)).card = degIn R S w := by
        unfold degIn
        congr 1; ext v; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
      exact_mod_cast hcnt
    rw [hdbl]
    have hE_eq : (dirEdges R S : ℝ) = (S.card : ℝ) * d := by
      rw [hd]; field_simp [hm_pos.ne']
    rw [hE_eq]; ring
  have hcs_deg : (S.card : ℝ) * d ^ 2 ≤ ∑ w ∈ S, (degIn R S w : ℝ) ^ 2 := by
    have h0 : 0 ≤ ∑ w ∈ S, ((degIn R S w : ℝ) - d) ^ 2 :=
      Finset.sum_nonneg fun w _ => sq_nonneg _
    have hexp : ∑ w ∈ S, ((degIn R S w : ℝ) - d) ^ 2 =
        (∑ w ∈ S, (degIn R S w : ℝ) ^ 2) - 2 * d * (∑ w ∈ S, (degIn R S w : ℝ)) +
        (S.card : ℝ) * d ^ 2 := by
      have h1 : ∀ w ∈ S, ((degIn R S w : ℝ) - d) ^ 2 =
          (degIn R S w : ℝ) ^ 2 - 2 * d * (degIn R S w : ℝ) + d ^ 2 := fun _ _ => by ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hexp, hsum_deg] at h0
    linarith
  exact ⟨hsum_deg, hsum_rem, hcs_deg⟩

private lemma ordTriangles_subset_zero {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] {S' S : Finset V}
    (hsub : S' ⊆ S) (htf : ordTriangles R S = 0) : ordTriangles R S' = 0 := by
  unfold ordTriangles at htf ⊢
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
  have hxS : x ∈ S := hsub hx
  have hyS : y ∈ R.neighborFinset x ∩ S := Finset.inter_subset_inter_left hsub hy
  have h0 : (R.neighborFinset y ∩ (R.neighborFinset x ∩ S)).card = 0 :=
    Finset.sum_eq_zero_iff.mp (Finset.sum_eq_zero_iff.mp htf x hxS) y hyS
  have hle : (R.neighborFinset y ∩ (R.neighborFinset x ∩ S')).card ≤
      (R.neighborFinset y ∩ (R.neighborFinset x ∩ S)).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left (Finset.inter_subset_inter_left hsub))
  omega

private lemma shearer_step_bound {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (htf : ordTriangles R S = 0)
    (d : ℝ) (hd_pos : 0 < d) (Imax : Finset V)
    (hImax_max : ∀ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) → I.card ≤ Imax.card)
    (ih : ∀ S' : Finset V, S'.card < S.card → ordTriangles R S' = 0 →
      ∃ I ⊆ S', (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) ∧
        (S'.card : ℝ) * shearerF ((dirEdges R S' : ℝ) / (S'.card : ℝ)) ≤ (I.card : ℝ))
    {v : V} (hv : v ∈ S) :
    1 + ((S.card : ℝ) - 1 - (degIn R S v : ℝ)) * shearerF d +
      shearerF' d * ((dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) -
        d * ((S.card : ℝ) - 1 - (degIn R S v : ℝ))) ≤ (Imax.card : ℝ) := by
  let B : Finset V := insert v (R.neighborFinset v ∩ S)
  let Sv : Finset V := S \ B
  have hBsub : B ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hm
    · exact hv
    · exact (Finset.mem_inter.mp hm).2
  have hv_not_N : v ∉ R.neighborFinset v ∩ S := by simp [SimpleGraph.mem_neighborFinset]
  have hBcard : B.card = degIn R S v + 1 := by
    simp [B, degIn, Finset.card_insert_of_notMem hv_not_N]
  have hSv_sub : Sv ⊆ S := Finset.sdiff_subset
  have hSv_card_nat : Sv.card + B.card = S.card := by
    rw [Finset.card_sdiff_of_subset hBsub]
    have := Finset.card_le_card hBsub
    omega
  have hSv_card : (Sv.card : ℝ) = (S.card : ℝ) - 1 - (degIn R S v : ℝ) := by
    have h1 : (Sv.card : ℝ) + ((degIn R S v : ℝ) + 1) = (S.card : ℝ) := by
      exact_mod_cast (hBcard ▸ hSv_card_nat)
    linarith
  have hSv_lt : Sv.card < S.card := by omega
  have hSv_tf : ordTriangles R Sv = 0 := ordTriangles_subset_zero R hSv_sub htf
  obtain ⟨Iv, hIv_sub, hIv_ind, hIv_bound⟩ := ih Sv hSv_lt hSv_tf
  have hv_not_Iv : v ∉ Iv := by
    intro hm
    have := hIv_sub hm
    simp [Sv, B] at this
  have halpha : (Iv.card : ℝ) + 1 ≤ (Imax.card : ℝ) := by
    have hsub : insert v Iv ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxI
      · exact hv
      · exact hSv_sub (hIv_sub hxI)
    have hind : ∀ x ∈ insert v Iv, ∀ y ∈ insert v Iv, ¬ R.Adj x y := by
      intro x hx y hy hadj
      rcases Finset.mem_insert.mp hx with rfl | hxI <;>
      rcases Finset.mem_insert.mp hy with rfl | hyI
      · exact hadj.ne rfl
      · have hyS := hIv_sub hyI
        simp only [Sv, B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
          SimpleGraph.mem_neighborFinset] at hyS
        exact hyS.2 (Or.inr ⟨hadj, hyS.1⟩)
      · have hxS := hIv_sub hxI
        simp only [Sv, B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
          SimpleGraph.mem_neighborFinset] at hxS
        exact hxS.2 (Or.inr ⟨hadj.symm, hxS.1⟩)
      · exact hIv_ind x hxI y hyI hadj
    have hle := hImax_max (insert v Iv) hsub hind
    rw [Finset.card_insert_of_notMem hv_not_Iv] at hle
    exact_mod_cast hle
  by_cases hSv0 : Sv.card = 0
  · have hSv_empty : Sv = ∅ := Finset.card_eq_zero.mp hSv0
    have hSvE : dirEdges R Sv = 0 := by simp [hSv_empty, dirEdges]
    have hSv0R : (S.card : ℝ) - 1 - (degIn R S v : ℝ) = 0 := by rw [← hSv_card, hSv0]; simp
    change 1 + ((S.card : ℝ) - 1 - (degIn R S v : ℝ)) * shearerF d +
      shearerF' d * ((dirEdges R Sv : ℝ) - d * ((S.card : ℝ) - 1 - (degIn R S v : ℝ))) ≤ (Imax.card : ℝ)
    rw [hSv0R, hSvE, Nat.cast_zero]
    linarith [Nat.cast_nonneg (α := ℝ) Iv.card]
  · have hSv_pos : (0 : ℝ) < (Sv.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hSv0)
    have htang := shearerF_tangent hd_pos
      (div_nonneg (Nat.cast_nonneg (dirEdges R Sv)) hSv_pos.le)
    have hmul := mul_le_mul_of_nonneg_left htang hSv_pos.le
    have heq : (Sv.card : ℝ) * (shearerF d + shearerF' d * ((dirEdges R Sv : ℝ) / (Sv.card : ℝ) - d)) =
        (Sv.card : ℝ) * shearerF d + shearerF' d * ((dirEdges R Sv : ℝ) - d * (Sv.card : ℝ)) := by
      field_simp [hSv_pos.ne']
    rw [heq, hSv_card] at hmul
    rw [hSv_card] at hIv_bound
    change 1 + ((S.card : ℝ) - 1 - (degIn R S v : ℝ)) * shearerF d +
      shearerF' d * ((dirEdges R Sv : ℝ) - d * ((S.card : ℝ) - 1 - (degIn R S v : ℝ))) ≤ (Imax.card : ℝ)
    linarith

private lemma shearer_triangle_free {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] :
    ∀ S : Finset V, ordTriangles R S = 0 →
      ∃ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) ∧
        (S.card : ℝ) * shearerF ((dirEdges R S : ℝ) / (S.card : ℝ)) ≤ (I.card : ℝ) := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    intro htf
    by_cases hS : S.Nonempty
    · by_cases hE : dirEdges R S = 0
      · refine ⟨S, Subset.rfl, ?_, ?_⟩
        · intro x hx y hy hadj
          unfold dirEdges degIn at hE
          have hx0 := Finset.sum_eq_zero_iff.mp hE x hx
          have hmem : y ∈ R.neighborFinset x ∩ S := by simp [SimpleGraph.mem_neighborFinset, hadj, hy]
          have := Finset.card_pos.mpr ⟨y, hmem⟩
          omega
        · rw [← hcard, hE, Nat.cast_zero, zero_div, shearerF_zero, mul_one]
      · have hm_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
        have hE_pos : (0 : ℝ) < (dirEdges R S : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hE)
        let d : ℝ := (dirEdges R S : ℝ) / (S.card : ℝ)
        have hd_pos : 0 < d := div_pos hE_pos hm_pos
        let indSets : Finset (Finset V) :=
          S.powerset.filter (fun I => ∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y)
        have hind_ne : indSets.Nonempty := ⟨∅, by simp [indSets]⟩
        obtain ⟨Imax, hImax_mem, hImax_max⟩ := Finset.exists_max_image indSets Finset.card hind_ne
        have hImax_sub : Imax ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hImax_mem).1
        have hImax_ind : ∀ x ∈ Imax, ∀ y ∈ Imax, ¬ R.Adj x y := (Finset.mem_filter.mp hImax_mem).2
        refine ⟨Imax, hImax_sub, hImax_ind, ?_⟩
        rw [← hcard]
        have hstep : ∀ v ∈ S,
            1 + ((S.card : ℝ) - 1 - (degIn R S v : ℝ)) * shearerF d +
              shearerF' d * ((dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) -
                d * ((S.card : ℝ) - 1 - (degIn R S v : ℝ))) ≤ (Imax.card : ℝ) := by
          intro v hv
          refine shearer_step_bound R S htf d hd_pos Imax ?_ ?_ hv
          · intro I hsub hind
            exact hImax_max I (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hind⟩)
          · intro S' hlt htf'
            exact ih S'.card (hcard ▸ hlt) S' rfl htf'
        have hsum_le : ∑ v ∈ S, (1 + ((S.card : ℝ) - 1 - (degIn R S v : ℝ)) * shearerF d +
            shearerF' d * ((dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) -
              d * ((S.card : ℝ) - 1 - (degIn R S v : ℝ)))) ≤ (S.card : ℝ) * (Imax.card : ℝ) := by
          calc _ ≤ ∑ _v ∈ S, (Imax.card : ℝ) := Finset.sum_le_sum hstep
            _ = (S.card : ℝ) * (Imax.card : ℝ) := by simp
        obtain ⟨hsum_deg, hsum_rem, hcs_deg⟩ := shearer_sum_identities R S htf hS d rfl
        have hsum_eval : ∑ v ∈ S, (1 + ((S.card : ℝ) - 1 - (degIn R S v : ℝ)) * shearerF d +
            shearerF' d * ((dirEdges R (S \ insert v (R.neighborFinset v ∩ S)) : ℝ) -
              d * ((S.card : ℝ) - 1 - (degIn R S v : ℝ)))) =
            (S.card : ℝ) + ((S.card : ℝ) * ((S.card : ℝ) - 1) - (S.card : ℝ) * d) * shearerF d +
              shearerF' d * (((S.card : ℝ) ^ 2 * d - 2 * ∑ w ∈ S, (degIn R S w : ℝ) ^ 2) -
                d * ((S.card : ℝ) * ((S.card : ℝ) - 1) - (S.card : ℝ) * d)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
            ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum_deg, hsum_rem]
        rw [hsum_eval] at hsum_le
        have hfp : shearerF' d ≤ 0 := shearerF'_nonpos hd_pos
        have hode : (d + 1) * shearerF d + (d ^ 2 - d) * shearerF' d = 1 := shearerF_ode hd_pos
        have hfinal : (S.card : ℝ) ^ 2 * shearerF d ≤ (S.card : ℝ) * (Imax.card : ℝ) := by
          have h1 : shearerF' d * ((S.card : ℝ) * (d - d ^ 2)) ≤
              shearerF' d * (((S.card : ℝ) ^ 2 * d - 2 * ∑ w ∈ S, (degIn R S w : ℝ) ^ 2) -
                d * ((S.card : ℝ) * ((S.card : ℝ) - 1) - (S.card : ℝ) * d)) := by
            have hdiff : ((S.card : ℝ) ^ 2 * d - 2 * ∑ w ∈ S, (degIn R S w : ℝ) ^ 2) -
                d * ((S.card : ℝ) * ((S.card : ℝ) - 1) - (S.card : ℝ) * d) ≤
                (S.card : ℝ) * (d - d ^ 2) := by linarith
            exact mul_le_mul_of_nonpos_left hdiff hfp
          have h2 : (S.card : ℝ) ^ 2 * shearerF d =
              (S.card : ℝ) + ((S.card : ℝ) * ((S.card : ℝ) - 1) - (S.card : ℝ) * d) * shearerF d +
                shearerF' d * ((S.card : ℝ) * (d - d ^ 2)) := by
            linear_combination (S.card : ℝ) * hode
          linarith
        have hfinal2 : ((S.card : ℝ) * shearerF d) * (S.card : ℝ) ≤ (Imax.card : ℝ) * (S.card : ℝ) := by
          linarith
        exact le_of_mul_le_mul_right hfinal2 hm_pos
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      refine ⟨∅, Subset.rfl, by simp, ?_⟩
      rw [← hcard]; simp

/- ### Part 6: Deterministic alteration (sampling mod t + deleting 1 vertex per triangle) -/

private lemma exists_pos_of_sum_nat_pos {α : Type*} {s : Finset α} {f : α → ℕ}
    (h : 0 < ∑ x ∈ s, f x) : ∃ x ∈ s, 0 < f x := by
  by_contra hc
  push Not at hc
  have hz : ∑ x ∈ s, f x = 0 := Finset.sum_eq_zero fun x hx => Nat.eq_zero_of_le_zero (hc x hx)
  omega

private lemma remove_triangles {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] :
    ∀ S : Finset V, ∃ S' ⊆ S, ordTriangles R S' = 0 ∧
      6 * S.card ≤ 6 * S'.card + ordTriangles R S := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases htf : ordTriangles R S = 0
    · exact ⟨S, Subset.rfl, htf, by rw [← hcard]; omega⟩
    · have hpos : 0 < ordTriangles R S := Nat.pos_of_ne_zero htf
      unfold ordTriangles at hpos
      obtain ⟨a, haS, ha_pos⟩ := exists_pos_of_sum_nat_pos hpos
      obtain ⟨b, hb_mem, hb_pos⟩ := exists_pos_of_sum_nat_pos ha_pos
      obtain ⟨c, hc_mem⟩ := Finset.card_pos.mp hb_pos
      have hbS : b ∈ S := (Finset.mem_inter.mp hb_mem).2
      have hab : R.Adj a b := (SimpleGraph.mem_neighborFinset R a b).mp (Finset.mem_inter.mp hb_mem).1
      have hcS : c ∈ S := (Finset.mem_inter.mp (Finset.mem_inter.mp hc_mem).2).2
      have hac : R.Adj a c := (SimpleGraph.mem_neighborFinset R a c).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp hc_mem).2).1
      have hbc : R.Adj b c := (SimpleGraph.mem_neighborFinset R b c).mp (Finset.mem_inter.mp hc_mem).1
      let S1 := S.erase a
      have hdrop : ordTriangles R S1 + 6 ≤ ordTriangles R S := by
        have htri_eq : ∀ T : Finset V, ordTriangles R T =
            (((T ×ˢ T) ×ˢ T).filter (fun p => R.Adj p.1.1 p.1.2 ∧ R.Adj p.1.1 p.2 ∧ R.Adj p.1.2 p.2)).card := by
          intro T
          unfold ordTriangles
          rw [Finset.card_filter]
          simp only [Finset.sum_product]
          refine Finset.sum_congr rfl fun x _ => ?_
          have h1 : ∑ y ∈ R.neighborFinset x ∩ T,
              (R.neighborFinset y ∩ (R.neighborFinset x ∩ T)).card =
              ∑ y ∈ T, if R.Adj x y then (R.neighborFinset y ∩ (R.neighborFinset x ∩ T)).card else 0 := by
            rw [← Finset.sum_filter]
            congr 1; ext y; simp [SimpleGraph.mem_neighborFinset, and_comm]
          rw [h1]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases hxy : R.Adj x y
          · rw [if_pos hxy]
            have h2 : ∑ z ∈ T, (if R.Adj x y ∧ R.Adj x z ∧ R.Adj y z then 1 else 0) =
                (T.filter (fun z => R.Adj x z ∧ R.Adj y z)).card := by
              rw [Finset.card_filter]
              refine Finset.sum_congr rfl fun z _ => by simp [hxy]
            rw [h2]
            congr 1; ext z; simp [SimpleGraph.mem_neighborFinset]; tauto
          · rw [if_neg hxy]
            symm
            exact Finset.sum_eq_zero fun z _ => by simp [hxy]
        rw [htri_eq S1, htri_eq S]
        let P := ((S ×ˢ S) ×ˢ S).filter (fun p => R.Adj p.1.1 p.1.2 ∧ R.Adj p.1.1 p.2 ∧ R.Adj p.1.2 p.2)
        let P1 := ((S1 ×ˢ S1) ×ˢ S1).filter (fun p => R.Adj p.1.1 p.1.2 ∧ R.Adj p.1.1 p.2 ∧ R.Adj p.1.2 p.2)
        let six : Finset ((V × V) × V) :=
          {((a, b), c), ((a, c), b), ((b, a), c), ((b, c), a), ((c, a), b), ((c, b), a)}
        have hne_ab : a ≠ b := hab.ne
        have hne_ac : a ≠ c := hac.ne
        have hne_bc : b ≠ c := hbc.ne
        have hsix_card : six.card = 6 := by
          simp [six, hne_ab, hne_ab.symm, hne_ac, hne_ac.symm, hne_bc, hne_bc.symm]
        have hP1_sub : P1 ⊆ P := Finset.filter_subset_filter _
          (Finset.product_subset_product
            (Finset.product_subset_product (Finset.erase_subset a S) (Finset.erase_subset a S))
            (Finset.erase_subset a S))
        have hsix_sub : six ⊆ P := by
          intro p hp
          simp only [six, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [P, haS, hbS, hcS, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
        have hdisj : Disjoint P1 six := by
          rw [Finset.disjoint_left]
          intro p hp1 hps
          have hp1' := (Finset.mem_filter.mp hp1).1
          simp only [Finset.mem_product, S1, Finset.mem_erase] at hp1'
          simp only [six, Finset.mem_insert, Finset.mem_singleton] at hps
          rcases hps with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hp1'.1.1.1 rfl
          · exact hp1'.1.1.1 rfl
          · exact hp1'.1.2.1 rfl
          · exact hp1'.2.1 rfl
          · exact hp1'.1.2.1 rfl
          · exact hp1'.2.1 rfl
        have hle := Finset.card_le_card (Finset.union_subset hP1_sub hsix_sub)
        rw [Finset.card_union_of_disjoint hdisj, hsix_card] at hle
        exact hle
      have hlt : S1.card < m := by
        rw [Finset.card_erase_of_mem haS, hcard]
        have := Finset.card_pos.mpr ⟨a, haS⟩
        omega
      obtain ⟨S', hS'sub, hS'tf, hS'bound⟩ := ih S1.card hlt S1 rfl
      refine ⟨S', hS'sub.trans (Finset.erase_subset a S), hS'tf, ?_⟩
      have hcs : S.card = S1.card + 1 := (Finset.card_erase_add_one haS).symm
      rw [← hcard]
      omega

private lemma exists_good_sample {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (t : ℕ) (ht : 1 ≤ t) (c : ℝ) :
    ∃ S : Finset V,
      ((Fintype.card V : ℝ) / (t : ℝ)) -
        ((ordTriangles R Finset.univ : ℝ) / (6 * (t : ℝ) ^ 3)) -
        c * ((dirEdges R Finset.univ : ℝ) / (t : ℝ) ^ 2) ≤
      (S.card : ℝ) - ((ordTriangles R S : ℝ) / 6) - c * (dirEdges R S : ℝ) := by
  classical
  have : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  let z0 : Fin t := ⟨0, by omega⟩
  let S_of (χ : V → Fin t) : Finset V := Finset.univ.filter (fun v => χ v = z0)
  let total : ℝ := (Fintype.card (V → Fin t) : ℝ)
  have htot_eq : total = (t : ℝ) ^ Fintype.card V := by
    simp [total, Fintype.card_fin]
  have htp : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcount_sub : ∀ A : Finset V,
      ((Finset.univ.filter (fun χ : V → Fin t => ∀ v ∈ A, χ v = z0)).card : ℝ) * (t : ℝ) ^ A.card =
        total := by
    intro A
    let e : {χ : V → Fin t // ∀ v ∈ A, χ v = z0} ≃ ({v : V // v ∉ A} → Fin t) :=
      { toFun := fun χ v => χ.1 v.1
        invFun := fun g => ⟨fun v => if h : v ∈ A then z0 else g ⟨v, h⟩, fun v hv => dif_pos hv⟩
        left_inv := fun χ => by
          ext v
          by_cases hv : v ∈ A
          · simp [hv, χ.2 v hv]
          · simp [hv]
        right_inv := fun g => by
          ext ⟨v, hv⟩
          simp [hv] }
    have hcard : (Finset.univ.filter (fun χ : V → Fin t => ∀ v ∈ A, χ v = z0)).card =
        t ^ (Fintype.card V - A.card) := by
      rw [← Fintype.card_subtype]
      rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_subtype_compl, Fintype.card_coe]
    rw [hcard, htot_eq]
    have hAle : A.card ≤ Fintype.card V := Finset.card_le_univ A
    push_cast
    rw [← pow_add, Nat.sub_add_cancel hAle]
  have hsum_V : ∑ χ : V → Fin t, ((S_of χ).card : ℝ) = total * ((Fintype.card V : ℝ) / (t : ℝ)) := by
    have h1 : ∑ χ : V → Fin t, ((S_of χ).card : ℝ) =
        ∑ v : V, ((Finset.univ.filter (fun χ : V → Fin t => ∀ x ∈ ({v} : Finset V), χ x = z0)).card : ℝ) := by
      have : ∀ χ : V → Fin t, ((S_of χ).card : ℝ) = ∑ v : V, if χ v = z0 then (1 : ℝ) else 0 := by
        intro χ; simp [S_of, Finset.sum_boole]
      simp_rw [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => by simp [Finset.sum_boole]
    rw [h1]
    have hterm : ∀ v : V, ((Finset.univ.filter (fun χ : V → Fin t => ∀ x ∈ ({v} : Finset V), χ x = z0)).card : ℝ) =
        total / (t : ℝ) := by
      intro v
      have hc := hcount_sub {v}
      simp only [Finset.card_singleton, pow_one] at hc
      exact (eq_div_iff htp.ne').mpr hc
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hsum_E : ∑ χ : V → Fin t, (dirEdges R (S_of χ) : ℝ) =
      total * ((dirEdges R Finset.univ : ℝ) / (t : ℝ) ^ 2) := by
    have hrew' : ∀ χ : V → Fin t, (dirEdges R (S_of χ) : ℝ) =
        ∑ u : V, ∑ v : V, if R.Adj u v then
          (if ∀ x ∈ ({u, v} : Finset V), χ x = z0 then (1 : ℝ) else 0) else 0 := by
      intro χ
      unfold dirEdges degIn
      push_cast
      have h1 : ∑ u ∈ S_of χ, ((R.neighborFinset u ∩ S_of χ).card : ℝ) =
          ∑ u : V, if u ∈ S_of χ then ((R.neighborFinset u ∩ S_of χ).card : ℝ) else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h1]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u ∈ S_of χ
      · rw [if_pos hu]
        have hu0 : χ u = z0 := (Finset.mem_filter.mp hu).2
        have h2 : ((R.neighborFinset u ∩ S_of χ).card : ℝ) =
            ∑ v : V, if R.Adj u v ∧ v ∈ S_of χ then (1 : ℝ) else 0 := by
          rw [Finset.sum_boole]
          congr 2; ext v; simp [SimpleGraph.mem_neighborFinset]
        rw [h2]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases huv : R.Adj u v
        · simp [huv, hu0, S_of]
        · simp [huv]
      · rw [if_neg hu]
        have hu0 : χ u ≠ z0 := fun h => hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
        symm
        refine Finset.sum_eq_zero fun v _ => ?_
        by_cases huv : R.Adj u v
        · simp [huv, hu0]
        · simp [huv]
    simp_rw [hrew']
    rw [Finset.sum_comm]
    have hswap : ∑ u : V, ∑ χ : V → Fin t, ∑ v : V,
        (if R.Adj u v then (if ∀ x ∈ ({u, v} : Finset V), χ x = z0 then (1 : ℝ) else 0) else 0) =
        ∑ u : V, ∑ v : V, if R.Adj u v then total / (t : ℝ) ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases huv : R.Adj u v
      · simp only [if_pos huv, Finset.sum_boole]
        have hc := hcount_sub {u, v}
        rw [Finset.card_pair huv.ne] at hc
        exact (eq_div_iff (pow_ne_zero 2 htp.ne')).mpr hc
      · simp [huv]
    rw [hswap]
    have hE_cnt : ∑ u : V, ∑ v : V, (if R.Adj u v then (1 : ℝ) else 0) = (dirEdges R Finset.univ : ℝ) := by
      unfold dirEdges degIn
      push_cast
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_boole]
      congr 2; ext v; simp [SimpleGraph.mem_neighborFinset]
    have hfact : ∑ u : V, ∑ v : V, (if R.Adj u v then total / (t : ℝ) ^ 2 else 0) =
        (total / (t : ℝ) ^ 2) * ∑ u : V, ∑ v : V, (if R.Adj u v then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by split <;> ring
    rw [hfact, hE_cnt]
    ring
  have hsum_T : ∑ χ : V → Fin t, (ordTriangles R (S_of χ) : ℝ) =
      total * ((ordTriangles R Finset.univ : ℝ) / (t : ℝ) ^ 3) := by
    have hrew' : ∀ χ : V → Fin t, (ordTriangles R (S_of χ) : ℝ) =
        ∑ u : V, ∑ v : V, ∑ w : V,
          if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then
            (if ∀ x ∈ ({u, v, w} : Finset V), χ x = z0 then (1 : ℝ) else 0) else 0 := by
      intro χ
      unfold ordTriangles
      push_cast
      have h1 : ∑ u ∈ S_of χ, ∑ v ∈ R.neighborFinset u ∩ S_of χ,
            ((R.neighborFinset v ∩ (R.neighborFinset u ∩ S_of χ)).card : ℝ) =
          ∑ u : V, if u ∈ S_of χ then ∑ v ∈ R.neighborFinset u ∩ S_of χ,
            ((R.neighborFinset v ∩ (R.neighborFinset u ∩ S_of χ)).card : ℝ) else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h1]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u ∈ S_of χ
      · rw [if_pos hu]
        have hu0 : χ u = z0 := (Finset.mem_filter.mp hu).2
        have h2 : ∑ v ∈ R.neighborFinset u ∩ S_of χ,
              ((R.neighborFinset v ∩ (R.neighborFinset u ∩ S_of χ)).card : ℝ) =
            ∑ v : V, if R.Adj u v ∧ v ∈ S_of χ then
              ((R.neighborFinset v ∩ (R.neighborFinset u ∩ S_of χ)).card : ℝ) else 0 := by
          rw [← Finset.sum_filter]
          congr 1; ext v; simp [SimpleGraph.mem_neighborFinset]
        rw [h2]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : R.Adj u v ∧ v ∈ S_of χ
        · rw [if_pos hv]
          have hv0 : χ v = z0 := (Finset.mem_filter.mp hv.2).2
          have h3 : ((R.neighborFinset v ∩ (R.neighborFinset u ∩ S_of χ)).card : ℝ) =
              ∑ w : V, if R.Adj v w ∧ R.Adj u w ∧ w ∈ S_of χ then (1 : ℝ) else 0 := by
            rw [Finset.sum_boole]
            congr 2; ext w; simp [SimpleGraph.mem_neighborFinset]
          rw [h3]
          refine Finset.sum_congr rfl fun w _ => ?_
          by_cases hw : R.Adj u w ∧ R.Adj v w
          · simp [hv.1, hw.1, hw.2, hu0, hv0, S_of]
          · have hnot1 : ¬ (R.Adj u v ∧ R.Adj u w ∧ R.Adj v w) := fun h => hw ⟨h.2.1, h.2.2⟩
            have hnot2 : ¬ (R.Adj v w ∧ R.Adj u w ∧ w ∈ S_of χ) := fun h => hw ⟨h.2.1, h.1⟩
            rw [if_neg hnot2, if_neg hnot1]
        · rw [if_neg hv]
          symm
          refine Finset.sum_eq_zero fun w _ => ?_
          by_cases huv : R.Adj u v
          · have hv0 : χ v ≠ z0 := fun h => hv ⟨huv, Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩⟩
            by_cases hrest : R.Adj u w ∧ R.Adj v w
            · simp [huv, hrest.1, hrest.2, hv0]
            · simp [huv, hrest]
          · simp [huv]
      · rw [if_neg hu]
        have hu0 : χ u ≠ z0 := fun h => hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
        symm
        refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun w _ => ?_
        by_cases htri : R.Adj u v ∧ R.Adj u w ∧ R.Adj v w
        · simp [htri.1, htri.2.1, htri.2.2, hu0]
        · simp [htri]
    simp_rw [hrew']
    rw [Finset.sum_comm]
    have hswap : ∑ u : V, ∑ χ : V → Fin t, ∑ v : V, ∑ w : V,
        (if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then
          (if ∀ x ∈ ({u, v, w} : Finset V), χ x = z0 then (1 : ℝ) else 0) else 0) =
        ∑ u : V, ∑ v : V, ∑ w : V, if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then total / (t : ℝ) ^ 3 else 0 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases htri : R.Adj u v ∧ R.Adj u w ∧ R.Adj v w
      · simp only [if_pos htri, Finset.sum_boole]
        have hc := hcount_sub {u, v, w}
        have h3 : ({u, v, w} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair htri.2.2.ne]
          simp [htri.1.ne, htri.2.1.ne]
        rw [h3] at hc
        exact (eq_div_iff (pow_ne_zero 3 htp.ne')).mpr hc
      · simp [htri]
    rw [hswap]
    have hT_cnt : ∑ u : V, ∑ v : V, ∑ w : V,
        (if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then (1 : ℝ) else 0) = (ordTriangles R Finset.univ : ℝ) := by
      unfold ordTriangles
      push_cast
      refine Finset.sum_congr rfl fun u _ => ?_
      have h1 : ∑ v ∈ R.neighborFinset u ∩ Finset.univ,
            ((R.neighborFinset v ∩ (R.neighborFinset u ∩ Finset.univ)).card : ℝ) =
          ∑ v : V, if R.Adj u v then ((R.neighborFinset v ∩ (R.neighborFinset u ∩ Finset.univ)).card : ℝ) else 0 := by
        rw [← Finset.sum_filter]
        congr 1; ext v; simp [SimpleGraph.mem_neighborFinset]
      rw [h1]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases huv : R.Adj u v
      · rw [if_pos huv]
        have h2 : ∑ w : V, (if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then (1 : ℝ) else 0) =
            ((Finset.univ.filter (fun w : V => R.Adj u w ∧ R.Adj v w)).card : ℝ) := by
          rw [Finset.sum_boole]; congr 2; ext w; simp [huv]
        rw [h2]
        congr 2; ext w; simp [SimpleGraph.mem_neighborFinset]; tauto
      · rw [if_neg huv]
        exact Finset.sum_eq_zero fun w _ => by simp [huv]
    have hfact : ∑ u : V, ∑ v : V, ∑ w : V,
        (if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then total / (t : ℝ) ^ 3 else 0) =
        (total / (t : ℝ) ^ 3) * ∑ u : V, ∑ v : V, ∑ w : V,
          (if R.Adj u v ∧ R.Adj u w ∧ R.Adj v w then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun w _ => by split <;> ring
    rw [hfact, hT_cnt]
    ring
  let F : (V → Fin t) → ℝ := fun χ =>
    ((S_of χ).card : ℝ) - ((ordTriangles R (S_of χ) : ℝ) / 6) - c * (dirEdges R (S_of χ) : ℝ)
  let avg : ℝ := ((Fintype.card V : ℝ) / (t : ℝ)) -
    ((ordTriangles R Finset.univ : ℝ) / (6 * (t : ℝ) ^ 3)) -
    c * ((dirEdges R Finset.univ : ℝ) / (t : ℝ) ^ 2)
  have hsumF : ∑ χ : V → Fin t, F χ = total * avg := by
    simp only [F, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      hsum_V, hsum_T, hsum_E]
    dsimp [avg]
    ring
  by_contra hlt
  push Not at hlt
  have hstrict : ∑ χ : V → Fin t, F χ < ∑ _χ : V → Fin t, avg :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun χ _ => hlt (S_of χ)
  have hrhs : ∑ _χ : V → Fin t, avg = total * avg := by
    simp [total]
  linarith

/- ### Part 7: Combining alteration + Shearer for the main theorem -/

private lemma shearer_final_algebra {k n N Ak C1 M t S'card Icard E' : ℕ}
    {d : ℝ} (hk : 3 ≤ k) (hAk_pos : 0 < Ak) (hC1_eq : C1 = 12 * (k - 2) * Ak ^ 2)
    (hM : Real.exp (200 * (C1 : ℝ) + 100) < (M : ℝ))
    (hN_pos : 0 < N) (hn2_le : n ^ 2 ≤ Ak ^ 2 * N)
    (hd_le : d ≤ ((k - 2 : ℕ) : ℝ) * (n : ℝ)) (hd_ge_M : (M : ℝ) ≤ d)
    (ht_ge : (20 : ℝ) ≤ (t : ℝ))
    (ht_sq_ge : 4 * ((k - 2 : ℕ) : ℝ) * d ≤ (t : ℝ) ^ 2)
    (ht_sq_le : (t : ℝ) ^ 2 ≤ 16 * ((k - 2 : ℕ) : ℝ) * d)
    (hS'_pos_lb : (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) ≤ (S'card : ℝ))
    (hS'_deg : (E' : ℝ) / (S'card : ℝ) ≤ (t : ℝ) / (2 * ((k - 2 : ℕ) : ℝ)))
    (hIbound : (S'card : ℝ) * shearerF ((E' : ℝ) / (S'card : ℝ)) ≤ (Icard : ℝ)) :
    n ≤ Icard := by
  have hNR_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hkm_pos : 0 < k - 2 := by omega
  have hkmR_pos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr hkm_pos
  have hS'_pos : (0 : ℝ) < (S'card : ℝ) := by
    have : (0 : ℝ) < (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) := by positivity
    linarith
  let d' : ℝ := (t : ℝ) / (2 * ((k - 2 : ℕ) : ℝ))
  have hC1_ge_k : ((k - 2 : ℕ) : ℝ) ≤ (C1 : ℝ) := by
    have h1 : 1 ≤ Ak ^ 2 := one_le_pow₀ hAk_pos
    have h2 : k - 2 ≤ 12 * (k - 2) * Ak ^ 2 := by nlinarith
    rw [hC1_eq]; exact_mod_cast h2
  have hM_gt_k : ((k - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by
    have hexp := Real.add_one_le_exp (200 * (C1 : ℝ) + 100)
    linarith
  have hd'_ge1 : 1 ≤ d' := by
    dsimp [d']
    rw [one_le_div (by positivity)]
    have h1 : (2 * ((k - 2 : ℕ) : ℝ)) ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hd'_pos : 0 < d' := by linarith
  have hF_mono : shearerF d' ≤ shearerF ((E' : ℝ) / (S'card : ℝ)) := by
    by_cases hE'0 : E' = 0
    · rw [hE'0, Nat.cast_zero, zero_div, shearerF_zero]
      unfold shearerF
      have hcx : ContinuousOn (fun s : ℝ => (1 - s) / (1 - s + d' * s)) (Set.uIcc 0 1) := by
        refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_
          (fun s hs => denom_ne_zero hd'_pos hs)
        exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn
      have hle := intervalIntegral.integral_mono_on zero_le_one hcx.intervalIntegrable
        (intervalIntegrable_const (μ := MeasureTheory.volume)) fun s hs => by
          have ha : 0 < 1 - s + d' * s := denom_pos hd'_pos hs.1 hs.2
          rw [div_le_one ha]
          nlinarith [hs.1]
      have h1eq : (∫ _s in (0 : ℝ)..1, (1 : ℝ)) = 1 := by simp
      linarith
    · have hd0_pos : 0 < (E' : ℝ) / (S'card : ℝ) :=
        div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hE'0)) hS'_pos
      exact shearerF_anti hd0_pos hS'_deg
  have hF_low : (Real.log d' - 1) / d' ≤ shearerF d' := shearerF_lower hd'_ge1
  have hM_pos : (0 : ℝ) < (M : ℝ) := (Real.exp_pos _).trans hM
  have hd'_sq_ge : (M : ℝ) / ((k - 2 : ℕ) : ℝ) ≤ d' ^ 2 := by
    dsimp [d']
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h2 : (M : ℝ) / ((k - 2 : ℕ) : ℝ) * (2 * ((k - 2 : ℕ) : ℝ)) ^ 2 =
        4 * ((k - 2 : ℕ) : ℝ) * (M : ℝ) := by
      field_simp [hkmR_pos.ne']; ring
    rw [h2]
    nlinarith
  have hlog_d' : 90 * (C1 : ℝ) + 40 ≤ Real.log d' := by
    have hlogM : 200 * (C1 : ℝ) + 100 ≤ Real.log (M : ℝ) := by
      have h1 := Real.log_le_log (Real.exp_pos _) hM.le
      rwa [Real.log_exp] at h1
    have hlogk : Real.log ((k - 2 : ℕ) : ℝ) ≤ (C1 : ℝ) := by
      have h1 : Real.log ((k - 2 : ℕ) : ℝ) ≤ ((k - 2 : ℕ) : ℝ) :=
        (Real.log_le_sub_one_of_pos hkmR_pos).trans (by linarith)
      linarith
    have hlog_sq : Real.log ((M : ℝ) / ((k - 2 : ℕ) : ℝ)) ≤ Real.log (d' ^ 2) :=
      Real.log_le_log (div_pos hM_pos hkmR_pos) hd'_sq_ge
    rw [Real.log_div hM_pos.ne' hkmR_pos.ne', Real.log_pow] at hlog_sq
    push_cast at hlog_sq
    linarith
  have hI_R : (n : ℝ) ≤ (Icard : ℝ) := by
    have hlog_pos : 90 * (C1 : ℝ) ≤ Real.log d' - 1 := by linarith
    have h1 : (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) * ((90 * (C1 : ℝ)) / d') ≤ (Icard : ℝ) := by
      calc (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) * ((90 * (C1 : ℝ)) / d')
          ≤ (S'card : ℝ) * ((Real.log d' - 1) / d') := by
            apply mul_le_mul hS'_pos_lb
            · exact div_le_div_of_nonneg_right hlog_pos hd'_pos.le
            · positivity
            · linarith
        _ ≤ (S'card : ℝ) * shearerF d' := mul_le_mul_of_nonneg_left hF_low hS'_pos.le
        _ ≤ (S'card : ℝ) * shearerF ((E' : ℝ) / (S'card : ℝ)) :=
            mul_le_mul_of_nonneg_left hF_mono hS'_pos.le
        _ ≤ (Icard : ℝ) := hIbound
    have hsimp : (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) * ((90 * (C1 : ℝ)) / d') =
        (75 * ((k - 2 : ℕ) : ℝ) * (C1 : ℝ) * (N : ℝ)) / (t : ℝ) ^ 2 := by
      dsimp [d']
      field_simp [show (t : ℝ) ≠ 0 by linarith, hkmR_pos.ne']
      ring
    rw [hsimp] at h1
    have hC1R : (C1 : ℝ) = 12 * ((k - 2 : ℕ) : ℝ) * (Ak : ℝ) ^ 2 := by
      rw [hC1_eq]; push_cast; ring
    have hn2R : (n : ℝ) ^ 2 ≤ (Ak : ℝ) ^ 2 * (N : ℝ) := by exact_mod_cast hn2_le
    have ht_ub : (t : ℝ) ^ 2 ≤ 16 * ((k - 2 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by
      calc (t : ℝ) ^ 2 ≤ 16 * ((k - 2 : ℕ) : ℝ) * d := ht_sq_le
        _ ≤ 16 * ((k - 2 : ℕ) : ℝ) * (((k - 2 : ℕ) : ℝ) * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hd_le (by positivity)
        _ = 16 * ((k - 2 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by ring
    have h2 : (n : ℝ) * (t : ℝ) ^ 2 ≤ 75 * ((k - 2 : ℕ) : ℝ) * (C1 : ℝ) * (N : ℝ) := by
      rw [hC1R]
      calc (n : ℝ) * (t : ℝ) ^ 2
          ≤ (n : ℝ) * (16 * ((k - 2 : ℕ) : ℝ) ^ 2 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left ht_ub (Nat.cast_nonneg n)
        _ = 16 * ((k - 2 : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
        _ ≤ 16 * ((k - 2 : ℕ) : ℝ) ^ 2 * ((Ak : ℝ) ^ 2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hn2R (by positivity)
        _ ≤ 900 * ((k - 2 : ℕ) : ℝ) ^ 2 * ((Ak : ℝ) ^ 2 * (N : ℝ)) := by
            have hnn : 0 ≤ ((k - 2 : ℕ) : ℝ) ^ 2 * ((Ak : ℝ) ^ 2 * (N : ℝ)) := by positivity
            linarith
        _ = 75 * ((k - 2 : ℕ) : ℝ) * (12 * ((k - 2 : ℕ) : ℝ) * (Ak : ℝ) ^ 2) * (N : ℝ) := by ring
    have h3 : (n : ℝ) ≤ (75 * ((k - 2 : ℕ) : ℝ) * (C1 : ℝ) * (N : ℝ)) / (t : ℝ) ^ 2 :=
      (le_div_iff₀ (by positivity)).mpr h2
    linarith
  exact_mod_cast hI_R

private lemma shearer_alteration_indep {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    {k n Ak C1 M : ℕ} (hk : 3 ≤ k) (hRfree : ¬ cycleGraph k ⊑ R)
    (hAk_pos : 0 < Ak) (hC1_eq : C1 = 12 * (k - 2) * Ak ^ 2)
    (hM : Real.exp (200 * (C1 : ℝ) + 100) < (M : ℝ))
    (hN_pos : 0 < Fintype.card V)
    (hn2_le : n ^ 2 ≤ Ak ^ 2 * Fintype.card V)
    (hd_le : (dirEdges R Finset.univ : ℝ) / (Fintype.card V : ℝ) ≤ ((k - 2 : ℕ) : ℝ) * (n : ℝ))
    (hd_ge_M : (M : ℝ) ≤ (dirEdges R Finset.univ : ℝ) / (Fintype.card V : ℝ)) :
    ∃ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) ∧ n ≤ I.card := by
  let N : ℕ := Fintype.card V
  let E : ℕ := dirEdges R Finset.univ
  let d : ℝ := (E : ℝ) / (N : ℝ)
  have hNR_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hkm_pos : 0 < k - 2 := by omega
  have hkmR_ge1 : (1 : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by exact_mod_cast hkm_pos
  have hM_ge_100 : (100 : ℝ) ≤ (M : ℝ) := by
    have h1 := Real.add_one_le_exp (200 * (C1 : ℝ) + 100)
    have h2 : (0 : ℝ) ≤ (C1 : ℝ) := Nat.cast_nonneg _
    linarith
  have hd_ge_100 : (100 : ℝ) ≤ d := by linarith
  let t : ℕ := Nat.ceil (Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d))
  have hrad_ge : (400 : ℝ) ≤ 4 * ((k - 2 : ℕ) : ℝ) * d := by nlinarith
  have hsqrt_ge : (20 : ℝ) ≤ Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d) := by
    have : (20 : ℝ) = Real.sqrt 400 := by
      rw [show (400 : ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt hrad_ge
  have ht_ge : (20 : ℝ) ≤ (t : ℝ) := hsqrt_ge.trans (Nat.le_ceil _)
  have ht_ge_1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ (t : ℝ) := by linarith
    exact_mod_cast this
  have ht_sq_ge : 4 * ((k - 2 : ℕ) : ℝ) * d ≤ (t : ℝ) ^ 2 := by
    have h1 := Nat.le_ceil (Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d))
    have h2 : (Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d)) ^ 2 ≤ (t : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (by linarith)] at h2
  have ht_le_2sqrt : (t : ℝ) ≤ 2 * Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d) := by
    have h1 : (t : ℝ) < Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    linarith
  have ht_sq_le : (t : ℝ) ^ 2 ≤ 16 * ((k - 2 : ℕ) : ℝ) * d := by
    have h1 : (t : ℝ) ^ 2 ≤ (2 * Real.sqrt (4 * ((k - 2 : ℕ) : ℝ) * d)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) ht_le_2sqrt 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h1
    linarith
  let c : ℝ := 2 * ((k - 2 : ℕ) : ℝ) / (t : ℝ)
  have hc_pos : 0 < c := by dsimp [c]; positivity
  obtain ⟨S, hS_good⟩ := exists_good_sample R t ht_ge_1 c
  have hT_le : (ordTriangles R Finset.univ : ℝ) ≤ 2 * ((k - 2 : ℕ) : ℝ) * (E : ℝ) := by
    have hnat := ordTriangles_le_of_no_cycle R hk hRfree
    have h1 : ordTriangles R Finset.univ ≤ 2 * (k - 2) * E := by
      have : k - 3 ≤ k - 2 := by omega
      calc ordTriangles R Finset.univ ≤ 2 * (k - 3) * E := hnat
        _ ≤ 2 * (k - 2) * E := Nat.mul_le_mul_right E (Nat.mul_le_mul_left 2 this)
    exact_mod_cast h1
  have hE_eq : (E : ℝ) = (N : ℝ) * d := by dsimp [d]; field_simp [hNR_pos.ne']
  have ht_pos : (0 : ℝ) < (t : ℝ) := by linarith
  have hNt3 : (N : ℝ) / (t : ℝ) * (t : ℝ) ^ 3 = (N : ℝ) * (t : ℝ) ^ 2 := by
    field_simp [ht_pos.ne']
  have hT_term : (ordTriangles R Finset.univ : ℝ) / (6 * (t : ℝ) ^ 3) ≤ (1 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) := by
    have h1 : (ordTriangles R Finset.univ : ℝ) ≤ 2 * ((k - 2 : ℕ) : ℝ) * ((N : ℝ) * d) := by
      rw [← hE_eq]; exact hT_le
    have h2 : 2 * ((k - 2 : ℕ) : ℝ) * ((N : ℝ) * d) ≤ (1 / 2 : ℝ) * (N : ℝ) * (t : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have h3 : (1 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) * (6 * (t : ℝ) ^ 3) =
        (1 / 2 : ℝ) * ((N : ℝ) / (t : ℝ) * (t : ℝ) ^ 3) := by ring
    rw [h3, hNt3]
    linarith
  have hE_term : c * ((E : ℝ) / (t : ℝ) ^ 2) ≤ (1 / 2 : ℝ) * ((N : ℝ) / (t : ℝ)) := by
    have hcE : c * ((E : ℝ) / (t : ℝ) ^ 2) =
        (2 * ((k - 2 : ℕ) : ℝ) * ((N : ℝ) * d)) / (t : ℝ) ^ 3 := by
      dsimp [c]; rw [hE_eq]; ring
    rw [hcE, div_le_iff₀ (by positivity)]
    have h3 : (1 / 2 : ℝ) * ((N : ℝ) / (t : ℝ)) * (t : ℝ) ^ 3 =
        (1 / 2 : ℝ) * ((N : ℝ) / (t : ℝ) * (t : ℝ) ^ 3) := by ring
    rw [h3, hNt3]
    nlinarith
  have hS_lower : (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) ≤
      (S.card : ℝ) - ((ordTriangles R S : ℝ) / 6) - c * (dirEdges R S : ℝ) := by
    have : (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) ≤
        ((N : ℝ) / (t : ℝ)) - ((ordTriangles R Finset.univ : ℝ) / (6 * (t : ℝ) ^ 3)) -
          c * ((E : ℝ) / (t : ℝ) ^ 2) := by linarith
    exact this.trans hS_good
  obtain ⟨S', hS'sub, hS'tf, hS'card_nat⟩ := remove_triangles R S
  have hS'card : (S.card : ℝ) - ((ordTriangles R S : ℝ) / 6) ≤ (S'.card : ℝ) := by
    have hR : 6 * (S.card : ℝ) ≤ 6 * (S'.card : ℝ) + (ordTriangles R S : ℝ) := by
      exact_mod_cast hS'card_nat
    linarith
  have hS'E : (dirEdges R S' : ℝ) ≤ (dirEdges R S : ℝ) := by
    have hnat : dirEdges R S' ≤ dirEdges R S := by
      unfold dirEdges degIn
      calc ∑ u ∈ S', (R.neighborFinset u ∩ S').card
          ≤ ∑ u ∈ S', (R.neighborFinset u ∩ S).card :=
            Finset.sum_le_sum fun u _ => Finset.card_le_card (Finset.inter_subset_inter_left hS'sub)
        _ ≤ ∑ u ∈ S, (R.neighborFinset u ∩ S).card :=
            Finset.sum_le_sum_of_subset hS'sub
    exact_mod_cast hnat
  have hS'_pos_lb : (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) ≤ (S'.card : ℝ) := by
    have hnn : 0 ≤ c * (dirEdges R S : ℝ) := mul_nonneg hc_pos.le (Nat.cast_nonneg _)
    linarith
  have hS'_pos : (0 : ℝ) < (S'.card : ℝ) := by
    have : (0 : ℝ) < (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) := by positivity
    linarith
  have hS'_deg : (dirEdges R S' : ℝ) / (S'.card : ℝ) ≤ (t : ℝ) / (2 * ((k - 2 : ℕ) : ℝ)) := by
    have h1 : c * (dirEdges R S' : ℝ) ≤ (S'.card : ℝ) := by
      have h2 : c * (dirEdges R S' : ℝ) ≤ c * (dirEdges R S : ℝ) :=
        mul_le_mul_of_nonneg_left hS'E hc_pos.le
      have h3 : (0 : ℝ) ≤ (5 / 12 : ℝ) * ((N : ℝ) / (t : ℝ)) := by positivity
      linarith
    rw [div_le_div_iff₀ hS'_pos (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right h1 ht_pos.le
    have hsimp : c * (dirEdges R S' : ℝ) * (t : ℝ) = (dirEdges R S' : ℝ) * (2 * ((k - 2 : ℕ) : ℝ)) := by
      dsimp [c]; field_simp [ht_pos.ne']
    linarith
  obtain ⟨I, _, hIind, hIbound⟩ := shearer_triangle_free R S' hS'tf
  refine ⟨I, hIind, shearer_final_algebra hk hAk_pos hC1_eq hM hN_pos hn2_le hd_le hd_ge_M
    ht_ge ht_sq_ge ht_sq_le hS'_pos_lb hS'_deg hIbound⟩

theorem main : OMA.R_Erdos570_erdos_570_R1_H1_R1.H2 := by
  classical
  intro k hk
  let Ak : ℕ := 2 * (200 * k ^ 2 + 2) * k
  let C1 : ℕ := 12 * (k - 2) * Ak ^ 2
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp (200 * (C1 : ℝ) + 100))
  let B : ℕ := max (100 * (k - 2) * (M + 1) ^ 2 * Ak ^ 4 + 100) 1000
  refine ⟨B, ?_⟩
  intro W V _ _ H G _hconn _hm_lo hW_lt hV_ge hV_size hfree
  let R : SimpleGraph V := Gᶜ
  have hRfree : ¬ cycleGraph k ⊑ R := hfree
  suffices h : ∃ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, ¬ R.Adj x y) ∧ Fintype.card W ≤ I.card by
    obtain ⟨I, hind, hcard⟩ := h
    have hcopy := isContained_compl_of_indepSet H R I hind hcard
    simpa [R, compl_compl] using hcopy
  let n : ℕ := Fintype.card W
  let N : ℕ := Fintype.card V
  by_cases hn0 : n = 0
  · exact ⟨∅, by simp, by omega⟩
  have hB_ge_1000 : 1000 ≤ B := le_max_right _ _
  have hN_ge_B : B ≤ N := hV_ge
  have hN_pos : 0 < N := by omega
  have hV_ne : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by simpa [N] using hN_pos)
  have hn2_le : n ^ 2 ≤ Ak ^ 2 * N := by
    have h1 : n ≤ Ak * Nat.sqrt (2 * H.edgeSet.ncard) := by
      dsimp [n, Ak]; rw [mul_assoc]; exact hW_lt.le
    have h2 : n ^ 2 ≤ (Ak * Nat.sqrt (2 * H.edgeSet.ncard)) ^ 2 := Nat.pow_le_pow_left h1 2
    rw [mul_pow] at h2
    have h3 : (Nat.sqrt (2 * H.edgeSet.ncard)) ^ 2 ≤ 2 * H.edgeSet.ncard := by
      rw [sq]; exact Nat.sqrt_le (2 * H.edgeSet.ncard)
    have h4 : 2 * H.edgeSet.ncard ≤ N := by dsimp [N]; omega
    calc n ^ 2 ≤ Ak ^ 2 * (Nat.sqrt (2 * H.edgeSet.ncard)) ^ 2 := h2
      _ ≤ Ak ^ 2 * (2 * H.edgeSet.ncard) := Nat.mul_le_mul_left _ h3
      _ ≤ Ak ^ 2 * N := Nat.mul_le_mul_left _ h4
  by_cases hbig_deg : ∃ v : V, (k - 2) * n ≤ (R.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hbig_deg
    have hnp := no_path_in_neighborFinset R hk hRfree v
    have hnp' : ¬ pathGraph (k - 2 + 1) ⊑ R.induce ((R.neighborFinset v : Finset V) : Set V) := by
      rwa [show k - 2 + 1 = k - 1 by omega]
    obtain ⟨I, _, hind, hIcard⟩ := indep_of_no_path R (r := k - 2) (by omega)
      (R.neighborFinset v) hnp'
    refine ⟨I, hind, ?_⟩
    have hkm : 0 < k - 2 := by omega
    nlinarith
  push Not at hbig_deg
  let E : ℕ := dirEdges R Finset.univ
  have hE_ub : E ≤ N * ((k - 2) * n) := by
    unfold E dirEdges degIn
    calc ∑ v : V, (R.neighborFinset v ∩ Finset.univ).card
        ≤ ∑ _v : V, (k - 2) * n := Finset.sum_le_sum fun v _ => by simpa using (hbig_deg v).le
      _ = N * ((k - 2) * n) := by simp [N]
  by_cases hsmall_E : n * (E + N) ≤ N ^ 2
  · obtain ⟨I, _, hind, hIbound⟩ := greedy_indep_bound R Finset.univ hV_ne
    refine ⟨I, hind, ?_⟩
    have hEN_pos : (0 : ℝ) < (E : ℝ) + (N : ℝ) := by positivity
    have h1 : (n : ℝ) * ((E : ℝ) + (N : ℝ)) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hsmall_E
    have h2 : (N : ℝ) ^ 2 ≤ (I.card : ℝ) * ((E : ℝ) + (N : ℝ)) := by simpa [E, N] using hIbound
    have h3 : (n : ℝ) ≤ (I.card : ℝ) := le_of_mul_le_mul_right (h1.trans h2) hEN_pos
    exact_mod_cast h3
  push Not at hsmall_E
  have hAk_pos : 0 < Ak := by dsimp [Ak]; positivity
  have hkm_pos : 0 < k - 2 := by omega
  have hN_lt_n2 : N < n * ((k - 2) * n + 1) := by
    have h1 : N ^ 2 < n * (N * ((k - 2) * n) + N) := lt_of_lt_of_le hsmall_E (by nlinarith)
    have h2 : N * N < N * (n * ((k - 2) * n + 1)) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h2
  have hNR_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hd_le : (E : ℝ) / (N : ℝ) ≤ ((k - 2 : ℕ) : ℝ) * (n : ℝ) := by
    rw [div_le_iff₀ hNR_pos]
    have : (E : ℝ) ≤ (N : ℝ) * (((k - 2 : ℕ) : ℝ) * (n : ℝ)) := by exact_mod_cast hE_ub
    linarith
  have hd_ge_half : (N : ℝ) / (n : ℝ) - 1 ≤ (E : ℝ) / (N : ℝ) := by
    have hnR_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have h1 : (N : ℝ) ^ 2 ≤ (n : ℝ) * ((E : ℝ) + (N : ℝ)) := by exact_mod_cast hsmall_E.le
    rw [sub_le_iff_le_add, div_le_iff₀ hnR_pos]
    have h3 : (N : ℝ) ≤ (n : ℝ) * ((E : ℝ) / (N : ℝ) + 1) := by
      have : (N : ℝ) * (N : ℝ) ≤ ((n : ℝ) * ((E : ℝ) / (N : ℝ) + 1)) * (N : ℝ) := by
        field_simp [hNR_pos.ne']
        linarith
      exact le_of_mul_le_mul_right this hNR_pos
    linarith
  have hd_ge_M : (M : ℝ) ≤ (E : ℝ) / (N : ℝ) := by
    have hN_ge : 100 * (k - 2) * (M + 1) ^ 2 * Ak ^ 4 ≤ N :=
      (le_trans (Nat.le_add_right _ 100) (le_max_left _ _)).trans hN_ge_B
    have hn2_ge : 50 * (M + 1) ^ 2 * Ak ^ 4 ≤ n ^ 2 := by
      have h1 : 1 ≤ (k - 2) * n := Nat.mul_pos hkm_pos (Nat.pos_of_ne_zero hn0)
      have h2 : n * ((k - 2) * n + 1) ≤ 2 * (k - 2) * n ^ 2 := by nlinarith
      have h3 : 100 * (k - 2) * (M + 1) ^ 2 * Ak ^ 4 ≤ 2 * (k - 2) * n ^ 2 :=
        hN_ge.trans (hN_lt_n2.le.trans h2)
      have h4 : (2 * (k - 2)) * (50 * (M + 1) ^ 2 * Ak ^ 4) ≤ (2 * (k - 2)) * n ^ 2 := by
        linarith
      exact Nat.le_of_mul_le_mul_left h4 (by omega)
    have hn_ge_Ak : 7 * (M + 1) * Ak ^ 2 ≤ n := by
      have hsq : (7 * (M + 1) * Ak ^ 2) ^ 2 ≤ n ^ 2 := by
        have : (7 * (M + 1) * Ak ^ 2) ^ 2 = 49 * (M + 1) ^ 2 * Ak ^ 4 := by ring
        rw [this]
        have h49 : 49 * (M + 1) ^ 2 * Ak ^ 4 ≤ 50 * (M + 1) ^ 2 * Ak ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
        exact h49.trans hn2_ge
      nlinarith
    have hNn : (7 * (M + 1) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
      have hnR_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      rw [le_div_iff₀ hnR_pos]
      have h1 : (7 * ((M : ℝ) + 1)) * (Ak : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn_ge_Ak
      have h2 : (n : ℝ) ^ 2 ≤ (Ak : ℝ) ^ 2 * (N : ℝ) := by exact_mod_cast hn2_le
      have hAkR : (0 : ℝ) < (Ak : ℝ) ^ 2 := by positivity
      have h3 : (7 * ((M : ℝ) + 1) * (n : ℝ)) * (Ak : ℝ) ^ 2 ≤ (N : ℝ) * (Ak : ℝ) ^ 2 := by
        nlinarith
      exact le_of_mul_le_mul_right h3 hAkR
    linarith
  exact shearer_alteration_indep R hk hRfree hAk_pos rfl hM hN_pos hn2_le hd_le hd_ge_M

end Erdos570DenseH2

theorem OMA.solution : OMA.R_Erdos570_erdos_570_R1_H1_R1.H2 :=
  Erdos570DenseH2.main
