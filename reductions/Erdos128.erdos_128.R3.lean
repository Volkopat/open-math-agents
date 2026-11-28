import FormalConjectures.ErdosProblems.«128»

/-!
# Independent-set expansion in a smallest counterexample to Erdős 128

Delete an independent set and equally many blocking vertices. Extending a sparse
half of the remainder by the independent set forces quantitative neighborhood
expansion in a smallest counterexample. Hall's theorem then gives a fractional
perfect matching even after up to a twenty-fourth of the vertices are deleted.
Doubling the graph turns a neighbor permutation into a perfect matching while
preserving expansion and the failure of the sparse-half bound. The two open
cases distinguish three-colorable graphs from graphs requiring more colors.

The two degree-sum identities and the balanced blow-up theorem, including its
rounding lemma, are from @iskamag's merged Erdős 128 reduction R2 (PR 1798).
-/

namespace OMA.R_Erdos128_erdos_128_R3

open Finset

/-- The remaining three-colorable case with quantitative expansion of independent sets. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    4 ∣ Fintype.card V → (G.Colorable 3) →
    (∀ I : Finset V, I.Nonempty → G.IsIndepSet (I : Set V) →
      23 * I.card + 2 * Fintype.card V <
        25 * ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).ncard) →
    (∃ τ : Equiv.Perm V, (∀ v, τ (τ v) = v) ∧ (∀ v, G.Adj v (τ v))) →
    (∀ D : Finset V, 24 * D.card ≤ Fintype.card V →
      ∃ σ : Equiv.Perm {v : V // v ∉ D}, ∀ v, G.Adj v.val (σ v).val) →
    ∃ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce S).edgeSet.ncard ≤ Fintype.card V ^ 2

/-- The remaining higher-chromatic case with quantitative expansion of independent sets. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    4 ∣ Fintype.card V → (¬ G.Colorable 3) →
    (∀ I : Finset V, I.Nonempty → G.IsIndepSet (I : Set V) →
      23 * I.card + 2 * Fintype.card V <
        25 * ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).ncard) →
    (∃ τ : Equiv.Perm V, (∀ v, τ (τ v) = v) ∧ (∀ v, G.Adj v (τ v))) →
    (∀ D : Finset V, 24 * D.card ≤ Fintype.card V →
      ∃ σ : Equiv.Perm {v : V // v ∉ D}, ∀ v, G.Adj v.val (σ v).val) →
    ∃ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce S).edgeSet.ncard ≤ Fintype.card V ^ 2

-- The following two degree-sum identities are from the merged Erdős 128 reduction R2.
lemma two_mul_induce_edgeSet_ncard {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    2 * (G.induce (S : Set V)).edgeSet.ncard = ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  classical
  have h1 : (G.induce (S : Set V)).edgeSet.ncard = #(G.induce (S : Set V)).edgeFinset := by
    rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_coe_sort S (fun u => #(S.filter (G.Adj u)))]
  apply Finset.sum_congr rfl
  intro u _
  rw [SimpleGraph.degree, ← Finset.card_map (Function.Embedding.subtype (· ∈ S))]
  congr 1
  ext v
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj,
    Function.Embedding.coe_subtype, Subtype.exists, Finset.mem_filter]
  constructor
  · rintro ⟨w, hw, hadj, rfl⟩
    exact ⟨hw, hadj⟩
  · rintro ⟨hv, hadj⟩
    exact ⟨v, hv, hadj, rfl⟩

/-- Directed edge count in a union of a disjoint independent set I and a set S. -/
lemma sum_adj_union_indep {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I S : Finset V}
    (hdisj : Disjoint I S)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) :
    ∑ u ∈ I ∪ S, #((I ∪ S).filter (G.Adj u)) =
      2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  rw [Finset.sum_union hdisj]
  have hfilter : ∀ u, #((I ∪ S).filter (G.Adj u)) = #(I.filter (G.Adj u)) + #(S.filter (G.Adj u)) := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  simp_rw [hfilter, Finset.sum_add_distrib]
  have hII : ∑ u ∈ I, #(I.filter (G.Adj u)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    exact hI u hu v hv
  have hIS : ∑ u ∈ I, #(S.filter (G.Adj u)) = ∑ w ∈ S, #(I.filter (G.Adj w)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm]
  omega


/-- A sparse half on an induced graph, expressed on the original vertex type. -/
lemma lift_half {V : Type} [Fintype V] (G : SimpleGraph V) (R : Finset V)
    (h : ∃ T : Set (R : Set V), 2 * T.ncard + 1 ≥ Fintype.card (R : Set V) ∧
      50 * ((G.induce (R : Set V)).induce T).edgeSet.ncard ≤ Fintype.card (R : Set V) ^ 2) :
    ∃ S : Finset V, S ⊆ R ∧ 2 * S.card + 1 ≥ R.card ∧
      50 * (G.induce (S : Set V)).edgeSet.ncard ≤ R.card ^ 2 := by
  classical
  obtain ⟨T, hsize, hedges⟩ := h
  let U : Set V := Subtype.val '' T
  let e : (G.induce (R : Set V)).induce T ≃g G.induce U :=
    { toEquiv := Equiv.Set.image Subtype.val T Subtype.val_injective
      map_rel_iff' := Iff.rfl }
  have hcount : ((G.induce (R : Set V)).induce T).edgeSet.ncard =
      (G.induce U).edgeSet.ncard := by
    simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using e.card_edgeFinset_eq
  have hR : Fintype.card (R : Set V) = R.card := Fintype.card_coe R
  have hU : U.ncard = T.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  refine ⟨U.toFinset, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, _, rfl⟩ := (Set.mem_toFinset.mp hv : v ∈ U)
    exact x.property
  · rwa [← Set.ncard_eq_toFinset_card', hU, ← hR]
  · rwa [Set.coe_toFinset, ← hcount, ← hR]

/-- Fill an equally sized deletion block, giving neighbors first priority. -/
lemma blocking_set {V : Type} [Fintype V] [DecidableEq V] (I N : Finset V)
    (hNI : Disjoint N I) (hsmall : 2 * I.card ≤ Fintype.card V) :
    ∃ D : Finset V, Disjoint I D ∧ D.card = I.card ∧ (N \ D).card = N.card - I.card := by
  have hsub : N ⊆ Iᶜ := fun x hx => mem_compl.mpr (disjoint_left.mp hNI hx)
  by_cases h : I.card ≤ N.card
  · obtain ⟨D, hd, hc⟩ := Finset.exists_subset_card_eq h
    exact ⟨D, hNI.symm.mono_right hd, hc, by rw [card_sdiff_of_subset hd, hc]⟩
  · obtain ⟨D, hn, hd, hc⟩ := Finset.exists_subsuperset_card_eq hsub (by omega)
      (by rw [card_compl]; omega : I.card ≤ Iᶜ.card)
    have hdis : Disjoint I D := disjoint_left.mpr fun x hx hd' => (mem_compl.mp (hd hd')) hx
    exact ⟨D, hdis, hc, by rw [sdiff_eq_empty_iff_subset.mpr hn, card_empty]; omega⟩


/-- If every smaller induced subgraph has a sparse half, remove two blocks of the same
size. Adding the independent block back to a sparse half of the remainder yields
a lower bound on its remaining incident edges in a counterexample. -/
lemma residual_edges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hbad : ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce S).edgeSet.ncard > Fintype.card V ^ 2)
    (hsmaller : ∀ R : Finset V, R.card < Fintype.card V →
      ∃ S : Finset V, S ⊆ R ∧ 2 * S.card + 1 ≥ R.card ∧
        50 * (G.induce (S : Set V)).edgeSet.ncard ≤ R.card ^ 2)
    (I D : Finset V) (hne : I.Nonempty) (hi : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hdis : Disjoint I D) (heq : D.card = I.card) :
    2 * I.card * (Fintype.card V - I.card) <
      25 * ∑ w ∈ (I ∪ D)ᶜ, (I.filter (G.Adj w)).card := by
  let R := (I ∪ D)ᶜ
  have hrn : R.card + 2 * I.card = Fintype.card V := by
    have h := Finset.card_add_card_compl (I ∪ D)
    rw [card_union_of_disjoint hdis, heq] at h
    change (I ∪ D)ᶜ.card + 2 * I.card = _
    omega
  have hpos := Finset.card_pos.mpr hne
  obtain ⟨S, hs, hsc, hse⟩ := hsmaller R (by omega)
  have hIS : Disjoint I S := disjoint_left.mpr fun x hx hxS =>
    (mem_compl.mp (hs hxS)) (mem_union_left D hx)
  have hc : 2 * (I ∪ S).card + 1 ≥ Fintype.card V := by
    rw [card_union_of_disjoint hIS]; omega
  have hb := hbad ((I ∪ S : Finset V) : Set V) (by rwa [Set.ncard_coe_finset])
  have hcount := two_mul_induce_edgeSet_ncard G (I ∪ S)
  rw [sum_adj_union_indep G hIS hi, ← two_mul_induce_edgeSet_ncard G S] at hcount
  have hsum : (∑ w ∈ S, (I.filter (G.Adj w)).card) ≤ ∑ w ∈ R, (I.filter (G.Adj w)).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  change 2 * I.card * (Fintype.card V - I.card) < 25 * ∑ w ∈ R, (I.filter (G.Adj w)).card
  rw [← hrn, show R.card + 2 * I.card - I.card = R.card + I.card by omega]
  rw [← hrn] at hb
  nlinarith only [hb, hcount, hse, hsum]

lemma expansion {V : Type} [Fintype V] (G : SimpleGraph V)
    (hbad : ∀ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce S).edgeSet.ncard > Fintype.card V ^ 2)
    (hsmaller : ∀ R : Finset V, R.card < Fintype.card V →
      ∃ S : Finset V, S ⊆ R ∧ 2 * S.card + 1 ≥ R.card ∧
        50 * (G.induce (S : Set V)).edgeSet.ncard ≤ R.card ^ 2)
    (I : Finset V) (hne : I.Nonempty) (hI : G.IsIndepSet (I : Set V)) :
    23 * I.card + 2 * Fintype.card V <
      25 * ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).ncard := by
  classical
  let N := ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).toFinset
  have hi : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := by
    intro x hx y hy ha
    exact hI hx hy ha.ne ha
  have hNI : Disjoint N I := by
    refine disjoint_left.mpr ?_
    intro x hx hxI
    obtain ⟨y, hy, ha⟩ := Set.mem_toFinset.mp hx
    exact hi y hy x hxI ha
  have hsmall : 2 * I.card ≤ Fintype.card V := by
    by_contra! h
    have he : 2 * (G.induce (I : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      apply Finset.sum_eq_zero
      intro w hw
      rw [card_eq_zero, filter_eq_empty_iff]
      exact hi w hw
    have hb := hbad (I : Set V) (by rw [Set.ncard_coe_finset]; omega)
    omega
  obtain ⟨D, hdis, heq, hdiff⟩ := blocking_set I N hNI hsmall
  have hlow := residual_edges G hbad hsmaller I D hne hi hdis heq
  let R := (I ∪ D)ᶜ
  have hfilter : ∀ w ∈ R, w ∉ N \ D → (I.filter (G.Adj w)).card = 0 := by
    intro w hw hnot
    rw [card_eq_zero, filter_eq_empty_iff]
    intro y hy hadj
    have hwD : w ∉ D := fun h => (mem_compl.mp hw) (mem_union_right I h)
    exact hnot (mem_sdiff.mpr ⟨Set.mem_toFinset.mpr ⟨y, hy, hadj.symm⟩, hwD⟩)
  have hsum : (∑ w ∈ R, (I.filter (G.Adj w)).card) ≤ (N \ D).card * I.card := by
    calc
      _ = ∑ w ∈ R.filter (· ∈ N \ D), (I.filter (G.Adj w)).card := by
        symm
        apply Finset.sum_subset (filter_subset _ _)
        intro w hw hnot
        exact hfilter w hw (fun h => hnot (mem_filter.mpr ⟨hw, h⟩))
      _ ≤ ∑ _w ∈ R.filter (· ∈ N \ D), I.card :=
        Finset.sum_le_sum (fun _ _ => card_filter_le _ _)
      _ ≤ (N \ D).card * I.card := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_le_card (fun _ hw => (mem_filter.mp hw).2))
  have hmul : (2 * (Fintype.card V - I.card)) * I.card < (25 * (N \ D).card) * I.card := by
    change 2 * I.card * (Fintype.card V - I.card) < 25 * ∑ w ∈ R, (I.filter (G.Adj w)).card at hlow
    calc
      _ = 2 * I.card * (Fintype.card V - I.card) := by ring
      _ < _ := hlow
      _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 25 hsum
  have hlt := Nat.lt_of_mul_lt_mul_right hmul
  rw [hdiff] at hlt
  change 23 * I.card + 2 * Fintype.card V < 25 * _
  rw [Set.ncard_eq_toFinset_card']
  change 23 * I.card + 2 * Fintype.card V < 25 * N.card
  omega



/-- Hall's condition for the bipartite double cover follows by testing independent
sets only. The unmatched part of a candidate obstruction is independent. -/
lemma neighbor_permutation {V : Type} [Fintype V] (G : SimpleGraph V)
    (hexp : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).ncard) :
    ∃ σ : Equiv.Perm V, ∀ v, G.Adj v (σ v) := by
  classical

  have hall (A : Finset V) :
      A.card ≤ (Finset.univ.filter (fun x => ∃ y ∈ A, G.Adj y x)).card := by
    let N := Finset.univ.filter (fun x => ∃ y ∈ A, G.Adj y x)
    let I := A \ N
    have hI : G.IsIndepSet (I : Set V) := by
      intro x hx y hy _ ha
      exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _, x, (mem_sdiff.mp hx).1, ha⟩)
    have hcount := hexp I hI
    rw [Set.ncard_eq_toFinset_card'] at hcount
    have hsub : ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).toFinset ⊆ N \ A := by
      intro x hx
      obtain ⟨y, hy, ha⟩ := Set.mem_toFinset.mp hx
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, y, (mem_sdiff.mp hy).1, ha⟩, ?_⟩
      intro hxA
      exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _, x, hxA, ha.symm⟩)
    have hle := hcount.trans (card_le_card hsub)
    change (A \ N).card ≤ (N \ A).card at hle
    have ha := Finset.card_inter_add_card_sdiff A N
    have hn := Finset.card_inter_add_card_sdiff N A
    rw [inter_comm N A] at hn
    change A.card ≤ N.card
    omega
  obtain ⟨f, hf, hadj⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective G.Adj).mp hall
  exact ⟨Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩, hadj⟩

/-- Deleting at most a twenty-fourth of the vertices still leaves a permutation
that sends every surviving vertex to a neighbor. Its cycles give a spanning
collection of disjoint edges and cycles, or equivalently a fractional perfect matching. -/
lemma robust_cycle_cover {V : Type} [Fintype V] (G : SimpleGraph V)
    (hexp : ∀ I : Finset V, I.Nonempty → G.IsIndepSet (I : Set V) →
      23 * I.card + 2 * Fintype.card V <
        25 * ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).ncard)
    (D : Finset V) (hd : 24 * D.card ≤ Fintype.card V) :
    ∃ σ : Equiv.Perm {v : V // v ∉ D}, ∀ v, G.Adj v.val (σ v).val := by
  classical
  let e := Function.Embedding.subtype (fun x : V => x ∉ D)
  let H := G.induce {x : V | x ∉ D}
  apply neighbor_permutation H
  intro I hI
  by_cases hi : I.Nonempty
  · let P := I.map e
    let N := ({x : V | ∃ y ∈ P, G.Adj y x} : Set V).toFinset
    let Q := ({x : {v : V // v ∉ D} | ∃ y ∈ I, H.Adj y x} : Set _).toFinset
    have hp : P.card = I.card := card_map _
    have hind : G.IsIndepSet (P : Set V) := by
      intro x hx y hy hne ha
      obtain ⟨a, haI, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hbI, rfl⟩ := mem_map.mp hy
      exact hI haI hbI (fun he => hne (congrArg e he)) ha
    have hpn : P.Nonempty := by rw [← Finset.card_pos, hp]; exact card_pos.mpr hi
    have hbound := hexp P hpn hind
    rw [Set.ncard_eq_toFinset_card'] at hbound
    change 23 * P.card + 2 * Fintype.card V < 25 * N.card at hbound
    have hdis : Disjoint P N := by
      refine disjoint_left.mpr ?_
      intro x hx hxn
      obtain ⟨y, hy, ha⟩ := Set.mem_toFinset.mp hxn
      exact hind hy hx ha.ne ha
    have hcap := card_le_univ (P ∪ N)
    rw [card_union_of_disjoint hdis] at hcap
    have hsub : N ⊆ D ∪ Q.map e := by
      intro x hx
      by_cases hxd : x ∈ D
      · exact mem_union_left _ hxd
      · obtain ⟨y, hy, ha⟩ := Set.mem_toFinset.mp hx
        obtain ⟨a, haI, rfl⟩ := mem_map.mp hy
        refine mem_union_right _ (mem_map.mpr ⟨⟨x, hxd⟩, ?_, rfl⟩)
        exact Set.mem_toFinset.mpr ⟨a, haI, ha⟩
    have hle := (card_le_card hsub).trans (card_union_le D (Q.map e))
    rw [card_map] at hle
    rw [Set.ncard_eq_toFinset_card']
    change I.card ≤ Q.card
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hi]

-- The rounding and blow-up lemmas below are reproduced from the merged R2.
-- They transfer the result back from two copies of each vertex.

lemma not_adj_of_cliqueFree_three {V : Type} {G : SimpleGraph V}
    (hTF : G.CliqueFree 3) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    False := by
  classical
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hne_bc : b ≠ c := G.ne_of_adj hbc
  have hne_ac : a ≠ c := G.ne_of_adj hac
  apply hTF {a, b, c}
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hac | exact hac.symm
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne_bc]
    · simp [hne_ab, hne_ac]

lemma shift_quad_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℕ) {u w : V} (huw : u ≠ w) {δ : ℕ} (hδ : δ ≤ a w)
    (hs : (∑ x : V, if G.Adj u x then a x else 0) ≤ ∑ x : V, if G.Adj w x then a x else 0) :
    let a' : V → ℕ := fun x => if x = u then a u + δ else if x = w then a w - δ else a x
    (∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0) ≤
      ∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 := by
  intro a'
  have hdiff : ((∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0 : ℕ) : ℤ) -
      ((∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 : ℕ) : ℤ) =
      2 * (δ : ℤ) * (((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) -
        ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ)) -
      (if G.Adj u w then 2 * (δ : ℤ) ^ 2 else 0) := by
    let d : V → ℤ := fun x => if x = u then (δ : ℤ) else if x = w then -(δ : ℤ) else 0
    have ha'z : ∀ x : V, (a' x : ℤ) = (a x : ℤ) + d x := by
      intro x
      by_cases hxu : x = u
      · subst hxu; simp [a', d]
      · by_cases hxw : x = w
        · subst hxw; simp [a', d, hxu, Nat.cast_sub hδ]; ring
        · simp [a', d, hxu, hxw]
    have hQ : ((∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0 : ℕ) : ℤ) -
        ((∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 : ℕ) : ℤ) =
        ∑ x : V, ∑ y : V, (if G.Adj x y then (a x : ℤ) * d y + d x * (a y : ℤ) + d x * d y else 0) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro y _
      by_cases hxy : G.Adj x y
      · simp only [hxy, if_true, ha'z x, ha'z y]; ring
      · simp [hxy]
    rw [hQ]
    have hsplit : ∑ x : V, ∑ y : V, (if G.Adj x y then (a x : ℤ) * d y + d x * (a y : ℤ) + d x * d y else 0) =
        (∑ x : V, ∑ y : V, if G.Adj x y then (a x : ℤ) * d y else 0) +
        (∑ x : V, ∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0) +
        (∑ x : V, ∑ y : V, if G.Adj x y then d x * d y else 0) := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      split_ifs <;> ring
    rw [hsplit]
    have hsym : (∑ x : V, ∑ y : V, if G.Adj x y then (a x : ℤ) * d y else 0) =
        ∑ x : V, ∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      by_cases h : G.Adj y x
      · have h' : G.Adj x y := h.symm
        simp only [h, h', if_true]; ring
      · have h' : ¬ G.Adj x y := fun hxy => h hxy.symm
        simp [h, h']
    have hsum_d : ∀ f : V → ℤ, ∑ x : V, d x * f x = (δ : ℤ) * (f u - f w) := by
      intro f
      have hsub : ∀ x : V, d x * f x = (if x = u then (δ : ℤ) * f u else 0) +
          (if x = w then -(δ : ℤ) * f w else 0) := by
        intro x
        by_cases hxu : x = u
        · subst hxu; simp [d, huw]
        · by_cases hxw : x = w
          · subst hxw; simp [d, hxu]
          · simp [d, hxu, hxw]
      simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hlin : (∑ x : V, ∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0) =
        (δ : ℤ) * (((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) -
          ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ)) := by
      have hterm : ∀ x : V, (∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0) =
          d x * (∑ y : V, if G.Adj x y then (a y : ℤ) else 0) := by
        intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring
      simp_rw [hterm]
      rw [hsum_d]
      push_cast
      have hc : ∀ z : V, (∑ y : V, (if G.Adj z y then (a y : ℤ) else 0)) =
          ∑ y : V, ((if G.Adj z y then a y else 0 : ℕ) : ℤ) := by
        intro z; apply Finset.sum_congr rfl; intro y _; split_ifs <;> simp
      rw [hc u, hc w]
    have hquad : (∑ x : V, ∑ y : V, if G.Adj x y then d x * d y else 0) =
        -(if G.Adj u w then 2 * (δ : ℤ) ^ 2 else 0) := by
      have hterm : ∀ x : V, (∑ y : V, if G.Adj x y then d x * d y else 0) =
          d x * (∑ y : V, if G.Adj x y then d y else 0) := by
        intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring
      simp_rw [hterm]
      rw [hsum_d]
      have hinner : ∀ z : V, (∑ y : V, if G.Adj z y then d y else 0) =
          (if G.Adj z u then (δ : ℤ) else 0) + (if G.Adj z w then -(δ : ℤ) else 0) := by
        intro z
        have hsub : ∀ y : V, (if G.Adj z y then d y else 0) =
            (if y = u then (if G.Adj z u then (δ : ℤ) else 0) else 0) +
            (if y = w then (if G.Adj z w then -(δ : ℤ) else 0) else 0) := by
          intro y
          by_cases hyu : y = u
          · subst hyu; simp [d, huw]
          · by_cases hyw : y = w
            · subst hyw; simp [d, hyu]
            · simp [d, hyu, hyw]
        simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hinner u, hinner w]
      by_cases huw_adj : G.Adj u w
      · have hwu_adj : G.Adj w u := huw_adj.symm
        simp [huw_adj, hwu_adj]; ring
      · have hwu_adj : ¬ G.Adj w u := fun h => huw_adj h.symm
        simp [huw_adj, hwu_adj]
    rw [hsym, hlin, hquad]; ring
  have hle0 : ((∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0 : ℕ) : ℤ) ≤
      ((∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 : ℕ) : ℤ) := by
    have hsz : ((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) ≤
        ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ) := Nat.cast_le.mpr hs
    have h1 : 2 * (δ : ℤ) * (((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) -
        ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h2 : (0 : ℤ) ≤ if G.Adj u w then 2 * (δ : ℤ) ^ 2 else 0 := by split_ifs <;> positivity
    linarith
  exact Nat.cast_le.mp hle0

theorem blowup_counterexample {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (H : SimpleGraph (V × Fin (2 * m))),
      (∀ u i v j, H.Adj (u, i) (v, j) ↔ G.Adj u v) ∧
      H.CliqueFree 3 ∧
      (∀ U : Set (V × Fin (2 * m)), 2 * U.ncard + 1 ≥ Fintype.card (V × Fin (2 * m)) →
        50 * (H.induce U).edgeSet.ncard > Fintype.card (V × Fin (2 * m)) ^ 2) ∧
      H.edgeSet.ncard = (2 * m) ^ 2 * G.edgeSet.ncard ∧
      (∀ u i, (H.neighborSet (u, i)).ncard = 2 * m * (G.neighborSet u).ncard) := by
  classical
  let H : SimpleGraph (V × Fin (2 * m)) := G.comap Prod.fst
  have hAdj : ∀ u i v j, H.Adj (u, i) (v, j) ↔ G.Adj u v := fun _ _ _ _ => Iff.rfl
  have hH_TF : H.CliqueFree 3 := by
    intro s hs
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hs.2
    have h1 : H.Adj p q := hs.1 (by simp) (by simp) hpq
    have h2 : H.Adj q r := hs.1 (by simp) (by simp) hqr
    have h3 : H.Adj p r := hs.1 (by simp) (by simp) hpr
    exact not_adj_of_cliqueFree_three hTF h1 h2 h3
  have hH_deg : ∀ u i, (H.neighborSet (u, i)).ncard = 2 * m * (G.neighborSet u).ncard := by
    intro u i
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    have hprod : (H.neighborSet (u, i)).toFinset = (G.neighborSet u).toFinset ×ˢ (Finset.univ : Finset (Fin (2 * m))) := by
      ext ⟨v, j⟩
      simp [H]
    rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hH_edges : H.edgeSet.ncard = (2 * m) ^ 2 * G.edgeSet.ncard := by
    have h1 : 2 * H.edgeSet.ncard = ∑ p : V × Fin (2 * m), (H.neighborSet p).ncard := by
      have hcard : H.edgeSet.ncard = #H.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro p _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    have h2 : 2 * G.edgeSet.ncard = ∑ u : V, (G.neighborSet u).ncard := by
      have hcard : G.edgeSet.ncard = #G.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro u _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    have hsum : ∑ p : V × Fin (2 * m), (H.neighborSet p).ncard =
        (2 * m) ^ 2 * ∑ u : V, (G.neighborSet u).ncard := by
      rw [Fintype.sum_prod_type]
      simp_rw [hH_deg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [← h1, ← h2] at hsum
    have hmul2 : 2 * H.edgeSet.ncard = 2 * ((2 * m) ^ 2 * G.edgeSet.ncard) := by rw [hsum]; ring
    omega
  have hH_sparse : ∀ U : Set (V × Fin (2 * m)), 2 * U.ncard + 1 ≥ Fintype.card (V × Fin (2 * m)) →
      50 * (H.induce U).edgeSet.ncard > Fintype.card (V × Fin (2 * m)) ^ 2 := by
    intro U hU_card
    by_contra hle
    push Not at hle
    set n := Fintype.card V
    have hN : Fintype.card (V × Fin (2 * m)) = 2 * m * n := by
      rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
    rw [hN] at hU_card hle
    have hU_ge : m * n ≤ #U.toFinset := by
      rw [Set.ncard_eq_toFinset_card'] at hU_card
      have : 2 * m * n = 2 * (m * n) := by ring
      omega
    obtain ⟨U₀, hU₀_sub, hU₀_card⟩ := Finset.exists_subset_card_eq hU_ge
    have hU₀_edges : 50 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard ≤ (2 * m * n) ^ 2 := by
      have hmono : (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard ≤ (H.induce U).edgeSet.ncard := by
        have h1 : 2 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard =
            ∑ p ∈ U₀, #(U₀.filter (H.Adj p)) := two_mul_induce_edgeSet_ncard H U₀
        have h2 : 2 * (H.induce U).edgeSet.ncard =
            ∑ p ∈ U.toFinset, #(U.toFinset.filter (H.Adj p)) := by
          have h2' := two_mul_induce_edgeSet_ncard H U.toFinset
          rwa [Set.coe_toFinset] at h2'
        have hle2 : ∑ p ∈ U₀, #(U₀.filter (H.Adj p)) ≤ ∑ p ∈ U.toFinset, #(U.toFinset.filter (H.Adj p)) :=
          (Finset.sum_le_sum (fun p _ => Finset.card_le_card (Finset.filter_subset_filter _ hU₀_sub))).trans
            (Finset.sum_le_sum_of_subset hU₀_sub)
        omega
      omega
    let a₀ : V → ℕ := fun v => #(Finset.univ.filter (fun i : Fin (2 * m) => (v, i) ∈ U₀))
    have ha₀_le : ∀ v, a₀ v ≤ 2 * m := fun v =>
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    have ha₀_sum : ∑ v : V, a₀ v = m * n := by
      rw [← hU₀_card]
      have hbij : #U₀ = ∑ v : V, #(Finset.univ.filter (fun i : Fin (2 * m) => (v, i) ∈ U₀)) := by
        have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := U₀) (t := (Finset.univ : Finset V))
          (fun _ _ => Finset.mem_univ _)
        rw [this]
        apply Finset.sum_congr rfl; intro v _
        refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            have hp' := Finset.mem_filter.mp hp; simpa [← hp'.2] using hp'.1⟩
        · intro p1 hp1 p2 hp2 heq
          exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) heq
        · intro i hi
          exact ⟨(v, i), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩, rfl⟩
      exact hbij.symm
    have hQ₀_eq : 2 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard =
        ∑ u : V, ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      have h1 : ∀ u : V, ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀),
          #(U₀.filter (H.Adj (u, i))) = ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0 := by
        intro u
        have hdeg : ∀ i : Fin (2 * m), #(U₀.filter (H.Adj (u, i))) =
            ∑ v : V, if G.Adj u v then a₀ v else 0 := by
          intro i
          have hfib := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
            (s := U₀.filter (H.Adj (u, i))) (t := (Finset.univ : Finset V)) (fun _ _ => Finset.mem_univ _)
          rw [hfib]
          apply Finset.sum_congr rfl; intro v _
          by_cases huv : G.Adj u v
          · rw [if_pos huv]
            refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
            · intro p hp
              have hp' := Finset.mem_filter.mp hp
              have hp1 := (Finset.mem_filter.mp hp'.1).1
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [← hp'.2] using hp1⟩
            · intro p1 hp1 p2 hp2 heq
              exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) heq
            · intro j hj
              exact ⟨(v, j), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, huv⟩, rfl⟩, rfl⟩
          · rw [if_neg huv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp heq
            have hadj : G.Adj u p.1 := (Finset.mem_filter.mp hp).2
            rw [heq] at hadj; exact huv hadj
        calc ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀), #(U₀.filter (H.Adj (u, i)))
            = ∑ _i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀), ∑ v : V, if G.Adj u v then a₀ v else 0 :=
              Finset.sum_congr rfl (fun i _ => hdeg i)
          _ = a₀ u * ∑ v : V, if G.Adj u v then a₀ v else 0 := by rw [Finset.sum_const, smul_eq_mul]
          _ = ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0 := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; split_ifs <;> ring
      have hfibU : ∑ p ∈ U₀, #(U₀.filter (H.Adj p)) =
          ∑ u : V, ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀), #(U₀.filter (H.Adj (u, i))) := by
        have hpart := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (s := U₀) (t := (Finset.univ : Finset V))
          (fun _ _ => Finset.mem_univ _) (fun p => #(U₀.filter (H.Adj p)))
        rw [← hpart]
        apply Finset.sum_congr rfl; intro u _
        refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
        · intro p hp
          have hp' := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [← hp'.2] using hp'.1⟩
        · intro p1 hp1 p2 hp2 heq
          exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) heq
        · intro i hi
          exact ⟨(u, i), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩, rfl⟩
        · intro p hp
          have hp' := (Finset.mem_filter.mp hp).2
          cases p with | mk v j => dsimp at hp'; subst hp'; rfl
      rw [hfibU]
      exact Finset.sum_congr rfl (fun u _ => h1 u)
    let valid : Finset (V → Fin (2 * m + 1)) :=
      Finset.univ.filter (fun f => ∑ v : V, (f v).val = m * n)
    let f₀ : V → Fin (2 * m + 1) := fun v => ⟨a₀ v, Nat.lt_succ_of_le (ha₀_le v)⟩
    have hf₀_mem : f₀ ∈ valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀_sum⟩
    let Q : (V → Fin (2 * m + 1)) → ℕ :=
      fun f => ∑ x : V, ∑ y : V, if G.Adj x y then (f x).val * (f y).val else 0
    let frac : (V → Fin (2 * m + 1)) → ℕ :=
      fun f => #(Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m))
    let score : (V → Fin (2 * m + 1)) → ℕ := fun f => (n + 1) * Q f + frac f
    obtain ⟨f, hf_mem, hf_min⟩ := Finset.exists_min_image valid score ⟨f₀, hf₀_mem⟩
    have hf_sum : ∑ v : V, (f v).val = m * n := (Finset.mem_filter.mp hf_mem).2
    have hQf_le : Q f ≤ Q f₀ := by
      have hsc := hf_min f₀ hf₀_mem
      dsimp only [score] at hsc
      have hfrac_le : frac f₀ ≤ n := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [n])
      have h1 : (n + 1) * Q f ≤ (n + 1) * Q f₀ + n := by omega
      by_contra hgt
      have : Q f₀ + 1 ≤ Q f := by omega
      have : (n + 1) * (Q f₀ + 1) ≤ (n + 1) * Q f := Nat.mul_le_mul_left (n + 1) this
      have : (n + 1) * (Q f₀ + 1) = (n + 1) * Q f₀ + n + 1 := by ring
      omega
    have hfrac_le1 : frac f ≤ 1 := by
      by_contra hgt
      dsimp only [frac] at hgt
      obtain ⟨u0, hu0, w0, hw0, hne0⟩ := Finset.one_lt_card.mp (by omega : 1 < #(Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m)))
      have hu0' := (Finset.mem_filter.mp hu0).2
      have hw0' := (Finset.mem_filter.mp hw0).2
      have hpair : ∃ u w : V, u ≠ w ∧ 0 < (f u).val ∧ (f u).val < 2 * m ∧ 0 < (f w).val ∧ (f w).val < 2 * m ∧
          (∑ x : V, if G.Adj u x then (f x).val else 0) ≤ ∑ x : V, if G.Adj w x then (f x).val else 0 := by
        by_cases hle_s : (∑ x : V, if G.Adj u0 x then (f x).val else 0) ≤ ∑ x : V, if G.Adj w0 x then (f x).val else 0
        · exact ⟨u0, w0, hne0, hu0'.1, hu0'.2, hw0'.1, hw0'.2, hle_s⟩
        · exact ⟨w0, u0, hne0.symm, hw0'.1, hw0'.2, hu0'.1, hu0'.2, by omega⟩
      obtain ⟨u, w, huw, hu_lo, hu_hi, hw_lo, hw_hi, hs_le⟩ := hpair
      set δ := min (2 * m - (f u).val) (f w).val
      have hδ_pos : 1 ≤ δ := by omega
      have hδ_u : (f u).val + δ ≤ 2 * m := by omega
      have hδ_w : δ ≤ (f w).val := Nat.min_le_right _ _
      let g : V → Fin (2 * m + 1) := fun x =>
        if x = u then ⟨(f u).val + δ, by omega⟩
        else if x = w then ⟨(f w).val - δ, by omega⟩
        else f x
      have hg_val : ∀ x : V, (g x).val = if x = u then (f u).val + δ else if x = w then (f w).val - δ else (f x).val := by
        intro x; by_cases hxu : x = u
        · subst hxu; simp [g]
        · by_cases hxw : x = w
          · subst hxw; simp [g, hxu]
          · simp [g, hxu, hxw]
      have hg_mem : g ∈ valid := by
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
        have hsum_g : ∑ x : V, (g x).val = ∑ x : V, (f x).val := by
          have hsub : ∀ x : V, (g x).val + (if x = w then δ else 0) = (f x).val + (if x = u then δ else 0) := by
            intro x; rw [hg_val]
            by_cases hxu : x = u
            · subst hxu; simp [huw]
            · by_cases hxw : x = w
              · subst hxw; simp [hxu]; omega
              · simp [hxu, hxw]
          have h1 := Finset.sum_congr rfl (fun x (_ : x ∈ (Finset.univ : Finset V)) => hsub x)
          simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
          omega
        omega
      have hQg_le : Q g ≤ Q f := by
        have hsh := shift_quad_le G (fun x => (f x).val) huw hδ_w hs_le
        have hEq : Q g = ∑ x : V, ∑ y : V, if G.Adj x y then
            (if x = u then (f u).val + δ else if x = w then (f w).val - δ else (f x).val) *
            (if y = u then (f u).val + δ else if y = w then (f w).val - δ else (f y).val) else 0 := by
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro y _
          rw [hg_val x, hg_val y]
        rw [hEq]; exact hsh
      have hfrac_lt : frac g < frac f := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          have hx' := (Finset.mem_filter.mp hx).2
          rw [hg_val] at hx'
          apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
          by_cases hxu : x = u
          · subst hxu; exact ⟨hu_lo, hu_hi⟩
          · by_cases hxw : x = w
            · subst hxw; exact ⟨hw_lo, hw_hi⟩
            · simp [hxu, hxw] at hx'; exact hx'
        · intro heq
          by_cases hhit : (f u).val + δ = 2 * m
          · have hu_in : u ∈ Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_lo, hu_hi⟩
            rw [← heq] at hu_in
            have := (Finset.mem_filter.mp hu_in).2
            rw [hg_val] at this; simp [hhit] at this
          · have hw_zero : (f w).val - δ = 0 := by omega
            have hw_in : w ∈ Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_lo, hw_hi⟩
            rw [← heq] at hw_in
            have := (Finset.mem_filter.mp hw_in).2
            rw [hg_val] at this; simp [huw.symm, hw_zero] at this
      have hsc_lt : score g < score f := by
        dsimp only [score]
        have : (n + 1) * Q g ≤ (n + 1) * Q f := Nat.mul_le_mul_left (n + 1) hQg_le
        omega
      have := hf_min g hg_mem
      omega
    let S : Finset V := Finset.univ.filter (fun v => (f v).val = 2 * m)
    have hS_card : 2 * #S + 1 ≥ n := by
      let F : Finset V := Finset.univ.filter (fun v => 0 < (f v).val ∧ (f v).val < 2 * m)
      have hsum_le : ∑ v : V, (f v).val ≤ 2 * m * #S + (2 * m - 1) * #F := by
        have hsplit : ∀ v : V, (f v).val ≤ (if v ∈ S then 2 * m else 0) + (if v ∈ F then 2 * m - 1 else 0) := by
          intro v
          by_cases hvS : (f v).val = 2 * m
          · have : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS⟩
            simp [this, hvS]
          · by_cases hv0 : (f v).val = 0
            · omega
            · have hvF : v ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by have := (f v).isLt; omega⟩
              simp [hvF]; have := (f v).isLt; omega
        calc ∑ v : V, (f v).val
            ≤ ∑ v : V, ((if v ∈ S then 2 * m else 0) + (if v ∈ F then 2 * m - 1 else 0)) :=
              Finset.sum_le_sum (fun v _ => hsplit v)
          _ = (∑ v : V, if v ∈ S then 2 * m else 0) + (∑ v : V, if v ∈ F then 2 * m - 1 else 0) :=
              Finset.sum_add_distrib
          _ = 2 * m * #S + (2 * m - 1) * #F := by
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
                ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
              ring
      have hF1 : #F ≤ 1 := hfrac_le1
      have hbound_n : m * n ≤ 2 * m * #S + (2 * m - 1) := by
        have : (2 * m - 1) * #F ≤ 2 * m - 1 := by
          calc (2 * m - 1) * #F ≤ (2 * m - 1) * 1 := Nat.mul_le_mul_left _ hF1
            _ = 2 * m - 1 := mul_one _
        omega
      have : m * n < m * (2 * #S + 2) := by
        have : m * (2 * #S + 2) = 2 * m * #S + 2 * m := by ring
        omega
      have : n < 2 * #S + 2 := Nat.lt_of_mul_lt_mul_left this
      omega
    have hQS : (2 * m) ^ 2 * (2 * (G.induce (S : Set V)).edgeSet.ncard) ≤ Q f := by
      rw [two_mul_induce_edgeSet_ncard]
      have h1 : (2 * m) ^ 2 * ∑ u ∈ S, #(S.filter (G.Adj u)) =
          ∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then (2 * m) * (2 * m) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _
        rw [Finset.card_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro v _
        split_ifs <;> ring
      rw [h1]
      calc (∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then (2 * m) * (2 * m) else 0)
          = (∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then (f u).val * (f v).val else 0) := by
            apply Finset.sum_congr rfl; intro u hu
            apply Finset.sum_congr rfl; intro v hv
            rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
        _ ≤ (∑ u ∈ S, ∑ v : V, if G.Adj u v then (f u).val * (f v).val else 0) :=
            Finset.sum_le_sum (fun u _ => Finset.sum_le_sum_of_subset (Finset.subset_univ S))
        _ ≤ Q f := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have h50S : 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
      apply hH (S : Set V)
      rw [Set.ncard_coe_finset]
      exact hS_card
    have h50_bad : 25 * Q f ≤ (2 * m) ^ 2 * n ^ 2 := by
      have hQf0 : 25 * Q f₀ = 50 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard := by
        change 25 * (∑ u : V, ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0) = _
        rw [← hQ₀_eq]; ring
      have hsq : (2 * m * n) ^ 2 = (2 * m) ^ 2 * n ^ 2 := by ring
      omega
    have h50_good : (2 * m) ^ 2 * n ^ 2 < 25 * ((2 * m) ^ 2 * (2 * (G.induce (S : Set V)).edgeSet.ncard)) := by
      have hpos : 0 < (2 * m) ^ 2 := by positivity
      have h1 : (2 * m) ^ 2 * n ^ 2 < (2 * m) ^ 2 * (50 * (G.induce (S : Set V)).edgeSet.ncard) :=
        Nat.mul_lt_mul_of_pos_left h50S hpos
      have h2 : (2 * m) ^ 2 * (50 * (G.induce (S : Set V)).edgeSet.ncard) =
          25 * ((2 * m) ^ 2 * (2 * (G.induce (S : Set V)).edgeSet.ncard)) := by ring
      omega
    omega
  exact ⟨H, hAdj, hH_TF, hH_sparse, hH_edges, hH_deg⟩


/-- The two-copy blow-up multiplies the neighborhood of an independent set's
projection by two. Partial fibers can only reduce the size of the set. -/
lemma double_expansion {V : Type} [Fintype V] (G : SimpleGraph V)
    (H : SimpleGraph (V × Fin 2))
    (hadj : ∀ u i v j, H.Adj (u, i) (v, j) ↔ G.Adj u v)
    (hexp : ∀ I : Finset V, I.Nonempty → G.IsIndepSet (I : Set V) →
      23 * I.card + 2 * Fintype.card V <
        25 * ({x : V | ∃ y ∈ I, G.Adj y x} : Set V).ncard)
    (I : Finset (V × Fin 2)) (hne : I.Nonempty) (hi : H.IsIndepSet (I : Set (V × Fin 2))) :
    23 * I.card + 2 * Fintype.card (V × Fin 2) <
      25 * ({x : V × Fin 2 | ∃ y ∈ I, H.Adj y x} : Set (V × Fin 2)).ncard := by
  classical
  let P := I.image Prod.fst
  have hp : G.IsIndepSet (P : Set V) := by
    intro u hu v hv hne' ha
    obtain ⟨⟨a, i⟩, hai, rfl⟩ := mem_image.mp hu
    obtain ⟨⟨b, j⟩, hbj, rfl⟩ := mem_image.mp hv
    exact hi hai hbj (fun h => hne' (congrArg Prod.fst h)) ((hadj a i b j).mpr ha)
  have h0 := hexp P (hne.image _) hp
  have hsub : I ⊆ P ×ˢ (Finset.univ : Finset (Fin 2)) := by
    intro x hx
    exact mem_product.mpr ⟨mem_image_of_mem _ hx, mem_univ _⟩
  have hle := card_le_card hsub
  simp only [card_product, card_univ, Fintype.card_fin] at hle
  let N := ({x : V | ∃ y ∈ P, G.Adj y x} : Set V).toFinset
  have hN : ({x : V × Fin 2 | ∃ y ∈ I, H.Adj y x} : Set (V × Fin 2)).toFinset =
      N ×ˢ (Finset.univ : Finset (Fin 2)) := by
    ext ⟨v, j⟩
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq, mem_product, mem_univ, and_true]
    constructor
    · rintro ⟨⟨u, i⟩, hu, ha⟩
      exact Set.mem_toFinset.mpr ⟨u, mem_image_of_mem _ hu, (hadj u i v j).mp ha⟩
    · intro hv
      obtain ⟨u, hu, ha⟩ := Set.mem_toFinset.mp hv
      obtain ⟨⟨a, i⟩, hai, rfl⟩ := mem_image.mp hu
      exact ⟨(a, i), hai, (hadj a i v j).mpr ha⟩
  rw [Set.ncard_eq_toFinset_card', hN, card_product, card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [Set.ncard_eq_toFinset_card'] at h0
  change 23 * P.card + 2 * Fintype.card V < 25 * N.card at h0
  omega

/-- A neighbor permutation on the base pairs every vertex of the first copy
with its image in the second, yielding a genuine perfect matching. -/
lemma double_matching {V : Type} (G : SimpleGraph V) (H : SimpleGraph (V × Fin 2))
    (hadj : ∀ u i v j, H.Adj (u, i) (v, j) ↔ G.Adj u v)
    (σ : Equiv.Perm V) (hσ : ∀ v, G.Adj v (σ v)) :
    ∃ τ : Equiv.Perm (V × Fin 2), (∀ v, τ (τ v) = v) ∧ (∀ v, H.Adj v (τ v)) := by
  let t : V × Fin 2 → V × Fin 2 := fun p =>
    if p.2 = 0 then (σ p.1, 1) else (σ.symm p.1, 0)
  have ht : Function.Involutive t := by
    rintro ⟨v, i⟩
    fin_cases i <;> simp [t]
  refine ⟨Function.Involutive.toPerm t ht, ht, ?_⟩
  rintro ⟨v, i⟩
  change H.Adj (v, i) (t (v, i))
  fin_cases i
  · simpa [t] using (hadj v 0 (σ v) 1).mpr (hσ v)
  · have ha : G.Adj v (σ.symm v) := by simpa using (hσ (σ.symm v)).symm
    simpa [t] using (hadj v 1 (σ.symm v) 0).mpr ha

theorem main : H1 → H2 → type_of% @Erdos128.erdos_128 := by
  classical
  intro hthree hhigher
  have inductionClaim (n : ℕ) : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → G.CliqueFree 3 →
      ∃ S : Set V, 2 * S.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce S).edgeSet.ncard ≤ Fintype.card V ^ 2 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ G hn htf
      by_contra! hbad
      have hsmaller (R : Finset V) (hr : R.card < Fintype.card V) :
          ∃ S : Finset V, S ⊆ R ∧ 2 * S.card + 1 ≥ R.card ∧
            50 * (G.induce (S : Set V)).edgeSet.ncard ≤ R.card ^ 2 := by
        apply lift_half
        have htf' : (G.induce (R : Set V)).CliqueFree 3 :=
          (G.cliqueFree_induce_iff _ _).mpr htf.cliqueFreeOn
        exact ih R.card (hr.trans_eq hn) (R : Set V) (G.induce (R : Set V))
          (Fintype.card_coe R) htf'
      have heven : Even (Fintype.card V) := by
        by_contra hodd
        rw [Nat.even_iff] at hodd
        have hnpos : 0 < Fintype.card V := by omega
        obtain ⟨v⟩ := Fintype.card_pos_iff.mp hnpos
        let R := (Finset.univ : Finset V).erase v
        have hr : R.card + 1 = Fintype.card V := by
          dsimp [R]; rw [card_erase_of_mem (mem_univ _), card_univ]; omega
        obtain ⟨S, _, hs, hedges⟩ := hsmaller R (by omega)
        have hlarge : 2 * S.card + 1 ≥ Fintype.card V := by omega
        have hb := hbad (S : Set V) (by rwa [Set.ncard_coe_finset])
        exact (not_lt_of_ge (hedges.trans (Nat.pow_le_pow_left (by omega : R.card ≤ Fintype.card V) 2))) hb
      have hexp := expansion G hbad hsmaller
      obtain ⟨σ, hσ⟩ := neighbor_permutation G (fun I hi => by
        by_cases hne : I.Nonempty
        · have h := hexp I hne hi
          have hc := Finset.card_le_univ I
          omega
        · simp [Finset.not_nonempty_iff_eq_empty.mp hne])
      obtain ⟨H, hadj, hHt, hHb, _, _⟩ := blowup_counterexample G htf hbad 1 (by decide)
      have he4 : 4 ∣ Fintype.card (V × Fin 2) := by
        obtain ⟨k, hk⟩ := heven
        refine ⟨k, ?_⟩
        rw [Fintype.card_prod, Fintype.card_fin, hk]
        ring
      have hHE := double_expansion G H hadj hexp
      have hM := double_matching G H hadj σ hσ
      have hrob := robust_cycle_cover H hHE
      have hsparse : ∃ S : Set (V × Fin 2), 2 * S.ncard + 1 ≥ Fintype.card (V × Fin 2) ∧
          50 * (H.induce S).edgeSet.ncard ≤ Fintype.card (V × Fin 2) ^ 2 := by
        by_cases hc : H.Colorable 3
        · exact hthree _ H hHt he4 hc hHE hM hrob
        · exact hhigher _ H hHt he4 hc hHE hM hrob
      obtain ⟨S, hs, he⟩ := hsparse
      exact (not_lt_of_ge he) (hHb S hs)
  intro V _ G hbad htf
  obtain ⟨S, hs, he⟩ := inductionClaim _ V G rfl htf
  exact (not_lt_of_ge he) (hbad S hs)

end OMA.R_Erdos128_erdos_128_R3
