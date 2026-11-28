import FormalConjectures.Paper.DegreeSequencesTriangleFree

/-!
# Theorem 1 of Erdős–Fajtlowicz–Staton (1991)

We prove `SimpleGraph.theorem1`: if a finite connected triangle-free graph `G` has maximum degree
multiplicity `degreeSequenceMultiplicity G = 2`, then `G` is bipartite, `G.minDegree = 1`, and
its degree sequence is compact (`d (k + 2) = d k + 1` for all `k + 2 < Fintype.card α`).

1. Order the vertices of `G` by nondecreasing degree `a 0 ≤ a 1 ≤ ... ≤ a (N - 1)`. Connectedness
   and `degreeSequenceMultiplicity G = 2` give `N ≥ 2`, `1 ≤ a k`, and `a k + 1 ≤ a (k + 2)`.
2. For any partition `V = S ⊔ T`, double counting gives
   `(∑ v ∈ T, G.degree v) + 2 * e(S) = (∑ v ∈ S, G.degree v) + 2 * e(T)`.
3. Mantel's theorem with equality characterization shows `e(T) ≤ |T|^2 / 4`, with equality forcing
   `G[T]` to be complete bipartite `K_{A,B}` with `|A|, |B| ≤ (|T| + 1) / 2`. When also `e(S) = 0`,
   triangle-freeness yields both `G.IsBipartite` and `G.degree s ≤ (|T| + 1) / 2` for all `s ∈ S`.
4. Splitting `N` modulo `4` rules out `N ≡ 1 (mod 4)` and forces equality (hence compactness,
   bipartiteness, and `a 0 = 1`) in all remaining cases `N ≡ 0, 2, 3 (mod 4)`.
-/

-- Problem: Theorem 1.
-- Upstream: formal-conjectures FormalConjectures/Paper/DegreeSequencesTriangleFree.lean:254 (declaration SimpleGraph.theorem1)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Theorem1EFSProof

open SimpleGraph Finset

/- ### Section 1: Ordering vertices by degree and basic degree-sequence properties -/

private lemma exists_vertex_ordering {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ ord : Fin (Fintype.card α) ≃ α,
      ∀ i : Fin (Fintype.card α), G.degree (ord i) = (degreeSequence G).getD i.1 0 := by
  let L : List α := Finset.univ.toList.mergeSort (fun u v => G.degree u ≤ G.degree v)
  have hperm : L.Perm Finset.univ.toList := List.mergeSort_perm _ _
  have hnodup : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList Finset.univ)
  have hlen : L.length = Fintype.card α := by
    rw [hperm.length_eq, Finset.length_toList, Finset.card_univ]
  have hsorted : (L.map (fun v => G.degree v)).Pairwise (· ≤ ·) := by
    have hp := List.pairwise_mergeSort (le := fun u v : α => decide (G.degree u ≤ G.degree v))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _)
      Finset.univ.toList
    rw [List.pairwise_map]
    exact hp.imp fun h => by simpa using h
  have hdeg_eq : L.map (fun v => G.degree v) = degreeSequence G := by
    have hperm_deg : (L.map (fun v => G.degree v)).Perm (degreeSequence G) := by
      have h1 : (L.map (fun v => G.degree v)).Perm (Finset.univ.toList.map (fun v => G.degree v)) :=
        hperm.map (fun v => G.degree v)
      have h2 : ((Finset.univ.toList.map (fun v => G.degree v) : List ℕ) : Multiset ℕ) =
          (degreeSequence G : Multiset ℕ) := by
        unfold degreeSequence
        rw [Multiset.sort_eq, ← Multiset.map_coe, Finset.coe_toList]
      exact h1.trans (Multiset.coe_eq_coe.mp h2)
    have hsorted_ds : (degreeSequence G).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
    exact hperm_deg.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hsorted hsorted_ds
  let f : Fin (Fintype.card α) → α := fun i => L[i.1]'(by omega)
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨?_, Fintype.card_fin _⟩
    intro i j hij
    have hfin_eq : (⟨i.1, by omega⟩ : Fin L.length) = ⟨j.1, by omega⟩ :=
      (List.nodup_iff_injective_getElem.mp hnodup)
        (show L[i.1]'(by omega) = L[j.1]'(by omega) from hij)
    exact Fin.ext (congrArg (Fin.val : Fin L.length → ℕ) hfin_eq)
  refine ⟨Equiv.ofBijective f hbij, fun i => ?_⟩
  change G.degree L[i.1] = (degreeSequence G).getD i.1 0
  rw [← hdeg_eq, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_map, hlen]; exact i.2)]
  simp

private lemma degreeSequence_length {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    (degreeSequence G).length = Fintype.card α := by
  unfold degreeSequence
  rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ]

private lemma degreeSequence_count_le {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (h₂ : degreeSequenceMultiplicity G = 2) (x : ℕ) :
    (degreeSequence G).count x ≤ 2 := by
  let ds := degreeSequence G
  by_cases hx : x ∈ ds
  · have hmem : ds.count x ∈ ds.map (fun d => ds.count d) :=
      List.mem_map.mpr ⟨x, hx, rfl⟩
    have hne : ds.map (fun d => ds.count d) ≠ [] := List.ne_nil_of_mem hmem
    obtain ⟨M, hmax⟩ := Option.ne_none_iff_exists'.mp (List.max?_eq_none_iff.not.mpr hne)
    have hM2 : M = 2 := by
      have h := h₂
      unfold degreeSequenceMultiplicity at h
      change (List.max? (ds.map (fun d => ds.count d))).getD 0 = 2 at h
      rw [hmax] at h
      simpa using h
    have hle : ds.count x ≤ M := (List.max?_eq_some_iff.mp hmax).2 _ hmem
    change ds.count x ≤ 2
    omega
  · rw [List.count_eq_zero_of_not_mem hx]
    omega

private lemma card_ge_two_of_mult_two {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (h_conn : G.Connected) [DecidableRel G.Adj]
    (h₂ : degreeSequenceMultiplicity G = 2) :
    2 ≤ Fintype.card α := by
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr h_conn.nonempty
  by_contra hlt
  have h1 : Fintype.card α = 1 := by omega
  have hlen : (degreeSequence G).length = 1 := by rw [degreeSequence_length, h1]
  cases hds : degreeSequence G with
  | nil => simp [hds] at hlen
  | cons x rest =>
    cases rest with
    | nil =>
      unfold degreeSequenceMultiplicity at h₂
      simp [hds] at h₂
    | cons _ _ =>
      simp [hds] at hlen

private lemma degreeSequence_mono {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {i j : ℕ}
    (hij : i ≤ j) (hj : j < Fintype.card α) :
    (degreeSequence G).getD i 0 ≤ (degreeSequence G).getD j 0 := by
  have hlen : (degreeSequence G).length = Fintype.card α := degreeSequence_length G
  have hi : i < (degreeSequence G).length := by omega
  have hj' : j < (degreeSequence G).length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj']
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have hp : (degreeSequence G).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
    exact (List.pairwise_iff_getElem.mp hp) i j hi hj' hlt

private lemma degreeSequence_step {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (h₂ : degreeSequenceMultiplicity G = 2) {k : ℕ} (hk : k + 2 < Fintype.card α) :
    (degreeSequence G).getD k 0 + 1 ≤ (degreeSequence G).getD (k + 2) 0 := by
  have hle01 := degreeSequence_mono G (show k ≤ k + 1 by omega) (by omega)
  have hle12 := degreeSequence_mono G (show k + 1 ≤ k + 2 by omega) hk
  by_contra hlt
  have heq02 : (degreeSequence G).getD (k + 2) 0 = (degreeSequence G).getD k 0 := by omega
  have heq01 : (degreeSequence G).getD (k + 1) 0 = (degreeSequence G).getD k 0 := by omega
  set x := (degreeSequence G).getD k 0
  have hlen : (degreeSequence G).length = Fintype.card α := degreeSequence_length G
  have hcount_ge : 3 ≤ (degreeSequence G).count x := by
    let i0 : Fin (degreeSequence G).length := ⟨k, by omega⟩
    let i1 : Fin (degreeSequence G).length := ⟨k + 1, by omega⟩
    let i2 : Fin (degreeSequence G).length := ⟨k + 2, by omega⟩
    have hs := List.map_getElem_sublist (l := degreeSequence G)
      (is := [i0, i1, i2]) (by simp [i0, i1, i2])
    have h0 : (degreeSequence G)[k] = x := by
      rw [← List.getD_eq_getElem _ _ (show k < (degreeSequence G).length by omega)]
    have h1 : (degreeSequence G)[k + 1] = x := by
      rw [← List.getD_eq_getElem _ _ (show k + 1 < (degreeSequence G).length by omega)]
      exact heq01
    have h2 : (degreeSequence G)[k + 2] = x := by
      rw [← List.getD_eq_getElem _ _ (show k + 2 < (degreeSequence G).length by omega)]
      exact heq02
    apply List.replicate_sublist_iff.mp
    simpa [i0, i1, i2, h0, h1, h2] using hs
  have hcount_le := degreeSequence_count_le G h₂ x
  omega

private lemma minDegree_eq_getD_zero {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (h_conn : G.Connected) [DecidableRel G.Adj] :
    G.minDegree = (degreeSequence G).getD 0 0 := by
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr h_conn.nonempty
  obtain ⟨ord, hord⟩ := exists_vertex_ordering G
  have hle1 : G.minDegree ≤ (degreeSequence G).getD 0 0 := by
    rw [← hord ⟨0, hpos⟩]
    exact G.minDegree_le_degree (ord ⟨0, hpos⟩)
  have hle2 : (degreeSequence G).getD 0 0 ≤ G.minDegree := by
    have : Nonempty α := h_conn.nonempty
    obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    obtain ⟨i, rfl⟩ : ∃ i, ord i = v := ⟨ord.symm v, ord.apply_symm_apply v⟩
    rw [hv, hord i]
    exact degreeSequence_mono G (Nat.zero_le _) i.2
  omega

private lemma telescope_excess {a : ℕ → ℕ} {N : ℕ}
    (hstep : ∀ k, k + 2 < N → a k + 1 ≤ a (k + 2)) :
    ∀ r k, k + 2 * r < N →
      a (k + 2 * r) = a k + r + ∑ j ∈ Finset.range r, (a (k + 2 * j + 2) - a (k + 2 * j) - 1) := by
  intro r
  induction r with
  | zero =>
    intro k _
    simp
  | succ r ih =>
    intro k hk
    have h1 := ih k (by omega)
    have h2 := hstep (k + 2 * r) (by omega)
    rw [Finset.sum_range_succ]
    have hidx : k + 2 * (r + 1) = k + 2 * r + 2 := by ring
    rw [hidx]
    omega

private lemma zero_of_double_sum {δ : ℕ → ℕ} {s t k : ℕ}
    (hsum : (∑ i ∈ Finset.range s, ∑ j ∈ Finset.range t, δ (i + 2 * j)) = 0)
    (ht : 0 < t) (hs : 2 ≤ s ∨ t = 1) (hk : k < s + 2 * (t - 1)) : δ k = 0 := by
  by_cases hkS : k < s
  · have h := (Finset.sum_eq_zero_iff.mp hsum) k (Finset.mem_range.mpr hkS)
    simpa using (Finset.sum_eq_zero_iff.mp h) 0 (Finset.mem_range.mpr ht)
  · have hs2 : 2 ≤ s := by omega
    let j : ℕ := (k - s) / 2 + 1
    let i : ℕ := k - 2 * j
    have hi : i < s := by dsimp [i, j]; omega
    have hj : j < t := by dsimp [j]; omega
    have heq : i + 2 * j = k := by dsimp [i, j]; omega
    have h := (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_range.mpr hi)
    have h' := (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_range.mpr hj)
    rwa [heq] at h'

/- ### Section 2: Partition degree identity and Mantel's theorem with equality -/

private lemma sum_deg_partition {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S T : Finset α) (hdisj : Disjoint S T) (hunion : S ∪ T = Finset.univ) :
    (∑ v ∈ T, G.degree v) + 2 * (G.induce (S : Set α)).edgeFinset.card =
      (∑ v ∈ S, G.degree v) + 2 * (G.induce (T : Set α)).edgeFinset.card := by
  have hdeg_split : ∀ v : α,
      G.degree v = (G.neighborFinset v ∩ T).card + (G.neighborFinset v ∩ S).card := by
    intro v
    rw [SimpleGraph.degree]
    have hdisj' : Disjoint (G.neighborFinset v ∩ T) (G.neighborFinset v ∩ S) :=
      hdisj.symm.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [← Finset.card_union_of_disjoint hdisj', ← Finset.inter_union_distrib_left,
      Finset.union_comm T S, hunion, Finset.inter_univ]
  have hind_sum : ∀ A : Finset α,
      ∑ v ∈ A, (G.neighborFinset v ∩ A).card = 2 * (G.induce (A : Set α)).edgeFinset.card := by
    intro A
    rw [← (G.induce (A : Set α)).sum_degrees_eq_twice_card_edges]
    rw [← Finset.sum_coe_sort A (fun v => (G.neighborFinset v ∩ A).card)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [SimpleGraph.degree]
    refine Finset.card_bij (fun u hu => (⟨u, (Finset.mem_inter.mp hu).2⟩ : { x : α // x ∈ A }))
      (fun u hu => by
        simp only [mem_neighborFinset, SimpleGraph.induce_adj]
        exact (mem_neighborFinset G v.1 u).mp (Finset.mem_inter.mp hu).1)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun u hu => ⟨u.1, Finset.mem_inter.mpr
        ⟨(mem_neighborFinset G v.1 u.1).mpr ((mem_neighborFinset _ v u).mp hu), u.2⟩, rfl⟩)
  have hcross : ∑ v ∈ T, (G.neighborFinset v ∩ S).card =
      ∑ v ∈ S, (G.neighborFinset v ∩ T).card := by
    have h1 : ∀ v : α, ∀ A : Finset α,
        (G.neighborFinset v ∩ A).card = ∑ u ∈ A, if G.Adj v u then 1 else 0 := by
      intro v A
      rw [← Finset.card_filter]
      congr 1
      ext u
      simp [Finset.mem_inter, mem_neighborFinset, and_comm]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp [G.adj_comm]
  have hT : ∑ v ∈ T, G.degree v =
      2 * (G.induce (T : Set α)).edgeFinset.card + ∑ v ∈ T, (G.neighborFinset v ∩ S).card := by
    simp_rw [hdeg_split, Finset.sum_add_distrib, hind_sum T]
  have hS : ∑ v ∈ S, G.degree v =
      ∑ v ∈ S, (G.neighborFinset v ∩ T).card + 2 * (G.induce (S : Set α)).edgeFinset.card := by
    simp_rw [hdeg_split, Finset.sum_add_distrib, hind_sum S]
  omega

private lemma mantel_bound_and_eq {β : Type*} [Fintype β] [DecidableEq β]
    (H : SimpleGraph β) [DecidableRel H.Adj] (hH : H.CliqueFree 3) :
    H.edgeFinset.card ≤ (Fintype.card β) ^ 2 / 4 ∧
      (1 ≤ Fintype.card β → H.edgeFinset.card = (Fintype.card β) ^ 2 / 4 →
        ∃ A B : Finset β,
          Disjoint A B ∧ A ∪ B = Finset.univ ∧
          A.card ≤ (Fintype.card β + 1) / 2 ∧ B.card ≤ (Fintype.card β + 1) / 2 ∧
          ∀ u v : β, H.Adj u v ↔ (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) := by
  by_cases ht0 : Fintype.card β = 0
  · have hE0 : H.edgeFinset.card = 0 := by
      have : IsEmpty β := Fintype.card_eq_zero_iff.mp ht0
      have : H.edgeFinset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e _
        induction e using Sym2.ind with
        | _ u _ => exact IsEmpty.elim ‹IsEmpty β› u
      simp [this]
    exact ⟨by simp [hE0], fun h => by omega⟩
  have hne : (Finset.univ : Finset β).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
  obtain ⟨x, _, hx_max⟩ := Finset.exists_max_image Finset.univ (fun v => H.degree v) hne
  let A : Finset β := H.neighborFinset x
  let B : Finset β := Finset.univ \ A
  have hdisj : Disjoint A B := Finset.disjoint_sdiff
  have hunion : A ∪ B = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ A)
  have hAcard : A.card = H.degree x := rfl
  have hBcard : B.card + A.card = Fintype.card β := by
    rw [← Finset.card_union_of_disjoint hdisj.symm, Finset.union_comm, hunion, Finset.card_univ]
  have hA_indep : ∀ u ∈ A, ∀ v ∈ A, ¬ H.Adj u v := by
    intro u hu v hv huv
    have hxu : H.Adj x u := (mem_neighborFinset H x u).mp hu
    have hxv : H.Adj x v := (mem_neighborFinset H x v).mp hv
    exact hH {x, u, v} (is3Clique_triple_iff.mpr ⟨hxu, hxv, huv⟩)
  have hdeg_split : ∀ v : β,
      H.degree v = (H.neighborFinset v ∩ A).card + (H.neighborFinset v ∩ B).card := by
    intro v
    rw [SimpleGraph.degree]
    have hd : Disjoint (H.neighborFinset v ∩ A) (H.neighborFinset v ∩ B) :=
      hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [← Finset.card_union_of_disjoint hd, ← Finset.inter_union_distrib_left, hunion,
      Finset.inter_univ]
  have hAA : ∑ u ∈ A, (H.neighborFinset u ∩ A).card = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    rw [Finset.mem_inter, mem_neighborFinset] at hv
    exact hA_indep u hu v hv.2 hv.1
  have hAB_eq : ∑ u ∈ A, (H.neighborFinset u ∩ B).card =
      ∑ b ∈ B, (H.neighborFinset b ∩ A).card := by
    have h1 : ∀ v : β, ∀ C : Finset β,
        (H.neighborFinset v ∩ C).card = ∑ w ∈ C, if H.Adj v w then 1 else 0 := by
      intro v C
      rw [← Finset.card_filter]
      congr 1; ext w; simp [Finset.mem_inter, mem_neighborFinset, and_comm]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun u _ => ?_
    simp [H.adj_comm]
  let pBA : ℕ := ∑ b ∈ B, (H.neighborFinset b ∩ A).card
  let pBB : ℕ := ∑ b ∈ B, (H.neighborFinset b ∩ B).card
  have h2E : 2 * H.edgeFinset.card = 2 * pBA + pBB := by
    rw [← H.sum_degrees_eq_twice_card_edges, ← hunion, Finset.sum_union hdisj]
    simp_rw [hdeg_split, Finset.sum_add_distrib, hAA, zero_add, hAB_eq]
    change pBA + (pBA + pBB) = 2 * pBA + pBB
    omega
  have hsumB : ∑ b ∈ B, H.degree b = pBA + pBB := by
    simp_rw [hdeg_split, Finset.sum_add_distrib]
    rfl
  have hsumB_le : ∑ b ∈ B, H.degree b ≤ B.card * A.card := by
    calc ∑ b ∈ B, H.degree b
        ≤ ∑ _b ∈ B, H.degree x := Finset.sum_le_sum fun b _ => hx_max b (Finset.mem_univ b)
      _ = B.card * A.card := by rw [Finset.sum_const, smul_eq_mul, hAcard]
  have hprod_le : B.card * A.card ≤ (Fintype.card β) ^ 2 / 4 := by
    have h4 : 4 * (B.card * A.card) ≤ (Fintype.card β) ^ 2 := by
      zify at hBcard ⊢
      nlinarith [sq_nonneg ((B.card : ℤ) - (A.card : ℤ))]
    omega
  have hE_le : H.edgeFinset.card ≤ (Fintype.card β) ^ 2 / 4 := by omega
  refine ⟨hE_le, fun _ hE_eq => ?_⟩
  have hpBB0 : pBB = 0 := by omega
  have hsumB_eq : ∑ b ∈ B, H.degree b = B.card * A.card := by omega
  have hprod_eq : B.card * A.card = (Fintype.card β) ^ 2 / 4 := by omega
  have hB_indep : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬ H.Adj b₁ b₂ := by
    intro b₁ hb₁ b₂ hb₂ hadj
    have h0 : (H.neighborFinset b₁ ∩ B).card = 0 :=
      (Finset.sum_eq_zero_iff.mp hpBB0) b₁ hb₁
    have hmem : b₂ ∈ H.neighborFinset b₁ ∩ B :=
      Finset.mem_inter.mpr ⟨(mem_neighborFinset H b₁ b₂).mpr hadj, hb₂⟩
    have hpos : 0 < (H.neighborFinset b₁ ∩ B).card := Finset.card_pos.mpr ⟨b₂, hmem⟩
    omega
  have hdegB_eq : ∀ b ∈ B, H.degree b = A.card := by
    have hsum_eq' : ∑ b ∈ B, H.degree b = ∑ _b ∈ B, A.card := by
      rw [hsumB_eq, Finset.sum_const, smul_eq_mul]
    exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hx_max b (Finset.mem_univ b))).mp hsum_eq'
  have hB_adj_all : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a := by
    intro b hb a ha
    have hsub : H.neighborFinset b ⊆ A := by
      intro u hu
      by_contra huA
      have huB : u ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huA⟩
      exact hB_indep b hb u huB ((mem_neighborFinset H b u).mp hu)
    have hnb_eq : H.neighborFinset b = A :=
      Finset.eq_of_subset_of_card_le hsub (by
        change A.card ≤ H.degree b
        rw [hdegB_eq b hb])
    exact (mem_neighborFinset H b a).mp (hnb_eq ▸ ha)
  have hA_le : A.card ≤ (Fintype.card β + 1) / 2 := by
    by_contra hgt
    have hdiff : (2 : ℤ) * A.card - Fintype.card β ≥ 2 := by omega
    have h4 : 4 * (B.card * A.card) + 4 ≤ (Fintype.card β) ^ 2 := by
      zify at hBcard ⊢
      nlinarith [sq_nonneg ((2 : ℤ) * A.card - Fintype.card β - 2)]
    omega
  have hB_le : B.card ≤ (Fintype.card β + 1) / 2 := by
    by_contra hgt
    have hdiff : (2 : ℤ) * B.card - Fintype.card β ≥ 2 := by omega
    have h4 : 4 * (B.card * A.card) + 4 ≤ (Fintype.card β) ^ 2 := by
      zify at hBcard ⊢
      nlinarith [sq_nonneg ((2 : ℤ) * B.card - Fintype.card β - 2)]
    omega
  refine ⟨A, B, hdisj, hunion, hA_le, hB_le, fun u v => ?_⟩
  constructor
  · intro huv
    have hu : u ∈ A ∨ u ∈ B := by
      have : u ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ u
      exact Finset.mem_union.mp this
    have hv : v ∈ A ∨ v ∈ B := by
      have : v ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ v
      exact Finset.mem_union.mp this
    rcases hu with huA | huB <;> rcases hv with hvA | hvB
    · exact absurd huv (hA_indep u huA v hvA)
    · exact Or.inl ⟨huA, hvB⟩
    · exact Or.inr ⟨huB, hvA⟩
    · exact absurd huv (hB_indep u huB v hvB)
  · rintro (⟨huA, hvB⟩ | ⟨huB, hvA⟩)
    · exact (hB_adj_all v hvB u huA).symm
    · exact hB_adj_all u huB v hvA

private lemma cliqueFree_induce {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) {n : ℕ} (h : G.CliqueFree n) (T : Finset α) :
    (G.induce (T : Set α)).CliqueFree n := by
  exact SimpleGraph.CliqueFree.comap ⟨SimpleGraph.Copy.induce G (T : Set α)⟩ h

private lemma bipartite_and_S_deg_of_mantel_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h₁ : G.CliqueFree 3)
    (S T : Finset α) (hdisj : Disjoint S T) (hunion : S ∪ T = Finset.univ)
    (hT_pos : 1 ≤ T.card)
    (heS : (G.induce (S : Set α)).edgeFinset.card = 0)
    (heT : (G.induce (T : Set α)).edgeFinset.card = T.card ^ 2 / 4) :
    G.IsBipartite ∧ ∀ s ∈ S, G.degree s ≤ (T.card + 1) / 2 := by
  have hT_tf : (G.induce (T : Set α)).CliqueFree 3 := cliqueFree_induce G h₁ T
  have hcardT : Fintype.card ↥(T : Set α) = T.card := Fintype.card_coe T
  obtain ⟨A', B', hAB_disj, hAB_union, hA_le, hB_le, hAB_adj⟩ :=
    (mantel_bound_and_eq (G.induce (T : Set α)) hT_tf).2 (by rw [hcardT]; exact hT_pos)
      (by rw [hcardT]; exact heT)
  let A : Finset α := A'.image Subtype.val
  let B : Finset α := B'.image Subtype.val
  have hA_card : A.card ≤ (T.card + 1) / 2 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simpa [hcardT] using hA_le
  have hB_card : B.card ≤ (T.card + 1) / 2 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simpa [hcardT] using hB_le
  have hA_sub : A ⊆ T := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact u.2
  have hB_sub : B ⊆ T := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact u.2
  have hT_split : ∀ v ∈ T, (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
    intro v hv
    let v' : { x : α // x ∈ T } := ⟨v, hv⟩
    have hv' : v' ∈ A' ∨ v' ∈ B' := by
      have : v' ∈ A' ∪ B' := by rw [hAB_union]; exact Finset.mem_univ v'
      exact Finset.mem_union.mp this
    rcases hv' with hA' | hB'
    · left
      refine ⟨Finset.mem_image.mpr ⟨v', hA', rfl⟩, ?_⟩
      intro hvB
      obtain ⟨w', hwB', hweq⟩ := Finset.mem_image.mp hvB
      have : w' = v' := Subtype.ext hweq
      subst this
      exact Finset.disjoint_left.mp hAB_disj hA' hwB'
    · right
      refine ⟨Finset.mem_image.mpr ⟨v', hB', rfl⟩, ?_⟩
      intro hvA
      obtain ⟨w', hwA', hweq⟩ := Finset.mem_image.mp hvA
      have : w' = v' := Subtype.ext hweq
      subst this
      exact Finset.disjoint_left.mp hAB_disj hwA' hB'
  have hAB_adj' : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u hu v hv
    have h := hAB_adj ⟨u, hu⟩ ⟨v, hv⟩
    have mem_img : ∀ (X' : Finset ↥(T : Set α)) (x : α) (hx : x ∈ T),
        (⟨x, hx⟩ : ↥(T : Set α)) ∈ X' ↔ x ∈ X'.image Subtype.val := by
      intro X' x hx
      refine ⟨fun hX => Finset.mem_image.mpr ⟨⟨x, hx⟩, hX, rfl⟩, fun hX => ?_⟩
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hX
      have : w = ⟨x, hx⟩ := Subtype.ext hweq
      rwa [← this]
    have huA : (⟨u, hu⟩ : ↥(T : Set α)) ∈ A' ↔ u ∈ A := mem_img A' u hu
    have huB : (⟨u, hu⟩ : ↥(T : Set α)) ∈ B' ↔ u ∈ B := mem_img B' u hu
    have hvA : (⟨v, hv⟩ : ↥(T : Set α)) ∈ A' ↔ v ∈ A := mem_img A' v hv
    have hvB : (⟨v, hv⟩ : ↥(T : Set α)) ∈ B' ↔ v ∈ B := mem_img B' v hv
    rw [← huA, ← huB, ← hvA, ← hvB]
    exact h
  have hS_indep : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    intro u hu v hv huv
    have hmem : s((⟨u, hu⟩ : { x : α // x ∈ S }), ⟨v, hv⟩) ∈
        (G.induce (S : Set α)).edgeFinset := by
      rw [mem_edgeFinset, mem_edgeSet]
      exact huv
    have hpos : 0 < (G.induce (S : Set α)).edgeFinset.card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hS_not_both : ∀ s ∈ S, ¬ ((∃ a ∈ A, G.Adj s a) ∧ (∃ b ∈ B, G.Adj s b)) := by
    rintro s hs ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩
    have hab : G.Adj a b := (hAB_adj' a (hA_sub ha) b (hB_sub hb)).mpr (Or.inl ⟨ha, hb⟩)
    exact h₁ {s, a, b} (is3Clique_triple_iff.mpr ⟨hsa, hsb, hab⟩)
  constructor
  · classical
    let col : α → Fin 2 := fun v =>
      if v ∈ A then 0
      else if v ∈ B then 1
      else if ∃ a ∈ A, G.Adj v a then 1 else 0
    refine ⟨SimpleGraph.Coloring.mk col ?_⟩
    intro u v huv
    have hu_ST : u ∈ S ∨ u ∈ T := by
      have : u ∈ S ∪ T := by rw [hunion]; exact Finset.mem_univ u
      exact Finset.mem_union.mp this
    have hv_ST : v ∈ S ∨ v ∈ T := by
      have : v ∈ S ∪ T := by rw [hunion]; exact Finset.mem_univ v
      exact Finset.mem_union.mp this
    rcases hu_ST with huS | huT <;> rcases hv_ST with hvS | hvT
    · exact absurd huv (hS_indep u huS v hvS)
    · have huA : u ∉ A := fun h => Finset.disjoint_left.mp hdisj huS (hA_sub h)
      have huB : u ∉ B := fun h => Finset.disjoint_left.mp hdisj huS (hB_sub h)
      rcases hT_split v hvT with ⟨hvA, _⟩ | ⟨hvB, hvA⟩
      · have hex : ∃ a ∈ A, G.Adj u a := ⟨v, hvA, huv⟩
        simp only [col, huA, huB, hvA, hex, ↓reduceIte]
        decide
      · have hno : ¬ ∃ a ∈ A, G.Adj u a := fun hex => hS_not_both u huS ⟨hex, ⟨v, hvB, huv⟩⟩
        simp only [col, huA, huB, hvA, hvB, hno, ↓reduceIte]
        decide
    · have hvA : v ∉ A := fun h => Finset.disjoint_left.mp hdisj hvS (hA_sub h)
      have hvB : v ∉ B := fun h => Finset.disjoint_left.mp hdisj hvS (hB_sub h)
      rcases hT_split u huT with ⟨huA, _⟩ | ⟨huB, huA⟩
      · have hex : ∃ a ∈ A, G.Adj v a := ⟨u, huA, huv.symm⟩
        simp only [col, huA, hvA, hvB, hex, ↓reduceIte]
        decide
      · have hno : ¬ ∃ a ∈ A, G.Adj v a := fun hex => hS_not_both v hvS ⟨hex, ⟨u, huB, huv.symm⟩⟩
        simp only [col, huA, huB, hvA, hvB, hno, ↓reduceIte]
        decide
    · rcases (hAB_adj' u huT v hvT).mp huv with ⟨huA, hvB⟩ | ⟨huB, hvA⟩
      · have hvA : v ∉ A := by
          rcases hT_split v hvT with ⟨_, h⟩ | ⟨_, h⟩
          · exact absurd hvB h
          · exact h
        simp only [col, huA, hvA, hvB, ↓reduceIte]
        decide
      · have huA : u ∉ A := by
          rcases hT_split u huT with ⟨_, h⟩ | ⟨_, h⟩
          · exact absurd huB h
          · exact h
        simp only [col, huA, huB, hvA, ↓reduceIte]
        decide
  · intro s hs
    have hnb_sub_T : G.neighborFinset s ⊆ T := by
      intro u hu
      have hsu : G.Adj s u := (mem_neighborFinset G s u).mp hu
      have hu_ST : u ∈ S ∨ u ∈ T := by
        have : u ∈ S ∪ T := by rw [hunion]; exact Finset.mem_univ u
        exact Finset.mem_union.mp this
      rcases hu_ST with huS | huT
      · exact absurd hsu (hS_indep s hs u huS)
      · exact huT
    by_cases hexA : ∃ a ∈ A, G.Adj s a
    · have hsubA : G.neighborFinset s ⊆ A := by
        intro u hu
        have hsu : G.Adj s u := (mem_neighborFinset G s u).mp hu
        rcases hT_split u (hnb_sub_T hu) with ⟨huA, _⟩ | ⟨huB, _⟩
        · exact huA
        · exact absurd ⟨hexA, ⟨u, huB, hsu⟩⟩ (hS_not_both s hs)
      exact le_trans (Finset.card_le_card hsubA) hA_card
    · have hsubB : G.neighborFinset s ⊆ B := by
        intro u hu
        have hsu : G.Adj s u := (mem_neighborFinset G s u).mp hu
        rcases hT_split u (hnb_sub_T hu) with ⟨huA, _⟩ | ⟨huB, _⟩
        · exact absurd ⟨u, huA, hsu⟩ hexA
        · exact huB
      exact le_trans (Finset.card_le_card hsubB) hB_card

private lemma mantel_ineq_induced {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h₁ : G.CliqueFree 3) (T : Finset α) :
    (G.induce (T : Set α)).edgeFinset.card ≤ T.card ^ 2 / 4 := by
  have hT_tf : (G.induce (T : Set α)).CliqueFree 3 := cliqueFree_induce G h₁ T
  have hcardT : Fintype.card ↥(T : Set α) = T.card := Fintype.card_coe T
  have h := (mantel_bound_and_eq (G.induce (T : Set α)) hT_tf).1
  rwa [hcardT] at h

end Theorem1EFSProof

theorem OMA.solution : type_of% @SimpleGraph.theorem1 := by
  intro α _ _ G h_conn _ h₁ h₂
  set N : ℕ := Fintype.card α
  have hN2 : 2 ≤ N := Theorem1EFSProof.card_ge_two_of_mult_two G h_conn h₂
  obtain ⟨ord, hord⟩ := Theorem1EFSProof.exists_vertex_ordering G
  let a : ℕ → ℕ := fun k => (SimpleGraph.degreeSequence G).getD k 0
  have ha_pos : ∀ k < N, 1 ≤ a k := by
    intro k hk
    have hdeg : G.degree (ord ⟨k, hk⟩) = a k := hord ⟨k, hk⟩
    have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hpos := h_conn.preconnected.degree_pos_of_nontrivial (ord ⟨k, hk⟩)
    omega
  have ha_mono : ∀ i j, i ≤ j → j < N → a i ≤ a j :=
    fun _ _ hij hj => Theorem1EFSProof.degreeSequence_mono G hij hj
  have ha_step : ∀ k, k + 2 < N → a k + 1 ≤ a (k + 2) :=
    fun _ hk => Theorem1EFSProof.degreeSequence_step G h₂ hk
  let δ : ℕ → ℕ := fun k => a (k + 2) - a k - 1
  have htele : ∀ r k, k + 2 * r < N →
      a (k + 2 * r) = a k + r + ∑ j ∈ Finset.range r, δ (k + 2 * j) :=
    Theorem1EFSProof.telescope_excess ha_step
  have hcompact_of_δ : (∀ k, k + 2 < N → δ k = 0) → SimpleGraph.HasCompactdegreeSequence G := by
    intro hδ k hk
    have h1 := ha_step k hk
    have h0 := hδ k hk
    dsimp only [δ] at h0
    change a (k + 2) = a k + 1
    omega
  have hmin_eq : G.minDegree = a 0 := Theorem1EFSProof.minDegree_eq_getD_zero G h_conn
  have hsplit_setup : ∀ s : ℕ, s ≤ N →
      ∃ S T : Finset α, Disjoint S T ∧ S ∪ T = Finset.univ ∧
        S.card = s ∧ T.card = N - s ∧
        (∀ i : Fin N, i.1 < s → ord i ∈ S) ∧
        (∑ v ∈ S, G.degree v = ∑ i ∈ Finset.range s, a i) ∧
        (∑ v ∈ T, G.degree v = ∑ i ∈ Finset.range (N - s), a (i + s)) := by
    intro s hs
    let S : Finset α := (Finset.univ.filter (fun i : Fin N => i.1 < s)).image ord
    let T : Finset α := (Finset.univ.filter (fun i : Fin N => s ≤ i.1)).image ord
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro v hvS hvT
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvS
      obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hvT
      have hij : j = i := ord.injective hjeq
      subst hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      omega
    have hunion : S ∪ T = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hlt : (ord.symm v).1 < s
      · left
        exact Finset.mem_image.mpr ⟨ord.symm v, by simp [hlt], Equiv.apply_symm_apply _ _⟩
      · right
        exact Finset.mem_image.mpr ⟨ord.symm v, by simp [show s ≤ (ord.symm v).1 by omega],
          Equiv.apply_symm_apply _ _⟩
    have hScard : S.card = s := by
      rw [Finset.card_image_of_injective _ ord.injective, Fin.card_filter_val_lt, min_eq_right hs]
    have hTcard : T.card = N - s := by
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, hScard] at h
      omega
    have hSsum : ∑ v ∈ S, G.degree v = ∑ i ∈ Finset.range s, a i := by
      rw [Finset.sum_image (fun _ _ _ _ h => ord.injective h)]
      refine Finset.sum_bij (fun i _ => i.1)
        (fun i hi => Finset.mem_range.mpr (by simpa using hi))
        (fun _ _ _ _ h => Fin.ext h)
        (fun k hk => ⟨⟨k, by have := Finset.mem_range.mp hk; omega⟩,
          by simp [Finset.mem_range.mp hk], rfl⟩)
        (fun i _ => hord i)
    have hTsum : ∑ v ∈ T, G.degree v = ∑ i ∈ Finset.range (N - s), a (i + s) := by
      rw [Finset.sum_image (fun _ _ _ _ h => ord.injective h)]
      refine Finset.sum_bij (fun i _ => i.1 - s)
        (fun i hi => Finset.mem_range.mpr (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := i.2; omega))
        (fun i₁ hi₁ i₂ hi₂ h => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
          exact Fin.ext (by omega))
        (fun k hk => ⟨⟨k + s, by have := Finset.mem_range.mp hk; omega⟩,
          by simp, by dsimp; omega⟩)
        (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [hord i, show i.1 - s + s = i.1 by omega])
    exact ⟨S, T, hdisj, hunion, hScard, hTcard,
      fun i hi => Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩, hSsum, hTsum⟩
  let n : ℕ := N / 4
  have hmod : N = 4 * n ∨ N = 4 * n + 1 ∨ N = 4 * n + 2 ∨ N = 4 * n + 3 := by omega
  rcases hmod with hN0 | hN1 | hN2_case | hN3
  · -- Case N = 4 * n (n ≥ 1)
    have hn1 : 1 ≤ n := by omega
    obtain ⟨S, T, hdisj, hunion, hScard, hTcard, hSmem, hSsum, hTsum⟩ :=
      hsplit_setup (2 * n) (by omega)
    have hTcard' : T.card = 2 * n := by omega
    have hpart := Theorem1EFSProof.sum_deg_partition G S T hdisj hunion
    have hmantel := Theorem1EFSProof.mantel_ineq_induced G h₁ T
    have hmantel_val : T.card ^ 2 / 4 = n * n := by
      rw [hTcard']
      have : (2 * n) ^ 2 = 4 * (n * n) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    have hTsum' : ∑ v ∈ T, G.degree v =
        (∑ i ∈ Finset.range (2 * n), a i) + 2 * n * n +
          ∑ i ∈ Finset.range (2 * n), ∑ j ∈ Finset.range n, δ (i + 2 * j) := by
      rw [hTsum, show N - 2 * n = 2 * n by omega]
      have hterm : ∀ i ∈ Finset.range (2 * n),
          a (i + 2 * n) = a i + n + ∑ j ∈ Finset.range n, δ (i + 2 * j) := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact htele n i (by omega)
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hmul : 2 * n * n = 2 * (n * n) := by ring
    have hdiff_eq : (∑ i ∈ Finset.range (2 * n), ∑ j ∈ Finset.range n, δ (i + 2 * j)) = 0 ∧
        (G.induce (S : Set α)).edgeFinset.card = 0 ∧
        (G.induce (T : Set α)).edgeFinset.card = T.card ^ 2 / 4 := by
      rw [hTsum', hSsum] at hpart
      omega
    obtain ⟨hδ_sum0, heS0, heT_eq⟩ := hdiff_eq
    have hδ0 : ∀ k, k + 2 < N → δ k = 0 := by
      intro k hk
      exact Theorem1EFSProof.zero_of_double_sum hδ_sum0 (by omega) (by omega) (by omega)
    obtain ⟨hbip, hSdeg⟩ := Theorem1EFSProof.bipartite_and_S_deg_of_mantel_eq G h₁ S T
      hdisj hunion (by omega) heS0 heT_eq
    have hmin1 : G.minDegree = 1 := by
      rw [hmin_eq]
      have htopS_le : a (2 * n - 1) ≤ n := by
        have hmem : ord ⟨2 * n - 1, by omega⟩ ∈ S := hSmem ⟨2 * n - 1, by omega⟩ (by dsimp; omega)
        have hdeg := hSdeg _ hmem
        rw [hord ⟨2 * n - 1, by omega⟩, hTcard'] at hdeg
        change a (2 * n - 1) ≤ (2 * n + 1) / 2 at hdeg
        omega
      have htopS_ge : a 1 + (n - 1) ≤ a (2 * n - 1) := by
        have ht := htele (n - 1) 1 (by omega)
        have hidx : 1 + 2 * (n - 1) = 2 * n - 1 := by omega
        rw [hidx] at ht
        omega
      have h01 : a 0 ≤ a 1 := ha_mono 0 1 (by omega) (by omega)
      have h0pos : 1 ≤ a 0 := ha_pos 0 (by omega)
      omega
    exact ⟨hbip, hmin1, hcompact_of_δ hδ0⟩
  · -- Case N = 4 * n + 1: impossible
    have hn1 : 1 ≤ n := by omega
    obtain ⟨S, T, hdisj, hunion, hScard, hTcard, _, hSsum, hTsum⟩ :=
      hsplit_setup (2 * n) (by omega)
    have hTcard' : T.card = 2 * n + 1 := by omega
    have hpart := Theorem1EFSProof.sum_deg_partition G S T hdisj hunion
    have hmantel := Theorem1EFSProof.mantel_ineq_induced G h₁ T
    have hmantel_val : T.card ^ 2 / 4 = n * n + n := by
      rw [hTcard']
      have : (2 * n + 1) ^ 2 = 4 * (n * n + n) + 1 := by ring
      rw [this]
      omega
    have hTsum_ge : (∑ i ∈ Finset.range (2 * n), a i) + 2 * n * n + (2 * n + 1) ≤
        ∑ v ∈ T, G.degree v := by
      rw [hTsum, show N - 2 * n = 2 * n + 1 by omega, Finset.sum_range_succ]
      have hle_sum : (∑ i ∈ Finset.range (2 * n), a i) + 2 * n * n ≤
          ∑ i ∈ Finset.range (2 * n), a (i + 2 * n) := by
        have hterm : ∀ i ∈ Finset.range (2 * n), a i + n ≤ a (i + 2 * n) := by
          intro i hi
          have hi' := Finset.mem_range.mp hi
          have := htele n i (by omega)
          omega
        calc (∑ i ∈ Finset.range (2 * n), a i) + 2 * n * n
            = ∑ i ∈ Finset.range (2 * n), (a i + n) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
          _ ≤ ∑ i ∈ Finset.range (2 * n), a (i + 2 * n) := Finset.sum_le_sum hterm
      have hlast : 2 * n + 1 ≤ a (2 * n + 2 * n) := by
        have h1 := htele (2 * n) 0 (by omega)
        rw [show 0 + 2 * (2 * n) = 2 * n + 2 * n by omega] at h1
        have h0 := ha_pos 0 (by omega)
        omega
      omega
    have hmul : 2 * n * n = 2 * (n * n) := by ring
    rw [hSsum] at hpart
    omega
  · -- Case N = 4 * n + 2
    by_cases hn0 : n = 0
    · -- Subcase N = 2 (K_2)
      have hN2eq : N = 2 := by omega
      have hdeg_all : ∀ v : α, G.degree v = 1 := by
        intro v
        have hle : G.degree v ≤ Fintype.card α - 1 := by
          have := G.degree_lt_card_verts v
          omega
        have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        have hge := h_conn.preconnected.degree_pos_of_nontrivial v
        omega
      have hbip : G.IsBipartite := by
        refine ⟨SimpleGraph.Coloring.mk (fun v => Fin.cast hN2eq (ord.symm v)) ?_⟩
        intro u v huv heq
        have : ord.symm u = ord.symm v := by
          apply Fin.ext
          have := congrArg Fin.val heq
          simpa using this
        exact G.ne_of_adj huv (ord.symm.injective this)
      have hmin1 : G.minDegree = 1 := by
        rw [hmin_eq]
        change (SimpleGraph.degreeSequence G).getD (⟨0, by omega⟩ : Fin N).1 0 = 1
        rw [← hord ⟨0, by omega⟩, hdeg_all]
      have hcomp : SimpleGraph.HasCompactdegreeSequence G := by
        intro k hk
        change k + 2 < N at hk
        omega
      exact ⟨hbip, hmin1, hcomp⟩
    · -- Subcase N = 4 * n + 2 with n ≥ 1
      have hn1 : 1 ≤ n := by omega
      obtain ⟨S, T, hdisj, hunion, hScard, hTcard, hSmem, hSsum, hTsum⟩ :=
        hsplit_setup (2 * n + 1) (by omega)
      have hTcard' : T.card = 2 * n + 1 := by omega
      have hpart := Theorem1EFSProof.sum_deg_partition G S T hdisj hunion
      have hmantel := Theorem1EFSProof.mantel_ineq_induced G h₁ T
      have hmantel_val : T.card ^ 2 / 4 = n * n + n := by
        rw [hTcard']
        have : (2 * n + 1) ^ 2 = 4 * (n * n + n) + 1 := by ring
        rw [this]
        omega
      have hTsum' : ∑ v ∈ T, G.degree v =
          a (2 * n + 1) +
            ((∑ i ∈ Finset.range (2 * n), a i) + 2 * n * (n + 1) +
              ∑ i ∈ Finset.range (2 * n), ∑ j ∈ Finset.range (n + 1), δ (i + 2 * j)) := by
        rw [hTsum, show N - (2 * n + 1) = 2 * n + 1 by omega, Finset.sum_range_succ']
        rw [zero_add, add_comm]
        congr 1
        have hterm : ∀ i ∈ Finset.range (2 * n),
            a (i + 1 + (2 * n + 1)) = a i + (n + 1) + ∑ j ∈ Finset.range (n + 1), δ (i + 2 * j) := by
          intro i hi
          have hi' := Finset.mem_range.mp hi
          have hidx : i + 1 + (2 * n + 1) = i + 2 * (n + 1) := by ring
          rw [hidx]
          exact htele (n + 1) i (by omega)
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hSsum' : ∑ v ∈ S, G.degree v = (∑ i ∈ Finset.range (2 * n), a i) + a (2 * n) := by
        rw [hSsum, Finset.sum_range_succ]
      have hmid_le : a (2 * n) ≤ a (2 * n + 1) := ha_mono (2 * n) (2 * n + 1) (by omega) (by omega)
      have hmul_eq : 2 * n * (n + 1) = 2 * (n * n + n) := by ring
      have hdiff_eq : (∑ i ∈ Finset.range (2 * n), ∑ j ∈ Finset.range (n + 1), δ (i + 2 * j)) = 0 ∧
          (G.induce (S : Set α)).edgeFinset.card = 0 ∧
          (G.induce (T : Set α)).edgeFinset.card = T.card ^ 2 / 4 := by
        rw [hTsum', hSsum'] at hpart
        omega
      obtain ⟨hδ_sum0, heS0, heT_eq⟩ := hdiff_eq
      have hδ0 : ∀ k, k + 2 < N → δ k = 0 := by
        intro k hk
        exact Theorem1EFSProof.zero_of_double_sum hδ_sum0 (by omega) (by omega) (by omega)
      obtain ⟨hbip, hSdeg⟩ := Theorem1EFSProof.bipartite_and_S_deg_of_mantel_eq G h₁ S T
        hdisj hunion (by omega) heS0 heT_eq
      have hmin1 : G.minDegree = 1 := by
        rw [hmin_eq]
        have htopS_le : a (2 * n) ≤ n + 1 := by
          have hmem : ord ⟨2 * n, by omega⟩ ∈ S := hSmem ⟨2 * n, by omega⟩ (by dsimp; omega)
          have hdeg := hSdeg _ hmem
          rw [hord ⟨2 * n, by omega⟩, hTcard'] at hdeg
          change a (2 * n) ≤ (2 * n + 1 + 1) / 2 at hdeg
          omega
        have htopS_ge : a 0 + n ≤ a (2 * n) := by
          have ht := htele n 0 (by omega)
          rw [zero_add] at ht
          omega
        have h0pos : 1 ≤ a 0 := ha_pos 0 (by omega)
        omega
      exact ⟨hbip, hmin1, hcompact_of_δ hδ0⟩
  · -- Case N = 4 * n + 3
    obtain ⟨S, T, hdisj, hunion, hScard, hTcard, _, hSsum, hTsum⟩ :=
      hsplit_setup (2 * n + 1) (by omega)
    have hTcard' : T.card = 2 * n + 2 := by omega
    have hpart := Theorem1EFSProof.sum_deg_partition G S T hdisj hunion
    have hmantel := Theorem1EFSProof.mantel_ineq_induced G h₁ T
    have hmantel_val : T.card ^ 2 / 4 = (n + 1) * (n + 1) := by
      rw [hTcard']
      have : (2 * n + 2) ^ 2 = 4 * ((n + 1) * (n + 1)) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    have hTsum' : ∑ v ∈ T, G.degree v =
        a (2 * n + 1) +
          ((∑ i ∈ Finset.range (2 * n + 1), a i) + (2 * n + 1) * (n + 1) +
            ∑ i ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1), δ (i + 2 * j)) := by
      rw [hTsum, show N - (2 * n + 1) = 2 * n + 2 by omega, Finset.sum_range_succ']
      rw [zero_add, add_comm]
      congr 1
      have hterm : ∀ i ∈ Finset.range (2 * n + 1),
          a (i + 1 + (2 * n + 1)) = a i + (n + 1) + ∑ j ∈ Finset.range (n + 1), δ (i + 2 * j) := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hidx : i + 1 + (2 * n + 1) = i + 2 * (n + 1) := by ring
        rw [hidx]
        exact htele (n + 1) i (by omega)
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, smul_eq_mul]
    have ha_mid : a (2 * n + 1) = a 1 + n + ∑ j ∈ Finset.range n, δ (1 + 2 * j) := by
      have hidx : 2 * n + 1 = 1 + 2 * n := by ring
      rw [hidx]
      exact htele n 1 (by omega)
    have h1pos : 1 ≤ a 1 := ha_pos 1 (by omega)
    have h01 : a 0 ≤ a 1 := ha_mono 0 1 (by omega) (by omega)
    have h0pos : 1 ≤ a 0 := ha_pos 0 (by omega)
    have halg : (2 * n + 1) * (n + 1) + (n + 1) = 2 * ((n + 1) * (n + 1)) := by ring
    have hdiff_eq : (∑ i ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1), δ (i + 2 * j)) = 0 ∧
        a 1 = 1 ∧
        (G.induce (S : Set α)).edgeFinset.card = 0 ∧
        (G.induce (T : Set α)).edgeFinset.card = T.card ^ 2 / 4 := by
      rw [hTsum', ha_mid, hSsum] at hpart
      omega
    obtain ⟨hδ_sum0, ha1_eq, heS0, heT_eq⟩ := hdiff_eq
    have hδ0 : ∀ k, k + 2 < N → δ k = 0 := by
      intro k hk
      exact Theorem1EFSProof.zero_of_double_sum hδ_sum0 (by omega) (by omega) (by omega)
    obtain ⟨hbip, _⟩ := Theorem1EFSProof.bipartite_and_S_deg_of_mantel_eq G h₁ S T
      hdisj hunion (by omega) heS0 heT_eq
    have hmin1 : G.minDegree = 1 := by
      rw [hmin_eq]
      omega
    exact ⟨hbip, hmin1, hcompact_of_δ hδ0⟩
