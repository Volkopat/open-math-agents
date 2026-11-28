import FormalConjectures.Paper.DegreeSequencesTriangleFree

/-!
# A bipartite graph with degree multiplicity three

Each side is divided into four equal blocks. The diagonal blocks have triangular adjacency.
Complete off-diagonal blocks place the eight blocks into three disjoint degree intervals.
-/

namespace OMA

open SimpleGraph Finset

def blockAdj {n : ℕ} (left right : Fin 4 × Fin n) : Prop :=
  (left.1 = right.1 ∧ left.2.rev ≤ right.2) ∨
  (left.1 = 2 ∧ right.1 ≠ 2) ∨
  (left.1 = 3 ∧ right.1 ≠ 3) ∨
  (left.1 < 2 ∧ right.1 = 3)

def blockGraph (n : ℕ) : SimpleGraph ((Fin 4 × Fin n) ⊕ (Fin 4 × Fin n)) where
  Adj
    | .inl u, .inr v => blockAdj u v
    | .inr v, .inl u => blockAdj u v
    | _, _ => False
  symm := by
    constructor
    intro u v h
    cases u <;> cases v <;> exact h
  loopless := by
    constructor
    intro u
    cases u <;> exact id

lemma card_ge_index {n : ℕ} (i : Fin n) :
    (univ.filter fun j : Fin n ↦ i ≤ j).card = n - (i : ℕ) := by
  simpa only [filter_le_eq_Ici] using Fin.card_Ici i

def leftBase (b : Fin 4) : ℕ :=
  if b < 2 then 1 else 3

def rightBase (b : Fin 4) : ℕ :=
  if b < 2 then 2 else if b = 2 then 1 else 3

lemma degree_as_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    G.degree i = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold SimpleGraph.degree neighborFinset neighborSet
  rw [Finset.sum_boole, Set.toFinset_ofPred]
  simp

lemma blockGraph_degree_left {n : ℕ} [DecidableRel (blockGraph n).Adj]
    (b : Fin 4) (i : Fin n) :
    (blockGraph n).degree (.inl (b, i)) = leftBase b * n + (i : ℕ) + 1 := by
  rw [degree_as_sum (blockGraph n), Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases b <;>
    simp [Fin.sum_univ_four, blockGraph, blockAdj, leftBase, card_ge_index, Fin.val_rev] <;> omega

lemma blockGraph_degree_right {n : ℕ} [DecidableRel (blockGraph n).Adj]
    (b : Fin 4) (i : Fin n) :
    (blockGraph n).degree (.inr (b, i)) = rightBase b * n + (i : ℕ) + 1 := by
  have h (j : Fin n) : j.rev ≤ i ↔ i.rev ≤ j := Fin.rev_le_iff
  rw [degree_as_sum (blockGraph n), Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  fin_cases b <;>
    simp [Fin.sum_univ_four, blockGraph, blockAdj, rightBase, h, card_ge_index, Fin.val_rev] <;> omega

lemma blockGraph_bipartite (n : ℕ) : (blockGraph n).IsBipartite := by
  refine isBipartite_iff_exists_isBipartiteWith.mpr
    ⟨Set.range Sum.inl, Set.range Sum.inr, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, h⟩
    cases h
  · intro x y h
    cases x <;> cases y <;> simp_all [blockGraph]

lemma sum_degree_interval (n base d : ℕ) :
    (∑ i : Fin n, if base + (i : ℕ) + 1 = d then 1 else 0) =
      if base < d ∧ d ≤ base + n then 1 else 0 := by
  rw [Fintype.sum_ite_eq_ite_exists _ (by
    intro i j hi hj
    exact Fin.ext (by omega))]
  have range : (∃ i : Fin n, base + (i : ℕ) + 1 = d) ↔ base < d ∧ d ≤ base + n := by
    constructor
    · rintro ⟨i, hi⟩
      have := i.isLt
      omega
    · intro h
      exact ⟨⟨d - base - 1, by omega⟩, by dsimp; omega⟩
  simp only [range]

lemma blockGraph_count {n : ℕ} [DecidableRel (blockGraph n).Adj] (d : ℕ) :
    countDegreeK (blockGraph n) d =
      (if n < d ∧ d ≤ n + n then 3 else 0) +
      (if 2 * n < d ∧ d ≤ 2 * n + n then 2 else 0) +
      (if 3 * n < d ∧ d ≤ 3 * n + n then 3 else 0) := by
  unfold countDegreeK
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [blockGraph_degree_left, blockGraph_degree_right, sum_degree_interval,
    Fin.sum_univ_four, leftBase, rightBase]
  norm_num
  split_ifs <;> omega

lemma multiplicity_eq_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : countDegreeK G d = 3) (hBound : ∀ e, countDegreeK G e ≤ 3) :
    degreeSequenceMultiplicity G = 3 := by
  let ds := degreeSequence G
  have hCount (e : ℕ) : ds.count e = countDegreeK G e := by
    simp [ds, degreeSequence, ← Multiset.coe_count, Multiset.count_map,
      countDegreeK, ← Finset.filter_val, Finset.card_val, eq_comm]
  have hdMem : d ∈ ds := List.count_pos_iff.mp (by rw [hCount, hd]; decide)
  have hMax : (ds.map (fun e ↦ ds.count e)).max? = some 3 := by
    refine List.max?_eq_some_iff.mpr ⟨List.mem_map.mpr ⟨d, hdMem, (hCount d).trans hd⟩, ?_⟩
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    simpa [hCount] using hBound a
  change ((ds.map (fun e ↦ ds.count e)).max?).getD 0 = 3
  simp [hMax]

end OMA

open SimpleGraph Finset

theorem OMA.solution : type_of% @SimpleGraph.lemma3 := by
  classical
  intro n hn
  let V := (Fin 4 × Fin n) ⊕ (Fin 4 × Fin n)
  let e : Fin (8 * n) ≃ V := Fintype.equivOfCardEq (by simp [V]; omega)
  let G := (OMA.blockGraph n).comap e
  let hDec : DecidableRel G.Adj := Classical.decRel _
  let hBlockDec : DecidableRel (OMA.blockGraph n).Adj := Classical.decRel _
  have hDegree (v : Fin (8 * n)) : G.degree v = (OMA.blockGraph n).degree (e v) :=
    ((Iso.comap e (OMA.blockGraph n)).degree_eq v).symm

  have hCount (d : ℕ) : countDegreeK G d = countDegreeK (OMA.blockGraph n) d := by
    simp only [countDegreeK, Finset.card_filter]
    apply Fintype.sum_equiv e
    intro v
    simp [hDegree]
  refine ⟨G, hDec, ?_, ?_, ?_⟩
  · exact (OMA.blockGraph_bipartite n).of_hom ⟨e, fun h ↦ h⟩
  · let : Nonempty (Fin (8 * n)) := ⟨⟨0, by omega⟩⟩
    let first : V := .inl (0, ⟨0, hn⟩)
    refine le_antisymm ((G.minDegree_le_degree (e.symm first)).trans ?_)
      (G.le_minDegree_of_forall_le_degree _ ?_)
    · rw [hDegree, e.apply_symm_apply]
      simp [first, OMA.blockGraph_degree_left, OMA.leftBase]
    · intro v
      rw [hDegree]
      rcases e v with ⟨b, i⟩ | ⟨b, i⟩ <;>
        simp only [OMA.blockGraph_degree_left, OMA.blockGraph_degree_right,
          OMA.leftBase, OMA.rightBase] <;>
        split_ifs <;> omega
  · refine OMA.multiplicity_eq_three G (d := n + 1) ?_ ?_
    · rw [hCount, OMA.blockGraph_count]
      split_ifs <;> omega
    · intro d
      rw [hCount, OMA.blockGraph_count]
      split_ifs <;> omega
