import FormalConjectures.WrittenOnTheWallII.GraphConjecture91

/-! Two squares and a four-clique joined in a chain give a counterexample. -/

open SimpleGraph Finset

universe u

namespace OMA.Squares

abbrev V := ULift.{u} (Fin 12)

def edges : List (Fin 12 × Fin 12) :=
  [(0,1),(1,2),(2,3),(3,0),(3,4),(4,5),(5,6),(6,7),(7,4),(7,8),
   (8,9),(8,10),(8,11),(9,10),(9,11),(10,11)]

def graph : SimpleGraph V.{u} where
  Adj x y := (x.down,y.down) ∈ edges ∨ (y.down,x.down) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.{u}.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma connected : graph.{u}.Connected := by
  have step : ∀ i : Fin 11, graph.{0}.Adj ⟨i.castSucc⟩ ⟨i.succ⟩ := by decide
  have reach (i : Fin 12) : graph.{u}.Reachable ⟨0⟩ ⟨i⟩ := by
    induction i using Fin.induction with
    | zero => exact .rfl
    | succ i ih => exact ih.trans (show graph.{u}.Adj _ _ from step i).reachable
  exact ⟨fun x y => (reach x.down).symm.trans (reach y.down)⟩


def ten : Finset V.{u} := Finset.univ.filter fun v => v.down.val < 10

lemma bip_lower : 10 ≤ b graph.{u} := by
  have hb : (graph.induce (ten.{u} : Set V)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring graph ten).mpr
    refine ⟨fun v => (Fin.ofNat 2 v.down.val), ?_⟩
    decide
  have h : 10 ≤ graph.{u}.largestInducedBipartiteSubgraphSize := by
    unfold largestInducedBipartiteSubgraphSize
    apply le_csSup
    · exact ⟨12, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨ten, hb, by decide⟩
  unfold b
  exact_mod_cast h

def square : Fin 2 → Fin 4 → Fin 12 := ![![0,1,2,3], ![4,5,6,7]]

lemma no_cycle {n : ℕ} {s : Finset V.{u}} (ha : (graph.induce (s : Set V)).IsAcyclic)
    (hn : 3 ≤ n) (f : Fin n → Fin 12) (hf : Function.Injective f)
    (he : ∀ i j, (cycleGraph n).Adj i j → graph.{0}.Adj (ULift.up (f i)) (ULift.up (f j))) :
    ¬ ∀ i, ULift.up (f i) ∈ s := by
  intro allIn
  apply isAcyclic_iff_free_cycleGraph.mp ha n hn
  let g : Fin n → ↥(s : Set V) := fun i => ⟨ULift.up (f i), allIn i⟩
  exact ⟨⟨⟨g, fun {i j} h => he i j h⟩,
    fun i j h => hf (congrArg (fun x : ↥(s : Set V) => x.val.down) h)⟩⟩

def block : Fin 3 → Finset (Fin 12) := ![{0,1,2,3},{4,5,6,7},{8,9,10,11}]

lemma forest_upper : graph.{u}.largestInducedForestSize ≤ 8 := by
  unfold largestInducedForestSize
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    apply isAcyclic_iff_free_cycleGraph.mpr
    rintro n hn ⟨f⟩
    exact Finset.notMem_empty _ (f ⟨0, by omega⟩).property
  · rintro k ⟨s, hs, rfl⟩
    let t := s.map Equiv.ulift.toEmbedding
    let piece (j : Fin 3) := t ∩ block j
    have back {x} (hx : x ∈ t) : ULift.up x ∈ s := mem_map_equiv.mp hx
    have sqCap (k : Fin 2) : (piece k.castSucc).card ≤ 3 := by
      by_contra! h
      have e : piece k.castSucc = block k.castSucc := eq_of_subset_of_card_le inter_subset_right (by
        rw [(by decide : ∀ k : Fin 2, (block k.castSucc).card = 4) k]
        exact h)
      exact no_cycle hs (by decide) (square k)
        ((by decide +kernel : ∀ k, Function.Injective (square k)) k)
        ((by decide +kernel : ∀ k i j, (cycleGraph 4).Adj i j →
          graph.{0}.Adj ⟨square k i⟩ ⟨square k j⟩) k) fun i =>
        back (mem_inter.mp (e.symm ▸ (by decide : ∀ (k : Fin 2) i, square k i ∈ block k.castSucc) k i)).1
    have : (piece 2).card ≤ 2 := by
      by_contra! h
      obtain ⟨r, hr, hr3⟩ := exists_subset_card_eq h
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hr3
      let f : Fin 3 → Fin 12 := ![a,b,c]
      have hinj : Function.Injective f := by
        intro i j e
        fin_cases i <;> fin_cases j <;> simp_all [f]
      have hin (i : Fin 3) : f i ∈ piece 2 := hr (by fin_cases i <;> simp [f])
      have hadj : ∀ x ∈ block 2, ∀ y ∈ block 2, x ≠ y → graph.{0}.Adj ⟨x⟩ ⟨y⟩ := by decide
      exact no_cycle hs (by decide) f hinj (fun i j e => hadj _ (mem_inter.mp (hin i)).2
        _ (mem_inter.mp (hin j)).2 (hinj.ne e.ne)) fun i => back (mem_inter.mp (hin i)).1
    have ht : t ⊆ piece 0 ∪ piece 1 ∪ piece 2 := by
      intro x hx
      have h := (by decide : ∀ x, x ∈ block 0 ∨ x ∈ block 1 ∨ x ∈ block 2) x
      simpa [piece, hx, or_assoc] using h
    have : t.card = s.card := card_map _
    have : (piece 0).card ≤ 3 := sqCap 0
    have : (piece 1).card ≤ 3 := sqCap 1
    have := card_le_card ht
    have := card_union_le (piece 0) (piece 1)
    have := card_union_le (piece 0 ∪ piece 1) (piece 2)
    omega


def weight (v : V.{u}) : ℕ := ![2,2,2,3,3,2,2,3,2,1,1,1] v.down

lemma avg_upper : l graph.{u} ≤ 2 := by
  have bound (v : V.{u}) : indepNeighborsCard graph v ≤ weight v := by
    unfold indepNeighborsCard
    rw [indep_num_eq_computable]
    exact (by decide : ∀ w : V, (graph.induce (graph.neighborSet w)).computable_indep_num ≤ weight w) v
  have hs : ∑ v : V.{u}, indepNeighborsCard graph v ≤ 24 :=
    (Finset.sum_le_sum (fun v _ => bound v)).trans (by decide)
  unfold l averageIndepNeighbors indepNeighbors
  rw [← Nat.cast_sum]
  have hs' : (↑(∑ v : V.{u}, indepNeighborsCard graph v) : ℝ) ≤ 24 := by exact_mod_cast hs
  change (↑(∑ v : V.{u}, indepNeighborsCard graph v) : ℝ) / 12 ≤ 2
  linarith

end OMA.Squares

open OMA.Squares

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture91.conjecture91 := by
  intro allGraphs
  have claim := allGraphs graph connected
  have hc : ⌈l graph⌉ ≤ 2 := Int.ceil_le.mpr (by simpa using avg_upper)
  have hf : (graph.largestInducedForestSize : ℝ) ≤ 8 := by exact_mod_cast forest_upper
  have hm := mul_le_mul_of_nonneg_left (show (⌈l graph⌉ : ℝ) ≤ 2 by exact_mod_cast hc)
    (Nat.cast_nonneg graph.largestInducedForestSize : (0 : ℝ) ≤ _)
  linarith [bip_lower]
