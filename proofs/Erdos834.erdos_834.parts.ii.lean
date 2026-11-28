import FormalConjectures.ErdosProblems.«834»

namespace OMA

/-- Li's nine-vertex hypergraph (arXiv:2512.24850). Each triple is paired with
a binary coloring that becomes proper when that triple is removed. -/
private def rows : List (Finset (Fin 9) × ℕ) := [
  ({0,1,2},31), ({0,1,8},60), ({0,2,7},58), ({0,3,5},59),
  ({0,3,7},203), ({0,3,8},178), ({0,4,6},91), ({0,4,7},179),
  ({0,4,8},202), ({0,5,6},30), ({1,2,5},62), ({1,2,6},94),
  ({1,3,8},53), ({1,4,8},77), ({1,5,6},29), ({2,3,7},51),
  ({2,4,7},75), ({2,5,6},27), ({3,5,7},186), ({3,5,8},195),
  ({4,6,7},218), ({4,6,8},163)]

private def LiH : Finset (Finset (Fin 9)) := (rows.map Prod.fst).toFinset

private def color (mask : ℕ) (vertex : Fin 9) : Fin 2 :=
  if mask.testBit vertex.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edges_colorable : ∀ e ∈ LiH, (LiH.erase e).HypergraphColorable 2 := by
  have certificates : ∀ p ∈ rows, (LiH.erase p.1).IsProperHypergraphColoring (color p.2) := by
    unfold Finset.IsProperHypergraphColoring
    decide +kernel
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  exact ⟨_,certificates p hp⟩

end OMA

open OMA in
theorem OMA.solution : type_of% @Erdos834.erdos_834.parts.ii := by
  have degree : ∀ v : Fin 9, 7 ≤ LiH.hypergraphDegree v := by
    unfold Finset.hypergraphDegree
    decide +kernel
  refine ⟨9,LiH,?_,⟨?_,?_⟩,edges_colorable,?_,degree⟩
  · unfold Finset.IsUniform
    decide +kernel
  · exact ⟨![0,0,1,0,0,1,2,1,1],by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · have no : ¬LiH.HypergraphColorable 2 := by
      unfold Finset.HypergraphColorable Finset.IsProperHypergraphColoring
      decide +kernel
    rintro k hk ⟨c,pc⟩
    let embed (x : Fin k) : Fin 2 := ⟨x.val,by have := x.isLt; omega⟩
    apply no
    refine ⟨embed ∘ c,?_⟩
    intro e he
    obtain ⟨x,hx,y,hy,diff⟩ := pc e he
    exact ⟨x,hx,y,hy,fun eq => diff (Fin.ext (congrArg (fun z : Fin 2 => z.val) eq))⟩
  · intro v
    have positive : 0 < (LiH.filter (fun e => v ∈ e)).card := by
      have h := degree v
      change 7 ≤ (LiH.filter (fun e => v ∈ e)).card at h
      omega
    obtain ⟨e,he,hv⟩ := Finset.filter_nonempty_iff.mp (Finset.card_pos.mp positive)
    obtain ⟨c,works⟩ := edges_colorable e he
    refine ⟨c,fun f hf => works f ?_⟩
    obtain ⟨member,apart⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_erase.mpr ⟨fun eq => apart (eq ▸ hv),member⟩
