import OMAStatements.S_mo_346399
import Mathlib

open SimpleGraph

namespace MatchingCycle

private abbrev Vertex := Fin 12
private def partner : Vertex → Vertex := ![2, 3, 0, 1, 6, 11, 4, 9, 10, 7, 8, 5]
private def other : Vertex → Vertex := ![3, 4, 6, 0, 1, 9, 2, 10, 11, 5, 7, 8]
private def neighbors (v : Vertex) : List Vertex := [v + 1, v + 11, partner v, other v]

private theorem adjSymm : ∀ v w : Vertex, w ∈ neighbors v → v ∈ neighbors w := by decide +kernel
private theorem adjIrrefl : ∀ v : Vertex, v ∉ neighbors v := by decide +kernel
private theorem partnerSymm : ∀ v w : Vertex, partner v = w → partner w = v := by decide +kernel
private theorem otherSymm : ∀ v w : Vertex, other v = w → other w = v := by decide +kernel

private def graph : SimpleGraph Vertex where
  Adj v w := w ∈ neighbors v
  symm := ⟨fun {v w} => adjSymm v w⟩
  loopless := ⟨adjIrrefl⟩

private instance graphAdjDecidable : DecidableRel graph.Adj :=
  fun v w => inferInstanceAs (Decidable (w ∈ neighbors v))

private def requiredMatching : graph.Subgraph where
  verts := Set.univ
  Adj v w := partner v = w
  adj_sub := by intro v w h; change w ∈ neighbors v; simp [neighbors, ← h]
  edge_vert := by simp
  symm := ⟨fun {v w} => partnerSymm v w⟩

private def otherMatching : graph.Subgraph where
  verts := Set.univ
  Adj v w := other v = w
  adj_sub := by intro v w h; change w ∈ neighbors v; simp [neighbors, ← h]
  edge_vert := by simp
  symm := ⟨fun {v w} => otherSymm v w⟩

private theorem requiredPerfect : requiredMatching.IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  exact ⟨partner v, rfl, fun _ h => Eq.symm h⟩

private theorem otherPerfect : otherMatching.IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  exact ⟨other v, rfl, fun _ h => Eq.symm h⟩

private def cycle : graph.Walk 0 0 :=
  .cons (v := 1) (by decide +kernel) (
  .cons (v := 2) (by decide +kernel) (
  .cons (v := 3) (by decide +kernel) (
  .cons (v := 4) (by decide +kernel) (
  .cons (v := 5) (by decide +kernel) (
  .cons (v := 6) (by decide +kernel) (
  .cons (v := 7) (by decide +kernel) (
  .cons (v := 8) (by decide +kernel) (
  .cons (v := 9) (by decide +kernel) (
  .cons (v := 10) (by decide +kernel) (
  .cons (v := 11) (by decide +kernel) (
  .cons (v := 0) (by decide +kernel) .nil)))))))))))

private theorem cycleHamiltonian : cycle.IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq, Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨⟨by decide +kernel, ?_, by decide +kernel⟩, by decide +kernel⟩
  intro h
  have hlen := congrArg Walk.length h
  exact (show cycle.length ≠ (Walk.nil : graph.Walk 0 0).length from by decide +kernel) hlen

private theorem matchingDisjoint : Disjoint requiredMatching.edgeSet otherMatching.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e
  refine e.inductionOn ?_
  change ∀ v w : Vertex, partner v = w → other v = w → False
  decide +kernel

private theorem matchingUnion : requiredMatching.edgeSet ∪ otherMatching.edgeSet =
    graph.edgeSet \ {e | e ∈ cycle.edges} := by
  ext e
  refine e.inductionOn ?_
  change ∀ v w : Vertex, (partner v = w ∨ other v = w) ↔
    (w ∈ neighbors v ∧ s(v,w) ∉ cycle.edges)
  decide +kernel

private def insertVertex (mask : ℕ) (v : Vertex) : ℕ := mask ||| 2 ^ v.val

private def addRequired (mask : ℕ) (v w : Vertex) : ℕ :=
  if partner v = w then insertVertex (insertVertex mask v) w else mask

private theorem addRequiredPreserves (mask : ℕ) (v w i : Vertex)
    (hi : mask.testBit i.val = true) : (addRequired mask v w).testBit i.val = true := by
  by_cases h : partner v = w <;> simp [addRequired, insertVertex, h, hi]

private theorem addRequiredSets (mask : ℕ) (v w i : Vertex)
    (he : s(i, partner i) = s(v, w)) : (addRequired mask v w).testBit i.val = true := by
  rcases Sym2.eq_iff.mp he with ⟨hv, hw⟩ | ⟨hw, hv⟩
  · have hp : partner v = w := hv ▸ hw
    simp [addRequired, insertVertex, hp, hv, Nat.testBit_two_pow_self]
  · have hp : partner v = w := (partnerSymm i v hv).trans hw
    simp [addRequired, insertVertex, hp, hw, Nat.testBit_two_pow_self]

private def search (target : Vertex) : ℕ → Vertex → ℕ → ℕ → Bool
  | 0, v, _, matched => (v == target) && (List.finRange 12).all (fun i => matched.testBit i.val)
  | steps + 1, v, visited, matched => (neighbors v).any fun w =>
      if visited.testBit w.val then false else
        search target steps w (insertVertex visited w) (addRequired matched v w)

private theorem searchComplete {v target : Vertex} (walk : graph.Walk v target)
    (visited matched : ℕ) (hnodup : walk.support.tail.Nodup)
    (hfresh : ∀ w ∈ walk.support.tail, visited.testBit w.val = false)
    (hpairs : ∀ i : Vertex, s(i, partner i) ∈ walk.edges ∨ matched.testBit i.val = true) :
    search target walk.length v visited matched = true := by
  induction walk generalizing visited matched with
  | nil =>
    simp [search, List.all_eq_true] at *
    exact hpairs
  | @cons v w target h walk ih =>
    rw [Walk.support_cons, List.tail_cons, ← Walk.cons_tail_support walk] at hnodup hfresh
    have hnot := hfresh w (List.mem_cons_self ..)
    have hchild := ih (insertVertex visited w) (addRequired matched v w)
      (List.nodup_cons.mp hnodup).2
      (by
        intro k hk
        have hne : w.val ≠ k.val := fun he => (List.nodup_cons.mp hnodup).1 ((Fin.ext he).symm ▸ hk)
        have hprev := hfresh k (List.mem_cons_of_mem _ hk)
        simp [insertVertex, hprev, Nat.testBit_two_pow_of_ne hne])
      (by
        intro i
        have hi := hpairs i
        simp only [Walk.edges_cons, List.mem_cons] at hi
        rcases hi with (he | ht) | hm
        · exact Or.inr (addRequiredSets matched v w i he)
        · exact Or.inl ht
        · exact Or.inr (addRequiredPreserves matched v w i hm))
    rw [Walk.length_cons, search]
    exact List.any_eq_true.mpr ⟨w, h, by simp [hnot, hchild]⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem startOne : search 0 11 1 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem startEleven : search 0 11 11 2048 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem startTwo : search 0 11 2 4 5 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem startThree : search 0 11 3 8 0 = false := by decide +kernel

private theorem noClosedWalk : search 0 12 0 0 0 = false := by
  change (search 0 11 1 2 0 || (search 0 11 11 2048 0 ||
    (search 0 11 2 4 5 || (search 0 11 3 8 0 || false)))) = false
  rw [startOne, startEleven, startTwo, startThree]
  rfl

private theorem noHamiltonianContaining : ¬ ∃ v, ∃ walk : graph.Walk v v,
    walk.IsHamiltonianCycle ∧ requiredMatching.edgeSet ⊆ {e | e ∈ walk.edges} := by
  rintro ⟨v, walk, hham, hcontained⟩
  have hzero : 0 ∈ walk.support := hham.mem_support 0
  let rotated := walk.rotate 0 hzero
  have hrot : rotated.IsHamiltonianCycle := hham.rotate hzero
  have hlength : rotated.length = 12 := by simpa using hrot.length_eq
  have hpairs : ∀ i : Vertex, s(i, partner i) ∈ rotated.edges ∨ (0 : ℕ).testBit i.val = true := by
    intro i
    have horig : s(i, partner i) ∈ walk.edges :=
      hcontained (show s(i, partner i) ∈ requiredMatching.edgeSet from rfl)
    exact Or.inl ((walk.rotate_edges 0 hzero).perm.mem_iff.mpr horig)
  have hsearch := searchComplete rotated 0 0 hrot.isCycle.support_nodup (by simp) hpairs
  rw [hlength, noClosedWalk] at hsearch
  cases hsearch

end MatchingCycle

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_346399.main) := by
  intro h
  exact MatchingCycle.noHamiltonianContaining
    (h MatchingCycle.Vertex MatchingCycle.graph 0 MatchingCycle.cycle
      MatchingCycle.requiredMatching MatchingCycle.otherMatching MatchingCycle.cycleHamiltonian
      MatchingCycle.requiredPerfect MatchingCycle.otherPerfect MatchingCycle.matchingDisjoint
      MatchingCycle.matchingUnion)