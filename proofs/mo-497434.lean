import OMAStatements.S_mo_497434

/-!
Expand one endpoint of each chord of a nine-cycle of the Petersen graph into a
triangle. The new cycle is on vertices 0 through 11. The three remaining
triangle vertices and the omitted Petersen vertex form an independent set.
-/
namespace OMA.MO497434

open SimpleGraph Finset

private abbrev Vertex := Fin 16
private abbrev Edge := Vertex × Vertex

private def neighbors : Vertex → List Vertex :=
  ![[1, 11, 12], [0, 2, 13], [1, 3, 13], [2, 4, 14], [3, 5, 14], [4, 6, 12],
    [5, 7, 15], [6, 8, 13], [7, 9, 12], [8, 10, 14], [9, 11, 15], [0, 10, 15],
    [0, 5, 8], [1, 2, 7], [3, 4, 9], [6, 10, 11]]

private def graph : SimpleGraph Vertex where
  Adj a b := b ∈ neighbors a
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel graph.Adj :=
  fun a b => inferInstanceAs (Decidable (b ∈ neighbors a))

private theorem cubic (v : Vertex) : (graph.neighborSet v).ncard = 3 := by
  have hset : graph.neighborSet v = ↑(neighbors v).toFinset := by ext w; simp [graph]
  have hcard : ∀ w : Vertex, (neighbors w).toFinset.card = 3 := by decide
  rw [hset, Set.ncard_coe_finset, hcard]

private def outside (a b : Option Vertex) (v : Vertex) : Prop :=
  some v ≠ a ∧ some v ≠ b

private instance (a b : Option Vertex) (v : Vertex) : Decidable (outside a b v) :=
  inferInstanceAs (Decidable (some v ≠ a ∧ some v ≠ b))

private def pivot (a b : Option Vertex) : Vertex :=
  if outside a b 0 then 0 else if outside a b 1 then 1 else 2

private theorem pivot_outside : ∀ a b, outside a b (pivot a b) := by decide

private def liftVertex (a b : Option Vertex) (v : Vertex) (h : outside a b v) :
    {v : Vertex // outside a b v} := ⟨v, h⟩

private def spread (a b : Option Vertex) (seen : List Vertex) : List Vertex :=
  (List.finRange 16).filter fun v =>
    decide (outside a b v) && (seen.contains v || (neighbors v).any seen.contains)

private def visited (a b : Option Vertex) : ℕ → List Vertex
  | 0 => [pivot a b]
  | n + 1 => spread a b (visited a b n)

private theorem reachable_visited (a b : Option Vertex) (n : ℕ) (v : Vertex)
    (hv : v ∈ visited a b n) :
    ∃ h : outside a b v,
      (graph.induce (outside a b)).Reachable (liftVertex a b _ (pivot_outside a b))
        (liftVertex a b v h) := by
  induction n generalizing v with
  | zero =>
    have heq : v = pivot a b := by simpa [visited] using hv
    subst v
    exact ⟨pivot_outside a b, Reachable.rfl⟩
  | succ n ih =>
    rw [visited, spread, List.mem_filter] at hv
    obtain ⟨hout, hfind⟩ := Bool.and_eq_true_iff.mp hv.2
    have ho : outside a b v := of_decide_eq_true hout
    rcases Bool.or_eq_true_iff.mp hfind with hold | hadj
    · obtain ⟨_, hp⟩ := ih v (List.contains_iff_mem.mp hold)
      exact ⟨ho, hp⟩
    · obtain ⟨w, hw, hwvis⟩ := List.any_eq_true.mp hadj
      obtain ⟨hwout, hp⟩ := ih w (List.contains_iff_mem.mp hwvis)
      have hstep : (graph.induce (outside a b)).Adj
          (liftVertex a b w hwout) (liftVertex a b v ho) :=
        (show graph.Adj v w from hw).symm
      exact ⟨ho, hp.trans hstep.reachable⟩

set_option maxHeartbeats 1000000 in
private theorem visited_all : ∀ a b : Option Vertex, ∀ v : Vertex,
    outside a b v → v ∈ visited a b 6 := by decide

private theorem deletion (a b : Option Vertex) : (graph.induce (outside a b)).Connected := by
  let p := liftVertex a b _ (pivot_outside a b)
  refine { preconnected := ?_, nonempty := ⟨p⟩ }
  intro x y
  obtain ⟨_, hx⟩ := reachable_visited a b 6 x.val (visited_all a b x.val x.property)
  obtain ⟨_, hy⟩ := reachable_visited a b 6 y.val (visited_all a b y.val y.property)
  exact hx.symm.trans hy

private theorem graph_connected (S : Finset Vertex) (hS : S.card < 3) :
    (graph.induce {v | v ∉ S}).Connected := by
  have hrepr : ∃ a b : Option Vertex, {v | v ∉ S} = outside a b := by
    rcases (show S.card = 0 ∨ S.card = 1 ∨ S.card = 2 by omega) with h | h | h
    · have he := card_eq_zero.mp h
      subst S
      exact ⟨none, none, by ext v; change (v ∉ ∅ ↔ outside none none v); simp [outside]⟩
    · obtain ⟨a, rfl⟩ := card_eq_one.mp h
      exact ⟨some a, none, by ext v; change (v ∉ {a} ↔ outside (some a) none v); simp [outside]⟩
    · obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp h
      refine ⟨some a, some b, ?_⟩
      ext v
      change v ∉ ({a, b} : Finset Vertex) ↔ outside (some a) (some b) v
      simp [outside]
  obtain ⟨a, b, heq⟩ := hrepr
  rw [heq]
  exact deletion a b

private def orderedEdges : List Edge :=
  [(0, 1), (0, 11), (0, 12), (1, 2), (1, 13), (2, 13), (2, 3), (7, 13),
    (3, 4), (3, 14), (4, 14), (4, 5), (5, 12), (5, 6), (6, 7), (6, 15),
    (7, 8), (8, 12), (8, 9), (9, 14), (9, 10), (10, 11), (10, 15), (11, 15)]

private def edgeOf (e : Edge) : Sym2 Vertex := s(e.1, e.2)

private def touches (e f : Edge) : Bool :=
  e.1 == f.1 || e.1 == f.2 || e.2 == f.1 || e.2 == f.2

private theorem touches_sound {e f : Edge} (h : touches e f = true) :
    ∃ v, v ∈ edgeOf e ∧ v ∈ edgeOf f := by
  simp only [touches, Bool.or_eq_true_iff, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact ⟨e.1, Sym2.mem_iff.mpr (.inl rfl), Sym2.mem_iff.mpr (.inl h)⟩
  · exact ⟨e.1, Sym2.mem_iff.mpr (.inl rfl), Sym2.mem_iff.mpr (.inr h)⟩
  · exact ⟨e.2, Sym2.mem_iff.mpr (.inr rfl), Sym2.mem_iff.mpr (.inl h)⟩
  · exact ⟨e.2, Sym2.mem_iff.mpr (.inr rfl), Sym2.mem_iff.mpr (.inr h)⟩

private def searchColor : List Edge → List (Edge × Fin 3) → Bool
  | [], _ => true
  | e :: rest, used =>
      (List.finRange 3).any fun k =>
        used.all (fun (f, j) => !(touches f e) || j != k) &&
          searchColor rest ((e, k) :: used)

private def colorCompatible (color : Edge → Fin 3) (e f : Edge) : Prop :=
  touches e f = true → color e ≠ color f

private theorem search_complete (color : Edge → Fin 3) (todo used : List Edge)
    (ht : todo.Pairwise (colorCompatible color))
    (hu : ∀ f ∈ used, ∀ e ∈ todo, colorCompatible color f e) :
    searchColor todo (used.map fun e => (e, color e)) = true := by
  induction todo generalizing used with
  | nil => rfl
  | cons e rest ih =>
    change (List.finRange 3).any _ = true
    apply List.any_eq_true.mpr
    refine ⟨color e, List.mem_finRange _, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · apply List.all_eq_true.mpr
      intro pair hp
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
      cases he : touches f e with
      | false => simp [he]
      | true =>
        have hne := hu f hf e (List.mem_cons_self) he
        simp [he, hne]
    · change searchColor rest ((e :: used).map fun f => (f, color f)) = true
      apply ih _ (List.pairwise_cons.mp ht).2
      intro f hf g hg
      rcases List.mem_cons.mp hf with rfl | hf
      · exact (List.pairwise_cons.mp ht).1 g hg
      · exact hu f hf g (List.mem_cons_of_mem _ hg)

private theorem edge_list_valid :
    orderedEdges.Pairwise fun e f =>
      graph.Adj e.1 e.2 ∧ graph.Adj f.1 f.2 ∧ edgeOf e ≠ edgeOf f := by decide

set_option maxHeartbeats 1000000 in
private theorem search_failed : searchColor orderedEdges [] = false := by decide

private theorem not_three_colorable :
    ¬ ∃ c : Sym2 Vertex → Fin 3, ∀ e ∈ graph.edgeSet, ∀ f ∈ graph.edgeSet,
        e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → c e ≠ c f := by
  rintro ⟨c, hc⟩
  have hpair : orderedEdges.Pairwise (colorCompatible (c ∘ edgeOf)) :=
    edge_list_valid.imp (fun ⟨he, hf, hne⟩ ht =>
      hc _ ((graph.mem_edgeSet).mpr he) _ ((graph.mem_edgeSet).mpr hf) hne (touches_sound ht))
  have hsearch := search_complete (c ∘ edgeOf) orderedEdges [] hpair (by simp)
  rw [List.map_nil, search_failed] at hsearch
  contradiction

private def cycle : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 1 by decide) <|
  .cons (show graph.Adj 1 2 by decide) <|
  .cons (show graph.Adj 2 3 by decide) <|
  .cons (show graph.Adj 3 4 by decide) <|
  .cons (show graph.Adj 4 5 by decide) <|
  .cons (show graph.Adj 5 6 by decide) <|
  .cons (show graph.Adj 6 7 by decide) <|
  .cons (show graph.Adj 7 8 by decide) <|
  .cons (show graph.Adj 8 9 by decide) <|
  .cons (show graph.Adj 9 10 by decide) <|
  .cons (show graph.Adj 10 11 by decide) <|
  .cons (show graph.Adj 11 0 by decide) .nil

private theorem cycle_valid : cycle.IsCycle := by
  refine ⟨⟨⟨by decide⟩, ?_⟩, by decide⟩
  intro h
  have hlen := congrArg Walk.length h
  exact (by decide : cycle.length ≠ (Walk.nil : graph.Walk 0 0).length) hlen

private theorem chordless : ∀ a b : Vertex, a ∈ cycle.support → b ∈ cycle.support →
    graph.Adj a b → s(a, b) ∈ cycle.edges := by decide

private theorem independent : ∀ a b : Vertex, a ∉ cycle.support → b ∉ cycle.support →
    ¬ graph.Adj a b := by decide

theorem solution : type_of% @OMA.S_mo_497434.main := by
  exact ⟨16, graph, cubic, ⟨by decide, graph_connected⟩,
    not_three_colorable, 0, cycle, cycle_valid, chordless, independent⟩

end OMA.MO497434

theorem OMA.solution : type_of% @OMA.S_mo_497434.main := OMA.MO497434.solution
