import OMAReductions.R_mse_1688329_R1

-- Step mse-1688329.R1.H1: hypothesis H1 of reduction mse-1688329.R1
-- Credit: @Ciphore
-- Dirac-dense graphs of minimum degree at least 3 contain a 4-cycle:
-- a non-adjacent pair has two common neighbours by inclusion-exclusion,
-- and in the complete case any four vertices form a 4-cycle.

open OMA.S_mse_1688329

/-- Closing a path of length at least 2 by its missing edge gives a cycle. -/
lemma cycle_of_path {V : Type} [DecidableEq V] {K : SimpleGraph V} [DecidableRel K.Adj]
    {a b : V} (p : K.Walk b a) (h : K.Adj a b) (hp : p.IsPath)
    (hl : 2 ≤ p.length) : (SimpleGraph.Walk.cons h p).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hp, fun he => ?_⟩
  cases p with
  | nil => simp at hl
  | cons h' p' =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 h.ne
      subst h1
      cases p' with
      | nil => simp at hl
      | cons h'' p'' =>
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        exact hp.1.2 p''.end_mem_support
    · exact hp.2 (SimpleGraph.Walk.snd_mem_support_of_mem_edges p' he)

/-- Building the 4-cycle on vertices u-x-w-y-u from the four adjacency facts. -/
lemma four_cycle {V : Type} [DecidableEq V] {K : SimpleGraph V} [DecidableRel K.Adj]
    {u x w y : V} (hux : K.Adj u x) (hxw : K.Adj x w) (hwy : K.Adj w y) (hyu : K.Adj y u)
    (hxy : x ≠ y) (hxu : x ≠ u) (hxw' : x ≠ w) (hwy' : w ≠ y) (hwu : w ≠ u) (hyu' : y ≠ u) :
    ∃ (v : V) (p : K.Walk v v) (k : ℕ), p.IsCycle ∧ p.length = 2 ^ k := by
  refine ⟨u, SimpleGraph.Walk.cons hux
    (SimpleGraph.Walk.cons hxw (SimpleGraph.Walk.cons hwy (SimpleGraph.Walk.cons hyu
      SimpleGraph.Walk.nil))), 2, ?_, ?_⟩
  · apply cycle_of_path _ hux _ (by simp [SimpleGraph.Walk.length_cons])
    -- the path x-w-y-u is a path
    have hp1 : (SimpleGraph.Walk.cons hyu SimpleGraph.Walk.nil).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [hyu']⟩
    have hp2 : (SimpleGraph.Walk.cons hwy (SimpleGraph.Walk.cons hyu SimpleGraph.Walk.nil)).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hp1, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false]
      rintro (h | h)
      · exact hwy' h
      · exact hwu h
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨hp2, ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | h | h)
    · exact hxw' h
    · exact hxy h
    · exact hxu h
  · simp [SimpleGraph.Walk.length_cons]

theorem OMA.solution : OMA.R_mse_1688329_R1.H1 := by
  intro V _ _ _ G _ hdeg hdense
  classical
  by_cases hcomp : ∃ u w : V, u ≠ w ∧ ¬ G.Adj u w
  · -- non-complete case: two common neighbours of the non-adjacent pair
    obtain ⟨u, w, hne, hnadj⟩ := hcomp
    set n := Fintype.card V with hn
    -- inclusion-exclusion on the neighbour finsets
    have huwbound : (G.neighborFinset u ∪ G.neighborFinset w).card ≤ n - 2 := by
      have hunotin : u ∉ G.neighborFinset u ∪ G.neighborFinset w := by
        simp only [Finset.mem_union, not_or]
        refine ⟨?_, ?_⟩
        · intro hmem
          exact (G.ne_of_adj ((G.mem_neighborFinset u u).mp hmem)) rfl
        · intro hmem
          exact hnadj ((G.mem_neighborFinset w u).mp hmem).symm
      have hwnotin : w ∉ G.neighborFinset u ∪ G.neighborFinset w := by
        simp only [Finset.mem_union, not_or]
        refine ⟨?_, ?_⟩
        · intro hmem
          exact hnadj ((G.mem_neighborFinset u w).mp hmem)
        · intro hmem
          exact (G.ne_of_adj ((G.mem_neighborFinset w w).mp hmem)) rfl
      have hb1 : (G.neighborFinset u ∪ G.neighborFinset w) ⊆ (Finset.univ.erase u).erase w := by
        have h1s : (G.neighborFinset u ∪ G.neighborFinset w) ⊆ Finset.univ.erase u := by
          rw [Finset.subset_erase]
          exact ⟨Finset.subset_univ _, hunotin⟩
        rw [Finset.subset_erase]
        exact ⟨h1s, hwnotin⟩
      have hcard := Finset.card_le_card hb1
      have huniv : (Finset.univ : Finset V).card = n := Finset.card_univ.trans hn.symm
      have hc1 : (Finset.univ.erase u : Finset V).card = n - 1 := by
        have he1 : (Finset.univ.erase u : Finset V).card = (Finset.univ : Finset V).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_univ u)
        omega
      have hc2 : ((Finset.univ.erase u).erase w : Finset V).card = n - 2 := by
        have he2 : ((Finset.univ.erase u).erase w : Finset V).card = (Finset.univ.erase u : Finset V).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ w⟩)
        omega
      omega
    have hdegree_sum : n ≤ (G.neighborFinset u).card + (G.neighborFinset w).card := by
      have h1 := hdense u
      have h2 := hdense w
      rw [← G.card_neighborFinset_eq_degree] at h1 h2
      omega
    have hn2 : 2 ≤ n := by
      have hnotmem2 : u ∉ ({w} : Finset V) := by
        simp only [Finset.mem_singleton]
        exact hne
      have hcard2 : ({u, w} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem hnotmem2, Finset.card_singleton]
      have hs := Finset.card_le_card (Finset.subset_univ ({u, w} : Finset V))
      have huniv2 : (Finset.univ : Finset V).card = n := Finset.card_univ.trans hn.symm
      omega
    have hinter : 2 ≤ (G.neighborFinset u ∩ G.neighborFinset w).card := by
      have hcu := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset w)
      omega
    obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (G.neighborFinset u ∩ G.neighborFinset w).card)
    simp only [Finset.mem_inter] at hx hy
    have hux : G.Adj u x := (G.mem_neighborFinset u x).mp hx.1
    have hwx : G.Adj w x := (G.mem_neighborFinset w x).mp hx.2
    have huy : G.Adj u y := (G.mem_neighborFinset u y).mp hy.1
    have hwy : G.Adj w y := (G.mem_neighborFinset w y).mp hy.2
    -- distinctness facts
    have hxu : x ≠ u := fun h => G.ne_of_adj (h ▸ hux) rfl
    have hyu' : y ≠ u := fun h => G.ne_of_adj (h ▸ huy) rfl
    have hxw' : x ≠ w := fun h => hnadj (h ▸ hux)
    have hyw' : y ≠ w := fun h => hnadj (h ▸ huy)
    have hwu : w ≠ u := fun h => hne h.symm
    exact four_cycle hux (hwx.symm) hwy (huy.symm) hxy hxu hxw' hyw'.symm hwu hyu'
  · -- complete case: pick any vertex and three distinct neighbours
    push_neg at hcomp
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv3 : 3 ≤ (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact hdeg v
    have hvpos : 0 < (G.neighborFinset v).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hvpos |>.exists_mem
    have hcardx : ((G.neighborFinset v).erase x).card = (G.neighborFinset v).card - 1 :=
      Finset.card_erase_of_mem hx
    have hposy : 0 < ((G.neighborFinset v).erase x).card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hposy |>.exists_mem
    have hysub : y ∈ G.neighborFinset v := Finset.mem_of_mem_erase hy
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    have hcardy : (((G.neighborFinset v).erase x).erase y).card = ((G.neighborFinset v).erase x).card - 1 :=
      Finset.card_erase_of_mem hy
    have hposz : 0 < (((G.neighborFinset v).erase x).erase y).card := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hposz |>.exists_mem
    have hzsub : z ∈ G.neighborFinset v := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
    have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    -- all needed adjacencies from completeness
    have hadj : ∀ a b : V, a ≠ b → G.Adj a b := fun a b hab => by
      have := hcomp a b
      tauto
    have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp hx
    have hvz : G.Adj v z := (G.mem_neighborFinset v z).mp hzsub
    have hvy : G.Adj v y := (G.mem_neighborFinset v y).mp hysub
    have hxv' : x ≠ v := fun h => G.ne_of_adj (h ▸ hvx) rfl
    have hyv' : y ≠ v := fun h => G.ne_of_adj (h ▸ hvy) rfl
    have hzv' : z ≠ v := fun h => G.ne_of_adj (h ▸ hvz) rfl
    have hxy : x ≠ y := fun h => hyx h.symm
    have hxz : x ≠ z := fun h => hzx h.symm
    have hyz : y ≠ z := fun h => hzy h.symm
    have hxya : G.Adj x y := hadj x y hxy
    have hyza : G.Adj y z := hadj y z hyz
    exact four_cycle hvx hxya hyza (hvz.symm) hxz (fun h => hxv' h) hxy hyz hyv' hzv'
