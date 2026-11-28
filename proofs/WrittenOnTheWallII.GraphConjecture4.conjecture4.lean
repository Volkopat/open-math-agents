import FormalConjectures.WrittenOnTheWallII.GraphConjecture4

-- Problem: Written on the Wall II - Conjecture 4
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture4.lean:44 (declaration WrittenOnTheWallII.GraphConjecture4.conjecture4)
-- Credit: @jonas-klesen (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea. A tree on at least two vertices has `2 + ∑ (deg x - 2)` leaves, the sum taken over
-- the non-leaves, so any set `S` of vertices gives `∑ x ∈ S, (deg x - 2) + 2 ≤ #leaves`.
-- If `G` is complete, a spanning tree containing a full star has `n - 1` leaves.
-- Otherwise some non-edge `{u, v}` has a common neighbour `w`. The two stars at `u` and `v`,
-- joined through `w`, form an acyclic subgraph in which `deg u + deg v = |N(u) ∪ N(v)| + 1`.
-- Extending it to a spanning tree keeps these degrees, hence at least `|N(u) ∪ N(v)| - 1` leaves.

open SimpleGraph

namespace OMAConjecture4

/-- A graph is acyclic if every vertex `x` has at most one neighbour of rank at most the rank
of `x`, namely `p x`. -/
lemma isAcyclic_of_rank {V : Type*} (H : SimpleGraph V) (r : V → ℕ) (p : V → V)
    (h : ∀ x y, H.Adj x y → r y ≤ r x → y = p x) : H.IsAcyclic := by
  classical
  intro a c hc
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image c.support.toFinset r
    ⟨a, List.mem_toFinset.2 c.start_mem_support⟩
  rw [List.mem_toFinset] at hx
  have hc' : (c.rotate x hx).IsCycle := hc.rotate hx
  have hsup : ∀ y ∈ (c.rotate x hx).support, r y ≤ r x := by
    intro y hy
    apply hmax
    rw [List.mem_toFinset]
    exact (c.mem_support_rotate_iff x hx).1 hy
  have h1 := h x _ ((c.rotate x hx).adj_snd hc'.not_nil)
    (hsup _ ((c.rotate x hx).getVert_mem_support 1))
  have h2 := h x _ ((c.rotate x hx).adj_penultimate hc'.not_nil).symm
    (hsup _ ((c.rotate x hx).getVert_mem_support _))
  exact hc'.snd_ne_penultimate (h1.trans h2.symm)

/-- A connected graph with a non-edge has a non-edge whose ends have a common neighbour. -/
lemma exists_dist_two {V : Type*} (G : SimpleGraph V) :
    ∀ {x y : V} (_ : G.Walk x y), x ≠ y → ¬ G.Adj x y →
      ∃ u w v, G.Adj u w ∧ G.Adj w v ∧ u ≠ v ∧ ¬ G.Adj u v := by
  intro x y p
  induction p with
  | nil => intro h; exact absurd rfl h
  | @cons a b c hab q ih =>
    intro hne hnadj
    by_cases hbc : b = c
    · subst hbc; exact absurd hab hnadj
    · by_cases hadj : G.Adj b c
      · exact ⟨a, b, c, hab, hadj, hne, hnadj⟩
      · exact ih hbc hadj

/-- A spanning tree containing the star at `u` and the edges from `v` to `w` and to the
neighbours of `v` that are not neighbours of `u`. -/
lemma exists_tree {α : Type*} (G : SimpleGraph α) (hconn : G.Connected) (u v w : α)
    (huv : ¬ G.Adj u v) :
    ∃ T : SimpleGraph α, T ≤ G ∧ T.IsTree ∧ (∀ y, G.Adj u y → T.Adj u y) ∧
      (∀ y, G.Adj v y → (¬ G.Adj u y ∨ y = w) → T.Adj v y) := by
  classical
  let H : SimpleGraph α := SimpleGraph.fromRel
    (fun x y => (x = u ∧ G.Adj u y) ∨ (x = v ∧ G.Adj v y ∧ (¬ G.Adj u y ∨ y = w)))
  have hHG : H ≤ G := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    obtain ⟨-, (⟨rfl, h1⟩ | ⟨rfl, h1, -⟩) | (⟨rfl, h1⟩ | ⟨rfl, h1, -⟩)⟩ := hxy
    · exact h1
    · exact h1
    · exact h1.symm
    · exact h1.symm
  have hHac : H.IsAcyclic := by
    apply isAcyclic_of_rank H
      (fun x => if x = u then 0 else if G.Adj u x then 1 else if x = v then 2 else 3)
      (fun x => if G.Adj u x then u else if x = v then w else v)
    intro x y hxy hr
    rw [SimpleGraph.fromRel_adj] at hxy
    have huu : ¬ G.Adj u u := G.irrefl
    have hvv : ¬ G.Adj v v := G.irrefl
    have hvu : ¬ G.Adj v u := fun h => huv h.symm
    obtain ⟨hne, (⟨rfl, h1⟩ | ⟨rfl, h1, h2⟩) | (⟨rfl, h1⟩ | ⟨rfl, h1, h2⟩)⟩ := hxy
    · have hyx : y ≠ x := fun h => hne h.symm
      simp [hyx, h1] at hr
    · by_cases hxu : x = u
      · subst hxu
        have hyx : y ≠ x := fun h => hne h.symm
        simp [hyx, h1] at hr
      · by_cases hy : G.Adj u y
        · rcases h2 with h2 | h2
          · exact absurd hy h2
          · simp [huv, h2]
        · have hyu : y ≠ u := by rintro rfl; exact hvu h1
          have hyx : y ≠ x := fun h => hne h.symm
          simp [hxu, huv, hy, hyu, hyx] at hr
    · simp [h1]
    · by_cases hx : G.Adj u x
      · have hxu : x ≠ u := by rintro rfl; exact huu hx
        by_cases hyu : y = u
        · simp [hx, hyu]
        · simp [hx, hxu, hyu, huv] at hr
      · have hxy : x ≠ y := hne
        simp [hx, hxy]
  obtain ⟨T, hHT, hTG, hT⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic hHG hHac
  refine ⟨T, hTG, hT, fun y hy => hHT ?_, fun y hy hy' => hHT ?_⟩
  · rw [SimpleGraph.fromRel_adj]
    exact ⟨hy.ne, Or.inl (Or.inl ⟨rfl, hy⟩)⟩
  · rw [SimpleGraph.fromRel_adj]
    exact ⟨hy.ne, Or.inl (Or.inr ⟨rfl, hy, hy'⟩)⟩

/-- In a tree on at least two vertices, `∑ x ∈ S, (deg x - 2) + 2` is at most the number of
leaves, for every set `S` of vertices. -/
lemma sum_degree_le_leaves {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α) :
    (∑ x ∈ S, ((T.degree x : ℤ) - 2)) + 2 ≤
      ((Finset.univ.filter fun x => T.degree x = 1).card : ℤ) := by
  let f (x : α) : ℤ := (T.degree x : ℤ) - 2
  let g (x : α) : ℤ := if T.degree x = 1 then 1 else 0
  change (∑ x ∈ S, f x) + 2 ≤ _
  have hsum : (∑ x, (T.degree x : ℤ)) = 2 * (Fintype.card α : ℤ) - 2 := by
    have h1 := T.sum_degrees_eq_twice_card_edges
    have h2 := hT.card_edgeFinset
    have h3 : (∑ x, T.degree x) + 2 = 2 * Fintype.card α := by omega
    have h4 : ((∑ x, T.degree x : ℕ) : ℤ) + 2 = 2 * (Fintype.card α : ℤ) := by exact_mod_cast h3
    rw [Nat.cast_sum] at h4
    linarith
  have htotal : ∑ x, f x = -2 := by
    simp [f, Finset.sum_sub_distrib, hsum, Finset.sum_const]
    omega
  have hcard : ((Finset.univ.filter fun x => T.degree x = 1).card : ℤ) = ∑ x, g x := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hnn (x : α) : 0 ≤ f x + g x := by
    have := hT.connected.preconnected.degree_pos_of_nontrivial x
    simp only [f, g]
    split_ifs <;> omega
  have hsub : (∑ x ∈ S, (f x + g x)) ≤ ∑ x, (f x + g x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun x _ _ => hnn x)
  have hsmall : (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (f x + g x) :=
    Finset.sum_le_sum (fun x _ => by simp only [g]; split_ifs <;> omega)
  have h := hsmall.trans hsub
  simp only [Finset.sum_add_distrib, htotal, ← hcard] at h
  omega

/-- The number of leaves of a spanning tree of `G` is at most `Ls G`. -/
lemma leaves_le_Ls {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (T : SimpleGraph α) [DecidableRel T.Adj] (hTG : T ≤ G)
    (hT : T.IsTree) :
    ((Finset.univ.filter fun x => T.degree x = 1).card : ℝ) ≤ Ls G := by
  classical
  unfold Ls
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro _ ⟨S, -, rfl⟩
    exact Nat.cast_le.2 (Finset.card_le_univ _)
  · refine ⟨SimpleGraph.toSubgraph T hTG, ⟨SimpleGraph.toSubgraph.isSpanning T hTG, ?_⟩, ?_⟩
    · let e : (SimpleGraph.toSubgraph T hTG).coe ≃g T :=
        { toEquiv := Equiv.Set.univ α
          map_rel_iff' := Iff.rfl }
      exact e.isTree_iff.2 hT
    · show ((Finset.filter (fun v => (SimpleGraph.toSubgraph T hTG).degree v = 1)
        (SimpleGraph.toSubgraph T hTG).verts.toFinset).card : ℝ) = _
      have hv : (SimpleGraph.toSubgraph T hTG).verts.toFinset = Finset.univ := by
        ext x
        exact ⟨fun _ => Finset.mem_univ x, fun _ => Set.mem_toFinset.2 (Set.mem_univ x)⟩
      rw [hv]
      simp_rw [SimpleGraph.degree_toSubgraph G T hTG]

end OMAConjecture4

open OMAConjecture4 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture4.conjecture4 := by
  intro α _ _ G _ _ hconn
  classical
  by_cases hne : (Gᶜ).edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ x y =>
    rw [mem_edgeFinset, mem_edgeSet, compl_adj] at he
    obtain ⟨p⟩ := hconn.preconnected x y
    obtain ⟨u, w, v, huw, hwv, huv, hnadj⟩ := exists_dist_two G p he.1 he.2
    obtain ⟨T, hTG, hT, hu, hv⟩ := exists_tree G hconn u v w hnadj
    have hL := leaves_le_Ls G T hTG hT
    have hd := sum_degree_le_leaves T hT {u, v}
    rw [Finset.sum_pair huv] at hd
    have hu' : G.neighborFinset u ⊆ T.neighborFinset u := by
      intro y hy
      rw [mem_neighborFinset] at hy ⊢
      exact hu y hy
    have hv' : insert w (G.neighborFinset v \ G.neighborFinset u) ⊆ T.neighborFinset v := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_sdiff, mem_neighborFinset, mem_neighborFinset] at hy
      rw [mem_neighborFinset]
      rcases hy with rfl | ⟨h1, h2⟩
      · exact hv _ hwv.symm (Or.inr rfl)
      · exact hv y h1 (Or.inl h2)
    have c1 := Finset.card_le_card hu'
    have c2 := Finset.card_le_card hv'
    rw [Finset.card_insert_of_notMem (by simp [huw])] at c2
    have c3 := Finset.card_sdiff_add_card (G.neighborFinset v) (G.neighborFinset u)
    rw [Finset.union_comm] at c3
    rw [T.card_neighborFinset_eq_degree u] at c1
    rw [T.card_neighborFinset_eq_degree v] at c2
    have hNG : NG G ≤ ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) := by
      have hmem : s(u, v) ∈ (Gᶜ).edgeFinset := by
        rw [mem_edgeFinset, mem_edgeSet, compl_adj]
        exact ⟨huv, hnadj⟩
      unfold NG
      simp only
      rw [dif_pos ⟨_, hmem⟩]
      exact_mod_cast Finset.min'_le _ _ (Finset.mem_image_of_mem _ hmem)
    have hk : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℤ) - 1 ≤
        ((Finset.univ.filter fun x => T.degree x = 1).card : ℤ) := by
      omega
    have hk' : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) - 1 ≤
        ((Finset.univ.filter fun x => T.degree x = 1).card : ℝ) := by
      exact_mod_cast hk
    linarith
  · have hadj : ∀ x y : α, x ≠ y → G.Adj x y := by
      intro x y hxy
      by_contra h
      exact hne ⟨s(x, y), by rw [mem_edgeFinset, mem_edgeSet, compl_adj]; exact ⟨hxy, h⟩⟩
    obtain ⟨u⟩ := (inferInstance : Nonempty α)
    obtain ⟨T, hTG, hT, hu, -⟩ := exists_tree G hconn u u u G.irrefl
    have hL := leaves_le_Ls G T hTG hT
    have hd := sum_degree_le_leaves T hT {u}
    rw [Finset.sum_singleton] at hd
    have hu' : Finset.univ.erase u ⊆ T.neighborFinset u := by
      intro y hy
      rw [mem_neighborFinset]
      exact hu y (hadj u y (Finset.ne_of_mem_erase hy).symm)
    have c1 := Finset.card_le_card hu'
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
      T.card_neighborFinset_eq_degree u] at c1
    have hNG : NG G = (Fintype.card α : ℝ) := by
      unfold NG
      simp only
      rw [dif_neg hne]
    have hk : (Fintype.card α : ℤ) - 1 ≤
        ((Finset.univ.filter fun x => T.degree x = 1).card : ℤ) := by
      omega
    have hk' : (Fintype.card α : ℝ) - 1 ≤
        ((Finset.univ.filter fun x => T.degree x = 1).card : ℝ) := by
      exact_mod_cast hk
    linarith
