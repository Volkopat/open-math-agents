import FormalConjectures.ErdosProblems.«184»
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Interval.Finset.Nat

/-!
The greedy longest-cycle argument for the Erdős–Gallai logarithmic decomposition bound.
-/

open Finset SimpleGraph Erdos184
open scoped Classical

theorem E (k n : ℕ) (_ : 1 ≤ k) : ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = n → k * n < #G.edgeFinset → ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ k < p.length := by
  induction n with
  | zero =>
    intro V _ _ G h l
    have := G.card_edgeFinset_le_card_choose_two
    simp_all
  | succ n ih =>
    intro V _ _ G _ l
    by_contra! h
    obtain ⟨u, v, p, P, M⟩ :=
      @Walk.exists_isPath_forall_isPath_length_le_length _ G (Fintype.card_pos_iff.1 (by omega)) _
    have : G.degree u ≤ k := by
      refine (card_le_card (t := (Icc 1 k).image p.getVert) fun x r => ?_).trans
        (card_image_le.trans (by simp))
      simp at r
      obtain ⟨i, rfl, _⟩ := Walk.mem_support_iff_exists_getVert.1 (not_not.1 fun t => by simpa using M _ _ (.cons r.symm p) (P.cons t))
      refine mem_image_of_mem _ (mem_Icc.2 ⟨Nat.pos_of_ne_zero ?_, ?_⟩)
      · rintro rfl; simp at r
      · by_contra!
        have := h _ (.cons r.symm (p.take i)) (Walk.isCycle_iff_isPath_tail_and_le_length.2
          ⟨by simpa using P.take i, by simp; omega⟩)
        simp at this; omega
    have := G.degree_le_card_edgeFinset u
    obtain ⟨w, q, Q, _⟩ := ih (G.induce {u}ᶜ)
      (by rw [Fintype.card_compl_set, Set.card_singleton]; omega)
      (by rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
          rw [Nat.mul_succ] at l; omega : k * n < #(G.induce {u}ᶜ).edgeFinset)
    have := h _ _ (Q.map (f := ⟨Subtype.val, id⟩) Subtype.val_injective)
    simp at this; omega

theorem S (m h n : ℕ) (H : (m : ℝ) ≤ h * n) (a : 0 < m) (b : h ≤ m) :
    2 * n * Real.log (↑(m - h) + 1) + 1 ≤ 2 * n * Real.log (m + 1) := by
  have c := Real.log_le_sub_one_of_pos (show (0:ℝ) < (↑(m - h) + 1) / (m + 1) by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at c
  field_simp at c
  push_cast [b] at c ⊢
  nlinarith [mul_le_mul_of_nonneg_left c (Nat.cast_nonneg n),
    (by exact_mod_cast a : (1 : ℝ) ≤ m)]

theorem OMA.solution : type_of% @Erdos184.erdos_184.variants.n_log_n := by
  refine ⟨fun n => 2 * n * Real.log (n ^ 2), (Asymptotics.isBigO_refl _ _).const_mul_left 4 |>.congr_left fun n => by rw [Real.log_pow]; ring, fun {V} _ _ G => ?_⟩
  set n := Fintype.card V
  have K : ∀ m F, F ≤ G → #F.edgeFinset = m → ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ ((D : Set G.Subgraph).PairwiseDisjoint (·.edgeSet) ∧
        (⋃ H ∈ D, H.edgeSet) = F.edgeSet) ∧ (#D : ℝ) ≤ 2 * n * Real.log (m + 1) := by
    refine fun m => m.strong_induction_on fun m I F A B => ?_
    obtain rfl | C := eq_or_ne m 0
    · exact ⟨∅, by simp_all⟩
    obtain ⟨⟨a, b⟩, e⟩ := card_ne_zero.1 (B ▸ C)
    obtain ⟨H, s, L, N, O, R⟩ : ∃ (H : G.Subgraph) (s : Finset (Sym2 V)),
        IsCycleOrEdge H.coe ∧ H.edgeSet = s ∧ s ⊆ F.edgeFinset ∧ m ≤ #s * n := by
      by_cases d : n < m
      · have P : 0 < n := Fintype.card_pos_iff.2 ⟨a⟩
        obtain ⟨v, p, Q, l⟩ := E ((m - 1) / n) n (Nat.div_pos (by omega) P) F rfl (by have := Nat.div_mul_le_self (m - 1) n; omega)
        have := Nat.lt_mul_of_div_lt l P
        refine ⟨_, p.edges.toFinset, Or.inl ⟨(p.mapLe A).toSubgraph_connected.coe, fun w => by simpa [Subgraph.degree] using (Q.mapLe A).ncard_neighborSet_toSubgraph_eq_two ((Walk.mem_verts_toSubgraph _).1 w.2)⟩, by ext; simp, fun e => by simpa using p.edges_subset_edgeSet (e := e), by rw [List.toFinset_card_of_nodup Q.edges_nodup, p.length_edges]; omega⟩
      · have h := A (mem_edgeFinset.1 e)
        exact ⟨G.subgraphOfAdj h, {s(a, b)}, Or.inr (by have := (IsTree.coe_subgraphOfAdj h).card_edgeFinset; simp [card_pair h.ne] at this; convert this), by simp, singleton_subset_iff.2 e, by simp; omega⟩
    obtain ⟨D, x, ⟨y, z⟩, t⟩ := I (m - #s)
      (Nat.sub_lt (by omega) (Nat.pos_of_mul_pos_right (b := n) (by omega)))
      (F.deleteEdges s) ((deleteEdges_le _).trans A) (by simp [card_sdiff_of_subset O, B])
    exact ⟨insert H D, by simpa [L] using x, ⟨coe_insert H D ▸ y.insert fun J j _ =>
      Set.disjoint_left.2 fun e f g =>
        ((edgeSet_deleteEdges _).le (z.le (Set.mem_biUnion j g))).2 (N ▸ f),
      by rw [set_biUnion_insert, z, edgeSet_deleteEdges, N]; simpa [← coe_edgeFinset] using O⟩,
      (Nat.cast_le.2 (card_insert_le _ _)).trans
        (by push_cast; linarith [S m #s _ (by exact_mod_cast R) (by omega) (B ▸ card_le_card O)])⟩
  obtain ⟨D, x, y, z⟩ := K _ G le_rfl rfl
  refine ⟨D, x, y, z.trans ?_⟩
  obtain h | h := eq_or_ne n 0
  · simp [h]
  dsimp only
  gcongr
  exact_mod_cast G.card_edgeFinset_le_card_choose_two.trans_lt (Nat.choose_lt_pow h le_rfl)
