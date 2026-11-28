import FormalConjectures.ErdosProblems.«1079»
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Nat.Choose.Vandermonde

/-! Shorter proof of `Erdos1079.erdos_1079`. -/

open SimpleGraph Finset Finset.Nat
open scoped BigOperators

private lemma eca {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  rw [← card_union_of_disjoint (by
      rw [disjoint_iff_inter_eq_empty, ← edgeFinset_inf, ← edgeFinset_bot, edgeFinset_inj]
      exact inf_compl_eq_bot),
    show G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset by
      rw [← edgeFinset_sup, edgeFinset_inj]; exact sup_compl_eq_top,
    card_edgeFinset_top_eq_card_choose_two]

private lemma ext_join (a b q : ℕ) (hq : 0 < q) :
    extremalNumber a (completeGraph (Fin (q + 1))) + a * b ≤
      extremalNumber (a + b) (completeGraph (Fin (q + 2))) := by
  classical
  let T := turanGraph a q
  let J := Tᶜ ⊕g (⊤ : SimpleGraph (Fin b))
  let col : Fin a ⊕ Fin b → Fin (q + 1)
    | .inl x => ⟨x.val % q, (Nat.mod_lt _ hq).trans (Nat.lt_succ_self q)⟩
    | .inr _ => ⟨q, Nat.lt_succ_self q⟩
  have hcol : Jᶜ.Colorable (q + 1) := ⟨Coloring.mk col fun {u v} huv hc => by
    rcases u with x | x <;> rcases v with y | y
    · have h : x ≠ y ∧ (x ≠ y → T.Adj x y) := by simpa [J, compl_adj] using huv
      exact (turanGraph_adj.mp (h.2 h.1)) (congrArg Fin.val hc)
    · exact (Nat.mod_lt _ hq).ne (congrArg Fin.val hc)
    · exact (Nat.mod_lt _ hq).ne (congrArg Fin.val hc).symm
    · simp [J, compl_adj] at huv⟩
  have hfree : (completeGraph (Fin (q + 2))).Free Jᶜ := by
    change (⊤ : SimpleGraph (Fin (q + 2))).Free Jᶜ
    rw [← cliqueFree_iff_top_free, Fintype.card_fin]
    exact hcol.cliqueFree (by omega)
  have hJle := card_edgeFinset_le_extremalNumber hfree
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hJle
  have hJcnt : J.edgeFinset.card =
      Tᶜ.edgeFinset.card + (⊤ : SimpleGraph (Fin b)).edgeFinset.card := by
    simp only [edgeFinset_card]
    exact (Fintype.card_congr (edgeSetSumEquiv (G := Tᶜ)
      (H := (⊤ : SimpleGraph (Fin b))))).trans Fintype.card_sum
  have ht := eca T; have hj := eca J
  have hch : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    rw [Nat.add_choose_eq, sum_antidiagonal_eq_sum_range_succ_mk]; norm_num [sum_range_succ]; omega
  rw [hJcnt, card_edgeFinset_top_eq_card_choose_two, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, hch] at hj
  rw [Fintype.card_fin] at ht
  have : Nontrivial (Fin (q + 1)) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  have hex : extremalNumber a (completeGraph (Fin (q + 1))) = T.edgeFinset.card := by
    change extremalNumber a (⊤ : SimpleGraph (Fin (q + 1))) = _
    rw [extremalNumber_top, Fintype.card_fin, Nat.add_sub_cancel]
  rw [show Jᶜ.edgeFinset.card = T.edgeFinset.card + a * b by omega, ← hex] at hJle
  exact hJle

theorem OMA.solution : type_of% @Erdos1079.erdos_1079 := by
  intro r hr
  refine ⟨1 / 3, by norm_num, fun n hn G hG => ?_⟩
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let d := G.degree v
  have hd (w : Fin n) : G.degree w ≤ d := by
    rw [show d = G.maxDegree from hv.symm]; exact G.degree_le_maxDegree w
  have hdn : d ≤ n := by
    simpa [d] using (show G.degree v ≤ Fintype.card (Fin n) from by
      rw [← card_neighborFinset_eq_degree, ← card_univ]; exact card_le_card (subset_univ _))
  have hjoin (a : ℕ) (ha : a ≤ n) :
      extremalNumber a (completeGraph (Fin (r - 1))) + a * (n - a) ≤
        extremalNumber n (completeGraph (Fin r)) := by
    have hb := ext_join a (n - a) (r - 2) (by omega)
    rwa [Nat.add_sub_of_le ha, show r - 2 + 1 = r - 1 by omega, show r - 2 + 2 = r by omega] at hb
  have hsplit : G.edgeSet.ncard ≤ {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard + (n - d) * d := by
    let ins := G.edgeFinset.filter fun e => ∀ x ∈ e, G.Adj v x
    let out := G.edgeFinset.filter fun e => ¬ ∀ x ∈ e, G.Adj v x
    let far := univ.filter fun w => ¬ G.Adj v w
    have hfar : far.card = n - d := by
      have hp := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (G.Adj v)
      rw [← G.neighborFinset_eq_filter, card_neighborFinset_eq_degree, card_univ,
        Fintype.card_fin] at hp
      change d + far.card = n at hp; omega
    have hsub : out ⊆ far.biUnion fun w => G.incidenceFinset w := fun e he => by
      obtain ⟨heG, heo⟩ := mem_filter.mp he; push Not at heo; obtain ⟨w, hw, hna⟩ := heo
      exact mem_biUnion.mpr ⟨w, mem_filter.mpr ⟨mem_univ _, hna⟩,
        by rw [G.incidenceFinset_eq_filter]; exact mem_filter.mpr ⟨heG, hw⟩⟩
    have hbnd : out.card ≤ far.card * d := (card_le_card hsub).trans <| card_biUnion_le.trans <|
      (sum_le_sum (g := fun _ => d) fun w _ => by rw [card_incidenceFinset_eq_degree]; exact hd w).trans_eq
        (by simp)
    have hpart : ins.card + out.card = G.edgeFinset.card :=
      card_filter_add_card_filter_not (s := G.edgeFinset) _
    have hins : ins.card = {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard := by
      rw [← Set.ncard_coe_finset]; congr 1; ext; simp [ins]
    rw [← hins, ← coe_edgeFinset G, Set.ncard_coe_finset, ← hpart, ← hfar]
    exact Nat.add_le_add_left hbnd _
  refine ⟨v, ?_, ?_⟩
  · let a := n / 2
    have hlow : a * (n - a) ≤ G.edgeSet.ncard :=
      (Nat.le_add_left _ _).trans ((hjoin a (by omega)).trans hG)
    have hsum : 2 * G.edgeSet.ncard ≤ n * d := by
      have h := G.sum_degrees_eq_twice_card_edges
      rw [← Set.ncard_coe_finset, coe_edgeFinset] at h
      rw [← h]; exact (sum_le_sum fun w _ => hd w).trans_eq (by simp)
    have hmul : n * n ≤ (3 * a) * (2 * (n - a)) := Nat.mul_le_mul (by omega) (by omega)
    have hnd : n ≤ 3 * d := Nat.le_of_mul_le_mul_left (by nlinarith : n * n ≤ n * (3 * d)) (by omega)
    have : (n : ℝ) ≤ 3 * d := by exact_mod_cast hnd
    change (1 / 3 : ℝ) * n ≤ d; linarith
  · have hh := (hjoin d hdn).trans (hG.trans hsplit)
    rw [Nat.mul_comm (n - d) d] at hh; exact Nat.le_of_add_le_add_right hh
