import FormalConjectures.ErdosProblems.«803»

open Finset SimpleGraph Filter Real
open scoped Classical

theorem OMA.solution : type_of% @Erdos803.erdos_803.variants.janzer_sudakov := by
  classical
  refine ⟨1, fun k => ?_⟩
  let m := 2 * (k + 1)
  let a := (√(log (m : ℝ)) / (log (log (m : ℝ))) ^ (3 / 2 : ℝ)) * m
  let c := (|a| + 1)⁻¹
  have hden : 0 < |a| + 1 := by positivity
  refine ⟨c, inv_pos.mpr hden, ?_⟩
  filter_upwards [(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop
    (m : ℝ), eventually_ge_atTop 1] with n hn hn1 G he
  have hlow : m * n < G.edgeSet.ncard := by
    have nr : (0 : ℝ) < n := by exact_mod_cast hn1
    exact_mod_cast (show (m : ℝ) * n < G.edgeSet.ncard from
      (mul_lt_mul_of_pos_right (show (m : ℝ) < log n from hn) nr).trans_le
        (by simpa [mul_comm] using he))
  have hfresh (S : Set (Fin n)) (hS : S.ncard * n < G.edgeSet.ncard) :
      ∃ u ∉ S, ∃ v ∉ S, G.Adj u v := by
    by_contra! hcov
    have hsub : G.edgeFinset ⊆ (S.toFinset ×ˢ (univ : Finset (Fin n))).image (fun z => s(z.1, z.2)) := by
      intro e; induction e using Sym2.inductionOn with
      | _ u v =>
        intro he; have hadj : G.Adj u v := by simpa using he
        by_cases hu : u ∈ S
        · exact mem_image.mpr ⟨(u, v), by simpa using hu, rfl⟩
        · exact mem_image.mpr ⟨(v, u), by simpa using by_contra fun hv => hcov u hu v hv hadj, Sym2.eq_swap⟩
    have := (card_le_card hsub).trans card_image_le
    have : G.edgeFinset.card = G.edgeSet.ncard := by rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard]
    have : (S.toFinset ×ˢ (univ : Finset (Fin n))).card = S.ncard * n := by
      simp [Set.ncard_eq_toFinset_card']
    omega
  have hmatch : ∀ t, 2 * t * n < G.edgeSet.ncard →
      ∃ H : G.Subgraph, H.IsMatching ∧ H.verts.ncard = 2 * t := by
    intro t; induction t with
    | zero => exact fun _ => ⟨⊥, by intro _ hv; simp at hv, by simp⟩
    | succ t ih =>
      intro hlt
      have hlt' : 2 * t * n < G.edgeSet.ncard := (Nat.mul_le_mul_right _ (by omega)).trans_lt hlt
      obtain ⟨H, hH, hc⟩ := ih hlt'
      obtain ⟨u, hu, v, hv, hadj⟩ := hfresh H.verts (by rwa [hc])
      have eH := Subgraph.IsMatching.subgraphOfAdj hadj
      have hdisj : Disjoint H.verts (G.subgraphOfAdj hadj).verts :=
        Set.disjoint_left.mpr fun w hw he => by
          simp [subgraphOfAdj_verts] at he; rcases he with rfl | rfl <;> contradiction
      refine ⟨H ⊔ G.subgraphOfAdj hadj,
        hH.sup eH (by rwa [hH.support_eq_verts, eH.support_eq_verts]), ?_⟩
      rw [Subgraph.verts_sup, Set.ncard_union_eq hdisj, hc, subgraphOfAdj_verts,
        Set.ncard_pair hadj.ne]; omega
  obtain ⟨H, hm, hsize⟩ := hmatch (k + 1) hlow
  have hp : H.verts.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  let : Nonempty H.verts := hp.to_subtype
  have hdeg (w : H.verts) (inst : Fintype (H.coe.neighborSet w)) :
      @SimpleGraph.degree _ H.coe w inst = 1 :=
    (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ H.coe w inst).mpr <| by
      obtain ⟨z, hz, hu⟩ := hm w.2
      exact ⟨⟨z, H.edge_vert hz.symm⟩, hz, fun j hj => Subtype.ext (hu j hj)⟩
  have hbal : IsBalanced H.coe 1 := by
    obtain ⟨u, hu⟩ := H.coe.exists_maximal_degree_vertex
    obtain ⟨v, hv⟩ := H.coe.exists_minimal_degree_vertex
    simp [IsBalanced, hu.trans (hdeg u _), hv.trans (hdeg v _)]
  obtain ⟨u, hu⟩ := hp; obtain ⟨v, hv, _⟩ := hm hu
  have hpos : 0 < H.edgeSet.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(u, v), hv⟩
  refine ⟨H, by omega, hbal, ?_⟩
  rw [hsize, mul_assoc]
  have h1 : c * a ≤ 1 := by
    dsimp [c]; rw [← div_eq_inv_mul, div_le_iff₀ hden, one_mul]; linarith [le_abs_self a]
  exact h1.trans (by exact_mod_cast hpos)
