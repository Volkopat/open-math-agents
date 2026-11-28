import FormalConjectures.ErdosProblems.«133»

/-! Cover the graph by the root and the closed neighbourhoods of its neighbours. -/

open Filter SimpleGraph Erdos133

private lemma card_le_closed_neighborhood_bound {n : ℕ} (r : Fin n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hd : G.diam = 2)
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) : n ≤ (d + 1) ^ 2 := by
  have hed : G.ediam = 2 := (ENat.toNat_eq_iff (by decide : (2 : ℕ) ≠ 0)).mp hd
  let B (u : Fin n) := insert u (G.neighborFinset u)
  have cover : (Finset.univ : Finset (Fin n)) ⊆ insert r ((G.neighborFinset r).biUnion B) := by
    intro v _
    by_cases hr : v = r
    · simp [hr]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    by_cases ha : G.Adj r v
    · exact ⟨v, by simpa using ha, Finset.mem_insert_self _ _⟩
    have hn : (G.commonNeighbors r v).Nonempty := by
      by_contra hempty
      exact (not_lt_of_ge (hed ▸ edist_le_ediam : G.edist r v ≤ 2))
        (two_lt_edist_iff.mpr ⟨Ne.symm hr, ha, Set.not_nonempty_iff_eq_empty.mp hempty⟩)
    obtain ⟨u, hu, hv⟩ := hn
    exact ⟨u, by simpa using hu, Finset.mem_insert_of_mem (by simpa using hv.symm)⟩
  have sz (u : Fin n) (_ : u ∈ G.neighborFinset r) : (B u).card ≤ d + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (hdeg u))
  have h := (Finset.card_le_card cover).trans (Finset.card_insert_le _ _)
  have b := Finset.card_biUnion_le_card_mul _ _ _ sz
  have rBound : (G.neighborFinset r).card ≤ d := hdeg r
  simp only [Finset.card_univ, Fintype.card_fin] at h
  nlinarith [Nat.mul_le_mul_right (d + 1) rBound]

theorem OMA.solution : type_of% @Erdos133.erdos_133.variants.lower_bound := by
  classical
  intro ε he
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (3 : ℕ), ht.eventually_ge_atTop (1 / ε)] with n hn hlarge
  let r : Fin n := ⟨0, by omega⟩
  let a : Fin n := ⟨1, by omega⟩
  let b : Fin n := ⟨2, by omega⟩
  let S := starGraph r
  have ha : r ≠ a := by simp [Fin.ext_iff, r, a]
  have hb : r ≠ b := by simp [Fin.ext_iff, r, b]
  have ab : a ≠ b := by simp [Fin.ext_iff, a, b]
  have hap : S.Adj a r := (starGraph_center_adj ha).symm
  have hbp : S.Adj b r := (starGraph_center_adj hb).symm
  have hdist : S.edist a b = 2 :=
    edist_eq_two_iff.mpr ⟨ab, by simp [S, ha.symm, hb.symm],
      ⟨r, S.mem_commonNeighbors.mpr ⟨hap, hbp⟩⟩⟩
  have slow : 2 ≤ S.ediam := hdist ▸ edist_le_ediam
  have sup : S.ediam ≤ 2 := by
    calc
      S.ediam ≤ 2 * S.eccent r := ediam_le_two_mul_eccent r
      _ ≤ 2 * 1 := by
        gcongr
        exact (eccent_le_one_iff r).mpr fun _ h => starGraph_center_adj h
      _ = 2 := mul_one _
  have hd : S.diam = 2 := by rw [SimpleGraph.diam, le_antisymm sup slow]; rfl
  have hne : {d : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧
      ∀ v, G.degree v ≤ d}.Nonempty :=
    ⟨n, S, (isAcyclic_starGraph r).cliqueFree (by decide), hd, fun v => by
      let : DecidableRel S.Adj := fun u w => Classical.propDecidable (S.Adj u w)
      exact Nat.le_of_lt (by simpa using S.degree_lt_card_verts v)⟩
  obtain ⟨G, _, hG, hdeg⟩ := Nat.sInf_mem hne
  have hc := card_le_closed_neighborhood_bound r G hG hdeg
  have hbnd : Real.sqrt (n : ℝ) ≤ (f n : ℝ) + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by exact_mod_cast hc⟩
  have hmul := (div_le_iff₀ he).mp hlarge
  linarith
