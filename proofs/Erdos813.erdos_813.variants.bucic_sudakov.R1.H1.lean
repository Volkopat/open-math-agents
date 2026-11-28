import OMAReductions.R_Erdos813_erdos_813_variants_bucic_sudakov_R1

-- Step Erdos813.erdos_813.variants.bucic_sudakov.R1.H1: hypothesis H1 of reduction Erdos813.erdos_813.variants.bucic_sudakov.R1

/-!
For `ε ≥ 5/12` the exponent is non-positive, so `n ^ (5/12 - ε) ≤ 1` for `n ≥ 1`. And `h n ≥ 1`
for `n ≥ 1`: the infimum defining `h n` is attained by some graph, and a single vertex is a clique.
-/

theorem OMA.solution : OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1.H1 := by
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hne : {k : ℕ | ∃ G : SimpleGraph (Fin n),
      Erdos813.EverySevenHasTriangle G ∧ G.cliqueNum = k}.Nonempty :=
    ⟨_, ⊤, Erdos813.everySevenHasTriangle_top n, rfl⟩
  obtain ⟨G, _, hG⟩ : ∃ G : SimpleGraph (Fin n),
      Erdos813.EverySevenHasTriangle G ∧ G.cliqueNum = Erdos813.h n := Nat.sInf_mem hne
  have hc : G.IsClique (↑({(⟨0, hn⟩ : Fin n)} : Finset (Fin n))) := by
    rw [Finset.coe_singleton]
    exact SimpleGraph.isClique_singleton _
  have h1 : 1 ≤ Erdos813.h n := by simpa [hG] using hc.card_le_cliqueNum
  exact (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (sub_nonpos.mpr hε)).trans
    (by exact_mod_cast h1)
