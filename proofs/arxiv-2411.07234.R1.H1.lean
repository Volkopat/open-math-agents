import OMAReductions.R_arxiv_2411_07234_R1

/-!
# Proof of `arxiv-2411.07234.R1.H1`

Proves the base cases `k < 3` (`k = 0, 1, 2`) of multiple mixing from 2-mixing for a
measure-preserving measurable equivalence `T : X ≃ᵐ X` on a probability space `(X, μ)`.

- `k = 0`: the empty intersection is `Set.univ`, with `μ Set.univ = 1 = ∏ i : Fin 0, μ (A i)`.
- `k = 1`: `μ ((T^[d r 0])⁻¹' A 0) = μ (A 0)` by `MeasurePreserving.iterate`.
- `k = 2`: since `d r 0 + r < d r 1`, we have `d r 1 = d r 0 + (d r 1 - d r 0)` with
  `r < d r 1 - d r 0`, so `MeasurePreserving.iterate` shifts the intersection to
  `μ (A 0 ∩ (T^[d r 1 - d r 0])⁻¹' A 1)`, which converges to `μ (A 0) * μ (A 1)` by mixing.
-/

open MeasureTheory Filter Topology

theorem OMA.solution : OMA.R_arxiv_2411_07234_R1.H1 := by
  intro X _ μ _ T hT hmix k hk d hd A hA
  interval_cases k
  · simp [measure_univ]
  · have hconst : ∀ r : ℕ, μ (⋂ i : Fin 1, (T^[d r i]) ⁻¹' A i) = ∏ i : Fin 1, μ (A i) := by
      intro r
      rw [Fin.prod_univ_one]
      have hinter : (⋂ i : Fin 1, (T^[d r i]) ⁻¹' A i) = (T^[d r 0]) ⁻¹' A 0 := by
        ext x
        simp [Fin.forall_fin_one]
      rw [hinter]
      exact (hT.iterate (d r 0)).measure_preimage (hA 0).nullMeasurableSet
    simp only [hconst]
    exact tendsto_const_nhds
  · have hshift : ∀ r : ℕ,
        μ (⋂ i : Fin 2, (T^[d r i]) ⁻¹' A i) =
          μ (A 0 ∩ (T^[d r 1 - d r 0]) ⁻¹' A 1) := by
      intro r
      have hlt : d r 0 < d r 1 := by
        have := hd r 0 1 (by decide)
        omega
      have hadd : d r 1 = d r 0 + (d r 1 - d r 0) := by omega
      have hinter : (⋂ i : Fin 2, (T^[d r i]) ⁻¹' A i) =
          (T^[d r 0]) ⁻¹' (A 0 ∩ (T^[d r 1 - d r 0]) ⁻¹' A 1) := by
        ext x
        simp only [Set.mem_iInter, Fin.forall_fin_two, Set.mem_preimage, Set.mem_inter_iff]
        have hiter : (T^[d r 1]) x = (T^[d r 1 - d r 0]) ((T^[d r 0]) x) := by
          conv_lhs => rw [hadd, add_comm]
          exact Function.iterate_add_apply T (d r 1 - d r 0) (d r 0) x
        rw [hiter]
      rw [hinter]
      have hmeas : MeasurableSet (A 0 ∩ (T^[d r 1 - d r 0]) ⁻¹' A 1) :=
        (hA 0).inter ((T.measurable.iterate (d r 1 - d r 0)) (hA 1))
      exact (hT.iterate (d r 0)).measure_preimage hmeas.nullMeasurableSet
    simp_rw [hshift, Fin.prod_univ_two]
    have hdiff_top : Tendsto (fun r : ℕ => d r 1 - d r 0) atTop atTop := by
      refine tendsto_atTop_mono (fun r => ?_) tendsto_id
      dsimp only [id]
      have := hd r 0 1 (by decide)
      omega
    exact (hmix (A 0) (A 1) (hA 0) (hA 1)).comp hdiff_top
