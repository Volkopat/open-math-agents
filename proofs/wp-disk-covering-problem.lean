import OMAStatements.S_wp_disk_covering_problem

open Set Metric OMA.S_wp_disk_covering_problem

private theorem exists_least_radius (n : ℕ) (hn : 0 < n) :
    ∃ r : ℝ, IsLeast {radius | IsCoveringRadius n radius} r := by
  classical
  let K : Set (ℝ × (Fin n → Plane)) :=
    Icc 0 1 ×ˢ pi univ (fun _ : Fin n => closedBall (0 : Plane) 2)
  let C : Set (ℝ × (Fin n → Plane)) :=
    {q | ∀ x ∈ closedBall (0 : Plane) 1, ∃ i : Fin n, dist x (q.2 i) ≤ q.1}
  have compactK : IsCompact K :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  have closedC : IsClosed C := by
    have eqC : C = ⋂ x : Plane, ⋂ _ : x ∈ closedBall (0 : Plane) 1,
        ⋃ i : Fin n, {q : ℝ × (Fin n → Plane) | dist x (q.2 i) ≤ q.1} := by
      ext q
      simp [C]
    rw [eqC]
    refine isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_iUnion_of_finite fun i => ?_
    exact isClosed_le (continuous_const.dist ((continuous_apply i).comp continuous_snd))
      continuous_fst
  have feasible : (K ∩ C).Nonempty := by
    refine ⟨(1, fun _ => 0), ⟨?_, ?_⟩⟩
    · simp [K]
    · exact fun x hx => ⟨⟨0, hn⟩, hx⟩
  obtain ⟨r, hr⟩ := ((compactK.inter_right closedC).image continuous_fst).exists_isLeast
    (feasible.image Prod.fst)
  obtain ⟨q, ⟨hqK, hqC⟩, rfl⟩ := hr.1
  refine ⟨q.1, ⟨⟨q.2, ?_⟩, ?_⟩⟩
  · intro x hx
    exact mem_iUnion.mpr (hqC x hx)
  · intro r' hr'
    by_cases hle : r' ≤ 1
    · obtain ⟨centers, hcover⟩ := hr'
      have hr0 : 0 ≤ r' := by
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (show (0 : Plane) ∈ closedBall 0 1 by simp))
        exact dist_nonneg.trans hi
      let boundedCenters (i : Fin n) : Plane :=
        if centers i ∈ closedBall (0 : Plane) 2 then centers i else 0
      have hbounded : (r', boundedCenters) ∈ K := by
        refine ⟨⟨hr0, hle⟩, ?_⟩
        intro i hi
        dsimp [boundedCenters]
        split
        · assumption
        · simp
      have hnew : (r', boundedCenters) ∈ C := by
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
        refine ⟨i, ?_⟩
        have hcenter : centers i ∈ closedBall (0 : Plane) 2 := by
          have hdist : dist (centers i) x ≤ r' := by simpa [dist_comm] using hi
          change dist (centers i) 0 ≤ 2
          change dist x 0 ≤ 1 at hx
          linarith [dist_triangle (centers i) x (0 : Plane)]
        simpa only [boundedCenters, if_pos hcenter] using (mem_closedBall.mp hi)
      exact hr.2 ⟨(r', boundedCenters), ⟨hbounded, hnew⟩, rfl⟩
    · exact le_trans hqK.1.2 (le_of_not_ge hle)

theorem OMA.solution : type_of% @OMA.S_wp_disk_covering_problem.main := by
  classical
  choose r hr using exists_least_radius
  exact ⟨fun n => if hn : 0 < n then r n hn else 0, fun n hn => by simpa [hn] using hr n hn⟩