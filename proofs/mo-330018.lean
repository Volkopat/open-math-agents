import OMAStatements.S_mo_330018

-- Problem mo-330018: on a Fort space (a set is open iff it misses the base point b or is cofinite), every map
-- f into [0, 1] has bounded range, and f is continuous iff for every eps > 0 only finitely many x have
-- dist (f x) (f b) >= eps.
-- Upstream: statements/mo-330018.lean (declaration OMA.S_mo_330018.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: the range lies in [0, 1]. If f is continuous, the preimage of the open ball of radius eps around f b is
-- open and contains b, so it is cofinite, and its complement is the set in question. Conversely, let s be open.
-- If f b is not in s, the preimage of s misses b and is open. If f b is in s, some ball of radius eps around f b
-- lies in s, so the complement of the preimage is contained in the finite set {x | eps <= dist (f x) (f b)}.

open Set Metric OMA.S_mo_330018

theorem OMA.solution : type_of% @OMA.S_mo_330018.main := by
  intro X _ _ b hF f
  have hF2 : ∀ U : Set X, IsOpen U ↔ b ∉ U ∨ Uᶜ.Finite := hF
  constructor
  · apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rintro _ ⟨x, rfl⟩
    exact (f x).2
  · constructor
    · intro hf ε hε
      have hopen : IsOpen (f ⁻¹' Metric.ball (f b) ε) := Metric.isOpen_ball.preimage hf
      rcases (hF2 _).mp hopen with hb | hfin
      · exact absurd (Metric.mem_ball_self hε) hb
      · apply hfin.subset
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, not_lt]
        exact hx
    · intro h
      rw [continuous_def]
      intro s hs
      rw [hF2]
      by_cases hbs : f b ∈ s
      · right
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs (f b) hbs
        apply (h ε hε).subset
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_preimage] at hx
        show ε ≤ dist (f x) (f b)
        by_contra hlt
        exact hx (hball (Metric.mem_ball.mpr (not_le.mp hlt)))
      · left
        exact hbs
