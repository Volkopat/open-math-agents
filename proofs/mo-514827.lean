import OMAStatements.S_mo_514827

-- Problem mo-514827: there is a group homomorphism from (R, +) to the permutations of N with countable kernel.
-- Upstream: statements/mo-514827.lean (declaration OMA.S_mo_514827.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Shortening also credits @PrimordialAA's pending #29676 for the standard translation-equivalence approach.
-- Proof: we construct an injective one. As Q-vector spaces, R and Q^N both have dimension continuum
-- (Real.rank_rat_real and the Erdos-Kaplansky theorem rank_fun_infinite), so there is a Q-linear bijection
-- E : R -> Q^N. The group Q^N acts faithfully on N x Q by (n, q) -> (n, q + g n), and N x Q is in bijection with
-- N. Composing gives an injective homomorphism from R into the permutations of N, whose kernel is trivial.

open Cardinal

theorem OMA.solution : type_of% @OMA.S_mo_514827.main := by
  have hrank : Module.rank ℚ ℝ = Module.rank ℚ (ℕ → ℚ) := by
    rw [Real.rank_rat_real, rank_fun_infinite]
    simp
  obtain ⟨E⟩ := nonempty_linearEquiv_of_rank_eq hrank
  let D : ℕ × ℚ ≃ ℕ := Denumerable.eqv (ℕ × ℚ)
  let f : Multiplicative ℝ →* Equiv.Perm ℕ :=
    { toFun := fun x => D.permCongr (Equiv.prodCongrRight fun n => Equiv.addRight (E (Multiplicative.toAdd x) n))
      map_one' := by
        ext n
        simp [Equiv.prodCongrRight, Equiv.permCongr_apply]
      map_mul' := by
        intro x y
        ext n
        simp [Equiv.prodCongrRight, Equiv.permCongr_apply, add_comm, add_left_comm] }
  refine ⟨f, ?_⟩
  apply Set.Countable.mono _ (Set.countable_singleton (1 : Multiplicative ℝ))
  intro x hx
  have hx1 : f x = 1 := MonoidHom.mem_ker.mp hx
  have hE : E (Multiplicative.toAdd x) = 0 := by
    funext n
    have h := congrArg (fun σ : Equiv.Perm ℕ => D.symm (σ (D (n, 0)))) hx1
    simp [f, Equiv.prodCongrRight, Equiv.permCongr_apply] at h
    exact h
  have h0 : Multiplicative.toAdd x = 0 := E.injective (hE.trans (map_zero E).symm)
  simpa using h0
