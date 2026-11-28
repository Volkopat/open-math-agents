import OMAStatements.S_mo_247291

-- Problem mo-247291: the statement claims that if U is unitary and conj(U) * U = D is diagonal with unit-modulus
-- entries, then D^2 = 1.
-- Upstream: statements/mo-247291.lean (declaration OMA.S_mo_247291.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take n = 2 and U = [[0, 1], [i, 0]]. U is unitary, conj(U) * U = diag(i, -i), whose entries have
-- modulus 1, but diag(i, -i)^2 = -1 is not the identity.

open Matrix

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_247291.main) := by
  intro h
  have hU : (!![0, 1; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  have hd : ∀ i : Fin 2, ‖(![Complex.I, -Complex.I] : Fin 2 → ℂ) i‖ = 1 := by
    intro i
    fin_cases i <;> simp
  have heq : (!![0, 1; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ).map star * !![0, 1; Complex.I, 0]
      = Matrix.diagonal ![Complex.I, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have h2 := h 2 _ hU _ hd heq
  have h00 := congrFun (congrFun h2 0) 0
  simp [pow_two, Matrix.mul_apply, Matrix.diagonal, Complex.ext_iff] at h00
  norm_num at h00
