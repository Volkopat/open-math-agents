import FormalConjectures.ErdosProblems.«395»

theorem OMA.solution : type_of% @Erdos395.erdos_395.variants.one := by
  rintro ⟨c, hc, h⟩
  have key := h 2 (by norm_num) ![1, Complex.I] (by intro i; fin_cases i <;> simp)
  generalize hz : (![1, Complex.I] : Fin 2 → ℂ) = z at key
  have : Erdos395.signedSumCount z 1 = 0 :=
    (congrArg Set.ncard (Set.eq_empty_of_forall_notMem fun ε hε => by
      have hεsq (i) : (ε i : ℝ) ^ 2 = 1 := by exact_mod_cast sq_eq_one_iff.mpr (hε.1 i).symm
      have : ‖∑ i, (ε i : ℂ) * z i‖ ^ 2 = 2 := by
        subst hz
        norm_num [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply, ← sq, hεsq]
      nlinarith [norm_nonneg (∑ i, (ε i : ℂ) * z i), hε.2])).trans (Set.ncard_empty _)
  norm_num [this] at key
  linarith
