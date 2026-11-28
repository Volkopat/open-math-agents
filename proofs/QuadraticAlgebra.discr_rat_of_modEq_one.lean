import FormalConjectures.Wikipedia.WallSunSun

/-! # The discriminant of a squarefree quadratic field when d is one modulo four -/
-- Original proof: @steveDOTdigital. Trace and basis simplifications: @Ciphore.

namespace OMA.QuadraticDisc
open QuadraticAlgebra NumberField Polynomial
variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]
private abbrev K (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0
private def beta (d : ℤ) : K d := ⟨1/2,1/2⟩
private theorem tr (x : K d) : Algebra.trace ℚ (K d) x = 2 * x.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis _ _), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]
  ring
private theorem integral_beta (hd : d ≡ 1 [ZMOD 4]) : IsIntegral ℤ (beta d) := by
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp hd
  refine ⟨X^2 - X + C t, ?_, ?_⟩
  · monicity!
  · change aeval (beta d) (X ^ 2 - X + C t) = 0
    simp only [map_add, map_sub, map_pow, aeval_X, aeval_C]
    have htQ : (1 : ℚ) - d = 4 * t := by exact_mod_cast ht
    ext <;> norm_num [beta, pow_two] <;> linarith [htQ]
private theorem disc_beta : Algebra.discr ℚ ![(1 : K d), beta d] = (d : ℚ) := by
  simp [Algebra.discr_def, Matrix.det_fin_two, Algebra.traceMatrix_apply, Algebra.traceForm_apply, tr, beta]
  ring
theorem fieldDiscr (hd : d ≡ 1 [ZMOD 4]) : NumberField.discr (K d) = d := by
  classical
  let e := (integralBasis (K d)).indexEquiv (QuadraticAlgebra.basis (d : ℚ) 0)
  let b := (integralBasis (K d)).reindex e
  let v : Fin 2 → K d := ![1, beta d]
  let M := b.toMatrix v
  have hint (i j : Fin 2) : IsIntegral ℤ (M i j) := by
    have hv : IsIntegral ℤ (v j) := by
      fin_cases j
      · exact isIntegral_one
      · exact integral_beta hd
    let a : 𝓞 (K d) := ⟨v j, hv⟩
    change IsIntegral ℤ (b.repr (algebraMap (𝓞 (K d)) (K d) a) i)
    rw [Module.Basis.repr_reindex_apply, integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hint)
  have h := Algebra.discr_of_matrix_vecMul b M
  rw [b.toMatrix_map_vecMul v, disc_beta, ← hn] at h
  simp only [b, Module.Basis.coe_reindex, Algebra.discr_reindex, ← NumberField.coe_discr] at h
  change (d : ℚ) = (n : ℚ)^2 * (NumberField.discr (K d) : ℚ) at h
  have h' : d = n^2 * NumberField.discr (K d) := by exact_mod_cast h
  have hu : IsUnit n := (Fact.out : Squarefree d) n ⟨_, by simpa [pow_two] using h'⟩
  simpa [pow_two, Int.isUnit_mul_self hu] using h'.symm
end OMA.QuadraticDisc

theorem OMA.solution : type_of% @QuadraticAlgebra.discr_rat_of_modEq_one := by
  intro d _ _ hd
  exact OMA.QuadraticDisc.fieldDiscr hd
