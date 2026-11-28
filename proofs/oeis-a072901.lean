import OMAStatements.S_oeis_a072901
import Mathlib

-- Problem: A072901: Composite numbers n such that the discriminant of the quadratic field Q(sqrt(n)) equals 4n.
-- Upstream: formal-conjectures statements/oeis-a072901.lean:0 (declaration OMA.S_oeis_a072901.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.A072901Proof

open OMA.S_oeis_a072901 NumberField Module Polynomial Matrix

theorem discr_family {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℚ K) (v : ι → K) (hv : ∀ i, IsIntegral ℤ (v i)) :
    ∃ d : ℤ, Algebra.discr ℚ v = (d : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by
  classical
  let e := b.indexEquiv (integralBasis K)
  let b₁ : Basis ι ℚ K := (integralBasis K).reindex e.symm
  let Q : Matrix ι ι ℤ := fun i j => (RingOfIntegers.basis K).repr ⟨v i, hv i⟩ (e j)
  let P : Matrix ι ι ℚ := Q.map (Int.castRingHom ℚ)
  have hP : (P.map (algebraMap ℚ K)) *ᵥ b₁ = v := by
    funext i
    have h1 : ∀ j, b₁.repr (v i) j = ((Q i j : ℤ) : ℚ) := by
      intro j
      have h := integralBasis_repr_apply (K := K) (⟨v i, hv i⟩ : 𝓞 K) (e j)
      have h' : b₁.repr (v i) j = (integralBasis K).repr (v i) (e j) := by simp [b₁]
      rw [h']; exact h
    calc (P.map (algebraMap ℚ K) *ᵥ b₁) i = ∑ j, b₁.repr (v i) j • b₁ j := by
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, h1, Algebra.smul_def]
          rfl
      _ = v i := b₁.sum_repr (v i)
  refine ⟨Q.det, ?_⟩
  rw [← hP, Algebra.discr_of_matrix_mulVec, coe_discr]
  have hdet : P.det = ((Q.det : ℤ) : ℚ) := by
    have := (Int.castRingHom ℚ).map_det Q
    simpa [P] using this.symm
  have hre : Algebra.discr ℚ (b₁ : ι → K) = Algebra.discr ℚ (integralBasis K) := by
    have := Algebra.discr_reindex ℚ (integralBasis K) e.symm
    simpa [b₁, Basis.coe_reindex] using this
  rw [hdet, hre]

theorem discr_of_rational (n : ℕ) (h : ∃ b : ℚ, b ^ 2 = (n : ℚ)) :
    NumberField.discr (sqrtField n) = 1 := by
  obtain ⟨b, hb⟩ := h
  have hmem : Real.sqrt (n : ℝ) ∈ (⊥ : IntermediateField ℚ ℝ) := by
    rw [IntermediateField.mem_bot]
    refine ⟨|b|, ?_⟩
    have h2 : (n : ℝ) = ((|b| : ℚ) : ℝ) ^ 2 := by
      have h3 : ((b ^ 2 : ℚ) : ℝ) = ((n : ℚ) : ℝ) := by rw [hb]
      push_cast at h3
      rw [← h3]; push_cast; rw [sq_abs]
    rw [h2, Real.sqrt_sq (by positivity)]
    rfl
  have hbot : sqrtField n = ⊥ := by
    unfold sqrtField
    exact IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem
  let f : sqrtField n ≃ₐ[ℚ] ℚ :=
    (IntermediateField.equivOfEq hbot).trans (IntermediateField.botEquiv ℚ ℝ)
  rw [NumberField.discr_eq_discr_of_algEquiv (K := sqrtField n) f]
  exact Rat.numberField_discr

theorem caseB (n p k : ℕ) (hp : p.Prime) (hk : n = p * p * k) (hn : 0 < n)
    (hno : ¬ ∃ b : ℚ, b ^ 2 = (n : ℚ)) :
    NumberField.discr (sqrtField n) ≠ 4 * (n : ℤ) := by
  intro hdisc
  have hα : IsIntegral ℚ (Real.sqrt (n : ℝ)) := by
    refine ⟨X ^ 2 - C (n : ℚ), monic_X_pow_sub_C _ (by decide), ?_⟩
    simp [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hirr : Irreducible (X ^ 2 - C (n : ℚ) : ℚ[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hno ⟨b, hb⟩)
  have hmin : minpoly ℚ (Real.sqrt (n : ℝ)) = X ^ 2 - C (n : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C _ (by decide))).symm
    simp [Real.sq_sqrt (Nat.cast_nonneg n)]
  let pb : PowerBasis ℚ (sqrtField n) := IntermediateField.adjoin.powerBasis hα
  have hfin : finrank ℚ (sqrtField n) = 2 := by
    have h := IntermediateField.adjoin.finrank hα
    rw [hmin, natDegree_X_pow_sub_C] at h
    exact h
  let x : sqrtField n := pb.gen
  have hxx : x * x = algebraMap ℚ (sqrtField n) (n : ℚ) := by
    apply Subtype.ext
    show Real.sqrt n * Real.sqrt n = ((n : ℚ) : ℝ)
    rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]; simp
  have htrx : Algebra.trace ℚ (sqrtField n) x = 0 := by
    have h := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
    have h2 : minpoly ℚ pb.gen = X ^ 2 - C (n : ℚ) := by
      rw [← hmin]
      exact IntermediateField.minpoly_gen ℚ _
    have h3 : (X ^ 2 - C (n : ℚ) : ℚ[X]).nextCoeff = 0 := by
      rw [nextCoeff, natDegree_X_pow_sub_C]
      simp [coeff_X_pow]
    rw [h2, h3, neg_zero] at h
    exact h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let y : sqrtField n := (p : ℚ)⁻¹ • x
  have hyy : y * y = algebraMap ℚ (sqrtField n) (k : ℚ) := by
    show ((p : ℚ)⁻¹ • x) * ((p : ℚ)⁻¹ • x) = _
    rw [smul_mul_smul_comm, hxx, Algebra.smul_def, ← map_mul]
    congr 1
    rw [hk]; push_cast; field_simp
  have htr1 : ∀ q : ℚ,
      Algebra.trace ℚ (sqrtField n) (algebraMap ℚ (sqrtField n) q) = 2 * q := by
    intro q; rw [Algebra.trace_algebraMap, hfin]; simp
  have htry : Algebra.trace ℚ (sqrtField n) y = 0 := by
    show Algebra.trace ℚ (sqrtField n) ((p : ℚ)⁻¹ • x) = 0
    rw [map_smul, htrx, smul_zero]
  let v : Fin 2 → sqrtField n := ![1, y]
  have hd : Algebra.discr ℚ v = 4 * (k : ℚ) := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one]
    rw [hyy, htry, htr1,
      show (1 : sqrtField n) = algebraMap ℚ (sqrtField n) 1 from (map_one _).symm, htr1]
    ring
  have hint : ∀ i, IsIntegral ℤ (v i) := by
    intro i
    fin_cases i
    · exact isIntegral_one
    · show IsIntegral ℤ y
      refine IsIntegral.of_pow two_pos ?_
      rw [pow_two, hyy, map_natCast]
      exact isIntegral_natCast k
  obtain ⟨d, hd2⟩ := discr_family (finBasisOfFinrankEq ℚ (sqrtField n) hfin) v hint
  rw [hd, hdisc] at hd2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; omega
    · exact h
  have hz : 4 * (k : ℤ) = d ^ 2 * (4 * (p * p * k)) := by
    rw [hk] at hd2; exact_mod_cast hd2
  have h1 : d ^ 2 * (p * p) = (1 : ℤ) := by
    have hk' : (4 * (k : ℤ)) ≠ 0 := by
      have : (0 : ℤ) < k := by exact_mod_cast hk0
      omega
    apply mul_left_cancel₀ hk'
    linear_combination (-1 : ℤ) * hz
  have hdvd : (p : ℤ) ∣ 1 := ⟨d ^ 2 * p, by linear_combination (-1 : ℤ) * h1⟩
  have h5 := Int.le_of_dvd one_pos hdvd
  have h6 := hp.two_le
  omega

end OMA.A072901Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a072901.main := by
  intro n hn1 _ hdisc
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hdvd
  obtain ⟨k, hk⟩ := hdvd
  by_cases h : ∃ b : ℚ, b ^ 2 = (n : ℚ)
  · rw [OMA.A072901Proof.discr_of_rational n h] at hdisc
    omega
  · exact OMA.A072901Proof.caseB n p k hp hk (by omega) h hdisc
