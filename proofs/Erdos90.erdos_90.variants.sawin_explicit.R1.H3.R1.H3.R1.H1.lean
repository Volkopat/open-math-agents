import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H3_R1

/-! The roots-of-unity estimate in Will Sawin, "An explicit lower bound for
the unit distance problem", Lemma 9. We bound the prime factors in the
cyclotomic discriminant and compare discriminants in towers. -/
namespace OMA.CycloSawin90
open NumberField Finset Module
open scoped IntermediateField

private theorem prime_product (n m : ℕ) (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, p ^ (m / (p-1)))^2 ≤ (2*n)^m := by
  let S := n.primeFactors
  have individual (p) (hp : p ∈ S) :
      (p ^ (m / (p-1)))^2 ≤ (if p = 2 then 2^m else 1) * p^m := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    split_ifs with eq
    · subst p
      simp [sq]
    · rw [one_mul,← pow_mul]
      apply Nat.pow_le_pow_right hprime.pos
      have hp3 : 2 ≤ p-1 := by have := hprime.two_le; omega
      have hh := Nat.div_mul_le_self m (p-1)
      exact (Nat.mul_le_mul_left _ hp3).trans hh
  calc _ = ∏ p ∈ S, (p ^ (m / (p-1)))^2 := (prod_pow ..).symm
       _ ≤ ∏ p ∈ S, (if p = 2 then 2^m else 1) * p^m :=
         prod_le_prod' individual
       _ = (if 2 ∈ S then 2^m else 1) * (∏ p ∈ S, p)^m := by
         rw [prod_mul_distrib,prod_pow]
         simp
       _ ≤ 2^m * n^m := by
         apply Nat.mul_le_mul
         · split_ifs <;> first | rfl | exact Nat.one_le_pow _ _ (by decide)
         · exact Nat.pow_le_pow_left (Nat.le_of_dvd hn n.prod_primeFactors_dvd) _
       _ = _ := (mul_pow ..).symm

private theorem cyclo_nat (E : Type*) [Field E] [NumberField E]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ E] :
    n ^ n.totient ≤ 2 ^ n.totient * (discr E).natAbs ^ 2 := by
  let q := ∏ p ∈ n.primeFactors, p ^ (n.totient/(p-1))
  have e : (discr E).natAbs = n^n.totient/q := by
    rw [IsCyclotomicExtension.Rat.discr n E]
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,one_pow,one_mul]
    rw [← Int.natCast_pow, ← Int.natCast_div]
    rfl
  have prod_eq : (discr E).natAbs * q = n^n.totient := by
    rw [e, Nat.div_mul_cancel (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos n))]
  have hq : 0 < q := Finset.prod_pos fun p hp => Nat.pow_pos (Nat.prime_of_mem_primeFactors hp).pos
  have h := prime_product n n.totient (NeZero.pos n)
  change q^2 ≤ _ at h
  rw [mul_pow,← prod_eq,sq,← Nat.mul_assoc] at h
  have h' := Nat.le_of_mul_le_mul_right h hq
  calc _ = (discr E).natAbs * q := prod_eq.symm
       _ ≤ (discr E).natAbs * (2^n.totient * (discr E).natAbs) := Nat.mul_le_mul_left _ h'
       _ = _ := by ring

private theorem discr_tower (E K : Type*) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] : (discr E).natAbs ^ finrank E K ≤ (discr K).natAbs := by
  have eq := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) K (𝓞 K)
  have positive : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  rw [eq] at positive ⊢
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right positive)

/-- Torsion in any number field is bounded by twice the square of its
root discriminant. The stated equivalent integral inequality avoids roots. -/
theorem torsion_discr (K : Type*) [Field K] [NumberField K] :
    Units.torsionOrder K ^ finrank ℚ K ≤ 2 ^ finrank ℚ K * (discr K).natAbs ^ 2 := by
  let n := Units.torsionOrder K
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)
  have prim : IsPrimitiveRoot u n := by
    change IsPrimitiveRoot u (Nat.card (Units.torsion K))
    rw [← hu]
    exact IsPrimitiveRoot.orderOf u
  let z : K := algebraMap (𝓞 K) K (u.val : 𝓞 K)
  have hζ : IsPrimitiveRoot z n :=
    (IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.coe_submonoidClass_iff.mpr prim)).map_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  let E := ℚ⟮z⟯
  let : IsCyclotomicExtension {n} ℚ E := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have dE : finrank ℚ E = n.totient :=
    IsCyclotomicExtension.finrank E (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))
  have h := cyclo_nat E n
  rw [← dE] at h
  have step := Nat.pow_le_pow_left h (finrank E K)
  change n^_ ≤ _
  rw [← finrank_mul_finrank ℚ E K, pow_mul, pow_mul]
  refine step.trans ?_
  rw [mul_pow,pow_right_comm (discr E).natAbs]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (discr_tower E K) 2)

/-- The form entering Sawin's relative class-number bound. -/
theorem torsion_le (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] (lam : ℝ) (hlam : 0 ≤ lam)
    (hr : |(discr K : ℝ)| / |(discr F : ℝ)| ≤ lam ^ finrank ℚ F) :
    (Units.torsionOrder K : ℝ) ≤ 2 * lam^2 := by
  have deg : finrank ℚ K = finrank ℚ F * 2 := by
    rw [← finrank_mul_finrank ℚ F K, Algebra.IsQuadraticExtension.finrank_eq_two F K]
  have cpos : 0 < |(discr F : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F))
  have dr := discr_tower F K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F K] at dr
  have le_disc : |(discr F : ℝ)| ^ 2 ≤ |(discr K : ℝ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (show ((discr F).natAbs : ℝ)^2 ≤ ((discr K).natAbs : ℝ) by exact_mod_cast dr)
  have hK := (div_le_iff₀ cpos).mp hr
  have hF : |(discr F : ℝ)| ≤ lam^finrank ℚ F := by
    apply le_of_mul_le_mul_right _ cpos
    simpa only [← sq] using le_disc.trans hK
  have disc_cap : |(discr K : ℝ)| ≤ lam^finrank ℚ K := by
    rw [deg, pow_mul, sq]
    exact hK.trans (mul_le_mul_of_nonneg_left hF (pow_nonneg hlam _))
  have raw := torsion_discr K
  have rb : (Units.torsionOrder K : ℝ)^finrank ℚ K ≤
      2^finrank ℚ K * |(discr K : ℝ)|^2 := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (show (Units.torsionOrder K : ℝ)^finrank ℚ K ≤
        2^finrank ℚ K*((discr K).natAbs : ℝ)^2 by exact_mod_cast raw)
  apply le_of_pow_le_pow_left₀ (n := finrank ℚ K) finrank_pos.ne' (by positivity)
  rw [mul_pow, pow_right_comm lam]
  exact rb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) disc_cap 2)
    (by positivity))

end OMA.CycloSawin90

theorem OMA.solution : OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H3_R1.H1 := by
  intro F K _ _ _ _ _ _ lam h hdisc
  exact OMA.CycloSawin90.torsion_le F K lam (by linarith) hdisc
