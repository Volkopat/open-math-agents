import OMAStatements.S_oeis_a071642

/-! A proof of Gallardo's conjecture for the all-ones polynomials.
The trace criterion also appears in Theorem 1.3 of Roland Bacher,
arXiv:math/0607413. -/

open Polynomial OMA.S_oeis_a071642 IntermediateField
open scoped IntermediateField

namespace AllOnesProof

private abbrev K := ZMod 2

private theorem coeff_one {n i : ℕ} (hi : i ≤ n) : (allOnes n).coeff i=1 := by
  classical
  simp [allOnes,coeff_X_pow,Finset.mem_range,hi]

private theorem degree_ones (n : ℕ) : (allOnes n).natDegree=n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ ((coeff_one (le_refl n)).trans_ne one_ne_zero)
  apply natDegree_sum_le_of_forall_le
  intro i hi
  simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

private theorem degree_P : P.natDegree=2 := by unfold P; compute_degree!

private theorem trace_square {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] (y : L) :
    Algebra.trace K L (y^2) = Algebra.trace K L y := by
  classical
  let b := Module.finBasis K L
  rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace b,
    map_pow,ZMod.trace_pow_card,ZMod.pow_card]

private theorem forward {n : ℕ} (hn : 2 ≤ n) (ir : Irreducible (allOnes n)) :
    Irreducible ((allOnes n).comp P) := by
  classical
  have parity : 2 ∣ n := by
    by_contra odd
    have root := ir.not_isRoot_of_natDegree_ne_one (by rw [degree_ones]; omega) (x:=(1:K))
    apply root
    simp only [IsRoot,allOnes,eval_finsetSum,eval_pow,eval_X,one_pow,Finset.sum_const,
      Finset.card_range,nsmul_eq_mul,mul_one]
    exact (ZMod.natCast_eq_zero_iff _ 2).mpr (by omega)
  have next : (allOnes n).nextCoeff=1 := by
    rw [nextCoeff_of_natDegree_pos (by rw [degree_ones]; omega),degree_ones]
    exact coeff_one (by omega)
  have monic : (allOnes n).Monic := monic_geom_sum_X (by omega)
  apply irreducible_comp monic (by unfold P; monicity; decide) ir
  intro L _ _ x hx
  have integral : IsIntegral K x := by
    by_contra h
    have z := minpoly.eq_zero h
    exact monic.ne_zero (hx ▸ z)
  let F := K⟮x⟯
  have : FiniteDimensional K F := adjoin.finiteDimensional integral
  let a := AdjoinSimple.gen K x
  have ta : Algebra.trace K F a = -1 := by
    simpa only [F,a,hx,next] using trace_adjoinSimpleGen integral
  have tone : Algebra.trace K F 1=0 := by
    rw [← map_one (algebraMap K F),Algebra.trace_algebraMap]
    change Module.finrank K K⟮x⟯ • (1:K)=0
    rw [adjoin.finrank integral,hx,degree_ones,nsmul_eq_mul,mul_one]
    exact (ZMod.natCast_eq_zero_iff _ 2).mpr parity
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_sub_C, natDegree_map,degree_P]
    decide
  · intro y hy
    change (P.map (algebraMap K F)-C a).eval y=0 at hy
    simp [P] at hy
    have equation : a=y^2+y+1 := (sub_eq_zero.mp hy).symm
    have traceEq := congrArg (Algebra.trace K F) equation
    rw [map_add,map_add,trace_square,tone,ta] at traceEq
    have twice (z : K) : z+z=0 := by rw [← two_mul,show (2:K)=0 by decide,zero_mul]
    rw [twice,zero_add] at traceEq
    exact (by decide : (-1 : K) ≠ 0) traceEq

private theorem unit_of_comp {f : K[X]} (h : IsUnit (f.comp P)) : IsUnit f := by
  have nz : f≠0 := fun z => h.ne_zero (by simp [z])
  have deg := natDegree_eq_zero_of_isUnit h
  rw [natDegree_comp,degree_P] at deg
  rw [isUnit_iff_degree_eq_zero,degree_eq_natDegree nz,show f.natDegree=0 by omega]
  rfl

private theorem backward {n : ℕ} (hn : 2 ≤ n) (h : Irreducible ((allOnes n).comp P)) :
    Irreducible (allOnes n) := by
  apply irreducible_iff.mpr
  refine ⟨fun u => ?_,?_⟩
  · have d := natDegree_eq_zero_of_isUnit u
    rw [degree_ones] at d
    omega
  · intro a b eq
    apply Or.imp unit_of_comp unit_of_comp
    exact h.isUnit_or_isUnit (by rw [eq,mul_comp])

end AllOnesProof

open AllOnesProof

theorem OMA.solution : type_of% @OMA.S_oeis_a071642.main := by
  ext n
  change (2 ≤ n ∧ Irreducible (allOnes n)) ↔
    Irreducible (∑ i ∈ Finset.range (n+1), P^i)
  rw [← show (allOnes n).comp P = ∑ i ∈ Finset.range (n+1), P^i by simp [allOnes]]
  constructor
  · rintro ⟨hn,ir⟩
    exact forward hn ir
  · intro h
    have large : 2 ≤ n := by
      by_contra! small
      interval_cases n
      · simp [allOnes] at h
      · apply h.not_isRoot_of_natDegree_ne_one (by rw [natDegree_comp,degree_ones,degree_P]; decide)
          (x:=(0:K))
        norm_num [IsRoot,allOnes,P,Finset.sum_range_succ]
        decide
    exact ⟨large,backward large h⟩
