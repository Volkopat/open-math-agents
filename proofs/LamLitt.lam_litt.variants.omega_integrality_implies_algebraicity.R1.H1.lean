import OMAReductions.R_LamLitt_lam_litt_variants_omega_integrality_implies_algebraicity_R1
import Mathlib

-- Step LamLitt.lam_litt.variants.omega_integrality_implies_algebraicity.R1.H1: hypothesis H1 of reduction LamLitt.lam_litt.variants.omega_integrality_implies_algebraicity.R1
-- Credit: @ivillar. Order zero: f q(z) = p(z) with q(0) != 0. With N = |num q(0)| times the denominators of all coefficients of p and q, all coefficients of p(z), q(z) and 1/q(0) lie in Z[1/N], and the recurrence q(0) f_n = p_n - sum_{i<n} f_i q_{n-i} keeps every f_n in Z[1/N].

/-! Step LamLitt.lam_litt.variants.omega_integrality_implies_algebraicity.R1.H1. -/

open PowerSeries LamLitt

namespace P8LamLitt

lemma div_mem (N b : ℕ) (hN : N ≠ 0) (a : ℤ) (hb : b ∣ N) :
    ((a : ℚ) / (b : ℚ)) ∈ ℤAdjoinInvNat N := by
  obtain ⟨k, rfl⟩ := hb
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h
    apply hN
    have : b = 0 := by exact_mod_cast h
    simp [this]
  have hk0 : (k : ℚ) ≠ 0 := by
    intro h
    apply hN
    have : k = 0 := by exact_mod_cast h
    simp [this]
  have e : (a : ℚ) / (b : ℚ) = ((a * k : ℤ) : ℚ) * (1 / ((b * k : ℕ) : ℚ)) := by
    push_cast
    field_simp
  rw [e]
  apply Subalgebra.mul_mem
  · exact Subalgebra.algebraMap_mem _ (a * k)
  · exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- Power series all of whose coefficients lie in `ℤ[1/N]`. -/
def S (N : ℕ) : Subring ℚ⟦X⟧ where
  carrier := {F | ∀ n, coeff n F ∈ ℤAdjoinInvNat N}
  mul_mem' := by
    intro a b ha hb n
    rw [coeff_mul]
    exact Subalgebra.sum_mem _ (fun p _ => Subalgebra.mul_mem _ (ha p.1) (hb p.2))
  one_mem' := by
    intro n
    rw [coeff_one]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  add_mem' := by
    intro a b ha hb n
    rw [map_add]
    exact Subalgebra.add_mem _ (ha n) (hb n)
  zero_mem' := by
    intro n
    rw [map_zero]
    exact Subalgebra.zero_mem _
  neg_mem' := by
    intro a ha n
    rw [map_neg]
    exact Subalgebra.neg_mem _ (ha n)

lemma C_mem (N : ℕ) (a : ℚ) (ha : a ∈ ℤAdjoinInvNat N) : (C a : ℚ⟦X⟧) ∈ S N := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact Subalgebra.zero_mem _

lemma X_mem (N : ℕ) : (X : ℚ⟦X⟧) ∈ S N := by
  intro n
  rw [coeff_X]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

lemma aeval_mem (N : ℕ) (pt : Fin 1 → ℚ⟦X⟧) (hpt : ∀ i, pt i = X) (r : MvPolynomial (Fin 1) ℚ)
    (hr : ∀ m ∈ r.support, r.coeff m ∈ ℤAdjoinInvNat N) :
    MvPolynomial.aeval pt r ∈ S N := by
  conv => arg 2; rw [MvPolynomial.as_sum r]
  rw [map_sum]
  apply Subring.sum_mem
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  apply Subring.mul_mem
  · exact C_mem N _ (hr m hm)
  · apply Subring.prod_mem
    intro i _
    show pt i ^ (m i) ∈ S N
    rw [hpt i]
    exact Subring.pow_mem _ (X_mem N) _

lemma den_dvd_prod (r : MvPolynomial (Fin 1) ℚ) (m) (hm : m ∈ r.support) :
    (r.coeff m).den ∣ ∏ m' ∈ r.support, (r.coeff m').den :=
  Finset.dvd_prod_of_mem _ hm

lemma cc_aeval (pt : Fin 1 → ℚ⟦X⟧) (q : MvPolynomial (Fin 1) ℚ) :
    constantCoeff (MvPolynomial.aeval pt q) = MvPolynomial.eval (constantCoeff ∘ pt) q := by
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  have h : (constantCoeff : ℚ⟦X⟧ →+* ℚ).comp (algebraMap ℚ ℚ⟦X⟧) = RingHom.id ℚ :=
    Subsingleton.elim _ _
  rw [h]
  rfl

lemma core (f : ℚ⟦X⟧) (pt : Fin 1 → ℚ⟦X⟧) (hpt : ∀ i, pt i = X)
    (p q : MvPolynomial (Fin 1) ℚ) (hq0 : q.eval (constantCoeff ∘ pt) ≠ 0)
    (heq : f * MvPolynomial.aeval pt q = MvPolynomial.aeval pt p) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  have hq0ne' : constantCoeff (MvPolynomial.aeval pt q) ≠ 0 := by
    rw [cc_aeval]
    exact hq0
  set P := MvPolynomial.aeval pt p with hP
  set Q := MvPolynomial.aeval pt q with hQ
  set q0 := constantCoeff Q with hq0def
  have hq0ne : q0 ≠ 0 := hq0ne'
  set N := q0.num.natAbs * ((∏ m ∈ p.support, (p.coeff m).den) *
    ∏ m ∈ q.support, (q.coeff m).den) with hN
  have hnum0 : q0.num ≠ 0 := Rat.num_ne_zero.mpr hq0ne
  have hN0 : N ≠ 0 := by
    rw [hN]
    apply Nat.mul_ne_zero
    · exact Int.natAbs_ne_zero.mpr hnum0
    · apply Nat.mul_ne_zero <;>
        exact Finset.prod_ne_zero_iff.mpr (fun m _ => Rat.den_ne_zero _)
  have hcoef : ∀ (r : MvPolynomial (Fin 1) ℚ) (m), (r.coeff m).den ∣ N →
      r.coeff m ∈ ℤAdjoinInvNat N := by
    intro r m hd
    rw [← Rat.num_div_den (r.coeff m)]
    exact div_mem N _ hN0 _ hd
  have hPS : P ∈ S N := aeval_mem N pt hpt p (fun m hm => hcoef p m (by
    rw [hN]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (den_dvd_prod p m hm) _) _))
  have hQS : Q ∈ S N := aeval_mem N pt hpt q (fun m hm => hcoef q m (by
    rw [hN]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (den_dvd_prod q m hm) _) _))
  have hinv : q0⁻¹ ∈ ℤAdjoinInvNat N := by
    have hinvq : q0⁻¹ = (q0.den : ℚ) / (q0.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den q0]
      rw [inv_div]
    have hb : ((q0.num.natAbs : ℕ) : ℚ) = |(q0.num : ℚ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hdvd : q0.num.natAbs ∣ N := by
      rw [hN]
      exact Nat.dvd_mul_right _ _
    rcases lt_or_gt_of_ne (show (q0.num : ℚ) ≠ 0 by exact_mod_cast hnum0) with hneg | hpos
    · have e : q0⁻¹ = ((-(q0.den : ℤ) : ℤ) : ℚ) / ((q0.num.natAbs : ℕ) : ℚ) := by
        rw [hinvq, hb, abs_of_neg hneg]
        push_cast
        rw [neg_div_neg_eq]
      rw [e]
      exact div_mem N _ hN0 _ hdvd
    · have e : q0⁻¹ = (((q0.den : ℤ)) : ℚ) / ((q0.num.natAbs : ℕ) : ℚ) := by
        rw [hinvq, hb, abs_of_pos hpos]
        push_cast
        rfl
      rw [e]
      exact div_mem N _ hN0 _ hdvd
  refine ⟨N, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (coeff n) heq
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] at hc
    simp only [Nat.sub_self] at hc
    have h0 : coeff 0 Q = q0 := by rw [hq0def, coeff_zero_eq_constantCoeff_apply]
    rw [h0] at hc
    have hfn : coeff n f =
        (coeff n P - ∑ i ∈ Finset.range n, coeff i f * coeff (n - i) Q) * q0⁻¹ := by
      rw [← hc]
      field_simp
      ring
    rw [hfn]
    apply Subalgebra.mul_mem _ _ hinv
    apply Subalgebra.sub_mem _ (hPS n)
    apply Subalgebra.sum_mem
    intro i hi
    exact Subalgebra.mul_mem _ (ih i (Finset.mem_range.mp hi)) (hQS (n - i))

theorem order_zero : ∀ (f : PowerSeries ℚ) (g : MvRatFunc (Fin 1) ℚ),
    IsSolutionOfAlgebraicODE 0 f g → ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  intro f g hODE
  obtain ⟨p, q, -, hq0, heq⟩ := hODE
  exact core f _ (fun i => by fin_cases i; rfl) p q hq0 heq

end P8LamLitt

theorem OMA.solution : OMA.R_LamLitt_lam_litt_variants_omega_integrality_implies_algebraicity_R1.H1 :=
  P8LamLitt.order_zero
