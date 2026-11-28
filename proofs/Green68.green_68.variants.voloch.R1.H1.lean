import OMAReductions.R_Green68_green_68_variants_voloch_R1

/-!
# Voloch's Theorem on Large Arcs in Prime Projective Planes

This file proves `OMA.R_Green68_green_68_variants_voloch_R1.H1` by formalizing Voloch's 1990
theorem: for any odd prime `p`, every arc in `F_p^2` of size strictly greater than
`(44 / 45) * p + 8 / 9` lies on a nonzero conic.
-/


namespace Green68Voloch

open Finset

namespace Mv
export MvPolynomial (C C_mul_monomial X X_ne_zero aeval aeval_C aeval_X aeval_monomial algebraMap_eq as_sum coeff coeff_C coeff_C_mul coeff_X coeff_add coeff_homogeneousComponent coeff_map coeff_monomial coeff_mul coeff_neg coeff_one coeff_pderiv coeff_sum coeff_zero constantCoeff_eq eval eval_C eval_X eval_eq' eval_eq_eval_mv_eval' eval_map eval_monomial eval_zero finSuccEquiv hom_eval₂ homogeneousComponent homogeneousComponent_isHomogeneous induction_on induction_on' isHomogeneous_X isHomogeneous_monomial isHomogeneous_one isHomogeneous_zero map map_C map_X mem_support_iff monomial monomial_eq monomial_mul notMem_support_iff pderiv pderiv_C pderiv_X pderiv_X_of_ne pderiv_X_self pderiv_monomial support_add support_mul support_nonempty totalDegree totalDegree_eq_zero_iff_eq_C totalDegree_one)
end Mv
namespace Pl
export Polynomial (C C_comp C_eq_natCast C_mul C_mul_X_pow_eq_monomial C_pow IsRoot Monic X X_comp X_ne_zero X_pow_dvd_iff add_comp add_modByMonic algebraMap_eq card_roots' coe_compRingHom coe_evalRingHom coe_mapRingHom coe_monomial coeff_C coeff_C_mul coeff_C_mul_X_pow coeff_C_zero coeff_X coeff_X_pow coeff_X_pow_mul' coeff_X_pow_self coeff_X_zero coeff_add coeff_coe coeff_derivative coeff_eq_zero_of_natDegree_lt coeff_map coeff_mul coeff_neg coeff_sub coeff_zero coeff_zero_eq_eval_zero compRingHom comp_X comp_assoc degree_C degree_add_eq_right_of_degree_lt degree_eq_natDegree degree_lt_degree degree_modByMonic_lt degree_mul_le degree_zero derivative_C derivative_add derivative_map derivative_monomial derivative_mul derivative_pow derivative_sub derivative_zero divByMonic_eq_zero_iff dvd_iff_isRoot eq_one_of_monic_natDegree_zero evalRingHom eval_C eval_X eval_add eval_comp eval_monomial eval_mul eval_one eval_pow eval_prod eval_sub eval_zero eval₂RingHom ext finsetSum_coeff induction_on' irreducible_X_sub_C isCoprime_X_sub_C_of_isUnit_sub le_natDegree_of_mem_supp le_natDegree_of_ne_zero leadingCoeff leadingCoeff_mul leadingCoeff_ne_zero map mapRingHom map_C map_X map_add map_injective map_modByMonic map_monomial map_mul map_one map_pow map_sub map_sum map_zero mem_roots mem_support_iff modByMonic_X_sub_C_eq_C_eval modByMonic_add_div modByMonic_eq_self_iff modByMonic_eq_zero_iff_dvd monic_X_add_C monic_X_sub_C monic_multiset_prod_of_monic monic_prod_of_monic monomial monomial_comp mul_comp natDegree_C natDegree_C_mul natDegree_C_mul_le natDegree_X natDegree_X_add_C natDegree_X_pow natDegree_X_sub_C natDegree_add_eq_left_of_natDegree_lt natDegree_add_eq_right_of_natDegree_lt natDegree_add_le natDegree_comp natDegree_derivative_le natDegree_eq_zero_iff_degree_le_zero natDegree_eq_zero_of_isUnit natDegree_le_iff_coeff_eq_zero natDegree_lt_natDegree natDegree_map_eq_of_injective natDegree_mul natDegree_mul_le natDegree_neg natDegree_one natDegree_pow natDegree_prod_le natDegree_prod_of_monic natDegree_sub_le natDegree_sum_le_of_forall_le natDegree_zero notMem_support_iff pow_comp sub_dvd_eval_sub sum_comp support_nonempty zero_comp zero_le_degree_iff)
end Pl
namespace Ps
export PowerSeries (C X X_pow_dvd_iff algebraMap_eq coeff coeff_C coeff_C_mul coeff_C_mul_X_pow coeff_X coeff_X_pow_mul' coeff_mk coeff_mul coeff_one coeff_zero_eq_constantCoeff constantCoeff constantCoeff_C constantCoeff_X isUnit_iff_constantCoeff mk monomial_eq_C_mul_X_pow)
end Ps
namespace Mx
export Matrix (adjugate_apply adjugate_mul cons_val cons_val_one cons_val_two cons_val_zero det det_apply det_diagonal det_eq_elem_of_subsingleton det_fin_three det_fromBlocks_zero₁₂ det_isEmpty det_mul det_of_isLowerTriangular det_of_isUpperTriangular det_one det_permute det_permute' det_reindex_self det_succ_row_zero det_transpose det_unique det_zero diagonal diagonal_apply diagonal_mul exists_mulVec_eq_zero_iff ext fromBlocks fromBlocks_apply₁₁ fromBlocks_apply₁₂ fromBlocks_apply₂₁ fromBlocks_apply₂₂ head_cons map_apply mulVec mulVec_add mulVec_mulVec mulVec_smul mulVec_sub mulVec_zero mul_adjugate mul_apply mul_assoc mul_nonsing_inv mul_one mul_smul nonsing_inv_mul of of_apply one_apply one_apply_ne one_mul one_mulVec reindex reindex_apply smul_mulVec submatrix submatrix_apply tail_cons transpose transpose_apply transpose_mul transpose_one transpose_transpose updateRow_apply zero_apply)
end Mx
namespace Fu
export Finsupp (add_apply degree degree_apply notMem_support_iff prod prod_fintype prod_mul single single_apply sum_fintype tsub_apply weight_apply)
end Fu
namespace Mu
export Multiset (card_le_card dvd_prod induction_on le_iff_subset le_sum_of_mem map_cons map_map map_zero mem_cons mem_cons_of_mem mem_cons_self mem_map mem_map_of_mem mem_toFinset prod_cons prod_eq_zero_iff prod_zero sum_cons toFinset_card_le)
end Mu
namespace Fs
export Finset (card card_eq_one card_eq_sum_ones card_eq_zero card_filter_add_card_filter_not card_le_one card_product card_range card_sdiff_of_subset card_singleton card_union_of_disjoint disjoint_singleton_right dvd_sum exists_max_image exists_mem_eq_sup exists_mem_notMem_of_card_lt_card exists_ne_zero_of_sum_ne_zero exists_subset_card_eq filter_subset induction_on insert_subset inter_subset_right mem_add mem_attach mem_coe mem_powerset mem_product mem_range mem_val mul_prod_erase not_nonempty_iff_eq_empty prod_bij prod_congr prod_const prod_div_distrib prod_dvd_of_coprime prod_dvd_prod_of_dvd prod_eq_one prod_eq_zero_iff prod_image prod_insert prod_involution prod_neg prod_range_succ prod_range_succ' prod_range_zero prod_singleton prod_union range subset_insert sum_const sum_const_zero sum_eq_add sum_filter sum_insert sum_neg_distrib sum_range_add sum_range_succ sum_range_succ' sum_singleton sup'_eq_sup sup_le univ)
end Fs
namespace Rh
export RingHom (coe_coe comp_apply comp_id id isUnit_map mapMatrix_apply map_det)
end Rh
namespace Fn
export Function (Injective Surjective comp_apply iterate_succ iterate_succ_apply' iterate_zero onFun update update_of_ne update_self)
end Fn
namespace Ah
export AlgHom (coe_toRingHom toRingHom_eq_coe)
end Ah
namespace Fi
export Fin (cons elim0 eta ext isValue last prod_univ_five prod_univ_six prod_univ_three prod_univ_two reduceEq snoc snoc_castSucc snoc_last succAbove sum_univ_castSucc sum_univ_eq_sum_range sum_univ_five sum_univ_four sum_univ_six sum_univ_three sum_univ_two val val_cast val_castSucc val_zero)
end Fi
namespace Dr
export Derivation (leibniz)
end Dr
namespace Eqv
export Equiv (Perm apply_symm_apply sumComm sumComm_apply sum_comp swap swap_apply_def symm_apply_apply)
end Eqv
namespace Ch
export CharP (cast_eq_zero cast_eq_zero_iff)
end Ch
namespace Ufm
export UniqueFactorizationMonoid (factors factors_prod irreducible_iff_prime irreducible_of_factor)
end Ufm
private abbrev Mv3 (R : Type*) [CommSemiring R] := MvPolynomial (Fin 3) R
private abbrev Mv2 (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R
private abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R
private abbrev PS (R : Type*) [Semiring R] := PowerSeries R
private abbrev Pol (R : Type*) [Semiring R] := Polynomial R
private abbrev E3 := Fin 3 →₀ ℕ
section Part1Scope
open Green68 MvPolynomial Finset
section BasicLinearAlgebra
lemma v03 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
lemma v151 (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
variable {R : Type*} [CommRing R]
def det3 (u v w : Fin 3 → R) : R :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)
def cross3 (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]
def dot3 (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2
lemma v14 (u v w : Fin 3 → R) :
    det3 u v w = dot3 (cross3 u v) w := by
  simp only [det3, dot3, cross3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
  ring
lemma v45 (u v : Fin 3 → R) : dot3 u v = dot3 v u := by
  simp only [dot3]; ring
lemma v06 (c : R) (u v : Fin 3 → R) : dot3 (c • u) v = c * dot3 u v := by
  simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring
lemma v02 (c : R) (u v : Fin 3 → R) : dot3 u (c • v) = c * dot3 u v := by
  simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring
lemma v84 (u v w : Fin 3 → R) : dot3 (u + v) w = dot3 u w + dot3 v w := by
  simp only [dot3, Pi.add_apply]; ring
lemma v13 (u v w : Fin 3 → R) : dot3 u (v + w) = dot3 u v + dot3 u w := by
  simp only [dot3, Pi.add_apply]; ring
lemma v135 (v : Fin 3 → R) : dot3 0 v = 0 := by
  simp [dot3]
lemma dot3_zero_right (u : Fin 3 → R) : dot3 u 0 = 0 := by
  simp [dot3]
lemma v69 (u v : Fin 3 → R) : cross3 u v = -cross3 v u := by
  ext i; fin_cases i <;> simp [cross3] <;> ring
lemma v85 (u : Fin 3 → R) : cross3 u u = 0 := by
  ext i; rcases v03 i with rfl | rfl | rfl <;> simp [cross3] <;> ring
lemma v72 (c : R) (u v : Fin 3 → R) : cross3 (c • u) v = c • cross3 u v := by
  ext i; fin_cases i <;> simp [cross3] <;> ring
lemma v42 (c : R) (u v : Fin 3 → R) : cross3 u (c • v) = c • cross3 u v := by
  ext i; fin_cases i <;> simp [cross3] <;> ring
lemma v56 (u v : Fin 3 → R) : dot3 (cross3 u v) u = 0 := by
  simp only [dot3, cross3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]; ring
lemma v28 (u v : Fin 3 → R) : dot3 (cross3 u v) v = 0 := by
  simp only [dot3, cross3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]; ring
lemma v206 (u v w : Fin 3 → R) : det3 v u w = -det3 u v w := by
  simp only [det3]; ring
lemma v184 (u v w : Fin 3 → R) : det3 u w v = -det3 u v w := by
  simp only [det3]; ring
lemma det3_swap13 (u v w : Fin 3 → R) : det3 w v u = -det3 u v w := by
  simp only [det3]; ring
lemma det3_cycle (u v w : Fin 3 → R) : det3 v w u = det3 u v w := by
  simp only [det3]; ring
lemma det3_self_12 (u w : Fin 3 → R) : det3 u u w = 0 := by
  simp only [det3]; ring
lemma v95 (u v : Fin 3 → R) : det3 u v u = 0 := by
  simp only [det3]; ring
lemma v116 (u v : Fin 3 → R) : det3 u v v = 0 := by
  simp only [det3]; ring
lemma det3_smul_1 (c : R) (u v w : Fin 3 → R) : det3 (c • u) v w = c * det3 u v w := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]; ring
lemma v185 (c : R) (u v w : Fin 3 → R) : det3 u (c • v) w = c * det3 u v w := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]; ring
lemma v76 (c : R) (u v w : Fin 3 → R) : det3 u v (c • w) = c * det3 u v w := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]; ring
lemma v199 (u v w₁ w₂ : Fin 3 → R) : det3 u v (w₁ + w₂) = det3 u v w₁ + det3 u v w₂ := by
  simp only [det3, Pi.add_apply]; ring
lemma v127 (u v w : Fin 3 → R) : det3 u v w = (Mx.of ![u, v, w]).det := by
  rw [Mx.det_fin_three]
  simp only [det3, Mx.of_apply, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
  ring
lemma cross3_triple (u v w : Fin 3 → R) :
    cross3 u (cross3 v w) = (dot3 u w) • v - (dot3 u v) • w := by
  ext i; fin_cases i <;> simp [cross3, dot3] <;> ring
lemma v174 (e₀ e₁ e₂ s : Fin 3 → R) :
    det3 e₀ e₁ e₂ • s = det3 s e₁ e₂ • e₀ + det3 e₀ s e₂ • e₁ + det3 e₀ e₁ s • e₂ := by
  ext i; fin_cases i <;> simp [det3] <;> ring
noncomputable def v55 (l : Fin 3 → R) : Mv3 R :=
  C (l 0) * X 0 + C (l 1) * X 1 + C (l 2) * X 2
lemma v27 (l x : Fin 3 → R) : eval x (v55 l) = dot3 l x := by
  simp [v55, dot3]
lemma v07 {σ : Type*} {R : Type*} [CommRing R] {d : ℕ} (c : R)
    {P : MvPolynomial σ R} (hP : P.IsHomogeneous d) : (C c * P).IsHomogeneous d := by
  simpa only [zero_add] using (isHomogeneous_C σ c).mul hP
lemma v05 {σ : Type*} {R : Type*} [CommRing R] {d : ℕ}
    {P : MvPolynomial σ R} (hP : P.IsHomogeneous d) (c : R) (x : σ → R) :
    eval (c • x) P = c ^ d * eval x P := by
  rw [P.as_sum, map_sum, map_sum, mul_sum]
  apply sum_congr rfl; intro m hm
  simp only [eval_monomial, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Fu.prod_mul, ← mul_assoc, mul_comm (P.coeff m), mul_assoc]
  congr 1
  have hsum : m.sum (fun _ e => e) = d := by
    simpa [Fu.weight_apply] using hP (Mv.mem_support_iff.mp hm)
  rw [Fu.prod, prod_pow_eq_pow_sum]
  exact congr_arg (c ^ ·) hsum
lemma v101 {σ τ : Type*} {R : Type*} [CommRing R] (f : σ → MvPolynomial τ R) (x : τ → R)
    (P : MvPolynomial σ R) : eval x (aeval f P) = eval (fun i => eval x (f i)) P := by
  induction P using Mv.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp]
lemma v124 {σ : Type*} {R : Type*} [CommRing R] (f : σ → Pol R) (r : R)
    (P : MvPolynomial σ R) : (aeval f P).eval r = eval (fun i => (f i).eval r) P := by
  induction P using Mv.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Pl.eval_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, Pl.eval_mul, eval_X, hp]
lemma aeval_comp_eq {σ τ υ : Type*} {R : Type*} [CommRing R]
    (g : τ → MvPolynomial υ R) (f : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    aeval g (aeval f P) = aeval (fun i => aeval g (f i)) P := by
  induction P using Mv.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]
lemma v202 {σ : Type*} {R : Type*} [CommRing R] (P : MvPolynomial σ R) :
    aeval (X : σ → MvPolynomial σ R) P = P := by
  induction P using Mv.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]
lemma v52 (l : Fin 3 → R) : (v55 l).IsHomogeneous 1 := by
  unfold v55
  apply IsHomogeneous.add
  · apply IsHomogeneous.add
    · exact v07 (l 0) (isHomogeneous_X R (0 : Fin 3))
    · exact v07 (l 1) (isHomogeneous_X R (1 : Fin 3))
  · exact v07 (l 2) (isHomogeneous_X R (2 : Fin 3))
lemma map_linForm {S : Type*} [CommRing S] (f : R →+* S) (l : Fin 3 → R) :
    Mv.map f (v55 l) = v55 (f ∘ l) := by
  simp [v55]
lemma v01 {K : Type*} [Field K] {u v : Fin 3 → K} (hu : u ≠ 0) :
    cross3 u v = 0 ↔ ∃ c : K, v = c • u := by
  constructor
  · intro h
    have h0 : u 1 * v 2 - u 2 * v 1 = 0 := by simpa [cross3] using congr_fun h 0
    have h1 : u 2 * v 0 - u 0 * v 2 = 0 := by simpa [cross3] using congr_fun h 1
    have h2 : u 0 * v 1 - u 1 * v 0 = 0 := by simpa [cross3] using congr_fun h 2
    have hex : ∃ i : Fin 3, u i ≠ 0 := by
      by_contra hall; push Not at hall; exact hu (funext hall)
    rcases hex with ⟨i, hi⟩
    refine ⟨v i / u i, ?_⟩
    ext j
    rcases v03 i with rfl | rfl | rfl <;> rcases v03 j with rfl | rfl | rfl <;>
      simp only [Pi.smul_apply, smul_eq_mul] <;> field_simp [hi]
    · linear_combination h2
    · linear_combination -h1
    · linear_combination -h2
    · linear_combination h0
    · linear_combination h1
    · linear_combination -h0
  · rintro ⟨c, rfl⟩
    rw [v42, v85, smul_zero]
lemma v09 {K : Type*} [Field K] {u v z : Fin 3 → K}
    (huv : cross3 u v ≠ 0) (hu : dot3 z u = 0) (hv : dot3 z v = 0) :
    ∃ c : K, z = c • cross3 u v := by
  have hc : cross3 (cross3 u v) z = 0 := by
    have h := cross3_triple z u v
    rw [v69, neg_eq_zero]
    rw [h, hu, hv]
    simp
  exact (v01 huv).mp hc
end BasicLinearAlgebra
section ProjectivePlane
variable {p : ℕ} [Fact p.Prime]
def v53 (v : Fin 3 → ZMod p) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)
instance (v : Fin 3 → ZMod p) : Decidable (v53 v) := by
  unfold v53; infer_instance
def pPts (p : ℕ) [Fact p.Prime] : Finset (Fin 3 → ZMod p) :=
  Fs.univ.filter v53
lemma v30 {v : Fin 3 → ZMod p} : v ∈ pPts p ↔ v53 v := by
  simp [pPts]
lemma v00 {v : Fin 3 → ZMod p} (hv : v53 v) : v ≠ 0 := by
  intro h0
  rcases hv with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> simp [h0] at h
def normPt (v : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  if v 0 ≠ 0 then (v 0)⁻¹ • v
  else if v 1 ≠ 0 then (v 1)⁻¹ • v
  else (v 2)⁻¹ • v
lemma v38 {v : Fin 3 → ZMod p} (hv : v ≠ 0) :
    v53 (normPt v) ∧ ∃ c : ZMod p, c ≠ 0 ∧ normPt v = c • v := by
  unfold normPt
  by_cases h0 : v 0 ≠ 0
  · rw [if_pos h0]
    refine ⟨Or.inl ?_, (v 0)⁻¹, inv_ne_zero h0, rfl⟩
    simp [inv_mul_cancel₀ h0]
  · push Not at h0
    rw [if_neg (not_not.mpr h0)]
    by_cases h1 : v 1 ≠ 0
    · rw [if_pos h1]
      refine ⟨Or.inr (Or.inl ⟨?_, ?_⟩), (v 1)⁻¹, inv_ne_zero h1, rfl⟩
      · simp [h0]
      · simp [inv_mul_cancel₀ h1]
    · push Not at h1
      have h2 : v 2 ≠ 0 := by
        intro h2; apply hv; ext i; fin_cases i <;> assumption
      rw [if_neg (not_not.mpr h1)]
      refine ⟨Or.inr (Or.inr ⟨?_, ?_, ?_⟩), (v 2)⁻¹, inv_ne_zero h2, rfl⟩
      · simp [h0]
      · simp [h1]
      · simp [inv_mul_cancel₀ h2]
lemma v90 {v : Fin 3 → ZMod p} (hv : v ≠ 0) : normPt v ∈ pPts p :=
  v30.mpr (v38 hv).1
lemma v04 {u v : Fin 3 → ZMod p} (hu : v53 u) (hv : v53 v)
    {c : ZMod p} (h : u = c • v) : u = v := by
  have hc : c = 1 := by
    rcases hu with h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩ <;>
    rcases hv with g0 | ⟨g0, g1⟩ | ⟨g0, g1, g2⟩ <;>
    have := congr_fun h 0 <;> have := congr_fun h 1 <;> have := congr_fun h 2 <;>
    simp_all
  rw [h, hc, one_smul]
lemma v44 {u v : Fin 3 → ZMod p} (hu : u ≠ 0) (hv : v ≠ 0) :
    normPt u = normPt v ↔ ∃ c : ZMod p, c ≠ 0 ∧ u = c • v := by
  rcases v38 hu with ⟨hnu, cu, hcu, hru⟩
  rcases v38 hv with ⟨hnv, cv, hcv, hrv⟩
  constructor
  · intro heq
    refine ⟨cu⁻¹ * cv, mul_ne_zero (inv_ne_zero hcu) hcv, ?_⟩
    rw [mul_smul, ← hrv, ← heq, hru, inv_smul_smul₀ hcu]
  · rintro ⟨c, hc, rfl⟩
    apply v04 hnu hnv (c := cu * c * cv⁻¹)
    rw [hru, hrv, smul_smul, smul_smul]
    congr 1; field_simp [hcv]
lemma v94 {u : Fin 3 → ZMod p} (hu : v53 u) : normPt u = u := by
  rcases v38 (v00 hu) with ⟨hnu, c, _, hru⟩
  exact v04 hnu hu hru
lemma v179 {u : Fin 3 → ZMod p} {c : ZMod p} (hu : u ≠ 0) (hc : c ≠ 0) :
    normPt (c • u) = normPt u :=
  (v44 (smul_ne_zero hc hu) hu).mpr ⟨c, hc, rfl⟩
lemma card_pPts : (pPts p).card = p ^ 2 + p + 1 := by
  have h1 : pPts p = (Fs.univ.image (fun x : ZMod p × ZMod p => ![1, x.1, x.2])) ∪
      ((Fs.univ.image (fun x : ZMod p => ![0, 1, x])) ∪
       {![(0 : ZMod p), 0, 1]}) := by
    ext v
    simp only [v30, v53, mem_union, mem_image, mem_univ, true_and, mem_singleton, Prod.exists]
    constructor
    · rintro (h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩)
      · left; exact ⟨v 1, v 2, by ext i; fin_cases i <;> simp [h0]⟩
      · right; left; exact ⟨v 2, by ext i; fin_cases i <;> simp [h0, h1]⟩
      · right; right; ext i; fin_cases i <;> simp [h0, h1, h2]
    · rintro (⟨a, b, rfl⟩ | ⟨a, rfl⟩ | rfl) <;> simp
  rw [h1]
  have hd1 : Disjoint (Fs.univ.image (fun x : ZMod p × ZMod p => ![1, x.1, x.2]))
      ((Fs.univ.image (fun x : ZMod p => ![0, 1, x])) ∪ {![(0 : ZMod p), 0, 1]}) := by
    rw [disjoint_left]
    intro v hv1 hv2
    simp only [mem_image, mem_univ, true_and, Prod.exists] at hv1
    rcases hv1 with ⟨a, b, rfl⟩
    simp only [mem_union, mem_image, mem_univ, true_and, mem_singleton] at hv2
    rcases hv2 with ⟨c, hc⟩ | hc <;>
    · have := congr_fun hc 0; simp at this
  have hd2 : Disjoint (Fs.univ.image (fun x : ZMod p => ![0, 1, x]))
      {![(0 : ZMod p), 0, 1]} := by
    rw [Fs.disjoint_singleton_right]
    simp only [mem_image, mem_univ, true_and, not_exists]
    intro c hc
    have := congr_fun hc 1; simp at this
  rw [Fs.card_union_of_disjoint hd1, Fs.card_union_of_disjoint hd2]
  have hinj1 : Fn.Injective (fun x : ZMod p × ZMod p => ![1, x.1, x.2]) := by
    intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h1 := congr_fun h 1; have h2 := congr_fun h 2
    simp at h1 h2; exact Prod.ext h1 h2
  have hinj2 : Fn.Injective (fun x : ZMod p => ![0, 1, x]) := by
    intro a1 a2 h
    have h2 := congr_fun h 2; simp at h2; exact h2
  rw [card_image_of_injective _ hinj1, card_image_of_injective _ hinj2, Fs.card_singleton]
  simp [ZMod.card, sq, add_assoc]
def lThru (x : Fin 3 → ZMod p) : Finset (Fin 3 → ZMod p) :=
  (pPts p).filter (fun l => dot3 l x = 0)
lemma v200 {x : Fin 3 → ZMod p} (hx : x ≠ 0) :
    (lThru x).card = p + 1 := by
  let orth : Finset (Fin 3 → ZMod p) := Fs.univ.filter (fun v => v ≠ 0 ∧ dot3 v x = 0)
  have horth_card : orth.card = p ^ 2 - 1 := by
    have hex : ∃ i : Fin 3, x i ≠ 0 := by
      by_contra hall; push Not at hall; exact hx (funext hall)
    rcases hex with ⟨i, hi⟩
    let S : Finset (Fin 3 → ZMod p) := Fs.univ.filter (fun v => dot3 v x = 0)
    have hS : S.card = p ^ 2 := by
      rcases v03 i with rfl | rfl | rfl
      · let f : ZMod p × ZMod p → Fin 3 → ZMod p :=
          fun ab => ![-(ab.1 * x 1 + ab.2 * x 2) / x 0, ab.1, ab.2]
        have hSeq : S = Fs.univ.image f := by
          ext v
          simp only [S, mem_filter, mem_univ, true_and, mem_image, Prod.exists]
          constructor
          · intro hd
            refine ⟨v 1, v 2, ?_⟩
            ext j; rcases v03 j with rfl | rfl | rfl
            · simp only [f, Mx.cons_val_zero]
              have : v 0 * x 0 = -(v 1 * x 1 + v 2 * x 2) := by
                simp only [dot3] at hd; linear_combination hd
              rw [← this, mul_div_cancel_right₀ _ hi]
            · simp [f]
            · simp [f]
          · rintro ⟨a, b, rfl⟩
            simp only [f, dot3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
            field_simp [hi]; ring
        rw [hSeq, card_image_of_injective]
        · simp [ZMod.card, sq]
        · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
          have h1 := congr_fun h 1; have h2 := congr_fun h 2
          simp [f] at h1 h2; exact Prod.ext h1 h2
      · let f : ZMod p × ZMod p → Fin 3 → ZMod p :=
          fun ab => ![ab.1, -(ab.1 * x 0 + ab.2 * x 2) / x 1, ab.2]
        have hSeq : S = Fs.univ.image f := by
          ext v
          simp only [S, mem_filter, mem_univ, true_and, mem_image, Prod.exists]
          constructor
          · intro hd
            refine ⟨v 0, v 2, ?_⟩
            ext j; rcases v03 j with rfl | rfl | rfl
            · simp [f]
            · simp only [f, Mx.cons_val_one, Mx.cons_val_zero]
              have : v 1 * x 1 = -(v 0 * x 0 + v 2 * x 2) := by
                simp only [dot3] at hd; linear_combination hd
              rw [← this, mul_div_cancel_right₀ _ hi]
            · simp [f]
          · rintro ⟨a, b, rfl⟩
            simp only [f, dot3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
            field_simp [hi]; ring
        rw [hSeq, card_image_of_injective]
        · simp [ZMod.card, sq]
        · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
          have h0 := congr_fun h 0; have h2 := congr_fun h 2
          simp [f] at h0 h2; exact Prod.ext h0 h2
      · let f : ZMod p × ZMod p → Fin 3 → ZMod p :=
          fun ab => ![ab.1, ab.2, -(ab.1 * x 0 + ab.2 * x 1) / x 2]
        have hSeq : S = Fs.univ.image f := by
          ext v
          simp only [S, mem_filter, mem_univ, true_and, mem_image, Prod.exists]
          constructor
          · intro hd
            refine ⟨v 0, v 1, ?_⟩
            ext j; rcases v03 j with rfl | rfl | rfl
            · simp [f]
            · simp [f]
            · simp only [f, Mx.cons_val]
              have : v 2 * x 2 = -(v 0 * x 0 + v 1 * x 1) := by
                simp only [dot3] at hd; linear_combination hd
              rw [← this, mul_div_cancel_right₀ _ hi]
          · rintro ⟨a, b, rfl⟩
            simp only [f, dot3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
            field_simp [hi]; ring
        rw [hSeq, card_image_of_injective]
        · simp [ZMod.card, sq]
        · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
          have h0 := congr_fun h 0; have h1 := congr_fun h 1
          simp [f] at h0 h1; exact Prod.ext h0 h1
    have horth_eq : orth = S.erase 0 := by
      ext v; simp [orth, S, and_comm]
    have h0S : (0 : Fin 3 → ZMod p) ∈ S := by simp [S, v135]
    rw [horth_eq, card_erase_of_mem h0S, hS]
  let φ : (ZMod p)ˣ × (Fin 3 → ZMod p) → Fin 3 → ZMod p := fun cl => (cl.1 : ZMod p) • cl.2
  have himg : orth = (Fs.univ ×ˢ lThru x).image φ := by
    ext v
    simp only [orth, mem_filter, mem_univ, true_and, mem_image, Fs.mem_product, lThru, v30, Prod.exists]
    constructor
    · rintro ⟨hv, hdx⟩
      rcases v38 hv with ⟨hnp, c, hc, hreq⟩
      refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc), normPt v, ⟨hnp, ?_⟩, ?_⟩
      · rw [hreq, v06, hdx, mul_zero]
      · simp only [φ, Units.val_mk0, hreq, inv_smul_smul₀ hc]
    · rintro ⟨c, l, ⟨hl, hdl⟩, rfl⟩
      refine ⟨smul_ne_zero c.ne_zero (v00 hl), ?_⟩
      simp only [φ, v06, hdl, mul_zero]
  have hinj : Set.InjOn φ ↑((Fs.univ : Finset (ZMod p)ˣ) ×ˢ lThru x) := by
    intro ⟨c1, l1⟩ h1 ⟨c2, l2⟩ h2 heq
    simp only [Fs.mem_coe, Fs.mem_product, mem_univ, true_and, lThru, mem_filter, v30] at h1 h2
    simp only [φ] at heq
    have hl_eq : l1 = l2 := by
      apply v04 h1.1 h2.1 (c := (c1 : ZMod p)⁻¹ * (c2 : ZMod p))
      rw [mul_smul, ← heq, inv_smul_smul₀ c1.ne_zero]
    subst hl_eq
    have hc_eq : (c1 : ZMod p) = (c2 : ZMod p) := by
      have hne := v00 h1.1
      have hsub : ((c1 : ZMod p) - (c2 : ZMod p)) • l1 = 0 := by
        rw [sub_smul, heq, sub_self]
      rcases smul_eq_zero.mp hsub with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hne
    exact Prod.ext (Units.ext hc_eq) rfl
  have hcard_prod : orth.card = (p - 1) * (lThru x).card := by
    rw [himg, card_image_of_injOn hinj, Fs.card_product]
    have hu : (Fs.univ : Finset (ZMod p)ˣ).card = p - 1 := by
      rw [card_univ, ZMod.card_units]
    rw [hu]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1p : 1 ≤ p := by omega
  have h1p2 : 1 ≤ p ^ 2 := by nlinarith
  have hmul : (p - 1) * (lThru x).card = (p - 1) * (p + 1) := by
    rw [← hcard_prod, horth_card]
    have hdiff : (p - 1) * (p + 1) = p ^ 2 - 1 := by zify [h1p, h1p2]; ring
    exact hdiff.symm
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
def IsProjArc (K : Finset (Fin 3 → ZMod p)) : Prop :=
  (∀ x ∈ K, v53 x) ∧ ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ K, x ≠ y → y ≠ z → x ≠ z → det3 x y z ≠ 0
def v153 (K : Finset (Fin 3 → ZMod p)) : Prop :=
  IsProjArc K ∧ ∀ q ∈ pPts p, q ∉ K → ∃ x ∈ K, ∃ y ∈ K, x ≠ y ∧ det3 q x y = 0
def v23 (K : Finset (Fin 3 → ZMod p)) (x : Fin 3 → ZMod p) : Finset (Fin 3 → ZMod p) :=
  (lThru x).filter (fun l => ∀ y ∈ K, y ≠ x → dot3 l y ≠ 0)
lemma v105 (K : Finset (Fin 3 → ZMod p)) (x : Fin 3 → ZMod p) :
    v23 K x ⊆ lThru x :=
  Fs.filter_subset _ _
lemma v26 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K)
    {x : Fin 3 → ZMod p} (hx : x ∈ K) :
    (v23 K x).card + (K.card - 1) = p + 1 := by
  let secants : Finset (Fin 3 → ZMod p) := (K.erase x).image (fun y => normPt (cross3 x y))
  have hdisj : Disjoint (v23 K x) secants := by
    rw [disjoint_left]
    intro l hl hs
    simp only [v23, mem_filter] at hl
    simp only [secants, mem_image, mem_erase] at hs
    rcases hs with ⟨y, ⟨hyx, hyK⟩, rfl⟩
    have hcr : cross3 x y ≠ 0 := by
      intro h0
      rcases (v01 (v00 (hK.1 x hx))).mp h0 with ⟨c, hc⟩
      exact hyx (v04 (hK.1 y hyK) (hK.1 x hx) hc)
    rcases v38 hcr with ⟨_, c, _, hrc⟩
    apply hl.2 y hyK hyx
    rw [hrc, v06, v28, mul_zero]
  have hunion : lThru x = v23 K x ∪ secants := by
    ext l
    simp only [mem_union, v23, mem_filter, secants, mem_image, mem_erase]
    constructor
    · intro hl
      by_cases h : ∀ y ∈ K, y ≠ x → dot3 l y ≠ 0
      · exact Or.inl ⟨hl, h⟩
      · push Not at h
        rcases h with ⟨y, hyK, hyx, hdly⟩
        right
        refine ⟨y, ⟨hyx, hyK⟩, ?_⟩
        have hcr : cross3 x y ≠ 0 := by
          intro h0
          rcases (v01 (v00 (hK.1 x hx))).mp h0 with ⟨c, hc⟩
          exact hyx (v04 (hK.1 y hyK) (hK.1 x hx) hc)
        have hdlx : dot3 l x = 0 := (mem_filter.mp hl).2
        rcases v09 hcr hdlx hdly with ⟨c, hc⟩
        have hln : v53 l := v30.mp (mem_filter.mp hl).1
        have hcne : c ≠ 0 := by
          intro h0; rw [h0, zero_smul] at hc; exact v00 hln hc
        rw [← v94 hln, hc, v179 hcr hcne]
    · rintro (⟨hl, _⟩ | ⟨y, ⟨hyx, hyK⟩, rfl⟩)
      · exact hl
      · have hcr : cross3 x y ≠ 0 := by
          intro h0
          rcases (v01 (v00 (hK.1 x hx))).mp h0 with ⟨c, hc⟩
          exact hyx (v04 (hK.1 y hyK) (hK.1 x hx) hc)
        rcases v38 hcr with ⟨hnp, c, _, hrc⟩
        simp only [lThru, mem_filter, v30]
        refine ⟨hnp, ?_⟩
        rw [hrc, v06, v56, mul_zero]
  have hinj : Set.InjOn (fun y => normPt (cross3 x y)) ↑(K.erase x) := by
    intro y1 hy1 y2 hy2 heq
    simp only [Fs.mem_coe, mem_erase] at hy1 hy2
    by_contra hne
    have hcr1 : cross3 x y1 ≠ 0 := by
      intro h0
      rcases (v01 (v00 (hK.1 x hx))).mp h0 with ⟨c, hc⟩
      exact hy1.1 (v04 (hK.1 y1 hy1.2) (hK.1 x hx) hc)
    have hcr2 : cross3 x y2 ≠ 0 := by
      intro h0
      rcases (v01 (v00 (hK.1 x hx))).mp h0 with ⟨c, hc⟩
      exact hy2.1 (v04 (hK.1 y2 hy2.2) (hK.1 x hx) hc)
    rcases (v44 hcr1 hcr2).mp heq with ⟨c, hc, hceq⟩
    have hdet : det3 x y1 y2 = 0 := by
      rw [v14, hceq, v06, v28, mul_zero]
    exact hK.2 x hx y1 hy1.2 y2 hy2.2 hy1.1.symm hne hy2.1.symm hdet
  have hsec_card : secants.card = K.card - 1 := by
    rw [card_image_of_injOn hinj, card_erase_of_mem hx]
  have hlt := v200 (v00 (hK.1 x hx))
  rw [hunion, Fs.card_union_of_disjoint hdisj, hsec_card] at hlt
  exact hlt
lemma v92 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K) (hp : p ≠ 2) :
    K.card ≤ p + 1 := by
  by_cases hne : K.Nonempty
  · rcases hne with ⟨x0, hx0⟩
    have hle2 : K.card ≤ p + 2 := by
      have := v26 hK hx0
      omega
    by_contra hgt
    have hcard : K.card = p + 2 := by omega
    have hnotan : ∀ x ∈ K, v23 K x = ∅ := by
      intro x hx
      have := v26 hK hx
      exact Fs.card_eq_zero.mp (by omega)
    have hlt : K.card < (pPts p).card := by
      rw [hcard, card_pPts]
      have hp3 : 3 ≤ p := by
        have := (Fact.out : p.Prime).two_le; omega
      nlinarith
    have hsub : K ⊆ pPts p := fun x hx => v30.mpr (hK.1 x hx)
    obtain ⟨q, hq_mem, hqK⟩ := Fs.exists_mem_notMem_of_card_lt_card hlt
    have h2dvd : 2 ∣ K.card := by
      have hbi : K.card = ∑ l ∈ lThru q, (K.filter (fun x => dot3 l x = 0)).card := by
        rw [Fs.card_eq_sum_ones]
        trans ∑ x ∈ K, ∑ l ∈ lThru q, if dot3 l x = 0 then 1 else 0
        · apply sum_congr rfl
          intro x hx
          have hxq : x ≠ q := fun h => hqK (h ▸ hx)
          have hcr : cross3 q x ≠ 0 := by
            intro h0
            rcases (v01 (v00 (v30.mp hq_mem))).mp h0
              with ⟨c, hc⟩
            exact hxq (v04 (hK.1 x hx) (v30.mp hq_mem) hc)
          have huniq : (lThru q).filter (fun l => dot3 l x = 0) = {normPt (cross3 q x)} := by
            ext l
            simp only [mem_filter, mem_singleton, lThru, v30]
            constructor
            · rintro ⟨⟨hln, hdlq⟩, hdlx⟩
              rcases v09 hcr hdlq hdlx with ⟨c, hc⟩
              have hcne : c ≠ 0 := by
                intro h0; rw [h0, zero_smul] at hc; exact v00 hln hc
              rw [← v94 hln, hc, v179 hcr hcne]
            · rintro rfl
              rcases v38 hcr with ⟨hnp, c, _, hrc⟩
              refine ⟨⟨hnp, ?_⟩, ?_⟩
              · rw [hrc, v06, v56, mul_zero]
              · rw [hrc, v06, v28, mul_zero]
          rw [← Fs.sum_filter, huniq, Fs.sum_singleton]
        · rw [sum_comm]
          apply sum_congr rfl
          intro l _
          rw [card_filter]
      rw [hbi]
      apply Fs.dvd_sum
      intro l hl
      by_cases hem : (K.filter (fun x => dot3 l x = 0)).Nonempty
      · rcases hem with ⟨x, hx⟩
        simp only [mem_filter] at hx
        have hlx : l ∈ lThru x := by
          simp only [lThru, mem_filter]
          exact ⟨(mem_filter.mp hl).1, hx.2⟩
        have hnt : l ∉ v23 K x := by rw [hnotan x hx.1]; simp
        simp only [v23, mem_filter, hlx, true_and, not_forall, Classical.not_not] at hnt
        rcases hnt with ⟨y, hyK, hyx, hdly⟩
        have hpair : K.filter (fun z => dot3 l z = 0) = {x, y} := by
          ext z
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨hzK, hdlz⟩
            by_contra hne
            push Not at hne
            have hcr : cross3 x y ≠ 0 := by
              intro h0
              rcases (v01 (v00 (hK.1 x hx.1))).mp h0 with ⟨c, hc⟩
              exact hyx (v04 (hK.1 y hyK) (hK.1 x hx.1) hc)
            rcases v09 hcr hx.2 hdly with ⟨c, hc⟩
            have hln : v53 l := v30.mp (mem_filter.mp hl).1
            have hcne : c ≠ 0 := by
              intro h0; rw [h0, zero_smul] at hc; exact v00 hln hc
            rw [hc, v06, ← v14] at hdlz
            have hdet0 : det3 x y z = 0 := (mul_eq_zero.mp hdlz).resolve_left hcne
            exact hK.2 x hx.1 y hyK z hzK hyx.symm hne.2.symm hne.1.symm hdet0
          · rintro (rfl | rfl)
            · exact ⟨hx.1, hx.2⟩
            · exact ⟨hyK, hdly⟩
        rw [hpair, card_pair hyx.symm]
      · rw [Fs.not_nonempty_iff_eq_empty.mp hem, card_empty]
        exact dvd_zero 2
    rw [hcard] at h2dvd
    have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
    rcases hp_odd with ⟨m, rfl⟩
    omega
  · rw [Fs.not_nonempty_iff_eq_empty.mp hne, card_empty]
    omega
def aff2P (a : Fin 2 → ZMod p) : Fin 3 → ZMod p :=
  ![1, a 0, a 1]
lemma v214 (a : Fin 2 → ZMod p) : v53 (aff2P a) :=
  Or.inl rfl
lemma aff2P_injective : Fn.Injective (@aff2P p _) := by
  intro a b h
  ext i; fin_cases i
  · exact congr_fun h 1
  · exact congr_fun h 2
lemma v96 {a b c : Fin 2 → ZMod p}
    (h : det3 (aff2P a) (aff2P b) (aff2P c) = 0) :
    Collinear (ZMod p) ({a, b, c} : Set (Fin 2 → ZMod p)) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  have hdet : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
    simp only [det3, aff2P, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val] at h
    linear_combination h
  by_cases hba : b = a
  · refine ⟨c - a, ?_⟩
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hba]⟩
    · exact ⟨1, by simp⟩
  · refine ⟨b - a, ?_⟩
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hqa | hqb | hqc
    · rw [hqa]; exact ⟨0, by simp⟩
    · rw [hqb]; exact ⟨1, by simp⟩
    · rw [hqc]
      by_cases h0 : b 0 - a 0 ≠ 0
      · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
        ext i; rcases v151 i with rfl | rfl
        · simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          field_simp [h0]; ring
        · simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          field_simp [h0]; linear_combination hdet
      · push Not at h0
        have h1 : b 1 - a 1 ≠ 0 := by
          intro h1; apply hba; ext i; rcases v151 i with rfl | rfl
          · exact sub_eq_zero.mp h0
          · exact sub_eq_zero.mp h1
        refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
        ext i; rcases v151 i with rfl | rfl
        · simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          rw [h0] at hdet ⊢
          have hc0 : c 0 - a 0 = 0 := by
            have : (b 1 - a 1) * (c 0 - a 0) = 0 := by linear_combination -hdet
            exact (mul_eq_zero.mp this).resolve_left h1
          simp [sub_eq_zero.mp hc0]
        · simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          field_simp [h1]; ring
lemma isProjArc_of_meetsLinesInAtMost {A : Finset (Fin 2 → ZMod p)}
    (hA : MeetsLinesInAtMost 2 A) :
    IsProjArc (A.image aff2P) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases mem_image.mp hx with ⟨a, _, rfl⟩
    exact v214 a
  · intro x hx y hy z hz hxy hyz hxz hdet
    rcases mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases mem_image.mp hy with ⟨b, hb, rfl⟩
    rcases mem_image.mp hz with ⟨c, hc, rfl⟩
    have hab : a ≠ b := fun h => hxy (h ▸ rfl)
    have hbc : b ≠ c := fun h => hyz (h ▸ rfl)
    have hac : a ≠ c := fun h => hxz (h ▸ rfl)
    have hsub : ({a, b, c} : Finset (Fin 2 → ZMod p)) ⊆ A := by
      intro u hu; simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hcard : ({a, b, c} : Finset (Fin 2 → ZMod p)).card = 3 := by
      rw [card_insert_of_notMem, card_pair hbc]
      simp [hab, hac]
    have hcol : Collinear (ZMod p) (({a, b, c} : Finset (Fin 2 → ZMod p)) : Set (Fin 2 → ZMod p)) := by
      simpa using v96 hdet
    exact hA {a, b, c} hsub hcard hcol
lemma exists_completeArc_superset {K₀ : Finset (Fin 3 → ZMod p)} (hK₀ : IsProjArc K₀) :
    ∃ K : Finset (Fin 3 → ZMod p), K₀ ⊆ K ∧ v153 K := by
  classical
  let S : Finset (Finset (Fin 3 → ZMod p)) :=
    (pPts p).powerset.filter (fun K => K₀ ⊆ K ∧ IsProjArc K)
  have hK₀_mem : K₀ ∈ S := by
    simp only [S, mem_filter, Fs.mem_powerset]
    exact ⟨fun x hx => v30.mpr (hK₀.1 x hx), Subset.rfl, hK₀⟩
  obtain ⟨K, hKS, hmax⟩ := Fs.exists_max_image S Fs.card ⟨K₀, hK₀_mem⟩
  simp only [S, mem_filter, Fs.mem_powerset] at hKS
  refine ⟨K, hKS.2.1, hKS.2.2, ?_⟩
  intro q hq hqK
  by_contra hno
  push Not at hno
  have hK' : IsProjArc (insert q K) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hxK
      · exact v30.mp hq
      · exact hKS.2.2.1 x hxK
    · intro x hx y hy z hz hxy hyz hxz
      rcases mem_insert.mp hx with rfl | hxK <;>
      rcases mem_insert.mp hy with rfl | hyK <;>
      rcases mem_insert.mp hz with rfl | hzK
      · exact absurd rfl hxy
      · exact absurd rfl hxy
      · exact absurd rfl hxz
      · exact hno y hyK z hzK hyz
      · exact absurd rfl hyz
      · rw [v206]; exact neg_ne_zero.mpr (hno x hxK z hzK hxz)
      · rw [det3_cycle]; exact hno x hxK y hyK hxy
      · exact hKS.2.2.2 x hxK y hyK z hzK hxy hyz hxz
  have hK'_mem : insert q K ∈ S := by
    simp only [S, mem_filter, Fs.mem_powerset]
    exact ⟨Fs.insert_subset hq hKS.1, hKS.2.1.trans (Fs.subset_insert q K), hK'⟩
  have hle := hmax (insert q K) hK'_mem
  rw [card_insert_of_notMem hqK] at hle
  omega
end ProjectivePlane
section SegreTangentsAndEnvelope
variable {p : ℕ} [Fact p.Prime]
lemma v190 : ∏ c ∈ (Fs.univ : Finset (ZMod p)).erase 0, c = -1 := by
  have hp : p.Prime := Fact.out
  have heq : (∏ c ∈ (Fs.univ : Finset (ZMod p)).erase 0, c) = ∏ u : (ZMod p)ˣ, (u : ZMod p) := by
    symm
    apply Fs.prod_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
    · intro u _; exact mem_erase.mpr ⟨u.ne_zero, mem_univ _⟩
    · intro u1 _ u2 _ h; exact Units.ext h
    · intro c hc
      exact ⟨Units.mk0 c (mem_erase.mp hc).1, mem_univ _, rfl⟩
    · intro _ _; rfl
  rw [heq]
  by_cases hp2 : p = 2
  · subst hp2
    have huniv : (Fs.univ : Finset (ZMod 2)ˣ) = {1} := by
      ext u; simp only [mem_univ, mem_singleton, true_iff]
      apply Units.ext
      have hne := u.ne_zero
      change (u : ZMod 2) = 1
      match hu : (u : ZMod 2) with
      | 0 => exact absurd hu hne
      | 1 => rfl
    rw [huniv, Fs.prod_singleton]
    rfl
  · have hself : ∀ u : (ZMod p)ˣ, u = u⁻¹ ↔ u = 1 ∨ u = -1 := by
      intro u
      constructor
      · intro h
        have hsq : (u : ZMod p) ^ 2 = 1 := by
          have huu : u * u = 1 := by
            calc u * u = u * u⁻¹ := by rw [← h]
              _ = 1 := mul_inv_cancel u
          rw [sq, ← Units.val_mul, huu, Units.val_one]
        rcases sq_eq_one_iff.mp hsq with h1 | h1
        · left; exact Units.ext h1
        · right; exact Units.ext h1
      · rintro (rfl | rfl) <;> simp
    have hne : (1 : (ZMod p)ˣ) ≠ -1 := by
      intro h
      have h2 : (2 : ZMod p) = 0 := by
        have := congr_arg Units.val h
        simp only [Units.val_one, Units.val_neg] at this
        linear_combination this
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
      have := Nat.le_of_dvd (by norm_num) hdvd
      have := hp.two_le
      omega
    have hrest : ∏ u ∈ ((Fs.univ : Finset (ZMod p)ˣ).erase 1).erase (-1), (u : ZMod p) = 1 := by
      apply Fs.prod_involution (g := fun u _ => u⁻¹)
      · intro u _; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      · intro u hu _
        simp only [mem_erase, mem_univ, and_true] at hu
        intro heq
        rcases (hself u).mp heq.symm with rfl | rfl
        · exact hu.2 rfl
        · exact hu.1 rfl
      · intro u _; exact inv_inv u
      · intro u hu
        simp only [mem_erase, mem_univ, and_true] at hu ⊢
        refine ⟨?_, ?_⟩
        · intro h; apply hu.1; rw [← inv_inv u, h]; simp
        · intro h; apply hu.2; rw [← inv_inv u, h]; simp
    have hsplit : (Fs.univ : Finset (ZMod p)ˣ) = insert (-1) (insert 1 (((Fs.univ : Finset (ZMod p)ˣ).erase 1).erase (-1))) := by
      ext u; simp only [mem_univ, mem_insert, mem_erase, and_true, true_iff]
      tauto
    rw [hsplit, Fs.prod_insert, Fs.prod_insert, hrest]
    · simp
    · simp
    · simp [hne.symm]
noncomputable def rawF (K : Finset (Fin 3 → ZMod p)) (x : Fin 3 → ZMod p) :
    Mv3 (ZMod p) :=
  ∏ l ∈ v23 K x, v55 l
lemma v125 (K : Finset (Fin 3 → ZMod p)) (x : Fin 3 → ZMod p) :
    (rawF K x).IsHomogeneous (v23 K x).card := by
  unfold rawF
  simpa using IsHomogeneous.prod (v23 K x) (fun l => v55 l) (fun _ => 1)
    (fun l _ => v52 l)
lemma v172 (K : Finset (Fin 3 → ZMod p)) (x u : Fin 3 → ZMod p) :
    eval u (rawF K x) = ∏ l ∈ v23 K x, dot3 l u := by
  simp [rawF, v27]
lemma v109 (K : Finset (Fin 3 → ZMod p)) (x : Fin 3 → ZMod p)
    (ht : (v23 K x).Nonempty) :
    eval x (rawF K x) = 0 := by
  rw [v172]
  rcases ht with ⟨l, hl⟩
  apply prod_eq_zero hl
  exact (mem_filter.mp (mem_filter.mp hl).1).2
lemma v24 {K : Finset (Fin 3 → ZMod p)} {x y : Fin 3 → ZMod p}
    (hy : y ∈ K) (hyx : y ≠ x) :
    eval y (rawF K x) ≠ 0 := by
  rw [v172]
  apply prod_ne_zero_iff.mpr
  intro l hl
  exact (mem_filter.mp hl).2 y hy hyx
lemma v141 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K)
    (hp : p ≠ 2) {x y z : Fin 3 → ZMod p} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    eval y (rawF K x) * eval z (rawF K y) * eval x (rawF K z) = (-1 : ZMod p) ^ (p + 2 - K.card + 1) * (eval x (rawF K y) * eval y (rawF K z) * eval z (rawF K x)) := by
  let B : Finset (Fin 3 → ZMod p) := {x, y, z}
  let R : Finset (Fin 3 → ZMod p) := K \ B
  have hd : det3 x y z ≠ 0 := hK.2 x hx y hy z hz hxy hyz hxz
  have hratio : ∀ (a b c : Fin 3 → ZMod p), a ∈ K → b ∈ K → c ∈ K → a ≠ b → b ≠ c → a ≠ c → eval c (rawF K a) * (∏ s ∈ K \ {a, b, c}, (-det3 a s c)) = -(eval b (rawF K a) * (∏ s ∈ K \ {a, b, c}, det3 a b s)) := by
    intro a b c ha hb hc hab hbc hac
    have hdabc : det3 a b c ≠ 0 := hK.2 a ha b hb c hc hab hbc hac
    let S_sec : Finset (ZMod p) := (K \ {a, b, c}).image (fun s => -det3 a s c / det3 a b s)
    let S_tan : Finset (ZMod p) := (v23 K a).image (fun l => dot3 l c / dot3 l b)
    have hsec_nz : ∀ s ∈ K \ {a, b, c}, det3 a s c ≠ 0 ∧ det3 a b s ≠ 0 := by
      intro s hs
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hs
      exact ⟨hK.2 a ha s hs.1 c hc (Ne.symm hs.2.1) hs.2.2.2 hac, hK.2 a ha b hb s hs.1 hab (Ne.symm hs.2.2.1) (Ne.symm hs.2.1)⟩
    have htan_nz : ∀ l ∈ v23 K a, dot3 l b ≠ 0 ∧ dot3 l c ≠ 0 := by
      intro l hl
      have h2 := (mem_filter.mp hl).2
      exact ⟨h2 b hb hab.symm, h2 c hc hac.symm⟩
    have hinj_sec : Set.InjOn (fun s => -det3 a s c / det3 a b s) ↑(K \ {a, b, c}) := by
      intro s1 hs1 s2 hs2 heq
      simp only [Fs.mem_coe] at hs1 hs2
      have h1 := hsec_nz s1 hs1; have h2 := hsec_nz s2 hs2
      have hcross : -det3 a s1 c * det3 a b s2 = -det3 a s2 c * det3 a b s1 := by
        exact (div_eq_div_iff h1.2 h2.2).mp heq
      have hs1_c := v174 a b c s1
      have hs2_c := v174 a b c s2
      have hdet_eq : det3 a b c * det3 a s1 s2 = det3 a s1 c * det3 a b s2 - det3 a b s1 * det3 a s2 c := by
        have h12 : det3 a (det3 a b c • s1) (det3 a b c • s2) = (det3 a b c) ^ 2 * det3 a s1 s2 := by
          rw [v185, v76]; ring
        rw [hs1_c, hs2_c] at h12
        have hlin : det3 a (det3 s1 b c • a + det3 a s1 c • b + det3 a b s1 • c)
            (det3 s2 b c • a + det3 a s2 c • b + det3 a b s2 • c) =
            det3 a b c * (det3 a s1 c * det3 a b s2 - det3 a b s1 * det3 a s2 c) := by
          simp only [det3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [hlin] at h12
        exact mul_left_cancel₀ hdabc (by linear_combination -h12)
      have hdet0 : det3 a s1 s2 = 0 := by
        apply mul_left_cancel₀ hdabc
        rw [hdet_eq, mul_zero]; linear_combination -hcross
      by_contra hne
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hs1 hs2
      exact hK.2 a ha s1 hs1.1 s2 hs2.1 (Ne.symm hs1.2.1) hne (Ne.symm hs2.2.1) hdet0
    have hinj_tan : Set.InjOn (fun l => dot3 l c / dot3 l b) ↑(v23 K a) := by
      intro l1 hl1 l2 hl2 heq
      simp only [Fs.mem_coe] at hl1 hl2
      have h1 := htan_nz l1 hl1; have h2 := htan_nz l2 hl2
      have h1a : dot3 l1 a = 0 := (mem_filter.mp (mem_filter.mp hl1).1).2
      have h2a : dot3 l2 a = 0 := (mem_filter.mp (mem_filter.mp hl2).1).2
      have hcross : dot3 l1 c * dot3 l2 b = dot3 l2 c * dot3 l1 b :=
        (div_eq_div_iff h1.1 h2.1).mp heq
      have hl_prop : l1 = (dot3 l1 b / dot3 l2 b) • l2 := by
        have h0 : ∀ v : Fin 3 → ZMod p, dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) v = 0 := by
          intro v
          have hv := v174 a b c v
          have hmul : det3 a b c * dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) v = 0 := by
            rw [← v02, hv, v13, v13, v02, v02, v02]
            have hda : dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) a = 0 := by
              have : dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) a = dot3 l1 a - (dot3 l1 b / dot3 l2 b) * dot3 l2 a := by
                simp only [dot3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
              rw [this, h1a, h2a]; ring
            have hdb : dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) b = 0 := by
              have : dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) b = dot3 l1 b - (dot3 l1 b / dot3 l2 b) * dot3 l2 b := by
                simp only [dot3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
              rw [this]; field_simp [h2.1]; ring
            have hdc : dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) c = 0 := by
              have : dot3 (l1 - (dot3 l1 b / dot3 l2 b) • l2) c = dot3 l1 c - (dot3 l1 b / dot3 l2 b) * dot3 l2 c := by
                simp only [dot3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
              rw [this]; field_simp [h2.1]; linear_combination hcross
            rw [hda, hdb, hdc]; ring
          exact (mul_eq_zero.mp hmul).resolve_left hdabc
        ext i; fin_cases i
        · have := h0 ![1, 0, 0]; simp [dot3] at this; exact sub_eq_zero.mp this
        · have := h0 ![0, 1, 0]; simp [dot3] at this; exact sub_eq_zero.mp this
        · have := h0 ![0, 0, 1]; simp [dot3] at this; exact sub_eq_zero.mp this
      have hn1 : v53 l1 := v30.mp (mem_filter.mp (mem_filter.mp hl1).1).1
      have hn2 : v53 l2 := v30.mp (mem_filter.mp (mem_filter.mp hl2).1).1
      exact v04 hn1 hn2 hl_prop
    have hdisj : Disjoint S_sec S_tan := by
      rw [disjoint_left]
      intro r hr1 hr2
      simp only [S_sec, mem_image] at hr1
      simp only [S_tan, mem_image] at hr2
      rcases hr1 with ⟨s, hs, rfl⟩
      rcases hr2 with ⟨l, hl, heq⟩
      have hsnz := hsec_nz s hs
      have htnz := htan_nz l hl
      have hla : dot3 l a = 0 := (mem_filter.mp (mem_filter.mp hl).1).2
      have hcr : dot3 l c * det3 a b s = -det3 a s c * dot3 l b :=
        (div_eq_div_iff htnz.1 hsnz.2).mp heq
      have hls : dot3 l s = 0 := by
        apply mul_left_cancel₀ hdabc
        rw [mul_zero, ← v02, v174 a b c s, v13, v13, v02, v02, v02, hla]
        linear_combination hcr
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hs
      exact (mem_filter.mp hl).2 s hs.1 hs.2.1 hls
    have hunion : S_sec ∪ S_tan = (Fs.univ : Finset (ZMod p)).erase 0 := by
      apply eq_of_subset_of_card_le
      · intro r hr
        rw [mem_erase]
        refine ⟨?_, mem_univ _⟩
        rcases mem_union.mp hr with hr | hr
        · rcases mem_image.mp hr with ⟨s, hs, rfl⟩
          exact div_ne_zero (neg_ne_zero.mpr (hsec_nz s hs).1) (hsec_nz s hs).2
        · rcases mem_image.mp hr with ⟨l, hl, rfl⟩
          exact div_ne_zero (htan_nz l hl).2 (htan_nz l hl).1
      · rw [Fs.card_union_of_disjoint hdisj, card_image_of_injOn hinj_sec, card_image_of_injOn hinj_tan]
        have hsubB : ({a, b, c} : Finset (Fin 3 → ZMod p)) ⊆ K := by
          intro u hu; simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl | rfl <;> assumption
        have hcardB : ({a, b, c} : Finset (Fin 3 → ZMod p)).card = 3 := by
          rw [card_insert_of_notMem, card_pair hbc]; simp [hab, hac]
        rw [Fs.card_sdiff_of_subset hsubB, hcardB]
        have hct := v26 hK ha
        have he0 : ((Fs.univ : Finset (ZMod p)).erase 0).card = p - 1 := by
          rw [card_erase_of_mem (mem_univ 0), card_univ, ZMod.card]
        rw [he0]
        have hK3 : 3 ≤ K.card := by have := card_le_card hsubB; omega
        omega
    have hprod : (∏ s ∈ K \ {a, b, c}, (-det3 a s c / det3 a b s)) * (∏ l ∈ v23 K a, (dot3 l c / dot3 l b)) = -1 := by
      have hp1 : ∏ r ∈ S_sec, r = ∏ s ∈ K \ {a, b, c}, (-det3 a s c / det3 a b s) :=
        Fs.prod_image (fun s1 hs1 s2 hs2 h => hinj_sec hs1 hs2 h)
      have hp2 : ∏ r ∈ S_tan, r = ∏ l ∈ v23 K a, (dot3 l c / dot3 l b) :=
        Fs.prod_image (fun l1 hl1 l2 hl2 h => hinj_tan hl1 hl2 h)
      rw [← hp1, ← hp2, ← Fs.prod_union hdisj, hunion, v190]
    rw [Fs.prod_div_distrib, Fs.prod_div_distrib] at hprod
    have hd1 : ∏ s ∈ K \ {a, b, c}, det3 a b s ≠ 0 :=
      prod_ne_zero_iff.mpr (fun s hs => (hsec_nz s hs).2)
    have hd2 : ∏ l ∈ v23 K a, dot3 l b ≠ 0 :=
      prod_ne_zero_iff.mpr (fun l hl => (htan_nz l hl).1)
    rw [v172, v172]
    have hmul : (∏ s ∈ K \ {a, b, c}, -det3 a s c) * (∏ l ∈ v23 K a, dot3 l c) = -((∏ s ∈ K \ {a, b, c}, det3 a b s) * (∏ l ∈ v23 K a, dot3 l b)) := by
      have hdiv : ((∏ s ∈ K \ {a, b, c}, -det3 a s c) * (∏ l ∈ v23 K a, dot3 l c)) /
          ((∏ s ∈ K \ {a, b, c}, det3 a b s) * (∏ l ∈ v23 K a, dot3 l b)) = -1 := by
        rw [mul_div_mul_comm]; exact hprod
      have := (div_eq_iff (mul_ne_zero hd1 hd2)).mp hdiv
      linear_combination this
    linear_combination hmul
  have h1 := hratio x y z hx hy hz hxy hyz hxz
  have h2 := hratio y z x hy hz hx hyz hxz.symm hxy.symm
  have h3 := hratio z x y hz hx hy hxz.symm hxy hyz.symm
  have hset2 : ({y, z, x} : Finset (Fin 3 → ZMod p)) = B := by ext u; simp [B]; tauto
  have hset3 : ({z, x, y} : Finset (Fin 3 → ZMod p)) = B := by ext u; simp [B]; tauto
  rw [hset2] at h2; rw [hset3] at h3
  have hneg1 : ∏ s ∈ R, (-det3 x s z) = (-1 : ZMod p) ^ R.card * ∏ s ∈ R, det3 z x s := by
    rw [Fs.prod_neg]
    congr 1; apply Fs.prod_congr rfl; intro s _; simp only [det3]; ring
  have hneg2 : ∏ s ∈ R, (-det3 y s x) = (-1 : ZMod p) ^ R.card * ∏ s ∈ R, det3 x y s := by
    rw [Fs.prod_neg]
    congr 1; apply Fs.prod_congr rfl; intro s _; simp only [det3]; ring
  have hneg3 : ∏ s ∈ R, (-det3 z s y) = (-1 : ZMod p) ^ R.card * ∏ s ∈ R, det3 y z s := by
    rw [Fs.prod_neg]
    congr 1; apply Fs.prod_congr rfl; intro s _; simp only [det3]; ring
  change eval z (rawF K x) * (∏ s ∈ R, (-det3 x s z)) = -(eval y (rawF K x) * (∏ s ∈ R, det3 x y s)) at h1
  change eval x (rawF K y) * (∏ s ∈ R, (-det3 y s x)) = -(eval z (rawF K y) * (∏ s ∈ R, det3 y z s)) at h2
  change eval y (rawF K z) * (∏ s ∈ R, (-det3 z s y)) = -(eval x (rawF K z) * (∏ s ∈ R, det3 z x s)) at h3
  rw [hneg1] at h1; rw [hneg2] at h2; rw [hneg3] at h3
  set P := (∏ s ∈ R, det3 z x s) * (∏ s ∈ R, det3 x y s) * (∏ s ∈ R, det3 y z s)
  have hPne : P ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;>
    · apply prod_ne_zero_iff.mpr
      intro s hs
      simp only [R, B, mem_sdiff, mem_insert, mem_singleton, not_or] at hs
      first
      | exact hK.2 z hz x hx s hs.1 hxz.symm (Ne.symm hs.2.1) (Ne.symm hs.2.2.2)
      | exact hK.2 x hx y hy s hs.1 hxy (Ne.symm hs.2.2.1) (Ne.symm hs.2.1)
      | exact hK.2 y hy z hz s hs.1 hyz (Ne.symm hs.2.2.2) (Ne.symm hs.2.2.1)
  have hprod3 :
      (eval y (rawF K x) * eval z (rawF K y) * eval x (rawF K z)) * P =
      (-1 : ZMod p) ^ (3 * R.card + 1) * (eval x (rawF K y) * eval y (rawF K z) * eval z (rawF K x)) * P := by
    have hm := congr_arg₂ (· * ·) (congr_arg₂ (· * ·) h1 h2) h3
    have hpow : (-1 : ZMod p) ^ (3 * R.card + 1) = -((-1 : ZMod p) ^ R.card) ^ 3 := by
      rw [pow_succ, mul_comm 3, pow_mul]; ring
    rw [hpow]
    linear_combination hm
  have hcancel := mul_right_cancel₀ hPne hprod3
  rw [hcancel]
  congr 1
  have hsubB : B ⊆ K := by
    intro u hu; simp only [B, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hcardB : B.card = 3 := by
    simp only [B]; rw [card_insert_of_notMem, card_pair hyz]; simp [hxy, hxz]
  have hRcard : R.card = K.card - 3 := by
    rw [Fs.card_sdiff_of_subset hsubB, hcardB]
  have hK3 : 3 ≤ K.card := by have := card_le_card hsubB; omega
  have hKp1 : K.card ≤ p + 1 := v92 hK hp
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  rcases hp_odd with ⟨m, hm⟩
  have hpar : Even (3 * R.card + 1) ↔ Even (p + 2 - K.card + 1) := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨m + 2 + K.card - k - 4, ?_⟩
      omega
    · rintro ⟨k, hk⟩
      refine ⟨m + 2 + K.card - k - 4, ?_⟩
      omega
  rcases Nat.even_or_odd (3 * R.card + 1) with he | ho
  · have he2 := hpar.mp he
    rw [he.neg_one_pow, he2.neg_one_pow]
  · have ho2 : Odd (p + 2 - K.card + 1) := by
      rcases Nat.even_or_odd (p + 2 - K.card + 1) with h2 | h2
      · exact absurd (hpar.mpr h2) (Nat.not_even_iff_odd.mpr ho)
      · exact h2
    rw [ho.neg_one_pow, ho2.neg_one_pow]
noncomputable def v37 (K : Finset (Fin 3 → ZMod p)) (e x : Fin 3 → ZMod p) :
    Mv3 (ZMod p) :=
  if x = e then rawF K e
  else C ((-1 : ZMod p) ^ (p + 2 - K.card + 1) * eval x (rawF K e) / eval e (rawF K x)) * rawF K x
lemma v106 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K)
    {e x : Fin 3 → ZMod p} (he : e ∈ K) (hx : x ∈ K) :
    (v37 K e x).IsHomogeneous (p + 2 - K.card) := by
  have hct : ∀ y ∈ K, (v23 K y).card = p + 2 - K.card := by
    intro y hy
    have := v26 hK hy
    have h1 : 1 ≤ K.card := card_pos.mpr ⟨y, hy⟩
    omega
  unfold v37
  split_ifs with hxe
  · rw [← hct e he]; exact v125 K e
  · exact v07 _ (hct x hx ▸ v125 K x)
lemma v196 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K) (hp : p ≠ 2)
    {e x y : Fin 3 → ZMod p} (he : e ∈ K) (hx : x ∈ K) (hy : y ∈ K) :
    eval y (v37 K e x) = (-1 : ZMod p) ^ (p + 2 - K.card + 1) * eval x (v37 K e y) := by
  have ht_pos : ∀ z ∈ K, (v23 K z).Nonempty := by
    intro z hz
    have h1 := v26 hK hz
    have h2 := v92 hK hp
    exact card_pos.mp (by omega)
  by_cases hxy : x = y
  · subst hxy
    unfold v37
    split_ifs with hxe
    · subst hxe; rw [v109 K x (ht_pos x hx), mul_zero]
    · simp [v109 K x (ht_pos x hx)]
  · by_cases hxe : x = e
    · subst hxe
      have hye : y ≠ x := Ne.symm hxy
      simp only [v37, ↓reduceIte, hye, map_mul, eval_C]
      have hne := v24 hx hye.symm
      have hsq : (-1 : ZMod p) ^ (p + 2 - K.card + 1) * (-1 : ZMod p) ^ (p + 2 - K.card + 1) = 1 := by
        rw [← mul_pow]; simp
      field_simp [hne]
      linear_combination eval y (rawF K x) * (-hsq)
    · by_cases hye : y = e
      · subst hye
        simp only [v37, ↓reduceIte, hxe, map_mul, eval_C]
        have hne := v24 hy (Ne.symm hxe)
        field_simp [hne]
      · simp only [v37, hxe, hye, ↓reduceIte, map_mul, eval_C]
        have hseg := v141 hK hp hx hy he hxy hye hxe
        have h1 := v24 he (Ne.symm hxe)
        have h2 := v24 he (Ne.symm hye)
        have h3 := v24 hx hxe
        have h4 := v24 hy hye
        have hsq : (-1 : ZMod p) ^ (p + 2 - K.card + 1) * (-1 : ZMod p) ^ (p + 2 - K.card + 1) = 1 := by
          rw [← mul_pow]; simp
        field_simp [h1, h2]
        calc eval x (rawF K e) * eval y (rawF K x) * eval e (rawF K y)
            = eval y (rawF K x) * eval e (rawF K y) * eval x (rawF K e) := by ring
          _ = (-1 : ZMod p) ^ (p + 2 - K.card + 1) * (eval x (rawF K y) * eval y (rawF K e) * eval e (rawF K x)) := hseg
          _ = (-1 : ZMod p) ^ (p + 2 - K.card + 1) * eval e (rawF K x) * eval y (rawF K e) * eval x (rawF K y) := by ring
lemma v158 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K) (hp : p ≠ 2)
    {e x y : Fin 3 → ZMod p} (he : e ∈ K) (hx : x ∈ K) (hy : y ∈ K) :
    (eval y (v37 K e x)) ^ 2 = (eval x (v37 K e y)) ^ 2 := by
  rw [v196 hK hp he hx hy, mul_pow, ← pow_mul, mul_comm _ 2, pow_mul]
  simp
lemma v115 {K : Finset (Fin 3 → ZMod p)} {e x y : Fin 3 → ZMod p}
    (he : e ∈ K) (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) :
    eval y (v37 K e x) ≠ 0 := by
  unfold v37
  split_ifs with hxe
  · subst hxe; exact v24 hy (Ne.symm hxy)
  · simp only [map_mul, eval_C]
    refine mul_ne_zero (div_ne_zero (mul_ne_zero ?_ (v24 hx hxe))
      (v24 he (Ne.symm hxe))) (v24 hy (Ne.symm hxy))
    exact pow_ne_zero _ (by simp)
theorem v165 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K) (hp : p ≠ 2)
    (hcard : K.card = p + 1) :
    ∃ Q : Mv3 (ZMod p), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ ∀ x ∈ K, eval x Q = 0 := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hK4 : 4 ≤ K.card := by omega
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, h01, h12, h02⟩ :
      ∃ e₀ ∈ K, ∃ e₁ ∈ K, ∃ e₂ ∈ K, e₀ ≠ e₁ ∧ e₁ ≠ e₂ ∧ e₀ ≠ e₂ := by
    obtain ⟨e₀, he₀⟩ := card_pos.mp (by omega : 0 < K.card)
    obtain ⟨e₁, he₁⟩ := card_pos.mp (by rw [card_erase_of_mem he₀]; omega : 0 < (K.erase e₀).card)
    have h01 : e₀ ≠ e₁ := (mem_erase.mp he₁).1.symm
    have he₁' : e₁ ∈ K := (mem_erase.mp he₁).2
    obtain ⟨e₂, he₂⟩ := card_pos.mp
      (by rw [card_erase_of_mem he₁, card_erase_of_mem he₀]; omega :
        0 < ((K.erase e₀).erase e₁).card)
    have h12 : e₁ ≠ e₂ := (mem_erase.mp he₂).1.symm
    have h02 : e₀ ≠ e₂ := (mem_erase.mp (mem_erase.mp he₂).2).1.symm
    have he₂' : e₂ ∈ K := (mem_erase.mp (mem_erase.mp he₂).2).2
    exact ⟨e₀, he₀, e₁, he₁', e₂, he₂', h01, h12, h02⟩
  have ht1 : p + 2 - K.card = 1 := by omega
  have hlin : ∀ x ∈ K, ∀ (a b c : ZMod p), eval (a • e₀ + b • e₁ + c • e₂) (v37 K e₀ x) = a * eval e₀ (v37 K e₀ x) + b * eval e₁ (v37 K e₀ x) + c * eval e₂ (v37 K e₀ x) := by
    intro x hx a b c
    have hct : (v23 K x).card = 1 := by
      have := v26 hK hx; omega
    obtain ⟨lx, hlx⟩ := Fs.card_eq_one.mp hct
    have hraw : rawF K x = v55 lx := by simp [rawF, hlx]
    unfold v37
    split_ifs with hxe
    · subst hxe
      have hct0 : (v23 K x).card = 1 := hct
      rw [hraw, v27, v27, v27, v27]
      rw [v13, v13, v02, v02, v02]
    · rw [hraw]
      simp only [map_mul, eval_C, v27, v13, v02]
      ring
  have hsymm : ∀ x ∈ K, ∀ y ∈ K, eval y (v37 K e₀ x) = eval x (v37 K e₀ y) := by
    intro x hx y hy
    have h := v196 hK hp he₀ hx hy
    rw [ht1] at h
    simpa using h
  have hself : ∀ x ∈ K, eval x (v37 K e₀ x) = 0 := by
    intro x hx
    have htne : (v23 K x).Nonempty := by
      have := v26 hK hx; exact card_pos.mp (by omega)
    unfold v37
    split_ifs with hxe
    · subst hxe; exact v109 K x htne
    · simp [v109 K x htne]
  let L₀ : Mv3 (ZMod p) := v55 (cross3 e₁ e₂)
  let L₁ : Mv3 (ZMod p) := v55 (cross3 e₂ e₀)
  let L₂ : Mv3 (ZMod p) := v55 (cross3 e₀ e₁)
  let M01 : ZMod p := eval e₁ (v37 K e₀ e₀)
  let M02 : ZMod p := eval e₂ (v37 K e₀ e₀)
  let M12 : ZMod p := eval e₂ (v37 K e₀ e₁)
  let Q : Mv3 (ZMod p) :=
    C (2 * M01) * (L₀ * L₁) + C (2 * M02) * (L₀ * L₂) + C (2 * M12) * (L₁ * L₂)
  have hD : det3 e₀ e₁ e₂ ≠ 0 := hK.2 e₀ he₀ e₁ he₁ e₂ he₂ h01 h12 h02
  have hQ_hom : Q.IsHomogeneous 2 := by
    have hL0 := v52 (cross3 e₁ e₂)
    have hL1 := v52 (cross3 e₂ e₀)
    have hL2 := v52 (cross3 e₀ e₁)
    refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
    · exact v07 _ (hL0.mul hL1)
    · exact v07 _ (hL0.mul hL2)
    · exact v07 _ (hL1.mul hL2)
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hev : eval (e₀ + e₁) Q = 0 := by rw [hQ0, map_zero]
    have hL0v : eval (e₀ + e₁) L₀ = det3 e₀ e₁ e₂ := by
      simp only [L₀, v27, v13, ← v14, v95, add_zero]
      simp only [det3]; ring
    have hL1v : eval (e₀ + e₁) L₁ = det3 e₀ e₁ e₂ := by
      simp only [L₁, v27, v13, ← v14, v116, zero_add]
      simp only [det3]; ring
    have hL2v : eval (e₀ + e₁) L₂ = 0 := by
      simp only [L₂, v27, v13, ← v14, v95, v116, add_zero]
    simp only [Q, map_add, map_mul, eval_C, hL0v, hL1v, hL2v, mul_zero, add_zero] at hev
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hM01_ne : M01 ≠ 0 := v115 he₀ he₀ he₁ h01
    have hprod_ne : 2 * M01 * (det3 e₀ e₁ e₂ * det3 e₀ e₁ e₂) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2ne hM01_ne) (mul_ne_zero hD hD)
    exact hprod_ne hev
  refine ⟨Q, hQ_ne, hQ_hom, ?_⟩
  intro x hx
  have hcr := v174 e₀ e₁ e₂ x
  set a := det3 x e₁ e₂
  set b := det3 e₀ x e₂
  set c := det3 e₀ e₁ x
  have hL0x : eval x L₀ = a := by
    simp only [L₀, v27, ← v14, a, det3]; ring
  have hL1x : eval x L₁ = b := by
    simp only [L₁, v27, ← v14, b, det3]; ring
  have hL2x : eval x L₂ = c := by
    simp only [L₂, v27, ← v14, c]
  have hx_hom : ∀ y ∈ K, eval (det3 e₀ e₁ e₂ • x) (v37 K e₀ y) = det3 e₀ e₁ e₂ * eval x (v37 K e₀ y) := by
    intro y hy
    have h := v05 (v106 hK he₀ hy) (det3 e₀ e₁ e₂) x
    rw [ht1, pow_one] at h
    exact h
  have h0x : eval (det3 e₀ e₁ e₂ • x) (v37 K e₀ x) = 0 := by
    rw [hx_hom x hx, hself x hx, mul_zero]
  rw [hcr, hlin x hx a b c] at h0x
  have hev0 : eval e₀ (v37 K e₀ x) = (b * M01 + c * M02) / det3 e₀ e₁ e₂ := by
    rw [hsymm x hx e₀ he₀]
    have h := hx_hom e₀ he₀
    rw [hcr, hlin e₀ he₀ a b c, hself e₀ he₀, mul_zero, zero_add] at h
    exact (eq_div_iff hD).mpr (by dsimp only [M01, M02]; linear_combination -h)
  have hev1 : eval e₁ (v37 K e₀ x) = (a * M01 + c * M12) / det3 e₀ e₁ e₂ := by
    rw [hsymm x hx e₁ he₁]
    have h := hx_hom e₁ he₁
    rw [hcr, hlin e₁ he₁ a b c, hself e₁ he₁, mul_zero, add_zero, hsymm e₁ he₁ e₀ he₀] at h
    exact (eq_div_iff hD).mpr (by dsimp only [M01, M12]; linear_combination -h)
  have hev2 : eval e₂ (v37 K e₀ x) = (a * M02 + b * M12) / det3 e₀ e₁ e₂ := by
    rw [hsymm x hx e₂ he₂]
    have h := hx_hom e₂ he₂
    rw [hcr, hlin e₂ he₂ a b c, hself e₂ he₂, mul_zero, add_zero, hsymm e₂ he₂ e₀ he₀, hsymm e₂ he₂ e₁ he₁] at h
    exact (eq_div_iff hD).mpr (by dsimp only [M02, M12]; linear_combination -h)
  rw [hev0, hev1, hev2] at h0x
  have hmul0 : a * (b * M01 + c * M02) + b * (a * M01 + c * M12) + c * (a * M02 + b * M12) = 0 := by
    have := congr_arg (· * det3 e₀ e₁ e₂) h0x
    simp only [zero_mul] at this
    field_simp [hD] at this
    exact this
  simp only [Q, map_add, map_mul, eval_C, hL0x, hL1x, hL2x]
  linear_combination hmul0
lemma v91 {F : Type*} [Field F] {d : ℕ}
    {P : Mv3 F} (hP : P.IsHomogeneous d)
    {y : Fin 3 → F} (hy : y ≠ 0)
    (hkill : ∀ (e₁ e₂ : Fin 3 → F), aeval (fun i : Fin 3 => C (y i) * X (0 : Fin 3) + C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3)) P = aeval (fun i : Fin 3 => C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3)) P)
    {S : Finset (Fin 3 → F)} (hS_card : d + 1 ≤ S.card)
    (hS_noncol : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → det3 y u v ≠ 0)
    (hS_zero : ∀ u ∈ S, eval u P = 0) :
    P = 0 := by
  classical
  have hbasis : ∃ e₁ e₂ : Fin 3 → F, det3 y e₁ e₂ ≠ 0 := by
    have hex : ∃ i : Fin 3, y i ≠ 0 := by
      by_contra hall; push Not at hall; exact hy (funext hall)
    rcases hex with ⟨i, hi⟩
    rcases v03 i with rfl | rfl | rfl
    · exact ⟨![0, 1, 0], ![0, 0, 1], by simp [det3, hi]⟩
    · exact ⟨![0, 0, 1], ![1, 0, 0], by simp [det3, hi]⟩
    · exact ⟨![1, 0, 0], ![0, 1, 0], by simp [det3, hi]⟩
  rcases hbasis with ⟨e₁, e₂, hD⟩
  let subst : Fin 3 → Mv3 F := fun i =>
    C (y i) * X (0 : Fin 3) + C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3)
  let subst0 : Fin 3 → Mv3 F := fun i =>
    C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3)
  let Q : Mv3 F := aeval subst P
  have hQ_eq0 : Q = aeval subst0 P := hkill e₁ e₂
  have hQ_eval : ∀ a b c : F, eval ![a, b, c] Q = eval (a • y + b • e₁ + c • e₂) P := by
    intro a b c
    rw [show Q = aeval subst P from rfl, v101]
    have hf : (fun i => eval ![a, b, c] (subst i)) = a • y + b • e₁ + c • e₂ := by
      funext i; simp [subst]; ring
    rw [hf]
  have hQ_hom : Q.IsHomogeneous d := by
    have hsubst_hom : ∀ i : Fin 3, (subst i).IsHomogeneous 1 := by
      intro i
      refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
      · exact v07 _ (isHomogeneous_X F 0)
      · exact v07 _ (isHomogeneous_X F 1)
      · exact v07 _ (isHomogeneous_X F 2)
    have hQeq : Q = ∑ n ∈ P.support, C (P.coeff n) * ∏ i : Fin 3, (subst i) ^ (n i) := by
      change aeval subst P = _
      conv_lhs => rw [P.as_sum]
      rw [map_sum]
      apply sum_congr rfl; intro n _
      rw [aeval_monomial, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [hQeq]
    apply IsHomogeneous.sum
    intro n hn
    have hnd : ∑ i : Fin 3, n i = d := by
      have := hP (Mv.mem_support_iff.mp hn)
      simpa [Fu.weight_apply, Fu.sum_fintype] using this
    have hprod_hom : (∏ i : Fin 3, (subst i) ^ (n i)).IsHomogeneous (∑ i : Fin 3, n i) := by
      simpa using IsHomogeneous.prod Fs.univ (fun i => (subst i) ^ (n i)) (fun i => n i)
        (fun i _ => by simpa using (hsubst_hom i).pow (n i))
    rw [hnd] at hprod_hom
    exact v07 (P.coeff n) hprod_hom
  suffices hQ0 : Q = 0 by
    let D := det3 y e₁ e₂
    let invSubst : Fin 3 → Mv3 F :=
      ![C D⁻¹ * v55 (cross3 e₁ e₂), C D⁻¹ * v55 (cross3 e₂ y), C D⁻¹ * v55 (cross3 y e₁)]
    have hcomp : ∀ i : Fin 3, aeval invSubst (subst i) = X i := by
      intro i
      simp only [subst, map_add, map_mul, aeval_C, Mv.algebraMap_eq, aeval_X, invSubst, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val, v55]
      have hcr : ∀ j : Fin 3, y i * (cross3 e₁ e₂ j) + e₁ i * (cross3 e₂ y j) + e₂ i * (cross3 y e₁ j) = if i = j then D else 0 := by
        intro j
        rcases v03 i with rfl | rfl | rfl <;> rcases v03 j with rfl | rfl | rfl <;>
          simp only [cross3, D, det3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val, ↓reduceIte, Fi.reduceEq] <;> ring
      have hsum :
          (C (y i) * (C D⁻¹ * (C (cross3 e₁ e₂ 0) * X (0 : Fin 3) + C (cross3 e₁ e₂ 1) * X 1 + C (cross3 e₁ e₂ 2) * X 2)) +
          C (e₁ i) * (C D⁻¹ * (C (cross3 e₂ y 0) * X 0 + C (cross3 e₂ y 1) * X 1 + C (cross3 e₂ y 2) * X 2)) +
          C (e₂ i) * (C D⁻¹ * (C (cross3 y e₁ 0) * X 0 + C (cross3 y e₁ 1) * X 1 + C (cross3 y e₁ 2) * X 2)) :
            Mv3 F) =
          C (D⁻¹ * (y i * cross3 e₁ e₂ 0 + e₁ i * cross3 e₂ y 0 + e₂ i * cross3 y e₁ 0)) * X 0 +
          C (D⁻¹ * (y i * cross3 e₁ e₂ 1 + e₁ i * cross3 e₂ y 1 + e₂ i * cross3 y e₁ 1)) * X 1 +
          C (D⁻¹ * (y i * cross3 e₁ e₂ 2 + e₁ i * cross3 e₂ y 2 + e₂ i * cross3 y e₁ 2)) * X 2 := by
        simp only [map_add, map_mul]; ring
      rw [hsum, hcr 0, hcr 1, hcr 2]
      rcases v03 i with rfl | rfl | rfl <;> simp [D, inv_mul_cancel₀ hD]
    have hPeq : P = aeval invSubst Q := by
      dsimp only [Q]
      rw [aeval_comp_eq]
      have hf : (fun i => aeval invSubst (subst i)) = X := funext hcomp
      rw [hf, v202]
    rw [hPeq, hQ0, map_zero]
  have hQ_no0 : ∀ m ∈ Q.support, m 0 = 0 := by
    intro m hm
    rw [hQ_eq0] at hm
    have hmem : ∀ R : Mv3 F, ∀ n ∈ (aeval subst0 R).support, n 0 = 0 := by
      intro R
      induction R using Mv.induction_on' with
      | monomial k c =>
        intro n hn
        simp only [aeval_monomial, algebraMap_eq] at hn
        have hfac : ∀ (T : Mv3 F), (∀ r ∈ T.support, r 0 = 0) → ∀ k : ℕ, ∀ r ∈ (T ^ k).support, r 0 = 0 := by
          intro T hT k
          induction k with
          | zero =>
            intro r hr
            simp only [pow_zero] at hr
            have : r = 0 := by
              rw [Mv.mem_support_iff, Mv.coeff_one] at hr
              by_contra hne; exact hr (if_neg (Ne.symm hne))
            simp [this]
          | succ k ih =>
            intro r hr
            rw [pow_succ] at hr
            rcases Fs.mem_add.mp (Mv.support_mul _ _ hr) with ⟨a, ha, b, hb, rfl⟩
            simp [ih a ha, hT b hb]
        have hsub0 : ∀ i : Fin 3, ∀ r ∈ (subst0 i).support, r 0 = 0 := by
          intro i r hr
          rcases mem_union.mp (Mv.support_add hr) with hr1 | hr2
          · rcases Fs.mem_add.mp (Mv.support_mul _ _ hr1) with ⟨a, ha, b, hb, rfl⟩
            have ha0 : a = 0 := by
              rw [Mv.mem_support_iff, Mv.coeff_C] at ha
              by_contra hne; exact ha (if_neg (Ne.symm hne))
            have hb0 : b = Fu.single 1 1 := by
              rw [Mv.mem_support_iff, Mv.coeff_X] at hb
              by_contra hne; exact hb (if_neg (Ne.symm hne))
            simp [ha0, hb0]
          · rcases Fs.mem_add.mp (Mv.support_mul _ _ hr2) with ⟨a, ha, b, hb, rfl⟩
            have ha0 : a = 0 := by
              rw [Mv.mem_support_iff, Mv.coeff_C] at ha
              by_contra hne; exact ha (if_neg (Ne.symm hne))
            have hb0 : b = Fu.single 2 1 := by
              rw [Mv.mem_support_iff, Mv.coeff_X] at hb
              by_contra hne; exact hb (if_neg (Ne.symm hne))
            simp [ha0, hb0]
        rcases Fs.mem_add.mp (Mv.support_mul _ _ hn) with ⟨a, ha, b, hb, rfl⟩
        have ha0 : a = 0 := by
          rw [Mv.mem_support_iff, Mv.coeff_C] at ha
          by_contra hne; exact ha (if_neg (Ne.symm hne))
        have hprod_eq : k.prod (fun i e => subst0 i ^ e) = (subst0 0 ^ k 0) * (subst0 1 ^ k 1) * (subst0 2 ^ k 2) := by
          rw [Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
        rw [hprod_eq] at hb
        rcases Fs.mem_add.mp (Mv.support_mul _ _ hb) with ⟨b1, hb1, b2, hb2, rfl⟩
        rcases Fs.mem_add.mp (Mv.support_mul _ _ hb1) with ⟨b10, hb10, b11, hb11, rfl⟩
        simp [ha0, hfac _ (hsub0 0) _ _ hb10, hfac _ (hsub0 1) _ _ hb11, hfac _ (hsub0 2) _ _ hb2]
      | add p₁ p₂ ih₁ ih₂ =>
        intro n hn
        rw [map_add] at hn
        rcases mem_union.mp (Mv.support_add hn) with h1 | h2
        · exact ih₁ n h1
        · exact ih₂ n h2
    exact hmem P m hm
  have hQ_mon : ∀ m ∈ Q.support, m 0 = 0 ∧ m 1 + m 2 = d := by
    intro m hm
    have h0 := hQ_no0 m hm
    have hsum : m 0 + m 1 + m 2 = d := by
      have := hQ_hom (Mv.mem_support_iff.mp hm)
      simpa [Fu.weight_apply, Fu.sum_fintype, Fi.sum_univ_three] using this
    exact ⟨h0, by omega⟩
  let q : Pol F := aeval ![0, Pl.X, 1] Q
  have hq_coeff : ∀ k : ℕ, q.coeff k = if hk : k ≤ d then Q.coeff (Fu.single 1 k + Fu.single 2 (d - k)) else 0 := by
    intro k
    have hq_eq : q = ∑ m ∈ Q.support, Pl.C (Q.coeff m) * Pl.X ^ (m 1) := by
      change aeval ![0, Pl.X, 1] Q = _
      conv_lhs => rw [Q.as_sum]
      rw [map_sum]
      apply sum_congr rfl
      intro m hm
      rw [aeval_monomial, Pl.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
      simp [(hQ_mon m hm).1]
    rw [hq_eq, Pl.finsetSum_coeff]
    split_ifs with hk
    · set m₀ : E3 := Fu.single 1 k + Fu.single 2 (d - k)
      by_cases hm₀ : m₀ ∈ Q.support
      · rw [sum_eq_single m₀]
        · simp [m₀]
        · intro m hm hne
          simp only [Pl.coeff_C_mul_X_pow]
          rw [if_neg]
          intro hmk
          apply hne
          ext i; fin_cases i
          · simp [m₀, (hQ_mon m hm).1]
          · simp [m₀, hmk]
          · have := (hQ_mon m hm).2; simp [m₀]; omega
        · intro h; exact absurd hm₀ h
      · rw [Mv.notMem_support_iff.mp hm₀]
        apply sum_eq_zero
        intro m hm
        simp only [Pl.coeff_C_mul_X_pow]
        rw [if_neg]
        intro hmk
        apply hm₀
        have heq : m = m₀ := by
          ext i; fin_cases i
          · simp [m₀, (hQ_mon m hm).1]
          · simp [m₀, hmk]
          · have := (hQ_mon m hm).2; simp [m₀]; omega
        exact heq ▸ hm
    · apply sum_eq_zero
      intro m hm
      simp only [Pl.coeff_C_mul_X_pow]
      rw [if_neg]
      intro hmk
      have := (hQ_mon m hm).2
      omega
  have hq_deg : q.natDegree ≤ d := by
    apply Pl.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [hq_coeff k, dif_neg (by omega)]
  have hq_zero_imp : q = 0 → Q = 0 := by
    intro hq0
    ext m
    rw [Mv.coeff_zero]
    by_contra hm_ne
    have hm : m ∈ Q.support := Mv.mem_support_iff.mpr hm_ne
    have ⟨h0, h12⟩ := hQ_mon m hm
    have hmeq : m = Fu.single 1 (m 1) + Fu.single 2 (d - m 1) := by
      ext i; fin_cases i
      · simp [h0]
      · simp
      · simp; omega
    have hc := hq_coeff (m 1)
    rw [hq0, Pl.coeff_zero, dif_pos (by omega), ← hmeq] at hc
    exact hm_ne hc.symm
  let b_of (u : Fin 3 → F) : F := det3 y u e₂
  let c_of (u : Fin 3 → F) : F := det3 y e₁ u
  have hQ_bc : ∀ u ∈ S, eval ![0, b_of u, c_of u] Q = 0 := by
    intro u hu
    have hcr := v174 y e₁ e₂ u
    have hev : eval ![det3 u e₁ e₂, b_of u, c_of u] Q = 0 := by
      rw [hQ_eval, ← hcr, v05 hP, hS_zero u hu, mul_zero]
    have hdep : eval ![det3 u e₁ e₂, b_of u, c_of u] Q = eval ![0, b_of u, c_of u] Q := by
      rw [hQ_eq0, v101, v101]
      have hf : (fun i => eval ![det3 u e₁ e₂, b_of u, c_of u] (subst0 i)) = (fun i => eval ![0, b_of u, c_of u] (subst0 i)) := by funext i; simp [subst0]
      rw [hf]
    exact hdep ▸ hev
  have hratio_ne : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → b_of u * c_of v ≠ b_of v * c_of u := by
    intro u hu v hv huv heq
    have h12 : det3 y (det3 y e₁ e₂ • u) (det3 y e₁ e₂ • v) = (det3 y e₁ e₂) ^ 2 * det3 y u v := by
      rw [v185, v76]; ring
    rw [v174 y e₁ e₂ u, v174 y e₁ e₂ v] at h12
    have hlin : det3 y (det3 u e₁ e₂ • y + b_of u • e₁ + c_of u • e₂)
        (det3 v e₁ e₂ • y + b_of v • e₁ + c_of v • e₂) =
        det3 y e₁ e₂ * (b_of u * c_of v - b_of v * c_of u) := by
      simp only [det3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hlin, heq, sub_self, mul_zero] at h12
    exact mul_ne_zero (pow_ne_zero 2 hD) (hS_noncol u hu v hv huv) h12.symm
  let S₀ := S.filter (fun u => c_of u = 0)
  let S₁ := S.filter (fun u => c_of u ≠ 0)
  have hS0_le : S₀.card ≤ 1 := by
    rw [Fs.card_le_one]
    intro u hu v hv
    simp only [S₀, mem_filter] at hu hv
    by_contra huv
    exact hratio_ne u hu.1 v hv.1 huv (by rw [hu.2, hv.2, mul_zero, mul_zero])
  have hS1_roots : ∀ u ∈ S₁, q.IsRoot (b_of u / c_of u) := by
    intro u hu
    simp only [S₁, mem_filter] at hu
    rw [Pl.IsRoot]
    have hq_ev : q.eval (b_of u / c_of u) = eval ![0, b_of u / c_of u, 1] Q := by
      rw [show q = aeval ![0, Pl.X, 1] Q from rfl, v124]
      have hf : (fun i => ((![0, Pl.X, 1] : Fin 3 → Pol F) i).eval (b_of u / c_of u)) = ![0, b_of u / c_of u, 1] := by
        funext i; rcases v03 i with rfl | rfl | rfl <;> simp
      rw [hf]
    rw [hq_ev]
    have hsc : ![0, b_of u / c_of u, 1] = (c_of u)⁻¹ • ![0, b_of u, c_of u] := by
      ext i; rcases v03 i with rfl | rfl | rfl <;>
        simp [div_eq_inv_mul, inv_mul_cancel₀ hu.2]
    rw [hsc, v05 hQ_hom, hQ_bc u hu.1, mul_zero]
  have hinj_S1 : Set.InjOn (fun u => b_of u / c_of u) ↑S₁ := by
    intro u hu v hv heq
    simp only [Fs.mem_coe, S₁, mem_filter] at hu hv
    by_contra huv
    exact hratio_ne u hu.1 v hv.1 huv ((div_eq_div_iff hu.2 hv.2).mp heq)
  have hS_part : S₀.card + S₁.card = S.card := by
    simpa [S₀, S₁] using Fs.card_filter_add_card_filter_not (s := S) (p := fun u => c_of u = 0)
  apply hq_zero_imp
  by_contra hq_ne
  let R_roots : Finset F := S₁.image (fun u => b_of u / c_of u)
  have hR_sub : R_roots.val ⊆ q.roots := by
    intro r hr
    rw [Fs.mem_val] at hr
    rcases mem_image.mp hr with ⟨u, hu, rfl⟩
    exact (Pl.mem_roots hq_ne).mpr (hS1_roots u hu)
  have hR_card_le : R_roots.card ≤ q.natDegree := by
    have h1 : R_roots.val.card ≤ q.roots.card := Mu.card_le_card (Mu.le_iff_subset R_roots.nodup |>.mpr hR_sub)
    exact h1.trans (Pl.card_roots' q)
  rw [card_image_of_injOn hinj_S1] at hR_card_le
  by_cases hS0_empty : S₀.card = 0
  · omega
  ·
    obtain ⟨u₀, hu₀⟩ := card_pos.mp (by omega : 0 < S₀.card)
    simp only [S₀, mem_filter] at hu₀
    by_cases hd0 : d = 0
    · exfalso
      have hq0 : q = 0 := by
        ext k
        rw [hq_coeff k, Pl.coeff_zero]
        split_ifs with hk
        · have hk0 : k = 0 := by omega
          subst hk0
          have hQ0' := hQ_bc u₀ hu₀.1
          have hQc : eval ![0, b_of u₀, c_of u₀] Q = Q.coeff 0 := by
            conv_lhs => rw [Q.as_sum]
            rw [map_sum]
            have hsupp : ∀ m ∈ Q.support, m = 0 := by
              intro m hm
              have ⟨h0, h12⟩ := hQ_mon m hm
              ext i; rcases v03 i with rfl | rfl | rfl
              · simp [h0]
              · simp; omega
              · simp; omega
            by_cases h0s : (0 : E3) ∈ Q.support
            · rw [sum_eq_single 0]
              · simp
              · intro m hm hne; exact absurd (hsupp m hm) hne
              · intro h; exact absurd h0s h
            · rw [Mv.notMem_support_iff.mp h0s]
              apply sum_eq_zero; intro m hm; exact absurd (hsupp m hm) (fun h => h0s (h ▸ hm))
          rw [hQc] at hQ0'
          simpa [hd0] using hQ0'
        · rfl
      exact hq_ne hq0
    · have hb₀_ne : b_of u₀ ≠ 0 := by
        obtain ⟨v, hvS, hvu⟩ := exists_mem_ne (by omega : 1 < S.card) u₀
        intro hb0
        exact hratio_ne u₀ hu₀.1 v hvS hvu.symm (by rw [hb0, hu₀.2, zero_mul, mul_zero])
      have hcoeff_d : q.coeff d = 0 := by
        rw [hq_coeff d, dif_pos le_rfl]
        have hsc : ![0, (1 : F), 0] = (b_of u₀)⁻¹ • ![0, b_of u₀, c_of u₀] := by
          ext i; rcases v03 i with rfl | rfl | rfl <;>
            simp [inv_mul_cancel₀ hb₀_ne, hu₀.2]
        have hev1 : eval ![0, (1 : F), 0] Q = 0 := by
          rw [hsc, v05 hQ_hom, hQ_bc u₀ hu₀.1, mul_zero]
        have hev_eq : eval ![0, (1 : F), 0] Q = Q.coeff (Fu.single 1 d) := by
          conv_lhs => rw [Q.as_sum]
          rw [map_sum]
          by_cases hsd : Fu.single (1 : Fin 3) d ∈ Q.support
          · rw [sum_eq_single (Fu.single 1 d)]
            · simp [eval_monomial, Fu.prod_fintype, Fi.prod_univ_three]
            · intro m hm hne
              have ⟨h0, h12⟩ := hQ_mon m hm
              have hm2 : m 2 ≠ 0 := by
                intro h2; apply hne
                ext i; rcases v03 i with rfl | rfl | rfl
                · simp [h0]
                · simp; omega
                · simp [h2]
              simp [eval_monomial, Fu.prod_fintype, Fi.prod_univ_three, zero_pow hm2]
            · intro h; exact absurd hsd h
          · rw [Mv.notMem_support_iff.mp hsd]
            apply sum_eq_zero
            intro m hm
            have ⟨h0, h12⟩ := hQ_mon m hm
            have hm2 : m 2 ≠ 0 := by
              intro h2; apply hsd
              have heq : m = Fu.single 1 d := by
                ext i; rcases v03 i with rfl | rfl | rfl
                · simp [h0]
                · simp; omega
                · simp [h2]
              exact heq ▸ hm
            simp [eval_monomial, Fu.prod_fintype, Fi.prod_univ_three, zero_pow hm2]
        simpa [Nat.sub_self] using hev_eq.symm.trans hev1
      have hq_deg_lt : q.natDegree ≤ d - 1 := by
        apply Pl.natDegree_le_iff_coeff_eq_zero.mpr
        intro k hk
        by_cases hkd : k = d
        · exact hkd ▸ hcoeff_d
        · rw [hq_coeff k, dif_neg (by omega)]
      omega
set_option maxHeartbeats 1600000 in
theorem v208 {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K) (hp : p ≠ 2)
    (hsize : 2 * (p + 2 - K.card) + 2 ≤ K.card) :
    ∃ φ : Mv3 (ZMod p), φ ≠ 0 ∧ φ.IsHomogeneous (2 * (p + 2 - K.card)) ∧ ∀ y ∈ K, (∀ l ∈ v23 K y, eval l φ = 0) ∧ (∀ {L : Type*} [Field L] (ι : ZMod p →+* L) (z : Fin 3 → L), z ≠ 0 → dot3 z (ι ∘ y) = 0 → eval z (Mv.map ι φ) = 0 → ∃ l ∈ v23 K y, ∃ c : L, z = c • (ι ∘ l)) := by
  set t := p + 2 - K.card
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨E, hEK, hEcard⟩ := Fs.exists_subset_card_eq hsize
  obtain ⟨e, heE⟩ := card_pos.mp (by omega : 0 < E.card)
  have heK : e ∈ K := hEK heE
  let φ : Mv3 (ZMod p) :=
    ∑ ab ∈ E.offDiag, C ((eval ab.2 (v37 K e ab.1)) ^ 2 * (2 : ZMod p)⁻¹) * ∏ u ∈ (E.erase ab.1).erase ab.2, C (det3 ab.1 ab.2 u)⁻¹ * v55 u
  have hφ_hom : φ.IsHomogeneous (2 * t) := by
    apply IsHomogeneous.sum
    intro ab hab
    rcases mem_offDiag.mp hab with ⟨haE, hbE, hab_ne⟩
    have hcard_er : ((E.erase ab.1).erase ab.2).card = 2 * t := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨hab_ne.symm, hbE⟩), card_erase_of_mem haE, hEcard]
      omega
    have hprod_hom : (∏ u ∈ (E.erase ab.1).erase ab.2, C (det3 ab.1 ab.2 u)⁻¹ * v55 u).IsHomogeneous
        ((E.erase ab.1).erase ab.2).card := by
      simpa using IsHomogeneous.prod ((E.erase ab.1).erase ab.2)
        (fun u => C (det3 ab.1 ab.2 u)⁻¹ * v55 u) (fun _ => 1)
        (fun u _ => v07 _ (v52 u))
    rw [hcard_er] at hprod_hom
    exact v07 _ hprod_hom
  let crossPoly (y : Fin 3 → ZMod p) : Fin 3 → Mv3 (ZMod p) :=
    ![C (y 1) * X 2 - C (y 2) * X 1, C (y 2) * X 0 - C (y 0) * X 2, C (y 0) * X 1 - C (y 1) * X 0]
  have hcross_lin : ∀ (y u : Fin 3 → ZMod p), aeval (crossPoly y) (v55 u) = v55 (cross3 u y) := by
    intro y u
    simp only [v55, crossPoly, cross3, map_add, map_sub, map_mul, aeval_C, Mv.algebraMap_eq, aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
    ring
  have hcross_eval : ∀ (y v : Fin 3 → ZMod p) (P : Mv3 (ZMod p)), eval v (aeval (crossPoly y) P) = eval (cross3 y v) P := by
    intro y v P
    rw [v101]
    have hf : (fun i => eval v (crossPoly y i)) = cross3 y v := by
      funext i; rcases v03 i with rfl | rfl | rfl <;> simp [crossPoly, cross3]
    rw [hf]
  have hcross_hom : ∀ (y : Fin 3 → ZMod p), (aeval (crossPoly y) φ).IsHomogeneous (2 * t) := by
    intro y
    have hcp_hom : ∀ i : Fin 3, (crossPoly y i).IsHomogeneous 1 := by
      intro i; rcases v03 i with rfl | rfl | rfl <;>
      · simp only [crossPoly, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val]
        apply IsHomogeneous.sub <;> exact v07 _ (isHomogeneous_X (ZMod p) _)
    have hφeq : aeval (crossPoly y) φ = ∑ n ∈ φ.support, C (φ.coeff n) * ∏ i : Fin 3, (crossPoly y i) ^ (n i) := by
      conv_lhs => rw [φ.as_sum]
      rw [map_sum]
      apply sum_congr rfl; intro n _
      rw [aeval_monomial, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [hφeq]
    apply IsHomogeneous.sum
    intro n hn
    have hnd : ∑ i : Fin 3, n i = 2 * t := by
      have := hφ_hom (Mv.mem_support_iff.mp hn)
      simpa [Fu.weight_apply, Fu.sum_fintype] using this
    have hprod_hom : (∏ i : Fin 3, (crossPoly y i) ^ (n i)).IsHomogeneous (∑ i : Fin 3, n i) := by
      simpa using IsHomogeneous.prod Fs.univ (fun i => (crossPoly y i) ^ (n i)) (fun i => n i)
        (fun i _ => by simpa using (hcp_hom i).pow (n i))
    rw [hnd] at hprod_hom
    exact v07 _ hprod_hom
  have hkill_lin : ∀ (y l e₁ e₂ : Fin 3 → ZMod p), dot3 l y = 0 → aeval (fun i : Fin 3 => C (y i) * X (0 : Fin 3) + C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3))
        (v55 l) =
      aeval (fun i : Fin 3 => C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3)) (v55 l) := by
    intro y l e₁ e₂ hly
    have h1 : C (l 0) * (C (y 0) * X (0 : Fin 3) + C (e₁ 0) * X (1 : Fin 3) + C (e₂ 0) * X (2 : Fin 3)) + C (l 1) * (C (y 1) * X (0 : Fin 3) + C (e₁ 1) * X (1 : Fin 3) + C (e₂ 1) * X (2 : Fin 3)) + C (l 2) * (C (y 2) * X (0 : Fin 3) + C (e₁ 2) * X (1 : Fin 3) + C (e₂ 2) * X (2 : Fin 3)) = C (dot3 l y) * X (0 : Fin 3) + C (dot3 l e₁) * X (1 : Fin 3) + C (dot3 l e₂) * X (2 : Fin 3) := by
      simp only [dot3, map_add, map_mul]; ring
    have h2 : C (l 0) * (C (e₁ 0) * X (1 : Fin 3) + C (e₂ 0) * X (2 : Fin 3)) + C (l 1) * (C (e₁ 1) * X (1 : Fin 3) + C (e₂ 1) * X (2 : Fin 3)) + C (l 2) * (C (e₁ 2) * X (1 : Fin 3) + C (e₂ 2) * X (2 : Fin 3)) = C (dot3 l e₁) * X (1 : Fin 3) + C (dot3 l e₂) * X (2 : Fin 3) := by
      simp only [dot3, map_add, map_mul]; ring
    simp only [v55, map_add, map_mul, aeval_C, Mv.algebraMap_eq, aeval_X]
    rw [h1, h2, hly, map_zero, zero_mul, zero_add]
  have hkill_hy : ∀ (y e₁ e₂ : Fin 3 → ZMod p), aeval (fun i : Fin 3 => C (y i) * X (0 : Fin 3) + C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3))
        (aeval (crossPoly y) φ) =
      aeval (fun i : Fin 3 => C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3))
        (aeval (crossPoly y) φ) := by
    intro y e₁ e₂
    dsimp only [φ]
    simp only [map_sum, map_mul, aeval_C, Mv.algebraMap_eq, map_prod, hcross_lin]
    apply sum_congr rfl; intro ab _; congr 1
    apply Fs.prod_congr rfl; intro u _; congr 1
    exact hkill_lin y (cross3 u y) e₁ e₂ (v28 u y)
  have hkill_sf : ∀ (y : Fin 3 → ZMod p), y ∈ K → ∀ (e₁ e₂ : Fin 3 → ZMod p), aeval (fun i : Fin 3 => C (y i) * X (0 : Fin 3) + C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3))
        ((v37 K e y) ^ 2) =
      aeval (fun i : Fin 3 => C (e₁ i) * X (1 : Fin 3) + C (e₂ i) * X (2 : Fin 3))
        ((v37 K e y) ^ 2) := by
    intro y hy e₁ e₂
    rw [map_pow, map_pow]
    apply congr_arg (· ^ 2)
    unfold v37
    split_ifs with hye
    · simp only [rawF, map_prod]
      apply Fs.prod_congr rfl; intro l hl
      have hly : dot3 l y = 0 := by
        rw [hye]; exact (mem_filter.mp (mem_filter.mp hl).1).2
      exact hkill_lin y l e₁ e₂ hly
    · simp only [rawF, map_mul, aeval_C, Mv.algebraMap_eq, map_prod]
      apply congr_arg (_ * ·)
      apply Fs.prod_congr rfl; intro l hl
      exact hkill_lin y l e₁ e₂ (mem_filter.mp (mem_filter.mp hl).1).2
  have hsf_sq_hom : ∀ y ∈ K, ((v37 K e y) ^ 2).IsHomogeneous (2 * t) := by
    intro y hyK
    have h := (v106 hK heK hyK).pow 2
    rwa [mul_comm] at h
  have hstep1 : ∀ y ∈ E, aeval (crossPoly y) φ = (v37 K e y) ^ 2 := by
    intro y hyE
    have hyK : y ∈ K := hEK hyE
    apply sub_eq_zero.mp
    apply v91 (d := 2 * t)
      ((hcross_hom y).sub (hsf_sq_hom y hyK))
      (v00 (hK.1 y hyK))
    · intro e₁ e₂
      rw [map_sub, map_sub, hkill_hy y e₁ e₂, hkill_sf y hyK e₁ e₂]
    · show 2 * t + 1 ≤ (E.erase y).card
      rw [card_erase_of_mem hyE, hEcard]; omega
    · intro u hu v hv huv
      exact hK.2 y hyK u (hEK (mem_erase.mp hu).2) v (hEK (mem_erase.mp hv).2)
        (mem_erase.mp hu).1.symm huv (mem_erase.mp hv).1.symm
    · intro c hc
      rcases mem_erase.mp hc with ⟨hcy, hcE⟩
      rw [map_sub, sub_eq_zero, hcross_eval]
      simp only [φ, map_sum, map_mul, eval_C, map_prod, v27]
      have hdot_det : ∀ u : Fin 3 → ZMod p, dot3 u (cross3 y c) = det3 y c u := fun u => by
        rw [v45, ← v14]
      simp_rw [hdot_det]
      have hterm_zero : ∀ ab ∈ E.offDiag, ab ≠ (y, c) → ab ≠ (c, y) → (eval ab.2 (v37 K e ab.1)) ^ 2 * (2 : ZMod p)⁻¹ * ∏ u ∈ (E.erase ab.1).erase ab.2, (det3 ab.1 ab.2 u)⁻¹ * det3 y c u = 0 := by
        intro ab hab h1 h2
        rcases mem_offDiag.mp hab with ⟨haE, hbE, hab_ne⟩
        have hor : y ∈ (E.erase ab.1).erase ab.2 ∨ c ∈ (E.erase ab.1).erase ab.2 := by
          by_contra hneither
          simp only [mem_erase, not_or, not_and] at hneither
          rcases hneither with ⟨hy_eq, hc_eq⟩
          by_cases hya : y = ab.1
          · by_cases hcb : c = ab.2
            · exact h1 (Prod.ext hya.symm hcb.symm)
            · have hca : c = ab.1 := by
                by_contra hca; exact absurd (hc_eq hcb hca) (not_not.mpr hcE)
              exact hcy (hca.trans hya.symm)
          · have hyb : y = ab.2 := by
              by_contra hyb; exact absurd (hy_eq hyb hya) (not_not.mpr hyE)
            by_cases hca : c = ab.1
            · exact h2 (Prod.ext hca.symm hyb.symm)
            · have hcb : c = ab.2 := by
                by_contra hcb; exact absurd (hc_eq hcb hca) (not_not.mpr hcE)
              exact hcy (hcb.trans hyb.symm)
        rcases hor with hy_in | hc_in
        · rw [prod_eq_zero hy_in (by rw [v95, mul_zero]), mul_zero]
        · rw [prod_eq_zero hc_in (by rw [v116, mul_zero]), mul_zero]
      have hyc_mem : (y, c) ∈ E.offDiag := mem_offDiag.mpr ⟨hyE, hcE, hcy.symm⟩
      have hcy_mem : (c, y) ∈ E.offDiag := mem_offDiag.mpr ⟨hcE, hyE, hcy⟩
      have hpair_ne : (y, c) ≠ (c, y) := fun h => hcy (congr_arg Prod.fst h).symm
      rw [Fs.sum_eq_add (y, c) (c, y) hpair_ne (fun ab hab h1 => hterm_zero ab hab h1.1 h1.2) (fun h => absurd hyc_mem h) (fun h => absurd hcy_mem h)]
      have hprod_yc : ∏ u ∈ (E.erase y).erase c, (det3 y c u)⁻¹ * det3 y c u = 1 := by
        apply Fs.prod_eq_one; intro u hu
        have huc : u ≠ c := (mem_erase.mp hu).1
        have huy : u ≠ y := (mem_erase.mp (mem_erase.mp hu).2).1
        have huK : u ∈ K := hEK (mem_erase.mp (mem_erase.mp hu).2).2
        exact inv_mul_cancel₀ (hK.2 y hyK c (hEK hcE) u huK hcy.symm huc.symm huy.symm)
      have hprod_cy : ∏ u ∈ (E.erase c).erase y, (det3 c y u)⁻¹ * det3 y c u = 1 := by
        have hcard_er : ((E.erase c).erase y).card = 2 * t := by
          rw [card_erase_of_mem (mem_erase.mpr ⟨hcy.symm, hyE⟩), card_erase_of_mem hcE, hEcard]; omega
        have heq1 : ∏ u ∈ (E.erase c).erase y, (det3 c y u)⁻¹ * det3 y c u = ∏ u ∈ (E.erase c).erase y, (-1 : ZMod p) := by
          apply Fs.prod_congr rfl; intro u hu
          have huy : u ≠ y := (mem_erase.mp hu).1
          have huc : u ≠ c := (mem_erase.mp (mem_erase.mp hu).2).1
          have huK : u ∈ K := hEK (mem_erase.mp (mem_erase.mp hu).2).2
          have hne := hK.2 y hyK c (hEK hcE) u huK hcy.symm huc.symm huy.symm
          rw [v206, inv_neg, neg_mul, inv_mul_cancel₀ hne]
        rw [heq1, Fs.prod_const, hcard_er, pow_mul]
        simp
      rw [hprod_yc, hprod_cy, mul_one, mul_one, v158 hK hp heK (hEK hcE) hyK]
      have hhalf : (2⁻¹ : ZMod p) + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2ne]
      rw [← mul_add, hhalf, mul_one, map_pow]
  have hstep2 : ∀ y ∈ K, aeval (crossPoly y) φ = (v37 K e y) ^ 2 := by
    intro y hyK
    by_cases hyE : y ∈ E
    · exact hstep1 y hyE
    · apply sub_eq_zero.mp
      apply v91 (d := 2 * t) (S := E)
        ((hcross_hom y).sub (hsf_sq_hom y hyK))
        (v00 (hK.1 y hyK))
      · intro e₁ e₂
        rw [map_sub, map_sub, hkill_hy y e₁ e₂, hkill_sf y hyK e₁ e₂]
      · omega
      · intro u hu v hv huv
        exact hK.2 y hyK u (hEK hu) v (hEK hv) (fun h => hyE (h ▸ hu)) huv (fun h => hyE (h ▸ hv))
      · intro c hcE
        rw [map_sub, sub_eq_zero, hcross_eval]
        have hcr_neg : cross3 y c = (-1 : ZMod p) • cross3 c y := by
          rw [v69, neg_one_smul]
        rw [hcr_neg, v05 hφ_hom]
        have hpow1 : (-1 : ZMod p) ^ (2 * t) = 1 := by rw [pow_mul]; simp
        rw [hpow1, one_mul, ← hcross_eval c y φ, hstep1 c hcE, map_pow, map_pow]
        exact v158 hK hp heK (hEK hcE) hyK
  have hφ_ne : φ ≠ 0 := by
    intro h0
    obtain ⟨c, hcE, hce⟩ := exists_mem_ne (by omega : 1 < E.card) e
    have h1 := congr_arg (eval c) (hstep2 e heK)
    rw [h0, map_zero, map_zero, map_pow] at h1
    exact pow_ne_zero 2 (v115 heK heK (hEK hcE) hce.symm) h1.symm
  refine ⟨φ, hφ_ne, hφ_hom, ?_⟩
  intro y hyK
  constructor
  ·
    intro l hl
    have hly : dot3 l y = 0 := (mem_filter.mp (mem_filter.mp hl).1).2
    have hln : v53 l := v30.mp (mem_filter.mp (mem_filter.mp hl).1).1
    have hyl_ne : y ≠ 0 := v00 (hK.1 y hyK)
    have hll_ne : l ≠ 0 := v00 hln
    have hu_ex : ∃ u : Fin 3 → ZMod p, dot3 l u = 0 ∧ cross3 y u ≠ 0 := by
      have hcard_l : (lThru l).card = p + 1 := v200 hll_ne
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      obtain ⟨u, hu, huy⟩ := exists_mem_ne (by omega : 1 < (lThru l).card) y
      refine ⟨u, ?_, ?_⟩
      · rw [v45]; exact (mem_filter.mp hu).2
      · intro hcr0
        rcases (v01 hyl_ne).mp hcr0 with ⟨c, hc⟩
        exact huy (v04 (v30.mp (mem_filter.mp hu).1) (hK.1 y hyK) hc)
    rcases hu_ex with ⟨u, hlu, hcr_ne⟩
    rcases v09 hcr_ne hly hlu with ⟨c, hc⟩
    rw [hc, v05 hφ_hom, ← hcross_eval y u φ, hstep2 y hyK]
    have hsf0 : eval u (v37 K e y) = 0 := by
      have hraw0 : eval u (rawF K y) = 0 := by
        rw [v172]; exact prod_eq_zero hl hlu
      unfold v37
      split_ifs with hye
      · subst hye; exact hraw0
      · simp [hraw0]
    simp [hsf0]
  ·
    intro L _ ι z hz hzy hφz
    have hy_ne : ι ∘ y ≠ 0 := by
      intro h0; apply v00 (hK.1 y hyK)
      ext i; exact ι.injective (by simpa using congr_fun h0 i)
    have hu_ex : ∃ u : Fin 3 → L, dot3 z u = 0 ∧ cross3 (ι ∘ y) u ≠ 0 := by
      have hex : ∃ i : Fin 3, z i ≠ 0 := by
        by_contra hall; push Not at hall; exact hz (funext hall)
      rcases hex with ⟨i, hi⟩
      have htwo : ∃ v₁ v₂ : Fin 3 → L, dot3 z v₁ = 0 ∧ dot3 z v₂ = 0 ∧ cross3 v₁ v₂ ≠ 0 := by
        rcases v03 i with rfl | rfl | rfl
        · exact ⟨![-z 1, z 0, 0], ![-z 2, 0, z 0], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 0; simp [cross3] at this; exact hi this⟩
        · exact ⟨![z 1, -z 0, 0], ![0, -z 2, z 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 1; simp [cross3] at this; exact hi this⟩
        · exact ⟨![z 2, 0, -z 0], ![0, z 2, -z 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 2; simp [cross3] at this; exact hi this⟩
      rcases htwo with ⟨v₁, v₂, hv1, hv2, hcr12⟩
      by_cases h1 : cross3 (ι ∘ y) v₁ ≠ 0
      · exact ⟨v₁, hv1, h1⟩
      · push Not at h1
        refine ⟨v₂, hv2, ?_⟩
        intro h2
        rcases (v01 hy_ne).mp h1 with ⟨c1, hc1⟩
        rcases (v01 hy_ne).mp h2 with ⟨c2, hc2⟩
        apply hcr12
        rw [hc1, hc2, v72, v42, v85, smul_zero, smul_zero]
    rcases hu_ex with ⟨u, hzu, hcr_ne⟩
    rcases v09 hcr_ne hzy hzu with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by intro h0; rw [h0, zero_smul] at hc; exact hz hc
    have hmap_hom : (Mv.map ι φ).IsHomogeneous (2 * t) := hφ_hom.map ι
    rw [hc, v05 hmap_hom] at hφz
    have hφ_cr : eval (cross3 (ι ∘ y) u) (Mv.map ι φ) = 0 :=
      (mul_eq_zero.mp hφz).resolve_left (pow_ne_zero _ hc_ne)
    have hmap_eq : Mv.map ι (aeval (crossPoly y) φ) = (Mv.map ι (v37 K e y)) ^ 2 := by
      rw [hstep2 y hyK, map_pow]
    have hev_lhs : eval u (Mv.map ι (aeval (crossPoly y) φ)) = eval (cross3 (ι ∘ y) u) (Mv.map ι φ) := by
      rw [eval_map, eval_map]
      have hcomp : ∀ P : Mv3 (ZMod p), eval₂ ι u (aeval (crossPoly y) P) = eval₂ ι (cross3 (ι ∘ y) u) P := by
        intro P
        induction P using Mv.induction_on with
        | C a => simp
        | add p₁ p₂ ih₁ ih₂ => simp only [map_add, eval₂_add, ih₁, ih₂]
        | mul_X p₁ i ih =>
          simp only [map_mul, aeval_X, eval₂_mul, eval₂_X, ih]; congr 1
          rcases v03 i with rfl | rfl | rfl <;>
            simp [crossPoly, cross3, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
      exact hcomp φ
    have hsf_zero : eval u (Mv.map ι (v37 K e y)) = 0 := by
      have hsq0 : (eval u (Mv.map ι (v37 K e y))) ^ 2 = 0 := by
        rw [← map_pow, ← hmap_eq, hev_lhs, hφ_cr]
      exact eq_zero_of_pow_eq_zero hsq0
    have hraw_zero : eval u (Mv.map ι (rawF K y)) = 0 := by
      unfold v37 at hsf_zero
      split_ifs at hsf_zero with hye
      · subst hye; exact hsf_zero
      · rw [map_mul, map_mul, map_C, eval_C] at hsf_zero
        have hsc_ne : (-1 : ZMod p) ^ (p + 2 - K.card + 1) * eval y (rawF K e) /
            eval e (rawF K y) ≠ 0 :=
          div_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (v24 hyK hye))
            (v24 heK (Ne.symm hye))
        exact (mul_eq_zero.mp hsf_zero).resolve_left
          (fun h => hsc_ne (ι.injective (h.trans (map_zero ι).symm)))
    have hprod0 : ∏ l ∈ v23 K y, dot3 (ι ∘ l) u = 0 := by
      rw [rawF, map_prod, map_prod] at hraw_zero
      simpa only [map_linForm, v27] using hraw_zero
    obtain ⟨l, hl, hlu⟩ := Fs.prod_eq_zero_iff.mp hprod0
    have hly_L : dot3 (ι ∘ l) (ι ∘ y) = 0 := by
      have h0 : dot3 l y = 0 := (mem_filter.mp (mem_filter.mp hl).1).2
      have : dot3 (ι ∘ l) (ι ∘ y) = ι (dot3 l y) := by simp [dot3]
      rw [this, h0, map_zero]
    rcases v09 hcr_ne hly_L hlu with ⟨c', hc'⟩
    have hc'_ne : c' ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hc'
      apply v00 (v30.mp (mem_filter.mp (mem_filter.mp hl).1).1)
      ext i; exact ι.injective ((congr_fun hc' i).trans (map_zero ι).symm)
    refine ⟨l, hl, c * c'⁻¹, ?_⟩
    ext i
    have h1 := congr_fun hc i
    have h2 := congr_fun hc' i
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    calc z i = c * cross3 (ι ∘ y) u i := h1
      _ = c * (c'⁻¹ * c') * cross3 (ι ∘ y) u i := by rw [inv_mul_cancel₀ hc'_ne, mul_one]
      _ = (c * c'⁻¹) * (c' * cross3 (ι ∘ y) u i) := by ring
      _ = (c * c'⁻¹) * (ι ∘ l) i := by rw [← h2]
end SegreTangentsAndEnvelope
end Part1Scope
section PolyNormEngine
variable {R : Type*} [CommRing R] [Nontrivial R]
noncomputable def mulMat (f g : Pol R) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  Mx.of fun i j => ((Pl.X ^ (j : ℕ) * g) %ₘ f).coeff (i : ℕ)
noncomputable def pNorm (f g : Pol R) : R :=
  (mulMat f g).det
omit [Nontrivial R] in
lemma v54 {d : ℕ} {p : Pol R} (hp : p.natDegree < d) (_hd : 0 < d) :
    p = ∑ k : Fin d, Pl.C (p.coeff (k : ℕ)) * Pl.X ^ (k : ℕ) := by
  ext n
  rw [Pl.finsetSum_coeff]
  by_cases hn : n < d
  · rw [sum_eq_single ⟨n, hn⟩]
    · simp
    · intro k _ hkn
      simp only [Pl.coeff_C_mul_X_pow]
      rw [if_neg (fun h => hkn (Fi.ext h.symm))]
    · intro h; exact absurd (mem_univ _) h
  · rw [Pl.coeff_eq_zero_of_natDegree_lt (by omega)]
    symm
    apply sum_eq_zero
    intro k _
    simp only [Pl.coeff_C_mul_X_pow]
    rw [if_neg (by omega)]
omit [Nontrivial R] in
lemma v49 {f : Pol R} (hf : f.Monic) (q : Pol R) :
    (f * q) %ₘ f = 0 :=
  (Pl.modByMonic_eq_zero_iff_dvd hf).mpr (dvd_mul_right f q)
omit [Nontrivial R] in
lemma v100 {f p q : Pol R} (hf : f.Monic) :
    (p %ₘ f * q) %ₘ f = (p * q) %ₘ f := by
  have hdiv : p = p %ₘ f + f * (p /ₘ f) := (Pl.modByMonic_add_div p f).symm
  conv_rhs => rw [hdiv, add_mul, mul_assoc]
  rw [Pl.add_modByMonic, v49 hf, add_zero]
omit [Nontrivial R] in
lemma v142 {f p q : Pol R} (hf : f.Monic) :
    (p * (q %ₘ f)) %ₘ f = (p * q) %ₘ f := by
  rw [mul_comm p (q %ₘ f), v100 hf, mul_comm]
lemma v170 {f p : Pol R} (hf : f.Monic)
    (hp : p.natDegree < f.natDegree) : p %ₘ f = p := by
  by_cases hp0 : p = 0
  · subst hp0; simp
  · exact Pl.modByMonic_eq_self_iff hf |>.mpr (Pl.degree_lt_degree hp)
lemma v70 {f p : Pol R} (hf : f.Monic) (c : R) :
    (Pl.C c * p) %ₘ f = Pl.C c * (p %ₘ f) := by
  have h1 := Pl.modByMonic_add_div p f
  have h2 : Pl.C c * p = Pl.C c * (p %ₘ f) + f * (Pl.C c * (p /ₘ f)) := by
    calc Pl.C c * p = Pl.C c * (p %ₘ f + f * (p /ₘ f)) := by rw [h1]
      _ = Pl.C c * (p %ₘ f) + f * (Pl.C c * (p /ₘ f)) := by ring
  rw [h2, Pl.add_modByMonic, v49 hf, add_zero]
  by_cases hd : f.natDegree = 0
  · have hf1 : f = 1 := Pl.eq_one_of_monic_natDegree_zero hf hd
    simp [hf1]
  · apply Pl.modByMonic_eq_self_iff hf |>.mpr
    calc (Pl.C c * (p %ₘ f)).degree
        ≤ (Pl.C c).degree + (p %ₘ f).degree := Pl.degree_mul_le _ _
      _ ≤ (p %ₘ f).degree := by
          by_cases hc : c = 0
          · simp [hc]
          · rw [Pl.degree_C hc, zero_add]
      _ < f.degree := Pl.degree_modByMonic_lt p hf
omit [Nontrivial R] in
lemma v108 {ι : Type*} (s : Finset ι) (f : Pol R) (g : ι → Pol R) :
    (∑ i ∈ s, g i) %ₘ f = ∑ i ∈ s, (g i %ₘ f) := by
  classical
  induction s using Fs.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Fs.sum_insert ha, Fs.sum_insert ha, Pl.add_modByMonic, ih]
lemma mulMat_mul {f g₁ g₂ : Pol R} (hf : f.Monic) :
    mulMat f (g₁ * g₂) = mulMat f g₁ * mulMat f g₂ := by
  ext i j
  simp only [mulMat, Mx.of_apply, Mx.mul_apply]
  have hd : 0 < f.natDegree := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  have hdeg : ((Pl.X ^ (j : ℕ) * g₂) %ₘ f).natDegree < f.natDegree := by
    by_cases h0 : (Pl.X ^ (j : ℕ) * g₂) %ₘ f = 0
    · rw [h0, Pl.natDegree_zero]; exact hd
    · exact Pl.natDegree_lt_natDegree h0 (Pl.degree_modByMonic_lt _ hf)
  have h1 : (Pl.X ^ (j : ℕ) * (g₁ * g₂)) %ₘ f = (((Pl.X ^ (j : ℕ) * g₂) %ₘ f) * g₁) %ₘ f := by
    rw [v100 hf]; congr 1; ring
  rw [h1]
  conv_lhs => rw [v54 hdeg hd]
  rw [sum_mul, v108, Pl.finsetSum_coeff]
  apply sum_congr rfl
  intro k _
  rw [mul_assoc, v70 hf, Pl.coeff_C_mul, mul_comm]
lemma pNorm_mul {f g₁ g₂ : Pol R} (hf : f.Monic) :
    pNorm f (g₁ * g₂) = pNorm f g₁ * pNorm f g₂ := by
  simp only [pNorm, mulMat_mul hf, Mx.det_mul]
omit [Nontrivial R] in
lemma pNorm_mod {f g : Pol R} (hf : f.Monic) :
    pNorm f (g %ₘ f) = pNorm f g := by
  unfold pNorm mulMat
  congr 1; ext i j
  simp only [Mx.of_apply, v142 hf]
omit [Nontrivial R] in
lemma pNorm_congr {f g₁ g₂ : Pol R} (hf : f.Monic) (h : f ∣ g₁ - g₂) :
    pNorm f g₁ = pNorm f g₂ := by
  rcases h with ⟨q, hq⟩
  have hg1 : g₁ = g₂ + f * q := by linear_combination hq
  rw [← pNorm_mod hf (g := g₁), hg1, Pl.add_modByMonic, v49 hf, add_zero, pNorm_mod hf]
lemma pNorm_C {f : Pol R} (hf : f.Monic) (c : R) :
    pNorm f (Pl.C c) = c ^ f.natDegree := by
  have hmat : mulMat f (Pl.C c) = Mx.diagonal (fun _ => c) := by
    ext i j
    simp only [mulMat, Mx.of_apply, Mx.diagonal_apply]
    rw [mul_comm, v70 hf, v170 hf (by rw [Pl.natDegree_X_pow]; exact j.2), Pl.coeff_C_mul_X_pow]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (fun h => hij (Fi.ext h)), if_neg hij]
  rw [pNorm, hmat, Mx.det_diagonal]
  simp
lemma pNorm_one {f : Pol R} (hf : f.Monic) : pNorm f 1 = 1 := by
  simpa using pNorm_C hf 1
lemma v132 (r : R) (g : Pol R) :
    pNorm (Pl.X - Pl.C r) g = g.eval r := by
  have hdeg : (Pl.X - Pl.C r).natDegree = 1 := Pl.natDegree_X_sub_C r
  have : Subsingleton (Fin (Pl.X - Pl.C r).natDegree) := by
    rw [hdeg]; infer_instance
  unfold pNorm mulMat
  rw [Mx.det_eq_elem_of_subsingleton (k := ⟨0, by omega⟩)]
  simp only [Mx.of_apply, pow_zero, one_mul, Pl.modByMonic_X_sub_C_eq_C_eval, Pl.coeff_C_zero]
omit [Nontrivial R] in
lemma v155 {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    {f g : Pol R} (hf : f.Monic) :
    φ (pNorm f g) = pNorm (f.map φ) (g.map φ) := by
  have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  unfold pNorm
  rw [Rh.map_det]
  have hmat : φ.mapMatrix (mulMat f g) = Mx.reindex (finCongr hdeg) (finCongr hdeg) (mulMat (f.map φ) (g.map φ)) := by
    ext i j
    simp only [Rh.mapMatrix_apply, Mx.map_apply, mulMat, Mx.of_apply, Mx.reindex_apply, Mx.submatrix_apply, finCongr_symm, finCongr_apply, Fi.val_cast]
    rw [← Pl.coeff_map, Pl.map_modByMonic φ hf, Pl.map_mul, Pl.map_pow, Pl.map_X]
  rw [hmat, Mx.det_reindex_self]
lemma v97 {f₁ f₂ g : Pol R} (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) :
    pNorm (f₁ * f₂) g = pNorm f₁ g * pNorm f₂ g := by
  set d₁ := f₁.natDegree
  set d₂ := f₂.natDegree
  have hf : (f₁ * f₂).Monic := hf₁.mul hf₂
  have hdeg : (f₁ * f₂).natDegree = d₁ + d₂ := hf₁.natDegree_mul hf₂
  let e : Fin d₁ ⊕ Fin d₂ ≃ Fin (f₁ * f₂).natDegree :=
    finSumFinEquiv.trans (finCongr hdeg.symm)
  let M : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) R :=
    (mulMat (f₁ * f₂) g).submatrix e e
  have hdetM : M.det = pNorm (f₁ * f₂) g := by
    rw [pNorm, ← Mx.det_reindex_self e.symm (mulMat (f₁ * f₂) g)]
    rfl
  let P : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) R :=
    Mx.of fun r c => match c with
      | Sum.inl j => if (e r : ℕ) = (j : ℕ) then 1 else 0
      | Sum.inr k => (Pl.X ^ (k : ℕ) * f₁).coeff (e r : ℕ)
  have hP_det : P.det = 1 := by
    let P' : Matrix (Fin (f₁ * f₂).natDegree) (Fin (f₁ * f₂).natDegree) R :=
      P.submatrix e.symm e.symm
    have hP'_tri : P'.BlockTriangular id := by
      intro r c hrc
      simp only [id_eq] at hrc
      simp only [P', P, Mx.submatrix_apply, Mx.of_apply, Eqv.apply_symm_apply]
      cases hc : e.symm c with
      | inl j =>
        dsimp only
        have hcj : (c : ℕ) = (j : ℕ) := by
          have := congr_arg e hc
          simp [e] at this
          simpa using congr_arg Fi.val this
        rw [if_neg (by omega)]
      | inr k =>
        dsimp only
        have hck : (c : ℕ) = d₁ + (k : ℕ) := by
          have := congr_arg e hc
          simp [e] at this
          simpa using congr_arg Fi.val this
        apply Pl.coeff_eq_zero_of_natDegree_lt
        have hdk : (Pl.X ^ (k : ℕ) * f₁).natDegree ≤ k + d₁ :=
          (Pl.natDegree_mul_le).trans (by rw [Pl.natDegree_X_pow])
        omega
    have hP'_diag : ∀ r : Fin (f₁ * f₂).natDegree, P' r r = 1 := by
      intro r
      simp only [P', P, Mx.submatrix_apply, Mx.of_apply, Eqv.apply_symm_apply]
      cases hr : e.symm r with
      | inl j =>
        dsimp only
        have hrj : (r : ℕ) = (j : ℕ) := by
          have := congr_arg e hr; simp [e] at this; simpa using congr_arg Fi.val this
        rw [if_pos hrj]
      | inr k =>
        dsimp only
        have hrk : (r : ℕ) = d₁ + (k : ℕ) := by
          have := congr_arg e hr; simp [e] at this; simpa using congr_arg Fi.val this
        rw [hrk, add_comm d₁ (k : ℕ), Pl.coeff_X_pow_mul', if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact hf₁.coeff_natDegree
    have hdet' : P'.det = 1 := by
      rw [Mx.det_of_isUpperTriangular hP'_tri]
      simp [hP'_diag]
    rw [← hdet']
    exact (Mx.det_reindex_self e P).symm
  let Q : Matrix (Fin d₂) (Fin d₁) R :=
    Mx.of fun k j => ((((Pl.X ^ (j : ℕ) * g) %ₘ (f₁ * f₂)) /ₘ f₁)).coeff (k : ℕ)
  let B : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) R :=
    Mx.fromBlocks (mulMat f₁ g) 0 Q (mulMat f₂ g)
  have hMP : M * P = P * B := by
    have hM_vec : ∀ (p : Pol R), (∀ m ≥ (f₁ * f₂).natDegree, p.coeff m = 0) → ∀ r : Fin d₁ ⊕ Fin d₂, (∑ c : Fin d₁ ⊕ Fin d₂, M r c * p.coeff (e c : ℕ)) = ((p * g) %ₘ (f₁ * f₂)).coeff (e r : ℕ) := by
      intro p hp r
      by_cases hd0 : (f₁ * f₂).natDegree = 0
      · exact Fi.elim0 (hd0 ▸ e r)
      · have hplt : p.natDegree < (f₁ * f₂).natDegree := by
          by_cases hp0 : p = 0
          · rw [hp0, Pl.natDegree_zero]; omega
          · by_contra hge; push Not at hge
            exact Pl.leadingCoeff_ne_zero.mpr hp0 (hp _ hge)
        rw [← Eqv.sum_comp e.symm]
        have hsum_eq : ∑ x : Fin (f₁ * f₂).natDegree, M r (e.symm x) * p.coeff (e (e.symm x) : ℕ) = ∑ x : Fin (f₁ * f₂).natDegree, ((Pl.X ^ (x : ℕ) * g) %ₘ (f₁ * f₂)).coeff (e r : ℕ) * p.coeff (x : ℕ) := by
          apply sum_congr rfl; intro x _
          simp [M, mulMat]
        rw [hsum_eq]
        conv_rhs => rw [v54 hplt (by omega)]
        rw [sum_mul, v108, Pl.finsetSum_coeff]
        apply sum_congr rfl; intro x _
        rw [mul_assoc, v70 hf, Pl.coeff_C_mul, mul_comm]
    have hP_vec : ∀ (u : Fin d₁ → R) (v : Fin d₂ → R) (r : Fin d₁ ⊕ Fin d₂), (∑ c : Fin d₁ ⊕ Fin d₂, P r c * Sum.elim u v c) = ((∑ j : Fin d₁, Pl.C (u j) * Pl.X ^ (j : ℕ)) + (∑ k : Fin d₂, Pl.C (v k) * Pl.X ^ (k : ℕ)) * f₁).coeff (e r : ℕ) := by
      intro u v r
      rw [Fintype.sum_sum_type, Pl.coeff_add, Pl.finsetSum_coeff, sum_mul, Pl.finsetSum_coeff]
      congr 1
      · apply sum_congr rfl; intro j _
        simp only [P, Mx.of_apply, Sum.elim_inl, Pl.coeff_C_mul_X_pow]
        split_ifs <;> simp
      · apply sum_congr rfl; intro k _
        simp only [P, Mx.of_apply, Sum.elim_inr]
        have heq : Pl.C (v k) * Pl.X ^ (k : ℕ) * f₁ = Pl.C (v k) * (Pl.X ^ (k : ℕ) * f₁) := by ring
        rw [heq, Pl.coeff_C_mul, mul_comm]
    ext r c
    rw [Mx.mul_apply, Mx.mul_apply]
    cases c with
    | inl j =>
      have hlhs : ∑ x : Fin d₁ ⊕ Fin d₂, M r x * P x (Sum.inl j) = ((Pl.X ^ (j : ℕ) * g) %ₘ (f₁ * f₂)).coeff (e r : ℕ) := by
        have hcol : ∀ x : Fin d₁ ⊕ Fin d₂, P x (Sum.inl j) = (Pl.X ^ (j : ℕ) : Pol R).coeff (e x : ℕ) := by
          intro x; simp [P, Pl.coeff_X_pow, eq_comm]
        simp_rw [hcol]
        exact hM_vec (Pl.X ^ (j : ℕ)) (fun m hm => by
          rw [Pl.coeff_X_pow, if_neg (by omega)]) r
      have hrhs : ∑ x : Fin d₁ ⊕ Fin d₂, P r x * B x (Sum.inl j) = (((Pl.X ^ (j : ℕ) * g) %ₘ f₁) + (((Pl.X ^ (j : ℕ) * g) %ₘ (f₁ * f₂)) /ₘ f₁) * f₁).coeff (e r : ℕ) := by
        have hcol : ∀ x, B x (Sum.inl j) = Sum.elim (fun i => mulMat f₁ g i j) (fun k => Q k j) x := by
          intro x; cases x <;> simp [B]
        simp_rw [hcol]
        rw [hP_vec]
        congr 1; congr 1
        · by_cases hd1 : d₁ = 0
          · exact Fi.elim0 (hd1 ▸ j)
          · have hlt1 : ((Pl.X ^ (j : ℕ) * g) %ₘ f₁).natDegree < d₁ := by
              by_cases h0 : (Pl.X ^ (j : ℕ) * g) %ₘ f₁ = 0
              · rw [h0, Pl.natDegree_zero]; omega
              · exact Pl.natDegree_lt_natDegree h0 (Pl.degree_modByMonic_lt _ hf₁)
            exact (v54 hlt1 (by omega)).symm
        · congr 1
          set w := (Pl.X ^ (j : ℕ) * g) %ₘ (f₁ * f₂)
          by_cases hd2 : d₂ = 0
          · have hf21 : f₂ = 1 := Pl.eq_one_of_monic_natDegree_zero hf₂ hd2
            have hw : w /ₘ f₁ = 0 := by
              have hlt : w.degree < f₁.degree := by
                have := Pl.degree_modByMonic_lt (Pl.X ^ (j : ℕ) * g) hf
                simpa [w, hf21] using this
              exact Pl.divByMonic_eq_zero_iff hf₁ |>.mpr hlt
            rw [hw]
            apply sum_eq_zero; intro k _; exact Fi.elim0 (hd2 ▸ k)
          · have hlt2 : (w /ₘ f₁).natDegree < d₂ := by
              by_cases h0 : w /ₘ f₁ = 0
              · rw [h0, Pl.natDegree_zero]; omega
              · have hdegw : w.degree < (f₁ * f₂).degree :=
                  Pl.degree_modByMonic_lt _ hf
                have hdiv_eq := Pl.modByMonic_add_div w f₁
                have hdeg_mul : (f₁ * (w /ₘ f₁)).degree < (f₁ * f₂).degree := by
                  have hlt1 : (w %ₘ f₁).degree < f₁.degree := Pl.degree_modByMonic_lt w hf₁
                  have hle1 : f₁.degree ≤ (f₁ * (w /ₘ f₁)).degree := by
                    rw [mul_comm f₁, hf₁.degree_mul, add_comm]
                    have hpos : (0 : WithBot ℕ) ≤ (w /ₘ f₁).degree := Pl.zero_le_degree_iff.mpr h0
                    calc f₁.degree = f₁.degree + 0 := (add_zero _).symm
                      _ ≤ f₁.degree + (w /ₘ f₁).degree := add_le_add le_rfl hpos
                  have hne : (w %ₘ f₁).degree < (f₁ * (w /ₘ f₁)).degree := hlt1.trans_le hle1
                  have heq : w.degree = (f₁ * (w /ₘ f₁)).degree := by
                    conv_lhs => rw [← hdiv_eq]
                    exact Pl.degree_add_eq_right_of_degree_lt hne
                  exact heq ▸ hdegw
                rw [mul_comm f₁ (w /ₘ f₁), hf₁.degree_mul, mul_comm f₁ f₂, hf₁.degree_mul] at hdeg_mul
                rw [Pl.degree_eq_natDegree h0, Pl.degree_eq_natDegree hf₁.ne_zero, Pl.degree_eq_natDegree hf₂.ne_zero] at hdeg_mul
                norm_cast at hdeg_mul; omega
            exact (v54 hlt2 (by omega)).symm
      rw [hlhs, hrhs]
      congr 1
      set w := (Pl.X ^ (j : ℕ) * g) %ₘ (f₁ * f₂)
      have hmod1 : w %ₘ f₁ = (Pl.X ^ (j : ℕ) * g) %ₘ f₁ := by
        have hdiv := Pl.modByMonic_add_div (Pl.X ^ (j : ℕ) * g) (f₁ * f₂)
        conv_rhs => rw [← hdiv, mul_assoc, Pl.add_modByMonic, v49 hf₁, add_zero]
      rw [← hmod1, mul_comm (w /ₘ f₁) f₁, Pl.modByMonic_add_div w f₁]
    | inr k =>
      have hlhs : ∑ x : Fin d₁ ⊕ Fin d₂, M r x * P x (Sum.inr k) = (((Pl.X ^ (k : ℕ) * f₁) * g) %ₘ (f₁ * f₂)).coeff (e r : ℕ) := by
        have hcol : ∀ x : Fin d₁ ⊕ Fin d₂, P x (Sum.inr k) = (Pl.X ^ (k : ℕ) * f₁).coeff (e x : ℕ) :=
          fun _ => rfl
        simp_rw [hcol]
        exact hM_vec (Pl.X ^ (k : ℕ) * f₁) (fun m hm => by
          apply Pl.coeff_eq_zero_of_natDegree_lt
          have : (Pl.X ^ (k : ℕ) * f₁).natDegree ≤ (k : ℕ) + d₁ :=
            Pl.natDegree_mul_le.trans (by rw [Pl.natDegree_X_pow])
          omega) r
      have hrhs : ∑ x : Fin d₁ ⊕ Fin d₂, P r x * B x (Sum.inr k) = (((Pl.X ^ (k : ℕ) * g) %ₘ f₂) * f₁).coeff (e r : ℕ) := by
        have hcol : ∀ x, B x (Sum.inr k) = Sum.elim (fun _ => 0) (fun l => mulMat f₂ g l k) x := by
          intro x; cases x <;> simp [B]
        simp_rw [hcol]
        rw [hP_vec]
        simp only [map_zero, zero_mul, Fs.sum_const_zero, zero_add]
        congr 1; congr 1
        by_cases hd2 : d₂ = 0
        · exact Fi.elim0 (hd2 ▸ k)
        · have hlt2 : ((Pl.X ^ (k : ℕ) * g) %ₘ f₂).natDegree < d₂ := by
            by_cases h0 : (Pl.X ^ (k : ℕ) * g) %ₘ f₂ = 0
            · rw [h0, Pl.natDegree_zero]; omega
            · exact Pl.natDegree_lt_natDegree h0 (Pl.degree_modByMonic_lt _ hf₂)
          exact (v54 hlt2 (by omega)).symm
      rw [hlhs, hrhs]
      congr 1
      have hdiv2 := Pl.modByMonic_add_div (Pl.X ^ (k : ℕ) * g) f₂
      have heq : (Pl.X ^ (k : ℕ) * f₁) * g = ((Pl.X ^ (k : ℕ) * g) %ₘ f₂) * f₁ + (f₁ * f₂) * ((Pl.X ^ (k : ℕ) * g) /ₘ f₂) := by
        calc (Pl.X ^ (k : ℕ) * f₁) * g
            = (Pl.X ^ (k : ℕ) * g) * f₁ := by ring
          _ = (((Pl.X ^ (k : ℕ) * g) %ₘ f₂) + f₂ * ((Pl.X ^ (k : ℕ) * g) /ₘ f₂)) * f₁ := by
              rw [hdiv2]
          _ = ((Pl.X ^ (k : ℕ) * g) %ₘ f₂) * f₁ + (f₁ * f₂) * ((Pl.X ^ (k : ℕ) * g) /ₘ f₂) := by ring
      rw [heq, Pl.add_modByMonic, v49 hf, add_zero]
      apply Pl.modByMonic_eq_self_iff hf |>.mpr
      rw [hf₁.degree_mul, mul_comm f₁ f₂, hf₁.degree_mul]
      have hlt := Pl.degree_modByMonic_lt (Pl.X ^ (k : ℕ) * g) hf₂
      cases hr2 : ((Pl.X ^ (k : ℕ) * g) %ₘ f₂).degree with
      | bot =>
        rw [WithBot.bot_add]; exact WithBot.bot_lt_coe _ |>.trans_eq (by
          rw [Pl.degree_eq_natDegree hf₂.ne_zero, Pl.degree_eq_natDegree hf₁.ne_zero]; rfl)
      | coe n =>
        rw [hr2] at hlt
        rw [Pl.degree_eq_natDegree hf₂.ne_zero] at hlt ⊢
        rw [Pl.degree_eq_natDegree hf₁.ne_zero]
        have hlt' : n < f₂.natDegree := WithBot.coe_lt_coe.mp hlt
        exact WithBot.coe_lt_coe.mpr (Nat.add_lt_add_right hlt' f₁.natDegree)
  have hdet_eq : M.det * P.det = P.det * B.det := by
    rw [← Mx.det_mul, ← Mx.det_mul, hMP]
  rw [hP_det, mul_one, one_mul, hdetM] at hdet_eq
  rw [hdet_eq]
  exact Mx.det_fromBlocks_zero₁₂ (mulMat f₁ g) Q (mulMat f₂ g)
noncomputable def v21 (d e : ℕ) (f g : Pol R) :
    Matrix (Fin (e + d)) (Fin e ⊕ Fin d) R :=
  Mx.of fun r c => match c with
    | Sum.inl i => (Pl.X ^ (i : ℕ) * f).coeff (r : ℕ)
    | Sum.inr j => (Pl.X ^ (j : ℕ) * g).coeff (r : ℕ)
lemma v99 {f g : Pol R} (hf : f.Monic) (e : ℕ)
    (hg : ∀ k > e, g.coeff k = 0) :
    ∃ s : R, s * s = 1 ∧ pNorm f g = s * ((v21 f.natDegree e f g).submatrix id finSumFinEquiv.symm).det := by
  set d := f.natDegree
  let er : Fin d ⊕ Fin e ≃ Fin (e + d) :=
    finSumFinEquiv.trans (finCongr (add_comm d e))
  let ec : Fin d ⊕ Fin e ≃ Fin e ⊕ Fin d := Eqv.sumComm (Fin d) (Fin e)
  let U : Matrix (Fin (e + d)) (Fin d ⊕ Fin e) R :=
    Mx.of fun r c => match c with
      | Sum.inl j => if (r : ℕ) = (j : ℕ) then 1 else 0
      | Sum.inr i => (Pl.X ^ (i : ℕ) * f).coeff (r : ℕ)
  have hU_det : (U.submatrix id er.symm).det = 1 := by
    have htri : (U.submatrix id er.symm).BlockTriangular id := by
      intro r c hrc
      simp only [id_eq] at hrc
      simp only [U, Mx.submatrix_apply, Mx.of_apply, id_eq]
      cases hc : er.symm c with
      | inl j =>
        dsimp only
        have hcj : (c : ℕ) = (j : ℕ) := by
          have := congr_arg er hc; simp [er] at this; simpa using congr_arg Fi.val this
        rw [if_neg (by omega)]
      | inr i =>
        dsimp only
        have hci : (c : ℕ) = d + (i : ℕ) := by
          have := congr_arg er hc; simp [er] at this
          have hval := congr_arg Fi.val this; simp at hval; omega
        apply Pl.coeff_eq_zero_of_natDegree_lt
        have : (Pl.X ^ (i : ℕ) * f).natDegree ≤ (i : ℕ) + d :=
          Pl.natDegree_mul_le.trans (by rw [Pl.natDegree_X_pow])
        omega
    have hdiag : ∀ r : Fin (e + d), (U.submatrix id er.symm) r r = 1 := by
      intro r
      simp only [U, Mx.submatrix_apply, Mx.of_apply, id_eq]
      cases hr : er.symm r with
      | inl j =>
        dsimp only
        have hrj : (r : ℕ) = (j : ℕ) := by
          have := congr_arg er hr; simp [er] at this; simpa using congr_arg Fi.val this
        rw [if_pos hrj]
      | inr i =>
        dsimp only
        have hri : (r : ℕ) = d + (i : ℕ) := by
          have := congr_arg er hr; simp [er] at this
          have hval := congr_arg Fi.val this; simp at hval; omega
        rw [hri, add_comm d (i : ℕ), Pl.coeff_X_pow_mul', if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact hf.coeff_natDegree
    rw [Mx.det_of_isUpperTriangular htri]
    exact Fs.prod_eq_one (fun r _ => hdiag r)
  let Q : Matrix (Fin e) (Fin d) R :=
    Mx.of fun i j => ((Pl.X ^ (j : ℕ) * g) /ₘ f).coeff (i : ℕ)
  let B : Matrix (Fin d ⊕ Fin e) (Fin d ⊕ Fin e) R :=
    Mx.fromBlocks (mulMat f g) 0 Q 1
  have hprod : (U.submatrix id er.symm) * (B.submatrix er.symm er.symm) = (v21 d e f g).submatrix id (ec ∘ er.symm) := by
    ext r c
    rw [Mx.mul_apply]
    simp only [Mx.submatrix_apply, id_eq, Fn.comp_apply]
    rw [← Eqv.sum_comp er]
    simp only [Eqv.symm_apply_apply]
    cases hc : er.symm c with
    | inr i =>
      rw [Fintype.sum_sum_type]
      have h1 : ∑ j : Fin d, U r (Sum.inl j) * B (Sum.inl j) (Sum.inr i) = 0 := by
        apply sum_eq_zero; intro j _; simp [B]
      have h2 : ∑ l : Fin e, U r (Sum.inr l) * B (Sum.inr l) (Sum.inr i) = U r (Sum.inr i) := by
        rw [sum_eq_single i]
        · simp [B]
        · intro l _ hli; simp [B, Mx.one_apply_ne hli]
        · intro h; exact absurd (mem_univ _) h
      rw [h1, zero_add, h2]
      simp [U, v21, ec]
    | inl j =>
      rw [Fintype.sum_sum_type]
      simp only [U, B, Q, mulMat, v21, ec, Eqv.sumComm_apply, Sum.swap_inl, Mx.fromBlocks_apply₁₁, Mx.fromBlocks_apply₂₁, Mx.of_apply]
      have hsum1 : ∑ l : Fin d, (if (r : ℕ) = (l : ℕ) then (1 : R) else 0) * ((Pl.X ^ (j : ℕ) * g) %ₘ f).coeff (l : ℕ) = ((Pl.X ^ (j : ℕ) * g) %ₘ f).coeff (r : ℕ) := by
        by_cases hr : (r : ℕ) < d
        · rw [sum_eq_single ⟨r, hr⟩]
          · simp
          · intro l _ hlr; rw [if_neg (fun h => hlr (Fi.ext h.symm)), zero_mul]
          · intro h; exact absurd (mem_univ _) h
        · have h0 : ((Pl.X ^ (j : ℕ) * g) %ₘ f).coeff (r : ℕ) = 0 := by
            by_cases hm0 : (Pl.X ^ (j : ℕ) * g) %ₘ f = 0
            · simp [hm0]
            · apply Pl.coeff_eq_zero_of_natDegree_lt
              have hlt := Pl.natDegree_lt_natDegree hm0 (Pl.degree_modByMonic_lt _ hf)
              omega
          rw [h0]
          apply sum_eq_zero; intro l _
          rw [if_neg (by omega), zero_mul]
      have hsum2 : ∑ l : Fin e, (Pl.X ^ (l : ℕ) * f).coeff (r : ℕ) * ((Pl.X ^ (j : ℕ) * g) /ₘ f).coeff (l : ℕ) = (f * ((Pl.X ^ (j : ℕ) * g) /ₘ f)).coeff (r : ℕ) := by
        set q := (Pl.X ^ (j : ℕ) * g) /ₘ f
        have hq_zero : ∀ k ≥ e, q.coeff k = 0 := by
          intro k hk
          by_cases hq0 : q = 0
          · simp [hq0]
          · apply Pl.coeff_eq_zero_of_natDegree_lt
            have hdiv := Pl.modByMonic_add_div (Pl.X ^ (j : ℕ) * g) f
            have hjlt := j.isLt
            have hdeg_lhs : (Pl.X ^ (j : ℕ) * g).natDegree < d + e := by
              by_cases h0 : Pl.X ^ (j : ℕ) * g = 0
              · rw [h0, Pl.natDegree_zero]; omega
              · have hg_le : g.natDegree ≤ e :=
                  Pl.natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => hg m hm)
                have h1 : (Pl.X ^ (j : ℕ) * g).natDegree ≤ (j : ℕ) + g.natDegree :=
                  Pl.natDegree_mul_le.trans (by simp)
                omega
            have hdeg_fq : (f * q).natDegree = d + q.natDegree := by
              rw [hf.natDegree_mul' hq0]
            have hdeg_rem : ((Pl.X ^ (j : ℕ) * g) %ₘ f).natDegree < d := by
              by_cases h0 : (Pl.X ^ (j : ℕ) * g) %ₘ f = 0
              · rw [h0, Pl.natDegree_zero]; omega
              · exact Pl.natDegree_lt_natDegree h0 (Pl.degree_modByMonic_lt _ hf)
            have hlt_deg : ((Pl.X ^ (j : ℕ) * g) %ₘ f).natDegree < (f * q).natDegree := by
              omega
            have hadd_deg : (((Pl.X ^ (j : ℕ) * g) %ₘ f) + f * q).natDegree = (f * q).natDegree :=
              Pl.natDegree_add_eq_right_of_natDegree_lt hlt_deg
            rw [hdiv] at hadd_deg
            omega
        by_cases he0 : e = 0
        · have hq0 : q = 0 := by ext m; exact hq_zero m (by omega)
          simp [hq0]
        · have hqlt : q.natDegree < e := by
            by_cases hq0 : q = 0
            · rw [hq0, Pl.natDegree_zero]; omega
            · by_contra hge; push Not at hge
              exact Pl.leadingCoeff_ne_zero.mpr hq0 (hq_zero _ hge)
          conv_rhs => rw [v54 hqlt (by omega)]
          rw [mul_sum, Pl.finsetSum_coeff]
          apply sum_congr rfl; intro l _
          have heq : f * (Pl.C (q.coeff (l : ℕ)) * Pl.X ^ (l : ℕ)) = Pl.C (q.coeff (l : ℕ)) * (Pl.X ^ (l : ℕ) * f) := by ring
          rw [heq, Pl.coeff_C_mul, mul_comm]
      rw [hsum1, hsum2, ← Pl.coeff_add, Pl.modByMonic_add_div _ f]
  have hdetB : (B.submatrix er.symm er.symm).det = pNorm f g := by
    have hre : Mx.reindex er er B = B.submatrix er.symm er.symm := rfl
    rw [← hre, Mx.det_reindex_self er B]
    simp [B, pNorm]
  have hdet_eq : pNorm f g = ((v21 d e f g).submatrix id (ec ∘ er.symm)).det := by
    have h := congr_arg Mx.det hprod
    rw [Mx.det_mul, hU_det, one_mul, hdetB] at h
    exact h
  let σ : Eqv.Perm (Fin (e + d)) := finSumFinEquiv.symm.trans (ec.symm.trans er)
  have hcol_eq : (ec ∘ er.symm) ∘ σ = finSumFinEquiv.symm := by
    funext x; simp [σ]
  have hsub_eq : (v21 d e f g).submatrix id finSumFinEquiv.symm = ((v21 d e f g).submatrix id (ec ∘ er.symm)).submatrix id σ := by
    ext r c; simp [σ]
  have hdet_perm : ((v21 d e f g).submatrix id finSumFinEquiv.symm).det = (Equiv.Perm.sign σ : R) * ((v21 d e f g).submatrix id (ec ∘ er.symm)).det := by
    rw [hsub_eq, Mx.det_permute']
  refine ⟨(Equiv.Perm.sign σ : R), ?_, ?_⟩
  · have := Int.units_mul_self (Equiv.Perm.sign σ)
    exact_mod_cast congr_arg (Int.cast (R := R)) (show ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) = 1 by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])
  · rw [hdet_perm, ← mul_assoc]
    have h1 : (Equiv.Perm.sign σ : R) * (Equiv.Perm.sign σ : R) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [h1, one_mul, hdet_eq]
end PolyNormEngine
section BezoutBounds
variable {K : Type*} [Field K]
lemma v74 {f g : Pol (Pol K)} (hf : f.Monic) (e : ℕ)
    (hfd : ∀ k, f.coeff k ≠ 0 → (f.coeff k).natDegree + k ≤ f.natDegree)
    (hge : ∀ k, g.coeff k ≠ 0 → (g.coeff k).natDegree + k ≤ e) :
    (pNorm f g).natDegree ≤ f.natDegree * e := by
  set d := f.natDegree
  have hg_zero : ∀ k > e, g.coeff k = 0 := by
    intro k hk
    by_contra hne
    have := hge k hne
    omega
  obtain ⟨s, hs, hnorm⟩ := v99 hf e hg_zero
  rw [hnorm]
  have hs_deg : s.natDegree = 0 := by
    have hne : s ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact zero_ne_one hs
    have h2 : (s * s).natDegree = 0 := by rw [hs, Pl.natDegree_one]
    rw [Pl.natDegree_mul hne hne] at h2
    omega
  refine (Pl.natDegree_mul_le).trans ?_
  rw [hs_deg, zero_add]
  rw [Mx.det_apply]
  apply Pl.natDegree_sum_le_of_forall_le
  intro σ _
  have hsmul : ((Equiv.Perm.sign σ : ℤ) • ∏ i : Fin (e + d), ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i).natDegree ≤ (∏ i : Fin (e + d), ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine hsmul.trans ?_
  by_cases hprod0 : (∏ i : Fin (e + d), ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i) = 0
  · rw [hprod0, Pl.natDegree_zero]; exact Nat.zero_le _
  · have hfac_ne : ∀ i : Fin (e + d), ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i ≠ 0 :=
      fun i => prod_ne_zero_iff.mp hprod0 i (mem_univ i)
    have hdeg_le : ∀ i : Fin (e + d), (((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i).natDegree + (σ i : ℕ) ≤ match finSumFinEquiv.symm i with
          | Sum.inl c => d + (c : ℕ)
          | Sum.inr c => e + (c : ℕ) := by
      intro i
      have hne := hfac_ne i
      simp only [Mx.submatrix_apply, id_eq, v21, Mx.of_apply] at hne ⊢
      cases hc : finSumFinEquiv.symm i with
      | inl c =>
        rw [hc] at hne
        dsimp only at hne ⊢
        simp only [Pl.coeff_X_pow_mul'] at hne ⊢
        split_ifs at hne ⊢ with hle
        · have h1 := hfd ((σ i : ℕ) - (c : ℕ)) hne
          have h2 : ((σ i : ℕ) - (c : ℕ)) + (c : ℕ) = (σ i : ℕ) := Nat.sub_add_cancel hle
          calc (f.coeff ((σ i : ℕ) - (c : ℕ))).natDegree + (σ i : ℕ)
              = ((f.coeff ((σ i : ℕ) - (c : ℕ))).natDegree + ((σ i : ℕ) - (c : ℕ))) + (c : ℕ) := by
                  rw [add_assoc, h2]
            _ ≤ d + (c : ℕ) := Nat.add_le_add_right h1 _
        · exact absurd rfl hne
      | inr c =>
        rw [hc] at hne
        dsimp only at hne ⊢
        simp only [Pl.coeff_X_pow_mul'] at hne ⊢
        split_ifs at hne ⊢ with hle
        · have h1 := hge ((σ i : ℕ) - (c : ℕ)) hne
          have h2 : ((σ i : ℕ) - (c : ℕ)) + (c : ℕ) = (σ i : ℕ) := Nat.sub_add_cancel hle
          calc (g.coeff ((σ i : ℕ) - (c : ℕ))).natDegree + (σ i : ℕ)
              = ((g.coeff ((σ i : ℕ) - (c : ℕ))).natDegree + ((σ i : ℕ) - (c : ℕ))) + (c : ℕ) := by
                  rw [add_assoc, h2]
            _ ≤ e + (c : ℕ) := Nat.add_le_add_right h1 _
        · exact absurd rfl hne
    have hsum_le : (∑ i : Fin (e + d), (((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i).natDegree) + (∑ i : Fin (e + d), (σ i : ℕ)) ≤ ∑ i : Fin (e + d), match finSumFinEquiv.symm i with
          | Sum.inl c => d + (c : ℕ)
          | Sum.inr c => e + (c : ℕ) := by
      rw [← sum_add_distrib]
      exact sum_le_sum (fun i _ => hdeg_le i)
    have hsum_perm : ∑ i : Fin (e + d), (σ i : ℕ) = ∑ i : Fin (e + d), (i : ℕ) :=
      Eqv.sum_comp σ (fun x : Fin (e + d) => (x : ℕ))
    have hsum_rhs : (∑ i : Fin (e + d), match finSumFinEquiv.symm i with
          | Sum.inl c => d + (c : ℕ)
          | Sum.inr c => e + (c : ℕ)) = d * e + ∑ i : Fin (e + d), (i : ℕ) := by
      rw [← Eqv.sum_comp finSumFinEquiv]
      simp only [Eqv.symm_apply_apply]
      rw [Fintype.sum_sum_type]
      dsimp only
      have hfin : ∑ i : Fin (e + d), (i : ℕ) = (∑ c : Fin e, (c : ℕ)) + ∑ c : Fin d, (e + (c : ℕ)) := by
        rw [← Eqv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
        simp [finSumFinEquiv]
      rw [hfin, sum_add_distrib, Fs.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm e d]
      omega
    have hprod_deg := Pl.natDegree_prod_le (Fs.univ : Finset (Fin (e + d)))
      (fun i => ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i)
    omega
lemma v169 {f g : Pol (Pol K)} (hf : f.Monic) (a b e : ℕ)
    (ha : a ≤ f.natDegree) (hb : b ≤ e) (hg : ∀ k > e, g.coeff k = 0)
    (hf_van : ∀ k, Pl.X ^ (a - k) ∣ f.coeff k)
    (hg_van : ∀ k, Pl.X ^ (b - k) ∣ g.coeff k) :
    Pl.X ^ (a * b) ∣ pNorm f g := by
  set d := f.natDegree
  obtain ⟨s, _, hnorm⟩ := v99 hf e hg
  rw [hnorm]
  apply dvd_mul_of_dvd_right
  rw [Mx.det_apply]
  apply Fs.dvd_sum
  intro σ _
  suffices hdvd : Pl.X ^ (a * b) ∣ ∏ i : Fin (e + d), ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simpa [h] using hdvd
    · simpa [h] using dvd_neg.mpr hdvd
  let u : Fin (e + d) → ℕ := fun i => match finSumFinEquiv.symm i with
    | Sum.inl c => a + (c : ℕ)
    | Sum.inr c => b + (c : ℕ)
  have hentry_dvd : ∀ i : Fin (e + d), Pl.X ^ (u i - (σ i : ℕ)) ∣
        ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i := by
    intro i
    simp only [u, Mx.submatrix_apply, id_eq, v21, Mx.of_apply]
    cases hc : finSumFinEquiv.symm i with
    | inl c =>
      simp only [Pl.coeff_X_pow_mul']
      split_ifs with hle
      · have hsub : a + (c : ℕ) - (σ i : ℕ) = a - ((σ i : ℕ) - (c : ℕ)) := by omega
        rw [hsub]; exact hf_van _
      · exact dvd_zero _
    | inr c =>
      simp only [Pl.coeff_X_pow_mul']
      split_ifs with hle
      · have hsub : b + (c : ℕ) - (σ i : ℕ) = b - ((σ i : ℕ) - (c : ℕ)) := by omega
        rw [hsub]; exact hg_van _
      · exact dvd_zero _
  have hprod_dvd : Pl.X ^ (∑ i : Fin (e + d), (u i - (σ i : ℕ))) ∣
      ∏ i : Fin (e + d), ((v21 d e f g).submatrix id finSumFinEquiv.symm) (σ i) i := by
    rw [← prod_pow_eq_pow_sum]
    exact Fs.prod_dvd_prod_of_dvd _ _ (fun i _ => hentry_dvd i)
  refine (pow_dvd_pow Pl.X ?_).trans hprod_dvd
  have hineq : ∀ x y : ℕ, min x (a + b) ≤ (x - y) + min y (a + b) := by
    intro x y; omega
  have hsum_ineq : ∑ i : Fin (e + d), min (u i) (a + b) ≤ (∑ i : Fin (e + d), (u i - (σ i : ℕ))) + ∑ i : Fin (e + d), min (σ i : ℕ) (a + b) := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun i _ => hineq (u i) (σ i : ℕ))
  have hsum_perm : ∑ i : Fin (e + d), min (σ i : ℕ) (a + b) = ∑ i : Fin (e + d), min (i : ℕ) (a + b) :=
    Eqv.sum_comp σ (fun x : Fin (e + d) => min (x : ℕ) (a + b))
  have hsum_u : ∑ i : Fin (e + d), min (u i) (a + b) = (∑ i : Fin e, min (a + (i : ℕ)) (a + b)) + ∑ j : Fin d, min (b + (j : ℕ)) (a + b) := by
    rw [← Eqv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp [u]
  have hmin_sum : ∀ (c n T : ℕ), c ≤ T → T ≤ c + n → (∑ k : Fin n, min (c + (k : ℕ)) T) = (∑ k ∈ Fs.range (T - c), (c + k)) + (c + n - T) * T := by
    intro c n T hcT hTcn
    rw [Fi.sum_univ_eq_sum_range (fun k => min (c + k) T)]
    have hsplit : n = (T - c) + (c + n - T) := by omega
    conv_lhs => rw [hsplit, Fs.sum_range_add]
    congr 1
    · apply sum_congr rfl; intro k hk
      rw [Fs.mem_range] at hk; exact Nat.min_eq_left (by omega)
    · trans ∑ _k ∈ Fs.range (c + n - T), T
      · apply sum_congr rfl; intro k _
        exact Nat.min_eq_right (by omega)
      · rw [Fs.sum_const, Fs.card_range, smul_eq_mul]
  have h1 := hmin_sum a e (a + b) (by omega) (by omega)
  have h2 := hmin_sum b d (a + b) (by omega) (by omega)
  have h3 := hmin_sum 0 (e + d) (a + b) (by omega) (by omega)
  simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel, zero_add, Nat.sub_zero] at h1 h2 h3
  rw [hsum_u, h1, h2, hsum_perm, h3] at hsum_ineq
  have hrange : (∑ k ∈ Fs.range b, (a + k)) + (∑ k ∈ Fs.range a, (b + k)) = a * b + ∑ k ∈ Fs.range (a + b), k := by
    rw [Fs.sum_range_add]
    have hsplit_a : ∑ k ∈ Fs.range a, (b + k) = a * b + ∑ k ∈ Fs.range a, k := by
      rw [sum_add_distrib, Fs.sum_const, Fs.card_range, smul_eq_mul]
    rw [hsplit_a]; ring
  have htail : (a + e - (a + b)) * (a + b) + (b + d - (a + b)) * (a + b) = (e + d - (a + b)) * (a + b) := by
    rw [← add_mul]; congr 1; omega
  omega
lemma v83 {f g : Pol (Pol K)} (hf : f.Monic) (hf_irr : Irreducible f)
    (hndvd : ¬ f ∣ g) :
    pNorm f g ≠ 0 := by
  intro h0
  set d := f.natDegree
  have hd_pos : 0 < d := by
    by_contra hd0
    have hf1 : f = 1 := Pl.eq_one_of_monic_natDegree_zero hf (by omega)
    exact hf_irr.not_isUnit (hf1 ▸ isUnit_one)
  let ι : Pol K →+* RatFunc K := algebraMap (Pol K) (RatFunc K)
  have hι_inj : Fn.Injective ι := IsFractionRing.injective (Pol K) (RatFunc K)
  let fF : Pol (RatFunc K) := f.map ι
  let gF : Pol (RatFunc K) := g.map ι
  have hfF : fF.Monic := hf.map ι
  have hdegF : fF.natDegree = d := hf.natDegree_map ι
  have hdet0 : (mulMat fF gF).det = 0 := by
    change pNorm fF gF = 0
    rw [← v155 ι hf, h0, map_zero]
  obtain ⟨v, hv_ne, hv_ker⟩ := Mx.exists_mulVec_eq_zero_iff.mpr hdet0
  let pF : Pol (RatFunc K) :=
    ∑ j : Fin fF.natDegree, Pl.C (v j) * Pl.X ^ (j : ℕ)
  have hpF_ne : pF ≠ 0 := by
    intro hp0
    apply hv_ne; funext j
    have := congr_arg (fun q => q.coeff (j : ℕ)) hp0
    simp only [pF, Pl.finsetSum_coeff, Pl.coeff_C_mul_X_pow, Pl.coeff_zero] at this
    rw [sum_eq_single j] at this
    · simpa using this
    · intro k _ hkj; rw [if_neg (fun h => hkj (Fi.ext h.symm))]
    · intro h; exact absurd (mem_univ _) h
  have hpF_deg : pF.natDegree < fF.natDegree := by
    have hle : pF.natDegree ≤ fF.natDegree - 1 := by
      apply Pl.natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      simp only [pF, Pl.finsetSum_coeff, Pl.coeff_C_mul_X_pow]
      apply sum_eq_zero; intro j _; rw [if_neg (by omega)]
    omega
  have hmod0 : (pF * gF) %ₘ fF = 0 := by
    ext n
    rw [Pl.coeff_zero]
    by_cases hn : n < fF.natDegree
    · have hker_n := congr_fun hv_ker ⟨n, hn⟩
      simp only [Mx.mulVec, dotProduct, mulMat, Mx.of_apply, Pi.zero_apply] at hker_n
      simp only [pF, sum_mul, v108, Pl.finsetSum_coeff]
      rw [← hker_n]
      apply sum_congr rfl; intro j _
      rw [mul_assoc, v70 hfF, Pl.coeff_C_mul, mul_comm]
    · by_cases hm0 : (pF * gF) %ₘ fF = 0
      · simp [hm0]
      · apply Pl.coeff_eq_zero_of_natDegree_lt
        have hlt := Pl.natDegree_lt_natDegree hm0 (Pl.degree_modByMonic_lt _ hfF)
        omega
  have hdvdF : fF ∣ pF * gF := (Pl.modByMonic_eq_zero_iff_dvd hfF).mp hmod0
  rcases hdvdF with ⟨qF, hqF⟩
  have hex_clear : ∀ r : Pol (RatFunc K), ∃ (c : Pol K) (r₀ : Pol (Pol K)), c ≠ 0 ∧ r₀.map ι = Pl.C (ι c) * r := by
    intro r
    have hcoeff : ∀ n ∈ r.support, ∃ a b : Pol K, b ≠ 0 ∧ ι b * r.coeff n = ι a := by
      intro n _
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Pol K) (r.coeff n)
      refine ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, ?_⟩
      have hb' : ι b ≠ 0 := fun h => mem_nonZeroDivisors_iff_ne_zero.mp hb (hι_inj (h.trans (map_zero ι).symm))
      rw [← hab, mul_div_cancel₀ _ hb']
    choose num den hden hnd using hcoeff
    let c : Pol K := ∏ n ∈ r.support.attach, den n.1 n.2
    have hc_ne : c ≠ 0 := prod_ne_zero_iff.mpr (fun n _ => hden n.1 n.2)
    let r₀ : Pol (Pol K) :=
      ∑ n ∈ r.support.attach, Pl.C ((∏ m ∈ r.support.attach.erase n, den m.1 m.2) * num n.1 n.2) * Pl.X ^ n.1
    refine ⟨c, r₀, hc_ne, ?_⟩
    ext k
    simp only [r₀, Pl.map_sum, Pl.map_mul, Pl.map_C, Pl.map_pow, Pl.map_X, Pl.finsetSum_coeff, Pl.coeff_C_mul]
    by_cases hk : k ∈ r.support
    · rw [sum_eq_single ⟨k, hk⟩]
      · simp only [Pl.coeff_X_pow_self, mul_one, map_mul, map_prod]
        have hsplit : c = (∏ m ∈ r.support.attach.erase ⟨k, hk⟩, den m.1 m.2) * den k hk := by
          dsimp only [c]
          rw [mul_comm, ← Fs.mul_prod_erase _ (fun m : { x // x ∈ r.support } => den m.1 m.2) (Fs.mem_attach _ ⟨k, hk⟩)]
        rw [hsplit, map_mul, mul_assoc, hnd k hk, map_prod]
      · intro n _ hnk
        rw [Pl.coeff_X_pow, if_neg (fun h => hnk (Subtype.ext h.symm)), mul_zero]
      · intro h; exact absurd (Fs.mem_attach _ ⟨k, hk⟩) h
    · rw [Pl.notMem_support_iff.mp hk, mul_zero]
      apply sum_eq_zero; intro n _
      rw [Pl.coeff_X_pow, if_neg (fun h : k = n.1 => hk (h ▸ n.2)), mul_zero]
  obtain ⟨c₁, p₀, hc₁, hp₀⟩ := hex_clear pF
  obtain ⟨c₂, q₀, hc₂, hq₀⟩ := hex_clear qF
  have heq_poly : (Pl.C c₂ * p₀) * g = f * (Pl.C c₁ * q₀) := by
    apply Pl.map_injective ι hι_inj
    simp only [Pl.map_mul, Pl.map_C]
    calc (Pl.C (ι c₂) * p₀.map ι) * gF
        = Pl.C (ι c₂) * (Pl.C (ι c₁) * pF) * gF := by rw [hp₀]
      _ = Pl.C (ι c₁) * (Pl.C (ι c₂) * (pF * gF)) := by ring
      _ = Pl.C (ι c₁) * (Pl.C (ι c₂) * (fF * qF)) := by rw [hqF]
      _ = fF * (Pl.C (ι c₁) * (Pl.C (ι c₂) * qF)) := by ring
      _ = fF * (Pl.C (ι c₁) * q₀.map ι) := by rw [hq₀]
  have hf_dvd : f ∣ (Pl.C c₂ * p₀) * g := ⟨Pl.C c₁ * q₀, heq_poly⟩
  have hf_prime : Prime f := Ufm.irreducible_iff_prime.mp hf_irr
  rcases hf_prime.dvd_or_dvd hf_dvd with hdvd_p | hdvd_g
  ·
    have hp₀_ne : Pl.C c₂ * p₀ ≠ 0 := by
      intro h0'
      have hmap0 := congr_arg (Pl.map ι) h0'
      simp only [Pl.map_mul, Pl.map_C, Pl.map_zero, hp₀] at hmap0
      have hc1' : Pl.C (ι c₁) ≠ 0 :=
        Polynomial.C_ne_zero.mpr (fun h => hc₁ (hι_inj (h.trans (map_zero ι).symm)))
      have hc2' : Pl.C (ι c₂) ≠ 0 :=
        Polynomial.C_ne_zero.mpr (fun h => hc₂ (hι_inj (h.trans (map_zero ι).symm)))
      rw [← mul_assoc] at hmap0
      exact hpF_ne ((mul_eq_zero.mp hmap0).resolve_left (mul_ne_zero hc2' hc1'))
    have hdeg_p0 : (Pl.C c₂ * p₀).natDegree < d := by
      have hmap_deg : ((Pl.C c₂ * p₀).map ι).natDegree = (Pl.C c₂ * p₀).natDegree :=
        Pl.natDegree_map_eq_of_injective hι_inj _
      rw [← hmap_deg, Pl.map_mul, Pl.map_C, hp₀, ← mul_assoc, ← map_mul, ← map_mul]
      have hc12 : ι (c₂ * c₁) ≠ 0 :=
        fun h => mul_ne_zero hc₂ hc₁ (hι_inj (h.trans (map_zero ι).symm))
      rw [Pl.natDegree_C_mul hc12]
      omega
    rcases hdvd_p with ⟨r, hr⟩
    have hr_ne : r ≠ 0 := fun hr0 => hp₀_ne (by rw [hr, hr0, mul_zero])
    have hdeg_ge : d ≤ (Pl.C c₂ * p₀).natDegree := by
      rw [hr, hf.natDegree_mul' hr_ne]; omega
    omega
  · exact hndvd hdvd_g
noncomputable def v16 (x₀ : K) : Pol K →+* PS K :=
  Pl.eval₂RingHom Ps.C (Ps.C x₀ + Ps.X)
lemma v138 (x₀ : K) :
    v16 x₀ (Pl.X - Pl.C x₀) = Ps.X := by
  simp [v16]
lemma v189 (x₀ : K) (k : ℕ) (h : Pol K) :
    Ps.X ^ k ∣ v16 x₀ h ↔ (Pl.X - Pl.C x₀) ^ k ∣ h := by
  constructor
  · intro hdvd
    let h_shift : Pol K := h.comp (Pl.X + Pl.C x₀)
    have hh_eq : h = h_shift.comp (Pl.X - Pl.C x₀) := by
      simp [h_shift, Pl.comp_assoc]
    have hps_eq : v16 x₀ h = (h_shift : PS K) := by
      rw [hh_eq]
      induction h_shift using Pl.induction_on' with
      | add p q hp hq =>
        rw [Pl.add_comp, map_add, hp, hq]; simp
      | monomial n a =>
        simp only [Pl.monomial_comp, map_mul, map_pow, v138]
        have hC : v16 x₀ (Pl.C a) = Ps.C a := by simp [v16]
        rw [hC, Pl.coe_monomial]
        simp [Ps.monomial_eq_C_mul_X_pow]
    rw [hps_eq] at hdvd
    have hcoeff0 : ∀ j < k, h_shift.coeff j = 0 := by
      intro j hj
      rcases hdvd with ⟨q, hq⟩
      have := congr_arg (Ps.coeff j) hq
      rw [Pl.coeff_coe, Ps.coeff_X_pow_mul'] at this
      rw [if_neg (by omega)] at this
      exact this
    have hdiv_shift : Pl.X ^ k ∣ h_shift := by
      rw [Pl.X_pow_dvd_iff]; exact hcoeff0
    rcases hdiv_shift with ⟨q, hq⟩
    refine ⟨q.comp (Pl.X - Pl.C x₀), ?_⟩
    rw [hh_eq, hq, Pl.mul_comp, Pl.pow_comp, Pl.X_comp]
  · rintro ⟨q, rfl⟩
    rw [map_mul, map_pow, v138]
    exact dvd_mul_right _ _
lemma v61 {f g : Pol (Pol K)} (hf : f.Monic)
    (x₀ : K) (Y_s : PS K) (k : ℕ)
    (hroot : (f.map (v16 x₀)).eval Y_s = 0)
    (hdvd : Ps.X ^ k ∣ (g.map (v16 x₀)).eval Y_s) :
    (Pl.X - Pl.C x₀) ^ k ∣ pNorm f g := by
  rw [← v189, v155 (v16 x₀) hf]
  have hf_ps : (f.map (v16 x₀)).Monic := hf.map (v16 x₀)
  have hlin_dvd : (Pl.X - Pl.C Y_s) ∣ f.map (v16 x₀) :=
    Pl.dvd_iff_isRoot.mpr hroot
  rcases hlin_dvd with ⟨h, hh⟩
  have hh_monic : h.Monic := by
    have h1 : ((Pl.X - Pl.C Y_s) * h).Monic := hh ▸ hf_ps
    exact (Pl.monic_X_sub_C Y_s).of_mul_monic_left h1
  rw [hh, v97 (Pl.monic_X_sub_C Y_s) hh_monic, v132]
  exact dvd_mul_of_dvd_left hdvd _
lemma v211 {f g : Pol (Pol K)} (hf : f.Monic) (x₀ y₀ : K) :
    let σx : Pol K →+* Pol K := Pl.compRingHom (Pl.X + Pl.C x₀)
    let f' : Pol (Pol K) := (f.map σx).comp (Pl.X + Pl.C (Pl.C y₀))
    let g' : Pol (Pol K) := (g.map σx).comp (Pl.X + Pl.C (Pl.C y₀))
    (pNorm f g).comp (Pl.X + Pl.C x₀) = pNorm f' g' := by
  intro σx f' g'
  have h1 : (pNorm f g).comp (Pl.X + Pl.C x₀) = pNorm (f.map σx) (g.map σx) :=
    v155 σx hf
  rw [h1]
  set p := f.map σx
  set q := g.map σx
  set c : Pol K := Pl.C y₀
  have hp : p.Monic := hf.map σx
  have hdeg : (p.comp (Pl.X + Pl.C c)).natDegree = p.natDegree := by
    rw [Pl.natDegree_comp, Pl.natDegree_X_add_C, mul_one]
  set d := p.natDegree
  let T : Matrix (Fin d) (Fin d) (Pol K) :=
    Mx.of fun i j => ((Pl.X + Pl.C c) ^ (j : ℕ)).coeff (i : ℕ)
  have hT_det : T.det = 1 := by
    have htri : T.BlockTriangular id := by
      intro i j hij
      simp only [id_eq] at hij
      simp only [T, Mx.of_apply]
      apply Pl.coeff_eq_zero_of_natDegree_lt
      have : ((Pl.X + Pl.C c) ^ (j : ℕ)).natDegree ≤ (j : ℕ) := by
        rw [Pl.natDegree_pow, Pl.natDegree_X_add_C, mul_one]
      omega
    have hdiag : ∀ i : Fin d, T i i = 1 := by
      intro i
      simp only [T, Mx.of_apply]
      have hmon : ((Pl.X + Pl.C c) ^ (i : ℕ)).Monic :=
        (Pl.monic_X_add_C c).pow (i : ℕ)
      have hnd : ((Pl.X + Pl.C c) ^ (i : ℕ)).natDegree = (i : ℕ) := by
        rw [Pl.natDegree_pow, Pl.natDegree_X_add_C, mul_one]
      convert hmon.coeff_natDegree using 2
      exact hnd.symm
    rw [Mx.det_of_isUpperTriangular htri]; simp [hdiag]
  let M' : Matrix (Fin d) (Fin d) (Pol K) :=
    (mulMat (p.comp (Pl.X + Pl.C c)) (q.comp (Pl.X + Pl.C c))).submatrix
      (finCongr hdeg.symm) (finCongr hdeg.symm)
  have hdetM' : M'.det = pNorm f' g' := by
    rw [pNorm, ← Mx.det_reindex_self (finCongr hdeg) (mulMat f' g')]
    rfl
  by_cases hd0 : d = 0
  · have hp1 : p = 1 := Pl.eq_one_of_monic_natDegree_zero hp hd0
    have hf'1 : f' = 1 := by simp [f', p, hp1]
    have h1' : p.natDegree = 0 := hd0
    have h2' : f'.natDegree = 0 := by rw [hf'1, Pl.natDegree_one]
    have : IsEmpty (Fin p.natDegree) := by rw [h1']; infer_instance
    have : IsEmpty (Fin f'.natDegree) := by rw [h2']; infer_instance
    simp [pNorm, Mx.det_isEmpty]
  have hconj : M' * T = T * mulMat p q := by
    have hp' : (p.comp (Pl.X + Pl.C c)).Monic :=
      hp.comp (Pl.monic_X_add_C c) (by simp)
    have hcomp_mod : ∀ u : Pol (Pol K), (u.comp (Pl.X + Pl.C c)) %ₘ (p.comp (Pl.X + Pl.C c)) = (u %ₘ p).comp (Pl.X + Pl.C c) := by
      intro u
      have hdiv := Pl.modByMonic_add_div u p
      have h1 : u.comp (Pl.X + Pl.C c) = (u %ₘ p).comp (Pl.X + Pl.C c) + (p.comp (Pl.X + Pl.C c)) * ((u /ₘ p).comp (Pl.X + Pl.C c)) := by
        conv_lhs => rw [← hdiv, Pl.add_comp, Pl.mul_comp]
      rw [h1, Pl.add_modByMonic, v49 hp', add_zero]
      apply Pl.modByMonic_eq_self_iff hp' |>.mpr
      by_cases h0 : u %ₘ p = 0
      · simp only [h0, Pl.zero_comp, Pl.degree_zero]
        rw [Pl.degree_eq_natDegree hp'.ne_zero]
        exact WithBot.bot_lt_coe _
      · rw [Pl.degree_eq_natDegree (by
            intro hc0
            have hinv := congr_arg (fun w => w.comp (Pl.X - Pl.C c)) hc0
            simp [Pl.comp_assoc] at hinv
            exact h0 hinv),
          Pl.degree_eq_natDegree hp'.ne_zero, hdeg,
          Pl.natDegree_comp, Pl.natDegree_X_add_C, mul_one]
        exact_mod_cast Pl.natDegree_lt_natDegree h0 (Pl.degree_modByMonic_lt u hp)
    ext i j
    rw [Mx.mul_apply, Mx.mul_apply]
    have hlhs : ∑ k : Fin d, M' i k * T k j = (((Pl.X + Pl.C c) ^ (j : ℕ) * q.comp (Pl.X + Pl.C c)) %ₘ
          p.comp (Pl.X + Pl.C c)).coeff (i : ℕ) := by
      have hj_lt : ((Pl.X + Pl.C c) ^ (j : ℕ)).natDegree < d := by
        rw [Pl.natDegree_pow, Pl.natDegree_X_add_C, mul_one]; exact j.2
      conv_rhs => rw [v54 hj_lt (by omega)]
      rw [sum_mul, v108, Pl.finsetSum_coeff]
      apply sum_congr rfl; intro k _
      rw [mul_assoc, v70 hp', Pl.coeff_C_mul, mul_comm]
      simp [M', mulMat, T]
    have hrhs : ∑ k : Fin d, T i k * mulMat p q k j = (((Pl.X ^ (j : ℕ) * q) %ₘ p).comp (Pl.X + Pl.C c)).coeff (i : ℕ) := by
      have hlt : ((Pl.X ^ (j : ℕ) * q) %ₘ p).natDegree < d := by
        by_cases h0 : (Pl.X ^ (j : ℕ) * q) %ₘ p = 0
        · rw [h0, Pl.natDegree_zero]; omega
        · exact Pl.natDegree_lt_natDegree h0 (Pl.degree_modByMonic_lt _ hp)
      conv_rhs => rw [v54 hlt (by omega)]
      rw [Pl.sum_comp, Pl.finsetSum_coeff]
      apply sum_congr rfl; intro k _
      rw [Pl.mul_comp, Pl.C_comp, Pl.pow_comp, Pl.X_comp, Pl.coeff_C_mul, mul_comm]
      simp [T, mulMat]
    rw [hlhs, hrhs, ← hcomp_mod (Pl.X ^ (j : ℕ) * q), Pl.mul_comp, Pl.pow_comp, Pl.X_comp]
  have hdet_eq : M'.det * T.det = T.det * (mulMat p q).det := by
    rw [← Mx.det_mul, ← Mx.det_mul, hconj]
  rw [hT_det, mul_one, one_mul, hdetM'] at hdet_eq
  exact hdet_eq.symm
end BezoutBounds
private lemma v36 (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  fin_cases i <;> decide
private lemma fin5_cases (i : Fin 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  fin_cases i <;> decide
private lemma v34 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    ![a0, a1, a2, a3, a4, a5] (0 : Fin 6) = a0 := rfl
private lemma v33 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    ![a0, a1, a2, a3, a4, a5] (1 : Fin 6) = a1 := rfl
private lemma v20 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    ![a0, a1, a2, a3, a4, a5] (2 : Fin 6) = a2 := rfl
private lemma v19 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    ![a0, a1, a2, a3, a4, a5] (3 : Fin 6) = a3 := rfl
private lemma v18 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    ![a0, a1, a2, a3, a4, a5] (4 : Fin 6) = a4 := rfl
private lemma v15 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    ![a0, a1, a2, a3, a4, a5] (5 : Fin 6) = a5 := rfl
private lemma cons5_val_0 {α : Type*} (a0 a1 a2 a3 a4 : α) :
    ![a0, a1, a2, a3, a4] (0 : Fin 5) = a0 := rfl
private lemma cons5_val_1 {α : Type*} (a0 a1 a2 a3 a4 : α) :
    ![a0, a1, a2, a3, a4] (1 : Fin 5) = a1 := rfl
private lemma cons5_val_2 {α : Type*} (a0 a1 a2 a3 a4 : α) :
    ![a0, a1, a2, a3, a4] (2 : Fin 5) = a2 := rfl
private lemma cons5_val_3 {α : Type*} (a0 a1 a2 a3 a4 : α) :
    ![a0, a1, a2, a3, a4] (3 : Fin 5) = a3 := rfl
private lemma cons5_val_4 {α : Type*} (a0 a1 a2 a3 a4 : α) :
    ![a0, a1, a2, a3, a4] (4 : Fin 5) = a4 := rfl
section Dehomog
variable {K : Type*} [Field K]
lemma v10 {F : Mv3 K} {d : ℕ} (hF : F.IsHomogeneous d)
    {m : E3} (hm : F.coeff m ≠ 0) : m 0 + m 1 + m 2 = d := by
  have hdeg := hF hm
  rw [Fu.weight_apply, Fu.sum_fintype _ _ (fun _ => by simp), Fi.sum_univ_three] at hdeg
  simpa only [smul_eq_mul, Pi.one_apply, mul_one] using hdeg
noncomputable def dhZ (F : Mv3 K) : Pol (Pol K) :=
  Mv.aeval ![Pl.C Pl.X, Pl.X, 1] F
lemma dhZ_C (c : K) : dhZ (Mv.C c) = Pl.C (Pl.C c) := by
  simp [dhZ]
lemma dhZ_X0 : dhZ (Mv.X 0 : Mv3 K) = Pl.C Pl.X := by
  simp [dhZ]
lemma dhZ_X1 : dhZ (Mv.X 1 : Mv3 K) = Pl.X := by
  simp [dhZ]
lemma dhZ_X2 : dhZ (Mv.X 2 : Mv3 K) = 1 := by
  simp [dhZ]
lemma dhZ_add (F G : Mv3 K) :
    dhZ (F + G) = dhZ F + dhZ G := map_add _ F G
lemma dhZ_sub (F G : Mv3 K) :
    dhZ (F - G) = dhZ F - dhZ G := map_sub _ F G
lemma v126 (F G : Mv3 K) :
    dhZ (F * G) = dhZ F * dhZ G := map_mul _ F G
lemma dhZ_pow (F : Mv3 K) (n : ℕ) :
    dhZ (F ^ n) = dhZ F ^ n := map_pow _ F n
lemma v136 (F : Mv3 K) (x₀ y₀ : K) :
    ((dhZ F).map (Pl.evalRingHom x₀)).eval y₀ = Mv.eval ![x₀, y₀, 1] F := by
  let φ : Mv3 K →+* K :=
    (Pl.evalRingHom y₀).comp (Pl.mapRingHom (Pl.evalRingHom x₀)) |>.comp
      (Mv.aeval ![Pl.C Pl.X, Pl.X, (1 : Pol (Pol K))]).toRingHom
  change φ F = Mv.eval ![x₀, y₀, 1] F
  induction F using Mv.induction_on with
  | C a =>
    simp [φ]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    congr 1
    fin_cases i <;> simp [φ]
lemma v40 {F : Mv3 K} {d : ℕ}
    (hF : F.IsHomogeneous d) (b a : ℕ) :
    ((dhZ F).coeff b).coeff a = if a + b ≤ d then
        F.coeff (Fu.single 0 a + Fu.single 1 b + Fu.single 2 (d - a - b))
      else 0 := by
  have hF_sum : F = ∑ m ∈ F.support, Mv.monomial m (F.coeff m) := Mv.as_sum F
  conv_lhs => rw [hF_sum]
  simp only [dhZ, map_sum]
  rw [Pl.finsetSum_coeff, Pl.finsetSum_coeff]
  have hterm : ∀ m ∈ F.support, (((Mv.aeval ![Pl.C Pl.X, Pl.X, (1 : Pol (Pol K))])
        (Mv.monomial m (F.coeff m))).coeff b).coeff a =
        if m 0 = a ∧ m 1 = b then F.coeff m else 0 := by
    intro m _
    rw [Mv.aeval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
    simp only [Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, mul_one, ← Pl.C_pow]
    have halg : algebraMap K (Pol (Pol K)) (F.coeff m) = Pl.C (Pl.C (F.coeff m)) := rfl
    rw [halg]
    have hmul : Pl.C (Pl.C (F.coeff m)) * (Pl.C (Pl.X ^ m 0) * Pl.X ^ m 1) = Pl.C (Pl.C (F.coeff m) * Pl.X ^ m 0) * Pl.X ^ m 1 := by
      rw [Pl.C_mul, mul_assoc]
    rw [hmul, Pl.coeff_C_mul_X_pow]
    by_cases h1 : b = m 1
    · rw [if_pos h1, Pl.coeff_C_mul_X_pow]
      by_cases h0 : a = m 0
      · rw [if_pos h0, if_pos ⟨h0.symm, h1.symm⟩]
      · rw [if_neg h0, if_neg (fun h => h0 h.1.symm)]
    · rw [if_neg h1, Pl.coeff_zero, if_neg (fun h => h1 h.2.symm)]
  rw [sum_congr rfl hterm]
  split_ifs with hab
  · set m₀ : E3 := Fu.single 0 a + Fu.single 1 b + Fu.single 2 (d - a - b)
    have hm0_0 : m₀ 0 = a := by simp [m₀]
    have hm0_1 : m₀ 1 = b := by simp [m₀]
    have huniq : ∀ m ∈ F.support, m 0 = a ∧ m 1 = b → m = m₀ := by
      intro m hm ⟨h0, h1⟩
      have hdeg := v10 hF (Mv.mem_support_iff.mp hm)
      ext i
      fin_cases i
      · simp [m₀, h0]
      · simp [m₀, h1]
      · simp only [m₀, Fu.add_apply, Fu.single_apply, Fi.isValue]
        change m 2 = (if (0 : Fin 3) = 2 then a else 0) + (if (1 : Fin 3) = 2 then b else 0) + (if (2 : Fin 3) = 2 then d - a - b else 0)
        simp only [Fi.reduceEq, ↓reduceIte, zero_add]; omega
    by_cases hm0 : m₀ ∈ F.support
    · rw [sum_eq_single m₀]
      · rw [if_pos ⟨hm0_0, hm0_1⟩]
      · intro m hm hne
        rw [if_neg (fun h => hne (huniq m hm h))]
      · intro h; exact absurd hm0 h
    · rw [Mv.notMem_support_iff.mp hm0]
      apply sum_eq_zero; intro m hm
      rw [if_neg (fun h => hm0 (huniq m hm h ▸ hm))]
  · apply sum_eq_zero; intro m hm
    rw [if_neg]
    rintro ⟨h0, h1⟩
    have hdeg := v10 hF (Mv.mem_support_iff.mp hm)
    omega
lemma v102 {F : Mv3 K} {d : ℕ} (hF : F.IsHomogeneous d) (b : ℕ) :
    ((dhZ F).coeff b).natDegree + b ≤ d ∨ (dhZ F).coeff b = 0 := by
  by_cases hb0 : (dhZ F).coeff b = 0
  · exact Or.inr hb0
  · left
    have hle : ((dhZ F).coeff b).natDegree ≤ d - b := by
      apply Pl.natDegree_le_iff_coeff_eq_zero.mpr
      intro a ha
      rw [v40 hF b a, if_neg (by omega)]
    have hb_le : b ≤ d := by
      by_contra hgt; push Not at hgt
      apply hb0; ext a
      rw [v40 hF b a, if_neg (by omega), Pl.coeff_zero]
    omega
lemma v93 {F : Mv3 K} {d : ℕ}
    (hF : F.IsHomogeneous d) {b : ℕ} (hb : d < b) : (dhZ F).coeff b = 0 := by
  ext a
  rw [v40 hF b a, if_neg (by omega), Pl.coeff_zero]
lemma dhZ_deg_bound' {F : Mv3 K} {d : ℕ} (hF : F.IsHomogeneous d) (b : ℕ)
    (hb : b ≤ d) : ((dhZ F).coeff b).natDegree + b ≤ d := by
  rcases v102 hF b with h | h
  · exact h
  · rw [h, Pl.natDegree_zero, zero_add]; exact hb
lemma v103 {F : Mv3 K} {d : ℕ} (hF : F.IsHomogeneous d) :
    (dhZ F).coeff d = Pl.C (Mv.eval ![0, 1, 0] F) := by
  have heval : Mv.eval ![0, 1, 0] F = F.coeff (Fu.single 1 d) := by
    conv_lhs => rw [Mv.as_sum F]
    rw [map_sum]
    have hterm : ∀ m ∈ F.support, Mv.eval ![0, 1, 0] (Mv.monomial m (F.coeff m)) = if m = Fu.single 1 d then F.coeff m else 0 := by
      intro m hm
      rw [Mv.eval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
      simp only [Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, mul_one]
      have hdeg := v10 hF (Mv.mem_support_iff.mp hm)
      by_cases h0 : m 0 = 0
      · by_cases h2 : m 2 = 0
        · have hm_eq : m = Fu.single 1 d := by
            ext i; fin_cases i <;> simp [h0, h2]; omega
          rw [h0, h2, pow_zero, mul_one, mul_one, if_pos hm_eq]
        · have hne : m ≠ Fu.single 1 d := by
            intro heq; apply h2; rw [heq]; simp
          rw [zero_pow h2, mul_zero, mul_zero, if_neg hne]
      · rw [zero_pow h0, zero_mul, mul_zero, if_neg]
        intro heq; apply h0; rw [heq]; simp
    rw [sum_congr rfl hterm]
    by_cases hmem : Fu.single 1 d ∈ F.support
    · rw [sum_eq_single (Fu.single 1 d)]
      · rw [if_pos rfl]
      · intro m _ hne; rw [if_neg hne]
      · intro h; exact absurd hmem h
    · rw [Mv.notMem_support_iff.mp hmem]
      apply sum_eq_zero; intro m hm
      rw [if_neg (fun (heq : m = Fu.single 1 d) => hmem (heq ▸ hm))]
  ext a
  rw [v40 hF d a, Pl.coeff_C]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos (by omega), if_pos rfl, heval]
    congr 1; ext i; fin_cases i <;> simp
  · rw [if_neg (by omega), if_neg ha]
noncomputable def mdhZ (F : Mv3 K) : Pol (Pol K) :=
  Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)⁻¹) * dhZ F
lemma v149 {F : Mv3 K} {d : ℕ}
    (hF : F.IsHomogeneous d) (h010 : Mv.eval ![0, 1, 0] F ≠ 0) :
    (mdhZ F).Monic ∧ (mdhZ F).natDegree = d := by
  have htop : (mdhZ F).coeff d = 1 := by
    simp only [mdhZ, Pl.coeff_C_mul, v103 hF, ← map_mul, inv_mul_cancel₀ h010, map_one]
  have hgt : ∀ b > d, (mdhZ F).coeff b = 0 := by
    intro b hb
    simp only [mdhZ, Pl.coeff_C_mul, v93 hF hb, mul_zero]
  have hdeg : (mdhZ F).natDegree = d := by
    apply le_antisymm
    · exact Pl.natDegree_le_iff_coeff_eq_zero.mpr hgt
    · exact Pl.le_natDegree_of_ne_zero (by rw [htop]; exact one_ne_zero)
  refine ⟨?_, hdeg⟩
  rw [Pl.Monic, Pl.leadingCoeff, hdeg, htop]
lemma v133 {F : Mv3 K} {d : ℕ}
    (hF : F.IsHomogeneous d) (b : ℕ) :
    ((mdhZ F).coeff b).natDegree + b ≤ d ∨ (mdhZ F).coeff b = 0 := by
  rcases v102 hF b with h | h
  · left
    simp only [mdhZ, Pl.coeff_C_mul]
    exact (Nat.add_le_add_right (Pl.natDegree_C_mul_le _ _) b).trans h
  · right
    simp only [mdhZ, Pl.coeff_C_mul, h, mul_zero]
noncomputable def bDeg (p : Pol (Pol K)) : ℕ :=
  p.support.sup (fun b => (p.coeff b).natDegree + b)
lemma bDeg_le {p : Pol (Pol K)} (b : ℕ) (hb : p.coeff b ≠ 0) :
    (p.coeff b).natDegree + b ≤ bDeg p :=
  le_sup (f := fun j => (p.coeff j).natDegree + j) (Pl.mem_support_iff.mpr hb)
noncomputable def hmZ (e : ℕ) (p : Pol (Pol K)) : Mv3 K :=
  ∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support, Mv.monomial
      (Fu.single 0 a + Fu.single 1 b + Fu.single 2 (e - a - b))
      ((p.coeff b).coeff a)
lemma v58 {p : Pol (Pol K)} {e : ℕ} (he : bDeg p ≤ e) :
    (hmZ e p).IsHomogeneous e := by
  unfold hmZ
  apply MvPolynomial.IsHomogeneous.sum
  intro b hb
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  apply Mv.isHomogeneous_monomial
  have hb_ne : p.coeff b ≠ 0 := Pl.mem_support_iff.mp hb
  have ha_le : a ≤ (p.coeff b).natDegree := Pl.le_natDegree_of_mem_supp a ha
  have hle : (p.coeff b).natDegree + b ≤ e := (bDeg_le b hb_ne).trans he
  rw [Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi), Fi.sum_univ_three]
  simp only [Fu.add_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, add_zero, zero_add]
  omega
lemma v198 {p : Pol (Pol K)} {e : ℕ} (he : bDeg p ≤ e) :
    dhZ (hmZ e p) = p := by
  ext b a
  rw [v40 (v58 he) b a]
  by_cases hmem : b ∈ p.support ∧ a ∈ (p.coeff b).support
  · have hb_ne : p.coeff b ≠ 0 := Pl.mem_support_iff.mp hmem.1
    have ha_le : a ≤ (p.coeff b).natDegree := Pl.le_natDegree_of_mem_supp a hmem.2
    have hle : a + b ≤ e := by have := (bDeg_le b hb_ne).trans he; omega
    rw [if_pos hle]
    unfold hmZ
    rw [Mv.coeff_sum]
    rw [sum_eq_single b]
    · rw [Mv.coeff_sum, sum_eq_single a]
      · rw [Mv.coeff_monomial, if_pos rfl]
      · intro a' _ ha'
        rw [Mv.coeff_monomial, if_neg]
        intro h; apply ha'
        have := congr_arg (fun f : E3 => f 0) h; simpa using this
      · intro h; exact absurd hmem.2 h
    · intro b' _ hb'
      rw [Mv.coeff_sum]
      apply sum_eq_zero; intro a' _
      rw [Mv.coeff_monomial, if_neg]
      intro h; apply hb'
      have := congr_arg (fun f : E3 => f 1) h; simpa using this
    · intro h; exact absurd hmem.1 h
  · have hzero : (p.coeff b).coeff a = 0 := by
      by_cases hb : b ∈ p.support
      · exact Pl.notMem_support_iff.mp (fun ha => hmem ⟨hb, ha⟩)
      · rw [Pl.notMem_support_iff.mp hb, Pl.coeff_zero]
    rw [hzero]
    split_ifs with hab
    · unfold hmZ
      rw [Mv.coeff_sum]
      apply sum_eq_zero; intro b' hb'
      rw [Mv.coeff_sum]
      apply sum_eq_zero; intro a' ha'
      rw [Mv.coeff_monomial, if_neg]
      intro h
      have h0 : a' = a := by have := congr_arg (fun f : E3 => f 0) h; simpa using this
      have h1 : b' = b := by have := congr_arg (fun f : E3 => f 1) h; simpa using this
      exact hmem ⟨h1 ▸ hb', h0 ▸ h1 ▸ ha'⟩
    · rfl
lemma v121 {p : Pol (Pol K)} (hp : p ≠ 0) :
    Mv.aeval ![Mv.X 0, Mv.X 1, (0 : Mv2 K)]
      (hmZ (bDeg p) p) ≠ 0 := by
  have hne : p.support.Nonempty := Pl.support_nonempty.mpr hp
  obtain ⟨b₀, hb₀_mem, hb₀_max⟩ := Fs.exists_mem_eq_sup p.support hne
    (fun b => (p.coeff b).natDegree + b)
  set a₀ := (p.coeff b₀).natDegree
  have hb₀_ne : p.coeff b₀ ≠ 0 := Pl.mem_support_iff.mp hb₀_mem
  have ha₀_ne : (p.coeff b₀).coeff a₀ ≠ 0 := Pl.leadingCoeff_ne_zero.mpr hb₀_ne
  have ha₀_mem : a₀ ∈ (p.coeff b₀).support := Pl.mem_support_iff.mpr ha₀_ne
  have hdeg : bDeg p = a₀ + b₀ := hb₀_max
  intro hzero
  have hc := congr_arg (Mv.coeff (Fu.single 0 a₀ + Fu.single 1 b₀)) hzero
  rw [Mv.coeff_zero] at hc
  apply ha₀_ne
  rw [← hc]
  unfold hmZ
  simp only [map_sum, Mv.coeff_sum]
  have hcoeff_mon : ∀ (a b c d' : ℕ) (r : K), Mv.coeff (Fu.single (0 : Fin 2) a + Fu.single 1 b)
        (Mv.C r * (Mv.X 0 ^ c * Mv.X 1 ^ d' : Mv2 K)) =
        if c = a ∧ d' = b then r else 0 := by
    intro a b c d' r
    have h1 : Mv.C r * (Mv.X 0 ^ c * Mv.X 1 ^ d' : Mv2 K) = Mv.monomial (Fu.single (0 : Fin 2) c + Fu.single 1 d') r := by
      rw [Mv.monomial_eq, Fu.prod_fintype (f := Fu.single (0 : Fin 2) c + Fu.single 1 d') _ (fun _ => pow_zero _), Fi.prod_univ_two]
      simp
    rw [h1, Mv.coeff_monomial]
    by_cases h : c = a ∧ d' = b
    · rw [if_pos (by rw [h.1, h.2]), if_pos h]
    · rw [if_neg, if_neg h]
      intro heq; apply h
      exact ⟨by simpa using congr_arg (fun f : Fin 2 →₀ ℕ => f 0) heq, by simpa using congr_arg (fun f : Fin 2 →₀ ℕ => f 1) heq⟩
  rw [sum_eq_single b₀]
  · rw [sum_eq_single a₀]
    · rw [Mv.aeval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
      simp only [Fu.add_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, add_zero, zero_add, hdeg]
      have hsub : a₀ + b₀ - a₀ - b₀ = 0 := by omega
      rw [hsub, pow_zero, mul_one, Mv.algebraMap_eq, hcoeff_mon, if_pos ⟨rfl, rfl⟩]
    · intro a' _ ha'
      rw [Mv.aeval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
      simp only [Fu.add_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, add_zero, zero_add]
      by_cases h2 : bDeg p - a' - b₀ = 0
      · rw [h2, pow_zero, mul_one, Mv.algebraMap_eq, hcoeff_mon, if_neg (fun h => ha' h.1)]
      · rw [zero_pow h2, mul_zero, mul_zero, Mv.coeff_zero]
    · intro h; exact absurd ha₀_mem h
  · intro b' _ hb'
    apply sum_eq_zero; intro a' _
    rw [Mv.aeval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
    simp only [Fu.add_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, add_zero, zero_add]
    by_cases h2 : bDeg p - a' - b' = 0
    · rw [h2, pow_zero, mul_one, Mv.algebraMap_eq, hcoeff_mon, if_neg (fun h => hb' h.2)]
    · rw [zero_pow h2, mul_zero, mul_zero, Mv.coeff_zero]
  · intro h; exact absurd hb₀_mem h
lemma v180 {P Q : Mv3 K} {d e : ℕ}
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous e)
    (hP0 : Mv.aeval ![Mv.X 0, Mv.X 1, (0 : Mv2 K)] P ≠ 0)
    (hQ0 : Mv.aeval ![Mv.X 0, Mv.X 1, (0 : Mv2 K)] Q ≠ 0)
    (heq : dhZ P = dhZ Q) :
    d = e ∧ P = Q := by
  have hcoeff : ∀ b a, (if a + b ≤ d then P.coeff (Fu.single 0 a + Fu.single 1 b + Fu.single 2 (d - a - b)) else 0) = (if a + b ≤ e then Q.coeff (Fu.single 0 a + Fu.single 1 b + Fu.single 2 (e - a - b)) else 0) := by
    intro b a
    have := congr_arg (fun r => (r.coeff b).coeff a) heq
    rwa [v40 hP, v40 hQ] at this
  have hle_de : d ≤ e := by
    have hex : ∃ m ∈ P.support, m 2 = 0 := by
      by_contra hnone; push Not at hnone
      apply hP0
      rw [Mv.as_sum P, map_sum]
      apply sum_eq_zero; intro m hm
      rw [Mv.aeval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
      simp only [Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons]
      rw [zero_pow (hnone m hm), mul_zero, mul_zero]
    rcases hex with ⟨m, hm, hm2⟩
    have hdeg := v10 hP (Mv.mem_support_iff.mp hm)
    have h1 := hcoeff (m 1) (m 0)
    have hm_eq : Fu.single 0 (m 0) + Fu.single 1 (m 1) + Fu.single 2 (d - m 0 - m 1) = m := by
      ext i; fin_cases i <;> simp [hm2]; omega
    rw [if_pos (by omega), hm_eq] at h1
    by_contra hlt; push Not at hlt
    rw [if_neg (by omega)] at h1
    exact Mv.mem_support_iff.mp hm h1
  have hle_ed : e ≤ d := by
    have hex : ∃ m ∈ Q.support, m 2 = 0 := by
      by_contra hnone; push Not at hnone
      apply hQ0
      rw [Mv.as_sum Q, map_sum]
      apply sum_eq_zero; intro m hm
      rw [Mv.aeval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
      simp only [Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons]
      rw [zero_pow (hnone m hm), mul_zero, mul_zero]
    rcases hex with ⟨m, hm, hm2⟩
    have hdeg := v10 hQ (Mv.mem_support_iff.mp hm)
    have h1 := hcoeff (m 1) (m 0)
    have hm_eq : Fu.single 0 (m 0) + Fu.single 1 (m 1) + Fu.single 2 (e - m 0 - m 1) = m := by
      ext i; fin_cases i <;> simp [hm2]; omega
    by_contra hlt; push Not at hlt
    rw [if_neg (by omega), if_pos (by omega), hm_eq] at h1
    exact Mv.mem_support_iff.mp hm h1.symm
  have hde : d = e := le_antisymm hle_de hle_ed
  refine ⟨hde, ?_⟩
  subst hde
  ext m
  by_cases hsum : m 0 + m 1 + m 2 = d
  · have hm_eq : Fu.single 0 (m 0) + Fu.single 1 (m 1) + Fu.single 2 (d - m 0 - m 1) = m := by
      ext i; fin_cases i <;> simp; omega
    have h1 := hcoeff (m 1) (m 0)
    rw [if_pos (by omega), if_pos (by omega), hm_eq] at h1
    exact h1
  · have hp0 : P.coeff m = 0 := by
      by_contra hne; exact hsum (v10 hP hne)
    have hq0 : Q.coeff m = 0 := by
      by_contra hne; exact hsum (v10 hQ hne)
    rw [hp0, hq0]
lemma v71 {F : Mv3 K} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F)
    (h010 : Mv.eval ![0, 1, 0] F ≠ 0) :
    Irreducible (mdhZ F) := by
  have heval_Z0 : ∀ G : Mv3 K, Mv.eval ![0, 1] (Mv.aeval ![Mv.X 0, Mv.X 1, (0 : Mv2 K)] G) = Mv.eval ![0, 1, 0] G := by
    intro G
    induction G using Mv.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1; fin_cases i <;> simp
  have hF_Z0 : Mv.aeval ![Mv.X 0, Mv.X 1, (0 : Mv2 K)] F ≠ 0 := by
    intro h0
    apply h010
    rw [← heval_Z0 F, h0, map_zero]
  have hirr_d : Irreducible (dhZ F) := by
    have hd_pos : 0 < d := by
      by_contra hd0; push Not at hd0
      have hd_eq : d = 0 := by omega
      subst hd_eq
      have hFc : F = Mv.C (Mv.eval ![0, 1, 0] F) := by
        ext m
        by_cases hm : m = 0
        · subst hm
          have h1 := v103 hF
          have h2 := v40 hF 0 0
          rw [if_pos (by omega)] at h2
          have h3 : (Fu.single 0 0 + Fu.single 1 0 + Fu.single 2 0 : E3) = 0 := by
            ext i; fin_cases i <;> simp
          rw [h3] at h2
          rw [h1, Pl.coeff_C_zero] at h2
          rw [Mv.coeff_C, if_pos rfl, ← h2]
        · rw [Mv.coeff_C, if_neg (Ne.symm hm)]
          by_contra hne
          have hdeg := v10 hF hne
          apply hm; ext i; fin_cases i <;> simp <;> omega
      exact hF_irr.not_isUnit (hFc ▸ (isUnit_iff_ne_zero.mpr h010).map Mv.C)
    refine ⟨?_, ?_⟩
    · intro hu
      have hdeg0 : (dhZ F).natDegree = 0 := Pl.natDegree_eq_zero_of_isUnit hu
      have htop_ne : (dhZ F).coeff d ≠ 0 := by
        rw [v103 hF]; exact Polynomial.C_ne_zero.mpr h010
      have hle := Pl.le_natDegree_of_ne_zero htop_ne
      omega
    · intro g h hgh
      have hg0 : g ≠ 0 := fun h0 => by
        rw [h0, zero_mul] at hgh
        have := congr_arg (fun r => r.coeff d) hgh
        rw [v103 hF, Pl.coeff_zero] at this
        exact Polynomial.C_ne_zero.mpr h010 this
      have hh0 : h ≠ 0 := fun h0 => by
        rw [h0, mul_zero] at hgh
        have := congr_arg (fun r => r.coeff d) hgh
        rw [v103 hF, Pl.coeff_zero] at this
        exact Polynomial.C_ne_zero.mpr h010 this
      set G := hmZ (bDeg g) g
      set H := hmZ (bDeg h) h
      have hGH_hom : (G * H).IsHomogeneous (bDeg g + bDeg h) :=
        (v58 le_rfl).mul (v58 le_rfl)
      have hGH_Z0 : Mv.aeval ![Mv.X 0, Mv.X 1, (0 : Mv2 K)] (G * H) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero (v121 hg0) (v121 hh0)
      have hGH_de : dhZ (G * H) = dhZ F := by
        rw [v126, v198 le_rfl, v198 le_rfl, hgh]
      have hF_eq : G * H = F := (v180 hGH_hom hF hGH_Z0 hF_Z0 hGH_de).2
      rcases hF_irr.isUnit_or_isUnit hF_eq.symm with huG | huH
      · left
        have := huG.map (Mv.aeval ![Pl.C Pl.X, Pl.X, (1 : Pol (Pol K))]).toRingHom
        change IsUnit (dhZ G) at this
        rwa [v198 le_rfl] at this
      · right
        have := huH.map (Mv.aeval ![Pl.C Pl.X, Pl.X, (1 : Pol (Pol K))]).toRingHom
        change IsUnit (dhZ H) at this
        rwa [v198 le_rfl] at this
  have hunit : IsUnit (Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)⁻¹) : Pol (Pol K)) :=
    ((isUnit_iff_ne_zero.mpr (inv_ne_zero h010)).map Pl.C).map Pl.C
  exact (Associated.irreducible_iff ⟨hunit.unit, mul_comm _ _⟩).mp hirr_d
end Dehomog
section PowerSeriesCalculus
variable {K : Type*} [Field K]
noncomputable def psD (f : PS K) : PS K :=
  Ps.mk fun n => ((n + 1 : ℕ) : K) * Ps.coeff (n + 1) f
lemma v66 (f : PS K) (n : ℕ) :
    Ps.coeff n (psD f) = ((n + 1 : ℕ) : K) * Ps.coeff (n + 1) f := by
  simp [psD]
lemma v104 : psD (0 : PS K) = 0 := by
  ext n; simp [v66]
lemma psD_C (c : K) : psD (Ps.C c) = 0 := by
  ext n; simp [v66]
lemma v159 : psD (1 : PS K) = 0 := by
  simpa using psD_C (1 : K)
lemma v209 (n : ℕ) [n.AtLeastTwo] : psD (OfNat.ofNat n : PS K) = 0 := by
  have h1 : (OfNat.ofNat n : PS K) = Ps.C (OfNat.ofNat n : K) := by
    simp [OfNat.ofNat]
  rw [h1, psD_C]
lemma psD_X : psD (Ps.X : PS K) = 1 := by
  ext n
  rw [v66, Ps.coeff_X, Ps.coeff_one]
  cases n <;> simp
lemma v51 (f g : PS K) : psD (f + g) = psD f + psD g := by
  ext n; simp only [v66, map_add]; ring
lemma psD_neg (f : PS K) : psD (-f) = -psD f := by
  ext n; simp only [v66, map_neg]; ring
lemma v148 (f g : PS K) : psD (f - g) = psD f - psD g := by
  ext n; simp only [v66, map_sub]; ring
lemma v210 (c : K) (f : PS K) :
    psD (Ps.C c * f) = Ps.C c * psD f := by
  ext n; simp only [v66, Ps.coeff_C_mul]; ring
lemma v29 (f g : PS K) :
    psD (f * g) = psD f * g + f * psD g := by
  ext n
  rw [v66, Ps.coeff_mul, map_add, Ps.coeff_mul, Ps.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Ps.coeff i f * Ps.coeff j g), Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Ps.coeff i (psD f) * Ps.coeff j g), Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Ps.coeff i f * Ps.coeff j (psD g))]
  rw [mul_sum]
  have hsplit : ∀ k ∈ Fs.range (n + 2), ((n + 1 : ℕ) : K) * (Ps.coeff k f * Ps.coeff (n + 1 - k) g) = ((k : ℕ) : K) * (Ps.coeff k f * Ps.coeff (n + 1 - k) g) + ((n + 1 - k : ℕ) : K) * (Ps.coeff k f * Ps.coeff (n + 1 - k) g) := by
    intro k hk
    rw [Fs.mem_range] at hk
    have hadd : k + (n + 1 - k) = n + 1 := by omega
    rw [← add_mul, ← Nat.cast_add, hadd]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  congr 1
  · rw [Fs.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply sum_congr rfl; intro k _
    rw [v66, Nat.succ_sub_succ]; ring
  · rw [Fs.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    apply sum_congr rfl; intro k hk
    rw [Fs.mem_range] at hk
    have hsub : n + 1 - k = (n - k) + 1 := by omega
    rw [hsub, v66]; ring
lemma v11 (n : ℕ) [n.AtLeastTwo] (f : PS K) :
    psD (OfNat.ofNat n * f) = OfNat.ofNat n * psD f := by
  rw [v29, v209, zero_mul, zero_add]
lemma psD_pow (f : PS K) (m : ℕ) :
    psD (f ^ m) = (m : PS K) * f ^ (m - 1) * psD f := by
  induction m with
  | zero => simp [v159]
  | succ m ih =>
    rw [pow_succ, v29, ih]
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      ring
lemma v197 {p : ℕ} [CharP K p] (f : PS K) :
    psD (f ^ p) = 0 := by
  have hp0 : (p : PS K) = 0 := by
    have : (p : PS K) = Ps.C (p : K) := (map_natCast Ps.C p).symm
    rw [this, Ch.cast_eq_zero K p, map_zero]
  rw [psD_pow, hp0, zero_mul, zero_mul]
lemma v160 {p : ℕ} (_hp : Nat.Prime p) [CharP K p] {f : PS K}
    (hf : psD f = 0) :
    Ps.X ^ p ∣ f - Ps.C (Ps.constantCoeff f) := by
  rw [Ps.X_pow_dvd_iff]
  intro n hn
  cases n with
  | zero => simp [Ps.coeff_zero_eq_constantCoeff]
  | succ k =>
    have h1 := congr_arg (Ps.coeff k) hf
    rw [v66, map_zero] at h1
    have hne : ((k + 1 : ℕ) : K) ≠ 0 := by
      intro h0
      have hdvd := (Ch.cast_eq_zero_iff K p (k + 1)).mp h0
      have hle := Nat.le_of_dvd (Nat.succ_pos k) hdvd
      omega
    have hc0 : Ps.coeff (k + 1) f = 0 := (mul_eq_zero.mp h1).resolve_left hne
    rw [map_sub, hc0, Ps.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]
lemma v167 {p : ℕ} (hp : Nat.Prime p) [CharP K p] (f : PS K) :
    Ps.X ^ p ∣ f ^ p - Ps.C (Ps.constantCoeff f ^ p) := by
  have h1 := v160 hp (v197 (p := p) f)
  simpa [map_pow] using h1
noncomputable def v17 (k : ℕ) (f : PS K) : PS K :=
  psD^[k] f
lemma v212 (f : PS K) : v17 0 f = f := rfl
lemma v41 (k : ℕ) (f : PS K) :
    v17 (k + 1) f = psD (v17 k f) :=
  Fn.iterate_succ_apply' psD k f
lemma iterDeriv_add (k : ℕ) (f g : PS K) :
    v17 k (f + g) = v17 k f + v17 k g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [v41, ih, v51, ← v41, ← v41]
lemma iterDeriv_sub (k : ℕ) (f g : PS K) :
    v17 k (f - g) = v17 k f - v17 k g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [v41, ih, v148, ← v41, ← v41]
lemma iterDeriv_C_mul (k : ℕ) (c : K) (f : PS K) :
    v17 k (Ps.C c * f) = Ps.C c * v17 k f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [v41, ih, v210, ← v41]
lemma v164 {R : Type*} [CommRing R] (p : Pol R) (u v : R) :
    ∃ q : R, p.eval (u + v) = p.eval u + p.derivative.eval u * v + v ^ 2 * q := by
  induction p using Pl.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    rcases hp₁ with ⟨q₁, hq₁⟩
    rcases hp₂ with ⟨q₂, hq₂⟩
    refine ⟨q₁ + q₂, ?_⟩
    simp only [Pl.eval_add, Pl.derivative_add, hq₁, hq₂]; ring
  | monomial n a =>
    have hpow : ∀ m : ℕ, ∃ r : R, (u + v) ^ m = u ^ m + (m : R) * u ^ (m - 1) * v + v ^ 2 * r := by
      intro m
      induction m with
      | zero => exact ⟨0, by simp⟩
      | succ m ih =>
        rcases ih with ⟨r, hr⟩
        cases m with
        | zero => exact ⟨0, by simp⟩
        | succ m =>
          refine ⟨(m + 1 : R) * u ^ m + r * (u + v), ?_⟩
          rw [pow_succ, hr]
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
          rw [pow_succ u m]
          ring
    rcases hpow n with ⟨r, hr⟩
    refine ⟨a * r, ?_⟩
    rw [Pl.eval_monomial, Pl.eval_monomial, Pl.derivative_monomial, Pl.eval_monomial, hr]
    ring
lemma v168 {R : Type*} [CommRing R] (p : Pol R) {u v w : R}
    (h : w ∣ u - v) : w ∣ p.eval u - p.eval v :=
  h.trans (Pl.sub_dvd_eval_sub u v p)
theorem v75 (f : Pol (Pol K)) (x₀ y₀ : K)
    (hroot : (f.map (Pl.evalRingHom x₀)).eval y₀ = 0)
    (hderiv : (f.derivative.map (Pl.evalRingHom x₀)).eval y₀ ≠ 0) :
    ∃ Y : PS K, Ps.constantCoeff Y = y₀ ∧ (f.map (v16 x₀)).eval Y = 0 := by
  let fps : Pol (PS K) := f.map (v16 x₀)
  let dy0 : K := (f.derivative.map (Pl.evalRingHom x₀)).eval y₀
  have hconst_eval : ∀ (g : Pol (Pol K)) (P : PS K), Ps.constantCoeff ((g.map (v16 x₀)).eval P) = (g.map (Pl.evalRingHom x₀)).eval (Ps.constantCoeff P) := by
    intro g P
    have hcomp : Ps.constantCoeff.comp (v16 x₀) = Pl.evalRingHom x₀ := by
      ext <;> simp [v16]
    induction g using Pl.induction_on' with
    | add g₁ g₂ h₁ h₂ => simp [Pl.map_add, Pl.eval_add, h₁, h₂]
    | monomial n a =>
      simp only [Pl.map_monomial, Pl.eval_monomial, map_mul, map_pow]
      congr 1
      exact congr_fun (congr_arg DFunLike.coe hcomp) a
  let P : ℕ → PS K := Nat.rec (Ps.C y₀) (fun n Pn =>
    Pn + Ps.C (-(dy0⁻¹ * Ps.coeff (n + 1) (fps.eval Pn))) * Ps.X ^ (n + 1))
  have hP0 : ∀ n, Ps.constantCoeff (P n) = y₀ := by
    intro n
    induction n with
    | zero => simp [P]
    | succ n ih =>
      dsimp only [P]
      rw [map_add, ih, map_mul, map_pow, Ps.constantCoeff_X, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
  have hP_coeff_stable : ∀ n m, n ≤ m → Ps.coeff n (P m) = Ps.coeff n (P n) := by
    intro n m hnm
    induction m with
    | zero =>
      have : n = 0 := by omega
      subst this; rfl
    | succ m ih =>
      by_cases h : n = m + 1
      · subst h; rfl
      · have hle : n ≤ m := by omega
        dsimp only [P]
        rw [map_add, ih hle, Ps.coeff_C_mul_X_pow, if_neg (by omega), add_zero]
  have hP_vanish : ∀ n k, k ≤ n → Ps.coeff k (fps.eval (P n)) = 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [Ps.coeff_zero_eq_constantCoeff]
      change Ps.constantCoeff ((f.map (v16 x₀)).eval (Ps.C y₀)) = 0
      rw [hconst_eval, Ps.constantCoeff_C, hroot]
    | succ n ih =>
      intro k hk
      set c : K := -(dy0⁻¹ * Ps.coeff (n + 1) (fps.eval (P n)))
      set v : PS K := Ps.C c * Ps.X ^ (n + 1)
      obtain ⟨q, hq⟩ := v164 fps (P n) v
      have hPn1 : P (n + 1) = P n + v := rfl
      rw [hPn1, hq, map_add, map_add]
      have hv2 : Ps.coeff k (v ^ 2 * q) = 0 := by
        have hv2_eq : v ^ 2 * q = Ps.X ^ (2 * (n + 1)) * (Ps.C (c ^ 2) * q) := by
          dsimp only [v]; rw [mul_pow, ← map_pow, ← pow_mul]; ring
        rw [hv2_eq, Ps.coeff_X_pow_mul', if_neg (by omega)]
      rw [hv2, add_zero]
      have hdv_eq : fps.derivative.eval (P n) * v = Ps.X ^ (n + 1) * (Ps.C c * fps.derivative.eval (P n)) := by
        dsimp only [v]; ring
      rw [hdv_eq, Ps.coeff_X_pow_mul']
      by_cases hkn : k ≤ n
      · rw [if_neg (by omega), ih k hkn, add_zero]
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        rw [if_pos le_rfl, Nat.sub_self, Ps.coeff_zero_eq_constantCoeff, map_mul, Ps.constantCoeff_C]
        have hder_const : Ps.constantCoeff (fps.derivative.eval (P n)) = dy0 := by
          have hdmap : fps.derivative = f.derivative.map (v16 x₀) :=
            Pl.derivative_map (p := f) (f := v16 x₀)
          rw [hdmap, hconst_eval, hP0 n]
        rw [hder_const]
        dsimp only [c]
        have : Ps.coeff (n + 1) (fps.eval (P n)) + -(dy0⁻¹ * Ps.coeff (n + 1) (fps.eval (P n))) * dy0 = 0 := by
          rw [neg_mul, mul_comm _ dy0, ← mul_assoc, mul_inv_cancel₀ hderiv, one_mul, add_neg_cancel]
        exact this
  let Y : PS K := Ps.mk fun n => Ps.coeff n (P n)
  refine ⟨Y, ?_, ?_⟩
  · rw [← Ps.coeff_zero_eq_constantCoeff]
    simp [Y, P]
  · ext n
    rw [map_zero]
    have hdiff : Ps.X ^ (n + 1) ∣ Y - P n := by
      rw [Ps.X_pow_dvd_iff]
      intro k hk
      rw [map_sub]
      simp only [Y, Ps.coeff_mk]
      rw [hP_coeff_stable k n (by omega), sub_self]
    have heval_diff := v168 fps hdiff
    have hc0 : Ps.coeff n (fps.eval Y - fps.eval (P n)) = 0 :=
      (PowerSeries.X_pow_dvd_iff.mp heval_diff) n (Nat.lt_succ_self n)
    rw [map_sub, hP_vanish n n le_rfl, sub_zero] at hc0
    exact hc0
end PowerSeriesCalculus
section AbstractFrobWronsk
variable {R : Type*} [CommRing R]
structure v35 (R : Type*) [CommRing R] where
  toFun : R → R
  map_add' : ∀ a b, toFun (a + b) = toFun a + toFun b
  leibniz' : ∀ a b, toFun (a * b) = toFun a * b + a * toFun b
instance : CoeFun (v35 R) (fun _ => R → R) := ⟨v35.toFun⟩
lemma v35.map_add (D : v35 R) (a b : R) : D (a + b) = D a + D b := D.map_add' a b
lemma v35.leibniz (D : v35 R) (a b : R) : D (a * b) = D a * b + a * D b := D.leibniz' a b
lemma v35.map_one (D : v35 R) : D 1 = 0 := by
  have h := D.leibniz 1 1
  simp only [mul_one, one_mul] at h
  exact add_left_cancel (h.symm.trans (add_zero (D 1)).symm)
lemma v35.map_two (D : v35 R) : D 2 = 0 := by
  have : (2 : R) = 1 + 1 := by ring
  rw [this, D.map_add, D.map_one, add_zero]
lemma v35.map_three (D : v35 R) : D 3 = 0 := by
  have : (3 : R) = 2 + 1 := by ring
  rw [this, D.map_add, D.map_two, D.map_one, add_zero]
def v35.smul (lam : R) (D : v35 R) : v35 R where
  toFun a := lam * D a
  map_add' a b := by rw [D.map_add, mul_add]
  leibniz' a b := by rw [D.leibniz]; ring
def v08 (p : ℕ) (D : R → R) (g : Fin 6 → R) : Matrix (Fin 6) (Fin 6) R :=
  Mx.of fun i j => match i with
    | ⟨0, _⟩ => g j ^ p
    | ⟨1, _⟩ => g j
    | ⟨2, _⟩ => D (g j)
    | ⟨3, _⟩ => D (D (g j))
    | ⟨4, _⟩ => D (D (D (g j)))
    | ⟨5, _⟩ => D (D (D (D (g j))))
def fWron (p : ℕ) (D : R → R) (g : Fin 6 → R) : R :=
  (v08 p D g).det
lemma v112 (p : ℕ) (D : v35 R) (lam : R) (g : Fin 6 → R) :
    fWron p (D.smul lam) g = lam ^ 10 * fWron p D g := by
  set d1 := D lam
  set d2 := D d1
  set d3 := D d2
  let L : Matrix (Fin 6) (Fin 6) R :=
    !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, lam, 0, 0, 0; 0, 0, lam * d1, lam ^ 2, 0, 0; 0, 0, lam * d1 ^ 2 + lam ^ 2 * d2, 3 * lam ^ 2 * d1, lam ^ 3, 0; 0, 0, lam * d1 ^ 3 + 4 * lam ^ 2 * d1 * d2 + lam ^ 3 * d3, 7 * lam ^ 2 * d1 ^ 2 + 4 * lam ^ 3 * d2, 6 * lam ^ 3 * d1, lam ^ 4]
  have hLM : L * v08 p D g = v08 p (D.smul lam) g := by
    ext i j
    set a := g j
    have hlam2 : D (lam ^ 2) = 2 * lam * d1 := by rw [sq, D.leibniz]; dsimp only [d1]; ring
    have hlam3 : D (lam ^ 3) = 3 * lam ^ 2 * d1 := by
      rw [pow_succ, D.leibniz, hlam2]; dsimp only [d1]; ring
    have hd1_2 : D (d1 ^ 2) = 2 * d1 * d2 := by rw [sq, D.leibniz]; dsimp only [d2]; ring
    have hD1 : (D.smul lam) a = lam * D a := rfl
    have hD2 : (D.smul lam) ((D.smul lam) a) = lam * d1 * D a + lam ^ 2 * D (D a) := by
      change lam * D (lam * D a) = _
      rw [D.leibniz]; dsimp only [d1]; ring
    have hD3 : (D.smul lam) ((D.smul lam) ((D.smul lam) a)) = (lam * d1 ^ 2 + lam ^ 2 * d2) * D a + (3 * lam ^ 2 * d1) * D (D a) + lam ^ 3 * D (D (D a)) := by
      rw [hD2]
      change lam * D (lam * d1 * D a + lam ^ 2 * D (D a)) = _
      rw [D.map_add, D.leibniz, D.leibniz, D.leibniz, hlam2]; dsimp only [d1, d2]; ring
    have hD4 : (D.smul lam) ((D.smul lam) ((D.smul lam) ((D.smul lam) a))) = (lam * d1 ^ 3 + 4 * lam ^ 2 * d1 * d2 + lam ^ 3 * d3) * D a + (7 * lam ^ 2 * d1 ^ 2 + 4 * lam ^ 3 * d2) * D (D a) + (6 * lam ^ 3 * d1) * D (D (D a)) + lam ^ 4 * D (D (D (D a))) := by
      rw [hD3]
      change lam * D ((lam * d1 ^ 2 + lam ^ 2 * d2) * D a + (3 * lam ^ 2 * d1) * D (D a) + lam ^ 3 * D (D (D a))) = _
      simp only [D.map_add, D.leibniz, D.map_three, hlam2, hlam3, hd1_2]
      dsimp only [d1, d2, d3]; ring
    rw [Mx.mul_apply, Fi.sum_univ_six]
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [L, v08, v15]
    · simp [L, v08, v15]
    · simp only [L, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD1.symm
    · simp only [L, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD2.symm
    · simp only [L, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD3.symm
    · simp only [L, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD4.symm
  have hL_tri : L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change j > i at hij
    fin_cases i <;> fin_cases j <;> simp_all [L]
  have hL_det : L.det = lam ^ 10 := by
    rw [Mx.det_of_isLowerTriangular L hL_tri, Fi.prod_univ_six]
    simp [L]; ring
  rw [fWron, ← hLM, Mx.det_mul, hL_det, fWron]
lemma v213 (p : ℕ) (D : v35 R) (phi : R) (g : Fin 6 → R) :
    fWron p D (fun j => phi * g j) = phi ^ (p + 5) * fWron p D g := by
  set p1 := D phi
  set p2 := D p1
  set p3 := D p2
  set p4 := D p3
  let G : Matrix (Fin 6) (Fin 6) R :=
    !![phi ^ p, 0, 0, 0, 0, 0; 0, phi, 0, 0, 0, 0; 0, p1, phi, 0, 0, 0; 0, p2, 2 * p1, phi, 0, 0; 0, p3, 3 * p2, 3 * p1, phi, 0; 0, p4, 4 * p3, 6 * p2, 4 * p1, phi]
  have hGM : G * v08 p D g = v08 p D (fun j => phi * g j) := by
    ext i j
    set a := g j
    have hD1 : D (phi * a) = p1 * a + phi * D a := D.leibniz phi a
    have hD2 : D (D (phi * a)) = p2 * a + 2 * p1 * D a + phi * D (D a) := by
      rw [hD1]; simp only [D.map_add, D.leibniz]; dsimp only [p1, p2]; ring
    have hD3 : D (D (D (phi * a))) = p3 * a + 3 * p2 * D a + 3 * p1 * D (D a) + phi * D (D (D a)) := by
      rw [hD2]; simp only [D.map_add, D.leibniz, D.map_two]; dsimp only [p1, p2, p3]; ring
    have hD4 : D (D (D (D (phi * a)))) = p4 * a + 4 * p3 * D a + 6 * p2 * D (D a) + 4 * p1 * D (D (D a)) + phi * D (D (D (D a))) := by
      rw [hD3]; simp only [D.map_add, D.leibniz, D.map_three]; dsimp only [p1, p2, p3, p4]; ring
    rw [Mx.mul_apply, Fi.sum_univ_six]
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [G, v08, mul_pow, v15]
    · simp [G, v08, v15]
    · simp only [G, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD1.symm
    · simp only [G, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD2.symm
    · simp only [G, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add, add_zero]
      exact hD3.symm
    · simp only [G, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, zero_mul, zero_add]
      exact hD4.symm
  have hG_tri : G.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change j > i at hij
    fin_cases i <;> fin_cases j <;> simp_all [G]
  have hG_det : G.det = phi ^ (p + 5) := by
    rw [Mx.det_of_isLowerTriangular G hG_tri, Fi.prod_univ_six]
    simp [G]; ring
  rw [fWron, ← hGM, Mx.det_mul, hG_det, fWron]
end AbstractFrobWronsk
section ConicWronskian
variable {K : Type*} [Field K]
noncomputable def v48 : v35 (PS K) where
  toFun := psD
  map_add' := v51
  leibniz' := v29
noncomputable def v64 (n : ℕ) (g : Fin n → PS K) :
    Matrix (Fin n) (Fin n) (PS K) :=
  Mx.of fun i j => v17 (i : ℕ) (g j)
noncomputable def v86 (n : ℕ) (g : Fin n → PS K) : PS K :=
  (v64 n g).det
lemma fWron_t5_dvd {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) [CharP K p]
    (g : Fin 6 → PS K)
    (hfp : ∀ j : Fin 6, Ps.constantCoeff (g j) ^ p = Ps.constantCoeff (g j)) :
    Ps.X ^ 5 ∣ fWron p psD g := by
  have h2 : (2 : K) ≠ 0 := by
    intro h0; have := (Ch.cast_eq_zero_iff K p 2).mp h0; have := Nat.le_of_dvd (by omega) this; omega
  have h6 : (6 : K) ≠ 0 := by
    intro h0; have := (Ch.cast_eq_zero_iff K p 6).mp h0
    have : p ∣ 2 ∨ p ∣ 3 := hp.dvd_mul.mp (show p ∣ 2 * 3 from this)
    rcases this with h | h <;> { have := Nat.le_of_dvd (by omega) h; omega }
  have h24 : (24 : K) ≠ 0 := by
    intro h0; have := (Ch.cast_eq_zero_iff K p 24).mp h0
    have h46 : p ∣ 4 ∨ p ∣ 6 := hp.dvd_mul.mp (show p ∣ 4 * 6 from this)
    rcases h46 with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have : p ∣ 2 ∨ p ∣ 3 := hp.dvd_mul.mp (show p ∣ 2 * 3 from h)
      rcases this with h' | h' <;> { have := Nat.le_of_dvd (by omega) h'; omega }
  set t : PS K := Ps.X
  let U : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, -1, t, -(Ps.C (2 : K)⁻¹) * t ^ 2, Ps.C (6 : K)⁻¹ * t ^ 3, -(Ps.C (24 : K)⁻¹) * t ^ 4; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  have hU_tri : U.BlockTriangular id := by
    intro i j hij
    simp only [id_eq] at hij
    fin_cases i <;> fin_cases j <;> simp_all [U]
  have hU_det : U.det = 1 := by
    rw [Mx.det_of_isUpperTriangular hU_tri, Fi.prod_univ_six]
    simp [U]
  have hrow0 : ∀ j : Fin 6, t ^ 5 ∣ (U * v08 p psD g) 0 j := by
    intro j
    rw [Mx.mul_apply, Fi.sum_univ_six]
    simp only [U, v08, Mx.of_apply, v34, v33, v20, v19, v18, v15, one_mul, neg_mul]
    set f := g j
    have hsplit : f ^ p + -f + t * psD f + -(Ps.C (2 : K)⁻¹ * t ^ 2 * psD (psD f)) + Ps.C (6 : K)⁻¹ * t ^ 3 * psD (psD (psD f)) + -(Ps.C (24 : K)⁻¹ * t ^ 4 * psD (psD (psD (psD f)))) = (f ^ p - Ps.C (Ps.constantCoeff f ^ p)) + (Ps.C (Ps.constantCoeff f) - f + t * psD f - Ps.C (2 : K)⁻¹ * t ^ 2 * psD (psD f) + Ps.C (6 : K)⁻¹ * t ^ 3 * psD (psD (psD f)) - Ps.C (24 : K)⁻¹ * t ^ 4 * psD (psD (psD (psD f)))) := by
      rw [hfp j]; ring
    rw [hsplit]
    apply dvd_add
    · exact (pow_dvd_pow t hp5).trans (v167 hp f)
    · rw [Ps.X_pow_dvd_iff]
      intro m hm
      have hderiv_coeff : ∀ k r, Ps.coeff r (v17 k f) = (∏ i ∈ Fs.range k, ((r + i + 1 : ℕ) : K)) * Ps.coeff (r + k) f := by
        intro k
        induction k with
        | zero => intro r; simp [v17]
        | succ k ih =>
          intro r
          rw [v41, v66, ih (r + 1), Fs.prod_range_succ']
          simp only [Nat.cast_add, Nat.cast_one, add_zero]
          have h1 : r + 1 + k = r + (k + 1) := by omega
          rw [h1]
          have hprod : ∏ x ∈ Fs.range k, ((r : K) + 1 + (x : K) + 1) = ∏ x ∈ Fs.range k, ((r : K) + ((x : K) + 1) + 1) := by
            apply Fs.prod_congr rfl; intro x _; ring
          rw [hprod]; ring
      have hsub_t : ∀ (c : K) (k : ℕ) (h : PS K), Ps.coeff m (Ps.C c * t ^ k * h) = if k ≤ m then c * Ps.coeff (m - k) h else 0 := by
        intro c k h
        have : Ps.C c * t ^ k * h = t ^ k * (Ps.C c * h) := by ring
        rw [this, Ps.coeff_X_pow_mul']
        split_ifs <;> simp
      have hsub_t1 : ∀ (h : PS K), Ps.coeff m (t * h) = if 1 ≤ m then Ps.coeff (m - 1) h else 0 := by
        intro h
        have : t * h = t ^ 1 * h := by rw [pow_one]
        rw [this, Ps.coeff_X_pow_mul']
      simp only [map_add, map_sub, hsub_t, hsub_t1, Ps.coeff_C]
      have h1 : psD f = v17 1 f := rfl
      have h2' : psD (psD f) = v17 2 f := rfl
      have h3 : psD (psD (psD f)) = v17 3 f := rfl
      have h4 : psD (psD (psD (psD f))) = v17 4 f := rfl
      rw [h4, h3, h2', h1]
      interval_cases m
      · simp [Ps.coeff_zero_eq_constantCoeff]
      · simp [hderiv_coeff]
      · simp only [Nat.reduceLeDiff, ↓reduceIte, OfNat.ofNat_ne_zero, Nat.reduceSub, hderiv_coeff, Fs.prod_range_succ, Fs.prod_range_zero, one_mul, zero_add]
        push_cast
        have : (2 : K)⁻¹ * (2 * Ps.coeff 2 f) = Ps.coeff 2 f := by
          rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
        linear_combination -this
      · simp only [Nat.reduceLeDiff, ↓reduceIte, OfNat.ofNat_ne_zero, Nat.reduceSub, hderiv_coeff, Fs.prod_range_succ, Fs.prod_range_zero, one_mul, zero_add]
        push_cast
        have h2c : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
        have h6c : (6 : K)⁻¹ * 6 = 1 := inv_mul_cancel₀ h6
        have hcalc : (0 : K) - Ps.coeff 3 f + 3 * Ps.coeff 3 f - (2 : K)⁻¹ * (2 * 3 * Ps.coeff 3 f) + (6 : K)⁻¹ * (1 * 2 * 3 * Ps.coeff 3 f) - 0 = 0 := by
          linear_combination -3 * Ps.coeff 3 f * h2c + Ps.coeff 3 f * h6c
        simpa using hcalc
      · simp only [Nat.reduceLeDiff, ↓reduceIte, OfNat.ofNat_ne_zero, Nat.reduceSub, hderiv_coeff, Fs.prod_range_succ, Fs.prod_range_zero, one_mul, zero_add]
        push_cast
        have h2c : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
        have h6c : (6 : K)⁻¹ * 6 = 1 := inv_mul_cancel₀ h6
        have h24c : (24 : K)⁻¹ * 24 = 1 := inv_mul_cancel₀ h24
        have hcalc : (0 : K) - Ps.coeff 4 f + 4 * Ps.coeff 4 f - (2 : K)⁻¹ * (3 * 4 * Ps.coeff 4 f) + (6 : K)⁻¹ * (2 * 3 * 4 * Ps.coeff 4 f) - (24 : K)⁻¹ * (1 * 2 * 3 * 4 * Ps.coeff 4 f) = 0 := by
          linear_combination -6 * Ps.coeff 4 f * h2c + 4 * Ps.coeff 4 f * h6c - Ps.coeff 4 f * h24c
        simpa using hcalc
  rw [fWron, ← one_mul (v08 p psD g).det, ← hU_det, ← Mx.det_mul, Mx.det_apply]
  apply Fs.dvd_sum; intro σ _
  suffices hd : t ^ 5 ∣ ∏ i : Fin 6, (U * v08 p psD g) (σ i) i by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simpa [h] using hd
    · simpa [h] using dvd_neg.mpr hd
  rw [← Fs.mul_prod_erase Fs.univ _ (mem_univ (σ.symm 0)), Eqv.apply_symm_apply]
  exact dvd_mul_of_dvd_left (hrow0 (σ.symm 0)) _
set_option maxHeartbeats 800000 in
lemma v171 {p : ℕ} (x y d1 d2 d3 d4 : PS K)
    (hx1 : psD x = 1)
    (hy1 : psD y = d1)
    (hy2 : psD d1 = 2 * d2)
    (hy3 : psD d2 = 3 * d3)
    (hy4 : psD d3 = 4 * d4) :
    let u := x ^ p - x
    let w := (y ^ p - y) - d1 * u
    fWron p psD ![1, x, y, x ^ 2, x * y, y ^ 2] = -288 * (d2 ^ 4 * u ^ 2 - d2 ^ 3 * w + d2 ^ 2 * d3 * u * w + (d2 * d4 - d3 ^ 2) * w ^ 2) := by
  intro u w
  have hx2 : psD (1 : PS K) = 0 := v159
  have h2c : ∀ a : PS K, psD (2 * a) = 2 * psD a := by
    intro a; have : (2 : PS K) * a = a + a := by ring
    rw [this, v51]; ring
  have h3c : ∀ a : PS K, psD (3 * a) = 3 * psD a := by
    intro a; have : (3 : PS K) * a = a + (a + a) := by ring
    rw [this, v51, v51]; ring
  have h4c : ∀ a : PS K, psD (4 * a) = 4 * psD a := by
    intro a; have : (4 : PS K) * a = 2 * (2 * a) := by ring
    rw [this, h2c, h2c]; ring
  have h6c : ∀ a : PS K, psD (6 * a) = 6 * psD a := by
    intro a; have : (6 : PS K) * a = 2 * (3 * a) := by ring
    rw [this, h2c, h3c]; ring
  have h12c : ∀ a : PS K, psD (12 * a) = 12 * psD a := by
    intro a; have : (12 : PS K) * a = 3 * (4 * a) := by ring
    rw [this, h3c, h4c]; ring
  have hd_x2_1 : psD (x ^ 2) = 2 * x := by rw [sq, v29, hx1]; ring
  have hd_x2_2 : psD (2 * x) = 2 := by rw [h2c, hx1]; ring
  have hd_x2_3 : psD (2 : PS K) = 0 := by
    have : (2 : PS K) = 1 + 1 := by ring
    rw [this, v51, v159, add_zero]
  have hd_xy_1 : psD (x * y) = y + x * d1 := by rw [v29, hx1, hy1]; ring
  have hd_xy_2 : psD (y + x * d1) = 2 * d1 + 2 * x * d2 := by
    rw [v51, v29, hx1, hy1, hy2]; ring
  have hd_xy_3 : psD (2 * d1 + 2 * x * d2) = 6 * d2 + 6 * x * d3 := by
    rw [v51, h2c, hy2, mul_assoc 2 x d2, h2c, v29, hx1, hy3]; ring
  have hd_xy_4 : psD (6 * d2 + 6 * x * d3) = 24 * d3 + 24 * x * d4 := by
    rw [v51, h6c, hy3, mul_assoc 6 x d3, h6c, v29, hx1, hy4]; ring
  have hd_y2_1 : psD (y ^ 2) = 2 * y * d1 := by rw [sq, v29, hy1]; ring
  have hd_y2_2 : psD (2 * y * d1) = 2 * d1 ^ 2 + 4 * y * d2 := by
    rw [mul_assoc 2 y d1, h2c, v29, hy1, hy2]; ring
  have hd_y2_3 : psD (2 * d1 ^ 2 + 4 * y * d2) = 12 * d1 * d2 + 12 * y * d3 := by
    rw [v51, h2c, sq, v29, hy2, mul_assoc 4 y d2, h4c, v29, hy1, hy3]; ring
  have hd_y2_4 : psD (12 * d1 * d2 + 12 * y * d3) = 24 * d2 ^ 2 + 48 * d1 * d3 + 48 * y * d4 := by
    rw [v51, mul_assoc 12 d1 d2, h12c, v29, hy2, hy3, mul_assoc 12 y d3, h12c, v29, hy1, hy4]; ring
  have hy_d2 : psD (2 * d2) = 6 * d3 := by rw [h2c, hy3]; ring
  have hy_d3 : psD (6 * d3) = 24 * d4 := by rw [h6c, hy4]; ring
  let U : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, -x, -y, x ^ 2, x * y, y ^ 2; 0,  1,  0, -2 * x, -y, 0; 0,  0,  1, 0, -x, -2 * y; 0,  0,  0, 1, 0, 0; 0,  0,  0, 0, 1, 0; 0,  0,  0, 0, 0, 1]
  let V : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, 0, 0, 0, 0, 0; 0, 1, -d1, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, -d1, d1 ^ 2; 0, 0, 0, 0, 1, -2 * d1; 0, 0, 0, 0, 0, 1]
  have hU_det : U.det = 1 := by
    have htri : U.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      fin_cases i <;> fin_cases j <;> simp_all [U]
    rw [Mx.det_of_isUpperTriangular htri, Fi.prod_univ_six]; simp [U]
  have hV_det : V.det = 1 := by
    have htri : V.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      fin_cases i <;> fin_cases j <;> simp_all [V]
    rw [Mx.det_of_isUpperTriangular htri, Fi.prod_univ_six]; simp [V]
  let P : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  have hP_det : P.det = 1 := by
    let σ : Eqv.Perm (Fin 6) := Eqv.swap (0 : Fin 6) 1 * Eqv.swap 1 2
    have hσ : ∀ i : Fin 6, σ i = ![1, 2, 0, 3, 4, 5] i := by decide
    have hP_eq : P = (1 : Matrix (Fin 6) (Fin 6) (PS K)).submatrix σ id := by
      refine Mx.ext fun i j => ?_
      rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [P, hσ, Mx.one_apply, v20, v19, v18, v15]
    rw [hP_eq, Mx.det_permute, Mx.det_one, mul_one]
    have hsign : Equiv.Perm.sign σ = 1 := by decide
    simp [hsign]
  let B : Matrix (Fin 4) (Fin 4) (PS K) :=
    !![w, u ^ 2, u * w, w ^ 2; 2 * d2, 2, 0, 0; 6 * d3, 0, 6 * d2, 0; 24 * d4, 0, 24 * d3, 24 * d2 ^ 2]
  let Rmat : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, u, w, u ^ 2, u * w, w ^ 2; 0, 0, 2 * d2, 2, 0, 0; 0, 0, 6 * d3, 0, 6 * d2, 0; 0, 0, 24 * d4, 0, 24 * d3, 24 * d2 ^ 2]
  have hxp : x ^ p = x + u := by dsimp only [u]; ring
  have hyp : y ^ p = y + d1 * u + w := by dsimp only [w]; ring
  have hPMUV : P * v08 p psD ![1, x, y, x ^ 2, x * y, y ^ 2] * U * V = Rmat := by
    refine Mx.ext fun i j => ?_
    simp only [Mx.mul_apply, Fi.sum_univ_six]
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [P, U, V, Rmat, v08, v15, hx1, hx2, hy1, hy2, hy_d2, hy_d3, hd_x2_1, hd_x2_2, hd_x2_3, hd_xy_1, hd_xy_2, hd_xy_3, hd_xy_4, hd_y2_1, hd_y2_2, hd_y2_3, hd_y2_4, v104, mul_pow, pow_right_comm, hxp, hyp] <;>
      ring
  have hR_det : Rmat.det = B.det := by
    let e : Fin 2 ⊕ Fin 4 ≃ Fin 6 := finSumFinEquiv
    have hre : Rmat.submatrix e e = Mx.fromBlocks (1 : Matrix (Fin 2) (Fin 2) (PS K)) 0
        !![1, u; 0, 0; 0, 0; 0, 0] B := by
      refine Mx.ext fun r c => ?_
      rcases r with r | r <;> rcases c with c | c
      · fin_cases r <;> fin_cases c <;> simp [e, Rmat, finSumFinEquiv]
      · fin_cases r <;> fin_cases c <;> simp [e, Rmat, finSumFinEquiv]
      · fin_cases r <;> fin_cases c <;> simp [e, Rmat, finSumFinEquiv]
      · fin_cases r <;> fin_cases c <;> simp [e, Rmat, B, finSumFinEquiv]
    have hdet1 : (Rmat.submatrix e e).det = Rmat.det := by
      have : Mx.reindex e.symm e.symm Rmat = Rmat.submatrix e e := rfl
      rw [← this, Mx.det_reindex_self]
    rw [← hdet1, hre, Mx.det_fromBlocks_zero₁₂, Mx.det_one, one_mul]
  have hB_det : B.det = -288 * (d2 ^ 4 * u ^ 2 - d2 ^ 3 * w + d2 ^ 2 * d3 * u * w + (d2 * d4 - d3 ^ 2) * w ^ 2) := by
    rw [Mx.det_succ_row_zero]
    simp only [Fi.sum_univ_four, Fi.isValue, Mx.det_fin_three]
    simp [B, Mx.submatrix, Fi.succAbove]
    ring
  have htot := congr_arg Mx.det hPMUV
  rw [Mx.det_mul, Mx.det_mul, Mx.det_mul, hP_det, hU_det, hV_det, one_mul, mul_one, mul_one] at htot
  rw [fWron, htot, hR_det, hB_det]
lemma v188 {p : ℕ} [CharP K p]
    (x y d1 d2 d3 d4 d5 : PS K)
    (hx1 : psD x = 1)
    (hy1 : psD y = d1)
    (hy2 : psD d1 = 2 * d2)
    (hy3 : psD d2 = 3 * d3)
    (hy4 : psD d3 = 4 * d4)
    (hy5 : psD d4 = 5 * d5) :
    let u := x ^ p - x
    let w := (y ^ p - y) - d1 * u
    let WF := d2 ^ 4 * u ^ 2 - d2 ^ 3 * w + d2 ^ 2 * d3 * u * w + (d2 * d4 - d3 ^ 2) * w ^ 2
    let WC := d2 * (d2 ^ 2 * d5 - 3 * d2 * d3 * d4 + 2 * d3 ^ 3)
    d2 ^ 2 * psD WF - 10 * d2 * d3 * WF = 5 * WC * w ^ 2 := by
  intro u w WF WC
  have hu : psD u = -1 := by
    dsimp only [u]; rw [v148, v197, hx1]; ring
  have hw : psD w = -2 * d2 * u := by
    dsimp only [w]
    rw [v148, v148, v197, hy1, v29, hy2, hu]; ring
  dsimp only [WF, WC]
  simp only [v51, v148, v29, psD_pow, hu, hw, hy3, hy4, hy5]
  push_cast
  ring
set_option maxHeartbeats 800000 in
lemma v129 (x y d1 d2 d3 d4 d5 : PS K)
    (hx1 : psD x = 1)
    (hy1 : psD y = d1)
    (hy2 : psD d1 = 2 * d2)
    (hy3 : psD d2 = 3 * d3)
    (hy4 : psD d3 = 4 * d4)
    (hy5 : psD d4 = 5 * d5) :
    v86 6 ![1, x, y, x ^ 2, x * y, y ^ 2] = -34560 * (d2 * (d2 ^ 2 * d5 - 3 * d2 * d3 * d4 + 2 * d3 ^ 3)) := by
  have hx2 : psD (1 : PS K) = 0 := v159
  have hd_x2_1 : psD (x ^ 2) = 2 * x := by rw [sq, v29, hx1]; ring
  have hd_x2_2 : psD (2 * x) = 2 := by rw [v11, hx1, mul_one]
  have hd_x2_3 : psD (2 : PS K) = 0 := v209 2
  have hd_xy_1 : psD (x * y) = y + x * d1 := by rw [v29, hx1, hy1]; ring
  have hd_xy_2 : psD (y + x * d1) = 2 * d1 + 2 * x * d2 := by
    rw [v51, v29, hx1, hy1, hy2]; ring
  have hd_xy_3 : psD (2 * d1 + 2 * x * d2) = 6 * d2 + 6 * x * d3 := by
    rw [v51, v11, hy2, mul_assoc 2 x d2, v11, v29, hx1, hy3]; ring
  have hd_xy_4 : psD (6 * d2 + 6 * x * d3) = 24 * d3 + 24 * x * d4 := by
    rw [v51, v11, hy3, mul_assoc 6 x d3, v11, v29, hx1, hy4]; ring
  have hd_xy_5 : psD (24 * d3 + 24 * x * d4) = 120 * d4 + 120 * x * d5 := by
    rw [v51, v11, hy4, mul_assoc 24 x d4, v11, v29, hx1, hy5]; ring
  have hd_y2_1 : psD (y ^ 2) = 2 * y * d1 := by rw [sq, v29, hy1]; ring
  have hd_y2_2 : psD (2 * y * d1) = 2 * d1 ^ 2 + 4 * y * d2 := by
    rw [mul_assoc 2 y d1, v11, v29, hy1, hy2]; ring
  have hd_y2_3 : psD (2 * d1 ^ 2 + 4 * y * d2) = 12 * d1 * d2 + 12 * y * d3 := by
    rw [v51, v11, sq, v29, hy2, mul_assoc 4 y d2, v11, v29, hy1, hy3]; ring
  have hd_y2_4 : psD (12 * d1 * d2 + 12 * y * d3) = 24 * d2 ^ 2 + 48 * d1 * d3 + 48 * y * d4 := by
    rw [v51, mul_assoc 12 d1 d2, v11, v29, hy2, hy3, mul_assoc 12 y d3, v11, v29, hy1, hy4]; ring
  have hd_y2_5 : psD (24 * d2 ^ 2 + 48 * d1 * d3 + 48 * y * d4) = 240 * d2 * d3 + 240 * d1 * d4 + 240 * y * d5 := by
    rw [v51, v51, v11, sq, v29, hy3, mul_assoc 48 d1 d3, v11, v29, hy2, hy4, mul_assoc 48 y d4, v11, v29, hy1, hy5]; ring
  have hy_d2 : psD (2 * d2) = 6 * d3 := by rw [v11, hy3]; ring
  have hy_d3 : psD (6 * d3) = 24 * d4 := by rw [v11, hy4]; ring
  have hy_d4 : psD (24 * d4) = 120 * d5 := by rw [v11, hy5]; ring
  let U : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, -x, -y, x ^ 2, x * y, y ^ 2; 0,  1,  0, -2 * x, -y, 0; 0,  0,  1, 0, -x, -2 * y; 0,  0,  0, 1, 0, 0; 0,  0,  0, 0, 1, 0; 0,  0,  0, 0, 0, 1]
  let V : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, 0, 0, 0, 0, 0; 0, 1, -d1, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, -d1, d1 ^ 2; 0, 0, 0, 0, 1, -2 * d1; 0, 0, 0, 0, 0, 1]
  have hU_det : U.det = 1 := by
    have htri : U.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      fin_cases i <;> fin_cases j <;> simp_all [U]
    rw [Mx.det_of_isUpperTriangular htri, Fi.prod_univ_six]; simp [U]
  have hV_det : V.det = 1 := by
    have htri : V.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      fin_cases i <;> fin_cases j <;> simp_all [V]
    rw [Mx.det_of_isUpperTriangular htri, Fi.prod_univ_six]; simp [V]
  let B : Matrix (Fin 4) (Fin 4) (PS K) :=
    !![2 * d2, 2, 0, 0; 6 * d3, 0, 6 * d2, 0; 24 * d4, 0, 24 * d3, 24 * d2 ^ 2; 120 * d5, 0, 120 * d4, 240 * d2 * d3]
  let Rmat : Matrix (Fin 6) (Fin 6) (PS K) :=
    !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 2 * d2, 2, 0, 0; 0, 0, 6 * d3, 0, 6 * d2, 0; 0, 0, 24 * d4, 0, 24 * d3, 24 * d2 ^ 2; 0, 0, 120 * d5, 0, 120 * d4, 240 * d2 * d3]
  have hMUV : v64 6 ![1, x, y, x ^ 2, x * y, y ^ 2] * U * V = Rmat := by
    refine Mx.ext fun i j => ?_
    simp only [Mx.mul_apply, Fi.sum_univ_six]
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [U, V, Rmat, v64, v17, v15, hx1, hx2, hy1, hy2, hy_d2, hy_d3, hy_d4, hd_x2_1, hd_x2_2, hd_x2_3, hd_xy_1, hd_xy_2, hd_xy_3, hd_xy_4, hd_xy_5, hd_y2_1, hd_y2_2, hd_y2_3, hd_y2_4, hd_y2_5, v104] <;> ring
  have hR_det : Rmat.det = B.det := by
    let e : Fin 2 ⊕ Fin 4 ≃ Fin 6 := finSumFinEquiv
    have hre : Rmat.submatrix e e = Mx.fromBlocks (1 : Matrix (Fin 2) (Fin 2) (PS K)) 0 0 B := by
      refine Mx.ext fun r c => ?_
      rcases r with r | r <;> rcases c with c | c <;>
        fin_cases r <;> fin_cases c <;> simp [e, Rmat, B, finSumFinEquiv]
    have hdet1 : (Rmat.submatrix e e).det = Rmat.det := by
      have : Mx.reindex e.symm e.symm Rmat = Rmat.submatrix e e := rfl
      rw [← this, Mx.det_reindex_self]
    rw [← hdet1, hre, Mx.det_fromBlocks_zero₁₂, Mx.det_one, one_mul]
  have hB_det : B.det = -34560 * (d2 * (d2 ^ 2 * d5 - 3 * d2 * d3 * d4 + 2 * d3 ^ 3)) := by
    rw [Mx.det_succ_row_zero]
    simp only [Fi.sum_univ_four, Fi.isValue, Mx.det_fin_three]
    simp [B, Mx.submatrix, Fi.succAbove]
    ring
  have htot := congr_arg Mx.det hMUV
  rw [Mx.det_mul, Mx.det_mul, hU_det, hV_det, mul_one, mul_one] at htot
  rw [v86, htot, hR_det, hB_det]
lemma v144 (x y d1 d2 d3 d4 : PS K)
    (hx0 : Ps.constantCoeff x = 0)
    (hy0 : Ps.constantCoeff y = 0)
    (hd10 : Ps.constantCoeff d1 = 0)
    (hx1 : psD x = 1)
    (hy1 : psD y = d1)
    (hy2 : psD d1 = 2 * d2)
    (hy3 : psD d2 = 3 * d3)
    (hy4 : psD d3 = 4 * d4) :
    Ps.constantCoeff (v86 5 ![1, x, x ^ 2, x * y, y ^ 2]) = 288 * Ps.constantCoeff d2 ^ 3 := by
  have hx2 : psD (1 : PS K) = 0 := v159
  have hd_x2_1 : psD (x ^ 2) = 2 * x := by rw [sq, v29, hx1]; ring
  have hd_x2_2 : psD (2 * x) = 2 := by rw [v11, hx1, mul_one]
  have hd_x2_3 : psD (2 : PS K) = 0 := v209 2
  have hd_xy_1 : psD (x * y) = y + x * d1 := by rw [v29, hx1, hy1]; ring
  have hd_xy_2 : psD (y + x * d1) = 2 * d1 + 2 * x * d2 := by
    rw [v51, v29, hx1, hy1, hy2]; ring
  have hd_xy_3 : psD (2 * d1 + 2 * x * d2) = 6 * d2 + 6 * x * d3 := by
    rw [v51, v11, hy2, mul_assoc 2 x d2, v11, v29, hx1, hy3]; ring
  have hd_xy_4 : psD (6 * d2 + 6 * x * d3) = 24 * d3 + 24 * x * d4 := by
    rw [v51, v11, hy3, mul_assoc 6 x d3, v11, v29, hx1, hy4]; ring
  have hd_y2_1 : psD (y ^ 2) = 2 * y * d1 := by rw [sq, v29, hy1]; ring
  have hd_y2_2 : psD (2 * y * d1) = 2 * d1 ^ 2 + 4 * y * d2 := by
    rw [mul_assoc 2 y d1, v11, v29, hy1, hy2]; ring
  have hd_y2_3 : psD (2 * d1 ^ 2 + 4 * y * d2) = 12 * d1 * d2 + 12 * y * d3 := by
    rw [v51, v11, sq, v29, hy2, mul_assoc 4 y d2, v11, v29, hy1, hy3]; ring
  have hd_y2_4 : psD (12 * d1 * d2 + 12 * y * d3) = 24 * d2 ^ 2 + 48 * d1 * d3 + 48 * y * d4 := by
    rw [v51, mul_assoc 12 d1 d2, v11, v29, hy2, hy3, mul_assoc 12 y d3, v11, v29, hy1, hy4]; ring
  rw [v86, Rh.map_det]
  let L : Matrix (Fin 5) (Fin 5) K :=
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 6 * Ps.constantCoeff d2, 0; 0, 0, 0, 24 * Ps.constantCoeff d3, 24 * Ps.constantCoeff d2 ^ 2]
  have hmat : Ps.constantCoeff.mapMatrix (v64 5 ![1, x, x ^ 2, x * y, y ^ 2]) = L := by
    refine Mx.ext fun i j => ?_
    rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp [L, v64, v17, hx0, hy0, hd10, hx1, hx2, map_ofNat, hd_x2_1, hd_x2_2, hd_x2_3, hd_xy_1, hd_xy_2, hd_xy_3, hd_xy_4, hd_y2_1, hd_y2_2, hd_y2_3, hd_y2_4, v104]
  have hL_tri : L.BlockTriangular OrderDual.toDual := by
    intro i j hij; change j > i at hij
    fin_cases i <;> fin_cases j <;> simp_all [L]
  rw [hmat, Mx.det_of_isLowerTriangular L hL_tri, Fi.prod_univ_five]
  simp [L]; ring
lemma v195 (g : Fin 5 → PS K) (h : PS K)
    (hw5 : Ps.constantCoeff (v86 5 g) ≠ 0)
    (hw6 : v86 6 (Fi.snoc g h) = 0) :
    ∃ c : Fin 5 → PS K, (∀ i : Fin 5, psD (c i) = 0) ∧ h = ∑ i : Fin 5, c i * g i := by
  let M : Matrix (Fin 5) (Fin 5) (PS K) := v64 5 g
  have hdet_unit : IsUnit M.det := Ps.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hw5)
  obtain ⟨u, hu⟩ := hdet_unit
  let invDet : PS K := ↑u⁻¹
  have hinv_mul : invDet * M.det = 1 := by
    dsimp only [invDet]; rw [← hu]; exact Units.inv_mul u
  let rhs : Fin 5 → PS K := fun k => v17 (k : ℕ) h
  let c : Fin 5 → PS K := fun i => invDet * (M.adjugate.mulVec rhs i)
  have hMc : M.mulVec c = rhs := by
    have h1 : M.mulVec c = invDet • (M.mulVec (M.adjugate.mulVec rhs)) := by
      funext k
      simp only [Mx.mulVec, dotProduct, c, Pi.smul_apply, smul_eq_mul, mul_sum]
      apply sum_congr rfl; intro i _; ring
    rw [h1, Mx.mulVec_mulVec, Mx.mul_adjugate]
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, Mx.smul_mulVec, Mx.one_mulVec]
    rw [← mul_assoc, hinv_mul, one_mul]
  have heq : ∀ k : Fin 5, ∑ i : Fin 5, v17 (k : ℕ) (g i) * c i = v17 (k : ℕ) h := by
    intro k
    have := congr_fun hMc k
    simpa [Mx.mulVec, dotProduct, M, v64, rhs] using this
  have heq5 : ∑ i : Fin 5, v17 5 (g i) * c i = v17 5 h := by
    let U : Matrix (Fin 6) (Fin 6) (PS K) :=
      Mx.of fun i j =>
        if j = 5 then (if h5 : (i : ℕ) < 5 then -c ⟨i, h5⟩ else 1)
        else if i = j then 1 else 0
    have hU_tri : U.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      simp only [U, Mx.of_apply]
      have hj5 : j ≠ 5 := by
        intro h5; subst h5
        have := i.isLt; omega
      rw [if_neg hj5, if_neg (fun h => by subst h; exact lt_irrefl _ hij)]
    have hU_det : U.det = 1 := by
      rw [Mx.det_of_isUpperTriangular hU_tri]
      apply Fs.prod_eq_one; intro i _
      simp only [U, Mx.of_apply]
      by_cases hi5 : i = 5
      · subst hi5; simp
      · rw [if_neg hi5]; simp
    let N := v64 6 (Fi.snoc g h) * U
    have hN_det : N.det = 0 := by
      rw [Mx.det_mul, hU_det, mul_one]; exact hw6
    have hN_col5 : ∀ r : Fin 6, N r 5 = if r = 5 then v17 5 h - ∑ i : Fin 5, v17 5 (g i) * c i else 0 := by
      intro r
      dsimp only [N]
      rw [Mx.mul_apply, Fi.sum_univ_castSucc]
      simp only [U, Mx.of_apply, ↓reduceIte]
      have hcast : ∀ i : Fin 5, ((i.castSucc : Fin 6) : ℕ) < 5 := fun i => i.isLt
      simp only [hcast, ↓reduceDIte]
      have hlast : ¬ ((Fi.last 5 : Fin 6) : ℕ) < 5 := by decide
      rw [dif_neg hlast, mul_one]
      have hsnoc_g : ∀ i : Fin 5, Fi.snoc (α := fun _ => PS K) g h i.castSucc = g i :=
        fun i => @Fi.snoc_castSucc 5 (fun _ => PS K) h g i
      have hsnoc_h : Fi.snoc (α := fun _ => PS K) g h (Fi.last 5) = h :=
        @Fi.snoc_last 5 (fun _ => PS K) h g
      simp only [v64, Mx.of_apply, hsnoc_g, hsnoc_h, Fi.val_castSucc, Fi.eta]
      have hsum_neg : (∑ x : Fin 5, v17 (r : ℕ) (g x) * -c x) = -(∑ x : Fin 5, v17 (r : ℕ) (g x) * c x) := by
        rw [← Fs.sum_neg_distrib]; apply sum_congr rfl; intro x _; ring
      rw [hsum_neg, neg_add_eq_sub]
      by_cases hr5 : r = 5
      · subst hr5; rw [if_pos rfl]; rfl
      · rw [if_neg hr5]
        have hrlt : (r : ℕ) < 5 := by
          have := r.isLt
          have : (r : ℕ) ≠ 5 := fun h' => hr5 (Fi.ext h')
          omega
        have := heq ⟨r, hrlt⟩
        dsimp only at this
        rw [this, sub_self]
    let e : Fin 5 ⊕ Fin 1 ≃ Fin 6 := finSumFinEquiv
    have he_inl : ∀ i : Fin 5, e (Sum.inl i) = i.castSucc := fun i => by
      ext; simp [e, finSumFinEquiv]
    have he_inr : ∀ i : Fin 1, e (Sum.inr i) = 5 := fun i => by
      fin_cases i; ext; simp [e, finSumFinEquiv]
    have hN_blk : N.submatrix e e = Mx.fromBlocks M 0
          (Mx.of fun _ j => v17 5 (g j))
          (Mx.of fun _ _ => v17 5 h - ∑ i : Fin 5, v17 5 (g i) * c i) := by
      refine Mx.ext fun r c' => ?_
      rcases r with r | r <;> rcases c' with c' | c'
      · simp only [Mx.submatrix_apply, Mx.fromBlocks_apply₁₁, he_inl]
        simp only [N, Mx.mul_apply, U, Mx.of_apply]
        have hc5 : c'.castSucc ≠ 5 := by
          intro h5; have := congr_arg Fi.val h5; simp at this; omega
        rw [sum_eq_single c'.castSucc]
        · rw [if_neg hc5, if_pos rfl, mul_one]
          simp [v64, M, Fi.snoc_castSucc]
        · intro k _ hkc
          rw [if_neg hc5, if_neg hkc, mul_zero]
        · intro h'; exact absurd (mem_univ _) h'
      · simp only [Mx.submatrix_apply, Mx.fromBlocks_apply₁₂, Mx.zero_apply, he_inl, he_inr]
        have hr5 : r.castSucc ≠ 5 := by
          intro h5; have := congr_arg Fi.val h5; simp at this; omega
        rw [hN_col5, if_neg hr5]
      · simp only [Mx.submatrix_apply, Mx.fromBlocks_apply₂₁, Mx.of_apply, he_inl, he_inr]
        simp only [N, Mx.mul_apply, U, Mx.of_apply]
        have hc5 : c'.castSucc ≠ 5 := by
          intro h5; have := congr_arg Fi.val h5; simp at this; omega
        rw [sum_eq_single c'.castSucc]
        · rw [if_neg hc5, if_pos rfl, mul_one]
          simp [v64, Fi.snoc_castSucc]
        · intro k _ hkc
          rw [if_neg hc5, if_neg hkc, mul_zero]
        · intro h'; exact absurd (mem_univ _) h'
      · simp only [Mx.submatrix_apply, Mx.fromBlocks_apply₂₂, Mx.of_apply, he_inr]
        rw [hN_col5, if_pos rfl]
    have hdet_N : N.det = M.det * (v17 5 h - ∑ i : Fin 5, v17 5 (g i) * c i) := by
      have hre : Mx.reindex e.symm e.symm N = N.submatrix e e := rfl
      rw [← Mx.det_reindex_self e.symm N, hre, hN_blk, Mx.det_fromBlocks_zero₁₂]
      congr 1
      rw [Mx.det_unique]
      rfl
    rw [hdet_N] at hN_det
    have hdiff0 : v17 5 h - ∑ i : Fin 5, v17 5 (g i) * c i = 0 := by
      have := congr_arg (invDet * ·) hN_det
      rw [← mul_assoc, hinv_mul, one_mul, mul_zero] at this
      exact this
    exact (sub_eq_zero.mp hdiff0).symm
  have hMdc : M.mulVec (fun i => psD (c i)) = 0 := by
    funext k
    simp only [Mx.mulVec, dotProduct, M, v64, Mx.of_apply, Pi.zero_apply]
    have hdiff := congr_arg psD (heq k)
    have hsum_d : psD (∑ i : Fin 5, v17 (k : ℕ) (g i) * c i) = (∑ i : Fin 5, v17 ((k : ℕ) + 1) (g i) * c i) + (∑ i : Fin 5, v17 (k : ℕ) (g i) * psD (c i)) := by
      have hps_sum : ∀ (s : Finset (Fin 5)) (F : Fin 5 → PS K), psD (∑ i ∈ s, F i) = ∑ i ∈ s, psD (F i) := by
        intro s F
        induction s using Fs.induction_on with
        | empty => simp [v104]
        | insert a s ha ih => rw [Fs.sum_insert ha, Fs.sum_insert ha, v51, ih]
      rw [hps_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro i _
      rw [v29, v41]
    rw [hsum_d, ← v41] at hdiff
    have hnext : ∑ i : Fin 5, v17 ((k : ℕ) + 1) (g i) * c i = v17 ((k : ℕ) + 1) h := by
      by_cases hk4 : (k : ℕ) + 1 < 5
      · exact heq ⟨(k : ℕ) + 1, hk4⟩
      · have hk_eq : (k : ℕ) + 1 = 5 := by have := k.isLt; omega
        rw [hk_eq]; exact heq5
    rw [hnext] at hdiff
    exact add_left_cancel (hdiff.trans (add_zero _).symm)
  have hdc : ∀ i : Fin 5, psD (c i) = 0 := by
    intro i
    have h1 := congr_arg (fun v => invDet * (M.adjugate.mulVec v i)) hMdc
    simp only [Mx.mulVec_zero, Pi.zero_apply, mul_zero] at h1
    rw [Mx.mulVec_mulVec, Mx.adjugate_mul, Mx.smul_mulVec, Mx.one_mulVec, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hinv_mul, one_mul] at h1
    exact h1
  refine ⟨c, hdc, ?_⟩
  have h0 := heq 0
  simp only [Fi.val_zero, v212] at h0
  rw [← h0]
  apply sum_congr rfl; intro i _; ring
end ConicWronskian
section NonVanishing
variable {K : Type*} [Field K]
lemma pderiv_comm_3 (i j : Fin 3) (P : Mv3 K) :
    Mv.pderiv i (Mv.pderiv j P) = Mv.pderiv j (Mv.pderiv i P) := by
  induction P using Mv.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [Dr.leibniz, map_add, smul_eq_mul, Mv.pderiv_X, hp]
    by_cases hjk : j = k <;> by_cases hik : i = k <;> simp [hjk, hik] <;> ring
noncomputable def cMon : Fin 6 → Mv3 K :=
  ![Mv.X 2 ^ 2, Mv.X 0 * Mv.X 2, Mv.X 1 * Mv.X 2, Mv.X 0 ^ 2, Mv.X 0 * Mv.X 1, Mv.X 1 ^ 2]
noncomputable def derivZ (F : Mv3 K) : v35 (Mv3 K) where
  toFun P := Mv.pderiv 1 F * Mv.pderiv 0 P - Mv.pderiv 0 F * Mv.pderiv 1 P
  map_add' P Q := by simp only [map_add]; ring
  leibniz' P Q := by simp only [Dr.leibniz, smul_eq_mul]; ring
noncomputable def derivX (F : Mv3 K) : v35 (Mv3 K) where
  toFun P := Mv.pderiv 2 F * Mv.pderiv 1 P - Mv.pderiv 1 F * Mv.pderiv 2 P
  map_add' P Q := by simp only [map_add]; ring
  leibniz' P Q := by simp only [Dr.leibniz, smul_eq_mul]; ring
noncomputable def derivY (F : Mv3 K) : v35 (Mv3 K) where
  toFun P := Mv.pderiv 0 F * Mv.pderiv 2 P - Mv.pderiv 2 F * Mv.pderiv 0 P
  map_add' P Q := by simp only [map_add]; ring
  leibniz' P Q := by simp only [Dr.leibniz, smul_eq_mul]; ring
noncomputable def v111 (F : Mv3 K) : Mv3 K :=
  Mv.pderiv 1 F ^ 2 * Mv.pderiv 0 (Mv.pderiv 0 F) -
  2 * Mv.pderiv 0 F * Mv.pderiv 1 F * Mv.pderiv 0 (Mv.pderiv 1 F) +
  Mv.pderiv 0 F ^ 2 * Mv.pderiv 1 (Mv.pderiv 1 F)
noncomputable def evBr (x₀ : K) (Y : PS K) :
    Mv3 K →+* PS K :=
  (Mv.aeval ![Ps.C x₀ + Ps.X, Y, (1 : PS K)]).toRingHom
lemma v62 (x₀ : K) (Y : PS K) (P : Mv3 K) :
    evBr x₀ Y P = ((dhZ P).map (v16 x₀)).eval Y := by
  induction P using Mv.induction_on with
  | C a => simp [evBr, dhZ, v16]
  | add p q hp hq => rw [map_add, dhZ_add, Pl.map_add, Pl.eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hp, v126, Pl.map_mul, Pl.eval_mul]
    congr 1
    fin_cases i <;> simp [evBr, dhZ, v16]
lemma v183 (P : Mv3 K) :
    dhZ (Mv.pderiv 1 P) = (dhZ P).derivative := by
  induction P using Mv.induction_on with
  | C a => simp [dhZ]
  | add p q hp hq => rw [map_add, dhZ_add, dhZ_add, Pl.derivative_add, hp, hq]
  | mul_X p i hp =>
    rw [Dr.leibniz, smul_eq_mul, smul_eq_mul, dhZ_add, v126, v126, v126, Pl.derivative_mul, hp]
    fin_cases i <;> simp [dhZ, Mv.pderiv_X] <;> ring
lemma v178 (x₀ : K) (Y : PS K) (P : Mv3 K) :
    psD (evBr x₀ Y P) = evBr x₀ Y (Mv.pderiv 0 P) + evBr x₀ Y (Mv.pderiv 1 P) * psD Y := by
  induction P using Mv.induction_on with
  | C a =>
    simp [evBr, psD_C]
  | add p q hp hq =>
    simp only [map_add, v51, hp, hq]; ring
  | mul_X p i hp =>
    rw [map_mul, v29, hp, Dr.leibniz, Dr.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    simp only [map_add, map_mul]
    fin_cases i <;> dsimp only
    · have hx : psD (evBr x₀ Y (Mv.X 0)) = 1 := by
        simp [evBr, v51, psD_C, psD_X]
      change _ = _
      rw [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl, hx, Mv.pderiv_X_self, Mv.pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1)]
      simp; ring
    · have hy : psD (evBr x₀ Y (Mv.X 1)) = psD Y := by
        simp [evBr]
      rw [show (⟨1, by decide⟩ : Fin 3) = 1 from rfl, hy, Mv.pderiv_X_self, Mv.pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0)]
      simp; ring
    · have hz : psD (evBr x₀ Y (Mv.X 2)) = 0 := by
        simp [evBr, v159]
      rw [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl, hz, Mv.pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), Mv.pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
      simp; ring
lemma v182 {F : Mv3 K} {x₀ : K} {Y : PS K}
    (hF0 : evBr x₀ Y F = 0) (P : Mv3 K) :
    evBr x₀ Y (derivZ F P) = evBr x₀ Y (Mv.pderiv 1 F) * psD (evBr x₀ Y P) := by
  have hdiff : evBr x₀ Y (Mv.pderiv 0 F) + evBr x₀ Y (Mv.pderiv 1 F) * psD Y = 0 := by
    rw [← v178, hF0, v104]
  have hFx : evBr x₀ Y (Mv.pderiv 0 F) = -(evBr x₀ Y (Mv.pderiv 1 F) * psD Y) := eq_neg_of_add_eq_zero_left hdiff
  simp only [derivZ, map_sub, map_mul, v178, hFx]
  ring
lemma v140 {p : ℕ} {F : Mv3 K} {x₀ : K} {Y : PS K}
    (hF0 : evBr x₀ Y F = 0) (g : Fin 6 → Mv3 K) :
    evBr x₀ Y (fWron p (derivZ F) g) = evBr x₀ Y (Mv.pderiv 1 F) ^ 10 * fWron p psD (fun j => evBr x₀ Y (g j)) := by
  set lam := evBr x₀ Y (Mv.pderiv 1 F)
  have hstep : ∀ P : Mv3 K, evBr x₀ Y (derivZ F P) = (v48.smul lam) (evBr x₀ Y P) :=
    fun P => v182 hF0 P
  rw [fWron, Rh.map_det]
  have hmat : (evBr x₀ Y).mapMatrix (v08 p (derivZ F) g) = v08 p (v48.smul lam) (fun j => evBr x₀ Y (g j)) := by
    ext i j
    fin_cases i <;> simp [v08, hstep, map_pow]
  rw [hmat]
  exact v112 p v48 lam (fun j => evBr x₀ Y (g j))
lemma v161 {F : Mv3 K} {x₀ : K} {Y : PS K}
    (hF0 : evBr x₀ Y F = 0) :
    evBr x₀ Y (v111 F) + evBr x₀ Y (Mv.pderiv 1 F) ^ 3 * psD (psD Y) = 0 := by
  have hdiff1 : evBr x₀ Y (Mv.pderiv 0 F) + evBr x₀ Y (Mv.pderiv 1 F) * psD Y = 0 := by
    rw [← v178, hF0, v104]
  have hdiff2 := congr_arg psD hdiff1
  rw [v51, v29, v178, v178, v104] at hdiff2
  have hcomm : Mv.pderiv 1 (Mv.pderiv 0 F) = Mv.pderiv 0 (Mv.pderiv 1 F) :=
    pderiv_comm_3 1 0 F
  rw [hcomm] at hdiff2
  have hFx : evBr x₀ Y (Mv.pderiv 0 F) = -(evBr x₀ Y (Mv.pderiv 1 F) * psD Y) := eq_neg_of_add_eq_zero_left hdiff1
  simp only [v111, map_add, map_sub, map_mul, map_pow, map_ofNat, hFx]
  linear_combination evBr x₀ Y (Mv.pderiv 1 F) ^ 2 * hdiff2
lemma v82 {L : Type*} [Field L] [IsAlgClosed L]
    {f g : Pol (Pol L)} (hf : f.Monic) (hf_irr : Irreducible f)
    (hd : 1 ≤ f.natDegree) (hndvd : ¬ f ∣ g) :
    ∃ x₀ y₀ : L, (f.map (Pl.evalRingHom x₀)).eval y₀ = 0 ∧ (g.map (Pl.evalRingHom x₀)).eval y₀ ≠ 0 := by
  classical
  have hnorm_ne : pNorm f g ≠ 0 := v83 hf hf_irr hndvd
  have hex_x : ∃ x₀ : L, (pNorm f g).eval x₀ ≠ 0 := by
    by_contra hall; push Not at hall
    have hinf : (Set.univ : Set L).Infinite := Set.infinite_univ
    have hsub : Set.univ ⊆ ((pNorm f g).roots.toFinset : Set L) := by
      intro x _
      rw [Fs.mem_coe, Mu.mem_toFinset, Pl.mem_roots hnorm_ne]
      exact hall x
    exact hinf ((pNorm f g).roots.toFinset.finite_toSet.subset hsub)
  rcases hex_x with ⟨x₀, hx₀⟩
  have hfx_mon : (f.map (Pl.evalRingHom x₀)).Monic := hf.map _
  have hfx_deg : (f.map (Pl.evalRingHom x₀)).natDegree = f.natDegree := hf.natDegree_map _
  have hdeg_pos : (f.map (Pl.evalRingHom x₀)).degree ≠ 0 := by
    rw [Pl.degree_eq_natDegree hfx_mon.ne_zero, hfx_deg]
    exact_mod_cast (by omega : f.natDegree ≠ 0)
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root (f.map (Pl.evalRingHom x₀)) hdeg_pos
  refine ⟨x₀, y₀, hy₀, ?_⟩
  intro hg0
  apply hx₀
  change Pl.evalRingHom x₀ (pNorm f g) = 0
  rw [v155 (Pl.evalRingHom x₀) hf]
  have hdvd : (Pl.X - Pl.C y₀) ∣ f.map (Pl.evalRingHom x₀) :=
    Pl.dvd_iff_isRoot.mpr hy₀
  rcases hdvd with ⟨q, hq⟩
  have hq_mon : q.Monic := (Pl.monic_X_sub_C y₀).of_mul_monic_left (hq ▸ hfx_mon)
  rw [hq, v97 (Pl.monic_X_sub_C y₀) hq_mon, v132, hg0, zero_mul]
theorem v201 {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    {L : Type*} [Field L] [IsAlgClosed L] [CharP L p]
    {F : Mv3 L} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F)
    (hd3 : 3 ≤ d) (hdp : 2 * d < p)
    (h010 : Mv.eval ![0, 1, 0] F ≠ 0) :
    ¬ (F ∣ fWron p (derivZ F) cMon) := by
  have hnat_ne : ∀ n : ℕ, 0 < n → n < p → (n : L) ≠ 0 := by
    intro n hn hnp h0
    have hdvd := (Ch.cast_eq_zero_iff L p n).mp h0
    have := Nat.le_of_dvd hn hdvd; omega
  have h2 : (2 : L) ≠ 0 := by exact_mod_cast hnat_ne 2 (by omega) (by omega)
  have h3 : (3 : L) ≠ 0 := by exact_mod_cast hnat_ne 3 (by omega) (by omega)
  have h4 : (4 : L) ≠ 0 := by exact_mod_cast hnat_ne 4 (by omega) (by omega)
  have h5 : (5 : L) ≠ 0 := by exact_mod_cast hnat_ne 5 (by omega) (by omega)
  have h288 : (288 : L) ≠ 0 := by
    have : (288 : L) = 2 ^ 5 * 3 ^ 2 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero 5 h2) (pow_ne_zero 2 h3)
  set f := mdhZ F
  obtain ⟨hf_mon, hf_deg⟩ := v149 hF h010
  have hf_irr : Irreducible f := v71 hF hF_irr h010
  have hf_bd : ∀ k, f.coeff k ≠ 0 → (f.coeff k).natDegree + k ≤ f.natDegree := by
    intro k hk
    rw [hf_deg]
    exact (v133 hF k).resolve_right hk
  have hf_ndvd_deriv : ¬ f ∣ f.derivative := by
    rintro ⟨q, hq⟩
    have hcoeff : f.derivative.coeff (d - 1) = Pl.C (d : L) := by
      rw [Pl.coeff_derivative]
      have hd1 : d - 1 + 1 = d := by omega
      have h1 : f.coeff d = 1 := by rw [← hf_deg]; exact hf_mon.coeff_natDegree
      rw [hd1, h1, one_mul]
      have hcast : ((d - 1 : ℕ) : Pol L) + 1 = (d : Pol L) := by
        rw [← Nat.cast_one (R := Pol L), ← Nat.cast_add, hd1]
      rw [hcast, Pl.C_eq_natCast]
    have hder_ne : f.derivative ≠ 0 := by
      intro h0
      rw [h0, Pl.coeff_zero] at hcoeff
      have hC0 : (d : L) = 0 := by
        have := congr_arg (fun r : Pol L => r.coeff 0) hcoeff.symm
        simpa using this
      exact hnat_ne d (by omega) (by omega) hC0
    have hq_ne : q ≠ 0 := fun h0 => hder_ne (by rw [hq, h0, mul_zero])
    have hdeg_ge : d ≤ f.derivative.natDegree := by
      rw [hq, hf_mon.natDegree_mul' hq_ne, hf_deg]; omega
    have hdeg_lt : f.derivative.natDegree < d := by
      have := Pl.natDegree_derivative_le f
      rw [hf_deg] at this
      omega
    omega
  have hf_ndvd_hess : ¬ f ∣ dhZ (v111 F) := by
    intro hdvd_H
    obtain ⟨x₀, y₀, hroot, hderiv⟩ := v82 hf_mon hf_irr (by omega) hf_ndvd_deriv
    obtain ⟨Y, hY0, hYroot⟩ := v75 f x₀ y₀ hroot hderiv
    have hF0 : evBr x₀ Y F = 0 := by
      rw [v62]
      have hscale : dhZ F = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)) * f := by
        simp [f, mdhZ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h010]
      rw [hscale, Pl.map_mul, Pl.eval_mul, hYroot, mul_zero]
    have hH0 : evBr x₀ Y (v111 F) = 0 := by
      rcases hdvd_H with ⟨q, hq⟩
      rw [v62, hq, Pl.map_mul, Pl.eval_mul, hYroot, zero_mul]
    have hFy_ne : evBr x₀ Y (Mv.pderiv 1 F) ≠ 0 := by
      intro h0
      have hconst := congr_arg Ps.constantCoeff h0
      rw [map_zero, v62, v183] at hconst
      have hcomp : ∀ (g : Pol (Pol L)) (P : PS L), Ps.constantCoeff ((g.map (v16 x₀)).eval P) = (g.map (Pl.evalRingHom x₀)).eval (Ps.constantCoeff P) := by
        intro g P
        have hc : Ps.constantCoeff.comp (v16 x₀) = Pl.evalRingHom x₀ := by
          ext <;> simp [v16]
        induction g using Pl.induction_on' with
        | add g₁ g₂ h₁ h₂ => simp [Pl.map_add, Pl.eval_add, h₁, h₂]
        | monomial n a =>
          simp only [Pl.map_monomial, Pl.eval_monomial, map_mul, map_pow]
          congr 1; exact congr_fun (congr_arg DFunLike.coe hc) a
      rw [hcomp, hY0] at hconst
      have hsc : f.derivative = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)⁻¹) * (dhZ F).derivative := by
        simp [f, mdhZ]
      apply hderiv
      rw [hsc, Pl.map_mul, Pl.eval_mul, hconst, mul_zero]
    have hhes := v161 hF0
    rw [hH0, zero_add] at hhes
    have hY2 : psD (psD Y) = 0 := (mul_eq_zero.mp hhes).resolve_left (pow_ne_zero 3 hFy_ne)
    set m := Ps.constantCoeff (psD Y)
    have hlin_dvd : Ps.X ^ p ∣ Y - (Ps.C y₀ + Ps.C m * Ps.X) := by
      rw [Ps.X_pow_dvd_iff]
      intro n hn
      have hY2_c : ∀ k, ((k + 1 : ℕ) : L) * (((k + 2 : ℕ) : L) * Ps.coeff (k + 2) Y) = 0 := by
        intro k
        have := congr_arg (Ps.coeff k) hY2
        rw [v66, v66, map_zero] at this
        exact this
      cases n with
      | zero => simp [Ps.coeff_zero_eq_constantCoeff, hY0]
      | succ k =>
        cases k with
        | zero =>
          simp only [map_sub, map_add, Ps.coeff_C, Ps.coeff_C_mul, Ps.coeff_X, one_ne_zero, ↓reduceIte, zero_add, mul_one]
          have hm : m = Ps.coeff 1 Y := by
            dsimp only [m]
            rw [← Ps.coeff_zero_eq_constantCoeff, v66]; simp
          rw [hm, sub_self]
        | succ k =>
          have h0 := hY2_c k
          have hk1 : ((k + 1 : ℕ) : L) ≠ 0 := hnat_ne (k + 1) (by omega) (by omega)
          have hk2 : ((k + 2 : ℕ) : L) ≠ 0 := hnat_ne (k + 2) (by omega) (by omega)
          have hc0 : Ps.coeff (k + 2) Y = 0 :=
            (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hk1)).resolve_left hk2
          simp only [map_sub, map_add, hc0, Ps.coeff_C, Ps.coeff_C_mul, Ps.coeff_X, Nat.succ_ne_zero, ↓reduceIte, zero_add]
          rw [if_neg (by omega), mul_zero, sub_self]
    let L_lin : Pol (Pol L) :=
      Pl.X - Pl.C (Pl.C y₀ + Pl.C m * (Pl.X - Pl.C x₀))
    have hL_eval : (L_lin.map (v16 x₀)).eval Y = Y - (Ps.C y₀ + Ps.C m * Ps.X) := by
      simp [L_lin, v16]
    have hnorm_dvd : (Pl.X - Pl.C x₀) ^ p ∣ pNorm f L_lin :=
      v61 hf_mon x₀ Y p hYroot (hL_eval ▸ hlin_dvd)
    have hL_ndvd : ¬ f ∣ L_lin := by
      rintro ⟨q, hq⟩
      have hL_ne : L_lin ≠ 0 := (Pl.monic_X_sub_C _).ne_zero
      have hq_ne : q ≠ 0 := fun h0 => hL_ne (by rw [hq, h0, mul_zero])
      have hdeg_L : L_lin.natDegree = 1 := Pl.natDegree_X_sub_C _
      have hdeg_ge : d ≤ L_lin.natDegree := by rw [← hf_deg, hq, hf_mon.natDegree_mul' hq_ne]; omega
      omega
    have hnorm_ne : pNorm f L_lin ≠ 0 := v83 hf_mon hf_irr hL_ndvd
    have hL_bd : ∀ k, L_lin.coeff k ≠ 0 → (L_lin.coeff k).natDegree + k ≤ 1 := by
      intro k hk
      have hL_deg : L_lin.natDegree = 1 := Pl.natDegree_X_sub_C _
      have hkle : k ≤ 1 := hL_deg ▸ Pl.le_natDegree_of_ne_zero hk
      interval_cases k
      · simp only [L_lin, Pl.coeff_sub, Pl.coeff_X_zero, Pl.coeff_C_zero, zero_sub, Pl.natDegree_neg, add_zero]
        refine (Pl.natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact (Pl.natDegree_C_mul_le _ _).trans (by simp)
      · simp [L_lin]
    have hdeg_le : (pNorm f L_lin).natDegree ≤ d := by
      simpa [hf_deg] using v74 hf_mon 1 hf_bd hL_bd
    have hdeg_ge : p ≤ (pNorm f L_lin).natDegree := by
      rcases hnorm_dvd with ⟨q, hq⟩
      have hq_ne : q ≠ 0 := fun h0 => hnorm_ne (by rw [hq, h0, mul_zero])
      have hpow_mon : ((Pl.X - Pl.C x₀) ^ p).Monic := (Pl.monic_X_sub_C x₀).pow p
      have hpow_deg : ((Pl.X - Pl.C x₀) ^ p).natDegree = p := by
        rw [Pl.natDegree_pow, Pl.natDegree_X_sub_C, mul_one]
      rw [hq, hpow_mon.natDegree_mul' hq_ne, hpow_deg]; omega
    omega
  intro hF_dvd_W
  have hf_prime : Prime f := Ufm.irreducible_iff_prime.mp hf_irr
  have hndvd_prod : ¬ f ∣ f.derivative * dhZ (v111 F) :=
    fun h => (hf_prime.dvd_or_dvd h).elim hf_ndvd_deriv hf_ndvd_hess
  obtain ⟨x₀, y₀, hroot, hprod_ne⟩ := v82 hf_mon hf_irr (by omega) hndvd_prod
  rw [Pl.map_mul, Pl.eval_mul] at hprod_ne
  have hderiv : (f.derivative.map (Pl.evalRingHom x₀)).eval y₀ ≠ 0 := left_ne_zero_of_mul hprod_ne
  have hhess_ne : ((dhZ (v111 F)).map (Pl.evalRingHom x₀)).eval y₀ ≠ 0 :=
    right_ne_zero_of_mul hprod_ne
  obtain ⟨Y, hY0, hYroot⟩ := v75 f x₀ y₀ hroot hderiv
  have hF0 : evBr x₀ Y F = 0 := by
    rw [v62]
    have hscale : dhZ F = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)) * f := by
      simp [f, mdhZ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h010]
    rw [hscale, Pl.map_mul, Pl.eval_mul, hYroot, mul_zero]
  have hconst_eval : ∀ (g : Pol (Pol L)) (P : PS L), Ps.constantCoeff ((g.map (v16 x₀)).eval P) = (g.map (Pl.evalRingHom x₀)).eval (Ps.constantCoeff P) := by
    intro g P
    have hc : Ps.constantCoeff.comp (v16 x₀) = Pl.evalRingHom x₀ := by
      ext <;> simp [v16]
    induction g using Pl.induction_on' with
    | add g₁ g₂ h₁ h₂ => simp [Pl.map_add, Pl.eval_add, h₁, h₂]
    | monomial n a =>
      simp only [Pl.map_monomial, Pl.eval_monomial, map_mul, map_pow]
      congr 1; exact congr_fun (congr_arg DFunLike.coe hc) a
  have hFy_const_ne : Ps.constantCoeff (evBr x₀ Y (Mv.pderiv 1 F)) ≠ 0 := by
    rw [v62, v183, hconst_eval, hY0]
    intro h0
    have hsc : f.derivative = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)⁻¹) * (dhZ F).derivative := by simp [f, mdhZ]
    apply hderiv; rw [hsc, Pl.map_mul, Pl.eval_mul, h0, mul_zero]
  have hFy_ne : evBr x₀ Y (Mv.pderiv 1 F) ≠ 0 :=
    fun h0 => hFy_const_ne (by rw [h0, map_zero])
  have hH_const_ne : Ps.constantCoeff (evBr x₀ Y (v111 F)) ≠ 0 := by
    rw [v62, hconst_eval, hY0]; exact hhess_ne
  set x : PS L := Ps.C x₀ + Ps.X
  set d1 : PS L := psD Y
  set d2 : PS L := Ps.C (2 : L)⁻¹ * psD d1
  set d3 : PS L := Ps.C (3 : L)⁻¹ * psD d2
  set d4 : PS L := Ps.C (4 : L)⁻¹ * psD d3
  set d5 : PS L := Ps.C (5 : L)⁻¹ * psD d4
  have hx1 : psD x = 1 := by simp [x, v51, psD_C, psD_X]
  have hy1 : psD Y = d1 := rfl
  have hy2 : psD d1 = 2 * d2 := by
    dsimp only [d2]
    have h1 : (2 : PS L) = Ps.C 2 := (map_ofNat Ps.C 2).symm
    rw [h1, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]
  have hy3 : psD d2 = 3 * d3 := by
    dsimp only [d3]
    have h1 : (3 : PS L) = Ps.C 3 := (map_ofNat Ps.C 3).symm
    rw [h1, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h3, map_one, one_mul]
  have hy4 : psD d3 = 4 * d4 := by
    dsimp only [d4]
    have h1 : (4 : PS L) = Ps.C 4 := (map_ofNat Ps.C 4).symm
    rw [h1, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h4, map_one, one_mul]
  have hy5 : psD d4 = 5 * d5 := by
    dsimp only [d5]
    have h1 : (5 : PS L) = Ps.C 5 := (map_ofNat Ps.C 5).symm
    rw [h1, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h5, map_one, one_mul]
  have hd2_const_ne : Ps.constantCoeff d2 ≠ 0 := by
    intro h0
    have hhes := congr_arg Ps.constantCoeff (v161 hF0)
    rw [map_add, map_mul, map_zero, hy1, hy2, map_mul, map_ofNat, h0, mul_zero, mul_zero, add_zero] at hhes
    exact hH_const_ne hhes
  have hd2_ne : d2 ≠ 0 := fun h0 => hd2_const_ne (by rw [h0, map_zero])
  have hW_zero : evBr x₀ Y (fWron p (derivZ F) cMon) = 0 := by
    rcases hF_dvd_W with ⟨q, hq⟩
    rw [hq, map_mul, hF0, zero_mul]
  rw [v140 hF0] at hW_zero
  have hfw0 : fWron p psD (fun j => evBr x₀ Y (cMon j)) = 0 :=
    (mul_eq_zero.mp hW_zero).resolve_left (pow_ne_zero 10 hFy_ne)
  have hvec_eq : (fun j => evBr x₀ Y (cMon j)) = ![1, x, Y, x ^ 2, x * Y, Y ^ 2] := by
    ext j; fin_cases j <;> simp [cMon, evBr, x]
  rw [hvec_eq, v171 x Y d1 d2 d3 d4 hx1 hy1 hy2 hy3 hy4] at hfw0
  set u : PS L := x ^ p - x
  set w : PS L := (Y ^ p - Y) - d1 * u
  set WF : PS L := d2 ^ 4 * u ^ 2 - d2 ^ 3 * w + d2 ^ 2 * d3 * u * w + (d2 * d4 - d3 ^ 2) * w ^ 2
  set WC : PS L := d2 * (d2 ^ 2 * d5 - 3 * d2 * d3 * d4 + 2 * d3 ^ 3)
  have h288_ps : (-288 : PS L) ≠ 0 := by
    intro h0
    have := congr_arg Ps.constantCoeff h0
    simp only [map_neg, map_ofNat, map_zero, neg_eq_zero] at this
    exact h288 this
  have hWF0 : WF = 0 := (mul_eq_zero.mp hfw0).resolve_left h288_ps
  have hWCw : 5 * WC * w ^ 2 = 0 := by
    have hid := v188 (p := p) x Y d1 d2 d3 d4 d5 hx1 hy1 hy2 hy3 hy4 hy5
    dsimp only at hid
    change d2 ^ 2 * psD WF - 10 * d2 * d3 * WF = 5 * WC * w ^ 2 at hid
    rw [hWF0, v104, mul_zero, mul_zero, sub_zero] at hid
    exact hid.symm
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hdw := congr_arg psD hw0
    have hu : psD u = -1 := by
      dsimp only [u]; rw [v148, v197, hx1]; ring
    have hw' : psD w = -2 * d2 * u := by
      dsimp only [w]; rw [v148, v148, v197, hy1, v29, hy2, hu]; ring
    rw [hw', v104] at hdw
    have h2d2 : (-2 : PS L) * d2 ≠ 0 := by
      intro h0
      have := congr_arg Ps.constantCoeff h0
      simp only [map_mul, map_neg, map_ofNat, map_zero, neg_mul, neg_eq_zero] at this
      exact mul_ne_zero h2 hd2_const_ne this
    have hu0 : u = 0 := (mul_eq_zero.mp hdw).resolve_left h2d2
    have hdu := congr_arg psD hu0
    rw [hu, v104] at hdu
    exact neg_ne_zero.mpr one_ne_zero hdu
  have h5_ps : (5 : PS L) ≠ 0 := by
    intro h0; have := congr_arg Ps.constantCoeff h0
    simp only [map_ofNat, map_zero] at this; exact h5 this
  have hWC0 : WC = 0 := by
    have h5WC := (mul_eq_zero.mp hWCw).resolve_right (pow_ne_zero 2 hw_ne)
    exact (mul_eq_zero.mp h5WC).resolve_left h5_ps
  set m : L := Ps.constantCoeff d1
  set t : PS L := Ps.X
  set yT : PS L := Y - Ps.C y₀ - Ps.C m * t
  set d1T : PS L := d1 - Ps.C m
  have ht0 : Ps.constantCoeff t = 0 := Ps.constantCoeff_X
  have hyT0 : Ps.constantCoeff yT = 0 := by
    simp [yT, t, hY0]
  have hd1T0 : Ps.constantCoeff d1T = 0 := by
    simp [d1T, m]
  have ht1 : psD t = 1 := psD_X
  have hyT1 : psD yT = d1T := by
    dsimp only [yT, d1T, t]
    rw [v148, v148, hy1, psD_C, v210, psD_X]; ring
  have hyT2 : psD d1T = 2 * d2 := by
    dsimp only [d1T]; rw [v148, hy2, psD_C, sub_zero]
  have hw6_0 : v86 6 (Fi.snoc ![1, t, t ^ 2, t * yT, yT ^ 2] yT) = 0 := by
    have h6 := v129 t yT d1T d2 d3 d4 d5 ht1 hyT1 hyT2 hy3 hy4 hy5
    change v86 6 ![1, t, yT, t ^ 2, t * yT, yT ^ 2] = -34560 * WC at h6
    rw [hWC0, mul_zero] at h6
    let σ : Eqv.Perm (Fin 6) :=
      Eqv.swap (2 : Fin 6) 3 * Eqv.swap 3 4 * Eqv.swap 4 5
    have hsnoc_eq : Fi.snoc ![1, t, t ^ 2, t * yT, yT ^ 2] yT = ![1, t, t ^ 2, t * yT, yT ^ 2, yT] := by
      funext j; rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hmat : v64 6 (Fi.snoc ![1, t, t ^ 2, t * yT, yT ^ 2] yT) = (v64 6 ![1, t, yT, t ^ 2, t * yT, yT ^ 2]).submatrix id σ := by
      rw [hsnoc_eq]
      refine Mx.ext fun i j => ?_
      simp only [Mx.submatrix_apply, id_eq, v64, Mx.of_apply]
      congr 1
      rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [σ, Eqv.swap_apply_def]
    rw [v86, hmat, Mx.det_permute', ← v86, h6, mul_zero]
  have hw5_ne : Ps.constantCoeff (v86 5 ![1, t, t ^ 2, t * yT, yT ^ 2]) ≠ 0 := by
    rw [v144 t yT d1T d2 d3 d4 ht0 hyT0 hd1T0 ht1 hyT1 hyT2 hy3 hy4]
    exact mul_ne_zero h288 (pow_ne_zero 3 hd2_const_ne)
  obtain ⟨c, hc_deriv, hyT_eq⟩ :=
    v195 ![1, t, t ^ 2, t * yT, yT ^ 2] yT hw5_ne hw6_0
  set a : Fin 5 → L := fun i => Ps.constantCoeff (c i)
  have hc_dvd : ∀ i : Fin 5, Ps.X ^ p ∣ c i - Ps.C (a i) :=
    fun i => v160 hp (hc_deriv i)
  have hQ_ps_dvd : Ps.X ^ p ∣
      yT - (Ps.C (a 0) * 1 + Ps.C (a 1) * t + Ps.C (a 2) * t ^ 2 + Ps.C (a 3) * (t * yT) + Ps.C (a 4) * yT ^ 2) := by
    have hdiff : yT - (Ps.C (a 0) * 1 + Ps.C (a 1) * t + Ps.C (a 2) * t ^ 2 + Ps.C (a 3) * (t * yT) + Ps.C (a 4) * yT ^ 2) = ∑ i : Fin 5, (c i - Ps.C (a i)) * (![1, t, t ^ 2, t * yT, yT ^ 2] i) := by
      conv_lhs => arg 1; rw [hyT_eq]
      rw [Fi.sum_univ_five, Fi.sum_univ_five]
      simp only [cons5_val_0, cons5_val_1, cons5_val_2, cons5_val_3, cons5_val_4]
      ring
    rw [hdiff]
    apply Fs.dvd_sum; intro i _
    exact dvd_mul_of_dvd_left (hc_dvd i) _
  let xT_p : Pol (Pol L) := Pl.C (Pl.X - Pl.C x₀)
  let yT_p : Pol (Pol L) :=
    Pl.X - Pl.C (Pl.C y₀ + Pl.C m * (Pl.X - Pl.C x₀))
  let Q : Pol (Pol L) :=
    yT_p - (Pl.C (Pl.C (a 0)) + Pl.C (Pl.C (a 1)) * xT_p + Pl.C (Pl.C (a 2)) * xT_p ^ 2 + Pl.C (Pl.C (a 3)) * (xT_p * yT_p) + Pl.C (Pl.C (a 4)) * yT_p ^ 2)
  have hQ_eval : (Q.map (v16 x₀)).eval Y = yT - (Ps.C (a 0) * 1 + Ps.C (a 1) * t + Ps.C (a 2) * t ^ 2 + Ps.C (a 3) * (t * yT) + Ps.C (a 4) * yT ^ 2) := by
    have hxTp : (xT_p.map (v16 x₀)).eval Y = t := by simp [xT_p, t, v16]
    have hyTp : (yT_p.map (v16 x₀)).eval Y = yT := by simp [yT_p, yT, t, v16]; ring
    simp only [Q, Pl.map_sub, Pl.map_add, Pl.map_mul, Pl.map_pow, Pl.map_C, Pl.eval_sub, Pl.eval_add, Pl.eval_mul, Pl.eval_pow, Pl.eval_C, hxTp, hyTp]
    have hshiftC : ∀ r : L, v16 x₀ (Pl.C r) = Ps.C r := by
      intro r; simp [v16]
    simp only [hshiftC, mul_one]
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hder0 : (Q.derivative.map (Pl.evalRingHom x₀)).eval y₀ = 0 := by
      rw [hQ0, Pl.derivative_zero, Pl.map_zero, Pl.eval_zero]
    have hx0_eval : (xT_p.map (Pl.evalRingHom x₀)).eval y₀ = 0 := by simp [xT_p]
    have hy0_eval : (yT_p.map (Pl.evalRingHom x₀)).eval y₀ = 0 := by simp [yT_p]
    have hx_der : xT_p.derivative = 0 := Pl.derivative_C
    have hy_der : yT_p.derivative = 1 := by simp [yT_p]
    have hQ_der : (Q.derivative.map (Pl.evalRingHom x₀)).eval y₀ = 1 := by
      simp only [Q, Pl.derivative_sub, Pl.derivative_add, Pl.derivative_mul, Pl.derivative_pow, Pl.derivative_C, hx_der, hy_der, zero_mul, mul_zero, zero_add, add_zero, Pl.map_sub, Pl.map_add, Pl.map_mul, Pl.map_pow, Pl.map_C, Pl.map_one, Pl.eval_sub, Pl.eval_add, Pl.eval_mul, Pl.eval_pow, Pl.eval_C, Pl.eval_one, hx0_eval, hy0_eval]
      ring
    rw [hQ_der] at hder0
    exact one_ne_zero hder0
  have hQ_bd : ∀ k, Q.coeff k ≠ 0 → (Q.coeff k).natDegree + k ≤ 2 := by
    let totLe : ℕ → Pol (Pol L) → Prop :=
      fun e p => ∀ k, p.coeff k ≠ 0 → (p.coeff k).natDegree + k ≤ e
    have hmono : ∀ {e₁ e₂ p}, e₁ ≤ e₂ → totLe e₁ p → totLe e₂ p :=
      fun hle hp k hk => (hp k hk).trans hle
    have hadd : ∀ {e p q}, totLe e p → totLe e q → totLe e (p + q) := by
      intro e p q hp' hq' k hk
      rw [Pl.coeff_add] at hk ⊢
      have hkle : k ≤ e := by
        by_cases hp0 : p.coeff k = 0
        · rw [hp0, zero_add] at hk; have := hq' k hk; omega
        · have := hp' k hp0; omega
      have h1 : (p.coeff k).natDegree + k ≤ e := by
        by_cases hp0 : p.coeff k = 0
        · rw [hp0, Pl.natDegree_zero, zero_add]; exact hkle
        · exact hp' k hp0
      have h2 : (q.coeff k).natDegree + k ≤ e := by
        by_cases hq0 : q.coeff k = 0
        · rw [hq0, Pl.natDegree_zero, zero_add]; exact hkle
        · exact hq' k hq0
      have hle := Pl.natDegree_add_le (p.coeff k) (q.coeff k)
      omega
    have hneg : ∀ {e p}, totLe e p → totLe e (-p) := by
      intro e p hp' k hk
      rw [Pl.coeff_neg] at hk ⊢
      rw [Pl.natDegree_neg]
      exact hp' k (neg_ne_zero.mp hk)
    have hsub : ∀ {e p q}, totLe e p → totLe e q → totLe e (p - q) :=
      fun hp' hq' => by rw [sub_eq_add_neg]; exact hadd hp' (hneg hq')
    have hmul : ∀ {e₁ e₂ p q}, totLe e₁ p → totLe e₂ q → totLe (e₁ + e₂) (p * q) := by
      intro e₁ e₂ p q hp' hq' k hk
      rw [Pl.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j)] at hk ⊢
      have hkle : k ≤ e₁ + e₂ := by
        obtain ⟨i, hi, hne⟩ := Fs.exists_ne_zero_of_sum_ne_zero hk
        rw [Fs.mem_range] at hi
        have h1 := hp' i (left_ne_zero_of_mul hne)
        have h2 := hq' (k - i) (right_ne_zero_of_mul hne)
        omega
      have hdeg : (∑ i ∈ Fs.range (k + 1), p.coeff i * q.coeff (k - i)).natDegree ≤ e₁ + e₂ - k := by
        apply Pl.natDegree_sum_le_of_forall_le
        intro i hi
        rw [Fs.mem_range] at hi
        by_cases h0 : p.coeff i * q.coeff (k - i) = 0
        · rw [h0, Pl.natDegree_zero]; exact Nat.zero_le _
        · have h1 := hp' i (left_ne_zero_of_mul h0)
          have h2 := hq' (k - i) (right_ne_zero_of_mul h0)
          have hm := Pl.natDegree_mul_le (p := p.coeff i) (q := q.coeff (k - i))
          omega
      exact Nat.add_le_of_le_sub hkle hdeg
    have hCC : ∀ r : L, totLe 0 (Pl.C (Pl.C r)) := by
      intro r k hk
      cases k with
      | zero => simp
      | succ k => simp at hk
    have hxT : totLe 1 xT_p := by
      intro k hk
      cases k with
      | zero =>
        simp only [xT_p, Pl.coeff_C_zero, add_zero]
        rw [Pl.natDegree_X_sub_C]
      | succ k => simp [xT_p] at hk
    have hyT : totLe 1 yT_p := by
      intro k hk
      have hy_deg : yT_p.natDegree = 1 := Pl.natDegree_X_sub_C _
      have hkle : k ≤ 1 := hy_deg ▸ Pl.le_natDegree_of_ne_zero hk
      interval_cases k
      · simp only [yT_p, Pl.coeff_sub, Pl.coeff_X_zero, Pl.coeff_C_zero, zero_sub, Pl.natDegree_neg, add_zero]
        refine (Pl.natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact (Pl.natDegree_C_mul_le _ _).trans (by simp)
      · simp [yT_p]
    have hsq : ∀ {e p}, totLe e p → totLe (e + e) (p ^ 2) := fun hp' => by
      rw [sq]; exact hmul hp' hp'
    have hCmul : ∀ {e p} (r : L), totLe e p → totLe e (Pl.C (Pl.C r) * p) :=
      fun r hp' => by simpa using hmul (hCC r) hp'
    exact hsub (hmono (by omega) hyT)
      (hadd (hadd (hadd (hadd (hmono (by omega) (hCC (a 0)))
        (hmono (by omega) (hCmul (a 1) hxT)))
        (hCmul (a 2) (hsq hxT)))
        (hCmul (a 3) (hmul hxT hyT)))
        (hCmul (a 4) (hsq hyT)))
  have hQ_deg_le : Q.natDegree ≤ 2 := by
    apply Pl.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk; by_contra hne
    have := hQ_bd k hne; omega
  have hQ_ndvd : ¬ f ∣ Q := by
    rintro ⟨q, hq⟩
    have hq_ne : q ≠ 0 := fun h0 => hQ_ne (by rw [hq, h0, mul_zero])
    have hdeg_ge : d ≤ Q.natDegree := by rw [← hf_deg, hq, hf_mon.natDegree_mul' hq_ne]; omega
    omega
  have hnorm_dvd : (Pl.X - Pl.C x₀) ^ p ∣ pNorm f Q :=
    v61 hf_mon x₀ Y p hYroot (hQ_eval ▸ hQ_ps_dvd)
  have hnorm_ne : pNorm f Q ≠ 0 := v83 hf_mon hf_irr hQ_ndvd
  have hdeg_le : (pNorm f Q).natDegree ≤ d * 2 := by
    simpa [hf_deg] using v74 hf_mon 2 hf_bd hQ_bd
  have hdeg_ge : p ≤ (pNorm f Q).natDegree := by
    rcases hnorm_dvd with ⟨q, hq⟩
    have hq_ne : q ≠ 0 := fun h0 => hnorm_ne (by rw [hq, h0, mul_zero])
    have hpow_mon : ((Pl.X - Pl.C x₀) ^ p).Monic := (Pl.monic_X_sub_C x₀).pow p
    have hpow_deg : ((Pl.X - Pl.C x₀) ^ p).natDegree = p := by
      rw [Pl.natDegree_pow, Pl.natDegree_X_sub_C, mul_one]
    rw [hq, hpow_mon.natDegree_mul' hq_ne, hpow_deg]; omega
  omega
end NonVanishing
lemma v89 {K : Type*} [Field K] (i : Fin 3) :
    Prime (Mv.X i : Mv3 K) := by
  let ev0 : Mv3 K →ₐ[K] Mv3 K :=
    Mv.aeval (Fn.update Mv.X i 0)
  have hev_sub : ∀ P : Mv3 K, Mv.X i ∣ P - ev0 P := by
    intro P
    induction P using Mv.induction_on with
    | C a => simp [ev0]
    | add p q hp hq =>
      have : p + q - ev0 (p + q) = (p - ev0 p) + (q - ev0 q) := by rw [map_add]; ring
      rw [this]; exact dvd_add hp hq
    | mul_X p j hp =>
      rw [map_mul]
      by_cases hj : j = i
      · subst hj
        simp only [ev0, Mv.aeval_X, Fn.update_self, mul_zero, sub_zero]
        exact dvd_mul_left _ _
      · have : p * Mv.X j - ev0 p * ev0 (Mv.X j) = (p - ev0 p) * Mv.X j := by
          simp only [ev0, Mv.aeval_X, Fn.update_of_ne hj]; ring
        rw [this]; exact dvd_mul_of_dvd_left hp _
  have hdvd_iff : ∀ P : Mv3 K, Mv.X i ∣ P ↔ ev0 P = 0 := by
    intro P
    constructor
    · rintro ⟨q, rfl⟩
      simp [ev0]
    · intro h0
      have := hev_sub P
      rwa [h0, sub_zero] at this
  refine ⟨Mv.X_ne_zero i, ?_, ?_⟩
  · intro hu
    rcases hu with ⟨u, hu⟩
    have h1 := congr_arg (Mv.eval (0 : Fin 3 → K))
      (show Mv.X i * ((u⁻¹ : (Mv3 K)ˣ) : Mv3 K) = 1 by
        rw [← hu]; exact Units.mul_inv u)
    simp at h1
  · intro A B hAB
    rw [hdvd_iff, map_mul, mul_eq_zero] at hAB
    rcases hAB with hA | hB
    · exact Or.inl ((hdvd_iff A).mpr hA)
    · exact Or.inr ((hdvd_iff B).mpr hB)
lemma v156 {K : Type*} [Field K] {c : K} (hc : c ≠ 0) :
    IsUnit (Mv.C c : Mv3 K) :=
  Rh.isUnit_map Mv.C (isUnit_iff_ne_zero.mpr hc)
lemma v120 {K : Type*} [Field K] {P : Mv3 K} :
    IsUnit P ↔ ∃ c : K, c ≠ 0 ∧ P = Mv.C c := by
  constructor
  · rintro ⟨u, rfl⟩
    have hmul : (u : Mv3 K) * ((u⁻¹ : (Mv3 K)ˣ) : Mv3 K) = 1 :=
      Units.mul_inv u
    have hdeg0 : (u : Mv3 K).totalDegree = 0 := by
      have h1 : ((u : Mv3 K) * ((u⁻¹ : (Mv3 K)ˣ) : Mv3 K)).totalDegree = 0 := by
        rw [hmul, Mv.totalDegree_one]
      have hdeg_add : ∀ A B : Mv3 K, A ≠ 0 → B ≠ 0 → A.totalDegree + B.totalDegree ≤ (A * B).totalDegree := by
        intro A B hA hB
        set a := A.totalDegree
        set b := B.totalDegree
        have hA_top : Mv.homogeneousComponent a A ≠ 0 := by
          obtain ⟨m, hm, hdm⟩ : ∃ m ∈ A.support, m.sum (fun _ e => e) = a := by
            have hs : A.support.Nonempty := Mv.support_nonempty.mpr hA
            obtain ⟨m, hm, heq⟩ := exists_mem_eq_sup' hs (fun m => m.sum (fun _ e => e))
            refine ⟨m, hm, ?_⟩
            dsimp only [a]; unfold Mv.totalDegree
            rw [← Fs.sup'_eq_sup hs]; exact heq.symm
          intro h0
          have := congr_arg (Mv.coeff m) h0
          rw [Mv.coeff_homogeneousComponent, Mv.coeff_zero] at this
          have hdm' : Fu.degree m = a := hdm
          rw [if_pos hdm'] at this
          exact Mv.mem_support_iff.mp hm this
        have hB_top : Mv.homogeneousComponent b B ≠ 0 := by
          obtain ⟨m, hm, hdm⟩ : ∃ m ∈ B.support, m.sum (fun _ e => e) = b := by
            have hs : B.support.Nonempty := Mv.support_nonempty.mpr hB
            obtain ⟨m, hm, heq⟩ := exists_mem_eq_sup' hs (fun m => m.sum (fun _ e => e))
            refine ⟨m, hm, ?_⟩
            dsimp only [b]; unfold Mv.totalDegree
            rw [← Fs.sup'_eq_sup hs]; exact heq.symm
          intro h0
          have := congr_arg (Mv.coeff m) h0
          rw [Mv.coeff_homogeneousComponent, Mv.coeff_zero] at this
          have hdm' : Fu.degree m = b := hdm
          rw [if_pos hdm'] at this
          exact Mv.mem_support_iff.mp hm this
        have htop_eq : Mv.homogeneousComponent (a + b) (A * B) = Mv.homogeneousComponent a A * Mv.homogeneousComponent b B := by
          ext m
          rw [Mv.coeff_homogeneousComponent, Mv.coeff_mul, Mv.coeff_mul]
          by_cases hm' : Fu.degree m = a + b
          · rw [if_pos hm']
            apply sum_congr rfl; intro xy hxy
            have hsum : xy.1 + xy.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
            by_cases h1 : A.coeff xy.1 = 0
            · simp [h1, Mv.coeff_homogeneousComponent]
            · by_cases h2 : B.coeff xy.2 = 0
              · simp [h2, Mv.coeff_homogeneousComponent]
              · have hle1 : Fu.degree xy.1 ≤ a :=
                  le_sup (f := fun s : E3 => s.sum fun _ e => e) (Mv.mem_support_iff.mpr h1)
                have hle2 : Fu.degree xy.2 ≤ b :=
                  le_sup (f := fun s : E3 => s.sum fun _ e => e) (Mv.mem_support_iff.mpr h2)
                have hdsum : Fu.degree xy.1 + Fu.degree xy.2 = a + b := by
                  rw [← map_add, hsum, hm']
                rw [Mv.coeff_homogeneousComponent, Mv.coeff_homogeneousComponent, if_pos (by omega), if_pos (by omega)]
          · rw [if_neg hm']; symm
            have hhom := (Mv.homogeneousComponent_isHomogeneous a A).mul
              (Mv.homogeneousComponent_isHomogeneous b B)
            by_contra hne'
            rw [← Mv.coeff_mul] at hne'
            have hdeg := v10 hhom hne'
            apply hm'
            rw [Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi), Fi.sum_univ_three]
            exact hdeg
        have hAB_top_ne : Mv.homogeneousComponent (a + b) (A * B) ≠ 0 := by
          rw [htop_eq]; exact mul_ne_zero hA_top hB_top
        obtain ⟨m, hm⟩ := Mv.support_nonempty.mpr hAB_top_ne
        have hcm := Mv.mem_support_iff.mp hm
        rw [Mv.coeff_homogeneousComponent] at hcm
        split_ifs at hcm with hdm
        · have hle : Fu.degree m ≤ (A * B).totalDegree :=
            le_sup (f := fun s : E3 => s.sum fun _ e => e) (Mv.mem_support_iff.mpr hcm)
          omega
        · exact absurd rfl hcm
      have := hdeg_add (u : Mv3 K) ((u⁻¹ : (Mv3 K)ˣ) : Mv3 K)
        u.ne_zero (Units.ne_zero u⁻¹)
      omega
    have huC : (u : Mv3 K) = Mv.C ((u : Mv3 K).coeff 0) :=
      Mv.totalDegree_eq_zero_iff_eq_C.mp hdeg0
    refine ⟨(u : Mv3 K).coeff 0, ?_, huC⟩
    intro h0; exact u.ne_zero (by rw [huC, h0, map_zero])
  · rintro ⟨c, hc, rfl⟩
    exact v156 hc
lemma v77 {K : Type*} [Field K] {A B : Mv3 K} {d : ℕ}
    (hA : A.IsHomogeneous d) (hB : B.IsHomogeneous d) (heq : dhZ A = dhZ B) : A = B := by
  ext m
  by_cases hm : m 0 + m 1 + m 2 = d
  · have h1 := v40 hA (m 1) (m 0)
    have h2 := v40 hB (m 1) (m 0)
    rw [heq, if_pos (by omega)] at h1; rw [if_pos (by omega)] at h2
    have hm_eq : Fu.single 0 (m 0) + Fu.single 1 (m 1) + Fu.single 2 (d - m 0 - m 1) = m := by
      ext i; rcases v03 i with rfl | rfl | rfl <;> simp; omega
    rw [hm_eq] at h1 h2; exact h1.symm.trans h2
  · have h1 : A.coeff m = 0 := by by_contra hne; exact hm (v10 hA hne)
    have h2 : B.coeff m = 0 := by by_contra hne; exact hm (v10 hB hne)
    rw [h1, h2]
section ProjectiveWronskian
variable {K : Type*} [Field K]
lemma v78 (i : Fin 3) (m : E3) (c : K) :
    Mv.X i * Mv.pderiv i (Mv.monomial m c) = Mv.C (m i : K) * Mv.monomial m c := by
  rw [Mv.pderiv_monomial]
  cases h : m i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, map_zero, zero_mul]
  | succ k =>
    have hsub : Fu.single i 1 + (m - Fu.single i 1) = m := by
      ext j
      simp only [Fu.add_apply, Fu.tsub_apply, Fu.single_apply]
      by_cases hj : i = j
      · subst hj; simp [h]; omega
      · simp [hj]
    rw [Mv.X, Mv.monomial_mul, hsub, one_mul, Mv.C_mul_monomial]
    congr 1; ring
lemma v157 {F : Mv3 K} {d : ℕ} (hF : F.IsHomogeneous d) :
    Mv.X 0 * Mv.pderiv 0 F +
    Mv.X 1 * Mv.pderiv 1 F +
    Mv.X 2 * Mv.pderiv 2 F = Mv.C (d : K) * F := by
  conv_lhs => rw [Mv.as_sum F]
  conv_rhs => rw [Mv.as_sum F]
  simp only [map_sum, mul_sum]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  rw [v78, v78, v78]
  have hdeg := v10 hF (Mv.mem_support_iff.mp hm)
  rw [← add_mul, ← add_mul, ← map_add, ← map_add, ← Nat.cast_add, ← Nat.cast_add, hdeg]
lemma v12 {P : Mv3 K} {k : ℕ}
    (hP : P.IsHomogeneous k) (i : Fin 3) :
    (Mv.pderiv i P).IsHomogeneous (k - 1) := by
  rw [Mv.as_sum P, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro m hm
  rw [Mv.pderiv_monomial]
  cases hmi : m i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, map_zero]
    exact Mv.isHomogeneous_zero _ _ _
  | succ r =>
    apply Mv.isHomogeneous_monomial
    have hdeg := v10 hP (Mv.mem_support_iff.mp hm)
    rw [Fu.degree_apply, sum_subset (subset_univ _) (fun j _ hj => Fu.notMem_support_iff.mp hj), Fi.sum_univ_three]
    rcases v03 i with rfl | rfl | rfl <;>
      simp only [Fu.tsub_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, tsub_zero] <;>
      omega
lemma v65 {F P : Mv3 K} {d k : ℕ}
    (hF : F.IsHomogeneous d) (hP : P.IsHomogeneous k) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (derivZ F P).IsHomogeneous (d + k - 2) := by
  have heq : d - 1 + (k - 1) = d + k - 2 := by omega
  rw [← heq]
  exact ((v12 hF 1).mul (v12 hP 0)).sub
    ((v12 hF 0).mul (v12 hP 1))
lemma v118 {F P : Mv3 K} {d k : ℕ}
    (hF : F.IsHomogeneous d) (hP : P.IsHomogeneous k) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (derivX F P).IsHomogeneous (d + k - 2) := by
  have heq : d - 1 + (k - 1) = d + k - 2 := by omega
  rw [← heq]
  exact ((v12 hF 2).mul (v12 hP 1)).sub
    ((v12 hF 1).mul (v12 hP 2))
lemma v117 {F P : Mv3 K} {d k : ℕ}
    (hF : F.IsHomogeneous d) (hP : P.IsHomogeneous k) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (derivY F P).IsHomogeneous (d + k - 2) := by
  have heq : d - 1 + (k - 1) = d + k - 2 := by omega
  rw [← heq]
  exact ((v12 hF 0).mul (v12 hP 2)).sub
    ((v12 hF 2).mul (v12 hP 0))
lemma v128 (j : Fin 6) :
    (cMon (K := K) j).IsHomogeneous 2 := by
  rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [cMon, v34, v33, v20, v19, v18, v15, sq] <;>
    exact (Mv.isHomogeneous_X K _).mul (Mv.isHomogeneous_X K _)
lemma v152 {n : ℕ} (M : Matrix (Fin n) (Fin n) (Mv3 K))
    (r : Fin n → ℕ) (hM : ∀ i j, (M i j).IsHomogeneous (r i)) :
    M.det.IsHomogeneous (∑ i : Fin n, r i) := by
  rw [Mx.det_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  have hprod : (∏ i : Fin n, M (σ i) i).IsHomogeneous (∑ i : Fin n, r (σ i)) :=
    MvPolynomial.IsHomogeneous.prod Fs.univ (fun i => M (σ i) i) (fun i => r (σ i))
      (fun i _ => hM (σ i) i)
  rw [Eqv.sum_comp σ r] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hprod
  · simpa [hs] using hprod.neg
lemma v32 (p : ℕ) {F : Mv3 K} {d : ℕ}
    (_hF : F.IsHomogeneous d) (hd : 2 ≤ d)
    (D : Mv3 K → Mv3 K)
    (hD : ∀ {P : Mv3 K} {k : ℕ}, P.IsHomogeneous k → 1 ≤ k → (D P).IsHomogeneous (d + k - 2)) :
    (fWron p D cMon).IsHomogeneous (2 * p + 10 * d - 10) := by
  let r : Fin 6 → ℕ := ![2 * p, 2, d, 2 * d - 2, 3 * d - 4, 4 * d - 6]
  have hsum : ∑ i : Fin 6, r i = 2 * p + 10 * d - 10 := by
    rw [Fi.sum_univ_six]
    dsimp only [r]
    simp only [v34, v33, v20, v19, v18, v15]
    omega
  rw [← hsum]
  apply v152 _ r
  intro i j
  have hg := v128 (K := K) j
  have h1 : (D (cMon j)).IsHomogeneous d := by
    have := hD hg (by omega); rwa [show d + 2 - 2 = d by omega] at this
  have h2 : (D (D (cMon j))).IsHomogeneous (2 * d - 2) := by
    have := hD h1 (by omega); rwa [show d + d - 2 = 2 * d - 2 by omega] at this
  have h3 : (D (D (D (cMon j)))).IsHomogeneous (3 * d - 4) := by
    have := hD h2 (by omega); rwa [show d + (2 * d - 2) - 2 = 3 * d - 4 by omega] at this
  have h4 : (D (D (D (D (cMon j))))).IsHomogeneous (4 * d - 6) := by
    have := hD h3 (by omega); rwa [show d + (3 * d - 4) - 2 = 4 * d - 6 by omega] at this
  fin_cases i
  · simpa [v08, r, mul_comm] using hg.pow p
  · simpa [v08, r] using hg
  · simpa [v08, r] using h1
  · simpa [v08, r] using h2
  · simpa [v08, r] using h3
  · simpa [v08, r] using h4
lemma v194 {F P : Mv3 K} {d k : ℕ}
    (hF : F.IsHomogeneous d) (hP : P.IsHomogeneous k) :
    Mv.X 2 * derivX F P - Mv.X 0 * derivZ F P = Mv.C (d : K) * F * Mv.pderiv 1 P - Mv.C (k : K) * Mv.pderiv 1 F * P := by
  have heF := v157 hF
  have heP := v157 hP
  change Mv.X 2 * (Mv.pderiv 2 F * Mv.pderiv 1 P - Mv.pderiv 1 F * Mv.pderiv 2 P) - Mv.X 0 * (Mv.pderiv 1 F * Mv.pderiv 0 P - Mv.pderiv 0 F * Mv.pderiv 1 P) = _
  linear_combination Mv.pderiv 1 P * heF - Mv.pderiv 1 F * heP
lemma v193 {F P : Mv3 K} {d k : ℕ}
    (hF : F.IsHomogeneous d) (hP : P.IsHomogeneous k) :
    Mv.X 2 * derivY F P - Mv.X 1 * derivZ F P = Mv.C (k : K) * Mv.pderiv 0 F * P - Mv.C (d : K) * F * Mv.pderiv 0 P := by
  have heF := v157 hF
  have heP := v157 hP
  change Mv.X 2 * (Mv.pderiv 0 F * Mv.pderiv 2 P - Mv.pderiv 2 F * Mv.pderiv 0 P) - Mv.X 1 * (Mv.pderiv 1 F * Mv.pderiv 0 P - Mv.pderiv 0 F * Mv.pderiv 1 P) = _
  linear_combination Mv.pderiv 0 F * heP - Mv.pderiv 0 P * heF
lemma v22 {A B : Mv3 K} {a b : ℕ}
    (hA : A.IsHomogeneous a) (hB : B.IsHomogeneous b) (hab : a ≤ b)
    (heq : dhZ A = dhZ B) :
    Mv.X 2 ^ (b - a) * A = B := by
  apply v77 (d := b)
  · have hpow : (Mv.X 2 ^ (b - a) : Mv3 K).IsHomogeneous (b - a) := by
      simpa using (Mv.isHomogeneous_X K (2 : Fin 3)).pow (b - a)
    have := hpow.mul hA
    rwa [Nat.sub_add_cancel hab] at this
  · exact hB
  · rw [v126, dhZ_pow, dhZ_X2, one_pow, one_mul, heq]
lemma v122 {F R : Mv3 K} {d e : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F) (h010 : Mv.eval ![0, 1, 0] F ≠ 0)
    (hR : R.IsHomogeneous e) {x₀ : K} {Y : PS K}
    (hYroot : ((mdhZ F).map (v16 x₀)).eval Y = 0)
    (hR0 : evBr x₀ Y R = 0) :
    F ∣ R := by
  set f := mdhZ F
  obtain ⟨hf_mon, _⟩ := v149 hF h010
  have hf_irr : Irreducible f := v71 hF hF_irr h010
  have hnorm0 : pNorm f (dhZ R) = 0 := by
    by_contra hne
    set k := (pNorm f (dhZ R)).natDegree + 1
    have hdvd : (Pl.X - Pl.C x₀) ^ k ∣ pNorm f (dhZ R) := by
      apply v61 hf_mon x₀ Y k hYroot
      rw [← v62, hR0]
      exact dvd_zero _
    rcases hdvd with ⟨q, hq⟩
    have hq_ne : q ≠ 0 := fun h0 => hne (by rw [hq, h0, mul_zero])
    have hmon : ((Pl.X - Pl.C x₀) ^ k).Monic :=
      (Pl.monic_X_sub_C x₀).pow k
    have hdeg_ge : k ≤ (pNorm f (dhZ R)).natDegree := by
      rw [hq, hmon.natDegree_mul' hq_ne, Pl.natDegree_pow, Pl.natDegree_X_sub_C, mul_one]
      omega
    omega
  have hf_dvd : f ∣ dhZ R := by
    by_contra hndvd
    exact v83 hf_mon hf_irr hndvd hnorm0
  have hdeF_dvd : dhZ F ∣ dhZ R := by
    rcases hf_dvd with ⟨q, hq⟩
    refine ⟨Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)⁻¹) * q, ?_⟩
    rw [hq]; simp only [f, mdhZ]; ring
  rcases hdeF_dvd with ⟨q, hq⟩
  set m := bDeg q
  set Q := hmZ m q
  have hQ_hom : Q.IsHomogeneous m := v58 (le_refl m)
  have hde_eq : dhZ (F * Q) = dhZ R := by
    rw [v126, v198 (le_refl m), hq]
  have hFQ_hom : (F * Q).IsHomogeneous (d + m) := hF.mul hQ_hom
  by_cases hle : d + m ≤ e
  · have heq := v22 hFQ_hom hR hle hde_eq
    exact ⟨Mv.X 2 ^ (e - (d + m)) * Q, by rw [← heq]; ring⟩
  · have heq := v22 hR hFQ_hom (by omega) hde_eq.symm
    have hF_dvd_mul : F ∣ Mv.X 2 ^ (d + m - e) * R := ⟨Q, heq⟩
    have hF_prime : Prime F := Ufm.irreducible_iff_prime.mp hF_irr
    have hF_ndvd_X2' : ¬ F ∣ Mv.X 2 := by
      intro hdvd
      have hX2_irr : Irreducible (Mv.X 2 : Mv3 K) :=
        (v89 2).irreducible
      rcases hdvd with ⟨u, hu⟩
      rcases hX2_irr.isUnit_or_isUnit hu with hFu | huu
      · exact hF_irr.not_isUnit hFu
      · rcases huu with ⟨v, hv⟩
        have hF_eq : F = Mv.X 2 * ((v⁻¹ : (Mv3 K)ˣ) : Mv3 K) := by
          rw [hu, ← hv, mul_assoc, Units.mul_inv, mul_one]
        have hev := congr_arg (Mv.eval ![0, 1, 0]) hF_eq
        simp only [map_mul, Mv.eval_X, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, zero_mul] at hev
        exact h010 hev
    exact (hF_prime.dvd_or_dvd hF_dvd_mul).resolve_left
      (fun hpow => hF_ndvd_X2' (hF_prime.dvd_of_dvd_pow hpow))
lemma v147 {u ui : PS K} (hui : u * ui = 1) (k : ℕ) (p : PS K) :
    u ^ (k + 1) * psD (ui ^ k * p) = u * psD p - (k : PS K) * psD u * p := by
  have hdui : u ^ 2 * psD ui = -psD u := by
    have h0 := congr_arg psD hui
    rw [v29, v159] at h0
    have h1 : u * (psD u * ui + u * psD ui) = 0 := by rw [h0, mul_zero]
    have h2 : u * (psD u * ui) = psD u := by
      calc u * (psD u * ui) = psD u * (u * ui) := by ring
        _ = psD u := by rw [hui, mul_one]
    linear_combination h1 - h2
  have huik : u ^ k * ui ^ k = 1 := by rw [← mul_pow, hui, one_pow]
  rw [v29, psD_pow]
  cases k with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, zero_add, pow_one, sub_zero]
  | succ m =>
    have huim : u ^ m * ui ^ m = 1 := by rw [← mul_pow, hui, one_pow]
    have hstep : u ^ (m + 2) * (((m + 1 : ℕ) : PS K) * ui ^ m * psD ui * p) = -((m + 1 : ℕ) : PS K) * psD u * p := by
      calc u ^ (m + 2) * (((m + 1 : ℕ) : PS K) * ui ^ m * psD ui * p)
          = ((m + 1 : ℕ) : PS K) * (u ^ m * ui ^ m) * (u ^ 2 * psD ui) * p := by ring
        _ = ((m + 1 : ℕ) : PS K) * 1 * (-psD u) * p := by rw [huim, hdui]
        _ = -((m + 1 : ℕ) : PS K) * psD u * p := by ring
    have hstep2 : u ^ (m + 2) * (ui ^ (m + 1) * psD p) = u * psD p := by
      calc u ^ (m + 2) * (ui ^ (m + 1) * psD p)
          = u * (u ^ (m + 1) * ui ^ (m + 1)) * psD p := by ring
        _ = u * 1 * psD p := by rw [huik]
        _ = u * psD p := by ring
    rw [Nat.add_sub_cancel, mul_add, hstep, hstep2]
    ring
theorem v181 {p : ℕ} (_hp : Nat.Prime p) {L : Type*} [Field L]
    [IsAlgClosed L] [CharP L p] {F : Mv3 L} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F) (hd3 : 3 ≤ d) (hdp : d < p)
    (h010 : Mv.eval ![0, 1, 0] F ≠ 0) :
    F ∣ Mv.X 2 ^ 10 * fWron p (derivX F) cMon - Mv.X 0 ^ 10 * fWron p (derivZ F) cMon ∧
    F ∣ Mv.X 2 ^ 10 * fWron p (derivY F) cMon - Mv.X 1 ^ 10 * fWron p (derivZ F) cMon := by
  set f := mdhZ F
  obtain ⟨hf_mon, hf_deg⟩ := v149 hF h010
  have hf_irr : Irreducible f := v71 hF hF_irr h010
  have hf_prime : Prime f := Ufm.irreducible_iff_prime.mp hf_irr
  have hnat_ne : ∀ n : ℕ, 0 < n → n < p → (n : L) ≠ 0 := by
    intro n hn1 hn2 h0
    have hdvd := (Ch.cast_eq_zero_iff L p n).mp h0
    have := Nat.le_of_dvd hn1 hdvd; omega
  have hf_ndvd_deriv : ¬ f ∣ f.derivative := by
    rintro ⟨q, hq⟩
    have hcoeff : f.derivative.coeff (d - 1) = Pl.C (d : L) := by
      rw [Pl.coeff_derivative]
      have hd1 : d - 1 + 1 = d := by omega
      have h1 : f.coeff d = 1 := by rw [← hf_deg]; exact hf_mon.coeff_natDegree
      rw [hd1, h1, one_mul]
      have hcast : ((d - 1 : ℕ) : Pol L) + 1 = (d : Pol L) := by
        rw [← Nat.cast_one (R := Pol L), ← Nat.cast_add, hd1]
      rw [hcast, Pl.C_eq_natCast]
    have hder_ne : f.derivative ≠ 0 := by
      intro h0; rw [h0, Pl.coeff_zero] at hcoeff
      have hC0 : (d : L) = 0 := by simpa using congr_arg (fun r : Pol L => r.coeff 0) hcoeff.symm
      exact hnat_ne d (by omega) hdp hC0
    have hq_ne : q ≠ 0 := fun h0 => hder_ne (by rw [hq, h0, mul_zero])
    have hdeg_ge : d ≤ f.derivative.natDegree := by rw [hq, hf_mon.natDegree_mul' hq_ne, hf_deg]; omega
    have hdeg_lt : f.derivative.natDegree < d := by
      have := Pl.natDegree_derivative_le f; rw [hf_deg] at this; omega
    omega
  have hf_ndvd_CX : ¬ f ∣ Pl.C (Pl.X : Pol L) := by
    rintro ⟨q, hq⟩
    have hne : (Pl.C (Pl.X : Pol L) : Pol (Pol L)) ≠ 0 :=
      Polynomial.C_ne_zero.mpr Pl.X_ne_zero
    have hq_ne : q ≠ 0 := fun h0 => hne (by rw [hq, h0, mul_zero])
    have hge : d ≤ (Pl.C (Pl.X : Pol L)).natDegree := by
      rw [hq, hf_mon.natDegree_mul' hq_ne, hf_deg]; omega
    rw [Pl.natDegree_C] at hge; omega
  have hf_ndvd_X : ¬ f ∣ (Pl.X : Pol (Pol L)) := by
    rintro ⟨q, hq⟩
    have hq_ne : q ≠ 0 := fun h0 => Pl.X_ne_zero (by rw [hq, h0, mul_zero])
    have hge : d ≤ (Pl.X : Pol (Pol L)).natDegree := by
      rw [hq, hf_mon.natDegree_mul' hq_ne, hf_deg]; omega
    rw [Pl.natDegree_X] at hge; omega
  have hf_ndvd_prod : ¬ f ∣ f.derivative * Pl.C Pl.X * Pl.X := by
    intro h
    rcases hf_prime.dvd_or_dvd h with h1 | h2
    · rcases hf_prime.dvd_or_dvd h1 with h11 | h12
      · exact hf_ndvd_deriv h11
      · exact hf_ndvd_CX h12
    · exact hf_ndvd_X h2
  obtain ⟨x₀, y₀, hroot, hprod_ne⟩ := v82 hf_mon hf_irr (by omega) hf_ndvd_prod
  simp only [Pl.map_mul, Pl.eval_mul, Pl.map_C, Pl.eval_C, Pl.map_X, Pl.eval_X, Pl.coe_evalRingHom] at hprod_ne
  have hderiv : (f.derivative.map (Pl.evalRingHom x₀)).eval y₀ ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul hprod_ne)
  have hx₀_ne : x₀ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hprod_ne)
  have hy₀_ne : y₀ ≠ 0 := right_ne_zero_of_mul hprod_ne
  obtain ⟨Y, hY0, hYroot⟩ := v75 f x₀ y₀ hroot hderiv
  have hF0 : evBr x₀ Y F = 0 := by
    rw [v62]
    have hscale : dhZ F = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F)) * f := by
      simp [f, mdhZ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h010]
    rw [hscale, Pl.map_mul, Pl.eval_mul, hYroot, mul_zero]
  set x : PS L := Ps.C x₀ + Ps.X
  have hx_unit : IsUnit x := by
    rw [Ps.isUnit_iff_constantCoeff]
    have : Ps.constantCoeff x = x₀ := by simp [x]
    rw [this]; exact isUnit_iff_ne_zero.mpr hx₀_ne
  have hY_unit : IsUnit Y := by
    rw [Ps.isUnit_iff_constantCoeff, hY0]; exact isUnit_iff_ne_zero.mpr hy₀_ne
  obtain ⟨ux, hux⟩ := hx_unit
  obtain ⟨uY, huY⟩ := hY_unit
  set xi : PS L := ↑ux⁻¹
  set yi : PS L := ↑uY⁻¹
  have hxxi : x * xi = 1 := by dsimp only [xi]; rw [← hux]; exact Units.mul_inv ux
  have hYyi : Y * yi = 1 := by dsimp only [yi]; rw [← huY]; exact Units.mul_inv uY
  have hx1 : psD x = 1 := by simp [x, v51, psD_C, psD_X]
  set Fy := evBr x₀ Y (Mv.pderiv 1 F)
  set Fx := evBr x₀ Y (Mv.pderiv 0 F)
  have hFx_rel : Fx + Fy * psD Y = 0 := by
    have h0 := congr_arg psD hF0
    rw [v178, v104] at h0
    exact h0
  have heb_C : ∀ c : L, evBr x₀ Y (Mv.C c) = Ps.C c :=
    fun c => by simp [evBr, Ps.algebraMap_eq]
  have heb_X0 : evBr x₀ Y (Mv.X 0) = x := by simp [evBr, x]
  have heb_X1 : evBr x₀ Y (Mv.X 1) = Y := by simp [evBr]
  have heb_X2 : evBr x₀ Y (Mv.X 2) = 1 := by simp [evBr]
  have hDX : ∀ {P : Mv3 L} {k : ℕ}, P.IsHomogeneous k → xi ^ (k + d - 2) * evBr x₀ Y (derivX F P) = (Fy * xi ^ (d - 3)) * psD (xi ^ k * evBr x₀ Y P) := by
    intro P k hP
    have hid := congr_arg (evBr x₀ Y) (v194 hF hP)
    simp only [map_sub, map_mul, heb_C, heb_X0, heb_X2, one_mul] at hid
    rw [hF0, mul_zero, zero_mul, zero_sub, v182 hF0] at hid
    have hDX_eq : evBr x₀ Y (derivX F P) = Fy * (x * psD (evBr x₀ Y P) - (k : PS L) * psD x * evBr x₀ Y P) := by
      have hkC : Ps.C (k : L) = (k : PS L) := map_natCast Ps.C k
      rw [hkC] at hid
      change evBr x₀ Y (derivX F P) - x * (Fy * psD (evBr x₀ Y P)) = -((k : PS L) * Fy * evBr x₀ Y P) at hid
      rw [hx1, mul_one]; linear_combination hid
    rw [hDX_eq, ← v147 hxxi k (evBr x₀ Y P)]
    have hexp : k + d - 2 = (k + 1) + (d - 3) := by omega
    rw [hexp, pow_add]
    have hcancel : xi ^ (k + 1) * x ^ (k + 1) = 1 := by rw [← mul_pow, mul_comm, hxxi, one_pow]
    calc xi ^ (k + 1) * xi ^ (d - 3) * (Fy * (x ^ (k + 1) * psD (xi ^ k * evBr x₀ Y P)))
        = (xi ^ (k + 1) * x ^ (k + 1)) * (Fy * xi ^ (d - 3)) * psD (xi ^ k * evBr x₀ Y P) := by ring
      _ = 1 * (Fy * xi ^ (d - 3)) * psD (xi ^ k * evBr x₀ Y P) := by rw [hcancel]
      _ = Fy * xi ^ (d - 3) * psD (xi ^ k * evBr x₀ Y P) := by ring
  have hDY : ∀ {P : Mv3 L} {k : ℕ}, P.IsHomogeneous k → yi ^ (k + d - 2) * evBr x₀ Y (derivY F P) = (Fy * yi ^ (d - 3)) * psD (yi ^ k * evBr x₀ Y P) := by
    intro P k hP
    have hid := congr_arg (evBr x₀ Y) (v193 hF hP)
    simp only [map_sub, map_mul, heb_C, heb_X1, heb_X2, one_mul] at hid
    rw [hF0, mul_zero, zero_mul, sub_zero, v182 hF0] at hid
    have hDY_eq : evBr x₀ Y (derivY F P) = Fy * (Y * psD (evBr x₀ Y P) - (k : PS L) * psD Y * evBr x₀ Y P) := by
      have hkC : Ps.C (k : L) = (k : PS L) := map_natCast Ps.C k
      rw [hkC] at hid
      change evBr x₀ Y (derivY F P) - Y * (Fy * psD (evBr x₀ Y P)) = (k : PS L) * Fx * evBr x₀ Y P at hid
      linear_combination hid + (k : PS L) * evBr x₀ Y P * hFx_rel
    rw [hDY_eq, ← v147 hYyi k (evBr x₀ Y P)]
    have hexp : k + d - 2 = (k + 1) + (d - 3) := by omega
    rw [hexp, pow_add]
    have hcancel : yi ^ (k + 1) * Y ^ (k + 1) = 1 := by rw [← mul_pow, mul_comm, hYyi, one_pow]
    calc yi ^ (k + 1) * yi ^ (d - 3) * (Fy * (Y ^ (k + 1) * psD (yi ^ k * evBr x₀ Y P)))
        = (yi ^ (k + 1) * Y ^ (k + 1)) * (Fy * yi ^ (d - 3)) * psD (yi ^ k * evBr x₀ Y P) := by ring
      _ = 1 * (Fy * yi ^ (d - 3)) * psD (yi ^ k * evBr x₀ Y P) := by rw [hcancel]
      _ = Fy * yi ^ (d - 3) * psD (yi ^ k * evBr x₀ Y P) := by ring
  have hchart : ∀ (u ui : PS L) (huui : u * ui = 1)
      (D : Mv3 L → Mv3 L)
      (hD_hom : ∀ {P : Mv3 L} {k : ℕ}, P.IsHomogeneous k → 1 ≤ k → (D P).IsHomogeneous (d + k - 2))
      (hD_ev : ∀ {P : Mv3 L} {k : ℕ}, P.IsHomogeneous k → ui ^ (k + d - 2) * evBr x₀ Y (D P) = (Fy * ui ^ (d - 3)) * psD (ui ^ k * evBr x₀ Y P)),
      evBr x₀ Y (fWron p D cMon) = u ^ 10 * evBr x₀ Y (fWron p (derivZ F) cMon) := by
    intro u ui huui D hD_hom hD_ev
    set Dbar : v35 (PS L) := v48.smul (Fy * ui ^ (d - 3))
    let r : Fin 6 → ℕ := ![2 * p, 2, d, 2 * d - 2, 3 * d - 4, 4 * d - 6]
    let S : Matrix (Fin 6) (Fin 6) (PS L) := Mx.diagonal (fun i => ui ^ r i)
    have hSM : S * (evBr x₀ Y).mapMatrix (v08 p D cMon) = v08 p Dbar (fun j => ui ^ 2 * evBr x₀ Y (cMon j)) := by
      refine Mx.ext fun i j => ?_
      rw [Mx.diagonal_mul]
      simp only [Rh.mapMatrix_apply, Mx.map_apply]
      set g := cMon (K := L) j
      have hg : g.IsHomogeneous 2 := v128 j
      have hg1 : (D g).IsHomogeneous d := by
        have := hD_hom hg (by omega); rwa [show d + 2 - 2 = d by omega] at this
      have hg2 : (D (D g)).IsHomogeneous (2 * d - 2) := by
        have := hD_hom hg1 (by omega); rwa [show d + d - 2 = 2 * d - 2 by omega] at this
      have hg3 : (D (D (D g))).IsHomogeneous (3 * d - 4) := by
        have := hD_hom hg2 (by omega); rwa [show d + (2 * d - 2) - 2 = 3 * d - 4 by omega] at this
      have h1 : ui ^ d * evBr x₀ Y (D g) = Dbar (ui ^ 2 * evBr x₀ Y g) := by
        simpa [Dbar, v35.smul, v48, show 2 + d - 2 = d by omega] using hD_ev hg
      have h2 : ui ^ (2 * d - 2) * evBr x₀ Y (D (D g)) = Dbar (Dbar (ui ^ 2 * evBr x₀ Y g)) := by
        rw [← h1]; simpa [Dbar, v35.smul, v48, show d + d - 2 = 2 * d - 2 by omega] using hD_ev hg1
      have h3 : ui ^ (3 * d - 4) * evBr x₀ Y (D (D (D g))) = Dbar (Dbar (Dbar (ui ^ 2 * evBr x₀ Y g))) := by
        rw [← h2]; simpa [Dbar, v35.smul, v48, show (2 * d - 2) + d - 2 = 3 * d - 4 by omega] using hD_ev hg2
      have h4 : ui ^ (4 * d - 6) * evBr x₀ Y (D (D (D (D g)))) = Dbar (Dbar (Dbar (Dbar (ui ^ 2 * evBr x₀ Y g)))) := by
        rw [← h3]; simpa [Dbar, v35.smul, v48, show (3 * d - 4) + d - 2 = 4 * d - 6 by omega] using hD_ev hg3
      rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [v08, Mx.of_apply, r, v34, map_pow, mul_pow, ← pow_mul]
      · simp only [v08, Mx.of_apply, r, v33]
      · simpa only [v08, Mx.of_apply, r, v20] using h1
      · simpa only [v08, Mx.of_apply, r, v19] using h2
      · simpa only [v08, Mx.of_apply, r, v18] using h3
      · simpa only [v08, Mx.of_apply, r, v15] using h4
    have hdet := congr_arg Mx.det hSM
    rw [Mx.det_mul, Mx.det_diagonal, ← Rh.map_det] at hdet
    have hprod_S : ∏ i : Fin 6, ui ^ r i = ui ^ (2 * p + 10 * d - 10) := by
      rw [prod_pow_eq_pow_sum, Fi.sum_univ_six]
      dsimp only [r]
      simp only [v34, v33, v20, v19, v18, v15]
      congr 1; omega
    rw [hprod_S] at hdet
    change ui ^ (2 * p + 10 * d - 10) * evBr x₀ Y (fWron p D cMon) = fWron p Dbar (fun j => ui ^ 2 * evBr x₀ Y (cMon j)) at hdet
    rw [v112 p v48 (Fy * ui ^ (d - 3)), v213 p v48 (ui ^ 2)] at hdet
    have hrhs : (Fy * ui ^ (d - 3)) ^ 10 * (ui ^ 2) ^ (p + 5) * fWron p v48 (fun j => evBr x₀ Y (cMon j)) = ui ^ (2 * p + 10 * d - 20) * evBr x₀ Y (fWron p (derivZ F) cMon) := by
      rw [v140 hF0]
      change (Fy * ui ^ (d - 3)) ^ 10 * (ui ^ 2) ^ (p + 5) * fWron p psD (fun j => evBr x₀ Y (cMon j)) = _
      rw [mul_pow, ← pow_mul, ← pow_mul]
      have hexp : (d - 3) * 10 + 2 * (p + 5) = 2 * p + 10 * d - 20 := by omega
      calc Fy ^ 10 * ui ^ ((d - 3) * 10) * ui ^ (2 * (p + 5)) * fWron p psD (fun j => evBr x₀ Y (cMon j))
          = ui ^ ((d - 3) * 10 + 2 * (p + 5)) * (Fy ^ 10 * fWron p psD (fun j => evBr x₀ Y (cMon j))) := by
            rw [pow_add]; ring
        _ = ui ^ (2 * p + 10 * d - 20) * (Fy ^ 10 * fWron p psD (fun j => evBr x₀ Y (cMon j))) := by
            rw [hexp]
    rw [← mul_assoc, hrhs] at hdet
    have hmul := congr_arg (fun z => u ^ (2 * p + 10 * d - 10) * z) hdet
    have hc1 : u ^ (2 * p + 10 * d - 10) * ui ^ (2 * p + 10 * d - 10) = 1 := by
      rw [← mul_pow, huui, one_pow]
    have hc2 : u ^ (2 * p + 10 * d - 10) * ui ^ (2 * p + 10 * d - 20) = u ^ 10 := by
      have hexp : 2 * p + 10 * d - 10 = 10 + (2 * p + 10 * d - 20) := by omega
      rw [hexp, pow_add, mul_assoc, ← mul_pow, huui, one_pow, mul_one]
    rw [← mul_assoc, hc1, one_mul, ← mul_assoc, hc2] at hmul
    exact hmul
  have hWX_ev := hchart x xi hxxi (derivX F) (fun hP hk => v118 hF hP (by omega) hk) hDX
  have hWY_ev := hchart Y yi hYyi (derivY F) (fun hP hk => v117 hF hP (by omega) hk) hDY
  have hWZ_hom : (fWron p (derivZ F) cMon).IsHomogeneous (2 * p + 10 * d - 10) :=
    v32 p hF (by omega) (derivZ F)
      (fun hP hk => v65 hF hP (by omega) hk)
  have hWX_hom : (fWron p (derivX F) cMon).IsHomogeneous (2 * p + 10 * d - 10) :=
    v32 p hF (by omega) (derivX F)
      (fun hP hk => v118 hF hP (by omega) hk)
  have hWY_hom : (fWron p (derivY F) cMon).IsHomogeneous (2 * p + 10 * d - 10) :=
    v32 p hF (by omega) (derivY F)
      (fun hP hk => v117 hF hP (by omega) hk)
  have hXpow_hom : ∀ i : Fin 3, (Mv.X i ^ 10 : Mv3 L).IsHomogeneous 10 :=
    fun i => by simpa using (Mv.isHomogeneous_X L i).pow 10
  constructor
  · apply v122 hF hF_irr h010 ((hXpow_hom 2).mul hWX_hom |>.sub ((hXpow_hom 0).mul hWZ_hom)) hYroot
    simp only [map_sub, map_mul, map_pow, heb_X0, heb_X2, one_pow, one_mul, hWX_ev, sub_self]
  · apply v122 hF hF_irr h010 ((hXpow_hom 2).mul hWY_hom |>.sub ((hXpow_hom 1).mul hWZ_hom)) hYroot
    simp only [map_sub, map_mul, map_pow, heb_X1, heb_X2, one_pow, one_mul, hWY_ev, sub_self]
noncomputable def evZ0 : Mv3 K →ₐ[K] Mv3 K :=
  Mv.aeval ![Mv.X 0, Mv.X 1, 0]
lemma v162 (P : Mv3 K) :
    Mv.X 2 ∣ P - evZ0 P := by
  induction P using Mv.induction_on with
  | C a => simp [evZ0]
  | add p q hp hq =>
    have : p + q - evZ0 (p + q) = (p - evZ0 p) + (q - evZ0 q) := by rw [map_add]; ring
    rw [this]; exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    rcases v03 i with rfl | rfl | rfl
    · have : p * Mv.X 0 - evZ0 p * evZ0 (Mv.X 0) = (p - evZ0 p) * Mv.X 0 := by simp [evZ0]; ring
      rw [this]; exact dvd_mul_of_dvd_left hp _
    · have : p * Mv.X 1 - evZ0 p * evZ0 (Mv.X 1) = (p - evZ0 p) * Mv.X 1 := by simp [evZ0]; ring
      rw [this]; exact dvd_mul_of_dvd_left hp _
    · have h2 : evZ0 (Mv.X 2 : Mv3 K) = 0 := by simp [evZ0]
      rw [h2, mul_zero, sub_zero]
      exact dvd_mul_left _ _
lemma eval_010_evZ0 (P : Mv3 K) :
    Mv.eval ![0, 1, 0] (evZ0 P) = Mv.eval ![0, 1, 0] P := by
  induction P using Mv.induction_on with
  | C a => simp [evZ0]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]; congr 1
    fin_cases i <;> simp [evZ0]
lemma v166 {i : Fin 3} {A B : Mv3 K} (m : ℕ)
    (hndvd : ¬ Mv.X i ∣ A) (hdvd : Mv.X i ^ m ∣ A * B) :
    Mv.X i ^ m ∣ B := by
  induction m generalizing B with
  | zero => simp
  | succ m ih =>
    have h1 : Mv.X i ∣ A * B :=
      (dvd_pow_self _ (Nat.succ_ne_zero m)).trans hdvd
    have hB1 : Mv.X i ∣ B :=
      ((v89 i).dvd_or_dvd h1).resolve_left hndvd
    rcases hB1 with ⟨B', rfl⟩
    have hm : Mv.X i ^ m ∣ A * B' := by
      rcases hdvd with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply mul_left_cancel₀ (Mv.X_ne_zero (R := K) i)
      calc Mv.X i * (A * B') = A * (Mv.X i * B') := by ring
        _ = Mv.X i ^ (m + 1) * q := hq
        _ = Mv.X i * (Mv.X i ^ m * q) := by rw [pow_succ']; ring
    rcases ih hm with ⟨q, hq⟩
    exact ⟨q, by rw [hq, pow_succ']; ring⟩
lemma v175 {F : Mv3 K}
    (h010 : Mv.eval ![0, 1, 0] F ≠ 0) (m k : ℕ) :
    ∀ {A B : Mv3 K}, F ∣ Mv.X 2 ^ k * A - Mv.X 0 ^ m * B → ∃ Q : Mv3 K, F ∣ B - Mv.X 2 ^ k * Q := by
  have hX0_ndvd : ¬ Mv.X 0 ∣ evZ0 F := by
    rintro ⟨u, hu⟩
    have := congr_arg (Mv.eval ![0, 1, 0]) hu
    rw [eval_010_evZ0] at this
    simp only [map_mul, Mv.eval_X, Mx.cons_val_zero, zero_mul] at this
    exact h010 this
  have hX2_ndvd_X0 : ¬ Mv.X 2 ∣ (Mv.X 0 : Mv3 K) := by
    rintro ⟨u, hu⟩
    have := congr_arg (Mv.eval ![1, 0, 0]) hu
    simp only [map_mul, Mv.eval_X, Mx.cons_val_zero, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, zero_mul] at this
    exact one_ne_zero this
  induction k with
  | zero =>
    intro A B _; exact ⟨B, by simp⟩
  | succ k ih =>
    intro A B ⟨H, hH⟩
    have hev := congr_arg evZ0 hH
    have hev2 : evZ0 (Mv.X 2 : Mv3 K) = 0 := by simp [evZ0]
    have hev0 : evZ0 (Mv.X 0 : Mv3 K) = Mv.X 0 := by simp [evZ0]
    simp only [map_sub, map_mul, map_pow, hev2, hev0, zero_pow (Nat.succ_ne_zero k), zero_mul, zero_sub] at hev
    have hX0m_dvd_evH : Mv.X 0 ^ m ∣ evZ0 H := by
      apply v166 m hX0_ndvd
      exact ⟨-evZ0 B, by rw [← hev]; ring⟩
    rcases hX0m_dvd_evH with ⟨H₀, hH₀⟩
    rcases v162 H with ⟨H₁, hH₁⟩
    have hH_split : H = Mv.X 0 ^ m * H₀ + Mv.X 2 * H₁ := by
      linear_combination hH₁ + hH₀
    have hrearr : Mv.X 0 ^ m * (B + F * H₀) = Mv.X 2 * (Mv.X 2 ^ k * A - F * H₁) := by
      rw [pow_succ', mul_assoc] at hH
      linear_combination -hH - F * hH_split
    have hX2_ndvd_X0m : ¬ Mv.X 2 ∣ (Mv.X 0 ^ m : Mv3 K) :=
      fun h => hX2_ndvd_X0 ((v89 2).dvd_of_dvd_pow h)
    have hX2_dvd_B : Mv.X 2 ∣ B + F * H₀ :=
      ((v89 2).dvd_or_dvd ⟨_, hrearr⟩).resolve_left hX2_ndvd_X0m
    rcases hX2_dvd_B with ⟨Q₁, hQ₁⟩
    have hstep : Mv.X 2 ^ k * A - Mv.X 0 ^ m * Q₁ = F * H₁ := by
      apply mul_left_cancel₀ (Mv.X_ne_zero (R := K) 2)
      calc Mv.X 2 * (Mv.X 2 ^ k * A - Mv.X 0 ^ m * Q₁)
          = Mv.X 2 * (Mv.X 2 ^ k * A) - Mv.X 0 ^ m * (Mv.X 2 * Q₁) := by ring
        _ = Mv.X 2 * (Mv.X 2 ^ k * A) - Mv.X 0 ^ m * (B + F * H₀) := by rw [hQ₁]
        _ = Mv.X 2 * (F * H₁) := by linear_combination -hrearr
    obtain ⟨Q, hQ⟩ := ih ⟨H₁, hstep⟩
    refine ⟨Q, ?_⟩
    have hB1 : F ∣ B - Mv.X 2 * Q₁ := ⟨-H₀, by linear_combination hQ₁⟩
    have hB2 : B - Mv.X 2 ^ (k + 1) * Q = (B - Mv.X 2 * Q₁) + Mv.X 2 * (Q₁ - Mv.X 2 ^ k * Q) := by
      rw [pow_succ']; ring
    rw [hB2]
    exact dvd_add hB1 (dvd_mul_of_dvd_right hQ _)
lemma v57 {A B : Mv3 K} {a b : ℕ}
    (hA : A.IsHomogeneous a) :
    Mv.homogeneousComponent (a + b) (A * B) = A * Mv.homogeneousComponent b B := by
  ext m
  rw [Mv.coeff_homogeneousComponent]
  by_cases hm : Fu.degree m = a + b
  · rw [if_pos hm]
    rw [Mv.coeff_mul, Mv.coeff_mul]
    apply sum_congr rfl
    intro xy hxy
    have hxy' : xy.1 + xy.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
    by_cases hA0 : A.coeff xy.1 = 0
    · simp [hA0]
    · have h1 : Fu.degree xy.1 = a := by
        have hdeg := v10 hA hA0
        rw [Fu.degree_apply, sum_subset (subset_univ _) (fun j _ hj => Fu.notMem_support_iff.mp hj), Fi.sum_univ_three]
        exact hdeg
      have h2 : Fu.degree xy.2 = b := by
        have hsum : Fu.degree (xy.1 + xy.2) = Fu.degree xy.1 + Fu.degree xy.2 :=
          map_add Fu.degree xy.1 xy.2
        rw [hxy', hm, h1] at hsum; omega
      rw [Mv.coeff_homogeneousComponent, if_pos h2]
  · rw [if_neg hm]
    have hprod_hom : (A * Mv.homogeneousComponent b B).IsHomogeneous (a + b) :=
      hA.mul (Mv.homogeneousComponent_isHomogeneous b B)
    symm
    by_contra hne
    have hdeg := v10 hprod_hom hne
    apply hm
    rw [Fu.degree_apply, sum_subset (subset_univ _) (fun j _ hj => Fu.notMem_support_iff.mp hj), Fi.sum_univ_three]
    exact hdeg
theorem v192 {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    {L : Type*} [Field L] [IsAlgClosed L] [CharP L p]
    {F : Mv3 L} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F) (hd3 : 3 ≤ d) (hdp : 2 * d < p)
    (h010 : Mv.eval ![0, 1, 0] F ≠ 0) :
    ∃ Wt : Mv3 L, Wt.IsHomogeneous (2 * p + 10 * d - 20) ∧ ¬ F ∣ Wt ∧ F ∣ fWron p (derivZ F) cMon - Mv.X 2 ^ 10 * Wt ∧ F ∣ fWron p (derivX F) cMon - Mv.X 0 ^ 10 * Wt ∧ F ∣ fWron p (derivY F) cMon - Mv.X 1 ^ 10 * Wt := by
  obtain ⟨hcompatX, hcompatY⟩ := v181 hp hF hF_irr hd3 (by omega) h010
  obtain ⟨Q, ⟨R, hQR⟩⟩ := v175 h010 10 10 hcompatX
  set e := 2 * p + 10 * d - 20
  set Wt := Mv.homogeneousComponent e Q
  have hWt_hom : Wt.IsHomogeneous e := Mv.homogeneousComponent_isHomogeneous e Q
  have hWZ_hom : (fWron p (derivZ F) cMon).IsHomogeneous (10 + e) := by
    have := v32 p hF (by omega) (derivZ F)
      (fun hP hk => v65 hF hP (by omega) hk)
    rwa [show 2 * p + 10 * d - 10 = 10 + e by omega] at this
  have hX2_10_hom : (Mv.X 2 ^ 10 : Mv3 L).IsHomogeneous 10 := by
    simpa using (Mv.isHomogeneous_X L (2 : Fin 3)).pow 10
  have hZ : F ∣ fWron p (derivZ F) cMon - Mv.X 2 ^ 10 * Wt := by
    have hcomp := congr_arg (Mv.homogeneousComponent (10 + e)) hQR
    have hWZ_self : Mv.homogeneousComponent (10 + e) (fWron p (derivZ F) cMon) = fWron p (derivZ F) cMon := by
      ext m; rw [Mv.coeff_homogeneousComponent]
      split_ifs with hm
      · rfl
      · symm; by_contra hne
        have hdeg := v10 hWZ_hom hne
        apply hm; rw [Fu.degree_apply, sum_subset (subset_univ _) (fun j _ hj => Fu.notMem_support_iff.mp hj), Fi.sum_univ_three]; exact hdeg
    rw [map_sub, hWZ_self, v57 hX2_10_hom] at hcomp
    have hde : 10 + e = d + (2 * p + 9 * d - 10) := by omega
    rw [hde, v57 hF] at hcomp
    exact ⟨Mv.homogeneousComponent (2 * p + 9 * d - 10) R, hcomp⟩
  have hF_prime : Prime F := Ufm.irreducible_iff_prime.mp hF_irr
  have hF_ndvd_X2 : ¬ F ∣ Mv.X 2 := by
    rintro ⟨u, hu⟩
    have hX2_irr : Irreducible (Mv.X 2 : Mv3 L) :=
      (v89 2).irreducible
    rcases hX2_irr.isUnit_or_isUnit hu with hFu | huu
    · exact hF_irr.not_isUnit hFu
    · rcases huu with ⟨v, hv⟩
      have hF_eq : F = Mv.X 2 * ((v⁻¹ : (Mv3 L)ˣ) : Mv3 L) := by
        rw [hu, ← hv, mul_assoc, Units.mul_inv, mul_one]
      have hev := congr_arg (Mv.eval ![0, 1, 0]) hF_eq
      simp only [map_mul, Mv.eval_X, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, zero_mul] at hev
      exact h010 hev
  have hF_ndvd_X2_10 : ¬ F ∣ Mv.X 2 ^ 10 :=
    fun h => hF_ndvd_X2 (hF_prime.dvd_of_dvd_pow h)
  have hX : F ∣ fWron p (derivX F) cMon - Mv.X 0 ^ 10 * Wt := by
    have hmul : F ∣ Mv.X 2 ^ 10 * (fWron p (derivX F) cMon - Mv.X 0 ^ 10 * Wt) := by
      have hid : Mv.X 2 ^ 10 * (fWron p (derivX F) cMon - Mv.X 0 ^ 10 * Wt) = (Mv.X 2 ^ 10 * fWron p (derivX F) cMon - Mv.X 0 ^ 10 * fWron p (derivZ F) cMon) + Mv.X 0 ^ 10 * (fWron p (derivZ F) cMon - Mv.X 2 ^ 10 * Wt) := by ring
      rw [hid]
      exact dvd_add hcompatX (dvd_mul_of_dvd_right hZ _)
    exact (hF_prime.dvd_or_dvd hmul).resolve_left hF_ndvd_X2_10
  have hY : F ∣ fWron p (derivY F) cMon - Mv.X 1 ^ 10 * Wt := by
    have hmul : F ∣ Mv.X 2 ^ 10 * (fWron p (derivY F) cMon - Mv.X 1 ^ 10 * Wt) := by
      have hid : Mv.X 2 ^ 10 * (fWron p (derivY F) cMon - Mv.X 1 ^ 10 * Wt) = (Mv.X 2 ^ 10 * fWron p (derivY F) cMon - Mv.X 1 ^ 10 * fWron p (derivZ F) cMon) + Mv.X 1 ^ 10 * (fWron p (derivZ F) cMon - Mv.X 2 ^ 10 * Wt) := by ring
      rw [hid]
      exact dvd_add hcompatY (dvd_mul_of_dvd_right hZ _)
    exact (hF_prime.dvd_or_dvd hmul).resolve_left hF_ndvd_X2_10
  have hndvd : ¬ F ∣ Wt := by
    intro hdvd
    apply v201 hp hp7 hF hF_irr hd3 hdp h010
    have hid : fWron p (derivZ F) cMon = (fWron p (derivZ F) cMon - Mv.X 2 ^ 10 * Wt) + Mv.X 2 ^ 10 * Wt := by ring
    rw [hid]
    exact dvd_add hZ (dvd_mul_of_dvd_right hdvd _)
  exact ⟨Wt, hWt_hom, hndvd, hZ, hX, hY⟩
end ProjectiveWronskian
section LinearSubstAndSingular
variable {K : Type*} [Field K]
noncomputable def sMat (T : Mat3 K) :
    Mv3 K →ₐ[K] Mv3 K :=
  Mv.aeval (fun i => ∑ j : Fin 3, Mv.C (T i j) * Mv.X j)
lemma v50 (T : Mat3 K) (v : Fin 3 → K) (P : Mv3 K) :
    Mv.eval v (sMat T P) = Mv.eval (T.mulVec v) P := by
  induction P using Mv.induction_on with
  | C a => simp [sMat]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]; congr 1
    simp [sMat, Mx.mulVec, dotProduct]
lemma v47 (T₁ T₂ : Mat3 K) (P : Mv3 K) :
    sMat T₂ (sMat T₁ P) = sMat (T₁ * T₂) P := by
  have hX : ∀ (M : Mat3 K) (k : Fin 3), sMat M (Mv.X k) = ∑ j : Fin 3, Mv.C (M k j) * Mv.X j :=
    fun M k => by simp [sMat]
  have hC : ∀ (M : Mat3 K) (c : K), sMat M (Mv.C c) = Mv.C c :=
    fun M c => by simp [sMat]
  induction P using Mv.induction_on with
  | C a => rw [hC, hC, hC]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    apply congr_arg (sMat (T₁ * T₂) p * ·)
    rw [hX T₁ i, hX (T₁ * T₂) i, map_sum]
    simp only [map_mul, hC, hX, mul_sum, Mx.mul_apply, map_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro j _
    ring
lemma v130 (P : Mv3 K) :
    sMat (1 : Mat3 K) P = P := by
  induction P using Mv.induction_on with
  | C a => simp [sMat]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hp]; congr 1
    simp [sMat, Mx.one_apply]
lemma v25 (T : Mat3 K) {P : Mv3 K} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    (sMat T P).IsHomogeneous d := by
  rw [Mv.as_sum P, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro m hm
  have hdeg := v10 hP (Mv.mem_support_iff.mp hm)
  rw [Mv.monomial_eq, map_mul]
  have hC : sMat T (Mv.C (P.coeff m)) = Mv.C (P.coeff m) := by simp [sMat]
  rw [hC]
  apply v07
  rw [Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
  have hlin : ∀ i : Fin 3, (sMat T (Mv.X i)).IsHomogeneous 1 := by
    intro i
    simp only [sMat, Mv.aeval_X]
    apply MvPolynomial.IsHomogeneous.sum; intro j _
    exact v07 _ (Mv.isHomogeneous_X K j)
  have hpow : ∀ i : Fin 3, (sMat T (Mv.X i ^ m i)).IsHomogeneous (m i) := by
    intro i; rw [map_pow]; simpa using (hlin i).pow (m i)
  have h := ((hpow 0).mul (hpow 1)).mul (hpow 2)
  rwa [hdeg] at h
lemma v88 {T Tinv : Mat3 K}
    (h1 : T * Tinv = 1) (h2 : Tinv * T = 1) {F : Mv3 K}
    (hF : Irreducible F) : Irreducible (sMat T F) := by
  let e : Mv3 K ≃+* Mv3 K :=
    { toFun := sMat T
      invFun := sMat Tinv
      left_inv := fun P => by rw [v47, h1, v130]
      right_inv := fun P => by rw [v47, h2, v130]
      map_mul' := map_mul _
      map_add' := map_add _ }
  exact (MulEquiv.irreducible_iff e.toMulEquiv).mpr hF
lemma v131 {T Tinv : Mat3 K}
    (h1 : T * Tinv = 1) (_h2 : Tinv * T = 1) (A B : Mv3 K) :
    sMat T A ∣ sMat T B ↔ A ∣ B := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨sMat Tinv q, ?_⟩
    have := congr_arg (sMat Tinv) hq
    rw [map_mul, v47, v47, h1, v130, v130] at this
    exact this
  · rintro ⟨q, rfl⟩
    exact ⟨sMat T q, map_mul _ A q⟩
set_option maxHeartbeats 800000 in
lemma v67 (T : Mat3 K) (j : Fin 3) (P : Mv3 K) :
    Mv.pderiv j (sMat T P) = ∑ i : Fin 3, Mv.C (T i j) * sMat T (Mv.pderiv i P) := by
  induction P using Mv.induction_on with
  | C a => simp [sMat]
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, sum_add_distrib]
  | mul_X p k hp =>
    have hlin : Mv.pderiv j (sMat T (Mv.X k)) = Mv.C (T k j) := by
      simp only [sMat, Mv.aeval_X, map_sum, Dr.leibniz, smul_eq_mul, Mv.pderiv_C, mul_zero, add_zero, Mv.pderiv_X, Pi.single_apply, mul_ite, mul_one, sum_ite_eq', mem_univ, ↓reduceIte]
    rw [map_mul, Dr.leibniz, hp, hlin]
    simp only [Dr.leibniz, smul_eq_mul, Mv.pderiv_X, Pi.single_apply, map_add, map_mul, mul_sum]
    have hsingle : ∑ i : Fin 3, Mv.C (T i j) * (sMat T p * sMat T (if k = i then 1 else 0)) = sMat T p * Mv.C (T k j) := by
      have hterm : ∀ i : Fin 3, Mv.C (T i j) * (sMat T p * sMat T (if k = i then 1 else 0)) = if k = i then sMat T p * Mv.C (T k j) else 0 := by
        intro i; by_cases h : k = i
        · subst h
          rw [if_pos rfl, if_pos rfl, map_one, mul_one, mul_comm]
        · rw [if_neg h, if_neg h, map_zero, mul_zero, mul_zero]
      simp only [hterm, sum_ite_eq, mem_univ, ↓reduceIte]
    rw [show ∑ x : Fin 3, Mv.C (T x j) * (sMat T p * sMat T (if k = x then 1 else 0) + sMat T (Mv.X k) * sMat T (Mv.pderiv x p)) = (∑ x : Fin 3, Mv.C (T x j) * (sMat T p * sMat T (if k = x then 1 else 0))) + ∑ x : Fin 3, Mv.C (T x j) * (sMat T (Mv.X k) * sMat T (Mv.pderiv x p))
      by rw [← sum_add_distrib]; apply sum_congr rfl; intro x _; ring]
    rw [hsingle]
    congr 1
    apply sum_congr rfl; intro i _; ring
def cycMat (K : Type*) [CommRing K] : Mat3 K :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]
lemma v68 : cycMat K * cycMat K * cycMat K = 1 := by
  refine Mx.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [cycMat, Mx.mul_apply, Fi.sum_univ_three]
lemma v73 (P : Mv3 K) :
    Mv.pderiv 0 (sMat (cycMat K) P) = sMat (cycMat K) (Mv.pderiv 2 P) ∧
    Mv.pderiv 1 (sMat (cycMat K) P) = sMat (cycMat K) (Mv.pderiv 0 P) ∧
    Mv.pderiv 2 (sMat (cycMat K) P) = sMat (cycMat K) (Mv.pderiv 1 P) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { rw [v67, Fi.sum_univ_three]; simp [cycMat] }
lemma v186 (F P : Mv3 K) :
    derivZ (sMat (cycMat K) F) (sMat (cycMat K) P) = sMat (cycMat K) (derivY F P) := by
  have ⟨hF0, hF1, _⟩ := v73 F
  have ⟨hP0, hP1, _⟩ := v73 P
  change Mv.pderiv 1 (sMat (cycMat K) F) * Mv.pderiv 0 (sMat (cycMat K) P) - Mv.pderiv 0 (sMat (cycMat K) F) * Mv.pderiv 1 (sMat (cycMat K) P) = _
  rw [hF0, hF1, hP0, hP1]
  simp only [derivY, map_sub, map_mul]
lemma v187 (F P : Mv3 K) :
    derivY (sMat (cycMat K) F) (sMat (cycMat K) P) = sMat (cycMat K) (derivX F P) := by
  have ⟨hF0, _, hF2⟩ := v73 F
  have ⟨hP0, _, hP2⟩ := v73 P
  change Mv.pderiv 0 (sMat (cycMat K) F) * Mv.pderiv 2 (sMat (cycMat K) P) - Mv.pderiv 2 (sMat (cycMat K) F) * Mv.pderiv 0 (sMat (cycMat K) P) = _
  rw [hF0, hF2, hP0, hP2]
  simp only [derivX, map_sub, map_mul]
lemma v146 :
    ∃ σ : Eqv.Perm (Fin 6), ∀ j : Fin 6, sMat (cycMat K) (cMon j) = cMon (σ j) := by
  let σ : Eqv.Perm (Fin 6) :=
    (Eqv.swap (0 : Fin 6) 3 * Eqv.swap 3 5) * (Eqv.swap (1 : Fin 6) 4 * Eqv.swap 4 2)
  have hσ : ∀ j : Fin 6, σ j = ![3, 4, 1, 5, 2, 0] j := by decide
  refine ⟨σ, fun j => ?_⟩
  have hX0 : sMat (cycMat K) (Mv.X 0) = Mv.X 1 := by
    simp [sMat, cycMat, Fi.sum_univ_three]
  have hX1 : sMat (cycMat K) (Mv.X 1) = Mv.X 2 := by
    simp [sMat, cycMat, Fi.sum_univ_three]
  have hX2 : sMat (cycMat K) (Mv.X 2) = Mv.X 0 := by
    simp [sMat, cycMat, Fi.sum_univ_three]
  rw [hσ j]
  fin_cases j <;>
    simp [cMon, hX0, hX1, hX2, map_pow, map_mul, mul_comm]
lemma v113 (p : ℕ) (F : Mv3 K) :
    ∃ s : K, (s = 1 ∨ s = -1) ∧ fWron p (derivZ (sMat (cycMat K) F)) cMon = Mv.C s * sMat (cycMat K) (fWron p (derivY F) cMon) := by
  obtain ⟨σ, hσ⟩ := v146 (K := K)
  have hiter : ∀ (n : ℕ) (P : Mv3 K), (derivZ (sMat (cycMat K) F))^[n] (sMat (cycMat K) P) = sMat (cycMat K) ((derivY F)^[n] P) := by
    intro n
    induction n with
    | zero => intro P; rfl
    | succ n ih =>
      intro P
      simp only [Fn.iterate_succ_apply']
      rw [ih P, v186]
  have hmat : (sMat (cycMat K)).toRingHom.mapMatrix (v08 p (derivY F) cMon) = (v08 p (derivZ (sMat (cycMat K) F)) cMon).submatrix id σ := by
    refine Mx.ext fun i j => ?_
    simp only [Rh.mapMatrix_apply, Mx.map_apply, Mx.submatrix_apply, id_eq]
    have hj := hσ j
    have h1 := hiter 1 (cMon j)
    have h2 := hiter 2 (cMon j)
    have h3 := hiter 3 (cMon j)
    have h4 := hiter 4 (cMon j)
    simp only [Fn.iterate_succ, Fn.iterate_zero, Fn.comp_apply, id_eq] at h1 h2 h3 h4
    fin_cases i
    · simp only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, map_pow, hj]
    · simp only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj]
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h1.symm
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h2.symm
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h3.symm
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h4.symm
  have hdet := congr_arg Mx.det hmat
  rw [← Rh.map_det, Mx.det_permute'] at hdet
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [hs, Units.val_one, Int.cast_one, one_mul] at hdet
    simpa [fWron] using hdet.symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hdet
    have h1 : sMat (cycMat K) (fWron p (derivY F) cMon) = -fWron p (derivZ (sMat (cycMat K) F)) cMon := hdet
    rw [h1, map_neg, map_one]; ring
lemma v139 (p : ℕ) (F : Mv3 K) :
    ∃ s : K, (s = 1 ∨ s = -1) ∧ fWron p (derivZ (sMat (cycMat K * cycMat K) F)) cMon = Mv.C s * sMat (cycMat K * cycMat K) (fWron p (derivX F) cMon) := by
  obtain ⟨s₁, hs₁, h1⟩ := v113 p (sMat (cycMat K) F)
  obtain ⟨σ, hσ⟩ := v146 (K := K)
  have hiter : ∀ (n : ℕ) (P : Mv3 K), (derivY (sMat (cycMat K) F))^[n] (sMat (cycMat K) P) = sMat (cycMat K) ((derivX F)^[n] P) := by
    intro n
    induction n with
    | zero => intro P; rfl
    | succ n ih =>
      intro P
      simp only [Fn.iterate_succ_apply']
      rw [ih P, v187]
  have hmat : (sMat (cycMat K)).toRingHom.mapMatrix (v08 p (derivX F) cMon) = (v08 p (derivY (sMat (cycMat K) F)) cMon).submatrix id σ := by
    refine Mx.ext fun i j => ?_
    simp only [Rh.mapMatrix_apply, Mx.map_apply, Mx.submatrix_apply, id_eq]
    have hj := hσ j
    have h1' := hiter 1 (cMon j)
    have h2' := hiter 2 (cMon j)
    have h3' := hiter 3 (cMon j)
    have h4' := hiter 4 (cMon j)
    simp only [Fn.iterate_succ, Fn.iterate_zero, Fn.comp_apply, id_eq] at h1' h2' h3' h4'
    fin_cases i
    · simp only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, map_pow, hj]
    · simp only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj]
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h1'.symm
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h2'.symm
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h3'.symm
    · simpa only [v08, Mx.of_apply, Ah.toRingHom_eq_coe, Rh.coe_coe, hj] using h4'.symm
  have hdet := congr_arg Mx.det hmat
  rw [← Rh.map_det, Mx.det_permute'] at hdet
  have h2 : ∃ s₂ : K, (s₂ = 1 ∨ s₂ = -1) ∧ fWron p (derivY (sMat (cycMat K) F)) cMon = Mv.C s₂ * sMat (cycMat K) (fWron p (derivX F) cMon) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hs, Units.val_one, Int.cast_one, one_mul] at hdet; simpa [fWron] using hdet.symm
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hdet
      have : sMat (cycMat K) (fWron p (derivX F) cMon) = -fWron p (derivY (sMat (cycMat K) F)) cMon := hdet
      rw [this, map_neg, map_one]; ring
  rcases h2 with ⟨s₂, hs₂, h2eq⟩
  refine ⟨s₁ * s₂, ?_, ?_⟩
  · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp
  · have hCs : sMat (cycMat K) (Mv.C s₂) = Mv.C s₂ := by simp [sMat]
    rw [← v47, h1, h2eq, map_mul, hCs, v47, map_mul, mul_assoc]
noncomputable def evalZ1 : Mv3 K →ₐ[K] Mv2 K :=
  Mv.aeval ![Mv.X 0, Mv.X 1, 1]
noncomputable def v43 (G : Mv2 K) : v35 (Mv2 K) where
  toFun P := Mv.pderiv 1 G * Mv.pderiv 0 P - Mv.pderiv 0 G * Mv.pderiv 1 P
  map_add' P Q := by simp only [map_add]; ring
  leibniz' P Q := by simp only [Dr.leibniz]; ring
lemma v63 (P : Mv3 K) :
    evalZ1 (Mv.pderiv 0 P) = Mv.pderiv 0 (evalZ1 P) ∧
    evalZ1 (Mv.pderiv 1 P) = Mv.pderiv 1 (evalZ1 P) := by
  have hX0 : evalZ1 (Mv.X 0 : Mv3 K) = Mv.X 0 := by simp [evalZ1]
  have hX1 : evalZ1 (Mv.X 1 : Mv3 K) = Mv.X 1 := by simp [evalZ1]
  have hX2 : evalZ1 (Mv.X 2 : Mv3 K) = 1 := by simp [evalZ1]
  induction P using Mv.induction_on with
  | C a => simp [evalZ1]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rcases v03 i with rfl | rfl | rfl
    · constructor <;>
        simp [Dr.leibniz, smul_eq_mul, map_add, map_mul, hX0, hp.1, hp.2]
    · constructor <;>
        simp [Dr.leibniz, smul_eq_mul, map_add, map_mul, hX1, hp.1, hp.2]
    · constructor <;>
        simp [Dr.leibniz, smul_eq_mul, map_mul, hX2, hp.1, hp.2]
lemma evalZ1_derivZ (F P : Mv3 K) :
    evalZ1 (derivZ F P) = v43 (evalZ1 F) (evalZ1 P) := by
  simp only [derivZ, v43, map_sub, map_mul, (v63 F).1, (v63 F).2, (v63 P).1, (v63 P).2]
def v39 (k : ℕ) (P : Mv2 K) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, P.coeff m ≠ 0 → k ≤ m 0 + m 1
lemma v163 (P : Mv2 K) : v39 0 P :=
  fun _ _ => Nat.zero_le _
lemma v137 (k : ℕ) : v39 k (0 : Mv2 K) :=
  fun _ h => absurd (Mv.coeff_zero _) h
lemma v81 {k₁ k₂ : ℕ} {P : Mv2 K}
    (hle : k₁ ≤ k₂) (hP : v39 k₂ P) : v39 k₁ P :=
  fun m hm => hle.trans (hP m hm)
lemma v205 {k : ℕ} {P Q : Mv2 K}
    (hP : v39 k P) (hQ : v39 k Q) : v39 k (P + Q) := by
  intro m hm
  rw [Mv.coeff_add] at hm
  by_cases h1 : P.coeff m = 0
  · rw [h1, zero_add] at hm; exact hQ m hm
  · exact hP m h1
lemma v204 {k : ℕ} {P : Mv2 K}
    (hP : v39 k P) : v39 k (-P) := by
  intro m hm; rw [Mv.coeff_neg] at hm; exact hP m (neg_ne_zero.mp hm)
lemma v203 {k : ℕ} {P Q : Mv2 K}
    (hP : v39 k P) (hQ : v39 k Q) : v39 k (P - Q) := by
  rw [sub_eq_add_neg]; exact v205 hP (v204 hQ)
lemma vanOrd2_sum {ι : Type*} {s : Finset ι} {k : ℕ} {f : ι → Mv2 K}
    (hf : ∀ i ∈ s, v39 k (f i)) : v39 k (∑ i ∈ s, f i) := by
  classical
  induction s using Fs.induction_on with
  | empty => simp [v137]
  | insert a s ha ih =>
    rw [Fs.sum_insert ha]
    exact v205 (hf a (mem_insert_self a s))
      (ih (fun i hi => hf i (mem_insert_of_mem hi)))
lemma v123 {k₁ k₂ : ℕ} {P Q : Mv2 K}
    (hP : v39 k₁ P) (hQ : v39 k₂ Q) : v39 (k₁ + k₂) (P * Q) := by
  intro m hm
  rw [Mv.coeff_mul] at hm
  obtain ⟨⟨a, b⟩, hab, hne⟩ := Fs.exists_ne_zero_of_sum_ne_zero hm
  have hab' : a + b = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have h1 := hP a (left_ne_zero_of_mul hne)
  have h2 := hQ b (right_ne_zero_of_mul hne)
  have h0 : m 0 = a 0 + b 0 := by rw [← hab', Fu.add_apply]
  have h1' : m 1 = a 1 + b 1 := by rw [← hab', Fu.add_apply]
  omega
lemma v177 {k : ℕ} {P : Mv2 K}
    (hP : v39 k P) (n : ℕ) : v39 (n * k) (P ^ n) := by
  induction n with
  | zero => simp [v163]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact v123 ih hP
lemma v154 (i : Fin 2) : v39 1 (Mv.X i : Mv2 K) := by
  intro m hm
  rw [Mv.coeff_X] at hm
  split_ifs at hm with h
  · subst h; rcases v151 i with rfl | rfl <;> simp
  · exact absurd rfl hm
lemma v107 {k : ℕ} {P : Mv2 K}
    (hP : v39 k P) (i : Fin 2) : v39 (k - 1) (Mv.pderiv i P) := by
  intro m hm
  rw [Mv.coeff_pderiv] at hm
  have hne : P.coeff (m + Fu.single i 1) ≠ 0 := left_ne_zero_of_mul hm
  have h := hP (m + Fu.single i 1) hne
  rcases v151 i with rfl | rfl <;> simp at h <;> omega
lemma v87 {m k : ℕ} {G P : Mv2 K}
    (hG : v39 m G) (hP : v39 k P) :
    v39 ((m - 1) + (k - 1)) (v43 G P) :=
  v203
    (v123 (v107 hG 1) (v107 hP 0))
    (v123 (v107 hG 0) (v107 hP 1))
lemma v119 {G : Mv2 K}
    (h0 : Mv.eval 0 G = 0)
    (hx : Mv.eval 0 (Mv.pderiv 0 G) = 0)
    (hy : Mv.eval 0 (Mv.pderiv 1 G) = 0) :
    v39 2 G := by
  intro m hm
  by_contra hlt
  have hle : m 0 + m 1 ≤ 1 := by omega
  have hcoeff0 : ∀ f : Mv2 K, Mv.eval 0 f = f.coeff 0 := by
    intro f; rw [Mv.eval_zero, Mv.constantCoeff_eq]
  have h0c : G.coeff 0 = 0 := by rwa [← hcoeff0]
  have hxc : G.coeff (Fu.single 0 1) = 0 := by
    have := hcoeff0 (Mv.pderiv 0 G)
    rw [hx, Mv.coeff_pderiv, zero_add] at this
    simpa using this.symm
  have hyc : G.coeff (Fu.single 1 1) = 0 := by
    have := hcoeff0 (Mv.pderiv 1 G)
    rw [hy, Mv.coeff_pderiv, zero_add] at this
    simpa using this.symm
  have hcases : m = 0 ∨ m = Fu.single 0 1 ∨ m = Fu.single 1 1 := by
    by_cases h0m : m 0 = 0
    · by_cases h1m : m 1 = 0
      · left; ext i; fin_cases i <;> simp [h0m, h1m]
      · right; right; ext i; fin_cases i <;> simp [h0m]; omega
    · right; left; ext i; fin_cases i <;> simp; omega; omega
  rcases hcases with rfl | rfl | rfl
  · exact hm h0c
  · exact hm hxc
  · exact hm hyc
lemma v134 {p m : ℕ} (hp1 : 1 ≤ p) (hm : 2 ≤ m)
    {G : Mv2 K} (hG : v39 m G) :
    v39 (10 * m - 15)
      (fWron p (v43 G)
        ![1, Mv.X 0, Mv.X 1, Mv.X 0 ^ 2, Mv.X 0 * Mv.X 1, Mv.X 1 ^ 2]) := by
  set u : Mv2 K := Mv.X 0
  set v : Mv2 K := Mv.X 1
  let g : Fin 6 → Mv2 K := ![1, u, v, u ^ 2, u * v, v ^ 2]
  let E : Matrix (Fin 6) (Fin 6) (Mv2 K) :=
    !![1, -1, 0, 0, 0, 0; 0,  1, 0, 0, 0, 0; 0,  0, 1, 0, 0, 0; 0,  0, 0, 1, 0, 0; 0,  0, 0, 0, 1, 0; 0,  0, 0, 0, 0, 1]
  have hE_det : E.det = 1 := by
    have htri : E.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      fin_cases i <;> fin_cases j <;> simp_all [E]
    rw [Mx.det_of_isUpperTriangular htri, Fi.prod_univ_six]; simp [E]
  set M := E * v08 p (v43 G) g
  have hdet_eq : fWron p (v43 G) g = M.det := by
    rw [fWron, ← one_mul (v08 p (v43 G) g).det, ← hE_det, ← Mx.det_mul]
  rw [hdet_eq, Mx.det_apply]
  apply vanOrd2_sum
  intro σ _
  have hD1 : v43 G 1 = 0 := (v43 G).map_one
  have hD0 : v43 G 0 = 0 := by
    have := (v43 G).map_add 0 0; rw [add_zero] at this
    exact add_left_cancel (this.symm.trans (add_zero _).symm)
  have hM_col0 : ∀ i : Fin 6, M i 0 = if i = 1 then 1 else 0 := by
    intro i
    simp only [M, Mx.mul_apply, Fi.sum_univ_six]
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [E, v08, g, v20, v19, v18, v15, hD1, hD0]
  by_cases hσ0 : σ 0 = 1
  ·
    have hg_ord : ∀ j : Fin 6, j ≠ 0 → v39 1 (g j) := by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · exact v154 0
      · exact v154 1
      · exact v81 (by omega) (v177 (v154 0) 2)
      · exact v81 (by omega) (v123 (v154 0) (v154 1))
      · exact v81 (by omega) (v177 (v154 1) 2)
    let r : Fin 6 → ℕ := ![1, 0, m - 1, 2 * m - 3, 3 * m - 5, 4 * m - 7]
    have hM_ord : ∀ (i j : Fin 6), j ≠ 0 → v39 (r i) (M i j) := by
      intro i j hj
      have hj1 := hg_ord j hj
      have hDj1 : v39 (m - 1) (v43 G (g j)) := by
        simpa using v87 hG hj1
      have hDj2 : v39 (2 * m - 3) (v43 G (v43 G (g j))) := by
        have := v87 hG hDj1
        exact v81 (by omega) this
      have hDj3 : v39 (3 * m - 5) (v43 G (v43 G (v43 G (g j)))) := by
        have := v87 hG hDj2
        exact v81 (by omega) this
      have hDj4 : v39 (4 * m - 7) (v43 G (v43 G (v43 G (v43 G (g j))))) := by
        have := v87 hG hDj3
        exact v81 (by omega) this
      simp only [M, Mx.mul_apply, Fi.sum_univ_six]
      rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [E, v08, Mx.of_apply, r, v34, v33, v20, v19, v18, v15, one_mul, neg_mul, zero_mul, add_zero]
        rw [← sub_eq_add_neg]
        exact v203 (v81 (by omega) (v177 hj1 p)) hj1
      · exact v163 _
      · simpa [E, v08, r, v34, v33, v20, v19, v18, v15] using hDj1
      · simpa [E, v08, r, v34, v33, v20, v19, v18, v15] using hDj2
      · simpa [E, v08, r, v34, v33, v20, v19, v18, v15] using hDj3
      · simpa [E, v08, r, v34, v33, v20, v19, v18, v15] using hDj4
    have hprod_ord : v39 (∑ j : Fin 6, r (σ j)) (∏ j : Fin 6, M (σ j) j) := by
      have hgen : ∀ s : Finset (Fin 6), v39 (∑ j ∈ s, r (σ j)) (∏ j ∈ s, M (σ j) j) := by
        intro s
        induction s using Fs.induction_on with
        | empty => simp [v163]
        | insert a s ha ih =>
          rw [Fs.sum_insert ha, Fs.prod_insert ha]
          by_cases ha0 : a = 0
          · subst ha0
            have h0 : r (σ 0) = 0 := by rw [hσ0]; rfl
            rw [h0, zero_add, hM_col0 (σ 0), if_pos hσ0, one_mul]
            exact ih
          · exact v123 (hM_ord (σ a) a ha0) ih
      exact hgen Fs.univ
    rw [Eqv.sum_comp σ r] at hprod_ord
    have hsum_r : ∑ i : Fin 6, r i = 10 * m - 15 := by
      rw [Fi.sum_univ_six]
      simp only [r, v34, v33, v20, v19, v18, v15]
      omega
    rw [hsum_r] at hprod_ord
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using hprod_ord
    · simpa [hs] using v204 hprod_ord
  · have hzero : ∏ j : Fin 6, M (σ j) j = 0 :=
      prod_eq_zero (mem_univ (0 : Fin 6)) (by rw [hM_col0, if_neg hσ0])
    rw [hzero, smul_zero]
    exact v137 _
lemma v191 {p : ℕ} (hp : Nat.Prime p) [CharP K p]
    (D : v35 (Mv2 K))
    (hD_C : ∀ c : K, D (Mv.C c) = 0)
    (a b : K) (ha : a ^ p = a) (hb : b ^ p = b) :
    let u : Mv2 K := Mv.X 0
    let v : Mv2 K := Mv.X 1
    let x := u + Mv.C a
    let y := v + Mv.C b
    fWron p D ![1, x, y, x ^ 2, x * y, y ^ 2] = fWron p D ![1, u, v, u ^ 2, u * v, v ^ 2] := by
  have : Fact p.Prime := ⟨hp⟩
  intro u v x y
  let g0 : Fin 6 → Mv2 K := ![1, u, v, u ^ 2, u * v, v ^ 2]
  let g1 : Fin 6 → Mv2 K := ![1, x, y, x ^ 2, x * y, y ^ 2]
  let Cmat : Matrix (Fin 6) (Fin 6) K :=
    !![1, a, b, a ^ 2, a * b, b ^ 2; 0, 1, 0, 2 * a, b,     0; 0, 0, 1, 0,     a,     2 * b; 0, 0, 0, 1,     0,     0; 0, 0, 0, 0,     1,     0; 0, 0, 0, 0,     0,     1]
  have hC_det : Cmat.det = 1 := by
    have htri : Cmat.BlockTriangular id := by
      intro i j hij; simp only [id_eq] at hij
      fin_cases i <;> fin_cases j <;> simp_all [Cmat]
    rw [Mx.det_of_isUpperTriangular htri, Fi.prod_univ_six]; simp [Cmat]
  have hC_frob : ∀ r c : Fin 6, Cmat r c ^ p = Cmat r c := by
    intro r c
    have h2 : (2 : K) ^ p = 2 := by
      have : (2 : K) = 1 + 1 := by ring
      rw [this, add_pow_char, one_pow]
    rcases v36 r with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases v36 c with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Cmat, v20, v19, v18, v15, ha, hb, h2, mul_pow, pow_right_comm, zero_pow hp.ne_zero]
  have hD_C_mul : ∀ (c : K) (P : Mv2 K), D (Mv.C c * P) = Mv.C c * D P := by
    intro c P; rw [D.leibniz, hD_C c, zero_mul, zero_add]
  have hD_sum : ∀ (f : Fin 6 → Mv2 K), D (∑ k : Fin 6, f k) = ∑ k : Fin 6, D (f k) := by
    intro f; rw [Fi.sum_univ_six, Fi.sum_univ_six]
    simp only [D.map_add]
  have hsum_pow : ∀ (f : Fin 6 → Mv2 K), (∑ k : Fin 6, f k) ^ p = ∑ k : Fin 6, f k ^ p := by
    intro f; rw [Fi.sum_univ_six, Fi.sum_univ_six]
    simp only [add_pow_char]
  have hg1_eq : ∀ j : Fin 6, g1 j = ∑ k : Fin 6, g0 k * Mv.C (Cmat k j) := by
    intro j
    rw [Fi.sum_univ_six]
    rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [g0, g1, Cmat, x, y, v20, v19, v18, v15, map_pow, map_mul, map_ofNat] <;> ring
  have hmat : v08 p D g1 = v08 p D g0 * (Mv.C : K →+* Mv2 K).mapMatrix Cmat := by
    refine Mx.ext fun i j => ?_
    rw [Mx.mul_apply]
    simp only [Rh.mapMatrix_apply, Mx.map_apply]
    have hD1 : D (g1 j) = ∑ k : Fin 6, D (g0 k) * Mv.C (Cmat k j) := by
      rw [hg1_eq j, hD_sum]; apply sum_congr rfl; intro k _
      rw [mul_comm, hD_C_mul, mul_comm]
    have hD2 : D (D (g1 j)) = ∑ k : Fin 6, D (D (g0 k)) * Mv.C (Cmat k j) := by
      rw [hD1, hD_sum]; apply sum_congr rfl; intro k _
      rw [mul_comm, hD_C_mul, mul_comm]
    have hD3 : D (D (D (g1 j))) = ∑ k : Fin 6, D (D (D (g0 k))) * Mv.C (Cmat k j) := by
      rw [hD2, hD_sum]; apply sum_congr rfl; intro k _
      rw [mul_comm, hD_C_mul, mul_comm]
    have hD4 : D (D (D (D (g1 j)))) = ∑ k : Fin 6, D (D (D (D (g0 k)))) * Mv.C (Cmat k j) := by
      rw [hD3, hD_sum]; apply sum_congr rfl; intro k _
      rw [mul_comm, hD_C_mul, mul_comm]
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [v08, Mx.of_apply]
      rw [hg1_eq j, hsum_pow]
      apply sum_congr rfl; intro k _
      rw [mul_pow, ← map_pow, hC_frob]
    · simp only [v08, Mx.of_apply]; exact hg1_eq j
    · simp only [v08, Mx.of_apply]; exact hD1
    · simp only [v08, Mx.of_apply]; exact hD2
    · simp only [v08, Mx.of_apply]; exact hD3
    · simp only [v08, Mx.of_apply]; exact hD4
  rw [fWron, fWron, hmat, Mx.det_mul, ← Rh.map_det, hC_det, map_one, mul_one]
def shZM (a b : K) : Mat3 K :=
  !![1, 0, a; 0, 1, b; 0, 0, 1]
lemma shZM_mul_inv (a b : K) : shZM a b * shZM (-a) (-b) = 1 := by
  refine Mx.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [shZM, Mx.mul_apply, Fi.sum_univ_three]
lemma shZM_inv_mul (a b : K) : shZM (-a) (-b) * shZM a b = 1 := by
  refine Mx.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [shZM, Mx.mul_apply, Fi.sum_univ_three]
lemma v143 (a b : K) (F P : Mv3 K) :
    evalZ1 (sMat (shZM a b) (derivZ F P)) = v43 (evalZ1 (sMat (shZM a b) F)) (evalZ1 (sMat (shZM a b) P)) := by
  have hp0 : ∀ Q : Mv3 K, Mv.pderiv 0 (sMat (shZM a b) Q) = sMat (shZM a b) (Mv.pderiv 0 Q) := by
    intro Q; rw [v67, Fi.sum_univ_three]; simp [shZM]
  have hp1 : ∀ Q : Mv3 K, Mv.pderiv 1 (sMat (shZM a b) Q) = sMat (shZM a b) (Mv.pderiv 1 Q) := by
    intro Q; rw [v67, Fi.sum_univ_three]; simp [shZM]
  rw [← evalZ1_derivZ]
  congr 1
  change sMat (shZM a b) (Mv.pderiv 1 F * Mv.pderiv 0 P - Mv.pderiv 0 F * Mv.pderiv 1 P) = Mv.pderiv 1 (sMat (shZM a b) F) * Mv.pderiv 0 (sMat (shZM a b) P) - Mv.pderiv 0 (sMat (shZM a b) F) * Mv.pderiv 1 (sMat (shZM a b) P)
  rw [hp0 F, hp1 F, hp0 P, hp1 P, map_sub, map_mul, map_mul]
lemma v145 {p : ℕ} (hp : Nat.Prime p) [CharP K p]
    {F : Mv3 K} {a b : K} (ha : a ^ p = a) (hb : b ^ p = b)
    (hF0 : Mv.eval ![a, b, 1] F = 0)
    (hFx : Mv.eval ![a, b, 1] (Mv.pderiv 0 F) = 0)
    (hFy : Mv.eval ![a, b, 1] (Mv.pderiv 1 F) = 0) :
    v39 5
      (evalZ1 (sMat (shZM a b) (fWron p (derivZ F) cMon))) := by
  set G : Mv2 K := evalZ1 (sMat (shZM a b) F)
  have hev0 : ∀ Q : Mv3 K, Mv.eval 0 (evalZ1 (sMat (shZM a b) Q)) = Mv.eval ![a, b, 1] Q := by
    intro Q
    have h1 : Mv.eval 0 (evalZ1 (sMat (shZM a b) Q)) = Mv.eval ![0, 0, 1] (sMat (shZM a b) Q) := by
      dsimp only [evalZ1]
      rw [v101]
      apply congr_arg (fun v => Mv.eval v (sMat (shZM a b) Q))
      ext i; rcases v03 i with rfl | rfl | rfl <;> simp
    rw [h1, v50]
    apply congr_arg (fun v => Mv.eval v Q)
    ext i; rcases v03 i with rfl | rfl | rfl <;>
      simp [shZM, Mx.mulVec, dotProduct, Fi.sum_univ_three]
  have hp0 : Mv.pderiv 0 G = evalZ1 (sMat (shZM a b) (Mv.pderiv 0 F)) := by
    dsimp only [G]; rw [← (v63 _).1, v67, Fi.sum_univ_three]; simp [shZM]
  have hp1 : Mv.pderiv 1 G = evalZ1 (sMat (shZM a b) (Mv.pderiv 1 F)) := by
    dsimp only [G]; rw [← (v63 _).2, v67, Fi.sum_univ_three]; simp [shZM]
  have hG2 : v39 2 G :=
    v119 (by rw [hev0, hF0]) (by rw [hp0, hev0, hFx]) (by rw [hp1, hev0, hFy])
  let φ : Mv3 K →+* Mv2 K :=
    (evalZ1.comp (sMat (shZM a b))).toRingHom
  have hiter : ∀ (n : ℕ) (P : Mv3 K), φ ((derivZ F)^[n] P) = (v43 G)^[n] (φ P) := by
    intro n
    induction n with
    | zero => intro P; rfl
    | succ n ih =>
      intro P
      simp only [Fn.iterate_succ_apply']
      change evalZ1 (sMat (shZM a b) (derivZ F ((derivZ F)^[n] P))) = _
      rw [v143]
      exact congr_arg (v43 G) (ih P)
  have hφ_conic : (fun j => φ (cMon j)) = ![1, Mv.X 0 + Mv.C a, Mv.X 1 + Mv.C b, (Mv.X 0 + Mv.C a) ^ 2, (Mv.X 0 + Mv.C a) * (Mv.X 1 + Mv.C b), (Mv.X 1 + Mv.C b) ^ 2] := by
    have hX0 : φ (Mv.X 0) = Mv.X 0 + Mv.C a := by
      simp [φ, evalZ1, sMat, shZM, Fi.sum_univ_three]
    have hX1 : φ (Mv.X 1) = Mv.X 1 + Mv.C b := by
      simp [φ, evalZ1, sMat, shZM, Fi.sum_univ_three]
    have hX2 : φ (Mv.X 2) = 1 := by
      simp [φ, evalZ1, sMat, shZM, Fi.sum_univ_three]
    funext j
    rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cMon, v20, v19, v18, v15, map_pow, map_mul, hX0, hX1, hX2]
  have hW_eq : φ (fWron p (derivZ F) cMon) = fWron p (v43 G) (fun j => φ (cMon j)) := by
    rw [fWron, fWron, Rh.map_det]
    congr 1; refine Mx.ext fun i j => ?_
    simp only [Rh.mapMatrix_apply, Mx.map_apply]
    have h1 := hiter 1 (cMon j)
    have h2 := hiter 2 (cMon j)
    have h3 := hiter 3 (cMon j)
    have h4 := hiter 4 (cMon j)
    simp only [Fn.iterate_succ, Fn.iterate_zero, Fn.comp_apply, id_eq] at h1 h2 h3 h4
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [v08]
    · simp [v08]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  change v39 5 (φ (fWron p (derivZ F) cMon))
  rw [hW_eq, hφ_conic]
  have hD_C : ∀ c : K, v43 G (Mv.C c) = 0 := by
    intro c; simp [v43]
  rw [v191 hp (v43 G) hD_C a b ha hb]
  exact v134 hp.one_le (le_refl 2) hG2
noncomputable def shXY (x₀ y₀ : K) :
    Pol (Pol K) →+* Pol (Pol K) :=
  (Pl.compRingHom (Pl.X + Pl.C (Pl.C y₀))).comp
    (Pl.mapRingHom (Pl.compRingHom (Pl.X + Pl.C x₀)))
lemma shXY_monic (x₀ y₀ : K) {f : Pol (Pol K)} (hf : f.Monic) :
    (shXY x₀ y₀ f).Monic := by
  change ((f.map (Pl.compRingHom (Pl.X + Pl.C x₀))).comp
    (Pl.X + Pl.C (Pl.C y₀))).Monic
  exact (hf.map _).comp (Pl.monic_X_add_C _) (by simp)
lemma v207 (x₀ y₀ : K) {f : Pol (Pol K)} (hf : f.Monic) :
    (shXY x₀ y₀ f).natDegree = f.natDegree := by
  change ((f.map (Pl.compRingHom (Pl.X + Pl.C x₀))).comp
    (Pl.X + Pl.C (Pl.C y₀))).natDegree = _
  rw [Pl.natDegree_comp, Pl.natDegree_X_add_C, mul_one, hf.natDegree_map]
lemma v79 {H : Mv3 K} {e k : ℕ}
    (hH : H.IsHomogeneous e) {a b : K}
    (hord : v39 k (evalZ1 (sMat (shZM a b) H)))
    (T : Mat3 K) (x' y' c : K) (_hc : c ≠ 0)
    (hTpt : T.mulVec ![x', y', 1] = c • ![a, b, 1]) :
    ∀ i j : ℕ, i + j < k → ((shXY x' y' (dhZ (sMat T H))).coeff j).coeff i = 0 := by
  set H0 := sMat (shZM a b) H
  have hH0_hom : H0.IsHomogeneous e := v25 _ hH
  have hH_eq : H = sMat (shZM (-a) (-b)) H0 := by
    dsimp only [H0]; rw [v47, shZM_mul_inv, v130]
  have hH0_supp : ∀ m ∈ H0.support, k ≤ m 0 + m 1 := by
    intro m hm
    let m2 : Fin 2 →₀ ℕ := Fu.single 0 (m 0) + Fu.single 1 (m 1)
    have hcoeff : (evalZ1 H0).coeff m2 = H0.coeff m := by
      conv_lhs => rw [Mv.as_sum H0, map_sum, Mv.coeff_sum]
      rw [sum_eq_single m]
      · rw [Mv.monomial_eq, map_mul, evalZ1, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
        simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, mul_one]
        have hmon : Mv.C (H0.coeff m) * (Mv.X 0 ^ m 0 * Mv.X 1 ^ m 1) = Mv.monomial m2 (H0.coeff m) := by
          rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_two]
          simp [m2]
        rw [hmon, Mv.coeff_monomial, if_pos rfl]
      · intro n hn hnm
        rw [Mv.monomial_eq, map_mul, evalZ1, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
        simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, mul_one]
        let n2 : Fin 2 →₀ ℕ := Fu.single 0 (n 0) + Fu.single 1 (n 1)
        have hmon : Mv.C (H0.coeff n) * (Mv.X 0 ^ n 0 * Mv.X 1 ^ n 1) = Mv.monomial n2 (H0.coeff n) := by
          rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_two]
          simp [n2]
        rw [hmon, Mv.coeff_monomial, if_neg]
        intro heq; apply hnm
        have hm_deg := v10 hH0_hom (Mv.mem_support_iff.mp hm)
        have hn_deg := v10 hH0_hom (Mv.mem_support_iff.mp hn)
        have h0 : n 0 = m 0 := by have := congr_arg (fun f : Fin 2 →₀ ℕ => f 0) heq; simpa [n2, m2] using this
        have h1 : n 1 = m 1 := by have := congr_arg (fun f : Fin 2 →₀ ℕ => f 1) heq; simpa [n2, m2] using this
        ext i; rcases v03 i with rfl | rfl | rfl
        · exact h0
        · exact h1
        · omega
      · intro h; exact absurd hm h
    have hne : (evalZ1 H0).coeff m2 ≠ 0 := by
      rw [hcoeff]; exact Mv.mem_support_iff.mp hm
    have := hord m2 hne
    simpa [m2] using this
  let dhZHom : Mv3 K →+* Pol (Pol K) :=
    (Mv.aeval ![Pl.C Pl.X, Pl.X, (1 : Pol (Pol K))]).toRingHom
  let ψ : Mv3 K →+* Pol (Pol K) :=
    (shXY x' y').comp (dhZHom.comp (sMat (shZM (-a) (-b) * T)).toRingHom)
  have hψ_def : ∀ P : Mv3 K, ψ P = shXY x' y' (dhZ (sMat (shZM (-a) (-b) * T) P)) := fun _ => rfl
  have hψ_H0 : ψ H0 = shXY x' y' (dhZ (sMat T H)) := by
    rw [hψ_def, ← v47, ← hH_eq]
  let hasOrd : ℕ → Pol (Pol K) → Prop :=
    fun r p => ∀ i j : ℕ, i + j < r → (p.coeff j).coeff i = 0
  have hadd : ∀ {r p q}, hasOrd r p → hasOrd r q → hasOrd r (p + q) := by
    intro r p q hp hq i j hij
    rw [Pl.coeff_add, Pl.coeff_add, hp i j hij, hq i j hij, add_zero]
  have hmul : ∀ {r₁ r₂ p q}, hasOrd r₁ p → hasOrd r₂ q → hasOrd (r₁ + r₂) (p * q) := by
    intro r₁ r₂ p q hp hq i j hij
    rw [Pl.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => p.coeff a * q.coeff b), Pl.finsetSum_coeff]
    apply sum_eq_zero; intro b hb
    rw [Fs.mem_range] at hb
    rw [Pl.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a c => (p.coeff b).coeff a * (q.coeff (j - b)).coeff c)]
    apply sum_eq_zero; intro a ha
    rw [Fs.mem_range] at ha
    by_cases h1 : a + b < r₁
    · rw [hp a b h1, zero_mul]
    · rw [hq (i - a) (j - b) (by omega), mul_zero]
  have hpow : ∀ {r p} (n : ℕ), hasOrd r p → hasOrd (n * r) (p ^ n) := by
    intro r p n hp
    induction n with
    | zero => intro i j hij; omega
    | succ n ih => rw [pow_succ, Nat.succ_mul]; exact hmul ih hp
  have hmono : ∀ {r₁ r₂ p}, r₁ ≤ r₂ → hasOrd r₂ p → hasOrd r₁ p :=
    fun hle hp i j hij => hp i j (hij.trans_le hle)
  have hψ_eval0 : ∀ P : Mv3 K, ((ψ P).coeff 0).coeff 0 = Mv.eval ![0, 0, c] P := by
    intro P
    have hev00 : ∀ q : Pol (Pol K), (q.coeff 0).coeff 0 = (q.map (Pl.evalRingHom 0)).eval 0 := by
      intro q
      rw [← Pl.coeff_zero_eq_eval_zero, Pl.coeff_map, Pl.coe_evalRingHom, ← Pl.coeff_zero_eq_eval_zero]
    rw [hev00]
    have hsh : ∀ q : Pol (Pol K), ((shXY x' y' q).map (Pl.evalRingHom 0)).eval 0 = (q.map (Pl.evalRingHom x')).eval y' := by
      intro q
      induction q using Pl.induction_on' with
      | add p₁ p₂ h₁ h₂ => simp [map_add, Pl.eval_add, h₁, h₂]
      | monomial n p =>
        have h1 : shXY x' y' (Pl.monomial n p) = Pl.C (p.comp (Pl.X + Pl.C x')) * (Pl.X + Pl.C (Pl.C y')) ^ n := by
          simp only [shXY, Rh.comp_apply, Pl.coe_mapRingHom, Pl.coe_compRingHom, ← Pl.C_mul_X_pow_eq_monomial, Pl.map_mul, Pl.map_C, Pl.map_pow, Pl.map_X, Pl.mul_comp, Pl.C_comp, Pl.pow_comp, Pl.X_comp]
        rw [h1]
        simp only [Pl.map_mul, Pl.map_C, Pl.map_pow, Pl.map_add, Pl.map_X, Pl.eval_mul, Pl.eval_C, Pl.eval_pow, Pl.eval_add, Pl.eval_X, Pl.coe_evalRingHom, zero_add, Pl.map_monomial, Pl.eval_monomial]
        congr 1
        simp [Pl.eval_comp]
    rw [hψ_def, hsh, v136, v50, ← Mx.mulVec_mulVec, hTpt, Mx.mulVec_smul]
    apply congr_arg (fun v => Mv.eval v P)
    ext i; rcases v03 i with rfl | rfl | rfl <;>
      simp [shZM]
  have hX0_ord : hasOrd 1 (ψ (Mv.X 0)) := by
    intro i j hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi; subst hj
    rw [hψ_eval0]; simp
  have hX1_ord : hasOrd 1 (ψ (Mv.X 1)) := by
    intro i j hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi; subst hj
    rw [hψ_eval0]; simp
  rw [← hψ_H0]
  suffices hasOrd k (ψ H0) by exact this
  rw [Mv.as_sum H0, map_sum]
  have hsum : ∀ s : Finset (E3), (∀ m ∈ s, hasOrd k (ψ (Mv.monomial m (H0.coeff m)))) → hasOrd k (∑ m ∈ s, ψ (Mv.monomial m (H0.coeff m))) := by
    intro s hs
    induction s using Fs.induction_on with
    | empty => intro i j _; simp
    | insert a s ha ih =>
      rw [Fs.sum_insert ha]
      exact hadd (hs a (mem_insert_self a s))
        (ih (fun m hm => hs m (mem_insert_of_mem hm)))
  apply hsum; intro m hm
  have hmk := hH0_supp m hm
  rw [Mv.monomial_eq, map_mul, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three, map_pow, map_pow, map_pow]
  have h01 : hasOrd (m 0 + m 1) (ψ (Mv.X 0) ^ m 0 * ψ (Mv.X 1) ^ m 1) := by
    have h0 := hpow (m 0) hX0_ord
    have h1 := hpow (m 1) hX1_ord
    rw [mul_one] at h0 h1
    exact hmul h0 h1
  have h012 : hasOrd (m 0 + m 1) (ψ (Mv.C (H0.coeff m)) * (ψ (Mv.X 0) ^ m 0 * ψ (Mv.X 1) ^ m 1 * ψ (Mv.X 2) ^ m 2)) := by
    have htriv1 : hasOrd 0 (ψ (Mv.C (H0.coeff m))) := fun _ _ h => by omega
    have htriv2 : hasOrd 0 (ψ (Mv.X 2) ^ m 2) := fun _ _ h => by omega
    have h1 := hmul htriv1 (hmul h01 htriv2)
    simpa only [zero_add, add_zero] using h1
  exact hmono hmk h012
end LinearSubstAndSingular
section CurvePointBound
open Classical in
lemma v46 {L : Type*} [Field L] [Infinite L] :
    ∀ {n : ℕ} {P : MvPolynomial (Fin n) L}, P ≠ 0 → ∃ v : Fin n → L, Mv.eval v P ≠ 0
  | 0, P, hP => by
    refine ⟨Fi.elim0, ?_⟩
    intro h0
    apply hP
    have hP_eq : P = Mv.C (Mv.eval Fi.elim0 P) := by
      ext m
      have hm : m = 0 := by ext i; exact Fi.elim0 i
      subst hm
      rw [Mv.coeff_C, if_pos rfl]
      symm
      rw [Mv.eval_eq']
      rw [sum_eq_single (0 : Fin 0 →₀ ℕ)]
      · simp
      · intro b _ hb; exact absurd (by ext i; exact Fi.elim0 i) hb
      · intro h; simp [Mv.notMem_support_iff.mp h]
    rw [hP_eq, h0, map_zero]
  | n + 1, P, hP => by
    classical
    set q : Pol (MvPolynomial (Fin n) L) := Mv.finSuccEquiv L n P
    have hq : q ≠ 0 := fun h0 => hP ((Mv.finSuccEquiv L n).injective (by simpa [q] using h0))
    have hex_coeff : ∃ k : ℕ, q.coeff k ≠ 0 := by
      by_contra hall; push Not at hall; exact hq (Pl.ext fun k => by simp [hall k])
    rcases hex_coeff with ⟨k, hk⟩
    obtain ⟨v, hv⟩ := v46 hk
    set r : Pol L := q.map (Mv.eval v)
    have hr : r ≠ 0 := by
      intro h0
      have := congr_arg (fun f : Pol L => f.coeff k) h0
      simp only [r, Pl.coeff_map, Pl.coeff_zero] at this
      exact hv this
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset r.roots.toFinset
    have hrx : r.eval x ≠ 0 := by
      intro h0
      apply hx
      rw [Mu.mem_toFinset, Pl.mem_roots hr]
      exact h0
    refine ⟨Fi.cons x v, ?_⟩
    have hev : Mv.eval (Fi.cons x v) P = r.eval x :=
      Mv.eval_eq_eval_mv_eval' v x P
    rw [hev]; exact hrx
lemma v114 {L : Type*} [Field L] [Infinite L]
    (q : Fin 3 → L) (hq : q ≠ 0) (S : Finset (Fin 3 → L))
    (hS : ∀ v ∈ S, cross3 q v ≠ 0) :
    ∃ n : Fin 3 → L, dot3 n q = 0 ∧ ∀ v ∈ S, dot3 n v ≠ 0 := by
  classical
  have hex : ∃ i : Fin 3, q i ≠ 0 := by
    by_contra hall; push Not at hall; exact hq (funext hall)
  rcases hex with ⟨i, hi⟩
  have htwo : ∃ u₁ u₂ : Fin 3 → L, dot3 u₁ q = 0 ∧ dot3 u₂ q = 0 ∧ cross3 u₁ u₂ ≠ 0 := by
    rcases v03 i with rfl | rfl | rfl
    · exact ⟨![-q 1, q 0, 0], ![-q 2, 0, q 0], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 0; simp [cross3] at this; exact hi this⟩
    · exact ⟨![q 1, -q 0, 0], ![0, -q 2, q 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 1; simp [cross3] at this; exact hi this⟩
    · exact ⟨![q 2, 0, -q 0], ![0, q 2, -q 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 2; simp [cross3] at this; exact hi this⟩
  rcases htwo with ⟨u₁, u₂, hu1, hu2, hcr12⟩
  let poly : Pol L := ∏ v ∈ S, (Pl.C (dot3 u₁ v) + Pl.C (dot3 u₂ v) * Pl.X)
  have hpoly_ne : poly ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro v hv h0
    have hc0 : dot3 u₁ v = 0 := by simpa using congr_arg (fun f : Pol L => f.coeff 0) h0
    have hc1 : dot3 u₂ v = 0 := by simpa using congr_arg (fun f : Pol L => f.coeff 1) h0
    have hq_prop := v09 hcr12 (v45 u₁ q ▸ hu1) (v45 u₂ q ▸ hu2)
    have hv_prop := v09 hcr12 (v45 u₁ v ▸ hc0) (v45 u₂ v ▸ hc1)
    rcases hq_prop with ⟨c1, hc1'⟩
    rcases hv_prop with ⟨c2, hc2'⟩
    apply hS v hv
    rw [hc1', hc2', v72, v42, v85, smul_zero, smul_zero]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset poly.roots.toFinset
  have hpt : poly.eval t ≠ 0 := fun h0 => ht (Mu.mem_toFinset.mpr ((Pl.mem_roots hpoly_ne).mpr h0))
  refine ⟨u₁ + t • u₂, ?_, ?_⟩
  · rw [v84, v06, hu1, hu2, mul_zero, add_zero]
  · intro v hv h0
    apply hpt
    rw [Pl.eval_prod]
    apply prod_eq_zero hv
    simp only [Pl.eval_add, Pl.eval_C, Pl.eval_mul, Pl.eval_X]
    rw [v84, v06] at h0
    linear_combination h0
lemma v60 {L : Type*} [Field L] {F : Mv3 L} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F) (hd2 : 2 ≤ d) (j : Fin 3) :
    ∃ Rset : Finset (Fin 3 → L), (∀ r ∈ Rset, r ≠ 0 ∧ r j = 0) ∧ ∀ v : Fin 3 → L, v ≠ 0 → v j = 0 → Mv.eval v F = 0 → ∃ r ∈ Rset, ∃ c : L, v = c • r := by
  have hXj_ndvd : ¬ Mv.X j ∣ F := by
    rintro ⟨q, hq⟩
    rcases hF_irr.isUnit_or_isUnit hq with hXu | hqu
    · exact (v89 j).not_isUnit hXu
    · rcases v120.mp hqu with ⟨c, _, rfl⟩
      have hdeg1 : F.IsHomogeneous 1 := by
        rw [hq, mul_comm]; exact v07 c (Mv.isHomogeneous_X L j)
      have hne : F ≠ 0 := hF_irr.ne_zero
      obtain ⟨m, hm⟩ := Mv.support_nonempty.mpr hne
      have hd := v10 hF (Mv.mem_support_iff.mp hm)
      have h1 := v10 hdeg1 (Mv.mem_support_iff.mp hm)
      omega
  let Pj : Mat3 L :=
    match j with
    | ⟨0, _⟩ => cycMat L * cycMat L
    | ⟨1, _⟩ => cycMat L
    | ⟨2, _⟩ => 1
  let PjInv : Mat3 L :=
    match j with
    | ⟨0, _⟩ => cycMat L
    | ⟨1, _⟩ => cycMat L * cycMat L
    | ⟨2, _⟩ => 1
  have hPmul : Pj * PjInv = 1 := by
    rcases v03 j with rfl | rfl | rfl
    · exact v68
    · rw [← Mx.mul_assoc]; exact v68
    · simp [Pj, PjInv]
  have hPmul' : PjInv * Pj = 1 := by
    rcases v03 j with rfl | rfl | rfl
    · rw [← Mx.mul_assoc]; exact v68
    · exact v68
    · simp [Pj, PjInv]
  have hP_coord2 : ∀ w : Fin 3 → L, (Pj.mulVec w) j = w 2 := by
    intro w; rcases v03 j with rfl | rfl | rfl <;>
      simp [Pj, cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
  set G := sMat Pj F
  have hG_hom : G.IsHomogeneous d := v25 Pj hF
  have hX2_ndvd_G : ¬ Mv.X 2 ∣ G := by
    intro hdvd
    apply hXj_ndvd
    have hX2_eq : sMat Pj (Mv.X j) = Mv.X 2 := by
      rcases v03 j with rfl | rfl | rfl <;>
        simp [Pj, cycMat, sMat, Fi.sum_univ_three]
    rw [← v131 hPmul hPmul', hX2_eq]
    exact hdvd
  let g : Pol L := Mv.aeval ![Pl.X, 1, 0] G
  have hg_ne : g ≠ 0 := by
    intro hg0
    apply hX2_ndvd_G
    have hev0 : evZ0 G = 0 := by
      have hev_hom : (evZ0 G).IsHomogeneous d := by
        have hsum : evZ0 G = ∑ m ∈ G.support, if m 2 = 0 then Mv.monomial m (G.coeff m) else 0 := by
          conv_lhs => rw [Mv.as_sum G, map_sum]
          apply sum_congr rfl; intro m _
          rw [Mv.monomial_eq, map_mul, evZ0, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
          simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons]
          by_cases h2 : m 2 = 0
          · rw [if_pos h2, h2, pow_zero, mul_one]
            symm
            rw [Fi.prod_univ_three, h2, pow_zero, mul_one]
          · rw [if_neg h2, zero_pow h2, mul_zero, mul_zero]
        rw [hsum]; apply MvPolynomial.IsHomogeneous.sum; intro m hm
        split_ifs with h2
        · apply Mv.isHomogeneous_monomial
          have hdeg := v10 hG_hom (Mv.mem_support_iff.mp hm)
          rw [Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi), Fi.sum_univ_three]
          exact hdeg
        · exact Mv.isHomogeneous_zero _ _ _
      ext m
      rw [Mv.coeff_zero]
      by_cases hm2 : m 2 = 0
      · by_cases hdeg : m 0 + m 1 = d
        · have hgc : g.coeff (m 0) = G.coeff m := by
            dsimp only [g]
            conv_lhs => rw [Mv.as_sum G, map_sum, Pl.finsetSum_coeff]
            rw [sum_eq_single m]
            · rw [Mv.monomial_eq, map_mul, Mv.aeval_C, Pl.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
              simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, hm2, pow_zero, one_pow, mul_one, map_one]
              rw [Pl.coeff_C_mul_X_pow, if_pos rfl]
            · intro n hn hnm
              rw [Mv.monomial_eq, map_mul, Mv.aeval_C, Pl.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
              simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, mul_one]
              by_cases hn2 : n 2 = 0
              · rw [hn2, pow_zero, mul_one, Pl.coeff_C_mul_X_pow, if_neg]
                intro h0; apply hnm
                have hnd := v10 hG_hom (Mv.mem_support_iff.mp hn)
                ext i; rcases v03 i with rfl | rfl | rfl <;> omega
              · rw [zero_pow hn2, mul_zero, mul_zero, Pl.coeff_zero]
            · intro h
              rw [Mv.notMem_support_iff.mp h, map_zero, map_zero, Pl.coeff_zero]
          have hG0 : G.coeff m = 0 := by rw [← hgc, hg0, Pl.coeff_zero]
          conv_lhs => rw [Mv.as_sum G, map_sum, Mv.coeff_sum]
          rw [sum_eq_single m]
          · rw [Mv.monomial_eq, map_mul, evZ0, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
            simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, hm2, pow_zero, mul_one, map_one]
            rw [hG0, map_zero, zero_mul, Mv.coeff_zero]
          · intro n _ hnm
            rw [Mv.monomial_eq, map_mul, evZ0, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
            simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons]
            by_cases hn2 : n 2 = 0
            · rw [hn2, pow_zero, mul_one]
              have hmon : Mv.C (G.coeff n) * (Mv.X 0 ^ n 0 * Mv.X 1 ^ n 1) = Mv.monomial n (G.coeff n) := by
                rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three, hn2, pow_zero, mul_one]
              rw [hmon, Mv.coeff_monomial, if_neg hnm]
            · rw [zero_pow hn2, mul_zero, mul_zero, Mv.coeff_zero]
          · intro h; rw [Mv.notMem_support_iff.mp h, map_zero, map_zero, Mv.coeff_zero]
        · by_contra hne; exact hdeg (by have := v10 hev_hom hne; omega)
      · conv_lhs => rw [Mv.as_sum G, map_sum, Mv.coeff_sum]
        apply sum_eq_zero; intro n _
        rw [Mv.monomial_eq, map_mul, evZ0, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
        simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons]
        by_cases hn2 : n 2 = 0
        · rw [hn2, pow_zero, mul_one]
          have hmon : Mv.C (G.coeff n) * (Mv.X 0 ^ n 0 * Mv.X 1 ^ n 1) = Mv.monomial n (G.coeff n) := by
            rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three, hn2, pow_zero, mul_one]
          rw [hmon, Mv.coeff_monomial, if_neg (fun (h : n = m) => hm2 (h ▸ hn2))]
        · rw [zero_pow hn2, mul_zero, mul_zero, Mv.coeff_zero]
    have hd := v162 G
    rwa [hev0, sub_zero] at hd
  classical
  let Wset : Finset (Fin 3 → L) :=
    insert ![1, 0, 0] (g.roots.toFinset.image (fun r => ![r, 1, 0]))
  refine ⟨Wset.image (fun w => Pj.mulVec w), ?_, ?_⟩
  · intro r hr
    rcases mem_image.mp hr with ⟨w, hw, rfl⟩
    have hw_spec : w ≠ 0 ∧ w 2 = 0 := by
      rcases mem_insert.mp hw with rfl | hmem
      · exact ⟨fun h0 => (one_ne_zero : (1 : L) ≠ 0) (by simpa using congr_fun h0 0), rfl⟩
      · rcases mem_image.mp hmem with ⟨a, _, rfl⟩
        exact ⟨fun h0 => (one_ne_zero : (1 : L) ≠ 0) (by simpa using congr_fun h0 1), rfl⟩
    refine ⟨?_, by rw [hP_coord2, hw_spec.2]⟩
    intro h0; apply hw_spec.1
    calc w = (PjInv * Pj).mulVec w := by rw [hPmul', Mx.one_mulVec]
      _ = PjInv.mulVec (Pj.mulVec w) := (Mx.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h0, Mx.mulVec_zero]
  · intro v hv hvj hFv
    set w := PjInv.mulVec v
    have hPw : Pj.mulVec w = v := by
      dsimp only [w]; rw [Mx.mulVec_mulVec, hPmul, Mx.one_mulVec]
    have hw2 : w 2 = 0 := by rw [← hP_coord2 w, hPw, hvj]
    have hw_ne : w ≠ 0 := fun h0 => hv (by rw [← hPw, h0, Mx.mulVec_zero])
    have hGw : Mv.eval w G = 0 := by
      dsimp only [G]; rw [v50, hPw, hFv]
    by_cases hw1 : w 1 = 0
    · have hw0 : w 0 ≠ 0 := by
        intro h0; apply hw_ne; ext i; fin_cases i <;> simp [h0, hw1, hw2]
      refine ⟨Pj.mulVec ![1, 0, 0], mem_image.mpr ⟨![1, 0, 0], mem_insert_self _ _, rfl⟩, w 0, ?_⟩
      rw [← hPw, ← Mx.mulVec_smul]; congr 1
      ext i; fin_cases i <;> simp [hw1, hw2]
    · set a := w 0 * (w 1)⁻¹
      have hga : g.eval a = 0 := by
        have hwa : w = (w 1) • ![a, 1, 0] := by
          ext i; rcases v03 i with rfl | rfl | rfl
          · simp only [a, Pi.smul_apply, smul_eq_mul, Mx.cons_val_zero]; field_simp [hw1]
          · simp
          · simp [hw2]
        rw [hwa, v05 hG_hom] at hGw
        have hG0 : Mv.eval ![a, 1, 0] G = 0 :=
          (mul_eq_zero.mp hGw).resolve_left (pow_ne_zero d hw1)
        have hge : g.eval a = Mv.eval ![a, 1, 0] G := by
          dsimp only [g]
          rw [v124]
          apply congr_arg (fun vec => Mv.eval vec G)
          ext i; rcases v03 i with rfl | rfl | rfl <;> simp
        rw [hge, hG0]
      have ha_mem : a ∈ g.roots.toFinset :=
        Mu.mem_toFinset.mpr ((Pl.mem_roots hg_ne).mpr hga)
      refine ⟨Pj.mulVec ![a, 1, 0], mem_image.mpr ⟨![a, 1, 0], mem_insert_of_mem (mem_image.mpr ⟨a, ha_mem, rfl⟩), rfl⟩, w 1, ?_⟩
      rw [← hPw, ← Mx.mulVec_smul]; congr 1
      ext i; rcases v03 i with rfl | rfl | rfl
      · simp only [a, Pi.smul_apply, smul_eq_mul, Mx.cons_val_zero]; field_simp [hw1]
      · simp
      · simp [hw2]
set_option maxHeartbeats 800000 in
lemma v110 {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    {L : Type*} [Field L] [CharP L p]
    {F : Mv3 L} {d : ℕ} (hF : F.IsHomogeneous d) (hd2 : 2 ≤ d)
    (T Tinv : Mat3 L) (_hT1 : T * Tinv = 1) (hT2 : Tinv * T = 1)
    {x' y' : L} {Y' : PS L} (hY0 : Ps.constantCoeff Y' = y')
    (hF0 : evBr x' Y' (sMat T F) = 0)
    (P : Fin 3 → ZMod p) (hP2 : P 2 ≠ 0) (c : L) (hc : c ≠ 0)
    (hTpt : T.mulVec ![x', y', 1] = c • ((ZMod.castHom (dvd_refl p) L) ∘ P)) :
    Ps.X ^ 5 ∣ evBr x' Y' (sMat T (fWron p (derivZ F) cMon)) := by
  have : Fact p.Prime := ⟨hp⟩
  set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
  let Z : Fin 3 → PS L :=
    fun i => ∑ j : Fin 3, Ps.C (T i j) * ![Ps.C x' + Ps.X, Y', 1] j
  have hev_Z : ∀ Q : Mv3 L, evBr x' Y' (sMat T Q) = Mv.aeval Z Q := by
    intro Q
    induction Q using Mv.induction_on with
    | C a => simp [evBr, sMat]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]; congr 1
      simp [sMat, evBr, Z, Fi.sum_univ_three, Ps.algebraMap_eq]
  have hZ_const : ∀ i : Fin 3, Ps.constantCoeff (Z i) = c * ι (P i) := by
    intro i
    have h1 : Ps.constantCoeff (Z i) = (T.mulVec ![x', y', 1]) i := by
      simp only [Z, Fi.sum_univ_three, map_add, map_mul, Ps.constantCoeff_C, Mx.mulVec, dotProduct, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, Ps.constantCoeff_X, add_zero, hY0, map_one]
    rw [h1, hTpt]; rfl
  have hZ2_unit : IsUnit (Z 2) := by
    rw [Ps.isUnit_iff_constantCoeff, hZ_const 2]
    have hιP2 : ι (P 2) ≠ 0 := fun h0 => hP2 (ι.injective (h0.trans (map_zero ι).symm))
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hc hιP2)
  obtain ⟨uz, huz⟩ := hZ2_unit
  set z2i : PS L := ↑uz⁻¹
  have hzz : Z 2 * z2i = 1 := by dsimp only [z2i]; rw [← huz]; exact Units.mul_inv uz
  let u : Fin 3 → PS L := fun k => z2i * Z k
  have hu2 : u 2 = 1 := by dsimp only [u]; rw [mul_comm, hzz]
  have hZ_eq_u : ∀ k : Fin 3, Z k = Z 2 * u k := by
    intro k; dsimp only [u]; rw [← mul_assoc, hzz, one_mul]
  have haeval_hom : ∀ {Q : Mv3 L} {e : ℕ}, Q.IsHomogeneous e → Mv.aeval Z Q = Z 2 ^ e * Mv.aeval u Q := by
    intro Q e hQ
    rw [Mv.as_sum Q, map_sum, map_sum, mul_sum]
    apply sum_congr rfl; intro m hm
    have hdeg := v10 hQ (Mv.mem_support_iff.mp hm)
    rw [Mv.monomial_eq, map_mul, map_mul, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_prod, Fi.prod_univ_three, Fi.prod_univ_three]
    simp only [map_pow, Mv.aeval_C, Mv.aeval_X]
    have h0 : Z 0 ^ m 0 = Z 2 ^ m 0 * u 0 ^ m 0 := by rw [hZ_eq_u 0, mul_pow]
    have h1 : Z 1 ^ m 1 = Z 2 ^ m 1 * u 1 ^ m 1 := by rw [hZ_eq_u 1, mul_pow]
    have h2 : Z 2 ^ m 2 = Z 2 ^ m 2 * u 2 ^ m 2 := by rw [hu2, one_pow, mul_one]
    rw [h0, h1, h2, ← hdeg, pow_add, pow_add]
    ring
  have hu_F0 : Mv.aeval u F = 0 := by
    rw [hev_Z, haeval_hom hF] at hF0
    have h1 := congr_arg (fun w => z2i ^ d * w) hF0
    rw [mul_zero, ← mul_assoc, ← mul_pow, mul_comm z2i, hzz, one_pow, one_mul] at h1
    exact h1
  have hps_aeval_u : ∀ P : Mv3 L, psD (Mv.aeval u P) = Mv.aeval u (Mv.pderiv 0 P) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 P) * psD (u 1) := by
    intro P
    induction P using Mv.induction_on with
    | C a => simp [psD_C, Ps.algebraMap_eq]
    | add p q hp hq => simp only [map_add, v51, hp, hq]; ring
    | mul_X p i hp =>
      rw [map_mul, v29, hp, Dr.leibniz, Dr.leibniz]
      rcases v03 i with rfl | rfl | rfl
      · simp only [smul_eq_mul, Mv.aeval_X, Mv.pderiv_X, Pi.single_apply, Fi.reduceEq, ↓reduceIte, map_add, map_mul, map_zero, mul_one, mul_zero]
        ring
      · simp only [smul_eq_mul, Mv.aeval_X, Mv.pderiv_X, Pi.single_apply, Fi.reduceEq, ↓reduceIte, map_add, map_mul, map_zero, mul_one, mul_zero]
        ring
      · simp only [smul_eq_mul, Mv.aeval_X, hu2, v159, mul_zero, add_zero, Mv.pderiv_X, Pi.single_apply, Fi.reduceEq, ↓reduceIte, map_add, map_mul, map_zero, mul_zero, add_zero]
        ring
  have hrelF : Mv.aeval u (Mv.pderiv 0 F) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 F) * psD (u 1) = 0 := by
    rw [← hps_aeval_u F, hu_F0, v104]
  have hdu_ne : Ps.constantCoeff (psD (u 0)) ≠ 0 ∨ Ps.constantCoeff (psD (u 1)) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hdu_all : ∀ k : Fin 3, Ps.constantCoeff (psD (u k)) = 0 := by
      intro k; rcases v03 k with rfl | rfl | rfl
      · exact hall.1
      · exact hall.2
      · rw [hu2, v159, map_zero]
    have hdZ : ∀ k : Fin 3, Ps.constantCoeff (psD (Z k)) = (T.mulVec ![1, Ps.constantCoeff (psD Y'), 0]) k := by
      intro k
      have hpsZ : psD (Z k) = Ps.C (T k 0) * 1 + Ps.C (T k 1) * psD Y' + 0 := by
        simp only [Z, Fi.sum_univ_three, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, v51, v210, psD_C, psD_X, v159, zero_add, mul_zero]
      rw [hpsZ]
      simp [Mx.mulVec, dotProduct, Fi.sum_univ_three]
    set lam : L := Ps.constantCoeff (psD (Z 2)) * (Ps.constantCoeff (Z 2))⁻¹
    have hTvec : T.mulVec ![1, Ps.constantCoeff (psD Y'), 0] = lam • T.mulVec ![x', y', 1] := by
      ext k
      rw [← hdZ k, hZ_eq_u k, v29]
      simp only [map_add, map_mul, hdu_all k, mul_zero, add_zero]
      have hZk : Ps.constantCoeff (Z k) = (T.mulVec ![x', y', 1]) k := by
        rw [hZ_const k, hTpt]; rfl
      have hZ2_ne : Ps.constantCoeff (Z 2) ≠ 0 := by
        have := congr_arg Ps.constantCoeff hzz
        rw [map_mul, map_one] at this; exact left_ne_zero_of_mul_eq_one this
      have huk : Ps.constantCoeff (u k) = (Ps.constantCoeff (Z 2))⁻¹ * (T.mulVec ![x', y', 1]) k := by
        have hz2 : Ps.constantCoeff (Z 2) * Ps.constantCoeff (u k) = Ps.constantCoeff (Z k) := by rw [← map_mul, ← hZ_eq_u k]
        apply mul_left_cancel₀ hZ2_ne
        rw [hz2, hZk, ← mul_assoc, mul_inv_cancel₀ hZ2_ne, one_mul]
      rw [huk]; simp only [Pi.smul_apply, smul_eq_mul, lam]; ring
    have hvec := congr_arg (Tinv.mulVec) hTvec
    rw [Mx.mulVec_mulVec, hT2, Mx.one_mulVec, Mx.mulVec_smul, Mx.mulVec_mulVec, hT2, Mx.one_mulVec] at hvec
    have h2 := congr_fun hvec 2
    simp only [Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, Pi.smul_apply, smul_eq_mul, mul_one] at h2
    have h0 := congr_fun hvec 0
    simp only [Mx.cons_val_zero, Pi.smul_apply, smul_eq_mul, ← h2, zero_mul] at h0
    exact one_ne_zero h0
  have hu_fp : ∀ k : Fin 3, Ps.constantCoeff (u k) ^ p = Ps.constantCoeff (u k) := by
    intro k
    have hZ2_c : Ps.constantCoeff (Z 2) = c * ι (P 2) := hZ_const 2
    have hZk_c : Ps.constantCoeff (Z k) = c * ι (P k) := hZ_const k
    have hιP2 : ι (P 2) ≠ 0 := fun h0 => hP2 (ι.injective (h0.trans (map_zero ι).symm))
    have huk : Ps.constantCoeff (u k) = ι (P k * (P 2)⁻¹) := by
      have hz2 : Ps.constantCoeff (Z 2) * Ps.constantCoeff (u k) = Ps.constantCoeff (Z k) := by rw [← map_mul, ← hZ_eq_u k]
      rw [hZ2_c, hZk_c] at hz2
      apply mul_left_cancel₀ (mul_ne_zero hc hιP2)
      rw [hz2, map_mul, map_inv₀]
      field_simp [hc, hιP2]
    rw [huk, ← map_pow, ZMod.pow_card]
  have hconic_fp : ∀ j : Fin 6, Ps.constantCoeff (Mv.aeval u (cMon (K := L) j)) ^ p = Ps.constantCoeff (Mv.aeval u (cMon (K := L) j)) := by
    intro j
    rcases v36 j with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [cMon, v34, map_pow, Mv.aeval_X]; rw [pow_right_comm, hu_fp]
    · simp only [cMon, v33, map_mul, Mv.aeval_X, mul_pow, hu_fp]
    · simp only [cMon, v20, map_mul, Mv.aeval_X, mul_pow, hu_fp]
    · simp only [cMon, v19, map_pow, Mv.aeval_X]; rw [pow_right_comm, hu_fp]
    · simp only [cMon, v18, map_mul, Mv.aeval_X, mul_pow, hu_fp]
    · simp only [cMon, v15, map_pow, Mv.aeval_X]; rw [pow_right_comm, hu_fp]
  have hlam_ex : ∃ lam : PS L, ∀ P : Mv3 L, Mv.aeval u (derivZ F P) = lam * psD (Mv.aeval u P) := by
    rcases hdu_ne with h0 | h1
    · obtain ⟨v0, hv0⟩ := Ps.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h0)
      set inv0 : PS L := ↑v0⁻¹
      have hmul0 : psD (u 0) * inv0 = 1 := by dsimp only [inv0]; rw [← hv0]; exact Units.mul_inv v0
      refine ⟨Mv.aeval u (Mv.pderiv 1 F) * inv0, fun P => ?_⟩
      change Mv.aeval u (Mv.pderiv 1 F * Mv.pderiv 0 P - Mv.pderiv 0 F * Mv.pderiv 1 P) = _
      rw [map_sub, map_mul, map_mul, hps_aeval_u P]
      calc Mv.aeval u (Mv.pderiv 1 F) * Mv.aeval u (Mv.pderiv 0 P) - Mv.aeval u (Mv.pderiv 0 F) * Mv.aeval u (Mv.pderiv 1 P)
          = (Mv.aeval u (Mv.pderiv 1 F) * Mv.aeval u (Mv.pderiv 0 P) - Mv.aeval u (Mv.pderiv 0 F) * Mv.aeval u (Mv.pderiv 1 P)) * (psD (u 0) * inv0) := by rw [hmul0, mul_one]
        _ = Mv.aeval u (Mv.pderiv 1 F) * inv0 * (Mv.aeval u (Mv.pderiv 0 P) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 P) * psD (u 1)) - inv0 * Mv.aeval u (Mv.pderiv 1 P) * (Mv.aeval u (Mv.pderiv 0 F) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 F) * psD (u 1)) := by ring
        _ = Mv.aeval u (Mv.pderiv 1 F) * inv0 * (Mv.aeval u (Mv.pderiv 0 P) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 P) * psD (u 1)) := by
              rw [hrelF, mul_zero, sub_zero]
    · obtain ⟨v1, hv1⟩ := Ps.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h1)
      set inv1 : PS L := ↑v1⁻¹
      have hmul1 : psD (u 1) * inv1 = 1 := by dsimp only [inv1]; rw [← hv1]; exact Units.mul_inv v1
      refine ⟨-(Mv.aeval u (Mv.pderiv 0 F) * inv1), fun P => ?_⟩
      change Mv.aeval u (Mv.pderiv 1 F * Mv.pderiv 0 P - Mv.pderiv 0 F * Mv.pderiv 1 P) = _
      rw [map_sub, map_mul, map_mul, hps_aeval_u P]
      calc Mv.aeval u (Mv.pderiv 1 F) * Mv.aeval u (Mv.pderiv 0 P) - Mv.aeval u (Mv.pderiv 0 F) * Mv.aeval u (Mv.pderiv 1 P)
          = (Mv.aeval u (Mv.pderiv 1 F) * Mv.aeval u (Mv.pderiv 0 P) - Mv.aeval u (Mv.pderiv 0 F) * Mv.aeval u (Mv.pderiv 1 P)) * (psD (u 1) * inv1) := by rw [hmul1, mul_one]
        _ = -(Mv.aeval u (Mv.pderiv 0 F) * inv1) * (Mv.aeval u (Mv.pderiv 0 P) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 P) * psD (u 1)) + inv1 * Mv.aeval u (Mv.pderiv 0 P) * (Mv.aeval u (Mv.pderiv 0 F) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 F) * psD (u 1)) := by ring
        _ = -(Mv.aeval u (Mv.pderiv 0 F) * inv1) * (Mv.aeval u (Mv.pderiv 0 P) * psD (u 0) + Mv.aeval u (Mv.pderiv 1 P) * psD (u 1)) := by
              rw [hrelF, mul_zero, add_zero]
  rcases hlam_ex with ⟨lam, hlam⟩
  have hWZ_hom : (fWron p (derivZ F) cMon).IsHomogeneous (2 * p + 10 * d - 10) :=
    v32 p hF hd2 (derivZ F)
      (fun hP hk => v65 hF hP (by omega) hk)
  rw [hev_Z, haeval_hom hWZ_hom]
  apply dvd_mul_of_dvd_right
  have hiter : ∀ (n : ℕ) (P : Mv3 L), Mv.aeval u ((derivZ F)^[n] P) = (v48.smul lam)^[n] (Mv.aeval u P) := by
    intro n
    induction n with
    | zero => intro P; rfl
    | succ n ih =>
      intro P; simp only [Fn.iterate_succ_apply']
      rw [hlam, ← ih P]; rfl
  have hW_eq : Mv.aeval u (fWron p (derivZ F) cMon) = fWron p (v48.smul lam) (fun j => Mv.aeval u (cMon (K := L) j)) := by
    rw [fWron, fWron, ← Ah.coe_toRingHom, Rh.map_det]
    congr 1; refine Mx.ext fun i j => ?_
    simp only [Rh.mapMatrix_apply, Mx.map_apply, Ah.coe_toRingHom]
    have h1 := hiter 1 (cMon j)
    have h2 := hiter 2 (cMon j)
    have h3 := hiter 3 (cMon j)
    have h4 := hiter 4 (cMon j)
    simp only [Fn.iterate_succ, Fn.iterate_zero, Fn.comp_apply, id_eq] at h1 h2 h3 h4
    rcases v36 i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [v08]
    · simp [v08]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  rw [hW_eq, v112 p v48 lam]
  exact dvd_mul_of_dvd_right (fWron_t5_dvd hp hp5 _ hconic_fp) _
set_option maxHeartbeats 800000 in
theorem v173 {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L p]
    {F : Mv3 L} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F) (hd3 : 3 ≤ d) (hdp : 2 * d < p) :
    5 * ((pPts p).filter (fun P => Mv.eval ((ZMod.castHom (dvd_refl p) L) ∘ P) F = 0)).card ≤ d * (2 * p + 10 * d - 20) := by
  have hp : Nat.Prime p := Fact.out
  set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
  set S : Finset (Fin 3 → ZMod p) :=
    (pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)
  have hQ_ex : ∃ Q : Fin 3 → ZMod p, Q ≠ 0 ∧ Mv.eval (ι ∘ Q) F ≠ 0 := by
    by_contra hall; push Not at hall
    have hde0 : dhZ F = 0 := by
      have hval_a : ∀ a : ZMod p, (dhZ F).map (Pl.evalRingHom (ι a)) = 0 := by
        intro a
        set pa := (dhZ F).map (Pl.evalRingHom (ι a))
        by_contra hpa
        have hdeg_pa : pa.natDegree ≤ d := by
          apply Pl.natDegree_le_iff_coeff_eq_zero.mpr
          intro k hk
          rw [Pl.coeff_map, v93 hF hk, map_zero]
        have hroots : Fs.univ.image ι ⊆ pa.roots.toFinset := by
          intro y hy
          rcases mem_image.mp hy with ⟨b, _, rfl⟩
          rw [Mu.mem_toFinset, Pl.mem_roots hpa, Pl.IsRoot]
          have h1 : pa.eval (ι b) = Mv.eval ![ι a, ι b, 1] F := v136 F (ι a) (ι b)
          rw [h1]
          have hvec : ![ι a, ι b, 1] = ι ∘ ![a, b, 1] := by
            ext i; rcases v03 i with rfl | rfl | rfl <;> simp
          rw [hvec]
          exact hall ![a, b, 1] (fun h0 => (one_ne_zero : (1 : ZMod p) ≠ 0) (by simpa using congr_fun h0 2))
        have hcard1 : (Fs.univ.image ι).card = p := by
          rw [card_image_of_injective _ ι.injective, card_univ, ZMod.card p]
        have hcard2 : pa.roots.toFinset.card ≤ d :=
          (Mu.toFinset_card_le _).trans ((Pl.card_roots' pa).trans hdeg_pa)
        have hle := card_le_card hroots
        omega
      apply Pl.ext; intro b
      rw [Pl.coeff_zero]
      set qb := (dhZ F).coeff b
      by_contra hqb
      have hdeg_qb : qb.natDegree ≤ d := by
        rcases v102 hF b with h | h
        · dsimp only [qb]; omega
        · exact absurd h hqb
      have hroots : Fs.univ.image ι ⊆ qb.roots.toFinset := by
        intro x hx
        rcases mem_image.mp hx with ⟨a, _, rfl⟩
        rw [Mu.mem_toFinset, Pl.mem_roots hqb]
        have := congr_arg (fun r : Pol L => r.coeff b) (hval_a a)
        simpa [qb] using this
      have hcard1 : (Fs.univ.image ι).card = p := by
        rw [card_image_of_injective _ ι.injective, card_univ, ZMod.card p]
      have hcard2 : qb.roots.toFinset.card ≤ d :=
        (Mu.toFinset_card_le _).trans ((Pl.card_roots' qb).trans hdeg_qb)
      have hle := card_le_card hroots
      omega
    have hF0 : F = 0 := v77 hF (Mv.isHomogeneous_zero _ _ d)
      (by rw [hde0]; simp [dhZ])
    exact hF_irr.ne_zero hF0
  suffices hmain : ∀ {F₀ : Mv3 L}, F₀.IsHomogeneous d → Irreducible F₀ → Mv.eval ![0, 1, 0] F₀ ≠ 0 → 5 * ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F₀ = 0)).card ≤ d * (2 * p + 10 * d - 20) by
    rcases hQ_ex with ⟨Q, hQ_ne, hFQ⟩
    have hex_i : ∃ i : Fin 3, Q i ≠ 0 := by
      by_contra hall; push Not at hall; exact hQ_ne (funext hall)
    rcases hex_i with ⟨i, hi⟩
    have hA_ex : ∃ A Ainv : Mat3 (ZMod p), A * Ainv = 1 ∧ Ainv * A = 1 ∧ A.mulVec ![0, 1, 0] = Q := by
      rcases v03 i with rfl | rfl | rfl
      · let A : Mat3 (ZMod p) := !![0, Q 0, 0; 1, Q 1, 0; 0, Q 2, 1]
        let Ai : Mat3 (ZMod p) :=
          !![-Q 1 * (Q 0)⁻¹, 1, 0; (Q 0)⁻¹, 0, 0; -Q 2 * (Q 0)⁻¹, 0, 1]
        refine ⟨A, Ai, ?_, ?_, ?_⟩
        · refine Mx.ext fun r c => ?_
          fin_cases r <;> fin_cases c <;>
            simp [A, Ai, Mx.mul_apply, Fi.sum_univ_three]; field_simp [hi]
        · refine Mx.ext fun r c => ?_
          fin_cases r <;> fin_cases c <;>
            simp [A, Ai, Mx.mul_apply, Fi.sum_univ_three] <;> field_simp [hi] <;> ring
        · ext r; fin_cases r <;> simp [A, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      · let A : Mat3 (ZMod p) := !![1, Q 0, 0; 0, Q 1, 0; 0, Q 2, 1]
        let Ai : Mat3 (ZMod p) :=
          !![1, -Q 0 * (Q 1)⁻¹, 0; 0, (Q 1)⁻¹, 0; 0, -Q 2 * (Q 1)⁻¹, 1]
        refine ⟨A, Ai, ?_, ?_, ?_⟩
        · refine Mx.ext fun r c => ?_
          fin_cases r <;> fin_cases c <;>
            simp [A, Ai, Mx.mul_apply, Fi.sum_univ_three]; field_simp [hi]
        · refine Mx.ext fun r c => ?_
          fin_cases r <;> fin_cases c <;>
            simp [A, Ai, Mx.mul_apply, Fi.sum_univ_three] <;> field_simp [hi] <;> ring
        · ext r; fin_cases r <;> simp [A, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      · let A : Mat3 (ZMod p) := !![1, Q 0, 0; 0, Q 1, 1; 0, Q 2, 0]
        let Ai : Mat3 (ZMod p) :=
          !![1, 0, -Q 0 * (Q 2)⁻¹; 0, 0, (Q 2)⁻¹; 0, 1, -Q 1 * (Q 2)⁻¹]
        refine ⟨A, Ai, ?_, ?_, ?_⟩
        · refine Mx.ext fun r c => ?_
          fin_cases r <;> fin_cases c <;>
            simp [A, Ai, Mx.mul_apply, Fi.sum_univ_three]; field_simp [hi]
        · refine Mx.ext fun r c => ?_
          fin_cases r <;> fin_cases c <;>
            simp [A, Ai, Mx.mul_apply, Fi.sum_univ_three] <;> field_simp [hi] <;> ring
        · ext r; fin_cases r <;> simp [A, Mx.mulVec, dotProduct, Fi.sum_univ_three]
    rcases hA_ex with ⟨A, Ainv, hAA1, hAA2, hAQ⟩
    let AL : Mat3 L := ι.mapMatrix A
    let ALi : Mat3 L := ι.mapMatrix Ainv
    have hAL1 : AL * ALi = 1 := by
      rw [← map_mul, hAA1, map_one]
    have hAL2 : ALi * AL = 1 := by
      rw [← map_mul, hAA2, map_one]
    set F₀ := sMat AL F
    have hF₀_hom : F₀.IsHomogeneous d := v25 AL hF
    have hF₀_irr : Irreducible F₀ := v88 hAL1 hAL2 hF_irr
    have hF₀_010 : Mv.eval ![0, 1, 0] F₀ ≠ 0 := by
      rw [v50]
      have hvec : AL.mulVec ![0, 1, 0] = ι ∘ Q := by
        rw [← hAQ]; ext r
        simp [AL, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      rw [hvec]; exact hFQ
    have hcard_eq : S.card = ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F₀ = 0)).card := by
      apply card_bij (fun P _ => normPt (Ainv.mulVec P))
      · intro P hP
        have hPn : v53 P := v30.mp (mem_filter.mp hP).1
        have hFP : Mv.eval (ι ∘ P) F = 0 := (mem_filter.mp hP).2
        have hAiP_ne : Ainv.mulVec P ≠ 0 := fun h0 => v00 hPn (by
          calc P = (A * Ainv).mulVec P := by rw [hAA1, Mx.one_mulVec]
            _ = A.mulVec (Ainv.mulVec P) := (Mx.mulVec_mulVec _ _ _).symm
            _ = 0 := by rw [h0, Mx.mulVec_zero])
        rw [mem_filter]
        refine ⟨v90 hAiP_ne, ?_⟩
        obtain ⟨_, c, hc, hnorm⟩ := v38 hAiP_ne
        have hιnorm : ι ∘ normPt (Ainv.mulVec P) = ι c • (ALi.mulVec (ι ∘ P)) := by
          ext r; simp only [Fn.comp_apply, hnorm, Pi.smul_apply, smul_eq_mul, map_mul, ALi, Rh.mapMatrix_apply, Mx.map_apply, Mx.mulVec, dotProduct, Fi.sum_univ_three, map_add]
        rw [hιnorm, v05 hF₀_hom, v50, Mx.mulVec_mulVec, hAL1, Mx.one_mulVec, hFP, mul_zero]
      · intro P₁ hP₁ P₂ hP₂ heq
        have hP1n : v53 P₁ := v30.mp (mem_filter.mp hP₁).1
        have hP2n : v53 P₂ := v30.mp (mem_filter.mp hP₂).1
        have hne1 : Ainv.mulVec P₁ ≠ 0 := fun h0 => v00 hP1n (by
          rw [← Mx.one_mulVec P₁, ← hAA1, ← Mx.mulVec_mulVec, h0, Mx.mulVec_zero])
        have hne2 : Ainv.mulVec P₂ ≠ 0 := fun h0 => v00 hP2n (by
          rw [← Mx.one_mulVec P₂, ← hAA1, ← Mx.mulVec_mulVec, h0, Mx.mulVec_zero])
        rcases (v44 hne1 hne2).mp heq with ⟨c, hc, hsc⟩
        have hP12 : P₁ = c • P₂ := by
          calc P₁ = A.mulVec (Ainv.mulVec P₁) := by rw [Mx.mulVec_mulVec, hAA1, Mx.one_mulVec]
            _ = A.mulVec (c • Ainv.mulVec P₂) := by rw [hsc]
            _ = c • A.mulVec (Ainv.mulVec P₂) := Mx.mulVec_smul _ _ _
            _ = c • P₂ := by rw [Mx.mulVec_mulVec, hAA1, Mx.one_mulVec]
        exact v04 hP1n hP2n hP12
      · intro R hR
        have hRn : v53 R := v30.mp (mem_filter.mp hR).1
        have hFR : Mv.eval (ι ∘ R) F₀ = 0 := (mem_filter.mp hR).2
        have hAR_ne : A.mulVec R ≠ 0 := fun h0 => v00 hRn (by
          rw [← Mx.one_mulVec R, ← hAA2, ← Mx.mulVec_mulVec, h0, Mx.mulVec_zero])
        refine ⟨normPt (A.mulVec R), ?_, ?_⟩
        · rw [mem_filter]
          refine ⟨v90 hAR_ne, ?_⟩
          obtain ⟨_, c, hc, hnorm⟩ := v38 hAR_ne
          have hιnorm : ι ∘ normPt (A.mulVec R) = ι c • (AL.mulVec (ι ∘ R)) := by
            ext r; simp only [Fn.comp_apply, hnorm, Pi.smul_apply, smul_eq_mul, map_mul, AL, Rh.mapMatrix_apply, Mx.map_apply, Mx.mulVec, dotProduct, Fi.sum_univ_three, map_add]
          rw [hιnorm, v05 hF, ← v50, hFR, mul_zero]
        · obtain ⟨_, c, hc, hnorm⟩ := v38 hAR_ne
          have h1 : Ainv.mulVec (normPt (A.mulVec R)) = c • R := by
            rw [hnorm, Mx.mulVec_smul, Mx.mulVec_mulVec, hAA2, Mx.one_mulVec]
          rw [h1, v179 (v00 hRn) hc, v94 hRn]
    rw [hcard_eq]
    exact hmain hF₀_hom hF₀_irr hF₀_010
  clear hQ_ex F hF hF_irr S
  intro F hF hF_irr h010
  set S : Finset (Fin 3 → ZMod p) :=
    (pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)
  by_cases hS_empty : S = ∅
  · rw [hS_empty, card_empty, mul_zero]; exact Nat.zero_le _
  obtain ⟨Wt, hWt_hom, hF_ndvd_Wt, hcompatZ, hcompatX, hcompatY⟩ :=
    v192 hp hp7 hF hF_irr hd3 hdp h010
  obtain ⟨R0, hR0_spec, hR0_cov⟩ := v60 hF hF_irr (by omega) 0
  obtain ⟨R1, hR1_spec, hR1_cov⟩ := v60 hF hF_irr (by omega) 1
  obtain ⟨R2, hR2_spec, hR2_cov⟩ := v60 hF hF_irr (by omega) 2
  let Rset : Fin 3 → Finset (Fin 3 → L) := ![R0, R1, R2]
  let gradF : (Fin 3 → L) → (Fin 3 → L) :=
    fun v i => Mv.eval v (Mv.pderiv i F)
  let badTangents : Finset (Fin 3 → L) :=
    (S.image (fun P => gradF (ι ∘ P))).filter (fun g => g ≠ 0)
  let badSecants : Finset (Fin 3 → L) :=
    S.offDiag.image (fun ab => cross3 (ι ∘ ab.1) (ι ∘ ab.2))
  let badCoordLines : Finset (Fin 3 → L) :=
    Fs.univ.biUnion fun j : Fin 3 =>
      (S.filter (fun P => P j ≠ 0)).biUnion fun P =>
        (Rset j).image fun r => cross3 (ι ∘ P) r
  let badLines : Finset (Fin 3 → L) := badTangents ∪ (badSecants ∪ badCoordLines)
  have hbad_ne : ∀ l ∈ badLines, l ≠ 0 := by
    intro l hl
    rcases mem_union.mp hl with h1 | h23
    · exact (mem_filter.mp h1).2
    · rcases mem_union.mp h23 with h2 | h3
      · rcases mem_image.mp h2 with ⟨⟨P₁, P₂⟩, hmem, rfl⟩
        rcases mem_offDiag.mp hmem with ⟨h1S, h2S, hne⟩
        have hP1n := v30.mp (mem_filter.mp h1S).1
        have hP2n := v30.mp (mem_filter.mp h2S).1
        intro hcr0
        have hιP1 : ι ∘ P₁ ≠ 0 := fun h0 => v00 hP1n (funext fun i =>
          ι.injective ((congr_fun h0 i).trans (map_zero ι).symm))
        rcases (v01 hιP1).mp hcr0 with ⟨c, hc⟩
        have hex1 : ∃ k : Fin 3, P₁ k ≠ 0 := by
          by_contra ha; push Not at ha; exact v00 hP1n (funext ha)
        rcases hex1 with ⟨k, hk⟩
        have hc_eq : c = ι (P₂ k * (P₁ k)⁻¹) := by
          have h1 := congr_fun hc k
          simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
          have hιk : ι (P₁ k) ≠ 0 := fun h0 => hk (ι.injective (h0.trans (map_zero ι).symm))
          rw [map_mul, map_inv₀, h1]; field_simp [hιk]
        have hP21 : P₂ = (P₂ k * (P₁ k)⁻¹) • P₁ := by
          ext i; apply ι.injective
          have h1 := congr_fun hc i
          simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
          rw [← map_mul, ← hc_eq]; exact h1
        exact hne (v04 hP2n hP1n hP21).symm
      · rcases mem_biUnion.mp h3 with ⟨j, _, hj⟩
        rcases mem_biUnion.mp hj with ⟨P, hP, hPr⟩
        rcases mem_image.mp hPr with ⟨r, hr, rfl⟩
        have hPj : P j ≠ 0 := (mem_filter.mp hP).2
        have hr_spec : r ≠ 0 ∧ r j = 0 := by
          rcases v03 j with rfl | rfl | rfl
          · exact hR0_spec r hr
          · exact hR1_spec r hr
          · exact hR2_spec r hr
        intro hcr0
        have hιP : ι ∘ P ≠ 0 := fun h0 => hPj (ι.injective ((congr_fun h0 j).trans (map_zero ι).symm))
        rcases (v01 hιP).mp hcr0 with ⟨c, hc⟩
        have h1 := congr_fun hc j
        simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul, hr_spec.2] at h1
        have hιPj : ι (P j) ≠ 0 := fun h0 => hPj (ι.injective (h0.trans (map_zero ι).symm))
        have hc0 : c = 0 := (mul_eq_zero.mp h1.symm).resolve_right hιPj
        rw [hc0, zero_smul] at hc; exact hr_spec.1 hc
  let bigPoly : Mv3 L := F * ∏ l ∈ badLines, v55 l
  have hbig_ne : bigPoly ≠ 0 := by
    apply mul_ne_zero hF_irr.ne_zero
    rw [prod_ne_zero_iff]
    intro l hl h0
    have hl_ne := hbad_ne l hl
    have hex : ∃ i : Fin 3, l i ≠ 0 := by by_contra ha; push Not at ha; exact hl_ne (funext ha)
    rcases hex with ⟨i, hi⟩
    have := congr_arg (Mv.eval (Pi.single i 1)) h0
    rw [v27, map_zero] at this
    apply hi
    rcases v03 i with rfl | rfl | rfl <;> simpa [dot3, Pi.single_apply] using this
  obtain ⟨q_inf, hq_big⟩ := v46 hbig_ne
  rw [map_mul, map_prod] at hq_big
  have hFq_ne : Mv.eval q_inf F ≠ 0 := left_ne_zero_of_mul hq_big
  have hq_ne : q_inf ≠ 0 := fun h0 => hFq_ne (by
    rw [h0, Mv.eval_zero]
    by_contra hc0; have := v10 hF hc0; simp at this; omega)
  have hq_bad : ∀ l ∈ badLines, dot3 l q_inf ≠ 0 := by
    intro l hl h0
    apply right_ne_zero_of_mul hq_big
    apply prod_eq_zero hl
    rw [v27, h0]
  have hS_not_prop : ∀ v ∈ S.image (fun P => ι ∘ P), cross3 q_inf v ≠ 0 := by
    intro v hv hcr
    rcases mem_image.mp hv with ⟨P, hPS, rfl⟩
    rcases (v01 hq_ne).mp hcr with ⟨c, hc⟩
    have hFP : Mv.eval (ι ∘ P) F = 0 := (mem_filter.mp hPS).2
    rw [hc, v05 hF] at hFP
    have hc0 : c = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hFP).resolve_right hFq_ne)
    rw [hc0, zero_smul] at hc
    have hPn := v30.mp (mem_filter.mp hPS).1
    exact v00 hPn (funext fun i => ι.injective ((congr_fun hc i).trans (map_zero ι).symm))
  obtain ⟨n, hnq, hnS⟩ := v114 q_inf hq_ne (S.image (fun P => ι ∘ P)) hS_not_prop
  have hn_ne : n ≠ 0 := by
    obtain ⟨P, hPS⟩ := nonempty_iff_ne_empty.mpr hS_empty
    intro h0; exact hnS (ι ∘ P) (mem_image_of_mem _ hPS) (by rw [h0, v135])
  have hex_n : ∃ i : Fin 3, n i ≠ 0 := by by_contra ha; push Not at ha; exact hn_ne (funext ha)
  rcases hex_n with ⟨in0, hin0⟩
  let v₂ : Fin 3 → L := Pi.single in0 (n in0)⁻¹
  have hnv2 : dot3 n v₂ = 1 := by
    rcases v03 in0 with rfl | rfl | rfl <;>
      simp [v₂, dot3, mul_inv_cancel₀ hin0]
  have hv0_ex : ∃ v₀ : Fin 3 → L, dot3 n v₀ = 0 ∧ det3 v₀ q_inf v₂ ≠ 0 := by
    have htwo : ∃ w₁ w₂ : Fin 3 → L, dot3 n w₁ = 0 ∧ dot3 n w₂ = 0 ∧ cross3 w₁ w₂ ≠ 0 := by
      rcases v03 in0 with rfl | rfl | rfl
      · exact ⟨![-n 1, n 0, 0], ![-n 2, 0, n 0], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 0; simp [cross3] at this; exact hin0 this⟩
      · exact ⟨![n 1, -n 0, 0], ![0, -n 2, n 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 1; simp [cross3] at this; exact hin0 this⟩
      · exact ⟨![n 2, 0, -n 0], ![0, n 2, -n 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 2; simp [cross3] at this; exact hin0 this⟩
    rcases htwo with ⟨w₁, w₂, hw1, hw2, hcr12⟩
    have hdet_of_cr : ∀ w : Fin 3 → L, dot3 n w = 0 → cross3 w q_inf ≠ 0 → det3 w q_inf v₂ ≠ 0 := by
      intro w hw hcr hdet0
      rw [v14] at hdet0
      rcases v09 hcr hw hnq with ⟨c, hc⟩
      have hc_ne : c ≠ 0 := fun h0 => hn_ne (by rw [hc, h0, zero_smul])
      rw [hc, v06, hdet0, mul_zero] at hnv2
      exact one_ne_zero hnv2.symm
    by_cases h1 : cross3 w₁ q_inf ≠ 0
    · exact ⟨w₁, hw1, hdet_of_cr w₁ hw1 h1⟩
    · push Not at h1
      refine ⟨w₂, hw2, hdet_of_cr w₂ hw2 ?_⟩
      intro h2
      rcases (v01 hq_ne).mp (by rw [v69, neg_eq_zero]; exact h1) with ⟨c1, hc1⟩
      rcases (v01 hq_ne).mp (by rw [v69, neg_eq_zero]; exact h2) with ⟨c2, hc2⟩
      apply hcr12
      rw [hc1, hc2, v72, v42, v85, smul_zero, smul_zero]
  rcases hv0_ex with ⟨v₀, hnv0, hdet_T⟩
  let T : Mat3 L := Mx.of fun i j =>
    match j with
    | ⟨0, _⟩ => v₀ i
    | ⟨1, _⟩ => q_inf i
    | ⟨2, _⟩ => v₂ i
  have hT_det : T.det ≠ 0 := by
    have h1 : T.det = det3 v₀ q_inf v₂ := by
      rw [← Mx.det_transpose, v127]
      congr 1; refine Mx.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [T]
    rw [h1]; exact hdet_T
  let Tinv : Mat3 L := T⁻¹
  have hT1 : T * Tinv = 1 := Mx.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT_det)
  have hT2 : Tinv * T = 1 := Mx.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT_det)
  have hT_010 : T.mulVec ![0, 1, 0] = q_inf := by
    ext i; simp [T, Mx.mulVec, dotProduct, Fi.sum_univ_three]
  have hT_dot_n : ∀ w : Fin 3 → L, dot3 n (T.mulVec w) = w 2 := by
    intro w
    have hlin : T.mulVec w = w 0 • v₀ + w 1 • q_inf + w 2 • v₂ := by
      ext i; simp [T, Mx.mulVec, dotProduct, Fi.sum_univ_three]; ring
    rw [hlin, v13, v13, v02, v02, v02, hnv0, hnq, hnv2]; ring
  set F' := sMat T F
  set Wt' := sMat T Wt
  have hF'_hom : F'.IsHomogeneous d := v25 T hF
  have hF'_irr : Irreducible F' := v88 hT1 hT2 hF_irr
  have hF'_010 : Mv.eval ![0, 1, 0] F' ≠ 0 := by
    rw [v50, hT_010]; exact hFq_ne
  have hWt'_hom : Wt'.IsHomogeneous (2 * p + 10 * d - 20) := v25 T hWt_hom
  have hF'_ndvd_Wt' : ¬ F' ∣ Wt' := by
    rwa [v131 hT1 hT2]
  set f' := mdhZ F'
  obtain ⟨hf'_mon, hf'_deg⟩ := v149 hF'_hom hF'_010
  have hf'_irr : Irreducible f' := v71 hF'_hom hF'_irr hF'_010
  have hf'_ndvd_Wt' : ¬ f' ∣ dhZ Wt' := by
    intro hdvd
    apply hF'_ndvd_Wt'
    have hdeF_dvd : dhZ F' ∣ dhZ Wt' := by
      rcases hdvd with ⟨q, hq⟩
      exact ⟨Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')⁻¹) * q, by rw [hq]; simp only [f', mdhZ]; ring⟩
    rcases hdeF_dvd with ⟨q, hq⟩
    set m := bDeg q
    set Q := hmZ m q
    have hde_eq : dhZ (F' * Q) = dhZ Wt' := by
      rw [v126, v198 (le_refl m), hq]
    have hFQ_hom : (F' * Q).IsHomogeneous (d + m) := hF'_hom.mul (v58 (le_refl m))
    by_cases hle : d + m ≤ 2 * p + 10 * d - 20
    · have heq := v22 hFQ_hom hWt'_hom hle hde_eq
      exact ⟨Mv.X 2 ^ (2 * p + 10 * d - 20 - (d + m)) * Q, by rw [← heq]; ring⟩
    · have heq := v22 hWt'_hom hFQ_hom (by omega) hde_eq.symm
      have hF'_prime : Prime F' := Ufm.irreducible_iff_prime.mp hF'_irr
      have hX2_ndvd : ¬ F' ∣ Mv.X 2 := by
        rintro ⟨u, hu⟩
        rcases (v89 2).irreducible.isUnit_or_isUnit hu with hFu | huu
        · exact hF'_irr.not_isUnit hFu
        · rcases huu with ⟨v, hv⟩
          have hFeq : F' = Mv.X 2 * ((v⁻¹ : (Mv3 L)ˣ) : Mv3 L) := by
            rw [hu, ← hv, mul_assoc, Units.mul_inv, mul_one]
          have := congr_arg (Mv.eval ![0, 1, 0]) hFeq
          simp only [map_mul, Mv.eval_X, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, zero_mul] at this
          exact hF'_010 this
      exact (hF'_prime.dvd_or_dvd ⟨Q, heq⟩).resolve_left
        (fun hpow => hX2_ndvd (hF'_prime.dvd_of_dvd_pow hpow))
  set Npoly : Pol L := pNorm f' (dhZ Wt')
  have hN_ne : Npoly ≠ 0 := v83 hf'_mon hf'_irr hf'_ndvd_Wt'
  have hN_deg : Npoly.natDegree ≤ d * (2 * p + 10 * d - 20) := by
    have hf'_bd : ∀ k, f'.coeff k ≠ 0 → (f'.coeff k).natDegree + k ≤ f'.natDegree := by
      intro k hk; rw [hf'_deg]; exact (v133 hF'_hom k).resolve_right hk
    have hW_bd : ∀ k, (dhZ Wt').coeff k ≠ 0 → ((dhZ Wt').coeff k).natDegree + k ≤ 2 * p + 10 * d - 20 := by
      intro k hk; exact (v102 hWt'_hom k).resolve_right hk
    simpa [Npoly, hf'_deg] using v74 hf'_mon (2 * p + 10 * d - 20) hf'_bd hW_bd
  let xP : (Fin 3 → ZMod p) → L := fun P => (dot3 n (ι ∘ P))⁻¹ * (Tinv.mulVec (ι ∘ P)) 0
  let yP : (Fin 3 → ZMod p) → L := fun P => (dot3 n (ι ∘ P))⁻¹ * (Tinv.mulVec (ι ∘ P)) 1
  have hT_P : ∀ P ∈ S, T.mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P) := by
    intro P hPS
    have hnP : dot3 n (ι ∘ P) ≠ 0 := hnS (ι ∘ P) (mem_image_of_mem _ hPS)
    have h2 : (Tinv.mulVec (ι ∘ P)) 2 = dot3 n (ι ∘ P) := by
      rw [← hT_dot_n (Tinv.mulVec (ι ∘ P)), Mx.mulVec_mulVec, hT1, Mx.one_mulVec]
    have hvec : ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • Tinv.mulVec (ι ∘ P) := by
      ext i; fin_cases i
      · rfl
      · rfl
      · simp [h2, inv_mul_cancel₀ hnP]
    rw [hvec, Mx.mulVec_smul, Mx.mulVec_mulVec, hT1, Mx.one_mulVec]
  have hxP_inj : Set.InjOn xP ↑S := by
    intro P₁ hP₁ P₂ hP₂ heq
    by_contra hne
    have h1 := hT_P P₁ hP₁
    have h2 := hT_P P₂ hP₂
    have hn1 : dot3 n (ι ∘ P₁) ≠ 0 := hnS (ι ∘ P₁) (mem_image_of_mem _ hP₁)
    have hn2 : dot3 n (ι ∘ P₂) ≠ 0 := hnS (ι ∘ P₂) (mem_image_of_mem _ hP₂)
    have hdiff : T.mulVec ![0, yP P₁ - yP P₂, 0] = (dot3 n (ι ∘ P₁))⁻¹ • (ι ∘ P₁) - (dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂) := by
      rw [← h1, ← h2, ← Mx.mulVec_sub]
      congr 1; ext i; fin_cases i <;> simp [heq]
    have hTq : T.mulVec ![0, yP P₁ - yP P₂, 0] = (yP P₁ - yP P₂) • q_inf := by
      have : ![0, yP P₁ - yP P₂, 0] = (yP P₁ - yP P₂) • ![0, 1, 0] := by ext i; fin_cases i <;> simp
      rw [this, Mx.mulVec_smul, hT_010]
    have hy_ne : yP P₁ - yP P₂ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hTq
      rw [h0] at hdiff
      have hsc : (dot3 n (ι ∘ P₁))⁻¹ • (ι ∘ P₁) = (dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂) :=
        sub_eq_zero.mp (hdiff.symm.trans hTq)
      have hP12_cr : cross3 (ι ∘ P₁) (ι ∘ P₂) = 0 := by
        have hP2_eq : ι ∘ P₂ = (dot3 n (ι ∘ P₂) * (dot3 n (ι ∘ P₁))⁻¹) • (ι ∘ P₁) := by
          ext i; have hsc_i := congr_fun hsc i
          simp only [Pi.smul_apply, smul_eq_mul] at hsc_i ⊢
          calc (ι ∘ P₂) i = dot3 n (ι ∘ P₂) * ((dot3 n (ι ∘ P₂))⁻¹ * (ι ∘ P₂) i) := by
                rw [← mul_assoc, mul_inv_cancel₀ hn2, one_mul]
            _ = dot3 n (ι ∘ P₂) * ((dot3 n (ι ∘ P₁))⁻¹ * (ι ∘ P₁) i) := by rw [← hsc_i]
            _ = dot3 n (ι ∘ P₂) * (dot3 n (ι ∘ P₁))⁻¹ * (ι ∘ P₁) i := by ring
        rw [hP2_eq, v42, v85, smul_zero]
      exact hbad_ne _ (mem_union_right _ (mem_union_left _
        (mem_image.mpr ⟨(P₁, P₂), mem_offDiag.mpr ⟨hP₁, hP₂, hne⟩, rfl⟩))) hP12_cr
    have hdot0 : dot3 (cross3 (ι ∘ P₁) (ι ∘ P₂)) q_inf = 0 := by
      have h := congr_arg (dot3 (cross3 (ι ∘ P₁) (ι ∘ P₂))) (hTq.symm.trans hdiff)
      rw [v02] at h
      conv at h => rhs; rw [sub_eq_add_neg, v13, v02, v56, mul_zero, zero_add]
      have hneg : dot3 (cross3 (ι ∘ P₁) (ι ∘ P₂)) (-((dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂))) = 0 := by
        have : -((dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂)) = (-(dot3 n (ι ∘ P₂))⁻¹) • (ι ∘ P₂) := by
          ext i; simp
        rw [this, v02, v28, mul_zero]
      rw [hneg] at h
      exact (mul_eq_zero.mp h).resolve_left hy_ne
    exact hq_bad _ (mem_union_right _ (mem_union_left _
      (mem_image.mpr ⟨(P₁, P₂), mem_offDiag.mpr ⟨hP₁, hP₂, hne⟩, rfl⟩))) hdot0
  have hlocal : ∀ P ∈ S, (Pl.X - Pl.C (xP P)) ^ 5 ∣ Npoly := by
    intro P hPS
    have hPn : v53 P := v30.mp (mem_filter.mp hPS).1
    have hFP : Mv.eval (ι ∘ P) F = 0 := (mem_filter.mp hPS).2
    have hnP : dot3 n (ι ∘ P) ≠ 0 := hnS (ι ∘ P) (mem_image_of_mem _ hPS)
    have hc_ne : (dot3 n (ι ∘ P))⁻¹ ≠ 0 := inv_ne_zero hnP
    have hTP := hT_P P hPS
    have hF'P : Mv.eval ![xP P, yP P, 1] F' = 0 := by
      rw [v50, hTP, v05 hF, hFP, mul_zero]
    have hroot : (f'.map (Pl.evalRingHom (xP P))).eval (yP P) = 0 := by
      simp only [f', mdhZ, Pl.map_mul, Pl.eval_mul, v136, hF'P, mul_zero]
    have hj_ex : ∃ j : Fin 3, P j ≠ 0 := by
      by_contra ha; push Not at ha; exact v00 hPn (funext ha)
    rcases hj_ex with ⟨j, hPj⟩
    let Wj : Mv3 L :=
      match j with
      | ⟨0, _⟩ => fWron p (derivX F) cMon
      | ⟨1, _⟩ => fWron p (derivY F) cMon
      | ⟨2, _⟩ => fWron p (derivZ F) cMon
    have hcompat_j : F ∣ Wj - Mv.X j ^ 10 * Wt := by
      rcases v03 j with rfl | rfl | rfl
      · exact hcompatX
      · exact hcompatY
      · exact hcompatZ
    set Wj' := sMat T Wj
    set Lj' := sMat T (Mv.X j)
    have hcompat_j' : F' ∣ Wj' - Lj' ^ 10 * Wt' := by
      have := (v131 hT1 hT2 F (Wj - Mv.X j ^ 10 * Wt)).mpr hcompat_j
      simpa only [F', Wj', Lj', map_sub, map_mul, map_pow] using this
    by_cases hsm : gradF (ι ∘ P) ≠ 0
    ·
      have hgrad_q : dot3 (gradF (ι ∘ P)) q_inf ≠ 0 :=
        hq_bad _ (mem_union_left _ (mem_filter.mpr ⟨mem_image_of_mem _ hPS, hsm⟩))
      have hFy'_ne : Mv.eval ![xP P, yP P, 1] (Mv.pderiv 1 F') ≠ 0 := by
        rw [v67, map_sum]
        have hsum : ∑ i : Fin 3, Mv.eval ![xP P, yP P, 1]
              (Mv.C (T i 1) * sMat T (Mv.pderiv i F)) =
            (dot3 n (ι ∘ P))⁻¹ ^ (d - 1) * dot3 (gradF (ι ∘ P)) q_inf := by
          rw [Fi.sum_univ_three]
          simp only [map_mul, Mv.eval_C, v50, hTP, v05 (v12 hF _), T, Mx.of_apply, dot3, gradF]
          ring
        rw [hsum]
        exact mul_ne_zero (pow_ne_zero _ hc_ne) hgrad_q
      have hderiv_ne : (f'.derivative.map (Pl.evalRingHom (xP P))).eval (yP P) ≠ 0 := by
        have hsc : f'.derivative = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')⁻¹) * (dhZ F').derivative := by simp [f', mdhZ]
        rw [hsc, Pl.map_mul, Pl.eval_mul, Pl.map_C, Pl.eval_C, Pl.coe_evalRingHom, Pl.eval_C, ← v183, v136]
        exact mul_ne_zero (inv_ne_zero hF'_010) hFy'_ne
      obtain ⟨Y', hY'0, hY'root⟩ := v75 f' (xP P) (yP P) hroot hderiv_ne
      have hF'0 : evBr (xP P) Y' F' = 0 := by
        rw [v62]
        have hsc : dhZ F' = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')) * f' := by
          simp [f', mdhZ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hF'_010]
        rw [hsc, Pl.map_mul, Pl.eval_mul, hY'root, mul_zero]
      have hsubC : ∀ (M : Mat3 L) (a : L), sMat M (Mv.C a) = Mv.C a := fun M a => by simp [sMat]
      have ht5_Wj : Ps.X ^ 5 ∣ evBr (xP P) Y' Wj' := by
        rcases v03 j with rfl | rfl | rfl
        ·
          obtain ⟨s, hs, hWX_eq⟩ := v139 p F
          set C2 := cycMat L * cycMat L
          set C1 := cycMat L
          have hC12 : C2 * C1 = 1 := v68
          have hC21 : C1 * C2 = 1 := by rw [← Mx.mul_assoc]; exact v68
          have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
          have hWj_eq : Wj = Mv.C s⁻¹ * sMat C1 (fWron p (derivZ (sMat C2 F)) cMon) := by
            dsimp only [Wj]
            rw [hWX_eq, map_mul, hsubC, v47, hC12, v130, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs_ne, map_one, one_mul]
          rw [show Wj' = sMat T Wj from rfl, hWj_eq, map_mul, hsubC, v47, map_mul]
          apply dvd_mul_of_dvd_right
          have hCT1 : (C1 * T) * (Tinv * C2) = 1 := by
            rw [Mx.mul_assoc, ← Mx.mul_assoc T, hT1, Mx.one_mul, hC21]
          have hCT2 : (Tinv * C2) * (C1 * T) = 1 := by
            rw [Mx.mul_assoc, ← Mx.mul_assoc C2, hC12, Mx.one_mul, hT2]
          set P' : Fin 3 → ZMod p := (cycMat (ZMod p)).mulVec P
          have hP'2 : P' 2 ≠ 0 := by
            simpa [P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three] using hPj
          have hF20 : evBr (xP P) Y' (sMat (C1 * T) (sMat C2 F)) = 0 := by
            rw [v47, ← Mx.mul_assoc, hC12, Mx.one_mul]; exact hF'0
          have hCTpt : (C1 * T).mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P') := by
            rw [← Mx.mulVec_mulVec, hTP, Mx.mulVec_smul]; congr 1
            ext r; fin_cases r <;> simp [C1, P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
          exact v110 hp (by omega) (v25 C2 hF) (by omega)
            (C1 * T) (Tinv * C2) hCT1 hCT2 hY'0 hF20 P' hP'2 _ hc_ne hCTpt
        ·
          obtain ⟨s, hs, hWY_eq⟩ := v113 p F
          set C1 := cycMat L
          set C2 := cycMat L * cycMat L
          have hC12 : C1 * C2 = 1 := by rw [← Mx.mul_assoc]; exact v68
          have hC21 : C2 * C1 = 1 := v68
          have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
          have hWj_eq : Wj = Mv.C s⁻¹ * sMat C2 (fWron p (derivZ (sMat C1 F)) cMon) := by
            dsimp only [Wj]
            rw [hWY_eq, map_mul, hsubC, v47, hC12, v130, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs_ne, map_one, one_mul]
          rw [show Wj' = sMat T Wj from rfl, hWj_eq, map_mul, hsubC, v47, map_mul]
          apply dvd_mul_of_dvd_right
          have hCT1 : (C2 * T) * (Tinv * C1) = 1 := by
            rw [Mx.mul_assoc, ← Mx.mul_assoc T, hT1, Mx.one_mul, hC21]
          have hCT2 : (Tinv * C1) * (C2 * T) = 1 := by
            rw [Mx.mul_assoc, ← Mx.mul_assoc C1, hC12, Mx.one_mul, hT2]
          set P' : Fin 3 → ZMod p := (cycMat (ZMod p) * cycMat (ZMod p)).mulVec P
          have hP'2 : P' 2 ≠ 0 := by
            simpa [P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three, Mx.mul_apply] using hPj
          have hF10 : evBr (xP P) Y' (sMat (C2 * T) (sMat C1 F)) = 0 := by
            rw [v47, ← Mx.mul_assoc, hC12, Mx.one_mul]; exact hF'0
          have hCTpt : (C2 * T).mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P') := by
            rw [← Mx.mulVec_mulVec, hTP, Mx.mulVec_smul]; congr 1
            ext r; fin_cases r <;>
              simp [C2, P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
          exact v110 hp (by omega) (v25 C1 hF) (by omega)
            (C2 * T) (Tinv * C1) hCT1 hCT2 hY'0 hF10 P' hP'2 _ hc_ne hCTpt
        ·
          exact v110 hp (by omega) hF (by omega) T Tinv hT1 hT2 hY'0 hF'0 P hPj _ hc_ne hTP
      have ht5_Wt : Ps.X ^ 5 ∣ evBr (xP P) Y' Wt' := by
        rcases hcompat_j' with ⟨Q, hQ⟩
        have hev := congr_arg (evBr (xP P) Y') hQ
        rw [map_sub, map_mul, map_mul, hF'0, zero_mul, sub_eq_zero] at hev
        have hLj_const : Ps.constantCoeff (evBr (xP P) Y' Lj') = (dot3 n (ι ∘ P))⁻¹ * ι (P j) := by
          have h1 : Ps.constantCoeff (evBr (xP P) Y' Lj') = Mv.eval ![xP P, yP P, 1] Lj' := by
            rw [v62, ← v136]
            have hc : Ps.constantCoeff.comp (v16 (xP P)) = Pl.evalRingHom (xP P) := by
              ext <;> simp [v16]
            have hcomp : ∀ (g : Pol (Pol L)) (ps : PS L), Ps.constantCoeff ((g.map (v16 (xP P))).eval ps) = (g.map (Pl.evalRingHom (xP P))).eval (Ps.constantCoeff ps) := by
              intro g ps
              induction g using Pl.induction_on' with
              | add g₁ g₂ h₁ h₂ => simp [Pl.map_add, Pl.eval_add, h₁, h₂]
              | monomial m a =>
                simp only [Pl.map_monomial, Pl.eval_monomial, map_mul, map_pow]
                congr 1; exact congr_fun (congr_arg DFunLike.coe hc) a
            rw [hcomp, hY'0]
          rw [h1, v50, hTP]; simp
        have hιPj : ι (P j) ≠ 0 := fun h0 => hPj (ι.injective (h0.trans (map_zero ι).symm))
        have hLj_unit : IsUnit (evBr (xP P) Y' (Lj' ^ 10)) := by
          rw [Ps.isUnit_iff_constantCoeff, map_pow, map_pow, hLj_const]
          exact isUnit_iff_ne_zero.mpr (pow_ne_zero 10 (mul_ne_zero hc_ne hιPj))
        rw [hev] at ht5_Wj
        exact (hLj_unit.dvd_mul_left).mp ht5_Wj
      rw [v62] at ht5_Wt
      exact v61 hf'_mon (xP P) Y' 5 hY'root ht5_Wt
    ·
      push Not at hsm
      have hgrad0 : ∀ i : Fin 3, Mv.eval (ι ∘ P) (Mv.pderiv i F) = 0 :=
        fun i => congr_fun hsm i
      have hvan : (∀ i k : ℕ, i + k < 2 → ((shXY (xP P) (yP P) f').coeff k).coeff i = 0) ∧ (∀ i k : ℕ, i + k < 5 → ((shXY (xP P) (yP P) (dhZ Wj')).coeff k).coeff i = 0) := by
        have hcase2 : ∀ (Fc : Mv3 L) (Tc : Mat3 L)
            (Pc : Fin 3 → ZMod p) (hFc_hom : Fc.IsHomogeneous d)
            (hPc2 : Pc 2 ≠ 0) (hTcpt : Tc.mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ Pc))
            (hFc0 : Mv.eval (ι ∘ Pc) Fc = 0)
            (hFc_g0 : Mv.eval (ι ∘ Pc) (Mv.pderiv 0 Fc) = 0)
            (hFc_g1 : Mv.eval (ι ∘ Pc) (Mv.pderiv 1 Fc) = 0),
            (∀ i k : ℕ, i + k < 2 → ((shXY (xP P) (yP P) (dhZ (sMat Tc Fc))).coeff k).coeff i = 0) ∧
            (∀ i k : ℕ, i + k < 5 → ((shXY (xP P) (yP P) (dhZ (sMat Tc (fWron p (derivZ Fc) cMon)))).coeff k).coeff i = 0) := by
          intro Fc Tc Pc hFc_hom hPc2 hTcpt hFc0 hFc_g0 hFc_g1
          set a := ι (Pc 0 * (Pc 2)⁻¹)
          set b := ι (Pc 1 * (Pc 2)⁻¹)
          have : Fact p.Prime := ⟨hp⟩
          have ha : a ^ p = a := by dsimp only [a]; rw [← map_pow, ZMod.pow_card]
          have hb : b ^ p = b := by dsimp only [b]; rw [← map_pow, ZMod.pow_card]
          have hιPc2 : ι (Pc 2) ≠ 0 := fun h0 => hPc2 (ι.injective (h0.trans (map_zero ι).symm))
          have hPc_eq : ι ∘ Pc = ι (Pc 2) • ![a, b, 1] := by
            ext r; rcases v03 r with rfl | rfl | rfl
            · simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul, Mx.cons_val_zero, a, map_mul, map_inv₀]
              field_simp [hιPc2]
            · simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul, Mx.cons_val_one, Mx.cons_val_zero, b, map_mul, map_inv₀]
              field_simp [hιPc2]
            · simp
          have hab_F0 : Mv.eval ![a, b, 1] Fc = 0 := by
            rw [hPc_eq, v05 hFc_hom] at hFc0
            exact (mul_eq_zero.mp hFc0).resolve_left (pow_ne_zero d hιPc2)
          have hab_Fx : Mv.eval ![a, b, 1] (Mv.pderiv 0 Fc) = 0 := by
            rw [hPc_eq, v05 (v12 hFc_hom 0)] at hFc_g0
            exact (mul_eq_zero.mp hFc_g0).resolve_left (pow_ne_zero _ hιPc2)
          have hab_Fy : Mv.eval ![a, b, 1] (Mv.pderiv 1 Fc) = 0 := by
            rw [hPc_eq, v05 (v12 hFc_hom 1)] at hFc_g1
            exact (mul_eq_zero.mp hFc_g1).resolve_left (pow_ne_zero _ hιPc2)
          have hTc_ab : Tc.mulVec ![xP P, yP P, 1] = ((dot3 n (ι ∘ P))⁻¹ * ι (Pc 2)) • ![a, b, 1] := by
            rw [hTcpt, hPc_eq, smul_smul]
          have hc2_ne : (dot3 n (ι ∘ P))⁻¹ * ι (Pc 2) ≠ 0 := mul_ne_zero hc_ne hιPc2
          have hFc_ord2 : v39 2 (evalZ1 (sMat (shZM a b) Fc)) := by
            have hev_z1 : ∀ R : Mv3 L, Mv.eval 0 (evalZ1 R) = Mv.eval ![0, 0, 1] R := by
              intro R
              induction R using Mv.induction_on with
              | C c => simp [evalZ1]
              | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
              | mul_X p i hp =>
                rw [map_mul, map_mul, map_mul, hp]; congr 1
                rcases v03 i with rfl | rfl | rfl <;> simp [evalZ1]
            have hev0 : ∀ Q : Mv3 L, Mv.eval 0 (evalZ1 (sMat (shZM a b) Q)) = Mv.eval ![a, b, 1] Q := by
              intro Q
              rw [hev_z1, v50]
              apply congr_arg (fun v => Mv.eval v Q)
              ext i; rcases v03 i with rfl | rfl | rfl <;>
                simp [shZM, Mx.mulVec, dotProduct, Fi.sum_univ_three]
            have hp0 : Mv.pderiv 0 (evalZ1 (sMat (shZM a b) Fc)) = evalZ1 (sMat (shZM a b) (Mv.pderiv 0 Fc)) := by
              rw [← (v63 _).1, v67, Fi.sum_univ_three]; simp [shZM]
            have hp1 : Mv.pderiv 1 (evalZ1 (sMat (shZM a b) Fc)) = evalZ1 (sMat (shZM a b) (Mv.pderiv 1 Fc)) := by
              rw [← (v63 _).2, v67, Fi.sum_univ_three]; simp [shZM]
            exact v119 (by rw [hev0, hab_F0]) (by rw [hp0, hev0, hab_Fx])
              (by rw [hp1, hev0, hab_Fy])
          have hW_ord5 := v145 hp ha hb hab_F0 hab_Fx hab_Fy
          have hW_hom : (fWron p (derivZ Fc) cMon).IsHomogeneous (2 * p + 10 * d - 10) :=
            v32 p hFc_hom (by omega) (derivZ Fc)
              (fun hP hk => v65 hFc_hom hP (by omega) hk)
          exact ⟨v79 hFc_hom hFc_ord2 Tc (xP P) (yP P) _ hc2_ne hTc_ab, v79 hW_hom hW_ord5 Tc (xP P) (yP P) _ hc2_ne hTc_ab⟩
        have hsubC : ∀ (M : Mat3 L) (a : L), sMat M (Mv.C a) = Mv.C a := fun M a => by simp [sMat]
        have hscale_f' : ∀ i k : ℕ, ((shXY (xP P) (yP P) (dhZ F')).coeff k).coeff i = 0 → ((shXY (xP P) (yP P) f').coeff k).coeff i = 0 := by
          intro i k h0
          have hshC : shXY (xP P) (yP P) f' = Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')⁻¹) * shXY (xP P) (yP P) (dhZ F') := by
            simp only [f', mdhZ, map_mul, shXY, Rh.comp_apply, Pl.coe_mapRingHom, Pl.coe_compRingHom, Pl.map_C, Pl.C_comp]
          rw [hshC, Pl.coeff_C_mul, Pl.coeff_C_mul, h0, mul_zero]
        rcases v03 j with rfl | rfl | rfl
        ·
          obtain ⟨s, hs, hWX_eq⟩ := v139 p F
          set C2 := cycMat L * cycMat L
          set C1 := cycMat L
          have hC12 : C2 * C1 = 1 := v68
          have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
          set P' : Fin 3 → ZMod p := (cycMat (ZMod p)).mulVec P
          have hP'2 : P' 2 ≠ 0 := by
            simpa [P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three] using hPj
          have hC2_P' : C2.mulVec (ι ∘ P') = ι ∘ P := by
            ext r; fin_cases r <;>
              simp [C2, P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
          have hCTpt : (C1 * T).mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P') := by
            rw [← Mx.mulVec_mulVec, hTP, Mx.mulVec_smul]; congr 1
            ext r; fin_cases r <;> simp [C1, P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
          have hFc0 : Mv.eval (ι ∘ P') (sMat C2 F) = 0 := by
            rw [v50, hC2_P', hFP]
          have hFc_g : ∀ k : Fin 3, Mv.eval (ι ∘ P') (Mv.pderiv k (sMat C2 F)) = 0 := by
            intro k; rw [v67, map_sum, Fi.sum_univ_three]
            simp [v50, hC2_P', hgrad0]
          have ⟨h1, h2⟩ := hcase2 (sMat C2 F) (C1 * T) P' (v25 C2 hF)
            hP'2 hCTpt hFc0 (hFc_g 0) (hFc_g 1)
          refine ⟨fun i k hik => hscale_f' i k (by
              have : sMat (C1 * T) (sMat C2 F) = F' := by
                rw [v47, ← Mx.mul_assoc, hC12, Mx.one_mul]
              rw [← this]; exact h1 i k hik), fun i k hik => ?_⟩
          have hWj'_eq : Wj' = Mv.C s⁻¹ * sMat (C1 * T) (fWron p (derivZ (sMat C2 F)) cMon) := by
            dsimp only [Wj', Wj]
            rw [← v47, hWX_eq, map_mul, hsubC, v47, hC12, v130, map_mul, hsubC, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs_ne, map_one, one_mul]
          rw [hWj'_eq, v126, dhZ_C]
          have hshC : shXY (xP P) (yP P) (Pl.C (Pl.C s⁻¹) * dhZ (sMat (C1 * T) (fWron p (derivZ (sMat C2 F)) cMon))) = Pl.C (Pl.C s⁻¹) * shXY (xP P) (yP P) (dhZ (sMat (C1 * T) (fWron p (derivZ (sMat C2 F)) cMon))) := by
            simp only [map_mul, shXY, Rh.comp_apply, Pl.coe_mapRingHom, Pl.coe_compRingHom, Pl.map_C, Pl.C_comp]
          rw [hshC, Pl.coeff_C_mul, Pl.coeff_C_mul, h2 i k hik, mul_zero]
        ·
          obtain ⟨s, hs, hWY_eq⟩ := v113 p F
          set C1 := cycMat L
          set C2 := cycMat L * cycMat L
          have hC12 : C1 * C2 = 1 := by rw [← Mx.mul_assoc]; exact v68
          have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
          set P' : Fin 3 → ZMod p := (cycMat (ZMod p) * cycMat (ZMod p)).mulVec P
          have hP'2 : P' 2 ≠ 0 := by
            simpa [P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three, Mx.mul_apply] using hPj
          have hC1_P' : C1.mulVec (ι ∘ P') = ι ∘ P := by
            ext r; fin_cases r <;>
              simp [C1, P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
          have hCTpt : (C2 * T).mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P') := by
            rw [← Mx.mulVec_mulVec, hTP, Mx.mulVec_smul]; congr 1
            ext r; fin_cases r <;>
              simp [C2, P', cycMat, Mx.mulVec, dotProduct, Fi.sum_univ_three]
          have hFc0 : Mv.eval (ι ∘ P') (sMat C1 F) = 0 := by
            rw [v50, hC1_P', hFP]
          have hFc_g : ∀ k : Fin 3, Mv.eval (ι ∘ P') (Mv.pderiv k (sMat C1 F)) = 0 := by
            intro k; rw [v67, map_sum, Fi.sum_univ_three]
            simp [v50, hC1_P', hgrad0]
          have ⟨h1, h2⟩ := hcase2 (sMat C1 F) (C2 * T) P' (v25 C1 hF)
            hP'2 hCTpt hFc0 (hFc_g 0) (hFc_g 1)
          refine ⟨fun i k hik => hscale_f' i k (by
              have : sMat (C2 * T) (sMat C1 F) = F' := by
                rw [v47, ← Mx.mul_assoc, hC12, Mx.one_mul]
              rw [← this]; exact h1 i k hik), fun i k hik => ?_⟩
          have hWj'_eq : Wj' = Mv.C s⁻¹ * sMat (C2 * T) (fWron p (derivZ (sMat C1 F)) cMon) := by
            dsimp only [Wj', Wj]
            rw [← v47, hWY_eq, map_mul, hsubC, v47, hC12, v130, map_mul, hsubC, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs_ne, map_one, one_mul]
          rw [hWj'_eq, v126, dhZ_C]
          have hshC : shXY (xP P) (yP P) (Pl.C (Pl.C s⁻¹) * dhZ (sMat (C2 * T) (fWron p (derivZ (sMat C1 F)) cMon))) = Pl.C (Pl.C s⁻¹) * shXY (xP P) (yP P) (dhZ (sMat (C2 * T) (fWron p (derivZ (sMat C1 F)) cMon))) := by
            simp only [map_mul, shXY, Rh.comp_apply, Pl.coe_mapRingHom, Pl.coe_compRingHom, Pl.map_C, Pl.C_comp]
          rw [hshC, Pl.coeff_C_mul, Pl.coeff_C_mul, h2 i k hik, mul_zero]
        ·
          have ⟨h1, h2⟩ := hcase2 F T P hF hPj hTP hFP (hgrad0 0) (hgrad0 1)
          exact ⟨fun i k hik => hscale_f' i k (h1 i k hik), h2⟩
      have hdvd_Wj : (Pl.X - Pl.C (xP P)) ^ 5 ∣ pNorm f' (dhZ Wj') := by
        set eW := max 5 (shXY (xP P) (yP P) (dhZ Wj')).natDegree
        have h10 : Pl.X ^ (2 * 5) ∣ pNorm (shXY (xP P) (yP P) f')
            (shXY (xP P) (yP P) (dhZ Wj')) := by
          apply v169 (shXY_monic (xP P) (yP P) hf'_mon) 2 5 eW
          · rw [v207 _ _ hf'_mon, hf'_deg]; omega
          · exact le_max_left _ _
          · intro k hk
            exact Pl.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_right _ _) hk)
          · intro k
            rw [Pl.X_pow_dvd_iff]
            intro i hi; exact hvan.1 i k (by omega)
          · intro k
            rw [Pl.X_pow_dvd_iff]
            intro i hi; exact hvan.2 i k (by omega)
        have hsh_eq : (pNorm f' (dhZ Wj')).comp (Pl.X + Pl.C (xP P)) = pNorm (shXY (xP P) (yP P) f') (shXY (xP P) (yP P) (dhZ Wj')) :=
          v211 hf'_mon (xP P) (yP P)
        rw [← hsh_eq] at h10
        rcases h10 with ⟨q, hq⟩
        have hcomp := congr_arg (fun r : Pol L => r.comp (Pl.X - Pl.C (xP P))) hq
        simp only [Pl.mul_comp, Pl.pow_comp, Pl.X_comp, Pl.comp_assoc, Pl.add_comp, Pl.C_comp, sub_add_cancel, Pl.comp_X] at hcomp
        exact (pow_dvd_pow _ (by omega : 5 ≤ 2 * 5)).trans ⟨_, hcomp⟩
      have hnorm_eq : pNorm f' (dhZ Wj') = pNorm f' (dhZ Lj') ^ 10 * Npoly := by
        have hcongr : f' ∣ dhZ Wj' - dhZ (Lj' ^ 10 * Wt') := by
          rcases hcompat_j' with ⟨Q, hQ⟩
          refine ⟨Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')) * dhZ Q, ?_⟩
          rw [← dhZ_sub, hQ, v126]
          simp only [f', mdhZ]
          have hcc : (Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')⁻¹) : Pol (Pol L)) * Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')) = 1 := by
            rw [← map_mul, ← map_mul, inv_mul_cancel₀ hF'_010, map_one, map_one]
          calc dhZ F' * dhZ Q = 1 * (dhZ F' * dhZ Q) := (one_mul _).symm
            _ = _ := by rw [← hcc]; ring
        rw [pNorm_congr hf'_mon hcongr, v126, dhZ_pow, pNorm_mul hf'_mon]
        have hpow_norm : ∀ (n : ℕ) (g : Pol (Pol L)), pNorm f' (g ^ n) = pNorm f' g ^ n := by
          intro n g
          induction n with
          | zero => rw [pow_zero, pow_zero, pNorm_one hf'_mon]
          | succ n ih => rw [pow_succ, pow_succ, pNorm_mul hf'_mon, ih]
        rw [hpow_norm]
      have hLj_eval_ne : (pNorm f' (dhZ Lj')).eval (xP P) ≠ 0 := by
        rw [← Pl.coe_evalRingHom, v155 (Pl.evalRingHom (xP P)) hf'_mon]
        set fx : Pol L := f'.map (Pl.evalRingHom (xP P))
        set lx : Pol L := (dhZ Lj').map (Pl.evalRingHom (xP P))
        have hfx_mon : fx.Monic := hf'_mon.map _
        have hsplit : fx.Splits := IsAlgClosed.splits fx
        have hfx_eq : fx = (fx.roots.map (fun r => Pl.X - Pl.C r)).prod := by
          have h := hsplit.eq_prod_roots
          rwa [hfx_mon.leadingCoeff, map_one, one_mul] at h
        have hprod_ne : ∀ (M : Multiset L), (∀ r ∈ M, lx.eval r ≠ 0) → pNorm (M.map (fun r => Pl.X - Pl.C r)).prod lx ≠ 0 := by
          intro M
          induction M using Mu.induction_on with
          | empty =>
            intro _
            rw [Mu.map_zero, Mu.prod_zero]
            unfold pNorm
            have : IsEmpty (Fin (1 : Pol L).natDegree) := by
              rw [Pl.natDegree_one]; infer_instance
            rw [Mx.det_isEmpty]
            exact one_ne_zero
          | cons r M ih =>
            intro hM
            rw [Mu.map_cons, Mu.prod_cons]
            have hlin : (Pl.X - Pl.C r).Monic := Pl.monic_X_sub_C r
            have hMmon : (M.map (fun a => Pl.X - Pl.C a)).prod.Monic :=
              Pl.monic_multiset_prod_of_monic _ _ (fun a _ => Pl.monic_X_sub_C a)
            rw [v97 hlin hMmon, v132]
            exact mul_ne_zero (hM r (Mu.mem_cons_self r M))
              (ih (fun a ha => hM a (Mu.mem_cons_of_mem ha)))
        rw [hfx_eq]
        apply hprod_ne
        intro r hr hlr0
        have hfxr : fx.eval r = 0 := (Pl.mem_roots hfx_mon.ne_zero).mp hr
        have hF'r : Mv.eval ![xP P, r, 1] F' = 0 := by
          have : fx.eval r = (Mv.eval ![0, 1, 0] F')⁻¹ * Mv.eval ![xP P, r, 1] F' := by
            simp only [fx, f', mdhZ, Pl.map_mul, Pl.eval_mul, Pl.map_C, Pl.eval_C, Pl.coe_evalRingHom, v136]
          rw [this] at hfxr
          exact (mul_eq_zero.mp hfxr).resolve_left (inv_ne_zero hF'_010)
        have hLjr : Mv.eval ![xP P, r, 1] Lj' = 0 := by
          rwa [v136] at hlr0
        set v : Fin 3 → L := T.mulVec ![xP P, r, 1]
        have hv_ne : v ≠ 0 := fun h0 => (one_ne_zero : (1 : L) ≠ 0) (by
          have := congr_fun (congr_arg Tinv.mulVec h0) 2
          rw [Mx.mulVec_mulVec, hT2, Mx.one_mulVec, Mx.mulVec_zero] at this
          simp at this)
        have hvj : v j = 0 := by
          have : Mv.eval ![xP P, r, 1] Lj' = v j := by
            dsimp only [Lj', v]; rw [v50, Mv.eval_X]
          rw [← this, hLjr]
        have hFv : Mv.eval v F = 0 := by rwa [v50] at hF'r
        have hcov : ∃ r₀ ∈ Rset j, ∃ c₀ : L, v = c₀ • r₀ := by
          rcases v03 j with rfl | rfl | rfl
          · exact hR0_cov v hv_ne hvj hFv
          · exact hR1_cov v hv_ne hvj hFv
          · exact hR2_cov v hv_ne hvj hFv
        rcases hcov with ⟨r₀, hr₀, c₀, hv_eq⟩
        have hc₀_ne : c₀ ≠ 0 := fun h0 => hv_ne (by rw [hv_eq, h0, zero_smul])
        have hdiff : v - (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P) = (r - yP P) • q_inf := by
          rw [← hTP, show v = T.mulVec ![xP P, r, 1] from rfl, ← Mx.mulVec_sub]
          have : ![xP P, r, 1] - ![xP P, yP P, 1] = (r - yP P) • ![0, 1, 0] := by
            ext i; fin_cases i <;> simp
          rw [this, Mx.mulVec_smul, hT_010]
        have hry_ne : r - yP P ≠ 0 := by
          intro h0
          rw [h0, zero_smul, sub_eq_zero] at hdiff
          have h1 := congr_fun hdiff j
          rw [hvj] at h1
          simp only [Pi.smul_apply, smul_eq_mul, Fn.comp_apply] at h1
          have hιPj : ι (P j) ≠ 0 := fun h0' => hPj (ι.injective (h0'.trans (map_zero ι).symm))
          exact mul_ne_zero hc_ne hιPj h1.symm
        have hdot0 : dot3 (cross3 (ι ∘ P) r₀) q_inf = 0 := by
          have h := congr_arg (dot3 (cross3 (ι ∘ P) r₀)) hdiff
          rw [v02, sub_eq_add_neg, v13, hv_eq, v02, v28, mul_zero, zero_add] at h
          have hneg : dot3 (cross3 (ι ∘ P) r₀) (-((dot3 n (ι ∘ P))⁻¹ • (ι ∘ P))) = 0 := by
            have : -((dot3 n (ι ∘ P))⁻¹ • (ι ∘ P)) = (-(dot3 n (ι ∘ P))⁻¹) • (ι ∘ P) := by ext i; simp
            rw [this, v02, v56, mul_zero]
          rw [hneg] at h
          exact (mul_eq_zero.mp h.symm).resolve_left hry_ne
        exact hq_bad _ (mem_union_right _ (mem_union_right _
          (mem_biUnion.mpr ⟨j, mem_univ j, mem_biUnion.mpr ⟨P, mem_filter.mpr ⟨hPS, hPj⟩, mem_image.mpr ⟨r₀, hr₀, rfl⟩⟩⟩))) hdot0
      rw [hnorm_eq] at hdvd_Wj
      have hlin_prime : Prime (Pl.X - Pl.C (xP P)) :=
        (Pl.irreducible_X_sub_C (xP P)).prime
      have hndvd_L : ¬ (Pl.X - Pl.C (xP P)) ∣ pNorm f' (dhZ Lj') ^ 10 := by
        intro hd
        have h1 := hlin_prime.dvd_of_dvd_pow hd
        exact hLj_eval_ne (Pl.dvd_iff_isRoot.mp h1)
      have hcancel : ∀ (k : ℕ) (B : Pol L), (Pl.X - Pl.C (xP P)) ^ k ∣ pNorm f' (dhZ Lj') ^ 10 * B → (Pl.X - Pl.C (xP P)) ^ k ∣ B := by
        intro k
        induction k with
        | zero => intro B _; simp
        | succ k ih =>
          intro B hd
          have h1 : Pl.X - Pl.C (xP P) ∣ pNorm f' (dhZ Lj') ^ 10 * B :=
            (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hd
          have hB1 : Pl.X - Pl.C (xP P) ∣ B :=
            (hlin_prime.dvd_or_dvd h1).resolve_left hndvd_L
          rcases hB1 with ⟨B', rfl⟩
          have hk : (Pl.X - Pl.C (xP P)) ^ k ∣ pNorm f' (dhZ Lj') ^ 10 * B' := by
            rcases hd with ⟨q, hq⟩
            refine ⟨q, ?_⟩
            apply mul_left_cancel₀ (Pl.monic_X_sub_C (xP P)).ne_zero
            calc (Pl.X - Pl.C (xP P)) * (pNorm f' (dhZ Lj') ^ 10 * B')
                = pNorm f' (dhZ Lj') ^ 10 * ((Pl.X - Pl.C (xP P)) * B') := by ring
              _ = (Pl.X - Pl.C (xP P)) ^ (k + 1) * q := hq
              _ = (Pl.X - Pl.C (xP P)) * ((Pl.X - Pl.C (xP P)) ^ k * q) := by
                rw [pow_succ']; ring
          rcases ih B' hk with ⟨q, hq⟩
          exact ⟨q, by rw [hq, pow_succ']; ring⟩
      exact hcancel 5 Npoly hdvd_Wj
  have hprod_dvd : ∏ P ∈ S, (Pl.X - Pl.C (xP P)) ^ 5 ∣ Npoly := by
    apply Fs.prod_dvd_of_coprime
    · intro P₁ hP₁ P₂ hP₂ hne
      have hxne : xP P₁ ≠ xP P₂ := fun h => hne (hxP_inj hP₁ hP₂ h)
      exact (Pl.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxne))).pow
    · exact hlocal
  rcases hprod_dvd with ⟨q, hq⟩
  have hq_ne : q ≠ 0 := fun h0 => hN_ne (by rw [hq, h0, mul_zero])
  have hprod_mon : (∏ P ∈ S, (Pl.X - Pl.C (xP P)) ^ 5).Monic :=
    Pl.monic_prod_of_monic _ _ (fun P _ => (Pl.monic_X_sub_C _).pow 5)
  have hprod_deg : (∏ P ∈ S, (Pl.X - Pl.C (xP P)) ^ 5).natDegree = 5 * S.card := by
    rw [Pl.natDegree_prod_of_monic _ _ (fun P _ => (Pl.monic_X_sub_C _).pow 5)]
    have : ∀ P ∈ S, ((Pl.X - Pl.C (xP P)) ^ 5).natDegree = 5 := by
      intro P _; rw [Pl.natDegree_pow, Pl.natDegree_X_sub_C, mul_one]
    rw [sum_congr rfl this, Fs.sum_const, smul_eq_mul, mul_comm]
  have hdeg_le : 5 * S.card ≤ Npoly.natDegree := by
    rw [hq, hprod_mon.natDegree_mul' hq_ne, hprod_deg]; omega
  exact hdeg_le.trans hN_deg
end CurvePointBound
section FactorizationAndDescent
theorem v176 {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (ι : ZMod p →+* L) {F G : Mv3 L} {d e : ℕ}
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hF_irr : Irreducible F) (hndvd : ¬ F ∣ G) :
    ((pPts p).filter (fun P =>
      Mv.eval (ι ∘ P) F = 0 ∧ Mv.eval (ι ∘ P) G = 0)).card ≤ d * e := by
  set S : Finset (Fin 3 → ZMod p) :=
    (pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0 ∧ Mv.eval (ι ∘ P) G = 0)
  by_cases hS_empty : S = ∅
  · rw [hS_empty, card_empty]; exact Nat.zero_le _
  let badSecants : Finset (Fin 3 → L) :=
    S.offDiag.image (fun ab => cross3 (ι ∘ ab.1) (ι ∘ ab.2))
  have hbad_ne : ∀ l ∈ badSecants, l ≠ 0 := by
    intro l hl
    rcases mem_image.mp hl with ⟨⟨P₁, P₂⟩, hmem, rfl⟩
    rcases mem_offDiag.mp hmem with ⟨h1S, h2S, hne⟩
    have hP1n := v30.mp (mem_filter.mp h1S).1
    have hP2n := v30.mp (mem_filter.mp h2S).1
    intro hcr0
    have hιP1 : ι ∘ P₁ ≠ 0 := fun h0 => v00 hP1n (funext fun i =>
      ι.injective ((congr_fun h0 i).trans (map_zero ι).symm))
    rcases (v01 hιP1).mp hcr0 with ⟨c, hc⟩
    have hex1 : ∃ k : Fin 3, P₁ k ≠ 0 := by
      by_contra ha; push Not at ha; exact v00 hP1n (funext ha)
    rcases hex1 with ⟨k, hk⟩
    have hc_eq : c = ι (P₂ k * (P₁ k)⁻¹) := by
      have h1 := congr_fun hc k
      simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
      have hιk : ι (P₁ k) ≠ 0 := fun h0 => hk (ι.injective (h0.trans (map_zero ι).symm))
      rw [map_mul, map_inv₀, h1]; field_simp [hιk]
    have hP21 : P₂ = (P₂ k * (P₁ k)⁻¹) • P₁ := by
      ext i; apply ι.injective
      have h1 := congr_fun hc i
      simp only [Fn.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
      rw [← map_mul, ← hc_eq]; exact h1
    exact hne (v04 hP2n hP1n hP21).symm
  let bigPoly : Mv3 L := F * ∏ l ∈ badSecants, v55 l
  have hbig_ne : bigPoly ≠ 0 := by
    apply mul_ne_zero hF_irr.ne_zero
    rw [prod_ne_zero_iff]
    intro l hl h0
    have hl_ne := hbad_ne l hl
    have hex : ∃ i : Fin 3, l i ≠ 0 := by by_contra ha; push Not at ha; exact hl_ne (funext ha)
    rcases hex with ⟨i, hi⟩
    have := congr_arg (Mv.eval (Pi.single i 1)) h0
    rw [v27, map_zero] at this
    apply hi
    rcases v03 i with rfl | rfl | rfl <;> simpa [dot3, Pi.single_apply] using this
  obtain ⟨q_inf, hq_big⟩ := v46 hbig_ne
  rw [map_mul, map_prod] at hq_big
  have hFq_ne : Mv.eval q_inf F ≠ 0 := left_ne_zero_of_mul hq_big
  have hd_pos : 1 ≤ d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    subst hd_eq
    have hFC : F = Mv.C (F.coeff 0) := by
      ext m; by_cases hm : m = 0
      · subst hm; simp
      · rw [Mv.coeff_C, if_neg (Ne.symm hm)]
        by_contra hne
        have := v10 hF hne
        apply hm; ext i; rcases v03 i with rfl | rfl | rfl <;> simp <;> omega
    apply hF_irr.not_isUnit
    rw [hFC]
    exact v156 (fun h0 => hF_irr.ne_zero (by rw [hFC, h0, map_zero]))
  have hq_ne : q_inf ≠ 0 := fun h0 => hFq_ne (by
    rw [h0, Mv.eval_zero]
    by_contra hc0; have := v10 hF hc0; simp at this; omega)
  have hq_bad : ∀ l ∈ badSecants, dot3 l q_inf ≠ 0 := by
    intro l hl h0
    apply right_ne_zero_of_mul hq_big
    apply prod_eq_zero hl
    rw [v27, h0]
  have hS_not_prop : ∀ v ∈ S.image (fun P => ι ∘ P), cross3 q_inf v ≠ 0 := by
    intro v hv hcr
    rcases mem_image.mp hv with ⟨P, hPS, rfl⟩
    rcases (v01 hq_ne).mp hcr with ⟨c, hc⟩
    have hFP : Mv.eval (ι ∘ P) F = 0 := (mem_filter.mp hPS).2.1
    rw [hc, v05 hF] at hFP
    have hc0 : c = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hFP).resolve_right hFq_ne)
    rw [hc0, zero_smul] at hc
    have hPn := v30.mp (mem_filter.mp hPS).1
    exact v00 hPn (funext fun i => ι.injective ((congr_fun hc i).trans (map_zero ι).symm))
  obtain ⟨n, hnq, hnS⟩ := v114 q_inf hq_ne (S.image (fun P => ι ∘ P)) hS_not_prop
  have hn_ne : n ≠ 0 := by
    obtain ⟨P, hPS⟩ := nonempty_iff_ne_empty.mpr hS_empty
    intro h0; exact hnS (ι ∘ P) (mem_image_of_mem _ hPS) (by rw [h0, v135])
  have hex_n : ∃ i : Fin 3, n i ≠ 0 := by by_contra ha; push Not at ha; exact hn_ne (funext ha)
  rcases hex_n with ⟨in0, hin0⟩
  let v₂ : Fin 3 → L := Pi.single in0 (n in0)⁻¹
  have hnv2 : dot3 n v₂ = 1 := by
    rcases v03 in0 with rfl | rfl | rfl <;>
      simp [v₂, dot3, mul_inv_cancel₀ hin0]
  have hv0_ex : ∃ v₀ : Fin 3 → L, dot3 n v₀ = 0 ∧ det3 v₀ q_inf v₂ ≠ 0 := by
    have htwo : ∃ w₁ w₂ : Fin 3 → L, dot3 n w₁ = 0 ∧ dot3 n w₂ = 0 ∧ cross3 w₁ w₂ ≠ 0 := by
      rcases v03 in0 with rfl | rfl | rfl
      · exact ⟨![-n 1, n 0, 0], ![-n 2, 0, n 0], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 0; simp [cross3] at this; exact hin0 this⟩
      · exact ⟨![n 1, -n 0, 0], ![0, -n 2, n 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 1; simp [cross3] at this; exact hin0 this⟩
      · exact ⟨![n 2, 0, -n 0], ![0, n 2, -n 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 2; simp [cross3] at this; exact hin0 this⟩
    rcases htwo with ⟨w₁, w₂, hw1, hw2, hcr12⟩
    have hdet_of_cr : ∀ w : Fin 3 → L, dot3 n w = 0 → cross3 w q_inf ≠ 0 → det3 w q_inf v₂ ≠ 0 := by
      intro w hw hcr hdet0
      rw [v14] at hdet0
      rcases v09 hcr hw hnq with ⟨c, hc⟩
      rw [hc, v06, hdet0, mul_zero] at hnv2
      exact one_ne_zero hnv2.symm
    by_cases h1 : cross3 w₁ q_inf ≠ 0
    · exact ⟨w₁, hw1, hdet_of_cr w₁ hw1 h1⟩
    · push Not at h1
      refine ⟨w₂, hw2, hdet_of_cr w₂ hw2 ?_⟩
      intro h2
      rcases (v01 hq_ne).mp (by rw [v69, neg_eq_zero]; exact h1) with ⟨c1, hc1⟩
      rcases (v01 hq_ne).mp (by rw [v69, neg_eq_zero]; exact h2) with ⟨c2, hc2⟩
      apply hcr12
      rw [hc1, hc2, v72, v42, v85, smul_zero, smul_zero]
  rcases hv0_ex with ⟨v₀, hnv0, hdet_T⟩
  let T : Mat3 L := Mx.of fun i j =>
    match j with | ⟨0, _⟩ => v₀ i | ⟨1, _⟩ => q_inf i | ⟨2, _⟩ => v₂ i
  have hT_det : T.det ≠ 0 := by
    have h1 : T.det = det3 v₀ q_inf v₂ := by
      rw [← Mx.det_transpose, v127]
      congr 1; refine Mx.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [T]
    rw [h1]; exact hdet_T
  let Tinv : Mat3 L := T⁻¹
  have hT1 : T * Tinv = 1 := Mx.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT_det)
  have hT2 : Tinv * T = 1 := Mx.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT_det)
  have hT_010 : T.mulVec ![0, 1, 0] = q_inf := by
    ext i; simp [T, Mx.mulVec, dotProduct, Fi.sum_univ_three]
  have hT_dot_n : ∀ w : Fin 3 → L, dot3 n (T.mulVec w) = w 2 := by
    intro w
    have hlin : T.mulVec w = w 0 • v₀ + w 1 • q_inf + w 2 • v₂ := by
      ext i; simp [T, Mx.mulVec, dotProduct, Fi.sum_univ_three]; ring
    rw [hlin, v13, v13, v02, v02, v02, hnv0, hnq, hnv2]; ring
  set F' := sMat T F
  set G' := sMat T G
  have hF'_hom : F'.IsHomogeneous d := v25 T hF
  have hG'_hom : G'.IsHomogeneous e := v25 T hG
  have hF'_irr : Irreducible F' := v88 hT1 hT2 hF_irr
  have hF'_010 : Mv.eval ![0, 1, 0] F' ≠ 0 := by rw [v50, hT_010]; exact hFq_ne
  have hF'_ndvd_G' : ¬ F' ∣ G' := by rwa [v131 hT1 hT2]
  set f' := mdhZ F'
  obtain ⟨hf'_mon, hf'_deg⟩ := v149 hF'_hom hF'_010
  have hf'_irr : Irreducible f' := v71 hF'_hom hF'_irr hF'_010
  have hf'_ndvd_G' : ¬ f' ∣ dhZ G' := by
    intro hdvd
    apply hF'_ndvd_G'
    have hdeF_dvd : dhZ F' ∣ dhZ G' := by
      rcases hdvd with ⟨q, hq⟩
      exact ⟨Pl.C (Pl.C (Mv.eval ![0, 1, 0] F')⁻¹) * q, by rw [hq]; simp only [f', mdhZ]; ring⟩
    rcases hdeF_dvd with ⟨q, hq⟩
    set m := bDeg q
    set Q := hmZ m q
    have hde_eq : dhZ (F' * Q) = dhZ G' := by
      rw [v126, v198 (le_refl m), hq]
    have hFQ_hom : (F' * Q).IsHomogeneous (d + m) := hF'_hom.mul (v58 (le_refl m))
    by_cases hle : d + m ≤ e
    · have heq := v22 hFQ_hom hG'_hom hle hde_eq
      exact ⟨Mv.X 2 ^ (e - (d + m)) * Q, by rw [← heq]; ring⟩
    · have heq := v22 hG'_hom hFQ_hom (by omega) hde_eq.symm
      have hF'_prime : Prime F' := Ufm.irreducible_iff_prime.mp hF'_irr
      have hX2_ndvd : ¬ F' ∣ Mv.X 2 := by
        rintro ⟨u, hu⟩
        rcases (v89 2).irreducible.isUnit_or_isUnit hu with hFu | huu
        · exact hF'_irr.not_isUnit hFu
        · rcases huu with ⟨v, hv⟩
          have hFeq : F' = Mv.X 2 * ((v⁻¹ : (Mv3 L)ˣ) : Mv3 L) := by
            rw [hu, ← hv, mul_assoc, Units.mul_inv, mul_one]
          have := congr_arg (Mv.eval ![0, 1, 0]) hFeq
          simp only [map_mul, Mv.eval_X, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, zero_mul] at this
          exact hF'_010 this
      exact (hF'_prime.dvd_or_dvd ⟨Q, heq⟩).resolve_left
        (fun hpow => hX2_ndvd (hF'_prime.dvd_of_dvd_pow hpow))
  set Npoly : Pol L := pNorm f' (dhZ G')
  have hN_ne : Npoly ≠ 0 := v83 hf'_mon hf'_irr hf'_ndvd_G'
  have hN_deg : Npoly.natDegree ≤ d * e := by
    have hf'_bd : ∀ k, f'.coeff k ≠ 0 → (f'.coeff k).natDegree + k ≤ f'.natDegree := by
      intro k hk; rw [hf'_deg]; exact (v133 hF'_hom k).resolve_right hk
    have hG_bd : ∀ k, (dhZ G').coeff k ≠ 0 → ((dhZ G').coeff k).natDegree + k ≤ e := by
      intro k hk; exact (v102 hG'_hom k).resolve_right hk
    simpa [Npoly, hf'_deg] using v74 hf'_mon e hf'_bd hG_bd
  let xP : (Fin 3 → ZMod p) → L := fun P => (dot3 n (ι ∘ P))⁻¹ * (Tinv.mulVec (ι ∘ P)) 0
  let yP : (Fin 3 → ZMod p) → L := fun P => (dot3 n (ι ∘ P))⁻¹ * (Tinv.mulVec (ι ∘ P)) 1
  have hT_P : ∀ P ∈ S, T.mulVec ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • (ι ∘ P) := by
    intro P hPS
    have hnP : dot3 n (ι ∘ P) ≠ 0 := hnS (ι ∘ P) (mem_image_of_mem _ hPS)
    have h2 : (Tinv.mulVec (ι ∘ P)) 2 = dot3 n (ι ∘ P) := by
      rw [← hT_dot_n (Tinv.mulVec (ι ∘ P)), Mx.mulVec_mulVec, hT1, Mx.one_mulVec]
    have hvec : ![xP P, yP P, 1] = (dot3 n (ι ∘ P))⁻¹ • Tinv.mulVec (ι ∘ P) := by
      ext i; fin_cases i
      · rfl
      · rfl
      · simp [h2, inv_mul_cancel₀ hnP]
    rw [hvec, Mx.mulVec_smul, Mx.mulVec_mulVec, hT1, Mx.one_mulVec]
  have hxP_inj : Set.InjOn xP ↑S := by
    intro P₁ hP₁ P₂ hP₂ heq
    by_contra hne
    have h1 := hT_P P₁ hP₁
    have h2 := hT_P P₂ hP₂
    have hn1 : dot3 n (ι ∘ P₁) ≠ 0 := hnS (ι ∘ P₁) (mem_image_of_mem _ hP₁)
    have hn2 : dot3 n (ι ∘ P₂) ≠ 0 := hnS (ι ∘ P₂) (mem_image_of_mem _ hP₂)
    have hdiff : T.mulVec ![0, yP P₁ - yP P₂, 0] = (dot3 n (ι ∘ P₁))⁻¹ • (ι ∘ P₁) - (dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂) := by
      rw [← h1, ← h2, ← Mx.mulVec_sub]
      congr 1; ext i; fin_cases i <;> simp [heq]
    have hTq : T.mulVec ![0, yP P₁ - yP P₂, 0] = (yP P₁ - yP P₂) • q_inf := by
      have : ![0, yP P₁ - yP P₂, 0] = (yP P₁ - yP P₂) • ![0, 1, 0] := by ext i; fin_cases i <;> simp
      rw [this, Mx.mulVec_smul, hT_010]
    have hy_ne : yP P₁ - yP P₂ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hTq
      rw [h0] at hdiff
      have hsc : (dot3 n (ι ∘ P₁))⁻¹ • (ι ∘ P₁) = (dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂) :=
        sub_eq_zero.mp (hdiff.symm.trans hTq)
      have hP12_cr : cross3 (ι ∘ P₁) (ι ∘ P₂) = 0 := by
        have hP2_eq : ι ∘ P₂ = (dot3 n (ι ∘ P₂) * (dot3 n (ι ∘ P₁))⁻¹) • (ι ∘ P₁) := by
          ext i; have hsc_i := congr_fun hsc i
          simp only [Pi.smul_apply, smul_eq_mul] at hsc_i ⊢
          calc (ι ∘ P₂) i = dot3 n (ι ∘ P₂) * ((dot3 n (ι ∘ P₂))⁻¹ * (ι ∘ P₂) i) := by
                rw [← mul_assoc, mul_inv_cancel₀ hn2, one_mul]
            _ = dot3 n (ι ∘ P₂) * ((dot3 n (ι ∘ P₁))⁻¹ * (ι ∘ P₁) i) := by rw [← hsc_i]
            _ = dot3 n (ι ∘ P₂) * (dot3 n (ι ∘ P₁))⁻¹ * (ι ∘ P₁) i := by ring
        rw [hP2_eq, v42, v85, smul_zero]
      exact hbad_ne _ (mem_image.mpr ⟨(P₁, P₂), mem_offDiag.mpr ⟨hP₁, hP₂, hne⟩, rfl⟩) hP12_cr
    have hdot0 : dot3 (cross3 (ι ∘ P₁) (ι ∘ P₂)) q_inf = 0 := by
      have h := congr_arg (dot3 (cross3 (ι ∘ P₁) (ι ∘ P₂))) (hTq.symm.trans hdiff)
      rw [v02] at h
      conv at h => rhs; rw [sub_eq_add_neg, v13, v02, v56, mul_zero, zero_add]
      have hneg : dot3 (cross3 (ι ∘ P₁) (ι ∘ P₂)) (-((dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂))) = 0 := by
        have : -((dot3 n (ι ∘ P₂))⁻¹ • (ι ∘ P₂)) = (-(dot3 n (ι ∘ P₂))⁻¹) • (ι ∘ P₂) := by ext i; simp
        rw [this, v02, v28, mul_zero]
      rw [hneg] at h
      exact (mul_eq_zero.mp h).resolve_left hy_ne
    exact hq_bad _ (mem_image.mpr ⟨(P₁, P₂), mem_offDiag.mpr ⟨hP₁, hP₂, hne⟩, rfl⟩) hdot0
  have hroots : S.image xP ⊆ Npoly.roots.toFinset := by
    intro x hx
    rcases mem_image.mp hx with ⟨P, hPS, rfl⟩
    rw [Mu.mem_toFinset, Pl.mem_roots hN_ne, Pl.IsRoot]
    rw [← Pl.coe_evalRingHom, v155 (Pl.evalRingHom (xP P)) hf'_mon]
    set fx : Pol L := f'.map (Pl.evalRingHom (xP P))
    set gx : Pol L := (dhZ G').map (Pl.evalRingHom (xP P))
    have hfx_root : fx.eval (yP P) = 0 := by
      have hF'P : Mv.eval ![xP P, yP P, 1] F' = 0 := by
        rw [v50, hT_P P hPS, v05 hF, (mem_filter.mp hPS).2.1, mul_zero]
      simp only [fx, f', mdhZ, Pl.map_mul, Pl.eval_mul, v136, hF'P, mul_zero]
    have hgx_root : gx.eval (yP P) = 0 := by
      rw [v136, v50, hT_P P hPS, v05 hG, (mem_filter.mp hPS).2.2, mul_zero]
    rcases Pl.dvd_iff_isRoot.mpr hfx_root with ⟨q, hq⟩
    have hfx_mon : fx.Monic := hf'_mon.map _
    have hlin_mon : (Pl.X - Pl.C (yP P)).Monic := Pl.monic_X_sub_C _
    have hq_mon : q.Monic := by
      have hlc : fx.leadingCoeff = (Pl.X - Pl.C (yP P)).leadingCoeff * q.leadingCoeff := by
        rw [hq, Pl.leadingCoeff_mul]
      rw [hfx_mon.leadingCoeff, hlin_mon.leadingCoeff, one_mul] at hlc
      exact hlc.symm
    rw [hq, v97 hlin_mon hq_mon, v132, hgx_root, zero_mul]
  calc S.card = (S.image xP).card := (card_image_of_injOn hxP_inj).symm
    _ ≤ Npoly.roots.toFinset.card := card_le_card hroots
    _ ≤ Npoly.roots.card := Mu.toFinset_card_le _
    _ ≤ Npoly.natDegree := Pl.card_roots' Npoly
    _ ≤ d * e := hN_deg
lemma v80 {K : Type*} [Field K] {H A B : Mv3 K} {e : ℕ}
    (hH : H.IsHomogeneous e) (hH_ne : H ≠ 0) (hAB : H = A * B) :
    ∃ a b : ℕ, a + b = e ∧ A.IsHomogeneous a ∧ B.IsHomogeneous b := by
  have hA_ne : A ≠ 0 := fun h0 => hH_ne (by rw [hAB, h0, zero_mul])
  have hB_ne : B ≠ 0 := fun h0 => hH_ne (by rw [hAB, h0, mul_zero])
  have hAs : A.support.Nonempty := Mv.support_nonempty.mpr hA_ne
  have hBs : B.support.Nonempty := Mv.support_nonempty.mpr hB_ne
  set amin := A.support.inf' hAs Fu.degree
  set amax := A.support.sup' hAs Fu.degree
  set bmin := B.support.inf' hBs Fu.degree
  set bmax := B.support.sup' hBs Fu.degree
  have hA_ge : ∀ m ∈ A.support, amin ≤ Fu.degree m := fun m hm => inf'_le _ hm
  have hA_le : ∀ m ∈ A.support, Fu.degree m ≤ amax := fun m hm => le_sup' _ hm
  have hB_ge : ∀ m ∈ B.support, bmin ≤ Fu.degree m := fun m hm => inf'_le _ hm
  have hB_le : ∀ m ∈ B.support, Fu.degree m ≤ bmax := fun m hm => le_sup' _ hm
  have hhc_ne : ∀ {P : Mv3 K} {r : ℕ}, (∃ m ∈ P.support, Fu.degree m = r) → Mv.homogeneousComponent r P ≠ 0 := by
    rintro P r ⟨m, hm, hdeg⟩ h0
    have := congr_arg (Mv.coeff m) h0
    rw [Mv.coeff_homogeneousComponent, if_pos hdeg, Mv.coeff_zero] at this
    exact Mv.mem_support_iff.mp hm this
  have hA_min_ne : Mv.homogeneousComponent amin A ≠ 0 :=
    hhc_ne (by obtain ⟨m, hm, h⟩ := exists_mem_eq_inf' hAs Fu.degree; exact ⟨m, hm, h.symm⟩)
  have hA_max_ne : Mv.homogeneousComponent amax A ≠ 0 :=
    hhc_ne (by obtain ⟨m, hm, h⟩ := exists_mem_eq_sup' hAs Fu.degree; exact ⟨m, hm, h.symm⟩)
  have hB_min_ne : Mv.homogeneousComponent bmin B ≠ 0 :=
    hhc_ne (by obtain ⟨m, hm, h⟩ := exists_mem_eq_inf' hBs Fu.degree; exact ⟨m, hm, h.symm⟩)
  have hB_max_ne : Mv.homogeneousComponent bmax B ≠ 0 :=
    hhc_ne (by obtain ⟨m, hm, h⟩ := exists_mem_eq_sup' hBs Fu.degree; exact ⟨m, hm, h.symm⟩)
  have hmin_eq : Mv.homogeneousComponent (amin + bmin) (A * B) = Mv.homogeneousComponent amin A * Mv.homogeneousComponent bmin B := by
    ext m
    rw [Mv.coeff_homogeneousComponent, Mv.coeff_mul, Mv.coeff_mul]
    by_cases hm : Fu.degree m = amin + bmin
    · rw [if_pos hm]
      apply sum_congr rfl; intro xy hxy
      have hxy' : xy.1 + xy.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
      by_cases h1 : A.coeff xy.1 = 0
      · simp [h1, Mv.coeff_homogeneousComponent]
      · by_cases h2 : B.coeff xy.2 = 0
        · simp [h2, Mv.coeff_homogeneousComponent]
        · have hge1 := hA_ge xy.1 (Mv.mem_support_iff.mpr h1)
          have hge2 := hB_ge xy.2 (Mv.mem_support_iff.mpr h2)
          have hsum : Fu.degree xy.1 + Fu.degree xy.2 = amin + bmin := by
            rw [← map_add, hxy', hm]
          rw [Mv.coeff_homogeneousComponent, Mv.coeff_homogeneousComponent, if_pos (by omega), if_pos (by omega)]
    · rw [if_neg hm]; symm
      have hhom := (Mv.homogeneousComponent_isHomogeneous amin A).mul
        (Mv.homogeneousComponent_isHomogeneous bmin B)
      by_contra hne
      rw [← Mv.coeff_mul] at hne
      have hdeg := v10 hhom hne
      apply hm
      rw [Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi), Fi.sum_univ_three]
      exact hdeg
  have hmax_eq : Mv.homogeneousComponent (amax + bmax) (A * B) = Mv.homogeneousComponent amax A * Mv.homogeneousComponent bmax B := by
    ext m
    rw [Mv.coeff_homogeneousComponent, Mv.coeff_mul, Mv.coeff_mul]
    by_cases hm : Fu.degree m = amax + bmax
    · rw [if_pos hm]
      apply sum_congr rfl; intro xy hxy
      have hxy' : xy.1 + xy.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
      by_cases h1 : A.coeff xy.1 = 0
      · simp [h1, Mv.coeff_homogeneousComponent]
      · by_cases h2 : B.coeff xy.2 = 0
        · simp [h2, Mv.coeff_homogeneousComponent]
        · have hle1 := hA_le xy.1 (Mv.mem_support_iff.mpr h1)
          have hle2 := hB_le xy.2 (Mv.mem_support_iff.mpr h2)
          have hsum : Fu.degree xy.1 + Fu.degree xy.2 = amax + bmax := by
            rw [← map_add, hxy', hm]
          rw [Mv.coeff_homogeneousComponent, Mv.coeff_homogeneousComponent, if_pos (by omega), if_pos (by omega)]
    · rw [if_neg hm]; symm
      have hhom := (Mv.homogeneousComponent_isHomogeneous amax A).mul
        (Mv.homogeneousComponent_isHomogeneous bmax B)
      by_contra hne
      rw [← Mv.coeff_mul] at hne
      have hdeg := v10 hhom hne
      apply hm
      rw [Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi), Fi.sum_univ_three]
      exact hdeg
  have hhc_H : ∀ r : ℕ, r ≠ e → Mv.homogeneousComponent r (A * B) = 0 := by
    intro r hr; rw [← hAB]; ext m
    rw [Mv.coeff_homogeneousComponent, Mv.coeff_zero]
    split_ifs with hdeg
    · by_contra hne
      have hd := v10 hH hne
      apply hr
      rw [← hdeg, Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi), Fi.sum_univ_three]
      exact hd
    · rfl
  have hmin_e : amin + bmin = e := by
    by_contra hne
    have h0 := hhc_H (amin + bmin) hne
    rw [hmin_eq] at h0
    exact mul_ne_zero hA_min_ne hB_min_ne h0
  have hmax_e : amax + bmax = e := by
    by_contra hne
    have h0 := hhc_H (amax + bmax) hne
    rw [hmax_eq] at h0
    exact mul_ne_zero hA_max_ne hB_max_ne h0
  have ha_le : amin ≤ amax := by
    obtain ⟨m, hm⟩ := hAs; exact (hA_ge m hm).trans (hA_le m hm)
  have hb_le : bmin ≤ bmax := by
    obtain ⟨m, hm⟩ := hBs; exact (hB_ge m hm).trans (hB_le m hm)
  have ha_eq : amin = amax := by omega
  have hb_eq : bmin = bmax := by omega
  refine ⟨amin, bmin, hmin_e, ?_, ?_⟩
  · intro m hm
    have h1 := hA_ge m (Mv.mem_support_iff.mpr hm)
    have h2 := hA_le m (Mv.mem_support_iff.mpr hm)
    rw [Fu.weight_apply, Fu.sum_fintype _ _ (fun _ => by simp)]
    have hdeg_m : Fu.degree m = amin := by omega
    rw [← hdeg_m, Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi)]
    simp [smul_eq_mul]
  · intro m hm
    have h1 := hB_ge m (Mv.mem_support_iff.mpr hm)
    have h2 := hB_le m (Mv.mem_support_iff.mpr hm)
    rw [Fu.weight_apply, Fu.sum_fintype _ _ (fun _ => by simp)]
    have hdeg_m : Fu.degree m = bmin := by omega
    rw [← hdeg_m, Fu.degree_apply, sum_subset (subset_univ _) (fun i _ hi => Fu.notMem_support_iff.mp hi)]
    simp [smul_eq_mul]
lemma v31 {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharP L p]
    {x : L} (hx : x ^ p = x) :
    ∃ z : ZMod p, (ZMod.castHom (dvd_refl p) L) z = x := by
  classical
  set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
  set P : Pol L := Pl.X ^ p - Pl.X
  have hP_ne : P ≠ 0 := by
    intro h0
    have := congr_arg (fun r : Pol L => r.coeff p) h0
    have h1p : (1 : ℕ) ≠ p := (Fact.out : p.Prime).ne_one.symm
    simp [P, Pl.coeff_X, h1p] at this
  have hP_deg : P.natDegree ≤ p := by
    refine (Pl.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    simpa [Pl.natDegree_X] using hp1
  have hsub : Fs.univ.image ι ⊆ P.roots.toFinset := by
    intro y hy
    rcases mem_image.mp hy with ⟨z, _, rfl⟩
    rw [Mu.mem_toFinset, Pl.mem_roots hP_ne, Pl.IsRoot]
    simp only [P, Pl.eval_sub, Pl.eval_pow, Pl.eval_X]
    rw [← map_pow, ZMod.pow_card, sub_self]
  have hcard1 : (Fs.univ.image ι).card = p := by
    rw [card_image_of_injective _ ι.injective, card_univ, ZMod.card p]
  have hcard2 : P.roots.toFinset.card ≤ p :=
    (Mu.toFinset_card_le _).trans ((Pl.card_roots' P).trans hP_deg)
  have heq : Fs.univ.image ι = P.roots.toFinset :=
    eq_of_subset_of_card_le hsub (by omega)
  have hx_mem : x ∈ P.roots.toFinset := by
    rw [Mu.mem_toFinset, Pl.mem_roots hP_ne]
    simp [P, hx]
  rw [← heq] at hx_mem
  rcases mem_image.mp hx_mem with ⟨z, _, hz⟩
  exact ⟨z, hz⟩
lemma v150 {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    [CharP L p] {F : Mv3 L} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF_irr : Irreducible F) :
    (∃ (c : L) (G : Mv3 (ZMod p)), c ≠ 0 ∧ G ≠ 0 ∧ G.IsHomogeneous d ∧ F = Mv.C c * Mv.map (ZMod.castHom (dvd_refl p) L) G) ∨
    ((pPts p).filter (fun P => Mv.eval ((ZMod.castHom (dvd_refl p) L) ∘ P) F = 0)).card ≤ d * d := by
  set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
  set Fp : Mv3 L := Mv.map (frobenius L p) F
  have hFp_hom : Fp.IsHomogeneous d := hF.map (frobenius L p)
  by_cases hdvd : F ∣ Fp
  · left
    rcases hdvd with ⟨U, hU⟩
    have hFp_ne : Fp ≠ 0 := by
      intro h0
      obtain ⟨m, hm⟩ := Mv.support_nonempty.mpr hF_irr.ne_zero
      have h1 := congr_arg (Mv.coeff m) h0
      rw [Mv.coeff_map, Mv.coeff_zero, frobenius_def] at h1
      exact Mv.mem_support_iff.mp hm (eq_zero_of_pow_eq_zero h1)
    obtain ⟨a, b, hab, hFa, hUb⟩ := v80 hFp_hom hFp_ne hU
    have ha_eq : a = d := by
      obtain ⟨m, hm⟩ := Mv.support_nonempty.mpr hF_irr.ne_zero
      have h1 := v10 hF (Mv.mem_support_iff.mp hm)
      have h2 := v10 hFa (Mv.mem_support_iff.mp hm)
      omega
    have hb_eq : b = 0 := by omega
    subst hb_eq
    have hU_C : U = Mv.C (U.coeff 0) := by
      ext m; by_cases hm : m = 0
      · subst hm; simp
      · rw [Mv.coeff_C, if_neg (Ne.symm hm)]
        by_contra hne; have := v10 hUb hne
        apply hm; ext i; rcases v03 i with rfl | rfl | rfl <;> simp <;> omega
    obtain ⟨m₀, hm₀⟩ := Mv.support_nonempty.mpr hF_irr.ne_zero
    set c := F.coeff m₀
    have hc_ne : c ≠ 0 := Mv.mem_support_iff.mp hm₀
    set F₀ := Mv.C c⁻¹ * F
    have hF₀_m0 : F₀.coeff m₀ = 1 := by
      dsimp only [F₀]; rw [Mv.coeff_C_mul]; exact inv_mul_cancel₀ hc_ne
    have hF₀_frob : Mv.map (frobenius L p) F₀ = F₀ := by
      set lam := (c⁻¹) ^ p * U.coeff 0 * c
      have hF₀p : Mv.map (frobenius L p) F₀ = Mv.C lam * F₀ := by
        dsimp only [F₀]
        rw [map_mul, Mv.map_C, frobenius_def, show Mv.map (frobenius L p) F = Fp from rfl, hU, hU_C]
        dsimp only [lam]
        rw [map_mul, map_mul]
        have hcc : (Mv.C c * Mv.C c⁻¹ : Mv3 L) = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hc_ne, map_one]
        calc Mv.C (c⁻¹ ^ p) * (F * Mv.C (U.coeff 0))
            = Mv.C (c⁻¹ ^ p) * Mv.C (U.coeff 0) * (1 * F) := by ring
          _ = Mv.C (c⁻¹ ^ p) * Mv.C (U.coeff 0) * (Mv.C c * Mv.C c⁻¹ * F) := by rw [hcc]
          _ = Mv.C (c⁻¹ ^ p) * Mv.C (U.coeff 0) * Mv.C c * (Mv.C c⁻¹ * F) := by ring
      have hlam1 : lam = 1 := by
        have h1 := congr_arg (Mv.coeff m₀) hF₀p
        rw [Mv.coeff_map, frobenius_def, hF₀_m0, one_pow, Mv.coeff_C_mul, hF₀_m0, mul_one] at h1
        exact h1.symm
      rw [hF₀p, hlam1, map_one, one_mul]
    have hcoeff_fix : ∀ m : E3, (F₀.coeff m) ^ p = F₀.coeff m := by
      intro m
      have := congr_arg (Mv.coeff m) hF₀_frob
      rwa [Mv.coeff_map, frobenius_def] at this
    classical
    let G : Mv3 (ZMod p) :=
      ∑ m ∈ F₀.support, Mv.monomial m (Classical.choose (v31 (hcoeff_fix m)))
    have hG_map : Mv.map ι G = F₀ := by
      ext m
      rw [Mv.coeff_map]
      by_cases hm : m ∈ F₀.support
      · dsimp only [G]
        rw [Mv.coeff_sum, sum_eq_single m]
        · rw [Mv.coeff_monomial, if_pos rfl]
          exact Classical.choose_spec (v31 (hcoeff_fix m))
        · intro n _ hnm; rw [Mv.coeff_monomial, if_neg hnm]
        · intro h; exact absurd hm h
      · dsimp only [G]
        rw [Mv.coeff_sum, sum_eq_zero, map_zero]
        · exact (Mv.notMem_support_iff.mp hm).symm
        · intro n hn; rw [Mv.coeff_monomial, if_neg (fun (h : n = m) => hm (h ▸ hn))]
    have hF_eq : F = Mv.C c * Mv.map ι G := by
      rw [hG_map]; dsimp only [F₀]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc_ne, map_one, one_mul]
    have hG_ne : G ≠ 0 := fun h0 => hF_irr.ne_zero (by rw [hF_eq, h0, map_zero, mul_zero])
    have hG_hom : G.IsHomogeneous d := by
      intro m hm
      have hF₀_hom : F₀.IsHomogeneous d := v07 c⁻¹ hF
      apply hF₀_hom
      rw [← hG_map, Mv.coeff_map]
      exact fun h0 => hm (ι.injective (h0.trans (map_zero ι).symm))
    exact ⟨c, G, hc_ne, hG_ne, hG_hom, hF_eq⟩
  · right
    have hsub : (pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0) ⊆
        (pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0 ∧ Mv.eval (ι ∘ P) Fp = 0) := by
      intro P hP
      rw [mem_filter] at hP ⊢
      refine ⟨hP.1, hP.2, ?_⟩
      have hev : ∀ Q : Mv3 L, Mv.eval (ι ∘ P) (Mv.map (frobenius L p) Q) = (Mv.eval (ι ∘ P) Q) ^ p := by
        intro Q
        induction Q using Mv.induction_on with
        | C a => simp [frobenius_def]
        | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, map_add, add_pow_char, h₁, h₂]
        | mul_X p₁ i h₁ =>
          rw [map_mul, Mv.map_X, map_mul, map_mul, mul_pow, h₁, Mv.eval_X]
          congr 1
          change ι (P i) = (ι (P i)) ^ p
          rw [← map_pow, ZMod.pow_card]
      rw [show Fp = Mv.map (frobenius L p) F from rfl, hev F, hP.2, zero_pow (Fact.out : p.Prime).ne_zero]
    exact (card_le_card hsub).trans (v176 ι hF hFp_hom hF_irr hdvd)
end FactorizationAndDescent
section VolochAssembly
lemma v98 {p : ℕ} [Fact p.Prime]
    {K : Finset (Fin 3 → ZMod p)} (hK : v153 K) (hK2 : 2 ≤ K.card)
    {φ G : Mv3 (ZMod p)}
    (henv : ∀ y ∈ K, (∀ l ∈ v23 K y, Mv.eval l φ = 0) ∧ (∀ {L : Type} [Field L] (ι : ZMod p →+* L) (z : Fin 3 → L), z ≠ 0 → dot3 z (ι ∘ y) = 0 → Mv.eval z (Mv.map ι φ) = 0 → ∃ l ∈ v23 K y, ∃ c : L, z = c • (ι ∘ l)))
    (hG_ne : G ≠ 0) (hG_hom : G.IsHomogeneous 1) (hdvd : G ∣ φ) :
    False := by
  let q : Fin 3 → ZMod p := fun i => G.coeff (Fu.single i 1)
  have hG_eq : G = v55 q := by
    have h01 : (Fu.single (0 : Fin 3) 1 : E3) ≠ Fu.single 1 1 := fun h => by
      have := congr_arg (fun f : E3 => f 0) h; simp at this
    have h02 : (Fu.single (0 : Fin 3) 1 : E3) ≠ Fu.single 2 1 := fun h => by
      have := congr_arg (fun f : E3 => f 0) h; simp at this
    have h12 : (Fu.single (1 : Fin 3) 1 : E3) ≠ Fu.single 2 1 := fun h => by
      have := congr_arg (fun f : E3 => f 1) h; simp at this
    ext m
    by_cases hm : m = Fu.single 0 1 ∨ m = Fu.single 1 1 ∨ m = Fu.single 2 1
    · rcases hm with rfl | rfl | rfl <;>
        simp [v55, q, Mv.coeff_X, Mv.coeff_C_mul, h01, h02, h12, h01.symm, h02.symm, h12.symm]
    · push Not at hm
      have h0 : G.coeff m = 0 := by
        by_contra hne
        have hdeg := v10 hG_hom hne
        have : m = Fu.single 0 1 ∨ m = Fu.single 1 1 ∨ m = Fu.single 2 1 := by
          by_cases h0 : m 0 = 1
          · left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [h0] <;> omega
          · by_cases h1 : m 1 = 1
            · right; left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [h1] <;> omega
            · right; right; ext i; rcases v03 i with rfl | rfl | rfl <;> simp <;> omega
        rcases this with h | h | h
        · exact hm.1 h
        · exact hm.2.1 h
        · exact hm.2.2 h
      rw [h0]
      simp [v55, Mv.coeff_X, Mv.coeff_C_mul, Ne.symm hm.1, Ne.symm hm.2.1, Ne.symm hm.2.2]
  have hq_ne : q ≠ 0 := by
    intro h0; apply hG_ne; rw [hG_eq, h0]; simp [v55]
  set q₀ := normPt q
  have hq₀_mem : q₀ ∈ pPts p := v90 hq_ne
  have hno_secant : ∀ y₁ ∈ K, ∀ y₂ ∈ K, y₁ ≠ y₂ → det3 q₀ y₁ y₂ ≠ 0 := by
    intro y₁ hy₁ y₂ hy₂ h12 hdet
    have hcr_ne : cross3 y₁ y₂ ≠ 0 := by
      intro h0
      rcases (v01 (v00 (hK.1.1 y₁ hy₁))).mp h0 with ⟨c, hc⟩
      exact h12 (v04 (hK.1.1 y₂ hy₂) (hK.1.1 y₁ hy₁) hc).symm
    have hq_dot : dot3 q (cross3 y₁ y₂) = 0 := by
      obtain ⟨_, c, hc, hnorm⟩ := v38 hq_ne
      have h1 : dot3 q₀ (cross3 y₁ y₂) = 0 := by
        rw [v45, ← v14, det3_cycle]; exact hdet
      dsimp only [q₀] at h1
      rw [hnorm, v06] at h1
      exact (mul_eq_zero.mp h1).resolve_left hc
    have hφ0 : Mv.eval (cross3 y₁ y₂) φ = 0 := by
      rcases hdvd with ⟨Q, rfl⟩
      rw [map_mul, hG_eq, v27, hq_dot, zero_mul]
    have hφ_id : Mv.eval (cross3 y₁ y₂) (Mv.map (Rh.id (ZMod p)) φ) = 0 := by
      simpa using hφ0
    obtain ⟨l, hl, c, hcr_eq⟩ := (henv y₁ hy₁).2 (Rh.id (ZMod p)) (cross3 y₁ y₂)
      hcr_ne (v56 y₁ y₂) hφ_id
    have hc_ne : c ≠ 0 := fun h0 => hcr_ne (by rw [hcr_eq, h0, zero_smul])
    have hly₂ : dot3 l y₂ = 0 := by
      have h0 : dot3 (cross3 y₁ y₂) y₂ = 0 := v28 y₁ y₂
      rw [hcr_eq, v06] at h0
      exact (mul_eq_zero.mp h0).resolve_left hc_ne
    exact (mem_filter.mp hl).2 y₂ hy₂ h12.symm hly₂
  by_cases hqK : q₀ ∈ K
  · obtain ⟨y, hyK, hyq⟩ := exists_mem_ne (by omega : 1 < K.card) q₀
    exact hno_secant q₀ hqK y hyK hyq.symm (det3_self_12 q₀ y)
  · obtain ⟨x, hxK, y, hyK, hxy, hdet⟩ := hK.2 q₀ hq₀_mem hqK
    exact hno_secant x hxK y hyK hxy hdet
set_option maxHeartbeats 800000 in
lemma v59 {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {K : Finset (Fin 3 → ZMod p)} (hK : IsProjArc K) (hKbig : 3 * p + 3 < 4 * K.card)
    {φ G : Mv3 (ZMod p)}
    (henv : ∀ y ∈ K, (∀ l ∈ v23 K y, Mv.eval l φ = 0) ∧ (∀ {L : Type} [Field L] (ι : ZMod p →+* L) (z : Fin 3 → L), z ≠ 0 → dot3 z (ι ∘ y) = 0 → Mv.eval z (Mv.map ι φ) = 0 → ∃ l ∈ v23 K y, ∃ c : L, z = c • (ι ∘ l)))
    (hG_hom : G.IsHomogeneous 2)
    (hG_irr : Irreducible (Mv.map (ZMod.castHom (dvd_refl p) (AlgebraicClosure (ZMod p))) G))
    (hdvd : G ∣ φ) :
    ∃ C : Mv3 (ZMod p), C ≠ 0 ∧ C.IsHomogeneous 2 ∧ ∀ x ∈ K, Mv.eval x C = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have := Nat.le_of_dvd (by norm_num) this; have := (Fact.out : p.Prime).two_le; omega
  let A : Mat3 (ZMod p) := Mx.of fun i j =>
    if i = j then G.coeff (Fu.single i 2)
    else (2 : ZMod p)⁻¹ * G.coeff (Fu.single i 1 + Fu.single j 1)
  have hA_symm : A.transpose = A := by
    refine Mx.ext fun i j => ?_
    simp only [Mx.transpose_apply, A, Mx.of_apply]
    by_cases h : j = i
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), add_comm]
  let m00 : E3 := Fu.single 0 2
  let m11 : E3 := Fu.single 1 2
  let m22 : E3 := Fu.single 2 2
  let m01 : E3 := Fu.single 0 1 + Fu.single 1 1
  let m02 : E3 := Fu.single 0 1 + Fu.single 2 1
  let m12 : E3 := Fu.single 1 1 + Fu.single 2 1
  have hdisj : m00 ≠ m11 ∧ m00 ≠ m22 ∧ m00 ≠ m01 ∧ m00 ≠ m02 ∧ m00 ≠ m12 ∧ m11 ≠ m22 ∧ m11 ≠ m01 ∧ m11 ≠ m02 ∧ m11 ≠ m12 ∧ m22 ≠ m01 ∧ m22 ≠ m02 ∧ m22 ≠ m12 ∧ m01 ≠ m02 ∧ m01 ≠ m12 ∧ m02 ≠ m12 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro h <;> first
      | (have := congr_arg (fun f : E3 => f 0) h; simp [m00, m11, m22, m01, m02, m12] at this; done)
      | (have := congr_arg (fun f : E3 => f 1) h; simp [m11, m22, m01, m02, m12] at this)
  have hdeg2_cases : ∀ m : E3, m 0 + m 1 + m 2 = 2 → m = m00 ∨ m = m11 ∨ m = m22 ∨ m = m01 ∨ m = m02 ∨ m = m12 := by
    intro m hd
    have h0 : m 0 = 0 ∨ m 0 = 1 ∨ m 0 = 2 := by omega
    rcases h0 with h0 | h0 | h0
    · have h1 : m 1 = 0 ∨ m 1 = 1 ∨ m 1 = 2 := by omega
      rcases h1 with h1 | h1 | h1
      · right; right; left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [m22, h0, h1]; omega
      · right; right; right; right; right; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [m12, h0, h1]; omega
      · right; left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [m11, h0, h1]; omega
    · have h1 : m 1 = 0 ∨ m 1 = 1 := by omega
      rcases h1 with h1 | h1
      · right; right; right; right; left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [m02, h0, h1]; omega
      · right; right; right; left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [m01, h0, h1]; omega
    · left; ext i; rcases v03 i with rfl | rfl | rfl <;> simp [m00, h0] <;> omega
  have hG_quad : ∀ v : Fin 3 → ZMod p, Mv.eval v G = dot3 v (A.mulVec v) := by
    intro v
    conv_lhs => rw [Mv.as_sum G, map_sum]
    let deg2 : Finset (E3) := {m00, m11, m22, m01, m02, m12}
    have hsupp_sub : G.support ⊆ deg2 := by
      intro m hm
      simp only [deg2, mem_insert, mem_singleton]
      exact hdeg2_cases m (v10 hG_hom (Mv.mem_support_iff.mp hm))
    rw [sum_subset hsupp_sub (fun m _ hm => by rw [Mv.notMem_support_iff.mp hm, map_zero, map_zero])]
    simp only [deg2, Fs.sum_insert, mem_insert, mem_singleton, Fs.sum_singleton, hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2.1, hdisj.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.2.2, or_self, not_false_eq_true]
    have hev_m : ∀ m : E3, Mv.eval v (Mv.monomial m (G.coeff m)) = G.coeff m * (v 0 ^ m 0 * v 1 ^ m 1 * v 2 ^ m 2) := by
      intro m; rw [Mv.eval_monomial, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three]
    rw [hev_m m00, hev_m m11, hev_m m22, hev_m m01, hev_m m02, hev_m m12]
    simp only [m00, m11, m22, m01, m02, m12, Fu.add_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul, dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three, A, Mx.of_apply]
    have hadd_comm01 : Fu.single (1 : Fin 3) 1 + Fu.single 0 1 = Fu.single 0 1 + Fu.single 1 1 := add_comm _ _
    have hadd_comm02 : Fu.single (2 : Fin 3) 1 + Fu.single 0 1 = Fu.single 0 1 + Fu.single 2 1 := add_comm _ _
    have hadd_comm12 : Fu.single (2 : Fin 3) 1 + Fu.single 1 1 = Fu.single 1 1 + Fu.single 2 1 := add_comm _ _
    rw [hadd_comm01, hadd_comm02, hadd_comm12]
    have h2inv : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2ne]
    linear_combination
      -(G.coeff (Fu.single 0 1 + Fu.single 1 1) * v 0 * v 1) * h2inv -
      (G.coeff (Fu.single 0 1 + Fu.single 2 1) * v 0 * v 2) * h2inv -
      (G.coeff (Fu.single 1 1 + Fu.single 2 1) * v 1 * v 2) * h2inv
  have hG_poly : G = ∑ i : Fin 3, ∑ j : Fin 3, Mv.C (A i j) * Mv.X i * Mv.X j := by
    let Q := ∑ i : Fin 3, ∑ j : Fin 3, Mv.C (A i j) * Mv.X i * Mv.X j
    change G = Q
    have hQ_hom : Q.IsHomogeneous 2 := by
      apply MvPolynomial.IsHomogeneous.sum; intro i _
      apply MvPolynomial.IsHomogeneous.sum; intro j _
      rw [mul_assoc]
      exact v07 _ ((Mv.isHomogeneous_X _ i).mul (Mv.isHomogeneous_X _ j))
    ext m
    by_cases hm2 : m 0 + m 1 + m 2 = 2
    · have hQ_eq : Q = Mv.monomial m00 (A 0 0) + Mv.monomial m11 (A 1 1) + Mv.monomial m22 (A 2 2) + Mv.monomial m01 (A 0 1 + A 1 0) + Mv.monomial m02 (A 0 2 + A 2 0) + Mv.monomial m12 (A 1 2 + A 2 1) := by
        dsimp only [Q, m00, m11, m22, m01, m02, m12]
        simp only [Fi.sum_univ_three, Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_three, Fu.add_apply, Fu.single_apply, Fi.reduceEq, ↓reduceIte, add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul, map_add]
        ring
      have h2inv : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2ne]
      rw [hQ_eq]
      rcases hdeg2_cases m hm2 with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [Mv.coeff_add, Mv.coeff_monomial, A, Mx.of_apply, ↓reduceIte, hdisj.1.symm, hdisj.2.1.symm, hdisj.2.2.1.symm, hdisj.2.2.2.1.symm, hdisj.2.2.2.2.1.symm, add_zero]; rfl
      · simp only [Mv.coeff_add, Mv.coeff_monomial, A, Mx.of_apply, ↓reduceIte, hdisj.1, hdisj.2.2.2.2.2.1.symm, hdisj.2.2.2.2.2.2.1.symm, hdisj.2.2.2.2.2.2.2.1.symm, hdisj.2.2.2.2.2.2.2.2.1.symm, add_zero, zero_add]; rfl
      · simp only [Mv.coeff_add, Mv.coeff_monomial, A, Mx.of_apply, ↓reduceIte, hdisj.2.1, hdisj.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.1.symm, hdisj.2.2.2.2.2.2.2.2.2.2.1.symm, hdisj.2.2.2.2.2.2.2.2.2.2.2.1.symm, add_zero, zero_add]; rfl
      · simp only [Mv.coeff_add, Mv.coeff_monomial, A, Mx.of_apply, Fi.reduceEq, ↓reduceIte, hdisj.2.2.1, hdisj.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.1.symm, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm, add_zero, zero_add]
        dsimp only [m01]; rw [add_comm (Fu.single (1 : Fin 3) 1), ← add_mul, h2inv, one_mul]
      · simp only [Mv.coeff_add, Mv.coeff_monomial, A, Mx.of_apply, Fi.reduceEq, ↓reduceIte, hdisj.2.2.2.1, hdisj.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm, add_zero, zero_add]
        dsimp only [m02]; rw [add_comm (Fu.single (2 : Fin 3) 1), ← add_mul, h2inv, one_mul]
      · simp only [Mv.coeff_add, Mv.coeff_monomial, A, Mx.of_apply, Fi.reduceEq, ↓reduceIte, hdisj.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2.2.2.2.2.2, add_zero, zero_add]
        dsimp only [m12]; rw [add_comm (Fu.single (2 : Fin 3) 1), ← add_mul, h2inv, one_mul]
    · have h1 : G.coeff m = 0 := by by_contra hne; exact hm2 (v10 hG_hom hne)
      have h2 : Q.coeff m = 0 := by by_contra hne; exact hm2 (v10 hQ_hom hne)
      rw [h1, h2]
  classical
  set L := AlgebraicClosure (ZMod p)
  set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
  have hA_det : A.det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv_ne, hAv⟩ : ∃ v : Fin 3 → ZMod p, v ≠ 0 ∧ A.mulVec v = 0 := by
      by_contra hall; push Not at hall
      have hinj : Fn.Injective A.mulVec := by
        intro x y hxy
        by_contra hne
        exact hall (x - y) (sub_ne_zero.mpr hne) (by rw [Mx.mulVec_sub, hxy, sub_self])
      have hsurj : Fn.Surjective A.mulVec := Finite.injective_iff_surjective.mp hinj
      have hinv : IsUnit A.det := by
        let e : (Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p) :=
          LinearEquiv.ofBijective A.mulVecLin ⟨hinj, hsurj⟩
        have h1 : A * Mx.of (fun i j => e.symm (Pi.single j 1) i) = 1 := by
          refine Mx.ext fun i j => ?_
          rw [Mx.mul_apply, Mx.one_apply]
          have hmv : A.mulVec (e.symm (Pi.single j (1 : ZMod p))) = Pi.single j (1 : ZMod p) :=
            e.apply_symm_apply (Pi.single j (1 : ZMod p))
          have hmv_i := congr_fun hmv i
          simpa [Mx.mulVec, dotProduct, Pi.single_apply, eq_comm] using hmv_i
        have hd := congr_arg Mx.det h1
        rw [Mx.det_mul, Mx.det_one] at hd
        exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hd)
      exact hinv.ne_zero hdet0
    have hex_i : ∃ i : Fin 3, v i ≠ 0 := by by_contra ha; push Not at ha; exact hv_ne (funext ha)
    rcases hex_i with ⟨i, hi⟩
    have hM_ex : ∃ M Minv : Mat3 (ZMod p), M * Minv = 1 ∧ Minv * M = 1 ∧ M.mulVec ![0, 0, 1] = v := by
      rcases v03 i with rfl | rfl | rfl
      · let M : Mat3 (ZMod p) := !![0, 0, v 0; 1, 0, v 1; 0, 1, v 2]
        let Mi : Mat3 (ZMod p) :=
          !![-v 1 * (v 0)⁻¹, 1, 0; -v 2 * (v 0)⁻¹, 0, 1; (v 0)⁻¹, 0, 0]
        refine ⟨M, Mi, ?_, ?_, ?_⟩
        · refine Mx.ext fun r c => ?_; fin_cases r <;> fin_cases c <;>
            simp [M, Mi, Mx.mul_apply, Fi.sum_univ_three]; field_simp [hi]
        · refine Mx.ext fun r c => ?_; fin_cases r <;> fin_cases c <;>
            simp [M, Mi, Mx.mul_apply, Fi.sum_univ_three] <;> field_simp [hi] <;> ring
        · ext r; fin_cases r <;> simp [M, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      · let M : Mat3 (ZMod p) := !![1, 0, v 0; 0, 0, v 1; 0, 1, v 2]
        let Mi : Mat3 (ZMod p) :=
          !![1, -v 0 * (v 1)⁻¹, 0; 0, -v 2 * (v 1)⁻¹, 1; 0, (v 1)⁻¹, 0]
        refine ⟨M, Mi, ?_, ?_, ?_⟩
        · refine Mx.ext fun r c => ?_; fin_cases r <;> fin_cases c <;>
            simp [M, Mi, Mx.mul_apply, Fi.sum_univ_three]; field_simp [hi]
        · refine Mx.ext fun r c => ?_; fin_cases r <;> fin_cases c <;>
            simp [M, Mi, Mx.mul_apply, Fi.sum_univ_three] <;> field_simp [hi] <;> ring
        · ext r; fin_cases r <;> simp [M, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      · let M : Mat3 (ZMod p) := !![1, 0, v 0; 0, 1, v 1; 0, 0, v 2]
        let Mi : Mat3 (ZMod p) :=
          !![1, 0, -v 0 * (v 2)⁻¹; 0, 1, -v 1 * (v 2)⁻¹; 0, 0, (v 2)⁻¹]
        refine ⟨M, Mi, ?_, ?_, ?_⟩
        · refine Mx.ext fun r c => ?_; fin_cases r <;> fin_cases c <;>
            simp [M, Mi, Mx.mul_apply, Fi.sum_univ_three]; field_simp [hi]
        · refine Mx.ext fun r c => ?_; fin_cases r <;> fin_cases c <;>
            simp [M, Mi, Mx.mul_apply, Fi.sum_univ_three] <;> field_simp [hi] <;> ring
        · ext r; fin_cases r <;> simp [M, Mx.mulVec, dotProduct, Fi.sum_univ_three]
    rcases hM_ex with ⟨M, Minv, hMM1, hMM2, hMv⟩
    let ML : Mat3 L := ι.mapMatrix M
    let MLi : Mat3 L := ι.mapMatrix Minv
    have hML1 : ML * MLi = 1 := by rw [← map_mul, hMM1, map_one]
    have hML2 : MLi * ML = 1 := by rw [← map_mul, hMM2, map_one]
    set G_L := sMat ML (Mv.map ι G)
    have hGL_irr : Irreducible G_L := v88 hML1 hML2 hG_irr
    let B' : Mat3 (ZMod p) := M.transpose * A * M
    have hB'2 : ∀ k : Fin 3, B' k 2 = 0 ∧ B' 2 k = 0 := by
      have hAM2 : ∀ r : Fin 3, (A * M) r 2 = 0 := by
        intro r
        have := congr_fun hAv r
        rw [← hMv] at this
        simpa [Mx.mul_apply, Mx.mulVec, dotProduct, Fi.sum_univ_three] using this
      have hB'symm : B'.transpose = B' := by
        dsimp only [B']; rw [Mx.transpose_mul, Mx.transpose_mul, Mx.transpose_transpose, hA_symm, Mx.mul_assoc]
      intro k
      have hk2 : B' k 2 = 0 := by
        dsimp only [B']; rw [Mx.mul_assoc, Mx.mul_apply, Fi.sum_univ_three]
        simp [hAM2]
      refine ⟨hk2, ?_⟩
      rw [← hB'symm, Mx.transpose_apply]; exact hk2
    have hGL_form : G_L = Mv.C (ι (B' 0 0)) * Mv.X 0 ^ 2 + Mv.C (ι (B' 0 1 + B' 1 0)) * Mv.X 0 * Mv.X 1 + Mv.C (ι (B' 1 1)) * Mv.X 1 ^ 2 := by
      have h1 : G_L = ∑ r : Fin 3, ∑ c : Fin 3, Mv.C (ι (B' r c)) * Mv.X r * Mv.X c := by
        dsimp only [G_L]
        rw [hG_poly, map_sum, map_sum]
        have hX : ∀ k : Fin 3, sMat ML (Mv.X k) = ∑ r : Fin 3, Mv.C (ι (M k r)) * Mv.X r :=
          fun k => by simp [sMat, ML]
        have hC : ∀ a : L, sMat ML (Mv.C a) = Mv.C a :=
          fun a => by simp [sMat]
        have hLHS : ∑ i : Fin 3, sMat ML (Mv.map ι
              (∑ j : Fin 3, Mv.C (A i j) * Mv.X i * Mv.X j)) =
            ∑ i : Fin 3, ∑ j : Fin 3, ∑ r : Fin 3, ∑ c : Fin 3, Mv.C (ι (M i r * A i j * M j c)) * Mv.X r * Mv.X c := by
          apply sum_congr rfl; intro i _
          rw [map_sum, map_sum]
          apply sum_congr rfl; intro j _
          simp only [map_mul, Mv.map_C, Mv.map_X, hC, hX, mul_sum, sum_mul]
          rw [sum_comm]
          apply sum_congr rfl; intro r _
          apply sum_congr rfl; intro c _
          ring
        have hRHS : ∑ r : Fin 3, ∑ c : Fin 3, Mv.C (ι (B' r c)) * Mv.X r * Mv.X c = ∑ r : Fin 3, ∑ c : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, Mv.C (ι (M i r * A i j * M j c)) * Mv.X r * Mv.X c := by
          apply sum_congr rfl; intro r _
          apply sum_congr rfl; intro c _
          have hBrc : B' r c = ∑ i : Fin 3, ∑ j : Fin 3, M i r * A i j * M j c := by
            simp only [B', Mx.mul_apply, Mx.transpose_apply, sum_mul]
            rw [sum_comm]
          rw [hBrc, map_sum, map_sum, sum_mul, sum_mul]
          apply sum_congr rfl; intro i _
          rw [map_sum, map_sum, sum_mul, sum_mul]
        rw [hLHS, hRHS]
        rw [sum_comm]
        conv_lhs => arg 2; ext j; rw [sum_comm]
        rw [sum_comm]
        apply sum_congr rfl; intro r _
        conv_lhs => arg 2; ext j; rw [sum_comm]
        rw [sum_comm]
        apply sum_congr rfl; intro c _
        rw [sum_comm]
      rw [h1, Fi.sum_univ_three]
      simp only [Fi.sum_univ_three, (hB'2 0).1, (hB'2 0).2, (hB'2 1).1, (hB'2 1).2, (hB'2 2).1, map_zero, zero_mul, add_zero, map_add]
      ring
    set a := ι (B' 0 0)
    set b := ι (B' 0 1 + B' 1 0)
    set c := ι (B' 1 1)
    have hnot_irr : ¬ Irreducible (Mv.C a * Mv.X 0 ^ 2 + Mv.C b * Mv.X 0 * Mv.X 1 + Mv.C c * Mv.X 1 ^ 2 : Mv3 L) := by
      have hlin_not_unit : ∀ (u w : L), (u ≠ 0 ∨ w ≠ 0) → ¬ IsUnit (Mv.C u * Mv.X 0 + Mv.C w * Mv.X 1 :
            Mv3 L) := by
        intro u w huw hu
        rcases v120.mp hu with ⟨r, _, hr⟩
        have h01 : (Fu.single (0 : Fin 3) 1 : E3) ≠ Fu.single 1 1 := fun h => by
          have := congr_arg (fun f : E3 => f 0) h; simp at this
        have h0_0 : (0 : E3) ≠ Fu.single 0 1 := fun h => by
          have := congr_arg (fun f : E3 => f 0) h; simp at this
        have h0_1 : (0 : E3) ≠ Fu.single 1 1 := fun h => by
          have := congr_arg (fun f : E3 => f 1) h; simp at this
        rcases huw with hu0 | hw0
        · have := congr_arg (Mv.coeff (Fu.single 0 1)) hr
          simp [Mv.coeff_C, Mv.coeff_X, h01.symm, h0_0] at this; exact hu0 this
        · have := congr_arg (Mv.coeff (Fu.single 1 1)) hr
          simp [Mv.coeff_C, Mv.coeff_X, h01, h0_1] at this; exact hw0 this
      by_cases ha : a = 0
      · rw [ha]
        intro hirr
        have hfac : (Mv.C (0 : L) * Mv.X 0 ^ 2 + Mv.C b * Mv.X 0 * Mv.X 1 + Mv.C c * Mv.X 1 ^ 2 : Mv3 L) = Mv.X 1 * (Mv.C b * Mv.X 0 + Mv.C c * Mv.X 1) := by
          simp; ring
        rcases hirr.isUnit_or_isUnit hfac with h1 | h2
        · exact (v89 1).not_isUnit h1
        · by_cases hbc : b ≠ 0 ∨ c ≠ 0
          · exact hlin_not_unit b c hbc h2
          · push Not at hbc
            have h0 : (Mv.C (0 : L) * Mv.X 0 ^ 2 + Mv.C b * Mv.X 0 * Mv.X 1 + Mv.C c * Mv.X 1 ^ 2 : Mv3 L) = 0 := by
              rw [hbc.1, hbc.2]; simp
            exact hirr.ne_zero h0
      ·
        let poly : Pol L := Pl.C a * Pl.X ^ 2 + Pl.C b * Pl.X + Pl.C c
        have hdeg : poly.degree ≠ 0 := by
          have hnd : poly.natDegree = 2 := by
            have h1 : (Pl.C a * Pl.X ^ 2 : Pol L).natDegree = 2 := by
              rw [Pl.natDegree_C_mul ha, Pl.natDegree_X_pow]
            have h2 : (Pl.C b * Pl.X + Pl.C c : Pol L).natDegree ≤ 1 := by
              refine (Pl.natDegree_add_le _ _).trans (max_le ?_ (by simp))
              exact (Pl.natDegree_C_mul_le _ _).trans (by simp)
            have h3 : poly = Pl.C a * Pl.X ^ 2 + (Pl.C b * Pl.X + Pl.C c) := by ring
            rw [h3, Pl.natDegree_add_eq_left_of_natDegree_lt (by omega), h1]
          intro h0
          have := Pl.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
          omega
        obtain ⟨r, hr⟩ := IsAlgClosed.exists_root poly hdeg
        have hr0 : a * r ^ 2 + b * r + c = 0 := by
          simpa [poly, Pl.IsRoot] using hr
        intro hirr
        have hfac : (Mv.C a * Mv.X 0 ^ 2 + Mv.C b * Mv.X 0 * Mv.X 1 + Mv.C c * Mv.X 1 ^ 2 : Mv3 L) = (Mv.C 1 * Mv.X 0 + Mv.C (-r) * Mv.X 1) * (Mv.C a * Mv.X 0 + Mv.C (a * r + b) * Mv.X 1) := by
          have hc_eq : c = -r * (a * r + b) := by linear_combination hr0
          rw [hc_eq]
          simp only [map_one, map_neg, map_add, map_mul]
          ring
        rcases hirr.isUnit_or_isUnit hfac with h1 | h2
        · exact hlin_not_unit 1 (-r) (Or.inl one_ne_zero) h1
        · exact hlin_not_unit a (a * r + b) (Or.inl ha) h2
    exact hnot_irr (hGL_form ▸ hGL_irr)
  let B : Mat3 (ZMod p) := A⁻¹
  have hAB : A * B = 1 := Mx.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA_det)
  have hBA : B * A = 1 := Mx.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA_det)
  have hB_symm : B.transpose = B := by
    have h1 : A * B.transpose = 1 := by
      have := congr_arg Mx.transpose hBA
      rw [Mx.transpose_mul, Mx.transpose_one, hA_symm] at this
      exact this
    calc B.transpose = 1 * B.transpose := (Mx.one_mul _).symm
      _ = (B * A) * B.transpose := by rw [hBA]
      _ = B * (A * B.transpose) := Mx.mul_assoc _ _ _
      _ = B := by rw [h1, Mx.mul_one]
  have hB_det : B.det ≠ 0 := by
    intro h0; have := congr_arg Mx.det hAB
    rw [Mx.det_mul, h0, mul_zero, Mx.det_one] at this; exact one_ne_zero this.symm
  let C_poly : Mv3 (ZMod p) :=
    ∑ i : Fin 3, ∑ j : Fin 3, Mv.C (B i j) * Mv.X i * Mv.X j
  have hC_hom : C_poly.IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum; intro i _
    apply MvPolynomial.IsHomogeneous.sum; intro j _
    rw [mul_assoc]
    exact v07 _ ((Mv.isHomogeneous_X _ i).mul (Mv.isHomogeneous_X _ j))
  have hC_eval : ∀ v : Fin 3 → ZMod p, Mv.eval v C_poly = dot3 v (B.mulVec v) := by
    intro v; simp [C_poly, dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three]; ring
  have hC_ne : C_poly ≠ 0 := by
    intro h0
    have hquad0 : ∀ v : Fin 3 → ZMod p, dot3 v (B.mulVec v) = 0 := fun v => by
      rw [← hC_eval v, h0, map_zero]
    have hbilin0 : ∀ u v : Fin 3 → ZMod p, dot3 u (B.mulVec v) = 0 := by
      intro u v
      have h1 := hquad0 (u + v)
      have h2 := hquad0 u
      have h3 := hquad0 v
      have hsym : dot3 v (B.mulVec u) = dot3 u (B.mulVec v) := by
        have hBu : ∀ i j, B j i = B i j := fun i j => by
          simpa [Mx.transpose_apply] using congr_fun (congr_fun hB_symm i) j
        simp only [dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three]
        rw [hBu 0 1, hBu 0 2, hBu 1 2]; ring
      rw [Mx.mulVec_add, v84, v13, v13, h2, h3, hsym] at h1
      have : (2 : ZMod p) * dot3 u (B.mulVec v) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left h2ne
    have hB0 : B = 0 := by
      refine Mx.ext fun i j => ?_
      have := hbilin0 (Pi.single i 1) (Pi.single j 1)
      rcases v03 i with rfl | rfl | rfl <;> rcases v03 j with rfl | rfl | rfl <;>
        simpa [dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three, Pi.single_apply] using this
    rw [hB0, Mx.det_zero] at hB_det
    exact hB_det rfl
  let C_pts : Finset (Fin 3 → ZMod p) := (pPts p).filter (fun x => dot3 x (B.mulVec x) = 0)
  let Cstar_pts : Finset (Fin 3 → ZMod p) := (pPts p).filter (fun l => dot3 l (A.mulVec l) = 0)
  have hconic_card_le : ∀ (M Minv : Mat3 (ZMod p)), M.transpose = M → M * Minv = 1 → Minv * M = 1 → ((pPts p).filter (fun x => dot3 x (M.mulVec x) = 0)).card ≤ p + 1 := by
    intro M Minv hMs hM1 hM2
    set S := (pPts p).filter (fun x => dot3 x (M.mulVec x) = 0)
    by_cases hS : S = ∅
    · rw [hS, card_empty]; omega
    obtain ⟨P₀, hP₀⟩ := nonempty_iff_ne_empty.mpr hS
    have hP₀n : v53 P₀ := v30.mp (mem_filter.mp hP₀).1
    have hP₀M : dot3 P₀ (M.mulVec P₀) = 0 := (mem_filter.mp hP₀).2
    have hMP₀_ne : M.mulVec P₀ ≠ 0 := fun h0 => v00 hP₀n (by
      rw [← Mx.one_mulVec P₀, ← hM2, ← Mx.mulVec_mulVec, h0, Mx.mulVec_zero])
    let f : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) :=
      fun P => if P = P₀ then normPt (M.mulVec P₀) else normPt (cross3 P₀ P)
    have hsymM : ∀ u v : Fin 3 → ZMod p, dot3 v (M.mulVec u) = dot3 u (M.mulVec v) := by
      intro u v
      have hMij : ∀ i j, M j i = M i j := fun i j => by
        simpa [Mx.transpose_apply] using congr_fun (congr_fun hMs i) j
      simp only [dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      rw [hMij 0 1, hMij 0 2, hMij 1 2]; ring
    have hf_maps : ∀ P ∈ S, f P ∈ lThru P₀ := by
      intro P hP
      by_cases hPP : P = P₀
      · simp only [f, if_pos hPP, lThru, mem_filter]
        refine ⟨v90 hMP₀_ne, ?_⟩
        obtain ⟨_, c, _, hnorm⟩ := v38 hMP₀_ne
        rw [hnorm, v06, v45, hP₀M, mul_zero]
      · simp only [f, if_neg hPP, lThru, mem_filter]
        have hPn := v30.mp (mem_filter.mp hP).1
        have hcr : cross3 P₀ P ≠ 0 := fun h0 => hPP (by
          rcases (v01 (v00 hP₀n)).mp h0 with ⟨c, hc⟩
          exact v04 hPn hP₀n hc)
        refine ⟨v90 hcr, ?_⟩
        obtain ⟨_, c, _, hnorm⟩ := v38 hcr
        rw [hnorm, v06, v56, mul_zero]
    have hf_inj : Set.InjOn f ↑S := by
      intro P₁ hP₁ P₂ hP₂ heq
      have hP1n := v30.mp (mem_filter.mp hP₁).1
      have hP2n := v30.mp (mem_filter.mp hP₂).1
      have hP1M : dot3 P₁ (M.mulVec P₁) = 0 := (mem_filter.mp hP₁).2
      have hP2M : dot3 P₂ (M.mulVec P₂) = 0 := (mem_filter.mp hP₂).2
      have hno_orth : ∀ P ∈ S, P ≠ P₀ → dot3 P (M.mulVec P₀) ≠ 0 := by
        intro P hP hPP hdot0
        have hPn := v30.mp (mem_filter.mp hP).1
        have hPM : dot3 P (M.mulVec P) = 0 := (mem_filter.mp hP).2
        have hcr : cross3 P₀ P ≠ 0 := fun h0 => hPP (by
          rcases (v01 (v00 hP₀n)).mp h0 with ⟨c, hc⟩
          exact v04 hPn hP₀n hc)
        have hMP0_prop := v09 hcr (v45 P₀ _ ▸ hP₀M) (v45 P _ ▸ hdot0)
        have hMP_prop := v09 hcr
          (by rw [v45, hsymM]; exact hdot0) (v45 P _ ▸ hPM)
        rcases hMP0_prop with ⟨c0, hc0⟩
        rcases hMP_prop with ⟨c1, hc1⟩
        have hc0_ne : c0 ≠ 0 := fun h0 => hMP₀_ne (by rw [hc0, h0, zero_smul])
        have hlin : M.mulVec (c1 • P₀ - c0 • P) = 0 := by
          rw [Mx.mulVec_sub, Mx.mulVec_smul, Mx.mulVec_smul, hc0, hc1, smul_smul, smul_smul, mul_comm, sub_self]
        have hvec0 : c1 • P₀ - c0 • P = 0 := by
          rw [← Mx.one_mulVec (c1 • P₀ - c0 • P), ← hM2, ← Mx.mulVec_mulVec, hlin, Mx.mulVec_zero]
        have hP_eq : P = (c0⁻¹ * c1) • P₀ := by
          have : c0 • P = c1 • P₀ := (sub_eq_zero.mp hvec0).symm
          calc P = c0⁻¹ • (c0 • P) := by rw [smul_smul, inv_mul_cancel₀ hc0_ne, one_smul]
            _ = c0⁻¹ • (c1 • P₀) := by rw [this]
            _ = (c0⁻¹ * c1) • P₀ := by rw [smul_smul]
        exact hPP (v04 hPn hP₀n hP_eq)
      by_cases h1 : P₁ = P₀
      · by_cases h2 : P₂ = P₀
        · exact h1.trans h2.symm
        · exfalso
          simp only [f, if_pos h1, if_neg h2] at heq
          have hcr2 : cross3 P₀ P₂ ≠ 0 := fun h0 => h2 (by
            rcases (v01 (v00 hP₀n)).mp h0 with ⟨c, hc⟩
            exact v04 hP2n hP₀n hc)
          rcases (v44 hMP₀_ne hcr2).mp heq with ⟨c, hc, hsc⟩
          have hdot0 : dot3 P₂ (M.mulVec P₀) = 0 := by
            rw [hsc, v02, v45, v28, mul_zero]
          exact hno_orth P₂ hP₂ h2 hdot0
      · by_cases h2 : P₂ = P₀
        · exfalso
          simp only [f, if_neg h1, if_pos h2] at heq
          have hcr1 : cross3 P₀ P₁ ≠ 0 := fun h0 => h1 (by
            rcases (v01 (v00 hP₀n)).mp h0 with ⟨c, hc⟩
            exact v04 hP1n hP₀n hc)
          rcases (v44 hcr1 hMP₀_ne).mp heq with ⟨c, hc, hsc⟩
          have hdot0 : dot3 P₁ (M.mulVec P₀) = 0 := by
            have h0 : dot3 P₁ (cross3 P₀ P₁) = 0 := by rw [v45]; exact v28 P₀ P₁
            rw [hsc, v02] at h0
            exact (mul_eq_zero.mp h0).resolve_left hc
          exact hno_orth P₁ hP₁ h1 hdot0
        · simp only [f, if_neg h1, if_neg h2] at heq
          have hcr1 : cross3 P₀ P₁ ≠ 0 := fun h0 => h1 (by
            rcases (v01 (v00 hP₀n)).mp h0 with ⟨c, hc⟩
            exact v04 hP1n hP₀n hc)
          have hcr2 : cross3 P₀ P₂ ≠ 0 := fun h0 => h2 (by
            rcases (v01 (v00 hP₀n)).mp h0 with ⟨c, hc⟩
            exact v04 hP2n hP₀n hc)
          rcases (v44 hcr1 hcr2).mp heq with ⟨c, _, hsc⟩
          have hdet0 : det3 P₀ P₁ P₂ = 0 := by
            rw [v14, hsc, v06, v28, mul_zero]
          have hlin : ∃ a b : ZMod p, P₂ = a • P₀ + b • P₁ := by
            have hcr01 : cross3 P₀ P₁ ≠ 0 := hcr1
            have hex : ∃ w : Fin 3 → ZMod p, det3 P₀ P₁ w ≠ 0 := by
              have hne : ∃ i : Fin 3, cross3 P₀ P₁ i ≠ 0 := by
                by_contra ha; push Not at ha; exact hcr01 (funext ha)
              rcases hne with ⟨i, hi⟩
              refine ⟨Pi.single i 1, ?_⟩
              rw [v14]
              rcases v03 i with rfl | rfl | rfl <;> simpa [dot3, Pi.single_apply] using hi
            rcases hex with ⟨w, hw⟩
            have hcr := v174 P₀ P₁ w P₂
            rw [hdet0, zero_smul, add_zero] at hcr
            refine ⟨(det3 P₀ P₁ w)⁻¹ * det3 P₂ P₁ w, (det3 P₀ P₁ w)⁻¹ * det3 P₀ P₂ w, ?_⟩
            calc P₂ = (det3 P₀ P₁ w)⁻¹ • (det3 P₀ P₁ w • P₂) := by
                  rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
              _ = (det3 P₀ P₁ w)⁻¹ • (det3 P₂ P₁ w • P₀ + det3 P₀ P₂ w • P₁) := by rw [hcr]
              _ = _ := by rw [smul_add, smul_smul, smul_smul]
          rcases hlin with ⟨a, b, hP2ab⟩
          rw [hP2ab, Mx.mulVec_add, Mx.mulVec_smul, Mx.mulVec_smul, v84, v13, v13, v06, v06, v06, v06, v02, v02, v02, v02, hP₀M, hP1M, hsymM P₁ P₀] at hP2M
          have h2ab : (2 : ZMod p) * a * b * dot3 P₁ (M.mulVec P₀) = 0 := by
            linear_combination hP2M
          have hab0 : a = 0 ∨ b = 0 := by
            have h1' := (mul_eq_zero.mp h2ab).resolve_right (hno_orth P₁ hP₁ h1)
            rcases mul_eq_zero.mp h1' with h2a | hb0
            · exact Or.inl ((mul_eq_zero.mp h2a).resolve_left h2ne)
            · exact Or.inr hb0
          rcases hab0 with rfl | rfl
          · rw [zero_smul, zero_add] at hP2ab
            exact (v04 hP2n hP1n hP2ab).symm
          · rw [zero_smul, add_zero] at hP2ab
            exact absurd (v04 hP2n hP₀n hP2ab) h2
    calc S.card = (S.image f).card := (card_image_of_injOn hf_inj).symm
      _ ≤ (lThru P₀).card := card_le_card (image_subset_iff.mpr hf_maps)
      _ = p + 1 := v200 (v00 hP₀n)
  have hC_card : C_pts.card ≤ p + 1 := hconic_card_le B A hB_symm hBA hAB
  have hCstar_card : Cstar_pts.card ≤ p + 1 := hconic_card_le A B hA_symm hAB hBA
  by_cases hKsub : K ⊆ C_pts
  · refine ⟨C_poly, hC_ne, hC_hom, fun x hx => ?_⟩
    rw [hC_eval x]
    exact (mem_filter.mp (hKsub hx)).2
  exfalso
  obtain ⟨Q, hQK, hQnotC⟩ := not_subset.mp hKsub
  have hQn : v53 Q := hK.1 Q hQK
  have hQBQ_ne : dot3 Q (B.mulVec Q) ≠ 0 := by
    intro h0; exact hQnotC (mem_filter.mpr ⟨v30.mpr hQn, h0⟩)
  have hno_secant_Cstar : ∀ l ∈ Cstar_pts, ∀ y₁ ∈ K, ∀ y₂ ∈ K, dot3 l y₁ = 0 → dot3 l y₂ = 0 → y₁ = y₂ := by
    intro l hl y₁ hy₁ y₂ hy₂ h1 h2
    have hln := v30.mp (mem_filter.mp hl).1
    have hGl : Mv.eval l G = 0 := by rw [hG_quad]; exact (mem_filter.mp hl).2
    have hφl : Mv.eval l (Mv.map (Rh.id (ZMod p)) φ) = 0 := by
      rcases hdvd with ⟨R, rfl⟩
      simp [map_mul, hGl]
    obtain ⟨l', hl', c, hl_eq⟩ := (henv y₁ hy₁).2 (Rh.id (ZMod p)) l (v00 hln) h1 hφl
    have hc_ne : c ≠ 0 := fun h0 => v00 hln (by rw [hl_eq, h0, zero_smul])
    have hl'y₂ : dot3 l' y₂ = 0 := by
      rw [hl_eq, v06] at h2
      exact (mul_eq_zero.mp h2).resolve_left hc_ne
    by_contra hne
    exact (mem_filter.mp hl').2 y₂ hy₂ (Ne.symm hne) hl'y₂
  have hCstar_y_in : ∀ y ∈ K, y ∈ C_pts → 1 ≤ (Cstar_pts ∩ lThru y).card := by
    intro y hyK hyC
    have hyn := hK.1 y hyK
    have hyBy : dot3 y (B.mulVec y) = 0 := (mem_filter.mp hyC).2
    have hBy_ne : B.mulVec y ≠ 0 := fun h0 => v00 hyn (by
      rw [← Mx.one_mulVec y, ← hAB, ← Mx.mulVec_mulVec, h0, Mx.mulVec_zero])
    set l₀ := normPt (B.mulVec y)
    have hl₀_mem : l₀ ∈ Cstar_pts ∩ lThru y := by
      obtain ⟨_, c, _, hnorm⟩ := v38 hBy_ne
      dsimp only [Cstar_pts, lThru]
      rw [mem_inter, mem_filter, mem_filter]
      refine ⟨⟨v90 hBy_ne, ?_⟩, ⟨v90 hBy_ne, ?_⟩⟩
      · dsimp only [l₀]; rw [hnorm, Mx.mulVec_smul, v06, v02, Mx.mulVec_mulVec, hAB, Mx.one_mulVec, v45, hyBy, mul_zero, mul_zero]
      · dsimp only [l₀]; rw [hnorm, v06, v45, hyBy, mul_zero]
    exact one_le_card.mpr ⟨l₀, hl₀_mem⟩
  have hCstar_y_out : ∀ y ∈ K, y ∉ C_pts → 2 ≤ (Cstar_pts ∩ lThru y).card := by
    intro y hyK hyNotC
    have hyn := hK.1 y hyK
    have hy_ne : y ≠ 0 := v00 hyn
    have hyBy_ne : dot3 y (B.mulVec y) ≠ 0 := fun h0 =>
      hyNotC (mem_filter.mpr ⟨v30.mpr hyn, h0⟩)
    have hex : ∃ i : Fin 3, y i ≠ 0 := by by_contra ha; push Not at ha; exact hy_ne (funext ha)
    rcases hex with ⟨i, hi⟩
    have htwo : ∃ u₁ u₂ : Fin 3 → ZMod p, dot3 u₁ y = 0 ∧ dot3 u₂ y = 0 ∧ cross3 u₁ u₂ ≠ 0 := by
      rcases v03 i with rfl | rfl | rfl
      · exact ⟨![-y 1, y 0, 0], ![-y 2, 0, y 0], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 0; simp [cross3] at this; exact hi this⟩
      · exact ⟨![y 1, -y 0, 0], ![0, -y 2, y 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 1; simp [cross3] at this; exact hi this⟩
      · exact ⟨![y 2, 0, -y 0], ![0, y 2, -y 1], by simp [dot3]; ring, by simp [dot3]; ring, by intro h0; have := congr_fun h0 2; simp [cross3] at this; exact hi this⟩
    rcases htwo with ⟨u₁, u₂, hu1, hu2, hcr12⟩
    rcases v09 hcr12 (v45 u₁ y ▸ hu1) (v45 u₂ y ▸ hu2) with ⟨ky, hky⟩
    have hky_ne : ky ≠ 0 := fun h0 => hy_ne (by rw [hky, h0, zero_smul])
    set a0 := dot3 u₁ (A.mulVec u₁)
    set b0 := dot3 u₁ (A.mulVec u₂)
    set c0 := dot3 u₂ (A.mulVec u₂)
    have hAij : ∀ r c, A c r = A r c := fun r c => by
      simpa [Mx.transpose_apply] using congr_fun (congr_fun hA_symm r) c
    have hsymA : ∀ w₁ w₂ : Fin 3 → ZMod p, dot3 w₂ (A.mulVec w₁) = dot3 w₁ (A.mulVec w₂) := by
      intro w₁ w₂
      simp only [dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      rw [hAij 0 1, hAij 0 2, hAij 1 2]; ring
    have hdisc_ne : a0 * c0 - b0 ^ 2 ≠ 0 := by
      have hadj : A.adjugate.mulVec (cross3 u₁ u₂) = cross3 (A.mulVec u₁) (A.mulVec u₂) := by
        ext r; rcases v03 r with rfl | rfl | rfl <;>
          simp [Mx.mulVec, dotProduct, Fi.sum_univ_three, Mx.adjugate_apply, Mx.det_fin_three, Mx.updateRow_apply, cross3] <;>
          rw [hAij 0 1, hAij 0 2, hAij 1 2] <;> ring
      have hB_adj : A.det • B = A.adjugate := by
        have h1 := Mx.mul_adjugate A
        calc A.det • B = B * (A.det • 1) := by rw [Mx.mul_smul, Mx.mul_one]
          _ = B * (A * A.adjugate) := by rw [h1]
          _ = (B * A) * A.adjugate := (Mx.mul_assoc _ _ _).symm
          _ = A.adjugate := by rw [hBA, Mx.one_mul]
      have hcb : A.det * dot3 (cross3 u₁ u₂) (B.mulVec (cross3 u₁ u₂)) = a0 * c0 - b0 ^ 2 := by
        have h1 : A.det * dot3 (cross3 u₁ u₂) (B.mulVec (cross3 u₁ u₂)) = dot3 (cross3 u₁ u₂) (A.adjugate.mulVec (cross3 u₁ u₂)) := by
          rw [← v02, ← Mx.smul_mulVec, hB_adj]
        rw [h1, hadj]
        have hlag : dot3 (cross3 u₁ u₂) (cross3 (A.mulVec u₁) (A.mulVec u₂)) = dot3 u₁ (A.mulVec u₁) * dot3 u₂ (A.mulVec u₂) - dot3 u₁ (A.mulVec u₂) * dot3 u₂ (A.mulVec u₁) := by
          simp only [dot3, cross3, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons]
          ring
        rw [hlag, hsymA u₁ u₂]; dsimp only [a0, b0, c0]; ring
      have hcrB_ne : dot3 (cross3 u₁ u₂) (B.mulVec (cross3 u₁ u₂)) ≠ 0 := by
        rw [hky, Mx.mulVec_smul, v06, v02] at hyBy_ne
        exact right_ne_zero_of_mul (right_ne_zero_of_mul hyBy_ne)
      rw [← hcb]; exact mul_ne_zero hA_det hcrB_ne
    have htwo_L : ∃ z₁ z₂ : Fin 3 → L, z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ cross3 z₁ z₂ ≠ 0 ∧ dot3 z₁ (ι ∘ y) = 0 ∧ dot3 z₂ (ι ∘ y) = 0 ∧ Mv.eval z₁ (Mv.map ι G) = 0 ∧ Mv.eval z₂ (Mv.map ι G) = 0 := by
      have hev_lin : ∀ s t : L, Mv.eval (s • (ι ∘ u₁) + t • (ι ∘ u₂)) (Mv.map ι G) = ι a0 * s ^ 2 + (2 * ι b0) * s * t + ι c0 * t ^ 2 := by
        intro s t
        rw [hG_poly, map_sum]
        simp only [map_mul, Mv.map_C, Mv.map_X, Mv.eval_C, Mv.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fn.comp_apply, Fi.sum_univ_three, a0, b0, c0, dot3, Mx.mulVec, dotProduct, map_add]
        rw [hAij 0 1, hAij 0 2, hAij 1 2]; ring
      have hdot_lin : ∀ s t : L, dot3 (s • (ι ∘ u₁) + t • (ι ∘ u₂)) (ι ∘ y) = 0 := by
        intro s t
        have h1 : dot3 (ι ∘ u₁) (ι ∘ y) = 0 := by
          have : dot3 (ι ∘ u₁) (ι ∘ y) = ι (dot3 u₁ y) := by simp [dot3]
          rw [this, hu1, map_zero]
        have h2 : dot3 (ι ∘ u₂) (ι ∘ y) = 0 := by
          have : dot3 (ι ∘ u₂) (ι ∘ y) = ι (dot3 u₂ y) := by simp [dot3]
          rw [this, hu2, map_zero]
        rw [v84, v06, v06, h1, h2]; ring
      have hcr_lin : ∀ s₁ t₁ s₂ t₂ : L, cross3 (s₁ • (ι ∘ u₁) + t₁ • (ι ∘ u₂)) (s₂ • (ι ∘ u₁) + t₂ • (ι ∘ u₂)) = (s₁ * t₂ - t₁ * s₂) • (ι ∘ cross3 u₁ u₂) := by
        intro s₁ t₁ s₂ t₂
        ext r; fin_cases r <;> simp [cross3, Fn.comp_apply] <;> ring
      have hιcr_ne : ι ∘ cross3 u₁ u₂ ≠ 0 := fun h0 => hcr12 (funext fun r =>
        ι.injective ((congr_fun h0 r).trans (map_zero ι).symm))
      have hιu1_ne : ι ∘ u₁ ≠ 0 := fun h0 => hcr12 (by
        have hu10 : u₁ = 0 := funext fun r => ι.injective ((congr_fun h0 r).trans (map_zero ι).symm)
        rw [hu10]; ext r; fin_cases r <;> simp [cross3])
      have hιu2_ne : ι ∘ u₂ ≠ 0 := fun h0 => hcr12 (by
        have hu20 : u₂ = 0 := funext fun r => ι.injective ((congr_fun h0 r).trans (map_zero ι).symm)
        rw [hu20]; ext r; fin_cases r <;> simp [cross3])
      by_cases ha0 : a0 = 0
      ·
        have hb0_ne : b0 ≠ 0 := by
          intro h0; rw [ha0, h0] at hdisc_ne; simp at hdisc_ne
        have h2b0_ne : ι (2 * b0) ≠ 0 := fun h0 => mul_ne_zero h2ne hb0_ne (ι.injective (h0.trans (map_zero ι).symm))
        refine ⟨1 • (ι ∘ u₁) + 0 • (ι ∘ u₂), (-ι c0) • (ι ∘ u₁) + ι (2 * b0) • (ι ∘ u₂), ?_, ?_, ?_, hdot_lin _ _, hdot_lin _ _, ?_, ?_⟩
        · simpa using hιu1_ne
        · intro h0
          have hl : cross3 (ι ∘ u₁) ((-ι c0) • (ι ∘ u₁) + ι (2 * b0) • (ι ∘ u₂)) = ι (2 * b0) • (ι ∘ cross3 u₁ u₂) := by
            have := hcr_lin 1 0 (-ι c0) (ι (2 * b0)); simpa using this
          have h0' : ι (2 * b0) • (ι ∘ cross3 u₁ u₂) = 0 := by
            rw [← hl, h0]; ext r; fin_cases r <;> simp [cross3]
          exact (smul_eq_zero.mp h0').elim h2b0_ne hιcr_ne
        · rw [hcr_lin]; simp only [one_mul, zero_mul, sub_zero]
          exact fun h0 => (smul_eq_zero.mp h0).elim h2b0_ne hιcr_ne
        · rw [hev_lin, ha0]; simp
        · rw [hev_lin, ha0]; simp only [map_zero, map_mul, map_ofNat, zero_mul, zero_add]; ring
      ·
        have hιa0 : ι a0 ≠ 0 := fun h0 => ha0 (ι.injective (h0.trans (map_zero ι).symm))
        let poly : Pol L :=
          Pl.C (ι a0) * Pl.X ^ 2 + Pl.C (2 * ι b0) * Pl.X + Pl.C (ι c0)
        have hdeg : poly.degree ≠ 0 := by
          have hnd : poly.natDegree = 2 := by
            have h1 : (Pl.C (ι a0) * Pl.X ^ 2 : Pol L).natDegree = 2 := by
              rw [Pl.natDegree_C_mul hιa0, Pl.natDegree_X_pow]
            have h2 : (Pl.C (2 * ι b0) * Pl.X + Pl.C (ι c0) : Pol L).natDegree ≤ 1 :=
              (Pl.natDegree_add_le _ _).trans (max_le ((Pl.natDegree_C_mul_le _ _).trans (by simp)) (by simp))
            have h3 : poly = Pl.C (ι a0) * Pl.X ^ 2 + (Pl.C (2 * ι b0) * Pl.X + Pl.C (ι c0)) := by ring
            rw [h3, Pl.natDegree_add_eq_left_of_natDegree_lt (by omega), h1]
          intro h0; have := Pl.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0); omega
        obtain ⟨r, hr⟩ := IsAlgClosed.exists_root poly hdeg
        have hr0 : ι a0 * r ^ 2 + 2 * ι b0 * r + ι c0 = 0 := by simpa [poly, Pl.IsRoot] using hr
        set r' : L := -(2 * ι b0) * (ι a0)⁻¹ - r
        have hr'0 : ι a0 * r' ^ 2 + 2 * ι b0 * r' + ι c0 = 0 := by
          have hinv : ι a0 * (ι a0)⁻¹ = 1 := mul_inv_cancel₀ hιa0
          have hr'a : ι a0 * r' = -(2 * ι b0) - ι a0 * r := by
            dsimp only [r']; linear_combination -(2 * ι b0) * hinv
          apply mul_left_cancel₀ hιa0; rw [mul_zero]
          linear_combination ι a0 * hr0 + (ι a0 * r' - ι a0 * r) * hr'a
        have hrr' : r ≠ r' := by
          intro heq
          have h2r : ι a0 * r = -ι b0 := by
            have h1 : 2 * r = -(2 * ι b0) * (ι a0)⁻¹ := by
              have : r + r = -(2 * ι b0) * (ι a0)⁻¹ := by linear_combination heq
              linear_combination this
            have h2L : (2 : L) ≠ 0 := fun h0 => h2ne (ι.injective (by rw [map_ofNat, map_zero]; exact h0))
            apply mul_left_cancel₀ h2L
            calc 2 * (ι a0 * r) = ι a0 * (2 * r) := by ring
              _ = ι a0 * (-(2 * ι b0) * (ι a0)⁻¹) := by rw [h1]
              _ = -(2 * ι b0) * (ι a0 * (ι a0)⁻¹) := by ring
              _ = 2 * (-ι b0) := by rw [mul_inv_cancel₀ hιa0]; ring
          have hdisc0 : ι (a0 * c0 - b0 ^ 2) = 0 := by
            simp only [map_sub, map_mul, map_pow]
            linear_combination ι a0 * hr0 - (ι a0 * r + ι b0) * (by linear_combination h2r : ι a0 * r + ι b0 = 0)
          exact hdisc_ne (ι.injective (hdisc0.trans (map_zero ι).symm))
        refine ⟨r • (ι ∘ u₁) + 1 • (ι ∘ u₂), r' • (ι ∘ u₁) + 1 • (ι ∘ u₂), ?_, ?_, ?_, hdot_lin _ _, hdot_lin _ _, ?_, ?_⟩
        · intro h0
          have hcr := hcr_lin r 1 1 0
          rw [h0] at hcr
          have hcr0 : cross3 (0 : Fin 3 → L) ((1 : L) • (ι ∘ u₁) + (0 : L) • (ι ∘ u₂)) = 0 := by
            ext i; fin_cases i <;> simp [cross3]
          have h1 := hcr0.symm.trans hcr
          simp only [mul_zero, one_mul, zero_sub, neg_smul, one_smul] at h1
          exact hιcr_ne (neg_eq_zero.mp h1.symm)
        · intro h0
          have hcr := hcr_lin r' 1 1 0
          rw [h0] at hcr
          have hcr0 : cross3 (0 : Fin 3 → L) ((1 : L) • (ι ∘ u₁) + (0 : L) • (ι ∘ u₂)) = 0 := by
            ext i; fin_cases i <;> simp [cross3]
          have h1 := hcr0.symm.trans hcr
          simp only [mul_zero, one_mul, zero_sub, neg_smul, one_smul] at h1
          exact hιcr_ne (neg_eq_zero.mp h1.symm)
        · rw [hcr_lin]; simp only [mul_one, one_mul]
          exact fun h0 => (smul_eq_zero.mp h0).elim (sub_ne_zero.mpr hrr') hιcr_ne
        · rw [hev_lin]; simpa using hr0
        · rw [hev_lin]; simpa using hr'0
    rcases htwo_L with ⟨z₁, z₂, hz1, hz2, hcr12', hzy1, hzy2, hGz1, hGz2⟩
    have hφz1 : Mv.eval z₁ (Mv.map ι φ) = 0 := by
      rcases hdvd with ⟨R, rfl⟩; rw [map_mul, map_mul, hGz1, zero_mul]
    have hφz2 : Mv.eval z₂ (Mv.map ι φ) = 0 := by
      rcases hdvd with ⟨R, rfl⟩; rw [map_mul, map_mul, hGz2, zero_mul]
    obtain ⟨l₁, hl₁, c₁, hz1_eq⟩ := (henv y hyK).2 ι z₁ hz1 hzy1 hφz1
    obtain ⟨l₂, hl₂, c₂, hz2_eq⟩ := (henv y hyK).2 ι z₂ hz2 hzy2 hφz2
    have hc1_ne : c₁ ≠ 0 := fun h0 => hz1 (by rw [hz1_eq, h0, zero_smul])
    have hc2_ne : c₂ ≠ 0 := fun h0 => hz2 (by rw [hz2_eq, h0, zero_smul])
    have hl12_ne : l₁ ≠ l₂ := by
      intro heq; subst heq; apply hcr12'
      rw [hz1_eq, hz2_eq, v72, v42, v85, smul_zero, smul_zero]
    have hl_in : ∀ (l : Fin 3 → ZMod p) (z : Fin 3 → L) (c : L), l ∈ v23 K y → c ≠ 0 → z = c • (ι ∘ l) → Mv.eval z (Mv.map ι G) = 0 → l ∈ Cstar_pts ∩ lThru y := by
      intro l z c hl hc hz_eq hGz
      have hl_lt : l ∈ lThru y := v105 K y hl
      have hln : l ∈ pPts p := (mem_filter.mp hl_lt).1
      rw [hz_eq, v05 (hG_hom.map ι)] at hGz
      have hGl_L : Mv.eval (ι ∘ l) (Mv.map ι G) = 0 :=
        (mul_eq_zero.mp hGz).resolve_left (pow_ne_zero 2 hc)
      have hGl : Mv.eval l G = 0 := by
        apply ι.injective
        rw [map_zero, ← hGl_L, Mv.eval_map]
        have h1 := Mv.hom_eval₂ G (Rh.id _) ι l
        rw [Rh.comp_id] at h1
        exact h1
      rw [mem_inter, mem_filter]
      exact ⟨⟨hln, by rw [← hG_quad]; exact hGl⟩, hl_lt⟩
    have hm1 := hl_in l₁ z₁ c₁ hl₁ hc1_ne hz1_eq hGz1
    have hm2 := hl_in l₂ z₂ c₂ hl₂ hc2_ne hz2_eq hGz2
    have hsub : ({l₁, l₂} : Finset (Fin 3 → ZMod p)) ⊆ Cstar_pts ∩ lThru y := by
      intro x hx; rcases mem_insert.mp hx with rfl | hx2
      · exact hm1
      · rw [mem_singleton.mp hx2]; exact hm2
    calc 2 = ({l₁, l₂} : Finset (Fin 3 → ZMod p)).card := (card_pair hl12_ne).symm
      _ ≤ (Cstar_pts ∩ lThru y).card := card_le_card hsub
  have hsum_Cstar : (K ∩ C_pts).card + 2 * (K \ C_pts).card ≤ p + 1 := by
    have hdisj : Set.PairwiseDisjoint (↑K : Set (Fin 3 → ZMod p)) (fun y => Cstar_pts ∩ lThru y) := by
      intro y₁ hy₁ y₂ hy₂ hne
      dsimp only [Fn.onFun]
      rw [disjoint_left]
      intro l hl₁ hl₂
      exact hne (hno_secant_Cstar l (mem_inter.mp hl₁).1 y₁ hy₁ y₂ hy₂
        (mem_filter.mp (mem_inter.mp hl₁).2).2
        (mem_filter.mp (mem_inter.mp hl₂).2).2)
    have hbi_sub : K.biUnion (fun y => Cstar_pts ∩ lThru y) ⊆ Cstar_pts := by
      intro l hl; rcases mem_biUnion.mp hl with ⟨y, _, hy⟩; exact (mem_inter.mp hy).1
    have hsum_le : ∑ y ∈ K, (Cstar_pts ∩ lThru y).card ≤ p + 1 := by
      rw [← card_biUnion hdisj]
      exact (card_le_card hbi_sub).trans hCstar_card
    have hsplit : K = (K ∩ C_pts) ∪ (K \ C_pts) := by
      ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
    have hdisj_KC : Disjoint (K ∩ C_pts) (K \ C_pts) :=
      disjoint_left.mpr (fun x h1 h2 => (mem_sdiff.mp h2).2 (mem_inter.mp h1).2)
    rw [hsplit, sum_union hdisj_KC] at hsum_le
    have h1 : (K ∩ C_pts).card ≤ ∑ y ∈ K ∩ C_pts, (Cstar_pts ∩ lThru y).card := by
      calc (K ∩ C_pts).card = ∑ _y ∈ K ∩ C_pts, 1 := by simp
        _ ≤ _ := sum_le_sum fun y hy =>
            hCstar_y_in y (mem_inter.mp hy).1 (mem_inter.mp hy).2
    have h2 : 2 * (K \ C_pts).card ≤ ∑ y ∈ K \ C_pts, (Cstar_pts ∩ lThru y).card := by
      calc 2 * (K \ C_pts).card = ∑ _y ∈ K \ C_pts, 2 := by simp [mul_comm]
        _ ≤ _ := sum_le_sum fun y hy =>
            hCstar_y_out y (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2
    omega
  have hKC_le : 2 * (K ∩ C_pts).card ≤ p + 1 := by
    have hsymB : ∀ u v : Fin 3 → ZMod p, dot3 v (B.mulVec u) = dot3 u (B.mulVec v) := by
      intro u v
      have hBij : ∀ i j, B j i = B i j := fun i j => by
        simpa [Mx.transpose_apply] using congr_fun (congr_fun hB_symm i) j
      simp only [dot3, Mx.mulVec, dotProduct, Fi.sum_univ_three]
      rw [hBij 0 1, hBij 0 2, hBij 1 2]; ring
    have hQBP_ne : ∀ P ∈ K ∩ C_pts, dot3 Q (B.mulVec P) ≠ 0 := by
      intro P hP hdot0
      have hPK := (mem_inter.mp hP).1
      have hPn := hK.1 P hPK
      have hPBP : dot3 P (B.mulVec P) = 0 := (mem_filter.mp (mem_inter.mp hP).2).2
      have hBP_ne : B.mulVec P ≠ 0 := fun h0 => v00 hPn (by
        rw [← Mx.one_mulVec P, ← hAB, ← Mx.mulVec_mulVec, h0, Mx.mulVec_zero])
      set l := normPt (B.mulVec P)
      obtain ⟨_, c, _, hnorm⟩ := v38 hBP_ne
      have hlC : l ∈ Cstar_pts := by
        rw [mem_filter]; refine ⟨v90 hBP_ne, ?_⟩
        dsimp only [l]; rw [hnorm, Mx.mulVec_smul, v06, v02, Mx.mulVec_mulVec, hAB, Mx.one_mulVec, v45, hPBP, mul_zero, mul_zero]
      have hlP : dot3 l P = 0 := by dsimp only [l]; rw [hnorm, v06, v45, hPBP, mul_zero]
      have hlQ : dot3 l Q = 0 := by dsimp only [l]; rw [hnorm, v06, v45, hdot0, mul_zero]
      have hPQ : P = Q := hno_secant_Cstar l hlC P hPK Q hQK hlP hlQ
      exact hQnotC (hPQ ▸ (mem_inter.mp hP).2)
    let rawPair : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) :=
      fun P => dot3 Q (B.mulVec Q) • P - (2 * dot3 Q (B.mulVec P)) • Q
    let pair : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) := fun P => normPt (rawPair P)
    have hraw_ne : ∀ P ∈ K ∩ C_pts, rawPair P ≠ 0 := by
      intro P hP h0
      have hPK := (mem_inter.mp hP).1
      have hPQ : P ≠ Q := fun h => hQnotC (h ▸ (mem_inter.mp hP).2)
      have hsc : dot3 Q (B.mulVec Q) • P = (2 * dot3 Q (B.mulVec P)) • Q := sub_eq_zero.mp h0
      have hP_eq : P = ((dot3 Q (B.mulVec Q))⁻¹ * (2 * dot3 Q (B.mulVec P))) • Q := by
        calc P = (dot3 Q (B.mulVec Q))⁻¹ • (dot3 Q (B.mulVec Q) • P) := by
              rw [smul_smul, inv_mul_cancel₀ hQBQ_ne, one_smul]
          _ = (dot3 Q (B.mulVec Q))⁻¹ • ((2 * dot3 Q (B.mulVec P)) • Q) := by rw [hsc]
          _ = _ := by rw [smul_smul]
      exact hPQ (v04 (hK.1 P hPK) hQn hP_eq)
    have hpair_maps : ∀ P ∈ K ∩ C_pts, pair P ∈ C_pts \ (K ∩ C_pts) := by
      intro P hP
      have hPK := (mem_inter.mp hP).1
      have hPn := hK.1 P hPK
      have hPBP : dot3 P (B.mulVec P) = 0 := (mem_filter.mp (mem_inter.mp hP).2).2
      have hPQ : P ≠ Q := fun h => hQnotC (h ▸ (mem_inter.mp hP).2)
      obtain ⟨_, c, hc, hnorm⟩ := v38 (hraw_ne P hP)
      have hrawB : dot3 (rawPair P) (B.mulVec (rawPair P)) = 0 := by
        dsimp only [rawPair]
        rw [Mx.mulVec_sub, Mx.mulVec_smul, Mx.mulVec_smul, sub_eq_add_neg, sub_eq_add_neg, v84, show -((2 * dot3 Q (B.mulVec P)) • B.mulVec Q) = (-(2 * dot3 Q (B.mulVec P))) • B.mulVec Q by
            ext i; simp,
          show -((2 * dot3 Q (B.mulVec P)) • Q) = (-(2 * dot3 Q (B.mulVec P))) • Q by ext i; simp,
          v13, v13,
          v06, v06, v06, v06,
          v02, v02, v02, v02,
          hPBP, hsymB Q P]
        ring
      have hpair_C : pair P ∈ C_pts := by
        rw [mem_filter]; refine ⟨v90 (hraw_ne P hP), ?_⟩
        rw [show pair P = normPt (rawPair P) from rfl, hnorm, Mx.mulVec_smul, v06, v02, hrawB, mul_zero, mul_zero]
      rw [mem_sdiff]; refine ⟨hpair_C, fun hmem => ?_⟩
      have hpairK : pair P ∈ K := (mem_inter.mp hmem).1
      have hpair_ne_Q : pair P ≠ Q := fun h => hQnotC (h ▸ hpair_C)
      have hpair_ne_P : pair P ≠ P := by
        intro h
        have h1 : P = c • rawPair P := h.symm.trans hnorm
        have h2 : (1 - c * dot3 Q (B.mulVec Q)) • P = (-(c * (2 * dot3 Q (B.mulVec P)))) • Q := by
          ext i; have := congr_fun h1 i
          simp only [rawPair, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
          linear_combination this
        have hc2 : -(c * (2 * dot3 Q (B.mulVec P))) ≠ 0 :=
          neg_ne_zero.mpr (mul_ne_zero hc (mul_ne_zero h2ne (hQBP_ne P hP)))
        have hQ_eq : Q = ((-(c * (2 * dot3 Q (B.mulVec P))))⁻¹ * (1 - c * dot3 Q (B.mulVec Q))) • P := by
          calc Q = (-(c * (2 * dot3 Q (B.mulVec P))))⁻¹ • ((-(c * (2 * dot3 Q (B.mulVec P)))) • Q) := by
                rw [smul_smul, inv_mul_cancel₀ hc2, one_smul]
            _ = (-(c * (2 * dot3 Q (B.mulVec P))))⁻¹ • ((1 - c * dot3 Q (B.mulVec Q)) • P) := by rw [← h2]
            _ = _ := by rw [smul_smul]
        exact hPQ (v04 hQn hPn hQ_eq).symm
      have hdet0 : det3 Q P (pair P) = 0 := by
        rw [show pair P = normPt (rawPair P) from rfl, hnorm, v76]
        have h0 : det3 Q P (rawPair P) = 0 := by
          dsimp only [rawPair]
          rw [sub_eq_add_neg, v199, v76, v116, mul_zero, zero_add]
          have : -((2 * dot3 Q (B.mulVec P)) • Q) = (-(2 * dot3 Q (B.mulVec P))) • Q := by ext i; simp
          rw [this, v76, v95, mul_zero]
        rw [h0, mul_zero]
      exact hK.2 Q hQK P hPK (pair P) hpairK hPQ.symm hpair_ne_P.symm hpair_ne_Q.symm hdet0
    have hpair_inj : Set.InjOn pair ↑(K ∩ C_pts) := by
      intro P₁ hP₁ P₂ hP₂ heq
      by_contra h12
      have hP1K := (mem_inter.mp hP₁).1
      have hP2K := (mem_inter.mp hP₂).1
      have hP1Q : P₁ ≠ Q := fun h => hQnotC (h ▸ (mem_inter.mp hP₁).2)
      have hP2Q : P₂ ≠ Q := fun h => hQnotC (h ▸ (mem_inter.mp hP₂).2)
      rcases (v44 (hraw_ne P₁ hP₁) (hraw_ne P₂ hP₂)).mp heq with ⟨c, hc, hsc⟩
      have hdet0 : det3 Q P₁ P₂ = 0 := by
        have h1 : det3 Q (rawPair P₁) P₂ = 0 := by
          rw [hsc, v185]
          have : det3 Q (rawPair P₂) P₂ = 0 := by
            rw [v184]
            have h0 : det3 Q P₂ (rawPair P₂) = 0 := by
              dsimp only [rawPair]
              rw [sub_eq_add_neg, v199, v76, v116, mul_zero, zero_add]
              have : -((2 * dot3 Q (B.mulVec P₂)) • Q) = (-(2 * dot3 Q (B.mulVec P₂))) • Q := by ext i; simp
              rw [this, v76, v95, mul_zero]
            rw [h0, neg_zero]
          rw [this, mul_zero]
        have h2 : det3 Q (rawPair P₁) P₂ = dot3 Q (B.mulVec Q) * det3 Q P₁ P₂ := by
          rw [v184, show rawPair P₁ = dot3 Q (B.mulVec Q) • P₁ + (-(2 * dot3 Q (B.mulVec P₁))) • Q by
            ext i; simp [rawPair, sub_eq_add_neg]]
          rw [v199, v76, v76, v95, mul_zero, add_zero, v184]
          ring
        rw [h2] at h1
        exact (mul_eq_zero.mp h1).resolve_left hQBQ_ne
      exact hK.2 Q hQK P₁ hP1K P₂ hP2K hP1Q.symm h12 hP2Q.symm hdet0
    have hcard_le : (K ∩ C_pts).card ≤ (C_pts \ (K ∩ C_pts)).card := by
      calc (K ∩ C_pts).card = ((K ∩ C_pts).image pair).card := (card_image_of_injOn hpair_inj).symm
        _ ≤ (C_pts \ (K ∩ C_pts)).card := card_le_card (image_subset_iff.mpr hpair_maps)
    have hC_split : (C_pts \ (K ∩ C_pts)).card + (K ∩ C_pts).card = C_pts.card :=
      card_sdiff_add_card_eq_card Fs.inter_subset_right
    omega
  have hK_split : (K ∩ C_pts).card + (K \ C_pts).card = K.card :=
    card_inter_add_card_sdiff K C_pts
  omega
theorem voloch_proj_arc_on_conic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {K : Finset (Fin 3 → ZMod p)} (hK : v153 K)
    (hsize : 44 * p + 40 < 45 * K.card) :
    ∃ C : Mv3 (ZMod p), C ≠ 0 ∧ C.IsHomogeneous 2 ∧ ∀ x ∈ K, Mv.eval x C = 0 := by
  have hp_prime : Nat.Prime p := Fact.out
  have hcard_le : K.card ≤ p + 1 := v92 hK.1 hp
  by_cases hoval : K.card = p + 1
  · exact v165 hK.1 hp hoval
  set t : ℕ := p + 2 - K.card
  have ht2 : 2 ≤ t := by omega
  have h45t : 45 * t < p + 50 := by omega
  have hp41 : 41 ≤ p := by omega
  have h2t_lt_p : 4 * t < p := by omega
  have hKbig : 3 * p + 3 < 4 * K.card := by omega
  have henv_size : 2 * t + 2 ≤ K.card := by omega
  obtain ⟨φ, hφ_ne, hφ_hom, henv⟩ := v208 hK.1 hp henv_size
  classical
  set L := AlgebraicClosure (ZMod p)
  set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
  set Φ : Mv3 L := Mv.map ι φ
  have hΦ_ne : Φ ≠ 0 := by
    intro h0; apply hφ_ne; ext m
    have := congr_arg (Mv.coeff m) h0
    rw [Mv.coeff_map, Mv.coeff_zero] at this
    exact ι.injective (this.trans (map_zero ι).symm)
  have hΦ_hom : Φ.IsHomogeneous (2 * t) := hφ_hom.map ι
  set facs := Ufm.factors Φ
  have hfac_irr : ∀ F ∈ facs, Irreducible F := fun F hF =>
    Ufm.irreducible_of_factor F hF
  have hfac_prod : Associated facs.prod Φ :=
    Ufm.factors_prod hΦ_ne
  have hfac_hom_ex : ∀ F ∈ facs, ∃ d : ℕ, 1 ≤ d ∧ F.IsHomogeneous d := by
    intro F hF
    have hF_dvd : F ∣ Φ := (Mu.dvd_prod hF).trans hfac_prod.dvd
    rcases hF_dvd with ⟨Q, hQ⟩
    obtain ⟨d, _, _, hFd, _⟩ := v80 hΦ_hom hΦ_ne hQ
    have hd1 : 1 ≤ d := by
      by_contra hd0
      have hd_eq : d = 0 := by omega
      subst hd_eq
      have hFC : F = Mv.C (F.coeff 0) := by
        ext m; by_cases hm : m = 0
        · subst hm; simp
        · rw [Mv.coeff_C, if_neg (Ne.symm hm)]
          by_contra hne; have := v10 hFd hne
          apply hm; ext i; rcases v03 i with rfl | rfl | rfl <;> simp <;> omega
      apply (hfac_irr F hF).not_isUnit
      rw [hFC]
      exact v156 (fun h0 => (hfac_irr F hF).ne_zero (by rw [hFC, h0, map_zero]))
    exact ⟨d, hd1, hFd⟩
  classical
  let degF : Mv3 L → ℕ := fun F =>
    if h : F ∈ facs then Classical.choose (hfac_hom_ex F h) else 0
  have hdegF_spec : ∀ F (hF : F ∈ facs), 1 ≤ degF F ∧ F.IsHomogeneous (degF F) := by
    intro F hF; simp only [degF, dif_pos hF]; exact Classical.choose_spec (hfac_hom_ex F hF)
  have hsum_deg : (facs.map degF).sum = 2 * t := by
    have hprod_hom : ∀ (M : Multiset (Mv3 L)), (∀ F ∈ M, F.IsHomogeneous (degF F)) → M.prod.IsHomogeneous (M.map degF).sum := by
      intro M
      induction M using Mu.induction_on with
      | empty => intro _; simp [Mv.isHomogeneous_one]
      | cons F M ih =>
        intro hM
        rw [Mu.prod_cons, Mu.map_cons, Mu.sum_cons]
        exact (hM F (Mu.mem_cons_self F M)).mul
          (ih (fun G hG => hM G (Mu.mem_cons_of_mem hG)))
    have hp_hom := hprod_hom facs (fun F hF => (hdegF_spec F hF).2)
    rcases hfac_prod with ⟨u, hu⟩
    rcases v120.mp u.isUnit with ⟨c, hc, huc⟩
    have hΦ_hom2 : Φ.IsHomogeneous (facs.map degF).sum := by
      rw [← hu, huc, mul_comm]; exact v07 c hp_hom
    obtain ⟨m, hm⟩ := Mv.support_nonempty.mpr hΦ_ne
    have h1 := v10 hΦ_hom (Mv.mem_support_iff.mp hm)
    have h2 := v10 hΦ_hom2 (Mv.mem_support_iff.mp hm)
    omega
  by_cases hconic_fac : ∃ F ∈ facs, degF F = 2 ∧ ∃ (c : L) (G : Mv3 (ZMod p)), c ≠ 0 ∧ G ≠ 0 ∧ G.IsHomogeneous 2 ∧ F = Mv.C c * Mv.map ι G
  · rcases hconic_fac with ⟨F, hF_mem, _, c, G, hc, hG_ne, hG_hom, hFG⟩
    have hG_irr : Irreducible (Mv.map ι G) := by
      have hF_irr := hfac_irr F hF_mem
      rw [hFG] at hF_irr
      exact (associated_unit_mul_left _ _ (v156 hc)).irreducible_iff.mp hF_irr
    have hG_dvd_φ : G ∣ φ := by
      have hF_dvd_Φ : F ∣ Φ := (Mu.dvd_prod hF_mem).trans hfac_prod.dvd
      rcases hF_dvd_Φ with ⟨Q, hQ⟩
      set Q' := Mv.C c * Q
      have hQ'_eq : Mv.map ι φ = Mv.map ι G * Q' := by
        dsimp only [Q']; change Φ = Mv.map ι G * (Mv.C c * Q); rw [hQ, hFG]; ring
      have hQ'_frob : Mv.map (frobenius L p) Q' = Q' := by
        have hmap_frob : ∀ P : Mv3 (ZMod p), Mv.map (frobenius L p) (Mv.map ι P) = Mv.map ι P := by
          intro P; ext m
          rw [Mv.coeff_map, Mv.coeff_map, frobenius_def, ← map_pow, ZMod.pow_card]
        have h1 := congr_arg (Mv.map (frobenius L p)) hQ'_eq
        rw [map_mul, hmap_frob φ, hmap_frob G, hQ'_eq] at h1
        have hG_map_ne : Mv.map ι G ≠ 0 := hG_irr.ne_zero
        exact mul_left_cancel₀ hG_map_ne h1.symm
      have hcoeff_fix : ∀ m : E3, (Q'.coeff m) ^ p = Q'.coeff m := by
        intro m; have := congr_arg (Mv.coeff m) hQ'_frob
        rwa [Mv.coeff_map, frobenius_def] at this
      let R : Mv3 (ZMod p) :=
        ∑ m ∈ Q'.support, Mv.monomial m (Classical.choose (v31 (hcoeff_fix m)))
      have hR_map : Mv.map ι R = Q' := by
        ext m; rw [Mv.coeff_map]
        by_cases hm : m ∈ Q'.support
        · dsimp only [R]; rw [Mv.coeff_sum, sum_eq_single m]
          · rw [Mv.coeff_monomial, if_pos rfl]
            exact Classical.choose_spec (v31 (hcoeff_fix m))
          · intro n _ hnm; rw [Mv.coeff_monomial, if_neg hnm]
          · intro h; exact absurd hm h
        · dsimp only [R]; rw [Mv.coeff_sum, sum_eq_zero, map_zero]
          · exact (Mv.notMem_support_iff.mp hm).symm
          · intro n hn; rw [Mv.coeff_monomial, if_neg (fun (h : n = m) => hm (h ▸ hn))]
      refine ⟨R, ?_⟩
      ext m; apply ι.injective
      rw [← Mv.coeff_map, ← Mv.coeff_map, map_mul, hR_map, hQ'_eq]
    exact v59 hp hK.1 hKbig henv hG_hom hG_irr hG_dvd_φ
  exfalso
  push Not at hconic_fac
  have hfac_bound : ∀ F ∈ facs, 5 * ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)).card ≤ degF F * (2 * p + 10 * degF F - 20) := by
    intro F hF_mem
    have hF_irr := hfac_irr F hF_mem
    obtain ⟨hd1, hF_hom⟩ := hdegF_spec F hF_mem
    have hd_le_2t : degF F ≤ 2 * t := by
      rw [← hsum_deg]
      exact Mu.le_sum_of_mem (Mu.mem_map_of_mem degF hF_mem)
    rcases v150 hF_hom hF_irr with ⟨c, G, hc, hG_ne, hG_hom, hFG⟩ | hbez
    ·
      by_cases hd3 : 3 ≤ degF F
      · exact v173 (by omega) hF_hom hF_irr hd3 (by omega)
      · have hd12 : degF F = 1 ∨ degF F = 2 := by omega
        rcases hd12 with hd_eq | hd_eq
        ·
          exfalso
          have hG_dvd_φ : G ∣ φ := by
            have hF_dvd_Φ : F ∣ Φ := (Mu.dvd_prod hF_mem).trans hfac_prod.dvd
            rcases hF_dvd_Φ with ⟨Q, hQ⟩
            set Q' := Mv.C c * Q
            have hQ'_eq : Mv.map ι φ = Mv.map ι G * Q' := by
              dsimp only [Q']; change Φ = Mv.map ι G * (Mv.C c * Q); rw [hQ, hFG]; ring
            have hQ'_frob : Mv.map (frobenius L p) Q' = Q' := by
              have hmap_frob : ∀ P : Mv3 (ZMod p), Mv.map (frobenius L p) (Mv.map ι P) = Mv.map ι P := by
                intro P; ext m
                rw [Mv.coeff_map, Mv.coeff_map, frobenius_def, ← map_pow, ZMod.pow_card]
              have h1 := congr_arg (Mv.map (frobenius L p)) hQ'_eq
              rw [map_mul, hmap_frob φ, hmap_frob G, hQ'_eq] at h1
              have hG_map_ne : Mv.map ι G ≠ 0 := by
                intro h0; apply hG_ne; ext m
                have := congr_arg (Mv.coeff m) h0
                rw [Mv.coeff_map, Mv.coeff_zero] at this
                exact ι.injective (this.trans (map_zero ι).symm)
              exact mul_left_cancel₀ hG_map_ne h1.symm
            have hcoeff_fix : ∀ m : E3, (Q'.coeff m) ^ p = Q'.coeff m := by
              intro m; have := congr_arg (Mv.coeff m) hQ'_frob
              rwa [Mv.coeff_map, frobenius_def] at this
            let R : Mv3 (ZMod p) :=
              ∑ m ∈ Q'.support, Mv.monomial m (Classical.choose (v31 (hcoeff_fix m)))
            have hR_map : Mv.map ι R = Q' := by
              ext m; rw [Mv.coeff_map]
              by_cases hm : m ∈ Q'.support
              · dsimp only [R]; rw [Mv.coeff_sum, sum_eq_single m]
                · rw [Mv.coeff_monomial, if_pos rfl]
                  exact Classical.choose_spec (v31 (hcoeff_fix m))
                · intro n _ hnm; rw [Mv.coeff_monomial, if_neg hnm]
                · intro h; exact absurd hm h
              · dsimp only [R]; rw [Mv.coeff_sum, sum_eq_zero, map_zero]
                · exact (Mv.notMem_support_iff.mp hm).symm
                · intro n hn; rw [Mv.coeff_monomial, if_neg (fun (h : n = m) => hm (h ▸ hn))]
            refine ⟨R, ?_⟩
            ext m; apply ι.injective
            rw [← Mv.coeff_map, ← Mv.coeff_map, map_mul, hR_map, hQ'_eq]
          rw [hd_eq] at hG_hom
          exact v98 hK (by omega) henv hG_ne hG_hom hG_dvd_φ
        ·
          exfalso
          rw [hd_eq] at hG_hom
          exact hconic_fac F hF_mem hd_eq c G hc hG_ne hG_hom hFG
    ·
      have h5d : 5 * (degF F * degF F) ≤ degF F * (2 * p + 10 * degF F - 20) := by
        have : 5 * degF F ≤ 2 * p + 10 * degF F - 20 := by omega
        calc 5 * (degF F * degF F) = degF F * (5 * degF F) := by ring
          _ ≤ degF F * (2 * p + 10 * degF F - 20) := Nat.mul_le_mul_left _ this
      exact (Nat.mul_le_mul_left 5 hbez).trans h5d
  set S_Phi : Finset (Fin 3 → ZMod p) :=
    (pPts p).filter (fun P => Mv.eval (ι ∘ P) Φ = 0)
  have hlower : t * K.card ≤ S_Phi.card := by
    have hdisj : Set.PairwiseDisjoint (↑K : Set (Fin 3 → ZMod p)) (fun y => v23 K y) := by
      intro y₁ hy₁ y₂ hy₂ hne
      dsimp only [Fn.onFun]
      rw [disjoint_left]; intro l hl₁ hl₂
      exact (mem_filter.mp hl₁).2 y₂ hy₂ hne.symm (mem_filter.mp (mem_filter.mp hl₂).1).2
    have hsub : K.biUnion (fun y => v23 K y) ⊆ S_Phi := by
      intro l hl
      rcases mem_biUnion.mp hl with ⟨y, hyK, hly⟩
      rw [mem_filter]
      refine ⟨(mem_filter.mp (v105 K y hly)).1, ?_⟩
      have hφl : Mv.eval l φ = 0 := (henv y hyK).1 l hly
      have : Mv.eval (ι ∘ l) Φ = ι (Mv.eval l φ) := by
        dsimp only [Φ]; rw [Mv.eval_map]
        exact (Mv.hom_eval₂ φ (Rh.id _) ι l).symm
      rw [this, hφl, map_zero]
    have hcard_tan : ∀ y ∈ K, (v23 K y).card = t := by
      intro y hyK; have := v26 hK.1 hyK; omega
    calc t * K.card = ∑ _y ∈ K, t := by simp [mul_comm]
      _ = ∑ y ∈ K, (v23 K y).card := sum_congr rfl (fun y hy => (hcard_tan y hy).symm)
      _ = (K.biUnion (fun y => v23 K y)).card := (card_biUnion hdisj).symm
      _ ≤ S_Phi.card := card_le_card hsub
  have hcover : S_Phi.card ≤ (facs.map (fun F =>
      ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)).card)).sum := by
    have hprod_eval : ∀ P ∈ S_Phi, ∃ F ∈ facs, Mv.eval (ι ∘ P) F = 0 := by
      intro P hP
      have hΦP : Mv.eval (ι ∘ P) Φ = 0 := (mem_filter.mp hP).2
      rcases hfac_prod with ⟨u, hu⟩
      rcases v120.mp u.isUnit with ⟨c, hc, huc⟩
      have h0 : Mv.eval (ι ∘ P) facs.prod = 0 := by
        rw [← hu, huc, map_mul, Mv.eval_C] at hΦP
        exact (mul_eq_zero.mp hΦP).resolve_right hc
      rw [map_multiset_prod, Mu.prod_eq_zero_iff] at h0
      rcases Mu.mem_map.mp h0 with ⟨F, hF, hFP⟩
      exact ⟨F, hF, hFP⟩
    have hind : ∀ (M : Multiset (Mv3 L)), (S_Phi.filter (fun P => ∃ F ∈ M, Mv.eval (ι ∘ P) F = 0)).card ≤ (M.map (fun F => ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)).card)).sum := by
      intro M
      induction M using Mu.induction_on with
      | empty => simp
      | cons F M ih =>
        rw [Mu.map_cons, Mu.sum_cons]
        have hsub : S_Phi.filter (fun P => ∃ G ∈ F ::ₘ M, Mv.eval (ι ∘ P) G = 0) ⊆
            ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)) ∪
            (S_Phi.filter (fun P => ∃ G ∈ M, Mv.eval (ι ∘ P) G = 0)) := by
          intro P hP
          rw [mem_filter] at hP
          rcases hP.2 with ⟨G, hG, hGP⟩
          rw [mem_union]
          rcases Mu.mem_cons.mp hG with rfl | hGM
          · left; exact mem_filter.mpr ⟨(mem_filter.mp hP.1).1, hGP⟩
          · right; exact mem_filter.mpr ⟨hP.1, ⟨G, hGM, hGP⟩⟩
        exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ih _))
    have hfilt : S_Phi.filter (fun P => ∃ F ∈ facs, Mv.eval (ι ∘ P) F = 0) = S_Phi :=
      filter_true_of_mem hprod_eval
    rw [← hfilt]; exact hind facs
  have h5_upper : 5 * S_Phi.card ≤ 2 * t * (2 * p + 10 * (2 * t) - 20) := by
    have h1 : 5 * (facs.map (fun F =>
          ((pPts p).filter (fun P => Mv.eval (ι ∘ P) F = 0)).card)).sum ≤
        (facs.map (fun F => degF F * (2 * p + 10 * degF F - 20))).sum := by
      have hmul_sum : ∀ (M : Multiset ℕ), 5 * M.sum = (M.map (fun x => 5 * x)).sum := by
        intro M; induction M using Mu.induction_on with
        | empty => simp
        | cons a M ih => rw [Mu.sum_cons, Mu.map_cons, Mu.sum_cons, mul_add, ih]
      rw [hmul_sum, Mu.map_map]
      have hms_le : ∀ (M : Multiset (Mv3 L)) (f g : Mv3 L → ℕ), (∀ x ∈ M, f x ≤ g x) → (M.map f).sum ≤ (M.map g).sum := by
        intro M f g hfg
        induction M using Mu.induction_on with
        | empty => simp
        | cons a M ih =>
          rw [Mu.map_cons, Mu.map_cons, Mu.sum_cons, Mu.sum_cons]
          exact Nat.add_le_add (hfg a (Mu.mem_cons_self a M))
            (ih (fun x hx => hfg x (Mu.mem_cons_of_mem hx)))
      exact hms_le facs _ _ (fun F hF => hfac_bound F hF)
    have h2 : (facs.map (fun F => degF F * (2 * p + 10 * degF F - 20))).sum ≤ 2 * t * (2 * p + 10 * (2 * t) - 20) := by
      have hterm : ∀ F ∈ facs, degF F * (2 * p + 10 * degF F - 20) ≤ degF F * (2 * p + 10 * (2 * t) - 20) := by
        intro F hF
        have hle : degF F ≤ 2 * t := by
          rw [← hsum_deg]; exact Mu.le_sum_of_mem (Mu.mem_map_of_mem degF hF)
        exact Nat.mul_le_mul_left _ (by omega)
      have hms_le : ∀ (M : Multiset (Mv3 L)) (f g : Mv3 L → ℕ), (∀ x ∈ M, f x ≤ g x) → (M.map f).sum ≤ (M.map g).sum := by
        intro M f g hfg
        induction M using Mu.induction_on with
        | empty => simp
        | cons a M ih =>
          rw [Mu.map_cons, Mu.map_cons, Mu.sum_cons, Mu.sum_cons]
          exact Nat.add_le_add (hfg a (Mu.mem_cons_self a M))
            (ih (fun x hx => hfg x (Mu.mem_cons_of_mem hx)))
      have hfac_const : ∀ (M : Multiset ℕ) (c : ℕ), (M.map (fun x => x * c)).sum = M.sum * c := by
        intro M c; induction M using Mu.induction_on with
        | empty => simp
        | cons a M ih => rw [Mu.map_cons, Mu.sum_cons, Mu.sum_cons, add_mul, ih]
      calc (facs.map (fun F => degF F * (2 * p + 10 * degF F - 20))).sum
          ≤ (facs.map (fun F => degF F * (2 * p + 10 * (2 * t) - 20))).sum := hms_le facs _ _ hterm
        _ = ((facs.map degF).map (fun x => x * (2 * p + 10 * (2 * t) - 20))).sum := by
            rw [Mu.map_map]; rfl
        _ = (facs.map degF).sum * (2 * p + 10 * (2 * t) - 20) := hfac_const _ _
        _ = 2 * t * (2 * p + 10 * (2 * t) - 20) := by rw [hsum_deg]
    exact (Nat.mul_le_mul_left 5 hcover).trans (h1.trans h2)
  have h5_lower : 5 * (t * K.card) ≤ 5 * S_Phi.card := Nat.mul_le_mul_left 5 hlower
  have hineq : 5 * (t * K.card) ≤ 2 * t * (2 * p + 10 * (2 * t) - 20) := h5_lower.trans h5_upper
  have hK_eq : K.card = p + 2 - t := by omega
  have hcancel : t * (5 * K.card) ≤ t * (2 * (2 * p + 10 * (2 * t) - 20)) := by
    calc t * (5 * K.card) = 5 * (t * K.card) := by ring
      _ ≤ 2 * t * (2 * p + 10 * (2 * t) - 20) := hineq
      _ = t * (2 * (2 * p + 10 * (2 * t) - 20)) := by ring
  have hfinal := Nat.le_of_mul_le_mul_left hcancel (by omega : 0 < t)
  omega
lemma affine_conic_of_proj_conic {p : ℕ} [Fact p.Prime] {A : Finset (Fin 2 → ZMod p)}
    {C : Mv3 (ZMod p)} (hC_ne : C ≠ 0) (hC_hom : C.IsHomogeneous 2)
    (hC_van : ∀ a ∈ A, Mv.eval (aff2P a) C = 0) :
    ∃ F : Mv2 (ZMod p), F ≠ 0 ∧ F.totalDegree ≤ 2 ∧ ∀ a ∈ A, Mv.eval a F = 0 := by
  let evA : Mv3 (ZMod p) →ₐ[ZMod p] Mv2 (ZMod p) :=
    Mv.aeval ![1, Mv.X 0, Mv.X 1]
  let F : Mv2 (ZMod p) := evA C
  have hF_eval : ∀ (P : Mv3 (ZMod p)) (a : Fin 2 → ZMod p), Mv.eval a (evA P) = Mv.eval (aff2P a) P := by
    intro P a
    induction P using Mv.induction_on with
    | C c => simp [evA]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]; congr 1
      rcases v03 i with rfl | rfl | rfl <;> simp [evA, aff2P]
  have hF_deg : F.totalDegree ≤ 2 := by
    unfold Mv.totalDegree
    apply Fs.sup_le; intro m hm
    have hcoeff_ne : F.coeff m ≠ 0 := Mv.mem_support_iff.mp hm
    by_contra hgt
    push Not at hgt
    apply hcoeff_ne
    dsimp only [F]
    rw [Mv.as_sum C, map_sum, Mv.coeff_sum]
    apply sum_eq_zero; intro n hn
    have hnd := v10 hC_hom (Mv.mem_support_iff.mp hn)
    dsimp only [evA]
    rw [Mv.monomial_eq, map_mul, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
    simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, one_mul]
    let n2 : Fin 2 →₀ ℕ := Fu.single 0 (n 1) + Fu.single 1 (n 2)
    have hmon : Mv.C (C.coeff n) * (Mv.X 0 ^ n 1 * Mv.X 1 ^ n 2) = Mv.monomial n2 (C.coeff n) := by
      rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_two]
      simp [n2]
    rw [hmon, Mv.coeff_monomial, if_neg]
    intro heq
    rw [← heq] at hgt
    have hdeg_n2 : n2.sum (fun _ e => e) = n 1 + n 2 := by
      rw [Fu.sum_fintype _ _ (fun _ => rfl), Fi.sum_univ_two]; simp [n2]
    omega
  have hF_ne : F ≠ 0 := by
    intro hF0
    apply hC_ne
    ext m
    rw [Mv.coeff_zero]
    by_cases hm2 : m 0 + m 1 + m 2 = 2
    · let m2 : Fin 2 →₀ ℕ := Fu.single 0 (m 1) + Fu.single 1 (m 2)
      have hcoeff : F.coeff m2 = C.coeff m := by
        dsimp only [F]
        conv_lhs => rw [Mv.as_sum C, map_sum, Mv.coeff_sum]
        rw [sum_eq_single m]
        · dsimp only [evA]
          rw [Mv.monomial_eq, map_mul, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
          simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, one_mul]
          have hmon : Mv.C (C.coeff m) * (Mv.X 0 ^ m 1 * Mv.X 1 ^ m 2) = Mv.monomial m2 (C.coeff m) := by
            rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_two]
            simp [m2]
          rw [hmon, Mv.coeff_monomial, if_pos rfl]
        · intro n hn hnm
          have hnd := v10 hC_hom (Mv.mem_support_iff.mp hn)
          dsimp only [evA]
          rw [Mv.monomial_eq, map_mul, Mv.aeval_C, Mv.algebraMap_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), map_prod, Fi.prod_univ_three]
          simp only [map_pow, Mv.aeval_X, Mx.cons_val_zero, Mx.cons_val_one, Mx.cons_val_two, Mx.tail_cons, Mx.head_cons, one_pow, one_mul]
          let n2 : Fin 2 →₀ ℕ := Fu.single 0 (n 1) + Fu.single 1 (n 2)
          have hmon : Mv.C (C.coeff n) * (Mv.X 0 ^ n 1 * Mv.X 1 ^ n 2) = Mv.monomial n2 (C.coeff n) := by
            rw [Mv.monomial_eq, Fu.prod_fintype _ _ (fun _ => pow_zero _), Fi.prod_univ_two]
            simp [n2]
          rw [hmon, Mv.coeff_monomial, if_neg]
          intro heq; apply hnm
          have h1 : n 1 = m 1 := by have := congr_arg (fun f : Fin 2 →₀ ℕ => f 0) heq; simpa [n2, m2] using this
          have h2 : n 2 = m 2 := by have := congr_arg (fun f : Fin 2 →₀ ℕ => f 1) heq; simpa [n2, m2] using this
          ext i; rcases v03 i with rfl | rfl | rfl <;> omega
        · intro h; rw [Mv.notMem_support_iff.mp h, map_zero, map_zero, Mv.coeff_zero]
      rw [← hcoeff, hF0, Mv.coeff_zero]
    · by_contra hne; exact hm2 (v10 hC_hom hne)
  exact ⟨F, hF_ne, hF_deg, fun a ha => by rw [hF_eval C a]; exact hC_van a ha⟩
end VolochAssembly
end Green68Voloch

/-- Final solution to `OMA.R_Green68_green_68_variants_voloch_R1.H1`. -/
theorem OMA.solution : OMA.R_Green68_green_68_variants_voloch_R1.H1 := by
  intro p _ hp A harc hsize S hSA _
  have hnat_size : 44 * p + 40 < 45 * A.card := by
    have hreal : (44 * p + 40 : ℝ) < (45 * A.card : ℝ) := by
      linarith
    exact_mod_cast hreal
  set K₀ : Finset (Fin 3 → ZMod p) := A.image Green68Voloch.aff2P
  have hK₀_arc : Green68Voloch.IsProjArc K₀ :=
    Green68Voloch.isProjArc_of_meetsLinesInAtMost harc
  have hK₀_card : K₀.card = A.card :=
    Finset.card_image_of_injective A Green68Voloch.aff2P_injective
  obtain ⟨K, hK₀K, hK_comp⟩ := Green68Voloch.exists_completeArc_superset hK₀_arc
  have hK_size : 44 * p + 40 < 45 * K.card := by
    have hle : A.card ≤ K.card := by rw [← hK₀_card]; exact Finset.card_le_card hK₀K
    omega
  obtain ⟨C, hC_ne, hC_hom, hC_van⟩ :=
    Green68Voloch.voloch_proj_arc_on_conic hp hK_comp hK_size
  obtain ⟨F, hF_ne, hF_deg, hF_van⟩ :=
    Green68Voloch.affine_conic_of_proj_conic hC_ne hC_hom
      (fun a ha => hC_van (Green68Voloch.aff2P a) (hK₀K (Finset.mem_image_of_mem _ ha)))
  exact ⟨F, hF_ne, hF_deg, fun a ha => hF_van a (hSA ha)⟩
