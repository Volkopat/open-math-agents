import OMAStatements.S_mo_443664

/-!
Credited port of @connoranderson's complete public proof, linked from merged statement
PR #23760 and desk DONE note #109202, pinned at:
https://github.com/connoranderson/open-math-agents/blob/4d9bbd36051eb80aed01bf8ef6218dd85c06d7d3/proofs/mo-443664.lean
All mathematical code is retained unchanged. This integrates prior proof work,
not a claim of a new mathematical discovery. David Roberson posed the question at
https://mathoverflow.net/questions/443664 (CC BY-SA 4.0).
-/

namespace OMA.S_mo_443664
open scoped ComplexOrder
open Matrix Finset

lemma finite_bochner {G : Type} [Fintype G] [AddCommGroup G] (f : G → ℂ) :
    (Matrix.of (fun x y : G => f (x-y))).PosSemidef ↔
      ∀ χ : AddChar G ℂ, 0 ≤ ∑ t : G, star (χ t) * f t := by
  classical
  let M : Matrix G G ℂ := Matrix.of (fun x y => f (x-y))
  let R : Matrix G (AddChar G ℂ) ℂ := Matrix.of (fun x χ => χ x)
  let w (χ : AddChar G ℂ) := ∑ t : G, star (χ t) * f t
  have hsub (χ : AddChar G ℂ) (x t : G) : χ (x-t) = χ x * star (χ t) := by
    rw [sub_eq_add_neg, χ.map_add_eq_mul, χ.map_neg_eq_conj]
    rfl
  have he (x : G) (χ : AddChar G ℂ) : (M * R) x χ = χ x * w χ := by
    change (∑ y, f (x-y)*χ y) = χ x * ∑ t, star (χ t)*f t
    rw [← (Equiv.subLeft x).sum_comp (fun y => f (x-y)*χ y), Finset.mul_sum]
    apply sum_congr rfl
    intro t _
    simp only [Equiv.subLeft_apply, sub_sub_cancel, hsub]
    ring
  have heq : M*R = R*diagonal w := by
    ext x χ
    rw [he, mul_diagonal]
    rfl
  have hunit : R*Rᴴ = (Fintype.card G : ℝ) • (1 : Matrix G G ℂ) := by
    ext x y
    calc _ = ∑ χ : AddChar G ℂ, χ (x-y) := by
              simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, R, Matrix.of_apply, hsub]
         _ = _ := by
              rw [AddChar.sum_apply_eq_ite, Matrix.smul_apply, Matrix.one_apply]
              by_cases h : x=y <;> simp [h,sub_eq_zero,Complex.real_smul]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change M.PosSemidef ↔ ∀ χ, 0 ≤ w χ
  constructor
  · intro h χ
    have hp := h.dotProduct_mulVec_nonneg (χ : G → ℂ)
    have hv : star (χ : G → ℂ) ⬝ᵥ (M *ᵥ (χ : G → ℂ)) = (Fintype.card G : ℂ)*w χ := by
      change (∑ x, star (χ x) * (M*R) x χ) = _
      simp_rw [he, ← mul_assoc]
      have hnorm (x : G) : star (χ x)*χ x = 1 := by
        rw [mul_comm, ← hsub χ x x, sub_self, χ.map_zero_eq_one]
      simp only [hnorm, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hv] at hp
    have hinv : 0 ≤ (Fintype.card G : ℂ)⁻¹ := by
      change 0 ≤ ((Fintype.card G : ℝ) : ℂ)⁻¹
      rw [← Complex.ofReal_inv, Complex.zero_le_real]
      positivity
    simpa [← mul_assoc, Fintype.card_ne_zero] using mul_nonneg hinv hp
  · intro h
    have hp := (Matrix.posSemidef_diagonal_iff.mpr h).mul_mul_conjTranspose_same R
    rw [← heq, Matrix.mul_assoc, hunit, Matrix.mul_smul, Matrix.mul_one] at hp
    simpa [smul_smul, hcard] using hp.smul (show 0 ≤ (Fintype.card G : ℝ)⁻¹ by positivity)

end OMA.S_mo_443664

namespace OMA.S_mo_443664
open scoped ComplexOrder

private def paired {G : Type} [AddCommGroup G] (χ ψ : AddChar G ℂ) : AddChar (G×G) ℂ where
  toFun x := χ x.1 * star (ψ x.2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by intro x y; simp [AddChar.map_add_eq_mul]; ring

private def secondStar {G : Type} [AddCommGroup G] (η : AddChar (G×G) ℂ) : AddChar G ℂ where
  toFun b := star (η (0,b))
  map_zero_eq_one' := by simp [show ((0,0) : G×G)=0 from rfl]
  map_add_eq_mul' := by
    intro x y
    rw [show ((0,x+y) : G×G) = (0,x)+(0,y) by simp,AddChar.map_add_eq_mul,star_mul,mul_comm]

lemma dual_nonneg_iff {G : Type} [Fintype G] [AddCommGroup G] (M : Matrix G G ℂ) :
    (∀ χ ψ, 0 ≤ dual M χ ψ) ↔ ∀ η : AddChar (G×G) ℂ, 0 ≤ ∑ t : G×G, star (η t)*M t.1 t.2 := by
  classical
  have hc : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hscale (z : ℂ) : 0 ≤ (Fintype.card G : ℂ)⁻¹ * z ↔ 0 ≤ z := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    simp [Complex.nonneg_iff,Complex.mul_re,Complex.mul_im,hc.ne',
      mul_nonneg_iff_of_pos_left (inv_pos.mpr hc),eq_comm (a := (0:ℝ))]
  have hsum (χ ψ : AddChar G ℂ) : (∑ t : G×G, star (paired χ ψ t)*M t.1 t.2) =
      ∑ a, ∑ b, star (χ a)*M a b*ψ b := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    change star (χ a * star (ψ b)) * _ = _
    rw [star_mul,star_star]; ring
  constructor
  · intro H η
    let χ := η.compAddMonoidHom (AddMonoidHom.inl G G)
    let ψ := secondStar η
    have he : paired χ ψ = η := by
      ext ⟨a,b⟩
      change η (a,0) * star (star (η (0,b))) = η (a,b)
      rw [star_star,← AddChar.map_add_eq_mul]; simp
    rw [← he,hsum]
    exact (hscale _).mp (H χ ψ)
  · intro H χ ψ
    exact (hscale _).mpr (hsum χ ψ ▸ H (paired χ ψ))

end OMA.S_mo_443664

namespace OMA.S_mo_443664

open Finset

private lemma invert_sums {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G] (f : G → ℂ) :
    (∀ χ : AddChar G ℂ, ∑ a, f a * χ a = 1) ↔ ∀ a, f a = if a = 0 then 1 else 0 := by
  classical
  constructor
  · intro H b
    have h : (∑ χ : AddChar G ℂ, χ (-b)) = f b * Fintype.card G := calc
      _ = ∑ χ : AddChar G ℂ, (∑ a, f a*χ a)*χ (-b) := by simp [H]
      _ = ∑ a, ∑ χ : AddChar G ℂ, f a * χ (a-b) := by
        simp only [Finset.sum_mul,sub_eq_add_neg,AddChar.map_add_eq_mul,mul_assoc]
        rw [sum_comm]
      _ = f b * Fintype.card G := by
        simp_rw [← mul_sum,AddChar.sum_apply_eq_ite,sub_eq_zero]
        simp [mul_ite]
    rw [AddChar.sum_apply_eq_ite] at h
    by_cases hb : b=0 <;> simpa [hb] using h
  · intro h χ
    simp [h,ite_mul]

private lemma sum3swap {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℂ) : (∑ c, ∑ a, ∑ b, f a b c) = ∑ a, ∑ b, ∑ c, f a b c := by
  rw [sum_comm]
  exact sum_congr rfl (fun _ _ => sum_comm)

private lemma char_star {G : Type} [Fintype G] [AddCommGroup G] (χ : AddChar G ℂ) (x : G) :
    star (χ x) = χ (-x) := (AddChar.map_neg_eq_conj χ x).symm

private lemma dual_row {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (M : Matrix G G ℂ) (χ : AddChar G ℂ) : (∑ ψ, dual M χ ψ) = ∑ a, M a 0 * χ (-a) := by
  classical
  unfold dual
  rw [← Finset.mul_sum,sum3swap (fun (a b : G) (ψ : AddChar G ℂ) => star (χ a)*M a b*ψ b)]
  simp_rw [← mul_sum,AddChar.sum_apply_eq_ite]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',mem_univ,if_true]
  rw [← sum_mul]
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  simp [char_star,mul_comm]

private lemma dual_col {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (M : Matrix G G ℂ) (ψ : AddChar G ℂ) : (∑ χ, dual M χ ψ) = ∑ b, M 0 b * ψ b := by
  classical
  unfold dual
  rw [← Finset.mul_sum,sum3swap (fun (a b : G) (χ : AddChar G ℂ) => star (χ a)*M a b*ψ b)]
  simp_rw [← Finset.sum_mul,char_star,AddChar.sum_apply_eq_ite]
  simp only [neg_eq_zero,ite_mul,zero_mul]
  rw [sum_comm]
  simp only [Finset.sum_ite_eq',mem_univ,if_true]
  simp_rw [mul_assoc]
  rw [← mul_sum]
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma dual_margins {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G] (M : Matrix G G ℂ) :
    Margins (dual M) ↔ (∀ a, M a 0 = if a=0 then 1 else 0) ∧
      ∀ b, M 0 b = if b=0 then 1 else 0 := by
  constructor
  · intro h
    constructor
    · apply (invert_sums (fun a => M a 0)).mp
      intro χ
      simpa [dual_row] using h.1 (-χ)
    · apply (invert_sums (fun b => M 0 b)).mp
      intro ψ
      simpa [dual_col] using h.2 ψ
  · intro h
    constructor
    · intro χ
      rw [dual_row]
      exact (invert_sums (fun a => M a 0)).mpr h.1 (-χ)
    · intro ψ
      rw [dual_col]
      exact (invert_sums (fun b => M 0 b)).mpr h.2 ψ

end OMA.S_mo_443664

namespace OMA.S_mo_443664

open Matrix Finset
open scoped ComplexOrder

private lemma perm_doubly {G : Type} [Fintype G] [DecidableEq G] (σ : Equiv.Perm G) :
    Doubly (permMatrix σ) := by
  classical
  refine ⟨⟨fun i => ?_,fun j => ?_⟩,?_⟩
  · simp only [permMatrix,←σ.symm_apply_eq]
    simp
  · simp [permMatrix]
  · intro i j
    simp only [permMatrix]
    split <;> norm_num

private lemma equal_columns {ι : Type} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℂ)
    (h : K.PosSemidef) (p q : ι) (hpp : K p p=1) (hqq : K q q=1)
    (hpq : K p q=1) (i : ι) : K i p=K i q := by
  have hqp : K q p=1 := by rw [←h.1.apply q p,hpq,star_one]
  let v : ι → ℂ := Pi.single p 1 - Pi.single q 1
  have hstar : star v = v := by
    ext j
    simp only [v,Pi.star_apply,Pi.sub_apply,star_sub]
    by_cases hp : j=p <;> by_cases hq : j=q <;> simp [Pi.single_apply,hp,hq]
  have h0 : star v ⬝ᵥ K *ᵥ v = 0 := by
    rw [hstar]
    simp only [v,Matrix.mulVec_sub,Matrix.mulVec_single_one,sub_dotProduct,
      single_one_dotProduct,Pi.sub_apply,Matrix.col_apply,hpp,hqq,hpq,hqp,sub_self]
  have eq := congrFun ((h.dotProduct_mulVec_zero_iff v).mp h0) i
  simpa [v,Matrix.mulVec_sub,Matrix.mulVec_single_one,sub_eq_zero] using eq

lemma perm_class {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G] (σ : Equiv.Perm G) :
    (((∀ a, permMatrix σ a 0 = if a=0 then 1 else 0) ∧
        (∀ b, permMatrix σ 0 b = if b=0 then 1 else 0)) ∧
      (liftMatrix (permMatrix σ)).PosSemidef) ↔ ∀ x y, σ (x+y)=σ x+σ y := by
  classical
  constructor
  · rintro ⟨ha,hps⟩
    have hσ : σ 0=0 := by
      by_contra hne
      simpa [permMatrix,hne] using ha.1 (σ 0)
    intro x y
    let K := liftMatrix (permMatrix σ)
    let p : G×G := (σ x,x)
    let q : G×G := (0,0)
    let i : G×G := (σ x+σ y,x+y)
    have hcol : K i p = K i q := equal_columns K hps p q (by simp [K,p,liftMatrix,permMatrix,hσ])
      (by simp [K,q,liftMatrix,permMatrix,hσ]) (by simp [K,p,q,liftMatrix,permMatrix]) _
    exact (by simpa [K,i,p,q,liftMatrix,permMatrix] using hcol : σ x+σ y=σ (x+y)).symm
  · intro hadd
    let e : G →+ G := AddMonoidHom.mk' σ hadd
    have h0 : σ 0=0 := e.map_zero
    refine ⟨⟨fun a => by simp [permMatrix,h0],?_⟩,?_⟩
    · intro b
      by_cases hb : b=0
      · simp [permMatrix,hb,h0]
      · have hne : 0 ≠ σ b := fun eq => hb (σ.injective (eq.symm.trans h0.symm))
        simp [permMatrix,hb,hne]
    · let B : Matrix (G×G) G ℂ := Matrix.of (fun u j => if u.1-e u.2=j then 1 else 0)
      have he : B * B.conjTranspose = liftMatrix (permMatrix σ) := by
        ext i j
        rw [Matrix.mul_apply]
        have hs : ∀ t : G, B i t * B.conjTranspose t j =
            if i.1-e i.2 = t then B.conjTranspose t j else 0 := by
          intro t
          by_cases h : i.1-e i.2 = t <;> simp only [B, Matrix.of_apply, h, if_true, if_false, one_mul, zero_mul]
        simp_rw [hs]
        rw [Finset.sum_ite_eq]
        simp only [mem_univ,if_true,Matrix.conjTranspose_apply,B,Matrix.of_apply,liftMatrix,permMatrix]
        have hi : i.1-e i.2 = j.1-e j.2 ↔ i.1-j.1=e (i.2-j.2) := by
          rw [map_sub]
          constructor <;> intro h
          · calc i.1 - j.1 = (i.1 - e i.2) - j.1 + e i.2 := by abel
                 _ = _ := by rw [h]; abel
          · calc i.1 - e i.2 = (i.1 - j.1) - e i.2 + j.1 := by abel
                 _ = _ := by rw [h]; abel
        change star (if j.1-e j.2=i.1-e i.2 then (1:ℂ) else 0) = (if i.1-j.1=e (i.2-j.2) then 1 else 0)
        by_cases h : i.1-e i.2 = j.1-e j.2
        · simp [h.symm,hi.mp h]
        · have nh : i.1-j.1 ≠ e (i.2-j.2) := fun eq => h (hi.mpr eq)
          simp only [if_neg (Ne.symm h),if_neg nh,star_zero]
      exact he ▸ Matrix.posSemidef_self_mul_conjTranspose B

end OMA.S_mo_443664

namespace OMA.S_mo_443664
open scoped ComplexOrder
lemma class_iff {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G] (M : Matrix G G ℂ) :
    Doubly (dual M) ↔ ((∀ a, M a 0 = if a=0 then 1 else 0) ∧
      (∀ b, M 0 b = if b=0 then 1 else 0)) ∧ (liftMatrix M).PosSemidef := by
  change (Margins (dual M) ∧ ∀ χ ψ, 0 ≤ dual M χ ψ) ↔ _
  rw [dual_margins,dual_nonneg_iff]
  exact and_congr_right fun _ => (finite_bochner (fun t : G×G => M t.1 t.2)).symm
end OMA.S_mo_443664

open OMA.S_mo_443664

theorem OMA.solution : type_of% @OMA.S_mo_443664.main := by
  intro G _ _ _
  exact ⟨fun M _ => class_iff M, fun σ => (class_iff (permMatrix σ)).trans (perm_class σ)⟩

