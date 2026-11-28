import OMAStatements.S_mo_242590
namespace OMA.S_mo_242590
open Polynomial Quaternion

private def a : H := ⟨0,0,0,-1⟩
private def b : H := ⟨0,1,0,0⟩

private lemma a_sq : a*a= -1 := by
  apply Quaternion.ext
  · exact (Quaternion.re_mul a a).trans (by norm_num [a])
  · exact (Quaternion.imI_mul a a).trans (by norm_num [a])
  · exact (Quaternion.imJ_mul a a).trans (by norm_num [a])
  · exact (Quaternion.imK_mul a a).trans (by norm_num [a])
private lemma b_sq : b*b= -1 := by
  apply Quaternion.ext
  · exact (Quaternion.re_mul b b).trans (by norm_num [b])
  · exact (Quaternion.imI_mul b b).trans (by norm_num [b])
  · exact (Quaternion.imJ_mul b b).trans (by norm_num [b])
  · exact (Quaternion.imK_mul b b).trans (by norm_num [b])
private lemma a_ne : a≠0 := by intro h; have := congrArg (fun x : H => x.imK) h; norm_num [a] at this
private lemma ab_ne : a+b≠0 := by intro h; have := congrArg (fun x : H => x.imI) h; change (0:ℝ)+1=0 at this; norm_num at this

private noncomputable def L : Polynomial H := X-C a
private noncomputable def family (m : ℕ) : Polynomial H := L^m*(X-C b)
private noncomputable def op (z t : H) : H := t*z-a*t

private lemma eval_step (Q : Polynomial H) (z : H) : (L*Q).eval z=op z (Q.eval z) := by
  rw [L,sub_mul,X_mul,eval_sub,eval_mul_X,eval_C_mul]
  rfl

private lemma family_step (m : ℕ) : family (m+1) = L*family m := by
  simp [family,pow_succ',mul_assoc]

private lemma unit_of_op {z t : H} (h : op z t=0) (ht : t≠0) : z*z= -1 := by
  have e := sub_eq_zero.mp h
  apply mul_left_cancel₀ ht
  calc
    t*(z*z) = (t*z)*z := (mul_assoc ..).symm
    _ = (a*t)*z := by rw [e]
    _ = a*(a*t) := by rw [mul_assoc,e]
    _ = t*(-1) := by rw [← mul_assoc,a_sq]; simp

private lemma double_op (z t : H) (hz : z*z= -1) : op z (op z t) = (-2*a)*op z t := by
  unfold op
  calc
    _ = t*(z*z) - 2*(a*t*z) + (a*a)*t := by noncomm_ring
    _ = -t - 2*(a*t*z) - t := by rw [hz,a_sq]; simp; abel
    _ = _ := by
      calc
        _ = -(2*(a*t*z)) + 2*((a*a)*t) := by rw [a_sq]; simp; noncomm_ring
        _ = _ := by noncomm_ring

private lemma roots_single (m : ℕ) (z : H) : (family (m+1)).eval z=0 ↔ z=b := by
  have ev (l : ℕ) : (family (l+1)).eval z=op z ((family l).eval z) := by rw [family_step,eval_step]
  have hbase : (family 0).eval z=z-b := by simp [family]
  induction m with
  | zero =>
    rw [ev,hbase]
    constructor
    · intro h
      by_contra hz
      have he := unit_of_op h (sub_ne_zero.mpr hz)
      have hh : (a+b)*(b-z)=0 := by
        calc
          _ = (b*b)-(a+b)*z+a*b := by noncomm_ring
          _ = (z*z)-(a+b)*z+a*b := by rw [b_sq,he]
          _ = op z (z-b) := by unfold op; noncomm_ring
          _ = 0 := h
      exact hz ((sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ab_ne)).symm)
    · rintro rfl
      simp [op]
  | succ m ih =>
    rw [ev]
    constructor
    · intro h
      apply ih.mp
      by_contra ht
      have he := unit_of_op h ht
      rw [ev,double_op _ _ he] at h
      have hcoef : (-2:H)*a≠0 := mul_ne_zero (neg_ne_zero.mpr (by intro h; have hh := congrArg (fun x : H => x.re) h; change (2:ℝ)=0 at hh; norm_num at hh)) a_ne
      exact ht ((ev m).trans ((mul_eq_zero.mp h).resolve_left hcoef))
    · intro h
      rw [ih.mpr h]
      simp [op]
private lemma deriv_family (m : ℕ) : (family (m+1)).derivative =
    L^m*((m+1) • (X-C b)+L) := by
  induction m with
  | zero =>
    rw [family_step]
    simp [family,L,derivative_mul]
  | succ m ih =>
    rw [family_step,derivative_mul,show L.derivative=1 by simp [L],one_mul,ih]
    change L^(m+1)*(X-C b) + L*(L^m*((m+1)•(X-C b)+L)) = _
    rw [← mul_assoc,← pow_succ',← mul_add]
    congr 1
    rw [succ_nsmul (X-C b) (m+1)]
    abel

private lemma eval_family_critical (m : ℕ) :
    ∃ z : H,(family (m+1)).derivative.eval z=0 ∧ z.imK= -1/((m+2:ℕ):ℝ) ∧ z.imK<0 := by
  let z : H := ⟨0,((m:ℝ)+1)/((m:ℝ)+2),0,-1/((m:ℝ)+2)⟩
  have hz : (((m+1) • (X-C b)+L):Polynomial H).eval z=0 := by
    simp only [L,eval_add,eval_sub,eval_X,eval_C,eval_smul]
    change (m+1) • (z-b) + (z-a) = 0
    apply Quaternion.ext
    · change (m+1) • ((0:ℝ)-0)+(0-0)=0; simp
    · change (m+1) • (((m:ℝ)+1)/((m:ℝ)+2)-1)+(((m:ℝ)+1)/((m:ℝ)+2)-0)=0
      simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; field_simp; ring
    · change (m+1) • ((0:ℝ)-0)+(0-0)=0; simp
    · change (m+1) • (-1/((m:ℝ)+2)-0)+(-1/((m:ℝ)+2)-(-1))=0
      simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; field_simp; ring
  have gen (k : ℕ) (p : Polynomial H) (hp : p.eval z=0) : (L^k*p).eval z=0 := by
    induction k with
    | zero => simpa using hp
    | succ k ih => rw [pow_succ',mul_assoc,eval_step,ih]; simp [op]
  refine ⟨z,?_,?_,?_⟩
  · rw [deriv_family]
    exact gen _ _ hz
  · simp [z]
  · change -1/((m:ℝ)+2)<0
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
end OMA.S_mo_242590

open OMA.S_mo_242590 in
theorem OMA.solution : type_of% @OMA.S_mo_242590.main := by
  rintro (_|_|m) hd
  · omega
  · omega
  obtain ⟨z,hz,hk,hl⟩ := eval_family_critical m
  refine ⟨family (m+1),b,z,((Polynomial.monic_X_sub_C a).pow _).mul (Polynomial.monic_X_sub_C b),?_,roots_single m,rfl,hz,hk,hl⟩
  rw [family,L,((Polynomial.monic_X_sub_C a).pow _).natDegree_mul (Polynomial.monic_X_sub_C b)]
  simp [(Polynomial.monic_X_sub_C a).natDegree_pow]
