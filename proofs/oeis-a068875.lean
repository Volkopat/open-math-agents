import OMAStatements.S_oeis_a068875
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The zeros of the power polynomials of OEIS A068875

Peter Bala conjectured that the nontrivial zeros of the nth coefficient
of (2C−1)^t all have real part −n/2, with C the Catalan series. Paul Barry
recorded the reverse Catalan substitution x=w(1−w) for the base series.

After this substitution the Miller recurrence gives (1−w²)G'=2tG.
A formal coefficient-change identity and a second differentiation express
the nth coefficient as 2t Q(n,n−1,2t+n)/n!. The monic polynomials Q obey
the Meixner–Pollaczek three-term recurrence after rotation. When Re(z)>0,
each successive ratio of Q values also has positive real part. Parity
gives the other half-plane. The same coefficient formula shows that the
zero at t=0 is simple.

Source: https://oeis.org/A068875
Classical recurrence: https://dlmf.nist.gov/18.22.E8
-/

namespace Poll875
open PowerSeries OMA.S_oeis_a068875

noncomputable def F (t : ℂ) : PowerSeries ℂ := mk (coeffPow t)
noncomputable def f : PowerSeries ℂ := X*(1-X)
noncomputable def G (t : ℂ) : PowerSeries ℂ := (F t).subst f
noncomputable def invOne : PowerSeries ℂ := (1-X)⁻¹

end Poll875

namespace Poll875

open PowerSeries OMA.S_oeis_a068875

private noncomputable def catC : PowerSeries ℂ := PowerSeries.map (Nat.castRingHom ℂ) catalanSeries

private noncomputable def baseA : PowerSeries ℂ := C (2:ℂ) * catC - 1

private theorem base_coeff (n : ℕ) : coeff n baseA = (a n : ℂ) := by
  cases n with
  | zero =>
    have hc : coeff 0 catC = 1 := by rw [catC,coeff_map,catalanSeries_coeff,catalan_zero,map_one]
    rw [baseA,map_sub,coeff_C_mul,hc,coeff_zero_one]
    norm_num [a]
  | succ n => simp [baseA,catC,a,coeff_C_mul]

private theorem xder_coeff (V : PowerSeries ℂ) (j : ℕ) :
    coeff j (X*derivative ℂ V) = (j:ℂ)*coeff j V := by
  cases j with
  | zero => simp
  | succ j => rw [coeff_succ_X_mul,coeff_derivative,Nat.cast_succ,mul_comm]

private theorem miller_step (t : ℂ) (n : ℕ) :
    ((n:ℂ)+1)*coeffPow t (n+1) =
    ∑ j ∈ Finset.range (n+1), ((((j+1:ℕ):ℂ)*(t+1)-((n:ℂ)+1))*
      (a (j+1):ℂ)*coeffPow t (n-j)) := by
  rw [coeffPow,Finset.sum_range]
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast (by omega : n+1 ≠ 0)
  rw [← mul_assoc,one_div,mul_inv_cancel₀ hn,one_mul]

private theorem convolution (P Q : PowerSeries ℂ) (n : ℕ) :
    coeff n (P*Q) = ∑ k ∈ Finset.range (n+1), coeff k P * coeff (n-k) Q :=
  (coeff_mul n P Q).trans (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i P * coeff j Q) n)

private theorem miller_ode (t : ℂ) :
    baseA * derivative ℂ (F t) = C t * (derivative ℂ baseA * F t) := by
  apply mul_left_cancel₀ (X_ne_zero (R := ℂ))
  calc
    X * (baseA * derivative ℂ (F t)) = baseA * (X*derivative ℂ (F t)) := by ring
    _ = C t * ((X*derivative ℂ baseA) * F t) := by
      apply PowerSeries.ext
      intro n
      have aux (k : ℕ) : coeff k (F t) = coeffPow t k := coeff_mk _ _
      rw [coeff_C_mul,convolution baseA,convolution (X*derivative ℂ baseA)]
      simp only [xder_coeff,base_coeff,aux,Finset.mul_sum]
      cases n with
      | zero => simp
      | succ n =>
        rw [Finset.sum_range_succ' _ (n+1), Finset.sum_range_succ' _ (n+1)]
        simp only [show a 0 = 1 by rfl, Nat.cast_zero, zero_mul, mul_zero, zero_add,
          one_mul, Nat.sub_zero, add_zero, Nat.cast_succ]
        have hm := miller_step t n
        simp only [Nat.cast_succ] at hm
        rw [hm]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjl : j ≤ n := by simpa using Finset.mem_range.mp hj
        rw [Nat.succ_sub_succ_eq_sub,Nat.cast_sub hjl]
        ring
    _ = X * (C t * (derivative ℂ baseA * F t)) := by ring

private theorem f_substable : HasSubst f :=
  .of_constantCoeff_zero' (by simp [f])

private theorem pull_base : ((baseA.subst f : PowerSeries ℂ) * (1-X)) = 1+X := by
  let c : PowerSeries ℂ := catC.subst f
  have eq : catC^2 * X + 1 = catC := by
    simpa [catC] using congrArg (PowerSeries.map (Nat.castRingHom ℂ)) catalanSeries_sq_mul_X_add_one
  have eq' : c^2*f + 1 = c := by
    have h := congrArg (PowerSeries.substAlgHom (R:=ℂ) f_substable) eq
    simpa only [map_pow,map_mul,map_add,map_one,coe_substAlgHom,subst_X f_substable,c] using h
  have hn : (X*c-1 : PowerSeries ℂ) ≠ 0 := by
    intro he
    have h := congrArg constantCoeff he
    simp at h
  have hc : (1-X)*c = 1 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show ((1-X)*c-1)*(X*c-1)=0 by
      dsimp [f] at eq'
      linear_combination eq')).resolve_right hn
  have base : (baseA.subst f : PowerSeries ℂ) = 2*c-1 := by
    rw [← coe_substAlgHom f_substable,baseA,map_sub,map_mul,map_one,coe_substAlgHom,subst_C]
    change C (2:ℂ)*c-1=2*c-1
    rw [map_ofNat]
  rw [base]
  linear_combination 2 * hc

theorem G_zero (t : ℂ) : coeff 0 (G t) = 1 := by
  rw [G,coeff_subst' f_substable, finsum_eq_single _ 0]
  · simp [F,coeffPow]
  · intro j hj
    rw [coeff_zero_eq_constantCoeff_apply,map_pow]
    simp [f,hj]

theorem G_ode (t : ℂ) :
    (1-X^2)*derivative ℂ (G t) = C (2*t)*G t := by
  let B : PowerSeries ℂ := baseA.subst f
  have hB : B*(1-X) = 1+X := pull_base
  have hdB : derivative ℂ B * (1-X) = 1+B := by
    have hd := congrArg (derivative ℂ) hB
    simp only [Derivation.leibniz,map_sub,map_add,derivative_one,derivative_X,
      zero_sub,zero_add,smul_eq_mul,mul_neg,mul_one] at hd
    linear_combination hd
  have he : B * derivative ℂ (G t) = C t * (derivative ℂ B * G t) := by
    have h := congrArg (PowerSeries.substAlgHom (R:=ℂ) f_substable) (miller_ode t)
    simp only [map_mul,coe_substAlgHom,subst_C] at h
    change baseA.subst f * (derivative ℂ (F t)).subst f =
      C t * ((derivative ℂ baseA).subst f * (F t).subst f) at h
    dsimp only [G,B]
    rw [derivative_subst f_substable,derivative_subst f_substable]
    linear_combination derivative ℂ f * h
  rw [map_mul,map_ofNat]
  linear_combination (1-X)^2*he + (X-1)*derivative ℂ (G t)*hB +
    C t*(1-X)*G t*hdB + C t*G t*hB

end Poll875

namespace Poll875
open PowerSeries

theorem one_mul_invOne : (1-X)*invOne = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp)

theorem f_mul_invOne : f*invOne = X := by rw [f,mul_assoc,one_mul_invOne,mul_one]

theorem invOne_coeff_zero : coeff 0 invOne=1 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  simp [invOne]
end Poll875

namespace Poll875
open PowerSeries

private theorem coefficient_parts (U H : PowerSeries ℂ) (k : ℕ) :
    coeff k (derivative ℂ U * H^(k+1)) +
      ((k:ℂ)+1)*coeff k (U*H^k*derivative ℂ H) =
      ((k:ℂ)+1)*coeff (k+1) (U*H^(k+1)) := by
  have d : derivative ℂ (U*H^(k+1)) =
      derivative ℂ U*H^(k+1) + C ((k:ℂ)+1)*(U*H^k*derivative ℂ H) := by
    rw [Derivation.leibniz, derivative_pow]
    simp only [smul_eq_mul,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,map_add,map_natCast,map_one]
    ring
  have a := congrArg (coeff k) d
  rw [map_add, coeff_C_mul, coeff_derivative] at a
  simpa only [mul_comm (coeff (k+1) _)] using a.symm

private theorem coefficient_parts_shift (q H U : PowerSeries ℂ) (id : q*H=X) (k : ℕ) :
    ((k:ℂ)+1)*coeff (k+1) (derivative ℂ (q*U)*H^(k+2)) =
    ((k:ℂ)+2)*coeff k (derivative ℂ U*H^(k+1)) := by
  have shift (V : PowerSeries ℂ) (m : ℕ) :
      q*V*H^(m+1) = X*(V*H^m) := by
    rw [pow_succ,← id]
    ring
  have L := coefficient_parts U H k
  have R := coefficient_parts (q*U) H (k+1)
  rw [shift, mul_assoc X, coeff_succ_X_mul, shift, coeff_succ_X_mul] at R
  push_cast at R
  linear_combination ((k:ℂ)+1)*R - ((k:ℂ)+2)*L

private theorem split_subst {q : PowerSeries ℂ} (hq : HasSubst q) (P : PowerSeries ℂ) :
    P.subst q = q*((mk fun k => coeff (k+1) P).subst q) + C (constantCoeff P) := by
  have h := congrArg (fun B : PowerSeries ℂ => B.subst q) (eq_X_mul_shift_add_const P)
  change _ = _ + MvPowerSeries.C (constantCoeff P)
  simpa only [subst_add hq,subst_mul hq,subst_X hq,subst_C] using h

private theorem coeff_zero_subst_zero {q : PowerSeries ℂ} (hq : constantCoeff q=0)
    (P : PowerSeries ℂ) : coeff 0 (P.subst q) = coeff 0 P := by
  rw [split_subst (HasSubst.of_constantCoeff_zero hq) P]
  simp [coeff_zero_eq_constantCoeff_apply,hq]

theorem residue_change_general (q H : PowerSeries ℂ) (id : q*H=X)
    (hq : constantCoeff q=0) (P : PowerSeries ℂ) (k : ℕ) :
    ((k:ℂ)+1)*coeff (k+1) P = coeff k (derivative ℂ (P.subst q) * H^(k+1)) := by
  let T (B : PowerSeries ℂ) := mk fun r => coeff (r+1) B
  have hd (B : PowerSeries ℂ) :
      derivative ℂ (B.subst q) = derivative ℂ (q*((T B).subst q)) := by
    rw [split_subst (HasSubst.of_constantCoeff_zero hq) B, map_add]
    simp [T]
  induction k generalizing P with
  | zero =>
    rw [hd]
    let U := (T P).subst q
    have A := coefficient_parts (q*U) H 0
    have hh : q*U*H = X*U := by rw [←id]; ring
    simp only [Nat.reduceAdd,pow_one,pow_zero,mul_one] at A
    rw [hh,show coeff 1 (X*U) = coeff 0 U from coeff_succ_X_mul 0 U] at A
    have zz : coeff 0 (q*U*derivative ℂ H) = 0 := by simp [coeff_zero_eq_constantCoeff_apply,hq]
    rw [zz] at A
    have B : coeff 0 U = coeff 1 P := (coeff_zero_subst_zero hq (T P)).trans (coeff_mk _ _)
    simpa [U,B] using A.symm
  | succ k ih =>
    rw [hd]
    have h := coefficient_parts_shift q H ((T P).subst q) id k
    rw [← ih (T P)] at h
    have same : coeff (k+1) (T P) = coeff (k+2) P := coeff_mk _ _
    rw [same] at h
    push_cast
    apply mul_left_cancel₀ (a:=((k:ℂ)+1)) (by exact_mod_cast Nat.succ_ne_zero k)
    linear_combination -h

theorem residue_change (P : PowerSeries ℂ) (n : ℕ) (hn : 0<n) :
    (n:ℂ)*coeff n P = coeff (n-1) (derivative ℂ (P.subst f) * invOne^n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simpa using residue_change_general f invOne f_mul_invOne (by simp [f]) P k

end Poll875

namespace Poll875

/-- Monic normalization of the Meixner–Pollaczek recurrence after rotation onto the
imaginary axis, with parameter `1 + n/2` and angle `π/2`. -/
def Q (n : ℕ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, z => z
  | j+2, z => z * Q n (j+1) z + ((j+1 : ℕ) : ℂ) * ((n+j+2 : ℕ) : ℂ) * Q n j z

end Poll875

namespace Poll875
open PowerSeries

noncomputable def invQuad : PowerSeries ℂ := (1-X^2)⁻¹
private theorem quad_unit : (1-X^2)*invQuad = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp)

private theorem quad_one : (1-X^2)*invOne = 1+X := by
  calc
    _ = (1+X)*((1-X)*invOne) := by ring
    _ = _ := by rw [one_mul_invOne,mul_one]

private theorem deriv_one_pow (n : ℕ) :
    derivative ℂ (invOne^n) = n*invOne^n*invOne := by
  have dh : derivative ℂ invOne=invOne^2 := by
    simp [invOne,derivative_inv']
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Derivation.leibniz,smul_eq_mul,smul_eq_mul,ih,dh,Nat.cast_succ]
    ring

private theorem deriv_quad : derivative ℂ invQuad=2*X*invQuad^2 := by
  simp only [invQuad,derivative_inv',map_sub,derivative_one,derivative_pow,derivative_X]
  norm_num
  ring

/-- The coefficient series for the three-term recurrence centered at 2t+n. -/
noncomputable def B (n : ℕ) (t : ℂ) : PowerSeries ℂ := G t * invOne^n * invQuad

theorem B_zero (n : ℕ) (t : ℂ) (z : coeff 0 (G t)=1) : coeff 0 (B n t)=1 := by
  rw [coeff_zero_eq_constantCoeff_apply] at z ⊢
  simp [B,invOne,invQuad,z]

theorem B_ode (n : ℕ) (t : ℂ) (ode : (1-X^2)*derivative ℂ (G t)=C (2*t)*G t) :
    (1-X^2)*derivative ℂ (B n t) = C (2*t+n)*B n t + C ((n:ℂ)+2)*X*B n t := by
  simp only [B,Derivation.leibniz,smul_eq_mul,deriv_one_pow,deriv_quad,map_add,map_natCast,map_ofNat]
  linear_combination (invOne^n*invQuad)*ode +
    ((n:PowerSeries ℂ)*G t*invOne^n*invQuad)*quad_one +
    (2*X*G t*invOne^n*invQuad)*quad_unit

theorem deriv_factor (n : ℕ) (t : ℂ)
    (ode : (1-X^2)*derivative ℂ (G t)=C (2*t)*G t) :
    derivative ℂ (G t)*invOne^n = C (2*t)*B n t := by
  unfold B
  linear_combination (invOne^n*invQuad)*ode - (derivative ℂ (G t)*invOne^n)*quad_unit

theorem coeff_Q (n : ℕ) (t : ℂ) (b : PowerSeries ℂ) (hzero : coeff 0 b=1)
    (hode : (1-X^2)*derivative ℂ b = C (2*t+n)*b+C ((n:ℂ)+2)*X*b) (j : ℕ) :
    (j.factorial : ℂ)*coeff j b = Q n j (2*t+n) := by
  have x_coeff (v : PowerSeries ℂ) (d : ℕ) : coeff d (X*v) =
      if 1≤d then coeff (d-1) v else 0 := by
    simpa only [pow_one] using coeff_X_pow_mul' v 1 d
  have extract (z v : ℂ) (H : (1-X^2)*derivative ℂ b=C z*b+C v*X*b) (k : ℕ) :
      coeff (k+1) b*((k:ℂ)+1) -
        (if 2≤k then coeff (k-2+1) b*(((k-2:ℕ):ℂ)+1) else 0) =
      z*coeff k b+v*(if 1≤k then coeff (k-1) b else 0) := by
    simpa only [sub_mul,one_mul,map_sub,map_add,mul_assoc,coeff_C_mul,x_coeff,
      coeff_X_pow_mul',coeff_derivative] using congrArg (coeff k) H
  have hshift (k : ℕ) := extract _ _ hode (k+1)
  have b₁ : coeff 1 b = 2*t+n := by
    have e := extract _ _ hode 0
    rw [hzero] at e
    norm_num at e
    exact e
  induction j using Nat.twoStepInduction with
  | zero => simp [Q,hzero]
  | one => simp [Q,b₁]
  | more j ih ih' =>
    have eqRec : ((j:ℂ)+2)*coeff (j+2) b =
        (2*t+n)*coeff (j+1) b+((n:ℂ)+j+2)*coeff j b := by
      have eq := hshift j
      cases j with
      | zero => norm_num at eq ⊢; linear_combination eq
      | succ j =>
        simp (disch := omega) only [if_pos,Nat.add_sub_cancel,
          show ∀ i:ℕ, i+1+1-2=i by omega,Nat.cast_add,Nat.cast_one] at eq
        push_cast
        linear_combination eq
    rw [Q,←ih,←ih',Nat.factorial_succ (j+1),Nat.factorial_succ j]
    push_cast
    linear_combination (j.factorial:ℂ)*((j:ℂ)+1)*eqRec

end Poll875

namespace Poll875
open OMA.S_oeis_a068875

private theorem Q_right (n j : ℕ) (z : ℂ) (hz : 0<z.re) :
    Q n j z ≠ 0 ∧ 0 < (Q n (j+1) z / Q n j z).re := by
  induction j with
  | zero => simpa [Q] using hz
  | succ j ih =>
    rcases ih with ⟨hp,hr⟩
    have hq : Q n (j+1) z ≠ 0 := by
      intro h
      simp [h] at hr
    have hratio : Q n (j+1) z / Q n j z ≠ 0 := div_ne_zero hq hp
    have invpos : 0 < (Q n (j+1) z / Q n j z)⁻¹.re := by
      rw [Complex.inv_re]
      exact div_pos hr (Complex.normSq_pos.mpr hratio)
    have recur : Q n (j+2) z / Q n (j+1) z =
        z+((j+1:ℕ):ℂ)*((n+j+2:ℕ):ℂ)*(Q n (j+1) z/Q n j z)⁻¹ := by
      rw [Q,inv_div]
      field_simp
    refine ⟨hq,?_⟩
    rw [recur]
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.natCast_re,
      Complex.natCast_im,mul_zero,zero_mul,sub_zero,add_zero]
    positivity

private theorem Q_parity (n j : ℕ) (z : ℂ) : Q n j (-z) = (-1:ℂ)^j * Q n j z := by
  induction j using Nat.twoStepInduction with
  | zero => simp [Q]
  | one => simp [Q]
  | more j ih0 ih1 =>
    rw [Q,Q,ih1,ih0]
    simp only [pow_succ]
    ring

theorem Q_re_zero {n j : ℕ} {z : ℂ} (h : Q n j z=0) : z.re=0 := by
  rcases lt_trichotomy 0 z.re with hp | he | hn
  · exact False.elim ((Q_right n j z hp).1 h)
  · exact he.symm
  · have hn' : 0<(-z).re := by simpa using hn
    apply False.elim
    apply (Q_right n j (-z) hn').1
    simp [Q_parity,h]

theorem Q_differentiable (n j : ℕ) : Differentiable ℂ (Q n j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact differentiable_const _
  | one => exact differentiable_id
  | more j ih0 ih1 =>
    change Differentiable ℂ (fun z => z*Q n (j+1) z+((j+1:ℕ):ℂ)*((n+j+2:ℕ):ℂ)*Q n j z)
    fun_prop

theorem native_of_Q (formula : ∀ (n : ℕ) (t : ℂ), 1≤n →
    coeffPow t n = (2*t/(n.factorial:ℂ))*Q n (n-1) (2*t+n)) :
    ∀ n : ℕ, 2 ≤ n →
      deriv (fun t : ℂ => coeffPow t n) 0 ≠ 0 ∧
      ∀ t : ℂ, t ≠ 0 → coeffPow t n = 0 → t.re = -((n : ℝ) / 2) := by
  intro n hn
  have fac : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  constructor
  · let H : ℂ → ℂ := fun t => Q n (n-1) (2*t+n)
    have de : DifferentiableAt ℂ H 0 := by
      apply (Q_differentiable n (n-1)).differentiableAt.comp
      fun_prop
    have eq : (fun t : ℂ => coeffPow t n) = fun t => (2/(n.factorial:ℂ))*t*H t := by
      funext t
      rw [formula n t (by omega)]
      dsimp [H]
      ring
    rw [eq]
    have qn : Q n (n-1) (n:ℂ) ≠ 0 := (Q_right n (n-1) _ (by simp; positivity)).1
    have value : deriv (fun t : ℂ => (2/(n.factorial:ℂ))*t*H t) 0 =
        (2/(n.factorial:ℂ))*Q n (n-1) n := by
      rw [deriv_fun_mul (by fun_prop) de]
      simp [H,deriv_const_mul_id]
    exact value ▸ mul_ne_zero (div_ne_zero (by norm_num) fac) qn
  · intro t ht ht0
    rw [formula n t (by omega)] at ht0
    have nz : 2*t/(n.factorial:ℂ) ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) ht) fac
    have hr := Q_re_zero ((mul_eq_zero.mp ht0).resolve_left nz)
    simp [Complex.add_re,Complex.mul_re] at hr
    linarith

end Poll875

open Poll875 OMA.S_oeis_a068875 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a068875.main := by
  apply native_of_Q
  intro n t hn
  obtain ⟨m,rfl⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  have cf := residue_change (F t) (m+1) (by omega)
  have val : coeff (m+1) (F t)=coeffPow t (m+1) := by simp [F]
  rw [val,Nat.add_sub_cancel] at cf
  change ((m+1:ℕ):ℂ)*coeffPow t (m+1) =
      coeff m (derivative ℂ (G t)*invOne^(m+1)) at cf
  rw [deriv_factor _ _ (G_ode t),coeff_C_mul] at cf
  have eq := coeff_Q (m+1) t (B (m+1) t) (B_zero _ _ (G_zero t)) (B_ode _ _ (G_ode t)) m
  have factor : ((m+1).factorial:ℂ)*coeffPow t (m+1) =
      2*t*Q (m+1) m (2*t+((m+1:ℕ):ℂ)) := calc
    _ = (m.factorial:ℂ)*(((m+1:ℕ):ℂ)*coeffPow t (m+1)) := by
      rw [Nat.factorial_succ]; push_cast; ring
    _ = _ := by rw [cf,←eq]; ring
  have hz : ((m+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m+1)
  simp only [Nat.add_sub_cancel]
  field_simp
  linear_combination factor
