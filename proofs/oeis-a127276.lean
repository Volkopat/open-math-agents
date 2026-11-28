import OMAStatements.S_oeis_a127276
import Mathlib

/-!
# Barry's endpoint-modified central-binomial Hankel determinants

Source: Paul Barry, OEIS A127275/A127276. R. J. Mathar proposed the
closed form and generating function. Credit: @connoranderson.
https://oeis.org/A127275
https://oeis.org/A127276

The shifted monic Chebyshev basis diagonalizes the central-binomial moment
functional. The two corrections at 0 and 4 have rank one each. Factoring
out the diagonal matrix reduces the remaining determinant to a 2 × 2 one.

The Chebyshev degree argument and the Jacobi-operator proof pattern are
adapted from our proof of MO442285 and the CiglerElevenPolynomials and
CiglerElevenMoments modules of The Omega Institute's TrureTuring project,
Apache License 2.0, revision c6adc5ebc6592e960b8eae4d9ac97ef3b07509d7.
https://github.com/The-Omega-Institute/trureturing/tree/c6adc5ebc6592e960b8eae4d9ac97ef3b07509d7/D5/S3/Combinatorics
-/
namespace OMA.S_oeis_a127276
noncomputable section
open Polynomial Matrix

def S (j : ℤ) : ℚ[X] := (Chebyshev.S ℚ j).comp (X - 2)
def T (j : ℕ) : ℚ[X] := (Chebyshev.C ℚ (j : ℤ)).comp (X - 2)
def P (j : ℕ) : ℚ[X] := S (j : ℤ)

@[simp] theorem P_zero : P 0 = 1 := by simp [P,S]
@[simp] theorem P_one : P 1 = X-2 := by simp [P,S,Chebyshev.S_one]
theorem P_next (j : ℕ) : P (j+2) = (X-2)*P (j+1) - P j := by
  simp only [P,S,Nat.cast_add,Nat.cast_ofNat,Chebyshev.S_add_two,sub_comp,mul_comp,X_comp,
    Nat.cast_one]

theorem P_deg (j : ℕ) : (P j).IsMonicOfDegree j := by
  have hlin : (X - 2 : ℚ[X]).IsMonicOfDegree 1 :=
    by
      rw [← Polynomial.C_ofNat (R := ℚ) (n := 2)]
      exact ⟨natDegree_X_sub_C _, monic_X_sub_C _⟩
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hlin
  | more j h₀ h₁ =>
    rw [P_next]
    have h := hlin.mul h₁
    rw [show 1+(j+1)=j+2 by omega] at h
    exact h.sub (by rw [h₀.natDegree_eq]; omega)

def G (j : ℕ) : ℚ[X] := if j=0 then 1 else T j

theorem G_deg (j : ℕ) : (G j).IsMonicOfDegree j := by
  cases j with
  | zero => simp [G]
  | succ j =>
    have h := Chebyshev.C_eq_S_sub_X_mul_S ℚ ((j : ℤ)+1)
    have h' := Chebyshev.S_add_one ℚ (j : ℤ)
    simp only [add_sub_cancel_right] at h
    have e : Chebyshev.C ℚ ((j : ℤ)+1) = Chebyshev.S ℚ ((j : ℤ)+1) -
        Chebyshev.S ℚ ((j : ℤ)-1) := by linear_combination h + h'
    change (G (j+1)).IsMonicOfDegree (j+1)
    rw [G,if_neg (by omega),T,Nat.cast_add,Nat.cast_one,e,sub_comp]
    apply (P_deg (j+1)).sub
    cases j with
    | zero => simp [Chebyshev.S_neg_one]
    | succ j =>
      change (S (((j+1 : ℕ) : ℤ)-1)).natDegree < j+1+1
      rw [show ((j+1 : ℕ) : ℤ)-1 = (j : ℤ) by omega]
      change (P j).natDegree < _
      rw [(P_deg j).natDegree_eq]
      omega


def W (j : ℤ) : ℚ[X] := (Chebyshev.C ℚ j).comp (X-2)
theorem W_next (n : ℕ) : W ((n+2:ℕ):ℤ)=(X-2)*W ((n+1:ℕ):ℤ)-W (n:ℤ) := by
  simp only [W,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Chebyshev.C_add_two,sub_comp,mul_comp,X_comp]
theorem W_mul (i j : ℤ) : W i * W j = W (i+j) + W (i-j) := by
  rw [W,W,←mul_comp,Chebyshev.C_mul_C,add_comp]
  rfl
theorem W_neg (i : ℤ) : W (-i) = W i := by simp [W,Chebyshev.C_neg]
theorem G_eval0 (i : ℕ) : (G i).eval 0 = (if i=0 then 1 else 2)*(-1)^i := by
  cases i with
  | zero => simp [G]
  | succ i =>
    have hh : ((i:ℤ)+1).natAbs=i+1 := by omega
    simp [G,T,Chebyshev.C_eval_neg_two,hh]
theorem G_eval4 (i : ℕ) : (G i).eval 4 = if i=0 then 1 else 2 := by
  cases i with
  | zero => simp [G]
  | succ i => simp [G,T,show (4:ℚ)-2=2 by norm_num,Chebyshev.C_eval_two]
end
end OMA.S_oeis_a127276

namespace OMA.S_oeis_a127276
noncomputable section
open Polynomial

theorem moments : ∃ L : ℚ[X] →ₗ[ℚ] ℚ,
    (∀ n : ℕ, L (X^n) = Nat.centralBinom n) ∧
    ∀ i j : ℕ, L (G i * G j) = if i=j then (if i=0 then 1 else 2) else 0 := by
  let J : Module.End ℚ (ℕ→ℚ) := {
    toFun := fun v => fun
      | 0 => 2*v 0 + 2*v 1
      | k+1 => v k + 2*v (k+1) + v (k+2)
    map_add' := by intro v w;ext k;cases k <;> simp <;> ring
    map_smul' := by intro c v;ext k;cases k <;> simp <;> ring }
  let L : ℚ[X] →ₗ[ℚ] ℚ := {
    toFun := fun p => (aeval J p) (Pi.single 0 1) 0
    map_add' := by intros;simp
    map_smul' := by intros;simp }
  have evTwo : aeval J (2:ℚ[X])=(2:Module.End ℚ (ℕ→ℚ)) := aeval_natCast J 2
  have row (n : ℕ) (v : ℕ→ℚ) : (aeval J (W (n:ℤ))) v 0 = 2*v n := by
    induction n using Nat.twoStepInduction generalizing v with
    | zero => simp [W,Chebyshev.C_zero,evTwo,Module.End.ofNat_apply]
    | one =>
      simp [W,Chebyshev.C_one,evTwo,J,LinearMap.sub_apply,Module.End.ofNat_apply,Pi.sub_apply]
    | more n ih₀ ih₁ =>
      rw [W_next]
      have hc : aeval J ((X-2)*W ((n+1:ℕ):ℤ)) = aeval J (W ((n+1:ℕ):ℤ))*(J-2) := by
        rw [mul_comm,map_mul,map_sub,aeval_X,evTwo]
      rw [map_sub,hc]
      change aeval J (W ((n+1:ℕ):ℤ)) ((J-2) v) 0 - aeval J (W (n:ℤ)) v 0 = _
      rw [ih₁,ih₀]
      simp [J,LinearMap.sub_apply,Module.End.ofNat_apply,Pi.sub_apply]
      ring
  let A (t k : ℕ) : ℚ := ((2*t).choose (t+k) : ℚ)
  have twoPascal (a b : ℕ) : ((a+2).choose (b+2):ℚ) =
      a.choose b + 2*(a.choose (b+1):ℚ) + a.choose (b+2) := by
    rw [show a+2=(a+1)+1 by omega,show b+2=(b+1)+1 by omega,Nat.choose_succ_succ',
      Nat.choose_succ_succ',Nat.choose_succ_succ'];push_cast;ring
  have first (t : ℕ) : A (t+1) 0 = 2*A t 0+2*A t 1 := by
    cases t with
    | zero => norm_num [A,Nat.choose]
    | succ t =>
      have hh := Nat.choose_symm (n:=2*(t+1)) (k:=t+2) (by omega)
      rw [show 2*(t+1)-(t+2)=t by omega] at hh
      simp only [A,add_zero]
      rw [show 2*(t+1+1)=2*(t+1)+2 by omega,twoPascal,hh]
      ring
  have next (t k : ℕ) : A (t+1) (k+1)=A t k+2*A t (k+1)+A t (k+2) := by
    simp only [A]
    rw [show 2*(t+1)=2*t+2 by omega,show t+1+(k+1)=(t+k)+2 by omega,twoPascal]
    simp [Nat.add_assoc]
  have powers (t k : ℕ) : (J^t) (Pi.single 0 1) k = A t k := by
    induction t generalizing k with
    | zero => cases k <;> simp [A]
    | succ t ih =>
      rw [pow_succ',Module.End.mul_apply]
      cases k with
      | zero =>
        change 2*(J^t) (Pi.single 0 1) 0+2*(J^t) (Pi.single 0 1) 1 = _
        rw [ih,ih,first]
      | succ k =>
        change (J^t) (Pi.single 0 1) k+2*(J^t) (Pi.single 0 1) (k+1)+(J^t) (Pi.single 0 1) (k+2) = _
        rw [ih,ih,ih,next]
  have natValue (j : ℕ) : L (W (j:ℤ)) = if j=0 then 2 else 0 := by
    change (aeval J (W (j:ℤ))) (Pi.single 0 1) 0 = _
    rw [row]
    by_cases hj : j=0 <;> simp [hj]
  have value (j : ℤ) : L (W j) = if j=0 then 2 else 0 := by
    cases j with
    | ofNat n => simpa using natValue n
    | negSucc n =>
      rw [show Int.negSucc n= -((n+1:ℕ):ℤ) by omega,W_neg,natValue]
      simp
      omega
  refine ⟨L,?_,?_⟩
  · intro n
    change (aeval J (X^n)) (Pi.single 0 1) 0 = _
    simp [powers,A,Nat.centralBinom_eq_two_mul_choose]
  · intro i j
    have hg (t : ℕ) : G t = if t=0 then 1 else W (t:ℤ) := rfl
    have hone : L 1=1 := by simp [L]
    cases i <;> cases j <;> simp [hg,hone,W_mul,map_add,value,sub_eq_zero] <;> omega
end
end OMA.S_oeis_a127276

namespace OMA.S_oeis_a127276
open Matrix Finset
noncomputable section

def weight (i : ℕ) : ℚ := if i=0 then 1 else 2

private theorem wsum (n : ℕ) : (∑ i : Fin (n+1),weight i.val) = 2*n+1 := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,show (∑ i : Fin (n+1),weight i.castSucc.val) = _ from ih]
    simp [weight]
    ring

private theorem walt (n : ℕ) : (∑ i : Fin (n+1),weight i.val*(-1)^i.val) = (-1)^n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,show (∑ i : Fin (n+1),weight i.castSucc.val*(-1)^i.castSucc.val) = _ from ih]
    simp [weight,pow_succ]
    ring

private theorem wprod (n : ℕ) : (∏ i : Fin (n+1),weight i.val) = 2^n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc,show (∏ i : Fin (n+1),weight i.castSucc.val) = _ from ih]
    simp [weight,pow_succ]

def gram (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ := Matrix.of fun i j =>
  (if i=j then weight i.val else 0) +
  (weight i.val*(-1)^i.val*(weight j.val*(-1)^j.val) - weight i.val*weight j.val)/4

theorem determinant_gram (n : ℕ) : (gram n).det = 2^n*(1-(n:ℚ)*(n+1)/4) := by
  classical
  let u : Matrix (Fin (n+1)) (Fin 2) ℚ := Matrix.of fun i j => if j=0 then (-1)^i.val else 1
  let v : Matrix (Fin 2) (Fin (n+1)) ℚ := Matrix.of fun j i =>
    if j=0 then weight i.val*(-1)^i.val/4 else -weight i.val/4
  let D := Matrix.diagonal fun i : Fin (n+1) => weight i.val
  have he : gram n = D*(1+u*v) := by
    ext i j
    rw [show D=Matrix.diagonal (fun i : Fin (n+1) => weight i.val) from rfl,diagonal_mul]
    simp only [Matrix.add_apply,one_apply,mul_apply,Fin.sum_univ_two,u,v,of_apply,
      gram,(by decide : (1:Fin 2)≠0),if_false,one_mul]
    split_ifs <;> ring
  have sq (k : ℕ) : (-1:ℚ)^k * (-1)^k = 1 := by rw [←mul_pow];norm_num
  have hh : 1+v*u = !![1+(2*n+1:ℚ)/4,(-1)^n/4; -((-1)^n)/4,1-(2*n+1:ℚ)/4] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply,one_apply,mul_apply,u,v,of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.isValue,Fin.zero_eta,Fin.mk_one,ite_true,(by decide : (1:Fin 2)≠0),(by decide : (0:Fin 2)≠1),if_false]
    · simp_rw [show ∀ k, weight k*(-1)^k/4*(-1)^k = weight k/4 by
        intro k; rw [show weight k*(-1)^k/4*(-1)^k=weight k*((-1)^k*(-1)^k)/4 by ring,sq,mul_one]]
      rw [←Finset.sum_div,wsum]
    · simp only [mul_one,zero_add]
      rw [←Finset.sum_div,walt]
    · simp_rw [show ∀ k, -weight k/4*(-1)^k = -(weight k*(-1)^k)/4 by intro k;ring]
      rw [←Finset.sum_div,Finset.sum_neg_distrib,walt,zero_add]
    · simp only [mul_one]
      rw [←Finset.sum_div,Finset.sum_neg_distrib,wsum]
      ring
  rw [he,det_mul,Matrix.det_one_add_mul_comm,hh,det_fin_two,show D.det=2^n from
    (Matrix.det_diagonal).trans (wprod n)]
  change 2^n*((1+(2*(n:ℚ)+1)/4)*(1-(2*n+1)/4)-(-1)^n/4*(-((-1)^n)/4)) = _
  have hsq := sq n
  linear_combination (norm := ring) (2^n:ℚ)/16 * hsq
end
end OMA.S_oeis_a127276

namespace OMA.S_oeis_a127276
open Polynomial Matrix
noncomputable section

theorem det_orthogonal_basis (F : ℚ[X] →ₗ[ℚ] ℚ) (N : ℕ) :
    (Matrix.of fun i j : Fin N => F (X^(i.val+j.val))).det =
    (Matrix.of fun i j : Fin N => F (G i.val*G j.val)).det := by
  classical
  let A := Matrix.of fun i j : Fin N => (G j.val).coeff i.val
  let H := Matrix.of fun i j : Fin N => F (X^(i.val+j.val))
  have ha : A.det=1 := det_matrixOfPolynomials (fun i : Fin N => G i.val)
    (fun i => (G_deg i.val).natDegree_eq) (fun i => (G_deg i.val).monic)
  have expand (i : Fin N) : G i.val = ∑ k : Fin N, (G i.val).coeff k.val • X^k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => (G i.val).coeff a • (X : ℚ[X])^a)]
    simpa only [smul_eq_C_mul] using (G i.val).as_sum_range_C_mul_X_pow' (by rw [(G_deg _).natDegree_eq]; exact i.isLt)
  have change (w : ℚ[X]) (i : Fin N) :
      F (w*G i.val) = ∑ k : Fin N, F (w*X^k.val)*(G i.val).coeff k.val := by
    conv_lhs => rw [expand i,Finset.mul_sum]
    simp only [mul_smul_comm,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have haH (i j : Fin N) : (A.transpose*H) i j=F (G i.val*X^j.val) := by
    rw [mul_comm (G _),change,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    change (G i.val).coeff k.val * F (X^(k.val+j.val))=_
    rw [←pow_add,mul_comm (G i.val |>.coeff k.val),Nat.add_comm]
  have eq : A.transpose*H*A = Matrix.of fun i j : Fin N => F (G i.val*G j.val) := by
    ext i j
    rw [mul_apply,of_apply,change]
    simp_rw [haH]
    rfl
  change H.det = _
  rw [←eq,det_mul,det_mul,det_transpose,ha,one_mul,mul_one]
end
end OMA.S_oeis_a127276

namespace OMA.S_oeis_a127276
noncomputable section
open PowerSeries

private theorem stepZero (c : ℚ) (p : PowerSeries ℚ) :
    coeff 0 ((1-C c*X)*p) = coeff 0 p := by simp [sub_mul,mul_assoc]
private theorem stepSucc (c : ℚ) (p : PowerSeries ℚ) (n : ℕ) :
    coeff (n+1) ((1-C c*X)*p) = coeff (n+1) p-c*coeff n p := by simp [sub_mul,mul_assoc]

theorem closed_generating (f : ℕ→ℚ) (h : ∀ n, f n = 2^n*(1-(n:ℚ)*(n+1)/4)) :
    (1-2*X)^3 * PowerSeries.mk f = (1-4*X)*(1-X) := by
  let p := PowerSeries.mk f
  let l (c : ℚ) : PowerSeries ℚ := 1-C c*X
  have hl : (1-2*X)^3 * p = l 2 * (l 2 * (l 2 * p)) := by simp [l,pow_succ,mul_assoc,map_ofNat]
  have hr : (1-4*X)*(1-X) = l 4 * (l 1 * (1:PowerSeries ℚ)) := by simp [l,map_ofNat]
  change _ * p = _
  rw [hl,hr]
  ext n
  rcases n with _|n
  · norm_num [l,p,stepZero,coeff_one,h]
  rcases n with _|n
  · norm_num [l,p,stepZero,stepSucc,coeff_one,coeff_X,h]
  rcases n with _|n
  · norm_num [l,p,stepZero,stepSucc,coeff_one,coeff_X,h]
  simp only [l,stepSucc,coeff_one,Nat.succ_ne_zero,if_false,p,coeff_mk,h,pow_succ,
    Nat.cast_succ]
  ring
end
end OMA.S_oeis_a127276

namespace OMA.S_oeis_a127276
open Polynomial Matrix
noncomputable section

theorem hankel_formula (n : ℕ) : hankel n = 2^n*(1-(n:ℚ)*(n+1)/4) := by
  obtain ⟨L,hX,hG⟩ := moments
  let F : ℚ[X] →ₗ[ℚ] ℚ := L + (1/4:ℚ) • leval 0 - (1/4:ℚ) • leval 4
  have mon (t : ℕ) : F (X^t) = term t := by
    simp [F,term,hX,leval_apply,smul_eq_mul]
    ring
  have gv (i j : Fin (n+1)) : F (G i.val*G j.val) = gram n i j := by
    simp only [F,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
      leval_apply,eval_mul,hG,G_eval0,G_eval4,gram,of_apply,weight,smul_eq_mul,Fin.val_inj]
    ring
  calc
    hankel n = (Matrix.of fun i j : Fin (n+1) => F (X^(i.val+j.val))).det := by simp [hankel,mon]
    _ = (Matrix.of fun i j : Fin (n+1) => F (G i.val*G j.val)).det := det_orthogonal_basis F _
    _ = (gram n).det := by congr 1; ext i j; exact gv i j
    _ = _ := determinant_gram n
end
end OMA.S_oeis_a127276

theorem OMA.solution : type_of% @OMA.S_oeis_a127276.main :=
  ⟨OMA.S_oeis_a127276.hankel_formula,
   OMA.S_oeis_a127276.closed_generating _ OMA.S_oeis_a127276.hankel_formula⟩
