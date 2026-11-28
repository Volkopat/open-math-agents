import OMAStatements.S_mo_255146
import Mathlib

/-!
# Leading principal Sylvester–Kac blocks

Question: Sihuang Hu, MathOverflow 255146.
https://mathoverflow.net/questions/255146
Credit: @connoranderson.

The differential equation of the binary Krawtchouk generating function
agrees coefficient by coefficient with the continuant recurrence of the
leading tridiagonal blocks. The identity holds for all complex evaluation
points. To bound the roots, rescale coordinate i by t^i, where
t = r / sqrt(r(n-r)), and apply Gershgorin's theorem.

For the relation of Kac matrices to the classical Krawtchouk system, see
Philip Feinsilver and Jerzy Kocik, “Krawtchouk polynomials and Krawtchouk
matrices.” https://arxiv.org/abs/quant-ph/0702073
-/
namespace OMA.S_mo_255146
noncomputable section
open PowerSeries
private theorem choose_step (a : ℂ) (k : ℕ) :
    Ring.choose a (k+1)*((k:ℂ)+1)= (a-k)*Ring.choose a k := by
  have h := Ring.choose_smul_choose (r:=a) (n:=k+1) (k:=k) (by omega)
  simpa [Nat.choose_succ_self_right,Ring.choose_one_right,nsmul_eq_mul,mul_comm] using h

private def factor (a c : ℂ) := rescale c (binomialSeries ℂ a)

private theorem factor_coeff (a c : ℂ) (k : ℕ) : coeff k (factor a c) =
    c^k*Ring.choose a k := by simp [factor,coeff_rescale,smul_eq_mul,mul_comm]

private theorem const_der (p : ℂ⟦X⟧) : constantCoeff (derivative ℂ p) = coeff 1 p := by
  rw [←coeff_zero_eq_constantCoeff_apply,coeff_derivative]
  simp

private theorem factor_diff (a c : ℂ) :
    (1+C c*X)*derivative ℂ (factor a c) = C (c*a)*factor a c := by
  ext k
  cases k with
  | zero => simp [add_mul,mul_assoc,const_der,factor_coeff]
  | succ k =>
    simp only [add_mul,one_mul,mul_assoc,coeff_C_mul,map_add,coeff_succ_X_mul,
      coeff_derivative,factor_coeff,Nat.cast_succ,pow_succ]
    have h := choose_step a (k+1)
    push_cast at h
    linear_combination (norm := ring) c^k*c*c*h

private def gen (n : ℕ) (z : ℂ) := factor (((n:ℂ)-1-z)/2) (-1) *
    factor (((n:ℂ)-1+z)/2) 1

private theorem gcoeff (n : ℕ) (z : ℂ) (r : ℕ) :
    coeff r (gen n z) = krawtchouk n z r := by simp [gen,factor,krawtchouk]

private theorem gen_diff (n : ℕ) (z : ℂ) :
    (1-X^2)*derivative ℂ (gen n z) = (C z - C ((n:ℂ)-1)*X)*gen n z := by
  let a : ℂ := ((n:ℂ)-1-z)/2
  let b : ℂ := ((n:ℂ)-1+z)/2
  have hA : (1-X)*derivative ℂ (factor a (-1)) = -C a * factor a (-1) := by
    simpa [sub_eq_add_neg] using factor_diff a (-1)
  have hB : (1+X)*derivative ℂ (factor b 1) = C b * factor b 1 := by
    simpa using factor_diff b 1
  have hsub : b-a=z := by dsimp [a,b];ring
  have hadd : a+b=(n:ℂ)-1 := by dsimp [a,b];ring
  change (1-X^2)*derivative ℂ (factor a (-1)*factor b 1) =
    (C z-C ((n:ℂ)-1)*X)*(factor a (-1)*factor b 1)
  rw [←hsub,←hadd,map_sub,map_add,Derivation.leibniz]
  simp only [smul_eq_mul]
  linear_combination (norm := ring) ((1+X)*factor b 1)*hA + ((1-X)*factor a (-1))*hB

theorem kraw_zero (n : ℕ) (z : ℂ) : krawtchouk n z 0=1 := by
  simp [krawtchouk]
  rw [←coeff_zero_eq_constantCoeff_apply,coeff_rescale]
  simp

theorem kraw_one (n : ℕ) (z : ℂ) : krawtchouk n z 1=z := by
  have h := congrArg (coeff 0 (R:=ℂ)) (gen_diff n z)
  have hz0 : constantCoeff (gen n z) = 1 := by
    rw [←coeff_zero_eq_constantCoeff_apply,gcoeff,kraw_zero]
  simpa [sub_mul,mul_assoc,const_der,gcoeff,hz0] using h

theorem kraw_step (n : ℕ) (z : ℂ) (r : ℕ) :
    ((r:ℂ)+2)*krawtchouk n z (r+2) =
      z*krawtchouk n z (r+1)-((n:ℂ)-1-r)*krawtchouk n z r := by
  have h := congrArg (coeff (r+1) (R:=ℂ)) (gen_diff n z)
  simp only [sub_mul,one_mul,map_sub,coeff_derivative,coeff_C_mul,mul_assoc,coeff_succ_X_mul,
    gcoeff,Nat.cast_succ] at h
  cases r with
  | zero =>
    norm_num [kraw_zero,coeff_X_pow_mul',coeff_derivative,gcoeff] at h ⊢
    linear_combination (norm := ring) h
  | succ r =>
    rw [show r+1+1=r+2 by omega,coeff_X_pow_mul] at h
    simp only [coeff_derivative,gcoeff,Nat.cast_succ] at h
    push_cast
    linear_combination (norm := ring) h
end
end OMA.S_mo_255146

namespace OMA.S_mo_255146
noncomputable section
open Matrix Finset
def pencil (n r : ℕ) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ := of fun i j =>
  if i=j then z else if j.val=i.val+1 then -((n:ℂ)-1-i.val) else if i.val=j.val+1 then -(i.val:ℂ) else 0

theorem char_eval (n r : ℕ) (z : ℂ) : (clement n r).charpoly.eval z = (pencil n r z).det := by
  rw [eval_charpoly]
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp [clement,pencil]
  · simp [clement,pencil,h]
    split_ifs <;> simp

private theorem plus_sign (a : ℕ) : (-1:ℂ)^(a+a)=1 := by rw [pow_add,← mul_pow]; norm_num
private theorem minus_sign (a : ℕ) : (-1:ℂ)^(a+1+a)= -1 := by rw [show a+1+a=a+a+1 by omega,pow_succ,plus_sign];norm_num

theorem det_step (n r : ℕ) (z : ℂ) : (pencil n (r+2) z).det =
    z*(pencil n (r+1) z).det - (r+1:ℂ)*(n-1-r)*(pencil n r z).det := by
  let A := pencil n (r+2) z
  let u := Fin.last (r+1)
  let t := Fin.last r
  let v : Fin (r+2) := t.castSucc
  let B := A.submatrix Fin.castSucc v.succAbove
  have principal : A.submatrix Fin.castSucc Fin.castSucc = pencil n (r+1) z := by
    ext i j
    simp [A,pencil]
  have minor : B.submatrix Fin.castSucc Fin.castSucc = pencil n r z := by
    ext i j
    simp only [B,Matrix.submatrix_apply,v,Fin.castSucc_succAbove_castSucc,t,Fin.succAbove_last]
    simp [A,pencil]
  have hole : v.succAbove t = u := by
    rw [Fin.succAbove_of_le_castSucc v t (by exact le_rfl)]
    rfl
  have bm : B.det = -((n:ℂ)-1-r)*(pencil n r z).det := by
    rw [det_succ_column B t,Finset.sum_eq_single t]
    · rw [show t.succAbove = Fin.castSucc by simp [t],minor]
      simp [B,Matrix.submatrix_apply,hole,A,u,t,pencil,Fin.ext_iff]
    · intro i _ hi
      have hi' : i.val<r := by by_contra! e; exact hi (Fin.ext (by dsimp [t];omega))
      have e : B i t=0 := by
        simp only [B,Matrix.submatrix_apply,hole,A,u,pencil,of_apply,Fin.ext_iff,Fin.val_castSucc,Fin.val_last]
        split_ifs <;> first | rfl | omega
      rw [e,mul_zero,zero_mul]
    · simp
  change A.det=_
  rw [det_succ_row A u,Fin.sum_univ_castSucc,Finset.sum_eq_single t]
  · rw [show u.succAbove = Fin.castSucc by simp [u]]
    change (-1:ℂ)^(r+1+r) * A u v * B.det +
      (-1)^(r+1+(r+1)) * A u u * (A.submatrix Fin.castSucc Fin.castSucc).det = _
    rw [minus_sign,plus_sign,principal,bm]
    have el : A u v= -((r:ℂ)+1) := by
      simp only [A,u,v,t,pencil,of_apply,Fin.ext_iff,Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
      split_ifs <;> first | rfl | omega
    have ed : A u u=z := by simp [A,pencil]
    rw [el,ed]
    ring
  · intro i _ hi
    have hi' : i.val<r := by by_contra! e;exact hi (Fin.ext (by dsimp [t];omega))
    have e : A u i.castSucc=0 := by
      simp only [A,u,pencil,of_apply,Fin.ext_iff,Fin.val_castSucc,Fin.val_last]
      split_ifs <;> first | rfl | omega
    rw [e,mul_zero,zero_mul]
  · simp
end
end OMA.S_mo_255146

namespace OMA.S_mo_255146
noncomputable section
open Matrix

theorem kraw_formula (n : ℕ) (z : ℂ) (r : ℕ) :
    (clement n r).charpoly.eval z = (r.factorial:ℂ)*krawtchouk n z r := by
  rw [char_eval]
  induction r using Nat.twoStepInduction with
  | zero => simp [kraw_zero]
  | one => simp [pencil,kraw_one]
  | more r h₀ h₁ =>
    rw [det_step,h₀,h₁]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    linear_combination (norm := ring) -((r:ℂ)+1)*(r.factorial:ℂ)*kraw_step n z r
end
end OMA.S_mo_255146

namespace OMA.S_mo_255146
noncomputable section
open Matrix Finset

private theorem single_bound (r k : ℕ) (u : ℝ) (hu : 0≤u) :
    (∑ j : Fin r, if j.val=k then u else 0) ≤ u := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j=k then u else 0)]
  simp only [Finset.sum_ite_eq',Finset.mem_range]
  split_ifs <;> first | rfl | exact hu

theorem eigen_bound (n r : ℕ) (hr : 1<r) (hn : 2*r≤n) (z : ℂ)
    (hz : (clement n r).charpoly.eval z=0) :
    ‖z‖ ≤ 2*Real.sqrt ((r:ℝ)*(n-r)) := by
  have hrpos : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hnr : (r:ℝ) ≤ (n:ℝ)-r := by
    have hh : 2*(r:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hp : 0 < (r:ℝ)*((n:ℝ)-r) := mul_pos hrpos (hrpos.trans_le hnr)
  let w := Real.sqrt ((r:ℝ)*(n-r))
  have hw : 0<w := Real.sqrt_pos.mpr hp
  have hw2 : w^2=(r:ℝ)*(n-r) := Real.sq_sqrt hp.le
  let t := (r:ℝ)/w
  have ht : 0<t := div_pos hrpos hw
  have ht1 : t≤1 := by
    apply (div_le_one hw).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnr hrpos.le]
  have wt : w*t=r := by dsimp [t];field_simp
  have ut : ((n:ℝ)-r)*t=w := by dsimp [t];field_simp;nlinarith
  have tc : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  let D := diagonal fun i : Fin r => (t:ℂ)^i.val
  let E := diagonal fun i : Fin r => ((t:ℂ)^i.val)⁻¹
  let S := E * clement n r * D
  have de : D*E=1 := by simp [D,E,diagonal_mul_diagonal,tc]
  have ch : S.charpoly=(clement n r).charpoly := by
    change (E*clement n r*D).charpoly=_
    rw [charpoly_mul_comm,←Matrix.mul_assoc,de,one_mul]
  have eig : Module.End.HasEigenvalue S.toLin' z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,Matrix.charpoly_toLin']
    rw [ch]
    exact hz
  obtain ⟨i,hi⟩ := eigenvalue_mem_ball eig
  have entry (i j : Fin r) : S i j =
      if j.val=i.val+1 then ((n:ℂ)-1-i.val)*t else
      if i.val=j.val+1 then (i.val:ℂ)/t else 0 := by
    simp only [S,D,E,mul_diagonal,diagonal_mul,clement,of_apply]
    split_ifs with h g
    · rw [h,pow_succ]
      field_simp
    · rw [g,pow_succ]
      field_simp
    · ring
  have iid : S i i=0 := by simp [entry]
  rw [Metric.mem_closedBall,dist_eq_norm,iid,sub_zero] at hi
  have hupper : 0≤(n:ℝ)-1-i.val := by
    have h0 : i.val+1≤n := by have := i.isLt;omega
    have h₁ : (i.val:ℝ)+1≤n := by exact_mod_cast h0
    linarith
  let U := ((n:ℝ)-1-i.val)*t
  let V := (i.val:ℝ)/t
  have hu : 0≤U := mul_nonneg hupper ht.le
  have hv : 0≤V := div_nonneg (by positivity) ht.le
  have plusNorm : ‖((n:ℂ)-1-i.val)*t‖=U := by
    rw [show ((n:ℂ)-1-i.val)*t = (U:ℂ) by dsimp [U];push_cast <;> ring,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  have minusNorm : ‖(i.val:ℂ)/t‖=V := by
    rw [show (i.val:ℂ)/t=(V:ℂ) by dsimp [V];push_cast <;> rfl,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv]
  have row (j : Fin r) : ‖S i j‖ ≤ (if j.val=i.val+1 then U else 0) +
      (if j.val=i.val-1 then V else 0) := by
    rw [entry]
    by_cases h₁ : j.val=i.val+1
    · simp only [if_pos h₁,if_neg (show ¬ j.val=i.val-1 by omega),plusNorm,add_zero,le_refl]
    · by_cases h₂ : i.val=j.val+1
      · simp only [if_neg h₁,if_pos h₂,if_pos (show j.val=i.val-1 by omega),minusNorm,zero_add,le_refl]
      · simp only [h₁,h₂,if_false,norm_zero,zero_add]
        split_ifs <;> positivity
  apply hi.trans
  calc
    _ ≤ ∑ j : Fin r, ‖S i j‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ j : Fin r, ((if j.val=i.val+1 then U else 0)+(if j.val=i.val-1 then V else 0)) :=
      Finset.sum_le_sum fun j _ => row j
    _ ≤ U+V := by rw [Finset.sum_add_distrib];exact add_le_add (single_bound _ _ _ hu) (single_bound _ _ _ hv)
    _ ≤ 2*w := by
      dsimp [U,V]
      apply (mul_le_mul_iff_left₀ ht).mp
      have ht2 : t*t≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (by linarith : 0≤1+t)]
      have hgap : (i.val:ℝ) ≤ r := by exact_mod_cast i.isLt.le
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hgap) (sub_nonneg.mpr ht2),
        congrArg (·*t) ut]
end
end OMA.S_mo_255146

theorem OMA.solution : type_of% @OMA.S_mo_255146.main := by
  intro n r hr hn z
  exact ⟨OMA.S_mo_255146.kraw_formula n z r, OMA.S_mo_255146.eigen_bound n r hr hn z⟩
