import OMAStatements.S_oeis_a292502
import Mathlib.Tactic

open OMA.S_oeis_a292502 Filter Topology Finset

namespace LogarithmicCoefficients

private lemma oddBound (k : ℕ) : (2*k-1)*3 ≤ 3^k := by
  cases k with
  | zero => decide
  | succ k =>
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ]; omega

private lemma productBound (L : List ℕ) :
    oddProduct L * 3^L.length ≤ 3^L.sum := by
  induction L with
  | nil => decide
  | cons k L ih =>
    change ((2*k-1)*oddProduct L)*3^(L.length+1) ≤ 3^(k+L.sum)
    rw [pow_succ,pow_add]
    calc
      _ = ((2*k-1)*3)*(oddProduct L*3^L.length) := by ring
      _ ≤ _ := Nat.mul_le_mul (oddBound k) ih

private lemma rectangle (a b : ℕ) : a*b ≤ (a+b)^2/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have h : (a:ℤ)*b*4 ≤ ((a:ℤ)+b)^2 := by nlinarith [sq_nonneg ((a:ℤ)-b)]
  exact_mod_cast h

private lemma coefficientBounds (n : ℕ) (hn : 0 < n) :
    (3:ℝ)^(n^2/4) ≤ term n ∧ term n ≤ (4:ℝ)^n*3^(n^2/4) := by
  classical
  have single (c : Composition n) : (oddProduct c.blocks:ℝ)^c.length ≤ term n := by
    have pos : (0:ℝ)<c.length := by exact_mod_cast c.length_pos_of_pos hn
    have len : (c.length:ℝ)≤n := by exact_mod_cast c.length_le
    calc
      _ ≤ (n:ℝ)/c.length*(oddProduct c.blocks:ℝ)^c.length :=
        le_mul_of_one_le_left (by positivity) ((one_le_div pos).mpr len)
      _ ≤ _ := single_le_sum (f:=fun d : Composition n =>
          (n:ℝ)/d.length*(oddProduct d.blocks:ℝ)^d.length) (fun _ _ => by positivity) (mem_univ c)
  constructor
  · obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      let c : Composition (2*k) := ⟨List.replicate k 2,by simp,by simp [mul_comm]⟩
      have e := single c
      have E : (2*k)^2/4 = k*k := by rw [show (2*k)^2=4*(k*k) by ring]; omega
      simpa [c,Composition.length,oddProduct,E,Nat.cast_pow,←pow_mul] using e
    · subst n
      let c : Composition (2*k+1) := ⟨1::List.replicate k 2,by simp,by simp [mul_comm,add_comm]⟩
      have e := single c
      have E : (2*k+1)^2/4 = k*(k+1) := by rw [show (2*k+1)^2=4*(k*(k+1))+1 by ring]; omega
      simpa [c,Composition.length,oddProduct,E,Nat.cast_pow,←pow_mul] using e
  · have contribution (c : Composition n) :
        (n:ℝ)/c.length*(oddProduct c.blocks:ℝ)^c.length ≤ (n:ℝ)*3^(n^2/4) := by
      have le := c.length_le
      have P : oddProduct c.blocks ≤ 3^(n-c.length) := by
        apply Nat.le_of_mul_le_mul_right (c:=3^c.length) _ (by positivity)
        rw [←pow_add,Nat.sub_add_cancel le]
        simpa [Composition.blocks_length] using productBound c.blocks
      have R : (n-c.length)*c.length ≤ n^2/4 := by
        simpa only [Nat.sub_add_cancel le] using rectangle (n-c.length) c.length
      have X : oddProduct c.blocks ^ c.length ≤ 3^(n^2/4) := by
        calc
          _ ≤ (3^(n-c.length))^c.length := Nat.pow_le_pow_left P _
          _ = _ := (pow_mul _ _ _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by decide) R
      apply mul_le_mul _ (by exact_mod_cast X) (by positivity) (by positivity)
      exact div_le_self (by positivity) (by exact_mod_cast c.length_pos_of_pos hn)
    have top := Finset.sum_le_sum (s:=(univ : Finset (Composition n))) (fun c _ => contribution c)
    have small : ((2:ℝ)^(n-1)) * n ≤ (4:ℝ)^n := by
      calc
        _ ≤ (2:ℝ)^n * 2^n := mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
          (by exact_mod_cast (Nat.lt_two_pow_self.le : n≤2^n)) (by positivity) (by positivity)
        _ = _ := by rw [←mul_pow]; norm_num
    unfold term
    calc
      _ ≤ _ := top
      _ = ((2:ℝ)^(n-1)*n)*3^(n^2/4) := by simp [composition_card]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small (by positivity)

private lemma asymptotic : Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop
    (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
  have inv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have low : Tendsto (fun n : ℕ => (3:ℝ)^((1:ℝ)/4-(1/(n:ℝ))^2)) atTop (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
    have e := (tendsto_const_nhds (x:=(1:ℝ)/4)).sub (inv.pow 2)
    simpa [Function.comp_def] using
      (Real.continuous_const_rpow (by norm_num : (3:ℝ)≠0)).continuousAt.tendsto.comp e
  have high : Tendsto (fun n : ℕ => (4:ℝ)^(1/(n:ℝ))*3^((1:ℝ)/4)) atTop (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
    have e := (Real.continuous_const_rpow (by norm_num : (4:ℝ)≠0)).continuousAt.tendsto.comp inv
    simpa using e.mul_const ((3:ℝ)^((1:ℝ)/4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨lo,_⟩ := coefficientBounds n hn
    have hp : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow (by positivity) lo (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)] at h
    apply le_trans _ h
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have rem : n^2 < (n^2/4+1)*4 := by omega
    have remR : (n:ℝ)^2 < (((n^2/4:ℕ):ℝ)+1)*4 := by exact_mod_cast rem
    field_simp [hp.ne']
    nlinarith only [remR]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨lo,hi⟩ := coefficientBounds n hn
    have hp : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow (le_trans (by positivity) lo) hi (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [Real.mul_rpow (by positivity) (by positivity),
        ←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤4),
        ←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)] at h
    rw [show (n:ℝ)*(1/(n:ℝ)^2)=1/n by field_simp] at h
    apply h.trans (mul_le_mul_of_nonneg_left _ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have rem : n^2/4*4 ≤ n^2 := by omega
    have remR : ((n^2/4:ℕ):ℝ)*4 ≤ (n:ℝ)^2 := by exact_mod_cast rem
    field_simp [hp.ne']
    linarith

end LogarithmicCoefficients

theorem OMA.solution : type_of% @OMA.S_oeis_a292502.main := LogarithmicCoefficients.asymptotic
