import OMAStatements.S_oeis_a292500
import Mathlib.Tactic

open OMA.S_oeis_a292500 Filter Topology Finset

namespace ExponentialCoefficients

private def area (n : ℕ) := n^2/4

private lemma rectangle (a b : ℕ) : a*b ≤ area (a+b) := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have h : (a:ℤ)*b*4 ≤ ((a:ℤ)+b)^2 := by nlinarith [sq_nonneg ((a:ℤ)-b)]
  exact_mod_cast h

private lemma areaAdd (a b : ℕ) : area a + area b ≤ area (a+b) := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  unfold area
  nlinarith only [Nat.div_mul_le_self (a^2) 4,Nat.div_mul_le_self (b^2) 4,Nat.zero_le (a*b)]

private lemma pointwise (k : ℕ) : (2*k-1)*3 ≤ 3^k := by
  cases k with
  | zero => decide
  | succ k => induction k with
    | zero => decide
    | succ k ih => rw [pow_succ]; omega

private lemma listBound (L : List ℕ) :
    (L.map (fun k => 2*k-1)).prod * 3^L.length ≤ 3^L.sum := by
  induction L with
  | nil => decide
  | cons k L ih =>
    change ((2*k-1)*(L.map (fun k => 2*k-1)).prod)*3^(L.length+1) ≤ 3^(k+L.sum)
    rw [pow_succ,pow_add]
    calc
      _ = ((2*k-1)*3)*((L.map (fun k => 2*k-1)).prod*3^L.length) := by ring
      _ ≤ _ := Nat.mul_le_mul (pointwise k) ih

private lemma weightUpper {n : ℕ} (c : Composition n) : weight c ≤ 3^area n := by
  have le := c.length_le
  have P : (c.blocks.map (fun k => 2*k-1)).prod ≤ 3^(n-c.length) := by
    apply Nat.le_of_mul_le_mul_right (c:=3^c.length) _ (by positivity)
    rw [←pow_add,Nat.sub_add_cancel le]
    simpa [Composition.blocks_length] using listBound c.blocks
  have R : (n-c.length)*c.length ≤ area n := by
    simpa only [Nat.sub_add_cancel le] using rectangle (n-c.length) c.length
  calc
    weight c ≤ (3^(n-c.length))^c.length := Nat.pow_le_pow_left P _
    _ = _ := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) R

private lemma witness (n : ℕ) : ∃ c : Composition n, 3^area n ≤ 3^n*weight c := by
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    let c : Composition (2*k) := ⟨List.replicate k 2,by simp,by simp [mul_comm]⟩
    have E : area (2*k)=k*k := by unfold area; rw [show (2*k)^2=4*(k*k) by ring]; omega
    refine ⟨c,?_⟩
    have W : weight c=3^area (2*k) := by simp [c,weight,Composition.length,E,←pow_mul]
    rw [W]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  · subst n
    let c : Composition (2*k+1) := ⟨1::List.replicate k 2,by simp,by simp [mul_comm,add_comm]⟩
    have E : area (2*k+1)=k*(k+1) := by unfold area; rw [show (2*k+1)^2=4*(k*(k+1))+1 by ring]; omega
    refine ⟨c,?_⟩
    have W : weight c=3^area (2*k+1) := by simp [c,weight,Composition.length,E,←pow_mul]
    rw [W]
    exact Nat.le_mul_of_pos_left _ (by positivity)

private lemma logNonneg (n : ℕ) : 0 ≤ logCoeff n := by
  unfold logCoeff
  exact sum_nonneg (fun _ _ => by positivity)

private lemma logBounds (n : ℕ) :
    logCoeff n ≤ (2:ℝ)^n*3^area n ∧
    (0<n → (3:ℝ)^area n ≤ (3:ℝ)^(2*n)*logCoeff n) := by
  classical
  have upper (c : Composition n) : (weight c:ℝ)/c.length ≤ (3:ℝ)^area n := by
    by_cases h : c.length=0
    · simp [h]
    · have hlen : (1:ℝ)≤c.length := by exact_mod_cast (Nat.pos_of_ne_zero h)
      exact (div_le_self (by positivity) hlen).trans (by exact_mod_cast weightUpper c)
  constructor
  · calc
      logCoeff n ≤ ∑ _c : Composition n, (3:ℝ)^area n := sum_le_sum (fun c _ => upper c)
      _ = (2:ℝ)^(n-1)*3^area n := by simp [composition_card]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  · intro hn
    obtain ⟨c,hc⟩ := witness n
    have p : (0:ℝ)<c.length := by exact_mod_cast c.length_pos_of_pos hn
    have size : (c.length:ℝ) ≤ (3:ℝ)^n := by
      exact_mod_cast (c.length_le.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by decide : 2≤3) n)))
    have sub : (weight c:ℝ)/c.length ≤ logCoeff n :=
      single_le_sum (f:=fun d : Composition n => (weight d:ℝ)/d.length)
        (fun _ _ => by positivity) (mem_univ c)
    have W : (weight c:ℝ) ≤ (3:ℝ)^n*logCoeff n := by
      calc
        _ = (c.length:ℝ)*((weight c:ℝ)/c.length) := by field_simp
        _ ≤ _ := mul_le_mul size sub (by positivity) (by positivity)
    calc
      (3:ℝ)^area n ≤ (3:ℝ)^n*(weight c:ℝ) := by exact_mod_cast hc
      _ ≤ (3:ℝ)^n*((3:ℝ)^n*logCoeff n) := mul_le_mul_of_nonneg_left W (by positivity)
      _ = _ := by rw [two_mul,pow_add]; ring

private lemma outerBound (L : List ℕ) :
    (L.map logCoeff).prod ≤ (2:ℝ)^L.sum*3^area L.sum := by
  induction L with
  | nil => norm_num [area]
  | cons k L ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    calc
      _ ≤ ((2:ℝ)^k*3^area k)*((2:ℝ)^L.sum*3^area L.sum) :=
        mul_le_mul (logBounds k).1 ih
          (List.prod_nonneg (fun x hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact logNonneg i))
          (by positivity)
      _ = (2:ℝ)^(k+L.sum)*3^(area k+area L.sum) := by rw [pow_add,pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (areaAdd k L.sum)) (by positivity)

private lemma coefficientBounds (n : ℕ) (hn : 0<n) :
    (3:ℝ)^area n ≤ (3:ℝ)^(2*n)*term n ∧ term n ≤ (4:ℝ)^n*3^area n ∧ 0 ≤ term n := by
  classical
  have nonneg (c : Composition n) : 0 ≤ (c.blocks.map logCoeff).prod :=
    List.prod_nonneg (fun x hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact logNonneg i)
  have onePart : logCoeff n ≤ term n := by
    let c : Composition n := ⟨[n],by simpa using hn,by simp⟩
    have h := single_le_sum (f:=fun d : Composition n =>
      (d.blocks.map logCoeff).prod/(d.length.factorial:ℝ))
      (fun d _ => div_nonneg (nonneg d) (by positivity)) (mem_univ c)
    simpa [c,Composition.length,term] using h
  refine ⟨((logBounds n).2 hn).trans (mul_le_mul_of_nonneg_left onePart (by positivity)),?_,?_⟩
  · have h (c : Composition n) : (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ) ≤
        (2:ℝ)^n*3^area n := by
      have fact : (1:ℝ) ≤ c.length.factorial := by exact_mod_cast Nat.factorial_pos c.length
      exact (div_le_self (nonneg c) fact).trans (by simpa using outerBound c.blocks)
    calc
      term n ≤ ∑ _c : Composition n, (2:ℝ)^n*3^area n := sum_le_sum (fun c _ => h c)
      _ = (2:ℝ)^(n-1)*((2:ℝ)^n*3^area n) := by simp [composition_card]
      _ ≤ (2:ℝ)^n*((2:ℝ)^n*3^area n) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = _ := by rw [←mul_assoc,←mul_pow]; norm_num
  · exact (logNonneg n).trans onePart

private lemma asymptotic : Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop
    (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
  have inv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have low : Tendsto (fun n : ℕ => (3:ℝ)^((1:ℝ)/4-(1/(n:ℝ))^2-2*(1/(n:ℝ)))) atTop
      (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
    have e := ((tendsto_const_nhds (x:=(1:ℝ)/4)).sub (inv.pow 2)).sub (inv.const_mul 2)
    simpa [Function.comp_def] using
      (Real.continuous_const_rpow (by norm_num : (3:ℝ)≠0)).continuousAt.tendsto.comp e
  have high : Tendsto (fun n : ℕ => (4:ℝ)^(1/(n:ℝ))*3^((1:ℝ)/4)) atTop
      (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
    have e := (Real.continuous_const_rpow (by norm_num : (4:ℝ)≠0)).continuousAt.tendsto.comp inv
    simpa using e.mul_const ((3:ℝ)^((1:ℝ)/4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨lo,_,_⟩ := coefficientBounds n hn
    have hp : (0:ℝ)<n := by exact_mod_cast hn
    have baseLo : (3:ℝ)^((area n:ℝ)-((2*n:ℕ):ℝ)) ≤ term n := by
      rw [Real.rpow_sub (by norm_num),Real.rpow_natCast,Real.rpow_natCast,div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using lo
    have h := Real.rpow_le_rpow (by positivity) baseLo (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤3)] at h
    apply le_trans _ h
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have rem : n^2 < (area n+1)*4 := by unfold area; omega
    have remR : (n:ℝ)^2 < ((area n:ℝ)+1)*4 := by exact_mod_cast rem
    push_cast
    field_simp [hp.ne']
    nlinarith only [remR]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨_,hi,nonneg⟩ := coefficientBounds n hn
    have hp : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow nonneg hi (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [Real.mul_rpow (by positivity) (by positivity),
        ←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤4),
        ←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)] at h
    rw [show (n:ℝ)*(1/(n:ℝ)^2)=1/n by field_simp] at h
    apply h.trans (mul_le_mul_of_nonneg_left _ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have rem : area n*4 ≤ n^2 := by unfold area; omega
    have remR : (area n:ℝ)*4 ≤ (n:ℝ)^2 := by exact_mod_cast rem
    field_simp [hp.ne']
    linarith

end ExponentialCoefficients

theorem OMA.solution : type_of% @OMA.S_oeis_a292500.main := ExponentialCoefficients.asymptotic
