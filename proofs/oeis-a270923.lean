import OMAStatements.S_oeis_a270923
import Mathlib.Tactic

open OMA.S_oeis_a270923 Filter Topology Finset

namespace IntegerPartGrowth

private lemma cubeBound (r : ℕ) : r^3 ≤ 3^r := by
  match r with
  | 0 | 1 | 2 => decide
  | k+3 =>
    induction k with
    | zero => decide
    | succ k ih =>
      change (k+4)^3 ≤ 3^(k+3+1)
      rw [pow_succ (3:ℕ) (k+3)]
      nlinarith only [ih,Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3)]

private lemma multiBound (t m : ℕ) : Nat.multichoose t m ≤ t^m := by
  induction m generalizing t with
  | zero => simp
  | succ m hm =>
    induction t with
    | zero => simp
    | succ t ht =>
      rw [Nat.multichoose_succ_succ]
      calc
        _ ≤ t^(m+1)+(t+1)^m := Nat.add_le_add ht (hm (t+1))
        _ ≤ (t+1)^m*t+(t+1)^m := by
          rw [pow_succ]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega) m)) _
        _ = _ := by rw [pow_succ]; ring

private lemma factorBound (t m n : ℕ) (hm : m≤n) : factor t m ≤ (n+1)*t^m := by
  unfold factor
  calc
    _ ≤ ∑ _j ∈ range (m+1), t^m := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
      calc
        _ ≤ t^j*t^(m-j) := Nat.mul_le_mul (Nat.choose_le_pow t j) (multiBound t (m-j))
        _ = t^m := by rw [←pow_add,show j+(m-j)=m by omega]
    _ = (m+1)*t^m := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

private lemma sizeBound (k n m : ℕ) :
    ((k:ℝ)^n)^m ≤ (3:ℝ)^(((k*m:ℕ):ℝ)*(n:ℝ)/3) := by
  have intMax : (k:ℝ) ≤ 3^((k:ℝ)/3) := by
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (by positivity)
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    rw [show (k:ℝ)/3*((3:ℕ):ℝ)=k by ring,Real.rpow_natCast]
    exact_mod_cast cubeBound k
  calc
    _ ≤ ((3^((k:ℝ)/3))^n)^m :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) intMax n) m
    _ = _ := by
      rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
        ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
      push_cast
      congr 1
      ring

private lemma productBound {n : ℕ} (m : Fin n → Fin (n+1)) (hm : m ∈ multiplicities n) :
    (∏ i : Fin n, (factor ((i.val+1)^n) (m i).val:ℝ)) ≤
      ((n:ℝ)+1)^n * 3^((n:ℝ)^2/3) := by
  let deg (i : Fin n) : ℝ := ((i.val+1)*(m i).val:ℕ)
  have total : (∑ i, deg i) = (n:ℝ) := by
    dsimp [deg]
    exact_mod_cast (mem_filter.mp hm).2
  have part (i : Fin n) : (factor ((i.val+1)^n) (m i).val:ℝ) ≤
      ((n:ℝ)+1)*3^(deg i*n/3) := by
    have h := factorBound ((i.val+1)^n) (m i).val n (Nat.le_of_lt_succ (m i).isLt)
    have h' : (factor ((i.val+1)^n) (m i).val:ℝ) ≤
        ((n:ℝ)+1)*((((i.val+1:ℕ):ℝ)^n)^(m i).val) := by exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_left (sizeBound (i.val+1) n (m i).val) (by positivity))
  calc
    _ ≤ ∏ i : Fin n, (((n:ℝ)+1)*3^(deg i*n/3)) :=
      prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => part i)
    _ = _ := by
      rw [prod_mul_distrib,←Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<3)]
      simp only [prod_const,card_univ,Fintype.card_fin,←sum_div,←sum_mul,total,sq]

private lemma upper (n : ℕ) :
    (term n:ℝ) ≤ ((n:ℝ)+1)^(2*n)*3^((n:ℝ)^2/3) := by
  let b : ℝ := (n:ℝ)+1
  have count : ((multiplicities n).card:ℝ) ≤ b^n := by
    have bound : (multiplicities n).card ≤ (n+1)^n := by
      simpa [multiplicities,Fintype.card_fun] using
        (card_filter_le (s:=(univ : Finset (Fin n → Fin (n+1)))) (fun m => (∑ i : Fin n,(i.val+1)*(m i).val)=n))
    dsimp [b]
    exact_mod_cast bound
  unfold term
  push_cast
  calc
    _ ≤ ∑ _m ∈ multiplicities n, b^n*3^((n:ℝ)^2/3) := sum_le_sum (fun m hm => productBound m hm)
    _ = ((multiplicities n).card:ℝ)*(b^n*3^((n:ℝ)^2/3)) := by simp
    _ ≤ b^n*(b^n*3^((n:ℝ)^2/3)) := mul_le_mul_of_nonneg_right count (by dsimp [b]; positivity)
    _ = _ := by change _ = b^(2*n)*_; rw [two_mul,pow_add]; ring

private lemma strictGap : (3:ℝ)^((1:ℝ)/3) < Real.exp (Real.exp (-1)) := by
  have h : 1 < 3 / Real.exp 1 := (lt_div_iff₀ (Real.exp_pos 1)).mpr (by simpa using Real.exp_one_lt_three)
  have lg := Real.log_lt_sub_one_of_pos (by positivity : 0 < 3 / Real.exp 1) (ne_of_gt h)
  rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne',Real.log_exp] at lg
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3),Real.exp_lt_exp,Real.exp_neg]
  rw [div_eq_mul_inv] at lg
  linarith only [lg]

end IntegerPartGrowth

open IntegerPartGrowth

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270923.main) := by
  intro proposed
  have inv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have lg : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  have logSmall : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
    have bound : Tendsto (fun n : ℕ => Real.log 2/(n:ℝ)+Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (inv.const_mul (Real.log 2)).add lg
    apply squeeze_zero' _ _ bound
    · exact Eventually.of_forall (fun n => div_nonneg
        (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))) (by positivity))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have h : (1:ℝ)≤n := by exact_mod_cast hn
      rw [←add_div,←Real.log_mul (by norm_num) (by linarith : (n:ℝ)≠0)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Real.log_le_log (by positivity) (by linarith)
  have high : Tendsto (fun n : ℕ => Real.exp (2*(Real.log ((n:ℝ)+1)/(n:ℝ)))*3^((1:ℝ)/3))
      atTop (𝓝 ((3:ℝ)^((1:ℝ)/3))) := by
    have e := (Real.continuous_exp.tendsto _).comp (logSmall.const_mul 2)
    simpa [Function.comp_def] using e.mul_const ((3:ℝ)^((1:ℝ)/3))
  have upperEventually : ∀ᶠ n : ℕ in atTop, (term n:ℝ)^(1/(n:ℝ)^2) ≤
      Real.exp (2*(Real.log ((n:ℝ)+1)/(n:ℝ)))*3^((1:ℝ)/3) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow (by positivity) (upper n) (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by positivity),
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤3)] at h
    have A : (((n:ℝ)+1)^(((2*n:ℕ):ℝ)*(1/(n:ℝ)^2))) =
        Real.exp (2*(Real.log ((n:ℝ)+1)/(n:ℝ))) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      push_cast
      field_simp
    have B : (n:ℝ)^2/3*(1/(n:ℝ)^2)=1/3 := by field_simp
    rwa [A,B] at h
  exact (not_lt_of_ge (le_of_tendsto_of_tendsto proposed high upperEventually)) strictGap
