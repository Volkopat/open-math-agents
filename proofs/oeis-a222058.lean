import OMAStatements.S_oeis_a222058
import Mathlib.Tactic

open OMA.S_oeis_a222058 Finset

namespace HarmonicGeometric

private noncomputable def H (k : ℕ) : ℝ := harmonic k
private noncomputable def w (k : ℕ) : ℝ := (1/2)^(k+1)
private noncomputable def b (j k : ℕ) : ℝ := (k.choose j:ℝ)*w k
private noncomputable def h (j k : ℕ) : ℝ := b j k*H k

private lemma Hsucc (k : ℕ) : H (k+1) = H k + 1/((k:ℝ)+1) := by
  simp [H,harmonic_succ,one_div]

private lemma Hbound (k : ℕ) : 0 ≤ H k ∧ H k ≤ k := by
  induction k with
  | zero => simp [H]
  | succ k ih =>
    rw [Hsucc,Nat.cast_succ]
    have hi : 1/((k:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by simpa using (Nat.cast_nonneg (R:=ℝ) k))
    constructor
    · exact add_nonneg ih.1 (by positivity)
    · linarith only [ih.2,hi]

private lemma wpos (k : ℕ) : 0 ≤ w k := by unfold w; positivity
private lemma bpos (j k : ℕ) : 0 ≤ b j k := mul_nonneg (by positivity) (wpos k)

private lemma major (j : ℕ) : Summable (fun k : ℕ => (k:ℝ)^j*w k) := by
  have q := (summable_pow_mul_geometric_of_norm_lt_one j (show ‖(1/2:ℝ)‖<1 by norm_num)).mul_right (1/2)
  simpa [w,pow_succ,mul_assoc] using q

private lemma sumB (j : ℕ) : Summable (b j) := by
  apply Summable.of_nonneg_of_le (bpos j) _ (major j)
  intro k
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow k j) (wpos k)

private lemma sumH (j : ℕ) : Summable (h j) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (bpos j k) (Hbound k).1) _ (major (j+1))
  intro k
  calc
    h j k ≤ ((k:ℝ)^j*w k)*k := by
      apply mul_le_mul _ (Hbound k).2 (Hbound k).1 (mul_nonneg (by positivity) (wpos k))
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow k j) (wpos k)
    _ = _ := by rw [pow_succ]; ring

private lemma wsucc (k : ℕ) : w (k+1) = w k/2 := by unfold w; rw [pow_succ]; ring

private lemma bshift (j k : ℕ) : b (j+1) (k+1) = (b (j+1) k + b j k)/2 := by
  simp only [b,Nat.choose_succ_succ,Nat.cast_add,wsucc]
  ring

private lemma mass (j : ℕ) : HasSum (b j) 1 := by
  induction j with
  | zero =>
    have q := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).mul_right (1/2)
    rw [show ((1:ℝ)-1/2)⁻¹*(1/2)=1 by norm_num] at q
    exact q.congr_fun (fun k => by simp [b,w,pow_succ])
  | succ j ih =>
    have z := (sumB (j+1)).tsum_eq_zero_add
    have shifted := (((sumB (j+1)).hasSum.add ih).div_const 2).congr_fun (bshift j)
    rw [shifted.tsum_eq] at z
    have first : b (j+1) 0 = 0 := by simp [b]
    rw [first] at z
    have total : ∑' k, b (j+1) k = 1 := by linarith
    exact total ▸ (sumB (j+1)).hasSum

private lemma logseries : HasSum (fun k : ℕ => w k/((k:ℝ)+1)) (Real.log 2) := by
  have q := Real.hasSum_pow_div_log_of_abs_lt_one (x:=(1/2:ℝ)) (by norm_num)
  have eq : (1:ℝ)-1/2=2⁻¹ := by norm_num
  rw [eq,Real.log_inv,neg_neg] at q
  exact q

private lemma initial : HasSum (h 0) (Real.log 2) := by
  have shift (k : ℕ) : h 0 (k+1) = (h 0 k + w k/((k:ℝ)+1))/2 := by
    simp only [h,b,Nat.choose_zero_right,Nat.cast_one,one_mul,wsucc,Hsucc]
    ring
  have z := (sumH 0).tsum_eq_zero_add
  have q := (((sumH 0).hasSum.add logseries).div_const 2).congr_fun shift
  rw [q.tsum_eq] at z
  have first : h 0 0=0 := by simp [h,H]
  rw [first] at z
  have total : ∑' k, h 0 k = Real.log 2 := by linarith
  exact total ▸ (sumH 0).hasSum

private lemma chooseRatio (k j : ℕ) :
    ((k+1).choose (j+1):ℝ)/((k:ℝ)+1) = (k.choose j:ℝ)/((j:ℝ)+1) := by
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  have q := Nat.add_one_mul_choose_eq k j
  exact_mod_cast (by simpa [mul_comm] using q.symm :
    (k+1).choose (j+1)*(j+1)=k.choose j*(k+1))

private lemma hshift (j k : ℕ) : h (j+1) (k+1) =
    (h (j+1) k + h j k + b j k/((j:ℝ)+1))/2 := by
  have e : b (j+1) (k+1)/((k:ℝ)+1) = b j k/((j:ℝ)+1)/2 := by
    unfold b
    rw [wsucc]
    linear_combination (w k/2)*chooseRatio k j
  unfold h
  rw [Hsucc,mul_add,show b (j+1) (k+1)*(1/((k:ℝ)+1)) = b (j+1) (k+1)/((k:ℝ)+1) by ring,e,bshift]
  ring

private lemma moment (j : ℕ) : HasSum (h j) (H j+Real.log 2) := by
  induction j with
  | zero => simpa [H] using initial
  | succ j ih =>
    have z := (sumH (j+1)).tsum_eq_zero_add
    have both := ((sumH (j+1)).hasSum.add ih).add ((mass j).div_const ((j:ℝ)+1))
    have q := (both.div_const 2).congr_fun (hshift j)
    rw [q.tsum_eq] at z
    have first : h (j+1) 0=0 := by simp [h,b]
    rw [first] at z
    have total : ∑' k, h (j+1) k = H (j+1)+Real.log 2 := by rw [Hsucc]; linarith
    exact total ▸ (sumH (j+1)).hasSum

private lemma centered (j : ℕ) :
    HasSum (fun k : ℕ => (k.choose j:ℝ)*w k*(H k-Real.log 2)) (H j) := by
  have q := (moment j).sub ((mass j).mul_right (Real.log 2))
  have e : H j+Real.log 2-1*Real.log 2 = H j := by ring
  rw [e] at q
  exact q.congr_fun (fun k => by unfold h b; ring)

private lemma firstStirling (j : ℕ) : (Nat.stirlingFirst (j+1) 2:ℝ) = j.factorial*H j := by
  induction j with
  | zero => norm_num [Nat.stirlingFirst,H]
  | succ j ih =>
    rw [Nat.stirlingFirst_succ_succ (j+1) 1,Nat.stirlingFirst_one_right,Nat.factorial_succ,Hsucc]
    push_cast
    rw [ih]
    field_simp
    <;> ring

private def basis (k j : ℕ) : ℝ := (j.factorial:ℝ)*(k.choose j:ℝ)
private def stir (n j : ℕ) : ℝ := Nat.stirlingSecond n j

private lemma basisStep (k j : ℕ) : (j:ℝ)*basis k j + basis k (j+1) = k*basis k j := by
  have a := Nat.add_one_mul_choose_eq k j
  rw [Nat.choose_succ_succ] at a
  have q : ((k:ℝ)+1)*(k.choose j:ℝ) =
      ((k.choose j:ℝ)+(k.choose (j+1):ℝ))*((j:ℝ)+1) := by exact_mod_cast a
  unfold basis
  rw [Nat.factorial_succ]
  push_cast
  linear_combination -(j.factorial:ℝ)*q

private lemma expandPower (k n : ℕ) :
    ∑ j ∈ range (n+1), stir n j*basis k j = (k:ℝ)^n := by
  induction n with
  | zero => simp [stir,basis]
  | succ n ih =>
    let g (j : ℕ) : ℝ := (j:ℝ)*stir n j*basis k j
    have h0 : g 0 = 0 := by simp [g]
    have hn : g (n+1)=0 := by
      simp [g,stir,Nat.stirlingSecond_eq_zero_of_lt (show n<n+1 by omega)]
    have slide : ∑ j ∈ range (n+1), g (j+1) = ∑ j ∈ range (n+1), g j := by
      have h1 := sum_range_succ g (n+1)
      have h2 := sum_range_succ' g (n+1)
      rw [h0,add_zero] at h2
      rw [hn,add_zero] at h1
      exact h2.symm.trans h1
    have recTerm (j : ℕ) : stir (n+1) (j+1)*basis k (j+1) =
        g (j+1)+stir n j*basis k (j+1) := by
      unfold g stir
      rw [Nat.stirlingSecond_succ_succ]
      push_cast
      ring
    rw [sum_range_succ',show stir (n+1) 0*basis k 0=0 by simp [stir],add_zero]
    simp_rw [recTerm]
    rw [sum_add_distrib,slide,← sum_add_distrib,pow_succ,← ih,sum_mul]
    apply sum_congr rfl
    intro j _
    dsimp [g]
    linear_combination stir n j * basisStep k j

end HarmonicGeometric

open HarmonicGeometric

theorem OMA.solution : type_of% @OMA.S_oeis_a222058.main := by
  intro n
  have terms (j : ℕ) :
      HasSum (fun k : ℕ => stir n j*basis k j*(w k*(H k-Real.log 2)))
        ((Nat.stirlingSecond n j:ℝ)*(Nat.stirlingFirst (j+1) 2:ℝ)) := by
    rw [firstStirling]
    have q := (centered j).mul_left (stir n j*(j.factorial:ℝ))
    have r : stir n j*j.factorial*H j=(Nat.stirlingSecond n j:ℝ)*(j.factorial*H j) := by
      unfold stir
      ring
    rw [r] at q
    exact q.congr_fun (fun k => by unfold basis; ring)
  have allTerms := hasSum_sum (s:=range (n+1)) (fun j _ => terms j)
  unfold geometricHarmonic
  push_cast
  apply allTerms.congr_fun
  intro k
  rw [← sum_mul,expandPower]
  simp [H,w,div_pow,div_eq_mul_inv]
  <;> ring
