import OMAStatements.S_oeis_a267689

/-! The binary value of a Rule 199 row is determined by its positive odd holes and its last bit. -/

namespace Rule199
open OMA.S_oeis_a267689 Finset

def hole (n : ℕ) (i : ℤ) : Prop := 1 ≤ i ∧ i ≤ n ∧ (i%2=1 ∨ i=n)

instance (n : ℕ) (i : ℤ) : Decidable (hole n i) := by unfold hole; infer_instance

def row (n : ℕ) (i : ℤ) : Bool := if hole n i then false else true

lemma start (i : ℤ) : cell 199 1 i = row 1 i := by
  by_cases hl : i < -1
  · have h : ¬ hole 1 i := by unfold hole; omega
    simp (disch := omega) only [cell, row, if_neg h, decide_eq_false, decide_eq_true]
    decide
  by_cases hr : 1 < i
  · have h : ¬ hole 1 i := by unfold hole; omega
    simp (disch := omega) only [cell, row, if_neg h, decide_eq_false, decide_eq_true]
    decide
  interval_cases i <;> decide

lemma advance (n : ℕ) (hn : 1 ≤ n) (i : ℤ) :
    ruleOut 199 (row n (i-1)) (row n i) (row n (i+1)) = row (n+1) i := by
  by_cases l : hole n (i-1) <;> by_cases c : hole n i <;>
    by_cases r : hole n (i+1) <;> by_cases v : hole (n+1) i <;>
    simp [row,l,c,r,v] <;> first | decide | (exfalso; simp only [hole, Nat.cast_succ] at *; omega)

lemma phase_succ (k : ℕ) (i : ℤ) : cell 199 (k+1) i = row (k+1) i := by
  induction k generalizing i with
  | zero => exact start i
  | succ k ih =>
    change ruleOut 199 (cell 199 (k+1) (i-1)) (cell 199 (k+1) i)
      (cell 199 (k+1) (i+1)) = row ((k+1)+1) i
    rw [ih, ih, ih]
    exact advance (k+1) (by omega) i

lemma phase (n : ℕ) (hn : 1 ≤ n) (i : ℤ) : cell 199 n i = row n i := by
  rw [show n=(n-1)+1 by omega]
  exact phase_succ (n-1) i

def weight (n j : ℕ) : ℤ :=
  if cell 199 n ((j : ℤ)-n) then (2 : ℤ)^(2*n-j) else 0

lemma inner (n j : ℕ) (hn : 1 ≤ n) (hj : j < 2*n) :
    weight (n+1) (j+1) = 2*weight n j := by
  unfold weight
  rw [phase (n+1) (by omega), phase n hn]
  have hi : ((j+1 : ℕ) : ℤ)-(n+1 : ℕ)=(j : ℤ)-n := by push_cast; ring
  rw [hi]
  have he : hole (n+1) ((j : ℤ)-n) ↔ hole n ((j : ℤ)-n) := by
    simp only [hole, Nat.cast_succ]
    omega
  rw [row, row, if_congr he rfl rfl, show 2*(n+1)-(j+1) = (2*n-j)+1 by omega, pow_succ]
  split <;> simp <;> ring

lemma boundaries (n : ℕ) (hn : 1 ≤ n) :
    weight (n+1) 0 = (4 : ℤ)^(n+1) ∧ weight (n+1) (2*n+2) = 0 ∧
    weight n (2*n) = 0 ∧ weight (n+1) (2*n+1) = if n%2=0 then 2 else 0 := by
  have hl : ¬ hole (n+1) ((0 : ℤ)-(n+1 : ℕ)) := by
    simp only [hole,Nat.cast_succ]; omega
  have hr : hole (n+1) (((2*n+2 : ℕ) : ℤ)-(n+1 : ℕ)) := by
    simp only [hole, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; omega
  have hend : hole n (((2*n : ℕ) : ℤ)-n) := by
    simp only [hole, Nat.cast_mul, Nat.cast_ofNat]; omega
  have hbit : hole (n+1) (((2*n+1 : ℕ) : ℤ)-(n+1 : ℕ)) ↔ n%2=1 := by
    simp only [hole, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; omega
  refine ⟨?_,?_,?_,?_⟩
  · simp only [weight, phase (n+1) (by omega), row, Nat.cast_zero, if_neg hl,
      Nat.sub_zero, pow_mul]
    norm_num
    all_goals (intro h; unfold hole at h; omega)
  · simp only [weight, phase (n+1) (by omega), row, if_pos hr]
    rfl
  · simp only [weight, phase n hn, row, if_pos hend]
    rfl
  · rw [weight, phase (n+1) (by omega), row, if_congr hbit rfl rfl]
    by_cases h : n%2=0
    · have h' : n%2 ≠ 1 := by omega
      simp [h,h',show 2*(n+1)-(2*n+1)=1 by omega]
    · have h' : n%2=1 := by omega
      simp [h,h']

theorem one_step (n : ℕ) (hn : 1 ≤ n) :
    a (n+1) = 2*a n + (4 : ℤ)^(n+1) + (if n%2=0 then 2 else 0) := by
  change (∑ j ∈ range (2*(n+1)+1), weight (n+1) j) =
    2*(∑ j ∈ range (2*n+1), weight n j)+ _ + _
  rw [show 2*(n+1)+1=(2*n+2)+1 by omega, sum_range_succ,
    show 2*n+2=(2*n+1)+1 by omega, sum_range_succ']
  rw [sum_range_succ (fun j => weight (n+1) (j+1)),sum_range_succ (weight n)]
  have h : (∑ j ∈ range (2*n), weight (n+1) (j+1)) = 2*∑ j ∈ range (2*n), weight n j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    exact inner n j hn (mem_range.mp hj)
  obtain ⟨hl,hr,hend,hbit⟩ := boundaries n hn
  rw [h,hl,hend,hbit,show 2*n+1+1=2*n+2 by omega,hr]
  ring

end Rule199

namespace Rule199
open OMA.S_oeis_a267689 PowerSeries

lemma four_step (k : ℕ) : a (k+5) = 6*a (k+4)-7*a (k+3)-6*a (k+2)+8*a (k+1) := by
  have h1 := one_step (k+1) (by omega)
  have h2 := one_step (k+2) (by omega)
  have h3 := one_step (k+3) (by omega)
  have h4 := one_step (k+4) (by omega)
  by_cases h : k%2=0 <;>
    simp (disch := omega) only [if_pos,if_neg,pow_add] at h1 h2 h3 h4 <;>
    linear_combination h4 - 4*h3 - h2 + 4*h1

theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) = 6*a (n-1)-7*a (n-2)-6*a (n-3)+8*a (n-4) := by
  have f := four_step (n-5)
  rw [show n-5+5=n by omega,show n-5+4=n-1 by omega,show n-5+3=n-2 by omega,
    show n-5+2=n-3 by omega,show n-5+1=n-4 by omega] at f
  exact_mod_cast f

theorem generating :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1-X)*(1+X)*(1-2*X)*(1-4*X) : PowerSeries ℚ) =
      (1+2*X)*(1-2*X+3*X^2-4*X^3) := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hd : F*((1-X)*(1+X)*(1-2*X)*(1-4*X)) =
      F-6 • (F*X^1)+7 • (F*X^2)+6 • (F*X^3)-8 • (F*X^4) := by
    simp only [nsmul_eq_mul]
    ring
  have hp : ((1+2*X)*(1-2*X+3*X^2-4*X^3) : PowerSeries ℚ) =
      C 1-C 1*X^2+C 2*X^3-C 8*X^4 := by
    simp only [map_one,map_ofNat]
    ring
  rw [hd,hp]
  ext n
  simp only [map_sub,map_add,map_nsmul]
  simp only [coeff_mul_X_pow',coeff_C,coeff_mk,F,nsmul_eq_mul]
  by_cases hn : 5 ≤ n
  · have h := recurrence n hn
    simp (disch := omega) only [if_pos,if_neg]
    norm_num <;> linarith
  · have h0 : a 0=1 := by decide
    have h1 : a 1=6 := by decide
    have h2 : a 2=28 := by decide
    have h3 : a 3=122 := by decide
    have h4 : a 4=500 := by decide
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4]

end Rule199

theorem OMA.solution : type_of% @OMA.S_oeis_a267689.main :=
  ⟨Rule199.recurrence, Rule199.generating⟩
