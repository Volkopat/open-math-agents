import OMAStatements.S_oeis_a001700

/-! Known result (Chu–Vandermonde): `hyp n = 2 (1/2)_{n+1} / (n+1)!`, via
`Ring.descPochhammer_smeval_add` at `1/2 + n`, and `(1/2)_m 4^m m! = (2m)!`. -/

open Polynomial Finset

namespace OMA.S_oeis_a001700

lemma sm_eq (k : ℕ) (r : ℚ) : (descPochhammer ℤ k).smeval r = (descPochhammer ℚ k).eval r := by
  induction k with
  | zero => simp [smeval_one]
  | succ k ih =>
    rw [descPochhammer_succ_right, smeval_mul, ih, descPochhammer_succ_eval, smeval_sub, smeval_X,
      smeval_natCast]
    simp

lemma A2 (k : ℕ) : (ascPochhammer ℚ k).eval 2 = ((k+1).factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (k+1)]; push_cast; ring

lemma Uhalf (m : ℕ) : (ascPochhammer ℚ m).eval (1/2) * 4 ^ m * (m.factorial : ℚ) =
    ((2*m).factorial : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, show 2 * (m+1) = (2*m+1)+1 by ring, Nat.factorial_succ (2*m+1),
      Nat.factorial_succ (2*m), Nat.factorial_succ m]
    push_cast
    rw [← ih]; ring

lemma Dhalf (k : ℕ) : (descPochhammer ℚ (k+1)).eval (1/2) =
    (1/2) * (-1) ^ k * (ascPochhammer ℚ k).eval (1/2) := by
  have h1 : (descPochhammer ℚ (k+1)).eval (1/2) = (1/2) * (descPochhammer ℚ k).eval (1/2 - 1) := by
    rw [descPochhammer_succ_left]; simp [eval_comp]
  have h2 := ascPochhammer_eval_neg_eq_descPochhammer (R := ℚ) (-(1/2)) k
  rw [neg_neg] at h2
  rw [h1, h2, show (1/2 : ℚ) - 1 = -(1/2) by norm_num]
  rw [← mul_assoc, mul_assoc (1/2 : ℚ), ← pow_add, ← two_mul, pow_mul]; norm_num

lemma Dnat (n k : ℕ) : (descPochhammer ℚ k).eval (n : ℚ) = (n.descFactorial k : ℚ) := by
  rw [← sm_eq, descPochhammer_smeval_eq_descFactorial]

lemma V (n : ℕ) : (ascPochhammer ℚ (n+1)).eval (1/2) = ((n+1).factorial : ℚ) / 2 * hyp n := by
  have hv := Ring.descPochhammer_smeval_add (R := ℚ) (r := 1/2) (s := (n : ℚ)) (n+1) (Commute.all _ _)
  rw [sm_eq, descPochhammer_eval_eq_ascPochhammer] at hv
  rw [show (1/2 : ℚ) + n - ((n+1 : ℕ) : ℚ) + 1 = 1/2 by push_cast; ring] at hv
  rw [hv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => ((n+1).choose i : ℚ) *
    ((descPochhammer ℤ i).smeval (1/2 : ℚ) * (descPochhammer ℤ j).smeval (n : ℚ))),
    Finset.sum_range_succ', hyp, Finset.mul_sum]
  simp only [sm_eq, Dnat]
  rw [Nat.descFactorial_of_lt (by omega)]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk : k ≤ n := by simp at hk; omega
  rw [Dhalf, A2, show n + 1 - (k + 1) = n - k by omega, ascPochhammer_eval_neg_eq_descPochhammer,
    Dnat]
  have e1 : ((n.descFactorial (n-k) : ℕ) : ℚ) * k.factorial = n.factorial := by
    have := Nat.factorial_mul_descFactorial (show n - k ≤ n by omega)
    rw [show n - (n - k) = k by omega] at this
    exact_mod_cast (by rw [mul_comm]; exact this)
  have e2 : ((n - k).factorial : ℚ) * (n.descFactorial k : ℕ) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have e3 : ((n+1).choose (k+1) : ℚ) * (k+1).factorial * (n-k).factorial = (n+1).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ n + 1 by omega)
    rw [show n + 1 - (k+1) = n - k by omega] at this
    exact_mod_cast this
  have f1 : ((k+1).factorial : ℚ) ≠ 0 := by positivity
  have f2 : (k.factorial : ℚ) ≠ 0 := by positivity
  have f3 : ((n-k).factorial : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ n] at e3 ⊢
  rw [Nat.factorial_succ k] at f1 e3 ⊢
  field_simp
  apply mul_left_cancel₀ f3
  push_cast at e1 e2 e3 ⊢
  set u := eval (1 / 2) (ascPochhammer ℚ k)
  linear_combination (u * ((n + 1).choose (k + 1) : ℚ) * ((k+1:ℚ) * k.factorial) * (n-k).factorial) * e1
    + (u * n.factorial) * e3 - (u * ((n:ℚ)+1) * n.factorial) * e2
theorem solution_main : ∀ n : ℕ, ((Nat.choose (2 * n + 1) (n + 1) : ℕ) : ℚ) = 4 ^ n * hyp n := by
  intro n
  have h1 := V n
  have h2 := Uhalf (n+1)
  have h3 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * n + 1 by omega)
  rw [show 2 * n + 1 - (n + 1) = n by omega] at h3
  rw [show 2 * (n+1) = (2*n+1)+1 by ring, Nat.factorial_succ (2*n+1)] at h2
  rw [Nat.factorial_succ n] at h1 h2 h3
  have h3' : ((2 * n + 1).choose (n + 1) : ℚ) * (((n+1) * n.factorial : ℕ) : ℚ) * n.factorial
      = (2*n+1).factorial := by exact_mod_cast h3
  push_cast at h1 h2 h3' ⊢
  have hN : (n.factorial : ℚ) ≠ 0 := by positivity
  have hK : ((2*(n:ℚ)+2) * (((n:ℚ)+1) * n.factorial) * n.factorial) ≠ 0 := by positivity
  apply mul_left_cancel₀ hK
  linear_combination (2*(n:ℚ)+2) * h3' - h2 + (4^(n+1) * (((n:ℚ)+1) * n.factorial)) * h1
end OMA.S_oeis_a001700

theorem OMA.solution : type_of% @OMA.S_oeis_a001700.main := OMA.S_oeis_a001700.solution_main
