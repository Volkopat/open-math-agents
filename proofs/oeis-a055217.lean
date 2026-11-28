import OMAStatements.S_oeis_a055217

/-! Proof. With `T m k` the coefficient of `x^k` in `P^m`, `P = 1 + x + x²`, the symmetry
`T m k = T m (2m-k)` and `∑ T m k = 3^m` give `2 a(n) + T n n = 3^n`. The `3^n` part satisfies the
recurrence directly; the central coefficients satisfy it by a fixed combination of the Pascal-type
rule (`P^(m+1) = P·P^m`) and the relation `P·(P^m)' = m·P'·P^m`. -/

namespace OMA.S_oeis_a055217
open Polynomial Finset

noncomputable def P : ℤ[X] := 1 + X + X^2
noncomputable def T (m k : ℕ) : ℤ := (P^m).coeff k

lemma pas (m k : ℕ) : T (m+1) (k+2) = T m (k+2) + T m (k+1) + T m k := by
  unfold T
  rw [pow_succ', P]
  simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_pow_mul]

lemma Rr (m k : ℕ) : ((k:ℤ)+3) * T m (k+3) + ((k:ℤ)+2) * T m (k+2) + ((k:ℤ)+1) * T m (k+1)
    = (m:ℤ) * (T m (k+2) + 2 * T m (k+1)) := by
  have hd : P * derivative (P^m) = (m:ℤ[X]) * (derivative P * P^m) := by
    rcases m with _ | m
    · simp
    · rw [derivative_pow, Nat.add_sub_cancel, ← C_eq_natCast]; ring
  have hP : derivative P = 1 + 2 * X := by
    simp [P]
  have h := congrArg (fun q => q.coeff (k+2)) hd
  rw [hP, ← C_eq_natCast, coeff_C_mul] at h
  unfold T
  have e1 : ∀ q : ℤ[X], (P * q).coeff (k+2) = q.coeff (k+2) + q.coeff (k+1) + q.coeff k := by
    intro q
    rw [P]; simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_pow_mul]
  have e2 : ∀ q : ℤ[X], ((1 + 2*X) * q).coeff (k+2) = q.coeff (k+2) + 2 * q.coeff (k+1) := by
    intro q
    simp only [add_mul, one_mul, coeff_add, mul_assoc]
    rw [show (2:ℤ[X]) = C 2 by simp, coeff_C_mul, coeff_X_mul]
  rw [e1, e2] at h
  simp only [coeff_derivative] at h
  push_cast at h
  linear_combination h

lemma natDeg_pow (n : ℕ) : (P^n).natDegree ≤ 2*n := by
  have : P.natDegree ≤ 2 := by unfold P; compute_degree
  calc (P^n).natDegree ≤ n * P.natDegree := natDegree_pow_le
    _ ≤ n * 2 := Nat.mul_le_mul_left n this
    _ = 2 * n := by ring

lemma reflP (n : ℕ) : reflect (2*n) (P^n) = P^n := by
  have hr : reflect 2 P = P := by
    ext i
    rw [coeff_reflect]
    rcases i with _ | _ | _ | i
    · rw [revAt_le (by norm_num)] <;> simp [P, coeff_X, coeff_one, coeff_X_pow]
    · rw [revAt_le (by norm_num)] <;> simp [P, coeff_X, coeff_one, coeff_X_pow]
    · rw [revAt_le (by norm_num)] <;> simp [P, coeff_X, coeff_one, coeff_X_pow]
    · rw [revAt_eq_self_of_lt (by omega)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show 2*(n+1) = 2*n + 2 by ring, reflect_mul _ _ (natDeg_pow n) (by unfold P; compute_degree),
      ih, hr]

lemma sym (n k : ℕ) (hk : k ≤ 2*n) : T n k = T n (2*n - k) := by
  unfold T
  conv_lhs => rw [← reflP n]
  rw [coeff_reflect, revAt_le hk]

lemma total (n : ℕ) : ∑ k ∈ range (2*n+1), T n k = 3^n := by
  unfold T
  have h := eval_eq_sum_range' (p := P^n) (n := 2*n+1) (by have := natDeg_pow n; omega) 1
  simp only [one_pow, mul_one] at h
  rw [← h]
  simp [P]

lemma half (n : ℕ) : 2 * (∑ k ∈ range n, T n k) + T n n = 3^n := by
  rw [← total, show 2*n+1 = (n+1) + n by ring, sum_range_add, sum_range_succ]
  have : ∑ x ∈ range n, T n (n + 1 + x) = ∑ x ∈ range n, T n x := by
    rw [← sum_range_reflect (fun x => T n x) n]
    refine sum_congr rfl (fun x hx => ?_)
    simp at hx
    rw [sym n (n+1+x) (by omega)]; congr 1; omega
  rw [this]; ring

lemma bT (n : ℕ) : 2 * b n = 3^(n+1) - T (n+1) (n+1) := by
  have := half (n+1)
  unfold b a
  simp only [T, P] at this ⊢
  linear_combination this


theorem solution_main : ∀ n : ℕ, 3 ≤ n →
    let m : ℤ := n
    (m + 1) * b n - (5 * m + 1) * b (n - 1) + 3 * (m - 1) * b (n - 2) + 9 * (m - 1) * b (n - 3) = 0 := by
  intro n hn m
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  simp only [m, show N + 3 - 1 = N + 2 by omega, show N + 3 - 2 = N + 1 by omega,
    show N + 3 - 3 = N by omega]
  have b0 := bT N
  have b1 := bT (N+1)
  have b2 := bT (N+2)
  have b3 := bT (N+3)
  have h0 := Rr (N+1) (N+0)
  have h1 := Rr (N+1) (N+1)
  have h2 := Rr (N+2) (N+0)
  have h3 := Rr (N+2) (N+1)
  have h4 := Rr (N+3) (N+1)
  have h5 := pas (N+1) (N+1)
  have h6 := pas (N+1) (N+2)
  have h7 := pas (N+2) (N+1)
  have h8 := pas (N+2) (N+2)
  have h9 := pas (N+3) (N+2)
  refine (mul_eq_zero.mp (?_ : (2 : ℤ) * _ = 0)).resolve_left (by norm_num)
  push_cast at *
  ring_nf at *
  linear_combination ((N:ℤ)+3+1) * b3 - (5*((N:ℤ)+3)+1) * b2 + 3*((N:ℤ)+3-1) * b1 + 9*((N:ℤ)+3-1) * b0
    - ((-3) * h0 + (3) * h1 + (4) * h2 + (-1) * h3 + (-1) * h4 + (-6*(N:ℤ) - 15) * h5 + (3*(N:ℤ) + 12) * h6 + (-4*(N:ℤ) - 12) * h7 + (2*(N:ℤ) + 8) * h8 + ((N:ℤ) + 4) * h9)

end OMA.S_oeis_a055217

theorem OMA.solution : type_of% @OMA.S_oeis_a055217.main := OMA.S_oeis_a055217.solution_main
