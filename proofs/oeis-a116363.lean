import OMAStatements.S_oeis_a116363

/-! Proof. The Catalan-triangle entry is the ballot number `C(2n-k,n) - C(2n-k,n+1)`; reflecting
`k ↦ n-k` and expanding `(1+x)^n (2+x)^n = ∑ₖ C(n,k)(1+x)^(n+k)` gives
`a(n) = [xⁿ]Qⁿ - [xⁿ⁺¹]Qⁿ` with `Q = (1+x)(2+x)`. The coefficients of `Qᵐ` satisfy the Pascal-type
rule from `Qᵐ⁺¹ = Q·Qᵐ` and the rule from `Q·(Qᵐ)' = m·Q'·Qᵐ`; a fixed combination of these gives
the recurrence (small cases `n = 2, 3` by computation). -/

namespace OMA.S_oeis_a116363

open Polynomial Finset

noncomputable def Q : ℚ[X] := (X + 1) * (X + 1 + 1)
noncomputable def T (m j : ℕ) : ℚ := (Q^m).coeff j

lemma Qe : Q = C 2 + C 3 * X + X^2 := by
  simp only [Q, map_ofNat]; ring

lemma pas (m k : ℕ) : T (m+1) (k+2) = 2 * T m (k+2) + 3 * T m (k+1) + T m k := by
  unfold T
  rw [pow_succ', Qe]
  simp only [add_mul, coeff_add, coeff_C_mul, coeff_X_pow_mul, mul_assoc, coeff_X_mul]

lemma hPd : derivative Q = C 3 + C 2 * X := by
  have : Q = (X + C 1) * (X + C 2) := by simp only [Q, map_one, map_ofNat]; ring
  rw [this, derivative_mul]; simp only [derivative_add, derivative_X, derivative_C, add_zero, one_mul, mul_one]
  rw [show (3:ℚ) = 1 + 2 by norm_num, C_add]; ring_nf; simp; rw [mul_comm]; rfl

lemma eQ (q : ℚ[X]) (k : ℕ) : (Q * q).coeff (k+2) = 2 * q.coeff (k+2) + 3 * q.coeff (k+1) + q.coeff k := by
  rw [Qe]; simp only [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul, coeff_X_pow_mul]

lemma eQ1 (q : ℚ[X]) : (Q * q).coeff 1 = 2 * q.coeff 1 + 3 * q.coeff 0 := by
  rw [Qe]; simp only [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul, coeff_X_pow_mul']; simp

lemma eP (q : ℚ[X]) (k : ℕ) : ((C 3 + C 2 * X) * q).coeff (k+1) = 3 * q.coeff (k+1) + 2 * q.coeff k := by
  simp only [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul]

lemma eP0 (q : ℚ[X]) : ((C 3 + C 2 * X) * q).coeff 0 = 3 * q.coeff 0 := by
  simp only [add_mul, coeff_add, coeff_C_mul, mul_assoc]; simp

lemma Rr (m j : ℕ) : 2 * ((j:ℚ)+2) * T m (j+2) + 3 * ((j:ℚ)+1) * T m (j+1) + (j:ℚ) * T m j
    = (m:ℚ) * (3 * T m (j+1) + 2 * T m j) := by
  have hd : Q * derivative (Q^m) = C (m:ℚ) * ((C 3 + C 2 * X) * Q^m) := by
    rw [← hPd]
    rcases m with _ | m
    · simp
    · rw [derivative_pow, Nat.add_sub_cancel, C_eq_natCast]; push_cast; ring
  unfold T
  rcases j with _ | k
  · have h := congrArg (fun q => q.coeff 1) hd
    simp only [coeff_C_mul] at h
    rw [eQ1, show (1:ℕ) = 0 + 1 from rfl, eP] at h
    simp only [coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h
  · have h := congrArg (fun q => q.coeff (k+2)) hd
    simp only [coeff_C_mul] at h
    rw [eQ, show k+2 = (k+1)+1 by ring, eP] at h
    simp only [coeff_derivative] at h
    push_cast at h ⊢
    ring_nf at h ⊢
    linear_combination h

lemma Tsum (n j : ℕ) : T n j = ∑ k ∈ range (n+1), (n.choose k : ℚ) * ((n+k).choose j : ℚ) := by
  unfold T
  rw [Q, mul_pow, add_pow (X + 1 : ℚ[X]) 1 n, mul_sum, finsetSum_coeff]
  refine sum_congr rfl (fun k _ => ?_)
  rw [one_pow, mul_one, ← mul_assoc, ← pow_add, ← C_eq_natCast, coeff_mul_C, coeff_X_add_one_pow]
  ring

lemma chS (N r : ℕ) : ((r:ℚ)+1) * (N.choose (r+1) : ℚ) = ((N:ℚ) - r) * (N.choose r : ℚ) := by
  rcases Nat.lt_or_ge N r with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have e := Nat.choose_succ_right_eq N r
    have e' : ((N.choose (r+1) * (r+1) : ℕ) : ℚ) = ((N.choose r * (N - r) : ℕ) : ℚ) := by rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'

lemma ballot (n k : ℕ) (hk : k ≤ n) :
    catTri n (n - k) = ((n+k).choose n : ℚ) - ((n+k).choose (n+1) : ℚ) := by
  unfold catTri
  rw [show 2*n - (n-k) + 1 = (n+k) + 1 by omega, show n - (n-k) = k by omega]
  have hs : (n+k+1).choose k = (n+k+1).choose (n+1) := by
    rw [Nat.choose_symm_of_eq_add]; ring
  rw [hs, Nat.choose_succ_succ]
  have h1 := chS (n+k) n
  have hpos : ((n+k+1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [div_eq_iff hpos]
  push_cast [Nat.cast_sub hk] at h1 ⊢
  simp only [Nat.succ_eq_add_one] at *
  linear_combination 2 * h1

lemma conv (n : ℕ) : a n = T n n - T n (n+1) := by
  rw [Tsum, Tsum, ← sum_sub_distrib, a, ← sum_range_reflect]
  refine sum_congr rfl (fun k hk => ?_)
  simp only [mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, ballot n k (by omega), Nat.choose_symm (by omega)]
  ring

theorem solution_main :
    ∀ n : ℕ, 2 ≤ n →
      (2 * (n : ℚ) + 5) * ((n : ℚ) + 1) * a n
      + 4 * (-3 * (n : ℚ) ^ 2 - 9 * (n : ℚ) + 5) * a (n - 1)
      + (2 * (n : ℚ) + 7) * ((n : ℚ) - 1) * a (n - 2) = 0 := by
  intro n hn
  rw [conv, conv, conv]
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · simp only [Tsum]; norm_num [Finset.sum_range_succ, Nat.choose]
  · simp only [Tsum]; norm_num [Finset.sum_range_succ, Nat.choose]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
  simp only [show N + 4 - 1 = N + 3 by omega, show N + 4 - 2 = N + 2 by omega]
  have r1 := Rr (N+2) N
  have r2 := Rr (N+2) (N+1)
  have r3 := Rr (N+3) N
  have r4 := Rr (N+3) (N+1)
  have r5 := Rr (N+3) (N+2)
  have r6 := Rr (N+4) (N+2)
  have r7 := Rr (N+4) (N+3)
  have p1 := pas (N+2) N
  have p2 := pas (N+2) (N+1)
  have p3 := pas (N+3) N
  have p4 := pas (N+3) (N+1)
  have hne : (2 * ((N:ℚ) + 4)) ≠ 0 := by positivity
  refine (mul_eq_zero.mp (?_ : (2 * ((N:ℚ) + 4)) * _ = 0)).resolve_left hne
  push_cast at *
  ring_nf at *
  linear_combination (exp := 1)
    (-7*(2*((N:ℚ)+2)+11)*((N:ℚ)+4)) * r1 + (-11*(2*((N:ℚ)+2)+11)*((N:ℚ)+4)) * r2
    + (-((N:ℚ)+5)*(2*((N:ℚ)+2)+9)) * r3 + (-(2*((N:ℚ)+2)+7)*(2*((N:ℚ)+2)+9)) * r4
    + (4*(3*((N:ℚ)+2)^2+21*((N:ℚ)+2)+25)) * r5 + (((N:ℚ)+5)*(2*((N:ℚ)+2)+9)) * r6
    + (-(2*((N:ℚ)+2)+9)*((N:ℚ)+4)) * r7
    + (7*((N:ℚ)+4)*(2*((N:ℚ)+2)+11)*((N:ℚ)+4)) * p1 + (-10*((N:ℚ)+3)*(2*((N:ℚ)+2)+11)*((N:ℚ)+4)) * p2
    + (((N:ℚ)+5)*((N:ℚ)+6)*(2*((N:ℚ)+2)+9)) * p3 + (-((N:ℚ)+1)*((N:ℚ)+5)*(2*((N:ℚ)+2)+9)) * p4

end OMA.S_oeis_a116363

theorem OMA.solution : type_of% @OMA.S_oeis_a116363.main := OMA.S_oeis_a116363.solution_main
