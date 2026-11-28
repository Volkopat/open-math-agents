import OMAStatements.S_oeis_a266438

namespace OMA.S_oeis_a266438

open PowerSeries





/-- Rule 23 is "ON iff at most one of the three cells is ON". -/
theorem eca23 (l c r : Bool) : eca 23 l c r = decide (l.toNat + c.toNat + r.toNat ≤ 1) := by
  revert l c r; decide

theorem state_one (i : ℤ) : state 1 i = true := by
  show eca 23 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = true
  rw [eca23, decide_eq_true_iff]
  by_cases h0 : i = 0
  · have h1 : ¬ i - 1 = 0 := by omega
    have h2 : ¬ i + 1 = 0 := by omega
    simp [h0, h1, h2]
  · by_cases h1 : i - 1 = 0
    · have h2 : ¬ i + 1 = 0 := by omega
      simp [h0, h1, h2]
    · simp only [h0, h1, decide_false, Bool.toNat_false, zero_add]
      cases decide (i + 1 = 0) <;> decide

theorem state_pos (t : ℕ) (i : ℤ) : state (t + 1) i = decide (t % 2 = 0) := by
  induction t generalizing i with
  | zero => exact state_one i
  | succ t ih =>
    show eca 23 (state (t + 1) (i - 1)) (state (t + 1) i) (state (t + 1) (i + 1)) = _
    rw [ih, ih, ih, eca23]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have : (t + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (t + 1) % 2 = 0 := by omega
      simp [h, this]

theorem black_zero : black 0 = 1 := by decide +kernel

theorem black_pos (t : ℕ) : black (t + 1) = if t % 2 = 0 then 2 * t + 3 else 0 := by
  unfold black
  simp only [state_pos]
  split_ifs with h
  · simp [h]
    omega
  · simp [h]

/-- Barker's closed form `a(n) = (n^2 + 2n - (-1)^n (n+1) + 3) / 2`, as `2 a(n) = ...`. -/
theorem closed_form (n : ℕ) :
    2 * (a n : ℤ) = (n : ℤ) ^ 2 + 2 * n - (-1) ^ n * (n + 1) + 3 := by
  induction n with
  | zero => simp [a, black_zero]
  | succ n ih =>
    have hs : a (n + 1) = a n + black (n + 1) := Finset.sum_range_succ _ _
    rw [hs, black_pos]
    push_cast
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h0 : n % 2 = 0 := by omega
      rw [if_pos h0]
      have e1 : ((-1 : ℤ)) ^ n = 1 := by rw [hk, ← two_mul, pow_mul]; norm_num
      have e2 : ((-1 : ℤ)) ^ (n + 1) = -1 := by rw [pow_succ, e1]; norm_num
      rw [e1] at ih
      rw [e2]
      push_cast
      linear_combination ih
    · have h0 : ¬ n % 2 = 0 := by omega
      rw [if_neg h0]
      have e1 : ((-1 : ℤ)) ^ n = -1 := by rw [hk, pow_succ, pow_mul]; norm_num
      have e2 : ((-1 : ℤ)) ^ (n + 1) = 1 := by rw [pow_succ, e1]; norm_num
      rw [e1] at ih
      rw [e2]
      push_cast
      linear_combination ih

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  have c5 := closed_form (k + 5)
  have c4 := closed_form (k + 4)
  have c3 := closed_form (k + 3)
  have c2 := closed_form (k + 2)
  have c1 := closed_form (k + 1)
  have c0 := closed_form k
  have p1 : ((-1 : ℤ)) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  have p2 : ((-1 : ℤ)) ^ (k + 2) = (-1) ^ k := by rw [pow_add]; norm_num
  have p3 : ((-1 : ℤ)) ^ (k + 3) = -(-1) ^ k := by rw [pow_add]; norm_num
  have p4 : ((-1 : ℤ)) ^ (k + 4) = (-1) ^ k := by rw [pow_add]; norm_num
  have p5 : ((-1 : ℤ)) ^ (k + 5) = -(-1) ^ k := by rw [pow_add]; norm_num
  rw [p5] at c5; rw [p4] at c4; rw [p3] at c3; rw [p2] at c2; rw [p1] at c1
  push_cast at c5 c4 c3 c2 c1 c0 ⊢
  have h2 : 2 * ((a (k + 5) : ℤ) - (a (k + 4) + 2 * a (k + 3) - 2 * a (k + 2) - a (k + 1)
      + a k)) = 0 := by
    linear_combination c5 - c4 - 2 * c3 + 2 * c2 + c1 - c0
  have := (mul_eq_zero.mp h2).resolve_left (by norm_num)
  linarith

/-- De Vlieger's g.f. with the denominator cleared:
`A(x) (1+x)^2 (1-x)^3 = 1 + 3x - 2x^2 + x^3 + x^4`. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 + X) ^ 2 * (1 - X) ^ 3) =
    (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have hD : A * ((1 + X) ^ 2 * (1 - X) ^ 3) =
      A - A * X ^ 1 - A * X ^ 2 - A * X ^ 2 + A * X ^ 3 + A * X ^ 3 + A * X ^ 4 - A * X ^ 5 := by
    ring
  have hN : (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) =
      1 + X ^ 1 + X ^ 1 + X ^ 1 - X ^ 2 - X ^ 2 + X ^ 3 + X ^ 4 := by ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk, coeff_one, coeff_X_pow]
  have v : (List.range 5).map a = [1, 4, 4, 11, 11] := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.map_append]
    simp [a, Finset.sum_range_succ, black_zero, black_pos]
  simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.cons.injEq, List.map_append, List.map_cons, List.map_nil] at v
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := v
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      if_false]
    linear_combination r

end OMA.S_oeis_a266438

theorem OMA.solution : type_of% @OMA.S_oeis_a266438.main :=
  ⟨OMA.S_oeis_a266438.gf, OMA.S_oeis_a266438.closed_form, OMA.S_oeis_a266438.recurrence⟩
