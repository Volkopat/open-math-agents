import OMAStatements.S_oeis_a214555


lemma rep_val (n d : ℕ) :
    (9 : ℤ) * (Nat.ofDigits 10 (List.replicate n d) : ℕ) = d * (10 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons]
    push_cast at ih ⊢
    linear_combination 10 * ih

lemma rev_eq (n : ℕ) : (OMA.S_oeis_a214555.digitList n).reverse =
    5 :: (List.replicate n 4 ++ (List.replicate (n + 1) 9 ++ (4 :: List.replicate n 5))) := by
  simp [OMA.S_oeis_a214555.digitList]

lemma closed (n : ℕ) : (9 : ℤ) * (OMA.S_oeis_a214555.a n : ℕ) =
    5 * (((10 : ℤ) ^ (n + 1)) ^ 3 - (10 ^ (n + 1)) ^ 2 - 10 ^ (n + 1) + 1) := by
  rw [OMA.S_oeis_a214555.a, rev_eq, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_append,
    Nat.ofDigits_cons, List.length_replicate, List.length_replicate]
  have h5 := rep_val n 5
  have h9 := rep_val (n + 1) 9
  have h4 := rep_val n 4
  push_cast at *
  linear_combination 10 * h4 + 10 * 10 ^ n * h9 + 10 * 10 ^ n * 10 ^ (n + 1) * 10 * h5

theorem OMA.solution : type_of% @OMA.S_oeis_a214555.main := by
  intro n
  have h0 := closed n
  have h1 := closed (n + 1)
  have h2 := closed (n + 2)
  have h3 := closed (n + 3)
  have h4 := closed (n + 4)
  have : (9 : ℤ) * (OMA.S_oeis_a214555.a (n + 4) : ℤ) = 9 * (1111 * OMA.S_oeis_a214555.a (n + 3)
      - 112110 * OMA.S_oeis_a214555.a (n + 2) + 1111000 * OMA.S_oeis_a214555.a (n + 1)
      - 1000000 * OMA.S_oeis_a214555.a n) := by
    rw [mul_sub, mul_add, mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    rw [mul_comm (9 : ℤ) 1111, mul_comm (9 : ℤ) 112110, mul_comm (9 : ℤ) 1111000,
      mul_comm (9 : ℤ) 1000000, mul_assoc, mul_assoc, mul_assoc, mul_assoc, h0, h1, h2, h3, h4]
    ring
  exact mul_left_cancel₀ (by norm_num) this
