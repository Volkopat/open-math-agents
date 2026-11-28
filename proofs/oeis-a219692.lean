import OMAStatements.S_oeis_a219692
import Mathlib

open OMA.S_oeis_a219692

private def dp (x : ℚ) (r : ℕ) : ℚ := ∏ i ∈ Finset.range r, (x - i)

private lemma dp_succ (x : ℚ) (r : ℕ) : dp x (r + 1) = dp x r * (x - r) := by
  simp [dp, Finset.prod_range_succ]

private lemma dp_shift (x : ℚ) (r : ℕ) : dp (x + 1) r * (x + 1 - r) = dp x r * (x + 1) := by
  induction r with
  | zero => simp [dp]
  | succ r ih =>
    rw [dp_succ, dp_succ]; push_cast
    linear_combination (x - r) * ih

private lemma dp_nat (x r : ℕ) : ((x.descFactorial r : ℕ) : ℚ) = dp x r := by
  induction r with
  | zero => simp [dp]
  | succ r ih =>
    rw [Nat.descFactorial_succ, dp_succ, ← ih]
    rcases le_or_gt r x with h | h
    · push_cast [Nat.cast_sub h]; ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

private lemma dp_zero_of_lt (x r : ℕ) (h : x < r) : dp x r = 0 := by
  rw [← dp_nat, Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

private lemma fact_sub (x r : ℕ) (h : r ≤ x) :
    (((x - r).factorial : ℕ) : ℚ) * dp x r = (x.factorial : ℚ) := by
  rw [← dp_nat]; exact_mod_cast Nat.factorial_mul_descFactorial h

private lemma dp_ne (x r : ℕ) (h : r ≤ x) : dp x r ≠ 0 := by
  intro h0
  have := fact_sub x r h
  rw [h0, mul_zero] at this
  exact (Nat.factorial_ne_zero x) (by exact_mod_cast this.symm)

private def Q (x r : ℕ) : ℚ := (x.factorial : ℚ) / dp x r

private def Rr (x r : ℕ) : ℚ := dp x r / (x.factorial : ℚ)

private lemma Q_eq (x r : ℕ) (h : r ≤ x) : Q x r = ((x - r).factorial : ℚ) := by
  unfold Q; rw [div_eq_iff (dp_ne x r h)]; exact (fact_sub x r h).symm

private lemma R_eq (x r : ℕ) (h : r ≤ x) : Rr x r = 1 / ((x - r).factorial : ℚ) := by
  unfold Rr
  have := fact_sub x r h
  have h1 : ((x - r).factorial : ℚ) ≠ 0 := by positivity
  have h2 := dp_ne x r h
  rw [← this]; field_simp

private lemma Q_succ (x r : ℕ) (h : r ≤ x) : Q (x + 1) r = Q x r * ((x : ℚ) + 1 - r) := by
  have h1 := dp_ne x r h
  have h2 := dp_ne (x + 1) r (by omega)
  have hs := dp_shift (x : ℚ) r
  push_cast at h2
  unfold Q
  rw [div_mul_eq_mul_div, div_eq_div_iff (by push_cast; exact h2) h1, Nat.factorial_succ]
  push_cast
  linear_combination (-(x.factorial : ℚ)) * hs

private lemma R_succ (x r : ℕ) : Rr x r = Rr (x + 1) r * ((x : ℚ) + 1 - r) := by
  have hs := dp_shift (x : ℚ) r
  unfold Rr
  rw [Nat.factorial_succ]; push_cast
  have : (x.factorial : ℚ) ≠ 0 := by positivity
  have : ((x : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linear_combination -hs

private lemma Q_step (x r : ℕ) : Q x (r + 1) = Q x r / ((x : ℚ) - r) := by
  unfold Q; rw [dp_succ, div_div]

private lemma R_step (x r : ℕ) : Rr x (r + 1) = Rr x r * ((x : ℚ) - r) := by
  unfold Rr; rw [dp_succ]; ring

private lemma cb (k : ℕ) : ((2 * (k + 1)).choose (k + 1) : ℚ) = ((2 * k).choose k : ℚ) * (4 * k + 2) / (k + 1) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((2 * (k + 1)).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((2 * k).choose k : ℚ) * (4 * k + 2) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) h
    push_cast at this; linarith
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

private def Pc (x y : ℚ) : ℚ :=
  (3456) * x ^ 0 * y ^ 3
    + (-27648) * x ^ 0 * y ^ 4
    + (80784) * x ^ 0 * y ^ 5
    + (-101952) * x ^ 0 * y ^ 6
    + (39204) * x ^ 0 * y ^ 7
    + (26568) * x ^ 0 * y ^ 8
    + (-26244) * x ^ 0 * y ^ 9
    + (5832) * x ^ 0 * y ^ 10
    + (-2304) * x ^ 1 * y ^ 2
    + (52992) * x ^ 1 * y ^ 3
    + (-291744) * x ^ 1 * y ^ 4
    + (673560) * x ^ 1 * y ^ 5
    + (-740268) * x ^ 1 * y ^ 6
    + (376776) * x ^ 1 * y ^ 7
    + (-72360) * x ^ 1 * y ^ 8
    + (4212) * x ^ 1 * y ^ 9
    + (-1944) * x ^ 1 * y ^ 10
    + (-23040) * x ^ 2 * y ^ 2
    + (306624) * x ^ 2 * y ^ 3
    + (-1267872) * x ^ 2 * y ^ 4
    + (2353488) * x ^ 2 * y ^ 5
    + (-2216172) * x ^ 2 * y ^ 6
    + (1121832) * x ^ 2 * y ^ 7
    + (-327132) * x ^ 2 * y ^ 8
    + (57672) * x ^ 2 * y ^ 9
    + (-3888) * x ^ 2 * y ^ 10
    + (-98688) * x ^ 3 * y ^ 2
    + (932064) * x ^ 3 * y ^ 3
    + (-2980320) * x ^ 3 * y ^ 4
    + (4411440) * x ^ 3 * y ^ 5
    + (-3385776) * x ^ 3 * y ^ 6
    + (1413936) * x ^ 3 * y ^ 7
    + (-314928) * x ^ 3 * y ^ 8
    + (28512) * x ^ 3 * y ^ 9
    + (-237312) * x ^ 4 * y ^ 2
    + (1681752) * x ^ 4 * y ^ 3
    + (-4154580) * x ^ 4 * y ^ 4
    + (4753776) * x ^ 4 * y ^ 5
    + (-2752020) * x ^ 4 * y ^ 6
    + (793728) * x ^ 4 * y ^ 7
    + (-90720) * x ^ 4 * y ^ 8
    + (-352848) * x ^ 5 * y ^ 2
    + (1892520) * x ^ 5 * y ^ 3
    + (-3524556) * x ^ 5 * y ^ 4
    + (2936676) * x ^ 5 * y ^ 5
    + (-1127976) * x ^ 5 * y ^ 6
    + (163584) * x ^ 5 * y ^ 7
    + (-336480) * x ^ 6 * y ^ 2
    + (1339296) * x ^ 6 * y ^ 3
    + (-1781616) * x ^ 6 * y ^ 4
    + (963288) * x ^ 6 * y ^ 5
    + (-182832) * x ^ 6 * y ^ 6
    + (-205968) * x ^ 7 * y ^ 2
    + (578256) * x ^ 7 * y ^ 3
    + (-492048) * x ^ 7 * y ^ 4
    + (129696) * x ^ 7 * y ^ 5
    + (-78144) * x ^ 8 * y ^ 2
    + (138912) * x ^ 8 * y ^ 3
    + (-57024) * x ^ 8 * y ^ 4
    + (-16704) * x ^ 9 * y ^ 2
    + (14208) * x ^ 9 * y ^ 3
    + (-1536) * x ^ 10 * y ^ 2

private lemma Q2 (x r : ℕ) (h : r ≤ x) :
    Q (x + 2) r = Q x r * ((x : ℚ) + 1 - r) * ((x : ℚ) + 2 - r) := by
  rw [show x + 2 = x + 1 + 1 from rfl, Q_succ (x + 1) r (by omega), Q_succ x r h]; push_cast; ring

private lemma Q4 (x r : ℕ) (h : r ≤ x) :
    Q (x + 4) r = Q x r * ((x : ℚ) + 1 - r) * ((x : ℚ) + 2 - r) * ((x : ℚ) + 3 - r) * ((x : ℚ) + 4 - r) := by
  rw [show x + 4 = x + 2 + 2 from rfl, Q2 (x + 2) r (by omega), Q2 x r h]; push_cast; ring

private lemma R1' (x r : ℕ) : Rr (x + 1) r = Rr (x + 2) r * ((x : ℚ) + 2 - r) := by
  rw [R_succ (x + 1) r]; push_cast; ring

private lemma R2 (x r : ℕ) : Rr x r = Rr (x + 2) r * ((x : ℚ) + 1 - r) * ((x : ℚ) + 2 - r) := by
  rw [R_succ x r, R1' x r]; ring

private def U (n j : ℕ) : ℚ :=
  (-1) ^ j * (((2 * j).choose j : ℚ) / (j.factorial : ℚ)) * Q (2 * n) (2 * j) * Q (2 * n) (3 * j + 1) *
    Rr n j ^ 3 * Rr n (3 * j) * (3 * ((n : ℚ) - 2 * j))

private def b (n j : ℕ) : ℚ :=
  (-1) ^ j * (((2 * j).choose j : ℚ) / (j.factorial : ℚ)) * Q (2 * n) (2 * j) * Q (2 * n) (3 * j + 1) *
    Rr (n + 2) j ^ 3 * Rr (n + 2) (3 * j)

private lemma TL (n j : ℕ) (hn : 1 ≤ n) (hj : 3 * j ≤ n) :
    ((-1) ^ j * (n.choose j : ℚ) * ((2 * j).choose j : ℚ) * ((2 * n - 2 * j).choose (n - j) : ℚ) *
      (((2 * n - 3 * j - 1).choose n : ℚ) + ((2 * n - 3 * j).choose n : ℚ))) = U n j := by
  have f1 : (j.factorial : ℚ) ≠ 0 := by positivity
  have f2 : (n.factorial : ℚ) ≠ 0 := by positivity
  have e1 : (n.choose j : ℚ) = n.factorial * Rr n j / j.factorial := by
    rw [Nat.cast_choose ℚ (by omega : j ≤ n), R_eq n j (by omega)]
    have : ((n - j).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  have e2 : ((2 * n - 2 * j).choose (n - j) : ℚ) = Q (2 * n) (2 * j) * Rr n j ^ 2 := by
    rw [Nat.cast_choose ℚ (by omega : n - j ≤ 2 * n - 2 * j), show 2 * n - 2 * j - (n - j) = n - j by omega,
      Q_eq (2 * n) (2 * j) (by omega), R_eq n j (by omega)]
    have : ((n - j).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  have e3 : ((2 * n - 3 * j).choose n : ℚ) =
      (2 * (n : ℚ) - 3 * j) * Q (2 * n) (3 * j + 1) * Rr n (3 * j) / n.factorial := by
    rw [Nat.cast_choose ℚ (by omega : n ≤ 2 * n - 3 * j), show 2 * n - 3 * j - n = n - 3 * j by omega,
      Q_eq (2 * n) (3 * j + 1) (by omega), R_eq n (3 * j) hj,
      show 2 * n - 3 * j = (2 * n - (3 * j + 1)) + 1 by omega, Nat.factorial_succ]
    have : ((n - 3 * j).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((2 * n - (3 * j + 1) : ℕ) : ℚ) = 2 * (n : ℚ) - 3 * j - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast [h3]
    field_simp
    ring
  have e4 : ((2 * n - 3 * j - 1).choose n : ℚ) =
      ((n : ℚ) - 3 * j) * Q (2 * n) (3 * j + 1) * Rr n (3 * j) / n.factorial := by
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      have : (n : ℚ) = 3 * j := by rw [← h]; push_cast; ring
      rw [this]; ring
    · rw [Nat.cast_choose ℚ (by omega : n ≤ 2 * n - 3 * j - 1), show 2 * n - 3 * j - 1 - n = n - 3 * j - 1 by omega,
        Q_eq (2 * n) (3 * j + 1) (by omega), R_eq n (3 * j) hj,
        show 2 * n - 3 * j - 1 = 2 * n - (3 * j + 1) by omega,
        show n - 3 * j = (n - 3 * j - 1) + 1 by omega, Nat.factorial_succ]
      have : ((n - 3 * j - 1).factorial : ℚ) ≠ 0 := by positivity
      have : ((2 * n - (3 * j + 1)).factorial : ℚ) ≠ 0 := by positivity
      have h3 : ((n - 3 * j - 1 : ℕ) : ℚ) = (n : ℚ) - 3 * j - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have h4 : ((n : ℚ) - 3 * j) ≠ 0 := by
        have : (3 * (j : ℚ)) < n := by exact_mod_cast h
        intro h0; linarith
      push_cast [h3]
      rw [show (n : ℚ) - 3 * j - 1 + 1 = n - 3 * j by ring]
      field_simp
  rw [e1, e2, e3, e4]
  unfold U
  field_simp
  ring

private lemma U0 (n j : ℕ) : U n j = b n j * (3 * ((n : ℚ) - 2 * j) * ((n : ℚ) + 1 - j) ^ 3 *
    ((n : ℚ) + 2 - j) ^ 3 * ((n : ℚ) + 1 - 3 * j) * ((n : ℚ) + 2 - 3 * j)) := by
  unfold U b
  rw [R2 n j, R2 n (3 * j)]; push_cast; ring

private lemma U1 (n j : ℕ) (h1 : 2 * j ≤ 2 * n) (h2 : 3 * j + 1 ≤ 2 * n) :
    U (n + 1) j = b n j * (3 * ((n : ℚ) + 1 - 2 * j) * (2 * (n : ℚ) + 1 - 2 * j) * (2 * (n : ℚ) + 2 - 2 * j) *
      (2 * (n : ℚ) - 3 * j) * (2 * (n : ℚ) + 1 - 3 * j) * ((n : ℚ) + 2 - j) ^ 3 * ((n : ℚ) + 2 - 3 * j)) := by
  unfold U b
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, Q2 (2 * n) (2 * j) h1, Q2 (2 * n) (3 * j + 1) h2,
    R1' n j, R1' n (3 * j)]
  push_cast; ring

private lemma U2 (n j : ℕ) (h1 : 2 * j ≤ 2 * n) (h2 : 3 * j + 1 ≤ 2 * n) :
    U (n + 2) j = b n j * (3 * ((n : ℚ) + 2 - 2 * j) * (2 * (n : ℚ) + 1 - 2 * j) * (2 * (n : ℚ) + 2 - 2 * j) *
      (2 * (n : ℚ) + 3 - 2 * j) * (2 * (n : ℚ) + 4 - 2 * j) * (2 * (n : ℚ) - 3 * j) *
      (2 * (n : ℚ) + 1 - 3 * j) * (2 * (n : ℚ) + 2 - 3 * j) * (2 * (n : ℚ) + 3 - 3 * j)) := by
  unfold U b
  rw [show 2 * (n + 2) = 2 * n + 4 by ring, Q4 (2 * n) (2 * j) h1, Q4 (2 * n) (3 * j + 1) h2]
  push_cast; ring

private def rho (x y : ℚ) : ℚ :=
  (-(4 * y + 2) * (x + 2 - y) ^ 3 * ((x + 2 - 3 * y) * (x + 1 - 3 * y) * (x - 3 * y))) /
    ((y + 1) ^ 2 * ((2 * x - 2 * y) * (2 * x - 2 * y - 1)) *
      ((2 * x - 3 * y - 1) * (2 * x - 3 * y - 2) * (2 * x - 3 * y - 3)))

private lemma L2 (n j : ℕ) : b n (j + 1) = b n j * rho n j := by
  unfold b rho
  rw [cb j, Nat.factorial_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
    show 3 * (j + 1) + 1 = 3 * j + 1 + 1 + 1 + 1 by ring, show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by ring,
    Q_step (2 * n) (2 * j + 1), Q_step (2 * n) (2 * j), Q_step (2 * n) (3 * j + 1 + 1 + 1),
    Q_step (2 * n) (3 * j + 1 + 1), Q_step (2 * n) (3 * j + 1), R_step (n + 2) j,
    R_step (n + 2) (3 * j + 1 + 1), R_step (n + 2) (3 * j + 1), R_step (n + 2) (3 * j)]
  push_cast
  have : (j.factorial : ℚ) ≠ 0 := by positivity
  have : ((j : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

private lemma L3 (n : ℕ) : b n ((n + 2) / 3 + 1) = 0 := by
  unfold b Rr
  rw [dp_zero_of_lt (n + 2) (3 * ((n + 2) / 3 + 1)) (by omega)]
  simp

private def G (n j : ℕ) : ℚ := Pc n j * b n j

private lemma G0 (n : ℕ) : G n 0 = 0 := by
  unfold G
  rw [show Pc (n : ℚ) ((0 : ℕ) : ℚ) = 0 by unfold Pc; push_cast; ring, zero_mul]

private lemma KI (n j : ℕ) (hn : 6 ≤ n) (hj : 3 * j ≤ n + 2) :
    12 * (4 * ((n : ℚ) + 2) - 5) * (((n : ℚ) + 2) - 1) * (4 * ((n : ℚ) + 2) - 3) *
        (3 * ((n : ℚ) - 2 * j) * ((n : ℚ) + 1 - j) ^ 3 *
          ((n : ℚ) + 2 - j) ^ 3 * ((n : ℚ) + 1 - 3 * j) * ((n : ℚ) + 2 - 3 * j))
      - 2 * (2 * ((n : ℚ) + 2) - 1) * (7 * ((n : ℚ) + 2) ^ 2 - 7 * ((n : ℚ) + 2) + 3) *
        (3 * ((n : ℚ) + 1 - 2 * j) * (2 * (n : ℚ) + 1 - 2 * j) * (2 * (n : ℚ) + 2 - 2 * j) *
          (2 * (n : ℚ) - 3 * j) * (2 * (n : ℚ) + 1 - 3 * j) * ((n : ℚ) + 2 - j) ^ 3 * ((n : ℚ) + 2 - 3 * j))
      + ((n : ℚ) + 2) ^ 3 *
        (3 * ((n : ℚ) + 2 - 2 * j) * (2 * (n : ℚ) + 1 - 2 * j) * (2 * (n : ℚ) + 2 - 2 * j) *
          (2 * (n : ℚ) + 3 - 2 * j) * (2 * (n : ℚ) + 4 - 2 * j) * (2 * (n : ℚ) - 3 * j) *
          (2 * (n : ℚ) + 1 - 3 * j) * (2 * (n : ℚ) + 2 - 3 * j) * (2 * (n : ℚ) + 3 - 3 * j))
      = Pc n ((j : ℚ) + 1) * rho n j - Pc n j := by
  have hj' : 3 * (j : ℚ) ≤ n + 2 := by exact_mod_cast hj
  have hn' : (6 : ℚ) ≤ n := by exact_mod_cast hn
  have hj0 : (0 : ℚ) ≤ j := by positivity
  have d1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have d2 : (2 * (n : ℚ) - 2 * j) ≠ 0 := by intro h; linarith
  have d3 : (2 * (n : ℚ) - 2 * j - 1) ≠ 0 := by intro h; linarith
  have d4 : (2 * (n : ℚ) - 3 * j - 1) ≠ 0 := by intro h; linarith
  have d5 : (2 * (n : ℚ) - 3 * j - 2) ≠ 0 := by intro h; linarith
  have d6 : (2 * (n : ℚ) - 3 * j - 3) ≠ 0 := by intro h; linarith
  have hD : ((j : ℚ) + 1) ^ 2 * ((2 * (n : ℚ) - 2 * j) * (2 * (n : ℚ) - 2 * j - 1)) *
      ((2 * (n : ℚ) - 3 * j - 1) * (2 * (n : ℚ) - 3 * j - 2) * (2 * (n : ℚ) - 3 * j - 3)) ≠ 0 := by
    apply mul_ne_zero; apply mul_ne_zero; exact pow_ne_zero 2 d1
    exact mul_ne_zero d2 d3; exact mul_ne_zero (mul_ne_zero d4 d5) d6
  have hr : rho n j * (((j : ℚ) + 1) ^ 2 * ((2 * (n : ℚ) - 2 * j) * (2 * (n : ℚ) - 2 * j - 1)) *
      ((2 * (n : ℚ) - 3 * j - 1) * (2 * (n : ℚ) - 3 * j - 2) * (2 * (n : ℚ) - 3 * j - 3))) =
      -(4 * (j : ℚ) + 2) * ((n : ℚ) + 2 - j) ^ 3 *
        (((n : ℚ) + 2 - 3 * j) * ((n : ℚ) + 1 - 3 * j) * ((n : ℚ) - 3 * j)) := by
    unfold rho
    exact div_mul_cancel₀ _ hD
  rw [← sub_eq_zero]
  refine (mul_eq_zero.mp ?_).resolve_right hD
  linear_combination (norm := skip) (-(Pc (n : ℚ) ((j : ℚ) + 1))) * hr
  unfold Pc
  ring

private lemma GK (n : ℕ) : G n ((n + 2) / 3 + 1) = 0 := by
  unfold G; rw [L3]; ring

private lemma step (n j : ℕ) (hn : 6 ≤ n) (hj : 3 * j ≤ n + 2) :
    12 * (4 * ((n : ℚ) + 2) - 5) * (((n : ℚ) + 2) - 1) * (4 * ((n : ℚ) + 2) - 3) * U n j
      - 2 * (2 * ((n : ℚ) + 2) - 1) * (7 * ((n : ℚ) + 2) ^ 2 - 7 * ((n : ℚ) + 2) + 3) * U (n + 1) j
      + ((n : ℚ) + 2) ^ 3 * U (n + 2) j = G n (j + 1) - G n j := by
  rw [U0, U1 n j (by omega) (by omega), U2 n j (by omega) (by omega)]
  unfold G
  rw [L2 n j]
  push_cast
  linear_combination (b n j) * KI n j hn hj

private lemma ext_sum (n K : ℕ) (hK : n / 3 ≤ K) :
    ∑ j ∈ Finset.range (n / 3 + 1), U n j = ∑ j ∈ Finset.range (K + 1), U n j := by
  apply Finset.sum_subset
  · intro x hx; simp at hx ⊢; omega
  · intro x hx hx'
    simp at hx hx'
    unfold U Rr
    rw [dp_zero_of_lt n (3 * x) (by omega)]
    simp

private lemma a_eq (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ∑ j ∈ Finset.range (n / 3 + 1), U n j := by
  unfold a
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  simp at hj
  exact TL n j hn (by omega)

private def lhsP (n : ℕ) : ℤ :=
  (n : ℤ) ^ 3 * a n - 2 * (2 * (n : ℤ) - 1) * (7 * (n : ℤ) ^ 2 - 7 * (n : ℤ) + 3) * a (n - 1)
    + 12 * (4 * (n : ℤ) - 5) * ((n : ℤ) - 1) * (4 * (n : ℤ) - 3) * a (n - 2)

private lemma big (n : ℕ) (hn : 6 ≤ n) : lhsP (n + 2) = 0 := by
  have hK := Finset.sum_range_sub (G n) ((n + 2) / 3 + 1)
  rw [GK n, G0 n] at hK
  have hs : ∑ j ∈ Finset.range ((n + 2) / 3 + 1),
      (12 * (4 * ((n : ℚ) + 2) - 5) * (((n : ℚ) + 2) - 1) * (4 * ((n : ℚ) + 2) - 3) * U n j
      - 2 * (2 * ((n : ℚ) + 2) - 1) * (7 * ((n : ℚ) + 2) ^ 2 - 7 * ((n : ℚ) + 2) + 3) * U (n + 1) j
      + ((n : ℚ) + 2) ^ 3 * U (n + 2) j) = 0 := by
    rw [sub_zero] at hK; rw [← hK]
    apply Finset.sum_congr rfl
    intro j hj; simp at hj
    exact step n j hn (by omega)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hs
  have a0 := a_eq n (by omega)
  have a1 := a_eq (n + 1) (by omega)
  have a2 := a_eq (n + 2) (by omega)
  rw [ext_sum n ((n + 2) / 3) (by omega)] at a0
  rw [ext_sum (n + 1) ((n + 2) / 3) (by omega)] at a1
  rw [ext_sum (n + 2) ((n + 2) / 3) (by omega)] at a2
  have : ((lhsP (n + 2) : ℤ) : ℚ) = 0 := by
    unfold lhsP
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
    push_cast
    rw [a0, a1, a2]
    linear_combination hs
  exact_mod_cast this

theorem OMA.solution : type_of% @OMA.S_oeis_a219692.main := by
  intro n hn
  have h : lhsP n = 0 := by
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      exact big m (by omega)
  have h2 := h
  unfold lhsP at h2
  linarith
