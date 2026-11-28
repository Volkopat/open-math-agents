import OMAStatements.S_oeis_a228331
import Mathlib

open OMA.S_oeis_a228331

private def Pg (x y : ℚ) : ℚ :=
  (-1) * x ^ 0 * y ^ 4
    + (5) * x ^ 0 * y ^ 6
    + (-6) * x ^ 0 * y ^ 7
    + (2) * x ^ 0 * y ^ 8
    + (4) * x ^ 1 * y ^ 3
    + (6) * x ^ 1 * y ^ 4
    + (-30) * x ^ 1 * y ^ 5
    + (20) * x ^ 1 * y ^ 6
    + (6) * x ^ 1 * y ^ 7
    + (-6) * x ^ 1 * y ^ 8
    + (-4) * x ^ 2 * y ^ 2
    + (-24) * x ^ 2 * y ^ 3
    + (57) * x ^ 2 * y ^ 4
    + (6) * x ^ 2 * y ^ 5
    + (-63) * x ^ 2 * y ^ 6
    + (24) * x ^ 2 * y ^ 7
    + (4) * x ^ 2 * y ^ 8
    + (24) * x ^ 3 * y ^ 2
    + (-28) * x ^ 3 * y ^ 3
    + (-88) * x ^ 3 * y ^ 4
    + (140) * x ^ 3 * y ^ 5
    + (-24) * x ^ 3 * y ^ 6
    + (-24) * x ^ 3 * y ^ 7
    + (-12) * x ^ 4 * y ^ 2
    + (102) * x ^ 4 * y ^ 3
    + (-126) * x ^ 4 * y ^ 4
    + (-24) * x ^ 4 * y ^ 5
    + (60) * x ^ 4 * y ^ 6
    + (-31) * x ^ 5 * y ^ 2
    + (42) * x ^ 5 * y ^ 3
    + (66) * x ^ 5 * y ^ 4
    + (-80) * x ^ 5 * y ^ 5
    + (-1) * x ^ 6 * y ^ 2
    + (-48) * x ^ 6 * y ^ 3
    + (60) * x ^ 6 * y ^ 4
    + (12) * x ^ 7 * y ^ 2
    + (-24) * x ^ 7 * y ^ 3
    + (4) * x ^ 8 * y ^ 2

private lemma reflA (n : ℕ) : a n = (∑ m ∈ Finset.range (n + 1),
    ((n : ℚ) + 1 - m) ^ 7 * (((2 * n + 2).choose m : ℕ) : ℚ) ^ 2) / ((n : ℚ) + 1) ^ 2 := by
  unfold a h
  rw [← Finset.sum_range_reflect, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [show n + 1 - 1 - j = n - j by omega]
  unfold T
  rw [show n - (n - j) = j by omega]
  have hc := Nat.choose_mul_succ_eq (2 * n + 1) j
  rw [show 2 * n + 1 + 1 - j = 2 * n + 2 - j by omega, show 2 * n + 1 + 1 = 2 * n + 2 by ring] at hc
  have hc' : ((2 * n + 1).choose j : ℚ) * (2 * (n : ℚ) + 2) = ((2 * n + 2).choose j : ℚ) * (2 * (n : ℚ) + 2 - j) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) hc
    push_cast [Nat.cast_sub (show j ≤ 2 * n + 2 by omega)] at this
    linarith
  have hj' : (j : ℚ) ≤ n := by exact_mod_cast (show j ≤ n by omega)
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
  have h3 : ((n : ℚ) + ((n - j : ℕ) : ℚ) + 2) ≠ 0 := by positivity
  have hcast : ((n - j : ℕ) : ℚ) = (n : ℚ) - j := by rw [Nat.cast_sub (by omega)]
  have hq : ((2 * n + 1).choose j : ℚ) = ((2 * n + 2).choose j : ℚ) * (2 * (n : ℚ) + 2 - j) / (2 * (n : ℚ) + 2) := by
    rw [eq_div_iff h2]; exact hc'
  have hT : ((2 * n + 1).choose j : ℚ) * (2 * (((n - j : ℕ) : ℚ) + 1)) / ((n : ℚ) + ((n - j : ℕ) : ℚ) + 2) =
      ((2 * n + 2).choose j : ℚ) * ((n : ℚ) + 1 - j) / ((n : ℚ) + 1) := by
    rw [div_eq_div_iff h3 h1, hcast]
    linear_combination ((n : ℚ) - j + 1) * hc'
  rw [hT, hcast]
  field_simp
  ring

private def Dd (x : ℚ) : ℚ := 4 * (2 * x - 1) * (x - 1) * (2 * x - 3)

private lemma gos (N M : ℕ) (hM : M ≤ 2 * N) :
    Dd N * ∑ m ∈ Finset.range M, ((N : ℚ) - m) ^ 7 * (((2 * N).choose m : ℕ) : ℚ) ^ 2 =
      Pg N M * (((2 * N).choose M : ℕ) : ℚ) ^ 2 := by
  induction M with
  | zero => simp [Pg]
  | succ M ih =>
    have ih' := ih (by omega)
    have hc := Nat.choose_succ_right_eq (2 * N) M
    have hc' : (((2 * N).choose (M + 1) : ℕ) : ℚ) * ((M : ℚ) + 1) =
        (((2 * N).choose M : ℕ) : ℚ) * (2 * (N : ℚ) - M) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) hc
      push_cast [Nat.cast_sub (show M ≤ 2 * N by omega)] at this
      linarith
    have hM1 : ((M : ℚ) + 1) ≠ 0 := by positivity
    have hq : (((2 * N).choose (M + 1) : ℕ) : ℚ) = (((2 * N).choose M : ℕ) : ℚ) * (2 * (N : ℚ) - M) / ((M : ℚ) + 1) := by
      rw [eq_div_iff hM1]; exact hc'
    rw [Finset.sum_range_succ, mul_add, ih', hq]
    push_cast
    field_simp
    unfold Pg Dd
    ring

private lemma closed (n : ℕ) : a n = ((n.centralBinom : ℕ) : ℚ) ^ 2 * (2 * (n : ℚ) + 1) *
    (3 * (n : ℚ) ^ 2 + n - 1) / (2 * (n : ℚ) - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; norm_num [a, h, T]
  · rw [reflA n]
    have g := gos (n + 1) (n + 1) (by omega)
    rw [show 2 * (n + 1) = 2 * n + 2 by ring] at g
    have hcb := Nat.succ_mul_centralBinom_succ n
    rw [Nat.centralBinom_eq_two_mul_choose (n + 1), show 2 * (n + 1) = 2 * n + 2 by ring] at hcb
    have hcb' : (((2 * n + 2).choose (n + 1) : ℕ) : ℚ) = ((n.centralBinom : ℕ) : ℚ) * (2 * (2 * (n : ℚ) + 1)) / ((n : ℚ) + 1) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) hcb
      push_cast at this
      have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
      rw [eq_div_iff h1]; linarith
    have hs : ∑ m ∈ Finset.range (n + 1), ((n : ℚ) + 1 - m) ^ 7 * (((2 * n + 2).choose m : ℕ) : ℚ) ^ 2 =
        Pg ((n + 1 : ℕ) : ℚ) ((n + 1 : ℕ) : ℚ) * (((2 * n + 2).choose (n + 1) : ℕ) : ℚ) ^ 2 / Dd ((n + 1 : ℕ) : ℚ) := by
      have hD : Dd ((n + 1 : ℕ) : ℚ) ≠ 0 := by
        unfold Dd; push_cast
        have : (1 : ℚ) ≤ n := by exact_mod_cast hpos
        have a1 : (2 * ((n : ℚ) + 1) - 1) ≠ 0 := by intro h; linarith
        have a2 : ((n : ℚ) + 1 - 1) ≠ 0 := by intro h; linarith
        have a3 : (2 * ((n : ℚ) + 1) - 3) ≠ 0 := by intro h; linarith
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) a1) a2) a3
      rw [eq_div_iff hD]
      push_cast at g ⊢
      linear_combination g
    rw [hs, hcb']
    have : (1 : ℚ) ≤ n := by exact_mod_cast hpos
    have a1 : (2 * (n : ℚ) - 1) ≠ 0 := by intro h; linarith
    have a2 : (n : ℚ) ≠ 0 := by intro h; linarith
    have a3 : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    have a4 : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    rw [show Dd ((n : ℚ) + 1) = 4 * (2 * (n : ℚ) + 1) * n * (2 * (n : ℚ) - 1) by unfold Dd; ring]
    unfold Pg
    field_simp
    ring

private lemma cbs (m : ℕ) : ((m + 1).centralBinom : ℚ) = (m.centralBinom : ℚ) * (2 * (2 * (m : ℚ) + 1)) / ((m : ℚ) + 1) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at this
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff h1]; linarith

private lemma key (x c : ℚ) (hx : 0 ≤ x) (b1 : 2 * x - 1 ≠ 0) :
    (x + 3) ^ 2 * ((c * (2 * (2 * x + 1)) / (x + 1) * (2 * (2 * (x + 1) + 1)) / (x + 1 + 1) *
      (2 * (2 * (x + 2) + 1)) / (x + 2 + 1)) ^ 2 * (2 * (x + 3) + 1) * (3 * (x + 3) ^ 2 + (x + 3) - 1) /
        (2 * (x + 3) - 1))
    + 4 * (2 * (x + 3) ^ 2 - 22 * (x + 3) + 11) *
      ((c * (2 * (2 * x + 1)) / (x + 1) * (2 * (2 * (x + 1) + 1)) / (x + 1 + 1)) ^ 2 *
        (2 * (x + 2) + 1) * (3 * (x + 2) ^ 2 + (x + 2) - 1) / (2 * (x + 2) - 1))
    + 16 * (-7 * (x + 3) ^ 2 - 54 * (x + 3) + 166) *
      ((c * (2 * (2 * x + 1)) / (x + 1)) ^ 2 * (2 * (x + 1) + 1) * (3 * (x + 1) ^ 2 + (x + 1) - 1) /
        (2 * (x + 1) - 1))
    - 1088 * (2 * (x + 3) - 3) * (2 * (x + 3) - 7) * (c ^ 2 * (2 * x + 1) * (3 * x ^ 2 + x - 1) / (2 * x - 1))
    = 0 := by
  rw [show x + 1 + 1 = x + 2 by ring, show x + 2 + 1 = x + 3 by ring,
    show 2 * (x + 3) - 1 = 2 * x + 5 by ring, show 2 * (x + 2) - 1 = 2 * x + 3 by ring,
    show 2 * (x + 1) - 1 = 2 * x + 1 by ring]
  have e1 : x + 1 ≠ 0 := by positivity
  have e2 : x + 2 ≠ 0 := by positivity
  have e3 : x + 3 ≠ 0 := by positivity
  have f1 : 2 * x + 1 ≠ 0 := by positivity
  have f3 : 2 * x + 3 ≠ 0 := by positivity
  have f5 : 2 * x + 5 ≠ 0 := by positivity
  have b1' : x * 2 - 1 ≠ 0 := by rw [mul_comm]; exact b1
  field_simp
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a228331.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  rw [closed (m + 3), closed (m + 2), closed (m + 1), closed m, cbs (m + 2), cbs (m + 1), cbs m]
  push_cast
  have b1 : (2 * (m : ℚ) - 1) ≠ 0 := by
    intro h
    have : (2 * (m : ℚ)) = 1 := by linarith
    have h2 : (2 * m : ℕ) = 1 := by exact_mod_cast this
    omega
  exact key (m : ℚ) _ (by positivity) b1
