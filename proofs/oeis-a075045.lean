import OMAStatements.S_oeis_a075045
import Mathlib

namespace OMA.S_oeis_a075045

lemma ch_succ (N k : ℕ) (hk : k ≤ N + 1) :
    (Nat.choose N k : ℚ) * ((N : ℚ) + 1) = Nat.choose (N + 1) k * (((N : ℚ) + 1) - k) := by
  have h := Nat.choose_mul_succ_eq N k
  have h' : ((Nat.choose N k * (N + 1) : ℕ) : ℚ) = ((Nat.choose (N + 1) k * (N + 1 - k) : ℕ) : ℚ) := by
    rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  exact h'

lemma ch_up (N k : ℕ) :
    ((Nat.choose (N + 1) (k + 1) : ℚ)) * ((k : ℚ) + 1) = ((N : ℚ) + 1) * Nat.choose N k := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : (((N + 1) * Nat.choose N k : ℕ) : ℚ) = ((Nat.choose (N + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

lemma ch3 (N k : ℕ) (hk : k ≤ N + 1) :
    (Nat.choose (N + 3) k : ℚ) * ((((N : ℚ) + 3) - k) * (((N : ℚ) + 2) - k) * (((N : ℚ) + 1) - k))
      = (Nat.choose N k : ℚ) * (((N : ℚ) + 3) * ((N : ℚ) + 2) * ((N : ℚ) + 1)) := by
  have h1 := ch_succ N k hk
  have h2 := ch_succ (N + 1) k (by omega)
  have h3 := ch_succ (N + 2) k (by omega)
  push_cast at h1 h2 h3
  rw [show N + 1 + 1 = N + 2 from rfl] at h2
  rw [show N + 2 + 1 = N + 3 from rfl] at h3
  rw [show (N:ℚ) + 2 + 1 = N + 3 by ring] at h3
  linear_combination (-((((N:ℚ) + 2) - k) * (((N:ℚ) + 1) - k))) * h3
    + (-(((N:ℚ) + 3) * (((N:ℚ) + 1) - k))) * h2 + (-(((N:ℚ) + 3) * ((N:ℚ) + 2))) * h1

noncomputable def FQ (n k : ℕ) : ℚ := (2 : ℚ) ^ n / 2 ^ k * (Nat.choose (3 * n + 4) k : ℚ)

def PP (n k : ℚ) : ℚ := 6 * (3 * k ^ 2 - 24 * k * n - 49 * k + 57 * n ^ 2 + 233 * n + 236)

noncomputable def G (n k : ℕ) : ℚ :=
  FQ n k * k * PP n k / (((3 * (n:ℚ) + 5) - k) * ((3 * (n:ℚ) + 6) - k) * ((3 * (n:ℚ) + 7) - k))

lemma term (n k : ℕ) (hk : k ≤ n) :
    27 * FQ n k - 4 * FQ (n + 1) k = G n (k + 1) - G n k := by
  set x : ℚ := (Nat.choose (3 * n + 4) k : ℚ) with hx
  have hk' : (k : ℚ) ≤ n := by exact_mod_cast hk
  have d1 : (3 * (n:ℚ) + 5) - k ≠ 0 := by linarith
  have d2 : (3 * (n:ℚ) + 6) - k ≠ 0 := by linarith
  have d3 : (3 * (n:ℚ) + 7) - k ≠ 0 := by linarith
  have e1 : (Nat.choose (3 * (n + 1) + 4) k : ℚ) = x * ((3 * (n:ℚ) + 7) * (3 * n + 6) * (3 * n + 5))
      / (((3 * (n:ℚ) + 5) - k) * ((3 * (n:ℚ) + 6) - k) * ((3 * (n:ℚ) + 7) - k)) := by
    have := ch3 (3 * n + 4) k (by omega)
    have e : 3 * (n + 1) + 4 = 3 * n + 4 + 3 := by ring
    rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero d1 d2) d3)]
    push_cast at this
    rw [hx]
    linear_combination this
  have g1 : (Nat.choose (3 * n + 4) (k + 1) : ℚ) * ((k : ℚ) + 1) = (3 * (n:ℚ) + 4 - k) * x := by
    have h := Nat.choose_succ_right_eq (3 * n + 4) k
    have h' : ((Nat.choose (3 * n + 4) (k + 1) * (k + 1) : ℕ) : ℚ) = ((Nat.choose (3 * n + 4) k * (3 * n + 4 - k) : ℕ) : ℚ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at h'
    push_cast at h'
    rw [hx]; linarith
  have G1 : (Nat.choose (3 * n + 4) (k + 1) : ℚ) = (3 * (n:ℚ) + 4 - k) * x / ((k : ℚ) + 1) := by
    rw [eq_div_iff (by positivity)]; exact g1
  unfold G FQ
  rw [e1, G1]
  rw [← hx]
  push_cast
  rw [pow_succ, pow_succ]
  unfold PP
  have d0 : 3 * (n:ℚ) + 4 - k ≠ 0 := by linarith
  rw [show 3 * (n:ℚ) + 5 - (k + 1) = 3 * n + 4 - k by ring, show 3 * (n:ℚ) + 6 - (k + 1) = 3 * n + 5 - k by ring,
    show 3 * (n:ℚ) + 7 - (k + 1) = 3 * n + 6 - k by ring]
  field_simp
  ring

lemma aq_eq (n : ℕ) : (a n : ℚ) = ∑ k ∈ Finset.range (n + 1), FQ n k := by
  unfold a FQ
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [pow_sub₀ _ (by norm_num) hk', div_eq_mul_inv]

noncomputable def H (n : ℕ) : ℚ := (Nat.choose (3 * n + 7) (n + 1) : ℚ)

lemma step (n : ℕ) :
    4 * (a (n + 1) : ℚ) = 27 * (a n : ℚ)
      + 2 * ((n:ℚ) + 3) * (7 * (n:ℚ) + 15) / (((n:ℚ) + 2) * (3 * (n:ℚ) + 5) * (3 * (n:ℚ) + 7)) * H n := by
  have hs : ∑ k ∈ Finset.range (n + 1), (27 * FQ n k - 4 * FQ (n + 1) k) = G n (n + 1) - G n 0 := by
    rw [Finset.sum_congr rfl (fun k hk => term n k (by have := Finset.mem_range.mp hk; omega))]
    exact Finset.sum_range_sub (fun k => G n k) (n + 1)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← aq_eq] at hs
  have hs2 : ∑ k ∈ Finset.range (n + 1), FQ (n + 1) k = (a (n + 1) : ℚ) - FQ (n + 1) (n + 1) := by
    have := aq_eq (n + 1)
    rw [Finset.sum_range_succ] at this
    linarith
  rw [hs2] at hs
  have hF : FQ (n + 1) (n + 1) = H n := by
    unfold FQ H
    rw [div_self (by positivity), one_mul, show 3 * (n + 1) + 4 = 3 * n + 7 by ring]
  have hG0 : G n 0 = 0 := by simp [G]
  have hc := ch3 (3 * n + 4) (n + 1) (by omega)
  have e : 3 * n + 4 + 3 = 3 * n + 7 := by ring
  rw [e] at hc
  push_cast at hc
  have hGn : G n (n + 1) = (2:ℚ) ^ n / 2 ^ (n + 1) * (Nat.choose (3 * n + 4) (n + 1) : ℚ) * ((n:ℚ) + 1)
      * PP n ((n:ℚ) + 1) / (((3 * (n:ℚ) + 5) - ((n:ℚ) + 1)) * ((3 * (n:ℚ) + 6) - ((n:ℚ) + 1)) * ((3 * (n:ℚ) + 7) - ((n:ℚ) + 1))) := by
    unfold G FQ
    push_cast
    rfl
  have hCn : (Nat.choose (3 * n + 4) (n + 1) : ℚ) = H n * ((2 * (n:ℚ) + 6) * (2 * n + 5) * (2 * n + 4)) / ((3 * (n:ℚ) + 7) * (3 * n + 6) * (3 * n + 5)) := by
    rw [eq_div_iff (by positivity)]
    unfold H
    have h2 : (3 * (n:ℚ) + 4 + 3 - (n + 1)) = 2 * n + 6 := by ring
    have h3 : (3 * (n:ℚ) + 4 + 2 - (n + 1)) = 2 * n + 5 := by ring
    have h4 : (3 * (n:ℚ) + 4 + 1 - (n + 1)) = 2 * n + 4 := by ring
    rw [h2, h3, h4] at hc
    linear_combination (-1 : ℚ) * hc
  rw [hG0, hGn, hCn, hF] at hs
  have e2 : (2:ℚ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e2] at hs
  unfold PP at hs
  have p1 : (0:ℚ) < 2 ^ n := by positivity
  rw [show 3 * (n:ℚ) + 5 - (n + 1) = 2 * n + 4 by ring, show 3 * (n:ℚ) + 6 - (n + 1) = 2 * n + 5 by ring,
    show 3 * (n:ℚ) + 7 - (n + 1) = 2 * n + 6 by ring] at hs
  have q1 : (2 * (n:ℚ) + 4) ≠ 0 := by positivity
  have q2 : (2 * (n:ℚ) + 5) ≠ 0 := by positivity
  have q3 : (2 * (n:ℚ) + 6) ≠ 0 := by positivity
  have q4 : (3 * (n:ℚ) + 5) ≠ 0 := by positivity
  have q5 : (3 * (n:ℚ) + 6) ≠ 0 := by positivity
  have q6 : (3 * (n:ℚ) + 7) ≠ 0 := by positivity
  have q7 : ((n:ℚ) + 2) ≠ 0 := by positivity
  field_simp at hs ⊢
  linear_combination (-1/6 : ℚ) * hs

lemma H_succ (n : ℕ) :
    H (n + 1) = H n * (((3 * (n:ℚ) + 8) * (3 * (n:ℚ) + 9) * (3 * (n:ℚ) + 10))
      / (((n:ℚ) + 2) * (2 * (n:ℚ) + 7) * (2 * (n:ℚ) + 8))) := by
  have u := ch_up (3 * n + 9) (n + 1)
  have c1 := ch_succ (3 * n + 7) (n + 1) (by omega)
  have c2 := ch_succ (3 * n + 7 + 1) (n + 1) (by omega)
  push_cast at u c1 c2
  rw [show 3 * n + 7 + 1 = 3 * n + 8 from rfl] at c2
  rw [show 3 * n + 9 + 1 = 3 * n + 10 from rfl, show n + 1 + 1 = n + 2 from rfl] at u
  have hH : H (n + 1) = (Nat.choose (3 * n + 10) (n + 2) : ℚ) := by
    unfold H
    rw [show 3 * (n + 1) + 7 = 3 * n + 10 by ring]
  have hH0 : H n = (Nat.choose (3 * n + 7) (n + 1) : ℚ) := rfl
  rw [hH, hH0]
  have q1 : ((n:ℚ) + 2) ≠ 0 := by positivity
  have q2 : (2 * (n:ℚ) + 7) ≠ 0 := by positivity
  have q3 : (2 * (n:ℚ) + 8) ≠ 0 := by positivity
  rw [mul_div_assoc', eq_div_iff (by positivity)]
  generalize (Nat.choose (3 * n + 10) (n + 2) : ℚ) = X at *
  generalize (Nat.choose (3 * n + 9) (n + 1) : ℚ) = Z at *
  generalize (Nat.choose (3 * n + 8) (n + 1) : ℚ) = W at *
  generalize (Nat.choose (3 * n + 7) (n + 1) : ℚ) = Y at *
  have c1' : Y * (3 * (n:ℚ) + 8) = W * (2 * n + 7) := by linarith
  have c2' : W * (3 * (n:ℚ) + 9) = Z * (2 * n + 8) := by linarith
  have u' : X * ((n:ℚ) + 2) = (3 * n + 10) * Z := by linarith
  linear_combination ((2 * (n:ℚ) + 7) * (2 * n + 8)) * u' + ((3 * (n:ℚ) + 10) * (2 * n + 7)) * (-1 : ℚ) * c2'
    + ((3 * (n:ℚ) + 10) * (3 * n + 9)) * (-1 : ℚ) * c1'

lemma rec_q (m : ℕ) :
    8 * (2 * ((m:ℚ) + 2) + 3) * (7 * ((m:ℚ) + 2) + 1) * (((m:ℚ) + 2) + 1) * (a (m + 2) : ℚ)
    + 6 * (-252 * ((m:ℚ) + 2) ^ 3 - 477 * ((m:ℚ) + 2) ^ 2 - 220 * ((m:ℚ) + 2) - 11) * (a (m + 1) : ℚ)
    + 81 * (7 * ((m:ℚ) + 2) + 8) * (3 * ((m:ℚ) + 2) - 1) * (3 * ((m:ℚ) + 2) + 1) * (a m : ℚ) = 0 := by
  have s0 := step m
  have s1 := step (m + 1)
  rw [H_succ m] at s1
  push_cast at s1
  have q1 : ((m:ℚ) + 2) ≠ 0 := by positivity
  have q2 : ((m:ℚ) + 3) ≠ 0 := by positivity
  have q3 : (3 * (m:ℚ) + 5) ≠ 0 := by positivity
  have q4 : (3 * (m:ℚ) + 7) ≠ 0 := by positivity
  have q5 : (2 * (m:ℚ) + 7) ≠ 0 := by positivity
  have q6 : (2 * (m:ℚ) + 8) ≠ 0 := by positivity
  have q7 : ((m:ℚ) + 4) ≠ 0 := by positivity
  have q8 : (3 * (m:ℚ) + 8) ≠ 0 := by positivity
  have q9 : (3 * (m:ℚ) + 10) ≠ 0 := by positivity
  have e1 : (a (m + 1) : ℚ) = (27 * (a m : ℚ) + 2 * ((m:ℚ) + 3) * (7 * (m:ℚ) + 15) / (((m:ℚ) + 2) * (3 * (m:ℚ) + 5) * (3 * (m:ℚ) + 7)) * H m) / 4 := by
    linarith
  have e2 : (a (m + 2) : ℚ) = (27 * (a (m + 1) : ℚ) + 2 * ((m:ℚ) + 1 + 3) * (7 * ((m:ℚ) + 1) + 15) / (((m:ℚ) + 1 + 2) * (3 * ((m:ℚ) + 1) + 5) * (3 * ((m:ℚ) + 1) + 7)) * (H m * (((3 * (m:ℚ) + 8) * (3 * (m:ℚ) + 9) * (3 * (m:ℚ) + 10)) / (((m:ℚ) + 2) * (2 * (m:ℚ) + 7) * (2 * (m:ℚ) + 8)))))/ 4 := by
    linarith
  rw [e2, e1]
  field_simp
  ring

end OMA.S_oeis_a075045

theorem OMA.solution : type_of% @OMA.S_oeis_a075045.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := OMA.S_oeis_a075045.rec_q m
  have e1 : m + 2 - 1 = m + 1 := rfl
  have e2 : m + 2 - 2 = m := rfl
  rw [e1, e2]
  have : ((8 * (2 * ((m + 2 : ℕ) : ℤ) + 3) * (7 * ((m + 2 : ℕ) : ℤ) + 1) * (((m + 2 : ℕ) : ℤ) + 1) * OMA.S_oeis_a075045.a (m + 2)
      + 6 * (-252 * ((m + 2 : ℕ) : ℤ) ^ 3 - 477 * ((m + 2 : ℕ) : ℤ) ^ 2 - 220 * ((m + 2 : ℕ) : ℤ) - 11) * OMA.S_oeis_a075045.a (m + 1)
      + 81 * (7 * ((m + 2 : ℕ) : ℤ) + 8) * (3 * ((m + 2 : ℕ) : ℤ) - 1) * (3 * ((m + 2 : ℕ) : ℤ) + 1) * OMA.S_oeis_a075045.a m : ℤ) : ℚ) = 0 := by
    push_cast at h ⊢
    linarith
  exact_mod_cast this
