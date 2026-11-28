import OMAStatements.S_oeis_a268543
import Mathlib

namespace OMA.S_oeis_a268543

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

def c0 (m : ℚ) : ℚ := -4 * (m + 1) * (2 * m + 1) ^ 2 * (17 * m + 28)
def c1 (m : ℚ) : ℚ := 2 * (2 * m + 1) * (1207 * m ^ 3 + 4402 * m ^ 2 + 5021 * m + 1730)
def c2 (m : ℚ) : ℚ := -8 * (2 * m + 1) * (2 * m + 3) * (m + 2) * (17 * m + 11)
def PP (m k : ℚ) : ℚ := 17 * k ^ 2 * m ^ 2 + 45 * k ^ 2 * m + 22 * k ^ 2 + 731 * k * m ^ 3 + 2700 * k * m ^ 2
  + 3103 * k * m + 1074 * k + 2006 * m ^ 4 + 8523 * m ^ 3 + 12737 * m ^ 2 + 7878 * m + 1724
noncomputable def G (m k : ℕ) : ℚ :=
  (k : ℚ) ^ 2 * PP m k * (Nat.choose (m + 2) k : ℚ) * (Nat.choose (2 * m + k) k : ℚ) / (((m : ℚ) + 1) * ((m : ℚ) + 2))

lemma term (m k : ℕ) (hk : k ≤ m + 2) :
    c0 m * ((Nat.choose m k : ℚ) * Nat.choose (2 * m + k) k)
    + c1 m * ((Nat.choose (m + 1) k : ℚ) * Nat.choose (2 * (m + 1) + k) k)
    + c2 m * ((Nat.choose (m + 2) k : ℚ) * Nat.choose (2 * (m + 2) + k) k)
    = G m (k + 1) - G m k := by
  set x : ℚ := (Nat.choose (m + 2) k : ℚ) with hx
  set y : ℚ := (Nat.choose (2 * m + k) k : ℚ) with hy
  have hm1 : (0:ℚ) < (m:ℚ) + 1 := by positivity
  have hm2 : (0:ℚ) < (m:ℚ) + 2 := by positivity
  have hkk : (0:ℚ) < (k:ℚ) + 1 := by positivity
  -- C(m+1,k)
  have e1 : (Nat.choose (m + 1) k : ℚ) = x * (((m:ℚ) + 2) - k) / ((m:ℚ) + 2) := by
    have := ch_succ (m + 1) k hk
    push_cast at this
    rw [eq_div_iff hm2.ne']
    rw [hx]; linarith
  have e0 : (Nat.choose m k : ℚ) = (Nat.choose (m + 1) k : ℚ) * (((m:ℚ) + 1) - k) / ((m:ℚ) + 1) := by
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · have hk2 : k = m + 2 := by omega
      subst hk2
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · have := ch_succ m k h
      rw [eq_div_iff hm1.ne']
      linarith
  -- upper entries
  have f1 : (Nat.choose (2 * (m + 1) + k) k : ℚ) * (((2:ℚ) * m + 1) * (2 * m + 2))
      = y * (((2:ℚ) * m + k + 1) * (2 * m + k + 2)) := by
    have a1 := ch_succ (2 * m + k) (k) (by omega)
    have a2 := ch_succ (2 * m + k + 1) k (by omega)
    have e : 2 * (m + 1) + k = 2 * m + k + 1 + 1 := by ring
    rw [e]
    push_cast at a1 a2
    have s1 : (2 * (m:ℚ) + k + 1 - k) = 2 * m + 1 := by ring
    have s2 : (2 * (m:ℚ) + k + 1 + 1 - k) = 2 * m + 2 := by ring
    rw [s1] at a1
    rw [s2] at a2
    rw [hy]
    nlinarith [a1, a2]
  have f2 : (Nat.choose (2 * (m + 2) + k) k : ℚ) * (((2:ℚ) * m + 1) * (2 * m + 2) * (2 * m + 3) * (2 * m + 4))
      = y * (((2:ℚ) * m + k + 1) * (2 * m + k + 2) * (2 * m + k + 3) * (2 * m + k + 4)) := by
    have a1 := ch_succ (2 * m + k) (k) (by omega)
    have a2 := ch_succ (2 * m + k + 1) k (by omega)
    have a3 := ch_succ (2 * m + k + 1 + 1) k (by omega)
    have a4 := ch_succ (2 * m + k + 1 + 1 + 1) k (by omega)
    have e : 2 * (m + 2) + k = 2 * m + k + 1 + 1 + 1 + 1 := by ring
    rw [e]
    push_cast at a1 a2 a3 a4
    have s1 : (2 * (m:ℚ) + k + 1 - k) = 2 * m + 1 := by ring
    have s2 : (2 * (m:ℚ) + k + 1 + 1 - k) = 2 * m + 2 := by ring
    have s3 : (2 * (m:ℚ) + k + 1 + 1 + 1 - k) = 2 * m + 3 := by ring
    have s4 : (2 * (m:ℚ) + k + 1 + 1 + 1 + 1 - k) = 2 * m + 4 := by ring
    rw [s1] at a1
    rw [s2] at a2
    rw [s3] at a3
    rw [s4] at a4
    rw [hy]
    generalize (Nat.choose (2 * m + k) k : ℚ) = A at *
    generalize (Nat.choose (2 * m + k + 1) k : ℚ) = B at *
    generalize (Nat.choose (2 * m + k + 1 + 1) k : ℚ) = C at *
    generalize (Nat.choose (2 * m + k + 1 + 1 + 1) k : ℚ) = D at *
    generalize (Nat.choose (2 * m + k + 1 + 1 + 1 + 1) k : ℚ) = E at *
    have hB : B * (2 * m + 1) = A * (2 * m + k + 1) := by linarith
    have hC : C * (2 * m + 2) = B * (2 * m + k + 2) := by linarith
    have hD : D * (2 * m + 3) = C * (2 * m + k + 3) := by linarith
    have hE : E * (2 * m + 4) = D * (2 * m + k + 4) := by linarith
    calc E * ((2 * (m:ℚ) + 1) * (2 * m + 2) * (2 * m + 3) * (2 * m + 4))
        = (E * (2 * m + 4)) * ((2 * m + 1) * (2 * m + 2) * (2 * m + 3)) := by ring
      _ = D * (2 * m + k + 4) * ((2 * m + 1) * (2 * m + 2) * (2 * m + 3)) := by rw [hE]
      _ = (D * (2 * m + 3)) * (2 * m + k + 4) * ((2 * m + 1) * (2 * m + 2)) := by ring
      _ = C * (2 * m + k + 3) * (2 * m + k + 4) * ((2 * m + 1) * (2 * m + 2)) := by rw [hD]
      _ = (C * (2 * m + 2)) * (2 * m + k + 3) * (2 * m + k + 4) * (2 * m + 1) := by ring
      _ = B * (2 * m + k + 2) * (2 * m + k + 3) * (2 * m + k + 4) * (2 * m + 1) := by rw [hC]
      _ = (B * (2 * m + 1)) * (2 * m + k + 2) * (2 * m + k + 3) * (2 * m + k + 4) := by ring
      _ = A * (2 * m + k + 1) * (2 * m + k + 2) * (2 * m + k + 3) * (2 * m + k + 4) := by rw [hB]
      _ = _ := by ring
  have g1 : (Nat.choose (m + 2) (k + 1) : ℚ) * ((k : ℚ) + 1) = ((m : ℚ) + 2 - k) * x := by
    have h := Nat.choose_succ_right_eq (m + 2) k
    have h' : ((Nat.choose (m + 2) (k + 1) * (k + 1) : ℕ) : ℚ) = ((Nat.choose (m + 2) k * (m + 2 - k) : ℕ) : ℚ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
    push_cast at h'
    rw [hx]; linarith
  have g2 : (Nat.choose (2 * m + (k + 1)) (k + 1) : ℚ) * ((k : ℚ) + 1) = (2 * (m:ℚ) + k + 1) * y := by
    have := ch_up (2 * m + k) k
    have e : 2 * m + (k + 1) = 2 * m + k + 1 := by ring
    rw [e]
    push_cast at this
    rw [hy]; linarith
  have hm3 : ((2:ℚ) * m + 1) ≠ 0 := by positivity
  have hm4 : ((2:ℚ) * m + 2) ≠ 0 := by positivity
  have hm5 : ((2:ℚ) * m + 3) ≠ 0 := by positivity
  have hm6 : ((2:ℚ) * m + 4) ≠ 0 := by positivity
  have F1 : (Nat.choose (2 * (m + 1) + k) k : ℚ) = y * (((2:ℚ) * m + k + 1) * (2 * m + k + 2)) / (((2:ℚ) * m + 1) * (2 * m + 2)) := by
    rw [eq_div_iff (mul_ne_zero hm3 hm4)]; exact f1
  have F2 : (Nat.choose (2 * (m + 2) + k) k : ℚ) = y * (((2:ℚ) * m + k + 1) * (2 * m + k + 2) * (2 * m + k + 3) * (2 * m + k + 4)) / (((2:ℚ) * m + 1) * (2 * m + 2) * (2 * m + 3) * (2 * m + 4)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hm3 hm4) hm5) hm6)]; exact f2
  have G1 : (Nat.choose (m + 2) (k + 1) : ℚ) = ((m : ℚ) + 2 - k) * x / ((k : ℚ) + 1) := by
    rw [eq_div_iff hkk.ne']; exact g1
  have G2 : (Nat.choose (2 * m + (k + 1)) (k + 1) : ℚ) = (2 * (m:ℚ) + k + 1) * y / ((k : ℚ) + 1) := by
    rw [eq_div_iff hkk.ne']; exact g2
  unfold G c0 c1 c2 PP
  rw [e0, e1, F1, F2]
  push_cast
  rw [G1, G2]
  field_simp
  ring

lemma sum_ext (n : ℕ) (N : ℕ) (hN : n + 1 ≤ N) :
    ∑ k ∈ Finset.range N, ((Nat.choose n k : ℚ) * Nat.choose (2 * n + k) k)
    = ∑ k ∈ Finset.range (n + 1), ((Nat.choose n k : ℚ) * Nat.choose (2 * n + k) k) := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk
  have : n < k := by simpa using hk
  simp [Nat.choose_eq_zero_of_lt this]

lemma rec_sum (m : ℕ) :
    c0 m * ∑ k ∈ Finset.range (m + 3), ((Nat.choose m k : ℚ) * Nat.choose (2 * m + k) k)
    + c1 m * ∑ k ∈ Finset.range (m + 3), ((Nat.choose (m + 1) k : ℚ) * Nat.choose (2 * (m + 1) + k) k)
    + c2 m * ∑ k ∈ Finset.range (m + 3), ((Nat.choose (m + 2) k : ℚ) * Nat.choose (2 * (m + 2) + k) k) = 0 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k hk => term m k (by have := Finset.mem_range.mp hk; omega))]
  rw [Finset.sum_range_sub (fun k => G m k)]
  have h0 : G m 0 = 0 := by simp [G]
  have h1 : G m (m + 3) = 0 := by
    simp [G, Nat.choose_eq_zero_of_lt (show m + 2 < m + 3 by omega)]
  rw [h0, h1]; ring


lemma rec_q (m : ℕ) :
    2 * ((m:ℚ) + 2) ^ 2 * (17 * ((m:ℚ) + 2) - 23) * (a (m + 2) : ℚ)
    + (-1207 * ((m:ℚ) + 2) ^ 3 + 2840 * ((m:ℚ) + 2) ^ 2 - 1897 * ((m:ℚ) + 2) + 360) * (a (m + 1) : ℚ)
    + 4 * (17 * ((m:ℚ) + 2) - 6) * (2 * ((m:ℚ) + 2) - 3) ^ 2 * (a m : ℚ) = 0 := by
  have hrec := rec_sum m
  rw [sum_ext m (m + 3) (by omega), sum_ext (m + 1) (m + 3) (by omega), sum_ext (m + 2) (m + 3) (by omega)] at hrec
  set S0 := ∑ k ∈ Finset.range (m + 1), ((Nat.choose m k : ℚ) * Nat.choose (2 * m + k) k)
  set S1 := ∑ k ∈ Finset.range (m + 1 + 1), ((Nat.choose (m + 1) k : ℚ) * Nat.choose (2 * (m + 1) + k) k)
  set S2 := ∑ k ∈ Finset.range (m + 2 + 1), ((Nat.choose (m + 2) k : ℚ) * Nat.choose (2 * (m + 2) + k) k)
  have ha0 : (a m : ℚ) = (Nat.choose (2 * m) m : ℚ) * S0 := by
    simp [a, S0]
  have ha1 : (a (m + 1) : ℚ) = (Nat.choose (2 * (m + 1)) (m + 1) : ℚ) * S1 := by
    simp [a, S1]
  have ha2 : (a (m + 2) : ℚ) = (Nat.choose (2 * (m + 2)) (m + 2) : ℚ) * S2 := by
    simp [a, S2]
  have hB1 : (Nat.choose (2 * (m + 1)) (m + 1) : ℚ) = 2 * (2 * (m:ℚ) + 1) * (Nat.choose (2 * m) m : ℚ) / ((m:ℚ) + 1) := by
    have := Nat.succ_mul_centralBinom_succ m
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at this
    have h' : (((m + 1) * Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℚ) = ((2 * (2 * m + 1) * Nat.choose (2 * m) m : ℕ) : ℚ) := by
      rw [this]
    push_cast at h'
    rw [eq_div_iff (by positivity)]; linarith
  have hB2 : (Nat.choose (2 * (m + 2)) (m + 2) : ℚ) = 2 * (2 * ((m:ℚ) + 1) + 1) * (Nat.choose (2 * (m + 1)) (m + 1) : ℚ) / ((m:ℚ) + 2) := by
    have := Nat.succ_mul_centralBinom_succ (m + 1)
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at this
    have h' : (((m + 1 + 1) * Nat.choose (2 * (m + 1 + 1)) (m + 1 + 1) : ℕ) : ℚ) = ((2 * (2 * (m + 1) + 1) * Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℚ) := by
      rw [this]
    push_cast at h'
    rw [eq_div_iff (by positivity)]
    have e : (m + 2 : ℕ) = m + 1 + 1 := rfl
    rw [e]; push_cast; linarith
  have key : 2 * ((m:ℚ) + 2) ^ 2 * (17 * ((m:ℚ) + 2) - 23) * (a (m + 2) : ℚ)
    + (-1207 * ((m:ℚ) + 2) ^ 3 + 2840 * ((m:ℚ) + 2) ^ 2 - 1897 * ((m:ℚ) + 2) + 360) * (a (m + 1) : ℚ)
    + 4 * (17 * ((m:ℚ) + 2) - 6) * (2 * ((m:ℚ) + 2) - 3) ^ 2 * (a m : ℚ)
    = (-(Nat.choose (2 * m) m : ℚ) / ((m:ℚ) + 1)) *
      (c0 m * S0 + c1 m * S1 + c2 m * S2) := by
    rw [ha0, ha1, ha2, hB2, hB1]
    unfold c0 c1 c2
    field_simp
    ring
  rw [key, hrec, mul_zero]

end OMA.S_oeis_a268543

theorem OMA.solution : type_of% @OMA.S_oeis_a268543.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := OMA.S_oeis_a268543.rec_q m
  have e1 : m + 2 - 1 = m + 1 := rfl
  have e2 : m + 2 - 2 = m := rfl
  rw [e1, e2]
  have : ((2 * ((m + 2 : ℕ) : ℤ) ^ 2 * (17 * ((m + 2 : ℕ) : ℤ) - 23) * OMA.S_oeis_a268543.a (m + 2)
      + (-1207 * ((m + 2 : ℕ) : ℤ) ^ 3 + 2840 * ((m + 2 : ℕ) : ℤ) ^ 2 - 1897 * ((m + 2 : ℕ) : ℤ) + 360) * OMA.S_oeis_a268543.a (m + 1)
      + 4 * (17 * ((m + 2 : ℕ) : ℤ) - 6) * (2 * ((m + 2 : ℕ) : ℤ) - 3) ^ 2 * OMA.S_oeis_a268543.a m : ℤ) : ℚ) = 0 := by
    push_cast at h ⊢
    linarith
  exact_mod_cast this
