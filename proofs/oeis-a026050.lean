import OMAStatements.S_oeis_a026050
import Mathlib

/-!
Splitting the dot product at i = m, for n = m + 7: d(n) = Sum_{i<m+1} (i+1)(i+7) +
Sum_{x<6} (m+2+x)(x+1), so 6 d(n) = 2n^3 - 15n^2 + 109n. Then d(n+4) - d(n) is even and
r(n+4) = r(n), so d(n) - r(n) is even for all n >= 7 (checked for n = 7..10), and
12 a(n) = 2n^3 - 15n^2 + 109n - 6 r(n). The operator (1+x^2)(1-x)^4 kills the cubic and the
4-periodic r, which gives the coefficients of x^n, n >= 13; the others are a finite check.
-/

namespace R026050
open OMA.S_oeis_a026050 PowerSeries

theorem S_closed (k : ℕ) :
    6 * ∑ i ∈ Finset.range k, (i + 1) * (i + 7) = 2 * k ^ 3 + 21 * k ^ 2 + 19 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem d_split (m : ℕ) : d (m + 7) = (∑ i ∈ Finset.range (m + 1), (i + 1) * (i + 7)) +
    ∑ x ∈ Finset.range 6, (m + 1 + x + 1) * (x + 1) := by
  unfold d
  rw [show m + 7 = m + 1 + 6 by ring, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (show i + 7 ≤ m + 1 + 6 by omega)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [if_neg (show ¬ (m + 1 + x + 7 ≤ m + 1 + 6) by omega)]
    congr 1
    omega

theorem d_closed (m : ℕ) : 6 * d (m + 7) = 2 * m ^ 3 + 27 * m ^ 2 + 193 * m + 714 := by
  rw [d_split, mul_add, S_closed]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem dZ (n : ℕ) (hn : 7 ≤ n) : (6 * d n : ℤ) = 2 * n ^ 3 - 15 * n ^ 2 + 109 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h := d_closed m
  have h' : (6 * d (m + 7) : ℤ) = 2 * m ^ 3 + 27 * m ^ 2 + 193 * m + 714 := by exact_mod_cast h
  push_cast
  linear_combination h'

theorem rle (n : ℕ) : r n ≤ 1 := by
  unfold r
  split_ifs <;> omega

theorem rstep (m : ℕ) : r (m + 11) = r (m + 7) := by
  have h : (m + 11 - 7) % 4 = (m + 7 - 7) % 4 := by omega
  unfold r
  rw [h]

theorem dstep (m : ℕ) : d (m + 11) = d (m + 7) + 4 * m ^ 2 + 52 * m + 222 := by
  have p1 : 7 ≤ m + 7 := by omega
  have p2 : 7 ≤ m + 11 := by omega
  have h1 := dZ (m + 7) p1
  have h2 := dZ (m + 11) p2
  push_cast at h1 h2
  have h3 : ((6 * d (m + 11) : ℕ) : ℤ) =
      ((6 * (d (m + 7) + 4 * m ^ 2 + 52 * m + 222) : ℕ) : ℤ) := by
    push_cast
    linear_combination h2 - h1
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 6) (by exact_mod_cast h3)

theorem par (m : ℕ) : (d (m + 7) + r (m + 7)) % 2 = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases (show m < 4 ∨ 4 ≤ m by omega) with h | h
    · interval_cases m <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      have h1 := ih k (by omega)
      rw [show k + 4 + 7 = k + 11 by ring, dstep, rstep]
      omega

theorem rel (n : ℕ) (hn : 7 ≤ n) : 2 * a n + r n = d n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h1 := par m
  have h2 := rle (m + 7)
  have h3 := d_closed m
  unfold a
  omega

theorem key (n : ℕ) (hn : 7 ≤ n) :
    (12 * a n : ℤ) = 2 * n ^ 3 - 15 * n ^ 2 + 109 * n - 6 * r n := by
  have h1 : (2 * a n + r n : ℤ) = d n := by exact_mod_cast rel n hn
  have h2 := dZ n hn
  linear_combination 6 * h1 + h2

theorem rchar (j : ℕ) : ((j - 7) % 4 = 0 ∧ r j = 1) ∨ ((j - 7) % 4 = 3 ∧ r j = 1) ∨
    ((j - 7) % 4 = 1 ∧ r j = 0) ∨ ((j - 7) % 4 = 2 ∧ r j = 0) := by
  unfold r
  split_ifs with h <;> omega

theorem rsum (m : ℕ) : (r (m + 13) : ℤ) - 4 * r (m + 12) + 7 * r (m + 11) - 8 * r (m + 10) +
    7 * r (m + 9) - 4 * r (m + 8) + r (m + 7) = 0 := by
  have c13 := rchar (m + 13)
  have c12 := rchar (m + 12)
  have c11 := rchar (m + 11)
  have c10 := rchar (m + 10)
  have c9 := rchar (m + 9)
  have c8 := rchar (m + 8)
  have c7 := rchar (m + 7)
  omega

theorem recur (m : ℕ) : (a (m + 13) : ℤ) - 4 * a (m + 12) + 7 * a (m + 11) - 8 * a (m + 10) +
    7 * a (m + 9) - 4 * a (m + 8) + a (m + 7) = 0 := by
  have p13 : 7 ≤ m + 13 := by omega
  have p12 : 7 ≤ m + 12 := by omega
  have p11 : 7 ≤ m + 11 := by omega
  have p10 : 7 ≤ m + 10 := by omega
  have p9 : 7 ≤ m + 9 := by omega
  have p8 : 7 ≤ m + 8 := by omega
  have p7 : 7 ≤ m + 7 := by omega
  have k13 := key (m + 13) p13
  have k12 := key (m + 12) p12
  have k11 := key (m + 11) p11
  have k10 := key (m + 10) p10
  have k9 := key (m + 9) p9
  have k8 := key (m + 8) p8
  have k7 := key (m + 7) p7
  have rs := rsum m
  push_cast at k13 k12 k11 k10 k9 k8 k7
  have h : (12 : ℤ) * ((a (m + 13) : ℤ) - 4 * a (m + 12) + 7 * a (m + 11) - 8 * a (m + 10) +
      7 * a (m + 9) - 4 * a (m + 8) + a (m + 7)) = 0 := by
    linear_combination k13 - 4 * k12 + 7 * k11 - 8 * k10 + 7 * k9 - 4 * k8 + k7 - 6 * rs
  linarith

theorem vals : a 7 = 59 ∧ a 8 = 78 ∧ a 9 = 102 ∧ a 10 = 132 ∧ a 11 = 170 ∧ a 12 = 217 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end R026050

open OMA.S_oeis_a026050 R026050 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a026050.main := by
  rw [show ((X ^ 2 + 1) * (X - 1) ^ 4 : ℤ⟦X⟧) =
      1 - C 4 * X ^ 1 + C 7 * X ^ 2 - C 8 * X ^ 3 + C 7 * X ^ 4 - C 4 * X ^ 5 + X ^ 6 by
      simp only [map_ofNat]; ring,
    show ∀ p : ℤ⟦X⟧, p * (1 - C 4 * X ^ 1 + C 7 * X ^ 2 - C 8 * X ^ 3 + C 7 * X ^ 4 -
      C 4 * X ^ 5 + X ^ 6) = p - C 4 * (p * X ^ 1) + C 7 * (p * X ^ 2) - C 8 * (p * X ^ 3) +
      C 7 * (p * X ^ 4) - C 4 * (p * X ^ 5) + p * X ^ 6 from fun p => by ring,
    show (X ^ 7 * (59 - 158 * X + 203 * X ^ 2 - 202 * X ^ 3 + 145 * X ^ 4 - 45 * X ^ 5) :
      ℤ⟦X⟧) = C 59 * X ^ 7 - C 158 * X ^ 8 + C 203 * X ^ 9 - C 202 * X ^ 10 +
      C 145 * X ^ 11 - C 45 * X ^ 12 by simp only [map_ofNat]; ring]
  ext n
  simp only [A, map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  by_cases hn : 13 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    have e1 : m + 13 - 1 = m + 12 := by omega
    have e2 : m + 13 - 2 = m + 11 := by omega
    have e3 : m + 13 - 3 = m + 10 := by omega
    have e4 : m + 13 - 4 = m + 9 := by omega
    have e5 : m + 13 - 5 = m + 8 := by omega
    have e6 : m + 13 - 6 = m + 7 := by omega
    have q13 : ¬ (m + 13 < 7) := by omega
    have q12 : ¬ (m + 12 < 7) := by omega
    have q11 : ¬ (m + 11 < 7) := by omega
    have q10 : ¬ (m + 10 < 7) := by omega
    have q9 : ¬ (m + 9 < 7) := by omega
    have q8 : ¬ (m + 8 < 7) := by omega
    have q7 : ¬ (m + 7 < 7) := by omega
    have hr := recur m
    simp [e1, e2, e3, e4, e5, e6, q13, q12, q11, q10, q9, q8, q7]
    linarith
  · interval_cases n <;> simp [vals]
