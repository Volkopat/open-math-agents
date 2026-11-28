import OMAStatements.S_oeis_a193663
import Mathlib

-- Problem: A193663, the g.f. x(1-x+x^2)/(1-2x-6x^2+7x^3+x^4) for
-- a(n) = Sum_{k=0..n} [x^k]F_n(x) r(n-k), F_n the Fibonacci polynomials.
-- Upstream: formal-conjectures statements/oeis-a193663.lean (declaration OMA.S_oeis_a193663.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated g.f. holds).
-- Proof: r(m+2) = 3r(m+1) - r(m) for m >= 1; with b_s(n) = Sum_k [x^k]F_n r(n+s-k) one has
-- b_s(n+2) = b_s(n+1) + b_{s+2}(n) and b_{s+2}(n) = 3b_{s+1}(n) - b_s(n), which give the
-- order-4 recurrence for a = b_0; then compare coefficients.

namespace OMA.P_oeis_a193663

open OMA.S_oeis_a193663 Finset Polynomial

def s (k : ℕ) : ℤ := ∑ i ∈ range (k + 1), ((i : ℤ) + 1) * r (k - i)

def t (k : ℕ) : ℤ := ∑ i ∈ range (k + 1), r (k - i)

theorem r_succ (k : ℕ) : r (k + 1) = s k := by
  rw [r, Fin.sum_univ_eq_sum_range (fun i => ((i : ℤ) + 1) * r (k - i)) (k + 1), s]

theorem t_succ (k : ℕ) : t (k + 1) = t k + r (k + 1) := by
  rw [t, sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  rfl

theorem s_succ (k : ℕ) : s (k + 1) = s k + t (k + 1) := by
  rw [t_succ, s, sum_range_succ', s, t]
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  push_cast
  rw [show (∑ i ∈ range (k + 1), ((i : ℤ) + 1 + 1) * r (k - i)) =
      ∑ i ∈ range (k + 1), ((i : ℤ) + 1) * r (k - i) + ∑ i ∈ range (k + 1), r (k - i) by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring]
  ring

theorem r_rec (m : ℕ) (hm : 1 ≤ m) : r (m + 2) = 3 * r (m + 1) - r m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : r (k + 3) = s (k + 2) := r_succ (k + 2)
  have h2 : r (k + 2) = s (k + 1) := r_succ (k + 1)
  have h3 : r (k + 1) = s k := r_succ k
  have h4 : s (k + 2) = s (k + 1) + t (k + 2) := s_succ (k + 1)
  have h5 : s (k + 1) = s k + t (k + 1) := s_succ k
  have h6 : t (k + 2) = t (k + 1) + r (k + 2) := t_succ (k + 1)
  show r (k + 3) = 3 * r (k + 2) - r (k + 1)
  linear_combination h1 + h4 + h6 - 2 * h2 - h5 + h3

theorem r1 : r 1 = 1 := by
  rw [r_succ, s]
  simp [r]

theorem r2 : r 2 = 3 := by
  rw [r_succ, s]
  simp [sum_range_succ, r1, r]

theorem Fc : ∀ n k : ℕ, n ≤ k → (F n).coeff k = 0
  | 0, k, _ => by simp [F]
  | 1, k, hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [F, coeff_one]
  | n + 2, k, hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [F, coeff_add, coeff_X_mul]
    rw [Fc (n + 1) j (by omega), Fc n (j + 1) (by omega)]
    simp

noncomputable def b (σ n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (F n).coeff k * r (n + σ - k)

theorem bext (σ n N : ℕ) (h : n + 1 ≤ N) :
    b σ n = ∑ k ∈ range N, (F n).coeff k * r (n + σ - k) := by
  apply sum_subset (range_mono h)
  intro k _ hk
  rw [mem_range, not_lt] at hk
  rw [Fc n k (by omega), zero_mul]

theorem b_step (σ n : ℕ) : b σ (n + 2) = b σ (n + 1) + b (σ + 2) n := by
  rw [bext (σ + 2) n (n + 3) (by omega), b, b]
  simp only [F, coeff_add, add_mul, sum_add_distrib]
  congr 1
  · rw [sum_range_succ']
    simp only [coeff_X_mul_zero, zero_mul, add_zero, coeff_X_mul]
    apply sum_congr rfl
    intro k _
    congr 2
    omega
  · apply sum_congr rfl
    intro k _
    congr 2
    omega

theorem b_rec (σ n : ℕ) : b (σ + 2) n = 3 * b (σ + 1) n - b σ n := by
  simp only [b, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  by_cases h : 1 ≤ n + σ - k
  · rw [show n + (σ + 2) - k = (n + σ - k) + 2 by omega,
      show n + (σ + 1) - k = (n + σ - k) + 1 by omega, r_rec _ h]
    ring
  · rw [show k = n by omega, Fc n n le_rfl]
    ring

theorem b_zero (σ : ℕ) : b σ 0 = 0 := by
  simp [b, F]

theorem b_one (σ : ℕ) : b σ 1 = r (σ + 1) := by
  simp [b, F, coeff_one, Nat.add_comm 1 σ]

theorem a_eq (n : ℕ) : a n = b 0 n := by
  simp only [a, b, Nat.add_zero]

theorem x_rec (n : ℕ) : b 0 (n + 2) = b 0 (n + 1) + 3 * b 1 n - b 0 n := by
  have h : b 0 (n + 2) = b 0 (n + 1) + b 2 n := b_step 0 n
  have h' : b 2 n = 3 * b 1 n - b 0 n := b_rec 0 n
  linear_combination h + h'

theorem y_rec (n : ℕ) : b 1 (n + 2) = b 1 (n + 1) + 8 * b 1 n - 3 * b 0 n := by
  have h : b 1 (n + 2) = b 1 (n + 1) + b 3 n := b_step 1 n
  have h' : b 3 n = 3 * b 2 n - b 1 n := b_rec 1 n
  have h'' : b 2 n = 3 * b 1 n - b 0 n := b_rec 0 n
  linear_combination h + h' + 3 * h''

theorem a_rec (n : ℕ) :
    a (n + 4) = 2 * a (n + 3) + 6 * a (n + 2) - 7 * a (n + 1) - a n := by
  simp only [a_eq]
  have e1 : b 0 (n + 2) = b 0 (n + 1) + 3 * b 1 n - b 0 n := x_rec n
  have e4 : b 0 (n + 3) = b 0 (n + 2) + 3 * b 1 (n + 1) - b 0 (n + 1) := x_rec (n + 1)
  have e2 : b 0 (n + 4) = b 0 (n + 3) + 3 * b 1 (n + 2) - b 0 (n + 2) := x_rec (n + 2)
  have e3 : b 1 (n + 2) = b 1 (n + 1) + 8 * b 1 n - 3 * b 0 n := y_rec n
  linear_combination e2 + 3 * e3 - e4 - 8 * e1

theorem a0 : a 0 = 0 := by rw [a_eq, b_zero]

theorem a1 : a 1 = 1 := by
  have h : b 0 1 = r 1 := b_one 0
  rw [a_eq, h, r1]

theorem a2 : a 2 = 1 := by
  have h : b 0 2 = b 0 1 + 3 * b 1 0 - b 0 0 := x_rec 0
  have h1 : b 0 1 = r 1 := b_one 0
  rw [a_eq, h, h1, b_zero, b_zero, r1]
  norm_num

theorem a3 : a 3 = 9 := by
  have h : b 0 3 = b 0 2 + 3 * b 1 1 - b 0 1 := x_rec 1
  have h1 : b 0 1 = r 1 := b_one 0
  have h2 : b 1 1 = r 2 := b_one 1
  have h3 : b 0 2 = 1 := by rw [← a_eq, a2]
  rw [a_eq, h, h1, h2, h3, r1, r2]
  norm_num

theorem key (f : PowerSeries ℤ) :
    f * (1 - 2 * PowerSeries.X - 6 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 3
      + PowerSeries.X ^ 4) =
      PowerSeries.C (1 : ℤ) * (PowerSeries.X ^ 0 * f) + PowerSeries.C (-2 : ℤ) * (PowerSeries.X ^ 1 * f)
        + PowerSeries.C (-6 : ℤ) * (PowerSeries.X ^ 2 * f) + PowerSeries.C (7 : ℤ) * (PowerSeries.X ^ 3 * f)
        + PowerSeries.C (1 : ℤ) * (PowerSeries.X ^ 4 * f) := by
  simp only [map_one, map_neg, map_ofNat]
  ring

theorem rhs : (PowerSeries.X : PowerSeries ℤ) * (1 - PowerSeries.X + PowerSeries.X ^ 2) =
    PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (-1 : ℤ) * PowerSeries.X ^ 2
      + PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 3 := by
  simp only [map_one, map_neg]
  ring

theorem main' :
    PowerSeries.mk a
        * (1 - 2 * PowerSeries.X - 6 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 3
          + PowerSeries.X ^ 4)
      = (PowerSeries.X : PowerSeries ℤ) * (1 - PowerSeries.X + PowerSeries.X ^ 2) := by
  rw [key, rhs]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases lt_or_ge n 4 with h | h
  · interval_cases n <;> simp [a0, a1, a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show 0 ≤ m + 4 by omega, show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega,
      show 3 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega, show m + 4 - 0 = m + 4 by omega,
      show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega, show m + 4 ≠ 1 by omega,
      show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega, if_true, if_false, a_rec]
    ring

end OMA.P_oeis_a193663

theorem OMA.solution : type_of% @OMA.S_oeis_a193663.main := OMA.P_oeis_a193663.main'
