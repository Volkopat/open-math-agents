import OMAStatements.S_oeis_a023864
import Mathlib

/-!
Write `S n K = ∑_{i=1}^{K} i F(n+2-i)`, so `a n = S n ((n+1)/2)`. For `K ≤ n + 2` the Fibonacci
recurrence gives `S (n+2) K = S (n+1) K + S n K`, so `a(n) - a(n-1) - a(n-2)` only sees the
boundary terms of the parity-dependent upper limit: it is `m F(m)` for `n = 2m` and
`(m+1) F(m+2)` for `n = 2m+1`. That sequence `c` satisfies the recurrence of `(1 - X^2 - X^4)^2`,
which gives the generating function in two steps.
-/

namespace R023864
open OMA.S_oeis_a023864 Finset PowerSeries

def S (n K : ℕ) : ℤ := ∑ i ∈ Icc 1 K, (i : ℤ) * (Nat.fib (n + 2 - i) : ℤ)

theorem a_eq (n : ℕ) : a023864 n = S n ((n + 1) / 2) := by
  unfold a023864 S
  split_ifs with h
  · subst h
    simp
  · rfl

theorem S_fib (n0 n1 n K : ℕ) (h0 : n0 = n + 2) (h1 : n1 = n + 1) (hK : K ≤ n + 2) :
    S n0 K = S n1 K + S n K := by
  subst h0 h1
  unfold S
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [show n + 2 + 2 - i = (n + 2 - i) + 2 by omega,
    show n + 1 + 2 - i = (n + 2 - i) + 1 by omega, Nat.fib_add_two (n := n + 2 - i)]
  push_cast
  ring

theorem S_succ (n K K' j : ℕ) (hK : K' = K + 1) (hj : j = n + 1 - K) :
    S n K' = S n K + (K' : ℤ) * Nat.fib j := by
  subst hK hj
  unfold S
  rw [Finset.sum_Icc_succ_top (by omega), show n + 2 - (K + 1) = n + 1 - K by omega]

theorem b_even (m : ℕ) :
    a023864 (2 * m + 2) - a023864 (2 * m + 1) - a023864 (2 * m)
      = ((m : ℤ) + 1) * Nat.fib (m + 1) := by
  rw [a_eq, a_eq, a_eq]
  rw [show (2 * m + 2 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
    show (2 * m + 1) / 2 = m by omega]
  have h1 := S_fib (2 * m + 2) (2 * m + 1) (2 * m) (m + 1) rfl rfl (by omega)
  have h2 := S_succ (2 * m) m (m + 1) (m + 1) rfl (by omega)
  push_cast at h2
  linear_combination h1 + h2

theorem b_odd (m : ℕ) :
    a023864 (2 * m + 3) - a023864 (2 * m + 2) - a023864 (2 * m + 1)
      = ((m : ℤ) + 2) * Nat.fib (m + 3) := by
  rw [a_eq, a_eq, a_eq]
  rw [show (2 * m + 3 + 1) / 2 = m + 2 by omega, show (2 * m + 2 + 1) / 2 = m + 1 by omega,
    show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  have h1 := S_fib (2 * m + 3) (2 * m + 2) (2 * m + 1) (m + 2) rfl rfl (by omega)
  have h2 := S_succ (2 * m + 2) (m + 1) (m + 2) (m + 2) rfl (by omega)
  have h3 := S_succ (2 * m + 1) (m + 1) (m + 2) (m + 1) rfl (by omega)
  push_cast at h2 h3
  have hf : (Nat.fib (m + 3) : ℤ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    exact_mod_cast Nat.fib_add_two (n := m + 1)
  linear_combination h1 + h2 + h3 - ((m : ℤ) + 2) * hf

def c (n : ℕ) : ℤ :=
  if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) * Nat.fib (n / 2)
  else ((n / 2 + 1 : ℕ) : ℤ) * Nat.fib (n / 2 + 2)

theorem c_even (n m : ℕ) (h : n = 2 * m) : c n = (m : ℤ) * Nat.fib m := by
  subst h
  unfold c
  rw [if_pos (by omega), show 2 * m / 2 = m by omega]

theorem c_odd (n m j : ℕ) (h : n = 2 * m + 1) (hj : j = m + 2) :
    c n = ((m : ℤ) + 1) * Nat.fib j := by
  subst h hj
  unfold c
  rw [if_neg (by omega), show (2 * m + 1) / 2 = m by omega]
  push_cast
  ring

theorem b_all (k : ℕ) : a023864 (k + 2) - a023864 (k + 1) - a023864 k = c (k + 2) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [b_even, c_even (2 * m + 2) (m + 1) (by omega)]
    push_cast
    ring
  · rw [show 2 * m + 1 + 2 = 2 * m + 3 by ring, show 2 * m + 1 + 1 = 2 * m + 2 by ring, b_odd,
      c_odd (2 * m + 3) (m + 1) (m + 3) (by omega) (by omega)]
    push_cast
    ring

theorem d_rec (m : ℕ) :
    ((m : ℤ) + 4) * Nat.fib (m + 4) - 2 * (((m : ℤ) + 3) * Nat.fib (m + 3))
      - ((m : ℤ) + 2) * Nat.fib (m + 2) + 2 * (((m : ℤ) + 1) * Nat.fib (m + 1))
      + (m : ℤ) * Nat.fib m = 0 := by
  have h2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_add_two (n := m)
  have h3 : (Nat.fib (m + 3) : ℤ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    exact_mod_cast Nat.fib_add_two (n := m + 1)
  have h4 : (Nat.fib (m + 4) : ℤ) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    exact_mod_cast Nat.fib_add_two (n := m + 2)
  linear_combination ((m : ℤ) + 4) * h4 + (-(m : ℤ) - 2) * h3 + (-(m : ℤ)) * h2

theorem e_rec (m : ℕ) :
    ((m : ℤ) + 5) * Nat.fib (m + 6) - 2 * (((m : ℤ) + 4) * Nat.fib (m + 5))
      - ((m : ℤ) + 3) * Nat.fib (m + 4) + 2 * (((m : ℤ) + 2) * Nat.fib (m + 3))
      + ((m : ℤ) + 1) * Nat.fib (m + 2) = 0 := by
  have h4 : (Nat.fib (m + 4) : ℤ) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    exact_mod_cast Nat.fib_add_two (n := m + 2)
  have h5 : (Nat.fib (m + 5) : ℤ) = Nat.fib (m + 3) + Nat.fib (m + 4) := by
    exact_mod_cast Nat.fib_add_two (n := m + 3)
  have h6 : (Nat.fib (m + 6) : ℤ) = Nat.fib (m + 4) + Nat.fib (m + 5) := by
    exact_mod_cast Nat.fib_add_two (n := m + 4)
  linear_combination ((m : ℤ) + 5) * h6 + (-(m : ℤ) - 3) * h5 + (-(m : ℤ) - 1) * h4

theorem c_rec (k : ℕ) :
    c (k + 8) - 2 * c (k + 6) - c (k + 4) + 2 * c (k + 2) + c k = 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have e8 := c_even (2 * m + 8) (m + 4) (by omega)
    have e6 := c_even (2 * m + 6) (m + 3) (by omega)
    have e4 := c_even (2 * m + 4) (m + 2) (by omega)
    have e2 := c_even (2 * m + 2) (m + 1) (by omega)
    have e0 := c_even (2 * m) m rfl
    push_cast at e8 e6 e4 e2
    linear_combination e8 - 2 * e6 - e4 + 2 * e2 + e0 + d_rec m
  · have e8 := c_odd (2 * m + 1 + 8) (m + 4) (m + 6) (by omega) (by omega)
    have e6 := c_odd (2 * m + 1 + 6) (m + 3) (m + 5) (by omega) (by omega)
    have e4 := c_odd (2 * m + 1 + 4) (m + 2) (m + 4) (by omega) (by omega)
    have e2 := c_odd (2 * m + 1 + 2) (m + 1) (m + 3) (by omega) (by omega)
    have e0 := c_odd (2 * m + 1) m (m + 2) rfl rfl
    push_cast at e8 e6 e4 e2
    linear_combination e8 - 2 * e6 - e4 + 2 * e2 + e0 + e_rec m

theorem a0 : a023864 0 = 0 := by decide
theorem a1 : a023864 1 = 1 := by decide
theorem c0 : c 0 = 0 := by decide
theorem c1 : c 1 = 1 := by decide
theorem c2 : c 2 = 1 := by decide
theorem c3 : c 3 = 4 := by decide
theorem c4 : c 4 = 2 := by decide
theorem c5 : c 5 = 9 := by decide
theorem c6 : c 6 = 6 := by decide
theorem c7 : c 7 = 20 := by decide

theorem step1 : ((1 - X - X ^ 2 : ℤ⟦X⟧)) * PowerSeries.mk a023864 = PowerSeries.mk c := by
  rw [show ((1 - X - X ^ 2 : ℤ⟦X⟧)) * PowerSeries.mk a023864
      = PowerSeries.mk a023864 - PowerSeries.mk a023864 * X ^ 1
        - PowerSeries.mk a023864 * X ^ 2 by ring]
  ext n
  simp only [map_sub, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp [a0, c0]
    · simp [a0, a1, c1]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [if_pos (show 1 ≤ k + 2 by omega), if_pos (show 2 ≤ k + 2 by omega),
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    exact b_all k

theorem step2 :
    ((1 - X ^ 2 - X ^ 4) ^ 2 : ℤ⟦X⟧) * PowerSeries.mk c = X + X ^ 2 + 2 * X ^ 3 + X ^ 6 := by
  rw [show ((1 - X ^ 2 - X ^ 4) ^ 2 : ℤ⟦X⟧) * PowerSeries.mk c
      = PowerSeries.mk c - (PowerSeries.mk c * X ^ 2 + PowerSeries.mk c * X ^ 2)
        - PowerSeries.mk c * X ^ 4 + (PowerSeries.mk c * X ^ 6 + PowerSeries.mk c * X ^ 6)
        + PowerSeries.mk c * X ^ 8 by ring,
    show (X + X ^ 2 + 2 * X ^ 3 + X ^ 6 : ℤ⟦X⟧) = X ^ 1 + X ^ 2 + (X ^ 3 + X ^ 3) + X ^ 6 by
      ring]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n <;> norm_num [c0, c1, c2, c3, c4, c5, c6, c7]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    simp only [if_pos (show 2 ≤ k + 8 by omega), if_pos (show 4 ≤ k + 8 by omega),
      if_pos (show 6 ≤ k + 8 by omega), if_pos (show 8 ≤ k + 8 by omega),
      if_neg (show ¬ (k + 8 = 1) by omega), if_neg (show ¬ (k + 8 = 2) by omega),
      if_neg (show ¬ (k + 8 = 3) by omega), if_neg (show ¬ (k + 8 = 6) by omega),
      show k + 8 - 2 = k + 6 by omega, show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 6 = k + 2 by omega, show k + 8 - 8 = k by omega]
    linarith [c_rec k]

end R023864

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a023864.main := by
  open OMA.S_oeis_a023864 R023864 in
  rw [mul_comm (1 - X - X ^ 2 : ℤ⟦X⟧), mul_assoc, step1, step2]
