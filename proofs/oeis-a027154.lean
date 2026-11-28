import OMAStatements.S_oeis_a027154
import Mathlib

/-!
# Proof of OEIS A027154

We prove both conjectures of Chai Wah Wu for `A027154`, defined as the rising diagonal sums
`a n = ∑ k ∈ Finset.range (n / 2 + 1), T (n - k) k` of Kimberling's triangle `A027144`:

1. `∀ n : ℕ, 6 ≤ n → a n = 2 * a (n - 2) + 3 * a (n - 4) + 4 * a (n - 6)`.
2. `PowerSeries.mk (fun n => (a n : ℤ)) * (4 * X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 - 1) = -((X ^ 2 + 1) * (2 * X ^ 3 + X + 1))`.

## Strategy
- Establish unified recurrences for `T n k` valid for all `n ≥ 2` and `1 ≤ k ≤ n`, absorbing
  the `k = n` boundary cases via `T (n - 1) n = 0`.
- Split `a s` into its even-column sum `E s` and odd-column sum `O s`.
- Derive three coupled linear recurrences:
  - `E s = E (s - 1) + O (s - 2)` for `s ≥ 3`,
  - `O s = E (s - 3) + E (s - 2) + O (s - 1)` for odd `s ≥ 5`,
  - `O s = E (s - 1) + E (s - 2) + O (s - 1)` for even `s ≥ 4`.
- Eliminate `E` and `O` by linear arithmetic to obtain the order-6 recurrence for `n ≥ 12`,
  and check `6 ≤ n < 12` from small values `E 0..4`, `O 0..4` and the coupled recurrences.
- Deduce the generating function identity coefficient by coefficient.
-/

namespace OMA.Proof_oeis_a027154

open OMA.S_oeis_a027154
open PowerSeries

private lemma T_zero_right (n : ℕ) : T n 0 = 1 := by
  unfold T
  simp

private lemma T_eq_zero_of_lt {n k : ℕ} (h : n < k) : T n k = 0 := by
  unfold T
  have hk : k ≠ 0 := by omega
  simp [hk, h]

private lemma T_rec_even {n k : ℕ} (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hke : k % 2 = 0) :
    T n k = T (n - 1) (k - 1) + T (n - 1) k := by
  conv_lhs => unfold T
  have hk0 : k ≠ 0 := by omega
  have hlt : ¬ n < k := by omega
  have hn1 : n ≠ 1 := by omega
  have hko : k % 2 ≠ 1 := by omega
  simp only [hk0, hlt, hn1, hko, ↓reduceIte]
  by_cases hne : n % 2 = 0
  · simp only [hne, ↓reduceIte]
    by_cases hkeq : k = n
    · subst hkeq
      simp only [↓reduceIte]
      rw [T_eq_zero_of_lt (by omega : k - 1 < k), add_zero]
    · simp [hkeq]
  · simp only [hne, ↓reduceIte]
    have hkeq : k ≠ n := by omega
    simp [hkeq]

private lemma T_rec_odd_even {n k : ℕ} (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hko : k % 2 = 1) (hne : n % 2 = 0) :
    T n k = T (n - 2) (k - 1) + T (n - 1) (k - 1) + T (n - 1) k := by
  conv_lhs => unfold T
  have hk0 : k ≠ 0 := by omega
  have hlt : ¬ n < k := by omega
  have hn1 : n ≠ 1 := by omega
  have hkeq : k ≠ n := by omega
  simp [hk0, hlt, hn1, hne, hkeq, hko]

private lemma T_rec_odd_odd {n k : ℕ} (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hko : k % 2 = 1) (hno : n % 2 = 1) :
    T n k = T n (k - 1) + T (n - 1) (k - 1) + T (n - 1) k := by
  conv_lhs => unfold T
  have hk0 : k ≠ 0 := by omega
  have hlt : ¬ n < k := by omega
  have hn1 : n ≠ 1 := by omega
  have hne : n % 2 ≠ 0 := by omega
  simp only [hk0, hlt, hn1, hne, ↓reduceIte]
  by_cases hkeq : k = n
  · subst hkeq
    simp only [↓reduceIte]
    rw [T_eq_zero_of_lt (by omega : k - 1 < k), add_zero, add_comm]
  · simp [hkeq, hko]

private def E (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (s + 1), T (s - 2 * j) (2 * j)

private def O (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (s + 1), T (s - (2 * j + 1)) (2 * j + 1)

private lemma E_eq_sum {s N : ℕ} (hN : s + 1 ≤ N) :
    E s = ∑ j ∈ Finset.range N, T (s - 2 * j) (2 * j) := by
  unfold E
  apply Finset.sum_subset (Finset.range_mono hN)
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  exact T_eq_zero_of_lt (by omega)

private lemma O_eq_sum {s N : ℕ} (hN : s + 1 ≤ N) :
    O s = ∑ j ∈ Finset.range N, T (s - (2 * j + 1)) (2 * j + 1) := by
  unfold O
  apply Finset.sum_subset (Finset.range_mono hN)
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  exact T_eq_zero_of_lt (by omega)

private lemma sum_range_two_mul (f : ℕ → ℕ) :
    ∀ m, ∑ k ∈ Finset.range (2 * m), f k =
      (∑ j ∈ Finset.range m, f (2 * j)) + ∑ j ∈ Finset.range m, f (2 * j + 1)
  | 0 => by simp
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, sum_range_two_mul f m]
    omega

private lemma a_eq_E_add_O (s : ℕ) : a s = E s + O s := by
  have h1 : a s = ∑ k ∈ Finset.range (2 * (s + 1)), T (s - k) k := by
    unfold a
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    exact T_eq_zero_of_lt (by omega)
  rw [h1, sum_range_two_mul]
  rfl

private lemma E_rec {s : ℕ} (hs : 3 ≤ s) : E s = E (s - 1) + O (s - 2) := by
  rw [E_eq_sum (s := s - 1) (N := s + 1) (by omega),
    O_eq_sum (s := s - 2) (N := s) (by omega)]
  unfold E
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [mul_zero, Nat.sub_zero, T_zero_right]
  have hsum :
      ∑ j ∈ Finset.range s, T (s - 2 * (j + 1)) (2 * (j + 1)) =
        (∑ j ∈ Finset.range s, T (s - 1 - 2 * (j + 1)) (2 * (j + 1))) +
          ∑ j ∈ Finset.range s, T (s - 2 - (2 * j + 1)) (2 * j + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : 2 * (j + 1) ≤ s - 2 * (j + 1)
    · have hrec := T_rec_even (n := s - 2 * (j + 1)) (k := 2 * (j + 1))
        (by omega) (by omega) h (by omega)
      rw [hrec, add_comm]
      exact congrArg₂ (· + ·) (congrArg₂ T (by omega) (by omega))
        (congrArg₂ T (by omega) (by omega))
    · rw [T_eq_zero_of_lt (by omega), T_eq_zero_of_lt (by omega), T_eq_zero_of_lt (by omega)]
  omega

private lemma O_rec_odd {s : ℕ} (hs : 5 ≤ s) (hso : s % 2 = 1) :
    O s = E (s - 3) + E (s - 2) + O (s - 1) := by
  rw [E_eq_sum (s := s - 3) (N := s + 1) (by omega),
    E_eq_sum (s := s - 2) (N := s + 1) (by omega),
    O_eq_sum (s := s - 1) (N := s + 1) (by omega)]
  unfold O
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 2 * j + 1 ≤ s - (2 * j + 1)
  · have hrec := T_rec_odd_even (n := s - (2 * j + 1)) (k := 2 * j + 1)
      (by omega) (by omega) h (by omega) (by omega)
    rw [hrec]
    exact congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (congrArg₂ T (by omega) (by omega))
        (congrArg₂ T (by omega) (by omega)))
      (congrArg₂ T (by omega) (by omega))
  · rw [T_eq_zero_of_lt (by omega), T_eq_zero_of_lt (by omega),
      T_eq_zero_of_lt (by omega), T_eq_zero_of_lt (by omega)]

private lemma O_rec_even {s : ℕ} (hs : 4 ≤ s) (hse : s % 2 = 0) :
    O s = E (s - 1) + E (s - 2) + O (s - 1) := by
  rw [E_eq_sum (s := s - 1) (N := s + 1) (by omega),
    E_eq_sum (s := s - 2) (N := s + 1) (by omega),
    O_eq_sum (s := s - 1) (N := s + 1) (by omega)]
  unfold O
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 2 * j + 1 ≤ s - (2 * j + 1)
  · have hrec := T_rec_odd_odd (n := s - (2 * j + 1)) (k := 2 * j + 1)
      (by omega) (by omega) h (by omega) (by omega)
    rw [hrec]
    exact congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (congrArg₂ T (by omega) (by omega))
        (congrArg₂ T (by omega) (by omega)))
      (congrArg₂ T (by omega) (by omega))
  · rw [T_eq_zero_of_lt (by omega), T_eq_zero_of_lt (by omega),
      T_eq_zero_of_lt (by omega), T_eq_zero_of_lt (by omega)]

private lemma a_rec_ge12 {n : ℕ} (hn : 12 ≤ n) :
    a n = 2 * a (n - 2) + 3 * a (n - 4) + 4 * a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  rw [show m + 12 - 2 = m + 10 by omega, show m + 12 - 4 = m + 8 by omega,
    show m + 12 - 6 = m + 6 by omega]
  rw [a_eq_E_add_O, a_eq_E_add_O, a_eq_E_add_O, a_eq_E_add_O]
  have e12 := E_rec (s := m + 12) (by omega)
  have e11 := E_rec (s := m + 11) (by omega)
  have e10 := E_rec (s := m + 10) (by omega)
  have e9 := E_rec (s := m + 9) (by omega)
  have e8 := E_rec (s := m + 8) (by omega)
  have e7 := E_rec (s := m + 7) (by omega)
  have e6 := E_rec (s := m + 6) (by omega)
  simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
    show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega,
    show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
    show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
    show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega] at e12 e11 e10 e9 e8 e7 e6
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have o12 := O_rec_even (s := k + k + 12) (by omega) (by omega)
    have o11 := O_rec_odd (s := k + k + 11) (by omega) (by omega)
    have o9 := O_rec_odd (s := k + k + 9) (by omega) (by omega)
    have o7 := O_rec_odd (s := k + k + 7) (by omega) (by omega)
    have o6 := O_rec_even (s := k + k + 6) (by omega) (by omega)
    simp only [show k + k + 12 - 1 = k + k + 11 by omega, show k + k + 12 - 2 = k + k + 10 by omega,
      show k + k + 11 - 1 = k + k + 10 by omega, show k + k + 11 - 2 = k + k + 9 by omega,
      show k + k + 11 - 3 = k + k + 8 by omega,
      show k + k + 9 - 1 = k + k + 8 by omega, show k + k + 9 - 2 = k + k + 7 by omega,
      show k + k + 9 - 3 = k + k + 6 by omega,
      show k + k + 7 - 1 = k + k + 6 by omega, show k + k + 7 - 2 = k + k + 5 by omega,
      show k + k + 7 - 3 = k + k + 4 by omega,
      show k + k + 6 - 1 = k + k + 5 by omega, show k + k + 6 - 2 = k + k + 4 by omega]
      at o12 o11 o9 o7 o6
    zify at e12 e11 e10 e9 e7 o12 o11 o9 o7 o6 ⊢
    linear_combination e12 + 2 * e11 + e10 + 2 * e9 + 2 * e7 +
      o12 + o11 + 2 * o9 + 2 * o7 - 2 * o6
  · have o12 := O_rec_odd (s := 2 * k + 1 + 12) (by omega) (by omega)
    have o11 := O_rec_even (s := 2 * k + 1 + 11) (by omega) (by omega)
    have o9 := O_rec_even (s := 2 * k + 1 + 9) (by omega) (by omega)
    have o8 := O_rec_odd (s := 2 * k + 1 + 8) (by omega) (by omega)
    have o7 := O_rec_even (s := 2 * k + 1 + 7) (by omega) (by omega)
    have o6 := O_rec_odd (s := 2 * k + 1 + 6) (by omega) (by omega)
    have o5 := O_rec_even (s := 2 * k + 1 + 5) (by omega) (by omega)
    simp only [show 2 * k + 1 + 12 - 1 = 2 * k + 1 + 11 by omega,
      show 2 * k + 1 + 12 - 2 = 2 * k + 1 + 10 by omega,
      show 2 * k + 1 + 12 - 3 = 2 * k + 1 + 9 by omega,
      show 2 * k + 1 + 11 - 1 = 2 * k + 1 + 10 by omega,
      show 2 * k + 1 + 11 - 2 = 2 * k + 1 + 9 by omega,
      show 2 * k + 1 + 9 - 1 = 2 * k + 1 + 8 by omega,
      show 2 * k + 1 + 9 - 2 = 2 * k + 1 + 7 by omega,
      show 2 * k + 1 + 8 - 1 = 2 * k + 1 + 7 by omega,
      show 2 * k + 1 + 8 - 2 = 2 * k + 1 + 6 by omega,
      show 2 * k + 1 + 8 - 3 = 2 * k + 1 + 5 by omega,
      show 2 * k + 1 + 7 - 1 = 2 * k + 1 + 6 by omega,
      show 2 * k + 1 + 7 - 2 = 2 * k + 1 + 5 by omega,
      show 2 * k + 1 + 6 - 1 = 2 * k + 1 + 5 by omega,
      show 2 * k + 1 + 6 - 2 = 2 * k + 1 + 4 by omega,
      show 2 * k + 1 + 6 - 3 = 2 * k + 1 + 3 by omega,
      show 2 * k + 1 + 5 - 1 = 2 * k + 1 + 4 by omega,
      show 2 * k + 1 + 5 - 2 = 2 * k + 1 + 3 by omega] at o12 o11 o9 o8 o7 o6 o5
    zify at e12 e11 e10 e9 e8 e7 e6 o12 o11 o9 o8 o7 o6 o5 ⊢
    linear_combination e12 + e11 + e10 + 3 * e9 + e8 + 2 * e7 - e6 +
      o12 + o11 + o9 - o8 + 2 * o7 - o6 + o5

private lemma small_values :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 5 ∧ a 4 = 9 ∧ a 5 = 15 ∧
    a 6 = 31 ∧ a 7 = 49 ∧ a 8 = 101 ∧ a 9 = 163 ∧ a 10 = 331 ∧ a 11 = 533 := by
  have hT11 : T 1 1 = 2 := by unfold T; simp
  have hT21 : T 2 1 = 4 := by
    conv_lhs => unfold T
    simp [T_zero_right, hT11]
  have hT22 : T 2 2 = 2 := by
    conv_lhs => unfold T
    simp [hT11]
  have hT31 : T 3 1 = 6 := by
    conv_lhs => unfold T
    simp [T_zero_right, hT21]
  have hE0 : E 0 = 1 := by simp [E, T_zero_right]
  have hE1 : E 1 = 1 := by
    simp [E, Finset.sum_range_succ, T_zero_right, T_eq_zero_of_lt]
  have hE2 : E 2 = 1 := by
    simp [E, Finset.sum_range_succ, T_zero_right, T_eq_zero_of_lt]
  have hE3 : E 3 = 1 := by
    simp [E, Finset.sum_range_succ, T_zero_right, T_eq_zero_of_lt]
  have hE4 : E 4 = 3 := by
    simp [E, Finset.sum_range_succ, T_zero_right, T_eq_zero_of_lt, hT22]
  have hO0 : O 0 = 0 := by simp [O, T_eq_zero_of_lt]
  have hO1 : O 1 = 0 := by simp [O, T_eq_zero_of_lt]
  have hO2 : O 2 = 2 := by
    simp [O, Finset.sum_range_succ, T_eq_zero_of_lt, hT11]
  have hO3 : O 3 = 4 := by
    simp [O, Finset.sum_range_succ, T_eq_zero_of_lt, hT21]
  have hO4 : O 4 = 6 := by
    simp [O, Finset.sum_range_succ, T_eq_zero_of_lt, hT31]
  have hE5 : E 5 = E 4 + O 3 := E_rec (by omega)
  have hO5 : O 5 = E 2 + E 3 + O 4 := O_rec_odd (by omega) (by omega)
  have hE6 : E 6 = E 5 + O 4 := E_rec (by omega)
  have hO6 : O 6 = E 5 + E 4 + O 5 := O_rec_even (by omega) (by omega)
  have hE7 : E 7 = E 6 + O 5 := E_rec (by omega)
  have hO7 : O 7 = E 4 + E 5 + O 6 := O_rec_odd (by omega) (by omega)
  have hE8 : E 8 = E 7 + O 6 := E_rec (by omega)
  have hO8 : O 8 = E 7 + E 6 + O 7 := O_rec_even (by omega) (by omega)
  have hE9 : E 9 = E 8 + O 7 := E_rec (by omega)
  have hO9 : O 9 = E 6 + E 7 + O 8 := O_rec_odd (by omega) (by omega)
  have hE10 : E 10 = E 9 + O 8 := E_rec (by omega)
  have hO10 : O 10 = E 9 + E 8 + O 9 := O_rec_even (by omega) (by omega)
  have hE11 : E 11 = E 10 + O 9 := E_rec (by omega)
  have hO11 : O 11 = E 8 + E 9 + O 10 := O_rec_odd (by omega) (by omega)
  have ha0 := a_eq_E_add_O 0
  have ha1 := a_eq_E_add_O 1
  have ha2 := a_eq_E_add_O 2
  have ha3 := a_eq_E_add_O 3
  have ha4 := a_eq_E_add_O 4
  have ha5 := a_eq_E_add_O 5
  have ha6 := a_eq_E_add_O 6
  have ha7 := a_eq_E_add_O 7
  have ha8 := a_eq_E_add_O 8
  have ha9 := a_eq_E_add_O 9
  have ha10 := a_eq_E_add_O 10
  have ha11 := a_eq_E_add_O 11
  omega

private lemma a_rec (n : ℕ) (hn : 6 ≤ n) :
    a n = 2 * a (n - 2) + 3 * a (n - 4) + 4 * a (n - 6) := by
  rcases Nat.lt_or_ge n 12 with hlt | hge
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := small_values
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · exact a_rec_ge12 hge

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) * (4 * X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 - 1)
      = -((X ^ 2 + 1) * (2 * X ^ 3 + X + 1)) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have e1 : A * (4 * X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 - 1) =
      C 4 * (A * X ^ 6) + C 3 * (A * X ^ 4) + C 2 * (A * X ^ 2) - A := by
    simp only [map_ofNat]
    ring
  have e2 : -(((X : ℤ⟦X⟧) ^ 2 + 1) * (2 * X ^ 3 + X + 1)) =
      -(C 2 * X ^ 5 + C 3 * X ^ 3 + X ^ 2 + X ^ 1 + C 1) := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (a k : ℤ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', hc, coeff_C]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · obtain ⟨h0, h1, h2, h3, h4, h5, _⟩ := small_values
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5]
  · have hrec : (a n : ℤ) = 2 * a (n - 2) + 3 * a (n - 4) + 4 * a (n - 6) := by
      exact_mod_cast a_rec n hn
    simp only [show 6 ≤ n by omega, show 4 ≤ n by omega, show 2 ≤ n by omega,
      show n ≠ 2 by omega, show n ≠ 1 by omega, show n ≠ 0 by omega, if_true, if_false]
    omega

end OMA.Proof_oeis_a027154

theorem OMA.solution : type_of% @OMA.S_oeis_a027154.main :=
  ⟨OMA.Proof_oeis_a027154.a_rec, OMA.Proof_oeis_a027154.gf_eq⟩
