import OMAStatements.S_oeis_a059133
import Mathlib

namespace OMA.P059133
open OMA.S_oeis_a059133

lemma W2c_eq (k : ℕ) : W2c k = 6 * padicValNat 2 k + 4 := by
  simp only [W2c, phrase, A001511, List.sum_cons, List.sum_nil]
  omega

lemma sum_odd_split (f : ℕ → ℕ) (N : ℕ) :
    ∑ i ∈ Finset.range (2 * N + 1), f i =
      ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) + f (2 * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    ring

lemma v_odd (j : ℕ) : padicValNat 2 (2 * j + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  omega

lemma v_even (j : ℕ) : padicValNat 2 (2 * j + 2) = padicValNat 2 (j + 1) + 1 := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, padicValNat.mul (by norm_num) (by omega)]
  simp
  ring

lemma V_eq (t : ℕ) :
    ∑ i ∈ Finset.range (2 ^ t - 1), padicValNat 2 (i + 1) + t + 1 = 2 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    have h2 : 2 ^ (t + 1) - 1 = 2 * (2 ^ t - 1) + 1 := by rw [pow_succ]; omega
    rw [h2, sum_odd_split (fun i => padicValNat 2 (i + 1))]
    have h3 : ∀ j, padicValNat 2 (2 * j + 1) + padicValNat 2 (2 * j + 1 + 1) =
        padicValNat 2 (j + 1) + 1 := by
      intro j
      rw [v_odd, show 2 * j + 1 + 1 = 2 * j + 2 by ring, v_even]
      ring
    simp only [h3]
    rw [v_odd, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rw [pow_succ]
    omega

lemma a_nat (n : ℕ) : a n + 6 * (n + 2) + 4 = 10 * 2 ^ (n + 1) := by
  have hV := V_eq (n + 1)
  have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have e : a n = 6 * ∑ i ∈ Finset.range (2 ^ (n + 1) - 1), padicValNat 2 (i + 1) +
      4 * (2 ^ (n + 1) - 1) := by
    simp only [a, S, W2c_eq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    ring
  omega

lemma a_int (n : ℕ) : (a n : ℤ) = 4 * (-4 + 5 * 2 ^ n) - 6 * n := by
  have h := a_nat n
  have h' : ((a n + 6 * (n + 2) + 4 : ℕ) : ℤ) = ((10 * 2 ^ (n + 1) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  rw [pow_succ] at h'
  linarith

lemma rec3 (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  rw [a_int, a_int, a_int, a_int]
  push_cast
  ring

lemma gf : ((PowerSeries.X - 1) ^ 2 * (2 * PowerSeries.X - 1) *
      PowerSeries.mk (fun n => (a n : ℤ)) : PowerSeries ℤ) = -2 * (PowerSeries.X + 2) := by
  have e1 : ((PowerSeries.X - 1) ^ 2 * (2 * PowerSeries.X - 1) *
      PowerSeries.mk (fun n => (a n : ℤ)) : PowerSeries ℤ) =
      PowerSeries.C 2 * (PowerSeries.X ^ 3 * PowerSeries.mk (fun n => (a n : ℤ))) -
        PowerSeries.C 5 * (PowerSeries.X ^ 2 * PowerSeries.mk (fun n => (a n : ℤ))) +
        PowerSeries.C 4 * (PowerSeries.X ^ 1 * PowerSeries.mk (fun n => (a n : ℤ))) -
        PowerSeries.mk (fun n => (a n : ℤ)) := by
    simp only [map_ofNat]
    ring
  have e2 : (-2 * (PowerSeries.X + 2) : PowerSeries ℤ) =
      -(PowerSeries.C 2 * PowerSeries.X ^ 1) - PowerSeries.C 4 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | n
  · simp [a_int]
  · simp [a_int]
  · simp [a_int]
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega)]
    rw [show n + 1 + 1 + 1 - 3 = n by omega, show n + 1 + 1 + 1 - 2 = n + 1 by omega,
      show n + 1 + 1 + 1 - 1 = n + 2 by omega]
    rw [a_int, a_int, a_int, a_int]
    push_cast
    ring

theorem sol : type_of% @OMA.S_oeis_a059133.main :=
  ⟨a_int, rec3, gf⟩

end OMA.P059133

theorem OMA.solution : type_of% @OMA.S_oeis_a059133.main := OMA.P059133.sol
