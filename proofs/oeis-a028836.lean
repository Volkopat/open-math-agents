import OMAStatements.S_oeis_a028836
import Mathlib

-- Problem: A028836, iterated sum of digits of n is a power of 2.
-- Upstream: formal-conjectures statements/oeis-a028836.lean (declaration OMA.S_oeis_a028836.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: the iterated digit sum of n >= 1 is the digital root 1 + (n-1) mod 9, so the terms are
-- the numbers congruent to 1, 2, 4, 8 modulo 9, i.e. a(m+1) = 9 (m / 4) + [1, 2, 4, 8] (m mod 4);
-- then a(n+4) = a(n) + 9 gives the recurrence and the generating function.

namespace OMA.P_oeis_a028836

open OMA.S_oeis_a028836 PowerSeries

theorem digitSum_le (m : ℕ) : digitSum m ≤ m := Nat.digit_sum_le 10 m

theorem digitSum_lt (m : ℕ) (hm : 10 ≤ m) : digitSum m < m := by
  unfold digitSum
  rw [show m = m % 10 + 10 * (m / 10) from (Nat.mod_add_div m 10).symm,
    Nat.digits_add 10 (by norm_num) _ _ (Nat.mod_lt _ (by norm_num)) (Or.inr (by omega)),
    List.sum_cons]
  have := Nat.digit_sum_le 10 (m / 10)
  omega

theorem digitSum_small (m : ℕ) (hm : m < 10) : digitSum m = m := by
  unfold digitSum
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp
  · rw [Nat.digits_of_lt 10 m (by omega) hm]
    simp

theorem digitSum_pos (m : ℕ) (hm : 1 ≤ m) : 1 ≤ digitSum m := by
  unfold digitSum
  have hne : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have h1 := Nat.getLast_digit_ne_zero 10 (show m ≠ 0 by omega)
  have h2 := List.le_sum_of_mem (List.getLast_mem hne)
  omega

theorem digitSum_mod (m : ℕ) : digitSum m % 9 = m % 9 :=
  (Nat.modEq_nine_digits_sum m).symm

/-- The digital root of a positive number. -/
def dr (m : ℕ) : ℕ := 1 + (m - 1) % 9

theorem iterate_eq : ∀ k m : ℕ, 1 ≤ m → m ≤ k + 9 → digitSum^[k] m = dr m := by
  intro k
  induction k with
  | zero =>
    intro m h1 h2
    simp only [Function.iterate_zero, id_eq, dr]
    omega
  | succ k ih =>
    intro m h1 h2
    by_cases hm : m < 10
    · rw [Function.iterate_fixed (digitSum_small m hm)]
      unfold dr
      omega
    · rw [Function.iterate_succ_apply]
      have hlt := digitSum_lt m (by omega)
      have hpos := digitSum_pos m h1
      rw [ih (digitSum m) hpos (by omega)]
      unfold dr
      have := digitSum_mod m
      omega

theorem isTerm_iff (n : ℕ) : IsTerm n ↔ 0 < n ∧ (n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 4 ∨ n % 9 = 8) := by
  unfold IsTerm iteratedDigitSum
  constructor
  · rintro ⟨hn, k, hk⟩
    refine ⟨hn, ?_⟩
    rw [iterate_eq n n hn (by omega)] at hk
    unfold dr at hk
    have hk3 : k ≤ 3 := by
      by_contra hc
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> simp at hk <;> omega
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rw [iterate_eq n n hn (by omega)]
    unfold dr
    rcases h with h | h | h | h
    · exact ⟨0, by omega⟩
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨3, by omega⟩

/-- The residues modulo 9 in increasing order. -/
def B (r : ℕ) : ℕ := if r = 0 then 1 else if r = 1 then 2 else if r = 2 then 4 else 8

/-- The claimed enumeration (zero-based). -/
def f (m : ℕ) : ℕ := 9 * (m / 4) + B (m % 4)

theorem f_mono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro m
  unfold f B
  split_ifs <;> omega

theorem f_maps (m : ℕ) : IsTerm (f m) := by
  rw [isTerm_iff]
  unfold f B
  split_ifs <;> omega

theorem f_surj (k : ℕ) (hk : IsTerm k) : ∃ m, f m = k := by
  rw [isTerm_iff] at hk
  obtain ⟨_, h⟩ := hk
  rcases h with h | h | h | h
  · exact ⟨4 * (k / 9), by unfold f B; split_ifs <;> omega⟩
  · exact ⟨4 * (k / 9) + 1, by unfold f B; split_ifs <;> omega⟩
  · exact ⟨4 * (k / 9) + 2, by unfold f B; split_ifs <;> omega⟩
  · exact ⟨4 * (k / 9) + 3, by unfold f B; split_ifs <;> omega⟩

theorem nth_eq (m : ℕ) : Nat.nth IsTerm m = f m := by
  have hinf : (Set.ofPred IsTerm).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective f_maps
  have hU : ∀ k, k ∈ {k : ℕ | ∀ hf : (Set.ofPred IsTerm).Finite, k < hf.toFinset.card} :=
    fun k hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hU m)).symm
  · intro x hx
    obtain ⟨k, hk⟩ := f_surj x hx
    exact ⟨k, hU k, hk⟩
  · intro k _
    exact f_maps k
  · exact f_mono.strictMonoOn _

theorem a_succ (m : ℕ) : a (m + 1) = f m := by
  unfold a
  rw [if_neg (by omega), Nat.add_sub_cancel, nth_eq]

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = f (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ, Nat.add_sub_cancel]

theorem shift (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + 9 := by
  rw [a_eq _ (by omega), a_eq _ hn, show n + 4 - 1 = (n - 1) + 4 by omega]
  unfold f B
  split_ifs <;> omega

theorem part2 (n : ℕ) (hn : 5 < n) : (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [show k + 6 - 1 = (k + 1) + 4 by omega, show k + 6 - 4 = (k + 1) + 1 by omega,
    show k + 6 - 5 = k + 1 by omega, show k + 6 = (k + 2) + 4 by omega,
    shift (k + 2) (by omega), shift (k + 1) (by omega)]
  push_cast
  ring

theorem a_vals : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 4 ∧ a 4 = 8 ∧ a 5 = 10 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [a_succ]; rfl)

theorem part1 : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
      X * (1 + X + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4) := by
  have hden : ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) : PowerSeries ℤ) =
      1 - X ^ 1 - X ^ 4 + X ^ 5 := by
    ring
  have hnum : (X * (1 + X + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 + C (4 : ℤ) * X ^ 4 +
      C (1 : ℤ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hden, hnum]
  ext n
  rw [mul_add, mul_sub, mul_sub, mul_one, map_add, map_sub, map_sub, coeff_mul_X_pow',
    coeff_mul_X_pow', coeff_mul_X_pow']
  simp only [map_add, coeff_C_mul_X_pow, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := a_vals
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5]
  · simp only [show 1 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, ↓reduceIte]
    rw [part2 n (by omega)]
    ring

end OMA.P_oeis_a028836

theorem OMA.solution : type_of% @OMA.S_oeis_a028836.main :=
  ⟨OMA.P_oeis_a028836.part1, OMA.P_oeis_a028836.part2⟩
