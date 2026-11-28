import OMAStatements.S_oeis_a124869
import Mathlib
open OMA.S_oeis_a124869
namespace A124869P

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (-(P n).1 + 3 * (P n).2, -3 * (P n).1 - (P n).2)

def u : ℕ → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => 13
  | 4 => 7
  | 5 => -79
  | 6 => 11
  | 7 => 307
  | n + 8 => 14 * u (n + 4) - 625 * u n

def e (n : ℕ) : ℕ := 2 * (n / 4) + (if n % 4 = 2 then 3 else if n % 4 = 3 then 1 else 0)

lemma base_pow (n : ℕ) : base ^ n = ⟨((P n).1 : ℚ) / 10 ^ n, ((P n).2 : ℚ) / 10 ^ n⟩ := by
  induction n with
  | zero => rw [pow_zero]; ext <;> simp [P] <;> rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    · simp only [QuadraticAlgebra.re_mul, base, P]; push_cast; field_simp; ring
    · simp only [QuadraticAlgebra.im_mul, base, P]; push_cast; field_simp; ring

lemma P_rec (n : ℕ) : (P (n + 8)).1 = 56 * (P (n + 4)).1 - 10000 * (P n).1 := by
  simp only [P]; ring

lemma e_add (n : ℕ) : e (n + 8) = e n + 4 ∧ e (n + 4) = e n + 2 := by
  unfold e
  have h1 : (n + 8) / 4 = n / 4 + 2 := by omega
  have h2 : (n + 4) / 4 = n / 4 + 1 := by omega
  have h3 : (n + 8) % 4 = n % 4 := by omega
  have h4 : (n + 4) % 4 = n % 4 := by omega
  rw [h1, h2, h3, h4]; constructor <;> split_ifs <;> omega

lemma closed (n : ℕ) : (P n).1 = 2 ^ e n * u n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | m + 8 =>
      rw [P_rec, ih (m + 4) (by omega), ih m (by omega), (e_add m).1, (e_add m).2]
      simp only [u, pow_add]; ring

lemma u_mod (n : ℕ) : u n % 10 = 1 ∨ u n % 10 = 3 ∨ u n % 10 = 7 ∨ u n % 10 = 9 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | m + 8 =>
      have h1 := ih (m + 4) (by omega)
      have h2 := ih m (by omega)
      simp only [u]; omega

lemma a_eq (n : ℕ) (hn : n ≠ 2) : a n = u n := by
  have hle : e n ≤ n := by unfold e; split_ifs <;> omega
  have hq : (base ^ n).re = (u n : ℚ) / ((2 ^ (n - e n) * 5 ^ n : ℤ) : ℚ) := by
    rw [base_pow, closed]
    push_cast
    have : (10 : ℚ) ^ n = 2 ^ e n * (2 ^ (n - e n) * 5 ^ n) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, ← mul_pow]; norm_num
    rw [this]; field_simp
  unfold a; rw [hq]
  apply Rat.num_div_eq_of_coprime (by positivity)
  have hc : IsCoprime (u n) (2 ^ (n - e n) * 5 ^ n) := by
    have hm := u_mod n
    apply IsCoprime.mul_right <;> apply IsCoprime.pow_right
    · exact ⟨1, -(u n / 2), by omega⟩
    · rcases (show u n % 5 = 1 ∨ u n % 5 = 2 ∨ u n % 5 = 3 ∨ u n % 5 = 4 by omega)
        with h | h | h | h
      · exact ⟨1, -(u n / 5), by omega⟩
      · exact ⟨3, -(3 * (u n / 5) + 1), by omega⟩
      · exact ⟨2, -(2 * (u n / 5) + 1), by omega⟩
      · exact ⟨4, -(4 * (u n / 5) + 3), by omega⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp hc

lemma a_two : a 2 = -2 := by
  unfold a; rw [base_pow]
  have : ((P 2).1 : ℚ) / 10 ^ 2 = ((-2 : ℤ) : ℚ) / ((25 : ℤ) : ℚ) := by
    simp [P]; norm_num
  rw [this]; exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

end A124869P

open A124869P in
theorem OMA.solution : type_of% @OMA.S_oeis_a124869.main := by
  have hrec : ∀ n : ℕ, 10 < n → a n = 14 * a (n - 4) - 625 * a (n - 8) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega)]
    rw [show m + 11 = (m + 3) + 8 by omega, show m + 3 + 8 - 4 = m + 3 + 4 by omega,
      show m + 3 + 8 - 8 = m + 3 by omega]
    simp only [u]
  refine ⟨hrec, ?_⟩
  have hp : ((1 - PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C 25 * PowerSeries.X ^ 4) *
      (1 + PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C 25 * PowerSeries.X ^ 4) :
        PowerSeries ℚ) = 1 - PowerSeries.C 14 * PowerSeries.X ^ 4 +
          PowerSeries.C 625 * PowerSeries.X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [hp]
  ext n
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', series, PowerSeries.coeff_mk, PowerSeries.coeff_one,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hn : 10 < n
  · have h := hrec n hn
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
      show n ≠ 10 by omega, if_false]
    rw [h]; push_cast; ring
  · interval_cases n <;> simp [a_two, a_eq, u] <;> norm_num
