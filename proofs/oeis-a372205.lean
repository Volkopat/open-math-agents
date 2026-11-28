import OMAStatements.S_oeis_a372205
import Mathlib

namespace OMA.P_oeis_a372205

open OMA.S_oeis_a372205

private lemma padicValNat_two_mul_odd (r k : ℕ) :
    padicValNat 2 (2 ^ r * (2 * k + 1)) = r := by
  have hodd : ¬(2 ∣ (2 * k + 1)) := by omega
  have hval_odd : padicValNat 2 (2 * k + 1) = 0 := padicValNat.eq_zero_of_not_dvd hodd
  have hne1 : 2 ^ r ≠ 0 := by positivity
  have hne2 : 2 * k + 1 ≠ 0 := by omega
  rw [padicValNat.mul hne1 hne2, padicValNat.prime_pow, hval_odd, add_zero]

private lemma a372205_pow2_odd (r : ℕ) :
    ∀ k : ℕ, a372205 (2 ^ r * (2 * k + 1)) =
      ((r : ℤ) - 1) * a372205 (2 ^ r * k) + a372205 (2 ^ (r + 1) * k) := by
  induction r with
  | zero =>
    intro k
    have hpos : 2 ^ 0 * (2 * k + 1) = (2 * k) + 1 := by simp
    rw [hpos, a372205]
    have hv : padicValNat 2 (2 * k + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    have h1 : (2 * k + 1 - 1) / 2 = k := by omega
    have h2 : (2 * (2 * k + 1) - 1) / 2 = 2 * k := by omega
    have hneg : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    simp only [hv, pow_zero, one_mul, Nat.cast_zero]
    rw [h1, h2, hneg]
    ring
  | succ r ih =>
    intro k
    have hm_pos : 1 ≤ 2 ^ (r + 1) * (2 * k + 1) := by
      have : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
      nlinarith
    obtain ⟨m', hm'⟩ : ∃ m', 2 ^ (r + 1) * (2 * k + 1) = m' + 1 :=
      ⟨2 ^ (r + 1) * (2 * k + 1) - 1, by omega⟩
    rw [hm', a372205, ← hm', padicValNat_two_mul_odd (r + 1) k]
    have h1 : (2 ^ (r + 1) * (2 * k + 1) - 2 ^ (r + 1)) / 2 = 2 ^ (r + 1) * k := by
      have : 2 ^ (r + 1) * (2 * k + 1) - 2 ^ (r + 1) = 2 * (2 ^ (r + 1) * k) := by
        rw [Nat.mul_add, mul_one, Nat.add_sub_cancel]; ring
      rw [this, Nat.mul_div_right _ (by omega : 0 < 2)]
    have h2 : (2 * (2 ^ (r + 1) * (2 * k + 1)) - 2 ^ (r + 1)) / 2 = 2 ^ r * (2 * (2 * k) + 1) := by
      have : 2 * (2 ^ (r + 1) * (2 * k + 1)) - 2 ^ (r + 1) = 2 * (2 ^ r * (2 * (2 * k) + 1)) := by
        apply Nat.sub_eq_of_eq_add
        rw [pow_succ']; ring
      rw [this, Nat.mul_div_right _ (by omega : 0 < 2)]
    have hev : (-1 : ℤ) ^ (2 ^ (r + 1) * (2 * k + 1)) = 1 := by
      have h2m : 2 ^ (r + 1) * (2 * k + 1) = 2 * (2 ^ r * (2 * k + 1)) := by
        rw [pow_succ']; ring
      rw [h2m, pow_mul]; norm_num
    rw [h1, h2, hev, one_mul, ih (2 * k)]
    have h3 : 2 ^ r * (2 * k) = 2 ^ (r + 1) * k := by rw [pow_succ']; ring
    have h4 : 2 ^ (r + 1) * (2 * k) = 2 ^ (r + 2) * k := by rw [pow_succ' 2 (r + 1)]; ring
    rw [h3, h4]
    push_cast
    ring

private def U (n r : ℕ) : ℤ :=
  a372205 (2 ^ r * (2 ^ n - 1))

private lemma U_zero (r : ℕ) : U 0 r = 1 := by
  simp [U, a372205]

private lemma U_succ (n r : ℕ) :
    U (n + 1) r = U n (r + 1) + ((r : ℤ) - 1) * U n r := by
  simp only [U]
  have h2n : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ']; omega
  rw [h2n, a372205_pow2_odd]
  ring

private lemma deriv_expSeries : PowerSeries.derivative ℚ expSeries = expSeries := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp only [expSeries, PowerSeries.coeff_mk, Nat.factorial_succ, Nat.cast_mul, mul_inv]
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp [hn1]

private lemma expSeries_coeff_zero : PowerSeries.coeff 0 expSeries = 1 := by
  simp [expSeries]

private theorem main_proved :
    ∀ B : PowerSeries ℚ,
      PowerSeries.coeff 0 B = 1 →
      PowerSeries.derivative ℚ B = (expSeries - 1) * B →
      ∀ n : ℕ,
        ((n.factorial : ℚ) * PowerSeries.coeff n B) = (a372205 (2 ^ n - 1) : ℚ) := by
  intro B hB0 hBd
  have hGr : ∀ n r : ℕ,
      ((n.factorial : ℚ) * PowerSeries.coeff n (expSeries ^ r * B)) = (U n r : ℚ) := by
    intro n
    induction n with
    | zero =>
      intro r
      rw [U_zero, Nat.factorial_zero, Nat.cast_one, one_mul, Int.cast_one]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff, expSeries_coeff_zero, hB0, one_pow, one_mul]
    | succ n ih =>
      intro r
      have hd : PowerSeries.derivative ℚ (expSeries ^ r * B) =
          (expSeries ^ (r + 1) * B) + PowerSeries.C ((r : ℚ) - 1) * (expSeries ^ r * B) := by
        rw [Derivation.leibniz, PowerSeries.derivative_pow, deriv_expSeries, hBd, smul_eq_mul, smul_eq_mul]
        have hpow : (r : PowerSeries ℚ) * expSeries ^ (r - 1) * expSeries = (r : PowerSeries ℚ) * expSeries ^ r := by
          cases r with
          | zero => simp
          | succ r => rw [mul_assoc, ← pow_succ, Nat.add_sub_cancel]
        rw [map_sub, map_natCast, map_one]
        calc expSeries ^ r * ((expSeries - 1) * B) + B * ((r : PowerSeries ℚ) * expSeries ^ (r - 1) * expSeries)
            = expSeries ^ r * ((expSeries - 1) * B) + B * ((r : PowerSeries ℚ) * expSeries ^ r) := by rw [hpow]
          _ = (expSeries ^ r * expSeries * B) + ((r : PowerSeries ℚ) - 1) * (expSeries ^ r * B) := by ring
          _ = (expSeries ^ (r + 1) * B) + ((r : PowerSeries ℚ) - 1) * (expSeries ^ r * B) := by rw [pow_succ]
      have hc := congr_arg (PowerSeries.coeff n) hd
      rw [PowerSeries.coeff_derivative, map_add, PowerSeries.coeff_C_mul] at hc
      have hmul : ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) (expSeries ^ r * B) =
          (n.factorial : ℚ) * (PowerSeries.coeff (n + 1) (expSeries ^ r * B) * ((n : ℚ) + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
      rw [hmul, hc, mul_add, ih (r + 1), ← mul_assoc, mul_comm (n.factorial : ℚ) ((r : ℚ) - 1), mul_assoc, ih r]
      rw [U_succ]
      push_cast
      ring
  intro n
  simpa [U] using hGr n 0

end OMA.P_oeis_a372205

theorem OMA.solution : type_of% @OMA.S_oeis_a372205.main :=
  OMA.P_oeis_a372205.main_proved
