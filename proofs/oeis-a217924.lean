import OMAStatements.S_oeis_a217924
import Mathlib

namespace OMA.P_oeis_a217924

open OMA.S_oeis_a217924

private lemma padicValNat_two_mul_odd (r k : ℕ) :
    padicValNat 2 (2 ^ r * (2 * k + 1)) = r := by
  have hodd : ¬(2 ∣ (2 * k + 1)) := by omega
  have hval_odd : padicValNat 2 (2 * k + 1) = 0 := padicValNat.eq_zero_of_not_dvd hodd
  have hne1 : 2 ^ r ≠ 0 := by positivity
  have hne2 : 2 * k + 1 ≠ 0 := by omega
  rw [padicValNat.mul hne1 hne2, padicValNat.prime_pow, hval_odd, add_zero]

-- Key 5-line pointwise identity: c(2^r * (2k + 1)) = (r - 1) * c(2^r * k) + c(2^(r + 1) * k)!
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

private def S (n r : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (2 ^ n), a372205 (2 ^ r * m)

private lemma S_zero (r : ℕ) : S 0 r = 1 := by
  simp [S, a372205]

private lemma sum_range_two_mul (g : ℕ → ℤ) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), g m =
      (∑ k ∈ Finset.range N, g (2 * k)) + (∑ k ∈ Finset.range N, g (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

private lemma S_succ (n r : ℕ) :
    S (n + 1) r = 2 * S n (r + 1) + ((r : ℤ) - 1) * S n r := by
  simp only [S]
  have hsplit : ∑ m ∈ Finset.range (2 ^ (n + 1)), a372205 (2 ^ r * m) =
      (∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ r * (2 * k))) +
      (∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ r * (2 * k + 1))) := by
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ'], sum_range_two_mul]
  rw [hsplit]
  have hev : ∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ r * (2 * k)) =
      ∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ (r + 1) * k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; rw [pow_succ']; ring
  have hodd : ∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ r * (2 * k + 1)) =
      ((r : ℤ) - 1) * (∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ r * k)) +
      (∑ k ∈ Finset.range (2 ^ n), a372205 (2 ^ (r + 1) * k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => a372205_pow2_odd r k
  rw [hev, hodd]
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
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.derivative ℚ A = (2 * expSeries - 1) * A →
      ∀ n : ℕ,
        ((n.factorial : ℚ) * PowerSeries.coeff n A) =
          ((∑ k ∈ Finset.range (2 ^ n), a372205 k : ℤ) : ℚ) := by
  intro A hA0 hAd
  have hFr : ∀ n r : ℕ,
      ((n.factorial : ℚ) * PowerSeries.coeff n (expSeries ^ r * A)) = (S n r : ℚ) := by
    intro n
    induction n with
    | zero =>
      intro r
      rw [S_zero, Nat.factorial_zero, Nat.cast_one, one_mul, Int.cast_one]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff, expSeries_coeff_zero, hA0, one_pow, one_mul]
    | succ n ih =>
      intro r
      have hd : PowerSeries.derivative ℚ (expSeries ^ r * A) =
          PowerSeries.C (2 : ℚ) * (expSeries ^ (r + 1) * A) + PowerSeries.C ((r : ℚ) - 1) * (expSeries ^ r * A) := by
        rw [Derivation.leibniz, PowerSeries.derivative_pow, deriv_expSeries, hAd, smul_eq_mul, smul_eq_mul]
        have hpow : (r : PowerSeries ℚ) * expSeries ^ (r - 1) * expSeries = (r : PowerSeries ℚ) * expSeries ^ r := by
          cases r with
          | zero => simp
          | succ r => rw [mul_assoc, ← pow_succ, Nat.add_sub_cancel]
        rw [map_sub, map_natCast, map_one, show PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) from map_ofNat _ 2]
        calc expSeries ^ r * ((2 * expSeries - 1) * A) + A * ((r : PowerSeries ℚ) * expSeries ^ (r - 1) * expSeries)
            = expSeries ^ r * ((2 * expSeries - 1) * A) + A * ((r : PowerSeries ℚ) * expSeries ^ r) := by rw [hpow]
          _ = 2 * (expSeries ^ r * expSeries * A) + ((r : PowerSeries ℚ) - 1) * (expSeries ^ r * A) := by ring
          _ = 2 * (expSeries ^ (r + 1) * A) + ((r : PowerSeries ℚ) - 1) * (expSeries ^ r * A) := by rw [pow_succ]
      have hc := congr_arg (PowerSeries.coeff n) hd
      rw [PowerSeries.coeff_derivative, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hc
      have hmul : ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) (expSeries ^ r * A) =
          (n.factorial : ℚ) * (PowerSeries.coeff (n + 1) (expSeries ^ r * A) * ((n : ℚ) + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
      rw [hmul, hc, mul_add, ← mul_assoc, mul_comm (n.factorial : ℚ) 2, mul_assoc, ih (r + 1),
        ← mul_assoc, mul_comm (n.factorial : ℚ) ((r : ℚ) - 1), mul_assoc, ih r]
      rw [S_succ]
      push_cast
      ring
  intro n
  simpa [S] using hFr n 0

end OMA.P_oeis_a217924

theorem OMA.solution : type_of% @OMA.S_oeis_a217924.main :=
  OMA.P_oeis_a217924.main_proved
