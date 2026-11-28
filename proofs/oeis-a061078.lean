import OMAStatements.S_oeis_a061078
import Mathlib

/-!
# OEIS A061078 (conjecture of Luca Onnis)

With `r = min (a - 1) b` and `N = 5 ^ a * 2 ^ b * p`, the number `2 * N` is a positive
multiple of `10 ^ (r + 1)`, while `2 * t <= 2 * fives r = (10 ^ (r + 1) - 10) / 9` for
`t <= fives r`.  A number at least `10 ^ k` whose decimal digits are all nonzero has
`m % 10 ^ k >= (10 ^ k - 1) / 9`, so `2 * N + 2 * t` has a zero digit and its digit product
vanishes.  Hence all the terms of index `N - 1, ..., N + j - 1` of the sum are zero.
-/

namespace OMA.A061078

open OMA.S_oeis_a061078

/-- If all decimal digits of `m >= 10 ^ k` are nonzero, the low `k` digits are at least
the repunit. -/
theorem low_ge : ∀ (k m : ℕ), 10 ^ k ≤ m → 0 ∉ Nat.digits 10 m →
    10 ^ k ≤ 9 * (m % 10 ^ k) + 1 := by
  intro k
  induction k with
  | zero => intro m _ _; simp
  | succ k ih =>
    intro m hm h
    have hk : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hm10 : 10 ≤ m := by
      have : 10 ^ (k + 1) = 10 ^ k * 10 := pow_succ 10 k
      omega
    rw [Nat.digits_def' (by norm_num) (by omega)] at h
    simp only [List.mem_cons, not_or] at h
    obtain ⟨h0, h1⟩ := h
    have hd : 10 ^ k ≤ m / 10 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have : 10 ^ (k + 1) = 10 ^ k * 10 := pow_succ 10 k
      omega
    have := ih (m / 10) hd h1
    have e : 10 ^ (k + 1) = 10 * 10 ^ k := pow_succ' 10 k
    rw [e, Nat.mod_mul]
    omega

theorem fives_closed (r : ℕ) : 9 * fives r + 5 = 5 * 10 ^ r := by
  induction r with
  | zero => simp [fives]
  | succ r ih =>
    have : fives (r + 1) = 5 + 10 * fives r := by
      simp [fives, List.replicate_succ, Nat.ofDigits_cons]
    rw [this, pow_succ]
    omega

theorem term_zero (k q t : ℕ) (hq : 1 ≤ q) (ht : 18 * t + 10 ≤ 10 ^ k) :
    (Nat.digits 10 (10 ^ k * q + 2 * t)).prod = 0 := by
  by_contra h
  have h0 : 0 ∉ Nat.digits 10 (10 ^ k * q + 2 * t) := fun hmem => h (List.prod_eq_zero hmem)
  have hle : 10 ^ k ≤ 10 ^ k * q + 2 * t := by nlinarith
  have := low_ge k _ hle h0
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)] at this
  omega

end OMA.A061078

open OMA.S_oeis_a061078 OMA.A061078 in
theorem OMA.solution : type_of% @OMA.S_oeis_a061078.main := by
  intro a b p ha h2 h5 j hj
  have hp : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · exact absurd (h ▸ dvd_zero 2) h2
    · exact h
  generalize hr : min (a - 1) b = r at hj
  have hr1 : r + 1 ≤ a := by omega
  have hr2 : r + 1 ≤ b + 1 := by omega
  have hN : 1 ≤ 5 ^ a * 2 ^ b * p :=
    Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity)) hp
  generalize hNe : 5 ^ a * 2 ^ b * p = N at hN
  have hdvd : 10 ^ (r + 1) ∣ 2 * N := by
    have e : 2 * N = 5 ^ a * 2 ^ (b + 1) * p := by rw [← hNe]; ring
    have e10 : (10 : ℕ) ^ (r + 1) = 5 ^ (r + 1) * 2 ^ (r + 1) := by
      rw [← mul_pow]; norm_num
    rw [e, e10]
    exact Dvd.dvd.mul_right
      (mul_dvd_mul (pow_dvd_pow 5 hr1) (pow_dvd_pow 2 hr2)) p
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hq; omega
    · exact h
  have hf := fives_closed r
  have hpow : (10 : ℕ) ^ (r + 1) = 10 ^ r * 10 := pow_succ 10 r
  have hsplit : N + j = (N - 1) + (j + 1) := by omega
  unfold partialSum
  rw [hsplit, Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range (j + 1), (Nat.digits 10 (2 * (N - 1 + x + 1))).prod = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    have e : 2 * (N - 1 + x + 1) = 10 ^ (r + 1) * q + 2 * x := by omega
    rw [e]
    exact term_zero (r + 1) q x hq1 (by omega)
  rw [hz, add_zero]
