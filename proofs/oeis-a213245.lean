import OMAStatements.S_oeis_a213245
import Mathlib

/-!
Credit: @ivillar
Proof (the argument behind the OEIS formula a(n) = M/gcd(M,7), M = 2^n - 1, which Robert Israel
used to verify Barker's conjectures): the nonzero 7th powers of GF(2^n) are the image of the
7th-power map on the cyclic group of units, of order M, so there are M/gcd(M,7) of them; since
2^3 = 8 = 1 mod 7, gcd(M,7) is 7 when 3 divides n and 1 otherwise. The recurrence and the g.f.
follow by algebra.
-/

namespace OMAA213245Helpers
open PowerSeries OMA.S_oeis_a213245

theorem card_pow (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0) :
    Nat.card {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ d = x} =
      (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) d := by
  have hU : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn]
  rw [← hU, ← IsCyclic.card_powMonoidHom_range]
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨Units.mk0 x.1 x.2.1, by
      obtain ⟨y, hy⟩ := x.2.2
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact x.2.1 (by rw [← hy, zero_pow hd])
      exact MonoidHom.mem_range.mpr ⟨Units.mk0 y hy0, by ext; simp [hy]⟩⟩
    invFun := fun u => ⟨((u : (GaloisField 2 n)ˣ) : GaloisField 2 n), Units.ne_zero _, by
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp u.2
      refine ⟨(v : GaloisField 2 n), ?_⟩
      rw [← hv]
      simp⟩
    left_inv := fun x => Subtype.ext (by simp)
    right_inv := fun u => Subtype.ext (Units.ext (by simp)) }

theorem a_spec (n : ℕ) (hn : 1 ≤ n) :
    (n % 3 = 0 → 7 * (a n : ℤ) = 2 ^ n - 1) ∧ (n % 3 ≠ 0 → (a n : ℤ) = 2 ^ n - 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hM : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by push_cast [Nat.cast_sub h1]; ring
  have h8 : ∀ k : ℕ, 8 ^ k % 7 = 1 := fun k => by rw [Nat.pow_mod]; norm_num
  have hsplit : 2 ^ n = 8 ^ (n / 3) * 2 ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3]
    rw [pow_add, pow_mul]
    norm_num
  have hmod : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
    rw [hsplit, Nat.mul_mod, h8, one_mul, Nat.mod_mod]
  have hg : Nat.gcd (2 ^ n - 1) 7 = Nat.gcd ((2 ^ n - 1) % 7) 7 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
  have ha : a n = (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 7 := card_pow n 7 (by omega) (by norm_num)
  constructor
  · intro h
    rw [h] at hmod
    have h0 : (2 ^ n - 1) % 7 = 0 := by norm_num at hmod; omega
    rw [h0, Nat.gcd_zero_left] at hg
    rw [hg] at ha
    have hd : 7 * a n = 2 ^ n - 1 := by
      rw [ha]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)
    rw [← hM, ← hd]
    push_cast
    ring
  · intro h
    have hg1 : Nat.gcd ((2 ^ n - 1) % 7) 7 = 1 := by
      have hr : n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hr with hr | hr
      · rw [hr] at hmod
        have h0 : (2 ^ n - 1) % 7 = 1 := by norm_num at hmod; omega
        rw [h0, Nat.gcd_one_left]
      · rw [hr] at hmod
        have h0 : (2 ^ n - 1) % 7 = 3 := by norm_num at hmod; omega
        rw [h0]
        norm_num
    rw [hg1] at hg
    rw [hg, Nat.div_one] at ha
    rw [ha, hM]

theorem rec (m : ℕ) : (a (m + 7) : ℤ) = 9 * (a (m + 4) : ℤ) - 8 * (a (m + 1) : ℤ) := by
  have e7 : (2 : ℤ) ^ (m + 7) = 64 * 2 ^ (m + 1) := by ring
  have e4 : (2 : ℤ) ^ (m + 4) = 8 * 2 ^ (m + 1) := by ring
  by_cases h : (m + 1) % 3 = 0
  · have h7 := (a_spec (m + 7) (by omega)).1 (by omega)
    have h4 := (a_spec (m + 4) (by omega)).1 (by omega)
    have h1 := (a_spec (m + 1) (by omega)).1 h
    rw [e7] at h7
    rw [e4] at h4
    omega
  · have h7 := (a_spec (m + 7) (by omega)).2 (by omega)
    have h4 := (a_spec (m + 4) (by omega)).2 (by omega)
    have h1 := (a_spec (m + 1) (by omega)).2 h
    rw [e7] at h7
    rw [e4] at h4
    omega

theorem a_val (k : ℕ) (hk : 1 ≤ k) (v : ℤ)
    (hv : (k % 3 = 0 ∧ 7 * v = 2 ^ k - 1) ∨ (k % 3 ≠ 0 ∧ v = 2 ^ k - 1)) : (a k : ℤ) = v := by
  have h := a_spec k hk
  rcases hv with ⟨hk3, hv⟩ | ⟨hk3, hv⟩
  · have := h.1 hk3
    linarith
  · rw [h.2 hk3, hv]

noncomputable def c (n : ℕ) : ℤ := if n = 0 then 0 else (a n : ℤ)

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk c * X ^ k) = if k ≤ n then c (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * (if k ≤ n then c (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (n k j : ℕ) (h : n = j + k) : coeff n (PowerSeries.mk c * X ^ k) = c j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * c j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at n k j h]

end OMAA213245Helpers

open PowerSeries OMAA213245Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a213245.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 3 = m + 4 by omega, show m + 7 - 6 = m + 1 by omega]
    exact rec m
  · change PowerSeries.mk c * _ = _
    ext n
    have hD : ((X - 1) * (2 * X - 1) * (X ^ 2 + X + 1) * (4 * X ^ 2 + 2 * X + 1) :
        PowerSeries ℤ) = C 8 * X ^ 6 - C 9 * X ^ 3 + X ^ 0 := by
      rw [map_ofNat C 8, map_ofNat C 9]; ring
    have hN : (X * (4 * X ^ 4 + 6 * X ^ 3 + X ^ 2 + 3 * X + 1) : PowerSeries ℤ) =
        C 4 * X ^ 5 + C 6 * X ^ 4 + X ^ 3 + C 3 * X ^ 2 + X ^ 1 := by
      rw [map_ofNat C 4, map_ofNat C 6, map_ofNat C 3]; ring
    rw [hD, hN]
    have v0 : c 0 = 0 := rfl
    have v1 : c 1 = 1 := a_val 1 le_rfl 1 (Or.inr ⟨by norm_num, by norm_num⟩)
    have v2 : c 2 = 3 := a_val 2 (by norm_num) 3 (Or.inr ⟨by norm_num, by norm_num⟩)
    have v3 : c 3 = 1 := a_val 3 (by norm_num) 1 (Or.inl ⟨by norm_num, by norm_num⟩)
    have v4 : c 4 = 15 := a_val 4 (by norm_num) 15 (Or.inr ⟨by norm_num, by norm_num⟩)
    have v5 : c 5 = 31 := a_val 5 (by norm_num) 31 (Or.inr ⟨by norm_num, by norm_num⟩)
    have v6 : c 6 = 9 := a_val 6 (by norm_num) 9 (Or.inl ⟨by norm_num, by norm_num⟩)
    rcases Nat.lt_or_ge n 7 with h | h
    · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
        coeff_C_mul, coeff_X_pow]
      interval_cases n
      · norm_num [v0]
      · norm_num [v1]
      · norm_num [v2]
      · norm_num [v0, v3]
      · norm_num [v1, v4]
      · norm_num [v2, v5]
      · norm_num [v0, v3, v6]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      simp only [mul_add, mul_sub, map_add, map_sub]
      rw [coeff_at_C 8 (m + 7) 6 (m + 1) (by omega), coeff_at_C 9 (m + 7) 3 (m + 4) (by omega),
        coeff_at (m + 7) 0 (m + 7) (by omega), coeff_C_mul, coeff_C_mul, coeff_C_mul,
        coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hr := rec m
      simp only [c, show m + 7 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 1 ≠ 0 by omega,
        ↓reduceIte]
      linear_combination hr
