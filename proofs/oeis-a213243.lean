import OMAStatements.S_oeis_a213243
import Mathlib

/-!
Credit: @ivillar
Proof (the argument behind the OEIS formula a(n) = M/gcd(M,3), M = 2^n - 1, which Robert Israel
used to verify Barker's conjectures): the nonzero cubes of GF(2^n) are the image of the cube map
on the cyclic group of units, of order M, so there are M/gcd(M,3) of them; gcd(M,3) is 3 for
even n and 1 for odd n. The closed form, the recurrence and the g.f. follow by algebra.
-/

namespace OMAA213243Helpers
open PowerSeries OMA.S_oeis_a213243

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
    (n % 2 = 0 → 3 * (a n : ℤ) = 2 ^ n - 1) ∧ (n % 2 = 1 → (a n : ℤ) = 2 ^ n - 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hM : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by push_cast [Nat.cast_sub h1]; ring
  have hmod : n % 2 = 0 → 2 ^ n % 3 = 1 := by
    intro h
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hmod' : n % 2 = 1 → 2 ^ n % 3 = 2 := by
    intro h
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hg : Nat.gcd (2 ^ n - 1) 3 = Nat.gcd ((2 ^ n - 1) % 3) 3 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
  have ha : a n = (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 3 := card_pow n 3 (by omega) (by norm_num)
  constructor
  · intro h
    have hm := hmod h
    have h0 : (2 ^ n - 1) % 3 = 0 := by omega
    rw [h0, Nat.gcd_zero_left] at hg
    rw [hg] at ha
    have hd : 3 * a n = 2 ^ n - 1 := by
      rw [ha]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)
    rw [← hM, ← hd]
    push_cast
    ring
  · intro h
    have hm := hmod' h
    have h0 : (2 ^ n - 1) % 3 = 1 := by omega
    rw [h0, Nat.gcd_one_left] at hg
    rw [hg, Nat.div_one] at ha
    rw [ha, hM]

theorem a_val (k : ℕ) (hk : 1 ≤ k) (v : ℤ)
    (hv : (k % 2 = 0 ∧ 3 * v = 2 ^ k - 1) ∨ (k % 2 = 1 ∧ v = 2 ^ k - 1)) : (a k : ℤ) = v := by
  have h := a_spec k hk
  rcases hv with ⟨hk2, hv⟩ | ⟨hk2, hv⟩
  · have := h.1 hk2
    linarith
  · rw [h.2 hk2, hv]

theorem rec (m : ℕ) : (a (m + 5) : ℤ) = 5 * (a (m + 3) : ℤ) - 4 * (a (m + 1) : ℤ) := by
  have e5 : (2 : ℤ) ^ (m + 5) = 16 * 2 ^ (m + 1) := by ring
  have e3 : (2 : ℤ) ^ (m + 3) = 4 * 2 ^ (m + 1) := by ring
  rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h
  · have h5 := (a_spec (m + 5) (by omega)).1 (by omega)
    have h3 := (a_spec (m + 3) (by omega)).1 (by omega)
    have h1 := (a_spec (m + 1) (by omega)).1 h
    rw [e5] at h5
    rw [e3] at h3
    omega
  · have h5 := (a_spec (m + 5) (by omega)).2 (by omega)
    have h3 := (a_spec (m + 3) (by omega)).2 (by omega)
    have h1 := (a_spec (m + 1) (by omega)).2 h
    rw [e5] at h5
    rw [e3] at h3
    omega

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

end OMAA213243Helpers

open PowerSeries OMAA213243Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a213243.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h3 := (a_spec n hn).1 h
      have hq : ((3 * (OMA.S_oeis_a213243.a n : ℤ) : ℤ) : ℚ) = ((2 ^ n - 1 : ℤ) : ℚ) := by
        rw [h3]
      push_cast at hq
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      rw [pow_mul, neg_one_sq, one_pow]
      linarith
    · have h3 := (a_spec n hn).2 h
      have hq : ((OMA.S_oeis_a213243.a n : ℤ) : ℚ) = ((2 ^ n - 1 : ℤ) : ℚ) := by rw [h3]
      push_cast at hq
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      rw [pow_succ, pow_mul, neg_one_sq, one_pow]
      rw [hq]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 2 = m + 3 by omega, show m + 5 - 4 = m + 1 by omega]
    exact rec m
  · change PowerSeries.mk c * _ = _
    ext n
    have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
    have h5 : (C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat C 5
    have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
    have hD : ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) : PowerSeries ℤ) =
        C 4 * X ^ 4 - C 5 * X ^ 2 + X ^ 0 := by
      rw [h4, h5]; ring
    have hN : (X * (2 * X ^ 2 + X + 1) : PowerSeries ℤ) = C 2 * X ^ 3 + X ^ 2 + X ^ 1 := by
      rw [h2]; ring
    rw [hD, hN]
    have v1 : c 1 = 1 := a_val 1 le_rfl 1 (Or.inr ⟨rfl, by norm_num⟩)
    have v2 : c 2 = 1 := a_val 2 (by norm_num) 1 (Or.inl ⟨rfl, by norm_num⟩)
    have v3 : c 3 = 7 := a_val 3 (by norm_num) 7 (Or.inr ⟨rfl, by norm_num⟩)
    have v4 : c 4 = 5 := a_val 4 (by norm_num) 5 (Or.inl ⟨rfl, by norm_num⟩)
    have v0 : c 0 = 0 := rfl
    rcases Nat.lt_or_ge n 5 with h | h
    · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
        coeff_C_mul, coeff_X_pow]
      interval_cases n
      · norm_num [v0]
      · norm_num [v1]
      · norm_num [v0, v2]
      · norm_num [v1, v3]
      · norm_num [v0, v2, v4]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      simp only [mul_add, mul_sub, map_add, map_sub]
      rw [coeff_at_C 4 (m + 5) 4 (m + 1) (by omega), coeff_at_C 5 (m + 5) 2 (m + 3) (by omega),
        coeff_at (m + 5) 0 (m + 5) (by omega), coeff_C_mul, coeff_X_pow, coeff_X_pow,
        coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hr := rec m
      simp only [c, show m + 5 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 1 ≠ 0 by omega,
        ↓reduceIte]
      linear_combination hr
