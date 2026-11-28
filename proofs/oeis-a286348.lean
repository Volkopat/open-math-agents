import OMAStatements.S_oeis_a286348
import Mathlib

/-
A286348: if (1 + y)^x + (-y)^x is a prime then x = 0, or x is a power of two (at least 2), or x
is an odd prime.

The expression is unchanged when y is replaced by -1 - y, so it is enough to treat
(m + 1)^x + (-m)^x with m >= 0. Suppose x is none of the listed exponents. If x = 1 the value is 1.
Otherwise x = u v with u >= 2 and v >= 3 odd (take for v an odd prime factor of x). For m = 0
the value is 1. For m >= 1 put g = (m + 1)^u + (-m)^u; then g divides the value because v is odd,
and 2 <= g < value by the elementary inequality (P - M) P^n <= P^(n+1) - M^(n+1) for 0 <= M <= P,
so the value is not prime.
-/

namespace OMA.P286348

lemma L (M P : ℤ) (hM : 0 ≤ M) (hMP : M ≤ P) (n : ℕ) :
    (P - M) * P ^ n ≤ P ^ (n + 1) - M ^ (n + 1) := by
  have h1 : M ^ n ≤ P ^ n := pow_le_pow_left₀ hM hMP n
  have h2 : M * M ^ n ≤ M * P ^ n := mul_le_mul_of_nonneg_left h1 hM
  rw [pow_succ, pow_succ]
  nlinarith

lemma absq (m : ℤ) (hm : 0 ≤ m) (n : ℕ) : -(m ^ n) ≤ (-m) ^ n ∧ (-m) ^ n ≤ m ^ n := by
  have h0 : 0 ≤ m ^ n := pow_nonneg hm n
  rw [neg_pow]
  rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] <;> constructor <;> linarith

lemma small (m : ℤ) (hm : 1 ≤ m) (u : ℕ) (hu : 2 ≤ u) : m ^ u + 2 ≤ (m + 1) ^ u := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
  have h1 := L m (m + 1) (by linarith) (by linarith) w
  have h2 : (m + 1) ^ 1 ≤ (m + 1) ^ w := pow_le_pow_right₀ (by linarith) (by omega)
  rw [pow_one] at h2
  have e : (m + 1 - m) * (m + 1) ^ w = (m + 1) ^ w := by ring
  rw [e] at h1
  linarith

lemma big (P M : ℤ) (hM : 1 ≤ M) (hPM : M + 2 ≤ P) (v : ℕ) (hv3 : 3 ≤ v) :
    P + M < P ^ v - M ^ v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have h1 := L M P (by linarith) (by linarith) w
  have h2 : P ^ 2 ≤ P ^ w := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 : 2 * P ^ w ≤ (P - M) * P ^ w :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) w)
  have h4 : 3 * P ≤ P ^ 2 := by nlinarith
  linarith

lemma core (m : ℤ) (hm : 0 ≤ m) (u v : ℕ) (hu : 2 ≤ u) (hv : Odd v) (hv3 : 3 ≤ v)
    (hpos : 0 < (m + 1) ^ (u * v) + (-m) ^ (u * v)) :
    ¬ ((m + 1) ^ (u * v) + (-m) ^ (u * v)).toNat.Prime := by
  intro hprime
  rcases hm.eq_or_lt with rfl | hm1
  · have h0 : u * v ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have : (0 + 1 : ℤ) ^ (u * v) + (-0) ^ (u * v) = 1 := by simp [h0]
    rw [this] at hprime
    norm_num at hprime
  · have hm1' : 1 ≤ m := hm1
    have hdvd : (m + 1) ^ u + (-m) ^ u ∣ (m + 1) ^ (u * v) + (-m) ^ (u * v) := by
      rw [pow_mul, pow_mul]
      exact Odd.add_dvd_pow_add_pow _ _ hv
    obtain ⟨hq1, hq2⟩ := absq m hm u
    obtain ⟨hr1, -⟩ := absq m hm (u * v)
    have hs := small m hm1' u hu
    have hb := big ((m + 1) ^ u) (m ^ u) (one_le_pow₀ hm1') (by linarith) v hv3
    rw [← pow_mul, ← pow_mul] at hb
    have hg2 : 2 ≤ (m + 1) ^ u + (-m) ^ u := by linarith
    have hgf : (m + 1) ^ u + (-m) ^ u < (m + 1) ^ (u * v) + (-m) ^ (u * v) := by linarith
    have hd' : ((m + 1) ^ u + (-m) ^ u).toNat ∣ ((m + 1) ^ (u * v) + (-m) ^ (u * v)).toNat := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg (by linarith),
        Int.toNat_of_nonneg (by linarith)]
      exact hdvd
    rcases hprime.eq_one_or_self_of_dvd _ hd' with h1 | h1
    · have := congrArg (Nat.cast : ℕ → ℤ) h1
      rw [Int.toNat_of_nonneg (by linarith)] at this
      push_cast at this
      linarith
    · have := congrArg (Nat.cast : ℕ → ℤ) h1
      rw [Int.toNat_of_nonneg (by linarith), Int.toNat_of_nonneg (by linarith)] at this
      linarith

lemma main' :
    ∀ (y : ℤ) (x : ℕ),
      0 < (1 + y) ^ x + (-y) ^ x →
      ((1 + y) ^ x + (-y) ^ x).toNat.Prime →
      x = 0 ∨ (∃ k ≥ 1, x = 2 ^ k) ∨ (x.Prime ∧ Odd x) := by
  intro y x hpos hprime
  by_contra hcon
  push Not at hcon
  obtain ⟨hx0, hx2, hxp⟩ := hcon
  have key : ∀ m : ℤ, 0 ≤ m → 0 < (m + 1) ^ x + (-m) ^ x →
      ¬ ((m + 1) ^ x + (-m) ^ x).toNat.Prime := by
    intro m hm hp
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd x with ⟨k, hk⟩ | ⟨p, hp', hpx, hodd⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · subst hk
        intro hpr
        have : (m + 1) ^ (2 ^ 0) + (-m) ^ (2 ^ 0) = 1 := by ring
        rw [this] at hpr
        norm_num at hpr
      · exact absurd hk (hx2 k hkpos)
    · obtain ⟨u, rfl⟩ := hpx
      have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hx0
      have hu1 : u ≠ 1 := by
        rintro rfl
        rw [mul_one] at hxp
        exact hxp hp' hodd
      have hp3 : 3 ≤ p := by
        have := hp'.two_le
        rcases hodd with ⟨t, rfl⟩
        omega
      rw [mul_comm] at hp ⊢
      exact core m hm u p (by omega) hodd hp3 hp
  rcases le_or_gt 0 y with hy | hy
  · have e : (1 + y) ^ x + (-y) ^ x = (y + 1) ^ x + (-y) ^ x := by rw [add_comm 1 y]
    rw [e] at hpos hprime
    exact key y hy hpos hprime
  · have e : (1 + y) ^ x + (-y) ^ x = ((-y - 1) + 1) ^ x + (-(-y - 1)) ^ x := by ring
    rw [e] at hpos hprime
    exact key (-y - 1) (by linarith) hpos hprime

end OMA.P286348

theorem OMA.solution : type_of% @OMA.S_oeis_a286348.main := OMA.P286348.main'
