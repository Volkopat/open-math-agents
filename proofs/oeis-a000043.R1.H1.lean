import OMAReductions.R_oeis_a000043_R1
import Mathlib

/-! The forward directions of the two A000043 congruence conjectures.

Write E = 2^k - 2. Three ingredients.

* Modulo k^2: (k - 1)^(2j) = 1 - 2kj + t k^2 by induction on j, so (k - 1)^E is 1 modulo k^2
  as soon as k divides E.
* If k divides 2^k - 2 then gcd(2^k - 1, k) = 1, so the congruences modulo 2^k - 1 and modulo
  k^2 combine.
* If 2^k - 1 is prime then k is prime, k divides 2^k - 2 by Fermat, and (k - 1)^E is 1 modulo
  the prime 2^k - 1 by Fermat again. If k = F = 2^(2^m) + 1 is a Fermat number, prime or not,
  then 2^(2^(m+1)) is 1 modulo F and m + 1 <= 2^m, so F divides 2^(F-1) - 1, hence F divides
  2^F - 2, and (F - 1)^E = 2^(2^m E) is a power of 2^F, which is 1 modulo 2^F - 1. -/

namespace A000043

/-- Binomial expansion of `(k - 1) ^ (2 j)` modulo `k ^ 2`. -/
lemma sub_one_pow_two_mul (k : ℤ) (j : ℕ) :
    ∃ t : ℤ, (k - 1) ^ (2 * j) = 1 - 2 * k * j + t * k ^ 2 := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨1 + 4 * j - 2 * k * j + t * (k - 1) ^ 2, ?_⟩
    have h2 : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [h2, pow_add, ht]
    push_cast
    ring

lemma sub_one_pow_modEq_one {k E : ℕ} (hk : 1 ≤ k) (hE : Even E) (hdvd : k ∣ E) :
    (k - 1) ^ E ≡ 1 [MOD k ^ 2] := by
  obtain ⟨j, hj⟩ := hE
  obtain ⟨e, he⟩ := hdvd
  obtain ⟨t, ht⟩ := sub_one_pow_two_mul (k : ℤ) j
  have hE2 : E = 2 * j := by omega
  apply (Int.natCast_modEq_iff).mp
  push_cast [Nat.cast_sub hk]
  rw [hE2, ht]
  have h2 : (2 : ℤ) * k * j = (k : ℤ) ^ 2 * e := by
    have h3 : ((2 * j : ℕ) : ℤ) = ((k * e : ℕ) : ℤ) := by rw [← hE2, he]
    push_cast at h3
    linear_combination (k : ℤ) * h3
  rw [h2]
  apply Int.modEq_iff_dvd.mpr
  exact ⟨e - t, by ring⟩

lemma key {k : ℕ} (hk : 1 < k) (hdvd : k ∣ 2 ^ k - 2)
    (hM : (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD 2 ^ k - 1]) :
    (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2] := by
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hEven : Even (2 ^ k - 2) := by
    obtain ⟨c, hc⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    refine ⟨2 ^ c - 1, ?_⟩
    rw [hc, pow_succ]
    have h1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    omega
  have hk2 := sub_one_pow_modEq_one (by omega : 1 ≤ k) hEven hdvd
  have hcop : Nat.Coprime (2 ^ k - 1) (k ^ 2) := by
    apply Nat.Coprime.pow_right
    have hg1 : Nat.gcd (2 ^ k - 1) k ∣ 2 ^ k - 1 := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd (2 ^ k - 1) k ∣ 2 ^ k - 2 := (Nat.gcd_dvd_right _ _).trans hdvd
    have hsub : (2 ^ k - 1) - (2 ^ k - 2) = 1 := by omega
    have h := Nat.dvd_sub hg1 hg2
    rw [hsub] at h
    exact Nat.dvd_one.mp h
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hM, hk2⟩

lemma prime_dvd_two_pow_sub_two {k : ℕ} (hk : k.Prime) : k ∣ 2 ^ k - 2 := by
  have hfact : Fact k.Prime := ⟨hk⟩
  have h : ((2 ^ k : ℕ) : ZMod k) = ((2 : ℕ) : ZMod k) := by
    push_cast
    exact ZMod.pow_card 2
  have h' : 2 ≡ 2 ^ k [MOD k] := ((ZMod.natCast_eq_natCast_iff _ _ _).mp h).symm
  have hle : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.one_lt.le
  exact (Nat.modEq_iff_dvd' hle).mp h'

lemma mersenne_case {k : ℕ} (hk : 1 < k) (hP : (2 ^ k - 1).Prime) :
    (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2] := by
  have hkp : k.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) hP).2
  apply key hk (prime_dvd_two_pow_sub_two hkp)
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have hcop : Nat.Coprime (k - 1) (2 ^ k - 1) := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hP]
    intro h
    have h1 := Nat.le_of_dvd (by omega) h
    omega
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hP] at h
  have e : 2 ^ k - 1 - 1 = 2 ^ k - 2 := by omega
  rw [e] at h
  exact h

/-- Fermat numbers are pseudoprimes to the base 2. -/
lemma fermat_pow_modEq (m : ℕ) : 2 ^ (2 ^ 2 ^ m) ≡ 1 [MOD 2 ^ 2 ^ m + 1] := by
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ 2 ^ m := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Nat.one_le_two_pow
  have hsq : a ^ 2 ≡ 1 [MOD a + 1] := by
    have h : a ^ 2 = (a + 1) * (a - 1) + 1 := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [h]
    exact Nat.mul_add_mod _ _ _
  have hle : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have hexp : 2 ^ m = (m + 1) + (2 ^ m - (m + 1)) := by omega
  have h2a : 2 ^ a = (a ^ 2) ^ (2 ^ (2 ^ m - (m + 1))) := by
    have h3 : 2 ^ m * (2 * 2 ^ (2 ^ m - (m + 1))) = 2 ^ (m + 1 + (2 ^ m - (m + 1))) := by
      rw [pow_add, pow_succ]
      ring
    rw [ha, ← pow_mul, ← pow_mul, h3, ← hexp]
  rw [← ha, h2a]
  have h5 := hsq.pow (2 ^ (2 ^ m - (m + 1)))
  rw [one_pow] at h5
  exact h5

lemma fermat_case (m : ℕ) :
    (2 ^ 2 ^ m + 1 - 1) ^ (2 ^ (2 ^ 2 ^ m + 1) - 2) ≡ 1
      [MOD (2 ^ (2 ^ 2 ^ m + 1) - 1) * (2 ^ 2 ^ m + 1) ^ 2] := by
  have hF := fermat_pow_modEq m
  have h1le : 1 ≤ 2 ^ (2 ^ 2 ^ m) := Nat.one_le_two_pow
  have hd1 : (2 ^ 2 ^ m + 1) ∣ 2 ^ (2 ^ 2 ^ m) - 1 := (Nat.modEq_iff_dvd' h1le).mp hF.symm
  have hdvd : (2 ^ 2 ^ m + 1) ∣ 2 ^ (2 ^ 2 ^ m + 1) - 2 := by
    have e : 2 ^ (2 ^ 2 ^ m + 1) - 2 = (2 ^ (2 ^ 2 ^ m) - 1) * 2 := by
      rw [pow_succ]
      omega
    rw [e]
    exact Dvd.dvd.mul_right hd1 2
  have hk : 1 < 2 ^ 2 ^ m + 1 := by
    have : 1 ≤ 2 ^ 2 ^ m := Nat.one_le_two_pow
    omega
  apply key hk hdvd
  obtain ⟨t, ht⟩ := hdvd
  rw [Nat.add_sub_cancel, ht, ← pow_mul]
  have e2 : 2 ^ m * ((2 ^ 2 ^ m + 1) * t) = (2 ^ 2 ^ m + 1) * (2 ^ m * t) := by ring
  rw [e2, pow_mul]
  have hone : 2 ^ (2 ^ 2 ^ m + 1) ≡ 1 [MOD 2 ^ (2 ^ 2 ^ m + 1) - 1] := by
    have h2 : 2 ≤ 2 ^ (2 ^ 2 ^ m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ 2 ^ m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : 2 ^ (2 ^ 2 ^ m + 1) = (2 ^ (2 ^ 2 ^ m + 1) - 1) + 1 := by omega
    conv_lhs => rw [e3]
    exact Nat.add_mod_left _ _
  have h5 := hone.pow (2 ^ m * t)
  rw [one_pow] at h5
  exact h5

theorem forward :
    (∀ k : ℕ, 1 < k → ((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1) →
      (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2]) ∧
    (∀ p : ℕ, p.Prime → ((2 ^ p - 1).Prime ∨ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1) →
      (p - 1) ^ (2 ^ p - 2) ≡ 1 [MOD 2 ^ p - 1]) := by
  have h1 : ∀ k : ℕ, 1 < k → ((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1) →
      (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2] := by
    intro k hk h
    rcases h with hP | ⟨m, rfl⟩
    · exact mersenne_case hk hP
    · exact fermat_case m
  exact ⟨h1, fun p hp h => Nat.ModEq.of_mul_right _ (h1 p hp.one_lt h)⟩

end A000043

theorem OMA.solution : OMA.R_oeis_a000043_R1.H1 := by
  unfold OMA.R_oeis_a000043_R1.H1
  exact A000043.forward
