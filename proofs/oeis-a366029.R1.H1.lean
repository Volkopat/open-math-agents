import OMAReductions.R_oeis_a366029_R1
import Mathlib

/-! If `2^k - 1` is prime or `k` is a Fermat number then `(2^k - 1) k² ∣ (k-1)^(2^k-2) - 1`.
In both cases `k ∣ 2^k - 2` (Fermat's little theorem; Fermat numbers are base-2 pseudoprimes),
which makes `2^k - 1` and `k` coprime. Modulo `k²`, `(k-1)^N ≡ (-1)^N (1 - N k)`, which is `1`
for even `N` divisible by `k`. Modulo `2^k - 1`: Fermat's little theorem in the Mersenne case,
and `2^k ≡ 1` together with `k ∣ 2^k - 2` in the Fermat-number case. -/

namespace A366029

/-- `(k-1)^n ≡ (-1)^n (1 - n k) (mod k²)`. -/
lemma binom (k : ℤ) (n : ℕ) : k ^ 2 ∣ (k - 1) ^ n - (-1) ^ n * (1 - n * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨(k - 1) * c - (-1) ^ n * n, by push_cast; linear_combination (k - 1) * hc⟩

lemma sq_part {k N : ℕ} (hk : 1 < k) (hN : Even N) (hkN : k ∣ N) :
    k ^ 2 ∣ (k - 1) ^ N - 1 := by
  have h1 : 1 ≤ (k - 1) ^ N := Nat.one_le_pow _ _ (by omega)
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub h1, Nat.cast_sub hk.le]
  obtain ⟨c, hc⟩ := binom (k : ℤ) N
  obtain ⟨d, rfl⟩ := hkN
  rw [hN.neg_one_pow] at hc
  exact ⟨c - d, by push_cast at hc ⊢; linear_combination hc⟩

/-- `k ∣ 2^k - 2` whenever `2^k ≡ 2 (mod k)`. -/
lemma dvd_of_zmod {k : ℕ} (h : ((2 : ℕ) : ZMod k) ^ k = ((2 : ℕ) : ZMod k)) (hk : 1 < k) :
    k ∣ 2 ^ k - 2 := by
  have : ((2 ^ k : ℕ) : ZMod k) = ((2 : ℕ) : ZMod k) := by push_cast at h ⊢; exact h
  rw [ZMod.natCast_eq_natCast_iff] at this
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (Nat.modEq_iff_dvd' h2).mp this.symm

end A366029

open A366029 in
theorem OMA.solution : OMA.R_oeis_a366029_R1.H1 := by
  intro k hk hcase
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  -- `k ∣ 2^k - 2` and the divisibility modulo `2^k - 1`
  have key : k ∣ 2 ^ k - 2 ∧ (2 ^ k - 1) ∣ (k - 1) ^ (2 ^ k - 2) - 1 := by
    rcases hcase with hp | ⟨m, rfl⟩
    · have hkp : k.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) hp).2
      have := Fact.mk hkp
      have := Fact.mk hp
      refine ⟨dvd_of_zmod (ZMod.pow_card _) hk, ?_⟩
      have hne : ((k - 1 : ℕ) : ZMod (2 ^ k - 1)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      have hf := ZMod.pow_card_sub_one_eq_one hne
      have e : 2 ^ k - 1 - 1 = 2 ^ k - 2 := by omega
      rw [e] at hf
      have : (((k - 1) ^ (2 ^ k - 2) : ℕ) : ZMod (2 ^ k - 1)) = ((1 : ℕ) : ZMod (2 ^ k - 1)) := by
        push_cast; exact hf
      rw [ZMod.natCast_eq_natCast_iff] at this
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm
    · have hdiv : 2 * 2 ^ m ∣ 2 ^ 2 ^ m := by
        rw [← pow_succ']
        exact Nat.pow_dvd_pow 2 (Nat.lt_two_pow_self (n := m))
      generalize 2 ^ m = E at hdiv ⊢
      -- in `ZMod k`, `2^E = -1`, hence `2^(2^(m+1)) = 1` and `2^(k-1) = 1`
      have hz : ((2 : ℕ) : ZMod (2 ^ E + 1)) ^ (2 ^ E + 1) = ((2 : ℕ) : ZMod (2 ^ E + 1)) := by
        have hm1 : ((2 : ℕ) : ZMod (2 ^ E + 1)) ^ E = -1 := by
          have : ((2 ^ E + 1 : ℕ) : ZMod (2 ^ E + 1)) = 0 := ZMod.natCast_self _
          push_cast at this ⊢
          linear_combination this
        have hm2 : ((2 : ℕ) : ZMod (2 ^ E + 1)) ^ (2 * E) = 1 := by
          rw [pow_mul', hm1]; norm_num
        obtain ⟨t, ht⟩ := hdiv
        have ex : ((2 : ℕ) : ZMod (2 ^ E + 1)) ^ (2 ^ E) =
            ((2 : ℕ) : ZMod (2 ^ E + 1)) ^ (2 * E * t) := by rw [← ht]
        rw [pow_succ, ex, pow_mul, hm2, one_pow, one_mul]
      have hkd : (2 ^ E + 1) ∣ 2 ^ (2 ^ E + 1) - 2 := dvd_of_zmod hz (by
        have := Nat.one_le_two_pow (n := E); omega)
      refine ⟨hkd, ?_⟩
      obtain ⟨t, ht⟩ := hkd
      have hmod : 1 ≡ 2 ^ (2 ^ E + 1) [MOD 2 ^ (2 ^ E + 1) - 1] :=
        (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr dvd_rfl
      have hpow := hmod.pow (E * t)
      rw [one_pow, ← pow_mul] at hpow
      have e : (2 ^ E + 1 - 1) ^ (2 ^ (2 ^ E + 1) - 2) = 2 ^ ((2 ^ E + 1) * (E * t)) := by
        rw [Nat.add_sub_cancel, ← pow_mul, ht]; ring_nf
      rw [e]
      exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hpow
  obtain ⟨hkd, hD⟩ := key
  have hev : Even (2 ^ k - 2) := ⟨2 ^ (k - 1) - 1, by
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    omega⟩
  have hC := sq_part hk hev hkd
  have hcop : Nat.Coprime (2 ^ k - 1) k := by
    have c1 : Nat.Coprime (2 ^ k - 1) (2 ^ k - 2) := by
      rw [show 2 ^ k - 1 = (2 ^ k - 2) + 1 by omega]
      exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
    exact Nat.Coprime.coprime_dvd_right hkd c1
  exact (hcop.pow_right 2).mul_dvd_of_dvd_of_dvd hD hC
