import OMAStatements.S_oeis_a280199
import Mathlib

-- Problem: OEIS A280199, conjecture: the composite terms of A280199 (numbers n such that
-- a^(n-1) == 1 (mod n^2) has a solution with 1 < a < n^2 - 1) are exactly the terms of A181780
-- (composite n that are Fermat pseudoprimes to some base b with 2 <= b <= n - 2).
-- Statement: statements/oeis-a280199.lean (declaration OMA.S_oeis_a280199.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The basic fact is: if x == c (mod n), then x^n == c^n (mod n^2).
-- From n^2 to n. Let a^(n-1) == 1 (mod n^2) with 1 < a < n^2 - 1, and let b = a mod n. Then
-- b^(n-1) == 1 (mod n), thus b is not 0. We have a^n == a (mod n^2). If b = 1, then
-- a^n == 1 (mod n^2), thus a == 1 (mod n^2), which is not possible. If b = n - 1, then
-- a^n == (-1)^n (mod n^2), thus a == 1 or a == -1 (mod n^2), which is not possible.
-- From n to n^2. Let b^(n-1) == 1 (mod n) with 2 <= b <= n - 2, and let a = b^n mod n^2. Then
-- a^(n-1) == (b^(n-1))^n == 1 (mod n^2) by the basic fact, and a == b (mod n). Thus a is not
-- 0, 1 or n^2 - 1.

namespace OMA.A280199

open OMA.S_oeis_a280199

lemma lift (n : ℕ) (x c : ℤ) (h : (n : ℤ) ∣ x - c) : (n : ℤ) ^ 2 ∣ x ^ n - c ^ n := by
  have := dvd_sub_pow_of_dvd_sub h 1
  simpa using this

lemma sq_sub_one_mod (n : ℕ) (hn : 1 < n) : (n ^ 2 - 1) % n = n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h : (k + 1) ^ 2 = k + (k + 1) * k + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_mul_mod_self_left, Nat.add_sub_cancel]
  exact Nat.mod_eq_of_lt (by omega)

lemma forward (n : ℕ) (hn : 1 < n) (a : ℕ) (h1 : 1 < a) (h2 : a < n ^ 2 - 1)
    (h3 : a ^ (n - 1) ≡ 1 [MOD n ^ 2]) :
    ∃ b : ℕ, 2 ≤ b ∧ b ≤ n - 2 ∧ b ^ (n - 1) ≡ 1 [MOD n] := by
  have hb : (a % n) ^ (n - 1) ≡ 1 [MOD n] :=
    ((Nat.mod_modEq a n).pow (n - 1)).trans (h3.of_dvd (Dvd.intro_left (n ^ 1) (by ring)))
  have hlt : a % n < n := Nat.mod_lt _ (by omega)
  -- facts over the integers
  have hZ : (n : ℤ) ^ 2 ∣ (a : ℤ) ^ n - a := by
    have h4 : ((a ^ (n - 1) : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD ((n ^ 2 : ℕ) : ℤ)] :=
      Int.natCast_modEq_iff.2 h3
    have h5 := h4.symm.dvd
    push_cast at h5
    have e : (a : ℤ) ^ n - a = ((a : ℤ) ^ (n - 1) - 1) * a := by
      have : n = n - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    rw [e]; exact Dvd.dvd.mul_right h5 _
  have hM : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hA : (a : ℤ) + 1 < (n : ℤ) ^ 2 := by
    have : a + 1 < n ^ 2 := by omega
    exact_mod_cast this
  have hA1 : (1 : ℤ) < a := by exact_mod_cast h1
  have key1 : ¬ (n : ℤ) ^ 2 ∣ (a : ℤ) - 1 := by
    intro hd
    have := Int.le_of_dvd (by linarith) hd
    linarith
  have key2 : ¬ (n : ℤ) ^ 2 ∣ (a : ℤ) + 1 := by
    intro hd
    have := Int.le_of_dvd (by linarith) hd
    linarith
  have hdm : (a : ℤ) = n * ((a / n : ℕ) : ℤ) + ((a % n : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a n).symm
  have b0 : a % n ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hb
    have := hb
    unfold Nat.ModEq at this
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hn] at this
    exact absurd this (by norm_num)
  have b1 : a % n ≠ 1 := by
    intro h0
    have hd : (n : ℤ) ∣ (a : ℤ) - 1 := by
      rw [hdm, h0]; exact ⟨((a / n : ℕ) : ℤ), by push_cast; ring⟩
    have hl := lift n a 1 hd
    rw [one_pow] at hl
    apply key1
    have := dvd_sub hl hZ
    have e : (a : ℤ) ^ n - 1 - ((a : ℤ) ^ n - a) = a - 1 := by ring
    rwa [e] at this
  have b2 : a % n ≠ n - 1 := by
    intro h0
    have hd : (n : ℤ) ∣ (a : ℤ) - (-1) := by
      rw [hdm, h0]
      refine ⟨((a / n : ℕ) : ℤ) + 1, ?_⟩
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hl := lift n a (-1) hd
    have hsub := dvd_sub hl hZ
    have e : (a : ℤ) ^ n - (-1) ^ n - ((a : ℤ) ^ n - a) = a - (-1) ^ n := by ring
    rw [e] at hsub
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow] at hsub; exact key1 hsub
    · rw [ho.neg_one_pow] at hsub
      apply key2
      have e2 : (a : ℤ) - -1 = a + 1 := by ring
      rwa [e2] at hsub
  exact ⟨a % n, by omega, by omega, hb⟩

lemma backward (n : ℕ) (hn : 1 < n) (b : ℕ) (h1 : 2 ≤ b) (h2 : b ≤ n - 2)
    (h3 : b ^ (n - 1) ≡ 1 [MOD n]) :
    ∃ a : ℕ, 1 < a ∧ a < n ^ 2 - 1 ∧ a ^ (n - 1) ≡ 1 [MOD n ^ 2] := by
  have hn2 : 0 < n ^ 2 := by positivity
  have hmod : (b ^ n % n ^ 2) % n = b := by
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left (n ^ 1) (by ring))]
    have e : b ^ n = b ^ (n - 1) * b := by
      have : n = n - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ]
    have h4 : b ^ n ≡ b [MOD n] := by
      rw [e]; simpa using h3.mul_right b
    have := h4
    unfold Nat.ModEq at this
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  have hpow : (b ^ n % n ^ 2) ^ (n - 1) ≡ 1 [MOD n ^ 2] := by
    refine ((Nat.mod_modEq (b ^ n) (n ^ 2)).pow (n - 1)).trans ?_
    have hd : (n : ℤ) ∣ (b : ℤ) ^ (n - 1) - 1 := by
      have h4 : ((b ^ (n - 1) : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (n : ℤ)] :=
        Int.natCast_modEq_iff.2 h3
      have h5 := h4.symm.dvd
      push_cast at h5
      exact h5
    have hl := lift n _ 1 hd
    rw [one_pow] at hl
    apply Int.natCast_modEq_iff.1
    apply Int.ModEq.symm
    apply (Int.modEq_iff_dvd).2
    push_cast
    have e : ((b : ℤ) ^ n) ^ (n - 1) = ((b : ℤ) ^ (n - 1)) ^ n := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e]; exact hl
  have hlt : b ^ n % n ^ 2 < n ^ 2 := Nat.mod_lt _ hn2
  generalize b ^ n % n ^ 2 = r at hmod hpow hlt
  refine ⟨r, ?_, ?_, hpow⟩
  · by_contra hle
    have hcases : r = 0 ∨ r = 1 := by omega
    rcases hcases with h0 | h0
    · rw [h0, Nat.zero_mod] at hmod; omega
    · rw [h0, Nat.mod_eq_of_lt hn] at hmod; omega
  · have hne : r ≠ n ^ 2 - 1 := by
      intro h0
      rw [h0, sq_sub_one_mod n hn] at hmod; omega
    omega

theorem main' (n : ℕ) : (1 < n ∧ ¬ n.Prime ∧ InA280199 n) ↔ InA181780 n := by
  constructor
  · rintro ⟨hn, hp, a, h1, h2, h3⟩
    exact ⟨hn, hp, forward n hn a h1 h2 h3⟩
  · rintro ⟨hn, hp, b, h1, h2, h3⟩
    exact ⟨hn, hp, backward n hn b h1 h2 h3⟩

end OMA.A280199

theorem OMA.solution : type_of% @OMA.S_oeis_a280199.main :=
  fun n => OMA.A280199.main' n
