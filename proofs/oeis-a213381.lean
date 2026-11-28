import OMAStatements.S_oeis_a213381
import Mathlib

/-!
Following @Mapika (#13393), with Robert Israel's argument retained.
Use the unit and natural-cast APIs for the modular helper calculations.

Robert Israel's argument (OEIS A213381, May 05 2015): since `n ≡ -2 (mod n+2)`,
`n^n ≡ (-2)^n (mod n+2)`.
* Zeros: `(n+2) ∣ n^n ↔ (n+2) ∣ 2^n ↔ n + 2 = 2^j` with `j ≤ n`.
* `n = 3q - 2`: `n ≡ 1 (mod 3)`, and Fermat gives `n^(3q-2) ≡ n (mod q)`; combine by CRT
  (the case `q = 3`, i.e. `n = 7`, is a direct computation).
* Odd prime `p`: in `ZMod p`, both `(-2)^(p-2)` and `(p-1)/2` are inverses of `-2`.
-/

namespace A213381Proof

open OMA.S_oeis_a213381

lemma dvd_iff_two (n : ℕ) : (n + 2) ∣ n ^ n ↔ (n + 2) ∣ 2 ^ n := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
  have h : ((n : ℕ) : ZMod (n + 2)) = -2 := by
    have : ((n + 2 : ℕ) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at this
    linear_combination this
  push_cast
  rw [h, neg_pow]
  exact (isUnit_neg_one.pow n).mul_right_eq_zero

lemma part1 (n : ℕ) : a n = 0 ↔ ∃ x : ℕ, n = 2 ^ (x + 2) - 2 := by
  unfold a
  rw [← Nat.dvd_iff_mod_eq_zero, dvd_iff_two, Nat.dvd_prime_pow Nat.prime_two]
  constructor
  · rintro ⟨j, hj, he⟩
    obtain ⟨x, rfl⟩ : ∃ x, j = x + 2 := by
      rcases j with _ | _ | x
      · simp at he
      · simp at he; omega
      · exact ⟨x, rfl⟩
    exact ⟨x, by omega⟩
  · rintro ⟨x, rfl⟩
    have h1 : x < 2 ^ x := Nat.lt_two_pow_self
    have h2 : 2 ^ (x + 2) = 4 * 2 ^ x := by ring
    refine ⟨x + 2, by omega, by omega⟩

lemma modq (q n : ℕ) (hq : q.Prime) (hn : n = 3 * q - 2) : n ^ n ≡ n [MOD q] := by
  have := Fact.mk hq
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have hq2 := hq.two_le
  by_cases h0 : (n : ZMod q) = 0
  · rw [h0, zero_pow (by omega)]
  · have hexp : n = 3 * (q - 1) + 1 := by omega
    calc (n : ZMod q) ^ n = (n : ZMod q) ^ (3 * (q - 1) + 1) := by rw [← hexp]
      _ = ((n : ZMod q) ^ (q - 1)) ^ 3 * (n : ZMod q) := by ring
      _ = n := by rw [ZMod.pow_card_sub_one_eq_one h0, one_pow, one_mul]

lemma part2 (n : ℕ) (h : InA176003 n) : a n = n := by
  obtain ⟨q, hq | hq, rfl⟩ := h
  · subst hq; decide
  · unfold a
    by_cases h3 : q = 3
    · subst h3; norm_num
    have hq2 := hq.two_le
    have hmod3 : (3 * q - 2) ^ (3 * q - 2) ≡ (3 * q - 2) [MOD 3] := by
      have e : (3 * q - 2) % 3 = 1 := by omega
      unfold Nat.ModEq
      rw [Nat.pow_mod, e, one_pow]
      norm_num
    have hcop : Nat.Coprime 3 q := by
      rw [Nat.coprime_primes Nat.prime_three hq]; exact fun h => h3 h.symm
    have hm := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmod3, modq q _ hq rfl⟩
    have e2 : 3 * q - 2 + 2 = 3 * q := by omega
    rw [e2]
    unfold Nat.ModEq at hm
    rw [hm]
    exact Nat.mod_eq_of_lt (by omega)

lemma part3 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : a (p - 2) = (p - 1) / 2 := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  unfold a
  have e : p - 2 + 2 = p := by omega
  rw [e]
  have hlt : (p - 1) / 2 < p := by omega
  rw [← Nat.mod_eq_of_lt hlt, ← ZMod.natCast_eq_natCast_iff']
  have hy : ((p - 2 : ℕ) : ZMod p) = -2 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; push_cast; ring
  have h2ne : (2 : ZMod p) ≠ 0 := by
    exact ((ZMod.isUnit_iff_coprime 2 p).mpr (Nat.coprime_two_left.mpr (hp.odd_of_ne_two h2))).ne_zero
  have hyne : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2ne
  have hhalf : (((p - 1) / 2 : ℕ) : ZMod p) * 2 = -1 := by
    rw [← Nat.cast_ofNat (R := ZMod p) (n := 2), ← Nat.cast_mul,
      show (p - 1) / 2 * 2 = p - 1 by omega, Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  push_cast
  rw [hy]
  have hfer : (-2 : ZMod p) ^ (p - 2) * (-2) = 1 := by
    rw [← pow_succ, show p - 2 + 1 = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hyne]
  apply mul_right_cancel₀ hyne
  rw [hfer]
  linear_combination hhalf
end A213381Proof

open A213381Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a213381.main :=
  ⟨part1, part2, part3⟩
