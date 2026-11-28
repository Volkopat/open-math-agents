import OMAStatements.S_oeis_a294074

/-
Disproof of the OEIS A294074 primality criterion.
Author: CubeJerry, with Codex assistance.

Take p = 639857297 and k = 5. The prime p has a short Lucas certificate.
The number N = 32*p+1 = 20475433505 is composite, but (p+2)^32 = 1 mod N.
Raising the last congruence to the p-th power gives the claimed divisibility.

The witness was found by factoring 63^32-32^32 and screening divisors N
with N = 33 mod 64 and (N-1)/32 prime. The original OEIS entry reports
verification only below 10^10; this counterexample is larger.
-/


namespace A294074Counterexample

lemma prime_85451 : Nat.Prime 85451 := by norm_num

lemma prime_3076237 : Nat.Prime 3076237 := by
  apply lucas_primality 3076237 (6 : ZMod 3076237)
  · reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 ^ 2 * 3 ^ 2 * 85451 at hdiv
    have hcases : q = 2 ∨ q = 3 ∨ q = 85451 := by
      rcases hq.dvd_or_dvd hdiv with hsmall | hlarge
      · rcases hq.dvd_or_dvd hsmall with htwo | hthree
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
            (hq.dvd_of_dvd_pow htwo))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
            (hq.dvd_of_dvd_pow hthree)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq prime_85451).mp hlarge))
    rcases hcases with rfl | rfl | rfl <;> reduce_mod_char <;> decide

lemma prime_p : Nat.Prime 639857297 := by
  apply lucas_primality 639857297 (3 : ZMod 639857297)
  · reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 ^ 4 * 13 * 3076237 at hdiv
    have hcases : q = 2 ∨ q = 13 ∨ q = 3076237 := by
      rcases hq.dvd_or_dvd hdiv with hsmall | hlarge
      · rcases hq.dvd_or_dvd hsmall with htwo | hthirteen
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
            (hq.dvd_of_dvd_pow htwo))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13)).mp
            hthirteen))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq prime_3076237).mp hlarge))
    rcases hcases with rfl | rfl | rfl <;> reduce_mod_char <;> decide

lemma composite_n : ¬ Nat.Prime 20475433505 := by norm_num

lemma small_power : Nat.ModEq 20475433505 (639857299 ^ 32) 1 := by
  norm_num [Nat.ModEq]

lemma passes_of_small_power (a n k m : ℕ) (h : Nat.ModEq n (a ^ k) 1) :
    n ∣ a ^ (m * k) - 1 := by
  rw [Nat.mul_comm m k, pow_mul]
  simpa only [one_pow] using (h.pow m).symm.dvd'

lemma passes_test :
    639857297 * 2 ^ 5 + 1 ∣ (639857297 + 2) ^ (639857297 * 2 ^ 5) - 1 := by
  have h : Nat.ModEq (639857297 * 2 ^ 5 + 1) ((639857297 + 2) ^ (2 ^ 5)) 1 :=
    small_power
  exact passes_of_small_power _ _ _ _ h

lemma disproof :
    ¬ (∀ p k : ℕ, Nat.Prime p → p ≠ 2 → Odd k →
      (Nat.Prime (p * 2 ^ k + 1) ↔ p * 2 ^ k + 1 ∣ (p + 2) ^ (p * 2 ^ k) - 1)) := by
  intro h
  have hp := (h 639857297 5 prime_p (by norm_num) ⟨2, rfl⟩).mpr passes_test
  exact composite_n hp

end A294074Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294074.main) := by
  exact A294074Counterexample.disproof
