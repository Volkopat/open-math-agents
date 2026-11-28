import OMAStatements.S_oeis_a240920

-- Problem: A240920: Prime numbers that occur as divisors of numbers of the form m^2 + 5.
-- Upstream: formal-conjectures statements/oeis-a240920.lean:0 (declaration OMA.S_oeis_a240920.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the tens digit of p is even iff p mod 20 < 10. The primes 2 and 5 are terms.
-- For an odd prime p other than 5, p divides some m^2 + 5 iff -5 is a square mod p, iff
-- legendreSym p (-5) = chi4(p) * legendreSym p 5 = chi4(p) * legendreSym 5 p = 1 (quadratic
-- reciprocity, 5 = 1 mod 4), and legendreSym 5 p = 1 iff p mod 5 is 1 or 4. Checking the
-- residues of p mod 20 gives the claim.

open OMA.S_oeis_a240920 in
theorem OMA.solution : type_of% @OMA.S_oeis_a240920.main := by
  intro p hp
  have hsq5 : ∀ r : ℕ, r < 5 → (IsSquare ((r : ℕ) : ZMod 5) ↔ (r = 0 ∨ r = 1 ∨ r = 4)) := by
    decide
  have key20 : ∀ r : ℕ, r < 20 → r % 5 ≠ 0 →
      ((r % 4 = 1 → ((r % 5 = 1 ∨ r % 5 = 4) ↔ r < 10)) ∧
        (r % 4 = 3 → (¬ (r % 5 = 1 ∨ r % 5 = 4) ↔ r < 10))) := by
    decide
  have arith : ∀ s : ℤ, (s = 1 ∨ s = -1) → (s = 1 ↔ (p % 5 = 1 ∨ p % 5 = 4)) → p % 5 ≠ 0 →
      ((p % 4 = 1 → (s = 1 ↔ p % 20 < 10)) ∧ (p % 4 = 3 → (-1 * s = 1 ↔ p % 20 < 10))) := by
    intro s h1 h2 h4
    have e : -1 * s = 1 ↔ ¬ s = 1 := by omega
    have hr5 : p % 20 % 5 = p % 5 := Nat.mod_mod_of_dvd p (by norm_num)
    have hr4 : p % 20 % 4 = p % 4 := Nat.mod_mod_of_dvd p (by norm_num)
    have hk := key20 (p % 20) (Nat.mod_lt p (by norm_num)) (by rw [hr5]; exact h4)
    rw [hr5, hr4] at hk
    constructor
    · intro h5
      rw [h2]
      exact hk.1 h5
    · intro h5
      rw [e, h2]
      exact hk.2 h5
  unfold IsTerm
  have hdig : Even (p / 10 % 10) ↔ p % 20 < 10 := by
    rw [Nat.even_iff]
    omega
  rw [hdig]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact ⟨fun _ => by norm_num, fun _ => ⟨Nat.prime_two, 1, by norm_num⟩⟩
  · by_cases hp5 : p = 5
    · subst hp5
      exact ⟨fun _ => by norm_num, fun _ => ⟨Nat.prime_five, 0, by norm_num⟩⟩
    · have := Fact.mk hp
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have : NeZero p := ⟨hp.ne_zero⟩
      have h2 : p % 2 = 1 := Nat.odd_iff.mp hodd
      have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      have hp2 : p ≠ 2 := by omega
      have hp5' : p % 5 ≠ 0 := by
        intro h
        have h5 : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
        exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h5).symm
      have hz5 : ((p : ℕ) : ZMod 5) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        omega
      have hs1 : legendreSym 5 p = 1 ∨ legendreSym 5 p = -1 :=
        legendreSym.eq_one_or_neg_one 5 (by exact_mod_cast hz5)
      have hs2 : legendreSym 5 p = 1 ↔ (p % 5 = 1 ∨ p % 5 = 4) := by
        rw [legendreSym.eq_one_iff' 5 hz5, ← ZMod.natCast_mod p 5,
          hsq5 (p % 5) (Nat.mod_lt p (by norm_num))]
        omega
      have hsq : (∃ m : ℕ, p ∣ m ^ 2 + 5) ↔ IsSquare ((-5 : ℤ) : ZMod p) := by
        constructor
        · rintro ⟨m, hm⟩
          have h0 : ((m ^ 2 + 5 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hm
          push_cast at h0
          refine ⟨(m : ZMod p), ?_⟩
          push_cast
          linear_combination -h0
        · rintro ⟨r, hr⟩
          refine ⟨r.val, ?_⟩
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, ZMod.natCast_zmod_val,
            Nat.cast_ofNat]
          push_cast at hr
          linear_combination -hr
      have hne : ((-5 : ℤ) : ZMod p) ≠ 0 := by
        rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro hd
        have h5 : (p : ℤ) ∣ 5 := dvd_neg.mp hd
        have h5' : p ∣ 5 := by exact_mod_cast h5
        exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5')
      have hqr : legendreSym p 5 = legendreSym 5 p := by
        have h := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hp2
        exact_mod_cast h
      have hleg : legendreSym p (-5) = ZMod.χ₄ p * legendreSym 5 p := by
        rw [legendreSym.at_neg hp2 5, hqr]
      rw [and_iff_right hp, hsq, ← legendreSym.eq_one_iff p hne]
      rcases hmod4 with h4 | h4
      · rw [hleg, ZMod.χ₄_nat_one_mod_four h4, one_mul]
        exact (arith _ hs1 hs2 hp5').1 h4
      · rw [hleg, ZMod.χ₄_nat_three_mod_four h4]
        exact (arith _ hs1 hs2 hp5').2 h4
