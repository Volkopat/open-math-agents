import OMAReductions.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1

-- Step CunninghamChain.infinitely_many_firstKind_chains.R1.H2.R1.H2: hypothesis H2 of reduction CunninghamChain.infinitely_many_firstKind_chains.R1.H2.R1
-- Credit: @luciusacarr
-- H2 := ∀ p : ℕ, ∃ j : ℕ, ¬ (firstKindTerm p j).Prime

/-! A nonprime start fails at `j = 0`. For an odd prime `p`, the term `t` at `j = p - 1`
satisfies `t + 1 = 2^(p-1) (p+1) ≡ 1 (mod p)` by Fermat, so `p ∣ t` while `t > p`.
For `p = 2` the chain is `2, 5, 11, 23, 47, 95`. -/

theorem OMA.solution : OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1.H2 := by
  intro p
  by_cases hp : p.Prime
  · by_cases h2 : p = 2
    · subst h2
      refine ⟨5, ?_⟩
      have h := OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1.firstKindTerm_add_one 2 5
      have h95 : CunninghamChain.firstKindTerm 2 5 = 95 := by norm_num at h; omega
      rw [h95]
      norm_num
    · refine ⟨p - 1, fun ht => ?_⟩
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hclosed :=
        OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1.firstKindTerm_add_one p (p - 1)
      set t := CunninghamChain.firstKindTerm p (p - 1) with htdef
      have := Fact.mk hp
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [CharP.cast_eq_zero_iff (ZMod p) p] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      have hfer : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
      have hz : ((t + 1 : ℕ) : ZMod p) = 1 := by
        rw [hclosed]
        push_cast
        rw [hfer, ZMod.natCast_self]
        ring
      have ht0 : ((t : ℕ) : ZMod p) = 0 := by
        push_cast at hz
        linear_combination hz
      rw [CharP.cast_eq_zero_iff (ZMod p) p] at ht0
      have heq : p = t := (Nat.prime_dvd_prime_iff_eq hp ht).mp ht0
      have hpow : 4 ≤ 2 ^ (p - 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 4 * (p + 1) ≤ 2 ^ (p - 1) * (p + 1) := Nat.mul_le_mul_right _ hpow
      omega
  · exact ⟨0, hp⟩
