import OMAStatements.S_oeis_a176997

-- Problem oeis-a176997: the positive integers k with 2^(k-1) = 1 (mod k) are exactly 1, the odd primes and the
-- Fermat pseudoprimes to base 2; equivalently, the union of A006005 (1 and the odd primes) and the pseudoprimes.
-- Upstream: statements/oeis-a176997.lean (declaration OMA.S_oeis_a176997.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let k > 0 with 2^(k-1) = 1 (mod k). If k = 1 we are done. If k is prime it cannot be 2 (2 does not
-- divide 2^1 - 1), so it is an odd prime. Otherwise k is composite, k > 1 and k divides 2^(k-1) - 1, which is the
-- definition of a Fermat pseudoprime to base 2. Conversely 1 satisfies the congruence trivially, an odd prime
-- satisfies it by Fermat's little theorem (2 is coprime to it), and a pseudoprime satisfies it by definition.
-- The second identity is the first one with {1} and the odd primes regrouped.

open OMA.S_oeis_a176997

private lemma mem_iff_a176997 (k : ℕ) :
    k ∈ A176997 ↔ k = 1 ∨ (k.Prime ∧ Odd k) ∨ Nat.FermatPsp k 2 := by
  simp only [A176997, Set.mem_setOf_eq]
  have hpow : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  constructor
  · rintro ⟨hk0, hk⟩
    by_cases h1 : k = 1
    · exact Or.inl h1
    have hk1 : 1 < k := by omega
    have hdvd : k ∣ 2 ^ (k - 1) - 1 := (Nat.modEq_iff_dvd' hpow).mp hk.symm
    by_cases hp : k.Prime
    · refine Or.inr (Or.inl ⟨hp, ?_⟩)
      rcases hp.eq_two_or_odd' with h2 | hodd
      · rw [h2] at hdvd
        norm_num at hdvd
      · exact hodd
    · exact Or.inr (Or.inr (show Nat.ProbablePrime k 2 ∧ ¬k.Prime ∧ 1 < k from ⟨hdvd, hp, hk1⟩))
  · rintro (h1 | ⟨hp, hodd⟩ | ⟨hpp, hnp, hk1⟩)
    · subst h1
      exact ⟨one_pos, Nat.modEq_one⟩
    · refine ⟨hp.pos, ?_⟩
      have hcop : Nat.Coprime 2 k := Nat.coprime_two_left.mpr hodd
      have h := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hp] at h
    · have hd : k ∣ 2 ^ (k - 1) - 1 := hpp
      exact ⟨by omega, ((Nat.modEq_iff_dvd' hpow).mpr hd).symm⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a176997.main := by
  refine ⟨?_, ?_⟩
  · ext k
    rw [mem_iff_a176997]
    simp only [Set.mem_union, Set.mem_singleton_iff, A065091, A001567, Set.mem_setOf_eq]
    tauto
  · ext k
    rw [mem_iff_a176997]
    simp only [Set.mem_union, A006005, A001567, Set.mem_setOf_eq]
    constructor
    · rintro (h1 | ⟨hp, hodd⟩ | h)
      · exact Or.inl ⟨h1 ▸ odd_one, Or.inl h1⟩
      · exact Or.inl ⟨hodd, Or.inr hp⟩
      · exact Or.inr h
    · rintro (⟨hodd, h1 | hp⟩ | h)
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨hp, hodd⟩)
      · exact Or.inr (Or.inr h)
