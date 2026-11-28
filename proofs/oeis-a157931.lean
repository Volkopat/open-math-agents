import OMAStatements.S_oeis_a157931

-- Problem: A157931: Numbers that are both the sum and the product of two primes.
-- Upstream: formal-conjectures statements/oeis-a157931.lean:0 (declaration OMA.S_oeis_a157931.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if an odd n = p + q with p, q prime, one of p, q is even, hence 2, and the other is
-- n - 2; conversely n = (n - 2) + 2. Under the Goldbach conjecture an even semiprime (>= 4) is a
-- sum of two primes, and p + 2 is one by definition.

open OMA.S_oeis_a157931 in
theorem OMA.solution : type_of% @OMA.S_oeis_a157931.main := by
  have hodd : ∀ n : ℕ, Odd n → (IsSumTwoPrimes n ↔ (n - 2).Prime) := by
    intro n hn
    constructor
    · rintro ⟨p, q, hp, hq, hpq⟩
      rcases hp.eq_two_or_odd' with h2 | hpo
      · rw [show n - 2 = q by omega]
        exact hq
      · rcases hq.eq_two_or_odd' with h2 | hqo
        · rw [show n - 2 = p by omega]
          exact hp
        · obtain ⟨a, ha⟩ := hpo
          obtain ⟨b, hb⟩ := hqo
          obtain ⟨c, hc⟩ := hn
          omega
    · intro h
      have h2 := h.two_le
      exact ⟨n - 2, 2, h, Nat.prime_two, by omega⟩
  refine ⟨hodd, ?_⟩
  intro hG n
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨hp, ?_⟩
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inl he
    · have h := (hodd n ho).mp hs
      have h2 := h.two_le
      exact Or.inr ⟨n - 2, h, by omega⟩
  · rintro ⟨hp, he | ⟨p, hpp, hn⟩⟩
    · have h4 : 4 ≤ n := by
        obtain ⟨p, q, hp1, hq1, hpq⟩ := hp
        have h := Nat.mul_le_mul hp1.two_le hq1.two_le
        omega
      exact ⟨hG n (by omega) he, hp⟩
    · exact ⟨⟨p, 2, hpp, Nat.prime_two, hn.symm⟩, hp⟩
