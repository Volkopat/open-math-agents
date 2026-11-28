import OMAStatements.S_oeis_a279884

-- Reduction oeis-a279884.R1 of the OEIS A279884 conjecture
-- ((n-1)^(n+1)+1 prime implies n prime).
-- Credit: @sntntHb
-- Sketch: write x = n - 1, so f n = x^(n+1) + 1. If n is composite, either
--  * n is even (n >= 4): then n+1 is odd, so x + 1 = n divides x^(n+1) + 1 (H1, elementary);
--  * n is odd and n+1 = 2^a * m with m > 1 odd: then x^(2^a) + 1 is a proper divisor
--    of x^(n+1) + 1 (H2, elementary);
--  * n + 1 = 2^k: then f n = (2^k - 2)^(2^k) + 1 is a generalized Fermat number
--    and no algebraic factorisation is available. This family is the open core (H3).
-- A computer check (gmpy2 probable-prime test) found no prime f(2^k - 1) with 2^k - 1
-- composite for k <= 12.

namespace OMA.R_oeis_a279884_R1

/-- Even composite indices: `n` divides `f n`. -/
def H1 : Prop := ∀ n : ℕ, 4 ≤ n → Even n → ¬ Nat.Prime (OMA.S_oeis_a279884.f n)

/-- Odd indices with `n + 1` not a power of two: `f n` has an algebraic factor. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → Odd n → (∀ k : ℕ, n + 1 ≠ 2 ^ k) →
    ¬ Nat.Prime (OMA.S_oeis_a279884.f n)

/-- The open core: composite Mersenne-type indices `2^k - 1`. -/
def H3 : Prop := ∀ k : ℕ, ¬ Nat.Prime (2 ^ k - 1) →
    ¬ Nat.Prime (OMA.S_oeis_a279884.f (2 ^ k - 1))

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a279884.main := by
  intro h1 h2 h3 n hn hp
  by_contra hn'
  rcases Nat.even_or_odd n with he | ho
  · have h4 : 4 ≤ n := by
      obtain ⟨k, rfl⟩ := he
      have hk : k ≠ 1 := by
        rintro rfl
        exact hn' Nat.prime_two
      omega
    exact h1 n h4 he hp
  · by_cases hpow : ∃ k : ℕ, n + 1 = 2 ^ k
    · obtain ⟨k, hk⟩ := hpow
      have hn2 : n = 2 ^ k - 1 := by omega
      subst hn2
      exact h3 k hn' hp
    · exact h2 n hn ho (fun k hk => hpow ⟨k, hk⟩) hp

end OMA.R_oeis_a279884_R1
