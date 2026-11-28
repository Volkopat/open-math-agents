import Mathlib

/-!
# A267824: composite n with C(2n-1, n-1) ≡ 1 (mod n^2) are squares of Wolstenholme primes

Source: https://oeis.org/A267824

A267824 (offset 1): the composite numbers `n` such that `binomial(2n-1, n-1) ≡ 1 (mod n^2)`:
283686649, 4514260853041, …  Here `283686649 = 16843^2` and `4514260853041 = 2124679^2` are
squares of Wolstenholme primes (A088164). The entry recalls that Babbage proved the congruence
for every prime `n > 2`.

Conjecture (Felix Fröhlich, Jan 27 2016; cf. McIntosh, 1995, p. 385): `n` is a term if and only
if `n = A088164(i)^2` for some `i ≥ 1`. The entry notes that the if-part is true (Jonathan
Sondow, Jan 28 2016, citing McIntosh).

Conventions:
- A composite number is an integer greater than `1` that is not prime.
- A Wolstenholme prime (A088164: 16843, 2124679, …) is a prime `p` such that
  `binomial(2p-1, p-1) ≡ 1 (mod p^4)`.
- The statement is: for every composite `n`, the congruence `C(2n-1, n-1) ≡ 1 (mod n^2)` holds
  if and only if `n` is the square of a Wolstenholme prime. Everything is in `ℕ`; the
  subtractions are exact for `n ≥ 1`.
-/

namespace OMA.S_oeis_a267824

/-- A Wolstenholme prime (A088164): a prime `p` with `binomial(2p-1, p-1) ≡ 1 (mod p^4)`. -/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

theorem main :
    ∀ n : ℕ, 1 < n → ¬ Nat.Prime n →
      ((2 * n - 1).choose (n - 1) ≡ 1 [MOD n ^ 2] ↔
        ∃ p : ℕ, IsWolstenholmePrime p ∧ n = p ^ 2) := by
  sorry

end OMA.S_oeis_a267824
