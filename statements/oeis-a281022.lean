import Mathlib

/-!
# A281022: Single (or isolated or non-twin) primes that are also safe primes.

Source: https://oeis.org/A281022
Credit: @eltociear

The source defines the sequence in its COMMENTS section:
  Primes p such that neither p - 2 nor p + 2 is prime while (p - 1) / 2 is prime.
and then states the open question:
  It is conjectured that there are infinitely many safe primes, but this is still unproved,
  so it is not known whether this sequence is infinite.

The statement below is that open question: the set of such primes is infinite. The conditions are
written exactly as the source words them. Subtraction is in Nat, where p - 2 saturates at 0 for
p <= 2 and 0 is not prime, so the truncation changes nothing: for p <= 2, p - 2 is not a prime
anyway. For the primes p the condition (p - 1) / 2 is an exact halving, since an odd p has p - 1
even, so Nat division is floor division without loss; the source's example p = 23 gives
(23 - 1) / 2 = 11, which is prime.
-/

namespace OMA.S_oeis_a281022

theorem main :
    ({p : ℕ | Nat.Prime p ∧ ¬ Nat.Prime (p - 2) ∧ ¬ Nat.Prime (p + 2) ∧
      Nat.Prime ((p - 1) / 2)}).Infinite := by
  sorry

end OMA.S_oeis_a281022
-- ci: re-run check-proof
