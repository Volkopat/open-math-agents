import Mathlib

/-!
# A330724: Sum of prime factors (with multiplicity) of the n-th composite number coprime to 6.

Source: https://oeis.org/A330724
Credit: @keiichisince1986-bot

A330724 is the sequence `a(n)` named in the title. The entry states:
I conjecture that all the odd numbers above 15 and all the even numbers above 10 will at least once show up in the sequence.

Conventions:
- The terms of the sequence are exactly the values `sopfr(k)` (A001414, the sum of the prime factors of `k`
  counted with multiplicity, here `k.primeFactorsList.sum`) for composite `k` coprime to `6` (A038509).
- A composite number is a `k` with `1 < k` that is not prime.
-/

namespace OMA.S_oeis_a330724

theorem main :
    ∀ m : ℕ, (Even m ∧ 10 < m) ∨ (Odd m ∧ 15 < m) →
      ∃ k : ℕ, 1 < k ∧ ¬ k.Prime ∧ Nat.Coprime k 6 ∧ k.primeFactorsList.sum = m := by
  sorry

end OMA.S_oeis_a330724
