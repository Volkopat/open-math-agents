import Mathlib

/-!
# A237819: Number of primes p < n such that floor(sqrt(n-p)) is a Sophie Germain prime.

Source: https://oeis.org/A237819
Credit: @keiichisince1986-bot

A237819 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 5. [Further parts of the entry are not formalized here.]

Conventions:
- `floor(sqrt(m))` is `Nat.sqrt m`. A Sophie Germain prime is a prime `q` with `2q + 1` also prime.
- `a(n) > 0` means that for some prime `p < n`, `q = Nat.sqrt (n - p)` is a Sophie Germain prime.
-/

namespace OMA.S_oeis_a237819

theorem main :
    ∀ n : ℕ, 5 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n - p)).Prime ∧
      (2 * Nat.sqrt (n - p) + 1).Prime := by
  sorry

end OMA.S_oeis_a237819
