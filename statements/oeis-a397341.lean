import Mathlib

/-!
# A397341: a(1) = 1; for n > 1, a(n) is the concatenation of a(n-1) and the smallest prime p such that the concatenation a(n-1) | p is prime.

Source: https://oeis.org/A397341
Credit: @keiichisince1986-bot

A397341 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for all n. Equivalently, for every F >= 1, there is a prime p such that
F*10^d(p) + p is prime. [We formalize the equivalent form stated in the entry.]

Conventions:
- `d(p)` is the number of decimal digits of `p`: `(Nat.digits 10 p).length`.
-/

namespace OMA.S_oeis_a397341

theorem main :
    ∀ F : ℕ, 1 ≤ F → ∃ p : ℕ, p.Prime ∧ (F * 10 ^ (Nat.digits 10 p).length + p).Prime := by
  sorry

end OMA.S_oeis_a397341
