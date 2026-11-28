import Mathlib

/-!
# A178307: Remove powers of 2 from A000069. Let b(n) be n-th term of the remaining sequence. Then a(n) is the least number m such that (b(n))^m is in A001969.

Source: https://oeis.org/A178307
Credit: @keiichisince1986-bot

A178307 is the sequence `a(n)` named in the title. The entry states:
Conjecture. For every n>=1, a(n) does exist.

Conventions:
- A000069 are the odious numbers (an odd number of `1`s in binary) and A001969 the evil numbers (an even
  number of `1`s); the number of binary `1`s of `x` is `(Nat.digits 2 x).sum`.
- `b` ranges over the odious numbers that are not powers of `2`; `a(n)` exists means that some power `b^m`
  (`m ≥ 1`) is evil.
-/

namespace OMA.S_oeis_a178307

theorem main :
    ∀ b : ℕ, Odd (Nat.digits 2 b).sum → (¬ ∃ j : ℕ, b = 2 ^ j) → ∃ m : ℕ, 1 ≤ m ∧ Even (Nat.digits 2 (b ^ m)).sum := by
  sorry

end OMA.S_oeis_a178307
