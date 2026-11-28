import Mathlib

/-!
# A139804: Smallest m such that (3^n)! + m is prime

Source: https://oeis.org/A139804

Conjecture (OEIS A139804):
There are no composite numbers in this sequence; that is, for every `n : ℕ`, the least
positive integer `m` such that `(3^n)! + m` is prime is either `1` or a prime number.

Conventions:
- Offset: `0`; first terms: `a(0) = 1`, `a(1) = 1`, `a(2) = 17`, `a(3) = 1`,
  `a(4) = 701`, `a(5) = 1367`, ...
- Minimality is expressed via a predicate `IsLeastValid` to avoid `Nat.find`.
- For `m ≥ 1`, being noncomposite is equivalent to `m = 1 ∨ Nat.Prime m`.
-/

namespace OMA.S_oeis_a139804

/-- Predicate stating that `m ≥ 1` and `(3^n)! + m` is prime. -/
def IsValid (n m : ℕ) : Prop :=
  1 ≤ m ∧ Nat.Prime ((3 ^ n).factorial + m)

/-- Predicate stating that `m = a(n)` is the least positive integer with `(3^n)! + m` prime
(OEIS A139804). -/
def IsLeastValid (n m : ℕ) : Prop :=
  IsValid n m ∧ ∀ j : ℕ, IsValid n j → m ≤ j

/-- Conjecture: every term of OEIS A139804 is either `1` or prime (no composite terms). -/
theorem main :
    ∀ n m : ℕ, IsLeastValid n m → m = 1 ∨ Nat.Prime m := by
  sorry

end OMA.S_oeis_a139804
