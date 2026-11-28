import Mathlib

/-!
# OEIS A354682: Interprimes that are products of two successive primes

Source: https://oeis.org/A354682
Credit: @unserus

OEIS: "Includes p*(p+2) where p, p+2,p^2+2*p-6 and p^2+2*p+6 are all primes but
p^2+2*p-2, p^2+2*p-4, p^2+2*p+2 and p^2+2*p+4 are composite. The Generalized
Bunyakovsky Conjecture implies there are infinitely many such terms."

An interprime is the average `(a + b) / 2` of two successive primes `a < b`,
written `a + b = 2 * m`. The terms are the `m` that are interprimes and also
products `s * t` of a prime `s` and the next prime `t` after it. The open
statement is that the sequence is infinite.
-/

namespace OMA.S_oeis_a354682

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A354682. -/
def a354682Set : Set ℕ :=
  {m | (∃ a b, a.Prime ∧ IsNextPrime a b ∧ a + b = 2 * m) ∧
    ∃ s t, s.Prime ∧ IsNextPrime s t ∧ m = s * t}

/-- A354682 is infinite. -/
theorem main : a354682Set.Infinite := by
  sorry

end OMA.S_oeis_a354682
