import Mathlib

/-!
# A401759: a(n) = number of primes p <= n, taken in decreasing order starting from the largest, that must be tried before reaching the first one for which 2*n - p is also prime.

Source: https://oeis.org/A401759
Credit: @agchua

Comment of A401759 (unsigned; the entry is by Henry E. Rodriguez Vargas, Nov 04 2026):
  a(n) is defined for every n >= 2 if and only if the Goldbach conjecture holds, since a(n)
  exists exactly when 2*n is a sum of two primes. This equivalence is immediate.
The offset is 2. Trying the primes p <= n in decreasing order, the first one with 2*n - p prime is
the largest element P of the set good n below, and a(n) is the number of primes p with
P <= p <= n (so a(8) = 2: 7 fails, 5 works; a(49) = 4). When no prime p <= n has 2*n - p prime,
the search never stops and a(n) is not defined: a n = none. The Goldbach conjecture: every even
number greater than 2 is the sum of two primes. Both claims of the comment are stated.
-/

namespace OMA.S_oeis_a401759

/-- The primes p <= n for which 2*n - p is also prime. -/
def good (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (2 * n - p).Prime)

/-- A401759(n), with none when it is not defined: if good n is nonempty, with largest element P,
it is the number of primes p with P <= p <= n. -/
noncomputable def a (n : ℕ) : Option ℕ :=
  if h : (good n).Nonempty then
    some (((Finset.Icc ((good n).max' h) n).filter Nat.Prime).card)
  else none

/-- The Goldbach conjecture: every even number greater than 2 is the sum of two primes. -/
def Goldbach : Prop := ∀ m : ℕ, 2 < m → Even m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m

/-- The comment: a(n) is defined exactly when 2*n is a sum of two primes, and a(n) is defined for
every n >= 2 if and only if the Goldbach conjecture holds. -/
theorem main : (∀ n : ℕ, (∃ v, a n = some v) ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * n) ∧
    ((∀ n : ℕ, 2 ≤ n → ∃ v, a n = some v) ↔ Goldbach) := by
  sorry

end OMA.S_oeis_a401759
