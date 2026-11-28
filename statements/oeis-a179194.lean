import Mathlib

/-!
# A179194: Bases n in which 1/(n-2) is non-terminating and has period n-3.

Source: https://oeis.org/A179194
Credit: @esracummings31-blip

Conjecture (Bill McEachen, Jun 11 2026): a(n) = A001122(n) + 2, where A001122 lists the
primes with primitive root 2.

Conventions.
* `digit b m k` is the (k+1)-st digit after the radix point of 1/m written in base b,
  namely floor(b^(k+1)/m) mod b.
* The expansion is non-terminating when infinitely many digits are nonzero.
* A period is a p > 0 such that the digit sequence satisfies d(k+p) = d(k) from some point on;
  "the period" is the least such p.
* Bases are n >= 3 (so that n - 2 >= 1 and the base is >= 2).
* Both sequences have offset 1 and list their terms in increasing order (`Nat.nth`).
  Whether A001122 is infinite is Artin's conjecture for 2 (open), so the identity is stated for
  every index n at which the n-th term of A001122 exists (`Nat.nth` returns 0 otherwise, and 0
  is not a term).
-/

namespace OMA.S_oeis_a179194

/-- The (k+1)-st digit after the radix point of 1/m in base b. -/
def digit (b m k : ℕ) : ℕ := b ^ (k + 1) / m % b

/-- The base-b expansion of 1/m does not terminate. -/
def NonTerminating (b m : ℕ) : Prop := ∀ K : ℕ, ∃ k, K ≤ k ∧ digit b m k ≠ 0

/-- p is an (eventual) period of the base-b digits of 1/m. -/
def IsPeriod (b m p : ℕ) : Prop :=
  0 < p ∧ ∃ K : ℕ, ∀ k, K ≤ k → digit b m (k + p) = digit b m k

/-- n is a term of A179194: in base n, 1/(n-2) is non-terminating and has period n-3. -/
def InSeq (n : ℕ) : Prop :=
  3 ≤ n ∧ NonTerminating n (n - 2) ∧ IsLeast {p | IsPeriod n (n - 2) p} (n - 3)

/-- A179194(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InSeq (n - 1)

/-- p is a prime with primitive root 2. -/
def PrimRoot2 (p : ℕ) : Prop := p.Prime ∧ orderOf (2 : ZMod p) = p - 1

/-- A001122(n), offset 1: primes with primitive root 2. -/
noncomputable def A001122 (n : ℕ) : ℕ := Nat.nth PrimRoot2 (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → A001122 n ≠ 0 → a n = A001122 n + 2 := by
  sorry

end OMA.S_oeis_a179194
