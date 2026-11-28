import Mathlib

/-!
# OEIS A238814: Primes p with prime(p)-p+1 and prime(q)-q+1 prime (q next prime)

Source: https://oeis.org/A238814
Credit: @unserus

OEIS: "Conjecture: The sequence is infinite, in other words, A234695 contains
infinitely many consecutive prime pairs prime(k) and prime(k+1)."

`prime(n)` is the `n`-th prime, 1-indexed (prime(1) = 2), which is
`Nat.nth Nat.Prime (n - 1)`. A prime `p` is in A234695 when `prime(p) - p + 1`
is prime (`prime(p) ≥ p`, so the subtraction does not truncate). The terms of
A238814 are the primes `p` such that `p` and the next prime `q` after `p` are
both in A234695. The conjecture is that there are infinitely many.
-/

namespace OMA.S_oeis_a238814

/-- `prime(n)`, 1-indexed. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `p` is in A234695: `prime(p) - p + 1` is prime. -/
def InA234695 (p : ℕ) : Prop := p.Prime ∧ (prime p - p + 1).Prime

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A238814. -/
def a238814Set : Set ℕ :=
  {p | InA234695 p ∧ ∃ q, IsNextPrime p q ∧ InA234695 q}

/-- A238814 is infinite. -/
theorem main : a238814Set.Infinite := by
  sorry

end OMA.S_oeis_a238814
