import Mathlib

/-!
# A127925: Primes p such that 2p < prime(k-i) + prime(k+i) for i=1..k-1, where p=prime(k).

Source: https://oeis.org/A127925
Credit: @azmiozgen

Conjecture (Thomas Ordowski, from the entry): the terms are the numbers k > 1 for which
2*pi(k) = pi(k-m) + pi(k+m) has no solution 0 < m < k.

Formalization notes:
* prime(j) = `Nat.nth Nat.Prime (j - 1)` (prime(1) = 2); pi = `Nat.primeCounting`. A prime p is the
  k-th prime with k = pi(p), so membership is stated with the index pi(p).
* The conjecture is stated as an equivalence for every number q > 1: q is a term iff the equation
  has no solution 0 < m < q.
* Controls (computed): the terms with index < 2000 begin 3, 7, 19, 23, 43, 47, 73, 109, 113, 199,
  283, 293, 313, 317, 463, 467, 503, 509, 523, as in the entry, and the numbers q > 1 below
  prime(1999) without a solution are exactly these terms.
-/

namespace OMA.S_oeis_a127925

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `p` is a term of A127925. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∀ i : ℕ, 1 ≤ i → i < Nat.primeCounting p →
    2 * p < prime (Nat.primeCounting p - i) + prime (Nat.primeCounting p + i)

/-- Ordowski's conjecture. -/
theorem main :
    ∀ q : ℕ, 1 < q → (IsTerm q ↔
      ¬ ∃ m : ℕ, 0 < m ∧ m < q ∧
        2 * Nat.primeCounting q = Nat.primeCounting (q - m) + Nat.primeCounting (q + m)) := by
  sorry

end OMA.S_oeis_a127925
