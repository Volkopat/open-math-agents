import Mathlib

/-!
# A365965: Numbers k such that A139315(k) = 0 but k is not in A138511.

Source: https://oeis.org/A365965
Credit: @agchua

Comment of A365965 (J. Lowell, Sep 27 2025):
  Conjecture: includes all numbers that are 4 times a prime number greater than 13. If true, 188
  would qualify for this sequence, but we don't know if any of 183-187 are in this sequence.
A139315(n) (offset 2) is the smallest integer k such that n*k is the smallest multiple of k with
twice as many divisors as k, or 0 if no such number is possible. The multiples of k are m*k with
m ≥ 1, and the number of divisors of N is the cardinality of Nat.divisors N. A138511 is the set of
semiprimes p*q (p, q prime) with p^2 < q. We state the first sentence of the comment: 4*p is a
term for every prime p > 13.
-/

namespace OMA.S_oeis_a365965

/-- n*k is the smallest multiple of k with twice as many divisors as k. -/
def LeastDoubling (n k : ℕ) : Prop :=
  (n * k).divisors.card = 2 * k.divisors.card ∧
    ∀ m : ℕ, 1 ≤ m → m < n → (m * k).divisors.card ≠ 2 * k.divisors.card

open Classical in
/-- A139315(n): the smallest k ≥ 1 such that n*k is the smallest multiple of k with twice as many
divisors as k, or 0 if there is no such k. -/
noncomputable def A139315 (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, 1 ≤ k ∧ LeastDoubling n k then Nat.find h else 0

/-- A138511: semiprimes p*q with p, q prime and p^2 < q. -/
def InA138511 (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ^ 2 < q ∧ n = p * q

/-- k is a term of A365965: A139315(k) = 0 and k is not in A138511. -/
def InSeq (k : ℕ) : Prop := A139315 k = 0 ∧ ¬ InA138511 k

/-- The comment's conjecture: 4*p is a term for every prime p > 13. -/
theorem main : ∀ p : ℕ, p.Prime → 13 < p → InSeq (4 * p) := by
  sorry

end OMA.S_oeis_a365965
