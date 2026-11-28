import Mathlib

/-!
# A325046: parity of the coefficients of a sum of binomial generating functions

Sources:
* OEIS Foundation, A325046, https://oeis.org/A325046.
* Sela Fried, Further proofs of conjectures from the OEIS, §3.8, Theorem 50,
  https://arxiv.org/html/2607.24832v1.

The ordinary generating function of A325046 is
∑_{n ≥ 0} X^n (1 + X^n)^n / (1 - X^(n+1))^(n+1).
By the binomial theorem, the coefficient of X^N is the sum of
choose(n,i) * choose(n+k,k) over n,i,k with i ≤ n and n*(i+1)+(n+1)*k = N.
This finite coefficient formula defines the sequence below. Each of its three
indices is at most N. The conjecture, proved in Fried's Theorem 50, is that the
coefficient is odd exactly at indices m*(m+1), with offset 0.
-/

namespace OMA.S_oeis_a325046

open Finset

/-- The triples that contribute to the coefficient of degree N. -/
def coefficientTerms (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (N + 1)) ×ˢ (range (N + 1)) ×ˢ (range (N + 1))).filter
    (fun t => t.2.1 ≤ t.1 ∧ t.1 * (t.2.1 + 1) + (t.1 + 1) * t.2.2 = N)

/-- The coefficient of degree N in the generating function for A325046. -/
def a (N : ℕ) : ℕ :=
  ∑ t ∈ coefficientTerms N, t.1.choose t.2.1 * (t.1 + t.2.2).choose t.2.2

theorem main : ∀ N : ℕ, Odd (a N) ↔ ∃ m : ℕ, N = m * (m + 1) := by
  sorry

end OMA.S_oeis_a325046
