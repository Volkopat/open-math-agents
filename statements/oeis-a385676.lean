import Mathlib

/-!
# OEIS A385676

Source: https://oeis.org/A385676 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A385676(n), for `n ≥ 1`, is the least prime `p ≤ 2 n^2 - n + 1` such that the polynomial
`Sum_{k=1..n} sigma(k) x^(n-k)` is irreducible modulo `p`, or `1` if no such `p` exists, where
`sigma` is the sum-of-divisors function (A000203).
Data (from n = 1): 1, 2, 3, 2, 1, 5, 11, 29, 2, 47, 5, 31, 13, 379, 37, ...

Conjecture (from the sequence entry): a(n) > 1 except for n = 1, 5.

So for every `n ≥ 1` other than `1` and `5` there is a prime `p ≤ 2 n^2 - n + 1` modulo which the
polynomial is irreducible, i.e. its image in `(ZMod p)[X]` is `Irreducible`.
-/

namespace OMA.S_oeis_a385676

open Polynomial

/-- `Sum_{k=1..n} sigma(k) x^(n-k)` with coefficients reduced modulo `p`. -/
noncomputable def sigmaPoly (n p : ℕ) : (ZMod p)[X] :=
  ∑ k ∈ Finset.Icc 1 n, C ((ArithmeticFunction.sigma 1 k : ℕ) : ZMod p) * X ^ (n - k)

theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 1 → n ≠ 5 →
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 * n ^ 2 - n + 1 ∧ Irreducible (sigmaPoly n p) := by
  sorry

end OMA.S_oeis_a385676
