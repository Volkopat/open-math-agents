import Mathlib

/-!
# OEIS A385678

Source: https://oeis.org/A385678 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A385678(n), for `n ≥ 1`, is the least prime `p ≤ n^2 - 2 n + 4` such that the polynomial
`Sum_{k=1..n} phi(k) x^(n-k)` is irreducible modulo `p`, or `1` if no such `p` exists, where
`phi` is Euler's totient function (A000010).
Data (from n = 1): 1, 2, 3, 1, 1, 7, 31, 13, 67, 7, 67, 13, 53, 7, 11, 19, 101, 239, 37, 23, ...

Conjecture (from the sequence entry): a(n) > 1 for all n > 5.

So for every `n > 5` there is a prime `p ≤ n^2 - 2 n + 4` modulo which the polynomial is
irreducible, i.e. its image in `(ZMod p)[X]` is `Irreducible`. (For `n > 5`, `n^2 - 2 n + 4`
is computed without truncation in `ℕ`.)
-/

namespace OMA.S_oeis_a385678

open Polynomial

/-- `Sum_{k=1..n} phi(k) x^(n-k)` with coefficients reduced modulo `p`. -/
noncomputable def totientPoly (n p : ℕ) : (ZMod p)[X] :=
  ∑ k ∈ Finset.Icc 1 n, C ((Nat.totient k : ℕ) : ZMod p) * X ^ (n - k)

theorem main : ∀ n : ℕ, 5 < n →
    ∃ p : ℕ, p.Prime ∧ p ≤ n ^ 2 - 2 * n + 4 ∧ Irreducible (totientPoly n p) := by
  sorry

end OMA.S_oeis_a385678
