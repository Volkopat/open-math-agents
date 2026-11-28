import Mathlib

/-!
# A362946: Positive integers that cannot be expressed as 1^e_1 + 2^e_2 + 3^e_3 ... + k^e_k with each exponent positive.

Source: https://oeis.org/A362946
Credit: @luciusacarr

The entry records one conjecture: this list is finite. Its known terms are 2, 4, 7, 11, 13, 19,
25, 31 (e.g. 1 = 1^1, 3 = 1^1 + 2^1, 20 = 1^1 + 2^4 + 3^1, 29 = 1^1 + 2^2 + 3^1 + 4^2 + 5^1).

Reading of the source:
* `n` is expressible if `n = ∑_{i=1}^{k} i^(e_i)` for some `k ≥ 1` and exponents `e_i ≥ 1`. The
  exponents are given as a function `e : ℕ → ℕ` that is positive everywhere (only `e 1, ..., e k`
  matter).
* The sequence is the set of positive integers that are not expressible; with this reading the
  terms up to 200 are exactly the listed ones.
-/

namespace OMA.S_oeis_a362946

/-- `n = 1^(e 1) + 2^(e 2) + ... + k^(e k)` for some `k ≥ 1` and positive exponents. -/
def IsExpressible (n : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ e : ℕ → ℕ, (∀ i, 1 ≤ e i) ∧ n = ∑ i ∈ Finset.Icc 1 k, i ^ (e i)

theorem main : {n : ℕ | 0 < n ∧ ¬ IsExpressible n}.Finite := by
  sorry

end OMA.S_oeis_a362946
