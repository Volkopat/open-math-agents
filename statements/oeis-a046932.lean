import Mathlib

/-!
# OEIS A046932: period of `xⁿ + x + 1` over GF(2), Bartholdi's conjecture

Source: https://oeis.org/A046932
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the period of `xⁿ + x + 1` over `GF(2)`: the least `m > 0` such that `xⁿ + x + 1`
divides `x^m + 1`. Conjectures (OEIS entry): `a(2^k - 1) = 2^(a(k)) - 1` (Bartholdi, 2000), and
more generally `a((2^(km) - 1)/(2^m - 1)) = (2^(a(k) m) - 1)/(2^m - 1)` (for `m = 1` this is
Bartholdi's conjecture).

Conventions:
* `n ≥ 2`, so `xⁿ + x + 1` has nonzero constant term and the period exists; in the conjectures
  `k ≥ 2` and `m ≥ 1`. `main` states the general conjecture together with Bartholdi's.
-/

namespace OMA.S_oeis_a046932

open Polynomial

/-- The period of `xⁿ + x + 1` over `GF(2)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (X ^ n + X + 1 : (ZMod 2)[X]) ∣ X ^ m + 1}

/-- Bartholdi's conjecture and its generalisation. -/
theorem main :
    (∀ k : ℕ, 2 ≤ k → a (2 ^ k - 1) = 2 ^ a k - 1) ∧
    (∀ k m : ℕ, 2 ≤ k → 1 ≤ m →
      a ((2 ^ (k * m) - 1) / (2 ^ m - 1)) = (2 ^ (a k * m) - 1) / (2 ^ m - 1)) := by
  sorry

end OMA.S_oeis_a046932
