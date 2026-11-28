import Mathlib

/-!
# A257310: Numbers n such that the decimal expansions of both n and n^2 have 2 as smallest digit and 5 as largest digit.

Source: https://oeis.org/A257310
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A257310 (Felix Fröhlich, Apr 20 2015): a(n) =
A137066(n+2) for all n, i.e., this is A137066 without the initial two terms.

Conventions:
* The sequence has offset 1 (data 235, 2335, 23335, 233335, 2333335, 2354235, 23333335, 233333335,
  2333333335, 2333524235, 23333333335, 23333524235, ...).
* `D m` says that the decimal expansion of m has 2 as smallest digit and 5 as largest digit: all
  digits of `Nat.digits 10 m` lie between 2 and 5 and both 2 and 5 occur. The terms of this
  sequence are the n with `D n` and `D (n^2)` (predicate `P`).
* A137066 is the sequence of positive integers k such that k and k^2 use only the digits 2, 3, 4
  and 5 (predicate `Q`).
* a(n) is `Nat.nth P (n - 1)` and A137066(n+2) is `Nat.nth Q (n + 1)` (`Nat.nth` is 0-indexed;
  both sequences have offset 1). The statement is for all n >= 1.
-/

namespace OMA.S_oeis_a257310

/-- The decimal expansion of m has 2 as smallest digit and 5 as largest digit. -/
def D (m : ℕ) : Prop :=
  (∀ d ∈ Nat.digits 10 m, 2 ≤ d ∧ d ≤ 5) ∧ 2 ∈ Nat.digits 10 m ∧ 5 ∈ Nat.digits 10 m

/-- n is a term of A257310. -/
def P (n : ℕ) : Prop := D n ∧ D (n ^ 2)

/-- k is a term of A137066: k > 0 and k and k^2 use only the digits 2, 3, 4, 5. -/
def Q (k : ℕ) : Prop :=
  0 < k ∧ (∀ d ∈ Nat.digits 10 k, 2 ≤ d ∧ d ≤ 5) ∧ ∀ d ∈ Nat.digits 10 (k ^ 2), 2 ≤ d ∧ d ≤ 5

/-- The conjecture recorded in A257310. -/
theorem main : ∀ n : ℕ, 0 < n → Nat.nth P (n - 1) = Nat.nth Q (n + 1) := by
  sorry

end OMA.S_oeis_a257310
