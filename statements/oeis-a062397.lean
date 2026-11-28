import Mathlib

/-!
# A062397: a(n) = 10^n + 1

Source: https://oeis.org/A062397
Credit: @xor2k

The entry text is a remark, not a conjecture: By Mihăilescu's theorem, a(n) can never be a
perfect power (see Catalan's conjecture in Links). Formalized is exactly the claim made in that
remark: for every `n ≥ 0` (offset 0), `10^n + 1` is not a perfect power. The famous conjecture
(Catalan / Mihăilescu) itself is not formalized.

Conventions: a perfect power is a number of the form `m^k` with natural numbers `m` and `k ≥ 2`
(as in A001597).
-/

namespace OMA.S_oeis_a062397

/-- `a(n) = 10^n + 1`. -/
def a (n : ℕ) : ℕ :=
  10 ^ n + 1

/-- For every `n`, `a(n)` is not a perfect power `m^k` with `k ≥ 2`. -/
theorem main :
    ∀ n : ℕ, ¬ ∃ m k : ℕ, 2 ≤ k ∧ a n = m ^ k := by
  sorry

end OMA.S_oeis_a062397
