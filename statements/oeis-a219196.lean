import Mathlib

/-!
# A219196: a subsequence of the denominators of the Bernoulli numbers

Source: https://oeis.org/A219196 (conjecture in the entry's comments, 2012)

`a(n) = A027642(A131577(n))` (offset 0), where A131577 is zero followed by the powers of 2,
i.e. `A131577(0) = 0` and `A131577(n) = 2^(n-1)` for `n >= 1`, and A027642(m) is the
denominator of the Bernoulli number B_m. Mathlib's `bernoulli` uses B_1 = -1/2; the sign
convention for B_1 does not affect any denominator.

The conjecture: a(15) = a(16) = 131070, and a(17) through a(32) are all 8589934590.
-/

namespace OMA.S_oeis_a219196

/-- A131577: zero followed by the powers of 2. -/
def A131577 (n : ℕ) : ℕ := if n = 0 then 0 else 2 ^ (n - 1)

/-- A027642: denominator of the Bernoulli number `B_n`. -/
noncomputable def A027642 (n : ℕ) : ℕ := (bernoulli n).den

/-- The sequence A219196. -/
noncomputable def a (n : ℕ) : ℕ := A027642 (A131577 n)

theorem main : a 15 = 131070 ∧ a 16 = 131070 ∧
    ∀ n : ℕ, 17 ≤ n → n ≤ 32 → a n = 8589934590 := by
  sorry

end OMA.S_oeis_a219196
