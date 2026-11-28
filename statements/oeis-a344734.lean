import Mathlib

/-!
# A344734: smallest divisibility checking number for the n-th number coprime to 10

Source: https://oeis.org/A344734 (conjecture of Chai Wah Wu, Dec 29 2021)

The divisibility checking number of a positive integer `m` coprime to 10 is the smallest
positive integer `x` such that `m` divides `10 * x + 1` (this is what the OEIS program
computes). `a(n)` is this number for the `n`-th positive integer coprime to 10
(offset 1, so the first such integer is 1).

Conjecture: `a(n) = 2 * a(n-4) - a(n-8)` for `n > 9`. The identity is stated over the
integers.
-/

namespace OMA.S_oeis_a344734

/-- The `n`-th positive integer coprime to 10 (1-indexed: `c 1 = 1`, `c 2 = 3`, ...). -/
noncomputable def c (n : ℕ) : ℕ := Nat.nth (fun k => Nat.Coprime k 10) (n - 1)

/-- The smallest positive `x` with `c n ∣ 10 * x + 1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {x : ℕ | 0 < x ∧ c n ∣ 10 * x + 1}

theorem main : ∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 4) - a (n - 8) := by
  sorry

end OMA.S_oeis_a344734
