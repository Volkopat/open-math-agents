import Mathlib

/-!
# A347365: a(n) = n * (2-(-1)^n)

Source: https://oeis.org/A347365
Credit: @xor2k

Formalizes the OEIS A347365 comment (offset 0): a(6n+1)/3 = 6n+1, and a(6n+5)/3 = 6n+5,
related to Collatz Conjecture.

Conventions: the sequence is defined over the integers, `a n = n * (2 - (-1)^n)` for `n : ℕ`
(offset 0, so `n` ranges over all natural numbers). The division `/ 3` is integer division in `ℤ`;
both claims are stated for every `n : ℕ`.
-/

namespace OMA.S_oeis_a347365

/-- `a(n) = n * (2 - (-1)^n)`, as an integer. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * (2 - (-1) ^ n)

/-- For every `n ≥ 0`: `a(6n+1)/3 = 6n+1` and `a(6n+5)/3 = 6n+5`. -/
theorem main :
    ∀ n : ℕ, a (6 * n + 1) / 3 = 6 * (n : ℤ) + 1 ∧ a (6 * n + 5) / 3 = 6 * (n : ℤ) + 5 := by
  sorry

end OMA.S_oeis_a347365
