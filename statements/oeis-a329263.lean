import Mathlib

/-!
# A329263: Irregular triangle read by rows in which row n is the result of iterating the operation f(n) = n/8 if n == 0 (mod 8), otherwise f(n) = 8*(floor(n/8) + n + 1), terminating at the first occurrence of 1.

Source: https://oeis.org/A329263
Credit: @keiichisince1986-bot

A329263 is the sequence `a(n)` named in the title. The entry states:
Conjecture: For any initial value of n >= 1 there is a number k such that f^{k}(n) = 1; in other
words, every row of the triangle is finite.

Conventions:
- `floor(n/8)` is natural-number division `n / 8`.
-/

namespace OMA.S_oeis_a329263

/-- `f(n) = n/8` if `8 ∣ n`, otherwise `8 (⌊n/8⌋ + n + 1)`. -/
def f (n : ℕ) : ℕ := if n % 8 = 0 then n / 8 else 8 * (n / 8 + n + 1)

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, f^[k] n = 1 := by
  sorry

end OMA.S_oeis_a329263
