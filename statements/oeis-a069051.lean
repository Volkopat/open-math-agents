import Mathlib

/-!
# A069051: Primes p such that p-1 divides 2^p-2.

Source: https://oeis.org/A069051
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a069051

theorem main :
    (∀ n : ℕ, 1 < n → n - 1 ∣ 2 ^ n - 2 →
      Squarefree ((2 ^ n - 2) / (n - 1))) ∧
    ∀ n : ℕ, 1 < n →
      ((∀ b : ℤ, b ^ n ≡ b [ZMOD (((n - 1) * n : ℕ) : ℤ)]) ↔
        n = 2 ∨ n = 3 ∨ n = 7 ∨ n = 43) := by
  sorry

end OMA.S_oeis_a069051
