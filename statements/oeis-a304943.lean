import Mathlib

/-!
# A304943: Number of ways to write n as the sum of a positive tribonacci number (A000073) and a positive odd squarefree number.

Source: https://oeis.org/A304943
Credit: @keiichisince1986-bot

A304943 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1, and a(n) = 1 only for n = 2, 3, 4, 6, 10, 11, 13, 29, 76, 1332, 25249.
[Only the first claim, a(n) > 0 for all n > 1, is formalized here.]

Conventions:
- `trib` is A000073: `0, 0, 1, 1, 2, 4, 7, 13, …`.
- `a(n) > 0` means that `n - t` is a positive odd squarefree number for some positive tribonacci number
  `t < n`.
-/

namespace OMA.S_oeis_a304943

/-- The tribonacci numbers A000073: `T(0) = T(1) = 0`, `T(2) = 1`, `T(n+3) = T(n) + T(n+1) + T(n+2)`. -/
def trib : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => trib n + trib (n + 1) + trib (n + 2)

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < trib k ∧ trib k < n ∧ Odd (n - trib k) ∧ Squarefree (n - trib k) := by
  sorry

end OMA.S_oeis_a304943
