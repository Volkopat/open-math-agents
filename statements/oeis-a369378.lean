import Mathlib

/-!
# A369378: a(n) is the smallest k such that 2^(2^n+1)-1 + 2^k is prime, or -1 if no such k exists.

Source: https://oeis.org/A369378
Credit: @bnb9001

Offset 0: 1, 2, 4, 16, 1968, 64, 64, ...

Conjecture: if n > 0, then 2^(2^n+1)-1 + 2^k is not prime for every k < 2^n (so a(n) >= 2^n).
-/

namespace OMA.S_oeis_a369378

/-- The conjecture: for `n > 0` and every `k < 2^n`, `2^(2^n+1) - 1 + 2^k` is not prime. -/
theorem main : ∀ n : ℕ, 0 < n → ∀ k : ℕ, k < 2 ^ n → ¬ Nat.Prime (2 ^ (2 ^ n + 1) - 1 + 2 ^ k) := by
  sorry

end OMA.S_oeis_a369378
