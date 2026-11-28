import Mathlib

/-!
# A308623: Number of ways to write n as a*(a+1)/2 + b*(b+1)/2 + 2^c*10^(2d) with a,b,c,d nonnegative integers.

Source: https://oeis.org/A308623
Credit: @keiichisince1986-bot

A308623 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `a(n) > 0` means that there is at least one such representation, with `a, b, c, d` natural
  numbers. (The data count the representations with `a ≤ b`; this does not affect whether one
  exists.)
- `a * (a + 1) / 2` is the triangular number `T(a)`; `a (a + 1)` is even, so the division in
  `ℕ` is exact.
-/

namespace OMA.S_oeis_a308623

theorem main :
    ∀ n : ℕ, 0 < n → ∃ a b c d : ℕ, n = a * (a + 1) / 2 + b * (b + 1) / 2 + 2 ^ c * 10 ^ (2 * d) := by
  sorry

end OMA.S_oeis_a308623
