import Mathlib

/-!
# A100311: Modulo 2 binomial transform of 8^n

Source: https://oeis.org/A100311
Credit: @jagong-cmu

Formalizes Alex Ratushnyak's OEIS A100311 conjecture (Apr 22 2012), offset 0:
`a(0)=1, a(n+1) = (a(n)*8) XOR a(n), where XOR is the bitwise exclusive-or operator`.

Conventions:
* The sequence is the OEIS formula for the modulo 2 binomial transform of `8^n`:
  `a(n) = Sum_{k=0..n} (binomial(n, k) mod 2)*8^k`, as a natural number.
* `^^^` is the bitwise exclusive-or on `ℕ` (`Nat.xor`).
* The claim is stated for every `n >= 0` (the offset is 0), together with `a(0) = 1`.
-/

namespace OMA.S_oeis_a100311

/-- `a(n) = Sum_{k=0..n} (binomial(n, k) mod 2) * 8^k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k % 2) * 8 ^ k

/-- `a(0) = 1` and, for every `n >= 0`, `a(n+1) = (a(n)*8) XOR a(n)`. -/
theorem main : a 0 = 1 ∧ ∀ n : ℕ, a (n + 1) = (a n * 8) ^^^ a n := by
  sorry

end OMA.S_oeis_a100311
