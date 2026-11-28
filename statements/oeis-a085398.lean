import Mathlib

/-!
# A085398: Let Cn(x) be the n-th cyclotomic polynomial; a(n) is the least k>1 such that Cn(k) is prime.

Source: https://oeis.org/A085398
Credit: @keiichisince1986-bot

A085398 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) is defined for all n. - Eric Chen, Nov 14 2014

Conventions:
- `Cn(x)` is Mathlib's `Polynomial.cyclotomic n ℤ`; `Cn(k)` is its value at the integer `k`, and being prime
  is `Prime` in `ℤ` (for `k > 1` and `n ≥ 1` the value is positive, so this is the usual notion).
- The offset is `1`, so `n ≥ 1`.
-/

namespace OMA.S_oeis_a085398

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 < k ∧ Prime ((Polynomial.cyclotomic n ℤ).eval (k : ℤ)) := by
  sorry

end OMA.S_oeis_a085398
