import Mathlib

/-!
# A248124: Least integer m > 0 such that gcd(m,n) = 1 and (m+n) | (C(m)+C(n)), where C(k) refers to the k-th Catalan number, binomial(2k,k)/(k+1).

Source: https://oeis.org/A248124
Credit: @keiichisince1986-bot

A248124 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for all n > 3.

Conventions:
- `C(k)` is Mathlib's `catalan k`.
-/

namespace OMA.S_oeis_a248124

theorem main :
    ∀ n : ℕ, 3 < n → ∃ m : ℕ, 0 < m ∧ Nat.Coprime m n ∧ m + n ∣ catalan m + catalan n := by
  sorry

end OMA.S_oeis_a248124
