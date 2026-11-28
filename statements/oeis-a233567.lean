import Mathlib

/-!
# A233567: Number of ways to write n = p + q (q > 0) with p and p^4 + phi(q)^4 both prime, where phi(.) is Euler's totient function (A000010).

Source: https://oeis.org/A233567
Credit: @keiichisince1986-bot

A233567 is the sequence `a(n)` named in the title. The entry states:
Conjecture: If n > 2 is not equal to 5, then we have a(n) > 0, also there is a prime p < n with
p^2 + phi(n-p)^2 prime.

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- Both assertions of the conjecture are formalized, under the same hypothesis `n > 2`, `n ≠ 5`.
-/

namespace OMA.S_oeis_a233567

theorem main :
    ∀ n : ℕ, 2 < n → n ≠ 5 →
      (∃ p q : ℕ, 0 < q ∧ p.Prime ∧ p + q = n ∧ (p ^ 4 + Nat.totient q ^ 4).Prime) ∧
      ∃ p : ℕ, p.Prime ∧ p < n ∧ (p ^ 2 + Nat.totient (n - p) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a233567
