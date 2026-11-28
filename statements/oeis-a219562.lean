import Mathlib

/-!
# OEIS A219562: supercongruences for a(n) = Sum_{k=0..n} binomial(n+k,k)^4

Source: https://oeis.org/A219562 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

A219562: `a(n) = Sum_{k=0..n} binomial(n+k,k)^4` (offset 0: 1, 17, 1378, ...).
Peter Bala (Nov 29 2024) records two conjectures:
* `a(p-1) == 1 (mod p^5)` for every prime `p >= 7` (checked up to `p = 499`; Coster proved the
  congruence modulo `p^3` for `p >= 5`);
* for `r >= 2`, the supercongruence `a(p^r - 1) == a(p^(r-1) - 1) (mod p^(3*r+3))` holds for all
  primes `p >= 5` (Coster proved it modulo `p^(3*r)`).

Formalized: `main` is the conjunction of both conjectures, with `Nat.ModEq`.
-/

namespace OMA.S_oeis_a219562

/-- `a(n) = Sum_{k=0..n} binomial(n+k,k)^4`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + k) k) ^ 4

theorem main :
    (∀ p : ℕ, p.Prime → 7 ≤ p → a (p - 1) ≡ 1 [MOD p ^ 5]) ∧
    (∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r →
      a (p ^ r - 1) ≡ a (p ^ (r - 1) - 1) [MOD p ^ (3 * r + 3)]) := by
  sorry

end OMA.S_oeis_a219562
