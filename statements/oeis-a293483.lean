import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a293483

/-- OEIS A293483: the number of 6th powers in the multiplicative group `(ℤ / nℤ)ˣ`. -/
noncomputable def a293483 (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun u : (ZMod n)ˣ => u ^ 6))

/-- OEIS A293483 conjecture: formulas for `a(p^e)` at prime powers `p^e`:
- `a(2^e) = 1` for `e ≤ 3` and `a(2^e) = 2^(e - 3)` for `e ≥ 3`;
- `a(3^e) = 1` for `e ≤ 2` and `a(3^e) = 3^(e - 2)` for `e ≥ 2`;
- `a(p^e) = (p - 1) * p^(e - 1) / 2` for primes `p ≡ 5 (mod 6)` and `e ≥ 1`;
- `a(p^e) = (p - 1) * p^(e - 1) / 6` for primes `p ≡ 1 (mod 6)` and `e ≥ 1`. -/
theorem main :
    (∀ e : ℕ, e ≤ 3 → a293483 (2 ^ e) = 1) ∧
    (∀ e : ℕ, 3 ≤ e → a293483 (2 ^ e) = 2 ^ (e - 3)) ∧
    (∀ e : ℕ, e ≤ 2 → a293483 (3 ^ e) = 1) ∧
    (∀ e : ℕ, 2 ≤ e → a293483 (3 ^ e) = 3 ^ (e - 2)) ∧
    (∀ p e : ℕ, p.Prime → 1 ≤ e → p % 6 = 5 →
      a293483 (p ^ e) = (p - 1) * p ^ (e - 1) / 2) ∧
    (∀ p e : ℕ, p.Prime → 1 ≤ e → p % 6 = 1 →
      a293483 (p ^ e) = (p - 1) * p ^ (e - 1) / 6) := by
  sorry

end OMA.S_oeis_a293483
