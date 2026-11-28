import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a052273

/-- OEIS A052273: the number of distinct 4th powers modulo `n`. -/
noncomputable def a052273 (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun x : ZMod n => x ^ 4))

/-- OEIS A052273 conjectures: formulas for `a(p^e)` at prime powers `p^e`:
1. `a(2^e) = 1 + 2^e / (2^4 - 1)` when `e % 4 = 0`,
   and `a(2^e) = 2 + 2^e / (2^4 - 1)` when `e % 4 ≠ 0`;
2. `a(p^e) = 1 + ((p - 1) * p^(e + 3)) / (Nat.gcd (p - 1) 4 * (p^4 - 1))`
   for every odd prime `p`. -/
theorem main :
    (∀ e : ℕ, e % 4 = 0 → a052273 (2 ^ e) = 1 + 2 ^ e / (2 ^ 4 - 1)) ∧
    (∀ e : ℕ, e % 4 ≠ 0 → a052273 (2 ^ e) = 2 + 2 ^ e / (2 ^ 4 - 1)) ∧
    (∀ p e : ℕ, p.Prime → p ≠ 2 →
      a052273 (p ^ e) = 1 + ((p - 1) * p ^ (e + 3)) / (Nat.gcd (p - 1) 4 * (p ^ 4 - 1))) := by
  sorry

end OMA.S_oeis_a052273
