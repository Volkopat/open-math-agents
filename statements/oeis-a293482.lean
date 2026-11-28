import Mathlib

/-!
# A293482: The number of 5th powers in the multiplicative group modulo n

Source: https://oeis.org/A293482 (conjecture in the formula section of the entry)

Conjecture: a(2^e) = 1 for e <= 1; a(2^e) = 2^(e-1) for e >= 1; a(5)=4; a(5^e) = 4*5^(e-2)
for e > 1; a(p^e) = (p-1)*p^(e-1) for p == {2,3,4} (mod 5); a(p^e) = (p-1)*p^(e-1)/5 for
p == 1 (mod 5).

Conventions:
* `a n` (offset 1) is the number of elements of the unit group `(ZMod n)ˣ` that are 5th powers
  of units, i.e. the cardinality of the image of x ↦ x^5 on `(ZMod n)ˣ`.
* In the last two clauses p is a prime and e >= 1 (a prime power p^e with e >= 1; for e = 0
  the right-hand sides are not meant). The division by 5 is exact there.
-/

namespace OMA.S_oeis_a293482

/-- A293482(n): the number of 5th powers in the multiplicative group modulo n. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Set.range fun x : (ZMod n)ˣ => x ^ 5)

theorem main :
    (∀ e : ℕ, e ≤ 1 → a (2 ^ e) = 1) ∧
    (∀ e : ℕ, 1 ≤ e → a (2 ^ e) = 2 ^ (e - 1)) ∧
    a 5 = 4 ∧
    (∀ e : ℕ, 1 < e → a (5 ^ e) = 4 * 5 ^ (e - 2)) ∧
    (∀ p e : ℕ, p.Prime → (p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4) → 1 ≤ e →
      a (p ^ e) = (p - 1) * p ^ (e - 1)) ∧
    (∀ p e : ℕ, p.Prime → p % 5 = 1 → 1 ≤ e → a (p ^ e) = (p - 1) * p ^ (e - 1) / 5) := by
  sorry

end OMA.S_oeis_a293482
