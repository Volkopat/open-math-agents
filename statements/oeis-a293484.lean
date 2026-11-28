import Mathlib

/-!
# A293484: The number of 7th powers in the multiplicative group modulo n

Source: https://oeis.org/A293484 (conjecture in the formula section of the entry)

Conjecture: a(2^e) = 1 for e <= 1; a(2^e) = 2^(e-1) for e >= 1; a(7^e) = 6 for e=1;
a(7^e) = 6*7^(e-2) for e >= 2; a(p^e) = (p-1)*p^(e-1) for p == {2,3,4,5,6} (mod 7);
a(p^e) = (p-1)*p^(e-1)/7 for p == 1 (mod 7).

Conventions:
* `a n` (offset 1) is the number of elements of the unit group `(ZMod n)ˣ` that are 7th powers
  of units, i.e. the cardinality of the image of x ↦ x^7 on `(ZMod n)ˣ`.
* In the last two clauses p is a prime and e >= 1 (a prime power p^e with e >= 1; for e = 0
  the right-hand sides are not meant). The division by 7 is exact there.
-/

namespace OMA.S_oeis_a293484

/-- A293484(n): the number of 7th powers in the multiplicative group modulo n. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Set.range fun x : (ZMod n)ˣ => x ^ 7)

theorem main :
    (∀ e : ℕ, e ≤ 1 → a (2 ^ e) = 1) ∧
    (∀ e : ℕ, 1 ≤ e → a (2 ^ e) = 2 ^ (e - 1)) ∧
    a (7 ^ 1) = 6 ∧
    (∀ e : ℕ, 2 ≤ e → a (7 ^ e) = 6 * 7 ^ (e - 2)) ∧
    (∀ p e : ℕ, p.Prime →
      (p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6) → 1 ≤ e →
      a (p ^ e) = (p - 1) * p ^ (e - 1)) ∧
    (∀ p e : ℕ, p.Prime → p % 7 = 1 → 1 ≤ e → a (p ^ e) = (p - 1) * p ^ (e - 1) / 7) := by
  sorry

end OMA.S_oeis_a293484
