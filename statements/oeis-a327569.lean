import Mathlib

/-!
# A327569: exponent of the group SL(2, Z_n)

Source: https://oeis.org/A327569 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A327569 (Jianing Song, Sep 17 2019), offset 1: exponent of the group SL(2, Z_n). Data
1, 6, 12, 12, 60, 12, 168, 24, 36, 60, 660, 12, 1092, 168, 60, 48, 2448, 36, 3420, 60, ...
The exponent of a finite group G is the least positive integer k such that x^k = e for all x
in G.

Formula section: Conjecture: a(p^e) = (p^2-1)*p^e/2 for primes p > 2 and 3*2^e for p = 2.
If this is true, then 12 divides a(n) for n > 2.

Formalization notes.
* SL(2, Z_n) is `Matrix.SpecialLinearGroup (Fin 2) (ZMod n)` and its exponent is
  `Monoid.exponent`.
* `main` is the conjecture: for each odd prime p and each e >= 1 the exponent of
  SL(2, Z_(p^e)) is (p^2 - 1) * p^e / 2 (the natural division is exact), and for each e >= 1
  the exponent of SL(2, Z_(2^e)) is 3 * 2^e. The last sentence of the comment is a consequence
  (with the formula a(m*n) = lcm(a(m), a(n)) of the entry) and is not a part of the statement.
-/

namespace OMA.S_oeis_a327569

/-- The exponent of SL(2, Z/p^e) is (p^2 - 1) p^e / 2 for an odd prime p, and 3 * 2^e for
p = 2. -/
theorem main :
    (∀ p e : ℕ, p.Prime → 2 < p → 0 < e →
      Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ e))) = (p ^ 2 - 1) * p ^ e / 2) ∧
    (∀ e : ℕ, 0 < e →
      Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ e))) = 3 * 2 ^ e) := by
  sorry

end OMA.S_oeis_a327569
