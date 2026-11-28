import Mathlib

/-!
# A327568: the exponent of GL(2, Z/p^e Z) is (p^2 - 1) p^e

Source: https://oeis.org/A327568 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A327568, offset 1: Exponent of the group GL(2, Z_n). Data
1, 6, 24, 12, 120, 24, 336, 24, 72, 120, 1320, 24, 2184, 336, 120, 48, 4896, 72, 6840, ...
Comment: The exponent of a finite group G is the least positive integer k such that x^k = e
for all x in G, where e is the identity of the group.

Formula section:
If gcd(m, n) = 1 then a(m*n) = lcm(a(m), a(n)).
Conjecture: a(p^e) = (p^2-1)*p^e for primes p. If this is true, then 24 divides a(n) for n > 2.

Formalization notes.
* GL(2, Z_n) is `GL (Fin 2) (ZMod n)`, the group of invertible 2 x 2 matrices over Z/nZ, and
  its exponent is `Monoid.exponent`.
* `main` states the conjecture for all primes p and all e >= 1. The data agree: a(2) = 6,
  a(4) = 12, a(8) = 24, a(3) = 24, a(9) = 72, a(5) = 120.
* The remark on the divisibility by 24 is a consequence of the conjecture and of the formula
  for coprime m, n; it is not stated here.
-/

namespace OMA.S_oeis_a327568

open Matrix

/-- The conjecture a(p^e) = (p^2 - 1) p^e for the exponent a(n) of the group GL(2, Z/nZ). -/
theorem main : ∀ p e : ℕ, p.Prime → 1 ≤ e →
    Monoid.exponent (GL (Fin 2) (ZMod (p ^ e))) = (p ^ 2 - 1) * p ^ e := by
  sorry

end OMA.S_oeis_a327568
