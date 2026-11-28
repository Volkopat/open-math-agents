import Mathlib.Data.Nat.Nth
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Barker's base-six square-truncation conjecture

Source: https://oeis.org/A204573, Colin Barker, September 20, 2014.
Credit: @NOELOO6

Scan integers x in increasing order beginning with 0. When floor(x²/6) is a
square, output that square. Distinct x can yield the same output. This gives
the OEIS multiplicities and its one-based offset, with three initial zeros.
The value assigned at index zero pads the ordinary generating function.
-/

namespace OMA.S_oeis_a204573
open PowerSeries

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (Nat.nth (fun x => IsSquare (x^2 / 6)) (n-1))^2 / 6

theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 99 * a (n-3) - 99 * a (n-6) + a (n-9)) ∧
    (1 - 99*X^3 + 99*X^6 - X^9) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X^4 * (X^6 + 16*X^5 + 4*X^4 + 22*X^3 + 16*X^2 + 4*X + 1) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a204573
