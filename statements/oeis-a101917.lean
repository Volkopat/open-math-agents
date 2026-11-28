import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A101917: Stephan's generating-function conjecture

Source: https://oeis.org/A101917 (OEIS Foundation, CC BY-SA 4.0).
Ralf Stephan proposed the rational generating function on May 17, 2007.
Johannes W. Meijer reported its first incorrect coefficient, at index 57.

The sequence begins at index zero. Its coefficients are computed by the
recurrence in the source, obtained by multiplying the defining equation
A(x) = 1 / (1 + x A(x^7)) by its denominator and taking coefficients at
each positive degree. At step n + 1, both indices in each product are at
most n, so the calculation uses the coefficients already stored.

Clearing the conjectured denominator preserves the power-series identity
because its constant coefficient is one.
-/

namespace OMA.S_oeis_a101917

def terms : ℕ → Array ℤ
  | 0 => #[1]
  | n + 1 =>
    let previous := terms n
    let sum := (List.range (n / 7 + 1)).foldl
      (fun acc k => acc + previous[k]! * previous[n - 7 * k]!) 0
    previous.push (-sum)

def a (n : ℕ) : ℤ := (terms n)[n]!

noncomputable def series : PowerSeries ℤ := PowerSeries.mk a

open PowerSeries in
theorem main : series * (1 + X + X^7) = 1 + X^7 := by
  sorry

end OMA.S_oeis_a101917
