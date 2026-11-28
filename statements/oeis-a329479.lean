import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


/-!
# OEIS A329479

Source: https://oeis.org/A329479
Credit: @etaubman

A monic polynomial of degree n+1 with coefficients in {0,1}, and constant
coefficient zero, is uniquely specified by its n intervening coefficients,
in descending order. `evalBits` evaluates those coefficients by Horner's rule,
starting with the leading coefficient 1; multiplication by x supplies the
constant coefficient zero. Any polynomial counted by the OEIS definition has
constant coefficient zero, since its value at zero is divisible by three.
It suffices to evaluate in ZMod 3, since evaluation commutes with reduction.

The integer-valued count below is the sum of one indicator for each such word.
The theorem is precisely the conjectured eighth-order recurrence, shifted to
avoid truncated subtraction of indices. The sequence has offset one, so the
first recurrence whose eight earlier indices are all in its domain is n = 9.
The auxiliary value at zero is not used in the theorem.
-/

namespace OMA.S_oeis_a329479

open Finset

def bit (b : Bool) : ZMod 3 := if b then 1 else 0

def evalBits (l : List Bool) (x s : ZMod 3) : ZMod 3 :=
  l.foldl (fun a b => x * a + bit b) s

def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ∑ w : Fin n → Bool,
      if ∀ x : ZMod 3, x * evalBits (List.ofFn w) x 1 = 0 then 1 else 0

theorem main : ∀ n : ℕ,
    a (n + 9) = 2 * a (n + 8) + 2 * a (n + 7) - 5 * a (n + 6) -
      2 * a (n + 5) + 10 * a (n + 4) - 4 * a (n + 3) -
      4 * a (n + 2) + 8 * a (n + 1)  := by
  sorry

end OMA.S_oeis_a329479
