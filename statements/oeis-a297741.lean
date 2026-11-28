import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Int.Defs

/-!
# The ball of the (3,4)-leaper on the infinite chessboard

A297741 counts distinct endpoints after at most n moves, starting with one
square for n=0. The generating function is stated coefficientwise after
multiplication by (1-x)^3. The quadratic, numerator and recurrence below
are the three assertions printed in the entry.

Source: https://oeis.org/A297741
Credit: @wtho704
-/

namespace OMA.S_oeis_a297741

abbrev Point := ℤ × ℤ

/-- The eight signed and permuted (3,4) jumps in counterclockwise order. -/
def step (i : Fin 8) : Point :=
  match i.val with
  | 0 => (4,-3)
  | 1 => (4,3)
  | 2 => (3,4)
  | 3 => (-3,4)
  | 4 => (-4,3)
  | 5 => (-4,-3)
  | 6 => (-3,-4)
  | _ => (3,-4)

def ball : ℕ → Finset Point
  | 0 => {(0,0)}
  | n+1 => (ball n) ∪ Finset.univ.biUnion (fun i : Fin 8 => (ball n).image fun p => p + step i)

def a (n : ℕ) : ℕ := (ball n).card

def coefficient (j : ℤ) : ℤ := if j < 0 then 0 else (a j.toNat : ℤ)

def numerator : ℕ → ℤ
  | 0 => 1
  | 1 => 6
  | 2 => 17
  | 3 => 32
  | 4 => 48
  | 5 => 64
  | 6 => 80
  | 7 => -24
  | 8 => -96
  | 9 => -48
  | 10 => -8
  | 11 => 28
  | 12 => 20
  | 13 => 4
  | _ => 0

theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 62 * (n : ℤ)^2 + 30 * n - 55) ∧
    (∀ n : ℕ, coefficient n - 3 * coefficient (n - 1 : ℤ) + 3 * coefficient (n - 2 : ℤ) -
      coefficient (n - 3 : ℤ) = numerator n) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 3 * (a (n-1) : ℤ) - 3 * (a (n-2) : ℤ) + a (n-3) := by
  sorry

end OMA.S_oeis_a297741
