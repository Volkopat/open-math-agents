import Mathlib

/-!
# A282124: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 430, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282124
Conjectures: Colin Barker, Feb 07 2017, and Paul Curtz, Jun 10 2019.
Formalization: @longling12 (drafted with AI assistance)

At stage zero only the origin is ON. Each integer lattice site uses bit c + 2s of Rule 430
with the four orthogonal neighbors. The positive x-axis is read in base two, origin first.
All sequences start at zero. The references use the Jacobsthal recurrence, the signed
power formula of A081631, and the trace of the Krawtchouk matrix specified in A098646.
-/

namespace OMA.S_oeis_a282124

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 430 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n (j : ℤ) 0).toNat : ℤ) * 2 ^ (n - j)

def a001045 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => a001045 (n+1) + 2*a001045 n

def a081631 (n : ℕ) : ℤ := 2*2^n - (-2)^n

def krawtchouk : Matrix (Fin 3) (Fin 3) ℤ := !![1,1,1; 2,0,-2; 1,-1,1]

def a098646 (n : ℕ) : ℤ := Matrix.trace (krawtchouk ^ n)

theorem main :
    (∀ n : ℕ, (a n : ℚ) = ((-1) + 2 * (-1) ^ n - (-1) ^ n * 2 ^ (1 + n) + 2 ^ (2 + n)) / 3) ∧
    (∀ n : ℕ, 3 < n → a n = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      (1 + 3 * X - 2 * X ^ 2 : PowerSeries ℤ)) ∧
    (∀ n : ℕ, a n = a001045 (n+1) * (if Even n then 1 else 3)) ∧
    (∀ n : ℕ, a (n+4) = a n + 10*a081631 n) ∧
    (∀ n : ℕ, a (2*n+1) = 2^(2*n+2)-1) ∧
    (∀ n : ℕ, a (n+2) = a n + a098646 (n+1)) := by
  sorry

end OMA.S_oeis_a282124
