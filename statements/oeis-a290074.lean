import Mathlib

/-!
# OEIS A290074

Decimal representation of the diagonal from the origin to the corner of the n-th stage of growth
of the two-dimensional cellular automaton defined by Rule 641, based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A290074
Conjectures: Colin Barker, Jul 20 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The diagonal runs from origin to corner inclusive. Its first cell is the most significant digit
in base 2.
The last line of %t extracts the central row and disagrees with the published terms.
The definition follows the diagonal in %N and the published data.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a290074

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the diagonal from origin to corner, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n (i : ℤ) (i : ℤ)).toNat : ℤ) * 2 ^ (n-i)

def a (n : ℕ) : ℤ := digits 641 n

/-- A283507 reads the x-axis from the origin to the right edge in base two. -/
def axis641 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state 641 n (i : ℤ) 0).toNat : ℤ) * 2^(n-i)

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 - 2 * X ^ 3 + 4 * X ^ 4) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → a n = 3 * 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → a n = axis641 n) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → a n = 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → a n = axis641 n) ∧
    (∀ n : ℕ, 4 < n → a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a290074
