import Mathlib

/-!
# OEIS A272762

Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton
defined by Rule 822, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A272762
Conjectures: Lars Blomberg, Jul 22 2016; Chai Wah Wu and Colin Barker, Apr 28 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has a single ON cell at the origin. The stored square grows by one cell on each
side per step. Its entire complement remains uniform by propagation at speed at most one.
Both the square and the exterior update synchronously, using bit c+2s, with four orthogonal
neighbors. At index n, sum the central square of stage 2^n-1, starting at n = 0.
-/

namespace OMA.S_oeis_a272762

open PowerSeries

/-- The uniform exterior and the rows in the central square, ordered by increasing coordinate. -/
structure Stage where
  exterior : Bool
  rows : Array (Array Bool)

/-- Row/column indices in the finite square begin at zero; all other indices are exterior. -/
def cell (g : Stage) (x y : ℤ) : Bool :=
  if 0 ≤ x ∧ 0 ≤ y then
    ((g.rows[y.toNat]?.getD #[])[x.toNat]?).getD g.exterior
  else g.exterior

def stage (r : ℕ) : ℕ → Stage
  | 0 => ⟨false, #[#[true]]⟩
  | t+1 =>
    let g := stage r t
    let indices := Array.range (2*t+3)
    ⟨r.testBit (9*g.exterior.toNat), indices.map fun (j : ℕ) => indices.map fun (i : ℕ) =>
      let x := (i : ℤ)-1
      let y := (j : ℤ)-1
      r.testBit ((cell g x y).toNat + 2*((cell g (x-1) y).toNat + (cell g (x+1) y).toNat +
        (cell g x (y-1)).toNat + (cell g x (y+1)).toNat))⟩

/-- Count only the central square at stage 2^n - 1. -/
def sampled (r n : ℕ) : ℤ :=
  (stage r (2^n-1)).rows.foldl (fun total row =>
    row.foldl (fun s b => s + (b.toNat : ℤ)) total) 0


def a (n : ℕ) : ℤ := sampled 822 n

theorem main :
    (∀ n : ℕ, a n = sampled 886 n) ∧
    (∀ n : ℕ, 4 < n → a n = 12 * a (n - 1) - 55 * a (n - 2) + 120 * a (n - 3) - 124 * a (n - 4) + 48 * a (n
      - 5)) ∧
    (PowerSeries.mk a * ((X - 1) * (2 * X - 1) ^ 2 * (3 * X - 1) * (4 * X - 1)) =
      -56 * X ^ 4 + 40 * X ^ 3 - 20 * X ^ 2 + 7 * X - 1) ∧
    (∀ n : ℕ, a n = 5 - 2 ^ (1 + n) + 2 ^ (1 + 2 * n) - 4 * 3 ^ n + 2 ^ (2 + n) * (n : ℤ)) := by
  sorry

end OMA.S_oeis_a272762
