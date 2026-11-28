import Mathlib

/-!
# OEIS A322056: Barker's conjectures for the knight-move automaton (first differences)

Source: https://oeis.org/A322056 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A322056 (N. J. A. Sloane, Dec 21 2018), offset 0: First differences of A322055.
Comments of A322055: the cells are the squares of the standard square grid; once ON they stay ON
forever; each cell has 8 neighbors, the cells a knight's move away; generation 0 has a single ON
cell; a cell is turned ON at generation n+1 if it has one or two ON neighbors at generation n.
Formula section:
Conjectures from Colin Barker, Dec 22 2018: (Start)
G.f.: (1 + 8*x + 32*x^2 + 32*x^3 + 70*x^4 + 24*x^5 + 72*x^6 + 49*x^8 - 8*x^10 + 16*x^11 - 8*x^12) / ((1 - x)^2*(1 + x)^2*(1 + x^2)^2).
a(n) = 2*a(n-4) - a(n-8) for n>8.
(End)

Formalization notes:
* `on t x y` is the state of cell (x, y) at generation t, the start cell being (0, 0). A cell
  that is ON stays ON; an OFF cell turns ON when 1 or 2 of its 8 knight neighbors are ON.
* `cnt t` counts the ON cells at generation t; every ON cell of generation t has |x|, |y| <= 2t
  (a knight move changes each coordinate by at most 2), so the count runs over that box.
* As in the entry (data 1, 8, 32, ...), a(0) = A322055(0) and a(n) = A322055(n) - A322055(n-1) for
  n >= 1; a(n) is an integer.
* The statement is the conjunction of Barker's recurrence and generating function, stated in the
  integers; the identity A(x) = N/D is stated as A * D = N in the formal power series ring over
  the integers (D has constant term 1).
* Controls: the definition gives 1, 8, 32, 32, 72, 40, 136, 64 for n = 0..7 (the entry's data, checked by direct
  simulation).
-/

namespace OMA.S_oeis_a322056

open PowerSeries

/-- The number of ON knight neighbors of (x, y) in the configuration s. -/
def nb (s : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (s (x + 1) (y + 2)).toNat + (s (x + 2) (y + 1)).toNat + (s (x - 1) (y + 2)).toNat +
    (s (x - 2) (y + 1)).toNat + (s (x + 1) (y - 2)).toNat + (s (x + 2) (y - 1)).toNat +
    (s (x - 1) (y - 2)).toNat + (s (x - 2) (y - 1)).toNat

/-- Generation t of the automaton. -/
def on : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => on t x y || decide (nb (on t) x y = 1 ∨ nb (on t) x y = 2)

/-- A322055(t): the number of ON cells at generation t. -/
def cnt (t : ℕ) : ℕ :=
  ((Finset.range (4 * t + 1) ×ˢ Finset.range (4 * t + 1)).filter fun p : ℕ × ℕ =>
    on t ((p.1 : ℤ) - 2 * t) ((p.2 : ℤ) - 2 * t)).card

/-- A322056(n): the first differences of A322055, starting with A322055(0). -/
def a : ℕ → ℤ
  | 0 => cnt 0
  | n + 1 => (cnt (n + 1) : ℤ) - cnt n

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 4) - a (n - 8)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2) =
      (1 + 8 * X + 32 * X ^ 2 + 32 * X ^ 3 + 70 * X ^ 4 + 24 * X ^ 5 + 72 * X ^ 6 + 49 * X ^ 8 - 8 * X ^ 10 + 16 * X ^ 11 - 8 * X ^ 12 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a322056
