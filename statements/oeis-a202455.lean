import Mathlib

/-!
# OEIS A202455: Barker's recurrence and generating function

Source: https://oeis.org/A202455 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 19 2011), offset 1: Number of (n+2) X 4 binary arrays with consecutive
windows of three bits considered as a binary number nondecreasing in every row and column. Data:
729, 1194, 1876, 2835, 4137, 5854, 8064, 10851, ... The formula section states: Empirical: a(n) =
(1/4)*n^4 + (15/2)*n^3 + (229/4)*n^2 + 237*n + 427. Conjectures from Colin Barker, May 31 2018:
(Start) G.f.: x*(729 - 2451*x + 3196*x^2 - 1895*x^3 + 427*x^4) / (1 - x)^5. a(n) = 5*a(n-1) -
10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array is a function x : Fin (n + 2) → Fin 4 → Bool, with rows x i; row i is the bit string
  `List.ofFn (x i)` and column j is `List.ofFn fun i => x i j`.
* `win b0 b1 b2` is the window b0 b1 b2 read as a binary number, 4 b0 + 2 b1 + b2, and `windowsOK s`
  says that the windows of three consecutive bits of s, from left to right, are nondecreasing (it
  holds trivially for strings of length at most 3). `good x` asks this for every row and every
  column. This is the reading of the staged sibling A202456 (width 5).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^5 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..34), all the entry's listed terms, and Hardin's empirical
  polynomial for all n >= 1.
-/

namespace OMA.S_oeis_a202455

open PowerSeries

/-- The window of three bits b0 b1 b2, read as a binary number. -/
def win (b0 b1 b2 : Bool) : ℕ := 4 * b0.toNat + 2 * b1.toNat + b2.toNat

/-- The consecutive windows of three bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: rest => decide (win b0 b1 b2 ≤ win b1 b2 b3) && windowsOK (b1 :: b2 :: b3 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 4 → Bool): in every row and in every column the
consecutive windows of three bits are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 4 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202455(n): the number of good (n+2) X 4 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 2) → Fin 4 → Bool => good x = true).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (729 - 2451 * X + 3196 * X ^ 2 - 1895 * X ^ 3 + 427 * X ^ 4) := by
  sorry

end OMA.S_oeis_a202455
