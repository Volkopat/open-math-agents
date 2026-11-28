import Mathlib

/-!
# OEIS A202459: Barker's recurrence and generating function

Source: https://oeis.org/A202459 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 19 2011), offset 1: Number of (n+2) X 8 binary arrays with consecutive
windows of three bits considered as a binary number nondecreasing in every row and column. Data:
2197, 5854, 14586, 33468, 71088, 141192, 264822, 473031, ... The formula section states: Empirical:
a(n) = (1/6720)*n^8 + (19/1680)*n^7 + (431/1440)*n^6 + (193/48)*n^5 + (90001/2880)*n^4 +
(5873/40)*n^3 + (2076229/5040)*n^2 + (10915/14)*n + 823. Conjectures from Colin Barker, May 31 2018:
(Start) G.f.: x*(2197 - 13919*x + 40992*x^2 - 71610*x^3 + 80058*x^4 - 58194*x^5 + 26730*x^6 -
7071*x^7 + 823*x^8) / (1 - x)^9. a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) -
84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9. (End)

Formalization notes:
* An array is a function x : Fin (n + 2) → Fin 8 → Bool, with rows x i; row i is the bit string
  `List.ofFn (x i)` and column j is `List.ofFn fun i => x i j`.
* `win b0 b1 b2` is the window b0 b1 b2 read as a binary number, 4 b0 + 2 b1 + b2, and `windowsOK s`
  says that the windows of three consecutive bits of s, from left to right, are nondecreasing (it
  holds trivially for strings of length at most 3). `good x` asks this for every row and every
  column. This is the reading of the staged sibling A202456 (width 5).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^9 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26), all the entry's listed terms, and Hardin's empirical
  polynomial for all n >= 1.
-/

namespace OMA.S_oeis_a202459

open PowerSeries

/-- The window of three bits b0 b1 b2, read as a binary number. -/
def win (b0 b1 b2 : Bool) : ℕ := 4 * b0.toNat + 2 * b1.toNat + b2.toNat

/-- The consecutive windows of three bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: rest => decide (win b0 b1 b2 ≤ win b1 b2 b3) && windowsOK (b1 :: b2 :: b3 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 8 → Bool): in every row and in every column the
consecutive windows of three bits are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 8 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202459(n): the number of good (n+2) X 8 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 2) → Fin 8 → Bool => good x = true).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n -
      4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
      X * (2197 - 13919 * X + 40992 * X ^ 2 - 71610 * X ^ 3 + 80058 * X ^ 4 - 58194 * X ^ 5 +
        26730 * X ^ 6 - 7071 * X ^ 7 + 823 * X ^ 8) := by
  sorry

end OMA.S_oeis_a202459
