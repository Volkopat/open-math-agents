import Mathlib

/-!
# OEIS A202458: Barker's recurrence and generating function

Source: https://oeis.org/A202458 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 19 2011), offset 1: Number of (n+2) X 7 binary arrays with consecutive
windows of three bits considered as a binary number nondecreasing in every row and column. Data:
1728, 4137, 9338, 19614, 38478, 71088, 124740, 209445, ... The formula section states: Empirical:
a(n) = (1/840)*n^7 + (3/40)*n^6 + (47/30)*n^5 + 16*n^4 + (10847/120)*n^3 + (11557/40)*n^2 +
(258737/420)*n + 715. Conjectures from Colin Barker, May 31 2018: (Start) G.f.: x*(1728 - 9687*x +
24626*x^2 - 36022*x^3 + 32318*x^4 - 17650*x^5 + 5408*x^6 - 715*x^7) / (1 - x)^8. a(n) = 8*a(n-1) -
28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function x : Fin (n + 2) → Fin 7 → Bool, with rows x i; row i is the bit string
  `List.ofFn (x i)` and column j is `List.ofFn fun i => x i j`.
* `win b0 b1 b2` is the window b0 b1 b2 read as a binary number, 4 b0 + 2 b1 + b2, and `windowsOK s`
  says that the windows of three consecutive bits of s, from left to right, are nondecreasing (it
  holds trivially for strings of length at most 3). `good x` asks this for every row and every
  column. This is the reading of the staged sibling A202456 (width 5).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^8 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..27), all the entry's listed terms, and Hardin's empirical
  polynomial for all n >= 1.
-/

namespace OMA.S_oeis_a202458

open PowerSeries

/-- The window of three bits b0 b1 b2, read as a binary number. -/
def win (b0 b1 b2 : Bool) : ℕ := 4 * b0.toNat + 2 * b1.toNat + b2.toNat

/-- The consecutive windows of three bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: rest => decide (win b0 b1 b2 ≤ win b1 b2 b3) && windowsOK (b1 :: b2 :: b3 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 7 → Bool): in every row and in every column the
consecutive windows of three bits are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 7 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202458(n): the number of good (n+2) X 7 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 2) → Fin 7 → Bool => good x = true).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (1728 - 9687 * X + 24626 * X ^ 2 - 36022 * X ^ 3 + 32318 * X ^ 4 - 17650 * X ^ 5 + 5408 *
        X ^ 6 - 715 * X ^ 7) := by
  sorry

end OMA.S_oeis_a202458
