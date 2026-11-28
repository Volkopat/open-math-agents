import Mathlib

/-!
# OEIS A202460: Barker's recurrence and generating function

Source: https://oeis.org/A202460 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 19 2011), offset 1: Number of (n+2) X 9 binary arrays with consecutive
windows of three bits considered as a binary number nondecreasing in every row and column. Data:
2744, 8064, 21972, 54618, 124740, 264822, 528390, 1000023, ... The formula section states:
Empirical: a(n) = (1/60480)*n^9 + (1/672)*n^8 + (163/3360)*n^7 + (119/144)*n^6 + (24221/2880)*n^5 +
(15553/288)*n^4 + (1671487/7560)*n^3 + (282325/504)*n^2 + (404227/420)*n + 937. Conjectures from
Colin Barker, Jun 01 2018: (Start) G.f.: x*(2744 - 19376*x + 64812*x^2 - 131502*x^3 + 175860*x^4 -
159456*x^5 + 97542*x^6 - 38691*x^7 + 9010*x^8 - 937*x^9) / (1 - x)^10. a(n) = 10*a(n-1) -
45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) -
a(n-10) for n>10. (End)

Formalization notes:
* An array is a function x : Fin (n + 2) → Fin 9 → Bool, with rows x i; row i is the bit string
  `List.ofFn (x i)` and column j is `List.ofFn fun i => x i j`.
* `win b0 b1 b2` is the window b0 b1 b2 read as a binary number, 4 b0 + 2 b1 + b2, and `windowsOK s`
  says that the windows of three consecutive bits of s, from left to right, are nondecreasing (it
  holds trivially for strings of length at most 3). `good x` asks this for every row and every
  column. This is the reading of the staged sibling A202456 (width 5).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^10 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..25), all the entry's listed terms, and Hardin's empirical
  polynomial for all n >= 1.
-/

namespace OMA.S_oeis_a202460

open PowerSeries

/-- The window of three bits b0 b1 b2, read as a binary number. -/
def win (b0 b1 b2 : Bool) : ℕ := 4 * b0.toNat + 2 * b1.toNat + b2.toNat

/-- The consecutive windows of three bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: rest => decide (win b0 b1 b2 ≤ win b1 b2 b3) && windowsOK (b1 :: b2 :: b3 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 9 → Bool): in every row and in every column the
consecutive windows of three bits are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 9 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202460(n): the number of good (n+2) X 9 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 2) → Fin 9 → Bool => good x = true).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n -
      4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a
      (n - 10)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
      X * (2744 - 19376 * X + 64812 * X ^ 2 - 131502 * X ^ 3 + 175860 * X ^ 4 - 159456 * X ^ 5 +
        97542 * X ^ 6 - 38691 * X ^ 7 + 9010 * X ^ 8 - 937 * X ^ 9) := by
  sorry

end OMA.S_oeis_a202460
