import Mathlib

/-!
# OEIS A202937: Barker's generating function and recurrence

Source: https://oeis.org/A202937 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A202937 (R. H. Hardin, Dec 26 2011), offset 1: Number of (n+3) X 9 binary arrays with consecutive windows of four bits considered as a binary number nondecreasing in every row and column.
Data: 194481, 359970, 695114, 1360328, 2631416, 4958318, 9044252, 15949741, ...
Formula section:
Empirical: a(n) = (1/15120)*n^9 + (1/96)*n^8 + (235/504)*n^7 + (725/72)*n^6 + 125*n^5 + (276005/288)*n^4 + (13991149/3024)*n^3 + (1320845/72)*n^2 + (24830539/420)*n + 111295.
Conjectures from Colin Barker, Jun 03 2018: (Start)
G.f.: x*(194481 - 1584840*x + 5847059*x^2 - 12729882*x^3 + 17952876*x^4 - 16970274*x^5 + 10737942*x^6 - 4382257*x^7 + 1046214*x^8 - 111295*x^9) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.
(End)

Formalization notes:
* An array is a function x : Fin (n + 3) → Fin 9 → Bool (false = 0, true = 1), x i j being the
  entry in row i and column j; row i is the bit string `List.ofFn (x i)`, read left to right, and
  column j is the bit string `List.ofFn fun i => x i j`, read top to bottom.
* `win b0 b1 b2 b3` is the window b0 b1 b2 b3 of 4 consecutive bits read as a binary number, the first
  bit being the high bit: 8 * b0 + 4 * b1 + 2 * b2 + b3. `windowsOK s` says that the windows of four
  consecutive bits of s, from first to last, are nondecreasing; it holds trivially for strings of
  at most 4 bits. `good x` asks this for every row and every column. This is the reading of the
  merged statements of the three-bit siblings A202455 - A202460, and the bit order and directions
  agree with the solutions shown in the entry.
* With this reading the definition reproduces every listed term of the entry: checked by a
  transfer-matrix evaluation of this exact definition for all listed terms, and by brute force
  for n = 1.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^10 = N(x) in Z[[x]],
  which is equivalent to the quotient form because 1 - x is a unit. The recurrence is stated in
  the integers for every n > 10, the range given in the entry.
* `main` is the conjunction of Barker's two conjectures; the empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a202937

open PowerSeries

/-- The window b0 b1 b2 b3 of 4 bits, read as a binary number with b0 the high bit. -/
def win (b0 b1 b2 b3 : Bool) : ℕ := 8 * b0.toNat + 4 * b1.toNat + 2 * b2.toNat + b3.toNat

/-- The consecutive windows of four bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => decide (win b0 b1 b2 b3 ≤ win b1 b2 b3 b4) && windowsOK (b1 :: b2 :: b3 :: b4 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 9 → Bool): in every row and in every column the
consecutive windows of four bits, read as binary numbers, are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 9 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202937(n): the number of good (n+3) X 9 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 3) → Fin 9 → Bool => good x = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
      X * (194481 - 1584840 * X + 5847059 * X ^ 2 - 12729882 * X ^ 3 + 17952876 * X ^ 4 - 16970274 * X ^ 5 + 10737942 * X ^ 6 - 4382257 * X ^ 7 + 1046214 * X ^ 8 - 111295 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a202937
