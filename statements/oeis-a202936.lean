import Mathlib

/-!
# OEIS A202936: Barker's generating function and recurrence

Source: https://oeis.org/A202936 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A202936 (R. H. Hardin, Dec 26 2011), offset 1: Number of (n+3) X 8 binary arrays with consecutive windows of four bits considered as a binary number nondecreasing in every row and column.
Data: 160000, 273683, 481798, 857408, 1515902, 2631416, 4457228, 7350643, ...
Formula section:
Empirical: a(n) = (1/1680)*n^8 + (17/210)*n^7 + (134/45)*n^6 + (256/5)*n^5 + (352481/720)*n^4 + (55381/20)*n^3 + (32201731/2520)*n^2 + (19670981/420)*n + 97073.
Conjectures from Colin Barker, Jun 03 2018: (Start)
G.f.: x*(160000 - 1166317*x + 3778651*x^2 - 7066186*x^3 + 8314586*x^4 - 6291988*x^5 + 2987174*x^6 - 812969*x^7 + 97073*x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.
(End)

Formalization notes:
* An array is a function x : Fin (n + 3) → Fin 8 → Bool (false = 0, true = 1), x i j being the
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
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^9 = N(x) in Z[[x]],
  which is equivalent to the quotient form because 1 - x is a unit. The recurrence is stated in
  the integers for every n > 9, the range given in the entry.
* `main` is the conjunction of Barker's two conjectures; the empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a202936

open PowerSeries

/-- The window b0 b1 b2 b3 of 4 bits, read as a binary number with b0 the high bit. -/
def win (b0 b1 b2 b3 : Bool) : ℕ := 8 * b0.toNat + 4 * b1.toNat + 2 * b2.toNat + b3.toNat

/-- The consecutive windows of four bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => decide (win b0 b1 b2 b3 ≤ win b1 b2 b3 b4) && windowsOK (b1 :: b2 :: b3 :: b4 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 8 → Bool): in every row and in every column the
consecutive windows of four bits, read as binary numbers, are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 8 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202936(n): the number of good (n+3) X 8 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 3) → Fin 8 → Bool => good x = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
      X * (160000 - 1166317 * X + 3778651 * X ^ 2 - 7066186 * X ^ 3 + 8314586 * X ^ 4 - 6291988 * X ^ 5 + 2987174 * X ^ 6 - 812969 * X ^ 7 + 97073 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a202936
