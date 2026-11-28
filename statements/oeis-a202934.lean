import Mathlib

/-!
# OEIS A202934: Barker's generating function and recurrence

Source: https://oeis.org/A202934 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A202934 (R. H. Hardin, Dec 26 2011), offset 1: Number of (n+3) X 6 binary arrays with consecutive windows of four bits considered as a binary number nondecreasing in every row and column.
Data: 104976, 153874, 225858, 330853, 481798, 695114, 991196, 1394929, ...
Formula section:
Empirical: a(n) = (1/30)*n^6 + (16/5)*n^5 + (875/12)*n^4 + (2116/3)*n^3 + (103801/20)*n^2 + (407932/15)*n + 71809.
Conjectures from Colin Barker, Jun 03 2018: (Start)
G.f.: x*(104976 - 580958*x + 1353236*x^2 - 1692959*x^3 + 1197415*x^4 - 453495*x^5 + 71809*x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array is a function x : Fin (n + 3) → Fin 6 → Bool (false = 0, true = 1), x i j being the
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
  for n = 1, 2.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]],
  which is equivalent to the quotient form because 1 - x is a unit. The recurrence is stated in
  the integers for every n > 7, the range given in the entry.
* `main` is the conjunction of Barker's two conjectures; the empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a202934

open PowerSeries

/-- The window b0 b1 b2 b3 of 4 bits, read as a binary number with b0 the high bit. -/
def win (b0 b1 b2 b3 : Bool) : ℕ := 8 * b0.toNat + 4 * b1.toNat + 2 * b2.toNat + b3.toNat

/-- The consecutive windows of four bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => decide (win b0 b1 b2 b3 ≤ win b1 b2 b3 b4) && windowsOK (b1 :: b2 :: b3 :: b4 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 6 → Bool): in every row and in every column the
consecutive windows of four bits, read as binary numbers, are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 6 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202934(n): the number of good (n+3) X 6 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 3) → Fin 6 → Bool => good x = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (104976 - 580958 * X + 1353236 * X ^ 2 - 1692959 * X ^ 3 + 1197415 * X ^ 4 - 453495 * X ^ 5 + 71809 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a202934
