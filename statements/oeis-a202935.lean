import Mathlib

/-!
# OEIS A202935: Barker's generating function and recurrence

Source: https://oeis.org/A202935 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A202935 (R. H. Hardin, Dec 26 2011), offset 1: Number of (n+3) X 7 binary arrays with consecutive windows of four bits considered as a binary number nondecreasing in every row and column.
Data: 130321, 206145, 330853, 533832, 857408, 1360328, 2121734, 3245653, ...
Formula section:
Empirical: a(n) = (1/210)*n^7 + (11/20)*n^6 + (81/5)*n^5 + (1713/8)*n^4 + (90179/60)*n^3 + (337713/40)*n^2 + (15214631/420)*n + 83919.
Conjectures from Colin Barker, Jun 03 2018: (Start)
G.f.: x*(130321 - 836423*x + 2330681*x^2 - 3638908*x^3 + 3428986*x^4 - 1947234*x^5 + 616520*x^6 - 83919*x^7) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
(End)

Formalization notes:
* An array is a function x : Fin (n + 3) → Fin 7 → Bool (false = 0, true = 1), x i j being the
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
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^8 = N(x) in Z[[x]],
  which is equivalent to the quotient form because 1 - x is a unit. The recurrence is stated in
  the integers for every n > 8, the range given in the entry.
* `main` is the conjunction of Barker's two conjectures; the empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a202935

open PowerSeries

/-- The window b0 b1 b2 b3 of 4 bits, read as a binary number with b0 the high bit. -/
def win (b0 b1 b2 b3 : Bool) : ℕ := 8 * b0.toNat + 4 * b1.toNat + 2 * b2.toNat + b3.toNat

/-- The consecutive windows of four bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => decide (win b0 b1 b2 b3 ≤ win b1 b2 b3 b4) && windowsOK (b1 :: b2 :: b3 :: b4 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 7 → Bool): in every row and in every column the
consecutive windows of four bits, read as binary numbers, are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 7 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202935(n): the number of good (n+3) X 7 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 3) → Fin 7 → Bool => good x = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (130321 - 836423 * X + 2330681 * X ^ 2 - 3638908 * X ^ 3 + 3428986 * X ^ 4 - 1947234 * X ^ 5 + 616520 * X ^ 6 - 83919 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a202935
