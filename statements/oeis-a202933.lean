import Mathlib

/-!
# A202933: Number of (n+3) X 5 binary arrays with consecutive windows of four bits considered as a binary number nondecreasing in every row and column.

Source: https://oeis.org/A202933
Credit: @Salofe

The sequence is due to R. H. Hardin (Dec 26 2011); it is column 2 of A202939.

Conjectures from Colin Barker, Jun 02 2018, quoted verbatim from the entry:
* "G.f.: x*(83521 - 387270*x + 723553*x^2 - 679679*x^3 + 320618*x^4 - 60719*x^5) / (1 - x)^6."
* "a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6."

The entry also lists Hardin's "Empirical: a(n) = (1/5)*n^5 + (31/2)*n^4 + (781/3)*n^3 +
2874*n^2 + (589559/30)*n + 60719."; that closed form is not part of this statement, which states
Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 83521, 113856, 153874, 206145, 273683, ...): for n ≥ 1, `a n`
  is the number of (n+3) X 5 arrays, that is, arrays with n + 3 rows and 5 columns (the entry
  shows 6 X 5 solutions for n = 3). We set `a 0 = 0`: the g.f. has no constant term, so `a 0` is
  its coefficient of x^0, and the recurrence (n > 6) never uses it.
* An array with `m` rows and 5 columns is a function `g : Fin m → Fin 5 → Bool`; `g i j` is the
  entry in row `i` (rows numbered from top to bottom) and column `j` (columns numbered from left to
  right), with `false` = 0 and `true` = 1. Arrays are labelled: they are not identified up to
  symmetry. The condition is the same for rows and for columns, so transposing shows that the
  count does not depend on which side has n + 3 entries.
* Every row is read from left to right and every column from top to bottom. A line of length `L`
  with bits b(0), ..., b(L-1) has the consecutive windows of four bits starting at i = 0, ..., L-4.
  The window starting at `i`, considered as a binary number with its first bit most significant,
  is 8*b(i) + 4*b(i+1) + 2*b(i+2) + b(i+3) (`win`). "Nondecreasing" means that the window starting
  at `i` is at most the window starting at `i + 1`, for every `i` with i + 4 < L (`LineOK`).
* This reading reproduces the data: an exhaustive count gives 83521, 113856, 153874 for
  n = 1, 2, 3, a row-by-row count of exactly this definition gives all 210 terms of the b-file
  (n = 1..210), and the four 6 X 5 solutions shown in the entry satisfy it. Reading the windows
  with their first bit least significant instead would reject the first of them (its third row
  0 1 1 1 0 would have the windows 14, 7); that reading gives the same counts (rotate an array by
  180 degrees and complement all its bits).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℤ` with the denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it is
  invertible in `ℤ⟦X⟧`).
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a202933

/-- An array with `m` rows and 5 columns: `g i j` is the entry in row `i` and column `j`
(`false` = 0, `true` = 1). -/
abbrev Grid (m : ℕ) := Fin m → Fin 5 → Bool

/-- The window of four consecutive bits of `line` starting at position `i`, considered as a
binary number with its first bit most significant: 8*b(i) + 4*b(i+1) + 2*b(i+2) + b(i+3). -/
def win {L : ℕ} (line : Fin L → Bool) (i : Fin (L - 3)) : ℕ :=
  have hi := i.isLt
  8 * (line ⟨i.val, by omega⟩).toNat + 4 * (line ⟨i.val + 1, by omega⟩).toNat +
    2 * (line ⟨i.val + 2, by omega⟩).toNat + (line ⟨i.val + 3, by omega⟩).toNat

/-- The consecutive windows of four bits of `line` are nondecreasing: for every `i` with
i + 4 < L, the window starting at `i` is at most the window starting at `i + 1`. -/
def LineOK {L : ℕ} (line : Fin L → Bool) : Prop :=
  ∀ i : Fin (L - 4),
    win line ⟨i.val, by have := i.isLt; omega⟩ ≤ win line ⟨i.val + 1, by have := i.isLt; omega⟩

/-- Every row of `g` (read from left to right) and every column of `g` (read from top to bottom)
has nondecreasing consecutive windows of four bits. -/
def IsValid {m : ℕ} (g : Grid m) : Prop :=
  (∀ i : Fin m, LineOK (g i)) ∧ (∀ j : Fin 5, LineOK (fun i => g i j))

instance {m : ℕ} (g : Grid m) : Decidable (IsValid g) := by
  unfold IsValid LineOK
  infer_instance

/-- A202933(n) for n ≥ 1: the number of (n+3) X 5 binary arrays with consecutive windows of four
bits, considered as binary numbers, nondecreasing in every row and column. The offset is 1, and
`a 0 = 0`. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((Finset.univ.filter (fun g : Grid (n + 4) => IsValid g)).card : ℤ)

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(83521 - 387270x + 723553x^2 - 679679x^3 + 320618x^4 - 60719x^5)/(1 - x)^6`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    PowerSeries.mk a * (1 - X) ^ 6 =
        X * (83521 - 387270 * X + 723553 * X ^ 2 - 679679 * X ^ 3 + 320618 * X ^ 4 -
          60719 * X ^ 5) ∧
    ∀ n : ℕ, 6 < n →
      a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a202933
