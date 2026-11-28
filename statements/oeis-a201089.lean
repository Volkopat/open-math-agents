import Mathlib

/-!
# A201089: Number of -n..n arrays of 4 elements with first and second differences also in -n..n.

A201089(n) is the number of arrays `x 0, x 1, x 2, x 3` of integers in `-n..n` whose first
differences `x (i + 1) - x i` (three of them) and second differences (two of them) all lie in
`-n..n` as well. A brute-force count of this reading gives
25, 175, 651, 1759, 3899, 7581, 13405, 22085 for n = 1..8, matching the listed terms
(row 4 of A201088).

The offset is 1, so the formulas are stated for n ≥ 1.

The problem: the conjectures of Colin Barker (Feb 14 2018):
  a(n) = (101*n^4 + 202*n^3 + 190*n^2 + 92*n + 24) / 24 for n even,
  a(n) = (101*n^4 + 202*n^3 + 190*n^2 + 86*n + 21) / 24 for n odd.
The division is exact division, stated over ℚ. (The entry also lists R. J. Mathar's empirical
recurrence and generating function; they are not part of this statement.)

Source: https://oeis.org/A201089
Credit: @VashaTS
-/

namespace OMA.S_oeis_a201089

/-- The integers `-n, ..., n`, as the image of `0, ..., 2n` under `k ↦ k - n`
(`Finset.Icc` on `ℤ` would make `a` noncomputable). -/
def box (n : ℕ) : Finset ℤ := (Finset.range (2 * n + 1)).image fun k : ℕ => (k : ℤ) - n

/-- The differences `x (i + 1) - x i` of a finite integer sequence. -/
def diff {k : ℕ} (x : Fin (k + 1) → ℤ) : Fin k → ℤ := fun i => x i.succ - x i.castSucc

/-- A201089(n): arrays of 4 entries in `-n..n` whose first and second differences are in `-n..n`. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => box n).filter fun x =>
    (∀ i, diff x i ∈ box n) ∧ ∀ i, diff (diff x) i ∈ box n).card

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Even n → (a n : ℚ) = (101 * n ^ 4 + 202 * n ^ 3 + 190 * n ^ 2 + 92 * n + 24) / 24) ∧
      (Odd n → (a n : ℚ) = (101 * n ^ 4 + 202 * n ^ 3 + 190 * n ^ 2 + 86 * n + 21) / 24) := by
  sorry

end OMA.S_oeis_a201089
