import Mathlib

/-!
# A273724: Place n equally-spaced points around a circle, labeled 0,1,2,...,n-1. For each i = 0..n-1 such that 3i != i mod n, draw an (undirected) chord from i to (3i mod n). Then a(n) is the total number of distinct chords.

Source: https://oeis.org/A273724
Credit: @ivillar

Status: known result (Brooke Logan and N. J. A. Sloane, Jun 23 2016). The entry states:
* a(n) = n-1 if n>0 is odd, n-2 if n == +-2 (mod 8), n-3 if n == 4 (mod 8), and n-5 if
  n == 0 (mod 8). These formulas are easily established by observing that the chord at i is
  missing if 2i == 0 mod n, and the chords starting at i and at 3i coincide if 8i == 0 mod n.
  (Brooke Logan and N. J. A. Sloane, Jun 23 2016; they note that the formulas imply the g.f.
  conjectured by Colin Barker.)
* a(n) = a(n-1)+a(n-8)-a(n-9) for n>9. (Colin Barker, May 29 2016; this follows from the
  above g.f., Brooke Logan and N. J. A. Sloane.)
This file states the closed form (for every n > 0) and Barker's recurrence (for every n > 9).

Formalization notes:
* Offset 0, as in the entry (data: 0, 0, 0, 2, 1, 4, 4, 6, 3, 8, 8, 10, 9, ...).
* The points are the numbers `0, ..., n-1`. For each `i < n` with `3 * i % n ≠ i` we draw the
  undirected chord `s(i, 3 * i % n)`, an element of `Sym2 ℕ` (an unordered pair), and `a n` is
  the number of distinct chords obtained (the cardinality of the image).
* Both formulas are stated in `ℤ`; the case split of the closed form is on `n % 2` and `n % 8`.
-/

namespace OMA.S_oeis_a273724

/-- The set of chords: for each point `i < n` with `3i ≢ i (mod n)`, the unordered pair
`{i, 3i mod n}`. -/
def chords (n : ℕ) : Finset (Sym2 ℕ) :=
  ((Finset.range n).filter fun i => 3 * i % n ≠ i).image fun i => s(i, 3 * i % n)

/-- A273724(n): the number of distinct chords. -/
def a (n : ℕ) : ℕ := (chords n).card

/-- The closed form of Logan and Sloane, and Barker's recurrence. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℤ) = n - (if n % 2 = 1 then 1
      else if n % 8 = 2 ∨ n % 8 = 6 then 2 else if n % 8 = 4 then 3 else 5)) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = a (n - 1) + a (n - 8) - a (n - 9)) := by
  sorry

end OMA.S_oeis_a273724
