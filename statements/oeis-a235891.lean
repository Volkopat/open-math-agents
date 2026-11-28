import Mathlib

/-!
# OEIS A235891: Barker's g.f. and closed form for (n+1) X (6+1) 0..3 arrays with the minimum plus the upper median equal to the lower median plus the maximum in every 2 X 2 subblock

Source: https://oeis.org/A235891 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A235891 (R. H. Hardin, Jan 16 2014), offset 1: Number of (n+1) X (6+1) 0..3 arrays with the
minimum plus the upper median equal to the lower median plus the maximum in every 2 X 2 subblock.
Column 6 of A235893. Data: 17152, 18712, 21928, 28744, 43912, ... Formula section: Empirical: a(n) =
7*a(n-1) - 14*a(n-2) + 8*a(n-3). Conjectures from Colin Barker, Oct 20 2018: (Start) G.f.:
8*x*(2144-12669*x+16384*x^2) / ((1-x)*(1-2*x)*(1-4*x)). a(n) = 4*(3906+189*2^n+4^n). (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 7 -> Fin 4, x i j being the element in row i and
  column j. The 2 X 2 subblocks are the blocks of rows i, i' = i + 1 and columns j, j' = j + 1. For
  the four elements of a block in increasing order m0 <= m1 <= m2 <= m3 (with repetitions) the
  minimum is m0, the lower median m1, the upper median m2 and the maximum m3; the condition is m0 +
  m2 = m1 + m3. `medEq` sorts the four values with List.insertionSort and compares the two sums.
  This reading reproduces the entry's data and the table A235893 (brute force over all arrays for
  small sizes, a row transfer for the rest of the table).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form carries no range in the source; it is stated in Q for every n >=
  1 (the offset).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..21) = 17152, 18712, 21928, 28744, 43912, 80392, 177928,
  471304, 1451272, 4984072, 18341128, 70221064, 274644232, 1086143752, 4319755528, 17229430024,
  68818582792, 275076103432, 1099908005128, 4398839250184, 17593771506952, the entry's data.
-/

namespace OMA.S_oeis_a235891

open PowerSeries

/-- For four values p, q, r, s with increasing order m0 <= m1 <= m2 <= m3 (listed with repetitions;
the lower median is m1 and the upper median m2): whether the minimum plus the upper median
equals the lower median plus the maximum, m0 + m2 = m1 + m3. -/
def medEq (p q r s : ℕ) : Bool :=
  let m := List.insertionSort (· ≤ ·) [p, q, r, s]
  m.getD 0 0 + m.getD 2 0 == m.getD 1 0 + m.getD 3 0

/-- A235891(n): the number of (n+1) X 7 arrays x with entries 0..3 (x i j in row i and column j) in
which every 2 X 2 subblock, rows i, i' = i + 1 and columns j, j' = j + 1, has the minimum plus the
upper median of its four elements equal to the lower median plus the maximum (`medEq`). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 7 → Fin 4)).filter (fun x =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 7, j'.val = j.val + 1 →
      medEq (x i j).val (x i j').val (x i' j).val (x i' j').val = true)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
        8 * X * (2144 - 12669 * X + 16384 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (3906 + 189 * 2 ^ n + 4 ^ n) := by
  sorry

end OMA.S_oeis_a235891
