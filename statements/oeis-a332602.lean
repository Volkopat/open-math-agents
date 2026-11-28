import Mathlib

/-!
# A332602: tridiagonal matrix with main diagonal 1,2,2,2,... and adjacent diagonals 1,1,1,...

Source: https://oeis.org/A332602 (conjectures by Gary W. Adamson, Mar 11 2020)

The entry is the infinite tridiagonal matrix M whose main diagonal is 1, 2, 2, 2, ... and whose
two adjacent diagonals are 1, 1, 1, .... Adamson's comment: extracting the 2 X 2, 3 X 3 and 4 X 4
(leading) submatrices from M and taking the upper left entries of their n-th powers gives the
sequences 1, 1, 2, 5, 13, ... = A001519, 1, 1, 2, 5, 14, 42, 131, ... = A080937 and
1, 1, 2, 5, 14, 42, 132, 429, 1429, ... = A080938. The statement says: For the proofs of the
2 X 2, 3 X 3 and 4 X 4 conjectures, see the comments in the respective A-numbers.

Formalization notes:
* `Msub N` is the leading N X N submatrix of M, with integer entries, indexed by `Fin N`
  (row and column 0 first); `(Msub N ^ n) 0 0` is the upper left entry of its n-th power.
* A001519 (offset 0) is defined by its title: a(n) = 3*a(n-1) - a(n-2) for n >= 2, with
  a(0) = a(1) = 1.
* A080937 and A080938 (offset 0) are defined by their titles: the number of Catalan paths
  (nonnegative, starting and ending at 0, steps up or down by 1) of 2n steps with all values <= 5,
  respectively <= 7. A path is a step sequence `s : Fin (2n) → Bool` (true is an up step);
  `ht s j` is the value after the first j steps.
* The statement is the identification of the three sequences, for every n >= 0. (The comment
  also lists the limits of the ratios of consecutive terms; these are not part of the claim
  formalized here, which is the identification of the sequences.)
-/

namespace OMA.S_oeis_a332602

/-- The leading N X N submatrix of the tridiagonal matrix M of A332602. -/
def Msub (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := fun i j =>
  if i = j then (if (i : ℕ) = 0 then 1 else 2)
  else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0

/-- A001519: a(n) = 3*a(n-1) - a(n-2) for n >= 2, with a(0) = a(1) = 1. -/
def A001519 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 3 * A001519 (n + 1) - A001519 n

/-- The value of the path `s` after its first `j` steps. -/
def ht {L : ℕ} (s : Fin L → Bool) (j : ℕ) : ℤ :=
  ∑ i : Fin L, if (i : ℕ) < j then (if s i then 1 else -1) else 0

/-- A080937(n): Catalan paths of 2n steps with all values <= 5. -/
def A080937 (n : ℕ) : ℕ := (Finset.univ.filter fun s : Fin (2 * n) → Bool =>
  (∀ j ≤ 2 * n, 0 ≤ ht s j ∧ ht s j ≤ 5) ∧ ht s (2 * n) = 0).card

/-- A080938(n): Catalan paths of 2n steps with all values <= 7. -/
def A080938 (n : ℕ) : ℕ := (Finset.univ.filter fun s : Fin (2 * n) → Bool =>
  (∀ j ≤ 2 * n, 0 ≤ ht s j ∧ ht s j ≤ 7) ∧ ht s (2 * n) = 0).card

theorem main : ∀ n : ℕ,
    (Msub 2 ^ n) 0 0 = A001519 n ∧ (Msub 3 ^ n) 0 0 = A080937 n ∧
      (Msub 4 ^ n) 0 0 = A080938 n := by
  sorry

end OMA.S_oeis_a332602
