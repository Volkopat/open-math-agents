import Mathlib

/-!
# A202194: Number of (n+2)X(n+2) binary arrays avoiding patterns 001 and 101 in rows and columns.

Source: https://oeis.org/A202194
Credit: @agchua

Michael Somos (Sep 11 2020), in the formula section of A202194, verbatim:
  Conjecture: a(n) = 4*(n+2)^2 * (2*n+1)!/(n! * (n+1)!). - _Michael Somos_, Sep 11 2020
The offset is 1 (the data 108, 640, 3500, 18144, 90552, ... start at n = 1), so the conjecture
is stated for n >= 1, as an identity in the rationals.
Definition (R. H. Hardin's convention for these arrays): an (n+2) X (n+2) binary array is a
function M : Fin (n+2) -> Fin (n+2) -> Fin 2, with M r c the entry in row r and column c. A row
is read from left to right and a column from top to bottom; a word w of length m avoids the
patterns 001 and 101 when no three consecutive entries w(i), w(i+1), w(i+2) are 0, 0, 1 or
1, 0, 1 (Avoids). An array is counted when all its rows and all its columns avoid both patterns
(Good). This reading agrees with the solutions shown in the entry for n = 3, and the definition
gives the listed terms 108, 640, 3500, 18144, 90552 for n = 1..5 (checked by direct enumeration).
-/

namespace OMA.S_oeis_a202194

/-- The word w of length m avoids the patterns 001 and 101: no three consecutive entries
w i, w j, w l (j = i + 1, l = i + 2) are 0, 0, 1 or 1, 0, 1. -/
def Avoids {m : ℕ} (w : Fin m → Fin 2) : Prop :=
  ∀ i j l : Fin m, (j : ℕ) = (i : ℕ) + 1 → (l : ℕ) = (i : ℕ) + 2 →
    ¬ (w i = 0 ∧ w j = 0 ∧ w l = 1) ∧ ¬ (w i = 1 ∧ w j = 0 ∧ w l = 1)
instance {m : ℕ} (w : Fin m → Fin 2) : Decidable (Avoids w) := by
  unfold Avoids
  infer_instance

/-- All rows (read from left to right) and all columns (read from top to bottom) of the
array M avoid the patterns 001 and 101. -/
def Good {m : ℕ} (M : Fin m → Fin m → Fin 2) : Prop :=
  (∀ r : Fin m, Avoids (M r)) ∧ ∀ c : Fin m, Avoids (fun r => M r c)
instance {m : ℕ} (M : Fin m → Fin m → Fin 2) : Decidable (Good M) := by
  unfold Good
  infer_instance

/-- A202194(n): the number of (n+2) X (n+2) binary arrays all of whose rows and columns avoid
the patterns 001 and 101. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Fin (n + 2) → Fin (n + 2) → Fin 2 => Good M)).card

/-- Somos' conjecture: a(n) = 4 (n+2)^2 (2n+1)! / (n! (n+1)!) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = 4 * ((n : ℚ) + 2) ^ 2 * ((2 * n + 1).factorial : ℚ) /
      ((n.factorial : ℚ) * ((n + 1).factorial : ℚ)) := by
  sorry

end OMA.S_oeis_a202194
