import Mathlib

/-!
# A151512: The triangle in A151359 read by rows upwards.

Source: https://oeis.org/A151512 (and https://oeis.org/A151359)
Credit: @agchua

In the comments of A151512 (from Philippe Beaudoin, Nov 09 2013), stated here literally, all of it:
  Conjectured: The i-th element of row j is the number of different equivalence relationships,
  within a set of (j-1) element, having (j-i) equivalence classes. For example: row 5 =
  [1, 6, 7, 1, 0] means that, in a set of 4 elements, there exists 7 equivalence relationships
  having 3 different equivalence classes.

A151359 (its name line): T(n,k) = number of partitions of [1..k] into n nonempty clumps of sizes
1, 2, 3, 4, 5 or 6 (n >= 0, 0 <= k <= 6n). Here [1..k] is Fin k and a partition is a
Finpartition of Finset.univ (its parts are nonempty by definition).
A151512 has offset 0; its row r (r >= 0) is column k = r of A151359 read upwards:
A151359(r, r), A151359(r-1, r), ..., A151359(0, r). This reproduces all 66 listed terms
(1; 1, 0; 1, 1, 0; 1, 3, 1, 0; 1, 6, 7, 1, 0; ...) and the entry's Mathematica program.
The comment counts rows and elements from 1 (its row 5 is [1, 6, 7, 1, 0], the row r = 4), so
the i-th element of row j is A151512(j-1, i-1). An equivalence relation on a set is the same as
the partition of the set into its classes, so the number of equivalence relations on an m-element
set with c classes is the number of partitions of Fin m into c blocks (eqRel m c below).
The statement is the conjecture, the printed row 5 and the printed count of the example.
Computed (not part of the statement): rows 1 to 7 (counted from 1) agree with the conjecture,
while row 8 is [1, 21, 140, 350, 301, 63, 0, 0], whose 7th element is 0 although there is one
equivalence relation with one class on a 7-element set. The example's count is a slip: a set of
4 elements has 6 equivalence relations with 3 classes and 7 with 2 classes (j - i = 5 - 3 = 2).
-/

namespace OMA.S_oeis_a151512

/-- A151359: T(n,k) = the number of partitions of [1..k] (here Fin k) into n nonempty clumps of
sizes 1, 2, 3, 4, 5 or 6. -/
noncomputable def A151359 (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin k)))).filter
    (fun P => P.parts.card = n ∧ ∀ b ∈ P.parts, 1 ≤ b.card ∧ b.card ≤ 6)).card

/-- A151512, row r (offset 0), position t (0 <= t <= r): the triangle A151359 read by rows upwards,
i.e. row r is A151359(r, r), A151359(r-1, r), ..., A151359(0, r). -/
noncomputable def A151512 (r t : ℕ) : ℕ := A151359 (r - t) r

/-- The number of equivalence relations on an m-element set with c equivalence classes, i.e. the
number of partitions of Fin m into c blocks. -/
noncomputable def eqRel (m c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin m)))).filter
    (fun P => P.parts.card = c)).card

/-- The comment as printed: the conjecture (rows j and elements i counted from 1), the row 5 of
the example, and the example's count of equivalence relations. -/
theorem main :
    (∀ j i : ℕ, 1 ≤ i → i ≤ j → A151512 (j - 1) (i - 1) = eqRel (j - 1) (j - i)) ∧
    (A151512 4 0 = 1 ∧ A151512 4 1 = 6 ∧ A151512 4 2 = 7 ∧ A151512 4 3 = 1 ∧
      A151512 4 4 = 0) ∧
    eqRel 4 3 = 7 := by
  sorry

end OMA.S_oeis_a151512
