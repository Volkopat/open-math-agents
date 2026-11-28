import Mathlib

/-!
# Catalan enumeration of inversion sequences avoiding 110, 120, and 021

OEIS A279557 records the exact formula for every length starting with zero.
Martinez and Savage proved it in Theorem 58 of *Patterns in Inversion Sequences
II*, Journal of Integer Sequences 21 (2018), article 18.2.2.
https://oeis.org/A279557
https://cs.uwaterloo.ca/journals/JIS/VOL21/Martinez/mart2.pdf
-/

namespace OMA.S_oeis_a279557

/-- At zero-based position i, an inversion sequence takes a value from 0 to i. -/
abbrev InversionSeq (n : ℕ) := (i : Fin n) → Fin (i.val + 1)

/-- An earlier value at most the middle value must equal the last value
whenever the middle value exceeds the last one. -/
def Avoids {n : ℕ} (e : InversionSeq n) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → (e i).val ≤ (e j).val →
    (e k).val < (e j).val → (e i).val = (e k).val

noncomputable def count (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (InversionSeq n)).filter Avoids).card

/-- The additive form of the Catalan formula avoids truncated subtraction. -/
theorem main : ∀ n : ℕ, count n + ∑ i ∈ Finset.Icc 1 n, catalan i = catalan (n+1) := by
  sorry

end OMA.S_oeis_a279557
