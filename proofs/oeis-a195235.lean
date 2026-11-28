import OMAStatements.S_oeis_a195235
import Mathlib

/-!
Credit: @ivillar
Proof: entries of a valid array differ by at most 4 (the king-move diameter of the
triangle), so the arrays with entries in 0..m+1 that reach m+1 are exactly the translates by
m-3 of the arrays with entries in 0..4 that reach 4; hence a(m+1) - a(m) is constant
for m >= 3, which gives the recurrence.
-/

namespace OMAA195235Helpers
open OMA.S_oeis_a195235

/-- The cell in row 0, column 0. -/
def c00 : Cell := ⟨(0, 0), by decide⟩

/-- The cell in row 1, column 0. -/
def c10 : Cell := ⟨(1, 0), by decide⟩

/-- The cell in row 1, column 1. -/
def c11 : Cell := ⟨(1, 1), by decide⟩

/-- The cell in row 2, column 0. -/
def c20 : Cell := ⟨(2, 0), by decide⟩

/-- The cell in row 2, column 1. -/
def c21 : Cell := ⟨(2, 1), by decide⟩

/-- The cell in row 2, column 2. -/
def c22 : Cell := ⟨(2, 2), by decide⟩

/-- The cell in row 3, column 0. -/
def c30 : Cell := ⟨(3, 0), by decide⟩

/-- The cell in row 3, column 1. -/
def c31 : Cell := ⟨(3, 1), by decide⟩

/-- The cell in row 3, column 2. -/
def c32 : Cell := ⟨(3, 2), by decide⟩

/-- The cell in row 3, column 3. -/
def c33 : Cell := ⟨(3, 3), by decide⟩

/-- The cell in row 4, column 0. -/
def c40 : Cell := ⟨(4, 0), by decide⟩

/-- The cell in row 4, column 1. -/
def c41 : Cell := ⟨(4, 1), by decide⟩

/-- The cell in row 4, column 2. -/
def c42 : Cell := ⟨(4, 2), by decide⟩

/-- The cell in row 4, column 3. -/
def c43 : Cell := ⟨(4, 3), by decide⟩

/-- The cell in row 4, column 4. -/
def c44 : Cell := ⟨(4, 4), by decide⟩

set_option synthInstance.maxSize 4096 in
theorem cells (p : Cell) : p = c00 ∨ p = c10 ∨ p = c11 ∨ p = c20 ∨ p = c21 ∨ p = c22 ∨ p = c30 ∨ p = c31 ∨ p = c32 ∨ p = c33 ∨ p = c40 ∨ p = c41 ∨ p = c42 ∨ p = c43 ∨ p = c44 := by
  revert p
  decide

theorem span {n : ℕ} (f : Cell → Fin (n + 1)) (hf : Good f) (p q : Cell) :
    (f p : ℤ) ≤ f q + 4 := by
  rcases cells p with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases cells q with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · omega
  · have := (abs_le.mp (hf c00 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c00 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c10 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c10 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c10 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c11 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c11 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c11 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c20 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c20 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c20 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c21 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c21 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c21 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c22 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c22 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c22 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c30 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c30 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c31 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c32 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c32 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c33 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c33 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c40 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c40 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c30 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c30 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c40 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c41 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c20 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c20 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c42 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c10 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c10 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c43 c42 (by unfold Adj; decide))).2; omega
  · omega
  · have := (abs_le.mp (hf c43 c44 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c00 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c11 c10 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c11 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c21 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c21 c20 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c22 c21 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c22 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c31 c30 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c32 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c32 c31 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c33 c32 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c33 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c41 c40 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c42 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c42 c41 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c43 (by unfold Adj; decide))).2; have := (abs_le.mp (hf c43 c42 (by unfold Adj; decide))).2; omega
  · have := (abs_le.mp (hf c44 c43 (by unfold Adj; decide))).2; omega
  · omega

open Classical in
theorem split_card (m : ℕ) :
    Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f} =
      Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∀ p, (f p : ℕ) ≤ m} +
      Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∃ p, (f p : ℕ) = m + 1} := by
  classical
  rw [← Fintype.card_subtype_or_disjoint]
  · exact Fintype.card_congr (Equiv.subtypeEquivRight fun f => by
      constructor
      · intro hf
        by_cases h : ∀ p, (f p : ℕ) ≤ m
        · exact Or.inl ⟨hf, h⟩
        · obtain ⟨p, hp⟩ := not_forall.mp h
          exact Or.inr ⟨hf, p, by have := (f p).2; omega⟩
      · rintro (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact hf)
  · rw [Pi.disjoint_iff]
    intro f
    rw [disjoint_iff]
    simp only [inf_Prop_eq, eq_iff_iff]
    constructor
    · rintro ⟨⟨-, h⟩, -, p, hp⟩
      have := h p
      omega
    · intro h
      exact h.elim

/-- Arrays with all entries at most `m` are the arrays with entries in `0..m`. -/
def lowEquiv (m : ℕ) :
    {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∀ p, (f p : ℕ) ≤ m} ≃
      {g : Cell → Fin (m + 1) // Good g} where
  toFun f := ⟨fun p => ⟨f.1 p, by have := f.2.2 p; omega⟩, fun p q h => by
    have := f.2.1 p q h
    simpa using this⟩
  invFun g := ⟨fun p => ⟨g.1 p, by have := (g.1 p).2; omega⟩, ⟨fun p q h => by
    have := g.2 p q h
    simpa using this, fun p => by have := (g.1 p).2; simp only; omega⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    rfl
  right_inv g := by
    apply Subtype.ext
    funext p
    rfl

/-- Arrays reaching the value `m + 1` are the translates of the arrays with entries in `0..4`
reaching `4` (all their entries are at least `m + 1 - 4`). -/
def highEquiv (m : ℕ) (hm : 3 ≤ m) :
    {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∃ p, (f p : ℕ) = m + 1} ≃
      {g : Cell → Fin 5 // Good g ∧ ∃ p, (g p : ℕ) = 4} where
  toFun f := ⟨fun p => ⟨(f.1 p : ℕ) - (m - 3), by have := (f.1 p).2; omega⟩, by
    obtain ⟨hf, p0, hp0⟩ := f.2
    have lo : ∀ p, m - 3 ≤ (f.1 p : ℕ) := fun p => by
      have := span f.1 hf p0 p
      omega
    refine ⟨fun p q h => ?_, p0, ?_⟩
    · have := hf p q h
      have h1 := lo p
      have h2 := lo q
      dsimp only
      rw [abs_le] at this ⊢
      constructor <;> push_cast [h1, h2] <;> omega
    · dsimp only
      omega⟩
  invFun g := ⟨fun p => ⟨(g.1 p : ℕ) + (m - 3), by have := (g.1 p).2; omega⟩, by
    obtain ⟨hg, p0, hp0⟩ := g.2
    refine ⟨fun p q h => ?_, p0, ?_⟩
    · have := hg p q h
      dsimp only
      rw [abs_le] at this ⊢
      constructor <;> push_cast <;> omega
    · dsimp only
      omega⟩
  left_inv f := by
    obtain ⟨f, hf, p0, hp0⟩ := f
    apply Subtype.ext
    funext p
    apply Fin.ext
    have := span f hf p0 p
    dsimp only
    omega
  right_inv g := by
    apply Subtype.ext
    funext p
    apply Fin.ext
    dsimp only
    omega

open Classical in
theorem step (m : ℕ) (hm : 3 ≤ m) :
    (a (m + 1) : ℤ) = a m +
      Fintype.card {g : Cell → Fin 5 // Good g ∧ ∃ p, (g p : ℕ) = 4} := by
  classical
  unfold a
  rw [split_card, Fintype.card_congr (lowEquiv m), Fintype.card_congr (highEquiv m hm)]
  push_cast
  ring

end OMAA195235Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a195235.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have h1 := OMAA195235Helpers.step (m + 1) (by omega)
  have h2 := OMAA195235Helpers.step m (by omega)
  rw [show m + 1 + 1 = m + 2 by omega] at h1
  linarith
