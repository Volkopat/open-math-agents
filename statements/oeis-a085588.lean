import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Bitwise

/-!
# Rule 150 on a cyclic ring

This file states Roman Khrabrov's explicit one-dimensional conjecture
(August 17, 2024): every width n at which the single-seed eventual period
equals n belongs to A115770. A085588 has offset 3.

Sources: https://oeis.org/A085588 and https://oeis.org/A115770
-/

namespace OMA.S_oeis_a085588

/-- The XOR of the left neighbor, center, and right neighbor at every site. -/
def step {n : ℕ} (w : BitVec n) : BitVec n :=
  w.rotateLeft 1 ^^^ w ^^^ w.rotateRight 1

/-- The initial configuration has exactly bit zero occupied at positive widths. -/
def row (n t : ℕ) : BitVec n := step^[t] (1 : BitVec n)

/-- Least positive time shift returning an entire labeled configuration
somewhere along the single-seed orbit. -/
noncomputable def period (n : ℕ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ ∃ t : ℕ, row n (t+p) = row n t}

/-- The carryless product by binary 1011 XORs shifts 0, 1, and 3. -/
def InA115770 (n : ℕ) : Prop := 7*n = n ^^^ (2*n) ^^^ (8*n)

theorem main : ∀ n : ℕ, 3 ≤ n → period n = n → InA115770 n := by
  sorry

end OMA.S_oeis_a085588
