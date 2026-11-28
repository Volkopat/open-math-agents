import Mathlib

/-!
# A077220: a(1) = 1; thereafter a(n) is smallest number not occurring earlier such that a(n-1)+a(n) is a triangular number.

Source: https://oeis.org/A077220
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectured to be a permutation of the natural numbers (cf. A099130).
The first few fixed points are: 1, 2, 19, 92, 220, 467, 556, 616, 690, 842.
-/

namespace OMA.S_oeis_a077220

/-- `m` is a triangular number. -/
def isTriangular (m : ℕ) : Prop :=
  ∃ k : ℕ, 2 * m = k * (k + 1)

/-- One step of the sequence state `(current term, set of terms used so far)`. -/
noncomputable def step (st : ℕ × Finset ℕ) : ℕ × Finset ℕ :=
  let m := sInf { m : ℕ | 1 ≤ m ∧ m ∉ st.2 ∧ isTriangular (st.1 + m) }
  (m, insert m st.2)

/-- The `n`-th term of A077220 (0-indexed, with `a 0 = 1`). -/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.iterate step n (1, {1})).1

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∃! n : ℕ, a n = m := by sorry

end OMA.S_oeis_a077220
