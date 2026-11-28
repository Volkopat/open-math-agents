import Mathlib

/-!
# A081319: Smallest squarefree k such that Q(sqrt(-k)) has class number n

Source: https://oeis.org/A081319
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Smallest squarefree integer k such that Q(sqrt(-k)) has class number n, or 0 if no such k exists.
Conjecture: all numbers at even positions are congruent to 2 (mod 3).
-/

namespace OMA.S_oeis_a081319

def fundDisc (k : ℕ) : ℤ :=
  if k % 4 = 3 then -(k : ℤ) else -4 * (k : ℤ)

noncomputable def classNumber (k : ℕ) : ℕ :=
  let D : ℤ := fundDisc k
  let B : ℤ := (D.natAbs : ℤ)
  (((Finset.Icc (1 : ℤ) B) ×ˢ ((Finset.Icc (-B) B) ×ˢ (Finset.Icc (1 : ℤ) B))).filter
    (fun ⟨a, b, c⟩ =>
      b ^ 2 - 4 * a * c = D ∧ -a < b ∧ b ≤ a ∧ a ≤ c ∧ (a = c → 0 ≤ b))).card

/-- Least squarefree `k` with class number `n`; `sInf ∅ = 0` gives the entry's 0 when none exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Squarefree k ∧ classNumber k = n}

theorem main :
    ∀ n : ℕ, 1 ≤ n → Even n → a n % 3 = 2 := by
  sorry

end OMA.S_oeis_a081319
