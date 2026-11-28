import Mathlib

/-!
# A065603: transposition diameter

Source: https://oeis.org/A065603
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Eriksson et al. 2001, listed in A065603): `a(n) = ⌈(n+1)/2⌉` for `n ≥ 3` except for
`n = 13` and `15`, where `a(n)` is the transposition diameter: the maximal number of moves in an
optimal sorting of `n` objects by moving blocks.

Conventions:
* A move (block transposition) exchanges two adjacent nonempty blocks:
  `A ++ B ++ C ++ D ↦ A ++ C ++ B ++ D`. The sorting distance of an arrangement of `0, …, n-1` is
  the least number of moves reaching `[0, 1, …, n-1]`, and `a(n)` is the maximum over all `n!`
  arrangements.
-/

namespace OMA.S_oeis_a065603

/-- One block transposition. -/
def Move (l l' : List ℕ) : Prop :=
  ∃ A B C D : List ℕ, B ≠ [] ∧ C ≠ [] ∧ l = A ++ B ++ C ++ D ∧ l' = A ++ C ++ B ++ D

/-- `l` reaches `l'` in exactly `k` moves. -/
def Reach : ℕ → List ℕ → List ℕ → Prop
  | 0, l, l' => l = l'
  | k + 1, l, l' => ∃ m, Move l m ∧ Reach k m l'

/-- Sorting distance of an arrangement of `0, …, n-1`. -/
noncomputable def dist (n : ℕ) (l : List ℕ) : ℕ := sInf {k | Reach k l (List.range n)}

/-- The transposition diameter. -/
noncomputable def a (n : ℕ) : ℕ := sSup {d | ∃ l : List ℕ, l.Perm (List.range n) ∧ d = dist n l}

theorem main : ∀ n : ℕ, 3 ≤ n → n ≠ 13 → n ≠ 15 → a n = (n + 2) / 2 := by
  sorry

end OMA.S_oeis_a065603
