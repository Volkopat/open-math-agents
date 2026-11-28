import Mathlib

/-!
# A083518: Beginning with 3, a(i)*a(j) + 2 is prime for all i, j, i != j.

Source: https://oeis.org/A083518
Credit: @gblacher2

Conjecture (comment in A083518): "sequence is finite."

Conventions:
* the sequence is the greedy increasing one, as its data shows (3, 5, 7, 27, 45, 495, ...):
  a(1) = 3 and each next term is the least number larger than all earlier terms whose product
  with every earlier term, plus 2, is prime. The increasing reading matters: without it, 1 would
  qualify as the third term;
* since a term may fail to exist, the sequence is encoded by its finite initial segments:
  `IsPrefix s` says that the list `s` is `[a(1), ..., a(k)]` for some `k ≥ 1`. The recursion
  pins each segment down uniquely;
* "the sequence is finite" means that the initial segments have bounded length, that is, from
  some point on no next term exists.
-/

namespace OMA.S_oeis_a083518

/-- `m` may follow the terms `s`: it is larger than each of them and `x * m + 2` is prime for
every term `x` in `s`. -/
def CanFollow (s : List ℕ) (m : ℕ) : Prop :=
  (∀ x ∈ s, x < m) ∧ ∀ x ∈ s, (x * m + 2).Prime

/-- `IsPrefix s`: the list `s` is an initial segment `[a(1), ..., a(k)]` of A083518, where
`a(1) = 3` and every next term is the least number that may follow the previous ones. -/
inductive IsPrefix : List ℕ → Prop
  | base : IsPrefix [3]
  | step {s : List ℕ} {m : ℕ} : IsPrefix s → IsLeast {k : ℕ | CanFollow s k} m →
      IsPrefix (s ++ [m])

/-- The conjecture: A083518 is finite, i.e. its initial segments have bounded length. -/
theorem main : ∃ N : ℕ, ∀ s : List ℕ, IsPrefix s → s.length ≤ N := by
  sorry

end OMA.S_oeis_a083518
