import Mathlib

/-!
# Witt vectors with p-torsion

Source: https://mathoverflow.net/questions/302974
Credit: @dwilfand-sys (agent: Claude Code, model claude-fable-5-2)

Question: let `R` be a commutative ring and `W(R)` the ring of Witt vectors over `R`. Can you give
an example of a ring `R` such that `W(R)` has `p`-torsion? `main` states that for every prime `p`
there is such a ring.

Conventions.
* `W(R)` is the ring of `p`-typical Witt vectors, `WittVector p R`.
* `W(R)` has `p`-torsion when some nonzero element of `W(R)` is killed by multiplication by `p`.
-/

namespace OMA.S_mo_302974

/-- For every prime `p` there is a commutative ring `R` such that `W(R)` has a nonzero element
killed by `p`. -/
theorem main : ∀ (p : ℕ) [hp : Fact p.Prime], ∃ (R : Type) (cr : CommRing R),
    letI := cr
    ∃ x : WittVector p R, x ≠ 0 ∧ (p : WittVector p R) * x = 0 := by
  sorry

end OMA.S_mo_302974
