import Mathlib

/-!
# A073608: Greedy sequence whose pairwise differences are prime powers > 1

Source: https://oeis.org/A073608
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(1) = 1, a(n) = smallest number such that a(n) - a(n-k) is a prime power > 1 for all k.
Conjecture: The sequence is bounded (terminates after finitely many terms).
-/

namespace OMA.S_oeis_a073608

open scoped Classical

/-- The greedy sequence `seq` (0-indexed, `seq 0 = some 1`), returning `none` once
no further term exists whose differences with all previous terms are prime powers `> 1`. -/
noncomputable def seq (n : ℕ) : Option ℕ :=
  Nat.strongRecOn n fun m ih =>
    match m with
    | 0 => some 1
    | m' + 1 =>
      let S : Set ℕ :=
        { x : ℕ | ∀ k (hk : k < m' + 1), ∀ v : ℕ,
          ih k hk = some v → v < x ∧ IsPrimePow (x - v) }
      if (∀ k (hk : k < m' + 1), (ih k hk).isSome) ∧ S.Nonempty then
        some (sInf S)
      else
        none

theorem main :
    ∃ B : ℕ, ∀ n v : ℕ, seq n = some v → v ≤ B := by
  sorry

end OMA.S_oeis_a073608
