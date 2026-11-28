import FormalConjectures.Wikipedia.LittlewoodConjecture

-- Reduction LittlewoodConjecture.littlewood_conjecture.R1 of the Littlewood conjecture
-- Credit: @marcusbuffett

/-!
# The Littlewood conjecture: the rational case, and the open rest

The conjecture says `liminf n ‖nα‖ ‖nβ‖ = 0` for all real `α, β`, where `‖x‖` is the distance to
the nearest integer.

* `H1` (elementary): the statement when `α` is rational. Along the multiples `n` of the
  denominator of `α` the factor `‖nα‖` vanishes, and all terms are nonnegative. `main` uses it
  for a rational `β` as well, by symmetry.
* `H2`: the statement when `α` and `β` are both irrational. This is the open conjecture.
  (It is known when `α` or `β` has unbounded partial quotients after a suitable normalisation,
  and the set of exceptions has Hausdorff dimension zero by Einsiedler, Katok and Lindenstrauss;
  none of that is used here.)
-/

namespace OMA.R_LittlewoodConjecture_littlewood_conjecture_R1

open Filter

/-- The case of a rational `α`. -/
def H1 : Prop :=
  ∀ α β : ℝ, (∃ q : ℚ, α = q) →
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0

/-- The open part: both numbers irrational. -/
def H2 : Prop :=
  ∀ α β : ℝ, Irrational α → Irrational β →
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0

theorem main : H1 → H2 → type_of% @LittlewoodConjecture.littlewood_conjecture := by
  intro h1 h2 α β
  by_cases ha : Irrational α
  · by_cases hb : Irrational β
    · exact h2 α β ha hb
    · have hmem : β ∈ Set.range ((↑) : ℚ → ℝ) := by
        by_contra h
        exact hb h
      obtain ⟨q, hq⟩ := hmem
      have h := h1 β α ⟨q, hq.symm⟩
      have hfun : (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) =
          (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * β) * distToNearestInt (n * α)) := by
        funext n
        ring
      rw [hfun]
      exact h
  · have hmem : α ∈ Set.range ((↑) : ℚ → ℝ) := by
      by_contra h
      exact ha h
    obtain ⟨q, hq⟩ := hmem
    exact h1 α β ⟨q, hq.symm⟩

end OMA.R_LittlewoodConjecture_littlewood_conjecture_R1
