import OMAReductions.R_LittlewoodConjecture_littlewood_conjecture_R1

-- Reduction LittlewoodConjecture.littlewood_conjecture.R1.H2.R1
-- of step LittlewoodConjecture.littlewood_conjecture.R1.H2
-- Credit: @marcusbuffett

/-!
# The Littlewood conjecture is only open for pairs of badly approximable numbers

The parent step is the conjecture for irrational `α` and `β`. Write `‖x‖` for the distance to the
nearest integer.

* `H1` (classical remark): if `n ‖nα‖` takes arbitrarily small values along infinitely many `n`
  (that is, `α` is not badly approximable), then `liminf n ‖nα‖ ‖nβ‖ = 0` for every `β`, because
  `‖nβ‖ ≤ 1/2`. `main` uses it for `β` as well, by symmetry.
* `H2`: the conjecture when both `α` and `β` are badly approximable, that is `n ‖nα‖ ≥ ε` and
  `n ‖nβ‖ ≥ ε'` for all large `n`. This is the open part (by Einsiedler, Katok and Lindenstrauss
  the exceptions form a set of Hausdorff dimension zero).
-/

namespace OMA.R_LittlewoodConjecture_littlewood_conjecture_R1_H2_R1

open Filter

/-- If `α` is not badly approximable the conjecture holds for `(α, β)`. -/
def H1 : Prop :=
  ∀ α β : ℝ, (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε) →
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0

/-- The open part: both numbers badly approximable. -/
def H2 : Prop :=
  ∀ α β : ℝ, Irrational α → Irrational β →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, ε ≤ n * distToNearestInt (n * α)) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, ε ≤ n * distToNearestInt (n * β)) →
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0

lemma bad_of_not {γ : ℝ}
    (h : ¬ ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * γ) < ε) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, ε ≤ n * distToNearestInt (n * γ) := by
  push Not at h
  obtain ⟨ε, hε, hn⟩ := h
  exact ⟨ε, hε, hn⟩

theorem main : H1 → H2 → OMA.R_LittlewoodConjecture_littlewood_conjecture_R1.H2 := by
  intro h1 h2 α β hα hβ
  by_cases ha : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε
  · exact h1 α β ha
  by_cases hb : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * β) < ε
  · have h := h1 β α hb
    have hfun : (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) =
        (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * β) * distToNearestInt (n * α)) := by
      funext n
      ring
    rw [hfun]
    exact h
  exact h2 α β hα hβ (bad_of_not ha) (bad_of_not hb)

end OMA.R_LittlewoodConjecture_littlewood_conjecture_R1_H2_R1
