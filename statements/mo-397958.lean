import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

/-!
# Arithmetic sets need not be unions of endpoint progressions

Source: https://mathoverflow.net/questions/397958/structure-of-certain-arithmetic-sets
Question by richrow, 20 July 2021. CC BY-SA 4.0.
Credit: @etaubman

This states the source's explicit conjecture that every finite symmetric
arithmetic set is a union of arithmetic progressions containing both -1 and 1.
It does not formalize the broader open-ended request to classify all such sets.
The source comment by Terry Tao gives a broad family of arithmetic sets; the
counterexample used in the accompanying proof is the N=4 instance of that
family with only zero retained in the middle third. No novelty is claimed.

Every finite progression contained in [-1,1] and containing both endpoints
can be ordered as -1 + 2*i/n for 0 <= i <= n, n > 0. A union of such
progressions is equivalently a set whose every point belongs to one of these
progressions entirely contained in the set. Those are the definitions below.
-/

namespace OMA.S_mo_397958

/-- A finite symmetric arithmetic set in the source's sense. -/
def ArithmeticSet (A : Finset ℝ) : Prop :=
  (∀ a ∈ A, -1 ≤ a ∧ a ≤ 1) ∧ (-1 ∈ A) ∧ (1 ∈ A) ∧
  (∀ a, a ∈ A ↔ -a ∈ A) ∧
  ∀ a ∈ A, a ≠ -1 → a ≠ 1 →
    ∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ 2 * a = b + c

/-- The finite arithmetic progression with endpoints -1 and 1 and n steps. -/
noncomputable def endpointAP (n : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range (n + 1)).image (fun (i : ℕ) => -1 + 2 * (i : ℝ) / n)

/-- A union of progressions each containing both endpoints. Since the set lies
in [-1,1], every such progression has precisely those endpoints. -/
def HasEndpointAPCover (A : Finset ℝ) : Prop :=
  ∀ a ∈ A, ∃ n : ℕ, 0 < n ∧ a ∈ endpointAP n ∧ endpointAP n ⊆ A

theorem main : ∀ A : Finset ℝ, ArithmeticSet A → HasEndpointAPCover A := by
  sorry

end OMA.S_mo_397958
