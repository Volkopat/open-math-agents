import Mathlib

/-!
# Some questions on the Collatz conjecture (reexpressed as an equivalence relation)

Source: https://mathoverflow.net/questions/226001
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `f(n) = n/2` for even `n` and `3n + 1` for odd `n` on the positive integers, and let
`m ∼ n` iff `f^{N₁}(m) = f^{N₂}(n)` for some `N₁, N₂`. The question asks how to prove that `∼` has
only finitely many equivalence classes (a weakening of the Collatz conjecture, which says there
is exactly one class). This file states that claim.

Formalized: finitely many classes means there is a finite set `F` of positive integers such that
every positive integer is equivalent to some element of `F`.
-/

namespace OMA.S_mo_226001

/-- The Collatz map. -/
def f (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The equivalence `m ∼ n`. -/
def Equiv' (m n : ℕ) : Prop := ∃ N₁ N₂ : ℕ, f^[N₁] m = f^[N₂] n

theorem main : ∃ F : Finset ℕ, (∀ m ∈ F, 0 < m) ∧ ∀ n : ℕ, 0 < n → ∃ m ∈ F, Equiv' m n := by
  sorry

end OMA.S_mo_226001
