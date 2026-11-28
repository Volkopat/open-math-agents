import OMAStatements.S_oeis_a109095
import Mathlib

-- Reduction oeis-a109095.R1 of OEIS A109095 (Surányi's conjecture on N! = a! b!)
-- Credit: @marcusbuffett

/-!
# Surányi's conjecture: Bertrand's postulate, the trivial case, and the open rest

The conjecture says that `N! = a! b!` with `2 ≤ a, b < N` forces `N = 10` or `N` a factorial.
This separates the elementary part from the open part. It is a classical partial result, not
progress on the conjecture itself.

* `H1` (proved): for a solution with `a ≤ b`, `N < 2b`, and if `N = b + 1` then `N = a!`. Proof:
  by Bertrand's postulate there is a prime `p` with `b < p ≤ 2b`; if `N ≥ 2b` then `p ∣ N!` but
  `p ∤ a! b!` since `a ≤ b < p`. If `N = b + 1` then `(b+1) b! = a! b!` gives `b + 1 = a!`.
* `H2`: every solution with `a ≤ b` and `b + 2 ≤ N < 2b` has `N = 10` or `N` a factorial. This
  is the open rest of the conjecture (`10! = 6! 7!` is the known solution of this kind).
-/

namespace OMA.R_oeis_a109095_R1

/-- Bertrand's bound `N < 2b` and the trivial case `N = b + 1`. -/
def H1 : Prop :=
  ∀ N a b : ℕ, 2 ≤ a → a < N → 2 ≤ b → b < N →
    Nat.factorial N = Nat.factorial a * Nat.factorial b → a ≤ b →
    N < 2 * b ∧ (N = b + 1 → N = Nat.factorial a)

/-- The open rest: solutions with `a ≤ b` and `b + 2 ≤ N < 2b`. -/
def H2 : Prop :=
  ∀ N a b : ℕ, 2 ≤ a → a < N → 2 ≤ b → b < N →
    Nat.factorial N = Nat.factorial a * Nat.factorial b → a ≤ b → b + 2 ≤ N → N < 2 * b →
    N = 10 ∨ ∃ x : ℕ, N = Nat.factorial x

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a109095.main := by
  intro h1 h2 N a b ha haN hb hbN h
  -- order the two factorials
  have key : ∀ a b : ℕ, 2 ≤ a → a < N → 2 ≤ b → b < N →
      Nat.factorial N = Nat.factorial a * Nat.factorial b → a ≤ b →
      N = 10 ∨ ∃ x : ℕ, N = Nat.factorial x := by
    intro a b ha haN hb hbN h hab
    obtain ⟨hlt, htriv⟩ := h1 N a b ha haN hb hbN h hab
    by_cases hN : N = b + 1
    · exact Or.inr ⟨a, htriv hN⟩
    · exact h2 N a b ha haN hb hbN h hab (by omega) hlt
  rcases le_total a b with hab | hab
  · exact key a b ha haN hb hbN h hab
  · exact key b a hb hbN ha haN (by rw [h, mul_comm]) hab

end OMA.R_oeis_a109095_R1
