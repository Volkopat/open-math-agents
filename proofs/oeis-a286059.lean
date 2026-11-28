import OMAStatements.S_oeis_a286059

-- Problem: A286059: Fixed point of the mapping 00->001, 1->011, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a286059.lean:0 (declaration OMA.S_oeis_a286059.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write words as blocks A = 00, B = 1, C = 01 (flat). Whatever follows, the mapping
-- sends 00 to 001 = A B, 1 to 011 = C B, and 01 (a 0 followed by 1 is kept) to 0011 = A B B, so
-- step (flat ts) = flat (mu ts) with mu: A -> A B, B -> C B, C -> A B B, and w(0) = flat [A].
-- With block counts (a, b, c) the length is 2a + b + 2c, and one step maps (a, b, c) to
-- (a + c, a + b + 2c, b); three steps give the lengths 3a+3b+4c, 6a+7b+9c, 13a+16b+20c, so
-- L(n+3) = 2L(n+2) + L(n+1) - L(n), the recurrence of A286062, with the same values 2, 3, 6.

namespace FS5A286059

open OMA.S_oeis_a286059

inductive Tok
  | A
  | B
  | C
  deriving DecidableEq

/-- Blocks to letters: A is 00, B is 1, C is 01. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.A :: ts => false :: false :: flat ts
  | Tok.B :: ts => true :: flat ts
  | Tok.C :: ts => false :: true :: flat ts

/-- The mapping on blocks: A -> A B, B -> C B, C -> A B B. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.A :: ts => Tok.A :: Tok.B :: mu ts
  | Tok.B :: ts => Tok.C :: Tok.B :: mu ts
  | Tok.C :: ts => Tok.A :: Tok.B :: Tok.B :: mu ts

open Tok

theorem key (ts : List Tok) : step (flat ts) = flat (mu ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp only [flat, mu, step, ih]

def blocks : ℕ → List Tok
  | 0 => [A]
  | n + 1 => mu (blocks n)

theorem w_flat (n : ℕ) : w n = flat (blocks n) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [w, blocks, ih] using key (blocks n)

theorem len_flat (ts : List Tok) : (flat ts).length = 2 * ts.count A + ts.count B + 2 * ts.count C := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [flat, ih] <;> omega

theorem cA_mu (ts : List Tok) : (mu ts).count A = ts.count A + ts.count C := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [mu, ih] <;> omega

theorem cB_mu (ts : List Tok) : (mu ts).count B = ts.count A + ts.count B + 2 * ts.count C := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [mu, ih] <;> omega

theorem cC_mu (ts : List Tok) : (mu ts).count C = ts.count B := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [mu, ih]

theorem len_rec (n : ℕ) : ((w (n + 3)).length : ℤ) =
    2 * ((w (n + 2)).length : ℤ) + ((w (n + 1)).length : ℤ) - ((w n).length : ℤ) := by
  simp only [w_flat, blocks, len_flat, cA_mu, cB_mu, cC_mu]
  push_cast
  ring

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A286062 n ∧ ((w (n + 1)).length : ℤ) = A286062 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A286062 (n + 2)
  | 0 => ⟨by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h0, h1, h2⟩ := len_eq n
    refine ⟨h1, h2, ?_⟩
    show ((w (n + 3)).length : ℤ) = A286062 (n + 3)
    have hA : A286062 (n + 3) = 2 * A286062 (n + 2) + A286062 (n + 1) - A286062 n := rfl
    rw [hA, ← h2, ← h1, ← h0]
    exact len_rec n

end FS5A286059

open OMA.S_oeis_a286059 FS5A286059 in
theorem OMA.solution : type_of% @OMA.S_oeis_a286059.main := by
  intro n
  exact (len_eq n).1
