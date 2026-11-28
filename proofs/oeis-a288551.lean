import OMAStatements.S_oeis_a288551

-- Problem: A288551: 0-limiting word of the mapping 00->0101, 1->011, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288551.lean:0 (declaration OMA.S_oeis_a288551.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write words as blocks A = 00, B = 1, C = 01 (flat). Whatever follows, the mapping
-- sends 00 to 0101 = C C, 1 to 011 = C B, and 01 (a 0 followed by 1 is kept) to 0011 = A B B, so
-- step (flat ts) = flat (mu ts) with mu: A -> C C, B -> C B, C -> A B B, and w(0) = flat [A].
-- With block counts (a, b, c) the length is 2a + b + 2c, and one step maps (a, b, c) to
-- (c, b + 2c, 2a + b); three steps give the lengths 4a+3b+4c, 8a+7b+10c, 20a+17b+22c, so
-- L(n+3) = L(n+2) + 4L(n+1) - 2L(n), the recurrence of A288476, with the same values 2, 4, 8.

namespace FS1A288551

open OMA.S_oeis_a288551

inductive Tok
  | A
  | B
  | C

/-- Blocks to letters: A is 00, B is 1, C is 01. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.A :: ts => false :: false :: flat ts
  | Tok.B :: ts => true :: flat ts
  | Tok.C :: ts => false :: true :: flat ts

/-- The mapping on blocks: A -> C C, B -> C B, C -> A B B. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.A :: ts => Tok.C :: Tok.C :: mu ts
  | Tok.B :: ts => Tok.C :: Tok.B :: mu ts
  | Tok.C :: ts => Tok.A :: Tok.B :: Tok.B :: mu ts

def cA : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cA ts + 1
  | Tok.B :: ts => cA ts
  | Tok.C :: ts => cA ts

def cB : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cB ts
  | Tok.B :: ts => cB ts + 1
  | Tok.C :: ts => cB ts

def cC : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cC ts
  | Tok.B :: ts => cC ts
  | Tok.C :: ts => cC ts + 1

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: false :: true :: step r := rfl

theorem step_1 (r : List Bool) : step (true :: r) = false :: true :: true :: step r := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem key (ts : List Tok) : step (flat ts) = flat (mu ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show step (false :: false :: flat ts) = false :: true :: false :: true :: flat (mu ts)
      rw [step_00, ih]
    | B =>
      show step (true :: flat ts) = false :: true :: true :: flat (mu ts)
      rw [step_1, ih]
    | C =>
      show step (false :: true :: flat ts) = false :: false :: true :: true :: flat (mu ts)
      rw [step_01, step_1, ih]

theorem w_flat : ∀ n : ℕ, ∃ ts : List Tok, w n = flat ts
  | 0 => ⟨[Tok.A], rfl⟩
  | n + 1 => by
    obtain ⟨ts, h⟩ := w_flat n
    refine ⟨mu ts, ?_⟩
    show step (w n) = flat (mu ts)
    rw [h, key]

theorem len_flat (ts : List Tok) : (flat ts).length = 2 * cA ts + cB ts + 2 * cC ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show (false :: false :: flat ts).length = 2 * (cA ts + 1) + cB ts + 2 * cC ts
      rw [List.length_cons, List.length_cons]
      omega
    | B =>
      show (true :: flat ts).length = 2 * cA ts + (cB ts + 1) + 2 * cC ts
      rw [List.length_cons]
      omega
    | C =>
      show (false :: true :: flat ts).length = 2 * cA ts + cB ts + 2 * (cC ts + 1)
      rw [List.length_cons, List.length_cons]
      omega

theorem cA_mu (ts : List Tok) : cA (mu ts) = cC ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show cA (mu ts) = cC ts
      exact ih
    | B =>
      show cA (mu ts) = cC ts
      exact ih
    | C =>
      show cA (mu ts) + 1 = cC ts + 1
      omega

theorem cB_mu (ts : List Tok) : cB (mu ts) = cB ts + 2 * cC ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show cB (mu ts) = cB ts + 2 * cC ts
      exact ih
    | B =>
      show cB (mu ts) + 1 = cB ts + 1 + 2 * cC ts
      omega
    | C =>
      show cB (mu ts) + 1 + 1 = cB ts + 2 * (cC ts + 1)
      omega

theorem cC_mu (ts : List Tok) : cC (mu ts) = 2 * cA ts + cB ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show cC (mu ts) + 1 + 1 = 2 * (cA ts + 1) + cB ts
      omega
    | B =>
      show cC (mu ts) + 1 = 2 * cA ts + (cB ts + 1)
      omega
    | C =>
      show cC (mu ts) = 2 * cA ts + cB ts
      exact ih

theorem len_rec (n : ℕ) : ((w (n + 3)).length : ℤ) =
    ((w (n + 2)).length : ℤ) + 4 * ((w (n + 1)).length : ℤ) - 2 * ((w n).length : ℤ) := by
  obtain ⟨ts, h0⟩ := w_flat n
  have h1 : w (n + 1) = flat (mu ts) := by
    rw [show w (n + 1) = step (w n) from rfl, h0, key]
  have h2 : w (n + 2) = flat (mu (mu ts)) := by
    rw [show w (n + 2) = step (w (n + 1)) from rfl, h1, key]
  have h3 : w (n + 3) = flat (mu (mu (mu ts))) := by
    rw [show w (n + 3) = step (w (n + 2)) from rfl, h2, key]
  rw [h3, h2, h1, h0]
  simp only [len_flat, cA_mu, cB_mu, cC_mu]
  push_cast
  ring

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A288476 n ∧ ((w (n + 1)).length : ℤ) = A288476 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A288476 (n + 2)
  | 0 => ⟨by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h0, h1, h2⟩ := len_eq n
    refine ⟨h1, h2, ?_⟩
    show ((w (n + 3)).length : ℤ) = A288476 (n + 3)
    have hA : A288476 (n + 3) = A288476 (n + 2) + 4 * A288476 (n + 1) - 2 * A288476 n := rfl
    rw [hA, ← h2, ← h1, ← h0]
    exact len_rec n

end FS1A288551

open OMA.S_oeis_a288551 FS1A288551 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288551.main := by
  intro n
  exact (len_eq n).1
