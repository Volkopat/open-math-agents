import OMAStatements.S_oeis_a288596

-- Problem: A288596: Fixed point of the mapping 00->0101, 10->1000, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288596.lean:0 (declaration OMA.S_oeis_a288596.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: from w(1) = 0101 on, every iterate is 0 followed by blocks U0 = 1, U1 = 10,
-- U3 = 1000, U4 = 10000. If the next letter is 1 or the word ends, the mapping sends 1 to 1,
-- 10 to 1000 = U3, 1000 to 1000 0101 = U4 U1 U0 and 10000 to 1000 0101 0 = U4 U1 U1, and the
-- leading 0 (followed by 1) to 0; so step (0 flat ts) = 0 flat (mu ts). With block counts
-- (p, q, r, s) of U0, U1, U3, U4 the length is 1 + p + 2q + 4r + 5s, and one step maps the counts
-- to (p + r, r + 2s, q, r + s), whose characteristic polynomial is t^4 - 2t^3 + 1. So
-- L(n+5) = 2L(n+4) - L(n+1) for n >= 0, the recurrence of A288599, with the same first values.

namespace FS1A288596

open OMA.S_oeis_a288596

inductive Tok
  | U0
  | U1
  | U3
  | U4

/-- Blocks to letters: U0 is 1, U1 is 10, U3 is 1000, U4 is 10000. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.U0 :: ts => true :: flat ts
  | Tok.U1 :: ts => true :: false :: flat ts
  | Tok.U3 :: ts => true :: false :: false :: false :: flat ts
  | Tok.U4 :: ts => true :: false :: false :: false :: false :: flat ts

/-- The mapping on blocks: U0 -> U0, U1 -> U3, U3 -> U4 U1 U0, U4 -> U4 U1 U1. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.U0 :: ts => Tok.U0 :: mu ts
  | Tok.U1 :: ts => Tok.U3 :: mu ts
  | Tok.U3 :: ts => Tok.U4 :: Tok.U1 :: Tok.U0 :: mu ts
  | Tok.U4 :: ts => Tok.U4 :: Tok.U1 :: Tok.U1 :: mu ts

def c0 : List Tok → ℕ
  | [] => 0
  | Tok.U0 :: ts => c0 ts + 1
  | Tok.U1 :: ts => c0 ts
  | Tok.U3 :: ts => c0 ts
  | Tok.U4 :: ts => c0 ts

def c1 : List Tok → ℕ
  | [] => 0
  | Tok.U0 :: ts => c1 ts
  | Tok.U1 :: ts => c1 ts + 1
  | Tok.U3 :: ts => c1 ts
  | Tok.U4 :: ts => c1 ts

def c3 : List Tok → ℕ
  | [] => 0
  | Tok.U0 :: ts => c3 ts
  | Tok.U1 :: ts => c3 ts
  | Tok.U3 :: ts => c3 ts + 1
  | Tok.U4 :: ts => c3 ts

def c4 : List Tok → ℕ
  | [] => 0
  | Tok.U0 :: ts => c4 ts
  | Tok.U1 :: ts => c4 ts
  | Tok.U3 :: ts => c4 ts
  | Tok.U4 :: ts => c4 ts + 1

theorem flat_head : ∀ ts : List Tok, flat ts = [] ∨ ∃ r, flat ts = true :: r
  | [] => Or.inl rfl
  | Tok.U0 :: ts => Or.inr ⟨flat ts, rfl⟩
  | Tok.U1 :: ts => Or.inr ⟨false :: flat ts, rfl⟩
  | Tok.U3 :: ts => Or.inr ⟨false :: false :: false :: flat ts, rfl⟩
  | Tok.U4 :: ts => Or.inr ⟨false :: false :: false :: false :: flat ts, rfl⟩

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: false :: true :: step r := rfl

theorem step_10 (r : List Bool) :
    step (true :: false :: r) = true :: false :: false :: false :: step r := rfl

theorem step_t (r : List Bool) (h : r = [] ∨ ∃ r', r = true :: r') :
    step (true :: r) = true :: step r := by
  rcases h with h | ⟨r', h⟩
  · subst h
    rfl
  · subst h
    rfl

theorem step_f (r : List Bool) (h : r = [] ∨ ∃ r', r = true :: r') :
    step (false :: r) = false :: step r := by
  rcases h with h | ⟨r', h⟩
  · subst h
    rfl
  · subst h
    rfl

theorem key (ts : List Tok) : step (flat ts) = flat (mu ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U0 =>
      show step (true :: flat ts) = true :: flat (mu ts)
      rw [step_t _ (flat_head ts), ih]
    | U1 =>
      show step (true :: false :: flat ts) = true :: false :: false :: false :: flat (mu ts)
      rw [step_10, ih]
    | U3 =>
      show step (true :: false :: false :: false :: flat ts) =
        true :: false :: false :: false :: false :: true :: false :: true :: flat (mu ts)
      rw [step_10, step_00, ih]
    | U4 =>
      show step (true :: false :: false :: false :: false :: flat ts) =
        true :: false :: false :: false :: false :: true :: false :: true :: false ::
          flat (mu ts)
      rw [step_10, step_00, step_f _ (flat_head ts), ih]

theorem w_flat : ∀ n : ℕ, ∃ ts : List Tok, w (n + 1) = false :: flat ts
  | 0 => ⟨[Tok.U1, Tok.U0], rfl⟩
  | n + 1 => by
    obtain ⟨ts, h⟩ := w_flat n
    refine ⟨mu ts, ?_⟩
    show step (w (n + 1)) = false :: flat (mu ts)
    rw [h, step_f _ (flat_head ts), key]

theorem len_flat (ts : List Tok) :
    (flat ts).length = c0 ts + 2 * c1 ts + 4 * c3 ts + 5 * c4 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U0 =>
      show (flat ts).length + 1 = (c0 ts + 1) + 2 * c1 ts + 4 * c3 ts + 5 * c4 ts
      omega
    | U1 =>
      show (flat ts).length + 1 + 1 = c0 ts + 2 * (c1 ts + 1) + 4 * c3 ts + 5 * c4 ts
      omega
    | U3 =>
      show (flat ts).length + 1 + 1 + 1 + 1 = c0 ts + 2 * c1 ts + 4 * (c3 ts + 1) + 5 * c4 ts
      omega
    | U4 =>
      show (flat ts).length + 1 + 1 + 1 + 1 + 1 =
        c0 ts + 2 * c1 ts + 4 * c3 ts + 5 * (c4 ts + 1)
      omega

theorem c0_mu (ts : List Tok) : c0 (mu ts) = c0 ts + c3 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U0 =>
      show c0 (mu ts) + 1 = c0 ts + 1 + c3 ts
      omega
    | U1 =>
      show c0 (mu ts) = c0 ts + c3 ts
      exact ih
    | U3 =>
      show c0 (mu ts) + 1 = c0 ts + (c3 ts + 1)
      omega
    | U4 =>
      show c0 (mu ts) = c0 ts + c3 ts
      exact ih

theorem c1_mu (ts : List Tok) : c1 (mu ts) = c3 ts + 2 * c4 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U0 =>
      show c1 (mu ts) = c3 ts + 2 * c4 ts
      exact ih
    | U1 =>
      show c1 (mu ts) = c3 ts + 2 * c4 ts
      exact ih
    | U3 =>
      show c1 (mu ts) + 1 = c3 ts + 1 + 2 * c4 ts
      omega
    | U4 =>
      show c1 (mu ts) + 1 + 1 = c3 ts + 2 * (c4 ts + 1)
      omega

theorem c3_mu (ts : List Tok) : c3 (mu ts) = c1 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U0 =>
      show c3 (mu ts) = c1 ts
      exact ih
    | U1 =>
      show c3 (mu ts) + 1 = c1 ts + 1
      omega
    | U3 =>
      show c3 (mu ts) = c1 ts
      exact ih
    | U4 =>
      show c3 (mu ts) = c1 ts
      exact ih

theorem c4_mu (ts : List Tok) : c4 (mu ts) = c3 ts + c4 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U0 =>
      show c4 (mu ts) = c3 ts + c4 ts
      exact ih
    | U1 =>
      show c4 (mu ts) = c3 ts + c4 ts
      exact ih
    | U3 =>
      show c4 (mu ts) + 1 = c3 ts + 1 + c4 ts
      omega
    | U4 =>
      show c4 (mu ts) + 1 = c3 ts + (c4 ts + 1)
      omega

theorem len_rec (n : ℕ) : ((w (n + 5)).length : ℤ) =
    2 * ((w (n + 4)).length : ℤ) - ((w (n + 1)).length : ℤ) := by
  obtain ⟨ts, h1⟩ := w_flat n
  have h2 : w (n + 2) = false :: flat (mu ts) := by
    rw [show w (n + 2) = step (w (n + 1)) from rfl, h1, step_f _ (flat_head ts), key]
  have h3 : w (n + 3) = false :: flat (mu (mu ts)) := by
    rw [show w (n + 3) = step (w (n + 2)) from rfl, h2, step_f _ (flat_head (mu ts)), key]
  have h4 : w (n + 4) = false :: flat (mu (mu (mu ts))) := by
    rw [show w (n + 4) = step (w (n + 3)) from rfl, h3, step_f _ (flat_head (mu (mu ts))), key]
  have h5 : w (n + 5) = false :: flat (mu (mu (mu (mu ts)))) := by
    rw [show w (n + 5) = step (w (n + 4)) from rfl, h4,
      step_f _ (flat_head (mu (mu (mu ts)))), key]
  rw [h5, h4, h1]
  simp only [List.length_cons, len_flat, c0_mu, c1_mu, c3_mu, c4_mu]
  push_cast
  ring

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A288599 n ∧ ((w (n + 1)).length : ℤ) = A288599 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A288599 (n + 2) ∧ ((w (n + 3)).length : ℤ) = A288599 (n + 3) ∧
    ((w (n + 4)).length : ℤ) = A288599 (n + 4)
  | 0 => ⟨by decide, by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨_, h1, h2, h3, h4⟩ := len_eq n
    refine ⟨h1, h2, h3, h4, ?_⟩
    show ((w (n + 5)).length : ℤ) = A288599 (n + 5)
    have hA : A288599 (n + 5) = 2 * A288599 (n + 4) - A288599 (n + 1) := rfl
    rw [hA, ← h4, ← h1]
    exact len_rec n

end FS1A288596

open OMA.S_oeis_a288596 FS1A288596 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288596.main := by
  intro n
  exact (len_eq n).1
