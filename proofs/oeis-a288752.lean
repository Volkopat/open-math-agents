import OMAStatements.S_oeis_a288752

-- Problem: A288752: 0-limiting word of the mapping 00->0110, 1->01, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288752.lean:0 (declaration OMA.S_oeis_a288752.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for n >= 1 the iterate w(n) is flat(ts) followed by a final letter 0, where ts is a
-- word in the blocks P = 001, Q = 01, R = 1. Whatever follows, the mapping sends 001 to
-- 0110 01 = Q R P, 01 (a 0 followed by 1 is kept) to 0 01 = P, 1 to 01 = Q, and the final 0 to 0,
-- so step (flat ts ++ 0) = flat (mu ts) ++ 0 with mu: P -> Q R P, Q -> P, R -> Q, and
-- w(1) = flat [Q, R] ++ 0. With block counts (p, q, r) the length is 3p + 2q + r + 1, and one
-- step maps (p, q, r) to (p + q, p + r, p); four steps give L(n+4) = 2L(n+3) - L(n), the
-- recurrence of A288465, with the same values 2, 4, 6, 10 (and the case n = 0 by evaluation).

namespace FS2A288752

open OMA.S_oeis_a288752

inductive Tok
  | P
  | Q
  | R

/-- Blocks to letters: P is 001, Q is 01, R is 1. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.P :: ts => false :: false :: true :: flat ts
  | Tok.Q :: ts => false :: true :: flat ts
  | Tok.R :: ts => true :: flat ts

/-- The mapping on blocks: P -> Q R P, Q -> P, R -> Q. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.P :: ts => Tok.Q :: Tok.R :: Tok.P :: mu ts
  | Tok.Q :: ts => Tok.P :: mu ts
  | Tok.R :: ts => Tok.Q :: mu ts

def cP : List Tok → ℕ
  | [] => 0
  | Tok.P :: ts => cP ts + 1
  | Tok.Q :: ts => cP ts
  | Tok.R :: ts => cP ts

def cQ : List Tok → ℕ
  | [] => 0
  | Tok.P :: ts => cQ ts
  | Tok.Q :: ts => cQ ts + 1
  | Tok.R :: ts => cQ ts

def cR : List Tok → ℕ
  | [] => 0
  | Tok.P :: ts => cR ts
  | Tok.Q :: ts => cR ts
  | Tok.R :: ts => cR ts + 1

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: true :: false :: step r := rfl

theorem step_1 (r : List Bool) : step (true :: r) = false :: true :: step r := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem key (ts : List Tok) : step (flat ts ++ [false]) = flat (mu ts) ++ [false] := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | P =>
      show step (false :: false :: true :: (flat ts ++ [false])) =
        false :: true :: true :: false :: false :: true :: (flat (mu ts) ++ [false])
      rw [step_00, step_1, ih]
    | Q =>
      show step (false :: true :: (flat ts ++ [false])) =
        false :: false :: true :: (flat (mu ts) ++ [false])
      rw [step_01, step_1, ih]
    | R =>
      show step (true :: (flat ts ++ [false])) = false :: true :: (flat (mu ts) ++ [false])
      rw [step_1, ih]

theorem w_flat : ∀ n : ℕ, ∃ ts : List Tok, w (n + 1) = flat ts ++ [false]
  | 0 => ⟨[Tok.Q, Tok.R], rfl⟩
  | n + 1 => by
    obtain ⟨ts, h⟩ := w_flat n
    refine ⟨mu ts, ?_⟩
    show step (w (n + 1)) = flat (mu ts) ++ [false]
    rw [h, key]

theorem len_flat (ts : List Tok) : (flat ts).length = 3 * cP ts + 2 * cQ ts + cR ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | P =>
      show (false :: false :: true :: flat ts).length = 3 * (cP ts + 1) + 2 * cQ ts + cR ts
      rw [List.length_cons, List.length_cons, List.length_cons]
      omega
    | Q =>
      show (false :: true :: flat ts).length = 3 * cP ts + 2 * (cQ ts + 1) + cR ts
      rw [List.length_cons, List.length_cons]
      omega
    | R =>
      show (true :: flat ts).length = 3 * cP ts + 2 * cQ ts + (cR ts + 1)
      rw [List.length_cons]
      omega

theorem cP_mu (ts : List Tok) : cP (mu ts) = cP ts + cQ ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | P =>
      show cP (mu ts) + 1 = cP ts + 1 + cQ ts
      omega
    | Q =>
      show cP (mu ts) + 1 = cP ts + (cQ ts + 1)
      omega
    | R =>
      show cP (mu ts) = cP ts + cQ ts
      exact ih

theorem cQ_mu (ts : List Tok) : cQ (mu ts) = cP ts + cR ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | P =>
      show cQ (mu ts) + 1 = cP ts + 1 + cR ts
      omega
    | Q =>
      show cQ (mu ts) = cP ts + cR ts
      exact ih
    | R =>
      show cQ (mu ts) + 1 = cP ts + (cR ts + 1)
      omega

theorem cR_mu (ts : List Tok) : cR (mu ts) = cP ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | P =>
      show cR (mu ts) + 1 = cP ts + 1
      omega
    | Q =>
      show cR (mu ts) = cP ts
      exact ih
    | R =>
      show cR (mu ts) = cP ts
      exact ih

theorem len_rec : ∀ n : ℕ, ((w (n + 4)).length : ℤ) =
    2 * ((w (n + 3)).length : ℤ) - ((w n).length : ℤ)
  | 0 => by decide
  | k + 1 => by
    obtain ⟨ts, h1⟩ := w_flat k
    have h2 : w (k + 1 + 1) = flat (mu ts) ++ [false] := by
      rw [show w (k + 1 + 1) = step (w (k + 1)) from rfl, h1, key]
    have h3 : w (k + 1 + 2) = flat (mu (mu ts)) ++ [false] := by
      rw [show w (k + 1 + 2) = step (w (k + 1 + 1)) from rfl, h2, key]
    have h4 : w (k + 1 + 3) = flat (mu (mu (mu ts))) ++ [false] := by
      rw [show w (k + 1 + 3) = step (w (k + 1 + 2)) from rfl, h3, key]
    have h5 : w (k + 1 + 4) = flat (mu (mu (mu (mu ts)))) ++ [false] := by
      rw [show w (k + 1 + 4) = step (w (k + 1 + 3)) from rfl, h4, key]
    rw [h5, h4, h1]
    simp only [List.length_append, List.length_singleton, len_flat, cP_mu, cQ_mu, cR_mu]
    push_cast
    ring

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A288465 n ∧ ((w (n + 1)).length : ℤ) = A288465 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A288465 (n + 2) ∧ ((w (n + 3)).length : ℤ) = A288465 (n + 3)
  | 0 => ⟨by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h0, h1, h2, h3⟩ := len_eq n
    refine ⟨h1, h2, h3, ?_⟩
    show ((w (n + 4)).length : ℤ) = A288465 (n + 4)
    have hA : A288465 (n + 4) = 2 * A288465 (n + 3) - A288465 n := rfl
    rw [hA, ← h3, ← h0]
    exact len_rec n

end FS2A288752

open OMA.S_oeis_a288752 FS2A288752 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288752.main := by
  intro n
  exact (len_eq n).1
