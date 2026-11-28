import OMAStatements.S_oeis_a288633

-- Problem: A288633: Fixed point of the mapping 00->0110, 1->10, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288633.lean:0 (declaration OMA.S_oeis_a288633.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write words in the blocks A = 00, B = 01, C = 1; the mapping acts on each block
-- whatever follows it (00 -> 0110, 01 -> 0 10, 1 -> 10), and every image ends with a letter 0
-- that joins the next image. Carrying that 0 to the right: 0 + step(flat ts) = flat(mu ts) + 0
-- and 0 + step(flat ts + 0) = flat(mu ts + A), with mu: A -> A C C, B -> A C, C -> B. For n >= 1
-- the iterate is 01 + flat(ts), followed by a final 0 or not, alternately; the next iterate is
-- 01 + flat(mu ts) + 0, resp. 01 + flat(mu ts + A). With block counts (a, b, c) and the final
-- letter e the length is 2 + 2a + 2b + c + e, and four steps give L(n+4) = 2L(n+3) - L(n) in
-- both cases, the recurrence of A288465, with the same values 2, 4, 6, 10 (n = 0 by evaluation).

namespace FS2A288633

open OMA.S_oeis_a288633

inductive Tok
  | A
  | B
  | C

/-- Blocks to letters: A is 00, B is 01, C is 1. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.A :: ts => false :: false :: flat ts
  | Tok.B :: ts => false :: true :: flat ts
  | Tok.C :: ts => true :: flat ts

/-- The mapping on blocks, after carrying the final 0 of each image: A -> A C C, B -> A C, C -> B. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.A :: ts => Tok.A :: Tok.C :: Tok.C :: mu ts
  | Tok.B :: ts => Tok.A :: Tok.C :: mu ts
  | Tok.C :: ts => Tok.B :: mu ts

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
    step (false :: false :: r) = false :: true :: true :: false :: step r := rfl

theorem step_1 (r : List Bool) : step (true :: r) = true :: false :: step r := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem G0 (ts : List Tok) : false :: step (flat ts) = flat (mu ts) ++ [false] := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show false :: step (false :: false :: flat ts) =
        false :: false :: true :: true :: (flat (mu ts) ++ [false])
      rw [step_00, ih]
    | B =>
      show false :: step (false :: true :: flat ts) =
        false :: false :: true :: (flat (mu ts) ++ [false])
      rw [step_01, step_1, ih]
    | C =>
      show false :: step (true :: flat ts) = false :: true :: (flat (mu ts) ++ [false])
      rw [step_1, ih]

theorem G1 (ts : List Tok) : false :: step (flat ts ++ [false]) = flat (mu ts ++ [Tok.A]) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show false :: step (false :: false :: (flat ts ++ [false])) =
        false :: false :: true :: true :: flat (mu ts ++ [Tok.A])
      rw [step_00, ih]
    | B =>
      show false :: step (false :: true :: (flat ts ++ [false])) =
        false :: false :: true :: flat (mu ts ++ [Tok.A])
      rw [step_01, step_1, ih]
    | C =>
      show false :: step (true :: (flat ts ++ [false])) = false :: true :: flat (mu ts ++ [Tok.A])
      rw [step_1, ih]

theorem stepF (ts : List Tok) : step (flat (Tok.B :: ts)) = flat (Tok.B :: mu ts) ++ [false] := by
  show step (false :: true :: flat ts) = false :: true :: (flat (mu ts) ++ [false])
  rw [step_01, step_1, G0]

theorem stepT (ts : List Tok) :
    step (flat (Tok.B :: ts) ++ [false]) = flat (Tok.B :: (mu ts ++ [Tok.A])) := by
  show step (false :: true :: (flat ts ++ [false])) = false :: true :: flat (mu ts ++ [Tok.A])
  rw [step_01, step_1, G1]

theorem w_rep : ∀ n : ℕ, ∃ ts : List Tok,
    w (n + 1) = flat (Tok.B :: ts) ∨ w (n + 1) = flat (Tok.B :: ts) ++ [false]
  | 0 => ⟨[Tok.C], Or.inr rfl⟩
  | n + 1 => by
    obtain ⟨ts, h | h⟩ := w_rep n
    · refine ⟨mu ts, Or.inr ?_⟩
      show step (w (n + 1)) = flat (Tok.B :: mu ts) ++ [false]
      rw [h, stepF]
    · refine ⟨mu ts ++ [Tok.A], Or.inl ?_⟩
      show step (w (n + 1)) = flat (Tok.B :: (mu ts ++ [Tok.A]))
      rw [h, stepT]

theorem len_flat (ts : List Tok) : (flat ts).length = 2 * cA ts + 2 * cB ts + cC ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show (false :: false :: flat ts).length = 2 * (cA ts + 1) + 2 * cB ts + cC ts
      rw [List.length_cons, List.length_cons]
      omega
    | B =>
      show (false :: true :: flat ts).length = 2 * cA ts + 2 * (cB ts + 1) + cC ts
      rw [List.length_cons, List.length_cons]
      omega
    | C =>
      show (true :: flat ts).length = 2 * cA ts + 2 * cB ts + (cC ts + 1)
      rw [List.length_cons]
      omega

theorem cA_mu (ts : List Tok) : cA (mu ts) = cA ts + cB ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show cA (mu ts) + 1 = cA ts + 1 + cB ts
      omega
    | B =>
      show cA (mu ts) + 1 = cA ts + (cB ts + 1)
      omega
    | C =>
      show cA (mu ts) = cA ts + cB ts
      exact ih

theorem cB_mu (ts : List Tok) : cB (mu ts) = cC ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | A =>
      show cB (mu ts) = cC ts
      exact ih
    | B =>
      show cB (mu ts) = cC ts
      exact ih
    | C =>
      show cB (mu ts) + 1 = cC ts + 1
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

theorem cA_append (l1 l2 : List Tok) : cA (l1 ++ l2) = cA l1 + cA l2 := by
  induction l1 with
  | nil =>
    show cA l2 = 0 + cA l2
    omega
  | cons t l ih =>
    cases t with
    | A =>
      show cA (l ++ l2) + 1 = cA l + 1 + cA l2
      omega
    | B =>
      show cA (l ++ l2) = cA l + cA l2
      exact ih
    | C =>
      show cA (l ++ l2) = cA l + cA l2
      exact ih

theorem cB_append (l1 l2 : List Tok) : cB (l1 ++ l2) = cB l1 + cB l2 := by
  induction l1 with
  | nil =>
    show cB l2 = 0 + cB l2
    omega
  | cons t l ih =>
    cases t with
    | A =>
      show cB (l ++ l2) = cB l + cB l2
      exact ih
    | B =>
      show cB (l ++ l2) + 1 = cB l + 1 + cB l2
      omega
    | C =>
      show cB (l ++ l2) = cB l + cB l2
      exact ih

theorem cC_append (l1 l2 : List Tok) : cC (l1 ++ l2) = cC l1 + cC l2 := by
  induction l1 with
  | nil =>
    show cC l2 = 0 + cC l2
    omega
  | cons t l ih =>
    cases t with
    | A =>
      show cC (l ++ l2) = cC l + cC l2
      exact ih
    | B =>
      show cC (l ++ l2) = cC l + cC l2
      exact ih
    | C =>
      show cC (l ++ l2) + 1 = cC l + 1 + cC l2
      omega

theorem len_rec : ∀ n : ℕ, ((w (n + 4)).length : ℤ) =
    2 * ((w (n + 3)).length : ℤ) - ((w n).length : ℤ)
  | 0 => by decide
  | k + 1 => by
    obtain ⟨ts, h1 | h1⟩ := w_rep k
    · have h2 : w (k + 1 + 1) = flat (Tok.B :: mu ts) ++ [false] := by
        rw [show w (k + 1 + 1) = step (w (k + 1)) from rfl, h1, stepF]
      have h3 : w (k + 1 + 2) = flat (Tok.B :: (mu (mu ts) ++ [Tok.A])) := by
        rw [show w (k + 1 + 2) = step (w (k + 1 + 1)) from rfl, h2, stepT]
      have h4 : w (k + 1 + 3) = flat (Tok.B :: mu (mu (mu ts) ++ [Tok.A])) ++ [false] := by
        rw [show w (k + 1 + 3) = step (w (k + 1 + 2)) from rfl, h3, stepF]
      have h5 : w (k + 1 + 4) =
          flat (Tok.B :: (mu (mu (mu (mu ts) ++ [Tok.A])) ++ [Tok.A])) := by
        rw [show w (k + 1 + 4) = step (w (k + 1 + 3)) from rfl, h4, stepT]
      rw [h5, h4, h1]
      simp only [List.length_append, List.length_singleton, len_flat, cA_append, cB_append,
        cC_append, cA_mu, cB_mu, cC_mu, cA, cB, cC]
      push_cast
      ring
    · have h2 : w (k + 1 + 1) = flat (Tok.B :: (mu ts ++ [Tok.A])) := by
        rw [show w (k + 1 + 1) = step (w (k + 1)) from rfl, h1, stepT]
      have h3 : w (k + 1 + 2) = flat (Tok.B :: mu (mu ts ++ [Tok.A])) ++ [false] := by
        rw [show w (k + 1 + 2) = step (w (k + 1 + 1)) from rfl, h2, stepF]
      have h4 : w (k + 1 + 3) = flat (Tok.B :: (mu (mu (mu ts ++ [Tok.A])) ++ [Tok.A])) := by
        rw [show w (k + 1 + 3) = step (w (k + 1 + 2)) from rfl, h3, stepT]
      have h5 : w (k + 1 + 4) =
          flat (Tok.B :: mu (mu (mu (mu ts ++ [Tok.A])) ++ [Tok.A])) ++ [false] := by
        rw [show w (k + 1 + 4) = step (w (k + 1 + 3)) from rfl, h4, stepF]
      rw [h5, h4, h1]
      simp only [List.length_append, List.length_singleton, len_flat, cA_append, cB_append,
        cC_append, cA_mu, cB_mu, cC_mu, cA, cB, cC]
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

end FS2A288633

open OMA.S_oeis_a288633 FS2A288633 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288633.main := by
  intro n
  exact (len_eq n).1
