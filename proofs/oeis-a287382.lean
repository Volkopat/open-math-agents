import OMAStatements.S_oeis_a287382

-- Problem: A287382: 0-limiting word of the mapping 00->1000, 10->001, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a287382.lean:0 (declaration OMA.S_oeis_a287382.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: every 1 is read by the mapping at the start of a token, so the mapping acts
-- separately on the two sides of any cut placed just before a 1 (step_app). Seven blocks,
-- all starting with 1: A = 1000, B = 10001001, C = 1000100101001, D = 100000, E = 1000001,
-- F = 100000101001, G = 100000100101001. Each block X satisfies step(X) 001 = 001 mu(X) with
-- mu: A -> E, B -> F, C -> D C, D -> A E, E -> A B, F -> A G, G -> A D C, so the image of each
-- block donates its leading 001 to the block before. With the tail T = 1000: step(flat ts T) =
-- 001 flat(mu ts) T and step(001 flat ts T) = flat(B mu ts) T, and w(1) = T. The counts of C
-- and D agree after every step, and on that subspace the lengths satisfy
-- L(n+5) = L(n+4) + L(n+3) - L(n+2) + L(n+1) + L(n) for both forms of the word.

namespace W1A287382

open OMA.S_oeis_a287382

inductive Tok
  | A
  | B
  | C
  | D
  | E
  | F
  | G

/-- The letters of a block. -/
def flatU : Tok → List Bool
  | Tok.A => [true, false, false, false]
  | Tok.B => [true, false, false, false, true, false, false, true]
  | Tok.C => [true, false, false, false, true, false, false, true, false, true, false, false, true]
  | Tok.D => [true, false, false, false, false, false]
  | Tok.E => [true, false, false, false, false, false, true]
  | Tok.F => [true, false, false, false, false, false, true, false, true, false, false, true]
  | Tok.G => [true, false, false, false, false, false, true, false, false, true, false, true, false, false, true]

def flat : List Tok → List Bool
  | [] => []
  | x :: xs => flatU x ++ flat xs

/-- The mapping on blocks. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.A :: ts => Tok.E :: mu ts
  | Tok.B :: ts => Tok.F :: mu ts
  | Tok.C :: ts => Tok.D :: Tok.C :: mu ts
  | Tok.D :: ts => Tok.A :: Tok.E :: mu ts
  | Tok.E :: ts => Tok.A :: Tok.B :: mu ts
  | Tok.F :: ts => Tok.A :: Tok.G :: mu ts
  | Tok.G :: ts => Tok.A :: Tok.D :: Tok.C :: mu ts

def cA : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cA ts + 1
  | Tok.B :: ts => cA ts
  | Tok.C :: ts => cA ts
  | Tok.D :: ts => cA ts
  | Tok.E :: ts => cA ts
  | Tok.F :: ts => cA ts
  | Tok.G :: ts => cA ts

def cB : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cB ts
  | Tok.B :: ts => cB ts + 1
  | Tok.C :: ts => cB ts
  | Tok.D :: ts => cB ts
  | Tok.E :: ts => cB ts
  | Tok.F :: ts => cB ts
  | Tok.G :: ts => cB ts

def cC : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cC ts
  | Tok.B :: ts => cC ts
  | Tok.C :: ts => cC ts + 1
  | Tok.D :: ts => cC ts
  | Tok.E :: ts => cC ts
  | Tok.F :: ts => cC ts
  | Tok.G :: ts => cC ts

def cD : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cD ts
  | Tok.B :: ts => cD ts
  | Tok.C :: ts => cD ts
  | Tok.D :: ts => cD ts + 1
  | Tok.E :: ts => cD ts
  | Tok.F :: ts => cD ts
  | Tok.G :: ts => cD ts

def cE : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cE ts
  | Tok.B :: ts => cE ts
  | Tok.C :: ts => cE ts
  | Tok.D :: ts => cE ts
  | Tok.E :: ts => cE ts + 1
  | Tok.F :: ts => cE ts
  | Tok.G :: ts => cE ts

def cF : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cF ts
  | Tok.B :: ts => cF ts
  | Tok.C :: ts => cF ts
  | Tok.D :: ts => cF ts
  | Tok.E :: ts => cF ts
  | Tok.F :: ts => cF ts + 1
  | Tok.G :: ts => cF ts

def cG : List Tok → ℕ
  | [] => 0
  | Tok.A :: ts => cG ts
  | Tok.B :: ts => cG ts
  | Tok.C :: ts => cG ts
  | Tok.D :: ts => cG ts
  | Tok.E :: ts => cG ts
  | Tok.F :: ts => cG ts
  | Tok.G :: ts => cG ts + 1

/-- The tail 1000. -/
def T : List Bool := [true, false, false, false]

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = true :: false :: false :: false :: step r := rfl

theorem step_10 (r : List Bool) :
    step (true :: false :: r) = false :: false :: true :: step r := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem step_11 (r : List Bool) : step (true :: true :: r) = true :: step (true :: r) := rfl

/-- A cut just before a letter 1 is respected by the mapping. -/
theorem step_app : ∀ (A r : List Bool), step (A ++ true :: r) = step A ++ step (true :: r)
  | [], _ => rfl
  | [false], _ => rfl
  | [true], _ => rfl
  | false :: false :: A, r => by
    show step (false :: false :: (A ++ true :: r)) =
      true :: false :: false :: false :: (step A ++ step (true :: r))
    rw [step_00, step_app A r]
  | true :: false :: A, r => by
    show step (true :: false :: (A ++ true :: r)) =
      false :: false :: true :: (step A ++ step (true :: r))
    rw [step_10, step_app A r]
  | false :: true :: A, r => by
    have h : step (true :: (A ++ true :: r)) = step (true :: A) ++ step (true :: r) :=
      step_app (true :: A) r
    show step (false :: true :: (A ++ true :: r)) =
      false :: (step (true :: A) ++ step (true :: r))
    rw [step_01, h]
  | true :: true :: A, r => by
    have h : step (true :: (A ++ true :: r)) = step (true :: A) ++ step (true :: r) :=
      step_app (true :: A) r
    show step (true :: true :: (A ++ true :: r)) =
      true :: (step (true :: A) ++ step (true :: r))
    rw [step_11, h]

theorem head_true : ∀ ts : List Tok, ∃ r, flat ts ++ T = true :: r
  | [] => ⟨[false, false, false], rfl⟩
  | x :: ts => by
    cases x <;> exact ⟨_, rfl⟩

theorem key : ∀ ts : List Tok,
    step (flat ts ++ T) = false :: false :: true :: (flat (mu ts) ++ T)
  | [] => rfl
  | x :: ts => by
    obtain ⟨r, hr⟩ := head_true ts
    have h2 : flat (x :: ts) ++ T = flatU x ++ true :: r := by
      rw [← hr]
      exact List.append_assoc (flatU x) (flat ts) T
    rw [h2, step_app (flatU x) r, ← hr, key ts]
    cases x <;> rfl

/-- The two forms of the iterates: flat ts T, and 001 flat ts T. -/
def word : Bool → List Tok → List Bool
  | true, ts => flat ts ++ T
  | false, ts => false :: false :: true :: (flat ts ++ T)

def nx : Bool × List Tok → Bool × List Tok
  | (true, ts) => (false, mu ts)
  | (false, ts) => (true, Tok.B :: mu ts)

theorem keyW (s : Bool × List Tok) : step (word s.1 s.2) = word (nx s).1 (nx s).2 := by
  obtain ⟨p, ts⟩ := s
  cases p with
  | true => exact key ts
  | false =>
    obtain ⟨r, hr⟩ := head_true ts
    show step (false :: false :: true :: (flat ts ++ T)) =
      true :: false :: false :: false :: true :: false :: false :: true :: (flat (mu ts) ++ T)
    rw [step_00, hr, step_11, ← hr, key ts]

def st : ℕ → Bool × List Tok
  | 0 => (true, [])
  | n + 1 => nx (st n)

theorem w_rep : ∀ n : ℕ, w (n + 1) = word (st n).1 (st n).2
  | 0 => rfl
  | n + 1 => by
    show step (w (n + 1)) = word (nx (st n)).1 (nx (st n)).2
    rw [w_rep n, keyW]

theorem len_flat : ∀ ts : List Tok,
    (flat ts).length = 4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts
  | [] => rfl
  | x :: ts => by
    have ih := len_flat ts
    have e : (flat (x :: ts)).length = (flatU x).length + (flat ts).length := by
      rw [show flat (x :: ts) = flatU x ++ flat ts from rfl, List.length_append]
    rw [e, ih]
    cases x with
    | A =>
      have hl : (flatU Tok.A).length = 4 := rfl
      show (flatU Tok.A).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * (cA ts + 1) + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts
      omega
    | B =>
      have hl : (flatU Tok.B).length = 8 := rfl
      show (flatU Tok.B).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * cA ts + 8 * (cB ts + 1) + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts
      omega
    | C =>
      have hl : (flatU Tok.C).length = 13 := rfl
      show (flatU Tok.C).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * cA ts + 8 * cB ts + 13 * (cC ts + 1) + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts
      omega
    | D =>
      have hl : (flatU Tok.D).length = 6 := rfl
      show (flatU Tok.D).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * (cD ts + 1) + 7 * cE ts + 12 * cF ts + 15 * cG ts
      omega
    | E =>
      have hl : (flatU Tok.E).length = 7 := rfl
      show (flatU Tok.E).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * (cE ts + 1) + 12 * cF ts + 15 * cG ts
      omega
    | F =>
      have hl : (flatU Tok.F).length = 12 := rfl
      show (flatU Tok.F).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * (cF ts + 1) + 15 * cG ts
      omega
    | G =>
      have hl : (flatU Tok.G).length = 15 := rfl
      show (flatU Tok.G).length + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts) =
        4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * (cG ts + 1)
      omega

theorem cA_mu : ∀ ts : List Tok, cA (mu ts) = cD ts + cE ts + cF ts + cG ts
  | [] => rfl
  | x :: ts => by
    have ih := cA_mu ts
    cases x with
    | A =>
      show cA (mu ts) = cD ts + cE ts + cF ts + cG ts
      omega
    | B =>
      show cA (mu ts) = cD ts + cE ts + cF ts + cG ts
      omega
    | C =>
      show cA (mu ts) = cD ts + cE ts + cF ts + cG ts
      omega
    | D =>
      show cA (mu ts) + 1 = (cD ts + 1) + cE ts + cF ts + cG ts
      omega
    | E =>
      show cA (mu ts) + 1 = cD ts + (cE ts + 1) + cF ts + cG ts
      omega
    | F =>
      show cA (mu ts) + 1 = cD ts + cE ts + (cF ts + 1) + cG ts
      omega
    | G =>
      show cA (mu ts) + 1 = cD ts + cE ts + cF ts + (cG ts + 1)
      omega

theorem cB_mu : ∀ ts : List Tok, cB (mu ts) = cE ts
  | [] => rfl
  | x :: ts => by
    have ih := cB_mu ts
    cases x with
    | A =>
      show cB (mu ts) = cE ts
      omega
    | B =>
      show cB (mu ts) = cE ts
      omega
    | C =>
      show cB (mu ts) = cE ts
      omega
    | D =>
      show cB (mu ts) = cE ts
      omega
    | E =>
      show cB (mu ts) + 1 = (cE ts + 1)
      omega
    | F =>
      show cB (mu ts) = cE ts
      omega
    | G =>
      show cB (mu ts) = cE ts
      omega

theorem cC_mu : ∀ ts : List Tok, cC (mu ts) = cC ts + cG ts
  | [] => rfl
  | x :: ts => by
    have ih := cC_mu ts
    cases x with
    | A =>
      show cC (mu ts) = cC ts + cG ts
      omega
    | B =>
      show cC (mu ts) = cC ts + cG ts
      omega
    | C =>
      show cC (mu ts) + 1 = (cC ts + 1) + cG ts
      omega
    | D =>
      show cC (mu ts) = cC ts + cG ts
      omega
    | E =>
      show cC (mu ts) = cC ts + cG ts
      omega
    | F =>
      show cC (mu ts) = cC ts + cG ts
      omega
    | G =>
      show cC (mu ts) + 1 = cC ts + (cG ts + 1)
      omega

theorem cD_mu : ∀ ts : List Tok, cD (mu ts) = cC ts + cG ts
  | [] => rfl
  | x :: ts => by
    have ih := cD_mu ts
    cases x with
    | A =>
      show cD (mu ts) = cC ts + cG ts
      omega
    | B =>
      show cD (mu ts) = cC ts + cG ts
      omega
    | C =>
      show cD (mu ts) + 1 = (cC ts + 1) + cG ts
      omega
    | D =>
      show cD (mu ts) = cC ts + cG ts
      omega
    | E =>
      show cD (mu ts) = cC ts + cG ts
      omega
    | F =>
      show cD (mu ts) = cC ts + cG ts
      omega
    | G =>
      show cD (mu ts) + 1 = cC ts + (cG ts + 1)
      omega

theorem cE_mu : ∀ ts : List Tok, cE (mu ts) = cA ts + cD ts
  | [] => rfl
  | x :: ts => by
    have ih := cE_mu ts
    cases x with
    | A =>
      show cE (mu ts) + 1 = (cA ts + 1) + cD ts
      omega
    | B =>
      show cE (mu ts) = cA ts + cD ts
      omega
    | C =>
      show cE (mu ts) = cA ts + cD ts
      omega
    | D =>
      show cE (mu ts) + 1 = cA ts + (cD ts + 1)
      omega
    | E =>
      show cE (mu ts) = cA ts + cD ts
      omega
    | F =>
      show cE (mu ts) = cA ts + cD ts
      omega
    | G =>
      show cE (mu ts) = cA ts + cD ts
      omega

theorem cF_mu : ∀ ts : List Tok, cF (mu ts) = cB ts
  | [] => rfl
  | x :: ts => by
    have ih := cF_mu ts
    cases x with
    | A =>
      show cF (mu ts) = cB ts
      omega
    | B =>
      show cF (mu ts) + 1 = (cB ts + 1)
      omega
    | C =>
      show cF (mu ts) = cB ts
      omega
    | D =>
      show cF (mu ts) = cB ts
      omega
    | E =>
      show cF (mu ts) = cB ts
      omega
    | F =>
      show cF (mu ts) = cB ts
      omega
    | G =>
      show cF (mu ts) = cB ts
      omega

theorem cG_mu : ∀ ts : List Tok, cG (mu ts) = cF ts
  | [] => rfl
  | x :: ts => by
    have ih := cG_mu ts
    cases x with
    | A =>
      show cG (mu ts) = cF ts
      omega
    | B =>
      show cG (mu ts) = cF ts
      omega
    | C =>
      show cG (mu ts) = cF ts
      omega
    | D =>
      show cG (mu ts) = cF ts
      omega
    | E =>
      show cG (mu ts) = cF ts
      omega
    | F =>
      show cG (mu ts) + 1 = (cF ts + 1)
      omega
    | G =>
      show cG (mu ts) = cF ts
      omega

def hl : Bool → ℕ
  | true => 4
  | false => 7

/-- The length of the word described by s. -/
def Ls (s : Bool × List Tok) : ℕ :=
  hl s.1 + (4 * cA s.2 + 8 * cB s.2 + 13 * cC s.2 + 6 * cD s.2 + 7 * cE s.2 + 12 * cF s.2 + 15 * cG s.2)

theorem len_word (s : Bool × List Tok) : (word s.1 s.2).length = Ls s := by
  obtain ⟨p, ts⟩ := s
  have hf := len_flat ts
  have hT : T.length = 4 := rfl
  cases p with
  | true =>
    show (flat ts ++ T).length = 4 + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts)
    rw [List.length_append]
    omega
  | false =>
    show (false :: false :: true :: (flat ts ++ T)).length = 7 + (4 * cA ts + 8 * cB ts + 13 * cC ts + 6 * cD ts + 7 * cE ts + 12 * cF ts + 15 * cG ts)
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_append]
    omega

theorem len_w (n : ℕ) : (w (n + 1)).length = Ls (st n) := by
  rw [w_rep n]
  exact len_word (st n)

theorem cinv_nx (s : Bool × List Tok) : cD (nx s).2 = cC (nx s).2 := by
  obtain ⟨p, ts⟩ := s
  cases p with
  | true =>
    show cD (mu ts) = cC (mu ts)
    rw [cD_mu, cC_mu]
  | false =>
    show cD (mu ts) = cC (mu ts)
    rw [cD_mu, cC_mu]

theorem cinv : ∀ n : ℕ, cD (st n).2 = cC (st n).2
  | 0 => rfl
  | n + 1 => cinv_nx (st n)

theorem E (s : Bool × List Tok) (h : cD s.2 = cC s.2) :
    (Ls (nx (nx (nx (nx (nx s))))) : ℤ) = (Ls (nx (nx (nx (nx s)))) : ℤ) +
      (Ls (nx (nx (nx s))) : ℤ) - (Ls (nx (nx s)) : ℤ) + (Ls (nx s) : ℤ) + (Ls s : ℤ) := by
  obtain ⟨p, ts⟩ := s
  have h' : (cD ts : ℤ) = (cC ts : ℤ) := by exact_mod_cast h
  cases p <;>
    simp only [nx, Ls, hl, cA, cB, cC, cD, cE, cF, cG, cA_mu, cB_mu, cC_mu, cD_mu, cE_mu,
      cF_mu, cG_mu] <;>
    push_cast <;> linear_combination h'

theorem len_eq : ∀ n : ℕ,
    ((w (n + 1)).length : ℤ) = A287525 (n + 1) ∧ ((w (n + 2)).length : ℤ) = A287525 (n + 2) ∧
    ((w (n + 3)).length : ℤ) = A287525 (n + 3) ∧ ((w (n + 4)).length : ℤ) = A287525 (n + 4) ∧
    ((w (n + 5)).length : ℤ) = A287525 (n + 5)
  | 0 => ⟨by decide, by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := len_eq n
    refine ⟨h2, h3, h4, h5, ?_⟩
    show ((w (n + 6)).length : ℤ) = A287525 (n + 6)
    have hA : A287525 (n + 6) = A287525 (n + 5) + A287525 (n + 4) - A287525 (n + 3) +
        A287525 (n + 2) + A287525 (n + 1) := rfl
    have hE := E (st n) (cinv n)
    have q0 := len_w n
    have q1 := len_w (n + 1)
    have q2 := len_w (n + 2)
    have q3 := len_w (n + 3)
    have q4 := len_w (n + 4)
    have q5 := len_w (n + 5)
    rw [show st (n + 1) = nx (st n) from rfl, show n + 1 + 1 = n + 2 by omega] at q1
    rw [show st (n + 2) = nx (nx (st n)) from rfl, show n + 2 + 1 = n + 3 by omega] at q2
    rw [show st (n + 3) = nx (nx (nx (st n))) from rfl, show n + 3 + 1 = n + 4 by omega] at q3
    rw [show st (n + 4) = nx (nx (nx (nx (st n)))) from rfl,
      show n + 4 + 1 = n + 5 by omega] at q4
    rw [show st (n + 5) = nx (nx (nx (nx (nx (st n))))) from rfl,
      show n + 5 + 1 = n + 6 by omega] at q5
    rw [hA, ← h5, ← h4, ← h3, ← h2, ← h1, q5, q4, q3, q2, q1, q0]
    exact hE

end W1A287382

open OMA.S_oeis_a287382 W1A287382 in
theorem OMA.solution : type_of% @OMA.S_oeis_a287382.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (len_eq m).1
