import OMAStatements.S_oeis_a288524

-- Problem: A288524: 1-limiting word of the mapping 00->0101, 10->010, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288524.lean:0 (declaration OMA.S_oeis_a288524.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: blocks U1 = 10, U2 = 100, U3 = 1000 and the tail T = 101. If the next letter is 1,
-- the mapping sends 10 to 010, 100 to 0100 and 1000 to 0100101, so the image of each block
-- starts with a 0 that joins the block before it: step (flat ts ++ T) = 0 (flat (mu ts) ++ T)
-- with mu: U1 -> U2, U2 -> U3, U3 -> U2 U1 U1. From w(1) = 0101 on, w is W1 ts = 0 flat ts T or
-- W2 ts = 00 flat ts T, and step (W1 ts) = W2 (mu ts), step (W2 ts) = W1 (U1 U1 mu ts). The
-- counts of U1, U2, U3 evolve by (a, b, c) -> (2c, a + c, b), with characteristic polynomial
-- t^3 - t - 2, and the constants of the alternating prefix fit the factor t - 1 of
-- t^4 - t^3 - t^2 - t + 2; so L(n+5) + 2L(n+1) = L(n+4) + L(n+3) + L(n+2), as in A288523.

namespace FS1A288524

open OMA.S_oeis_a288524

inductive Tok
  | U1
  | U2
  | U3

/-- Blocks to letters: U1 is 10, U2 is 100, U3 is 1000. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.U1 :: ts => true :: false :: flat ts
  | Tok.U2 :: ts => true :: false :: false :: flat ts
  | Tok.U3 :: ts => true :: false :: false :: false :: flat ts

/-- The shifted mapping on blocks: U1 -> U2, U2 -> U3, U3 -> U2 U1 U1. -/
def mu : List Tok → List Tok
  | [] => []
  | Tok.U1 :: ts => Tok.U2 :: mu ts
  | Tok.U2 :: ts => Tok.U3 :: mu ts
  | Tok.U3 :: ts => Tok.U2 :: Tok.U1 :: Tok.U1 :: mu ts

def c1 : List Tok → ℕ
  | [] => 0
  | Tok.U1 :: ts => c1 ts + 1
  | Tok.U2 :: ts => c1 ts
  | Tok.U3 :: ts => c1 ts

def c2 : List Tok → ℕ
  | [] => 0
  | Tok.U1 :: ts => c2 ts
  | Tok.U2 :: ts => c2 ts + 1
  | Tok.U3 :: ts => c2 ts

def c3 : List Tok → ℕ
  | [] => 0
  | Tok.U1 :: ts => c3 ts
  | Tok.U2 :: ts => c3 ts
  | Tok.U3 :: ts => c3 ts + 1

/-- The tail 101. -/
def T : List Bool := [true, false, true]

def W1 (ts : List Tok) : List Bool := false :: (flat ts ++ T)

def W2 (ts : List Tok) : List Bool := false :: false :: (flat ts ++ T)

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: false :: true :: step r := rfl

theorem step_10 (r : List Bool) : step (true :: false :: r) = false :: true :: false :: step r := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem head_true : ∀ ts : List Tok, ∃ r, flat ts ++ T = true :: r
  | [] => ⟨[false, true], rfl⟩
  | Tok.U1 :: ts => ⟨false :: (flat ts ++ T), rfl⟩
  | Tok.U2 :: ts => ⟨false :: false :: (flat ts ++ T), rfl⟩
  | Tok.U3 :: ts => ⟨false :: false :: false :: (flat ts ++ T), rfl⟩

theorem step_f1 (ts : List Tok) : step (false :: (flat ts ++ T)) = false :: step (flat ts ++ T) := by
  obtain ⟨r, h⟩ := head_true ts
  rw [h, step_01]

theorem key : ∀ ts : List Tok, step (flat ts ++ T) = false :: (flat (mu ts) ++ T)
  | [] => rfl
  | Tok.U1 :: ts => by
    show step (true :: false :: (flat ts ++ T)) =
      false :: true :: false :: false :: (flat (mu ts) ++ T)
    rw [step_10, key ts]
  | Tok.U2 :: ts => by
    show step (true :: false :: false :: (flat ts ++ T)) =
      false :: true :: false :: false :: false :: (flat (mu ts) ++ T)
    rw [step_10, step_f1 ts, key ts]
  | Tok.U3 :: ts => by
    show step (true :: false :: false :: false :: (flat ts ++ T)) =
      false :: true :: false :: false :: true :: false :: true :: false :: (flat (mu ts) ++ T)
    rw [step_10, step_00, key ts]

theorem stepW1 (ts : List Tok) : step (W1 ts) = W2 (mu ts) := by
  show step (false :: (flat ts ++ T)) = false :: false :: (flat (mu ts) ++ T)
  rw [step_f1 ts, key ts]

theorem stepW2 (ts : List Tok) : step (W2 ts) = W1 (Tok.U1 :: Tok.U1 :: mu ts) := by
  show step (false :: false :: (flat ts ++ T)) =
    false :: true :: false :: true :: false :: (flat (mu ts) ++ T)
  rw [step_00, key ts]

theorem w_inv : ∀ n : ℕ, ∃ ts : List Tok, w (n + 1) = W1 ts ∨ w (n + 1) = W2 ts
  | 0 => ⟨[], Or.inl rfl⟩
  | n + 1 => by
    obtain ⟨ts, h | h⟩ := w_inv n
    · refine ⟨mu ts, Or.inr ?_⟩
      show step (w (n + 1)) = W2 (mu ts)
      rw [h, stepW1]
    · refine ⟨Tok.U1 :: Tok.U1 :: mu ts, Or.inl ?_⟩
      show step (w (n + 1)) = W1 (Tok.U1 :: Tok.U1 :: mu ts)
      rw [h, stepW2]

theorem len_flat (ts : List Tok) : (flat ts).length = 2 * c1 ts + 3 * c2 ts + 4 * c3 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U1 =>
      show (flat ts).length + 1 + 1 = 2 * (c1 ts + 1) + 3 * c2 ts + 4 * c3 ts
      omega
    | U2 =>
      show (flat ts).length + 1 + 1 + 1 = 2 * c1 ts + 3 * (c2 ts + 1) + 4 * c3 ts
      omega
    | U3 =>
      show (flat ts).length + 1 + 1 + 1 + 1 = 2 * c1 ts + 3 * c2 ts + 4 * (c3 ts + 1)
      omega

theorem lenW1 (ts : List Tok) : (W1 ts).length = 2 * c1 ts + 3 * c2 ts + 4 * c3 ts + 4 := by
  have hT : T.length = 3 := rfl
  have h := len_flat ts
  show (flat ts ++ T).length + 1 = 2 * c1 ts + 3 * c2 ts + 4 * c3 ts + 4
  rw [List.length_append]
  omega

theorem lenW2 (ts : List Tok) : (W2 ts).length = 2 * c1 ts + 3 * c2 ts + 4 * c3 ts + 5 := by
  have hT : T.length = 3 := rfl
  have h := len_flat ts
  show (flat ts ++ T).length + 1 + 1 = 2 * c1 ts + 3 * c2 ts + 4 * c3 ts + 5
  rw [List.length_append]
  omega

theorem c1_mu (ts : List Tok) : c1 (mu ts) = 2 * c3 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U1 =>
      show c1 (mu ts) = 2 * c3 ts
      exact ih
    | U2 =>
      show c1 (mu ts) = 2 * c3 ts
      exact ih
    | U3 =>
      show c1 (mu ts) + 1 + 1 = 2 * (c3 ts + 1)
      omega

theorem c2_mu (ts : List Tok) : c2 (mu ts) = c1 ts + c3 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U1 =>
      show c2 (mu ts) + 1 = c1 ts + 1 + c3 ts
      omega
    | U2 =>
      show c2 (mu ts) = c1 ts + c3 ts
      exact ih
    | U3 =>
      show c2 (mu ts) + 1 = c1 ts + (c3 ts + 1)
      omega

theorem c3_mu (ts : List Tok) : c3 (mu ts) = c2 ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | U1 =>
      show c3 (mu ts) = c2 ts
      exact ih
    | U2 =>
      show c3 (mu ts) + 1 = c2 ts + 1
      omega
    | U3 =>
      show c3 (mu ts) = c2 ts
      exact ih

theorem mu_UU (x : List Tok) : mu (Tok.U1 :: Tok.U1 :: x) = Tok.U2 :: Tok.U2 :: mu x := rfl

theorem mu_VV (x : List Tok) : mu (Tok.U2 :: Tok.U2 :: x) = Tok.U3 :: Tok.U3 :: mu x := rfl

theorem mu_WW (x : List Tok) :
    mu (Tok.U3 :: Tok.U3 :: x) =
      Tok.U2 :: Tok.U1 :: Tok.U1 :: Tok.U2 :: Tok.U1 :: Tok.U1 :: mu x := rfl

theorem c1_U1 (x : List Tok) : c1 (Tok.U1 :: x) = c1 x + 1 := rfl
theorem c1_U2 (x : List Tok) : c1 (Tok.U2 :: x) = c1 x := rfl
theorem c1_U3 (x : List Tok) : c1 (Tok.U3 :: x) = c1 x := rfl
theorem c2_U1 (x : List Tok) : c2 (Tok.U1 :: x) = c2 x := rfl
theorem c2_U2 (x : List Tok) : c2 (Tok.U2 :: x) = c2 x + 1 := rfl
theorem c2_U3 (x : List Tok) : c2 (Tok.U3 :: x) = c2 x := rfl
theorem c3_U1 (x : List Tok) : c3 (Tok.U1 :: x) = c3 x := rfl
theorem c3_U2 (x : List Tok) : c3 (Tok.U2 :: x) = c3 x := rfl
theorem c3_U3 (x : List Tok) : c3 (Tok.U3 :: x) = c3 x + 1 := rfl

theorem len_rec (n : ℕ) : (w (n + 5)).length + 2 * (w (n + 1)).length =
    (w (n + 4)).length + (w (n + 3)).length + (w (n + 2)).length := by
  obtain ⟨ts, h | h⟩ := w_inv n
  · have h2 : w (n + 2) = W2 (mu ts) := by
      rw [show w (n + 2) = step (w (n + 1)) from rfl, h, stepW1]
    have h3 : w (n + 3) = W1 (Tok.U1 :: Tok.U1 :: mu (mu ts)) := by
      rw [show w (n + 3) = step (w (n + 2)) from rfl, h2, stepW2]
    have h4 : w (n + 4) = W2 (mu (Tok.U1 :: Tok.U1 :: mu (mu ts))) := by
      rw [show w (n + 4) = step (w (n + 3)) from rfl, h3, stepW1]
    rw [mu_UU] at h4
    have h5 : w (n + 5) =
        W1 (Tok.U1 :: Tok.U1 :: mu (Tok.U2 :: Tok.U2 :: mu (mu (mu ts)))) := by
      rw [show w (n + 5) = step (w (n + 4)) from rfl, h4, stepW2]
    rw [mu_VV] at h5
    rw [h5, h4, h3, h2, h]
    simp only [lenW1, lenW2, c1_U1, c1_U2, c1_U3, c2_U1, c2_U2, c2_U3, c3_U1, c3_U2, c3_U3,
      c1_mu, c2_mu, c3_mu]
    ring
  · have h2 : w (n + 2) = W1 (Tok.U1 :: Tok.U1 :: mu ts) := by
      rw [show w (n + 2) = step (w (n + 1)) from rfl, h, stepW2]
    have h3 : w (n + 3) = W2 (mu (Tok.U1 :: Tok.U1 :: mu ts)) := by
      rw [show w (n + 3) = step (w (n + 2)) from rfl, h2, stepW1]
    rw [mu_UU] at h3
    have h4 : w (n + 4) = W1 (Tok.U1 :: Tok.U1 :: mu (Tok.U2 :: Tok.U2 :: mu (mu ts))) := by
      rw [show w (n + 4) = step (w (n + 3)) from rfl, h3, stepW2]
    rw [mu_VV] at h4
    have h5 : w (n + 5) =
        W2 (mu (Tok.U1 :: Tok.U1 :: Tok.U3 :: Tok.U3 :: mu (mu (mu ts)))) := by
      rw [show w (n + 5) = step (w (n + 4)) from rfl, h4, stepW1]
    rw [mu_UU, mu_WW] at h5
    rw [h5, h4, h3, h2, h]
    simp only [lenW1, lenW2, c1_U1, c1_U2, c1_U3, c2_U1, c2_U2, c2_U3, c3_U1, c3_U2, c3_U3,
      c1_mu, c2_mu, c3_mu]
    ring

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A288523 n ∧ ((w (n + 1)).length : ℤ) = A288523 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A288523 (n + 2) ∧ ((w (n + 3)).length : ℤ) = A288523 (n + 3) ∧
    ((w (n + 4)).length : ℤ) = A288523 (n + 4)
  | 0 => ⟨by decide, by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨_, h1, h2, h3, h4⟩ := len_eq n
    refine ⟨h1, h2, h3, h4, ?_⟩
    show ((w (n + 5)).length : ℤ) = A288523 (n + 5)
    have hk : ((w (n + 5)).length : ℤ) + 2 * ((w (n + 1)).length : ℤ) =
        ((w (n + 4)).length : ℤ) + ((w (n + 3)).length : ℤ) + ((w (n + 2)).length : ℤ) := by
      exact_mod_cast len_rec n
    have hA : A288523 (n + 5) =
        A288523 (n + 4) + A288523 (n + 3) + A288523 (n + 2) - 2 * A288523 (n + 1) := rfl
    rw [hA, ← h4, ← h3, ← h2, ← h1]
    linarith

end FS1A288524

open OMA.S_oeis_a288524 FS1A288524 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288524.main := by
  intro n
  exact (len_eq n).1
