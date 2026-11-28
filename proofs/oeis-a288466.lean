import OMAStatements.S_oeis_a288466

-- Problem: A288466: Fixed point of the mapping 00->0101, 1->010, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288466.lean:0 (declaration OMA.S_oeis_a288466.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for n >= 1, w(n) = h ++ flat(ps) ++ z with a head h = 01 or 001, blocks
-- P = 01, Q = 001, R = 0001 and a tail z = (empty), 0 or 00. A block 0^k 1 always maps to
-- f(0^k) 010, and the last 0 of each image is carried into the next block, which gives
-- step(h ++ flat(ps) ++ z) = h' ++ flat(e(h) ++ sig(ps) ++ e(z)) ++ z' with sig: P -> R,
-- Q -> Q P P, R -> Q P Q, heads 01 -> 001 -> 01 (with two extra P), tails (empty) -> 0 -> 00 ->
-- (empty) (with extra Q P). The block counts evolve by a matrix with characteristic polynomial
-- t^3 - t^2 - t - 3, and the head and tail contributions cancel in
-- L(n+4) - 2L(n+3) - 2L(n+1) + 3L(n), checked for every head and tail by ring.

namespace FS5A288466

open OMA.S_oeis_a288466

inductive Pl
  | P
  | Q
  | R

inductive Fh
  | q
  | r

inductive Tr
  | t0
  | t1
  | t2

def flatP : List Pl → List Bool
  | [] => []
  | Pl.P :: ps => false :: true :: flatP ps
  | Pl.Q :: ps => false :: false :: true :: flatP ps
  | Pl.R :: ps => false :: false :: false :: true :: flatP ps

def fhead : Fh → List Bool
  | Fh.q => [false, true]
  | Fh.r => [false, false, true]

def ftail : Tr → List Bool
  | Tr.t0 => []
  | Tr.t1 => [false]
  | Tr.t2 => [false, false]

def word (f : Fh) (ps : List Pl) (t : Tr) : List Bool := fhead f ++ (flatP ps ++ ftail t)

def sig : List Pl → List Pl
  | [] => []
  | Pl.P :: ps => Pl.R :: sig ps
  | Pl.Q :: ps => Pl.Q :: Pl.P :: Pl.P :: sig ps
  | Pl.R :: ps => Pl.Q :: Pl.P :: Pl.Q :: sig ps

def nf : Fh → Fh
  | Fh.q => Fh.r
  | Fh.r => Fh.q

def ef : Fh → List Pl
  | Fh.q => []
  | Fh.r => [Pl.P, Pl.P]

def nt : Tr → Tr
  | Tr.t0 => Tr.t1
  | Tr.t1 => Tr.t2
  | Tr.t2 => Tr.t0

def et : Tr → List Pl
  | Tr.t0 => []
  | Tr.t1 => []
  | Tr.t2 => [Pl.Q, Pl.P]

def cP : List Pl → ℕ
  | [] => 0
  | Pl.P :: ps => cP ps + 1
  | Pl.Q :: ps => cP ps
  | Pl.R :: ps => cP ps

def cQ : List Pl → ℕ
  | [] => 0
  | Pl.P :: ps => cQ ps
  | Pl.Q :: ps => cQ ps + 1
  | Pl.R :: ps => cQ ps

def cR : List Pl → ℕ
  | [] => 0
  | Pl.P :: ps => cR ps
  | Pl.Q :: ps => cR ps
  | Pl.R :: ps => cR ps + 1

def hl : Fh → ℕ
  | Fh.q => 2
  | Fh.r => 3

def tl : Tr → ℕ
  | Tr.t0 => 0
  | Tr.t1 => 1
  | Tr.t2 => 2

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: false :: true :: step r := rfl

theorem step_1 (r : List Bool) : step (true :: r) = false :: true :: false :: step r := rfl

theorem step_01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem tailstep (ps : List Pl) (t : Tr) :
    false :: step (flatP ps ++ ftail t) = flatP (sig ps ++ et t) ++ ftail (nt t) := by
  induction ps with
  | nil =>
    cases t with
    | t0 => rfl
    | t1 => rfl
    | t2 => rfl
  | cons x ps ih =>
    cases x with
    | P =>
      show false :: step (false :: true :: (flatP ps ++ ftail t)) =
        false :: false :: false :: true :: (flatP (sig ps ++ et t) ++ ftail (nt t))
      rw [step_01, step_1, ← ih]
    | Q =>
      show false :: step (false :: false :: true :: (flatP ps ++ ftail t)) =
        false :: false :: true :: false :: true :: false :: true ::
          (flatP (sig ps ++ et t) ++ ftail (nt t))
      rw [step_00, step_1, ← ih]
    | R =>
      show false :: step (false :: false :: false :: true :: (flatP ps ++ ftail t)) =
        false :: false :: true :: false :: true :: false :: false :: true ::
          (flatP (sig ps ++ et t) ++ ftail (nt t))
      rw [step_00, step_01, step_1, ← ih]

theorem key (f : Fh) (ps : List Pl) (t : Tr) :
    step (word f ps t) = word (nf f) (ef f ++ (sig ps ++ et t)) (nt t) := by
  cases f with
  | q =>
    show step (false :: true :: (flatP ps ++ ftail t)) =
      false :: false :: true :: (flatP (sig ps ++ et t) ++ ftail (nt t))
    rw [step_01, step_1, ← tailstep]
  | r =>
    show step (false :: false :: true :: (flatP ps ++ ftail t)) =
      false :: true :: false :: true :: false :: true :: (flatP (sig ps ++ et t) ++ ftail (nt t))
    rw [step_00, step_1, ← tailstep]

theorem len_flatP (ps : List Pl) : (flatP ps).length = 2 * cP ps + 3 * cQ ps + 4 * cR ps := by
  induction ps with
  | nil => rfl
  | cons x ps ih =>
    cases x with
    | P =>
      show (false :: true :: flatP ps).length = 2 * (cP ps + 1) + 3 * cQ ps + 4 * cR ps
      rw [List.length_cons, List.length_cons]
      omega
    | Q =>
      show (false :: false :: true :: flatP ps).length = 2 * cP ps + 3 * (cQ ps + 1) + 4 * cR ps
      rw [List.length_cons, List.length_cons, List.length_cons]
      omega
    | R =>
      show (false :: false :: false :: true :: flatP ps).length =
        2 * cP ps + 3 * cQ ps + 4 * (cR ps + 1)
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons]
      omega

theorem hl_eq (f : Fh) : (fhead f).length = hl f := by
  cases f <;> rfl

theorem tl_eq (t : Tr) : (ftail t).length = tl t := by
  cases t <;> rfl

theorem len_word (f : Fh) (ps : List Pl) (t : Tr) :
    (word f ps t).length = hl f + (2 * cP ps + 3 * cQ ps + 4 * cR ps) + tl t := by
  unfold word
  rw [List.length_append, List.length_append, len_flatP, hl_eq, tl_eq]
  omega

theorem cP_app (a b : List Pl) : cP (a ++ b) = cP a + cP b := by
  induction a with
  | nil => simp [cP]
  | cons x a ih =>
    cases x with
    | P =>
      show cP (a ++ b) + 1 = cP a + 1 + cP b
      omega
    | Q =>
      show cP (a ++ b) = cP a + cP b
      exact ih
    | R =>
      show cP (a ++ b) = cP a + cP b
      exact ih

theorem cQ_app (a b : List Pl) : cQ (a ++ b) = cQ a + cQ b := by
  induction a with
  | nil => simp [cQ]
  | cons x a ih =>
    cases x with
    | P =>
      show cQ (a ++ b) = cQ a + cQ b
      exact ih
    | Q =>
      show cQ (a ++ b) + 1 = cQ a + 1 + cQ b
      omega
    | R =>
      show cQ (a ++ b) = cQ a + cQ b
      exact ih

theorem cR_app (a b : List Pl) : cR (a ++ b) = cR a + cR b := by
  induction a with
  | nil => simp [cR]
  | cons x a ih =>
    cases x with
    | P =>
      show cR (a ++ b) = cR a + cR b
      exact ih
    | Q =>
      show cR (a ++ b) = cR a + cR b
      exact ih
    | R =>
      show cR (a ++ b) + 1 = cR a + 1 + cR b
      omega

theorem cP_sig (ps : List Pl) : cP (sig ps) = 2 * cQ ps + cR ps := by
  induction ps with
  | nil => rfl
  | cons x ps ih =>
    cases x with
    | P =>
      show cP (sig ps) = 2 * cQ ps + cR ps
      exact ih
    | Q =>
      show cP (sig ps) + 1 + 1 = 2 * (cQ ps + 1) + cR ps
      omega
    | R =>
      show cP (sig ps) + 1 = 2 * cQ ps + (cR ps + 1)
      omega

theorem cQ_sig (ps : List Pl) : cQ (sig ps) = cQ ps + 2 * cR ps := by
  induction ps with
  | nil => rfl
  | cons x ps ih =>
    cases x with
    | P =>
      show cQ (sig ps) = cQ ps + 2 * cR ps
      exact ih
    | Q =>
      show cQ (sig ps) + 1 = cQ ps + 1 + 2 * cR ps
      omega
    | R =>
      show cQ (sig ps) + 1 + 1 = cQ ps + 2 * (cR ps + 1)
      omega

theorem cR_sig (ps : List Pl) : cR (sig ps) = cP ps := by
  induction ps with
  | nil => rfl
  | cons x ps ih =>
    cases x with
    | P =>
      show cR (sig ps) + 1 = cP ps + 1
      omega
    | Q =>
      show cR (sig ps) = cP ps
      exact ih
    | R =>
      show cR (sig ps) = cP ps
      exact ih

/-- One step on the description (head, blocks, tail). -/
def nx (s : Fh × List Pl × Tr) : Fh × List Pl × Tr :=
  (nf s.1, ef s.1 ++ (sig s.2.1 ++ et s.2.2), nt s.2.2)

/-- The length of the word described by s. -/
def Ls (s : Fh × List Pl × Tr) : ℕ := hl s.1 + (2 * cP s.2.1 + 3 * cQ s.2.1 + 4 * cR s.2.1) + tl s.2.2

theorem E (s : Fh × List Pl × Tr) :
    (Ls (nx (nx (nx (nx s)))) : ℤ) = 2 * (Ls (nx (nx (nx s))) : ℤ) + 2 * (Ls (nx s) : ℤ) -
      3 * (Ls s : ℤ) := by
  obtain ⟨f, ps, t⟩ := s
  cases f <;> cases t <;>
    simp only [nx, Ls, nf, nt, ef, et, hl, tl, cP_app, cQ_app, cR_app, cP_sig, cQ_sig, cR_sig,
      cP, cQ, cR] <;>
    push_cast <;> ring

/-- The descriptions of w(1), w(2), ... -/
def st : ℕ → Fh × List Pl × Tr
  | 0 => (Fh.q, [Pl.P], Tr.t0)
  | n + 1 => nx (st n)

theorem w_rep : ∀ n : ℕ, w (n + 1) = word (st n).1 (st n).2.1 (st n).2.2
  | 0 => rfl
  | n + 1 => by
    show step (w (n + 1)) =
      word (nf (st n).1) (ef (st n).1 ++ (sig (st n).2.1 ++ et (st n).2.2)) (nt (st n).2.2)
    rw [w_rep n, key]

theorem len_w (n : ℕ) : (w (n + 1)).length = Ls (st n) := by
  unfold Ls
  rw [w_rep n, len_word]

theorem len_eq : ∀ n : ℕ,
    ((w (n + 1)).length : ℤ) = A288260 (n + 1) ∧ ((w (n + 2)).length : ℤ) = A288260 (n + 2) ∧
    ((w (n + 3)).length : ℤ) = A288260 (n + 3) ∧ ((w (n + 4)).length : ℤ) = A288260 (n + 4)
  | 0 => ⟨by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := len_eq n
    refine ⟨h2, h3, h4, ?_⟩
    show ((w (n + 5)).length : ℤ) = A288260 (n + 5)
    have hA : A288260 (n + 5) =
        2 * A288260 (n + 4) + 2 * A288260 (n + 2) - 3 * A288260 (n + 1) := rfl
    have hE := E (st n)
    have q0 := len_w n
    have q1 := len_w (n + 1)
    have q3 := len_w (n + 3)
    have q4 := len_w (n + 4)
    rw [show st (n + 1) = nx (st n) from rfl, show n + 1 + 1 = n + 2 by omega] at q1
    rw [show st (n + 3) = nx (nx (nx (st n))) from rfl, show n + 3 + 1 = n + 4 by omega] at q3
    rw [show st (n + 4) = nx (nx (nx (nx (st n)))) from rfl,
      show n + 4 + 1 = n + 5 by omega] at q4
    rw [hA, ← h4, ← h2, ← h1, q4, q3, q1, q0]
    exact hE

end FS5A288466

open OMA.S_oeis_a288466 FS5A288466 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288466.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (len_eq m).1
