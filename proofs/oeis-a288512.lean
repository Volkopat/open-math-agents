import OMAStatements.S_oeis_a288512

-- Problem: A288512: 1-limiting word of the mapping 00->0101, 10->001, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288512.lean:0 (declaration OMA.S_oeis_a288512.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: every 1 is read at the start of a token, so the mapping acts separately on the
-- two sides of a cut placed just before a 1 (step_app). For n >= 6 the iterate w(n) is
-- 0^a, then runs P = 10, Q = 100, R = 1000, then 1^(m+1). Each run image starts with 00,
-- which goes to the run before: step(P) 00 = 00 Q, step(Q) 00 = 00 R, step(R) 00 = 00 P P Q.
-- The head alternates 0 -> 000 -> 0 P R, and the last two or three runs before the 1s go
-- through a cycle of ten phases (tailS), each moving a few runs into the body and adding 0 or 1
-- to the final run of 1s. So w(n+6) = word(st n) with a phase, a body Y and m, and the body
-- counts evolve by (p, q, r) -> (2r, p + r, q), characteristic polynomial t^3 - t - 2. In every
-- phase the lengths satisfy the order-13 recurrence of A288511 for all Y and m (E, by ring);
-- the 13 initial values L(6..18) and L(0..5) are computed.

namespace W1A288512

open OMA.S_oeis_a288512

inductive Rn
  | P
  | Q
  | R

/-- The letters of a run: P is 10, Q is 100, R is 1000. -/
def flatR : Rn → List Bool
  | Rn.P => [true, false]
  | Rn.Q => [true, false, false]
  | Rn.R => [true, false, false, false]

def flat : List Rn → List Bool
  | [] => []
  | x :: xs => flatR x ++ flat xs

/-- The mapping on runs: P -> Q, Q -> R, R -> P P Q. -/
def mu : List Rn → List Rn
  | [] => []
  | Rn.P :: ts => Rn.Q :: mu ts
  | Rn.Q :: ts => Rn.R :: mu ts
  | Rn.R :: ts => Rn.P :: Rn.P :: Rn.Q :: mu ts

def cP : List Rn → ℕ
  | [] => 0
  | Rn.P :: ts => cP ts + 1
  | Rn.Q :: ts => cP ts
  | Rn.R :: ts => cP ts

def cQ : List Rn → ℕ
  | [] => 0
  | Rn.P :: ts => cQ ts
  | Rn.Q :: ts => cQ ts + 1
  | Rn.R :: ts => cQ ts

def cR : List Rn → ℕ
  | [] => 0
  | Rn.P :: ts => cR ts
  | Rn.Q :: ts => cR ts
  | Rn.R :: ts => cR ts + 1

theorem step_00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: false :: true :: step r := rfl

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
      false :: true :: false :: true :: (step A ++ step (true :: r))
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

theorem step_ones : ∀ m : ℕ, step (true :: List.replicate m true) = true :: List.replicate m true
  | 0 => rfl
  | m + 1 => by
    show step (true :: true :: List.replicate m true) = true :: true :: List.replicate m true
    rw [step_11, step_ones m]

theorem flat_append : ∀ a b : List Rn, flat (a ++ b) = flat a ++ flat b
  | [], _ => rfl
  | x :: a, b => by
    show flatR x ++ flat (a ++ b) = (flatR x ++ flat a) ++ flat b
    rw [flat_append a b, List.append_assoc]

theorem headY : ∀ (Y : List Rn) (A : List Bool), (∃ r, A = true :: r) →
    ∃ r, flat Y ++ A = true :: r
  | [], _, h => h
  | x :: _, _, _ => by
    cases x <;> exact ⟨_, rfl⟩

/-- The body: every run donates the leading 00 of its image to the run before. -/
theorem keyY : ∀ (Y : List Rn) (r G : List Bool), step (true :: r) = false :: false :: G →
    step (flat Y ++ true :: r) = false :: false :: (flat (mu Y) ++ G)
  | [], _, _, h => h
  | x :: Y, r, G, h => by
    obtain ⟨r2, hr2⟩ := headY Y (true :: r) ⟨r, rfl⟩
    have e1 : flat (x :: Y) ++ true :: r = flatR x ++ true :: r2 := by
      rw [← hr2]
      exact List.append_assoc (flatR x) (flat Y) (true :: r)
    rw [e1, step_app (flatR x) r2, ← hr2, keyY Y r G h]
    cases x <;> rfl

inductive Ph
  | p0
  | p1
  | p2
  | p3
  | p4
  | p5
  | p6
  | p7
  | p8
  | p9

def np : Ph → Ph
  | Ph.p0 => Ph.p1
  | Ph.p1 => Ph.p2
  | Ph.p2 => Ph.p3
  | Ph.p3 => Ph.p4
  | Ph.p4 => Ph.p5
  | Ph.p5 => Ph.p6
  | Ph.p6 => Ph.p7
  | Ph.p7 => Ph.p8
  | Ph.p8 => Ph.p9
  | Ph.p9 => Ph.p0

/-- true when the word starts with 000, false when it starts with 0 then 1. -/
def par : Ph → Bool
  | Ph.p0 => true
  | Ph.p1 => false
  | Ph.p2 => true
  | Ph.p3 => false
  | Ph.p4 => true
  | Ph.p5 => false
  | Ph.p6 => true
  | Ph.p7 => false
  | Ph.p8 => true
  | Ph.p9 => false

/-- The last runs before the final 1s, in each phase. -/
def S : Ph → List Rn
  | Ph.p0 => [Rn.Q, Rn.R]
  | Ph.p1 => [Rn.R, Rn.P, Rn.P]
  | Ph.p2 => [Rn.P, Rn.Q, Rn.Q]
  | Ph.p3 => [Rn.Q, Rn.R, Rn.P]
  | Ph.p4 => [Rn.P, Rn.P, Rn.Q]
  | Ph.p5 => [Rn.Q, Rn.Q, Rn.P]
  | Ph.p6 => [Rn.R, Rn.R]
  | Ph.p7 => [Rn.Q, Rn.P, Rn.P]
  | Ph.p8 => [Rn.R, Rn.Q]
  | Ph.p9 => [Rn.P, Rn.Q, Rn.P]

/-- The runs that move from the end into the body, in each phase. -/
def Z : Ph → List Rn
  | Ph.p0 => []
  | Ph.p1 => [Rn.P]
  | Ph.p2 => []
  | Ph.p3 => [Rn.R]
  | Ph.p4 => []
  | Ph.p5 => []
  | Ph.p6 => [Rn.P, Rn.P]
  | Ph.p7 => []
  | Ph.p8 => [Rn.P]
  | Ph.p9 => []

/-- The growth of the final run of 1s, in each phase. -/
def dl : Ph → ℕ
  | Ph.p0 => 1
  | Ph.p1 => 1
  | Ph.p2 => 0
  | Ph.p3 => 1
  | Ph.p4 => 0
  | Ph.p5 => 1
  | Ph.p6 => 1
  | Ph.p7 => 1
  | Ph.p8 => 0
  | Ph.p9 => 1

def sl : Ph → ℕ
  | Ph.p0 => 7
  | Ph.p1 => 8
  | Ph.p2 => 8
  | Ph.p3 => 9
  | Ph.p4 => 7
  | Ph.p5 => 8
  | Ph.p6 => 8
  | Ph.p7 => 7
  | Ph.p8 => 7
  | Ph.p9 => 7

def hz : Bool → List Bool
  | true => [false, false, false]
  | false => [false]

def hzl : Bool → ℕ
  | true => 3
  | false => 1

def Hh : Bool → List Rn
  | true => [Rn.P, Rn.R]
  | false => []

/-- The word described by a phase, a body and the number m (the word ends with m + 1 ones). -/
def word : Ph × List Rn × ℕ → List Bool
  | (p, Y, m) => hz (par p) ++ (flat Y ++ (flat (S p) ++ true :: List.replicate m true))

def nx : Ph × List Rn × ℕ → Ph × List Rn × ℕ
  | (p, Y, m) => (np p, Hh (par p) ++ (mu Y ++ Z p), m + dl p)

theorem headS (p : Ph) (m : ℕ) : ∃ r, flat (S p) ++ true :: List.replicate m true = true :: r := by
  cases p <;> exact ⟨_, rfl⟩

theorem tailS (p : Ph) (m : ℕ) :
    step (flat (S p) ++ true :: List.replicate m true) =
      false :: false :: (flat (Z p ++ S (np p)) ++ true :: List.replicate (m + dl p) true) := by
  rw [step_app, step_ones]
  cases p <;> rfl

theorem head1 (X G : List Bool) (hX : ∃ r, X = true :: r) (h : step X = false :: false :: G) :
    step (false :: X) = false :: false :: false :: G := by
  obtain ⟨r, rfl⟩ := hX
  rw [step_01, h]

theorem head3 (X G : List Bool) (hX : ∃ r, X = true :: r) (h : step X = false :: false :: G) :
    step (false :: false :: false :: X) =
      false :: true :: false :: true :: false :: false :: false :: G := by
  obtain ⟨r, rfl⟩ := hX
  rw [step_00, step_01, h]

theorem keyW (s : Ph × List Rn × ℕ) : step (word s) = word (nx s) := by
  obtain ⟨p, Y, m⟩ := s
  obtain ⟨r, hr⟩ := headS p m
  have hT : step (true :: r) =
      false :: false :: (flat (Z p ++ S (np p)) ++ true :: List.replicate (m + dl p) true) := by
    rw [← hr]
    exact tailS p m
  have hB := keyY Y r _ hT
  rw [← hr] at hB
  have hX := headY Y (flat (S p) ++ true :: List.replicate m true) ⟨r, hr⟩
  have hpn : par (np p) = !par p := by
    cases p <;> rfl
  show step (hz (par p) ++ (flat Y ++ (flat (S p) ++ true :: List.replicate m true))) =
    hz (par (np p)) ++ (flat (Hh (par p) ++ (mu Y ++ Z p)) ++
      (flat (S (np p)) ++ true :: List.replicate (m + dl p) true))
  rw [hpn]
  cases par p with
  | false =>
    show step (false :: (flat Y ++ (flat (S p) ++ true :: List.replicate m true))) =
      false :: false :: false :: (flat ([] ++ (mu Y ++ Z p)) ++
        (flat (S (np p)) ++ true :: List.replicate (m + dl p) true))
    rw [head1 _ _ hX hB]
    simp only [List.nil_append, flat_append, List.append_assoc]
  | true =>
    show step (false :: false :: false :: (flat Y ++ (flat (S p) ++ true :: List.replicate m true))) =
      false :: (flat ([Rn.P, Rn.R] ++ (mu Y ++ Z p)) ++
        (flat (S (np p)) ++ true :: List.replicate (m + dl p) true))
    rw [head3 _ _ hX hB]
    simp only [flat, flatR, flat_append, List.cons_append, List.nil_append, List.append_assoc]

def st : ℕ → Ph × List Rn × ℕ
  | 0 => (Ph.p4, [Rn.Q], 3)
  | n + 1 => nx (st n)

theorem w_rep : ∀ n : ℕ, w (n + 6) = word (st n)
  | 0 => rfl
  | n + 1 => by
    show step (w (n + 6)) = word (nx (st n))
    rw [w_rep n, keyW]

theorem len_flat : ∀ Y : List Rn, (flat Y).length = 2 * cP Y + 3 * cQ Y + 4 * cR Y
  | [] => rfl
  | x :: Y => by
    have ih := len_flat Y
    have e : (flat (x :: Y)).length = (flatR x).length + (flat Y).length := by
      rw [show flat (x :: Y) = flatR x ++ flat Y from rfl, List.length_append]
    rw [e, ih]
    cases x with
    | P =>
      have hl : (flatR Rn.P).length = 2 := rfl
      show (flatR Rn.P).length + (2 * cP Y + 3 * cQ Y + 4 * cR Y) = 2 * (cP Y + 1) + 3 * cQ Y + 4 * cR Y
      omega
    | Q =>
      have hl : (flatR Rn.Q).length = 3 := rfl
      show (flatR Rn.Q).length + (2 * cP Y + 3 * cQ Y + 4 * cR Y) = 2 * cP Y + 3 * (cQ Y + 1) + 4 * cR Y
      omega
    | R =>
      have hl : (flatR Rn.R).length = 4 := rfl
      show (flatR Rn.R).length + (2 * cP Y + 3 * cQ Y + 4 * cR Y) = 2 * cP Y + 3 * cQ Y + 4 * (cR Y + 1)
      omega

theorem cP_app : ∀ a b : List Rn, cP (a ++ b) = cP a + cP b
  | [], b => by
    show cP b = 0 + cP b
    omega
  | x :: a, b => by
    have ih := cP_app a b
    cases x with
    | P =>
      show cP (a ++ b) + 1 = cP a + 1 + cP b
      omega
    | Q =>
      show cP (a ++ b) = cP a + cP b
      omega
    | R =>
      show cP (a ++ b) = cP a + cP b
      omega

theorem cQ_app : ∀ a b : List Rn, cQ (a ++ b) = cQ a + cQ b
  | [], b => by
    show cQ b = 0 + cQ b
    omega
  | x :: a, b => by
    have ih := cQ_app a b
    cases x with
    | P =>
      show cQ (a ++ b) = cQ a + cQ b
      omega
    | Q =>
      show cQ (a ++ b) + 1 = cQ a + 1 + cQ b
      omega
    | R =>
      show cQ (a ++ b) = cQ a + cQ b
      omega

theorem cR_app : ∀ a b : List Rn, cR (a ++ b) = cR a + cR b
  | [], b => by
    show cR b = 0 + cR b
    omega
  | x :: a, b => by
    have ih := cR_app a b
    cases x with
    | P =>
      show cR (a ++ b) = cR a + cR b
      omega
    | Q =>
      show cR (a ++ b) = cR a + cR b
      omega
    | R =>
      show cR (a ++ b) + 1 = cR a + 1 + cR b
      omega

theorem cP_mu : ∀ ts : List Rn, cP (mu ts) = 2 * cR ts
  | [] => rfl
  | x :: ts => by
    have ih := cP_mu ts
    cases x with
    | P =>
      show cP (mu ts) = 2 * cR ts
      omega
    | Q =>
      show cP (mu ts) = 2 * cR ts
      omega
    | R =>
      show cP (mu ts) + 1 + 1 = 2 * (cR ts + 1)
      omega

theorem cQ_mu : ∀ ts : List Rn, cQ (mu ts) = cP ts + cR ts
  | [] => rfl
  | x :: ts => by
    have ih := cQ_mu ts
    cases x with
    | P =>
      show cQ (mu ts) + 1 = (cP ts + 1) + cR ts
      omega
    | Q =>
      show cQ (mu ts) = cP ts + cR ts
      omega
    | R =>
      show cQ (mu ts) + 1 = cP ts + (cR ts + 1)
      omega

theorem cR_mu : ∀ ts : List Rn, cR (mu ts) = cQ ts
  | [] => rfl
  | x :: ts => by
    have ih := cR_mu ts
    cases x with
    | P =>
      show cR (mu ts) = cQ ts
      omega
    | Q =>
      show cR (mu ts) + 1 = (cQ ts + 1)
      omega
    | R =>
      show cR (mu ts) = cQ ts
      omega

theorem hz_len : ∀ b : Bool, (hz b).length = hzl b
  | true => rfl
  | false => rfl

theorem sl_eq (p : Ph) : (flat (S p)).length = sl p := by
  cases p <;> rfl

/-- The length of the word described by s. -/
def Ls : Ph × List Rn × ℕ → ℕ
  | (p, Y, m) => hzl (par p) + (2 * cP Y + 3 * cQ Y + 4 * cR Y) + sl p + m + 1

theorem len_word (s : Ph × List Rn × ℕ) : (word s).length = Ls s := by
  obtain ⟨p, Y, m⟩ := s
  have h1 := hz_len (par p)
  have h2 := sl_eq p
  have h3 := len_flat Y
  show (hz (par p) ++ (flat Y ++ (flat (S p) ++ true :: List.replicate m true))).length =
    hzl (par p) + (2 * cP Y + 3 * cQ Y + 4 * cR Y) + sl p + m + 1
  rw [List.length_append, List.length_append, List.length_append, List.length_cons,
    List.length_replicate]
  omega

theorem len_w (n : ℕ) : (w (n + 6)).length = Ls (st n) := by
  rw [w_rep n]
  exact len_word (st n)

-- The recurrence of A288511 for the lengths, from phase 0, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E0 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p0, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p0, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p0, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p0, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p0, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p0, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p0, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p0, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p0, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p0, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p0, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p0, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p0, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p0, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 1, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E1 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p1, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p1, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p1, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p1, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p1, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p1, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p1, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p1, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p1, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p1, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p1, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p1, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p1, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p1, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 2, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E2 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p2, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p2, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p2, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p2, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p2, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p2, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p2, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p2, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p2, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p2, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p2, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p2, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p2, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p2, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 3, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E3 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p3, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p3, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p3, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p3, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p3, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p3, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p3, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p3, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p3, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p3, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p3, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p3, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p3, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p3, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 4, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E4 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p4, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p4, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p4, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p4, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p4, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p4, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p4, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p4, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p4, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p4, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p4, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p4, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p4, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p4, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 5, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E5 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p5, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p5, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p5, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p5, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p5, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p5, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p5, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p5, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p5, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p5, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p5, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p5, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p5, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p5, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 6, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E6 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p6, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p6, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p6, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p6, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p6, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p6, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p6, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p6, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p6, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p6, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p6, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p6, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p6, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p6, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 7, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E7 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p7, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p7, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p7, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p7, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p7, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p7, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p7, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p7, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p7, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p7, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p7, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p7, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p7, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p7, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 8, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E8 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p8, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p8, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p8, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p8, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p8, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p8, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p8, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p8, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p8, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p8, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p8, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p8, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p8, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p8, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

-- The recurrence of A288511 for the lengths, from phase 9, for every body and m.
set_option maxHeartbeats 4000000 in
theorem E9 (Y : List Rn) (m : ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx ((Ph.p9, Y, m))))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p9, Y, m))))))))))))) : ℤ) -
      (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p9, Y, m)))))))))))) : ℤ) + 2 * (Ls (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx (Ph.p9, Y, m))))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx (nx (nx (nx (nx (Ph.p9, Y, m)))))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx
      (Ph.p9, Y, m))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (Ph.p9, Y, m)))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (Ph.p9, Y, m))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx
      (Ph.p9, Y, m)))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (Ph.p9, Y, m))))) : ℤ) - 3 * (Ls (nx (nx
      (nx (Ph.p9, Y, m)))) : ℤ) + 2 * (Ls (nx (nx (Ph.p9, Y, m))) : ℤ) - 3 * (Ls (nx (Ph.p9, Y,
      m)) : ℤ) + 2 * (Ls (Ph.p9, Y, m) : ℤ) := by
  simp only [nx, Ls, np, par, Hh, hzl, sl, Z, dl, cP_app, cQ_app, cR_app, cP_mu, cQ_mu,
    cR_mu, cP, cQ, cR]
  push_cast
  ring

/-- In every phase the lengths satisfy the recurrence of A288511, for every body and m. -/
theorem E (s : Ph × List Rn × ℕ) :
    (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (s)))))))))))))) : ℤ) =
      2 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx (nx s)))))))))))) : ℤ) - (Ls (nx (nx
      (nx (nx (nx (nx (nx (nx (nx (nx (nx s))))))))))) : ℤ) + 2 * (Ls (nx (nx (nx (nx (nx (nx (nx
      (nx (nx (nx s)))))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx (nx s))))))))) : ℤ)
      + 4 * (Ls (nx (nx (nx (nx (nx (nx (nx (nx s)))))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx (nx (nx
      (nx s))))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx (nx (nx s)))))) : ℤ) - 4 * (Ls (nx (nx (nx (nx
      (nx s))))) : ℤ) + 4 * (Ls (nx (nx (nx (nx s)))) : ℤ) - 3 * (Ls (nx (nx (nx s))) : ℤ) + 2 *
      (Ls (nx (nx s)) : ℤ) - 3 * (Ls (nx s) : ℤ) + 2 * (Ls s : ℤ) := by
  obtain ⟨p, Y, m⟩ := s
  cases p with
  | p0 => exact E0 Y m
  | p1 => exact E1 Y m
  | p2 => exact E2 Y m
  | p3 => exact E3 Y m
  | p4 => exact E4 Y m
  | p5 => exact E5 Y m
  | p6 => exact E6 Y m
  | p7 => exact E7 Y m
  | p8 => exact E8 Y m
  | p9 => exact E9 Y m

theorem len_eq : ∀ n : ℕ,
    (Ls (st n) : ℤ) = A288511 (n + 6) ∧ (Ls (st (n + 1)) : ℤ) = A288511 (n + 7) ∧
    (Ls (st (n + 2)) : ℤ) = A288511 (n + 8) ∧ (Ls (st (n + 3)) : ℤ) = A288511 (n + 9) ∧
    (Ls (st (n + 4)) : ℤ) = A288511 (n + 10) ∧ (Ls (st (n + 5)) : ℤ) = A288511 (n + 11) ∧
    (Ls (st (n + 6)) : ℤ) = A288511 (n + 12) ∧ (Ls (st (n + 7)) : ℤ) = A288511 (n + 13) ∧
    (Ls (st (n + 8)) : ℤ) = A288511 (n + 14) ∧ (Ls (st (n + 9)) : ℤ) = A288511 (n + 15) ∧
    (Ls (st (n + 10)) : ℤ) = A288511 (n + 16) ∧ (Ls (st (n + 11)) : ℤ) = A288511 (n + 17) ∧
    (Ls (st (n + 12)) : ℤ) = A288511 (n + 18)
  | 0 => ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩
  | n + 1 => by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := len_eq n
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ?_⟩
    show (Ls (st (n + 13)) : ℤ) = A288511 (n + 19)
    have hA : A288511 (n + 19) =
        2 * A288511 (n + 18) - A288511 (n + 17) + 2 * A288511 (n + 16) - 4 * A288511 (n + 15) + 4
        * A288511 (n + 14) - 4 * A288511 (n + 13) + 4 * A288511 (n + 12) - 4 * A288511 (n + 11) +
        4 * A288511 (n + 10) - 3 * A288511 (n + 9) + 2 * A288511 (n + 8) - 3 * A288511 (n + 7) +
        2 * A288511 (n + 6) := rfl
    have hE : (Ls (st (n + 13)) : ℤ) =
        2 * (Ls (st (n + 12)) : ℤ) - (Ls (st (n + 11)) : ℤ) + 2 * (Ls (st (n + 10)) : ℤ) - 4 *
        (Ls (st (n + 9)) : ℤ) + 4 * (Ls (st (n + 8)) : ℤ) - 4 * (Ls (st (n + 7)) : ℤ) + 4 * (Ls
        (st (n + 6)) : ℤ) - 4 * (Ls (st (n + 5)) : ℤ) + 4 * (Ls (st (n + 4)) : ℤ) - 3 * (Ls (st
        (n + 3)) : ℤ) + 2 * (Ls (st (n + 2)) : ℤ) - 3 * (Ls (st (n + 1)) : ℤ) + 2 * (Ls (st n) :
        ℤ) := E (st n)
    rw [hA, ← h12, ← h11, ← h10, ← h9, ← h8, ← h7, ← h6, ← h5, ← h4, ← h3, ← h2, ← h1, ← h0]
    exact hE

end W1A288512

open OMA.S_oeis_a288512 W1A288512 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288512.main := by
  intro n
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [len_w m]
    exact (len_eq m).1
