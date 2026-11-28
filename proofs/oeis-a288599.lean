import OMAStatements.S_oeis_a288599
import Mathlib

-- From word 1 on, every word is the prefix [false] followed by blocks T F^k (k in [0, 1, 3, 4]), and the
-- rewriting acts on the blocks as a substitution: TF^0 -> TF^0; TF^1 -> TF^3; TF^3 -> TF^4 TF^1 TF^0; TF^4 -> TF^4 TF^1 TF^1.
inductive Blk_oeis_a288599 where
  | k0 : Blk_oeis_a288599
  | k1 : Blk_oeis_a288599
  | k3 : Blk_oeis_a288599
  | k4 : Blk_oeis_a288599

def render_oeis_a288599 : List Blk_oeis_a288599 → List Bool
  | [] => []
  | Blk_oeis_a288599.k0 :: r => true :: render_oeis_a288599 r
  | Blk_oeis_a288599.k1 :: r => true :: false :: render_oeis_a288599 r
  | Blk_oeis_a288599.k3 :: r => true :: false :: false :: false :: render_oeis_a288599 r
  | Blk_oeis_a288599.k4 :: r => true :: false :: false :: false :: false :: render_oeis_a288599 r

def phi_oeis_a288599 : Blk_oeis_a288599 → List Blk_oeis_a288599
  | Blk_oeis_a288599.k0 => [Blk_oeis_a288599.k0]
  | Blk_oeis_a288599.k1 => [Blk_oeis_a288599.k3]
  | Blk_oeis_a288599.k3 => [Blk_oeis_a288599.k4, Blk_oeis_a288599.k1, Blk_oeis_a288599.k0]
  | Blk_oeis_a288599.k4 => [Blk_oeis_a288599.k4, Blk_oeis_a288599.k1, Blk_oeis_a288599.k1]

theorem w0_oeis_a288599 : OMA.S_oeis_a288599.rewrite [] = [] := by
  first | rw [OMA.S_oeis_a288599.rewrite] | simp [OMA.S_oeis_a288599.rewrite]

theorem w1_oeis_a288599 (x : Bool) : OMA.S_oeis_a288599.rewrite [x] = [x] := by
  first | rw [OMA.S_oeis_a288599.rewrite] | simp [OMA.S_oeis_a288599.rewrite]

theorem wFF_oeis_a288599 (w : List Bool) : OMA.S_oeis_a288599.rewrite (false :: false :: w) = [false, true, false, true] ++ OMA.S_oeis_a288599.rewrite w := by
  first | rw [OMA.S_oeis_a288599.rewrite] | simp [OMA.S_oeis_a288599.rewrite]

theorem wTF_oeis_a288599 (w : List Bool) : OMA.S_oeis_a288599.rewrite (true :: false :: w) = [true, false, false, false] ++ OMA.S_oeis_a288599.rewrite w := by
  first | rw [OMA.S_oeis_a288599.rewrite] | simp [OMA.S_oeis_a288599.rewrite]

theorem wFT_oeis_a288599 (w : List Bool) : OMA.S_oeis_a288599.rewrite (false :: true :: w) = false :: OMA.S_oeis_a288599.rewrite (true :: w) := by
  first | rw [OMA.S_oeis_a288599.rewrite] | simp [OMA.S_oeis_a288599.rewrite]

theorem wTT_oeis_a288599 (w : List Bool) : OMA.S_oeis_a288599.rewrite (true :: true :: w) = true :: OMA.S_oeis_a288599.rewrite (true :: w) := by
  first | rw [OMA.S_oeis_a288599.rewrite] | simp [OMA.S_oeis_a288599.rewrite]

theorem head_oeis_a288599 (y : Blk_oeis_a288599) (s : List Blk_oeis_a288599) : ∃ w, render_oeis_a288599 (y :: s) = true :: w := by
  cases y <;> exact ⟨_, rfl⟩

-- Rewriting a concatenation of blocks applies the substitution block by block.
theorem rw_oeis_a288599 (bs : List Blk_oeis_a288599) :
    OMA.S_oeis_a288599.rewrite (render_oeis_a288599 bs) = render_oeis_a288599 (bs.flatMap phi_oeis_a288599) := by
  induction bs with
  | nil => exact w0_oeis_a288599
  | cons x r ih =>
    cases x with
    | k0 =>
      cases r with
      | nil =>
        show OMA.S_oeis_a288599.rewrite [true] = [true]
        rw [w1_oeis_a288599]
        all_goals rfl
      | cons y r' =>
        obtain ⟨w, hw⟩ := head_oeis_a288599 y r'
        have e1 : render_oeis_a288599 (Blk_oeis_a288599.k0 :: y :: r') = true :: true :: w := by
          show true :: render_oeis_a288599 (y :: r') = _
          rw [hw]
        have e2 : (Blk_oeis_a288599.k0 :: y :: r').flatMap phi_oeis_a288599 = Blk_oeis_a288599.k0 :: (y :: r').flatMap phi_oeis_a288599 := rfl
        rw [e1, wTT_oeis_a288599, ← hw, ih, e2]
        all_goals rfl
    | k1 =>
      have e1 : render_oeis_a288599 (Blk_oeis_a288599.k1 :: r) = true :: false :: render_oeis_a288599 r := rfl
      have e2 : (Blk_oeis_a288599.k1 :: r).flatMap phi_oeis_a288599 = Blk_oeis_a288599.k3 :: r.flatMap phi_oeis_a288599 := rfl
      rw [e1, wTF_oeis_a288599, ih, e2]
      all_goals rfl
    | k3 =>
      have e1 : render_oeis_a288599 (Blk_oeis_a288599.k3 :: r) = true :: false :: false :: false :: render_oeis_a288599 r := rfl
      have e2 : (Blk_oeis_a288599.k3 :: r).flatMap phi_oeis_a288599 = Blk_oeis_a288599.k4 :: Blk_oeis_a288599.k1 :: Blk_oeis_a288599.k0 :: r.flatMap phi_oeis_a288599 := rfl
      rw [e1, wTF_oeis_a288599, wFF_oeis_a288599, ih, e2]
      all_goals rfl
    | k4 =>
      cases r with
      | nil =>
        show OMA.S_oeis_a288599.rewrite [true, false, false, false, false] = [true, false, false, false, false, true, false, true, false]
        rw [wTF_oeis_a288599, wFF_oeis_a288599, w1_oeis_a288599]
        all_goals rfl
      | cons y r' =>
        obtain ⟨w, hw⟩ := head_oeis_a288599 y r'
        have e1 : render_oeis_a288599 (Blk_oeis_a288599.k4 :: y :: r') = true :: false :: false :: false :: false :: true :: w := by
          show true :: false :: false :: false :: false :: render_oeis_a288599 (y :: r') = _
          rw [hw]
        have e2 : (Blk_oeis_a288599.k4 :: y :: r').flatMap phi_oeis_a288599 = Blk_oeis_a288599.k4 :: Blk_oeis_a288599.k1 :: Blk_oeis_a288599.k1 :: (y :: r').flatMap phi_oeis_a288599 := rfl
        rw [e1, wTF_oeis_a288599, wFF_oeis_a288599, wFT_oeis_a288599, ← hw, ih, e2]
        all_goals rfl

theorem rwP_oeis_a288599 (bs : List Blk_oeis_a288599) :
    OMA.S_oeis_a288599.rewrite (false :: render_oeis_a288599 bs) = false :: render_oeis_a288599 (bs.flatMap phi_oeis_a288599) := by
  cases bs with
  | nil =>
    show OMA.S_oeis_a288599.rewrite [false] = [false]
    rw [w1_oeis_a288599]
    all_goals rfl
  | cons y s =>
    obtain ⟨w, hw⟩ := head_oeis_a288599 y s
    rw [hw, wFT_oeis_a288599, ← hw, rw_oeis_a288599]
    all_goals rfl

-- Number of blocks of each kind.
def cnt0_oeis_a288599 : List Blk_oeis_a288599 → ℕ
  | [] => 0
  | Blk_oeis_a288599.k0 :: r => 1 + cnt0_oeis_a288599 r
  | Blk_oeis_a288599.k1 :: r => cnt0_oeis_a288599 r
  | Blk_oeis_a288599.k3 :: r => cnt0_oeis_a288599 r
  | Blk_oeis_a288599.k4 :: r => cnt0_oeis_a288599 r

def cnt1_oeis_a288599 : List Blk_oeis_a288599 → ℕ
  | [] => 0
  | Blk_oeis_a288599.k0 :: r => cnt1_oeis_a288599 r
  | Blk_oeis_a288599.k1 :: r => 1 + cnt1_oeis_a288599 r
  | Blk_oeis_a288599.k3 :: r => cnt1_oeis_a288599 r
  | Blk_oeis_a288599.k4 :: r => cnt1_oeis_a288599 r

def cnt3_oeis_a288599 : List Blk_oeis_a288599 → ℕ
  | [] => 0
  | Blk_oeis_a288599.k0 :: r => cnt3_oeis_a288599 r
  | Blk_oeis_a288599.k1 :: r => cnt3_oeis_a288599 r
  | Blk_oeis_a288599.k3 :: r => 1 + cnt3_oeis_a288599 r
  | Blk_oeis_a288599.k4 :: r => cnt3_oeis_a288599 r

def cnt4_oeis_a288599 : List Blk_oeis_a288599 → ℕ
  | [] => 0
  | Blk_oeis_a288599.k0 :: r => cnt4_oeis_a288599 r
  | Blk_oeis_a288599.k1 :: r => cnt4_oeis_a288599 r
  | Blk_oeis_a288599.k3 :: r => cnt4_oeis_a288599 r
  | Blk_oeis_a288599.k4 :: r => 1 + cnt4_oeis_a288599 r

theorem len_oeis_a288599 (bs : List Blk_oeis_a288599) :
    (render_oeis_a288599 bs).length = 1 * cnt0_oeis_a288599 bs + 2 * cnt1_oeis_a288599 bs + 4 * cnt3_oeis_a288599 bs + 5 * cnt4_oeis_a288599 bs := by
  induction bs with
  | nil => rfl
  | cons x r ih =>
    cases x with
    | k0 =>
      show (render_oeis_a288599 r).length + 1 = 1 * (1 + cnt0_oeis_a288599 r) + 2 * (cnt1_oeis_a288599 r) + 4 * (cnt3_oeis_a288599 r) + 5 * (cnt4_oeis_a288599 r)
      omega
    | k1 =>
      show (render_oeis_a288599 r).length + 1 + 1 = 1 * (cnt0_oeis_a288599 r) + 2 * (1 + cnt1_oeis_a288599 r) + 4 * (cnt3_oeis_a288599 r) + 5 * (cnt4_oeis_a288599 r)
      omega
    | k3 =>
      show (render_oeis_a288599 r).length + 1 + 1 + 1 + 1 = 1 * (cnt0_oeis_a288599 r) + 2 * (cnt1_oeis_a288599 r) + 4 * (1 + cnt3_oeis_a288599 r) + 5 * (cnt4_oeis_a288599 r)
      omega
    | k4 =>
      show (render_oeis_a288599 r).length + 1 + 1 + 1 + 1 + 1 = 1 * (cnt0_oeis_a288599 r) + 2 * (cnt1_oeis_a288599 r) + 4 * (cnt3_oeis_a288599 r) + 5 * (1 + cnt4_oeis_a288599 r)
      omega

theorem step_oeis_a288599 (bs : List Blk_oeis_a288599) :
    cnt0_oeis_a288599 (bs.flatMap phi_oeis_a288599) = 1 * cnt0_oeis_a288599 bs + 1 * cnt3_oeis_a288599 bs ∧
    cnt1_oeis_a288599 (bs.flatMap phi_oeis_a288599) = 1 * cnt3_oeis_a288599 bs + 2 * cnt4_oeis_a288599 bs ∧
    cnt3_oeis_a288599 (bs.flatMap phi_oeis_a288599) = 1 * cnt1_oeis_a288599 bs ∧
    cnt4_oeis_a288599 (bs.flatMap phi_oeis_a288599) = 1 * cnt3_oeis_a288599 bs + 1 * cnt4_oeis_a288599 bs := by
  induction bs with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x r ih =>
    obtain ⟨h0, h1, h3, h4⟩ := ih
    cases x with
    | k0 =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · show 1 + cnt0_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (1 + cnt0_oeis_a288599 r) + 1 * (cnt3_oeis_a288599 r)
        omega
      · show cnt1_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt3_oeis_a288599 r) + 2 * (cnt4_oeis_a288599 r)
        omega
      · show cnt3_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt1_oeis_a288599 r)
        omega
      · show cnt4_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt3_oeis_a288599 r) + 1 * (cnt4_oeis_a288599 r)
        omega
    | k1 =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · show cnt0_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt0_oeis_a288599 r) + 1 * (cnt3_oeis_a288599 r)
        omega
      · show cnt1_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt3_oeis_a288599 r) + 2 * (cnt4_oeis_a288599 r)
        omega
      · show 1 + cnt3_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (1 + cnt1_oeis_a288599 r)
        omega
      · show cnt4_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt3_oeis_a288599 r) + 1 * (cnt4_oeis_a288599 r)
        omega
    | k3 =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · show 1 + cnt0_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt0_oeis_a288599 r) + 1 * (1 + cnt3_oeis_a288599 r)
        omega
      · show 1 + cnt1_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (1 + cnt3_oeis_a288599 r) + 2 * (cnt4_oeis_a288599 r)
        omega
      · show cnt3_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt1_oeis_a288599 r)
        omega
      · show 1 + cnt4_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (1 + cnt3_oeis_a288599 r) + 1 * (cnt4_oeis_a288599 r)
        omega
    | k4 =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · show cnt0_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt0_oeis_a288599 r) + 1 * (cnt3_oeis_a288599 r)
        omega
      · show 1 + (1 + cnt1_oeis_a288599 (r.flatMap phi_oeis_a288599)) = 1 * (cnt3_oeis_a288599 r) + 2 * (1 + cnt4_oeis_a288599 r)
        omega
      · show cnt3_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt1_oeis_a288599 r)
        omega
      · show 1 + cnt4_oeis_a288599 (r.flatMap phi_oeis_a288599) = 1 * (cnt3_oeis_a288599 r) + 1 * (1 + cnt4_oeis_a288599 r)
        omega

def blocks_oeis_a288599 : ℕ → List Blk_oeis_a288599
  | 0 => [Blk_oeis_a288599.k1, Blk_oeis_a288599.k0]
  | n + 1 => (blocks_oeis_a288599 n).flatMap phi_oeis_a288599

theorem word_oeis_a288599 (n : ℕ) :
    OMA.S_oeis_a288599.word (n + 1) = false :: render_oeis_a288599 (blocks_oeis_a288599 n) := by
  induction n with
  | zero =>
    show OMA.S_oeis_a288599.rewrite [false, false] = [false, true, false, true]
    rw [wFF_oeis_a288599, w0_oeis_a288599]
    all_goals rfl
  | succ n ih =>
    show OMA.S_oeis_a288599.rewrite (OMA.S_oeis_a288599.word (n + 1)) = _
    rw [ih, rwP_oeis_a288599]
    all_goals rfl

theorem wlen_oeis_a288599 (n : ℕ) :
    (OMA.S_oeis_a288599.word (n + 1)).length = 1 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 n) + 2 * cnt1_oeis_a288599 (blocks_oeis_a288599 n) + 4 * cnt3_oeis_a288599 (blocks_oeis_a288599 n) + 5 * cnt4_oeis_a288599 (blocks_oeis_a288599 n)) := by
  rw [word_oeis_a288599]
  simp only [List.length_cons]
  rw [len_oeis_a288599]
  omega

theorem evo_oeis_a288599 (n : ℕ) :
    cnt0_oeis_a288599 (blocks_oeis_a288599 (n + 1)) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 n) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 n)) ∧
    cnt1_oeis_a288599 (blocks_oeis_a288599 (n + 1)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 n) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 n)) ∧
    cnt3_oeis_a288599 (blocks_oeis_a288599 (n + 1)) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 n)) ∧
    cnt4_oeis_a288599 (blocks_oeis_a288599 (n + 1)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 n) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 n)) := by
  obtain ⟨h0, h1, h3, h4⟩ := step_oeis_a288599 (blocks_oeis_a288599 n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show cnt0_oeis_a288599 ((blocks_oeis_a288599 n).flatMap phi_oeis_a288599) = _
    omega
  · show cnt1_oeis_a288599 ((blocks_oeis_a288599 n).flatMap phi_oeis_a288599) = _
    omega
  · show cnt3_oeis_a288599 ((blocks_oeis_a288599 n).flatMap phi_oeis_a288599) = _
    omega
  · show cnt4_oeis_a288599 ((blocks_oeis_a288599 n).flatMap phi_oeis_a288599) = _
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a288599.main := by
  have c0_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 0) = 1 := rfl
  have c0_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 0) = 1 := rfl
  have c0_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 0) = 0 := rfl
  have c0_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 0) = 0 := rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ =>
      have rv : OMA.S_oeis_a288599.reference 1 = 4 := rfl
      rw [wlen_oeis_a288599 0, rv]
      omega
    | 2, _ =>
      have rv : OMA.S_oeis_a288599.reference 2 = 6 := rfl
      have a0_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 0) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).1
      have a0_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.1
      have a0_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.2.1
      have a0_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.2.2
      rw [wlen_oeis_a288599 1, rv]
      omega
    | 3, _ =>
      have rv : OMA.S_oeis_a288599.reference 3 = 10 := rfl
      have a0_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 0) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).1
      have a0_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.1
      have a0_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.2.1
      have a0_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.2.2
      have a1_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 1) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).1
      have a1_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 1) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).2.1
      have a1_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).2.2.1
      have a1_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 1) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).2.2.2
      rw [wlen_oeis_a288599 2, rv]
      omega
    | 4, _ =>
      have rv : OMA.S_oeis_a288599.reference 4 = 16 := rfl
      have a0_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 0) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).1
      have a0_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.1
      have a0_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.2.1
      have a0_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 1) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 0) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 0)) := (evo_oeis_a288599 0).2.2.2
      have a1_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 1) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).1
      have a1_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 1) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).2.1
      have a1_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).2.2.1
      have a1_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 2) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 1) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 1)) := (evo_oeis_a288599 1).2.2.2
      have a2_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 3) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 2) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 2)) := (evo_oeis_a288599 2).1
      have a2_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 3) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 2) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 2)) := (evo_oeis_a288599 2).2.1
      have a2_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 3) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 2)) := (evo_oeis_a288599 2).2.2.1
      have a2_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 3) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 2) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 2)) := (evo_oeis_a288599 2).2.2.2
      rw [wlen_oeis_a288599 3, rv]
      omega
    | k + 5, ih =>
      have i1 := ih (k + 1) (by omega)
      have i4 := ih (k + 4) (by omega)
      have rr : OMA.S_oeis_a288599.reference (k + 5) =
          (-1) * OMA.S_oeis_a288599.reference (k + 1) + (2) * OMA.S_oeis_a288599.reference (k + 4) := by
        rw [OMA.S_oeis_a288599.reference]
        ring
      rw [wlen_oeis_a288599 k] at i1
      rw [wlen_oeis_a288599 (k + 3)] at i4
      rw [wlen_oeis_a288599 (k + 4), rr, ← i1, ← i4]
      have a0_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 1)) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 k) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 k)) := (evo_oeis_a288599 k).1
      have a0_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 1)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 k) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 k)) := (evo_oeis_a288599 k).2.1
      have a0_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 1)) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 k)) := (evo_oeis_a288599 k).2.2.1
      have a0_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 1)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 k) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 k)) := (evo_oeis_a288599 k).2.2.2
      have a1_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 2)) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 1)) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 1))) := (evo_oeis_a288599 (k + 1)).1
      have a1_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 2)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 1)) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 1))) := (evo_oeis_a288599 (k + 1)).2.1
      have a1_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 2)) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 1))) := (evo_oeis_a288599 (k + 1)).2.2.1
      have a1_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 2)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 1)) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 1))) := (evo_oeis_a288599 (k + 1)).2.2.2
      have a2_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 3)) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 2)) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 2))) := (evo_oeis_a288599 (k + 2)).1
      have a2_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 3)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 2)) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 2))) := (evo_oeis_a288599 (k + 2)).2.1
      have a2_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 3)) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 2))) := (evo_oeis_a288599 (k + 2)).2.2.1
      have a2_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 3)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 2)) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 2))) := (evo_oeis_a288599 (k + 2)).2.2.2
      have a3_0 : cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 4)) = 0 + (1 * cnt0_oeis_a288599 (blocks_oeis_a288599 (k + 3)) + 1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 3))) := (evo_oeis_a288599 (k + 3)).1
      have a3_1 : cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 4)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 3)) + 2 * cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 3))) := (evo_oeis_a288599 (k + 3)).2.1
      have a3_3 : cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 4)) = 0 + (1 * cnt1_oeis_a288599 (blocks_oeis_a288599 (k + 3))) := (evo_oeis_a288599 (k + 3)).2.2.1
      have a3_4 : cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 4)) = 0 + (1 * cnt3_oeis_a288599 (blocks_oeis_a288599 (k + 3)) + 1 * cnt4_oeis_a288599 (blocks_oeis_a288599 (k + 3))) := (evo_oeis_a288599 (k + 3)).2.2.2
      push_cast
      omega
