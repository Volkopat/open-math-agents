import OMAStatements.S_oeis_a288478
import Mathlib

-- From word 1 on, every word is the prefix [false] followed by blocks T F^k (k in [0, 1, 2]), and the
-- rewriting acts on the blocks as a substitution: TF^0 -> TF^0 TF^1; TF^1 -> TF^0 TF^2; TF^2 -> TF^0 TF^2 TF^1 TF^0.
inductive Blk_oeis_a288478 where
  | k0 : Blk_oeis_a288478
  | k1 : Blk_oeis_a288478
  | k2 : Blk_oeis_a288478

def render_oeis_a288478 : List Blk_oeis_a288478 → List Bool
  | [] => []
  | Blk_oeis_a288478.k0 :: r => true :: render_oeis_a288478 r
  | Blk_oeis_a288478.k1 :: r => true :: false :: render_oeis_a288478 r
  | Blk_oeis_a288478.k2 :: r => true :: false :: false :: render_oeis_a288478 r

def phi_oeis_a288478 : Blk_oeis_a288478 → List Blk_oeis_a288478
  | Blk_oeis_a288478.k0 => [Blk_oeis_a288478.k0, Blk_oeis_a288478.k1]
  | Blk_oeis_a288478.k1 => [Blk_oeis_a288478.k0, Blk_oeis_a288478.k2]
  | Blk_oeis_a288478.k2 => [Blk_oeis_a288478.k0, Blk_oeis_a288478.k2, Blk_oeis_a288478.k1, Blk_oeis_a288478.k0]

theorem w0_oeis_a288478 : OMA.S_oeis_a288478.rewriteWord [] = [] := by
  first | rfl | simp [OMA.S_oeis_a288478.rewriteWord] | (rw [OMA.S_oeis_a288478.rewriteWord]; rfl)

theorem wF1_oeis_a288478 : OMA.S_oeis_a288478.rewriteWord [false] = [false] := by
  first | rfl | simp [OMA.S_oeis_a288478.rewriteWord] | (rw [OMA.S_oeis_a288478.rewriteWord]; rfl)

theorem wT_oeis_a288478 (w : List Bool) : OMA.S_oeis_a288478.rewriteWord (true :: w) = [true, true, false] ++ OMA.S_oeis_a288478.rewriteWord w := by
  first | rfl | simp [OMA.S_oeis_a288478.rewriteWord] | (rw [OMA.S_oeis_a288478.rewriteWord]; rfl)

theorem wFF_oeis_a288478 (w : List Bool) : OMA.S_oeis_a288478.rewriteWord (false :: false :: w) = [false, true, false, true] ++ OMA.S_oeis_a288478.rewriteWord w := by
  first | rfl | simp [OMA.S_oeis_a288478.rewriteWord] | (rw [OMA.S_oeis_a288478.rewriteWord]; rfl)

theorem wFT0_oeis_a288478 (w : List Bool) : OMA.S_oeis_a288478.rewriteWord (false :: true :: w) = false :: ([true, true, false] ++ OMA.S_oeis_a288478.rewriteWord w) := by
  first | rfl | simp [OMA.S_oeis_a288478.rewriteWord] | (rw [OMA.S_oeis_a288478.rewriteWord]; rfl)

theorem wFT_oeis_a288478 (w : List Bool) : OMA.S_oeis_a288478.rewriteWord (false :: true :: w) = false :: OMA.S_oeis_a288478.rewriteWord (true :: w) := by
  rw [wFT0_oeis_a288478, wT_oeis_a288478]

theorem head_oeis_a288478 (y : Blk_oeis_a288478) (s : List Blk_oeis_a288478) : ∃ w, render_oeis_a288478 (y :: s) = true :: w := by
  cases y <;> exact ⟨_, rfl⟩

-- Rewriting a concatenation of blocks applies the substitution block by block.
theorem rw_oeis_a288478 (bs : List Blk_oeis_a288478) :
    OMA.S_oeis_a288478.rewriteWord (render_oeis_a288478 bs) = render_oeis_a288478 (bs.flatMap phi_oeis_a288478) := by
  induction bs with
  | nil => exact w0_oeis_a288478
  | cons x r ih =>
    cases x with
    | k0 =>
      have e1 : render_oeis_a288478 (Blk_oeis_a288478.k0 :: r) = true :: render_oeis_a288478 r := rfl
      have e2 : (Blk_oeis_a288478.k0 :: r).flatMap phi_oeis_a288478 = Blk_oeis_a288478.k0 :: Blk_oeis_a288478.k1 :: r.flatMap phi_oeis_a288478 := rfl
      rw [e1, wT_oeis_a288478, ih, e2]
      all_goals rfl
    | k1 =>
      cases r with
      | nil =>
        show OMA.S_oeis_a288478.rewriteWord [true, false] = [true, true, false, false]
        rw [wT_oeis_a288478, wF1_oeis_a288478]
        all_goals rfl
      | cons y r' =>
        obtain ⟨w, hw⟩ := head_oeis_a288478 y r'
        have e1 : render_oeis_a288478 (Blk_oeis_a288478.k1 :: y :: r') = true :: false :: true :: w := by
          show true :: false :: render_oeis_a288478 (y :: r') = _
          rw [hw]
        have e2 : (Blk_oeis_a288478.k1 :: y :: r').flatMap phi_oeis_a288478 = Blk_oeis_a288478.k0 :: Blk_oeis_a288478.k2 :: (y :: r').flatMap phi_oeis_a288478 := rfl
        rw [e1, wT_oeis_a288478, wFT_oeis_a288478, ← hw, ih, e2]
        all_goals rfl
    | k2 =>
      have e1 : render_oeis_a288478 (Blk_oeis_a288478.k2 :: r) = true :: false :: false :: render_oeis_a288478 r := rfl
      have e2 : (Blk_oeis_a288478.k2 :: r).flatMap phi_oeis_a288478 = Blk_oeis_a288478.k0 :: Blk_oeis_a288478.k2 :: Blk_oeis_a288478.k1 :: Blk_oeis_a288478.k0 :: r.flatMap phi_oeis_a288478 := rfl
      rw [e1, wT_oeis_a288478, wFF_oeis_a288478, ih, e2]
      all_goals rfl

theorem rwP_oeis_a288478 (bs : List Blk_oeis_a288478) :
    OMA.S_oeis_a288478.rewriteWord (false :: render_oeis_a288478 bs) = false :: render_oeis_a288478 (bs.flatMap phi_oeis_a288478) := by
  cases bs with
  | nil =>
    show OMA.S_oeis_a288478.rewriteWord [false] = [false]
    rw [wF1_oeis_a288478]
    all_goals rfl
  | cons y s =>
    obtain ⟨w, hw⟩ := head_oeis_a288478 y s
    rw [hw, wFT_oeis_a288478, ← hw, rw_oeis_a288478]
    all_goals rfl

-- Number of blocks of each kind.
def cnt0_oeis_a288478 : List Blk_oeis_a288478 → ℕ
  | [] => 0
  | Blk_oeis_a288478.k0 :: r => 1 + cnt0_oeis_a288478 r
  | Blk_oeis_a288478.k1 :: r => cnt0_oeis_a288478 r
  | Blk_oeis_a288478.k2 :: r => cnt0_oeis_a288478 r

def cnt1_oeis_a288478 : List Blk_oeis_a288478 → ℕ
  | [] => 0
  | Blk_oeis_a288478.k0 :: r => cnt1_oeis_a288478 r
  | Blk_oeis_a288478.k1 :: r => 1 + cnt1_oeis_a288478 r
  | Blk_oeis_a288478.k2 :: r => cnt1_oeis_a288478 r

def cnt2_oeis_a288478 : List Blk_oeis_a288478 → ℕ
  | [] => 0
  | Blk_oeis_a288478.k0 :: r => cnt2_oeis_a288478 r
  | Blk_oeis_a288478.k1 :: r => cnt2_oeis_a288478 r
  | Blk_oeis_a288478.k2 :: r => 1 + cnt2_oeis_a288478 r

theorem len_oeis_a288478 (bs : List Blk_oeis_a288478) :
    (render_oeis_a288478 bs).length = 1 * cnt0_oeis_a288478 bs + 2 * cnt1_oeis_a288478 bs + 3 * cnt2_oeis_a288478 bs := by
  induction bs with
  | nil => rfl
  | cons x r ih =>
    cases x with
    | k0 =>
      show (render_oeis_a288478 r).length + 1 = 1 * (1 + cnt0_oeis_a288478 r) + 2 * (cnt1_oeis_a288478 r) + 3 * (cnt2_oeis_a288478 r)
      omega
    | k1 =>
      show (render_oeis_a288478 r).length + 1 + 1 = 1 * (cnt0_oeis_a288478 r) + 2 * (1 + cnt1_oeis_a288478 r) + 3 * (cnt2_oeis_a288478 r)
      omega
    | k2 =>
      show (render_oeis_a288478 r).length + 1 + 1 + 1 = 1 * (cnt0_oeis_a288478 r) + 2 * (cnt1_oeis_a288478 r) + 3 * (1 + cnt2_oeis_a288478 r)
      omega

theorem step_oeis_a288478 (bs : List Blk_oeis_a288478) :
    cnt0_oeis_a288478 (bs.flatMap phi_oeis_a288478) = 1 * cnt0_oeis_a288478 bs + 1 * cnt1_oeis_a288478 bs + 2 * cnt2_oeis_a288478 bs ∧
    cnt1_oeis_a288478 (bs.flatMap phi_oeis_a288478) = 1 * cnt0_oeis_a288478 bs + 1 * cnt2_oeis_a288478 bs ∧
    cnt2_oeis_a288478 (bs.flatMap phi_oeis_a288478) = 1 * cnt1_oeis_a288478 bs + 1 * cnt2_oeis_a288478 bs := by
  induction bs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x r ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    cases x with
    | k0 =>
      refine ⟨?_, ?_, ?_⟩
      · show 1 + cnt0_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (1 + cnt0_oeis_a288478 r) + 1 * (cnt1_oeis_a288478 r) + 2 * (cnt2_oeis_a288478 r)
        omega
      · show 1 + cnt1_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (1 + cnt0_oeis_a288478 r) + 1 * (cnt2_oeis_a288478 r)
        omega
      · show cnt2_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (cnt1_oeis_a288478 r) + 1 * (cnt2_oeis_a288478 r)
        omega
    | k1 =>
      refine ⟨?_, ?_, ?_⟩
      · show 1 + cnt0_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (cnt0_oeis_a288478 r) + 1 * (1 + cnt1_oeis_a288478 r) + 2 * (cnt2_oeis_a288478 r)
        omega
      · show cnt1_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (cnt0_oeis_a288478 r) + 1 * (cnt2_oeis_a288478 r)
        omega
      · show 1 + cnt2_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (1 + cnt1_oeis_a288478 r) + 1 * (cnt2_oeis_a288478 r)
        omega
    | k2 =>
      refine ⟨?_, ?_, ?_⟩
      · show 1 + (1 + cnt0_oeis_a288478 (r.flatMap phi_oeis_a288478)) = 1 * (cnt0_oeis_a288478 r) + 1 * (cnt1_oeis_a288478 r) + 2 * (1 + cnt2_oeis_a288478 r)
        omega
      · show 1 + cnt1_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (cnt0_oeis_a288478 r) + 1 * (1 + cnt2_oeis_a288478 r)
        omega
      · show 1 + cnt2_oeis_a288478 (r.flatMap phi_oeis_a288478) = 1 * (cnt1_oeis_a288478 r) + 1 * (1 + cnt2_oeis_a288478 r)
        omega

def blocks_oeis_a288478 : ℕ → List Blk_oeis_a288478
  | 0 => [Blk_oeis_a288478.k1, Blk_oeis_a288478.k0]
  | n + 1 => (blocks_oeis_a288478 n).flatMap phi_oeis_a288478

theorem word_oeis_a288478 (n : ℕ) :
    OMA.S_oeis_a288478.word (n + 1) = false :: render_oeis_a288478 (blocks_oeis_a288478 n) := by
  induction n with
  | zero =>
    show OMA.S_oeis_a288478.rewriteWord [false, false] = [false, true, false, true]
    rw [wFF_oeis_a288478, w0_oeis_a288478]
    all_goals rfl
  | succ n ih =>
    have e : OMA.S_oeis_a288478.word (n + 1 + 1) =
        OMA.S_oeis_a288478.rewriteWord (OMA.S_oeis_a288478.word (n + 1)) :=
      Function.iterate_succ_apply' _ _ _
    rw [e]
    rw [ih, rwP_oeis_a288478]
    all_goals rfl

theorem wlen_oeis_a288478 (n : ℕ) :
    (OMA.S_oeis_a288478.word (n + 1)).length = 1 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 n) + 2 * cnt1_oeis_a288478 (blocks_oeis_a288478 n) + 3 * cnt2_oeis_a288478 (blocks_oeis_a288478 n)) := by
  rw [word_oeis_a288478]
  simp only [List.length_cons]
  rw [len_oeis_a288478]
  omega

theorem evo_oeis_a288478 (n : ℕ) :
    cnt0_oeis_a288478 (blocks_oeis_a288478 (n + 1)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 n) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 n) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 n)) ∧
    cnt1_oeis_a288478 (blocks_oeis_a288478 (n + 1)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 n) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 n)) ∧
    cnt2_oeis_a288478 (blocks_oeis_a288478 (n + 1)) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 n) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 n)) := by
  obtain ⟨h0, h1, h2⟩ := step_oeis_a288478 (blocks_oeis_a288478 n)
  refine ⟨?_, ?_, ?_⟩
  · show cnt0_oeis_a288478 ((blocks_oeis_a288478 n).flatMap phi_oeis_a288478) = _
    omega
  · show cnt1_oeis_a288478 ((blocks_oeis_a288478 n).flatMap phi_oeis_a288478) = _
    omega
  · show cnt2_oeis_a288478 ((blocks_oeis_a288478 n).flatMap phi_oeis_a288478) = _
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a288478.main := by
  have c0_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 0) = 1 := rfl
  have c0_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 0) = 1 := rfl
  have c0_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 0) = 0 := rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ =>
      have rv : OMA.S_oeis_a288478.a 1 = 4 := rfl
      rw [wlen_oeis_a288478 0, rv]
      omega
    | 2, _ =>
      have rv : OMA.S_oeis_a288478.a 2 = 8 := rfl
      have a0_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 1) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 0) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 0) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 0)) := (evo_oeis_a288478 0).1
      have a0_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 1) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 0) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 0)) := (evo_oeis_a288478 0).2.1
      have a0_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 1) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 0) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 0)) := (evo_oeis_a288478 0).2.2
      rw [wlen_oeis_a288478 1, rv]
      omega
    | 3, _ =>
      have rv : OMA.S_oeis_a288478.a 3 = 18 := rfl
      have a0_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 1) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 0) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 0) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 0)) := (evo_oeis_a288478 0).1
      have a0_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 1) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 0) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 0)) := (evo_oeis_a288478 0).2.1
      have a0_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 1) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 0) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 0)) := (evo_oeis_a288478 0).2.2
      have a1_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 2) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 1) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 1) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 1)) := (evo_oeis_a288478 1).1
      have a1_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 2) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 1) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 1)) := (evo_oeis_a288478 1).2.1
      have a1_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 2) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 1) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 1)) := (evo_oeis_a288478 1).2.2
      rw [wlen_oeis_a288478 2, rv]
      omega
    | k + 4, ih =>
      have i0 := ih (k + 1) (by omega)
      have i1 := ih (k + 2) (by omega)
      have i2 := ih (k + 3) (by omega)
      have rr : OMA.S_oeis_a288478.a (k + 4) =
          (-1) * OMA.S_oeis_a288478.a (k + 1) + (-1) * OMA.S_oeis_a288478.a (k + 2) + (3) * OMA.S_oeis_a288478.a (k + 3) := by
        rw [OMA.S_oeis_a288478.a]
        ring
      rw [wlen_oeis_a288478 k] at i0
      rw [wlen_oeis_a288478 (k + 1)] at i1
      rw [wlen_oeis_a288478 (k + 2)] at i2
      rw [wlen_oeis_a288478 (k + 3), rr, ← i0, ← i1, ← i2]
      have a0_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 1)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 k) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 k) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 k)) := (evo_oeis_a288478 k).1
      have a0_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 1)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 k) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 k)) := (evo_oeis_a288478 k).2.1
      have a0_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 1)) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 k) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 k)) := (evo_oeis_a288478 k).2.2
      have a1_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 2)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 1)) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 1)) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 1))) := (evo_oeis_a288478 (k + 1)).1
      have a1_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 2)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 1)) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 1))) := (evo_oeis_a288478 (k + 1)).2.1
      have a1_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 2)) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 1)) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 1))) := (evo_oeis_a288478 (k + 1)).2.2
      have a2_0 : cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 3)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 2)) + 1 * cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 2)) + 2 * cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 2))) := (evo_oeis_a288478 (k + 2)).1
      have a2_1 : cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 3)) = 0 + (1 * cnt0_oeis_a288478 (blocks_oeis_a288478 (k + 2)) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 2))) := (evo_oeis_a288478 (k + 2)).2.1
      have a2_2 : cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 3)) = 0 + (1 * cnt1_oeis_a288478 (blocks_oeis_a288478 (k + 2)) + 1 * cnt2_oeis_a288478 (blocks_oeis_a288478 (k + 2))) := (evo_oeis_a288478 (k + 2)).2.2
      push_cast
      omega
