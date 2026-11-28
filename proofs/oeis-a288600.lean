import OMAStatements.S_oeis_a288600
import Mathlib

-- After the first step every word is `false` followed by blocks T, TF, TFF, and the rewriting
-- acts on these blocks as a substitution:  T -> T,  TF -> TFF T,  TFF -> TFF TF.
inductive OeisA288600Blk where
  | c : OeisA288600Blk
  | b : OeisA288600Blk
  | d : OeisA288600Blk

def oeis_a288600_render : List OeisA288600Blk → List Bool
  | [] => []
  | OeisA288600Blk.c :: r => true :: oeis_a288600_render r
  | OeisA288600Blk.b :: r => true :: false :: oeis_a288600_render r
  | OeisA288600Blk.d :: r => true :: false :: false :: oeis_a288600_render r

def oeis_a288600_phi : OeisA288600Blk → List OeisA288600Blk
  | OeisA288600Blk.c => [OeisA288600Blk.c]
  | OeisA288600Blk.b => [OeisA288600Blk.d, OeisA288600Blk.c]
  | OeisA288600Blk.d => [OeisA288600Blk.d, OeisA288600Blk.b]

theorem oeis_a288600_w0 : OMA.S_oeis_a288600.rewrite [] = [] := by
  first | rw [OMA.S_oeis_a288600.rewrite] | simp [OMA.S_oeis_a288600.rewrite]

theorem oeis_a288600_w1 (x : Bool) : OMA.S_oeis_a288600.rewrite [x] = [x] := by
  first | rw [OMA.S_oeis_a288600.rewrite] | simp [OMA.S_oeis_a288600.rewrite]

theorem oeis_a288600_w2 (w : List Bool) : OMA.S_oeis_a288600.rewrite (false :: false :: w) =
    [false, true, false, true] ++ OMA.S_oeis_a288600.rewrite w := by
  first | rw [OMA.S_oeis_a288600.rewrite] | simp [OMA.S_oeis_a288600.rewrite]

theorem oeis_a288600_w3 (w : List Bool) : OMA.S_oeis_a288600.rewrite (true :: false :: w) =
    [true, false, false, true] ++ OMA.S_oeis_a288600.rewrite w := by
  first | rw [OMA.S_oeis_a288600.rewrite] | simp [OMA.S_oeis_a288600.rewrite]

theorem oeis_a288600_w4 (w : List Bool) : OMA.S_oeis_a288600.rewrite (false :: true :: w) =
    false :: OMA.S_oeis_a288600.rewrite (true :: w) := by
  first | rw [OMA.S_oeis_a288600.rewrite] | simp [OMA.S_oeis_a288600.rewrite]

theorem oeis_a288600_w5 (w : List Bool) : OMA.S_oeis_a288600.rewrite (true :: true :: w) =
    true :: OMA.S_oeis_a288600.rewrite (true :: w) := by
  first | rw [OMA.S_oeis_a288600.rewrite] | simp [OMA.S_oeis_a288600.rewrite]

theorem oeis_a288600_head (y : OeisA288600Blk) (s : List OeisA288600Blk) :
    ∃ w, oeis_a288600_render (y :: s) = true :: w := by
  cases y <;> exact ⟨_, rfl⟩

-- Rewriting a concatenation of blocks applies the substitution block by block.
theorem oeis_a288600_rw (bs : List OeisA288600Blk) :
    OMA.S_oeis_a288600.rewrite (oeis_a288600_render bs) =
      oeis_a288600_render (bs.flatMap oeis_a288600_phi) := by
  induction bs with
  | nil => exact oeis_a288600_w0
  | cons x r ih =>
    cases x with
    | c =>
      cases r with
      | nil => exact oeis_a288600_w1 true
      | cons y r' =>
        obtain ⟨w, hw⟩ := oeis_a288600_head y r'
        have e1 : oeis_a288600_render (OeisA288600Blk.c :: y :: r') = true :: true :: w := by
          show true :: oeis_a288600_render (y :: r') = _
          rw [hw]
        have e2 : (OeisA288600Blk.c :: y :: r').flatMap oeis_a288600_phi =
            OeisA288600Blk.c :: (y :: r').flatMap oeis_a288600_phi := rfl
        rw [e1, oeis_a288600_w5, ← hw, ih, e2]
        rfl
    | b =>
      have e1 : oeis_a288600_render (OeisA288600Blk.b :: r) =
          true :: false :: oeis_a288600_render r := rfl
      have e2 : (OeisA288600Blk.b :: r).flatMap oeis_a288600_phi =
          OeisA288600Blk.d :: OeisA288600Blk.c :: r.flatMap oeis_a288600_phi := rfl
      rw [e1, oeis_a288600_w3, ih, e2]
      rfl
    | d =>
      cases r with
      | nil =>
        show OMA.S_oeis_a288600.rewrite [true, false, false] = [true, false, false, true, false]
        rw [oeis_a288600_w3, oeis_a288600_w1]
        rfl
      | cons y r' =>
        obtain ⟨w, hw⟩ := oeis_a288600_head y r'
        have e1 : oeis_a288600_render (OeisA288600Blk.d :: y :: r') =
            true :: false :: false :: true :: w := by
          show true :: false :: false :: oeis_a288600_render (y :: r') = _
          rw [hw]
        have e2 : (OeisA288600Blk.d :: y :: r').flatMap oeis_a288600_phi =
            OeisA288600Blk.d :: OeisA288600Blk.b :: (y :: r').flatMap oeis_a288600_phi := rfl
        rw [e1, oeis_a288600_w3, oeis_a288600_w4, ← hw, ih, e2]
        rfl

theorem oeis_a288600_rwF (bs : List OeisA288600Blk) :
    OMA.S_oeis_a288600.rewrite (false :: oeis_a288600_render bs) =
      false :: oeis_a288600_render (bs.flatMap oeis_a288600_phi) := by
  cases bs with
  | nil => exact oeis_a288600_w1 false
  | cons y s =>
    obtain ⟨w, hw⟩ := oeis_a288600_head y s
    rw [hw, oeis_a288600_w4, ← hw, oeis_a288600_rw]

-- Length of the rendered word, number of blocks TF or TFF, number of blocks TFF.
def oeis_a288600_len : List OeisA288600Blk → ℕ
  | [] => 0
  | OeisA288600Blk.c :: r => 1 + oeis_a288600_len r
  | OeisA288600Blk.b :: r => 2 + oeis_a288600_len r
  | OeisA288600Blk.d :: r => 3 + oeis_a288600_len r

def oeis_a288600_t : List OeisA288600Blk → ℕ
  | [] => 0
  | OeisA288600Blk.c :: r => oeis_a288600_t r
  | OeisA288600Blk.b :: r => 1 + oeis_a288600_t r
  | OeisA288600Blk.d :: r => 1 + oeis_a288600_t r

def oeis_a288600_dd : List OeisA288600Blk → ℕ
  | [] => 0
  | OeisA288600Blk.c :: r => oeis_a288600_dd r
  | OeisA288600Blk.b :: r => oeis_a288600_dd r
  | OeisA288600Blk.d :: r => 1 + oeis_a288600_dd r

theorem oeis_a288600_len_render (bs : List OeisA288600Blk) :
    (oeis_a288600_render bs).length = oeis_a288600_len bs := by
  induction bs with
  | nil => rfl
  | cons x r ih =>
    cases x with
    | c =>
      show (oeis_a288600_render r).length + 1 = 1 + oeis_a288600_len r
      omega
    | b =>
      show (oeis_a288600_render r).length + 1 + 1 = 2 + oeis_a288600_len r
      omega
    | d =>
      show (oeis_a288600_render r).length + 1 + 1 + 1 = 3 + oeis_a288600_len r
      omega

theorem oeis_a288600_step (bs : List OeisA288600Blk) :
    oeis_a288600_len (bs.flatMap oeis_a288600_phi) = oeis_a288600_len bs + 2 * oeis_a288600_t bs ∧
    oeis_a288600_t (bs.flatMap oeis_a288600_phi) = oeis_a288600_t bs + oeis_a288600_dd bs ∧
    oeis_a288600_dd (bs.flatMap oeis_a288600_phi) = oeis_a288600_t bs := by
  induction bs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    cases x with
    | c =>
      refine ⟨?_, ?_, ?_⟩
      · show 1 + oeis_a288600_len (r.flatMap oeis_a288600_phi) =
          1 + oeis_a288600_len r + 2 * oeis_a288600_t r
        omega
      · show oeis_a288600_t (r.flatMap oeis_a288600_phi) = oeis_a288600_t r + oeis_a288600_dd r
        omega
      · show oeis_a288600_dd (r.flatMap oeis_a288600_phi) = oeis_a288600_t r
        omega
    | b =>
      refine ⟨?_, ?_, ?_⟩
      · show 3 + (1 + oeis_a288600_len (r.flatMap oeis_a288600_phi)) =
          2 + oeis_a288600_len r + 2 * (1 + oeis_a288600_t r)
        omega
      · show 1 + oeis_a288600_t (r.flatMap oeis_a288600_phi) =
          1 + oeis_a288600_t r + oeis_a288600_dd r
        omega
      · show 1 + oeis_a288600_dd (r.flatMap oeis_a288600_phi) = 1 + oeis_a288600_t r
        omega
    | d =>
      refine ⟨?_, ?_, ?_⟩
      · show 3 + (2 + oeis_a288600_len (r.flatMap oeis_a288600_phi)) =
          3 + oeis_a288600_len r + 2 * (1 + oeis_a288600_t r)
        omega
      · show 1 + (1 + oeis_a288600_t (r.flatMap oeis_a288600_phi)) =
          1 + oeis_a288600_t r + (1 + oeis_a288600_dd r)
        omega
      · show 1 + oeis_a288600_dd (r.flatMap oeis_a288600_phi) = 1 + oeis_a288600_t r
        omega

def oeis_a288600_blocks : ℕ → List OeisA288600Blk
  | 0 => [OeisA288600Blk.b, OeisA288600Blk.c]
  | n + 1 => (oeis_a288600_blocks n).flatMap oeis_a288600_phi

theorem oeis_a288600_word (n : ℕ) :
    OMA.S_oeis_a288600.word (n + 1) = false :: oeis_a288600_render (oeis_a288600_blocks n) := by
  induction n with
  | zero =>
    show OMA.S_oeis_a288600.rewrite [false, false] = [false, true, false, true]
    rw [oeis_a288600_w2, oeis_a288600_w0]
    rfl
  | succ n ih =>
    show OMA.S_oeis_a288600.rewrite (OMA.S_oeis_a288600.word (n + 1)) = _
    rw [ih, oeis_a288600_rwF]
    rfl

theorem oeis_a288600_wlen (n : ℕ) :
    (OMA.S_oeis_a288600.word (n + 1)).length = 1 + oeis_a288600_len (oeis_a288600_blocks n) := by
  rw [oeis_a288600_word, List.length_cons, oeis_a288600_len_render]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a288600.main := by
  have hL : ∀ n, oeis_a288600_len (oeis_a288600_blocks (n + 1)) =
      oeis_a288600_len (oeis_a288600_blocks n) + 2 * oeis_a288600_t (oeis_a288600_blocks n) :=
    fun n => (oeis_a288600_step (oeis_a288600_blocks n)).1
  have hT : ∀ n, oeis_a288600_t (oeis_a288600_blocks (n + 1)) =
      oeis_a288600_t (oeis_a288600_blocks n) + oeis_a288600_dd (oeis_a288600_blocks n) :=
    fun n => (oeis_a288600_step (oeis_a288600_blocks n)).2.1
  have hD : ∀ n, oeis_a288600_dd (oeis_a288600_blocks (n + 1)) =
      oeis_a288600_t (oeis_a288600_blocks n) :=
    fun n => (oeis_a288600_step (oeis_a288600_blocks n)).2.2
  have L0 : oeis_a288600_len (oeis_a288600_blocks 0) = 3 := rfl
  have T0 : oeis_a288600_t (oeis_a288600_blocks 0) = 1 := rfl
  have D0 : oeis_a288600_dd (oeis_a288600_blocks 0) = 0 := rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ =>
      have r1 : OMA.S_oeis_a288600.reference 1 = 4 := rfl
      rw [oeis_a288600_wlen 0, r1]
      omega
    | 2, _ =>
      have r2 : OMA.S_oeis_a288600.reference 2 = 6 := rfl
      have a1 : oeis_a288600_len (oeis_a288600_blocks 1) = oeis_a288600_len (oeis_a288600_blocks 0) + 2 * oeis_a288600_t (oeis_a288600_blocks 0) := hL 0
      rw [oeis_a288600_wlen 1, r2]
      omega
    | 3, _ =>
      have r3 : OMA.S_oeis_a288600.reference 3 = 8 := rfl
      have a1 : oeis_a288600_len (oeis_a288600_blocks 1) = oeis_a288600_len (oeis_a288600_blocks 0) + 2 * oeis_a288600_t (oeis_a288600_blocks 0) := hL 0
      have a2 : oeis_a288600_len (oeis_a288600_blocks 2) = oeis_a288600_len (oeis_a288600_blocks 1) + 2 * oeis_a288600_t (oeis_a288600_blocks 1) := hL 1
      have a3 : oeis_a288600_t (oeis_a288600_blocks 1) = oeis_a288600_t (oeis_a288600_blocks 0) + oeis_a288600_dd (oeis_a288600_blocks 0) := hT 0
      rw [oeis_a288600_wlen 2, r3]
      omega
    | k + 4, ih =>
      have i3 := ih (k + 3) (by omega)
      have i1 := ih (k + 1) (by omega)
      have rr : OMA.S_oeis_a288600.reference (k + 4) =
          2 * OMA.S_oeis_a288600.reference (k + 3) - OMA.S_oeis_a288600.reference (k + 1) := rfl
      rw [oeis_a288600_wlen (k + 2)] at i3
      rw [oeis_a288600_wlen k] at i1
      rw [oeis_a288600_wlen (k + 3), rr, ← i3, ← i1]
      have a1 : oeis_a288600_len (oeis_a288600_blocks (k + 3)) = oeis_a288600_len (oeis_a288600_blocks (k + 2)) + 2 * oeis_a288600_t (oeis_a288600_blocks (k + 2)) := hL (k + 2)
      have a2 : oeis_a288600_len (oeis_a288600_blocks (k + 2)) = oeis_a288600_len (oeis_a288600_blocks (k + 1)) + 2 * oeis_a288600_t (oeis_a288600_blocks (k + 1)) := hL (k + 1)
      have a3 : oeis_a288600_len (oeis_a288600_blocks (k + 1)) = oeis_a288600_len (oeis_a288600_blocks k) + 2 * oeis_a288600_t (oeis_a288600_blocks k) := hL k
      have a4 : oeis_a288600_t (oeis_a288600_blocks (k + 2)) = oeis_a288600_t (oeis_a288600_blocks (k + 1)) + oeis_a288600_dd (oeis_a288600_blocks (k + 1)) := hT (k + 1)
      have a5 : oeis_a288600_dd (oeis_a288600_blocks (k + 1)) = oeis_a288600_t (oeis_a288600_blocks k) := hD k
      omega
