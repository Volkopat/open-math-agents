import OMAStatements.S_oeis_a288694

-- Problem: A288694: Fixed point of the mapping 00->0110, 10->100, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288694.lean:0 (declaration OMA.S_oeis_a288694.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: use the blocks K = 00110, V = 0110, Y = 110. The mapping acts on each block whatever
-- follows it (00110 -> 0110 1100, 0110 -> 0 1 100, 110 -> 1 100), and each image ends with a 0
-- that joins the next image. Carrying that 0 to the right gives
-- 0 + step(flat ts ++ T) = flat(sig ts) ++ (0 + step T) with sig: K -> K Y, V -> K, Y -> V. For
-- n >= 1 the iterate is flat(V :: ts) followed by an end T that cycles through [], 0, 00; from
-- the end 00 the carried 0 makes 000110 = 0 + 00110, one more block K. With block counts (k, v, y)
-- and end length e the length is 4 + 5k + 4v + 3y + e, and four steps give
-- L(n+4) = 2L(n+3) - L(n+2) + L(n+1) - L(n) in each of the three phases, the recurrence of
-- A288429, with the same values 2, 4, 5, 6 (the case n = 0 by evaluation).

namespace FS2A288694

open OMA.S_oeis_a288694

inductive Tok
  | K
  | V
  | Y

/-- Blocks to letters: K is 00110, V is 0110, Y is 110. -/
def flat : List Tok → List Bool
  | [] => []
  | Tok.K :: ts => false :: false :: true :: true :: false :: flat ts
  | Tok.V :: ts => false :: true :: true :: false :: flat ts
  | Tok.Y :: ts => true :: true :: false :: flat ts

/-- The mapping on blocks, after carrying the final 0 of each image: K -> K Y, V -> K, Y -> V. -/
def sig : List Tok → List Tok
  | [] => []
  | Tok.K :: ts => Tok.K :: Tok.Y :: sig ts
  | Tok.V :: ts => Tok.K :: sig ts
  | Tok.Y :: ts => Tok.V :: sig ts

def cK : List Tok → ℕ
  | [] => 0
  | Tok.K :: ts => cK ts + 1
  | Tok.V :: ts => cK ts
  | Tok.Y :: ts => cK ts

def cV : List Tok → ℕ
  | [] => 0
  | Tok.K :: ts => cV ts
  | Tok.V :: ts => cV ts + 1
  | Tok.Y :: ts => cV ts

def cY : List Tok → ℕ
  | [] => 0
  | Tok.K :: ts => cY ts
  | Tok.V :: ts => cY ts
  | Tok.Y :: ts => cY ts + 1

theorem s00 (r : List Bool) :
    step (false :: false :: r) = false :: true :: true :: false :: step r := rfl

theorem s10 (r : List Bool) : step (true :: false :: r) = true :: false :: false :: step r := rfl

theorem s11 (r : List Bool) : step (true :: true :: r) = true :: step (true :: r) := rfl

theorem s01 (r : List Bool) : step (false :: true :: r) = false :: step (true :: r) := rfl

theorem G (ts : List Tok) (T : List Bool) :
    false :: step (flat ts ++ T) = flat (sig ts) ++ (false :: step T) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | K =>
      show false :: step (false :: false :: true :: true :: false :: (flat ts ++ T)) =
        false :: false :: true :: true :: false :: true :: true :: false ::
          (flat (sig ts) ++ (false :: step T))
      rw [s00, s11, s10, ih]
    | V =>
      show false :: step (false :: true :: true :: false :: (flat ts ++ T)) =
        false :: false :: true :: true :: false :: (flat (sig ts) ++ (false :: step T))
      rw [s01, s11, s10, ih]
    | Y =>
      show false :: step (true :: true :: false :: (flat ts ++ T)) =
        false :: true :: true :: false :: (flat (sig ts) ++ (false :: step T))
      rw [s11, s10, ih]

theorem stepW (ts : List Tok) (T : List Bool) :
    step (flat (Tok.V :: ts) ++ T) = flat (Tok.V :: sig ts) ++ (false :: step T) := by
  show step (false :: true :: true :: false :: (flat ts ++ T)) =
    false :: true :: true :: false :: (flat (sig ts) ++ (false :: step T))
  rw [s01, s11, s10, G]

theorem flat_append (l1 l2 : List Tok) : flat (l1 ++ l2) = flat l1 ++ flat l2 := by
  induction l1 with
  | nil => rfl
  | cons t l ih =>
    cases t with
    | K =>
      show false :: false :: true :: true :: false :: flat (l ++ l2) =
        false :: false :: true :: true :: false :: (flat l ++ flat l2)
      rw [ih]
    | V =>
      show false :: true :: true :: false :: flat (l ++ l2) =
        false :: true :: true :: false :: (flat l ++ flat l2)
      rw [ih]
    | Y =>
      show true :: true :: false :: flat (l ++ l2) = true :: true :: false :: (flat l ++ flat l2)
      rw [ih]

theorem st0 (ts : List Tok) : step (flat (Tok.V :: ts)) = flat (Tok.V :: sig ts) ++ [false] := by
  have h := stepW ts []
  rw [List.append_nil] at h
  exact h

theorem st1 (ts : List Tok) :
    step (flat (Tok.V :: ts) ++ [false]) = flat (Tok.V :: sig ts) ++ [false, false] :=
  stepW ts [false]

theorem st2 (ts : List Tok) :
    step (flat (Tok.V :: ts) ++ [false, false]) = flat (Tok.V :: (sig ts ++ [Tok.K])) := by
  have h := stepW ts [false, false]
  have e : flat (Tok.V :: (sig ts ++ [Tok.K])) = flat (Tok.V :: sig ts) ++ flat [Tok.K] :=
    flat_append (Tok.V :: sig ts) [Tok.K]
  rw [e]
  exact h

theorem w_rep : ∀ n : ℕ, ∃ ts : List Tok, w (n + 1) = flat (Tok.V :: ts) ∨
    w (n + 1) = flat (Tok.V :: ts) ++ [false] ∨ w (n + 1) = flat (Tok.V :: ts) ++ [false, false]
  | 0 => ⟨[], Or.inl rfl⟩
  | n + 1 => by
    obtain ⟨ts, h | h | h⟩ := w_rep n
    · refine ⟨sig ts, Or.inr (Or.inl ?_)⟩
      show step (w (n + 1)) = flat (Tok.V :: sig ts) ++ [false]
      rw [h, st0]
    · refine ⟨sig ts, Or.inr (Or.inr ?_)⟩
      show step (w (n + 1)) = flat (Tok.V :: sig ts) ++ [false, false]
      rw [h, st1]
    · refine ⟨sig ts ++ [Tok.K], Or.inl ?_⟩
      show step (w (n + 1)) = flat (Tok.V :: (sig ts ++ [Tok.K]))
      rw [h, st2]

theorem len_flat (ts : List Tok) : (flat ts).length = 5 * cK ts + 4 * cV ts + 3 * cY ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | K =>
      show (false :: false :: true :: true :: false :: flat ts).length =
        5 * (cK ts + 1) + 4 * cV ts + 3 * cY ts
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
        List.length_cons]
      omega
    | V =>
      show (false :: true :: true :: false :: flat ts).length =
        5 * cK ts + 4 * (cV ts + 1) + 3 * cY ts
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons]
      omega
    | Y =>
      show (true :: true :: false :: flat ts).length = 5 * cK ts + 4 * cV ts + 3 * (cY ts + 1)
      rw [List.length_cons, List.length_cons, List.length_cons]
      omega

theorem cK_sig (ts : List Tok) : cK (sig ts) = cK ts + cV ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | K =>
      show cK (sig ts) + 1 = cK ts + 1 + cV ts
      omega
    | V =>
      show cK (sig ts) + 1 = cK ts + (cV ts + 1)
      omega
    | Y =>
      show cK (sig ts) = cK ts + cV ts
      exact ih

theorem cV_sig (ts : List Tok) : cV (sig ts) = cY ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | K =>
      show cV (sig ts) = cY ts
      exact ih
    | V =>
      show cV (sig ts) = cY ts
      exact ih
    | Y =>
      show cV (sig ts) + 1 = cY ts + 1
      omega

theorem cY_sig (ts : List Tok) : cY (sig ts) = cK ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | K =>
      show cY (sig ts) + 1 = cK ts + 1
      omega
    | V =>
      show cY (sig ts) = cK ts
      exact ih
    | Y =>
      show cY (sig ts) = cK ts
      exact ih

theorem cK_append (l1 l2 : List Tok) : cK (l1 ++ l2) = cK l1 + cK l2 := by
  induction l1 with
  | nil =>
    show cK l2 = 0 + cK l2
    omega
  | cons t l ih =>
    cases t with
    | K =>
      show cK (l ++ l2) + 1 = cK l + 1 + cK l2
      omega
    | V =>
      show cK (l ++ l2) = cK l + cK l2
      exact ih
    | Y =>
      show cK (l ++ l2) = cK l + cK l2
      exact ih

theorem cV_append (l1 l2 : List Tok) : cV (l1 ++ l2) = cV l1 + cV l2 := by
  induction l1 with
  | nil =>
    show cV l2 = 0 + cV l2
    omega
  | cons t l ih =>
    cases t with
    | K =>
      show cV (l ++ l2) = cV l + cV l2
      exact ih
    | V =>
      show cV (l ++ l2) + 1 = cV l + 1 + cV l2
      omega
    | Y =>
      show cV (l ++ l2) = cV l + cV l2
      exact ih

theorem cY_append (l1 l2 : List Tok) : cY (l1 ++ l2) = cY l1 + cY l2 := by
  induction l1 with
  | nil =>
    show cY l2 = 0 + cY l2
    omega
  | cons t l ih =>
    cases t with
    | K =>
      show cY (l ++ l2) = cY l + cY l2
      exact ih
    | V =>
      show cY (l ++ l2) = cY l + cY l2
      exact ih
    | Y =>
      show cY (l ++ l2) + 1 = cY l + 1 + cY l2
      omega

theorem len_rec : ∀ n : ℕ, ((w (n + 4)).length : ℤ) =
    2 * ((w (n + 3)).length : ℤ) - ((w (n + 2)).length : ℤ) + ((w (n + 1)).length : ℤ) -
      ((w n).length : ℤ)
  | 0 => by decide
  | k + 1 => by
    obtain ⟨ts, h1 | h1 | h1⟩ := w_rep k
    · have h2 : w (k + 1 + 1) = flat (Tok.V :: sig ts) ++ [false] := by
        rw [show w (k + 1 + 1) = step (w (k + 1)) from rfl, h1, st0]
      have h3 : w (k + 1 + 2) = flat (Tok.V :: sig (sig ts)) ++ [false, false] := by
        rw [show w (k + 1 + 2) = step (w (k + 1 + 1)) from rfl, h2, st1]
      have h4 : w (k + 1 + 3) = flat (Tok.V :: (sig (sig (sig ts)) ++ [Tok.K])) := by
        rw [show w (k + 1 + 3) = step (w (k + 1 + 2)) from rfl, h3, st2]
      have h5 : w (k + 1 + 4) =
          flat (Tok.V :: sig (sig (sig (sig ts)) ++ [Tok.K])) ++ [false] := by
        rw [show w (k + 1 + 4) = step (w (k + 1 + 3)) from rfl, h4, st0]
      rw [h5, h4, h3, h2, h1]
      simp only [List.length_append, List.length_cons, List.length_nil, len_flat,
        cK_append, cV_append, cY_append, cK_sig, cV_sig, cY_sig, cK, cV, cY]
      push_cast
      ring
    · have h2 : w (k + 1 + 1) = flat (Tok.V :: sig ts) ++ [false, false] := by
        rw [show w (k + 1 + 1) = step (w (k + 1)) from rfl, h1, st1]
      have h3 : w (k + 1 + 2) = flat (Tok.V :: (sig (sig ts) ++ [Tok.K])) := by
        rw [show w (k + 1 + 2) = step (w (k + 1 + 1)) from rfl, h2, st2]
      have h4 : w (k + 1 + 3) = flat (Tok.V :: sig (sig (sig ts) ++ [Tok.K])) ++ [false] := by
        rw [show w (k + 1 + 3) = step (w (k + 1 + 2)) from rfl, h3, st0]
      have h5 : w (k + 1 + 4) =
          flat (Tok.V :: sig (sig (sig (sig ts) ++ [Tok.K]))) ++ [false, false] := by
        rw [show w (k + 1 + 4) = step (w (k + 1 + 3)) from rfl, h4, st1]
      rw [h5, h4, h3, h2, h1]
      simp only [List.length_append, List.length_cons, List.length_nil, len_flat,
        cK_append, cV_append, cY_append, cK_sig, cV_sig, cY_sig, cK, cV, cY]
      push_cast
      ring
    · have h2 : w (k + 1 + 1) = flat (Tok.V :: (sig ts ++ [Tok.K])) := by
        rw [show w (k + 1 + 1) = step (w (k + 1)) from rfl, h1, st2]
      have h3 : w (k + 1 + 2) = flat (Tok.V :: sig (sig ts ++ [Tok.K])) ++ [false] := by
        rw [show w (k + 1 + 2) = step (w (k + 1 + 1)) from rfl, h2, st0]
      have h4 : w (k + 1 + 3) =
          flat (Tok.V :: sig (sig (sig ts ++ [Tok.K]))) ++ [false, false] := by
        rw [show w (k + 1 + 3) = step (w (k + 1 + 2)) from rfl, h3, st1]
      have h5 : w (k + 1 + 4) =
          flat (Tok.V :: (sig (sig (sig (sig ts ++ [Tok.K]))) ++ [Tok.K])) := by
        rw [show w (k + 1 + 4) = step (w (k + 1 + 3)) from rfl, h4, st2]
      rw [h5, h4, h3, h2, h1]
      simp only [List.length_append, List.length_cons, List.length_nil, len_flat,
        cK_append, cV_append, cY_append, cK_sig, cV_sig, cY_sig, cK, cV, cY]
      push_cast
      ring

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A288429 n ∧ ((w (n + 1)).length : ℤ) = A288429 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A288429 (n + 2) ∧ ((w (n + 3)).length : ℤ) = A288429 (n + 3)
  | 0 => ⟨by decide, by decide, by decide, by decide⟩
  | n + 1 => by
    obtain ⟨h0, h1, h2, h3⟩ := len_eq n
    refine ⟨h1, h2, h3, ?_⟩
    show ((w (n + 4)).length : ℤ) = A288429 (n + 4)
    have hA : A288429 (n + 4) =
        2 * A288429 (n + 3) - A288429 (n + 2) + A288429 (n + 1) - A288429 n := rfl
    rw [hA, ← h3, ← h2, ← h1, ← h0]
    exact len_rec n

end FS2A288694

open OMA.S_oeis_a288694 FS2A288694 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288694.main := by
  intro n
  exact (len_eq n).1
