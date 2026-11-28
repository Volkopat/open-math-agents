import OMAStatements.S_oeis_a289060
import Mathlib

namespace A289060Aux

open OMA.S_oeis_a289060 in
lemma rw_ones_zero (k : ℕ) (w : List Bool) :
    rewrite (List.replicate (k + 1) true ++ false :: w)
      = List.replicate k true ++ (false :: true :: true :: rewrite w) := by
  induction k with
  | zero =>
    show rewrite (true :: false :: w) = [false, true, true] ++ rewrite w
    rw [rewrite]
  | succ k ih =>
    show rewrite (true :: true :: (List.replicate k true ++ false :: w))
      = true :: (List.replicate k true ++ (false :: true :: true :: rewrite w))
    rw [rewrite, show true :: (List.replicate k true ++ false :: w)
      = List.replicate (k + 1) true ++ false :: w from rfl, ih]

open OMA.S_oeis_a289060 in
lemma rw_ones1 (t : ℕ) : rewrite (List.replicate (t + 1) true) = List.replicate (t + 1) true := by
  induction t with
  | zero =>
    show rewrite [true] = [true]
    rw [rewrite]
  | succ t ih =>
    show rewrite (true :: true :: List.replicate t true) = true :: List.replicate (t + 1) true
    rw [rewrite, show true :: List.replicate t true = List.replicate (t + 1) true from rfl, ih]

open OMA.S_oeis_a289060 in
lemma rw_ones (t : ℕ) : rewrite (List.replicate t true) = List.replicate t true := by
  cases t with
  | zero =>
    show rewrite [] = []
    rw [rewrite]
  | succ t => exact rw_ones1 t

def blk (j : ℕ) (w : List Bool) : List Bool :=
  List.replicate (j + 1) true ++ false :: (List.replicate (j + 3) true ++ false ::
    (List.replicate (j + 3) true ++ false :: (List.replicate (j + 2) true ++ false :: w)))

open OMA.S_oeis_a289060 in
lemma h_blk (j : ℕ) (w : List Bool) :
    true :: true :: rewrite (blk j w) = blk (j + 1) (true :: true :: rewrite w) := by
  unfold blk
  rw [rw_ones_zero, rw_ones_zero, rw_ones_zero, rw_ones_zero]
  rfl

def U : ℕ → ℕ → ℕ → List Bool
  | _, 0, t => List.replicate t true
  | j, m + 1, t => blk j (U (j + 1) m t)

open OMA.S_oeis_a289060 in
lemma h_U (m : ℕ) : ∀ j t : ℕ, true :: true :: rewrite (U j m t) = U (j + 1) m (t + 2) := by
  induction m with
  | zero =>
    intro j t
    show true :: true :: rewrite (List.replicate t true) = true :: true :: List.replicate t true
    rw [rw_ones]
  | succ m ih =>
    intro j t
    show true :: true :: rewrite (blk j (U (j + 1) m t)) = blk (j + 1) (U (j + 1 + 1) m (t + 2))
    rw [h_blk, ih]

def P : List Bool :=
  [false, false, true, false, false, true, true, false, true, false, false, true, true, false,
    true, true, false, true, false, false, true, true, true, false, true, true, false, true, true,
    false, true, false, true, false, true, true, true, false, true, true, true, false, true, true,
    false]

open OMA.S_oeis_a289060 in
lemma rw_P (w : List Bool) : rewrite (P ++ w) = P ++ blk 1 (true :: true :: rewrite w) := by
  have e : rewrite (false :: false :: true :: false :: false :: true :: true :: false :: true :: false :: false ::
      true :: true :: false :: true :: true :: false :: true :: false :: false :: true :: true :: true
      :: false :: true :: true :: false :: true :: true :: false :: true :: false :: true :: false ::
      true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: false :: w)
      = false :: false :: true :: false :: false :: true :: true :: false :: true :: false :: false ::
        true :: true :: false :: true :: true :: false :: true :: false :: false :: true :: true :: true
        :: false :: true :: true :: false :: true :: true :: false :: true :: false :: true :: false ::
        true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: false :: true
        :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: true ::
        false :: true :: true :: true :: false :: true :: true :: rewrite w := by
    simp [rewrite]
  exact e

open OMA.S_oeis_a289060 in
lemma word7' : word 7
    = [false, false, true, false, false, true, true, false, true, false, false, true, true, false,
      true, true, false, true, false, false, true, true, true, false, true, true, false, true, true,
      false, true, false, true, false, true, true, true, false, true, true, true, false, true, true,
      false, true, true, true, true, true, true] := by
  simp [word, rewrite]

open OMA.S_oeis_a289060 in
lemma word7 : word 7 = P ++ List.replicate 6 true := word7'.trans (by decide +kernel)

open OMA.S_oeis_a289060 in
lemma word_ge (n : ℕ) : word (n + 7) = P ++ U 1 n (2 * n + 6) := by
  induction n with
  | zero => exact word7
  | succ n ih =>
    have e : word (n + 1 + 7) = rewrite (word (n + 7)) := rfl
    have e2 : 2 * (n + 1) + 6 = 2 * n + 6 + 2 := by ring
    rw [e, ih, rw_P, h_U]
    show P ++ blk 1 (U (1 + 1) n (2 * n + 6 + 2)) = P ++ blk 1 (U (1 + 1) n (2 * (n + 1) + 6))
    rw [e2]

lemma len_blk (j : ℕ) (w : List Bool) : (blk j w).length = 4 * j + 13 + w.length := by
  unfold blk
  simp only [List.length_append, List.length_cons, List.length_replicate]
  omega

lemma len_U (m : ℕ) : ∀ j t : ℕ, (U j m t).length = 2 * m * m + (4 * j + 11) * m + t := by
  induction m with
  | zero =>
    intro j t
    show (List.replicate t true).length = 2 * 0 * 0 + (4 * j + 11) * 0 + t
    rw [List.length_replicate]
    omega
  | succ m ih =>
    intro j t
    show (blk j (U (j + 1) m t)).length = 2 * (m + 1) * (m + 1) + (4 * j + 11) * (m + 1) + t
    rw [len_blk, ih]
    ring

open OMA.S_oeis_a289060 in
lemma ref_rec (n : ℕ) : reference (n + 8)
    = 3 * reference (n + 7) - 3 * reference (n + 6) + reference (n + 5) := by
  rw [reference]

open OMA.S_oeis_a289060 in
lemma ref_quad (n : ℕ) : reference (n + 5) = 2 * (n : ℤ) ^ 2 + 9 * (n : ℤ) + 25 ∧
    reference (n + 6) = 2 * ((n : ℤ) + 1) ^ 2 + 9 * ((n : ℤ) + 1) + 25 ∧
    reference (n + 7) = 2 * ((n : ℤ) + 2) ^ 2 + 9 * ((n : ℤ) + 2) + 25 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have r : reference (n + 8) = 3 * reference (n + 7) - 3 * reference (n + 6) + reference (n + 5) :=
      ref_rec n
    refine ⟨?_, ?_, ?_⟩
    · show reference (n + 6) = 2 * ((n + 1 : ℕ) : ℤ) ^ 2 + 9 * ((n + 1 : ℕ) : ℤ) + 25
      rw [Nat.cast_succ, h1]
    · show reference (n + 7) = 2 * (((n + 1 : ℕ) : ℤ) + 1) ^ 2 + 9 * (((n + 1 : ℕ) : ℤ) + 1) + 25
      rw [Nat.cast_succ, h2]
      ring
    · show reference (n + 8) = 2 * (((n + 1 : ℕ) : ℤ) + 2) ^ 2 + 9 * (((n + 1 : ℕ) : ℤ) + 2) + 25
      rw [Nat.cast_succ, r, h0, h1, h2]
      ring

open OMA.S_oeis_a289060 in
lemma small : ∀ n : ℕ, n < 7 → ((word n).length : ℤ) = reference n := by
  intro n hn
  interval_cases n <;> simp [word, rewrite, reference]

end A289060Aux

open OMA.S_oeis_a289060 A289060Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a289060.main := by
  intro n
  rcases Nat.lt_or_ge n 7 with h | h
  · exact small n h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have hP : P.length = 45 := rfl
    rw [word_ge, List.length_append, len_U, hP, (ref_quad m).2.2]
    push_cast
    ring
