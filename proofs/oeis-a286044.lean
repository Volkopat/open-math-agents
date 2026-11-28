import OMAStatements.S_oeis_a286044
import Mathlib.Data.Nat.Digits.Defs

/-!
A286044 records the parity of successive change positions in the Thue–Morse word.
The odd positions all change. An even position `2 * m` changes precisely when `m`
does not. Counting these complementary positions gives the recurrence for A003160
and identifies its second iterate with the count of even change positions.
-/

namespace OMA.A286044

open OMA.S_oeis_a286044

private theorem tm_bit (n : ℕ) : tm n = 0 ∨ tm n = 1 := by
  unfold tm
  omega

private theorem tm_even (n : ℕ) : tm (2 * n) = tm n := by
  by_cases h : n = 0
  · subst n
    rfl
  · unfold tm
    rw [show 2 * n = 0 + 2 * n by omega, Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr h)]
    simp

private theorem tm_odd (n : ℕ) : tm (2 * n + 1) = 1 - tm n := by
  unfold tm
  rw [show 2 * n + 1 = 1 + 2 * n by omega,
    Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide)), List.sum_cons]
  omega

/-- A change at position `m` means that the letter at `m` differs from the preceding one. -/
private def changes (m : ℕ) : Bool := decide (tm m ≠ tm (m - 1))

private theorem changes_odd (m : ℕ) : changes (2 * m + 1) = true := by
  unfold changes
  rw [show 2 * m + 1 - 1 = 2 * m by omega, tm_odd, tm_even]
  rcases tm_bit m with h | h <;> simp [h]

private theorem changes_even (m : ℕ) (hm : 0 < m) : changes (2 * m) = !changes m := by
  unfold changes
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, tm_even, tm_odd]
  rcases tm_bit m with h | h <;> rcases tm_bit (m - 1) with h' | h' <;> simp [h, h']

private theorem even_of_no_change {m : ℕ} (h : changes m = false) : m % 2 = 0 := by
  by_contra he
  have hm : m = 2 * (m / 2) + 1 := by omega
  rw [hm, changes_odd] at h
  contradiction

/-- Number of change positions from `1` through `m`. -/
private def count : ℕ → ℕ
  | 0 => 0
  | m + 1 => count m + if changes (m + 1) then 1 else 0

private theorem count_odd (m : ℕ) : count (2 * m + 1) = count (2 * m) + 1 := by
  rw [count, changes_odd]
  rfl

private theorem count_even (m : ℕ) : count (2 * m) + count m = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hprevious := count_odd m
    have hbig : count (2 * (m + 1)) = count (2 * m + 1) +
        (if !changes (m + 1) then 1 else 0) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, count,
        show 2 * m + 1 + 1 = 2 * (m + 1) by omega, changes_even _ (by omega)]
    have hsmall : count (m + 1) = count m + (if changes (m + 1) then 1 else 0) := rfl
    cases h : changes (m + 1) <;> simp [h] at hbig hsmall <;> omega

private theorem count_balance (m : ℕ) : count m + count (m / 2) = m := by
  by_cases h : m % 2 = 0
  · have h' := count_even (m / 2)
    rwa [show 2 * (m / 2) = m by omega] at h'
  · have h' := count_even (m / 2)
    have h'' := count_odd (m / 2)
    rw [show 2 * (m / 2) + 1 = m by omega] at h''
    omega

private theorem count_quarter (m : ℕ) : count (m / 4) + (m + 1) / 2 = count m := by
  have h₁ := count_balance m
  have h₂ := count_balance (m / 2)
  rw [show m / 2 / 2 = m / 4 by omega] at h₂
  omega

private theorem count_pos (m : ℕ) (hm : 0 < m) : 0 < count m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : m = 0
    · subst m
      decide
    · have hp := ih (by omega)
      rw [count]
      omega

/-- The `n`-th positive change position, with `v 0 = 0` as its starting value. -/
private def v : ℕ → ℕ
  | 0 => 0
  | n + 1 => if changes (v n + 1) then v n + 1 else v n + 2

private theorem v_bounds (n : ℕ) : n + 1 ≤ v (n + 1) ∧ v (n + 1) ≤ 2 * n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [v]
    split <;> omega

private theorem v_changes (n : ℕ) : changes (v (n + 1)) = true := by
  rw [v]
  cases h : changes (v n + 1)
  · have he := even_of_no_change h
    simp only [Bool.false_eq_true, if_false]
    rw [show v n + 2 = 2 * ((v n + 1) / 2) + 1 by omega, changes_odd]
  · simp [h]

private theorem count_v (n : ℕ) : count (v n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnext := v_changes n
    rw [v] at hnext ⊢
    cases h : changes (v n + 1)
    · simp only [h, Bool.false_eq_true, if_false] at hnext ⊢
      rw [show v n + 2 = (v n + 1) + 1 by omega, count, count]
      simp [h, hnext, ih, show v n + 1 + 1 = v n + 2 by omega]
    · simp only [h, if_true] at hnext ⊢
      rw [count]
      simp [h, ih]

private theorem next_change (m : ℕ) :
    v (count m + 1) = if changes (m + 1) then m + 1 else m + 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    cases h : changes (m + 1)
    · have he := even_of_no_change h
      have hnext : changes (m + 1 + 1) = true := by
        rw [show m + 1 + 1 = 2 * ((m + 1) / 2) + 1 by omega, changes_odd]
      have heq : count (m + 1) = count m := by rw [count]; simp [h]
      rw [heq, ih]
      simp [h, hnext, show m + 2 = m + 1 + 1 by omega]
    · have heq : count (m + 1) = count m + 1 := by rw [count]; simp [h]
      rw [heq, v, ih]
      simp [h]

private theorem next_change_half (m : ℕ) : v (count m + 1) / 2 = (m + 1) / 2 := by
  rw [next_change]
  cases h : changes (m + 1)
  · have hm := even_of_no_change h
    simp only [Bool.false_eq_true, if_false]
    omega
  · simp

private theorem v_next_half (n : ℕ) : v (n + 1) / 2 = (v n + 1) / 2 := by
  rw [v]
  cases h : changes (v n + 1)
  · have hm := even_of_no_change h
    simp only [Bool.false_eq_true, if_false]
    omega
  · simp

/-- The number of positions without a change up to the `(n+1)`-st change. -/
private def model (n : ℕ) : ℕ := count (v (n + 1) / 2)

private theorem model_bounds (n : ℕ) (hn : 1 ≤ n) : 1 ≤ model n ∧ model n ≤ n := by
  obtain ⟨hlo, hhi⟩ := v_bounds n
  unfold model
  have hpos := count_pos (v (n + 1) / 2) (by omega)
  have hb := count_balance (v (n + 1) / 2)
  omega

private theorem model_comp (n : ℕ) : model (model n) = count (v (n + 2) / 4) := by
  unfold model
  rw [next_change_half]
  have hnext := v_next_half (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at hnext
  congr 1
  by_cases h : v (n + 1) % 2 = 0
  · have hv := (v_bounds n).1
    have he : changes (2 * (v (n + 1) / 2)) = true := by
      rw [show 2 * (v (n + 1) / 2) = v (n + 1) by omega]
      exact v_changes n
    rw [changes_even _ (by omega)] at he
    have hn : changes (v (n + 1) / 2) = false := by simpa using he
    have hm := even_of_no_change hn
    omega
  · omega

private theorem model_rec (n : ℕ) (hn : 3 ≤ n) :
    model n + model (model (n - 1)) + model (model (n - 2)) = n := by
  rw [model_comp, model_comp, show n - 1 + 2 = n + 1 by omega, show n - 2 + 2 = n by omega]
  have h₁ := count_quarter (v (n + 1))
  have h₂ := count_quarter (v n)
  rw [count_v] at h₁ h₂
  have hb := count_balance (v (n + 1))
  rw [count_v] at hb
  have hnext := v_next_half n
  unfold model
  omega

private theorem b_eq_model (n : ℕ) (hn : 1 ≤ n) : b n = model n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n ≤ 2
    · have he : n = 1 ∨ n = 2 := by omega
      rcases he with rfl | rfl <;> rw [b.eq_def, if_pos (by decide)] <;> decide
    · have h₁ := ih (n - 1) (by omega) (by omega)
      have h₂ := ih (n - 2) (by omega) (by omega)
      obtain ⟨hp₁, hb₁⟩ := model_bounds (n - 1) (by omega)
      obtain ⟨hp₂, hb₂⟩ := model_bounds (n - 2) (by omega)
      rw [b.eq_def, if_neg h, h₁, h₂, min_eq_left hb₁, min_eq_left hb₂,
        ih (model (n - 1)) (by omega) hp₁, ih (model (n - 2)) (by omega) hp₂]
      have hr := model_rec n (by omega)
      omega

private def slice (j len : ℕ) : List ℕ := (List.range len).map (fun k => tm (j + k))

private theorem slice_succ (j len : ℕ) : slice j (len + 1) = tm j :: slice (j + 1) len := by
  simp [slice, List.range_succ_eq_map, List.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]

/-- Start at the zero in the pair `01` or `10` and retain its remaining suffix. -/
private def centered (x : ℕ) (w : List ℕ) : List ℕ :=
  0 :: ((if x = 0 then [1] else []) ++ w)

private theorem compress_center (x y : ℕ) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (w : List ℕ) :
    rep011 (centered x ([y, 1 - y] ++ w)) =
      (if x = y then [0, 1] else [0]) ++ rep011 (centered y w) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl

private theorem center_head (x : ℕ) (w : List ℕ) : (rep011 (centered x w)).getD 0 0 = 0 := by
  have aux (w : List ℕ) : (rep011 (0 :: w)).getD 0 0 = 0 := by
    cases w with
    | nil => rfl
    | cons u w =>
      cases u with
      | zero => rfl
      | succ u =>
        cases u with
        | succ u => rfl
        | zero =>
          cases w with
          | nil => rfl
          | cons z w => cases z with
            | zero => rfl
            | succ z => cases z <;> rfl
  exact aux _

private theorem center_next (j len : ℕ) :
    rep011 (centered (tm j) (slice (2 * j + 2) (len + 2))) =
      (if tm j = tm (j + 1) then [0, 1] else [0]) ++
        rep011 (centered (tm (j + 1)) (slice (2 * (j + 1) + 2) len)) := by
  have hslice : slice (2 * j + 2) (len + 2) =
      [tm (j + 1), 1 - tm (j + 1)] ++ slice (2 * (j + 1) + 2) len := by
    rw [slice_succ, slice_succ, show 2 * j + 2 = 2 * (j + 1) by omega,
      tm_even, tm_odd]
    rfl
  rw [hslice]
  exact compress_center _ _ (tm_bit _) (tm_bit _) _

private theorem changes_pair (j : ℕ) : changes (2 * j + 2) = decide (tm j = tm (j + 1)) := by
  unfold changes
  rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    show 2 * j + 2 = 2 * (j + 1) by omega, tm_odd, tm_even]
  rcases tm_bit j with h | h <;> rcases tm_bit (j + 1) with h' | h' <;> simp [h, h']

private theorem count_pair (j : ℕ) :
    count (2 * (j + 1)) = count (2 * j) + (if tm j = tm (j + 1) then 2 else 1) := by
  have h : count (2 * j + 2) = count (2 * j + 1) + (if changes (2 * j + 2) then 1 else 0) := rfl
  rw [changes_pair, count_odd] at h
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, h]
  by_cases he : tm j = tm (j + 1) <;> simp [he, Nat.add_assoc]

private def marker (r : ℕ) : ℕ := if v r % 2 = 0 then 1 else 0

private theorem first_marker (j : ℕ) : marker (count (2 * j) + 1) = 0 := by
  rw [marker, next_change, changes_odd]
  simp only [if_true]
  exact if_neg (by omega)

private theorem second_marker (j : ℕ) (h : tm j = tm (j + 1)) :
    marker (count (2 * j) + 1 + 1) = 1 := by
  have hfirst : v (count (2 * j) + 1) = 2 * j + 1 := by rw [next_change, changes_odd]; rfl
  rw [marker, v, hfirst, changes_pair]
  simp [h, show (2 * j + 1 + 1) % 2 = 0 by omega]

/-- Compression emits one zero per input pair and an intervening one exactly at an even change. -/
private theorem center_at (j m e k : ℕ) (hk : k ≤ m) :
    (rep011 (centered (tm j) (slice (2 * j + 2) (2 * m + e)))).getD k 0 =
      marker (count (2 * j) + k + 1) := by
  induction m generalizing j k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    rw [center_head, Nat.add_zero, first_marker]
  | succ m ih =>
    rw [show 2 * (m + 1) + e = (2 * m + e) + 2 by omega, center_next]
    cases k with
    | zero =>
      rw [Nat.add_zero, first_marker]
      by_cases h : tm j = tm (j + 1) <;> simp [h]
    | succ k =>
      by_cases h : tm j = tm (j + 1)
      · cases k with
        | zero =>
          rw [second_marker j h]
          simp [h]
        | succ k =>
          simp only [h, if_true, List.cons_append, List.nil_append, List.getD_cons_succ]
          rw [ih (j + 1) k (by omega), count_pair, if_pos h]
          congr 1
          omega
      · simp only [if_neg h, List.cons_append, List.nil_append, List.getD_cons_succ]
        rw [ih (j + 1) k (by omega), count_pair, if_neg h]
        congr 1
        omega

private theorem a_eq_marker (n : ℕ) (hn : 1 ≤ n) : a n = marker n := by
  have len : 3 * n + 3 = (2 * (n - 1) + (n + 3)) + 2 := by omega
  have hs : tmWord (3 * n + 3) = slice 0 (3 * n + 3) := by simp [tmWord, slice]
  rw [a, hs, len, slice_succ, slice_succ]
  change (rep011 (centered (tm 0) (slice (2 * 0 + 2) (2 * (n - 1) + (n + 3))))).getD
    (n - 1) 0 = marker n
  rw [center_at 0 (n - 1) (n + 3) (n - 1) le_rfl]
  change marker (0 + (n - 1) + 1) = marker n
  rw [show 0 + (n - 1) + 1 = n by omega]

private theorem b_comp (n : ℕ) (hn : 1 ≤ n) : b (b n) = count (v (n + 2) / 4) := by
  rw [b_eq_model n hn, b_eq_model _ (model_bounds n hn).1, model_comp]

private theorem solve (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = (b (b (n - 2)) : ℤ) - (b (b (n - 3)) : ℤ) := by
  rw [a_eq_marker n (by omega), b_comp _ (by omega), b_comp _ (by omega),
    show n - 2 + 2 = n by omega, show n - 3 + 2 = n - 1 by omega]
  have h₁ := count_quarter (v n)
  have h₂ := count_quarter (v (n - 1))
  rw [count_v] at h₁ h₂
  have hnext := v_next_half (n - 1)
  rw [show n - 1 + 1 = n by omega] at hnext
  unfold marker
  by_cases h : v n % 2 = 0 <;> simp [h] <;> omega

end OMA.A286044

theorem OMA.solution : type_of% @OMA.S_oeis_a286044.main := OMA.A286044.solve
