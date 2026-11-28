import OMAStatements.S_oeis_a297444

/-! The least positive integer of a prescribed ternary down-variation. -/
-- Credit: @STARDUSTLC666

namespace TernaryThreshold

open OMA.S_oeis_a297444

-- Appending 20 in ternary sends q to 9*q + 6.
private def least : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | n + 3 => 9 * least (n + 1) + 6

private lemma recurrence (n : ℕ) : a (n+3) = 9 * a (n+1) + 6 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change a (n+3) + 9 * a (n+2) - 9 * a (n+1) = 9 * a (n+2) + 6
    omega

private lemma sequence_eq (n : ℕ) : a n = (least n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 => decide
    | k + 3 =>
      rw [recurrence, ih (k+1) (by omega), least]
      push_cast
      rfl

-- The added drops depend only on the last digit of the prefix and the two new digits.
private lemma append_pair {q t u : ℕ} (hq : 0 < q) (ht : t < 3) (hu : u < 3) :
    downVar (u + 3 * (t + 3*q)) = (t-u) + (q%3-t) + downVar q := by
  unfold downVar
  rw [Nat.digits_add 3 (by decide) u (t+3*q) hu (Or.inr (by omega)),
    Nat.digits_add 3 (by decide) t q ht (Or.inr hq.ne'),
    Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hq.ne']
  simp only [down]
  omega

private lemma witness (n : ℕ) :
    0 < least n ∧ downVar (least n) = n ∧ (0 < n → least n % 3 = 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 => decide
    | k + 3 =>
      obtain ⟨pos,variation,last⟩ := ih (k+1) (by omega)
      have digits := append_pair (q := least (k+1)) (t := 2) (u := 0) pos
        (by decide) (by decide)
      rw [last (by omega), variation] at digits
      have eq : least (k+3) = 0 + 3*(2 + 3*least (k+1)) := by rw [least]; omega
      rw [eq,digits]
      omega

private lemma lower_bound (n : ℕ) :
    ∀ m : ℕ, 0 < m → n ≤ downVar m → least n ≤ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m hm high
    match n with
    | 0 => exact hm
    | 1 =>
      by_contra! small
      exact (not_lt_of_ge high) ((by decide : ∀ j : Fin 3, downVar j < 1) ⟨m,small⟩)
    | 2 =>
      by_contra! small
      exact (not_lt_of_ge high) ((by decide : ∀ j : Fin 6, downVar j < 2) ⟨m,small⟩)
    | k + 3 =>
      let q := m/9
      let t := m/3%3
      let u := m%3
      have large : 9 ≤ m := by
        by_contra! small
        have low := (by decide : ∀ j : Fin 9, downVar j < 3) ⟨m,small⟩
        change downVar m < 3 at low
        omega
      have qp : 0 < q := by dsimp [q]; omega
      have ht : t < 3 := Nat.mod_lt _ (by decide)
      have hu : u < 3 := Nat.mod_lt _ (by decide)
      have decomposition : m = u + 3*(t + 3*q) := by dsimp [q,t,u]; omega
      have digits := append_pair (q := q) (t := t) (u := u) qp ht hu
      rw [← decomposition] at digits
      have tail_bound : (t-u) + (q%3-t) ≤ 2 := by omega
      have lower := ih (k+1) (by omega) q qp (by omega)
      rw [least]
      by_cases equal : q = least (k+1)
      · obtain ⟨_,variation,last⟩ := witness (k+1)
        rw [equal,variation,last (by omega)] at digits
        omega
      · omega

end TernaryThreshold

open OMA.S_oeis_a297444 TernaryThreshold

theorem OMA.solution : type_of% @OMA.S_oeis_a297444.main := by
  intro n
  obtain ⟨pos,variation,_⟩ := witness n
  exact ⟨least n, (sequence_eq n).symm, ⟨pos,variation⟩,
    fun m hm => lower_bound n m hm.1 hm.2.ge⟩
