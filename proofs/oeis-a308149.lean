import OMAStatements.S_oeis_a308149

-- Problem: A308149: Positive integers with Collatz trajectories that do not include the number 5.
-- Upstream: formal-conjectures statements/oeis-a308149.lean:0 (declaration OMA.S_oeis_a308149.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: P = {1, 2, 4, 8, 16} is closed under T. A trajectory that reaches 1 from a start
-- outside P enters P from a number outside P whose image is in P; that number is 32 or 5.
-- The trajectories of 5 and of 32 enter P at once and never return, so no trajectory contains
-- both 5 and 32. The numbers 1..16 outside P reach 5 in at most 14 steps.

namespace H15A308149

open OMA.S_oeis_a308149

def inP (x : ℕ) : Prop := x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 16

theorem T_inP (x : ℕ) (h : inP x) : inP (T x) := by
  unfold inP at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · unfold inP; decide
  · unfold inP; decide
  · unfold inP; decide
  · unfold inP; decide
  · unfold inP; decide

theorem iter_inP (x : ℕ) (h : inP x) (k : ℕ) : inP (T^[k] x) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact T_inP _ ih

theorem notTraj_of_inP (x y : ℕ) (h : inP x) (hy : ¬ inP y) : ¬ InTraj x y := by
  unfold InTraj
  rintro ⟨k, hk⟩
  have h2 := iter_inP x h k
  rw [hk] at h2
  exact hy h2

theorem orbit5 (k : ℕ) : T^[k] 5 ≠ 32 := by
  cases k with
  | zero => decide
  | succ k =>
    rw [Function.iterate_succ_apply]
    intro h32
    have h := iter_inP (T 5) (by unfold inP; decide) k
    rw [h32] at h
    unfold inP at h
    omega

theorem orbit32 (k : ℕ) : T^[k] 32 ≠ 5 := by
  cases k with
  | zero => decide
  | succ k =>
    rw [Function.iterate_succ_apply]
    intro h5
    have h := iter_inP (T 32) (by unfold inP; decide) k
    rw [h5] at h
    unfold inP at h
    omega

theorem excl (n : ℕ) (h32 : InTraj n 32) : ¬ InTraj n 5 := by
  unfold InTraj at h32 ⊢
  rintro ⟨j, hj⟩
  obtain ⟨i, hi⟩ := h32
  rcases Nat.le_total i j with hij | hij
  · have h1 : T^[j - i] 32 = 5 := by
      rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel hij]
      exact hj
    exact orbit32 _ h1
  · have h1 : T^[i - j] 5 = 32 := by
      rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel hij]
      exact hi
    exact orbit5 _ h1

theorem reach (k : ℕ) : ∀ n, T^[k] n = 1 → ¬ inP n → InTraj n 5 ∨ InTraj n 32 := by
  induction k with
  | zero =>
    intro n hn hP
    unfold inP at hP
    exact (hP (Or.inl hn)).elim
  | succ k ih =>
    unfold InTraj at ih ⊢
    intro n hn hP
    rw [Function.iterate_succ_apply] at hn
    by_cases hT : inP (T n)
    · unfold inP at hT hP
      unfold T at hT
      by_cases he : n % 2 = 0
      · rw [if_pos he] at hT
        right
        exact ⟨0, by show n = 32; omega⟩
      · rw [if_neg he] at hT
        left
        exact ⟨0, by show n = 5; omega⟩
    · rcases ih (T n) hn hT with ⟨j, hj⟩ | ⟨j, hj⟩
      · left
        exact ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hj⟩
      · right
        exact ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hj⟩

theorem small (n : ℕ) (h1 : 1 ≤ n) (h16 : n ≤ 16) : inP n ∨ InTraj n 5 := by
  unfold inP InTraj
  interval_cases n
  · left; decide
  · left; decide
  · right; exact ⟨2, by decide⟩
  · left; decide
  · right; exact ⟨0, by decide⟩
  · right; exact ⟨3, by decide⟩
  · right; exact ⟨11, by decide⟩
  · left; decide
  · right; exact ⟨14, by decide⟩
  · right; exact ⟨1, by decide⟩
  · right; exact ⟨9, by decide⟩
  · right; exact ⟨4, by decide⟩
  · right; exact ⟨4, by decide⟩
  · right; exact ⟨12, by decide⟩
  · right; exact ⟨12, by decide⟩
  · left; decide

end H15A308149

open OMA.S_oeis_a308149 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308149.main := by
  have h5 : ¬ H15A308149.inP 5 := by unfold H15A308149.inP; decide
  have h32 : ¬ H15A308149.inP 32 := by unfold H15A308149.inP; decide
  refine ⟨?_, ?_⟩
  · ext n
    constructor
    · rintro ⟨h1, hn5, h16⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases H15A308149.small n h1 h16 with h | h
      · unfold H15A308149.inP at h
        exact h
      · exact absurd h hn5
    · intro hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      have hP : H15A308149.inP n := by
        unfold H15A308149.inP
        exact hn
      show 1 ≤ n ∧ ¬ InTraj n 5 ∧ n ≤ 16
      exact ⟨by omega, H15A308149.notTraj_of_inP n 5 hP h5, by omega⟩
  · intro hC
    ext n
    constructor
    · rintro ⟨h1, hn5, h16⟩
      show 1 ≤ n ∧ InTraj n 32
      refine ⟨h1, ?_⟩
      obtain ⟨k, hk⟩ := hC n h1
      have hnP : ¬ H15A308149.inP n := by
        unfold H15A308149.inP
        omega
      rcases H15A308149.reach k n hk hnP with h | h
      · exact absurd h hn5
      · exact h
    · rintro ⟨h1, hn32⟩
      show 1 ≤ n ∧ ¬ InTraj n 5 ∧ 16 < n
      refine ⟨h1, H15A308149.excl n hn32, ?_⟩
      by_contra hle
      rcases H15A308149.small n h1 (by omega) with h | h
      · exact H15A308149.notTraj_of_inP n 32 h h32 hn32
      · exact H15A308149.excl n hn32 h
