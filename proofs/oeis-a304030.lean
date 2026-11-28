import OMAStatements.S_oeis_a304030
import Mathlib

open OMA.S_oeis_a304030


theorem x_add (n s t : ℕ) : x n (t + s) = x (x n t) s := by
  unfold x
  rw [Function.iterate_add_apply]
  rw [show collatz^[s] (collatz^[t] n) = collatz^[s] (collatz^[t] n) from rfl]
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]

theorem x_succ (n t : ℕ) : x n (t + 1) = collatz (x n t) := by
  unfold x; rw [Function.iterate_succ_apply']

theorem not_n (n : ℕ) (hn : 1 < n) (hr : ∃ t, x n t = 1) :
    ∀ t, 1 ≤ t → t ≤ stop n → x n t ≠ n := by
  intro t ht htS hx
  have hstop : x n (stop n) = 1 := Nat.sInf_mem hr
  have : x n (stop n - t) = 1 := by
    have e := x_add n (stop n - t) t
    rw [show t + (stop n - t) = stop n by omega, hx] at e
    rw [← e]; exact hstop
  have : stop n ≤ stop n - t := Nat.sInf_le (show stop n - t ∈ {t : ℕ | x n t = 1} from this)
  have h0 : stop n ≠ 0 := by
    intro h; rw [h] at hstop; simp [x] at hstop; omega
  omega

theorem parity (n : ℕ) (hn : 1 < n) (hr : ∃ t, x n t = 1) :
    ∀ T, 1 ≤ T → T ≤ stop n →
      ((Finset.range T).filter fun t => ((x n (t + 1) : ℤ) - n) * ((x n t : ℤ) - n) < 0).card % 2 =
        if (x n T < n ↔ x n 1 < n) then 0 else 1 := by
  intro T hT
  induction T with
  | zero => omega
  | succ T ih =>
    intro hTS
    rcases Nat.eq_zero_or_pos T with rfl | hT0
    · rw [if_pos Iff.rfl]
      simp only [zero_add, Finset.range_one, Finset.filter_singleton]
      rw [if_neg (by simp [x])]
      rfl
    · have ih' := ih hT0 (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      have hxT := not_n n hn hr T hT0 (by omega)
      have hxT1 := not_n n hn hr (T + 1) (by omega) hTS
      by_cases hc : ((x n (T + 1) : ℤ) - n) * ((x n T : ℤ) - n) < 0
      · rw [if_pos hc, Finset.card_insert_of_notMem (by simp)]
        have hside : (x n (T + 1) < n ↔ ¬ x n T < n) := by
          constructor
          · intro h1 h2
            have : (0 : ℤ) < ((x n (T + 1) : ℤ) - n) * ((x n T : ℤ) - n) := by
              apply mul_pos_of_neg_of_neg <;> push_cast <;> omega
            linarith
          · intro h2
            by_contra h1
            have a1 : (n : ℤ) < x n (T + 1) := by
              have : x n (T + 1) ≠ n := hxT1
              omega
            have a2 : (n : ℤ) < x n T := by
              have : x n T ≠ n := hxT
              omega
            have : (0 : ℤ) < ((x n (T + 1) : ℤ) - n) * ((x n T : ℤ) - n) := by
              apply mul_pos <;> linarith
            linarith
        by_cases hq : (x n T < n ↔ x n 1 < n)
        · rw [if_pos hq] at ih'
          rw [if_neg (by tauto)]
          omega
        · rw [if_neg hq] at ih'
          rw [if_pos (by tauto)]
          omega
      · rw [if_neg hc]
        have hside : (x n (T + 1) < n ↔ x n T < n) := by
          constructor
          · intro h1
            by_contra h2
            have a2 : (n : ℤ) < x n T := by
              have : x n T ≠ n := hxT
              omega
            have : ((x n (T + 1) : ℤ) - n) * ((x n T : ℤ) - n) < 0 := by
              apply mul_neg_of_neg_of_pos <;> push_cast <;> omega
            exact hc this
          · intro h2
            by_contra h1
            have a1 : (n : ℤ) < x n (T + 1) := by
              have : x n (T + 1) ≠ n := hxT1
              omega
            have : ((x n (T + 1) : ℤ) - n) * ((x n T : ℤ) - n) < 0 := by
              apply mul_neg_of_pos_of_neg <;> push_cast <;> omega
            exact hc this
        by_cases hq : (x n T < n ↔ x n 1 < n)
        · rw [if_pos hq] at ih'
          rw [if_pos (by tauto)]
          exact ih'
        · rw [if_neg hq] at ih'
          rw [if_neg (by tauto)]
          exact ih'

theorem OMA.solution : type_of% @OMA.S_oeis_a304030.main := by
  intro hC n hn
  have hr := hC n (by omega)
  have hstop : x n (stop n) = 1 := Nat.sInf_mem hr
  have h1 : 1 ≤ stop n := by
    by_contra h
    have : stop n = 0 := by omega
    rw [this] at hstop; simp [x] at hstop; omega
  have hp := parity n hn hr (stop n) h1 le_rfl
  unfold crossings
  rw [hp, hstop]
  have hx1 : x n 1 = collatz n := by simp [x]
  rw [hx1]
  rcases Nat.even_or_odd n with ⟨r, hr'⟩ | ⟨r, hr'⟩
  · have hc : collatz n = n / 2 := by unfold collatz; rw [if_pos (by omega)]
    rw [hc, if_pos (by constructor <;> intro _ <;> omega)]
    omega
  · have hc : collatz n = 3 * n + 1 := by unfold collatz; rw [if_neg (by omega)]
    rw [hc, if_neg (by intro h; have := h.1 (by omega); omega)]
    omega
