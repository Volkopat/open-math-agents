import OMAStatements.S_oeis_a319303
import Mathlib

open OMA.S_oeis_a319303


theorem walk_nb (r v : ℕ) (h : ¬ (4 < v ∧ (v + 2) % 6 = 0)) : walk (r + 1) v = walk r (2 * v) := by
  rw [walk, if_neg h]

theorem walk_half (r v : ℕ) (h : 4 < v ∧ (v + 2) % 6 = 0) : walk (2 * r + 1) v = walk r (2 * v) := by
  rw [walk, if_pos h, if_pos (by omega), show 2 * r / 2 = r by omega]

theorem walk_trip (r v : ℕ) (h : 4 < v ∧ (v + 2) % 6 = 0) :
    walk (2 * r + 2) v = walk r ((v - 1) / 3) := by
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by ring, walk, if_pos h, if_neg (by omega),
    show (2 * r + 1) / 2 = r by omega]

theorem step_double (v w : ℕ) (h : ∃ r, walk r (2 * v) = w) : ∃ r, walk r v = w := by
  obtain ⟨r, hr⟩ := h
  by_cases hb : 4 < v ∧ (v + 2) % 6 = 0
  · exact ⟨2 * r + 1, by rw [walk_half r v hb, hr]⟩
  · exact ⟨r + 1, by rw [walk_nb r v hb, hr]⟩

theorem step_trip (v w : ℕ) (hb : 4 < v ∧ (v + 2) % 6 = 0) (h : ∃ r, walk r ((v - 1) / 3) = w) :
    ∃ r, walk r v = w := by
  obtain ⟨r, hr⟩ := h
  exact ⟨2 * r + 2, by rw [walk_trip r v hb, hr]⟩

theorem iter_zero (T : ℕ) : collatz^[T] 0 = 0 := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem key : ∀ T v, collatz^[T] v = 1 → ∀ w, (∃ r, walk r v = w) → ∃ r, walk r 1 = w := by
  intro T
  induction T with
  | zero =>
    intro v hv w hw
    simp only [Function.iterate_zero, id] at hv
    subst hv; exact hw
  | succ T ih =>
    intro v hv w hw
    by_cases h1 : v = 1
    · subst h1; exact hw
    have hv0 : v ≠ 0 := by
      rintro rfl; rw [iter_zero] at hv; omega
    rw [Function.iterate_succ_apply] at hv
    apply ih (collatz v) hv w
    unfold collatz
    by_cases he : v % 2 = 0
    · rw [if_pos he]
      apply step_double
      rw [show 2 * (v / 2) = v by omega]
      exact hw
    · rw [if_neg he]
      apply step_trip (3 * v + 1) w (by omega)
      rw [show (3 * v + 1 - 1) / 3 = v by omega]
      exact hw

theorem OMA.solution : type_of% @OMA.S_oeis_a319303.main := by
  intro hC m hm
  obtain ⟨t, ht⟩ := hC m hm
  exact key t m ht m ⟨0, by rw [walk]⟩
