import OMAStatements.S_oeis_a316316
import Mathlib

/-
A316316: term(n + 12) = term(n) + 40 for n > 0, where the terms are read off a window of six
consecutive values updated by x6 = x5 - x4 + 2 x3 - x2 + x1 - x0.

The update commutes with adding a constant to all six entries, because the coefficients
1 - 1 + 2 - 1 + 1 - 1 sum to 1. So it is enough to check that the window after twelve steps is the
initial window plus 40 in every entry (a finite computation), and then induct.
-/

namespace OMA.P316316

open OMA.S_oeis_a316316

lemma key : ∀ k : ℕ,
    (window (k + 12)).a = (window k).a + 40 ∧ (window (k + 12)).b = (window k).b + 40 ∧
    (window (k + 12)).c = (window k).c + 40 ∧ (window (k + 12)).d = (window k).d + 40 ∧
    (window (k + 12)).e = (window k).e + 40 ∧ (window (k + 12)).f = (window k).f + 40 := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    have e1 : window (k + 1 + 12) = step (window (k + 12)) := rfl
    have e2 : window (k + 1) = step (window k) := rfl
    rw [e1, e2]
    simp only [step]
    refine ⟨h2, h3, h4, h5, h6, ?_⟩
    linarith

lemma main' : ∀ n : ℕ, 0 < n → term (n + 12) = term n + 40 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

end OMA.P316316

theorem OMA.solution : type_of% @OMA.S_oeis_a316316.main := OMA.P316316.main'
