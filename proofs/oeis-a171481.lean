import OMAStatements.S_oeis_a171481
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a171481.main := by
  intro a h0 h1 h2 hr
  have h3 : a 3 = 1 := by
    have := hr 3 (by norm_num)
    simpa [h2, h1, h0] using this
  have h4 : a 4 = 2 := by
    have := hr 4 (by norm_num)
    simpa [h3, h2, h1, h0] using this
  have key : ∀ n, (1 ≤ n → (a n = a (n - 1) ∨ a n = a (n - 1) + 1)) ∧ (1 ≤ n → 1 ≤ a n) ∧
      (4 ≤ n → a n + 2 ≤ n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 5 with hn | hn
      · interval_cases n <;> simp [h0, h1, h2, h3, h4]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        obtain ⟨s1, p1, b1⟩ := ih m (by omega)
        have s := s1 (by omega)
        have p := p1 (by omega)
        have b := b1 (by omega)
        have e1 := hr (m + 1) (by omega)
        have e0 := hr m (by omega)
        simp only [Nat.add_sub_cancel] at e1
        have step : a (m + 1) = a m ∨ a (m + 1) = a m + 1 := by
          rcases s with s | s
          · have hk := (ih (m - 1 - a m) (by omega)).1 (by omega)
            have i1 : m + 1 - a m - 2 = m - 1 - a m := by omega
            have i2 : m - a (m - 1) - 2 = m - 1 - a m - 1 := by omega
            rw [i1] at e1
            rw [i2, ← s] at e0
            omega
          · have hk := (ih (a m) (by omega)).1 (by omega)
            have i1 : m + 1 - a m - 2 = m - a (m - 1) - 2 := by omega
            have i3 : a m - 1 = a (m - 1) := by omega
            rw [i1] at e1
            rw [i3] at hk
            omega
        refine ⟨fun _ => by simpa using step, fun _ => by omega, fun _ => by omega⟩
  exact fun n hn => (key n).1 hn
