import OMAStatements.S_oeis_a192752

namespace OMA.P192752

open Polynomial OMA.S_oeis_a192752 Nat

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((w n).2 + (4 * ((n : ℤ) + 1) + 3), (w n).1 + (w n).2)

lemma red (n : ℕ) : ∃ s : ℤ[X],
    p n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w, p]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨X * s + C (w n).2, ?_⟩
    rw [p, hs]
    simp only [w, map_add]
    ring

lemma q_monic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  norm_num

lemma q_degree : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e, degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow] <;> try rfl
  rw [degree_X_add_C]
  norm_num

lemma rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (w n).2 * X + C (w n).1 := by
  obtain ⟨s, hs⟩ := red n
  refine (div_modByMonic_unique s _ q_monic ⟨?_, ?_⟩).2
  · rw [hs]; ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma a_eq (n : ℕ) : a n = (w n).1 := by
  unfold a
  rw [rem]; simp

lemma fibz (m : ℕ) : (fib (m + 2) : ℤ) = (fib (m + 1) : ℤ) + (fib m : ℤ) := by
  rw [fib_add_two]
  push_cast
  ring

lemma key : ∀ n : ℕ, (w n).1 = (fib (n + 3) : ℤ) + 5 * (fib (n + 2) : ℤ) - 2 * (fib (n + 1) : ℤ) - 4 ∧
    (w n).2 = (fib (n + 4) : ℤ) + 5 * (fib (n + 3) : ℤ) - 2 * (fib (n + 2) : ℤ) - 4 * (n : ℤ) - 11 := by
  intro n
  induction n with
  | zero =>
    have h1 : fib 1 = 1 := rfl
    have h2 : fib 2 = 1 := rfl
    have h3 : fib 3 = 2 := rfl
    have h4 : fib 4 = 3 := rfl
    constructor <;> simp [w, h1, h2, h3, h4]
  | succ n ih =>
    obtain ⟨hu, hv⟩ := ih
    have f3 : (fib (n + 3) : ℤ) = (fib (n + 2) : ℤ) + (fib (n + 1) : ℤ) := fibz (n + 1)
    have f4 : (fib (n + 4) : ℤ) = (fib (n + 3) : ℤ) + (fib (n + 2) : ℤ) := fibz (n + 2)
    have f5 : (fib (n + 5) : ℤ) = (fib (n + 4) : ℤ) + (fib (n + 3) : ℤ) := fibz (n + 3)
    constructor
    · show (w (n + 1)).1 = (fib (n + 4) : ℤ) + 5 * (fib (n + 3) : ℤ) - 2 * (fib (n + 2) : ℤ) - 4
      simp only [w, hv]
      linarith
    · show (w (n + 1)).2 = (fib (n + 5) : ℤ) + 5 * (fib (n + 4) : ℤ) - 2 * (fib (n + 3) : ℤ) - 4 * ((n : ℤ) + 1) - 11
      simp only [w, hu, hv]
      linarith

end OMA.P192752

open OMA.S_oeis_a192752 OMA.P192752 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192752.main := by
  intro n
  rw [a_eq, (key n).1]
  ring
