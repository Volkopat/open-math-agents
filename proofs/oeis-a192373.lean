import OMAStatements.S_oeis_a192373

namespace OMA.P192373

open Polynomial OMA.S_oeis_a192373

/-- Coordinates in the basis `1, x` of the reductions of `P_n` (first pair) and `Q_n` (second pair). -/
def w : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((1, 0), (0, 0))
  | n + 1 => (((w n).1.2 + 4 * (w n).2.1 + (w n).2.2,
      (w n).1.1 + (w n).1.2 + (w n).2.1 + (4 + 1) * (w n).2.2),
      ((w n).1.1 + (w n).2.2, (w n).1.2 + (w n).2.1 + (w n).2.2))

lemma w_succ (n : ℕ) : w (n + 1) = (((w n).1.2 + 4 * (w n).2.1 + (w n).2.2,
      (w n).1.1 + (w n).1.2 + (w n).2.1 + (4 + 1) * (w n).2.2),
      ((w n).1.1 + (w n).2.2, (w n).1.2 + (w n).2.1 + (w n).2.2)) := by rw [w]

lemma pq_succ (n : ℕ) :
    pq (n + 1) = (X * (pq n).1 + (X + 4) * (pq n).2, (pq n).1 + X * (pq n).2) := by rw [pq]

lemma red (n : ℕ) :
    (∃ s : ℤ[X], (pq n).1 = (X ^ 2 - X - 1) * s + (C (w n).1.2 * X + C (w n).1.1)) ∧
    (∃ s : ℤ[X], (pq n).2 = (X ^ 2 - X - 1) * s + (C (w n).2.2 * X + C (w n).2.1)) := by
  induction n with
  | zero => exact ⟨⟨0, by simp [w, pq]⟩, ⟨0, by simp [w, pq]⟩⟩
  | succ n ih =>
    obtain ⟨⟨s1, h1⟩, ⟨s2, h2⟩⟩ := ih
    rw [pq_succ, w_succ]
    refine ⟨⟨X * s1 + (X + 4) * s2 + C (w n).1.2 + C (w n).2.2, ?_⟩,
      ⟨s1 + X * s2 + C (w n).2.2, ?_⟩⟩
    · show X * (pq n).1 + (X + 4) * (pq n).2 = _
      rw [h1, h2]
      simp only [map_add, map_mul, map_ofNat, map_one]
      ring
    · show (pq n).1 + X * (pq n).2 = _
      rw [h1, h2]
      simp only [map_add]
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

lemma rem (n : ℕ) : (pq n).2 %ₘ (X ^ 2 - X - 1) = C (w n).2.2 * X + C (w n).2.1 := by
  obtain ⟨s, hs⟩ := (red n).2
  refine (div_modByMonic_unique s _ q_monic ⟨?_, ?_⟩).2
  · rw [hs]; ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma b_eq (j : ℕ) : a j = (w j).2.1 := by
  unfold a p
  rw [rem]; simp

lemma key (k : ℕ) :
    ((w (k + 4)).2.1 = 2 * (w (k + 3)).2.1 + 10 * (w (k + 2)).2.1 + (-6) * (w (k + 1)).2.1 + (-9) * (w k).2.1) ∧
    ((w (k + 4)).2.2 = 2 * (w (k + 3)).2.2 + 10 * (w (k + 2)).2.2 + (-6) * (w (k + 1)).2.2 + (-9) * (w k).2.2) := by
  have h4 : w (k + 4) = _ := w_succ (k + 3)
  have h3 : w (k + 3) = _ := w_succ (k + 2)
  have h2 : w (k + 2) = _ := w_succ (k + 1)
  have h1 : w (k + 1) = _ := w_succ k
  rw [h4, h3, h2, h1]
  constructor <;> ring

end OMA.P192373

open OMA.S_oeis_a192373 OMA.P192373 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192373.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  have e4 : k + 4 - 4 = k := by omega
  rw [e1, e2, e3, e4]
  simp only [b_eq]
  linarith [(key k).1]
