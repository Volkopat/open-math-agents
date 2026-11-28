import OMAStatements.S_oeis_a192431

-- Proof of the statement in #26398 (statement by @JeremyDevs). Credit for the proof: @bnb9001
-- Modulo X^2 - X - 1, P_n = A + BX and Q_n = C + DX with an integer 4x4 linear recursion; the
-- coefficient a(n) = B + D, and unrolling four steps gives the stated recurrence.

namespace OMA_OEIS_A192431_Proof

open OMA.S_oeis_a192431 Polynomial

/-- coefficients of `P_n ≡ A + B X`, `Q_n ≡ C + D X` modulo `X^2 - X - 1` -/
def cf : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 => ((cf n).2.1 + 2 * (cf n).2.2.1 + (cf n).2.2.2,
      (cf n).1 + (cf n).2.1 + (cf n).2.2.1 + 3 * (cf n).2.2.2,
      (cf n).1 + (cf n).2.2.2, (cf n).2.1 + (cf n).2.2.1 + (cf n).2.2.2)

def cA (n : ℕ) : ℤ := (cf n).1
def cB (n : ℕ) : ℤ := (cf n).2.1
def cC (n : ℕ) : ℤ := (cf n).2.2.1
def cD (n : ℕ) : ℤ := (cf n).2.2.2

theorem cA_succ (n : ℕ) : cA (n + 1) = cB n + 2 * cC n + cD n := rfl
theorem cB_succ (n : ℕ) : cB (n + 1) = cA n + cB n + cC n + 3 * cD n := rfl
theorem cC_succ (n : ℕ) : cC (n + 1) = cA n + cD n := rfl
theorem cD_succ (n : ℕ) : cD (n + 1) = cB n + cC n + cD n := rfl

noncomputable def q : ℤ[X] := X ^ 2 - X - 1

theorem cong (n : ℕ) : ∃ k1 k2 : ℤ[X],
    (pq n).1 = C (cA n) + C (cB n) * X + q * k1 ∧
    (pq n).2 = C (cC n) + C (cD n) * X + q * k2 := by
  induction n with
  | zero => exact ⟨0, 0, by simp [pq, cA, cB, cf], by simp [pq, cC, cD, cf]⟩
  | succ n ih =>
    obtain ⟨k1, k2, h1, h2⟩ := ih
    refine ⟨X * k1 + (X + 2) * k2 + C (cB n) + C (cD n), k1 + X * k2 + C (cD n), ?_, ?_⟩
    · show X * (pq n).1 + (X + 2) * (pq n).2 = _
      rw [h1, h2, cA_succ, cB_succ]
      simp only [q, map_add, map_mul, map_ofNat]
      ring
    · show (pq n).1 + X * (pq n).2 = _
      rw [h1, h2, cC_succ, cD_succ]
      simp only [q, map_add]
      ring

theorem q_monic : q.Monic := by unfold q; monicity!

theorem q_deg : q.degree = 2 := by unfold q; compute_degree!

theorem a_eq (n : ℕ) : a n = cB n + cD n := by
  obtain ⟨k1, k2, h1, h2⟩ := cong n
  have hp : p n = (C (cA n + cC n) + C (cB n + cD n) * X) + q * (k1 + k2) := by
    unfold p; rw [h1, h2]; simp only [map_add]; ring
  have hdeg : (C (cA n + cC n) + C (cB n + cD n) * X).degree < q.degree := by
    rw [q_deg]
    refine lt_of_le_of_lt (b := 1) ?_ (by norm_num)
    rw [add_comm]; exact Polynomial.degree_linear_le
  have hmod := (Polynomial.div_modByMonic_unique (k1 + k2) _ q_monic ⟨hp.symm, hdeg⟩).2
  unfold a
  rw [show (X ^ 2 - X - 1 : ℤ[X]) = q from rfl, hmod, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X]
  simp

theorem stmt' : ∀ n : ℕ, 3 < n →
    a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  simp only [a_eq, cA_succ, cB_succ, cC_succ, cD_succ]
  ring

end OMA_OEIS_A192431_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a192431.main := OMA_OEIS_A192431_Proof.stmt'
