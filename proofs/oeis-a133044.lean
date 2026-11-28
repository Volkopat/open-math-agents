import OMAStatements.S_oeis_a133044

namespace A133044P
open OMA.S_oeis_a133044 PowerSeries

/-- The Padovan sequence A000931: 1, 0, 0, 1, 0, 1, 1, 1, 2, 2, 3, ... -/
def q : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | k + 3 => q k + q (k + 1)

lemma hq (k : ℕ) : q (k + 3) = q k + q (k + 1) := rfl

lemma pq : ∀ k, p k = q (k + 5)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | k + 3 => by
    have e : p (k + 3) = p k + p (k + 1) := rfl
    rw [e, pq k, pq (k + 1), show k + 3 + 5 = (k + 5) + 3 by omega, hq (k + 5)]

lemma ca (n : ℕ) : a n = 2 * q (n + 4) * q (n + 5) - q (n + 2) ^ 2 := by
  induction n with
  | zero => simp [a]; decide
  | succ n ih =>
    have e : a (n + 1) = a n + p n ^ 2 := by
      simp only [a, Finset.sum_range_succ]
    rw [e, ih, pq, show n + 1 + 4 = n + 5 by omega, show n + 1 + 5 = n + 6 by omega,
      show n + 1 + 2 = n + 3 by omega]
    have h5 : q (n + 5) = q (n + 2) + q (n + 3) := hq (n + 2)
    have h6 : q (n + 6) = q (n + 3) + q (n + 4) := hq (n + 3)
    linear_combination (q (n + 5) - q (n + 3) + q (n + 2)) * h5 - 2 * q (n + 5) * h6

lemma rec (n : ℕ) (hn : 7 ≤ n) :
    a n = a (n - 1) + a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
  simp only [ca, Nat.add_assoc, Nat.reduceAdd]
  have h3 : q (m + 3) = q m + q (m + 1) := hq m
  have h4 : q (m + 4) = q (m + 1) + q (m + 2) := hq (m + 1)
  have h5 : q (m + 5) = q (m + 2) + q (m + 3) := hq (m + 2)
  have h6 : q (m + 6) = q (m + 3) + q (m + 4) := hq (m + 3)
  have h7 : q (m + 7) = q (m + 4) + q (m + 5) := hq (m + 4)
  have h8 : q (m + 8) = q (m + 5) + q (m + 6) := hq (m + 5)
  have h9 : q (m + 9) = q (m + 6) + q (m + 7) := hq (m + 6)
  have h10 : q (m + 10) = q (m + 7) + q (m + 8) := hq (m + 7)
  have h11 : q (m + 11) = q (m + 8) + q (m + 9) := hq (m + 8)
  have h12 : q (m + 12) = q (m + 9) + q (m + 10) := hq (m + 9)
  rw [h12, h11, h10, h9, h8, h7, h6, h5, h4, h3]
  ring

lemma cm (f : ℕ → ℚ) (d n : ℕ) :
    coeff n (PowerSeries.mk f * X ^ d) = if d ≤ n then f (n - d) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

lemma gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X ^ 3 - X ^ 2 + 2 * X - 1) * (X ^ 3 - X - 1) : ℚ⟦X⟧) =
      X * (X ^ 3 + X + 1) := by
  set f : ℕ → ℚ := fun n => (a n : ℚ) with hf
  have key : PowerSeries.mk f * ((X ^ 3 - X ^ 2 + 2 * X - 1) * (X ^ 3 - X - 1) : ℚ⟦X⟧) =
      PowerSeries.mk f - PowerSeries.mk f * X ^ 1 - PowerSeries.mk f * X ^ 2 - PowerSeries.mk f * X ^ 3
        + PowerSeries.mk f * X ^ 4 - PowerSeries.mk f * X ^ 5 + PowerSeries.mk f * X ^ 6 := by ring
  rw [key, show (X * (X ^ 3 + X + 1) : ℚ⟦X⟧) = X ^ 1 + X ^ 2 + X ^ 4 by ring]
  ext n
  simp only [map_sub, map_add, cm, coeff_mk, coeff_X_pow]
  by_cases hn : 7 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have r := rec (m + 7) hn
    simp only [hf, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega,
      show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, if_true,
      show m + 7 ≠ 1 by omega, show m + 7 ≠ 2 by omega, show m + 7 ≠ 4 by omega, if_false]
    rw [r]
    push_cast
    ring
  · have v : ∀ k, (a k : ℚ) = ((2 * q (k + 4) * q (k + 5) - q (k + 2) ^ 2 : ℤ) : ℚ) := fun k => by
      rw [ca]
    interval_cases n <;> simp [hf, v, q] <;> norm_num

end A133044P

theorem OMA.solution : type_of% @OMA.S_oeis_a133044.main := ⟨A133044P.rec, A133044P.gf⟩
