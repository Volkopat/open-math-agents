import OMAStatements.S_oeis_a192347

namespace OMA.P_oeis_a192347

open Polynomial OMA.S_oeis_a192347

noncomputable def q : ℤ[X] := X ^ 2 - X - 1

lemma q_monic : q.Monic := by
  unfold q
  have : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  apply monic_X_pow_sub
  compute_degree!

lemma q_natDegree : q.natDegree = 2 := by
  unfold q
  compute_degree!

/-- Coefficients of the reduction of p(n,x). -/
noncomputable def c0 (n : ℕ) : ℤ := (p n %ₘ q).coeff 0
noncomputable def c1 (n : ℕ) : ℤ := (p n %ₘ q).coeff 1

lemma eval_p (t : ℝ) (ht : t ^ 2 = t + 1) (n : ℕ) :
    (p n).eval₂ (Int.castRingHom ℝ) t = (c1 n : ℝ) * t + c0 n := by
  have h1 := modByMonic_add_div (p n) q
  have hdeg : (p n %ₘ q).natDegree ≤ 1 := by
    have hq1 : q ≠ 1 := by
      intro h
      have := q_natDegree
      rw [h] at this
      simp at this
    have := natDegree_modByMonic_lt (p n) q_monic hq1
    rw [q_natDegree] at this
    omega
  have h2 := eq_X_add_C_of_natDegree_le_one hdeg
  have hq : q.eval₂ (Int.castRingHom ℝ) t = 0 := by
    simp [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linarith
  rw [← h1, eval₂_add, eval₂_mul, hq, zero_mul, add_zero, h2]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  simp [c0, c1]

lemma eval_p_closed (t : ℝ) (ht2 : 0 ≤ t + 2) (n : ℕ) :
    (p n).eval₂ (Int.castRingHom ℝ) t =
      ((√(t + 2) + t) ^ n + (-√(t + 2) + t) ^ n) / 2 := by
  set d := √(t + 2) with hd
  have hdd : d ^ 2 = t + 2 := Real.sq_sqrt ht2
  rw [add_pow, add_pow, ← Finset.sum_add_distrib, Finset.sum_div]
  unfold p
  rw [eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.even_or_odd j with he | ho
  · rw [if_pos he]
    obtain ⟨k, hk⟩ := he
    have hj : j = 2 * k := by omega
    subst hj
    have : (2 * k) / 2 = k := by omega
    rw [this]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, eval₂_add]
    simp only [eq_intCast, Int.cast_natCast, Int.cast_ofNat]
    rw [Even.neg_pow ⟨k, by ring⟩, pow_mul, hdd]
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho), Odd.neg_pow ho]
    simp

lemma rec_eval (t : ℝ) (ht : t ^ 2 = t + 1) (ht2 : 0 ≤ t + 2) (n : ℕ) :
    (p (n + 2)).eval₂ (Int.castRingHom ℝ) t =
      2 * t * (p (n + 1)).eval₂ (Int.castRingHom ℝ) t + (p n).eval₂ (Int.castRingHom ℝ) t := by
  rw [eval_p_closed t ht2, eval_p_closed t ht2, eval_p_closed t ht2]
  set d := √(t + 2) with hd
  have hdd : d ^ 2 = t + 2 := Real.sq_sqrt ht2
  have hu : (d + t) ^ 2 = 2 * t * (d + t) + 1 := by linear_combination hdd - ht
  have hv : (-d + t) ^ 2 = 2 * t * (-d + t) + 1 := by linear_combination hdd - ht
  rw [pow_add, pow_add (d + t) n 1, pow_add (-d + t), pow_add (-d + t) n 1, hu, hv]
  ring

lemma coeff_rec (n : ℕ) :
    c0 (n + 2) = 2 * c1 (n + 1) + c0 n ∧
      c1 (n + 2) = 2 * c0 (n + 1) + 2 * c1 (n + 1) + c1 n := by
  have key : ∀ t : ℝ, t ^ 2 = t + 1 → 0 ≤ t + 2 →
      ((c0 (n + 2) - 2 * c1 (n + 1) - c0 n : ℤ) : ℝ) +
        ((c1 (n + 2) - 2 * c0 (n + 1) - 2 * c1 (n + 1) - c1 n : ℤ) : ℝ) * t = 0 := by
    intro t ht ht2
    have h := rec_eval t ht ht2 n
    rw [eval_p t ht, eval_p t ht, eval_p t ht] at h
    push_cast
    linear_combination h + (2 * (c1 (n + 1) : ℝ)) * ht
  have hφ := key Real.goldenRatio Real.goldenRatio_sq (by linarith [Real.goldenRatio_pos])
  have hψ := key Real.goldenConj Real.goldenConj_sq (by linarith [Real.neg_one_lt_goldenConj])
  have hs : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    rw [Real.goldenRatio_sub_goldenConj]; positivity
  set E0 : ℤ := c0 (n + 2) - 2 * c1 (n + 1) - c0 n
  set E1 : ℤ := c1 (n + 2) - 2 * c0 (n + 1) - 2 * c1 (n + 1) - c1 n
  have h1 : (E1 : ℝ) = 0 := by
    have : (E1 : ℝ) * (Real.goldenRatio - Real.goldenConj) = 0 := by linear_combination hφ - hψ
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hs
  have h0 : (E0 : ℝ) = 0 := by linear_combination hφ - Real.goldenRatio * h1
  have h1' : E1 = 0 := by exact_mod_cast h1
  have h0' : E0 = 0 := by exact_mod_cast h0
  constructor <;> omega

end OMA.P_oeis_a192347

theorem OMA.solution : type_of% @OMA.S_oeis_a192347.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have ha : ∀ k, OMA.S_oeis_a192347.a (k + 1) = OMA.P_oeis_a192347.c1 k := fun k => rfl
  have e1 : m + 5 - 1 = m + 3 + 1 := by omega
  have e2 : m + 5 - 2 = m + 2 + 1 := by omega
  have e3 : m + 5 - 3 = m + 1 + 1 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  rw [e1, e2, e3, e4, show m + 5 = m + 4 + 1 by omega, ha, ha, ha, ha, ha]
  have r1 := (OMA.P_oeis_a192347.coeff_rec (m + 2)).2
  have r2 := (OMA.P_oeis_a192347.coeff_rec (m + 1)).1
  have r3 := (OMA.P_oeis_a192347.coeff_rec m).2
  linear_combination r1 + 2 * r2 - r3
