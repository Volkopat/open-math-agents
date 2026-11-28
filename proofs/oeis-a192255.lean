import OMAStatements.S_oeis_a192255

namespace OMA.P_oeis_a192255

open Polynomial OMA.S_oeis_a192255

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

lemma eval_mod (f : ℤ[X]) (t : ℝ) (ht : t ^ 2 = t + 1) :
    f.eval₂ (Int.castRingHom ℝ) t =
      ((f %ₘ q).coeff 1 : ℝ) * t + ((f %ₘ q).coeff 0 : ℝ) := by
  have h1 := modByMonic_add_div f q
  have hdeg : (f %ₘ q).natDegree ≤ 1 := by
    have hq1 : q ≠ 1 := by
      intro h
      have := q_natDegree
      rw [h] at this
      simp at this
    have := natDegree_modByMonic_lt f q_monic hq1
    rw [q_natDegree] at this
    omega
  have h2 := eq_X_add_C_of_natDegree_le_one hdeg
  have hq : q.eval₂ (Int.castRingHom ℝ) t = 0 := by
    simp [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linarith
  have h3 : f.eval₂ (Int.castRingHom ℝ) t =
      (f %ₘ q + q * (f /ₘ q)).eval₂ (Int.castRingHom ℝ) t := by rw [h1]
  rw [h3, eval₂_add, eval₂_mul, hq, zero_mul, add_zero]
  conv_lhs => rw [h2]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  simp

/-- The coefficient of x of the reduction is read from the values at the two roots. -/
lemma coeff_one_of_eval (f : ℤ[X]) (u v : ℤ)
    (h : ∀ t : ℝ, t ^ 2 = t + 1 → f.eval₂ (Int.castRingHom ℝ) t = (u : ℝ) * t + v) :
    (f %ₘ q).coeff 1 = u := by
  have key : ∀ t : ℝ, t ^ 2 = t + 1 →
      (((f %ₘ q).coeff 1 - u : ℤ) : ℝ) * t + (((f %ₘ q).coeff 0 - v : ℤ) : ℝ) = 0 := by
    intro t ht
    have e1 := eval_mod f t ht
    have e2 := h t ht
    push_cast
    linear_combination e2 - e1
  have hφ := key Real.goldenRatio Real.goldenRatio_sq
  have hψ := key Real.goldenConj Real.goldenConj_sq
  have hs : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    rw [Real.goldenRatio_sub_goldenConj]; positivity
  have h1 : (((f %ₘ q).coeff 1 - u : ℤ) : ℝ) = 0 := by
    have : (((f %ₘ q).coeff 1 - u : ℤ) : ℝ) * (Real.goldenRatio - Real.goldenConj) = 0 := by
      linear_combination hφ - hψ
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hs
  have h1' : (f %ₘ q).coeff 1 - u = 0 := by exact_mod_cast h1
  omega

lemma pow_root (t : ℝ) (ht : t ^ 2 = t + 1) (k : ℕ) :
    t ^ k = (Nat.fib k : ℝ) * t + ((Nat.fib (k + 1) : ℝ) - Nat.fib k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hf : (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [pow_succ, ih, hf]
    linear_combination (Nat.fib k : ℝ) * ht

lemma eval_p (t : ℝ) (ht : t ^ 2 = t + 1) (n : ℕ) :
    (p n).eval₂ (Int.castRingHom ℝ) t =
      ((∑ i ∈ Finset.Icc 1 (n + 1), (i : ℤ) ^ 2 * (Nat.fib (i - 1) : ℤ) : ℤ) : ℝ) * t +
      ((∑ i ∈ Finset.Icc 1 (n + 1),
        (i : ℤ) ^ 2 * ((Nat.fib i : ℤ) - (Nat.fib (i - 1) : ℤ)) : ℤ) : ℝ) := by
  induction n with
  | zero => simp [p]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 + 1 by omega),
      Finset.sum_Icc_succ_top (show 1 ≤ n + 1 + 1 by omega)]
    simp only [p, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, ih]
    simp only [eq_intCast]
    rw [pow_root t ht (n + 1)]
    have e : n + 1 + 1 - 1 = n + 1 := by omega
    rw [e]
    push_cast
    ring

end OMA.P_oeis_a192255

theorem OMA.solution : type_of% @OMA.S_oeis_a192255.main := by
  intro n
  show (OMA.S_oeis_a192255.p (n + 1 - 1) %ₘ OMA.P_oeis_a192255.q).coeff 1 = _
  rw [Nat.add_sub_cancel]
  exact OMA.P_oeis_a192255.coeff_one_of_eval _ _ _ (fun t ht => OMA.P_oeis_a192255.eval_p t ht n)
