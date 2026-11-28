import OMAStatements.S_oeis_a059142

-- Problem: A059142 hierarchical sequence S(W2{3}*): closed form, recurrence and g.f.
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)

open PowerSeries

namespace OMA.A059142

open OMA.S_oeis_a059142

lemma sum_v (N : ℕ) : ∑ k ∈ Finset.range N, padicValNat 2 (k + 1) = padicValNat 2 N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _), add_comm]

lemma digits_sum (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := Nat.one_le_two_pow (n := m)
    rw [show 2 ^ (m + 1) - 1 = 1 + 2 * (2 ^ m - 1) by rw [pow_succ]; omega,
      Nat.digits_add 2 (by norm_num) 1 _ (by norm_num) (Or.inl one_ne_zero), List.sum_cons, ih,
      add_comm]

lemma key (m : ℕ) : (∑ k ∈ Finset.range (2 ^ m - 1), padicValNat 2 (k + 1) : ℤ) = 2 ^ m - 1 - m := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ m - 1)
  rw [digits_sum, show 2 - 1 = 1 from rfl, one_mul] at h
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [← Nat.cast_sum, sum_v, h]
  push_cast [Nat.cast_sub h1, Nat.cast_sub (by omega : m ≤ 2 ^ m - 1)]
  ring

lemma closed (n : ℕ) : (a n : ℤ) = -25 + 9 * 2 ^ (2 + n) - 7 * n := by
  have hc : ∀ k, ((phrase (k + 1)).sum : ℤ) = 7 * padicValNat 2 (k + 1) + 11 := fun k => by
    simp [phrase, ruler]; ring
  have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  unfold a
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_add_distrib, ← Finset.mul_sum, key]
  simp [Nat.cast_sub h1]
  ring

lemma closedQ (n : ℕ) : (a n : ℚ) = -25 + 9 * 2 ^ (2 + n) - 7 * n := by
  exact_mod_cast closed n

end OMA.A059142

open OMA.A059142 in
theorem OMA.solution : type_of% @OMA.S_oeis_a059142.main := by
  refine ⟨fun n hn => ?_, closed, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
      show k + 3 - 3 = k by omega, closed]
    push_cast; ring
  · have e1 : ∀ f : PowerSeries ℚ, f * ((X - 1) ^ 2 * (2 * X - 1)) =
        C 2 * (X * (X * (X * f))) - C 5 * (X * (X * f)) + C 4 * (X * f) - f := fun f => by
      simp only [map_ofNat]; ring
    rw [e1, show (4 * X - 11 : PowerSeries ℚ) = C 4 * X - C 11 by simp only [map_ofNat]]
    ext n
    rcases n with _ | _ | _ | k <;> simp [closedQ, coeff_X] <;> ring
