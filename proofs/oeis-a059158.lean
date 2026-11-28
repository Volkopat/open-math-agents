import OMAStatements.S_oeis_a059158

-- Problem: A059158 hierarchical sequence S(W'3{2,2}cc): closed form, recurrence and g.f.
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)

open PowerSeries

namespace OMA.A059158

open OMA.S_oeis_a059158

lemma split (g : ℕ → ℤ) (N : ℕ) : ∑ k ∈ Finset.range (2 * N + 1), g (k + 1) =
    ∑ j ∈ Finset.range (N + 1), g (2 * j + 1) + ∑ j ∈ Finset.range N, g (2 * j + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ _ (N + 1),
      Finset.sum_range_succ (fun j => g (2 * j + 2)) N]
    ring_nf

lemma key (m : ℕ) : 14 * ∑ k ∈ Finset.range (2 ^ m - 1), (16 : ℤ) ^ padicValNat 2 (k + 1) =
    2 ^ m * 8 ^ m - 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [show 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 by rw [pow_succ]; omega,
      split (fun i => (16 : ℤ) ^ padicValNat 2 i),
      Finset.sum_congr rfl (fun j _ => show (16 : ℤ) ^ padicValNat 2 (2 * j + 1) = 1 by
        simp [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * j + 1)]),
      Finset.sum_congr rfl (fun j _ => show (16 : ℤ) ^ padicValNat 2 (2 * j + 2) =
        16 * 16 ^ padicValNat 2 (j + 1) by
          rw [show 2 * j + 2 = 2 * (j + 1) by ring, padicValNat.mul (by norm_num) (by omega)]
          simp; ring), ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub h1]
    linear_combination 16 * ih

lemma closedQ (n : ℕ) : (a n : ℚ) = 24 / 7 * (8 * 16 ^ n - 2 ^ n) := by
  have hc : ∀ k, collapsed2 (k + 1) = 24 * 16 ^ padicValNat 2 (k + 1) := fun k => by
    simp [collapsed2, element', element, ruler, pow_add, pow_mul]; ring
  have h : ((14 * ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), (16 : ℤ) ^ padicValNat 2 (k + 1) : ℤ) : ℚ) =
      ((2 ^ (n + 1) * 8 ^ (n + 1) - 2 ^ (n + 1) : ℤ) : ℚ) := by rw [key]
  unfold a
  rw [Finset.sum_congr rfl (fun k _ => hc k), ← Finset.mul_sum]
  push_cast at h ⊢
  rw [show (16 : ℚ) ^ n = 2 ^ n * 8 ^ n by rw [← mul_pow]; norm_num]
  linear_combination (12 / 7 : ℚ) * h

end OMA.A059158

open OMA.S_oeis_a059158 OMA.A059158 in
theorem OMA.solution : type_of% @OMA.S_oeis_a059158.main := by
  refine ⟨closedQ, fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    have hq : (a (k + 2) : ℚ) = 18 * a (k + 1) - 32 * a k := by
      rw [closedQ, closedQ, closedQ]; ring
    exact_mod_cast hq
  · have e1 : ∀ f : PowerSeries ℚ, f * ((2 * X - 1) * (16 * X - 1)) =
        C 32 * (X * (X * f)) - C 18 * (X * f) + f := fun f => by
      simp only [map_ofNat]; ring
    rw [e1, show (24 : PowerSeries ℚ) = C 24 by simp only [map_ofNat]]
    ext n
    rcases n with _ | _ | k <;> simp [closedQ, coeff_C] <;> ring
