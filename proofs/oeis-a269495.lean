import OMAStatements.S_oeis_a269495

-- Problem: A269495: Number of length-4 0..n arrays with no repeated value differing from the previous repeated value by one.
-- Upstream: formal-conjectures statements/oeis-a269495.lean:0 (declaration OMA.S_oeis_a269495.main)
-- Credit: @minimumnz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
namespace OMA.P269495
open OMA.S_oeis_a269495

theorem inj (n : ℕ) : Function.Injective (prohibited n) := by
  rintro ⟨b1, j1⟩ ⟨b2, j2⟩ h
  cases b1 <;> cases b2 <;>
    simp only [prohibited, Bool.false_eq_true, if_false, if_true, Prod.mk.injEq] at h
  · obtain ⟨h1, -⟩ := h
    rw [Fin.castSucc_inj] at h1
    rw [h1]
  · exfalso
    obtain ⟨h1, -, h3, -⟩ := h
    have e1 := congrArg Fin.val h1
    have e3 := congrArg Fin.val h3
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e3
    omega
  · exfalso
    obtain ⟨h1, -, h3, -⟩ := h
    have e1 := congrArg Fin.val h1
    have e3 := congrArg Fin.val h3
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e3
    omega
  · obtain ⟨h1, -⟩ := h
    rw [Fin.succ_inj] at h1
    rw [h1]

theorem count_eq (n : ℕ) : count n = (n + 1) ^ 4 - 2 * n := by
  unfold count
  rw [Finset.card_univ_sdiff, Finset.card_image_of_injective _ (inj n)]
  simp only [Word, Fintype.card_prod, Fintype.card_fin, Finset.card_univ, Fintype.card_bool]
  congr 1
  ring

theorem terms_eq (n : ℕ) : terms (n + 1) = ((n : ℤ) + 2) ^ 4 - 2 * (n + 1) := by
  show ((count (n + 1) : ℕ) : ℤ) = _
  rw [count_eq]
  have h : 2 * (n + 1) ≤ (n + 1 + 1) ^ 4 := by
    have : (n + 1 + 1) ^ 4 = 2 * (n + 1) + (n ^ 4 + 8 * n ^ 3 + 24 * n ^ 2 + 30 * n + 14) := by ring
    omega
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem rec (n : ℕ) : terms (n + 6) = 5 * terms (n + 5) - 10 * terms (n + 4) +
    10 * terms (n + 3) - 5 * terms (n + 2) + terms (n + 1) := by
  rw [terms_eq (n + 5), terms_eq (n + 4), terms_eq (n + 3), terms_eq (n + 2), terms_eq (n + 1),
    terms_eq n]
  push_cast
  ring

end OMA.P269495

theorem OMA.solution : type_of% @OMA.S_oeis_a269495.main := by
  refine ⟨OMA.P269495.terms_eq, OMA.P269495.rec, ?_⟩
  have T0 : OMA.S_oeis_a269495.terms 0 = 0 := rfl
  have T1 : OMA.S_oeis_a269495.terms 1 = 14 := by rw [OMA.P269495.terms_eq 0]; norm_num
  have T2 : OMA.S_oeis_a269495.terms 2 = 77 := by rw [OMA.P269495.terms_eq 1]; norm_num
  have T3 : OMA.S_oeis_a269495.terms 3 = 250 := by rw [OMA.P269495.terms_eq 2]; norm_num
  have T4 : OMA.S_oeis_a269495.terms 4 = 617 := by rw [OMA.P269495.terms_eq 3]; norm_num
  have T5 : OMA.S_oeis_a269495.terms 5 = 1286 := by rw [OMA.P269495.terms_eq 4]; norm_num
  have hD : ((1 - PowerSeries.X) ^ 5 : PowerSeries ℤ)
      = PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 0 + PowerSeries.C (-5 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (10 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (-10 : ℤ) * PowerSeries.X ^ 3 + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 4 + PowerSeries.C (-1 : ℤ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat, map_neg, map_one, map_zero]; ring
  have hNum : ((PowerSeries.X * (14 + 7 * PowerSeries.X + 5 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4)) : PowerSeries ℤ)
      = PowerSeries.C (0 : ℤ) * PowerSeries.X ^ 0 + PowerSeries.C (14 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (7 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 3 + PowerSeries.C (-3 : ℤ) * PowerSeries.X ^ 4 + PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat, map_neg, map_one, map_zero]; ring
  have key : ∀ F : PowerSeries ℤ, (PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 0 + PowerSeries.C (-5 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (10 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (-10 : ℤ) * PowerSeries.X ^ 3 + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 4 + PowerSeries.C (-1 : ℤ) * PowerSeries.X ^ 5) * F
      = PowerSeries.C (1 : ℤ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-5 : ℤ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (10 : ℤ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (-10 : ℤ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (5 : ℤ) * (F * PowerSeries.X ^ 4) + PowerSeries.C (-1 : ℤ) * (F * PowerSeries.X ^ 5) := by
    intro F; ring
  rw [hD, hNum, key]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
    PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases n with _ | _ | _ | _ | _ | _ | m
  · norm_num [T0]
  · norm_num [T0, T1]
  · norm_num [T0, T1, T2]
  · norm_num [T0, T1, T2, T3]
  · norm_num [T0, T1, T2, T3, T4]
  · norm_num [T0, T1, T2, T3, T4, T5]
  · rw [show m + 1 + 1 + 1 + 1 + 1 + 1 = m + 6 from rfl]
    have h := OMA.P269495.rec m
    simp only [show 0 ≤ m + 6 from by omega,
      show m + 6 - 0 = m + 6 from rfl,
      show 1 ≤ m + 6 from by omega,
      show m + 6 - 1 = m + 5 from rfl,
      show 2 ≤ m + 6 from by omega,
      show m + 6 - 2 = m + 4 from rfl,
      show 3 ≤ m + 6 from by omega,
      show m + 6 - 3 = m + 3 from rfl,
      show 4 ≤ m + 6 from by omega,
      show m + 6 - 4 = m + 2 from rfl,
      show 5 ≤ m + 6 from by omega,
      show m + 6 - 5 = m + 1 from rfl,
      show ¬ (m + 6 = 0) from by omega,
      show ¬ (m + 5 = 0) from by omega,
      show ¬ (m + 4 = 0) from by omega,
      show ¬ (m + 3 = 0) from by omega,
      show ¬ (m + 2 = 0) from by omega,
      show ¬ (m + 1 = 0) from by omega,
      if_true, if_false]
    rw [h]
    ring
