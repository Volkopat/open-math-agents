import OMAStatements.S_oeis_a136746

-- Problem: A136746: G.f.: (z^12+1-z^11-z^10+z^8-z^6+z^5-z^3+z)/((z+1)*(z-1)^2).
-- Upstream: formal-conjectures statements/oeis-a136746.lean:0 (declaration OMA.S_oeis_a136746.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the set T = {1, 2, 3, 5, 6, 8, 12, 13, 14, 16, 17, 19, 23, 24, 25, 27, 28}
-- (the numbers in 1..28 whose residue mod 11 is 1, 2, 3, 5, 6 or 8) has 17 elements and no
-- 4-term arithmetic progression, so A003003(28) >= 17 (indeed A003003(28) = 17). If the g.f.
-- identity held, the coefficients of z^0, ..., z^27 would determine A003003(1), ..., A003003(28)
-- one after the other (the coefficient of z^m involves A003003(m+1), A003003(m), A003003(m-1)
-- and A003003(m-2)), and they give A003003(28) = 16, the coefficient of z^27 of the g.f.

namespace R02A136746

open OMA.S_oeis_a136746

def Tset : Finset ℕ := {1, 2, 3, 5, 6, 8, 12, 13, 14, 16, 17, 19, 23, 24, 25, 27, 28}


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
/-- No 4-term progression in T, with the difference bounded (a + 3d <= 28 forces d <= 9). -/
theorem key : ∀ a ∈ Tset,
    ∀ d ∈ Finset.range 10, 0 < d →
      a + d ∈ Tset →
      a + 2 * d ∈ Tset →
      a + 3 * d ∉ Tset := by
  decide

theorem bounds : ∀ x ∈ Tset,
    1 ≤ x ∧ x ≤ 28 := by
  decide

theorem noAP :
    ¬ HasAP4 Tset := by
  intro h
  unfold HasAP4 at h
  obtain ⟨a, d, hd, h0, h1, h2, h3⟩ := h
  have hb := (bounds _ h3).2
  exact key a h0 d (Finset.mem_range.mpr (by omega)) hd h1 h2 h3

theorem low : 17 ≤ A003003 28 := by
  have hsub : Tset ⊆
      Finset.Icc 1 28 := by
    intro x hx
    rw [Finset.mem_Icc]
    exact bounds x hx
  have hcard :
      Tset.card = 17 := by
    decide
  unfold A003003
  rw [← hcard]
  apply Finset.le_sup
  classical
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, noAP⟩

end R02A136746

open OMA.S_oeis_a136746 in
theorem OMA.solution : type_of% @OMA.S_oeis_a136746.main := by
  intro H
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℚ, ∀ n, r n = (A003003 (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
  have hmk : PowerSeries.mk (fun n => (A003003 (n + 1) : ℚ)) = PowerSeries.mk r :=
    PowerSeries.ext fun n => by rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, hr]
  have H1 : PowerSeries.mk r * ((PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2) =
      PowerSeries.X ^ 12 + 1 - PowerSeries.X ^ 11 - PowerSeries.X ^ 10 + PowerSeries.X ^ 8 -
        PowerSeries.X ^ 6 + PowerSeries.X ^ 5 - PowerSeries.X ^ 3 + PowerSeries.X := by
    rw [← hmk]
    exact H
  have e : PowerSeries.mk r * ((PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2) =
      PowerSeries.mk r * PowerSeries.X ^ 3 - PowerSeries.mk r * PowerSeries.X ^ 2
        - PowerSeries.mk r * PowerSeries.X ^ 1 + PowerSeries.mk r := by
    ring
  have e2 : (PowerSeries.X ^ 12 + 1 - PowerSeries.X ^ 11 - PowerSeries.X ^ 10 +
      PowerSeries.X ^ 8 - PowerSeries.X ^ 6 + PowerSeries.X ^ 5 - PowerSeries.X ^ 3 +
      PowerSeries.X : PowerSeries ℚ) =
      PowerSeries.X ^ 12 + PowerSeries.X ^ 0 - PowerSeries.X ^ 11 - PowerSeries.X ^ 10 +
        PowerSeries.X ^ 8 - PowerSeries.X ^ 6 + PowerSeries.X ^ 5 - PowerSeries.X ^ 3 +
        PowerSeries.X ^ 1 := by
    ring
  have E := PowerSeries.ext_iff.mp (e.symm.trans (H1.trans e2))
  have v0 : r 0 = 1 := by
    have h := E 0
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v1 : r 1 = 2 := by
    have h := E 1
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v2 : r 2 = 3 := by
    have h := E 2
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v3 : r 3 = 3 := by
    have h := E 3
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v4 : r 4 = 4 := by
    have h := E 4
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v5 : r 5 = 5 := by
    have h := E 5
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v6 : r 6 = 5 := by
    have h := E 6
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v7 : r 7 = 6 := by
    have h := E 7
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v8 : r 8 = 7 := by
    have h := E 8
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v9 : r 9 = 8 := by
    have h := E 9
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v10 : r 10 = 8 := by
    have h := E 10
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v11 : r 11 = 8 := by
    have h := E 11
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v12 : r 12 = 9 := by
    have h := E 12
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v13 : r 13 = 9 := by
    have h := E 13
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v14 : r 14 = 10 := by
    have h := E 14
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v15 : r 15 = 10 := by
    have h := E 15
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v16 : r 16 = 11 := by
    have h := E 16
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v17 : r 17 = 11 := by
    have h := E 17
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v18 : r 18 = 12 := by
    have h := E 18
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v19 : r 19 = 12 := by
    have h := E 19
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v20 : r 20 = 13 := by
    have h := E 20
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v21 : r 21 = 13 := by
    have h := E 21
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v22 : r 22 = 14 := by
    have h := E 22
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v23 : r 23 = 14 := by
    have h := E 23
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v24 : r 24 = 15 := by
    have h := E 24
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v25 : r 25 = 15 := by
    have h := E 25
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v26 : r 26 = 16 := by
    have h := E 26
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have v27 : r 27 = 16 := by
    have h := E 27
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow] at h
    norm_num at h
    linarith
  have h28 : (17 : ℚ) ≤ r 27 := by
    rw [hr, show (27 : ℕ) + 1 = 28 from rfl]
    exact_mod_cast R02A136746.low
  linarith
