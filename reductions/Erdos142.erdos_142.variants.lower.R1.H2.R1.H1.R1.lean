import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1
-- Credit: @TomsBack

/-!
# A super-polylogarithmic saving makes the density-increment step vacuous

If r k N ≤ N exp(-c (log log N)^A) with A > 1, the premise of step
lower.R1.H2.R1.H1 cannot hold once R is large: the budget C p^β + R ≤ log log N
fails because p ≥ c (log log N)^A and Aβ ≥ 1 for β = (1 + 1/A)/2 < 1.
Leng-Sah-Sawhney proved this bound shape with an exponent below one, so the step
sits exactly at pushing that exponent past one. These hypotheses also give
lower.R1.H2 directly; the value is in locating the step.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1

open Erdos142 Filter Real
open scoped Topology

/-- A super-polylogarithmic saving for 4-term progressions: Leng-Sah-Sawhney shape with exponent above one. -/
def H1 : Prop :=
  ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    (r 4 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)

/-- The same saving for every progression length at least five. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)

/-- A set with no k-term progression of positive step is k-AP-free in the library sense. -/
lemma free_of_no_step {A : Set ℕ} {k : ℕ} (hk : 1 < k)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A) : A.IsAPOfLengthFree k := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  intro T hsub hT
  obtain ⟨a, d, hcard, hterms⟩ := hT
  have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
    rw [hterms]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hd : 0 < d := by
    by_contra! h
    have he : d = 0 := Nat.eq_zero_of_le_zero h
    have hs : T = {a} := by
      apply Set.Subset.antisymm
      · rw [hterms, he]
        rintro _ ⟨i, -, rfl⟩
        simp
      · apply Set.singleton_subset_iff.mpr
        simpa using hmem 0 (by omega)
    rw [hs] at hcard
    exact hk'.ne (by simpa using hcard)
  exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hS, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

/-- log log N stays below N. -/
lemma loglog_lt_self {N : ℕ} (hN : 2 ≤ N) : Real.log (Real.log (N : ℝ)) < (N : ℝ) := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
  linarith

/-- A super-polylog saving for one length makes the density-increment premise vacuous. -/
theorem step_of_superpolylog (k : ℕ) (hk : 4 ≤ k) (A c : ℝ) (hA : 1 < A) (hc : 0 < c)
    (hb : ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)) :
    ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
        2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
          (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
          ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
            (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
            let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
            let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
            0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ)) := by
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hb
  have hA0 : 0 < A := by linarith
  have hinv0 : 0 < 1 / A := by positivity
  have hinv1 : 1 / A < 1 := by rw [div_lt_one hA0]; exact hA
  set β : ℝ := (1 + 1 / A) / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hAβ : 1 ≤ A * β := by
    have : A * β = (A + 1) / 2 := by
      rw [hβdef]; field_simp
    rw [this]; linarith
  have hcβ : 0 < c ^ β := Real.rpow_pos_of_pos hc β
  refine ⟨β, 2 / c ^ β, 0, max 1 (N1 : ℝ), hβ0, hβ1, by positivity, ?_⟩
  intro R hR N S hN hS hcard hfree p hT hbud
  exfalso
  set x : ℝ := Real.log (Real.log (N : ℝ)) with hxdef
  have hp2 : (2 : ℝ) ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hCp : 0 ≤ 2 / c ^ β * p ^ β := by
    have := Real.rpow_nonneg hp0.le β
    positivity
  have hxR : R ≤ x := by linarith
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) (hR.trans hxR)
  have hxN1 : (N1 : ℝ) ≤ x := le_trans (le_max_right _ _) (hR.trans hxR)
  have hNN1 : N1 ≤ N := by
    have := loglog_lt_self hN
    have : (N1 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hbound := hN1 N hNN1
  have hcardr : (S.card : ℝ) ≤ (r k N : ℝ) :=
    by exact_mod_cast card_le_r hS (free_of_no_step (by omega) hfree)
  set y : ℝ := c * x ^ A with hydef
  have hy0 : 0 ≤ y := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) A
    positivity
  have hScard : 0 < (S.card : ℝ) := by exact_mod_cast hcard
  have hNpos : 0 < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hexp : Real.exp y ≤ 2 * (N : ℝ) / (S.card : ℝ) := by
    rw [le_div_iff₀ hScard]
    have h1 : (S.card : ℝ) ≤ (N : ℝ) * Real.exp (-y) := by
      have : -c * x ^ A = -y := by rw [hydef]; ring
      rw [← this]; linarith
    have h2 : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : Real.exp y * (S.card : ℝ) ≤ Real.exp y * ((N : ℝ) * Real.exp (-y)) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos y).le
    have h4 : Real.exp y * ((N : ℝ) * Real.exp (-y)) = (N : ℝ) := by
      rw [mul_comm (N : ℝ), ← mul_assoc, h2, one_mul]
    linarith
  have hyp : y ≤ p := by
    have := Real.log_le_log (Real.exp_pos y) hexp
    rw [Real.log_exp] at this
    exact this.trans (le_max_right _ _)
  have hpow : y ^ β ≤ p ^ β := Real.rpow_le_rpow hy0 hyp hβ0.le
  have hyβ : y ^ β = c ^ β * x ^ (A * β) := by
    rw [hydef, Real.mul_rpow hc.le (Real.rpow_nonneg (by linarith) A),
      ← Real.rpow_mul (by linarith)]
  have hxpow : x ≤ x ^ (A * β) := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hAβ
    rwa [Real.rpow_one] at this
  have hkey : 2 * x ≤ 2 / c ^ β * p ^ β := by
    have e : 2 / c ^ β * (c ^ β * x ^ (A * β)) = 2 * x ^ (A * β) := by
      field_simp
    have := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 2 / c ^ β by positivity)
    rw [hyβ, e] at this
    linarith
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.H1 := by
  intro h4 h5 k hk
  rcases eq_or_lt_of_le hk with rfl | hlt
  · obtain ⟨A, c, hA, hc, hb⟩ := h4
    exact step_of_superpolylog 4 le_rfl A c hA hc hb
  · obtain ⟨A, c, hA, hc, hb⟩ := h5 k hlt
    exact step_of_superpolylog k hk A c hA hc hb

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1
