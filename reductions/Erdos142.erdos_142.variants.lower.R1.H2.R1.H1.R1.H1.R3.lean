import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R3 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1
-- Credit: @jktcv2kz4f-cyber

/-!
# Amplified 4-AP density increment plus fixed-density 4-AP Szemeredi

We reduce the super-polylogarithmic 4-AP bound
`r 4 N <= N * exp(-c * (log (log N))^A)` (`A > 1`) to two independent theorems:

1. `H1` (amplified 4-AP density increment): every sparse 4-AP-free subset of `[1, N]`
   with sufficient double-logarithmic length budget admits an arithmetic subprogression
   on which the logarithmic density parameter `p = max 2 (log (2N / |S|))` contracts by
   a fixed factor `1 - eta` while losing at most `K * p ^ beta` (`0 < beta < 1`) in
   `log (log N)`.
2. `H2` (Szemeredi theorem for 4-term progressions): every subset of `[1, N]` of fixed
   positive density `delta > 0` contains a non-trivial 4-AP once `N` is large enough.

Setting the geometric-series potential constant `C = K / (1 - (1 - eta)^beta)` yields
`C * (1 - eta)^beta + K = C`, so each application of `H1` preserves the budget
`C * p^beta + R <= log (log N)` while dropping `p` by at least `2 * eta`. Strong
induction eliminates every budget-satisfying 4-AP-free set once `R` exceeds the
threshold from `H2` at density `2 * exp(-T)`. Inverting the failure of the budget on
an extremizer yields exponent `A = 1 / beta > 1`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3

open Erdos142 Filter Real
open scoped Topology

/-- Amplified 4-AP density increment: a sparse 4-AP-free subset of `[1, N]` with
sufficient double-logarithmic length budget admits a subprogression on which the
logarithmic density parameter `p = max 2 (log (2N / |S|))` contracts by a fixed
factor `1 - eta` while losing at most `K * p ^ beta` in `log (log N)`. -/
def H1 : Prop :=
  ∃ (β η K T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < η ∧ η < 1 ∧ 0 < K ∧
    ∀ (N : ℕ) (S : Finset ℕ),
      2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → K * p ^ β + R₀ ≤ Real.log (Real.log (N : ℝ)) →
      ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        0 < U.card ∧ p' ≤ (1 - η) * p ∧
          Real.log (Real.log (N : ℝ)) - K * p ^ β ≤ Real.log (Real.log (M : ℝ))

/-- Fixed-density Szemeredi theorem for 4-term arithmetic progressions:
every subset of `[1, N]` of density at least `delta > 0` contains a 4-AP once `N` is
sufficiently large. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ (N : ℕ) (S : Finset ℕ),
    N₀ ≤ N → S ⊆ Finset.Icc 1 N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S

lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have h : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) h

lemma nat_lt_of_loglog_lt {M N : ℕ} (hM : 3 ≤ M) (hN : 2 ≤ N)
    (h : Real.log (Real.log (M : ℝ)) < Real.log (Real.log (N : ℝ))) : M < N := by
  have hM3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogM : 1 < Real.log (M : ℝ) :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hM3)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hloglt : Real.log (M : ℝ) < Real.log (N : ℝ) :=
    (Real.log_lt_log_iff (by linarith) hlogN).mp h
  have hlt : (M : ℝ) < (N : ℝ) :=
    (Real.log_lt_log_iff (by linarith) (by linarith)).mp hloglt
  exact_mod_cast hlt

lemma no_budget_four (hinc : H1) (hszem : H2) :
    ∃ (β C R : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
        ¬ C * (max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))) ^ β + R ≤
          Real.log (Real.log (N : ℝ)) := by
  obtain ⟨β, η, K, T, R₀, hβ0, hβ1, hη0, hη1, hK, hstep⟩ := hinc
  obtain ⟨N₀, hN₀⟩ := hszem (2 * Real.exp (-T)) (by positivity)
  let θ : ℝ := (1 - η) ^ β
  have h1η0 : 0 < 1 - η := by linarith
  have h1η1 : 1 - η < 1 := by linarith
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos h1η0 β
  have hθ1 : θ < 1 := Real.rpow_lt_one h1η0.le h1η1 hβ0
  have h1θ0 : 0 < 1 - θ := by linarith
  let C : ℝ := K / (1 - θ)
  have hC0 : 0 < C := div_pos hK h1θ0
  have hKC : K ≤ C := by
    rw [show C = K / (1 - θ) from rfl, le_div_iff₀ h1θ0]
    nlinarith
  have htel : C * θ + K = C := by
    dsimp [C]
    field_simp [h1θ0.ne']
    ring
  let M₀ : ℕ := max 3 N₀
  let R : ℝ := max R₀ (Real.log (Real.log (M₀ : ℝ)) + 1)
  have hR₀R : R₀ ≤ R := le_max_left _ _
  have hRM₀ : Real.log (Real.log (M₀ : ℝ)) < R := by
    have := le_max_right R₀ (Real.log (Real.log (M₀ : ℝ)) + 1)
    linarith
  refine ⟨β, C, R, hβ0, hβ1, hC0, ?_⟩
  let P : (ℕ × Finset ℕ) → Prop := fun x ↦
    2 ≤ x.1 ∧ x.2 ⊆ Finset.Icc 1 x.1 ∧ 0 < x.2.card ∧
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ x.2) ∧
      C * (max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ)))) ^ β + R ≤
        Real.log (Real.log (x.1 : ℝ))
  let pot : (ℕ × Finset ℕ) → ℝ := fun x ↦
    max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ))) / (2 * η)
  have hno : ∀ x, ¬ P x := by
    apply OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.eliminate_descent pot P
    · intro x
      have hp2 : (2 : ℝ) ≤ max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ))) := le_max_left _ _
      exact div_nonneg (by linarith) (by positivity)
    · rintro ⟨N, S⟩ ⟨hN, hS, hcard, hfree, hbud⟩
      set p : ℝ := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) with hpdef
      have hp2 : (2 : ℝ) ≤ p := le_max_left _ _
      have hp0 : 0 < p := by linarith
      have hpβ0 : 0 ≤ p ^ β := Real.rpow_nonneg hp0.le β
      by_cases hT : T < p
      · have hKbud : K * p ^ β + R₀ ≤ Real.log (Real.log (N : ℝ)) := by
          have : K * p ^ β ≤ C * p ^ β := mul_le_mul_of_nonneg_right hKC hpβ0
          linarith
        obtain ⟨a, q, M, hq, hM, hP, hUcard, hp', hloss⟩ :=
          hstep N S hN hS hcard hfree hT hKbud
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        set p' : ℝ := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ))) with hp'def
        have hp'2 : (2 : ℝ) ≤ p' := le_max_left _ _
        have hp'0 : 0 ≤ p' := by linarith
        have hUsub : U ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
        have hUfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < 4, b + i * d ∈ U :=
          OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.progression_preimage_free
            le_rfl hq hfree
        have hp'β : p' ^ β ≤ θ * p ^ β := by
          calc p' ^ β ≤ ((1 - η) * p) ^ β := Real.rpow_le_rpow hp'0 hp' hβ0.le
            _ = θ * p ^ β := Real.mul_rpow h1η0.le hp0.le
        have hMbud : C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ)) := by
          have h1 : C * p' ^ β ≤ C * θ * p ^ β := by
            have := mul_le_mul_of_nonneg_left hp'β hC0.le
            linarith
          have h2 : C * θ * p ^ β + K * p ^ β = C * p ^ β := by
            calc C * θ * p ^ β + K * p ^ β = (C * θ + K) * p ^ β := by ring
              _ = C * p ^ β := by rw [htel]
          linarith
        have hdrop : pot (M, U) + 1 ≤ pot (N, S) := by
          change p' / (2 * η) + 1 ≤ p / (2 * η)
          have h2η : 0 < 2 * η := by positivity
          rw [show p' / (2 * η) + 1 = (p' + 2 * η) / (2 * η) by field_simp [h2η.ne']]
          exact div_le_div_of_nonneg_right (by nlinarith) h2η.le
        exact ⟨(M, U), ⟨hM, hUsub, hUcard, hUfree, hMbud⟩, hdrop⟩
      · exfalso
        have hpT : p ≤ T := not_lt.mp hT
        have hlogle : Real.log (2 * (N : ℝ) / (S.card : ℝ)) ≤ T :=
          (le_max_right _ _).trans hpT
        have hNpos : 0 < (N : ℝ) := by
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hcard
        have hfracpos : 0 < 2 * (N : ℝ) / (S.card : ℝ) := by positivity
        have hexp : 2 * (N : ℝ) / (S.card : ℝ) ≤ Real.exp T := by
          have := Real.exp_le_exp.mpr hlogle
          rwa [Real.exp_log hfracpos] at this
        have hdens : 2 * Real.exp (-T) * (N : ℝ) ≤ (S.card : ℝ) := by
          have hmul := (div_le_iff₀ hSpos).mp hexp
          have hpos : 0 ≤ Real.exp (-T) := (Real.exp_pos (-T)).le
          have h1 := mul_le_mul_of_nonneg_left hmul hpos
          have h2 : Real.exp (-T) * Real.exp T = 1 := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          have h3 : Real.exp (-T) * (Real.exp T * (S.card : ℝ)) = (S.card : ℝ) := by
            rw [← mul_assoc, h2, one_mul]
          linarith
        have hCp0 : 0 ≤ C * p ^ β := mul_nonneg hC0.le hpβ0
        have hloglt : Real.log (Real.log (M₀ : ℝ)) < Real.log (Real.log (N : ℝ)) := by linarith
        have hMN : M₀ < N := nat_lt_of_loglog_lt (le_max_left 3 N₀) hN hloglt
        have hN₀N : N₀ ≤ N := le_trans (le_max_right 3 N₀) hMN.le
        exact hfree (hN₀ N S hN₀N hS hdens)
  intro N S hN hS hcard hfree hbud
  exact hno (N, S) ⟨hN, hS, hcard, hfree, hbud⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H1 := by
  intro hinc hszem
  obtain ⟨β, C, R, hβ0, hβ1, hC0, hnobud⟩ := no_budget_four hinc hszem
  let A : ℝ := 1 / β
  have hA1 : 1 < A := by
    dsimp [A]
    rw [one_lt_div hβ0]
    exact hβ1
  have hA0 : 0 < A := by linarith
  have hβA : β * A = 1 := by
    dsimp [A]
    field_simp [hβ0.ne']
  let c₁ : ℝ := (2 * C)⁻¹ ^ A
  have hc₁0 : 0 < c₁ := Real.rpow_pos_of_pos (by positivity) A
  let c : ℝ := c₁ / 2
  have hc0 : 0 < c := by positivity
  refine ⟨A, c, hA1, hc0, ?_⟩
  have hll : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpow : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ)) ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA0).comp hll
  have hthresh : ∀ᶠ N : ℕ in atTop,
      max (max 1 (2 * R)) (4 * C * (2 : ℝ) ^ β) < Real.log (Real.log (N : ℝ)) :=
    hll.eventually_gt_atTop _
  have habsorb : ∀ᶠ N : ℕ in atTop, Real.log 2 / c ≤ Real.log (Real.log (N : ℝ)) ^ A :=
    hpow.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 : ℕ), hthresh, habsorb] with N hN hbig hlog2
  obtain ⟨S, hS, hfree, hcard⟩ :=
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.extremizer (by decide : 1 < 4) N
  rw [← hcard]
  by_cases hzero : S.card = 0
  · rw [hzero, Nat.cast_zero]
    positivity
  have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
  have hno4 : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S :=
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.no_positive_step (by decide : 1 < 4) hfree
  set x : ℝ := Real.log (Real.log (N : ℝ)) with hxdef
  set p : ℝ := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) with hpdef
  have hx1 : 1 < x := lt_of_le_of_lt ((le_max_left 1 (2 * R)).trans (le_max_left _ _)) hbig
  have hx2R : 2 * R < x := lt_of_le_of_lt ((le_max_right 1 (2 * R)).trans (le_max_left _ _)) hbig
  have hx4C : 4 * C * (2 : ℝ) ^ β < x := lt_of_le_of_lt (le_max_right _ _) hbig
  have hfail : x < C * p ^ β + R := lt_of_not_ge (hnobud N S hN hS hpos hno4)
  have hhalf : x / (2 * C) < p ^ β := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * C)]
    linarith
  have h2ltpβ : (2 : ℝ) ^ β < p ^ β := by
    have : (2 : ℝ) ^ β < x / (2 * C) := by
      rw [lt_div_iff₀ (by positivity : 0 < 2 * C)]
      linarith
    exact this.trans hhalf
  have hp2lt : (2 : ℝ) < p := by
    by_contra hle
    have hp2 : p ≤ 2 := not_lt.mp hle
    have hp0 : 0 ≤ p := le_trans (by norm_num) (le_max_left 2 _)
    exact not_lt_of_ge (Real.rpow_le_rpow hp0 hp2 hβ0.le) h2ltpβ
  have hpeq : p = Real.log (2 * (N : ℝ) / (S.card : ℝ)) := by
    rcases max_choice 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) with h | h
    · exfalso; linarith
    · exact h
  have hpowp : c₁ * x ^ A ≤ p := by
    have hxC0 : 0 ≤ x / (2 * C) := by positivity
    have h1 := Real.rpow_le_rpow hxC0 hhalf.le hA0.le
    have h2 : (p ^ β) ^ A = p := by
      rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ p), hβA, Real.rpow_one]
    have h3 : (x / (2 * C)) ^ A = c₁ * x ^ A := by
      rw [div_eq_mul_inv, mul_comm x (2 * C)⁻¹, Real.mul_rpow (by positivity) (by linarith)]
    linarith
  have hlog2' : Real.log 2 ≤ c * x ^ A := by
    have := (div_le_iff₀ hc0).mp hlog2
    linarith
  have hlogbound : Real.log 2 + c * x ^ A ≤ Real.log (2 * (N : ℝ) / (S.card : ℝ)) := by
    rw [← hpeq]
    have h2c : c₁ = 2 * c := by dsimp [c]; ring
    rw [h2c] at hpowp
    linarith
  have hNpos : 0 < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hpos
  have hexp : 2 * Real.exp (c * x ^ A) ≤ 2 * (N : ℝ) / (S.card : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hlogbound
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by positivity : 0 < 2 * (N : ℝ) / (S.card : ℝ))] at h1
    exact h1
  have hmul : (S.card : ℝ) * Real.exp (c * x ^ A) ≤ (N : ℝ) := by
    have h1 := (le_div_iff₀ hSpos).mp hexp
    nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hmul (Real.exp_pos (-c * x ^ A)).le
  have hcancel : Real.exp (c * x ^ A) * Real.exp (-c * x ^ A) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  calc (S.card : ℝ) = (S.card : ℝ) * (Real.exp (c * x ^ A) * Real.exp (-c * x ^ A)) := by
        rw [hcancel, mul_one]
    _ = (S.card : ℝ) * Real.exp (c * x ^ A) * Real.exp (-c * x ^ A) := by ring
    _ ≤ (N : ℝ) * Real.exp (-c * x ^ A) := hfinal

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3
