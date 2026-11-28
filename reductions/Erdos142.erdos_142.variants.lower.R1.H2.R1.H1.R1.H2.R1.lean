import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H2.R1 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H2
-- Credit: @PianothShaveck

/-!
# Iteration at exponential density thresholds

At density exp(-(j+1)), one increment takes us to density exp(-j).
The allowed log-log length loss is the discrete difference of C j^β.
Thus a descent from level n to any fixed level J costs at most C n^β,
and fixed-density Szemerédi rules out the terminal set. Rounding the initial
level up gives a stretched-exponential bound for every 1 < A < 1/β.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R1

open Erdos142 Filter Real

/-- Above a fixed level, an AP-free set gains a factor e in density on a
progression, with a length loss charged to the difference of consecutive powers. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ (β C B : ℝ) (J : ℕ), 0 < β ∧ β < 1 ∧ 0 < C ∧
    ∀ j : ℕ, J ≤ j → ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S) →
      (N : ℝ) * exp (-((j+1 : ℕ) : ℝ)) ≤ S.card →
      C * ((j+1 : ℕ) : ℝ) ^ β + B ≤ log (log N) →
      ∃ a q M : ℕ, 0 < q ∧ 0 < M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i-1)*q ∈ Finset.Icc 1 N) ∧
        (M : ℝ) * exp (-(j : ℝ)) ≤
          ((Finset.Icc 1 M).filter fun i ↦ a + (i-1)*q ∈ S).card ∧
        log (log (N : ℝ)) - log (log (M : ℝ)) ≤
          C * (((j+1 : ℕ) : ℝ) ^ β - (j : ℝ) ^ β)

/-- Qualitative Szemerédi at each fixed exponential density threshold. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∀ J : ℕ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    0 < N → Q ≤ log (log (N : ℝ)) → S ⊆ Finset.Icc 1 N →
    (N : ℝ) * exp (-(J : ℝ)) ≤ S.card →
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S

/-- The length costs telescope from the starting density level down to J. -/
theorem iterate_levels (hs : H1) (ht : H2) {k : ℕ} (hk : 5 ≤ k) :
    ∃ (β C R : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ j N : ℕ, 0 < N → C * (j : ℝ)^β + R ≤ log (log (N : ℝ)) →
      (r k N : ℝ) ≤ N * exp (-(j : ℝ)) := by
  obtain ⟨β,C,B,J,hβ,hβ1,hC,step⟩ := hs k hk
  obtain ⟨Q,terminal⟩ := ht k hk J
  let R := max B Q
  refine ⟨β,C,R,hβ,hβ1,hC,?_⟩
  have aux (j : ℕ) : ∀ (N : ℕ) (S : Finset ℕ), 0 < N →
      C * (j : ℝ)^β + R ≤ log (log (N : ℝ)) → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S) →
      ¬ (N : ℝ) * exp (-(j : ℝ)) ≤ S.card := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro N S hN hlen hS hf hdens
      by_cases hj : j ≤ J
      · have hp : 0 ≤ C * (j : ℝ)^β := by positivity
        have hQ : Q ≤ R := le_max_right _ _
        apply hf (terminal N S hN (by linarith) hS ?_)
        refine le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (Nat.cast_nonneg N)) hdens
        exact neg_le_neg (by exact_mod_cast hj)
      · obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
        have hB : B ≤ R := le_max_left _ _
        obtain ⟨a,q,M,hq,hM,_,hd,hl⟩ := step i (by omega) N S hS hf hdens (by linarith)
        apply ih i (by omega) M _ hM _ (Finset.filter_subset _ _)
          (OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.progression_preimage_free (by omega) hq hf) hd
        linarith only [hlen,hl]
  intro j N hN hlen
  obtain ⟨S,hS,hf,hcard⟩ := OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.extremizer (by omega : 1 < k) N
  rw [← hcard]
  exact le_of_lt (lt_of_not_ge (aux j N S hN hlen hS
    (OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.no_positive_step (by omega) hf)))

/-- Invert the length budget, including the integer rounding of the density level. -/
lemma rounded_budget {β A : ℝ} (hβ : 0 < β) (hA : 0 < A) (hab : A*β < 1)
    (C R : ℝ) (hC : 0 < C) : ∀ᶠ t : ℝ in atTop,
    C * (⌈t ^ A⌉₊ : ℝ)^β + R ≤ t := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.eventually_budget (A*β) (C * (2 : ℝ)^β) R hab] with t ht h
  have ht0 : 0 ≤ t := by linarith
  have hx : 1 ≤ t^A := Real.one_le_rpow ht hA.le
  have hceil : (⌈t^A⌉₊ : ℝ) ≤ 2 * t^A := by
    linarith [Nat.ceil_lt_add_one (Real.rpow_nonneg ht0 A)]
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hβ.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg ht0 A),
    ← Real.rpow_mul ht0] at hp
  have hmono := Real.rpow_le_rpow ht0 (by linarith : t ≤ 4*t) (mul_pos hA hβ).le
  calc
    _ ≤ C * (2^β * t^(A*β)) + R := by gcongr
    _ ≤ (C * 2^β) * (4*t)^(A*β) + R := by rw [← mul_assoc]; gcongr
    _ ≤ t := h.2

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H2 := by
  intro hs ht k hk
  obtain ⟨β,C,R,hβ,hβ1,hC,bound⟩ := iterate_levels hs ht hk
  let A := (1 + 1 / β) / 2
  have hinv : 1 < 1 / β := (one_lt_div hβ).mpr hβ1
  have hA : 1 < A := by dsimp [A]; linarith
  have he : A * β = (β + 1) / 2 := by dsimp [A]; field_simp
  have hab : A * β < 1 := by linarith
  refine ⟨A,1,hA,one_pos,?_⟩
  have hlog : Tendsto (fun N : ℕ ↦ log (log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hlog.eventually (rounded_budget hβ (by linarith : 0 < A) hab C R hC)] with N hN hlen
  apply (bound _ N hN hlen).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  apply exp_le_exp.mpr
  simpa using neg_le_neg (Nat.le_ceil (log (log (N : ℝ)) ^ A))

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R1
