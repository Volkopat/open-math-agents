import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3
import Mathlib

/-!
A fixed-density and sparse-increment reduction of the reciprocal-window step.
Thomas Fredrickson with Codex. The interval decomposition is from PR 12335,
using @mucoucah's R3. The sparse invariant is adapted from OpenAI's Progressions.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1

open Erdos142 Filter Real OMA.R_Erdos142_erdos_142_variants_lower_R3

/-- Positive density at a fixed progression length forces an arithmetic progression. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ,
    S ⊆ Finset.Icc 1 N → δ * N ≤ S.card →
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S

/-- In the sparse regime, gain at least one unit of log density while retaining
the size reserve. OpenAI's sublinear power potential is one possible F. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ (F : ℝ → ℝ) (T D Cmin : ℝ),
    (∀ x ≥ 2, 0 ≤ F x ∧ F x ≤ x / 2 + D) ∧
    let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * N / (S.card : ℝ)))
    let valid := fun (N : ℕ) (S : Finset ℕ) => 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
      ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S
    ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
      F (p N S) + C ≤ log (log N) → ∃ (M : ℕ) (B : Finset ℕ),
        valid M B ∧ F (p M B) + C ≤ log (log M) ∧ p M B + 1 ≤ p N S

lemma reciprocal_window_le {k n : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hw : ∀ x ∈ S, ∃ j ∈ Finset.Ico n (2*n), 4*4^j < x ∧ x ≤ 5*4^j)
    (hf : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ n * ((r k (4^n) : ℝ) / (4:ℝ)^n) / 4 := by
  let B (j : ℕ) := (Finset.Icc 1 (4^j)).filter (fun b => 4*4^j+b ∈ S)
  have sub j : B j ⊆ Finset.Icc 1 (4^j) := Finset.filter_subset _ _
  let block j := (B j).map (addLeftEmbedding (4*4^j))
  have cover : S ⊆ (Finset.Ico n (2*n)).biUnion block := by
    intro x hx
    obtain ⟨j, hj, hl, hu⟩ := hw x hx
    refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_map.mpr ⟨x-4*4^j, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simpa [Nat.add_sub_of_le hl.le] using hx⟩
    · change 4*4^j+(x-4*4^j) = x
      omega
  have size j : (B j).card ≤ r k (4^j) := by
    apply card_le_r (sub j) ((apFree_iff hk).mpr ?_)
    rintro ⟨a, d, hd, h⟩
    exact hf ⟨4*4^j+a, d, hd, fun i hi => by simpa [Nat.add_assoc] using (Finset.mem_filter.mp (h i hi)).2⟩
  calc
    _ ≤ ∑ x ∈ (Finset.Ico n (2*n)).biUnion block, (x : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg cover (by intros; positivity)
    _ = _ := Finset.sum_biUnion (shiftBlocks_pairwiseDisjoint _ B sub)
    _ ≤ ∑ _j ∈ Finset.Ico n (2*n), ((r k (4^n) : ℝ) / (4:ℝ)^n) / 4 := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ _x ∈ block j, (4 * (4:ℝ)^j)⁻¹ := by
          apply Finset.sum_le_sum
          intro x hx
          apply inv_anti₀ (by positivity)
          exact_mod_cast (mem_shiftBlock_bounds (sub j) hx).1.le
        _ = (B j).card / (4:ℝ)^j / 4 := by simp [block, div_eq_mul_inv]; ring
        _ ≤ (r k (4^j) : ℝ) / (4:ℝ)^j / 4 := by gcongr; exact_mod_cast size j
        _ ≤ _ := div_le_div_of_nonneg_right (blockDensity_antitone hk (Finset.mem_Ico.mp hj).1) (by norm_num)
    _ = _ := by simp [show 2 * n - n = n by omega, mul_div_assoc]

theorem no_invariant_of_descent {S : Type*} (P : S → Prop) (potential : S → ℝ)
    (T : ℝ)
    (h_nonneg : ∀ x, P x → 0 ≤ potential x)
    (h_terminal : ∀ x, P x → potential x ≤ T → False)
    (h_step : ∀ x, P x → T < potential x →
      ∃ y, P y ∧ potential y + 1 ≤ potential x) :
    ∀ x, ¬ P x := by
  have h : ∀ n : ℕ, ∀ x, ⌊potential x⌋₊ = n → ¬ P x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hPx
      have hlarge : T < potential x := lt_of_not_ge (h_terminal x hPx)
      obtain ⟨y, hPy, hdec⟩ := h_step x hPx hlarge
      have hfloor := Nat.floor_mono hdec
      rw [Nat.floor_add_one (h_nonneg y hPy), hx] at hfloor
      exact ih ⌊potential y⌋₊ (by omega) y rfl hPy
  intro x
  exact h _ x rfl

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R3.H2 := by
  intro fixed sparse k hk ε hε
  obtain ⟨F,T,D,Cmin,hF,step⟩ := sparse k hk
  let p (N : ℕ) (S : Finset ℕ) := max 2 (log (2 * N / (S.card : ℝ)))
  let valid (N : ℕ) (S : Finset ℕ) := 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a+i*d ∈ S
  obtain ⟨L,hL⟩ := eventually_atTop.mp (fixed k hk (exp (-T)) (exp_pos _))
  let M := max 2 L
  let C := max Cmin (log (log M))
  let P (y : ℕ × Finset ℕ) := valid y.1 y.2 ∧ F (p y.1 y.2) + C ≤ log (log y.1)
  have hp N S : 2 ≤ p N S := le_max_left _ _
  have no := no_invariant_of_descent P (fun y => p y.1 y.2) T
    (fun y _ => (by linarith [hp y.1 y.2])) (by
      rintro ⟨N,S⟩ ⟨⟨hN,hS,hsub,hfree⟩,hbudget⟩ hsmall
      change p N S ≤ T at hsmall
      have hc : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
      have hN' : (1:ℝ) < N := by exact_mod_cast hN
      have hM : (1:ℝ) < M := by exact_mod_cast (show 1 < M by dsimp [M]; omega)
      have hl : log (log M) ≤ log (log N) := calc
        _ ≤ C := le_max_right _ _
        _ ≤ F (p N S) + C := le_add_of_nonneg_left (hF _ (hp N S)).1
        _ ≤ _ := hbudget
      have hMN := (log_le_log_iff (by linarith : (0:ℝ)<M) (by linarith : (0:ℝ)<N)).mp
        ((log_le_log_iff (log_pos hM) (log_pos hN')).mp hl)
      have ht := (log_le_iff_le_exp (by positivity : 0 < 2 * (N:ℝ) / S.card)).mp
        ((le_max_right _ _).trans hsmall)
      rw [div_le_iff₀ hc] at ht
      have hden : exp (-T) * (N:ℝ) ≤ S.card := by
        rw [exp_neg, inv_mul_eq_div, div_le_iff₀ (exp_pos T)]
        linarith only [ht, hN', mul_comm (exp T) (S.card : ℝ)]
      exact hfree (hL N ((le_max_right 2 L).trans (by exact_mod_cast hMN)) S hsub hden))
    (by
      rintro ⟨N,S⟩ ⟨hv,hinv⟩ hsp
      obtain ⟨m,B,hB,hbound,hgain⟩ := step C (le_max_left _ _) N S hv hsp hinv
      exact ⟨(m,B),⟨hB,hbound⟩,hgain⟩)
  have h4 : 0 < log 4 := log_pos (by norm_num)
  have hlim := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (0:ℕ),
    hlim.eventually_ge_atTop (max (2 - log (2/ε)) (log (2/ε) + 2*(D+C-log (log 4))))] with n hn hbig S hw hf
  apply (reciprocal_window_le (by omega : 1 < k) S hw hf).trans
  suffices hsmall : (n:ℝ) * ((r k (4^n):ℝ)/(4:ℝ)^n) ≤ ε by linarith
  by_contra! hbad
  obtain ⟨B,hsub,hfree,hcard⟩ := exists_maximizer (by omega : 1 < k) (4^n)
  rw [hcard] at hbad
  have hb : 0 < (B.card:ℝ) := by
    by_contra! hz
    have hzero : (B.card:ℝ) = 0 := le_antisymm hz (by positivity)
    rw [hzero,zero_div,mul_zero] at hbad
    linarith
  have hv : valid (4^n) B := ⟨one_lt_pow' (by decide) hn.ne', Finset.card_pos.mp
    (by exact_mod_cast hb), hsub, (apFree_iff (by omega : 1 < k)).mp hfree⟩
  apply no ((4^n),B)
  refine ⟨hv,?_⟩
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hm : 2 * (4:ℝ)^n / B.card ≤ (2/ε)*n := by
    rw [div_mul_eq_mul_div,div_le_div_iff₀ hb hε]
    rw [← mul_div_assoc,lt_div_iff₀ (by positivity)] at hbad
    nlinarith only [hbad]
  have hε' : 0 < 2/ε := by positivity
  have hpl : p (4^n) B ≤ log (2/ε) + log n := by
    apply max_le
    · have h := (le_max_left _ _).trans hbig
      change 2 - log (2/ε) ≤ log (n:ℝ) at h
      linarith
    · push_cast
      simpa only [log_mul hε'.ne' hnR.ne'] using log_le_log (by positivity) hm
  change F (p (4^n) B) + C ≤ log (log ((4^n:ℕ):ℝ))
  push_cast
  rw [log_pow, log_mul hnR.ne' h4.ne']
  have h := (le_max_right _ _).trans hbig
  change log (2/ε) + 2*(D+C-log (log 4)) ≤ log (n:ℝ) at h
  linarith only [(hF _ (hp (4^n) B)).2,hpl,h]

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1
