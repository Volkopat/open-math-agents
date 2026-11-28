import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2

/-!
Retains @minimumnz's scalar comparison proof from open-math-agents PR #11004.
Uses the Mathlib constant-barrier comparison as in @Salofe's pending PR #11192.
This proves only the registered finite-trace scalar bound.
-/

open Filter Set Real
open scoped Topology

private lemma dini_nonincreasing {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hdini : ∀ x ∈ Ico a b, ∀ r > 0, ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (f y - f x) < r) :
    f b ≤ f a := by
  exact image_le_of_liminf_slope_right_le_deriv_boundary hcont
    (B := fun _ => f a) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const x _ (f a))
    (by simpa only [slope, vsub_eq_sub, smul_eq_mul] using hdini) ⟨hab, le_rfl⟩

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2.H1 := by
  intro n t w ht0 hmono hcont hdini hjump hw0 hwn
  let Φ : (ℝ → ℝ) → ℝ → ℝ := fun u s =>
    u s * (4 * s + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * s + 1) ^ (1 / 4 : ℝ)
  have ht_nonneg : ∀ k : ℕ, 0 ≤ t k := fun k => ht0 ▸ hmono (Nat.zero_le k)
  have hstep : ∀ i < n, Φ (w (i + 1)) (t (i + 1)) ≤ Φ (w i) (t i) := by
    intro i hi
    have hti : 0 ≤ t i := ht_nonneg i
    have hti1 : 0 ≤ t (i + 1) := ht_nonneg (i + 1)
    have hle : t i ≤ t (i + 1) := hmono (Nat.le_succ i)
    have hPhi_cont : ContinuousOn (Φ (w i)) (Icc (t i) (t (i + 1))) := by
      have hlin : ContinuousOn (fun s : ℝ => 4 * s + 1) (Icc (t i) (t (i + 1))) :=
        (continuousOn_const.mul continuousOn_id).add continuousOn_const
      have hne : ∀ s ∈ Icc (t i) (t (i + 1)), (4 * s + 1 : ℝ) ≠ 0 := by
        intro s hs
        have : 0 ≤ s := hti.trans hs.1
        linarith
      have hp1 : ContinuousOn (fun s : ℝ => (4 * s + 1) ^ (-(3 / 4) : ℝ)) (Icc (t i) (t (i + 1))) :=
        hlin.rpow_const fun s hs => Or.inl (hne s hs)
      have hp2 : ContinuousOn (fun s : ℝ => (4 * s + 1) ^ (1 / 4 : ℝ)) (Icc (t i) (t (i + 1))) :=
        hlin.rpow_const fun s hs => Or.inl (hne s hs)
      exact ((hcont i hi).mul hp1).add (continuousOn_const.mul hp2)
    have hdec : Φ (w i) (t (i + 1)) ≤ Φ (w i) (t i) :=
      dini_nonincreasing hle hPhi_cont (hdini i hi)
    have hpos : 0 ≤ (4 * t (i + 1) + 1) ^ (-(3 / 4) : ℝ) :=
      rpow_nonneg (by linarith) _
    have hj : Φ (w (i + 1)) (t (i + 1)) ≤ Φ (w i) (t (i + 1)) := by
      dsimp [Φ]
      gcongr
      exact hjump i hi
    exact hj.trans hdec
  have hind : ∀ k ≤ n, Φ (w k) (t k) ≤ Φ (w 0) (t 0) := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ m ih =>
      exact (hstep m (by omega)).trans (ih (by omega))
  have hfinal : Φ (w n) (t n) ≤ Φ (w 0) (t 0) := hind n le_rfl
  have hPhi0 : Φ (w 0) (t 0) = w 0 0 + 2 * Real.pi := by
    dsimp [Φ]
    rw [ht0]
    norm_num
  have htn0 : 0 ≤ t n := ht_nonneg n
  have hbase_pos : 0 < 4 * t n + 1 := by linarith
  have hwn_term : 0 ≤ w n (t n) * (4 * t n + 1) ^ (-(3 / 4) : ℝ) :=
    mul_nonneg hwn (rpow_nonneg hbase_pos.le _)
  have hineq1 : 2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ w 0 0 + 2 * Real.pi := by
    dsimp [Φ] at hfinal
    linarith [hfinal, hPhi0, hwn_term]
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hineq2 : (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ 1 + w 0 0 / (2 * Real.pi) := by
    have hdiv := div_le_div_of_nonneg_right hineq1 h2pi_pos.le
    have hlhs : 2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ) / (2 * Real.pi) =
        (4 * t n + 1) ^ (1 / 4 : ℝ) := by
      field_simp [h2pi_pos.ne']
    have hrhs : (w 0 0 + 2 * Real.pi) / (2 * Real.pi) = 1 + w 0 0 / (2 * Real.pi) := by
      field_simp [h2pi_pos.ne']
      ring
    linarith
  have hpow4 : ((4 * t n + 1) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) ≤ (1 + w 0 0 / (2 * Real.pi)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (rpow_nonneg hbase_pos.le _) hineq2 4
  have hlhs4 : ((4 * t n + 1) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = 4 * t n + 1 := by
    rw [← rpow_natCast, ← rpow_mul hbase_pos.le]
    norm_num
  rw [hlhs4] at hpow4
  linarith
