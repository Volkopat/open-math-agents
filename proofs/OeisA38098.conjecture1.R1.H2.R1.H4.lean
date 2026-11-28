import OMAReductions.R_OeisA38098_conjecture1_R1_H2_R1

-- Step OeisA38098.conjecture1.R1.H2.R1.H4: hypothesis H4 of reduction OeisA38098.conjecture1.R1.H2.R1
-- Credit: @senamakel
-- Proof: the schoenfeld-rh argument (schoenfeldPi_of_RH_of_inputs) with the erdos-985 toolkit, pruned
-- to what it uses. Under RH, the explicit formula for psi with the zero sum bounded by Rosser's count
-- gives |theta(x) - x| for x >= 10^10; partial summation from theta to pi - li, with the theta range
-- and the psi certificate in between, gives the bound for x >= 4*10^5; the pi range covers the rest.

theorem Complex.digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
  Complex.digamma (s + n) = Complex.digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
 induction n with
 | zero => simp
 | succ n ih =>
  have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h =>
   hs (m + n) (by push_cast at h ⊢; linear_combination h)
  rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
   Complex.digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]
  ring
section
namespace Schoenfeld
open Complex Real
noncomputable def vek (T : ℝ) : ℝ := by
 classical
 exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
  ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0
def vbc : Prop :=
 ∀ T : ℝ, 2 ≤ T →
  |vek T -
   (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
   0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588
def ved : Prop :=
 ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x
end Schoenfeld
end
section
open scoped BigOperators
namespace Real
lemma vfq {r : ℝ} (hr : 0 ≤ r) (qlE : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have qgV : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) qgV
    _ = 2 * r ^ (m + 1) := by ring
end Real
namespace Complex
open scoped BigOperators in
lemma vgh {z : ℂ} (hz : ‖z‖ < 1) :
  -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
 have h := hasSum_taylorSeries_neg_log hz
 rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
 simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]
noncomputable
def vap (m : ℕ) (z : ℂ) : ℂ :=
 -logTaylor (m + 1) (-z)
@[simp]
lemma vhO (z : ℂ) : vap 0 z = 0 := by
 simp [vap, logTaylor_succ, logTaylor_zero]
@[simp]
lemma vgT (m : ℕ) : vap m 0 = 0 := by
 simp [vap, logTaylor_at_zero]
lemma vhI (n : ℕ) (z : ℂ) :
  logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
 rw [logTaylor_succ, Pi.add_apply]
 have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
  have qaJ : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
  rw [qaJ, mul_pow, ← mul_assoc, ← pow_add]
  have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
   rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
   norm_num
  rw [hpow]
  ring
 rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
  rw [hsign]
  ring]
 abel
lemma vfJ (m : ℕ) (z : ℂ) :
  logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
 induction m with
 | zero =>
   simp [logTaylor_succ, logTaylor_zero]
 | succ m hm =>
   rw [vhI, hm, Finset.sum_range_succ]
   have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
    simp [Nat.cast_add, Nat.cast_one, add_comm]
   rw [hcast]
   ring_nf
lemma vdi (m : ℕ) (z : ℂ) :
  vap m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
 simpa [vap] using congrArg Neg.neg (vfJ m z)
lemma vfI (m : ℕ) (z : ℂ) :
    HasDerivAt (vap m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : vap 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact vhO w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [vap] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)
lemma vcQ (m : ℕ) :
  Differentiable ℂ (fun z : ℂ => vap m z) := by
 intro z
 exact (vfI m z).differentiableAt
noncomputable
def vaJ (m : ℕ) (z : ℂ) : ℂ :=
 ∑' k, z ^ (m + 1 + k) / (m + 1 + k)
lemma vik {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have qcC : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) qcC ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _
lemma viC {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖vaJ m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [vaJ]
  have qaU : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have qaN : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ qaU
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm qaN
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine qaN.tsum_le_tsum ?_ qaU
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have qcC := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [qcC.tsum_eq, div_eq_mul_inv]
lemma vcq {z : ℂ} (hz : ‖z‖ < 1) (qgX : ‖z‖ ≤ 1 / 2) (m : ℕ) :
  ‖vaJ m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
 (viC hz m).trans (Real.vfq (norm_nonneg z) qgX m)
lemma vcw (m : ℕ) (z : ℂ) :
    ‖vap m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  have hsum :
      ‖vap m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
    rw [vdi]
    exact norm_sum_le _ _
  have hterm : ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
    intro k hk
    rw [norm_div, norm_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have qgc : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast qgc
    have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (k + 1))
    have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have hpow_le : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
      · have : ‖z‖ ^ (k + 1) ≤ 1 := by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have qe5 : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := pow_le_pow_right₀ qe5 hk_le
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
      _ ≤ ‖z‖ ^ (k + 1) := by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m) := hpow_le
  have hsum_le :
      (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖) ≤
        ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hcard : ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) = (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simp [Finset.sum_const]
  exact hsum.trans (hsum_le.trans_eq hcard)
lemma vcE {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
  -log (1 - z) = vap m z + vaJ m z := by
 let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
 have h_summable : Summable f := by
  simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
   (vik hz 0)
 have h_decomp := h_summable.sum_add_tsum_nat_add m
 rw [vgh hz, vdi, ← h_decomp]
 congr 1
 dsimp only [vaJ]
 refine tsum_congr fun k ↦ ?_
 simp only [f, Nat.cast_add]
 ring_nf
end Complex
end
section
noncomputable section
namespace Complex
variable {z : ℂ}
theorem vgG (z : ℂ) : -‖z‖ ≤ z.re :=
 neg_le_of_abs_le (abs_re_le_norm z)
lemma vem (u : ℂ) (n : ℕ) (hu : (1 : ℝ) ≤ ‖u‖) :
    ‖(u ^ n)⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖u ^ n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u ^ n)⁻¹‖ = ‖(1 : ℂ) / u ^ n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u ^ n‖ := by
        have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
        rw [Complex.norm_div, hone]
    _ ≤ 1 := by simpa [one_div] using inv_le_one_of_one_le₀ hge
end Complex
end
end
section
noncomputable section
open scoped BigOperators
open Set
namespace Complex
def qB (m : ℕ) (z : ℂ) : ℂ :=
 (1 - z) * exp (vap m z)
lemma veE (m : ℕ) (z : ℂ) :
  qB m z = (1 - z) * exp (vap m z) := by
 simp [qB]
@[simp]
lemma vju (m : ℕ) : qB m 0 = 1 := by
 simp [qB, vgT]
lemma vbf (m : ℕ) (z : ℂ) :
    qB m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [qB] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [qB]
lemma vcK (m : ℕ) (z : ℂ) :
  qB m z ≠ 0 ↔ z ≠ 1 := by
 simpa [ne_eq] using (not_congr (vbf (m := m) (z := z)))
lemma vdW (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
  qB m z ≠ 0 :=
 (vcK (m := m) (z := z)).2 hz
lemma vaE (m : ℕ) :
  Differentiable ℂ (fun z : ℂ => qB m z) := by
 simpa [qB] using!
  ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
   (differentiable_exp.comp (vcQ m))
theorem vcT (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
  analyticOrderAt (fun z : ℂ => qB m (z / a)) a = (1 : ℕ∞) := by
 set F : ℂ → ℂ := fun z => qB m (z / a)
 have hF : AnalyticAt ℂ F a := by
  have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
   simp [div_eq_mul_inv]
  have hdiff : Differentiable ℂ F := (vaE m).comp hdiv
  exact Differentiable.analyticAt (f := F) hdiff a
 let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (vap m (z / a))
 have hg : AnalyticAt ℂ g a := by
  have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
   simp [div_eq_mul_inv]
  have qe6 : Differentiable ℂ (fun z : ℂ => vap m (z / a)) :=
   (vcQ m).comp hdiv
  have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (vap m (z / a))) :=
   (Complex.differentiable_exp).comp qe6
  have qgY : Differentiable ℂ g := by
   simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
  exact Differentiable.analyticAt (f := g) qgY a
 have hg0 : g a ≠ 0 := by
  have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
  have qir : Complex.exp (vap m (a / a)) ≠ 0 :=
   Complex.exp_ne_zero (vap m (a / a))
  simpa [g] using mul_ne_zero hconst qir
 refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
 refine ⟨g, hg, hg0, ?_⟩
 refine Filter.Eventually.of_forall ?_
 intro z
 have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
  have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
  simp [div_eq_mul_inv, h1]
  ring
 simp only [F, g, pow_one, smul_eq_mul]
 rw [veE]
 simp [hlin, mul_assoc]
lemma vcl (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    qB m z = exp (-vaJ m z) := by
  unfold qB
  have qgd : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log qgd, ← Complex.exp_add]
  have hsum : log (1 - z) + vap m z = -vaJ m z := by
    have hdecomp := vcE hz m
    calc
      log (1 - z) + vap m z
          = log (1 - z) + (vap m z + vaJ m z) - vaJ m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - vaJ m z := by rw [hdecomp]
      _ = -vaJ m z := by ring
  simp [hsum]
theorem vbj {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖qB m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [qB] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : qB m z = exp (-vaJ m z) :=
      vcl m hz_lt hz1
    rw [h_eq]
    have qcD := vcq hz_lt hz m
    have qeb : ‖-vaJ m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖vaJ m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have qe5 : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' qe5 h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have qp0 : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (qcD.trans hmul).trans hsq
      linarith
    have qa8 : ‖exp (-vaJ m z) - 1‖ ≤ 2 * ‖-vaJ m z‖ :=
      Complex.norm_exp_sub_one_le qeb
    simp only [norm_neg] at qa8
    calc
      ‖exp (-vaJ m z) - 1‖ ≤ 2 * ‖vaJ m z‖ := qa8
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring
lemma vch (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - ‖vap m z‖ ≤ Real.log ‖qB m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [qB]
  set S : ℂ := vap m z
  have hS : qB m z = (1 - z) * Complex.exp S := by
    simp [qB, S]
  have qbe : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖qB m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt qbe
    calc
      Real.log ‖qB m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
              simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.vgG S
  have : Real.log ‖qB m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  simpa [S] using this
lemma vcV {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖qB m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq : qB m z = Complex.exp (-vaJ m z) :=
    vcl m hz_lt hz1
  have hlog :
      Real.log ‖qB m z‖ = (-vaJ m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-vaJ m z).re ≥ -‖vaJ m z‖ := by
    simpa [norm_neg] using Complex.vgG (-vaJ m z)
  have htail := vcq hz_lt hz m
  have : (-vaJ m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-vaJ m z).re ≥ -‖vaJ m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this
end Complex
end
end
section
noncomputable section
open Filter Topology
namespace Complex
theorem vcd {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
  logDeriv (fun w : ℂ => qB 1 (w / a)) z =
   1 / (z - a) + 1 / a := by
 have hE :
   (fun w : ℂ => qB 1 (w / a)) =
    fun w : ℂ => (1 - w / a) * exp (w / a) := by
  ext w
  simp [veE, vdi]
 have hf : (1 - z / a) ≠ 0 := by
  intro hzero
  have hdiv : z / a = 1 := by
   exact (sub_eq_zero.mp hzero).symm
  exact hz ((div_eq_one_iff_eq ha).1 hdiv)
 rw [hE,
  logDeriv_mul z hf (exp_ne_zero (z / a)) (by fun_prop) (by fun_prop)]
 have hleft : logDeriv (fun w : ℂ => 1 - w / a) z = 1 / (z - a) := by
  rw [logDeriv_apply]
  have hderiv : deriv (fun w : ℂ => 1 - w / a) z = -(1 / a) := by
   simp [one_div]
  rw [hderiv]
  have haz : -z + a ≠ 0 := by
   simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (Ne.symm hz)
  field_simp [ha, sub_ne_zero.mpr hz, haz]
  have haz' : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hza : z - a = -(a - z) := by ring
  rw [hza]
  field_simp [haz']
 have hright : logDeriv (fun w : ℂ => exp (w / a)) z = 1 / a := by
  rw [logDeriv_apply]
  have hderiv : deriv (fun w : ℂ => exp (w / a)) z =
    exp (z / a) * (1 / a) := by
   simp [one_div]
  rw [hderiv]
  field_simp [exp_ne_zero (z / a)]
 rw [hleft, hright]
end Complex
end
end
section
open Filter Topology Set
namespace MeromorphicOn
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
 {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma vdM (f : 𝕜 → E) {U K : Set 𝕜}
  (hK : IsCompact K) (hKU : K ⊆ U) :
  (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
 classical
 set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
 have hloc :
   ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
  intro x hxK
  rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
  exact ⟨V, hV, hfin⟩
 choose V qg0 qit using hloc
 rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => qg0 x hx) with
  ⟨t, ht⟩
 have hsub :
   K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
  intro y hy
  rcases hy with ⟨hyK, hyS⟩
  have qiu : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
  rcases Set.mem_iUnion.1 qiu with ⟨x, qg1⟩
  rcases Set.mem_iUnion.1 qg1 with ⟨hxT, hyV⟩
  refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
  exact ⟨hxT, ⟨hyV, hyS⟩⟩
 have qiv : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
  classical
  refine (t.finite_toSet).biUnion ?_
  intro x hx
  simpa using (qit (x : 𝕜) x.2)
 exact qiv.subset hsub
end MeromorphicOn
end
section
open Set
namespace Complex.Hadamard
def vio (f : ℂ → ℂ) (U : Set ℂ) : Type :=
 Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))
abbrev qv (f : ℂ → ℂ) (U : Set ℂ) : Type :=
 {p : vio f U // p.1 ≠ 0}
abbrev qg {f : ℂ → ℂ} {U : Set ℂ} (p : qv f U) : ℂ :=
 p.1.1
@[simp]
lemma vao {f : ℂ → ℂ} {U : Set ℂ} (p : qv f U) :
  qg p ≠ 0 := p.2
@[simp]
lemma vbs {f : ℂ → ℂ} {U : Set ℂ}
  (p : qv f U) :
  MeromorphicOn.divisor f U (qg p) ≠ 0 := by
 have hn :
   Int.toNat (MeromorphicOn.divisor f U (qg p)) ≠ 0 := by
  intro h0
  have q0 : Fin 0 := by
   simpa [qg, h0] using p.1.2
  exact Fin.elim0 q0
 intro hdiv
 have : Int.toNat (MeromorphicOn.divisor f U (qg p)) = 0 := by
  simp [hdiv]
 exact hn this
noncomputable def qA (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
 ∏' p : qv f U, qB m (z / qg p)
@[simp]
lemma vaD (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
  qA m f U 0 = 1 := by
 simp [qA]
end Complex.Hadamard
end
section
namespace Complex
section qdD
theorem _root_.TendstoUniformlyOn.vij {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have qcF : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos qcF, fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' := hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C' := by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') := mul_lt_mul_of_pos_left hn' qcF
  have hnorm :
      ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    rw [dist_eq_norm, hnorm]
    have hlt' : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C' * (ε / C') := hlt
        _ = ε := by field_simp [qcF.ne']
    exact hlt'
  exact hεu hdist
end qdD
end Complex
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
lemma vaT {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
  (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
  Finite {p : qv f U // ‖qg p‖ ≤ B} := by
 set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
 have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
 have qiw : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
  MeromorphicOn.vdM (f := f) (U := U)
   (K := Metric.closedBall (0 : ℂ) B) hK hBU
 set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
 have hpts : pts.Finite := qiw.sdiff
 let : Fintype pts := hpts.fintype
 let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
 have : Finite T := by infer_instance
 let F :
   {p : qv f U // ‖qg p‖ ≤ B} → T := fun p =>
  ⟨⟨qg p.1, by
    have hball : qg p.1 ∈ Metric.closedBall (0 : ℂ) B := by
     simpa [Metric.mem_closedBall, dist_zero_right] using p.2
    have hsupport : qg p.1 ∈ D.support := by
     have qec :
       Int.toNat (MeromorphicOn.divisor f U (qg p.1)) ≠ 0 := by
      intro h0
      have qix :
        Fin (Int.toNat (MeromorphicOn.divisor f U (qg p.1))) := by
       simpa [D] using p.1.1.2
      have : Fin 0 := by simpa [h0] using qix
      exact Fin.elim0 this
     have qp1 : D (qg p.1) ≠ 0 := by
      intro hD0
      apply qec
      simp [D, hD0]
     simp [D, Function.locallyFinsuppWithin.support, Function.support]
    have hne0 : qg p.1 ≠ 0 := vao p.1
    exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
   p.1.1.2⟩
 refine Finite.of_injective F ?_
 intro p q hpq
 apply Subtype.ext
 apply Subtype.ext
 have h' := (Sigma.mk.inj_iff.1 hpq)
 have hz : qg p.1 = qg q.1 := congrArg Subtype.val h'.1
 apply (Sigma.mk.inj_iff).2
 refine ⟨hz, ?_⟩
 exact h'.2
lemma vau {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
  (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
  ({p : qv f U | ‖qg p‖ ≤ B} : Set _).Finite := by
 let s : Set (qv f U) := {p | ‖qg p‖ ≤ B}
 have : Finite (↥s) :=
  vaT (f := f) (U := U) B hBU
 exact Set.toFinite s
lemma vbz {z a : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2 * R : ℝ) < ‖a‖) :
    ‖z / a‖ ≤ (1 / 2 : ℝ) := by
  have qaV : 0 < (2 * R : ℝ) := by nlinarith [hR]
  have hinv : ‖a‖⁻¹ < (2 * R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt qaV ha
  have qaW : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have hmul_lt : R * ‖a‖⁻¹ < R * (2 * R)⁻¹ :=
    mul_lt_mul_of_pos_left hinv hR
  have qbg : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
    have qcH : (R : ℝ) ≠ 0 := hR.ne'
    rw [show R * (2 * R)⁻¹ = R / (2 * R) by simp [div_eq_mul_inv]]
    field_simp [qcH]
  have hnorm : ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := hnorm
      _ ≤ R * ‖a‖⁻¹ := qaW
      _ < R * (2 * R)⁻¹ := hmul_lt
      _ = (1 / 2 : ℝ) := qbg
theorem vaM
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : qv f (Set.univ : Set ℂ), z ≠ qg p) :
    Summable (fun p : qv f (Set.univ : Set ℂ) =>
      1 / (z - qg p) + 1 / qg p) := by
  let R : ℝ := max ‖z‖ 1
  have qG : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have qa0 : ‖z‖ ≤ R := le_max_left _ _
  let u : qv f (Set.univ : Set ℂ) → ℝ :=
    fun p => (2 * R) * (‖qg p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u := h_sum.mul_left (2 * R)
  refine hu.of_norm_bounded_eventually ?_
  have qa1 :
      ∀ᶠ p : qv f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖qg p‖ := by
    have hfin :
        ({p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤
          2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vau
        (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖qg p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  filter_upwards [qa1] with p hp
  let a : ℂ := qg p
  have ha0 : a ≠ 0 := vao p
  have qg3 : z - a ≠ 0 := sub_ne_zero.mpr (hz p)
  have hterm : 1 / (z - a) + 1 / a = z / (a * (z - a)) := by
    field_simp [ha0, qg3]
    ring
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have qee : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, qa0, hp]
  have hnorm : ‖1 / (z - a) + 1 / a‖ ≤ (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by
    rw [hterm, norm_div, norm_mul]
    have qbB : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have qcI : 0 < ‖z - a‖ := norm_pos_iff.mpr qg3
    rw [div_eq_mul_inv]
    calc
      ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
          = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              field_simp [qbB.ne', qcI.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
              gcongr
              have qef : 0 < ‖a‖ / 2 := by positivity
              have hinv : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le qef qee
              have qeg : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by field_simp [qbB.ne']
              simpa [qeg] using hinv
      _ = (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by ring
  simpa [u, a] using hnorm
theorem vcu
  (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  HasProdUniformlyOn
   (fun (p : qv f (Set.univ : Set ℂ)) (z : ℂ) =>
    qB m (z / qg p))
   (qA m f (Set.univ : Set ℂ)) K := by
 rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
 set R : ℝ := max R0 1
 have qG : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
 have qcJ : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
 let g : qv f (Set.univ : Set ℂ) → ℂ → ℂ :=
  fun p z => qB m (z / qg p) - 1
 let u : qv f (Set.univ : Set ℂ) → ℝ :=
  fun p => (4 * R ^ (m + 1)) * (‖qg p‖⁻¹ ^ (m + 1))
 have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
 have qa1 :
   ∀ᶠ p : qv f (Set.univ : Set ℂ) in Filter.cofinite,
    (2 * R : ℝ) < ‖qg p‖ := by
  have hfin :
    ({p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤ 2 * R} :
      Set _).Finite := by
   have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
   exact vau (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
  have := hfin.eventually_cofinite_notMem
  filter_upwards [this] with p hp
  have : ¬ ‖qg p‖ ≤ 2 * R := by simpa using hp
  exact lt_of_not_ge this
 have hBound :
   ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
  filter_upwards [qa1] with p hp z hzK
  have qa0 : ‖z‖ ≤ R := qcJ z hzK
  have qbh : ‖z / qg p‖ ≤ (1 / 2 : ℝ) := by
   exact vbz qG qa0 hp
  have hE :
    ‖qB m (z / qg p) - 1‖ ≤
     4 * ‖z / qg p‖ ^ (m + 1) :=
   vbj (m := m) (z := z / qg p) qbh
  have hz_pow :
    ‖z / qg p‖ ^ (m + 1) ≤
     (R ^ (m + 1)) * (‖qg p‖⁻¹ ^ (m + 1)) := by
   have : ‖z / qg p‖ = ‖z‖ * ‖qg p‖⁻¹ := by
    simp [div_eq_mul_inv]
   rw [this]
   have : (‖z‖ * ‖qg p‖⁻¹) ^ (m + 1) =
     ‖z‖ ^ (m + 1) * (‖qg p‖⁻¹ ^ (m + 1)) := by
    simp [mul_pow]
   rw [this]
   have qcK : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
    pow_le_pow_left₀ (norm_nonneg z) qa0 (m + 1)
   gcongr
  dsimp [g, u]
  nlinarith [hE, hz_pow]
 have hcts : ∀ p, ContinuousOn (g p) K := by
  intro p
  have qcL : Continuous (fun z : ℂ => qB m z) :=
   (vaE m).continuous
  have hdiv : Continuous fun z : ℂ => z / qg p := by
   simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
  have hcont : Continuous fun z : ℂ => qB m (z / qg p) :=
   qcL.comp hdiv
  simpa only [g] using hcont.continuousOn.fun_sub continuous_const.continuousOn
 have hprod :
   HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
  simpa using
   Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
 simpa [g, qA, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  using! hprod
theorem vav
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  HasProdLocallyUniformlyOn
   (fun (p : qv f (Set.univ : Set ℂ)) (z : ℂ) =>
    qB m (z / qg p))
   (qA m f (Set.univ : Set ℂ))
   (Set.univ : Set ℂ) := by
 refine hasProdLocallyUniformlyOn_of_forall_compact
   (f := fun p z => qB m (z / qg p))
   (g := qA m f (Set.univ : Set ℂ))
   (s := (Set.univ : Set ℂ)) isOpen_univ ?_
 intro K hKU hK
 simpa using
  (vcu (m := m) (f := f) (K := K) hK h_sum)
theorem vaw
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  DifferentiableOn ℂ (qA m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) := by
 have hloc :
   TendstoLocallyUniformlyOn
    (fun (s : Finset (qv f (Set.univ : Set ℂ))) (z : ℂ) =>
     ∏ p ∈ s, qB m (z / qg p))
    (qA m f (Set.univ : Set ℂ))
    Filter.atTop (Set.univ : Set ℂ) := by
  simpa [HasProdLocallyUniformlyOn] using
   (vav (m := m) (f := f) h_sum)
 have hF :
   ∀ᶠ s : Finset (qv f (Set.univ : Set ℂ)) in Filter.atTop,
    DifferentiableOn ℂ
     (fun z : ℂ => ∏ p ∈ s, qB m (z / qg p))
     (Set.univ : Set ℂ) := by
  refine Filter.Eventually.of_forall ?_
  intro s
  have hdiff :
    Differentiable ℂ
     (fun z : ℂ => ∏ p ∈ s, qB m (z / qg p)) := by
   let F : qv f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => qB m (z / qg p)
   have hF' : ∀ p ∈ s, Differentiable ℂ (F p) := by
    intro p hp
    have hdiv : Differentiable ℂ (fun z : ℂ => z / qg p) := by
     have : Differentiable ℂ (fun z : ℂ => z * ((qg p)⁻¹)) :=
      (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const
       ((qg p)⁻¹)
     simp [div_eq_mul_inv]
    exact (vaE m).comp hdiv
   simpa [F] using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := F) (u := s) hF')
  simpa using hdiff.differentiableOn
 have : (Filter.atTop : Filter (Finset (qv f (Set.univ : Set ℂ)))).NeBot :=
  Filter.atTop_neBot
 exact hloc.differentiableOn hF isOpen_univ
theorem vcC
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) (z : ℂ) :
  DifferentiableAt ℂ (qA m f (Set.univ : Set ℂ)) z :=
 ((vaw m f h_sum) z (by simp)).differentiableAt
  (by simp)
theorem vcH
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : qv f (Set.univ : Set ℂ), z ≠ qg p)
    (hprod_ne : qA 1 f (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (qA 1 f (Set.univ : Set ℂ)) z =
      ∑' p : qv f (Set.univ : Set ℂ),
        (1 / (z - qg p) + 1 / qg p) := by
  let Φ : qv f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => qB 1 (w / qg p)
  have hf : ∀ p, Φ p z ≠ 0 := by
    intro p
    have hp0 : qg p ≠ 0 := vao p
    refine vdW 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p, DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ) := by
    intro p
    have hdiv : Differentiable ℂ (fun w : ℂ => w / qg p) := by
      have : Differentiable ℂ (fun w : ℂ => w * ((qg p)⁻¹)) :=
        (differentiable_id : Differentiable ℂ (fun w : ℂ => w)).mul_const
          ((qg p)⁻¹)
      simp [div_eq_mul_inv]
    exact ((vaE 1).comp hdiv).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z := by
    have hm :
        Summable (fun p : qv f (Set.univ : Set ℂ) =>
          1 / (z - qg p) + 1 / qg p) :=
      vaM h_sum hz
    refine hm.congr ?_
    intro p
    have hp0 : qg p ≠ 0 := vao p
    simpa [Φ] using
      (Complex.vcd
        (a := qg p) (z := z) hp0 (hz p)).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    have hprod := vav
      (m := 1) (f := f) h_sum
    simpa [Φ, qA] using hprod.multipliableLocallyUniformlyOn
  have hnez : (∏' p, Φ p z) ≠ 0 := by
    simpa [Φ, qA] using hprod_ne
  have hlog : logDeriv (∏' p, Φ p ·) z = ∑' p, logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (qA 1 f (Set.univ : Set ℂ)) z
        = ∑' p, logDeriv (Φ p) z := by
          simpa [Φ, qA] using! hlog
    _ = ∑' p : qv f (Set.univ : Set ℂ),
          (1 / (z - qg p) + 1 / qg p) := by
          refine tsum_congr fun p => ?_
          have hp0 : qg p ≠ 0 := vao p
          simpa [Φ] using
            Complex.vcd
              (a := qg p) (z := z) hp0 (hz p)
end Complex.Hadamard
end
section
noncomputable section
open Set
open scoped Topology BigOperators
namespace Complex.Hadamard
lemma vax {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
  MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
 have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
  intro w hw
  exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
 simp only
  [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)), analyticOrderNatAt]
 have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
 cases h : analyticOrderAt f z with
 | top =>
   simp [han.meromorphicOrderAt_eq, h]
 | coe n =>
   simp [han.meromorphicOrderAt_eq, h]
theorem vcp (f : ℂ → ℂ) (z₀ : ℂ) :
  ({p : qv f (Set.univ : Set ℂ) | qg p = z₀} :
   Set _).Finite := by
 have hsub :
   ({p : qv f (Set.univ : Set ℂ) | qg p = z₀} : Set _)
    ⊆ ({p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤ ‖z₀‖} :
     Set _) := by
  intro p hp
  have : qg p = z₀ := hp
  simp [this]
 have hfin :
   ({p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤ ‖z₀‖} :
    Set _).Finite := by
  have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
  simpa using (vau (f := f) (U := (Set.univ : Set ℂ))
   (B := ‖z₀‖) this)
 exact hfin.subset hsub
def qO (f : ℂ → ℂ) (z₀ : ℂ) :
  Finset (qv f (Set.univ : Set ℂ)) :=
 (vcp (f := f) z₀).toFinset
@[simp]
lemma vai (f : ℂ → ℂ) (z₀ : ℂ)
  (p : qv f (Set.univ : Set ℂ)) :
  p ∈ qO (f := f) z₀ ↔ qg p = z₀ := by
 simp [qO]
theorem vdY
  (f : ℂ → ℂ) (z₀ : ℂ) :
  ∀ᶠ s : Finset (qv f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
   qO (f := f) z₀ ⊆ s := by
 refine (Filter.eventually_atTop.2 ?_)
 refine ⟨qO (f := f) z₀, ?_⟩
 intro s hs
 exact hs
lemma vbR (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (qO (f := f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  let S : Set (qv f (Set.univ : Set ℂ)) := {p | qg p = z₀}
  have hS : S.Finite := vcp (f := f) z₀
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    have : Fintype S := hS.fintype
    let e : S ≃ Fin n :=
      { toFun := by
          intro x
          rcases x with ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have qe7 : z = z₀ := by simpa [qg] using! hp
          subst qe7
          simpa [n] using q
        invFun := by
          intro q
          refine ⟨⟨⟨z₀, ?_⟩, hz₀⟩, ?_⟩
          · simpa [n] using q
          · simp [S, qg]
        left_inv := by
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have qe7 : z = z₀ := by simpa [qg] using! hp
          subst qe7
          (ext; rfl)
        right_inv := by
          intro q
          rfl }
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have qge : S.ncard = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  have hto : hS.toFinset = qO (f := f) z₀ := by
    rfl
  have qei : S.ncard = (qO (f := f) z₀).card := by
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact qei.symm.trans qge
lemma vaC
  {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
  (qO (f := f) z₀).card = analyticOrderNatAt f z₀ := by
 have hdiv :
   MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
  vax (f := f) hf z₀
 have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
  analyticOrderNatAt f z₀ := by
  simp [hdiv]
 exact (vbR (f := f) (z₀ := z₀) hz₀).trans htoNat
lemma vcg
  {f : ℂ → ℂ} (z₀ : ℂ) (p : qv f (Set.univ : Set ℂ)) :
  p ∉ qO (f := f) z₀ ↔ qg p ≠ z₀ := by
 simp [vai]
end Complex.Hadamard
end
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
noncomputable def vam
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (p : qv f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
 classical
 exact if p ∈ qO (f := f) z₀ then (1 : ℂ)
  else qB m (z / qg p)
@[simp]
theorem vbJ
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (p : qv f (Set.univ : Set ℂ)) (z : ℂ)
  (hp : p ∈ qO (f := f) z₀) :
  vam m f z₀ p z = 1 := by
 classical
 simp [vam, hp]
@[simp]
theorem vaV
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (p : qv f (Set.univ : Set ℂ)) (z : ℂ)
  (hp : p ∉ qO (f := f) z₀) :
  vam m f z₀ p z =
   qB m (z / qg p) := by
 classical
 simp [vam, hp]
lemma vfi
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : qv f (Set.univ : Set ℂ)) (z : ℂ) :
    vam m f z₀ p z =
      if qg p = z₀ then (1 : ℂ)
      else qB m (z / qg p) := by
  classical
  by_cases h : qg p = z₀
  · have hp : p ∈ qO (f := f) z₀ := by
      simpa [vai] using h
    simp [vbJ, hp, h]
  · have hp : p ∉ qO (f := f) z₀ := by
      intro hmem
      exact h ((vai f z₀ p).1 hmem)
    simp [vaV, hp, h]
noncomputable def q7 (m : ℕ) (f : ℂ → ℂ)
  (s : Finset (qv f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
 ∏ p ∈ s, qB m (z / qg p)
theorem vay (m : ℕ) {f : ℂ → ℂ}
  (p : qv f (Set.univ : Set ℂ)) :
  Differentiable ℂ (fun z : ℂ => qB m (z / qg p)) := by
 have hdiv : Differentiable ℂ (fun z : ℂ => z / qg p) := by
  simp [div_eq_mul_inv]
 exact (vaE m).comp hdiv
theorem vbN (m : ℕ) (f : ℂ → ℂ)
  (s : Finset (qv f (Set.univ : Set ℂ))) :
  Differentiable ℂ (q7 m f s) := by
 let Φ : qv f (Set.univ : Set ℂ) → ℂ → ℂ :=
  fun p z => qB m (z / qg p)
 have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
  intro p _hp
  exact vay m p
 simpa [q7, Φ] using!
  (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
theorem vbv (m : ℕ) (f : ℂ → ℂ)
  (s : Finset (qv f (Set.univ : Set ℂ))) (z₀ : ℂ) :
  AnalyticAt ℂ (q7 m f s) z₀ :=
 (vbN m f s).analyticAt z₀
noncomputable def vah
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (s : Finset (qv f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
 ∏ p ∈ s, vam m f z₀ p z
@[simp]
lemma vee
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (s : Finset (qv f (Set.univ : Set ℂ))) (z : ℂ) :
  vah m f z₀ s z =
   ∏ p ∈ s, if qg p = z₀ then (1 : ℂ)
    else qB m (z / qg p) := by
 simp [vah, vam,
  vai]
theorem vcy
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (qv f (Set.univ : Set ℂ))) :
    Differentiable ℂ (vah m f z₀ s) := by
  let Φ : qv f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => vam m f z₀ p z
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    by_cases hpF : p ∈ qO (f := f) z₀
    · have qe8 : Φ p = fun _ => (1 : ℂ) := by
        ext z
        simp only [Φ, vbJ m f z₀ p z hpF]
      rw [qe8]
      exact differentiable_const (1 : ℂ)
    · have qe8 : Φ p = fun z => qB m (z / qg p) := by
        ext z
        simp only [Φ, vaV m f z₀ p z hpF]
      rw [qe8]
      exact vay m p
  have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) =
      vah m f z₀ s := by
    ext z
    simp [Φ, vah]
  have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
    simpa using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
  simpa [hEq] using this
noncomputable def vaf
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
 ∏' p : qv f (Set.univ : Set ℂ), vam m f z₀ p z
theorem vbD
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn (fun (p : qv f (Set.univ : Set ℂ)) (z : ℂ) =>
        vam m f z₀ p z) (vaf m f z₀)
      K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have qG : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have qcJ : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let term : qv f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    vam m f z₀ p z
  let g : qv f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : qv f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖qg p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have qa1 :
      ∀ᶠ p : qv f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖qg p‖ := by
    have hfin :
        ({p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤ 2 * R} :
          Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vau (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖qg p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [qa1] with p hp z hzK
    by_cases hpF : p ∈ qO (f := f) z₀
    · have hval : qg p = z₀ :=
        (vai (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt qG) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      simp [g, term, vam, hval, hu0, sub_eq_add_neg]
    · have qa0 : ‖z‖ ≤ R := qcJ z hzK
      have qbh : ‖z / qg p‖ ≤ (1 / 2 : ℝ) := by
        have qaV : 0 < (2 * R : ℝ) := by nlinarith [qG]
        have hinv : ‖qg p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt qaV hp)
        have qaW : ‖z‖ * ‖qg p‖⁻¹ ≤ R * ‖qg p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right qa0 ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖qg p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv qG
        have hlt : ‖z‖ * ‖qg p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt qaW hmul_lt
        have qbg : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have qcH : (R : ℝ) ≠ 0 := qG.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [qcH]
        have hnorm : ‖z / qg p‖ = ‖z‖ * ‖qg p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have qe9 : ‖z / qg p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / qg p‖ = ‖z‖ * ‖qg p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := qbg
        exact le_of_lt qe9
      have hE : ‖qB m (z / qg p) - 1‖ ≤
            4 * ‖z / qg p‖ ^ (m + 1) :=
        vbj (m := m) (z := z / qg p) qbh
      have hz_pow : ‖z / qg p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖qg p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / qg p‖ = ‖z‖ * ‖qg p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖qg p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖qg p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have qcK : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) qa0 (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [vam, hpF] at *
      nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ qO (f := f) z₀
    · have hval : qg p = z₀ :=
        (vai (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, vam, hval, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · have qg6 : qg p ≠ z₀ :=
        (vcg (f := f) z₀ p).1 hpF
      have qcL : Continuous (fun z : ℂ => qB m z) :=
        (vaE m).continuous
      have hdiv : Continuous fun z : ℂ => z / qg p := by
        simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => qB m (z / qg p) :=
        qcL.comp hdiv
      have : ContinuousOn (fun z : ℂ => qB m (z / qg p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      simpa [g, term, vam, vai, qg6] using this
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  simp [term, vaf, vam]
theorem vbt
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  HasProdLocallyUniformlyOn
   (fun (p : qv f (Set.univ : Set ℂ)) (z : ℂ) =>
    vam m f z₀ p z)
   (vaf m f z₀)
   (Set.univ : Set ℂ) := by
 refine hasProdLocallyUniformlyOn_of_forall_compact
   (f := fun p z => vam m f z₀ p z)
   (g := vaf m f z₀) (s := (Set.univ : Set ℂ))
   isOpen_univ ?_
 intro K hKU hK
 simpa using
  (vbD (m := m) (f := f) (z₀ := z₀)
   (K := K) hK h_sum)
theorem vaK
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  TendstoLocallyUniformlyOn
   (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
    vah m f z₀ s)
   (vaf m f z₀)
   Filter.atTop
   (Set.univ : Set ℂ) := by
 have hprod :
   HasProdLocallyUniformlyOn
    (fun (p : qv f (Set.univ : Set ℂ)) (z : ℂ) =>
     vam m f z₀ p z)
    (vaf m f z₀)
    (Set.univ : Set ℂ) :=
  vbt (m := m) (f := f)
   (z₀ := z₀) h_sum
 have h :
   TendstoLocallyUniformlyOn
    (fun (s : Finset (qv f (Set.univ : Set ℂ))) (z : ℂ) =>
     ∏ p ∈ s,
      if qg p = z₀ then (1 : ℂ)
      else qB m (z / qg p))
    (vaf m f z₀)
    Filter.atTop
    (Set.univ : Set ℂ) := by
  simpa [HasProdLocallyUniformlyOn, vam, vai]
   using hprod
 refine h.congr (G := fun s z => vah m f z₀ s z) ?_
 intro s z hz
 simp [vee]
theorem vaW
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  DifferentiableOn ℂ (vaf m f z₀) (Set.univ : Set ℂ) := by
 have hloc :
   TendstoLocallyUniformlyOn
    (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
     vah m f z₀ s)
    (vaf m f z₀)
    Filter.atTop
    (Set.univ : Set ℂ) :=
  vaK (m := m) (f := f)
   (z₀ := z₀) h_sum
 have hF :
   ∀ᶠ s : Finset (qv f (Set.univ : Set ℂ)) in Filter.atTop,
    DifferentiableOn ℂ (vah m f z₀ s) (Set.univ : Set ℂ) := by
  refine Filter.Eventually.of_forall ?_
  intro s
  exact (vcy m f z₀ s).differentiableOn
 have : (Filter.atTop : Filter (Finset (qv f (Set.univ : Set ℂ)))).NeBot :=
  Filter.atTop_neBot
 exact hloc.differentiableOn hF isOpen_univ
lemma vbL
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (qv f (Set.univ : Set ℂ)))
    (hs : qO (f := f) z₀ ⊆ s) :
    q7 m f s z =
      q7 m f (qO (f := f) z₀) z *
        vah m f z₀ s z := by
  classical
  let fiber : Finset (qv f (Set.univ : Set ℂ)) :=
    qO (f := f) z₀
  let P : qv f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : qv f (Set.univ : Set ℂ) → ℂ :=
    fun p => qB m (z / qg p)
  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))
  have hP : (∏ p ∈ s with P p, term p) = q7 m f fiber z := by
    have hg : ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    have hsub := (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    simpa [q7, term, P, fiber, Finset.prod_filter] using hsub.symm
  have qiy : (∏ p ∈ s with ¬ P p, term p) = vah m f z₀ s z := by
    simp [vah, vam, term, P, fiber,
      Finset.prod_filter, vai]
  have qgf : ∏ p ∈ s, term p = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) :=
    hsplit.symm
  calc
    q7 m f s z
        = ∏ p ∈ s, term p := by simp [q7, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := qgf
    _ = q7 m f fiber z * vah m f z₀ s z := by
      simp [hP, qiy, fiber]
end Complex.Hadamard
end
section
noncomputable section
open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem vbq
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (qv f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, qB m (z / qg p))
        z₀ = ((s.filter (fun p => qg p = z₀)).card : ℕ∞) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : qg p = z₀
    · have hp0 : qg p ≠ 0 := p.property
      have qby :
          AnalyticAt ℂ (fun z : ℂ => qB m (z / qg p)) z₀ := by
        exact (vay m p).analyticAt z₀
      have qbG : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, qB m
          (z / qg q)) z₀ := by
        simpa [q7] using! vbv m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => qB m (z / qg p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, qB m (z / qg q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) qby qbG)
      have hcard :
          (Finset.filter (fun q => qg q = z₀) (insert p s)).card =
            (Finset.filter (fun q => qg q = z₀) s).card + 1 := by
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (vcT (m := m) (a := qg p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter
          (fun q => qg q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, qB m (z / qg q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, qB m
            (z / qg q)) z₀ = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => qg q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => qg q = z₀)).card : ℕ∞) := by
              simp [hcard, Nat.add_comm]
    · have qby :
          AnalyticAt ℂ (fun z : ℂ => qB m (z / qg p)) z₀ := by
        exact (vay m p).analyticAt z₀
      have qiz : analyticOrderAt (fun z : ℂ => qB m
          (z / qg p)) z₀ = 0 := by
        have hp0 : qg p ≠ 0 := p.property
        have hval : qB m (z₀ / qg p) ≠ 0 := by
          have : (z₀ / qg p) ≠ 1 := by
            intro h1
            have : z₀ = qg p := by
              have : z₀ = (z₀ / qg p) * (qg p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          exact (vcK m (z₀ / qg p)).2 this
        simpa using (qby.analyticOrderAt_eq_zero).2 (by simpa using hval)
      have hcard :
          (Finset.filter (fun q => qg q = z₀) (insert p s)).card =
            (Finset.filter (fun q => qg q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      have qbG : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, qB m
          (z / qg q)) z₀ := by
        simpa [q7] using! vbv m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => qB m (z / qg p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, qB m (z / qg q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) qby qbG)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, qB m (z / qg q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, qB m
        (z / qg q)) z₀
            = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have qg7 : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using qiz
                      simp [qg7]
        _ = ((s.filter (fun q => qg q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => qg q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm
theorem vbS
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (qv f (Set.univ : Set ℂ)))
    (hs : qO (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, qB m (z / qg p))
        z₀ = ((qO (f := f) z₀).card : ℕ∞) := by
  have h :=
    vbq
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => qg p = z₀) =
        qO (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : qg p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [vai] using hpv
    · intro qfa
      have hpv : qg p = z₀ :=
        (vai (f := f) (z₀ := z₀) p).1 qfa
      have hps : p ∈ s := hs (by simpa [vai] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h
theorem vbx
  (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
  (s : Finset (qv f (Set.univ : Set ℂ)))
  (hs : qO (f := f) z₀ ⊆ s) :
  ∃ g : ℂ → ℂ,
   AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
    (fun z : ℂ => ∏ p ∈ s, qB m (z / qg p))
     =ᶠ[𝓝 z₀]
     fun z : ℂ => (z - z₀) ^ (qO (f := f) z₀).card • g z := by
 let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, qB m (z / qg p)
 have qg8 : AnalyticAt ℂ F z₀ := by
  simpa [F, q7] using! vbv m f s z₀
 have qg9 :
   analyticOrderAt F z₀ =
    ((qO (f := f) z₀).card : ℕ∞) := by
  simpa [F] using
   (vbS (m := m)
   (f := f) (z₀ := z₀) (s := s) hs)
 refine (qg8.analyticOrderAt_eq_natCast (n := (qO
  (f := f) z₀).card)).1 ?_
 simp [qg9]
end Complex.Hadamard
end
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem vbW
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  TendstoLocallyUniformlyOn
   (fun s : Finset (qv f (Set.univ : Set ℂ)) => q7 m f s)
   (qA m f (Set.univ : Set ℂ))
   Filter.atTop
   (Set.univ : Set ℂ) := by
 have hprod :
   HasProdLocallyUniformlyOn
    (fun (p : qv f (Set.univ : Set ℂ)) (z : ℂ) =>
     qB m (z / qg p))
    (qA m f (Set.univ : Set ℂ))
    (Set.univ : Set ℂ) :=
  vav (m := m) (f := f) h_sum
 simpa [HasProdLocallyUniformlyOn, q7] using! hprod
theorem vbY
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
  TendstoUniformlyOn
   (fun s z => (q7 m f s z) / (z - z₀) ^ k)
   (fun z => (qA m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
   (Filter.atTop : Filter (Finset (qv f (Set.univ : Set ℂ))))
   K := by
 have hloc :
   TendstoLocallyUniformlyOn
    (fun s : Finset (qv f (Set.univ : Set ℂ)) => q7 m f s)
    (qA m f (Set.univ : Set ℂ))
    Filter.atTop
    K :=
  (vbW (m := m) (f := f) h_sum).mono
   (by intro z hz; simp)
 have hunif :
   TendstoUniformlyOn
    (fun s : Finset (qv f (Set.univ : Set ℂ)) => q7 m f s)
    (qA m f (Set.univ : Set ℂ))
    Filter.atTop
    K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc
 let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
 have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
  have hcont : ContinuousOn h K := by
   have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
    fun_prop
   refine hpow.inv₀ ?_
   intro z hz
   have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
   exact pow_ne_zero k hz0
  have qiA : IsCompact (h '' K) := hK.image_of_continuousOn hcont
  rcases (isBounded_iff_forall_norm_le.1 qiA.isBounded) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro z hz
  exact hC (h z) ⟨z, hz, rfl⟩
 have qhb :=
  (TendstoUniformlyOn.vij (p := (Filter.atTop : Filter (Finset (qv f
  (Set.univ : Set ℂ)))))
    (K := K)
    (F := fun s z => q7 m f s z)
    (f := fun z => qA m f (Set.univ : Set ℂ) z)
    (h := h)
    hunif hh)
 simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using qhb
theorem vaN
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (z₀ : ℂ) (k : ℕ) :
  TendstoLocallyUniformlyOn
   (fun s z => (q7 m f s z) / (z - z₀) ^ k)
   (fun z => (qA m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
   (Filter.atTop : Filter (Finset (qv f (Set.univ : Set ℂ))))
   ((Set.univ : Set ℂ) \ {z₀}) := by
 have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
  have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
   ext z
   simp
  simp [hset]
 refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
 intro K hKsub hK
 have hKz : ∀ z ∈ K, z ≠ z₀ := by
  intro z hzK
  have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
  exact by simpa [Set.mem_sdiff, Set.mem_singleton_iff] using this.2
 exact vbY
  (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz
open Filter
theorem vbe
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (qA m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (qO (f := f) z₀).card =
            (vaf m f z₀ z) * u z := by
  let fiber : Finset (qv f (Set.univ : Set ℂ)) :=
    qO (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => q7 m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, q7] using
      (vbx (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, qk1⟩
  have hmem : {z : ℂ | q7 m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := qk1
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (q7 m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (qA m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (qv f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    vaN
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
          vah m f z₀ s)
        (vaf m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    vaK (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
          (q7 m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((qA m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
          vah m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (vaf m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
          (vah m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((vaf m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (qv f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := vdY (f := f) z₀
  have qb8 :
      ∀ᶠ s : Finset (qv f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (q7 m f s z) / (z - z₀) ^ fiber.card
          = (vah m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        q7 m f s z =
          q7 m f fiber z * vah m f z₀ s z := by
      simpa [fiber] using
        (vbL (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have qiB :
        q7 m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have qaJ : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using qaJ
    set c : ℂ := vah m f z₀ s z with hc
    rw [hsplit, qiB, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (vah m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (qv f (Set.univ : Set ℂ)) =>
          (q7 m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((vaf m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (qv f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (vah m f z₀ s z) * u z
            = (q7 m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [qb8] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'
theorem vbA
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, BddAbove (norm ∘ (fun z : ℂ =>
      (qA m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (qO (f := f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})) := by
  rcases vbe (m := m) (f := f) (h_sum := h_sum)
    (z₀ := z₀) with ⟨ε, hε, u, huA, hu0, hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, qU, qhc⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) qU
  have qfb : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have qgg : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := qhc hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]
  have qhd :
      DifferentiableOn ℂ (vaf m f z₀) (Set.univ : Set ℂ) :=
    vaW (m := m) (f := f) (z₀ := z₀) h_sum
  have qhe : ContinuousOn (vaf m f z₀) (Metric.closedBall z₀ r) :=
    (qhd.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn qhe).isBounded) with ⟨C, hC⟩
  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, qiC, rfl⟩
  rcases qiC with ⟨hzr, hzne⟩
  have qfc : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball qfb.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (qA m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (qO (f := f) z₀).card
        = vaf m f z₀ z * u z :=
    hEq z qfc hz_ne
  have hCz : ‖vaf m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := qgg z hzr
  have qfd : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖vaf m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖vaf m f z₀ z * u z‖
          = ‖vaf m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) qfd
  simpa [Function.comp, hq] using hmul
theorem vcG
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1))) :
    vaf m f z₀ z₀ ≠ 0 := by
  let Φ : qv f (Set.univ : Set ℂ) → ℂ :=
    fun p => if qg p = z₀ then (1 : ℂ)
      else qB m (z₀ / qg p)
  let a : qv f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1
  have qhf : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : qg p = z₀
    · simp [Φ, hp]
    · have hval : qg p ≠ z₀ := hp
      have hz : z₀ / qg p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : qg p = 0
        · have : z₀ / qg p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = qg p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : qB m (z₀ / qg p) ≠ 0 := by
        intro h0
        have : z₀ / qg p = (1 : ℂ) :=
          (vbf (m := m) (z := z₀ / qg p)).1 h0
        exact hz this
      simp [Φ, hp, hE]
  have qej : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have qG : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : qv f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖qg p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have qa1 :
      ∀ᶠ p : qv f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖qg p‖ := by
    have hfin : ({p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤
        2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vau (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖qg p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [qa1] with p hp
    have ha_pos : 0 < ‖qg p‖ := lt_trans (by nlinarith [qG]) hp
    have qbh : ‖z₀ / qg p‖ ≤ (1 / 2 : ℝ) := by
      have qaV : 0 < (2 * R : ℝ) := by nlinarith [qG]
      have hinv : ‖qg p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt qaV hp)
      have qaW : ‖z₀‖ * ‖qg p‖⁻¹ ≤ R * ‖qg p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact qej
      have hmul_lt : R * ‖qg p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv qG
      have hlt : ‖z₀‖ * ‖qg p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt qaW hmul_lt
      have qbg : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have qcH : (R : ℝ) ≠ 0 := qG.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [qcH]
      have hnorm : ‖z₀ / qg p‖ = ‖z₀‖ * ‖qg p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have qe9 : ‖z₀ / qg p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / qg p‖ = ‖z₀‖ * ‖qg p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := qbg
      exact le_of_lt qe9
    have hE :
        ‖qB m (z₀ / qg p) - 1‖ ≤
          4 * ‖z₀ / qg p‖ ^ (m + 1) :=
      vbj (m := m) (z := z₀ / qg p) qbh
    have hz_pow :
        ‖z₀ / qg p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖qg p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / qg p‖ = ‖z₀‖ * ‖qg p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖qg p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖qg p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have qcK : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) qej (m + 1)
      gcongr
    have hp_ne : qg p ≠ z₀ := by
      intro h
      have : ‖qg p‖ ≤ R := by
        simp [h, R]
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [qG]) hp)
    have ha : ‖a p‖ = ‖qB m (z₀ / qg p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg]
    calc
      ‖a p‖ = ‖qB m (z₀ / qg p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / qg p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖qg p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]
  have qek : Summable (fun p => ‖a p‖) := by
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp
  have qel :
      (∏' p : qv f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      simpa [a, Φ, add_sub_cancel] using qhf p) qek
  have : (∏' p : qv f (Set.univ : Set ℂ), (1 + a p)) =
      vaf m f z₀ z₀ := by
    simp [a, Φ, vaf, vfi]
  exact by
    intro h0
    exact qel (by simpa [this] using h0)
end Complex.Hadamard
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem vck
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (qv f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ (fun z : ℂ => (q7 m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have qbT : DifferentiableOn ℂ (q7 m f s) (Set.univ : Set ℂ) := by
    exact (vbN m f s).differentiableOn
  have qem : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k = 0
  · subst hk
    simpa [pow_zero] using! (qbT.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have qen :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      qem.inv hne
    simpa [div_eq_mul_inv] using! (qbT.mono (by intro z hz; exact hz.1)).mul qen
theorem vbX
  (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (z₀ : ℂ) (k : ℕ) : DifferentiableOn ℂ
   (fun z : ℂ => (qA m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
   ((Set.univ : Set ℂ) \ {z₀}) := by
 have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
  have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
   ext z; simp
  simp [hset]
 have hconv :=
  vaN
   (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
 refine hconv.differentiableOn ?_ hopen
 refine Filter.Eventually.of_forall ?_
 intro s
 exact vck (m := m) (f := f) (z₀ := z₀) (k := k) s
theorem vbw
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (z₀ : ℂ) : ∃ r > 0, DifferentiableOn ℂ (Function.update
     (fun z : ℂ => (qA m f (Set.univ : Set ℂ) z) /
      (z - z₀) ^ (qO (f := f) z₀).card) z₀
     (limUnder (𝓝[≠] z₀) (fun z : ℂ => (qA m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (qO (f := f) z₀).card)))
    (Metric.ball z₀ r) := by
 rcases vbA (m := m) (f := f)
   (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
 refine ⟨r, hrpos, ?_⟩
 have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
 have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
    (qA m f (Set.univ : Set ℂ) z) /
     (z - z₀) ^ (qO (f := f) z₀).card)
   ((Metric.ball z₀ r) \ {z₀}) := by
  have qdE :=
   vbX
    (m := m) (f := f) h_sum (z₀ := z₀)
    (k := (qO (f := f) z₀).card)
  refine qdE.mono ?_
  intro z hz
  exact ⟨by simp, hz.2⟩
 have hb : BddAbove (norm ∘ (fun z : ℂ => (qA m f (Set.univ : Set ℂ) z) /
   (z - z₀) ^ (qO (f := f) z₀).card) ''
  ((Metric.ball z₀ r) \ {z₀})) := hbdd
 simpa using
  (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
    (qA m f (Set.univ : Set ℂ) z) /
     (z - z₀) ^ (qO (f := f) z₀).card)
   (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)
theorem vbB
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z : ℂ =>
     (qA m f (Set.univ : Set ℂ) z) /
    (z - z₀) ^ (qO (f := f) z₀).card) z₀
    (limUnder (𝓝[≠] z₀) (fun z : ℂ => (qA m f (Set.univ : Set ℂ) z) /
       (z - z₀) ^ (qO (f := f) z₀).card)))
   z₀ := by
 rcases
   vbw
    (m := m) (f := f) h_sum (z₀ := z₀) with ⟨r, hrpos, hdiff⟩
 let g : ℂ → ℂ :=
  Function.update
   (fun z : ℂ =>
    (qA m f (Set.univ : Set ℂ) z) /
     (z - z₀) ^ (qO (f := f) z₀).card)
   z₀
   (limUnder (𝓝[≠] z₀) fun z : ℂ =>
    (qA m f (Set.univ : Set ℂ) z) /
     (z - z₀) ^ (qO (f := f) z₀).card)
 have hcont : ContinuousAt g z₀ :=
  (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
 have hd :
   ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
  have qdb : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
   refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
   refine ⟨Metric.ball z₀ r, Metric.ball_mem_nhds z₀ hrpos, ?_⟩
   intro z hz
   exact hz.1
  filter_upwards [qdb] with z hz
  exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
 simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont
theorem vci
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ q : ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z : ℂ =>
            (qA m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (qO (f := f) z₀).card) ∧
        ∀ z : ℂ, z ≠ z₀ →
          q z =
            (qA m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (qO (f := f) z₀).card := by
  let q : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (qA m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (qO (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (qA m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (qO (f := f) z₀).card)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      vbB
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q, Function.update_of_ne hz]
theorem vaU
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z₀ =
      (qO (f := f) z₀).card := by
  set k : ℕ := (qO (f := f) z₀).card
  let F : ℂ → ℂ := qA m f (Set.univ : Set ℂ)
  let q0 : ℂ → ℂ := fun z => F z / (z - z₀) ^ k
  rcases vci
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) with
    ⟨q, hqA, qgh, hq_ne⟩
  have qbU : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    vaw (m := m) (f := f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z := qbU z (by simp)
    exact this.differentiableAt (by simp)
  rcases
      vbe (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
    with ⟨ε, hε, u, huA, hu0, hEq⟩
  let g : ℂ → ℂ := fun z => (vaf m f z₀ z) * u z
  have qeo : DifferentiableOn ℂ (vaf m f z₀)
      (Set.univ : Set ℂ) :=
    vaW (m := m) (f := f) (z₀ := z₀) h_sum
  have qep : ContinuousAt (vaf m f z₀) z₀ :=
    (qeo z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have qhg : ContinuousAt g z₀ := (qep.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0 := by
    have qhh : vaf m f z₀ z₀ ≠ 0 :=
      vcG (m := m) (f := f) (z₀ := z₀) h_sum
    exact mul_ne_zero qhh hu0
  have qgi : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
    filter_upwards [qgi] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz
  have qiD : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)) := by
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hball, hne] with z hz hzne
      have hq := hEq z hz hzne
      simpa [q0, F, k, g, smul_eq_mul] using hq
    exact (qhg.continuousWithinAt.tendsto.congr' heq.symm)
  have hlim : limUnder (𝓝[≠] z₀) q0 = g z₀ := qiD.limUnder_eq
  have hq0 : q z₀ ≠ 0 := by
    have qfe : q z₀ = limUnder (𝓝[≠] z₀) q0 := by
      simpa [q0, F, k] using qgh
    have : q z₀ = g z₀ := qfe.trans hlim
    exact this.symm ▸ hg0
  have qeq : (fun z : ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z : ℂ => (z - z₀) ^ k • q z := by
    filter_upwards [hne] with z hz
    have qaJ : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz
    have hmul : (z - z₀) ^ k * q0 z = F z := by
      calc
        (z - z₀) ^ k * q0 z
            = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                simp [q0, div_eq_mul_inv, mul_assoc]
        _ = F z := by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) qaJ)
    have : F z = (z - z₀) ^ k * q z := by
      calc
        F z = (z - z₀) ^ k * q0 z := hmul.symm
        _ = (z - z₀) ^ k * q z := by simp [hq]
    simpa [smul_eq_mul] using this
  have qhi : ContinuousAt F z₀ :=
    (qbU z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have qhj : ContinuousAt q z₀ := hqA.continuousAt
  have qgj : F z₀ = (z₀ - z₀) ^ k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := qhi.continuousWithinAt.tendsto
    have hpow :
        Tendsto (fun z : ℂ => (z - z₀) ^ k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z : ℂ => (z - z₀) ^ k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      hpow.mul (qhj.continuousWithinAt.tendsto)
    have qk2 : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      ht2.congr' qeq.symm
    exact tendsto_nhds_unique ht1 qk2
  have hfac : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ k • q z := by
    have qhk : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have qgk : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem qhk (fun _ hz => hz)
    filter_upwards [qgk] with z _hz
    by_cases hz0 : z = z₀
    · subst hz0
      simpa using qgj
    · have qaJ : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz0
      have hmul : (z - z₀) ^ k * q0 z = F z := by
        calc
          (z - z₀) ^ k * q0 z
              = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                  simp [q0, div_eq_mul_inv, mul_assoc]
          _ = F z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) qaJ)
      have : F z = (z - z₀) ^ k * q z := by
        calc
          F z = (z - z₀) ^ k * q0 z := hmul.symm
          _ = (z - z₀) ^ k * q z := by simp [hq]
      simpa [smul_eq_mul] using this
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨q, hqA, hq0, hfac⟩
  have qiE : analyticOrderNatAt F z₀ = k := by
    simp [analyticOrderNatAt, hk']
  simpa [F, k] using qiE
theorem vaI
  (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
  analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z₀ =
   analyticOrderNatAt f z₀ := by
 have hcp :
   analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z₀ =
    (qO (f := f) z₀).card :=
  vaU (m := m) (f := f) (h_sum := h_sum)
   (z₀ := z₀)
 have hfib :
   (qO (f := f) z₀).card = analyticOrderNatAt f z₀ :=
  vaC (hf := hf) (z₀ := z₀) hz₀
 simpa [hfib] using hcp
end Complex.Hadamard
end
section
namespace Complex.Hadamard
open scoped Topology
open Set
lemma vak {f : ℂ → ℂ} (hf : Differentiable ℂ f)
  (hnot : ∃ z : ℂ, f z ≠ 0) :
  ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
 rcases hnot with ⟨z1, hz1⟩
 have qiF : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
  intro z hz
  exact (Differentiable.analyticAt (f := f) hf z)
 have qdc : analyticOrderAt f z1 ≠ ⊤ := by
  have : analyticOrderAt f z1 = 0 :=
   (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
  simp [this]
 intro z
 exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := qiF)
  (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
  (by simp) (by simp) qdc
lemma vdn
  {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
  {B r : ℝ} (hrpos : 0 < r) (hBr : r ≤ B) (qcM : ∀ p : qv f (Set.univ : Set ℂ),
   ‖qg p‖ ≤ B → r ≠ ‖qg p‖) :
  ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
 intro u hur
 have hu0 : u ≠ 0 := by
  intro hu0
  subst hu0
  have : (0 : ℝ) = r := by simpa using hur
  exact (ne_of_gt hrpos) this.symm
 intro qk3
 have qb9 : analyticOrderAt f u ≠ ⊤ :=
  vak (f := f) hf hnot u
 have qff : analyticOrderNatAt f u ≠ 0 := by
  intro h0
  have hEN : (analyticOrderNatAt f u : ENat) = 0 := by simp [h0]
  have qk4 : analyticOrderAt f u = 0 := by
   have hcast : (analyticOrderNatAt f u : ENat) = analyticOrderAt f u :=
    Nat.cast_analyticOrderNatAt (f := f) (z₀ := u) qb9
   simpa [hcast] using hEN
  have han : AnalyticAt ℂ f u := Differentiable.analyticAt (f := f) hf u
  exact ((han.analyticOrderAt_eq_zero).1 qk4) qk3
 have hcard_pos : 0 < (qO (f := f) u).card := by
  have hcard :=
   vaC (hf := hf) (z₀ := u) hu0
  have : 0 < analyticOrderNatAt f u := Nat.pos_of_ne_zero qff
  simpa [hcard] using this
 rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
 have qfV : qg p = u :=
  (vai (f := f) (z₀ := u) p).1 hp
 have hpB : ‖qg p‖ ≤ B := by
  have : ‖qg p‖ = r := by simp [qfV, hur]
  simpa [this] using hBr
 have : r ≠ ‖qg p‖ := qcM p hpB
 exact this (by simp [qfV, hur])
theorem vbT
  (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (z₀ : ℂ) :
  analyticOrderAt (qA m f (Set.univ : Set ℂ)) z₀ =
   ((qO (f := f) z₀).card : ℕ∞) := by
 let F : ℂ → ℂ := qA m f (Set.univ : Set ℂ)
 have hNat :
   analyticOrderNatAt F z₀ = (qO (f := f) z₀).card := by
  simpa [F] using
   (vaU
    (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀))
 have qca : DifferentiableOn ℂ F (Set.univ : Set ℂ) := by
  simpa [F] using vaw (m := m) (f := f) h_sum
 have hdiff : Differentiable ℂ F := by
  intro z
  exact (qca z (by simp)).differentiableAt (by simp)
 have qb9 : analyticOrderAt F z₀ ≠ ⊤ :=
  vak (hf := hdiff)
   ⟨0, by simp [F, vaD]⟩ z₀
 have hcast : (analyticOrderNatAt F z₀ : ℕ∞) = analyticOrderAt F z₀ :=
  Nat.cast_analyticOrderNatAt (f := F) (z₀ := z₀) qb9
 have qfg :
   (analyticOrderNatAt F z₀ : ℕ∞) =
    ((qO (f := f) z₀).card : ℕ∞) := by
  simp [hNat]
 simpa [F, hcast] using qfg
theorem vbp
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : ∀ p : qv f (Set.univ : Set ℂ), z ≠ qg p) :
    qA m f (Set.univ : Set ℂ) z ≠ 0 := by
  let F : ℂ → ℂ := qA m f (Set.univ : Set ℂ)
  have qcN : qO (f := f) z = ∅ := by
    ext p
    constructor
    · intro hp
      exact False.elim (hz p ((vai (f := f) (z₀ := z) p).1 hp).symm)
    · intro hp
      simp at hp
  have horder :
      analyticOrderAt F z = (0 : ℕ∞) := by
    have h :=
      vbT
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z)
    simpa [F, qcN] using h
  have han : AnalyticAt ℂ F z := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    exact (((vaw m f h_sum) w
      (by simp)).differentiableAt (by simp))
  exact (han.analyticOrderAt_eq_zero).1 horder
theorem vbE
  {f : ℂ → ℂ} {z : ℂ}
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (2 : ℕ)))
  (hz : ∀ p : qv f (Set.univ : Set ℂ), z ≠ qg p) :
  logDeriv (qA 1 f (Set.univ : Set ℂ)) z =
   ∑' p : qv f (Set.univ : Set ℂ),
    (1 / (z - qg p) + 1 / qg p) :=
 vcH h_sum hz
  (vbp 1 f h_sum hz)
end Hadamard
end Complex
end
section
namespace Complex.Hadamard
open Filter Topology Set Complex
open scoped BigOperators Topology
noncomputable def qW (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
 z ^ (analyticOrderNatAt f 0) * qA m f (Set.univ : Set ℂ) z
theorem vas (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  Differentiable ℂ (qA m f (Set.univ : Set ℂ)) := by
 intro z
 have qca :
   DifferentiableOn ℂ (qA m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
  vaw (m := m) (f := f) h_sum
 exact (qca z (by simp)).differentiableAt (by simp)
theorem vaZ (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) (z : ℂ) :
  AnalyticAt ℂ (qA m f (Set.univ : Set ℂ)) z :=
 (vas m f h_sum).analyticAt z
theorem vbG (m : ℕ) (f : ℂ → ℂ)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  Differentiable ℂ (qW m f) := by
 have qhn : Differentiable ℂ (qA m f (Set.univ : Set ℂ)) := by
  exact vas m f h_sum
 simpa [qW] using! (differentiable_id.pow (analyticOrderNatAt f 0)).mul qhn
theorem vdR {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1))) {z : ℂ} (hz : f z ≠ 0) : qW m f z ≠ 0 := by
  have qdF : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    vak (hf := hf) hnot
  have qiG : AnalyticAt ℂ f z := hf.analyticAt z
  have qcO : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (qiG.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (qdF z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have qer : AnalyticAt ℂ (qA m f (Set.univ : Set ℂ)) z := by
    exact vaZ m f h_sum z
  by_cases hz0 : z = 0
  · subst hz0
    have qiH : analyticOrderNatAt f 0 = 0 := by simpa using qcO
    simp [qW, qiH, vaD]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have qcP :
        analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [qcO] using
        (vaI (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have qes : qA m f (Set.univ : Set ℂ) z ≠ 0 := by
      have qas :
          Differentiable ℂ (qA m f (Set.univ : Set ℂ)) := by
        exact vas m f h_sum
      have qaf :
          analyticOrderAt (qA m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        vak (hf := qas)
          ⟨0, by simp [vaD]⟩ z
      have qdd :
          (analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (qA m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := qA m f (Set.univ : Set ℂ)) (z₀ := z) qaf
      have : analyticOrderAt (qA m f (Set.univ : Set ℂ)) z = 0 := by
        have :
            (analyticOrderNatAt
              (qA m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast qcP
        simp [qdd] at this
        simpa using this
      exact (qer.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp qes
lemma vcv
  (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) 0 = 0 := by
 have qas :
   Differentiable ℂ (qA m f (Set.univ : Set ℂ)) := by
  exact vas m f h_sum
 have qaf :
   analyticOrderAt (qA m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
  vak (hf := qas)
   ⟨0, by simp [vaD]⟩ 0
 have qaX : AnalyticAt ℂ (qA m f (Set.univ : Set ℂ)) 0 :=
  qas.analyticAt 0
 have qcb : qA m f (Set.univ : Set ℂ) 0 ≠ 0 := by
  simp [vaD]
 have : analyticOrderAt (qA m f (Set.univ : Set ℂ)) 0 = 0 :=
  (qaX.analyticOrderAt_eq_zero).2 qcb
 have hcast :
   (analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
    analyticOrderAt (qA m f (Set.univ : Set ℂ)) 0 :=
  Nat.cast_analyticOrderNatAt
   (f := qA m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) qaf
 have :
   (analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
    0 := by
  simp [hcast, this]
 exact_mod_cast this
theorem veb
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (qW m f) z = analyticOrderNatAt f z := by
  by_cases hz0 : z = 0
  · subst hz0
    have qcA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have qaw :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      vak
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ 0
    have qaX : AnalyticAt ℂ (qA m f (Set.univ : Set ℂ)) 0 := by
      exact vaZ m f h_sum 0
    have qcb :
        analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) 0 = 0 :=
      vcv (m := m) (f := f) h_sum
    have qk5 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have qdG : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using
          (vax
            (f := fun z : ℂ => z) qdG 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using
          (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ))
            (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have qdH :
        analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 =
          analyticOrderNatAt f 0 := by
      have qk6 : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [qk5] using! (analyticOrderNatAt_pow (hf := qk6) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (qW m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) 0 := by
      have qbV :
          analyticOrderAt (qA m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        vak
          (hf := vas m f h_sum)
          ⟨0, by simp [vaD]⟩ 0
      simpa [qW] using!
        analyticOrderNatAt_mul (hf := qcA) (hg := qaX)
          (hf' := qaw) (hg' := qbV)
    simp [hmul, qdH, qcb]
  · have qcA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have qaw :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      vak
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ z
    have qdH : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((qcA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt
          (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) qaw
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have qet :
        analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z =
          analyticOrderNatAt f z :=
      vaI
        (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have qaX : AnalyticAt ℂ (qA m f (Set.univ : Set ℂ)) z := by
      exact vaZ m f h_sum z
    have qaf :
        analyticOrderAt (qA m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      vak
        (hf := vas m f h_sum)
        ⟨0, by simp [vaD]⟩ z
    have hmul :
        analyticOrderNatAt (qW m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (qA m f (Set.univ : Set ℂ)) z := by
      simpa [qW] using!
        analyticOrderNatAt_mul (hf := qcA) (hg := qaX)
          (hf' := qaw) (hg' := qaf)
    simp [hmul, qdH, qet]
theorem vfQ
  (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1))) :
  MeromorphicOn.divisor (qW m f) (Set.univ : Set ℂ) =
   MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
 ext z
 have qX : Differentiable ℂ (qW m f) :=
  vbG (m := m) f h_sum
 have qeu : Differentiable ℂ f := hf
 have hden :
   (MeromorphicOn.divisor (qW m f) (Set.univ : Set ℂ)) z =
    (analyticOrderNatAt (qW m f) z : ℤ) := by
  simpa using (vax (f := qW m f) qX z)
 have hfz :
   (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
    (analyticOrderNatAt f z : ℤ) := by
  simpa using (vax (f := f) qeu z)
 simp [hden, hfz, veb (m := m) (hf := hf) (h_sum := h_sum) z]
theorem vey
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (fun z : ℂ => f z / qW m f z) (Set.univ : Set ℂ) = 0 := by
  have qcc : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have qX : Differentiable ℂ (qW m f) :=
    vbG (m := m) f h_sum
  have qaP : MeromorphicOn (qW m f) (Set.univ : Set ℂ) := by
    intro z hz
    exact (qX.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1, hz1⟩
  have qa2 : qW m f z1 ≠ 0 :=
    vdR (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have qbW : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have qax : meromorphicOrderAt f z1 ≠ ⊤ := by
      have qk7 : MeromorphicAt f z1 := qcc z1 (by simp)
      have hcont : ContinuousAt f z1 := (hf.differentiableAt).continuousAt
      have qaL : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hz1
      have qay : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds qaL
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := qk7)).2 qay
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := qcc)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) qax
  have qe4 :
      ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (qW m f) z ≠ ⊤ := by
    intro z hzU
    have qax : meromorphicOrderAt (qW m f) z1 ≠ ⊤ := by
      have qho : MeromorphicAt (qW m f) z1 := qaP z1 (by simp)
      have hcont : ContinuousAt (qW m f) z1 :=
        (qX.differentiableAt).continuousAt
      have qaL : ∀ᶠ w in 𝓝 z1, qW m f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 qa2
      have qay : ∀ᶠ w in 𝓝[≠] z1, qW m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds qaL
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := qho)).2 qay
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := qaP)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) qax
  have qbA :
      ∀ z ∈ (Set.univ : Set ℂ),
        meromorphicOrderAt (fun z : ℂ => (qW m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have qcn :
        MeromorphicOn (fun z : ℂ => (qW m f z)⁻¹) (Set.univ : Set ℂ) :=
      qaP.inv
    have qax :
        meromorphicOrderAt (fun z : ℂ => (qW m f z)⁻¹) z1 ≠ ⊤ := by
      have qhp : MeromorphicAt (fun z : ℂ => (qW m f z)⁻¹) z1 :=
        qcn z1 (by simp)
      have qde : ContinuousAt (qW m f) z1 :=
        (qX.differentiableAt).continuousAt
      have hcont : ContinuousAt (fun z : ℂ => (qW m f z)⁻¹) z1 :=
        qde.inv₀ qa2
      have hinv1 : (fun z : ℂ => (qW m f z)⁻¹) z1 ≠ 0 := by
        simpa using inv_ne_zero qa2
      have qaL :
          ∀ᶠ w in 𝓝 z1, (fun z : ℂ => (qW m f z)⁻¹) w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hinv1
      have qay :
          ∀ᶠ w in 𝓝[≠] z1, (fun z : ℂ => (qW m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds qaL
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := qhp)).2 qay
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := qcn)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) qax
  have qdI : MeromorphicOn.divisor (qW m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    vfQ (m := m) (hf := hf) (h_sum := h_sum)
  calc
    MeromorphicOn.divisor (fun z : ℂ => f z / qW m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor
            (fun z : ℂ => f z * (qW m f z)⁻¹) (Set.univ : Set ℂ) := by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z : ℂ => (qW m f z)⁻¹) (Set.univ : Set ℂ) := by
          simpa using (MeromorphicOn.divisor_fun_mul (U := (Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (qW m f z)⁻¹) qcc (qaP.inv)
            qbW qbA)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) -
          MeromorphicOn.divisor (qW m f) (Set.univ : Set ℂ) := by
          simp [sub_eq_add_neg]
    _ = 0 := by
          simp [qdI]
theorem vdx
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
      H z * z ^ (analyticOrderNatAt f 0) * qA m f (Set.univ : Set ℂ) z := by
  let denom : ℂ → ℂ := qW m f
  let q : ℂ → ℂ := fun z => f z / denom z
  have qX : Differentiable ℂ denom :=
    vbG (m := m) f h_sum
  have qcd : MeromorphicOn q (Set.univ : Set ℂ) := by
    intro z hzU
    have hf_m : MeromorphicAt f z := (hf.analyticAt z).meromorphicAt
    have qhq : MeromorphicAt denom z := (qX.analyticAt z).meromorphicAt
    simpa [q, denom, div_eq_mul_inv] using! (hf_m.mul qhq.inv)
  let H : ℂ → ℂ := toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have qdJ : MeromorphicOn.divisor H (Set.univ : Set ℂ) = 0 := by
    have hdivq : MeromorphicOn.divisor q (Set.univ : Set ℂ) = 0 :=
      vey (m := m) (f := f) (hf := hf)
        (hnot := hnot) (h_sum := h_sum)
    simpa [H, hdivq] using
      (MeromorphicOn.divisor_of_toMeromorphicNFOn
        (f := q) (U := (Set.univ : Set ℂ)) qcd)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ) := by
    have :
        (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤
          MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      simp [qdJ]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f := hNF)).1 (by simp [qdJ])
  have qai : Differentiable ℂ H := by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1, hz1⟩
  have qa2 : denom z1 ≠ 0 :=
    vdR (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have qk8 : AnalyticAt ℂ q z1 := by
    have qhr : AnalyticAt ℂ denom z1 := qX.analyticAt z1
    exact (hf.analyticAt z1).div qhr qa2
  have qiI : MeromorphicNFAt q z1 := qk8.meromorphicNFAt
  have qfW : toMeromorphicNFAt q z1 = q := (toMeromorphicNFAt_eq_self (f := q) (x := z1)).2 qiI
  have hH1 : H z1 = q z1 := by
    have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1 = toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := q) (U := (Set.univ : Set ℂ)) qcd hx)
    simpa [H, qfW] using this
  have qhs : H z1 ≠ 0 := by
    have : q z1 ≠ 0 := div_ne_zero hz1 qa2
    simpa [hH1] using this
  have qdK : ∀ z : ℂ, analyticOrderAt H z ≠ ⊤ := by
    exact vak (hf := qai) ⟨z1, qhs⟩
  have qbH : ∀ z : ℂ, analyticOrderNatAt H z = 0 := by
    intro z
    have qiJ :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = (analyticOrderNatAt H z : ℤ) := by
      simpa using (vax (f := H) qai z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = 0 := by
      simp [qdJ]
    have : (analyticOrderNatAt H z : ℤ) = 0 := by simpa [qiJ] using this
    exact_mod_cast this
  have qdL : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hcast : (analyticOrderNatAt H z : ℕ∞) = analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f := H) (z₀ := z) (qdK z)
    have : analyticOrderAt H z = 0 := by
      have : (analyticOrderNatAt H z : ℕ∞) = 0 := by exact_mod_cast (qbH z)
      simpa [hcast] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z hzU => hf.analyticAt z
  have qiK : AnalyticOnNhd ℂ denom (Set.univ : Set ℂ) := fun z hzU => qX.analyticAt z
  have qht : AnalyticOnNhd ℂ (fun z => H z * denom z) (Set.univ : Set ℂ) :=
    (hA.mul qiK)
  have hlocal : f =ᶠ[𝓝 z1] fun z => H z * denom z := by
    have qce : ∀ᶠ z in 𝓝 z1, denom z ≠ 0 :=
      (qX.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 qa2
    have qgl : H =ᶠ[𝓝 z1] q := by
      have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hloc :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1 := by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f := q)
          (U := (Set.univ : Set ℂ)) qcd hx)
      simpa [H, qfW] using hloc
    filter_upwards [qce, qgl] with z qiL hHz
    have hcancel : q z * denom z = f z := by
      dsimp [q]
      field_simp [qiL]
    calc
      f z = q z * denom z := hcancel.symm
      _ = H z * denom z := by simp [hHz]
  have qdE : f = fun z => H z * denom z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf := hfA) (hg := qht) hlocal
  refine ⟨H, qai, qdL, ?_⟩
  intro z
  have qhu : f z = H z * denom z := congrArg (fun g => g z) qdE
  simpa [denom, qW, mul_assoc, mul_left_comm, mul_comm] using qhu
end Complex.Hadamard
end
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
lemma vaB {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
  (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
 have qag : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
 simpa [mem_closedBall, dist_zero_right] using qag
lemma vaO {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
  (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
 have qag : z ∈ closedBall (0 : E) |r| := by
  simpa [mem_closedBall, dist_zero_right] using hz
 simpa using toClosedBall_eval_within (f := D) qag
lemma vaX
  {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
  z ∈ (toClosedBall r D).support := by
 rw [Function.mem_support]
 rw [vaO hzR]
 rwa [Function.mem_support] at hzD
lemma vdr {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
  (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
 have hnorm : ‖z‖ ≤ |r| := vaB hz
 rw [Function.mem_support] at hz ⊢
 rw [vaO hnorm] at hz
 exact hz
noncomputable def vbm {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
 classical
 exact
  (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
   (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
theorem vbu
  {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
  logCounting (divisor f ⊤) R =
   circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
 have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
 simpa [top_eq_univ] using
  logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR
end Function.locallyFinsuppWithin
end
section
namespace Real
theorem veK {x : ℝ} (hx : 0 ≤ x) :
    log (1 + exp x) ≤ x + log 2 := by
  have qk9 : (1 : ℝ) ≤ exp x := by
    simpa using (one_le_exp_iff.2 hx)
  have hadd : 1 + exp x ≤ 2 * exp x := by linarith
  have hlog : log (1 + exp x) ≤ log (2 * exp x) :=
    log_le_log (by positivity) hadd
  calc
    log (1 + exp x) ≤ log (2 * exp x) := hlog
    _ = log 2 + x := by simp [log_mul, add_comm]
    _ = x + log 2 := by ring
theorem vdL {x y : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x)
  (hxy : y ≤ exp x) :
  log (1 + y) ≤ x + log 2 := by
 have hpos : 0 < (1 : ℝ) + y := by linarith
 have hle : (1 : ℝ) + y ≤ 1 + exp x := by linarith
 exact (log_le_log hpos hle).trans (veK hx)
theorem vfS {x y : ℝ} (hy : 0 ≤ y) (hxy : log (1 + y) ≤ x) :
  y ≤ exp x := by
 have hpos : 0 < (1 : ℝ) + y := by linarith
 have hone : 1 + y ≤ exp x := (log_le_iff_le_exp hpos).1 hxy
 linarith
theorem vgA (x : ℝ) : -log⁺ x⁻¹ ≤ log x := by
 linarith [posLog_sub_posLog_inv (x := x), posLog_nonneg (x := x)]
end Real
end
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
theorem vfe (w : E) :
    Real.log ‖w‖ ≤ Real.log (1 + ‖w‖) := by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log hpos (by linarith [norm_nonneg w])
variable {F : Type*} [NormedAddCommGroup F]
theorem ven {z : F} {r : ℝ} (hz : ‖z‖ ≤ r) :
    0 ≤ Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1 : ℝ) ≤ r / ‖z‖ := (one_le_div hzpos).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this
theorem vcx {z : F} {R : ℝ} (hz0 : z ≠ 0)
  (hz : ‖z‖ ≤ R) :
  Real.log 2 ≤ Real.log ((2 * R) * ‖z‖⁻¹) := by
 have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
 have qp2 : (1 : ℝ) ≤ R / ‖z‖ := (one_le_div hzpos).2 hz
 have hle2 : (2 : ℝ) ≤ (2 * R) * ‖z‖⁻¹ := by
  have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
 exact Real.log_le_log (by norm_num) hle2
theorem vea
  {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (qdM : ρ ≤ τ)
  (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ ρ)) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
 intro x
 refine (hbound x).trans (Real.exp_le_exp.2 ?_)
 exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hr x) qdM) hC
theorem vel
  {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (qdM : ρ ≤ τ)
  (hlog : ∀ x, Real.log (1 + ‖f x‖) ≤ C * (r x) ^ ρ) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
 intro x
 have hpow : (r x) ^ ρ ≤ (r x) ^ τ :=
  Real.rpow_le_rpow_of_exponent_le (hr x) qdM
 have qhv : Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ :=
  (hlog x).trans (mul_le_mul_of_nonneg_left hpow hC)
 exact Real.vfS (norm_nonneg (f x)) qhv
theorem vcc
  {f : α → E} {r : α → ℝ} {C τ : ℝ} (hC : 0 < C) (hτ : 0 ≤ τ)
  (hr : ∀ x, 1 ≤ r x) (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
  ∃ C' > 0, ∀ x, Real.log (1 + ‖f x‖) ≤ C' * (r x) ^ τ := by
 refine ⟨C + Real.log 2, by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith, ?_⟩
 intro x
 have hX : (1 : ℝ) ≤ (r x) ^ τ := Real.one_le_rpow (hr x) hτ
 have hB : 0 ≤ C * (r x) ^ τ :=
  mul_nonneg hC.le (Real.rpow_nonneg (le_trans zero_le_one (hr x)) _)
 have hlog :
   Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ + Real.log 2 :=
  Real.vdL (norm_nonneg _) hB (hbound x)
 have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
 nlinarith [hlog, hX, hlog2_nonneg]
theorem vdh
  {f : α → E} {r : α → ℝ} {τ : ℝ} {n : ℕ} (hr : ∀ x, 1 ≤ r x) (hτn : τ < (n : ℝ))
  (hbound : ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
  ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ n) := by
 rcases hbound with ⟨C, hCpos, hC⟩
 have hweak :
   ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ (n : ℝ)) :=
  vea
   (f := f) (r := r) hCpos.le hr (le_of_lt hτn) hC
 refine ⟨C, hCpos, ?_⟩
 intro x
 have hpow : (r x) ^ (n : ℝ) = (r x) ^ n := Real.rpow_natCast (r x) n
 simpa [hpow] using hweak x
theorem vcA {x r : ℝ} (hx : 0 ≤ x)
  (hr : r ≤ 2 * max x 1) :  1 + r ≤ 3 * (1 + x) := by
 have hmax : max x 1 ≤ 1 + x := max_le_iff.2 ⟨by linarith, by linarith⟩
 nlinarith
theorem vdv
  {A B x y τ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y)
  (hτ : 0 ≤ τ) (hxy : x ≤ B * y) : Real.exp (A * x ^ τ) ≤ Real.exp ((A * B ^ τ) * y ^ τ) := by
 refine Real.exp_le_exp.2 ?_
 have hpow : x ^ τ ≤ (B * y) ^ τ := Real.rpow_le_rpow hx hxy hτ
 have hsplit : (B * y) ^ τ = B ^ τ * y ^ τ := by
  simpa using (Real.mul_rpow (x := B) (y := y) (z := τ) hB hy)
 simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hpow.trans_eq hsplit) hA
theorem vaH {ρ : ℝ} (hρ : 0 ≤ ρ) :
  ∃ τ : ℝ, ρ < τ ∧ τ < (Nat.floor ρ + 1 : ℝ) ∧ 0 ≤ τ ∧ Nat.floor τ = Nat.floor ρ := by
 set m : ℕ := Nat.floor ρ
 set τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
 have hm : ρ < (m + 1 : ℝ) := by simpa [m] using Nat.lt_floor_add_one (a := ρ)
 have hτ : ρ < τ := by dsimp [τ]; linarith
 have qak : τ < (m + 1 : ℝ) := by dsimp [τ]; linarith
 have qz : 0 ≤ τ := le_trans hρ (le_of_lt hτ)
 have qam : Nat.floor τ = m := by
  have qfh : (m : ℝ) ≤ τ := le_trans (Nat.floor_le hρ) (le_of_lt hτ)
  have qex : τ < (m : ℝ) + 1 := by simpa [add_assoc, add_comm, add_left_comm] using qak
  exact (Nat.floor_eq_iff qz).2 ⟨qfh, qex⟩
 exact ⟨τ, hτ, by simpa [m] using qak, qz, by simpa [m] using qam⟩
open Metric Complex
theorem vcN {f : ℂ → ℂ} {C ρ R : ℝ}
  (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {z : ℂ}
  (hz : z ∈ sphere (0 : ℂ) |R|) : log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
 have hz_norm : ‖z‖ = |R| := by
  simpa [mem_sphere, dist_zero_right] using hz
 simpa [hz_norm] using le_trans (vfe (f z)) (hC z)
end Real
end
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
theorem vdN {f : ℂ → ℂ} {ρ C : ℝ} (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR0 : 0 < R) :
    logCounting (divisor f (Set.univ : Set ℂ)) R
      ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq :=
    vbu (f := f) hf hR
  have qey : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm qey
  have qct : ∀ z ∈ sphere (0 : ℂ) |R|,
      log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    exact vcN hC hz
  have qcu :
      circleAverage (fun z : ℂ => log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => log ‖f z‖) hInt qct
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z : ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z : ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [qcu]
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
theorem vcI {D : locallyFinsupp E ℤ} (qat : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * vbm D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  let Dr := toClosedBall r D
  have qbz : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E := qbz.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E := SR.filter fun z => z ≠ (0 : E)
  have hS_sub : S ⊆ F := by
    intro z hzS
    have qbi : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support := by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        qbi
    have qaz : ‖z‖ ≤ R := by
      have := vaB hzR
      simpa [abs_of_pos hR0] using this
    have qcQ : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans qaz (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support := vdr hzR
    have : z ∈ Dr.support := by
      simpa [Dr] using
        vaX (D := D) (r := r) hzD qcQ
    exact qbz.mem_toFinset.2 this
  have qcR :
      logCounting D r
        = (F.sum fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    have hsupp : Function.support (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact qbz.mem_toFinset.2 this
    simp [logCounting, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (log 2) * (S.sum fun z => (D z : ℝ))
        ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzF
      have qez : z ∈ Dr.support := qbz.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z := by
        have qla : 0 ≤ D z := qat z
        have qfi : Dr z = D z :=
          vaO (vaB qez)
        simpa [qfi] using qla
      have hlog : 0 ≤ log (r * ‖z‖⁻¹) := by
        have qa0 : ‖z‖ ≤ r := by
          have hnorm := vaB qez
          simpa [abs_of_pos hrpos] using hnorm
        exact ven qa0
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have qhx :
        S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF _; exact hterm_nonneg z hzF)
    have qfj : ∀ z ∈ S, (log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ (0 : E) := (Finset.mem_filter.1 hzS).2
      have qaz : ‖z‖ ≤ R := by
        have qbi : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have qhy : z ∈ (toClosedBall R D).support := by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            qbi
        have hnorm := vaB qhy
        simpa [abs_of_pos hR0] using hnorm
      have hlog_le : log 2 ≤ log (r * ‖z‖⁻¹) := by
        simpa [r] using vcx hz0 qaz
      have qa3 : 0 ≤ D z := qat z
      have qdg : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r := le_trans qaz (by dsimp [r]; nlinarith)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have qfi : Dr z = D z := by
        have qdN : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall, dist_zero_right] using qdg
        simpa [Dr] using vaO (D := D) (r := r) (z := z) qdN
      have : (log 2) * (D z : ℝ) ≤ (log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast qa3)
      simpa [qfi, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (log 2) * (S.sum fun z => (D z : ℝ))
          = S.sum (fun z => (log 2) * (D z : ℝ)) := by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => qfj z hz
      _ ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := qhx
  have qcf : 0 ≤ (D 0 : ℝ) * log r := by
    have hD0 : 0 ≤ D 0 := qat 0
    have hlogr : 0 ≤ log r := log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (log 2) * (S.sum fun z => (D z : ℝ)) ≤ logCounting D r := by
    rw [qcR]
    nlinarith [hsum_le, qcf]
  simpa [vbm, r, S, SR] using this
theorem vcP {f : ℂ → ℂ} {ρ C : ℝ}
  (hf : Differentiable ℂ f)
  (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
  vbm (divisor f (Set.univ : Set ℂ)) R
   ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
 have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
 have qbI : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
 have hlow :
   (log 2) * vbm (divisor f (Set.univ : Set ℂ)) R
    ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
  vcI
   (D := divisor f (Set.univ : Set ℂ))
   (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
 have hupp :
   logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
    ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have qlb : 0 < 2 * R := by nlinarith [hR0]
  simpa using vdN (f := f) (ρ := ρ) (C := C) hf hC
   (R := 2 * R) qlb
 have hmul :
   (log 2) * vbm (divisor f (Set.univ : Set ℂ)) R
    ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
  hlow.trans hupp
 have hmul' :
   vbm (divisor f (Set.univ : Set ℂ)) R * log 2
    ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
 exact (le_div_iff₀ qbI).2 hmul'
end Function.locallyFinsuppWithin
end
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
  0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
 MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
section
noncomputable section
open scoped BigOperators
open Filter
namespace Real
lemma vgE {x : ℝ} (hx : 1 ≤ x) :
  (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
 have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
 have hlog_nonneg : 0 ≤ Real.logb 2 x :=
  Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
 have qeA : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
  simpa using (Nat.floor_le hlog_nonneg)
 exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ))
  (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
  (by norm_num : (1 : ℝ) < 2) hx0).1 qeA
lemma veR {x : ℝ} (hx : 1 ≤ x) :
  x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
 have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
 have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
  simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
 exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
  (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1)
  (by norm_num : (1 : ℝ) < 2) hx0).1 hlt
lemma vgb {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
  (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
  r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
 have qaQ : r0 ≠ 0 := ne_of_gt hr0
 have hx1 : (1 : ℝ) ≤ x / r0 := by
  have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
  simpa [qaQ] using this
 have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
  have := Real.vgE (x := x / r0) hx1
  simpa [hk] using this
 have := mul_le_mul_of_nonneg_left hle hr0.le
 have qfk : r0 * (x / r0) = x := by
  field_simp [qaQ]
 simpa [mul_assoc, qfk] using this
lemma vgg {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
  (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
  x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
 have qaQ : r0 ≠ 0 := ne_of_gt hr0
 have hx1 : (1 : ℝ) ≤ x / r0 := by
  have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
  simpa [qaQ] using this
 have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have := Real.veR (x := x / r0) hx1
  simpa [hk] using this
 have := mul_lt_mul_of_pos_left hlt hr0
 have qfk : r0 * (x / r0) = x := by
  field_simp [qaQ]
 exact le_of_lt (by simpa [mul_assoc, qfk] using this)
lemma vgJ (A : ℝ) :
  ∃ k0 : ℕ, ∀ n ≥ k0, A ≤ (2 : ℝ) ^ n := by
 have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
 exact eventually_atTop.1 ((tendsto_atTop.1 htend) A)
lemma vcR
    {r0 : ℝ} {k0 kk : ℕ} (hr0 : 0 < r0)
    (hk0 : ∀ n ≥ k0, (1 / r0 : ℝ) ≤ (2 : ℝ) ^ n) (hkk : k0 ≤ kk + 1) :
    (1 : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) := by
  have qaQ : r0 ≠ 0 := ne_of_gt hr0
  have qfl : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ (kk + 1) := hk0 (kk + 1) hkk
  have qbj : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
    have hcast : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
      calc
        (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one]
        _ = (2 : ℝ) ^ (kk + 1) := by
          simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
    simpa [hcast] using qfl
  have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left qbj hr0.le
  simpa [one_div, qaQ, mul_assoc] using this
lemma vdf {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have qlc : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
    have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
      have : 0 ≤ Rk := by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
      dsimp [Rk]
      calc
        (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
            = (2 * r0) * (2 : ℝ) ^ ((k : ℝ) + 1) := by ring
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
              simp [Real.rpow_add, mul_assoc]
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * 2) := by simp [Real.rpow_one]
        _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by ring
    calc
      |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
      _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := hmul
  have hbase :
      (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
        simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
      simpa [Real.rpow_natCast] using this
    have habs :
        1 + |2 * Rk| ≤ (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      rw [qlc]
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (k : ℝ)))
    have hfac :
        (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ)
          = (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      ring
    exact habs.trans (le_of_eq hfac)
  have qbJ : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
  have :
      (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ :=
    Real.rpow_le_rpow qbJ hbase hρ
  have hsplit :
      ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ
        = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0.le]
    have h2 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have hpow : ((2 : ℝ) ^ (k : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    have qaB : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ((2 : ℝ) ^ (k : ℝ)) ^ ρ = (2 : ℝ) ^ ((k : ℝ) * ρ) := by
        simp [Real.rpow_mul]
      _ = ((2 : ℝ) ^ ρ) ^ (k : ℝ) := by
        simpa [mul_comm] using
          (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (k : ℝ)) qaB)
      _ = ((2 : ℝ) ^ ρ) ^ k := by
        simp [Real.rpow_natCast]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
        = (1 + |2 * Rk|) ^ ρ := by rfl
    _ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ := this
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := hsplit
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow
lemma vda {α : Type*} [Fintype α] {a : α → ℝ}
  {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
  (qfm : ∀ x, R ≤ a x) :
  (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
 have hsum_le :
   (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
  refine Finset.sum_le_sum ?_
  intro x _hx
  have hinv : (a x)⁻¹ ≤ R⁻¹ := by
   simpa using (inv_anti₀ hR (qfm x))
  exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
 simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le
lemma vdS (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  have qa4 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  calc
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0 * (2 : ℝ) ^ (k : ℝ)) ^ (-τ) := by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0 * (2 : ℝ) ^ (k : ℝ)) τ).symm
    _ = r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
      simpa using (Real.mul_rpow hr0 qa4 (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
      have hr0' : r0 ^ (-τ) = (r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = ((2 : ℝ) ^ (-τ)) ^ k := by
        have qaB : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        calc
          ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((k : ℝ) * (-τ)) := by
            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (k : ℝ)) (z := -τ)
              qaB).symm
          _ = (2 : ℝ) ^ ((-τ) * (k : ℝ)) := by ring_nf
          _ = ((2 : ℝ) ^ (-τ)) ^ (k : ℝ) := by
            exact Real.rpow_mul (x := (2 : ℝ)) (y := -τ) (z := (k : ℝ)) qaB
          _ = ((2 : ℝ) ^ (-τ)) ^ k := by
            simp [Real.rpow_natCast]
      calc
        r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
              rw [hr0']
        _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
              rw [h2']
lemma vgd (ρ τ : ℝ) :
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
    _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
      simp [Real.rpow_add h2pos]
lemma vfm (ρ τ : ℝ) (k : ℕ) :
  ((2 : ℝ) ^ (ρ - τ)) ^ k =
   ((2 : ℝ) ^ ρ) ^ k * (((2 : ℝ) ^ (-τ)) ^ k) := by
 simp [vgd, mul_pow]
lemma vfy (C L M r0 ρ τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
  ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
    ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
   = (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k := by
 have qgm :
   (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
    (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (-τ)) ^ k) :=
  vdS r0 τ k hr0
 rw [qgm, vfm]
 ac_rfl
lemma vfl (C L r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
  (C / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
   ≤ (((C / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
 rw [vdS r0 τ k hr0]
 have hcoeff : C / L ≤ C / L + 1 := by linarith
 have qcv : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
  Real.rpow_nonneg (inv_nonneg.2 hr0) _
 have hmul :
   (C / L) * ((r0⁻¹ : ℝ) ^ τ)
    ≤ ((C / L) + 1) * ((r0⁻¹ : ℝ) ^ τ) :=
  mul_le_mul_of_nonneg_right hcoeff qcv
 have qcS : 0 ≤ ((2 : ℝ) ^ (-τ)) ^ k :=
  pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) _
 have := mul_le_mul_of_nonneg_right hmul qcS
 simpa [mul_assoc, mul_left_comm, mul_comm] using this
lemma vdm {C L M X T qP r0 ρ τ : ℝ} {k : ℕ}
  (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0)
  (hX : X ≤ M * ((2 : ℝ) ^ ρ) ^ k)
  (hT : T ≤ ((C * X + qP) / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :
  T ≤ (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k
    + (((qP / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
 have hmul : C * X ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) :=
  mul_le_mul_of_nonneg_left hX hC
 have hnum : C * X + qP ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) + qP :=
  add_le_add hmul le_rfl
 have hdiv :
   (C * X + qP) / L ≤ (C * (M * ((2 : ℝ) ^ ρ) ^ k) + qP) / L :=
  div_le_div_of_nonneg_right hnum hL.le
 have qa4 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
  le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ))
 have qdO : 0 ≤ r0 * (2 : ℝ) ^ (k : ℝ) :=
  mul_nonneg hr0 qa4
 have qcg : 0 ≤ ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ) :=
  Real.rpow_nonneg (inv_nonneg.2 qdO) τ
 have hmul' :=
  mul_le_mul_of_nonneg_right hdiv qcg
 have hdecomp :
   ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + qP) / L) *
     ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
    =
    ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
      ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
     + ((qP / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) := by
  let Y : ℝ := (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ
  have :
    ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + qP) / L) * Y
     = ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) * Y
      + ((qP / L) * Y) := by
   ring
  simpa [Y]
 have hpre :
   T ≤ ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
      ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
     + ((qP / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :=
  hT.trans (hmul'.trans_eq hdecomp)
 have hA := le_of_eq (vfy C L M r0 ρ τ k hr0)
 have hB := vfl qP L r0 τ k hr0
 exact hpre.trans (by
  simpa [mul_assoc, mul_left_comm, mul_comm] using add_le_add hA hB)
lemma vgc (A B q qσ : ℝ) (k k0 : ℕ) :
  A * q ^ (k + k0) + B * qσ ^ (k + k0)
   = (A * q ^ k0) * q ^ k + (B * qσ ^ k0) * qσ ^ k := by
 rw [pow_add, pow_add]
 ac_rfl
end Real
end
end
section
noncomputable section
open Filter Topology Set Complex
open scoped BigOperators Topology
namespace Complex.Hadamard
open scoped Real
noncomputable def vaA (f : ℂ → ℂ) (R : ℝ) : ℝ :=
 Function.locallyFinsuppWithin.vbm (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
lemma vdE {f : ℂ → ℂ} {ρ C : ℝ}
  (hf : Differentiable ℂ f)
  (hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
  {R : ℝ} (hR : 1 ≤ R) :
  vaA f R
   ≤ (C * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) /
     Real.log 2 := by
 simpa [vaA] using
  (Function.locallyFinsuppWithin.vcP
   (f := f) (ρ := ρ) (C := C) hf hC hR)
lemma vcY {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ p : qv f (Set.univ : Set ℂ), r0 ≤ ‖qg p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have qat : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  have hzero : ∀ p : qv f U, f (qg p) = 0 := by
    intro p
    set z : ℂ := qg p
    have qhz : meromorphicOrderAt f z ≠ ⊤ := by
      have qhA : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        vak (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        qhA.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have qiM : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using qiM
    have qiN : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using qat z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 qiN
      simpa [WithTop.coe_untop₀_of_ne_top qhz] using this
    have qcT : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have qhB : ContinuousAt f z := (hf z).continuousAt
    have qhC : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (qhB.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique qhC qcT
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have qhD : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have qgn : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          vak (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact absurd h hA0
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have qcT : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have qcU : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using qcU.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have qiO : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos qhD).1 qcT
      have qhE : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top qgn] using qiO
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using
          (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ))
            hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt qhE
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, qU, hr0⟩
    refine ⟨r0, qU, ?_⟩
    intro p
    have hp : qg p ∈ D.support := by
      simp [D, vbs (f := f) (U := U) p]
    have qfn : qg p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : qg p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : qg p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : qg p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (vao p) this
    have : r0 ≤ ‖qg p‖ := by
      have : ¬ ‖qg p‖ < r0 := by
        intro hlt
        exact qfn (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have qcU : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := qcU.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, qU, hr0⟩
    refine ⟨r0, qU, ?_⟩
    intro p
    have : ¬ ‖qg p‖ < r0 := by
      intro hlt
      have qhF : qg p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (qg p) ≠ 0 := hr0 qhF
      exact this (hzero p)
    exact le_of_not_gt this
open scoped BigOperators
lemma vdI
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    (Nat.card {p : qv f (Set.univ : Set ℂ) // ‖qg p‖ ≤ R} : ℝ)
      ≤ vaA f R := by
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have :
      Fintype {p : qv f U // ‖qg p‖ ≤ R} := by
    have : Finite {p : qv f U // ‖qg p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (vaT (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have qat : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : qv f U // ‖qg p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := qg p.1
    have qeB : z0 ∈ SR := by
      have qfo : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R := p.2
        simpa [abs_of_pos hR] using this
      have qdh : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have qeC : z0 ∈ D.support := by
          simp [z0, D]
        exact Function.locallyFinsuppWithin.vaX
          qeC qfo
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0 : ℂ) |R|))).2 qdh
    have qgo : z0 ≠ 0 := vao p.1
    have qfp : z0 ∈ S := Finset.mem_filter.2 ⟨qeB, qgo⟩
    ⟨⟨z0, qfp⟩, by
        simpa [z0, qg, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : qg p.1 = qg q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : qv f U // ‖qg p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have qgp :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have qeD : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have qa3 : 0 ≤ D z := by simpa [D] using qat z
    have qld : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg qa3)
    have qlf : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast qld
    exact le_of_eq qlf
  calc
    (Nat.card {p : qv f U // ‖qg p‖ ≤ R} : ℝ)
        = (Fintype.card {p : qv f U // ‖qg p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := qgp
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact qeD z hz
    _ = vaA f R := by
      rfl
lemma vcb
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Set (qv f (Set.univ : Set ℂ))} [Fintype s]
    {R : ℝ} (hR : 0 < R) (hs : ∀ p : s, ‖qg p.1‖ ≤ R) :
    (Fintype.card s : ℝ) ≤ vaA f R := by
  let qaD : Type :=
    {p : qv f (Set.univ : Set ℂ) // ‖qg p‖ ≤ R}
  have : Fintype qaD := by
    have : Finite qaD := by
      have : Metric.closedBall (0 : ℂ) R ⊆ (Set.univ : Set ℂ) := by simp
      simpa [qaD] using
        (vaT (f := f) (U := (Set.univ : Set ℂ))
          (B := R) this)
    exact Fintype.ofFinite _
  have hinj : Function.Injective (fun p : s => (⟨p.1, hs p⟩ : qaD)) := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : qaD => x.1) hpq
  have hcard_le : Fintype.card s ≤ Fintype.card qaD :=
    Fintype.card_le_of_injective _ hinj
  have qhG : (Nat.card qaD : ℝ) ≤ vaA f R := by
    simpa [qaD] using vdI (f := f) hf hR
  calc
    (Fintype.card s : ℝ) ≤ (Fintype.card qaD : ℝ) := by exact_mod_cast hcard_le
    _ = (Nat.card qaD : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ vaA f R := qhG
lemma vbr
  {f : ℂ → ℂ} {r0 : ℝ}
  (qU : 0 < r0)
  (hr0 : ∀ p : qv f (Set.univ : Set ℂ), r0 ≤ ‖qg p‖)
  {k : ℕ} {p : qv f (Set.univ : Set ℂ)}
  (hp : ⌊Real.logb 2 (‖qg p‖ / r0)⌋₊ = k) :
  ‖qg p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
 exact Real.vgg (r0 := r0) (x := ‖qg p‖)
  qU (hr0 p) hp
lemma vcO
  {f : ℂ → ℂ} {r0 : ℝ}
  (qU : 0 < r0)
  (hr0 : ∀ p : qv f (Set.univ : Set ℂ), r0 ≤ ‖qg p‖)
  {k : ℕ} {p : qv f (Set.univ : Set ℂ)}
  (hp : ⌊Real.logb 2 (‖qg p‖ / r0)⌋₊ = k) :
  r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖qg p‖ := by
 exact Real.vgb (r0 := r0) (x := ‖qg p‖)
  qU (hr0 p) hp
lemma vbC
  {f : ℂ → ℂ} {r0 : ℝ}
  (qU : 0 < r0)
  (hr0 : ∀ p : qv f (Set.univ : Set ℂ), r0 ≤ ‖qg p‖)
  (k : ℕ) :
  ({p : qv f (Set.univ : Set ℂ) |
   ⌊Real.logb 2 (‖qg p‖ / r0)⌋₊ = k} : Set _).Finite := by
 have hsub :
   {p : qv f (Set.univ : Set ℂ) |
    ⌊Real.logb 2 (‖qg p‖ / r0)⌋₊ = k} ⊆
    {p : qv f (Set.univ : Set ℂ) |
     ‖qg p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
  intro p hp
  exact vbr qU hr0 hp
 have hfin :
   ({p : qv f (Set.univ : Set ℂ) |
    ‖qg p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
  have :
    Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
     (Set.univ : Set ℂ) := by
   simp
  simpa using
   (vau (f := f) (U := (Set.univ : Set ℂ))
    (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
 exact hfin.subset hsub
lemma vbl
  {f : ℂ → ℂ} {ρ τ r0 qaE : ℝ}
  (hρ : 0 ≤ ρ) (qbY : 0 < τ) (hf : Differentiable ℂ f)
  (qa5 : 0 < qaE)
  (qcV : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ qaE * (1 + ‖z‖) ^ ρ)
  (qU : 0 < r0)
  (hr0 : ∀ p : qv f (Set.univ : Set ℂ),
   r0 ≤ ‖qg p‖)
  (k : ℕ) (qco : 1 ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) :
  let qaI : qv f (Set.univ : Set ℂ) → ℕ :=
   fun p => ⌊Real.logb 2 (‖qg p‖ / r0)⌋₊
  let S : Set (qv f (Set.univ : Set ℂ)) := {p | qaI p = k}
  let qP : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
  let A : ℝ := ((qaE / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
  let B : ℝ := ((qP / Real.log 2) + 1) * (r0⁻¹) ^ τ
  let q : ℝ := (2 : ℝ) ^ (ρ - τ)
  let qσ : ℝ := (2 : ℝ) ^ (-τ)
  (∑' p : S, ‖qg p.1‖⁻¹ ^ τ) ≤ A * q ^ k + B * qσ ^ k := by
 classical
 intro qaI S qP A B q qσ
 let rk : ℝ := r0 * (2 : ℝ) ^ (k : ℝ)
 let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
 have qdv : 0 < rk := mul_pos qU (Real.rpow_pos_of_pos (by norm_num) _)
 have qlg : 0 ≤ rk := le_of_lt qdv
 have : Finite S := by
  simpa [S, qaI] using (vbC
   (f := f) qU hr0 k).to_subtype
 have : Fintype S := Fintype.ofFinite S
 have qfq : ∀ p : S, ‖qg p.1‖ ≤ Rk := by
  intro p
  have hk' : qaI p.1 = k := p.2
  simpa [Rk, qaI] using
   vbr (f := f) qU hr0 hk'
 have hk_lower : ∀ p : S, rk ≤ ‖qg p.1‖ := by
  intro p
  have hk' : qaI p.1 = k := p.2
  simpa [rk, qaI] using
   vcO (f := f) qU hr0 hk'
 have qbK :
   (∑' p : S, ‖qg p.1‖⁻¹ ^ τ)
    ≤ (Fintype.card S : ℝ) * (rk⁻¹ ^ τ) := by
  exact Real.vda
   (a := fun p : S => ‖qg p.1‖)
   qdv qbY (fun _ => norm_nonneg _) hk_lower
 have qbZ :
   vaA f Rk
    ≤ (qaE * (1 + |2 * Rk|) ^ ρ + qP) / (Real.log 2) := by
  simpa [qP, Rk] using
   (vdE (f := f) (ρ := ρ) (C := qaE) hf qcV
    (R := Rk) qco)
 have qcw :
   (Fintype.card S : ℝ) ≤ vaA f Rk := by
  have qgq : 0 < Rk := lt_of_lt_of_le (by norm_num) qco
  exact vcb (f := f) hf qgq qfq
 have qhH :
   (∑' p : S, ‖qg p.1‖⁻¹ ^ τ)
    ≤ ((qaE * (1 + |2 * Rk|) ^ ρ + qP) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
  have qb0 :
    (Fintype.card S : ℝ) ≤
     (qaE * (1 + |2 * Rk|) ^ ρ + qP) / (Real.log 2) :=
   le_trans qcw qbZ
  exact le_trans qbK <|
   mul_le_mul_of_nonneg_right qb0 (Real.rpow_nonneg (inv_nonneg.2 qlg) τ)
 have qdP :
   (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  simpa [Rk] using
   Real.vdf (r0 := r0) (ρ := ρ) k qU hρ
 have qbI : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
 simpa [A, B, q, qσ, rk, qP, mul_assoc, mul_left_comm, mul_comm] using
  Real.vdm
   (C := qaE) (L := Real.log 2) (M := (1 + 4 * r0) ^ ρ)
   (X := (1 + |2 * Rk|) ^ ρ)
   (T := ∑' p : S, ‖qg p.1‖⁻¹ ^ τ)
   (qP := qP) (r0 := r0) (ρ := ρ) (τ := τ) (k := k)
   qbI qa5.le qU.le qdP
   (by simpa [rk] using qhH)
theorem vaG {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ τ) := by
  rcases hgrowth with ⟨qaE, qa5, qcV⟩
  have qbY : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases vcY (f := f) hf hnot with ⟨r0, qU, hr0⟩
  have qaQ : (r0 : ℝ) ≠ 0 := ne_of_gt qU
  let qaI : qv f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖qg p‖ / r0)⌋₊
  let S : ℕ → Set (qv f (Set.univ : Set ℂ)) :=
    fun k => {p | qaI p = k}
  have hS : ∀ p : qv f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨qaI p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have qcW : ∀ k : ℕ, Summable fun p : S k => ‖qg p.1‖⁻¹ ^ τ := by
    intro k
    have : Finite (S k) := by
      simpa [S, qaI] using (vbC
        (f := f) qU hr0 k).to_subtype
    exact Summable.of_finite
  have qb1 :
      Summable fun k : ℕ => ∑' p : S k, ‖qg p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have qeE : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have qdi : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have qdj : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos qbY))
    have qgr : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg qeE
    have qeF : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one qdi qdj
    let qP : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((qaE / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((qP / Real.log 2) + 1) * (r0⁻¹) ^ τ
    rcases Real.vgJ (1 / r0) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have qhJ : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (qgr.mul_left A0).add (qeF.mul_left B0)
    have qaY :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖qg p.1‖⁻¹ ^ τ := by
      refine qhJ.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖qg p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have qdQ : (1 : ℝ) ≤ Rk := by
            have hkk : k0 ≤ kk + 1 := by
              simp [kk, Nat.add_assoc, Nat.add_comm]
            simpa [Rk] using
              Real.vcR qU hk0 hkk
          have hmain :
              (∑' p : S kk, ‖qg p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            simpa [S, qaI, qP, A, B, q, qσ] using
              vbl
                (f := f) (ρ := ρ) (τ := τ) hρ qbY hf qa5 qcV qU hr0 kk qdQ
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            simpa [A0, B0, kk] using Real.vgc A B q qσ k k0
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 qaY
  have hpart :=
    (summable_partition (f := fun p : qv f (Set.univ : Set ℂ) =>
        ‖qg p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨qcW, qb1⟩)
theorem vbb {f : ℂ → ℂ} {ρ : ℝ}
  (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
  (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
  Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
 have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
  simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
 have hs :=
  vaG (f := f) (ρ := ρ)
   (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
 exact hs.congr fun p => by
  have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
   norm_num
  rw [hcast, Real.rpow_natCast]
end Complex.Hadamard
end
end
section
namespace Complex
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem vcF {f : ℂ → F} {r C : ℝ} {z : ℂ}
  (hd : Differentiable ℂ f) (hrpos : 0 < r)
  (hz : z ∈ Metric.ball (0 : ℂ) r) (hsphere : ∀ u : ℂ, ‖u‖ = r → ‖f u‖ ≤ C) :
  ‖f z‖ ≤ C := by
 let U : Set ℂ := Metric.ball (0 : ℂ) r
 have qhK : ∀ u ∈ frontier U, ‖f u‖ ≤ C := by
  intro u hu
  have hur : ‖u‖ = r := by
   have qgs : frontier (Metric.ball (0 : ℂ) r) = Metric.sphere (0 : ℂ) r := by
    simpa using (frontier_ball (x := (0 : ℂ)) (r := r) (ne_of_gt hrpos))
   have : u ∈ Metric.sphere (0 : ℂ) r := by simpa [U, qgs] using hu
   simpa [Metric.mem_sphere, dist_zero_right] using this
  exact hsphere u hur
 exact norm_le_of_forall_mem_frontier_norm_le (f := f) (U := U) Metric.isBounded_ball
  hd.diffContOnCl qhK (subset_closure hz)
end Complex
end
section
namespace Complex
namespace qw
open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal
private lemma vfZ {x : ℝ} (hx : 0 < x) (hxle : x ≤ 1) :
  -Real.log x ≤ Real.sqrt (2 / x) := by
 have hx0 : 0 ≤ x := le_of_lt hx
 have ht : 0 ≤ -Real.log x := by
  have : Real.log x ≤ 0 := Real.log_nonpos hx0 hxle
  linarith
 have qbk : ∀ {t : ℝ}, 0 ≤ t → t ^ 2 / 2 ≤ Real.exp t := by
  intro t ht
  let g : ℝ → ℝ := fun u => Real.exp u - u ^ 2 / 2
  have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
   have : Continuous g := by fun_prop
   simpa using this.continuousOn
  have qgt : DifferentiableOn ℝ g (interior (Set.Ici (0 : ℝ))) := by
   intro u hu
   have : DifferentiableAt ℝ g u := by fun_prop
   exact this.differentiableWithinAt
  have qdR : ∀ u ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv g u := by
   intro u hu
   have hu0 : 0 < u := by simpa [interior_Ici] using hu
   have hderiv : deriv g u = Real.exp u - u := by
    have hExp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
    have hpow2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
     simpa using! ((hasDerivAt_id u).pow 2)
    have qeG : HasDerivAt (fun z : ℝ => z ^ 2 / 2) u u := by
     simpa using (hpow2.div_const (2 : ℝ))
    have hG : HasDerivAt g (Real.exp u - u) u := by
     simpa [g] using! hExp.sub qeG
    exact hG.deriv
   have hu_le : u ≤ Real.exp u := by
    have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
    exact (le_trans (le_add_of_nonneg_right (by norm_num)) h1)
   have : 0 ≤ Real.exp u - u := sub_nonneg.2 hu_le
   simpa [hderiv] using this
  have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) :=
   monotoneOn_of_deriv_nonneg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici 0)
    hg_cont qgt qdR
  have hg0 : g 0 = 1 := by simp [g]
  have hle : g 0 ≤ g t := hg_mono (by simp) (by simpa [Set.mem_Ici] using ht) ht
  have : (1 : ℝ) ≤ Real.exp t - t ^ 2 / 2 := by simpa [g, hg0] using hle
  linarith
 have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := qbk ht
 have hexp : Real.exp (-Real.log x) = x⁻¹ := by simp [Real.exp_neg, Real.exp_log hx]
 have hsq2 : (-Real.log x) ^ 2 ≤ 2 * Real.exp (-Real.log x) := by nlinarith [hmain]
 have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by simpa [hexp, div_eq_mul_inv, mul_assoc] using hsq2
 have hy : 0 ≤ 2 / x := div_nonneg (by norm_num) (le_of_lt hx)
 exact (Real.le_sqrt ht hy).2 hsq'
lemma vdt {t : ℝ} :
    Real.posLog (1 / |1 - t|) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        vfZ (x := |1 - t|) hpos ht
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        exact Real.log_nonneg ((one_le_div hpos).2 ht)
      have hmax : Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      calc
        Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 (le_of_lt hlt)
      exact le_trans (Real.log_le_log (by positivity) this) (by simp)
    have hmax : Real.posLog (1 / |1 - t|) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      exact Real.sqrt_nonneg _
    rw [hmax]
    exact hrhs
noncomputable def φ (t : ℝ) : ℝ :=
 log⁺ (1 / |1 - t|)
lemma vgM : Measurable φ := by
 unfold φ
 simpa [Real.posLog_def, Real.posLog] using
  (by fun_prop : Measurable fun t : ℝ => max 0 (Real.log (1 / |1 - t|)))
lemma vfx {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) : φ t ≤ Real.log 2 := by
 have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
 have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
  have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
  simpa [abs_of_nonneg hnonneg] using this
 have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
  have qfr : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have := one_div_le_one_div_of_le qfr hden
  simpa [one_div, div_eq_mul_inv] using this
 have qgu : log⁺ (1 / |1 - t|) ≤ log⁺ (2 : ℝ) :=
  Real.posLog_le_posLog (by positivity) hfrac
 have habs : (1 : ℝ) ≤ |(2 : ℝ)| := by
  simp
 have qfs : (log⁺ (2 : ℝ)) = Real.log 2 := by
  simpa using (Real.posLog_eq_log habs)
 simpa [φ, qfs] using qgu
lemma vev {t : ℝ} (ht : (1 : ℝ) ≤ |1 - t|) : φ t = 0 := by
 have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) ht
 have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 ht
 have habs : |(1 / |1 - t| : ℝ)| ≤ 1 := by
  have hnonneg : 0 ≤ (1 / |1 - t| : ℝ) := by positivity
  simpa [abs_of_nonneg hnonneg] using hfrac
 have : log⁺ (1 / |1 - t|) = 0 := (Real.posLog_eq_zero_iff _).2 habs
 simpa [φ] using this
lemma vjf (t : ℝ) : 0 ≤ φ t := by
 simpa [φ] using (Real.posLog_nonneg (x := (1 / |1 - t|)))
lemma viL (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
 simpa [φ, Real.posLog] using
  vdt (t := t)
lemma vbI {A B : ℝ} (hAB : A ≤ B) {g : ℝ → ℝ}
  (hg : ∀ t, 0 ≤ g t) (h : ∀ t ∈ Set.Icc A B, φ t ≤ g t) :
  (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] fun t => ‖g t‖ := by
 refine
  MeasureTheory.ae_restrict_of_forall_mem (μ := (volume : MeasureTheory.Measure ℝ))
  (s := Set.uIoc A B)
   (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A B))) ?_
 intro t ht
 have qcB : t ∈ Set.Ioc A B := by
  simpa [Set.uIoc_of_le hAB] using ht
 have qiP : t ∈ Set.Icc A B := ⟨le_of_lt qcB.1, qcB.2⟩
 have hle : φ t ≤ g t := h t qiP
 have hφ0 : 0 ≤ φ t := vjf t
 have hg0 : 0 ≤ g t := hg t
 simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hg0] using hle
lemma veI {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -φ (r / ‖a‖) := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have qft : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [habs]
      exact hdiv
    rwa [hnorm_eq]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have hlogx :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖) := by
    have := Real.vgA (x := |1 - (r / ‖a‖)|)
    simpa [φ, one_div, inv_inv, abs_sub_comm, sub_eq_add_neg] using this
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) qft
  linarith [hlog_mono, hlogx]
noncomputable def K : ℝ :=
 ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume
lemma vir : 0 ≤ K := by
 have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
 have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
  intro _t _ht
  exact Real.sqrt_nonneg _
 simpa [K] using (intervalIntegral.integral_nonneg
  (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)
noncomputable def Cφ : ℝ :=
 Real.log 2 + 4 * K + 1
lemma viP : 0 < Cφ := by
 have hlog : 0 < Real.log 2 := by
  simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
 have hK : 0 ≤ K := vir
 have : 0 < Real.log 2 + 4 * K := by nlinarith
 have : 0 < Real.log 2 + 4 * K + 1 := by linarith
 simpa [Cφ] using this
lemma vbh :
    IntervalIntegrable
      (fun t : ℝ => Real.sqrt (2 / |1 - t|))
      volume (1 / 4 : ℝ) (4 : ℝ) := by
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)
  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    have hpow :
        IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact
      (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm)
        hpow2
  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)
  have hleft :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have qfu :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have qdS :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) :=
      qfu.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    have qhM : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using qdS
    simpa [f] using qhM
  have hright :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have qfu :
        IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have qdS : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using qfu
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|))
          (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t _ht
      simp [f, abs_sub_comm]
    exact
      (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr)
        qdS
  exact hleft.trans hright
lemma vbF {A t : ℝ} (hA : A ≤ (1 / 4 : ℝ))
  (ht : t ∈ Set.Icc A (2 * A)) :
  φ t ≤ Real.log 2 := by
 have ht_le : t ≤ (1 / 2 : ℝ) := by
  exact ht.2.trans (by nlinarith [hA])
 exact vfx ht_le
lemma veG {t : ℝ} (ht : (2 : ℝ) ≤ t) : φ t = 0 := by
 have hden : (1 : ℝ) ≤ |1 - t| := by
  have : (1 : ℝ) ≤ t - 1 := by linarith
  have : (1 : ℝ) ≤ |t - 1| := by
   simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
  simpa [abs_sub_comm] using this
 exact vev hden
lemma vbU {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ (1 / 4 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have qan : A ≤ 2 * A := by nlinarith
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (vgM.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun _ => ‖(Real.log 2 : ℝ)‖ := by
    refine vbI (A := A) (B := 2 * A) qan
      (g := fun _ => (Real.log 2 : ℝ)) (hg := fun _ => ?_) ?_
    · simpa using (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    · intro t ht
      exact vbF hA ht
  exact IntervalIntegrable.mono_fun hconst hmeas hdom
lemma vdZ {A : ℝ} (hA : (2 : ℝ) ≤ A) :
  IntervalIntegrable φ volume A (2 * A) := by
 have qan : A ≤ 2 * A := by nlinarith
 have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
  intro t ht
  have qcB : t ∈ Set.Ioc A (2 * A) := by
   simpa [Set.uIoc_of_le qan] using ht
  exact veG (le_trans hA (le_of_lt qcB.1))
 have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
  intervalIntegrable_const
 exact (IntervalIntegrable.congr (a := A) (b := (2 * A))
  (μ := (volume : MeasureTheory.Measure ℝ))
  (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
   intro t ht
   simpa using (hEq (x := t) ht).symm)) hz
lemma vaP {A : ℝ}
    (qV : (1 / 4 : ℝ) ≤ A) (qab : A ≤ (2 : ℝ)) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
  have qbl :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|))
        (volume : MeasureTheory.Measure ℝ) (1 / 4 : ℝ) (4 : ℝ) :=
    vbh
  refine qbl.mono_set ?_
  refine Set.uIcc_subset_uIcc ?_ ?_
  · exact (Set.mem_uIcc).2 (Or.inl ⟨qV, by nlinarith [qab]⟩)
  · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [qV], by nlinarith [qab]⟩)
lemma vbM {A : ℝ}
  (qV : (1 / 4 : ℝ) ≤ A) (qab : A ≤ (2 : ℝ)) :
  IntervalIntegrable φ volume A (2 * A) := by
 have qan : A ≤ 2 * A := by nlinarith [qV]
 have hsqrt :
   IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) :=
  vaP qV qab
 have hmeas :
   AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
  (vgM.aestronglyMeasurable : _)
 have hdom :
   (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
    fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
  refine vbI (A := A) (B := 2 * A) qan
   (g := fun t => Real.sqrt (2 / |1 - t|)) (hg := fun _ => Real.sqrt_nonneg _) ?_
  intro t _ht
  exact viL t
 exact IntervalIntegrable.mono_fun hsqrt hmeas hdom
lemma veS {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  by_cases hA0 : A = 0
  · subst hA0
    simp
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact vbU hA hsmall
  | inr qaT =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact vdZ hbig
      | inr qbm =>
          exact vbM qaT qbm
lemma vdl {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
  IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
 have ha0 : a ≠ 0 := ne_of_gt ha
 have qdT : 0 ≤ R / a := by
  exact div_nonneg hR (le_of_lt ha)
 have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
  veS (A := (R / a)) qdT
 have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
 have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
  field_simp [ha0]
 simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this
lemma viU : Real.log 2 ≤ Cφ := by
 dsimp [Cφ]
 have hK : 0 ≤ K := vir
 linarith [hK]
lemma vfB : (4 * K + 1 : ℝ) ≤ Cφ := by
 dsimp [Cφ]
 have hlog_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
 linarith [hlog_nonneg]
lemma veT {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (1 / 4 : ℝ)) :
  (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
 have qan : A ≤ 2 * A := by nlinarith
 have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
  vbU hA0 hA
 have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
  intervalIntegrable_const
 have qch :
   (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
    ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
  refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ))
   qan hφ_int hconst ?_
  intro t ht
  exact vbF hA ht
 have hRHS :
   (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
  simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
 have hcoef : A * Real.log 2 ≤ Cφ * A := by
  have := mul_le_mul_of_nonneg_left viU hA0
  simpa [mul_assoc, mul_left_comm, mul_comm] using this
 exact le_trans (by simpa [hRHS] using qch) hcoef
lemma veV {A : ℝ} (hA : (2 : ℝ) ≤ A) :
  (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
 have qan : A ≤ 2 * A := by nlinarith
 have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
  intro t ht
  have ht' : t ∈ Set.Icc A (2 * A) := by
   simpa [Set.uIcc_of_le qan] using ht
  exact veG (le_trans hA ht'.1)
 have hzero : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
  simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
 have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg (le_of_lt viP) (by linarith)
 simpa [hzero] using hnonneg
lemma vbZ {A : ℝ}
  (qV : (1 / 4 : ℝ) ≤ A) (qab : A ≤ (2 : ℝ)) :
  (∫ (t : ℝ) in A..(2 * A), Real.sqrt (2 / |1 - t|) ∂volume) ≤ K := by
 let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
 have qan : A ≤ 2 * A := by nlinarith [qV]
 have qeH : (2 * A : ℝ) ≤ 4 := by nlinarith [qab]
 have qbl : IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) := by
  simpa [s] using vbh
 have qiQ :
   (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
    ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
  refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
   (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
   qV qan qeH ?_ qbl
  exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
 simpa [K, s] using qiQ
lemma vcZ {A : ℝ} (hA : (1 / 4 : ℝ) ≤ A) :
  K ≤ (4 * K + 1) * A := by
 have hcoef : 1 ≤ 4 * A := by nlinarith [hA]
 have hK : 0 ≤ K := vir
 nlinarith [hK, hcoef]
lemma veN {A : ℝ}
  (qV : (1 / 4 : ℝ) ≤ A) (qab : A ≤ (2 : ℝ)) :
  (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
 let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
 have qan : A ≤ 2 * A := by nlinarith [qV]
 have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
  vbM qV qab
 have hsqrt : IntervalIntegrable s volume A (2 * A) := by
  simpa [s] using
   vaP qV qab
 have qch :
   (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
    ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
  refine intervalIntegral.integral_mono_on
   (μ := (volume : MeasureTheory.Measure ℝ)) qan hφ_int hsqrt ?_
  intro t _ht
  exact viL t
 have hsqrt_le : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ (4 * K + 1) * A := by
  have hK : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ K := by
   simpa [s] using vbZ qV qab
  exact le_trans hK (vcZ qV)
 have hcoef : (4 * K + 1 : ℝ) * A ≤ Cφ * A :=
  mul_le_mul_of_nonneg_right vfB (by nlinarith [qV])
 exact le_trans qch (le_trans hsqrt_le hcoef)
lemma vga {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact veT hA hsmall
  | inr qaT =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact veV hbig
      | inr qbm =>
          exact veN qaT qbm
open scoped BigOperators
lemma vfr {R : ℝ} (hR : 0 < R) :
  (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) ≠ 0 := by
 have hpos : (0 : ℝ) < 2 * R - R := by nlinarith [hR]
 simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
lemma vdy (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
  (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
 have qeI : (volume : MeasureTheory.Measure ℝ) (bad : Set ℝ) = 0 := by
  simpa using (bad.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)))
 have hdiff :
   (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
    = (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) := by
  simpa [Set.sdiff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
   (MeasureTheory.measure_sdiff_null (s := Set.Ioc R (2 * R)) (t := (bad : Set ℝ))
    qeI)
 simpa [hdiff] using vfr hR
lemma vct (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
  (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
 have hsubset : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ Set.Ioc R (2 * R) := by
  intro r hr
  exact hr.1
 have hinter :
   (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ∩ Set.Ioc R (2 * R)
    = (Set.Ioc R (2 * R) \ (bad : Set ℝ)) := by
  exact Set.inter_eq_left.mpr hsubset
 simpa [MeasureTheory.Measure.restrict_apply, measurableSet_Ioc, hinter] using
  vdy bad hR
lemma vfo {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
  (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume) ≤ Cφ * R := by
 have ha0 : a ≠ 0 := ne_of_gt ha
 have hrew :
   (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume)
    = a * (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) := by
  simp [smul_eq_mul, mul_left_comm, mul_comm, div_eq_mul_inv, ha0]
 rw [hrew]
 have hA : 0 ≤ R / a := by
  exact div_nonneg hR ha.le
 have hle : (∫ (t : ℝ) in (R / a)..(2 * (R / a)), φ t ∂volume) ≤ Cφ * (R / a) :=
  vga (A := R / a) hA
 have hEq : (2 * R / a) = 2 * (R / a) := by ring
 have hle' :
   (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) ≤ Cφ * (R / a) := by
  simpa [hEq] using hle
 have ha_nonneg : 0 ≤ a := ha.le
 have := mul_le_mul_of_nonneg_left hle' ha_nonneg
 have hRHS : a * (Cφ * (R / a)) = Cφ * R := by
  field_simp [ha0]
 simpa [hRHS, mul_assoc, mul_left_comm, mul_comm] using this
lemma vei
  {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
  (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
  IntervalIntegrable (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i))
   volume R (2 * R) := by
 refine IntervalIntegrable.sum (μ := volume) (a := R) (b := 2 * R)
  (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) ?_
 intro i hi
 have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
  vdl (a := a i) (R := R) (ha i hi) hR
 simpa [mul_assoc] using hφi.const_mul (w i)
lemma vdo
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
      ≤ Cφ * (∑ i ∈ s, w i) * R := by
  have hint : ∀ i ∈ s, IntervalIntegrable (fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
    intro i hi
    have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
      vdl (a := a i) (R := R) (ha i hi) hR
    simpa [mul_assoc] using hφi.const_mul (w i)
  have qfv :
      (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        = ∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r
            ∂volume := by
    simpa using
      (intervalIntegral.integral_finsetSum (μ := volume) (a := R) (b := 2 * R)
        (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) hint)
  rw [qfv]
  have hsum_le :
      (∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        ≤ ∑ i ∈ s, w i * (Cφ * R) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hphi :
        (∫ r in R..(2 * R), φ (r / a i) ∂volume) ≤ Cφ * R :=
      vfo (a := a i) (R := R) (ha i hi) hR
    have := mul_le_mul_of_nonneg_left hphi (hw i hi)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  refine le_trans hsum_le ?_
  have : (∑ i ∈ s, w i * (Cφ * R)) = Cφ * (∑ i ∈ s, w i) * R := by
    calc
      (∑ i ∈ s, w i * (Cφ * R)) = (∑ i ∈ s, w i) * (Cφ * R) := by
        simp [Finset.sum_mul]
      _ = Cφ * (∑ i ∈ s, w i) * R := by
        ac_rfl
  exact le_of_eq this
lemma vbQ
  {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
  (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i)
  (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
  ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
   (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
 by_contra hbad
 have qdw :
   ∀ r ∈ Set.Ioc R (2 * R), r ∉ bad →
    Cφ * (∑ i ∈ s, w i) < (∑ i ∈ s, w i * φ (r / a i)) := by
  intro r hr qdU
  have : ¬(∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
   intro hle
   exact hbad ⟨r, hr, qdU, hle⟩
  exact lt_of_not_ge this
 let g : ℝ → ℝ := ∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)
 have hg_int : IntervalIntegrable g volume R (2 * R) := by
  simpa [g] using vei s w a ha hR.le
 have qdV :
   IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) :=
  intervalIntegrable_const
 have qfw :
   (volume.restrict (Set.Ioc R (2 * R)))
    {r | Cφ * (∑ i ∈ s, w i) < g r} ≠ 0 := by
  have hall : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ {r | Cφ * (∑ i ∈ s, w i) < g r} := by
   intro r hr
   have qdW : r ∈ Set.Ioc R (2 * R) := hr.1
   have qdU : r ∉ bad := by simpa using hr.2
   simpa [g] using qdw r qdW qdU
  have hle :
    (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
     ≤ (volume.restrict (Set.Ioc R (2 * R))) {r | Cφ * (∑ i ∈ s, w i) < g r} :=
   MeasureTheory.measure_mono hall
  have hpos' :
    (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
   exact vct bad hR
  intro hzero
  have : (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) = 0 :=
   le_antisymm (le_trans hle (le_of_eq hzero)) (by positivity)
  exact hpos' this
 have qgv :
   (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume)
    < ∫ r in R..(2 * R), g r ∂volume := by
  have hab : R ≤ 2 * R := by nlinarith [hR.le]
  refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (μ := volume)
   (a := R) (b := 2 * R) (f := fun _ => (Cφ * (∑ i ∈ s, w i))) (g := g)
   hab qdV hg_int ?_ qfw
  have hmem : ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∈ Set.Ioc R (2 * R) :=
   MeasureTheory.ae_restrict_mem (by simp)
  have qgw :
    ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∉ (bad : Set ℝ) := by
   simpa using
    (bad.finite_toSet.countable.ae_notMem (μ := (volume.restrict (Set.Ioc R (2 * R)))))
  filter_upwards [hmem, qgw] with r qdW qfx
  have qeJ : r ∉ bad := by simpa using qfx
  exact le_of_lt (by simpa [g] using qdw r qdW qeJ)
 have qdk :
   (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume) = Cφ * (∑ i ∈ s, w i) * R := by
  simp [intervalIntegral.integral_const, sub_eq_add_neg, mul_comm]
  ring
 have hg_le :
   (∫ r in R..(2 * R), g r ∂volume) ≤ Cφ * (∑ i ∈ s, w i) * R := by
  simpa [g] using vdo s w a hw ha hR.le
 have : ¬(Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R) := lt_irrefl _
 have hcontra : Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R := by
  have := qgv
  simpa [qdk] using (this.trans_le hg_le)
 exact this hcontra
end qw
end Complex
end
section
noncomputable section
namespace Complex.Hadamard
open Complex Real
lemma vdT
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r)
    (qcX : (m : ℝ) ≤ τ) :
    max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
  by_cases hx : ‖u / a‖ ≤ 1
  · have qeK : ‖u / a‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg (u / a)) hx
    have hr0 : 0 ≤ r := by simpa [hur] using (norm_nonneg u)
    have hbase : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have hnonneg : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg hbase τ
    have hle1 : (1 : ℝ) ≤ 1 + (r / ‖a‖) ^ τ := le_add_of_nonneg_right hnonneg
    have hle2 : ‖u / a‖ ^ m ≤ 1 + (r / ‖a‖) ^ τ := qeK.trans hle1
    exact (max_le_iff).2 ⟨hle1, hle2⟩
  · have hx1 : 1 < ‖u / a‖ := lt_of_not_ge hx
    have hpow :
        (‖u / a‖ : ℝ) ^ (m : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) qcX
    have hpow' : ‖u / a‖ ^ m ≤ (‖u / a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using hpow
    have qfy : max 1 (‖u / a‖ ^ m) ≤ 1 + ‖u / a‖ ^ m := by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u / a‖ ^ m) ≤ 1 + (‖u / a‖ : ℝ) ^ τ :=
      qfy.trans (by nlinarith [hpow'])
    simpa [norm_div, hur] using this
lemma vdw
  {m : ℕ} {τ r : ℝ} {u a : ℂ}
  (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
  (qcX : (m : ℝ) ≤ τ) :
  ‖(qB m (u / a))⁻¹‖
   ≤ Real.exp (qw.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
 have qfz :
   Real.log ‖(1 : ℂ) - u / a‖ ≥ -qw.φ (r / ‖a‖) :=
  qw.veI (hur := hur) (ha := ha) (hr := hr)
 have hbase :=
  vch (m := m) (z := (u / a))
 have qdX :
   Real.log ‖qB m (u / a)‖
    ≥ -qw.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
  have qe6 :=
   vcw m (u / a)
  linarith [hbase, qfz, qe6]
 have hmax :
   max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ :=
  vdT (m := m) (τ := τ) (r := r) (u := u) (a := a) hur qcX
 have qci :
   -Real.log ‖qB m (u / a)‖
    ≤ qw.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
  have : -Real.log ‖qB m (u / a)‖
    ≤ qw.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
   linarith [qdX]
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
 have hpos : 0 < ‖qB m (u / a)‖ := by
  have : qB m (u / a) ≠ 0 := by
   intro h0
   have : u / a = (1 : ℂ) := (vbf m (u / a)).1 h0
   have : u = a := (div_eq_one_iff_eq ha).1 this
   have : r = ‖a‖ := by simpa [this] using hur.symm
   exact (hr this).elim
  exact norm_pos_iff.2 this
 have hEq :
   ‖(qB m (u / a))⁻¹‖ =
    Real.exp (-Real.log ‖qB m (u / a)‖) := by
  simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
 have := Real.exp_le_exp.2 qci
 simpa [hEq] using this
lemma vdF
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0)
    (hz : ‖u / a‖ ≤ (1 / 2 : ℝ)) (hτ_le : τ ≤ (m + 1 : ℝ)) :
    ‖(qB m (u / a))⁻¹‖ ≤ Real.exp ((2 : ℝ) * (r / ‖a‖) ^ τ) := by
  by_cases hu : u = 0
  · subst hu
    have hr0 : r = 0 := by simpa [hur] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0 : ℝ) / ‖a‖) ^ τ := by
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have hexp : (1 : ℝ) ≤ Real.exp ((2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using hexp
  have qdX :=
    vcV (m := m) (z := (u / a)) hz
  have qci : -Real.log ‖qB m (u / a)‖ ≤ (2 : ℝ) * (r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖qB m (u / a)‖ ≤ (2 : ℝ) * ‖u / a‖ ^ (m + 1) := by
      linarith [qdX]
    set x : ℝ := ‖u / a‖
    have hx1 : x ≤ 1 := le_trans (by simpa [x] using hz) (by norm_num)
    have hxpos : 0 < x := by
      simpa [x] using (norm_pos_iff.2 (div_ne_zero hu ha))
    have hτ_le' : τ ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hτ_le
    have qbj : x ^ ((m + 1 : ℕ) : ℝ) ≤ x ^ τ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hτ_le'
    have hpow : x ^ (m + 1) ≤ x ^ τ := by
      simpa [← Real.rpow_natCast] using qbj
    have h2x : (2 : ℝ) * x ^ (m + 1) ≤ (2 : ℝ) * x ^ τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h2 : (2 : ℝ) * ‖u / a‖ ^ (m + 1) ≤ (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ := by
      simpa [x] using h2x
    have h3 : (‖u‖ / ‖a‖) ^ τ = (r / ‖a‖) ^ τ := by
      simp [hur]
    exact (h1.trans h2).trans_eq (by simp [h3])
  have hpos : 0 < ‖qB m (u / a)‖ := by
    have : qB m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (vbf m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : (‖u / a‖ : ℝ) = 1 := by simpa [this] using (by simp [ha])
      linarith [hz, this]
    exact norm_pos_iff.2 this
  have hEq :
      ‖(qB m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖qB m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 qci
  simpa [hEq] using this
end Complex.Hadamard
end
end
section
noncomputable section
namespace Complex.Hadamard
open scoped BigOperators
open Filter Finset Real Topology
section qb2
variable {α : Type*}
private lemma vaL [DecidableEq α] (s : Finset α) (u : α → ℝ) :
  Summable (fun a => if a ∈ s then u a else 0) :=
 summable_of_ne_finset_zero (s := s) fun a ha => by simp [ha]
private lemma vdu [DecidableEq α] (s : Finset α) (u : α → ℝ) :
  (∑' a, if a ∈ s then u a else 0) = ∑ a ∈ s, u a := by
 classical
 simpa [Finset.sum_ite] using
  (hasSum_sum_of_ne_finset_zero (s := s) (f := fun a => if a ∈ s then u a else 0)
   fun a ha => by simp [ha]).tsum_eq
private lemma vjj (u₁ u₂ u₃ u₄ : α → ℝ)
    (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) :
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
      = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  calc
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
        = tsum (fun a => (u₁ a + u₂ a) + (u₃ a + u₄ a)) := by
          simp [add_comm, add_left_comm]
    _ = tsum (fun a => u₁ a + u₂ a) + tsum (fun a => u₃ a + u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [Summable.tsum_add h₁ h₂, Summable.tsum_add h₃ h₄]
        ring
end qb2
noncomputable def vaS (m : ℕ) (τ qE : ℝ) : ℝ :=
 ((qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (qE + 1)
lemma vff {m : ℕ} {τ qE : ℝ} (qp3 : 0 ≤ qE) :
  0 ≤ vaS m τ qE := by
 have hS : 0 ≤ qE + 1 := by linarith
 have hA : 0 ≤ (qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3 := by
  have qfA : 0 ≤ qw.Cφ := le_of_lt qw.viP
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have qlh : 0 ≤ (4 : ℝ) ^ τ := by positivity
  nlinarith [qfA, hm0, qlh]
 simpa [vaS] using mul_nonneg hA hS
lemma vaF
  {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r)
  (p : qv f (Set.univ : Set ℂ)) :
  (r / ‖qg p‖) ^ τ =
   (r ^ τ) * ((‖qg p‖⁻¹ : ℝ) ^ τ) := by
 have hp : 0 ≤ (‖qg p‖⁻¹ : ℝ) := by positivity
 simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
  (Real.mul_rpow (x := r) (y := (‖qg p‖⁻¹ : ℝ)) (z := τ) hr hp)
lemma vcX
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) :
    (∑' p : qv f (Set.univ : Set ℂ),
        (r / ‖qg p‖) ^ τ)
      = (r ^ τ) * ∑' p : qv f (Set.univ : Set ℂ),
          ‖qg p‖⁻¹ ^ τ := by
  calc
    (∑' p : qv f (Set.univ : Set ℂ),
        (r / ‖qg p‖) ^ τ)
        = ∑' p : qv f (Set.univ : Set ℂ),
            (r ^ τ) * (‖qg p‖⁻¹ : ℝ) ^ τ := by
            refine tsum_congr ?_
            intro p
            exact vaF (f := f) (τ := τ) hr p
    _ = (r ^ τ) * ∑' p : qv f (Set.univ : Set ℂ),
          ‖qg p‖⁻¹ ^ τ := by
        simp [tsum_mul_left]
lemma vcm
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (qz : 0 ≤ τ) :
    (∑' p : qv f (Set.univ : Set ℂ),
        (2 : ℝ) * (r / ‖qg p‖) ^ τ)
      ≤ (2 : ℝ) * ((∑' p : qv f (Set.univ : Set ℂ),
          ‖qg p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set qE : ℝ :=
    ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
  have htsum :
      (∑' p : qv f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖qg p‖) ^ τ)
        = (2 : ℝ) * (r ^ τ) * qE := by
    calc
      (∑' p : qv f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖qg p‖) ^ τ)
          = (2 : ℝ) * ∑' p : qv f (Set.univ : Set ℂ),
              (r / ‖qg p‖) ^ τ := by
              simp [tsum_mul_left]
      _ = (2 : ℝ) * ((r ^ τ) * qE) := by
              rw [vcX (f := f) (τ := τ) hr]
      _ = (2 : ℝ) * (r ^ τ) * qE := by ring
  have qar : 0 ≤ qE :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) qz
  have hS : qE ≤ qE + 1 := by linarith
  have hle : (r ^ τ) * qE ≤ (1 + r) ^ τ * (qE + 1) :=
    mul_le_mul h1r hS (by linarith) (by positivity)
  rw [htsum]
  have : (2 : ℝ) * (r ^ τ) * qE ≤ (2 : ℝ) * (qE + 1) * (1 + r) ^ τ := by
    nlinarith [hle]
  simpa [qE, mul_assoc, mul_left_comm, mul_comm] using this
lemma vde
  {f : ℂ → ℂ} {r τ : ℝ} (small : Finset (qv f (Set.univ : Set ℂ)))
  (hr : 0 ≤ r) (qz : 0 ≤ τ)
  (qZ :
   Summable (fun p : qv f (Set.univ : Set ℂ) =>
    ‖qg p‖⁻¹ ^ τ)) :
  (∑ p ∈ small, (r / ‖qg p‖) ^ τ)
   ≤ ((∑' p : qv f (Set.univ : Set ℂ),
     ‖qg p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
 set qE : ℝ :=
  ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
 have hsum_inv :
   (∑ p ∈ small, (‖qg p‖⁻¹ : ℝ) ^ τ) ≤ qE := by
  have hnn : ∀ p : qv f (Set.univ : Set ℂ),
    0 ≤ (‖qg p‖⁻¹ : ℝ) ^ τ := by
   intro p
   positivity
  simpa [qE] using
   (Summable.sum_le_tsum (s := small)
    (f := fun p : qv f (Set.univ : Set ℂ) =>
     (‖qg p‖⁻¹ : ℝ) ^ τ)
    (fun p _ => hnn p) qZ)
 have hsum_eq :
   ∑ p ∈ small, (r / ‖qg p‖) ^ τ =
    (r ^ τ) * ∑ p ∈ small, (‖qg p‖⁻¹ : ℝ) ^ τ := by
  simp [vaF (f := f) (τ := τ) hr, Finset.mul_sum]
 have h1r : r ^ τ ≤ (1 + r) ^ τ :=
  Real.rpow_le_rpow (by positivity) (by linarith) qz
 have hS : (∑ p ∈ small, (‖qg p‖⁻¹ : ℝ) ^ τ) ≤ qE + 1 := by
  linarith [hsum_inv]
 have hle :
   (r ^ τ) * (∑ p ∈ small, (‖qg p‖⁻¹ : ℝ) ^ τ)
    ≤ (1 + r) ^ τ * (qE + 1) :=
  mul_le_mul h1r hS (by positivity) (by positivity)
 simpa [qE, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hle
lemma veU {x₁ x₂ x₃ x₄ A B C : ℝ}
  (h₁ : x₁ ≤ A) (h₂ : x₂ ≤ B) (h₃ : x₃ ≤ B) (h₄ : x₄ ≤ C) :
  x₁ + x₂ + x₃ + x₄ ≤ A + 2 * B + C := by
 nlinarith
lemma veJ
  {xφ x0 xm xt Cφ m q Y T : ℝ}
  (hφ : xφ ≤ Cφ * q * Y * T)
  (h0 : x0 ≤ m * q * Y * T)
  (hm : xm ≤ m * q * Y * T)
  (ht : xt ≤ (2 : ℝ) * Y * T) :
  xφ + x0 + xm + xt ≤ (Cφ + (2 : ℝ) * m) * q * Y * T + (2 : ℝ) * Y * T := by
 have h :=
  veU hφ h0 hm ht
 have qdY :
   Cφ * (q * (Y * T)) + 2 * (m * (q * (Y * T))) + 2 * (Y * T)
    = (Cφ + (2 : ℝ) * m) * (q * (Y * T)) + (2 : ℝ) * (Y * T) := by
  ring
 simpa [mul_assoc, qdY] using h
lemma veP (A Y T : ℝ) :
  A * Y * T + (2 : ℝ) * Y * T = ((A + 2) * Y) * T := by
 ring
lemma veB {A S T : ℝ} (hS : 0 ≤ S + 1) (hT : 0 ≤ T) :
  ((A + 2) * (S + 1)) * T ≤ ((A + 3) * (S + 1)) * T := by
 have h : (A + 2) * (S + 1) ≤ (A + 3) * (S + 1) := by
  nlinarith
 exact mul_le_mul_of_nonneg_right h hT
lemma vgv
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (qv f (Set.univ : Set ℂ))) :
    letI : DecidableEq (qv f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
    let b : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    ∀ p, 0 ≤ b p := by
  classical
  dsimp
  intro p
  let ap : qv f (Set.univ : Set ℂ) → ℝ := fun q => ‖qg q‖
  have hap : ap p = ‖qg p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ qw.φ (r / ap p) := qw.vjf (t := r / ap p)
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1 + (r / ap p) ^ τ) := by positivity
    have : 0 ≤ qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ) := by
      nlinarith [hφ, hm0, h1]
    simpa [hap, hp, ap] using this
  · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
    have hpow : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
    have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hpow
    simpa [hap, hp, ap] using this
lemma vfV
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (qv f (Set.univ : Set ℂ)))
    (qZ :
      Summable (fun p : qv f (Set.univ : Set ℂ) =>
        ‖qg p‖⁻¹ ^ τ)) :
    letI : DecidableEq (qv f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
    let b : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    Summable b := by
  classical
  dsimp
  let ap : qv f (Set.univ : Set ℂ) → ℝ := fun q => ‖qg q‖
  let b : qv f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hb : Summable b := by
    let b₁ : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else 0
    let b₂ : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2 : ℝ) * (r / ap p) ^ τ
    have qeM : b = fun p => b₁ p + b₂ p := by
      funext p
      by_cases hp : p ∈ small <;> simp [b, b₁, b₂, hp]
    have hb₁ : Summable b₁ := by
      simpa [b₁] using
        vaL small
          (fun p => qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ))
    have hb₂ : Summable b₂ := by
      have hconst :
          Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖qg p‖⁻¹ ^ τ)) :=
        qZ.mul_left ((2 : ℝ) * (r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂, hp]
          · have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := by positivity
            simpa [b₂, hp] using this)
        (fun p => ?_) hconst
      by_cases hp : p ∈ small
      · have : 0 ≤ (2 : ℝ) * (r ^ τ) * (‖qg p‖⁻¹ ^ τ) := by positivity
        simpa [b₂, hp] using this
      · have hrpow : (r / ap p) ^ τ = (r ^ τ) * (‖qg p‖⁻¹ ^ τ) := by
          simpa [ap] using vaF (f := f) (τ := τ) hr p
        simp [b₂, hp, hrpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [qeM] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b, ap, hp]
lemma vhb
  {f : ℂ → ℂ} {τ R : ℝ} (qG : 0 < R) (qz : 0 ≤ τ)
  (small : Finset (qv f (Set.univ : Set ℂ)))
  (hsmall : ∀ p ∈ small, ‖qg p‖ ≤ 4 * R)
  (qZ :
   Summable
    (fun p : qv f (Set.univ : Set ℂ) =>
     ‖qg p‖⁻¹ ^ τ)) :
  (small.card : ℝ)
   ≤ (4 * R) ^ τ
     * ((∑' p : qv f (Set.univ : Set ℂ),
        ‖qg p‖⁻¹ ^ τ) + 1) := by
 classical
 set qE : ℝ :=
  ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
 have hsum_le : (∑ p ∈ small, ‖qg p‖⁻¹ ^ τ) ≤ qE := by
  have hnn :
    ∀ p : qv f (Set.univ : Set ℂ),
     0 ≤ ‖qg p‖⁻¹ ^ τ := by
   intro p
   exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  simpa [qE] using
   (Summable.sum_le_tsum (s := small)
    (f := fun p : qv f (Set.univ : Set ℂ) =>
     ‖qg p‖⁻¹ ^ τ)
    (fun p _ => hnn p) qZ)
 have qeN :
   (small.card : ℝ) ≤ ∑ p ∈ small, (4 * R) ^ τ * ‖qg p‖⁻¹ ^ τ := by
  have hcard_eq : (small.card : ℝ) = ∑ p ∈ small, (1 : ℝ) := by simp
  rw [hcard_eq]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp_le : ‖qg p‖ ≤ 4 * R := hsmall p hp
  have hap : 0 < ‖qg p‖ :=
   norm_pos_iff.2 (vao p)
  have hbase : (1 : ℝ) ≤ (4 * R) / ‖qg p‖ := by
   exact (le_div_iff₀ hap).2 (by simpa [mul_one] using hp_le)
  have : (1 : ℝ) ≤ ((4 * R) / ‖qg p‖) ^ τ :=
   Real.one_le_rpow hbase qz
  have hdiv :
    ((4 * R) / ‖qg p‖) ^ τ =
     (4 * R) ^ τ * (‖qg p‖)⁻¹ ^ τ := by
   have h4 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt qG]
   have ha : 0 ≤ (‖qg p‖ : ℝ)⁻¹ := by positivity
   simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (Real.mul_rpow (x := (4 * R : ℝ))
     (y := (‖qg p‖ : ℝ)⁻¹) (z := τ) h4 ha)
  have : (1 : ℝ) ≤ (4 * R) ^ τ * ‖qg p‖⁻¹ ^ τ := by
   simpa [hdiv] using this
  exact this
 have hgeom :
   (small.card : ℝ) ≤ (4 * R) ^ τ * (∑ p ∈ small, ‖qg p‖⁻¹ ^ τ) := by
  simpa [Finset.mul_sum] using qeN
 have qeO : (small.card : ℝ) ≤ (4 * R) ^ τ * qE := by
  exact hgeom.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
 have hS_le : (4 * R) ^ τ * qE ≤ (4 * R) ^ τ * (qE + 1) := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith
 have : (small.card : ℝ) ≤ (4 * R) ^ τ * (qE + 1) := qeO.trans hS_le
 simpa [qE, add_comm, add_left_comm, add_assoc, mul_assoc] using this
lemma vhE
  {τ R r : ℝ} (qG : 0 < R) (hrpos : 0 < r) (q9 : R ≤ r) (qz : 0 ≤ τ) :
  (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ := by
 have qfB : R ≤ 1 + r := by linarith [q9, le_of_lt hrpos]
 have qhO : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt qG]
 have : (4 * R) ^ τ ≤ (4 * (1 + r)) ^ τ := by
  refine Real.rpow_le_rpow qhO ?_ qz
  nlinarith [qfB]
 have hmul : (4 * (1 + r)) ^ τ = (4 : ℝ) ^ τ * (1 + r) ^ τ := by
  have h4 : 0 ≤ (4 : ℝ) := by norm_num
  have h1 : 0 ≤ (1 + r : ℝ) := by positivity
  simpa [mul_assoc] using
   (Real.mul_rpow (x := (4 : ℝ)) (y := (1 + r : ℝ)) (z := τ) h4 h1)
 simpa [hmul] using this
open Classical in
theorem vgy
    {f : ℂ → ℂ} {m : ℕ} {τ R r : ℝ}
    (qG : 0 < R)
    (hrpos : 0 < r)
    (q9 : R ≤ r)
    (qz : 0 ≤ τ)
    (qH : Set (qv f (Set.univ : Set ℂ)))
    (qC : qH.Finite)
    (q5 :
      qH = {p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤ 4 * R})
    (qZ :
      Summable (fun p : qv f (Set.univ : Set ℂ) => ‖qg p‖⁻¹ ^ τ))
    (qaG :
      let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
      let a : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
      (∑ p ∈ small, qw.φ (r / a p)) ≤ qw.Cφ * (small.card : ℝ)) :
    let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
    letI : DecidableEq (qv f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
    let b : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    let qE : ℝ := ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
    let qJ : ℝ := vaS m τ qE
    ∀ s : Finset (qv f (Set.univ : Set ℂ)),
      (∑ p ∈ s, b p) ≤ qJ * (1 + r) ^ τ := by
  classical
  intro small ap b qE qJ s
  have hr : 0 ≤ r := le_of_lt hrpos
  have qar : 0 ≤ qE :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have qdZ : ∀ p, p ∈ small ↔ p ∈ qH := by
    intro p
    simp [small, qC.mem_toFinset]
  have qfC :
      (∑ p ∈ small, qw.φ (r / ap p)) ≤ qw.Cφ * (small.card : ℝ) := by
    simpa [small, ap] using qaG
  have hb_nonneg : ∀ p, 0 ≤ b p := by
    simpa [ap, b] using (vgv (f := f) (m := m) (τ := τ) (r := r) hr small)
  have qbC : Summable b := by
    simpa [ap, b] using
      (vfV (f := f) (m := m) (τ := τ) (r := r) hr small qZ)
  have qdl : ∀ p ∈ small, ‖qg p‖ ≤ 4 * R := by
    intro p hp
    have : p ∈ qH := (qdZ p).1 hp
    simpa [q5] using this
  have hcard_le : (small.card : ℝ) ≤ (4 * R) ^ τ * (qE + 1) := by
    simpa [qE, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (vhb (f := f) (τ := τ) (R := R) qG qz small qdl qZ)
  have qiR : (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ :=
    vhE (τ := τ) (R := R) (r := r) qG hrpos q9 qz
  have qeP : (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (qE + 1) := by
    have : (4 * R) ^ τ * (qE + 1) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (qE + 1) := by
      exact mul_le_mul_of_nonneg_right qiR (by linarith [qar])
    exact le_trans hcard_le this
  have qd0 :
      (∑' p : qv f (Set.univ : Set ℂ), b p) ≤ qJ * (1 + r) ^ τ := by
    let bφ : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then qw.φ (r / ap p) else 0
    let b0 : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) else 0
    let qac : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) * (r / ap p) ^ τ else 0
    let bt : qv f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2 : ℝ) * (r / ap p) ^ τ
    have qc0 : ∀ p, b p ≤ bφ p + b0 p + qac p + bt p := by
      intro p
      by_cases hp : p ∈ small
      · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
        have hx : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
        have hpos : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b, bφ, b0, qac, bt, hp]
        nlinarith
      · simp [b, bφ, b0, qac, bt, hp]
    have qeQ : Summable (fun p => bφ p + b0 p + qac p + bt p) := by
      have qbn : Summable bφ := by
        simpa [bφ] using vaL small (fun p => qw.φ (r / ap p))
      have qbL : Summable b0 := by
        simpa [b0] using vaL small (fun _ => (m : ℝ))
      have qa6 : Summable qac := by
        simpa [qac] using vaL small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      have qbM : Summable bt := by
        have hconst : Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖qg p‖⁻¹ ^ τ)) :=
          qZ.mul_left ((2 : ℝ) * (r ^ τ))
        refine hconst.congr ?_
        intro p
        simp [bt, ap, vaF (f := f) (τ := τ) hr p,
          mul_assoc, mul_left_comm, mul_comm]
      have h' : Summable (fun p => bφ p + b0 p + (qac p + bt p)) :=
        (qbn.add qbL).add (qa6.add qbM)
      simpa [add_assoc] using h'
    have qbK :
        (∑' p : qv f (Set.univ : Set ℂ), b p)
          ≤ ∑' p : qv f (Set.univ : Set ℂ), (bφ p + b0 p + qac p + bt p) :=
      (hasSum_le qc0 qbC.hasSum qeQ.hasSum)
    have qeR :
        (∑' p : qv f (Set.univ : Set ℂ), bφ p)
          = ∑ p ∈ small, qw.φ (r / ap p) := by
      classical
      simpa [bφ] using vdu small (fun p => qw.φ (r / ap p))
    have qfD :
        (∑' p : qv f (Set.univ : Set ℂ), b0 p)
          = (m : ℝ) * (small.card : ℝ) := by
      classical
      have : (∑' p : qv f (Set.univ : Set ℂ), b0 p) = ∑ p ∈ small, (m : ℝ) := by
        simpa [b0] using vdu small (fun _ => (m : ℝ))
      simp [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have qd1 :
        (∑' p : qv f (Set.univ : Set ℂ), qac p)
          = (m : ℝ) * ∑ p ∈ small, (r / ap p) ^ τ := by
      classical
      have :
          (∑' p : qv f (Set.univ : Set ℂ), qac p)
            = ∑ p ∈ small, (m : ℝ) * (r / ap p) ^ τ := by
        simpa [qac] using vdu small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      simp [this, Finset.mul_sum]
    have qfE :
        (∑' p : qv f (Set.univ : Set ℂ), bt p)
          ≤ (2 : ℝ) * (qE + 1) * (1 + r) ^ τ := by
      simpa [bt, ap, qE] using
        vcm (f := f) (τ := τ) hr qz
    have qbo :
        (∑ p ∈ small, (r / ap p) ^ τ) ≤ (qE + 1) * (1 + r) ^ τ := by
      simpa [ap, qE] using
        vde (f := f) (τ := τ) small hr qz qZ
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have qfA : 0 ≤ qw.Cφ := le_of_lt qw.viP
    have hS : 0 ≤ qE + 1 := by linarith [qar]
    have qcj :
        (∑' p : qv f (Set.univ : Set ℂ), (bφ p + b0 p + qac p + bt p))
          ≤ (((qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (qE + 1))
              * (1 + r) ^ τ := by
      have hφ_le :
          (∑' p : qv f (Set.univ : Set ℂ), bφ p)
            ≤ qw.Cφ * (small.card : ℝ) := by
        simpa [qeR] using qfC
      have qhP :
          (∑' p : qv f (Set.univ : Set ℂ), b0 p)
            ≤ (m : ℝ) * (small.card : ℝ) := by
        simp [qfD]
      have qfF :
          (∑' p : qv f (Set.univ : Set ℂ), qac p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ := by
        have h0 :
            (∑' p : qv f (Set.univ : Set ℂ), qac p)
              ≤ (m : ℝ) * ((qE + 1) * (1 + r) ^ τ) := by
          have hmul := mul_le_mul_of_nonneg_left qbo hm0
          simpa [qd1, mul_assoc, mul_left_comm, mul_comm] using hmul
        have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) qz
        have hscale :
            (m : ℝ) * ((qE + 1) * (1 + r) ^ τ)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ := by
          have hnonneg : 0 ≤ (m : ℝ) * ((qE + 1) * (1 + r) ^ τ) := by
            have : 0 ≤ (qE + 1) * (1 + r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_right h1 hnonneg)
        exact h0.trans hscale
      have qhQ :
          (∑' p : qv f (Set.univ : Set ℂ), bt p)
            ≤ (2 : ℝ) * (qE + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using qfE
      have hsplit :
          (∑' p : qv f (Set.univ : Set ℂ), (bφ p + b0 p + qac p + bt p))
            = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, qac p) + (∑' p, bt p) := by
        classical
        have qbn : Summable bφ := by
          simpa [bφ] using vaL small (fun p => qw.φ (r / ap p))
        have qbL : Summable b0 := by
          simpa [b0] using vaL small (fun _ => (m : ℝ))
        have qa6 : Summable qac := by
          simpa [qac] using vaL small (fun p => (m : ℝ) * (r / ap p) ^ τ)
        have qbM : Summable bt := by
          have hconst :
              Summable
                (fun p : qv f (Set.univ : Set ℂ) =>
                  (2 : ℝ) * (r ^ τ) * ((‖qg p‖⁻¹ : ℝ) ^ τ)) :=
            qZ.mul_left ((2 : ℝ) * (r ^ τ))
          refine hconst.congr ?_
          intro p
          simp [bt, ap, vaF (f := f) (τ := τ) hr p,
            mul_assoc, mul_left_comm, mul_comm]
        exact vjj bφ b0 qac bt qbn qbL qa6 qbM
      have qb3 :
          (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using qeP
      have qgx :
          (∑' p : qv f (Set.univ : Set ℂ), bφ p) ≤
            qw.Cφ * (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ := by
        have : qw.Cφ * (small.card : ℝ) ≤
            qw.Cφ * ((4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left qb3 qfA
        exact hφ_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have qgy :
          (∑' p : qv f (Set.univ : Set ℂ), b0 p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ := by
        have : (m : ℝ) * (small.card : ℝ) ≤ (m : ℝ) * ((4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left qb3 hm0
        exact qhP.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have qb4 :
          (∑' p : qv f (Set.univ : Set ℂ), (bφ p + b0 p + qac p + bt p))
            ≤ (qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (qE + 1) * (1 + r) ^ τ := by
        rw [hsplit]
        set Y : ℝ := qE + 1 with hY
        set T : ℝ := (1 + r) ^ τ with hT
        have qgz :
            (∑' p : qv f (Set.univ : Set ℂ), bφ p)
              ≤ qw.Cφ * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using qgx
        have qgA :
            (∑' p : qv f (Set.univ : Set ℂ), b0 p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using qgy
        have qeS :
            (∑' p : qv f (Set.univ : Set ℂ), qac p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using qfF
        have qgB :
            (∑' p : qv f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * Y * T := by
          simpa [hY, hT, mul_assoc] using qhQ
        have hmain :=
          veJ
            (q := (4 : ℝ) ^ τ) qgz qgA qeS qgB
        simpa [Y, T, add_assoc] using hmain
      have qdY :
          (qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (qE + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (qE + 1) * (1 + r) ^ τ
            = (((qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (qE + 1)) * (1 + r) ^ τ := by
        exact veP
          ((qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ) (qE + 1) ((1 + r) ^ τ)
      rw [← qdY]
      exact qb4
    have qgC :
        (((qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (qE + 1)) * (1 + r) ^ τ
          ≤ qJ * (1 + r) ^ τ := by
      simpa [qJ, vaS, mul_assoc, mul_left_comm, mul_comm] using
        veB
          (A := (qw.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ)
          (S := qE) (T := (1 + r) ^ τ) hS (by positivity)
    exact (le_trans (le_trans qbK qcj) qgC)
  have qdm :
      (∑ p ∈ s, b p) ≤ (∑' p : qv f (Set.univ : Set ℂ), b p) := by
    simpa using
      (Summable.sum_le_tsum (s := s) (f := b) (fun p _ => hb_nonneg p) qbC)
  exact qdm.trans qd0
end Complex.Hadamard
end
end
section
noncomputable section
open scoped BigOperators
open Filter Finset Real Topology
lemma Finset.viO {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm
lemma vfz {α : Type} {f : α → ℝ} {a : ℝ}
  (hf : HasProd f a (SummationFilter.unconditional α))
  {B : ℝ} (hB : ∀ s : Finset α, (∏ x ∈ s, f x) ≤ Real.exp B) :
  a ≤ Real.exp B :=
 hasProd_le_of_prod_le (L := (SummationFilter.unconditional α)) hf hB
lemma vfA {α : Type} {fac : α → ℂ} {F : ℂ}
  (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
  HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α) := by
 change
  Tendsto (fun s : Finset α => ∏ x ∈ s, (fac x)⁻¹)
   (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
 have hprod :
   Tendsto (fun s : Finset α => ∏ x ∈ s, fac x)
    (SummationFilter.unconditional α).filter (𝓝 F) := by
  simpa [HasProd] using hfac
 have hinv :
   Tendsto (fun s : Finset α => (∏ x ∈ s, fac x)⁻¹)
    (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
  hprod.inv₀ hF
 refine hinv.congr' (Filter.Eventually.of_forall ?_)
 intro s
 simp [Finset.prod_inv_distrib]
lemma veO {α : Type} {fac : α → ℂ} {F : ℂ}
  (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
  HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) := by
 change
  Tendsto (fun s : Finset α => ∏ x ∈ s, ‖(fac x)⁻¹‖)
   (SummationFilter.unconditional α).filter (𝓝 ‖F⁻¹‖)
 have hnorm := (vfA hfac hF).norm
 refine hnorm.congr' (Filter.Eventually.of_forall ?_)
 intro s
 simp [norm_inv, Finset.prod_inv_distrib]
lemma vcM {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α))
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ x, ‖(fac x)⁻¹‖ ≤ Real.exp (b x))
    (hsum : ∀ s : Finset α, (∑ x ∈ s, b x) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  by_cases hF : F = 0
  · subst hF
    simpa using exp_nonneg B
  have hnorm :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    veO hfac hF
  have hprod : ∀ s : Finset α, (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp B := by
    intro s
    have h0 : ∀ x ∈ s, 0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s, b x) := by
      refine Finset.viO s (a := fun x => ‖(fac x)⁻¹‖) (b := b) h0 ?_
      intro x hx
      simpa using hterm x
    have h2 : Real.exp (∑ x ∈ s, b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (hsum s)
    exact h1.trans h2
  exact vfz hnorm hprod
end
end
section
open Metric
namespace Complex
theorem vet {f : ℂ → ℂ} {M r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0 = 0)
    (qd2 : ∀ w, ‖w‖ ≤ R → (f w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := lt_trans hr hlt
  have qag : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hlt
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := ball_subset_closedBall hw
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have hf_map : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w | w.re ≤ M} := by
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have hw' : ‖w‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hw
    exact qd2 w hw'.le
  have hbc :=
    borelCaratheodory_zero hM hf_diff hf_map hR qag hf0
  have hzR : ‖z‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at qag
    exact qag
  have hmono : ‖z‖ / (R - ‖z‖) ≤ r / (R - r) := by
    have qiS : 0 < R - r := sub_pos.mpr hlt
    have hden : 0 < R - ‖z‖ := sub_pos.mpr hzR
    rw [div_le_div_iff₀ hden qiS]
    nlinarith [hz, norm_nonneg z]
  have hM' : 0 ≤ 2 * M := mul_nonneg (by norm_num) (le_of_lt hM)
  calc ‖f z‖
      ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
    _ ≤ 2 * M * (r / (R - r)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hmono hM'
    _ = 2 * M * r / (R - r) := by ring
end Complex
end
section
noncomputable section
namespace Complex
namespace Hadamard
open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology
theorem vdq {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = Complex.exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have qgD : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using! (qgD.div hH h_nonzero)
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have qbN : ∀ z, HasDerivAt h (L z) z := by
    intro z
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]; linarith [norm_nonneg z]
    have qag : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have qfG : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using qfG.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := qag)
  have hh : Differentiable ℂ h := fun z => (qbN z).differentiableAt
  have qli : ∀ z, deriv h z = L z := fun z => (qbN z).deriv
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))
  have qeT : ∀ z, H z = Complex.exp (k z) := by
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have qfH : ∀ z, deriv F z = 0 := by
      intro z
      have qhR : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have qhS : HasDerivAt k (L z) z := by
        have qhT : HasDerivAt h (L z) z := qbN z
        simpa [k, L] using qhT.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp qhS)
      have hDiv := (HasDerivAt.div hExp qhR (h_nonzero z))
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using! hDiv.deriv
      rw [this]
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := (hk.cexp).div hH h_nonzero
    have qfI : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff qfH z 0
    have hF0 : F 0 = 1 := by
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (qfI z)
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    have : Complex.exp (k z) = H z := by
      field_simp [hHz] at this
      simpa using this
    exact this.symm
  have qdn : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [qeT z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    simpa [hlog_eq] using hlog_le
  have qaM : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    have qdo : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R qG z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := qdn z
      have qlj : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      have qlk : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        nlinarith [this, qlj, qlk]
      exact this
    have qbO : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R qG z hz
      have qc1 : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have qgE : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w _hw
        exact (hf.analyticAt w)
      have qd2 : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := qdo R qG w hw
        linarith
      have qiT :=
        vet (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          qgE qc1 hlt hMpos hf0 qd2 (z := z) hz
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [qG.ne'] ; ring
      simpa [hconst] using qiT
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R qG
      have qc1 : 0 < R / 2 := by nlinarith
      have qdp : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have qcx :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact qbO R qG z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := qc1) qdp qcx)
    have qd3 : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne
      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have qgF : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R qG
        simpa [RHS] using hCauchy R qG
      have qc2 : Tendsto RHS atTop (𝓝 0) := by
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos
        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have qc3 : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have qll : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact qll.symm
            exact Filter.Tendsto.congr' hEq qc3
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this
        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using! hpow.inv_tendsto_atTop
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv' : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv')
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            field_simp [hR]; ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have qfJ : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have qck :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            have qiU : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) qiU)
            exact hident.symm
          have hmul :
              Tendsto
                (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m))
                atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (qfJ.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul
        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul qck)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto
              (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹)
              atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop
              (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) := tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have qgG : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [qgG] using hmul
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 qc2).2 _ (half_pos ha)
      have qcl : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R qG
        exact qgF R qG
      rcases (qcl.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ :=
        (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have qlm : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have qln : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub :
        iteratedDeriv m f 0 =
          iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using! (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) qlm qln)
    have qgH : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, qgH]
    simpa [hf_eq] using qd3
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have qiV :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans qiV
  have qgI : ∀ z, k z = Polynomial.eval z P := by
    intro z
    have qgJ := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have qlo : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := qaM m qlo
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using qgJ.symm
        _ = _ := htsum
    have qiW :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have qfK :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [qiW] using qfK
  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [qeT z]
  simp [this, qgI z]
end Hadamard
end Complex
end
end
section
noncomputable section
namespace Complex
namespace Hadamard
open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology
open Polynomial
private lemma vgF {n : ℕ} (hn : 0 < n) (w : ℂ) : ∃ z : ℂ, z ^ n = w := by
  classical
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w / n), ?_⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w / n)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.log w / n)) := by
              simpa using (Complex.exp_nat_mul (Complex.log w / n) n).symm
      _ = Complex.exp (Complex.log w) := by
            have : (n : ℂ) * (Complex.log w / n) = Complex.log w := by
              field_simp [hn0]
            simp [this]
      _ = w := by simpa using (Complex.exp_log hw)
private lemma vhX (a : ℂ) (ha : a ≠ 0) :
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  have qbe : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have qfL : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt qbe)
  have hmul : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) :=
    Complex.mul_conj a
  have hcast : (Complex.normSq a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (Complex.normSq_eq_norm_sq a)
  have hdiv : ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) = (‖a‖ : ℂ) := by
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = (‖a‖ : ℂ) * (‖a‖ : ℂ) := by
      simp [pow_two]
    calc
      ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ)
          = ((‖a‖ : ℂ) * (‖a‖ : ℂ)) / (‖a‖ : ℂ) := by simp [this]
      _ = (‖a‖ : ℂ) := by
            field_simp [qfL]
  calc
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ))
        = (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) := by
            simp [div_eq_mul_inv, mul_assoc]
    _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) := by simp [hmul]
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) := by simp [hcast]
    _ = (‖a‖ : ℂ) := hdiv
private lemma vfn
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ∃ z : ℂ, ‖z‖ = R ∧
          (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  classical
  set n : ℕ := P.natDegree
  have hn0 : 0 < n := hn
  have hP0 : P ≠ 0 := by
    intro h0
    simp [n, h0] at hn0
  have hLC : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  set a : ℂ := P.leadingCoeff
  have ha : a ≠ 0 := hLC
  have qbD : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set qaC : ℂ := (starRingEnd ℂ) a / (‖a‖ : ℂ)
  have qcy : ‖qaC‖ = (1 : ℝ) := by
    calc
      ‖qaC‖ = ‖(starRingEnd ℂ) a‖ / ‖(‖a‖ : ℂ)‖ := by
        simp [qaC]
      _ = ‖a‖ / ‖a‖ := by simp
      _ = (1 : ℝ) := by
        field_simp [qbD.ne']
  rcases vgF (n := n) hn0 (w := qaC) with ⟨w, hw⟩
  have qgK : ‖w‖ = (1 : ℝ) := by
    have hpow : (‖w‖ : ℝ) ^ n = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) hw
      simpa [norm_pow, qcy] using this
    have hn0' : n ≠ 0 := Nat.ne_of_gt hn0
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn0').1 hpow
  set S : ℝ := ∑ i ∈ Finset.range n, ‖P.coeff i‖
  set R0 : ℝ := max 1 (2 * S / ‖a‖)
  refine ⟨R0, ?_, ?_⟩
  · have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro R hR
    have qbp : (1 : ℝ) ≤ R := by
      exact le_trans (le_max_left _ _) hR
    have qcp : 0 ≤ R := le_trans (by norm_num) qbp
    set z : ℂ := (R : ℂ) * w
    have hz_norm : ‖z‖ = R := by
      have : ‖z‖ = |R| * ‖w‖ := by
        simp [z]
      simp [this, qgK, abs_of_nonneg qcp]
    have h_eval : P.eval z =
        (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
      have hsum : P.eval z = ∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i := by
        have : P.natDegree + 1 = n + 1 := by simp [n]
        simpa [this] using (Polynomial.eval_eq_sum_range (p := P) z)
      have hsplit :
          (∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i)
            = (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
        simpa using (Finset.sum_range_succ (f := fun i => P.coeff i * z ^ i) n)
      exact hsum.trans hsplit
    have qc4 :
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ S * R ^ (n - 1) := by
      have h1 :
          ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := by
        simpa using (norm_sum_le (Finset.range n) (fun i => P.coeff i * z ^ i))
      have hterm : ∀ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hi_le : i ≤ n - 1 := Nat.le_pred_of_lt hi_lt
        have qaJ : ‖z‖ ^ i ≤ R ^ (n - 1) := by
          have hmono : ‖z‖ ^ i ≤ ‖z‖ ^ (n - 1) :=
            pow_le_pow_right₀ (by simpa [hz_norm] using qbp) hi_le
          simpa [hz_norm] using hmono
        calc
          ‖P.coeff i * z ^ i‖ = ‖P.coeff i‖ * ‖z‖ ^ i := by
            simp [norm_pow]
          _ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_left qaJ (norm_nonneg _)
      have h2 :
          ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := by
        exact Finset.sum_le_sum (fun i hi => hterm i hi)
      have h3 :
          (∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1))
            = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := by
        simp [Finset.sum_mul]
      have hsum_le : (∑ i ∈ Finset.range n, ‖P.coeff i‖) ≤ S := by
        simp [S]
      calc
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := h1
        _ ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := h2
        _ = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := h3
        _ ≤ S * R ^ (n - 1) := by
              exact mul_le_mul_of_nonneg_right hsum_le (pow_nonneg qcp _)
    have qeU : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by
      have qhU : w ^ n = qaC := hw
      have qhV : a * w ^ n = (‖a‖ : ℂ) := by
        have : a * w ^ n = a * qaC := by simp [qhU]
        simpa [qaC, a] using (this.trans (vhX a ha))
      have hz_pow : z ^ n = ((R : ℂ) ^ n) * (w ^ n) := by
        simp [z, mul_pow, mul_comm]
      have qgL : P.coeff n = a := by simp [a, n, Polynomial.coeff_natDegree]
      have qlp : ∀ m : ℕ, (((R : ℂ) ^ m).re) = R ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [pow_succ, ih, mul_re]
      calc
        (P.coeff n * z ^ n).re
            = (a * z ^ n).re := by simp [qgL]
        _ = (a * (((R : ℂ) ^ n) * (w ^ n))).re := by simp [hz_pow]
        _ = (((R : ℂ) ^ n) * (a * (w ^ n))).re := by
              ring_nf
        _ = (((R : ℂ) ^ n) * (‖a‖ : ℂ)).re := by simp [qhV]
        _ = (((R : ℂ) ^ n).re) * ‖a‖ := by
              simp [mul_re]
        _ = (R ^ n) * ‖a‖ := by simp [qlp n]
        _ = ‖a‖ * R ^ n := by ring
    refine ⟨z, hz_norm, ?_⟩
    have qeV : (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re
        ≥ -‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have habs : |(∑ i ∈ Finset.range n, P.coeff i * z ^ i).re|
          ≤ ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        Complex.abs_re_le_norm _
      have := neg_le_of_abs_le habs
      simpa using this
    have qfM :
        (P.eval z).re ≥ (P.coeff n * z ^ n).re - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have : (P.eval z).re =
          (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re + (P.coeff n * z ^ n).re := by
        simp [h_eval, add_comm]
      linarith [this, qeV]
    have qbP : R0 ≤ R := hR
    have qiX : 2 * S / ‖a‖ ≤ R := le_trans (le_max_right _ _) qbP
    have qG : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) qbp
    have qd4 : 0 ≤ R := le_of_lt qG
    have qhW : 1 ≤ n := Nat.succ_le_of_lt hn0
    have qeW : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R ^ n := by
      have ha_pos : 0 < ‖a‖ := qbD
      have hS_le : S ≤ (‖a‖ / 2) * R := by
        have : 2 * S ≤ ‖a‖ * R := by
          have := (mul_le_mul_of_nonneg_left qiX (by linarith [ha_pos.le] : (0 : ℝ) ≤ ‖a‖))
          have hne : (‖a‖ : ℝ) ≠ 0 := ne_of_gt ha_pos
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hne] using this
        have : S ≤ (‖a‖ * R) / 2 := by linarith
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R * R ^ (n - 1) := by
        have qdq : 0 ≤ R ^ (n - 1) := pow_nonneg qd4 _
        exact mul_le_mul_of_nonneg_right hS_le qdq
      have hRR : R * R ^ (n - 1) = R ^ n := by
        have : n = (n - 1) + 1 := by
          exact (Nat.sub_add_cancel qhW).symm
        rw [this, pow_succ]
        ring_nf; grind
      simpa [mul_assoc, hRR] using this
    have qeX :
        (‖a‖ / 2) * R ^ n ≤ (P.eval z).re := by
      have qgM : ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (‖a‖ / 2) * R ^ n := by
        exact qc4.trans qeW
      have hlead : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by simpa [a] using qeU
      have qeY :
          (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (P.eval z).re := by
        simpa [hlead] using qfM
      have hsub :
          (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤
            (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        sub_le_sub_left qgM (‖a‖ * R ^ n)
      have qlq : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n = (‖a‖ / 2) * R ^ n := by ring
      have : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤ (P.eval z).re :=
        hsub.trans qeY
      simpa [qlq] using this
    simpa [a, n] using qeX
theorem vdJ
    {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ)
    (hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree = 0
  · simp [hdeg]
  · have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    rcases vfn (P := P) hnpos with ⟨R0, qnw, qlr⟩
    rcases hgrowth with ⟨C, hCpos, hC⟩
    have qhX : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0 := by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c : ℝ := ‖P.leadingCoeff‖ / 2
    have hcpos : 0 < c := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact (div_pos qhX this)
    have qd5 : (P.natDegree : ℝ) ≤ ρ := by
      by_contra hnlt
      have qiY : ρ < (P.natDegree : ℝ) := lt_of_not_ge hnlt
      let δ : ℝ := (P.natDegree : ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 qiY
      let K0 : ℝ := (C * (2 : ℝ) ^ ρ) / c
      have hK0 : ∃ R1, ∀ R ≥ R1, K0 + 1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ), K0 + 1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0 + 1)
        rcases (eventually_atTop.1 h) with ⟨R1, hR1⟩
        exact ⟨R1, hR1⟩
      rcases hK0 with ⟨R1, hR1⟩
      set R : ℝ := max (max R0 1) R1
      have qbP : R0 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
      have qbp : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
      have qfN : R1 ≤ R := le_max_right _ _
      have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) qbp
      have hRδ : K0 + 1 ≤ R ^ δ := hR1 R qfN
      rcases qlr R qbP with ⟨z, hz_norm, hz_re⟩
      have qd6 :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) := by
        have hpos : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle :
            ‖Complex.exp (Polynomial.eval z P)‖ ≤
              1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have hlog_le : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log hpos hle
        have hlog_eq : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re := by
          simp [Complex.norm_exp]
        simpa [hlog_eq] using hlog_le
      have qd7 :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ :=
        hC z
      have hmain : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + R) ^ ρ := by
        have qhY : c * R ^ P.natDegree ≤ (P.eval z).re := by
          simpa [c] using hz_re
        have qgN : c * R ^ (P.natDegree : ℝ) ≤ (P.eval z).re := by
          simpa [Real.rpow_natCast, c] using qhY
        have : c * R ^ (P.natDegree : ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          qgN.trans qd6
        have : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + ‖z‖) ^ ρ :=
          this.trans qd7
        simpa [hz_norm] using this
      have qhZ : (1 + R : ℝ) ≤ R * 2 := by linarith
      have hpow1 : (1 + R : ℝ) ^ ρ ≤ (R * 2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hR_pos.le]) qhZ hρ
      have hR2 : (R * 2) ^ ρ = R ^ ρ * (2 : ℝ) ^ ρ := by
        have qbJ : 0 ≤ R := le_of_lt hR_pos
        have qaB : 0 ≤ (2 : ℝ) := by norm_num
        simpa [mul_assoc] using (Real.mul_rpow qbJ qaB (z := ρ))
      have qc3 : c * R ^ (P.natDegree : ℝ) ≤ C * (R ^ ρ * (2 : ℝ) ^ ρ) := by
        have := le_trans hmain (mul_le_mul_of_nonneg_left hpow1 (le_of_lt hCpos))
        simpa [hR2, mul_assoc, mul_left_comm, mul_comm] using this
      have qc5 : 0 < R ^ ρ := Real.rpow_pos_of_pos hR_pos _
      have qgO : (R ^ ρ : ℝ) ≠ 0 := ne_of_gt qc5
      have hdiv :
          (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) ≤ C * (2 : ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right qc3 (le_of_lt qc5)
        have qls : (C * (R ^ ρ * (2 : ℝ) ^ ρ)) / (R ^ ρ) = C * (2 : ℝ) ^ ρ := by
          field_simp [qgO]
        simpa [qls, mul_assoc, mul_left_comm, mul_comm] using h
      have hRsub : R ^ δ = R ^ (P.natDegree : ℝ) / R ^ ρ := by
        simpa [δ] using (Real.rpow_sub hR_pos (P.natDegree : ℝ) ρ)
      have qgP : c * (R ^ δ) ≤ C * (2 : ℝ) ^ ρ := by
        have qlt : c * (R ^ δ) = (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) := by
          simp [hRsub, div_eq_mul_inv, mul_left_comm, mul_comm]
        simpa [qlt] using hdiv
      have qfO : R ^ δ ≤ K0 := by
        have : R ^ δ ≤ (C * (2 : ℝ) ^ ρ) / c := by
          refine (le_div_iff₀ hcpos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using qgP
        simpa [K0] using this
      have : K0 + 1 ≤ K0 := le_trans hRδ (le_trans qfO (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 qd5
theorem vcW {τ : ℝ} (hτ : 0 ≤ τ) (P : Polynomial ℂ)
  (hbound :
   ∃ C > 0, ∀ z : ℂ,
    ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ)) :
  P.natDegree ≤ Nat.floor τ := by
 rcases hbound with ⟨C, hCpos, hC⟩
 have qdr :
   ∃ C > 0, ∀ z : ℂ,
    Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ :=
  Real.vcc
   (f := fun z : ℂ => Complex.exp (Polynomial.eval z P))
   (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ
   (fun z => by linarith [norm_nonneg z]) hC
 exact vdJ (ρ := τ) hτ P qdr
end Hadamard
end Complex
end
end
section
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators
namespace Complex.Hadamard
lemma vdH
  {f : ℂ → ℂ} (qaa : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
  {B r : ℝ} (hrpos : 0 < r) (qgQ : r ≤ B)
  (qH : Set (qv f (Set.univ : Set ℂ))) (qC : qH.Finite)
  (q5 :
   qH = {p : qv f (Set.univ : Set ℂ) | ‖qg p‖ ≤ B})
  (q8 :
   let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
   let a : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
   r ∉ small.image a) :
  ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
 classical
 let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
 let a : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
 let bad : Finset ℝ := small.image a
 have qaF : r ∉ bad := by
  simpa [bad, small, a] using q8
 have qcM :
   ∀ p : qv f (Set.univ : Set ℂ),
    ‖qg p‖ ≤ B → r ≠ ‖qg p‖ := by
  intro p hpB hEq
  have hp_small : p ∈ small := by
   have hp_mem : p ∈ qH := by
    simpa [q5] using hpB
   simpa [small] using (qC.mem_toFinset.2 hp_mem)
  have : r ∈ bad := Finset.mem_image.2 ⟨p, hp_small, by simpa [a] using hEq.symm⟩
  exact (qaF this).elim
 exact vdn (f := f) qaa hnot
  (B := B) (r := r) hrpos qgQ qcM
theorem vca
    {f : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (qbQ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (qak : τ < (m + 1 : ℝ))
    (qz : 0 ≤ τ)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    (qZ : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ τ)) :
    let qE : ℝ :=
      ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
    let qJ : ℝ := vaS m τ qE
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R →
      ∀ (qH : Set (qv f (Set.univ : Set ℂ)))
        (qC : qH.Finite),
        qH =
            {p : qv f (Set.univ : Set ℂ) |
              ‖qg p‖ ≤ 4 * R} →
        (let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
         let a : qv f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖qg p‖
         r ∉ small.image a) →
        (let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
         let a : qv f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖qg p‖
         (∑ p ∈ small, (1 : ℝ) * qw.φ (r / a p)) ≤
          qw.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r →
          ‖(u ^ analyticOrderNatAt f 0 *
              qA m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (qJ * (1 + r) ^ τ) := by
  classical
  intro qE qJ R r qG qc6 q9 qau qH qC
    q5 q8 qaG u hur
  let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
  let a : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
  let bad : Finset ℝ := small.image a
  have qaF : r ∉ bad := by
    simpa [bad, small, a] using q8
  have hr1 : (1 : ℝ) ≤ r := le_trans qc6 q9
  have qc7 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 :=
    Complex.vem u (analyticOrderNatAt f 0) (by simpa [hur] using hr1)
  let fac : qv f (Set.univ : Set ℂ) → ℂ :=
    fun p => qB m (u / qg p)
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : qv f (Set.univ : Set ℂ)) (w : ℂ) =>
          qB m (w / qg p))
        (qA m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    vav (m := m) (f := f) h_sum
  have hprod :
      HasProd fac (qA m f (Set.univ : Set ℂ) u) :=
    hloc.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
  let ap : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
  have : DecidablePred (fun p : qv f (Set.univ : Set ℂ) => p ∈ small) :=
    Classical.decPred _
  let b : qv f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if hp : p ∈ small then
        qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hterm : ∀ p, ‖(fac p)⁻¹‖ ≤ Real.exp (b p) := by
    intro p
    by_cases hp : p ∈ small
    · have qgR : r ≠ ap p := by
        intro hEq
        have : r ∈ bad := by
          refine Finset.mem_image.2 ⟨p, hp, ?_⟩
          simp [ap, a, hEq]
        exact (qaF this).elim
      have qiZ : qg p ≠ 0 := vao p
      have qcX : (m : ℝ) ≤ τ := le_trans qbQ (le_of_lt hτ)
      have hnear :
          ‖(qB m (u / qg p))⁻¹‖
            ≤ Real.exp (qw.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
        simpa [ap] using
          (vdw (m := m) (τ := τ) (r := r)
              (u := u) (a := qg p)
              (hur := hur) (ha := qiZ) (hr := by simpa [ap] using qgR) qcX)
      simpa [fac, b, hp] using hnear
    · have hlarge : (4 * R : ℝ) < ap p := by
        have : ¬ap p ≤ 4 * R := by
          intro hle
          have : p ∈ small := by
            have hp_mem : p ∈ qH := by
              simpa [q5, ap] using hle
            simpa [small] using (qC.mem_toFinset.2 hp_mem)
          exact hp this
        exact lt_of_not_ge this
      have hz' : ‖u / qg p‖ ≤ (1 / 2 : ℝ) :=
        vbz (z := u) (a := qg p)
          (R := 2 * R) (by nlinarith [qG]) (by rw [hur]; exact qau)
          (by nlinarith [hlarge])
      have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt qak
      have hfar :
          ‖(qB m (u / qg p))⁻¹‖ ≤
            Real.exp ((2 : ℝ) * (r / ap p) ^ τ) := by
        simpa [ap] using
          (vdF (m := m) (τ := τ) (r := r)
              (u := u) (a := qg p)
              (hur := hur) (ha := vao p) (hz := hz') hτ_le)
      simpa [fac, b, hp] using hfar
  have hb_le :
      ∀ s : Finset (qv f (Set.univ : Set ℂ)),
        (∑ p ∈ s, b p) ≤ qJ * (1 + r) ^ τ := by
    intro s
    simpa [small, ap, b, qE, qJ, a, q5] using
      (Complex.Hadamard.vgy (f := f) (m := m) (τ := τ) (R := R) (r := r)
        (qG := qG) (hrpos := lt_of_lt_of_le qG q9)
        (q9 := q9) (qz := qz)
        (qH := qH) (qC := qC) (q5 := q5)
        (qZ := qZ)
        (qaG := by
          simpa [small, a, one_mul] using qaG)
        s)
  have qd8 :
      ‖(qA m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
        Real.exp (qJ * (1 + r) ^ τ) := by
    refine vcM
      (α := qv f (Set.univ : Set ℂ)) (fac := fac)
      (F := qA m f (Set.univ : Set ℂ) u)
      hprod (b := b) (B := qJ * (1 + r) ^ τ) ?_ ?_
    · exact hterm
    · intro s
      exact hb_le s
  have hmul :
      ‖(u ^ analyticOrderNatAt f 0 *
          qA m f (Set.univ : Set ℂ) u)⁻¹‖
        =
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
        ‖(qA m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    simp [mul_inv_rev, mul_comm]
  rw [hmul]
  have :
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
          ‖(qA m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ 1 * Real.exp (qJ * (1 + r) ^ τ) :=
    mul_le_mul qc7 qd8 (by positivity) (by positivity)
  simpa using this
theorem vcD
    {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
    (qbQ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (qak : τ < (m + 1 : ℝ))
    (qz : 0 ≤ τ) (qaa : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ (m + 1)))
    (qZ : Summable (fun p : qv f (Set.univ : Set ℂ) =>
      ‖qg p‖⁻¹ ^ τ))
    (qa7 : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          qA m f (Set.univ : Set ℂ) z) :
    let qE : ℝ :=
      ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
    let qJ : ℝ := vaS m τ qE
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
      ∀ (qH : Set (qv f (Set.univ : Set ℂ)))
        (qC : qH.Finite),
        qH =
            {p : qv f (Set.univ : Set ℂ) |
              ‖qg p‖ ≤ 4 * R} →
        (let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
         let a : qv f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖qg p‖
         r ∉ small.image a) →
        (let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
         let a : qv f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖qg p‖
         (∑ p ∈ small, (1 : ℝ) * qw.φ (r / a p)) ≤
          qw.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + qJ + 10) * (1 + r) ^ τ) := by
  classical
  intro qE qJ R r qG qc6 q9 qau hrpos qH qC
    q5 q8 qaG u hur
  let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
  let a : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
  let bad : Finset ℝ := small.image a
  have qaF : r ∉ bad := by
    simpa [bad, small, a] using q8
  have qdx :
      f u =
        H u * (u ^ analyticOrderNatAt f 0 *
          qA m f (Set.univ : Set ℂ) u) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
  have qh0 : f u ≠ 0 := by
    have qfP : r ≤ 4 * R := by nlinarith [qau, qG]
    exact vdH (f := f) qaa hnot
      (B := 4 * R) (r := r) hrpos qfP qH qC q5
      (by simpa [small, a] using q8) u hur
  have qce :
      (u ^ analyticOrderNatAt f 0 *
        qA m f (Set.univ : Set ℂ) u) ≠ 0 := by
    intro hden0
    have : f u = 0 := by simpa [hden0] using qdx
    exact qh0 this
  have hHu :
      H u =
        f u / (u ^ analyticOrderNatAt f 0 *
          qA m f (Set.univ : Set ℂ) u) := by
    exact eq_div_of_mul_eq qce (Eq.symm qdx)
  have qlu : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
    simpa [hur] using qa7 u
  have qfQ :
      ‖(u ^ analyticOrderNatAt f 0 *
          qA m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (qJ * (1 + r) ^ τ) := by
    simpa [qE, qJ] using
      (vca
        (f := f) (ρ := ρ) (τ := τ) (m := m)
        qbQ hτ qak qz h_sum qZ
        (R := R) (r := r) qG qc6 q9 qau
        qH qC q5
        (by simpa [small, a] using q8)
        (by simpa [small, a, one_mul] using qaG)
        u hur)
  have :
      ‖H u‖ ≤
        ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            qA m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    have :
        ‖H u‖ =
          ‖f u /
            (u ^ analyticOrderNatAt f 0 *
              qA m f (Set.univ : Set ℂ) u)‖ := by
      simp [hHu]
    simp [div_eq_mul_inv, norm_inv, this]
  have hmul :
      ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            qA m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (qJ * (1 + r) ^ τ) :=
    mul_le_mul qlu qfQ (by positivity) (by positivity)
  have hexp :
      Real.exp (Cf * (1 + r) ^ τ) * Real.exp (qJ * (1 + r) ^ τ)
        = Real.exp ((Cf + qJ) * (1 + r) ^ τ) := by
    simp [Real.exp_add, add_mul, add_comm]
  have : ‖H u‖ ≤ Real.exp ((Cf + qJ) * (1 + r) ^ τ) :=
    (this.trans hmul).trans_eq hexp
  have qh1 :
      Real.exp ((Cf + qJ) * (1 + r) ^ τ) ≤
        Real.exp ((Cf + qJ + 10) * (1 + r) ^ τ) := by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (1 + r) ^ τ := by positivity
    nlinarith
  exact this.trans qh1
theorem vcL {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
  (hρ : 0 ≤ ρ) (qbQ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (qak : τ < (m + 1 : ℝ))
  (qz : 0 ≤ τ) (qaa : Differentiable ℂ f) (qai : Differentiable ℂ H)
  (hnot : ∃ z : ℂ, f z ≠ 0)
  (h_sum : Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (m + 1)))
  (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
  (hfactor : ∀ z : ℂ,
   f z =
    H z * z ^ analyticOrderNatAt f 0 *
     qA m f (Set.univ : Set ℂ) z) :
  ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
 rcases hgrowth with ⟨Cf, qb5, hCf⟩
 have qZ :
   Summable (fun p : qv f (Set.univ : Set ℂ) =>
    ‖qg p‖⁻¹ ^ τ) :=
  vaG (f := f) (ρ := ρ) (τ := τ)
   hρ hτ qaa hnot ⟨Cf, qb5, hCf⟩
 let qE : ℝ := ∑' p : qv f (Set.univ : Set ℂ), ‖qg p‖⁻¹ ^ τ
 have qar : 0 ≤ qE := tsum_nonneg fun _ =>
  Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
 let qJ : ℝ := vaS m τ qE
 have qba : 0 ≤ qJ := by
  simpa [qJ] using vff (m := m) (τ := τ) qar
 have qa7 : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) :=
  Real.vel
   (f := f) (r := fun z : ℂ => 1 + ‖z‖) (C := Cf) (ρ := ρ) (τ := τ)
   qb5.le (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ) hCf
 refine ⟨(Cf + qJ + 10) * (3 : ℝ) ^ τ, by
  have qlv : 0 < (3 : ℝ) ^ τ := by positivity
  nlinarith [qb5, qba, qlv], ?_⟩
 intro z
 let R : ℝ := max ‖z‖ 1
 have qG : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
 have qc6 : (1 : ℝ) ≤ R := le_max_right _ _
 let qH : Set (qv f (Set.univ : Set ℂ)) :=
  {p | ‖qg p‖ ≤ 4 * R}
 have qC : qH.Finite := by
  have : Metric.closedBall (0 : ℂ) (4 * R) ⊆ (Set.univ : Set ℂ) := by simp
  simpa [qH] using
   (vau (f := f) (U := (Set.univ : Set ℂ))
    (B := 4 * R) this)
 let small : Finset (qv f (Set.univ : Set ℂ)) := qC.toFinset
 let a : qv f (Set.univ : Set ℂ) → ℝ := fun p => ‖qg p‖
 have ha_pos : ∀ p ∈ small, 0 < a p := by
  intro p hp
  exact norm_pos_iff.2 (vao p)
 let bad : Finset ℝ := small.image a
 rcases qw.vbQ
   (s := small) (w := fun _ => (1 : ℝ)) (a := a)
   (hw := by intro _ _; norm_num) (ha := ha_pos) (bad := bad) (R := R) qG with
  ⟨r, hr_mem, q8, qaG⟩
 have q9 : R ≤ r := le_of_lt hr_mem.1
 have qau : r ≤ 2 * R := hr_mem.2
 have hrpos : 0 < r := lt_of_lt_of_le qG q9
 have qgS :
   ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + qJ + 10) * (1 + r) ^ τ) := by
  simpa [qE, qJ] using
   (vcD
    (f := f) (H := H) (ρ := ρ) (τ := τ) (m := m) (Cf := Cf)
    qbQ hτ qak qz qaa hnot h_sum qZ qa7 hfactor
    (R := R) (r := r) qG qc6 q9 qau hrpos
    qH qC (by rfl)
    (by simpa [small, a, bad] using q8)
    (by simpa [small, a, one_mul, Finset.sum_const, nsmul_eq_mul] using qaG))
 have qag : z ∈ Metric.ball (0 : ℂ) r := by
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (le_max_left _ _) hr_mem.1
 have hball :
   ‖H z‖ ≤ Real.exp ((Cf + qJ + 10) * (1 + r) ^ τ) := by
  exact Complex.vcF qai hrpos qag qgS
 have qgT : 1 + r ≤ 3 * (1 + ‖z‖) := by
  exact Real.vcA (norm_nonneg z)
   (by simpa [R] using qau)
 have hmain :
   Real.exp ((Cf + qJ + 10) * (1 + r) ^ τ)
    ≤ Real.exp (((Cf + qJ + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := by
  have hnn : 0 ≤ (Cf + qJ + 10) := by nlinarith [le_of_lt qb5, qba]
  exact Real.vdv hnn (by norm_num)
   (by linarith [le_of_lt hrpos]) (by positivity) qz qgT
 simpa [mul_assoc] using hball.trans hmain
theorem veA {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (qaa : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            qA (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : qv f (Set.univ : Set ℂ) =>
        ‖qg p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (vbb (f := f) (ρ := ρ)
        hρ qaa hnot hgrowth)
  rcases vdx (m := m) (f := f) qaa hnot h_sum with
    ⟨H, qai, qdL, hfactor⟩
  rcases Real.vaH hρ with
    ⟨τ, hτ, qak, qz, qbq⟩
  have qam : Nat.floor τ = m := by
    simpa [m] using qbq
  have qfR : τ < (m + 1 : ℝ) := by
    simpa [m] using qak
  have qd9 : τ < ((m + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using qfR
  have qbQ : (m : ℝ) ≤ ρ := by
    have := Nat.floor_le hρ
    simpa [m] using this
  have qbb :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) :=
    vcL (f := f) (H := H) (ρ := ρ) (τ := τ)
      (m := m) hρ qbQ hτ qak qz qaa qai hnot h_sum hgrowth hfactor
  have qcz :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
    exact Real.vdh
      (f := H) (r := fun z : ℂ => 1 + ‖z‖)
      (fun z => by linarith [norm_nonneg z]) qd9 qbb
  rcases vdq (H := H) (n := m + 1)
      qai qdL qcz with
    ⟨P, hPn, hHP⟩
  have qi0 : P.natDegree ≤ m := by
    have hbound :
        ∃ C > 0, ∀ z : ℂ,
          ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
      rcases qbb with ⟨C, hCpos, hC⟩
      exact ⟨C, hCpos, fun z => by simpa [hHP z] using (hC z)⟩
    have := vcW qz P hbound
    simpa [qam] using this
  refine ⟨P, ?_, ?_⟩
  · have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le qi0
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)
end Complex.Hadamard
end
end
section
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators
namespace Complex.Hadamard
def vaQ (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
 ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))
namespace vaQ
theorem differentiable {ρ : ℝ} {f : ℂ → ℂ} (h : vaQ ρ f) :
  Differentiable ℂ f :=
 h.1
theorem exists_bound {ρ ε : ℝ} {f : ℂ → ℂ} (h : vaQ ρ f)
  (hε : 0 < ε) :
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
 h.2 ε hε
theorem ver {ρ τ : ℝ} {f : ℂ → ℂ} (h : vaQ ρ f)
  (hτ : ρ < τ) (qz : 0 ≤ τ) :
  ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
 rcases h.exists_bound (sub_pos.2 hτ) with ⟨C, hCpos, hC⟩
 have hnorm : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
  intro z
  simpa [sub_add_cancel] using (hC z)
 exact Real.vcc (f := f)
  (r := fun z : ℂ => 1 + ‖z‖) hCpos qz
  (fun z => by linarith [norm_nonneg z]) hnorm
theorem vcU {ρ : ℝ} {f : ℂ → ℂ}
  (h : vaQ ρ f) (hρ : 0 ≤ ρ) (hnot : ∃ z : ℂ, f z ≠ 0) :
  Summable (fun p : qv f (Set.univ : Set ℂ) =>
   ‖qg p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
 rcases Real.vaH hρ with
  ⟨τ, hτ, qlD, qz, qam⟩
 have qbr :
   ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
  h.ver hτ qz
 have qeZ :=
  vbb
   (f := f) (ρ := τ) qz h.differentiable hnot qbr
 simpa [qam] using qeZ
end vaQ
theorem veH {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : vaQ ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            qA (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  classical
  let qaa : Differentiable ℂ f := horder.differentiable
  set m : ℕ := Nat.floor ρ
  rcases Real.vaH hρ with
    ⟨τ, hτ, qak, qz, qbq⟩
  have qam : Nat.floor τ = m := by
    simpa [m] using qbq
  have qbr :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    horder.ver hτ qz
  rcases veA (f := f) (ρ := τ) qz
      qaa hnot qbr with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [m, qam] using hdeg
  · intro z
    simpa [m, qam] using hfac z
end Complex.Hadamard
end
end
section
namespace Polynomial
theorem vhR (P : ℂ[X]) (z : ℂ) :
  logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
   Polynomial.eval z P.derivative := by
 have hderiv :
   deriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
    Complex.exp (Polynomial.eval z P) * Polynomial.eval z P.derivative := by
  simpa [Function.comp_def, mul_comm] using
   ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).deriv
 rw [logDeriv_apply, hderiv]
 field_simp [Complex.exp_ne_zero (Polynomial.eval z P)]
end Polynomial
end
section
namespace Erdos985.Analytic.HadamardAux
open Complex.Hadamard
variable {f : ℂ → ℂ}
lemma viv (hf : Differentiable ℂ f) (p : qv f Set.univ) :
  f (qg p) = 0 := by
 have h := vbs p
 rw [vax hf] at h
 exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by exact_mod_cast h)
noncomputable def vjB (hf : Differentiable ℂ f) (p : qv f Set.univ) :
  {ρ : ℂ // f ρ = 0} :=
 ⟨qg p, viv hf p⟩
lemma vgr {E : Type*} [NormedAddCommGroup E]
  (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (g : ℂ → E) {a : E}
  (h : HasSum (fun p : qv f Set.univ => g (qg p)) a) :
  HasSum (fun ρ : {ρ : ℂ // f ρ = 0} => analyticOrderNatAt f ρ • g ρ) a := by
 classical
 set π := vjB hf
 have h' := (Equiv.sigmaFiberEquiv π).hasSum_iff.mpr h
 refine h'.sigma fun ρ => ?_
 have hiff : ∀ p, π p = ρ ↔ p ∈ qO f (ρ : ℂ) := by
  intro p
  rw [vai]
  simp [π, vjB, Subtype.ext_iff]
 let _ : Fintype {p // π p = ρ} :=
  Fintype.subtype (qO f (ρ : ℂ)) (fun p => (hiff p).symm)
 have hρ0 : (ρ : ℂ) ≠ 0 := fun h0 => hf0 (by simpa [h0] using ρ.2)
 have hcard : Fintype.card {p // π p = ρ} = analyticOrderNatAt f ρ := by
  rw [← vaC hf hρ0]
  exact Fintype.card_of_subtype _ (fun p => (hiff p).symm)
 have hc : ∀ c : {p // π p = ρ},
   g (qg ((Equiv.sigmaFiberEquiv π) ⟨ρ, c⟩)) = g ρ := by
  intro c
  have : qg c.1 = ρ := congrArg Subtype.val c.2
  simp [Equiv.sigmaFiberEquiv_apply, this]
 simp only [Function.comp_def, hc]
 rw [← hcard]
 convert hasSum_fintype (fun _ : {p // π p = ρ} => g ρ) using 1
 simp
lemma vgi (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    vaQ 1 f := by
  obtain ⟨C, hC⟩ := hgrowth
  have hCpos : 0 < C := by
    have h0 := hC 0
    simp only [norm_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] at h0
    exact lt_of_lt_of_le (norm_pos_iff.2 hf0) h0
  refine ⟨hf, fun ε hε => ?_⟩
  refine ⟨|Real.log C| + C * (1 + 1 / ε) + 1, by positivity, fun z => ?_⟩
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have h1 : 1 ≤ 1 + r := by linarith
  set Y := (1 + r) ^ ((1 : ℝ) + ε)
  have hA : 1 + r ≤ Y := Real.self_le_rpow_of_one_le h1 (by linarith)
  have hB : 1 ≤ Y := le_trans h1 hA
  have hlog : Real.log (r + 2) ≤ 1 + (1 + r) ^ ε / ε := by
    have h4 : Real.log (r + 2) ≤ Real.log 2 + Real.log (1 + r) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have h3 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 1 + r) hε
    linarith
  have hmul : (1 + r) * (1 + r) ^ ε = Y := by
    simp only [Y]
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have e1 : Real.log C ≤ |Real.log C| * Y :=
    le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hB)
  have e2 : C * r * Real.log (r + 2) ≤ C * (1 + 1 / ε) * Y := by
    calc C * r * Real.log (r + 2) ≤ C * (1 + r) * (1 + (1 + r) ^ ε / ε) := by
          gcongr
          · exact Real.log_nonneg (by linarith)
          · linarith
      _ = C * ((1 + r) + ((1 + r) * (1 + r) ^ ε) / ε) := by ring
      _ = C * ((1 + r) + Y / ε) := by rw [hmul]
      _ ≤ C * (Y + Y / ε) := by gcongr
      _ = C * (1 + 1 / ε) * Y := by ring
  calc ‖f z‖ ≤ C * Real.exp (C * r * Real.log (r + 2)) := hC z
    _ = Real.exp (Real.log C + C * r * Real.log (r + 2)) := by
      rw [Real.exp_add, Real.exp_log hCpos]
    _ ≤ Real.exp ((|Real.log C| + C * (1 + 1 / ε) + 1) * Y) := by
      gcongr
      have : (|Real.log C| + C * (1 + 1 / ε) + 1) * Y
          = |Real.log C| * Y + C * (1 + 1 / ε) * Y + Y := by ring
      rw [this]
      linarith
end Erdos985.Analytic.HadamardAux
end
section
namespace Erdos985.Analytic
open Complex.Hadamard HadamardAux
theorem vej {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv f z / f z = b + ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  have hord := vgi hf hf0 hgrowth
  have hnot : ∃ z, f z ≠ 0 := ⟨0, hf0⟩
  have hsum2 : Summable (fun p : qv f Set.univ =>
      ‖qg p‖⁻¹ ^ (2 : ℕ)) := by
    simpa [Nat.floor_one] using hord.vcU (by norm_num) hnot
  constructor
  · intro ε hε
    obtain ⟨C', hC', hlog⟩ :=
      hord.ver (τ := 1 + ε / 2) (by linarith) (by linarith)
    have hs := vaG (τ := 1 + ε)
      (by linarith) (by linarith) hf hnot ⟨C', hC', hlog⟩
    have hW := vgr hf hf0 (fun x : ℂ => ‖x‖⁻¹ ^ (1 + ε)) hs.hasSum
    refine hW.summable.congr fun ρ => ?_
    simp [nsmul_eq_mul, Real.inv_rpow (norm_nonneg _), div_eq_mul_inv]
  · obtain ⟨P, hdeg, hfac⟩ :=
      veH (by norm_num : (0 : ℝ) ≤ 1) hnot hord
    refine ⟨P.coeff 1, fun z hz => ?_⟩
    have hz' : ∀ p : qv f Set.univ, z ≠ qg p :=
      fun p h => hz (h ▸ viv hf p)
    have hS := vaM hsum2 hz'
    have hW := vgr hf hf0 (fun x : ℂ => 1 / (z - x) + 1 / x) hS.hasSum
    simp only [nsmul_eq_mul] at hW
    refine ⟨hW.summable, ?_⟩
    rw [hW.tsum_eq]
    have h0 : analyticOrderNatAt f 0 = 0 := by
      by_contra h
      exact hf0 (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
    set G : ℂ → ℂ := qA 1 f Set.univ with hG
    have hfun : f = fun w => Complex.exp (Polynomial.eval w P) * G w := by
      funext w
      simpa [h0, G, Nat.floor_one] using hfac w
    have qe0 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z :=
      (P.differentiable.differentiableAt (x := z)).cexp
    have hG0 : G z ≠ 0 := vbp 1 f hsum2 hz'
    have hGd : DifferentiableAt ℂ G z := vcC 1 f hsum2 z
    have hP1 : Polynomial.eval z P.derivative = P.coeff 1 := by
      have hdeg' : P.degree ≤ 1 := by simpa [Nat.floor_one] using hdeg
      rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg']
      simp
    have hL : logDeriv f z = logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w) z := by
      conv_lhs => rw [hfun]
    rw [← logDeriv_apply, hL, logDeriv_mul (f := fun w : ℂ => Complex.exp (Polynomial.eval w P)) (g := G) z
        (Complex.exp_ne_zero _) hG0 qe0 hGd,
      Polynomial.vhR, hP1,
      vbE hsum2 hz']
end Erdos985.Analytic
end
section
open Complex MeasureTheory Set
namespace Erdos985.Analytic.PerronKernel
noncomputable def cesaro (t : ℝ) : ℂ := ((max 0 (1 - t) : ℝ) : ℂ)
lemma vhV : Continuous cesaro := by
 unfold cesaro; fun_prop
lemma vfH {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    cesaro t = indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      - indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  unfold cesaro
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    rw [indicator_of_mem hm, indicator_of_mem hm, cpow_one, max_eq_right (by linarith)]
    push_cast; ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    rw [indicator_of_notMem hm, indicator_of_notMem hm, max_eq_left (by linarith)]
    simp
lemma vfR {s : ℂ} (hs : 0 < s.re) : HasMellin cesaro s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have h := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hval : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by field_simp; ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [vfH ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [vfH ht]
lemma denom_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) :
  ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) ≠ 0 := by
 have h0 : ((c : ℂ) + t * I) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith
 have h1 : ((c : ℂ) + t * I + 1) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith
 exact mul_ne_zero h0 h1
lemma vjn (c : ℝ) (hc : 0 < c) (t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ := by
  have hs : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hs1 : ‖(c : ℂ) + t * I‖ ^ 2 ≤ ‖(c : ℂ) + t * I + 1‖ ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith
  have hn1 : ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hs1
  rw [norm_mul]
  calc min (c ^ 2) 1 * (1 + t ^ 2) ≤ c ^ 2 + t ^ 2 := by
        rcases le_total (c ^ 2) 1 with h | h
        · rw [min_eq_left h]; nlinarith [sq_nonneg t]
        · rw [min_eq_right h]; linarith
    _ = ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I‖ := by rw [← hs]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
lemma vgZ (c : ℝ) (hc : 0 < c) :
  Continuous fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
 by
 have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) := by
  have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
   continuous_const.add (continuous_ofReal.mul continuous_const)
  exact h0.mul (h0.add continuous_const)
 exact Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (denom_ne_zero c hc)
lemma vdj (c : ℝ) (hc : 0 < c) :
    Integrable fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (min (c ^ 2) 1)⁻¹)
    (vgZ c hc).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_div, norm_one]
  have h := vjn c hc t
  have hpos : 0 < min (c ^ 2) 1 * (1 + t ^ 2) := by positivity
  calc 1 / ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ ≤ 1 / (min (c ^ 2) 1 * (1 + t ^ 2)) :=
        one_div_le_one_div_of_le hpos h
    _ = (min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by rw [one_div, mul_inv]
theorem vfv (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
   (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
   = (max 0 (1 - 1 / y) : ℝ) := by
 have hmel : ∀ t : ℝ, mellin cesaro ((c : ℂ) + t * I)
   = 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
  (vfR (s := (c : ℂ) + t * I) (by simpa using hc)).2
 have hconv : MellinConvergent cesaro (c : ℂ) := (vfR (by simpa using hc)).1
 have hvert : VerticalIntegrable (mellin cesaro) c := by
  unfold VerticalIntegrable
  simp_rw [hmel]
  exact vdj c hc
 have hinv := mellinInv_mellin_eq (E := ℂ) c cesaro (x := 1 / y) (by positivity) hconv hvert
  vhV.continuousAt
 have hint : (∫ t : ℝ,
   (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
   = ∫ t : ℝ, (((1 / y : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin cesaro ((c : ℂ) + t * I) := by
  congr 1
  funext t
  rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (y : ℂ),
   inv_cpow_ofReal_nonneg hy.le, cpow_neg, inv_inv]
  ring
 rw [hint]
 unfold mellinInv at hinv
 rw [Complex.real_smul] at hinv
 have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
 rw [h2] at hinv
 exact hinv
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter
namespace Erdos985.Analytic.PerronKernel
theorem vhm (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 2 * Real.pi * (if 1 ≤ y then 1 - 1 / y else 0) := by
  have h := vfv y c hy hc
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.2 this.ne')
  have h' : (∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = 2 * Real.pi * ((max 0 (1 - 1 / y) : ℝ) : ℂ) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rw [h']
  congr 1
  split_ifs with h1
  · rw [max_eq_right (by rw [sub_nonneg, div_le_one hy]; exact h1)]
  · rw [max_eq_left (by
      rw [sub_nonpos, le_div_iff₀ hy]; linarith)]
noncomputable def K (c y t : ℝ) : ℂ :=
 (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
lemma vkn (c y t : ℝ) (hy : 0 < y) :
  ‖K c y t‖ = y ^ c * ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
 unfold K
 rw [div_eq_mul_one_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
 simp
lemma vhJ (c y : ℝ) (hc : 0 < c) (hy : 0 < y) : Integrable (K c y) := by
 have hcont : Continuous (K c y) := by
  unfold K
  have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
   continuous_const.add (continuous_ofReal.mul continuous_const)
  have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
   h0.mul (h0.add continuous_const)
  exact (h0.const_cpow (Or.inl (ofReal_ne_zero.2 hy.ne'))).div h1 (denom_ne_zero c hc)
 refine Integrable.mono' ((vdj c hc).norm.const_mul (y ^ c))
  hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
 rw [vkn c y t hy]
lemma viw (c y : ℝ) (hy : 0 < y) :
  ∫ t : ℝ, ‖K c y t‖ = y ^ c * ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
 simp_rw [vkn c y _ hy]
 rw [integral_const_mul]
lemma vjI (a : ℕ → ℂ) (c t : ℝ) (N n : ℕ) (hN : 1 ≤ N) :
    LSeries.term a ((c : ℂ) + t * I) n * ((N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = if n = 0 then 0 else a n * K c ((N : ℝ) / n) t := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · unfold K
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hnc : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
      rw [cpow_ne_zero_iff]; left; exact_mod_cast hn
    rw [ofReal_div, div_eq_mul_inv ((N : ℝ) : ℂ), ← ofReal_inv, mul_cpow_ofReal_nonneg
      (by positivity) (by positivity), ofReal_inv, inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast,
      ofReal_natCast]
    field_simp
theorem viM (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * (1 - (n : ℂ) / N)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
          / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  set C := ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hN0 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  let G : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * K c ((N : ℝ) / n) t
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]; exact (vhJ c _ hc (hpos n hn)).const_mul _
  have hG_norm : ∀ n, ∫ t, ‖G n t‖ = if n = 0 then 0 else ‖a n‖ * (((N : ℝ) / n) ^ c * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul, viw c _ (hpos n hn)]
  have hsum : Summable fun n => ∫ t, ‖G n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (ha.mul_left ((N : ℝ) ^ c * C))
    rw [hG_norm]
    split_ifs with hn
    · have : 0 ≤ ‖a n‖ / (n : ℝ) ^ c := div_nonneg (norm_nonneg _) (by positivity)
      positivity
    · rw [Real.div_rpow hN0.le (Nat.cast_nonneg n)]
      apply le_of_eq
      ring
  have hfun : (fun t : ℝ => LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) = fun t => ∑' n, G n t := by
    funext t
    rw [mul_div_assoc, LSeries, ← tsum_mul_right]
    congr 1
    funext n
    exact vjI a c t N n hN
  have hGint : ∀ n, ∫ t, G n t = if n = 0 then 0 else
      a n * (2 * Real.pi * ((if 1 ≤ (N : ℝ) / n then 1 - 1 / ((N : ℝ) / n) else 0 : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      unfold K
      rw [vhm _ c (hpos n hn) hc]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.Ioo 0 N), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioo] at hn
    have hn0 : n ≠ 0 := by omega
    have hle : 1 ≤ (N : ℝ) / n := by
      rw [one_le_div (Nat.cast_pos.2 (by omega))]; exact_mod_cast hn.2.le
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    field_simp
  · intro n hn
    rw [Finset.mem_Ioo] at hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      have hnN : N ≤ n := by omega
      rcases eq_or_lt_of_le hnN with h | h
      · subst h
        have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp [div_self (show (N : ℝ) ≠ 0 by exact_mod_cast hn0)]
      · have hlt : ¬ 1 ≤ (N : ℝ) / n := by
          rw [not_le, div_lt_one (Nat.cast_pos.2 (by omega))]; exact_mod_cast h
        simp [hlt]
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronKernel
noncomputable def veF (w : ℂ) (t : ℝ) : ℂ :=
 (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)
noncomputable def vdk (w : ℂ) (t : ℝ) : ℂ := if t ≤ 1 then veF w t else 0
lemma vjQ (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : veF w 1 = 0 := by
 have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
 have h2 : 1 + w ≠ 0 := by rwa [add_comm]
 unfold veF
 simp only [ofReal_one, one_cpow]
 field_simp
 ring
lemma vfP (w : ℂ) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    vdk w t = (1 / (w * (w + 1))) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-w) : ℝ → ℂ) t
      - (1 / w) • indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      + (1 / (1 + w)) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  unfold vdk veF
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    simp only [h1, ↓reduceIte]
    rw [indicator_of_mem hm, indicator_of_mem hm, indicator_of_mem hm, cpow_one]
    simp only [smul_eq_mul]
    ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    simp only [h1, ↓reduceIte]
    rw [indicator_of_notMem hm, indicator_of_notMem hm, indicator_of_notMem hm]
    simp
lemma vfK {s w : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) (hw0 : w ≠ 0)
    (hw1 : w ≠ -1) : HasMellin (vdk w) s (1 / ((s - w) * s * (s + 1))) := by
  have hA := hasMellin_cpow_Ioc (-w) (s := s) (by simp; linarith)
  have hB := hasMellin_one_Ioc hs
  have hC := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have hA' := hasMellin_const_smul hA.1 (1 / (w * (w + 1)))
  have hB' := hasMellin_const_smul hB.1 (1 / w)
  have hC' := hasMellin_const_smul hC.1 (1 / (1 + w))
  have hAB := hasMellin_sub hA'.1 hB'.1
  have h := hasMellin_add hAB.1 hC'.1
  rw [hAB.2, hA'.2, hB'.2, hC'.2, hA.2, hB.2, hC.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0 : s - w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0' : s + -w ≠ 0 := by rwa [← sub_eq_add_neg]
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  have hval : (1 / (w * (w + 1))) • (1 / (s + -w)) - (1 / w) • (1 / s)
      + (1 / (1 + w)) • (1 / (s + 1)) = 1 / ((s - w) * s * (s + 1)) := by
    simp only [smul_eq_mul, ← sub_eq_add_neg]
    field_simp
    ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [vfP w ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [vfP w ht]
lemma vhq (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
  ContinuousAt (vdk w) x₀ := by
 set a := min (x₀ / 2) (1 / 2) with ha
 have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
 have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
 have hax : a < x₀ := (min_le_left _ _).trans_lt (by linarith)
 let g : ℝ → ℂ := fun t => if t ≤ 1 then veF w (max t a) else 0
 have hE : Continuous fun t : ℝ => veF w (max t a) := by
  have hm : Continuous fun t : ℝ => max t a := continuous_id.max continuous_const
  have hpow : Continuous fun t : ℝ => ((max t a : ℝ) : ℂ) ^ (-w) := by
   refine continuous_iff_continuousAt.2 fun t => ?_
   refine ContinuousAt.cpow (continuous_ofReal.comp hm).continuousAt continuousAt_const ?_
   exact ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha0 (le_max_right _ _))
  unfold veF
  exact ((hpow.div_const _).sub continuous_const).add
   ((continuous_ofReal.comp hm).div_const _)
 have hg : Continuous g := by
  refine continuous_if_le continuous_id continuous_const hE.continuousOn
   continuous_const.continuousOn (fun t ht => ?_)
  rw [ht, max_eq_left ha1]
  exact vjQ w hw0 hw1
 have hev : g =ᶠ[𝓝 x₀] vdk w := by
  filter_upwards [Ioi_mem_nhds hax] with t ht
  simp only [g, vdk, max_eq_left (le_of_lt (mem_Ioi.1 ht))]
 exact hg.continuousAt.congr hev
lemma vfE (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
  Integrable fun t : ℝ =>
   1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
 have hδ : 0 < c - w.re := by linarith
 have hne : ∀ t : ℝ, ((c : ℂ) + t * I - w) ≠ 0 := by
  intro t h; have := congrArg Complex.re h; simp at this; linarith
 have hcont : Continuous fun t : ℝ =>
   1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
   continuous_const.add (continuous_ofReal.mul continuous_const)
  have h1 : Continuous fun t : ℝ =>
    ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
   ((h0.sub continuous_const).mul h0).mul (h0.add continuous_const)
  refine Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (fun t => ?_)
  rw [mul_assoc]
  exact mul_ne_zero (hne t) (denom_ne_zero c hc t)
 refine Integrable.mono' ((vdj c hc).norm.const_mul (c - w.re)⁻¹)
  hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
 have hge : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := re_le_norm ((c : ℂ) + t * I - w); simpa using this
 rw [mul_assoc, norm_div, norm_div, norm_one, norm_mul]
 rw [← one_div_mul_one_div, ← one_div (c - w.re)]
 exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hδ hge)
  (one_div_nonneg.2 (norm_nonneg _))
theorem vhy (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
  (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
   (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
   = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) := by
 have hx0 : 0 < x := by linarith
 have hmel : ∀ t : ℝ, mellin (vdk w) ((c : ℂ) + t * I)
   = 1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
  (vfK (s := (c : ℂ) + t * I) (by simpa using hc) (by simpa using hw) hw0 hw1).2
 have hconv : MellinConvergent (vdk w) (c : ℂ) :=
  (vfK (by simpa using hc) (by simpa using hw) hw0 hw1).1
 have hvert : VerticalIntegrable (mellin (vdk w)) c := by
  unfold VerticalIntegrable
  simp_rw [hmel]
  exact vfE c hc w hw
 have hinv := mellinInv_mellin_eq (E := ℂ) c (vdk w) (x := 1 / x) (by positivity) hconv hvert
  (vhq w hw0 hw1 (by positivity))
 have hint : (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
   = ∫ t : ℝ, (((1 / x : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (vdk w) ((c : ℂ) + t * I) := by
  congr 1
  funext t
  rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (x : ℂ),
   inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv]
  ring
 rw [hint]
 unfold mellinInv at hinv
 rw [Complex.real_smul] at hinv
 have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
 rw [h2] at hinv
 rw [hinv]
 have hle : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
 unfold vdk veF
 simp only [hle, ↓reduceIte]
 rw [ofReal_div, ofReal_one, one_div (x : ℂ), inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv,
  cpow_neg_one]
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronAux
lemma vhx {y : ℝ} (hy : 0 < y) (s : ℂ) :
  ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
 rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
  cpow_neg, inv_inv]
theorem viq {f : ℝ → ℂ} {F : ℂ → ℂ} {y c : ℝ} (hy : 0 < y)
  (hf : MellinConvergent f c) (hF : ∀ t : ℝ, mellin f (c + t * I) = F (c + t * I))
  (hFi : Integrable fun t : ℝ => F (c + t * I)) (hfc : ContinuousAt f y⁻¹) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
   = f y⁻¹ := by
 have hV : VerticalIntegrable (mellin f) c := by
  unfold VerticalIntegrable
  simp_rw [hF]; exact hFi
 have := mellinInv_mellin_eq c f (inv_pos.2 hy) hf hV hfc
 rw [← this, mellinInv]
 simp_rw [hF, vhx hy, smul_eq_mul]
 rw [Complex.real_smul]
 push_cast; ring
lemma vfs {h : ℝ → ℂ} {t : ℝ} (ht : 0 < t) (hh : ContinuousAt h t)
    (h1 : t = 1 → h 1 = 0) : ContinuousAt (indicator (Ioc 0 1) h) t := by
  rcases lt_trichotomy t 1 with h' | rfl | h'
  · refine hh.congr ?_
    filter_upwards [Ioo_mem_nhds ht h'] with u hu
    rw [indicator_of_mem (show u ∈ Ioc (0:ℝ) 1 from ⟨hu.1, hu.2.le⟩)]
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · refine (hh.continuousWithinAt).congr_of_eventuallyEq ?_ (by simp)
      filter_upwards [Ioc_mem_nhdsLE (show (0:ℝ) < 1 by norm_num)] with u hu
      rw [indicator_of_mem hu]
    · have : ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Ici 1) 1 := continuousWithinAt_const
      refine this.congr_of_eventuallyEq ?_ (by simp [h1 rfl])
      filter_upwards [self_mem_nhdsWithin] with u hu
      rcases eq_or_lt_of_le (show (1:ℝ) ≤ u from hu) with rfl | hu'
      · simp [h1 rfl]
      · rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 hu'))]
  · refine continuousAt_const.congr (f := fun _ => (0:ℂ)) ?_
    filter_upwards [Ioi_mem_nhds h'] with u hu
    rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 (show 1 < u from hu)))]
noncomputable def P (a : ℂ) : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)
lemma ves (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) : HasMellin (P a) s (1 / (s + a)) :=
 hasMellin_cpow_Ioc a hs
lemma viA (α β γ a b d : ℂ) {s : ℂ} (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re)
  (hd : 0 < s.re + d.re) :
  HasMellin (indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
   γ * (t : ℂ) ^ d)) s (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d))) := by
 have e : indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
   γ * (t : ℂ) ^ d) = fun t => (α • P a t + β • P b t) + γ • P d t := by
  funext t
  by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [P, ht]
 rw [e]
 have h1 := ves a ha
 have h2 := ves b hb
 have h3 := ves d hd
 have k1 := hasMellin_const_smul h1.1 α
 have k2 := hasMellin_const_smul h2.1 β
 have k3 := hasMellin_const_smul h3.1 γ
 have k12 := hasMellin_add k1.1 k2.1
 have k := hasMellin_add k12.1 k3.1
 refine ⟨k.1, ?_⟩
 rw [k.2, k12.2, k1.2, k2.2, k3.2, h1.2, h2.2, h3.2]
 simp [smul_eq_mul]
lemma vjb (a : ℂ) (ha : -1 < a.re) : IntegrableOn (P a) (Ioi 0) := by
 have := (ves a (s := 1) (by simp; linarith)).1
 unfold MellinConvergent at this
 refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
 simp
lemma viK (a : ℂ) {s : ℂ} (ha : -1 < a.re) (hs : 0 < s.re + a.re) :
    HasMellin (fun t : ℝ => (Real.log t : ℂ) * P a t) s (-1 / (s + a) ^ 2) := by
  have hloc : LocallyIntegrableOn (P a) (Ioi 0) := (vjb a ha).locallyIntegrableOn
  have htop : P a =O[atTop] (· ^ (-(s.re + 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [P, indicator_of_notMem (fun hm : t ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 ht))]
  have hbot : P a =O[𝓝[>] 0] (· ^ (-(-a.re))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    rw [P, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      norm_cpow_eq_rpow_re_of_pos ht.1, neg_neg, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hloc htop (by linarith) hbot
    (by linarith)
  have hne : s + a ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hev : mellin (P a) =ᶠ[𝓝 s] fun z => (z + a)⁻¹ := by
    have hopen : IsOpen {z : ℂ | 0 < z.re + a.re} :=
      isOpen_lt continuous_const (continuous_re.add continuous_const)
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [(ves a hz).2, one_div]
  have h2 : HasDerivAt (fun z => (z + a)⁻¹) (-1 / (s + a) ^ 2) s := by
    have := ((hasDerivAt_id s).add_const a).inv hne
    simp only [id] at this
    convert this using 1
    all_goals try with_reducible_and_instances rfl
  have h3 := (h2.congr_of_eventuallyEq hev).unique hder
  refine ⟨?_, ?_⟩
  · refine (hconv).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.real_smul]
  · rw [h3]; unfold mellin; congr 1
noncomputable def prof (κ a₀ α β γ a b d : ℂ) : ℝ → ℂ :=
 indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) +
  (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))
lemma vgU (κ a₀ α β γ a b d : ℂ) {s : ℂ} (ha₀ : -1 < a₀.re) (ha₀' : 0 < s.re + a₀.re)
  (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re) (hd : 0 < s.re + d.re) :
  HasMellin (prof κ a₀ α β γ a b d) s (κ * (-1 / (s + a₀) ^ 2) +
   (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d)))) := by
 have e : prof κ a₀ α β γ a b d = fun t => κ • ((Real.log t : ℂ) * P a₀ t) +
   indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
   γ * (t : ℂ) ^ d) t := by
  funext t
  by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [prof, P, ht]
 rw [e]
 have h1 := viK a₀ ha₀ ha₀'
 have k1 := hasMellin_const_smul h1.1 κ
 have h2 := viA α β γ a b d ha hb hd
 have k := hasMellin_add k1.1 h2.1
 refine ⟨k.1, ?_⟩
 rw [k.2, k1.2, h1.2, h2.2, smul_eq_mul]
lemma vhQ (κ a₀ α β γ a b d : ℂ) {t : ℝ} (ht : 0 < t)
  (h1 : t = 1 → α + β + γ = 0) : ContinuousAt (prof κ a₀ α β γ a b d) t := by
 refine vfs ht ?_ (fun h => by simp [h1 h])
 have hc : ∀ e : ℂ, ContinuousAt (fun u : ℝ => (u : ℂ) ^ e) t :=
  fun e => continuousAt_ofReal_cpow_const t e (Or.inr ht.ne')
 have hl : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t :=
  continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht.ne')
 exact (continuousAt_const.mul (hl.mul (hc a₀))).add
  (((continuousAt_const.mul (hc a)).add (continuousAt_const.mul (hc b))).add
   (continuousAt_const.mul (hc d)))
theorem vih {y c : ℝ} (hy : 0 < y) (κ a₀ α β γ a b d : ℂ)
    (ha₀ : -1 < a₀.re) (ha₀' : 0 < c + a₀.re) (ha : 0 < c + a.re) (hb : 0 < c + b.re)
    (hd : 0 < c + d.re) (h1 : y⁻¹ = 1 → α + β + γ = 0) {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, κ * (-1 / ((c : ℂ) + t * I + a₀) ^ 2) +
      (α * (1 / ((c : ℂ) + t * I + a)) + β * (1 / ((c : ℂ) + t * I + b)) +
        γ * (1 / ((c : ℂ) + t * I + d))) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = prof κ a₀ α β γ a b d y⁻¹ := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  refine viq hy ?_ ?_ hFi (vhQ _ _ _ _ _ _ _ _ (inv_pos.2 hy) h1)
  · exact (vgU κ a₀ α β γ a b d (s := (c : ℂ)) ha₀ (by simpa using ha₀')
      (by simpa using ha) (by simpa using hb) (by simpa using hd)).1
  · intro t
    rw [(vgU κ a₀ α β γ a b d (s := (c : ℂ) + t * I) ha₀ (by rw [hre]; exact ha₀')
      (by rw [hre]; exact ha) (by rw [hre]; exact hb) (by rw [hre]; exact hd)).2, hF]
end Erdos985.Analytic.PerronAux
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronAux
lemma vfT (c t : ℝ) : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
 rw [Complex.sq_norm, normSq_add_mul_I]
lemma vfO (c t : ℝ) : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
 push_cast; ring
lemma vho (c t : ℝ) : |t| ≤ ‖(c : ℂ) + t * I‖ := by
 simpa using abs_im_le_norm ((c : ℂ) + t * I)
lemma vgD (c t : ℝ) (w : ℂ) : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
 have := re_le_norm ((c : ℂ) + t * I - w)
 simpa using this
lemma vgu (c t : ℝ) (w : ℂ) : |t - w.im| ≤ ‖(c : ℂ) + t * I - w‖ := by
 have := abs_im_le_norm ((c : ℂ) + t * I - w)
 simpa using this
lemma vjc {c : ℝ} (_hc : 0 ≤ c) (t : ℝ) : c ≤ ‖(c : ℂ) + t * I‖ := by
 have := re_le_norm ((c : ℂ) + t * I)
 simpa using this
lemma vhd {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
  ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ := by
 rw [vfO]
 have h1 := vfT c t
 have h2 := vfT (c + 1) t
 have := norm_nonneg ((c : ℂ) + t * I)
 have := norm_nonneg (((c + 1 : ℝ) : ℂ) + t * I)
 nlinarith
lemma vdO {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 1 ≤ ‖(c : ℂ) + t * I + 1‖ := by
 rw [vfO]; have := vjc (c := c + 1) (by linarith) t; linarith
lemma vfY (c t : ℝ) :
  min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ ^ 2 := by
 rw [vfT]
 have h1 : min (c ^ 2) 1 ≤ c ^ 2 := min_le_left _ _
 have h2 : min (c ^ 2) 1 ≤ 1 := min_le_right _ _
 nlinarith [sq_nonneg t]
lemma veQ {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
 intro h; have := congrArg re h; simp at this; linarith
lemma vbi {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I + 1 ≠ 0 := by
 intro h; have := congrArg re h; simp at this; linarith
lemma veC {c : ℝ} (t : ℝ) {w : ℂ} (hw : w.re < c) : (c : ℂ) + t * I - w ≠ 0 := by
 intro h; have := congrArg re h; simp at this; linarith
lemma veg {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) :
    Integrable fun t : ℝ => G t / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (integrable_inv_one_add_sq.const_mul (B / min (c ^ 2) 1)).mono' ?_ (ae_of_all _ ?_)
  · refine (hG.div (by fun_prop) fun t => ?_).aestronglyMeasurable
    exact mul_ne_zero (veQ hc t) (vbi hc t)
  · intro t
    rw [norm_div, norm_mul]
    have hs := vfY c t
    have h1 := vhd hc.le t
    have hpos : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.2 (veQ hc t)
    have hpos1 : 0 < ‖(c : ℂ) + t * I + 1‖ := norm_pos_iff.2 (vbi hc t)
    have key : min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc ‖G t‖ ≤ B := hB t
      _ = B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ * (min (c ^ 2) 1 * (1 + t ^ 2)) := by
          field_simp
      _ ≤ B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ *
          (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) := by
          gcongr
lemma vce {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
  (hB : ∀ t, ‖G t‖ ≤ B) {w : ℂ} (hw : w.re < c) :
  Integrable fun t : ℝ =>
   G t / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
 have hδ : 0 < c - w.re := by linarith
 have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
 have hG' : Continuous fun t : ℝ => G t / ((c : ℂ) + t * I - w) :=
  hG.div (by fun_prop) fun t => veC t hw
 have := veg hc hG' (B := B / (c - w.re)) fun t => by
  rw [norm_div]
  exact div_le_div₀ hB0 (hB t) hδ (vgD c t w)
 refine this.congr (ae_of_all _ fun t => ?_)
 simp only
 rw [div_div, mul_assoc]
lemma vfa {x : ℝ} (hx : 0 < x) (c t : ℝ) :
  ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
 rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
lemma vdd {x : ℝ} (hx : 0 < x) (c : ℝ) :
  Continuous fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) :=
 Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.2 hx.ne'))
lemma vcr {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {w : ℂ} (hw : w.re < c) :
  Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
 vce hc (vdd hx c) (B := x ^ c)
  (fun t => (vfa hx c t).le) hw
lemma vdP {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
  Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
 veg hc (vdd hx c) (B := x ^ c)
  (fun t => (vfa hx c t).le)
lemma vhv {a b D θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hab : D ≤ a + b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 / (a * b) ≤ (D / 2) ^ (-θ) * (a ^ (-(2 - θ)) + b ^ (-(2 - θ))) := by
  have key : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → D ≤ a + b →
      1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
    intro a b ha hb hle hab
    have hb2 : D / 2 ≤ b := by linarith
    have h1 : b ^ (-θ) ≤ (D / 2) ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb2 (by linarith)
    have hp : (0 : ℝ) ≤ 1 - θ := by linarith
    have hap : a ^ (1 - θ) ≤ b ^ (1 - θ) := Real.rpow_le_rpow ha.le hle hp
    have hA : a ^ (-(2 - θ)) = (a * a ^ (1 - θ))⁻¹ := by
      rw [Real.rpow_neg ha.le, show 2 - θ = 1 + (1 - θ) by ring, Real.rpow_add ha, Real.rpow_one]
    have hB : b ^ (-θ) = b ^ (1 - θ) / b := by
      rw [Real.rpow_neg hb.le, show θ = 1 - (1 - θ) by ring, Real.rpow_sub hb, Real.rpow_one]
      field_simp
      rw [show 1 - (1 - (1 - θ)) = 1 - θ by ring]
    have hapos : 0 < a ^ (1 - θ) := Real.rpow_pos_of_pos ha _
    have hbpos : 0 < b ^ (1 - θ) := Real.rpow_pos_of_pos hb _
    calc 1 / (a * b) ≤ b ^ (-θ) * a ^ (-(2 - θ)) := by
          rw [hA, hB, div_le_iff₀ (by positivity)]
          field_simp
          exact hap
      _ ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
          gcongr
  have hA0 : 0 ≤ a ^ (-(2 - θ)) := Real.rpow_nonneg ha.le _
  have hB0 : 0 ≤ b ^ (-(2 - θ)) := Real.rpow_nonneg hb.le _
  have hD0 : 0 ≤ (D / 2) ^ (-θ) := Real.rpow_nonneg (by positivity) _
  rcases le_total a b with h | h
  · calc 1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := key a b ha hb h hab
      _ ≤ _ := by gcongr; linarith
  · calc 1 / (a * b) = 1 / (b * a) := by rw [mul_comm]
      _ ≤ (D / 2) ^ (-θ) * b ^ (-(2 - θ)) := key b a hb ha h (by linarith)
      _ ≤ _ := by gcongr; linarith
lemma vjH {c δ : ℝ} (t : ℝ) {w : ℂ} (hw : w.re ≤ c - δ) :
  min δ 1 / 2 * (1 + |t - w.im|) ≤ ‖(c : ℂ) + t * I - w‖ := by
 have h1 := vgD c t w
 have h2 := vgu c t w
 have h3 : min δ 1 ≤ δ := min_le_left _ _
 have h4 : min δ 1 ≤ 1 := min_le_right _ _
 have h5 := abs_nonneg (t - w.im)
 nlinarith
lemma viH {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
  1 / 2 * (1 + |t|) ≤ ‖(c : ℂ) + t * I + 1‖ := by
 have h1 := vdO hc t
 have h2 : |t| ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [vfO]; exact vho _ t
 linarith
lemma vbo {r : ℝ} (hr : 1 < r) (v : ℝ) :
  Integrable fun t : ℝ => (1 + |t - v|) ^ (-r) := by
 have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
 simpa [Real.norm_eq_abs] using h.comp_sub_right v
lemma vdC (r v : ℝ) :
  ∫ t : ℝ, (1 + |t - v|) ^ (-r) = ∫ t : ℝ, (1 + |t|) ^ (-r) :=
 integral_sub_right_eq_self (fun t : ℝ => (1 + |t|) ^ (-r)) v
theorem vfk {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) := by
  set r : ℝ := 2 - θ with hr_def
  have hr : 1 < r := by rw [hr_def]; linarith
  set m : ℝ := min δ 1 / 2 with hm_def
  have hm : 0 < m := by rw [hm_def]; exact half_pos (lt_min hδ one_pos)
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  set A : ℝ := m ^ (-r) + (1 / 2 : ℝ) ^ (-r) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(6⁻¹ : ℝ) ^ (-θ) * A * J, by positivity, ?_⟩
  intro x c hx hc w hw
  have hwc : w.re < c := by linarith
  set D : ℝ := max 1 ‖w + 1‖ with hD_def
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  set C : ℝ := x ^ c * (D / 2) ^ (-θ) with hC
  have hC0 : 0 ≤ C := by positivity
  set h : ℝ → ℝ := fun t => C * (m ^ (-r) * (1 + |t - w.im|) ^ (-r) +
    (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r)) with hh
  have hint : Integrable h :=
    (((vbo hr w.im).const_mul _).add
      ((vbo hr 0).const_mul _)).const_mul _
  have hpt : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ ≤ h t := by
    intro t
    set a := ‖(c : ℂ) + t * I - w‖
    set b := ‖(c : ℂ) + t * I + 1‖
    have ha : 0 < a := norm_pos_iff.2 (veC t hwc)
    have hb : 0 < b := norm_pos_iff.2 (vbi hc t)
    have hDab : D ≤ a + b := by
      refine max_le (by have := vdO hc.le t; linarith) ?_
      have : w + 1 = ((c : ℂ) + t * I + 1) - ((c : ℂ) + t * I - w) := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have hab := vhv ha hb hD hDab hθ0 hθ1.le
    have hal : a ^ (-r) ≤ m ^ (-r) * (1 + |t - w.im|) ^ (-r) := by
      rw [← Real.mul_rpow hm.le (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (vjH t hw) (by linarith)
    have hbl : b ^ (-r) ≤ (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity), sub_zero]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (viH hc.le t) (by linarith)
    rw [norm_div, vfa hx, norm_mul, div_eq_mul_one_div]
    simp only [hh, hC]
    rw [mul_assoc]
    gcongr
    refine hab.trans ?_
    rw [hr_def] at hal hbl
    gcongr
  refine ⟨?_, ?_⟩
  · refine hint.mono' ?_ (ae_of_all _ hpt)
    exact ((vdd hx c).div (by fun_prop) fun t =>
      mul_ne_zero (veC t hwc) (vbi hc t)).aestronglyMeasurable
  · calc _ ≤ ∫ t, h t := integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hint
          (ae_of_all _ hpt)
      _ = C * A * J := by
          simp only [hh]
          rw [integral_const_mul, integral_add ((vbo hr w.im).const_mul _)
            ((vbo hr 0).const_mul _), integral_const_mul,
            integral_const_mul, vdC, vdC]
          rw [hA]; ring
      _ ≤ _ := by
          rw [hC]
          have hw1 : (1 + ‖w‖) / 6 ≤ D / 2 := by
            have : ‖w‖ ≤ ‖w + 1‖ + 1 := by
              have := norm_sub_le (w + 1) 1; simpa using this
            have h1 : ‖w + 1‖ ≤ D := le_max_right _ _
            have h2 : (1 : ℝ) ≤ D := le_max_left _ _
            linarith
          have hθ' : (D / 2) ^ (-θ) ≤ (6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ) := by
            rw [← Real.mul_rpow (by norm_num) (by positivity)]
            exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          calc x ^ c * (D / 2) ^ (-θ) * A * J
              ≤ x ^ c * ((6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ)) * A * J := by gcongr
            _ = _ := by ring
end Erdos985.Analytic.PerronAux
end
section
open Complex MeasureTheory Set
namespace Erdos985.Analytic
open PerronAux
theorem vjl (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
   (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
   = (max 0 (1 - 1 / y) : ℝ) :=
 PerronKernel.vfv y c hy hc
theorem vfd (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
  (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
   (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
   = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) :=
 PerronKernel.vhy x c hx hc w hw hw0 hw1
theorem veW (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = 0) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
   (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
   = (Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ) := by
 subst hw
 have hx0 : 0 < x := by linarith
 have key := vih (c := c) hx0 (-1) 0 (-1) 0 1 0 0 1
  (by simp) (by simpa using hc) (by simpa using hc)
  (by simpa using hc) (by simpa using (show 0 < c + 1 by linarith))
  (fun _ => by ring) (F := fun s => 1 / ((s - 0) * s * (s + 1)))
  (fun t => by
   have h0 := veQ hc t
   have h1 := vbi hc t
   simp only [add_zero, sub_zero]
   field_simp
   ring)
  (vce hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
   (fun _ => by simp) (w := 0) (by simpa using hc))
 simp only [mul_one_div] at key
 rw [key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
  ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
 push_cast
 simp only [cpow_one, cpow_zero]
 ring
theorem vgw (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = -1) :
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
   (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
   = 1 - (x : ℂ) ^ (-1 : ℂ) - (x : ℂ) ^ (-1 : ℂ) * (Real.log x : ℂ) := by
 subst hw
 have hx0 : 0 < x := by linarith
 have key := vih (c := c) hx0 1 1 1 (-1) 0 0 1 0
  (by simp) (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
  (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
  (fun _ => by ring) (F := fun s => 1 / ((s - -1) * s * (s + 1)))
  (fun t => by
   have h0 := veQ hc t
   have h1 := vbi hc t
   simp only [add_zero, sub_neg_eq_add]
   field_simp
   ring)
  (vce hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
   (fun _ => by simp) (w := -1) (by simp; linarith))
 simp only [mul_one_div] at key
 rw [key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
  ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
 push_cast
 simp only [cpow_one, cpow_zero]
 ring
theorem vdz (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
  Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
 vcr hx hc hw
theorem vcS {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
   Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
   ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
    (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
    ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) :=
 vfk hδ hθ0 hθ1
end Erdos985.Analytic
end
section
open Real Filter Topology
namespace Erdos985.Analytic.DigammaAux
lemma vhL {a : ℝ} (ha : 0 < a) :
    log (1 + a⁻¹) ≤ 1 / (2 * a) + 1 / (2 * (a + 1)) := by
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 * y)
  have hle := hasSum_le (fun k : ℕ => ?_) (hasSum_log_one_add_inv ha) hg
  · refine hle.trans (le_of_eq ?_)
    have h2a : (2 * a + 1) ≠ 0 := by positivity
    have e1 : 1 - y ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
      rw [hy]; field_simp; ring
    rw [e1, hy]
    field_simp
    ring
  · rw [← hy, pow_succ, ← pow_mul]
    have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    have h2 : 0 ≤ y ^ (2 * k) * y := by positivity
    nlinarith
end Erdos985.Analytic.DigammaAux
end
section
open Real ArithmeticFunction
namespace Erdos985.Analytic.ConstantsAux
lemma vco (m : ℝ) (hm : 0 < m) :
  Real.log (m + 1) ≤ Real.log m + (1 / (2 * m) + 1 / (2 * (m + 1))) := by
 have h := Erdos985.Analytic.DigammaAux.vhL hm
 have e : Real.log (m + 1) = Real.log m + Real.log (1 + m⁻¹) := by
  rw [← Real.log_mul hm.ne' (by positivity)]
  congr 1
  field_simp
 linarith
lemma vjp :
  Real.log 2 ≤ 0.6931471808 ∧ Real.log 3 ≤ 1.098749 ∧ Real.log 5 ≤ 1.609512 ∧
  Real.log 7 ≤ 1.945980 ∧ Real.log 11 ≤ 2.398001 ∧ Real.log 13 ≤ 2.565052 ∧
  Real.log 17 ≤ 2.833350 ∧ Real.log 19 ≤ 2.944613 := by
 have p2 := Real.log_two_lt_d9.le
 have p3 : 2 * Real.log 3 ≤ 3 * Real.log 2 + (1 / (2 * 8) + 1 / (2 * (8 + 1))) := by
  have h := vco 8 (by norm_num)
  have e1 : Real.log (8 + 1) = 2 * Real.log 3 := by
   rw [show (8 : ℝ) + 1 = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 8 = 3 * Real.log 2 := by
   rw [show (8 : ℝ) = 2^3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 have p5 : 2 * Real.log 5 ≤ 3 * Real.log 2 + Real.log 3 + (1 / (2 * 24) + 1 / (2 * (24 + 1))) := by
  have h := vco 24 (by norm_num)
  have e1 : Real.log (24 + 1) = 2 * Real.log 5 := by
   rw [show (24 : ℝ) + 1 = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
   rw [show (24 : ℝ) = 2^3 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 have p7 : 2 * Real.log 7 ≤ 4 * Real.log 2 + Real.log 3 + (1 / (2 * 48) + 1 / (2 * (48 + 1))) := by
  have h := vco 48 (by norm_num)
  have e1 : Real.log (48 + 1) = 2 * Real.log 7 := by
   rw [show (48 : ℝ) + 1 = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
   rw [show (48 : ℝ) = 2^4 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 have p11 : 2 * Real.log 11 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 5 + (1 / (2 * 120) + 1 / (2 * (120 + 1))) := by
  have h := vco 120 (by norm_num)
  have e1 : Real.log (120 + 1) = 2 * Real.log 11 := by
   rw [show (120 : ℝ) + 1 = 11 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 120 = 3 * Real.log 2 + Real.log 3 + Real.log 5 := by
   rw [show (120 : ℝ) = 2^3 * 3 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 have p13 : 2 * Real.log 13 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 7 + (1 / (2 * 168) + 1 / (2 * (168 + 1))) := by
  have h := vco 168 (by norm_num)
  have e1 : Real.log (168 + 1) = 2 * Real.log 13 := by
   rw [show (168 : ℝ) + 1 = 13 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 168 = 3 * Real.log 2 + Real.log 3 + Real.log 7 := by
   rw [show (168 : ℝ) = 2^3 * 3 * 7 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 have p17 : 2 * Real.log 17 ≤ 5 * Real.log 2 + 2 * Real.log 3 + (1 / (2 * 288) + 1 / (2 * (288 + 1))) := by
  have h := vco 288 (by norm_num)
  have e1 : Real.log (288 + 1) = 2 * Real.log 17 := by
   rw [show (288 : ℝ) + 1 = 17 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 288 = 5 * Real.log 2 + 2 * Real.log 3 := by
   rw [show (288 : ℝ) = 2^5 * 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 have p19 : 2 * Real.log 19 ≤ 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + (1 / (2 * 360) + 1 / (2 * (360 + 1))) := by
  have h := vco 360 (by norm_num)
  have e1 : Real.log (360 + 1) = 2 * Real.log 19 := by
   rw [show (360 : ℝ) + 1 = 19 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log 360 = 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
   rw [show (360 : ℝ) = 2^3 * 3^2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [e1, e2] at h; exact h
 norm_num at *
 refine ⟨p2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
end Erdos985.Analytic.ConstantsAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
noncomputable def vbP (χ : DirichletCharacter ℂ N) : ℕ := if χ.Even then 0 else 1
noncomputable def vba (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
 -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + vbP χ) / 2)
noncomputable def vbn (χ : DirichletCharacter ℂ N) (x : ℕ) : ℂ :=
 (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
  (vba χ (2 + t * I) - vba χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
   / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
noncomputable def vdg (x : ℕ) (ρ : ℂ) : ℂ :=
 (1 - 1 / (x : ℂ)) / (2 - ρ)
  - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.StepAAux
open Complex
theorem vfF {w : ℂ} (hw : 0 < w.re) :
  HasDerivAt Gamma (Gamma w * digamma w) w := by
 have hd : DifferentiableAt ℂ Gamma w := differentiableAt_Gamma w fun m h => by
  rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
 convert hd.hasDerivAt using 1
 all_goals try with_reducible_and_instances rfl
 rw [digamma_def, logDeriv_apply, mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hw)]
theorem hasDerivAt_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gammaℝ (Gammaℝ w * (-(1 / 2) * (Real.log Real.pi : ℂ)
      + (1 / 2) * digamma (w / 2))) w := by
  have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) w := by
    simpa using ((hasDerivAt_id w).neg.div_const 2)
  have h2 := h1.const_cpow (c := (Real.pi : ℂ)) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h3 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) w := by
    simpa using (hasDerivAt_id w).div_const 2
  have hw2 : 0 < (w / 2).re := by simp; linarith
  have h4 := (vfF hw2).comp w h3
  have h5 := h2.mul h4
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (ofReal_log Real.pi_pos.le).symm
  convert h5 using 1
  all_goals try with_reducible_and_instances rfl
  · rfl
  · rw [hlog, Gammaℝ_def]; simp only [Function.comp_apply]; ring
variable {N : ℕ}
end Erdos985.Analytic.StepAAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real
def q6 (F : ℂ → ℂ) : Prop :=
 ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))
lemma vcJ {u : ℝ} (hu : 3 ≤ u) : 1 ≤ log u := by
 have h3 : exp 1 < 3 := lt_of_lt_of_le exp_one_lt_d9 (by norm_num)
 rw [le_log_iff_exp_le (by linarith)]
 linarith
lemma viI {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u * log u ≤ v * log v :=
 mul_le_mul huv (log_le_log (by linarith) huv) (log_nonneg hu) (by linarith)
lemma vjg {a a' b b' y y' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 3 ≤ b) (hy : 0 ≤ y)
  (hle : y + b ≤ y' + b') :
  a * ((y + b) * log (y + b)) ≤ a' * ((y' + b') * log (y' + b')) := by
 have h1 : 1 ≤ log (y + b) := vcJ (by linarith)
 have h2 : (y + b) * log (y + b) ≤ (y' + b') * log (y' + b') :=
  viI (by linarith) hle
 have h3 : 0 ≤ (y' + b') * log (y' + b') := by nlinarith
 exact mul_le_mul haa h2 (by nlinarith) (ha.trans haa)
lemma q6.vgY {F : ℂ → ℂ} {K a b : ℝ}
  (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) : 0 ≤ K :=
 nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h 0)) (exp_pos _)
lemma q6.mono {F : ℂ → ℂ} {K a b : ℝ} (ha : 0 ≤ a) (hb : 3 ≤ b)
  (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) {a' b' : ℝ} (haa : a ≤ a')
  (hbb : b ≤ b') : ∀ s, ‖F s‖ ≤ K * exp (a' * ((‖s‖ + b') * log (‖s‖ + b'))) := by
 intro s
 refine (h s).trans (mul_le_mul_of_nonneg_left ?_ (q6.vgY h))
 exact exp_le_exp.2 (vjg ha haa hb (norm_nonneg _) (by linarith))
lemma q6.congr {F G : ℂ → ℂ} (hF : q6 F) (h : ∀ s, F s = G s) : q6 G := by
 obtain ⟨K, a, b, ha, hb, hK⟩ := hF
 exact ⟨K, a, b, ha, hb, fun s => h s ▸ hK s⟩
lemma q6.const (c : ℂ) : q6 (fun _ => c) :=
 ⟨‖c‖, 0, 3, le_rfl, le_rfl, fun s => by simp⟩
lemma q6.add {F G : ℂ → ℂ} (hF : q6 F) (hG : q6 G) :
    q6 (fun s => F s + G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K + K', max a a', max b b', le_max_of_le_left ha, le_max_of_le_left hb, fun s => ?_⟩
  have h1 := q6.mono ha hb hK (le_max_left a a') (le_max_left b b') s
  have h2 := q6.mono ha' hb' hK' (le_max_right a a') (le_max_right b b') s
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
lemma q6.mul {F G : ℂ → ℂ} (hF : q6 F) (hG : q6 G) :
    q6 (fun s => F s * G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K * K', a + a', max b b', add_nonneg ha ha', le_max_of_le_left hb, fun s => ?_⟩
  have h1 := q6.mono ha hb hK le_rfl (le_max_left b b') s
  have h2 := q6.mono ha' hb' hK' le_rfl (le_max_right b b') s
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ _ := mul_le_mul h1 h2 (norm_nonneg _)
        (mul_nonneg (q6.vgY hK) (exp_pos _).le)
    _ = _ := by rw [add_mul a a', exp_add]; ring
lemma q6.comp {F : ℂ → ℂ} (hF : q6 F) {g : ℂ → ℂ} {d : ℝ} (hd : 0 ≤ d)
  (hg : ∀ s, ‖g s‖ ≤ ‖s‖ + d) : q6 (fun s => F (g s)) := by
 obtain ⟨K, a, b, ha, hb, hK⟩ := hF
 refine ⟨K, a, b + d, ha, by linarith, fun s => (hK (g s)).trans ?_⟩
 refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (q6.vgY hK)
 exact vjg ha le_rfl hb (norm_nonneg _) (by linarith [hg s])
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set MeasureTheory
open scoped Nat
lemma vdQ {y : ℝ} (hy : 0 < y) (m : ℕ) : exp (-y) ≤ m ! * y⁻¹ ^ m := by
  have h := pow_div_factorial_le_exp (x := y) (hx := hy.le) (n := m)
  have hpos : 0 < y ^ m / m ! := by positivity
  rw [exp_neg]
  calc (exp y)⁻¹ ≤ (y ^ m / m !)⁻¹ := inv_anti₀ hpos h
    _ = m ! * y⁻¹ ^ m := by rw [inv_div, inv_pow, div_eq_mul_inv]
noncomputable def veu : ℝ → ℝ :=
 (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))
lemma vhp : IntegrableOn veu (Ioi 0) := by
 have h1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
  (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
 have h2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ))) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).integrable_indicator measurableSet_Ioi
 exact (h1.add h2).integrableOn
lemma viu (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * veu t := by
  have hsre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk := P.hk
  have hA : 0 ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by positivity
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  ·
    have hdom : veu t = 1 := by
      simp [veu, indicator, ht, h1.le, not_lt.2 h1.le]
    rw [hdom, mul_one]
    have hfm : P.f_modif t = (P.ε * ((1 / t) ^ P.k : ℝ)) • (P.g (1 / t) - P.g₀) := by
      have hfe := P.h_feq (1 / t) (by simpa using ht)
      rw [one_div_one_div] at hfe
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator, mem_Ioi, mem_Ioo, ht, h1,
        and_self, ite_true, not_lt.2 h1.le, ite_false, zero_add, hfe, smul_sub]
      congr 2
      rw [one_div, inv_rpow ht.le, rpow_neg ht.le]
    have h1t : 1 < 1 / t := by rw [lt_one_div one_pos ht, div_one]; exact h1
    rw [hfm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hgb := hg (1 / t) h1t
    have he := vdQ (show 0 < p * (1 / t) by positivity) m
    rw [neg_mul] at hgb
    have hcalc : t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m) ≤ 1 := by
      rw [one_div, inv_inv, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_natCast,
        ← rpow_add ht, ← rpow_add ht]
      apply rpow_le_one ht.le h1.le
      have := neg_abs_le s.re
      linarith
    calc t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖)
        ≤ t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * (C * (m ! * (p * (1 / t))⁻¹ ^ m))) := by
          gcongr
          exact hgb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * ‖P.ε‖ * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m)) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * ‖P.ε‖ * m ! * p⁻¹ ^ m * 1 := by gcongr
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by
          rw [mul_one]; gcongr; exact le_max_right _ _
  · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hA (by simp [veu])
  ·
    have hdom : veu t = t ^ (-2 : ℝ) := by
      simp [veu, indicator, h1, not_le.2 h1]
    rw [hdom]
    have hfm : P.f_modif t = P.f t - P.f₀ := by
      simp [WeakFEPair.f_modif, indicator, h1, not_lt.2 h1.le]
    rw [hfm]
    have he := vdQ (show 0 < p * t by positivity) m
    have hfb := hf t h1
    rw [neg_mul] at hfb
    have ht0 : 0 < t := ht
    have hcalc : t ^ (s.re - 1) * t⁻¹ ^ m ≤ t ^ (-2 : ℝ) := by
      rw [inv_pow, ← rpow_natCast, ← rpow_neg ht.le, ← rpow_add ht]
      apply rpow_le_rpow_of_exponent_le h1.le
      have := le_abs_self s.re
      linarith
    calc t ^ (s.re - 1) * ‖P.f t - P.f₀‖
        ≤ t ^ (s.re - 1) * (C * (m ! * (p * t)⁻¹ ^ m)) := by
          gcongr
          exact hfb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * 1 * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * t⁻¹ ^ m) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * t ^ (-2 : ℝ) := by
          gcongr
          exact le_max_left _ _
lemma vjL (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
  (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
  (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
  (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) :
  ‖P.Λ₀ s‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ∫ t in Ioi 0, veu t := by
 rw [← integral_const_mul]
 refine norm_integral_le_of_norm_le (vhp.const_mul _) ?_
 exact ae_restrict_of_forall_mem measurableSet_Ioi
  (fun t ht => viu P hp hC hf hg s m hm t ht)
theorem viF (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) : q6 P.Λ₀ := by
  set I0 := ∫ t in Ioi 0, veu t
  set Q := max 1 p⁻¹
  have hQ : 1 ≤ Q := le_max_left _ _
  have hk := P.hk
  set b := P.k + 5
  refine ⟨C * max 1 ‖P.ε‖ * I0, 1 + log Q, b, by linarith [log_nonneg hQ], by linarith,
    fun s => ?_⟩
  set m := ⌈‖s‖ + P.k + 1⌉₊
  have hm : ‖s‖ + P.k + 1 ≤ m := Nat.le_ceil _
  have hm' : (m : ℝ) ≤ ‖s‖ + b := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖s‖ + P.k + 1 by positivity)
    linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith [norm_nonneg s]
  have hI0 : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun t _ => by
    simp only [veu, Pi.add_apply]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _) _))
  refine (vjL P hp hC hf hg s m hm).trans ?_
  have hfac : (m ! : ℝ) * p⁻¹ ^ m ≤ exp ((1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b))) := by
    have h1 : (m ! : ℝ) * p⁻¹ ^ m ≤ ((m : ℝ) * Q) ^ m := by
      rw [mul_pow]
      gcongr
      · exact_mod_cast Nat.factorial_le_pow m
      · exact le_max_right _ _
    have h2 : ((m : ℝ) * Q) ^ m = exp (m * log (m * Q)) := by
      rw [← log_pow, exp_log (by positivity)]
    have hL : 1 ≤ log (‖s‖ + b) := vcJ (by linarith [norm_nonneg s])
    have hlogQ : 0 ≤ log Q := log_nonneg hQ
    have h3 : (m : ℝ) * log (m * Q) ≤ (1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b)) := by
      rw [log_mul (by positivity) (by positivity)]
      have e1 : (m : ℝ) * log m ≤ (‖s‖ + b) * log (‖s‖ + b) := viI hm1 hm'
      have e2 : (m : ℝ) * log Q ≤ (‖s‖ + b) * log (‖s‖ + b) * log Q := by
        have : (m : ℝ) ≤ (‖s‖ + b) * log (‖s‖ + b) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlogQ
      nlinarith
    rw [h2] at h1
    exact h1.trans (exp_le_exp.2 h3)
  have hE : 0 ≤ C * max 1 ‖P.ε‖ := by positivity
  calc C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * I0 = C * max 1 ‖P.ε‖ * I0 * (m ! * p⁻¹ ^ m) := by ring
    _ ≤ _ := by gcongr
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set Filter Asymptotics HurwitzZeta
lemma veY {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (h : F =O[atTop] fun x => exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 < t → |F t| ≤ C * exp (-p * t) := by
  obtain ⟨c, hc'⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc'
  set T' := max T 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T')).exists_bound_of_continuousOn
    (hc.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
  refine ⟨max (max c 0) (max M 0 * exp (p * T')), by positivity, fun t ht => ?_⟩
  rcases le_total T' t with h1 | h1
  · have := hT t ((le_max_left _ _).trans h1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have h2 := hM t ⟨ht.le, h1⟩
    rw [Real.norm_eq_abs] at h2
    calc |F t| ≤ max M 0 := h2.trans (le_max_left _ _)
      _ ≤ max M 0 * (exp (p * T') * exp (-p * t)) := by
          refine le_mul_of_one_le_right (le_max_right _ _) ?_
          rw [← exp_add, one_le_exp_iff]
          nlinarith
      _ = (max M 0 * exp (p * T')) * exp (-p * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
lemma viX {f g : ℝ → ℝ} {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hf : ∀ t, 1 < t → f t ≤ C₁ * exp (-p₁ * t)) (hg : ∀ t, 1 < t → g t ≤ C₂ * exp (-p₂ * t)) :
    ∃ p C, 0 < p ∧ 0 ≤ C ∧ (∀ t, 1 < t → f t ≤ C * exp (-p * t)) ∧
      (∀ t, 1 < t → g t ≤ C * exp (-p * t)) := by
  refine ⟨min p₁ p₂, max C₁ C₂, lt_min hp₁ hp₂, le_max_of_le_left hC₁, fun t ht => ?_,
    fun t ht => ?_⟩
  · refine (hf t ht).trans (mul_le_mul (le_max_left _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_left p₁ p₂]
  · refine (hg t ht).trans (mul_le_mul (le_max_right _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_right p₁ p₂]
lemma viY (a : UnitAddCircle) : q6 (hurwitzEvenFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C₁, hC₁, hb₁⟩ := veY
    ((continuousOn_evenKernel a).sub continuousOn_const) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := veY
    ((continuousOn_cosKernel a).sub continuousOn_const) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := viX hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine viF _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · have : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀ =
        ((evenKernel a t - if a = 0 then 1 else 0 : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hf t ht
  · have : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀ =
        ((cosKernel a t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hg t ht
lemma vdG (a : UnitAddCircle) :
    q6 (completedHurwitzZetaEven₀ a) := by
  refine (((viY a).comp (g := fun s => s / 2) le_rfl (fun s => ?_)).mul
    (q6.const (1 / 2))).congr (fun s => ?_)
  · rw [norm_div, Complex.norm_two, add_zero]
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaEven₀]; ring
end Erdos985.Analytic.XiOrderAux
end
section
open Complex
namespace Erdos985.Analytic
noncomputable def van (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1
theorem vbd : Differentiable ℂ van := by
 unfold van
 have := differentiable_completedZeta₀
 fun_prop
theorem vgq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
  van s = s * (s - 1) * completedRiemannZeta s := by
 have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
 have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
 rw [van, completedRiemannZeta_eq]
 field_simp
 ring
theorem vds : van 0 = 1 := by simp [van]
open XiOrderAux in
theorem vht {F : ℂ → ℂ} (hF : q6 F) :
    ∃ C : ℝ, ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨K, a, b, ha, hb, h⟩ := hF
  have hK : 0 ≤ K := q6.vgY h
  set lb := Real.log b
  have hlb : 0 ≤ lb := Real.log_nonneg (by linarith)
  set C₀ := a * (2 * lb + 1 + 2 * b)
  set D := a * (b * (lb + 1))
  refine ⟨max (K * Real.exp D) C₀, fun s => (h s).trans ?_⟩
  set u := ‖s‖
  have hu : 0 ≤ u := norm_nonneg s
  set ℓ := Real.log (u + 2)
  have hℓ2 : (1 / 2 : ℝ) ≤ ℓ := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hℓu : ℓ ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by linarith); linarith
  have hL : 0 ≤ u * ℓ := by positivity
  have h1 : Real.log (u + b) ≤ lb + ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : u ≤ 2 * (u * ℓ) := by nlinarith
  have key : a * ((u + b) * Real.log (u + b)) ≤ C₀ * (u * ℓ) + D := by
    have e : (u + b) * Real.log (u + b) ≤ (2 * lb + 1 + 2 * b) * (u * ℓ) + b * (lb + 1) := by
      calc (u + b) * Real.log (u + b) ≤ (u + b) * (lb + ℓ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = lb * u + u * ℓ + b * lb + b * ℓ := by ring
        _ ≤ lb * (2 * (u * ℓ)) + u * ℓ + b * lb + b * (2 * (u * ℓ) + 1) := by
            gcongr; linarith
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left e ha
    simp only [C₀, D]; nlinarith
  calc K * Real.exp (a * ((u + b) * Real.log (u + b)))
      ≤ K * Real.exp (C₀ * (u * ℓ) + D) := by gcongr
    _ = K * Real.exp D * Real.exp (C₀ * (u * ℓ)) := by
        rw [Real.exp_add]; ring
    _ ≤ max (K * Real.exp D) C₀ * Real.exp (max (K * Real.exp D) C₀ * (u * ℓ)) :=
        mul_le_mul (le_max_left _ _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL))
          (Real.exp_pos _).le (le_max_of_le_left (by positivity))
    _ = _ := by ring_nf
theorem vfp :
  ∃ C : ℝ, ∀ s : ℂ, ‖van s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
 open XiOrderAux in
 have hid : q6 (fun s : ℂ => s) := by
  refine ⟨1, 1, 3, zero_le_one, le_rfl, fun s => ?_⟩
  have h3 : 1 ≤ Real.log (‖s‖ + 3) := vcJ (by linarith [norm_nonneg s])
  have := Real.add_one_le_exp ‖s‖
  have : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by nlinarith [norm_nonneg s]
  have : Real.exp ‖s‖ ≤ Real.exp (1 * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
   Real.exp_le_exp.mpr (by linarith)
  linarith
 open XiOrderAux in
 have h : q6 van :=
  (((hid.mul (hid.add (q6.const (-1)))).mul
   (vdG 0)).add (q6.const 1)).congr fun s => by
    simp only [van, completedRiemannZeta₀]; ring
 exact vht h
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.IdentityAux
open Complex MeasureTheory
theorem vha {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (hF_int : ∀ i, Integrable (F i))
    (hF_sum : Summable fun i => ∫ t, ‖F i t‖) (hsum : ∀ t, HasSum (fun i => F i t) (f t)) :
    Integrable f := by
  refine ⟨hf, ?_⟩
  have h1 : ∀ t, ‖f t‖ₑ ≤ ∑' i, ‖F i t‖ₑ := fun t => by
    rw [← (hsum t).tsum_eq]; exact enorm_tsum_le_tsum_enorm
  unfold HasFiniteIntegral
  calc ∫⁻ t, ‖f t‖ₑ ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ := lintegral_mono h1
    _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ := lintegral_tsum fun i => (hF_int i).1.enorm
    _ = ∑' i, ENNReal.ofReal (∫ t, ‖F i t‖) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF_int i)]
    _ = ENNReal.ofReal (∑' i, ∫ t, ‖F i t‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _)
          hF_sum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic.IdentityAux
end
section
namespace Erdos985.Analytic.IdentityAux
open Complex MeasureTheory
noncomputable def qad (x t : ℝ) : ℂ :=
 (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
noncomputable def vcB (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
 (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
noncomputable def vbH (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
 (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * qad x t
lemma vhk (t : ℝ) : (2 : ℂ) + t * I ≠ 0 := fun h => by
 have := congrArg re h; simp at this
lemma veD (t : ℝ) : (2 : ℂ) + t * I + 1 ≠ 0 := fun h => by
 have := congrArg re h; simp at this; norm_num at this
lemma vfw {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) : (2 : ℂ) + t * I - ρ ≠ 0 := fun h => by
 have := congrArg re h; simp at this; linarith
lemma vin {ρ : ℂ} (hρ : ρ.re < 2) : (2 : ℂ) - ρ ≠ 0 := fun h => by
 have := congrArg re h; simp at this; linarith
lemma vic (x : ℝ) (ρ : ℂ) (t : ℝ) :
  vbH x ρ t = vcB x ρ t - (1 / (2 - ρ)) * qad x t := by
 unfold vbH vcB qad
 simp only [div_eq_mul_inv, mul_inv]
 ring
lemma vbV {x : ℝ} (hx : 0 < x) : Integrable (qad x) := by
 have := PerronKernel.vhJ 2 x two_pos hx
 unfold PerronKernel.K at this
 simp only [ofReal_ofNat] at this
 exact this
lemma vdK {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
  Integrable (vcB x ρ) := by
 have := vdz x 2 hx two_pos ρ (by simpa using hρ)
 simp only [ofReal_ofNat] at this
 exact this
lemma veZ {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
  Integrable (vbH x ρ) := by
 have : vbH x ρ = fun t => vcB x ρ t - (1 / (2 - ρ)) * qad x t :=
  funext (vic x ρ)
 rw [this]
 exact (vdK hx hρ).sub ((vbV hx).const_mul _)
lemma vhh {x : ℝ} (hx : 1 ≤ x) :
  ∫ t, qad x t = 2 * Real.pi * (1 - 1 / (x : ℂ)) := by
 have h := PerronKernel.vhm x 2 (by linarith) two_pos
 simp only [ofReal_ofNat] at h
 rw [show (∫ t, qad x t) = _ from h, ite_eq_left_iff.2 (fun h => absurd hx h)]
 push_cast
 ring
lemma via (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0)
  (hρ1 : ρ ≠ -1) :
  ∫ t, vbH (x : ℝ) ρ t = -(2 * Real.pi) * vdg x ρ := by
 have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
 have hx0 : (0 : ℝ) < x := by linarith
 have h := vfd (x : ℝ) 2 hx' two_pos ρ (by simpa using hρ) hρ0 hρ1
 simp only [ofReal_ofNat, ofReal_natCast] at h
 have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
 have hR : ∫ t, vcB (x : ℝ) ρ t = 2 * Real.pi * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ
   + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ)) := by
  rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  simp [vcB]
 have hK := vhh hx'
 simp_rw [vic]
 rw [integral_sub (vdK hx0 hρ) ((vbV hx0).const_mul _),
  integral_const_mul, hR, hK]
 simp only [ofReal_natCast]
 unfold vdg
 ring
lemma vii {x : ℝ} {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) :
    ‖vbH x ρ t‖ ≤
      ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
        / ‖(2 : ℂ) - ρ‖ := by
  have h0 := vhk t
  have h1 := veD t
  have h2 := vfw hρ t
  have h3 := vin hρ
  have heq : vbH x ρ t = ((2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1)))
        / (2 - ρ) := by
    unfold vbH qad
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  gcongr
  calc ‖(2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)‖ * _ ≤ 1 * _ := by
        gcongr
        rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
        have e : (2 : ℂ) - ((2 : ℂ) + t * I) = -(t * I) := by ring
        rw [e, norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        have := abs_im_le_norm ((2 : ℂ) + t * I)
        simpa using this
    _ = _ := one_mul _
theorem vfD :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ ρ : ℂ, ρ.re < 1 → ρ ≠ 0 →
      ∫ t, ‖vbH x ρ t‖ ≤ C * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := vcS (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  refine ⟨3 * K, by positivity, fun x hx ρ hρ hρ0 => ?_⟩
  obtain ⟨hint, hbd⟩ := hK x 2 hx two_pos ρ (by norm_num; exact hρ.le)
  simp only [ofReal_ofNat] at hint hbd
  have hρ2 : ρ.re < 2 := by linarith
  have ha : 1 < ‖(2 : ℂ) - ρ‖ := by
    have := re_le_norm ((2 : ℂ) - ρ); simp at this; linarith
  have hr : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  calc ∫ t, ‖vbH x ρ t‖
      ≤ ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
          / ‖(2 : ℂ) - ρ‖ :=
        integral_mono (veZ hx hρ2).norm (hint.norm.div_const _)
          (vii hρ2)
    _ = (∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖)
          / ‖(2 : ℂ) - ρ‖ := integral_div _ _
    _ ≤ K * x ^ (2 : ℝ) * (1 + ‖ρ‖) ^ (-(1 / 2 : ℝ)) / ‖(2 : ℂ) - ρ‖ := by gcongr
    _ ≤ 3 * K * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
        have hle : ‖ρ‖ ≤ 3 * ‖(2 : ℂ) - ρ‖ := by
          have := norm_sub_le (2 : ℂ) ((2 : ℂ) - ρ)
          simp at this
          linarith
        have hsq : ‖ρ‖ ^ (1 / 2 : ℝ) ≤ (1 + ‖ρ‖) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hr.le (by linarith) (by norm_num)
        rw [Real.rpow_neg (by positivity), Real.rpow_add hr, Real.rpow_one]
        have hp1 : 0 < (1 + ‖ρ‖) ^ (1 / 2 : ℝ) := by positivity
        have hp2 : 0 < ‖ρ‖ ^ (1 / 2 : ℝ) := by positivity
        have hxk : 0 ≤ K * x ^ (2 : ℝ) := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹ * (‖ρ‖ * ‖ρ‖ ^ (1 / 2 : ℝ))
            ≤ K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹
                * (3 * ‖(2 : ℂ) - ρ‖ * (1 + ‖ρ‖) ^ (1 / 2 : ℝ)) := by
              gcongr
          _ = 3 * K * x ^ (2 : ℝ) * ‖(2 : ℂ) - ρ‖ := by
              field_simp
end Erdos985.Analytic.IdentityAux
end
section
namespace Erdos985.Analytic.BoundsAux
open Complex
lemma vjK (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
  vdg x ρ = 2 / (ρ * (2 - ρ)) - (3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))
   - (x : ℂ) ^ ρ / (ρ * (ρ + 1)) := by
 have h0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
 have h2 : (2 : ℂ) - ρ ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
 have h1 : (1 : ℂ) + ρ ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
 have h1' : ρ + 1 ≠ 0 := by rwa [add_comm]
 have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
 unfold vdg
 rw [cpow_neg_one]
 field_simp
 ring
lemma viy {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖(2 : ℂ) - ρ‖ = ‖ρ + 1‖ := by
 rw [← Complex.norm_conj (ρ + 1)]
 congr 1
 apply Complex.ext <;> norm_num [hρ]
lemma vcf {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
 rw [Complex.norm_def, Complex.norm_def]
 apply Real.sqrt_le_sqrt
 simp [Complex.normSq_apply, hρ]
 norm_num
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open Complex BoundsAux
end Erdos985.Analytic
end
section
open Real ArithmeticFunction
namespace Erdos985.Analytic.BoundsAux
lemma vjG (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) 2 n = ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]
    push_cast
    rfl
lemma vfg (f : ℕ → ℝ) :
  LSeries (fun n => (f n : ℂ)) 2 = ((∑' n : ℕ, f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
 rw [LSeries, Complex.ofReal_tsum]
 exact tsum_congr (vjG f)
lemma vhf (f : ℕ → ℝ) (h : LSeriesSummable (fun n => (f n : ℂ)) 2) :
  Summable fun n : ℕ => f n / (n : ℝ) ^ 2 := by
 have : LSeries.term (fun n => (f n : ℂ)) 2 =
   fun n => ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := funext (vjG f)
 rw [LSeriesSummable, this] at h
 exact Complex.summable_ofReal.mp h
lemma re2 : 1 < (2 : ℂ).re := by norm_num
lemma vjq : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ 2 := by
 refine vhf (fun n => Real.log n) ?_
 have := (LSeriesSummable_vonMangoldt re2).convolution (LSeriesSummable_one_iff.mpr re2)
 rw [convolution_vonMangoldt_const_one] at this
 convert this using 2 with n
 simp [Complex.natCast_log]
lemma vkv :
  (∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) =
   ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
 have h := LSeries_convolution' (LSeriesSummable_vonMangoldt re2)
  (LSeriesSummable_one_iff.mpr re2)
 rw [convolution_vonMangoldt_const_one] at h
 have e1 := vfg (fun n => (Λ n : ℝ))
 have e2 := vfg (fun _ => (1 : ℝ))
 have e3 := vfg (fun n : ℕ => Real.log n)
 have h1 : (1 : ℕ → ℂ) = fun _ => ((1 : ℝ) : ℂ) := by ext; simp
 have h3 : (fun n : ℕ => Complex.log n) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
  ext n; simp [Complex.natCast_log]
 rw [h1, h3, e1, e2, e3] at h
 exact_mod_cast h.symm
lemma vku {c y : ℝ} (hc : 2 ≤ c) (hcy : c ≤ y) :
  Real.log y / y ^ 2 ≤ Real.log c / c ^ 2 := by
 have hc0 : 0 < c := by linarith
 have hy0 : 0 < y := by linarith
 have hL : 2 / 3 ≤ Real.log c := by
  have := Real.log_le_log (by norm_num) hc
  linarith [Real.log_two_gt_d9]
 have hlog : Real.log y - Real.log c ≤ y / c - 1 := by
  rw [← Real.log_div hy0.ne' hc0.ne']
  exact Real.log_le_sub_one_of_pos (by positivity)
 have hlog' : (Real.log y - Real.log c) * c ≤ y - c := by
  have : y / c - 1 = (y - c) / c := by field_simp
  rw [this, le_div_iff₀ hc0] at hlog; exact hlog
 rw [div_le_div_iff₀ (by positivity) (by positivity)]
 have h1 : 0 ≤ y - c := by linarith
 have : (y - c) * c ≤ Real.log c * (y - c) * (y + c) := by
  have : c ≤ Real.log c * (y + c) := by nlinarith
  nlinarith
 nlinarith
noncomputable def G2 (x : ℝ) : ℝ := (Real.log x + 1) / x
lemma vhl {t : ℝ} (ht : 0 < t) :
  HasDerivAt G2 (-(Real.log t / t ^ 2)) t := by
 have h1 : HasDerivAt (fun x => Real.log x + 1) (t⁻¹) t :=
  (Real.hasDerivAt_log ht.ne').add_const 1
 have := h1.div (hasDerivAt_id' t) ht.ne'
 unfold G2
 convert this using 1
 all_goals try with_reducible_and_instances rfl
 field_simp
 ring
lemma vky {x : ℝ} (hx : 2 ≤ x) :
  Real.log (x + 1) / (x + 1) ^ 2 ≤ G2 x - G2 (x + 1) := by
 obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope G2 (fun t => -(Real.log t / t ^ 2))
  (by linarith : x < x + 1)
  (fun t ht => (vhl (by linarith [ht.1])).continuousAt.continuousWithinAt)
  (fun t ht => vhl (by linarith [ht.1]))
 have : G2 x - G2 (x + 1) = Real.log c / c ^ 2 := by
  rw [show x + 1 - x = 1 by ring, div_one] at hcd
  linarith
 rw [this]
 exact vku (by linarith [hc.1]) hc.2.le
lemma vko {x : ℝ} (hx : 1 ≤ x) : 0 ≤ G2 x := by
 unfold G2
 have := Real.log_nonneg hx
 have : 0 < x := by linarith
 positivity
lemma vkx (K : ℕ) (hK : 3 ≤ K) :
    ∑' i : ℕ, Real.log ((i + K : ℕ) : ℝ) / (((i + K : ℕ) : ℝ)) ^ 2 ≤ G2 ((K : ℝ) - 1) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun M => ?_)
  · have : (1 : ℝ) ≤ ((i + K : ℕ) : ℝ) := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := Real.log_nonneg this
    positivity
  · have htel := Finset.sum_range_sub' (fun i : ℕ => G2 ((K : ℝ) - 1 + i)) M
    simp only [Nat.cast_zero, add_zero] at htel
    have hG : 0 ≤ G2 ((K : ℝ) - 1 + M) :=
      vko (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (le_of_eq_of_le htel (by linarith))
    have hx : (2 : ℝ) ≤ (K : ℝ) - 1 + i := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := vky hx
    push_cast
    rw [show (K : ℝ) - 1 + ((i : ℝ) + 1) = (K : ℝ) - 1 + i + 1 by ring,
      show (i : ℝ) + K = (K : ℝ) - 1 + i + 1 by ring]
    exact this
lemma vkE : ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 ≤ 0.962 := by
 obtain ⟨l2, l3, l5, -, -, -, -, -⟩ := ConstantsAux.vjp
 have hD := (vjq.sum_add_tsum_nat_add 7).symm
 have hdt := vkx 7 (by norm_num)
 simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hD
 norm_num at hD hdt
 unfold G2 at hdt
 have e4 : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
 have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
 rw [hD]
 norm_num [e4, e6] at hdt ⊢
 linarith
lemma vkC : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 ≤ 0.6 := by
 have hmul := vkv
 have hZ : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 := hasSum_zeta_two.tsum_eq
 have hD := vkE
 have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
  tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
 rw [hZ] at hmul
 have hpi : (1.643 : ℝ) ≤ π ^ 2 / 6 := by
  nlinarith [Real.pi_gt_d2, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3.14) Real.pi_gt_d2.le]
 set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2
 by_contra h
 have h' := (not_le.mp h).le
 nlinarith [mul_le_mul h' hpi (by norm_num) hS]
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open Complex BoundsAux
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
open Complex Filter Topology Set
namespace Erdos985.Analytic.BoundsAux
noncomputable def rD (x : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) x
lemma vgL {x : ℝ} (hx : 0 < x) : digamma (x : ℂ) = (rD x : ℂ) := by
 have hne : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
  have := congrArg Complex.re h
  simp at this
  linarith [m.cast_nonneg (α := ℝ)]
 have hneR : ∀ m : ℕ, x ≠ -m := fun m h => by linarith [m.cast_nonneg (α := ℝ)]
 have h1 := ((Complex.differentiableAt_Gamma _ hne).hasDerivAt).comp_ofReal
 have h2 := ((Real.differentiableAt_Gamma hneR).hasDerivAt).ofReal_comp
 have heq : (fun t : ℝ => Complex.Gamma (t : ℂ)) = fun t => ((Real.Gamma t : ℝ) : ℂ) :=
  funext Complex.Gamma_ofReal
 rw [heq] at h1
 have hd := h1.unique h2
 rw [digamma_def, logDeriv_apply, hd, Complex.Gamma_ofReal, rD, Function.comp_def,
  deriv.log (Real.differentiableAt_Gamma hneR) (Real.Gamma_pos_of_pos hx).ne']
 push_cast
 rfl
lemma vgl {x : ℝ} (hx : 1 < x) : Real.log (x - 1) ≤ rD x ∧ rD x ≤ Real.log x := by
  let f := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith [m.cast_nonneg (α := ℝ)])
  constructor
  · refine (le_of_eq ?_).trans (hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0:ℝ) < x - 1))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x)) (by linarith) (hder (by linarith)))
    rw [slope_def_field, show x - (x - 1) = (1:ℝ) by ring, div_one]
    have := h_rec (x - 1) (by linarith)
    rw [show x - 1 + 1 = x by ring] at this
    linarith
  · refine (hc.deriv_le_slope (mem_Ioi.mpr (by linarith : (0:ℝ) < x))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x + 1)) (by linarith) (hder (by linarith))).trans
      (le_of_eq ?_)
    rw [slope_def_field, show x + 1 - x = (1:ℝ) by ring, div_one, h_rec x (by linarith)]
    ring
lemma vgR {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log a - Real.log b ≤ a / b - 1 := by
 rw [← Real.log_div ha.ne' hb.ne']
 exact Real.log_le_sub_one_of_pos (by positivity)
lemma viV {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => rD (x + n) - rD (1 + n)) atTop (𝓝 0) := by
  have hC := tendsto_const_div_atTop_nhds_zero_nat (x + 4)
  have hC' := hC.neg
  rw [neg_zero] at hC'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hC' hC ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨l1, -⟩ := vgl (x := x + n) (by linarith)
    obtain ⟨-, u2⟩ := vgl (x := 1 + n) (by linarith)
    have := vgR (a := 1 + n) (b := x + n - 1) (by linarith) (by linarith)
    have hq : (1 + n) / (x + n - 1) - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨-, u1⟩ := vgl (x := x + n) (by linarith)
    obtain ⟨l2, -⟩ := vgl (x := 1 + n) (by linarith)
    rw [show 1 + (n : ℝ) - 1 = n by ring] at l2
    have := vgR (a := x + n) (b := n) (by linarith) (by linarith)
    have hq : (x + n) / n - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
lemma norm_term_le {w : ℂ} (hw : 1 / 2 < w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ 2 * (‖w‖ + 1) / ((k : ℝ) + 1) ^ 2 := by
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hre : ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + w‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp
    linarith [k.cast_nonneg (α := ℝ)]
  have hkw : ((k : ℂ) + w) ≠ 0 := by
    intro h; rw [h, norm_zero] at hre; linarith [k.cast_nonneg (α := ℝ)]
  rw [div_sub_div _ _ hk1 hkw, norm_div, norm_mul]
  have e1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [e1]
  have hnum : ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ ≤ ‖w‖ + 1 := by
    rw [show 1 * ((k : ℂ) + w) - (k + 1) * 1 = w - 1 by ring]
    exact (norm_sub_le _ _).trans (by simp)
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ ‖w‖ + 1 := by positivity
  calc ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ * ((k : ℝ) + 1) ^ 2
      ≤ (‖w‖ + 1) * ((k : ℝ) + 1) ^ 2 := by gcongr
    _ ≤ 2 * (‖w‖ + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + w‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * (‖w‖ + 1) * ((k : ℝ) + 1))]
lemma veM : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
 have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
 simpa using this
lemma vhn {w : ℂ} (hw : 1 / 2 < w.re) :
  Summable fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w) := by
 refine Summable.of_norm_bounded ?_ (norm_term_le hw)
 exact (veM.mul_left (2 * (‖w‖ + 1))).congr (fun k => by ring)
lemma vhr {x : ℝ} (hx : 1 / 2 < x) :
  HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) (digamma x - digamma 1) := by
 have hx0 : 0 < x := by linarith
 have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
  have := congrArg Complex.re h
  simp at this
  linarith [m.cast_nonneg (α := ℝ)]
 have h1' : ∀ m : ℕ, (1 : ℂ) ≠ -m := fun m h => by
  have := congrArg Complex.re h
  simp at this
  linarith [m.cast_nonneg (α := ℝ)]
 have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) =
   (digamma x - digamma 1) - (digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) := by
  intro n
  push_cast
  rw [digamma_apply_add_nat hx' n, digamma_apply_add_nat h1' n, Finset.sum_sub_distrib]
  simp only [one_div, add_comm (1 : ℂ), add_comm (x : ℂ)]
  ring
 have hs := vhn (w := (x : ℂ)) (by simpa using hx)
 rw [hs.hasSum_iff_tendsto_nat]
 simp_rw [hpart]
 rw [show nhds (digamma (x : ℂ) - digamma 1) = nhds (digamma (x : ℂ) - digamma 1 - 0) by simp]
 refine tendsto_const_nhds.sub ?_
 have : (fun n : ℕ => digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) =
   fun n : ℕ => ((rD (x + n) - rD (1 + n) : ℝ) : ℂ) := by
  funext n
  rw [vgL (by positivity), vgL (by positivity)]
  push_cast; ring
 rw [this, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
 exact (Complex.continuous_ofReal.tendsto _).comp (viV hx0)
lemma vfL :
  DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} := by
 have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
 have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -m := fun z hz m h => by
  rw [h] at hz; simp at hz; linarith [m.cast_nonneg (α := ℝ)]
 have hG : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
  (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
 have : digamma = fun z => deriv Gamma z / Gamma z := by
  funext z; rw [digamma_def, logDeriv_apply]
 rw [this]
 exact (hG.deriv ho).div hG (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)
lemma vft (R : ℝ) :
    DifferentiableOn ℂ (fun z => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)))
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 R) := by
  refine differentiableOn_tsum_of_summable_norm (u := fun k : ℕ => 2 * (R + 1) / ((k : ℝ) + 1) ^ 2)
    (F := fun (k : ℕ) (z : ℂ) => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))
    ?_ (fun k => ?_) ((isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball)
    (fun k z hz => ?_)
  · exact (veM.mul_left (2 * (R + 1))).congr (fun k => by ring)
  · intro z hz
    have hkz : (k : ℂ) + z ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      have h2 : 1 / 2 < z.re := hz.1
      simp only [add_re, natCast_re, zero_re] at h1
      linarith [k.cast_nonneg (α := ℝ)]
    have : DifferentiableAt ℂ (fun z : ℂ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) z := by
      fun_prop (disch := exact hkz)
    exact this.differentiableWithinAt
  · refine (norm_term_le hz.1 k).trans ?_
    have hz2 : ‖z‖ < R := by simpa using hz.2
    gcongr
lemma vhW :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), (digamma z - digamma 1) =
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) := by
  let u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ))
      rw [add_zero] at this
      have := (Complex.continuous_ofReal.tendsto _).comp this
      simpa [u, Function.comp_def] using this
    · simp only [mem_compl_iff, mem_singleton_iff, u]
      intro h
      have h1 := congrArg Complex.re h
      simp only [ofReal_re, one_re] at h1
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall (fun n => ?_))
  have hx : 1 / 2 < (1 + 1 / ((n : ℝ) + 1)) := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact (vhr hx).tsum_eq.symm
theorem vgP {w : ℂ} (hw : 1 / 2 < w.re) :
  HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) (digamma w - digamma 1) := by
 have hUo : IsOpen ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
  (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
 have hUc : IsPreconnected ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
  ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
 have hF : DifferentiableOn ℂ (fun z => digamma z - digamma 1)
   ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := by
  refine (vfL.mono (fun z hz => ?_)).sub_const _
  have h : 1 / 2 < z.re := hz.1
  show 0 < z.re
  linarith
 have h1U : (1 : ℂ) ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
  ⟨by norm_num, by rw [Metric.mem_ball, dist_zero_right, norm_one]; linarith [norm_nonneg w]⟩
 have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
  ((vft _).analyticOnNhd hUo) hUc h1U vhW
 have hwU : w ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := ⟨hw, by simp⟩
 have := heq hwU
 simp only at this
 rw [this]
 exact (vhn hw).hasSum
end Erdos985.Analytic.BoundsAux
end
section
open Filter Topology
namespace Erdos985.Analytic.BoundsAux
noncomputable def tau (x : ℝ) (m : ℕ) : ℝ :=
 if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x)
 else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x)
 else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))
lemma vkw (y p M K : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ y) (hK : 0 ≤ K) (hM : 2 * (K + 1) ≤ M) :
    -(1 / 2) * (1 / ((K + 1) * (K + 2))) ≤
      (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1)) := by
  have h1 : M - 1 ≠ 0 := by intro h; linarith
  have h2 : M ≠ 0 := by intro h; linarith
  have h3 : 2 + M ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1))
      - -(1 / 2) * (1 / ((K + 1) * (K + 2))) =
      ((M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) + (K + 1) * (K + 2) * (4 * M - 4) * y
        + 2 * (K + 1) * (K + 2) * (M + 2) * (y - p)) / (2 * M * (K + 1) * (K + 2) * (M - 1) * (2 + M)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  have hy : 0 ≤ y := hp0.trans hp
  apply div_nonneg
  · have : 0 ≤ M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K := by nlinarith
    have : 0 ≤ (M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) := mul_nonneg (by linarith) this
    have : 0 ≤ (K + 1) * (K + 2) * (4 * M - 4) * y :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) hy
    have : 0 ≤ 2 * (K + 1) * (K + 2) * (M + 2) * (y - p) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    linarith
  · have : 0 ≤ M - 1 := by linarith
    have : 0 ≤ M := by linarith
    positivity
lemma vki (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
  (1 - y) / (2 + 2 * (K + 1)) - (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1))
   - y / (2 * (K + 1) - 1)) ≤ (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) := by
 have h1 : 2 * K + 1 ≠ 0 := by intro h; linarith
 have h1' : 2 * (K + 1) - 1 ≠ 0 := by intro h; linarith
 have h4 : K + 1 ≠ 0 := by intro h; linarith
 have h5 : K + 2 ≠ 0 := by intro h; linarith
 have e : (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + 2 * (K + 1)) -
   (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1)) - y / (2 * (K + 1) - 1))) =
   (K * p + 3 * K * y + 2 * p) / (2 * (K + 1) * (K + 2) * (2 * K + 1)) := by
  field_simp
  ring
 rw [← sub_nonneg, e]
 positivity
lemma vkr (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
  (1 - y) / (2 + (2 * (K + 1) + 1)) - (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1))
   + 1 / (2 * (K + 1) + 1) - y / (2 * (K + 1) + 1 - 1))
   ≤ 3 * y / 4 * (1 / ((K + 1) * (K + 2))) := by
 have h1 : 2 * K + 3 ≠ 0 := by intro h; linarith
 have h2 : 2 * K + 5 ≠ 0 := by intro h; linarith
 have h4 : K + 1 ≠ 0 := by intro h; linarith
 have h5 : K + 2 ≠ 0 := by intro h; linarith
 have e : 3 * y / 4 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + (2 * (K + 1) + 1)) -
   (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1)) + 1 / (2 * (K + 1) + 1)
    - y / (2 * (K + 1) + 1 - 1))) =
   (4 * K ^ 2 * p + 8 * K ^ 2 + 18 * K * p + 6 * K * y + 24 * K + 20 * p + 9 * y + 16) /
    (4 * (K + 1) * (K + 2) * (2 * K + 3) * (2 * K + 5)) := by
  field_simp
  ring
 rw [← sub_nonneg, e]
 positivity
lemma vkg (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (m : ℕ) (hm : 2 * (k + 1) ≤ m) :
  -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ tau x m := by
 have hm0 : m ≠ 0 := by omega
 have hm1 : m ≠ 1 := by omega
 simp only [tau, hm0, hm1, ite_false]
 have hy0 : 0 < 1 / x := by positivity
 have hy1 : 1 / x ≤ 1 := by rw [div_le_one (by linarith)]; exact hx
 exact vkw _ _ _ _ (by positivity) (pow_le_of_le_one hy0.le hy1 hm0) (Nat.cast_nonneg k)
  (by exact_mod_cast hm)
lemma vid (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
  tau x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
 have hm0 : 2 * (k + 1) ≠ 0 := by omega
 have hm1 : 2 * (k + 1) ≠ 1 := by omega
 simp only [tau, hm0, hm1, ite_false]
 have hy0 : 0 < 1 / x := by positivity
 have := vki (1 / x) ((1 / x) ^ (2 * (k + 1))) k (by positivity) hy0.le (Nat.cast_nonneg k)
 push_cast
 exact this
lemma vjU (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
  tau x (2 * (k + 1) + 1) ≤ 3 * (1 / x) / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
 have hm0 : 2 * (k + 1) + 1 ≠ 0 := by omega
 have hm1 : 2 * (k + 1) + 1 ≠ 1 := by omega
 simp only [tau, hm0, hm1, ite_false]
 have hy0 : 0 < 1 / x := by positivity
 have := vkr (1 / x) ((1 / x) ^ (2 * (k + 1) + 1)) k (by positivity) hy0.le
  (Nat.cast_nonneg k)
 push_cast
 exact this
lemma vdc : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) 1 := by
 rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
 have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
   1 - 1 / ((n : ℝ) + 1) := by
  intro n
  have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + 1)) n
  simp only [Nat.cast_zero, zero_add, div_one, Nat.cast_add, Nat.cast_one] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp
  ring
 simp_rw [hps]
 have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ)
 simpa using this
theorem viR (x : ℝ) (hx : 1 ≤ x) (a : ℕ) (ha : a ≤ 1) :
    Summable (fun k : ℕ => tau x (2 * k + a)) ∧
      |∑' k : ℕ, tau x (2 * k + a)| ≤ Real.log x + 1 := by
  set y := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; exact hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL1 : 1 - y ≤ Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < x)
    rwa [hy, one_div]
  set u : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  set B : ℝ := if a = 0 then (3 * y - 1) / 2 else 3 * y / 4 with hB
  have hup : ∀ k : ℕ, tau x (2 * (k + 1) + a) ≤ B * u k := by
    intro k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · simp only [hB, ↓reduceIte]; exact vid x hx k
    · simp only [hB, one_ne_zero, ite_false]; exact vjU x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * u k ≤ tau x (2 * (k + 1) + a) :=
    fun k => vkg x hx k _ (by omega)
  have hB1 : |B| ≤ 1 := by
    rw [hB]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hg : Summable (fun k : ℕ => tau x (2 * (k + 1) + a)) := by
    refine Summable.of_norm_bounded vdc.summable (fun k => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hup k
    have h2 := hlo k
    have h3 : B * u k ≤ u k := by
      have := (abs_le.mp hB1).2
      nlinarith [hu0 k]
    constructor <;> nlinarith [hu0 k]
  have hS : Summable (fun k : ℕ => tau x (2 * k + a)) := by
    exact (summable_nat_add_iff 1).mp hg
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have e1 : (fun k : ℕ => tau x (2 * (k + 1) + a)) = fun k : ℕ => tau x (2 * (k + 1) + a) := rfl
  have hle : ∑' k : ℕ, tau x (2 * (k + 1) + a) ≤ B := by
    have := Summable.tsum_le_tsum hup hg (vdc.summable.mul_left B)
    rwa [tsum_mul_left, vdc.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, tau x (2 * (k + 1) + a) := by
    have := Summable.tsum_le_tsum hlo (vdc.summable.mul_left _) hg
    rwa [tsum_mul_left, vdc.tsum_eq, mul_one] at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · simp only [hB, ite_true] at hle
    simp only [mul_zero, add_zero, tau, ite_true] at hle hge ⊢
    rw [← hy] at *
    rw [abs_le]; constructor <;> linarith
  · simp only [hB, one_ne_zero, ite_false] at hle
    simp only [mul_zero, zero_add, tau, ite_true, one_ne_zero, ite_false] at hle hge ⊢
    rw [← hy] at *
    have hyL : y * Real.log x ≤ Real.log x := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hy0.le hL]
end Erdos985.Analytic.BoundsAux
end
section
open Complex MeasureTheory Filter Topology
namespace Erdos985.Analytic.BoundsAux
lemma vgW {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + vbP χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + vbP χ : ℕ) : ℂ)))
      (vba χ s - vba χ 2) := by
  have ha0 : (0 : ℝ) ≤ (vbP χ : ℝ) := Nat.cast_nonneg _
  have hw : 1 / 2 < ((s + (vbP χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have hw2 : 1 / 2 < ((2 + (vbP χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have h := ((vgP hw).sub (vgP hw2)).mul_left (1 / 2)
  unfold vba
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  · funext k
    have hh (u z : ℂ) : 1 / 2 * (1 / (u + z / 2)) = 1 / (2 * u + z) := by
      rw [one_div_mul_one_div]; congr 1; ring
    rw [show (1 / 2 : ℂ) * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (s + (vbP χ : ℂ)) / 2)
        - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (2 + (vbP χ : ℂ)) / 2)))
        = 1 / 2 * (1 / ((k : ℂ) + (2 + (vbP χ : ℂ)) / 2))
          - 1 / 2 * (1 / ((k : ℂ) + (s + (vbP χ : ℂ)) / 2)) by ring, hh, hh]
    push_cast
    congr 1 <;> congr 1 <;> ring
  · ring
noncomputable def vdD (x : ℕ) (m : ℕ) (t : ℝ) : ℂ :=
 (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I)
  / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
lemma vjF (x m : ℕ) (t : ℝ) : vdD x m t =
  1 / (2 + (m : ℂ)) * ((x : ℂ) ^ ((2 : ℂ) + t * I) /
   (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
  - (x : ℂ) ^ ((2 : ℂ) + t * I) /
   (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) := by
 have hm : (0 : ℝ) ≤ m := m.cast_nonneg
 have h0 : (2 : ℂ) + t * I ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this
 have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith
 have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith
 have h3 : (2 : ℂ) + m ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith
 unfold vdD
 rw [sub_neg_eq_add]
 field_simp
lemma hw_m (m : ℕ) : (-(m : ℂ)).re < 2 := by
 simp only [neg_re, natCast_re]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
lemma vfG (x : ℕ) (hx : 1 ≤ x) (m : ℕ) : Integrable (vdD x m) := by
 have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
 have hK := PerronAux.vdP (x := (x : ℝ)) (c := 2) hx0 two_pos
 have hP := PerronAux.vcr (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
 simp only [ofReal_natCast, ofReal_ofNat] at hK hP
 rw [show vdD x m = _ from funext (vjF x m)]
 exact (hK.const_mul _).sub hP
lemma viQ (x : ℕ) (hx : 1 ≤ x) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, vdD x m t = (tau x m : ℂ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hK := PerronAux.vdP (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.vcr (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  have hC := vjl (x : ℝ) 2 hx0 two_pos
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP hC
  rw [show vdD x m = _ from funext (vjF x m), integral_sub (hK.const_mul _) hP,
    integral_const_mul, mul_sub, mul_left_comm, hC,
    max_eq_right (show (0 : ℝ) ≤ 1 - 1 / (x : ℝ) by
      rw [sub_nonneg, div_le_one hx0]; exact hx1)]
  rcases m with _ | _ | m
  · have hR := veW (x : ℝ) 2 hx1 two_pos (-((0 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hR := vgw (x : ℝ) 2 hx1 two_pos (-((0 + 1 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte, zero_add, one_ne_zero]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hM : (2 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hw0 : -((m + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hw1 : -((m + 1 + 1 : ℕ) : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR := vfd (x : ℝ) 2 hx1 two_pos _ (hw_m (m + 1 + 1)) hw0 hw1
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    have h0 : m + 1 + 1 ≠ 0 := by omega
    have h1 : m + 1 + 1 ≠ 1 := by omega
    simp only [tau, h0, h1, ↓reduceIte]
    rw [cpow_neg, cpow_natCast, cpow_neg_one]
    push_cast
    have e1 : (m : ℂ) + 1 + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e2 : (m : ℂ) + 1 + 1 - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e3 : (2 : ℂ) + ((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e4 : -((m : ℂ) + 1 + 1) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e5 : 1 + -((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e6 : (x : ℂ) ^ (m + 1 + 1) ≠ 0 := pow_ne_zero _ hxC
    simp only [one_div, inv_pow]
    field_simp
    ring
lemma vjo (x m : ℕ) (t : ℝ) :
    ‖vdD x m t‖ ≤ 1 / (2 + m) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : vdD x m t = (((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)) * (1 / (2 + (m : ℂ))) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))) := by
    unfold vdD
    rw [sub_neg_eq_add]
    field_simp
    ring
  rw [e, norm_mul, norm_mul]
  have hq : ‖((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr h0)]
    have : (2 : ℂ) + t * I - 2 = t * I := by ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.abs_im_le_norm ((2 : ℂ) + t * I)
    simpa using this
  have hn : ‖1 / (2 + (m : ℂ))‖ = 1 / (2 + m) := by
    rw [norm_div, norm_one]
    congr 1
    exact_mod_cast Complex.norm_natCast (2 + m)
  rw [hn]
  have := norm_nonneg ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1)))
  have : 0 ≤ 1 / (2 + (m : ℝ)) := by positivity
  calc _ ≤ 1 * (1 / (2 + (m : ℝ))) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by gcongr
    _ = _ := by ring
lemma vka (k m : ℕ) (hkm : k ≤ m) :
  (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
 have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
 have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
 have e : ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) = ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1) := by
  rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + (-1) by norm_num, Real.rpow_add hk, Real.rpow_neg_one]
  ring
 rw [e]
 apply div_le_div₀ (by positivity) _ hk (by linarith)
 exact Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)
lemma viD : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
 have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
 simpa using this
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open BoundsAux
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.PrincipalAux
open Complex
theorem vby {s : ℂ} (hs : 1 ≤ s.re) :
  completedRiemannZeta s ≠ 0 := by
 have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
 intro h
 apply riemannZeta_ne_zero_of_one_le_re hs
 rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
theorem vfC : van 1 = 1 := by simp [van]
theorem vbO {ρ : ℂ} (hρ : van ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, vds] at hρ; exact one_ne_zero hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, vfC] at hρ; exact one_ne_zero hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [vgq hρ0 hρ1] at hρ
    rcases mul_eq_zero.mp hρ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.mp h) hρ1
    · exact h
  constructor
  · by_contra h
    push Not at h
    apply vby (s := 1 - ρ) (by simp; linarith)
    rw [completedRiemannZeta_one_sub, hΛ]
  · by_contra h
    push Not at h
    exact vby h hΛ
theorem veL {ρ : ℂ} (hρ : van ρ = 0) : analyticOrderNatAt van ρ ≠ 0 := by
  have han : AnalyticOnNhd ℂ van Set.univ :=
    vbd.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt van 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr (by rw [vds]; exact one_ne_zero)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ ρ) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h hρ
theorem vew : Countable {ρ : ℂ // van ρ = 0} := by
 have hs := (vej vbd (by rw [vds]; exact one_ne_zero)
  vfp).1 1 one_pos
 rw [← Set.countable_univ_iff]
 convert hs.countable_support
 symm
 rw [Function.support_eq_univ]
 intro ρ
 have hm := veL ρ.2
 have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (vbO ρ.2).1.ne' (by simp [h])
 have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
 positivity
theorem vhS (s : ℂ) :
  vba (1 : DirichletCharacter ℂ 1) s
   = -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2) := by
 simp [vba, vbP, DirichletCharacter.Even, MulChar.one_apply (isUnit_of_subsingleton _)]
theorem vef {s : ℂ} (hs : 1 < s.re) :
  deriv riemannZeta s / riemannZeta s
   = deriv van s / van s - 1 / s - 1 / (s - 1)
     - vba (1 : DirichletCharacter ℂ 1) s := by
 have hs0 : 0 < s.re := by linarith
 have hne0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
 have hne1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
 have hne1' : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
 have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
 have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
 have hev : van =ᶠ[nhds s] fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
   (show s ∈ {w : ℂ | 1 < w.re} from hs)] with w hw
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
  rw [vgq hw0 hw1, riemannZeta_def_of_ne_zero hw0,
   mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by linarith))]
 have hp : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
  (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
 have hd := hp.fun_mul ((StepAAux.hasDerivAt_Gammaℝ hs0).fun_mul
  (differentiableAt_riemannZeta hne1).hasDerivAt)
 rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds, vhS]
 field_simp
 ring
end Erdos985.Analytic.PrincipalAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory IdentityAux
theorem vbO {ρ : ℂ} (hρ : van ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
 PrincipalAux.vbO hρ
theorem vgB (x : ℕ) (hx : 1 ≤ x) :
    (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (∑' ρ : {ρ : ℂ // van ρ = 0}, (analyticOrderNatAt van ρ : ℂ) * vdg x ρ)
        + vbn (1 : DirichletCharacter ℂ 1) x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv riemannZeta 2 / riemannZeta 2) := by
  classical
  set G := vba (1 : DirichletCharacter ℂ 1) with hG
  set D : ℂ → ℂ := fun z => deriv van z / van z with hD
  set m : {ρ : ℂ // van ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt van ρ : ℂ) with hm
  set c2 : ℂ := deriv riemannZeta 2 / riemannZeta 2 with hc2
  have := PrincipalAux.vew
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ van := vbd
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → van z ≠ 0 := fun z hz h => by
    linarith [(vbO h).2]
  obtain ⟨hsum_ε, b, hb⟩ := vej hΛd (by rw [vds]; exact one_ne_zero)
    vfp
  have hzre : ∀ ρ : {ρ : ℂ // van ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => vbO ρ.2
  let F : {ρ : ℂ // van ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * vbH x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (veZ hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := vfD
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt van ρ : ℝ) * ∫ t, ‖vbH x ρ t‖
        ≤ (analyticOrderNatAt van ρ : ℝ) *
            (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I) - D 2) * qad x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (qad x t)
    convert this using 1
    all_goals try with_reducible_and_instances rfl
    · funext ρ
      simp only [F, m, vbH]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv van) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * qad x t :=
    vha
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (vbV hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * qad x t
      = ∑' ρ : {ρ : ℂ // van ρ = 0}, m ρ * (-(2 * Real.pi) * vdg x ρ) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * qad x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, via x hx (by linarith [hzre ρ]) hρ0 hρ1]
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.viM a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - 1 / z - 1 / (z - 1) - G z) := fun z hz => by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
    change LSeries a z = _ at h1
    rw [h1, neg_div, PrincipalAux.vef hz]
  have hc2' : c2 = D 2 - 1 / 2 - 1 / (2 - 1) - G 2 :=
    PrincipalAux.vef (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * qad x t := fun t => by
    simp only [hH, qad, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) := by
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num))) ?_
      have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
      rw [this]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) :=
      (LSeries_differentiableOn a).continuousOn.comp_continuous hs_cont
        (fun t => by simp only [Set.mem_ofPred_eq, hsre]; exact_mod_cast hab)
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * qad x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((vbV hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (vbV hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  set P0 : ℝ → ℂ := fun t => ((x : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
    (((2 : ℂ) + t * I - 0) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hP0
  have hP0_int : Integrable P0 := by
    have := vdz (x : ℝ) 2 hx0 two_pos 0 (by simp)
    simp only [ofReal_ofNat] at this
    exact this
  have hP0_integral : ∫ t, P0 t = 2 * Real.pi * ((Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ)) := by
    have h := veW (x : ℝ) 2 hx1 two_pos 0 rfl
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [hP0]
  have hR1_int : Integrable (vcB x 1) := vdK hx0 (by norm_num)
  have hR1_integral : ∫ t, vcB x 1 t
      = 2 * Real.pi * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)) - 1 / 1 + (x : ℂ) ^ (-1 : ℂ) / (1 + 1)) := by
    have h := vfd (x : ℝ) 2 hx1 two_pos 1 (by norm_num) one_ne_zero (by norm_num)
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [vcB]
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * qad x t - P0 t - vcB x 1 t
          + (c2 + 3 / 2) * qad x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    have h0 := vhk t
    have h1 := veD t
    have h2 := vfw (ρ := 1) (by norm_num) t
    rw [hH_eq, hLS _ hz, hc2']
    simp only [qad, vcB, hP0, ofReal_natCast, sub_zero]
    field_simp
    ring
  have hgamma : vbn (1 : DirichletCharacter ℂ 1) x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * qad x t)
        - (∫ t, P0 t) - (∫ t, vcB x 1 t) + (c2 + 3 / 2) * ∫ t, qad x t) := by
    unfold vbn
    rw [← hG, hF2, integral_add _ ((vbV hx0).const_mul _),
      integral_sub _ hR1_int, integral_sub _ hP0_int, integral_add hH_int hF1_int,
      integral_const_mul]
    · exact hH_int.add hF1_int
    · exact (hH_int.add hF1_int).sub hP0_int
    · exact ((hH_int.add hF1_int).sub hP0_int).sub hR1_int
  have hbach : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    push_cast
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := vhh hx1
  have htsum : ∑' ρ : {ρ : ℂ // van ρ = 0}, m ρ * (-(2 * Real.pi) * vdg x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // van ρ = 0}, m ρ * vdg x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK, hP0_integral, hR1_integral]
  simp only [ofReal_natCast, cpow_one, cpow_neg_one]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  field_simp
  ring
end Erdos985.Analytic
end
section
open Complex MeasureTheory Filter Topology ArithmeticFunction
namespace Erdos985.Analytic.PrincipalAux
open BoundsAux
theorem vhw (x : ℝ) (hx : 1 ≤ x) :
  Summable (fun k : ℕ => tau x (2 * k)) ∧
   1 - 3 / (2 * x) ≤ ∑' k : ℕ, tau x (2 * k) + Real.log x ∧
   ∑' k : ℕ, tau x (2 * k) + Real.log x ≤ 1 := by
 have hup : ∀ k : ℕ, tau x (2 * (k + 1)) ≤
   (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := fun k =>
  vid x hx k
 have hlo : ∀ k : ℕ, -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ tau x (2 * (k + 1)) :=
  fun k => vkg x hx k (2 * (k + 1)) le_rfl
 have hS : Summable (fun k : ℕ => tau x (2 * k)) := by
  simpa using (viR x hx 0 (by norm_num)).1
 have hg : Summable (fun k : ℕ => tau x (2 * (k + 1))) :=
  (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k)) 1).mpr hS
 refine ⟨hS, ?_⟩
 rw [hS.tsum_eq_zero_add]
 have hle : ∑' k : ℕ, tau x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 := by
  have := Summable.tsum_le_tsum hup hg (vdc.summable.mul_left _)
  rwa [tsum_mul_left, vdc.tsum_eq, mul_one] at this
 have hge : -(1 / 2) ≤ ∑' k : ℕ, tau x (2 * (k + 1)) := by
  have := Summable.tsum_le_tsum hlo (vdc.summable.mul_left _) hg
  rwa [tsum_mul_left, vdc.tsum_eq, mul_one] at this
 have h0 : tau x (2 * 0) = (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) := by simp [tau]
 rw [h0]
 have e : 3 / (2 * x) = 3 / 2 * (1 / x) := by field_simp
 rw [e]
 constructor <;> linarith
theorem vgC {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ)
    (hx : 1 ≤ x) :
    vbn χ x = ((∑' k : ℕ, tau x (2 * k + vbP χ) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := vcS (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (vba χ (2 + t * I) - vba χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, vdD x (2 * k + vbP χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact (((vgW χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖vdD x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖vdD x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (vfG x hx m).norm (hQi.norm.const_mul _)
            (fun t => vjo x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖vdD x (2 * k + vbP χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (viD.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact vka k _ (by omega)
  have hgp : vbn χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, vdD x (2 * k + vbP χ) t := by
    unfold vbn
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => vfG x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [viQ x hx]
  rw [← Complex.ofReal_tsum]
lemma vkc : vbP (1 : DirichletCharacter ℂ 1) = 0 := by
 simp [vbP, DirichletCharacter.Even, MulChar.one_apply (isUnit_of_subsingleton _)]
theorem vhe (x : ℕ) (hx : 1 ≤ x) :
  (vbn (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
  1 - 3 / (2 * (x : ℝ)) ≤ (vbn (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
  (vbn (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
 rw [vgC _ x hx, vkc]
 simp only [add_zero, Complex.ofReal_im, Complex.ofReal_re, true_and]
 have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
 exact (vhw x hx1).2
theorem vfU :
  (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
  -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧
   (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
 have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div re2
 have e : deriv riemannZeta 2 / riemannZeta 2
   = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [← vfg (fun n => (Λ n : ℝ)), key]; ring
 rw [e]
 simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
  true_and]
 have hS := vkC
 have h0 : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
  tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
 constructor <;> linarith
end Erdos985.Analytic.PrincipalAux
end
section
open Real Filter Topology
namespace Erdos985.Analytic.PrincipalAux
lemma vhM {a : ℝ} (ha : 0 < a) :
  2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 ≤ log (1 + a⁻¹) := by
 have h := hasSum_log_one_add_inv ha
 have hle := sum_le_hasSum (Finset.range 2) (fun k _ => by positivity) h
 simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
 norm_num at hle
 simpa [one_div, inv_pow] using hle
lemma vkh {a : ℝ} (ha : 0 < a) :
  1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2)
   ≤ log (1 + a⁻¹) := by
 refine le_trans ?_ (vhM ha)
 rw [← sub_nonneg]
 have e : 2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 -
   (1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2))
   = (4 * a ^ 2 + 2 * a + 1) * (4 * a ^ 2 + 6 * a + 3) /
    (24 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1) ^ 3) := by
  field_simp
  ring
 rw [e]
 positivity
noncomputable def vhD (m : ℕ) : ℝ :=
 (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)
  + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2
lemma vjM : Antitone vhD := by
 refine antitone_nat_of_succ_le (fun m => ?_)
 have ha : (0 : ℝ) < (m + 1 : ℕ) := by positivity
 have key := vkh ha
 have hlog : log (((m + 1 + 1 : ℕ) : ℝ)) =
   log ((m + 1 : ℕ) : ℝ) + log (1 + ((m + 1 : ℕ) : ℝ)⁻¹) := by
  rw [← log_mul ha.ne' (by positivity)]
  congr 1
  field_simp
  push_cast
  ring
 simp only [vhD]
 rw [hlog, harmonic_succ (m + 1)]
 push_cast at key ⊢
 have : (1 : ℝ) / (2 * (m + 1)) + 1 / (2 * (m + 1 + 1)) + 1 / (8 * (m + 1 + 1) ^ 2)
   - 1 / (8 * (m + 1) ^ 2) =
   ((m : ℝ) + 1 + 1)⁻¹ + 1 / 2 / (m + 1) - 1 / 2 / (m + 1 + 1)
    + 1 / 8 / (m + 1 + 1) ^ 2 - 1 / 8 / (m + 1) ^ 2 := by
  field_simp; ring
 linarith
lemma viT : Tendsto vhD atTop (𝓝 eulerMascheroniConstant) := by
 have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - (1 / 2) / n + (1 / 8) / (n : ℝ) ^ 2)
   atTop (𝓝 (eulerMascheroniConstant - 0 + 0)) := by
  refine (tendsto_harmonic_sub_log.sub (tendsto_const_div_atTop_nhds_zero_nat _)).add ?_
  have := (tendsto_const_div_atTop_nhds_zero_nat (1 / 8 : ℝ)).comp
   (tendsto_pow_atTop (α := ℕ) (n := 2) (by norm_num))
  refine this.congr (fun n => ?_)
  simp
 rw [sub_zero, add_zero] at h1
 exact (tendsto_add_atTop_iff_nat 1).mpr h1
lemma vkj (m : ℕ) : eulerMascheroniConstant ≤ vhD m :=
 vjM.le_of_tendsto viT m
lemma vfh : eulerMascheroniConstant < 0.5774 := by
 refine lt_of_le_of_lt (vkj 15) ?_
 have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
  norm_num [harmonic, Finset.sum_range_succ]
 have hl : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
  rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
 simp only [vhD]
 norm_num only [Nat.reduceAdd] at hH hl ⊢
 rw [hH, hl]
 linarith [log_two_gt_d9]
lemma vhg : (1.144 : ℝ) < Real.log Real.pi := by
 rw [Real.lt_log_iff_exp_lt Real.pi_pos]
 have h1 : Real.exp 1.144 = Real.exp 1 * Real.exp 0.144 := by
  rw [← Real.exp_add]; norm_num
 have h2 := Real.exp_bound' (x := 0.144) (by norm_num) (by norm_num) (n := 4) (by norm_num)
 simp [Finset.sum_range_succ, Nat.factorial] at h2
 rw [h1]
 have h3 := Real.exp_one_lt_d9
 have h4 := Real.pi_gt_d4
 have h5 : 0 < Real.exp 0.144 := Real.exp_pos _
 nlinarith
lemma vfX : 2 + eulerMascheroniConstant - Real.log (4 * Real.pi) < 1 / 20 := by
 rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
 have := vfh
 have := vhg
 have := log_two_gt_d9
 push_cast
 linarith
end Erdos985.Analytic.PrincipalAux
end
section
open Complex
namespace Erdos985.Analytic.PrincipalAux
theorem vdU (s : ℂ) : van (1 - s) = van s := by
 simp only [van, completedRiemannZeta₀_one_sub]
 ring
theorem vfu (s : ℂ) :
  HasDerivAt van ((1 * (s - 1) + s * 1) * completedRiemannZeta₀ s
   + s * (s - 1) * deriv completedRiemannZeta₀ s) s := by
 have h := (((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).mul
  (differentiable_completedZeta₀ s).hasDerivAt).add_const 1
 exact h
theorem vhT : deriv van 0 = -completedRiemannZeta₀ 0 := by
 rw [(vfu 0).deriv]; ring
theorem vip : deriv van 1 = completedRiemannZeta₀ 1 := by
 rw [(vfu 1).deriv]; ring
theorem veo :
  (2 * completedRiemannZeta₀ 1).re = 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
 rw [completedRiemannZeta₀_one]
 have e : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
  rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
 rw [e]
 simp
 ring
end Erdos985.Analytic.PrincipalAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction
theorem veX (x : ℕ) (hx : 1 ≤ x) :
  (vbn (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
  1 - 3 / (2 * (x : ℝ)) ≤ (vbn (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
  (vbn (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
 exact PrincipalAux.vhe x hx
theorem veh :
  (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
  -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧ (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
 exact PrincipalAux.vfU
end Erdos985.Analytic
end
section
namespace Schoenfeld
open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux ArithmeticFunction
abbrev qQ := {ρ : ℂ // van ρ = 0}
instance : Countable qQ := vew
noncomputable def mult (ρ : qQ) : ℝ := (analyticOrderNatAt van (ρ : ℂ) : ℝ)
lemma vat (ρ : qQ) : 0 ≤ mult ρ := Nat.cast_nonneg _
lemma one_le_mult (ρ : qQ) : 1 ≤ mult ρ := by
 unfold mult
 exact_mod_cast Nat.one_le_iff_ne_zero.mpr (veL ρ.2)
theorem vdB (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) : van s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [vfC] at h; norm_num at h
  rw [vgq hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s hζ htriv hs1
  linarith
theorem vbK (hRH : RiemannHypothesis) (ρ : qQ) : (ρ : ℂ).re = 1 / 2 := by
 have h1 : ¬ 1 / 2 < (ρ : ℂ).re := fun h => vdB hRH h ρ.2
 have h2 : ¬ 1 / 2 < (1 - (ρ : ℂ)).re := fun h =>
  vdB hRH h (by rw [vdU]; exact ρ.2)
 simp only [sub_re, one_re] at h2
 linarith
lemma vfM {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
 rw [← normSq_eq_norm_sq, normSq_apply, hρ]; ring
lemma vjD {ρ : ℂ} (hρ : ρ.re = 1 / 2) : (1 / ρ).re = 1 / 2 / ‖ρ‖ ^ 2 := by
 rw [one_div, inv_re, normSq_eq_norm_sq, hρ]
theorem vgV (hRH : RiemannHypothesis) :
  HasSum (fun ρ : qQ => mult ρ / ‖(ρ : ℂ)‖ ^ 2)
   (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) := by
 have hx0 : van 0 ≠ 0 := by rw [vds]; norm_num
 have hx1 : van 1 ≠ 0 := by rw [vfC]; norm_num
 obtain ⟨-, b, H⟩ := vej vbd hx0 vfp
 obtain ⟨-, e0⟩ := H 0 hx0
 obtain ⟨s1, e1⟩ := H 1 hx1
 have hz : ∀ ρ : qQ, (analyticOrderNatAt van ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
  intro ρ; simp
 simp only [hz, tsum_zero, add_zero, vhT, vds, div_one] at e0
 rw [vip, vfC, div_one] at e1
 set T := ∑' ρ : qQ, (analyticOrderNatAt van ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ) with hT
 have hTv : T = 2 * completedRiemannZeta₀ 1 := by
  have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
   rw [← completedRiemannZeta₀_one_sub]; norm_num
  rw [h01] at e0
  linear_combination e0 - e1
 have hre := Complex.reCLM.hasSum s1.hasSum
 rw [← hT, hTv] at hre
 simp only [Complex.reCLM_apply, veo] at hre
 refine hre.congr_fun fun ρ => ?_
 have hρ := vbK hRH ρ
 have h1 : (1 - (ρ : ℂ)) = (starRingEnd ℂ) ρ := by
  apply Complex.ext <;> simp [hρ]; norm_num
 rw [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re, h1, one_div,
  inv_re, normSq_conj, vjD hρ, conj_re, normSq_eq_norm_sq, hρ, mult]
 ring
theorem vbg (hRH : RiemannHypothesis) :
  Summable (fun ρ : qQ => mult ρ / ‖(ρ : ℂ)‖ ^ 2) := (vgV hRH).summable
theorem vis (hRH : RiemannHypothesis) :
  ∑' ρ : qQ, mult ρ / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 := by
 rw [(vgV hRH).tsum_eq]; exact vfX.le
theorem vcn (hRH : RiemannHypothesis) (ρ : qQ) : 20 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
 have hpos : 0 < ‖(ρ : ℂ)‖ ^ 2 := by
  have : (ρ : ℂ) ≠ 0 := fun h => by have := vbK hRH ρ; rw [h] at this; norm_num at this
  positivity
 have h1 : mult ρ / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
  ((vbg hRH).le_tsum ρ fun j _ => div_nonneg (vat j) (sq_nonneg _)).trans
   (vis hRH)
 have h2 : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
  le_trans (div_le_div_of_nonneg_right (one_le_mult ρ) hpos.le) h1
 rw [div_le_div_iff₀ hpos (by norm_num)] at h2
 linarith
end Schoenfeld
end
section
namespace Schoenfeld
open Complex Real MeasureTheory
noncomputable def fmin (T : ℝ) (ρ : qQ) : ℝ :=
 mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2)
lemma vgt {T : ℝ} (hT : 0 ≤ T) (ρ : qQ) : 0 ≤ fmin T ρ :=
 mul_nonneg (vat ρ) (le_min (by positivity) (by positivity))
lemma vjy {T : ℝ} (_hT : 0 ≤ T) (ρ : qQ) :
    fmin T ρ ≤ T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  unfold fmin
  calc mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ mult ρ * (T / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (vat ρ)
    _ = _ := by ring
theorem vex (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) : Summable (fmin T) :=
 Summable.of_nonneg_of_le (vgt hT) (vjy hT) ((vbg hRH).mul_left T)
theorem viS (hRH : RiemannHypothesis) {T T' : ℝ} (hT : 0 ≤ T) (hTT : T ≤ T') :
  ∑' ρ, fmin T ρ ≤ ∑' ρ, fmin T' ρ := by
 refine (vex hRH hT).tsum_le_tsum (fun ρ => ?_) (vex hRH (hT.trans hTT))
 unfold fmin
 gcongr
 exact vat ρ
lemma vjv (hRH : RiemannHypothesis) (ρ : qQ) :
  ‖(ρ : ℂ)‖ ^ 2 / 2 ≤ (ρ : ℂ).im ^ 2 := by
 have h1 := vfM (vbK hRH ρ)
 have h2 := vcn hRH ρ
 linarith
lemma vkl (hRH : RiemannHypothesis) (ρ : qQ) : 0 < (ρ : ℂ).im ^ 2 := by
 have := vjv hRH ρ; have := vcn hRH ρ; linarith
end Schoenfeld
end
section
namespace Schoenfeld
open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux MeasureTheory Filter Topology
theorem vdp {ρ : ℂ} (hρ : 0 < ρ.im) :
  analyticOrderAt riemannZeta ρ = analyticOrderAt van ρ := by
 set V : Set ℂ := {s | 0 < s.im} with hV
 have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
 have hVn : V ∈ 𝓝 ρ := hVo.mem_nhds hρ
 have ne0 : ∀ s ∈ V, s ≠ 0 := fun s hs h => by simp [hV, h] at hs
 have ne1 : ∀ s ∈ V, s ≠ 1 := fun s hs h => by simp [hV, h] at hs
 have hG : ∀ s ∈ V, Gammaℝ s ≠ 0 := by
  intro s hs h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
  have : s.im = 0 := by rw [hn]; simp
  simp only [hV, Set.mem_ofPred_eq] at hs; linarith
 set u : ℂ → ℂ := fun s => (Gammaℝ s)⁻¹ / (s * (s - 1)) with hu
 have hud : DifferentiableOn ℂ u V := by
  intro s hs
  have h1 : s * (s - 1) ≠ 0 := mul_ne_zero (ne0 s hs) (sub_ne_zero.mpr (ne1 s hs))
  exact ((differentiable_Gammaℝ_inv s).div (by fun_prop) h1).differentiableWithinAt
 have hua : AnalyticAt ℂ u ρ := hud.analyticAt hVn
 have hxa : AnalyticAt ℂ van ρ := vbd.analyticAt ρ
 have hu0 : u ρ ≠ 0 := by
  have h1 : ρ * (ρ - 1) ≠ 0 := mul_ne_zero (ne0 ρ hρ) (sub_ne_zero.mpr (ne1 ρ hρ))
  simp only [hu]
  exact div_ne_zero (inv_ne_zero (hG ρ hρ)) h1
 have heq : riemannZeta =ᶠ[𝓝 ρ] u * van := by
  filter_upwards [hVn] with s hs
  have h0 := ne0 s hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne1 s hs)
  simp only [Pi.mul_apply, hu, vgq h0 (ne1 s hs), riemannZeta_def_of_ne_zero h0]
  field_simp
 rw [analyticOrderAt_congr heq, analyticOrderAt_mul hua hxa,
  hua.analyticOrderAt_eq_zero.mpr hu0, zero_add]
noncomputable def cnt (T : ℝ) : ℝ :=
 ∑' ρ : qQ, if 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T then mult ρ else 0
theorem vhc (T : ℝ) : vek T = cnt T := by
  classical
  unfold vek cnt
  have hsupp : (Function.support fun ρ : ℂ => if 0 < ρ.im ∧ ρ.im ≤ T then
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) ⊆ {ρ : ℂ | van ρ = 0} := by
    intro ρ hρ
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hρ
    obtain ⟨⟨him, -⟩, hne⟩ := hρ
    simp only [Set.mem_ofPred_eq]
    by_contra hx
    have : analyticOrderAt van ρ = 0 :=
      (vbd.analyticAt ρ).analyticOrderAt_eq_zero.mpr hx
    rw [vdp him, this] at hne
    simp at hne
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun ρ => ?_
  split_ifs with h
  · rw [vdp h.1, mult]; rfl
  · rfl
lemma vjC (ρ : qQ) :
  analyticOrderNatAt van (1 - (ρ : ℂ)) = analyticOrderNatAt van (ρ : ℂ) := by
 have hg : AnalyticAt ℂ (fun w : ℂ => 1 - w) (1 - (ρ : ℂ)) := by fun_prop
 have hd : deriv (fun w : ℂ => 1 - w) (1 - (ρ : ℂ)) ≠ 0 := by
  rw [deriv_const_sub, deriv_id'']; norm_num
 have h := analyticOrderAt_comp_of_deriv_ne_zero (f := van) hg hd
 have hc : (van ∘ fun w : ℂ => 1 - w) = van := funext fun w => vdU w
 rw [hc, sub_sub_cancel] at h
 simp only [analyticOrderNatAt, h]
def reflect : qQ ≃ qQ where
 toFun ρ := ⟨1 - (ρ : ℂ), by rw [vdU]; exact ρ.2⟩
 invFun ρ := ⟨1 - (ρ : ℂ), by rw [vdU]; exact ρ.2⟩
 left_inv ρ := Subtype.ext (by simp)
 right_inv ρ := Subtype.ext (by simp)
lemma vjE (ρ : qQ) : mult (reflect ρ) = mult ρ := by
 simp only [mult, reflect, Equiv.coe_fn_mk, vjC]
lemma viN (ρ : qQ) : ((reflect ρ : qQ) : ℂ).im = -(ρ : ℂ).im := by
 simp [reflect]
noncomputable def qbt (T u : ℝ) : ℝ := min (1 / u) (T / u ^ 2)
noncomputable def vaY (T : ℝ) (ρ : qQ) : ℝ :=
 if 0 < (ρ : ℂ).im then mult ρ * qbt T (ρ : ℂ).im else 0
noncomputable def qbu (T : ℝ) : ℝ := ∑' ρ, vaY T ρ
lemma viW {T : ℝ} (hT : 0 ≤ T) (ρ : qQ) : 0 ≤ vaY T ρ := by
  unfold vaY qbt
  split_ifs with h
  · exact mul_nonneg (vat ρ) (le_min (by positivity) (by positivity))
  · exact le_rfl
lemma vkb (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (ρ : qQ) :
    vaY T ρ ≤ 2 * T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have h1 := vjv hRH ρ
  have h2 := vcn hRH ρ
  have hm := vat ρ
  unfold vaY qbt
  split_ifs with h
  · calc mult ρ * min (1 / (ρ : ℂ).im) (T / (ρ : ℂ).im ^ 2) ≤ mult ρ * (T / (ρ : ℂ).im ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ ≤ mult ρ * (T / (‖(ρ : ℂ)‖ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hT (by positivity) h1) hm
      _ = 2 * T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by field_simp
  · positivity
theorem vfN (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
  Summable (vaY T) :=
 Summable.of_nonneg_of_le (viW hT) (vkb hRH hT)
  ((vbg hRH).mul_left (2 * T))
lemma vix (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (ρ : qQ) :
    fmin T ρ ≤ vaY T ρ + vaY T (reflect ρ) := by
  have hp := vkl hRH ρ
  have hne : (ρ : ℂ).im ≠ 0 := fun h => by rw [h] at hp; norm_num at hp
  set a := |(ρ : ℂ).im| with ha
  have ha0 : 0 < a := abs_pos.mpr hne
  have han : a ≤ ‖(ρ : ℂ)‖ := Complex.abs_im_le_norm _
  have key : fmin T ρ ≤ mult ρ * qbt T a := by
    unfold fmin qbt
    refine mul_le_mul_of_nonneg_left (min_le_min ?_ ?_) (vat ρ)
    · exact one_div_le_one_div_of_le ha0 han
    · exact div_le_div_of_nonneg_left hT (by positivity) (pow_le_pow_left₀ ha0.le han 2)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have e1 : vaY T ρ = 0 := by unfold vaY; rw [if_neg (by linarith)]
    have e2 : vaY T (reflect ρ) = mult ρ * qbt T a := by
      unfold vaY
      rw [viN, if_pos (by linarith), vjE, ha, abs_of_neg hneg]
    rw [e1, e2, zero_add]; exact key
  · have e1 : vaY T ρ = mult ρ * qbt T a := by
      unfold vaY; rw [if_pos hpos, ha, abs_of_pos hpos]
    have e2 : vaY T (reflect ρ) = 0 := by
      unfold vaY; rw [viN, if_neg (by linarith)]
    rw [e1, e2, add_zero]; exact key
theorem vgz (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    ∑' ρ, fmin T ρ ≤ 2 * qbu T := by
  have hs := vfN hRH hT
  have hs' : Summable fun ρ => vaY T (reflect ρ) := (reflect.summable_iff).mpr hs
  calc ∑' ρ, fmin T ρ ≤ ∑' ρ, (vaY T ρ + vaY T (reflect ρ)) :=
        (vex hRH hT).tsum_le_tsum (vix hRH hT) (hs.add hs')
    _ = qbu T + qbu T := by
        rw [hs.tsum_add hs', qbu, reflect.tsum_eq (vaY T)]
    _ = 2 * qbu T := by ring
end Schoenfeld
end
section
namespace Schoenfeld
open Real MeasureTheory Filter Topology Set
noncomputable def Nc (t : ℝ) : ℝ :=
 t / (2 * π) * (Real.log t - Real.log (2 * π) - 1) + 2.463 + 0.3 * Real.log t
noncomputable def P1 (t : ℝ) : ℝ :=
 Real.log t ^ 2 / (4 * π) - (Real.log (2 * π) + 1) / (2 * π) * Real.log t
  - (2.463 + 0.3) * t⁻¹ - 0.3 * (Real.log t * t⁻¹)
noncomputable def Rt (T t : ℝ) : ℝ :=
 2 * T * (-(1 / (2 * π)) * (Real.log t * t⁻¹) + Real.log (2 * π) / (2 * π) * t⁻¹
  - (2.463 / 2 + 0.3 / 4) * t⁻¹ ^ 2 - 0.3 / 2 * (Real.log t * t⁻¹) * t⁻¹)
noncomputable def Ub (T : ℝ) : ℝ :=
 P1 T - P1 4.4 + (Real.log T - Real.log (2 * π)) / π + (2.463 + 0.3 / 2) / T
  + 0.3 * Real.log T / T
lemma vkB {t : ℝ} (ht : 1 ≤ t) : 0 < Nc t := by
 have hp := Real.pi_pos
 have hy : 0 < t / (2 * π) := by positivity
 have h1 := Real.one_sub_inv_le_log_of_pos hy
 rw [Real.log_div (by linarith) (by positivity)] at h1
 have h2 : 0 ≤ Real.log t := Real.log_nonneg ht
 have h3 : t / (2 * π) * (Real.log t - Real.log (2 * π) - 1) ≥ -1 := by
  have : t / (2 * π) * (1 - (t / (2 * π))⁻¹) = t / (2 * π) - 1 := by field_simp
  nlinarith
 unfold Nc; linarith
lemma vjt {t : ℝ} (ht : 0 < t) : HasDerivAt P1 (Nc t / t ^ 2) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hi := hasDerivAt_inv ht.ne'
  have h := ((((hl.pow 2).div_const (4 * π)).sub (hl.const_mul ((Real.log (2 * π) + 1) / (2 * π)))).sub
    (hi.const_mul (2.463 + 0.3))).sub ((hl.mul hi).const_mul 0.3)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  · funext y; simp only [P1, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  have ht' : t ≠ 0 := ht.ne'
  unfold Nc
  field_simp
  ring
lemma vjs (T : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Rt T) (Nc t * (2 * T / t ^ 3)) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hi := hasDerivAt_inv ht.ne'
  have h := (((((hl.mul hi).const_mul (-(1 / (2 * π)))).add
    (hi.const_mul (Real.log (2 * π) / (2 * π)))).sub ((hi.pow 2).const_mul (2.463 / 2 + 0.3 / 4))).sub
    (((hl.mul hi).mul hi).const_mul (0.3 / 2))).const_mul (2 * T)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  · funext y; simp only [Rt, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring
  simp only [Pi.mul_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have ht' : t ≠ 0 := ht.ne'
  unfold Nc
  field_simp
  ring
lemma viE (T : ℝ) : Tendsto (Rt T) atTop (𝓝 0) := by
 have hL : Tendsto (fun t : ℝ => Real.log t * t⁻¹) atTop (𝓝 0) := by
  have := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  refine this.congr fun t => ?_
  simp [div_eq_mul_inv]
 have hI : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
 have h := ((((hL.const_mul (-(1 / (2 * π)))).add (hI.const_mul (Real.log (2 * π) / (2 * π)))).sub
  ((hI.pow 2).const_mul (2.463 / 2 + 0.3 / 4))).sub ((hL.mul hI).const_mul (0.3 / 2))).const_mul
  (2 * T)
 simp only [mul_zero, add_zero, sub_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
  not_false_eq_true, zero_pow] at h
 refine h.congr fun t => ?_
 simp only [Rt]; ring
lemma vhN (hRH : RiemannHypothesis) (ρ : qQ) (h : 0 < (ρ : ℂ).im) :
  4.4 < (ρ : ℂ).im := by
 have h1 := vfM (vbK hRH ρ)
 have h2 := vcn hRH ρ
 nlinarith
lemma viz {a b : ℝ} (c : ℝ) (ha : 0 < a) (hab : a ≤ b) :
  ∫ t in a..b, c / t ^ 2 = c * (1 / a - 1 / b) := by
 have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t => -c * t⁻¹) (c / x ^ 2) x := by
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  convert (hasDerivAt_inv hx0).const_mul (-c) using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
 have hc : ContinuousOn (fun t : ℝ => c / t ^ 2) (uIcc a b) := by
  refine continuousOn_const.div (continuousOn_pow 2) fun x hx => ?_
  rw [uIcc_of_le hab] at hx
  have : 0 < x := by linarith [hx.1]
  exact (pow_pos this 2).ne'
 rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
 field_simp
 ring
lemma vgj (m T : ℝ) {t : ℝ} (ht : 0 < t) :
  HasDerivAt (fun s : ℝ => -(m * T) * (s ^ 2)⁻¹) (m * (2 * T / t ^ 3)) t := by
 have h := ((hasDerivAt_pow 2 t).inv (by positivity)).const_mul (-(m * T))
 convert h using 1
 all_goals try with_reducible_and_instances rfl
 field_simp
 ring
lemma vhB (m T : ℝ) : Tendsto (fun s : ℝ => -(m * T) * (s ^ 2)⁻¹) atTop (𝓝 0) := by
 have := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero)).const_mul
  (-(m * T))
 simpa using this
noncomputable def aF (ρ : qQ) : ℝ → ℝ :=
 if 0 < (ρ : ℂ).im then (Ioi (ρ : ℂ).im).indicator (fun t => mult ρ / t ^ 2) else 0
noncomputable def bF (T : ℝ) (ρ : qQ) : ℝ → ℝ :=
 if 0 < (ρ : ℂ).im then (Ioi (ρ : ℂ).im).indicator (fun t => mult ρ * (2 * T / t ^ 3)) else 0
lemma vgo (ρ : qQ) (t : ℝ) : 0 ≤ aF ρ t := by
  unfold aF
  split_ifs
  · exact indicator_nonneg (fun _ _ => div_nonneg (vat ρ) (sq_nonneg _)) t
  · exact le_rfl
lemma vgs {T : ℝ} (hT : 0 ≤ T) (ρ : qQ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ bF T ρ t := by
  unfold bF
  split_ifs
  · exact indicator_nonneg (fun _ _ => mul_nonneg (vat ρ)
      (div_nonneg (by linarith) (pow_nonneg ht 3))) t
  · exact le_rfl
lemma vhs (c : ℝ) {T : ℝ} :
  IntegrableOn (fun t : ℝ => c / t ^ 2) (Ioc 4.4 T) := by
 refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
 refine continuousOn_const.div (continuousOn_pow 2) fun x hx => ?_
 have : 0 < x := by linarith [hx.1]
 exact (pow_pos this 2).ne'
lemma vhU (m : ℝ) {T : ℝ} (hT : 0 < T) (hm : 0 ≤ m) {a : ℝ} (ha : T ≤ a) :
    IntegrableOn (fun t : ℝ => m * (2 * T / t ^ 3)) (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x hx => vgj m T ?_)
    (fun x hx => ?_) (vhB m T)
  · have : T ≤ x := ha.trans hx; linarith
  · have : 0 < x := by have := hx.out; linarith
    positivity
lemma vjR (hRH : RiemannHypothesis) {T : ℝ} (hT : 4.4 ≤ T) (ρ : qQ) :
    ∫ t in Ioc 4.4 T, aF ρ t
      = if 0 < (ρ : ℂ).im then mult ρ * (if (ρ : ℂ).im < T then 1 / (ρ : ℂ).im - 1 / T else 0)
        else 0 := by
  unfold aF
  by_cases h : 0 < (ρ : ℂ).im
  · simp only [if_pos h]
    have hg := vhN hRH ρ h
    rw [setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, max_eq_right hg.le]
    by_cases hl : (ρ : ℂ).im < T
    · rw [if_pos hl, ← intervalIntegral.integral_of_le hl.le, viz _ h hl.le]
    · rw [if_neg hl, Ioc_eq_empty hl, Measure.restrict_empty, integral_zero_measure, mul_zero]
  · simp [h]
lemma vjO (hRH : RiemannHypothesis) {T : ℝ} (hT : 4.4 ≤ T) (ρ : qQ) :
    ∫ t in Ioi T, bF T ρ t
      = if 0 < (ρ : ℂ).im then mult ρ * (T / (max T (ρ : ℂ).im) ^ 2) else 0 := by
  unfold bF
  by_cases h : 0 < (ρ : ℂ).im
  · simp only [if_pos h]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi]
    have hm : 0 < max T (ρ : ℂ).im := lt_max_of_lt_left (by linarith)
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => vgj (mult ρ) T
      (lt_of_lt_of_le hm hx)) (fun x hx => ?_) (vhB (mult ρ) T)]
    · field_simp
      ring
    · have : 0 < x := lt_trans hm hx
      exact mul_nonneg (vat ρ) (by positivity)
  · simp [h]
lemma vgX (hRH : RiemannHypothesis) {T : ℝ} (hT : 4.4 ≤ T) (ρ : qQ) :
    vaY T ρ = (∫ t in Ioc 4.4 T, aF ρ t) + ∫ t in Ioi T, bF T ρ t := by
  rw [vjR hRH hT, vjO hRH hT]
  unfold vaY qbt
  by_cases h : 0 < (ρ : ℂ).im
  · simp only [if_pos h]
    set g := (ρ : ℂ).im
    have hg := vhN hRH ρ h
    by_cases hl : g < T
    · rw [if_pos hl, max_eq_left hl.le, min_eq_left]
      · field_simp; ring
      · rw [div_le_div_iff₀ h (by positivity)]; nlinarith
    · push Not at hl
      rw [if_neg (not_lt.mpr hl), max_eq_right hl, min_eq_right]
      · ring
      · rw [div_le_div_iff₀ (by positivity) h]; nlinarith
  · simp [h]
noncomputable def ind (t : ℝ) (ρ : qQ) : ℝ :=
 if 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t then mult ρ else 0
lemma vke (t : ℝ) (ρ : qQ) : 0 ≤ ind t ρ := by
  unfold ind; split_ifs
  · exact vat ρ
  · exact le_rfl
lemma vkA (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) (ρ : qQ) :
    ind t ρ ≤ (1 / 4 + t ^ 2) * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have h1 := vfM (vbK hRH ρ)
  have h2 := vcn hRH ρ
  have hm := vat ρ
  unfold ind
  split_ifs with h
  · rw [mul_div_assoc', le_div_iff₀ (by positivity), h1]
    have : (ρ : ℂ).im ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h.1.le h.2 2
    nlinarith
  · positivity
lemma vhH (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) : Summable (ind t) :=
 Summable.of_nonneg_of_le (vke t) (vkA hRH ht)
  ((vbg hRH).mul_left _)
lemma vkm (t : ℝ) : cnt t = ∑' ρ, ind t ρ := rfl
lemma vks (ρ : qQ) {t : ℝ} : aF ρ t ≤ ind t ρ / t ^ 2 := by
  unfold aF ind
  by_cases h : 0 < (ρ : ℂ).im
  · rw [if_pos h]
    by_cases hl : (ρ : ℂ).im < t
    · rw [indicator_of_mem (show t ∈ Ioi (ρ : ℂ).im from hl), if_pos ⟨h, hl.le⟩]
    · rw [indicator_of_notMem (show t ∉ Ioi (ρ : ℂ).im from hl)]
      split_ifs
      · exact div_nonneg (vat ρ) (sq_nonneg _)
      · simp
  · rw [if_neg h]
    simp only [Pi.zero_apply]
    split_ifs
    · exact div_nonneg (vat ρ) (sq_nonneg _)
    · simp
lemma vkD {T : ℝ} (hT : 0 ≤ T) (ρ : qQ) {t : ℝ} (ht : 0 ≤ t) :
    bF T ρ t ≤ ind t ρ * (2 * T / t ^ 3) := by
  have hc : 0 ≤ 2 * T / t ^ 3 := by positivity
  unfold bF ind
  by_cases h : 0 < (ρ : ℂ).im
  · rw [if_pos h]
    by_cases hl : (ρ : ℂ).im < t
    · rw [indicator_of_mem (show t ∈ Ioi (ρ : ℂ).im from hl), if_pos ⟨h, hl.le⟩]
    · rw [indicator_of_notMem (show t ∉ Ioi (ρ : ℂ).im from hl)]
      split_ifs
      · exact mul_nonneg (vat ρ) hc
      · simp
  · rw [if_neg h]
    simp only [Pi.zero_apply]
    split_ifs
    · exact mul_nonneg (vat ρ) hc
    · simp
theorem vjh (hR : vbc) {t : ℝ} (ht : 2 ≤ t) : cnt t ≤ Nc t := by
  have h := (abs_lt.mp (hR t ht)).2
  rw [vhc] at h
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hll : Real.log (Real.log t) ≤ Real.log t / Real.exp 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log t / Real.exp 1 by positivity)
    rw [Real.log_div hl.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    linarith
  have he : 0.443 / Real.exp 1 ≤ 0.163 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith [Real.exp_one_gt_d9]
  have hll' : 0.443 * Real.log (Real.log t) ≤ 0.163 * Real.log t := by
    calc 0.443 * Real.log (Real.log t) ≤ 0.443 * (Real.log t / Real.exp 1) := by gcongr
      _ = 0.443 / Real.exp 1 * Real.log t := by ring
      _ ≤ 0.163 * Real.log t := by gcongr
  have hd : Real.log (t / (2 * π)) = Real.log t - Real.log (2 * π) :=
    Real.log_div (by linarith) (by positivity)
  rw [hd] at h
  unfold Nc
  nlinarith
theorem vjW (hRH : RiemannHypothesis) (hR : vbc) {T : ℝ} (hT : 4.4 ≤ T) :
    qbu T ≤ Ub T := by
  have hT0 : 0 < T := by linarith
  have hAi : ∀ ρ, Integrable (aF ρ) (volume.restrict (Ioc (4.4 : ℝ) T)) := by
    intro ρ; unfold aF
    split_ifs
    · exact (vhs (mult ρ)).indicator measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hBi : ∀ ρ, Integrable (bF T ρ) (volume.restrict (Ioi T)) := by
    intro ρ; unfold bF
    split_ifs
    · exact (vhU (mult ρ) hT0 (vat ρ) le_rfl).indicator measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hA0 : ∀ ρ, 0 ≤ ∫ t in (Ioc (4.4 : ℝ) T), aF ρ t := fun ρ => integral_nonneg (vgo ρ)
  have hB0 : ∀ ρ, 0 ≤ ∫ t in (Ioi T), bF T ρ t := fun ρ =>
    setIntegral_nonneg measurableSet_Ioi fun t ht => vgs hT0.le ρ (by linarith [ht.out])
  have hps := vfN hRH hT0.le
  have hAs : Summable fun ρ => ∫ t in (Ioc (4.4 : ℝ) T), aF ρ t :=
    Summable.of_nonneg_of_le hA0 (fun ρ => by rw [vgX hRH hT ρ]; linarith [hB0 ρ]) hps
  have hBs : Summable fun ρ => ∫ t in (Ioi T), bF T ρ t :=
    Summable.of_nonneg_of_le hB0 (fun ρ => by rw [vgX hRH hT ρ]; linarith [hA0 ρ]) hps
  have hAn : Summable fun ρ => ∫ t in (Ioc (4.4 : ℝ) T), ‖aF ρ t‖ := by
    refine hAs.congr fun ρ => ?_
    exact integral_congr_ae (ae_of_all _ fun t => (Real.norm_of_nonneg (vgo ρ t)).symm)
  have hBn : Summable fun ρ => ∫ t in (Ioi T), ‖bF T ρ t‖ := by
    refine hBs.congr fun ρ => ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact (Real.norm_of_nonneg (vgs hT0.le ρ (by linarith [ht.out]))).symm
  have eA := integral_tsum_of_summable_integral_norm hAi hAn
  have eB := integral_tsum_of_summable_integral_norm hBi hBn
  have eG : qbu T = (∑' ρ, ∫ t in (Ioc (4.4 : ℝ) T), aF ρ t) + ∑' ρ, ∫ t in (Ioi T), bF T ρ t := by
    rw [qbu, ← hAs.tsum_add hBs]
    exact tsum_congr (vgX hRH hT)
  rw [eG, eA, eB]
  have hA : ∫ t in (Ioc (4.4 : ℝ) T), (∑' ρ, aF ρ t) ≤ P1 T - P1 4.4 := by
    have hI : IntegrableOn (fun t => Nc t / t ^ 2) (Ioc (4.4 : ℝ) T) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x ≠ 0 := hx0.ne'
      have hx2 : x ^ 2 ≠ 0 := by positivity
      unfold Nc
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    have hle : ∫ t in (Ioc (4.4 : ℝ) T), (∑' ρ, aF ρ t) ≤ ∫ t in (Ioc (4.4 : ℝ) T), Nc t / t ^ 2 := by
      refine integral_mono_of_nonneg (ae_of_all _ fun t => tsum_nonneg (vgo · t)) hI ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hs := vhH hRH ht0
      calc ∑' ρ, aF ρ t ≤ ∑' ρ, ind t ρ / t ^ 2 :=
            (Summable.of_nonneg_of_le (vgo · t) (fun ρ => vks ρ) (hs.div_const _)).tsum_le_tsum
              (fun ρ => vks ρ) (hs.div_const _)
        _ = cnt t / t ^ 2 := by rw [tsum_div_const, vkm]
        _ ≤ Nc t / t ^ 2 := by
            gcongr; exact vjh hR (by linarith [ht.1])
    refine hle.trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_of_le hT]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
    · rw [uIcc_of_le hT] at hx; exact vjt (by linarith [hx.1])
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hI
  have hB : ∫ t in (Ioi T), (∑' ρ, bF T ρ t)
      ≤ (Real.log T - Real.log (2 * π)) / π + (2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T := by
    have hd : ∀ x ∈ Ici T, HasDerivAt (Rt T) (Nc x * (2 * T / x ^ 3)) x :=
      fun x hx => vjs T (by linarith [hx.out])
    have hpos : ∀ x ∈ Ioi T, 0 ≤ Nc x * (2 * T / x ^ 3) := fun x hx => by
      have : T < x := hx.out
      exact mul_nonneg (vkB (by linarith)).le
        (div_nonneg (by linarith) (pow_nonneg (by linarith) 3))
    have hI := integrableOn_Ioi_deriv_of_nonneg' hd hpos (viE T)
    have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos (viE T)
    have hle : ∫ t in (Ioi T), (∑' ρ, bF T ρ t) ≤ ∫ t in (Ioi T), Nc t * (2 * T / t ^ 3) := by
      refine integral_mono_of_nonneg ?_ hI ?_
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
        exact tsum_nonneg fun ρ => vgs hT0.le ρ (by linarith [ht.out])
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 ≤ t := by linarith [ht.out]
      have hs := vhH hRH ht0
      have hb := fun ρ => vkD hT0.le ρ ht0
      calc ∑' ρ, bF T ρ t ≤ ∑' ρ, ind t ρ * (2 * T / t ^ 3) :=
            (Summable.of_nonneg_of_le (fun ρ => vgs hT0.le ρ ht0) hb
              (hs.mul_right _)).tsum_le_tsum hb (hs.mul_right _)
        _ = cnt t * (2 * T / t ^ 3) := by rw [tsum_mul_right, vkm]
        _ ≤ Nc t * (2 * T / t ^ 3) := by
            gcongr; exact vjh hR (by linarith [ht.out])
    refine hle.trans (le_of_eq ?_)
    rw [hval]
    unfold Rt
    field_simp
    ring
  unfold Ub
  linarith
end Schoenfeld
end
section
namespace Schoenfeld
open ArithmeticFunction Real Chebyshev
noncomputable def psi1 (t : ℝ) : ℝ :=
 ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * (t - n)
lemma vfj (s : ℝ) {N : ℕ} (hN : ⌊s⌋₊ ≤ N) (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ s → f n = g n)
    (h2 : ∀ n : ℕ, s < n → g n = 0) :
    ∑ n ∈ Finset.range (⌊s⌋₊ + 1), f n = ∑ n ∈ Finset.range (N + 1), g n := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega) :
    Finset.range (⌊s⌋₊ + 1) ⊆ Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · exact h0
    · simp only [Finset.mem_range] at hn
      exact h1 n hn0 ((Nat.le_floor_iff' hn0).mp (by omega))
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    exact h2 n (Nat.lt_of_floor_lt (by omega))
lemma vgp {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
  psi1 t = ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * max (t - n) 0 :=
 vfj t hN _ _ (by simp)
  (fun n _ hn => by rw [max_eq_left (by linarith)])
  (fun n hn => by rw [max_eq_right (by linarith), mul_zero])
lemma vim (t : ℝ) : ψ t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) := by
 rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
lemma vgO {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
  ψ t = ∑ n ∈ Finset.range (N + 1), if (n : ℝ) ≤ t then (Λ n : ℝ) else 0 := by
 rw [vim]
 exact vfj t hN _ _ (by simp) (fun n _ hn => by simp [hn])
  (fun n hn => by simp [not_le.mpr hn])
lemma vjd (s h : ℝ) (hh : 0 ≤ h) :
    h * ψ s ≤ psi1 (s + h) - psi1 s ∧ psi1 (s + h) - psi1 s ≤ h * ψ (s + h) := by
  have hN : ⌊s⌋₊ ≤ ⌊s + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [vgp hN, vgp le_rfl, vgO hN, vgO le_rfl,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      exact le_of_eq (by ring)
    · rw [mul_zero, ← mul_sub]
      exact mul_nonneg hΛ (sub_nonneg.mpr (max_le_max (by linarith) le_rfl))
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [← mul_sub, mul_comm h]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      have := le_max_left (s - n) 0
      have := le_max_right (s - n) 0
      have : max (s + h - n) 0 ≤ max (s - n) 0 + h := max_le (by linarith) (by linarith)
      linarith
    · push Not at hn
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      simp
lemma vkp (m : ℕ) (hm : 1 ≤ m) :
  psi1 m = m * ∑ n ∈ Finset.range m, (Λ n : ℝ) * (1 - (n : ℝ) / m) := by
 have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
 unfold psi1
 rw [Nat.floor_natCast, Finset.sum_range_succ, sub_self, mul_zero, add_zero, Finset.mul_sum]
 refine Finset.sum_congr rfl fun n _ => ?_
 field_simp
end Schoenfeld
end
section
namespace Schoenfeld
open Complex Erdos985.Analytic ArithmeticFunction Chebyshev
noncomputable def tA (ρ : qQ) : ℂ := (mult ρ : ℂ) * (2 / ((ρ : ℂ) * (2 - ρ)))
noncomputable def tB (ρ : qQ) : ℂ := (mult ρ : ℂ) * (1 / ((2 - (ρ : ℂ)) * (1 + ρ)))
noncomputable def tW (x : ℕ) (ρ : qQ) : ℂ :=
 (mult ρ : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))
section Norms
variable {ρ : ℂ}
lemma vdV (hρ : ρ.re = 1 / 2) : 0 < ‖ρ‖ :=
 norm_pos_iff.mpr fun h => by rw [h] at hρ; norm_num at hρ
lemma vhi (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖(2 : ℂ) - ρ‖ := by
 rw [BoundsAux.viy hρ]; exact BoundsAux.vcf hρ
lemma vji (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖(1 : ℂ) + ρ‖ := by
 rw [add_comm]; exact BoundsAux.vcf hρ
lemma norm_inv_mul_le {u v : ℂ} (hu : ‖ρ‖ ≤ ‖u‖) (hv : ‖ρ‖ ≤ ‖v‖) (h0 : 0 < ‖ρ‖) (c : ℝ)
    (hc : 0 ≤ c) {w : ℂ} (hw : ‖w‖ ≤ c) : ‖w / (u * v)‖ ≤ c / ‖ρ‖ ^ 2 := by
  rw [norm_div, norm_mul]
  have hu0 : 0 < ‖u‖ := h0.trans_le hu
  have hv0 : 0 < ‖v‖ := h0.trans_le hv
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖w‖ * ‖ρ‖ ^ 2 ≤ c * (‖u‖ * ‖v‖) := by
        rw [sq]; exact mul_le_mul hw (mul_le_mul hu hv h0.le hu0.le) (by positivity) hc
    _ = _ := rfl
end Norms
lemma viJ (hRH : RiemannHypothesis) (ρ : qQ) :
    ‖tA ρ‖ ≤ 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have hρ := vbK hRH ρ
  unfold tA
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vat ρ)]
  have := norm_inv_mul_le le_rfl (vhi hρ) (vdV hρ) 2 (by norm_num)
    (w := 2) (by simp)
  calc mult ρ * ‖2 / ((ρ : ℂ) * (2 - ρ))‖ ≤ mult ρ * (2 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (vat ρ)
    _ = _ := by ring
lemma vjV (hRH : RiemannHypothesis) (ρ : qQ) :
    ‖tB ρ‖ ≤ mult ρ / ‖(ρ : ℂ)‖ ^ 2 := by
  have hρ := vbK hRH ρ
  unfold tB
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vat ρ)]
  have := norm_inv_mul_le (vhi hρ) (vji hρ) (vdV hρ) 1
    (by norm_num) (w := 1) (by simp)
  calc mult ρ * ‖1 / ((2 - (ρ : ℂ)) * (1 + ρ))‖ ≤ mult ρ * (1 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (vat ρ)
    _ = _ := by ring
lemma vjk (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
  ‖(x : ℂ) ^ ρ‖ = √(x : ℝ) := by
 have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
 rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ,
  Real.sqrt_eq_rpow]
lemma vkf (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) (ρ : qQ) :
    ‖tW x ρ‖ ≤ √(x : ℝ) * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have hρ := vbK hRH ρ
  unfold tW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vat ρ)]
  have := norm_inv_mul_le le_rfl (BoundsAux.vcf hρ) (vdV hρ) _
    (Real.sqrt_nonneg _) (w := (x : ℂ) ^ (ρ : ℂ)) (vjk x hx hρ).le
  calc mult ρ * ‖(x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖
      ≤ mult ρ * (√(x : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := mul_le_mul_of_nonneg_left this (vat ρ)
    _ = _ := by ring
lemma vie (hRH : RiemannHypothesis) : Summable tA :=
 Summable.of_norm_bounded ((vbg hRH).mul_left 2) (viJ hRH)
lemma vif (hRH : RiemannHypothesis) : Summable tB :=
 Summable.of_norm_bounded (vbg hRH) (vjV hRH)
lemma vgx (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) : Summable (tW x) :=
 Summable.of_norm_bounded ((vbg hRH).mul_left _) (vkf hRH x hx)
noncomputable def vhP : ℝ :=
 (∑' ρ, tA ρ).re - 7 / 2 - (deriv riemannZeta 2 / riemannZeta 2).re
noncomputable def delta : ℝ :=
 3 + (deriv riemannZeta 2 / riemannZeta 2).re - 3 * (∑' ρ, tB ρ).re
noncomputable def qc9 (x : ℕ) : ℝ := (vbn (1 : DirichletCharacter ℂ 1) x).re + Real.log x
theorem vib (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) :
  psi1 x = (x : ℝ) ^ 2 / 2 - x * (∑' ρ, tW x ρ).re + vhP * x + x * qc9 x + delta := by
 have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
 have hid := vgB x hx
 have hzt : ∀ ρ : qQ, (analyticOrderNatAt van ρ : ℂ) * vdg x ρ
   = tA ρ - (3 / (x : ℂ)) * tB ρ - tW x ρ := by
  intro ρ
  rw [BoundsAux.vjK x hx (vbK hRH ρ), tA, tB, tW, mult]
  push_cast
  ring
 simp_rw [hzt] at hid
 rw [Summable.tsum_sub ((vie hRH).sub ((vif hRH).mul_left _))
   (vgx hRH x hx), Summable.tsum_sub (vie hRH) ((vif hRH).mul_left _),
  tsum_mul_left] at hid
 have hre := congrArg Complex.re hid
 have hL2 : (deriv riemannZeta 2 / riemannZeta 2).im = 0 := (veh).1
 have hΓ : (vbn (1 : DirichletCharacter ℂ 1) x).im = 0 := (veX x hx).1
 have e3 : (3 / (x : ℂ)) = ((3 / x : ℝ) : ℂ) := by push_cast; rfl
 have e1 : (1 - 1 / (x : ℂ)) = ((1 - 1 / x : ℝ) : ℂ) := by push_cast; rfl
 have e2 : ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
   = (((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x : ℝ) : ℂ) := by push_cast; rfl
 rw [e1, e2, e3] at hre
 simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul] at hre
 rw [vkp x hx, hre, vhP, delta, qc9]
 field_simp
 ring
lemma vhG (hRH : RiemannHypothesis) : -2.6 ≤ vhP + 1 ∧ vhP + 1 ≤ -1.8 := by
  have hA : ‖∑' ρ, tA ρ‖ ≤ 2 * (1 / 20) := by
    calc ‖∑' ρ, tA ρ‖ ≤ ∑' ρ, 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) :=
          tsum_of_norm_bounded ((vbg hRH).mul_left 2).hasSum (viJ hRH)
      _ = 2 * ∑' ρ, mult ρ / ‖(ρ : ℂ)‖ ^ 2 := tsum_mul_left
      _ ≤ 2 * (1 / 20) := by linarith [vis hRH]
  have hAr := (Complex.abs_re_le_norm (∑' ρ, tA ρ)).trans hA
  obtain ⟨-, hl1, hl2⟩ := veh
  rw [abs_le] at hAr
  unfold vhP
  constructor <;> linarith [hAr.1, hAr.2]
lemma vig (x : ℕ) (hx : 1 ≤ x) : (x : ℝ) - 3 / 2 ≤ x * qc9 x ∧ x * qc9 x ≤ x := by
  obtain ⟨-, h1, h2⟩ := veX x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  unfold qc9
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hx0.le
    have e : (x : ℝ) * (1 - 3 / (2 * x)) = x - 3 / 2 := by field_simp
    linarith
  · nlinarith
lemma vhY {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
  ‖(b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)‖ ≤ ‖ρ + 1‖ * ((b - a) * √b) := by
 have hρ1 : ρ + 1 ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
 have hI := integral_cpow (a := a) (b := b) (r := ρ) (Or.inl (by rw [hρ]; norm_num))
 have e : (b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1) = (ρ + 1) * ∫ x in a..b, (x : ℂ) ^ ρ := by
  rw [hI]; field_simp
 rw [e, norm_mul]
 refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
 have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
  (f := fun x : ℝ => (x : ℂ) ^ ρ) (C := √b) (fun x hx => by
   rw [Set.uIoc_of_le hab] at hx
   have hx0 : 0 < x := ha.trans hx.1
   rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ, ← Real.sqrt_eq_rpow]
   exact Real.sqrt_le_sqrt hx.2)
 rw [abs_of_nonneg (by linarith)] at hb
 linarith
lemma vgH {b : ℝ} (hb : 0 < b) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
  ‖(b : ℂ) ^ (ρ + 1)‖ = b * √b := by
 rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, add_re, hρ, one_re,
  show (1 / 2 + 1 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb, Real.rpow_one,
  ← Real.sqrt_eq_rpow]
lemma vhK (x : ℕ) (hx : 1 ≤ x) (ρ : ℂ) :
  (x : ℂ) * (x : ℂ) ^ ρ = ((x : ℝ) : ℂ) ^ (ρ + 1) := by
 have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
 rw [show ((x : ℝ) : ℂ) = (x : ℂ) by push_cast; rfl, cpow_add _ _ hx0, cpow_one, mul_comm]
lemma vjZ (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) (ρ : qQ) :
    ‖((a + h : ℕ) : ℂ) * tW (a + h) ρ - (a : ℂ) * tW a ρ‖
      ≤ h * √((a + h : ℕ) : ℝ) * fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hρ := vbK hRH ρ
  set b : ℕ := a + h with qi1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hbR : (b : ℝ) = a + h := by rw [qi1]; push_cast; ring
  have hb0 : (0 : ℝ) < b := by rw [hbR]; linarith
  have hab : (a : ℝ) ≤ b := by rw [hbR]; linarith
  have hN := vdV hρ
  have hN1 := BoundsAux.vcf hρ
  have e : ((b : ℕ) : ℂ) * tW b ρ - (a : ℂ) * tW a ρ
      = (mult ρ : ℂ) * ((((b : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - ((a : ℝ) : ℂ) ^ ((ρ : ℂ) + 1))
        / ((ρ : ℂ) * ((ρ : ℂ) + 1))) := by
    unfold tW
    rw [← vhK b (by omega), ← vhK a ha]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (vat ρ), norm_div, norm_mul]
  set D := ‖((b : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - ((a : ℝ) : ℂ) ^ ((ρ : ℂ) + 1)‖
  have hD1 : D ≤ ‖(ρ : ℂ) + 1‖ * (h * √(b : ℝ)) := by
    have := vhY ha0 hab hρ
    rwa [show (b : ℝ) - a = h by rw [hbR]; ring] at this
  have hD2 : D ≤ 2 * (b * √(b : ℝ)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [vgH hb0 hρ, vgH ha0 hρ]
    have : (a : ℝ) * √(a : ℝ) ≤ b * √(b : ℝ) :=
      mul_le_mul hab (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg _) hb0.le
    linarith
  have qp4 : 0 < ‖(ρ : ℂ) + 1‖ := hN.trans_le hN1
  unfold fmin
  rw [show (h : ℝ) * √(b : ℝ) * (mult ρ * min (1 / ‖(ρ : ℂ)‖) (2 * b / h / ‖(ρ : ℂ)‖ ^ 2))
      = mult ρ * (h * √(b : ℝ) * min (1 / ‖(ρ : ℂ)‖) (2 * b / h / ‖(ρ : ℂ)‖ ^ 2)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (vat ρ)
  rw [mul_min_of_nonneg _ _ (by positivity), le_min_iff]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc D ≤ ‖(ρ : ℂ) + 1‖ * (h * √(b : ℝ)) := hD1
      _ = h * √(b : ℝ) * (1 / ‖(ρ : ℂ)‖) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖) := by field_simp
  · rw [div_le_iff₀ (by positivity)]
    calc D ≤ 2 * (b * √(b : ℝ)) := hD2
      _ = h * √(b : ℝ) * (2 * b / h / ‖(ρ : ℂ)‖ ^ 2) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) := by
          field_simp
      _ ≤ h * √(b : ℝ) * (2 * b / h / ‖(ρ : ℂ)‖ ^ 2) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖) := by
          gcongr
theorem vil (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
  |((a + h : ℕ) : ℝ) * (∑' ρ, tW (a + h) ρ).re - (a : ℝ) * (∑' ρ, tW a ρ).re|
   ≤ h * √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
 have hT : 0 ≤ 2 * ((a + h : ℕ) : ℝ) / h := by positivity
 have hsF := (vex hRH hT).mul_left (h * √((a + h : ℕ) : ℝ))
 have e : ((a + h : ℕ) : ℝ) * (∑' ρ, tW (a + h) ρ).re - (a : ℝ) * (∑' ρ, tW a ρ).re
   = (∑' ρ, (((a + h : ℕ) : ℂ) * tW (a + h) ρ - (a : ℂ) * tW a ρ)).re := by
  rw [Summable.tsum_sub ((vgx hRH _ (by omega)).mul_left _)
   ((vgx hRH a ha).mul_left _), tsum_mul_left, tsum_mul_left, Complex.sub_re]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
 rw [e]
 refine (Complex.abs_re_le_norm _).trans ?_
 rw [← tsum_mul_left]
 exact tsum_of_norm_bounded hsF.hasSum (vjZ hRH a h ha hh)
theorem vgm (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
  |psi1 ((a + h : ℕ) : ℝ) - psi1 a - ((((a + h : ℕ) : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2
    + (vhP + 1) * h)|
   ≤ 3 / 2 + h * √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
 have hb := vib hRH (a + h) (by omega)
 have ha' := vib hRH a ha
 have hZ := vil hRH a h ha hh
 obtain ⟨eb1, eb2⟩ := vig (a + h) (by omega)
 obtain ⟨ea1, ea2⟩ := vig a ha
 have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
 rw [hb, ha']
 rw [abs_le] at hZ ⊢
 rw [hbR] at eb1 eb2 hZ ⊢
 constructor <;> nlinarith [hZ.1, hZ.2]
theorem vjr (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
  ψ a - a ≤ h / 2 - 1.8 + 1.5 / h
   + √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
 have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
 have hd := (vjd (a : ℝ) h hh0.le).1
 have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
 have hB := vgm hRH a h ha hh
 rw [hbR] at hB ⊢
 have hk := vhG hRH
 set F := √((a : ℝ) + h) * ∑' ρ, fmin (2 * ((a : ℝ) + h) / h) ρ
 have hB' := (abs_le.mp hB).2
 have key : (h : ℝ) * (ψ a - a) ≤ h * (h / 2 - 1.8 + 1.5 / h + F) := by
  have e : (h : ℝ) * (1.5 / h) = 3 / 2 := by field_simp; norm_num
  nlinarith
 exact le_of_mul_le_mul_left key hh0
theorem vjm (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
  ((a + h : ℕ) : ℝ) - ψ ((a + h : ℕ) : ℝ) ≤ h / 2 + 2.6 + 1.5 / h
   + √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
 have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
 have hd := (vjd (a : ℝ) h hh0.le).2
 have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
 have hB := vgm hRH a h ha hh
 rw [hbR] at hB ⊢
 have hk := vhG hRH
 set F := √((a : ℝ) + h) * ∑' ρ, fmin (2 * ((a : ℝ) + h) / h) ρ
 have hB' := (abs_le.mp hB).1
 have key : (h : ℝ) * ((a + h) - ψ (a + h)) ≤ h * (h / 2 + 2.6 + 1.5 / h + F) := by
  have e : (h : ℝ) * (1.5 / h) = 3 / 2 := by field_simp; norm_num
  nlinarith
 exact le_of_mul_le_mul_left key hh0
theorem viZ (hRH : RiemannHypothesis) (x : ℝ) (h : ℕ) (hh : 1 ≤ h)
    (hx : (h : ℝ) + 2 ≤ x) :
    |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hx0 : 0 ≤ x := by linarith
  set n := ⌊x⌋₊ with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hψ : ψ x = ψ n := by rw [psi_eq_psi_coe_floor]
  have hhn : h + 1 ≤ n := by
    have : ((h + 1 : ℕ) : ℝ) < (n : ℝ) + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hmono : ∀ y : ℝ, 0 ≤ y → y ≤ x + h →
      √y * ∑' ρ, fmin (2 * y / h) ρ ≤ √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ := by
    intro y hy hyx
    have hT : 0 ≤ 2 * y / h := by positivity
    exact mul_le_mul (Real.sqrt_le_sqrt hyx) (viS hRH hT (by gcongr))
      (tsum_nonneg (vgt hT)) (Real.sqrt_nonneg _)
  rw [hψ, abs_le]
  constructor
  ·
    have hL := vjm hRH (n - h) h (by omega) hh
    rw [show n - h + h = n by omega] at hL
    have := hmono n (by positivity) (by linarith)
    linarith
  · have hU := vjr hRH n h (by omega) hh
    have := hmono ((n + h : ℕ) : ℝ) (by positivity) (by push_cast; linarith)
    linarith
end Schoenfeld
end
section
namespace Schoenfeld
open Chebyshev Real
def vkt (C x₀ : ℝ) : Prop :=
 ∀ x : ℝ, x₀ ≤ x →
  |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < C * (√x * Real.log x)
def vjw : Prop := vkt (1 / (8 * π)) 2657
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev
lemma vaR : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
 ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩
lemma vez {a : ℝ} (k : ℕ) (hk : (2 : ℝ) ^ k ≤ a) :
  k * 0.6931471803 + (1 - 2 ^ k / a) ≤ Real.log a := by
 have h2k : (0 : ℝ) < 2 ^ k := by positivity
 have ha : 0 < a := h2k.trans_le hk
 have e : Real.log a = Real.log (2 ^ k) + Real.log (a / 2 ^ k) := by
  rw [← Real.log_mul h2k.ne' (by positivity), mul_div_cancel₀ _ h2k.ne']
 have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < a / 2 ^ k by positivity)
 rw [inv_div] at h1
 rw [e, Real.log_pow]
 have := vaR.1
 have : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
  mul_le_mul_of_nonneg_left this.le (Nat.cast_nonneg k)
 linarith
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev
lemma vje : Real.log π < 1.1718 := by
 have h1 := Real.log_le_sub_one_of_pos (show 0 < π / 4 by positivity)
 rw [Real.log_div Real.pi_pos.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
  Real.log_pow] at h1
 have := Real.pi_lt_d4
 have := vaR.2
 push_cast at h1
 linarith
lemma vhu : 1.4772 < Real.log 4.4 ∧ Real.log 4.4 < 1.4864 := by
  have e : Real.log 4.4 = 2 * Real.log 2 + Real.log 1.1 := by
    rw [show (4.4 : ℝ) = 2 ^ 2 * 1.1 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.1 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.1 by norm_num)
  have := vaR
  constructor
  · rw [e]; norm_num at h2; linarith
  · rw [e]; norm_num at h1; linarith
lemma vjX {T : ℝ} (hT : 4.4 ≤ T) :
  Ub T ≤ Real.log T ^ 2 / (4 * π) + (1 - Real.log (2 * π)) / (2 * π) * Real.log T + 0.65 := by
 have hp := Real.pi_gt_d4
 have hp' := Real.pi_lt_d4
 have hpi : 0 < π := Real.pi_pos
 obtain ⟨hL1, hL2⟩ := vhu
 have hk1 : 1.8371 < Real.log (2 * π) := by
  rw [Real.log_mul (by norm_num) hpi.ne']
  linarith [vaR.1, Erdos985.Analytic.PrincipalAux.vhg]
 have hk2 : Real.log (2 * π) < 1.8650 := by
  rw [Real.log_mul (by norm_num) hpi.ne']
  linarith [vaR.2, vje]
 have e : Ub T = Real.log T ^ 2 / (4 * π) + (1 - Real.log (2 * π)) / (2 * π) * Real.log T
   + (-(Real.log (2 * π) / π) - P1 4.4) - 0.15 / T := by
  have hP : P1 4.4 = Real.log 4.4 ^ 2 / (4 * π) - (Real.log (2 * π) + 1) / (2 * π) * Real.log 4.4
    - (2.463 + 0.3) * (4.4 : ℝ)⁻¹ - 0.3 * (Real.log 4.4 * (4.4 : ℝ)⁻¹) := rfl
  unfold Ub
  rw [hP]
  unfold P1
  generalize Real.log (2 * π) = k
  generalize Real.log 4.4 = L
  generalize Real.log T = ℓ
  field_simp
  ring
 set k := Real.log (2 * π)
 set L := Real.log 4.4
 have hT0 : 0 < T := by linarith
 have hC : -(k / π) - P1 4.4 ≤ 0.65 := by
  unfold P1
  rw [← sub_nonneg]
  have e : 0.65 - (-(k / π) - (L ^ 2 / (4 * π) - (k + 1) / (2 * π) * L - (2.463 + 0.3) * (4.4 : ℝ)⁻¹
    - 0.3 * (L * (4.4 : ℝ)⁻¹)))
    = (0.65 * π + k + L ^ 2 / 4 - (k + 1) * L / 2 - π * ((2.463 + 0.3) / 4.4) - π * (0.3 * L / 4.4))
     / π := by
   field_simp; ring
  rw [e]
  refine div_nonneg ?_ hpi.le
  have hL0 : 0 < L := by linarith
  have q1 := mul_pos (sub_pos.mpr hk1) (show (0 : ℝ) < 2 - L by linarith)
  have q2 := mul_pos (sub_pos.mpr hp') hL0
  have q3 := mul_pos (sub_pos.mpr hL1) hL0
  ring_nf at q1 q2 q3 ⊢
  linarith
 rw [e]
 have : 0 ≤ 0.15 / T := by positivity
 linarith
lemma vkk {x w : ℝ} (hx : 1 ≤ x) (hw : 0 ≤ w) (hwx : w ^ 4 = x) :
    Real.log x ^ 2 ≤ 64 * w := by
  set v := √w with hv
  have hv2 : v ^ 2 = w := Real.sq_sqrt hw
  have hv0 : 0 < v := by
    rw [hv]; apply Real.sqrt_pos.mpr
    by_contra h; push Not at h
    have : w = 0 := le_antisymm h hw
    rw [this] at hwx; norm_num at hwx; linarith
  have hlx : Real.log x = 8 * Real.log v := by
    rw [← hwx, ← hv2, ← pow_mul, Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos hv0
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h3 : Real.log x ≤ 8 * v := by rw [hlx]; linarith
  calc Real.log x ^ 2 ≤ (8 * v) ^ 2 := pow_le_pow_left₀ h2 h3 2
    _ = 64 * w := by rw [← hv2]; ring
lemma vjT {u ℓ : ℝ} (hu : 0 ≤ u) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ u / 2 - 1.0396) :
  2 * (ℓ ^ 2 / (4 * π) + (1 - Real.log (2 * π)) / (2 * π) * ℓ + 0.65)
   ≤ u ^ 2 / (8 * π) - 0.2985 * u + 1.76 := by
 have hp := Real.pi_gt_d4
 have hp' := Real.pi_lt_d4
 have hpi : 0 < π := Real.pi_pos
 have hk1 : 1.8371 < Real.log (2 * π) := by
  rw [Real.log_mul (by norm_num) hpi.ne']
  linarith [vaR.1, Erdos985.Analytic.PrincipalAux.vhg]
 have hk2 : Real.log (2 * π) < 1.8650 := by
  rw [Real.log_mul (by norm_num) hpi.ne']
  linarith [vaR.2, vje]
 generalize Real.log (2 * π) = k at hk1 hk2 ⊢
 set m := u / 2 - 1.0396
 have hmono : ℓ ^ 2 + 2 * (1 - k) * ℓ ≤ m ^ 2 + 2 * (1 - k) * m := by
  nlinarith
 rw [← sub_nonneg]
 have e : u ^ 2 / (8 * π) - 0.2985 * u + 1.76 - 2 * (ℓ ^ 2 / (4 * π) + (1 - k) / (2 * π) * ℓ + 0.65)
   = ((m ^ 2 + 2 * (1 - k) * m) - (ℓ ^ 2 + 2 * (1 - k) * ℓ)
    + (u ^ 2 / 4 - 0.597 * π * u + 0.92 * π - m ^ 2 - 2 * (1 - k) * m)) / (2 * π) := by
  field_simp; ring
 rw [e]
 refine div_nonneg ?_ (by positivity)
 have hm : u ^ 2 / 4 - 0.597 * π * u + 0.92 * π - m ^ 2 - 2 * (1 - k) * m
   = u * (k + 1.0396 - 1 - 0.597 * π) + (0.92 * π - 1.0396 ^ 2 - 2 * 1.0396 * (k - 1)) := by
  simp only [m]; ring
 have h1 : 0 ≤ u * (k + 1.0396 - 1 - 0.597 * π) := mul_nonneg hu (by linarith)
 nlinarith
lemma vjN {s u w A r : ℝ} (hs5 : 100000 ≤ s) (hw2 : w ^ 2 = s) (qf9 : 316 ≤ w)
  (qij : u ^ 2 ≤ 64 * w) (hAu : A ≤ u ^ 2 / (8 * π)) (hr : r ≤ 2.8285)
  (hA : A = u ^ 2 / (8 * π) - 0.2985 * u + 1.76) :
  (2 * r * s + 1) / 2 + 3.6 + 0.01 + (s * A + 2.85 * A)
   ≤ s * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) := by
 have hp := Real.pi_gt_d4
 have h8 : u ^ 2 / (8 * π) ≤ u ^ 2 / 25.13 :=
  div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) (by linarith)
 have hww : 316 * w ≤ w ^ 2 := by
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ w by linarith) (show (0 : ℝ) ≤ w - 316 by linarith)]
 have hsmall : 2.85 * A ≤ 0.0232 * s := by
  have : u ^ 2 / 25.13 ≤ 64 * w / 25.13 := by gcongr
  have hws : 64 * w ≤ 0.2026 * s := by rw [← hw2]; linarith
  have : 64 * w / 25.13 ≤ 0.2026 * s / 25.13 := by gcongr
  have h11 : 0.2026 * s / 25.13 ≤ 0.00811 * s := by
   rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith
 have hrs : r * s ≤ 2.8285 * s := mul_le_mul_of_nonneg_right hr (by linarith)
 have e1 : s * A = s * (u ^ 2 / (8 * π)) - 0.2985 * (s * u) + 1.76 * s := by rw [hA]; ring
 have e2 : s * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62)
   = s * (u ^ 2 / (8 * π)) - 0.2985 * (s * u) + 4.62 * s := by ring
 rw [e1, e2]; nlinarith
theorem vhA (hRH : RiemannHypothesis) (hR : vbc) {x : ℝ}
    (hx : 10 ^ 10 ≤ x) :
    |ψ x - x| ≤ √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 4.62) := by
  obtain ⟨qp5, qp6⟩ := vaR
  have hpi : 0 < π := Real.pi_pos
  have hp := Real.pi_gt_d4
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs5 : 100000 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs0 : 0 < s := by linarith
  set w := √s with hw
  have hw2 : w ^ 2 = s := Real.sq_sqrt hs0.le
  have qf9 : 316 ≤ w := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  set u := Real.log x with hu
  have hus : Real.log s = u / 2 := by
    rw [hu, ← hs2, Real.log_pow]; push_cast; ring
  have qij : u ^ 2 ≤ 64 * w :=
    vkk (by linarith) (by linarith) (by rw [← hs2, ← hw2]; ring)
  have hu0 : 33 * 0.6931471803 ≤ u := by
    have h1 := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 33 ≤ x by norm_num; linarith)
    rw [Real.log_pow] at h1; push_cast at h1
    linarith
  set r := √8 with hr
  have hr2 : r ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hrlo : 2.8284 ≤ r := Real.le_sqrt_of_sq_le (by norm_num)
  have hrhi : r ≤ 2.8285 := by nlinarith
  set h : ℕ := ⌈2 * r * s⌉₊ with hhdef
  have hh1 : 2 * r * s ≤ h := Nat.le_ceil _
  have hh2 : (h : ℝ) < 2 * r * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrs : r * s ≤ 2.8285 * s := mul_le_mul_of_nonneg_right hrhi hs0.le
  have hrs' : 2.8284 * s ≤ r * s := mul_le_mul_of_nonneg_right hrlo hs0.le
  have hss : 100000 * s ≤ s ^ 2 := by nlinarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hh : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hB := viZ hRH x h hh (by linarith)
  set T := 2 * (x + h) / h with hTdef
  have hTeq : T = 2 * x / h + 2 := by rw [hTdef]; field_simp
  have hT1 : T ≤ s / r + 2 := by
    have : 2 * x / h ≤ s / r := by
      rw [div_le_div_iff₀ hh0 hr0, ← hs2]
      have := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ s by linarith)
      nlinarith
    linarith
  have hT2 : s / 3 ≤ T := by
    have : s / 3 ≤ 2 * x / h := by
      rw [le_div_iff₀ hh0, ← hs2]
      have := mul_le_mul_of_nonneg_left hh2.le (show 0 ≤ s by linarith)
      nlinarith
    linarith
  have hTpos : 0 < T := by linarith
  have qik : 4.4 ≤ T := by linarith
  have hF := (vgz hRH hTpos.le).trans
    (mul_le_mul_of_nonneg_left ((vjW hRH hR qik).trans (vjX qik)) (by norm_num))
  have hlr : Real.log r = 3 / 2 * Real.log 2 := by
    rw [hr, Real.log_sqrt (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  have hlT : Real.log T ≤ u / 2 - 1.0396 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < T / (s / r) by positivity)
    rw [Real.log_div hTpos.ne' (by positivity), Real.log_div hs0.ne' hr0.ne', hus, hlr] at h1
    have : T / (s / r) - 1 ≤ 0.00006 := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      have : T - s / r ≤ 2 := by linarith
      have : 35000 ≤ s / r := by rw [le_div_iff₀ hr0]; linarith
      linarith
    linarith
  have qlw : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hq := vjT (u := u) (by linarith) qlw hlT
  have hF0 : 0 ≤ ∑' ρ, fmin T ρ := tsum_nonneg (vgt hTpos.le)
  set A := u ^ 2 / (8 * π) - 0.2985 * u + 1.76 with hA
  have hFA : ∑' ρ, fmin T ρ ≤ A := hF.trans hq
  have hA0 : 0 ≤ A := hF0.trans hFA
  have hAu : A ≤ u ^ 2 / (8 * π) := by rw [hA]; linarith
  have hsq : √(x + h) ≤ s + 2.85 := by
    rw [show s + 2.85 = √((s + 2.85) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    have e : (s + 2.85) ^ 2 = s ^ 2 + 5.7 * s + 8.1225 := by ring
    have hle : x + h ≤ (s + 2.85) ^ 2 := by rw [e, hs2]; linarith
    exact Real.sqrt_le_sqrt hle
  have hz : √(x + h) * ∑' ρ, fmin T ρ ≤ (s + 2.85) * A :=
    mul_le_mul hsq hFA hF0 (by linarith)
  have hh3 : 1.5 / (h : ℝ) ≤ 0.01 := by rw [div_le_iff₀ hh0]; linarith
  calc |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin T ρ := hB
    _ ≤ (2 * r * s + 1) / 2 + 3.6 + 0.01 + (s * A + 2.85 * A) := by
        have : (s + 2.85) * A = s * A + 2.85 * A := by ring
        linarith
    _ ≤ s * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) := vjN hs5 hw2 qf9 qij hAu hrhi hA
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev
lemma vhC {x : ℝ} (hx : 0 ≤ x) :
    ∃ a : ℝ, 0 ≤ a ∧ x = a ^ 12 ∧ x ^ (2 : ℝ)⁻¹ = a ^ 6 ∧ x ^ (3 : ℝ)⁻¹ = a ^ 4 := by
  refine ⟨x ^ ((1 : ℝ) / 12), by positivity, ?_, ?_, ?_⟩ <;>
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev
lemma vkd {q : ℝ} (hq : 0 < q) (n : ℕ) : Real.log (q ^ n) ≤ n * q := by
 rw [Real.log_pow]
 have := Real.log_le_sub_one_of_pos hq
 have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
 nlinarith
lemma vjx (hRH : RiemannHypothesis) (hR : vbc) {y : ℝ} (hy : 10 ^ 10 ≤ y) :
    ψ y ≤ 1.0026 * y := by
  have hp := Real.pi_gt_d4
  have h := (abs_le.mp (vhA hRH hR hy)).2
  have hy0 : 0 < y := by linarith
  set u := Real.log y
  have hu0 : 33 * 0.6931471803 ≤ u := by
    have h1 := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 33 ≤ y by norm_num; linarith)
    rw [Real.log_pow] at h1; push_cast at h1
    linarith [vaR.1]
  set q := √(√(√(√y))) with hq
  have hq0 : 0 < q := by positivity
  have qea : q ^ 16 = y := by
    have h1 : √y ^ 2 = y := Real.sq_sqrt hy0.le
    have h2 : √(√y) ^ 2 = √y := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : √(√(√y)) ^ 2 = √(√y) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h4 : q ^ 2 = √(√(√y)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc q ^ 16 = (((q ^ 2) ^ 2) ^ 2) ^ 2 := by ring
      _ = y := by rw [h4, h3, h2, h1]
  have hsy : √y = q ^ 8 := by
    rw [← qea, show q ^ 16 = (q ^ 8) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hq4 : 4.2 ≤ q := by
    by_contra hc; push Not at hc
    have : q ^ 16 < 4.2 ^ 16 := pow_lt_pow_left₀ hc hq0.le (by norm_num)
    rw [qea] at this; norm_num at this; linarith
  have hlu : u ≤ 16 * q := by
    have := vkd hq0 16; rw [qea] at this; push_cast at this; exact this
  have qp7 : 0 ≤ u := by linarith
  have hneg : -0.2985 * u + 4.62 ≤ 0 := by linarith
  have hu2 : u ^ 2 ≤ 256 * q ^ 2 := by nlinarith
  have h8 : u ^ 2 / (8 * π) ≤ u ^ 2 / 25.13 :=
    div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) (by linarith)
  have hkey : √y * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) ≤ 0.0026 * y := by
    rw [hsy, ← qea]
    have hq8 : 0 < q ^ 8 := by positivity
    have e1 : q ^ 8 * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) ≤ q ^ 8 * (u ^ 2 / 25.13) :=
      mul_le_mul_of_nonneg_left (by linarith) hq8.le
    have e2 : q ^ 8 * (u ^ 2 / 25.13) ≤ q ^ 8 * (256 * q ^ 2 / 25.13) :=
      mul_le_mul_of_nonneg_left (by gcongr) hq8.le
    have e3 : q ^ 8 * (256 * q ^ 2 / 25.13) ≤ 0.0026 * q ^ 16 := by
      have : 256 / 25.13 ≤ 0.0026 * q ^ 6 := by
        have : (4.2 : ℝ) ^ 6 ≤ q ^ 6 := pow_le_pow_left₀ (by norm_num) hq4 6
        nlinarith
      have e : q ^ 8 * (256 * q ^ 2 / 25.13) = q ^ 10 * (256 / 25.13) := by ring
      rw [e, show (0.0026 : ℝ) * q ^ 16 = q ^ 10 * (0.0026 * q ^ 6) by ring]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  linarith
lemma vjP (hC : ved) {y : ℝ} (h1 : 1500 ≤ y) (h2 : y ≤ 10 ^ 10) :
  ψ y ≤ y + 0.8 * √y := by
 have := (abs_le.mp (hC y h1 h2)).2; linarith
lemma vhF (hRH : RiemannHypothesis) (hR : vbc) (hC : ved) {y c : ℝ}
    (hy : 1500 ≤ y) (hc : 0.0026 ≤ c) (hcy : 0.8 ≤ c * √y) : ψ y ≤ (1 + c) * y := by
  rcases le_or_gt y (10 ^ 10) with h | h
  · have := vjP hC hy h
    have hsy : √y * √y = y := Real.mul_self_sqrt (by linarith)
    have h3 := mul_le_mul_of_nonneg_right hcy (Real.sqrt_nonneg y)
    have : c * √y * √y = c * y := by rw [mul_assoc, hsy]
    linarith
  · have := vjx hRH hR h.le
    nlinarith
theorem vgQ (hRH : RiemannHypothesis) (hR : vbc) (hC : ved) {x : ℝ}
  (hx : 10 ^ 10 ≤ x) :
  |θ x - x| ≤ √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 5.667) := by
 have hx0 : 0 ≤ x := by linarith
 have hψ := abs_le.mp (vhA hRH hR hx)
 have h1 := theta_le_psi x
 have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
 have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
  psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
 obtain ⟨a, ha0, hxa, h2, h3⟩ := vhC hx0
 rw [h2, h3] at hCP
 rw [h3] at h53
 have hsx : √x = a ^ 6 := by
  rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
 have ha2 : 46.41 ≤ a ^ 2 := by
  by_contra hc; push Not at hc
  have : (a ^ 2) ^ 6 < 46.41 ^ 6 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  rw [← pow_mul] at this; norm_num at this; linarith
 have ha6 : 100000 ≤ a ^ 6 := by
  by_contra hc; push Not at hc
  have : (a ^ 6) ^ 2 < 100000 ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  rw [← pow_mul] at this; norm_num at this; linarith
 have ha4 : 2153 ≤ a ^ 4 := by
  have : (46.41 : ℝ) ^ 2 ≤ (a ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) ha2 2
  rw [← pow_mul] at this; norm_num at this; linarith
 have qlx : √(a ^ 6) = a ^ 3 := by
  rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
 have qly : √(a ^ 4) = a ^ 2 := by
  rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
 have ha3 : 316 ≤ a ^ 3 := by
  by_contra hc; push Not at hc
  have : (a ^ 3) ^ 2 < 316 ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  rw [← pow_mul] at this; norm_num at this; linarith
 have hp6 : ψ (a ^ 6) ≤ (1 + 0.0026) * a ^ 6 :=
  vhF hRH hR hC (by linarith) le_rfl (by rw [qlx]; linarith)
 have hp4 : ψ (a ^ 4) ≤ (1 + 0.0173) * a ^ 4 :=
  vhF hRH hR hC (by linarith) (by norm_num) (by rw [qly]; linarith)
 have hz : a ^ 4 ≤ 0.02155 * a ^ 6 := by
  have : a ^ 6 = a ^ 4 * a ^ 2 := by ring
  rw [this]; nlinarith [pow_nonneg ha0 4]
 have hD : ψ x - θ x ≤ 1.047 * √x := by rw [hsx]; linarith
 rw [abs_le]
 have e : √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 5.667)
   = √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 4.62) + 1.047 * √x := by ring
 rw [e]
 have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
 constructor <;> nlinarith [hψ.1, hψ.2]
theorem vhj (hC : ved) {x : ℝ} (hx1 : 30000 ≤ x) (hx2 : x ≤ 10 ^ 10) :
  |θ x - x| ≤ 3.9252 * √x := by
 have hx0 : 0 ≤ x := by linarith
 have hψ := abs_le.mp (hC x (by linarith) hx2)
 have h1 := theta_le_psi x
 have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
 have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
  psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
 obtain ⟨a, ha0, hxa, h2, h3⟩ := vhC hx0
 rw [h2, h3] at hCP
 rw [h3] at h53
 have hsx : √x = a ^ 6 := by
  rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
 have ha : 2.36 ≤ a := by
  by_contra hc; push Not at hc
  have : a ^ 12 < 2.36 ^ 12 := pow_lt_pow_left₀ hc ha0 (by norm_num)
  norm_num at this; linarith
 have ha1 : 1 ≤ a := by linarith
 set ℓ := Real.log a with hℓ
 have hL : Real.log x = 12 * ℓ := by rw [hxa, Real.log_pow]; push_cast; ring
 have hℓlo : 0.8456 ≤ ℓ := by
  have e : Real.log 2.36 = Real.log 2 + Real.log 1.18 := by
   rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.18 by norm_num)
  have h2 := Real.log_le_log (by norm_num) ha
  have := vaR.1
  rw [e, ← hℓ] at h2
  have : (0.1525 : ℝ) ≤ 1 - (1.18 : ℝ)⁻¹ := by norm_num
  linarith
 have hℓhi : ℓ ≤ a / 2.718 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < a / Real.exp 1 by positivity)
  rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at h1
  have : a / Real.exp 1 ≤ a / 2.718 :=
   div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith [Real.exp_one_gt_d9])
  linarith
 have hl4 : Real.log 4 ≤ 1.3863 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
  linarith [Real.log_two_lt_d9]
 have hp6 := psi_le (x := a ^ 6) (one_le_pow₀ ha1)
 have hp4 := psi_le (x := a ^ 4) (one_le_pow₀ ha1)
 rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp6
 rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp4
 rw [show (a ^ 3) ^ 2 = a ^ 6 by ring] at hp6
 rw [show (a ^ 2) ^ 2 = a ^ 4 by ring] at hp4
 rw [Real.log_pow] at hp6 hp4
 push_cast at hp6 hp4
 rw [← hℓ] at hp6 hp4
 have ha2 : 5.5696 ≤ a ^ 2 := by nlinarith
 have ha3 : 13.144 ≤ a ^ 3 := by nlinarith
 have hℓ0 : 0 ≤ ℓ := by linarith
 have h42 : a ^ 4 * 5.5696 ≤ a ^ 6 := by
  have := mul_le_mul_of_nonneg_left ha2 (pow_nonneg ha0 4)
  have e : a ^ 4 * a ^ 2 = a ^ 6 := by ring
  linarith
 have h33 : a ^ 3 * 13.144 ≤ a ^ 6 := by
  have := mul_le_mul_of_nonneg_left ha3 (pow_nonneg ha0 3)
  have e : a ^ 3 * a ^ 3 = a ^ 6 := by ring
  linarith
 have e1 : 2 * a ^ 3 * (6 * ℓ) ≤ 0.793 * a ^ 6 := by
  have s1 := mul_le_mul_of_nonneg_left hℓhi (pow_nonneg ha0 3)
  have e : a ^ 3 * (a / 2.718) = a ^ 4 / 2.718 := by ring
  have e' : 2 * a ^ 3 * (6 * ℓ) = 12 * (a ^ 3 * ℓ) := by ring
  rw [e'] at ⊢; rw [e] at s1
  have h6 := pow_nonneg ha0 6
  have qlz := h42
  norm_num at s1 qlz ⊢
  linarith
 have e2 : 2 * (Real.log 4 * a ^ 4) ≤ 0.4979 * a ^ 6 := by
  have := mul_le_mul_of_nonneg_right hl4 (pow_nonneg ha0 4)
  have := pow_nonneg ha0 6
  linarith
 have e3 : 2 * (2 * a ^ 2 * (4 * ℓ)) ≤ 0.448 * a ^ 6 := by
  have s1 := mul_le_mul_of_nonneg_left hℓhi (pow_nonneg ha0 2)
  have e : a ^ 2 * (a / 2.718) = a ^ 3 / 2.718 := by ring
  have e' : 2 * (2 * a ^ 2 * (4 * ℓ)) = 16 * (a ^ 2 * ℓ) := by ring
  rw [e']; rw [e] at s1
  have h6 := pow_nonneg ha0 6
  have qlA := h33
  norm_num at s1 qlA ⊢
  linarith
 have hD : ψ x - θ x ≤ (1.3863 + 0.793 + 0.4979 + 0.448) * a ^ 6 := by
  have := mul_le_mul_of_nonneg_right hl4 (pow_nonneg ha0 6)
  linarith
 rw [hsx]
 rw [hsx] at hψ
 rw [abs_le]
 have ha6 : 0 ≤ a ^ 6 := by positivity
 constructor <;> linarith [hψ.1, hψ.2]
end Schoenfeld
end
section
namespace Schoenfeld
open Chebyshev Real
def vdA : Prop :=
 ∀ x : ℝ, 599 ≤ x → x ≤ 30000 → |θ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2)
def vjz : Prop :=
 ∀ x : ℝ, 2657 ≤ x → x ≤ 400000 →
  |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < 1 / (8 * π) * (√x * Real.log x)
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev MeasureTheory
lemma vgS : 0 ≤ logIntegralTwo := by
 have := Real.logIntegral_two_pos; rw [Real.logIntegral_two] at this; exact this.le
lemma vgK : logIntegralTwo ≤ 2 := by
  unfold logIntegralTwo
  calc ∫ u in Set.Ioo (0 : ℝ) 1, (1 / Real.log (1 + u) + 1 / Real.log (1 - u))
      ≤ ∫ u in Set.Ioo (0 : ℝ) 1, (2 : ℝ) :=
        setIntegral_mono_on Real.logIntegralTwo_integrand_integrableOn
          (integrableOn_const (hs := by simp) (hC := by simp)) measurableSet_Ioo
          (fun u hu => Real.logIntegralTwo_integrand_le_two hu.1 hu.2)
    _ = 2 := by simp
lemma vbk {t : ℝ} (ht : 2 ≤ t) : 0 < Real.log t := Real.log_pos (by linarith)
lemma vcj {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (n : ℕ) :
  ContinuousOn (fun t : ℝ => 1 / Real.log t ^ n) (Set.uIcc a b) := by
 intro t ht
 rw [Set.uIcc_of_le hab] at ht
 have ht0 : t ≠ 0 := by linarith [ht.1]
 have hl : Real.log t ^ n ≠ 0 := pow_ne_zero _ (vbk (by linarith [ht.1])).ne'
 exact (continuousAt_const.div ((Real.continuousAt_log ht0).pow n) hl).continuousWithinAt
theorem vja {x : ℝ} (hx : 2 ≤ x) :
  logIntegral x = logIntegralTwo + x / Real.log x - 2 / Real.log 2
   + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
 have i1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 1) volume 2 x :=
  (vcj le_rfl hx 1).intervalIntegrable
 have i2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
  (vcj le_rfl hx 2).intervalIntegrable
 have hFTC : ∫ t in (2 : ℝ)..x, (1 / Real.log t ^ 1 - 1 / Real.log t ^ 2)
   = x / Real.log x - 2 / Real.log 2 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t / Real.log t)
   (fun t ht => ?_) (i1.sub i2)
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl := (vbk ht.1).ne'
  have := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
  convert this using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
 rw [intervalIntegral.integral_sub i1 i2] at hFTC
 simp only [pow_one] at hFTC
 unfold logIntegral
 linarith
noncomputable def qI (t : ℝ) : ℝ := θ t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2
lemma vcz {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
  IntervalIntegrable qI volume a b := by
 have h1 : IntervalIntegrable (fun t => θ t / (t * Real.log t ^ 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc ha le_rfl)
 exact h1.sub (vcj ha hab 2).intervalIntegrable
lemma vjS {t : ℝ} (ht : 2 ≤ t) : qI t = (θ t - t) / (t * Real.log t ^ 2) := by
 have ht0 : t ≠ 0 := by linarith
 have hl := (vbk ht).ne'
 unfold qI; field_simp
lemma vhZ {t : ℝ} (ht : 2 ≤ t) : |qI t| ≤ 1 / Real.log t ^ 2 := by
 have ht0 : 0 < t := by linarith
 have hl := vbk ht
 rw [vjS ht, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2),
  div_le_div_iff₀ (by positivity) (by positivity)]
 have h1 := theta_nonneg t
 have h2 := theta_le_log4_mul_x ht0.le
 have h4 : Real.log 4 ≤ 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
  linarith [Real.log_two_lt_d9]
 have : |θ t - t| ≤ t := by rw [abs_le]; constructor <;> nlinarith
 nlinarith [sq_nonneg (Real.log t)]
lemma vjJ {a b ℓ : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hℓ : 0 < ℓ) (hℓa : ℓ ≤ Real.log a) :
    |∫ t in a..b, qI t| ≤ (b - a) / ℓ ^ 2 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := qI)
    (C := 1 / ℓ ^ 2) (fun t ht => by
      rw [Set.uIoc_of_le hab] at ht
      rw [Real.norm_eq_abs]
      refine (vhZ (by linarith [ht.1])).trans ?_
      have hl : ℓ ≤ Real.log t := hℓa.trans (Real.log_le_log (by linarith) ht.1.le)
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hℓ.le hl 2))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at this
  calc _ ≤ 1 / ℓ ^ 2 * (b - a) := this
    _ = (b - a) / ℓ ^ 2 := by ring
lemma vdX (k : ℕ) (hk : 1 ≤ k) {b : ℝ} (hb : (2 : ℝ) ^ k ≤ b) :
    |∫ t in (2 : ℝ) ^ k..b, qI t| ≤ (b - 2 ^ k) / (k * 0.6931471803) ^ 2 := by
  refine vjJ ?_ hb (by positivity) ?_
  · calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  · rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg k)
theorem vgN : |∫ t in (2 : ℝ)..599, qI t| ≤ 33 := by
 have I := fun a b (ha : (2 : ℝ) ≤ a) (hab : a ≤ b) => vcz ha hab
 have s1 := vdX 1 le_rfl (b := 4) (by norm_num)
 have s2 := vdX 2 (by norm_num) (b := 8) (by norm_num)
 have s3 := vdX 3 (by norm_num) (b := 16) (by norm_num)
 have s4 := vdX 4 (by norm_num) (b := 32) (by norm_num)
 have s5 := vdX 5 (by norm_num) (b := 64) (by norm_num)
 have s6 := vdX 6 (by norm_num) (b := 128) (by norm_num)
 have s7 := vdX 7 (by norm_num) (b := 256) (by norm_num)
 have s8 := vdX 8 (by norm_num) (b := 512) (by norm_num)
 have s9 := vdX 9 (by norm_num) (b := 599) (by norm_num)
 replace s1 := abs_le.mp s1; replace s2 := abs_le.mp s2; replace s3 := abs_le.mp s3
 replace s4 := abs_le.mp s4; replace s5 := abs_le.mp s5; replace s6 := abs_le.mp s6
 replace s7 := abs_le.mp s7; replace s8 := abs_le.mp s8; replace s9 := abs_le.mp s9
 norm_num at s1 s2 s3 s4 s5 s6 s7 s8 s9
 have e : ∫ t in (2 : ℝ)..599, qI t
   = (∫ t in (2 : ℝ)..4, qI t) + (∫ t in (4 : ℝ)..8, qI t) + (∫ t in (8 : ℝ)..16, qI t)
    + (∫ t in (16 : ℝ)..32, qI t) + (∫ t in (32 : ℝ)..64, qI t)
    + (∫ t in (64 : ℝ)..128, qI t) + (∫ t in (128 : ℝ)..256, qI t)
    + (∫ t in (256 : ℝ)..512, qI t) + (∫ t in (512 : ℝ)..599, qI t) := by
  simp only [intervalIntegral.integral_add_adjacent_intervals (I 2 4 (by norm_num) (by norm_num))
   (I 4 8 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
   (I 2 8 (by norm_num) (by norm_num)) (I 8 16 (by norm_num) (by norm_num)),
   intervalIntegral.integral_add_adjacent_intervals (I 2 16 (by norm_num) (by norm_num))
   (I 16 32 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
   (I 2 32 (by norm_num) (by norm_num)) (I 32 64 (by norm_num) (by norm_num)),
   intervalIntegral.integral_add_adjacent_intervals (I 2 64 (by norm_num) (by norm_num))
   (I 64 128 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
   (I 2 128 (by norm_num) (by norm_num)) (I 128 256 (by norm_num) (by norm_num)),
   intervalIntegral.integral_add_adjacent_intervals (I 2 256 (by norm_num) (by norm_num))
   (I 256 512 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
   (I 2 512 (by norm_num) (by norm_num)) (I 512 599 (by norm_num) (by norm_num))]
 rw [e, abs_le]
 constructor <;> linarith [s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2, s5.1, s5.2, s6.1,
  s6.2, s7.1, s7.2, s8.1, s8.2, s9.1, s9.2]
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev MeasureTheory
theorem vhz {x : ℝ} (hx2 : 2 ≤ x) :
  (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x
   = (θ x - x) / Real.log x + (∫ t in (2 : ℝ)..x, qI t)
    + (2 / Real.log 2 - logIntegralTwo) := by
 have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
 have hli := vja hx2
 have hI1 : IntervalIntegrable (fun t => θ t / (t * Real.log t ^ 2)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx2]
  exact integrableOn_theta_div_id_mul_log_sq x
 have hI2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
  (vcj le_rfl hx2 2).intervalIntegrable
 have hg : ∫ t in (2 : ℝ)..x, qI t
   = (∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)) - ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
  intervalIntegral.integral_sub hI1 hI2
 rw [hpi, hli, hg, sub_div, div_eq_mul_inv]; ring
lemma vgI : |2 / Real.log 2 - logIntegralTwo| ≤ 2.886 := by
 have hli2 := vgS
 have hli2' := vgK
 have hlog2 := Real.log_two_gt_d9
 have h2l : 2 / Real.log 2 ≤ 2.886 := by rw [div_le_iff₀ (by linarith)]; nlinarith
 have h2l' : 2 ≤ 2 / Real.log 2 := by
  rw [le_div_iff₀ (by linarith)]; linarith [Real.log_two_lt_d9]
 rw [abs_le]; constructor <;> linarith
lemma vdb {a b : ℝ} {G : ℝ → ℝ} (hab : a ≤ b)
  (hb : ∀ t ∈ Set.Ioc a b, |qI t| ≤ G t) (hG : IntervalIntegrable G volume a b) :
  |∫ t in a..b, qI t| ≤ ∫ t in a..b, G t := by
 have := intervalIntegral.norm_integral_le_of_norm_le hab
  (ae_of_all _ fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht) hG
 rwa [Real.norm_eq_abs] at this
lemma vgf (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, c / √t = 2 * c * (√b - √a) := by
  have hint : IntervalIntegrable (fun t => c / √t) volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr (by linarith [ht.1])).ne').continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2 * c * √t)
    (fun t ht => ?_) hint]
  · ring
  · rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have := (Real.hasDerivAt_sqrt ht0).const_mul (2 * c)
    convert this using 1
    all_goals try with_reducible_and_instances rfl
    have : 0 < √t := Real.sqrt_pos.mpr (by linarith [ht.1])
    field_simp
lemma vfW {a b L : ℝ} (ha : 1 < a) (hab : a ≤ b) (hL : 4 < L)
    (hLa : L ≤ Real.log a) :
    ∫ t in a..b, 1 / (√t * Real.log t ^ 2) ≤ L / (L - 4) * (2 * √b / Real.log b ^ 2) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ L ≤ Real.log t := fun t ht =>
    ⟨by linarith [ht.1], hLa.trans (Real.log_le_log (by linarith) ht.1)⟩
  set F : ℝ → ℝ := fun t => 2 * √t / Real.log t ^ 2 with hF
  set F' : ℝ → ℝ := fun t => 1 / (√t * Real.log t ^ 2) - 4 / (√t * Real.log t ^ 3) with hF'
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs := Real.hasDerivAt_sqrt ht0.ne'
    have hl := Real.hasDerivAt_log ht0.ne'
    have h := (hs.const_mul 2).div (hl.pow 2) (pow_pos hl0 2).ne'
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ t = r ^ 2 :=
      ⟨√t, Real.sqrt_pos.mpr ht0, (Real.sq_sqrt ht0.le).symm⟩
    rw [Real.sqrt_sq hr0.le]
    simp only [hF', Pi.pow_apply]
    rw [Real.sqrt_sq hr0.le]
    generalize Real.log (r ^ 2) = ℓ at *
    field_simp
    ring
  have hcont : ∀ t ∈ Set.uIcc a b, ContinuousAt (fun t => 1 / (√t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    exact continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul
      ((Real.continuousAt_log ht0.ne').pow 2)) (mul_pos hs0 (pow_pos hl0 2)).ne'
  have hcont' : ∀ t ∈ Set.uIcc a b, ContinuousAt F' t := by
    intro t ht
    have hc1 := hcont t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    exact hc1.sub (continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul
      ((Real.continuousAt_log ht0.ne').pow 3)) (mul_pos hs0 (pow_pos hl0 3)).ne')
  have hi1 : IntervalIntegrable (fun t => 1 / (√t * Real.log t ^ 2)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht => (hcont t ht).continuousWithinAt
  have hi2 : IntervalIntegrable F' volume a b :=
    ContinuousOn.intervalIntegrable fun t ht => (hcont' t ht).continuousWithinAt
  have hle : ∫ t in a..b, 1 / (√t * Real.log t ^ 2) ≤ ∫ t in a..b, L / (L - 4) * F' t := by
    refine intervalIntegral.integral_mono_on hab hi1 (hi2.const_mul _) fun t ht => ?_
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    simp only [hF']
    rw [show 1 / (√t * Real.log t ^ 2) - 4 / (√t * Real.log t ^ 3)
      = 1 / (√t * Real.log t ^ 2) * (1 - 4 / Real.log t) by field_simp]
    have hA : 0 < 1 / (√t * Real.log t ^ 2) := by
      have := mul_pos hs (pow_pos hl0 2); positivity
    have hq : 1 ≤ L / (L - 4) * (1 - 4 / Real.log t) := by
      have h1 : 4 / Real.log t ≤ 4 / L := div_le_div_of_nonneg_left (by norm_num) (by linarith) hlt
      have h4 : L * (4 / L) = 4 := by field_simp
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    calc 1 / (√t * Real.log t ^ 2) = 1 / (√t * Real.log t ^ 2) * 1 := by ring
      _ ≤ 1 / (√t * Real.log t ^ 2) * (L / (L - 4) * (1 - 4 / Real.log t)) :=
          mul_le_mul_of_nonneg_left hq hA.le
      _ = L / (L - 4) * (1 / (√t * Real.log t ^ 2) * (1 - 4 / Real.log t)) := by ring
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi2] at hle
  have hFa : 0 ≤ F a := by
    have := (hpos a ⟨le_rfl, hab⟩).1
    simp only [hF]; positivity
  have hc : 0 ≤ L / (L - 4) := div_nonneg (by linarith) (by linarith)
  calc _ ≤ L / (L - 4) * (F b - F a) := hle
    _ ≤ L / (L - 4) * F b := by nlinarith
    _ = _ := rfl
lemma viB {a b c₀ β γ d L : ℝ} (ha : 1 < a) (hab : a ≤ b) (hL0 : 0 < L)
  (hLa : L ≤ Real.log a) (hd : 0 ≤ d) (hkey : 4 * d ≤ (d + 2 * β - γ) * L) :
  ∫ t in a..b, (c₀ - β / Real.log t + γ / Real.log t ^ 2) / √t
   ≤ 2 * √b * (c₀ - β / Real.log b + d / Real.log b ^ 2)
    - 2 * √a * (c₀ - β / Real.log a + d / Real.log a ^ 2) := by
 have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ L ≤ Real.log t := fun t ht =>
  ⟨by linarith [ht.1], hLa.trans (Real.log_le_log (by linarith) ht.1)⟩
 set F : ℝ → ℝ := fun t => 2 * √t * (c₀ - β / Real.log t + d / Real.log t ^ 2) with hF
 set F' : ℝ → ℝ := fun t =>
  (c₀ - β / Real.log t + (d + 2 * β) / Real.log t ^ 2 - 4 * d / Real.log t ^ 3) / √t with hF'
 have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  obtain ⟨ht0, hlt⟩ := hpos t ht
  have hl0 : 0 < Real.log t := by linarith
  have hs := Real.hasDerivAt_sqrt ht0.ne'
  have hl := Real.hasDerivAt_log ht0.ne'
  have h := (hs.const_mul 2).mul ((hasDerivAt_const t c₀).sub ((hasDerivAt_const t β).div hl
   hl0.ne') |>.add ((hasDerivAt_const t d).div (hl.pow 2) (pow_pos hl0 2).ne'))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ t = r ^ 2 :=
   ⟨√t, Real.sqrt_pos.mpr ht0, (Real.sq_sqrt ht0.le).symm⟩
  simp only [hF', Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Nat.cast_ofNat]
  rw [Real.sqrt_sq hr0.le]
  generalize Real.log (r ^ 2) = ℓ at *
  field_simp
  ring
 have hcont : ∀ t ∈ Set.uIcc a b, 0 < t ∧ 0 < Real.log t ∧ 0 < √t := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  obtain ⟨ht0, hlt⟩ := hpos t ht
  exact ⟨ht0, by linarith, Real.sqrt_pos.mpr ht0⟩
 have hi1 : IntervalIntegrable (fun t => (c₀ - β / Real.log t + γ / Real.log t ^ 2) / √t)
   volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  obtain ⟨ht0, hl0, hs⟩ := hcont t ht
  have hl := Real.continuousAt_log ht0.ne'
  exact ((continuousAt_const.sub (continuousAt_const.div hl hl0.ne')).add
   (continuousAt_const.div (hl.pow 2) (pow_pos hl0 2).ne')).div
   Real.continuous_sqrt.continuousAt hs.ne' |>.continuousWithinAt
 have hi2 : IntervalIntegrable F' volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  obtain ⟨ht0, hl0, hs⟩ := hcont t ht
  have hl := Real.continuousAt_log ht0.ne'
  exact ((((continuousAt_const.sub (continuousAt_const.div hl hl0.ne')).add
   (continuousAt_const.div (hl.pow 2) (pow_pos hl0 2).ne')).sub
   (continuousAt_const.div (hl.pow 3) (pow_pos hl0 3).ne'))).div
   Real.continuous_sqrt.continuousAt hs.ne' |>.continuousWithinAt
 have hle := intervalIntegral.integral_mono_on hab hi1 hi2 fun t ht => by
  obtain ⟨ht0, hlt⟩ := hpos t ht
  have hl0 : 0 < Real.log t := by linarith
  have hs : 0 < √t := Real.sqrt_pos.mpr ht0
  simp only [hF']
  apply div_le_div_of_nonneg_right _ hs.le
  have hk : 4 * d ≤ (d + 2 * β - γ) * Real.log t := by
   have : 0 ≤ d + 2 * β - γ := by
    by_contra hc; push Not at hc; nlinarith
   nlinarith
  have : 4 * d / Real.log t ^ 3 ≤ (d + 2 * β - γ) / Real.log t ^ 2 := by
   rw [div_le_div_iff₀ (by positivity) (by positivity)]
   have : (d + 2 * β - γ) * Real.log t ^ 3 = ((d + 2 * β - γ) * Real.log t) * Real.log t ^ 2 := by
    ring
   rw [this]
   exact mul_le_mul_of_nonneg_right hk (by positivity)
  have e : (d + 2 * β) / Real.log t ^ 2 = γ / Real.log t ^ 2 + (d + 2 * β - γ) / Real.log t ^ 2 := by
   ring
  linarith
 rwa [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi2] at hle
lemma vfb {t K : ℝ} (ht : 2 ≤ t) (h : |θ t - t| ≤ √t * K) :
    |qI t| ≤ K / (√t * Real.log t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hl := vbk ht
  have hs : 0 < √t := Real.sqrt_pos.mpr ht0
  have hst : √t * √t = t := Real.mul_self_sqrt ht0.le
  rw [vjS ht, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : √t * K * (√t * Real.log t ^ 2) = K * (t * Real.log t ^ 2) := by
    rw [show √t * K * (√t * Real.log t ^ 2) = (√t * √t) * (K * Real.log t ^ 2) by ring, hst]; ring
  calc |θ t - t| * (√t * Real.log t ^ 2) ≤ √t * K * (√t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = K * (t * Real.log t ^ 2) := e
lemma vjA : 10.15 ≤ Real.log 30000 := by
 have := vez 14 (show (2 : ℝ) ^ 14 ≤ 30000 by norm_num)
 norm_num at this ⊢; linarith
lemma viG : 23.01 ≤ Real.log (10 ^ 10) := by
 have := vez 33 (show (2 : ℝ) ^ 33 ≤ 10 ^ 10 by norm_num)
 norm_num at this ⊢; linarith
lemma vjY : Real.log (10 ^ 10) ≤ 23.3 := by
 have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.25 by norm_num)
 have e : Real.log (10 ^ 10) = 10 * (3 * Real.log 2 + Real.log 1.25) := by
  rw [Real.log_pow, show (10 : ℝ) = 2 ^ 3 * 1.25 by norm_num,
   Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
 rw [e]; linarith [vaR.2]
theorem vgn (hS : vdA) : |∫ t in (599 : ℝ)..30000, qI t| ≤ 14 := by
  have hp := Real.pi_gt_d4
  have hb : ∀ t ∈ Set.Ioc (599 : ℝ) 30000, |qI t| ≤ 1 / (8 * π) / √t := by
    intro t ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have h := vfb ht2 (K := Real.log t ^ 2 / (8 * π)) (by
      have := (hS t ht.1.le ht.2).le
      calc |θ t - t| ≤ 1 / (8 * π) * (√t * Real.log t ^ 2) := this
        _ = √t * (Real.log t ^ 2 / (8 * π)) := by ring)
    have hl := vbk ht2
    have hs : 0 < √t := Real.sqrt_pos.mpr (by linarith)
    calc |qI t| ≤ _ := h
      _ = 1 / (8 * π) / √t := by field_simp
  have hint : IntervalIntegrable (fun t => 1 / (8 * π) / √t) volume 599 30000 := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr (by linarith [ht.1])).ne').continuousWithinAt
  refine (vdb (by norm_num) hb hint).trans ?_
  rw [vgf _ (by norm_num) (by norm_num)]
  have h1 : √(30000 : ℝ) ≤ 173.3 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : 0 ≤ √(599 : ℝ) := Real.sqrt_nonneg _
  have h3 : 1 / (8 * π) ≤ 0.0398 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h4 : 0 ≤ 1 / (8 * π) := by positivity
  nlinarith
theorem vgk (hC : ved) {b : ℝ} (hb1 : 30000 ≤ b) (hb2 : b ≤ 10 ^ 10) :
    |∫ t in (30000 : ℝ)..b, qI t| ≤ 3.9252 * (10.15 / (10.15 - 4) * (2 * √b / Real.log b ^ 2)) := by
  have hb : ∀ t ∈ Set.Ioc (30000 : ℝ) b, |qI t| ≤ 3.9252 * (1 / (√t * Real.log t ^ 2)) := by
    intro t ht
    have h1 := vhj hC ht.1.le (ht.2.trans hb2)
    have h2 : |θ t - t| ≤ √t * 3.9252 := by rw [mul_comm]; exact h1
    have h := vfb (by linarith [ht.1]) h2
    calc |qI t| ≤ _ := h
      _ = _ := by ring
  have hc : IntervalIntegrable (fun t => 1 / (√t * Real.log t ^ 2)) volume 30000 b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hb1] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    exact (continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul
      ((Real.continuousAt_log ht0.ne').pow 2)) (mul_pos hs0 (pow_pos hl0 2)).ne').continuousWithinAt
  have hint : IntervalIntegrable (fun t => 3.9252 * (1 / (√t * Real.log t ^ 2))) volume 30000 b :=
    hc.const_mul 3.9252
  refine (vdb hb1 hb hint).trans ?_
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (vfW (by norm_num) hb1 (by norm_num)
    vjA) (by norm_num)
noncomputable def qbx (ℓ : ℝ) : ℝ := 1 / (8 * π) - 0.2985 / ℓ + 6.2 / ℓ ^ 2
theorem vit (hRH : RiemannHypothesis) (hR : vbc) (hC : ved) {x : ℝ}
    (hx : 10 ^ 10 ≤ x) :
    |∫ t in (10 ^ 10 : ℝ)..x, qI t|
      ≤ 2 * √x * qbx (Real.log x) - 2 * 100000 * qbx (Real.log (10 ^ 10)) := by
  have hb : ∀ t ∈ Set.Ioc (10 ^ 10 : ℝ) x,
      |qI t| ≤ (1 / (8 * π) - 0.2985 / Real.log t + 5.667 / Real.log t ^ 2) / √t := by
    intro t ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have h := vfb ht2 (vgQ hRH hR hC ht.1.le)
    have hl := vbk ht2
    have hs : 0 < √t := Real.sqrt_pos.mpr (by linarith)
    calc |qI t| ≤ _ := h
      _ = _ := by field_simp
  have hint : IntervalIntegrable
      (fun t => (1 / (8 * π) - 0.2985 / Real.log t + 5.667 / Real.log t ^ 2) / √t)
      volume (10 ^ 10) x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    have hl := Real.continuousAt_log ht0.ne'
    exact ((continuousAt_const.sub (continuousAt_const.div hl hl0.ne')).add
      (continuousAt_const.div (hl.pow 2) (pow_pos hl0 2).ne')).div
      Real.continuous_sqrt.continuousAt hs0.ne' |>.continuousWithinAt
  refine (vdb hx hb hint).trans ?_
  have hL := viG
  have h := viB (c₀ := 1 / (8 * π)) (β := 0.2985) (γ := 5.667) (d := 6.2) (L := 22)
    (a := 10 ^ 10) (b := x) (by norm_num) hx (by norm_num) ((by norm_num : (22 : ℝ) ≤ 23.01).trans hL)
    (by norm_num) (by norm_num)
  have hs : √((10 : ℝ) ^ 10) = 100000 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
  rw [hs] at h
  unfold qbx
  linarith
lemma vep {x B : ℝ} {n : ℕ} (hx : 0 < x) (hB : 0 ≤ B) (hn0 : n ≠ 0)
    (hu : Real.log x ≤ n) (hn : (2.7182818286 : ℝ) ^ n ≤ B ^ 2) : √x ≤ B := by
  have h1 : x ≤ Real.exp n := by
    calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ Real.exp n := Real.exp_le_exp.mpr hu
  have h2 : Real.exp n < 2.7182818286 ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le hn0
  rw [Real.sqrt_le_left hB]
  linarith
theorem vkz (hC : ved) (hS : vdA) {x : ℝ} (h1 : 400000 ≤ x) (h2 : x ≤ 10 ^ 10) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| < 1 / (8 * π) * (√x * Real.log x) := by
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hp := Real.pi_lt_d4
  have hpi := Real.pi_pos
  rw [vhz hx2]
  have I := fun a b (ha : (2 : ℝ) ≤ a) (hab : a ≤ b) => vcz ha hab
  have hsplit : ∫ t in (2 : ℝ)..x, qI t = (∫ t in (2 : ℝ)..599, qI t)
      + (∫ t in (599 : ℝ)..30000, qI t) + ∫ t in (30000 : ℝ)..x, qI t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (I 2 599 (by norm_num) (by norm_num))
      (I 599 30000 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 30000 (by norm_num) (by norm_num))
      (I 30000 x (by norm_num) (by linarith))]
  rw [hsplit]
  have hI1 := vgN
  have hI2 := vgn hS
  have hI3 := vgk hC (b := x) (by linarith) h2
  have hc := vgI
  have hθ := vhj hC (x := x) (by linarith) h2
  set s := √x with qi2
  set u := Real.log x with qi3
  have hs : 632 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hu : 12.82 ≤ u := by
    have := vez 18 (show (2 : ℝ) ^ 18 ≤ x by norm_num; linarith)
    have : (2 : ℝ) ^ 18 / x ≤ 262144 / 400000 := by
      rw [div_le_div_iff₀ hx0 (by norm_num)]; norm_num; linarith
    norm_num at *; linarith
  have hu0 : 0 < u := by linarith
  have hA : |(θ x - x) / u| ≤ 3.9252 * (s / u) := by
    rw [abs_div, abs_of_pos hu0, mul_div_assoc']
    exact div_le_div_of_nonneg_right hθ hu0.le
  have h1u : s / u ≤ s / 12.82 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hu
  have hu2 : 164.35 ≤ u ^ 2 := by nlinarith
  have h2u : 2 * s / u ^ 2 ≤ 2 * s / 164.35 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hu2
  have hR : 0.51 * s ≤ 1 / (8 * π) * (s * u) := by
    rw [show 1 / (8 * π) * (s * u) = s * u / (8 * π) by ring, le_div_iff₀ (by positivity)]
    nlinarith
  set A := (θ x - x) / u
  set B1 := ∫ t in (2 : ℝ)..599, qI t
  set B2 := ∫ t in (599 : ℝ)..30000, qI t
  set B3 := ∫ t in (30000 : ℝ)..x, qI t
  set C := 2 / Real.log 2 - logIntegralTwo
  have a1 := abs_add_le (A + (B1 + B2 + B3)) C
  have a2 := abs_add_le A (B1 + B2 + B3)
  have a3 := abs_add_le (B1 + B2) B3
  have a4 := abs_add_le B1 B2
  have e : A + (B1 + B2 + B3) + C = A + (B1 + B2 + B3) + C := rfl
  have hk : 3.9252 * (10.15 / (10.15 - 4) * (2 * s / u ^ 2)) ≤ 6.479 * (2 * s / 164.35) := by
    have : (3.9252 : ℝ) * (10.15 / (10.15 - 4)) ≤ 6.479 := by norm_num
    have h0 : 0 ≤ 2 * s / u ^ 2 := by positivity
    calc 3.9252 * (10.15 / (10.15 - 4) * (2 * s / u ^ 2))
        = 3.9252 * (10.15 / (10.15 - 4)) * (2 * s / u ^ 2) := by ring
      _ ≤ 6.479 * (2 * s / u ^ 2) := mul_le_mul_of_nonneg_right this h0
      _ ≤ 6.479 * (2 * s / 164.35) := mul_le_mul_of_nonneg_left h2u (by norm_num)
  have hfin : 3.9252 * (s / 12.82) + 33 + 14 + 6.479 * (2 * s / 164.35) + 2.886 < 0.51 * s := by
    norm_num; linarith
  calc |A + (B1 + B2 + B3) + C| ≤ |A| + (|B1| + |B2| + |B3|) + |C| := by linarith
    _ < 1 / (8 * π) * (s * u) := by nlinarith
theorem vkq (hRH : RiemannHypothesis) (hR : vbc) (hC : ved)
    (hS : vdA) {x : ℝ} (hx : 10 ^ 10 ≤ x) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| < 1 / (8 * π) * (√x * Real.log x) := by
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hp := Real.pi_lt_d4
  have hp' := Real.pi_gt_d4
  have hpi := Real.pi_pos
  rw [vhz hx2]
  have I := fun a b (ha : (2 : ℝ) ≤ a) (hab : a ≤ b) => vcz ha hab
  have hsplit : ∫ t in (2 : ℝ)..x, qI t = (∫ t in (2 : ℝ)..599, qI t)
      + (∫ t in (599 : ℝ)..30000, qI t) + (∫ t in (30000 : ℝ)..10 ^ 10, qI t)
      + ∫ t in (10 ^ 10 : ℝ)..x, qI t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (I 2 599 (by norm_num) (by norm_num))
      (I 599 30000 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 30000 (by norm_num) (by norm_num))
      (I 30000 (10 ^ 10) (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 (10 ^ 10) (by norm_num) (by norm_num))
      (I (10 ^ 10) x (by norm_num) hx)]
  rw [hsplit]
  have hI1 := vgN
  have hI2 := vgn hS
  have hI3 := vgk hC (b := 10 ^ 10) (by norm_num) le_rfl
  have hI4 := vit hRH hR hC hx
  have hc := vgI
  have hθ := vgQ hRH hR hC hx
  have hlo := viG
  have hhi := vjY
  have qlB : √((10 : ℝ) ^ 10) = 100000 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
  rw [qlB] at hI3
  have qp8 : 3.9252 * (10.15 / (10.15 - 4) * (2 * 100000 / Real.log (10 ^ 10) ^ 2)) ≤ 2448 := by
    have : (23.01 : ℝ) ^ 2 ≤ Real.log (10 ^ 10) ^ 2 := pow_le_pow_left₀ (by norm_num) hlo 2
    have h0 : 2 * 100000 / Real.log (10 ^ 10) ^ 2 ≤ 2 * 100000 / 23.01 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
    have h3 : (3.9252 : ℝ) * (10.15 / (10.15 - 4)) * (2 * 100000 / (23.01 : ℝ) ^ 2) ≤ 2448 := by
      norm_num
    have h4 : (0 : ℝ) ≤ 3.9252 * (10.15 / (10.15 - 4)) := by norm_num
    calc (3.9252 : ℝ) * (10.15 / (10.15 - 4) * (2 * 100000 / Real.log (10 ^ 10) ^ 2))
        = 3.9252 * (10.15 / (10.15 - 4)) * (2 * 100000 / Real.log (10 ^ 10) ^ 2) := by ring
      _ ≤ 3.9252 * (10.15 / (10.15 - 4)) * (2 * 100000 / (23.01 : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h0 h4
      _ ≤ 2448 := h3
  have hr : 0.03823 ≤ qbx (Real.log (10 ^ 10)) := by
    unfold qbx
    set L := Real.log (10 ^ 10)
    have h1 : 0.2985 / L ≤ 0.2985 / 23.01 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
    have h2 : 6.2 / 23.3 ^ 2 ≤ 6.2 / L ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) hhi 2)
    have h3 : 0.0397886 ≤ 1 / (8 * π) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have h1' : 0.2985 / L ≤ 0.012973 := h1.trans (by norm_num)
    have h2' : 0.01142 ≤ 6.2 / L ^ 2 := (show (0.01142 : ℝ) ≤ 6.2 / 23.3 ^ 2 by norm_num).trans h2
    linarith
  set s := √x with qi2
  set u := Real.log x with qi3
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hu : 23.01 ≤ u := hlo.trans (Real.log_le_log (by norm_num) hx)
  have hu0 : 0 < u := by linarith
  have hA : |(θ x - x) / u| ≤ s * (u / (8 * π) - 0.2985 + 5.667 / u) := by
    rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |θ x - x| ≤ s * (u ^ 2 / (8 * π) - 0.2985 * u + 5.667) := hθ
      _ = s * (u / (8 * π) - 0.2985 + 5.667 / u) * u := by field_simp
  set p := 1 / (8 * π) with hpdef
  set q := 5.07 / u with hqdef
  set r := 12.4 / u ^ 2 with qi4
  set P := 2 * p - 0.2985 + q + r with hPdef
  have h2c : p ≤ 0.03979 := by rw [hpdef, div_le_iff₀ (by positivity)]; nlinarith
  have hsP : s * P ≤ 4100 := by
    rcases le_or_gt u 24 with h24 | h24
    · have hsb : s ≤ 162756 := vep (n := 24) hx0 (by norm_num) (by norm_num)
        (by exact_mod_cast h24) (by norm_num)
      have q1 : q ≤ 0.22034 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu).trans
        (by norm_num)
      have q2 : r ≤ 0.02343 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) hu 2)).trans (by norm_num)
      have hP : P ≤ 0.02485 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      have := mul_le_mul_of_nonneg_right hsb (show (0 : ℝ) ≤ 0.02485 by norm_num)
      linarith
    rcases le_or_gt u 25 with h25 | h25
    · have hsb : s ≤ 268340 := vep (n := 25) hx0 (by norm_num) (by norm_num)
        (by exact_mod_cast h25) (by norm_num)
      have q1 : q ≤ 0.21125 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h24.le).trans
        (by norm_num)
      have q2 : r ≤ 0.021528 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h24.le 2)).trans (by norm_num)
      have hP : P ≤ 0.01386 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      have := mul_le_mul_of_nonneg_right hsb (show (0 : ℝ) ≤ 0.01386 by norm_num)
      linarith
    rcases le_or_gt u 26 with h26 | h26
    · have hsb : s ≤ 442414 := vep (n := 26) hx0 (by norm_num) (by norm_num)
        (by exact_mod_cast h26) (by norm_num)
      have q1 : q ≤ 0.2028 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h25.le).trans
        (by norm_num)
      have q2 : r ≤ 0.01984 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h25.le 2)).trans (by norm_num)
      have hP : P ≤ 0.00373 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      have := mul_le_mul_of_nonneg_right hsb (show (0 : ℝ) ≤ 0.00373 by norm_num)
      linarith
    · have q1 : q ≤ 0.19501 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h26.le).trans
        (by norm_num)
      have q2 : r ≤ 0.018344 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h26.le 2)).trans (by norm_num)
      have hP : P ≤ 0 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      linarith
  have qp9 : |∫ t in (10 ^ 10 : ℝ)..x, qI t| ≤ 2 * s * qbx u - 2 * 100000 * 0.03823 := by
    have h5 := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 2 * 100000 by norm_num)
    exact hI4.trans (sub_le_sub_left h5 _)
  have hkey : s * (u / (8 * π) - 0.2985 + 5.667 / u) + 2 * s * qbx u
      = 1 / (8 * π) * (s * u) + s * P := by
    rw [hPdef, hpdef, hqdef, qi4]; unfold qbx; field_simp; ring
  set A := (θ x - x) / u
  set B1 := ∫ t in (2 : ℝ)..599, qI t
  set B2 := ∫ t in (599 : ℝ)..30000, qI t
  set B3 := ∫ t in (30000 : ℝ)..10 ^ 10, qI t
  set B4 := ∫ t in (10 ^ 10 : ℝ)..x, qI t
  set C := 2 / Real.log 2 - logIntegralTwo
  have a1 := abs_add_le (A + (B1 + B2 + B3 + B4)) C
  have a2 := abs_add_le A (B1 + B2 + B3 + B4)
  have a3 := abs_add_le (B1 + B2 + B3) B4
  have a4 := abs_add_le (B1 + B2) B3
  have a5 := abs_add_le B1 B2
  calc |A + (B1 + B2 + B3 + B4) + C| ≤ |A| + (|B1| + |B2| + |B3| + |B4|) + |C| := by linarith
    _ < 1 / (8 * π) * (s * u) := by linarith
theorem vfc (hRH : RiemannHypothesis) (hR : vbc) (hC : ved)
    (qiq : vdA) (qlC : vjz) : vjw := by
  intro x hx
  rcases le_or_gt x 400000 with h | h
  · exact qlC x hx h
  rcases le_or_gt x (10 ^ 10) with h' | h'
  · exact vkz hC qiq h.le h'
  · exact vkq hRH hR hC qiq h'.le
end Schoenfeld
end

theorem OMA.solution : OMA.R_OeisA38098_conjecture1_R1_H2_R1.H4 := by
 intro hRH hR hC hT hP
 exact Schoenfeld.vfc hRH hR hC hT hP
