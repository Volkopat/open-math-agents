import OMAStatements.S_mo_130387

-- Problem: Savings property: A transformation which turns nonnegative martingales into uniformly
-- integrable ones (https://mathoverflow.net/questions/130387).
-- Credit: @ricnov (the owner of the agent is credited as the solver)
-- Shortening uses the defining maxima, Martingale.setIntegral_eq, and domination of a constant
-- uniformly integrable family; the original savings construction and pathwise limits are retained.
--
-- Status. The source states the three facts proved here as known (it can be shown that ...) and
-- asks only whether probability theory has a name for such a transformation; the savings trick is
-- standard in algorithmic randomness. This file is a formal proof of a known result.
--
-- Proof. Along a path m = (M_n(w)) put U_0 = 1 and U_{n+1} = max(U_n, m_{n+1} + 1), so that
-- U_n = max(1, m_1 + 1, ..., m_n + 1). By induction (OMA.NL_sub, OMA.N_succ, OMA.L_succ)
--   N_n - L_n = (m_n + 1) / U_n,   N_{n+1} = N_n + (m_{n+1} - m_n) / U_n,
--   L_{n+1} = L_n + (U_{n+1} - U_n) / U_n,
-- hence 0 <= L_n <= N_n, N_{n+1} <= L_{n+1} + 1 and log U_n <= L_n <= U_n - 1.
-- (1) N_{n+1} - N_n is the martingale difference of M times the G_n-measurable weight 1 / U_n,
--     which lies in (0, 1]; so N is a martingale (OMA.N_martingale), and N >= L >= 0.
-- (2) Pathwise: limsup m = infinity iff U tends to infinity iff L tends to infinity iff N tends to
--     infinity (OMA.N_tendsto_of_limsup, OMA.limsup_of_N_tendsto).
-- (3) L is non-decreasing with E[L_n] <= E[N_n] = E[M_0] + 1, so by monotone convergence its limit
--     is integrable, and N_n <= M_0 + 2 + lim L. A sequence dominated by an integrable function is
--     uniformly integrable (OMA.ui_of_dominated, OMA.N_ui). A uniformly integrable martingale is
--     closed by its limit (Mathlib).

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OMA

/-- The pair `(N_n, L_n)` of the savings transformation along one path `m` of the martingale. -/
noncomputable def NL (m : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (m 0 + 1, 0)
  | n + 1 =>
      ((NL m n).1 + (m (n + 1) - m n) * (((NL m n).1 - (NL m n).2) / (m n + 1)),
        max ((NL m n).1 + (m (n + 1) - m n) * (((NL m n).1 - (NL m n).2) / (m n + 1)) - 1)
          (NL m n).2)

/-- The running maximum `max(1, m_1 + 1, ..., m_n + 1)`. -/
noncomputable def U (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => max (U m n) (m (n + 1) + 1)

lemma U_ge_one (m : ℕ → ℝ) (n : ℕ) : 1 ≤ U m n := by
  induction n with
  | zero => simp [U]
  | succ k ih => exact le_trans ih (le_max_left _ _)

lemma U_mono (m : ℕ → ℝ) : Monotone (U m) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

lemma U_ge (m : ℕ → ℝ) (n : ℕ) : m (n + 1) + 1 ≤ U m (n + 1) := le_max_right _ _

/-- The key invariant: `N_n - L_n = (m_n + 1) / U_n`. -/
lemma NL_sub (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n) (n : ℕ) :
    (NL m n).1 - (NL m n).2 = (m n + 1) / U m n := by
  induction n with
  | zero => simp [NL, U]
  | succ n ih =>
    have hu : 0 < U m n := lt_of_lt_of_le one_pos (U_ge_one m n)
    have hm1 : 0 < m n + 1 := by linarith [hm n]
    have hN : (NL m (n + 1)).1 = (NL m n).2 + (m (n + 1) + 1) / U m n := by
      have e : ((NL m n).1 - (NL m n).2) / (m n + 1) = 1 / U m n := by
        rw [ih]
        field_simp
      have e2 : (NL m n).1 = (NL m n).2 + (m n + 1) / U m n := by linarith
      simp only [NL]
      rw [e, e2]
      field_simp
      ring
    have hL : (NL m (n + 1)).2 = max ((NL m (n + 1)).1 - 1) (NL m n).2 := by simp only [NL]
    rw [hL, hN]
    simp only [U]
    rcases le_total (m (n + 1) + 1) (U m n) with h | h
    · rw [max_eq_left h]
      have h1 : (m (n + 1) + 1) / U m n ≤ 1 := (div_le_one hu).2 h
      rw [max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h]
      have h1 : 1 ≤ (m (n + 1) + 1) / U m n := (one_le_div hu).2 h
      rw [max_eq_left (by linarith)]
      have hm2 : (0:ℝ) < m (n + 1) + 1 := by linarith [hm (n + 1)]
      field_simp
      ring

lemma N_succ (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n) (n : ℕ) :
    (NL m (n + 1)).1 = (NL m n).1 + (m (n + 1) - m n) / U m n := by
  have hu : 0 < U m n := lt_of_lt_of_le one_pos (U_ge_one m n)
  have hm1 : 0 < m n + 1 := by linarith [hm n]
  have e : ((NL m n).1 - (NL m n).2) / (m n + 1) = 1 / U m n := by
    rw [NL_sub m hm n]
    field_simp
  simp only [NL]
  rw [e]
  ring

lemma L_succ (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n) (n : ℕ) :
    (NL m (n + 1)).2 = (NL m n).2 + (U m (n + 1) - U m n) / U m n := by
  have hu : 0 < U m n := lt_of_lt_of_le one_pos (U_ge_one m n)
  have h1 := NL_sub m hm n
  have h2 := NL_sub m hm (n + 1)
  have h3 := N_succ m hm n
  have hL : (NL m (n + 1)).2 = max ((NL m (n + 1)).1 - 1) (NL m n).2 := by simp only [NL]
  have hNL : (NL m (n + 1)).1 = (NL m n).2 + (m (n + 1) + 1) / U m n := by
    rw [h3]
    have : (NL m n).1 = (NL m n).2 + (m n + 1) / U m n := by linarith
    rw [this]
    field_simp
    ring
  rw [hL, hNL]
  simp only [U]
  rcases le_total (m (n + 1) + 1) (U m n) with h | h
  · rw [max_eq_left h]
    have h1' : (m (n + 1) + 1) / U m n ≤ 1 := (div_le_one hu).2 h
    rw [max_eq_right (by linarith)]
    simp
  · rw [max_eq_right h]
    have h1' : 1 ≤ (m (n + 1) + 1) / U m n := (one_le_div hu).2 h
    rw [max_eq_left (by linarith)]
    field_simp
    ring

lemma L_nonneg (m : ℕ → ℝ) (n : ℕ) : 0 ≤ (NL m n).2 := by
  induction n with
  | zero => simp [NL]
  | succ n ih => exact ih.trans (le_max_right _ _)

lemma L_mono (m : ℕ → ℝ) : Monotone fun n => (NL m n).2 := by
  exact monotone_nat_of_le_succ fun _ => le_max_right _ _

lemma N_ge_L (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n) (n : ℕ) : (NL m n).2 ≤ (NL m n).1 := by
  have h := NL_sub m hm n
  have hu : 0 < U m n := lt_of_lt_of_le one_pos (U_ge_one m n)
  have : 0 ≤ (m n + 1) / U m n := div_nonneg (by linarith [hm n]) hu.le
  linarith

lemma N_le_L_add_one (m : ℕ → ℝ) (n : ℕ) :
    (NL m (n + 1)).1 ≤ (NL m (n + 1)).2 + 1 := by
  have h : (NL m (n + 1)).1 - 1 ≤ (NL m (n + 1)).2 := le_max_left _ _
  linarith

/-- `L_n ≤ U_n - 1`. -/
lemma L_le_U (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n) (n : ℕ) : (NL m n).2 ≤ U m n - 1 := by
  induction n with
  | zero => simp [NL, U]
  | succ n ih =>
    rw [L_succ m hm n]
    have hu1 : 1 ≤ U m n := U_ge_one m n
    have hu : 0 < U m n := lt_of_lt_of_le one_pos hu1
    have hmono := U_mono m (Nat.le_succ n)
    have : (U m (n + 1) - U m n) / U m n ≤ U m (n + 1) - U m n :=
      div_le_self (by linarith) hu1
    linarith

/-- `log U_n ≤ L_n`. -/
lemma log_U_le_L (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n) (n : ℕ) : Real.log (U m n) ≤ (NL m n).2 := by
  induction n with
  | zero => simp [NL, U]
  | succ n ih =>
    rw [L_succ m hm n]
    have hu1 : 1 ≤ U m n := U_ge_one m n
    have hu : 0 < U m n := lt_of_lt_of_le one_pos hu1
    have hu' : 0 < U m (n + 1) := lt_of_lt_of_le one_pos (U_ge_one m (n + 1))
    have hlog : Real.log (U m (n + 1) / U m n) ≤ U m (n + 1) / U m n - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hu' hu)
    rw [Real.log_div hu'.ne' hu.ne'] at hlog
    have : (U m (n + 1) - U m n) / U m n = U m (n + 1) / U m n - 1 := by
      field_simp
    linarith

lemma savings_eq {Ω : Type} (M : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    OMA.S_mo_130387.savings M ω n = NL (fun k => M k ω) n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [OMA.S_mo_130387.savings, OMA.S_mo_130387.step, NL, ih]

lemma N_eq {Ω : Type} (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    OMA.S_mo_130387.N M n ω = (NL (fun k => M k ω) n).1 := by
  unfold OMA.S_mo_130387.N
  rw [savings_eq]

/-- If the path is unbounded, `N` tends to infinity. -/
lemma N_tendsto_of_limsup (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (h : limsup (fun n => (m n : EReal)) atTop = ⊤) :
    Tendsto (fun n => (NL m n).1) atTop atTop := by
  have hU : Tendsto (U m) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone (U_mono m) fun B => ?_
    have hlt : ((B : ℝ) : EReal) < limsup (fun n => (m n : EReal)) atTop := by
      rw [h]
      exact EReal.coe_lt_top B
    have hfreq : ∃ᶠ n in atTop, ((B : ℝ) : EReal) < (m n : EReal) :=
      frequently_lt_of_lt_limsup (by isBoundedDefault) hlt
    obtain ⟨n, hn, hn1⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hB : B < m (k + 1) := by exact_mod_cast hn
    exact ⟨k + 1, by linarith [U_ge m k]⟩
  have hL : Tendsto (fun n => (NL m n).2) atTop atTop :=
    tendsto_atTop_mono (fun n => log_U_le_L m hm n) (Real.tendsto_log_atTop.comp hU)
  exact tendsto_atTop_mono (fun n => N_ge_L m hm n) hL

/-- If `N` tends to infinity, the path is unbounded. -/
lemma limsup_of_N_tendsto (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (h : Tendsto (fun n => (NL m n).1) atTop atTop) :
    limsup (fun n => (m n : EReal)) atTop = ⊤ := by
  by_contra hne
  have hlt : limsup (fun n => (m n : EReal)) atTop < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨b, hb1, -⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hev : ∀ᶠ n in atTop, (m n : EReal) < (b : EReal) := eventually_lt_of_limsup_lt hb1
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hev
  have hUb : ∀ n, n0 ≤ n → U m n ≤ max (U m n0) (b + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ k hk ih =>
      simp only [U]
      refine max_le ih ?_
      have hmk : m (k + 1) < b := by exact_mod_cast hn0 (k + 1) (by omega)
      exact le_trans (by linarith) (le_max_right _ _)
  have hNb : ∀ n, n0 ≤ n → (NL m (n + 1)).1 ≤ max (U m n0) (b + 1) := by
    intro n hn
    have h1 := N_le_L_add_one m n
    have h2 := L_le_U m hm (n + 1)
    have h3 := hUb (n + 1) (by omega)
    linarith
  obtain ⟨n1, hn1⟩ := eventually_atTop.1 (tendsto_atTop.1 h (max (U m n0) (b + 1) + 1))
  have h4 := hn1 (max n1 n0 + 1) (by omega)
  have h5 := hNb (max n1 n0) (le_max_right _ _)
  linarith


/-! The probabilistic part. -/

lemma U_meas {Ω : Type} [m0 : MeasurableSpace Ω] {G : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hM : StronglyAdapted G M) (n : ℕ) :
    Measurable[G n] (fun ω => U (fun k => M k ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ k ih =>
    have h1 : Measurable[G (k + 1)] (fun ω => U (fun j => M j ω) k) :=
      ih.mono (G.mono (Nat.le_succ k)) le_rfl
    have h2 : Measurable[G (k + 1)] (fun ω => M (k + 1) ω + 1) :=
      (hM (k + 1)).measurable.add_const 1
    exact h1.max h2

lemma N_meas {Ω : Type} [m0 : MeasurableSpace Ω] {G : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hM : StronglyAdapted G M) (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ) :
    Measurable[G n] (fun ω => (NL (fun k => M k ω) n).1) := by
  induction n with
  | zero => exact (hM 0).measurable.add_const 1
  | succ k ih =>
    have hfun : (fun ω => (NL (fun j => M j ω) (k + 1)).1)
        = fun ω => (NL (fun j => M j ω) k).1
            + (M (k + 1) ω - M k ω) / U (fun j => M j ω) k := by
      funext ω
      exact N_succ (fun j => M j ω) (fun j => hnn j ω) k
    rw [hfun]
    have h1 : Measurable[G (k + 1)] (fun ω => (NL (fun j => M j ω) k).1) :=
      ih.mono (G.mono (Nat.le_succ k)) le_rfl
    have hk1 : Measurable[G (k + 1)] (M (k + 1)) := (hM (k + 1)).measurable
    have hk0 : Measurable[G (k + 1)] (M k) :=
      (hM k).measurable.mono (G.mono (Nat.le_succ k)) le_rfl
    have h2 : Measurable[G (k + 1)] (fun ω => M (k + 1) ω - M k ω) := hk1.sub hk0
    have h3 : Measurable[G (k + 1)] (fun ω => U (fun j => M j ω) k) :=
      (U_meas hM k).mono (G.mono (Nat.le_succ k)) le_rfl
    exact h1.add (h2.div h3)

lemma N_integrable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Martingale M G P) (hnn : ∀ n ω, 0 ≤ M n ω)
    (n : ℕ) : Integrable (fun ω => (NL (fun k => M k ω) n).1) P := by
  induction n with
  | zero => exact (hM.integrable 0).add (integrable_const 1)
  | succ k ih =>
    have hfun : (fun ω => (NL (fun j => M j ω) (k + 1)).1)
        = fun ω => (NL (fun j => M j ω) k).1
            + (M (k + 1) ω - M k ω) / U (fun j => M j ω) k := by
      funext ω
      exact N_succ (fun j => M j ω) (fun j => hnn j ω) k
    rw [hfun]
    refine ih.add ?_
    have hD : Integrable (fun ω => |M (k + 1) ω - M k ω|) P :=
      ((hM.integrable (k + 1)).sub (hM.integrable k)).abs
    have hk1 : Measurable (M (k + 1)) := (hM.1 (k + 1)).measurable.mono (G.le _) le_rfl
    have hk0 : Measurable (M k) := (hM.1 k).measurable.mono (G.le _) le_rfl
    have hmeas : Measurable (fun ω => (M (k + 1) ω - M k ω) / U (fun j => M j ω) k) :=
      (hk1.sub hk0).div ((U_meas hM.1 k).mono (G.le _) le_rfl)
    refine hD.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have hU1 : 1 ≤ U (fun j => M j ω) k := U_ge_one _ k
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le one_pos hU1)]
    exact div_le_self (abs_nonneg _) hU1

/-- Fact (1): `N` is a martingale. -/
lemma N_martingale {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Martingale M G P) (hnn : ∀ n ω, 0 ≤ M n ω) :
    Martingale (fun n ω => (NL (fun k => M k ω) n).1) G P := by
  refine martingale_of_condExp_sub_eq_zero_nat
    (fun n => (N_meas hM.1 hnn n).stronglyMeasurable) (fun n => N_integrable hM hnn n) fun i => ?_
  have hfun : ((fun ω => (NL (fun k => M k ω) (i + 1)).1) - fun ω => (NL (fun k => M k ω) i).1)
      = (fun ω => (U (fun k => M k ω) i)⁻¹) * (M (i + 1) - M i) := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [N_succ (fun k => M k ω) (fun k => hnn k ω) i]
    ring
  rw [hfun]
  have hξ : StronglyMeasurable[G i] (fun ω => (U (fun k => M k ω) i)⁻¹) :=
    (U_meas hM.1 i).inv.stronglyMeasurable
  have hbound : ∀ᵐ ω ∂P, ‖(U (fun k => M k ω) i)⁻¹‖ ≤ 1 := Eventually.of_forall fun ω => by
    have hU1 : 1 ≤ U (fun k => M k ω) i := U_ge_one _ i
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (lt_of_lt_of_le one_pos hU1))]
    exact inv_le_one_of_one_le₀ hU1
  have h1 := condExp_stronglyMeasurable_mul_of_bound (G.le i) hξ
    ((hM.integrable (i + 1)).sub (hM.integrable i)) 1 hbound
  have h2 := condExp_sub (hM.integrable (i + 1)) (hM.integrable i) (G i)
  have h3 := hM.2 i (i + 1) (Nat.le_succ i)
  have h4 := hM.2 i i le_rfl
  filter_upwards [h1, h2, h3, h4] with ω hω1 hω2 hω3 hω4
  rw [hω1]
  simp only [Pi.mul_apply, Pi.zero_apply]
  rw [hω2]
  simp only [Pi.sub_apply]
  rw [hω3, hω4, sub_self, mul_zero]

/-- A sequence dominated by an integrable function is uniformly integrable. -/
lemma ui_of_dominated {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (Z : Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hZ : Integrable Z P) (hdom : ∀ n, ∀ᵐ ω ∂P, |f n ω| ≤ Z ω) :
    UniformIntegrable f 1 P := by
  have hnorm : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ ‖Z ω‖ := fun n =>
    (hdom n).mono fun ω hω => hω.trans (le_abs_self _)
  obtain ⟨_, hu, C, hC⟩ := uniformIntegrable_const (ι := ℕ) le_rfl
    ENNReal.one_ne_top (memLp_one_iff_integrable.2 hZ)
  refine ⟨hf, ?_, C, fun n => (eLpNorm_mono_ae (hnorm n)).trans (hC n)⟩
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hu hε
  refine ⟨δ, hδ, fun n s hs hμs => (eLpNorm_mono_ae ?_).trans (hbound n s hs hμs)⟩
  filter_upwards [hnorm n] with ω hω
  simpa only [norm_indicator_eq_indicator_norm] using Set.indicator_le_indicator hω

/-- Fact (3): `N` is uniformly integrable. -/
lemma N_ui {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Martingale M G P) (hnn : ∀ n ω, 0 ≤ M n ω) :
    UniformIntegrable (fun n ω => (NL (fun k => M k ω) n).1) 1 P := by
  have hN := N_martingale hM hnn
  have hNm : ∀ n, Measurable (fun ω => (NL (fun k => M k ω) n).1) :=
    fun n => (N_meas hM.1 hnn n).mono (G.le n) le_rfl
  have hMm : ∀ n, Measurable (M n) := fun n => (hM.1 n).measurable.mono (G.le n) le_rfl
  have hUm : ∀ n, Measurable (fun ω => U (fun k => M k ω) n) :=
    fun n => (U_meas hM.1 n).mono (G.le n) le_rfl
  -- the savings account
  have hLfun : ∀ n, (fun ω => (NL (fun k => M k ω) n).2)
      = fun ω => (NL (fun k => M k ω) n).1 - (M n ω + 1) / U (fun k => M k ω) n := by
    intro n
    funext ω
    have := NL_sub (fun k => M k ω) (fun k => hnn k ω) n
    linarith
  have hLm : ∀ n, Measurable (fun ω => (NL (fun k => M k ω) n).2) := by
    intro n
    rw [hLfun n]
    exact (hNm n).sub (((hMm n).add_const 1).div (hUm n))
  have hLnn : ∀ n ω, 0 ≤ (NL (fun k => M k ω) n).2 :=
    fun n ω => L_nonneg (fun k => M k ω) n
  have hLle : ∀ n ω, (NL (fun k => M k ω) n).2 ≤ (NL (fun k => M k ω) n).1 :=
    fun n ω => N_ge_L (fun k => M k ω) (fun k => hnn k ω) n
  have hLint : ∀ n, Integrable (fun ω => (NL (fun k => M k ω) n).2) P := by
    intro n
    refine (hN.integrable n).mono' (hLm n).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hLnn n ω)]
    exact hLle n ω
  -- expectations
  have hEN : ∀ n, ∫ ω, (NL (fun k => M k ω) n).1 ∂P = ∫ ω, M 0 ω ∂P + 1 := by
    intro n
    simpa [NL, integral_add (hM.integrable 0) (integrable_const 1)] using
      (hN.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ).symm
  have hEL : ∀ n, ∫ ω, (NL (fun k => M k ω) n).2 ∂P ≤ ∫ ω, M 0 ω ∂P + 1 := by
    intro n
    rw [← hEN n]
    exact integral_mono (hLint n) (hN.integrable n) (hLle n)
  -- the limit of the savings account, in the extended nonnegative reals
  have hfm : ∀ n, Measurable (fun ω => ENNReal.ofReal (NL (fun k => M k ω) n).2) :=
    fun n => ENNReal.measurable_ofReal.comp (hLm n)
  have hfmono : Monotone (fun n ω => ENNReal.ofReal (NL (fun k => M k ω) n).2) :=
    fun i j hij ω => ENNReal.ofReal_le_ofReal (L_mono (fun k => M k ω) hij)
  have hYm : Measurable (fun ω => ⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2) :=
    Measurable.iSup hfm
  have hlin : ∫⁻ ω, ⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2 ∂P
      ≤ ENNReal.ofReal (∫ ω, M 0 ω ∂P + 1) := by
    rw [lintegral_iSup hfm hfmono]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hLint n) (Eventually.of_forall (hLnn n))]
    exact ENNReal.ofReal_le_ofReal (hEL n)
  have hfin : ∫⁻ ω, ⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2 ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hYint : Integrable (fun ω => (⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hYm.aemeasurable hfin
  have hae : ∀ᵐ ω ∂P, (⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2) < ⊤ := ae_lt_top hYm hfin
  -- domination
  refine ui_of_dominated _
    (fun ω => M 0 ω + 2 + (⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2).toReal)
    (fun n => (hNm n).aestronglyMeasurable)
    (((hM.integrable 0).add (integrable_const 2)).add hYint) fun n => ?_
  filter_upwards [hae] with ω hω
  have hY0 : 0 ≤ (⨆ n, ENNReal.ofReal (NL (fun k => M k ω) n).2).toReal := ENNReal.toReal_nonneg
  have hLY : ∀ k, (NL (fun j => M j ω) k).2
      ≤ (⨆ n, ENNReal.ofReal (NL (fun j => M j ω) n).2).toReal := by
    intro k
    have h1 : ENNReal.ofReal (NL (fun j => M j ω) k).2
        ≤ ⨆ n, ENNReal.ofReal (NL (fun j => M j ω) n).2 :=
      le_iSup (fun n => ENNReal.ofReal (NL (fun j => M j ω) n).2) k
    have h2 := ENNReal.toReal_mono hω.ne h1
    rwa [ENNReal.toReal_ofReal (hLnn k ω)] at h2
  have hNnn : 0 ≤ (NL (fun k => M k ω) n).1 := le_trans (hLnn n ω) (hLle n ω)
  rw [abs_of_nonneg hNnn]
  cases n with
  | zero =>
    have : (NL (fun k => M k ω) 0).1 = M 0 ω + 1 := by simp [NL]
    rw [this]
    linarith
  | succ k =>
    have h1 := N_le_L_add_one (fun j => M j ω) k
    have h2 := hLY (k + 1)
    have h3 := hnn 0 ω
    linarith

end OMA

theorem OMA.solution : type_of% @OMA.S_mo_130387.main := by
  intro Ω m0 P _ G M hM hnn
  have hNeq : OMA.S_mo_130387.N M = fun n ω => (OMA.NL (fun k => M k ω) n).1 := by
    funext n ω
    exact OMA.N_eq M n ω
  rw [hNeq]
  have hN := OMA.N_martingale hM hnn
  have hUI := OMA.N_ui hM hnn
  refine ⟨⟨hN, fun n ω => ?_⟩, fun ω => ⟨fun h => ?_, fun h => ?_⟩, hUI, ?_⟩
  · exact le_trans (OMA.L_nonneg (fun k => M k ω) n)
      (OMA.N_ge_L (fun k => M k ω) (fun k => hnn k ω) n)
  · exact OMA.N_tendsto_of_limsup (fun k => M k ω) (fun k => hnn k ω) h
  · exact OMA.limsup_of_N_tendsto (fun k => M k ω) (fun k => hnn k ω) h
  · obtain ⟨R, hR⟩ := hUI.2.2
    exact ⟨G.limitProcess (fun n ω => (OMA.NL (fun k => M k ω) n).1) P,
      (MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd hUI.1 hR).integrable le_rfl,
      fun n => hN.ae_eq_condExp_limitProcess hUI n⟩
