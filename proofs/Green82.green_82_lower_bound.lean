import FormalConjectures.GreensOpenProblems.«82»

/-!
# Green 82: a lower bound for zeros of cosine polynomials

We follow the structured-polynomial and sparse-product argument of Benjamin
Bedert, *An improved lower bound for a problem of Littlewood on the zeros of
cosine polynomials* (arXiv:2407.16075). Frequencies in the target are signed
and angles are measured in turns. Folding the frequencies gives coefficients
in {0, 1, 2} and preserves the value at zero.

* `solution_of_estimates` combines periodic structure and a root bound for
  structured polynomials, including the logarithmic inversion and the floor.
* `structuredRootEstimate_of_littlewood` uses a squared geometric sum and
  a direct estimate on the primitive of each constant-coefficient block.
* `sparseProductEstimate_of_littlewood` constructs the perturbed companion.
  Small product coefficients force an exact rational recurrence. A factorial
  is a common period for its torsion roots, and bounded integer second
  differences then vanish in the interior of a long interval.
* `littlewood_l1` proves the weighted exponential-sum inequality on the unit
  circle using an explicitly bounded test function on growing frequency blocks.

The last declaration applies these results to the type of the upstream theorem.
-/

namespace OMA.G82

open scoped BigOperators

/-- The coefficient of the cosine at natural frequency `k`. -/
def multiplicity (A : Finset ℤ) (k : ℕ) : ℕ :=
  (A.filter (fun a ↦ a.natAbs = k)).card

/-- The last frequency used in the cosine expansion, with value zero for an empty sum. -/
def lastFrequency (A : Finset ℤ) : ℕ := A.sup Int.natAbs

private theorem frequency_mem_range {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    a.natAbs ∈ Finset.range (lastFrequency A + 1) :=
  Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup ha))

theorem multiplicity_le_two (A : Finset ℤ) (k : ℕ) : multiplicity A k ≤ 2 := by
  have h : A.filter (fun a ↦ a.natAbs = k) ⊆ ({(k : ℤ), -(k : ℤ)} : Finset ℤ) := by
    intro a ha
    have habs : a.natAbs = (k : ℤ).natAbs := (Finset.mem_filter.mp ha).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using Int.natAbs_eq_natAbs_iff.mp habs
  exact (Finset.card_le_card h).trans Finset.card_le_two

theorem multiplicity_zero_le_one (A : Finset ℤ) : multiplicity A 0 ≤ 1 := by
  have h : A.filter (fun a ↦ a.natAbs = 0) ⊆ ({0} : Finset ℤ) := by
    intro a ha
    simpa using (Finset.mem_filter.mp ha).2
  simpa [multiplicity] using Finset.card_le_card h

theorem multiplicity_last_pos {A : Finset ℤ} (hA : A.Nonempty) :
    0 < multiplicity A (lastFrequency A) := by
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup A hA Int.natAbs
  exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, he.symm⟩⟩

theorem sum_multiplicity (A : Finset ℤ) :
    ∑ k ∈ Finset.range (lastFrequency A + 1), multiplicity A k = A.card :=
  (Finset.card_eq_sum_card_fiberwise (fun _ ha ↦ frequency_mem_range ha)).symm

private theorem cos_natAbs_frequency (a : ℤ) (θ : ℝ) :
    Real.cos (2 * Real.pi * (a.natAbs : ℝ) * θ) = Real.cos (2 * Real.pi * a * θ) := by
  cases a with
  | ofNat m => rfl
  | negSucc m =>
    simp only [Int.natAbs_negSucc, Nat.cast_succ, Int.cast_negSucc]
    rw [← Real.cos_neg (2 * Real.pi * ((m : ℝ) + 1) * θ)]
    congr 1
    ring

theorem sum_cos_eq_multiplicity (A : Finset ℤ) (θ : ℝ) :
    ∑ a ∈ A, Real.cos (2 * Real.pi * a * θ) =
      ∑ k ∈ Finset.range (lastFrequency A + 1),
        (multiplicity A k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) := by
  symm
  calc
    _ = ∑ a ∈ A, Real.cos (2 * Real.pi * (a.natAbs : ℝ) * θ) := by
      simpa [multiplicity, nsmul_eq_mul] using
        (Finset.sum_fiberwise_of_maps_to'
          (fun a (ha : a ∈ A) ↦ frequency_mem_range ha)
          (fun k : ℕ ↦ Real.cos (2 * Real.pi * (k : ℝ) * θ)))
    _ = _ := Finset.sum_congr rfl (fun a _ ↦ cos_natAbs_frequency a θ)

open Set

/-- The identity theorem rules out an accumulation of zeros on a closed period. -/
theorem finite_zeros_Icc {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc 0 1))
    (h₀ : g 0 ≠ 0) : {θ : ℝ | θ ∈ Icc 0 1 ∧ g θ = 0}.Finite := by
  rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Icc with h | h
  · exact (h₀ (h (left_mem_Icc.mpr zero_le_one))).elim
  · have hfin := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin h
    convert hfin using 1
    ext x
    simp

theorem analytic_cosine_sum (N : ℕ) (b : ℕ → ℕ) :
    AnalyticOnNhd ℝ (fun θ : ℝ ↦ ∑ k ∈ Finset.range (N+1),
      (b k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ)) (Icc 0 1) := by
  intro x _
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  apply Real.analyticAt_cos.comp
  exact analyticAt_const.mul analyticAt_id

/-- An open half-period can be used for the root count in Bedert's structural estimate. -/
theorem half_period_ncard_le {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc 0 1))
    (h₀ : g 0 ≠ 0) :
    {θ : ℝ | θ ∈ Ioo 0 (1/2) ∧ g θ = 0}.ncard ≤
      {θ : ℝ | θ ∈ Ico 0 1 ∧ g θ = 0}.ncard := by
  apply Set.ncard_le_ncard
  · rintro x ⟨⟨hx, hy⟩, hz⟩
    exact ⟨⟨hx.le, by linarith⟩, hz⟩
  · apply (finite_zeros_Icc hg h₀).subset
    rintro x ⟨⟨hx, hy⟩, hz⟩
    exact ⟨⟨hx, hy.le⟩, hz⟩

open Filter Real
open scoped Topology

/-- A fixed power of the third logarithm can be absorbed in a vanishing loss
in the exponent of the second logarithm. -/
theorem exists_loglog_exponent_loss_pow {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ o : ℕ → ℝ, o =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop, (log (log n)) ^ (1 - |o n|) ≤
        c * log (log n) / (log (log (log n))) ^ C := by
  let x (n : ℕ) : ℝ := log (log n)
  let y (n : ℕ) : ℝ := log (x n)
  have hx : Tendsto x atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hy : Tendsto y atTop atTop := tendsto_log_atTop.comp hx
  let o (n : ℕ) : ℝ := C * (log (y n) / y n) - log c * (y n)⁻¹
  refine ⟨o, (Asymptotics.isLittleO_one_iff ℝ).2 ?_, ?_⟩
  · have hratio : Tendsto (fun n ↦ log (y n) / y n) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hy
    have hinv : Tendsto (fun n ↦ (y n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hy
    simpa [o] using (hratio.const_mul C).sub (hinv.const_mul (log c))
  · filter_upwards [hx.eventually_gt_atTop 1, hy.eventually_gt_atTop 0] with n hxn hyn
    change x n ^ (1 - |o n|) ≤ c * x n / y n ^ C
    calc
      x n ^ (1 - |o n|) ≤ x n ^ (1 - o n) :=
        Real.rpow_le_rpow_of_exponent_le hxn.le (sub_le_sub_left (le_abs_self _) _)
      _ = exp (log c + log (x n) - log (y n) * C) := by
        rw [Real.rpow_def_of_pos (by linarith)]
        congr 1
        change y n * (1 - (C * (log (y n) / y n) - log c * (y n)⁻¹)) =
          log c + y n - log (y n) * C
        field_simp [ne_of_gt hyn]
        ring
      _ = c * x n / y n ^ C := by
        rw [exp_sub, exp_add, exp_log hc, exp_log (by linarith : 0 < x n),
          Real.rpow_def_of_pos hyn]

theorem exists_loglog_exponent_loss {c : ℝ} (hc : 0 < c) :
    ∃ o : ℕ → ℝ, o =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop, (log (log n)) ^ (1 - |o n|) ≤
        c * log (log n) / log (log (log n)) := by
  simpa using exists_loglog_exponent_loss_pow hc 1


open Filter Real Set
open scoped Topology

noncomputable def cosineSum (N : ℕ) (b : ℕ → ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), (b k : ℝ) * cos (2 * π * (k : ℝ) * θ)

noncomputable def halfRoots (N : ℕ) (b : ℕ → ℕ) : ℕ :=
  {θ : ℝ | θ ∈ Ioo 0 (1/2) ∧ cosineSum N b θ = 0}.ncard

theorem cosineSum_zero (N : ℕ) (b : ℕ → ℕ) :
    cosineSum N b 0 = (∑ k ∈ Finset.range (N + 1), b k : ℕ) := by
  simp [cosineSum]

/-- Half-open natural intervals with endpoints cut 0 through cut K.
Only pairs of indices in the same interval are constrained by the period. -/
def PeriodicPieces (N : ℕ) (b : ℕ → ℕ) (K P : ℕ) : Prop :=
  ∃ cut : ℕ → ℕ, cut 0 = 0 ∧ cut K = N + 1 ∧
    StrictMonoOn cut (Iic K) ∧
    ∀ j < K, ∀ i, cut j ≤ i → i + P < cut (j + 1) → b (i + P) = b i

/-- A positive version of the scale d log d, including d = 0. -/
noncomputable def rootScale (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) * (1 + log ((d : ℝ) + 1))

/-- The numerical conclusion needed from Bedert's §4, specialized to
coefficients in {0,1,2} and with both complexity bounds weakened to d log d. -/
def StructureEstimate : Prop :=
  ∃ B : ℝ, 1 ≤ B ∧ ∀ (N : ℕ) (b : ℕ → ℕ),
    (∀ k ≤ N, b k ≤ 2) → 0 < b N → 2 ≤ cosineSum N b 0 →
    ∃ K P : ℕ, 0 < K ∧ 0 < P ∧ PeriodicPieces N b K P ∧
      (P : ℝ) ≤ exp (B * rootScale (halfRoots N b)) ∧
      log (K : ℝ) ≤ exp (B * rootScale (halfRoots N b))

/-- Bedert's §3 bound on a polynomial with a specified partition.
Using the number of distinct interior zeros bounds the number of sign changes. -/
def StructuredRootEstimate : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ (N : ℕ) (b : ℕ → ℕ) (K P : ℕ),
    (∀ k ≤ N, b k ≤ 2) → 0 < b N → 2 ≤ cosineSum N b 0 →
    0 < K → 0 < P → PeriodicPieces N b K P →
    log (cosineSum N b 0) ≤
      A * ((halfRoots N b : ℝ) + 1) * (P : ℝ)^2 * (1 + log ((K : ℝ) * P))

private theorem one_le_rootScale (d : ℕ) : 1 ≤ rootScale d := by
  have hr : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  exact one_le_mul_of_one_le_of_one_le hr (by linarith [log_nonneg hr])

/-- Eliminate the period and the number of pieces in the two estimates. -/
theorem loglog_of_piece_bounds {A B n : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {d K P : ℕ} (hn : 1 < n) (hK : 0 < K) (hP : 0 < P)
    (hp : (P : ℝ) ≤ exp (B * rootScale d))
    (hk : log (K : ℝ) ≤ exp (B * rootScale d))
    (h : log n ≤ A * ((d : ℝ) + 1) * (P : ℝ)^2 * (1 + log ((K : ℝ) * P))) :
    log (log n) ≤ (3 * A + 1 + 3 * B) * rootScale d := by
  let r : ℝ := (d : ℝ) + 1
  let E := exp (B * rootScale d)
  have hr : 1 ≤ r := by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hs := one_le_rootScale d
  have he : 1 ≤ E := Real.one_le_exp (by positivity [B * rootScale d])
  have hlog : 1 + log ((K : ℝ) * P) ≤ 3 * E := by
    rw [log_mul (by positivity) (by positivity)]
    linarith [log_le_self (Nat.cast_nonneg P)]
  have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hp1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hkp := log_nonneg (one_le_mul_of_one_le_of_one_le hk1 hp1)
  have hg : log n ≤ 3 * A * r * E^3 := by
    calc
      log n ≤ A * r * (P : ℝ)^2 * (1 + log ((K : ℝ) * P)) := h
      _ ≤ A * r * E^2 * (3 * E) := by
        gcongr
      _ = _ := by ring
  have hlogr : log r ≤ rootScale d := by
    change log r ≤ r * (1 + log r)
    nlinarith [log_nonneg hr, mul_nonneg (sub_nonneg.mpr hr) (log_nonneg hr)]
  have hconst : log (3 * A) ≤ 3 * A * rootScale d := by
    calc
      _ ≤ 3 * A := log_le_self (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hs
  calc
    log (log n) ≤ log (3 * A * r * E^3) := log_le_log (log_pos hn) hg
    _ = log (3 * A) + log r + 3 * (B * rootScale d) := by
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow, show log E = B * rootScale d from log_exp _]
      norm_num
    _ ≤ _ := by linarith

/-- Invert x ≤ H(d+1)(1+log(d+1)) without an inverse special function. -/
theorem roots_of_loglog_le_scale {H x : ℝ} {d : ℕ} (hH : 1 ≤ H)
    (hx : H < x) (hlog : 1 ≤ log x) (h : x ≤ H * rootScale d) :
    (4 * H)⁻¹ * x / log x ≤ d := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp [rootScale] at h
    linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hr : (d : ℝ) + 1 ≤ 2 * d := by linarith
  have hb : x ≤ 4 * H * (d : ℝ) * log x := by
    by_cases hh : (d : ℝ) + 1 ≤ x
    · have hr0 := log_nonneg (show (1 : ℝ) ≤ d + 1 by linarith)
      have hl := log_le_log (by positivity) hh
      calc
        _ ≤ H * (((d : ℝ) + 1) * (1 + log ((d : ℝ) + 1))) := h
        _ ≤ H * ((2 * (d : ℝ)) * (2 * log x)) := by gcongr; linarith
        _ = _ := by ring
    · calc
        x ≤ 2 * (d : ℝ) := by linarith
        _ ≤ (4 * H * (d : ℝ)) * log x := by
          apply le_trans _ (le_mul_of_one_le_right (by positivity) hlog)
          nlinarith [mul_nonneg (sub_nonneg.mpr hH) (Nat.cast_nonneg d)]
  apply (div_le_iff₀ (by linarith : 0 < log x)).2
  rw [← div_eq_inv_mul, div_le_iff₀ (by linarith : 0 < 4 * H)]
  linarith

/-- The Green 82 declaration follows from the structured root estimate
and the piecewise-periodic structure theorem. -/
theorem solution_of_estimates (h₃ : StructuredRootEstimate) (h₄ : StructureEstimate) :
    type_of% @Green82.green_82_lower_bound := by
  obtain ⟨A, hA, hroot⟩ := h₃
  obtain ⟨B, hB, hstr⟩ := h₄
  let H := 3 * A + 1 + 3 * B
  have hH : 1 ≤ H := by dsimp [H]; linarith
  obtain ⟨o, ho, hexp⟩ := exists_loglog_exponent_loss (c := (4 * H)⁻¹) (by positivity)
  refine ⟨o, ho, ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ log (log n)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hexp, ht.eventually_gt_atTop H,
    (tendsto_log_atTop.comp ht).eventually_ge_atTop 1, eventually_ge_atTop 2]
    with n hpow hx hlog hn S hcard
  let N := lastFrequency S
  let b := multiplicity S
  have hzero : cosineSum N b 0 = n := by
    rw [cosineSum_zero, sum_multiplicity, hcard]
  have hdeg : 0 < b N := multiplicity_last_pos (Finset.card_pos.mp (by omega))
  have hbound : ∀ k ≤ N, b k ≤ 2 := fun k _ ↦ multiplicity_le_two _ k
  have htwo : 2 ≤ cosineSum N b 0 := by rw [hzero]; exact_mod_cast hn
  obtain ⟨K,P,hK,hP,hpieces,hp,hk⟩ := hstr N b hbound hdeg htwo
  have h := hroot N b K P hbound hdeg htwo hK hP hpieces
  rw [hzero] at h
  have hscale := loglog_of_piece_bounds hA hB (n := (n : ℝ)) (by exact_mod_cast show 1 < n by omega)
    hK hP hp hk h
  have hsmall := hpow.trans (roots_of_loglog_le_scale hH hx hlog hscale)
  have hfloor : ⌊log (log n) ^ (1 - |o n|)⌋₊ ≤ halfRoots N b := by
    exact (Nat.floor_le_floor hsmall).trans (by simp)
  have hhalf := half_period_ncard_le (analytic_cosine_sum N b)
    (show cosineSum N b 0 ≠ 0 by linarith)
  have hsame : (fun θ ↦ ∑ a ∈ S, cos (2 * π * a * θ)) = cosineSum N b :=
    funext (sum_cos_eq_multiplicity S)
  have hz : {θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ S, cos (2 * π * a * θ) = 0} =
      {θ : ℝ | θ ∈ Ico 0 1 ∧ cosineSum N b θ = 0} := by
    ext θ
    simp only [mem_ofPred_eq, congrFun hsame θ]
  rw [hz]
  exact_mod_cast hfloor.trans hhalf

end OMA.G82

namespace OMA.G82

open scoped BigOperators

/-- The coefficients `c 0, …, c D` annihilate the window starting at `u`. -/
def WindowRelation (x c : ℕ → ℂ) (D u : ℕ) : Prop :=
  ∑ k ∈ Finset.range (D + 1), c k * x (u + k) = 0

private theorem window_forward {x c : ℕ → ℂ} {D u v : ℕ}
    (hc : c D ≠ 0) (hu : WindowRelation x c D u) (hv : WindowRelation x c D v)
    (he : ∀ k < D, x (u + k) = x (v + k)) : x (u + D) = x (v + D) := by
  unfold WindowRelation at hu hv
  rw [Finset.sum_range_succ] at hu hv
  have hsum : ∑ k ∈ Finset.range D, c k * x (u + k) =
      ∑ k ∈ Finset.range D, c k * x (v + k) :=
    Finset.sum_congr rfl fun k hk ↦ by rw [he k (Finset.mem_range.mp hk)]
  rw [hsum] at hu
  exact mul_left_cancel₀ hc (add_left_cancel (hu.trans hv.symm))

private theorem window_backward {x c : ℕ → ℂ} {D u v : ℕ}
    (hc : c 0 ≠ 0) (hu : WindowRelation x c D u) (hv : WindowRelation x c D v)
    (he : ∀ k < D, x (u + 1 + k) = x (v + 1 + k)) : x u = x v := by
  unfold WindowRelation at hu hv
  rw [Finset.sum_range_succ'] at hu hv
  simp only [Nat.add_zero] at hu hv
  have hsum : ∑ k ∈ Finset.range D, c (k + 1) * x (u + (k + 1)) =
      ∑ k ∈ Finset.range D, c (k + 1) * x (v + (k + 1)) :=
    Finset.sum_congr rfl fun k hk ↦ by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using
        congrArg (c (k + 1) * ·) (he k (Finset.mem_range.mp hk))
  rw [hsum] at hu
  exact mul_left_cancel₀ hc (add_left_cancel (hu.trans hv.symm))

/-- A collision of two length-`D` windows propagates through the whole word. -/
theorem window_collision_period {x c : ℕ → ℂ} {D L i T : ℕ}
    (hc₀ : c 0 ≠ 0) (hcD : c D ≠ 0)
    (hrec : ∀ u, u + D < L → WindowRelation x c D u)
    (hfits : i + T + D ≤ L)
    (hcollision : ∀ k < D, x (i + k) = x (i + T + k)) :
    ∀ n, n + T < L → x n = x (n + T) := by
  let W (p : ℕ) := ∀ k < D, x (p + k) = x (p + T + k)
  have hback : ∀ m p, p + m = i → W p := by
    intro m
    induction m with
    | zero =>
      intro p hp
      simp only [Nat.add_zero] at hp
      simpa [hp, W] using hcollision
    | succ m ih =>
      intro p hp
      have hw := ih (p + 1) (by omega)
      intro k hk
      cases k with
      | zero =>
        simp only [Nat.add_zero]
        apply window_backward hc₀ (hrec p (by omega)) (hrec (p+T) (by omega))
        intro j hj
        simpa only [Nat.add_right_comm p 1 T] using hw j hj
      | succ k =>
        simpa only [Nat.add_succ, Nat.succ_add, Nat.add_one] using hw k (by omega)
  have hw := hback i 0 (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n < D
    · simpa only [Nat.zero_add, Nat.add_comm T n] using hw n hsmall
    · let u := n - D
      have hud : u + D = n := by dsimp [u]; omega
      have htranslate : u + T + D = n + T := by omega
      have heq := window_forward hcD (hrec u (by omega)) (hrec (u + T) (by omega))
        (fun k hk ↦ by
          simpa only [Nat.add_right_comm u k T] using ih (u+k) (by omega) (by omega))
      simpa only [hud, htranslate] using heq

private theorem repeated_window {S : Finset ℂ} {x : ℕ → ℂ} {D L : ℕ}
    (hx : ∀ n < L, x n ∈ S) (hlen : S.card ^ D + D ≤ L) :
    ∃ i T, 0 < T ∧ i + T ≤ S.card ^ D ∧
      ∀ k < D, x (i + k) = x (i + T + k) := by
  classical
  let M := S.card ^ D
  let word (i : Fin (M+1)) (k : Fin D) : S :=
    ⟨x (i.val + k.val), hx _ (by have hi := i.isLt; have hk := k.isLt; dsimp [M] at *; omega)⟩
  have hs : Fintype.card (Fin D → S) < Fintype.card (Fin (M+1)) := by simp [M]
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt word hs
  have aux (a b : Fin (M+1)) (hab : a < b) (he : word a = word b) :
      ∃ i T, 0 < T ∧ i + T ≤ S.card ^ D ∧
        ∀ k < D, x (i + k) = x (i + T + k) := by
    have hlt : a.val < b.val := hab
    have hb := b.isLt
    have heval : a.val + (b.val - a.val) = b.val := by omega
    refine ⟨a.val, b.val - a.val, by omega, ?_, ?_⟩
    · rw [heval]
      change b.val ≤ M
      omega
    · intro k hk
      rw [heval]
      exact congrArg Subtype.val (congrFun he ⟨k,hk⟩)
  rcases lt_or_gt_of_ne hab with h | h
  · exact aux a b h he
  · exact aux b a h he.symm

/-- A long finite-alphabet recurrence word is a segment of a periodic solution
of the same recurrence on all natural indices. The period is bounded by the
number of possible length-`D` windows. -/
theorem periodic_extension_of_recurrence {S : Finset ℂ} {x c : ℕ → ℂ} {D L : ℕ}
    (hx : ∀ n < L, x n ∈ S) (hlen : S.card ^ D + D ≤ L)
    (hc₀ : c 0 ≠ 0) (hcD : c D ≠ 0)
    (hrec : ∀ u, u + D < L → WindowRelation x c D u) :
    ∃ (T : ℕ) (y : ℕ → ℂ), 0 < T ∧ T ≤ S.card ^ D ∧ Function.Periodic y T ∧
      (∀ n < L, y n = x n) ∧ ∀ u, WindowRelation y c D u := by
  obtain ⟨i, T, hT, hsize, hsame⟩ := repeated_window hx hlen
  have hperiod := window_collision_period hc₀ hcD hrec (by omega : i + T + D ≤ L) hsame
  let y := fun n ↦ x (n % T)
  have hagree : ∀ n < L, y n = x n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : n < T
      · simp [y, Nat.mod_eq_of_lt hsmall]
      · have hn' : n - T + T = n := by omega
        calc
          y n = y (n-T) := by
            dsimp [y]
            conv_lhs => rw [← hn']
            simp
          _ = x (n-T) := ih _ (by omega) (by omega)
          _ = x n := by simpa only [hn'] using hperiod (n-T) (by omega)
  refine ⟨T, y, hT, by omega, fun n ↦ by simp [y], hagree, ?_⟩
  intro u
  have hr := Nat.mod_lt u hT
  have hlocal := hrec (u % T) (by omega)
  unfold WindowRelation at hlocal ⊢
  refine (Finset.sum_congr rfl (fun k hk ↦ ?_)).trans hlocal
  have hk' := Finset.mem_range.mp hk
  have hy : y (u+k) = y (u%T+k) := by simp [y, Nat.mod_add_mod]
  rw [hy, hagree _ (by omega)]



open Polynomial

/-- One forward shift on a sequence of complex numbers. -/
def sequenceShift : Module.End ℂ (ℕ → ℂ) where
  toFun x n := x (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sequenceShift_pow_apply (k : ℕ) (x : ℕ → ℂ) (n : ℕ) :
    (sequenceShift ^ k) x n = x (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (sequenceShift ^ k) x (n+1) = x (n + (k+1))
    rw [ih]
    congr 1
    omega

/-- Evaluation of a polynomial in the forward shift is the linear recurrence
whose window coefficients are the polynomial coefficients in ascending order. -/
theorem shift_aeval_eq_zero_iff {q : Polynomial ℂ} {x : ℕ → ℂ} {D : ℕ} (hd : q.natDegree ≤ D) :
    (aeval sequenceShift q) x = 0 ↔ ∀ u, WindowRelation x q.coeff D u := by
  have he (u : ℕ) : (aeval sequenceShift q) x u =
      ∑ k ∈ Finset.range (D+1), q.coeff k * x (u+k) := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hd)]
    simp [LinearMap.sum_apply, Finset.sum_apply, sequenceShift_pow_apply]
  constructor
  · intro h u
    exact (he u).symm.trans (congrFun h u)
  · intro h
    exact funext fun u ↦ (he u).trans (h u)

private theorem periodic_iff_shift_annihilates (x : ℕ → ℂ) (T : ℕ) :
    Function.Periodic x T ↔ (aeval sequenceShift ((X : Polynomial ℂ)^T - 1)) x = 0 := by
  constructor
  · intro h
    funext n
    simp [sequenceShift_pow_apply, h n]
  · intro h n
    have he := congrFun h n
    simpa [sequenceShift_pow_apply, sub_eq_zero] using he

/-- A polynomial identity of Bézout type transfers the prescribed period to a
periodic solution of the structural recurrence. -/
theorem periodic_of_window_bezout {x : ℕ → ℂ} {q U V : Polynomial ℂ} {P T D : ℕ}
    (ht : Function.Periodic x T)
    (hdeg : q.natDegree ≤ D) (hrec : ∀ u, WindowRelation x q.coeff D u)
    (hbez : X^P - 1 = U * (X^T - 1) + V * q) : Function.Periodic x P := by
  apply (periodic_iff_shift_annihilates x P).mpr
  have h₁ := (periodic_iff_shift_annihilates x T).mp ht
  have h₂ := (shift_aeval_eq_zero_iff hdeg).mpr hrec
  rw [hbez, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.mul_apply, h₁, h₂, map_zero, map_zero, add_zero]



/-- On a periodic sequence, the only possible characteristic roots of the
smoothed recurrence are the P-th roots of unity, each needed only once. -/
theorem period_factor_bezout {Q : Polynomial ℂ} {T P : ℕ} (hT : 0 < T)
    (hQ : ∀ z : ℂ, z ^ T = 1 → Q.eval z ≠ 0) :
    ∃ U V : Polynomial ℂ, X^P - 1 = U * (X^T - 1) + V * (Q * (X^P - 1)^2) := by
  let a : Polynomial ℂ := X^T - 1
  let b : Polynomial ℂ := X^P - 1
  let g := IsBezout.gcd a (Q * b^2)
  have hga : g ∣ a := IsBezout.gcd_dvd_left _ _
  have hsa : Squarefree a :=
    (X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hT.ne' : (T : ℂ) ≠ 0)).squarefree
  have hsq : Squarefree g := fun x hx ↦ hsa x (hx.trans hga)
  have hcop : IsCoprime a Q := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).2
    intro z
    by_cases hz : z ^ T = 1
    · exact Or.inr (by simpa [aeval_def] using hQ z hz)
    · exact Or.inl (by simpa [a, sub_ne_zero] using hz)
  have hgb : g ∣ b^2 :=
    (hcop.of_isCoprime_of_dvd_left hga).dvd_of_dvd_mul_left (IsBezout.gcd_dvd_right _ _)
  obtain ⟨m, hm⟩ := (hsq.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hgb
  obtain ⟨u, v, huv⟩ := IsBezout.gcd_eq_sum a (Q * b^2)
  refine ⟨m*u, m*v, ?_⟩
  change b = m*u*a + m*v*(Q*b^2)
  calc
    b = (u*a + v*(Q*b^2)) * m := hm.trans (congrArg (· * m) huv.symm)
    _ = _ := by ring

end OMA.G82

namespace OMA.G82

open Set Polynomial
/-- Placing a cut immediately after each defective period comparison produces
at most one more interval than the number of defective comparisons. -/
theorem pieces_of_breaks {N P : ℕ} (hP : 0 < P) (b : ℕ → ℕ) (bad : Finset ℕ)
    (hbad : ∀ i, i + P ≤ N → b (i + P) ≠ b i → i ∈ bad) :
    ∃ K, 0 < K ∧ K ≤ bad.card + 1 ∧ PeriodicPieces N b K P := by
  classical
  let B := (bad.image (fun i ↦ i+1)).filter (· ≤ N+1)
  let C := insert 0 (insert (N+1) B)
  have hz : 0 ∈ C := Finset.mem_insert_self _ _
  have hn : N+1 ∈ C := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have htop : ∀ a ∈ C, a ≤ N+1 := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · omega
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rfl
    exact (Finset.mem_filter.mp ha).2
  have hlow : 2 ≤ C.card := by
    have hh : ({0, N+1} : Finset ℕ) ⊆ C  := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hz
      · simpa [Finset.mem_singleton.mp ha] using hn
    simpa using Finset.card_le_card hh
  have hupp : C.card ≤ bad.card + 2 := by
    have hh : B.card ≤ bad.card := Finset.card_le_card (Finset.filter_subset ..) |>.trans Finset.card_image_le
    have h1 := Finset.card_insert_le 0 (insert (N+1) B)
    have h2 := Finset.card_insert_le (N+1) B
    change (insert 0 (insert (N+1) B)).card ≤ _
    omega
  let K := C.card - 1
  have hk : K + 1 = C.card := by dsimp [K]; omega
  let e := C.orderEmbOfFin rfl
  let cut (j : ℕ) := if h : j < C.card then e ⟨j,h⟩ else 0
  have hcut (j : ℕ) (hj : j ≤ K) : cut j = e ⟨j, by omega⟩ := dif_pos (by omega)
  have hrange (a : ℕ) (ha : a ∈ C) : ∃ l : Fin C.card, e l = a := by
    have hr := C.range_orderEmbOfFin (k := C.card) rfl
    exact (Set.ext_iff.mp hr a).mpr ha
  obtain ⟨z,hz'⟩ := hrange 0 hz
  obtain ⟨w,hw'⟩ := hrange (N+1) hn
  have hend : cut K = N+1 := by
    rw [hcut K le_rfl]
    apply le_antisymm (htop _ (C.orderEmbOfFin_mem rfl _))
    rw [← hw']
    apply e.monotone
    have := w.isLt
    change w.val ≤ K
    omega
  refine ⟨K, by omega, by omega, cut, ?_, hend, ?_, ?_⟩
  · rw [hcut 0 (by omega)]
    have he : (⟨0,by omega⟩ : Fin C.card) ≤ z := Nat.zero_le _
    have hm := e.monotone he
    rw [hz'] at hm
    exact Nat.eq_zero_of_le_zero hm
  · intro j hj l hl hjl
    rw [hcut j hj, hcut l hl]
    exact e.strictMono hjl
  · intro j hj i hi hnext
    by_contra hcmp
    have hj' : j+1 ≤ K := by omega
    have hiN : i+P ≤ N := by
      have hm : cut (j+1) ≤ N+1 := by
        rw [hcut _ hj']
        exact htop _ (C.orderEmbOfFin_mem rfl _)
      omega
    have hc : i+1 ∈ C := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (hbad i hiN hcmp), by omega⟩
    obtain ⟨l,hl⟩ := hrange (i+1) hc
    have hleft : cut j < e l := by omega
    have hright : e l < cut (j+1) := by omega
    rw [hcut j (by omega)] at hleft
    rw [hcut _ hj'] at hright
    have hl₁ : j < l.val := e.lt_iff_lt.mp hleft
    have hl₂ : l.val < j+1 := e.lt_iff_lt.mp hright
    omega

/-- Sparse violations of the recurrence with multiplier `Q*(X^P-1)^2` force a
partition with common period `P`. Each exceptional window, and the right
endpoint, accounts for at most `3^D+D+P+1` candidate break positions. -/
theorem pieces_of_sparse_windows {N P D : ℕ} {b : ℕ → ℕ} {Q q : Polynomial ℂ}
    (hP : 0 < P) (hcoef : ∀ k ≤ N, b k ≤ 2)
    (hq : q = Q * (X^P - 1)^2) (hdeg : q.natDegree ≤ D)
    (hc₀ : q.coeff 0 ≠ 0) (hcD : q.coeff D ≠ 0)
    (hQ : ∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → Q.eval z ≠ 0)
    (E : Finset ℕ)
    (hrec : ∀ u, u + D ≤ N → u ∉ E → WindowRelation (fun n ↦ (b n : ℂ)) q.coeff D u) :
    ∃ K, 0 < K ∧ K ≤ (E.card + 1) * (3^D + D + P + 1) + 1 ∧ PeriodicPieces N b K P := by
  classical
  let L := 3^D + D + P + 1
  let S : Finset ℂ := {0, 1, 2}
  have hS : S.card = 3 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_pair (by norm_num)]
  have hloc (i : ℕ) (hfull : i + L ≤ N+1)
      (hclear : ∀ r, i ≤ r → r < i + L → r ∉ E) : b (i+P) = b i := by
    let x (n : ℕ) : ℂ := b (i+n)
    have hx : ∀ n < L, x n ∈ S := by
      intro n hn
      have hb := hcoef (i+n) (by omega)
      interval_cases h : b (i+n) <;> simp [x, h, S]
    have hr : ∀ u, u+D<L → WindowRelation x q.coeff D u := by
      intro u hu
      simpa [WindowRelation, x, Nat.add_assoc] using
        hrec (i+u) (by omega) (hclear _ (by omega) (by omega))
    have hlen : S.card ^ D + D ≤ L := by rw [hS]; dsimp [L]; omega
    obtain ⟨T,y,hT,_,hy,hmatch,hrel⟩ := periodic_extension_of_recurrence hx hlen hc₀ hcD hr
    obtain ⟨U,V,huv⟩ := period_factor_bezout (P := P) hT (hQ T hT)
    rw [← hq] at huv
    have hyP := periodic_of_window_bezout hy hdeg hrel huv
    have hPeq := hyP 0
    simp only [Nat.zero_add] at hPeq
    have hLP : P < L := by
      exact Nat.lt_succ_of_le (Nat.le_add_left P (3^D+D))
    rw [hmatch P hLP, hmatch 0 (Nat.zero_lt_of_lt hLP)] at hPeq
    simpa [x] using (Nat.cast_inj (R := ℂ)).mp hPeq
  let ends := insert (N+1) E
  let near (r : ℕ) := (Finset.range L).image (fun j ↦ r-j)
  let bad := ends.biUnion near
  have hbad (i : ℕ) (hi : i+P≤N) (hb : b (i+P) ≠ b i) : i ∈ bad := by
    have hpoint : ∃ r ∈ ends, i ≤ r ∧ r < i+L := by
      by_contra! h
      have hfull : i+L ≤ N+1 := by
        exact h (N+1) (Finset.mem_insert_self _ _) (by omega)
      apply hb (hloc i hfull ?_)
      intro r hr hr' he
      exact (h r (Finset.mem_insert_of_mem he) hr).not_gt hr'
    obtain ⟨r,he,hr,hr'⟩ := hpoint
    refine Finset.mem_biUnion.mpr ⟨r,he,Finset.mem_image.mpr ⟨r-i,?_,?_⟩⟩
    · exact Finset.mem_range.mpr (by omega)
    · omega
  have hcount : bad.card ≤ (E.card + 1) * L := by
    calc
      bad.card ≤ ∑ r ∈ ends, (near r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ ends, L := by
        apply Finset.sum_le_sum
        intro r _
        exact Finset.card_image_le.trans_eq (Finset.card_range L)
      _ = ends.card * L := by simp
      _ ≤ _ := Nat.mul_le_mul_right L (Finset.card_insert_le _ _)
  obtain ⟨K,hK,hbound,hpieces⟩ := pieces_of_breaks hP b bad hbad
  exact ⟨K,hK,hbound.trans (Nat.succ_le_succ hcount),hpieces⟩

end OMA.G82

namespace OMA.G82

open Polynomial Finset

/-- Clearing negative powers in twice the cosine expansion. The two monomials
at frequency zero both contribute to the middle coefficient. -/
noncomputable def palindromicLift (N : ℕ) (b : ℕ → ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (N+1), (monomial (N-i) (b i : ℂ) + monomial (N+i) (b i : ℂ))

theorem palindromicLift_coeff_left {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N)
    (b : ℕ → ℕ) : (palindromicLift N b).coeff (N-i) = (b i : ℂ) := by
  simp only [palindromicLift, finsetSum_coeff, coeff_add, coeff_monomial]
  rw [sum_eq_single_of_mem i (mem_range.mpr (by omega))]
  · rw [if_pos rfl, if_neg (show N+i ≠ N-i by omega), add_zero]
  · intro j hj hji
    have hjN := mem_range.mp hj
    simp [show N-j ≠ N-i by omega, show N+j ≠ N-i by omega]

/-- Except at the center, a vanishing product coefficient is precisely the
forward window relation, using the left half of the reflected polynomial. -/
theorem lift_product_window {N D u : ℕ} (b : ℕ → ℕ) (q : Polynomial ℂ)
    (hD : q.natDegree ≤ D) (hu : 0 < u) (hfit : u+D ≤ N) :
    (q * palindromicLift N b).coeff (N-u) =
      ∑ k ∈ range (D+1), q.coeff k * (b (u+k) : ℂ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ k ∈ range (D+1), q.coeff k * (palindromicLift N b).coeff (N-u-k) := by
      symm
      apply sum_subset (range_subset_range.mpr (by omega))
      intro k _ hk
      have hk' : D < k := by simpa using hk
      simp [coeff_eq_zero_of_natDegree_lt (hD.trans_lt hk')]
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      rw [show N-u-k=N-(u+k) by omega, palindromicLift_coeff_left (by omega) (by omega)]

theorem sparse_windows_of_product {N : ℕ} (b : ℕ → ℕ) (q : Polynomial ℂ) :
    ∃ E : Finset ℕ, E.card ≤ (q * palindromicLift N b).support.card + 1 ∧
      ∀ u, u + q.natDegree ≤ N → u ∉ E →
        (∑ k ∈ range (q.natDegree+1), q.coeff k * (b (u+k) : ℂ)) = 0 := by
  let S := (q * palindromicLift N b).support
  refine ⟨insert 0 (S.image (fun j ↦ N-j)), ?_, ?_⟩
  · exact (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1)
  · intro u hfit hu
    have hu0 : 0 < u := by
      by_contra! h
      exact hu ((show u = 0 by omega) ▸ mem_insert_self _ _)
    rw [← lift_product_window b q le_rfl hu0 hfit]
    apply notMem_support_iff.mp
    intro hmem
    apply hu
    exact mem_insert_of_mem (mem_image.mpr ⟨N-u, hmem, by omega⟩)

end OMA.G82

namespace OMA.G82

open Real Polynomial

/-- The sparse-product input from §4 (Corollary 4.3), allowing the
weaker exponential envelope that suffices for the Green problem. -/
def SparseProductEstimate : Prop :=
  ∃ B : ℝ, 1 ≤ B ∧ ∀ (N : ℕ) (b : ℕ → ℕ),
    (∀ k ≤ N, b k ≤ 2) → 0 < b N → 2 ≤ cosineSum N b 0 →
    ∃ (P : ℕ) (Q : Polynomial ℂ), 0 < P ∧ Q.coeff 0 ≠ 0 ∧
      (∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → Q.eval z ≠ 0) ∧
      let q := Q * (X^P - 1)^2
      (P : ℝ) + q.natDegree + log (((q * palindromicLift N b).support.card : ℝ) + 2) ≤
        exp (B * rootScale (halfRoots N b))

private theorem log_pieces_le {P D e s K : ℕ} (hK : 0 < K) (he : e ≤ s + 1)
    (h : K ≤ (e+1) * (3^D+D+P+1) + 1) :
    log (K : ℝ) ≤ log ((s : ℝ) + 2) + (D : ℝ) * log 3 + D + P + 3 := by
  have hnat : K ≤ (s+2) * (3^D*(D+P+3)) := by
    have h1 : 1 ≤ (3:ℕ)^D := Nat.one_le_pow _ _ (by decide)
    have h2 : 3^D+D+P+2 ≤ 3^D*(D+P+3) := by
      nlinarith [Nat.mul_le_mul_right (D+P+2) h1]
    calc
      K ≤ (e+1) * (3^D+D+P+1) + 1 := h
      _ ≤ (s+2) * (3^D+D+P+2) := by
        have h' := Nat.mul_le_mul_right (3^D+D+P+1) (show e+1 ≤ s+2 by omega)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hr : (K : ℝ) ≤ ((s : ℝ)+2) * (3^D*((D : ℝ)+P+3)) := by exact_mod_cast hnat
  calc
    log (K : ℝ) ≤ _ := log_le_log (by positivity) hr
    _ = log ((s : ℝ)+2) + ((D : ℝ)*log 3 + log ((D : ℝ)+P+3)) := by
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity), log_pow]
    _ ≤ _ := by linarith [log_le_self (by positivity : 0 ≤ (D : ℝ)+P+3)]

/-- A sparse multiplier gives a common period with controlled partition size. -/
theorem structureEstimate_of_sparse (hsparse : SparseProductEstimate) : StructureEstimate := by
  obtain ⟨B,hB,H⟩ := hsparse
  refine ⟨B+10, by linarith, ?_⟩
  intro N b hb hdeg hg
  obtain ⟨P,Q,hP,hQ₀,hQ,hsize⟩ := H N b hb hdeg hg
  let q := Q * (X^P - 1)^2
  have hq₀ : q.coeff 0 ≠ 0 := by
    simpa [q, sq, mul_coeff_zero, coeff_sub, coeff_X_pow, hP.ne', hP.ne] using hQ₀
  have hq : q ≠ 0 := fun h ↦ hq₀ (by rw [h]; simp)
  obtain ⟨E,hE,hwin⟩ := sparse_windows_of_product b q
  obtain ⟨K,hK,hcount,hpieces⟩ := pieces_of_sparse_windows (q := q) hP hb rfl le_rfl hq₀
    (by simpa using hq) hQ E hwin
  refine ⟨K,P,hK,hP,hpieces,?_,?_⟩
  all_goals
    let d := halfRoots N b
    let s := (q * palindromicLift N b).support.card
    change (P : ℝ) + q.natDegree + log ((s : ℝ)+2) ≤ exp (B * rootScale d) at hsize
    have hd := one_le_rootScale d
    have hn : 0 ≤ log ((s : ℝ)+2) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) s])
    have hbd : 10 * exp (B * rootScale d) ≤ exp ((B+10) * rootScale d) := by
      rw [add_mul, exp_add, mul_comm]
      gcongr
      linarith [Real.add_one_le_exp (10 * rootScale d)]
    have he1 : 1 ≤ exp (B * rootScale d) := Real.one_le_exp (by positivity)
  · exact le_trans (by linarith [Nat.cast_nonneg (α := ℝ) q.natDegree]) hbd
  · have hl := log_pieces_le hK hE hcount
    change log (K : ℝ) ≤ log ((s : ℝ)+2) + (q.natDegree : ℝ)*log 3 + q.natDegree + P + 3 at hl
    apply le_trans _ hbd
    have hlog : log 3 ≤ (3 : ℝ) := log_le_self (by norm_num)
    linarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) q.natDegree),
      Nat.cast_nonneg (α := ℝ) P, Nat.cast_nonneg (α := ℝ) q.natDegree]

end OMA.G82

namespace OMA.G82

open Finset Real

private theorem weighted_diff_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) :
    ∑ k ∈ Ico m n, (u k - u (k+1)) / (k : ℝ) ≤ u m / m - u n / n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [sum_Ico_succ_top hmn, sub_div]
    have hn : (0 : ℝ) < n := by exact_mod_cast hm.trans_le hmn
    have hmono : u (n+1) / (n+1 : ℕ) ≤ u (n+1) / (n : ℝ) :=
      div_le_div_of_nonneg_left (hu _) hn (by exact_mod_cast Nat.le_succ n)
    linarith

/-- Discrete summation by parts for a bounded primitive with reciprocal weights. -/
theorem abs_weighted_diff_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    |∑ k ∈ Ico m n, (f k - f (k+1)) / (k : ℝ)| ≤ 2 / m := by
  have upper (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (hu' : u m ≤ 2) :
      ∑ k ∈ Ico m n, (u k - u (k+1)) / (k : ℝ) ≤ 2 / m := by
    apply (weighted_diff_le hm hmn u hu).trans
    calc
      _ ≤ u m / m := sub_le_self _ (div_nonneg (hu _) (Nat.cast_nonneg _))
      _ ≤ _ := div_le_div_of_nonneg_right hu' (Nat.cast_nonneg _)
  apply abs_le.mpr
  constructor
  · have h := upper (fun k ↦ 1 - f k) (fun k ↦ sub_nonneg.mpr (abs_le.mp (hf k)).2)
        (by linarith [(abs_le.mp (hf m)).1])
    simp only [sub_sub_sub_cancel_left] at h
    rw [← neg_le_neg_iff] at h
    simp only [← sum_neg_distrib, ← neg_div, neg_sub] at h
    simpa only [neg_div] using h
  · have h := upper (fun k ↦ 1 + f k)
        (fun k ↦ by linarith [(abs_le.mp (hf k)).1])
        (by linarith [(abs_le.mp (hf m)).2])
    simpa only [add_sub_add_left_eq_sub] using h

/-- A uniform bound on the primitive of one high-frequency interval. -/
theorem abs_sin_sum_div_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {t : ℝ} (ht : 0 < t) (hπ : t ≤ π) :
    |∑ k ∈ Ico m n, sin ((k : ℝ) * t) / k| ≤ π / ((m : ℝ) * t) := by
  let f (k : ℕ) := cos ((k : ℝ) * t - t / 2)
  have hf (k : ℕ) : |f k| ≤ 1 := abs_cos_le_one _
  have hdiff (k : ℕ) : 2 * sin (t/2) * sin ((k : ℝ) * t) = f k - f (k+1) := by
    dsimp [f]
    push_cast
    rw [show ((k : ℝ) + 1) * t - t / 2 = (k : ℝ) * t + t / 2 by ring]
    rw [cos_sub, cos_add]
    ring
  have hsum :
      (2 * sin (t/2)) * (∑ k ∈ Ico m n, sin ((k : ℝ) * t) / k) =
        ∑ k ∈ Ico m n, (f k - f (k+1)) / (k : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [← mul_div_assoc, hdiff]
  have chord : t / π ≤ sin (t/2) := by
    simpa using mul_le_sin (x := t / 2) (by positivity) (by linarith)
  have sinpos := (div_pos ht pi_pos).trans_le chord
  have bound := abs_weighted_diff_le hm hmn f hf
  rw [← hsum, abs_mul, abs_of_pos (mul_pos (by norm_num) sinpos)] at bound
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ (mul_pos hm' ht)).mpr
  set S := |∑ k ∈ Ico m n, sin ((k : ℝ) * t) / k|
  change 2 * sin (t/2) * S ≤ 2 / m at bound
  rw [mul_assoc, show (2 : ℝ) / m = 2 * (1 / m) by ring] at bound
  have hS : 0 ≤ S := abs_nonneg _
  have bound' := (mul_le_mul_of_nonneg_right chord hS).trans
    ((mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp bound)
  field_simp [ne_of_gt pi_pos, ne_of_gt hm'] at bound'
  linarith


private theorem reciprocal_block {L B : ℕ} (hL : 0 < L) (hLB : L ≤ B) :
    ∑ k ∈ Ico L B, (k : ℝ)⁻¹ ≤ 1 + log (B / (L : ℝ)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hB' : (0 : ℝ) < B := by exact_mod_cast hL.trans_le hLB
  have hshift (n : ℕ) (hn : L ≤ n) :
      ∑ k ∈ Ico L n, (k : ℝ)⁻¹ + (n : ℝ)⁻¹ =
        (L : ℝ)⁻¹ + ∑ k ∈ Ico L n, ((k+1 : ℕ) : ℝ)⁻¹ := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => simp only [sum_Ico_succ_top hn]; linarith
  have hi := (inv_antitoneOn_Icc_right (b := (B : ℝ)) hL').sum_le_integral_Ico hLB
  rw [integral_inv_of_pos hL' hB'] at hi
  have h1 : (L : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hL)
  linarith [hshift B hLB, inv_pos.mpr hB']

private noncomputable def cosPrimitive (t : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then t else sin ((k : ℝ) * t) / k

private theorem cosPrimitive_abs_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    |cosPrimitive t k| ≤ t := by
  by_cases hk : k = 0
  · simp [cosPrimitive, hk, abs_of_nonneg ht]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [cosPrimitive, if_neg hk, abs_div, abs_of_pos hk', div_le_iff₀ hk']
    simpa [abs_of_nonneg ht, mul_comm] using
      (abs_sin_le_abs (x := (k : ℝ) * t))

private theorem cosPrimitive_prefix {K L : ℕ} (hK : 0 < K) (hL : 0 < L) {t : ℝ}
    (ht : 0 ≤ t) (hLt : (L : ℝ) * t ≤ 1 + t) :
    ∑ k ∈ range (K * L), |cosPrimitive t k| ≤ 2 + t + log K := by
  have hLB : L ≤ K * L := Nat.le_mul_of_pos_left L hK
  have hlo : ∑ k ∈ range L, |cosPrimitive t k| ≤ (L : ℝ) * t := by
    calc
      _ ≤ ∑ _k ∈ range L, t := sum_le_sum fun k _ ↦ cosPrimitive_abs_le ht k
      _ = _ := by simp
  have hmid : ∑ k ∈ Ico L (K * L), |cosPrimitive t k| ≤ 1 + log K := by
    apply le_trans (b := ∑ k ∈ Ico L (K * L), (k : ℝ)⁻¹)
    · apply sum_le_sum
      intro k hk
      have hk' : 0 < k := hL.trans_le (mem_Ico.mp hk).1
      have hk'' : (0 : ℝ) < k := by exact_mod_cast hk'
      rw [cosPrimitive, if_neg hk'.ne', abs_div, abs_of_pos hk'', ← one_div]
      exact div_le_div_of_nonneg_right (abs_sin_le_one _) hk''.le
    · simpa [Nat.cast_mul, hL.ne'] using reciprocal_block hL hLB
  rw [sum_Ico_eq_sub _ hLB] at hmid
  linarith

private theorem split_clipped_block {a b B : ℕ} (hab : a ≤ b) (f : ℕ → ℝ) :
    ∑ k ∈ Ico a b, f k = (∑ k ∈ Ico (min a B) (min b B), f k) +
      ∑ k ∈ Ico (max a B) (max b B), f k := by
  rcases le_total b B with h | h
  · simp [h, hab.trans h]
  rcases le_total B a with h' | h'
  · simp [h, h']
  simp [min_eq_left h', min_eq_right h, max_eq_right h', max_eq_left h,
    sum_Ico_consecutive f h' h]



private theorem cosPrimitive_variation {K : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
    (hcut : ∀ j < K, cut j ≤ cut (j+1)) {t : ℝ} (ht : 0 < t) (hπ : t ≤ π) :
    ∑ j ∈ range K, |∑ k ∈ Ico (cut j) (cut (j+1)), cosPrimitive t k| ≤
      2 + 2 * π + log K := by
  let L := ⌈1 / t⌉₊
  let B := K * L
  have hL : 0 < L := Nat.ceil_pos.mpr (by positivity)
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have htL : 1 ≤ (L : ℝ) * t := (div_le_iff₀ ht).mp (Nat.le_ceil _)
  have hLt : (L : ℝ) * t ≤ 1 + t := by
    have h := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / t)).le ht.le
    simpa [L, add_mul, ht.ne'] using h
  let S (j : ℕ) := ∑ k ∈ range (min (cut j) B), |cosPrimitive t k|
  have hblock (j : ℕ) (hj : j < K) :
      |∑ k ∈ Ico (cut j) (cut (j+1)), cosPrimitive t k| ≤
        (S (j+1) - S j) + π / K := by
    let a := cut j
    let b := cut (j+1)
    have hab : a ≤ b := hcut j hj
    have hlo : |∑ k ∈ Ico (min a B) (min b B), cosPrimitive t k| ≤ S (j+1) - S j := by
      apply (abs_sum_le_sum_abs _ _).trans
      exact le_of_eq (sum_Ico_eq_sub _ (min_le_min_right B hab))
    have hB : 0 < B := Nat.mul_pos hK hL
    have haB : 0 < max a B := hB.trans_le (le_max_right _ _)
    have hhi : |∑ k ∈ Ico (max a B) (max b B), cosPrimitive t k| ≤ π / K := by
      have heq : (∑ k ∈ Ico (max a B) (max b B), cosPrimitive t k) =
          ∑ k ∈ Ico (max a B) (max b B), sin ((k : ℝ) * t) / k := by
        apply sum_congr rfl
        intro k hk
        exact if_neg (haB.trans_le (mem_Ico.mp hk).1).ne'
      rw [heq]
      apply (abs_sin_sum_div_le haB (max_le_max_right B hab) ht hπ).trans
      apply div_le_div_of_nonneg_left pi_pos.le hK'
      calc
        (K : ℝ) = K * 1 := (mul_one _).symm
        _ ≤ K * (L * t : ℝ) := mul_le_mul_of_nonneg_left htL hK'.le
        _ = B * t := by simp [B, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right a B) ht.le
    rw [split_clipped_block (B := B) hab]
    exact (abs_add_le _ _).trans (add_le_add hlo hhi)
  have hfull := sum_le_sum (s := range K) (fun j hj ↦ hblock j (mem_range.mp hj))
  rw [sum_add_distrib, sum_range_sub] at hfull
  simp at hfull
  rw [show (K : ℝ) * (π / K) = π by field_simp] at hfull
  have hS : S K ≤ ∑ k ∈ range B, |cosPrimitive t k| :=
    sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right _ _)) (fun i _ _ ↦ abs_nonneg _)
  have h0 : 0 ≤ S 0 := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hp := cosPrimitive_prefix hK hL ht.le hLt
  change (∑ k ∈ range B, |cosPrimitive t k|) ≤ _ at hp
  linarith



private theorem integral_cos_nat (t : ℝ) (k : ℕ) :
    (∫ x in 0..t, cos ((k : ℝ) * x)) = cosPrimitive t k := by
  by_cases hk : k = 0
  · simp [cosPrimitive, hk]
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [cosPrimitive, if_neg hk, intervalIntegral.integral_comp_mul_left _ hk', integral_cos]
    simp [div_eq_inv_mul]

/-- A cosine polynomial with K constant coefficient blocks has a uniformly
bounded primitive on the half-period. The bound is independent of the degrees. -/
theorem block_cosine_primitive_le {K : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
    (hcut : ∀ j < K, cut j ≤ cut (j+1)) (c : ℕ → ℝ)
    {M : ℝ} (hc : ∀ j < K, |c j| ≤ M) {t : ℝ} (ht : 0 ≤ t) (hπ : t ≤ π) :
    |∫ x in 0..t, ∑ j ∈ range K, c j * ∑ k ∈ Ico (cut j) (cut (j+1)), cos ((k : ℝ) * x)| ≤
      M * (2 + 2 * π + log K) := by
  have hM := (abs_nonneg (c 0)).trans (hc 0 hK)
  have hlog : 0 ≤ log (K : ℝ) := log_nonneg (by exact_mod_cast hK)
  rcases ht.eq_or_lt with rfl | ht
  · simp
    positivity
  rw [intervalIntegral.integral_finsetSum (fun j _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _)]
  have block (a b : ℕ) :
      (∫ x in 0..t, ∑ k ∈ Ico a b, cos ((k : ℝ) * x)) =
        ∑ k ∈ Ico a b, cosPrimitive t k := by
    rw [intervalIntegral.integral_finsetSum (fun k _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [integral_cos_nat]
  simp_rw [intervalIntegral.integral_const_mul, block]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range K, M * |∑ k ∈ Ico (cut j) (cut (j+1)), cosPrimitive t k| := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc j (mem_range.mp hj)) (abs_nonneg _)
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (cosPrimitive_variation hK cut hcut ht hπ) hM

end OMA.G82

namespace OMA.G82

open Set MeasureTheory intervalIntegral

/-- The sign of the integrand can be read from `f` on each zero-free interval,
even when its nonnegative weight introduces additional zeros. -/
private theorem integral_abs_mul_le_of_no_zero {f w : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hf : ContinuousOn f (Ioo u v))
    (hw : ∀ x ∈ Ioo u v, 0 ≤ w x) (hz : ∀ x ∈ Ioo u v, f x ≠ 0) :
    (∫ x in u..v, |f x * w x|) ≤ |∫ x in u..v, f x * w x| := by
  by_cases hp : ∀ x ∈ Ioo u v, 0 ≤ f x
  · rw [integral_congr_Ioo_of_le huv (g := fun x ↦ f x * w x)
      (fun x hx ↦ abs_of_nonneg (mul_nonneg (hp x hx) (hw x hx)))]
    exact le_abs_self _
  · push Not at hp
    obtain ⟨x, hx, hneg⟩ := hp
    have hn : ∀ y ∈ Ioo u v, f y ≤ 0 := by
      intro y hy
      by_contra! hpos
      obtain ⟨z, hz', he⟩ := isPreconnected_Ioo.intermediate_value hx hy hf
        (show (0 : ℝ) ∈ Icc (f x) (f y) from ⟨hneg.le, hpos.le⟩)
      exact hz z hz' he
    rw [integral_congr_Ioo_of_le huv (g := fun y ↦ -(f y * w y))
      (fun y hy ↦ abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (hn y hy) (hw y hy))),
      intervalIntegral.integral_neg]
    exact neg_le_abs _

/-- Split at the last zero and bound each newly added interval by the
difference of two values of the primitive. -/
theorem integral_abs_mul_le_of_finite_zeros {f w : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hn : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hB : ∀ x ∈ Icc a b, |∫ t in a..x, f t * w t| ≤ B)
    (hfinite : {x ∈ Ioo a b | f x = 0}.Finite) :
    (∫ t in a..b, |f t * w t|) ≤ 2 * (({x ∈ Ioo a b | f x = 0}.ncard : ℝ) + 1) * B := by
  classical
  let F (x : ℝ) := ∫ t in a..x, f t * w t
  have integrable_on {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
      IntervalIntegrable (fun x ↦ f x * w x) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact (hf.mul hw).mono (Icc_subset_Icc hu hv)
  have local_bound {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
      (hz : ∀ x ∈ Ioo u v, f x ≠ 0) : (∫ t in u..v, |f t * w t|) ≤ 2 * B := by
    have hsub : Ioo u v ⊆ Icc a b := fun x hx ↦
      ⟨hu.trans hx.1.le, hx.2.le.trans hv⟩
    have hsum : F u + (∫ t in u..v, f t * w t) = F v :=
      integral_add_adjacent_intervals (integrable_on le_rfl hu (huv.trans hv))
        (integrable_on hu huv hv)
    calc
      _ ≤ |∫ t in u..v, f t * w t| :=
        integral_abs_mul_le_of_no_zero huv (hf.mono hsub) (fun x hx ↦ hn x (hsub hx)) hz
      _ = |F v - F u| := by rw [← hsum]; ring_nf
      _ ≤ |F v| + |F u| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB v ⟨hu.trans huv, hv⟩, hB u ⟨hu, huv.trans hv⟩]
  have split_bound (s : Finset ℝ) : ∀ {v : ℝ}, a ≤ v → v ≤ b →
      (∀ x, x ∈ s ↔ x ∈ Ioo a v ∧ f x = 0) →
      (∫ t in a..v, |f t * w t|) ≤ 2 * ((s.card : ℝ) + 1) * B := by
    induction s using Finset.induction_on_max with
    | empty =>
      intro v hav hv hs
      have hz : ∀ x ∈ Ioo a v, f x ≠ 0 :=
        fun x hx hfx ↦ Finset.notMem_empty x ((hs x).2 ⟨hx, hfx⟩)
      simpa using local_bound le_rfl hav hv hz
    | insert u s hmax ih =>
      intro v hav hv hs
      have hu : u ∈ Ioo a v := ((hs u).1 (Finset.mem_insert_self u s)).1
      have hus : u ∉ s := fun h ↦ (lt_irrefl u) (hmax u h)
      have hleft : ∀ x, x ∈ s ↔ x ∈ Ioo a u ∧ f x = 0 := by
        intro x
        constructor
        · intro hx
          have hz := (hs x).1 (Finset.mem_insert_of_mem hx)
          exact ⟨⟨hz.1.1, hmax x hx⟩, hz.2⟩
        · rintro ⟨hx, hz⟩
          exact (Finset.mem_insert.mp ((hs x).2 ⟨⟨hx.1, hx.2.trans hu.2⟩, hz⟩)).resolve_left
            hx.2.ne
      have hright : ∀ x ∈ Ioo u v, f x ≠ 0 := by
        intro x hx hfx
        have hsx := (hs x).2 ⟨⟨hu.1.trans hx.1, hx.2⟩, hfx⟩
        have hx' := (Finset.mem_insert.mp hsx).resolve_left hx.1.ne'
        exact (lt_asymm hx.1 (hmax x hx'))
      have h1 := ih hu.1.le (hu.2.le.trans hv) hleft
      have h2 := local_bound hu.1.le hu.2.le hv hright
      rw [← integral_add_adjacent_intervals
        (integrable_on le_rfl hu.1.le (hu.2.le.trans hv)).abs
        (integrable_on hu.1.le hu.2.le hv).abs, Finset.card_insert_of_notMem hus,
        Nat.cast_add, Nat.cast_one]
      linarith
  simpa only [Set.ncard_eq_toFinset_card _ hfinite] using
    split_bound hfinite.toFinset hab le_rfl (fun _ ↦ hfinite.mem_toFinset)

/-- Unweighted bound for a continuous function. -/
theorem integral_abs_le_of_finite_zeros {f : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hB : ∀ x ∈ Icc a b, |∫ t in a..x, f t| ≤ B)
    (hfinite : {x ∈ Ioo a b | f x = 0}.Finite) :
    (∫ t in a..b, |f t|) ≤ 2 * (({x ∈ Ioo a b | f x = 0}.ncard : ℝ) + 1) * B := by
  simpa using integral_abs_mul_le_of_finite_zeros (w := fun _ ↦ 1) hab hf continuousOn_const
    (fun _ _ ↦ zero_le_one) (by simpa using hB) hfinite

end OMA.G82

namespace OMA.G82

open Finset Real Set MeasureTheory

noncomputable def blockPoly (J : ℕ) (cut : ℕ → ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range J, c j * ∑ k ∈ Finset.Ico (cut j) (cut (j+1)), cos ((k : ℝ) * x)

private theorem blockPoly_reflect (J : ℕ) (cut : ℕ → ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    blockPoly J cut c (2 * π * (1 - θ)) = blockPoly J cut c (2 * π * θ) := by
  apply sum_congr rfl
  intro j _
  apply congrArg (c j * ·)
  apply sum_congr rfl
  intro k _
  rw [show (k : ℝ) * (2 * π * (1-θ)) = (k : ℝ)*(2*π) - (k : ℝ)*(2*π*θ) by ring]
  exact cos_nat_mul_two_pi_sub _ _

/-- The square multiplier can introduce additional zeros. Counting only the
zeros of the original polynomial suffices for the full-period integral bound. -/
theorem weighted_block_l1_upper {N J : ℕ} (b : ℕ → ℕ) (hg : cosineSum N b 0 ≠ 0)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ θ, 0 ≤ w θ)
    (hJ : 0 < J) (cut : ℕ → ℕ) (hcut : ∀ j < J, cut j ≤ cut (j+1))
    (c : ℕ → ℝ) {M : ℝ} (hc : ∀ j < J, |c j| ≤ M)
    (he : ∀ θ, cosineSum N b θ * w θ = blockPoly J cut c (2 * π * θ)) :
    (∫ θ in (0 : ℝ)..1, |cosineSum N b θ * w θ|) ≤
      4 * ((halfRoots N b : ℝ) + 1) * (M * (2 + 2 * π + log J)) := by
  let f := cosineSum N b
  have hf : Continuous f := by unfold f cosineSum; fun_prop
  have hB : 0 ≤ M * (2 + 2 * π + log J) := by
    have hM := (abs_nonneg _).trans (hc 0 hJ)
    have hlog := log_nonneg (show (1 : ℝ) ≤ J by exact_mod_cast hJ)
    positivity
  have hprim (x : ℝ) (hx : x ∈ Set.Icc 0 (1/2)) :
      |∫ θ in 0..x, f θ * w θ| ≤ M * (2 + 2 * π + log J) := by
    change |∫ θ in 0..x, cosineSum N b θ * w θ| ≤ _
    simp_rw [he]
    rw [intervalIntegral.integral_comp_mul_left _ (by positivity : 2 * π ≠ 0), mul_zero,
      smul_eq_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * π)⁻¹)]
    have hb := block_cosine_primitive_le hJ cut hcut c hc
      (t := 2 * π * x) (mul_nonneg (by positivity) hx.1) (by nlinarith [mul_le_mul_of_nonneg_left hx.2 pi_pos.le])
    apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 * π)⁻¹)).trans
    exact mul_le_of_le_one_left hB (inv_le_one_of_one_le₀ (by linarith [pi_gt_three]))
  have hfinite : {x ∈ Set.Ioo 0 (1/2) | f x = 0}.Finite := by
    apply (finite_zeros_Icc (analytic_cosine_sum N b) hg).subset
    rintro x ⟨⟨h1,h2⟩,hz⟩
    exact ⟨⟨h1.le, by linarith⟩, hz⟩
  have hhalf := integral_abs_mul_le_of_finite_zeros (by norm_num : (0:ℝ) ≤ 1/2)
    hf.continuousOn hw.continuousOn (fun x _ ↦ hw0 x) hprim hfinite
  let F (θ : ℝ) := |f θ * w θ|
  have hF : Continuous F := (hf.mul hw).abs
  have hsym (θ : ℝ) : F (1-θ) = F θ :=
    congrArg abs (((he (1-θ)).trans (blockPoly_reflect J cut c θ)).trans (he θ).symm)
  have hint := intervalIntegral.integral_comp_sub_left (a := (1/2:ℝ)) (b := 1) F 1
  simp only [hsym, sub_self, show (1:ℝ) - 1/2 = 1/2 by norm_num] at hint
  change (∫ θ in 0..1, F θ) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (a := 0) (b := 1/2)) (hF.intervalIntegrable (a := 1/2) (b := 1)), hint]
  change (∫ θ in 0..1/2, F θ) ≤ 2 * ((halfRoots N b : ℝ) + 1) * _ at hhalf
  linarith

/-- The data of a filtered cosine polynomial on one turn. The frequency cut
count and coefficient sizes are on the scales KP and P² respectively. -/
def SmoothedBlockEstimate : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (b : ℕ → ℕ) (K P : ℕ),
    (∀ k ≤ N, b k ≤ 2) → 0 < b N → 2 ≤ cosineSum N b 0 →
    0 < K → 0 < P → PeriodicPieces N b K P →
    ∃ (w : ℝ → ℝ) (J : ℕ) (cut : ℕ → ℕ) (c : ℕ → ℝ),
      Continuous w ∧ (∀ θ, 0 ≤ w θ) ∧ 0 < J ∧ J ≤ 100 * K * P ∧
      (∀ j < J, cut j ≤ cut (j+1)) ∧ (∀ j < J, |c j| ≤ 8 * (P : ℝ)^2) ∧
      (∀ θ, cosineSum N b θ * w θ = blockPoly J cut c (2 * π * θ)) ∧
      δ * log (cosineSum N b 0 / 2) ≤ ∫ θ in (0 : ℝ)..1, |cosineSum N b θ * w θ|

theorem structuredRootEstimate_of_smoothed (hs : SmoothedBlockEstimate) :
    StructuredRootEstimate := by
  obtain ⟨δ,hδ,hs⟩ := hs
  let H := 2 + 2 * π + log 100
  have hH : 1 ≤ H := by dsimp [H]; linarith [pi_pos, log_nonneg (by norm_num : (1:ℝ) ≤ 100)]
  let A := 1 + log 2 + 32 * H / δ
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    linarith [log_nonneg (by norm_num : (1:ℝ) ≤ 2),
      div_nonneg (show 0 ≤ 32 * H by linarith) hδ.le]
  intro N b K P hcoef hN hmass hK hP hpieces
  obtain ⟨w,J,cut,c,hw,hn,hJ,hsize,hcut,hc,he,hlo⟩ := hs N b K P hcoef hN hmass hK hP hpieces
  have hhi := weighted_block_l1_upper b (by linarith : cosineSum N b 0 ≠ 0)
    w hw hn hJ cut hcut c hc he
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hKP := one_le_mul_of_one_le_of_one_le hK' hP'
  have hlog := log_nonneg hKP
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hlogJ : log J ≤ log 100 + log ((K : ℝ) * P) := by
    rw [← log_mul (by norm_num : (100 : ℝ) ≠ 0) (by positivity)]
    apply log_le_log hJ'
    rw [← mul_assoc]
    exact_mod_cast hsize
  have hb : 2 + 2 * π + log J ≤ H * (1 + log ((K : ℝ) * P)) := by
    calc
      _ ≤ H + log ((K : ℝ) * P) := by dsimp [H]; linarith
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hH) hlog]
  let d := (halfRoots N b : ℝ) + 1
  let Z := d * (P : ℝ)^2 * (1 + log ((K : ℝ) * P))
  have hd : 1 ≤ d := by dsimp [d]; linarith [Nat.cast_nonneg (α := ℝ) (halfRoots N b)]
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hd (one_le_pow₀ hP')) (by linarith)
  have hmain : δ * log (cosineSum N b 0 / 2) ≤ 32 * H * Z := by
    apply (hlo.trans hhi).trans
    change 4 * d * (8 * (P : ℝ)^2 * _) ≤ _
    calc
      _ ≤ 4 * d * (8 * (P : ℝ)^2 * (H * (1 + log ((K : ℝ) * P)))) := by gcongr
      _ = _ := by dsimp [Z]; ring
  rw [log_div (by linarith) (by norm_num)] at hmain
  have hr : log (cosineSum N b 0) - log 2 ≤ (32 * H / δ) * Z := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
  have hconst := le_mul_of_one_le_right (log_nonneg (by norm_num : (1:ℝ) ≤ 2)) hZ
  calc
    log (cosineSum N b 0) ≤ A * Z := by dsimp [A]; nlinarith
    _ = _ := by dsimp [Z,d]; ring

end OMA.G82

namespace OMA.G82

open scoped BigOperators ComplexConjugate
open Finset

/-- The angular variable is measured in radians. -/
noncomputable def angularCharacter (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((k : ℂ) * (t : ℂ)) * Complex.I)

private theorem angularCharacter_add (k d : ℤ) (t : ℝ) :
    angularCharacter (k + d) t = angularCharacter k t * angularCharacter d t := by
  simp only [angularCharacter, Int.cast_add, add_mul, Complex.exp_add]

private theorem angularCharacter_neg (k : ℤ) (t : ℝ) :
    angularCharacter (-k) t = conj (angularCharacter k t) := by
  rw [angularCharacter, angularCharacter, ← Complex.exp_conj]
  congr 1
  simp

/-- The trigonometric polynomial represented by a finitely supported Laurent coefficient list. -/
noncomputable def fourierValue (c : ℤ →₀ ℤ) (t : ℝ) : ℂ :=
  c.sum fun k m ↦ (m : ℂ) * angularCharacter k t

private theorem fourierValue_shift (c : ℤ →₀ ℤ) (d : ℤ) (t : ℝ) :
    fourierValue (c.mapDomain (· + d)) t = fourierValue c t * angularCharacter d t := by
  unfold fourierValue
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [add_mul])]
  simp [Finsupp.sum, angularCharacter_add, sum_mul, mul_assoc]

/-- Smoothing by all differences of two elements of the period window. -/
noncomputable def smoothCoeffs (c : ℤ →₀ ℤ) (P : ℕ) : ℤ →₀ ℤ :=
  ∑ j ∈ range P, ∑ i ∈ range P, c.mapDomain (fun k ↦ k + ((j : ℤ) - i))

theorem smoothCoeffs_apply (c : ℤ →₀ ℤ) (P : ℕ) (n : ℤ) :
    smoothCoeffs c P n = ∑ j ∈ range P, ∑ i ∈ range P, c (n - j + i) := by
  simp only [smoothCoeffs, Finsupp.finsetSum_apply]
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ ?_
  have he := Finsupp.mapDomain_apply (f := fun k : ℤ ↦ k + ((j : ℤ) - i))
    (fun _ _ h ↦ add_right_cancel h) c (n - j + i)
  convert he using 2
  omega

/-- In the angular variable the multiplier is real and nonnegative. -/
theorem fourierValue_smoothCoeffs (c : ℤ →₀ ℤ) (P : ℕ) (t : ℝ) :
    fourierValue (smoothCoeffs c P) t =
      fourierValue c t * (Complex.normSq (∑ j ∈ range P, angularCharacter j t) : ℂ) := by
  have eval_sum (s : Finset ℕ) (g : ℕ → ℤ →₀ ℤ) :
      fourierValue (∑ i ∈ s, g i) t = ∑ i ∈ s, fourierValue (g i) t := by
    unfold fourierValue
    exact (Finsupp.sum_finsetSum_index (fun _ ↦ by simp)
      (fun _ _ _ ↦ by simp [add_mul])).symm
  simp only [smoothCoeffs, eval_sum, fourierValue_shift, sub_eq_add_neg,
    angularCharacter_add, angularCharacter_neg, ← Complex.mul_conj, map_sum]
  simp only [sum_mul, mul_sum]
  rw [Finset.sum_comm]

theorem fourierValue_smoothCoeffs_zero (c : ℤ →₀ ℤ) (P : ℕ) :
    fourierValue (smoothCoeffs c P) 0 = fourierValue c 0 * (P : ℂ)^2 := by
  rw [fourierValue_smoothCoeffs]
  simp [angularCharacter, pow_two]

theorem abs_smoothCoeffs_le {c : ℤ →₀ ℤ} {M : ℤ} (hc : ∀ n, |c n| ≤ M)
    (P : ℕ) (n : ℤ) : |smoothCoeffs c P n| ≤ M * (P : ℤ)^2 := by
  rw [smoothCoeffs_apply]
  calc
    _ ≤ ∑ j ∈ range P, |∑ i ∈ range P, c (n - j + i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range P, ∑ _i ∈ range P, M := by
      gcongr with j
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ hc _)
    _ = _ := by simp; ring

/-- Moving a window one place to the right replaces only its two end terms. -/
private theorem sum_window_step (c : ℤ → ℤ) (P : ℕ) (a : ℤ) :
    (∑ i ∈ range P, c (a + 1 + i)) - (∑ i ∈ range P, c (a + i)) =
      c (a + P) - c a := by
  induction P with
  | zero => simp
  | succ k ih =>
    simp only [sum_range_succ, Nat.cast_succ]
    rw [show a + 1 + (k : ℤ) = a + ((k : ℤ) + 1) by ring]
    omega

/-- The smoothed sequence is constant across adjacent interior sites of any periodic block. -/
theorem smoothCoeffs_succ_eq {c : ℤ →₀ ℤ} {P : ℕ} {n : ℤ}
    (h : ∀ j ∈ range P, c (n - j + P) = c (n - j)) :
    smoothCoeffs c P (n + 1) = smoothCoeffs c P n := by
  rw [smoothCoeffs_apply, smoothCoeffs_apply]
  apply sum_congr rfl
  intro j hj
  have hstep := sum_window_step c P (n - j)
  rw [h j hj, sub_self, sub_eq_zero] at hstep
  simpa only [show n - j + 1 = n + 1 - j by ring] using hstep

/-- Every coefficient on the interval left after trimming a period from each end
of a periodic coefficient block has the same value. -/
theorem smoothCoeffs_eq_on_trimmed_block {c : ℤ →₀ ℤ} {P : ℕ} {u v m n : ℤ}
    (hper : ∀ k, u ≤ k → k + P ≤ v → c (k + P) = c k)
    (hm : u + P ≤ m) (hmn : m ≤ n) (hn : n + P ≤ v) :
    smoothCoeffs c P m = smoothCoeffs c P n := by
  induction n, hmn using Int.leInduction with
  | base => rfl
  | succ k hmk ih =>
    have hk : k + P ≤ v := by omega
    refine (ih hk).trans (smoothCoeffs_succ_eq ?_).symm
    intro j hj
    have hj' := mem_range.mp hj
    apply hper <;> omega

/-- If each failure of period `P` crosses a cut, the smoothed coefficients
can change at most `2 * P` times per cut. -/
theorem smoothCoeffs_jump_cover {c : ℤ →₀ ℤ} {P : ℕ} (cuts : Finset ℤ)
    (hcuts : ∀ k : ℤ, c (k + P) ≠ c k → ∃ t ∈ cuts, k < t ∧ t ≤ k + P) :
    ∃ jumps : Finset ℤ, jumps.card ≤ cuts.card * (2 * P) ∧
      ∀ n : ℤ, n ∉ jumps → smoothCoeffs c P (n + 1) = smoothCoeffs c P n := by
  let near (t : ℤ) := Finset.Ico (t - P) (t + P)
  refine ⟨cuts.biUnion near, card_biUnion_le_card_mul _ _ _ ?_, ?_⟩
  · intro t _
    simp only [near, Int.card_Ico]
    omega
  · intro n hn
    refine smoothCoeffs_succ_eq fun j hj ↦ ?_
    by_contra h
    obtain ⟨t, ht, h1, h2⟩ := hcuts (n - j) h
    have hj' := mem_range.mp hj
    apply hn
    exact mem_biUnion.mpr ⟨t, ht, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩

/-- Reflection counts the constant twice, so that every cosine has the same normalization. -/
noncomputable def reflectedCoeffs (N : ℕ) (b : ℕ → ℕ) : ℤ →₀ ℤ :=
  ∑ k ∈ range (N + 1),
    (Finsupp.single (k : ℤ) (b k : ℤ) + Finsupp.single (-(k : ℤ)) (b k : ℤ))

theorem reflectedCoeffs_apply (N : ℕ) (b : ℕ → ℕ) (n : ℤ) :
    reflectedCoeffs N b n = if n.natAbs ≤ N then
      (if n = 0 then 2 else 1) * (b n.natAbs : ℤ) else 0 := by
  simp only [reflectedCoeffs, Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply]
  have hoff (k : ℕ) (hne : k ≠ n.natAbs) :
      (if (k : ℤ) = n then (b k : ℤ) else 0) + (if -(k : ℤ) = n then (b k : ℤ) else 0) = 0 := by
    have h1 : (k : ℤ) ≠ n := fun he ↦ hne (by simpa using congrArg Int.natAbs he)
    have h2 : -(k : ℤ) ≠ n := fun he ↦ hne (by simpa using congrArg Int.natAbs he)
    simp [h1, h2]
  by_cases h : n.natAbs ≤ N
  · rw [if_pos h, sum_eq_single_of_mem n.natAbs (mem_range.mpr (by omega))
      (fun k _ hne ↦ hoff k hne)]
    cases n with
    | ofNat k =>
      simp only [Int.natAbs_natCast, Int.ofNat_eq_natCast, if_true]
      split_ifs <;> omega
    | negSucc k =>
      simp only [Int.negSucc_eq]
      split_ifs <;> omega
  · rw [if_neg h]
    apply sum_eq_zero
    intro k hk
    exact hoff k (by have := mem_range.mp hk; omega)

theorem fourierValue_reflectedCoeffs (N : ℕ) (b : ℕ → ℕ) (t : ℝ) :
    fourierValue (reflectedCoeffs N b) t =
      ((2 * ∑ k ∈ range (N + 1), (b k : ℝ) * Real.cos ((k : ℝ) * t) : ℝ) : ℂ) := by
  unfold fourierValue reflectedCoeffs
  rw [← Finsupp.sum_finsetSum_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [add_mul])]
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat, Finset.mul_sum]
  apply sum_congr rfl
  intro k _
  rw [Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [add_mul]),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  rw [angularCharacter_neg, ← mul_add, Complex.add_conj, angularCharacter]
  rw [show (↑(↑k : ℤ) : ℂ) * (t : ℂ) = (((k : ℝ) * t : ℝ) : ℂ) by simp,
    Complex.exp_ofReal_mul_I_re]
  push_cast
  ring

/-- Order the finitely many change points of a real coefficient sequence and group
the corresponding terms into constant blocks. Empty blocks are unnecessary. -/
private theorem make_constant_blocks (a : ℕ → ℝ) (s : Finset ℕ) :
    ∀ T : ℕ, (∀ k ∈ s, 0 < k ∧ k < T) →
    (∀ k, k + 1 < T → k + 1 ∉ s → a (k+1) = a k) →
    ∃ cut : ℕ → ℕ, cut 0 = 0 ∧ cut (s.card+1) = T ∧
      (∀ j < s.card+1, cut j ≤ cut (j+1)) ∧
      ∀ j < s.card+1, ∀ k ∈ Ico (cut j) (cut (j+1)), a k = a (cut j) := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
    intro T _ h
    refine ⟨fun j ↦ if j = 0 then 0 else T, by simp, by simp, ?_, ?_⟩
    · intro j hj
      have hj' : j = 0 := by simpa using hj
      simp [hj']
    · intro j hj k hk
      have hj' : j = 0 := by simpa using hj
      simp [hj'] at hk ⊢
      induction k with
      | zero => rfl
      | succ k ih => exact (h k hk (by simp)).trans (ih (by omega))
  | insert u s hmax ih =>
    intro T hs hn
    have hu := hs u (mem_insert_self _ _)
    have hus : u ∉ s := fun h ↦ (lt_irrefl u) (hmax u h)
    obtain ⟨c, hc0, hcu, hcmono, hconst⟩ := ih u
      (fun k hk ↦ ⟨(hs k (mem_insert_of_mem hk)).1, hmax k hk⟩)
      (fun k hk hks ↦ hn k (hk.trans hu.2) (by simp [hks, hk.ne]))
    rw [card_insert_of_notMem hus]
    let cut (j : ℕ) := if j ≤ s.card+1 then c j else T
    refine ⟨cut, by simp [cut, hc0], by simp [cut], ?_, ?_⟩
    · intro j hj
      by_cases h : j < s.card+1
      · simpa [cut, h.le, Nat.le_of_lt_succ h] using hcmono j h
      · have he : j = s.card+1 := by omega
        simp [cut, he, hcu, hu.2.le]
    · intro j hj k hk
      by_cases h : j < s.card+1
      · have hm := hconst j h k
        simpa [cut, h.le, Nat.le_of_lt_succ h] using hm (by simpa [cut, h.le, Nat.le_of_lt_succ h] using hk)
      · have he : j = s.card+1 := by omega
        simp [cut, he, hcu] at hk ⊢
        obtain ⟨huk, hkt⟩ := hk
        induction k, huk using Nat.le_induction with
        | base => rfl
        | succ k huk ih' =>
          have hks : k + 1 ∉ insert u s := by
            intro hh
            rcases mem_insert.mp hh with he | he
            · omega
            · have := hmax _ he
              omega
          exact (hn k hkt hks).trans (ih' (by omega))

private theorem block_reindex (cut : ℕ → ℕ) {J : ℕ} (hc : ∀ j < J, cut j ≤ cut (j+1))
    (a v : ℕ → ℝ) (h : ∀ j < J, ∀ k ∈ Ico (cut j) (cut (j+1)), a k = a (cut j)) :
    ∑ j ∈ range J, a (cut j) * ∑ k ∈ Ico (cut j) (cut (j+1)), v k =
      ∑ k ∈ Ico (cut 0) (cut J), a k * v k := by
  calc
    _ = ∑ j ∈ range J, ∑ k ∈ Ico (cut j) (cut (j+1)), a k * v k := by
      apply sum_congr rfl
      intro j hj
      rw [mul_sum]
      exact sum_congr rfl fun k hk ↦ by rw [h j (mem_range.mp hj) k hk]
    _ = _ := by
      induction J with
      | zero => simp
      | succ n ih =>
        have hm : ∀ j < n, cut j ≤ cut (j+1) := fun j hj ↦ hc j (by omega)
        have h' : cut 0 ≤ cut n := by
          have hmono : MonotoneOn cut (Set.Iic n) := monotoneOn_of_le_succ Set.ordConnected_Iic
            (fun j _ _ hsucc ↦ hm j (Nat.lt_of_succ_le hsucc))
          exact hmono (a := 0) (b := n) (Nat.zero_le n) (show n ≤ n from le_rfl) (Nat.zero_le n)
        rw [sum_range_succ, ih hm (fun j hj ↦ h j (by omega)),
          sum_Ico_consecutive _ h' (hc n (by omega))]

theorem abs_reflectedCoeffs_le_four {N : ℕ} {b : ℕ → ℕ} (hb : ∀ k ≤ N, b k ≤ 2) (n : ℤ) :
    |reflectedCoeffs N b n| ≤ 4 := by
  rw [reflectedCoeffs_apply]
  split_ifs with h h0 <;> simp <;> have := hb _ h <;> omega

private theorem smooth_reflected_even (N P : ℕ) (b : ℕ → ℕ) (n : ℤ) :
    smoothCoeffs (reflectedCoeffs N b) P (-n) = smoothCoeffs (reflectedCoeffs N b) P n := by
  rw [smoothCoeffs_apply, smoothCoeffs_apply, sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [show -n - j + i = -(n - i + j) by ring]
  generalize n - (i : ℤ) + j = z
  simp [reflectedCoeffs_apply]

private theorem smooth_reflected_nonneg (N P : ℕ) (b : ℕ → ℕ) (n : ℤ) :
    0 ≤ smoothCoeffs (reflectedCoeffs N b) P n := by
  rw [smoothCoeffs_apply]
  refine sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ ?_
  rw [reflectedCoeffs_apply]
  split_ifs <;> positivity

private theorem smooth_reflected_vanish {N P : ℕ} (b : ℕ → ℕ) {n : ℤ}
    (hn : N + P < n.natAbs) : smoothCoeffs (reflectedCoeffs N b) P n = 0 := by
  rw [smoothCoeffs_apply]
  refine sum_eq_zero fun j hj ↦ sum_eq_zero fun i hi ↦ ?_
  have hj' := mem_range.mp hj
  have hi' := mem_range.mp hi
  rw [reflectedCoeffs_apply, if_neg]
  omega

private noncomputable def foldedSmooth (N P : ℕ) (b : ℕ → ℕ) (k : ℕ) : ℕ :=
  (if k = 0 then 1 else 2) * (smoothCoeffs (reflectedCoeffs N b) P k).toNat

private theorem reflected_foldedSmooth (N P : ℕ) (b : ℕ → ℕ) :
    reflectedCoeffs (N+P) (foldedSmooth N P b) =
      smoothCoeffs (reflectedCoeffs N b) P + smoothCoeffs (reflectedCoeffs N b) P := by
  ext n
  rw [reflectedCoeffs_apply, Finsupp.add_apply]
  by_cases ha : n.natAbs ≤ N + P
  · rw [if_pos ha]
    have hcast : (↑((smoothCoeffs (reflectedCoeffs N b) P (n.natAbs : ℤ)).toNat) : ℤ) =
        smoothCoeffs (reflectedCoeffs N b) P (n.natAbs : ℤ) :=
      Int.toNat_of_nonneg (smooth_reflected_nonneg ..)
    have he : smoothCoeffs (reflectedCoeffs N b) P (n.natAbs : ℤ) =
        smoothCoeffs (reflectedCoeffs N b) P n := by
      rw [Int.natCast_natAbs]
      rcases le_total 0 n with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, smooth_reflected_even]
    simp only [foldedSmooth, Nat.cast_mul, he]
    split_ifs <;> omega
  · rw [if_neg ha, smooth_reflected_vanish b (by omega), zero_add]

/-- The smoothed Fourier polynomial in its real cosine basis, before making the blocks. -/
private theorem foldedSmooth_eval (N P : ℕ) (b : ℕ → ℕ) (t : ℝ) :
    2 * (∑ k ∈ range (N + 1), (b k : ℝ) * Real.cos ((k : ℝ)*t)) *
        Complex.normSq (∑ j ∈ range P, angularCharacter j t) =
      ∑ k ∈ range (N + P + 1), (foldedSmooth N P b k : ℝ) * Real.cos ((k : ℝ)*t) := by
  have he := fourierValue_reflectedCoeffs (N+P) (foldedSmooth N P b) t
  rw [reflected_foldedSmooth] at he
  have hlin (s : ℤ →₀ ℤ) : fourierValue (s+s) t = fourierValue s t + fourierValue s t := by
    unfold fourierValue
    rw [Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [add_mul])]
  rw [hlin, fourierValue_smoothCoeffs, fourierValue_reflectedCoeffs] at he
  have hh := congrArg Complex.re he
  simp only [Complex.ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_add] at hh
  linarith

private theorem find_frequency_block (v : ℕ → ℕ) {K r : ℕ} (h0 : v 0 ≤ r)
    (hK : r < v K) : ∃ l < K, v l ≤ r ∧ r < v (l+1) := by
  induction K with
  | zero => omega
  | succ k ih =>
    by_cases hr : r < v k
    · obtain ⟨l, hl, hh⟩ := ih hr
      exact ⟨l, by omega, hh⟩
    · exact ⟨k, by omega, by omega, hK⟩

/-- The canonical squared geometric multiplier has a cosine block decomposition
with a linear cost in the number of original pieces times the period. -/
theorem periodic_smooth_block_expansion {N K P : ℕ} (b : ℕ → ℕ)
    (hb : ∀ k ≤ N, b k ≤ 2) (hK : 0 < K) (hP : 0 < P) (v : ℕ → ℕ)
    (hv0 : v 0 = 0) (hvK : v K = N+1)
    (hper : ∀ l < K, ∀ i, v l ≤ i → i + P < v (l+1) → b (i+P) = b i) :
    ∃ (J : ℕ) (cut : ℕ → ℕ) (c : ℕ → ℝ),
      0 < J ∧ J ≤ 100*K*P ∧ (∀ j < J, cut j ≤ cut (j+1)) ∧
      (∀ j < J, |c j| ≤ 8*(P : ℝ)^2) ∧ ∀ t : ℝ,
        2 * (∑ k ∈ range (N+1), (b k : ℝ) * Real.cos ((k : ℝ)*t)) *
            Complex.normSq (∑ j ∈ range P, angularCharacter j t) =
          ∑ j ∈ range J, c j * ∑ k ∈ Ico (cut j) (cut (j+1)), Real.cos ((k : ℝ)*t) := by
  classical
  let a := foldedSmooth N P b
  let T := N+P+1
  let near (j : ℕ) := Ico (v j-P) (v j+P+2)
  let s := ((range (K+1)).biUnion near).filter (fun k ↦ 0 < k ∧ k < T)
  have hs (k : ℕ) (hk : k ∈ s) : 0 < k ∧ k < T := (mem_filter.mp hk).2
  have hcard : s.card ≤ (K+1) * (2*P+2) := by
    apply card_filter_le .. |>.trans
    have hh := card_biUnion_le_card_mul (range (K+1)) near (2*P+2) (by
      intro j _
      simp only [near, Nat.card_Ico]
      omega)
    simpa using hh
  have hstep (k : ℕ) (hk : k+1 < T) (hks : k+1 ∉ s) : a (k+1) = a k := by
    have hfar (l : ℕ) (hl : l ≤ K) : k+1 ∉ near l :=
      fun hn ↦ hks (mem_filter.mpr ⟨mem_biUnion.mpr ⟨l, mem_range.mpr (by omega), hn⟩,
        by omega, hk⟩)
    have hkP : P ≤ k := by
      have hh := hfar 0 (Nat.zero_le _)
      simp [near, hv0] at hh
      omega
    have hsm : smoothCoeffs (reflectedCoeffs N b) P ((k : ℤ) + 1) =
        smoothCoeffs (reflectedCoeffs N b) P k := by
      apply smoothCoeffs_succ_eq
      intro j hj
      have hj' := mem_range.mp hj
      let r := k-j
      have hr : 0 < r := by dsimp [r]; omega
      have he : (k : ℤ) - (j : ℤ) = (r : ℤ) := by dsimp [r]; omega
      rw [he, ← Nat.cast_add, reflectedCoeffs_apply, reflectedCoeffs_apply]
      simp only [Int.natAbs_natCast, Nat.cast_eq_zero]
      rw [if_neg hr.ne', if_neg (show r + P ≠ 0 by omega)]
      by_cases hrN : r ≤ N
      · obtain ⟨l, hl, hl1, hl2⟩ := find_frequency_block v (by simp [hv0] : v 0 ≤ r)
          (by omega : r < v K)
        have hright : r+P < v (l+1) := by
          by_contra! hh
          have hbad := hfar (l+1) (by omega)
          apply hbad
          apply mem_Ico.mpr
          dsimp [r] at hh hl2
          omega
        have hrP : r + P ≤ N := by
          by_contra! hex
          have hbad := hfar K le_rfl
          apply hbad
          apply mem_Ico.mpr
          dsimp [r] at hex hrN
          omega
        simp [hrN, hrP, hper l hl r hl1 hright]
      · simp [hrN, show ¬r+P ≤ N by omega]
    simp [a, foldedSmooth, show k ≠ 0 by omega, hsm]
  obtain ⟨cut, h0, hT, hm, hc⟩ := make_constant_blocks (fun k ↦ (a k : ℝ)) s T hs
    (fun k hk hks ↦ by rw [hstep k hk hks])
  refine ⟨s.card+1, cut, fun j ↦ ((a (cut j) : ℕ) : ℝ), by omega, ?_, hm, ?_, ?_⟩
  · have hK1 : K+1 ≤ 2*K := by omega
    have hP1 : 2*P+2 ≤ 4*P := by omega
    have hp := hcard.trans (Nat.mul_le_mul hK1 hP1)
    have hprod : 0 < K*P := Nat.mul_pos hK hP
    nlinarith
  · intro j _
    let k := cut j
    have habs := abs_smoothCoeffs_le (abs_reflectedCoeffs_le_four hb) P (k : ℤ)
    have hnonneg := smooth_reflected_nonneg N P b (k : ℤ)
    have hbd : ((a k : ℕ) : ℤ) ≤ 8*(P : ℤ)^2 := by
      simp only [a, foldedSmooth, Nat.cast_mul, Int.toNat_of_nonneg hnonneg]
      rw [abs_of_nonneg hnonneg] at habs
      split_ifs <;> push_cast <;> nlinarith
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    change (a k : ℝ) ≤ 8 * (P : ℝ)^2
    exact_mod_cast hbd
  · intro t
    rw [foldedSmooth_eval, block_reindex cut hm _ _ hc, h0, hT, Nat.Ico_zero_eq_range]

end OMA.G82

namespace OMA.G82

open Finset

/-- The external Littlewood inequality in §2, with the increasing frequency
order recorded by an order embedding and the angular integral normalized to
one full turn. -/
def LittlewoodL1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (ν : Fin k ↪o ℤ) (a : Fin k → ℂ),
    c * (∑ j, ‖a j‖ / ((j.val : ℝ) + 1)) ≤
      ∫ t in (0 : ℝ)..1, ‖∑ j, a j * angularCharacter (ν j) (2 * Real.pi * t)‖

/-- The signed integer lattice supplies a unit gap at every occupied frequency.
Evaluation at zero then bounds the number of occupied frequencies from below. -/
theorem integer_fourier_l1_lower (hmps : LittlewoodL1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℤ →₀ ℤ) (M : ℝ),
      0 < M → 0 < ‖fourierValue f 0‖ → (∀ k, ‖(f k : ℂ)‖ ≤ M) →
      C * Real.log (‖fourierValue f 0‖ / M) ≤
        ∫ t in (0 : ℝ)..1, ‖fourierValue f (2 * Real.pi * t)‖ := by
  obtain ⟨C, hC, H⟩ := hmps
  refine ⟨C, hC, ?_⟩
  intro f M hM h0 hmax
  let k := f.support.card
  let ν : Fin k ↪o ℤ := f.support.orderEmbOfFin rfl
  have eval_formula (t : ℝ) :
      fourierValue f t = ∑ j : Fin k, (f (ν j) : ℂ) * angularCharacter (ν j) t := by
    unfold fourierValue Finsupp.sum
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ f.support (k := k) rfl]
    rw [Finset.sum_map]
    rfl
  have hsize : ‖fourierValue f 0‖ ≤ (k : ℝ) * M := by
    rw [eval_formula]
    calc
      _ ≤ ∑ j : Fin k, ‖(f (ν j) : ℂ) * angularCharacter (ν j) 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin k, M := by
        apply Finset.sum_le_sum
        intro j _
        simpa [angularCharacter] using hmax (ν j)
      _ = _ := by simp
  have hunit (j : Fin k) : 1 ≤ ‖(f (ν j) : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (Finsupp.mem_support_iff.mp (f.support.orderEmbOfFin_mem rfl j))
  have hsum : (harmonic k : ℝ) ≤ ∑ j : Fin k, ‖(f (ν j) : ℂ)‖ / ((j.val : ℝ) + 1) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_succ, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum (fun j _ ↦ by
      simpa only [one_div] using
        (div_le_div_of_nonneg_right (hunit j) (by positivity : 0 ≤ (j.val : ℝ) + 1)))
  calc
    C * Real.log (‖fourierValue f 0‖ / M) ≤ C * (harmonic k : ℝ) := by
      gcongr
      apply le_trans _ (log_add_one_le_harmonic k)
      apply Real.log_le_log (div_pos h0 hM)
      exact ((div_le_iff₀ hM).2 hsize).trans (by norm_num)
    _ ≤ C * (∑ j : Fin k, ‖(f (ν j) : ℂ)‖ / ((j.val : ℝ) + 1)) := by gcongr
    _ ≤ _ := by simpa only [eval_formula] using H k ν (fun j ↦ (f (ν j) : ℂ))

end OMA.G82

namespace OMA.G82

open Real Finset

noncomputable def windowWeight (P : ℕ) (θ : ℝ) : ℝ :=
  2 * Complex.normSq (∑ j ∈ range P, angularCharacter j (2 * π * θ))

theorem continuous_windowWeight (P : ℕ) : Continuous (windowWeight P) := by
  unfold windowWeight angularCharacter
  fun_prop

theorem windowWeight_nonneg (P : ℕ) (θ : ℝ) : 0 ≤ windowWeight P θ :=
  mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

theorem smoothed_norm_at_angle (N P : ℕ) (b : ℕ → ℕ) (θ : ℝ) :
    ‖fourierValue (smoothCoeffs (reflectedCoeffs N b) P) (2 * π * θ)‖ =
      |cosineSum N b θ * windowWeight P θ| := by
  rw [fourierValue_smoothCoeffs, fourierValue_reflectedCoeffs, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs]
  congr 1
  unfold cosineSum windowWeight
  rw [mul_assoc, mul_left_comm 2]
  congr 1
  apply sum_congr rfl
  intro k _
  congr 2
  ring

theorem smoothed_mass_lower (hmps : LittlewoodL1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N P : ℕ) (b : ℕ → ℕ),
    (∀ k ≤ N, b k ≤ 2) → 0 < P → 0 < cosineSum N b 0 →
    δ * log (cosineSum N b 0 / 2) ≤
      ∫ θ in (0 : ℝ)..1, |cosineSum N b θ * windowWeight P θ| := by
  obtain ⟨δ,hδ,H⟩ := integer_fourier_l1_lower hmps
  refine ⟨δ,hδ,?_⟩
  intro N P b hb hP hn
  let f := smoothCoeffs (reflectedCoeffs N b) P
  have hcoeff (n : ℤ) : ‖(f n : ℂ)‖ ≤ 4 * (P : ℝ)^2 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast abs_smoothCoeffs_le (abs_reflectedCoeffs_le_four hb) P n
  have heval : ‖fourierValue f 0‖ = 2 * cosineSum N b 0 * (P : ℝ)^2 := by
    have h := smoothed_norm_at_angle N P b 0
    simp [f, windowWeight, angularCharacter, abs_of_pos hn, Complex.normSq_eq_norm_sq,
      mul_assoc, mul_left_comm] at h ⊢
    exact h
  have h := H f (4 * (P : ℝ)^2) (by positivity) (by rw [heval]; positivity) hcoeff
  rw [heval, show 2 * cosineSum N b 0 * (P : ℝ)^2 / (4 * (P : ℝ)^2) =
      cosineSum N b 0 / 2 by field_simp; ring] at h
  simpa only [f, smoothed_norm_at_angle] using h


theorem structuredRootEstimate_of_littlewood (h : LittlewoodL1) : StructuredRootEstimate := by
  apply structuredRootEstimate_of_smoothed
  obtain ⟨δ,hδ,hlower⟩ := smoothed_mass_lower h
  refine ⟨δ,hδ,?_⟩
  intro N b K P hb _ hmass hK hP hp
  obtain ⟨v,hv0,hvK,_,hper⟩ := hp
  obtain ⟨J,cut,c,hJ,hsize,hcut,hc,he⟩ :=
    periodic_smooth_block_expansion b hb hK hP v hv0 hvK hper
  refine ⟨windowWeight P,J,cut,c,continuous_windowWeight P,windowWeight_nonneg P,hJ,
    hsize,hcut,hc,?_,hlower N P b hb hP (by linarith)⟩
  intro θ
  rw [blockPoly, ← he, cosineSum, windowWeight]
  simp only [mul_assoc, mul_left_comm, mul_comm]

end OMA.G82

namespace OMA.G82

open Polynomial Finset Complex Set Filter
open scoped Topology

/-- The point of the unit circle at angle `t` in radians. -/
noncomputable def unitPhase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem unitPhase_ne_zero (t : ℝ) : unitPhase t ≠ 0 := Complex.exp_ne_zero _
private theorem norm_unitPhase (t : ℝ) : ‖unitPhase t‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

/-- One conjugate pair of roots for each of the translated angles. -/
noncomputable def angleCompanion {d : ℕ} (a : Fin d → ℝ) (ε : ℝ) : Polynomial ℂ :=
  ∏ j, ((X - C (unitPhase (a j + ε))) * (X - C (unitPhase (a j + ε))⁻¹))

theorem angleCompanion_monic {d : ℕ} (a : Fin d → ℝ) (ε : ℝ) : (angleCompanion a ε).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ (monic_X_sub_C _).mul (monic_X_sub_C _)

theorem angleCompanion_degree {d : ℕ} (a : Fin d → ℝ) (ε : ℝ) :
    (angleCompanion a ε).natDegree = 2*d := by
  rw [angleCompanion, natDegree_prod_of_monic _ _ (fun _ _ ↦ (monic_X_sub_C _).mul (monic_X_sub_C _))]
  simp [natDegree_mul, X_sub_C_ne_zero, mul_comm]

theorem angleCompanion_coeff_zero {d : ℕ} (a : Fin d → ℝ) (ε : ℝ) :
    (angleCompanion a ε).coeff 0 = 1 := by
  simp [angleCompanion, coeff_zero_prod, mul_coeff_zero, unitPhase_ne_zero]

theorem angleCompanion_coeff_bound {d : ℕ} (a : Fin d → ℝ) (ε : ℝ) (k : ℕ) :
    ‖(angleCompanion a ε).coeff k‖ ≤ (2 : ℝ)^(2*d) := by
  have hm (s : Finset (Fin d)) :
      (∏ j ∈ s, ((X - C (unitPhase (a j + ε))) * (X - C (unitPhase (a j + ε))⁻¹))).mahlerMeasure = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, mahlerMeasure_mul, ih, mul_one]
      simp [mahlerMeasure_mul, mahlerMeasure_X_sub_C, norm_unitPhase]
  have h := norm_coeff_le_choose_mul_mahlerMeasure k (angleCompanion a ε)
  rw [angleCompanion_degree, show (angleCompanion a ε).mahlerMeasure = 1 from hm univ, mul_one] at h
  exact h.trans (by exact_mod_cast Nat.choose_le_two_pow (2*d) k)

private theorem angle_eq_of_torsion {t : ℝ} {T : ℕ} (hT : 0 < T) (hz : (unitPhase t)^T = 1) :
    ∃ m : ℤ, t = (m : ℝ) * (2 * Real.pi) / T := by
  change Complex.exp ((t : ℂ) * I) ^ T = 1 at hz
  rw [← Complex.exp_nat_mul] at hz
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp hz
  refine ⟨m, (eq_div_iff (by exact_mod_cast hT.ne' : (T : ℝ) ≠ 0)).2 ?_⟩
  have hi := congrArg Complex.im hm
  simp at hi
  linarith

/-- The translates having no torsion roots form a dense set of parameters. -/
theorem dense_companion_avoids_torsion {d : ℕ} (a : Fin d → ℝ) :
    Dense {ε : ℝ | ∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → (angleCompanion a ε).eval z ≠ 0} := by
  let bad : Set ℝ := Set.range fun w : Fin d × ℤ × ℕ ↦
    (w.2.1 : ℝ) * (2 * Real.pi) / w.2.2 - a w.1
  apply ((Set.countable_range _).dense_compl ℝ : Dense badᶜ).mono
  intro ε hε T hT z hz
  have hf (j : Fin d) : unitPhase (a j + ε) ^ T ≠ 1 := by
    intro h
    obtain ⟨m,hm⟩ := angle_eq_of_torsion hT h
    exact hε ⟨⟨j,m,T⟩, by dsimp; linarith⟩
  simp only [angleCompanion, eval_prod, eval_mul, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (fun he ↦ hf j (he ▸ hz))
  · apply sub_ne_zero.mpr
    intro he
    rw [he, inv_pow, inv_eq_one] at hz
    exact hf j hz

/-- A qualifying translate can be chosen in any neighborhood of zero,
including neighborhoods imposed by a strict correlation inequality. -/
theorem exists_companion_perturbation {d : ℕ} (a : Fin d → ℝ) {U : Set ℝ} (hU : U ∈ 𝓝 0) :
    ∃ ε ∈ U, ∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → (angleCompanion a ε).eval z ≠ 0 := by
  have h := (dense_companion_avoids_torsion a) (0 : ℝ)
  exact (mem_closure_iff_nhds.mp h U hU).imp fun ε he ↦ ⟨he.1, he.2⟩

/-- The real-valued central factor obtained by dividing the unit-circle
evaluation by the middle monomial. -/
noncomputable def companionWeight {d : ℕ} (a : Fin d → ℝ) (ε t : ℝ) : ℝ :=
  ∏ j, (2 * (Real.cos t - Real.cos (a j + ε)))

private theorem two_cos_unitPhase (t : ℝ) :
    (2 : ℂ) * (Real.cos t : ℂ) = unitPhase t + (unitPhase t)⁻¹ := by
  simpa only [unitPhase, Complex.ofReal_cos, neg_mul, Complex.exp_neg] using Complex.two_cos (t : ℂ)

theorem angleCompanion_eval_phase {d : ℕ} (a : Fin d → ℝ) (ε t : ℝ) :
    (angleCompanion a ε).eval (unitPhase t) = (unitPhase t)^d * (companionWeight a ε t : ℂ) := by
  have hpair (u : ℝ) :
      (unitPhase t - unitPhase u) * (unitPhase t - (unitPhase u)⁻¹) =
        unitPhase t * ((2 * (Real.cos t - Real.cos u) : ℝ) : ℂ) := by
    calc
      _ = unitPhase t * ((unitPhase t + (unitPhase t)⁻¹) - (unitPhase u + (unitPhase u)⁻¹)) := by
        field_simp [unitPhase_ne_zero]
        ring
      _ = _ := by rw [← two_cos_unitPhase, ← two_cos_unitPhase]; push_cast; ring
  simp only [angleCompanion, eval_prod, eval_mul, eval_sub, eval_X, eval_C]
  simp_rw [hpair]
  rw [Finset.prod_mul_distrib]
  simp [companionWeight]

/-- A strict half-norm correlation survives the small perturbation removing
torsion roots. `w` may include the real cosine polynomial and the centered
square of the differencing multiplier. -/
theorem exists_correlated_companion {d : ℕ} (a : Fin d → ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (u v : ℝ) {U : Set ℝ} (hU : U ∈ 𝓝 0)
    (hpos : 0 < ∫ t in u..v, |w t * companionWeight a 0 t|)
    (hsign : (∫ t in u..v, |w t * companionWeight a 0 t|) ≤
      |∫ t in u..v, w t * companionWeight a 0 t|) :
    ∃ ε ∈ U, (∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → (angleCompanion a ε).eval z ≠ 0) ∧
      (∫ t in u..v, |w t * companionWeight a ε t|) / 2 < |∫ t in u..v, w t * companionWeight a ε t| := by
  let f (ε t : ℝ) := w t * companionWeight a ε t
  have hf : Continuous f.uncurry := by
    change Continuous (fun p : ℝ × ℝ ↦ w p.2 * ∏ j, (2 * (Real.cos p.2 - Real.cos (a j + p.1))))
    fun_prop
  have hL := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hf u v
  have hR := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) (f := fun ε t ↦ |f ε t|) hf.abs u v
  have hstrict : (∫ t in u..v, |f 0 t|) / 2 < |∫ t in u..v, f 0 t| := by
    dsimp [f]; linarith
  have hn := (hR.div_const 2).continuousAt.eventually_lt hL.abs.continuousAt hstrict
  obtain ⟨ε,hε,ht⟩ := exists_companion_perturbation a (inter_mem hU hn)
  exact ⟨ε,hε.1,ht,hε.2⟩

end OMA.G82

namespace OMA.G82

open Polynomial

/-- Every prime-power divisor of an order of totient at most d is at most 2d.
The factorial therefore gives a single period for all those orders. -/
theorem dvd_factorial_of_totient_le {m d : ℕ} (hm : 0 < m) (hd : m.totient ≤ d) :
    m ∣ (2*d).factorial := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hk
  cases k with
  | zero => simp
  | succ k =>
    have hle := (Nat.le_of_dvd (Nat.totient_pos.mpr hm) (Nat.totient_dvd_of_dvd hk)).trans hd
    rw [Nat.totient_prime_pow_succ hp] at hle
    apply Nat.dvd_factorial (pow_pos hp.pos _)
    rw [pow_succ]
    have ha : p ≤ 2*(p-1) := by have := hp.two_le; omega
    nlinarith [Nat.mul_le_mul_left (p^k) ha]

theorem torsion_order_dvd_factorial_of_annihilation {q : Polynomial ℚ} (hq : q ≠ 0)
    {z : ℂ} {T : ℕ} (hT : 0 < T) (hpow : z^T = 1) (hroot : aeval z q = 0) :
    orderOf z ∣ (2*q.natDegree).factorial := by
  have hpos := Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hpow) hT
  apply dvd_factorial_of_totient_le hpos
  have hdiv : minpoly ℚ z ∣ q := minpoly.dvd ℚ z hroot
  rw [← cyclotomic_eq_minpoly_rat (IsPrimitiveRoot.orderOf z) hpos] at hdiv
  simpa [natDegree_cyclotomic] using natDegree_le_of_dvd hdiv hq

/-- A periodic sequence annihilated by a rational polynomial of degree d is
annihilated by the difference with step (2d)!, uniformly in its first period. -/
theorem rational_period_bezout {q : Polynomial ℚ} (hq : q ≠ 0) {T : ℕ} (hT : 0 < T) :
    ∃ U V : Polynomial ℂ, X^(2*q.natDegree).factorial - 1 =
      U * (X^T - 1) + V * q.map (algebraMap ℚ ℂ) := by
  let a : Polynomial ℂ := X^T - 1
  let b := q.map (algebraMap ℚ ℂ)
  let P := (2*q.natDegree).factorial
  let g := IsBezout.gcd a b
  have hga : g ∣ a := IsBezout.gcd_dvd_left _ _
  have hgb : g ∣ b := IsBezout.gcd_dvd_right _ _
  have hsep : a.Separable := X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hT.ne')
  have hgn : g ≠ 0 := by
    intro hg
    have he := hga
    rw [hg, zero_dvd_iff] at he
    exact X_pow_sub_C_ne_zero hT (1 : ℂ) (by simpa [a] using he)
  have hp : (X^P-1 : Polynomial ℂ) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (Nat.factorial_pos _) (1 : ℂ)
  have hgd : g ∣ X^P-1 := by
    apply (IsAlgClosed.dvd_iff_roots_le_roots hgn hp).2
    apply (Multiset.le_iff_subset (nodup_roots (hsep.of_dvd hga))).2
    intro z hz
    have hz' := (mem_roots hgn).mp hz
    have hzt : z^T=1 := by
      simpa [a, IsRoot, sub_eq_zero] using hz'.dvd hga
    have hzq : aeval z q = 0 := by
      simpa [b, IsRoot, eval_map_algebraMap] using hz'.dvd hgb
    have hpz := torsion_order_dvd_factorial_of_annihilation hq hT hzt hzq
    apply (mem_roots hp).mpr
    simpa [IsRoot, sub_eq_zero] using (orderOf_dvd_iff_pow_eq_one.mp hpz)
  obtain ⟨m,hm⟩ := hgd
  obtain ⟨u,v,huv⟩ := IsBezout.gcd_eq_sum a b
  refine ⟨m*u,m*v, ?_⟩
  change X^P-1 = m*u*a + m*v*b
  calc
    X^P-1 = (u*a+v*b)*m := hm.trans (congrArg (· * m) huv.symm)
    _ = _ := by ring

end OMA.G82

namespace OMA.G82

open Matrix Finset

/-- An upper bound for all entries of the integer adjugate. -/
private theorem adjugate_entry_abs_le {m M : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ i j, |A i j| ≤ M) (i j : Fin m) :
    |A.adjugate i j| ≤ (m.factorial : ℤ) * (M+1)^m := by
  rw [Matrix.adjugate_apply]
  have hh := Matrix.det_le (A := A.updateRow j (Pi.single i 1))
    (abv := AbsoluteValue.abs) (x := (M : ℤ)+1) (by
      intro k l
      change |(A.updateRow j (Pi.single i 1)) k l| ≤ _
      by_cases he : k = j
      · subst k
        by_cases hl : l = i
        · simp [hl]
        · simp [Pi.single_eq_of_ne hl]
          omega
      · rw [Matrix.updateRow_ne he]
        linarith [hA k l])
  simpa [nsmul_eq_mul] using hh

/-- Cramer's identity forces the determinant of every candidate square minor to
vanish when all row pairings lie below a uniform factorial threshold. -/
theorem det_eq_zero_of_tiny_pairings {m M : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ i j, |A i j| ≤ M) (q : Fin m → ℂ) (j : Fin m) (hj : 1 ≤ ‖q j‖)
    (htiny : ∀ i, ‖∑ k, (A i k : ℂ) * q k‖ ≤
      1 / (2 * ((m : ℝ)+1) * m.factorial * ((M : ℝ)+1)^m)) : A.det = 0 := by
  classical
  let B : Matrix (Fin m) (Fin m) ℂ := (Int.castRingHom ℂ).mapMatrix A
  let L : ℝ := m.factorial * ((M : ℝ)+1)^m
  have hL : 0 < L := by dsimp [L]; positivity
  have hden : 0 < 2*((m : ℝ)+1)*L := by positivity
  have hcoord : B.det * q j = ∑ i, B.adjugate j i * (B *ᵥ q) i := by
    change _ = (B.adjugate *ᵥ (B *ᵥ q)) j
    simp [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec]
  have hnorm (i : Fin m) : ‖B.adjugate j i‖ ≤ L := by
    have he : B.adjugate j i = ((A.adjugate j i : ℤ) : ℂ) :=
      congrFun (congrFun ((Int.castRingHom ℂ).map_adjugate A).symm j) i
    rw [he]
    simpa [L] using (show |((A.adjugate j i : ℤ) : ℝ)| ≤ _ by
      exact_mod_cast adjugate_entry_abs_le A hA j i)
  have hres (i : Fin m) : ‖(B *ᵥ q) i‖ ≤ 1 / (2*((m : ℝ)+1)*L) := by
    simpa [B, L, Matrix.mulVec, dotProduct, mul_assoc] using htiny i
  have hupper : ‖B.det * q j‖ ≤ (m : ℝ) * (L * (1 / (2*((m : ℝ)+1)*L))) := by
    rw [hcoord]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin m, L * (1 / (2*((m : ℝ)+1)*L)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul (hnorm i) (hres i) (norm_nonneg _) hL.le
      _ = _ := by simp
  by_contra hd
  have hdet : 1 ≤ ‖B.det‖ := by
    have he : B.det = (A.det : ℂ) := ((Int.castRingHom ℂ).map_det A).symm
    rw [he]
    have ha : (1 : ℤ) ≤ |A.det| := abs_pos.mpr hd
    simpa using (show (1 : ℝ) ≤ |(A.det : ℝ)| by exact_mod_cast ha)
  have hlo : 1 ≤ ‖B.det * q j‖ := by rw [norm_mul]; exact one_le_mul_of_one_le_of_one_le hdet hj
  have hbad := hlo.trans hupper
  rw [one_div, ← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ hden] at hbad
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hL.le]

/-- An arbitrary family of integral row vectors with small residuals has an
exact rational annihilator. No cardinality assumption on the family is needed. -/
theorem rational_annihilator_of_tiny_pairings {ι : Type*} {m M : ℕ}
    (v : ι → Fin m → ℤ) (hv : ∀ i j, |v i j| ≤ M)
    (q : Fin m → ℂ) (j : Fin m) (hj : 1 ≤ ‖q j‖)
    (htiny : ∀ i, ‖∑ k, (v i k : ℂ) * q k‖ ≤
      1 / (2 * ((m : ℝ)+1) * m.factorial * ((M : ℝ)+1)^m)) :
    ∃ p : Fin m → ℚ, p ≠ 0 ∧ ∀ i, ∑ k, (v i k : ℚ) * p k = 0 := by
  classical
  let u (i : ι) (k : Fin m) : ℚ := v i k
  let W := Submodule.span ℚ (Set.range u)
  have hW : W ≠ ⊤ := by
    intro hfull
    obtain ⟨κ, f, _, hspan, hlin⟩ := exists_linearIndependent' ℚ u
    let B := Module.Basis.mk hlin (le_of_eq ((hspan.trans hfull).symm))
    have : Finite κ := Module.Finite.finite_basis B
    let _ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = m := by
      simpa using (Module.finrank_eq_card_basis B).symm
    let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    let A : Matrix (Fin m) (Fin m) ℤ := Matrix.of (fun i k ↦ v (f (e i)) k)
    have hz := det_eq_zero_of_tiny_pairings A (fun i k ↦ hv _ k) q j hj (fun i ↦ htiny _)
    let A' : Matrix (Fin m) (Fin m) ℚ := (Int.castRingHom ℚ).mapMatrix A
    have hh : LinearIndependent ℚ A'.row := hlin.comp e e.injective
    have hunit := (Matrix.isUnit_iff_isUnit_det A').mp (Matrix.linearIndependent_rows_iff_isUnit.mp hh)
    have hzero : A'.det = 0 := by
      rw [show A'.det = (A.det : ℚ) from ((Int.castRingHom ℚ).map_det A).symm, hz, Int.cast_zero]
    exact hunit.ne_zero hzero
  have hdual : W.dualAnnihilator ≠ ⊥ := fun h ↦ hW (Submodule.dualAnnihilator_eq_bot_iff.mp h)
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdual
  let p (k : Fin m) : ℚ := φ (Pi.single k 1)
  have hact (x : Fin m → ℚ) : φ x = ∑ k, x k * p k := by
    conv_lhs => rw [← (Pi.basisFun ℚ (Fin m)).sum_repr x]
    simp [p, Pi.basisFun_apply]
  refine ⟨p, ?_, fun i ↦ ?_⟩
  · intro hp
    apply hne
    ext x
    simp [hact, hp]
  · change ∑ k, u i k * p k = 0
    rw [← hact]
    exact (W.mem_dualAnnihilator φ).mp hφ _ (Submodule.subset_span (Set.mem_range_self i))

end OMA.G82

namespace OMA.G82

open Polynomial Matrix Finset
/-- A forward recurrence can have zero constant coefficient. After the first
collision of two windows its suffix agrees with a globally periodic sequence. -/
private theorem periodic_suffix_of_recurrence {S : Finset ℂ} {x c : ℕ → ℂ} {D L : ℕ}
    (hx : ∀ n < L, x n ∈ S) (hlen : S.card ^ D + D ≤ L) (hcD : c D ≠ 0)
    (hrec : ∀ u, u + D < L → WindowRelation x c D u) :
    ∃ (i T : ℕ) (z : ℕ → ℂ), i + T ≤ S.card ^ D ∧ 0 < T ∧ Function.Periodic z T ∧
      (∀ n, i + n < L → z n = x (i+n)) ∧ ∀ u, WindowRelation z c D u := by
  obtain ⟨i,T,hT,hi,hcollision⟩ := repeated_window hx hlen
  let seg (n : ℕ) := x (i+n)
  have hperiod (n : ℕ) : i+n+T < L → seg n = seg (n+T) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : n < D
      · simpa only [seg, Nat.add_assoc, Nat.add_comm T n] using hcollision n hsmall
      · let u := n-D
        have he := window_forward hcD (hrec (i+u) (by dsimp [u]; omega))
          (hrec (i+u+T) (by dsimp [u]; omega)) (fun k hk ↦ by
            have hh := ih (u+k) (by dsimp [u]; omega) (by dsimp [u]; omega)
            simpa only [seg, Nat.add_assoc, Nat.add_comm T k] using hh)
        dsimp [seg]
        convert he using 2 <;> dsimp [u] <;> omega
  let z (n : ℕ) := seg (n % T)
  have hagree (n : ℕ) : i + n < L → z n = seg n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : n < T
      · simp [z, Nat.mod_eq_of_lt hsmall]
      · have hn' : n - T + T = n := by omega
        calc
          z n = z (n-T) := by
            dsimp [z]
            conv_lhs => rw [← hn']
            simp
          _ = seg (n-T) := ih _ (by omega) (by omega)
          _ = seg n := by simpa only [hn'] using hperiod (n-T) (by omega)
  refine ⟨i,T,z,hi,hT, fun n ↦ by simp [z], hagree, ?_⟩
  intro u
  have hr := Nat.mod_lt u hT
  have hlocal := hrec (i + u%T) (by omega)
  unfold WindowRelation at hlocal ⊢
  refine (Finset.sum_congr rfl (fun k hk ↦ ?_)).trans hlocal
  have hk' := Finset.mem_range.mp hk
  have hy : z (u+k) = z (u%T+k) := by simp [z, Nat.mod_add_mod]
  rw [hy, hagree _ (by omega)]
  dsimp [seg]
  rw [Nat.add_assoc]

/-- Second difference taken with step `P`. -/
def stepDifference (x : ℕ → ℤ) (P n : ℕ) : ℤ :=
  x (n + 2*P) - 2*x (n+P) + x n

/-- Residual of a window of second differences against the monic multiplier. -/
noncomputable def tinyRunValue {m : ℕ} (x : ℕ → ℤ) (P : ℕ) (h : Fin m → ℂ) (u : ℕ) : ℂ :=
  ∑ k : Fin m, (stepDifference x P (u+k) : ℂ) * h k

private theorem constant_stepDifference_vanish (x : ℕ → ℤ) (hx : ∀ n, |x n| ≤ 4) (P n : ℕ)
    (h : ∀ j : Fin 9, stepDifference x P (n + j.val*P) = stepDifference x P n) :
    stepDifference x P n = 0 := by
  let v (j : ℕ) := x (n+j*P)
  let d := stepDifference x P n
  have eqn (j : Fin 9) : v (j.val+2) - 2*v (j.val+1) + v j.val = d := by
    simpa [v, d, stepDifference, Nat.add_mul, Nat.add_assoc] using h j
  have hd : v 10 - 2*v 5 + v 0 = 25*d := by
    have allEq (j : ℕ) (hj : j < 9) : v (j+2) - 2*v (j+1) + v j = d := eqn ⟨j,hj⟩
    linarith only [allEq 0 (by decide), allEq 1 (by decide), allEq 2 (by decide),
      allEq 3 (by decide), allEq 4 (by decide), allEq 5 (by decide), allEq 6 (by decide),
      allEq 7 (by decide), allEq 8 (by decide)]
  have h0 := abs_le.mp (hx (n + 0*P))
  have h5 := abs_le.mp (hx (n + 5*P))
  have h10 := abs_le.mp (hx (n + 10*P))
  change d = 0
  dsimp [v] at hd
  omega

/-- On a stretch of uniformly tiny residuals, every residual sufficiently far
from both ends vanishes exactly. -/
theorem tiny_run_vanish {m L : ℕ} (hm : 0 < m)
    (x : ℕ → ℤ) (hx : ∀ n, |x n| ≤ 4) (h : Fin m → ℂ) (j : Fin m) (hj : 1 ≤ ‖h j‖)
    (hsmall : ∀ u < L, ‖tinyRunValue x (2*m).factorial h u‖ ≤
      1 / (2 * ((m : ℝ)+1) * m.factorial * (17 : ℝ)^m))
    {u : ℕ} (hleft : 33^m + m ≤ u) (hright : u + m + 10*(2*m).factorial < L) :
    tinyRunValue x (2*m).factorial h u = 0 := by
  classical
  let P := (2*m).factorial
  let y := stepDifference x P
  have hb (n : ℕ) : |y n| ≤ 16 := by
    have h1 := abs_le.mp (hx n)
    have h2 := abs_le.mp (hx (n+P))
    have h3 := abs_le.mp (hx (n+2*P))
    dsimp [y, stepDifference]
    exact abs_le.mpr ⟨by omega, by omega⟩
  obtain ⟨p,hp,hann⟩ := rational_annihilator_of_tiny_pairings
    (fun r : Fin L ↦ fun k : Fin m ↦ y (r.val+k)) (M := 16) (fun r k ↦ hb _)
    h j hj (fun r ↦ by
      have hs := hsmall r.val r.isLt
      norm_num [tinyRunValue, y, P] at hs ⊢
      exact hs)
  let q := Polynomial.ofFn m p
  let Q := q.map (algebraMap ℚ ℂ)
  have hqn : q ≠ 0 := by
    change Polynomial.ofFn m p ≠ 0
    rw [← map_zero (Polynomial.ofFn (R := ℚ) m)]
    exact fun he ↦ hp (Polynomial.injective_ofFn m he)
  let D := q.natDegree
  have hd : D < m := ofFn_natDegree_lt hm p
  have hdeg : Q.natDegree = D := natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective _
  have hlead : Q.coeff D ≠ 0 := by
    simpa [Q, D, coeff_map] using (show q.leadingCoeff ≠ 0 from leadingCoeff_ne_zero.mpr hqn)
  have hrec (r : ℕ) (hr : r+D < L) : WindowRelation (fun n ↦ (y n : ℂ)) Q.coeff D r := by
    let f (k : ℕ) : ℂ := Q.coeff k * (y (r+k) : ℂ)
    have hsame : (∑ k ∈ Finset.range (D+1), f k) = ∑ k ∈ Finset.range m, f k :=
      Finset.sum_subset (Finset.range_mono (by omega)) (fun k _ hk ↦ by
        have hlt : Q.natDegree < k := by rw [hdeg]; simp at hk; omega
        simp [f, coeff_eq_zero_of_natDegree_lt hlt])
    unfold WindowRelation
    change (∑ k ∈ Finset.range (D+1), f k) = 0
    rw [hsame, ← Fin.sum_univ_eq_sum_range]
    have hrat := hann ⟨r,by omega⟩
    have he := congrArg (algebraMap ℚ ℂ) hrat
    simpa [f,Q,q,coeff_map,Polynomial.ofFn_coeff_eq_val_of_lt, mul_comm] using he
  let S : Finset ℂ := (Finset.Icc (-16:ℤ) 16).image fun z : ℤ ↦ (z : ℂ)
  have hS (n : ℕ) : (y n : ℂ) ∈ S := Finset.mem_image.mpr
    ⟨y n, Finset.mem_Icc.mpr (abs_le.mp (hb n)), rfl⟩
  have hcard : S.card ≤ 33 := by
    exact Finset.card_image_le.trans (by decide)
  have hsD : S.card^D ≤ 33^m := by
    exact (Nat.pow_le_pow_left hcard D).trans (Nat.pow_le_pow_right (by decide) hd.le)
  obtain ⟨i,T,z,hsize,hT,hperiod,hmatches,hrel⟩ :=
    periodic_suffix_of_recurrence (S := S) (fun n _ ↦ hS n) (by omega) hlead hrec
  obtain ⟨U,V,hbez⟩ := rational_period_bezout hqn hT
  have hperD := periodic_of_window_bezout hperiod (le_of_eq hdeg) hrel hbez
  have hdvd : (2*D).factorial ∣ P := Nat.factorial_dvd_factorial (by omega)
  have hperP : Function.Periodic z P := by
    obtain ⟨r,hr⟩ := hdvd
    rw [hr, Nat.mul_comm]
    exact hperD.nat_mul r
  unfold tinyRunValue
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  have hzero : y (u+k) = 0 := by
    apply constant_stepDifference_vanish x hx P
    intro e
    have he := e.isLt
    have hbound : i + (u+k-i) + e.val*P < L := by
      have := Nat.mul_le_mul_right P (show e.val ≤ 10 by omega)
      dsimp [P] at *
      omega
    have hmatch0 := hmatches (u+k-i) (by omega)
    have hmatch1 := hmatches ((u+k-i) + e.val*P) (by omega)
    have heq : z ((u+k-i) + e.val*P) = z (u+k-i) := by
      simpa only [Nat.cast_id] using (hperP.nat_mul e.val) (u+k-i)
    rw [hmatch0, hmatch1] at heq
    have hidx : i + (u+k-i) = u+k := by omega
    rw [← Nat.add_assoc, hidx] at heq
    exact_mod_cast heq
  change (y (u+k) : ℂ)*h k = 0
  simp [hzero]

/-- Count the two boundary strips of a tiny stretch. -/
theorem tiny_run_nonzero_card_le {m L : ℕ} (hm : 0 < m)
    (x : ℕ → ℤ) (hx : ∀ n, |x n| ≤ 4) (h : Fin m → ℂ) (j : Fin m) (hj : 1 ≤ ‖h j‖)
    (hsmall : ∀ u < L, ‖tinyRunValue x (2*m).factorial h u‖ ≤
      1 / (2 * ((m : ℝ)+1) * m.factorial * (17 : ℝ)^m)) :
    ((Finset.range L).filter (fun u ↦ tinyRunValue x (2*m).factorial h u ≠ 0)).card ≤
      33^m + 2*m + 10*(2*m).factorial := by
  classical
  let a := 33^m + m
  let b := m + 10*(2*m).factorial
  have hs : ((Finset.range L).filter (fun u ↦ tinyRunValue x (2*m).factorial h u ≠ 0))
      ⊆ Finset.range a ∪ Finset.Ico (L-b) L := by
    intro u hu
    obtain ⟨hr,hne⟩ := Finset.mem_filter.mp hu
    have huL := Finset.mem_range.mp hr
    by_cases hl : u < a
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hl)
    · apply Finset.mem_union_right
      apply Finset.mem_Ico.mpr
      refine ⟨?_,huL⟩
      by_contra! hmid
      exact hne (tiny_run_vanish hm x hx h j hj hsmall (by dsimp [a] at hl; omega)
        (by dsimp [b] at hmid; omega))
  refine (Finset.card_le_card hs).trans ((Finset.card_union_le ..).trans ?_)
  simp only [Finset.card_range, Nat.card_Ico]
  dsimp [a,b]
  omega

end OMA.G82

namespace OMA.G82

open Finset Real

/-- The underlying scales are ranks in the support, not the frequency gaps. -/
theorem log_support_le_of_weighted_ranks {k L : ℕ} (hL : 0 < L)
    (a : Fin k → ℂ) {δ C B : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hw : C * (∑ i : Fin k, ‖a i‖ / ((i.val : ℝ) + 1)) ≤ B)
    (hblocks : ∀ j : Fin (k / L), ∃ i : Fin k, i.val / L = j.val ∧ δ ≤ ‖a i‖) :
    log ((k : ℝ) + 1) ≤ log (L : ℝ) + (L : ℝ) * B / (C * δ) := by
  classical
  choose f hq hbig using hblocks
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  let e : Fin (k / L) ↪ Fin k := ⟨f, fun j j' he ↦ Fin.ext (by rw [← hq j, he, hq j'])⟩
  let w (i : Fin k) := ‖a i‖ / ((i.val : ℝ) + 1)
  have hw0 (i : Fin k) : 0 ≤ w i := by dsimp [w]; positivity
  have hbound (j : Fin (k / L)) : δ / ((L : ℝ) * (j.val + 1)) ≤ w (e j) := by
    have hidx := Nat.lt_mul_div_succ (f j).val hL
    rw [hq] at hidx
    have hreal : ((f j).val : ℝ) + 1 ≤ (L : ℝ) * (j.val+1) := by exact_mod_cast hidx
    apply (div_le_div_of_nonneg_left hδ.le (by positivity) hreal).trans
    exact div_le_div_of_nonneg_right (hbig j) (by positivity)
  have harm : (harmonic (k / L) : ℝ) =
      ∑ j : Fin (k / L), 1 / ((j.val : ℝ) + 1) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_succ, Rat.cast_add, Rat.cast_one,
      Rat.cast_natCast, one_div]
    rw [← Fin.sum_univ_eq_sum_range]
  have hsum : δ / (L : ℝ) * log ((k / L : ℕ) + 1 : ℝ) ≤ ∑ i, w i := by
    calc
      _ ≤ δ / (L : ℝ) * (harmonic (k / L) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast log_add_one_le_harmonic (k/L)) (by positivity)
      _ = ∑ j : Fin (k / L), δ / ((L : ℝ) * (j.val + 1)) := by
        rw [harm, mul_sum]
        exact sum_congr rfl fun j _ ↦ by rw [div_mul_div_comm, mul_one]
      _ ≤ ∑ j : Fin (k/L), w (e j) := sum_le_sum fun j _ ↦ hbound j
      _ = ∑ i ∈ univ.map e, w i := (sum_map _ _ _).symm
      _ ≤ ∑ i, w i := sum_le_univ_sum_of_nonneg hw0
  have hquot : log ((k / L : ℕ) + 1 : ℝ) ≤ (L : ℝ) * B / (C * δ) := by
    apply (le_div_iff₀ (mul_pos hC hδ)).2
    have hh := (mul_le_mul_of_nonneg_left hsum hC.le).trans hw
    have hh' := mul_le_mul_of_nonneg_left hh hL'.le
    convert hh' using 1
    field_simp
  have hlog : log ((k : ℝ) + 1) ≤ log ((L : ℝ) * ((k/L : ℕ) + 1 : ℝ)) :=
    log_le_log (by positivity) (by exact_mod_cast Nat.lt_mul_div_succ k hL)
  rw [log_mul hL'.ne' (by positivity)] at hlog
  linarith

/-- Apply the rank estimate to the increasing support of a complex trigonometric
polynomial. The kernel is left as a parameter so the normalization of the
exponential agrees with the supplied Littlewood inequality. -/
theorem log_complex_support_le_of_littlewood
    (E : ℤ → ℝ → ℂ) {C : ℝ} (hC : 0 < C)
    (hL1 : ∀ (k : ℕ) (ν : Fin k ↪o ℤ) (a : Fin k → ℂ),
      C * (∑ j, ‖a j‖ / ((j.val : ℝ) + 1)) ≤
        ∫ t in (0 : ℝ)..1, ‖∑ j, a j * E (ν j) t‖)
    (f : ℤ →₀ ℂ) {L : ℕ} (hL : 0 < L) {B δ : ℝ} (hδ : 0 < δ)
    (hupper : (∫ t in (0 : ℝ)..1, ‖f.sum (fun n z ↦ z * E n t)‖) ≤ B)
    (hblocks : ∀ j : Fin (f.support.card / L), ∃ i : Fin f.support.card,
      i.val / L = j.val ∧ δ ≤ ‖f (f.support.orderEmbOfFin rfl i)‖) :
    log ((f.support.card : ℝ) + 1) ≤ log (L : ℝ) + (L : ℝ)*B/(C*δ) := by
  classical
  let ν := f.support.orderEmbOfFin rfl
  have he (t : ℝ) : f.sum (fun n z ↦ z * E n t) =
      ∑ i : Fin f.support.card, f (ν i) * E (ν i) t := by
    unfold Finsupp.sum
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ f.support rfl]
    rw [sum_map]
    rfl
  simp_rw [he] at hupper
  exact log_support_le_of_weighted_ranks hL (fun i ↦ f (ν i)) hδ hC
    ((hL1 _ ν _).trans hupper) hblocks

end OMA.G82

namespace OMA.G82

open Polynomial Finset

theorem norm_palindromicLift_coeff_le {b : ℕ → ℕ} {N : ℕ}
    (hb : ∀ k ≤ N, b k ≤ 2) (m : ℕ) : ‖(palindromicLift N b).coeff m‖ ≤ 4 := by
  let s := range (N+1)
  have hpart {h : ℕ → ℕ} (he : Set.InjOn h (s : Set ℕ)) :
      ‖∑ i ∈ s, (if h i = m then (b i : ℂ) else 0)‖ ≤ 2 := by
    by_cases hx : ∃ i ∈ s, h i = m
    · obtain ⟨i,hi,hm⟩ := hx
      rw [sum_eq_single_of_mem i hi (fun j hj hji ↦ if_neg fun h ↦
        hji (he hj hi (h.trans hm.symm))), if_pos hm]
      simpa using (show (b i : ℝ) ≤ 2 by
        exact_mod_cast hb i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
    · rw [sum_eq_zero (fun i hi ↦ if_neg fun h ↦ hx ⟨i,hi,h⟩)]
      norm_num
  simp only [palindromicLift, finsetSum_coeff, coeff_add, coeff_monomial, sum_add_distrib]
  apply (norm_add_le _ _).trans
  have hl : Set.InjOn (fun i : ℕ ↦ N-i) s := by
    intro i hi j hj h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    dsimp at h
    omega
  have hr : Set.InjOn (fun i : ℕ ↦ N+i) s := by
    intro i _ j _ h
    exact Nat.add_left_cancel h
  linarith [hpart hl, hpart hr]

private theorem norm_coeff_difference_le {p : Polynomial ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ j, ‖p.coeff j‖ ≤ B) (P m : ℕ) :
    ‖((X^P-1)*p).coeff m‖ ≤ 2 * B := by
  rw [sub_mul, one_mul, coeff_sub]
  apply (norm_sub_le _ _).trans
  have h : ‖(X^P*p).coeff m‖ ≤ B := by
    by_cases hPm : P ≤ m
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hPm
      rw [mul_comm (X^P) p, Nat.add_comm P k, coeff_mul_X_pow]
      exact hp _
    · rw [mul_comm (X^P) p, coeff_mul_X_pow']
      simp [hPm, hB]
  linarith [hp m]

/-- The coefficient selected by the companion correlation is bounded
independently of P and N. -/
theorem lift_multiplier_coeff_bound {N : ℕ} {b : ℕ → ℕ} (hb : ∀ k ≤ N, b k ≤ 2)
    (Q : Polynomial ℂ) {A : ℝ} (hA : 0 ≤ A) (hQ : ∀ j, ‖Q.coeff j‖ ≤ A)
    (P m : ℕ) : ‖((Q*(X^P-1)^2)*palindromicLift N b).coeff m‖ ≤
      16 * ((Q.natDegree : ℝ) + 1) * A := by
  let p := (X^P-1)*((X^P-1)*palindromicLift N b)
  have hp (j : ℕ) : ‖p.coeff j‖ ≤ 16 := by
    convert norm_coeff_difference_le (by norm_num : (0 : ℝ) ≤ 2*4)
      (norm_coeff_difference_le (by norm_num) (norm_palindromicLift_coeff_le hb) P) P j using 1; norm_num
  rw [sq, mul_assoc, mul_assoc]
  change ‖(Q*p).coeff m‖ ≤ _
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  let s := (range (m+1)).filter (fun i ↦ i ≤ Q.natDegree)
  have hs : s ⊆ range (Q.natDegree+1) := fun i hi ↦
    mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2)
  have hcount : s.card ≤ Q.natDegree + 1 := by simpa using card_le_card hs
  have hr : (∑ k ∈ s, Q.coeff k * p.coeff (m-k)) =
      ∑ k ∈ range (m+1), Q.coeff k * p.coeff (m-k) := by
    apply sum_subset (filter_subset ..)
    intro i hi h
    have hdeg : Q.natDegree < i := by
      by_contra! hle
      exact h (mem_filter.mpr ⟨hi,hle⟩)
    simp [coeff_eq_zero_of_natDegree_lt hdeg]
  rw [← hr]
  calc
    _ ≤ ∑ k ∈ s, ‖Q.coeff k * p.coeff (m-k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ s, A * 16 := by
      apply sum_le_sum
      intro k _
      rw [norm_mul]
      gcongr <;> [exact hQ k; exact hp _]
    _ = (s.card : ℝ) * (A * 16) := by simp
    _ ≤ ((Q.natDegree : ℝ)+1) * (A*16) := by gcongr; exact_mod_cast hcount
    _ = _ := by ring

end OMA.G82

namespace OMA.G82

open Polynomial Finset

noncomputable def integerLift (N : ℕ) (b : ℕ → ℕ) : Polynomial ℤ :=
  ∑ i ∈ range (N+1), (monomial (N-i) (b i : ℤ) + monomial (N+i) (b i : ℤ))

theorem integerLift_map (N : ℕ) (b : ℕ → ℕ) :
    (integerLift N b).map (Int.castRingHom ℂ) = palindromicLift N b := by
  simp [integerLift, palindromicLift, Polynomial.map_sum]

theorem delayed_lift_bounded {N : ℕ} {b : ℕ → ℕ} (hb : ∀ k ≤ N, b k ≤ 2) (v n : ℕ) :
    |((X^v) * integerLift N b).coeff n| ≤ 4 := by
  rw [coeff_X_pow_mul']
  split
  · have h := norm_palindromicLift_coeff_le hb (n-v)
    rw [← integerLift_map, coeff_map, Int.coe_castRingHom, Complex.norm_intCast, ← Int.cast_abs] at h
    exact_mod_cast h
  · norm_num

private theorem second_difference_coeff {R : Type*} [CommRing R] (p : Polynomial R) (P k : ℕ) :
    ((X^P-1)^2*p).coeff (k+2*P) =
      p.coeff (k+2*P)-2*p.coeff (k+P)+p.coeff k := by
  have he : (X^P-1)^2*p = (X^(P+P)*p - (X^P*p + X^P*p)) + p := by
    rw [pow_add]
    ring
  rw [he, coeff_add, coeff_sub, coeff_add, show k+2*P=k+(P+P) by omega, coeff_X_pow_mul,
    show k+(P+P)=k+P+P by omega, coeff_X_pow_mul]
  ring

/-- A single zero-padded integer sequence realizes *all* coefficients of the
product as short moving pairings, including those at the boundary. -/
theorem product_coefficient_window (G : Polynomial ℤ) (Q : Polynomial ℂ) {D : ℕ}
    (hD : Q.natDegree ≤ D) (P u : ℕ) :
    ((Q*(X^P-1)^2) * G.map (Int.castRingHom ℂ)).coeff u =
      let x := ((X^(D+2*P))*G).coeff
      ∑ j : Fin (D+1),
        ((x (u+j+2*P)-2*x (u+j+P)+x (u+j) : ℤ) : ℂ) * Q.coeff (D-j) := by
  let A : Polynomial ℤ := X^(D+2*P)*G
  let B : Polynomial ℂ := A.map (Int.castRingHom ℂ)
  let H := (X^P-1)^2*B
  have hshift :
      (X^(D+2*P))*((Q*(X^P-1)^2)*G.map (Int.castRingHom ℂ)) = Q*H := by
    dsimp [H,B,A]
    rw [Polynomial.map_mul, Polynomial.map_pow, map_X]
    ring
  rw [← coeff_X_pow_mul ((Q*(X^P-1)^2)*G.map (Int.castRingHom ℂ)) (D+2*P) u, hshift,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have htr : ∑ k ∈ range (D+1), Q.coeff k * H.coeff (u+(D+2*P)-k) =
      ∑ k ∈ range ((u+(D+2*P))+1), Q.coeff k * H.coeff (u+(D+2*P)-k) := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k _ h
    have hlt : D < k := by simpa using h
    simp [coeff_eq_zero_of_natDegree_lt (hlt.trans_le' hD)]
  rw [← htr, ← sum_range_reflect _ (D+1)]
  let f (k : ℕ) := (Q.coeff (D-k) * H.coeff (u+(D+2*P)-(D-k)))
  change (∑ k ∈ range (D+1), f k) = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  dsimp [f]
  rw [show u+(D+2*P)-(D-j) = (u+j)+2*P by have := j.isLt; omega,
    show H = (X^P-1)^2*B by rfl, second_difference_coeff]
  change Q.coeff (D-j) * _ = ((A.coeff (u+j+2*P) - 2*A.coeff (u+j+P) + A.coeff (u+j) : ℤ) : ℂ) * _
  simp only [B, coeff_map, Int.coe_castRingHom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

/-- A run of ordered occupied frequencies must have a large coefficient if
vanishing on the middle of every interval of tiny coefficients is known. -/
theorem rank_blocks_of_vanishing {p : Polynomial ℂ} {A B : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ a n, (∀ j < n, ‖p.coeff (a+j)‖ ≤ δ) →
      ∀ u, A ≤ u → u+B < n → p.coeff (a+u) = 0) :
    let L := A+B+1
    ∀ j : Fin (p.support.card / L), ∃ i : Fin p.support.card, i.val / L = j.val ∧
      δ ≤ ‖p.coeff (p.support.orderEmbOfFin rfl i)‖ := by
  let S := p.support
  let L := A+B+1
  change ∀ j : Fin (S.card / L), _
  intro j
  have hL : 0 < L := by dsimp [L]; omega
  have hfits := (Nat.le_div_iff_mul_le hL).mp (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at hfits
  have hlval : L = A+B+1 := rfl
  let lo : Fin S.card := ⟨j.val*L, by omega⟩
  let mid : Fin S.card := ⟨j.val*L+A, by omega⟩
  let hi : Fin S.card := ⟨j.val*L+A+B, by omega⟩
  let ν := S.orderEmbOfFin rfl
  have gap {i k : Fin S.card} (hle : i ≤ k) : k.val-i.val ≤ ν k - ν i := by
    obtain ⟨v,hvid⟩ := Nat.exists_eq_add_of_le (show i.val ≤ k.val from hle)
    have hh : ∀ w, ∀ hw : i.val + w < S.card, ν i + w ≤ ν ⟨i.val+w,hw⟩ := by
      intro w
      induction w with
      | zero => intro hw; simp
      | succ w ih =>
        intro hw
        have hw' : i.val+w < S.card := by omega
        have hl := ν.strictMono (show (⟨i.val+w,hw'⟩ : Fin S.card) < ⟨i.val+(w+1),hw⟩ by
          change i.val+w < i.val+(w+1); omega)
        have := ih hw'
        omega
    have h := hh v (by rw [← hvid]; exact k.isLt)
    have he : (⟨i.val+v,by omega⟩ : Fin S.card) = k := Fin.ext hvid.symm
    rw [he] at h
    omega
  have hlo : ν lo ≤ ν mid := ν.monotone (show lo.val ≤ mid.val by dsimp [lo,mid]; omega)
  have hhi : ν mid ≤ ν hi := ν.monotone (show mid.val ≤ hi.val by dsimp [mid,hi]; omega)
  have h₁ := gap (i := lo) (k := mid) (by change lo.val ≤ mid.val; dsimp [lo,mid]; omega)
  have h₂ := gap (i := mid) (k := hi) (by change mid.val ≤ hi.val; dsimp [mid,hi]; omega)
  have hleft : A ≤ ν mid - ν lo := by simpa [mid,lo] using h₁
  have hright : B ≤ ν hi - ν mid := by simpa [hi,mid] using h₂
  by_contra! hn
  have hsmall : ∀ t < ν hi - ν lo + 1, ‖p.coeff (ν lo+t)‖ ≤ δ := by
    intro t ht
    by_cases hm : ν lo+t ∈ S
    · obtain ⟨i,hi'⟩ := (show ν lo+t ∈ Set.range ν by simpa [ν] using hm)
      have hlrk : lo ≤ i := ν.le_iff_le.mp (by omega)
      have hhrk : i ≤ hi := ν.le_iff_le.mp (by omega)
      have hdiv : i.val / L = j.val := by
        apply Nat.div_eq_of_lt_le
        · exact hlrk
        · change i.val ≤ j.val*L+A+B at hhrk
          rw [Nat.add_mul, one_mul]
          omega
      exact hi' ▸ (hn i hdiv).le
    · have hzero : p.coeff (ν lo+t) = 0 := notMem_support_iff.mp hm
      simp [hzero,hδ.le]
  have h := hlocal (ν lo) _ hsmall (ν mid-ν lo) hleft (by omega)
  rw [Nat.add_sub_of_le hlo] at h
  exact mem_support_iff.mp (S.orderEmbOfFin_mem rfl mid) h

end OMA.G82

namespace OMA.G82

open Polynomial Finset Complex Set Filter
open scoped Topology
open Finset Filter Set Real
open scoped Topology

/-- A weak sign is sufficient at isolated zeros and interval endpoints. -/
def OneSign (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  (∀ x ∈ S, 0 ≤ f x) ∨ (∀ x ∈ S, f x ≤ 0)

private theorem oneSign_no_zero {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hz : ∀ x ∈ Ioo a b, f x ≠ 0) : OneSign f (Icc a b) := by
  classical
  by_cases hp : ∀ x ∈ Icc a b, 0 ≤ f x
  · exact Or.inl hp
  push Not at hp
  obtain ⟨l,hl,hfl⟩ := hp
  right
  intro r hr
  by_contra! hfr
  rcases le_total l r with hlr | hrl
  · obtain ⟨u,hu,he⟩ := intermediate_value_Ioo hlr hf.continuousOn ⟨hfl,hfr⟩
    exact hz _ ⟨hl.1.trans_lt hu.1, hu.2.trans_le hr.2⟩ he
  · obtain ⟨u,hu,he⟩ := intermediate_value_Ioo' hrl hf.continuousOn ⟨hfl,hfr⟩
    exact hz _ ⟨hr.1.trans_lt hu.1, hu.2.trans_le hl.2⟩ he

private theorem oneSign_across {f κ : ℝ → ℝ} {a r b : ℝ} (hr : r ∈ Icc a b)
    (hκ : AntitoneOn κ (Icc a b)) (hl : OneSign f (Icc a r)) (hh : OneSign f (Icc r b)) :
    OneSign f (Icc a b) ∨ OneSign (fun x ↦ f x * (κ x - κ r)) (Icc a b) := by
  have hsplit (p : ℝ → Prop) (h₁ : ∀ x ∈ Icc a r, p x) (h₂ : ∀ x ∈ Icc r b, p x) :
      ∀ x ∈ Icc a b, p x := by
    intro x hx
    rcases le_total x r with h | h
    · exact h₁ _ ⟨hx.1,h⟩
    · exact h₂ _ ⟨h,hx.2⟩
  have hlκ (x : ℝ) (hx : x ∈ Icc a r) : 0 ≤ κ x - κ r :=
    sub_nonneg.mpr (hκ ⟨hx.1,hx.2.trans hr.2⟩ hr hx.2)
  have hrκ (x : ℝ) (hx : x ∈ Icc r b) : κ x - κ r ≤ 0 :=
    sub_nonpos.mpr (hκ hr ⟨hr.1.trans hx.1,hx.2⟩ hx.1)
  rcases hl with hp | hn <;> rcases hh with hp' | hn'
  · exact Or.inl (Or.inl (hsplit _ hp hp'))
  · exact Or.inr (Or.inl (hsplit _ (fun x hx ↦ mul_nonneg (hp x hx) (hlκ x hx))
        (fun x hx ↦ mul_nonneg_of_nonpos_of_nonpos (hn' x hx) (hrκ x hx))))
  · exact Or.inr (Or.inr (hsplit _ (fun x hx ↦ mul_nonpos_of_nonpos_of_nonneg (hn x hx) (hlκ x hx))
        (fun x hx ↦ mul_nonpos_of_nonneg_of_nonpos (hp' x hx) (hrκ x hx))))
  · exact Or.inl (Or.inr (hsplit _ hn hn'))

/-- On a segment where `κ` decreases strictly, one may select interior zeros
whose linear factors in `κ` make a continuous function have a single sign. -/
theorem select_sign_factors (f κ : ℝ → ℝ) (hf : Continuous f) (hκc : Continuous κ)
    (s : Finset ℝ) {a b : ℝ} (hκ : StrictAntiOn κ (Icc a b))
    (hs : ∀ r ∈ s, r ∈ Ioo a b) (hz : ∀ x ∈ Ioo a b, f x = 0 → x ∈ s) :
    ∃ R ⊆ s, OneSign (fun x ↦ f x * ∏ r ∈ R, (κ x - κ r)) (Icc a b) := by
  classical
  induction s using Finset.induction_on_max generalizing b with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    simpa using (oneSign_no_zero hf (fun x hx he ↦ Finset.notMem_empty x (hz x hx he)))
  | insert r s hmax ih =>
    have hr := hs r (Finset.mem_insert_self _ _)
    have hs' : ∀ t ∈ s, t ∈ Ioo a r := fun t ht ↦
      ⟨(hs t (Finset.mem_insert_of_mem ht)).1,hmax t ht⟩
    have hsub : Icc a r ⊆ Icc a b := Icc_subset_Icc_right hr.2.le
    have hz' : ∀ x ∈ Ioo a r, f x = 0 → x ∈ s := by
      intro x hx he
      exact (Finset.mem_insert.mp (hz x ⟨hx.1,hx.2.trans hr.2⟩ he)).resolve_left hx.2.ne
    obtain ⟨R,hR,hleft⟩ := ih (hκ.mono hsub) hs' hz'
    let g (x : ℝ) := f x * ∏ t ∈ R, (κ x - κ t)
    have hg : Continuous g := by dsimp [g]; fun_prop
    have hright : OneSign g (Icc r b) := by
      apply oneSign_no_zero hg
      intro x hx
      have hfx : f x ≠ 0 := by
        intro he
        rcases Finset.mem_insert.mp (hz x ⟨hr.1.trans hx.1,hx.2⟩ he) with h | h
        · exact hx.1.ne' h
        · exact (hmax x h).asymm hx.1
      apply mul_ne_zero hfx
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      have htr := hs' t (hR ht)
      apply sub_ne_zero.mpr
      exact (hκ (hsub ⟨htr.1.le,htr.2.le⟩) ⟨(hr.1.trans hx.1).le,hx.2.le⟩ (htr.2.trans hx.1)).ne
    rcases oneSign_across (f := g) ⟨hr.1.le,hr.2.le⟩ hκ.antitoneOn hleft hright with h | h
    · exact ⟨R, hR.trans (Finset.subset_insert _ _),h⟩
    · have hnot : r ∉ R := fun h ↦ (hmax r (hR h)).false
      refine ⟨insert r R, Finset.insert_subset_insert r hR, ?_⟩
      simpa only [Finset.prod_insert hnot, g, mul_left_comm, mul_assoc, mul_comm] using h

/-- Real, reflection-symmetric data on a period have an aligned companion;
its roots come from the distinct interior zeros on the half period. -/
theorem exists_aligned_angles {f : ℝ → ℝ} (hf : Continuous f)
    (hreflect : ∀ t, f (2 * π - t) = f t)
    (hfinite : {t : ℝ | t ∈ Ioo 0 π ∧ f t = 0}.Finite) :
    ∃ e ≤ {t : ℝ | t ∈ Ioo 0 π ∧ f t = 0}.ncard, ∃ a : Fin e → ℝ,
      (∀ j, a j ∈ Ioo 0 π) ∧
      OneSign (fun t ↦ f t * companionWeight a 0 t) (Icc 0 (2 * π)) := by
  classical
  let s := hfinite.toFinset
  have hs : ∀ t ∈ s, t ∈ Ioo 0 π := fun t ht ↦ (hfinite.mem_toFinset.mp ht).1
  obtain ⟨R,hR,hsgn⟩ := select_sign_factors f Real.cos hf continuous_cos s strictAntiOn_cos hs
    (fun t ht he ↦ hfinite.mem_toFinset.mpr ⟨ht,he⟩)
  let a (j : Fin R.card) := R.orderEmbOfFin rfl j
  have ha : ∀ j, a j ∈ Ioo 0 π := fun j ↦ hs (a j) (hR (R.orderEmbOfFin_mem rfl j))
  have heval (t : ℝ) : companionWeight a 0 t =
      2^R.card * ∏ r ∈ R, (Real.cos t - Real.cos r) := by
    have he := (R.orderIsoOfFin rfl).toEquiv.prod_comp (fun j : R ↦ Real.cos t - Real.cos j.val)
    change (∏ j : Fin R.card, (Real.cos t - Real.cos (a j))) = _ at he
    rw [Finset.prod_coe_sort R (fun x : ℝ ↦ Real.cos t - Real.cos x)] at he
    simp [companionWeight, Finset.prod_mul_distrib, he]
  have he' (t : ℝ) : f t * companionWeight a 0 t =
      (f t * ∏ r ∈ R, (Real.cos t - Real.cos r)) * 2^R.card := by rw [heval]; ring
  have hsym (t : ℝ) :
      f (2*π-t) * companionWeight a 0 (2*π-t) = f t * companionWeight a 0 t := by
    simp [companionWeight,hreflect]
  have hreduce (t : ℝ) (ht : t ∈ Icc 0 (2*π)) :
      ∃ u ∈ Icc 0 π, f t * companionWeight a 0 t = f u * companionWeight a 0 u := by
    by_cases h : t ≤ π
    · exact ⟨t,⟨ht.1,h⟩,rfl⟩
    · exact ⟨2*π-t,⟨sub_nonneg.mpr ht.2,by linarith⟩,(hsym t).symm⟩
  refine ⟨R.card, (Finset.card_le_card hR).trans_eq (Set.ncard_eq_toFinset_card _ hfinite).symm, a, ha, ?_⟩
  rcases hsgn with h | h
  · left
    intro t ht
    obtain ⟨u,hu,he⟩ := hreduce t ht
    dsimp only
    rw [he,he']
    exact mul_nonneg (h u hu) (by positivity)
  · right
    intro t ht
    obtain ⟨u,hu,he⟩ := hreduce t ht
    dsimp only
    rw [he,he']
    exact mul_nonpos_of_nonpos_of_nonneg (h u hu) (by positivity)

private theorem integral_abs_of_oneSign {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hs : OneSign f (Icc a b)) : (∫ t in a..b, |f t|) ≤ |∫ t in a..b, f t| := by
  rcases hs with hp | hn
  · calc
      _ = ∫ t in a..b, f t := intervalIntegral.integral_congr (by
        rw [uIcc_of_le hab]; exact fun x hx ↦ abs_of_nonneg (hp x hx))
      _ ≤ _ := le_abs_self _
  · calc
      _ = ∫ t in a..b, -f t := intervalIntegral.integral_congr (by
        rw [uIcc_of_le hab]; exact fun x hx ↦ abs_of_nonpos (hn x hx))
      _ = -(∫ t in a..b, f t) := intervalIntegral.integral_neg
      _ ≤ _ := neg_le_abs _

/-- The centered square of the difference multiplier gives a real weight with
constant sign. Its vanishing at zero leaves positive mass arbitrarily near zero. -/
theorem correlated_angles_for_period {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : f 0 ≠ 0)
    (hreflect : ∀ t, f (2*π-t) = f t) (hfinite : {t : ℝ | t ∈ Ioo 0 π ∧ f t = 0}.Finite)
    {P : ℕ} (hP : 0 < P) :
    ∃ e ≤ {t : ℝ | t ∈ Ioo 0 π ∧ f t = 0}.ncard, ∃ (a : Fin e → ℝ) (ε : ℝ),
      (∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → (angleCompanion a ε).eval z ≠ 0) ∧
      (∫ t in 0..(2*π), |(f t * (2*Real.cos (P*t)-2)) * companionWeight a ε t|) / 2 <
      |∫ t in 0..(2*π), (f t * (2*Real.cos (P*t)-2)) * companionWeight a ε t| := by
  obtain ⟨e,he,a,ha,hsgn⟩ := exists_aligned_angles hf hreflect hfinite
  let W (t : ℝ) := companionWeight a 0 t
  let M (t : ℝ) := 2 * Real.cos (P*t) - 2
  have hW : Continuous W := by dsimp [W, companionWeight]; fun_prop
  have hM : Continuous M := by dsimp [M]; fun_prop
  have hMneg (t : ℝ) : M t ≤ 0 := by dsimp [M]; linarith [Real.cos_le_one (P*t)]
  have hs : OneSign (fun t ↦ f t * M t * W t) (Icc 0 (2*π)) := by
    rcases hsgn with h | h
    · right
      intro t ht
      change f t * M t * W t ≤ 0
      rw [mul_right_comm]
      exact mul_nonpos_of_nonneg_of_nonpos (h t ht) (hMneg t)
    · left
      intro t ht
      change 0 ≤ f t * M t * W t
      rw [mul_right_comm]
      exact mul_nonneg_of_nonpos_of_nonpos (h t ht) (hMneg t)
  have hW₀ : W 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply mul_ne_zero (by norm_num)
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (ha j).2.le (ha j).1
    simpa only [add_zero] using sub_ne_zero.mpr hcos.ne'
  have hF : ∀ᶠ t in 𝓝 0, f t * W t ≠ 0 := (hf.mul hW).continuousAt.eventually_ne (mul_ne_zero hf₀ hW₀)
  have hp' : (0 : ℝ) < P := by exact_mod_cast hP
  have hpos : 0 < ∫ t in 0..(2*π), |f t * M t * W t| := by
    apply intervalIntegral.integral_pos (by positivity) ((hf.mul hM).mul hW).abs.continuousOn (fun _ _ ↦ abs_nonneg _)
    have hturn : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Ioo 0 (2*π) := Ioo_mem_nhdsGT (by positivity)
    have hnear : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Ioo 0 (π/P) := Ioo_mem_nhdsGT (div_pos pi_pos hp')
    obtain ⟨t,ht,hsmall,hne⟩ := (hturn.and (hnear.and (hF.filter_mono nhdsWithin_le_nhds))).exists
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (le_refl 0)
      (by linarith [(lt_div_iff₀ hp').mp hsmall.2] : (P:ℝ)*t≤π) (mul_pos hp' ht.1)
    have hm : M t ≠ 0 := by dsimp [M]; simp only [Real.cos_zero] at hc; linarith
    refine ⟨t,⟨ht.1.le,ht.2.le⟩,abs_pos.mpr ?_⟩
    rw [mul_right_comm]
    exact mul_ne_zero hne hm
  have hcorr := integral_abs_of_oneSign (by positivity : (0:ℝ) ≤ 2*π) hs
  obtain ⟨ε,_,hfree,hbound⟩ := exists_correlated_companion a (w := fun t ↦ f t * M t) (hf.mul hM) 0 (2*π)
    (U := univ) univ_mem hpos hcorr
  exact ⟨e,he,a,ε,hfree,hbound⟩

end OMA.G82

namespace OMA.G82

open Polynomial Finset Complex Set Filter Real
open scoped Topology
/-- The same cosine polynomial in the angular variable used by the companion. -/
noncomputable def radianCosineSum (N : ℕ) (b : ℕ → ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N+1), (b k : ℝ) * Real.cos ((k : ℝ) * t)

theorem radianCosineSum_scaled (N : ℕ) (b : ℕ → ℕ) (θ : ℝ) :
    radianCosineSum N b (2*π*θ) = cosineSum N b θ := by
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring

private theorem radianCosineSum_reflect (N : ℕ) (b : ℕ → ℕ) (t : ℝ) :
    radianCosineSum N b (2*π-t) = radianCosineSum N b t := by
  simp [radianCosineSum, mul_sub, Real.cos_nat_mul_two_pi_sub]

private theorem radian_half_zero_image (N : ℕ) (b : ℕ → ℕ) :
    {t : ℝ | t ∈ Set.Ioo 0 π ∧ radianCosineSum N b t = 0} =
      (fun θ : ℝ ↦ 2*π*θ) '' {θ : ℝ | θ ∈ Set.Ioo 0 (1/2) ∧ cosineSum N b θ = 0} := by
  ext t
  constructor
  · rintro ⟨ht,he⟩
    have h : 2*π*(t/(2*π)) = t := by field_simp
    refine ⟨t/(2*π),⟨⟨div_pos ht.1 two_pi_pos, (div_lt_iff₀ two_pi_pos).mpr (by linarith [ht.2])⟩,
      ?_⟩,h⟩
    simpa [← radianCosineSum_scaled, h] using he
  · rintro ⟨θ,⟨hθ,he⟩,rfl⟩
    refine ⟨⟨mul_pos two_pi_pos hθ.1,?_⟩,by simpa [radianCosineSum_scaled] using he⟩
    nlinarith [mul_pos two_pi_pos (sub_pos.mpr hθ.2)]

private theorem unitPhase_nat_mul (k : ℕ) (t : ℝ) :
    unitPhase ((k : ℝ)*t) = (unitPhase t)^k := by
  simp only [unitPhase, Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul, mul_assoc]

theorem palindromicLift_eval_phase (N : ℕ) (b : ℕ → ℕ) (t : ℝ) :
    (palindromicLift N b).eval (unitPhase t) = 2 * (unitPhase t)^N * (radianCosineSum N b t : ℂ) := by
  simp only [palindromicLift, eval_finsetSum, eval_add, eval_monomial, radianCosineSum,
    Complex.ofReal_sum, Complex.ofReal_mul, mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Finset.mem_range_succ_iff.mp hk
  have hcos := two_cos_unitPhase ((k : ℝ)*t)
  rw [unitPhase_nat_mul] at hcos
  rw [show (2 : ℂ) * unitPhase t ^ N * _ =
    (b k : ℂ) * unitPhase t ^ N * (2 * (Real.cos ((k : ℝ)*t) : ℂ)) by push_cast; ring, hcos]
  rw [pow_add, show unitPhase t ^ N = unitPhase t ^ (N-k) * unitPhase t ^ k by
    rw [← pow_add, Nat.sub_add_cancel hkN]]
  field_simp [unitPhase_ne_zero]
  ring

/-- Fourier projection of an ordinary polynomial, in radian normalization. -/
theorem coefficient_as_angular_integral (F : Polynomial ℂ) (m : ℕ) :
    (2*π)⁻¹ • (∫ t in (0 : ℝ)..(2*π), ((unitPhase t)^m)⁻¹ * F.eval (unitPhase t)) = F.coeff m := by
  let _ : Fact (0 < 2*π) := ⟨two_pi_pos⟩
  have hbase (t : ℝ) : ((AddCircle.toCircle (t : AddCircle (2*π))) : ℂ) = unitPhase t := by
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_self two_pi_pos.ne', one_mul]
    rfl
  have heval (t : ℝ) : F.toAddCircle (t : AddCircle (2*π)) = F.eval (unitPhase t) := by
    induction F using Polynomial.induction_on' with
    | add f g hf hg => simp [hf,hg]
    | monomial k c =>
      simp only [Polynomial.toAddCircle, aeval_monomial, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
        eval_monomial]
      change c * ((AddCircle.toCircle (t : AddCircle (2*π))) : ℂ)^k = _
      rw [hbase]
  have hfour (t : ℝ) : fourier (-(m:ℤ)) (t : AddCircle (2*π)) = ((unitPhase t)^m)⁻¹ := by
    rw [fourier_apply, AddCircle.toCircle_zsmul]
    simp [hbase]
  rw [← Polynomial.fourierCoeff_toAddCircle_natCast, fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp [hfour,heval,smul_eq_mul]

/-- The multiplier square is a nonpositive real factor times its middle monomial. -/
private theorem centered_difference_eval (P : ℕ) (t : ℝ) :
    ((unitPhase t)^P - 1)^2 = (unitPhase t)^P * ((2 * Real.cos (P*t) - 2 : ℝ) : ℂ) := by
  push_cast
  have hc := two_cos_unitPhase ((P:ℝ)*t)
  rw [unitPhase_nat_mul] at hc
  push_cast at hc
  rw [hc]
  field_simp [unitPhase_ne_zero]
  ring

private theorem normalized_l1_of_centered_correlation {F : Polynomial ℂ} {m : ℕ} {B : ℝ → ℝ}
    (heval : ∀ t, F.eval (unitPhase t) = (unitPhase t)^m * ((2 * B t : ℝ) : ℂ))
    (hcorr : (∫ t in 0..(2*π), |B t|) / 2 < |∫ t in 0..(2*π), B t|) :
    (∫ θ in (0 : ℝ)..1, ‖F.eval (unitPhase (2*π*θ))‖) ≤ 2 * ‖F.coeff m‖ := by
  have hphase (t : ℝ) : ((unitPhase t)^m)⁻¹ * F.eval (unitPhase t) = ((2 * B t : ℝ) : ℂ) := by
    rw [heval, inv_mul_cancel_left₀ (pow_ne_zero _ (unitPhase_ne_zero t))]
  have hnorm (t : ℝ) : ‖F.eval (unitPhase t)‖ = 2 * |B t| := by
    rw [heval, norm_mul, norm_pow, norm_unitPhase, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hproj := coefficient_as_angular_integral F m
  simp_rw [hphase] at hproj
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul] at hproj
  have hn := congrArg norm hproj
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos two_pi_pos, Complex.norm_real, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)] at hn
  rw [intervalIntegral.integral_comp_mul_left (fun t ↦ ‖F.eval (unitPhase t)‖) two_pi_pos.ne']
  simp only [mul_zero,mul_one,smul_eq_mul,hnorm, intervalIntegral.integral_const_mul]
  rw [← hn]
  nlinarith [mul_lt_mul_of_pos_left hcorr (inv_pos.mpr two_pi_pos)]

/-- For every differencing period there is a low-degree companion with no
torsion roots and bounded normalized integral for the entire sparse product.
The estimate does not grow with the period or the degree of the original sum. -/
theorem exists_small_l1_companion {N P : ℕ} {b : ℕ → ℕ}
    (hP : 0 < P) (hb : ∀ k ≤ N, b k ≤ 2) (h₀ : cosineSum N b 0 ≠ 0) :
    ∃ (e : ℕ) (Q : Polynomial ℂ), e ≤ halfRoots N b ∧ Q.Monic ∧ Q.natDegree = 2*e ∧
      Q.coeff 0 = 1 ∧ (∀ j, ‖Q.coeff j‖ ≤ (2 : ℝ)^(2*e)) ∧
      (∀ T : ℕ, 0 < T → ∀ z : ℂ, z^T = 1 → Q.eval z ≠ 0) ∧
      (∫ θ in (0 : ℝ)..1,
        ‖((Q*(X^P-1)^2)*palindromicLift N b).eval (unitPhase (2*π*θ))‖) ≤
        32 * ((2*e : ℕ) + 1 : ℝ) * 2^(2*e) := by
  let f := radianCosineSum N b
  have hf : Continuous f := by
    change Continuous (fun t : ℝ ↦ ∑ k ∈ Finset.range (N+1), (b k : ℝ)*Real.cos (k*t))
    fun_prop
  have hf₀ : f 0 ≠ 0 := by simpa [f, ← radianCosineSum_scaled] using h₀
  have hfin : {t : ℝ | t ∈ Set.Ioo 0 π ∧ f t = 0}.Finite := by
    rw [show {t : ℝ | t ∈ Set.Ioo 0 π ∧ f t = 0} = _ from radian_half_zero_image N b]
    apply Set.Finite.image
    apply (finite_zeros_Icc (analytic_cosine_sum N b) h₀).subset
    rintro t ⟨ht,he⟩
    exact ⟨⟨ht.1.le, by linarith [ht.2]⟩,he⟩
  have hcount : {t : ℝ | t ∈ Set.Ioo 0 π ∧ f t = 0}.ncard = halfRoots N b := by
    rw [show {t : ℝ | t ∈ Set.Ioo 0 π ∧ f t = 0} = _ from radian_half_zero_image N b]
    exact ncard_image_of_injective _ (fun _ _ he ↦ mul_left_cancel₀ two_pi_pos.ne' he)
  obtain ⟨e,he,a,ε,htor,hcorr⟩ := correlated_angles_for_period hf hf₀ (radianCosineSum_reflect N b) hfin hP
  let Q := angleCompanion a ε
  let F := (Q*(X^P-1)^2)*palindromicLift N b
  let B (t : ℝ) := f t * (2*Real.cos (P*t)-2) * companionWeight a ε t
  let m := N + e + P
  have heval (t : ℝ) : F.eval (unitPhase t) = (unitPhase t)^m * ((2 * B t : ℝ) : ℂ) := by
    simp only [F, Q, eval_mul, eval_pow, eval_sub, eval_X, eval_one, angleCompanion_eval_phase,
      palindromicLift_eval_phase, centered_difference_eval, m, pow_add, B, f]
    push_cast
    ring
  have h1 := normalized_l1_of_centered_correlation heval hcorr
  have h2 := lift_multiplier_coeff_bound hb Q (A := (2:ℝ)^(2*e)) (by positivity)
    (angleCompanion_coeff_bound a ε) P m
  rw [hcount] at he
  refine ⟨e,Q,he,angleCompanion_monic a ε,angleCompanion_degree a ε,angleCompanion_coeff_zero a ε,
    angleCompanion_coeff_bound a ε,htor,h1.trans ?_⟩
  change ‖F.coeff m‖ ≤ _ at h2
  rw [show Q.natDegree = 2*e from angleCompanion_degree a ε] at h2
  linarith

end OMA.G82

namespace OMA.G82

open Real
private theorem bounded_power_on_rootScale {a t d : ℕ}
    (ha : a ≤ 1000*(d+1)) (ht : t ≤ 4*(d+1)) :
    ((a^t : ℕ) : ℝ) ≤ exp (4000*rootScale d) := by
  let x : ℝ := d+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hxpos : 0 < x := by linarith
  have hbase : 0 < 1000*x := by positivity
  have hpow : a^t ≤ (1000*(d+1))^(4*(d+1)) :=
    (Nat.pow_le_pow_left ha t).trans (Nat.pow_le_pow_right (by omega) ht)
  calc
    _ ≤ ((1000*x)^(4*(d+1)) : ℝ) := by dsimp [x]; exact_mod_cast hpow
    _ ≤ _ := by
      apply (log_le_iff_le_exp (pow_pos hbase _)).mp
      rw [log_pow, log_mul (by norm_num) hxpos.ne']
      push_cast
      have hlog := log_nonneg hx
      have h1000 := log_le_self (by norm_num : (0:ℝ) ≤ 1000)
      change 4*x*(log 1000 + log x) ≤ 4000*(x*(1+log x))
      nlinarith [mul_le_mul_of_nonneg_left h1000 hxpos.le, mul_nonneg hxpos.le hlog]

/-- The factorial common period, Cramer threshold and rank-block cost all obey
the section-four exponential bound, including for zero roots. -/
theorem sectionFour_envelope {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ d : ℕ,
      let D := 2*d
      let m := D+1
      let P := (2*m).factorial
      let L := 33^m+m+(m+10*P)+1
      let δ : ℝ := 1 / (2*((m : ℝ)+1)*m.factorial*(17 : ℝ)^m)
      let W : ℝ := 1000*(m : ℝ)*(4 : ℝ)^m
      (P : ℝ) + ((D+2*P : ℕ) : ℝ) + log 2 + log L + (L : ℝ)*W/(c*δ) ≤ exp (B*rootScale d) := by
  refine ⟨32003+1/c, by have := inv_pos.mpr hc; linarith [one_div c], ?_⟩
  intro d D m P L δ W
  let Z := exp (4000*rootScale d)
  have hZ0 : 0 < Z := exp_pos _
  have hscale : 1 ≤ rootScale d := by
    have hx : 1 ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
    exact one_le_mul_of_one_le_of_one_le hx (by linarith [log_nonneg hx])
  have h1000 : 1000 ≤ Z := by
    simpa using (bounded_power_on_rootScale (a := 1000) (t := 1)
      (d := d) (by omega) (by omega))
  have hZ : 1 ≤ Z := by linarith
  have power (a t : ℕ) (ha : a ≤ 1000*(d+1)) (ht : t ≤ 4*(d+1)) :
      (a : ℝ)^t ≤ Z := by simpa [Z] using bounded_power_on_rootScale ha ht
  have hm : m ≤ 4*(d+1) := by dsimp [m,D]; omega
  have hfac (n : ℕ) (hn : n ≤ 4*(d+1)) : (n.factorial : ℝ) ≤ Z := by
    exact (show (n.factorial : ℝ) ≤ (n : ℝ)^n by exact_mod_cast Nat.factorial_le_pow n).trans
      (power n n (by omega) hn)
  have hP : (P : ℝ) ≤ Z := hfac (2*m) (by dsimp [m,D]; omega)
  have hM : (m : ℝ) ≤ Z := by simpa using power m 1 (by omega) (by omega)
  have hD : (D : ℝ) ≤ Z := by
    exact (show (D : ℝ) ≤ m by dsimp [m]; norm_num).trans hM
  have h33 : (33 : ℝ)^m ≤ Z := by simpa using power 33 m (by omega) hm
  have hL : (L : ℝ) ≤ Z^2 := by
    dsimp [L]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr h1000) hZ0.le]
  have hW : W ≤ Z^3 := by
    dsimp [W]
    calc
      _ ≤ Z * Z * Z := by
        gcongr
        simpa using power 4 m (by omega) hm
      _ = _ := by ring
  let I : ℝ := 2*((m:ℝ)+1)*m.factorial*(17:ℝ)^m
  have hI : I ≤ Z^3 := by
    have h2m : 2*((m : ℝ)+1) ≤ Z := by
      have h := power (2*(m+1)) 1 (by omega) (by omega)
      simpa using h
    dsimp [I]
    calc
      _ ≤ Z*Z*Z := by
        gcongr
        · exact hfac m hm
        · simpa using power 17 m (by omega) hm
      _ = _ := by ring
  have h8 : Z^2 ≤ Z^8 := pow_le_pow_right₀ hZ (by decide : 2 ≤ 8)
  have hterm : (L : ℝ)*W/(c*δ) ≤ Z^8/c := by
    change (L : ℝ)*W/(c*(1/I)) ≤ _
    have hIpos : 0 < I := by dsimp [I]; positivity
    rw [show (L : ℝ)*W/(c*(1/I)) = (L*W*I)/c by field_simp]
    apply div_le_div_of_nonneg_right _ hc.le
    calc
      _ ≤ Z^2*Z^3*Z^3 := by
        have hW0 : 0 ≤ W := by dsimp [W]; positivity
        gcongr
      _ = _ := by ring
  have hpre : (P : ℝ) + ((D+2*P : ℕ) : ℝ) + log 2 + log L ≤ 2*Z^8 := by
    push_cast
    have hlog := (log_le_self (Nat.cast_nonneg L)).trans hL
    have hlog2 := log_le_self (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr h1000) hZ0.le]
  have hconst : 3 + 1/c ≤ exp ((3+1/c)*rootScale d) := by
    have hh := le_mul_of_one_le_right (show 0 ≤ 3+1/c by positivity) hscale
    linarith [add_one_le_exp ((3+1/c)*rootScale d)]
  calc
    _ ≤ 2*Z^8 + Z^8/c := add_le_add hpre hterm
    _ ≤ (3+1/c)*Z^8 := by
      rw [div_eq_mul_inv, one_div]
      nlinarith [pow_nonneg hZ0.le 8]
    _ ≤ exp ((3+1/c)*rootScale d) * Z^8 := by gcongr
    _ = _ := by
      dsimp [Z]
      rw [← exp_nat_mul, ← exp_add]
      congr 1
      ring

end OMA.G82

namespace OMA.G82

open Polynomial Finset Real

private theorem ordered_eval_sum (p : Polynomial ℂ) (t : ℝ) :
    let ν := p.support.orderEmbOfFin rfl
    p.eval (unitPhase t) = ∑ i : Fin p.support.card,
      p.coeff (ν i) * angularCharacter ((ν i : ℕ) : ℤ) t := by
  dsimp only
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ p.support rfl]
  rw [Finset.sum_map]
  apply sum_congr rfl
  intro j _
  apply congrArg (_ * ·)
  simp only [angularCharacter, Int.cast_natCast, unitPhase, ← Complex.exp_nat_mul]
  congr 1
  exact (mul_assoc _ _ _).symm

/-- Quantitative sparsity of the perturbed companion product, obtained by
combining its small integral with the impossibility of a long stretch of tiny
nonzero coefficients. -/
theorem sparse_estimate_aux {C T : ℝ} (hC : 0 < C) (hT : 1 ≤ T)
    (hmps : ∀ (k : ℕ) (ν : Fin k ↪o ℤ) (a : Fin k → ℂ),
      C * (∑ j, ‖a j‖ / ((j.val : ℝ) + 1)) ≤
        ∫ t in (0 : ℝ)..1, ‖∑ j, a j * angularCharacter (ν j) (2 * π * t)‖)
    (henv : ∀ d : ℕ,
      let D := 2*d
      let m := D+1
      let P := (2*m).factorial
      let L := 33^m+m+(m+10*P)+1
      let δ : ℝ := 1/(2*((m:ℝ)+1)*m.factorial*(17:ℝ)^m)
      let W : ℝ := 1000*(m:ℝ)*(4:ℝ)^m
      (P:ℝ) + ((D+2*P:ℕ):ℝ) + log 2 + log L + (L:ℝ)*W/(C*δ) ≤ exp (T*rootScale d)) :
    SparseProductEstimate := by
  refine ⟨T,hT,?_⟩
  intro N b hb _ hg
  let d := halfRoots N b
  let D := 2*d
  let m := D+1
  let P := (2*m).factorial
  let L := 33^m+m+(m+10*P)+1
  let δ : ℝ := 1/(2*((m:ℝ)+1)*m.factorial*(17:ℝ)^m)
  let W : ℝ := 1000*(m:ℝ)*(4:ℝ)^m
  have hP : 0 < P := Nat.factorial_pos _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨e,Q,he,_,hdeg,h₀,_,htor,hupper⟩ :=
    exists_small_l1_companion hP hb (by linarith : cosineSum N b 0 ≠ 0)
  let q := Q*(X^P-1)^2
  let F := q * palindromicLift N b
  have hDQ : Q.natDegree ≤ D := by rw [hdeg]; exact Nat.mul_le_mul_left _ he
  have hdq : q.natDegree ≤ D+2*P := by
    apply (natDegree_mul_le ..).trans (Nat.add_le_add hDQ ?_)
    refine (natDegree_pow_le ..).trans ?_
    apply Nat.mul_le_mul_left
    exact (natDegree_sub_le ..).trans (by simp)
  refine ⟨P,Q,hP,by rw [h₀]; norm_num,htor,?_⟩
  let v := (X^(D+2*P)*integerLift N b).coeff
  let h (i : Fin m) := Q.coeff (D-i)
  have hpairs (a u : ℕ) : F.coeff (a+u) = tinyRunValue (fun n ↦ v (a+n)) P h u := by
    dsimp [F,q]
    rw [← integerLift_map, product_coefficient_window _ Q hDQ]
    simp only [tinyRunValue, stepDifference, h, v, Nat.add_assoc]
    rfl
  have hmax : 1 ≤ ‖h (⟨D, Nat.lt_succ_self D⟩ : Fin m)‖ := by simp [h,h₀]
  have hlocal (a n : ℕ) (hs : ∀ j < n, ‖F.coeff (a+j)‖ ≤ δ)
      (u : ℕ) (hu : 33^m+m ≤ u) (hu' : u+(m+10*P)<n) : F.coeff (a+u) = 0 := by
    rw [hpairs]
    apply tiny_run_vanish (Nat.succ_pos D) (fun k ↦ v (a+k)) (fun k ↦ delayed_lift_bounded hb _ _)
      h _ hmax (fun j hj ↦ (hpairs a j) ▸ hs j hj) hu
    change u+m+10*P < n
    omega
  have hblocks := rank_blocks_of_vanishing hδ hlocal
  let ν := F.support.orderEmbOfFin rfl
  let w (i : Fin F.support.card) := F.coeff (ν i)
  have hweighted := hmps _ (ν.trans (Nat.castOrderEmbedding (α := ℤ))) w
  change C * (∑ i, ‖w i‖ / ((i.val : ℝ)+1)) ≤
    ∫ t in (0 : ℝ)..1, ‖∑ i, w i * angularCharacter (ν i) (2*π*t)‖ at hweighted
  change (∫ t in (0:ℝ)..1, ‖F.eval (unitPhase (2*π*t))‖) ≤ _ at hupper
  simp_rw [ordered_eval_sum] at hupper
  have hmono : (2*e : ℕ) ≤ m := by dsimp [m,D,d]; omega
  have hmono' : ((2*e : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
    exact_mod_cast (show 2*e+1 ≤ m from Nat.add_le_add_right (hdeg ▸ hDQ) 1)
  have hB : C*(∑ i, ‖w i‖ / ((i.val : ℝ)+1)) ≤ W := by
    apply (hweighted.trans hupper).trans
    dsimp [W]
    apply mul_le_mul (mul_le_mul (by norm_num : (32:ℝ) ≤ 1000) hmono' (by positivity) (by norm_num))
      _ (by positivity) (by positivity)
    exact (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ 4) _).trans
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hmono)
  have hlog := log_support_le_of_weighted_ranks (L := L) (Nat.succ_pos _) w hδ hC hB hblocks
  have h2 : log ((F.support.card:ℝ)+2) ≤ log 2 + log ((F.support.card:ℝ)+1) := by
    rw [← log_mul (by norm_num) (by positivity)]
    exact log_le_log (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) F.support.card])
  change (P:ℝ) + q.natDegree + log ((F.support.card:ℝ)+2) ≤ _
  have hcast : (q.natDegree:ℝ) ≤ ((D+2*P:ℕ):ℝ) := by exact_mod_cast hdq
  apply le_trans _ (henv d)
  change _ ≤ (P:ℝ) + ((D+2*P:ℕ):ℝ) + log 2 + log L + (L:ℝ)*W/(C*δ)
  linarith

end OMA.G82

namespace OMA.G82

theorem sparseProductEstimate_of_littlewood (h : LittlewoodL1) : SparseProductEstimate := by
  obtain ⟨C,hC,hmps⟩ := h
  obtain ⟨B,hB,henv⟩ := sectionFour_envelope hC
  exact sparse_estimate_aux hC hB hmps henv

/-- Both the structured bound and sparse companion estimate follow from the weighted Fourier inequality. -/
theorem solution_of_littlewood (hL : LittlewoodL1) : type_of% @Green82.green_82_lower_bound :=
  solution_of_estimates (structuredRootEstimate_of_littlewood hL)
    (structureEstimate_of_sparse (sparseProductEstimate_of_littlewood hL))

end OMA.G82

namespace OMA.G82

private def blockStart (R : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => blockStart R j + R^j

/-- Pad the list on the right, preserving its original ranks, so every block
is full. The coefficient at a padded frequency will be taken to be zero. -/
theorem geometric_frequency_blocks {R : ℕ} (hR : 0 < R) (k : ℕ) (ν : Fin k ↪o ℤ) :
    ∃ (J : ℕ) (s : ℕ → Finset ℤ), (∀ j < J, (s j).card = R^j) ∧
      (∀ j r, j < r → r < J → ∀ u ∈ s j, ∀ v ∈ s r, u < v) ∧
      ∀ i : Fin k, ∃ r < J, ν i ∈ s r ∧ R^r ≤ R*(i.val+1) := by
  classical
  obtain ⟨M, hM⟩ := (Set.finite_range ν).bddAbove
  let val (n : ℕ) : ℤ := if h : n < k then ν ⟨n,h⟩ else M + n + 1
  have hv : StrictMono val := by
    intro a b hab
    dsimp [val]
    split_ifs with ha hb hb
    · exact ν.strictMono (show (⟨a,ha⟩ : Fin k) < ⟨b,hb⟩ from hab)
    · have hz := hM (Set.mem_range_self (f := ν) (⟨a,ha⟩ : Fin k))
      omega
    · omega
    · omega
  let s (j : ℕ) := (Finset.Ico (blockStart R j) (blockStart R (j+1))).image val
  have hstart : StrictMono (blockStart R) := by
    apply strictMono_nat_of_lt_succ
    intro n
    change blockStart R n < blockStart R n + R^n
    exact Nat.lt_add_of_pos_right (pow_pos hR _)
  have hloc (n : ℕ) (i : ℕ) (hi : i < blockStart R n) :
      ∃ r < n, blockStart R r ≤ i ∧ i < blockStart R (r+1) := by
    induction n with
    | zero => exact absurd hi (Nat.not_lt_zero _)
    | succ n ih =>
      by_cases hlt : i < blockStart R n
      · obtain ⟨r,hr,h1,h2⟩ := ih hlt
        exact ⟨r,by omega,h1,h2⟩
      · exact ⟨n,by omega,by omega,hi⟩
  refine ⟨k,s,?_,?_,?_⟩
  · intro j _
    dsimp [s]
    rw [Finset.card_image_of_injective _ hv.injective, Nat.card_Ico]
    simp [blockStart]
  · intro j r hjr _ u hu v hmem
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hmem
    exact hv (((Finset.mem_Ico.mp ha).2.trans_le (hstart.monotone hjr)).trans_le
      (Finset.mem_Ico.mp hb).1)
  · intro i
    have hk : k ≤ blockStart R k := hstart.id_le k
    obtain ⟨r,hr,hlo,hhi⟩ := hloc k i.val (i.isLt.trans_le hk)
    refine ⟨r,hr,Finset.mem_image.mpr ⟨i.val,Finset.mem_Ico.mpr ⟨hlo,hhi⟩,by simp [val]⟩,?_⟩
    cases r with
    | zero => exact Nat.mul_pos hR (Nat.succ_pos i.val)
    | succ r =>
      change blockStart R r + R^r ≤ i.val at hlo
      rw [pow_succ, mul_comm (R^r) R]
      exact Nat.mul_le_mul_left _ (by omega)

end OMA.G82

namespace OMA.G82

open Real Finset
open scoped ComplexConjugate
/-- Test function built in order of increasing frequency blocks. -/
noncomputable def blockTest {X : Type*} (f g : ℕ → X → ℂ) : ℕ → X → ℂ
  | 0 => fun _ ↦ 0
  | n+1 => fun x ↦ f n x + Complex.exp (-g n x) * blockTest f g n x

/-- A one-sided real-part majorant bounds the dual test pointwise at every stage. -/
theorem blockTest_norm_le {X : Type*} (f g : ℕ → X → ℂ) (n : ℕ) (x : X)
    (hf : ∀ j < n, ‖f j x‖ ≤ 1) (hg : ∀ j < n, ‖f j x‖ ≤ (g j x).re) :
    ‖blockTest f g n x‖ ≤ 2 := by
  induction n with
  | zero => simp [blockTest]
  | succ n ih =>
    have hb := ih (fun j hj ↦ hf j (by omega)) (fun j hj ↦ hg j (by omega))
    let a := ‖f n x‖
    have ha : 0 ≤ a := norm_nonneg _
    have hau : a ≤ 1 := hf _ (by omega)
    have hdom : a ≤ (g n x).re := hg _ (by omega)
    have hpos : 0 < 1 + a := by linarith
    have hexp : Real.exp (-(g n x).re) ≤ (1 + a)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hpos (by linarith [Real.add_one_le_exp (g n x).re])
    apply (norm_add_le (f n x) _).trans
    rw [norm_mul, Complex.norm_exp, Complex.neg_re]
    calc
      _ ≤ a + (1 + a)⁻¹ * 2 := by gcongr
      _ ≤ 2 := by
        rw [← div_eq_inv_mul, ← le_sub_iff_add_le', div_le_iff₀ hpos]
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hau)]

/-- Expanding the recurrence makes each frequency block carry only the
damping from later blocks. -/
theorem blockTest_eq_sum {X : Type*} (f g : ℕ → X → ℂ) (n : ℕ) (x : X) :
    blockTest f g n x = ∑ j ∈ range n, f j x * Complex.exp (-(∑ i ∈ Ico (j+1) n, g i x)) := by
  induction n with
  | zero => simp [blockTest]
  | succ n ih =>
    change f n x + Complex.exp (-g n x) * blockTest f g n x = _
    rw [ih, mul_sum, sum_range_succ]
    simp only [Ico_self, sum_empty, neg_zero, Complex.exp_zero, mul_one]
    rw [add_comm (f n x)]
    apply congrArg (· + f n x)
    apply sum_congr rfl
    intro j hj
    rw [sum_Ico_succ_top (mem_range.mp hj), neg_add, Complex.exp_add]
    ring

/-- On the right half plane the exponential damping deviates from the
identity by at most twice the size of its argument. -/
theorem norm_one_sub_damping (z : ℂ) (hz : 0 ≤ z.re) : ‖1 - Complex.exp (-z)‖ ≤ 2 * ‖z‖ := by
  by_cases hsmall : ‖z‖ ≤ 1
  · rw [norm_sub_rev]
    simpa using Complex.norm_exp_sub_one_le (x := -z) (by simpa using hsmall)
  · have he : ‖Complex.exp (-z)‖ ≤ 1 := by simpa [Complex.norm_exp] using hz
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-z)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_one]; linarith

/-- The contribution of all later blocks to a Fourier coefficient can be
estimated using only the L² sizes of their majorants. This is the pointwise
step before applying Cauchy--Schwarz. -/
theorem norm_block_correction_le {X : Type*} (f g : ℕ → X → ℂ) (n j : ℕ) (x : X)
    (hg : ∀ i ∈ Ico (j+1) n, 0 ≤ (g i x).re) :
    ‖f j x * (1 - Complex.exp (-(∑ i ∈ Ico (j+1) n, g i x)))‖ ≤
      2 * ‖f j x‖ * ∑ i ∈ Ico (j+1) n, ‖g i x‖ := by
  have hsum : 0 ≤ (∑ i ∈ Ico (j+1) n, g i x).re := by
    rw [Complex.re_sum]
    exact sum_nonneg hg
  rw [norm_mul]
  calc
    _ ≤ ‖f j x‖ * (2 * ‖∑ i ∈ Ico (j+1) n, g i x‖) := by
      exact mul_le_mul_of_nonneg_left (norm_one_sub_damping _ hsum) (norm_nonneg _)
    _ ≤ _ := by rw [← mul_assoc, mul_comm _ 2]; gcongr; exact norm_sum_le _ _


open AddCircle MeasureTheory
open scoped ComplexConjugate

noncomputable abbrev circleL2 := ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle 1 inferInstance) ℂ

private theorem harmonic_energy {ι : Type*} (s : Finset ι) (ν : ι → ℤ)
    (hν : Function.Injective ν) (a : ι → ℂ) :
    ‖circleL2 (∑ i ∈ s, a i • (fourier (T := 1) (ν i)))‖^2 = ∑ i ∈ s, ‖a i‖^2 := by
  have ho := (orthonormal_fourier (T := 1)).comp ν hν
  rw [map_sum]
  simp only [map_smul]
  rw [@norm_sq_eq_re_inner ℂ]
  have he := ho.inner_sum a a s
  change inner ℂ (∑ i ∈ s, a i • circleL2 (fourier (ν i))) (∑ i ∈ s, a i • circleL2 (fourier (ν i))) = _ at he
  rw [he]
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

/-- A normalized block of m distinct characters with unit-bounded phases
has squared L² norm at most 1/m, independently of its frequencies. -/
theorem frequency_block_energy {ι : Type*} (s : Finset ι) (ν : ι → ℤ)
    (hν : Function.Injective ν) (a : ι → ℂ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ‖circleL2 (∑ i ∈ s, (a i / s.card) • fourier (T := 1) (ν i))‖^2 ≤ (s.card : ℝ)⁻¹ := by
  rw [harmonic_energy s ν hν]
  by_cases h : s.card = 0
  · simp [h]
  calc
    _ ≤ ∑ _i ∈ s, ((s.card : ℝ)⁻¹)^2 := by
      apply sum_le_sum
      intro i hi
      rw [norm_div, Complex.norm_natCast]
      gcongr
      simpa only [one_div] using div_le_div_of_nonneg_right (ha i hi) (Nat.cast_nonneg s.card)
    _ = _ := by simp; field_simp

/-- The linear span of the constant and nonpositive-frequency characters on the unit circle. -/
noncomputable def negativeFourierSpan : Submodule ℂ C(AddCircle (1:ℝ), ℂ) :=
  Submodule.span ℂ (fourier (T := 1) '' Set.Iic (0 : ℤ))

/-- Fold the positive frequencies of a trigonometric polynomial into the
nonpositive frequencies by conjugation. Its real part is preserved, and
the L² norm of the resulting polynomial is at most twice the original. -/
theorem one_sided_real_part (s : Finset ℤ) (a : ℤ → ℂ) :
    ∃ g ∈ negativeFourierSpan,
      (∀ x, (g x).re = ((∑ k ∈ s, a k • fourier (T := 1) k) x).re) ∧
      ‖circleL2 g‖ ≤ 2 * ‖circleL2 (∑ k ∈ s, a k • fourier (T := 1) k)‖ := by
  let u := s.filter (· ≤ 0)
  let v := s.filter (¬ · ≤ 0)
  let low := ∑ k ∈ u, a k • fourier (T := 1) k
  let flip := ∑ k ∈ v, conj (a k) • fourier (T := 1) (-k)
  have join := sum_filter_add_sum_filter_not s (fun k ↦ k ≤ 0) (fun k ↦ a k • fourier (T := 1) k)
  refine ⟨low + flip, Submodule.add_mem _ ?_ ?_, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, (mem_filter.mp hk).2, rfl⟩)
  · apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨-k, by have hk' : ¬ k ≤ 0 := (mem_filter.mp hk).2; exact (show -k ≤ 0 from neg_nonpos.mpr (lt_of_not_ge hk').le), rfl⟩)
  · intro x
    rw [← join]
    simp only [low,flip,u,v,ContinuousMap.add_apply, ContinuousMap.sum_apply,
      Complex.add_re, Complex.re_sum, ContinuousMap.smul_apply, smul_eq_mul]
    congr 1
    apply sum_congr rfl
    intro k _
    rw [fourier_neg, ← map_mul, Complex.conj_re]
  · let n := ‖circleL2 (∑ k ∈ s, a k • fourier (T := 1) k)‖
    have htot := harmonic_energy s id Function.injective_id a
    change n^2 = _ at htot
    have bound (t : Finset ℤ) (ht : t ⊆ s) : ∑ k ∈ t, ‖a k‖^2 ≤ n^2 := by
      rw [htot]
      exact sum_le_sum_of_subset_of_nonneg ht (by intros; positivity)
    have hlow : ‖circleL2 low‖ ≤ n := by
      have h := harmonic_energy u id Function.injective_id a
      have hb := bound u (filter_subset ..)
      change ‖circleL2 low‖^2 = _ at h
      nlinarith [norm_nonneg (circleL2 low), show 0 ≤ n from norm_nonneg _]
    have hflip : ‖circleL2 flip‖ ≤ n := by
      have h := harmonic_energy v (fun k ↦ -k) neg_injective (fun k ↦ conj (a k))
      simp only [Complex.norm_conj] at h
      change ‖circleL2 flip‖^2 = _ at h
      have hb := bound v (filter_subset ..)
      nlinarith [norm_nonneg (circleL2 flip), show 0 ≤ n from norm_nonneg _]
    rw [map_add]
    exact (norm_add_le _ _).trans (by change _ ≤ 2*n; linarith)


private theorem circleL2_contraction (f : C(AddCircle (1 : ℝ), ℂ)) : ‖circleL2 f‖ ≤ ‖f‖ := by
  have hc : ‖circleL2‖ ≤ 1 := by
    simpa [measureUnivNNReal] using ContinuousMap.toLp_norm_le (E := ℂ) (p := 2) (𝕜 := ℂ) (@haarAddCircle 1 _)
  simpa using (circleL2.le_opNorm f).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg f))

/-- Uniform approximation and one-sided reflection give an analytic
majorant for the modulus of a block, with controlled L² norm. -/
theorem one_sided_modulus_majorant (f : C(AddCircle (1 : ℝ), ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ negativeFourierSpan, (∀ x, ‖f x‖ ≤ (g x).re) ∧
      ‖circleL2 g‖ ≤ 2 * ‖circleL2 f‖ + 3 * ε := by
  let u : C(AddCircle (1 : ℝ), ℂ) := ⟨fun x ↦ (‖f x‖ : ℂ), by fun_prop⟩
  have huet : ‖circleL2 u‖ = ‖circleL2 f‖ := by
    have he : inner ℂ (circleL2 u) (circleL2 u) = inner ℂ (circleL2 f) (circleL2 f) := by
      rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
      congr 1
      funext x
      simp [u, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two]
    have h := congrArg Complex.re he
    change RCLike.re (inner ℂ (circleL2 u) (circleL2 u)) =
        RCLike.re (inner ℂ (circleL2 f) (circleL2 f)) at h
    rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h
    nlinarith [norm_nonneg (circleL2 u), norm_nonneg (circleL2 f)]
  have hu : u ∈ closure ((Submodule.span ℂ (Set.range (@fourier 1))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨q,hq,hclose⟩ := Metric.mem_closure_iff.mp hu ε hε
  obtain ⟨a,ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
  obtain ⟨p,hp,hr,hn⟩ := one_sided_real_part a.support a
  change (∑ k ∈ a.support, a k • fourier (T := 1) k) = q at ha
  rw [ha] at hr hn
  let e : C(AddCircle (1 : ℝ), ℂ) := (ε : ℂ) • fourier (T := 1) 0
  have hem : e ∈ negativeFourierSpan :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, rfl⟩)
  have hx (x : AddCircle (1 : ℝ)) : (e x).re = ε := by simp [e]
  refine ⟨p+e, Submodule.add_mem _ hp hem, ?_, ?_⟩
  · intro x
    change ‖f x‖ ≤ (p x + e x).re
    rw [Complex.add_re, hx, hr]
    have h := (Complex.re_le_norm ((u-q) x)).trans ((u-q).norm_coe_le_norm x)
    rw [dist_eq_norm] at hclose
    change (‖f x‖ : ℂ).re - (q x).re ≤ ‖u-q‖ at h
    simpa using (show (‖f x‖ : ℂ).re ≤ (q x).re + ε by linarith)
  · have hqnorm : ‖circleL2 q‖ ≤ ‖circleL2 f‖ + ε := by
      rw [← huet]
      apply (norm_le_norm_add_norm_sub _ _).trans
      gcongr
      rw [← map_sub]
      apply (circleL2_contraction _).trans
      simpa [dist_eq_norm, norm_sub_rev] using hclose.le
    have hen : ‖circleL2 e‖ ≤ ε := by
      apply (circleL2_contraction _).trans
      simp [e, norm_smul, fourier_norm, abs_of_pos hε]
    rw [map_add]
    exact (norm_add_le _ _).trans (by linarith)


/-- With nonpositive frequencies, multiplication keeps the spectrum in the
same half-line. -/
private noncomputable def negativeFourierAlgebra : Subalgebra ℂ C(AddCircle (1 : ℝ), ℂ) :=
  Algebra.adjoin ℂ (fourier (T := 1) '' Set.Iic (0 : ℤ))

private theorem negativeFourierAlgebra_span :
    negativeFourierAlgebra.toSubmodule = negativeFourierSpan := by
  apply Algebra.adjoin_eq_span_of_subset
  apply Set.Subset.trans _ Submodule.subset_span
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one =>
    exact ⟨0, Set.mem_Iic.mpr le_rfl, ContinuousMap.ext fun _ ↦ fourier_zero⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k,hk,rfl⟩ := hx
    obtain ⟨l,hl,rfl⟩ := hy
    exact ⟨k+l, Set.mem_Iic.mpr (add_nonpos hk hl), ContinuousMap.ext fun _ ↦ fourier_add⟩

private theorem circle_exp_apply (f : C(AddCircle (1 : ℝ), ℂ)) (x : AddCircle (1 : ℝ)) :
    NormedSpace.exp f x = Complex.exp (f x) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x) (continuous_eval_const _) f

/-- Multiplying by the damping polynomial's exponential cannot generate any
Fourier coefficient above the original single frequency. -/
theorem upper_frequency_vanishes (g : C(AddCircle (1 : ℝ), ℂ)) (hg : g ∈ negativeFourierSpan)
    {k n : ℤ} (hkn : k < n) :
    inner ℂ (fourierLp (T := 1) 2 n) (circleL2 (fourier k * NormedSpace.exp (-g))) = 0 := by
  let F (p : C(AddCircle (1 : ℝ), ℂ)) := inner ℂ (fourierLp (T := 1) 2 n) (circleL2 (fourier k * p))
  have hF : Continuous F := continuous_const.inner (circleL2.continuous.comp
    (continuous_const.mul continuous_id))
  have hvanish : ∀ q ∈ negativeFourierSpan, F q = 0 := by
    intro q hq
    change q ∈ Submodule.span _ _ at hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨l,hl,rfl⟩ := hq
      have he : fourier (T := 1) k * fourier l = fourier (k+l) :=
        ContinuousMap.ext fun _ ↦ fourier_add.symm
      change inner ℂ _ (circleL2 (fourier k * fourier l)) = 0
      rw [he]
      exact (orthonormal_fourier (T := 1)).2 (show n ≠ k+l by have : l ≤ 0 := hl; omega)
    | zero => simp [F]
    | add a b _ _ ha hb =>
      change inner ℂ _ (circleL2 (fourier k * (a+b))) = 0
      rw [mul_add, map_add, inner_add_right]
      change F a + F b = 0
      simp [ha, hb]
    | smul r a _ ha =>
      change inner ℂ _ (circleL2 (fourier k * (r • a))) = 0
      rw [mul_smul_comm, map_smul, inner_smul_right]
      change r * F a = _
      simp [ha]
  have hgc : -g ∈ negativeFourierAlgebra.topologicalClosure :=
    negativeFourierAlgebra.le_topologicalClosure (by
      change -g ∈ negativeFourierAlgebra.toSubmodule
      rw [negativeFourierAlgebra_span]
      exact negativeFourierSpan.neg_mem hg)
  have he := NormedSpace.exp_mem (R := ℂ) negativeFourierAlgebra.isClosed_topologicalClosure hgc
  apply closure_minimal (s := (negativeFourierSpan : Set C(AddCircle (1:ℝ),ℂ)))
    (t := {p | F p = 0}) hvanish (isClosed_eq hF continuous_const)
  change NormedSpace.exp (-g) ∈ closure (negativeFourierAlgebra : Set _) at he
  rw [← negativeFourierAlgebra_span]
  exact he


private theorem circleL2_mono {f g : C(AddCircle (1 : ℝ), ℂ)} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    ‖circleL2 f‖ ≤ ‖circleL2 g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle, g.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle]
    with x hx hy
  rw [hx,hy]
  exact h x

/-- The Fourier coefficient of a product is controlled by the two L² norms. -/
private theorem circle_coefficient_product_le (f h : C(AddCircle (1:ℝ), ℂ)) (n : ℤ) :
    ‖inner ℂ (fourierLp (T := 1) 2 n) (circleL2 (f * h))‖ ≤ ‖circleL2 f‖ * ‖circleL2 h‖ := by
  let w := star f * fourier (T := 1) n
  have he : inner ℂ (fourierLp (T := 1) 2 n) (circleL2 (f * h)) = inner ℂ (circleL2 w) (circleL2 h) := by
    change inner ℂ (circleL2 (fourier n)) _ = _
    rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
    congr 1
    funext x
    simp [w, mul_left_comm, mul_comm]
  rw [he]
  apply (norm_inner_le_norm _ _).trans
  gcongr
  apply circleL2_mono
  intro x
  simp [w, fourier_apply, Circle.norm_coe]

/-- Per-frequency error bound for a block times the product of all its
subsequent exponential dampers. -/
theorem fourier_block_error {ι : Type*} (s : Finset ι) (g : ι → C(AddCircle (1 : ℝ), ℂ))
    (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℤ) (hg : ∀ i ∈ s, ∀ x, 0 ≤ (g i x).re) :
    ‖inner ℂ (fourierLp (T := 1) 2 n)
        (circleL2 (f * (1 - NormedSpace.exp (-(∑ i ∈ s, g i)))))‖ ≤
      2 * ‖circleL2 f‖ * ∑ i ∈ s, ‖circleL2 (g i)‖ := by
  let G := ∑ i ∈ s, g i
  have hre (x : AddCircle (1 : ℝ)) : 0 ≤ (G x).re := by
    simp only [G, ContinuousMap.sum_apply, Complex.re_sum]
    exact sum_nonneg fun i hi ↦ hg i hi x
  have hG : ‖circleL2 (1 - NormedSpace.exp (-G))‖ ≤ 2 * ∑ i ∈ s, ‖circleL2 (g i)‖ := by
    calc
      _ ≤ ‖circleL2 ((2 : ℂ) • G)‖ := by
        apply circleL2_mono
        intro x
        simpa only [ContinuousMap.sub_apply, ContinuousMap.one_apply, circle_exp_apply,
          ContinuousMap.neg_apply, ContinuousMap.smul_apply, norm_smul, Complex.norm_ofNat] using
          norm_one_sub_damping (G x) (hre x)
      _ ≤ _ := by rw [map_smul, norm_smul, Complex.norm_ofNat, show circleL2 G = _ from map_sum ..]
                  gcongr
                  exact norm_sum_le _ _
  apply (circle_coefficient_product_le _ _ _).trans
  rw [mul_assoc, mul_left_comm 2]
  exact mul_le_mul_of_nonneg_left hG (norm_nonneg _)


noncomputable def circleCoefficient (n : ℤ) : C(AddCircle (1:ℝ), ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (fourierLp (T := 1) 2 n)).comp circleL2

private theorem coefficient_block (s : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) :
    circleCoefficient n (∑ k ∈ s, a k • fourier k) = if n ∈ s then a n else 0 := by
  classical
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hc (k : ℤ) : circleCoefficient n (fourier k) = if n = k then 1 else 0 :=
    orthonormal_iff_ite.mp (orthonormal_fourier (T := 1)) n k
  simp [hc]

private theorem norm_phase_block_le (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (x : AddCircle (1 : ℝ)) :
    ‖(∑ i ∈ s, (a i / s.card) • fourier (T := 1) i) x‖ ≤ 1 := by
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  calc
    _ ≤ ∑ i ∈ s, ‖(a i / s.card) • fourier (T := 1) i x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, (s.card : ℝ)⁻¹ := by
      apply sum_le_sum
      intro i _
      simp only [norm_smul, fourier_apply, Circle.norm_coe, mul_one, norm_div, Complex.norm_natCast]
      simpa only [one_div] using div_le_div_of_nonneg_right (ha i) (Nat.cast_nonneg s.card)
    _ ≤ _ := by
      by_cases h : s.card = 0 <;> simp [h]

private theorem geom_tail (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Ico a b, q^j ≤ q^a / (1-q) := by
  rw [geom_sum_Ico' hq'.ne hab]
  gcongr
  exact sub_le_self _ (pow_nonneg hq _)

/-- Test the phases on ordered, equal-weight blocks whose sizes grow by a
factor 4096. The approximation error at each occupied frequency is at most
half the corresponding block weight. -/
theorem exists_block_fourier_test (J : ℕ) (s : ℕ → Finset ℤ) (a : ℤ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hs : ∀ j < J, (s j).card = 4096^j)
    (hord : ∀ j r, j < r → r < J → ∀ u ∈ s j, ∀ v ∈ s r, u < v) :
    ∃ T : C(AddCircle (1:ℝ), ℂ), (∀ x, ‖T x‖ ≤ 2) ∧
      ∀ r < J, ∀ n ∈ s r, ‖circleCoefficient n T - a n / (4096 : ℂ)^r‖ ≤
        (1/2 : ℝ) / (4096:ℝ)^r := by
  classical
  let f (j : ℕ) : C(AddCircle (1:ℝ), ℂ) :=
    ∑ k ∈ s j, (a k / (s j).card) • fourier k
  let q := (1/64 : ℝ)
  have hq : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have qsq : q^2 = (4096 : ℝ)⁻¹ := by norm_num [q]
  have hE (j : ℕ) (hj : j < J) : ‖circleL2 (f j)‖ ≤ q^j := by
    have h := frequency_block_energy (s j) id Function.injective_id a (fun i _ ↦ ha i)
    change ‖circleL2 (f j)‖^2 ≤ _ at h
    rw [hs j hj, Nat.cast_pow, Nat.cast_ofNat] at h
    have he : (q^j)^2 = ((4096:ℝ)^j)⁻¹ := by rw [← pow_mul, Nat.mul_comm, pow_mul, qsq, inv_pow]
    rw [← he] at h
    nlinarith [norm_nonneg (circleL2 (f j)), pow_nonneg hq.le j]
  choose g hgm hgr hgn using (fun j : ℕ ↦ one_sided_modulus_majorant (f j) (pow_pos hq j))
  have hg (j : ℕ) (hj : j < J) : ‖circleL2 (g j)‖ ≤ 5 * q^j := by linarith [hgn j, hE j hj]
  let G (j : ℕ) := ∑ i ∈ Ico (j+1) J, g i
  let D (j : ℕ) := NormedSpace.exp (-(G j))
  let E (j : ℕ) := f j * (1 - D j)
  let T := ∑ j ∈ range J, f j * D j
  refine ⟨T, ?_, ?_⟩
  · intro x
    have ht : T x = blockTest (fun i y ↦ f i y) (fun i y ↦ g i y) J x := by
      simp [T,D,G,blockTest_eq_sum,circle_exp_apply, ContinuousMap.sum_apply]
    rw [ht]
    exact blockTest_norm_le _ _ J x (fun j _ ↦ norm_phase_block_le (s j) a ha x)
      (fun j _ ↦ hgr j x)
  intro r hr n hn
  let C := circleCoefficient n
  have hplain (j : ℕ) (hj : j < J) (hjr : j ≠ r) : n ∉ s j := by
    intro hn'
    rcases lt_or_gt_of_ne hjr with h | h
    · exact lt_irrefl n (hord j r h hr n hn' n hn)
    · exact lt_irrefl n (hord r j h hj n hn n hn')
  have hmain : ∑ j ∈ range J, C (f j) = a n / (4096:ℂ)^r := by
    rw [sum_eq_single_of_mem r (mem_range.mpr hr)]
    · simp only [C,f,coefficient_block, if_pos hn, hs r hr, Nat.cast_pow, Nat.cast_ofNat]
    · intro j hj hne
      simp only [C,f,coefficient_block,if_neg (hplain j (mem_range.mp hj) hne)]
  have hearly (j : ℕ) (hjr : j < r) : C (E j) = 0 := by
    have hG : G j ∈ negativeFourierSpan := Submodule.sum_mem _ fun i _ ↦ hgm i
    have hfd : C (f j * D j) = 0 := by
      simp only [f, sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
      apply sum_eq_zero
      intro k hk
      have hzero := upper_frequency_vanishes (G j) hG (hord j r hjr hr k hk n hn)
      change _ * C (fourier k * D j) = 0
      exact mul_eq_zero_of_right _ hzero
    simp only [E, mul_sub, mul_one, map_sub, hfd, sub_zero, C, f, coefficient_block,
      if_neg (hplain j (hjr.trans hr) hjr.ne)]
  have herr (j : ℕ) (hj : j < J) : ‖C (E j)‖ ≤ (1/4 : ℝ) * (q^2)^j := by
    have h1 := fourier_block_error (Ico (j+1) J) g (f j) n
      (fun i _ x ↦ (norm_nonneg _).trans (hgr i x))
    have hsum : ∑ i ∈ Ico (j+1) J, ‖circleL2 (g i)‖ ≤ 5 * (q^(j+1)/(1-q)) := by
      calc
        _ ≤ ∑ i ∈ Ico (j+1) J, 5*q^i := sum_le_sum fun i hi ↦ hg i (mem_Ico.mp hi).2
        _ ≤ _ := by rw [← mul_sum]; gcongr; exact geom_tail q hq.le hq1 hj
    apply h1.trans
    calc
      _ ≤ 2 * q^j * (5 * (q^(j+1)/(1-q))) := by gcongr; exact hE j hj
      _ ≤ _ := by
        rw [pow_succ, ← pow_mul, Nat.mul_comm, pow_mul, pow_two]
        generalize q^j = z
        norm_num [q]
        nlinarith [sq_nonneg z]
  have hall : C T = (∑ j ∈ range J, C (f j)) - ∑ j ∈ range J, C (E j) := by
    rw [← sum_sub_distrib]
    simp only [T, map_sum]
    apply sum_congr rfl
    intro j _
    simp [E, mul_sub]
  have ht0 : ∑ j ∈ range r, C (E j) = 0 := sum_eq_zero (fun j hj ↦ hearly j (mem_range.mp hj))
  have htrim : ∑ j ∈ range J, C (E j) = ∑ j ∈ Ico r J, C (E j) := by
    rw [sum_Ico_eq_sub _ hr.le, ht0, sub_zero]
  change ‖C T - _‖ ≤ _
  rw [hall,hmain,htrim,sub_sub_cancel_left, norm_neg]
  calc
    _ ≤ ∑ j ∈ Ico r J, ‖C (E j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Ico r J, (1/4:ℝ) * (q^2)^j :=
      sum_le_sum (fun j hj ↦ herr j (mem_Ico.mp hj).2)
    _ ≤ (1/4:ℝ) * ((q^2)^r / (1-q^2)) := by
      rw [← mul_sum]
      gcongr
      exact geom_tail _ (sq_nonneg _) (by norm_num [q]) hr.le
    _ ≤ _ := by
      rw [qsq, inv_pow]
      have hpos : 0 < (4096:ℝ)^r := by positivity
      field_simp
      norm_num

end OMA.G82

namespace OMA.G82

open Real Finset AddCircle MeasureTheory
open scoped ComplexConjugate
private theorem bounded_test_pairing (F T : C(AddCircle (1:ℝ),ℂ)) (hT : ∀ x, ‖T x‖ ≤ 2) :
    ‖inner ℂ (circleL2 F) (circleL2 T)‖ ≤
      2 * ∫ θ in (0:ℝ)..1, ‖F (θ : AddCircle (1:ℝ))‖ := by
  let μ := @haarAddCircle (1:ℝ) inferInstance
  have hgi : Integrable (fun x ↦ 2 * ‖F x‖) μ := by
    have hcont : Continuous (fun x ↦ 2 * ‖F x‖) := by fun_prop
    simpa using hcont.continuousOn.integrableOn_compact
      (μ := μ) isCompact_univ
  rw [ContinuousMap.inner_toLp]
  calc
    _ ≤ ∫ x, ‖inner ℂ (F x) (T x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, 2 * ‖F x‖ ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hgi
      apply Filter.Eventually.of_forall
      intro x
      calc
        ‖inner ℂ (F x) (T x)‖ ≤ ‖F x‖ * ‖T x‖ := norm_inner_le_norm ..
        _ ≤ _ := by dsimp only; rw [mul_comm (2:ℝ)]; gcongr; exact hT x
    _ = _ := by
      rw [integral_const_mul, AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
      simp

private theorem weighted_phase_lower {z w : ℂ} {t : ℝ} (_ht : 0 < t)
    (he : ‖w - (z / (‖z‖ : ℂ)) / (t : ℂ)‖ ≤ (1/2:ℝ)/t) :
    ‖z‖/(2*t) ≤ (conj z * w).re := by
  have hc : conj z * ((z / (‖z‖ : ℂ)) / (t : ℂ)) = ((‖z‖/t : ℝ) : ℂ) := by
    by_cases hz : z = 0
    · simp [hz]
    rw [← mul_div_assoc, ← mul_div_assoc, Complex.conj_mul']
    push_cast
    field_simp [norm_ne_zero_iff.mpr hz]
  let δ := w - (z / (‖z‖ : ℂ)) / (t : ℂ)
  have hreal := (abs_le.mp (Complex.abs_re_le_norm (conj z * δ))).1
  have hn : ‖conj z * δ‖ ≤ ‖z‖ * ((1/2)/t) := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
  have hr : (conj z * δ).re = (conj z * w).re - ‖z‖/t := by
    dsimp only [δ]; rw [mul_sub,hc]; rfl
  rw [hr] at hreal
  have h₁ : ‖z‖/(2*t) = (‖z‖/t)/2 := by ring
  have h₂ : ‖z‖*((1/2)/t) = (‖z‖/t)/2 := by ring
  linarith

/-- Duality applied to the bounded test function gives the full weighted
Littlewood inequality for arbitrary complex coefficients. -/
theorem littlewood_l1 : LittlewoodL1 := by
  classical
  refine ⟨(1/16384 : ℝ),by norm_num,?_⟩
  intro k ν a
  obtain ⟨J,s,hs,hord,hcover⟩ := geometric_frequency_blocks (R := 4096) (by decide) k ν
  let A := Function.extend ν a (fun _ ↦ (0:ℂ))
  let φ (n : ℤ) := A n / (‖A n‖ : ℂ)
  have hφ (n : ℤ) : ‖φ n‖ ≤ 1 := by
    dsimp [φ]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  obtain ⟨T,hT,hc⟩ := exists_block_fourier_test J s φ hφ hs hord
  let F : C(AddCircle (1:ℝ), ℂ) := ∑ i, a i • fourier (ν i)
  have hpair : inner ℂ (circleL2 F) (circleL2 T) = ∑ i, conj (a i) * circleCoefficient (ν i) T := by
    rw [show circleL2 F = _ from map_sum ..,sum_inner]
    simp only [map_smul,inner_smul_left]
    rfl
  have hi (i : Fin k) : (‖a i‖ / ((i.val:ℝ)+1))/8192 ≤
      (conj (a i)*circleCoefficient (ν i) T).re := by
    obtain ⟨r,hr,hm,hi⟩ := hcover i
    have hpow : (4096:ℝ)^r ≤ 4096*((i.val:ℝ)+1) := by exact_mod_cast hi
    have hφi : φ (ν i) = (a i / (‖a i‖ : ℂ)) := by simp [φ,A,ν.injective.extend_apply]
    have h := hc r hr (ν i) hm
    rw [hφi] at h
    have h' := weighted_phase_lower (z := a i) (t := (4096:ℝ)^r) (by positivity) (by simpa using h)
    apply le_trans _ h'
    rw [div_div]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    linarith
  have hsummed := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
  rw [← Finset.sum_div, ← Complex.re_sum, ← hpair] at hsummed
  have hx := bounded_test_pairing F T hT
  have hf (θ : ℝ) : F (θ : AddCircle (1:ℝ)) = ∑ i, a i * angularCharacter (ν i) (2*Real.pi*θ) := by
    simp only [F,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [fourier_coe_apply,angularCharacter]
    push_cast
    ring_nf
  simp_rw [hf] at hx
  linarith [Complex.re_le_norm (inner ℂ (circleL2 F) (circleL2 T))]

end OMA.G82

theorem OMA.solution : type_of% @Green82.green_82_lower_bound := by
  exact OMA.G82.solution_of_littlewood OMA.G82.littlewood_l1
