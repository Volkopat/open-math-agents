import OMAReductions.R_Constant7b_irrational_gamma_one_div_four_R1
import Mathlib

/-!
Construction of the Weierstrass zeta function and proof of Legendre's period relation
for the lemniscatic square lattice (`OMA.R_Constant7b_irrational_gamma_one_div_four_R1.H1`).
-/

open Filter Topology Complex MeasureTheory

namespace WeierstrassLemniscate

section Zeta

noncomputable def weierstrassZetaExcept (L : PeriodPair) (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else (1 / (z - l.1) + 1 / l.1 + z / l.1 ^ 2)

noncomputable def weierstrassZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, (1 / (z - l.1) + 1 / l.1 + z / l.1 ^ 2)

lemma weierstrassZeta_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ)
    (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl_pos : 0 < ‖l‖ := by linarith
  have hl_ne : l ≠ 0 := norm_ne_zero_iff.mp hl_pos.ne'
  have hsl_ne : s - l ≠ 0 := by
    intro h0
    have hs_eq : s = l := sub_eq_zero.mp h0
    subst hs_eq
    linarith
  have halg : 1 / (s - l) + 1 / l + s / l ^ 2 = s ^ 2 / (l ^ 2 * (s - l)) := by
    field_simp [hl_ne, hsl_ne]
    ring
  rw [halg, norm_div, norm_mul, norm_pow, norm_pow]
  have hsub : ‖l‖ / 2 ≤ ‖s - l‖ := by
    rw [norm_sub_rev]
    have h1 := norm_sub_norm_le l s
    linarith
  have hden_pos : 0 < ‖l‖ ^ 2 * (‖l‖ / 2) := by positivity
  calc
    ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖)
        ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
          gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by
          field_simp [hl_pos.ne']
    _ = 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
          rw [Real.rpow_neg hl_pos.le, ← div_eq_mul_inv]
          norm_cast

lemma hasSumLocallyUniformly_weierstrassZetaExcept (L : PeriodPair) (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) =>
        if l.1 = l₀ then 0 else (1 / (z - l.1) + 1 / l.1 + z / l.1 ^ 2))
      (weierstrassZetaExcept L l₀) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l => 2 * r ^ 2 * ‖l.1‖ ^ (-3 : ℝ)) _
    (fun r _ => (ZLattice.summable_norm_rpow L.lattice (-3 : ℝ) (by simp; norm_num)).mul_left _)
    fun r hr => Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · rw [norm_zero]
    positivity
  · exact weierstrassZeta_bound r hr s hs l.1 h

lemma hasSum_weierstrassZetaExcept (L : PeriodPair) (l₀ : ℂ) (z : ℂ) :
    HasSum
      (fun l : L.lattice =>
        if l.1 = l₀ then 0 else (1 / (z - l.1) + 1 / l.1 + z / l.1 ^ 2))
      (weierstrassZetaExcept L l₀ z) :=
  (hasSumLocallyUniformly_weierstrassZetaExcept L l₀).hasSum

lemma differentiableOn_weierstrassZetaExcept (L : PeriodPair) (l₀ : ℂ) :
    DifferentiableOn ℂ (weierstrassZetaExcept L l₀) (L.lattice \ {l₀})ᶜ := by
  refine (hasSumLocallyUniformly_weierstrassZetaExcept L l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s => .fun_sum fun i _ => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs with hi
  · simp
  · refine ((DifferentiableOn.div (differentiableOn_const 1)
      (differentiableOn_id.sub (differentiableOn_const i.1)) ?_).add
      (differentiableOn_const _)).add
      (differentiableOn_id.div_const _)
    intro x hx hsub
    have hxe : x = i.1 := sub_eq_zero.mp hsub
    exact hx ⟨hxe ▸ i.2, hxe ▸ hi⟩

lemma weierstrassZetaExcept_zero_zero (L : PeriodPair) :
    weierstrassZetaExcept L 0 0 = 0 := by
  unfold weierstrassZetaExcept
  have hterm : ∀ l : L.lattice,
      (if l.1 = (0 : ℂ) then (0 : ℂ) else (1 / (0 - l.1) + 1 / l.1 + 0 / l.1 ^ 2)) = 0 := by
    intro l
    split_ifs with hl
    · rfl
    · simp only [zero_sub, zero_div, add_zero, div_neg, neg_add_cancel]
  simp_rw [hterm]
  exact tsum_zero

lemma weierstrassZetaExcept_add (L : PeriodPair) (l₀ : L.lattice) (z : ℂ) :
    weierstrassZetaExcept L l₀.1 z + (1 / (z - l₀.1) + 1 / l₀.1 + z / l₀.1 ^ 2) =
      weierstrassZeta L z := by
  trans weierstrassZetaExcept L l₀.1 z +
      ∑' i : L.lattice, if i = l₀ then (1 / (z - l₀.1) + 1 / l₀.1 + z / l₀.1 ^ 2) else 0
  · rw [tsum_ite_eq]
  · rw [weierstrassZetaExcept, ← Summable.tsum_add]
    · unfold weierstrassZeta
      congr 1 with w
      by_cases hw : w = l₀
      · subst hw; simp
      · have hw1 : w.1 ≠ l₀.1 := fun h => hw (Subtype.ext h)
        simp [hw, hw1]
    · exact ⟨_, hasSum_weierstrassZetaExcept L l₀.1 z⟩
    · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

lemma weierstrassZeta_sub_inv (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L z - z⁻¹ = weierstrassZetaExcept L 0 z := by
  have h := weierstrassZetaExcept_add L 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, div_zero, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, one_div] at h
  rw [← h, add_sub_cancel_right]

lemma tendsto_weierstrassZeta_sub_inv (L : PeriodPair) :
    Tendsto (fun z : ℂ => weierstrassZeta L z - z⁻¹) (𝓝[≠] 0) (𝓝 0) := by
  simp_rw [weierstrassZeta_sub_inv]
  have hdiff : DifferentiableAt ℂ (weierstrassZetaExcept L 0) 0 :=
    (differentiableOn_weierstrassZetaExcept L 0).differentiableAt
      (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  have hcont : ContinuousAt (weierstrassZetaExcept L 0) 0 := hdiff.continuousAt
  have hval : weierstrassZetaExcept L 0 0 = 0 := weierstrassZetaExcept_zero_zero L
  have ht : Tendsto (weierstrassZetaExcept L 0) (𝓝[≠] 0) (𝓝 (weierstrassZetaExcept L 0 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  rwa [hval] at ht

lemma weierstrassZetaExcept_of_notMem (L : PeriodPair) (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    weierstrassZetaExcept L l₀ = weierstrassZeta L := by
  ext z
  unfold weierstrassZetaExcept weierstrassZeta
  congr 1 with l
  have hne : l.1 ≠ l₀ := fun h => hl (h ▸ l.2)
  simp [hne]

lemma hasSumLocallyUniformly_weierstrassZeta (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) => 1 / (z - l.1) + 1 / l.1 + z / l.1 ^ 2)
      (weierstrassZeta L) := by
  have h := hasSumLocallyUniformly_weierstrassZetaExcept L (L.ω₁ / 2)
  rw [weierstrassZetaExcept_of_notMem L _ L.ω₁_div_two_notMem_lattice] at h
  convert h using 3 with l z
  have hne : l.1 ≠ L.ω₁ / 2 := fun he => L.ω₁_div_two_notMem_lattice (he ▸ l.2)
  simp [hne]

lemma hasSum_weierstrassZeta (L : PeriodPair) (z : ℂ) :
    HasSum (fun l : L.lattice => 1 / (z - l.1) + 1 / l.1 + z / l.1 ^ 2) (weierstrassZeta L z) :=
  (hasSumLocallyUniformly_weierstrassZeta L).hasSum

lemma differentiableOn_weierstrassZeta (L : PeriodPair) :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ := by
  rw [← weierstrassZetaExcept_of_notMem L _ L.ω₁_div_two_notMem_lattice]
  have h := differentiableOn_weierstrassZetaExcept L (L.ω₁ / 2)
  have hset : ((L.lattice : Set ℂ) \ {L.ω₁ / 2})ᶜ = (L.lattice : Set ℂ)ᶜ := by
    ext x
    simp [L.ω₁_div_two_notMem_lattice]
  rwa [hset] at h

lemma eqOn_deriv_weierstrassZeta (L : PeriodPair) :
    Set.EqOn (deriv (weierstrassZeta L)) (fun z => -L.weierstrassP z) L.latticeᶜ := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hderiv_lim := (hasSumLocallyUniformly_weierstrassZeta L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s => .fun_sum fun i _ => by
      refine ((DifferentiableOn.div (differentiableOn_const 1)
        (differentiableOn_id.sub (differentiableOn_const i.1)) ?_).add
        (differentiableOn_const _)).add
        (differentiableOn_id.div_const _)
      intro x hx hsub
      have hxe : x = i.1 := sub_eq_zero.mp hsub
      exact hx (hxe ▸ i.2)) hopen
  have hneg_P :
      TendstoLocallyUniformlyOn
        (fun (s : Finset L.lattice) (z : ℂ) => -(∑ i ∈ s, (1 / (z - i.1) ^ 2 - 1 / i.1 ^ 2)))
        (fun z => -L.weierstrassP z) atTop (L.lattice : Set ℂ)ᶜ := by
    have hP := L.hasSumLocallyUniformly_weierstrassP.tendstoLocallyUniformlyOn.mono
      (Set.subset_univ (L.lattice : Set ℂ)ᶜ)
    exact uniformContinuous_neg.comp_tendstoLocallyUniformlyOn hP
  refine hderiv_lim.unique (hneg_P.congr ?_)
  intro s z hz
  simp only [Function.comp_apply, ← Finset.sum_neg_distrib]
  rw [deriv_fun_sum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have hne : z - l.1 ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ l.2)
    have h1 : HasDerivAt (fun w : ℂ => 1 / (w - l.1)) (-1 / (z - l.1) ^ 2) z := by
      have ha := (hasDerivAt_const z (1 : ℂ)).fun_div ((hasDerivAt_id z).sub_const l.1) hne
      refine ha.congr_deriv ?_
      simp only [id_eq]
      ring
    have h2 : HasDerivAt (fun _ : ℂ => 1 / l.1) 0 z := hasDerivAt_const z _
    have h3 : HasDerivAt (fun w : ℂ => w / l.1 ^ 2) (1 / l.1 ^ 2) z :=
      (hasDerivAt_id z).div_const (l.1 ^ 2)
    have htot : HasDerivAt (fun w : ℂ => 1 / (w - l.1) + 1 / l.1 + w / l.1 ^ 2)
        (-1 / (z - l.1) ^ 2 + 0 + 1 / l.1 ^ 2) z := (h1.fun_add h2).fun_add h3
    rw [htot.deriv]
    ring
  · intro l _
    have hne : z - l.1 ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ l.2)
    exact (((differentiableAt_const (1 : ℂ)).div
      (differentiableAt_id.sub (differentiableAt_const l.1)) hne).add
      (differentiableAt_const _)).add (differentiableAt_id.div_const _)

lemma weierstrassZeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  unfold weierstrassZeta
  rw [← tsum_neg, ← (Equiv.neg L.lattice).tsum_eq]
  congr 1 with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg]
  have h1 : -z - -l.1 = -(z - l.1) := by ring
  rw [h1, div_neg, div_neg]
  ring

lemma weierstrassZeta_add_coe (L : PeriodPair) (l : L.lattice) (hl : l.1 / 2 ∉ L.lattice) :
    Set.EqOn (fun z => weierstrassZeta L (z + l.1))
      (fun z => weierstrassZeta L z + 2 * weierstrassZeta L (l.1 / 2)) L.latticeᶜ := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hconn : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  refine hopen.eqOn_of_deriv_eq hconn ?_ ?_ ?_ (x := -(l.1 / 2)) ?_ ?_
  · refine (differentiableOn_weierstrassZeta L).comp (differentiableOn_id.add (differentiableOn_const l.1)) ?_
    intro x hx hmem
    exact hx (by simpa using sub_mem hmem l.2)
  · exact (differentiableOn_weierstrassZeta L).add (differentiableOn_const _)
  · intro x hx
    have hxl : x + l.1 ∉ L.lattice := fun hmem => hx (by simpa using sub_mem hmem l.2)
    rw [deriv_comp_add_const, deriv_add_const',
      eqOn_deriv_weierstrassZeta L hxl, eqOn_deriv_weierstrassZeta L hx]
    dsimp only
    rw [L.weierstrassP_add_coe]
  · intro hmem
    exact hl (by simpa using neg_mem hmem)
  · have hhalf : -(l.1 / 2) + l.1 = l.1 / 2 := by ring
    rw [hhalf, weierstrassZeta_neg]
    ring

end Zeta

section SquareLattice

noncomputable def squarePeriod (ω : ℝ) (hω : 0 < ω) : PeriodPair where
  ω₁ := 2 * (ω : ℂ)
  ω₂ := 2 * (ω : ℂ) * I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [add_re, add_im, real_smul, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      zero_re, zero_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, re_ofNat, im_ofNat] at hre him
    constructor
    · nlinarith
    · nlinarith

lemma mem_squarePeriod_lattice (ω : ℝ) (hω : 0 < ω) (w : ℂ) :
    w ∈ (squarePeriod ω hω).lattice ↔
      ∃ m n : ℤ, w = (2 * (m : ℂ) + 2 * (n : ℂ) * I) * (ω : ℂ) := by
  rw [PeriodPair.mem_lattice]
  simp only [squarePeriod]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by ring⟩

lemma ofReal_mem_squarePeriod_lattice (ω : ℝ) (hω : 0 < ω) (t : ℝ) :
    (t : ℂ) ∈ (squarePeriod ω hω).lattice ↔ ∃ m : ℤ, t = 2 * (m : ℝ) * ω := by
  rw [mem_squarePeriod_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    have hre := congrArg Complex.re h
    simp only [ofReal_re, mul_re, add_re, intCast_re, intCast_im, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, add_im, mul_im, re_ofNat, im_ofNat] at hre
    exact ⟨m, by linarith⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m, 0, ?_⟩
    push_cast
    ring

lemma Ioo_notMem_squarePeriod_lattice (ω : ℝ) (hω : 0 < ω) {t : ℝ} (ht0 : 0 < t)
    (ht2 : t < 2 * ω) : (t : ℂ) ∉ (squarePeriod ω hω).lattice := by
  rw [ofReal_mem_squarePeriod_lattice]
  rintro ⟨m, hm⟩
  have h1 : (0 : ℝ) < (m : ℝ) := by nlinarith
  have h2 : (m : ℝ) < 1 := by nlinarith
  have hm1 : (0 : ℤ) < m := Int.cast_pos.mp h1
  have hm2 : m < (1 : ℤ) := by exact_mod_cast h2
  omega

noncomputable def squareConjEquiv (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod ω hω).lattice ≃ (squarePeriod ω hω).lattice where
  toFun l := ⟨starRingEnd ℂ l.1, by
    rcases (mem_squarePeriod_lattice ω hω l.1).mp l.2 with ⟨m, n, hl⟩
    rw [mem_squarePeriod_lattice]
    refine ⟨m, -n, ?_⟩
    rw [hl]
    simp [map_mul, map_add, conj_ofReal, conj_I, map_ofNat]⟩
  invFun l := ⟨starRingEnd ℂ l.1, by
    rcases (mem_squarePeriod_lattice ω hω l.1).mp l.2 with ⟨m, n, hl⟩
    rw [mem_squarePeriod_lattice]
    refine ⟨m, -n, ?_⟩
    rw [hl]
    simp [map_mul, map_add, conj_ofReal, conj_I, map_ofNat]⟩
  left_inv l := Subtype.ext (Complex.conj_conj l.1)
  right_inv l := Subtype.ext (Complex.conj_conj l.1)

noncomputable def squareMulIEquiv (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod ω hω).lattice ≃ (squarePeriod ω hω).lattice where
  toFun l := ⟨I * l.1, by
    rcases (mem_squarePeriod_lattice ω hω l.1).mp l.2 with ⟨m, n, hl⟩
    rw [mem_squarePeriod_lattice]
    refine ⟨-n, m, ?_⟩
    rw [hl]
    push_cast
    linear_combination (2 * (n : ℂ) * (ω : ℂ)) * I_sq⟩
  invFun l := ⟨-I * l.1, by
    rcases (mem_squarePeriod_lattice ω hω l.1).mp l.2 with ⟨m, n, hl⟩
    rw [mem_squarePeriod_lattice]
    refine ⟨n, -m, ?_⟩
    rw [hl]
    push_cast
    linear_combination -(2 * (n : ℂ) * (ω : ℂ)) * I_sq⟩
  left_inv l := Subtype.ext (by linear_combination -l.1 * I_sq)
  right_inv l := Subtype.ext (by linear_combination -l.1 * I_sq)

noncomputable def squareScaleEquiv (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod 1 one_pos).lattice ≃ (squarePeriod ω hω).lattice where
  toFun l := ⟨(ω : ℂ) * l.1, by
    rcases (mem_squarePeriod_lattice 1 one_pos l.1).mp l.2 with ⟨m, n, hl⟩
    rw [mem_squarePeriod_lattice]
    refine ⟨m, n, ?_⟩
    rw [hl]
    push_cast
    ring⟩
  invFun l := ⟨(ω : ℂ)⁻¹ * l.1, by
    rcases (mem_squarePeriod_lattice ω hω l.1).mp l.2 with ⟨m, n, hl⟩
    rw [mem_squarePeriod_lattice]
    refine ⟨m, n, ?_⟩
    rw [hl]
    have hωc : (ω : ℂ) ≠ 0 := ofReal_ne_zero.mpr hω.ne'
    simp only [Complex.ofReal_one, mul_one]
    field_simp [hωc]⟩
  left_inv l := Subtype.ext (by
    have hωc : (ω : ℂ) ≠ 0 := ofReal_ne_zero.mpr hω.ne'
    field_simp [hωc])
  right_inv l := Subtype.ext (by
    have hωc : (ω : ℂ) ≠ 0 := ofReal_ne_zero.mpr hω.ne'
    field_simp [hωc])

lemma squarePeriod_weierstrassZeta_conj (ω : ℝ) (hω : 0 < ω) (z : ℂ) :
    weierstrassZeta (squarePeriod ω hω) (starRingEnd ℂ z) =
      starRingEnd ℂ (weierstrassZeta (squarePeriod ω hω) z) := by
  unfold weierstrassZeta
  rw [Complex.conj_tsum, ← (squareConjEquiv ω hω).tsum_eq]
  congr 1 with l
  simp [squareConjEquiv, map_add, map_sub, map_div₀, map_pow]

lemma squarePeriod_weierstrassP_conj (ω : ℝ) (hω : 0 < ω) (z : ℂ) :
    (squarePeriod ω hω).weierstrassP (starRingEnd ℂ z) =
      starRingEnd ℂ ((squarePeriod ω hω).weierstrassP z) := by
  unfold PeriodPair.weierstrassP
  rw [Complex.conj_tsum, ← (squareConjEquiv ω hω).tsum_eq]
  congr 1 with l
  simp [squareConjEquiv, map_sub, map_pow]

lemma squarePeriod_derivWeierstrassP_conj (ω : ℝ) (hω : 0 < ω) (z : ℂ) :
    (squarePeriod ω hω).derivWeierstrassP (starRingEnd ℂ z) =
      starRingEnd ℂ ((squarePeriod ω hω).derivWeierstrassP z) := by
  unfold PeriodPair.derivWeierstrassP
  rw [map_neg, Complex.conj_tsum, ← (squareConjEquiv ω hω).tsum_eq]
  congr 2 with l
  simp [squareConjEquiv, map_sub, map_div₀, map_pow, map_ofNat]

lemma squarePeriod_G_conj (ω : ℝ) (hω : 0 < ω) (n : ℕ) :
    starRingEnd ℂ ((squarePeriod ω hω).G n) = (squarePeriod ω hω).G n := by
  unfold PeriodPair.G
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (squareConjEquiv ω hω).tsum_eq]
  congr 1 with l
  simp [squareConjEquiv, map_inv₀, map_pow]

lemma squarePeriod_G_im_zero (ω : ℝ) (hω : 0 < ω) (n : ℕ) :
    ((squarePeriod ω hω).G n).im = 0 :=
  Complex.conj_eq_iff_im.mp (squarePeriod_G_conj ω hω n)

lemma squarePeriod_G_six (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod ω hω).G 6 = 0 := by
  have h : (squarePeriod ω hω).G 6 = -(squarePeriod ω hω).G 6 := by
    unfold PeriodPair.G
    rw [← tsum_neg]
    conv_lhs => rw [← (squareMulIEquiv ω hω).tsum_eq]
    congr 1 with l
    simp only [squareMulIEquiv, Equiv.coe_fn_mk]
    have hI6 : I ^ 6 = -1 := by
      calc I ^ 6 = (I ^ 2) ^ 3 := by ring
      _ = (-1) ^ 3 := by rw [I_sq]
      _ = -1 := by norm_num
    rw [mul_pow, hI6, neg_one_mul, inv_neg]
  exact CharZero.eq_neg_self_iff.mp h

lemma squarePeriod_g₃ (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod ω hω).g₃ = 0 := by
  simp [PeriodPair.g₃, squarePeriod_G_six]

lemma squarePeriod_weierstrassZeta_mul_I (ω : ℝ) (hω : 0 < ω) (z : ℂ) :
    weierstrassZeta (squarePeriod ω hω) (I * z) =
      -I * weierstrassZeta (squarePeriod ω hω) z := by
  unfold weierstrassZeta
  rw [← tsum_mul_left, ← (squareMulIEquiv ω hω).tsum_eq]
  congr 1 with l
  simp only [squareMulIEquiv, Equiv.coe_fn_mk]
  by_cases hl : l.1 = 0
  · simp only [hl, mul_zero, sub_zero, div_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    rw [one_div, mul_inv, inv_I, one_div]
  · have hI_ne : I ≠ 0 := I_ne_zero
    by_cases hzl : z - l.1 = 0
    · have hIz : I * z - I * l.1 = 0 := by linear_combination I * hzl
      rw [hzl, hIz]
      simp only [div_zero, zero_add]
      field_simp [hI_ne, hl]
      linear_combination (l.1 + z) * I_sq
    · have hIz : I * z - I * l.1 ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hI_ne hzl
      field_simp [hI_ne, hl, hzl, hIz]
      linear_combination (l.1 ^ 2 + z * l.1 - l.1 ^ 2 + z ^ 2 - z * l.1) * I_sq

lemma squarePeriod_G_four_scale (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod ω hω).G 4 = (squarePeriod 1 one_pos).G 4 / (ω : ℂ) ^ 4 := by
  unfold PeriodPair.G
  rw [div_eq_mul_inv, mul_comm, ← tsum_mul_left, ← (squareScaleEquiv ω hω).tsum_eq]
  congr 1 with l
  simp only [squareScaleEquiv, Equiv.coe_fn_mk, mul_pow, mul_inv]

lemma squarePeriod_g₂_scale (ω : ℝ) (hω : 0 < ω) :
    (squarePeriod ω hω).g₂ = (squarePeriod 1 one_pos).g₂ / (ω : ℂ) ^ 4 := by
  rw [PeriodPair.g₂, PeriodPair.g₂, squarePeriod_G_four_scale ω hω, mul_div_assoc]

lemma squarePeriod_weierstrassZeta_ofReal_im (ω : ℝ) (hω : 0 < ω) (t : ℝ) :
    (weierstrassZeta (squarePeriod ω hω) (t : ℂ)).im = 0 := by
  have h := squarePeriod_weierstrassZeta_conj ω hω (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma squarePeriod_weierstrassP_ofReal_im (ω : ℝ) (hω : 0 < ω) (t : ℝ) :
    ((squarePeriod ω hω).weierstrassP (t : ℂ)).im = 0 := by
  have h := squarePeriod_weierstrassP_conj ω hω (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma squarePeriod_derivWeierstrassP_ofReal_im (ω : ℝ) (hω : 0 < ω) (t : ℝ) :
    ((squarePeriod ω hω).derivWeierstrassP (t : ℂ)).im = 0 := by
  have h := squarePeriod_derivWeierstrassP_conj ω hω (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end SquareLattice

section PositivityG2

private def shell (k : ℕ) : Finset (ℤ × ℤ) :=
  (({-(k : ℤ), (k : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)) ∪
  (Finset.Icc (-(k : ℤ) + 1) ((k : ℤ) - 1) ×ˢ ({-(k : ℤ), (k : ℤ)} : Finset ℤ))

private lemma card_shell_le (k : ℕ) (hk : 1 ≤ k) : (shell k).card ≤ 8 * k := by
  unfold shell
  refine (Finset.card_union_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_product]
  have hpair : ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have h1 : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
    rw [Int.card_Icc]
    omega
  have h2 : (Finset.Icc (-(k : ℤ) + 1) ((k : ℤ) - 1)).card = 2 * k - 1 := by
    rw [Int.card_Icc]
    omega
  rw [h1, h2]
  have hA : ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card * (2 * k + 1) ≤ 2 * (2 * k + 1) :=
    Nat.mul_le_mul_right _ hpair
  have hB : (2 * k - 1) * ({-(k : ℤ), (k : ℤ)} : Finset ℤ).card ≤ (2 * k - 1) * 2 :=
    Nat.mul_le_mul_left _ hpair
  omega

private lemma mem_shell_of_max_eq (p : ℤ × ℤ) (k : ℕ)
    (hmax : max p.1.natAbs p.2.natAbs = k) : p ∈ shell k := by
  unfold shell
  rw [Finset.mem_union, Finset.mem_product, Finset.mem_product]
  have h1 : p.1.natAbs ≤ k := hmax ▸ le_max_left _ _
  have h2 : p.2.natAbs ≤ k := hmax ▸ le_max_right _ _
  have h1z : -(k : ℤ) ≤ p.1 ∧ p.1 ≤ k := by omega
  have h2z : -(k : ℤ) ≤ p.2 ∧ p.2 ≤ k := by omega
  rcases max_choice p.1.natAbs p.2.natAbs with hl | hr
  · left
    have h1eq : p.1.natAbs = k := hl.symm.trans hmax
    have h1or : p.1 = -(k : ℤ) ∨ p.1 = (k : ℤ) := by omega
    exact ⟨by simp [h1or], Finset.mem_Icc.mpr h2z⟩
  · by_cases h1eq : p.1.natAbs = k
    · left
      have h1or : p.1 = -(k : ℤ) ∨ p.1 = (k : ℤ) := by omega
      exact ⟨by simp [h1or], Finset.mem_Icc.mpr h2z⟩
    · right
      have h2eq : p.2.natAbs = k := hr.symm.trans hmax
      have h2or : p.2 = -(k : ℤ) ∨ p.2 = (k : ℤ) := by omega
      have h1lt : p.1.natAbs < k := lt_of_le_of_ne h1 h1eq
      exact ⟨Finset.mem_Icc.mpr (by omega), by simp [h2or]⟩

private lemma norm_inv_pow_four_le_of_mem_shell (k : ℕ) (hk : 1 ≤ k) (p : ℤ × ℤ)
    (hp : p ∈ shell k) :
    ‖(((p.1 : ℂ) + (p.2 : ℂ) * I) ^ 4)⁻¹‖ ≤ (1 : ℝ) / (k : ℝ) ^ 4 := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hge : (k : ℝ) ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    unfold shell at hp
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product] at hp
    rcases hp with ⟨h1, _⟩ | ⟨_, h2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with h1 | h1 <;>
        · rw [h1]; push_cast; nlinarith [sq_nonneg (p.2 : ℝ)]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      rcases h2 with h2 | h2 <;>
        · rw [h2]; push_cast; nlinarith [sq_nonneg (p.1 : ℝ)]
  have hnorm_sq : ‖(p.1 : ℂ) + (p.2 : ℂ) * I‖ ^ 2 = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [norm_inv, norm_pow, ← one_div]
  have h4 : (k : ℝ) ^ 4 ≤ ‖(p.1 : ℂ) + (p.2 : ℂ) * I‖ ^ 4 := by
    calc (k : ℝ) ^ 4 = ((k : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (‖(p.1 : ℂ) + (p.2 : ℂ) * I‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) (by linarith [hnorm_sq]) 2
    _ = ‖(p.1 : ℂ) + (p.2 : ℂ) * I‖ ^ 4 := by ring
  exact one_div_le_one_div_of_le (by positivity) h4

private lemma telescoping_shell_bound (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, ((8 : ℝ) * k) / (k : ℝ) ^ 4 ≤ 2 := by
  have hstep : ∀ k ∈ Finset.Icc 2 N,
      ((8 : ℝ) * k) / (k : ℝ) ^ 4 ≤
        4 / (((k : ℝ) - 1) * (k : ℝ)) - 4 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hkp1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hrhs : 4 / (((k : ℝ) - 1) * (k : ℝ)) - 4 / ((k : ℝ) * ((k : ℝ) + 1)) =
        8 / (((k : ℝ) - 1) * (k : ℝ) * ((k : ℝ) + 1)) := by
      field_simp [hkm1.ne', hk0.ne', hkp1.ne']
      ring
    rw [hrhs]
    have hlhs : ((8 : ℝ) * k) / (k : ℝ) ^ 4 = 8 / (k : ℝ) ^ 3 := by
      field_simp [hk0.ne']
    rw [hlhs]
    gcongr
    nlinarith
  refine (Finset.sum_le_sum hstep).trans ?_
  by_cases hN : N < 2
  · have hemp : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    norm_num
  · push Not at hN
    have htel : ∀ M : ℕ, 2 ≤ M →
        ∑ k ∈ Finset.Icc 2 M,
          (4 / (((k : ℝ) - 1) * (k : ℝ)) - 4 / ((k : ℝ) * ((k : ℝ) + 1))) =
        2 - 4 / ((M : ℝ) * ((M : ℝ) + 1)) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base =>
        simp
        norm_num
      | succ m hm ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
    rw [htel N hN]
    have hpos : (0 : ℝ) ≤ 4 / ((N : ℝ) * ((N : ℝ) + 1)) := by positivity
    linarith

lemma squarePeriod_one_G_four_re_pos : 0 < ((squarePeriod 1 one_pos).G 4).re := by
  let L₁ := squarePeriod 1 one_pos
  let f : ℤ × ℤ → ℂ := fun p => (((p.1 : ℂ) + (p.2 : ℂ) * I) ^ 4)⁻¹
  have hG4 : L₁.G 4 = (16 : ℂ)⁻¹ * ∑' p : ℤ × ℤ, f p := by
    unfold PeriodPair.G
    rw [← tsum_mul_left]
    rw [← L₁.latticeEquivProd.symm.tsum_eq]
    congr 1 with p
    change ((L₁.latticeEquivProd.symm p).1 ^ 4)⁻¹ = (16 : ℂ)⁻¹ * f p
    rw [L₁.latticeEquiv_symm_apply]
    simp only [L₁, squarePeriod, ofReal_one, mul_one, f]
    have h2 : (p.1 : ℂ) * 2 + (p.2 : ℂ) * (2 * I) = 2 * ((p.1 : ℂ) + (p.2 : ℂ) * I) := by ring
    rw [h2, mul_pow, mul_inv]
    norm_num
  have hsum_norm : Summable (fun p : ℤ × ℤ => ‖f p‖) := by
    have h1 : Summable (fun p : ℤ × ℤ => ‖((L₁.latticeEquivProd.symm p).1 ^ 4)⁻¹‖) := by
      have h0 : Summable (fun l : L₁.lattice => ‖(l.1 ^ 4)⁻¹‖) := by
        refine (ZLattice.summable_norm_zpow L₁.lattice (-4 : ℤ) (by simp)).congr fun l => ?_
        rw [norm_inv, norm_pow, zpow_neg, zpow_ofNat]
        rfl
      exact h0.comp_injective L₁.latticeEquivProd.symm.injective
    refine (h1.mul_left 16).congr fun p => ?_
    rw [L₁.latticeEquiv_symm_apply]
    simp only [L₁, squarePeriod, ofReal_one, mul_one, f]
    have h2 : (p.1 : ℂ) * 2 + (p.2 : ℂ) * (2 * I) = 2 * ((p.1 : ℂ) + (p.2 : ℂ) * I) := by ring
    rw [h2, mul_pow, mul_inv, norm_mul]
    have h16 : ‖((2 : ℂ) ^ 4)⁻¹‖ = (16 : ℝ)⁻¹ := by norm_num
    rw [h16]
    ring
  have hsum_f : Summable f := hsum_norm.of_norm
  let S₁ : Finset (ℤ × ℤ) := Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1
  have hsplit := hsum_f.sum_add_tsum_compl (s := S₁)
  have hS1_re : (∑ p ∈ S₁, f p).re = 3 := by
    have hS1_eq : S₁ = {(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1),
        (1, -1), (1, 0), (1, 1)} := by decide
    have hf_mm : f (-1, -1) = (-4 : ℂ)⁻¹ := by
      dsimp only [f]
      congr 1
      have h : ((-1 : ℂ) + (-1 : ℂ) * I) ^ 4 = -4 := by
        linear_combination (I ^ 2 + 4 * I + 5) * I_sq
      simpa using h
    have hf_mp : f (-1, 1) = (-4 : ℂ)⁻¹ := by
      dsimp only [f]
      congr 1
      have h : ((-1 : ℂ) + (1 : ℂ) * I) ^ 4 = -4 := by
        linear_combination (I ^ 2 - 4 * I + 5) * I_sq
      simpa using h
    have hf_pm : f (1, -1) = (-4 : ℂ)⁻¹ := by
      dsimp only [f]
      congr 1
      have h : ((1 : ℂ) + (-1 : ℂ) * I) ^ 4 = -4 := by
        linear_combination (I ^ 2 - 4 * I + 5) * I_sq
      simpa using h
    have hf_pp : f (1, 1) = (-4 : ℂ)⁻¹ := by
      dsimp only [f]
      congr 1
      have h : ((1 : ℂ) + (1 : ℂ) * I) ^ 4 = -4 := by
        linear_combination (I ^ 2 + 4 * I + 5) * I_sq
      simpa using h
    have hf_m0 : f (-1, 0) = 1 := by simp [f]; norm_num
    have hf_p0 : f (1, 0) = 1 := by simp [f]
    have hf_00 : f (0, 0) = 0 := by simp [f]
    have hf_0m : f (0, -1) = 1 := by
      have hI4 : (-I) ^ 4 = 1 := by linear_combination (I ^ 2 - 1) * I_sq
      simp [f, hI4]
    have hf_0p : f (0, 1) = 1 := by
      have hI4 : I ^ 4 = 1 := by linear_combination (I ^ 2 - 1) * I_sq
      simp [f, hI4]
    have hS1_val : ∑ p ∈ S₁, f p = (3 : ℂ) := by
      rw [hS1_eq]
      repeat rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton]
      rw [hf_mm, hf_m0, hf_mp, hf_0m, hf_00, hf_0p, hf_pm, hf_p0, hf_pp]
      norm_num
    rw [hS1_val]
    norm_num
  have hbiUnion_le : ∀ (A : Finset ℕ),
      ∑ p ∈ A.biUnion shell, ‖f p‖ ≤ ∑ k ∈ A, ∑ p ∈ shell k, ‖f p‖ := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have hunion : ∑ p ∈ shell a ∪ s.biUnion shell, ‖f p‖ ≤
          ∑ p ∈ shell a, ‖f p‖ + ∑ p ∈ s.biUnion shell, ‖f p‖ := by
        have h := Finset.sum_union_inter (s₁ := shell a) (s₂ := s.biUnion shell) (f := fun p => ‖f p‖)
        have hnn : 0 ≤ ∑ p ∈ shell a ∩ s.biUnion shell, ‖f p‖ :=
          Finset.sum_nonneg fun _ _ => norm_nonneg _
        linarith
      linarith
  have htail_norm : ∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), ‖f p.1‖ ≤ 2 := by
    have hsum_sub : Summable (fun p : ↑((S₁ : Set (ℤ × ℤ))ᶜ) => ‖f p.1‖) :=
      hsum_norm.subtype _
    refine hsum_sub.tsum_le_of_sum_le ?_
    intro F
    let N : ℕ := F.sup (fun p => max p.1.1.natAbs p.1.2.natAbs)
    have hsub : F.image Subtype.val ⊆ (Finset.Icc 2 N).biUnion shell := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨⟨q, hqS⟩, hqF, rfl⟩
      rw [Finset.mem_biUnion]
      refine ⟨max q.1.natAbs q.2.natAbs, ?_, mem_shell_of_max_eq q _ rfl⟩
      rw [Finset.mem_Icc]
      refine ⟨?_, Finset.le_sup (f := fun p : ↑((S₁ : Set (ℤ × ℤ))ᶜ) => max p.1.1.natAbs p.1.2.natAbs) hqF⟩
      by_contra hlt
      push Not at hlt
      apply hqS
      simp only [Finset.mem_coe, S₁, Finset.mem_product, Finset.mem_Icc]
      omega
    calc
      ∑ p ∈ F, ‖f p.1‖ = ∑ p ∈ F.image Subtype.val, ‖f p‖ := by
        rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
      _ ≤ ∑ p ∈ (Finset.Icc 2 N).biUnion shell, ‖f p‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ k ∈ Finset.Icc 2 N, ∑ p ∈ shell k, ‖f p‖ := hbiUnion_le (Finset.Icc 2 N)
      _ ≤ ∑ k ∈ Finset.Icc 2 N, ((8 : ℝ) * k) / (k : ℝ) ^ 4 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
        calc
          ∑ p ∈ shell k, ‖f p‖
              ≤ ∑ _p ∈ shell k, (1 : ℝ) / (k : ℝ) ^ 4 :=
                Finset.sum_le_sum fun p hp => norm_inv_pow_four_le_of_mem_shell k hk1 p hp
          _ = ((shell k).card : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 4) := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((8 * k : ℕ) : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 4) := by
                gcongr
                exact_mod_cast card_shell_le k hk1
          _ = ((8 : ℝ) * k) / (k : ℝ) ^ 4 := by push_cast; ring
      _ ≤ 2 := telescoping_shell_bound N
  have htail_re : -2 ≤ (∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), f p.1).re := by
    have h1 : |(∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), f p.1).re| ≤
        ‖∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), f p.1‖ := Complex.abs_re_le_norm _
    have h2 : ‖∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), f p.1‖ ≤
        ∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), ‖f p.1‖ := norm_tsum_le_tsum_norm (hsum_norm.subtype _)
    have h3 : |(∑' p : ↑((S₁ : Set (ℤ × ℤ))ᶜ), f p.1).re| ≤ 2 := (h1.trans h2).trans htail_norm
    linarith [(abs_le.mp h3).1]
  have htot_re : 1 ≤ (∑' p : ℤ × ℤ, f p).re := by
    rw [← hsplit, Complex.add_re, hS1_re]
    linarith
  rw [hG4]
  have h16 : ((16 : ℂ)⁻¹ * ∑' p : ℤ × ℤ, f p).re = (16 : ℝ)⁻¹ * (∑' p : ℤ × ℤ, f p).re := by
    have hcast : ((16 : ℂ)⁻¹) = (((16 : ℝ)⁻¹ : ℝ) : ℂ) := by norm_num
    rw [hcast, Complex.re_ofReal_mul]
  rw [h16]
  linarith

lemma squarePeriod_one_g₂_re_pos : 0 < ((squarePeriod 1 one_pos).g₂).re := by
  simp only [PeriodPair.g₂]
  have hcast : (60 : ℂ) = ((60 : ℝ) : ℂ) := by norm_num
  rw [hcast, Complex.re_ofReal_mul]
  linarith [squarePeriod_one_G_four_re_pos]

lemma squarePeriod_one_g₂_im_zero : ((squarePeriod 1 one_pos).g₂).im = 0 := by
  simp only [PeriodPair.g₂]
  have hcast : (60 : ℂ) = ((60 : ℝ) : ℂ) := by norm_num
  rw [hcast, Complex.im_ofReal_mul, squarePeriod_G_im_zero 1 one_pos 4, mul_zero]

noncomputable def ω₀ : ℝ := (((squarePeriod 1 one_pos).g₂).re / 4) ^ (1 / 4 : ℝ)

lemma ω₀_pos : 0 < ω₀ := by
  unfold ω₀
  exact Real.rpow_pos_of_pos (div_pos squarePeriod_one_g₂_re_pos (by norm_num)) _

lemma ω₀_pow_four : ω₀ ^ 4 = ((squarePeriod 1 one_pos).g₂).re / 4 := by
  unfold ω₀
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos squarePeriod_one_g₂_re_pos (by norm_num)).le]
  norm_num

noncomputable def L₀ : PeriodPair := squarePeriod ω₀ ω₀_pos

lemma L₀_g₂ : L₀.g₂ = 4 := by
  unfold L₀
  rw [squarePeriod_g₂_scale ω₀ ω₀_pos]
  have hreal : (squarePeriod 1 one_pos).g₂ = (((squarePeriod 1 one_pos).g₂).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [squarePeriod_one_g₂_im_zero]
  rw [hreal]
  have hpow : (ω₀ : ℂ) ^ 4 = ((((squarePeriod 1 one_pos).g₂).re / 4 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ω₀_pow_four]
  rw [hpow]
  have hne : ((squarePeriod 1 one_pos).g₂).re ≠ 0 := squarePeriod_one_g₂_re_pos.ne'
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hne]

lemma L₀_g₃ : L₀.g₃ = 0 := squarePeriod_g₃ ω₀ ω₀_pos

lemma L₀_derivWeierstrassP_sq (z : ℂ) (hz : z ∉ L₀.lattice) :
    L₀.derivWeierstrassP z ^ 2 = 4 * L₀.weierstrassP z ^ 3 - 4 * L₀.weierstrassP z := by
  rw [L₀.derivWeierstrassP_sq z hz, L₀_g₂, L₀_g₃, sub_zero]

end PositivityG2

section HalfPeriodIntegral

private noncomputable def P (t : ℝ) : ℝ := (L₀.weierstrassP (t : ℂ)).re
private noncomputable def P' (t : ℝ) : ℝ := (L₀.derivWeierstrassP (t : ℂ)).re

private lemma ofReal_P (t : ℝ) : (P t : ℂ) = L₀.weierstrassP (t : ℂ) := by
  apply Complex.ext
  · simp [P]
  · simp [L₀, squarePeriod_weierstrassP_ofReal_im]

private lemma ofReal_P' (t : ℝ) : (P' t : ℂ) = L₀.derivWeierstrassP (t : ℂ) := by
  apply Complex.ext
  · simp [P']
  · simp [L₀, squarePeriod_derivWeierstrassP_ofReal_im]

private lemma hasDerivAt_P {t : ℝ} (ht : (t : ℂ) ∉ L₀.lattice) :
    HasDerivAt P (P' t) t := by
  have hdiffC : DifferentiableAt ℂ L₀.weierstrassP (t : ℂ) :=
    L₀.differentiableOn_weierstrassP.differentiableAt
      (L₀.isClosed_lattice.isOpen_compl.mem_nhds ht)
  have hderivC : HasDerivAt L₀.weierstrassP (L₀.derivWeierstrassP (t : ℂ)) (t : ℂ) := by
    rw [← L₀.deriv_weierstrassP]
    exact hdiffC.hasDerivAt
  have hcomp : HasDerivAt (fun x : ℝ => L₀.weierstrassP (x : ℂ))
      (L₀.derivWeierstrassP (t : ℂ)) t := by
    simpa using hderivC.comp_ofReal
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp

private lemma continuousOn_P_Ioo : ContinuousOn P (Set.Ioo 0 (2 * ω₀)) := fun _t ht =>
  (hasDerivAt_P (Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 ht.2)).continuousAt.continuousWithinAt

private lemma continuousOn_P'_Ioo : ContinuousOn P' (Set.Ioo 0 (2 * ω₀)) := by
  intro t ht
  have hnot : (t : ℂ) ∉ L₀.lattice := Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 ht.2
  have hdiffC : DifferentiableAt ℂ L₀.derivWeierstrassP (t : ℂ) :=
    L₀.differentiableOn_derivWeierstrassP.differentiableAt
      (L₀.isClosed_lattice.isOpen_compl.mem_nhds hnot)
  have hcont : ContinuousAt P' t :=
    Complex.continuous_re.continuousAt.comp
      (hdiffC.continuousAt.comp Complex.continuous_ofReal.continuousAt)
  exact hcont.continuousWithinAt

private lemma P'_sq {t : ℝ} (ht : (t : ℂ) ∉ L₀.lattice) :
    P' t ^ 2 = 4 * P t ^ 3 - 4 * P t := by
  have hC := L₀_derivWeierstrassP_sq (t : ℂ) ht
  rw [← ofReal_P, ← ofReal_P'] at hC
  exact_mod_cast hC

private lemma P'_half_period : P' ω₀ = 0 := by
  have h1 : L₀.derivWeierstrassP (-(ω₀ : ℂ)) = -L₀.derivWeierstrassP (ω₀ : ℂ) :=
    L₀.derivWeierstrassP_neg (ω₀ : ℂ)
  have h2 : L₀.derivWeierstrassP (-(ω₀ : ℂ) + L₀.ω₁) = L₀.derivWeierstrassP (-(ω₀ : ℂ)) :=
    L₀.derivWeierstrassP_add_coe (-(ω₀ : ℂ)) ⟨L₀.ω₁, L₀.ω₁_mem_lattice⟩
  have hadd : -(ω₀ : ℂ) + L₀.ω₁ = (ω₀ : ℂ) := by
    simp only [L₀, squarePeriod]
    ring
  rw [hadd] at h2
  have h0 : L₀.derivWeierstrassP (ω₀ : ℂ) = 0 := CharZero.eq_neg_self_iff.mp (h2.trans h1)
  simp [P', h0]

private lemma tendsto_P_zero_right : Tendsto P (𝓝[>] 0) atTop := by
  have hrew : ∀ t : ℝ, P t = (L₀.weierstrassPExcept 0 (t : ℂ)).re + (t ^ 2)⁻¹ := by
    intro t
    have h := L₀.weierstrassPExcept_add 0 (t : ℂ)
    simp only [ZeroMemClass.coe_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero,
      sub_zero, one_div] at h
    unfold P
    rw [← h, Complex.add_re]
    congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [show P = fun t : ℝ => (L₀.weierstrassPExcept 0 (t : ℂ)).re + (t ^ 2)⁻¹ from funext hrew]
  have h0 : Tendsto (fun t : ℝ => (L₀.weierstrassPExcept 0 (t : ℂ)).re) (𝓝[>] 0) (𝓝 0) := by
    have hdiff : DifferentiableAt ℂ (L₀.weierstrassPExcept 0) 0 :=
      (L₀.differentiableOn_weierstrassPExcept 0).differentiableAt
        (L₀.compl_lattice_sdiff_singleton_mem_nhds 0)
    have hcont : ContinuousAt (fun t : ℝ => (L₀.weierstrassPExcept 0 (t : ℂ)).re) 0 :=
      Complex.continuous_re.continuousAt.comp
        (hdiff.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt Complex.ofReal_zero)
    have hval : (L₀.weierstrassPExcept 0 ((0 : ℝ) : ℂ)).re = 0 := by
      rw [Complex.ofReal_zero, L₀.weierstrassPExcept_zero, Complex.zero_re]
    have ht : Tendsto (fun t : ℝ => (L₀.weierstrassPExcept 0 (t : ℂ)).re) (𝓝[>] 0)
        (𝓝 (L₀.weierstrassPExcept 0 ((0 : ℝ) : ℂ)).re) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hval] at ht
  have hinv : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) (𝓝[>] 0) atTop := by
    refine Tendsto.inv_tendsto_nhdsGT_zero ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun t ht => Set.mem_Ioi.mpr (sq_pos_of_pos (Set.mem_Ioi.mp ht))⟩
    have hcont : ContinuousAt (fun t : ℝ => t ^ 2) 0 := (continuous_pow 2).continuousAt
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact h0.add_atTop hinv

private lemma tendsto_P'_zero_right : Tendsto P' (𝓝[>] 0) atBot := by
  have hrew : ∀ t : ℝ, P' t = (L₀.derivWeierstrassPExcept 0 (t : ℂ)).re + (-(2 / t ^ 3)) := by
    intro t
    have h := L₀.derivWeierstrassPExcept_sub 0 (t : ℂ)
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    unfold P'
    rw [← h, Complex.sub_re]
    have hcast : ((2 : ℂ) / (t : ℂ) ^ 3).re = 2 / t ^ 3 := by
      rw [← Complex.ofReal_pow, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hcast]
    ring
  rw [show P' = fun t : ℝ => (L₀.derivWeierstrassPExcept 0 (t : ℂ)).re + (-(2 / t ^ 3)) from funext hrew]
  have h0 : Tendsto (fun t : ℝ => (L₀.derivWeierstrassPExcept 0 (t : ℂ)).re) (𝓝[>] 0) (𝓝 0) := by
    have hdiff : DifferentiableAt ℂ (L₀.derivWeierstrassPExcept 0) 0 :=
      (L₀.differentiableOn_derivWeierstrassPExcept 0).differentiableAt
        (L₀.compl_lattice_sdiff_singleton_mem_nhds 0)
    have hcont : ContinuousAt (fun t : ℝ => (L₀.derivWeierstrassPExcept 0 (t : ℂ)).re) 0 :=
      Complex.continuous_re.continuousAt.comp
        (hdiff.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt Complex.ofReal_zero)
    have hval : (L₀.derivWeierstrassPExcept 0 ((0 : ℝ) : ℂ)).re = 0 := by
      rw [Complex.ofReal_zero, L₀.derivWeierstrassPExcept_zero_zero, Complex.zero_re]
    have ht : Tendsto (fun t : ℝ => (L₀.derivWeierstrassPExcept 0 (t : ℂ)).re) (𝓝[>] 0)
        (𝓝 (L₀.derivWeierstrassPExcept 0 ((0 : ℝ) : ℂ)).re) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hval] at ht
  have hinv : Tendsto (fun t : ℝ => -(2 / t ^ 3)) (𝓝[>] 0) atBot := by
    rw [← tendsto_neg_atTop_iff]
    simp only [neg_neg]
    have hpow : Tendsto (fun t : ℝ => (t ^ 3)⁻¹) (𝓝[>] 0) atTop := by
      refine Tendsto.inv_tendsto_nhdsGT_zero ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, eventually_nhdsWithin_of_forall fun t ht => Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp ht) 3)⟩
      simpa using ((continuous_pow 3).continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa [div_eq_mul_inv] using hpow.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  exact h0.add_atBot hinv

private lemma one_le_P_of_mem_Ioc {t : ℝ} (ht : t ∈ Set.Ioc 0 ω₀) : 1 ≤ P t := by
  by_contra hlt
  push Not at hlt
  have hnot : (t : ℂ) ∉ L₀.lattice :=
    Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 (by linarith [ht.2, ω₀_pos])
  have hsq : 0 ≤ 4 * P t ^ 3 - 4 * P t := by
    rw [← P'_sq hnot]
    exact sq_nonneg _
  have hle0 : P t ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hfac : 4 * P t ^ 3 - 4 * P t = 4 * P t * (P t - 1) * (P t + 1) := by ring
    have hneg : 4 * P t * (P t - 1) * (P t + 1) < 0 := by
      have h1 : 0 < 4 * P t := by linarith
      have h2 : P t - 1 < 0 := by linarith
      have h3 : 0 < P t + 1 := by linarith
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 h2) h3
    linarith
  have hev := tendsto_P_zero_right.eventually (eventually_gt_atTop (1 : ℝ))
  rcases (nhdsWithin_hasBasis (nhds_basis_Ioo_pos (0 : ℝ)) _).mem_iff.mp hev with ⟨δ, hδ0, hδ⟩
  set s : ℝ := min (t / 2) (δ / 2)
  have hs0 : 0 < s := lt_min (by linarith [ht.1]) (by linarith)
  have hst : s < t := (min_le_left _ _).trans_lt (by linarith [ht.1])
  have hsδ : s < δ := (min_le_right _ _).trans_lt (by linarith)
  have hPs : 1 < P s := hδ ⟨⟨by linarith, by linarith⟩, hs0⟩
  have hcont : ContinuousOn P (Set.Icc s t) :=
    continuousOn_P_Ioo.mono fun x hx => ⟨lt_of_lt_of_le hs0 hx.1, by linarith [hx.2, ht.2, ω₀_pos]⟩
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc (P t) (P s) := ⟨by linarith, by linarith⟩
  rcases intermediate_value_Icc' hst.le hcont hmem with ⟨c, hc, hPc⟩
  have hcnot : (c : ℂ) ∉ L₀.lattice :=
    Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos (lt_of_lt_of_le hs0 hc.1)
      (by linarith [hc.2, ht.2, ω₀_pos])
  have hcsq : 0 ≤ 4 * P c ^ 3 - 4 * P c := by
    rw [← P'_sq hcnot]
    exact sq_nonneg _
  rw [hPc] at hcsq
  norm_num at hcsq

private lemma P_half_period : P ω₀ = 1 := by
  have hge : 1 ≤ P ω₀ := one_le_P_of_mem_Ioc ⟨ω₀_pos, le_rfl⟩
  have hnot : (ω₀ : ℂ) ∉ L₀.lattice :=
    Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ω₀_pos (by linarith [ω₀_pos])
  have hsq : 4 * P ω₀ ^ 3 - 4 * P ω₀ = 0 := by
    rw [← P'_sq hnot, P'_half_period]
    norm_num
  have hfac : 4 * P ω₀ * (P ω₀ - 1) * (P ω₀ + 1) = 0 := by linarith [show 4 * P ω₀ ^ 3 - 4 * P ω₀ = 4 * P ω₀ * (P ω₀ - 1) * (P ω₀ + 1) by ring]
  have h1 : 4 * P ω₀ ≠ 0 := by linarith
  have h3 : P ω₀ + 1 ≠ 0 := by linarith
  have h2 : P ω₀ - 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h12 | h3'
    · exact (mul_eq_zero.mp h12).resolve_left h1
    · exact absurd h3' h3
  linarith

private lemma deriv_derivWeierstrassP_eq_of_eventually (t₁ : ℝ)
    (ht₁0 : 0 < t₁) (ht₁2 : t₁ < 2 * ω₀)
    (hne : ∀ t ∈ Set.Ioo 0 t₁, P' t ≠ 0) :
    ∀ᶠ z in 𝓝 (t₁ : ℂ),
      deriv L₀.derivWeierstrassP z = 6 * L₀.weierstrassP z ^ 2 - 2 := by
  have hU_open : IsOpen (L₀.lattice : Set ℂ)ᶜ := L₀.isClosed_lattice.isOpen_compl
  have ht₁_mem : (t₁ : ℂ) ∈ (L₀.lattice : Set ℂ)ᶜ :=
    Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht₁0 ht₁2
  have hprod : ∀ z ∈ (L₀.lattice : Set ℂ)ᶜ,
      2 * L₀.derivWeierstrassP z * deriv L₀.derivWeierstrassP z =
        (12 * L₀.weierstrassP z ^ 2 - 4) * L₀.derivWeierstrassP z := by
    intro z hz
    have hnhds : (L₀.lattice : Set ℂ)ᶜ ∈ 𝓝 z := hU_open.mem_nhds hz
    have heq : (fun w => L₀.derivWeierstrassP w ^ 2) =ᶠ[𝓝 z]
        (fun w => 4 * L₀.weierstrassP w ^ 3 - 4 * L₀.weierstrassP w) :=
      Filter.eventually_of_mem hnhds fun w hw => L₀_derivWeierstrassP_sq w hw
    have hdL : HasDerivAt (fun w => L₀.derivWeierstrassP w ^ 2)
        (2 * L₀.derivWeierstrassP z * deriv L₀.derivWeierstrassP z) z := by
      have hd1 : DifferentiableAt ℂ L₀.derivWeierstrassP z :=
        L₀.differentiableOn_derivWeierstrassP.differentiableAt hnhds
      exact (hd1.hasDerivAt.fun_pow 2).congr_deriv (by ring)
    have hdR : HasDerivAt (fun w => 4 * L₀.weierstrassP w ^ 3 - 4 * L₀.weierstrassP w)
        ((12 * L₀.weierstrassP z ^ 2 - 4) * L₀.derivWeierstrassP z) z := by
      have hd0 : HasDerivAt L₀.weierstrassP (L₀.derivWeierstrassP z) z := by
        rw [← L₀.deriv_weierstrassP]
        exact (L₀.differentiableOn_weierstrassP.differentiableAt hnhds).hasDerivAt
      have h1 := (hd0.fun_pow 3).const_mul (4 : ℂ)
      have h2 := hd0.const_mul (4 : ℂ)
      exact (h1.fun_sub h2).congr_deriv (by ring)
    exact (hdL.congr_of_eventuallyEq heq.symm).unique hdR
  have hdiff_eq : AnalyticOnNhd ℂ
      (fun z => deriv L₀.derivWeierstrassP z - (6 * L₀.weierstrassP z ^ 2 - 2))
      (L₀.lattice : Set ℂ)ᶜ := by
    have hA1 : AnalyticOnNhd ℂ (deriv L₀.derivWeierstrassP) (L₀.lattice : Set ℂ)ᶜ :=
      (L₀.differentiableOn_derivWeierstrassP.deriv hU_open).analyticOnNhd hU_open
    have hA2 : AnalyticOnNhd ℂ L₀.weierstrassP (L₀.lattice : Set ℂ)ᶜ :=
      L₀.analyticOnNhd_weierstrassP
    exact hA1.sub ((analyticOnNhd_const.mul (hA2.pow 2)).sub analyticOnNhd_const)
  have hconn : IsPreconnected (L₀.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L₀.lattice))).2
  have hfreq : ∃ᶠ z in 𝓝[≠] (t₁ : ℂ),
      deriv L₀.derivWeierstrassP z - (6 * L₀.weierstrassP z ^ 2 - 2) = 0 := by
    rw [frequently_nhdsWithin_iff, Metric.nhds_basis_ball.frequently_iff]
    intro ε hε
    set s : ℝ := t₁ - min (t₁ / 2) (ε / 2)
    have hs0 : 0 < s := by
      have : min (t₁ / 2) (ε / 2) ≤ t₁ / 2 := min_le_left _ _
      linarith
    have hst : s < t₁ := by
      have : 0 < min (t₁ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
      linarith
    refine ⟨(s : ℂ), ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hmin : min (t₁ / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
      rw [abs_of_neg (by linarith)]
      linarith
    · have hs_not : (s : ℂ) ∉ L₀.lattice :=
        Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos hs0 (lt_trans hst ht₁2)
      have hp := hprod (s : ℂ) hs_not
      have hP'ne : L₀.derivWeierstrassP (s : ℂ) ≠ 0 := by
        rw [← ofReal_P']
        exact Complex.ofReal_ne_zero.mpr (hne s ⟨hs0, hst⟩)
      have hmul : (deriv L₀.derivWeierstrassP (s : ℂ) - (6 * L₀.weierstrassP (s : ℂ) ^ 2 - 2)) *
          (2 * L₀.derivWeierstrassP (s : ℂ)) = 0 := by
        linear_combination hp
      exact (mul_eq_zero.mp hmul).resolve_right (mul_ne_zero two_ne_zero hP'ne)
    · exact Complex.ofReal_injective.ne hst.ne
  have hall := hdiff_eq.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const hconn ht₁_mem hfreq
  filter_upwards [hU_open.mem_nhds ht₁_mem] with z hz
  exact sub_eq_zero.mp (hall hz)

private lemma first_one_eq_half_period :
    ∀ t ∈ Set.Ioo 0 ω₀, 1 < P t ∧ P' t < 0 := by
  let S : Set ℝ := {t ∈ Set.Ioc 0 ω₀ | P t = 1}
  have hS_ne : S.Nonempty := ⟨ω₀, ⟨ω₀_pos, le_rfl⟩, P_half_period⟩
  have hev := tendsto_P_zero_right.eventually (eventually_gt_atTop (2 : ℝ))
  rcases (nhdsWithin_hasBasis (nhds_basis_Ioo_pos (0 : ℝ)) _).mem_iff.mp hev with ⟨δ₀, hδ₀_pos, hδ₀⟩
  set δ : ℝ := min (δ₀ / 2) (ω₀ / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith [ω₀_pos])
  have hδ_lt : δ < ω₀ := (min_le_right _ _).trans_lt (by linarith [ω₀_pos])
  have hS_lb : ∀ t ∈ S, δ ≤ t := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have htδ₀ : t < δ₀ := hlt.trans ((min_le_left _ _).trans_lt (by linarith))
    have hgt : 2 < P t := hδ₀ ⟨⟨by linarith [ht.1.1], by linarith⟩, ht.1.1⟩
    linarith [ht.2]
  have hS_bdd : BddBelow S := ⟨δ, hS_lb⟩
  set t₁ : ℝ := sInf S
  have ht₁_ge : δ ≤ t₁ := le_csInf hS_ne hS_lb
  have ht₁_pos : 0 < t₁ := lt_of_lt_of_le hδ_pos ht₁_ge
  have ht₁_le : t₁ ≤ ω₀ := csInf_le hS_bdd ⟨⟨ω₀_pos, le_rfl⟩, P_half_period⟩
  have ht₁_mem : t₁ ∈ S := by
    have hS_eq : S = Set.Icc δ ω₀ ∩ P ⁻¹' {1} := by
      ext t
      constructor
      · intro ht
        exact ⟨⟨hS_lb t ht, ht.1.2⟩, ht.2⟩
      · rintro ⟨⟨ht1, ht2⟩, hPt⟩
        exact ⟨⟨lt_of_lt_of_le hδ_pos ht1, ht2⟩, hPt⟩
    have hclosed : IsClosed S := by
      rw [hS_eq]
      have hcont : ContinuousOn P (Set.Icc δ ω₀) :=
        continuousOn_P_Ioo.mono fun x hx =>
          ⟨lt_of_lt_of_le hδ_pos hx.1, by linarith [hx.2, ω₀_pos]⟩
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    exact hclosed.csInf_mem hS_ne hS_bdd
  have hP_gt : ∀ t ∈ Set.Ioo 0 t₁, 1 < P t := by
    intro t ht
    have hge : 1 ≤ P t := one_le_P_of_mem_Ioc ⟨ht.1, ht.2.le.trans ht₁_le⟩
    have hne : P t ≠ 1 := fun heq =>
      not_le_of_gt ht.2 (csInf_le hS_bdd ⟨⟨ht.1, ht.2.le.trans ht₁_le⟩, heq⟩)
    exact lt_of_le_of_ne hge hne.symm
  have hP'_ne : ∀ t ∈ Set.Ioo 0 t₁, P' t ≠ 0 := by
    intro t ht hzero
    have hnot : (t : ℂ) ∉ L₀.lattice :=
      Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 (by linarith [ht.2, ht₁_le, ω₀_pos])
    have hsq := P'_sq hnot
    rw [hzero] at hsq
    have hgt := hP_gt t ht
    have hfac : 4 * P t ^ 3 - 4 * P t = 4 * P t * (P t - 1) * (P t + 1) := by ring
    have hpos : 0 < 4 * P t * (P t - 1) * (P t + 1) := by
      have h1 : 0 < 4 * P t := by linarith
      have h2 : 0 < P t - 1 := by linarith
      have h3 : 0 < P t + 1 := by linarith
      exact mul_pos (mul_pos h1 h2) h3
    linarith
  have hP'_neg : ∀ t ∈ Set.Ioo 0 t₁, P' t < 0 := by
    intro t ht
    by_contra hge
    push Not at hge
    have hpos : 0 < P' t := lt_of_le_of_ne hge (hP'_ne t ht).symm
    have hev' := tendsto_P'_zero_right.eventually (eventually_lt_atBot (0 : ℝ))
    rcases (nhdsWithin_hasBasis (nhds_basis_Ioo_pos (0 : ℝ)) _).mem_iff.mp hev' with ⟨ε, hε0, hε⟩
    set s : ℝ := min (t / 2) (ε / 2)
    have hs0 : 0 < s := lt_min (by linarith [ht.1]) (by linarith)
    have hst : s < t := (min_le_left _ _).trans_lt (by linarith [ht.1])
    have hsε : s < ε := (min_le_right _ _).trans_lt (by linarith)
    have hP's : P' s < 0 := hε ⟨⟨by linarith, by linarith⟩, hs0⟩
    have hcont : ContinuousOn P' (Set.Icc s t) :=
      continuousOn_P'_Ioo.mono fun x hx =>
        ⟨lt_of_lt_of_le hs0 hx.1, by linarith [hx.2, ht.2, ht₁_le, ω₀_pos]⟩
    rcases intermediate_value_Icc hst.le hcont ⟨hP's.le, hpos.le⟩ with ⟨c, hc, hP'c⟩
    exact hP'_ne c ⟨lt_of_lt_of_le hs0 hc.1, lt_of_le_of_lt hc.2 ht.2⟩ hP'c
  suffices ht₁_eq : t₁ = ω₀ by
    rw [← ht₁_eq]
    exact fun t ht => ⟨hP_gt t ht, hP'_neg t ht⟩
  by_contra hne_ω₀
  have ht₁_lt : t₁ < ω₀ := lt_of_le_of_ne ht₁_le hne_ω₀
  have ht₁_not : (t₁ : ℂ) ∉ L₀.lattice :=
    Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht₁_pos (by linarith [ω₀_pos])
  have hP't₁ : P' t₁ = 0 := by
    have hsq := P'_sq ht₁_not
    rw [ht₁_mem.2] at hsq
    nlinarith
  have hode_nhds := deriv_derivWeierstrassP_eq_of_eventually t₁ ht₁_pos (by linarith [ω₀_pos]) hP'_ne
  let f : ℂ → ℂ := fun z => L₀.weierstrassP ((t₁ : ℂ) + z)
  let g : ℂ → ℂ := fun z => L₀.weierstrassP ((t₁ : ℂ) - z)
  let h : ℂ → ℂ := fun z => f z - g z
  have hf_an : AnalyticAt ℂ f 0 := by
    have h0 := L₀.analyticOnNhd_weierstrassP (t₁ : ℂ) ht₁_not
    have hadd : AnalyticAt ℂ (fun z : ℂ => (t₁ : ℂ) + z) 0 := analyticAt_const.add analyticAt_id
    exact h0.comp_of_eq hadd (by simp)
  have hg_an : AnalyticAt ℂ g 0 := by
    have h0 := L₀.analyticOnNhd_weierstrassP (t₁ : ℂ) ht₁_not
    have hsub : AnalyticAt ℂ (fun z : ℂ => (t₁ : ℂ) - z) 0 := analyticAt_const.sub analyticAt_id
    exact h0.comp_of_eq hsub (by simp)
  have hh_an : AnalyticAt ℂ h 0 := hf_an.sub hg_an
  have hadd_tendsto : Tendsto (fun z : ℂ => (t₁ : ℂ) + z) (𝓝 0) (𝓝 (t₁ : ℂ)) := by
    simpa using (tendsto_const_nhds (x := (t₁ : ℂ))).add (tendsto_id (x := 𝓝 (0 : ℂ)))
  have hf_dd : deriv (deriv f) =ᶠ[𝓝 0] fun z => 6 * f z ^ 2 - 2 := by
    have hnhds1 : ∀ᶠ z in 𝓝 (0 : ℂ), (t₁ : ℂ) + z ∈ (L₀.lattice : Set ℂ)ᶜ :=
      hadd_tendsto.eventually (L₀.isClosed_lattice.isOpen_compl.mem_nhds ht₁_not)
    have hnhds2 : ∀ᶠ z in 𝓝 (0 : ℂ),
        deriv L₀.derivWeierstrassP ((t₁ : ℂ) + z) = 6 * L₀.weierstrassP ((t₁ : ℂ) + z) ^ 2 - 2 :=
      hadd_tendsto.eventually hode_nhds
    have hd1 : deriv f =ᶠ[𝓝 0] fun z => L₀.derivWeierstrassP ((t₁ : ℂ) + z) := by
      filter_upwards [hnhds1] with z _
      change deriv (fun w => L₀.weierstrassP ((t₁ : ℂ) + w)) z = _
      have : (fun w => L₀.weierstrassP ((t₁ : ℂ) + w)) = (fun w => L₀.weierstrassP (w + (t₁ : ℂ))) := by
        ext w; ring_nf
      rw [this, deriv_comp_add_const, L₀.deriv_weierstrassP, add_comm]
    have hd2 : deriv (deriv f) =ᶠ[𝓝 0] fun z => deriv L₀.derivWeierstrassP ((t₁ : ℂ) + z) := by
      refine hd1.deriv.trans ?_
      filter_upwards with z
      have : (fun w => L₀.derivWeierstrassP ((t₁ : ℂ) + w)) =
          (fun w => L₀.derivWeierstrassP (w + (t₁ : ℂ))) := by
        ext w; ring_nf
      rw [this, deriv_comp_add_const, add_comm]
    exact hd2.trans hnhds2
  have hg_dd : deriv (deriv g) =ᶠ[𝓝 0] fun z => 6 * g z ^ 2 - 2 := by
    have hgf : g = fun z => f (-z) := by ext z; simp [f, g, sub_eq_add_neg]
    have hneg_tendsto : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto
    have hd1 : deriv g =ᶠ[𝓝 0] fun z => -deriv f (-z) := by
      filter_upwards with z
      rw [hgf, deriv_comp_neg]
    have hd2 : deriv (deriv g) =ᶠ[𝓝 0] fun z => deriv (deriv f) (-z) := by
      refine hd1.deriv.trans ?_
      filter_upwards with z
      change deriv (-(fun w => deriv f (-w))) z = deriv (deriv f) (-z)
      rw [deriv.neg, deriv_comp_neg, neg_neg]
    exact hd2.trans (hf_dd.comp_tendsto hneg_tendsto)
  have hh_dd : deriv (deriv h) =ᶠ[𝓝 0] fun z => 6 * (f z + g z) * h z := by
    have hdiff_f : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ f z :=
      hf_an.eventually_analyticAt.mono fun _ ha => ha.differentiableAt
    have hdiff_g : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ g z :=
      hg_an.eventually_analyticAt.mono fun _ ha => ha.differentiableAt
    have hdiff_df : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (deriv f) z :=
      hf_an.deriv.eventually_analyticAt.mono fun _ ha => ha.differentiableAt
    have hdiff_dg : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (deriv g) z :=
      hg_an.deriv.eventually_analyticAt.mono fun _ ha => ha.differentiableAt
    have hd1 : deriv h =ᶠ[𝓝 0] fun z => deriv f z - deriv g z := by
      filter_upwards [hdiff_f, hdiff_g] with z hzf hzg
      exact deriv_fun_sub hzf hzg
    have hd2 : deriv (deriv h) =ᶠ[𝓝 0] fun z => deriv (deriv f) z - deriv (deriv g) z := by
      refine hd1.deriv.trans ?_
      filter_upwards [hdiff_df, hdiff_dg] with z hzdf hzdg
      exact deriv_fun_sub hzdf hzdg
    filter_upwards [hd2, hf_dd, hg_dd] with z h1 h2 h3
    rw [h1, h2, h3]
    dsimp only [h]
    ring
  have hiter_zero : ∀ n : ℕ, iteratedDeriv n h 0 = 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      match n with
      | 0 =>
        simp [h, f, g]
      | 1 =>
        rw [iteratedDeriv_one]
        have hd : deriv h 0 = deriv f 0 - deriv g 0 :=
          deriv_fun_sub hf_an.differentiableAt hg_an.differentiableAt
        rw [hd]
        have hgf : g = fun z => f (-z) := by ext z; simp [f, g, sub_eq_add_neg]
        have hdg : deriv g 0 = -deriv f 0 := by rw [hgf, deriv_comp_neg, neg_zero]
        have hdf : deriv f 0 = L₀.derivWeierstrassP (t₁ : ℂ) := by
          change deriv (fun w => L₀.weierstrassP ((t₁ : ℂ) + w)) 0 = _
          have : (fun w => L₀.weierstrassP ((t₁ : ℂ) + w)) =
              (fun w => L₀.weierstrassP (w + (t₁ : ℂ))) := by ext w; ring_nf
          rw [this, deriv_comp_add_const, zero_add, L₀.deriv_weierstrassP]
        have hP'0 : L₀.derivWeierstrassP (t₁ : ℂ) = 0 := by
          rw [← ofReal_P', hP't₁, Complex.ofReal_zero]
        rw [hdg, hdf, hP'0]
        ring
      | m + 2 =>
        have hshift : iteratedDeriv (m + 2) h 0 = iteratedDeriv m (deriv (deriv h)) 0 := by
          rw [iteratedDeriv_succ', iteratedDeriv_succ']
        rw [hshift, hh_dd.iteratedDeriv_eq]
        have hc1 : ContDiffAt ℂ m (fun z => 6 * (f z + g z)) 0 :=
          (analyticAt_const.mul (hf_an.add hg_an)).contDiffAt.of_le le_top
        have hc2 : ContDiffAt ℂ m h 0 := hh_an.contDiffAt.of_le le_top
        rw [iteratedDeriv_fun_mul hc1 hc2]
        refine Finset.sum_eq_zero fun k hk => ?_
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hklt : m - k < m + 2 := by omega
        have hzero : iteratedDeriv (m - k) h 0 = 0 := ih (m - k) hklt
        rw [hzero, mul_zero]
  have hord_top : analyticOrderAt h 0 = ⊤ := by
    by_contra hne
    lift analyticOrderAt h 0 to ℕ using hne with m hm
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt h 0 := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh_an]
      intro i _
      exact hiter_zero i
    rw [← hm] at hle
    norm_cast at hle
    omega
  have hh_ev : ∀ᶠ z in 𝓝 (0 : ℂ), h z = 0 := analyticOrderAt_eq_top.mp hord_top
  let Λ₂ : Set ℂ := (L₀.lattice : Set ℂ) ∪ ((fun l : ℂ => 2 * (t₁ : ℂ) - l) '' (L₀.lattice : Set ℂ))
  have hΛ₂_closed : IsClosed Λ₂ := by
    refine L₀.isClosed_lattice.union ?_
    have himg : (fun l : ℂ => 2 * (t₁ : ℂ) - l) '' (L₀.lattice : Set ℂ) =
        (fun l : ℂ => 2 * (t₁ : ℂ) - l) ⁻¹' (L₀.lattice : Set ℂ) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨l, hl, rfl⟩
        simpa using hl
      · intro hx
        exact ⟨2 * (t₁ : ℂ) - x, hx, by ring⟩
    rw [himg]
    exact L₀.isClosed_lattice.preimage (continuous_const.sub continuous_id)
  have hL₀_count : (L₀.lattice : Set ℂ).Countable := by
    have : Countable L₀.lattice := countable_of_Lindelof_of_discrete (X := L₀.lattice)
    exact Set.to_countable (L₀.lattice : Set ℂ)
  have hΛ₂_count : Λ₂.Countable := hL₀_count.union (hL₀_count.image _)
  have hU_open : IsOpen Λ₂ᶜ := hΛ₂_closed.isOpen_compl
  have hU_conn : IsPreconnected Λ₂ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hΛ₂_count).2
  have ht₁_U : (t₁ : ℂ) ∈ Λ₂ᶜ := by
    rintro (h1 | ⟨l, hl, h2⟩)
    · exact ht₁_not h1
    · have : l = (t₁ : ℂ) := by linear_combination -h2
      exact ht₁_not (this ▸ hl)
  have hAn1 : AnalyticOnNhd ℂ L₀.weierstrassP Λ₂ᶜ :=
    L₀.analyticOnNhd_weierstrassP.mono fun z hz hmem => hz (Or.inl hmem)
  have hAn2 : AnalyticOnNhd ℂ (fun w => L₀.weierstrassP (2 * (t₁ : ℂ) - w)) Λ₂ᶜ := by
    intro z hz
    have h2tz : 2 * (t₁ : ℂ) - z ∉ L₀.lattice := fun hmem =>
      hz (Or.inr ⟨2 * (t₁ : ℂ) - z, hmem, by ring⟩)
    exact (L₀.analyticOnNhd_weierstrassP _ h2tz).comp (analyticAt_const.sub analyticAt_id)
  have hev_eq : L₀.weierstrassP =ᶠ[𝓝 (t₁ : ℂ)] fun w => L₀.weierstrassP (2 * (t₁ : ℂ) - w) := by
    have hshift : Tendsto (fun w : ℂ => w - (t₁ : ℂ)) (𝓝 (t₁ : ℂ)) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (t₁ : ℂ))).sub (tendsto_const_nhds (x := (t₁ : ℂ)))
    filter_upwards [hshift.eventually hh_ev] with w hw
    have hfg : f (w - (t₁ : ℂ)) = g (w - (t₁ : ℂ)) := sub_eq_zero.mp hw
    simpa [f, g, add_sub_cancel, sub_sub_eq_add_sub, two_mul] using hfg
  have hEqOn := hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 hU_conn ht₁_U hev_eq
  have h2t₁_not : ((2 * t₁ : ℝ) : ℂ) ∉ L₀.lattice :=
    Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos (by linarith) (by linarith)
  have hcont_2t₁ : ContinuousAt (fun r : ℝ => (L₀.weierstrassP (2 * (t₁ : ℂ) - (r : ℂ))).re) 0 := by
    have hdiff := L₀.differentiableOn_weierstrassP.differentiableAt
      (L₀.isClosed_lattice.isOpen_compl.mem_nhds h2t₁_not)
    have h2eq : 2 * (t₁ : ℂ) - ((0 : ℝ) : ℂ) = ((2 * t₁ : ℝ) : ℂ) := by push_cast; ring
    have hinner : ContinuousAt (fun r : ℝ => 2 * (t₁ : ℂ) - (r : ℂ)) 0 :=
      continuousAt_const.sub Complex.continuous_ofReal.continuousAt
    exact Complex.continuous_re.continuousAt.comp (hdiff.continuousAt.comp_of_eq hinner h2eq)
  have htend_rhs : Tendsto (fun r : ℝ => (L₀.weierstrassP (2 * (t₁ : ℂ) - (r : ℂ))).re)
      (𝓝[>] 0) (𝓝 (L₀.weierstrassP (2 * (t₁ : ℂ) - ((0 : ℝ) : ℂ))).re) :=
    hcont_2t₁.tendsto.mono_left nhdsWithin_le_nhds
  have hev_P_eq : P =ᶠ[𝓝[>] 0] fun r : ℝ => (L₀.weierstrassP (2 * (t₁ : ℂ) - (r : ℂ))).re := by
    have hIoo : Set.Ioo (0 : ℝ) (min t₁ (2 * ω₀ - 2 * t₁)) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (lt_min ht₁_pos (by linarith))
    filter_upwards [hIoo] with r hr
    have hr_lt_t1 : r < t₁ := hr.2.trans_le (min_le_left _ _)
    have hr_lt_2 : r < 2 * ω₀ - 2 * t₁ := hr.2.trans_le (min_le_right _ _)
    have hr_U : (r : ℂ) ∈ Λ₂ᶜ := by
      rintro (h1 | ⟨l, hl, h2⟩)
      · exact Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos hr.1 (by linarith [ω₀_pos]) h1
      · have hl_eq : l = ((2 * t₁ - r : ℝ) : ℂ) := by push_cast; linear_combination -h2
        exact Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos (by linarith) (by linarith [ht₁_lt, hr.1]) (hl_eq ▸ hl)
    have heq := hEqOn hr_U
    unfold P
    rw [heq]
  have htend_P_fin := htend_rhs.congr' hev_P_eq.symm
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_P_zero_right _ htend_P_fin

lemma integral_Ioi_eq_ω₀ :
    (∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)) = ω₀ := by
  have himg : P '' Set.Ioo 0 ω₀ = Set.Ioi 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (first_one_eq_half_period t ht).1
    · intro hx
      have hx1 : 1 < x := Set.mem_Ioi.mp hx
      have hev := tendsto_P_zero_right.eventually (eventually_gt_atTop x)
      rcases (nhdsWithin_hasBasis (nhds_basis_Ioo_pos (0 : ℝ)) _).mem_iff.mp hev with ⟨δ, hδ0, hδ⟩
      set a : ℝ := min (ω₀ / 2) (δ / 2)
      have ha0 : 0 < a := lt_min (by linarith [ω₀_pos]) (by linarith)
      have haω : a < ω₀ := (min_le_left _ _).trans_lt (by linarith [ω₀_pos])
      have haδ : a < δ := (min_le_right _ _).trans_lt (by linarith)
      have hPa : x < P a := hδ ⟨⟨by linarith, by linarith⟩, ha0⟩
      have hcont : ContinuousOn P (Set.Icc a ω₀) :=
        continuousOn_P_Ioo.mono fun t ht =>
          ⟨lt_of_lt_of_le ha0 ht.1, by linarith [ht.2, ω₀_pos]⟩
      have hmem : x ∈ Set.Icc (P ω₀) (P a) := ⟨by rw [P_half_period]; exact hx1.le, hPa.le⟩
      rcases intermediate_value_Icc' haω.le hcont hmem with ⟨t, ht, hPt⟩
      have ht_gt0 : 0 < t := lt_of_lt_of_le ha0 ht.1
      have ht_lt : t < ω₀ := by
        refine lt_of_le_of_ne ht.2 fun heq => ?_
        rw [heq, P_half_period] at hPt
        linarith
      exact ⟨t, ⟨ht_gt0, ht_lt⟩, hPt⟩
  have hanti : StrictAntiOn P (Set.Ioo 0 ω₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo 0 ω₀) ?_ ?_
    · exact continuousOn_P_Ioo.mono fun t ht => ⟨ht.1, by linarith [ht.2, ω₀_pos]⟩
    · intro t ht
      rw [interior_Ioo] at ht
      have hnot : (t : ℂ) ∉ L₀.lattice :=
        Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 (by linarith [ht.2, ω₀_pos])
      rw [(hasDerivAt_P hnot).deriv]
      exact (first_one_eq_half_period t ht).2
  have hinj : Set.InjOn P (Set.Ioo 0 ω₀) := hanti.injOn
  have hderiv : ∀ t ∈ Set.Ioo 0 ω₀, HasDerivWithinAt P (P' t) (Set.Ioo 0 ω₀) t := fun t ht =>
    (hasDerivAt_P (Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 (by linarith [ht.2, ω₀_pos]))).hasDerivWithinAt
  rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  have hcongr : (∫ t in Set.Ioo 0 ω₀, |P' t| • (1 / Real.sqrt (4 * P t ^ 3 - 4 * P t))) =
      ∫ _t in Set.Ioo 0 ω₀, (1 : ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hnot : (t : ℂ) ∉ L₀.lattice :=
      Ioo_notMem_squarePeriod_lattice ω₀ ω₀_pos ht.1 (by linarith [ht.2, ω₀_pos])
    have hP'_lt : P' t < 0 := (first_one_eq_half_period t ht).2
    have hsq : 4 * P t ^ 3 - 4 * P t = (-P' t) ^ 2 := by
      rw [← P'_sq hnot]
      ring
    have hpos : 0 < -P' t := neg_pos.mpr hP'_lt
    rw [smul_eq_mul, abs_of_neg hP'_lt, hsq, Real.sqrt_sq hpos.le, one_div, mul_inv_cancel₀ hpos.ne']
  rw [hcongr, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le ω₀_pos.le,
    sub_zero]

end HalfPeriodIntegral

section Legendre

private lemma rect_subset_compl_lattice_sdiff_zero (ω : ℝ) (hω : 0 < ω) :
    (Set.uIcc (-ω) ω ×ℂ Set.uIcc (-ω) ω) ⊆
      (((squarePeriod ω hω).lattice : Set ℂ) \ {0})ᶜ := by
  rintro z ⟨hzre, hzim⟩ ⟨hmem, hz0⟩
  rw [Set.uIcc_of_le (by linarith : -ω ≤ ω)] at hzre hzim
  simp only [Set.mem_preimage, Set.mem_Icc] at hzre hzim
  rcases (mem_squarePeriod_lattice ω hω z).mp hmem with ⟨m, n, hmn⟩
  have hre : z.re = 2 * (m : ℝ) * ω := by
    have := congrArg Complex.re hmn
    simp only [mul_re, add_re, intCast_re, intCast_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, add_im, mul_im, re_ofNat, im_ofNat] at this
    linarith
  have him : z.im = 2 * (n : ℝ) * ω := by
    have := congrArg Complex.im hmn
    simp only [mul_im, add_re, add_im, intCast_re, intCast_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, mul_re, re_ofNat, im_ofNat] at this
    linarith
  rw [hre] at hzre
  rw [him] at hzim
  have hm1 : (-1 : ℝ) < (m : ℝ) := by nlinarith [hzre.1]
  have hm2 : (m : ℝ) < 1 := by nlinarith [hzre.2]
  have hn1 : (-1 : ℝ) < (n : ℝ) := by nlinarith [hzim.1]
  have hn2 : (n : ℝ) < 1 := by nlinarith [hzim.2]
  have hm0 : m = 0 := by
    have h1 : (-1 : ℤ) < m := by exact_mod_cast hm1
    have h2 : m < (1 : ℤ) := by exact_mod_cast hm2
    omega
  have hn0 : n = 0 := by
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hn1
    have h2 : n < (1 : ℤ) := by exact_mod_cast hn2
    omega
  apply hz0
  simp [hmn, hm0, hn0]

private lemma edge_notMem_lattice_bottom (ω : ℝ) (hω : 0 < ω) (x : ℝ) :
    (x : ℂ) + (-ω : ℝ) * I ∉ (squarePeriod ω hω).lattice := by
  intro hmem
  rcases (mem_squarePeriod_lattice ω hω _).mp hmem with ⟨m, n, hmn⟩
  have him := congrArg Complex.im hmn
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero,
    zero_add, mul_re, add_re, intCast_re, intCast_im, sub_zero, re_ofNat, im_ofNat] at him
  have hn1 : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have hn2 : (n : ℝ) < 0 := by nlinarith
  have h1 : (-1 : ℤ) < n := by exact_mod_cast hn1
  have h2 : n < (0 : ℤ) := by exact_mod_cast hn2
  omega

private lemma edge_notMem_lattice_top (ω : ℝ) (hω : 0 < ω) (x : ℝ) :
    (x : ℂ) + (ω : ℝ) * I ∉ (squarePeriod ω hω).lattice := by
  intro hmem
  rcases (mem_squarePeriod_lattice ω hω _).mp hmem with ⟨m, n, hmn⟩
  have him := congrArg Complex.im hmn
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero,
    zero_add, mul_re, add_re, intCast_re, intCast_im, sub_zero, re_ofNat, im_ofNat] at him
  have hn1 : (0 : ℝ) < (n : ℝ) := by nlinarith
  have hn2 : (n : ℝ) < 1 := by nlinarith
  have h1 : (0 : ℤ) < n := by exact_mod_cast hn1
  have h2 : n < (1 : ℤ) := by exact_mod_cast hn2
  omega

private lemma edge_notMem_lattice_left (ω : ℝ) (hω : 0 < ω) (y : ℝ) :
    ((-ω : ℝ) : ℂ) + (y : ℂ) * I ∉ (squarePeriod ω hω).lattice := by
  intro hmem
  rcases (mem_squarePeriod_lattice ω hω _).mp hmem with ⟨m, n, hmn⟩
  have hre := congrArg Complex.re hmn
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_one, mul_zero, sub_zero,
    add_zero, add_im, mul_im, intCast_re, intCast_im, re_ofNat, im_ofNat] at hre
  have hm1 : (-1 : ℝ) < (m : ℝ) := by nlinarith
  have hm2 : (m : ℝ) < 0 := by nlinarith
  have h1 : (-1 : ℤ) < m := by exact_mod_cast hm1
  have h2 : m < (0 : ℤ) := by exact_mod_cast hm2
  omega

private lemma edge_notMem_lattice_right (ω : ℝ) (hω : 0 < ω) (y : ℝ) :
    ((ω : ℝ) : ℂ) + (y : ℂ) * I ∉ (squarePeriod ω hω).lattice := by
  intro hmem
  rcases (mem_squarePeriod_lattice ω hω _).mp hmem with ⟨m, n, hmn⟩
  have hre := congrArg Complex.re hmn
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_one, mul_zero, sub_zero,
    add_zero, add_im, mul_im, intCast_re, intCast_im, re_ofNat, im_ofNat] at hre
  have hm1 : (0 : ℝ) < (m : ℝ) := by nlinarith
  have hm2 : (m : ℝ) < 1 := by nlinarith
  have h1 : (0 : ℤ) < m := by exact_mod_cast hm1
  have h2 : m < (1 : ℤ) := by exact_mod_cast hm2
  omega

private lemma integral_two_mul_div_sq_add_sq (ω : ℝ) (hω : 0 < ω) :
    (∫ x in -ω..ω, 2 * ω / (x ^ 2 + ω ^ 2)) = Real.pi := by
  have hderiv : ∀ x ∈ Set.uIcc (-ω) ω,
      HasDerivAt (fun t : ℝ => 2 * Real.arctan (t / ω)) (2 * ω / (x ^ 2 + ω ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / ω) (1 / ω) x := (hasDerivAt_id x).div_const ω
    have h2 := (Real.hasDerivAt_arctan (x / ω)).comp x h1
    have h3 : HasDerivAt (fun t : ℝ => 2 * Real.arctan (t / ω))
        (2 * (1 / (1 + (x / ω) ^ 2) * (1 / ω))) x := h2.const_mul (2 : ℝ)
    refine h3.congr_deriv ?_
    have hpos : 0 < x ^ 2 + ω ^ 2 := by positivity
    have h1pos : 0 < 1 + (x / ω) ^ 2 := by positivity
    field_simp [hω.ne', hpos.ne', h1pos.ne']
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 2 * ω / (x ^ 2 + ω ^ 2)) volume (-ω) ω := by
    refine ContinuousOn.intervalIntegrable ?_
    refine Continuous.continuousOn ?_
    exact continuous_const.div ((continuous_pow 2).add continuous_const) (fun x => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [div_self hω.ne', neg_div, div_self hω.ne', Real.arctan_neg, Real.arctan_one]
  ring

lemma legendre_relation (ω : ℝ) (hω : 0 < ω) :
    let L := squarePeriod ω hω
    let η : ℝ := (weierstrassZeta L (ω : ℂ)).re
    ω * η = Real.pi / 4 := by
  intro L η
  have hη_eq : (η : ℂ) = weierstrassZeta L (ω : ℂ) := by
    apply Complex.ext
    · simp [η]
    · simp [L, squarePeriod_weierstrassZeta_ofReal_im]
  let z₀ : ℂ := (-ω : ℝ) + (-ω : ℝ) * I
  let w₀ : ℂ := (ω : ℝ) + (ω : ℝ) * I
  have hz₀_re : z₀.re = -ω := by simp [z₀]
  have hz₀_im : z₀.im = -ω := by simp [z₀]
  have hw₀_re : w₀.re = ω := by simp [w₀]
  have hw₀_im : w₀.im = ω := by simp [w₀]
  have hdiff : DifferentiableOn ℂ (weierstrassZetaExcept L 0)
      (Set.uIcc z₀.re w₀.re ×ℂ Set.uIcc z₀.im w₀.im) := by
    rw [hz₀_re, hz₀_im, hw₀_re, hw₀_im]
    exact (differentiableOn_weierstrassZetaExcept L 0).mono
      (rect_subset_compl_lattice_sdiff_zero ω hω)
  have hcg := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (weierstrassZetaExcept L 0) z₀ w₀ hdiff
  simp only [hz₀_re, hz₀_im, hw₀_re, hw₀_im, smul_eq_mul] at hcg
  have hfun : weierstrassZetaExcept L 0 = fun z : ℂ => weierstrassZeta L z - z⁻¹ := by
    ext z; exact (weierstrassZeta_sub_inv L z).symm
  rw [hfun] at hcg
  have hζ_cont : ∀ g : ℝ → ℂ, Continuous g → (∀ t, g t ∉ L.lattice) →
      IntervalIntegrable (fun t => weierstrassZeta L (g t)) volume (-ω) ω := by
    intro g hg hnot
    refine Continuous.intervalIntegrable ?_ _ _
    rw [continuous_iff_continuousAt]
    intro t
    have hdiff_at := (differentiableOn_weierstrassZeta L).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds (hnot t))
    exact hdiff_at.continuousAt.comp hg.continuousAt
  have hinv_cont : ∀ g : ℝ → ℂ, Continuous g → (∀ t, g t ≠ 0) →
      IntervalIntegrable (fun t => (g t)⁻¹) volume (-ω) ω := by
    intro g hg hne
    exact (hg.inv₀ hne).intervalIntegrable _ _
  have hnot_bot : ∀ x : ℝ, (x : ℂ) + (-ω : ℝ) * I ∉ L.lattice := edge_notMem_lattice_bottom ω hω
  have hnot_top : ∀ x : ℝ, (x : ℂ) + (ω : ℝ) * I ∉ L.lattice := edge_notMem_lattice_top ω hω
  have hnot_left : ∀ y : ℝ, ((-ω : ℝ) : ℂ) + (y : ℂ) * I ∉ L.lattice := edge_notMem_lattice_left ω hω
  have hnot_right : ∀ y : ℝ, ((ω : ℝ) : ℂ) + (y : ℂ) * I ∉ L.lattice := edge_notMem_lattice_right ω hω
  have hne_bot : ∀ x : ℝ, (x : ℂ) + (-ω : ℝ) * I ≠ 0 := fun x h => hnot_bot x (h.symm ▸ zero_mem _)
  have hne_top : ∀ x : ℝ, (x : ℂ) + (ω : ℝ) * I ≠ 0 := fun x h => hnot_top x (h.symm ▸ zero_mem _)
  have hne_left : ∀ y : ℝ, ((-ω : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun y h => hnot_left y (h.symm ▸ zero_mem _)
  have hne_right : ∀ y : ℝ, ((ω : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun y h => hnot_right y (h.symm ▸ zero_mem _)
  have hc_bot : Continuous (fun x : ℝ => (x : ℂ) + (-ω : ℝ) * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hc_top : Continuous (fun x : ℝ => (x : ℂ) + (ω : ℝ) * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hc_left : Continuous (fun y : ℝ => ((-ω : ℝ) : ℂ) + (y : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hc_right : Continuous (fun y : ℝ => ((ω : ℝ) : ℂ) + (y : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hζ_bot := hζ_cont _ hc_bot hnot_bot
  have hζ_top := hζ_cont _ hc_top hnot_top
  have hζ_left := hζ_cont _ hc_left hnot_left
  have hζ_right := hζ_cont _ hc_right hnot_right
  have hi_bot := hinv_cont _ hc_bot hne_bot
  have hi_top := hinv_cont _ hc_top hne_top
  have hi_left := hinv_cont _ hc_left hne_left
  have hi_right := hinv_cont _ hc_right hne_right
  rw [intervalIntegral.integral_sub hζ_bot hi_bot,
      intervalIntegral.integral_sub hζ_top hi_top,
      intervalIntegral.integral_sub hζ_right hi_right,
      intervalIntegral.integral_sub hζ_left hi_left] at hcg
  have hper1 : ∀ z, z ∉ L.lattice → weierstrassZeta L (z + 2 * (ω : ℂ)) =
      weierstrassZeta L z + 2 * (η : ℂ) := by
    intro z hz
    have h := weierstrassZeta_add_coe L ⟨L.ω₁, L.ω₁_mem_lattice⟩ L.ω₁_div_two_notMem_lattice hz
    dsimp only at h
    have h1 : L.ω₁ = 2 * (ω : ℂ) := rfl
    have h2 : L.ω₁ / 2 = (ω : ℂ) := by rw [h1]; ring
    rw [h2, h1, ← hη_eq] at h
    exact h
  have hper2 : ∀ z, z ∉ L.lattice → weierstrassZeta L (z + 2 * (ω : ℂ) * I) =
      weierstrassZeta L z - 2 * (η : ℂ) * I := by
    intro z hz
    have h := weierstrassZeta_add_coe L ⟨L.ω₂, L.ω₂_mem_lattice⟩ L.ω₂_div_two_notMem_lattice hz
    dsimp only at h
    have h1 : L.ω₂ = 2 * (ω : ℂ) * I := rfl
    have h2 : L.ω₂ / 2 = I * (ω : ℂ) := by rw [h1]; ring
    rw [h2, h1, squarePeriod_weierstrassZeta_mul_I ω hω (ω : ℂ), ← hη_eq] at h
    linear_combination h
  have hζ_horiz :
      (∫ x in -ω..ω, weierstrassZeta L ((x : ℂ) + (-ω : ℝ) * I)) -
      (∫ x in -ω..ω, weierstrassZeta L ((x : ℂ) + (ω : ℝ) * I)) =
        4 * (ω : ℂ) * (η : ℂ) * I := by
    rw [← intervalIntegral.integral_sub hζ_bot hζ_top]
    have heq : (fun x : ℝ => weierstrassZeta L ((x : ℂ) + (-ω : ℝ) * I) -
        weierstrassZeta L ((x : ℂ) + (ω : ℝ) * I)) = fun _ => 2 * (η : ℂ) * I := by
      ext x
      have hshift : ((x : ℂ) + (ω : ℝ) * I) =
          ((x : ℂ) + (-ω : ℝ) * I) + 2 * (ω : ℂ) * I := by push_cast; ring
      rw [hshift, hper2 _ (hnot_bot x)]
      ring
    rw [heq, intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  have hζ_vert :
      (∫ y in -ω..ω, weierstrassZeta L (((ω : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y in -ω..ω, weierstrassZeta L (((-ω : ℝ) : ℂ) + (y : ℂ) * I)) =
        4 * (ω : ℂ) * (η : ℂ) := by
    rw [← intervalIntegral.integral_sub hζ_right hζ_left]
    have heq : (fun y : ℝ => weierstrassZeta L (((ω : ℝ) : ℂ) + (y : ℂ) * I) -
        weierstrassZeta L (((-ω : ℝ) : ℂ) + (y : ℂ) * I)) = fun _ => 2 * (η : ℂ) := by
      ext y
      have hshift : (((ω : ℝ) : ℂ) + (y : ℂ) * I) =
          (((-ω : ℝ) : ℂ) + (y : ℂ) * I) + 2 * (ω : ℂ) := by push_cast; ring
      rw [hshift, hper1 _ (hnot_left y)]
      ring
    rw [heq, intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  have hinv_horiz :
      (∫ x in -ω..ω, ((x : ℂ) + (-ω : ℝ) * I)⁻¹) -
      (∫ x in -ω..ω, ((x : ℂ) + (ω : ℝ) * I)⁻¹) = (Real.pi : ℂ) * I := by
    rw [← intervalIntegral.integral_sub hi_bot hi_top]
    have heq : (fun x : ℝ => ((x : ℂ) + (-ω : ℝ) * I)⁻¹ - ((x : ℂ) + (ω : ℝ) * I)⁻¹) =
        fun x : ℝ => ((2 * ω / (x ^ 2 + ω ^ 2) : ℝ) : ℂ) * I := by
      ext x
      have hden_r : (x : ℝ) ^ 2 + ω ^ 2 ≠ 0 := by positivity
      have hden : (x : ℂ) ^ 2 + (ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden_r
      have hbot : (x : ℂ) - (ω : ℂ) * I ≠ 0 := by
        simpa [Complex.ofReal_neg, sub_eq_add_neg] using hne_bot x
      have htop : (x : ℂ) + (ω : ℂ) * I ≠ 0 := hne_top x
      have hrew : ((x : ℂ) + (-ω : ℝ) * I) = (x : ℂ) - (ω : ℂ) * I := by push_cast; ring
      rw [hrew]
      push_cast
      field_simp [hbot, htop, hden]
      linear_combination (2 * (ω : ℂ) * I) * ((ω : ℂ) ^ 2 * I_sq)
    rw [heq, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      integral_two_mul_div_sq_add_sq ω hω]
  have hinv_vert :
      (∫ y in -ω..ω, (((ω : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) -
      (∫ y in -ω..ω, (((-ω : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) = (Real.pi : ℂ) := by
    rw [← intervalIntegral.integral_sub hi_right hi_left]
    have heq : (fun y : ℝ => (((ω : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ - (((-ω : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) =
        fun y : ℝ => ((2 * ω / (y ^ 2 + ω ^ 2) : ℝ) : ℂ) := by
      ext y
      have hden_r : (y : ℝ) ^ 2 + ω ^ 2 ≠ 0 := by positivity
      have hden : (y : ℂ) ^ 2 + (ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden_r
      have hleft : -(ω : ℂ) + (y : ℂ) * I ≠ 0 := by
        simpa [Complex.ofReal_neg] using hne_left y
      have hright : (ω : ℂ) + (y : ℂ) * I ≠ 0 := hne_right y
      have hrew : (((-ω : ℝ) : ℂ) + (y : ℂ) * I) = -(ω : ℂ) + (y : ℂ) * I := by push_cast; ring
      rw [hrew]
      push_cast
      field_simp [hright, hleft, hden]
      linear_combination -(2 * (ω : ℂ)) * ((y : ℂ) ^ 2 * I_sq)
    rw [heq, intervalIntegral.integral_ofReal, integral_two_mul_div_sq_add_sq ω hω]
  have hfinalC : 8 * (ω : ℂ) * (η : ℂ) * I = 2 * (Real.pi : ℂ) * I := by
    linear_combination hcg - hζ_horiz - I * hζ_vert + hinv_horiz + I * hinv_vert
  have him := congrArg Complex.im hfinalC
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    add_zero, re_ofNat, im_ofNat] at him
  linarith

end Legendre

end WeierstrassLemniscate

theorem OMA.solution : OMA.R_Constant7b_irrational_gamma_one_div_four_R1.H1 := by
  unfold OMA.R_Constant7b_irrational_gamma_one_div_four_R1.H1
  intro ω₁ Λ
  have hω_eq : ω₁ = WeierstrassLemniscate.ω₀ := WeierstrassLemniscate.integral_Ioi_eq_ω₀
  have hΛ_eq : Λ = (WeierstrassLemniscate.L₀.lattice : Set ℂ) := by
    ext w
    change (∃ m n : ℤ, w = (2 * (m : ℂ) + 2 * (n : ℂ) * I) * (ω₁ : ℂ)) ↔
      w ∈ WeierstrassLemniscate.L₀.lattice
    rw [hω_eq]
    exact (WeierstrassLemniscate.mem_squarePeriod_lattice
      WeierstrassLemniscate.ω₀ WeierstrassLemniscate.ω₀_pos w).symm
  refine ⟨WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀,
    (WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
      (WeierstrassLemniscate.ω₀ : ℂ)).re, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hΛ_eq] at hz
    exact (WeierstrassLemniscate.differentiableOn_weierstrassZeta
      WeierstrassLemniscate.L₀).differentiableAt
      (WeierstrassLemniscate.L₀.isClosed_lattice.isOpen_compl.mem_nhds hz)
  · exact WeierstrassLemniscate.tendsto_weierstrassZeta_sub_inv WeierstrassLemniscate.L₀
  · intro z hz
    rw [hΛ_eq] at hz
    rw [hω_eq]
    have hη_eq : ((WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
        (WeierstrassLemniscate.ω₀ : ℂ)).re : ℂ) =
        WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
          (WeierstrassLemniscate.ω₀ : ℂ) := by
      apply Complex.ext
      · simp
      · simp [WeierstrassLemniscate.L₀,
          WeierstrassLemniscate.squarePeriod_weierstrassZeta_ofReal_im]
    have h := WeierstrassLemniscate.weierstrassZeta_add_coe WeierstrassLemniscate.L₀
      ⟨WeierstrassLemniscate.L₀.ω₁, WeierstrassLemniscate.L₀.ω₁_mem_lattice⟩
      WeierstrassLemniscate.L₀.ω₁_div_two_notMem_lattice hz
    dsimp only at h
    have h1 : WeierstrassLemniscate.L₀.ω₁ = 2 * (WeierstrassLemniscate.ω₀ : ℂ) := rfl
    have h2 : WeierstrassLemniscate.L₀.ω₁ / 2 = (WeierstrassLemniscate.ω₀ : ℂ) := by
      rw [h1]; ring
    rw [h2, h1, ← hη_eq] at h
    exact h
  · intro z hz
    rw [hΛ_eq] at hz
    rw [hω_eq]
    have hη_eq : ((WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
        (WeierstrassLemniscate.ω₀ : ℂ)).re : ℂ) =
        WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
          (WeierstrassLemniscate.ω₀ : ℂ) := by
      apply Complex.ext
      · simp
      · simp [WeierstrassLemniscate.L₀,
          WeierstrassLemniscate.squarePeriod_weierstrassZeta_ofReal_im]
    have h := WeierstrassLemniscate.weierstrassZeta_add_coe WeierstrassLemniscate.L₀
      ⟨WeierstrassLemniscate.L₀.ω₂, WeierstrassLemniscate.L₀.ω₂_mem_lattice⟩
      WeierstrassLemniscate.L₀.ω₂_div_two_notMem_lattice hz
    dsimp only at h
    have h1 : WeierstrassLemniscate.L₀.ω₂ = 2 * (WeierstrassLemniscate.ω₀ : ℂ) * I := rfl
    have h2 : WeierstrassLemniscate.L₀.ω₂ / 2 = I * (WeierstrassLemniscate.ω₀ : ℂ) := by
      rw [h1]; ring
    have hmulI : WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
        (I * (WeierstrassLemniscate.ω₀ : ℂ)) =
        -I * WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀
          (WeierstrassLemniscate.ω₀ : ℂ) :=
      WeierstrassLemniscate.squarePeriod_weierstrassZeta_mul_I
        WeierstrassLemniscate.ω₀ WeierstrassLemniscate.ω₀_pos
        (WeierstrassLemniscate.ω₀ : ℂ)
    rw [h2, h1, hmulI, ← hη_eq] at h
    linear_combination h
  · intro z hz
    rw [hΛ_eq] at hz
    have hP_eq : ∀ w ∈ (WeierstrassLemniscate.L₀.lattice : Set ℂ)ᶜ,
        -deriv (WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀) w =
          WeierstrassLemniscate.L₀.weierstrassP w := by
      intro w hw
      rw [WeierstrassLemniscate.eqOn_deriv_weierstrassZeta WeierstrassLemniscate.L₀ hw, neg_neg]
    have hP_z : -deriv (WeierstrassLemniscate.weierstrassZeta WeierstrassLemniscate.L₀) z =
        WeierstrassLemniscate.L₀.weierstrassP z := hP_eq z hz
    have hP_ev : (fun w => -deriv (WeierstrassLemniscate.weierstrassZeta
        WeierstrassLemniscate.L₀) w) =ᶠ[𝓝 z] WeierstrassLemniscate.L₀.weierstrassP :=
      Filter.eventually_of_mem
        (WeierstrassLemniscate.L₀.isClosed_lattice.isOpen_compl.mem_nhds hz) hP_eq
    have hd_z : deriv (fun w => -deriv (WeierstrassLemniscate.weierstrassZeta
        WeierstrassLemniscate.L₀) w) z = WeierstrassLemniscate.L₀.derivWeierstrassP z := by
      rw [hP_ev.deriv_eq, WeierstrassLemniscate.L₀.deriv_weierstrassP]
    dsimp only
    rw [hd_z, hP_z]
    exact WeierstrassLemniscate.L₀_derivWeierstrassP_sq z hz
  · rw [hω_eq]
    exact WeierstrassLemniscate.legendre_relation WeierstrassLemniscate.ω₀
      WeierstrassLemniscate.ω₀_pos
