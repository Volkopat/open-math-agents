import OMAStatements.S_mo_61882

/-!
Adapted from @romechenko’s merged PR #17061, head
b68b8bedc62ce94f0d7a8cb0e1258a5d74cb231d. The original mathematical credits
are retained below. Standard exponential strip injectivity replaces the explicit
integer-period argument, and the derivative composition is normalized directly.
-/

open Filter Metric Set
open scoped Topology

namespace MO61882

private noncomputable def F (z : ℂ) : ℂ := Complex.exp z⁻¹

private noncomputable def dF (z : ℂ) : ℂ := -(Complex.exp z⁻¹) / z ^ 2

private theorem hasDeriv_F {z : ℂ} (hz : z ≠ 0) : HasDerivAt F (dF z) z := by
  convert! ((hasDerivAt_id z).inv hz).cexp using 1
  simp [dF, ← mul_div_assoc]

private def disk : Set ℂ := ball 0 1 \ {0}

private def cell (c : Fin 2 × Fin 2) (a : ℤ × ℤ) : Set ℂ :=
  {z ∈ disk | |z⁻¹.re - (2 * (a.1 : ℝ) + c.1.val)| < 3 / 4 ∧
               |z⁻¹.im - (2 * (a.2 : ℝ) + c.2.val)| < 3 / 4}

private theorem cell_open (c : Fin 2 × Fin 2) (a : ℤ × ℤ) : IsOpen (cell c a) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨hz, hre, him⟩
  have hz0 : z ≠ 0 := hz.2
  have hi : ContinuousAt (fun x : ℂ => x⁻¹) z := continuousAt_inv₀ hz0
  have hr : ContinuousAt (fun x : ℂ => |x⁻¹.re - (2 * (a.1 : ℝ) + c.1.val)|) z :=
    ((Complex.continuous_re.continuousAt.comp hi).sub continuousAt_const).abs
  have hs : ContinuousAt (fun x : ℂ => |x⁻¹.im - (2 * (a.2 : ℝ) + c.2.val)|) z :=
    ((Complex.continuous_im.continuousAt.comp hi).sub continuousAt_const).abs
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hz,
    hr.eventually_lt continuousAt_const hre, hs.eventually_lt continuousAt_const him]
    with w hw hwr hwi using ⟨hw, hwr, hwi⟩

private theorem small_dbl_diff {a b : ℤ} {u v : ℝ}
    (ha : |u - (2 * (a : ℝ) + v)| < 3 / 4)
    (hb : |u - (2 * (b : ℝ) + v)| < 3 / 4) : a = b := by
  rw [abs_lt] at ha hb
  have h₁ : (a : ℝ) < (b : ℝ) + 1 := by linarith
  have h₂ : (b : ℝ) < (a : ℝ) + 1 := by linarith
  exact le_antisymm (Int.lt_add_one_iff.mp (by exact_mod_cast h₁))
    (Int.lt_add_one_iff.mp (by exact_mod_cast h₂))

private theorem cell_unique {c : Fin 2 × Fin 2} {a b : ℤ × ℤ} {z : ℂ}
    (ha : z ∈ cell c a) (hb : z ∈ cell c b) : a = b :=
  Prod.ext (small_dbl_diff ha.2.1 hb.2.1) (small_dbl_diff ha.2.2 hb.2.2)

private theorem close_center (x : ℝ) :
    ∃ (a : ℤ) (c : Fin 2), |x - (2 * (a : ℝ) + c.val)| < 3 / 4 := by
  let t := ⌊x + 1 / 2⌋
  let c : Fin 2 := ⟨(t % 2).toNat, by omega⟩
  have ht : (t : ℝ) = 2 * ((t / 2 : ℤ) : ℝ) + c.val := by
    have ht' : t = 2 * (t / 2) + (c.val : ℤ) := by
      dsimp [c]
      omega
    exact_mod_cast ht'
  refine ⟨t / 2, c, ?_⟩
  rw [← ht, abs_lt]
  have hl := Int.floor_le (x + 1 / 2)
  have hu := Int.lt_floor_add_one (x + 1 / 2)
  change (t : ℝ) ≤ x + 1 / 2 at hl
  change x + 1 / 2 < (t : ℝ) + 1 at hu
  constructor <;> linarith

private def U (j : Fin 4) : Set ℂ := ⋃ a : ℤ × ℤ, cell (finProdFinEquiv.symm j) a

private theorem U_open (j : Fin 4) : IsOpen (U j) :=
  isOpen_iUnion fun a => cell_open _ a

private theorem cover : (⋃ j : Fin 4, U j) = disk := by
  ext z
  constructor
  · simp only [mem_iUnion, U]
    rintro ⟨j, a, ha⟩
    exact ha.1
  · intro hz
    obtain ⟨a, c, hc⟩ := close_center z⁻¹.re
    obtain ⟨b, e, he⟩ := close_center z⁻¹.im
    apply mem_iUnion.mpr
    refine ⟨finProdFinEquiv (c, e), mem_iUnion.mpr ⟨(a, b), ?_⟩⟩
    simpa only [Equiv.symm_apply_apply] using
      (show z ∈ cell (c, e) (a, b) from ⟨hz, hc, he⟩)

-- The standard exponential strip theorem replaces the explicit integer-period case split.
private theorem F_inj {c : Fin 2 × Fin 2} {a : ℤ × ℤ} : InjOn F (cell c a) := by
  intro x hx y hy heq
  change Complex.exp x⁻¹ = Complex.exp y⁻¹ at heq
  have hb : -Real.pi < (x⁻¹-y⁻¹).im ∧ (x⁻¹-y⁻¹).im ≤ Real.pi := by
    simp only [Complex.sub_im]
    constructor <;> linarith [abs_lt.mp hx.2.2, abs_lt.mp hy.2.2, Real.pi_gt_three]
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi (y := 0) hb.1 hb.2
    (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)
    (by simpa using Complex.exp_eq_exp_iff_exp_sub_eq_one.mp heq)
  exact inv_injective (sub_eq_zero.mp he)

private noncomputable def radius (c : Fin 2 × Fin 2) (m : ℕ) : ℝ :=
  Real.exp (2 * (((Encodable.decode (α := ℤ × ℤ) m).getD (0, 0)).1 : ℝ) + c.1.val + 1)

private noncomputable def endpoint (c : Fin 2 × Fin 2) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, 2 * radius c k

private theorem endpoint_succ (c : Fin 2 × Fin 2) (m : ℕ) :
    endpoint c (m + 1) = endpoint c m + 2 * radius c m := by
  simp only [endpoint, Finset.sum_range_succ]

private theorem endpoint_mono (c : Fin 2 × Fin 2) : Monotone (endpoint c) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [endpoint_succ]
  exact le_add_of_nonneg_right (by unfold radius; positivity)

private noncomputable def shift (c : Fin 2 × Fin 2) (a : ℤ × ℤ) : ℂ :=
  let m := Encodable.encode a
  (endpoint c m + radius c m : ℝ)

private theorem shifted_bounds {c : Fin 2 × Fin 2} {a : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell c a) :
    let m := Encodable.encode a
    endpoint c m < (F z + shift c a).re ∧
    (F z + shift c a).re < endpoint c (m + 1) := by
  dsimp only
  have hnorm : ‖F z‖ < radius c (Encodable.encode a) := by
    rw [F, Complex.norm_exp, radius, Encodable.encodek]
    change Real.exp (z⁻¹).re < Real.exp (2 * (a.1 : ℝ) + c.1.val + 1)
    exact Real.exp_lt_exp.mpr (by linarith [abs_lt.mp hz.2.1])
  have hre := Complex.abs_re_le_norm (F z)
  have hb := abs_lt.mp (lt_of_le_of_lt hre hnorm)
  simp only [shift, Complex.add_re, Complex.ofReal_re, endpoint_succ]
  constructor <;> linarith

private noncomputable def index (c : Fin 2 × Fin 2) (z : ℂ) : ℤ × ℤ := by
  classical
  exact if h : ∃ a : ℤ × ℤ, z ∈ cell c a then Classical.choose h else (0, 0)

private theorem index_eq {c : Fin 2 × Fin 2} {a : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell c a) :
    index c z = a := by
  classical
  rw [index, dif_pos ⟨a, hz⟩]
  exact cell_unique (Classical.choose_spec (show ∃ b, z ∈ cell c b from ⟨a, hz⟩)) hz

private noncomputable def f (j : Fin 4) (z : ℂ) : ℂ :=
  let c : Fin 2 × Fin 2 := finProdFinEquiv.symm j
  F z + shift c (index c z)

private theorem f_eq {j : Fin 4} {a : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell (finProdFinEquiv.symm j) a) :
    f j z = F z + shift (finProdFinEquiv.symm j) a := by
  rw [f, index_eq hz]

private theorem f_inj (j : Fin 4) : InjOn (f j) (U j) := by
  intro x hx y hy hxy
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  obtain ⟨b, hb⟩ := mem_iUnion.mp hy
  rw [f_eq ha, f_eq hb] at hxy
  have hr := congrArg Complex.re hxy
  have hxa := shifted_bounds ha
  have hyb := shifted_bounds hb
  have hab : Encodable.encode a = Encodable.encode b := by
    rcases lt_trichotomy (Encodable.encode a) (Encodable.encode b) with hlt | he | hgt
    · have hp := endpoint_mono (finProdFinEquiv.symm j) (Nat.succ_le_of_lt hlt)
      linarith [hxa.2, hyb.1]
    · exact he
    · have hp := endpoint_mono (finProdFinEquiv.symm j) (Nat.succ_le_of_lt hgt)
      linarith [hxa.1, hyb.2]
  obtain rfl := Encodable.encode_injective hab
  exact F_inj ha hb (add_right_cancel hxy)

private theorem hasDeriv_f {j : Fin 4} {z : ℂ} (hz : z ∈ U j) :
    HasDerivAt (f j) (dF z) z := by
  obtain ⟨a, ha⟩ := mem_iUnion.mp hz
  refine ((hasDeriv_F ha.1.2).add_const (shift (finProdFinEquiv.symm j) a)).congr_of_eventuallyEq ?_
  filter_upwards [(cell_open _ a).mem_nhds ha] with w hw using f_eq hw

private theorem no_meromorphic_glue {g : ℂ → ℂ} (hg : MeromorphicAt g 0)
    (hd : EqOn g dF disk) : False := by
  obtain ⟨n, hn⟩ := hg
  have hinv : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  let C := ‖((0 : ℂ) - 0) ^ n • g 0‖ + 1
  have hC := (hn.continuousAt.norm.tendsto.comp hinv).eventually
    (eventually_lt_nhds (show ‖((0 : ℂ) - 0) ^ n • g 0‖ < C from lt_add_one _))
  have hbig := (tendsto_atTop.1 (Real.tendsto_exp_div_pow_atTop n)) (C + 1)
  have hlarge : ∀ᶠ t : ℝ in atTop, 1 < t := eventually_gt_atTop 1
  obtain ⟨t, ht, hCt, hbt⟩ := (hlarge.and (hC.and hbig)).exists
  have ht0 : 0 < t := by linarith
  let z : ℂ := ((t⁻¹ : ℝ) : ℂ)
  have hz : z ∈ disk := by
    refine ⟨?_, ?_⟩
    · change dist z 0 < 1
      rw [dist_zero_right]
      simpa [z, abs_of_pos ht0] using (inv_lt_one_of_one_lt₀ ht)
    · simpa [z] using (ne_of_gt ht0)
  have hnorm : ‖(z - 0) ^ n • g z‖ = Real.exp t / t ^ n * t ^ 2 := by
    rw [hd hz]
    simp [dF, z, Complex.norm_exp, abs_of_pos ht0, inv_pow, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  change ‖(z - 0) ^ n • g z‖ < C at hCt
  rw [hnorm] at hCt
  have hpos : 0 ≤ Real.exp t / t ^ n := by positivity
  have hsq : 1 ≤ t ^ 2 := by nlinarith
  have hle : Real.exp t / t ^ n ≤ Real.exp t / t ^ n * t ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left hsq hpos
  linarith

end MO61882

/-- Translations on separate components give injective primitives of an essential differential.
The disconnected example is due to the MathOverflow discussion by Goodwillie, Thurston and Mali. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_61882.main) := by
  intro h
  obtain ⟨g, hmero, hderiv⟩ := h 4 MO61882.U MO61882.f
    MO61882.U_open MO61882.cover (fun j z hz => (MO61882.hasDeriv_f hz).differentiableAt.differentiableWithinAt)
    MO61882.f_inj (fun j k z hz => (MO61882.hasDeriv_f hz.1).deriv.trans (MO61882.hasDeriv_f hz.2).deriv.symm)
  apply MO61882.no_meromorphic_glue hmero
  intro z hz
  rw [← MO61882.cover] at hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  exact (hderiv j z hj).trans (MO61882.hasDeriv_f hj).deriv
