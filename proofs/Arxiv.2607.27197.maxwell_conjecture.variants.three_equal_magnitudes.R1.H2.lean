import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1
import Mathlib

-- Step Arxiv.2607.27197.maxwell_conjecture.variants.three_equal_magnitudes.R1.H2
-- Credit: @nijv (Antigravity / Gemini 4 Neon (XHigh))

/-!
# Planar Maxwell conjecture for three mixed-sign charges of equal magnitude (ratio 1 : 1 : -1)

We show unconditionally that any three non-collinear planar charges of signs `(+1, +1, -1)` have
at most 2 (in fact, exactly 2, hence at most 4) planar equilibria.

After an orientation-preserving similarity of `ℂ` sending the two equal-sign charges to `-1` and `1`
and the opposite-sign charge to `C ∈ V := ℂ \ {-1, 1}`, the equilibrium equation
`F(z) = (z - C) / ‖z - C‖^3`, where `F(z) = (z + 1)/‖z + 1‖^3 + (z - 1)/‖z - 1‖^3`,
is equivalent (via the radial bijection `w ↦ w / ‖w‖^(3/2)` on `ℂ \ {0}`) to
`Phi(z) = C` on `U := ℂ \ {-1, 1, 0}`, where `Phi(z) = z - F(z) / (sqrt ‖F(z)‖)^3`.

We prove:
1. `Phi` maps `U` into `V` and is proper on `U → V`.
2. `Phi` has a strict `ℝ`-Fréchet derivative everywhere on `U` with strictly positive Jacobian
   determinant (proved algebraically via rotation invariance and two cubic Bernstein identities).
3. By the inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`), the fiber
   cardinality `C ↦ (Phi ⁻¹' {C} ∩ U).encard` is locally constant on the connected set `V`,
   hence constant.
4. At `C = 0 ∈ V`, elementary algebra gives `(Phi ⁻¹' {0} ∩ U).encard ≤ 2 ≤ 4`.
-/

namespace OMA.MaxwellH2

open Complex Real Topology Filter Set Metric
open scoped RealInnerProductSpace

/-- Domain `U = ℂ \ {-1, 1, 0}` of the covering map `Phi`. -/
def U : Set ℂ := {(-1 : ℂ), (1 : ℂ), (0 : ℂ)}ᶜ

/-- Codomain `V = ℂ \ {-1, 1}` of the covering map `Phi`. -/
def V : Set ℂ := {(-1 : ℂ), (1 : ℂ)}ᶜ

/-- Electric field of two unit positive charges at `-1` and `1`. -/
noncomputable def F (z : ℂ) : ℂ :=
  ((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1) + ((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)

/-- The parameter-free covering map `Phi : U → V`. -/
noncomputable def Phi (z : ℂ) : ℂ :=
  z - ((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z

/- Basic properties of `U`, `V`, `F`, `Phi` -/

lemma mem_U_iff {z : ℂ} : z ∈ U ↔ z ≠ -1 ∧ z ≠ 1 ∧ z ≠ 0 := by
  simp [U]

lemma mem_V_iff {z : ℂ} : z ∈ V ↔ z ≠ -1 ∧ z ≠ 1 := by
  simp [V]

lemma isOpen_U : IsOpen U :=
  (Set.toFinite {(-1 : ℂ), (1 : ℂ), (0 : ℂ)}).isClosed.isOpen_compl

lemma isOpen_V : IsOpen V :=
  (Set.toFinite {(-1 : ℂ), (1 : ℂ)}).isClosed.isOpen_compl

lemma isConnected_V : IsConnected V := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  exact (Set.toFinite {(-1 : ℂ), (1 : ℂ)}).countable.isConnected_compl_of_one_lt_rank hrank

lemma F_neg (z : ℂ) : F (-z) = -F z := by
  have h1 : ‖-z + 1‖ = ‖z - 1‖ := by
    rw [show (-z + 1 : ℂ) = -(z - 1) by ring, norm_neg]
  have h2 : ‖-z - 1‖ = ‖z + 1‖ := by
    rw [show (-z - 1 : ℂ) = -(z + 1) by ring, norm_neg]
  simp only [F, h1, h2]
  rw [show (-z + 1 : ℂ) = -(z - 1) by ring, show (-z - 1 : ℂ) = -(z + 1) by ring]
  simp only [smul_neg]
  abel

lemma Phi_neg (z : ℂ) : Phi (-z) = -Phi z := by
  simp only [Phi, F_neg, norm_neg, smul_neg]
  abel

lemma F_ne_zero {z : ℂ} (hz : z ∈ U) : F z ≠ 0 := by
  rw [mem_U_iff] at hz
  obtain ⟨hm1, h1, h0⟩ := hz
  have hz1 : z + 1 ≠ 0 := fun h => hm1 (eq_neg_of_add_eq_zero_left h)
  have hz2 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hr1 : 0 < ‖z + 1‖ := norm_pos_iff.mpr hz1
  have hr2 : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz2
  intro hF
  simp only [F] at hF
  have heq : ((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1) = -(((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)) :=
    eq_neg_of_add_eq_zero_left hF
  have hnorm : ‖((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1)‖ = ‖((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)‖ := by
    rw [heq, norm_neg]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hr1 3)), abs_of_pos (inv_pos.mpr (pow_pos hr2 3))] at hnorm
  have hsq : ‖z + 1‖ ^ 2 = ‖z - 1‖ ^ 2 := by
    have h1' : (‖z + 1‖ ^ 3)⁻¹ * ‖z + 1‖ = (‖z + 1‖ ^ 2)⁻¹ := by field_simp
    have h2' : (‖z - 1‖ ^ 3)⁻¹ * ‖z - 1‖ = (‖z - 1‖ ^ 2)⁻¹ := by field_simp
    rw [h1', h2'] at hnorm
    exact inv_injective hnorm
  have hreq : ‖z + 1‖ = ‖z - 1‖ := by nlinarith
  rw [hreq, ← smul_add] at hF
  have hsum : (z + 1) + (z - 1) = 0 :=
    (smul_eq_zero.mp hF).resolve_left (inv_ne_zero (pow_ne_zero 3 hr2.ne'))
  apply h0
  have : (2 : ℂ) * z = 0 := by linear_combination hsum
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

lemma g_inv_equiv {w v : ℂ} (hw : w ≠ 0) :
    v = ((Real.sqrt ‖w‖ ^ 3)⁻¹ : ℝ) • w ↔ v ≠ 0 ∧ ((‖v‖ ^ 3)⁻¹ : ℝ) • v = w := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hs : 0 < Real.sqrt ‖w‖ := Real.sqrt_pos.mpr hwn
  constructor
  · intro hv
    have hnv : ‖v‖ = (Real.sqrt ‖w‖)⁻¹ := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hs 3))]
      have hsq : Real.sqrt ‖w‖ ^ 2 = ‖w‖ := Real.sq_sqrt hwn.le
      field_simp [hs.ne']
      linarith
    refine ⟨norm_pos_iff.mp (by rw [hnv]; positivity), ?_⟩
    rw [hnv, hv, smul_smul, inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero 3 hs.ne'), one_smul]
  · rintro ⟨hv0, hvw⟩
    have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hnw : ‖w‖ = (‖v‖ ^ 2)⁻¹ := by
      rw [← hvw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hvn 3))]
      field_simp [hvn.ne']
    have hsq : Real.sqrt ‖w‖ = ‖v‖⁻¹ := by
      rw [hnw, Real.sqrt_inv, Real.sqrt_sq hvn.le]
    rw [hsq, ← hvw, smul_smul, inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero 3 hvn.ne'), one_smul]

lemma Phi_eq_iff {z C : ℂ} (hz : z ∈ U) :
    Phi z = C ↔ z ≠ C ∧ F z = ((‖z - C‖ ^ 3)⁻¹ : ℝ) • (z - C) := by
  have hsub : Phi z = C ↔ z - C = ((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z := by
    simp only [Phi]
    constructor
    · intro h
      calc z - C = z - (z - ((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z) := by rw [← h]
        _ = ((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z := by abel
    · intro h
      calc z - ((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z = z - (z - C) := by rw [← h]
        _ = C := by abel
  rw [hsub, g_inv_equiv (F_ne_zero hz), sub_ne_zero, eq_comm]

lemma Phi_mapsTo : Set.MapsTo Phi U V := by
  intro z hz
  rw [mem_V_iff]
  have hz' := mem_U_iff.mp hz
  constructor
  · intro h
    obtain ⟨_, hF⟩ := (Phi_eq_iff hz).mp h
    simp only [F, sub_neg_eq_add] at hF
    have h0 : ((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1) = 0 := by linear_combination hF
    have hz2 : z - 1 ≠ 0 := sub_ne_zero.mpr hz'.2.1
    exact hz2 ((smul_eq_zero.mp h0).resolve_left (inv_ne_zero (pow_ne_zero 3 (norm_ne_zero_iff.mpr hz2))))
  · intro h
    obtain ⟨_, hF⟩ := (Phi_eq_iff hz).mp h
    simp only [F] at hF
    have h0 : ((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1) = 0 := by linear_combination hF
    have hz1 : z + 1 ≠ 0 := fun e => hz'.1 (eq_neg_of_add_eq_zero_left e)
    exact hz1 ((smul_eq_zero.mp h0).resolve_left (inv_ne_zero (pow_ne_zero 3 (norm_ne_zero_iff.mpr hz1))))

/- Fiber cardinality at `C = 0` is at most `2` -/

lemma unique_pos_root_four_cube {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h2 : 0 < t₂)
    (e1 : 4 * t₁ ^ 3 = (t₁ + 1) ^ 3) (e2 : 4 * t₂ ^ 3 = (t₂ + 1) ^ 3) : t₁ = t₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hm : t₁ * (t₂ + 1) < t₂ * (t₁ + 1) := by nlinarith
    have hm0 : 0 ≤ t₁ * (t₂ + 1) := by positivity
    have hcube : (t₁ * (t₂ + 1)) ^ 3 < (t₂ * (t₁ + 1)) ^ 3 :=
      pow_lt_pow_left₀ hm hm0 (by norm_num)
    rw [mul_pow, mul_pow, ← e2, ← e1] at hcube
    linarith
  · have hm : t₂ * (t₁ + 1) < t₁ * (t₂ + 1) := by nlinarith
    have hm0 : 0 ≤ t₂ * (t₁ + 1) := by positivity
    have hcube : (t₂ * (t₁ + 1)) ^ 3 < (t₁ * (t₂ + 1)) ^ 3 :=
      pow_lt_pow_left₀ hm hm0 (by norm_num)
    rw [mul_pow, mul_pow, ← e1, ← e2] at hcube
    linarith

lemma zero_fiber_char {z : ℂ} (hz : z ∈ U) (hPhi : Phi z = 0) :
    z.re = 0 ∧ z.im ≠ 0 ∧ 4 * (z.im ^ 2) ^ 3 = (z.im ^ 2 + 1) ^ 3 := by
  obtain ⟨_, hF⟩ := (Phi_eq_iff hz).mp hPhi
  rw [sub_zero] at hF
  have hz' := mem_U_iff.mp hz
  set a : ℝ := (‖z + 1‖ ^ 3)⁻¹
  set b : ℝ := (‖z - 1‖ ^ 3)⁻¹
  set c : ℝ := (‖z‖ ^ 3)⁻¹
  have ha : 0 < a := inv_pos.mpr (pow_pos (norm_pos_iff.mpr (fun e => hz'.1 (eq_neg_of_add_eq_zero_left e))) 3)
  have hb : 0 < b := inv_pos.mpr (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz'.2.1)) 3)
  have hc : 0 < c := inv_pos.mpr (pow_pos (norm_pos_iff.mpr hz'.2.2) 3)
  have hre : a * (z.re + 1) + b * (z.re - 1) = c * z.re := by
    have := congrArg Complex.re hF
    simpa only [F, a, b, c, Complex.add_re, Complex.smul_re, Complex.sub_re,
      Complex.one_re, smul_eq_mul] using this
  have him : (a + b) * z.im = c * z.im := by
    have := congrArg Complex.im hF
    simp only [F, a, b, c, Complex.add_im, Complex.smul_im, Complex.sub_im,
      Complex.one_im, add_zero, sub_zero, smul_eq_mul] at this
    linarith
  have hy0 : z.im ≠ 0 := by
    intro hy
    have hzre : z = (z.re : ℂ) := Complex.ext rfl hy
    set x := z.re
    have hx0 : x ≠ 0 := fun h => hz'.2.2 (by rw [hzre, h]; simp)
    have hx1 : x ≠ 1 := fun h => hz'.2.1 (by rw [hzre, h]; simp)
    have hxm1 : x ≠ -1 := fun h => hz'.1 (by rw [hzre, h]; simp)
    have hn1 : ‖z + 1‖ = |x + 1| := by
      rw [hzre, show ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    have hn2 : ‖z - 1‖ = |x - 1| := by
      rw [hzre, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    have hn0 : ‖z‖ = |x| := by
      rw [hzre, Complex.norm_real, Real.norm_eq_abs]
    have hre' : (|x + 1| ^ 3)⁻¹ * (x + 1) + (|x - 1| ^ 3)⁻¹ * (x - 1) = (|x| ^ 3)⁻¹ * x := by
      simpa only [a, b, c, hn1, hn2, hn0] using hre
    have term_pos : ∀ t : ℝ, 0 < t → (|t| ^ 3)⁻¹ * t = (t ^ 2)⁻¹ := by
      intro t ht; rw [abs_of_pos ht]; field_simp [ht.ne']
    have term_neg : ∀ t : ℝ, t < 0 → (|t| ^ 3)⁻¹ * t = -((t ^ 2)⁻¹) := by
      intro t ht; rw [abs_of_neg ht]; field_simp [ht.ne']
    rcases lt_or_gt_of_ne hx0 with hxn | hxp
    · rcases lt_or_gt_of_ne hxm1 with hxlt | hxgt
      · rw [term_neg (x + 1) (by linarith), term_neg (x - 1) (by linarith), term_neg x hxn] at hre'
        have h1 : (x ^ 2)⁻¹ < ((x + 1) ^ 2)⁻¹ :=
          inv_strictAnti₀ (sq_pos_of_ne_zero (by linarith)) (by nlinarith)
        have h2 : 0 < ((x - 1) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero (by linarith))
        linarith
      · rw [term_pos (x + 1) (by linarith), term_neg (x - 1) (by linarith), term_neg x hxn] at hre'
        have h1 : ((x - 1) ^ 2)⁻¹ < ((x + 1) ^ 2)⁻¹ :=
          inv_strictAnti₀ (sq_pos_of_ne_zero (by linarith)) (by nlinarith)
        have h2 : 0 < (x ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero hx0)
        linarith
    · rcases lt_or_gt_of_ne hx1 with hxlt | hxgt
      · rw [term_pos (x + 1) (by linarith), term_neg (x - 1) (by linarith), term_pos x hxp] at hre'
        have h1 : ((x + 1) ^ 2)⁻¹ < ((x - 1) ^ 2)⁻¹ :=
          inv_strictAnti₀ (sq_pos_of_ne_zero (by linarith)) (by nlinarith)
        have h2 : 0 < (x ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero hx0)
        linarith
      · rw [term_pos (x + 1) (by linarith), term_pos (x - 1) (by linarith), term_pos x hxp] at hre'
        have h1 : (x ^ 2)⁻¹ < ((x - 1) ^ 2)⁻¹ :=
          inv_strictAnti₀ (sq_pos_of_ne_zero (by linarith)) (by nlinarith)
        have h2 : 0 < ((x + 1) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero (by linarith))
        linarith
  have habc : a + b = c := mul_right_cancel₀ hy0 him
  have hab : a = b := by
    have : a - b = 0 := by linear_combination hre - z.re * habc
    linarith
  have hnorm_eq : ‖z + 1‖ = ‖z - 1‖ := by
    have hcube : ‖z + 1‖ ^ 3 = ‖z - 1‖ ^ 3 := inv_injective hab
    have h1 : 0 ≤ ‖z + 1‖ := norm_nonneg _
    have h2 : 0 ≤ ‖z - 1‖ := norm_nonneg _
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hcube (ne_of_lt (pow_lt_pow_left₀ h h1 (by norm_num)))
    · exact absurd hcube (ne_of_gt (pow_lt_pow_left₀ h h2 (by norm_num)))
  have hsq : Complex.normSq (z + 1) = Complex.normSq (z - 1) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, hnorm_eq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    Complex.sub_re, Complex.sub_im, add_zero, sub_zero] at hsq
  have hx0 : z.re = 0 := by nlinarith
  refine ⟨hx0, hy0, ?_⟩
  have h2a : 2 * a = c := by linarith
  have hnz : ‖z‖ = |z.im| := by
    rw [← Real.sqrt_sq (norm_nonneg z), Complex.sq_norm, Complex.normSq_apply, hx0]
    simp [← sq, Real.sqrt_sq_eq_abs]
  have hnz1 : ‖z + 1‖ = Real.sqrt (z.im ^ 2 + 1) := by
    rw [← Real.sqrt_sq (norm_nonneg (z + 1)), Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, hx0]
    congr 1; ring
  have hpos1 : 0 < Real.sqrt (z.im ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hpos2 : 0 < |z.im| := abs_pos.mpr hy0
  have h2a' : 2 * (Real.sqrt (z.im ^ 2 + 1) ^ 3)⁻¹ = (|z.im| ^ 3)⁻¹ := by
    simpa only [a, c, hnz, hnz1] using h2a
  have hEq : 2 * |z.im| ^ 3 = Real.sqrt (z.im ^ 2 + 1) ^ 3 := by
    field_simp [hpos1.ne', hpos2.ne'] at h2a'
    linarith
  have hSq := congrArg (fun t : ℝ => t ^ 2) hEq
  have h1 : (2 * |z.im| ^ 3) ^ 2 = 4 * (z.im ^ 2) ^ 3 := by
    rw [mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, sq_abs]
    ring
  have h2 : (Real.sqrt (z.im ^ 2 + 1) ^ 3) ^ 2 = (z.im ^ 2 + 1) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  linarith

lemma encard_zero_fiber_le_two : (Phi ⁻¹' {0} ∩ U).encard ≤ 2 := by
  by_cases hne : (Phi ⁻¹' {0} ∩ U).Nonempty
  · obtain ⟨z₀, hz₀Phi, hz₀U⟩ := hne
    obtain ⟨hx₀, hy₀, he₀⟩ := zero_fiber_char hz₀U hz₀Phi
    have hsub : Phi ⁻¹' {0} ∩ U ⊆ {z₀, -z₀} := by
      rintro z ⟨hzPhi, hzU⟩
      obtain ⟨hx, hy, he⟩ := zero_fiber_char hzU hzPhi
      have hsq : z.im ^ 2 = z₀.im ^ 2 :=
        unique_pos_root_four_cube (sq_pos_of_ne_zero hy) (sq_pos_of_ne_zero hy₀) he he₀
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · left; exact Complex.ext (by linarith) h
      · right; exact Complex.ext (by simp [hx, hx₀]) (by simp [h])
    calc (Phi ⁻¹' {0} ∩ U).encard ≤ ({z₀, -z₀} : Set ℂ).encard := Set.encard_le_encard hsub
      _ ≤ ({-z₀} : Set ℂ).encard + 1 := Set.encard_insert_le _ _
      _ = 2 := by rw [Set.encard_singleton]; norm_num
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.encard_empty]
    exact bot_le

/- Continuity and Properness of `Phi : U → V` -/

lemma continuousAt_F {z : ℂ} (hz1 : z ≠ -1) (hz2 : z ≠ 1) : ContinuousAt F z := by
  have h1 : ContinuousAt (fun y : ℂ => ((‖y + 1‖ ^ 3)⁻¹ : ℝ) • (y + 1)) z :=
    ContinuousAt.smul
      (((continuousAt_id.add continuousAt_const).norm.pow 3).inv₀
        (pow_ne_zero 3 (norm_ne_zero_iff.mpr (fun e => hz1 (eq_neg_of_add_eq_zero_left e)))))
      (continuousAt_id.add continuousAt_const)
  have h2 : ContinuousAt (fun y : ℂ => ((‖y - 1‖ ^ 3)⁻¹ : ℝ) • (y - 1)) z :=
    ContinuousAt.smul
      (((continuousAt_id.sub continuousAt_const).norm.pow 3).inv₀
        (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz2))))
      (continuousAt_id.sub continuousAt_const)
  exact h1.add h2

lemma continuousOn_Phi : ContinuousOn Phi U := by
  intro z hz
  have hz' := mem_U_iff.mp hz
  have hFc : ContinuousAt F z := continuousAt_F hz'.1 hz'.2.1
  have hF0 : F z ≠ 0 := F_ne_zero hz
  have hgs : ContinuousAt (fun y : ℂ => ((Real.sqrt ‖F y‖ ^ 3)⁻¹ : ℝ) • F y) z :=
    ContinuousAt.smul
      (((hFc.norm.sqrt).pow 3).inv₀
        (pow_ne_zero 3 (Real.sqrt_pos.mpr (norm_pos_iff.mpr hF0)).ne'))
      hFc
  exact (continuousAt_id.sub hgs).continuousWithinAt

lemma large_t_bound {t : ℝ} (ht : 10 ≤ t) : (5 / 4 : ℝ) / t ^ 2 ≤ 2 * (t - 1) / (t + 1) ^ 3 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hid : 2 * (t - 1) * t ^ 2 - 5 / 4 * (t + 1) ^ 3 =
      ((t - 10) * (3 * t ^ 2 + 7 * t + 55) + 545) / 4 := by ring
  have h1 : 0 ≤ (t - 10) * (3 * t ^ 2 + 7 * t + 55) := by
    have : 0 ≤ t - 10 := by linarith
    have : 0 ≤ 3 * t ^ 2 + 7 * t + 55 := by positivity
    positivity
  linarith

lemma norm_Phi_ge_large {z : ℂ} (hz : 10 ≤ ‖z‖) : (1 / 10 : ℝ) * ‖z‖ ≤ ‖Phi z‖ := by
  set t : ℝ := ‖z‖
  have htpos : 0 < t := by linarith
  have hz1 : ‖z + 1‖ ≤ t + 1 := by simpa [t] using norm_add_le z (1 : ℂ)
  have hz2 : ‖z - 1‖ ≤ t + 1 := by
    calc ‖z - 1‖ = ‖z + (-1 : ℂ)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖(-1 : ℂ)‖ := norm_add_le z (-1)
      _ = t + 1 := by simp [t]
  have hz1p : 0 < ‖z + 1‖ := by
    have := norm_sub_norm_le z (-1 : ℂ)
    simp at this
    linarith
  have hz2p : 0 < ‖z - 1‖ := by
    have := norm_sub_norm_le z (1 : ℂ)
    simp at this
    linarith
  have hin1 : ⟪z, (1 : ℂ)⟫ = z.re := by simp [Complex.inner]
  have habs_re : |z.re| ≤ t := Complex.abs_re_le_norm z
  have hre1 : t ^ 2 - t ≤ ⟪z, z + 1⟫ := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hin1]
    linarith [(abs_le.mp habs_re).1]
  have hre2 : t ^ 2 - t ≤ ⟪z, z - 1⟫ := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hin1]
    linarith [(abs_le.mp habs_re).2]
  have hinner : 2 * (t ^ 2 - t) / (t + 1) ^ 3 ≤ ⟪z, F z⟫ := by
    have hnn : 0 ≤ t ^ 2 - t := by nlinarith
    have hc1 : ((t + 1) ^ 3)⁻¹ ≤ (‖z + 1‖ ^ 3)⁻¹ :=
      inv_anti₀ (pow_pos hz1p 3) (pow_le_pow_left₀ hz1p.le hz1 3)
    have hc2 : ((t + 1) ^ 3)⁻¹ ≤ (‖z - 1‖ ^ 3)⁻¹ :=
      inv_anti₀ (pow_pos hz2p 3) (pow_le_pow_left₀ hz2p.le hz2 3)
    have hF_in : ⟪z, F z⟫ = (‖z + 1‖ ^ 3)⁻¹ * ⟪z, z + 1⟫ + (‖z - 1‖ ^ 3)⁻¹ * ⟪z, z - 1⟫ := by
      simp only [F, inner_add_right, real_inner_smul_right]
    rw [hF_in]
    have t1 : ((t + 1) ^ 3)⁻¹ * (t ^ 2 - t) ≤ (‖z + 1‖ ^ 3)⁻¹ * ⟪z, z + 1⟫ :=
      mul_le_mul hc1 hre1 hnn (inv_nonneg.mpr (pow_nonneg hz1p.le 3))
    have t2 : ((t + 1) ^ 3)⁻¹ * (t ^ 2 - t) ≤ (‖z - 1‖ ^ 3)⁻¹ * ⟪z, z - 1⟫ :=
      mul_le_mul hc2 hre2 hnn (inv_nonneg.mpr (pow_nonneg hz2p.le 3))
    rw [div_eq_inv_mul]
    linarith
  have hCS : ⟪z, F z⟫ ≤ t * ‖F z‖ := real_inner_le_norm z (F z)
  have hF_lb : (5 / 4 : ℝ) / t ^ 2 ≤ ‖F z‖ := by
    have h1 : 2 * (t - 1) / (t + 1) ^ 3 ≤ ‖F z‖ := by
      have hdiv : 2 * (t ^ 2 - t) / (t + 1) ^ 3 ≤ t * ‖F z‖ := hinner.trans hCS
      have hfac : 2 * (t ^ 2 - t) / (t + 1) ^ 3 = t * (2 * (t - 1) / (t + 1) ^ 3) := by ring
      rw [hfac] at hdiv
      exact le_of_mul_le_mul_left hdiv htpos
    exact (large_t_bound hz).trans h1
  have hFpos : 0 < ‖F z‖ := lt_of_lt_of_le (by positivity) hF_lb
  have hsqrt_lb : (10 / 9 : ℝ) / t ≤ Real.sqrt ‖F z‖ := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (10 / 9 : ℝ) / t)]
    refine Real.sqrt_le_sqrt (le_trans ?_ hF_lb)
    rw [div_pow]
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg t)
  have hterm : ‖((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ ≤ (9 / 10 : ℝ) * t := by
    have hs : 0 < Real.sqrt ‖F z‖ := Real.sqrt_pos.mpr hFpos
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hs 3))]
    have hsim : (Real.sqrt ‖F z‖ ^ 3)⁻¹ * ‖F z‖ = (Real.sqrt ‖F z‖)⁻¹ := by
      have hsq : Real.sqrt ‖F z‖ ^ 2 = ‖F z‖ := Real.sq_sqrt hFpos.le
      field_simp [hs.ne']
      linarith
    rw [hsim]
    have := inv_anti₀ (by positivity) hsqrt_lb
    rw [inv_div] at this
    linarith
  have hrev : t - ‖((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ ≤ ‖Phi z‖ :=
    norm_sub_norm_le z (((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z)
  linarith only [hrev, hterm]

lemma norm_Phi_sub_one_le {z : ℂ} (hz : z ∈ U) (hsmall : ‖z - 1‖ ≤ 1 / 2) :
    ‖Phi z - 1‖ ≤ 3 * ‖z - 1‖ := by
  have hz' := mem_U_iff.mp hz
  have hr2 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz'.2.1)
  have hr1 : 3 / 2 ≤ ‖z + 1‖ := by
    have h : ‖(2 : ℂ)‖ - ‖-(z - 1)‖ ≤ ‖(2 : ℂ) - (-(z - 1))‖ := norm_sub_norm_le (2 : ℂ) (-(z - 1))
    rw [norm_neg, show (2 : ℂ) - -(z - 1) = z + 1 by ring] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith
  have hF_lb : (1 / 2 : ℝ) / ‖z - 1‖ ^ 2 ≤ ‖F z‖ := by
    have h1 : ‖((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)‖ - ‖((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1)‖ ≤ ‖F z‖ := by
      have := norm_sub_norm_le (((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)) (-(((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1)))
      simp only [sub_neg_eq_add, norm_neg] at this
      simpa [F, add_comm] using this
    have hn2 : ‖((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)‖ = (‖z - 1‖ ^ 2)⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hr2 3))]
      field_simp [hr2.ne']
    have hn1 : ‖((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1)‖ = (‖z + 1‖ ^ 2)⁻¹ := by
      have hr1p : 0 < ‖z + 1‖ := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hr1p 3))]
      field_simp [hr1p.ne']
    rw [hn2, hn1] at h1
    have hb1 : (‖z + 1‖ ^ 2)⁻¹ ≤ 4 / 9 := by
      have : (9 / 4 : ℝ) ≤ ‖z + 1‖ ^ 2 := by nlinarith
      calc (‖z + 1‖ ^ 2)⁻¹ ≤ (9 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
        _ = 4 / 9 := by norm_num
    have hb2 : 4 ≤ (‖z - 1‖ ^ 2)⁻¹ := by
      have : ‖z - 1‖ ^ 2 ≤ 1 / 4 := by nlinarith
      calc (4 : ℝ) = (1 / 4 : ℝ)⁻¹ := by norm_num
        _ ≤ (‖z - 1‖ ^ 2)⁻¹ := inv_anti₀ (pow_pos hr2 2) this
    rw [div_eq_mul_inv]
    linarith
  have hFpos : 0 < ‖F z‖ := lt_of_lt_of_le (by positivity) hF_lb
  have hsqrt_lb : (1 / 2 : ℝ) / ‖z - 1‖ ≤ Real.sqrt ‖F z‖ := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) / ‖z - 1‖)]
    refine Real.sqrt_le_sqrt (le_trans ?_ hF_lb)
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hterm : ‖((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ ≤ 2 * ‖z - 1‖ := by
    have hs : 0 < Real.sqrt ‖F z‖ := Real.sqrt_pos.mpr hFpos
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hs 3))]
    have hsim : (Real.sqrt ‖F z‖ ^ 3)⁻¹ * ‖F z‖ = (Real.sqrt ‖F z‖)⁻¹ := by
      have hsq : Real.sqrt ‖F z‖ ^ 2 = ‖F z‖ := Real.sq_sqrt hFpos.le
      field_simp [hs.ne']
      linarith
    rw [hsim]
    have := inv_anti₀ (by positivity) hsqrt_lb
    rw [inv_div] at this
    linarith
  calc ‖Phi z - 1‖ = ‖(z - 1) - ((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ := by simp [Phi]; ring_nf
    _ ≤ ‖z - 1‖ + ‖((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ := norm_sub_le _ _
    _ ≤ 3 * ‖z - 1‖ := by linarith

lemma Phi_proper_local {C : ℂ} (hC : C ∈ V) :
    ∃ δ > 0, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧
      Phi ⁻¹' Metric.closedBall C δ ∩ U ⊆ K := by
  rw [mem_V_iff] at hC
  set δ : ℝ := (1 / 4 : ℝ) * min ‖C - 1‖ ‖C + 1‖
  have hδ : 0 < δ := by
    have h1 : 0 < ‖C - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hC.2)
    have h2 : 0 < ‖C + 1‖ := norm_pos_iff.mpr (fun e => hC.1 (eq_neg_of_add_eq_zero_left e))
    positivity
  set M : ℝ := ‖C‖ + δ + 2
  have hM : 0 < M := by positivity
  have hF0 : F 0 = 0 := by simp [F]
  have hFc0 : ContinuousAt F 0 := continuousAt_F (by norm_num) (by norm_num)
  have hball0 := Metric.continuousAt_iff.mp hFc0 (1 / M ^ 2) (by positivity)
  obtain ⟨ε₀', hε₀'pos, hε₀'⟩ := hball0
  set ε₀ : ℝ := min (1 / 2) ε₀'
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) hε₀'pos
  set ε₁ : ℝ := min (1 / 2) (δ / 3)
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by positivity)
  set R : ℝ := max 10 (10 * (‖C‖ + δ + 1))
  set K : Set ℂ := {z : ℂ | ‖z‖ ≤ R ∧ ε₀ ≤ ‖z‖ ∧ ε₁ ≤ ‖z - 1‖ ∧ ε₁ ≤ ‖z + 1‖}
  refine ⟨δ, hδ, K, ?_, ?_, ?_⟩
  · refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hc1 : IsClosed {z : ℂ | ‖z‖ ≤ R} := isClosed_le continuous_norm continuous_const
      have hc2 : IsClosed {z : ℂ | ε₀ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
      have hc3 : IsClosed {z : ℂ | ε₁ ≤ ‖z - 1‖} :=
        isClosed_le continuous_const (continuous_id.sub continuous_const).norm
      have hc4 : IsClosed {z : ℂ | ε₁ ≤ ‖z + 1‖} :=
        isClosed_le continuous_const (continuous_id.add continuous_const).norm
      exact hc1.inter (hc2.inter (hc3.inter hc4))
    · rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
      exact ⟨R, fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1⟩
  · intro z ⟨_, h0, h1, hm1⟩
    rw [mem_U_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro e; rw [e] at hm1; simp at hm1; linarith
    · intro e; rw [e] at h1; simp at h1; linarith
    · intro e; rw [e] at h0; simp at h0; linarith
  · rintro z ⟨hPhi, hzU⟩
    change Phi z ∈ Metric.closedBall C δ at hPhi
    rw [Metric.mem_closedBall, dist_eq_norm] at hPhi
    have hPhi_ub : ‖Phi z‖ ≤ ‖C‖ + δ := by
      have := norm_add_le (Phi z - C) C
      simpa using this.trans (by linarith)
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hgt
      push Not at hgt
      have h10 : 10 ≤ ‖z‖ := le_trans (le_max_left _ _) hgt.le
      have hbig := norm_Phi_ge_large h10
      have hR2 : 10 * (‖C‖ + δ + 1) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hgt
      linarith
    · by_contra hlt
      push Not at hlt
      have hlt' : dist z 0 < ε₀' := by
        simpa [dist_zero_right] using lt_of_lt_of_le hlt (min_le_right _ _)
      have hFsm : ‖F z‖ < 1 / M ^ 2 := by
        simpa [dist_eq_norm, hF0] using hε₀' hlt'
      have hFpos : 0 < ‖F z‖ := norm_pos_iff.mpr (F_ne_zero hzU)
      have hsq_lt : Real.sqrt ‖F z‖ < 1 / M := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / M)]
        refine Real.sqrt_lt_sqrt hFpos.le ?_
        simpa [div_pow] using hFsm
      have hterm_gt : M < ‖((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ := by
        have hs : 0 < Real.sqrt ‖F z‖ := Real.sqrt_pos.mpr hFpos
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hs 3))]
        have hsim : (Real.sqrt ‖F z‖ ^ 3)⁻¹ * ‖F z‖ = (Real.sqrt ‖F z‖)⁻¹ := by
          have hsq : Real.sqrt ‖F z‖ ^ 2 = ‖F z‖ := Real.sq_sqrt hFpos.le
          field_simp [hs.ne']
          linarith
        rw [hsim]
        have := inv_strictAnti₀ hs hsq_lt
        simpa [one_div] using this
      have hrev : ‖((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z‖ - ‖z‖ ≤ ‖Phi z‖ := by
        have := norm_sub_norm_le (((Real.sqrt ‖F z‖ ^ 3)⁻¹ : ℝ) • F z) z
        rw [norm_sub_rev] at this
        simpa [Phi] using this
      have hle_half : ‖z‖ < 1 / 2 := lt_of_lt_of_le hlt (min_le_left _ _)
      linarith
    · by_contra hlt
      push Not at hlt
      have hle_half : ‖z - 1‖ ≤ 1 / 2 := (lt_of_lt_of_le hlt (min_le_left _ _)).le
      have h3 := norm_Phi_sub_one_le hzU hle_half
      have hlt_d : ‖Phi z - 1‖ < δ := by
        have : ‖z - 1‖ < δ / 3 := lt_of_lt_of_le hlt (min_le_right _ _)
        linarith
      have hC1 : 4 * δ ≤ ‖C - 1‖ := by
        have : δ ≤ (1 / 4) * ‖C - 1‖ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        linarith
      have htri : ‖C - 1‖ ≤ ‖Phi z - C‖ + ‖Phi z - 1‖ := by
        calc ‖C - 1‖ = ‖-(Phi z - C) + (Phi z - 1)‖ := by ring_nf
          _ ≤ ‖-(Phi z - C)‖ + ‖Phi z - 1‖ := norm_add_le _ _
          _ = ‖Phi z - C‖ + ‖Phi z - 1‖ := by rw [norm_neg]
      linarith
    · by_contra hlt
      push Not at hlt
      have hnzU : -z ∈ U := by
        rw [mem_U_iff] at hzU ⊢
        refine ⟨?_, ?_, ?_⟩
        · intro e; exact hzU.2.1 (by linear_combination -e)
        · intro e; exact hzU.1 (by linear_combination -e)
        · intro e; exact hzU.2.2 (neg_eq_zero.mp e)
      have hzm1 : ‖-z - 1‖ = ‖z + 1‖ := by
        rw [show (-z - 1 : ℂ) = -(z + 1) by ring, norm_neg]
      have hle_half : ‖-z - 1‖ ≤ 1 / 2 := by
        rw [hzm1]; exact (lt_of_lt_of_le hlt (min_le_left _ _)).le
      have h3 := norm_Phi_sub_one_le hnzU hle_half
      rw [Phi_neg, show (-Phi z - 1 : ℂ) = -(Phi z + 1) by ring, norm_neg, hzm1] at h3
      have hlt_d : ‖Phi z + 1‖ < δ := by
        have : ‖z + 1‖ < δ / 3 := lt_of_lt_of_le hlt (min_le_right _ _)
        linarith
      have hCm1 : 4 * δ ≤ ‖C + 1‖ := by
        have : δ ≤ (1 / 4) * ‖C + 1‖ := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        linarith
      have htri : ‖C + 1‖ ≤ ‖Phi z - C‖ + ‖Phi z + 1‖ := by
        calc ‖C + 1‖ = ‖-(Phi z - C) + (Phi z + 1)‖ := by ring_nf
          _ ≤ ‖-(Phi z - C)‖ + ‖Phi z + 1‖ := norm_add_le _ _
          _ = ‖Phi z - C‖ + ‖Phi z + 1‖ := by rw [norm_neg]
      linarith

/- Strict Fréchet derivative of `Phi` -/

noncomputable def L_term (d : ℂ) : ℂ →L[ℝ] ℂ :=
  ((‖d‖ ^ 3)⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ +
    (((-3 : ℝ) * (‖d‖ ^ 5)⁻¹) • innerSL ℝ d).smulRight d

noncomputable def DF (z : ℂ) : ℂ →L[ℝ] ℂ :=
  L_term (z + 1) + L_term (z - 1)

noncomputable def Dg (w : ℂ) : ℂ →L[ℝ] ℂ :=
  ((Real.sqrt ‖w‖ ^ 3)⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ +
    (((-3 / 2 : ℝ) * (Real.sqrt ‖w‖ ^ 7)⁻¹) • innerSL ℝ w).smulRight w

noncomputable def DPhi (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ - (Dg (F z)).comp (DF z)

lemma hasStrictFDerivAt_norm_sub (p z : ℂ) (h : z ≠ p) :
    HasStrictFDerivAt (fun y : ℂ => ‖y - p‖) (‖z - p‖⁻¹ • innerSL ℝ (z - p)) z := by
  have hd : z - p ≠ 0 := sub_ne_zero.mpr h
  have hn : 0 < ‖z - p‖ := norm_pos_iff.mpr hd
  have hsq : HasStrictFDerivAt (fun y : ℂ => ‖y - p‖ ^ 2) ((2 : ℝ) • innerSL ℝ (z - p)) z := by
    have h1 := (hasStrictFDerivAt_norm_sq (z - p)).comp z ((hasStrictFDerivAt_id z).sub_const p)
    refine h1.congr_fderiv ?_
    ext v
    simp [Nat.cast_smul_eq_nsmul]
  have hsqrt := hsq.sqrt (pow_ne_zero 2 hn.ne')
  have hfun : (fun y : ℂ => ‖y - p‖) = (fun y : ℂ => Real.sqrt (‖y - p‖ ^ 2)) := by
    funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hfun]
  refine hsqrt.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    Real.sqrt_sq (norm_nonneg _)]
  field_simp [hn.ne']

lemma hasStrictFDerivAt_term (p z : ℂ) (h : z ≠ p) :
    HasStrictFDerivAt (fun y : ℂ => ((‖y - p‖ ^ 3)⁻¹ : ℝ) • (y - p)) (L_term (z - p)) z := by
  have hd : z - p ≠ 0 := sub_ne_zero.mpr h
  have hn : 0 < ‖z - p‖ := norm_pos_iff.mpr hd
  have hnorm := hasStrictFDerivAt_norm_sub p z h
  have hpow : HasStrictFDerivAt (fun y : ℂ => ‖y - p‖ ^ 3)
      (((3 : ℝ) * ‖z - p‖ ^ 2) • (‖z - p‖⁻¹ • innerSL ℝ (z - p))) z := by
    simpa [Nat.cast_ofNat] using hnorm.pow 3
  have hinv : HasStrictFDerivAt (fun y : ℂ => (‖y - p‖ ^ 3)⁻¹)
      (((-3 : ℝ) * (‖z - p‖ ^ 5)⁻¹) • innerSL ℝ (z - p)) z := by
    have hi := (hasStrictDerivAt_inv (pow_ne_zero 3 hn.ne')).comp_hasStrictFDerivAt z hpow
    refine hi.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    field_simp [hn.ne']
  have hsmul := hinv.smul ((hasStrictFDerivAt_id z).sub_const p)
  refine hsmul.congr_fderiv ?_
  ext v
  simp [L_term, add_comm]

lemma hasStrictFDerivAt_F {z : ℂ} (hz : z ∈ U) : HasStrictFDerivAt F (DF z) z := by
  rw [mem_U_iff] at hz
  have h1 := hasStrictFDerivAt_term (-1) z hz.1
  have h2 := hasStrictFDerivAt_term 1 z hz.2.1
  have hFeq : F = (fun y : ℂ => ((‖y - (-1)‖ ^ 3)⁻¹ : ℝ) • (y - (-1))) +
      (fun y : ℂ => ((‖y - 1‖ ^ 3)⁻¹ : ℝ) • (y - 1)) := by
    funext y; simp [F, sub_neg_eq_add]
  have hDFeq : DF z = L_term (z - (-1)) + L_term (z - 1) := by
    simp [DF, sub_neg_eq_add]
  rw [hFeq, hDFeq]
  exact h1.add h2

lemma hasStrictFDerivAt_g {w : ℂ} (hw : w ≠ 0) :
    HasStrictFDerivAt (fun y : ℂ => ((Real.sqrt ‖y‖ ^ 3)⁻¹ : ℝ) • y) (Dg w) w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set s : ℝ := Real.sqrt ‖w‖
  have hs : 0 < s := Real.sqrt_pos.mpr hn
  have hsq : s ^ 2 = ‖w‖ := Real.sq_sqrt hn.le
  have hnorm : HasStrictFDerivAt (fun y : ℂ => ‖y‖) (‖w‖⁻¹ • innerSL ℝ w) w := by
    simpa using hasStrictFDerivAt_norm_sub 0 w hw
  have hsqrt : HasStrictFDerivAt (fun y : ℂ => Real.sqrt ‖y‖)
      (((2 * s)⁻¹ * ‖w‖⁻¹) • innerSL ℝ w) w := by
    have := hnorm.sqrt hn.ne'
    refine this.congr_fderiv ?_
    ext v
    simp [s, smul_smul]
  have hpow : HasStrictFDerivAt (fun y : ℂ => Real.sqrt ‖y‖ ^ 3)
      (((3 : ℝ) * s ^ 2) • (((2 * s)⁻¹ * ‖w‖⁻¹) • innerSL ℝ w)) w := by
    simpa [Nat.cast_ofNat, s] using hsqrt.pow 3
  have hinv : HasStrictFDerivAt (fun y : ℂ => (Real.sqrt ‖y‖ ^ 3)⁻¹)
      (((-3 / 2 : ℝ) * (s ^ 7)⁻¹) • innerSL ℝ w) w := by
    have hi := (hasStrictDerivAt_inv (pow_ne_zero 3 hs.ne')).comp_hasStrictFDerivAt w hpow
    change HasStrictFDerivAt (fun y : ℂ => (Real.sqrt ‖y‖ ^ 3)⁻¹) _ w at hi
    refine hi.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [← hsq]
    field_simp [hs.ne']
  have hsmul := hinv.smul (hasStrictFDerivAt_id w)
  refine hsmul.congr_fderiv ?_
  ext v
  simp [Dg, s, add_comm]

lemma hasStrictFDerivAt_Phi {z : ℂ} (hz : z ∈ U) : HasStrictFDerivAt Phi (DPhi z) z := by
  have hF := hasStrictFDerivAt_F hz
  have hg := (hasStrictFDerivAt_g (F_ne_zero hz)).comp z hF
  exact (hasStrictFDerivAt_id z).sub hg

/- Algebraic positivity of the 2x2 Jacobian determinant `det2 (DPhi z) > 0` -/

/-- Determinant of an `ℝ`-linear map `ℂ →L[ℝ] ℂ` in the basis `(1, I)`. -/
noncomputable def det2 (L : ℂ →L[ℝ] ℂ) : ℝ :=
  (L 1).re * (L I).im - (L 1).im * (L I).re

lemma det2_conj_unit (L : ℂ →L[ℝ] ℂ) (u : ℂ) (hu : ‖u‖ = 1) :
    det2 L =
      (starRingEnd ℂ u * L u).re * (starRingEnd ℂ u * L (u * I)).im -
      (starRingEnd ℂ u * L u).im * (starRingEnd ℂ u * L (u * I)).re := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have := congrArg (fun t : ℝ => t ^ 2) hu
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    simpa [sq] using this
  have hLu : L u = u.re • L 1 + u.im • L I := by
    have hu_eq : u = u.re • (1 : ℂ) + u.im • I := by
      apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im]
    conv_lhs => rw [hu_eq]
    rw [map_add, map_smul, map_smul]
  have hLuI : L (u * I) = (-u.im) • L 1 + u.re • L I := by
    have hui : u * I = (-u.im) • (1 : ℂ) + u.re • I := by
      apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im]
    rw [hui, map_add, map_smul, map_smul]
  rw [hLu, hLuI]
  simp only [det2, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  linear_combination
    ((L 1).re * (L I).im - (L 1).im * (L I).re) * (-(u.re ^ 2 + u.im ^ 2 + 1)) * (hu2 - 1)

/-- Normalized cubic polynomial `P1(q, r) > 0` on the feasible region `0 < r < 1`,
`(1 - r^4)/4 ≤ q ≤ min((1 - r^2)/2, 1/4)`. -/
def P1 (q r : ℝ) : ℝ :=
  -72 * q ^ 3 * r + 144 * q ^ 3 - 36 * q ^ 2 * r ^ 5 + 84 * q ^ 2 * r ^ 4 + 132 * q ^ 2 * r
    - 180 * q ^ 2 + 8 * q * r ^ 7 + 72 * q * r ^ 5 - 88 * q * r ^ 4 - 64 * q * r
    + 72 * q + 9 * r ^ 9 - 9 * r ^ 8 - 18 * r ^ 5 + 18 * r ^ 4 + 9 * r - 9

lemma P1_pos_hi {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hhalf : (1 / 2 : ℝ) ≤ r)
    (hqlo : (1 - r ^ 4) / 4 ≤ q) (hqhi : q ≤ (1 - r ^ 2) / 2) :
    0 < P1 q r := by
  set u : ℝ := (1 - r ^ 2) / 2 - q
  set v : ℝ := q - (1 - r ^ 4) / 4
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have huv : 0 < u + v := by
    have : u + v = (1 - r ^ 2) ^ 2 / 4 := by dsimp only [u, v]; ring
    rw [this]
    have : 0 < 1 - r ^ 2 := by nlinarith
    positivity
  set c0 := 2 * r * (1 - r) ^ 5 * (1 + r) * (r ^ 2 + 1) * (3 * r ^ 2 + 2 * r + 1) ^ 2
  set c1 := 4 * (1 - r) ^ 5 * (1 + r) *
      (9 * r ^ 7 + 15 * r ^ 6 + 40 * r ^ 5 + 55 * r ^ 4 + 57 * r ^ 3 + 41 * r ^ 2 + 26 * r + 9)
  set c2 := 8 * r * (1 - r) ^ 5 * (1 + r) *
      (22 * r ^ 4 + 46 * r ^ 3 + 45 * r ^ 2 + 14 * r - 1)
  set c3 := 16 * r * (1 - r) ^ 5 * (1 + r) * (2 * r + 1) ^ 2
  have hid : 16 * (u + v) ^ 3 * P1 q r =
      c0 * u ^ 3 + c1 * u ^ 2 * v + c2 * u * v ^ 2 + c3 * v ^ 3 := by
    simp only [P1, u, v, c0, c1, c2, c3]; ring
  have h1r : 0 < 1 - r := by linarith
  have hc0 : 0 < c0 := by dsimp only [c0]; positivity
  have hc1 : 0 < c1 := by dsimp only [c1]; positivity
  have hc2 : 0 < c2 := by
    have h2 : 0 < 22 * r ^ 4 + 46 * r ^ 3 + 45 * r ^ 2 + 14 * r - 1 := by
      have : 0 ≤ 22 * r ^ 4 + 46 * r ^ 3 + 45 * r ^ 2 := by positivity
      linarith
    dsimp only [c2]; positivity
  have hc3 : 0 < c3 := by dsimp only [c3]; positivity
  have hrhs_pos : 0 < 16 * (u + v) ^ 3 * P1 q r := by
    rw [hid]
    rcases eq_or_lt_of_le hu with hu0 | hup
    · have hvp : 0 < v := by linarith
      have t0 : 0 ≤ c0 * u ^ 3 := by positivity
      have t1 : 0 ≤ c1 * u ^ 2 * v := by positivity
      have t2 : 0 ≤ c2 * u * v ^ 2 := by positivity
      have t3 : 0 < c3 * v ^ 3 := by positivity
      linarith
    · have t0 : 0 < c0 * u ^ 3 := by positivity
      have t1 : 0 ≤ c1 * u ^ 2 * v := by positivity
      have t2 : 0 ≤ c2 * u * v ^ 2 := by positivity
      have t3 : 0 ≤ c3 * v ^ 3 := by positivity
      linarith
  have hfac : 0 < 16 * (u + v) ^ 3 := by positivity
  nlinarith

lemma P1_pos_lo {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hhalf : r < 1 / 2)
    (hqlo : (1 - r ^ 4) / 4 ≤ q) (hq4 : q ≤ 1 / 4) :
    0 < P1 q r := by
  set u : ℝ := 1 / 4 - q
  set v : ℝ := q - (1 - r ^ 4) / 4
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have huv : 0 < u + v := by
    have : u + v = r ^ 4 / 4 := by dsimp only [u, v]; ring
    rw [this]; positivity
  set d0 := 8 * r * (1 - r) ^ 5 * (1 + r) * (r ^ 2 + 1) * (3 * r ^ 2 + 2 * r + 1) ^ 2
  set d1 := 8 * r * (1 - r) ^ 3 *
      (18 * r ^ 9 + 12 * r ^ 8 + 14 * r ^ 7 + 24 * r ^ 6 + 3 * r ^ 5 + 19 * r ^ 4 + 24 * r ^ 3 + 18 * r ^ 2 + 9 * r + 3)
  set d2 := 8 * r * (1 - r) *
      (16 * r ^ 9 + 16 * r ^ 8 - 92 * r ^ 7 + 32 * r ^ 6 - 16 * r ^ 5 - 16 * r ^ 4 + 15 * r ^ 3 + 3 * r ^ 2 + 3 * r + 3)
  set d3 := 8 * r * (1 - 6 * r ^ 4 + 2 * r ^ 3) * (1 - 12 * r ^ 4 + 8 * r ^ 3)
  have hid : 64 * (u + v) ^ 3 * P1 q r =
      d0 * u ^ 3 + d1 * u ^ 2 * v + d2 * u * v ^ 2 + d3 * v ^ 3 := by
    simp only [P1, u, v, d0, d1, d2, d3]; ring
  have hr2 : r ^ 2 < 1 / 4 := by nlinarith
  have hr4 : r ^ 4 < 1 / 16 := by nlinarith
  have hr5 : r ^ 5 < 1 / 32 := by nlinarith
  have hr7 : r ^ 7 < 1 / 128 := by nlinarith
  have h1r : 0 < 1 - r := by linarith
  have hd0 : 0 < d0 := by dsimp only [d0]; positivity
  have hd1 : 0 < d1 := by dsimp only [d1]; positivity
  have hd2 : 0 < d2 := by
    have h2 : 0 < 16 * r ^ 9 + 16 * r ^ 8 - 92 * r ^ 7 + 32 * r ^ 6 - 16 * r ^ 5 - 16 * r ^ 4 + 15 * r ^ 3 + 3 * r ^ 2 + 3 * r + 3 := by
      have hpos : 0 ≤ 16 * r ^ 9 + 16 * r ^ 8 + 32 * r ^ 6 + 15 * r ^ 3 + 3 * r ^ 2 + 3 * r := by positivity
      linarith
    dsimp only [d2]; positivity
  have hd3 : 0 < d3 := by
    have h1 : 0 < 1 - 6 * r ^ 4 + 2 * r ^ 3 := by
      have : 0 ≤ 2 * r ^ 3 := by positivity
      linarith
    have h2 : 0 < 1 - 12 * r ^ 4 + 8 * r ^ 3 := by
      have : 0 ≤ 8 * r ^ 3 := by positivity
      linarith
    dsimp only [d3]; positivity
  have hrhs_pos : 0 < 64 * (u + v) ^ 3 * P1 q r := by
    rw [hid]
    rcases eq_or_lt_of_le hu with hu0 | hup
    · have hvp : 0 < v := by linarith
      have t0 : 0 ≤ d0 * u ^ 3 := by positivity
      have t1 : 0 ≤ d1 * u ^ 2 * v := by positivity
      have t2 : 0 ≤ d2 * u * v ^ 2 := by positivity
      have t3 : 0 < d3 * v ^ 3 := by positivity
      linarith
    · have t0 : 0 < d0 * u ^ 3 := by positivity
      have t1 : 0 ≤ d1 * u ^ 2 * v := by positivity
      have t2 : 0 ≤ d2 * u * v ^ 2 := by positivity
      have t3 : 0 ≤ d3 * v ^ 3 := by positivity
      linarith
  have hfac : 0 < 64 * (u + v) ^ 3 := by positivity
  nlinarith

lemma P1_pos {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hqlo : (1 - r ^ 4) / 4 ≤ q) (hqhi : q ≤ (1 - r ^ 2) / 2) (hq4 : q ≤ 1 / 4) :
    0 < P1 q r := by
  by_cases hhalf : (1 / 2 : ℝ) ≤ r
  · exact P1_pos_hi hr0 hr1 hhalf hqlo hqhi
  · exact P1_pos_lo hr0 hr1 (lt_of_not_ge hhalf) hqlo hq4

lemma det2_DPhi_alg {a b c s r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hcs : c ^ 2 + s ^ 2 = 1) (hr4 : r ^ 4 = a ^ 4 + 2 * a ^ 2 * b ^ 2 * c + b ^ 4) :
    let Fx : ℝ := a ^ 2 + b ^ 2 * c
    let Fy : ℝ := b ^ 2 * s
    let m11 : ℝ := -2 * a ^ 3 + b ^ 3 * (1 - 3 * c ^ 2)
    let m12 : ℝ := -3 * b ^ 3 * c * s
    let m22 : ℝ := a ^ 3 + b ^ 3 * (1 - 3 * s ^ 2)
    let A11 : ℝ := r ^ 4 * m11 - 3 / 2 * (Fx * m11 + Fy * m12) * Fx
    let A21 : ℝ := r ^ 4 * m12 - 3 / 2 * (Fx * m11 + Fy * m12) * Fy
    let A12 : ℝ := r ^ 4 * m12 - 3 / 2 * (Fx * m12 + Fy * m22) * Fx
    let A22 : ℝ := r ^ 4 * m22 - 3 / 2 * (Fx * m12 + Fy * m22) * Fy
    0 < ((r ^ 7 - A11) * (r ^ 7 - A22) - A21 * A12) / r ^ 14 := by
  intro Fx Fy m11 m12 m22 A11 A21 A12 A22
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  have htr : A11 + A22 =
      (a + b) * (4 * a ^ 6 - 4 * a ^ 5 * b + 8 * a ^ 4 * b ^ 2 * c + 4 * a ^ 4 * b ^ 2 +
        9 * a ^ 3 * b ^ 3 * c ^ 2 - 8 * a ^ 3 * b ^ 3 * c - 9 * a ^ 3 * b ^ 3 +
        8 * a ^ 2 * b ^ 4 * c + 4 * a ^ 2 * b ^ 4 - 4 * a * b ^ 5 + 4 * b ^ 6) / 2 := by
    simp only [A11, A22, m11, m12, m22, Fx, Fy]
    linear_combination
      (-a ^ 3 - 3 * b ^ 3 * c ^ 2 - 3 * b ^ 3 * s ^ 2 + 2 * b ^ 3) * hr4 +
      (3 * b ^ 3 * (-2 * a ^ 4 - a ^ 3 * b + 2 * a ^ 2 * b ^ 2 * c + 3 * b ^ 4 * c ^ 2 + 3 * b ^ 4 * s ^ 2) / 2) * hs2
  have hdetA : A11 * A22 - A21 * A12 =
      r ^ 8 * ((2 * a ^ 6 + 9 * a ^ 3 * b ^ 3 * c ^ 2 - 5 * a ^ 3 * b ^ 3 + 2 * b ^ 6) / 2) := by
    have hfac : A11 * A22 - A21 * A12 =
        r ^ 4 * (r ^ 4 - 3 / 2 * (Fx ^ 2 + Fy ^ 2)) * (m11 * m22 - m12 ^ 2) := by
      simp only [A11, A22, A21, A12]; ring
    have hF2 : Fx ^ 2 + Fy ^ 2 = r ^ 4 := by
      simp only [Fx, Fy]; linear_combination b ^ 4 * hs2 - hr4
    have hDFdet : m11 * m22 - m12 ^ 2 =
        -(2 * a ^ 6 + 9 * a ^ 3 * b ^ 3 * c ^ 2 - 5 * a ^ 3 * b ^ 3 + 2 * b ^ 6) := by
      simp only [m11, m12, m22]
      linear_combination (3 * b ^ 3 * (2 * a ^ 3 - b ^ 3)) * hs2
    rw [hfac, hF2, hDFdet]; ring
  set S : ℝ := a + b
  have hS : 0 < S := by positivity
  set q : ℝ := a * b / S ^ 2
  set r1 : ℝ := r / S
  have hpoly : 8 * a * b * r ^ 7 * (((r ^ 7 - A11) * (r ^ 7 - A22) - A21 * A12) / r ^ 14) = S ^ 9 * P1 q r1 := by
    have hdiv : 8 * a * b * r ^ 7 * (((r ^ 7 - A11) * (r ^ 7 - A22) - A21 * A12) / r ^ 14) =
        8 * a * b * (r ^ 7 - (A11 + A22) + (A11 * A22 - A21 * A12) / r ^ 7) := by
      field_simp [hr.ne']; ring
    rw [hdiv, htr, hdetA]
    have hdiv2 : r ^ 8 * ((2 * a ^ 6 + 9 * a ^ 3 * b ^ 3 * c ^ 2 - 5 * a ^ 3 * b ^ 3 + 2 * b ^ 6) / 2) / r ^ 7 =
        r * (2 * a ^ 6 + 9 * a ^ 3 * b ^ 3 * c ^ 2 - 5 * a ^ 3 * b ^ 3 + 2 * b ^ 6) / 2 := by
      field_simp [hr.ne']
    rw [hdiv2]
    have hP_hom : S ^ 9 * P1 q r1 =
        -72 * (a * b) ^ 3 * r * (a + b) ^ 2 + 144 * (a * b) ^ 3 * (a + b) ^ 3 -
        36 * (a * b) ^ 2 * r ^ 5 + 84 * (a * b) ^ 2 * r ^ 4 * (a + b) +
        132 * (a * b) ^ 2 * r * (a + b) ^ 4 - 180 * (a * b) ^ 2 * (a + b) ^ 5 +
        8 * (a * b) * r ^ 7 + 72 * (a * b) * r ^ 5 * (a + b) ^ 2 -
        88 * (a * b) * r ^ 4 * (a + b) ^ 3 - 64 * (a * b) * r * (a + b) ^ 6 +
        72 * (a * b) * (a + b) ^ 7 + 9 * r ^ 9 - 9 * r ^ 8 * (a + b) -
        18 * r ^ 5 * (a + b) ^ 4 + 18 * r ^ 4 * (a + b) ^ 5 +
        9 * r * (a + b) ^ 8 - 9 * (a + b) ^ 9 := by
      simp only [P1, q, r1, S]; field_simp [hS.ne']
    rw [hP_hom]
    have hc_eq : 2 * a ^ 2 * b ^ 2 * c = r ^ 4 - a ^ 4 - b ^ 4 := by linarith only [hr4]
    dsimp only [S]
    linear_combination
      (9 * a ^ 5 - 7 * a ^ 4 * b - 9 * a ^ 4 * r - 18 * a ^ 3 * b ^ 2 * c -
        18 * a ^ 2 * b ^ 3 * c + 18 * a ^ 2 * b ^ 2 * c * r - 7 * a * b ^ 4 -
        9 * a * r ^ 4 + 9 * b ^ 5 - 9 * b ^ 4 * r - 9 * b * r ^ 4 + 9 * r ^ 5) * hc_eq
  have hr1_pos : 0 < r1 := div_pos hr hS
  have hc_lo : -1 ≤ c := by nlinarith only [hcs, sq_nonneg s]
  have hc_hi : c ≤ 1 := by nlinarith only [hcs, sq_nonneg s]
  have hq_pos : 0 < q := by positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [show q = a * b / (a + b) ^ 2 from rfl, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [sq_nonneg (a - b)]
  have hr1_4_lo : 1 - 4 * q ≤ r1 ^ 4 := by
    have h1 : (a ^ 2 - b ^ 2) ^ 2 ≤ r ^ 4 := by
      have : r ^ 4 - (a ^ 2 - b ^ 2) ^ 2 = 2 * a ^ 2 * b ^ 2 * (c + 1) := by linarith only [hr4]
      have hpos : 0 ≤ 2 * a ^ 2 * b ^ 2 * (c + 1) := by
        have : 0 ≤ c + 1 := by linarith only [hc_lo]
        positivity
      linarith only [this, hpos]
    have h2 : (1 - 4 * q) * S ^ 4 = (a ^ 2 - b ^ 2) ^ 2 := by
      simp only [q, S]; field_simp [hS.ne']; ring
    have h3 : r1 ^ 4 * S ^ 4 = r ^ 4 := by
      simp only [r1]; field_simp [hS.ne']
    have hS4 : 0 < S ^ 4 := pow_pos hS 4
    nlinarith only [h1, h2, h3, hS4]
  have hr1_4_hi : r1 ^ 4 ≤ (1 - 2 * q) ^ 2 := by
    have h1 : r ^ 4 ≤ (a ^ 2 + b ^ 2) ^ 2 := by
      have : (a ^ 2 + b ^ 2) ^ 2 - r ^ 4 = 2 * a ^ 2 * b ^ 2 * (1 - c) := by linarith only [hr4]
      have hpos : 0 ≤ 2 * a ^ 2 * b ^ 2 * (1 - c) := by
        have : 0 ≤ 1 - c := by linarith only [hc_hi]
        positivity
      linarith only [this, hpos]
    have h2 : (1 - 2 * q) ^ 2 * S ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by
      simp only [q, S]; field_simp [hS.ne']; ring
    have h3 : r1 ^ 4 * S ^ 4 = r ^ 4 := by
      simp only [r1]; field_simp [hS.ne']
    have hS4 : 0 < S ^ 4 := pow_pos hS 4
    nlinarith only [h1, h2, h3, hS4]
  have hr1_sq_hi : r1 ^ 2 ≤ 1 - 2 * q := by
    have hnn : 0 ≤ 1 - 2 * q := by linarith only [hq4]
    nlinarith only [hr1_4_hi, hnn, sq_nonneg r1]
  have hr1_lt_one : r1 < 1 := by nlinarith only [hr1_sq_hi, hq_pos, hr1_pos]
  have hP1 : 0 < P1 q r1 := P1_pos hr1_pos hr1_lt_one (by linarith only [hr1_4_lo]) (by linarith only [hr1_sq_hi]) hq4
  have hpos_lhs : 0 < 8 * a * b * r ^ 7 * (((r ^ 7 - A11) * (r ^ 7 - A22) - A21 * A12) / r ^ 14) := by
    rw [hpoly]; positivity
  have hfac : 0 < 8 * a * b * r ^ 7 := by positivity
  nlinarith only [hpos_lhs, hfac]

lemma real_inner_mul_left_unit (u x y : ℂ) (hu : ‖u‖ = 1) :
    ⟪u * x, u * y⟫ = ⟪x, y⟫ := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have := congrArg (fun t : ℝ => t ^ 2) hu
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    simpa [sq] using this
  simp only [Complex.inner, RCLike.re_to_complex, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  linear_combination (x.re * y.re + x.im * y.im) * hu2

lemma mul_conj_unit_left (u : ℂ) (hu : ‖u‖ = 1) (w : ℂ) :
    u * (starRingEnd ℂ u * w) = w := by
  have h : u * starRingEnd ℂ u = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hu]; norm_num
  rw [← mul_assoc, h, one_mul]

lemma conj_mul_unit_left (u : ℂ) (hu : ‖u‖ = 1) (w : ℂ) :
    starRingEnd ℂ u * (u * w) = w := by
  have h : starRingEnd ℂ u * u = 1 := by
    rw [Complex.conj_mul', hu]; norm_num
  rw [← mul_assoc, h, one_mul]

lemma det2_DPhi_pos {z : ℂ} (hz : z ∈ U) : 0 < det2 (DPhi z) := by
  have hz' := mem_U_iff.mp hz
  have hz1 : z + 1 ≠ 0 := fun e => hz'.1 (eq_neg_of_add_eq_zero_left e)
  have hz2 : z - 1 ≠ 0 := sub_ne_zero.mpr hz'.2.1
  have hr1 : 0 < ‖z + 1‖ := norm_pos_iff.mpr hz1
  have hr2 : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz2
  have hF0 : F z ≠ 0 := F_ne_zero hz
  have hFn : 0 < ‖F z‖ := norm_pos_iff.mpr hF0
  set a : ℝ := ‖z + 1‖⁻¹
  set b : ℝ := ‖z - 1‖⁻¹
  have ha : 0 < a := inv_pos.mpr hr1
  have hb : 0 < b := inv_pos.mpr hr2
  set u : ℂ := a • (z + 1)
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, inv_mul_cancel₀ hr1.ne']
  set v : ℂ := starRingEnd ℂ u * (b • (z - 1))
  have hv : ‖v‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, hu, one_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hb, inv_mul_cancel₀ hr2.ne']
  set c : ℝ := v.re
  set s : ℝ := v.im
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have := congrArg (fun t : ℝ => t ^ 2) hv
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    simpa [c, s, sq] using this
  have hzp1 : z + 1 = u * ((‖z + 1‖ : ℝ) : ℂ) := by
    simp only [u, Complex.real_smul]
    have : (a : ℂ) * (‖z + 1‖ : ℂ) = 1 := by
      exact_mod_cast inv_mul_cancel₀ hr1.ne'
    calc z + 1 = ((a : ℂ) * (‖z + 1‖ : ℂ)) * (z + 1) := by rw [this, one_mul]
      _ = (a : ℂ) * (z + 1) * (‖z + 1‖ : ℂ) := by ring
  have hzm1 : z - 1 = u * ((‖z - 1‖ : ℝ) • v) := by
    rw [Complex.real_smul, mul_comm ((‖z - 1‖ : ℝ) : ℂ) v, ← mul_assoc,
      mul_conj_unit_left u hu]
    simp only [Complex.real_smul]
    have : (b : ℂ) * (‖z - 1‖ : ℂ) = 1 := by
      exact_mod_cast inv_mul_cancel₀ hr2.ne'
    calc z - 1 = ((b : ℂ) * (‖z - 1‖ : ℂ)) * (z - 1) := by rw [this, one_mul]
      _ = (b : ℂ) * (z - 1) * (‖z - 1‖ : ℂ) := by ring
  have hF_rot : starRingEnd ℂ u * F z = ((a ^ 2 : ℝ) : ℂ) + (b ^ 2 : ℝ) • v := by
    simp only [F, mul_add]
    have t1 : starRingEnd ℂ u * (((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (z + 1)) = ((a ^ 2 : ℝ) : ℂ) := by
      conv_lhs => rhs; rhs; rw [hzp1]
      rw [show ((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (u * ((‖z + 1‖ : ℝ) : ℂ)) =
        u * (((‖z + 1‖ ^ 3)⁻¹ * ‖z + 1‖ : ℝ) : ℂ) by simp [Complex.real_smul]; ring]
      rw [conj_mul_unit_left u hu]
      exact_mod_cast (show (‖z + 1‖ ^ 3)⁻¹ * ‖z + 1‖ = a ^ 2 by simp [a]; field_simp [hr1.ne'])
    have t2 : starRingEnd ℂ u * (((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (z - 1)) = (b ^ 2 : ℝ) • v := by
      conv_lhs => rhs; rhs; rw [hzm1]
      rw [show ((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (u * ((‖z - 1‖ : ℝ) • v)) =
        u * ((((‖z - 1‖ ^ 3)⁻¹ * ‖z - 1‖ : ℝ)) • v) by simp [Complex.real_smul]; ring]
      rw [conj_mul_unit_left u hu]
      congr 1
      simp [b]; field_simp [hr2.ne']
    rw [t1, t2]
  set r : ℝ := Real.sqrt ‖F z‖
  have hr : 0 < r := Real.sqrt_pos.mpr hFn
  have hr4 : r ^ 4 = a ^ 4 + 2 * a ^ 2 * b ^ 2 * c + b ^ 4 := by
    have hnormF : ‖F z‖ = ‖starRingEnd ℂ u * F z‖ := by
      rw [norm_mul, Complex.norm_conj, hu, one_mul]
    have hr4' : r ^ 4 = ‖starRingEnd ℂ u * F z‖ ^ 2 := by
      rw [← hnormF, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sq_sqrt hFn.le]
    rw [hr4', Complex.sq_norm, Complex.normSq_apply, hF_rot]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.smul_re, Complex.add_im,
      Complex.ofReal_im, Complex.smul_im, zero_add, smul_eq_mul]
    change (a ^ 2 + b ^ 2 * c) * (a ^ 2 + b ^ 2 * c) + b ^ 2 * s * (b ^ 2 * s) = _
    linear_combination b ^ 4 * hcs
  have hDF_rot : ∀ w : ℂ,
      starRingEnd ℂ u * DF z (u * w) =
        ((a ^ 3 : ℝ) • w - (3 * a ^ 3 * w.re) • (1 : ℂ)) +
        ((b ^ 3 : ℝ) • w - (3 * b ^ 3 * (c * w.re + s * w.im)) • v) := by
    intro w
    simp only [DF, ContinuousLinearMap.add_apply, mul_add]
    have h1 : starRingEnd ℂ u * L_term (z + 1) (u * w) =
        (a ^ 3 : ℝ) • w - (3 * a ^ 3 * w.re) • (1 : ℂ) := by
      simp only [L_term, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, smul_eq_mul]
      have hin : ⟪z + 1, u * w⟫ = ‖z + 1‖ * w.re := by
        conv_lhs => rw [hzp1]
        rw [real_inner_mul_left_unit u ((‖z + 1‖ : ℝ) : ℂ) w hu]
        simp [Complex.inner]; ring
      rw [hin, mul_add]
      have p1 : starRingEnd ℂ u * (((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (u * w)) = (a ^ 3 : ℝ) • w := by
        rw [show ((‖z + 1‖ ^ 3)⁻¹ : ℝ) • (u * w) = u * (((‖z + 1‖ ^ 3)⁻¹ : ℝ) • w) by
          simp [Complex.real_smul]; ring]
        rw [conj_mul_unit_left u hu]; simp [a]
      have p2 : starRingEnd ℂ u * ((-3 * (‖z + 1‖ ^ 5)⁻¹ * (‖z + 1‖ * w.re)) • (z + 1)) =
          -((3 * a ^ 3 * w.re) • (1 : ℂ)) := by
        conv_lhs => rhs; rhs; rw [hzp1]
        rw [show (-3 * (‖z + 1‖ ^ 5)⁻¹ * (‖z + 1‖ * w.re)) • (u * ((‖z + 1‖ : ℝ) : ℂ)) =
          u * (((-3 * (‖z + 1‖ ^ 5)⁻¹ * (‖z + 1‖ * w.re) * ‖z + 1‖ : ℝ)) • (1 : ℂ)) by
            simp [Complex.real_smul]; ring]
        rw [conj_mul_unit_left u hu, ← neg_smul]
        congr 1; simp [a]; field_simp [hr1.ne']
      rw [p1, p2]; abel
    have h2 : starRingEnd ℂ u * L_term (z - 1) (u * w) =
        (b ^ 3 : ℝ) • w - (3 * b ^ 3 * (c * w.re + s * w.im)) • v := by
      simp only [L_term, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, smul_eq_mul]
      have hin : ⟪z - 1, u * w⟫ = ‖z - 1‖ * (c * w.re + s * w.im) := by
        conv_lhs => rw [hzm1]
        rw [real_inner_mul_left_unit u ((‖z - 1‖ : ℝ) • v) w hu]
        simp only [Complex.inner, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
          Complex.conj_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
        change w.re * (‖z - 1‖ * c) - w.im * -(‖z - 1‖ * s) = _
        ring
      rw [hin, mul_add]
      have p1 : starRingEnd ℂ u * (((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (u * w)) = (b ^ 3 : ℝ) • w := by
        rw [show ((‖z - 1‖ ^ 3)⁻¹ : ℝ) • (u * w) = u * (((‖z - 1‖ ^ 3)⁻¹ : ℝ) • w) by
          simp [Complex.real_smul]; ring]
        rw [conj_mul_unit_left u hu]; simp [b]
      have p2 : starRingEnd ℂ u * ((-3 * (‖z - 1‖ ^ 5)⁻¹ * (‖z - 1‖ * (c * w.re + s * w.im))) • (z - 1)) =
          -((3 * b ^ 3 * (c * w.re + s * w.im)) • v) := by
        conv_lhs => rhs; rhs; rw [hzm1]
        rw [show (-3 * (‖z - 1‖ ^ 5)⁻¹ * (‖z - 1‖ * (c * w.re + s * w.im))) • (u * ((‖z - 1‖ : ℝ) • v)) =
          u * (((-3 * (‖z - 1‖ ^ 5)⁻¹ * (‖z - 1‖ * (c * w.re + s * w.im)) * ‖z - 1‖ : ℝ)) • v) by
            simp [Complex.real_smul]; ring]
        rw [conj_mul_unit_left u hu, ← neg_smul]
        congr 1; simp [b]; field_simp [hr2.ne']
      rw [p1, p2]; abel
    rw [h1, h2]
    congr 1; congr 1; congr 1; ring
  set Fx : ℝ := a ^ 2 + b ^ 2 * c
  set Fy : ℝ := b ^ 2 * s
  have hF_re : (starRingEnd ℂ u * F z).re = Fx := by
    rw [hF_rot]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.smul_re, smul_eq_mul]
    rfl
  have hF_im : (starRingEnd ℂ u * F z).im = Fy := by
    rw [hF_rot]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, smul_eq_mul, zero_add]
    rfl
  have hDg_rot : ∀ y : ℂ,
      starRingEnd ℂ u * Dg (F z) (u * y) =
        (r ^ 3)⁻¹ • y - ((3 / 2 : ℝ) * (r ^ 7)⁻¹ * (Fx * y.re + Fy * y.im)) • (starRingEnd ℂ u * F z) := by
    intro y
    simp only [Dg, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, smul_eq_mul]
    have hFu : F z = u * (starRingEnd ℂ u * F z) := (mul_conj_unit_left u hu (F z)).symm
    have hin : ⟪F z, u * y⟫ = Fx * y.re + Fy * y.im := by
      conv_lhs => rw [hFu]
      rw [real_inner_mul_left_unit u (starRingEnd ℂ u * F z) y hu]
      simp only [Complex.inner, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, hF_re, hF_im]
      ring
    rw [hin, mul_add]
    have p1 : starRingEnd ℂ u * (((r ^ 3)⁻¹ : ℝ) • (u * y)) = ((r ^ 3)⁻¹ : ℝ) • y := by
      rw [show ((r ^ 3)⁻¹ : ℝ) • (u * y) = u * (((r ^ 3)⁻¹ : ℝ) • y) by
        simp [Complex.real_smul]; ring]
      rw [conj_mul_unit_left u hu]
    have p2 : starRingEnd ℂ u * (((-3 / 2 : ℝ) * (r ^ 7)⁻¹ * (Fx * y.re + Fy * y.im)) • F z) =
        -(((3 / 2 : ℝ) * (r ^ 7)⁻¹ * (Fx * y.re + Fy * y.im)) • (starRingEnd ℂ u * F z)) := by
      simp [Complex.real_smul]; ring
    change starRingEnd ℂ u * (((r ^ 3)⁻¹ : ℝ) • (u * y)) +
        starRingEnd ℂ u * (((-3 / 2 : ℝ) * (r ^ 7)⁻¹ * (Fx * y.re + Fy * y.im)) • F z) = _
    rw [p1, p2]; abel
  have hDPhi_rot : ∀ w : ℂ,
      starRingEnd ℂ u * DPhi z (u * w) =
        w - ((r ^ 3)⁻¹ • (starRingEnd ℂ u * DF z (u * w)) -
          ((3 / 2 : ℝ) * (r ^ 7)⁻¹ * (Fx * (starRingEnd ℂ u * DF z (u * w)).re +
            Fy * (starRingEnd ℂ u * DF z (u * w)).im)) • (starRingEnd ℂ u * F z)) := by
    intro w
    simp only [DPhi, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.comp_apply, mul_sub]
    rw [conj_mul_unit_left u hu w]
    have hDFu : DF z (u * w) = u * (starRingEnd ℂ u * DF z (u * w)) :=
      (mul_conj_unit_left u hu _).symm
    conv_lhs => rhs; rw [hDFu]
    rw [hDg_rot]
  set m11 : ℝ := -2 * a ^ 3 + b ^ 3 * (1 - 3 * c ^ 2)
  set m12 : ℝ := -3 * b ^ 3 * c * s
  set m22 : ℝ := a ^ 3 + b ^ 3 * (1 - 3 * s ^ 2)
  have hDF1_re : (starRingEnd ℂ u * DF z (u * 1)).re = m11 := by
    rw [hDF_rot 1]; simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.one_re,
      Complex.one_im, smul_eq_mul, mul_zero, add_zero, mul_one]; change _ = _; simp only [m11, c]; ring
  have hDF1_im : (starRingEnd ℂ u * DF z (u * 1)).im = m12 := by
    rw [hDF_rot 1]; simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, Complex.one_re,
      Complex.one_im, smul_eq_mul, mul_zero, add_zero, mul_one]; change _ = _; simp only [m12, s]; ring
  have hDFI_re : (starRingEnd ℂ u * DF z (u * I)).re = m12 := by
    rw [hDF_rot I]; simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.I_re,
      Complex.I_im, Complex.one_re, smul_eq_mul, mul_zero, zero_add, mul_one]; change _ = _; simp only [m12, c]; ring
  have hDFI_im : (starRingEnd ℂ u * DF z (u * I)).im = m22 := by
    rw [hDF_rot I]; simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, Complex.I_re,
      Complex.I_im, Complex.one_im, smul_eq_mul, mul_zero, zero_add, mul_one]; change _ = _; simp only [m22, s]; ring
  set A11 : ℝ := r ^ 4 * m11 - 3 / 2 * (Fx * m11 + Fy * m12) * Fx
  set A21 : ℝ := r ^ 4 * m12 - 3 / 2 * (Fx * m11 + Fy * m12) * Fy
  set A12 : ℝ := r ^ 4 * m12 - 3 / 2 * (Fx * m12 + Fy * m22) * Fx
  set A22 : ℝ := r ^ 4 * m22 - 3 / 2 * (Fx * m12 + Fy * m22) * Fy
  have h11 : (starRingEnd ℂ u * DPhi z u).re = (r ^ 7 - A11) / r ^ 7 := by
    rw [show DPhi z u = DPhi z (u * 1) by rw [mul_one], hDPhi_rot 1]
    simp only [Complex.sub_re, Complex.one_re, Complex.smul_re, hDF1_re, hDF1_im, hF_re, smul_eq_mul]
    simp only [A11]; field_simp [hr.ne']
  have h21 : (starRingEnd ℂ u * DPhi z u).im = -A21 / r ^ 7 := by
    rw [show DPhi z u = DPhi z (u * 1) by rw [mul_one], hDPhi_rot 1]
    simp only [Complex.sub_im, Complex.one_im, Complex.smul_im, hDF1_re, hDF1_im, hF_im, smul_eq_mul]
    simp only [A21]; field_simp [hr.ne']; ring
  have h12 : (starRingEnd ℂ u * DPhi z (u * I)).re = -A12 / r ^ 7 := by
    rw [hDPhi_rot I]
    simp only [Complex.sub_re, Complex.I_re, Complex.smul_re, hDFI_re, hDFI_im, hF_re, smul_eq_mul]
    simp only [A12]; field_simp [hr.ne']; ring
  have h22 : (starRingEnd ℂ u * DPhi z (u * I)).im = (r ^ 7 - A22) / r ^ 7 := by
    rw [hDPhi_rot I]
    simp only [Complex.sub_im, Complex.I_im, Complex.smul_im, hDFI_re, hDFI_im, hF_im, smul_eq_mul]
    simp only [A22]; field_simp [hr.ne']
  have hdet_eq : det2 (DPhi z) =
      ((r ^ 7 - A11) * (r ^ 7 - A22) - A21 * A12) / r ^ 14 := by
    rw [det2_conj_unit (DPhi z) u hu, h11, h21, h12, h22]
    field_simp [hr.ne']
  rw [hdet_eq]
  exact det2_DPhi_alg ha hb hr hcs hr4

/- Explicit inverse of a 2x2 non-singular `ℝ`-linear map on `ℂ` -/

noncomputable def equivOfDet2NeZero (L : ℂ →L[ℝ] ℂ) (hd : det2 L ≠ 0) : ℂ ≃L[ℝ] ℂ := by
  set a11 := (L 1).re
  set a21 := (L 1).im
  set a12 := (L I).re
  set a22 := (L I).im
  set d := det2 L
  let M : ℂ →L[ℝ] ℂ :=
    ((d⁻¹ * a22) • Complex.reCLM - (d⁻¹ * a12) • Complex.imCLM).smulRight (1 : ℂ) +
    ((-(d⁻¹ * a21)) • Complex.reCLM + (d⁻¹ * a11) • Complex.imCLM).smulRight I
  have hL_apply : ∀ w : ℂ, L w = (a11 * w.re + a12 * w.im) • (1 : ℂ) + (a21 * w.re + a22 * w.im) • I := by
    intro w
    have hw : w = w.re • (1 : ℂ) + w.im • I := by
      apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im]
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul]
    apply Complex.ext <;> simp [a11, a21, a12, a22, Complex.smul_re, Complex.smul_im] <;> ring
  have hM_re : ∀ w : ℂ, (M w).re = d⁻¹ * (a22 * w.re - a12 * w.im) := by
    intro w
    simp [M, Complex.smul_re]
    ring
  have hM_im : ∀ w : ℂ, (M w).im = d⁻¹ * (-a21 * w.re + a11 * w.im) := by
    intro w
    simp [M, Complex.smul_im]
    ring
  have hLM : ∀ w : ℂ, L (M w) = w := by
    intro w
    rw [hL_apply]
    have hd' : a11 * a22 - a21 * a12 = d := rfl
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.one_re, Complex.I_re,
        hM_re, hM_im, smul_eq_mul, mul_one, mul_zero, add_zero]
      field_simp [hd]
      linear_combination w.re * hd'
    · simp only [Complex.add_im, Complex.smul_im, Complex.one_im, Complex.I_im,
        hM_re, hM_im, smul_eq_mul, mul_one, mul_zero, zero_add]
      field_simp [hd]
      linear_combination w.im * hd'
  have hML : ∀ w : ℂ, M (L w) = w := by
    intro w
    have hd' : a11 * a22 - a21 * a12 = d := rfl
    apply Complex.ext
    · rw [hM_re, hL_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
      field_simp [hd]
      linear_combination w.re * hd'
    · rw [hM_im, hL_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
      field_simp [hd]
      linear_combination w.im * hd'
  exact ContinuousLinearEquiv.equivOfInverse L M hML hLM

lemma equivOfDet2NeZero_coe (L : ℂ →L[ℝ] ℂ) (hd : det2 L ≠ 0) :
    ((equivOfDet2NeZero L hd : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = L := by
  ext w; rfl

/- Covering-map local constancy of fiber cardinality on `V` -/

lemma fiber_encard_locally_constant (C₀ : ℂ) (hC₀ : C₀ ∈ V) :
    ∃ N : Set ℂ, IsOpen N ∧ C₀ ∈ N ∧
      ∀ C ∈ N, (Phi ⁻¹' {C} ∩ U).encard = (Phi ⁻¹' {C₀} ∩ U).encard := by
  classical
  obtain ⟨δ, hδ, K, hKcomp, hKU, hKsub⟩ := Phi_proper_local hC₀
  set S : Set ℂ := Phi ⁻¹' {C₀} ∩ U
  have hSK : S ⊆ K := by
    rintro z ⟨hzPhi, hzU⟩
    exact hKsub ⟨by simpa [Metric.mem_closedBall, show Phi z = C₀ from hzPhi] using hδ.le, hzU⟩
  have hIFT : ∀ z ∈ U, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (∀ y, e y = Phi y) ∧ z ∈ e.source := by
    intro z hz
    let L := equivOfDet2NeZero (DPhi z) (det2_DPhi_pos hz).ne'
    have hsf : HasStrictFDerivAt Phi (L : ℂ →L[ℝ] ℂ) z := by
      rw [equivOfDet2NeZero_coe]; exact hasStrictFDerivAt_Phi hz
    exact ⟨hsf.toOpenPartialHomeomorph Phi, fun _ => rfl, hsf.mem_toOpenPartialHomeomorph_source⟩
  have hS_comp : IsCompact S := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcomp
    have hcont : Continuous (K.restrict Phi) :=
      continuousOn_iff_continuous_restrict.mp (continuousOn_Phi.mono hKU)
    have hcl : IsClosed ((K.restrict Phi) ⁻¹' {C₀}) := isClosed_singleton.preimage hcont
    have hsub : ((Subtype.val : K → ℂ) '' ((K.restrict Phi) ⁻¹' {C₀})) = S := by
      ext z; constructor
      · rintro ⟨⟨y, hyK⟩, hyPhi, rfl⟩
        exact ⟨hyPhi, hKU hyK⟩
      · intro hz
        exact ⟨⟨z, hSK hz⟩, hz.1, rfl⟩
    rw [← hsub]
    exact hcl.isCompact.image continuous_subtype_val
  have hS_fin : S.Finite := by
    have hcov : ∀ z ∈ S, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ S ∩ W = {z} := by
      intro z hz
      obtain ⟨e, he, hzs⟩ := hIFT z hz.2
      refine ⟨e.source, e.open_source, hzs, ?_⟩
      ext y; constructor
      · rintro ⟨hyS, hys⟩
        have heq : e y = e z := by rw [he, he]; exact hyS.1.trans hz.1.symm
        exact e.injOn hys hzs heq
      · rintro rfl; exact ⟨hz, hzs⟩
    choose W₀ hW₀open hW₀mem hW₀cap using hcov
    let W' : ℂ → Set ℂ := fun z => if hz : z ∈ S then W₀ z hz else ∅
    have hW'open : ∀ z ∈ S, IsOpen (W' z) := fun z hz => by simpa [W', hz] using hW₀open z hz
    have hW'cov : S ⊆ ⋃ z ∈ S, W' z := fun z hz => Set.mem_biUnion hz (by simpa [W', hz] using hW₀mem z hz)
    obtain ⟨t, htS, htfin, htsub⟩ := hS_comp.elim_finite_subcover_image hW'open hW'cov
    have hsub : S ⊆ t := by
      intro y hy
      obtain ⟨z, hzt, hyW⟩ := Set.mem_iUnion₂.mp (htsub hy)
      have hzS : z ∈ S := htS hzt
      simp only [W', dif_pos hzS] at hyW
      have hyz : y = z := by
        have : y ∈ S ∩ W₀ z hzS := ⟨hy, hyW⟩
        rw [hW₀cap z hzS] at this
        exact this
      rwa [hyz]
    exact htfin.subset hsub
  set F₀ : Finset ℂ := hS_fin.toFinset
  have hF₀_coe : (F₀ : Set ℂ) = S := hS_fin.coe_toFinset
  choose e he_eq he_src using fun (z : ℂ) (hz : z ∈ F₀) =>
    hIFT z ((hF₀_coe ▸ hz : z ∈ S).2)
  have hrad : ∃ ρ > 0, ∀ z ∈ F₀, ∀ z' ∈ F₀, z ≠ z' → 2 * ρ ≤ dist z z' := by
    by_cases hpair : ∃ p ∈ (F₀ ×ˢ F₀).filter (fun p => p.1 ≠ p.2), True
    · set P := (F₀ ×ˢ F₀).filter (fun p => p.1 ≠ p.2)
      have hPne : P.Nonempty := by obtain ⟨p, hp, _⟩ := hpair; exact ⟨p, hp⟩
      obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image P (fun p => dist p.1 p.2) hPne
      have hpos : 0 < dist p₀.1 p₀.2 := dist_pos.mpr (Finset.mem_filter.mp hp₀).2
      refine ⟨dist p₀.1 p₀.2 / 2, by positivity, fun z hz z' hz' hne => ?_⟩
      have hmem : (z, z') ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hz'⟩, hne⟩
      have := hmin (z, z') hmem
      linarith
    · refine ⟨1, by norm_num, fun z hz z' hz' hne => ?_⟩
      exfalso; exact hpair ⟨(z, z'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hz'⟩, hne⟩, trivial⟩
  obtain ⟨ρ, hρ, hρdist⟩ := hrad
  let W : ℂ → Set ℂ := fun z => if hz : z ∈ F₀ then (e z hz).source ∩ U ∩ Metric.ball z ρ else ∅
  have hW_def : ∀ z (hz : z ∈ F₀), W z = (e z hz).source ∩ U ∩ Metric.ball z ρ := fun z hz => dif_pos hz
  have hWopen : ∀ z ∈ (F₀ : Set ℂ), IsOpen (W z) := by
    intro z hz
    have hz' : z ∈ F₀ := hz
    rw [hW_def z hz']
    exact ((e z hz').open_source.inter isOpen_U).inter Metric.isOpen_ball
  have hWmem : ∀ z (hz : z ∈ F₀), z ∈ W z := by
    intro z hz
    rw [hW_def z hz]
    exact ⟨⟨he_src z hz, (hF₀_coe ▸ hz : z ∈ S).2⟩, Metric.mem_ball_self hρ⟩
  have hWdisj : ∀ z (hz : z ∈ F₀) z' (hz' : z' ∈ F₀), z ≠ z' → Disjoint (W z) (W z') := by
    intro z hz z' hz' hne
    rw [hW_def z hz, hW_def z' hz', Set.disjoint_left]
    intro y hy hy'
    have h1 : dist y z < ρ := hy.2
    have h2 : dist y z' < ρ := hy'.2
    have h3 : dist z z' ≤ dist z y + dist y z' := dist_triangle z y z'
    rw [dist_comm z y] at h3
    have h4 := hρdist z hz z' hz' hne
    linarith
  have hImgOpen : ∀ z ∈ (F₀ : Set ℂ), IsOpen (Phi '' W z) := by
    intro z hz
    have hz' : z ∈ F₀ := hz
    have heq : Phi '' W z = (e z hz') '' W z := by
      ext y; simp [he_eq z hz']
    rw [heq]
    refine (e z hz').isOpen_image_of_subset_source (hWopen z hz) ?_
    rw [hW_def z hz']; exact fun y hy => hy.1.1
  have hImgMem : ∀ z ∈ (F₀ : Set ℂ), C₀ ∈ Phi '' W z := by
    intro z hz
    have hz' : z ∈ F₀ := hz
    exact ⟨z, hWmem z hz', (hF₀_coe ▸ hz' : z ∈ S).1⟩
  set U_union : Set ℂ := ⋃ z ∈ (F₀ : Set ℂ), W z
  have hU_open : IsOpen U_union := isOpen_biUnion hWopen
  set K' : Set ℂ := K \ U_union
  have hK'comp : IsCompact K' := hKcomp.diff hU_open
  have hPhiK'_closed : IsClosed (Phi '' K') :=
    (hK'comp.image_of_continuousOn (continuousOn_Phi.mono (diff_subset.trans hKU))).isClosed
  have hC₀_not_K' : C₀ ∉ Phi '' K' := by
    rintro ⟨y, ⟨hyK, hyU⟩, hyPhi⟩
    have hyS : y ∈ S := ⟨hyPhi, hKU hyK⟩
    have hyF : y ∈ F₀ := by rwa [← hF₀_coe] at hyS
    exact hyU (Set.mem_biUnion hyF (hWmem y hyF))
  set N : Set ℂ := Metric.ball C₀ δ ∩ (Phi '' K')ᶜ ∩ ⋂ z ∈ (F₀ : Set ℂ), Phi '' W z
  have hNopen : IsOpen N :=
    (Metric.isOpen_ball.inter hPhiK'_closed.isOpen_compl).inter
      (F₀.finite_toSet.isOpen_biInter hImgOpen)
  have hNmem : C₀ ∈ N :=
    ⟨⟨Metric.mem_ball_self hδ, hC₀_not_K'⟩, Set.mem_biInter hImgMem⟩
  refine ⟨N, hNopen, hNmem, ?_⟩
  intro C hC
  have hCball : C ∈ Metric.closedBall C₀ δ := Metric.ball_subset_closedBall hC.1.1
  have hCnotK' : C ∉ Phi '' K' := hC.1.2
  have hCimgs : ∀ z ∈ (F₀ : Set ℂ), C ∈ Phi '' W z := Set.mem_iInter₂.mp hC.2
  have hex : ∀ z (hz : z ∈ F₀), ∃ y ∈ W z, Phi y = C := fun z hz => hCimgs z hz
  choose f hfW hfPhi using hex
  let g : ℂ → ℂ := fun z => if hz : z ∈ F₀ then f z hz else 0
  have hIm : g '' (F₀ : Set ℂ) = Phi ⁻¹' {C} ∩ U := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ F₀ := hz
      have hW' := hfW z hz'
      rw [hW_def z hz'] at hW'
      simp only [g, dif_pos hz']
      exact ⟨hfPhi z hz', hW'.1.2⟩
    · rintro ⟨hyPhi, hyU⟩
      have hyK : y ∈ K := hKsub ⟨by simpa [show Phi y = C from hyPhi] using hCball, hyU⟩
      have hyInUnion : y ∈ U_union := by
        by_contra hnot
        exact hCnotK' ⟨y, ⟨hyK, hnot⟩, hyPhi⟩
      obtain ⟨z, hz, hyW⟩ := Set.mem_iUnion₂.mp hyInUnion
      have hz' : z ∈ F₀ := hz
      refine ⟨z, hz, ?_⟩
      simp only [g, dif_pos hz']
      have h1 : (e z hz') (f z hz') = (e z hz') y := by
        rw [he_eq z hz', he_eq z hz', hfPhi z hz', show Phi y = C from hyPhi]
      have hfsrc : f z hz' ∈ (e z hz').source := by
        have := hfW z hz'; rw [hW_def z hz'] at this; exact this.1.1
      have hysrc : y ∈ (e z hz').source := by
        rw [hW_def z hz'] at hyW; exact hyW.1.1
      exact (e z hz').injOn hfsrc hysrc h1
  have hInj : Set.InjOn g (F₀ : Set ℂ) := by
    intro z hz z' hz' heq
    have hz1 : z ∈ F₀ := hz
    have hz2 : z' ∈ F₀ := hz'
    simp only [g, dif_pos hz1, dif_pos hz2] at heq
    by_contra hne
    exact Set.disjoint_left.mp (hWdisj z hz1 z' hz2 hne) (hfW z hz1) (heq ▸ hfW z' hz2)
  rw [← hIm, hInj.encard_image, hF₀_coe]

lemma fiber_encard_eq_zero_fiber {C : ℂ} (hC : C ∈ V) :
    (Phi ⁻¹' {C} ∩ U).encard = (Phi ⁻¹' {0} ∩ U).encard := by
  set k : ℕ∞ := (Phi ⁻¹' {0} ∩ U).encard
  set A : Set ℂ := {x : ℂ | x ∈ V ∧ (Phi ⁻¹' {x} ∩ U).encard = k}
  set B : Set ℂ := {x : ℂ | x ∈ V ∧ (Phi ⁻¹' {x} ∩ U).encard ≠ k}
  have hAopen : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨N, hNopen, hxN, hNconst⟩ := fiber_encard_locally_constant x hx.1
    refine ⟨N ∩ V, ?_, hNopen.inter isOpen_V, hxN, hx.1⟩
    intro y ⟨hyN, hyV⟩
    exact ⟨hyV, (hNconst y hyN).trans hx.2⟩
  have hBopen : IsOpen B := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨N, hNopen, hxN, hNconst⟩ := fiber_encard_locally_constant x hx.1
    refine ⟨N ∩ V, ?_, hNopen.inter isOpen_V, hxN, hx.1⟩
    intro y ⟨hyN, hyV⟩
    exact ⟨hyV, fun h => hx.2 ((hNconst y hyN).symm.trans h)⟩
  have hVsub : V ⊆ A ∪ B := by
    intro x hx
    by_cases h : (Phi ⁻¹' {x} ∩ U).encard = k
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hdisj : Disjoint A B := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha.2)
  have h0A : (0 : ℂ) ∈ V ∩ A := ⟨by simp [mem_V_iff], by simp [mem_V_iff], rfl⟩
  have hVA : V ⊆ A :=
    isConnected_V.isPreconnected.subset_left_of_subset_union hAopen hBopen hdisj hVsub ⟨0, h0A⟩
  exact (hVA hC).2

lemma encard_fiber_le_four {C : ℂ} (hC : C ∈ V) : (Phi ⁻¹' {C} ∩ U).encard ≤ 4 := by
  rw [fiber_encard_eq_zero_fiber hC]
  exact encard_zero_fiber_le_two.trans (by norm_num)

/- Reduction from planar `H2` to the canonical complex configuration `(-1, 1, C)` -/

lemma complex_similarity_bound (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    {z : ℂ | z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
      ((‖z - a‖ ^ 3)⁻¹ : ℝ) • (z - a) + ((‖z - b‖ ^ 3)⁻¹ : ℝ) • (z - b) -
        ((‖z - c‖ ^ 3)⁻¹ : ℝ) • (z - c) = 0}.encard ≤ 4 := by
  set m : ℂ := ((2 : ℂ)⁻¹) * (a + b)
  set d : ℂ := ((2 : ℂ)⁻¹) * (b - a)
  have hd : d ≠ 0 := mul_ne_zero (inv_ne_zero two_ne_zero) (sub_ne_zero.mpr hab.symm)
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let T : ℂ → ℂ := fun z => (z - m) / d
  have hTa : T a = -1 := by
    simp only [T, m, d]
    field_simp [hd, sub_ne_zero.mpr hab.symm]
    ring
  have hTb : T b = 1 := by
    simp only [T, m, d]
    field_simp [hd, sub_ne_zero.mpr hab.symm]
    ring
  set C : ℂ := T c
  have hTinj : Function.Injective T := by
    intro z₁ z₂ h
    simp only [T] at h
    have h1 := (div_left_inj' hd).mp h
    linear_combination h1
  have hCV : C ∈ V := by
    rw [mem_V_iff]
    exact ⟨fun h => hac (hTinj (hTa.trans h.symm)), fun h => hbc (hTinj (hTb.trans h.symm))⟩
  have hsub_eq : ∀ z w : ℂ, z - w = d * (T z - T w) := by
    intro z w; simp only [T]; field_simp [hd]; ring
  have hmaps : Set.MapsTo T
      {z : ℂ | z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
        ((‖z - a‖ ^ 3)⁻¹ : ℝ) • (z - a) + ((‖z - b‖ ^ 3)⁻¹ : ℝ) • (z - b) -
          ((‖z - c‖ ^ 3)⁻¹ : ℝ) • (z - c) = 0}
      (Phi ⁻¹' {C} ∩ U) := by
    rintro z ⟨hza, hzb, hzc, heq⟩
    set w := T z
    have hwm1 : w ≠ -1 := fun h => hza (hTinj (h.trans hTa.symm))
    have hw1 : w ≠ 1 := fun h => hzb (hTinj (h.trans hTb.symm))
    have hwC : w ≠ C := fun h => hzc (hTinj h)
    have hza' : z - a = d * (w + 1) := by rw [hsub_eq z a, hTa]; ring
    have hzb' : z - b = d * (w - 1) := by rw [hsub_eq z b, hTb]
    have hzc' : z - c = d * (w - C) := by rw [hsub_eq z c]
    have hterm : ∀ u : ℂ,
        ((‖d * u‖ ^ 3)⁻¹ : ℝ) • (d * u) = (((‖d‖ ^ 3)⁻¹ : ℝ) • d) * (((‖u‖ ^ 3)⁻¹ : ℝ) • u) := by
      intro u
      rw [norm_mul, mul_pow, mul_inv]
      simp [Complex.real_smul]; ring
    rw [hza', hzb', hzc', hterm, hterm, hterm, ← mul_add, ← mul_sub] at heq
    have hfac0 : (((‖d‖ ^ 3)⁻¹ : ℝ) • d) ≠ 0 :=
      smul_ne_zero (inv_ne_zero (pow_ne_zero 3 hdn.ne')) hd
    have hFw : F w = ((‖w - C‖ ^ 3)⁻¹ : ℝ) • (w - C) :=
      sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hfac0)
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hFw
      have hF0 : F 0 = 0 := by simp [F]
      rw [hF0] at hFw
      have hne : w - C ≠ 0 := sub_ne_zero.mpr hwC
      rw [h0] at hne
      have := (smul_eq_zero.mp hFw.symm).resolve_left (inv_ne_zero (pow_ne_zero 3 (norm_ne_zero_iff.mpr hne)))
      exact hne this
    have hwU : w ∈ U := mem_U_iff.mpr ⟨hwm1, hw1, hw0⟩
    exact ⟨(Phi_eq_iff hwU).mpr ⟨hwC, hFw⟩, hwU⟩
  calc {z : ℂ | z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
          ((‖z - a‖ ^ 3)⁻¹ : ℝ) • (z - a) + ((‖z - b‖ ^ 3)⁻¹ : ℝ) • (z - b) -
            ((‖z - c‖ ^ 3)⁻¹ : ℝ) • (z - c) = 0}.encard
      ≤ (Phi ⁻¹' {C} ∩ U).encard := Set.encard_le_encard_of_injOn hmaps hTinj.injOn
    _ ≤ 4 := encard_fiber_le_four hCV

lemma norm_sub_eq_sqrt (p a : ℂ) :
    ‖p - a‖ = Real.sqrt ((p.re - a.re) ^ 2 + (p.im - a.im) ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

lemma H2_proof :
    OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.H2 := by
  intro q u w hw hq hqabs hqne _
  set m : ℝ := |q 0|
  have hm : 0 < m := abs_pos.mpr (hq 0)
  have hqsign : ∀ j : Fin 3, q j = m ∨ q j = -m := fun j =>
    (abs_eq hm.le).mp (hqabs j 0)
  let P : Fin 3 → ℂ := fun j => ⟨![0, 1, u] j, ![0, 0, w] j⟩
  have hP01 : P 0 ≠ P 1 := by
    intro h; have := congrArg Complex.re h; simp [P] at this
  have hP02 : P 0 ≠ P 2 := by
    intro h; have := congrArg Complex.im h; simp [P] at this; exact hw this.symm
  have hP12 : P 1 ≠ P 2 := by
    intro h; have := congrArg Complex.im h; simp [P] at this; exact hw this.symm
  have hsplit : ∃ (a b c : ℂ) (s : ℝ), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s ≠ 0 ∧
      ({a, b, c} : Set ℂ) = {P 0, P 1, P 2} ∧
      ∀ p : ℂ,
        (∑ j : Fin 3, q j • (((‖p - P j‖ ^ 3)⁻¹ : ℝ) • (p - P j))) =
        s • (((‖p - a‖ ^ 3)⁻¹ : ℝ) • (p - a) + ((‖p - b‖ ^ 3)⁻¹ : ℝ) • (p - b) -
          ((‖p - c‖ ^ 3)⁻¹ : ℝ) • (p - c)) := by
    rcases hqsign 0 with h0 | h0 <;> rcases hqsign 1 with h1 | h1 <;> rcases hqsign 2 with h2 | h2
    · exfalso
      obtain ⟨i, j, hij⟩ := hqne
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2] at hij
    · refine ⟨P 0, P 1, P 2, m, hP01, hP02, hP12, hm.ne', rfl, fun p => ?_⟩
      simp [Fin.sum_univ_three, h0, h1, h2, smul_add, sub_eq_add_neg]; abel
    · refine ⟨P 0, P 2, P 1, m, hP02, hP01, hP12.symm, hm.ne', by ext; simp; tauto, fun p => ?_⟩
      simp [Fin.sum_univ_three, h0, h1, h2, smul_add, sub_eq_add_neg]; abel
    · refine ⟨P 1, P 2, P 0, -m, hP12, hP01.symm, hP02.symm, neg_ne_zero.mpr hm.ne', by ext; simp; tauto, fun p => ?_⟩
      simp [Fin.sum_univ_three, h0, h1, h2, smul_add, sub_eq_add_neg]; abel
    · refine ⟨P 1, P 2, P 0, m, hP12, hP01.symm, hP02.symm, hm.ne', by ext; simp; tauto, fun p => ?_⟩
      simp [Fin.sum_univ_three, h0, h1, h2, smul_add, sub_eq_add_neg]; abel
    · refine ⟨P 0, P 2, P 1, -m, hP02, hP01, hP12.symm, neg_ne_zero.mpr hm.ne', by ext; simp; tauto, fun p => ?_⟩
      simp [Fin.sum_univ_three, h0, h1, h2, smul_add, sub_eq_add_neg]; abel
    · refine ⟨P 0, P 1, P 2, -m, hP01, hP02, hP12, neg_ne_zero.mpr hm.ne', rfl, fun p => ?_⟩
      simp [Fin.sum_univ_three, h0, h1, h2, smul_add, sub_eq_add_neg]; abel
    · exfalso
      obtain ⟨i, j, hij⟩ := hqne
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2] at hij
  obtain ⟨a, b, c, s, hab, hac, hbc, hs0, hset, hsum_eq⟩ := hsplit
  let embed : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2⟩
  have hinj : Function.Injective embed := fun p₁ p₂ h =>
    Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)
  have hmaps : Set.MapsTo embed
      {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2 ≠ 0) ∧
        ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2) ^ 3 = 0 ∧
        ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2) ^ 3 = 0}
      {z : ℂ | z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
        ((‖z - a‖ ^ 3)⁻¹ : ℝ) • (z - a) + ((‖z - b‖ ^ 3)⁻¹ : ℝ) • (z - b) -
          ((‖z - c‖ ^ 3)⁻¹ : ℝ) • (z - c) = 0} := by
    rintro p ⟨hneq, hre0, him0⟩
    have hnotP : ∀ j : Fin 3, embed p ≠ P j := by
      intro j heq
      apply hneq j
      have hr := congrArg Complex.re heq
      have hi := congrArg Complex.im heq
      simp only [embed, P] at hr hi
      rw [hr, hi]; ring
    have hne_abc : embed p ≠ a ∧ embed p ≠ b ∧ embed p ≠ c := by
      have hmem : ∀ z ∈ ({a, b, c} : Set ℂ), embed p ≠ z := by
        intro z hz
        rw [hset] at hz
        rcases hz with rfl | rfl | rfl
        · exact hnotP 0
        · exact hnotP 1
        · exact hnotP 2
      exact ⟨hmem a (by simp), hmem b (by simp), hmem c (by simp)⟩
    refine ⟨hne_abc.1, hne_abc.2.1, hne_abc.2.2, ?_⟩
    have hsum0 : (∑ j : Fin 3, q j • (((‖embed p - P j‖ ^ 3)⁻¹ : ℝ) • (embed p - P j))) = 0 := by
      apply Complex.ext
      · simp only [Complex.re_sum, Complex.smul_re, Complex.sub_re, smul_eq_mul, Complex.zero_re]
        convert hre0 using 1
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_sub_eq_sqrt (embed p) (P j)]
        simp only [embed, P]
        ring
      · simp only [Complex.im_sum, Complex.smul_im, Complex.sub_im, smul_eq_mul, Complex.zero_im]
        convert him0 using 1
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_sub_eq_sqrt (embed p) (P j)]
        simp only [embed, P]
        ring
    rw [hsum_eq (embed p)] at hsum0
    exact (smul_eq_zero.mp hsum0).resolve_left hs0
  calc {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2 ≠ 0) ∧
          ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2) ^ 3 = 0 ∧
          ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j) ^ 2 + (p.2 - ![0, 0, w] j) ^ 2) ^ 3 = 0}.encard
      ≤ {z : ℂ | z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
          ((‖z - a‖ ^ 3)⁻¹ : ℝ) • (z - a) + ((‖z - b‖ ^ 3)⁻¹ : ℝ) • (z - b) -
            ((‖z - c‖ ^ 3)⁻¹ : ℝ) • (z - c) = 0}.encard :=
        Set.encard_le_encard_of_injOn hmaps hinj.injOn
    _ ≤ 4 := complex_similarity_bound a b c hab hac hbc

end OMA.MaxwellH2

theorem OMA.solution :
    OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.H2 :=
  OMA.MaxwellH2.H2_proof
