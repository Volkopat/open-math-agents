import OMAStatements.S_mo_350545

/-!
# The sector analogue of the Gauss–Lucas theorem

Blagovest and Hristo Sendov proved the sector theorem for polynomials with
nonnegative coefficients. We follow the Descartes rule argument of Vilmos
Totik, Critical points of polynomials, Theorems 21 and 23. A continuous lift
on the compactified sector determines the terminal argument on each ray.
The open mapping theorem for the logarithmic derivative excludes a critical
point, and finite root sets give the strict boundary conclusion.

Credit: @connoranderson
-/

section

/-!
# From an open sector to angular monotonicity

Gauss–Lucas treats the convex region obtained from conjugation symmetry. The remaining
acute zero-free sectors are reduced to the radial argument monotonicity in Vilmos Totik,
Critical points of polynomials, Theorems 21 and 23, and the holomorphic open mapping theorem.
The general sector result was established by Blagovest and Hristo Sendov.

Credit: @connoranderson
-/

namespace OMA.S_mo_350545
open Real

private lemma outside_iff_norm {α : ℝ} (hα : π / 2 ≤ α) (hπ : α < π) (z : ℂ) (hz : z ≠ 0) :
    α < |z.arg| ↔ z.re < Real.cos α * ‖z‖ := by
  have hmem : α ∈ Set.Icc 0 π := ⟨by linarith [Real.pi_pos], hπ.le⟩
  have hzmem : |z.arg| ∈ Set.Icc 0 π := ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hc := Real.strictAntiOn_cos.lt_iff_gt hzmem hmem
  rw [Real.cos_abs, Complex.cos_arg hz, div_lt_iff₀ (norm_pos_iff.mpr hz)] at hc
  exact hc.symm

/-- The complement of the closed central angular sector, together with its apex,
is convex when the sector half-angle is between a right and a straight angle. -/
theorem outside_arg_convex {α : ℝ} (hα : π / 2 ≤ α) (hπ : α < π) :
    Convex ℝ {z : ℂ | z = 0 ∨ α < |z.arg|} := by
  let S := {z : ℂ | z = 0 ∨ z.re < Real.cos α * ‖z‖}
  have hs : {z : ℂ | z = 0 ∨ α < |z.arg|} = S := by
    ext z
    by_cases hz : z=0
    · simp [S,hz]
    · simp [S,hz,outside_iff_norm hα hπ z hz]
  rw [hs]
  have hc : Real.cos α ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hα (by linarith [Real.pi_pos])
  have hsum {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) : x+y ∈ S := by
    rcases hx with rfl|hx
    · simpa using hy
    rcases hy with rfl|hy
    · simpa [S] using Or.inr hx
    right
    calc
      (x+y).re = x.re + y.re := rfl
      _ < Real.cos α * (‖x‖+‖y‖) := by rw [mul_add]; exact add_lt_add hx hy
      _ ≤ Real.cos α * ‖x+y‖ := mul_le_mul_of_nonpos_left (norm_add_le x y) hc
  have hscale {a : ℝ} {x : ℂ} (ha : 0<a) (hx : x ∈ S) : a • x ∈ S := by
    rcases hx with rfl|hx
    · left; exact smul_zero _
    right
    simpa [Complex.smul_re,smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos ha,mul_left_comm]
      using mul_lt_mul_of_pos_left hx ha
  exact convex_iff_forall_pos.mpr fun x hx y hy a b ha hb _ => hsum (hscale ha hx) (hscale hb hy)

end OMA.S_mo_350545


open Real ComplexConjugate Polynomial
namespace OMA.S_mo_350545

theorem small_sector {φ : ℝ} (hφ : φ ≤ π) (z : ℂ) :
    sector φ z ∧ sector φ (conj z) ↔ (0 < φ ∧ z = 0) := by
  by_cases hz : z = 0
  · simp [hz, sector]
  have hcz : conj z ≠ 0 := by simpa using hz
  have hr := Complex.neg_pi_lt_arg z
  have hs := Complex.arg_le_pi z
  have hp := Real.pi_pos
  simp only [sector, angle, hz, hcz, false_or, and_false, iff_false, Complex.arg_conj]
  split_ifs <;> push Not <;> intros <;> grind

theorem large_sector {φ : ℝ} (hφ : π < φ) (hm : φ ≤ 2*π) (z : ℂ) :
    sector φ z ∧ sector φ (conj z) ↔ (z = 0 ∨ 2*π-φ < |z.arg|) := by
  have hp := Real.pi_pos
  have hpos : 0 < φ := by linarith
  by_cases hz : z = 0
  · simp [hz, sector, hpos]
  have hcz : conj z ≠ 0 := by simpa using hz
  have hr := Complex.neg_pi_lt_arg z
  have hs := Complex.arg_le_pi z
  simp only [sector, angle, hz, hcz, false_or, hpos, true_and, Complex.arg_conj, abs]
  split_ifs <;> rw [max_def] <;> split_ifs <;> constructor <;> intro h <;>
    (try obtain ⟨⟨_, _⟩, _, _⟩ := h) <;> (repeat' apply And.intro) <;> linarith

theorem real_gauss_lucas (p : ℝ[X]) (hp : 0 < p.natDegree) (s : Set ℂ)
    (hc : Convex ℝ s) (hr : ∀ z : ℂ, aeval z p = 0 → z ∈ s) :
    ∀ z : ℂ, aeval z p.derivative = 0 → z ∈ s := by
  let P := p.map (algebraMap ℝ ℂ)
  have hd : 0 < P.natDegree := by simpa [P] using hp
  have he : P.derivative ≠ 0 := derivative_ne_zero.mpr hd.ne'
  have hs : P.rootSet ℂ ⊆ s := by
    intro z hz
    exact hr z (by simpa [P, coe_aeval_eq_eval, eval_map_algebraMap] using (mem_rootSet.mp hz).2)
  intro z hz
  apply convexHull_min hs hc
  apply P.rootSet_derivative_subset_convexHull_rootSet (natDegree_pos_iff_degree_pos.mp hd)
  apply mem_rootSet.mpr
  refine ⟨he, ?_⟩
  simpa [P, coe_aeval_eq_eval, derivative_map, eval_map_algebraMap] using hz

theorem poly_positive_real {p : ℝ[X]} (hp : p ≠ 0) (hn : ∀ k, 0 ≤ p.coeff k)
    {x : ℝ} (hx : 0 < x) : 0 < p.eval x := by
  rw [eval_eq_sum_range]
  apply Finset.sum_pos'
  · exact fun i _ => mul_nonneg (hn _) (pow_nonneg hx.le i)
  · refine ⟨p.natDegree, Finset.mem_range.mpr (by omega), mul_pos ?_ (pow_pos hx _)⟩
    exact lt_of_le_of_ne (hn _) (leadingCoeff_ne_zero.mpr hp).symm

theorem critical_arg_ne_zero {p : ℝ[X]} (hp : 0 < p.natDegree) (hn : ∀ k, 0 ≤ p.coeff k)
    {z : ℂ} (hz : z ≠ 0) (hd : aeval z p.derivative = 0) : z.arg ≠ 0 := by
  intro ha
  obtain ⟨hre,him⟩ := Complex.arg_eq_zero_iff.mp ha
  have he : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simp [him])
  have hpos : 0 < z.re := lt_of_le_of_ne hre (fun h => hz (by rw [← he, ← h]; simp))
  have hcoeff : ∀ k, 0 ≤ p.derivative.coeff k := by
    intro k
    rw [coeff_derivative]
    exact mul_nonneg (hn _) (by positivity)
  have h := poly_positive_real (derivative_ne_zero.mpr hp.ne') hcoeff hpos
  rw [← he, ← RCLike.ofReal_eq_complex_ofReal, aeval_ofReal] at hd
  exact h.ne' (Complex.ofReal_eq_zero.mp hd)

end OMA.S_mo_350545


open Real Polynomial Filter Topology ComplexConjugate
namespace OMA.S_mo_350545

theorem strengthen_angle_set (s : Finset ℂ) (α b : ℝ) (hb : α < b)
    (hs : ∀ z ∈ s, z = 0 ∨ α < |z.arg|) :
    ∃ β, α < β ∧ β < b ∧ ∀ z ∈ s, z = 0 ∨ β < |z.arg| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨(α+b)/2, by linarith, by linarith, by simp⟩
  | insert x s hx ih =>
    obtain ⟨c,hc,hb',hr⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
    rcases hs x (Finset.mem_insert_self ..) with hz | ha
    · refine ⟨c,hc,hb',?_⟩
      intro z h
      rcases Finset.mem_insert.mp h with rfl|hm
      · exact Or.inl hz
      · exact hr z hm
    · obtain ⟨β,hl,hu⟩ := exists_between (lt_min hc ha)
      refine ⟨β,hl,(hu.trans_le (min_le_left ..)).trans hb',?_⟩
      intro z h
      rcases Finset.mem_insert.mp h with rfl|hm
      · exact Or.inr (hu.trans_le (min_le_right ..))
      · exact (hr z hm).imp_right fun e => (hu.trans_le (min_le_left ..)).trans e

theorem strengthen_roots {p : ℝ[X]} (hp : p ≠ 0) {α b : ℝ} (hab : α < b)
    (hr : ∀ z : ℂ, aeval z p = 0 → z = 0 ∨ α < |z.arg|) :
    ∃ β, α < β ∧ β < b ∧ ∀ z : ℂ, aeval z p = 0 → z = 0 ∨ β < |z.arg| := by
  classical
  let s := (p.rootSet_finite ℂ).toFinset
  have hs (z : ℂ) : z ∈ s ↔ aeval z p = 0 := by
    simp [s,mem_rootSet_of_ne hp]
  obtain ⟨β,hl,hu,h⟩ := strengthen_angle_set s α b hab (fun z hz => hr z ((hs z).mp hz))
  exact ⟨β,hl,hu,fun z hz => h z ((hs z).mpr hz)⟩

theorem drop_zero_roots
    (core : ∀ (p : ℝ[X]) (β : ℝ), (∀ k, 0 ≤ p.coeff k) → 0 < p.coeff 0 →
      0 < β → β < π/2 → (∀ z : ℂ, aeval z p = 0 → β < |z.arg|) →
      ∀ z : ℂ, 0 < z.arg → z.arg < β → 0 ≤ (z * aeval z p.derivative / aeval z p).im)
    (p : ℝ[X]) (β : ℝ) (hn : ∀ k, 0 ≤ p.coeff k) (hb : 0 < β) (hβ : β < π/2)
    (hr : ∀ z : ℂ, aeval z p = 0 → z = 0 ∨ β < |z.arg|)
    (z : ℂ) (ha : 0 < z.arg) (hu : z.arg < β) : 0 ≤ (z * aeval z p.derivative / aeval z p).im := by
  have hz : z ≠ 0 := fun e => by simp [e] at ha
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases c0 : p.coeff 0 = 0
    · by_cases h0 : p.natDegree = 0
      · have he := eq_C_of_natDegree_eq_zero h0
        rw [c0,map_zero] at he
        simp [he]
      let q := p.divX
      have he : X * q = p := by simpa only [q,c0,map_zero,add_zero] using X_mul_divX_add p
      have hq : ∀ w : ℂ, aeval w q = 0 → w = 0 ∨ β < |w.arg| := by
        intro w hw
        exact hr w (by rw [← he, map_mul,hw,mul_zero])
      have hqz : aeval z q ≠ 0 := fun h => hu.not_gt (by simpa [abs_of_pos ha] using (hq z h).resolve_left hz)
      have hlt : q.natDegree < n := by dsimp [q]; rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      have hi := ih q.natDegree hlt q (fun k => by simpa [q] using hn (k+1)) hq rfl
      have eq : z * aeval z p.derivative / aeval z p =
          1 + z * aeval z q.derivative / aeval z q := by
        rw [← he,derivative_mul]
        simp only [derivative_X, one_mul, map_add, map_mul, aeval_X]
        field_simp
      simpa [eq] using hi
    · have hc := lt_of_le_of_ne (hn 0) (Ne.symm c0)
      apply core p β hn hc hb hβ _ z ha hu
      intro w hw
      apply (hr w hw).resolve_left
      rintro rfl
      exact c0 (by simpa [aeval_def] using hw)

end OMA.S_mo_350545

namespace OMA.R_mo_350545_R1
open Real Polynomial Filter Topology ComplexConjugate OMA.S_mo_350545

/-- The ray argument of a polynomial with positive constant coefficient has nonnegative
radial derivative inside any acute zero-free sector, expressed as a logarithmic derivative. -/
def H1 : Prop := ∀ (p : ℝ[X]) (β : ℝ), (∀ k, 0 ≤ p.coeff k) → 0 < p.coeff 0 →
    0 < β → β < π/2 → (∀ z : ℂ, aeval z p = 0 → β < |z.arg|) →
    ∀ z : ℂ, 0 < z.arg → z.arg < β → 0 ≤ (z * aeval z p.derivative / aeval z p).im

/-- A logarithmic derivative that stays in the closed upper half-plane near a regular
nonzero point cannot vanish there, by the open mapping theorem. -/
def H2 : Prop := ∀ (p : ℝ[X]), 0 < p.natDegree → ∀ z : ℂ,
    z ≠ 0 → aeval z p ≠ 0 →
    (∀ᶠ w in 𝓝 z, 0 ≤ (w * aeval w p.derivative / aeval w p).im) →
    aeval z p.derivative ≠ 0

theorem main : H1 → H2 → type_of% @OMA.S_mo_350545.main := by
  intro core hop p φ hp hn hφ hm roots z hd
  have hconj (p : ℝ[X]) (w : ℂ) (h : aeval w p = 0) : aeval (conj w) p = 0 := by
    rw [aeval_conj, h, map_zero]
  have hrs (w : ℂ) (h : aeval w p = 0) := And.intro (roots w h) (roots _ (hconj p w h))
  by_cases hs : φ ≤ π
  · let s := {w : ℂ | 0 < φ ∧ w = 0}
    have hc : Convex ℝ s := by
      by_cases h : 0 < φ
      · simp [s,h]
      · simpa [s,h] using (convex_empty (𝕜 := ℝ) (E := ℂ))
    have hr (w : ℂ) (h : aeval w p = 0) : w ∈ s := (small_sector hs w).mp (hrs w h)
    exact ((small_sector hs z).mpr (real_gauss_lucas p hp s hc hr z hd)).1
  let α := 2*π-φ
  have hφ' : π < φ := lt_of_not_ge hs
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have haπ : α < π := by dsimp [α]; linarith
  have hr (w : ℂ) (h : aeval w p = 0) : w = 0 ∨ α < |w.arg| := (large_sector hφ' hm w).mp (hrs w h)
  apply ((large_sector hφ' hm z).mpr _).1
  by_cases hc : π/2 ≤ α
  · exact real_gauss_lucas p hp _ (outside_arg_convex hc haπ) hr z hd
  by_cases hz : z = 0
  · exact Or.inl hz
  right
  have harg := critical_arg_ne_zero hp hn hz hd
  obtain ⟨β,hab,hb,hrβ⟩ := strengthen_roots (ne_zero_of_natDegree_gt hp) (lt_of_not_ge hc) hr
  have hβ := hα.trans_lt hab
  have upper (w : ℂ) (hw : w ≠ 0) (hwd : aeval w p.derivative = 0) (ha : 0 < w.arg) : α < w.arg := by
    by_contra! hle
    have hu := hle.trans_lt hab
    have hnr : aeval w p ≠ 0 := fun h =>
      ((hrβ w h).resolve_left hw).not_ge (by simpa [abs_of_pos ha] using hu.le)
    have hsl : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff_arg.mpr ⟨by linarith [Real.pi_pos],hw⟩
    have hcont := Complex.continuousAt_arg hsl
    have hlow := hcont.eventually (lt_mem_nhds ha)
    have hhigh := hcont.eventually (gt_mem_nhds hu)
    apply hop p hp w hw hnr _ hwd
    filter_upwards [hlow,hhigh] with a h1 h2
    exact drop_zero_roots core p β hn hβ hb hrβ a h1 h2
  rcases lt_or_gt_of_ne harg with ha|ha
  · have hcz : conj z ≠ 0 := by simpa using hz
    have e : (conj z).arg = -z.arg := by rw [Complex.arg_conj, if_neg (by linarith [Real.pi_pos])]
    have h := upper (conj z) hcz (hconj p.derivative z hd) (by rw [e]; linarith)
    simpa [e,abs_of_neg ha] using h
  · simpa [abs_of_pos ha] using upper z hz hd ha

end OMA.R_mo_350545_R1
end

section

open Filter Topology Polynomial
namespace OMA.S_mo_350545

theorem exclude_critical_halfplane (p : ℝ[X]) (hp : 0 < p.natDegree) (z : ℂ)
    (hz : z ≠ 0) (hr : aeval z p ≠ 0)
    (hi : ∀ᶠ w in 𝓝 z, 0 ≤ (w * aeval w p.derivative / aeval w p).im) :
    aeval z p.derivative ≠ 0 := by
  intro h
  let f := fun w : ℂ => w * aeval w p.derivative / aeval w p
  have hf : AnalyticAt ℂ f z :=
    (analyticAt_id.mul (analyticAt_id.aeval_polynomial p.derivative)).div
      (analyticAt_id.aeval_polynomial p) hr
  have hzero : f z = 0 := by simp [f,h]
  rcases hf.eventually_constant_or_nhds_le_map_nhds with hc|ho
  · have hnr : ∀ᶠ w in 𝓝 z, aeval w p ≠ 0 :=
      ((analyticAt_id (𝕜 := ℂ)).aeval_polynomial p).continuousAt.eventually_ne hr
    have hw : ∀ᶠ w in 𝓝 z, w ≠ 0 := eventually_ne_nhds hz
    have hn : p.derivative.rootSet ℂ ∈ 𝓝 z := by
      filter_upwards [hc,hnr,hw] with w hfw hwr hwz
      rw [hzero] at hfw
      apply (mem_rootSet_of_ne (derivative_ne_zero.mpr hp.ne')).mpr
      exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hfw).resolve_right hwr)).resolve_left hwz
    exact (infinite_of_mem_nhds z hn) (p.derivative.rootSet_finite ℂ)
  · rw [hzero] at ho
    have hn : {w : ℂ | 0 ≤ w.im} ∈ 𝓝 (0 : ℂ) := ho hi
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hn
    have hb : -(ε/2 : ℝ) * Complex.I ∈ Metric.ball (0:ℂ) ε := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul]
      simp [abs_of_pos hε]
      linarith
    have hc := he hb
    simp only [Set.mem_ofPred_eq, Complex.mul_im, Complex.neg_re,
      Complex.ofReal_re,Complex.I_im, mul_one, Complex.neg_im,
      Complex.ofReal_im, neg_zero, Complex.I_re, zero_mul, add_zero] at hc
    linarith

end OMA.S_mo_350545
end

section

open Real Polynomial
namespace OMA.S_mo_350545

lemma zero_free_polar {p : ℝ[X]} {θ β : ℝ} (hθ : θ < β) (hβ : β < π/2)
    (hr : ∀ z : ℂ, aeval z p = 0 → β < |z.arg|) :
    ∀ t γ : ℝ, 0 ≤ t → 0 ≤ γ → γ ≤ θ →
    aeval ((t : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)) p ≠ 0 := by
  intro t γ ht hg hγ hz
  have h := hr _ hz
  rcases ht.eq_or_lt with ht|ht
  · simp [← ht] at h
    linarith
  · have he := (toIocMod_eq_self Real.two_pi_pos).mpr (show γ ∈ Set.Ioc (-π) (-π + 2*π) by constructor <;> linarith [Real.pi_pos])
    rw [Complex.arg_real_mul _ ht, Complex.arg_exp_mul_I, he, abs_of_nonneg hg] at h
    linarith

end OMA.S_mo_350545
end

section

/-! Coefficient sign changes on a ray in the proof of Theorem 23 of
V. Totik, *Critical points of polynomials*. -/

namespace OMA.Sector
open Polynomial

/-- The sign can only change when a nondecreasing integer label increases. -/
theorem signVariations_le_label (P : ℝ[X]) (b : ℕ → ℤ) (hb : Monotone b)
    (h₀ : 0 ≤ b 0) (s : ℤ → SignType)
    (hs : ∀ i ∈ P.support, SignType.sign (P.coeff i) = s (b i)) :
    (P.signVariations : ℤ) ≤ b P.natDegree := by
  by_cases hp : P = 0
  · simpa [hp] using h₀
  have hpL := leadingCoeff_ne_zero.mpr hp
  have hbase := h₀.trans (hb (Nat.zero_le P.natDegree))
  by_cases he : P.eraseLead = 0
  · rw [signVariations_eq_eraseLead_add_ite hp]
    simpa [he, hpL] using hbase
  have hem := natDegree_mem_support_of_nonzero he
  have hd := lt_natDegree_of_mem_eraseLead_support hem
  have hcoeff : ∀ i ∈ P.eraseLead.support, P.eraseLead.coeff i = P.coeff i := by
    intro i hi
    exact P.eraseLead_coeff_of_ne i (ne_natDegree_of_mem_eraseLead_support hi)
  have hi := signVariations_le_label P.eraseLead b hb h₀ s (by
    intro i hi
    rw [hcoeff i hi]
    exact hs i (by simpa only [mem_support_iff, ← hcoeff i hi] using hi))
  have hbnd := hb hd.le
  rw [signVariations_eq_eraseLead_add_ite hp]
  split_ifs with hsign
  · have hne : b P.eraseLead.natDegree ≠ b P.natDegree := by
      intro hsame
      have ha := hs P.natDegree (natDegree_mem_support_of_nonzero hp)
      have hb' := hs P.eraseLead.natDegree (by
        simpa only [mem_support_iff, ← hcoeff _ hem] using hem)
      rw [← hcoeff _ hem, hsame] at hb'
      change SignType.sign P.leadingCoeff = _ at ha
      change SignType.sign P.eraseLead.leadingCoeff = _ at hb'
      have hself : SignType.sign P.leadingCoeff = -SignType.sign P.leadingCoeff := by
        exact hsign.trans (congrArg Neg.neg (hb'.trans ha.symm))
      exact hpL (sign_eq_zero_iff.mp (SignType.neg_eq_self_iff.mp hself.symm))
    omega
  · omega
termination_by P.support.card
decreasing_by exact eraseLead_support_card_lt hp

private lemma sine_sign (z c : ℝ) (hc : 0 ≤ c) (hn : c * Real.sin z ≠ 0) :
    SignType.sign (c * Real.sin z) = SignType.sign ((-1:ℝ) ^ ⌊z/Real.pi⌋) := by
  let k := ⌊z/Real.pi⌋
  have ht₀ : (k:ℝ)*Real.pi ≤ z := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le _)
  have ht₁ : z < ((k:ℝ)+1)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one _)
  have hre : Real.sin z = (-1:ℝ)^k * Real.sin (z-(k:ℝ)*Real.pi) := by
    simpa only [sub_add_cancel] using Real.sin_add_int_mul_pi (z-(k:ℝ)*Real.pi) k
  have ht : 0 < z-(k:ℝ)*Real.pi := by
    apply lt_of_le_of_ne (sub_nonneg.mpr ht₀)
    intro hz
    rw [hre, ← hz, Real.sin_zero, mul_zero, mul_zero] at hn
    contradiction
  have hsi := Real.sin_pos_of_pos_of_lt_pi ht (by linarith)
  have hc' : 0 < c := lt_of_le_of_ne hc (fun h => hn (by rw [← h, zero_mul]))
  rw [hre]
  simp only [sign_mul, sign_pos hc', sign_pos hsi, one_mul, mul_one, k]

/-- The floor plus one counts the levels ψ + mπ crossed by the ray through
degree n, including a possible endpoint at nθ. -/
theorem sine_signVariations_le (P : ℝ[X]) (n : ℕ) (θ ψ : ℝ) (hθ : 0 < θ)
    (hψπ : ψ < Real.pi) (hdeg : P.natDegree ≤ n)
    (hcoeff : ∀ j ≤ n, ∃ c : ℝ, 0 ≤ c ∧ P.coeff j = c * Real.sin ((j:ℝ)*θ-ψ)) :
    (P.signVariations : ℤ) ≤ ⌊((n:ℝ)*θ-ψ)/Real.pi⌋ + 1 := by
  let b (j : ℕ) : ℤ := ⌊((j:ℝ)*θ-ψ)/Real.pi⌋ + 1
  have hb : Monotone b := by
    intro i j hij
    apply add_le_add_left
    apply Int.floor_mono
    gcongr
  have h₀ : 0 ≤ b 0 := by
    have hlow : (-1:ℤ) ≤ ⌊((0:ℝ)*θ-ψ)/Real.pi⌋ := by
      apply Int.le_floor.mpr
      rw [le_div_iff₀ Real.pi_pos]
      norm_num
      linarith
    simpa [b] using (by omega : 0 ≤ ⌊((0:ℝ)*θ-ψ)/Real.pi⌋ + 1)
  apply (signVariations_le_label P b hb h₀ (fun m => SignType.sign ((-1:ℝ)^(m-1))) ?_).trans (hb hdeg)
  intro j hj
  obtain ⟨c,hc,hval⟩ := hcoeff j ((le_natDegree_of_mem_supp j hj).trans hdeg)
  have hn := mem_support_iff.mp hj
  rw [hval] at hn ⊢
  simpa [b] using sine_sign ((j:ℝ)*θ-ψ) c hc hn

/-- Natural levels whose heights are strictly between the endpoint ray arguments. -/
noncomputable def rayLevels (n : ℕ) (θ ψ : ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun k => ψ + (k:ℝ)*Real.pi < (n:ℝ)*θ)

theorem rayLevels_eq_range (n : ℕ) (θ ψ : ℝ) (hθ : θ < Real.pi) (hψ : 0 < ψ)
    (havoid : ∀ k : ℕ, ψ+(k:ℝ)*Real.pi ≠ (n:ℝ)*θ) :
    rayLevels n θ ψ = Finset.range (⌊((n:ℝ)*θ-ψ)/Real.pi⌋+1).toNat := by
  ext k
  simp only [rayLevels, Finset.mem_filter, Finset.mem_range]
  have hk : (k:ℤ) ≤ ⌊((n:ℝ)*θ-ψ)/Real.pi⌋ ↔ ψ+(k:ℝ)*Real.pi < (n:ℝ)*θ := by
    rw [Int.le_floor, le_div_iff₀ Real.pi_pos]
    push_cast
    constructor
    · intro h
      exact lt_of_le_of_ne (by linarith) (havoid k)
    · intro h
      linarith
  constructor
  · rintro ⟨_,h⟩
    have := hk.mpr h
    omega
  · intro h
    have hl := hk.mp (by omega)
    refine ⟨?_,hl⟩
    by_contra! hnk
    have hn' : (n:ℝ) ≤ k := by exact_mod_cast hnk
    have H := mul_le_mul_of_nonneg_right hn' Real.pi_pos.le
    have H' := mul_le_mul_of_nonneg_left hθ.le (show 0 ≤ (n:ℝ) by positivity)
    linarith

/-- Descartes' rule on the ray, counting positive roots with multiplicity. -/
theorem sine_roots_countP_le_levels (P : ℝ[X]) (n : ℕ) (θ ψ : ℝ)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) (hψ : 0 < ψ) (hψπ : ψ < Real.pi)
    (hdeg : P.natDegree ≤ n)
    (hcoeff : ∀ j ≤ n, ∃ c : ℝ, 0 ≤ c ∧ P.coeff j = c * Real.sin ((j:ℝ)*θ-ψ))
    (havoid : ∀ k : ℕ, ψ+(k:ℝ)*Real.pi ≠ (n:ℝ)*θ) :
    P.roots.countP (0 < ·) ≤ (rayLevels n θ ψ).card := by
  have h := sine_signVariations_le P n θ ψ hθ hψπ hdeg hcoeff
  rw [rayLevels_eq_range n θ ψ hθπ hψ havoid, Finset.card_range]
  exact (roots_countP_pos_le_signVariations (P := P)).trans (by omega)

end OMA.Sector
end

section

/-! Crossing count for the continuous argument in Totik's proof of the sector theorem. -/

namespace OMA.Sector
open Set Filter
open scoped Topology

/-- A translate of the π-lattice meeting a prescribed open interval and avoiding
all sample angles jθ. The first coordinate is the representative in (0, π). -/
theorem exists_generic_ray_level {a b : ℝ} (h : a < b) (θ : ℝ) :
    ∃ ψ : ℝ, 0 < ψ ∧ ψ < Real.pi ∧
      (∀ j : ℕ, ∀ m : ℤ, ψ+(m:ℝ)*Real.pi ≠ (j:ℝ)*θ) ∧
      ∃ k : ℤ, ψ+(k:ℝ)*Real.pi ∈ Ioo a b := by
  let u (p : ℕ × ℤ) := (p.1:ℝ)*θ + (p.2:ℝ)*Real.pi
  have hd := (countable_range u).dense_compl ℝ
  obtain ⟨y,hy,hyI⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr h)
  let k := ⌊y/Real.pi⌋
  let ψ := y-(k:ℝ)*Real.pi
  have hyre : ψ+(k:ℝ)*Real.pi = y := sub_add_cancel _ _
  have hk₁ := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le (y/Real.pi))
  have hk₂ := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one (y/Real.pi))
  change (k:ℝ)*Real.pi ≤ y at hk₁
  change y < ((k:ℝ)+1)*Real.pi at hk₂
  have hgen : ∀ j : ℕ, ∀ m : ℤ, ψ+(m:ℝ)*Real.pi ≠ (j:ℝ)*θ := by
    intro j m hm
    apply hy
    refine ⟨(j,k-m), ?_⟩
    dsimp [u]
    push_cast
    linarith
  refine ⟨ψ,?_,?_,hgen,k,hyre ▸ hyI⟩
  · apply lt_of_le_of_ne (sub_nonneg.mpr hk₁)
    intro he
    exact hgen 0 0 (by simpa using (show ψ = 0 from he.symm))
  · dsimp [ψ]
    linarith

/-- If every generic π-lattice is hit at most once for each of its levels
between the endpoint arguments, the argument cannot decrease. Here T may
contain extra positive times, as when it consists of polynomial roots. -/
theorem monotoneOn_of_ray_crossing_bound (F : ℝ → ℝ) (n : ℕ) (θ : ℝ)
    (hF : ContinuousOn F (Ici 0)) (hzero : F 0 = 0)
    (hlim : Tendsto F atTop (𝓝 ((n:ℝ)*θ)))
    (hcount : ∀ ψ : ℝ, 0 < ψ → ψ < Real.pi →
      (∀ j : ℕ, j ≤ n → ∀ m : ℤ, ψ+(m:ℝ)*Real.pi ≠ (j:ℝ)*θ) →
      ∃ T : Finset ℝ, T.card ≤ (rayLevels n θ ψ).card ∧
        ∀ t : ℝ, 0 < t → ∀ m : ℤ, F t = ψ+(m:ℝ)*Real.pi → t ∈ T) :
    MonotoneOn F (Ici 0) := by
  classical
  intro a ha b hb hab
  by_contra! h
  obtain ⟨ψ,hψ,hψπ,hgeneric,k,hk⟩ := exists_generic_ray_level h θ
  obtain ⟨T,hcard,hT⟩ := hcount ψ hψ hψπ (fun j _ => hgeneric j)
  obtain ⟨v,hv,hFv⟩ := intermediate_value_Ioo' hab (hF.mono (fun z hz => ha.trans hz.1)) hk
  have hvT := hT v (ha.trans_lt hv.1) k hFv
  let level (j : ℕ) := ψ+(j:ℝ)*Real.pi
  have hli : Function.Injective level := by
    intro i j h
    dsimp [level] at h
    have he : (i:ℝ)*Real.pi = (j:ℝ)*Real.pi := by linarith
    exact_mod_cast (mul_right_cancel₀ Real.pi_ne_zero he)
  have hsubset : (rayLevels n θ ψ).image level ⊆ (T.erase v).image F := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    have hjtop : level j < (n:ℝ)*θ := (Finset.mem_filter.mp hj).2
    have hjpos : F 0 < level j := by
      rw [hzero]; dsimp [level]; positivity
    by_cases he : (j:ℤ) = k
    · have hjlo : level j < F a := by
        simpa only [level, ← he, Int.cast_natCast] using hk.2
      obtain ⟨t,ht,hFt⟩ := intermediate_value_Ioo ha (hF.mono (fun z hz => hz.1))
        (show level j ∈ Ioo (F 0) (F a) from ⟨hjpos,hjlo⟩)
      exact Finset.mem_image.mpr ⟨t,Finset.mem_erase.mpr
        ⟨(ht.2.trans hv.1).ne, hT t ht.1 j (by simpa [level] using hFt)⟩,hFt⟩
    · obtain ⟨r,hr,hrF⟩ := ((eventually_gt_atTop (0:ℝ)).and
          (hlim.eventually (lt_mem_nhds hjtop))).exists
      obtain ⟨t,ht,hFt⟩ := intermediate_value_Ioo hr.le (hF.mono (fun z hz => hz.1))
        (show level j ∈ Ioo (F 0) (F r) from ⟨hjpos,hrF⟩)
      apply Finset.mem_image.mpr
      refine ⟨t,Finset.mem_erase.mpr ⟨?_, hT t ht.1 j (by simpa [level] using hFt)⟩,hFt⟩
      rintro rfl
      apply he
      have heq : (j:ℝ)*Real.pi = (k:ℝ)*Real.pi := by dsimp [level] at hFt; linarith
      exact_mod_cast (mul_right_cancel₀ Real.pi_ne_zero heq)
  have hle := (Finset.card_le_card hsubset).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ hli] at hle
  have hlt := Finset.card_erase_lt_of_mem hvT
  omega

/-- Polynomial version of the crossing criterion. Only inclusion of the
crossings in the real roots is needed. -/
theorem monotoneOn_of_sine_ray_polynomials (F : ℝ → ℝ) (n : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (hF : ContinuousOn F (Ici 0)) (hzero : F 0 = 0)
    (hlim : Tendsto F atTop (𝓝 ((n:ℝ)*θ)))
    (hpoly : ∀ ψ : ℝ, 0 < ψ → ψ < Real.pi →
      (∀ j : ℕ, j ≤ n → ∀ m : ℤ, ψ+(m:ℝ)*Real.pi ≠ (j:ℝ)*θ) →
      ∃ P : Polynomial ℝ, P ≠ 0 ∧ P.natDegree ≤ n ∧
        (∀ j ≤ n, ∃ c : ℝ, 0 ≤ c ∧ P.coeff j = c * Real.sin ((j:ℝ)*θ-ψ)) ∧
        ∀ t : ℝ, 0 < t → ∀ m : ℤ, F t = ψ+(m:ℝ)*Real.pi → P.IsRoot t) :
    MonotoneOn F (Ici 0) := by
  classical
  apply monotoneOn_of_ray_crossing_bound F n θ hF hzero hlim
  intro ψ hψ hψπ havoid
  obtain ⟨P,hP,hdeg,hcoeff,hroot⟩ := hpoly ψ hψ hψπ havoid
  let S := P.roots.filter (0 < ·)
  refine ⟨S.toFinset, (Multiset.toFinset_card_le _).trans ?_, ?_⟩
  · have H := sine_roots_countP_le_levels P n θ ψ hθ hθπ hψ hψπ hdeg hcoeff
        (fun k => by simpa using havoid n le_rfl k)
    rwa [Multiset.countP_eq_card_filter] at H
  · intro t ht m hm
    exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP).mpr (hroot t ht m hm), ht⟩)

end OMA.Sector
end

section

namespace OMA.S_mo_350545

open Polynomial Finset Complex Real

noncomputable def sineProjection (p : ℝ[X]) (θ ψ : ℝ) : ℝ[X] :=
  ∑ j ∈ range (p.natDegree+1), monomial j (p.coeff j * Real.sin ((j:ℝ)*θ-ψ))

theorem sineProjection_coeff (p : ℝ[X]) (θ ψ : ℝ) (j : ℕ) :
    (sineProjection p θ ψ).coeff j = p.coeff j * Real.sin ((j:ℝ)*θ-ψ) := by
  by_cases h : j ≤ p.natDegree
  · simp [sineProjection,coeff_monomial,mem_range.mpr (by omega : j<p.natDegree+1)]
  · simp [sineProjection,coeff_monomial,show j∉range (p.natDegree+1) by simp; omega,
      coeff_eq_zero_of_natDegree_lt (lt_of_not_ge h)]

private lemma rayCis_mul (c d : ℝ) : Complex.exp ((c:ℂ)*I) * Complex.exp ((d:ℂ)*I) =
    Complex.exp (((c+d:ℝ):ℂ)*I) := by rw [← Complex.exp_add]; push_cast; ring_nf

private lemma rayCis_im (c : ℝ) : (Complex.exp ((c:ℂ)*I)).im = Real.sin c := by
  simp [Complex.exp_mul_I,← Complex.ofReal_sin]

theorem sineProjection_eval (p : ℝ[X]) (θ ψ t : ℝ) :
    (sineProjection p θ ψ).eval t =
      (Complex.exp (((-ψ:ℝ):ℂ)*I) *
        Polynomial.aeval ((t:ℂ)*Complex.exp ((θ:ℂ)*I)) p).im := by
  rw [show Polynomial.aeval ((t:ℂ)*Complex.exp ((θ:ℂ)*I)) p =
    p.eval₂ (algebraMap ℝ ℂ) ((t:ℂ)*Complex.exp ((θ:ℂ)*I)) by rfl,
    Polynomial.eval₂_eq_sum_range,Finset.mul_sum,Complex.im_sum]
  simp only [sineProjection,eval_finsetSum,eval_monomial]
  apply sum_congr rfl
  intro j _
  rw [mul_pow, ← Complex.exp_nat_mul]
  have hcis : Complex.exp ((j:ℂ)*((θ:ℂ)*I)) = Complex.exp ((((j:ℝ)*θ:ℝ):ℂ)*I) := by
    congr 1; push_cast; ring
  rw [hcis]
  have he : Complex.exp (((-ψ:ℝ):ℂ)*I) * ((algebraMap ℝ ℂ) (p.coeff j) *
      ((t:ℂ)^j * Complex.exp ((((j:ℝ)*θ:ℝ):ℂ)*I))) =
      ((p.coeff j*t^j:ℝ):ℂ)*Complex.exp (((((j:ℝ)*θ-ψ):ℝ):ℂ)*I) := by
    rw [show (j:ℝ)*θ-ψ= -ψ+(j:ℝ)*θ by ring,← rayCis_mul]
    push_cast
    change _ * ((p.coeff j : ℂ) * _) = _
    ring
  rw [he,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,rayCis_im]
  ring

/-- A nonzero polynomial detecting all phase crossings of the ray at ψ modulo π. -/
theorem phase_crossing_polynomial (p : ℝ[X]) (θ ψ : ℝ) (F : ℝ → ℝ)
    (hc : 0 < p.coeff 0) (hn : ∀ j, 0 ≤ p.coeff j) (hψ : 0<ψ) (hπ : ψ<π)
    (hphase : ∀ t, 0 ≤ t → Complex.exp ((F t:ℂ)*I) =
      Polynomial.aeval ((t:ℂ)*Complex.exp ((θ:ℂ)*I)) p /
      (‖Polynomial.aeval ((t:ℂ)*Complex.exp ((θ:ℂ)*I)) p‖:ℂ)) :
    ∃ Q : ℝ[X], Q ≠ 0 ∧ Q.natDegree ≤ p.natDegree ∧
      (∀ j ≤ p.natDegree, ∃ c : ℝ, 0 ≤ c ∧ Q.coeff j = c * Real.sin ((j:ℝ)*θ-ψ)) ∧
      ∀ t, 0<t → ∀ m : ℤ, F t=ψ+(m:ℝ)*π → Q.IsRoot t := by
  refine ⟨sineProjection p θ ψ,?_,?_,fun j _ => ⟨p.coeff j,hn j,sineProjection_coeff ..⟩,?_⟩
  · intro hz
    have h := sineProjection_coeff p θ ψ 0
    simp [hz, mul_eq_zero, ne_of_gt hc, ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hψ hπ)] at h
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [sineProjection_coeff,coeff_eq_zero_of_natDegree_lt hj,zero_mul]
  · intro t ht m hm
    let Z := Polynomial.aeval ((t:ℂ)*Complex.exp ((θ:ℂ)*I)) p
    have hnorm : Z ≠ 0 := by
      intro hz
      have hp := hphase t ht.le
      change Complex.exp ((F t:ℂ)*I) = Z/(‖Z‖:ℂ) at hp
      simp [hz, Complex.exp_ne_zero] at hp
    have he : Z = Complex.exp ((F t:ℂ)*I)*(‖Z‖:ℂ) :=
      ((eq_div_iff (by exact_mod_cast (norm_ne_zero_iff.mpr hnorm))).mp (hphase t ht.le)).symm
    rw [Polynomial.IsRoot,sineProjection_eval]
    change (Complex.exp (((-ψ:ℝ):ℂ)*I)*Z).im=0
    rw [he,← mul_assoc,rayCis_mul,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add,rayCis_im,hm]
    simp [show -ψ+(ψ+(m:ℝ)*π)=(m:ℝ)*π by ring,Real.sin_int_mul_pi]

end OMA.S_mo_350545
end

section

/-! A nondecreasing continuous choice of phase forces a nonnegative angular
velocity. Only the complex-valued curve itself needs to be differentiable. -/

namespace OMA.Sector
open Set Filter
open scoped Topology

theorem im_logDeriv_nonneg_of_monotone_phase (g : ℝ → ℂ) (F : ℝ → ℝ)
    {t : ℝ} (ht : 0 < t) {d : ℂ} (hd : HasDerivAt g d t) (hne : g t ≠ 0)
    (hc : ContinuousOn F (Ici 0)) (hm : MonotoneOn F (Ici 0))
    (harg : ∀ s : ℝ, 0 ≤ s →
      g s = (‖g s‖ : ℂ) * Complex.exp ((F s:ℂ)*Complex.I)) :
    0 ≤ (d / g t).im := by
  let f (s : ℝ) := (g s / g t).im
  have hf : HasDerivAt f (d/g t).im t := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd.div_const (g t))
  have htend := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  apply ge_of_tendsto htend
  have hct : Tendsto F (𝓝[>] t) (𝓝 (F t)) :=
    (hc t ht.le).mono_left (nhdsWithin_mono _ (fun s hs => ht.le.trans hs.le))
  have hlt : ∀ᶠ s in 𝓝[>] t, F s < F t + Real.pi :=
    hct.eventually (gt_mem_nhds (by linarith [Real.pi_pos]))
  filter_upwards [self_mem_nhdsWithin, hlt] with s hs hsb
  change t < s at hs
  have hs₀ := (ht.trans hs).le
  have hangle : 0 ≤ Real.sin (F s - F t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr (hm ht.le hs₀ hs.le)) (by linarith)
  have heq : g s / g t =
      ((‖g s‖/‖g t‖ : ℝ):ℂ)*Complex.exp (((F s-F t:ℝ):ℂ)*Complex.I) := by
    rw [Complex.ofReal_div, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    exact (congrArg₂ (· / ·) (harg s hs₀) (harg t ht.le)).trans (mul_div_mul_comm ..)
  have hfpos : 0 ≤ f s := by
    dsimp only [f]
    rw [heq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im]
    exact mul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) hangle
  have hft : f t = 0 := by simp [f,hne]
  rw [slope_def_field, hft, sub_zero]
  exact div_nonneg hfpos (sub_nonneg.mpr hs.le)

/-- Logarithmic derivative on a ray under the normalized phase convention. -/
theorem polynomial_im_ray_logDeriv_nonneg (P : Polynomial ℝ) (ξ : ℂ) (F : ℝ → ℝ)
    {t : ℝ} (ht : 0 < t) (hne : Polynomial.aeval ((t:ℂ)*ξ) P ≠ 0)
    (hc : ContinuousOn F (Ici 0)) (hm : MonotoneOn F (Ici 0))
    (hphase : ∀ s : ℝ, 0 ≤ s → Complex.exp ((F s:ℂ)*Complex.I) =
      Polynomial.aeval ((s:ℂ)*ξ) P / (‖Polynomial.aeval ((s:ℂ)*ξ) P‖ : ℂ)) :
    0 ≤ (ξ * Polynomial.aeval ((t:ℂ)*ξ) P.derivative /
      Polynomial.aeval ((t:ℂ)*ξ) P).im := by
  let g (s : ℝ) := Polynomial.aeval ((s:ℂ)*ξ) P
  have hdC : HasDerivAt (fun w : ℂ => Polynomial.aeval (w*ξ) P)
      (ξ * Polynomial.aeval ((t:ℂ)*ξ) P.derivative) (t:ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => w*ξ) ξ (t:ℂ) := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id (t:ℂ)).mul_const ξ)
    simpa only [Function.comp_def, smul_eq_mul, mul_comm (Polynomial.aeval ((t:ℂ)*ξ) P.derivative) ξ]
      using (P.hasDerivAt_aeval ((t:ℂ)*ξ)).comp (t:ℂ) h1
  apply im_logDeriv_nonneg_of_monotone_phase g F ht hdC.comp_ofReal hne hc hm
  intro s hs
  rw [hphase s hs]
  change g s = (‖g s‖:ℂ) * (g s / (‖g s‖:ℂ))
  by_cases hz : g s = 0
  · simp [hz]
  · have hnorm : (‖g s‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    field_simp

end OMA.Sector
end

section

open Set Filter Topology Finset Polynomial
open scoped Polynomial
namespace OMA.S_mo_350545


/-- A continuous argument on a square is pinned down along its three known
    edges. The fourth edge is the desired radial parameterization. -/
theorem square_argument (G : C(unitInterval × unitInterval, Circle)) (A : ℝ)
    (bottom : ∀ t : unitInterval, G (t, 0) = 1)
    (left : ∀ s : unitInterval, G (0, s) = 1)
    (right : ∀ s : unitInterval, G (1, s) = Circle.exp ((s : ℝ) * A)) :
    ∃ F : C(unitInterval, ℝ), F 0 = 0 ∧ F 1 = A ∧
      ∀ t : unitInterval, Circle.exp (F t) = G (t, 1) := by
  let _ : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let _ : LocallyPathConnectedSpace unitInterval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨L, ⟨h0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    G (0, 0) 0 (by simp [bottom])
  have lifts (u : unitInterval × unitInterval) : Circle.exp (L u) = G u := congrFun hL u
  have zeroEdge (f : unitInterval → ℝ) (hf : Continuous f) (hz : f 0 = 0)
      (he : ∀ x, Circle.exp (f x) = 1) : ∀ x, f x = 0 := by
    have eq := Circle.isCoveringMap_exp.eq_of_comp_eq hf (g₂ := fun _ ↦ (0 : ℝ))
      continuous_const (funext fun x ↦ (he x).trans Circle.exp_zero.symm) 0 hz
    exact congrFun eq
  have hbottom := zeroEdge (fun t ↦ L (t, 0)) (by fun_prop) h0
    (fun t ↦ (lifts (t, 0)).trans (bottom t))
  have hleft := zeroEdge (fun s ↦ L (0, s)) (by fun_prop) h0
    (fun s ↦ (lifts (0, s)).trans (left s))
  have hright := Circle.isCoveringMap_exp.eq_of_comp_eq
    (g₁ := fun s : unitInterval ↦ L (1, s)) (g₂ := fun s : unitInterval ↦ (s : ℝ) * A)
    (by fun_prop) (by fun_prop) (funext fun s ↦ (lifts (1,s)).trans (right s)) 0
    (by simpa using hbottom 1)
  exact ⟨⟨fun t ↦ L (t, 1), by fun_prop⟩, hleft 1, by simpa using congrFun hright 1,
    fun t ↦ lifts (t, 1)⟩

noncomputable def homogenized (p : ℝ[X]) (θ : ℝ) (u : unitInterval × unitInterval) : ℂ :=
  ∑ k ∈ range (p.natDegree + 1), (p.coeff k : ℂ) *
    (((u.1 : ℝ) : ℂ) * Complex.exp ((((u.2 : ℝ) * θ : ℝ) : ℂ) * Complex.I)) ^ k *
    (1 - ((u.1 : ℝ) : ℂ)) ^ (p.natDegree - k)

theorem homogenized_continuous (p : ℝ[X]) (θ : ℝ) : Continuous (homogenized p θ) := by
  unfold homogenized
  fun_prop

theorem homogenized_of_lt_one (p : ℝ[X]) (θ : ℝ) (t s : unitInterval) (ht : (t : ℝ) < 1) :
    homogenized p θ (t,s) = (1 - ((t : ℝ) : ℂ)) ^ p.natDegree *
      aeval ((((t : ℝ) : ℂ) / (1 - ((t : ℝ) : ℂ))) *
        Complex.exp ((((s : ℝ) * θ : ℝ) : ℂ) * Complex.I)) p := by
  have hn : (1 : ℂ) - (t : ℝ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr ht.ne' : (1:ℝ)-t ≠ 0)
  rw [homogenized, aeval_eq_sum_range, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hle := Nat.le_of_lt_succ (mem_range.mp hk)
  simp only [Algebra.smul_def, Complex.coe_algebraMap, mul_pow, div_pow]
  rw [show p.natDegree = (p.natDegree-k) + k by omega]
  simp only [Nat.add_sub_cancel, pow_add]
  field_simp

theorem homogenized_zero (p : ℝ[X]) (θ : ℝ) (s : unitInterval) :
    homogenized p θ (0,s) = (p.coeff 0 : ℂ) := by
  rw [homogenized_of_lt_one p θ 0 s (by norm_num)]
  simp [aeval_def, eval₂_at_zero]

theorem homogenized_one (p : ℝ[X]) (θ : ℝ) (s : unitInterval) :
    homogenized p θ (1,s) = (p.leadingCoeff : ℂ) *
      (Complex.exp ((((s : ℝ) * θ : ℝ) : ℂ) * Complex.I)) ^ p.natDegree := by
  rw [homogenized, sum_eq_single p.natDegree]
  · simp
  · intro k hk hkn
    have hlt : k < p.natDegree := by have := mem_range.mp hk; omega
    simp [zero_pow (by omega : p.natDegree-k ≠ 0)]
  · simp

open Complex


noncomputable def phase (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    change z / (‖z‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    simp [hz]⟩

private theorem phase_pos_mul (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    phase ((r : ℂ) * z) (mul_ne_zero (by exact_mod_cast hr.ne') hz) = phase z hz := by
  apply Subtype.ext
  change ((r : ℂ) * z) / (‖(r : ℂ) * z‖ : ℂ) = z / (‖z‖ : ℂ)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0)

private theorem phase_exp (θ : ℝ) : phase (Complex.exp ((θ : ℂ) * I)) (Complex.exp_ne_zero _) =
    Circle.exp θ := by
  apply Subtype.ext
  change Complex.exp ((θ : ℂ) * I) / (‖Complex.exp ((θ : ℂ) * I)‖ : ℂ) = _
  simp [Complex.norm_exp, Circle.coe_exp]

private theorem phase_real_pos (r : ℝ) (hr : 0 < r) : phase (r : ℂ) (by exact_mod_cast hr.ne') = 1 := by
  apply Subtype.ext
  change (r : ℂ) / (‖(r : ℂ)‖ : ℂ) = 1
  simp [Real.norm_of_nonneg hr.le, hr.ne']

private noncomputable def diskCoordinate (t : ℝ) : unitInterval :=
  ⟨max t 0 / (1 + max t 0), div_nonneg (le_max_right _ _) (by positivity),
    (div_le_one (by positivity)).mpr (by linarith)⟩

private theorem diskCoordinate_cont : Continuous diskCoordinate := by
  apply Continuous.subtype_mk
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  positivity

private theorem diskCoordinate_lim : Tendsto diskCoordinate atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  have h : Tendsto (fun t : ℝ ↦ (1 : ℝ) - (1 + t)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ tendsto_id))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change _ = max t 0 / (1 + max t 0)
  rw [max_eq_left ht]
  field_simp
  ring

open Complex
private theorem pos_eval_from_constant (p : ℝ[X]) (hc : ∀ k, 0 ≤ p.coeff k)
    (h0 : 0 < p.coeff 0) (t : ℝ) (ht : 0 ≤ t) : 0 < p.eval t := by
  rw [eval_eq_sum_range]
  refine Finset.sum_pos' (fun k _ ↦ mul_nonneg (hc k) (pow_nonneg ht k)) ?_
  exact ⟨0, by simp, by simpa using h0⟩

private theorem phase_congr {z w : ℂ} {hz : z ≠ 0} {hw : w ≠ 0} (h : z = w) :
    phase z hz = phase w hw := by subst w; rfl

/-- The continuous radial argument is anchored at the positive real constant
    term. At infinity its unwrapped value is the degree times the ray angle. -/
theorem ray_argument (p : ℝ[X]) (θ : ℝ) (hθ : 0 ≤ θ) (hc : ∀ k, 0 ≤ p.coeff k)
    (h0 : 0 < p.coeff 0)
    (hfree : ∀ t γ : ℝ, 0 ≤ t → 0 ≤ γ → γ ≤ θ →
      aeval ((t : ℂ) * Complex.exp ((γ : ℂ) * I)) p ≠ 0) :
    ∃ F : ℝ → ℝ, Continuous F ∧ F 0 = 0 ∧ Tendsto F atTop (𝓝 ((p.natDegree : ℝ) * θ)) ∧
      ∀ t : ℝ, 0 ≤ t → Complex.exp ((F t : ℂ) * I) =
        aeval ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) p /
          (‖aeval ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) p‖ : ℂ) := by
  have hp : p ≠ 0 := by intro e; simp [e] at h0
  have hlead : 0 < p.leadingCoeff := lt_of_le_of_ne (hc _) (leadingCoeff_ne_zero.mpr hp).symm
  let pe (t γ : ℝ) := aeval ((t : ℂ) * Complex.exp ((γ : ℂ) * I)) p
  let ρ (u : unitInterval) := (u : ℝ) / (1 - (u : ℝ))
  have hρ (u : unitInterval) : 0 ≤ ρ u := div_nonneg u.2.1 (sub_nonneg.mpr u.2.2)
  have hpe (t s : unitInterval) : pe (ρ t) (s * θ) ≠ 0 := hfree _ _ (hρ _) (mul_nonneg s.2.1 hθ)
    (by simpa using mul_le_mul_of_nonneg_right s.2.2 hθ)
  have interior (t s : unitInterval) (ht : (t : ℝ) < 1) :
      homogenized p θ (t,s) = (((1 - (t : ℝ)) ^ p.natDegree : ℝ) : ℂ) * pe (ρ t) (s * θ) := by
    rw [homogenized_of_lt_one _ _ _ _ ht]
    dsimp [ρ, pe]
    push_cast
    rfl
  have outer (s : unitInterval) : homogenized p θ (1,s) =
      (p.leadingCoeff : ℂ) * Complex.exp (((s : ℝ) * ((p.natDegree : ℝ) * θ) : ℝ) * I) := by
    rw [homogenized_one, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hn (u : unitInterval × unitInterval) : homogenized p θ u ≠ 0 := by
    obtain ⟨t,s⟩ := u
    rcases lt_or_eq_of_le t.2.2 with ht | ht
    · rw [interior t s ht]
      exact mul_ne_zero (by exact_mod_cast (pow_pos (sub_pos.mpr ht) p.natDegree).ne') (hpe _ _)
    · have he : t = 1 := Subtype.ext ht
      subst t
      rw [outer]
      exact mul_ne_zero (by exact_mod_cast hlead.ne') (Complex.exp_ne_zero _)
  let G : C(unitInterval × unitInterval, Circle) := ⟨fun u ↦ phase (homogenized p θ u) (hn u), by
    apply Continuous.subtype_mk
    apply (homogenized_continuous p θ).div
    · exact Complex.continuous_ofReal.comp (homogenized_continuous p θ).norm
    · intro u
      exact_mod_cast (norm_ne_zero_iff.mpr (hn u))⟩
  have interiorPhase (t s : unitInterval) (ht : (t : ℝ) < 1) :
      G (t,s) = phase (pe (ρ t) (s * θ)) (hpe t s) := by
    exact (phase_congr (hz := hn (t,s)) (interior t s ht)).trans
      (phase_pos_mul _ (pow_pos (sub_pos.mpr ht) _) _ (hpe t s))
  have outerPhase (s : unitInterval) : G (1,s) = Circle.exp ((s : ℝ) * (p.natDegree * θ)) := by
    exact (phase_congr (hz := hn (1,s)) (outer s)).trans ((phase_pos_mul _ hlead _ (Complex.exp_ne_zero _)).trans
      (phase_exp _))
  have leftPhase (s : unitInterval) : G (0,s) = 1 :=
    (phase_congr (hz := hn (0,s)) (homogenized_zero p θ s)).trans (phase_real_pos _ h0)
  have bottomPhase (t : unitInterval) : G (t,0) = 1 := by
    rcases lt_or_eq_of_le t.2.2 with ht | ht
    · rw [interiorPhase t 0 ht]
      have he : pe (ρ t) ((0 : unitInterval) * θ) = ((p.eval (ρ t) : ℝ) : ℂ) := by
        change pe (ρ t) ((0 : ℝ) * θ) = _
        simp only [pe, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
        exact Polynomial.aeval_ofReal p (ρ t)
      exact (phase_congr (hz := hpe t 0) he).trans (phase_real_pos _ (pos_eval_from_constant p hc h0 _ (hρ _)))
    · have he : t = 1 := Subtype.ext ht
      subst t
      simpa using outerPhase 0
  obtain ⟨f, f0, f1, hf⟩ := square_argument G _ bottomPhase leftPhase outerPhase
  have coord0 : diskCoordinate 0 = 0 := Subtype.ext (by norm_num [diskCoordinate])
  refine ⟨fun t ↦ f (diskCoordinate t), f.continuous.comp diskCoordinate_cont, ?_, ?_, ?_⟩
  · simpa [coord0] using f0
  · change Tendsto (f ∘ diskCoordinate) atTop (𝓝 ((p.natDegree : ℝ) * θ))
    rw [← f1]
    exact (f.continuous.tendsto 1).comp diskCoordinate_lim
  · intro t ht
    have hu : (diskCoordinate t : ℝ) < 1 := by
      simp only [diskCoordinate, max_eq_left ht]
      exact (div_lt_one (by positivity)).mpr (by linarith)
    have invu : ρ (diskCoordinate t) = t := by
      simp only [ρ, diskCoordinate, max_eq_left ht]
      field_simp
      ring
    have he := congrArg (fun z : Circle ↦ (z : ℂ))
      ((hf (diskCoordinate t)).trans (interiorPhase (diskCoordinate t) 1 hu))
    simpa [phase, pe, invu, Circle.coe_exp] using he

end OMA.S_mo_350545
end

section

open Real Polynomial Topology Filter
namespace OMA.S_mo_350545

theorem from_radial_im {p : ℝ[X]} (z : ℂ)
    (h : 0 ≤ (Complex.exp ((z.arg : ℂ)*Complex.I) * aeval z p.derivative / aeval z p).im) :
    0 ≤ (z * aeval z p.derivative / aeval z p).im := by
  have he : z * aeval z p.derivative / aeval z p =
      (‖z‖:ℂ) * (Complex.exp ((z.arg:ℂ)*Complex.I) * aeval z p.derivative / aeval z p) := by
    rw [← mul_div_assoc,← mul_assoc,Complex.norm_mul_exp_arg_mul_I]
  simp only [he, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_nonneg (norm_nonneg _) h


end OMA.S_mo_350545

end

section
namespace OMA.S_mo_350545
open Polynomial Real
open OMA.Sector

theorem sector_logarithmic_velocity : OMA.R_mo_350545_R1.H1 := by
  intro p β hc h0 _ hβ hr z hθ hu
  have hfree := zero_free_polar hu hβ hr
  obtain ⟨F,hF,hF0,hlim,hphase⟩ := ray_argument p z.arg hθ.le hc h0 hfree
  have hmono := monotoneOn_of_sine_ray_polynomials F p.natDegree z.arg hθ
    (by linarith [Real.pi_pos]) hF.continuousOn hF0 hlim
    (fun ψ hψ hψπ _ => phase_crossing_polynomial p z.arg ψ F h0 hc hψ hψπ hphase)
  have hz : z ≠ 0 := fun e => by simp [e] at hθ
  have hd := polynomial_im_ray_logDeriv_nonneg p (Complex.exp ((z.arg:ℂ)*Complex.I)) F
    (norm_pos_iff.mpr hz) (hfree ‖z‖ z.arg (norm_nonneg _) hθ.le le_rfl)
    hF.continuousOn hmono hphase
  rw [Complex.norm_mul_exp_arg_mul_I] at hd
  exact from_radial_im z hd

end OMA.S_mo_350545

end

theorem OMA.solution : type_of% @OMA.S_mo_350545.main :=
  OMA.R_mo_350545_R1.main OMA.S_mo_350545.sector_logarithmic_velocity
    OMA.S_mo_350545.exclude_critical_halfplane
