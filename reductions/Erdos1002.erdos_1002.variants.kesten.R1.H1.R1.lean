import OMAReductions.R_Erdos1002_erdos_1002_variants_kesten_R1
import Mathlib.NumberTheory.Real.Irrational

/-!
# Initial-phase integration and Gauss reciprocity for Kesten's rotation sums

At fixed irrational angle, integration over the initial phase gives a uniform
mixture of unit intervals centered at differences of two unshifted prefix
sums. Each prefix admits an exact expansion along the Gauss map. Splitting
this expansion at partial quotient √(log n) leaves a small-digit cancellation
estimate and a large-digit cosine limit. The two prefixes share their angle.

The common slope and unit jumps in the initial phase are also described in
Ralston, Tangerman, Veerman and Wu, *Birkhoff Measures, Birkhoff Sums, and
Discrepancies*, sections 1–2. The merged parent reduction by justusklocke-cloud
supplies the characteristic function of a pushforward and the reciprocal-log limit.
-/

-- Reduction Erdos1002.erdos_1002.variants.kesten.R1.H1.R1 of step Erdos1002.erdos_1002.variants.kesten.R1.H1
-- Credit: @yuka30240

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace OMA.R_Erdos1002_erdos_1002_variants_kesten_R1_H1_R1

private lemma measurable_cut_count (s : Finset ℝ) :
    Measurable (fun x : ℝ => ((s.filter (· ≤ x)).card : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h : (fun x : ℝ => (((insert a s).filter (· ≤ x)).card : ℝ)) =
        (fun x => (if a ≤ x then 1 else 0) + ((s.filter (· ≤ x)).card : ℝ)) := by
      funext x
      by_cases hx : a ≤ x <;> simp [Finset.filter_insert, hx, ha, Nat.cast_add, add_comm]
    rw [h]
    exact (Measurable.ite measurableSet_Ici measurable_const measurable_const).add ih

/-- Integrating a linear function of slope k with a unit downward jump at each cut.
The primitive picks up the integral across the skipped unit interval at every jump. -/
private lemma integrate_jumps (φ F : ℝ → ℂ) (hc : Continuous φ)
    (hb : ∀ x, ‖φ x‖ ≤ 1) (hF : ∀ a b, (∫ x in a..b, φ x) = F b - F a)
    (k A : ℝ) (s : Finset ℝ) (b : ℝ) (hb0 : 0 ≤ b)
    (hs : ∀ u ∈ s, u ∈ Icc 0 b) :
    k • (∫ x in (0 : ℝ)..b, φ (x * k + A - ((s.filter (· ≤ x)).card : ℝ))) =
      F (b * k + A - s.card) - F A +
        ∑ u ∈ s, (F (u * k + A - ((s.filter (· ≤ u)).card : ℝ) + 1) -
          F (u * k + A - ((s.filter (· ≤ u)).card : ℝ))) := by
  classical
  have affine (u v B : ℝ) :
      k • (∫ x in u..v, φ (x * k + B)) = F (v * k + B) - F (u * k + B) := by
    simpa only [mul_comm k, hF] using
      (intervalIntegral.smul_integral_comp_mul_add (a := u) (b := v) φ k B)
  have hint (S : Finset ℝ) (a d : ℝ) :
      IntervalIntegrable (fun x : ℝ => φ (x * k + A - ((S.filter (· ≤ x)).card : ℝ)))
        volume a d := by
    apply intervalIntegrable_iff.mpr
    apply IntegrableOn.of_bound (C := 1) (by simp [uIoc])
    · exact (hc.measurable.comp (((measurable_id.mul_const k).add_const A).sub
        (measurable_cut_count S))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => hb _
  induction s using Finset.induction_on_max generalizing b with
  | empty => simpa using affine 0 b A
  | @insert u s hu ih =>
    have hun : u ∉ s := fun h => (hu u h).false
    have hu0 := (hs u (Finset.mem_insert_self _ _)).1
    have hub := (hs u (Finset.mem_insert_self _ _)).2
    have hs' (v) (hv : v ∈ s) : v ∈ Icc 0 u :=
      ⟨(hs v (Finset.mem_insert_of_mem hv)).1, (hu v hv).le⟩
    have hbefore (x : ℝ) (hx : x < u) :
        (insert u s).filter (· ≤ x) = s.filter (· ≤ x) := by
      simp [Finset.filter_insert, not_le.mpr hx]
    have hafter (x : ℝ) (hx : u ≤ x) :
        (insert u s).filter (· ≤ x) = insert u s := by
      apply Finset.filter_true_of_mem
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hx
      · exact (hu v hv).le.trans hx
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ 0 u) (hint _ u b), smul_add]
    have left := intervalIntegral.integral_congr_Ioo_of_le (f := fun x : ℝ =>
      φ (x * k + A - (((insert u s).filter (· ≤ x)).card : ℝ)))
      (g := fun x : ℝ => φ (x * k + A - ((s.filter (· ≤ x)).card : ℝ)))
      (μ := volume) hu0 (fun x hx => by simp only [hbefore x hx.2])
    have right := intervalIntegral.integral_congr_Ioo_of_le (f := fun x : ℝ =>
      φ (x * k + A - (((insert u s).filter (· ≤ x)).card : ℝ)))
      (g := fun x : ℝ => φ (x * k + (A - ((insert u s).card : ℝ))))
      (μ := volume) hub (fun x hx => by simp only [hafter x hx.1.le, add_sub_assoc])
    rw [left, right, ih u hu0 hs', affine, Finset.sum_insert hun, hafter u le_rfl]
    have old : (∑ v ∈ s, (F (v * k + A - (((insert u s).filter (· ≤ v)).card : ℝ) + 1) -
        F (v * k + A - (((insert u s).filter (· ≤ v)).card : ℝ)))) =
        ∑ v ∈ s, (F (v * k + A - ((s.filter (· ≤ v)).card : ℝ) + 1) -
          F (v * k + A - ((s.filter (· ≤ v)).card : ℝ))) :=
      Finset.sum_congr rfl fun v hv => by rw [hbefore v (hu v hv)]
    rw [old, Finset.card_insert_of_notMem hun, Nat.cast_add, Nat.cast_one]
    simp only [← add_sub_assoc]
    rw [show u * k + A - (s.card + 1 : ℝ) + 1 = u * k + A - s.card by ring]
    abel

private lemma cut_injective {α : ℝ} (hα : Irrational α) :
    Function.Injective (fun j : ℕ => Int.fract (-(α * j))) := by
  intro j k hjk
  by_contra h
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hjk
  have hdiff : (k : ℤ) - j ≠ 0 := by omega
  apply (hα.mul_intCast hdiff).ne_int z
  push_cast
  linarith only [hz, mul_sub α (k : ℝ) j]

private lemma phase_as_count {x : ℝ} (hx : x ∈ Ico 0 1) {α : ℝ}
    (hα : Irrational α) (n : ℕ) :
    let s := (Finset.range n).image (fun k : ℕ => Int.fract (-(α * k)))
    (∑ k ∈ Finset.range n, (Int.fract (x + α * k) - 1 / 2)) =
      x * n + (∑ u ∈ s, (1 / 2 - u)) - ((s.filter (· ≤ x)).card : ℝ) := by
  classical
  intro s
  have hterm (v : ℝ) :
      Int.fract (x + v) - 1 / 2 =
        x + (1 / 2 - Int.fract (-v)) - (if Int.fract (-v) ≤ x then 1 else 0) := by
    set u := Int.fract (-v) with hu
    have hmod : Int.fract (x + v) = Int.fract (x - u) := by
      apply Int.fract_eq_fract.mpr
      exact ⟨-⌊-v⌋, by rw [hu, Int.fract]; push_cast; ring⟩
    rw [hmod]
    have hu0 := Int.fract_nonneg (-v)
    have hu1 := Int.fract_lt_one (-v)
    change 0 ≤ u at hu0
    change u < 1 at hu1
    by_cases hux : u ≤ x
    · rw [if_pos hux, Int.fract_eq_self.mpr ⟨by linarith, by linarith [hx.2]⟩]
      ring
    · have hshift : Int.fract (x - u) = x - u + 1 := by
        rw [← Int.fract_add_one (x - u)]
        apply Int.fract_eq_self.mpr
        constructor <;> linarith [hx.1]
      rw [if_neg hux, hshift]
      ring
  have hs (f : ℝ → ℝ) : ∑ u ∈ s, f u =
      ∑ k ∈ Finset.range n, f (Int.fract (-(α * k))) :=
    Finset.sum_image (fun _ _ _ _ he => cut_injective hα he)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hs, ← hs (fun u => if u ≤ x then 1 else 0)]
  simp [Finset.sum_boole, mul_comm]

private lemma at_cut {α : ℝ} (hα : Irrational α) (j r : ℕ) :
    let D := fun m : ℕ => ∑ i ∈ Finset.range m, (Int.fract (α * ((i : ℝ) + 1)) - 1 / 2)
    (∑ k ∈ Finset.range (j + 1 + r),
      (Int.fract (Int.fract (-(α * j)) + α * k) - 1 / 2)) =
      D r - D j - 1 / 2 := by
  intro D
  have shift (k : ℕ) :
      Int.fract (Int.fract (-(α * j)) + α * k) = Int.fract (α * ((k : ℝ) - j)) := by
    apply Int.fract_eq_fract.mpr
    exact ⟨-⌊-(α * j)⌋, by rw [Int.fract]; push_cast; ring⟩
  simp_rw [shift]
  rw [Finset.sum_range_add, Finset.sum_range_succ]
  have prev : (∑ k ∈ Finset.range j, (Int.fract (α * ((k : ℝ) - j)) - 1 / 2)) = -D j := by
    rw [← Finset.sum_range_reflect (fun k : ℕ => Int.fract (α * ((k : ℝ) - j)) - 1 / 2) j]
    dsimp [D]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e : ((j - 1 - i : ℕ) : ℝ) - j = -((i : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      ring
    have hn : Int.fract (α * ((i : ℝ) + 1)) ≠ 0 := by
      apply ne_of_gt
      apply Int.fract_pos.mpr
      have hir := hα.mul_natCast (m := i + 1) (by omega)
      push_cast at hir
      exact hir.ne_int _
    rw [e, mul_neg, Int.fract_neg hn]
    ring
  have after : (∑ i ∈ Finset.range r,
      (Int.fract (α * (((j + 1 + i : ℕ) : ℝ) - j)) - 1 / 2)) = D r := by
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring_nf
  rw [prev, after]
  simp
  ring

/-- Integrating over the initial phase is exactly the average of uniform unit
intervals centered at differences of two unshifted rotation sums. -/
theorem phase_mixture {α : ℝ} (hα : Irrational α) (n : ℕ)
    (φ : ℝ → ℂ) (hc : Continuous φ) (hb : ∀ x, ‖φ x‖ ≤ 1) :
    let D := fun m : ℕ => ∑ i ∈ Finset.range m, (Int.fract (α * ((i : ℝ) + 1)) - 1 / 2)
    (n : ℝ) • (∫ x in (0 : ℝ)..1, φ (∑ k ∈ Finset.range n,
      (Int.fract (x + α * k) - 1 / 2))) =
      ∑ j ∈ Finset.range n, ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
        φ (u + (D (n - 1 - j) - D j)) := by
  classical
  intro D
  let cut (k : ℕ) := Int.fract (-(α * k))
  let s := (Finset.range n).image cut
  let A := ∑ u ∈ s, (1 / 2 - u)
  let S (x : ℝ) := ∑ k ∈ Finset.range n, (Int.fract (x + α * k) - 1 / 2)
  let F (a : ℝ) := ∫ z in (0 : ℝ)..a, φ z
  have hF (a b : ℝ) : (∫ z in a..b, φ z) = F b - F a := by
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
    dsimp [F]
    rw [← h]
    abel
  have hcard : s.card = n := by
    change ((Finset.range n).image cut).card = n
    rw [Finset.card_image_of_injective _ (show Function.Injective cut from cut_injective hα), Finset.card_range]
  have hcut (k : ℕ) : cut k ∈ Ico 0 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hs (x : ℝ) (hx : x ∈ Ico 0 1) :
      S x = x * n + A - ((s.filter (· ≤ x)).card : ℝ) := phase_as_count hx hα n
  change (n : ℝ) • (∫ x in (0 : ℝ)..1, φ (S x)) = _
  rw [intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (g := fun x =>
      φ (x * n + A - ((s.filter (· ≤ x)).card : ℝ))) zero_le_one
      (fun x hx => by simp only [hs x ⟨hx.1.le, hx.2⟩])]
  rw [integrate_jumps φ F hc hb hF _ _ s 1 zero_le_one (by
    intro u hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨(hcut k).1, (hcut k).2.le⟩)]
  rw [hcard]
  simp only [one_mul, add_sub_cancel_left, sub_self, zero_add]
  change (∑ u ∈ (Finset.range n).image cut, _) = _
  rw [Finset.sum_image (fun _ _ _ _ he => cut_injective hα he)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  have e : j + 1 + (n - 1 - j) = n := by omega
  have value : S (cut j) = D (n - 1 - j) - D j - 1 / 2 := by
    simpa only [e] using at_cut hα j (n - 1 - j)
  rw [← hs _ (hcut j), value, intervalIntegral.integral_comp_add_right, hF]
  congr 2 <;> ring

private lemma wave_factor (s u v : ℝ) :
    Complex.exp (((s * (u + v) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((s * u : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((s * v : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private lemma phase_fourier {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : n ≠ 0) (w : ℝ) :
    let D := fun m : ℕ => ∑ i ∈ Finset.range m, (Int.fract (α * ((i : ℝ) + 1)) - 1 / 2)
    let wave := fun z : ℝ => Complex.exp (((w * z : ℝ) : ℂ) * Complex.I)
    (∫ x in (0 : ℝ)..1, wave (∑ k ∈ Finset.range n, (Int.fract (x + α * k) - 1 / 2))) =
      (∫ u in (-(1 / 2) : ℝ)..(1 / 2), wave u) *
        ((n : ℂ)⁻¹ * ∑ j ∈ Finset.range n, wave (D (n - 1 - j) - D j)) := by
  intro D wave
  have hm := phase_mixture hα n wave (by dsimp [wave]; fun_prop)
    (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (n : ℝ) • _ = ∑ j ∈ Finset.range n, ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
    wave (u + (D (n - 1 - j) - D j)) at hm
  have h (u v : ℝ) : wave (u + v) = wave u * wave v := wave_factor w u v
  simp_rw [h, intervalIntegral.integral_mul_const] at hm
  rw [← Finset.mul_sum, Complex.real_smul] at hm
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast at hm
  calc
    _ = (n : ℂ)⁻¹ * ((n : ℂ) * _) := by rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul]
    _ = _ := by rw [hm]; ac_rfl

private lemma reflected_cosine (n : ℕ) (D : ℕ → ℝ) (w : ℝ) :
    (∑ j ∈ Finset.range n, Complex.exp (((w * (D (n - 1 - j) - D j) : ℝ) : ℂ) * Complex.I)) =
      ((∑ j ∈ Finset.range n, Real.cos (w * (D (n - 1 - j) - D j)) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re]
  · simp only [Complex.im_sum, Complex.exp_ofReal_mul_I_im, Complex.ofReal_im]
    let f := fun j : ℕ => Real.sin (w * (D (n - 1 - j) - D j))
    change ∑ j ∈ Finset.range n, f j = 0
    have h : ∑ j ∈ Finset.range n, f (n - 1 - j) = -(∑ j ∈ Finset.range n, f j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      dsimp [f]
      rw [show n - 1 - (n - 1 - j) = j by omega, ← Real.sin_neg, ← mul_neg, neg_sub]
    rw [Finset.sum_range_reflect] at h
    linarith

private lemma ae_irrational_angle :
    ∀ᵐ a : ℝ ∂volume.restrict (Ico (0 : ℝ) 1), Irrational a :=
  (Set.countable_range ((↑) : ℚ → ℝ)).ae_notMem _

/-- The full characteristic function is a uniform-noise factor times a one-angle
cosine average. Reflection of the cut index cancels the sine terms exactly. -/
theorem square_fourier {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    let D := fun (a : ℝ) (m : ℕ) => ∑ k ∈ Finset.range m,
      (Int.fract (a * ((k : ℝ) + 1)) - 1 / 2)
    let w := t / Real.log n
    charFun ((volume.restrict (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)).map
      (fun p : ℝ × ℝ => (1 / Real.log (n : ℝ)) *
        ∑ k ∈ Finset.range n, (Int.fract (p.2 + p.1 * k) - 1 / 2))) t =
      (∫ u in (-(1 / 2) : ℝ)..(1 / 2), Complex.exp (((w * u : ℝ) : ℂ) * Complex.I)) *
      ((∫ a in Ico (0 : ℝ) 1, (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
        Real.cos (w * (D a (n - 1 - j) - D a j)) : ℝ) : ℂ) := by
  intro D w
  let S (p : ℝ × ℝ) := ∑ k ∈ Finset.range n, (Int.fract (p.2 + p.1 * k) - 1 / 2)
  let I := Ico (0 : ℝ) 1
  let wave (z : ℝ) := Complex.exp (((w * z : ℝ) : ℂ) * Complex.I)
  have hm : Measurable S := Finset.measurable_sum _ fun k _ =>
    (measurable_fract.comp (by fun_prop)).sub measurable_const
  have hX : Measurable (fun p : ℝ × ℝ => 1 / Real.log (n : ℝ) * S p) := measurable_const.mul hm
  change charFun ((volume.restrict (I ×ˢ I)).map (fun p => 1 / Real.log (n : ℝ) * S p)) t = _
  rw [OMA.R_Erdos1002_erdos_1002_variants_kesten_R1.charFun_map_apply hX t]
  have he (p : ℝ × ℝ) :
      Complex.exp ((t : ℂ) * (((1 / Real.log (n : ℝ)) * S p : ℝ) : ℂ) * Complex.I) =
        wave (S p) := by
    dsimp only [wave, w]
    push_cast
    congr 2
    ring
  change (∫ p in I ×ˢ I, Complex.exp ((t : ℂ) * (((1 / Real.log (n : ℝ)) * S p : ℝ) : ℂ) *
    Complex.I)) = _
  simp_rw [he]
  rw [Measure.volume_eq_prod, setIntegral_prod]
  · rw [← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_irrational_angle] with a ha
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have h := phase_fourier ha hn w
    change (∫ x in (0 : ℝ)..1, wave (S (a, x))) = (∫ u in (-(1 / 2) : ℝ)..(1 / 2), wave u) *
      ((n : ℂ)⁻¹ * ∑ j ∈ Finset.range n, wave (D a (n - 1 - j) - D a j)) at h
    rw [h, show (∑ j ∈ Finset.range n, wave (D a (n - 1 - j) - D a j)) =
      ((∑ j ∈ Finset.range n, Real.cos (w * (D a (n - 1 - j) - D a j)) : ℝ) : ℂ) from
        reflected_cosine n (D a) w]
    simp only [wave, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  · exact IntegrableOn.of_bound (by simp [I, Measure.prod_prod, Real.volume_Ico])
      ((show Measurable wave by dsimp [wave]; fun_prop).comp hm).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => (Complex.norm_exp_ofReal_mul_I _).le)

private lemma uniform_factor_limit (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
      Complex.exp ((((t / Real.log n) * u : ℝ) : ℂ) * Complex.I)) atTop (𝓝 1) := by
  let K (w : ℝ) := ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
    Complex.exp (((w * u : ℝ) : ℂ) * Complex.I)
  have hK : Continuous K := by dsimp [K]; fun_prop
  have h0 : K 0 = 1 := by norm_num [K, intervalIntegral.integral_const, Complex.real_smul]
  have hw : Tendsto (fun n : ℕ => t / Real.log n) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using
      OMA.R_Erdos1002_erdos_1002_variants_kesten_R1.reciprocal_log_tendsto.const_mul t
  exact h0 ▸ hK.continuousAt.tendsto.comp hw

/-- The change in the unshifted sum under one step of the continued fraction algorithm. -/
theorem gauss_reciprocity {α : ℝ} (hα : Irrational α) (h0 : 0 < α) (h1 : α < 1) (n : ℕ) :
    let D := fun (a : ℝ) (m : ℕ) =>
      ∑ i ∈ Finset.range m, (Int.fract (a * ((i : ℝ) + 1)) - 1 / 2)
    let x := Int.fract (α * n)
    D α n + D (Int.fract α⁻¹) ⌊α * n⌋₊ = x * (x - 1) / (2 * α) + x / 2 := by
  intro D
  let cost (x : ℝ) := x * (x - 1) / (2 * α) + x / 2
  change D α n + D (Int.fract α⁻¹) ⌊α * n⌋₊ = cost (Int.fract (α * n))
  have split (k : ℕ) :
      (⌊α * k⌋₊ : ℝ) + Int.fract (α * k) = α * k := by
    rw [natCast_floor_eq_intCast_floor (mul_nonneg h0.le k.cast_nonneg), add_comm,
      Int.fract_add_floor]
  have succD (a : ℝ) (k : ℕ) :
      D a (k + 1) = D a k + (Int.fract (a * ((k : ℝ) + 1)) - 1 / 2) :=
    Finset.sum_range_succ _ _
  induction n with
  | zero => simp [D, cost]
  | succ n ih =>
    let m := ⌊α * n⌋₊
    let m' := ⌊α * (n + 1 : ℕ)⌋₊
    let x := Int.fract (α * n)
    let y := Int.fract (α * (n + 1 : ℕ))
    change D α (n + 1) + D (Int.fract α⁻¹) m' = cost y
    change D α n + D (Int.fract α⁻¹) m = cost x at ih
    have hx : (m : ℝ) + x = α * n := split n
    have hy : (m' : ℝ) + y = α * ((n : ℝ) + 1) := by simpa [m', y] using split (n + 1)
    have hx0 : 0 ≤ x := Int.fract_nonneg _
    have hx1 : x < 1 := Int.fract_lt_one _
    have hy0 : 0 < y := by
      apply Int.fract_pos.mpr
      exact (hα.mul_natCast (m := n + 1) (by omega)).ne_int _
    have hym : m ≤ m' := Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) h0.le)
    have hym' : (m' : ℝ) < (m : ℝ) + 2 := by nlinarith only [hx, hy, h1, hx1, hy0]
    have hym'' : m' < m + 2 := by exact_mod_cast hym'
    have hD : D α (n + 1) = D α n + (y - 1 / 2) := by
      simpa [y] using succD α n
    rw [hD]
    rcases (show m' = m ∨ m' = m + 1 by omega) with he | he
    · rw [he] at hy ⊢
      have hyx : y = x + α := by linarith only [hx, hy, mul_add α (n : ℝ) 1, mul_one α]
      have hcost : cost y - cost x = y - 1 / 2 := by
        rw [hyx]; dsimp [cost]; field_simp; ring
      linarith only [ih, hcost]
    · rw [he, Nat.cast_add, Nat.cast_one] at hy
      rw [he, succD]
      have hyx : y = x + α - 1 := by nlinarith only [hx, hy]
      have hya : y < α := by linarith only [hyx, hx1]
      have hmfract :
          Int.fract (Int.fract α⁻¹ * ((m : ℝ) + 1)) = 1 - y / α := by
        apply Int.fract_eq_iff.mpr
        refine ⟨by linarith [(div_lt_one h0).mpr hya], by linarith [div_pos hy0 h0], ?_⟩
        refine ⟨(n : ℤ) - ⌊α⁻¹⌋ * ((m : ℤ) + 1), ?_⟩
        rw [Int.fract]
        push_cast
        field_simp
        nlinarith only [hy]
      rw [hmfract]
      have hcost : cost y - cost x = y - y / α := by
        rw [hyx]; dsimp [cost]; field_simp; ring
      linarith only [ih, hcost]

/-- After at most m steps the integer length has reached zero. Reciprocity then
expresses the entire sum as an alternating sum along this finite Gauss orbit. -/
theorem gauss_expansion (N m : ℕ) (hm : m ≤ N) {α : ℝ}
    (hα : Irrational α) (h0 : 0 < α) (h1 : α < 1) :
    let T := fun p : ℝ × ℕ => (Int.fract p.1⁻¹, ⌊p.1 * p.2⌋₊)
    let C := fun p : ℝ × ℕ =>
      let x := Int.fract (p.1 * p.2)
      x * (x - 1) / (2 * p.1) + x / 2
    (∑ k ∈ Finset.range m, (Int.fract (α * ((k : ℝ) + 1)) - 1 / 2)) =
      ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * C (T^[r] (α, m)) := by
  intro T C
  induction N generalizing m α with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp
  | succ N ih =>
    let q := T (α, m)
    have hi : Irrational q.1 := hα.inv.sub_intCast _
    have hp : 0 < q.1 := Int.fract_pos.mpr (hα.inv.ne_int _)
    have hl : q.1 < 1 := Int.fract_lt_one _
    have hq : q.2 ≤ N := by
      by_cases hz : m = 0
      · simp [q, T, hz]
      · have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
        have hlt : ⌊α * m⌋₊ < m := (Nat.floor_lt (by positivity)).mpr (by nlinarith)
        change ⌊α * m⌋₊ ≤ N
        omega
    have hrec := gauss_reciprocity hα h0 h1 m
    change _ + (∑ k ∈ Finset.range q.2, (Int.fract (q.1 * ((k : ℝ) + 1)) - 1 / 2)) =
      C (α, m) at hrec
    rw [ih q.2 hq hi hp hl] at hrec
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Function.iterate_zero_apply]
    have tail : (∑ r ∈ Finset.range N, (-1 : ℝ) ^ (r + 1) * C (T^[r + 1] (α, m))) =
        -(∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * C (T^[r] q)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [Function.iterate_succ_apply, pow_succ]
      change _ * C (T^[r] q) = _
      ring
    rw [tail]
    linarith only [hrec]

private lemma cosine_shift (t x y z : ℝ) (h : x = y + z) :
    |Real.cos (t * x) - Real.cos (t * y)| ≤ max 2 |t| * min 1 |z| := by
  by_cases hz : |z| ≤ 1
  · rw [min_eq_right hz]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, h, add_sub_cancel_left, abs_mul]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  · rw [min_eq_left (le_of_not_ge hz), mul_one]
    refine le_trans (abs_le.mpr ⟨?_, ?_⟩ : |Real.cos (t * x) - Real.cos (t * y)| ≤ 2)
      (le_max_left _ _)
    · linarith [Real.neg_one_le_cos (t * x), Real.cos_le_one (t * y)]
    · linarith [Real.cos_le_one (t * x), Real.neg_one_le_cos (t * y)]

/-- A truncated first absolute moment suffices to compare the two cosine transforms. -/
private lemma cosine_error (n : ℕ) (t : ℝ) (X Y Z : ℕ → ℝ → ℝ)
    (hX : ∀ j, Measurable (X j)) (hY : ∀ j, Measurable (Y j)) (hZ : ∀ j, Measurable (Z j))
    (hs : ∀ᵐ a ∂volume.restrict (Ico (0 : ℝ) 1), ∀ j < n, X j a = Y j a + Z j a) :
    |(∫ a in Ico (0 : ℝ) 1, (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, Real.cos (t * X j a)) -
     (∫ a in Ico (0 : ℝ) 1, (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, Real.cos (t * Y j a))| ≤
     max 2 |t| * ∫ a in Ico (0 : ℝ) 1, (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, min 1 |Z j a| := by
  let I := Ico (0 : ℝ) 1
  let M (f : ℕ → ℝ → ℝ) (a : ℝ) := (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j a
  have hM (f : ℕ → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) (hb : ∀ j a, |f j a| ≤ 1) :
      IntegrableOn (M f) I := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    exact IntegrableOn.of_bound (by simp [I, Real.volume_Ico]) (hf j).aestronglyMeasurable 1
      (Eventually.of_forall (hb j))
  have hcos (W : ℕ → ℝ → ℝ) (hW : ∀ j, Measurable (W j)) :
      IntegrableOn (M (fun j a => Real.cos (t * W j a))) I :=
    hM _ (fun j => Real.continuous_cos.measurable.comp (measurable_const.mul (hW j)))
      (fun j a => Real.abs_cos_le_one _)
  have hclip : IntegrableOn (M (fun j a => min 1 |Z j a|)) I :=
    hM _ (fun j => measurable_const.min (hZ j).abs) (fun j a => by
      rw [abs_of_nonneg (le_min zero_le_one (abs_nonneg _))]; apply min_le_left)
  rw [← integral_sub (hcos X hX) (hcos Y hY), ← integral_const_mul]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hclip.const_mul (max 2 |t|))
  filter_upwards [hs] with a ha
  dsimp only [M]
  rw [Real.norm_eq_abs, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n : (0 : ℝ) ≤ n)), mul_left_comm,
    Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj =>
    cosine_shift t _ _ _ (ha j (Finset.mem_range.mp hj)))

/-- Cancellation of the digits up to the square-root-log cutoff, measured by a
bounded first absolute moment of the normalized difference of two prefixes. -/
def H1 : Prop :=
  let T := fun p : ℝ × ℕ => (Int.fract p.1⁻¹, ⌊p.1 * p.2⌋₊)
  let cost := fun p : ℝ × ℕ =>
    let x := Int.fract (p.1 * p.2)
    x * (x - 1) / (2 * p.1) + x / 2
  let small := fun (n m : ℕ) (a : ℝ) =>
    ∑ r ∈ Finset.range n,
      let p := T^[r] (a, m)
      if (⌊p.1⁻¹⌋₊ : ℝ) ≤ Real.sqrt (Real.log n) then (-1 : ℝ) ^ r * cost p else 0
  Tendsto (fun n : ℕ => ∫ a in Ico (0 : ℝ) 1, (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
    min 1 |(small n (n - 1 - j) a - small n j a) / Real.log n|) atTop (𝓝 0)

/-- The mean cosine transform for the large continued-fraction digits. Both
prefix lengths use the same angle and the same sequence of partial quotients. -/
def H2 : Prop :=
  let T := fun p : ℝ × ℕ => (Int.fract p.1⁻¹, ⌊p.1 * p.2⌋₊)
  let cost := fun p : ℝ × ℕ =>
    let x := Int.fract (p.1 * p.2)
    x * (x - 1) / (2 * p.1) + x / 2
  let large := fun (n m : ℕ) (a : ℝ) =>
    ∑ r ∈ Finset.range n,
      let p := T^[r] (a, m)
      if (⌊p.1⁻¹⌋₊ : ℝ) ≤ Real.sqrt (Real.log n) then 0 else (-1 : ℝ) ^ r * cost p
  ∃ γ : ℝ≥0, 0 < γ ∧ ∀ t : ℝ,
    Tendsto (fun n : ℕ => ∫ a in Ico (0 : ℝ) 1, (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
      Real.cos (t * ((large n (n - 1 - j) a - large n j a) / Real.log n)))
      atTop (𝓝 (Real.exp (-(γ : ℝ) * |t|)))

theorem main : H1 → H2 → OMA.R_Erdos1002_erdos_1002_variants_kesten_R1.H1 := by
  intro hsmall hlarge
  let T := fun p : ℝ × ℕ => (Int.fract p.1⁻¹, ⌊p.1 * p.2⌋₊)
  let cost := fun p : ℝ × ℕ =>
    let x := Int.fract (p.1 * p.2)
    x * (x - 1) / (2 * p.1) + x / 2
  let digit (p : ℝ × ℕ) : ℝ := ⌊p.1⁻¹⌋₊
  let small (n m : ℕ) (a : ℝ) := ∑ r ∈ Finset.range n,
    let p := T^[r] (a, m)
    if digit p ≤ Real.sqrt (Real.log n) then (-1 : ℝ) ^ r * cost p else 0
  let large (n m : ℕ) (a : ℝ) := ∑ r ∈ Finset.range n,
    let p := T^[r] (a, m)
    if digit p ≤ Real.sqrt (Real.log n) then 0 else (-1 : ℝ) ^ r * cost p
  let D (_ m : ℕ) (a : ℝ) := ∑ k ∈ Finset.range m, (Int.fract (a * ((k : ℝ) + 1)) - 1 / 2)
  let diff (f : ℕ → ℕ → ℝ → ℝ) (n j : ℕ) (a : ℝ) :=
    (f n (n - 1 - j) a - f n j a) / Real.log n
  let transform (f : ℕ → ℕ → ℝ → ℝ) (t : ℝ) (n : ℕ) := ∫ a in Ico (0 : ℝ) 1,
    (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, Real.cos (t * diff f n j a)
  let error (n : ℕ) := ∫ a in Ico (0 : ℝ) 1,
    (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, min 1 |diff small n j a|
  change Tendsto error atTop (𝓝 0) at hsmall
  change ∃ γ : ℝ≥0, 0 < γ ∧ ∀ t : ℝ, Tendsto (transform large t) atTop
    (𝓝 (Real.exp (-(γ : ℝ) * |t|))) at hlarge
  obtain ⟨γ, hγ, hlarge⟩ := hlarge
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hcost : Measurable cost := by dsimp [cost]; fun_prop
  have hdigit : Measurable digit := by dsimp [digit]; fun_prop
  have horbit (r m : ℕ) : Measurable (fun a : ℝ => T^[r] (a, m)) :=
    (hT.iterate r).comp (measurable_id.prodMk measurable_const)
  have hsm (n m : ℕ) : Measurable (small n m) := by
    apply Finset.measurable_sum
    intro r _
    exact Measurable.ite (measurableSet_le (hdigit.comp (horbit r m)) measurable_const)
      (measurable_const.mul (hcost.comp (horbit r m))) measurable_const
  have hlg (n m : ℕ) : Measurable (large n m) := by
    apply Finset.measurable_sum
    intro r _
    exact Measurable.ite (measurableSet_le (hdigit.comp (horbit r m)) measurable_const)
      measurable_const (measurable_const.mul (hcost.comp (horbit r m)))
  have hD (n m : ℕ) : Measurable (D n m) := by dsimp [D]; fun_prop
  have hdiff (f : ℕ → ℕ → ℝ → ℝ) (hf : ∀ n m, Measurable (f n m)) (n j : ℕ) :
      Measurable (diff f n j) := ((hf n _).sub (hf n _)).div_const _
  have decompose (n : ℕ) :
      ∀ᵐ a ∂volume.restrict (Ico (0 : ℝ) 1), ∀ j < n,
        diff D n j a = diff large n j a + diff small n j a := by
    filter_upwards [ae_irrational_angle, ae_restrict_mem (μ := volume) measurableSet_Ico]
      with a hirr ha
    have allLengths (m : ℕ) (hm : m ≤ n) : D n m a = large n m a + small n m a := by
      have h := gauss_expansion n m hm hirr (lt_of_le_of_ne ha.1 hirr.ne_zero.symm) ha.2
      change D n m a = ∑ r ∈ Finset.range n, (-1 : ℝ) ^ r * cost (T^[r] (a, m)) at h
      rw [h]
      dsimp only [small, large]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      split <;> simp
    intro j hj
    dsimp only [diff]
    rw [allLengths _ (by omega), allLengths _ hj.le]
    ring
  refine ⟨γ, hγ, fun t => ?_⟩
  have hbound (n : ℕ) :
      |transform D t n - transform large t n| ≤ max 2 |t| * error n :=
    cosine_error n t _ _ _ (hdiff D hD n) (hdiff large hlg n) (hdiff small hsm n) (decompose n)
  have hzero : Tendsto (fun n => transform D t n - transform large t n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun n => max 2 |t| * error n) atTop (𝓝 0) by
        simpa only [mul_zero] using hsmall.const_mul (max 2 |t|))
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hbound)
  have hfull : Tendsto (transform D t) atTop (𝓝 (Real.exp (-(γ : ℝ) * |t|))) := by
    simpa only [sub_add_cancel, zero_add] using hzero.add (hlarge t)
  have hlim := (uniform_factor_limit t).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hfull)
  rw [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [square_fourier hn.ne']
  dsimp only [Function.comp_apply, transform, diff, D]
  congr 1
  have alg (b : ℝ) : t * (b / Real.log n) = t / Real.log n * b := by ring
  simp only [alg]

end OMA.R_Erdos1002_erdos_1002_variants_kesten_R1_H1_R1
