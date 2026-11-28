import OMAStatements.S_mo_442224

/-!
Pólya's cone-area inequality and a two-function generalization.
Problem source: Sergei, https://mathoverflow.net/questions/442224 (CC BY-SA 4.0),
citing problem 230 of the 1957 Otto Dunkel Memorial Problem Book.
Formal statement credit: @connoranderson. Independent proof: @grp06.
-/

open Set MeasureTheory
open scoped Topology

private theorem cone_pointwise (x y v w : ℝ)
    (hx : 0 < x) (hy : 0 ≤ y) (hv : 0 ≤ v) (ht : y * v ≤ x * w) :
    2 * (y * Real.sqrt (v^2 + w^2)) ≤
      w * Real.sqrt (x^2 + y^2) + y * ((x*v + y*w) / Real.sqrt (x^2 + y^2)) := by
  let r := Real.sqrt (x^2 + y^2)
  let s := Real.sqrt (v^2 + w^2)
  let A := x*v + y*w
  let T := x*w - y*v
  have hr : 0 < r := Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg y))
  have hr2 : r^2 = x^2 + y^2 := Real.sq_sqrt (by positivity)
  have hs2 : s^2 = v^2 + w^2 := Real.sq_sqrt (by positivity)
  have hw : 0 ≤ w := nonneg_of_mul_nonneg_right
    ((mul_nonneg hy hv).trans ht) hx
  have hA : 0 ≤ A := add_nonneg (mul_nonneg hx.le hv) (mul_nonneg hy hw)
  have hT : 0 ≤ T := sub_nonneg.mpr ht
  have hdot : x*A - y*T = (x^2 + y^2)*v := by dsimp [A, T]; ring
  have hsum : A^2 + T^2 = (x^2 + y^2)*(v^2 + w^2) := by
    dsimp [A, T]
    ring
  have hdiff : 0 ≤ x*A - y*T := by rw [hdot]; positivity
  have hsq :
      (2*y*A + x*T)^2 - (2*y*(r*s))^2 = x^2*T^2 + 4*y*T*(x*A - y*T) := by
    calc
      _ = (2*y*A + x*T)^2 - (2*y)^2*(r^2*s^2) := by ring
      _ = (2*y*A + x*T)^2 - (2*y)^2*(A^2 + T^2) := by rw [hr2, hs2, hsum]
      _ = _ := by ring
  have hsqle : (2*y*(r*s))^2 ≤ (2*y*A + x*T)^2 := by
    apply sub_nonneg.mp
    rw [hsq]
    exact add_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg T))
      (mul_nonneg (by positivity) hdiff)
  have hle : 2*y*(r*s) ≤ 2*y*A + x*T := le_of_sq_le_sq hsqle (by positivity)
  have hradial : r^2*w = y*A + x*T := by
    rw [hr2]
    dsimp [A, T]
    ring
  change 2 * (y*s) ≤ w*r + y*(A/r)
  apply (mul_le_mul_iff_left₀ hr).mp
  calc
    2 * (y*s)*r = 2*y*(r*s) := by ring
    _ ≤ 2*y*A + x*T := hle
    _ = (w*r + y*(A/r))*r := by
      rw [show (w*r + y*(A/r))*r = r^2*w + y*A by
        rw [add_mul, mul_assoc y, div_mul_cancel₀ A hr.ne']
        ring]
      rw [hradial]
      ring

private theorem cone_two_functions (a : ℝ) (x y v w : ℝ → ℝ)
    (ha : 0 < a) (hx0 : x 0 = 0) (hy0 : y 0 = 0)
    (hx : OMA.S_mo_442224.regular a x v) (hy : OMA.S_mo_442224.regular a y w)
    (hslope : ∀ t ∈ Ioo 0 a, 0 < x t ∧ 0 ≤ y t ∧ 0 ≤ v t ∧ y t*v t ≤ x t*w t) :
    2 * (∫ t in (0:ℝ)..a, y t * Real.sqrt ((v t)^2 + (w t)^2)) ≤
      y a * Real.sqrt ((x a)^2 + (y a)^2) := by
  rcases hx with ⟨hxc, hvc, hxd⟩
  rcases hy with ⟨hyc, hwc, hyd⟩
  let F : ℝ → ℝ := fun t => y t * Real.sqrt ((x t)^2 + (y t)^2)
  let g : ℝ → ℝ := fun t => y t * Real.sqrt ((v t)^2 + (w t)^2)
  let P : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, g u
  let G : ℝ → ℝ := fun t => F t - 2 * P t
  have hFc : ContinuousOn F (Icc 0 a) :=
    hyc.mul (((hxc.pow 2).add (hyc.pow 2)).sqrt)
  have hgc : ContinuousOn g (Icc 0 a) :=
    hyc.mul (((hvc.pow 2).add (hwc.pow 2)).sqrt)
  have hPc : ContinuousOn P (Icc 0 a) := by
    have hi : IntervalIntegrable g volume 0 a := hgc.intervalIntegrable_of_Icc ha.le
    have hz : (0 : ℝ) ∈ uIcc (0 : ℝ) a := left_mem_uIcc
    simpa only [uIcc_of_le ha.le] using intervalIntegral.continuousOn_primitive_interval' hi hz
  have hGc : ContinuousOn G (Icc 0 a) := hFc.sub (continuousOn_const.mul hPc)
  let d : ℝ → ℝ := fun t =>
    w t * Real.sqrt ((x t)^2 + (y t)^2) +
      y t * ((x t*v t + y t*w t) / Real.sqrt ((x t)^2 + (y t)^2)) - 2*g t
  have hGd : ∀ t ∈ Ioo 0 a, HasDerivAt G (d t) t := by
    intro t ht
    have hs : 0 < (x t)^2 + (y t)^2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos (hslope t ht).1) (sq_nonneg (y t))
    have hr : 0 < Real.sqrt ((x t)^2 + (y t)^2) := Real.sqrt_pos.2 hs
    have hS : HasDerivAt (fun u => (x u)^2 + (y u)^2)
        (2 * (x t*v t + y t*w t)) t := by
      have hX := (hxd t ht).fun_mul (hxd t ht)
      have hY := (hyd t ht).fun_mul (hyd t ht)
      have he :
          (v t * x t + x t * v t) + (w t * y t + y t * w t) =
            2 * (x t*v t + y t*w t) := by ring
      simpa only [pow_two, he] using hX.fun_add hY
    have hR : HasDerivAt (fun u => Real.sqrt ((x u)^2 + (y u)^2))
        ((x t*v t + y t*w t) / Real.sqrt ((x t)^2 + (y t)^2)) t := by
      convert hS.sqrt hs.ne' using 1 <;> field_simp [hr.ne'] <;> ring
    have hFd : HasDerivAt F
        (w t * Real.sqrt ((x t)^2 + (y t)^2) +
          y t * ((x t*v t + y t*w t) / Real.sqrt ((x t)^2 + (y t)^2))) t :=
      (hyd t ht).fun_mul hR
    have htn : Icc (0 : ℝ) a ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hgt : ContinuousOn g (Icc 0 t) :=
      hgc.mono (fun u hu => ⟨hu.1, hu.2.trans ht.2.le⟩)
    have hit : IntervalIntegrable g volume 0 t := hgt.intervalIntegrable_of_Icc ht.1.le
    have hPd : HasDerivAt P (g t) t :=
      intervalIntegral.integral_hasDerivAt_right hit
        ⟨Icc 0 a, htn, hgc.aestronglyMeasurable measurableSet_Icc⟩
        ((hgc t ⟨ht.1.le, ht.2.le⟩).continuousAt htn)
    exact hFd.sub (hPd.const_mul 2)
  have hd : ∀ t ∈ Ioo 0 a, 0 ≤ d t := by
    intro t ht
    obtain ⟨hxt, hyt, hvt, hst⟩ := hslope t ht
    exact sub_nonneg.mpr (cone_pointwise (x t) (y t) (v t) (w t) hxt hyt hvt hst)
  have hm : MonotoneOn G (Icc 0 a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := d) (convex_Icc 0 a) hGc
    · rw [interior_Icc]
      exact fun t ht => (hGd t ht).hasDerivWithinAt
    · rw [interior_Icc]
      exact hd
  have hends : G 0 ≤ G a := hm ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩ ha.le
  apply sub_nonneg.mp
  simpa [G, F, P, g, hy0] using hends

theorem OMA.solution : type_of% @OMA.S_mo_442224.main := by
  constructor
  · intro a b f p q ha _hb hf0 hfa hf hnonneg hq
    have hpmono : MonotoneOn p (Icc 0 a) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := q) (convex_Icc 0 a) hf.2.1
      · rw [interior_Icc]
        exact fun t ht => (hq t ht).1.hasDerivWithinAt
      · rw [interior_Icc]
        exact fun t ht => (hq t ht).2
    have hslope : ∀ t ∈ Ioo 0 a, f t ≤ t * p t := by
      intro t ht
      have hc : ContinuousOn f (Icc 0 t) :=
        hf.1.mono fun u hu => ⟨hu.1, hu.2.trans ht.2.le⟩
      have hder : ∀ u ∈ Ioo 0 t, HasDerivAt f (p u) u :=
        fun u hu => hf.2.2 u ⟨hu.1, hu.2.trans ht.2⟩
      obtain ⟨c, hc', heq⟩ := exists_hasDerivAt_eq_slope f p ht.1 hc hder
      have hle : p c ≤ p t :=
        hpmono ⟨hc'.1.le, hc'.2.le.trans ht.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hc'.2.le
      simp only [hf0, sub_zero] at heq
      rw [heq] at hle
      simpa only [mul_comm (p t) t] using (div_le_iff₀ ht.1).mp hle
    have hId : OMA.S_mo_442224.regular a (fun t : ℝ => t) (fun _ => 1) :=
      ⟨continuousOn_id, continuousOn_const, fun t _ => hasDerivAt_id t⟩
    simpa [hfa] using
      (cone_two_functions a (fun t => t) f (fun _ => 1) p ha rfl hf0 hId hf
        (fun t ht => ⟨ht.1, hnonneg t ⟨ht.1.le, ht.2.le⟩, zero_le_one,
          by simpa only [mul_one] using hslope t ht⟩))
  · exact cone_two_functions
