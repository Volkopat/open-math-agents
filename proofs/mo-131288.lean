import OMAStatements.S_mo_131288
import Mathlib

namespace RadialOscillation

open OMA.S_mo_131288 Polynomial Metric Set Bornology

private theorem radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {f : E → ℝ} {x : E} {r : ℝ} {d : ℕ}
    (hf : lineDegree Ω f d) (hr : 0 < r) (hΩ : ball x (2 * r) ⊆ Ω)
    {y : E} (hy : y ∈ ball x (2 * r)) :
    ∃ P : ℝ[X], P.natDegree ≤ d ∧ P.eval 2 = f y ∧ P.eval 0 = f x ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, P.eval t ∈ f '' ball x r := by
  have hx : x ∈ Ω := hΩ (mem_ball_self (by positivity))
  let v : E := (2 : ℝ)⁻¹ • (y - x)
  obtain ⟨P, hp, hP⟩ := hf x hx v
  have hnorm : ‖v‖ < r := by
    have hy' : ‖y - x‖ < 2 * r := by simpa [dist_eq_norm] using hy
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have he : x + (2 : ℝ) • v = y := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
    abel
  refine ⟨P, hp, ?_, ?_, ?_⟩
  · simpa [he] using hP 2 (he.symm ▸ hΩ hy)
  · simpa using hP 0 (by simpa using hx)
  · intro t ht
    have hb : x + t • v ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have h := abs_le.mpr ht
      exact (mul_le_of_le_one_left (norm_nonneg _) h).trans_lt hnorm
    have hb' : x + t • v ∈ ball x (2 * r) := ball_subset_ball (by linarith) hb
    exact ⟨_, hb, (hP t (hΩ hb')).symm⟩

private theorem quadratic (P : ℝ[X]) (hP : P.natDegree ≤ 2) :
    P.eval 2 = 3 * P.eval 1 + P.eval (-1) - 3 * P.eval 0 := by
  have hp := P.as_sum_range_C_mul_X_pow' (show P.natDegree < 3 by omega)
  nth_rw 1 2 3 4 [hp]
  simp [Finset.sum_range_succ]
  ring

private theorem diam_interval_image {α : Type*} (f : α → ℝ) (S : Set α)
    {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ S, f x ∈ Icc a b) :
    diam (f '' S) ≤ b - a := by
  refine diam_le_of_forall_dist_le (sub_nonneg.mpr hab) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hx' := h x hx
  have hy' := h y hy
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith [hx'.1, hy'.2], by linarith [hx'.2, hy'.1]⟩

private theorem doubling (n d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : lineDegree Ω f d)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (hΩ : ball x (2 * r) ⊆ Ω) (hpos : 0 < osc f x r) :
    osc f x (2 * r) ≤ |(Chebyshev.T ℝ d).eval 2| * osc f x r ∧
      (d ≤ 2 → osc f x (2 * r) ≤ 4 * osc f x r) := by
  let S := f '' ball x r
  let D := diam S
  change 0 < D at hpos
  have hD2 : 0 < D / 2 := half_pos hpos
  have hS : S.Nonempty := ⟨f x, ⟨x, mem_ball_self hr, rfl⟩⟩
  have hb : IsBounded S := by
    by_contra h
    exact hpos.ne' (diam_eq_zero_of_unbounded h)
  have hc : IsCompact (closure S) := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩
  obtain ⟨lo, hlo, hlo'⟩ := hc.exists_isMinOn hS.closure continuous_id.continuousOn
  obtain ⟨hi, hhi, hhi'⟩ := hc.exists_isMaxOn hS.closure continuous_id.continuousOn
  have hdiff : hi - lo ≤ D := by
    have hd := dist_le_diam_of_mem hb.closure hhi hlo
    have hle : lo ≤ hi := hlo' hhi
    rwa [diam_closure, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)] at hd
  have hbounds (s : ℝ) (hs : s ∈ S) : lo ≤ s ∧ s ≤ hi :=
    ⟨hlo' (subset_closure hs), hhi' (subset_closure hs)⟩
  let c : ℝ := (lo + hi) / 2
  have hcenter (s : ℝ) (hs : s ∈ S) : |s - c| ≤ D / 2 := by
    obtain ⟨hl, hu⟩ := hbounds s hs
    exact abs_le.mpr ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  constructor
  · let C := |(Chebyshev.T ℝ d).eval 2|
    have hC : 0 ≤ C := abs_nonneg _
    have hout (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball x (2*r)) :
        |f y - c| ≤ C * D / 2 := by
      obtain ⟨P, hp, h2, _, hsmall⟩ := radial hf hr hΩ hy
      let Q : ℝ[X] := Polynomial.C ((D / 2)⁻¹) * (P - Polynomial.C c)
      have hPC : (P - Polynomial.C c).natDegree ≤ d :=
        (natDegree_sub_le P (Polynomial.C c)).trans (max_le hp (by simp))
      have hnat : Q.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hPC
      have hQdeg : Q.degree ≤ (d : WithBot ℕ) :=
        degree_le_natDegree.trans (by exact_mod_cast hnat)
      have heval (t : ℝ) : Q.eval t = (P.eval t - c) / (D / 2) := by
        simp [Q, div_eq_mul_inv, mul_comm]
      have hQ (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |Q.eval t| ≤ 1 := by
        rw [heval, abs_div, abs_of_pos hD2, div_le_iff₀ hD2, one_mul]
        exact hcenter _ (hsmall t ht)
      have hQN (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |(-Q).eval t| ≤ 1 := by
        simpa using hQ t ht
      have h₁ := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
        (k := 0) (x := 2) (by norm_num) hQdeg hQ
      have h₂ := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
        (k := 0) (x := 2) (by norm_num) (by simpa using hQdeg) hQN
      simp only [Function.iterate_zero, id_eq, eval_neg] at h₁ h₂
      have h : |Q.eval 2| ≤ C := by
        dsimp [C]
        exact abs_le.mpr ⟨by linarith [le_abs_self ((Chebyshev.T ℝ d).eval 2)],
          h₁.trans (le_abs_self _)⟩
      rw [heval, h2, abs_div, abs_of_pos hD2, div_le_iff₀ hD2] at h
      simpa [mul_div_assoc] using h
    change diam (f '' ball x (2*r)) ≤ C * D
    have h := diam_interval_image f (ball x (2*r)) (a := c - C * D / 2)
      (b := c + C * D / 2) (by nlinarith) (fun y hy => by
        have hout' := abs_le.mp (hout y hy)
        exact ⟨by linarith [hout'.1], by linarith [hout'.2]⟩)
    convert h using 1
    ring
  · intro hd
    have hy (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball x (2*r)) :
        f y ∈ Icc (4 * lo - 3 * f x) (4 * hi - 3 * f x) := by
      obtain ⟨P, hp, h2, h0, hs⟩ := radial hf hr hΩ hy
      have h₁ := hbounds _ (hs 1 (by norm_num))
      have h₂ := hbounds _ (hs (-1) (by norm_num))
      have h := quadratic P (hp.trans hd)
      rw [h2, h0] at h
      exact ⟨by linarith [h₁.1,h₂.1], by linarith [h₁.2,h₂.2]⟩
    have h := diam_interval_image f (ball x (2*r)) (by linarith [show lo ≤ hi from hlo' hhi]) hy
    change _ ≤ 4 * D
    exact h.trans (by linarith)

private theorem square_osc (r : ℝ) (hr : 0 < r) : osc (fun t : ℝ => t^2) 0 r = r^2 := by
  let f := fun t : ℝ => t^2
  let S := f '' ball (0 : ℝ) r
  have hs (t : ℝ) (ht : t ∈ ball (0 : ℝ) r) : f t ∈ Icc 0 (r^2) := by
    simp only [mem_ball, Real.dist_eq, sub_zero] at ht
    have ht' := (abs_lt.mp ht)
    exact ⟨sq_nonneg _, by nlinarith [mul_pos (sub_pos.mpr ht'.2) (by linarith [ht'.1] : 0 < r + t)]⟩
  have hsub : S ⊆ Icc 0 (r^2) := by rintro _ ⟨t, ht, rfl⟩; exact hs t ht
  have hb : IsBounded S := isCompact_Icc.isBounded.subset hsub
  have hrmem : r ∈ closure (ball (0 : ℝ) r) := by
    rw [closure_ball 0 hr.ne']
    simp [abs_of_pos hr]
  have h1 : r^2 ∈ closure S :=
    image_closure_subset_closure_image (by fun_prop : Continuous f) ⟨r, hrmem, rfl⟩
  have h0 : 0 ∈ closure S := subset_closure ⟨0, mem_ball_self hr, by simp [f]⟩
  change diam S = r^2
  apply le_antisymm
  · simpa using diam_interval_image f (ball (0 : ℝ) r) (sq_nonneg r) hs
  · have h := dist_le_diam_of_mem hb.closure h1 h0
    simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg r)] using h

private theorem hinge :
    ¬ ∃ M : ℝ, ∀ x r : ℝ, 0 < r → ball x (2*r) ⊆ Ioo (-4) 4 →
      0 < osc (fun t : ℝ => max t 0) x r →
      osc (fun t : ℝ => max t 0) x (2*r) ≤ M * osc (fun t : ℝ => max t 0) x r := by
  rintro ⟨M, hM⟩
  let e : ℝ := (|M| + 1)⁻¹ / 2
  have he : 0 < e := by dsimp [e]; positivity
  have hel : e < 1 := by
    dsimp [e]
    rw [div_lt_iff₀ (by norm_num), inv_lt_comm₀ (by positivity) (by positivity)]
    linarith [abs_nonneg M]
  let x := e - 1
  let f := fun t : ℝ => max t 0
  have ballbounds {t R : ℝ} (ht : t ∈ ball x R) : x - R < t ∧ t < x + R := by
    rw [mem_ball, Real.dist_eq, abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hs (t : ℝ) (ht : t ∈ ball x 1) : f t ∈ Icc 0 e :=
    ⟨le_max_right _ _, max_le (by linarith [(ballbounds ht).2]) he.le⟩
  have ht (t : ℝ) (ht : t ∈ ball x 2) : f t ∈ Icc 0 (1+e) :=
    ⟨le_max_right _ _, max_le (by linarith [(ballbounds ht).2]) (by linarith)⟩
  have hx0 : f x = 0 := max_eq_right (by dsimp [x]; linarith)
  have hehalf : e / 2 ∈ ball x 1 := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [x]
    constructor <;> linarith
  have hunit : 1 ∈ ball x 2 := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [x]
    constructor <;> linarith
  have hsmallB : IsBounded (f '' ball x 1) :=
    (isCompact_Icc (a := (0 : ℝ)) (b := e)).isBounded.subset (by rintro _ ⟨t, ht, rfl⟩; exact hs t ht)
  have hlargeB : IsBounded (f '' ball x 2) :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1 + e)).isBounded.subset (by rintro _ ⟨t, ht', rfl⟩; exact ht t ht')
  have hsmall : 0 < osc f x 1 := by
    have hd := dist_le_diam_of_mem hsmallB
      (mem_image_of_mem f hehalf) (mem_image_of_mem f (mem_ball_self (by norm_num)))
    change 0 < diam (f '' ball x 1)
    exact (show 0 < dist (f (e / 2)) (f x) by simp [hx0, f, he]).trans_le hd
  have hlower : 1 ≤ osc f x 2 := by
    have hd := dist_le_diam_of_mem hlargeB
      (mem_image_of_mem f hunit) (mem_image_of_mem f (mem_ball_self (by norm_num)))
    simpa [osc, hx0, f, Real.dist_eq] using hd
  have hupper : osc f x 1 ≤ e := by
    simpa [osc] using diam_interval_image f (ball x 1) he.le hs
  have hΩ : ball x (2 * (1 : ℝ)) ⊆ Ioo (-4) 4 := by
    intro t h
    obtain ⟨h₁,h₂⟩ := ballbounds h
    dsimp [x] at *
    exact ⟨by linarith, by linarith⟩
  have H := hM x 1 (by norm_num) hΩ hsmall
  rw [mul_one] at H
  have hnew : 1 ≤ |M| * e :=
    hlower.trans (H.trans ((mul_le_mul_of_nonneg_right (le_abs_self M) hsmall.le).trans
      (mul_le_mul_of_nonneg_left hupper (abs_nonneg _))))
  have heq : e * (|M| + 1) = 1 / 2 := by
    dsimp [e]
    field_simp
  nlinarith

theorem result : type_of% @main :=
  ⟨doubling, ⟨square_osc 2 (by norm_num) |>.trans (by norm_num), square_osc 1 (by norm_num) |>.trans (by norm_num)⟩, hinge⟩

end RadialOscillation

theorem OMA.solution : type_of% @OMA.S_mo_131288.main := RadialOscillation.result