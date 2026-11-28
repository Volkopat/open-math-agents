import OMAStatements.S_mo_412572
import Mathlib

/-!
MathOverflow 412572: the sets `A = {f < 0}` and `B = {f ≥ 0}` in the open orthant are disjoint
convex cones, and `A` is open (continuity). Convexity rests on a ray lemma: if `f(a) < 0` then
`f(s a) < 0` for all `s > 0` (otherwise the dyadic multiples of `s a`, where `f ≥ 0`, accumulate
at `a`, where `f < 0` near `a`). The geometric Hahn–Banach theorem separates `A` from `B` by a
linear form, which is then nonnegative exactly on `B` (the separation suggested in a comment by
Gjergji Zaimi; scaling handles the boundary). If `B` is empty, `c = (-1, …, -1)` works.
-/

namespace OMA.P412572

open OMA.S_mo_412572

variable {n : ℕ}

lemma orth_add {x y : Fin n → ℝ} (hx : x ∈ orthant n) (hy : y ∈ orthant n) :
    x + y ∈ orthant n := fun i => add_pos (hx i) (hy i)

lemma orth_smul {x : Fin n → ℝ} (hx : x ∈ orthant n) {t : ℝ} (ht : 0 < t) :
    t • x ∈ orthant n := fun i => by simpa using mul_pos ht (hx i)

lemma orth_open : IsOpen (orthant n) := by
  have : orthant n = ⋂ i, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Ioi 0 := by
    ext x; simp [orthant]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage (continuous_apply i)

section
variable {f : (Fin n → ℝ) → ℝ} (hS : SignAdditive f)
include hS

lemma half_neg {x : Fin n → ℝ} (hx : x ∈ orthant n) (h : f x < 0) :
    f ((1 / 2 : ℝ) • x) < 0 := by
  by_contra hc
  push Not at hc
  have hh := orth_smul hx (by norm_num : (0 : ℝ) < 1 / 2)
  have := (hS _ hh _ hh).1 hc hc
  rw [← add_smul] at this
  norm_num at this
  linarith

lemma half_nonneg {x : Fin n → ℝ} (hx : x ∈ orthant n) (h : 0 ≤ f x) :
    0 ≤ f ((1 / 2 : ℝ) • x) := by
  by_contra hc
  push Not at hc
  have hh := orth_smul hx (by norm_num : (0 : ℝ) < 1 / 2)
  have := (hS _ hh _ hh).2.2.2 hc.le hc
  rw [← add_smul] at this
  norm_num at this
  linarith

lemma pow_nonneg' {x : Fin n → ℝ} (hx : x ∈ orthant n) (h : 0 ≤ f x) (k : ℕ) :
    0 ≤ f (((1 / 2 : ℝ) ^ k) • x) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := half_nonneg hS (orth_smul hx (by positivity)) ih
    rwa [smul_smul, ← pow_succ'] at this

lemma mul_nonneg' {x : Fin n → ℝ} (hx : x ∈ orthant n) (h : 0 ≤ f x) (m : ℕ) :
    0 ≤ f (((m : ℝ) + 1) • x) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have := (hS _ (orth_smul hx (by positivity)) _ hx).1 ih h
    have e : (((m + 1 : ℕ) : ℝ) + 1) • x = ((m : ℝ) + 1) • x + x := by
      rw [show (((m + 1 : ℕ) : ℝ) + 1) = ((m : ℝ) + 1) + 1 by push_cast; ring, add_smul, one_smul]
    rwa [e]

/-- Along a ray in the orthant, negativity of `f` propagates to every point. -/
lemma ray_neg (hc : ContinuousOn f (orthant n)) {a : Fin n → ℝ} (ha : a ∈ orthant n)
    (h : f a < 0) {s : ℝ} (hs : 0 < s) : f (s • a) < 0 := by
  by_contra hcon
  push Not at hcon
  have hcont : ContinuousAt (fun t : ℝ => f (t • a)) 1 := by
    have h1 : ContinuousAt f a := hc.continuousAt (orth_open.mem_nhds ha)
    have h2 : ContinuousAt (fun t : ℝ => t • a) 1 :=
      (continuous_id.smul (continuous_const (y := a))).continuousAt
    exact ContinuousAt.comp_of_eq h1 h2 (one_smul ℝ a)
  have hev : ∀ᶠ t in nhds (1 : ℝ), f (t • a) < 0 :=
    hcont.eventually (gt_mem_nhds (by simpa using h))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s * (1 / 2 : ℝ) ^ k < ε := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hs) (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨k, by rwa [lt_div_iff₀ hs, mul_comm] at hk⟩
  set δ : ℝ := s * (1 / 2 : ℝ) ^ k with hδ
  have hδpos : 0 < δ := by positivity
  set m : ℕ := ⌊1 / δ⌋₊ with hm
  have hm1 : (m : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hm2 : 1 / δ < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  set t : ℝ := ((m : ℝ) + 1) * δ
  have ht1 : 1 < t := by
    have := (div_lt_iff₀ hδpos).1 hm2; simpa [t] using this
  have ht2 : t ≤ 1 + δ := by
    have := (le_div_iff₀ hδpos).1 hm1
    simp only [t]; nlinarith
  have hdist : dist t 1 < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have hneg := hball hdist
  have hpos : 0 ≤ f (t • a) := by
    have h0 := pow_nonneg' hS (orth_smul ha hs) hcon k
    have h1 := mul_nonneg' hS (orth_smul (orth_smul ha hs) (by positivity)) h0 m
    have e2 : t • a = ((m : ℝ) + 1) • ((1 / 2 : ℝ) ^ k • (s • a)) := by
      rw [smul_smul, smul_smul]; congr 1; simp only [t, hδ]; ring
    rw [e2]; exact h1
  linarith

lemma ray_nonneg (hc : ContinuousOn f (orthant n)) {b : Fin n → ℝ} (hb : b ∈ orthant n)
    (h : 0 ≤ f b) {s : ℝ} (hs : 0 < s) : 0 ≤ f (s • b) := by
  by_contra hcon
  push Not at hcon
  have := ray_neg hS hc (orth_smul hb hs) hcon (inv_pos.2 hs)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at this
  linarith

end

theorem solve : ∀ (n : ℕ), 0 < n → ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (orthant n) →
    SignAdditive f → ∃ c : Fin n → ℝ, ∀ x ∈ orthant n, (0 ≤ ∑ i, c i * x i ↔ 0 ≤ f x) := by
  intro n hn f hc hS
  set A : Set (Fin n → ℝ) := orthant n ∩ f ⁻¹' Set.Iio 0
  set B : Set (Fin n → ℝ) := orthant n ∩ f ⁻¹' Set.Ici 0
  by_cases hB : B.Nonempty
  swap
  · refine ⟨fun _ => -1, fun x hx => ?_⟩
    have hfx : f x < 0 := by
      by_contra h; push Not at h; exact hB ⟨x, hx, h⟩
    have hsum : ∑ i, (-1) * x i < 0 := by
      have : ∑ i : Fin n, (-1) * x i = -∑ i, x i := by simp
      rw [this, neg_lt_zero]
      exact Finset.sum_pos (fun i _ => hx i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    constructor <;> intro h <;> linarith
  obtain ⟨b0, hb0⟩ := hB
  have hAo : IsOpen A := hc.isOpen_inter_preimage orth_open isOpen_Iio
  have hAc : Convex ℝ A := by
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ => ?_
    have h1 := ray_neg hS hc hx.1 hx.2 ha
    have h2 := ray_neg hS hc hy.1 hy.2 hb
    exact ⟨orth_add (orth_smul hx.1 ha) (orth_smul hy.1 hb),
      (hS _ (orth_smul hx.1 ha) _ (orth_smul hy.1 hb)).2.2.2 h1.le h2⟩
  have hBc : Convex ℝ B := by
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ => ?_
    have h1 := ray_nonneg hS hc hx.1 hx.2 ha
    have h2 := ray_nonneg hS hc hy.1 hy.2 hb
    exact ⟨orth_add (orth_smul hx.1 ha) (orth_smul hy.1 hb),
      (hS _ (orth_smul hx.1 ha) _ (orth_smul hy.1 hb)).1 h1 h2⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have h1 : f x < 0 := hxA.2
    have h2 : 0 ≤ f x := hxB.2
    linarith
  obtain ⟨φ, u, hA, hBu⟩ := geometric_hahn_banach_open hAc hAo hBc hdisj
  -- on `B` the form is nonnegative, and `u ≤ 0`
  have hscale : ∀ x ∈ B, ∀ t : ℝ, 0 < t → u ≤ t * φ x := by
    intro x hx t ht
    have := hBu _ ⟨orth_smul hx.1 ht, ray_nonneg hS hc hx.1 hx.2 ht⟩
    simpa [map_smul] using this
  have hu : u ≤ 0 := by
    by_contra hu; push Not at hu
    rcases le_or_gt (φ b0) 0 with h | h
    · have := hscale b0 hb0 1 one_pos; nlinarith
    · have := hscale b0 hb0 (u / (2 * φ b0)) (by positivity)
      rw [div_mul_eq_mul_div, mul_div_assoc, div_mul_eq_div_div] at this
      field_simp at this
      linarith
  have hBnn : ∀ x ∈ B, 0 ≤ φ x := by
    intro x hx
    by_contra h; push Not at h
    have := hscale x hx ((|u| + 1) / (-φ x)) (div_pos (by positivity) (by linarith))
    have hne : φ x ≠ 0 := h.ne
    rw [div_mul_eq_mul_div, show (|u| + 1) * φ x / -φ x = -(|u| + 1) by field_simp] at this
    linarith [neg_abs_le u]
  refine ⟨fun i => φ (Pi.single i 1), fun x hx => ?_⟩
  have hφ : φ x = ∑ i, φ (Pi.single i 1) * x i := by
    conv_lhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [← hφ]
  constructor
  · intro h
    by_contra hf; push Not at hf
    have := hA x ⟨hx, hf⟩
    linarith
  · intro h
    exact hBnn x ⟨hx, h⟩

end OMA.P412572

theorem OMA.solution : type_of% @OMA.S_mo_412572.main := OMA.P412572.solve
