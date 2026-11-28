import OMAReductions.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1
import Mathlib

/-! The entropy method for graphs whose edges lie in unique triangles. -/

open Finset

namespace TriangleWeakRegularity

section Average

variable {X I J : Type*} [Fintype X]

private noncomputable def fiber (p : X → I) (i : I) : Finset X := by
  classical
  exact univ.filter (fun x => p x = i)

noncomputable def blockAverage (p : X → I) (f : X → ℝ) (i : I) : ℝ :=
  (∑ x ∈ fiber p i, f x) / (fiber p i).card

noncomputable def blockApprox (p : X → I) (f : X → ℝ) (x : X) : ℝ :=
  blockAverage p f (p x)

theorem blockAverage_mem_Icc (p : X → I) {f : X → ℝ}
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (i : I) :
    blockAverage p f i ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold blockAverage
  have hnon : 0 ≤ ∑ x ∈ fiber p i, f x := sum_nonneg fun x _ => (hf x).1
  refine ⟨div_nonneg hnon (Nat.cast_nonneg _), ?_⟩
  by_cases h : (fiber p i).Nonempty
  · apply (div_le_iff₀ (Nat.cast_pos.2 h.card_pos)).2
    simpa using sum_le_sum (s := fiber p i) (fun x _ => (hf x).2)
  · simp [not_nonempty_iff_eq_empty.1 h]

private theorem card_mul_blockAverage (p : X → I) (f : X → ℝ) (i : I) :
    (fiber p i).card * blockAverage p f i = ∑ x ∈ fiber p i, f x := by
  classical
  unfold blockAverage
  by_cases h : (fiber p i).Nonempty
  · field_simp [Nat.cast_ne_zero.mpr h.card_ne_zero]
  · simp [not_nonempty_iff_eq_empty.1 h]

theorem approx_orthogonal [Fintype I] (p : X → I) (f : X → ℝ) (g : I → ℝ) :
    (∑ x, (f x - blockApprox p f x) * g (p x)) = 0 := by
  classical
  rw [← Finset.sum_fiberwise univ p (fun x => (f x - blockApprox p f x) * g (p x))]
  apply sum_eq_zero
  intro i _
  have hsum :
      (∑ x ∈ fiber p i, (f x - blockApprox p f x) * g (p x)) =
        ∑ x ∈ fiber p i, (f x - blockAverage p f i) * g i := by
    apply sum_congr rfl
    intro x hx
    have hp : p x = i := (mem_filter.1 hx).2
    simp only [blockApprox, hp]
  change (∑ x ∈ fiber p i, (f x - blockApprox p f x) * g (p x)) = 0
  rw [hsum, ← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul, card_mul_blockAverage,
    sub_self, zero_mul]

noncomputable def blockEnergy (p : X → I) (f : X → ℝ) : ℝ :=
  ∑ x, (blockApprox p f x)^2

theorem energy_bounds (p : X → I) {f : X → ℝ}
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ blockEnergy p f ∧ blockEnergy p f ≤ Fintype.card X := by
  unfold blockEnergy
  refine ⟨sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  have h (x : X) : (blockApprox p f x)^2 ≤ 1 :=
    (pow_le_pow_left₀ (blockAverage_mem_Icc p hf (p x)).1
      (blockAverage_mem_Icc p hf (p x)).2 2).trans_eq (one_pow _)
  simpa using sum_le_sum (s := (univ : Finset X)) (fun x _ => h x)

theorem energy_difference [Fintype I] [Fintype J] (p : X → I) (q : X → J)
    (forget : J → I) (href : ∀ x, forget (q x) = p x) (f : X → ℝ) :
    blockEnergy q f - blockEnergy p f =
      ∑ x, (blockApprox q f x - blockApprox p f x)^2 := by
  have hc : ∑ x, (blockApprox q f x - blockApprox p f x) * blockApprox p f x = 0 := by
    have hp := approx_orthogonal p f (blockAverage p f)
    have hq := approx_orthogonal q f (blockAverage p f ∘ forget)
    simp only [Function.comp_apply, href] at hq
    calc
      _ = (∑ x, (f x - blockApprox p f x) * blockAverage p f (p x)) -
          (∑ x, (f x - blockApprox q f x) * blockAverage p f (p x)) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        unfold blockApprox
        ring
      _ = 0 := by rw [hp, hq, sub_self]
  unfold blockEnergy
  calc
    _ = ∑ x, ((blockApprox q f x - blockApprox p f x)^2 +
        2 * ((blockApprox q f x - blockApprox p f x) * blockApprox p f x)) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, hc, mul_zero, add_zero]

theorem energy_gain [Fintype I] [Fintype J] [Nonempty X]
    (p : X → I) (q : X → J) (forget : J → I)
    (href : ∀ x, forget (q x) = p x) (f : X → ℝ)
    (g : J → ℝ) (hg : ∀ j, g j ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : δ * Fintype.card X <
        |∑ x, (f x - blockApprox p f x) * g (q x)|) :
    δ^2 * Fintype.card X < blockEnergy q f - blockEnergy p f := by
  have hs : (∑ x, (f x - blockApprox p f x) * g (q x)) =
      ∑ x, (blockApprox q f x - blockApprox p f x) * g (q x) := by
    have hq := approx_orthogonal q f g
    rw [← add_zero (∑ x, (blockApprox q f x - blockApprox p f x) * g (q x)), ← hq,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [hs] at hw
  let D := fun x => blockApprox q f x - blockApprox p f x
  have hnorm : (∑ x, (g (q x))^2) ≤ (Fintype.card X : ℝ) := by
    have h (x : X) : (g (q x))^2 ≤ 1 :=
      (pow_le_pow_left₀ (hg (q x)).1 (hg (q x)).2 2).trans_eq (one_pow _)
    simpa using sum_le_sum (s := (univ : Finset X)) (fun x _ => h x)
  have hpos : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  have hsq : (δ * Fintype.card X)^2 < (∑ x, D x * g (q x))^2 := by
    rw [← sq_abs (∑ x, D x * g (q x))]
    exact pow_lt_pow_left₀ hw (mul_nonneg hδ hpos.le) (by decide)
  have hCS := sum_mul_sq_le_sq_mul_sq (univ : Finset X) D (g ∘ q)
  have hbig := hsq.trans_le (hCS.trans (mul_le_mul_of_nonneg_left hnorm
    (sum_nonneg fun x _ => sq_nonneg (D x))))
  rw [energy_difference p q forget href]
  apply (mul_lt_mul_iff_right₀ hpos).1
  calc
    _ = (δ * Fintype.card X)^2 := by ring
    _ < _ := by simpa only [mul_comm (Fintype.card X : ℝ)] using hbig

end Average


section Cuts

variable {V : Type*} [Fintype V]

def pairLabel {k : ℕ} (p : V → Fin k) (xy : V × V) : Fin k × Fin k :=
  (p xy.1, p xy.2)

noncomputable def cutApprox {k : ℕ} (p : V → Fin k) (W : V × V → ℝ) (x y : V) : ℝ :=
  blockApprox (pairLabel p) W (x, y)

def CutRegular {k : ℕ} (p : V → Fin k) (W : V × V → ℝ) (δ : ℝ) : Prop :=
  ∀ s t : Finset V, |∑ x ∈ s, ∑ y ∈ t, (W (x, y) - cutApprox p W x y)| ≤
    δ * (Fintype.card V : ℝ)^2

theorem cut_refine_gain [Nonempty V] {k : ℕ} (p : V → Fin k) (W : V × V → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hfail : ¬ CutRegular p W δ) :
    ∃ (q : V → Fin (k * 4)) (forget : Fin (k * 4) → Fin k),
      (∀ v, forget (q v) = p v) ∧
      δ^2 * (Fintype.card V : ℝ)^2 < blockEnergy (pairLabel q) W - blockEnergy (pairLabel p) W := by
  classical
  unfold CutRegular at hfail
  push Not at hfail
  obtain ⟨s, t, hcut⟩ := hfail
  let e : Fin k × (Fin 2 × Fin 2) ≃ Fin (k * 4) :=
    (Equiv.prodCongr (Equiv.refl (Fin k)) finProdFinEquiv).trans finProdFinEquiv
  let q (v : V) := e (p v, if v ∈ s then 1 else 0, if v ∈ t then 1 else 0)
  let forget (v : Fin (k * 4)) : Fin k := (e.symm v).1
  have hforget (v : V) : forget (q v) = p v := by simp [q, forget]
  let g (ab : Fin (k * 4) × Fin (k * 4)) : ℝ :=
    if (e.symm ab.1).2.1 = 1 ∧ (e.symm ab.2).2.2 = 1 then 1 else 0
  have htest (j) : g j ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [g]
    split_ifs <;> norm_num
  have hs :
      (∑ xy, (W xy - blockApprox (pairLabel p) W xy) * g (pairLabel q xy)) =
        ∑ x ∈ s, ∑ y ∈ t, (W (x, y) - cutApprox p W x y) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x ∈ (univ : Finset V).filter (· ∈ s),
          ∑ y ∈ (univ : Finset V).filter (· ∈ t), (W (x, y) - cutApprox p W x y) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro x _
        by_cases hx : x ∈ s
        · simp only [hx, if_true, sum_filter]
          apply sum_congr rfl
          intro y _
          by_cases hy : y ∈ t <;> simp [g, pairLabel, q, hx, hy, cutApprox]
        · simp [g, pairLabel, q, hx]
      _ = _ := by simp
  let projection (ab : Fin (k * 4) × Fin (k * 4)) := (forget ab.1, forget ab.2)
  have href (xy : V × V) : projection (pairLabel q xy) = pairLabel p xy := by
    simp [projection, pairLabel, hforget]
  refine ⟨q, forget, hforget, ?_⟩
  have gain := energy_gain (pairLabel p) (pairLabel q) projection href W g htest hδ (by
    rw [hs]
    simpa [Fintype.card_prod, Nat.cast_mul, pow_two] using hcut)
  simpa [Fintype.card_prod, Nat.cast_mul, pow_two] using gain

private theorem cut_refine_loop [Nonempty V] (W : V × V → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (m : ℕ) {k : ℕ} (p : V → Fin k) :
    ∃ (l : ℕ) (q : V → Fin l) (forget : Fin l → Fin k),
      l ≤ k * 4^m ∧ (∀ v, forget (q v) = p v) ∧
      (CutRegular q W δ ∨ blockEnergy (pairLabel p) W +
        (m : ℝ) * δ^2 * (Fintype.card V : ℝ)^2 ≤ blockEnergy (pairLabel q) W) := by
  induction m generalizing k with
  | zero =>
    exact ⟨k, p, id, by simp, fun _ => rfl, Or.inr (by simp)⟩
  | succ m ih =>
    by_cases hp : CutRegular p W δ
    · refine ⟨k, p, id, ?_, fun _ => rfl, Or.inl hp⟩
      exact Nat.le_mul_of_pos_right _ (by positivity)
    · obtain ⟨r, forget, hforget, hstep⟩ := cut_refine_gain p W hδ hp
      obtain ⟨l, q, proj, hl, hproj, hq⟩ := ih r
      have hsize : l ≤ k * 4^(m + 1) := by
        simpa only [pow_succ, mul_assoc, mul_comm 4 (4 ^ m)] using hl
      refine ⟨l, q, forget ∘ proj, hsize, fun v => (congrArg forget (hproj v)).trans (hforget v), ?_⟩
      rcases hq with hq | hg
      · exact Or.inl hq
      · right
        push_cast
        nlinarith only [hstep, hg]

theorem exists_cut_regular_refinement [Nonempty V] {k : ℕ}
    (W : V × V → ℝ) (hW : ∀ xy, W xy ∈ Set.Icc (0 : ℝ) 1)
    (p : V → Fin k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (l : ℕ) (q : V → Fin l) (forget : Fin l → Fin k),
      l ≤ k * 4^(⌈1 / δ^2⌉₊ + 1) ∧ (∀ v, forget (q v) = p v) ∧ CutRegular q W δ := by
  obtain ⟨l, q, forget, hl, hforget, hq⟩ := cut_refine_loop W hδ.le (⌈1 / δ^2⌉₊ + 1) p
  refine ⟨l, q, forget, hl, hforget, hq.resolve_right ?_⟩
  have hδsq : 0 < δ^2 := by positivity
  have hN : 0 < (Fintype.card V : ℝ)^2 := by positivity
  have hm : 1 / δ^2 < ((⌈1 / δ^2⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith only [Nat.le_ceil (1 / δ^2)]
  have hgt : 1 < ((⌈1 / δ^2⌉₊ + 1 : ℕ) : ℝ) * δ^2 :=
    (div_lt_iff₀ hδsq).1 hm
  have hp := (energy_bounds (pairLabel p) hW).1
  have hq := (energy_bounds (pairLabel q) hW).2
  simp only [Fintype.card_prod, Nat.cast_mul] at hq
  rw [← pow_two] at hq
  have hh := mul_lt_mul_of_pos_right hgt hN
  intro h
  rw [one_mul] at hh
  linarith only [hp, hq, hh, h]

end Cuts

end TriangleWeakRegularity


namespace TriangleRemovalEntropy

private theorem mul_log_ge_neg_half {x : ℝ} (hx : 0 ≤ x) :
    -(1 / 2 : ℝ) ≤ x * Real.log x := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (2 * x) by positivity)
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
    Real.log_mul (by norm_num) hx.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have hcancel : x * (1 / (2 * x)) = (1 / 2 : ℝ) := by field_simp
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hnon := mul_nonneg hx.le (sub_nonneg.mpr hlog)
  simp only [mul_sub, hcancel, zero_sub] at hm
  nlinarith only [hm, hnon]

private noncomputable def defect (d x : ℝ) : ℝ :=
  x * Real.log x - d * Real.log d - (Real.log d + 1) * (x - d)

private theorem defect_eq {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) :
    defect d x = d * ((x / d) * Real.log (x / d) - x / d + 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [defect]
    ring
  unfold defect
  rw [Real.log_div hx.ne' hd.ne']
  field_simp
  ring

private theorem defect_nonneg {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) : 0 ≤ defect d x := by
  rw [defect_eq hd hx]
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hd.le
  let u := x / d
  have hu : 0 < u := div_pos hx hd
  have h := Real.log_le_sub_one_of_pos (show 0 < u⁻¹ by positivity)
  rw [Real.log_inv] at h
  have hm := mul_le_mul_of_nonneg_left h hu.le
  rw [mul_sub, mul_inv_cancel₀ hu.ne'] at hm
  apply mul_nonneg hd.le
  change 0 ≤ u * Real.log u - u + 1
  linarith only [hm]

private theorem defect_of_low {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) (hl : x ≤ d / 4) :
    d / 4 ≤ defect d x := by
  rw [defect_eq hd hx]
  have hu : x / d ≤ 1 / 4 := (div_le_iff₀ hd).2 (by linarith)
  have hm := mul_log_ge_neg_half (div_nonneg hx hd.le)
  calc
    d / 4 = d * (1 / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hu, hm]) hd.le

end TriangleRemovalEntropy

namespace TriangleWeakRegularity

open TriangleRemovalEntropy

section Entropy

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

noncomputable def blockEntropy (p : X → I) (W : X → ℝ) : ℝ :=
  ∑ x, blockApprox p W x * Real.log (blockApprox p W x)

omit [Fintype I] in
private theorem sum_fine_on_coarse (p : X → I) (q : X → J) (forget : J → I)
    (href : ∀ x, forget (q x) = p x) (W : X → ℝ) (i : I) :
    (∑ x ∈ fiber p i, blockApprox q W x) = ∑ x ∈ fiber p i, W x := by
  classical
  have h := approx_orthogonal q W (fun j => if forget j = i then 1 else 0)
  simp only [href, mul_ite, mul_one, mul_zero, ← sum_filter, sum_sub_distrib,
    sub_eq_zero] at h
  exact h.symm

private theorem entropy_difference (p : X → I) (q : X → J) (forget : J → I)
    (href : ∀ x, forget (q x) = p x) (W : X → ℝ) :
    blockEntropy q W - blockEntropy p W =
      ∑ x, defect (blockApprox p W x) (blockApprox q W x) := by
  let g (i : I) := Real.log (blockAverage p W i) + 1
  have hp := approx_orthogonal p W g
  have hq := approx_orthogonal q W (g ∘ forget)
  simp only [Function.comp_apply, href] at hq
  have ht :
      (∑ x, (Real.log (blockApprox p W x) + 1) *
        (blockApprox q W x - blockApprox p W x)) = 0 := by
    calc
      _ = (∑ x, (W x - blockApprox p W x) * g (p x)) -
          (∑ x, (W x - blockApprox q W x) * g (p x)) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        unfold g blockApprox
        ring
      _ = 0 := by rw [hp, hq, sub_self]
  unfold blockEntropy defect
  rw [sum_sub_distrib, sum_sub_distrib, ht, sub_zero]

omit [Fintype I] in
private theorem fine_zero_of_coarse_zero (p : X → I) (q : X → J) (forget : J → I)
    (href : ∀ x, forget (q x) = p x) {W : X → ℝ}
    (hW : ∀ x, W x ∈ Set.Icc (0 : ℝ) 1) {x : X}
    (hx : blockApprox p W x = 0) : blockApprox q W x = 0 := by
  classical
  have hz : (∑ y ∈ fiber p (p x), blockApprox q W y) = 0 := by
    rw [sum_fine_on_coarse p q forget href, ← card_mul_blockAverage]
    change (fiber p (p x)).card * blockApprox p W x = 0
    rw [hx, mul_zero]
  exact (sum_eq_zero_iff_of_nonneg (fun y _ => (blockAverage_mem_Icc q hW (q y)).1)).1 hz x
    (by simp [fiber])

theorem marked_entropy_gain (p : X → I) (q : X → J) (forget : J → I)
    (href : ∀ x, forget (q x) = p x) {W : X → ℝ}
    (hW : ∀ x, W x ∈ Set.Icc (0 : ℝ) 1) (marked : Finset I)
    (hm : ∀ i ∈ marked, ((fiber p i).card : ℝ) / 4 ≤
      ((fiber p i).filter (fun x => blockApprox q W x ≤ blockAverage p W i / 4)).card) :
    (∑ i ∈ marked, ∑ x ∈ fiber p i, W x) / 16 ≤ blockEntropy q W - blockEntropy p W := by
  classical
  rw [entropy_difference p q forget href, ← Finset.sum_fiberwise univ p
    (fun x => defect (blockApprox p W x) (blockApprox q W x)), sum_div]
  have hnon (x : X) : 0 ≤ defect (blockApprox p W x) (blockApprox q W x) := by
    rcases (blockAverage_mem_Icc p hW (p x)).1.eq_or_lt with hz | hp
    · have hpz : blockApprox p W x = 0 := hz.symm
      simp [defect, hpz, fine_zero_of_coarse_zero p q forget href hW hpz]
    · exact defect_nonneg hp (blockAverage_mem_Icc q hW (q x)).1
  calc
    _ ≤ ∑ i ∈ marked, ∑ x ∈ fiber p i, defect (blockApprox p W x) (blockApprox q W x) := by
      apply sum_le_sum
      intro i hi
      let d := blockAverage p W i
      rcases (blockAverage_mem_Icc p hW i).1.eq_or_lt with hd | hd
      · have hz : blockAverage p W i = 0 := hd.symm
        rw [← card_mul_blockAverage, hz, mul_zero, zero_div]
        exact sum_nonneg fun x _ => hnon x
      · let s := (fiber p i).filter (fun x => blockApprox q W x ≤ d / 4)
        calc
          _ = d / 4 * ((fiber p i).card / 4) := by
            rw [← card_mul_blockAverage]
            dsimp [d]
            ring
          _ ≤ d / 4 * (s.card : ℝ) :=
            mul_le_mul_of_nonneg_left (hm i hi) (by positivity)
          _ = ∑ _x ∈ s, d / 4 := by rw [sum_const, nsmul_eq_mul, mul_comm]
          _ ≤ ∑ x ∈ s, defect (blockApprox p W x) (blockApprox q W x) := by
            apply sum_le_sum
            intro x hx
            have he : blockApprox p W x = d := by
              have hpx : p x = i := (mem_filter.1 (mem_filter.1 hx).1).2
              simp [blockApprox, hpx, d]
            rw [he]
            exact defect_of_low hd (blockAverage_mem_Icc q hW (q x)).1 (mem_filter.1 hx).2
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => hnon x
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
      sum_nonneg fun x _ => hnon x

end Entropy

end TriangleWeakRegularity

namespace TriangleCut

variable {V : Type*} [Fintype V]

theorem weighted_cut (D : V → V → ℝ) (ε : ℝ)
    (h : ∀ s t : Finset V, |∑ x ∈ s, ∑ y ∈ t, D x y| ≤ ε)
    (f g : V → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) :
    |∑ x, ∑ y, f x * D x y * g y| ≤ ε := by
  classical
  have positive_cut (d : V → ℝ) (a : V → ℝ)
      (ha : ∀ x, a x ∈ Set.Icc (0 : ℝ) 1) :
      ∑ x, a x * d x ≤ ∑ x ∈ (univ : Finset V).filter (fun x => 0 < d x), d x := by
    rw [sum_filter]
    apply sum_le_sum
    intro x _
    split_ifs with hx
    · exact mul_le_of_le_one_left hx.le (ha x).2
    · exact mul_nonpos_of_nonneg_of_nonpos (ha x).1 (le_of_not_gt hx)
  have upper (D' : V → V → ℝ)
      (h' : ∀ s t : Finset V, ∑ x ∈ s, ∑ y ∈ t, D' x y ≤ ε) :
      ∑ x, ∑ y, f x * D' x y * g y ≤ ε := by
    let d x := ∑ y, D' x y * g y
    let S : Finset V := univ.filter (fun x => 0 < d x)
    let e y := ∑ x ∈ S, D' x y
    let T : Finset V := univ.filter (fun y => 0 < e y)
    calc
      _ = ∑ x, f x * d x := by
        simp_rw [d, mul_sum, mul_assoc]
      _ ≤ ∑ x ∈ S, d x := positive_cut d f hf
      _ = ∑ y, g y * e y := by
        simp_rw [d, e, mul_sum, mul_comm (g _)]
        exact sum_comm
      _ ≤ ∑ y ∈ T, e y := positive_cut e g hg
      _ = ∑ x ∈ S, ∑ y ∈ T, D' x y := sum_comm
      _ ≤ ε := h' S T
  apply abs_le.2
  constructor
  · have hneg := upper (fun x y => -D x y)
      (fun s t => by
        simpa only [sum_neg_distrib, neg_neg] using neg_le_neg (abs_le.1 (h s t)).1)
    simp only [mul_neg, neg_mul, sum_neg_distrib] at hneg
    linarith only [hneg]
  · exact upper D fun s t => (abs_le.1 (h s t)).2

def triangleMass (A B C : V → V → ℝ) (s t u : Finset V) : ℝ :=
  ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, A x y * B y z * C z x

private theorem triangleMass_change_first
    (A A' B C : V → V → ℝ) (s t u : Finset V) (ε : ℝ)
    (hA : ∀ s' t' : Finset V, |∑ x ∈ s', ∑ y ∈ t', (A x y - A' x y)| ≤ ε)
    (hB : ∀ y z, B y z ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ z x, C z x ∈ Set.Icc (0 : ℝ) 1) :
    |triangleMass A B C s t u - triangleMass A' B C s t u| ≤ (u.card : ℝ) * ε := by
  classical
  have hin (z : V) :
      |∑ x ∈ s, ∑ y ∈ t, C z x * (A x y - A' x y) * B y z| ≤ ε := by
    have hw := weighted_cut (fun x y => A x y - A' x y) ε hA
      (fun x => if x ∈ s then C z x else 0)
      (fun y => if y ∈ t then B y z else 0)
      (fun x => by split_ifs; exact hC z x; exact ⟨le_rfl, zero_le_one⟩)
      (fun y => by split_ifs; exact hB y z; exact ⟨le_rfl, zero_le_one⟩)
    convert hw using 1
    congr 1
    calc
      _ = ∑ x ∈ s, ∑ y : V,
          (if x ∈ s then C z x else 0) * (A x y - A' x y) *
            (if y ∈ t then B y z else 0) := by
        apply sum_congr rfl
        intro x hx
        simp only [if_pos hx]
        rw [← sum_subset (s₁ := t) (s₂ := univ) (subset_univ t)]
        · apply sum_congr rfl
          intro y hy
          simp only [if_pos hy]
        · intro y _ hy
          simp [hy]
      _ = _ := by
        apply sum_subset (subset_univ s)
        intro x _ hx
        simp [hx]
  have heq : triangleMass A B C s t u - triangleMass A' B C s t u =
      ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, C z x * (A x y - A' x y) * B y z := by
    unfold triangleMass
    simp only [← sum_sub_distrib]
    trans ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, C z x * (A x y - A' x y) * B y z
    · apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro z _
      ring
    · calc
        _ = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, C z x * (A x y - A' x y) * B y z :=
          sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
  rw [heq]
  calc
    _ ≤ ∑ z ∈ u, |∑ x ∈ s, ∑ y ∈ t, C z x * (A x y - A' x y) * B y z| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ u, ε := sum_le_sum fun z _ => hin z
    _ = _ := by simp

omit [Fintype V] in
private theorem triangleMass_rotate (A B C : V → V → ℝ) (s t u : Finset V) :
    triangleMass A B C s t u = triangleMass B C A t u s := by
  unfold triangleMass
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro x _
  ring

theorem triangleMass_change
    (A A' B B' C C' : V → V → ℝ) (s t u : Finset V) (ε : ℝ)
    (hA : ∀ s' t' : Finset V, |∑ x ∈ s', ∑ y ∈ t', (A x y - A' x y)| ≤ ε)
    (hB : ∀ s' t' : Finset V, |∑ x ∈ s', ∑ y ∈ t', (B x y - B' x y)| ≤ ε)
    (hC : ∀ s' t' : Finset V, |∑ x ∈ s', ∑ y ∈ t', (C x y - C' x y)| ≤ ε)
    (hA' : ∀ x y, A' x y ∈ Set.Icc (0 : ℝ) 1)
    (hBin : ∀ x y, B x y ∈ Set.Icc (0 : ℝ) 1) (hB' : ∀ x y, B' x y ∈ Set.Icc (0 : ℝ) 1)
    (hCin : ∀ x y, C x y ∈ Set.Icc (0 : ℝ) 1) :
    |triangleMass A B C s t u - triangleMass A' B' C' s t u| ≤
      ((s.card + t.card + u.card : ℕ) : ℝ) * ε := by
  have h₁ := triangleMass_change_first A A' B C s t u ε hA hBin hCin
  have h₂ := triangleMass_change_first B B' C A' t u s ε hB hCin hA'
  have h₃ := triangleMass_change_first C C' A' B' u s t ε hC hA' hB'
  rw [← triangleMass_rotate A' B C, ← triangleMass_rotate A' B' C] at h₂
  rw [← triangleMass_rotate B' C A', ← triangleMass_rotate B' C' A',
    ← triangleMass_rotate A' B' C, ← triangleMass_rotate A' B' C'] at h₃
  have heq : triangleMass A B C s t u - triangleMass A' B' C' s t u =
    (triangleMass A B C s t u - triangleMass A' B C s t u) +
      (triangleMass A' B C s t u - triangleMass A' B' C s t u) +
      (triangleMass A' B' C s t u - triangleMass A' B' C' s t u) := by ring
  rw [heq]
  push_cast
  have htriangle := abs_add_le
    (triangleMass A B C s t u - triangleMass A' B C s t u +
      (triangleMass A' B C s t u - triangleMass A' B' C s t u))
    (triangleMass A' B' C s t u - triangleMass A' B' C' s t u)
  have htriangle' := abs_add_le
    (triangleMass A B C s t u - triangleMass A' B C s t u)
    (triangleMass A' B C s t u - triangleMass A' B' C s t u)
  nlinarith only [h₁, h₂, h₃, htriangle, htriangle']

end TriangleCut



namespace TriangleCut

variable {V : Type*} [Fintype V]

noncomputable def lowCount (A : V → V → ℝ) (s t : Finset V) (α : ℝ) : ℕ := by
  classical
  exact ((s ×ˢ t).filter fun xy => A xy.1 xy.2 ≤ α).card

omit [Fintype V] in
private theorem low_sum (A : V → V → ℝ) (s t : Finset V) (α : ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, if A x y ≤ α then (1 : ℝ) else 0) =
      (lowCount A s t α : ℝ) := by
  classical
  rw [lowCount, card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter]
  rw [sum_product]

omit [Fintype V] in
theorem some_low_pair (A B C : V → V → ℝ) (s t u : Finset V) {α : ℝ}
    (hα : 0 < α) (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty)
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ y z, 0 ≤ B y z) (hC : ∀ z x, 0 ≤ C z x)
    (hmass : triangleMass A B C s t u <
      α^3 * ((s.card : ℝ) * t.card * u.card) / 4) :
    (s.card : ℝ) * t.card / 4 ≤ (lowCount A s t α : ℝ) ∨
      (t.card : ℝ) * u.card / 4 ≤ (lowCount B t u α : ℝ) ∨
      (u.card : ℝ) * s.card / 4 ≤ (lowCount C u s α : ℝ) := by
  classical
  by_contra! no
  let bad (w : ℝ) : ℝ := if w ≤ α then 1 else 0
  have hbad (w : ℝ) : 0 ≤ bad w := by
    unfold bad
    split_ifs <;> norm_num
  have hpoint (x y z : V) :
      α^3 ≤ A x y * B y z * C z x + α^3 * (bad (A x y) + bad (B y z) + bad (C z x)) := by
    by_cases h : A x y ≤ α ∨ B y z ≤ α ∨ C z x ≤ α
    · have hsum : 1 ≤ bad (A x y) + bad (B y z) + bad (C z x) := by
        rcases h with h | h | h
        · have hh : bad (A x y) = 1 := if_pos h
          linarith only [hh, hbad (B y z), hbad (C z x)]
        · have hh : bad (B y z) = 1 := if_pos h
          linarith only [hh, hbad (A x y), hbad (C z x)]
        · have hh : bad (C z x) = 1 := if_pos h
          linarith only [hh, hbad (A x y), hbad (B y z)]
      have hmul := mul_le_mul_of_nonneg_left hsum (pow_nonneg hα.le 3)
      have hprod := mul_nonneg (mul_nonneg (hA x y) (hB y z)) (hC z x)
      rw [mul_one] at hmul
      linarith only [hmul, hprod]
    · push Not at h
      have hp : α^3 ≤ A x y * B y z * C z x := by
        rw [pow_succ, pow_two]
        exact mul_le_mul (mul_le_mul h.1.le h.2.1.le hα.le (hA x y))
          h.2.2.le hα.le (mul_nonneg (hA x y) (hB y z))
      exact hp.trans (le_add_of_nonneg_right (mul_nonneg (pow_nonneg hα.le 3)
        (add_nonneg (add_nonneg (hbad _) (hbad _)) (hbad _))))
  have hall :
      (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, α^3) ≤
        ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u,
          (A x y * B y z * C z x + α^3 * (bad (A x y) + bad (B y z) + bad (C z x))) :=
    sum_le_sum fun x _ => sum_le_sum fun y _ => sum_le_sum fun z _ => hpoint x y z
  let N := (s.card : ℝ) * t.card * u.card
  let K₁ := (lowCount A s t α : ℝ) * u.card
  let K₂ := (lowCount B t u α : ℝ) * s.card
  let K₃ := (lowCount C u s α : ℝ) * t.card
  have hK₁ : (∑ x ∈ s, ∑ y ∈ t, ∑ _z ∈ u, bad (A x y)) = K₁ := by
    simp only [sum_const, nsmul_eq_mul, ← mul_sum, K₁]
    rw [show (∑ x ∈ s, ∑ y ∈ t, bad (A x y)) = (lowCount A s t α : ℝ) from low_sum A s t α]
    ring
  have hK₂ : (∑ _x ∈ s, ∑ y ∈ t, ∑ z ∈ u, bad (B y z)) = K₂ := by
    rw [sum_const, nsmul_eq_mul]
    change (s.card : ℝ) * (∑ y ∈ t, ∑ z ∈ u, if B y z ≤ α then 1 else 0) = K₂
    rw [low_sum]
    dsimp [K₂]
    ring
  have hK₃ : (∑ x ∈ s, ∑ _y ∈ t, ∑ z ∈ u, bad (C z x)) = K₃ := by
    simp only [sum_const, nsmul_eq_mul, ← mul_sum]
    rw [sum_comm, show (∑ z ∈ u, ∑ x ∈ s, bad (C z x)) =
      (lowCount C u s α : ℝ) from low_sum C u s α]
    dsimp [K₃]
    ring
  have hleft : (∑ _x ∈ s, ∑ _y ∈ t, ∑ _z ∈ u, α^3) = α^3 * N := by
    simp only [sum_const, nsmul_eq_mul, N]
    ring
  have hmain : α^3 * N ≤ triangleMass A B C s t u + α^3 * (K₁ + K₂ + K₃) := by
    rw [hleft] at hall
    simp only [sum_add_distrib, mul_add, ← mul_sum] at hall
    rw [hK₁, hK₂, hK₃] at hall
    unfold triangleMass
    calc
      _ ≤ _ := hall
      _ = _ := by ring
  have hn₁ : K₁ < N / 4 := by
    have h := mul_lt_mul_of_pos_right no.1 (Nat.cast_pos.2 hu.card_pos : (0 : ℝ) < u.card)
    dsimp [K₁,N]
    linarith only [h]
  have hn₂ : K₂ < N / 4 := by
    have h := mul_lt_mul_of_pos_right no.2.1 (Nat.cast_pos.2 hs.card_pos : (0 : ℝ) < s.card)
    dsimp [K₂,N]
    linarith only [h]
  have hn₃ : K₃ < N / 4 := by
    have h := mul_lt_mul_of_pos_right no.2.2 (Nat.cast_pos.2 ht.card_pos : (0 : ℝ) < t.card)
    dsimp [K₃,N]
    linarith only [h]
  have hbad_lt : α^3 * (K₁ + K₂ + K₃) < α^3 * (3 * N / 4) :=
    mul_lt_mul_of_pos_left (by linarith only [hn₁, hn₂, hn₃]) (pow_pos hα 3)
  change triangleMass A B C s t u < α^3 * N / 4 at hmass
  linarith only [hmain, hmass, hbad_lt]

end TriangleCut

namespace TriangleRemovalCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def orderedEdges : Finset (V × V) :=
  univ.filter fun xy => G.Adj xy.1 xy.2

def orderedTriangles : Finset (V × V × V) :=
  univ.filter fun xyz =>
    G.Adj xyz.1 xyz.2.1 ∧ G.Adj xyz.2.1 xyz.2.2 ∧ G.Adj xyz.2.2 xyz.1

def firstEdge (xyz : V × V × V) : V × V := (xyz.1, xyz.2.1)

def nextEdge (xyz : V × V × V) : V × V := (xyz.2.1, xyz.2.2)

def lastEdge (xyz : V × V × V) : V × V := (xyz.2.2, xyz.1)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem adj_unique_common (hG : G.LocallyLinear)
    {x y : V} (hxy : G.Adj x y) : ∃! z, G.Adj y z ∧ G.Adj z x := by
  obtain ⟨s, hs, hx, hy⟩ := hG.2 hxy
  have hlt : ({x, y} : Finset V).card < s.card := by
    simp [hs.card_eq, hxy.ne]
  obtain ⟨z, hz, hznot⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hzy : z ≠ y := fun h => hznot (by simp [h])
  have hzx : z ≠ x := fun h => hznot (by simp [h])
  have hyz := hs.isClique hy hz hzy.symm
  have hzx' := hs.isClique hz hx hzx
  refine ⟨z, ⟨hyz, hzx'⟩, ?_⟩
  intro w hw
  have hzcl : G.IsNClique 3 ({x, y, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.2 ⟨hxy, hzx'.symm, hyz⟩
  have hwcl : G.IsNClique 3 ({x, y, w} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.2 ⟨hxy, hw.2.symm, hw.1⟩
  have hcl : ({x, y, w} : Finset V) = {x, y, z} := by
    by_contra hne
    have hsub := hG.1 (SimpleGraph.mem_cliqueSet_iff.2 hwcl)
      (SimpleGraph.mem_cliqueSet_iff.2 hzcl) hne
    have he : x = y := hsub (by simp) (by simp)
    exact hxy.ne he
  have hmem : w ∈ ({x, y, z} : Finset V) := hcl ▸ (by simp : w ∈ ({x, y, w} : Finset V))
  simpa [hw.2.ne, hw.1.ne.symm] using hmem

theorem card_triangles_filtered (hG : G.LocallyLinear)
    (P : V × V → Prop) [DecidablePred P] :
    ((orderedTriangles G).filter (fun xyz => P (firstEdge xyz))).card =
      ((orderedEdges G).filter P).card := by
  classical
  let triangles := (orderedTriangles G).filter (fun xyz => P (firstEdge xyz))
  let edges := (orderedEdges G).filter P
  have hil : Set.InjOn firstEdge (triangles : Set (V × V × V)) := by
    rintro ⟨a, b, c⟩ hc ⟨x, y, z⟩ hz he
    change (a, b) = (x, y) at he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp only [triangles, mem_coe, mem_filter, orderedTriangles, mem_univ, true_and] at hc hz
    obtain ⟨w, hw, hu⟩ := adj_unique_common G hG hc.1.1
    rw [hu c hc.1.2, hu z hz.1.2]
  have hi : triangles.image firstEdge = edges := by
    ext e
    obtain ⟨a, b⟩ := e
    simp only [edges, mem_filter, orderedEdges, mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨⟨x, y, z⟩, hz, he⟩ := mem_image.1 h
      change (x, y) = (a, b) at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hmem := Finset.mem_filter.1 hz
      exact ⟨(Finset.mem_filter.1 hmem.1).2.1, hmem.2⟩
    · intro h
      obtain ⟨z, hz, _⟩ := adj_unique_common G hG h.1
      apply mem_image.2
      refine ⟨(a, b, z), ?_, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_univ _, h.1, hz.1, hz.2⟩, h.2⟩
  change triangles.card = edges.card
  rw [← hi, card_image_of_injOn hil]

private def rotate : (V × V × V) ≃ (V × V × V) where
  toFun t := (t.2.1, t.2.2, t.1)
  invFun t := (t.2.2, t.1, t.2.1)
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

omit [DecidableEq V] in
private theorem card_rotate (P : V × V × V → Prop) [DecidablePred P] :
    ((orderedTriangles G).filter (P ∘ rotate)).card = ((orderedTriangles G).filter P).card := by
  classical
  let s := (orderedTriangles G).filter (P ∘ rotate)
  have hh : s.map rotate.toEmbedding = (orderedTriangles G).filter P := by
    ext t
    constructor
    · intro ht
      obtain ⟨u, hu, rfl⟩ := mem_map.1 ht
      obtain ⟨hu, hp⟩ := mem_filter.1 hu
      refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, hp⟩
      have h := (mem_filter.1 hu).2
      exact ⟨h.2.1, h.2.2, h.1⟩
    · intro ht
      obtain ⟨ht, hp⟩ := mem_filter.1 ht
      have h := (mem_filter.1 ht).2
      refine mem_map.2 ⟨rotate.symm t, mem_filter.2 ⟨mem_filter.2
        ⟨mem_univ _, h.2.2, h.1, h.2.1⟩, ?_⟩, rotate.apply_symm_apply t⟩
      change P (rotate (rotate.symm t))
      simpa only [Equiv.apply_symm_apply] using hp
  change s.card = _
  rw [← hh, card_map]

theorem triangles_edge_cover (hG : G.LocallyLinear) (P : V × V → Prop) [DecidablePred P]
    (hcover : ∀ t ∈ orderedTriangles G, P (firstEdge t) ∨ P (nextEdge t) ∨ P (lastEdge t)) :
    (orderedEdges G).card ≤ 3 * ((orderedEdges G).filter P).card := by
  classical
  let ts := orderedTriangles G
  let f₁ := ts.filter (P ∘ firstEdge)
  let f₂ := ts.filter (P ∘ nextEdge)
  let f₃ := ts.filter (P ∘ lastEdge)
  have ht : ts ⊆ f₁ ∪ (f₂ ∪ f₃) := by
    intro x hx
    simpa [f₁, f₂, f₃, hx] using hcover x hx
  have hcard := (card_le_card ht).trans
    ((card_union_le f₁ (f₂ ∪ f₃)).trans (Nat.add_le_add_left (card_union_le f₂ f₃) _))
  have h₁ : f₁.card = ((orderedEdges G).filter P).card := card_triangles_filtered G hG P
  have h₂ : f₂.card = f₁.card := card_rotate G (P ∘ firstEdge)
  have h₃ : f₃.card = f₂.card := card_rotate G (P ∘ nextEdge)
  have hall : ts.card = (orderedEdges G).card := by
    simpa using card_triangles_filtered G hG (fun _ => True)
  rw [h₃, h₂, h₁, hall] at hcard
  omega

end TriangleRemovalCounting
namespace TriangleWeakRegularity

open TriangleRemovalCounting TriangleCut

section GraphCounting

variable {X I : Type*} [Fintype X] [Fintype I]

private theorem sum_marked_fibers [DecidableEq I] (p : X → I) (W : X → ℝ) (marked : Finset I) :
    (∑ i ∈ marked, ∑ x ∈ fiber p i, W x) =
      ∑ x ∈ (univ : Finset X).filter (fun x => p x ∈ marked), W x := by
  classical
  rw [sum_filter, ← sum_fiberwise univ p (fun x => if p x ∈ marked then W x else 0)]
  calc
    _ = ∑ i, if i ∈ marked then ∑ x ∈ fiber p i, W x else 0 := by
      rw [← sum_filter]
      simp
    _ = _ := by
      apply sum_congr rfl
      intro i _
      have hf : (univ.filter (fun x => p x = i)) = fiber p i := by
        ext x
        simp [fiber]
      rw [hf]
      by_cases hi : i ∈ marked
      · rw [if_pos hi]
        apply sum_congr rfl
        intro x hx
        have hpx : p x = i := by simpa [fiber] using hx
        simp [hpx, hi]
      · rw [if_neg hi]
        symm
        apply sum_eq_zero
        intro x hx
        have hpx : p x = i := by simpa [fiber] using hx
        simp [hpx, hi]

private theorem sum_fiber_cards (p : X → I) :
    (∑ i : I, ((fiber p i).card : ℝ)) = Fintype.card X := by
  classical
  simp only [fiber, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [sum_fiberwise _ p]
  simp

end GraphCounting

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def adjacencyWeight (xy : V × V) : ℝ := if G.Adj xy.1 xy.2 then 1 else 0

omit [Fintype V] [DecidableEq V] in
theorem adjacencyWeight_Icc (xy : V × V) : adjacencyWeight G xy ∈ Set.Icc (0 : ℝ) 1 := by
  unfold adjacencyWeight
  split_ifs <;> norm_num

omit [DecidableEq V] in
private theorem filter_edges_as_sum (P : V × V → Prop) [DecidablePred P] :
    (((orderedEdges G).filter P).card : ℝ) =
      ∑ xy ∈ (univ : Finset (V × V)).filter P, adjacencyWeight G xy := by
  rw [orderedEdges, filter_filter, card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, adjacencyWeight, ← sum_filter, filter_filter, and_comm]

private theorem triangle_mass_count (s t u : Finset V) :
    triangleMass (fun x y => adjacencyWeight G (x, y))
      (fun x y => adjacencyWeight G (x, y)) (fun x y => adjacencyWeight G (x, y)) s t u =
      (((orderedTriangles G).filter
        (fun xyz => xyz.1 ∈ s ∧ xyz.2.1 ∈ t ∧ xyz.2.2 ∈ u)).card : ℝ) := by
  have hf :
      (orderedTriangles G).filter (fun xyz => xyz.1 ∈ s ∧ xyz.2.1 ∈ t ∧ xyz.2.2 ∈ u) =
      (s ×ˢ (t ×ˢ u)).filter (fun xyz => G.Adj xyz.1 xyz.2.1 ∧
        G.Adj xyz.2.1 xyz.2.2 ∧ G.Adj xyz.2.2 xyz.1) := by
    ext xyz
    simp only [orderedTriangles, mem_filter, mem_univ, true_and, mem_product, and_comm]
  rw [hf, card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter, sum_product]
  unfold triangleMass
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  unfold adjacencyWeight
  by_cases hxy : G.Adj x y <;> by_cases hyz : G.Adj y z <;> by_cases hzx : G.Adj z x <;>
    simp [hxy, hyz, hzx]

theorem triangle_mass_le_sq (hG : G.LocallyLinear) (s t u : Finset V) :
    triangleMass (fun x y => adjacencyWeight G (x, y))
      (fun x y => adjacencyWeight G (x, y)) (fun x y => adjacencyWeight G (x, y)) s t u ≤
      (Fintype.card V : ℝ)^2 := by
  rw [triangle_mass_count]
  have htotal : (orderedTriangles G).card = (orderedEdges G).card := by
    simpa using card_triangles_filtered G hG (fun _ => True)
  have hcard := (card_filter_le (s := orderedTriangles G)
    (p := fun xyz => xyz.1 ∈ s ∧ xyz.2.1 ∈ t ∧ xyz.2.2 ∈ u))
  have hE : (orderedEdges G).card ≤ Fintype.card V * Fintype.card V := by
    simpa only [Fintype.card_prod] using card_le_univ (orderedEdges G)
  rw [pow_two, ← Nat.cast_mul]
  exact Nat.cast_le.2 (hcard.trans (htotal.le.trans hE))

omit [DecidableEq V] in
private theorem fiber_pairLabel {k : ℕ} (p : V → Fin k) (i j : Fin k) :
    fiber (pairLabel p) (i, j) = fiber p i ×ˢ fiber p j := by
  classical
  ext x
  simp [fiber, pairLabel]

omit [DecidableEq V] in
private theorem small_vertices_card_le {k : ℕ} (p : V → Fin k) (τ : ℝ) (hτ : 0 ≤ τ) :
    (((univ : Finset V).filter (fun x => ((fiber p (p x)).card : ℝ) < τ)).card : ℝ) ≤
      (k : ℝ) * τ := by
  classical
  let marked : Finset (Fin k) := univ.filter (fun i => ((fiber p i).card : ℝ) < τ)
  have heq := sum_marked_fibers p (fun _ => (1 : ℝ)) marked
  simp only [sum_const, nsmul_eq_mul, mul_one, marked, mem_filter, mem_univ, true_and] at heq
  rw [← heq]
  calc
    _ ≤ ∑ _ ∈ marked, τ := sum_le_sum fun i hi => (mem_filter.1 hi).2.le
    _ = (marked.card : ℝ) * τ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.2
      ((card_le_univ marked).trans_eq (Fintype.card_fin k))) hτ

omit [DecidableEq V] in
private theorem sparse_edges_card_le {k : ℕ} (p : V → Fin k) (α : ℝ) (hα : 0 ≤ α) :
    (((orderedEdges G).filter (fun xy =>
      blockAverage (pairLabel p) (adjacencyWeight G) (pairLabel p xy) < α)).card : ℝ) ≤
      α * (Fintype.card V : ℝ)^2 := by
  classical
  let marked := (univ : Finset (Fin k × Fin k)).filter
    (fun i => blockAverage (pairLabel p) (adjacencyWeight G) i < α)
  rw [filter_edges_as_sum]
  have heq := sum_marked_fibers (pairLabel p) (adjacencyWeight G) marked
  simp only [marked, mem_filter, mem_univ, true_and] at heq
  rw [← heq]
  change (∑ i ∈ marked, ∑ xy ∈ fiber (pairLabel p) i, adjacencyWeight G xy) ≤ _
  calc
    _ ≤ ∑ i ∈ marked, α * ((fiber (pairLabel p) i).card : ℝ) := by
      apply sum_le_sum
      intro i hi
      rw [← card_mul_blockAverage, mul_comm]
      have hd := (mem_filter.1 hi).2.le
      exact mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
    _ ≤ ∑ i : Fin k × Fin k, α * ((fiber (pairLabel p) i).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
    _ = _ := by rw [← mul_sum, sum_fiber_cards, Fintype.card_prod, Nat.cast_mul, pow_two]

end Graph

end TriangleWeakRegularity

namespace TriangleWeakRegularity

open TriangleCut TriangleRemovalCounting

section Refinement

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def separatedPairs {k l : ℕ} (p : V → Fin k) (q : V → Fin l)
    (W : V × V → ℝ) : Finset (Fin k × Fin k) :=
  univ.filter (fun i => ((fiber (pairLabel p) i).card : ℝ) / 4 ≤
    ((fiber (pairLabel p) i).filter
      (fun x => blockApprox (pairLabel q) W x ≤ blockAverage (pairLabel p) W i / 4)).card)

private theorem coarse_triple_separated (hG : G.LocallyLinear)
    {k l : ℕ} (p : V → Fin k) (q : V → Fin l) {α θ : ℝ} (hα : 0 < α) (hθ : 0 < θ)
    (hreg : CutRegular q (adjacencyWeight G) (α^3 * θ^3 / 24))
    (hN : 8 / (α^3 * θ^3) < (Fintype.card V : ℝ)) (i j r : Fin k)
    (hi : θ * Fintype.card V ≤ ((fiber p i).card : ℝ))
    (hj : θ * Fintype.card V ≤ ((fiber p j).card : ℝ))
    (hr : θ * Fintype.card V ≤ ((fiber p r).card : ℝ))
    (hij : 4 * α ≤ blockAverage (pairLabel p) (adjacencyWeight G) (i, j))
    (hjr : 4 * α ≤ blockAverage (pairLabel p) (adjacencyWeight G) (j, r))
    (hri : 4 * α ≤ blockAverage (pairLabel p) (adjacencyWeight G) (r, i)) :
    (i, j) ∈ separatedPairs p q (adjacencyWeight G) ∨
      (j, r) ∈ separatedPairs p q (adjacencyWeight G) ∨
      (r, i) ∈ separatedPairs p q (adjacencyWeight G) := by
  classical
  let N : ℝ := Fintype.card V
  let W (x y : V) : ℝ := adjacencyWeight G (x, y)
  let Q (x y : V) : ℝ := cutApprox q (adjacencyWeight G) x y
  let s := fiber p i
  let t := fiber p j
  let u := fiber p r
  have hNpos : 0 < N := (by positivity : (0 : ℝ) ≤ 8 / (α^3 * θ^3)).trans_lt hN
  have hvol : θ^3 * N^3 ≤ (s.card : ℝ) * t.card * u.card := by
    rw [← mul_pow, pow_succ, pow_two]
    exact mul_le_mul (mul_le_mul hi hj (mul_nonneg hθ.le hNpos.le) (Nat.cast_nonneg _))
      hr (mul_nonneg hθ.le hNpos.le) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hQ (x y) : Q x y ∈ Set.Icc (0 : ℝ) 1 :=
    blockAverage_mem_Icc (pairLabel q) (adjacencyWeight_Icc G) (q x, q y)
  have hW (x y) : W x y ∈ Set.Icc (0 : ℝ) 1 := adjacencyWeight_Icc G (x, y)
  have hdiff := triangleMass_change W Q W Q W Q s t u _ hreg hreg hreg hQ hW hQ hW
  have hsizes : ((s.card + t.card + u.card : ℕ) : ℝ) ≤ 3 * N := by
    have hs : (s.card : ℝ) ≤ Fintype.card V := Nat.cast_le.2 (card_le_univ s)
    have ht : (t.card : ℝ) ≤ Fintype.card V := Nat.cast_le.2 (card_le_univ t)
    have hu : (u.card : ℝ) ≤ Fintype.card V := Nat.cast_le.2 (card_le_univ u)
    push_cast
    dsimp [N]
    linarith only [hs, ht, hu]
  have hb : ((s.card + t.card + u.card : ℕ) : ℝ) * (α^3 * θ^3 / 24 * N^2) ≤
      α^3 * θ^3 * N^3 / 8 := by
    calc
      _ ≤ (3 * N) * (α^3 * θ^3 / 24 * N^2) :=
        mul_le_mul_of_nonneg_right hsizes (by positivity)
      _ = _ := by ring
  have hmass : triangleMass Q Q Q s t u ≤ N^2 + α^3 * θ^3 * N^3 / 8 := by
    have h := (abs_le.1 hdiff).1
    have htriangle := triangle_mass_le_sq G hG s t u
    change -(((s.card + t.card + u.card : ℕ) : ℝ) * (α^3 * θ^3 / 24 * N^2)) ≤
      triangleMass W W W s t u - triangleMass Q Q Q s t u at h
    change triangleMass W W W s t u ≤ N^2 at htriangle
    linarith only [h, htriangle, hb]
  have hcutoff : N^2 < α^3 * θ^3 * N^3 / 8 := by
    have h₁ := (div_lt_iff₀ (by positivity : 0 < α^3 * θ^3)).1 hN
    have h₂ := mul_lt_mul_of_pos_right h₁ (show 0 < N^2 by positivity)
    linarith only [h₂]
  have hm : triangleMass Q Q Q s t u < α^3 * ((s.card : ℝ) * t.card * u.card) / 4 := by
    have h := mul_le_mul_of_nonneg_left hvol (show 0 ≤ α^3 by positivity)
    linarith only [hcutoff, hmass, h]
  have cell_nonempty {a : Fin k} (ha : θ * N ≤ ((fiber p a).card : ℝ)) :
      (fiber p a).Nonempty :=
    card_pos.1 (Nat.cast_pos.1 ((mul_pos hθ hNpos).trans_le ha))
  have hlow := some_low_pair Q Q Q s t u hα (cell_nonempty hi) (cell_nonempty hj)
    (cell_nonempty hr) (fun x y => (hQ x y).1) (fun x y => (hQ x y).1)
    (fun x y => (hQ x y).1) hm
  have hl (a b : Fin k)
      (hd : 4 * α ≤ blockAverage (pairLabel p) (adjacencyWeight G) (a, b))
      (he : ((fiber p a).card : ℝ) * (fiber p b).card / 4 ≤
        (lowCount Q (fiber p a) (fiber p b) α : ℝ)) :
      (a, b) ∈ separatedPairs p q (adjacencyWeight G) := by
    apply mem_filter.2
    refine ⟨mem_univ _, ?_⟩
    rw [fiber_pairLabel, card_product, Nat.cast_mul]
    refine he.trans (Nat.cast_le.2 (card_le_card ?_))
    intro xy hxy
    have h := mem_filter.1 hxy
    apply mem_filter.2
    refine ⟨h.1, ?_⟩
    have hle : α ≤ blockAverage (pairLabel p) (adjacencyWeight G) (a, b) / 4 := by
      linarith only [hd]
    exact h.2.trans hle
  rcases hlow with h | h | h
  · exact Or.inl (hl i j hij h)
  · exact Or.inr (Or.inl (hl j r hjr h))
  · exact Or.inr (Or.inr (hl r i hri h))

end Refinement

end TriangleWeakRegularity

namespace TriangleWeakRegularity

open TriangleRemovalCounting

private theorem card_filter_or_le {A : Type*} [DecidableEq A]
    (s : Finset A) (P Q : A → Prop) [DecidablePred P] [DecidablePred Q] :
    (s.filter (fun x => P x ∨ Q x)).card ≤ (s.filter P).card + (s.filter Q).card := by
  rw [filter_or]
  exact card_union_le _ _

section Increment

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def cutoff (d : ℝ) (k : ℕ) : ℝ :=
  8 / ((d / 48)^3 * (d / (48 * k))^3)

noncomputable def tolerance (d : ℝ) (k : ℕ) : ℝ :=
  (d / 48)^3 * (d / (48 * k))^3 / 24

theorem entropy_increment (hG : G.LocallyLinear) {k : ℕ} (p : V → Fin k)
    {d : ℝ} (hd : 0 < d) (hdE : ((orderedEdges G).card : ℝ) = d * (Fintype.card V : ℝ)^2)
    (hN : cutoff d k < (Fintype.card V : ℝ)) :
    ∃ (l : ℕ) (q : V → Fin l), l ≤ k * 4^(⌈1 / (tolerance d k)^2⌉₊ + 1) ∧
      d * (Fintype.card V : ℝ)^2 / 96 ≤
        blockEntropy (pairLabel q) (adjacencyWeight G) -
          blockEntropy (pairLabel p) (adjacencyWeight G) := by
  classical
  let N : ℝ := Fintype.card V
  have hNpos : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  have hk : 0 < k := Nat.zero_lt_of_lt (p (Classical.choice ‹Nonempty V›)).isLt
  let W := adjacencyWeight G
  let α := d / 48
  let θ := d / (48 * (k : ℝ))
  have hα : 0 < α := by dsimp [α]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have htol : 0 < tolerance d k := by unfold tolerance; positivity
  obtain ⟨l, q, forget, hsize, hforget, hreg⟩ :=
    exists_cut_regular_refinement W (adjacencyWeight_Icc G) p htol
  let marked := separatedPairs p q W
  let small (x : V) := ((fiber p (p x)).card : ℝ) < θ * N
  let sparse (xy : V × V) := blockAverage (pairLabel p) W (pairLabel p xy) < d / 12
  let picked (xy : V × V) := pairLabel p xy ∈ marked
  let covered (xy : V × V) := small xy.1 ∨ small xy.2 ∨ sparse xy ∨ picked xy
  have good (xy : V × V) (h : ¬ covered xy) :
      θ * N ≤ ((fiber p (p xy.1)).card : ℝ) ∧
      θ * N ≤ ((fiber p (p xy.2)).card : ℝ) ∧
      4 * α ≤ blockAverage (pairLabel p) W (pairLabel p xy) ∧ ¬ picked xy := by
    dsimp [covered, small, sparse] at h
    push Not at h
    refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
    have he : 4 * α = d / 12 := by dsimp [α]; ring
    simpa only [he] using h.2.2.1
  have hall (v : V × V × V) (_ : v ∈ orderedTriangles G) :
      covered (firstEdge v) ∨ covered (nextEdge v) ∨ covered (lastEdge v) := by
    by_contra! h
    have h₁ := good (firstEdge v) h.1
    have h₂ := good (nextEdge v) h.2.1
    have h₃ := good (lastEdge v) h.2.2
    have hr := coarse_triple_separated G hG p q hα hθ hreg hN
      (p v.1) (p v.2.1) (p v.2.2)
      h₁.1 h₂.1 h₃.1 h₁.2.2.1 h₂.2.2.1 h₃.2.2.1
    exact hr.elim h₁.2.2.2 (fun hh => hh.elim h₂.2.2.2 h₃.2.2.2)
  let E := orderedEdges G
  let tiny : Finset V := univ.filter small
  have htiny : (tiny.card : ℝ) ≤ d * N / 48 := by
    have hb := small_vertices_card_le p (θ * N) (mul_nonneg hθ.le hNpos.le)
    have hθk : (k : ℝ) * (θ * N) = d * N / 48 := by
      dsimp [θ]
      field_simp [(Nat.cast_pos.2 hk : (0 : ℝ) < k).ne']
    exact hb.trans_eq hθk
  have hleft : ((E.filter (fun xy => small xy.1)).card : ℝ) ≤ d * N^2 / 48 := by
    have hs : E.filter (fun xy => small xy.1) ⊆ tiny ×ˢ (univ : Finset V) := by
      intro xy hxy
      exact mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, (mem_filter.1 hxy).2⟩, mem_univ _⟩
    have hb : ((E.filter (fun xy => small xy.1)).card : ℝ) ≤ (tiny.card : ℝ) * N := by
      dsimp [N]
      rw [← Nat.cast_mul]
      exact Nat.cast_le.2 ((card_le_card hs).trans_eq (by rw [card_product, card_univ]))
    calc
      _ ≤ _ := hb.trans (mul_le_mul_of_nonneg_right htiny hNpos.le)
      _ = _ := by ring
  have hright : ((E.filter (fun xy => small xy.2)).card : ℝ) ≤ d * N^2 / 48 := by
    have hs : E.filter (fun xy => small xy.2) ⊆ (univ : Finset V) ×ˢ tiny := by
      intro xy hxy
      exact mem_product.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _, (mem_filter.1 hxy).2⟩⟩
    have hb : ((E.filter (fun xy => small xy.2)).card : ℝ) ≤ N * (tiny.card : ℝ) := by
      dsimp [N]
      rw [← Nat.cast_mul]
      exact Nat.cast_le.2 ((card_le_card hs).trans_eq (by rw [card_product, card_univ]))
    calc
      _ ≤ _ := hb.trans (mul_le_mul_of_nonneg_left htiny hNpos.le)
      _ = _ := by ring
  have hsparse : ((E.filter sparse).card : ℝ) ≤ d / 12 * N^2 :=
    sparse_edges_card_le G p _ (by positivity)
  have hc₁ := card_filter_or_le E (fun xy => small xy.1)
    (fun xy => small xy.2 ∨ sparse xy ∨ picked xy)
  have hc₂ := card_filter_or_le E (fun xy => small xy.2) (fun xy => sparse xy ∨ picked xy)
  have hc₃ := card_filter_or_le E sparse picked
  have hc : (E.filter covered).card ≤
      (E.filter (fun xy => small xy.1)).card + (E.filter (fun xy => small xy.2)).card +
        (E.filter sparse).card + (E.filter picked).card := by
    unfold covered
    omega
  have he : ((E.filter covered).card : ℝ) ≤
      ((E.filter (fun xy => small xy.1)).card : ℝ) + ((E.filter (fun xy => small xy.2)).card : ℝ) +
        ((E.filter sparse).card : ℝ) + ((E.filter picked).card : ℝ) := by exact_mod_cast hc
  have hcover : (E.card : ℝ) ≤ 3 * ((E.filter covered).card : ℝ) := by
    exact_mod_cast triangles_edge_cover G hG covered hall
  have hnum : d * N^2 / 6 ≤ ((E.filter picked).card : ℝ) := by
    have hrel : (E.card : ℝ) = d * N^2 := hdE
    have hpos : 0 ≤ d * N^2 := by positivity
    linarith only [hcover, he, hrel, hleft, hright, hsparse, hpos]
  have hm :
      (∑ i ∈ marked, ∑ xy ∈ fiber (pairLabel p) i, W xy) =
        ((E.filter picked).card : ℝ) := by
    rw [filter_edges_as_sum]
    exact sum_marked_fibers (pairLabel p) W marked
  let forgetPair (ab : Fin l × Fin l) : Fin k × Fin k := (forget ab.1, forget ab.2)
  have href (xy : V × V) : forgetPair (pairLabel q xy) = pairLabel p xy := by
    simp [forgetPair, pairLabel, hforget]
  have hgain := marked_entropy_gain (pairLabel p) (pairLabel q) forgetPair href
    (adjacencyWeight_Icc G) marked (fun _ hi => (mem_filter.1 hi).2)
  rw [hm] at hgain
  exact ⟨l, q, hsize, by linarith only [hnum, hgain]⟩

end Increment

end TriangleWeakRegularity


open Filter

namespace TriangleRemovalTower

private theorem tower_ge_nat (m : ℕ) : (m : ℝ) + 1 ≤ Real.exp^[m] 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Nat.cast_succ]
    linarith only [ih, Real.add_one_le_exp (Real.exp^[m] 1)]

private theorem hits_iff_le_tower (m : ℕ) (x : ℝ) :
    (∃ k ≤ m, Real.log^[k] x ≤ 1) ↔ x ≤ Real.exp^[m] 1 := by
  induction m generalizing x with
  | zero =>
    simp
  | succ m ih =>
    by_cases hx : x ≤ 1
    · have h : (1 : ℝ) ≤ Real.exp^[m + 1] 1 := by
        have hnat : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith only [tower_ge_nat (m + 1), hnat]
      exact ⟨fun _ => hx.trans h, fun _ => ⟨0, by omega, hx⟩⟩
    · have hxpos : 0 < x := by linarith only [lt_of_not_ge hx]
      rw [Function.iterate_succ_apply', ← Real.log_le_iff_le_exp hxpos, ← ih (Real.log x)]
      constructor
      · rintro ⟨k, hk, hh⟩
        cases k with
        | zero => exact (hx hh).elim
        | succ k =>
          exact ⟨k, by omega, by simpa only [← Function.iterate_succ_apply] using hh⟩
      · rintro ⟨k, hk, hh⟩
        exact ⟨k + 1, by omega, by simpa only [Function.iterate_succ_apply] using hh⟩

theorem iteratedLog_le_iff (m : ℕ) (x : ℝ) :
    Real.iteratedLog x ≤ m ↔ x ≤ Real.exp^[m] 1 := by
  have hne : {n : ℕ | Real.log^[n] x ≤ 1}.Nonempty := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, x < k := exists_nat_gt x
    obtain ⟨j, _, hj⟩ := (hits_iff_le_tower k x).2 (by
      linarith only [hk, tower_ge_nat k])
    exact ⟨j, hj⟩
  unfold Real.iteratedLog
  rw [Nat.sInf_def hne, ← hits_iff_le_tower]
  exact ⟨fun h => ⟨Nat.find hne, h, Nat.find_spec hne⟩,
    fun ⟨k, hk, hh⟩ => (Nat.find_min' hne hh).trans hk⟩

theorem iteratedLog_mono : Monotone Real.iteratedLog := by
  intro x y hxy
  exact (iteratedLog_le_iff _ _).2
    (hxy.trans ((iteratedLog_le_iff _ _).1 le_rfl))

theorem tendsto_iteratedLog_nat : Tendsto (fun n : ℕ => Real.iteratedLog n) atTop atTop := by
  rw [tendsto_atTop]
  intro k
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Real.exp^[k] 1 < n := exists_nat_gt _
  filter_upwards [eventually_ge_atTop n] with j hj
  have h : Real.exp^[k] 1 < (j : ℝ) := hn.trans_le (Nat.cast_le.2 hj)
  exact (lt_of_not_ge (fun hh => h.not_ge ((iteratedLog_le_iff _ _).1 hh))).le

theorem iteratedLog_le_log_ceil {b : ℝ} (hb : 0 < b) :
    Real.iteratedLog b ≤ ⌈Real.log b⌉₊ + 1 := by
  apply (iteratedLog_le_iff _ _).2
  rw [Function.iterate_succ_apply']
  apply (Real.log_le_iff_le_exp hb).1
  have ht := tower_ge_nat ⌈Real.log b⌉₊
  linarith only [ht, Nat.le_ceil (Real.log b)]

theorem iteratedLog_le_of_tower {b x : ℝ} {m : ℕ}
    (hb : 0 < b) (hx : x ≤ Real.exp^[m] b) :
    Real.iteratedLog x ≤ m + (⌈Real.log b⌉₊ + 1) := by
  apply (iteratedLog_le_iff _ _).2
  rw [Function.iterate_add_apply]
  apply hx.trans
  exact (Real.exp_monotone.iterate m) ((iteratedLog_le_iff _ _).1 (iteratedLog_le_log_ceil hb))

end TriangleRemovalTower



namespace TriangleRemovalTower

noncomputable def base (d : ℝ) : ℝ := 10^30 / d^12

theorem base_ge {d : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1) :
    (10^30 : ℝ) ≤ base d := by
  unfold base
  have h : d^12 ≤ 1 := by simpa using pow_le_pow_left₀ hd.le hd₁ 12
  exact (le_div_iff₀ (pow_pos hd _)).2 (by nlinarith only [h])

theorem refining_growth {d x : ℝ} {k : ℕ} (hd : 0 < d) (hd₁ : d ≤ 1)
    (hx : base d ≤ x) (hk : 0 < k) (hkx : (k : ℝ) ≤ x) :
    8 / ((d / 48)^3 * (d / (48 * (k : ℝ)))^3) ≤ Real.exp x ∧
      (((k * 4^(⌈1 / (((d / 48)^3 * (d / (48 * (k : ℝ)))^3 / 24)^2)⌉₊ + 1)) : ℕ) : ℝ)
        ≤ Real.exp (Real.exp x) := by
  have hxbase := (base_ge hd hd₁).trans hx
  have hx1 : 1 ≤ x := by linarith only [hxbase]
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hfactorial : (Nat.factorial 8 : ℝ) ≤ x := by
    norm_num [Nat.factorial] at *
    linarith only [hxbase]
  have hbig : base d * x^6 ≤ Real.exp x := by
    calc
      _ ≤ x^7 := by
        rw [show x^7 = x * x^6 by ring]
        exact mul_le_mul_of_nonneg_right hx (by positivity)
      _ ≤ x^8 / (Nat.factorial 8 : ℝ) := by
        apply (le_div_iff₀ (by positivity)).2
        rw [show x^8 = x^7 * x by ring]
        exact mul_le_mul_of_nonneg_left hfactorial (by positivity)
      _ ≤ _ := Real.pow_div_factorial_le_exp x hxpos.le 8
  let T := x^6 / d^12
  have hT : (10^30 : ℝ) * T = base d * x^6 := by dsimp [T, base]; ring
  have hd12 : d^12 ≤ 1 := by simpa using pow_le_pow_left₀ hd.le hd₁ 12
  have hd6 : d^6 ≤ 1 := by simpa using pow_le_pow_left₀ hd.le hd₁ 6
  have hx6 : x ≤ x^6 := by simpa only [pow_one] using pow_le_pow_right₀ hx1 (by decide : 1 ≤ 6)
  have hx6T : x^6 ≤ T := (le_div_iff₀ (pow_pos hd 12)).2 (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd12 (show 0 ≤ x^6 by positivity))
  have hkT : (k : ℝ) ≤ T := hkx.trans (hx6.trans hx6T)
  have hT1 : 1 ≤ T := hx1.trans (hx6.trans hx6T)
  have hk3 : (k : ℝ)^3 ≤ x^6 :=
    (pow_le_pow_left₀ hkpos.le hkx 3).trans (pow_le_pow_right₀ hx1 (by decide : 3 ≤ 6))
  have cutoffEq : 8 / ((d / 48)^3 * (d / (48 * (k : ℝ)))^3) =
      (8 * 48^6 : ℝ) * ((k : ℝ)^3 * d^6) / d^12 := by
    field_simp [hd.ne', hkpos.ne']
  constructor
  · rw [cutoffEq]
    apply le_trans _ hbig
    rw [← hT]
    have hc : (k : ℝ)^3 * d^6 ≤ x^6 := by
      simpa only [mul_one] using mul_le_mul hk3 hd6 (show 0 ≤ d^6 by positivity)
        (show 0 ≤ x^6 by positivity)
    have h₁ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 8 * 48^6)) (show 0 ≤ d^12 by positivity)
    have h₂ : (8 * 48^6 : ℝ) * T ≤ 10^30 * T :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc
      _ ≤ (8 * 48^6 : ℝ) * T := by simpa only [T, mul_div_assoc] using h₁
      _ ≤ _ := h₂
  · let r := 1 / (((d / 48)^3 * (d / (48 * (k : ℝ)))^3 / 24)^2)
    let m := ⌈r⌉₊ + 1
    have hm : (m : ℝ) ≤ r + 2 := by
      dsimp [m]
      push_cast
      linarith only [Nat.ceil_lt_add_one (by positivity : 0 ≤ r)]
    have hrEq : r = (24^2 * 48^12 : ℝ) * (k : ℝ)^6 / d^12 := by
      dsimp [r]
      field_simp [hd.ne', hkpos.ne']
    have hr : r ≤ (10^24 : ℝ) * T := by
      rw [hrEq]
      have hp := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hkpos.le hkx 6) (by norm_num : (0 : ℝ) ≤ 24^2*48^12))
        (show 0 ≤ d^12 by positivity)
      have hcoeff : (24^2*48^12 : ℝ) * T ≤ 10^24*T :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      calc
        _ ≤ (24^2*48^12 : ℝ) * T := by simpa only [T, mul_div_assoc] using hp
        _ ≤ _ := hcoeff
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) := by
      linarith only [Real.log_le_sub_one_of_pos hkpos]
    have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
      linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    have hlog : Real.log ((k : ℝ) * (4 : ℝ)^m) ≤ (10^30 : ℝ) * T := by
      rw [Real.log_mul hkpos.ne' (by positivity), Real.log_pow]
      have hm₄ := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg m)
      nlinarith only [hm₄, hm, hr, hlogk, hkT, hT1]
    change ((k * 4^m : ℕ) : ℝ) ≤ _
    push_cast
    apply (Real.log_le_iff_le_exp (by positivity)).1
    exact hlog.trans (hT.trans_le hbig)

end TriangleRemovalTower

namespace TriangleWeakRegularity

open TriangleRemovalCounting TriangleRemovalTower

section Iteration

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem refine_entropy_many (hG : G.LocallyLinear) {d : ℝ}
    (hd : 0 < d) (hd₁ : d ≤ 1) (hE : ((orderedEdges G).card : ℝ) = d * (Fintype.card V : ℝ)^2)
    (m : ℕ) (hN : Real.exp^[2*m + 1] (base d) < (Fintype.card V : ℝ)) :
    ∃ (k : ℕ) (p : V → Fin k), (k : ℝ) ≤ Real.exp^[2*m] (base d) ∧
      (Fintype.card V : ℝ)^2 * (d * Real.log d) +
        (m : ℝ) * (d * (Fintype.card V : ℝ)^2 / 96) ≤
        blockEntropy (pairLabel p) (adjacencyWeight G) := by
  classical
  let N : ℝ := Fintype.card V
  have hNpos : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  let W := adjacencyWeight G
  let b := base d
  have hb : 1 ≤ b := le_trans (by norm_num) (base_ge hd hd₁)
  have hmono : Monotone (fun i : ℕ => Real.exp^[i] b) := by
    apply monotone_nat_of_le_succ
    intro i
    rw [Function.iterate_succ_apply']
    linarith only [Real.add_one_le_exp (Real.exp^[i] b)]
  induction m with
  | zero =>
    refine ⟨1, fun _ => 0, by simpa [b] using hb, ?_⟩
    let p : V → Fin 1 := fun _ => 0
    have hconst (xy : V × V) : blockApprox (pairLabel p) W xy = d := by
      have hf : fiber (pairLabel p) (pairLabel p xy) = univ := by
        ext
        simp [fiber, pairLabel, p]
      have hs : ∑ xy, W xy = d * N^2 := by
        have hh := filter_edges_as_sum G (fun _ => True)
        simp only [filter_true] at hh
        exact hh.symm.trans hE
      unfold blockApprox blockAverage
      rw [hf, hs, card_univ, Fintype.card_prod, Nat.cast_mul, ← pow_two]
      exact mul_div_cancel_right₀ _ (by positivity)
    suffices blockEntropy (pairLabel p) W = N^2 * (d * Real.log d) by
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact this.ge
    unfold blockEntropy
    simp only [hconst, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    rw [← pow_two]
  | succ m ih =>
    have hsm : Real.exp^[2*m+1] b < N :=
      (hmono (by omega : 2*m+1 ≤ 2*(m+1)+1)).trans_lt hN
    obtain ⟨k, p, hk, hent⟩ := ih hsm
    let x := Real.exp^[2*m] b
    have hx : b ≤ x := hmono (Nat.zero_le _)
    have hkpos : 0 < k := Nat.zero_lt_of_lt (p (Classical.choice ‹Nonempty V›)).isLt
    obtain ⟨hcut, hgrowth⟩ := refining_growth hd hd₁ hx hkpos hk
    have hcut' : cutoff d k < N := hcut.trans_lt (by
      simpa only [x, Function.iterate_succ_apply'] using hsm)
    obtain ⟨l, q, hl, hg⟩ := entropy_increment G hG p hd hE hcut'
    have hl' : (l : ℝ) ≤ Real.exp (Real.exp x) := (Nat.cast_le.2 hl).trans hgrowth
    have hsize : (l : ℝ) ≤ Real.exp^[2*(m+1)] b := by
      rw [show 2*(m+1) = (2*m).succ.succ by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hl'
    refine ⟨l, q, hsize, ?_⟩
    push_cast
    linarith only [hent, hg]

theorem density_bound_of_locallyLinear (hG : G.LocallyLinear) {d : ℝ}
    (hd : 0 < d) (hd₂ : d ≤ 2 / 3)
    (hE : ((orderedEdges G).card : ℝ) = d * (Fintype.card V : ℝ)^2) :
    d ≤ Real.exp (-(Real.iteratedLog (Fintype.card V) : ℝ) / 1100) := by
  let N : ℝ := Fintype.card V
  have hNpos : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  let L := -Real.log d
  have hL : 1 / 3 ≤ L := by
    dsimp [L]
    linarith only [Real.log_le_sub_one_of_pos hd, hd₂]
  have hd₁ : d ≤ 1 := by linarith only [hd₂]
  let m := ⌈96 * L⌉₊ + 1
  let b := base d
  have hb : 1 ≤ b := le_trans (by norm_num) (base_ge hd hd₁)
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlarge : N ≤ Real.exp^[2*m+1] b := by
    by_contra! h
    obtain ⟨k, p, _, hp⟩ := refine_entropy_many G hG hd hd₁ hE m h
    have hnonpos : blockEntropy (pairLabel p) (adjacencyWeight G) ≤ 0 := by
      unfold blockEntropy
      apply sum_nonpos
      intro xy _
      have hh := blockAverage_mem_Icc (pairLabel p) (adjacencyWeight_Icc G) (pairLabel p xy)
      exact mul_nonpos_of_nonneg_of_nonpos hh.1 (Real.log_nonpos hh.1 hh.2)
    have hm : 96 * L < (m : ℝ) := by
      dsimp [m]
      push_cast
      linarith only [Nat.le_ceil (96 * L)]
    have hm' := mul_lt_mul_of_pos_right hm (show 0 < d * N^2 / 96 by positivity)
    dsimp [L] at hm'
    change N^2 * (d * Real.log d) + (m : ℝ) * (d * N^2 / 96) ≤ _ at hp
    linarith only [hp, hnonpos, hm']
  have hlogN := iteratedLog_le_of_tower (show 0 < b by linarith only [hb]) hlarge
  have hcast : (Real.iteratedLog N : ℝ) ≤ (2*m+1 : ℕ) + (⌈Real.log b⌉₊ + 1 : ℕ) := by
    exact_mod_cast hlogN
  have hmUpper : (m : ℝ) ≤ 96 * L + 2 := by
    dsimp [m]
    push_cast
    linarith only [Nat.ceil_lt_add_one (by positivity : 0 ≤ 96 * L)]
  have hlogbUpper : Real.log b ≤ 270 + 12 * L := by
    dsimp [b, base, L]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hlog10 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
    norm_num at *
    linarith only [hlog10]
  have hceil := Nat.ceil_lt_add_one hlogb
  push_cast at hcast
  have hstar : (Real.iteratedLog N : ℝ) ≤ 1100 * L :=
    by linarith only [hcast, hmUpper, hlogbUpper, hceil, hL]
  apply (Real.log_le_iff_le_exp hd).1
  dsimp [L] at hstar
  exact (show Real.log d ≤ -(Real.iteratedLog N : ℝ) / 1100 by linarith only [hstar])

end Iteration

end TriangleWeakRegularity

namespace TriangleWeakRegularity

open SimpleGraph.TripartiteFromTriangles TriangleRemovalCounting TriangleRemovalTower Filter

private theorem ordered_edges_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (orderedEdges G).card = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  unfold orderedEdges
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter,
    card_eq_sum_ones, sum_filter]

theorem tripartite_triangle_bound :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ t : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint t → NoAccidental t →
        (t.card : ℝ) ≤ (n : ℝ)^2 / Real.exp (c * (Real.iteratedLog n : ℝ)) := by
  classical
  refine ⟨1 / 2200, by norm_num, ?_⟩
  have hlarge := tendsto_iteratedLog_nat.eventually_ge_atTop 1100
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn h₁
  intro t ht hno
  let : ExplicitDisjoint t := ht
  let : NoAccidental t := hno
  have hnpos : 0 < n := h₁
  let G := graph t
  have hG : G.LocallyLinear := locallyLinear t
  have hcount : (orderedEdges G).card = 6 * t.card := by
    rw [ordered_edges_card, hG.card_edgeFinset, card_triangles]
    omega
  have hmax : t.card ≤ n^2 := by
    let pr (p : Fin n × Fin n × Fin n) := (p.1, p.2.1)
    have hinj : Set.InjOn pr (t : Set (Fin n × Fin n × Fin n)) := by
      rintro ⟨a,b,c⟩ h ⟨x,y,z⟩ h' he
      change (a,b) = (x,y) at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hz : c = z := ExplicitDisjoint.inj₂ h h'
      rw [hz]
    rw [← card_image_of_injOn hinj]
    exact (card_le_univ _).trans_eq (by simp [Fintype.card_prod, pow_two])
  by_cases h0 : t.card = 0
  · rw [h0, Nat.cast_zero]
    positivity
  let V := Fin n ⊕ Fin n ⊕ Fin n
  let : Nonempty (Fin n ⊕ Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hnpos⟩⟩
  have hV : Fintype.card V = 3 * n := by
    simp [V, Fintype.card_sum]
    omega
  let d : ℝ := (2 / 3) * ((t.card : ℝ) / (n : ℝ)^2)
  have hd : 0 < d := by
    have hc : 0 < t.card := Nat.pos_of_ne_zero h0
    dsimp [d]
    positivity
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hnpos
  have hd₂ : d ≤ 2 / 3 := by
    have hratio : (t.card : ℝ) / (n : ℝ)^2 ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast hmax)
    exact (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans_eq (mul_one _)
  have hE : ((orderedEdges G).card : ℝ) = d * (Fintype.card V : ℝ)^2 := by
    rw [hcount, hV]
    push_cast
    dsimp [d]
    field_simp [hnR.ne']
    ring
  have hD : d ≤ Real.exp (-(Real.iteratedLog (Fintype.card V) : ℝ) / 1100) :=
    density_bound_of_locallyLinear G hG hd hd₂ hE
  let L : ℝ := Real.iteratedLog n
  have hLN : L ≤ (Real.iteratedLog (Fintype.card V) : ℝ) := by
    apply Nat.cast_le.2
    apply iteratedLog_mono
    rw [hV]
    exact_mod_cast (show n ≤ 3 * n by omega)
  have hD' : d ≤ Real.exp (-L / 1100) :=
    hD.trans ((Real.exp_le_exp).2 (by linarith only [hLN]))
  have hL : (1100 : ℝ) ≤ L := by
    change (1100 : ℝ) ≤ (Real.iteratedLog (n : ℝ) : ℝ)
    exact_mod_cast hn
  have hcoeff : (3 / 2 : ℝ) ≤ Real.exp (L / 2200) := by
    apply (Real.log_le_iff_le_exp (by norm_num)).1
    linarith only [hL, Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3/2 by norm_num)]
  have hreal : (t.card : ℝ) / (n : ℝ)^2 ≤ Real.exp (-L / 2200) := by
    calc
      _ = (3/2) * d := by dsimp [d]; ring
      _ ≤ (3/2) * Real.exp (-L / 1100) := mul_le_mul_of_nonneg_left hD' (by norm_num)
      _ ≤ Real.exp (L / 2200) * Real.exp (-L / 1100) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : (1 / 2200 : ℝ) * (Real.iteratedLog n : ℝ) = L / 2200 := by dsimp [L]; ring
  rw [he, div_eq_mul_inv, ← Real.exp_neg]
  simpa only [neg_div, mul_comm] using (div_le_iff₀ (pow_pos hnR 2)).1 hreal

end TriangleWeakRegularity

theorem OMA.solution : OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1.H1 :=
  TriangleWeakRegularity.tripartite_triangle_bound