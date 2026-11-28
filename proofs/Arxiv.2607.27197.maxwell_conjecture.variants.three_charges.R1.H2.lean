import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1

/-!
# Collinear three-charge Maxwell bound (`H2`)

When three distinct nonzero point charges in `ℝ³` are collinear, any off-axis
equilibrium has a degenerate Hessian along the azimuthal direction orthogonal
to both the charge axis and the radial offset. Hence all equilibria lie on the
charge line, where a 1D sign and strict-convexity analysis across the four
complementary open intervals bounds the number of equilibria by at most `4`.
-/

-- Credit: @LiJiaHua1024

namespace OMA.Proof_Maxwell_ThreeCharges_R1_H2

open Arxiv.«2607.27197» InnerProductSpace
open scoped BigOperators Gradient RealInnerProductSpace Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/- ### Part 1: Strict convexity of `x ↦ 1 / x²` and root bounds -/

private lemma inv_sq_strictConvexOn :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => (1 : ℝ) / x ^ 2) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hcomb : 0 < a * x + b * y := by nlinarith
  simp only [smul_eq_mul]
  rw [div_lt_iff₀ (pow_pos hcomb 2)]
  have h1 : (a * (1 / x ^ 2) + b * (1 / y ^ 2)) * (a * x + b * y) ^ 2 - 1 =
      a * b * (x - y) ^ 2 * (a * x ^ 2 + 2 * x * y + b * y ^ 2) / (x ^ 2 * y ^ 2) := by
    have hxne : x ≠ 0 := hx0.ne'
    have hyne : y ≠ 0 := hy0.ne'
    field_simp
    have hba : b = 1 - a := by linarith
    subst hba
    ring
  have hdiff : (x - y) ^ 2 > 0 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hpos : 0 < a * b * (x - y) ^ 2 *
      (a * x ^ 2 + 2 * x * y + b * y ^ 2) /
      (x ^ 2 * y ^ 2) := by
    apply div_pos
    · apply mul_pos (mul_pos (mul_pos ha hb) hdiff)
      have : 0 < x * y := mul_pos hx0 hy0
      nlinarith
    · positivity
  linarith

private lemma strictConvexOn_at_most_two_zeros {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) (c : ℝ) :
    {t ∈ s | f t = c}.encard ≤ 2 := by
  by_contra hgt
  set A := {t ∈ s | f t = c}
  have hne1 : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Set.encard_empty] at hgt
    exact hgt (by norm_num)
  obtain ⟨x, hxA⟩ := hne1
  have hne2 : (A \ {x}).Nonempty := by
    by_contra h
    have hsub : A ⊆ {x} := Set.diff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
    have hle : A.encard ≤ 1 := (Set.encard_le_encard hsub).trans (by simp)
    exact hgt (hle.trans (by norm_num))
  obtain ⟨y, hyA, hyx⟩ := hne2
  have hxy : x ≠ y := Ne.symm hyx
  have hne3 : (A \ {x, y}).Nonempty := by
    by_contra h
    have hsub : A ⊆ {x, y} := Set.diff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
    have hle : A.encard ≤ 2 := (Set.encard_le_encard hsub).trans (by
      calc ({x, y} : Set ℝ).encard ≤ ({x} : Set ℝ).encard + ({y} : Set ℝ).encard := Set.encard_union_le _ _
        _ = 2 := by norm_num)
    exact hgt hle
  obtain ⟨z, hzA, hzxy⟩ := hne3
  have hxz : x ≠ z := fun h => hzxy (Or.inl h.symm)
  have hyz : y ≠ z := fun h => hzxy (Or.inr h.symm)
  have htriple : ∃ a b d : ℝ, a ∈ A ∧ b ∈ A ∧ d ∈ A ∧ a < b ∧ b < d := by
    rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
    rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
    · exact ⟨x, y, z, hxA, hyA, hzA, h1, h3⟩
    · exact ⟨x, z, y, hxA, hzA, hyA, h2, h3⟩
    · exact ⟨z, x, y, hzA, hxA, hyA, h2, h1⟩
    · exact ⟨z, x, y, hzA, hxA, hyA, h2, h1⟩
    · exact ⟨y, x, z, hyA, hxA, hzA, h1, h2⟩
    · exact ⟨y, x, z, hyA, hxA, hzA, h1, h2⟩
    · exact ⟨y, z, x, hyA, hzA, hxA, h3, h2⟩
    · exact ⟨z, y, x, hzA, hyA, hxA, h3, h1⟩
  obtain ⟨a, b, d, haS, hbS, hdS, hab, hbd⟩ := htriple
  set u : ℝ := (d - b) / (d - a)
  set v : ℝ := (b - a) / (d - a)
  have hda : 0 < d - a := by linarith
  have hu : 0 < u := div_pos (by linarith) hda
  have hv : 0 < v := div_pos (by linarith) hda
  have huv : u + v = 1 := by
    simp only [u, v]
    field_simp [hda.ne']
    ring
  have hb_eq : u • a + v • d = b := by
    simp only [u, v, smul_eq_mul]
    field_simp [hda.ne']
    ring
  have hlt := hf.2 haS.1 hdS.1 (by linarith) hu hv huv
  rw [hb_eq, haS.2, hbS.2, hdS.2] at hlt
  simp only [smul_eq_mul] at hlt
  have : u * c + v * c = c := by rw [← add_mul, huv, one_mul]
  linarith

private lemma two_pole_strictConvexOn {p q α β : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hα : 0 < α) (hβ : 0 < β) :
    StrictConvexOn ℝ (Set.Ioo (-1 / α) (1 / β))
      (fun z : ℝ => p / (1 + α * z) ^ 2 + q / (1 - β * z) ^ 2) := by
  have h1 : StrictConvexOn ℝ (Set.Ioo (-1 / α) (1 / β)) (fun z : ℝ => p / (1 + α * z) ^ 2) := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hx' : 0 < 1 + α * x := by
      have := (div_lt_iff₀ hα).mp hx.1; linarith
    have hy' : 0 < 1 + α * y := by
      have := (div_lt_iff₀ hα).mp hy.1; linarith
    have hne : 1 + α * x ≠ 1 + α * y := by
      intro heq; exact hxy (mul_left_cancel₀ hα.ne' (by linarith))
    have hsc := inv_sq_strictConvexOn.2 hx' hy' hne ha hb hab
    have hlin : a • (1 + α * x) + b • (1 + α * y) = 1 + α * (a • x + b • y) := by
      simp only [smul_eq_mul]; nlinarith [hab]
    rw [hlin] at hsc
    simp only [smul_eq_mul] at hsc ⊢
    have := mul_lt_mul_of_pos_left hsc hp
    linarith [show p * (1 / (1 + α * (a * x + b * y)) ^ 2) = p / (1 + α * (a * x + b * y)) ^ 2 by ring,
      show p * (a * (1 / (1 + α * x) ^ 2) + b * (1 / (1 + α * y) ^ 2)) =
        a * (p / (1 + α * x) ^ 2) + b * (p / (1 + α * y) ^ 2) by ring]
  have h2 : StrictConvexOn ℝ (Set.Ioo (-1 / α) (1 / β)) (fun z : ℝ => q / (1 - β * z) ^ 2) := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hx' : 0 < 1 - β * x := by
      have := (lt_div_iff₀ hβ).mp hx.2; linarith
    have hy' : 0 < 1 - β * y := by
      have := (lt_div_iff₀ hβ).mp hy.2; linarith
    have hne : 1 - β * x ≠ 1 - β * y := by
      intro heq; exact hxy (mul_left_cancel₀ hβ.ne' (by linarith))
    have hsc := inv_sq_strictConvexOn.2 hx' hy' hne ha hb hab
    have hlin : a • (1 - β * x) + b • (1 - β * y) = 1 - β * (a • x + b • y) := by
      simp only [smul_eq_mul]; nlinarith [hab]
    rw [hlin] at hsc
    simp only [smul_eq_mul] at hsc ⊢
    have := mul_lt_mul_of_pos_left hsc hq
    linarith [show q * (1 / (1 - β * (a * x + b * y)) ^ 2) = q / (1 - β * (a * x + b * y)) ^ 2 by ring,
      show q * (a * (1 / (1 - β * x) ^ 2) + b * (1 / (1 - β * y) ^ 2)) =
        a * (q / (1 - β * x) ^ 2) + b * (q / (1 - β * y) ^ 2) by ring]
  exact h1.add h2

private lemma strictMonoOn_at_most_one_zero {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictMonoOn f s) (c : ℝ) :
    {t ∈ s | f t = c}.encard ≤ 1 := by
  refine Set.encard_le_one_iff.mpr ?_
  intro x y hx hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_lt (hf hx.1 hy.1 hlt)) (hx.2.trans hy.2.symm)
  · exact (ne_of_lt (hf hy.1 hx.1 hgt)) (hy.2.trans hx.2.symm)

/- ### Part 2: 1D root bound (at most 4 roots across all 4 intervals) -/

private noncomputable def force1D (w c : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, -w i * (t - c i) / |t - c i| ^ 3

private lemma force1D_eq_on_interval (w₀ w₁ w₂ c₀ c₁ c₂ t : ℝ)
    (h0 : t ≠ c₀) (h1 : t ≠ c₁) (h2 : t ≠ c₂) :
    force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t =
      (if t < c₀ then w₀ / (t - c₀) ^ 2 else -w₀ / (t - c₀) ^ 2) +
      (if t < c₁ then w₁ / (t - c₁) ^ 2 else -w₁ / (t - c₁) ^ 2) +
      (if t < c₂ then w₂ / (t - c₂) ^ 2 else -w₂ / (t - c₂) ^ 2) := by
  have hterm (w c : ℝ) (hc : t ≠ c) :
      -w * (t - c) / |t - c| ^ 3 =
        if t < c then w / (t - c) ^ 2 else -w / (t - c) ^ 2 := by
    have hne : t - c ≠ 0 := sub_ne_zero.mpr hc
    by_cases hlt : t < c
    · rw [if_pos hlt, abs_of_neg (sub_neg.mpr hlt)]
      field_simp [hne]
    · rw [if_neg hlt, abs_of_pos (sub_pos.mpr (lt_of_le_of_ne (not_lt.mp hlt) hc.symm))]
      field_simp [hne]
  unfold force1D
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hterm w₀ c₀ h0, hterm w₁ c₁ h1, hterm w₂ c₂ h2]

private lemma card_roots_outer_le_two {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : 0 < w₀) (hw1 : w₁ < 0) (hw2 : 0 < w₂) :
    {t : ℝ | (t < c₀ ∨ c₂ < t) ∧
      w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}.encard ≤ 2 := by
  set α : ℝ := c₁ - c₀
  set β : ℝ := c₂ - c₁
  have hα : 0 < α := by linarith
  have hβ : 0 < β := by linarith
  let φ : ℝ → ℝ := fun z => w₀ / (1 + α * z) ^ 2 + w₂ / (1 - β * z) ^ 2
  have hsc := two_pole_strictConvexOn hw0 hw2 hα hβ
  have hbound := strictConvexOn_at_most_two_zeros hsc (-w₁)
  let g : ℝ → ℝ := fun t => 1 / (t - c₁)
  have hinj : Set.InjOn g {t : ℝ | (t < c₀ ∨ c₂ < t) ∧
      w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0} := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hne1 : t₁ - c₁ ≠ 0 := by rcases ht₁.1 with h | h <;> linarith
    have hne2 : t₂ - c₁ ≠ 0 := by rcases ht₂.1 with h | h <;> linarith
    have : t₁ - c₁ = t₂ - c₁ := by
      have := congrArg Inv.inv heq
      simpa [g] using this
    linarith
  have hmaps : Set.MapsTo g
      {t : ℝ | (t < c₀ ∨ c₂ < t) ∧
        w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}
      {z ∈ Set.Ioo (-1 / α) (1 / β) | φ z = -w₁} := by
    intro t ⟨ht, heq⟩
    have hne1 : t - c₁ ≠ 0 := by rcases ht with h | h <;> linarith
    have hne0 : t - c₀ ≠ 0 := by rcases ht with h | h <;> linarith
    have hne2 : t - c₂ ≠ 0 := by rcases ht with h | h <;> linarith
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases ht with h | h
      · have h1 : 1 / (-(t - c₁)) < 1 / α := one_div_lt_one_div_of_lt hα (by linarith)
        have h2 : g t = -(1 / (-(t - c₁))) := by
          dsimp only [g]
          rw [div_neg, neg_neg]
        have h3 : -1 / α = -(1 / α) := by ring
        linarith
      · have hpos : 0 < g t := one_div_pos.mpr (by linarith)
        have hneg : -1 / α < 0 := div_neg_of_neg_of_pos (by norm_num) hα
        linarith
    · rcases ht with h | h
      · have hneg : g t < 0 := div_neg_of_pos_of_neg zero_lt_one (by linarith)
        have hpos : 0 < 1 / β := one_div_pos.mpr hβ
        linarith
      · have hgt : β < t - c₁ := by linarith
        exact one_div_lt_one_div_of_lt hβ hgt
    · have h1 : 1 + α * g t = (t - c₀) / (t - c₁) := by
        simp only [g, α]; field_simp [hne1]; ring
      have h2 : 1 - β * g t = (t - c₂) / (t - c₁) := by
        simp only [g, β]; field_simp [hne1]; ring
      simp only [φ, h1, h2]
      have hmul := congrArg (· * (t - c₁) ^ 2) heq
      simp only [zero_mul] at hmul
      have hrewrite : (w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2) * (t - c₁) ^ 2 =
          w₀ / ((t - c₀) / (t - c₁)) ^ 2 + w₂ / ((t - c₂) / (t - c₁)) ^ 2 + w₁ := by
        field_simp [hne0, hne1, hne2]
        ring
      linarith
  calc
    _ = (g '' _).encard := (hinj.encard_image).symm
    _ ≤ {z ∈ Set.Ioo (-1 / α) (1 / β) | φ z = -w₁}.encard :=
        Set.encard_le_encard hmaps.image_subset
    _ ≤ 2 := hbound

private lemma card_roots_mid1_le_two {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : 0 < w₀) (hw1 : w₁ < 0) (hw2 : 0 < w₂) :
    {t : ℝ | (c₀ < t ∧ t < c₁) ∧
      -w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}.encard ≤ 2 := by
  set α : ℝ := c₂ - c₀
  set β : ℝ := c₂ - c₁
  have hα : 0 < α := by linarith
  have hβ : 0 < β := by linarith
  have hαβ : β < α := by linarith
  -- Map t ∈ (c₀, c₁) to u = 1 / (c₂ - t) ∈ (1/α, 1/β); shift to z = u - (1/α + 1/β)/2?
  -- Even simpler: map t ↦ u = 1 / (c₂ - t) and check StrictConvexOn directly on Ioo (1/α) (1/β)
  let ψ : ℝ → ℝ := fun u => w₀ / (α * u - 1) ^ 2 + (-w₁) / (1 - β * u) ^ 2
  have hsc : StrictConvexOn ℝ (Set.Ioo (1 / α) (1 / β)) ψ := by
    have h1 : StrictConvexOn ℝ (Set.Ioo (1 / α) (1 / β)) (fun u => w₀ / (α * u - 1) ^ 2) := by
      refine ⟨convex_Ioo _ _, ?_⟩
      intro x hx y hy hxy a b ha hb hab
      have hx' : 0 < α * x - 1 := by
        have := (div_lt_iff₀ hα).mp hx.1; linarith
      have hy' : 0 < α * y - 1 := by
        have := (div_lt_iff₀ hα).mp hy.1; linarith
      have hne : α * x - 1 ≠ α * y - 1 := by
        intro heq; exact hxy (mul_left_cancel₀ hα.ne' (by linarith))
      have hsc0 := inv_sq_strictConvexOn.2 hx' hy' hne ha hb hab
      have hlin : a • (α * x - 1) + b • (α * y - 1) = α * (a • x + b • y) - 1 := by
        simp only [smul_eq_mul]; nlinarith [hab]
      rw [hlin] at hsc0
      simp only [smul_eq_mul] at hsc0 ⊢
      have := mul_lt_mul_of_pos_left hsc0 hw0
      linarith [show w₀ * (1 / (α * (a * x + b * y) - 1) ^ 2) = w₀ / (α * (a * x + b * y) - 1) ^ 2 by ring,
        show w₀ * (a * (1 / (α * x - 1) ^ 2) + b * (1 / (α * y - 1) ^ 2)) =
          a * (w₀ / (α * x - 1) ^ 2) + b * (w₀ / (α * y - 1) ^ 2) by ring]
    have h2 : StrictConvexOn ℝ (Set.Ioo (1 / α) (1 / β)) (fun u => (-w₁) / (1 - β * u) ^ 2) := by
      refine ⟨convex_Ioo _ _, ?_⟩
      intro x hx y hy hxy a b ha hb hab
      have hx' : 0 < 1 - β * x := by
        have := (lt_div_iff₀ hβ).mp hx.2; linarith
      have hy' : 0 < 1 - β * y := by
        have := (lt_div_iff₀ hβ).mp hy.2; linarith
      have hne : 1 - β * x ≠ 1 - β * y := by
        intro heq; exact hxy (mul_left_cancel₀ hβ.ne' (by linarith))
      have hsc0 := inv_sq_strictConvexOn.2 hx' hy' hne ha hb hab
      have hlin : a • (1 - β * x) + b • (1 - β * y) = 1 - β * (a • x + b • y) := by
        simp only [smul_eq_mul]; nlinarith [hab]
      rw [hlin] at hsc0
      simp only [smul_eq_mul] at hsc0 ⊢
      have := mul_lt_mul_of_pos_left hsc0 (by linarith : 0 < -w₁)
      linarith [show (-w₁) * (1 / (1 - β * (a * x + b * y)) ^ 2) = (-w₁) / (1 - β * (a * x + b * y)) ^ 2 by ring,
        show (-w₁) * (a * (1 / (1 - β * x) ^ 2) + b * (1 / (1 - β * y) ^ 2)) =
          a * ((-w₁) / (1 - β * x) ^ 2) + b * ((-w₁) / (1 - β * y) ^ 2) by ring]
    exact h1.add h2
  have hbound := strictConvexOn_at_most_two_zeros hsc w₂
  let g : ℝ → ℝ := fun t => 1 / (c₂ - t)
  have hinj : Set.InjOn g {t : ℝ | (c₀ < t ∧ t < c₁) ∧
      -w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0} := by
    intro t₁ ht₁ t₂ ht₂ heq
    have : c₂ - t₁ = c₂ - t₂ := by
      have := congrArg Inv.inv heq; simpa [g] using this
    linarith
  have hmaps : Set.MapsTo g
      {t : ℝ | (c₀ < t ∧ t < c₁) ∧
        -w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}
      {u ∈ Set.Ioo (1 / α) (1 / β) | ψ u = w₂} := by
    intro t ⟨⟨ht0, ht1⟩, heq⟩
    have hne0 : t - c₀ ≠ 0 := by linarith
    have hne1 : t - c₁ ≠ 0 := by linarith
    have hne2 : c₂ - t ≠ 0 := by linarith
    refine ⟨⟨one_div_lt_one_div_of_lt (by linarith) (by linarith),
      one_div_lt_one_div_of_lt hβ (by linarith)⟩, ?_⟩
    have h1 : α * g t - 1 = (t - c₀) / (c₂ - t) := by
      simp only [g, α]; field_simp [hne2]; ring
    have h2 : 1 - β * g t = (c₁ - t) / (c₂ - t) := by
      simp only [g, β]; field_simp [hne2]; ring
    simp only [ψ, h1, h2]
    have hmul := congrArg (· * (c₂ - t) ^ 2) heq
    simp only [zero_mul] at hmul
    have hrewrite : (-w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2) * (c₂ - t) ^ 2 =
        w₂ - (w₀ / ((t - c₀) / (c₂ - t)) ^ 2 + (-w₁) / ((c₁ - t) / (c₂ - t)) ^ 2) := by
      have hsq1 : (t - c₁) ^ 2 = (c₁ - t) ^ 2 := by ring
      have hsq2 : (t - c₂) ^ 2 = (c₂ - t) ^ 2 := by ring
      rw [hsq1, hsq2]
      field_simp [hne0, (by linarith : c₁ - t ≠ 0), hne2]
      ring
    linarith
  calc
    _ = (g '' _).encard := (hinj.encard_image).symm
    _ ≤ {u ∈ Set.Ioo (1 / α) (1 / β) | ψ u = w₂}.encard :=
        Set.encard_le_encard hmaps.image_subset
    _ ≤ 2 := hbound

private lemma card_roots_mid2_le_two {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : 0 < w₀) (hw1 : w₁ < 0) (hw2 : 0 < w₂) :
    {t : ℝ | (c₁ < t ∧ t < c₂) ∧
      -w₀ / (t - c₀) ^ 2 - w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}.encard ≤ 2 := by
  -- Reflection t ↦ -t reduces mid2 to mid1 with (w₂, w₁, w₀) and (-c₂, -c₁, -c₀)
  have href := card_roots_mid1_le_two (w₀ := w₂) (w₁ := w₁) (w₂ := w₀)
    (c₀ := -c₂) (c₁ := -c₁) (c₂ := -c₀) (by linarith) (by linarith) hw2 hw1 hw0
  let g : ℝ → ℝ := fun t => -t
  have hinj : Set.InjOn g {t : ℝ | (c₁ < t ∧ t < c₂) ∧ -w₀ / (t - c₀) ^ 2 - w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0} := fun x _ y _ h => neg_inj.mp h
  have hmaps : Set.MapsTo g
      {t : ℝ | (c₁ < t ∧ t < c₂) ∧
        -w₀ / (t - c₀) ^ 2 - w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}
      {t : ℝ | (-c₂ < t ∧ t < -c₁) ∧
        -w₂ / (t - (-c₂)) ^ 2 + w₁ / (t - (-c₁)) ^ 2 + w₀ / (t - (-c₀)) ^ 2 = 0} := by
    intro t ⟨⟨h1, h2⟩, heq⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp only [g]
    have s0 : (-t - -c₀) ^ 2 = (t - c₀) ^ 2 := by ring
    have s1 : (-t - -c₁) ^ 2 = (t - c₁) ^ 2 := by ring
    have s2 : (-t - -c₂) ^ 2 = (t - c₂) ^ 2 := by ring
    rw [s0, s1, s2]
    have e0 : -w₀ / (t - c₀) ^ 2 = -(w₀ / (t - c₀) ^ 2) := by ring
    have e2 : -w₂ / (t - c₂) ^ 2 = -(w₂ / (t - c₂) ^ 2) := by ring
    linarith
  calc
    _ = (g '' _).encard := (hinj.encard_image).symm
    _ ≤ _ := Set.encard_le_encard hmaps.image_subset
    _ ≤ 2 := href

private lemma card_roots_pos_pos_neg {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : 0 < w₀) (hw1 : 0 < w₁) (hw2 : w₂ < 0) :
    {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
      force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}.encard ≤ 4 := by
  -- Split into I₀ ∪ I₃ (≤ 2 via convexity after reflecting? Wait: degree ≤ 4 poly has root in (c₁, c₂) -> ≤ 3!)
  -- Plus I₁ (≤ 1 via StrictMonoOn of (t - c₂)² F(t)) + I₂ (0 roots since all 3 terms < 0)!
  set S := {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
    force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}
  set S_out := {t ∈ S | t < c₀ ∨ c₂ < t}
  set S_mid1 := {t ∈ S | c₀ < t ∧ t < c₁}
  have hsub : S ⊆ S_out ∪ S_mid1 := by
    intro t ht
    rcases ht with ⟨h0, h1, h2, hfeq⟩
    have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
    rcases lt_or_gt_of_ne h0 with hlt0 | hgt0
    · exact Or.inl ⟨⟨h0, h1, h2, hfeq⟩, Or.inl hlt0⟩
    · rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
      · exact Or.inr ⟨⟨h0, h1, h2, hfeq⟩, hgt0, hlt1⟩
      · rcases lt_or_gt_of_ne h2 with hlt2 | hgt2
        · exfalso
          rw [if_neg (not_lt.mpr hgt0.le), if_neg (not_lt.mpr hgt1.le), if_pos hlt2] at hF
          have t0 : -w₀ / (t - c₀) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero (by linarith))
          have t1 : -w₁ / (t - c₁) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero (by linarith))
          have t2 : w₂ / (t - c₂) ^ 2 < 0 := div_neg_of_neg_of_pos hw2 (sq_pos_of_ne_zero (by linarith))
          linarith
        · exact Or.inl ⟨⟨h0, h1, h2, hfeq⟩, Or.inr hgt2⟩
  -- Bound S_mid1 ≤ 1 using strict monotonicity of g(t) = -w₀((c₂-t)/(t-c₀))² + w₁((c₂-t)/(c₁-t))²
  have hmid1 : S_mid1.encard ≤ 1 := by
    let g : ℝ → ℝ := fun t => -w₀ * ((c₂ - t) / (t - c₀)) ^ 2 + w₁ * ((c₂ - t) / (c₁ - t)) ^ 2
    have hmono : StrictMonoOn g (Set.Ioo c₀ c₁) := by
      intro x hx y hy hxy
      have h1 : (c₂ - y) / (y - c₀) < (c₂ - x) / (x - c₀) := by
        rw [div_lt_div_iff₀ (by linarith [hy.1]) (by linarith [hx.1])]
        nlinarith [hx.1, hy.1, hc01, hc12]
      have h1pos : 0 < (c₂ - y) / (y - c₀) := div_pos (by linarith [hy.2, hc12]) (by linarith [hy.1])
      have h1sq : ((c₂ - y) / (y - c₀)) ^ 2 < ((c₂ - x) / (x - c₀)) ^ 2 :=
        sq_lt_sq' (by linarith) h1
      have h2 : (c₂ - x) / (c₁ - x) < (c₂ - y) / (c₁ - y) := by
        rw [div_lt_div_iff₀ (by linarith [hx.2]) (by linarith [hy.2])]
        nlinarith [hx.2, hy.2, hc12]
      have h2pos : 0 < (c₂ - x) / (c₁ - x) := div_pos (by linarith [hx.2, hc12]) (by linarith [hx.2])
      have h2sq : ((c₂ - x) / (c₁ - x)) ^ 2 < ((c₂ - y) / (c₁ - y)) ^ 2 :=
        sq_lt_sq' (by linarith) h2
      dsimp only [g]
      nlinarith
    have hsub1 : S_mid1 ⊆ {t ∈ Set.Ioo c₀ c₁ | g t = -w₂} := by
      intro t ⟨⟨h0, h1, h2, hfeq⟩, ht0, ht1⟩
      refine ⟨⟨ht0, ht1⟩, ?_⟩
      have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
      rw [if_neg (not_lt.mpr ht0.le), if_pos ht1, if_pos (ht1.trans hc12)] at hF
      have hmul := congrArg (· * (c₂ - t) ^ 2) (hF.symm.trans hfeq)
      simp only [zero_mul] at hmul
      have hrew : (-w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2) * (c₂ - t) ^ 2 =
          g t + w₂ := by
        dsimp only [g]
        have s1 : (t - c₁) ^ 2 = (c₁ - t) ^ 2 := by ring
        have s2 : (t - c₂) ^ 2 = (c₂ - t) ^ 2 := by ring
        rw [s1, s2]
        field_simp [(by linarith : t - c₀ ≠ 0), (by linarith : c₁ - t ≠ 0), (by linarith : c₂ - t ≠ 0)]
      linarith
    exact (Set.encard_le_encard hsub1).trans (strictMonoOn_at_most_one_zero hmono (-w₂))
  -- Bound S_out ≤ 3 via polynomial P(X) = w₀(X-c₁)²(X-c₂)² + w₁(X-c₀)²(X-c₂)² + w₂(X-c₀)²(X-c₁)²
  have hout : S_out.encard ≤ 3 := by
    let P : Polynomial ℝ :=
      Polynomial.C w₀ * (Polynomial.X - Polynomial.C c₁) ^ 2 * (Polynomial.X - Polynomial.C c₂) ^ 2 +
      Polynomial.C w₁ * (Polynomial.X - Polynomial.C c₀) ^ 2 * (Polynomial.X - Polynomial.C c₂) ^ 2 +
      Polynomial.C w₂ * (Polynomial.X - Polynomial.C c₀) ^ 2 * (Polynomial.X - Polynomial.C c₁) ^ 2
    have hPeval (t : ℝ) : P.eval t =
        w₀ * (t - c₁) ^ 2 * (t - c₂) ^ 2 + w₁ * (t - c₀) ^ 2 * (t - c₂) ^ 2 +
        w₂ * (t - c₀) ^ 2 * (t - c₁) ^ 2 := by
      simp [P]
    have hP_c1 : 0 < P.eval c₁ := by
      rw [hPeval]; simp
      have h1 : 0 < (c₁ - c₀) ^ 2 := sq_pos_of_ne_zero (by linarith)
      have h2 : 0 < (c₁ - c₂) ^ 2 := sq_pos_of_ne_zero (by linarith)
      positivity
    have hP_c2 : P.eval c₂ < 0 := by
      rw [hPeval]; simp
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hw2 (sq_pos_of_ne_zero (by linarith)))
        (sq_pos_of_ne_zero (by linarith))
    have hPne : P ≠ 0 := by
      intro h0; rw [h0, Polynomial.eval_zero] at hP_c1; linarith
    have hdeg : P.natDegree ≤ 4 := by
      have d0 : (Polynomial.C w₀ * (Polynomial.X - Polynomial.C c₁) ^ 2 * (Polynomial.X - Polynomial.C c₂) ^ 2).natDegree ≤ 4 := by
        compute_degree!
      have d1 : (Polynomial.C w₁ * (Polynomial.X - Polynomial.C c₀) ^ 2 * (Polynomial.X - Polynomial.C c₂) ^ 2).natDegree ≤ 4 := by
        compute_degree!
      have d2 : (Polynomial.C w₂ * (Polynomial.X - Polynomial.C c₀) ^ 2 * (Polynomial.X - Polynomial.C c₁) ^ 2).natDegree ≤ 4 := by
        compute_degree!
      exact (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le d0 d1)) d2)
    -- By IVT, P has a root r ∈ (c₁, c₂) which is NOT in S_out
    have hcont : Continuous (fun t => P.eval t) := P.continuous
    obtain ⟨r, hr_mem, hr_zero⟩ := intermediate_value_Ioo' hc12.le hcont.continuousOn ⟨hP_c2, hP_c1⟩
    have hr_not_out : r ∉ S_out := by
      rintro ⟨_, hlt | hgt⟩ <;> linarith [hr_mem.1, hr_mem.2]
    have hsub_roots : insert r S_out ⊆ (P.roots.toFinset : Set ℝ) := by
      intro t ht
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hPne]
      rcases Set.mem_insert_iff.mp ht with rfl | ⟨⟨h0, h1, h2, hfeq⟩, hout_t⟩
      · exact hr_zero
      · have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
        rw [Polynomial.IsRoot, hPeval]
        rcases hout_t with hlt0 | hgt2
        · rw [if_pos hlt0, if_pos (hlt0.trans hc01), if_pos (hlt0.trans (hc01.trans hc12))] at hF
          have hmul := congrArg (· * ((t - c₀) ^ 2 * (t - c₁) ^ 2 * (t - c₂) ^ 2)) (hF.symm.trans hfeq)
          simp only [zero_mul] at hmul
          have hrew : (w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2) *
              ((t - c₀) ^ 2 * (t - c₁) ^ 2 * (t - c₂) ^ 2) =
              w₀ * (t - c₁) ^ 2 * (t - c₂) ^ 2 + w₁ * (t - c₀) ^ 2 * (t - c₂) ^ 2 +
              w₂ * (t - c₀) ^ 2 * (t - c₁) ^ 2 := by
            field_simp [sub_ne_zero.mpr h0, sub_ne_zero.mpr h1, sub_ne_zero.mpr h2]
          linarith
        · rw [if_neg (not_lt.mpr ((hc01.trans hc12).trans hgt2).le),
            if_neg (not_lt.mpr (hc12.trans hgt2).le),
            if_neg (not_lt.mpr hgt2.le)] at hF
          have hmul := congrArg (· * ((t - c₀) ^ 2 * (t - c₁) ^ 2 * (t - c₂) ^ 2)) (hF.symm.trans hfeq)
          simp only [zero_mul] at hmul
          have hrew : (-w₀ / (t - c₀) ^ 2 + -w₁ / (t - c₁) ^ 2 + -w₂ / (t - c₂) ^ 2) *
              ((t - c₀) ^ 2 * (t - c₁) ^ 2 * (t - c₂) ^ 2) =
              -(w₀ * (t - c₁) ^ 2 * (t - c₂) ^ 2 + w₁ * (t - c₀) ^ 2 * (t - c₂) ^ 2 +
              w₂ * (t - c₀) ^ 2 * (t - c₁) ^ 2) := by
            field_simp [sub_ne_zero.mpr h0, sub_ne_zero.mpr h1, sub_ne_zero.mpr h2]
            ring
          linarith
    have hcard_ins : (insert r S_out).encard ≤ 4 := by
      calc
        (insert r S_out).encard ≤ (P.roots.toFinset : Set ℝ).encard := Set.encard_le_encard hsub_roots
        _ = (P.roots.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
        _ ≤ (P.roots.card : ℕ∞) := by exact_mod_cast Multiset.toFinset_card_le _
        _ ≤ (P.natDegree : ℕ∞) := by exact_mod_cast Polynomial.card_roots' P
        _ ≤ 4 := by exact_mod_cast hdeg
    rw [Set.encard_insert_of_notMem hr_not_out] at hcard_ins
    have h31 : S_out.encard + 1 ≤ (3 : ℕ∞) + 1 := by
      simpa only [show (3 : ℕ∞) + 1 = 4 by norm_num] using hcard_ins
    exact (WithTop.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp h31
  calc
    S.encard ≤ (S_out ∪ S_mid1).encard := Set.encard_le_encard hsub
    _ ≤ S_out.encard + S_mid1.encard := Set.encard_union_le _ _
    _ ≤ 3 + 1 := add_le_add hout hmid1
    _ = 4 := by norm_num

private lemma card_roots_pos_neg_pos {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : 0 < w₀) (hw1 : w₁ < 0) (hw2 : 0 < w₂) :
    {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
      force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}.encard ≤ 4 := by
  set p₁ : ℝ := -w₁
  have hp1 : 0 < p₁ := by linarith
  set S := {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
    force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}
  set S_out := {t : ℝ | (t < c₀ ∨ c₂ < t) ∧
    w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}
  set S_mid1 := {t : ℝ | (c₀ < t ∧ t < c₁) ∧
    -w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}
  set S_mid2 := {t : ℝ | (c₁ < t ∧ t < c₂) ∧
    -w₀ / (t - c₀) ^ 2 - w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2 = 0}
  have hS_split : ∀ t ∈ S, t ∈ S_out ∨ t ∈ S_mid1 ∨ t ∈ S_mid2 := by
    intro t ⟨h0, h1, h2, hfeq⟩
    have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
    rcases lt_or_gt_of_ne h0 with hlt0 | hgt0
    · rw [if_pos hlt0, if_pos (hlt0.trans hc01), if_pos (hlt0.trans (hc01.trans hc12))] at hF
      exact Or.inl ⟨Or.inl hlt0, hF.symm.trans hfeq⟩
    · rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
      · rw [if_neg (not_lt.mpr hgt0.le), if_pos hlt1, if_pos (hlt1.trans hc12)] at hF
        exact Or.inr (Or.inl ⟨⟨hgt0, hlt1⟩, hF.symm.trans hfeq⟩)
      · rcases lt_or_gt_of_ne h2 with hlt2 | hgt2
        · rw [if_neg (not_lt.mpr hgt0.le), if_neg (not_lt.mpr hgt1.le), if_pos hlt2] at hF
          refine Or.inr (Or.inr ⟨⟨hgt1, hlt2⟩, ?_⟩)
          have e1 : -w₁ / (t - c₁) ^ 2 = -(w₁ / (t - c₁) ^ 2) := by ring
          linarith
        · rw [if_neg (not_lt.mpr hgt0.le), if_neg (not_lt.mpr hgt1.le),
            if_neg (not_lt.mpr hgt2.le)] at hF
          refine Or.inl ⟨Or.inr hgt2, ?_⟩
          have e0 : -w₀ / (t - c₀) ^ 2 = -(w₀ / (t - c₀) ^ 2) := by ring
          have e1 : -w₁ / (t - c₁) ^ 2 = -(w₁ / (t - c₁) ^ 2) := by ring
          have e2 : -w₂ / (t - c₂) ^ 2 = -(w₂ / (t - c₂) ^ 2) := by ring
          linarith
  have hno_I0 (hq0 : p₁ ≤ w₀) : ∀ t ∈ S_out, ¬ t < c₀ := by
    intro t ⟨_, heq⟩ hlt0
    have hsq : (t - c₀) ^ 2 < (t - c₁) ^ 2 := by
      have : 0 < c₀ - t := by linarith
      have : c₀ - t < c₁ - t := by linarith
      nlinarith
    have hdiv : w₀ / (t - c₁) ^ 2 < w₀ / (t - c₀) ^ 2 :=
      div_lt_div_of_pos_left hw0 (sq_pos_of_ne_zero (by linarith)) hsq
    have hdiv2 : p₁ / (t - c₁) ^ 2 ≤ w₀ / (t - c₁) ^ 2 :=
      div_le_div_of_nonneg_right hq0 (sq_nonneg _)
    have hdiv3 : 0 < w₂ / (t - c₂) ^ 2 := div_pos hw2 (sq_pos_of_ne_zero (by linarith))
    have : w₁ / (t - c₁) ^ 2 = -(p₁ / (t - c₁) ^ 2) := by simp [p₁]; ring
    linarith
  have hno_I3 (hq2 : p₁ ≤ w₂) : ∀ t ∈ S_out, ¬ c₂ < t := by
    intro t ⟨_, heq⟩ hgt2
    have hsq : (t - c₂) ^ 2 < (t - c₁) ^ 2 := by
      have : 0 < t - c₂ := by linarith
      have : t - c₂ < t - c₁ := by linarith
      nlinarith
    have hdiv : w₂ / (t - c₁) ^ 2 < w₂ / (t - c₂) ^ 2 :=
      div_lt_div_of_pos_left hw2 (sq_pos_of_ne_zero (by linarith)) hsq
    have hdiv2 : p₁ / (t - c₁) ^ 2 ≤ w₂ / (t - c₁) ^ 2 :=
      div_le_div_of_nonneg_right hq2 (sq_nonneg _)
    have hdiv3 : 0 < w₀ / (t - c₀) ^ 2 := div_pos hw0 (sq_pos_of_ne_zero (by linarith))
    have : w₁ / (t - c₁) ^ 2 = -(p₁ / (t - c₁) ^ 2) := by simp [p₁]; ring
    linarith
  have hno_mid1 (hq2 : w₂ ≤ p₁) : S_mid1 = ∅ := by
    ext t; simp only [S_mid1, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨ht0, ht1⟩, heq⟩
    have hsq : (t - c₁) ^ 2 < (t - c₂) ^ 2 := by
      have : 0 < c₁ - t := by linarith
      have : c₁ - t < c₂ - t := by linarith
      nlinarith
    have hdiv : w₂ / (t - c₂) ^ 2 < w₂ / (t - c₁) ^ 2 :=
      div_lt_div_of_pos_left hw2 (sq_pos_of_ne_zero (by linarith)) hsq
    have hdiv2 : w₂ / (t - c₁) ^ 2 ≤ p₁ / (t - c₁) ^ 2 :=
      div_le_div_of_nonneg_right hq2 (sq_nonneg _)
    have hdiv0 : 0 < w₀ / (t - c₀) ^ 2 := div_pos hw0 (sq_pos_of_ne_zero (by linarith))
    have : w₁ / (t - c₁) ^ 2 = -(p₁ / (t - c₁) ^ 2) := by simp [p₁]; ring
    have : -w₀ / (t - c₀) ^ 2 = -(w₀ / (t - c₀) ^ 2) := by ring
    linarith
  have hno_mid2 (hq0 : w₀ ≤ p₁) : S_mid2 = ∅ := by
    ext t; simp only [S_mid2, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨ht1, ht2⟩, heq⟩
    have hsq : (t - c₁) ^ 2 < (t - c₀) ^ 2 := by
      have : 0 < t - c₁ := by linarith
      have : t - c₁ < t - c₀ := by linarith
      nlinarith
    have hdiv : w₀ / (t - c₀) ^ 2 < w₀ / (t - c₁) ^ 2 :=
      div_lt_div_of_pos_left hw0 (sq_pos_of_ne_zero (by linarith)) hsq
    have hdiv2 : w₀ / (t - c₁) ^ 2 ≤ p₁ / (t - c₁) ^ 2 :=
      div_le_div_of_nonneg_right hq0 (sq_nonneg _)
    have hdiv2' : 0 < w₂ / (t - c₂) ^ 2 := div_pos hw2 (sq_pos_of_ne_zero (by linarith))
    have : w₁ / (t - c₁) ^ 2 = -(p₁ / (t - c₁) ^ 2) := by simp [p₁]; ring
    have : -w₀ / (t - c₀) ^ 2 = -(w₀ / (t - c₀) ^ 2) := by ring
    linarith
  have h_out := card_roots_outer_le_two hc01 hc12 hw0 hw1 hw2
  have h_m1 := card_roots_mid1_le_two hc01 hc12 hw0 hw1 hw2
  have h_m2 := card_roots_mid2_le_two hc01 hc12 hw0 hw1 hw2
  by_cases hq0 : p₁ ≤ w₀ <;> by_cases hq2 : p₁ ≤ w₂
  · -- Case A: S_out = ∅
    have hS_out_empty : S_out = ∅ := by
      ext t; simp only [Set.mem_empty_iff_false, iff_false]
      intro ht
      rcases ht.1 with hlt0 | hgt2
      · exact hno_I0 hq0 t ht hlt0
      · exact hno_I3 hq2 t ht hgt2
    have hsub : S ⊆ S_mid1 ∪ S_mid2 := by
      intro t ht; rcases hS_split t ht with h | h | h
      · rw [hS_out_empty] at h; exact h.elim
      · exact Or.inl h
      · exact Or.inr h
    calc S.encard ≤ (S_mid1 ∪ S_mid2).encard := Set.encard_le_encard hsub
      _ ≤ S_mid1.encard + S_mid2.encard := Set.encard_union_le _ _
      _ ≤ 2 + 2 := add_le_add h_m1 h_m2
      _ = 4 := by norm_num
  · -- Case C: S_mid1 = ∅
    have hm1e : S_mid1 = ∅ := hno_mid1 (not_le.mp hq2).le
    have hsub : S ⊆ S_out ∪ S_mid2 := by
      intro t ht; rcases hS_split t ht with h | h | h
      · exact Or.inl h
      · rw [hm1e] at h; exact h.elim
      · exact Or.inr h
    calc S.encard ≤ (S_out ∪ S_mid2).encard := Set.encard_le_encard hsub
      _ ≤ S_out.encard + S_mid2.encard := Set.encard_union_le _ _
      _ ≤ 2 + 2 := add_le_add h_out h_m2
      _ = 4 := by norm_num
  · -- Case B: S_mid2 = ∅
    have hm2e : S_mid2 = ∅ := hno_mid2 (not_le.mp hq0).le
    have hsub : S ⊆ S_out ∪ S_mid1 := by
      intro t ht; rcases hS_split t ht with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rw [hm2e] at h; exact h.elim
    calc S.encard ≤ (S_out ∪ S_mid1).encard := Set.encard_le_encard hsub
      _ ≤ S_out.encard + S_mid1.encard := Set.encard_union_le _ _
      _ ≤ 2 + 2 := add_le_add h_out h_m1
      _ = 4 := by norm_num
  · -- Case D: S_mid1 = ∅ and S_mid2 = ∅
    have hm1e : S_mid1 = ∅ := hno_mid1 (not_le.mp hq2).le
    have hm2e : S_mid2 = ∅ := hno_mid2 (not_le.mp hq0).le
    have hsub : S ⊆ S_out := by
      intro t ht; rcases hS_split t ht with h | h | h
      · exact h
      · rw [hm1e] at h; exact h.elim
      · rw [hm2e] at h; exact h.elim
    exact (Set.encard_le_encard hsub).trans (h_out.trans (by norm_num))

private lemma card_roots_pos_pos_pos {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : 0 < w₀) (hw1 : 0 < w₁) (hw2 : 0 < w₂) :
    {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
      force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}.encard ≤ 4 := by
  set S := {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
    force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}
  set S1 := {t ∈ S | c₀ < t ∧ t < c₁}
  set S2 := {t ∈ S | c₁ < t ∧ t < c₂}
  have hsub : S ⊆ S1 ∪ S2 := by
    intro t ht
    rcases ht with ⟨h0, h1, h2, hfeq⟩
    have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
    rcases lt_or_gt_of_ne h0 with hlt0 | hgt0
    · exfalso
      rw [if_pos hlt0, if_pos (hlt0.trans hc01), if_pos (hlt0.trans (hc01.trans hc12))] at hF
      have t0 : 0 < w₀ / (t - c₀) ^ 2 := div_pos hw0 (sq_pos_of_ne_zero (by linarith))
      have t1 : 0 < w₁ / (t - c₁) ^ 2 := div_pos hw1 (sq_pos_of_ne_zero (by linarith))
      have t2 : 0 < w₂ / (t - c₂) ^ 2 := div_pos hw2 (sq_pos_of_ne_zero (by linarith))
      linarith
    · rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
      · exact Or.inl ⟨⟨h0, h1, h2, hfeq⟩, hgt0, hlt1⟩
      · rcases lt_or_gt_of_ne h2 with hlt2 | hgt2
        · exact Or.inr ⟨⟨h0, h1, h2, hfeq⟩, hgt1, hlt2⟩
        · exfalso
          rw [if_neg (not_lt.mpr hgt0.le), if_neg (not_lt.mpr hgt1.le),
            if_neg (not_lt.mpr hgt2.le)] at hF
          have t0 : -w₀ / (t - c₀) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero (by linarith))
          have t1 : -w₁ / (t - c₁) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero (by linarith))
          have t2 : -w₂ / (t - c₂) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero (by linarith))
          linarith
  have hm1 : S1.encard ≤ 1 := by
    let g : ℝ → ℝ := fun t => -w₀ / (t - c₀) ^ 2 + w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2
    have hmono : StrictMonoOn g (Set.Ioo c₀ c₁) := by
      intro x hx y hy hxy
      have h0 : w₀ / (y - c₀) ^ 2 < w₀ / (x - c₀) ^ 2 :=
        div_lt_div_of_pos_left hw0 (sq_pos_of_ne_zero (by linarith [hx.1]))
          (sq_lt_sq' (by linarith [hx.1, hy.1]) (by linarith))
      have hsq1 : (y - c₁) ^ 2 < (x - c₁) ^ 2 := by
        have hdiff : (x - c₁) ^ 2 - (y - c₁) ^ 2 = (y - x) * ((c₁ - x) + (c₁ - y)) := by ring
        have hpos : 0 < (y - x) * ((c₁ - x) + (c₁ - y)) := mul_pos (by linarith) (by linarith [hx.2, hy.2])
        linarith
      have h1 : w₁ / (x - c₁) ^ 2 < w₁ / (y - c₁) ^ 2 :=
        div_lt_div_of_pos_left hw1 (sq_pos_of_ne_zero (by linarith [hy.2])) hsq1
      have hsq2 : (y - c₂) ^ 2 < (x - c₂) ^ 2 := by
        have hdiff : (x - c₂) ^ 2 - (y - c₂) ^ 2 = (y - x) * ((c₂ - x) + (c₂ - y)) := by ring
        have hpos : 0 < (y - x) * ((c₂ - x) + (c₂ - y)) := mul_pos (by linarith) (by linarith [hx.2, hy.2, hc12])
        linarith
      have h2 : w₂ / (x - c₂) ^ 2 < w₂ / (y - c₂) ^ 2 :=
        div_lt_div_of_pos_left hw2 (sq_pos_of_ne_zero (by linarith [hy.2, hc12])) hsq2
      dsimp only [g]
      have : -w₀ / (x - c₀) ^ 2 = -(w₀ / (x - c₀) ^ 2) := by ring
      have : -w₀ / (y - c₀) ^ 2 = -(w₀ / (y - c₀) ^ 2) := by ring
      linarith
    have hsub1 : S1 ⊆ {t ∈ Set.Ioo c₀ c₁ | g t = 0} := by
      intro t ⟨⟨h0, h1, h2, hfeq⟩, ht0, ht1⟩
      refine ⟨⟨ht0, ht1⟩, ?_⟩
      have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
      rw [if_neg (not_lt.mpr ht0.le), if_pos ht1, if_pos (ht1.trans hc12)] at hF
      exact hF.symm.trans hfeq
    exact (Set.encard_le_encard hsub1).trans (strictMonoOn_at_most_one_zero hmono 0)
  have hm2 : S2.encard ≤ 1 := by
    let g : ℝ → ℝ := fun t => -w₀ / (t - c₀) ^ 2 + -w₁ / (t - c₁) ^ 2 + w₂ / (t - c₂) ^ 2
    have hmono : StrictMonoOn g (Set.Ioo c₁ c₂) := by
      intro x hx y hy hxy
      have h0 : w₀ / (y - c₀) ^ 2 < w₀ / (x - c₀) ^ 2 :=
        div_lt_div_of_pos_left hw0 (sq_pos_of_ne_zero (by linarith [hx.1, hc01]))
          (sq_lt_sq' (by linarith [hx.1, hy.1, hc01]) (by linarith))
      have h1 : w₁ / (y - c₁) ^ 2 < w₁ / (x - c₁) ^ 2 :=
        div_lt_div_of_pos_left hw1 (sq_pos_of_ne_zero (by linarith [hx.1]))
          (sq_lt_sq' (by linarith [hx.1, hy.1]) (by linarith))
      have hsq2 : (y - c₂) ^ 2 < (x - c₂) ^ 2 := by
        have hdiff : (x - c₂) ^ 2 - (y - c₂) ^ 2 = (y - x) * ((c₂ - x) + (c₂ - y)) := by ring
        have hpos : 0 < (y - x) * ((c₂ - x) + (c₂ - y)) := mul_pos (by linarith) (by linarith [hx.2, hy.2])
        linarith
      have h2 : w₂ / (x - c₂) ^ 2 < w₂ / (y - c₂) ^ 2 :=
        div_lt_div_of_pos_left hw2 (sq_pos_of_ne_zero (by linarith [hy.2])) hsq2
      dsimp only [g]
      have : -w₀ / (x - c₀) ^ 2 = -(w₀ / (x - c₀) ^ 2) := by ring
      have : -w₀ / (y - c₀) ^ 2 = -(w₀ / (y - c₀) ^ 2) := by ring
      have : -w₁ / (x - c₁) ^ 2 = -(w₁ / (x - c₁) ^ 2) := by ring
      have : -w₁ / (y - c₁) ^ 2 = -(w₁ / (y - c₁) ^ 2) := by ring
      linarith
    have hsub2 : S2 ⊆ {t ∈ Set.Ioo c₁ c₂ | g t = 0} := by
      intro t ⟨⟨h0, h1, h2, hfeq⟩, ht1, ht2⟩
      refine ⟨⟨ht1, ht2⟩, ?_⟩
      have hF := force1D_eq_on_interval w₀ w₁ w₂ c₀ c₁ c₂ t h0 h1 h2
      rw [if_neg (not_lt.mpr (hc01.trans ht1).le), if_neg (not_lt.mpr ht1.le), if_pos ht2] at hF
      exact hF.symm.trans hfeq
    exact (Set.encard_le_encard hsub2).trans (strictMonoOn_at_most_one_zero hmono 0)
  calc S.encard ≤ (S1 ∪ S2).encard := Set.encard_le_encard hsub
    _ ≤ S1.encard + S2.encard := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add hm1 hm2
    _ ≤ 4 := by norm_num

private lemma card_roots_sorted {w₀ w₁ w₂ c₀ c₁ c₂ : ℝ}
    (hc01 : c₀ < c₁) (hc12 : c₁ < c₂) (hw0 : w₀ ≠ 0) (hw1 : w₁ ≠ 0) (hw2 : w₂ ≠ 0) :
    {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
      force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0}.encard ≤ 4 := by
  have hneg_eq (a₀ a₁ a₂ : ℝ) :
      {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧ force1D ![-a₀, -a₁, -a₂] ![c₀, c₁, c₂] t = 0} =
      {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧ force1D ![a₀, a₁, a₂] ![c₀, c₁, c₂] t = 0} := by
    ext t; simp only [Set.mem_setOf_eq, force1D, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    constructor <;> rintro ⟨h0, h1, h2, heq⟩ <;> refine ⟨h0, h1, h2, ?_⟩
    · have : -a₀ * (t - c₀) / |t - c₀| ^ 3 + -a₁ * (t - c₁) / |t - c₁| ^ 3 +
          -a₂ * (t - c₂) / |t - c₂| ^ 3 =
          -(-(-a₀) * (t - c₀) / |t - c₀| ^ 3 + -(-a₁) * (t - c₁) / |t - c₁| ^ 3 +
          -(-a₂) * (t - c₂) / |t - c₂| ^ 3) := by ring
      linarith
    · have : -(-a₀) * (t - c₀) / |t - c₀| ^ 3 + -(-a₁) * (t - c₁) / |t - c₁| ^ 3 +
          -(-a₂) * (t - c₂) / |t - c₂| ^ 3 =
          -(-a₀ * (t - c₀) / |t - c₀| ^ 3 + -a₁ * (t - c₁) / |t - c₁| ^ 3 +
          -a₂ * (t - c₂) / |t - c₂| ^ 3) := by ring
      linarith
  have href_eq (a₀ a₁ a₂ : ℝ) :
      {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧ force1D ![a₀, a₁, a₂] ![c₀, c₁, c₂] t = 0}.encard =
      {t : ℝ | t ≠ -c₂ ∧ t ≠ -c₁ ∧ t ≠ -c₀ ∧ force1D ![a₂, a₁, a₀] ![-c₂, -c₁, -c₀] t = 0}.encard := by
    let g : ℝ → ℝ := fun t => -t
    have hinj : Function.Injective g := neg_injective
    have himg : g '' {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧ force1D ![a₀, a₁, a₂] ![c₀, c₁, c₂] t = 0} =
        {t : ℝ | t ≠ -c₂ ∧ t ≠ -c₁ ∧ t ≠ -c₀ ∧ force1D ![a₂, a₁, a₀] ![-c₂, -c₁, -c₀] t = 0} := by
      ext u; constructor
      · rintro ⟨t, ⟨h0, h1, h2, heq⟩, rfl⟩
        refine ⟨fun h => h2 (neg_inj.mp h), fun h => h1 (neg_inj.mp h), fun h => h0 (neg_inj.mp h), ?_⟩
        simp only [g, force1D, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at heq ⊢
        have a0 : |-t - -c₀| = |t - c₀| := by rw [show -t - -c₀ = -(t - c₀) by ring, abs_neg]
        have a1 : |-t - -c₁| = |t - c₁| := by rw [show -t - -c₁ = -(t - c₁) by ring, abs_neg]
        have a2 : |-t - -c₂| = |t - c₂| := by rw [show -t - -c₂ = -(t - c₂) by ring, abs_neg]
        rw [a0, a1, a2]
        have : -a₂ * (-t - -c₂) / |t - c₂| ^ 3 + -a₁ * (-t - -c₁) / |t - c₁| ^ 3 +
            -a₀ * (-t - -c₀) / |t - c₀| ^ 3 =
            -(-a₀ * (t - c₀) / |t - c₀| ^ 3 + -a₁ * (t - c₁) / |t - c₁| ^ 3 +
            -a₂ * (t - c₂) / |t - c₂| ^ 3) := by ring
        linarith
      · rintro ⟨h2, h1, h0, heq⟩
        refine ⟨-u, ⟨fun h => h0 (by linarith), fun h => h1 (by linarith), fun h => h2 (by linarith), ?_⟩, neg_neg u⟩
        simp only [force1D, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at heq ⊢
        have a0 : |-u - c₀| = |u - -c₀| := by rw [show -u - c₀ = -(u - -c₀) by ring, abs_neg]
        have a1 : |-u - c₁| = |u - -c₁| := by rw [show -u - c₁ = -(u - -c₁) by ring, abs_neg]
        have a2 : |-u - c₂| = |u - -c₂| := by rw [show -u - c₂ = -(u - -c₂) by ring, abs_neg]
        rw [a0, a1, a2]
        have : -a₀ * (-u - c₀) / |u - -c₀| ^ 3 + -a₁ * (-u - c₁) / |u - -c₁| ^ 3 +
            -a₂ * (-u - c₂) / |u - -c₂| ^ 3 =
            -(-a₂ * (u - -c₂) / |u - -c₂| ^ 3 + -a₁ * (u - -c₁) / |u - -c₁| ^ 3 +
            -a₀ * (u - -c₀) / |u - -c₀| ^ 3) := by ring
        linarith
    rw [← himg, hinj.injOn.encard_image]
  rcases lt_or_gt_of_ne hw0 with h0n | h0p <;>
  rcases lt_or_gt_of_ne hw1 with h1n | h1p <;>
  rcases lt_or_gt_of_ne hw2 with h2n | h2p
  · rw [← hneg_eq w₀ w₁ w₂]
    exact card_roots_pos_pos_pos hc01 hc12 (by linarith) (by linarith) (by linarith)
  · rw [← hneg_eq w₀ w₁ w₂]
    exact card_roots_pos_pos_neg hc01 hc12 (by linarith) (by linarith) (by linarith)
  · rw [← hneg_eq w₀ w₁ w₂]
    exact card_roots_pos_neg_pos hc01 hc12 (by linarith) (by linarith) (by linarith)
  · rw [href_eq]
    exact card_roots_pos_pos_neg (by linarith) (by linarith) h2p h1p h0n
  · rw [← hneg_eq w₀ w₁ w₂, href_eq]
    exact card_roots_pos_pos_neg (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · exact card_roots_pos_neg_pos hc01 hc12 h0p h1n h2p
  · exact card_roots_pos_pos_neg hc01 hc12 h0p h1p h2n
  · exact card_roots_pos_pos_pos hc01 hc12 h0p h1p h2p

/- ### Part 3: Off-axis equilibria have degenerate Hessian -/

private lemma coulomb_hasGradient (q : ℝ) {a x : E3} (hne : x ≠ a) :
    HasGradientAt (fun y : E3 => q / dist y a) ((-q / ‖x - a‖ ^ 3) • (x - a)) x := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hs : HasFDerivAt (fun y : E3 => ‖y - a‖ ^ 2) (2 • innerSL ℝ (x - a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : E3 => ‖y - a‖) (‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1; field_simp [hn]; norm_num
  have hderiv := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hderiv using 1
  ext v
  simp [toDual_apply_apply, div_eq_mul_inv, smul_smul]
  field_simp [hn]; simp

private lemma potential_hasGradient (q : Fin 3 → ℝ) (a : Fin 3 → E3) (x : E3)
    (hx : x ∉ Set.range a) :
    HasGradientAt (potential q a) (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  unfold potential
  rw [map_sum]
  exact HasFDerivAt.fun_sum fun i _ =>
    (coulomb_hasGradient (q i) (fun h => hx ⟨i, h.symm⟩)).hasFDerivAt

private lemma force_term_hasFDerivAt (q : ℝ) {a x : E3} (hne : x ≠ a) :
    ∃ L : E3 →L[ℝ] E3,
      HasFDerivAt (fun y : E3 => (-q / ‖y - a‖ ^ 3) • (y - a)) L x ∧
      ∀ v : E3, ⟪x - a, v⟫ = 0 → L v = (-q / ‖x - a‖ ^ 3) • v := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hs : HasFDerivAt (fun y : E3 => ‖y - a‖ ^ 2) (2 • innerSL ℝ (x - a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : E3 => ‖y - a‖) (‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1; field_simp [hn]; norm_num
  have hpow := hd.pow 3
  have hinv0 := ((hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt x hpow).const_mul (-q)
  have hinv : HasFDerivAt (fun y : E3 => -q / ‖y - a‖ ^ 3)
      ((-q) • -((‖x - a‖ ^ 3) ^ 2)⁻¹ • ((3 : ℕ) • ‖x - a‖ ^ (3 - 1)) • ‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
    convert! hinv0 using 1
  have hvec : HasFDerivAt (fun y : E3 => y - a) (ContinuousLinearMap.id ℝ E3) x :=
    (hasFDerivAt_id x).sub_const a
  have hprod := hinv.smul hvec
  refine ⟨_, hprod, ?_⟩
  intro v hv
  rw [inner_sub_left] at hv
  simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hv]

private lemma exists_orth_to_two (u r : E3) : ∃ v : E3, v ≠ 0 ∧ ⟪u, v⟫ = 0 ∧ ⟪r, v⟫ = 0 := by
  let S : Submodule ℝ E3 := Submodule.span ℝ {u, r}
  have hdim : Module.finrank ℝ S ≤ 2 := by
    have h1 := finrank_span_le_card (R := ℝ) ({u, r} : Set E3)
    have h2 : ({u, r} : Set E3).toFinset.card ≤ 2 := by
      have heq : ({u, r} : Set E3).toFinset = ({u, r} : Finset E3) := by
        ext z; simp
      rw [heq]
      exact Finset.card_le_two
    exact h1.trans h2
  have hE3 : Module.finrank ℝ E3 = 3 := by simp [E3]
  have hne_top : S ≠ ⊤ := by
    intro htop
    have : Module.finrank ℝ S = 3 := by rw [htop, finrank_top, hE3]
    omega
  have horth_ne : Sᗮ ≠ ⊥ := by
    intro hbot
    exact hne_top (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth_ne
  refine ⟨v, hv0, ?_, ?_⟩
  · exact (Submodule.mem_orthogonal S v).mp hvS u (Submodule.subset_span (by simp))
  · exact (Submodule.mem_orthogonal S v).mp hvS r (Submodule.subset_span (by simp))

private lemma equilibrium_on_line {q : Fin 3 → ℝ} {a : Fin 3 → E3} {p₀ u : E3} {s : Fin 3 → ℝ}
    (ha_line : ∀ i, a i = p₀ + s i • u) (hu : ‖u‖ = 1)
    {x : E3} (hx : x ∈ equilibria q a) (hnd : HasNondegenerateHessianAt (potential q a) x) :
    ∃ t : ℝ, x = p₀ + t • u := by
  set y : E3 := x - p₀
  set t : ℝ := ⟪y, u⟫
  set r : E3 := y - t • u
  by_cases hr0 : r = 0
  · refine ⟨t, ?_⟩
    have : y = t • u := sub_eq_zero.mp hr0
    simp only [y] at this
    exact eq_add_of_sub_eq' this
  · exfalso
    have hru : ⟪r, u⟫ = 0 := by
      simp only [r, t, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hu, one_pow,
        mul_one, conj_trivial, sub_self]
    have hforce : ∑ i : Fin 3, (-q i / ‖x - a i‖ ^ 3) • (x - a i) = 0 :=
      (potential_hasGradient q a x hx.1).gradient.symm.trans hx.2
    have hxai (i : Fin 3) : x - a i = r + (t - s i) • u := by
      rw [ha_line i]
      simp only [r, y, sub_smul]
      abel
    have hsum_zero : ∑ i : Fin 3, (-q i / ‖x - a i‖ ^ 3) = 0 := by
      have hinner : ⟪∑ i : Fin 3, (-q i / ‖x - a i‖ ^ 3) • (x - a i), r⟫ = 0 := by
        rw [hforce, inner_zero_left]
      rw [sum_inner] at hinner
      have hterm (i : Fin 3) :
          ⟪(-q i / ‖x - a i‖ ^ 3) • (x - a i), r⟫ = (-q i / ‖x - a i‖ ^ 3) * ‖r‖ ^ 2 := by
        rw [inner_smul_left, conj_trivial, hxai i, inner_add_left, inner_smul_left, conj_trivial,
          real_inner_comm r u, hru, mul_zero, add_zero, real_inner_self_eq_norm_sq]
      simp_rw [hterm, ← Finset.sum_mul] at hinner
      have hr_sq : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr0)
      exact (mul_eq_zero.mp hinner).resolve_right hr_sq
    obtain ⟨v, hv0, huv, hrv⟩ := exists_orth_to_two u r
    have hxv (i : Fin 3) : ⟪x - a i, v⟫ = 0 := by
      rw [hxai i, inner_add_left, inner_smul_left, conj_trivial, hrv, huv, mul_zero, add_zero]
    -- Compute derivative of gradient G at x along v: D G(x) v = (∑ (-q_i/‖x-a_i‖^3)) • v = 0
    have hL : ∀ i : Fin 3, ∃ L : E3 →L[ℝ] E3,
        HasFDerivAt (fun z : E3 => (-q i / ‖z - a i‖ ^ 3) • (z - a i)) L x ∧
        L v = (-q i / ‖x - a i‖ ^ 3) • v := by
      intro i
      obtain ⟨L, hLf, hLv⟩ := force_term_hasFDerivAt (q i) (fun h => hx.1 ⟨i, h.symm⟩)
      exact ⟨L, hLf, hLv v (hxv i)⟩
    choose L hLf hLv using hL
    let G : E3 → E3 := fun z => ∑ i : Fin 3, (-q i / ‖z - a i‖ ^ 3) • (z - a i)
    have hG_fderiv : HasFDerivAt G (∑ i : Fin 3, L i) x := by
      simpa only [G] using HasFDerivAt.fun_sum (fun i _ => hLf i)
    have hG_v : (∑ i : Fin 3, L i) v = 0 := by
      rw [sum_apply]
      simp_rw [hLv, ← Finset.sum_smul, hsum_zero, zero_smul]
    -- Relate fderiv ℝ (potential q a) to (toDual ℝ E3) ∘ G near x
    have hopen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
    have hev : fderiv ℝ (potential q a) =ᶠ[𝓝 x] fun z => (toDual ℝ E3) (G z) := by
      filter_upwards [hopen.mem_nhds hx.1] with z hz
      exact (potential_hasGradient q a z hz).hasFDerivAt.fderiv
    have hD2 : HasFDerivAt (fderiv ℝ (potential q a))
        ((toDual ℝ E3).toContinuousLinearMap.comp (∑ i : Fin 3, L i)) x := by
      have h1 : HasFDerivAt (fun z => (toDual ℝ E3) (G z))
          ((toDual ℝ E3).toContinuousLinearMap.comp (∑ i : Fin 3, L i)) x :=
        (toDual ℝ E3).toContinuousLinearMap.hasFDerivAt.comp x hG_fderiv
      exact h1.congr_of_eventuallyEq hev
    obtain ⟨w, hw⟩ := hnd v hv0
    apply hw
    rw [iteratedFDeriv_two_apply, hD2.fderiv]
    simp [hG_v]

/- ### Part 4: Main proof of `H2` -/

private lemma collinear_param {a : Fin 3 → E3} (ha : Function.Injective a)
    (hdep : ¬ AffineIndependent ℝ a) :
    ∃ (p₀ u : E3) (s : Fin 3 → ℝ), ‖u‖ = 1 ∧ Function.Injective s ∧ ∀ i, a i = p₀ + s i • u := by
  have h10 : a 1 ≠ a 0 := fun h => by have := ha h; omega
  set d : E3 := a 1 - a 0
  have hd : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h10)
  set u : E3 := ‖d‖⁻¹ • d
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hd
  -- Since ¬ AffineIndependent ℝ a, there is a nontrivial zero-sum linear combination
  rw [affineIndependent_iff_of_fintype] at hdep
  push Not at hdep
  obtain ⟨w, hw_sum, hw_vsub, i₀, hi₀⟩ := hdep
  -- Expand Fin.sum_univ_three on weightedVSub
  have hlin : w 1 • (a 1 - a 0) + w 2 • (a 2 - a 0) = 0 := by
    have h1 := Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero Finset.univ w a hw_sum (a 0)
    rw [hw_vsub] at h1
    simp only [Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three, vsub_eq_sub, sub_self,
      smul_zero, zero_add] at h1
    exact h1.symm
  have hw2 : w 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero] at hlin
    have h1 : w 1 = 0 := (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr h10)
    have h0 : w 0 = 0 := by
      simp only [Fin.sum_univ_three] at hw_sum; linarith
    fin_cases i₀ <;> exact hi₀ (by assumption)
  have ha2 : a 2 - a 0 = (-(w 1 / w 2)) • (a 1 - a 0) := by
    have h1 : w 2 • (a 2 - a 0) = (-w 1) • (a 1 - a 0) := by
      rw [neg_smul]; exact eq_neg_of_add_eq_zero_right hlin
    calc
      a 2 - a 0 = (w 2)⁻¹ • (w 2 • (a 2 - a 0)) := by rw [inv_smul_smul₀ hw2]
      _ = (w 2)⁻¹ • ((-w 1) • (a 1 - a 0)) := by rw [h1]
      _ = (-(w 1 / w 2)) • (a 1 - a 0) := by rw [smul_smul]; congr 1; ring
  let s : Fin 3 → ℝ := ![0, ‖d‖, (-(w 1 / w 2)) * ‖d‖]
  have hparam : ∀ i : Fin 3, a i = a 0 + s i • u := by
    intro i; fin_cases i
    · simp [s]
    · change a 1 = a 0 + ‖d‖ • u
      simp only [u, smul_smul, mul_inv_cancel₀ hd, one_smul, d]
      abel
    · change a 2 = a 0 + (-(w 1 / w 2) * ‖d‖) • u
      simp only [u, smul_smul]
      rw [mul_assoc, mul_inv_cancel₀ hd, mul_one, ← ha2]
      abel
  refine ⟨a 0, u, s, hu, ?_, hparam⟩
  intro i j hij
  apply ha
  rw [hparam i, hparam j, hij]

end OMA.Proof_Maxwell_ThreeCharges_R1_H2

open OMA.Proof_Maxwell_ThreeCharges_R1_H2
open Arxiv.«2607.27197» InnerProductSpace
open scoped BigOperators Gradient RealInnerProductSpace

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1.H2 := by
  intro q a ha hdep hq hnd
  obtain ⟨p₀, u, s, hu, hs_inj, ha_line⟩ := collinear_param ha hdep
  -- Sort the 3 distinct values s 0, s 1, s 2 via an equivalence σ : Fin 3 ≃ Fin 3
  have hperm : ∃ σ : Equiv.Perm (Fin 3), s (σ 0) < s (σ 1) ∧ s (σ 1) < s (σ 2) := by
    have h01 : s 0 ≠ s 1 := fun h => by have := hs_inj h; omega
    have h02 : s 0 ≠ s 2 := fun h => by have := hs_inj h; omega
    have h12 : s 1 ≠ s 2 := fun h => by have := hs_inj h; omega
    rcases lt_or_gt_of_ne h01 with a01 | a10 <;>
    rcases lt_or_gt_of_ne h02 with a02 | a20 <;>
    rcases lt_or_gt_of_ne h12 with a12 | a21
    · exact ⟨Equiv.refl _, a01, a12⟩
    · exact ⟨Equiv.swap 1 2, a02, a21⟩
    · exfalso; linarith
    · exact ⟨Equiv.swap 0 2 * Equiv.swap 1 2, a20, a01⟩
    · exact ⟨Equiv.swap 0 1, a10, a02⟩
    · exfalso; linarith
    · exact ⟨Equiv.swap 0 1 * Equiv.swap 1 2, a12, a20⟩
    · exact ⟨Equiv.swap 0 2, a21, a10⟩
  obtain ⟨σ, hσ01, hσ12⟩ := hperm
  set c₀ := s (σ 0); set c₁ := s (σ 1); set c₂ := s (σ 2)
  set w₀ := q (σ 0); set w₁ := q (σ 1); set w₂ := q (σ 2)
  have h1D := card_roots_sorted hσ01 hσ12 (hq (σ 0)) (hq (σ 1)) (hq (σ 2))
  let f : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => p₀ + t • u
  have hsub : equilibria q a ⊆ f '' {t : ℝ | t ≠ c₀ ∧ t ≠ c₁ ∧ t ≠ c₂ ∧
      force1D ![w₀, w₁, w₂] ![c₀, c₁, c₂] t = 0} := by
    intro x hx
    obtain ⟨t, rfl⟩ := equilibrium_on_line ha_line hu hx (hnd x hx)
    refine ⟨t, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · intro ht; exact hx.1 ⟨σ 0, by rw [ha_line (σ 0), ht]⟩
    · intro ht; exact hx.1 ⟨σ 1, by rw [ha_line (σ 1), ht]⟩
    · intro ht; exact hx.1 ⟨σ 2, by rw [ha_line (σ 2), ht]⟩
    · have hforce := (potential_hasGradient q a (p₀ + t • u) hx.1).gradient.symm.trans hx.2
      have hinner : ⟪∑ i : Fin 3, (-q i / ‖(p₀ + t • u) - a i‖ ^ 3) • ((p₀ + t • u) - a i), u⟫ = 0 := by
        rw [hforce, inner_zero_left]
      rw [sum_inner, ← Equiv.sum_comp σ] at hinner
      have hterm (j : Fin 3) :
          ⟪(-q (σ j) / ‖(p₀ + t • u) - a (σ j)‖ ^ 3) • ((p₀ + t • u) - a (σ j)), u⟫ =
            -q (σ j) * (t - s (σ j)) / |t - s (σ j)| ^ 3 := by
        have hdiff : (p₀ + t • u) - a (σ j) = (t - s (σ j)) • u := by
          rw [ha_line (σ j), sub_smul]; abel
        rw [hdiff, norm_smul, Real.norm_eq_abs, hu, mul_one, inner_smul_left, inner_smul_left,
          conj_trivial, conj_trivial, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
        ring
      simp_rw [hterm] at hinner
      unfold force1D
      rw [Fin.sum_univ_three] at hinner ⊢
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] using hinner
  exact (Set.encard_le_encard hsub).trans ((Set.encard_image_le f _).trans h1D)
