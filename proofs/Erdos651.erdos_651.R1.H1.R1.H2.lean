import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1
import Mathlib

/-! An exact proof of three-dimensional cups versus caps for an affine orthant. -/

/-
The three coordinate projections of a polyhedral orthant give three contraction
preorders. An antichain in one preorder contains a large planar line-free
family, where planar cups and caps provide the required witnesses.
-/

open scoped Affine EuclideanGeometry BigOperators

namespace OMA.R_Erdos651_erdos_651_R1_H1_R1_H2_R1

private theorem median_between {u v w : ℝ} :
    min u v ≤ max (min u v) (max (min u w) (min v w)) ∧
      max (min u v) (max (min u w) (min v w)) ≤ max u v := by
  exact ⟨le_max_left _ _, max_le (min_le_left _ _ |>.trans (le_max_left _ _))
    (max_le ((min_le_left _ _).trans (le_max_left _ _))
      ((min_le_left _ _).trans (le_max_right _ _)))⟩

private theorem affine_between_nonpos {a b u v t : ℝ}
    (hu : a + u * b ≤ 0) (hv : a + v * b ≤ 0)
    (ht₁ : min u v ≤ t) (ht₂ : t ≤ max u v) : a + t * b ≤ 0 := by
  have hsign := le_total 0 b
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv] at ht₁
    rw [max_eq_right huv] at ht₂
    rcases hsign with hb | hb
    · linarith [mul_le_mul_of_nonneg_right ht₂ hb]
    · linarith [mul_le_mul_of_nonpos_right ht₁ hb]
  · rw [min_eq_right hvu] at ht₁
    rw [max_eq_left hvu] at ht₂
    rcases hsign with hb | hb
    · linarith [mul_le_mul_of_nonneg_right ht₂ hb]
    · linarith [mul_le_mul_of_nonpos_right ht₁ hb]

/-- If every two coordinates allow an affine-line parameter, all three do.
The median of the three witnesses satisfies every coordinate. -/
theorem all_coordinates_of_pairs (a b : Fin 3 → ℝ)
    (h : ∀ j : Fin 3, ∃ t : ℝ, ∀ k : Fin 3, k ≠ j → a k + t * b k ≤ 0) :
    ∃ t : ℝ, ∀ k : Fin 3, a k + t * b k ≤ 0 := by
  obtain ⟨t₀, h₀⟩ := h 0
  obtain ⟨t₁, h₁⟩ := h 1
  obtain ⟨t₂, h₂⟩ := h 2
  refine ⟨max (min t₀ t₁) (max (min t₀ t₂) (min t₁ t₂)), ?_⟩
  intro k
  fin_cases k
  · apply affine_between_nonpos (h₁ 0 (by decide)) (h₂ 0 (by decide))
    · exact (le_max_right (min t₀ t₂) (min t₁ t₂)).trans (le_max_right _ _)
    · exact max_le ((min_le_right _ _).trans (le_max_left _ _))
        (max_le ((min_le_right _ _).trans (le_max_right _ _))
          ((min_le_left _ _).trans (le_max_left _ _)))
  · apply affine_between_nonpos (h₀ 1 (by decide)) (h₂ 1 (by decide))
    · exact (le_max_left (min t₀ t₂) (min t₁ t₂)).trans (le_max_right _ _)
    · exact max_le ((min_le_left _ _).trans (le_max_left _ _))
        (max_le (min_le_left _ _ |>.trans (le_max_left _ _))
          ((min_le_right _ _).trans (le_max_right _ _)))
  · exact affine_between_nonpos (h₀ 2 (by decide)) (h₁ 2 (by decide))
      median_between.1 median_between.2

/-- An extrapolated point of a segment can belong to the negative orthant
only when one endpoint is dominated by a contraction of the other. -/
theorem contraction_of_extrapolated_nonpos {ι : Type*} (x y : ι → ℝ) {t : ℝ}
    (ht : t < 0) (h : ∀ i, (1 - t) * x i + t * y i ≤ 0) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ i, x i ≤ s * y i := by
  have hden : 0 < 1 - t := by linarith
  refine ⟨-t / (1 - t), div_nonneg (by linarith) hden.le, ?_, fun i => ?_⟩
  · exact (div_lt_one hden).2 (by linarith)
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    linarith only [h i]

/-- Conversely coordinatewise domination by a strict contraction gives
an explicit point of the full line in the closed negative orthant. -/
theorem nonpos_line_of_contraction {ι : Type*} (x y : ι → ℝ) {s : ℝ}
    (hs : s < 1) (h : ∀ i, x i ≤ s * y i) :
    ∃ t : ℝ, ∀ i, (1 - t) * x i + t * y i ≤ 0 := by
  have hden : 0 < 1 - s := by linarith
  refine ⟨-s / (1 - s), fun i => ?_⟩
  have heq : (1 - -s / (1 - s)) * x i + (-s / (1 - s)) * y i =
      (x i - s * y i) / (1 - s) := by
    field_simp
    ring
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (h i)) hden.le

/-- A strict common positive coordinate rules out an intersection on the segment.
If both endpoint contractions also fail, the whole line avoids the quadrant. -/
theorem pair_line_avoids {ι : Type*} (x y : ι → ℝ) (j : ι)
    (hx : 0 < x j) (hy : 0 < y j)
    (hxy : ¬ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ i, x i ≤ s * y i)
    (hyx : ¬ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ i, y i ≤ s * x i) :
    ¬ ∃ t : ℝ, ∀ i, (1 - t) * x i + t * y i ≤ 0 := by
  rintro ⟨t, ht⟩
  rcases lt_or_ge t 0 with hn | hn
  · exact hxy (contraction_of_extrapolated_nonpos x y hn ht)
  rcases lt_or_ge 1 t with hp | hp
  · apply hyx (contraction_of_extrapolated_nonpos y x (t := 1 - t) (by linarith) ?_)
    intro i
    convert ht i using 1
    ring
  · have hsum : 0 < (1 - t) * x j + t * y j := by
      rcases eq_or_lt_of_le hn with hzero | hpos
      · simpa [← hzero] using hx
      · positivity
    exact (not_le_of_gt hsum) (ht j)

theorem binomial_slack {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n) :
    2 * ((n + a - 4).choose (a - 2) + 1) ≤ (n + a).choose a := by
  have hrepr : n + a = (n + a - 4) + 4 := by omega
  have hrhs : (n + a).choose a =
      ((n + a - 4) + 4).choose a := by rw [← hrepr]
  rw [hrhs, Nat.add_choose_eq]
  have hm : (a - 2, 2) ∈ Finset.HasAntidiagonal.antidiagonal a :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
  have hle : (n + a - 4).choose (a - 2) * (4 : ℕ).choose 2 ≤
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal a, (n + a - 4).choose ij.1 * (4 : ℕ).choose ij.2 :=
    Finset.single_le_sum (f := fun ij => (n + a - 4).choose ij.1 * (4 : ℕ).choose ij.2)
      (fun _ _ => Nat.zero_le _) hm
  have hc : 0 < (n + a - 4).choose (a - 2) := Nat.choose_pos (by omega)
  have h42 : (4 : ℕ).choose 2 = 6 := by decide
  rw [h42] at hle
  omega

private theorem of_line_free (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)) (x y : ℝ^3)
    (h : Disjoint (line[ℝ, x, y] : Set (ℝ^3)) {z | ∀ k : Fin 3, e z k ≤ 0}) :
    ∃ j : Fin 3, ¬ ∃ t : ℝ, ∀ k : Fin 2,
      (1 - t) * e x (j.succAbove k) + t * e y (j.succAbove k) ≤ 0 := by
  by_contra! hall
  have hp (j : Fin 3) : ∃ t : ℝ, ∀ k : Fin 3, k ≠ j →
      e x k + t * (e y k - e x k) ≤ 0 := by
    obtain ⟨t, ht⟩ := hall j
    refine ⟨t, fun k hkj => ?_⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hkj
    convert ht i using 1
    ring
  obtain ⟨t, ht⟩ := all_coordinates_of_pairs (fun k => e x k)
    (fun k => e y k - e x k) hp
  let w := AffineMap.lineMap x y t
  have hw : w ∈ line[ℝ, x, y] := mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, rfl⟩
  apply Set.disjoint_left.mp h hw
  intro k
  change e.toAffineMap (AffineMap.lineMap x y t) k ≤ 0
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
  change (1 - t) * e x k + t * e y k ≤ 0
  convert ht k using 1
  ring

private theorem orientation_symmetric {ι : Type*} {u v : ι → ℝ}
    (h : ∃ t : ℝ, ∀ k, (1 - t) * u k + t * v k ≤ 0) :
    ∃ t : ℝ, ∀ k, (1 - t) * v k + t * u k ≤ 0 := by
  obtain ⟨t, ht⟩ := h
  refine ⟨1 - t, fun k => ?_⟩
  convert ht k using 1
  ring

private theorem large_positive_half {V : Type} [DecidableEq V]
    (S : Finset V) (f : V → Fin 2 → ℝ) {m : ℕ} (hS : 2 * m < S.card)
    (hpos : ∀ x ∈ S, ∃ i, 0 < f x i) :
    ∃ i : Fin 2, ∃ T ⊆ S, m < T.card ∧ ∀ x ∈ T, 0 < f x i := by
  classical
  let A := S.filter (fun x => 0 < f x 0)
  let B := S.filter (fun x => ¬0 < f x 0)
  have hsum : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not (s := S) _
  by_cases hA : m < A.card
  · exact ⟨0, A, Finset.filter_subset _ _, hA, fun x hx => (Finset.mem_filter.mp hx).2⟩
  · refine ⟨1, B, Finset.filter_subset _ _, by omega, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hpos x (Finset.mem_filter.mp hx).1
    fin_cases i
    · exact ((Finset.mem_filter.mp hx).2 hi).elim
    · exact hi

/-- Finite simultaneous-chain pigeonhole consequence of Dilworth's theorem. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (R : Fin 3 → V → V → Prop) (m : ℕ),
    (∀ j x, R j x x) →
    (∀ j x y z, R j x y → R j y z → R j x z) →
    (∀ x y, x ≠ y → ∃ j, ¬R j x y ∧ ¬R j y x) →
    m ^ 3 < Fintype.card V →
    ∃ S : Finset V, m < S.card ∧ ∃ j : Fin 3,
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬R j x y ∧ ¬R j y x

/-- The planar cups-versus-caps theorem for a set of points whose pair lines
miss the negative quadrant. Witnesses are indexed by the original set. -/
def H2 : Prop :=
  ∀ (V : Type) [DecidableEq V] (S : Finset V) (f : V → Fin 2 → ℝ) (a n : ℕ),
    (∀ Z ⊆ S, Z.card ≤ 3 → AffineIndependent ℝ (fun z : ↥(Z : Set V) => f z)) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ¬ ∃ t : ℝ, ∀ i, (1 - t) * f x i + t * f y i ≤ 0) →
    2 ≤ a → 2 ≤ n → (n + a - 4).choose (a - 2) + 1 < S.card →
    (∃ K ⊆ S, K.card = n ∧ ∀ x ∈ K,
      f x ∉ convexHull ℝ (f '' (K.erase x : Set V))) ∨
    (∃ K ⊆ S, K.card = a ∧ ∀ x ∈ K,
      f x ∉ convexHull ℝ ({q : Fin 2 → ℝ | ∀ i, q i ≤ 0} ∪
        f '' (K.erase x : Set V)))

theorem main : H1 → H2 → OMA.R_Erdos651_erdos_651_R1_H1_R1.H2 := by
  classical
  intro hDilworth hPlanar P Y a n hOrthant _hGeneral hLines ha hn hLarge
  obtain ⟨e, rfl, hProjections⟩ := hOrthant
  let m := (n + a).choose a
  let f (j : Fin 3) : (ℝ^3) →ᵃ[ℝ] (Fin 2 → ℝ) :=
    (({ toFun := fun x k => x (j.succAbove k)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl } :
        (ℝ^3) →ₗ[ℝ] (Fin 2 → ℝ)).toAffineMap).comp e.toAffineMap
  have hf (j : Fin 3) (x : ℝ^3) (i : Fin 2) : f j x i = e x (j.succAbove i) := rfl
  let R (j : Fin 3) (x y : (ℝ^3)) : Prop :=
    x = y ∨ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ k, f j x k ≤ s * f j y k
  have hRtrans (j : Fin 3) (x y z : (ℝ^3)) : R j x y → R j y z → R j x z := by
    rintro (rfl | ⟨r, hr0, hr1, hr⟩) hs
    · exact hs
    rcases hs with rfl | ⟨s, hs0, hs1, hs⟩
    · exact Or.inr ⟨r, hr0, hr1, hr⟩
    refine Or.inr ⟨r * s, mul_nonneg hr0 hs0, ?_, fun k => ?_⟩
    · calc
        r * s ≤ r * 1 := mul_le_mul_of_nonneg_left hs1.le hr0
        _ = r := mul_one _
        _ < 1 := hr1
    · calc
        f j x k ≤ r * f j y k := hr k
        _ ≤ r * (s * f j z k) := mul_le_mul_of_nonneg_left (hs k) hr0
        _ = (r * s) * f j z k := (mul_assoc _ _ _).symm
  have hRinc (x y : ↥Y) (hxy : x ≠ y) : ∃ j, ¬ R j x y ∧ ¬ R j y x := by
    have hv : (x : ℝ^3) ≠ (y : ℝ^3) := fun h => hxy (Subtype.ext h)
    obtain ⟨j, hj⟩ := of_line_free e x y (hLines x x.property y y.property hv)
    simp only [← hf] at hj
    refine ⟨j, ?_, ?_⟩
    · rintro (h | ⟨s, _, hs, h⟩)
      · exact hv h
      · exact hj (nonpos_line_of_contraction (f j x) (f j y) hs h)
    · rintro (h | ⟨s, _, hs, h⟩)
      · exact hv h.symm
      · exact hj (orientation_symmetric (nonpos_line_of_contraction (f j y) (f j x) hs h))
  have hcard : m ^ 3 < Fintype.card ↥Y := by
    simpa [m] using hLarge
  obtain ⟨T, hT, j, hAnti⟩ := hDilworth ↥Y (fun j x y => R j x y) m
    (fun _ _ => Or.inl rfl) (fun j x y z => hRtrans j x y z) hRinc hcard
  let S := T.map (Function.Embedding.subtype fun x : ℝ^3 => x ∈ Y)
  have hSY : S ⊆ Y := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hx
    exact z.property
  have hS : m < S.card := by simpa only [S, Finset.card_map] using hT
  have hAnt (x : ℝ^3) (hx : x ∈ S) (y : ℝ^3) (hy : y ∈ S) (hne : x ≠ y) :
      ¬R j x y ∧ ¬R j y x := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact hAnti u hu v hv (fun h => hne (congrArg Subtype.val h))
  have hm := binomial_slack ha hn
  have hpos (x : ℝ^3) (hx : x ∈ S) : ∃ i, 0 < f j x i := by
    by_contra! hx0
    have hOne : 1 < S.card := by omega
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne hOne x
    apply (hAnt x hx y hy hne.symm).1
    exact Or.inr ⟨0, le_rfl, zero_lt_one, by simpa using hx0⟩
  obtain ⟨i, U, hUS, hU, hUpos⟩ :=
    large_positive_half S (f j) (by omega : 2 * ((n + a - 4).choose (a - 2) + 1) < S.card) hpos
  have hUY := hUS.trans hSY
  have hULine (x : ℝ^3) (hx : x ∈ U) (y : ℝ^3) (hy : y ∈ U) (hne : x ≠ y) :
      ¬ ∃ t : ℝ, ∀ k, (1 - t) * f j x k + t * f j y k ≤ 0 := by
    obtain ⟨hn₁, hn₂⟩ := hAnt x (hUS hx) y (hUS hy) hne
    exact pair_line_avoids (f j x) (f j y) i (hUpos x hx) (hUpos y hy)
      (fun ht => hn₁ (Or.inr ht)) (fun ht => hn₂ (Or.inr ht))
  have hUP (Z : Finset (ℝ^3)) (hZU : Z ⊆ U) (hZ : Z.card ≤ 3) :
      AffineIndependent ℝ (fun z : ↥(Z : Set (ℝ^3)) => f j z) := by
    change AffineIndependent ℝ
      (fun z : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => e z (j.succAbove k))
    exact hProjections j Z (hZU.trans hUY) hZ
  rcases hPlanar (ℝ^3) U (f j) a n hUP hULine ha hn hU with
      ⟨K, hKU, hKcard, hK⟩ | ⟨K, hKU, hKcard, hK⟩
  · apply Or.inl
    refine ⟨K, hKU.trans hUY, hKcard, ?_⟩
    rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro x hx hcx
    apply hK x hx
    rw [← (f j).image_convexHull]
    exact ⟨x, by simpa only [Finset.coe_erase] using hcx, rfl⟩
  · apply Or.inr
    refine ⟨K, hKU.trans hUY, hKcard, ?_⟩
    intro x hx hcx
    apply hK x hx
    have him : (f j) '' ({z : ℝ^3 | ∀ k : Fin 3, e z k ≤ 0} ∪ (K.erase x : Set (ℝ^3))) ⊆
        {q : Fin 2 → ℝ | ∀ k, q k ≤ 0} ∪ (f j) '' (K.erase x : Set (ℝ^3)) := by
      rintro q ⟨z, hz | hz, rfl⟩
      · exact Or.inl fun k => hz (j.succAbove k)
      · exact Or.inr ⟨z, hz, rfl⟩
    refine convexHull_mono him ?_
    rw [← (f j).image_convexHull]
    exact ⟨x, hcx, rfl⟩

end OMA.R_Erdos651_erdos_651_R1_H1_R1_H2_R1

/- A finite Dilworth chain coloring from Hall's marriage theorem. -/

namespace OMA.Erdos651Dilworth

open Finset

private theorem hall_successor {V : Type} [Fintype V] (r : V → V → Prop) (m : ℕ)
    (hw : ∀ s : Finset V, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬r x y ∧ ¬r y x) → s.card ≤ m) :
    ∃ f : V → V ⊕ Fin m, Function.Injective f ∧ ∀ x y, f x = Sum.inl y → r x y := by
  classical
  let allowed (a : V) (b : V ⊕ Fin m) := b.elim (r a) (fun _ => True)
  have hall : ∀ s : Finset V, s.card ≤
      (Finset.univ.filter fun b : V ⊕ Fin m => ∃ a ∈ s, allowed a b).card := by
    intro s
    by_cases hs : s.Nonempty
    · let t := s.filter fun b => ¬∃ a ∈ s, r a b
      have ht : t.card ≤ m := by
        apply hw
        intro x hx y hy _
        have hx' := Finset.mem_filter.mp hx
        have hy' := Finset.mem_filter.mp hy
        exact ⟨fun h => hy'.2 ⟨x,hx'.1,h⟩, fun h => hx'.2 ⟨y,hy'.1,h⟩⟩
      let u := (s \ t).disjSum (Finset.univ : Finset (Fin m))
      have hsub : u ⊆ Finset.univ.filter (fun b : V ⊕ Fin m => ∃ a ∈ s, allowed a b) := by
        intro b hb
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        cases b with
        | inl b =>
          have hb' : b ∈ s \ t := by simpa [u] using hb
          have hbs := (Finset.mem_sdiff.mp hb').1
          have hbt := (Finset.mem_sdiff.mp hb').2
          by_contra! h
          exact hbt (Finset.mem_filter.mpr ⟨hbs, fun ⟨a,ha,hr⟩ => h a ha hr⟩)
        | inr b =>
          obtain ⟨a,ha⟩ := hs
          exact ⟨a,ha,trivial⟩
      calc
        s.card = (s \ t).card + t.card := by
          rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
          exact (Nat.sub_add_cancel (Finset.card_le_card (Finset.filter_subset _ _))).symm
        _ ≤ u.card := by simp only [u, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]; omega
        _ ≤ _ := Finset.card_le_card hsub
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp
  obtain ⟨f,hf,hfok⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective allowed).mp hall
  refine ⟨f,hf,fun x y h => ?_⟩
  simpa only [h, allowed, Sum.elim_inl] using hfok x

private theorem strict_successors_wf {V : Type} [Fintype V] (r : V → V → Prop)
    (hir : ∀ x, ¬r x x)
    (htr : ∀ x y z, r x y → r y z → r x z) :
    WellFounded (fun y x => r x y) := by
  classical
  let s (x : V) := Finset.univ.filter (r x)
  refine Subrelation.wf (r := fun y x => (s y).card < (s x).card) (fun {y x} h => ?_)
    (measure (fun x => (s x).card)).wf
  have hsub : s y ⊆ s x := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htr x y z h (Finset.mem_filter.mp hz).2⟩
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset hsub).mpr ⟨y,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩, fun hy => hir y (Finset.mem_filter.mp hy).2⟩

/-- An injective assignment to a successor or a dummy gives a chain color. -/
private theorem chain_color_of_successors {V : Type} (r : V → V → Prop) (m : ℕ)
    (hwf : WellFounded (fun y x => r x y))
    (trans : ∀ x y z, r x y → r y z → r x z)
    (f : V → V ⊕ Fin m) (hinj : Function.Injective f)
    (hstep : ∀ x y, f x = Sum.inl y → r x y) :
    ∃ c : V → Fin m, ∀ x y, c x = c y → x = y ∨ r x y ∨ r y x := by
  let code : V → ℕ × Fin m := hwf.fix (fun x rec =>
    match h : f x with
    | Sum.inl y => ((rec y (hstep x y h)).1 + 1, (rec y (hstep x y h)).2)
    | Sum.inr c => (0,c))
  have code_step (x y : V) (h : f x = Sum.inl y) :
      code x = ((code y).1 + 1, (code y).2) := by
    conv_lhs => unfold code; rw [WellFounded.fix_eq]
    split
    · rename_i b hb
      have e : b = y := Sum.inl.inj (hb.symm.trans h)
      subst b
      rfl
    · rename_i d hd
      rw [h] at hd
      cases hd
  have code_end (x : V) (c : Fin m) (h : f x = Sum.inr c) :
      code x = (0,c) := by
    conv_lhs => unfold code; rw [WellFounded.fix_eq]
    split
    · rename_i b hb
      rw [h] at hb
      cases hb
    · rename_i d hd
      have e : d = c := Sum.inr.inj (hd.symm.trans h)
      subst d
      rfl
  have code_inj : Function.Injective code := by
    have aux : ∀ k : ℕ, ∀ x y, (code x).1 = k → code x = code y → x = y := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro x y hx he
        cases hfx : f x with
        | inl a =>
          have hca := code_step x a hfx
          have ht : (code a).1 < k := by rw [hca] at hx; simp only at hx; omega
          cases hfy : f y with
          | inl b =>
            have hcb := code_step y b hfy
            rw [hca,hcb] at he
            have hdepth : (code a).1 = (code b).1 := by
              have h := congrArg Prod.fst he
              simp only at h
              omega
            have hcolor := congrArg (fun z : ℕ × Fin m => z.2) he
            have hab := ih (code a).1 ht a b rfl (Prod.ext hdepth hcolor)
            apply hinj
            rw [hfx,hfy,hab]
          | inr c =>
            rw [hca,code_end y c hfy] at he
            have h := congrArg Prod.fst he
            simp at h
        | inr c =>
          have hc := code_end x c hfx
          cases hfy : f y with
          | inl b =>
            rw [hc,code_step y b hfy] at he
            have h := congrArg Prod.fst he
            simp at h
          | inr d =>
            rw [hc,code_end y d hfy] at he
            have hcd : c = d := congrArg (fun z : ℕ × Fin m => z.2) he
            apply hinj
            rw [hfx,hfy,hcd]
    intro x y h
    exact aux _ x y rfl h
  have reverse_chain : ∀ n : ℕ, ∀ x y : V, (code y).1 = n →
      (code x).1 ≤ (code y).1 → (code x).2 = (code y).2 → y = x ∨ r y x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hy hd hc
      by_cases heq : (code x).1 = (code y).1
      · exact Or.inl ((code_inj (Prod.ext heq hc)).symm)
      have hlt := lt_of_le_of_ne hd heq
      cases hf : f y with
      | inl z =>
        have hz := code_step y z hf
        have hzn : (code z).1 < n := by rw [hz] at hy; simp only at hy; omega
        have hdepth : (code x).1 ≤ (code z).1 := by rw [hz] at hlt; simp only at hlt; omega
        have hcolor : (code x).2 = (code z).2 := by rw [hz] at hc; exact hc
        rcases ih _ hzn x z rfl hdepth hcolor with rfl | h
        · exact Or.inr (hstep y z hf)
        · exact Or.inr (trans y z x (hstep y z hf) h)
      | inr c =>
        rw [code_end y c hf] at hlt
        exact (Nat.not_lt_zero _ hlt).elim
  refine ⟨fun x => (code x).2,fun x y h => ?_⟩
  rcases le_total (code x).1 (code y).1 with hxy | hyx
  · rcases reverse_chain _ x y rfl hxy h with e | hr
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr hr)
  · rcases reverse_chain _ y x rfl hyx h.symm with e | hr
    · exact Or.inl e
    · exact Or.inr (Or.inl hr)

/-- A finite preorder of antichain width at most m admits a chain coloring with m colors. -/
theorem preorder_chain_coloring {V : Type} [Fintype V] (r : V → V → Prop) (m : ℕ)
    (hre : ∀ x, r x x) (htr : ∀ x y z, r x y → r y z → r x z)
    (hw : ∀ s : Finset V, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬r x y ∧ ¬r y x) → s.card ≤ m) :
    ∃ c : V → Fin m, ∀ x y, c x = c y → r x y ∨ r y x := by
  classical
  let label := Fintype.equivFin V
  let lt (x y : V) := r x y ∧ (¬r y x ∨ label x < label y)
  have hir (x : V) : ¬ lt x x := by
    rintro ⟨_,hn|hn⟩
    · exact hn (hre x)
    · exact (lt_irrefl _ hn)
  have ht (x y z : V) (hxy : lt x y) (hyz : lt y z) : lt x z := by
    refine ⟨htr x y z hxy.1 hyz.1,?_⟩
    by_cases hzx : r z x
    · exact Or.inr ((hxy.2.resolve_left (not_not_intro (htr y z x hyz.1 hzx))).trans
        (hyz.2.resolve_left (not_not_intro (htr z x y hzx hxy.1))))
    · exact Or.inl hzx
  have hwidth (s : Finset V) (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬lt x y ∧ ¬lt y x) :
      s.card ≤ m := by
    apply hw
    intro x hx y hy hne
    have h := hs x hx y hy hne
    rcases lt_or_gt_of_ne (fun h => hne (label.injective h)) with hxy | hyx
    · have hxn : ¬r x y := fun hr => h.1 ⟨hr,Or.inr hxy⟩
      exact ⟨hxn,fun hr => h.2 ⟨hr,Or.inl hxn⟩⟩
    · have hyn : ¬r y x := fun hr => h.2 ⟨hr,Or.inr hyx⟩
      exact ⟨fun hr => h.1 ⟨hr,Or.inl hyn⟩,hyn⟩
  obtain ⟨f,hf,hstep⟩ := hall_successor lt m hwidth
  obtain ⟨c,hc⟩ := chain_color_of_successors lt m (strict_successors_wf lt hir ht) ht f hf hstep
  refine ⟨c,fun x y h => ?_⟩
  rcases hc x y h with rfl | hxy | hyx
  · exact Or.inl (hre x)
  · exact Or.inl hxy.1
  · exact Or.inr hyx.1

/-- Three preorders that separate every distinct pair cannot all have width at most m
when the finite vertex set has more than m cubed elements. -/
theorem three_preorders {V : Type} [Fintype V] (R : Fin 3 → V → V → Prop) (m : ℕ)
    (hr : ∀ j x, R j x x) (ht : ∀ j x y z, R j x y → R j y z → R j x z)
    (hsep : ∀ x y, x ≠ y → ∃ j, ¬R j x y ∧ ¬R j y x)
    (hN : m^3 < Fintype.card V) :
    ∃ S : Finset V, m < S.card ∧ ∃ j : Fin 3,
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬R j x y ∧ ¬R j y x := by
  classical
  by_contra hbad
  have hc j : ∃ c : V → Fin m, ∀ x y, c x = c y → R j x y ∨ R j y x := by
    apply preorder_chain_coloring (R j) m (hr j) (ht j)
    intro s hs
    apply Nat.le_of_not_gt
    intro h
    exact hbad ⟨s,h,j,hs⟩
  choose c hc using hc
  have inj : Function.Injective (fun x (j : Fin 3) => c j x) := by
    intro x y h
    by_contra hn
    obtain ⟨j,hj₁,hj₂⟩ := hsep x y hn
    exact (hc j x y (congrFun h j)).elim hj₁ hj₂
  have h := Fintype.card_le_of_injective _ inj
  simp at h
  omega

end OMA.Erdos651Dilworth

/- Ordered cups and caps and the Erdős–Szekeres endpoint recurrence. -/

namespace OMA.Erdos651CupsCaps

open Finset

variable {V : Type}

/-- Successive triples have the given orientation. -/
def tripChain (r : V → V → V → Prop) : List V → Prop
  | x :: y :: z :: tail => r x y z ∧ tripChain r (y :: z :: tail)
  | _ => True

/-- A chain of (k) vertices, increasing in the first coordinate. -/
def HasChain (u : V → ℝ) (r : V → V → V → Prop) (S : Finset V) (k : ℕ) : Prop :=
  ∃ l : List V, l.length = k ∧ (∀ x ∈ l, x ∈ S) ∧
    l.Pairwise (fun x y => u x < u y) ∧ tripChain r l

private theorem append_two_of_length (l : List V) (h : 2 ≤ l.length) :
    ∃ (p : List V) (x y : V), l = p ++ [x,y] := by
  cases l using List.reverseRecOn with
  | nil => simp at h
  | append_singleton l y =>
    cases l using List.reverseRecOn with
    | nil => simp at h
    | append_singleton l x =>
      exact ⟨l,x,y,by simp [List.append_assoc]⟩

private theorem trip_snoc (r : V → V → V → Prop)
    (p : List V) (x y z : V) (h : tripChain r (p ++ [x,y]))
    (hy : r x y z) : tripChain r (p ++ [x,y,z]) := by
  induction p with
  | nil => simpa [tripChain] using hy
  | cons w l ih =>
    cases l with
    | nil =>
      simp [tripChain] at h ⊢
      exact ⟨h,hy⟩
    | cons v l =>
      cases l with
      | nil =>
        simp [tripChain] at h ⊢
        exact ⟨h.1,h.2,hy⟩
      | cons q l =>
        simp only [List.cons_append, tripChain] at h ⊢
        exact ⟨h.1,ih h.2⟩

private theorem sorted_snoc (u : V → ℝ) {p : List V} {x y : V}
    (h : (p ++ [x]).Pairwise (fun a b => u a < u b)) (hy : u x < u y) :
    (p ++ [x,y]).Pairwise (fun a b => u a < u b) := by
  have h' := List.pairwise_append.mp h
  apply List.pairwise_append.mpr
  refine ⟨h'.1, by simpa using hy, ?_⟩
  intro a ha b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact h'.2.2 a ha _ (by simp)
  · exact (h'.2.2 a ha x (by simp)).trans hy

private theorem has_two (u : V → ℝ) (r : V → V → V → Prop)
    {S : Finset V} (hU : Set.InjOn u (↑S : Set V)) (hS : 1 < S.card) :
    HasChain u r S 2 := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hS
  rcases lt_or_gt_of_ne (fun h => hxy (hU hx hy h)) with huv | huv
  · refine ⟨[x,y],rfl,?_,by simpa using huv,by trivial⟩
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · refine ⟨[y,x],rfl,?_,by simpa using huv,by trivial⟩
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hy
    · exact hx

private theorem endpoint_split (u : V → ℝ) (r : V → V → V → Prop)
    (a b : ℕ) (S : Finset V) (hplus : ¬ HasChain u r S (a + 3))
    (hminus : ¬ HasChain u (fun x y z => ¬r x y z) S (b + 3)) :
    ∃ A B : Finset V, A ⊆ S ∧ B ⊆ S ∧ S.card = A.card + B.card ∧
      ¬ HasChain u r A (a + 2) ∧ ¬ HasChain u (fun x y z => ¬r x y z) B (b + 2) := by
  classical
  let Endpoint (x : V) : Prop := ∃ (p : List V) (y : V), (p ++ [y,x]).length = a + 2 ∧
      (∀ z ∈ p ++ [y,x], z ∈ S) ∧
      (p ++ [y,x]).Pairwise (fun v w => u v < u w) ∧ tripChain r (p ++ [y,x])
  let B := S.filter Endpoint
  let A := S \ B
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hAS : A ⊆ S := Finset.sdiff_subset
  have hAB : S.card = A.card + B.card := by
    rw [show A = S \ B from rfl, Finset.card_sdiff_of_subset hBS]
    exact (Nat.sub_add_cancel (Finset.card_le_card hBS)).symm
  refine ⟨A,B,hAS,hBS,hAB,?_,?_⟩
  · rintro ⟨l,hl,hmem,hsorted,hchain⟩
    obtain ⟨p,y,x,rfl⟩ := append_two_of_length l (by omega)
    have hxA := hmem x (by simp)
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_filter.mpr
      ⟨hAS hxA, p,y,hl,fun z hz => hAS (hmem z hz),hsorted,hchain⟩)
  · rintro ⟨l,hl,hmem,hsorted,hchain⟩
    cases l with
    | nil => simp at hl
    | cons x l =>
      cases l with
      | nil => simp at hl
      | cons y tail =>
        have hxB := hmem x (by simp)
        have hyB := hmem y (by simp)
        obtain ⟨p,z,hp,hpmem,hpsorted,hpcup⟩ := (Finset.mem_filter.mp hxB).2
        have hzS := hpmem z (by simp)
        have hxy : u x < u y := (List.pairwise_cons.mp hsorted).1 y (by simp)
        by_cases hpstep : r z x y
        · apply hplus
          refine ⟨p ++ [z,x,y],?_,?_,?_,trip_snoc r p z x y hpcup hpstep⟩
          · simp only [List.length_append, List.length_cons, List.length_nil] at hp ⊢
            omega
          · intro t ht
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with ht | rfl | rfl | rfl
            · exact hpmem t (List.mem_append_left _ ht)
            · exact hzS
            · exact hBS hxB
            · exact hBS hyB
          · have h := sorted_snoc u (p := p ++ [z]) (x := x) (y := y)
              (by simpa only [List.append_assoc, List.singleton_append] using hpsorted) hxy
            simpa only [List.append_assoc, List.singleton_append] using h
        · apply hminus
          refine ⟨z :: x :: y :: tail,?_,?_,List.pairwise_cons.mpr ⟨?_,hsorted⟩,?_⟩
          · simp only [List.length_cons] at hl ⊢
            omega
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hzS
            · exact hBS (hmem t ht)
          · have hzx : u z < u x := by simpa using (List.pairwise_append.mp hpsorted).2.1
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hzx
            · exact hzx.trans ((List.pairwise_cons.mp hsorted).1 _ ht)
          · exact ⟨hpstep,hchain⟩

/-- If neither orientation has a long chain, the binomial bound holds. -/
theorem card_le_choose (u : V → ℝ) (r : V → V → V → Prop)
    (a b : ℕ) (S : Finset V) (hU : Set.InjOn u (↑S : Set V))
    (hplus : ¬ HasChain u r S (a + 2))
    (hminus : ¬ HasChain u (fun x y z => ¬r x y z) S (b + 2)) :
    S.card ≤ (a + b).choose a := by
  have aux : ∀ k a b : ℕ, a+b = k → ∀ S : Finset V,
      Set.InjOn u (↑S : Set V) → ¬ HasChain u r S (a + 2) →
      ¬ HasChain u (fun x y z => ¬r x y z) S (b + 2) →
      S.card ≤ (a + b).choose a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b hk S hU hplus hminus
      cases a with
      | zero =>
        simp only [Nat.choose_zero_right]
        exact Nat.le_of_not_gt (fun hc => hplus (has_two u r hU hc))
      | succ a =>
        cases b with
        | zero =>
          simp only [Nat.add_zero, Nat.choose_self]
          exact Nat.le_of_not_gt (fun hc => hminus (has_two u (fun x y z => ¬r x y z) hU hc))
        | succ b =>
          obtain ⟨A,B,hAS,hBS,hAB,hA,hB⟩ := endpoint_split u r a b S hplus hminus
          have hAc := ih (a + (b+1)) (by omega) a (b+1) rfl A
            (hU.mono hAS) hA (fun ⟨l,hl,hm,hs,hr⟩ => hminus ⟨l,hl,fun x hx => hAS (hm x hx),hs,hr⟩)
          have hBc := ih ((a+1) + b) (by omega) (a+1) b rfl B
            (hU.mono hBS) (fun ⟨l,hl,hm,hs,hr⟩ => hplus ⟨l,hl,fun x hx => hBS (hm x hx),hs,hr⟩) hB
          rw [hAB]
          have ha : a + (b + 1) = a + b + 1 := by omega
          have hb : a + 1 + b = a + b + 1 := by omega
          have hab : a.succ + b.succ = (a + b + 1).succ := by omega
          rw [ha] at hAc
          rw [hb] at hBc
          rw [hab, Nat.choose_succ_succ, Nat.succ_eq_add_one]
          omega
  exact aux _ a b rfl S hU hplus hminus

/-- The finite cups-caps theorem in adjacent-triple form. -/
theorem cups_or_caps (u : V → ℝ) (r : V → V → V → Prop) (a b : ℕ)
    (S : Finset V) (hU : Set.InjOn u (↑S : Set V)) (hS : (a + b).choose a < S.card) :
    HasChain u r S (a + 2) ∨ HasChain u (fun x y z => ¬r x y z) S (b + 2) := by
  classical
  by_cases h : HasChain u r S (a + 2)
  · exact Or.inl h
  · exact Or.inr (by_contra fun hn => (card_le_choose u r a b S hU h hn).not_gt hS)

/-- The orientation at three consecutive indices. -/
theorem tripChain_getElem (r : V → V → V → Prop) (l : List V)
    (h : tripChain r l) (i : ℕ) (hi : i + 2 < l.length) :
    r (l[i]'(by omega)) (l[i+1]'(by omega)) l[i+2] := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => simp at hi
    | cons x l =>
      cases l with
      | nil => simp at hi
      | cons y l =>
        cases l with
        | nil => simp at hi
        | cons z l => exact h.1
  | succ i ih =>
    cases l with
    | nil => simp at hi
    | cons x l =>
      have hil : i + 2 < l.length := by
        simp only [List.length_cons] at hi
        omega
      have ht : tripChain r l := by
        cases l with
        | nil => trivial
        | cons y l =>
          cases l with
          | nil => trivial
          | cons z l => exact h.2
      simpa only [Nat.succ_add, List.getElem_cons_succ] using (ih l ht hil)


end OMA.Erdos651CupsCaps

/- Slope coordinates and supporting lines for a line-free planar family. -/

namespace OMA.Erdos651Planar

def horizontal (p : Fin 2 → ℝ) := p 0 - p 1
def vertical (p : Fin 2 → ℝ) := p 0 + p 1

noncomputable def slope (p q : Fin 2 → ℝ) :=
  (vertical q - vertical p) / (horizontal q - horizontal p)

theorem horizontal_ne_of_line_free {p q : Fin 2 → ℝ} (hne : p ≠ q)
    (hfree : ¬ ∃ t : ℝ, ∀ k, (1 - t) * p k + t * q k ≤ 0) :
    horizontal p ≠ horizontal q := by
  intro hu
  have he : q 0 - p 0 = q 1 - p 1 := by unfold horizontal at hu; linarith
  have hd : q 0 - p 0 ≠ 0 := by
    intro hd
    apply hne
    funext k
    fin_cases k
    · change p 0 = q 0
      linarith
    · change p 1 = q 1
      linarith
  let t := -(max (p 0) (p 1)) / (q 0 - p 0)
  have hmul : t * (q 0 - p 0) = -(max (p 0) (p 1)) :=
    div_mul_cancel₀ _ hd
  apply hfree
  refine ⟨t, ?_⟩
  intro k
  have hk : q k - p k = q 0 - p 0 := by fin_cases k <;> simp_all
  have hp : p k ≤ max (p 0) (p 1) := by
    fin_cases k
    · exact le_max_left _ _
    · exact le_max_right _ _
  calc
    (1 - t) * p k + t * q k = p k + t * (q k - p k) := by ring
    _ ≤ 0 := by rw [hk, hmul]; linarith

theorem slope_in_interval {p q : Fin 2 → ℝ} (h : horizontal p < horizontal q)
    (hfree : ¬ ∃ t : ℝ, ∀ k, (1 - t) * p k + t * q k ≤ 0) :
    -1 ≤ slope p q ∧ slope p q ≤ 1 := by
  have hA : 0 < horizontal q - horizontal p := sub_pos.mpr h
  have hu : p 0 - p 1 < q 0 - q 1 := h
  have same_direction (hd0 : q 0 - p 0 ≠ 0)
      (hd : 0 < (q 1 - p 1) / (q 0 - p 0)) : False := by
    let w := (q 1 - p 1) / (q 0 - p 0)
    let c := max (p 0) (p 1 / w)
    let t := -c / (q 0 - p 0)
    have ht : t * (q 0 - p 0) = -c := div_mul_cancel₀ _ hd0
    have he : t * (q 1 - p 1) = -c * w := by
      dsimp [t, w]
      ring
    have hc0 : p 0 ≤ c := le_max_left _ _
    have hc1 : p 1 ≤ c * w := (div_le_iff₀ hd).mp (le_max_right _ _)
    apply hfree
    refine ⟨t, ?_⟩
    intro k
    fin_cases k
    · change (1 - t) * p 0 + t * q 0 ≤ 0
      linarith only [ht, hc0]
    · change (1 - t) * p 1 + t * q 1 ≤ 0
      linarith only [he, hc1]
  have h0 : 0 ≤ q 0 - p 0 := by
    by_contra! h0
    have h1 : q 1 - p 1 < 0 := by linarith
    exact same_direction h0.ne (div_pos_of_neg_of_neg h1 h0)
  have h1 : q 1 - p 1 ≤ 0 := by
    by_contra! h1
    have h0 : 0 < q 0 - p 0 := by linarith
    exact same_direction h0.ne' (div_pos h1 h0)
  unfold slope
  constructor
  · apply (le_div_iff₀ hA).2
    unfold horizontal vertical
    linarith
  · apply (div_le_iff₀ hA).2
    unfold horizontal vertical
    linarith

theorem secant_positive {p q : Fin 2 → ℝ} (h : horizontal p ≠ horizontal q)
    (hfree : ¬ ∃ t : ℝ, ∀ k, (1 - t) * p k + t * q k ≤ 0) :
    0 < vertical p - slope p q * horizontal p := by
  by_contra! hnot
  have hd : horizontal q - horizontal p ≠ 0 := sub_ne_zero.mpr h.symm
  let t := -horizontal p / (horizontal q - horizontal p)
  have hu : (1 - t) * horizontal p + t * horizontal q = 0 := by
    have hh : t * (horizontal q - horizontal p) = -horizontal p := div_mul_cancel₀ _ hd
    linarith only [hh]
  have hv : (1 - t) * vertical p + t * vertical q ≤ 0 := by
    have he : t * (vertical q - vertical p) = -slope p q * horizontal p := by
      unfold slope t
      ring
    linarith only [he, hnot]
  unfold horizontal at hu
  unfold vertical at hv
  apply hfree
  refine ⟨t, ?_⟩
  intro k
  fin_cases k
  · change (1 - t) * p 0 + t * q 0 ≤ 0
    linarith only [hu, hv]
  · change (1 - t) * p 1 + t * q 1 ≤ 0
    linarith only [hu, hv]

theorem secant_nonpos_on_quadrant {p q : Fin 2 → ℝ} (h : horizontal p < horizontal q)
    (hfree : ¬ ∃ t : ℝ, ∀ k, (1 - t) * p k + t * q k ≤ 0)
    {z : Fin 2 → ℝ} (hz : ∀ k, z k ≤ 0) :
    vertical z - slope p q * horizontal z ≤ 0 := by
  obtain ⟨hs₁, hs₂⟩ := slope_in_interval h hfree
  have h0 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - slope p q by linarith) (hz 0)
  have h1 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 + slope p q by linarith) (hz 1)
  unfold horizontal vertical
  linarith only [h0, h1]

theorem slope_symm (p q : Fin 2 → ℝ) : slope p q = slope q p := by
  unfold slope
  rw [← neg_sub (vertical p) (vertical q), ← neg_sub (horizontal p) (horizontal q),
    neg_div_neg_eq]

theorem slope_average {p q r : Fin 2 → ℝ}
    (hpq : horizontal p < horizontal q) (hqr : horizontal q < horizontal r) :
    (horizontal r - horizontal p) * slope p r =
      (horizontal q - horizontal p) * slope p q +
        (horizontal r - horizontal q) * slope q r := by
  unfold slope
  rw [mul_div_cancel₀ _ (sub_ne_zero.mpr (hpq.trans hqr).ne'),
    mul_div_cancel₀ _ (sub_ne_zero.mpr hpq.ne'),
    mul_div_cancel₀ _ (sub_ne_zero.mpr hqr.ne')]
  ring

/-- A supporting level can meet a set in at most one point other than the
point being tested. This suffices to exclude the latter from the convex hull. -/
theorem support_excludes {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (x y : E) (hxy : x ≠ y)
    (h : ∀ z ∈ S, L z ≤ L x ∧ (L z = L x → z = y)) :
    x ∉ convexHull ℝ S := by
  let C : Set E := {z | L z ≤ L x ∧ (L z = L x → z = y)}
  have hC : Convex ℝ C := by
    intro p hp q hq a b ha hb hab
    have hp' : L p ≤ L x ∧ (L p = L x → p = y) := hp
    have hq' : L q ≤ L x ∧ (L q = L x → q = y) := hq
    change L (a • p + b • q) ≤ L x ∧ (L (a • p + b • q) = L x → a • p + b • q = y)
    simp only [map_add, map_smul, smul_eq_mul]
    have hap := mul_le_mul_of_nonneg_left hp'.1 ha
    have hbq := mul_le_mul_of_nonneg_left hq'.1 hb
    have hlevel : a * L x + b * L x = L x := by rw [← add_mul, hab, one_mul]
    refine ⟨by linarith only [hap, hbq, hlevel], fun hs => ?_⟩
    rcases eq_or_lt_of_le ha with hale | hap'
    · have ha0 : a = 0 := hale.symm
      have hb1 : b = 1 := by linarith
      have hqy : q = y := hq'.2 (by simpa [ha0, hb1] using hs)
      simp [ha0, hb1, hqy]
    rcases eq_or_lt_of_le hb with hble | hbq'
    · have hb0 : b = 0 := hble.symm
      have ha1 : a = 1 := by linarith
      have hpy : p = y := hp'.2 (by simpa [ha1, hb0] using hs)
      simp [ha1, hb0, hpy]
    · have hlevels : L p = L x ∧ L q = L x := by
        constructor
        · apply le_antisymm hp'.1
          by_contra! hlt
          have hm := mul_lt_mul_of_pos_left hlt hap'
          linarith only [hm, hbq, hs, hlevel]
        · apply le_antisymm hq'.1
          by_contra! hlt
          have hm := mul_lt_mul_of_pos_left hlt hbq'
          linarith only [hap, hm, hs, hlevel]
      rw [hp'.2 hlevels.1, hq'.2 hlevels.2, ← add_smul, hab, one_smul]
  intro hx
  have hxC : x ∈ C := convexHull_min h hC hx
  exact hxy (hxC.2 rfl)

theorem secant_comparison {p q : Fin 2 → ℝ} (h : horizontal p < horizontal q)
    (ε l : ℝ) :
    (ε * vertical q - l * horizontal q ≤ ε * vertical p - l * horizontal p ↔
      ε * slope p q ≤ l) ∧
    (ε * vertical p - l * horizontal p ≤ ε * vertical q - l * horizontal q ↔
      l ≤ ε * slope p q) := by
  have he : (horizontal q - horizontal p) * slope p q = vertical q - vertical p :=
    mul_div_cancel₀ _ (sub_ne_zero.mpr h.ne')
  have eq : (horizontal q - horizontal p) * (ε * slope p q) =
      ε * (vertical q - vertical p) := by linear_combination ε * he
  have hp := sub_pos.mpr h
  constructor
  · constructor
    · intro hle
      apply le_of_mul_le_mul_left _ hp
      nlinarith only [eq, hle]
    · intro hle
      have hm := mul_le_mul_of_nonneg_left hle hp.le
      nlinarith only [eq, hm]
  · constructor
    · intro hle
      apply le_of_mul_le_mul_left _ hp
      nlinarith only [eq, hle]
    · intro hle
      have hm := mul_le_mul_of_nonneg_left hle hp.le
      nlinarith only [eq, hm]

noncomputable def slopeFunctional (ε l : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun p := ε * vertical p - l * horizontal p
  map_add' p q := by simp [vertical, horizontal]; ring
  map_smul' a p := by simp [vertical, horizontal]; ring

/-- Given an everywhere decreasing signed slope, pick a secant whose line
supports every other point and meets the family in just its two endpoints. -/
theorem supporting_secant {V : Type*} [DecidableEq V] (K : Finset V)
    (f : V → Fin 2 → ℝ) (ε : ℝ) (hm : 1 < K.card)
    (hu : Set.InjOn (fun x => horizontal (f x)) (K : Set V))
    (hs : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ K,
      horizontal (f x) < horizontal (f y) → horizontal (f y) < horizontal (f z) →
      ε * slope (f y) (f z) < ε * slope (f x) (f y))
    (x : V) (hx : x ∈ K) :
    ∃ y ∈ K, y ≠ x ∧
      ∀ z ∈ K.erase x,
        slopeFunctional ε (ε * slope (f x) (f y)) (f z) ≤
          slopeFunctional ε (ε * slope (f x) (f y)) (f x) ∧
        (slopeFunctional ε (ε * slope (f x) (f y)) (f z) =
          slopeFunctional ε (ε * slope (f x) (f y)) (f x) → z = y) := by
  let u (z : V) := horizontal (f z)
  let R := K.filter (fun z => u x < u z)
  let A := K.filter (fun z => u z < u x)
  let w (y z : V) := ε * slope (f y) (f z)
  have wcomm (y z : V) : w y z = w z y := by simp only [w, slope_symm (f y) (f z)]
  have hune (y : V) (hy : y ∈ K) (hne : y ≠ x) : u y ≠ u x :=
    fun h => hne (hu hy hx h)
  have slope_inj (y z : V) (hy : y ∈ K) (hz : z ∈ K)
      (hxy : u x ≠ u y) (hxz : u x ≠ u z) (he : w x y = w x z) : y = z := by
    by_contra hne
    have hyz : u y ≠ u z := fun h => hne (hu hy hz h)
    have avg {p q r : V} (hpq : u p < u q) (hqr : u q < u r) :
        (u r - u p) * w p r = (u q - u p) * w p q + (u r - u q) * w q r := by
      linear_combination ε * slope_average (p := f p) (q := f q) (r := f r) hpq hqr
    rcases lt_or_gt_of_ne hxy with hxyL | hxyR <;>
      rcases lt_or_gt_of_ne hxz with hxzL | hxzR
    · rcases lt_or_gt_of_ne hyz with hyzL | hyzR
      · have hh := avg hxyL hyzL
        have hlt := hs x hx y hy z hz hxyL hyzL
        rw [← he] at hh
        have hp := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hyzL)
        nlinarith only [hh, hp]
      · have hh := avg hxzL hyzR
        have hlt := hs x hx z hz y hy hxzL hyzR
        rw [he] at hh
        have hp := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hyzR)
        nlinarith only [hh, hp]
    · have hlt := hs z hz x hx y hy hxzR hxyL
      change w x y < w z x at hlt
      rw [wcomm z x, he] at hlt
      exact (lt_irrefl _ hlt)
    · have hlt := hs y hy x hx z hz hxyR hxzL
      change w x z < w y x at hlt
      rw [wcomm y x, he] at hlt
      exact (lt_irrefl _ hlt)
    · rcases lt_or_gt_of_ne hyz with hyzL | hyzR
      · have hh := avg hyzL hxzR
        have hlt : w z x < w y z := hs y hy z hz x hx hyzL hxzR
        rw [wcomm z x] at hlt
        rw [wcomm y x, wcomm z x, he] at hh
        have hp := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hyzL)
        nlinarith only [hh, hp]
      · have hh := avg hyzR hxyR
        have hlt : w y x < w z y := hs z hz y hy x hx hyzR hxyR
        rw [wcomm y x, he] at hlt
        rw [wcomm z x, wcomm y x, he] at hh
        have hp := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hyzR)
        nlinarith only [hh, hp]
  by_cases hR : R.Nonempty
  · obtain ⟨y, hyR, hymax⟩ := R.exists_max_image (w x) hR
    obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hyR
    refine ⟨y, hy, fun e => (lt_irrefl _ (e ▸ hxy)), fun z hz => ?_⟩
    obtain ⟨hzne, hzK⟩ := Finset.mem_erase.mp hz
    rcases lt_or_gt_of_ne (hune z hzK hzne) with hzx | hxz
    · have hs' : w x y < w z x := hs z hzK x hx y hy hzx hxy
      have hc := (secant_comparison (p := f z) (q := f x) hzx ε (w x y)).2
      refine ⟨hc.2 hs'.le, fun he => ?_⟩
      have hb := (secant_comparison (p := f z) (q := f x) hzx ε (w x y)).1
      exact ((not_le_of_gt hs') (hb.1 he.symm.le)).elim
    · have hs' := hymax z (Finset.mem_filter.mpr ⟨hzK, hxz⟩)
      have hc := secant_comparison (p := f x) (q := f z) hxz ε (w x y)
      exact ⟨hc.1.2 hs', fun he => slope_inj z y hzK hy hxz.ne hxy.ne
        (le_antisymm hs' (hc.2.1 he.symm.le))⟩
  · obtain ⟨y₀, hy₀, hne⟩ := Finset.exists_mem_ne hm x
    have hy₀A : y₀ ∈ A := by
      rcases lt_or_gt_of_ne (hune y₀ hy₀ hne) with hlt | hlt
      · exact Finset.mem_filter.mpr ⟨hy₀, hlt⟩
      · exact (hR ⟨y₀, Finset.mem_filter.mpr ⟨hy₀, hlt⟩⟩).elim
    obtain ⟨y, hyA, hymin⟩ := A.exists_min_image (fun z => w z x) ⟨_, hy₀A⟩
    obtain ⟨hy, hyx⟩ := Finset.mem_filter.mp hyA
    refine ⟨y, hy, fun e => (lt_irrefl _ (e ▸ hyx)), fun z hz => ?_⟩
    obtain ⟨hzne, hzK⟩ := Finset.mem_erase.mp hz
    rcases lt_or_gt_of_ne (hune z hzK hzne) with hzx | hxz
    · have hs' := hymin z (Finset.mem_filter.mpr ⟨hzK, hzx⟩)
      rw [wcomm y x] at hs'
      have hc := secant_comparison (p := f z) (q := f x) hzx ε (w x y)
      refine ⟨hc.2.2 hs', fun he => ?_⟩
      apply slope_inj z y hzK hy hzx.ne.symm hyx.ne.symm
      rw [wcomm x z]
      exact le_antisymm (hc.1.1 he.symm.le) hs'
    · exact (hR ⟨z, Finset.mem_filter.mpr ⟨hzK, hxz⟩⟩).elim

end OMA.Erdos651Planar

namespace OMA.Erdos651Planar

variable {V : Type} [DecidableEq V]

/-- General position for pairs gives injectivity on the given index set. -/
theorem injOn_of_general_position (S : Finset V) (f : V → Fin 2 → ℝ)
    (hgen : ∀ Z ⊆ S, Z.card ≤ 3 → AffineIndependent ℝ (fun z : ↥(Z : Set V) => f z)) :
    Set.InjOn f (↑S : Set V) := by
  intro p hp q hq he
  let Z : Finset V := {p,q}
  have hZ : Z ⊆ S := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hq
  have hZc : Z.card ≤ 3 :=
    (Finset.card_insert_le p {q}).trans (by simp)
  have h := (hgen Z hZ hZc).injective
  exact congrArg Subtype.val (h (a₁ := ⟨p,by simp [Z]⟩) (a₂ := ⟨q,by simp [Z]⟩) he)

/-- General position for triples rules out coincident slopes of successive secants. -/
theorem slope_ne_of_general_position (S : Finset V) (f : V → Fin 2 → ℝ)
    (hgen : ∀ Z ⊆ S, Z.card ≤ 3 → AffineIndependent ℝ (fun z : ↥(Z : Set V) => f z))
    {p q r : V} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S)
    (hpq : horizontal (f p) < horizontal (f q))
    (hqr : horizontal (f q) < horizontal (f r)) :
    slope (f p) (f q) ≠ slope (f q) (f r) := by
  intro he
  let Z : Finset V := {p,q,r}
  have hZ : Z ⊆ S := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hZc : Z.card ≤ 3 := by
    have hp' := Finset.card_insert_le p ({q,r} : Finset V)
    have hq' := Finset.card_insert_le q ({r} : Finset V)
    simp only [Finset.card_singleton] at hq'
    change ({p,q,r} : Finset V).card ≤ 3
    omega
  let P : ↥(Z : Set V) := ⟨p,by simp [Z]⟩
  let Q : ↥(Z : Set V) := ⟨q,by simp [Z]⟩
  let R : ↥(Z : Set V) := ⟨r,by simp [Z]⟩
  have hQP : Q ≠ P := fun h => hpq.ne' (congrArg (horizontal ∘ f ∘ Subtype.val) h)
  have hQR : Q ≠ R := fun h => hqr.ne (congrArg (horizontal ∘ f ∘ Subtype.val) h)
  let t := (horizontal (f q) - horizontal (f p)) / (horizontal (f r) - horizontal (f p))
  have hu : t * (horizontal (f r) - horizontal (f p)) = horizontal (f q) - horizontal (f p) :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr (hpq.trans hqr).ne')
  have hv₁ : (horizontal (f q) - horizontal (f p)) * slope (f p) (f q) =
      vertical (f q) - vertical (f p) := mul_div_cancel₀ _ (sub_ne_zero.mpr hpq.ne')
  have hv₂ : (horizontal (f r) - horizontal (f q)) * slope (f p) (f q) =
      vertical (f r) - vertical (f q) := by
    rw [he]
    exact mul_div_cancel₀ _ (sub_ne_zero.mpr hqr.ne')
  have hv₃ : (horizontal (f r) - horizontal (f p)) * slope (f p) (f q) =
      vertical (f r) - vertical (f p) := by linear_combination hv₁ + hv₂
  have hv : t * (vertical (f r) - vertical (f p)) = vertical (f q) - vertical (f p) := by
    rw [← hv₃, ← mul_assoc, hu, hv₁]
  have hmid : f q = AffineMap.lineMap (f p) (f r) t := by
    rw [AffineMap.lineMap_apply_module]
    funext i
    unfold horizontal at hu
    unfold vertical at hv
    fin_cases i
    · change f q 0 = (1-t) * f p 0 + t * f r 0
      linarith only [hu,hv]
    · change f q 1 = (1-t) * f p 1 + t * f r 1
      linarith only [hu,hv]
  let g : ↥(Z : Set V) → (Fin 2 → ℝ) := fun z => f z
  have hgm : f q ∈ affineSpan ℝ (g '' ({P,R} : Set ↥(Z : Set V))) := by
    rw [hmid]
    apply AffineMap.lineMap_mem
    · exact subset_affineSpan ℝ _ ⟨P,by simp,rfl⟩
    · exact subset_affineSpan ℝ _ ⟨R,by simp,rfl⟩
  have hm := ((hgen Z hZ hZc).mem_affineSpan_iff Q {P,R}).mp hgm
  simp [hQP,hQR] at hm

end OMA.Erdos651Planar

/- Convert adjacent slope inequalities to inequalities for every ordered triple. -/

namespace OMA.Erdos651Planar

open OMA.Erdos651CupsCaps

variable {V : Type} (f : V → Fin 2 → ℝ) (ε : ℝ)

private theorem signed_between {p q r : V}
    (hpq : horizontal (f p) < horizontal (f q)) (hqr : horizontal (f q) < horizontal (f r))
    (h : ε * slope (f q) (f r) < ε * slope (f p) (f q)) :
    ε * slope (f q) (f r) < ε * slope (f p) (f r) ∧
      ε * slope (f p) (f r) < ε * slope (f p) (f q) := by
  have he : (horizontal (f r) - horizontal (f p)) * (ε * slope (f p) (f r)) =
      (horizontal (f q) - horizontal (f p)) * (ε * slope (f p) (f q)) +
        (horizontal (f r) - horizontal (f q)) * (ε * slope (f q) (f r)) := by
    linear_combination ε * slope_average hpq hqr
  have ha := mul_lt_mul_of_pos_left h (sub_pos.mpr hqr)
  have hb := mul_lt_mul_of_pos_left h (sub_pos.mpr hpq)
  constructor
  · by_contra! hbad
    have hc := mul_le_mul_of_nonneg_left hbad (sub_nonneg.mpr (hpq.trans hqr).le)
    nlinarith only [he, hb, hc]
  · by_contra! hbad
    have hc := mul_le_mul_of_nonneg_left hbad (sub_nonneg.mpr (hpq.trans hqr).le)
    nlinarith only [he, ha, hc]

private theorem score_next (L : List V) (x y : V)
    (hOrd : (x :: y :: L).Pairwise (fun p q => horizontal (f p) < horizontal (f q)))
    (hTrip : tripChain (fun p q r => ε * slope (f q) (f r) < ε * slope (f p) (f q))
      (x :: y :: L)) :
    ∀ z ∈ L, ε * slope (f y) (f z) < ε * slope (f x) (f y) := by
  induction L generalizing x y with
  | nil => simp
  | cons w L ih =>
    intro z hz
    have ht := List.pairwise_cons.mp hOrd
    have hu := List.pairwise_cons.mp ht.2
    have hw := List.pairwise_cons.mp hu.2
    have hyp := hTrip.1
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hyp
    · have hz' := ih y w ht.2 hTrip.2 z hz
      exact (signed_between f ε (hu.1 _ List.mem_cons_self) (hw.1 _ hz) hz').2.trans hyp

theorem all_triples_of_chain (L : List V)
    (hOrd : L.Pairwise (fun p q => horizontal (f p) < horizontal (f q)))
    (hTrip : tripChain (fun p q r => ε * slope (f q) (f r) < ε * slope (f p) (f q)) L) :
    ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
      horizontal (f x) < horizontal (f y) → horizontal (f y) < horizontal (f z) →
      ε * slope (f y) (f z) < ε * slope (f x) (f y) := by
  induction L with
  | nil => simp
  | cons v L ih =>
    intro x hx y hy z hz hxy hyz
    have hord := List.pairwise_cons.mp hOrd
    have inner : tripChain (fun p q r => ε * slope (f q) (f r) < ε * slope (f p) (f q)) L := by
      rcases L with _ | ⟨p, _ | ⟨q, L⟩⟩
      · trivial
      · trivial
      · exact hTrip.2
    have hyL : y ∈ L := by
      rcases List.mem_cons.mp hy with rfl | hyL
      · rcases List.mem_cons.mp hx with rfl | hxL
        · exact (lt_irrefl _ hxy).elim
        · exact ((not_lt_of_gt (hord.1 _ hxL)) hxy).elim
      · exact hyL
    have hzL : z ∈ L := by
      rcases List.mem_cons.mp hz with rfl | hzL
      · exact ((not_lt_of_gt (hord.1 _ hyL)) hyz).elim
      · exact hzL
    rcases List.mem_cons.mp hx with rfl | hxL
    · rcases L with _ | ⟨w, L⟩
      · simp at hyL
      have hw := List.pairwise_cons.mp hord.2
      have hzTail : z ∈ L := by
        rcases List.mem_cons.mp hzL with rfl | hzT
        · rcases List.mem_cons.mp hyL with rfl | hyT
          · exact (lt_irrefl _ hyz).elim
          · exact ((not_lt_of_gt (hw.1 _ hyT)) hyz).elim
        · exact hzT
      rcases List.mem_cons.mp hyL with rfl | hyTail
      · exact score_next f ε L x y hOrd hTrip z hzTail
      · have hwy := hw.1 _ hyTail
        have hxw := hord.1 w List.mem_cons_self
        have hleft := score_next f ε L x w hOrd hTrip y hyTail
        have hright := ih hord.2 inner w List.mem_cons_self y hyL z hzL hwy hyz
        exact hright.trans (signed_between f ε hxw hwy hleft).1
    · exact ih hord.2 inner x hxL y hyL z hzL hxy hyz

end OMA.Erdos651Planar

/- Complete planar cups-versus-caps witness transport. -/

namespace OMA.Erdos651Planar

open OMA.Erdos651CupsCaps

variable {V : Type}

private theorem cup_to_signed (f : V → Fin 2 → ℝ) (S : Finset V)
    (hNe : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, horizontal (f x) < horizontal (f y) →
      horizontal (f y) < horizontal (f z) → slope (f y) (f z) ≠ slope (f x) (f y))
    (L : List V) (hm : ∀ x ∈ L, x ∈ S)
    (hord : L.Pairwise (fun x y => horizontal (f x) < horizontal (f y)))
    (h : tripChain (fun x y z => ¬(1 * slope (f y) (f z) < 1 * slope (f x) (f y))) L) :
    tripChain (fun x y z => (-1) * slope (f y) (f z) < (-1) * slope (f x) (f y)) L := by
  induction L with
  | nil => trivial
  | cons x L ih =>
    rcases L with _ | ⟨y, _ | ⟨z, L⟩⟩
    · trivial
    · trivial
    have hs := List.pairwise_cons.mp hord
    have hx := hm x List.mem_cons_self
    have hy := hm y (by simp)
    have hz := hm z (by simp)
    have hxy := hs.1 y List.mem_cons_self
    have hyz := (List.pairwise_cons.mp hs.2).1 z List.mem_cons_self
    have hNo := hNe x hx y hy z hz hxy hyz
    have hstep := (not_lt.mp (by simpa only [one_mul] using h.1 :
      ¬slope (f y) (f z) < slope (f x) (f y))).lt_of_ne hNo.symm
    change (-1 : ℝ) * slope (f y) (f z) < (-1) * slope (f x) (f y) ∧ _
    exact ⟨by linarith, ih (fun p hp => hm p (List.mem_cons_of_mem _ hp)) hs.2 h.2⟩

variable [DecidableEq V]

private theorem chain_finset (f : V → Fin 2 → ℝ) (S : Finset V) (ε : ℝ) (k : ℕ)
    (L : List V) (hl : L.length = k) (hlin : ∀ x ∈ L, x ∈ S)
    (hord : L.Pairwise (fun p q => horizontal (f p) < horizontal (f q)))
    (htrip : tripChain (fun p q r => ε * slope (f q) (f r) < ε * slope (f p) (f q)) L) :
    ∃ K ⊆ S, K.card = k ∧
      ∀ p ∈ K, ∀ q ∈ K, ∀ r ∈ K,
        horizontal (f p) < horizontal (f q) → horizontal (f q) < horizontal (f r) →
          ε * slope (f q) (f r) < ε * slope (f p) (f q) := by
  have hnd : L.Nodup := by
    change List.Pairwise (fun x y => x ≠ y) L
    apply hord.imp
    intro x y h he
    subst y
    exact (lt_irrefl _ h)
  refine ⟨L.toFinset, ?_, (List.toFinset_card_of_nodup hnd).trans hl, ?_⟩
  · intro x hx
    exact hlin x (List.mem_toFinset.mp hx)
  · intro p hp q hq r hr hpq hqr
    exact all_triples_of_chain f ε L hord htrip p (List.mem_toFinset.mp hp)
      q (List.mem_toFinset.mp hq) r (List.mem_toFinset.mp hr) hpq hqr

theorem planar_from_general_position_interfaces
    (hInjGP : ∀ (V : Type) [DecidableEq V] (S : Finset V) (f : V → Fin 2 → ℝ),
      (∀ Z ⊆ S, Z.card ≤ 3 → AffineIndependent ℝ (fun z : ↥(Z : Set V) => f z)) →
      Set.InjOn f (S : Set V))
    (hSlopeGP : ∀ (V : Type) [DecidableEq V] (S : Finset V) (f : V → Fin 2 → ℝ),
      (∀ Z ⊆ S, Z.card ≤ 3 → AffineIndependent ℝ (fun z : ↥(Z : Set V) => f z)) →
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, horizontal (f x) < horizontal (f y) →
        horizontal (f y) < horizontal (f z) → slope (f y) (f z) ≠ slope (f x) (f y)) :
    OMA.R_Erdos651_erdos_651_R1_H1_R1_H2_R1.H2 := by
  classical
  intro V inst S f a n hGen hFree ha hn hCard
  let u (x : V) := horizontal (f x)
  have hf := hInjGP V S f hGen
  have hu : Set.InjOn u (S : Set V) := by
    intro x hx y hy huEq
    by_contra hxy
    have hfNe := fun h => hxy (hf hx hy h)
    exact horizontal_ne_of_line_free hfNe (hFree x hx y hy hxy) huEq
  have hc : ((a - 2) + (n - 2)).choose (a - 2) < S.card := by
    rw [show a - 2 + (n - 2) = n + a - 4 by omega]
    omega
  obtain hCap | hCup := cups_or_caps u
    (fun x y z => (1 : ℝ) * slope (f y) (f z) < 1 * slope (f x) (f y))
    (a - 2) (n - 2) S hu hc
  · obtain ⟨L, hL, hLS, hOrd, hTrip⟩ := hCap
    obtain ⟨K, hKS, hK, hSlopes⟩ := chain_finset f S 1 a L (by omega) hLS hOrd hTrip
    right
    refine ⟨K, hKS, hK, fun x hx => ?_⟩
    have hsmall : 1 < K.card := by omega
    obtain ⟨y, hy, hxy, hsup⟩ := supporting_secant K f 1 hsmall (hu.mono hKS) hSlopes x hx
    let A := slopeFunctional 1 (1 * slope (f x) (f y))
    have huy : u x ≠ u y := fun h => hxy (hu (hKS hx) (hKS hy) h).symm
    have hval : 0 < A (f x) := by
      simpa [A, slopeFunctional] using secant_positive huy (hFree x (hKS hx) y (hKS hy) hxy.symm)
    apply support_excludes A _ _ (f y) (fun h => hxy (hf (hKS hx) (hKS hy) h).symm)
    intro q hq
    rcases hq with hquad | ⟨z, hz, rfl⟩
    · have hquad' : ∀ i : Fin 2, q i ≤ 0 := hquad
      have hneg : A q ≤ 0 := by
        rcases lt_or_gt_of_ne huy with hless | hgreater
        · simpa [A, slopeFunctional] using secant_nonpos_on_quadrant hless
            (hFree x (hKS hx) y (hKS hy) hxy.symm) hquad'
        · simpa [A, slopeFunctional, slope_symm (f x) (f y)] using secant_nonpos_on_quadrant hgreater
            (hFree y (hKS hy) x (hKS hx) hxy) hquad'
      exact ⟨hneg.trans hval.le, fun he => (not_le_of_gt hval (he ▸ hneg)).elim⟩
    · exact ⟨(hsup z hz).1, fun he => congrArg f ((hsup z hz).2 he)⟩
  · obtain ⟨L, hL, hLS, hOrd, hTrip⟩ := hCup
    have hSigned := cup_to_signed f S (hSlopeGP V S f hGen) L hLS hOrd hTrip
    obtain ⟨K, hKS, hK, hSlopes⟩ := chain_finset f S (-1) n L (by omega) hLS hOrd hSigned
    left
    refine ⟨K, hKS, hK, fun x hx => ?_⟩
    have hsmall : 1 < K.card := by omega
    obtain ⟨y, hy, hxy, hsup⟩ := supporting_secant K f (-1) hsmall (hu.mono hKS) hSlopes x hx
    let A := slopeFunctional (-1) ((-1) * slope (f x) (f y))
    apply support_excludes A _ _ (f y) (fun h => hxy (hf (hKS hx) (hKS hy) h).symm)
    rintro q ⟨z, hz, rfl⟩
    exact ⟨(hsup z hz).1, fun he => congrArg f ((hsup z hz).2 he)⟩

end OMA.Erdos651Planar

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1_H1_R1.H2 :=
  OMA.R_Erdos651_erdos_651_R1_H1_R1_H2_R1.main
    (fun _ _ R m hr ht hs hc => OMA.Erdos651Dilworth.three_preorders R m hr ht hs hc)
    (OMA.Erdos651Planar.planar_from_general_position_interfaces
        (fun _ _ S f hg => OMA.Erdos651Planar.injOn_of_general_position S f hg)
        (fun _ _ S f hg _ hx _ hy _ hz hxy hyz =>
          (OMA.Erdos651Planar.slope_ne_of_general_position S f hg hx hy hz hxy hyz).symm))
