import FormalConjectures.ErdosProblems.«949»
import Mathlib

-- Reduction Erdos949.erdos_949.R1 of Erdős Problem 949
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
What `main` proves, for a sum-free set `S ⊆ ℝ` (no solutions of `a + b = c` in `S`):

* Without loss of generality `S` is a maximal sum-free set: Zorn's lemma extends `S` to a maximal
  one, and a set `A` that works for the larger set works for `S`.
* Small pieces are easy. If `X` has size continuum, `X ∪ (X + X) ⊆ Y`, and `S` meets `Y` in
  fewer than continuum points, then Zorn's lemma gives a maximal `A ⊆ X` with `A` and `A + A`
  disjoint from `S`. Maximality puts `X` inside `T ∪ T / 2 ∪ A ∪ ⋃ a ∈ A, (T - a)` with
  `T = S ∩ Y`, so `A` has size continuum. (This is the counting of `erdos_949.variants.sidon`
  upstream.) With `X = (u, v / 2)` and `Y = (u, v)` this settles every `S` that has fewer than
  continuum points in some interval `(u, v)` with `0 ≤ u` and `2 u < v`, or in its mirror image
  `(-v, -u)`. This covers bounded `S`, `S` of size below continuum, `S` missing a neighbourhood
  of one side of `0`, and `S` with a small tail.
* Steinhaus. If `S` is Lebesgue measurable with positive measure, then `S - S` contains an
  interval `(-δ, δ)`, and a point `y ∈ S` with `|y| < δ` would give `x + y = z` in `S`. So `S`
  misses `(0, δ)`, which the previous item already settles.

What is left is a maximal sum-free set with continuum many points in every interval `(u, v)` and
`(-v, -u)` with `0 ≤ u`, `2 u < v`, which is Lebesgue null (H1) or not Lebesgue measurable (H2).
-/

namespace OMA.R_Erdos949_erdos_949_R1

open Cardinal
open scoped Pointwise

/-- Erdős 949 for a maximal sum-free set of Lebesgue measure zero that has continuum many points
in every interval `(u, v)` and `(-v, -u)` with `0 ≤ u` and `2 u < v`. -/
def H1 : Prop :=
  ∀ S : Set ℝ, Maximal (fun T : Set ℝ => ∀ a ∈ T, ∀ b ∈ T, a + b ∉ T) S →
    MeasureTheory.volume S = 0 →
    (∀ u v : ℝ, 0 ≤ u → 2 * u < v → #(S ∩ Set.Ioo u v : Set ℝ) = 𝔠) →
    (∀ u v : ℝ, 0 ≤ u → 2 * u < v → #(S ∩ Set.Ioo (-v) (-u) : Set ℝ) = 𝔠) →
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ

/-- Erdős 949 for a maximal sum-free set that is not Lebesgue measurable and has continuum many
points in every interval `(u, v)` and `(-v, -u)` with `0 ≤ u` and `2 u < v`. -/
def H2 : Prop :=
  ∀ S : Set ℝ, Maximal (fun T : Set ℝ => ∀ a ∈ T, ∀ b ∈ T, a + b ∉ T) S →
    ¬ MeasureTheory.NullMeasurableSet S MeasureTheory.volume →
    (∀ u v : ℝ, 0 ≤ u → 2 * u < v → #(S ∩ Set.Ioo u v : Set ℝ) = 𝔠) →
    (∀ u v : ℝ, 0 ≤ u → 2 * u < v → #(S ∩ Set.Ioo (-v) (-u) : Set ℝ) = 𝔠) →
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ

/-- Every sum-free set of reals lies in a maximal sum-free set (Zorn). -/
lemma exists_maximal_sumFree (S : Set ℝ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ M, S ⊆ M ∧ Maximal (fun T : Set ℝ => ∀ a ∈ T, ∀ b ∈ T, a + b ∉ T) M := by
  have hch : ∀ C ⊆ {T : Set ℝ | ∀ a ∈ T, ∀ b ∈ T, a + b ∉ T},
      IsChain (fun x1 x2 => x1 ⊆ x2) C → C.Nonempty →
      ∃ ub ∈ {T : Set ℝ | ∀ a ∈ T, ∀ b ∈ T, a + b ∉ T}, ∀ s ∈ C, s ⊆ ub := by
    intro C hC hchain _
    refine ⟨⋃₀ C, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro a ha b hb hab
    obtain ⟨Ta, hTa, haT⟩ := Set.mem_sUnion.mp ha
    obtain ⟨Tb, hTb, hbT⟩ := Set.mem_sUnion.mp hb
    obtain ⟨Tc, hTc, hcT⟩ := Set.mem_sUnion.mp hab
    obtain ⟨D, hD, hTaD, hTbD⟩ := hchain.directedOn Ta hTa Tb hTb
    obtain ⟨E, hE, hDE, hTcE⟩ := hchain.directedOn D hD Tc hTc
    exact hC hE a (hDE (hTaD haT)) b (hDE (hTbD hbT)) (hTcE hcT)
  obtain ⟨M, hSM, hM⟩ :=
    zorn_subset_nonempty {T : Set ℝ | ∀ a ∈ T, ∀ b ∈ T, a + b ∉ T} hch S hS
  exact ⟨M, hSM, hM⟩

/-- If `X` has size continuum, `X ∪ (X + X) ⊆ Y`, and `S` meets `Y` in fewer than continuum
points, then some `A ⊆ X` of size continuum avoids `S`, and so does `A + A`. -/
lemma exists_big_of_small (S X Y : Set ℝ) (hX : #X = 𝔠) (hXY : X ⊆ Y)
    (hXX : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ Y) (hS : #(S ∩ Y : Set ℝ) < 𝔠) :
    ∃ A ⊆ X, #A = 𝔠 ∧ (∀ x ∈ A, x ∉ S) ∧ ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S := by
  set T := S ∩ Y with hT
  have hch : ∀ C ⊆ {B : Set ℝ | B ⊆ X ∧ (∀ x ∈ B, x ∉ T) ∧ ∀ x ∈ B, ∀ y ∈ B, x + y ∉ T},
      IsChain (fun x1 x2 => x1 ⊆ x2) C →
      ∃ ub ∈ {B : Set ℝ | B ⊆ X ∧ (∀ x ∈ B, x ∉ T) ∧ ∀ x ∈ B, ∀ y ∈ B, x + y ∉ T},
        ∀ s ∈ C, s ⊆ ub := by
    intro C hC hchain
    refine ⟨⋃₀ C, ⟨?_, ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hx
      exact (hC hB).1 hxB
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hx
      exact (hC hB).2.1 x hxB
    · intro x hx y hy
      obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hx
      obtain ⟨B', hB', hyB'⟩ := Set.mem_sUnion.mp hy
      obtain ⟨D, hD, hBD, hB'D⟩ := hchain.directedOn B hB B' hB'
      exact (hC hD).2.2 x (hBD hxB) y (hB'D hyB')
  obtain ⟨A, ⟨hAX, hAT, hAA⟩, hmax⟩ := zorn_subset _ hch
  -- By maximality every point of `X` is in `T`, in `T / 2`, in `A`, or in some `T - a`.
  have hcover : X ⊆ T ∪ (fun z => z / 2) '' T ∪ A ∪ ⋃ a ∈ A, (fun z => z - a) '' T := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Or.inl (Or.inl (Or.inl hxT))
    by_cases hx2 : x + x ∈ T
    · exact Or.inl (Or.inl (Or.inr ⟨x + x, hx2, by ring⟩))
    by_cases hxA : x ∈ A
    · exact Or.inl (Or.inr hxA)
    right
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and] at hno
    have hadm : insert x A ∈
        {B : Set ℝ | B ⊆ X ∧ (∀ x ∈ B, x ∉ T) ∧ ∀ x ∈ B, ∀ y ∈ B, x + y ∉ T} := by
      refine ⟨Set.insert_subset hx hAX, ?_, ?_⟩
      · intro z hz
        rcases hz with hz | hz
        · rw [hz]
          exact hxT
        · exact hAT z hz
      · intro z hz w hw
        rcases hz with hz | hz <;> rcases hw with hw | hw
        · rw [hz, hw]
          exact hx2
        · rw [hz]
          intro h
          exact hno w hw (x + w) h (by ring)
        · rw [hw]
          intro h
          exact hno z hz (z + x) h (by ring)
        · exact hAA z hz w hw
    exact hxA (hmax hadm (Set.subset_insert x A) (Set.mem_insert x A))
  refine ⟨A, hAX, ?_, ?_, ?_⟩
  · apply le_antisymm
    · calc #A ≤ #X := Cardinal.mk_le_mk_of_subset hAX
        _ = 𝔠 := hX
    · by_contra hlt
      push Not at hlt
      have hc := Cardinal.aleph0_le_continuum
      have h1 : #(T ∪ (fun z => z / 2) '' T ∪ A ∪ ⋃ a ∈ A, (fun z => z - a) '' T : Set ℝ) ≤
          #T + #T + #A + #A * #T := by
        refine (Cardinal.mk_union_le _ _).trans ?_
        refine add_le_add ((Cardinal.mk_union_le _ _).trans
          (add_le_add ((Cardinal.mk_union_le _ _).trans (add_le_add le_rfl Cardinal.mk_image_le))
            le_rfl)) ?_
        refine (Cardinal.mk_biUnion_le _ _).trans ?_
        exact mul_le_mul' le_rfl (ciSup_le' fun a => Cardinal.mk_image_le)
      have h2 : #T + #T + #A + #A * #T < 𝔠 :=
        add_lt_of_lt hc (add_lt_of_lt hc (add_lt_of_lt hc hS hS) hlt) (mul_lt_of_lt hc hlt hS)
      have h3 : #X < 𝔠 := lt_of_le_of_lt ((Cardinal.mk_le_mk_of_subset hcover).trans h1) h2
      rw [hX] at h3
      exact lt_irrefl _ h3
  · intro x hx hxS
    exact hAT x hx ⟨hxS, hXY (hAX hx)⟩
  · intro x hx y hy hxyS
    exact hAA x hx y hy ⟨hxyS, hXX x (hAX hx) y (hAX hy)⟩

/-- Steinhaus: a sum-free set of positive Lebesgue measure stays a fixed distance away from 0.
If `t ⊆ S` is measurable with the same measure, `t - t` contains `(-δ, δ)`, and `y = z - x`
with `x, z ∈ S` would give `x + y = z`. -/
lemma steinhaus_gap (S : Set ℝ) (hsf : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S)
    (hm : MeasureTheory.NullMeasurableSet S MeasureTheory.volume)
    (hpos : MeasureTheory.volume S ≠ 0) :
    ∃ δ > 0, ∀ y ∈ S, δ ≤ |y| := by
  obtain ⟨t, hts, htm, hteq⟩ := hm.exists_measurable_subset_ae_eq
  have htpos : 0 < MeasureTheory.volume t := by
    rw [MeasureTheory.measure_congr hteq]
    exact pos_iff_ne_zero.mpr hpos
  have hnhds :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos MeasureTheory.volume t htm htpos
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, fun y hy => ?_⟩
  by_contra hlt
  push Not at hlt
  have hyb : y ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hlt
  obtain ⟨z, hz, x, hx, hzx⟩ := Set.mem_sub.mp (hball hyb)
  apply hsf x (hts hx) y hy
  have hxy : x + y = z := by linarith
  rw [hxy]
  exact hts hz

theorem main : H1 → H2 → type_of% @Erdos949.erdos_949 := by
  intro h1 h2 S hS
  obtain ⟨M, hSM, hM⟩ := exists_maximal_sumFree S hS
  suffices hsuff : ∃ A ⊆ Mᶜ, #A = 𝔠 ∧ A + A ⊆ Mᶜ by
    obtain ⟨A, hA, hcard, hAA⟩ := hsuff
    exact ⟨A, hA.trans (Set.compl_subset_compl.mpr hSM), hcard,
      hAA.trans (Set.compl_subset_compl.mpr hSM)⟩
  have hMsf : ∀ a ∈ M, ∀ b ∈ M, a + b ∉ M := hM.prop
  have fin : ∀ X Y : Set ℝ, #X = 𝔠 → X ⊆ Y → (∀ x ∈ X, ∀ y ∈ X, x + y ∈ Y) →
      #(M ∩ Y : Set ℝ) < 𝔠 → ∃ A ⊆ Mᶜ, #A = 𝔠 ∧ A + A ⊆ Mᶜ := by
    intro X Y hX hXY hXX hY
    obtain ⟨A, -, hcard, hA1, hA2⟩ := exists_big_of_small M X Y hX hXY hXX hY
    exact ⟨A, fun x hx => hA1 x hx, hcard,
      Set.add_subset_iff.mpr fun x hx y hy => hA2 x hx y hy⟩
  have small : ∀ Y : Set ℝ, #(M ∩ Y : Set ℝ) ≠ 𝔠 → #(M ∩ Y : Set ℝ) < 𝔠 := fun Y h =>
    lt_of_le_of_ne ((Cardinal.mk_set_le _).trans_eq Cardinal.mk_real) h
  -- an interval `(u, v)` with `0 ≤ u` and `2 u < v` that holds few points of `M`
  by_cases hpos : ∀ u v : ℝ, 0 ≤ u → 2 * u < v → #(M ∩ Set.Ioo u v : Set ℝ) = 𝔠
  swap
  · push Not at hpos
    obtain ⟨u, v, hu, huv, hc⟩ := hpos
    refine fin (Set.Ioo u (v / 2)) (Set.Ioo u v) (Cardinal.mk_Ioo_real (by linarith)) ?_ ?_
      (small _ hc)
    · intro x hx
      simp only [Set.mem_Ioo] at hx ⊢
      constructor <;> linarith
    · intro x hx y hy
      simp only [Set.mem_Ioo] at hx hy ⊢
      constructor <;> linarith
  -- the mirror image `(-v, -u)`
  by_cases hneg : ∀ u v : ℝ, 0 ≤ u → 2 * u < v → #(M ∩ Set.Ioo (-v) (-u) : Set ℝ) = 𝔠
  swap
  · push Not at hneg
    obtain ⟨u, v, hu, huv, hc⟩ := hneg
    refine fin (Set.Ioo (-(v / 2)) (-u)) (Set.Ioo (-v) (-u)) (Cardinal.mk_Ioo_real (by linarith))
      ?_ ?_ (small _ hc)
    · intro x hx
      simp only [Set.mem_Ioo] at hx ⊢
      constructor <;> linarith
    · intro x hx y hy
      simp only [Set.mem_Ioo] at hx hy ⊢
      constructor <;> linarith
  -- the remaining sets: null, of positive measure (impossible by Steinhaus), or non-measurable
  by_cases hnull : MeasureTheory.volume M = 0
  · exact h1 M hM hnull hpos hneg
  by_cases hmeas : MeasureTheory.NullMeasurableSet M MeasureTheory.volume
  · exfalso
    obtain ⟨δ, hδ, hgap⟩ := steinhaus_gap M hMsf hmeas hnull
    have h0 : (M ∩ Set.Ioo 0 δ : Set ℝ) = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hy1 hy2
      have := hgap y hy
      rw [abs_of_pos hy1] at this
      linarith
    have h0c := hpos 0 δ le_rfl (by linarith)
    rw [h0, Cardinal.mk_eq_zero] at h0c
    exact Cardinal.continuum_pos.ne h0c
  · exact h2 M hM hmeas hpos hneg

end OMA.R_Erdos949_erdos_949_R1
