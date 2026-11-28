import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1
import Mathlib

/-! Select mutually containing line-free orthants from the ordered triples. -/

open scoped Affine EuclideanGeometry

namespace OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1

/-- Reserve the two ends and one separating index on each side of a retained
index. In either monochromatic alternative, these choices place every other
retained index in the allowed ranges of its triple. -/
private theorem choose_spaced_triples {t k : ℕ} (f : Fin (2 * t + 3) → Fin k)
    (hf : StrictMono f) (C : Fin k → Fin k → Fin k → Bool) (color : Bool)
    (hm : ∀ i j l, i < j → j < l → C (f i) (f j) (f l) = color) :
    ∃ (a b c : Fin t → Fin k), Function.Injective b ∧
      (∀ i, a i < b i ∧ b i < c i) ∧
      (∀ i, C (a i) (b i) (c i) = color) ∧
      ∀ i j, i ≠ j →
        (if color then b j < a i ∨ b i < b j ∧ b j ≤ c i
         else a i ≤ b j ∧ b j < b i ∨ c i < b j) := by
  let mid (i : Fin t) : Fin (2 * t + 3) := ⟨2 * i.val + 2, by omega⟩
  let lo (i : Fin t) : Fin (2 * t + 3) := ⟨2 * i.val + 1, by omega⟩
  let hi (i : Fin t) : Fin (2 * t + 3) := ⟨2 * i.val + 3, by omega⟩
  let first : Fin (2 * t + 3) := ⟨0, by omega⟩
  let last : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
  have hmid : StrictMono mid := by
    intro i j hij
    change i.val < j.val at hij
    change 2 * i.val + 2 < 2 * j.val + 2
    omega
  have hml (i : Fin t) : lo i < mid i := by
    change 2 * i.val + 1 < 2 * i.val + 2
    omega
  have hmh (i : Fin t) : mid i < hi i := by
    change 2 * i.val + 2 < 2 * i.val + 3
    omega
  have hfirst (i : Fin t) : first < mid i := by
    change 0 < 2 * i.val + 2
    omega
  have hlast (i : Fin t) : mid i < last := by
    change 2 * i.val + 2 < 2 * t + 2
    omega
  cases color
  · refine ⟨fun _ => f first, f ∘ mid, fun i => f (hi i),
      (hf.comp hmid).injective, fun i => ⟨hf (hfirst i), hf (hmh i)⟩,
      fun i => hm first (mid i) (hi i) (hfirst i) (hmh i), ?_⟩
    intro i j hne
    simp only [Bool.false_eq_true, ↓reduceIte, Function.comp_apply]
    rcases lt_or_gt_of_ne hne with hij | hji
    · right
      apply hf
      change i.val < j.val at hij
      change 2 * i.val + 3 < 2 * j.val + 2
      omega
    · exact Or.inl ⟨(hf (hfirst j)).le, (hf.comp hmid) hji⟩
  · refine ⟨fun i => f (lo i), f ∘ mid, fun _ => f last,
      (hf.comp hmid).injective, fun i => ⟨hf (hml i), hf (hlast i)⟩,
      fun i => hm (lo i) (mid i) last (hml i) (hlast i), ?_⟩
    intro i j hne
    simp only [↓reduceIte, Function.comp_apply]
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact Or.inr ⟨(hf.comp hmid) hij, (hf (hlast j)).le⟩
    · left
      apply hf
      change j.val < i.val at hji
      change 2 * j.val + 2 < 2 * i.val + 1
      omega

/-- Ordered, two-color, three-uniform finite Ramsey theorem. -/
def H1 : Prop :=
  ∀ m : ℕ, ∃ k : ℕ, ∀ C : Fin k → Fin k → Fin k → Bool,
    ∃ (f : Fin m → Fin k) (color : Bool), StrictMono f ∧
      ∀ i j l, i < j → j < l → C (f i) (f j) (f l) = color

/-- The geometric cluster input before the monochromatic selection.
Each triple has one of the two separated line-free alternatives of §3. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ B : ℕ, ∀ X : Finset (ℝ^3), Erdos651.IsInGeneralPosition X → B ≤ X.card →
    ∃ (C : Fin k → Finset (ℝ^3)) (color : Fin k → Fin k → Fin k → Bool),
      (∀ i, C i ⊆ X) ∧ (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ a b c, a < b → b < c →
        ∃ (Y : Finset (ℝ^3)) (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)),
          Y ⊆ C b ∧ X.card ≤ Y.card ^ 4 ∧
          (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y →
            Disjoint (line[ℝ, x, y] : Set (ℝ^3)) {z | ∀ s : Fin 3, e z s ≤ 0}) ∧
          ∀ i, (if color a b c then i < a ∨ b < i ∧ i ≤ c
            else a ≤ i ∧ i < b ∨ c < i) →
            ∀ x ∈ C i, ∀ s : Fin 3, e x s < 0

/-- A strictly contained finite family remains inside a shrunk orthant
whose three coordinate projections are generic for the test set. -/
def H3 : Prop :=
  ∀ (Y U : Finset (ℝ^3)) (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)),
    Erdos651.IsInGeneralPosition Y → (∀ x ∈ U, ∀ s : Fin 3, e x s < 0) →
    ∃ f : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3),
      (∀ x ∈ U, ∀ s : Fin 3, f x s ≤ 0) ∧
      {x | ∀ s : Fin 3, f x s ≤ 0} ⊆ {x | ∀ s : Fin 3, e x s ≤ 0} ∧
      ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
        AffineIndependent ℝ
          (fun z : ↥(Z : Set (ℝ^3)) => fun s : Fin 2 => f z (j.succAbove s))

theorem main : H1 → H2 → H3 → OMA.R_Erdos651_erdos_651_R1_H1_R1.H1 := by
  classical
  intro hRamsey hSpatial hPerturb t _ht
  obtain ⟨k, hk⟩ := hRamsey (2 * t + 3)
  obtain ⟨B, hB⟩ := hSpatial k
  refine ⟨B, fun X hX hsize => ?_⟩
  obtain ⟨C, color, hCX, hDisj, hTriple⟩ := hB X hX hsize
  obtain ⟨f, d, hf, hm⟩ := hk color
  obtain ⟨a, b, c, hb, hOrder, bcolor, hRange⟩ :=
    choose_spaced_triples (t := t) f hf color d hm
  choose Y e hYC hSize hLine hInside using fun i => hTriple (a i) (b i) (c i)
    (hOrder i).1 (hOrder i).2
  let U (i : Fin t) := Finset.univ.biUnion (fun j => if j = i then ∅ else Y j)
  have hUY (i j : Fin t) (hji : j ≠ i) : Y j ⊆ U i := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simpa [hji] using hx⟩
  have hU (i : Fin t) : ∀ x ∈ U i, ∀ s : Fin 3, e i x s < 0 := by
    intro x hx s
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    by_cases heq : j = i
    · simp [heq] at hj
    have hY : x ∈ Y j := by simpa [heq] using hj
    have hr := hRange i j (Ne.symm heq)
    rw [← bcolor i] at hr
    exact hInside i (b j) hr x (hYC j hY) s
  have hYgen (i : Fin t) : Erdos651.IsInGeneralPosition (Y i) := by
    intro Z hZ hZc
    exact hX Z ((hZ.trans (hYC i)).trans (hCX (b i))) hZc
  choose g hgU hgSubset hgproj using fun i => hPerturb (Y i) (U i) (e i) (hYgen i) (hU i)
  refine ⟨Y, fun i => {x | ∀ s : Fin 3, g i x s ≤ 0}, ?_, ?_⟩
  · intro i
    refine ⟨(hYC i).trans (hCX (b i)), hSize i, ⟨g i, rfl, hgproj i⟩, ?_⟩
    intro x hx y hy hne
    exact (hLine i x hx y hy hne).mono Set.Subset.rfl (hgSubset i)
  · intro i j hne
    constructor
    · exact (hDisj (b i) (b j) (fun h => hne (hb h))).mono (hYC i) (hYC j)
    · intro x hx
      exact hgU i x (hUY i j hne.symm hx)

end OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1
