import OMAReductions.R_Erdos604_erdos_604_variants_katz_tardos_R1
import Mathlib

/-!
# Weak pinned bound: planar extraction and arithmetic obstruction

Reduction by my-other-github-account, following the proof of `OAI.WeakPinned.main`
in openai/math (Apache-2.0, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
`OAI/Geometry/PinnedDistances`). Copyright OpenAI 2026.

The source proof by contradiction has two independent halves.
* `H1` (arithmetic obstruction, source `arithmetic_sequence_impossible`): there is
  no sequence of finite fiber graphs whose fibers are level sets of the product
  `(Z₁ x - Z₁ y) * (Z₂ x - Z₂ y)` over number fields and which satisfy the
  prepared density, degree, large-fiber and heavy-subset bounds.
* `H2` (extraction, source `graph_sequence_of_failure`, `core_arithmetic_model`,
  `exists_pin_eventually`): a failure of the planar weak pinned bound yields such
  a sequence.
The image-count bridge is adapted from @marcusbuffett's reduction R1.
-/

namespace OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1_H1_R1
open Filter Finset
open scoped EuclideanGeometry

/-- No sequence of prepared arithmetic product-fiber graphs exists. -/
def H1 : Prop :=
  ∀ θ γ c : ℝ, 0 < θ → 0 < c → c < γ → γ < 1 →
  ∀ (V I K : ℕ → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)] [∀ j, Fintype (I j)]
    [∀ j, Field (K j)] [∀ j, NumberField (K j)]
    (s : ∀ j, I j → V j) (T : ∀ j, I j → Finset (V j)) (Z₁ Z₂ : ∀ j, V j → K j) (t : ∀ j, I j → K j),
  (∀ j e, s j e ∉ T j e) → (∀ j e f, e ≠ f → s j e = s j f → Disjoint (T j e) (T j f)) →
  (∀ j, Function.Injective (Z₁ j) ∧ Function.Injective (Z₂ j)) →
  (∀ j e y, y ∈ T j e → (Z₁ j (s j e) - Z₁ j y) * (Z₂ j (s j e) - Z₂ j y) = t j e) →
  ¬ ∀ j : ℕ, let n : ℝ := Fintype.card (V j); let η := θ / (j + 2);
    let h := fun D : Finset (V j) ↦ ∑ e, if 1 / Real.log n * (#(T j e) : ℝ) ≤ #(T j e ∩ D) ∧
      s j e ∈ D then (#(T j e ∩ D) : ℝ) else 0
    j < n ∧ 2 ≤ n ∧ (θ - η) * n * (n - 1) ≤ ∑ e, (#(T j e) : ℝ) ∧
    ∑ e, (#(T j e) : ℝ) ≤ (θ + η / 8) * n * (n - 1) ∧
    (∀ x, 2 * (θ - η) * (n - 1) ≤ (#{y | ∃ e, s j e = x ∧ y ∈ T j e} : ℝ) +
      #{y | ∃ e, s j e = y ∧ x ∈ T j e}) ∧ (∀ e, n ^ γ < #(T j e)) ∧
    (∀ D, h D ≤ (θ + η) * #D * (#D - 1)) ∧ ∀ D, (#D : ℝ) ≤ n ^ (1 - c) → h D ≤ η * #D * (#D - 1)

/-- A failure of the planar weak pinned bound yields a prepared arithmetic sequence. -/
def H2 : Prop :=
  (¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℝ², #P = n →
    ∃ x ∈ P, (n : ℝ) ^ (1 - ε) ≤ #((P.erase x).image (fun y ↦ dist y x))) →
  ∃ θ γ c : ℝ, 0 < θ ∧ 0 < c ∧ c < γ ∧ γ < 1 ∧
  ∃ (V I K : ℕ → Type) (_ : ∀ j, Fintype (V j)) (_ : ∀ j, DecidableEq (V j)) (_ : ∀ j, Fintype (I j))
    (_ : ∀ j, Field (K j)) (_ : ∀ j, NumberField (K j))
    (s : ∀ j, I j → V j) (T : ∀ j, I j → Finset (V j)) (Z₁ Z₂ : ∀ j, V j → K j) (t : ∀ j, I j → K j),
  (∀ j e, s j e ∉ T j e) ∧ (∀ j e f, e ≠ f → s j e = s j f → Disjoint (T j e) (T j f)) ∧
  (∀ j, Function.Injective (Z₁ j) ∧ Function.Injective (Z₂ j)) ∧
  (∀ j e y, y ∈ T j e → (Z₁ j (s j e) - Z₁ j y) * (Z₂ j (s j e) - Z₂ j y) = t j e) ∧
  ∀ j : ℕ, let n : ℝ := Fintype.card (V j); let η := θ / (j + 2);
    let h := fun D : Finset (V j) ↦ ∑ e, if 1 / Real.log n * (#(T j e) : ℝ) ≤ #(T j e ∩ D) ∧
      s j e ∈ D then (#(T j e ∩ D) : ℝ) else 0
    j < n ∧ 2 ≤ n ∧ (θ - η) * n * (n - 1) ≤ ∑ e, (#(T j e) : ℝ) ∧
    ∑ e, (#(T j e) : ℝ) ≤ (θ + η / 8) * n * (n - 1) ∧
    (∀ x, 2 * (θ - η) * (n - 1) ≤ (#{y | ∃ e, s j e = x ∧ y ∈ T j e} : ℝ) +
      #{y | ∃ e, s j e = y ∧ x ∈ T j e}) ∧ (∀ e, n ^ γ < #(T j e)) ∧
    (∀ D, h D ≤ (θ + η) * #D * (#D - 1)) ∧ ∀ D, (#D : ℝ) ≤ n ^ (1 - c) → h D ≤ η * #D * (#D - 1)

/-- Adapted from @marcusbuffett, reduction `Erdos604.erdos_604.variants.katz_tardos.R1`. -/
lemma image_count {α β γ : Type} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b ↔ g a = g b) : #(S.image f) = #(S.image g) := by
  classical
  have one {X Y : Type} [DecidableEq X] [DecidableEq Y] (u : α → X) (v : α → Y)
      (hle : ∀ a b, u a = u b → v a = v b) : #(S.image v) ≤ #(S.image u) := by
    by_cases hS : S.Nonempty
    · haveI : Nonempty α := ⟨hS.choose⟩
      have eq : S.image v = (S.image u).image (fun x ↦ v (Function.invFun u x)) := by
        rw [image_image]
        apply image_congr
        intro a _
        exact hle _ _ (Function.invFun_eq ⟨a, rfl⟩).symm
      rw [eq]
      exact card_image_le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  exact le_antisymm (one g f fun a b ↦ (h a b).mpr) (one f g fun a b ↦ (h a b).mp)

theorem main : H1 → H2 → OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1.H1 := by
  classical
  intro h1 h2
  have bound : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℝ², #P = n →
      ∃ x ∈ P, (n : ℝ) ^ (1 - ε) ≤ #((P.erase x).image (fun y ↦ dist y x)) := by
    by_contra hb
    obtain ⟨θ, γ, c, hθ, hc, hcγ, hγ, V, I, K, _, _, _, _, _, s, T, Z₁, Z₂, t,
      hl, hd, hZ, ht, hG⟩ := h2 hb
    exact h1 θ γ c hθ hc hcγ hγ V I K s T Z₁ Z₂ t hl hd hZ ht hG
  intro ε hε
  filter_upwards [bound ε hε] with n hn
  intro ι _ _ hcard K hK hi u v hu hv
  dsimp only
  rintro ⟨x, hx, hdist⟩
  let P : Finset ℝ² := univ.image x
  have hP : #P = n := by
    rw [Finset.card_image_of_injective _ hx]
    exact hcard
  obtain ⟨z, hz, hzbound⟩ := hn P hP
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨a, ?_⟩
  have himage : (univ.erase a).image x = P.erase (x a) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, P]
    constructor
    · rintro ⟨b, hba, rfl⟩
      exact ⟨fun h ↦ hba (hx h), b, trivial, rfl⟩
    · rintro ⟨hne, b, _, rfl⟩
      exact ⟨b, fun h ↦ hne (congrArg x h), rfl⟩
  have hcounts := image_count (univ.erase a)
    (fun b ↦ (u b - u a) * (v b - v a)) (fun b ↦ dist (x b) (x a))
    (fun b c ↦ hdist b a c a)
  rw [← himage, Finset.image_image] at hzbound
  rw [hcounts]
  exact hzbound

end OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1_H1_R1
