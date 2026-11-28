import FormalConjectures.ErdosProblems.«774»
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Finset.Union

-- Credit: @LDJAI
namespace OMA.R_Erdos774_erdos_774_R1

open scoped BigOperators

/-- Weighted extraction, known by Bourgain (1985), once the unweighted proportional
    extraction bound has been converted to a uniform Sidon bound. -/
def H1 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ F : Finset ℕ,
      (∀ B : Finset ℕ, B ⊆ F →
        ∃ S ⊆ B, (S.card : ℝ) ≥ c * B.card ∧ Set.IsDissociated (↑S : Set ℕ)) →
      ∀ w : ℕ → ℝ, (∀ n ∈ F, 0 ≤ w n) →
        ∃ S ⊆ F, Set.IsDissociated (↑S : Set ℕ) ∧
          (∑ n ∈ S, w n) ≥ δ * (∑ n ∈ F, w n)

/-- The remaining finite weighted decomposition problem; this is a conjectural step. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : ℕ, 0 < k ∧ ∀ F : Finset ℕ,
      (∀ w : ℕ → ℝ, (∀ n ∈ F, 0 ≤ w n) →
        ∃ S ⊆ F, Set.IsDissociated (↑S : Set ℕ) ∧
          (∑ n ∈ S, w n) ≥ δ * (∑ n ∈ F, w n)) →
      ∃ D : Fin k → Set ℕ, (∀ i, Set.IsDissociated (D i)) ∧
        (↑F : Set ℕ) ⊆ ⋃ i, D i

theorem good_mono {k : ℕ} {A B : Set ℕ} {f : ℕ → Fin k} (h : (∀ i, Set.IsDissociated {n | n ∈ B ∧ f n = i}))
    (hAB : A ⊆ B) : (∀ i, Set.IsDissociated {n | n ∈ A ∧ f n = i}) := by
  intro i S hS T hT heq
  apply h i (fun x hx => ⟨hAB (hS hx).1, (hS hx).2⟩)
    (fun x hx => ⟨hAB (hT hx).1, (hT hx).2⟩) heq

/-- A finite coloring condition only depends on finitely many coordinates. -/
theorem good_congr {k : ℕ} {F : Finset ℕ} {f g : ℕ → Fin k}
    (h : ∀ n ∈ F, f n = g n) : (∀ i, Set.IsDissociated {n | n ∈ (↑F : Set ℕ) ∧ f n = i}) ↔ (∀ i, Set.IsDissociated {n | n ∈ (↑F : Set ℕ) ∧ g n = i}) := by
  have e (i : Fin k) : {n | n ∈ (↑F : Set ℕ) ∧ f n = i} =
      {n | n ∈ (↑F : Set ℕ) ∧ g n = i} := by
    ext n
    constructor
    · rintro ⟨hn, hc⟩
      exact ⟨hn, (h n hn).symm.trans hc⟩
    · rintro ⟨hn, hc⟩
      exact ⟨hn, (h n hn).trans hc⟩
  simp only [e]

/-- Uniformly colorable finite subsets imply uniform colorability of the whole set. -/
theorem finite_iff_global (A : Set ℕ) (k : ℕ)
    (h : ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ A →
      ∃ f : ℕ → Fin k, (∀ i, Set.IsDissociated {n | n ∈ (↑F : Set ℕ) ∧ f n = i})) :
    ∃ f : ℕ → Fin k, (∀ i, Set.IsDissociated {n | n ∈ A ∧ f n = i}) := by
  classical
  let : TopologicalSpace (Fin k) := ⊥
  let : DiscreteTopology (Fin k) := ⟨rfl⟩
  let I := {F : Finset ℕ // (↑F : Set ℕ) ⊆ A}
  let : Nonempty I := ⟨⟨∅, by simp⟩⟩
  let C : I → Set (ℕ → Fin k) := fun F => {f | (∀ i, Set.IsDissociated {n | n ∈ (↑F.val : Set ℕ) ∧ f n = i})}
  have hcl (F : I) : IsClosed (C F) := by
    let R : (ℕ → Fin k) → (F.val → Fin k) := fun f n => f n.val
    let D : Set (F.val → Fin k) := {g | ∃ f : ℕ → Fin k, (∀ i, Set.IsDissociated {n | n ∈ (↑F.val : Set ℕ) ∧ f n = i}) ∧ R f = g}
    have he : C F = R ⁻¹' D := by
      ext f
      change (∀ i, Set.IsDissociated {n | n ∈ (↑F.val : Set ℕ) ∧ f n = i}) ↔ ∃ g : ℕ → Fin k, (∀ i, Set.IsDissociated {n | n ∈ (↑F.val : Set ℕ) ∧ g n = i}) ∧ R g = R f
      constructor
      · exact fun hf => ⟨f, hf, rfl⟩
      · rintro ⟨g, hg, he⟩
        exact (good_congr (fun n hn => congrFun he ⟨n, hn⟩)).mp hg
    have hc : Continuous R := continuous_pi (fun n => continuous_apply n.val)
    rw [he]
    exact D.toFinite.isClosed.preimage hc
  have hd : Directed (· ⊇ ·) C := by
    intro F G
    let H : I := ⟨F.val ∪ G.val, by
      simpa only [Finset.coe_union] using Set.union_subset F.prop G.prop⟩
    refine ⟨H, ?_, ?_⟩
    · intro f hf
      exact good_mono hf (by intro x hx; exact Finset.mem_union_left _ hx)
    · intro f hf
      exact good_mono hf (by intro x hx; exact Finset.mem_union_right _ hx)
  have hnon (F : I) : (C F).Nonempty := h F.val F.prop
  have hcompact (F : I) : IsCompact (C F) := (hcl F).isCompact
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hd hnon hcompact hcl
  refine ⟨f, ?_⟩
  intro i S hS T hT he
  let F : I := ⟨S ∪ T, by
    intro n hn
    rcases Finset.mem_union.mp hn with hS' | hT'
    · exact (hS hS').1
    · exact (hT hT').1⟩
  have hf' : (∀ i, Set.IsDissociated {n | n ∈ (↑F.val : Set ℕ) ∧ f n = i}) := Set.mem_iInter.mp hf F
  apply hf' i _ _ he
  · intro n hn
    exact ⟨Finset.mem_union_left _ hn, (hS hn).2⟩
  · intro n hn
    exact ⟨Finset.mem_union_right _ hn, (hT hn).2⟩

/-- Colorability gives a finite union of dissociated sets. -/
theorem cover_of_good {A : Set ℕ} {k : ℕ} {f : ℕ → Fin k} (h : (∀ i, Set.IsDissociated {n | n ∈ A ∧ f n = i})) :
    ∃ D : Fin k → Set ℕ, (∀ i, Set.IsDissociated (D i)) ∧ A = ⋃ i, D i := by
  refine ⟨fun i => {n | n ∈ A ∧ f n = i}, h, ?_⟩
  ext n
  simp

/-- A finite dissociated cover can be refined to a coloring. -/
theorem good_of_cover {A : Set ℕ} {k : ℕ} (hk : 0 < k)
    {D : Fin k → Set ℕ} (hD : ∀ i, Set.IsDissociated (D i))
    (hA : A ⊆ ⋃ i, D i) :
    ∃ f : ℕ → Fin k, (∀ i, Set.IsDissociated {n | n ∈ A ∧ f n = i}) := by
  classical
  have h (n : ℕ) (hn : n ∈ A) : ∃ i, n ∈ D i := Set.mem_iUnion.mp (hA hn)
  let f (n : ℕ) : Fin k := if hn : n ∈ A then (h n hn).choose else ⟨0,hk⟩
  refine ⟨f, ?_⟩
  intro i S hS T hT heq
  have hsub : {n | n ∈ A ∧ f n = i} ⊆ D i := by
    intro n hn
    change n ∈ A ∧ f n = i at hn
    have hf : f n = (h n hn.1).choose := dif_pos hn.1
    rw [← hn.2, hf]
    exact (h n hn.1).choose_spec
  exact hD i (fun n hn => hsub (hS hn)) (fun n hn => hsub (hT hn)) heq

/-- The two stated hypotheses together imply exactly the original theorem. -/
theorem main : H1 → H2 → type_of% @Erdos774.erdos_774 := by
  intro H1 H2 A _ hA
  obtain ⟨c,hc,hA⟩ := hA
  obtain ⟨δ,hδ,h1⟩ := H1 c hc
  obtain ⟨k,hk,h2⟩ := H2 δ hδ
  obtain ⟨f,hf⟩ := finite_iff_global A k (fun F hF => by
    have hFweighted := h1 F (fun B hB => hA B (fun _ hn => hF (hB hn)))
    obtain ⟨D,hD,hC⟩ := h2 F hFweighted
    exact good_of_cover hk hD hC)
  obtain ⟨D,hD,hAeq⟩ := cover_of_good hf
  refine ⟨Set.range D, ?_, Set.finite_range _, ?_⟩
  · rintro _ ⟨i,rfl⟩
    exact hD i
  · simpa only [Set.sUnion_range] using hAeq


end OMA.R_Erdos774_erdos_774_R1
