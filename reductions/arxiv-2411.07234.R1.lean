import OMAStatements.S_arxiv_2411_07234
import Mathlib
/- Adapted from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. -/
open MeasureTheory Filter
open scoped Topology BigOperators
namespace OMA.R_arxiv_2411_07234_R1
def H1 : Prop := ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X ≃ᵐ X), MeasurePreserving T μ μ → (∀ s t : Set X, MeasurableSet s → MeasurableSet t → Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) → ∀ k, k < 3 → (∀ d : ℕ → Fin k → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin k → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i))))

def H2 : Prop := ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X ≃ᵐ X), MeasurePreserving T μ μ → (∀ s t : Set X, MeasurableSet s → MeasurableSet t → Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) → ∀ k, 3 ≤ k → ∀ d : ℕ → Fin k → ℕ, (∀ r i j, i < j → d r i+r < d r j) → (∀ J : Finset (Fin k), J ≠ Finset.univ → ∀ s : J → Set X, (∀ j, MeasurableSet (s j)) → Tendsto (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop (𝓝 (∏ j : J, μ (s j)))) → ∀ A : Fin k → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i)))

variable {X : Type} [MeasurableSpace X]
lemma proper_rectangles_of_induction (μ : Measure X) (T : X ≃ᵐ X) {k : ℕ}
    (ih : ∀ n < k, (∀ d : ℕ → Fin n → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin n → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i))))) (d : ℕ → Fin k → ℕ) (hd : ∀ r i j, i < j → d r i+r < d r j) :
    ∀ J : Finset (Fin k), J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))) := by
  intro J hJ s hs
  have hcard : J.card < k := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ J,hJ⟩)
  let e : Fin J.card ≃o J := J.orderIsoOfFin rfl
  have he : ∀ r (i j : Fin J.card), i < j → d r (e i)+r < d r (e j) := by
    intro r i j hij
    exact hd r _ _ (e.strictMono hij)
  have ht := ih J.card hcard _ he (fun i => s (e i)) (fun i => hs (e i))
  have hi r : (⋂ i : Fin J.card, (T^[d r (e i)]) ⁻¹' s (e i)) = ⋂ j : J, (T^[d r j]) ⁻¹' s j :=
    e.surjective.iInter_comp (fun j : J => (T^[d r j]) ⁻¹' s j)
  have hp : (∏ i : Fin J.card, μ (s (e i))) = ∏ j : J, μ (s j) := e.toEquiv.prod_comp (fun j : J => μ (s j))
  simpa only [hi,hp] using ht

lemma prefixTime_gap_bound {k : ℕ} (g : Fin k → ℕ) (i j : Fin (k+1)) (hij : i<j) :
    ∃ q : Fin k, (∑ j : Fin k, if j.val < i.val then g j else 0)+(g q:ℕ) ≤ (∑ l : Fin k, if l.val < j.val then g l else 0) := by
  classical
  let q : Fin k := ⟨i.val,by have := j.isLt; have := hij; omega⟩
  let s : Finset (Fin k) := Finset.univ.filter (fun t => t.val < i.val)
  let t : Finset (Fin k) := Finset.univ.filter (fun t => t.val < j.val)
  have hqs : q ∉ s := by simp [s,q]
  have hsub : insert q s ⊆ t := by
    intro l hl
    rcases Finset.mem_insert.mp hl with h | h
    · subst l; simpa [t,q] using hij
    · have hl := (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans hl hij⟩
  refine ⟨q,?_⟩
  have hei : (∑ j : Fin k, if j.val < i.val then g j else 0) = ∑ l ∈ s, (g l:ℕ) := by simp [s,Finset.sum_filter]
  have hej : (∑ l : Fin k, if l.val < j.val then g l else 0) = ∑ l ∈ t, (g l:ℕ) := by simp [t,Finset.sum_filter]
  rw [hei,hej,add_comm,←Finset.sum_insert (f := fun l => (g l:ℕ)) hqs]
  exact Finset.sum_le_sum_of_subset hsub

theorem gaps_of_sequential (μ : Measure X) (T : X ≃ᵐ X) (k : ℕ)
    (hseq : (∀ d : ℕ → Fin (k+1) → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin (k+1) → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i))))) (A : Fin (k+1) → Set X)
    (hA : ∀ i, MeasurableSet (A i)) : Tendsto
    (fun g : Fin k → ℕ => μ (⋂ i, (T^[(∑ j : Fin k, if j.val < i.val then g j else 0)]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i))) := by
  classical
  by_contra hn
  rw [Filter.tendsto_def] at hn
  push Not at hn
  obtain ⟨s,hs,hbad⟩ := hn
  have hex (r : ℕ) : ∃ g : Fin k → ℕ, (∀ j, r < g j) ∧
      μ (⋂ i, (T^[(∑ j : Fin k, if j.val < i.val then g j else 0)]) ⁻¹' A i) ∉ s := by
    obtain ⟨g,hg,hout⟩ := frequently_atTop.1 (Filter.not_eventually.mp hbad) (fun _ => r+1)
    exact ⟨g,fun j => hg j,hout⟩
  choose g hg hout using hex
  let d : ℕ → Fin (k+1) → ℕ := fun r i => ∑ j : Fin k, if j.val < i.val then g r j else 0
  have hd : ∀ r i j, i < j → d r i+r < d r j := by
    intro r i j hij
    obtain ⟨q,hq⟩ := prefixTime_gap_bound (g r) i j hij
    have hh := hg r q
    dsimp [d]
    omega
  obtain ⟨r,hr⟩ := ((hseq d hd A hA).eventually hs).exists
  exact hout r hr
lemma image_eq_inverse_preimage (T : X ≃ᵐ X) (n : ℕ) (A : Set X) :
    (⇑T)^[n] '' A = (⇑T.symm)^[n] ⁻¹' A := by
  have hL : Function.LeftInverse T.symm T := T.left_inv
  have hR : Function.LeftInverse T T.symm := T.right_inv
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [Set.mem_preimage, hL.iterate n y] using hy
  · intro hx
    exact ⟨_, hx, hR.iterate n x⟩

theorem images_of_inverse_sequential (μ : Measure X) (T : X ≃ᵐ X) (k : ℕ)
    (hseq : (∀ d : ℕ → Fin (k+1) → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin (k+1) → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T.symm^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i))))) (A : Fin (k+1) → Set X)
    (hA : ∀ i, MeasurableSet (A i)) : Tendsto
    (fun g : Fin k → ℕ => μ (⋂ i : Fin (k+1), (⇑T)^[∑ j : Fin k, if j.val < i.val then g j else 0] '' A i)) atTop (𝓝 (∏ i, μ (A i))) := by
  simpa only [image_eq_inverse_preimage] using gaps_of_sequential μ T.symm k hseq A hA
lemma all_orders (b : H1) (h : H2) : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X ≃ᵐ X), MeasurePreserving T μ μ → (∀ s t : Set X, MeasurableSet s → MeasurableSet t → Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) → ∀ k, (∀ d : ℕ → Fin k → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin k → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i)))) := by
  intro X _ μ _ T hT hm k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : 3 ≤ k
    · intro d hd
      exact h X μ T hT hm k hk d hd (proper_rectangles_of_induction μ T ih d hd)
    · exact b X μ T hT hm k (by omega)

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2411_07234.main := by
  intro b h X _ μ _ T hT hm k _ A hA
  refine images_of_inverse_sequential μ T k ?_ A hA
  apply all_orders b h X μ T.symm (MeasurePreserving.symm T hT)
  intro s t hs ht
  simpa only [image_eq_inverse_preimage] using hm s t hs ht

end OMA.R_arxiv_2411_07234_R1
