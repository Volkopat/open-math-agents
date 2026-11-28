import OMAStatements.S_wp_rokhlin_s
import Mathlib
/- Adapted from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. -/
open MeasureTheory Filter
open scoped Topology BigOperators
namespace OMA.R_wp_rokhlin_s_R1
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

theorem three_of_sequential (μ : Measure X) (T : X ≃ᵐ X)
    (hseq : (∀ d : ℕ → Fin 3 → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin 3 → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i)))))
    (A B C : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Tendsto (fun p : ℕ × ℕ => μ (A ∩ (⇑T)^[p.1] ⁻¹' B ∩ (⇑T)^[p.1 + p.2] ⁻¹' C))
      atTop (𝓝 (μ A * μ B * μ C)) := by
  classical
  by_contra hn
  rw [Filter.tendsto_def] at hn
  push Not at hn
  obtain ⟨s, hs, hbad⟩ := hn
  have hex (r : ℕ) : ∃ p : ℕ × ℕ, r < p.1 ∧ r < p.2 ∧
      μ (A ∩ (⇑T)^[p.1] ⁻¹' B ∩ (⇑T)^[p.1 + p.2] ⁻¹' C) ∉ s := by
    have hfreq := Filter.not_eventually.mp hbad
    obtain ⟨p, hp, hout⟩ := frequently_atTop.1 hfreq (r+1,r+1)
    exact ⟨p, by have := hp.1; omega, by have := hp.2; omega, hout⟩
  choose p hp hq hout using hex
  let d : ℕ → Fin 3 → ℕ := fun r => ![0, (p r).1, (p r).1 + (p r).2]
  have hd : ∀ r i j, i < j → d r i+r < d r j := by
    intro r i j hij
    have h1 := hp r
    have h2 := hq r
    fin_cases i <;> fin_cases j <;> simp_all [d] <;> exact (hp r).trans_le (Nat.le_add_right _ _)
  let S : Fin 3 → Set X := ![A,B,C]
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    fin_cases i <;> simpa [S]
  have ht := hseq d hd S hS
  have he r : (⋂ i, (T^[d r i]) ⁻¹' S i) =
      A ∩ (⇑T)^[(p r).1] ⁻¹' B ∩ (⇑T)^[(p r).1 + (p r).2] ⁻¹' C := by
    ext x
    simp [d, S, Fin.forall_fin_succ, and_assoc]
  have hprod : (∏ i, μ (S i)) = μ A * μ B * μ C := by
    simp [S, Fin.prod_univ_succ, mul_assoc]
  simp only [he, hprod] at ht
  obtain ⟨r, hr⟩ := (ht.eventually hs).exists
  exact hout r hr

lemma all_orders (b : H1) (h : H2) : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X ≃ᵐ X), MeasurePreserving T μ μ → (∀ s t : Set X, MeasurableSet s → MeasurableSet t → Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) → ∀ k, (∀ d : ℕ → Fin k → ℕ, (∀ r i j, i < j → d r i+r < d r j) → ∀ A : Fin k → Set X, (∀ i, MeasurableSet (A i)) → Tendsto (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i)))) := by
  intro X _ μ _ T hT hm k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : 3 ≤ k
    · intro d hd
      exact h X μ T hT hm k hk d hd (proper_rectangles_of_induction μ T ih d hd)
    · exact b X μ T hT hm k (by omega)

theorem main : H1 → H2 → type_of% @OMA.S_wp_rokhlin_s.main := by
  intro b h X _ μ _ T hT hm A B C hA hB hC
  refine three_of_sequential μ T ?_ A B C hA hB hC
  apply all_orders b h X μ T hT
  intro s t hs ht
  simpa only [Set.inter_comm, mul_comm] using hm t s ht hs

end OMA.R_wp_rokhlin_s_R1
