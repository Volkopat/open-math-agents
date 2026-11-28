import FormalConjectures.GreensOpenProblems.«4»
import Mathlib

/-! Keevash, Lifshitz and Minzer, On the largest product-free subsets of
the alternating groups. Isolate the lower bound for the model family,
their approximate containment theorem, and the subsequent upgrade to
exact containment. Finiteness then turns containment into equality. -/
open Filter Green4 Set
open scoped Topology
namespace OMA.R_Green4_large_green_4_R1

/-- The model construction reaches the density threshold for approximate stability. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, ∃ (x : Fin n) (I : Set (Fin n)),
  (n:ℝ)^(-(33:ℝ)/50) ≤
    ((extremalFamily x I).ncard:ℝ) / Fintype.card (alternatingGroup (Fin n))

/-- Approximate containment up to inversion at the density threshold of Theorem 1.2. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, ∀ S : Set (alternatingGroup (Fin n)),
  ProdFree S → (n:ℝ)^(-(33:ℝ)/50) ≤ (S.ncard:ℝ) / Fintype.card (alternatingGroup (Fin n)) →
  ∃ (x : Fin n) (I : Set (Fin n)),
    ((S \ extremalFamily x I).ncard:ℝ) / Fintype.card (alternatingGroup (Fin n)) < (n:ℝ)^(-(33:ℝ)/50) ∨
    ((S \ (extremalFamily x I).image (·⁻¹)).ncard:ℝ) / Fintype.card (alternatingGroup (Fin n)) <
      (n:ℝ)^(-(33:ℝ)/50)

/-- Upgrade approximate containment at the size of the largest model family.
The witness of exact containment may be a different model family. -/
def H3 : Prop := ∀ᶠ n : ℕ in atTop, ∀ S : Set (alternatingGroup (Fin n)),
  ProdFree S → (∀ (x : Fin n) (I : Set (Fin n)), (extremalFamily x I).ncard ≤ S.ncard) →
  (∃ (x : Fin n) (I : Set (Fin n)),
    ((S \ extremalFamily x I).ncard:ℝ) / Fintype.card (alternatingGroup (Fin n)) < (n:ℝ)^(-(33:ℝ)/50) ∨
    ((S \ (extremalFamily x I).image (·⁻¹)).ncard:ℝ) / Fintype.card (alternatingGroup (Fin n)) <
      (n:ℝ)^(-(33:ℝ)/50)) →
  ∃ (x : Fin n) (I : Set (Fin n)), S ⊆ extremalFamily x I ∨ S ⊆ (extremalFamily x I).image (·⁻¹)

theorem model_product_free {n : ℕ} (x : Fin n) (I : Set (Fin n)) :
    ProdFree (extremalFamily x I) := by
  intro a ha b hb hab
  have him : a.val (b.val x) ∈ I.image a.val := ⟨b.val x,hb.1,rfl⟩
  exact Set.disjoint_left.mp ha.2 him hab.1

theorem inverse_product_free {G : Type*} [Group G] {S : Set G} (h : ProdFree S) :
    ProdFree (S.image (·⁻¹)) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ⟨c,hc,he⟩
  apply h b hb a ha
  have hc' : c = b*a := by
    simpa using congrArg (fun d : G ↦ d⁻¹) he
  simpa only [hc'] using hc

theorem main : H1 → H2 → H3 → type_of% @Green4.large_green_4 := by
  intro lower approximate upgrade
  filter_upwards [lower,approximate,upgrade] with n hn happrox hup
  intro S hS
  have hs (T : Set (alternatingGroup (Fin n))) (hT : ProdFree T) : T.ncard ≤ S.ncard := by
    by_contra! nh
    exact (not_le_of_gt nh) (hS.2 hT nh.le)
  obtain ⟨x,I,hI⟩ := hn
  have size : (n:ℝ)^(-(33:ℝ)/50) ≤ (S.ncard:ℝ) / Fintype.card (alternatingGroup (Fin n)) :=
    hI.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast hs _ (model_product_free x I)) (by positivity))
  obtain ⟨y,J,h⟩ := hup S hS.1 (fun z K ↦ hs _ (model_product_free z K)) (happrox S hS.1 size)
  refine ⟨y,J,?_⟩
  rcases h with h|h
  · exact Or.inl (Set.eq_of_subset_of_ncard_le h (hs _ (model_product_free y J)))
  · exact Or.inr (Set.eq_of_subset_of_ncard_le h (hs _ (inverse_product_free (model_product_free y J))))

end OMA.R_Green4_large_green_4_R1
