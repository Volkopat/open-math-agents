import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1
import Mathlib

/-! In a proper edge coloring of an odd complete graph, every color is missing at a vertex. -/
namespace MissingColors

open Finset

private theorem even_of_involution {A : Type*} [Fintype A] [LinearOrder A]
    (τ : A → A) (hτ : Function.Involutive τ) (hne : ∀ a, τ a ≠ a) :
    Even (Fintype.card A) := by
  let L := univ.filter fun a : A => a < τ a
  let R := univ.filter fun a : A => τ a < a
  have hLR : L.card ≤ R.card := by
    refine card_le_card_of_injOn τ ?_ hτ.injective.injOn
    intro a ha
    have h := (mem_filter.mp (show a ∈ L from ha)).2
    exact mem_filter.mpr ⟨mem_univ _, by rw [hτ]; exact h⟩
  have hRL : R.card ≤ L.card := by
    refine card_le_card_of_injOn τ ?_ hτ.injective.injOn
    intro a ha
    have h := (mem_filter.mp (show a ∈ R from ha)).2
    exact mem_filter.mpr ⟨mem_univ _, by rw [hτ]; exact h⟩
  have hother : univ.filter (fun a : A => ¬ a < τ a) = R := by
    ext a
    simp only [R, mem_filter, mem_univ, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hne a), le_of_lt⟩
  have hsum := (univ : Finset A).card_filter_add_card_filter_not (fun a => a < τ a)
  change L.card + (univ.filter fun a : A => ¬ a < τ a).card = (univ : Finset A).card at hsum
  rw [hother, card_univ] at hsum
  exact ⟨L.card, by omega⟩

theorem injective (p : ℕ) (hp : Odd p) (Q : Finset (Fin (2*p-3))) (hQ : Q.card = p)
    (e : Fin (2*p-3) → Fin (2*p-3) → Fin p)
    (hsym : ∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a)
    (hlocal : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, b ≠ a → c ≠ a → b ≠ c → e a b ≠ e a c)
    (f : Fin (2*p-3) → Fin p)
    (hmiss : ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → e a b ≠ f a) : Set.InjOn f Q := by
  classical
  have himage (a : Fin (2*p-3)) (ha : a ∈ Q) :
      (Q.erase a).image (e a) = (univ : Finset (Fin p)).erase (f a) := by
    apply eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
      obtain ⟨hba, hbQ⟩ := mem_erase.mp hb
      exact mem_erase.mpr ⟨hmiss a ha b hbQ hba.symm, mem_univ _⟩
    · have hi : Set.InjOn (e a) ((Q.erase a : Finset (Fin (2*p-3))) : Set _) := by
        intro b hb c hc hbc
        obtain ⟨hba, hbQ⟩ := mem_erase.mp (show b ∈ Q.erase a from hb)
        obtain ⟨hca, hcQ⟩ := mem_erase.mp (show c ∈ Q.erase a from hc)
        by_contra! hne
        exact hlocal a ha b hbQ c hcQ hba hca hne hbc
      rw [card_image_of_injOn hi, card_erase_of_mem ha, card_erase_of_mem (mem_univ _),
        card_univ, Fintype.card_fin, hQ]
  let F : Q → Fin p := fun a => f a
  have hs : Function.Surjective F := by
    intro c
    by_contra! hnone
    have hchoose (a : Q) : ∃ b : Q, b ≠ a ∧ e a b = c := by
      have hc : c ∈ (Q.erase (a : Fin (2*p-3))).image (e a) := by
        rw [himage a a.property]
        exact mem_erase.mpr ⟨(hnone a).symm, mem_univ _⟩
      obtain ⟨b, hb, he⟩ := mem_image.mp hc
      obtain ⟨hba, hbQ⟩ := mem_erase.mp hb
      exact ⟨⟨b, hbQ⟩, fun heq => hba (congrArg Subtype.val heq), he⟩
    choose τ hne hcolor using hchoose
    have hinv : Function.Involutive τ := by
      intro a
      apply Subtype.ext
      by_contra! hne'
      have ht₁ : (τ (τ a)).val ≠ (τ a).val := fun h => hne (τ a) (Subtype.ext h)
      have ht₂ : a.val ≠ (τ a).val := fun h => hne a (Subtype.ext h.symm)
      exact hlocal (τ a) (τ a).property (τ (τ a)) (τ (τ a)).property a a.property ht₁ ht₂ hne'
        ((hcolor (τ a)).trans ((hsym (τ a) (τ a).property a a.property).trans (hcolor a)).symm)
    have heven := even_of_involution τ hinv hne
    rw [Fintype.card_coe, hQ] at heven
    exact (Nat.not_even_iff_odd.mpr hp) heven
  have hcards : Fintype.card Q = Fintype.card (Fin p) := by rw [Fintype.card_coe, hQ, Fintype.card_fin]
  have hinj := ((Fintype.bijective_iff_surjective_and_card F).mpr ⟨hs, hcards⟩).1
  intro a ha b hb h
  exact congrArg Subtype.val (hinj (show F ⟨a, ha⟩ = F ⟨b, hb⟩ from h))

end MissingColors

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1.H2 := MissingColors.injective