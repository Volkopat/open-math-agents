import OMAReductions.R_mo_179790_R1
import Mathlib

/-! Step mo-179790.R1.H1: a product of chain-complete posets has the fixed point property.
The product is chain-complete (coordinatewise suprema); Zorn's lemma on the post-fixed points
x with x ≤ f x gives a maximal m, and m ≤ f m with f m post-fixed forces f m = m. -/

namespace OMA.P179

/-- A chain-complete poset (every chain has a supremum): every monotone self-map has a fixed
point (Zorn on the post-fixed points). -/
theorem fixed_of_chainComplete {R : Type} [PartialOrder R]
    (hR : ∀ c : Set R, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) (f : R →o R) : ∃ x, f x = x := by
  obtain ⟨m, hm⟩ := zorn_le₀ {x : R | x ≤ f x} (by
    intro c hcS hc
    obtain ⟨s, hs⟩ := hR c hc
    refine ⟨s, ?_, hs.1⟩
    show s ≤ f s
    apply hs.2
    intro z hz
    exact (hcS hz).trans (f.monotone (hs.1 hz)))
  have hm1 : m ≤ f m := hm.prop
  have hm2 : f m ∈ {x : R | x ≤ f x} := f.monotone hm1
  exact ⟨m, (hm.eq_of_le hm2 hm1).symm⟩

theorem prod_chainComplete {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (hP : ∀ c : Set P, IsChain (· ≤ ·) c → ∃ s, IsLUB c s)
    (hQ : ∀ c : Set Q, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) :
    ∀ c : Set (P × Q), IsChain (· ≤ ·) c → ∃ s, IsLUB c s := by
  intro c hc
  have c1 : IsChain (· ≤ ·) (Prod.fst '' c) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
    rcases hc.total hx hy with h | h
    exacts [Or.inl h.1, Or.inr h.1]
  have c2 : IsChain (· ≤ ·) (Prod.snd '' c) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
    rcases hc.total hx hy with h | h
    exacts [Or.inl h.2, Or.inr h.2]
  obtain ⟨s, hs⟩ := hP (Prod.fst '' c) c1
  obtain ⟨t, ht⟩ := hQ (Prod.snd '' c) c2
  refine ⟨(s, t), ?_, ?_⟩
  · intro z hz
    exact ⟨hs.1 ⟨z, hz, rfl⟩, ht.1 ⟨z, hz, rfl⟩⟩
  · intro u hu
    refine ⟨hs.2 ?_, ht.2 ?_⟩
    · rintro _ ⟨z, hz, rfl⟩; exact (hu hz).1
    · rintro _ ⟨z, hz, rfl⟩; exact (hu hz).2

theorem solution_aux : ∀ (P Q : Type) [PartialOrder P] [PartialOrder Q],
    (∀ c : Set P, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) →
    (∀ c : Set Q, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) →
    OMA.S_mo_179790.FPP (P × Q) := by
  intro P Q _ _ hP hQ f
  exact fixed_of_chainComplete (prod_chainComplete hP hQ) f

end OMA.P179

theorem OMA.solution : OMA.R_mo_179790_R1.H1 := OMA.P179.solution_aux
