import OMAStatements.S_mo_248883
import Mathlib

namespace OMA.P_mo_248883

open Equiv

/-- The nontrivial homomorphism from the units of the integers to the permutations of two letters. -/
def tau : ℤˣ →* Perm (Fin 2) where
  toFun u := if u = 1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' := by decide

/-- The seven letters split as the two letters `0, 1` and the five letters `2, ..., 6`. -/
def e7 : Fin 2 ⊕ Fin 5 ≃ Fin 7 := finSumFinEquiv

/-- The block embedding of `S_2 × S_5` into `S_7`. -/
def blk : Perm (Fin 2) × Perm (Fin 5) →* Perm (Fin 7) :=
  e7.permCongrHom.toMonoidHom.comp (Perm.sumCongrHom (Fin 2) (Fin 5))

lemma blk_inj : Function.Injective blk := by
  intro a b hab
  apply Perm.sumCongrHom_injective
  exact e7.permCongrHom.injective hab

lemma blk_apply (p : Perm (Fin 2)) (s : Perm (Fin 5)) (y : Fin 2 ⊕ Fin 5) :
    blk (p, s) (e7 y) = e7 (Sum.map p s y) := by
  simp [blk, Equiv.permCongrHom]

/-- The copy of `S_2` on the letters `0, 1`. -/
def psi : Perm (Fin 2) →* Perm (Fin 7) :=
  blk.comp (MonoidHom.inl (Perm (Fin 2)) (Perm (Fin 5)))

/-- The twisted copy of `S_5`: a permutation of the letters `2, ..., 6`, times the transposition of
`0, 1` exactly when that permutation is odd. -/
def phi : Perm (Fin 5) →* Perm (Fin 7) :=
  blk.comp ((tau.comp Perm.sign).prod (MonoidHom.id (Perm (Fin 5))))

lemma psi_inj : Function.Injective psi := by
  intro a b hab
  have h := blk_inj hab
  simpa using h

lemma phi_inj : Function.Injective phi := by
  intro a b hab
  have h := blk_inj hab
  simp only [MonoidHom.prod_apply, MonoidHom.id_apply, Prod.mk.injEq] at h
  exact h.2

lemma perm2_comm : ∀ p q : Perm (Fin 2), p * q = q * p := by decide

lemma comm : ∀ a ∈ psi.range, ∀ b ∈ phi.range, a * b = b * a := by
  rintro _ ⟨p, rfl⟩ _ ⟨s, rfl⟩
  simp only [psi, phi, MonoidHom.comp_apply, ← map_mul]
  congr 1
  ext1
  · exact perm2_comm _ _
  · simp

lemma tau_neg_one : tau (-1) = Equiv.swap 0 1 := by decide

lemma swap01_moves : ∀ i : Fin 2, Equiv.swap (0 : Fin 2) 1 i ≠ i := by decide

lemma succ_ne : ∀ j : Fin 5, j + 1 ≠ j := by decide

lemma moves (x : Fin 7) : ∃ s : Perm (Fin 5), phi s x ≠ x := by
  obtain ⟨y, rfl⟩ := e7.surjective x
  rcases y with i | j
  · refine ⟨Equiv.swap 0 1, ?_⟩
    have hs : Perm.sign (Equiv.swap (0 : Fin 5) 1) = -1 := Perm.sign_swap (by decide)
    have h : phi (Equiv.swap 0 1) (e7 (Sum.inl i))
        = e7 (Sum.inl (Equiv.swap (0 : Fin 2) 1 i)) := by
      simp only [phi, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.id_apply, hs, tau_neg_one]
      rw [blk_apply]
      rfl
    rw [h]
    intro hc
    exact swap01_moves i (Sum.inl_injective (e7.injective hc))
  · refine ⟨Equiv.swap j (j + 1), ?_⟩
    have h : phi (Equiv.swap j (j + 1)) (e7 (Sum.inr j))
        = e7 (Sum.inr (j + 1)) := by
      simp only [phi, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.id_apply]
      rw [blk_apply]
      simp
    rw [h]
    intro hc
    exact succ_ne j (Sum.inr_injective (e7.injective hc))

end OMA.P_mo_248883

open OMA.P_mo_248883

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_248883.main) := by
  intro h
  obtain ⟨-, T, hT, hmem⟩ := h 7 (by norm_num) (by norm_num) 2 (by norm_num) psi.range phi.range
    ⟨(MonoidHom.ofInjective psi_inj).symm⟩ ⟨(MonoidHom.ofInjective phi_inj).symm⟩ comm
  have hne : T.Nonempty := by
    rw [← Finset.card_pos, hT]
    norm_num
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, hs⟩ := moves x
  exact hs ((hmem (phi s)).1 ⟨s, rfl⟩ x hx)
