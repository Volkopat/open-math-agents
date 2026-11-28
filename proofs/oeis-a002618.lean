import OMAStatements.S_oeis_a002618
import Mathlib

/-! The merged statement puts the coprimality hypotheses inside the existential, so every
function satisfies `IsAPPermutation` (take `c = 0`, which is not coprime to `4`). The set is
then all `4! = 24` bijections of `Fin 4`, while `a 4 = 4 * φ(4) = 8`. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002618.main) := by
  intro h
  have h4 := h 4 (by norm_num)
  have hall : ∀ f : Fin 4 → Fin 4, OMA.S_oeis_a002618.IsAPPermutation f := by
    intro f
    refine ⟨0, 0, ?_⟩
    intro hc
    exact absurd hc (by decide)
  have hset : { f : Fin 4 → Fin 4 | Function.Bijective f ∧ OMA.S_oeis_a002618.IsAPPermutation f }
      = { f | Function.Bijective f } := by
    ext f; simp [hall f]
  rw [hset] at h4
  have e : Equiv.Perm (Fin 4) ≃ { f : Fin 4 → Fin 4 | Function.Bijective f } :=
    { toFun := fun σ => ⟨σ, σ.bijective⟩
      invFun := fun f => Equiv.ofBijective f.1 f.2
      left_inv := fun σ => by ext; rfl
      right_inv := fun f => by ext; rfl }
  have ht : Nat.totient 4 = 2 := by decide
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_perm] at h4
  simp [OMA.S_oeis_a002618.a, ht, Nat.factorial] at h4
