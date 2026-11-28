import FormalConjectures.GreensOpenProblems.«100»

/-! Residually finite groups are sofic. Original proof: @niclorusso (#692);
this version follows @LordMike's pending proof (#499). -/

open Green100

namespace OMA

theorem hamming_self {n : ℕ} (σ : Equiv.Perm (Fin n)) : hammingDistNorm σ σ = 0 := by
  simp [hammingDistNorm]

theorem hamming_all {n : ℕ} (hn : 0 < n) (σ τ : Equiv.Perm (Fin n)) (h : ∀ i, σ i ≠ τ i) :
    hammingDistNorm σ τ = 1 := by
  simp [hammingDistNorm, hammingDist, h, hn.ne']

end OMA

theorem OMA.solution : type_of% @Green100.green_100.variants.residuallyFinite_isSofic := by
  intro G _ _ F ε hε
  classical
  have hK : ∀ p : F.offDiag, ∃ K : FiniteIndexNormalSubgroup G,
      (p.1.1 : G ⧸ K.toSubgroup) ≠ ↑p.1.2 := fun p =>
    Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite _ _
      (Finset.mem_offDiag.mp p.2).2.2
  choose K hK using hK
  let Q := ∀ p : F.offDiag, G ⧸ (K p).toSubgroup
  let φ : G →* Q := MonoidHom.pi fun p => QuotientGroup.mk' (K p).toSubgroup
  have : Finite Q := inferInstance
  let n := Nat.card Q
  let e : Q ≃ Fin n := Finite.equivFin Q
  have hn : 0 < n := Nat.card_pos
  let θ : G →* Equiv.Perm (Fin n) :=
    e.permCongrHom.toMonoidHom.comp ((MulAction.toPermHom Q Q).comp φ)
  refine ⟨n, θ, ?_, ?_, ?_⟩
  · intro g _ h _ _
    rw [← map_mul, OMA.hamming_self]; exact hε
  · intro _
    rw [map_one, OMA.hamming_self]; exact hε
  · intro x hx y hy hxy
    have hφ : φ x ≠ φ y := by
      intro h
      exact hK ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩
        (congrFun h ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩)
    rw [OMA.hamming_all hn]
    · norm_num
    · intro i hi
      apply hφ
      have := e.injective hi
      simpa [θ, Equiv.permCongr_apply] using this
