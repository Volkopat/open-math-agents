import OMAReductions.R_Erdos724_erdos_724_variants_beth_R1

-- Step Erdos724.erdos_724.variants.wilson.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.wilson.R1
-- Credit: @ivillar
-- Over a finite field F with q elements the q - 1 squares (i, j) -> c i + j, c nonzero, are
-- Latin and pairwise orthogonal; GaloisField p k has p^k elements.

open Finset

namespace O2W

variable {F : Type*} [Field F]

/-- The square `(i, j) ↦ c * i + j` over a finite field, transported to `Fin n`. -/
def sq {n : ℕ} (e : Fin n ≃ F) (c : F) (hc : c ≠ 0) : LatinSquare n where
  mat := fun i j => e.symm (c * e i + e j)
  row_injective := by
    intro i a b h
    have h' := e.symm.injective h
    exact e.injective (add_left_cancel h')
  col_injective := by
    intro j a b h
    have h' := e.symm.injective h
    have h'' : c * e a = c * e b := add_right_cancel h'
    exact e.injective (mul_left_cancel₀ hc h'')

theorem field_bound [Fintype F] [DecidableEq F] (n : ℕ) (hn : Fintype.card F = n) :
    n - 1 ≤ Erdos724.maxMOLS n := by
  classical
  let e : Fin n ≃ F := (Fintype.equivFinOfCardEq hn).symm
  let f : Fˣ → LatinSquare n := fun u => sq e (u : F) u.ne_zero
  have finj : Function.Injective f := by
    intro u v h
    have h1 := congrArg (fun L : LatinSquare n => e (L.mat (e.symm 1) (e.symm 0))) h
    simp only [f, sq, Equiv.apply_symm_apply, mul_one, add_zero] at h1
    exact Units.ext h1
  have hcard : (univ.image f).card = n - 1 := by
    rw [card_image_of_injective _ finj, card_univ, Fintype.card_units, hn]
  refine le_csSup ⟨Fintype.card (LatinSquare n), ?_⟩ ⟨univ.image f, hcard, ?_⟩
  · rintro k ⟨S, rfl, -⟩
    exact card_le_univ S
  · intro L hL M hM hLM
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hL hM
    obtain ⟨u, rfl⟩ := hL
    obtain ⟨v, rfl⟩ := hM
    have huv : (u : F) ≠ v := fun h => hLM (by rw [Units.ext h])
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f, sq, Prod.mk.injEq] at h
    have h1 := e.symm.injective h.1
    have h2 := e.symm.injective h.2
    have h3 : ((u : F) - v) * (e i - e i') = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) huv
    · have hii : i = i' := e.injective (sub_eq_zero.mp h4)
      subst hii
      have hjj : e j = e j' := add_left_cancel h1
      rw [e.injective hjj]

theorem prime_power_bound (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k - 1 ≤ Erdos724.maxMOLS (p ^ k) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype (GaloisField p k) := Fintype.ofFinite _
  exact field_bound (F := GaloisField p k) (p ^ k)
    (by rw [Fintype.card_eq_nat_card]; exact GaloisField.card p k (by omega))

end O2W

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_beth_R1.H1 :=
  fun p k hp hk => O2W.prime_power_bound p k hp hk
