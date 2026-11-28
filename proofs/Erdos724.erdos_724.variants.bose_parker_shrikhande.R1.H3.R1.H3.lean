import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H3.R1.H3: hypothesis H3 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H3.R1

/-!
Direct product. For odd `b` the squares `(i, j) ↦ i + j` and `(i, j) ↦ i - j` over `Fin b` are
orthogonal, because `(i + j, i - j)` determines `2 i` and doubling is injective modulo an odd
number. Given orthogonal `L`, `M` of order `a`, identify `Fin (a * b)` with `Fin a × Fin b` and
take `(L x₁ y₁, x₂ + y₂)` and `(M x₁ y₁, x₂ - y₂)` (`OMA.P` builds such a product square once,
for any quasigroup operation on `Fin b`). They differ already in the first coordinate, at a cell
where `L` and `M` differ.
-/

open Function

/-- The direct product of a Latin square `L` of order `a` with a quasigroup operation `f` on
`Fin b`, as a Latin square of order `a * b`. -/
def OMA.P {a b : ℕ} (L : LatinSquare a) (f : Fin b → Fin b → Fin b) (h : ∀ x, Injective (f x))
    (h' : ∀ y, Injective (f · y)) : LatinSquare (a * b) :=
  ⟨fun x y => finProdFinEquiv (L.mat (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
      f (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2),
    fun _ _ _ e => have := Prod.ext_iff.1 (finProdFinEquiv.injective e)
      finProdFinEquiv.symm.injective (Prod.ext (L.row_injective _ this.1) (h _ this.2)),
    fun _ _ _ e => have := Prod.ext_iff.1 (finProdFinEquiv.injective e)
      finProdFinEquiv.symm.injective (Prod.ext (L.col_injective _ this.1) (h' _ this.2))⟩

theorem OMA.solution :
    OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1.H3 := by
  rintro a b hb hb3 ⟨L, M, hne, ho⟩
  have : NeZero b := ⟨by omega⟩
  obtain ⟨i, hi⟩ := ne_iff.1 fun h : L.mat = M.mat => hne (by cases L; cases M; cases h; rfl)
  obtain ⟨j, hj⟩ := ne_iff.1 hi
  refine ⟨OMA.P L (· + ·) (fun _ => add_right_injective _) (fun _ => add_left_injective _),
    OMA.P M (· - ·) (fun _ => sub_right_injective) (fun _ => sub_left_injective), fun h => hj ?_, ?_⟩
  · simpa only [OMA.P, Equiv.symm_apply_apply] using congrArg (fun S : LatinSquare _ =>
      (finProdFinEquiv.symm (S.mat (finProdFinEquiv (i, 0)) (finProdFinEquiv (j, 0)))).1) h
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [OMA.P, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨⟨l1, l2⟩, m1, m2⟩ := h
    obtain ⟨u, v⟩ := Prod.mk.inj (ho (Prod.ext l1 m1))
    have w : (finProdFinEquiv.symm x).2 = (finProdFinEquiv.symm x').2 := by
      have := congrArg Fin.val (((add_add_sub_cancel _ _ _).symm.trans
        (congrArg₂ (· + ·) l2 m2)).trans (add_add_sub_cancel _ _ _))
      simp only [Fin.val_add, ← two_mul] at this
      exact Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt] using
        Nat.ModEq.cancel_left_of_coprime (Nat.coprime_two_right.2 hb) this)
    rw [w] at l2
    rw [finProdFinEquiv.symm.injective (Prod.ext u w),
      finProdFinEquiv.symm.injective (Prod.ext v (add_left_cancel l2))]
