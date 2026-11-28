import FormalConjectures.Wikipedia.PollocksConjecture

/-!
Reduction PollocksConjecture.pollock_tetrahedral.R1: split Pollock's infinite
universal claim into the finite Salzer--Levine classification of four-term
exceptions and a finite check of the bounded range.
-/

-- Reduction PollocksConjecture.pollock_tetrahedral.R1
-- of Pollock's conjecture that every integer is a sum of at most five tetrahedral numbers.
--
-- The infinite universal claim is split into the Salzer--Levine classification of the
-- exceptions to four terms (a finite, decidable statement) and a finite check of the
-- bounded range.  From the classification every N > 343867 is a sum of four tetrahedral
-- numbers, hence of five (append a zero term); the bounded range is handled directly.

namespace OMA.R_PollocksConjecture_pollock_tetrahedral_R1

open PollocksConjecture

/-- Salzer--Levine: the set of integers that are not a sum of four tetrahedral numbers
    has greatest element 343867.  This is a finite classification, not the infinite
    five-term claim. -/
def H1 : Prop :=
  IsGreatest NotSumOfFourTetrahedral 343867

/-- Every integer up to the largest four-term exception is a sum of at most five
    tetrahedral numbers (a finite, kernel-checkable range). -/
def H2 : Prop :=
  ∀ n : ℕ, n ≤ 343867 → ∃ f : Fin 5 → ℕ, n = ∑ i, tetrahedral (f i)

theorem main : H1 → H2 → type_of% @PollocksConjecture.pollock_tetrahedral := by
  classical
  intro hs hsmall N
  by_cases hN : N ≤ 343867
  · exact hsmall N hN
  · have hnotmem : N ∉ NotSumOfFourTetrahedral := by
      intro hmem
      have hle : N ≤ 343867 := hs.2 hmem
      omega
    simp only [NotSumOfFourTetrahedral, Set.mem_ofPred_eq, not_forall, not_ne_iff] at hnotmem
    rcases hnotmem with ⟨f4, hf4⟩
    let f5 : Fin 5 → ℕ := Fin.snoc f4 0
    refine ⟨f5, ?_⟩
    have hsum : (∑ i : Fin 5, tetrahedral (f5 i)) = ∑ i : Fin 4, tetrahedral (f4 i) := by
      rw [Fin.sum_univ_castSucc]
      have hlast : f5 (Fin.last 4) = 0 := by
        dsimp [f5]
        exact Fin.snoc_last (α := fun _ : Fin 5 => ℕ) 0 f4
      rw [hlast]
      simp [f5, tetrahedral]
    exact hf4.trans hsum.symm

end OMA.R_PollocksConjecture_pollock_tetrahedral_R1
