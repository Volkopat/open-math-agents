import Mathlib

/-!
# Binary necklaces admitting a palindromic cut

Source: https://oeis.org/A185376, Tony Bartoletti (2011).
-/
namespace OMA.S_oeis_a185376

/-- Read a cyclic binary word of length L repeatedly in both directions.
The cut between positions -1 and 0 is palindromic. -/
def PalWord (L : ℕ) :=
  {f : ℤ → Bool // Function.Periodic f (L : ℤ) ∧ ∀ i, f (-1-i)=f i}

/-- Two cuts determine the same necklace exactly when they differ by a rotation. -/
def rotation (L : ℕ) : Setoid (PalWord L) where
  r w v := ∃ k : ℤ, ∀ i, v.val i=w.val (i+k)
  iseqv := {
    refl := fun _ => ⟨0,by simp⟩
    symm := by
      rintro w v ⟨k,h⟩
      exact ⟨-k,fun i=>by rw [h]; simp⟩
    trans := by
      rintro w v u ⟨k,h⟩ ⟨m,e⟩
      exact ⟨m+k,fun i=>by rw [e,h,add_assoc]⟩ }

/-- Only necklaces with a palindromic cut have representatives here. -/
def Necklace (L : ℕ) := Quotient (rotation L)

theorem main : ∀ n : ℕ, 0 < n →
    Nat.card (Necklace (2*n)) =
      2^(n-1) + 2^((n-2^(n.factorization 2))/2^(n.factorization 2+1)) := by
  sorry

end OMA.S_oeis_a185376
