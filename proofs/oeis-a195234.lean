import OMAStatements.S_oeis_a195234
import Mathlib

/-!
Credit: @ivillar
Proof: entries of a valid array differ by at most 3 (the king-move diameter of the
triangle), so the arrays with entries in 0..m+1 that reach m+1 are exactly the translates by
m-2 of the arrays with entries in 0..3 that reach 3; hence a(m+1) - a(m) is constant
for m >= 2, which gives the recurrence.
-/

namespace OMAA195234Helpers
open OMA.S_oeis_a195234

/-- The cell in row 0, column 0. -/
def c00 : Cell := ⟨(0, 0), by decide⟩

/-- The cell in row 1, column 0. -/
def c10 : Cell := ⟨(1, 0), by decide⟩

/-- The cell in row 1, column 1. -/
def c11 : Cell := ⟨(1, 1), by decide⟩

/-- The cell in row 2, column 0. -/
def c20 : Cell := ⟨(2, 0), by decide⟩

/-- The cell in row 2, column 1. -/
def c21 : Cell := ⟨(2, 1), by decide⟩

/-- The cell in row 2, column 2. -/
def c22 : Cell := ⟨(2, 2), by decide⟩

/-- The cell in row 3, column 0. -/
def c30 : Cell := ⟨(3, 0), by decide⟩

/-- The cell in row 3, column 1. -/
def c31 : Cell := ⟨(3, 1), by decide⟩

/-- The cell in row 3, column 2. -/
def c32 : Cell := ⟨(3, 2), by decide⟩

/-- The cell in row 3, column 3. -/
def c33 : Cell := ⟨(3, 3), by decide⟩

theorem cells (p : Cell) : p = c00 ∨ p = c10 ∨ p = c11 ∨ p = c20 ∨ p = c21 ∨ p = c22 ∨ p = c30 ∨ p = c31 ∨ p = c32 ∨ p = c33 := by
  revert p
  decide

theorem span {n : ℕ} (f : Cell → Fin (n + 1)) (hf : Good f) (p q : Cell) :
    (f p : ℤ) ≤ f q + 3 := by
  have e0 := abs_le.mp (hf c00 c10 (by unfold Adj; decide))
  have e1 := abs_le.mp (hf c00 c11 (by unfold Adj; decide))
  have e2 := abs_le.mp (hf c10 c11 (by unfold Adj; decide))
  have e3 := abs_le.mp (hf c10 c20 (by unfold Adj; decide))
  have e4 := abs_le.mp (hf c10 c21 (by unfold Adj; decide))
  have e5 := abs_le.mp (hf c11 c20 (by unfold Adj; decide))
  have e6 := abs_le.mp (hf c11 c21 (by unfold Adj; decide))
  have e7 := abs_le.mp (hf c11 c22 (by unfold Adj; decide))
  have e8 := abs_le.mp (hf c20 c21 (by unfold Adj; decide))
  have e9 := abs_le.mp (hf c20 c30 (by unfold Adj; decide))
  have e10 := abs_le.mp (hf c20 c31 (by unfold Adj; decide))
  have e11 := abs_le.mp (hf c21 c22 (by unfold Adj; decide))
  have e12 := abs_le.mp (hf c21 c30 (by unfold Adj; decide))
  have e13 := abs_le.mp (hf c21 c31 (by unfold Adj; decide))
  have e14 := abs_le.mp (hf c21 c32 (by unfold Adj; decide))
  have e15 := abs_le.mp (hf c22 c31 (by unfold Adj; decide))
  have e16 := abs_le.mp (hf c22 c32 (by unfold Adj; decide))
  have e17 := abs_le.mp (hf c22 c33 (by unfold Adj; decide))
  have e18 := abs_le.mp (hf c30 c31 (by unfold Adj; decide))
  have e19 := abs_le.mp (hf c31 c32 (by unfold Adj; decide))
  have e20 := abs_le.mp (hf c32 c33 (by unfold Adj; decide))
  rcases cells p with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases cells q with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

open Classical in
theorem split_card (m : ℕ) :
    Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f} =
      Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∀ p, (f p : ℕ) ≤ m} +
      Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∃ p, (f p : ℕ) = m + 1} := by
  classical
  rw [← Fintype.card_subtype_or_disjoint]
  · exact Fintype.card_congr (Equiv.subtypeEquivRight fun f => by
      constructor
      · intro hf
        by_cases h : ∀ p, (f p : ℕ) ≤ m
        · exact Or.inl ⟨hf, h⟩
        · obtain ⟨p, hp⟩ := not_forall.mp h
          exact Or.inr ⟨hf, p, by have := (f p).2; omega⟩
      · rintro (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact hf)
  · rw [Pi.disjoint_iff]
    intro f
    rw [disjoint_iff]
    simp only [inf_Prop_eq, eq_iff_iff]
    constructor
    · rintro ⟨⟨-, h⟩, -, p, hp⟩
      have := h p
      omega
    · intro h
      exact h.elim

/-- Arrays with all entries at most `m` are the arrays with entries in `0..m`. -/
def lowEquiv (m : ℕ) :
    {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∀ p, (f p : ℕ) ≤ m} ≃
      {g : Cell → Fin (m + 1) // Good g} where
  toFun f := ⟨fun p => ⟨f.1 p, by have := f.2.2 p; omega⟩, fun p q h => by
    have := f.2.1 p q h
    simpa using this⟩
  invFun g := ⟨fun p => ⟨g.1 p, by have := (g.1 p).2; omega⟩, ⟨fun p q h => by
    have := g.2 p q h
    simpa using this, fun p => by have := (g.1 p).2; simp only; omega⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    rfl
  right_inv g := by
    apply Subtype.ext
    funext p
    rfl

/-- Arrays reaching the value `m + 1` are the translates of the arrays with entries in `0..3`
reaching `3` (all their entries are at least `m + 1 - 3`). -/
def highEquiv (m : ℕ) (hm : 2 ≤ m) :
    {f : Cell → Fin (m + 1 + 1) // Good f ∧ ∃ p, (f p : ℕ) = m + 1} ≃
      {g : Cell → Fin 4 // Good g ∧ ∃ p, (g p : ℕ) = 3} where
  toFun f := ⟨fun p => ⟨(f.1 p : ℕ) - (m - 2), by have := (f.1 p).2; omega⟩, by
    obtain ⟨hf, p0, hp0⟩ := f.2
    have lo : ∀ p, m - 2 ≤ (f.1 p : ℕ) := fun p => by
      have := span f.1 hf p0 p
      omega
    refine ⟨fun p q h => ?_, p0, ?_⟩
    · have := hf p q h
      have h1 := lo p
      have h2 := lo q
      dsimp only
      rw [abs_le] at this ⊢
      constructor <;> push_cast [h1, h2] <;> omega
    · dsimp only
      omega⟩
  invFun g := ⟨fun p => ⟨(g.1 p : ℕ) + (m - 2), by have := (g.1 p).2; omega⟩, by
    obtain ⟨hg, p0, hp0⟩ := g.2
    refine ⟨fun p q h => ?_, p0, ?_⟩
    · have := hg p q h
      dsimp only
      rw [abs_le] at this ⊢
      constructor <;> push_cast <;> omega
    · dsimp only
      omega⟩
  left_inv f := by
    obtain ⟨f, hf, p0, hp0⟩ := f
    apply Subtype.ext
    funext p
    apply Fin.ext
    have := span f hf p0 p
    dsimp only
    omega
  right_inv g := by
    apply Subtype.ext
    funext p
    apply Fin.ext
    dsimp only
    omega

open Classical in
theorem step (m : ℕ) (hm : 2 ≤ m) :
    (a (m + 1) : ℤ) = a m +
      Fintype.card {g : Cell → Fin 4 // Good g ∧ ∃ p, (g p : ℕ) = 3} := by
  classical
  unfold a
  rw [split_card, Fintype.card_congr (lowEquiv m), Fintype.card_congr (highEquiv m hm)]
  push_cast
  ring

end OMAA195234Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a195234.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have h1 := OMAA195234Helpers.step (m + 1) (by omega)
  have h2 := OMAA195234Helpers.step m (by omega)
  rw [show m + 1 + 1 = m + 2 by omega] at h1
  linarith
