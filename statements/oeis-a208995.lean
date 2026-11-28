import Mathlib

/-!
# OEIS A208995

Number of 4-bead necklaces labeled with numbers `-n..n` not allowing reversal,
with sum zero and first differences in `-n..n`.

Conjectured by Colin Barker (Jul 07 2018):
* for even `n ≥ 1`, `12 * a(n) = 4 * n^3 + 6 * n^2 + 8 * n + 12`,
* for odd `n ≥ 1`, `12 * a(n) = 4 * n^3 + 6 * n^2 + 8 * n + 6`.
-/

namespace OMA.S_oeis_a208995

/-- A 4-tuple `f : Fin 4 → ℤ` is valid for parameter `n` if its entries lie in `[-n, n]`,
its sum is `0`, and all cyclic first differences lie in `[-n, n]`. -/
def isValid (n : ℕ) (f : Fin 4 → ℤ) : Prop :=
  (∀ i : Fin 4, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧
  (f 0 + f 1 + f 2 + f 3 = 0) ∧
  (∀ i : Fin 4, -(n : ℤ) ≤ f (i + 1) - f i ∧ f (i + 1) - f i ≤ n)

/-- Cyclic rotation action of `Multiplicative (Fin 4)` on valid 4-tuples. -/
def rotAction (n : ℕ) : MulAction (Multiplicative (Fin 4)) {f : Fin 4 → ℤ // isValid n f} where
  smul g f := ⟨fun i => f.1 (i + Multiplicative.toAdd g), by
    rcases f.2 with ⟨hb, hsum, hd1⟩
    let k := Multiplicative.toAdd g
    refine ⟨fun i => hb (i + k), ?_, ?_⟩
    · generalize Multiplicative.toAdd g = k
      match k with
      | 0 => simp only [add_zero]; exact hsum
      | 1 => simp only [Fin.reduceAdd]; omega
      | 2 => simp only [Fin.reduceAdd]; omega
      | 3 => simp only [Fin.reduceAdd]; omega
    · intro i
      dsimp only
      have h := hd1 (i + k)
      have h1 : i + 1 + k = i + k + 1 := by abel
      rw [h1]; exact h⟩
  one_smul f := by
    apply Subtype.ext; ext i
    change f.1 (i + 0) = f.1 i
    rw [add_zero]
  mul_smul g h f := by
    apply Subtype.ext; ext i
    change f.1 (i + (Multiplicative.toAdd g + Multiplicative.toAdd h)) =
      f.1 (i + Multiplicative.toAdd g + Multiplicative.toAdd h)
    rw [add_assoc]

/-- `a(n)` is the number of 4-bead necklaces (not allowing reversal) with labels in `-n..n`,
sum zero, and first differences in `-n..n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := rotAction n
  Nat.card (MulAction.orbitRel.Quotient (Multiplicative (Fin 4)) {f : Fin 4 → ℤ // isValid n f})

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 12 * a n = 4 * n ^ 3 + 6 * n ^ 2 + 8 * n + 12) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 12 * a n = 4 * n ^ 3 + 6 * n ^ 2 + 8 * n + 6) := by
  sorry

end OMA.S_oeis_a208995
