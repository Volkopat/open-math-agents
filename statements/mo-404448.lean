import Mathlib

/-!
# A Borel-measurable singular value decomposition

Source: Exodd, https://mathoverflow.net/questions/404448 (CC BY-SA 4.0).
Credit: @connoranderson.

For every pair of matrix dimensions, including zero dimensions, one Borel
function chooses both unitary factors and a rectangular nonnegative real
diagonal factor. The matrix space carries its usual Borel sigma algebra.
The admissible unitary pairs form nonempty compact fibers of a closed
relation. A continuous map from the real Cantor set onto the compact space
of unitary pairs lets us choose the least Cantor code in each fiber.
-/
namespace OMA.S_mo_404448
open Matrix Set
abbrev Rect (n m : ℕ) := Matrix (Fin n) (Fin m) ℂ
abbrev U (n : ℕ) := unitary (Rect n n)
abbrev Pair (n m : ℕ) := U n × U m
def diagOK {n m : ℕ} (D : Rect n m) : Prop :=
  (∀ i j, i.val≠j.val → D i j=0) ∧ ∀ i j, (D i j).im=0 ∧ 0≤(D i j).re
abbrev SigmaMat (n m : ℕ) := {D : Rect n m // diagOK D}
noncomputable def middle {n m : ℕ} (A : Rect n m) (q : Pair n m) : Rect n m :=
  (q.1 : Rect n n)ᴴ*A*(q.2 : Rect m m)
noncomputable instance rectMeasurableSpace (n m : ℕ) : MeasurableSpace (Rect n m) :=
  borel (Rect n m)
instance rectBorelSpace (n m : ℕ) : BorelSpace (Rect n m) := ⟨rfl⟩
theorem main : ∀ n m : ℕ,
    ∃ F : Rect n m → U n × SigmaMat n m × U m, Measurable F ∧
      ∀ A, A=((F A).1 : Rect n n)*((F A).2.1 : Rect n m)*((F A).2.2 : Rect m m)ᴴ := by
  sorry
end OMA.S_mo_404448
