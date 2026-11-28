import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
OEIS A208599, R. H. Hardin. Colin Barker's two conjectures of 7 March 2018.
Source: https://oeis.org/A208599
Credit: @jiyongparkphysics

Adding n to each label bijects integer labels in [-n,n] with Fin (2*n+1).
The zero-sum condition becomes total 5*n. This bijection commutes with rotations.
The cyclic group acts on positions; reflected configurations are counted separately
unless a rotation already identifies them. The OEIS series starts at n = 1.
-/

open scoped BigOperators

namespace OMA.S_oeis_a208599

abbrev BalancedWord (n : ℕ) :=
  {w : Fin 5 → Fin (2*n+1) // ∑ i, (w i).val = 5*n}

instance balancedRotation (n : ℕ) : AddAction (Fin 5) (BalancedWord n) where
  vadd g w := ⟨fun i => w.val (i + g), by
    exact (Equiv.sum_comp (Equiv.addRight g) (fun i => (w.val i).val)).trans w.property⟩
  zero_vadd w := by
    apply Subtype.ext
    funext i
    exact congrArg w.val (add_zero i)
  add_vadd g h w := by
    apply Subtype.ext
    funext i
    exact congrArg w.val (add_assoc i g h).symm

noncomputable def necklaceCount (n : ℕ) : ℕ :=
  Nat.card (Quotient (AddAction.orbitRel (Fin 5) (BalancedWord n)))

open PowerSeries

theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (necklaceCount n : ℚ))) *
        (1 - X)^5 = X * (11 + 22*X + 16*X^2 - 4*X^3 + X^4) ∧
    ∀ n : ℕ, 5 < n → (necklaceCount n : ℚ) =
      5*(necklaceCount (n-1) : ℚ) - 10*(necklaceCount (n-2) : ℚ) +
      10*(necklaceCount (n-3) : ℚ) - 5*(necklaceCount (n-4) : ℚ) +
      (necklaceCount (n-5) : ℚ) := by
  sorry

end OMA.S_oeis_a208599
