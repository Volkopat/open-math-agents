import Mathlib

/-!
# Five collinear points in a five-wide grid

Ron Hardin proposed this interpretation of A081200 on May 24, 2010.
Source: https://oeis.org/A081200 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a081200

abbrev Grid (k n : ℕ) := Fin n → Fin k

/-- A nonconstant direction through two points of the set contains every
point of the set precisely when all two-coordinate minors vanish. -/
def Collinear {k n : ℕ} (s : Finset (Grid k n)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∀ z ∈ s, ∀ i j : Fin n,
    ((z i : ℤ) - a i) * ((b j : ℤ) - a j) =
      ((z j : ℤ) - a j) * ((b i : ℤ) - a i)

/-- Count each unordered set of k distinct grid points once. -/
noncomputable def lineCount (k n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Finset (Grid k n) => s.card = k ∧ Collinear s)).card

def binomialTransform (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℤ) * f j

/-- A081200 is the sixth binomial transform of 0,1,0,1,... . -/
def a : ℕ → ℤ := binomialTransform^[6] (fun n => (n % 2 : ℕ))

theorem main : ∀ n : ℕ, (lineCount 5 n : ℤ) = a n := by
  sorry

end OMA.S_oeis_a081200
