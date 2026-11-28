import Mathlib

/-!
# Row sums of the quadratic Casimir coefficients for type A

A116863 lists the coefficients of the polynomial
(n+1) (a+2)ᵀ C⁻¹ a, where C is the type A Cartan matrix of rank n.
The sum of all these coefficients is its value at a=(1,...,1), hence
3(n+1) times the sum of every entry of C⁻¹. The Cartan matrix below
has diagonal 2, immediate off-diagonals -1, and all other entries zero.
The selectors use one-based labels inside a zero-based Fin n index.

A002415(k) is the four-dimensional pyramidal number k²(k²-1)/12.
The conjecture compares row n with three times A002415(n+1).
Sources: https://oeis.org/A116863 and https://oeis.org/A002415
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a116863

def selector {n : ℕ} (k : ℕ) (j : Fin n) : ℚ :=
  if j.val + 1 = k then 1 else 0

def cartan (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => 2 * selector (i.val+1) j - selector i.val j - selector (i.val+2) j

noncomputable def rowSum (n : ℕ) : ℚ :=
  3 * ((n : ℚ)+1) * ∑ i : Fin n, ∑ j : Fin n, (cartan n)⁻¹ i j

def pyramidal (k : ℕ) : ℚ := (k : ℚ)^2 * ((k : ℚ)^2-1) / 12

theorem main : ∀ n : ℕ, 0 < n → rowSum n = 3 * pyramidal (n+1) := by
  sorry

end OMA.S_oeis_a116863
