import Mathlib

/-!
# Eigenvalues of leading Sylvester–Kac submatrices

Source: Sihuang Hu, https://mathoverflow.net/questions/255146
Credit: @connoranderson.

The displayed full matrix has n rows and upper diagonal n−1,...,1.
The binary Krawtchouk polynomial is given by its binomial generating
function. We identify the characteristic polynomial of the entire leading
block and give a two-sided absolute bound for its eigenvalues.
-/

namespace OMA.S_mo_255146

def clement (n r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j =>
  if j.val=i.val+1 then (n:ℂ)-1-i.val else if i.val=j.val+1 then i.val else 0

noncomputable def krawtchouk (n : ℕ) (z : ℂ) (r : ℕ) : ℂ :=
  PowerSeries.coeff r
    (PowerSeries.rescale (-1:ℂ) (PowerSeries.binomialSeries ℂ (((n:ℂ)-1-z)/2)) *
      PowerSeries.binomialSeries ℂ (((n:ℂ)-1+z)/2))

theorem main : ∀ (n r : ℕ), 1 < r → 2*r ≤ n → ∀ z : ℂ,
    (clement n r).charpoly.eval z = (r.factorial:ℂ)*krawtchouk n z r ∧
    ((clement n r).charpoly.eval z = 0 → ‖z‖ ≤ 2*Real.sqrt ((r:ℝ)*(n-r))) := by
  sorry
end OMA.S_mo_255146
