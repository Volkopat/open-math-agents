import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
OEIS A322844. The matrix is indexed from zero below; row i corresponds to
row i+1 of the source. The first expression is the sum of all principal
two by two minors. The higher exterior-power traces are represented by
their standard principal-minor sum formula.
Source: https://oeis.org/A322844
-/

namespace OMA.S_oeis_a322844

def entry (n i j : ℕ) : ℚ :=
  if i % 2 = 0 then (j : ℚ) + 1 + (n : ℚ) * i
  else (n : ℚ) * ((i : ℚ) + 1) - j

def principalTwo (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
    (entry n i i * entry n j j - entry n i j * entry n j i)

noncomputable def principalTrace (n k : ℕ) : ℚ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    Matrix.det (fun (i j : s) => entry n i.val.val j.val.val)

def formula (n : ℕ) : ℚ :=
  (n : ℚ)^2 * (3 * (1 + (n : ℚ)^2) - 2 * (2 + (n : ℚ)^2) * ((n % 2 : ℕ) : ℚ)) / 12

theorem main :
    (∀ n : ℕ, 1 < n → |principalTwo n| = formula n) ∧
    (∀ n k : ℕ, 2 < k → principalTrace n k = 0) := by
  sorry

end OMA.S_oeis_a322844
