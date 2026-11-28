import Mathlib

/-!
# Square standard Young tableaux and the combinatorial factor in the zeta moments

Source: https://oeis.org/A039622 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson

Michael Somos identifies this count with the factor g_n in the conjectured 2n-th zeta moment.
Keating and Snaith give g_n = (n²)! times the product of j!/(n+j)! for 0 ≤ j < n.
The equation below clears its positive denominators. It includes the empty square.
-/

namespace OMA.S_oeis_a039622

/-- The square Young diagram with n rows and n columns. -/
def squareDiagram (n : ℕ) : YoungDiagram where
  cells := Finset.range n ×ˢ Finset.range n
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe,Finset.mem_product,Finset.mem_range] at hb ⊢
    exact ⟨lt_of_le_of_lt hab.1 hb.1,lt_of_le_of_lt hab.2 hb.2⟩

/-- Each of 0 through n²−1 occurs once. Distinct entries make every weak row strict. -/
noncomputable def tableaux (n : ℕ) : ℕ :=
  Nat.card {T : SemistandardYoungTableau (squareDiagram n) //
    (squareDiagram n).cells.val.map (fun p => T p.1 p.2) = Multiset.range (n^2)}

theorem main : ∀ n : ℕ,
    tableaux n * (∏ j ∈ Finset.range n, (n+j).factorial) =
      (n^2).factorial * (∏ j ∈ Finset.range n, j.factorial) := by
  sorry

end OMA.S_oeis_a039622
