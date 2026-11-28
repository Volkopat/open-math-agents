import Mathlib

/-!
# Lower bounds for a sum of products of singular values

Source: Adam, https://mathoverflow.net/questions/420936 (CC BY-SA 4.0).
Credit: @connoranderson.

The question's text names three matrices and its sums have four terms. We cover
every family size at least two. The author's comment confirms that the third
singular value is not involved. The mixed summand is factored using
nonnegativity of singular values. For every fixed pair of positive exponents,
the sharp power-mean lower bound uses the two-singular-value sum alone. No
positive uniform multiple of the proposed product bounds the mixed sum below,
even for invertible diagonal matrices in any fixed dimension at least two.
-/

namespace OMA.S_mo_420936

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
noncomputable def sv {d : ℕ} (A : Mat d) (j : ℕ) : ℝ := A.toEuclideanLin.singularValues j
noncomputable def pair {d : ℕ} (A : Mat d) (p : ℝ) : ℝ := (sv A 0 * sv A 1)^p
noncomputable def t1 {d m : ℕ} (A : Fin m → Mat d) (q : ℝ) : ℝ := ∑ i, (sv (A i) 0)^q
noncomputable def t2 {d m : ℕ} (A : Fin m → Mat d) (p : ℝ) : ℝ := ∑ i, pair (A i) p
noncomputable def mixed {d m : ℕ} (A : Fin m → Mat d) (p q : ℝ) : ℝ :=
  ∑ i, pair (A i) p * (sv (A i) 0)^q

theorem main : ∀ (d m : ℕ) (p q : ℝ), 0<p → 0<q →
    (∀ A : Fin (m+2) → Mat (d+2), (∀ i, IsUnit (A i)) →
      ((m:ℝ)+2)*(t2 A p / ((m:ℝ)+2))^(1+q/(2*p)) ≤ mixed A p q) ∧
    (let A : Fin (m+2) → Mat (d+2) := fun _ => 1
     ((m:ℝ)+2)*(t2 A p / ((m:ℝ)+2))^(1+q/(2*p)) = mixed A p q) ∧
    (∀ c : ℝ, 0<c → ∃ A : Fin (m+2) → Mat (d+2),
      (∀ i, IsUnit (A i) ∧ ∃ a : Fin (d+2) → ℝ, (∀ j, 0<a j) ∧ A i=Matrix.diagonal a) ∧
      mixed A p q < c*t2 A p*t1 A q) := by
  sorry

end OMA.S_mo_420936
