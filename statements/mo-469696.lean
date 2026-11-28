import Mathlib

/-!
# Extremal eigenvalues of the Cauchy Gram matrix

Source: PIII, https://mathoverflow.net/questions/469696 (CC BY-SA 4.0).
Credit: @connoranderson.

Moving one real frequency weakly closer to each of the others weakly decreases
the least eigenvalue and weakly increases the greatest eigenvalue. This allows
repeated frequencies, including collisions. The second assertion gives the
ordered one-sided displacement asked for in the source. The nonnegativity
of that displacement matters: the two frequencies 0 and 1 have a smaller
least eigenvalue than the frequencies −1 and 1.
-/
namespace OMA.S_mo_469696
open Matrix Finset
open scoped ComplexOrder
abbrev Sq (ι : Type) := Matrix ι ι ℂ
noncomputable def K (x y : ℝ) : ℂ := (1-Complex.I*((y:ℂ)-x))⁻¹
noncomputable def gram {ι : Type} (x : ι → ℝ) : Sq ι := fun i j => K (x i) (x j)
noncomputable def bordered {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : Sq (Unit ⊕ Fin n) :=
  gram (Sum.elim (fun _ => t) x)

noncomputable def eigenvalue {n : ℕ} (t : ℝ) (x : Fin n → ℝ) (i : Unit ⊕ Fin n) : ℝ :=
  (show (bordered t x).IsHermitian by
    ext j k
    let y := Sum.elim (fun _ : Unit => t) x
    change star (K (y k) (y j)) = K (y j) (y k)
    simp [K]
    ring).eigenvalues i

noncomputable def leastEigen {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (eigenvalue t x)
noncomputable def greatestEigen {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (eigenvalue t x)

theorem main :
    (∀ (n : ℕ) (x : Fin n → ℝ) (s t : ℝ), (∀ j, |x j-s| ≤ |x j-t|) →
      leastEigen s x ≤ leastEigen t x ∧ greatestEigen t x ≤ greatestEigen s x) ∧
    (∀ (n : ℕ) (x : Fin n → ℝ) (t ε : ℝ), 0 ≤ ε → (∀ j, t+ε ≤ x j) →
      leastEigen (t+ε) x ≤ leastEigen t x) ∧
    leastEigen 0 (fun _ : Fin 1 => 1) < leastEigen (-1) (fun _ : Fin 1 => 1) := by
  sorry

end OMA.S_mo_469696
