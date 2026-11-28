import FormalConjectures.Wikipedia.PierceBirkhoff

-- Reduction PierceBirkhoff.pierce_birkhoff_conjecture_dim_two.R1 of
-- PierceBirkhoff.pierce_birkhoff_conjecture_dim_two
-- Credit: @arindale

/-!
Mahé's proof has two parts.  The deep part (Mahé 1984, the "major–minor" separation
argument) says that for any two closed semialgebraic pieces `S, T` and polynomials
`p, q` with `p ≤ q` on `S ∩ T`, one can find a polynomial lying above `p` on `S` and
below `q` on `T`.  The second part is the elementary assembly: separating polynomials
`q i j` with `q i j ≥ g i` on `P i` and `q i j ≤ g j` on `P j`, and `q i i = g i`,
immediately give `f = sup_i inf_j q i j`.  We isolate both.
-/

namespace OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1

/-- Major–minor separation lemma (Mahé, 1984): two closed semialgebraic pieces with
compatible polynomials admit a polynomial that is above the first piece and below
the second. -/
def H1 : Prop :=
  ∀ (S T : Set (Fin 2 → ℝ)) (p q : MvPolynomial (Fin 2) ℝ),
    IsClosed S → IsClosed T →
    PierceBirkhoff.IsSemiAlgebraic S → PierceBirkhoff.IsSemiAlgebraic T →
    (∀ x, x ∈ S → x ∈ T → MvPolynomial.eval x p ≤ MvPolynomial.eval x q) →
    ∃ r : MvPolynomial (Fin 2) ℝ,
      (∀ x, x ∈ S → MvPolynomial.eval x p ≤ MvPolynomial.eval x r) ∧
      (∀ x, x ∈ T → MvPolynomial.eval x r ≤ MvPolynomial.eval x q)

/-- Assembly: separating polynomials give the `sup inf` representation. -/
def H2 : Prop :=
  ∀ (f : (Fin 2 → ℝ) → ℝ) (ι : Type) (P : ι → Set (Fin 2 → ℝ))
    (g : ι → MvPolynomial (Fin 2) ℝ) (q : ι → ι → MvPolynomial (Fin 2) ℝ),
    Finite ι →
    (∀ i, IsClosed (P i)) →
    (⋃ i, P i) = Set.univ →
    (∀ i, q i i = g i) →
    (∀ i j (x : Fin 2 → ℝ), x ∈ P i →
      MvPolynomial.eval x (g i) ≤ MvPolynomial.eval x (q i j)) →
    (∀ i j (x : Fin 2 → ℝ), x ∈ P j →
      MvPolynomial.eval x (q i j) ≤ MvPolynomial.eval x (g j)) →
    (∀ i (x : Fin 2 → ℝ), x ∈ P i → f x = MvPolynomial.eval x (g i)) →
    ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (q i j)

theorem main : H1 → H2 → type_of% @PierceBirkhoff.pierce_birkhoff_conjecture_dim_two := by
  intro h1 h2 f hf
  classical
  unfold PierceBirkhoff.IsPiecewiseMvPolynomial at hf
  obtain ⟨ι, P, g, hfin, hclosed, hsa, hcover, hpiece⟩ := hf
  have hcompat : ∀ i j (x : Fin 2 → ℝ), x ∈ P i → x ∈ P j →
      MvPolynomial.eval x (g i) ≤ MvPolynomial.eval x (g j) := by
    intro i j x hxS hxT
    rw [← hpiece i x hxS, ← hpiece j x hxT]
  let q : ι → ι → MvPolynomial (Fin 2) ℝ := fun i j =>
    if i = j then g i
    else Classical.choose
      (h1 (P i) (P j) (g i) (g j) (hclosed i) (hclosed j) (hsa i) (hsa j) (hcompat i j))
  have hdiag : ∀ i, q i i = g i := by
    intro i
    simp [q]
  have hmaj : ∀ i j (x : Fin 2 → ℝ), x ∈ P i →
      MvPolynomial.eval x (g i) ≤ MvPolynomial.eval x (q i j) := by
    intro i j x hx
    by_cases hij : i = j
    · rw [hij, hdiag j]
    · simp only [q, if_neg hij]
      exact (Classical.choose_spec
        (h1 (P i) (P j) (g i) (g j) (hclosed i) (hclosed j) (hsa i) (hsa j)
          (hcompat i j))).1 x hx
  have hmin : ∀ i j (x : Fin 2 → ℝ), x ∈ P j →
      MvPolynomial.eval x (q i j) ≤ MvPolynomial.eval x (g j) := by
    intro i j x hx
    by_cases hij : i = j
    · rw [hij, hdiag j]
    · simp only [q, if_neg hij]
      exact (Classical.choose_spec
        (h1 (P i) (P j) (g i) (g j) (hclosed i) (hclosed j) (hsa i) (hsa j)
          (hcompat i j))).2 x hx
  have hrepr : ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (q i j) :=
    h2 f ι P g q hfin hclosed hcover hdiag hmaj hmin hpiece
  exact ⟨ι, ι, q, hfin, hfin, hrepr⟩

end OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1
