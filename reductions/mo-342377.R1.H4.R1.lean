import OMAReductions.R_mo_342377_R1

-- Reduction mo-342377.R1.H4.R1 of step mo-342377.R1.H4
-- Credit: @thematthewdunlop-cpu

namespace OMA.R_mo_342377_R1_H4_R1

/-- For each fixed length the polynomial on the right is squarefree.
For l ≥ 6 its values have alternating signs on the half-integers
bracketing the roots of the rising factorial, since the product there
has magnitude at least (1/2 * 3/2 * 5/2)^2 > 9/4. For l = 5 use the
nonzero constant derivative modulo 5. Siegel's theorem then applies. -/
def H1 : Prop := ∀ l : ℕ, 5 ≤ l →
    Set.Finite {p : ℕ × ℕ | p.2 ^ 2 = 4 * Nat.ascFactorial p.1 l + 9}

/-- A uniform bound on lengths for which the polynomial takes a square value. -/
def H2 : Prop := ∃ B : ℕ, ∀ k l z : ℕ, 2 ≤ k → 5 ≤ l →
    z ^ 2 = 4 * Nat.ascFactorial k l + 9 → l ≤ B

theorem main : H1 → H2 → OMA.R_mo_342377_R1.H4 := by
  intro fixedLength boundedLength
  obtain ⟨B, hB⟩ := boundedLength
  let lengths := Finset.Icc 5 B
  let points (l : ℕ) := {p : ℕ × ℕ | p.2 ^ 2 = 4 * Nat.ascFactorial p.1 l + 9}
  let recover (l : ℕ) (p : ℕ × ℕ) : ℕ × ℕ × ℕ := ((p.2 - 1) / 2, p.1, l)
  have finiteUnion : (⋃ l : ↥lengths, recover l.val '' points l.val).Finite := by
    apply Set.finite_iUnion
    intro l
    exact (fixedLength l.val (Finset.mem_Icc.mp l.property).1).image (recover l.val)
  apply finiteUnion.subset
  rintro ⟨n, k, l⟩ ⟨hn, hk, hl, he⟩
  have sq : (2 * n + 1) ^ 2 = 4 * Nat.ascFactorial k l + 9 := by
    rw [← he]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    subst n
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  have hlB := hB k l (2 * n + 1) hk hl sq
  apply Set.mem_iUnion.mpr
  refine ⟨⟨l, Finset.mem_Icc.mpr ⟨hl, hlB⟩⟩, (k, 2 * n + 1), sq, ?_⟩
  change ((2 * n + 1 - 1) / 2, k, l) = (n, k, l)
  rw [show (2 * n + 1 - 1) / 2 = n by omega]

end OMA.R_mo_342377_R1_H4_R1
