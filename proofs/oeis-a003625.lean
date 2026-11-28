import OMAStatements.S_oeis_a003625

/-!
Federico Provvedi recorded the residue criterion on 21 July 2018 in OEIS A003625.
Source: https://oeis.org/A003625 (OEIS Foundation, CC BY-SA 4.0).

Completing the square gives discriminant −7. Quadratic reciprocity and the
supplement for −1 reduce its square class to that of the prime modulo 7.
-/

namespace OMA
open Polynomial

private theorem irreducible_quadratic_iff (p : ℕ) [Fact p.Prime] :
    Irreducible ((X : (ZMod p)[X]) ^ 2 + X + 2) ↔
      ¬ ∃ x : ZMod p, x ^ 2 + x + 2 = 0 := by
  let f : (ZMod p)[X] := X ^ 2 + X + 2
  have hdegree : f.natDegree = 2 := by
    have hconst : (2 : (ZMod p)[X]) = C 2 := rfl
    dsimp [f]
    rw [hconst, natDegree_add_C, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  have hnonzero : f ≠ 0 := by
    intro h
    simp [h] at hdegree
  change Irreducible f ↔ _
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (p := f) (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  simp [mem_roots hnonzero, IsRoot, f]

private theorem discriminant (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∃ x : ZMod p, x ^ 2 + x + 2 = 0) ↔ IsSquare (-7 : ZMod p) := by
  rw [isSquare_iff_exists_sq]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    linear_combination -4 * hx
  · rintro ⟨y, hy⟩
    let x := (y - 1) / 2
    refine ⟨x, ?_⟩
    have hxy : 2 * x + 1 = y := by
      dsimp [x]
      field_simp
      ring
    have hprod : (2 : ZMod p) ^ 2 * (x ^ 2 + x + 2) = 0 := by
      calc
        _ = (2 * x + 1) ^ 2 + 7 := by ring
        _ = 0 := by rw [hxy, ← hy, neg_add_cancel]
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ htwo)

private theorem reciprocity_seven (p : ℕ) [Fact p.Prime] [Fact (Nat.Prime 7)]
    (hp : p ≠ 2) : legendreSym p (-7) = legendreSym 7 p := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  have hqr : legendreSym p 7 = (-1) ^ (7 / 2 * (p / 2)) * legendreSym 7 p :=
    legendreSym.quadratic_reciprocity' (p := 7) (q := p) (by decide) hp
  rw [legendreSym.at_neg hp, hqr, ZMod.χ₄_eq_neg_one_pow hodd, ← mul_assoc, ← pow_add]
  have hexponent : p / 2 + 7 / 2 * (p / 2) = 2 * (2 * (p / 2)) := by omega
  rw [hexponent, pow_mul]
  norm_num

private theorem nonresidue_table : ∀ r : Fin 7,
    (r.val = 3 ∨ r.val = 5 ∨ r.val = 6) ↔
      ¬ ∃ y : ZMod 7, (r.val : ZMod 7) = y ^ 2 := by
  decide

private theorem nonresidues_mod_seven (n : ℕ) [Fact (Nat.Prime 7)] :
    (n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) ↔ legendreSym 7 n = -1 := by
  have hmod : legendreSym 7 n = legendreSym 7 (n % 7 : ℕ) := by
    rw [legendreSym.mod 7 (n : ℤ), Int.natCast_emod]
  rw [hmod, legendreSym.eq_neg_one_iff', isSquare_iff_exists_sq]
  exact nonresidue_table ⟨n % 7, Nat.mod_lt n (by decide)⟩

private theorem root_two : (0 : ZMod 2) + 0 + 2 = 0 := by decide

private theorem root_seven : (3 : ZMod 7) ^ 2 + 3 + 2 = 0 := by decide

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a003625.main := by
  intro p hp
  rw [OMA.irreducible_quadratic_iff]
  by_cases htwo : p = 2
  · subst p
    norm_num
    exact ⟨0, OMA.root_two⟩
  by_cases hseven : p = 7
  · subst p
    norm_num
    exact ⟨3, OMA.root_seven⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [OMA.discriminant p htwo]
  have hsymbol : legendreSym p (-7) = -1 ↔ ¬ IsSquare (-7 : ZMod p) := by
    simpa using (legendreSym.eq_neg_one_iff p (a := -7))
  rw [← hsymbol, OMA.reciprocity_seven p htwo]
  exact OMA.nonresidues_mod_seven p
