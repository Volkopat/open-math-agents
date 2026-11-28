import OMAStatements.S_oeis_a105877
import Mathlib

-- Credit: @erood (Lean proof with Codex)

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace OMA.A105877Proof

/-- The supplementary law for −1 and reciprocity for 5 depend only on r modulo 20. -/
private theorem residue_table (r : ℕ) (hr : r < 20)
    (h : ZMod.χ₄ (r % 4 : ℕ) * legendreSym 5 (r % 5 : ℕ) = -1) :
    r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 := by
  interval_cases r <;> first
    | decide
    | exfalso; revert h; norm_num [ZMod.χ₄_nat_eq_if_mod_four]

end OMA.A105877Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a105877.main := by
  intro p hp hlarge t hprim
  let : Fact p.Prime := ⟨hp⟩
  have hnz := hprim.ne_zero (by omega : p - 1 ≠ 0)
  have hns : ¬ IsSquare (-5 : ZMod p) := by
    intro hs
    have hs' := hs.mul (IsSquare.sq t)
    exact hprim.pow_ne_one_of_pos_of_lt (l := p / 2) (by omega) (by omega)
      ((ZMod.euler_criterion p hnz).mp hs')
  have hsym : legendreSym p (-5) = -1 :=
    (legendreSym.eq_neg_one_iff p).mpr (by simpa using hns)
  have hrec : legendreSym p 5 = legendreSym 5 (p : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by decide) (by omega)
  rw [legendreSym.at_neg (p := p) (by omega) 5, hrec, ZMod.χ₄_nat_mod_four p,
    legendreSym.mod 5 (p : ℤ)] at hsym
  have h4 : p % 4 = (p % 20) % 4 := by omega
  have h5 : (p : ℤ) % 5 = (((p % 20) % 5 : ℕ) : ℤ) := by omega
  have hres := OMA.A105877Proof.residue_table (p % 20) (Nat.mod_lt _ (by decide))
    (by simpa only [h4, h5, Nat.cast_ofNat] using hsym)
  refine ⟨hres, (p / 20) % 5, ?_⟩
  omega
