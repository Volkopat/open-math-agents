import OMAStatements.S_oeis_a140444
import Mathlib

open Polynomial

namespace OMA_A140444

theorem shifted_eq (R : Type*) [CommRing R] :
    OMA.S_oeis_a140444.shiftedQuotient R = taylor 1 (cyclotomic 7 R) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [cyclotomic_prime, taylor_apply, OMA.S_oeis_a140444.shiftedQuotient]
  simp

theorem irr : Irreducible (OMA.S_oeis_a140444.shiftedQuotient ℚ) := by
  rw [shifted_eq]
  exact (MulEquiv.irreducible_iff (taylorEquiv (1 : ℚ))).mpr (cyclotomic.irreducible_rat (by decide))

theorem shifted_eval (p : ℕ) (a : ZMod p) :
    (OMA.S_oeis_a140444.shiftedQuotient (ZMod p)).eval a =
      ∑ j ∈ Finset.range 7, (a+1)^j := by
  simp [OMA.S_oeis_a140444.shiftedQuotient, Polynomial.eval_finsetSum]

theorem shifted_roots_card (p : ℕ) [Fact p.Prime] [NeZero (7 : ZMod p)] :
    (Finset.univ.filter (fun a : ZMod p => (OMA.S_oeis_a140444.shiftedQuotient (ZMod p)).eval a = 0)).card =
      (primitiveRoots 7 (ZMod p)).card := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h (a : ZMod p) : (OMA.S_oeis_a140444.shiftedQuotient (ZMod p)).eval a = 0 ↔
      a+1 ∈ primitiveRoots 7 (ZMod p) := by
    rw [mem_primitiveRoots (by decide : 0 < 7), ← Polynomial.isRoot_cyclotomic_iff]
    simp [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime, shifted_eval, Polynomial.eval_finsetSum]
  exact Finset.card_equiv (Equiv.addRight 1) (fun a => by simpa using h a)

theorem seven_case : 7 % 14 = 1 ↔
    (Finset.univ.filter (fun a : ZMod 7 => (∑ j ∈ Finset.range 7, (a+1)^j) = 0)).card = 6 := by
  decide

theorem two_case : 2 % 14 = 1 ↔
    (Finset.univ.filter (fun a : ZMod 2 => (∑ j ∈ Finset.range 7, (a+1)^j) = 0)).card = 6 := by
  decide

theorem roots_part (p : ℕ) [hp : Fact p.Prime] : p % 14 = 1 ↔
    (Finset.univ.filter (fun a : ZMod p => (OMA.S_oeis_a140444.shiftedQuotient (ZMod p)).eval a = 0)).card = 6 := by
  by_cases same : p = 7
  · subst p
    simp_rw [shifted_eval]
    exact seven_case
  by_cases two : p = 2
  · subst p
    simp_rw [shifted_eval]
    exact two_case
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two two)
  have hp0 := hp.out.pos
  have hnp : ¬ p ∣ 7 := fun hd =>
    same (((show Nat.Prime 7 by decide).eq_one_or_self_of_dvd p hd).resolve_left hp.out.ne_one)
  letI : NeZero (7 : ZMod p) := ⟨fun h => hnp ((ZMod.natCast_eq_zero_iff 7 p).mp h)⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [shifted_roots_card]
  constructor
  · intro hmod
    have hd : 7 ∣ Fintype.card (ZMod p)ˣ := by rw [ZMod.card_units]; omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 7 hd
    have hprim : IsPrimitiveRoot (u : ZMod p) 7 :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
    rw [hprim.card_primitiveRoots, Nat.totient_prime (by decide : Nat.Prime 7)]
  · intro hcard
    have hpos : 0 < (primitiveRoots 7 (ZMod p)).card := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hprim := (mem_primitiveRoots (by decide : 0 < 7)).mp hz
    have hu := hprim.isUnit_unit (by decide : 7 ≠ 0)
    have hd := ZMod.orderOf_units_dvd_card_sub_one (hprim.isUnit (by decide)).unit
    rw [← hu.eq_orderOf] at hd
    omega

end OMA_A140444

theorem OMA.solution : type_of% @OMA.S_oeis_a140444.main :=
  ⟨OMA_A140444.irr, fun p _ => OMA_A140444.roots_part p⟩
