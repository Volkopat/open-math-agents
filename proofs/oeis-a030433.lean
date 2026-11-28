import OMAStatements.S_oeis_a030433
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.Ring

-- Formal proof of Federico Provvedi’s A030433 factorization criterion.
-- Original proof: @anmolspace (#7813); translation and characteristic-five steps simplified.

open Polynomial UniqueFactorizationMonoid
namespace OMA.P_oeis_a030433
open OMA.S_oeis_a030433

private theorem translate_normalize {K : Type*} [Field K] [DecidableEq K] (r : K) (f : K[X]) :
    normalize (taylorEquiv r f) = taylorEquiv r (normalize f) := by
  have hl : (taylorEquiv r f).leadingCoeff = f.leadingCoeff := leadingCoeff_taylor r f
  have hC (a : K) : taylorEquiv r (C a) = C a := taylor_C r a
  simp only [normalize_apply,Polynomial.coe_normUnit,map_mul,hl,hC]

private theorem shift_eq (p : ℕ) [Fact p.Prime] :
    shiftedQuotient p = taylorEquiv (1:ZMod p) (cyclotomic 5 (ZMod p)) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hx : taylorEquiv (1:ZMod p) X = X+1 := by
    change taylor _ X = _
    rw [taylor_X,map_one]
  simp only [shiftedQuotient,cyclotomic_prime,map_sum,map_pow,hx]

private theorem shift_card (p : ℕ) [Fact p.Prime] :
    (quadraticFactors p).card =
      ((normalizedFactors (cyclotomic 5 (ZMod p))).toFinset.filter (fun f => f.natDegree=2)).card := by
  classical
  let e := taylorEquiv (1:ZMod p)
  let q := cyclotomic 5 (ZMod p)
  let E := normalizedFactorsEquiv (f:=e) (translate_normalize _) q
  rw [quadraticFactors,shift_eq]
  symm
  refine Finset.card_equiv e.toEquiv (fun f => ?_)
  simp only [Finset.mem_filter, Multiset.mem_toFinset]
  constructor
  · rintro ⟨hf, hd⟩
    exact ⟨(E ⟨f, hf⟩).property, (natDegree_taylor f _).trans hd⟩
  · rintro ⟨hf, hd⟩
    exact ⟨by simpa [E, e] using (E.symm ⟨e f, hf⟩).property,
      (natDegree_taylor f _).symm.trans hd⟩

set_option maxHeartbeats 1000000 in
private theorem exceptional [Fact (Nat.Prime 5)] : (quadraticFactors 5).card = 0 := by
  classical
  have hc : cyclotomic 5 (ZMod 5) = (X - 1)^4 := by
    simpa using cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod 5) (p := 5) (n := 1) (by decide)
  have shift : shiftedQuotient 5 = (X : (ZMod 5)[X])^4 := by
    rw [shift_eq, hc]
    rw [map_pow, map_sub, map_one]
    change (taylor 1 X - 1)^4 = _
    simp [taylor_X]
  rw [quadraticFactors,shift,(irreducible_X (R:=ZMod 5)).normalizedFactors_pow]
  have normalX : normalize (X:(ZMod 5)[X]) = X := monic_X.normalize_eq_self
  simp [normalX]

private theorem order_two (p : ℕ) (hc : p.Coprime 5) :
    orderOf (ZMod.unitOfCoprime p hc)=2 ↔ p%5=4 := by
  let u := ZMod.unitOfCoprime p hc
  have table : ∀ v : (ZMod 5)ˣ, (v^2=1 ∧ v≠1) ↔ (v:ZMod 5)=4 := by decide +kernel
  rw [orderOf_eq_prime_iff,table]
  exact ZMod.natCast_eq_natCast_iff' p 4 5

theorem criterion (p : ℕ) [hp : Fact p.Prime] :
    p%10=9 ↔ (quadraticFactors p).card=2 := by
  classical
  by_cases he : p=5
  · subst p
    rw [exceptional]
    decide
  have hc : p.Coprime 5 := hp.out.coprime_iff_not_dvd.mpr (fun h =>
    he (((show Nat.Prime 5 by decide).eq_one_or_self_of_dvd p h).resolve_left hp.out.ne_one))
  let u := ZMod.unitOfCoprime p hc
  let A := (normalizedFactors (cyclotomic 5 (ZMod p))).toFinset
  have deg (f : (ZMod p)[X]) (hf : f ∈ A) : f.natDegree=orderOf u := by
    simpa [u] using (natDegree_of_mem_normalizedFactors_cyclotomic (p:=p) (f:=1)
      (K:=ZMod p) (by simp) hc (Multiset.mem_toFinset.mp hf))
  have card : A.card=4/orderOf u := by
    simpa [A,u,Nat.totient_prime (by decide : Nat.Prime 5)] using
      (normalizedFactors_cyclotomic_card (K:=ZMod p) (p:=p) (f:=1) (by simp) hc)
  rw [shift_card]
  change p%10=9 ↔ (A.filter (fun f => f.natDegree=2)).card=2
  have mod : p%10=9 ↔ p%5=4 := by
    rcases hp.out.eq_two_or_odd with h|h <;> omega
  rw [mod,← order_two p hc]
  change orderOf u=2 ↔ _
  by_cases h : orderOf u=2
  · rw [Finset.filter_true_of_mem (fun f hf => (deg f hf).trans h),card,h]
  · rw [Finset.filter_false_of_mem (fun f hf hd => h ((deg f hf).symm.trans hd))]
    simp [h]

end OMA.P_oeis_a030433
theorem OMA.solution : type_of% @OMA.S_oeis_a030433.main := by
  intro p hp
  exact OMA.P_oeis_a030433.criterion p
