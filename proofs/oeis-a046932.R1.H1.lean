import OMAReductions.R_oeis_a046932_R1

/-!
Let q = 2^m. In the quotient by the long trinomial, let r be the class of X
and let T send y to r * y^q. The n-th iterate of T at 1 is r to the
geometric sum 1 + q + ... + q^(n-1). Thus the short trinomial in T
annihilates 1. Evaluating the short trinomial's period at T produces a
period for the long trinomial. The least period divides that period.

For m = 1, the divisibility is Proposition 2.4 in Laurent Bartholdi,
“Lamps, factorizations, and finite fields” (arXiv:math/9910056).
The general statement appears as the first divisibility direction of Max
Alekseyev's conjecture in https://oeis.org/A046932.
-/

namespace OMA

open Polynomial
open OMA.S_oeis_a046932 OMA.R_oeis_a046932_R1

private noncomputable abbrev trinomial (n : ℕ) : (ZMod 2)[X] := X ^ n + X + 1

private theorem add_one_eq_zero_iff (f : (ZMod 2)[X]) (x : AdjoinRoot f) :
    x + 1 = 0 ↔ x = 1 := by
  have h : (1 : AdjoinRoot f) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using
      congrArg (algebraMap (ZMod 2) (AdjoinRoot f)) (show (1 : ZMod 2) + 1 = 0 by decide)
  have hi : -(1 : AdjoinRoot f) = 1 := by
    apply neg_eq_of_add_eq_zero_left
    exact h
  rw [← eq_neg_iff_add_eq_zero, hi]

private theorem period_iff (f : (ZMod 2)[X]) (s : ℕ) :
    f ∣ X ^ s + 1 ↔ AdjoinRoot.root f ^ s = 1 := by
  rw [← AdjoinRoot.mk_eq_zero, map_add, map_pow, map_one]
  exact add_one_eq_zero_iff f _

private theorem least_period_dvd (n s : ℕ) (hs : 0 < s)
    (hp : trinomial n ∣ X ^ s + 1) : a n ∣ s := by
  let r := AdjoinRoot.root (trinomial n)
  have hrs : r ^ s = 1 := (period_iff _ s).mp hp
  have ho : 0 < orderOf r :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨s, hs, hrs⟩).orderOf_pos
  have he : a n = orderOf r := by
    apply le_antisymm
    · exact Nat.sInf_le ⟨ho, (period_iff _ _).mpr (pow_orderOf_eq_one r)⟩
    · have hne : {j : ℕ | 0 < j ∧ trinomial n ∣ X ^ j + 1}.Nonempty := ⟨s, hs, hp⟩
      have ha : 0 < a n ∧ trinomial n ∣ X ^ a n + 1 := Nat.sInf_mem hne
      exact Nat.le_of_dvd ha.1 (orderOf_dvd_of_pow_eq_one ((period_iff _ _).mp ha.2))
  rw [he]
  exact orderOf_dvd_of_pow_eq_one hrs

private theorem transfer_period : H1 := by
  intro k m _ hm
  by_cases ha : a k = 0
  · simp [ha]
  have hshort : trinomial k ∣ X ^ a k + 1 := by
    let periods : Set ℕ := {j : ℕ | 0 < j ∧ trinomial k ∣ X ^ j + 1}
    have hn : periods.Nonempty := by
      by_contra! he
      apply ha
      change sInf periods = 0
      rw [he, Nat.sInf_empty]
    exact (Nat.sInf_mem hn).2
  have hq : 2 ≤ (2 : ℕ) ^ m := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm)
  have geom (j : ℕ) :
      (∑ i ∈ Finset.range j, ((2 : ℕ) ^ m) ^ i) = (2 ^ (j * m) - 1) / (2 ^ m - 1) := by
    rw [Nat.geomSum_eq hq, ← pow_mul, Nat.mul_comm m j]
  let n := (2 ^ (k * m) - 1) / (2 ^ m - 1)
  let s := (2 ^ (a k * m) - 1) / (2 ^ m - 1)
  change a n ∣ s
  have hs : 0 < s := by
    dsimp only [s]
    rw [← geom]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero ha
    rw [hj, Finset.sum_range_succ']
    simp
  apply least_period_dvd n s hs
  let f := trinomial n
  let r := AdjoinRoot.root f
  apply (period_iff f s).mpr
  change r ^ s = 1
  let R := AdjoinRoot f
  by_cases hn : Nontrivial R
  · let _ : Nontrivial R := hn
    let _ : CharP R 2 := CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) R) 2 (by decide)
    let T : Module.End (ZMod 2) R :=
      (((AddMonoidHom.mulLeft r).comp (iterateFrobenius R 2 m).toAddMonoidHom)).toZModLinearMap 2
    have hT (x : R) : T x = r * x ^ ((2 : ℕ) ^ m) := rfl
    have hpower (j : ℕ) :
        (T ^ j) 1 = r ^ ∑ i ∈ Finset.range j, ((2 : ℕ) ^ m) ^ i := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, hT, ih, ← pow_mul]
        have hsum : (∑ i ∈ Finset.range (j + 1), ((2 : ℕ) ^ m) ^ i) =
            1 + (∑ i ∈ Finset.range j, ((2 : ℕ) ^ m) ^ i) * 2 ^ m := by
          rw [Finset.sum_range_succ', Finset.sum_mul]
          simp only [pow_zero, pow_succ]
          omega
        rw [hsum, pow_add, pow_one]
    let E : (ZMod 2)[X] →ₐ[ZMod 2] Module.End (ZMod 2) R := Polynomial.aeval T
    have hX : E X = T := Polynomial.aeval_X T
    have hmk : r ^ n + r + 1 = 0 := by
      change (AdjoinRoot.mk f X) ^ n + AdjoinRoot.mk f X + 1 = 0
      simpa only [trinomial, map_add, map_pow, map_one] using
        (show AdjoinRoot.mk f (trinomial n) = 0 from AdjoinRoot.mk_self)
    have hf : E (trinomial k) 1 = 0 := by
      simp only [trinomial, map_add, map_pow, map_one, hX, LinearMap.add_apply, Module.End.one_apply]
      rw [hpower, geom, hT, one_pow, mul_one]
      exact hmk
    obtain ⟨g, hg⟩ := hshort
    have hperiod : E (X ^ a k + 1) 1 = 0 := by
      rw [hg, mul_comm (trinomial k) g, map_mul, Module.End.mul_apply, hf, map_zero]
    simp only [map_add, map_pow, map_one, hX, LinearMap.add_apply, Module.End.one_apply] at hperiod
    rw [hpower, geom] at hperiod
    exact (add_one_eq_zero_iff f _).mp hperiod
  · exact (not_nontrivial_iff_subsingleton.mp hn).elim _ _

end OMA

theorem OMA.solution : OMA.R_oeis_a046932_R1.H1 := OMA.transfer_period

