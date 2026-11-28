import OMAStatements.S_oeis_a006531
import Mathlib

/-! Eventual periodicity of Bala's signed Stirling formula for labelled semiorders.
Finite differences make the eventual Euler period uniform in the Stirling index. -/
namespace Deldor14.Semiorders
open OMA.S_oeis_a006531 Finset

private def delta {R : Type*} [CommRing R] (f : ℕ → R) : ℕ → ℕ → R
  | 0,t => f t
  | k+1,t => delta f k (t+1) - delta f k t

private theorem deltaLinear {R : Type*} [CommRing R] (f : ℕ → R) (k t : ℕ) :
    delta (fun i => (i:R)*f i) (k+1) t =
    ((t:R)+k+1)*delta f (k+1) t+((k:R)+1)*delta f k t := by
  induction k generalizing t with
  | zero => simp [delta];ring
  | succ k ih =>
    change delta _ (k+1) (t+1)-delta _ (k+1) t=_
    rw [ih (t+1),ih t]
    simp only [delta,Nat.cast_add,Nat.cast_one,Nat.cast_succ]
    ring

private theorem deltaOne {R : Type*} [CommRing R] (k t : ℕ) :
    delta (fun _ => (1:R)) (k+1) t=0 := by
  induction k generalizing t with
  | zero => simp [delta]
  | succ k ih => change delta _ (k+1) (t+1)-delta _ (k+1) t=0;rw [ih,ih,sub_self]

private theorem deltaStirling (R : Type*) [CommRing R] (n k : ℕ) :
    delta (fun i : ℕ => (i:R)^n) k 0 = (k.factorial:R)*(Nat.stirlingSecond n k:R) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [delta]
    | succ k => simpa only [pow_zero,Nat.stirlingSecond_zero_succ,Nat.cast_zero,mul_zero] using deltaOne (R:=R) k 0
  | succ n ih =>
    cases k with
    | zero => simp [delta,Nat.stirlingSecond_succ_zero]
    | succ k =>
      simp only [pow_succ']
      rw [deltaLinear,ih,ih,Nat.stirlingSecond_succ_succ,Nat.factorial_succ]
      push_cast
      ring

private theorem powers (m : ℕ) (hm : 0 < m) : ∃ N : ℕ, ∀ n ≥ N, ∀ x T : ℕ,
    m.totient ∣ T → Nat.ModEq m (x^(n+T)) (x^n) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact ⟨0,fun _ _ _ _ _ => by simp only [Nat.ModEq,Nat.mod_one]⟩
  | prime_pow p k hp hk =>
    refine ⟨k,fun n hn x T hT => ?_⟩
    by_cases d : p ∣ x
    · have z (j : ℕ) (hj : k≤j) : p^k ∣ x^j := (pow_dvd_pow_of_dvd d k).trans (pow_dvd_pow x hj)
      exact (z (n+T) (by omega)).modEq_zero_nat.trans (z n hn).modEq_zero_nat.symm
    · obtain ⟨l,rfl⟩ := hT
      rw [mul_comm (p^k).totient l]
      exact Nat.pow_add_mul_totient_mod_eq (one_lt_pow₀ hp.one_lt hk.ne') ((hp.coprime_iff_not_dvd.mpr d).symm.pow_right k)
  | coprime a b ha hb hcp iha ihb =>
    obtain ⟨u,hu⟩ := iha (by omega)
    obtain ⟨v,hv⟩ := ihb (by omega)
    refine ⟨max u v,fun n hn x T d => (Nat.modEq_and_modEq_iff_modEq_mul hcp).mp ⟨?_,?_⟩⟩
    · exact hu n (by omega) x T ((Nat.totient_dvd_of_dvd (dvd_mul_right a b)).trans d)
    · exact hv n (by omega) x T ((Nat.totient_dvd_of_dvd (dvd_mul_left b a)).trans d)

private theorem stirling_eq (n k : ℕ) : stirling2 n k=Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp [stirling2,Nat.stirlingSecond,ih,add_comm]

private def summand (m n k : ℕ) : ZMod m :=
  (-1)^(n+k) * ((catalan k : ZMod m)*((k.factorial:ZMod m)*(Nat.stirlingSecond n k:ZMod m)))

private theorem cut (m n : ℕ) (hm : 0 < m) (hn : m ≤ n + 1) :
    (a n : ZMod m)=∑ k ∈ range m,summand m n k := by
  unfold a
  push_cast
  simp only [stirling_eq,mul_assoc]
  change (∑ k ∈ range (n+1),summand m n k)=_
  rw [show n+1=m+(n+1-m) by omega,sum_range_add]
  apply add_eq_left.mpr
  apply sum_eq_zero
  intro i _
  have z := (ZMod.natCast_eq_zero_iff (m+i).factorial m).mpr (Nat.dvd_factorial hm (by omega))
  simp [summand,z]

theorem result : type_of% @OMA.S_oeis_a006531.main := by
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨N,hN⟩ := powers m hm
  refine ⟨m.totient,max N m,Nat.totient_pos.mpr hm,dvd_rfl,fun n hn => ?_⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ m).mp
  rw [cut m (n+m.totient) hm (by omega),cut m n hm (by omega)]
  apply sum_congr rfl
  intro k _
  have point : (fun i : ℕ => (i : ZMod m)^(n+m.totient)) = (fun i : ℕ => (i : ZMod m)^n) := by
    funext i
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ m).mpr (hN n (by omega) i m.totient dvd_rfl)
  have sign : (-1:ZMod m)^m.totient=1 := by
    have e : (-(1 : (ZMod m)ˣ)) ^ Fintype.card (ZMod m)ˣ = 1 := pow_card_eq_one
    rw [ZMod.card_units_eq_totient] at e
    simpa only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one] using congrArg (fun u : (ZMod m)ˣ => (u:ZMod m)) e
  unfold summand
  rw [← deltaStirling,← deltaStirling,point,show n+m.totient+k=(n+k)+m.totient by omega,pow_add,sign,mul_one]
end Deldor14.Semiorders
theorem OMA.solution : type_of% @OMA.S_oeis_a006531.main := Deldor14.Semiorders.result
