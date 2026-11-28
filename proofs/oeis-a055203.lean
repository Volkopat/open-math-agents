import OMAStatements.S_oeis_a055203
import Mathlib

/-! Peter Bala's two periodicity conjectures for interval relations, using
Vladeta Jovovic's Stirling expansion. The finite-difference calculation works
over every commutative ring, so it also applies directly to composite moduli. -/
namespace Deldor14.IntervalRelations
open OMA.S_oeis_a055203 Finset

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

private def summand (m n k : ℕ) : ZMod m :=
  (k.factorial : ZMod m) * (Nat.stirlingSecond n k : ZMod m) * (weight k : ZMod m)
private theorem cut (m n K : ℕ) (h : K≤n+1) (hd : m ∣ K.factorial) :
    (term n : ZMod m)=∑ k ∈ range K,summand m n k := by
  unfold term
  push_cast
  change (∑ k ∈ range (n+1),summand m n k)=_
  rw [show n+1=K+(n+1-K) by omega,sum_range_add]
  apply add_eq_left.mpr
  apply sum_eq_zero
  intro i _
  have z := (ZMod.natCast_eq_zero_iff (K+i).factorial m).mpr (hd.trans (Nat.factorial_dvd_factorial (by omega)))
  simp [summand,z]

private theorem modTwelve (n : ℕ) : (term n : ZMod 12)=1 := by
  by_cases sm : n<3
  · interval_cases n <;> decide
  rw [cut 12 n 4 (by omega) (by decide)]
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  have wt₁ : weight 1=1 := by decide
  have wt₂ : weight 2=6 := by decide
  have wt₃ : weight 3=62 := by decide
  simp only [sum_range_succ,sum_range_zero,summand,Nat.stirlingSecond_succ_zero,
    Nat.stirlingSecond_one_right,Nat.cast_zero,Nat.cast_one,mul_zero,zero_mul,zero_add,wt₁,wt₂,wt₃]
  norm_num [Nat.factorial]
  ring_nf
  simp [show (12 : ZMod 12)=0 by decide,show (372 : ZMod 12)=0 by decide]

theorem result : type_of% @OMA.S_oeis_a055203.main := by
  refine ⟨modTwelve,?_⟩
  intro m hm
  obtain ⟨N,hN⟩ := powers m hm
  refine ⟨max N m,fun n hn => ?_⟩
  have dv := Nat.dvd_factorial hm (le_refl m)
  rw [cut m (n+m.totient) m (by omega) dv,cut m n m (by omega) dv]
  apply sum_congr rfl
  intro k _
  have point : (fun i : ℕ => (i : ZMod m)^(n+m.totient)) = (fun i : ℕ => (i : ZMod m)^n) := by
    funext i
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ m).mpr (hN n (by omega) i m.totient dvd_rfl)
  unfold summand
  rw [← deltaStirling,← deltaStirling,point]
end Deldor14.IntervalRelations
theorem OMA.solution : type_of% @OMA.S_oeis_a055203.main := Deldor14.IntervalRelations.result
