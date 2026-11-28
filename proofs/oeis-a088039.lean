import OMAStatements.S_oeis_a088039
import Mathlib

namespace OMA.CubeRoots88039

open OMA.S_oeis_a088039
open PowerSeries

private theorem size_five (n : ℕ) (hn : 3 ≤ n) :
    (2^n)^2 + 2^n + 1 < (5:ℕ)^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ (2:ℕ), pow_succ (5:ℕ)]
    nlinarith

private theorem size_three (s : ℕ) (hs : 2 ≤ s) : (2:ℕ)^(s+1) ≤ 3^s := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs ih =>
    rw [pow_succ 2 (s+1),pow_succ 3 s]
    omega

private theorem lower (n k : ℕ) (hn : 3 ≤ n) (hk : k ∈ candidates n) : 2^n < k := by
  obtain ⟨hk,b,hb,hd⟩ := hk
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hm : 0 < m := by omega
  let p := b.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have fact : (m+1)^3-1 = m*(m*m+3*m+3) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [fact] at hd
  have pd : p^n ∣ m*(m*m+3*m+3) := (pow_dvd_pow_of_dvd (Nat.minFac_dvd b) n).trans hd
  have modp : p ∣ m*(m*m+3*m+3) :=
    (dvd_pow_self p (by omega : n ≠ 0)).trans pd
  by_cases hpm : p ∣ m
  · by_cases h3 : p = 3
    · obtain ⟨u,hu⟩ := hpm
      rw [h3] at hu pd
      let r := 3*u*u + 3*u + 1
      have hr : ¬ (3:ℕ) ∣ r := by
        dsimp [r]
        rw [Nat.dvd_iff_mod_eq_zero]
        simp [Nat.add_mod,Nat.mul_mod]
      have eq : m*(m*m+3*m+3) = (m*3)*r := by rw [hu]; dsimp [r]; ring
      rw [eq] at pd
      have d := (Nat.prime_iff.mp Nat.prime_three).pow_dvd_of_dvd_mul_right n hr pd
      cases n with
      | zero => omega
      | succ s =>
        rw [pow_succ] at d
        have div : 3^s ∣ m := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 3) d
        have le := Nat.le_of_dvd hm div
        have small := size_three s (by omega)
        omega
    · have no : ¬ p ∣ m*m+3*m+3 := by
        intro h
        have d : p ∣ m*m+3*m :=
          dvd_add (dvd_mul_of_dvd_left hpm _) (dvd_mul_of_dvd_right hpm _)
        have three : p ∣ 3 := (Nat.dvd_add_iff_right d).mpr h
        exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp three)
      have d := (Nat.prime_iff.mp hp).pow_dvd_of_dvd_mul_right n no pd
      have h := (Nat.pow_le_pow_left hp.two_le n).trans (Nat.le_of_dvd hm d)
      omega
  · have d := (Nat.prime_iff.mp hp).pow_dvd_of_dvd_mul_left n hpm pd
    have smallPrime : 5 ≤ p := by
      by_contra! h
      have low := hp.two_le
      have factor : p ∣ m*m+3*m+3 := (hp.dvd_mul.mp modp).resolve_left hpm
      interval_cases p
      · have odd : m%2 = 1 := by omega
        rw [Nat.dvd_iff_mod_eq_zero] at factor
        simp [Nat.add_mod,Nat.mul_mod,odd] at factor
      · have rem := Nat.mod_lt m (by decide : 0 < 3)
        rw [Nat.dvd_iff_mod_eq_zero] at factor hpm
        rcases (by omega : m%3=1 ∨ m%3=2) with e|e <;>
          simp [Nat.add_mod,Nat.mul_mod,e] at factor
      · norm_num at hp
    by_contra! contra
    have lo := (Nat.pow_le_pow_left smallPrime n).trans (Nat.le_of_dvd (by positivity) d)
    have high := size_five n hn
    nlinarith [Nat.mul_self_le_mul_self contra]

private theorem tail (n : ℕ) (hn : 3 ≤ n) : a n = 2^n+1 := by
  have mem : 2^n+1 ∈ candidates n := by
    refine ⟨Nat.succ_lt_succ (pow_pos (by decide) n), 2, by decide, ?_⟩
    refine ⟨(2^n)^2+3*2^n+3, ?_⟩
    apply Nat.sub_eq_of_eq_add
    ring
  simp only [a, if_neg (by omega : n ≠ 0)]
  exact le_antisymm (Nat.sInf_le mem)
    (by have := lower n _ hn (Nat.sInf_mem (show (candidates n).Nonempty from ⟨_,mem⟩)); omega)

private theorem one : a 1 = 2 := by
  have mem : 2 ∈ candidates 1 := ⟨by decide,7,by decide,by decide⟩
  simp only [a, if_neg (by decide : 1 ≠ 0)]
  refine le_antisymm (Nat.sInf_le mem) ?_
  exact (Nat.sInf_mem (show (candidates 1).Nonempty from ⟨_,mem⟩)).1

private theorem two : a 2 = 4 := by
  have mem : 4 ∈ candidates 2 := ⟨by decide,3,by decide,by decide⟩
  simp only [a,if_neg (by decide : 2 ≠ 0)]
  refine le_antisymm (Nat.sInf_le mem) ?_
  obtain ⟨hk,b,hb,hd⟩ := Nat.sInf_mem (show (candidates 2).Nonempty from ⟨_,mem⟩)
  generalize sInf (candidates 2) = k at *
  by_contra! h
  have pos : 0 < k^3-1 := by interval_cases k <;> decide
  have small := Nat.le_of_dvd pos hd
  have bound : b ≤ 5 := by
    have t : k^3-1 ≤ 26 := by interval_cases k <;> decide
    nlinarith
  interval_cases k <;> interval_cases b <;> norm_num at hd

private theorem recurrence (n : ℕ) (h : 4 < n) :
    (a n : ℤ) = 3 * (a (n-1) : ℤ) - 2*(a (n-2) : ℤ) := by
  obtain ⟨k,hk⟩ : ∃ k, n = k+5 := ⟨n-5,by omega⟩
  rw [tail n (by omega),tail (n-1) (by omega),tail (n-2) (by omega)]
  rw [hk,show k+5-1 = k+4 by omega,show k+5-2=k+3 by omega]
  push_cast
  ring

private theorem generating :
    ((1-X)*(1-2*X)*mk (fun n => (a n : ℤ)) =
      2*X-2*X^2+X^3-2*X^4) := by
  let S := mk (fun n => (a n : ℤ))
  change _ * S = _
  have lhs : (1-X)*(1-2*X)*S =
      S - (3:ℕ) • (S*X^1) + (2:ℕ) • (S*X^2) := by
    simp only [nsmul_eq_mul]
    ring
  have rhs : (2*X-2*X^2+X^3-2*X^4 : PowerSeries ℤ) =
      (2:ℕ) • X^1 - (2:ℕ) • X^2 + X^3 - (2:ℕ) • X^4 := by
    simp [nsmul_eq_mul]
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 4 < n
  · have r := recurrence n h
    simp only [if_pos (show 1 ≤ n by omega),if_pos (show 2 ≤ n by omega),
      if_neg (show n ≠ 1 by omega),if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),if_neg (show n ≠ 4 by omega),
      nsmul_eq_mul]
    omega
  · have z : a 0 = 0 := by simp [a]
    have t3 := tail 3 (by decide)
    have t4 := tail 4 (by decide)
    interval_cases n <;> norm_num [z,one,two,t3,t4]

theorem result : type_of% @OMA.S_oeis_a088039.main :=
  ⟨tail,recurrence,generating⟩

end OMA.CubeRoots88039

theorem OMA.solution : type_of% @OMA.S_oeis_a088039.main := OMA.CubeRoots88039.result
