import OMAStatements.S_oeis_a367175
import Mathlib

namespace OMA.A367175

open Finset

def s (n : ℕ) := ∑ x ∈ n.primeFactors, x
def sig (n : ℕ) := ∑ x ∈ n.divisors, x

theorem formula (n : ℕ) : S_oeis_a367175.a n = (sig n : ℤ) - 2 * (s n : ℤ) := by
  unfold S_oeis_a367175.a sig s
  rw [Nat.primeFactors_eq_to_filter_divisors_prime, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> push_cast <;> ring

theorem factor_sum_bound (n : ℕ) : s n ≤ n := by
  by_cases hn : n = 0
  · simp [hn, s]
  have h (S : Finset ℕ) (hS : ∀ x ∈ S, 2 ≤ x) : (∑ x ∈ S, x) ≤ ∏ x ∈ S, x := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      have h₁ : 2 ≤ a := hS _ (mem_insert_self ..)
      have h₂ : ∀ x ∈ S, 2 ≤ x := fun x hx => hS x (mem_insert_of_mem hx)
      by_cases hs : S = ∅
      · simp [hs]
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hx' : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (fun i _ => Nat.zero_le i) hx
      have hi := ih h₂
      rw [sum_insert ha, prod_insert ha]
      exact (Nat.add_le_add_left hi _).trans (Nat.add_le_mul h₁ ((h₂ x hx).trans (hx'.trans hi)))
  exact (h n.primeFactors (fun x hx => (Nat.prime_of_mem_primeFactors hx).two_le)).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

theorem small_sigma (n : ℕ) (hn : 1 < n) (hd : S_oeis_a367175.a n ∣ (sig n : ℤ)) :
    sig n ≤ 4 * s n := by
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hn
  have hs : 0 < s n := (Nat.pos_of_mem_primeFactors hp).trans_le
    (Finset.single_le_sum (fun i _ => Nat.zero_le i) hp)
  rw [formula] at hd
  by_contra! h
  have h' : (4:ℤ) * (s n : ℤ) < (sig n : ℤ) := by exact_mod_cast h
  have hs' : (0:ℤ) < s n := by exact_mod_cast hs
  have hd' : ((sig n : ℤ) - 2 * (s n : ℤ)) ∣ 2 * (s n : ℤ) := by
    have aux := dvd_sub hd (dvd_refl ((sig n : ℤ) - 2 * (s n : ℤ)))
    rwa [show (sig n : ℤ) - ((sig n : ℤ) - 2 * (s n : ℤ)) = 2 * (s n : ℤ) by omega] at aux
  have := Int.le_of_dvd (show (0:ℤ) < 2 * (s n : ℤ) by omega) hd'
  omega

theorem sigma_lower (n : ℕ) (hn : 0 < n) : n ≤ sig n :=
  Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors.mpr ⟨dvd_rfl, hn.ne'⟩)

theorem finite_check : ∀ i : Fin 69, 0 < i.val →
    (S_oeis_a367175.a i.val ∣ (sig i.val : ℤ) ↔
      i.val ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ)) := by
  decide +kernel

lemma small_cofactor_arithmetic (p q : ℕ) (hp : 11 ≤ p) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 6)
    (hd : (((p+1 : ℕ) * sig q : ℕ) : ℤ) - 2 * ((p + s q : ℕ) : ℤ) ∣ (((p+1 : ℕ) * sig q : ℕ) : ℤ)) : False := by
  have hpI : 11 ≤ (p : ℤ) := by exact_mod_cast hp
  interval_cases q
  · have hz : sig 1 = 1 := by decide +kernel
    have hs : s 1 = 0 := by decide +kernel
    rw [hz,hs] at hd
    push_cast at hd
    let x : ℤ := ((p : ℤ)+1)*1-2*((p : ℤ)+0)
    let v : ℤ := ((p : ℤ)+1)*1
    change x ∣ v at hd
    have h : -x ∣ v+x := neg_dvd.mpr (dvd_add hd (dvd_refl _))
    have hpos : 0 < v+x := by dsimp [v,x]; omega
    have hh := Int.le_of_dvd hpos h
    dsimp [v,x] at hh
    omega
  · have hz : sig 2 = 3 := by decide +kernel
    have hs : s 2 = 2 := by decide +kernel
    rw [hz,hs] at hd
    push_cast at hd
    let x : ℤ := ((p : ℤ)+1)*3-2*((p : ℤ)+2)
    let v : ℤ := ((p : ℤ)+1)*3
    change x ∣ v at hd
    have h : x ∣ v-3*x := dvd_sub hd (dvd_mul_left _ _)
    have hpos : 0 < v-3*x := by dsimp [v,x]; omega
    have hh := Int.le_of_dvd hpos h
    dsimp [v,x] at hh
    omega
  · have hz : sig 3 = 4 := by decide +kernel
    have hs : s 3 = 3 := by decide +kernel
    rw [hz,hs] at hd
    push_cast at hd
    let x : ℤ := ((p : ℤ)+1)*4-2*((p : ℤ)+3)
    let v : ℤ := ((p : ℤ)+1)*4
    change x ∣ v at hd
    have h : x ∣ v-2*x := dvd_sub hd (dvd_mul_left _ _)
    have hpos : 0 < v-2*x := by dsimp [v,x]; omega
    have hh := Int.le_of_dvd hpos h
    dsimp [v,x] at hh
    omega
  · have hz : sig 4 = 7 := by decide +kernel
    have hs : s 4 = 2 := by decide +kernel
    rw [hz,hs] at hd
    push_cast at hd
    let x : ℤ := ((p : ℤ)+1)*7-2*((p : ℤ)+2)
    let v : ℤ := ((p : ℤ)+1)*7
    change x ∣ v at hd
    have h : x ∣ v-1*x := dvd_sub hd (dvd_mul_left _ _)
    have hpos : 0 < v-1*x := by dsimp [v,x]; omega
    have hh := Int.le_of_dvd hpos h
    dsimp [v,x] at hh
    omega
  · have hz : sig 5 = 6 := by decide +kernel
    have hs : s 5 = 5 := by decide +kernel
    rw [hz,hs] at hd
    push_cast at hd
    let x : ℤ := ((p : ℤ)+1)*6-2*((p : ℤ)+5)
    let v : ℤ := ((p : ℤ)+1)*6
    change x ∣ v at hd
    have h : x ∣ v-1*x := dvd_sub hd (dvd_mul_left _ _)
    have hpos : 0 < v-1*x := by dsimp [v,x]; omega
    have hh := Int.le_of_dvd hpos h
    dsimp [v,x] at hh
    omega
  · have hz : sig 6 = 12 := by decide +kernel
    have hs : s 6 = 5 := by decide +kernel
    rw [hz,hs] at hd
    push_cast at hd
    let x : ℤ := ((p : ℤ)+1)*12-2*((p : ℤ)+5)
    let v : ℤ := ((p : ℤ)+1)*12
    change x ∣ v at hd
    have h : x ∣ v-1*x := dvd_sub hd (dvd_mul_left _ _)
    have hpos : 0 < v-1*x := by dsimp [v,x]; omega
    have hh := Int.le_of_dvd hpos h
    dsimp [v,x] at hh
    omega

lemma large_prime_bridge (p q : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hq : 0 < q)
    (hsq : s q ≤ q) (hsig : p*q ≤ sig (p*q)) (hsmall : sig (p*q) ≤ 4*s (p*q))
    (hd : (sig (p*q) : ℤ) - 2*(s (p*q) : ℤ) ∣ (sig (p*q) : ℤ))
    (exclude : ∀ u v : ℕ, 11 ≤ u → 1 ≤ v → v ≤ 6 →
      (((u+1 : ℕ) * sig v : ℕ) : ℤ) - 2 * ((u + s v : ℕ) : ℤ) ∣ (((u+1 : ℕ) * sig v : ℕ) : ℤ) → False) : False := by
  have hS : s (p*q) ≤ p + s q := by
    unfold s
    rw [Nat.primeFactors_mul hp.ne_zero hq.ne', hp.primeFactors]
    by_cases hl : p ∈ q.primeFactors
    · simp [hl]
    · simp [hl]
  have hq6 : q ≤ 6 := by
    by_contra! h
    have hg : 0 ≤ (p - 11 : ℕ) * (q - 7) := Nat.zero_le _
    have he : p-11+11=p := Nat.sub_add_cancel hp11
    have hf : q-7+7=q := Nat.sub_add_cancel h
    have big : 7 * p + 11 * q ≤ p*q + 77 := by nlinarith only [congrArg (fun x : ℕ => x*(q-7)) he, congrArg (fun x : ℕ => p*x) hf, congrArg (fun x : ℕ => 11*x) hf, hg]
    nlinarith only [big, hp11, h, hsig, hsmall, hS, hsq]
  have hqp : q < p := by omega
  have nd : ¬p ∣ q := Nat.not_dvd_of_pos_of_lt hq hqp
  have cop := hp.coprime_iff_not_dvd.mpr nd
  have hSeq : s (p*q) = p + s q := by
    unfold s
    rw [Nat.primeFactors_mul hp.ne_zero hq.ne', hp.primeFactors]
    have hn : p ∉ q.primeFactors := fun h => nd (Nat.dvd_of_mem_primeFactors h)
    simp [hn]
  have hσeq : sig (p*q) = (p+1) * sig q := by
    unfold sig
    rw [cop.sum_divisors_mul, hp.divisors]
    simp [hp.ne_one, hp.ne_one.symm, Nat.add_comm]
  rw [hSeq,hσeq] at hd
  exact exclude p q hp11 hq hq6 hd

lemma small_prime_bound (n : ℕ) (hs : ∀ p ∈ n.primeFactors, p < 11)
    (hnσ : n ≤ sig n) (hσ : sig n ≤ 4 * s n) : n ≤ 68 := by
  have ht : n.primeFactors ⊆ ({2,3,5,7} : Finset ℕ) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hlt := hs p hp
    interval_cases p <;> norm_num at *
  have hs17 : s n ≤ 17 := by
    calc
      s n ≤ ∑ p ∈ ({2,3,5,7} : Finset ℕ), p := Finset.sum_le_sum_of_subset_of_nonneg ht (by intros; omega)
      _ = 17 := by decide
  omega

lemma classify_from_no_large_prime (a : ℕ → ℤ)
    (hsig : ∀ n, 0 < n → n ≤ sig n)
    (hfour : ∀ n, 1 < n → a n ∣ (sig n : ℤ) → sig n ≤ 4 * s n)
    (hsmall : ∀ n, 1 < n → a n ∣ (sig n : ℤ) → ∀ p ∈ n.primeFactors, p < 11)
    (hcheck : ∀ i : Fin 69, 0 < i.val → (a i.val ∣ (sig i.val : ℤ) ↔
      i.val ∈ ({1,2,3,6,14,15,35} : Finset ℕ))) (n : ℕ) (hn : 0 < n) :
      a n ∣ (sig n : ℤ) ↔ n ∈ ({1,2,3,6,14,15,35} : Finset ℕ) := by
  by_cases ht : n < 69
  · exact hcheck ⟨n,ht⟩ hn
  have h1 : 1 < n := by omega
  constructor
  · intro hd
    have he := small_prime_bound n (hsmall n h1 hd) (hsig n hn) (hfour n h1 hd)
    omega
  · intro hm
    simp only [mem_insert, mem_singleton] at hm
    omega

lemma no_large_prime (n : ℕ) (hn : 1 < n) (hd : S_oeis_a367175.a n ∣ (sig n : ℤ))
    (p : ℕ) (hp : p ∈ n.primeFactors) : p < 11 := by
  by_contra! hp11
  have pp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mem_primeFactors hp
  have hq : 0 < q := by
    by_contra! hf
    have hz : q = 0 := by omega
    simp [hz] at hn
  have hsd := small_sigma (p*q) hn hd
  rw [formula] at hd
  exact large_prime_bridge p q pp hp11 hq (factor_sum_bound q)
    (sigma_lower (p*q) (by omega)) hsd hd small_cofactor_arithmetic

end OMA.A367175

theorem OMA.solution : type_of% @OMA.S_oeis_a367175.main :=
  OMA.A367175.classify_from_no_large_prime OMA.S_oeis_a367175.a
    OMA.A367175.sigma_lower OMA.A367175.small_sigma OMA.A367175.no_large_prime
    OMA.A367175.finite_check
