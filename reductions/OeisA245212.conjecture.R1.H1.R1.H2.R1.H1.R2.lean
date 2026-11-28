import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1
import Mathlib

/-! Distinct prime support restrictions for the odd low-totient branch of A245212. -/
open Nat

namespace A245212Triple

theorem small_support {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp3 : 3 ≤ p) (hpq : p<q) (hqr : q<r) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (h : 2*(p^a*q^b*r^c).totient < p^a*q^b*r^c) :
    p=3 ∧ q=5 ∧ (r=7 ∨ r=11 ∨ r=13) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  have hpq' := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hpr' := (Nat.coprime_primes hp hr).mpr (hpq.trans hqr).ne
  have hqr' := (Nat.coprime_primes hq hr).mpr hqr.ne
  rw [Nat.totient_mul ((hpr'.pow_left _).mul_left (hqr'.pow_left _) |>.pow_right _),
    Nat.totient_mul ((hpq'.pow_left _).pow_right _),
    Nat.totient_prime_pow_succ hp,Nat.totient_prime_pow_succ hq,
    Nat.totient_prime_pow_succ hr,pow_succ p a,pow_succ q b,pow_succ r c] at h
  have t : 2*((p-1)*(q-1)*(r-1)) < p*q*r := by
    apply (Nat.lt_of_mul_lt_mul_right (a := p^a*q^b*r^c))
    convert h using 1 <;> ring
  have g (x : ℕ) (k : ℕ) (hx : k ≤ x) (hk : 1 ≤ k) :
      (k-1)*x ≤ k*(x-1) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x≠0)
    simp only [Nat.add_one_sub_one]
    nlinarith
  have hp5 : p<5 := by
    by_contra! bad
    have le := Nat.mul_le_mul (Nat.mul_le_mul (g p 5 bad (by decide))
      (g q 5 (by omega) (by decide))) (g r 5 (by omega) (by decide))
    norm_num at le
    have le' : 64*(p*q*r) ≤ 125*((p-1)*(q-1)*(r-1)) := by convert le using 1 <;> ring
    omega
  have ep : p=3 := by
    have lemma5 : ∀ x : Fin 5, x.val.Prime → 3 ≤ x.val → x.val=3 := by decide
    exact lemma5 ⟨p,hp5⟩ hp hp3
  subst p
  have eq : q=5 := by
    by_contra bad
    have q7 : 7≤q := by
      by_contra! h
      have test : ∀ x : Fin 7, x.val.Prime → 3 < x.val → x.val=5 := by decide
      exact bad (test ⟨q,h⟩ hq hpq)
    have r11 : 11≤r := by
      by_contra! h
      have test : ∀ x : Fin 11, x.val.Prime → x.val≤7 := by decide
      have : r ≤ 7 := test ⟨r,h⟩ hr
      omega
    have le := Nat.mul_le_mul (g q 7 q7 (by decide)) (g r 11 r11 (by decide))
    norm_num at le t
    have le' : 60*(q*r) ≤ 77*((q-1)*(r-1)) := by convert le using 1 <;> ring
    have t' : 4*((q-1)*(r-1)) < 3*(q*r) := by convert t using 1 <;> ring
    omega
  subst q
  norm_num at t
  have r16 : r < 16 := by omega
  have test : ∀ x : Fin 16, x.val.Prime → 5<x.val → x.val=7 ∨ x.val=11 ∨ x.val=13 := by decide
  exact ⟨rfl,rfl,test ⟨r,r16⟩ hr hqr⟩
end A245212Triple
open Finset
namespace A245212Large


lemma prime_step {i x : ℕ} (hi : i<5) (hx : x.Prime) (h : ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i<x) : ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) (i+1)≤x := by
  by_contra! h'
  have bound : ∀ j : Fin 5, ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) (j.val+1) ≤ 19 := by decide
  have b : ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) (i+1) ≤ 19 := bound ⟨i,hi⟩
  have test : ∀ j : Fin 5, ∀ z : Fin 19, z.val.Prime → ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) j.val < z.val →
      ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) (j.val+1) ≤ z.val := by decide
  exact (not_le_of_gt h') (test ⟨i,hi⟩ ⟨x,h'.trans_le b⟩ hx h)

lemma lower_rank {k : ℕ} (hk : k≤6) (f : Fin k ↪o ℕ)
    (hp : ∀ j, (f j).Prime) (h5 : ∀ j, 5≤f j) (i : Fin k) : ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val ≤ f i := by
  have aux : ∀ j : ℕ, ∀ hj : j<k, ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) j≤f ⟨j,hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact h5 _
    | succ j ih =>
      intro hj
      have hj' : j<k := by omega
      exact prime_step (by omega) (hp _) ((ih hj').trans_lt (f.strictMono
        (show (⟨j,hj'⟩:Fin k) < ⟨j+1,hj⟩ from Nat.lt_succ_self j)))
  exact aux i.val i.isLt

lemma ratio_bound {k : ℕ} (hk : k ≤ 6) (f : Fin k ↪o ℕ)
    (hp : ∀ j, (f j).Prime) (h5 : ∀ j, 5≤f j) :
    (∏ i, f i) ≤ 2*∏ i, (f i-1) := by
  have pos : ∀ i : Fin k, 1 < ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val := fun i =>
    (show ∀ j : Fin 6, 1 < ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) j.val by decide) ⟨i.val,by omega⟩
  have one (i : Fin k) : (((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val-1)*f i ≤ ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val*(f i-1) := by
    have hi := lower_rank hk f hp h5 i
    have h := pos i
    zify [show 1≤((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val by omega,show 1≤f i by omega]
    nlinarith
  have le := Finset.prod_le_prod' (s:=Finset.univ) (fun i _ => one i)
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib] at le
  have cut : (∏ i : Fin k, ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val) ≤ 2*∏ i : Fin k, (((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val-1) :=
    (show ∀ j : Fin 7, (∏ i : Fin j.val, ((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val) ≤ 2*∏ i : Fin j.val, (((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val-1)
       by decide +kernel) ⟨k,by omega⟩
  have P : 0 < ∏ i : Fin k, (((fun i : ℕ => ([5,7,11,13,17,19] : List ℕ)[i]?.getD 23)) i.val-1) := Finset.prod_pos (fun i _ => by have := pos i; omega)
  apply Nat.le_of_mul_le_mul_left _ P
  exact le.trans ((Nat.mul_le_mul_right _ cut).trans_eq (by ring))

lemma sorted_prod {n k : ℕ} (h : n.primeFactors.card=k) (F : ℕ→ℕ) :
    (∏ i : Fin k, F (n.primeFactors.orderEmbOfFin h i)) = ∏ p ∈ n.primeFactors, F p := by
  conv_rhs => rw [← n.primeFactors.map_orderEmbOfFin_univ h]
  rw [Finset.prod_map]
  rfl

lemma many_without_three (n : ℕ) (hn : 1<n) (ho : Odd n) (h3 : ¬3∣n)
    (hφ : 2*n.totient<n) : 7≤n.primeFactors.card := by
  by_contra! small
  let f := n.primeFactors.orderEmbOfFin rfl
  have mem (i) : f i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem rfl i
  have pr (i) := Nat.prime_of_mem_primeFactors (mem i)
  have h5 (i) : 5 ≤ f i := by
    by_contra! h
    have test : ∀ x : Fin 5, x.val.Prime → x.val=2 ∨ x.val=3 := by decide
    have hd := Nat.dvd_of_mem_primeFactors (mem i)
    rcases test ⟨f i,h⟩ (pr i) with h2|ht
    · exact ho.not_two_dvd_nat (h2 ▸ hd)
    · exact h3 (ht ▸ hd)
  have bound := ratio_bound (show n.primeFactors.card≤6 by omega) f pr h5
  change (∏ i, (fun p : ℕ => p) (f i)) ≤ 2*∏ i, (fun p : ℕ => p-1) (f i) at bound
  dsimp only [f] at bound
  rw [sorted_prod (n := n) rfl (fun x => x), sorted_prod (n := n) rfl (fun x => x-1)] at bound
  have P : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have lt := Nat.mul_lt_mul_of_pos_right hφ P
  have le := Nat.mul_le_mul_left n bound
  have eq := Nat.totient_mul_prod_primeFactors n
  nlinarith only [lt,le,eq]
end A245212Large
namespace OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R2
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The three-prime case has exactly these possible supports. -/
def H1 : Prop := ∀ r a b c : ℕ, r ∈ ({7,11,13} : Finset ℕ) → 0<a → 0<b → 0<c →
  let n := 3^a*5^b*r^c
  OeisA245212.a n ≠ (σ 1 n : ℤ)

/-- Odd multiples of three with at least five distinct prime factors. -/
def H2 : Prop := ∀ n : ℕ, Odd n → 3∣n → 5≤n.primeFactors.card → 2*n.totient<n →
  OeisA245212.a n ≠ (σ 1 n : ℤ)

/-- Without three, a small totient requires at least seven distinct prime factors. -/
def H3 : Prop := ∀ n : ℕ, Odd n → ¬3∣n → 7≤n.primeFactors.card → 2*n.totient<n →
  OeisA245212.a n ≠ (σ 1 n : ℤ)

private lemma sorted_factors {n k : ℕ} (hn : 1<n) (ho : Odd n) (h3 : 3∣n)
    (hk : n.primeFactors.card=k) (hpos : 0<k) :
    ∃ (f : Fin k ↪o ℕ) (e : Fin k → ℕ), f ⟨0,hpos⟩ = 3 ∧
      (∀ i, (f i).Prime) ∧ (∀ i, 0<e i) ∧ n=∏ i, (f i)^(e i) := by
  let f := n.primeFactors.orderEmbOfFin hk
  have mem (i) : f i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem hk i
  have pr (i) := Nat.prime_of_mem_primeFactors (mem i)
  have m3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide,h3,by omega⟩
  have im : 3 ∈ Set.range f := by simpa [f] using m3
  obtain ⟨j,hj⟩ := im
  have u := f.monotone (show (⟨0,hpos⟩:Fin k)≤j from Nat.zero_le _)
  rw [hj] at u
  have l := (pr ⟨0,hpos⟩).two_le
  have ne : f ⟨0,hpos⟩ ≠ 2 := by
    intro h
    exact ho.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors (mem ⟨0,hpos⟩))
  refine ⟨f,fun i => n.factorization (f i),by omega,pr,
    fun i => (pr i).factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors (mem i)),?_⟩
  exact (Nat.prod_primeFactors_pow_factorization (by omega : n≠0)).trans
    (A245212Large.sorted_prod hk (fun x => x^n.factorization x)).symm

private lemma next_prime {x : ℕ} (h : 3<x) (hp : x.Prime) : 5≤x := by
  by_contra! hh
  have : x=4 := by omega
  subst x
  norm_num at hp

theorem main : H1 → H2 → H3 → OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1.H1 := by
  intro three many without n hn ho hnp hφ two four
  by_cases h3 : 3∣n
  case neg => exact without n ho h3 (A245212Large.many_without_three n hn ho h3 hφ) hφ
  by_cases big : 5≤n.primeFactors.card
  · exact many n ho h3 big hφ
  have lb := Finset.one_lt_card_iff_nontrivial.mpr ((Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hnp)
  have cases : n.primeFactors.card=2 ∨ n.primeFactors.card=3 ∨ n.primeFactors.card=4 := by omega
  rcases cases with h|h|h
  · obtain ⟨f,e,h0,pr,ep,form⟩ := sorted_factors hn ho h3 h (by decide)
    rw [Fin.prod_univ_two] at form
    change f 0 = 3 at h0
    have lt := f.strictMono (show (0:Fin 2)<1 by decide)
    have q5 := next_prime (by simpa only [h0] using lt) (pr 1)
    exact False.elim (two ⟨f 0,f 1,e 0,e 1,pr 0,pr 1,lt,by omega,q5,ep 0,ep 1,form⟩)
  · obtain ⟨f,e,h0,pr,ep,form⟩ := sorted_factors hn ho h3 h (by decide)
    rw [Fin.prod_univ_three] at form
    change f 0 = 3 at h0
    have lt := f.strictMono (show (0:Fin 3)<1 by decide)
    have lt' := f.strictMono (show (1:Fin 3)<2 by decide)
    have CL := A245212Triple.small_support (pr 0) (pr 1) (pr 2) (by omega) lt lt'
      (ep 0) (ep 1) (ep 2) (form ▸ hφ)
    obtain ⟨h₀,h₁,hr⟩ := CL
    rw [form,h₀,h₁]
    exact three _ _ _ _ (by simpa using hr) (ep 0) (ep 1) (ep 2)
  · obtain ⟨f,e,h0,pr,ep,form⟩ := sorted_factors hn ho h3 h (by decide)
    rw [Fin.prod_univ_four] at form
    change f 0 = 3 at h0
    have lt := f.strictMono (show (0:Fin 4)<1 by decide)
    have q5 := next_prime (by simpa only [h0] using lt) (pr 1)
    exact False.elim (four ⟨e 0,f 1,f 2,f 3,e 1,e 2,e 3,ep 0,pr 1,pr 2,pr 3,q5,
      f.strictMono (by decide),f.strictMono (by decide),ep 1,ep 2,ep 3,by simpa only [h0] using form⟩)

end OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R2
