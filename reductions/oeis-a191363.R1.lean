import OMAStatements.S_oeis_a191363
import Mathlib
namespace OMA.R_oeis_a191363_R1
open OMA.S_oeis_a191363 ArithmeticFunction

lemma sig_two (a : ℕ) : sigma 1 (2^a) + 1 = 2*2^a := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  simpa [pow_succ,Nat.mul_comm] using geom_sum_mul_add (1:ℕ) (a+1)

lemma prime_power (a q e : ℕ) (hp : q.Prime) (odd : Odd q) (he : 0<e)
    (ht : IsTerm (2^a*q^e)) : e=1 ∧ q=2*2^a+1 := by
  let s := ∑ i ∈ Finset.range e, q^i
  have cq := (Nat.coprime_two_left.mpr odd).pow_left a
  change sigma 1 (2^a*q^e)+2=2*(2^a*q^e) at ht
  rw [isMultiplicative_sigma.map_mul_of_coprime (cq.pow_right e),sigma_one_apply_prime_pow hp,
    Finset.sum_range_succ] at ht
  change sigma 1 (2^a)*(s+q^e)+2=2*(2^a*q^e) at ht
  have g : s*q+1=s+q^e := by
    have j := geom_sum_mul_add (q-1) e
    rw [Nat.sub_add_cancel hp.one_le] at j
    change s*(q-1)+1=q^e at j
    rw [Nat.mul_sub,Nat.mul_one] at j
    have ge : s ≤ s*q := Nat.le_mul_of_pos_right _ hp.pos
    omega
  have sg := sig_two a
  have eqn : s*q = (2*2^a)*s+1 := by
    nlinarith [congrArg (·*(q^e)) sg,congrArg (·*s) sg]
  have large : 2*2^a<q := by
    by_contra! h
    nlinarith [Nat.mul_le_mul_left s h]
  have one : s*(q-2*2^a)=1 := by rw [Nat.mul_sub,Nat.mul_comm s (2*2^a)]; omega
  have hs : s=1 := Nat.dvd_one.mp ⟨_,one.symm⟩
  have hq : q-2*2^a=1 := by simpa [hs] using one
  refine ⟨?_,by omega⟩
  by_contra! h
  have le : 2≤e := by omega
  have z : (∑ i ∈ Finset.range 2, q^i) ≤ s := Finset.sum_le_sum_of_subset (Finset.range_mono le)
  simp [Finset.sum_range_succ] at z
  omega

lemma shape (a q : ℕ) (hp : q.Prime) (hq : q=2*2^a+1) :
    ∃ k : ℕ, (2^(2^k)+1).Prime ∧ 2^a*q=(2^(2^k)+1-1)*(2^(2^k)+1)/2 := by
  have eqn : q=2^(a+1)+1 := by rw [pow_succ]; omega
  obtain ⟨k,hk⟩ := Nat.pow_of_pow_add_prime (by decide : 1<2) (Nat.succ_ne_zero a) (eqn ▸ hp)
  refine ⟨k,by rwa [←hk,←eqn],?_⟩
  rw [←hk,←eqn,show q-1=2*2^a by omega,Nat.mul_assoc]
  simp

lemma gap (a q : ℕ) (hp : q.Prime) (hq : q=2*2^a+1) :
    ¬ ∃ d : ℕ, d ∣ 2^a*q ∧ 2^a*q ≤ 2*d^2 ∧ d^2 < 2*(2^a*q) := by
  rintro ⟨d,div,lo,hi⟩
  obtain ⟨i,j,di,dj,rfl⟩ := Nat.dvd_mul.mp div
  have ip := Nat.le_of_dvd (by positivity : 0<2^a) di
  rcases (Nat.dvd_prime hp).mp dj with e|e
  · subst j
    simp only [Nat.mul_one] at lo
    nlinarith [Nat.mul_self_le_mul_self ip, pow_pos (by decide : 0<2) a]
  · subst j
    have iz : i≠0 := by rintro rfl; simp at di
    have le : q ≤ i*q := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith [Nat.mul_self_le_mul_self le]


lemma prime_restriction {a u b q : ℕ} (odd : Odd u) (gt : 1<u) (hp : q.Prime) (div : q∣u)
    (eqn : u=(2^(a+1)-1)*b+2) (sig : sigma 1 u=u+b) : 2^(a+1)<q := by
  obtain ⟨c,hc⟩ := div
  have cp : c≠0 := by rintro rfl; simp_all
  have csmall : c<u := by rw [hc]; nlinarith [hp.two_le, Nat.mul_le_mul_right c hp.two_le]
  have cmem : c∈u.divisors := Nat.mem_divisors.mpr ⟨⟨q,by rw [hc,Nat.mul_comm]⟩,by omega⟩
  have umem : u∈u.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _,by omega⟩
  have sub : ({u,c} : Finset ℕ) ⊆ u.divisors := by
    intro k h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact h.elim (fun eq => eq.symm ▸ umem) (fun eq => eq.symm ▸ cmem)
  have bound : u+c ≤ sigma 1 u := by
    rw [sigma_one_apply]
    simpa [Finset.sum_pair csmall.ne'] using (Finset.sum_le_sum_of_subset (f:=fun i : ℕ=>i) sub)
  have bc : c≤b := by omega
  let v := 2^(a+1)-1
  have ds : v*c≤v*b := Nat.mul_le_mul_left _ bc
  have lt : v<q := by
    by_contra! h
    have cmp := Nat.mul_le_mul_right c h
    change u=v*b+2 at eqn
    omega
  have vp : 0 < 2^(a+1) := by positivity
  change 2^(a+1)-1<q at lt
  have ne : 2^(a+1)≠q := by
    intro h
    have d2 : 2 ∣ q := h ▸ dvd_pow_self 2 (Nat.succ_ne_zero a)
    exact odd.not_two_dvd_nat (d2.trans ⟨c,hc⟩)
  omega

def H1 : Prop := ∀ u : ℕ, 1 < u → Odd u →
    (¬ ∃ q e : ℕ, q.Prime ∧ 0 < e ∧ u=q^e) → sigma 1 u + 2 ≠ 2*u

def H2 : Prop := ∀ a u b : ℕ, 0 < a → 1 < u → Odd u → 0 < b →
    (¬ ∃ q e : ℕ, q.Prime ∧ 0 < e ∧ u=q^e) →
    (∀ q : ℕ, q.Prime → q∣u → 2^(a+1)<q) →
    u = (2^(a+1)-1)*b+2 → sigma 1 u ≠ u+b

lemma classify (h1 : H1) (h2 : H2) (m : ℕ) (hm : IsTerm m) :
    ∃ a q : ℕ, q.Prime ∧ q=2*2^a+1 ∧ m=2^a*q := by
  have mn : m≠0 := by rintro rfl; simp [IsTerm] at hm
  obtain ⟨a,u,odd,fac⟩ := Nat.exists_eq_two_pow_mul_odd mn
  subst m
  have nz : u ≠ 0 := by rintro rfl; simp at odd
  have gt : 1 < u := by
    by_contra! small
    have : u=1 := by omega
    subst u
    simp only [Nat.mul_one,IsTerm] at hm
    have := sig_two a
    omega
  by_cases powers : ∃ q e : ℕ, q.Prime ∧ 0 < e ∧ u=q^e
  · obtain ⟨q,e,hq,he,rfl⟩ := powers
    have oq : Odd q := by
      apply hq.odd_of_ne_two
      rintro rfl
      have even : 2 ∣ 2^e := dvd_pow_self 2 (by omega)
      exact odd.not_two_dvd_nat even
    obtain ⟨rfl,form⟩ := prime_power a q e hq oq he hm
    exact ⟨a,q,hq,form,by simp⟩
  · by_cases az : a=0
    · subst a
      exact (h1 u gt odd powers (by simpa [IsTerm] using hm)).elim
    change sigma 1 (2^a*u)+2=2*(2^a*u) at hm
    rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_two_left.mpr odd).pow_left a)] at hm
    have sig := sig_two a
    have ev : sigma 1 (2^a)*sigma 1 u+2=sigma 1 (2^a)*u+u := by nlinarith [congrArg (·*u) sig]
    have ug : 2<u := by
      by_contra! h
      have : u=2 := by omega
      subst u; norm_num at odd
    have grow : u<sigma 1 u := by
      by_contra! h
      have := Nat.mul_le_mul_left (sigma 1 (2^a)) h
      omega
    let b := sigma 1 u-u
    have xb : sigma 1 u=u+b := by dsimp [b]; omega
    have sz : sigma 1 (2^a)=2^(a+1)-1 := by rw [pow_succ]; omega
    have eqn : u=(2^(a+1)-1)*b+2 := by rw [←sz]; rw [xb,Nat.mul_add] at ev; omega
    exact (h2 a u b (by omega) gt odd (by dsimp [b]; omega) powers (fun _ hp dv => prime_restriction odd gt hp dv eqn xb) eqn xb).elim

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a191363.main := by
  intro h1 h2
  refine ⟨?_,?_,?_,?_⟩
  · intro m hm ho
    obtain ⟨a,q,hp,hq,rfl⟩ := classify h1 h2 m hm
    cases a with
    | zero => simpa using hq
    | succ a =>
      exact (ho.not_two_dvd_nat ((dvd_pow_self 2 (Nat.succ_ne_zero a)).trans (dvd_mul_right _ q))).elim
  · intro m hm
    obtain ⟨a,q,hp,hq,rfl⟩ := classify h1 h2 m hm
    exact shape a q hp hq
  · intro m hm
    obtain ⟨a,q,hp,hq,rfl⟩ := classify h1 h2 m hm
    exact ⟨2^a,by rw [←hq]⟩
  · intro m hm
    obtain ⟨a,q,hp,hq,rfl⟩ := classify h1 h2 m hm
    exact gap a q hp hq
end OMA.R_oeis_a191363_R1
