import FormalConjectures.ErdosProblems.«387»
import Mathlib

/-! Finite divisor classification for BNPZ, Section 6. -/
open Finset

namespace OMA.R_Erdos387_erdos_387_R1

theorem crossing (T : ℕ) (ht : 1 ≤ T) (l : List ℕ)
    (small : ∀ p ∈ l, p ≤ T) (large : T < l.prod) :
    ∃ a, a ∣ l.prod ∧ T<a ∧ a ≤ T^2 := by
  induction l with
  | nil => exact False.elim (not_lt.mpr ht large)
  | cons p l ih =>
    by_cases h : T<l.prod
    · obtain ⟨a,ha,lo,hi⟩ := ih (fun v hv => small v (by simp [hv])) h
      exact ⟨a, dvd_trans ha (by simp [List.prod_cons]),lo,hi⟩
    · refine ⟨_,dvd_rfl,large,?_⟩
      simpa [pow_two] using Nat.mul_le_mul (small p (by simp)) (le_of_not_gt h)

theorem almost_prime (T d : ℕ) (ht : 1 ≤ T) (hd : 0<d)
    (unsplit : ∀ r s : ℕ, d=r*s → r≤T ∨ s≤T) :
    ∃ f q, d=f*q ∧ f ≤ T^3 ∧ (q=1 ∨ q.Prime ∧ T<q) := by
  have t3 : T ≤ T^3 := by simpa using Nat.pow_le_pow_right (n := T) ht (by decide : 1≤3)
  by_cases h : ∃ q, q ∈ d.primeFactorsList ∧ T<q
  · obtain ⟨q,hq,large⟩ := h
    obtain ⟨f,hf⟩ := Nat.dvd_of_mem_primeFactorsList hq
    have hf' : d=f*q := hf.trans (Nat.mul_comm _ _)
    exact ⟨f,q,hf',((unsplit f q hf').resolve_right large.not_ge).trans t3,Or.inr ⟨Nat.prime_of_mem_primeFactorsList hq,large⟩⟩
  · refine ⟨d,1,by simp,?_,Or.inl rfl⟩
    by_contra! big
    obtain ⟨a,div,lo,hi⟩ := crossing T ht d.primeFactorsList
      (fun p hp => le_of_not_gt (fun gt => h ⟨p,hp,gt⟩)) (by rw [Nat.prod_primeFactorsList hd.ne']; omega)
    rw [Nat.prod_primeFactorsList hd.ne'] at div
    obtain ⟨b,hb⟩ := div
    have bs := (unsplit a b hb).resolve_left lo.not_ge
    have bm := Nat.mul_le_mul hi bs
    rw [←pow_succ,←hb] at bm; exact big.not_ge bm

theorem allocate {α : Type*} (s : Finset α) (c : α → ℕ) (d : ℕ) (hd : d ∣ ∏ i ∈ s,c i) :
    ∃ a : α → ℕ, d=(∏ i ∈ s, a i) ∧ ∀ i ∈ s, a i ∣ c i := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty =>
    simp at hd; subst d; exact ⟨fun _ => 1,by simp,by simp⟩
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi] at hd
    obtain ⟨v,w,hv,hw,eq⟩ := Nat.dvd_mul.mp hd
    obtain ⟨a,ha,div⟩ := ih w hw
    refine ⟨Function.update a i v,?_,?_⟩
    · rw [Finset.prod_insert hi,Function.update_self,Finset.prod_congr rfl (g := a) (fun j hj => Function.update_of_ne (by rintro rfl; exact hi hj) ..),←ha]
      omega
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji|hjmem
      · subst j; simpa using hv
      · have neq : j ≠ i := fun e => hi (e ▸ hjmem)
        rw [Function.update_of_ne neq]; exact div j hjmem

theorem second_large {k : ℕ} (hk : 2 ≤ k) (T U W : ℕ) (f q : Fin k → ℕ)
    (small : ∀ i, f i ≤ T^3) (bound : ∀ i, q i ≤ U)
    (large : (T^3)^k * U * W^(k-1) < ∏ i, (f i*q i)) :
    ∃ i j, i≠j ∧ W<q j ∧ (∀ l, q l ≤ q i) ∧ (∀ l, l≠i → q l ≤ q j) := by
  classical
  let x : Fin k := ⟨0,by omega⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k)) q ⟨x,Finset.mem_univ _⟩
  let s := (Finset.univ : Finset (Fin k)).erase i
  have sc : s.card=k-1 := by simp [s]
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image s q (Finset.card_pos.mp (by omega))
  have ij : j ≠ i := (Finset.mem_erase.mp hj).1
  refine ⟨i,j,ij.symm,?_,fun l => hi l (mem_univ _),fun l neq => hmax l (Finset.mem_erase.mpr ⟨neq,mem_univ _⟩)⟩
  by_contra! le
  have ff : ∏ l, f l ≤ (T^3)^k := by simpa using Finset.prod_le_prod' (s := Finset.univ) (fun i _ => small i)
  have qq : ∏ l ∈ s, q l ≤ W^(k-1) := by simpa [sc] using Finset.prod_le_prod' (s := s) (fun i h => (hmax i h).trans le)
  have qmax : ∏ l, q l ≤ U * W^(k-1) := by
    rw [←Finset.mul_prod_erase _ _ (mem_univ i)]
    exact Nat.mul_le_mul (bound i) qq
  rw [Finset.prod_mul_distrib] at large
  exact large.not_ge ((Nat.mul_le_mul ff qmax).trans_eq (Nat.mul_assoc ..).symm)



theorem cofactorization (n k : ℕ) (g : Fin k → ℕ) (prod : ∏ i, g i=k.factorial)
    (div : ∀ i : Fin k, g i ∣ n-i) :
    n.choose k = ∏ i : Fin k, ((n-i)/g i) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
  rw [←Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,←prod,
    ←Finset.prod_mul_distrib, ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => (Nat.mul_div_cancel' (div i)).symm

theorem distinct_shift {n k p : ℕ} (hn : k ≤ n) (hp : k ≤ p) (i j : Fin k)
    (hi : p ∣ n-i) (hj : p ∣ n-j) : i=j := by
  have residue (a : Fin k) (h : p ∣ n-a) : n%p = a.val := by
    calc n%p = ((n-a)+a.val)%p := by rw [Nat.sub_add_cancel (by omega : a.val≤n)]
         _ = a.val := by rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd h,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  exact Fin.ext ((residue i hi).symm.trans (residue j hj))

/-- Four exceptional classes in BNPZ §6. The first combines Propositions 6.2 and 6.3. -/
theorem classify (B n k T U W V : ℕ) (hk : 2≤k) (kn : k≤n) (kt : k≤T) (w : 1≤W)
    (scale : B*((T^3)^k*U*W^(k-1))≤n) (g : Fin k → ℕ)
    (pg : ∏ i,g i = k.factorial) (dg : ∀ i : Fin k, g i∣n-i)
    {d : ℕ} (dvd : d∣n.choose k) (window : n<B*d ∧ d≤n) :
    ∃ a : Fin k → ℕ, d=∏ i,a i ∧ (∀ i : Fin k, a i ∣ (n-i)/g i) ∧
      ((∃ i, U<a i) ∨
       (∃ i r s, a i=r*s ∧ T<r ∧ T<s) ∨
       (∃ f q : Fin k → ℕ, (∀ i, a i=f i*q i ∧ f i≤T^3 ∧ (q i=1 ∨ (q i).Prime ∧ T<q i)) ∧
         ∃ i j, i≠j ∧ W<q j ∧ q j<q i ∧ q i≤U ∧
         (∀ l, q l ≤ q i) ∧ (∀ l, l≠i → q l ≤ q j) ∧
         (q i < V*q j ∨ (∀ l, l≠i → V*q l ≤ q i)))) := by
  have dp : 0<d := by by_contra! h; simpa [Nat.eq_zero_of_le_zero h] using window.1
  rw [cofactorization n k g pg dg] at dvd
  obtain ⟨a,prod,ad⟩ := allocate Finset.univ _ d dvd
  have dv i := ad i (Finset.mem_univ _)
  refine ⟨a,prod,dv,?_⟩
  by_cases big : ∃ i, U<a i
  · exact Or.inl big
  push Not at big
  by_cases sp : ∃ i r s, a i=r*s ∧ T<r ∧ T<s
  · exact Or.inr (Or.inl sp)
  have ap (i : Fin k) : 0<a i := by
    by_contra! bad
    have zero : a i=0 := by omega
    have hz : (∏ j, a j)=0 := Finset.prod_eq_zero (Finset.mem_univ i) zero
    omega
  have af (i : Fin k) := almost_prime T (a i) (by omega) (ap i) (fun r s eq => by
    by_contra! h; exact sp ⟨i,r,s,eq,h.1,h.2⟩)
  choose f q decomp sm prime using af
  have qd i : q i ∣ a i := by rw [decomp]; exact dvd_mul_left _ _
  have qb i : q i ≤ U := (Nat.le_of_dvd (ap i) (qd i)).trans (big i)
  have sz : (T^3)^k*U*W^(k-1)<∏ i, (f i*q i) := by
    simp_rw [←decomp]; rw [←prod]
    exact Nat.lt_of_mul_lt_mul_left (scale.trans_lt window.1)
  obtain ⟨i,j,ij,lo,top,next⟩ := second_large hk T U W f q sm qb sz
  have qp : T<q j := ((prime j).resolve_left (by omega)).2
  have small (v : Fin k) : q v∣n-v := (qd v).trans ((dv v).trans (Nat.div_dvd_of_dvd (dg v)))
  have strict : q j<q i := lt_of_le_of_ne (top j) (by
    intro eq
    exact ij (distinct_shift kn (by omega : k≤q j) i j (eq ▸ small i) (small j)))
  refine Or.inr (Or.inr ⟨f,q,fun l => ⟨decomp l,sm l,prime l⟩,i,j,ij,lo,strict,qb i,top,next,?_⟩)
  by_cases near : q i < V*q j
  · exact Or.inl near
  · exact Or.inr (fun l h => (Nat.mul_le_mul_left V (next l h)).trans (le_of_not_gt near))


/-- Fixed-window progression from BNPZ Theorem 5.1, in the form of Naprienko's
fixed_B_cover_section6_input. -/
def H1 : Prop := ∀ B K : ℕ, 3≤B → ∃ k≥max 3 K, ∃ a : ℕ, ∃ g : Fin k → ℕ,
  let M := ∏ p ∈ (range (k+1)).filter Nat.Prime, p^(Nat.log p k+1)
  (∀ i, B≤g i) ∧ (∏ i,g i)=k.factorial ∧ ∀ n>k, n ≡ a [MOD M] →
    (∀ i : Fin k, g i∣n-i) ∧ ∀ p : ℕ, p.Prime → p≤k → ¬p∣n.choose k

/-- Simultaneous finite counting consequence of BNPZ Propositions 6.1–6.6.
The four exception sets count, respectively, a large allocated factor, a balanced
split, two close primes, or a prime separated from the other primes. The scale
x=t^(600*k^100) makes all four cutoffs integral. -/
def H2 : Prop := ∀ B : ℕ, 3≤B → ∃ K : ℕ, ∀ k≥max 3 K, ∀ a : ℕ, ∀ g : Fin k → ℕ,
  let M := ∏ p ∈ (range (k+1)).filter Nat.Prime, p^(Nat.log p k+1)
  (∀ i, B≤g i) → (∏ i,g i)=k.factorial → (∀ n>k, n ≡ a [MOD M] →
    (∀ i : Fin k, g i∣n-i) ∧ ∀ p : ℕ, p.Prime → p≤k → ¬p∣n.choose k) →
  ∃ t≥max (2*B) k, ∃ S : Finset ℕ, ∃ E : Fin 4 → Finset ℕ,
    let X := t^(600*k^100)
    let T := t^600
    let U := t^(202*k^100)
    let W := t^(300*k^99)
    let V := t^(600*k^96)
    (∀ j, 4*(E j).card<S.card) ∧ ∀ n∈S, k<n ∧ X≤2*n ∧ n≤2*X ∧ n ≡ a [MOD M] ∧
      ∀ u : Fin k → ℕ, (∀ i : Fin k, u i∣(n-i)/g i) →
        n<B*(∏ i,u i) → (∏ i,u i)≤n →
        ((∃ i, U<u i) → n∈E 0) ∧
        ((∀ i, u i≤U) → (∃ i r s, u i=r*s ∧ T<r ∧ T<s) → n∈E 1) ∧
        ((∀ i, u i≤U) → ∀ f q : Fin k → ℕ, (∀ i, u i=f i*q i ∧ f i≤T^3 ∧
          (q i=1 ∨ (q i).Prime ∧ T<q i)) → ∀ i j, i≠j → W<q j → q j<q i → q i≤U →
          (∀ l, q l≤q i) → (∀ l, l≠i → q l≤q j) →
          (q i<V*q j → n∈E 2) ∧ ((∀ l, l≠i → V*q l≤q i) → n∈E 3))

theorem scale_bound (B k t n : ℕ) (hk : 3≤k) (ht : max (2*B) k ≤ t)
    (hn : t^(600*k^100)≤2*n) :
    B*(((t^600)^3)^k*t^(202*k^100)*(t^(300*k^99))^(k-1)) ≤ n := by
  have b : 2*B≤t := (le_max_left ..).trans ht
  have one : 1≤t := by have := le_max_right (2*B) k; omega
  have k100 : k^100=k^99*k := pow_succ _ _
  have small : 1+1800*k ≤ 98*k^100 := by
    have t4 : 27≤k^3 := Nat.pow_le_pow_left hk 3
    have t99 : k^3≤k^99 := Nat.pow_le_pow_right (by omega) (by decide)
    have := Nat.mul_le_mul_right k (t4.trans t99)
    rw [k100]; omega
  have expbound : 1+600*3*k+202*k^100+300*k^99*(k-1)≤600*k^100 := by
    have := Nat.mul_le_mul_left (300*k^99) (Nat.sub_le k 1)
    rw [Nat.mul_assoc 300 (k^99) k,←k100] at this
    omega
  have pair : 2*(B*(((t^600)^3)^k*t^(202*k^100)*(t^(300*k^99))^(k-1))) ≤ 2*n := calc
    _ ≤ t*(((t^600)^3)^k*t^(202*k^100)*(t^(300*k^99))^(k-1)) := by rw [←mul_assoc]; gcongr
    _ = t^(1+600*3*k+202*k^100+300*k^99*(k-1)) := by
      simp only [pow_add,pow_mul,pow_one]; ring
    _ ≤ _ := (Nat.pow_le_pow_right one expbound).trans hn
  omega

theorem main : H1 → H2 → type_of% @Erdos387.erdos_387 := by
  intro cover counts ⟨c,hc,claimed⟩
  obtain ⟨b,hb⟩ := exists_nat_gt (1/c)
  let B := max 3 b
  have hB : 3≤B := le_max_left _ _
  have bc : 1 ≤ c*(B:ℝ) := by
    have h := (div_lt_iff₀ hc).mp hb
    have h' : (b:ℝ) ≤ B := by exact_mod_cast (le_max_right 3 b)
    nlinarith [mul_le_mul_of_nonneg_left h' hc.le]
  obtain ⟨K,est⟩ := counts B hB
  obtain ⟨k,hk,a,g,gb,pg,prog⟩ := cover B K hB
  obtain ⟨t,ht,S,E,small,good⟩ := est k hk a g gb pg prog
  have others : ¬S ⊆ univ.biUnion E := by
    intro sub
    have h := (Finset.card_le_card sub).trans (Finset.card_biUnion_le)
    rw [Fin.sum_univ_four] at h
    have a := small 0; have b := small 1; have e := small 2; have f := small 3
    omega
  obtain ⟨n,hn,avoid⟩ := Finset.not_subset.mp others
  have missing (j : Fin 4) : n ∉ E j := fun h => avoid (Finset.mem_biUnion.mpr ⟨j,mem_univ _,h⟩)
  obtain ⟨kn,dy,_,cong,ex⟩ := good n hn
  obtain ⟨d,⟨lo,hi⟩,dd⟩ := claimed n k (by omega) kn
  have win : n < B*d := by
    have mat := mul_lt_mul_of_pos_left lo (show (0:ℝ)<B by exact_mod_cast (by omega : 0<B))
    have n0 := Nat.cast_nonneg (α := ℝ) n
    have lower := mul_le_mul_of_nonneg_right bc n0
    exact_mod_cast (by nlinarith : (n:ℝ)<(B:ℝ)*d)
  have dn : d≤n := by exact_mod_cast hi
  have kt : k≤t^600 := (le_max_right (2*B) k).trans (ht.trans (by
    simpa using Nat.pow_le_pow_right (n := t) (by omega) (by decide : 1≤600)))
  obtain ⟨u,eq,ud,cases⟩ := classify B n k (t^600) (t^(202*k^100)) (t^(300*k^99))
    (t^(600*k^96)) (by omega) kn.le kt (Nat.one_le_pow _ _ (by omega)) (scale_bound B k t n (by omega) ht dy)
    g pg (prog n kn cong).1 dd ⟨win,dn⟩
  obtain ⟨large,split,prime⟩ := ex u ud (eq ▸ win) (eq ▸ dn)
  have all (i : Fin k) : u i ≤ t^(202*k^100) := le_of_not_gt (fun h => missing 0 (large ⟨i,h⟩))
  rcases cases with h|h|⟨f,q,hf,i,j,ij,lo,lt,hi,mx,sm,near|far⟩
  · exact missing 0 (large h)
  · exact missing 1 (split all h)
  · exact missing 2 ((prime all f q hf i j ij lo lt hi mx sm).1 near)
  · exact missing 3 ((prime all f q hf i j ij lo lt hi mx sm).2 far)

end OMA.R_Erdos387_erdos_387_R1
