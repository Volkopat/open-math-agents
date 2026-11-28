import OMAStatements.S_oeis_a330816
import Mathlib

/-!
# An exhaustive inverse search for Corneth's list

Write τ(n) for the number of divisors. A predecessor of m coming from a division
has the form mt with t = τ(mt). Submultiplicativity and τ(t) ≤ 2√t yield
t ≤ 4τ(m)². Split t into its part u supported on 2, 3, 5, 7, 11, 13 and its
coprime part w. For each of the 45 targets m, the latter part of m is squarefree
and 4τ(m)² < 17¹¹. Consequently, for every prime q ≥ 17 in mt, its exponent
plus one is at most 12. The coprime part w of τ(mt) therefore comes entirely
from the six small-prime factors of the divisor-count product.

For each vector of six exponents this determines t. The search uses local
divisibility and size checks to skip whole branches. Its last test computes
the remaining divisor count from checked prime-power factorizations.
The certificates at the end also verify a decreasing forward step for every
listed value greater than one.
-/

namespace Inverse330
open Finset

lemma count_on (n : ℕ) (hn : n ≠ 0) (S : Finset ℕ) (inc : n.primeFactors ⊆ S) :
    n.divisors.card = ∏ p ∈ S,(n.factorization p+1) := by
  rw [Nat.card_divisors hn]
  apply Finset.prod_subset inc
  intro p _ out
  have z : n.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa using out
  simp [z]

lemma submultiplicative (m t : ℕ) (hm : m≠0) (ht : t≠0) :
    (m*t).divisors.card ≤ m.divisors.card*t.divisors.card := by
  let S := m.primeFactors ∪ t.primeFactors
  rw [count_on m hm S Finset.subset_union_left,count_on t ht S Finset.subset_union_right,
      Nat.card_divisors (Nat.mul_ne_zero hm ht),Nat.primeFactors_mul hm ht,← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p _
  rw [Nat.factorization_mul hm ht,Finsupp.add_apply]
  nlinarith only [Nat.zero_le (m.factorization p*t.factorization p)]

lemma divisor_sqrt (t : ℕ) (ht : 0 < t) : t.divisors.card ≤ 2*t.sqrt := by
  let s := Finset.Icc 1 t.sqrt
  have cover : t.divisors ⊆ s ∪ s.image (fun q => t/q) := by
    intro d hd
    have dv := Nat.dvd_of_mem_divisors hd
    have dp := Nat.pos_of_dvd_of_pos dv ht
    by_cases low : d ≤ t.sqrt
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨dp,low⟩)
    · obtain ⟨q,eq⟩ := dv
      have qp : 0 < q := Nat.pos_of_mul_pos_left (eq ▸ ht)
      have lim : q ≤ t.sqrt := by
        by_contra! big
        have l : (t.sqrt+1)*(t.sqrt+1) ≤ d*q := Nat.mul_le_mul (by omega) (by omega)
        have top := Nat.succ_le_succ_sqrt t
        omega
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨q,Finset.mem_Icc.mpr ⟨qp,lim⟩,by rw [eq,Nat.mul_div_cancel _ qp]⟩
  calc
    t.divisors.card ≤ (s ∪ s.image (fun q => t/q)).card := Finset.card_le_card cover
    _ ≤ s.card + (s.image (fun q => t/q)).card := Finset.card_union_le _ _
    _ ≤ s.card+s.card := Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by simp [s,Nat.card_Icc]; omega

lemma multiplier_bound (m t : ℕ) (hm : 0 < m) (ht : 0 < t) (e : (m*t).divisors.card=t) :
    t ≤ 4*m.divisors.card^2 := by
  have bound := submultiplicative m t hm.ne' ht.ne'
  rw [e] at bound
  have lin := bound.trans (Nat.mul_le_mul_left _ (divisor_sqrt t ht))
  have sq := Nat.mul_le_mul lin lin
  have rt := Nat.sqrt_le t
  have comp := Nat.mul_le_mul_left (4*m.divisors.card^2) rt
  nlinarith only [sq,comp,ht]
open scoped Nat

def smallPrimes : List ℕ := [2,3,5,7,11,13]

def peel : List ℕ → ℕ → ℕ
  | [], n => n
  | p::ps,n => ordCompl[p] (peel ps n)

lemma peel_pos (ps : List ℕ) (n : ℕ) (hn : 0 < n) : 0 < peel ps n := by
  induction ps with
  | nil => exact hn
  | cons p ps ih => exact Nat.ordCompl_pos p ih.ne'

lemma peel_mul (ps : List ℕ) (m n : ℕ) : peel ps (m*n) = peel ps m * peel ps n := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [peel,ih,Nat.ordCompl_mul]

lemma exponent_peel (ps : List ℕ) (n q : ℕ) :
    (peel ps n).factorization q = if q ∈ ps then 0 else n.factorization q := by
  induction ps with
  | nil => simp [peel]
  | cons p ps ih =>
    simp only [peel,Nat.factorization_ordCompl,Finsupp.erase_apply,List.mem_cons]
    by_cases h : q=p <;> simp_all [eq_comm]

lemma split_number (ps : List ℕ) (nd : ps.Nodup) (n : ℕ) :
    (ps.map (fun p => p^(n.factorization p))).prod * peel ps n = n := by
  induction ps with
  | nil => simp [peel]
  | cons p ps ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    have part := Nat.ordProj_mul_ordCompl_eq_self (peel ps n) p
    change p ^ (peel ps n).factorization p * peel (p::ps) n = peel ps n at part
    rw [exponent_peel,if_neg fresh] at part
    simp only [List.map_cons,List.prod_cons]
    rw [mul_comm (p^_),mul_assoc,part,ih rest]

lemma count_peel (ps : List ℕ) (nd : ps.Nodup) (good : ∀ p ∈ ps,p.Prime) (n : ℕ) (hn : 0 < n) :
    (ps.map (fun p => n.factorization p+1)).prod * (peel ps n).divisors.card = n.divisors.card := by
  induction ps with
  | nil => simp [peel]
  | cons p ps ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    have hp := good p List.mem_cons_self
    let w := peel ps n
    have wp : 0 < w := peel_pos _ _ hn
    have part := Nat.ordProj_mul_ordCompl_eq_self w p
    have cop := (Nat.coprime_ordCompl hp wp.ne').pow_left (w.factorization p)
    have eq : (w.factorization p+1)*(peel (p::ps) n).divisors.card = w.divisors.card := by
      calc
        _ = (p^(w.factorization p)).divisors.card * (ordCompl[p] w).divisors.card := by
          rw [Nat.divisors_prime_pow hp]; simp [peel,w]
        _ = (p^(w.factorization p) * ordCompl[p] w).divisors.card := (cop.card_divisors_mul).symm
        _ = _ := congrArg (fun x : ℕ => x.divisors.card) part
    change ((peel ps n).factorization p+1)*(peel (p::ps) n).divisors.card = (peel ps n).divisors.card at eq
    rw [exponent_peel,if_neg fresh] at eq
    simp only [List.map_cons,List.prod_cons]
    rw [mul_comm (n.factorization p+1),mul_assoc,eq,ih rest (fun q h => good q (List.mem_cons_of_mem p h))]

lemma peel_one : ∀ ps : List ℕ, peel ps 1 = 1 := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [peel,ih]

lemma peel_prod (ps : List ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    peel ps (∏ i ∈ s, f i) = ∏ i ∈ s,peel ps (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [peel_one]
  | insert i s h ih => simp [h,peel_mul,ih]

lemma prime_large (p : ℕ) (hp : p.Prime) (out : p ∉ smallPrimes) : 17 ≤ p := by
  by_contra! small
  have cert : ∀ i : Fin 17, i.val.Prime → i.val ∈ smallPrimes := by decide +kernel
  exact out (cert ⟨p,small⟩ hp)

lemma small_gone (n : ℕ) (pos : 0 < n) (hn : n < 17) : peel smallPrimes n = 1 := by
  have cert : ∀ i : Fin 17, 0 < i.val → peel smallPrimes i.val = 1 := by decide +kernel
  exact cert ⟨n,hn⟩ pos

lemma residual_count (m t : ℕ) (hm : 0 < m) (ht : 0 < t) (lim : t < 17^11)
    (free : Squarefree (peel smallPrimes m)) :
    peel smallPrimes ((peel smallPrimes (m*t)).divisors.card) = 1 := by
  let z := peel smallPrimes (m*t)
  have zp : 0 < z := peel_pos _ _ (Nat.mul_pos hm ht)
  change peel smallPrimes z.divisors.card = 1
  rw [Nat.card_divisors zp.ne',peel_prod]
  apply Finset.prod_eq_one
  intro q hq
  have qp := Nat.prime_of_mem_primeFactors hq
  have exp : 0 < z.factorization q := qp.factorization_pos_of_dvd zp.ne' (Nat.dvd_of_mem_primeFactors hq)
  have out : q ∉ smallPrimes := by
    intro mem
    change 0 < (peel smallPrimes (m*t)).factorization q at exp
    simp [exponent_peel,mem] at exp
  have large := prime_large q qp out
  have low : t.factorization q < 11 := by
    by_contra! high
    have d := (Nat.Prime.pow_dvd_iff_le_factorization qp ht.ne').mpr high
    have size := Nat.le_of_dvd ht d
    have base := Nat.pow_le_pow_left large 11
    omega
  have rm : (peel smallPrimes m).factorization q ≤ 1 := (Nat.squarefree_iff_factorization_le_one (peel_pos _ _ hm).ne').mp free q
  rw [exponent_peel,if_neg out] at rm
  apply small_gone _ (by omega)
  change (peel smallPrimes (m*t)).factorization q + 1 < _
  rw [exponent_peel,if_neg out,Nat.factorization_mul hm.ne' ht.ne',Finsupp.add_apply]
  omega

def lookupCount : List (ℕ × ℕ) → ℕ → ℕ
  | [],_ => 0
  | (a,b)::rows,w => if a=w then b else lookupCount rows w

lemma lookup_sound (rows : List (ℕ × ℕ)) (r w : ℕ)
    (correct : ∀ v ∈ rows, (r*v.1).divisors.card=v.2) (found : lookupCount rows w ≠ 0) :
    (r*w).divisors.card = lookupCount rows w := by
  induction rows with
  | nil => exact (found rfl).elim
  | cons v vs ih =>
    obtain ⟨a,b⟩ := v
    by_cases eq : a=w
    · subst a; simpa [lookupCount] using correct (w,b) List.mem_cons_self
    · simp only [lookupCount,if_neg eq] at found ⊢
      exact ih (fun v hv => correct v (List.mem_cons_of_mem _ hv)) found

def leafTest (cap : ℕ) (allowed : List ℕ) (rows : List (ℕ × ℕ)) (u a w : ℕ) : Bool :=
  let t := u*w
  if cap<t ∨ t%a≠0 then true else
    let c := lookupCount rows w
    decide (c≠0 ∧ (t≠a*c ∨ t ∈ allowed))

def allPowers (p cap : ℕ) (f : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0,_,_ => true
  | fuel+1,e,u => if cap<u then true else f e u && allPowers p cap f fuel (e+1) (u*p)

lemma allPowers_spec (p cap : ℕ) (hp : 0 < p) (f : ℕ → ℕ → Bool)
    (fuel e u i : ℕ) (fi : i<fuel) (lim : u*p^i ≤ cap)
    (ok : allPowers p cap f fuel e u = true) : f (e+i) (u*p^i) = true := by
  induction fuel generalizing e u i with
  | zero => omega
  | succ fuel ih =>
    have first : u ≤ cap := le_trans (by grw [← Nat.one_le_pow i p hp]; simp) lim
    simp only [allPowers,if_neg (not_lt.mpr first),Bool.and_eq_true] at ok
    cases i with
    | zero => simpa using ok.1
    | succ i =>
      have l : (u*p)*p^i ≤ cap := by simpa [pow_succ',Nat.mul_assoc] using lim
      simpa [pow_succ',Nat.mul_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (e+1) (u*p) i (by omega) l ok.2

-- For each local divisor-count factor below 128, remove all six small primes.
def quickRough (a : ℕ) : ℕ := a / a.gcd (30030^7)

lemma quickRough_spec {a : ℕ} (pos : 0 < a) (h : a < 128) : quickRough a = peel smallPrimes a := by
  have cert : ∀ i : Fin 128, 0 < i.val → quickRough i.val = peel smallPrimes i.val := by decide +kernel
  exact cert ⟨a,h⟩ pos

def smallProduct (ss : List (ℕ × ℕ)) (t : ℕ) : ℕ :=
  (ss.map (fun row => row.1^(t.factorization row.1))).prod

def countProduct (ss : List (ℕ × ℕ)) (t : ℕ) : ℕ :=
  (ss.map (fun row => row.2+t.factorization row.1+1)).prod

lemma smallProduct_pos (ss : List (ℕ × ℕ)) (t : ℕ) : 0 < smallProduct ss t := by
  induction ss with
  | nil => simp [smallProduct]
  | cons x xs ih =>
    simp only [smallProduct,List.map_cons,List.prod_cons]
    apply Nat.mul_pos _ ih
    by_cases h : x.1=0
    · simp [h]
    · exact Nat.pow_pos (by omega)

def baseProduct (ss : List (ℕ × ℕ)) : ℕ := (ss.map (fun v => v.2+1)).prod

lemma growLinear (p b e : ℕ) (hp : 2 ≤ p) : b+e+1 ≤ (b+1)*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have pos : 0 < (b+1)*p^e := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    rw [pow_succ,← Nat.mul_assoc]
    have le := Nat.mul_le_mul_left ((b+1)*p^e) hp
    omega

lemma count_le_base (ss : List (ℕ × ℕ)) (t : ℕ) (pr : ∀ v ∈ ss,v.1.Prime) :
    countProduct ss t ≤ baseProduct ss * smallProduct ss t := by
  induction ss with
  | nil => simp [countProduct,baseProduct,smallProduct]
  | cons v ss ih =>
    have head := growLinear v.1 v.2 (t.factorization v.1) (pr v List.mem_cons_self).two_le
    have tail := ih (fun w hw => pr w (List.mem_cons_of_mem _ hw))
    simpa [countProduct,baseProduct,smallProduct,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul head tail
/-- Enumerate the exponents of the six small primes, skipping impossible prefixes. -/
def boundedScan (rt cap : ℕ) (allowed : List ℕ) (rows : List (ℕ × ℕ)) :
    List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool
  | [],u,a,w => if a*rt<u then true else leafTest cap allowed rows u a w
  | (p,b)::ss,u,a,w =>
    if a * baseProduct ((p,b)::ss) * rt < u then true else
    allPowers p cap (fun e v =>
      let f := b+e+1
      let a' := a*f
      if a' % (p^(e+1))=0 then true else
        decide (f<128) && boundedScan rt cap allowed rows ss v a' (w*quickRough f)) 43 0 u

lemma fast_follow (rt cap t : ℕ) (ht : 0 < t) (allowed : List ℕ) (rows : List (ℕ × ℕ))
    (ss : List (ℕ × ℕ)) (u a w : ℕ) (pr : ∀ v ∈ ss,v.1.Prime)
    (fuel : ∀ v ∈ ss,t.factorization v.1 < 43)
    (lim : u*smallProduct ss t ≤ cap) (d : a*countProduct ss t ∣ t)
    (necessary : u*smallProduct ss t ≤ a*countProduct ss t*rt)
    (ok : boundedScan rt cap allowed rows ss u a w = true) :
    leafTest cap allowed rows (u*smallProduct ss t) (a*countProduct ss t)
      (w*peel smallPrimes (countProduct ss t)) = true := by
  induction ss generalizing u a w with
  | nil =>
    have okLim : ¬a*rt<u := by simpa [smallProduct,countProduct] using not_lt.mpr necessary
    simpa [smallProduct,countProduct,peel_one,boundedScan,okLim] using ok
  | cons row ss ih =>
    obtain ⟨p,b⟩ := row
    let e := t.factorization p
    let f := b+e+1
    have hp := pr (p,b) List.mem_cons_self
    have bound : u*p^e ≤ cap := by
      have pos := smallProduct_pos ss t
      change u*(p^e*smallProduct ss t) ≤ cap at lim
      calc
        _ ≤ (u*p^e)*smallProduct ss t := Nat.le_mul_of_pos_right _ pos
        _ ≤ _ := by simpa [Nat.mul_assoc] using lim
    have ratio := count_le_base ((p,b)::ss) t pr
    have localBound : u ≤ a*baseProduct ((p,b)::ss)*rt := by
      apply Nat.le_of_mul_le_mul_right (c := smallProduct ((p,b)::ss) t)
      · calc
          _ ≤ _ := necessary
          _ ≤ a*(baseProduct ((p,b)::ss)*smallProduct ((p,b)::ss) t)*rt := Nat.mul_le_mul_right rt (Nat.mul_le_mul_left a ratio)
          _ = _ := by ring
      · exact smallProduct_pos _ _
    simp only [boundedScan, if_neg (not_lt.mpr localBound)] at ok
    have ev := allPowers_spec p cap hp.pos _ 43 0 u e (fuel (p,b) List.mem_cons_self) bound ok
    simp only [Nat.zero_add] at ev
    change (if a*f%(p^(e+1))=0 then true else decide (f<128) &&
      boundedScan rt cap allowed rows ss (u*p^e) (a*f) (w*quickRough f)) = true at ev
    change a*(f*countProduct ss t) ∣ t at d
    rw [← Nat.mul_assoc] at d
    have div : a*f ∣ t := (dvd_mul_right _ _).trans d
    have no : a*f%(p^(e+1))≠0 := by
      intro z
      have implied := (hp.pow_dvd_iff_le_factorization ht.ne').mp ((Nat.dvd_of_mod_eq_zero z).trans div)
      change e+1 ≤ e at implied
      omega
    simp only [if_neg no,Bool.and_eq_true,decide_eq_true_eq] at ev
    have next := ih (u*p^e) (a*f) (w*quickRough f) (fun v hv => pr v (List.mem_cons_of_mem _ hv))
      (fun v hv => fuel v (List.mem_cons_of_mem _ hv)) (by simpa [smallProduct,e,Nat.mul_assoc] using lim) d (by simpa [smallProduct,countProduct,f,e,Nat.mul_assoc] using necessary) ev.2
    rw [quickRough_spec (by dsimp [f]; omega) ev.1] at next
    simpa [smallProduct,countProduct,e,f,peel_mul,Nat.mul_assoc] using next

open scoped Nat
abbrev Specs := List (ℕ × ℕ)

lemma small_good : ∀ p ∈ smallPrimes,p.Prime := by decide +kernel
lemma small_unique : smallPrimes.Nodup := by decide +kernel

/-- Prime-power divisibility witnesses for the small-prime part of the target. -/
def checkSpec (m : ℕ) (ss : Specs) : Prop :=
  ss.map Prod.fst = smallPrimes ∧ ∀ v ∈ ss,v.1^v.2 ∣ m ∧ ¬v.1^(v.2+1) ∣ m
instance (m : ℕ) (ss : Specs) : Decidable (checkSpec m ss) := by unfold checkSpec; infer_instance

lemma spec_eq {m : ℕ} (hm : 0 < m) (ss : Specs) (good : checkSpec m ss) :
    ss = smallPrimes.map (fun p => (p,m.factorization p)) := by
  rw [← good.1,List.map_map]
  conv_lhs => rw [← List.map_id ss]
  apply List.map_congr_left
  intro v hv
  have hp := small_good v.1 (good.1 ▸ List.mem_map_of_mem hv)
  obtain ⟨yes,no⟩ := good.2 v hv
  have le := (hp.pow_dvd_iff_le_factorization hm.ne').mp yes
  have lt := mt (hp.pow_dvd_iff_le_factorization hm.ne').mpr no
  exact Prod.ext rfl (by dsimp; omega)

lemma match_rough {m r : ℕ} (hm : 0 < m) (ss : Specs) (good : checkSpec m ss)
    (eq : (ss.map (fun v => v.1^v.2)).prod*r=m) : peel smallPrimes m=r := by
  rw [spec_eq hm ss good] at eq
  simp only [List.map_map, Function.comp_def] at eq
  have e := split_number _ small_unique m
  have pos := peel_pos smallPrimes m hm
  have nonz : 0 < (smallPrimes.map (fun p => p^m.factorization p)).prod := Nat.pos_of_mul_pos_right (e ▸ hm)
  exact Nat.eq_of_mul_eq_mul_left nonz (e.trans eq.symm)

lemma match_count {m r mt : ℕ} (hm : 0 < m) (ss : Specs) (good : checkSpec m ss)
    (rough : peel smallPrimes m=r) (eq : (ss.map (fun v => v.2+1)).prod*r.divisors.card=mt) :
    m.divisors.card=mt := by
  rw [spec_eq hm ss good] at eq
  simpa only [List.map_map,Function.comp_def,←rough, count_peel _ small_unique small_good m hm] using eq

def factorData : Specs → ℕ × ℕ
  | [] => (1,1)
  | (p,e)::fs => (p^e*(factorData fs).1,(e+1)*(factorData fs).2)
def factorsGood : Specs → Bool
  | [] => true
  | (p,_)::fs => decide (p.Prime ∧ p.Coprime (factorData fs).1) && factorsGood fs

lemma factor_count (fs : Specs) (ok : factorsGood fs = true) :
    (factorData fs).1.divisors.card=(factorData fs).2 := by
  induction fs with
  | nil => simp [factorData]
  | cons v fs ih =>
    obtain ⟨p,e⟩ := v
    simp only [factorsGood,Bool.and_eq_true,decide_eq_true_eq] at ok
    simp only [factorData,(ok.1.2.pow_left e).card_divisors_mul,Nat.divisors_prime_pow ok.1.1,
      Finset.card_map,ih ok.2]
    simp

def lookupRows (cs : List (ℕ × Specs)) : Specs := cs.map (fun c => (c.1,(factorData c.2).2))
def checkedRows (r : ℕ) (cs : List (ℕ × Specs)) : Bool :=
  cs.all fun c => decide ((factorData c.2).1 = r*c.1) && factorsGood c.2

lemma checked_sound {r : ℕ} {cs : List (ℕ × Specs)} (good : checkedRows r cs = true) :
    ∀ v ∈ lookupRows cs, (r*v.1).divisors.card=v.2 := by
  intro v hv
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
  have h := List.all_eq_true.mp good c hc
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  change (r*c.1).divisors.card = _
  rw [← h.1]
  exact factor_count c.2 h.2

lemma inverse_scan (m r mt cap : ℕ) (ss : Specs) (allowed : List ℕ) (rows : Specs)
    (hm : 0 < m) (good : checkSpec m ss) (rough : peel smallPrimes m=r)
    (card : m.divisors.card=mt) (free : Squarefree r)
    (capEq : 4*mt^2 = cap) (capLim : cap < 17^11 ∧ cap < 2^43)
    (correct : ∀ v ∈ rows,(r*v.1).divisors.card=v.2)
    (scan : boundedScan r.divisors.card cap allowed rows ss 1 1 1=true)
    (t : ℕ) (ht : 0 < t) (eq : (m*t).divisors.card=t) : t ∈ allowed := by
  have bound := multiplier_bound m t hm ht eq
  rw [card,capEq] at bound
  have pr : ∀ v ∈ ss,v.1.Prime := fun v hv => small_good _ (good.1 ▸ List.mem_map_of_mem hv)
  have fuel : ∀ v ∈ ss,t.factorization v.1 < 43 := by
    intro v hv
    by_contra! ge
    have d := ((pr v hv).pow_dvd_iff_le_factorization ht.ne').mpr ge
    have low := Nat.pow_le_pow_left (pr v hv).two_le 43
    have lim := Nat.le_of_dvd ht d
    omega
  have split : smallProduct ss t * peel smallPrimes t=t := by
    simpa [smallProduct,spec_eq hm ss good,List.map_map,Function.comp_def] using split_number _ small_unique t
  have count : countProduct ss t * (peel smallPrimes (m*t)).divisors.card=t := by
    have h := (count_peel _ small_unique small_good (m*t) (Nat.mul_pos hm ht)).trans eq
    simpa [countProduct,spec_eq hm ss good,List.map_map,Function.comp_def,Nat.factorization_mul hm.ne' ht.ne',Finsupp.add_apply] using h
  have d : countProduct ss t ∣ t := Dvd.intro _ count
  have res := residual_count m t hm ht (bound.trans_lt capLim.1) (rough ▸ free)
  have peeled := congrArg (peel smallPrimes) count
  rw [peel_mul,res,Nat.mul_one] at peeled
  have rp : 0 < r := rough ▸ peel_pos _ _ hm
  have wp := peel_pos smallPrimes t ht
  have upper := (submultiplicative r (peel smallPrimes t) rp.ne' wp.ne').trans
    (Nat.mul_le_mul_left r.divisors.card (Nat.card_divisors_le_self _))
  have necessary : smallProduct ss t ≤ countProduct ss t*r.divisors.card := by
    apply Nat.le_of_mul_le_mul_right (c := peel smallPrimes t) _ wp
    calc
      _ = countProduct ss t * (peel smallPrimes (m*t)).divisors.card := split.trans count.symm
      _ ≤ countProduct ss t * (r.divisors.card*peel smallPrimes t) := by
        rw [peel_mul,rough]
        exact Nat.mul_le_mul_left _ upper
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have follow := fast_follow r.divisors.card cap t ht allowed rows ss 1 1 1 pr fuel
    (by simp only [Nat.one_mul]; exact (Nat.le_mul_of_pos_right _ (peel_pos _ _ ht)).trans (split ▸ bound)) (by simpa using d) (by simpa using necessary) scan
  simp only [Nat.one_mul] at follow
  rw [← peeled] at split
  unfold leafTest at follow
  simp only [split,not_lt.mpr bound,Nat.mod_eq_zero_of_dvd d,ne_eq,not_true_eq_false,or_self,if_false,
    decide_eq_true_eq] at follow
  have matchC := lookup_sound rows r _ correct follow.1
  rw [peel_mul,rough,←peeled,matchC] at count
  exact follow.2.resolve_left (fun ne => ne count.symm)

open OMA.S_oeis_a330816 (entries step)

def ClosedAt (m : ℕ) : Prop :=
    (∀ t : ℕ, 0 < t → (m*t).divisors.card=t → m*t ∈ entries) ∧
    (m≠1 → step m ∈ entries ∧ step m < m)

lemma from_closed (allClosed : ∀ m ∈ entries, ClosedAt m) :
    ∀ n : ℕ, 0 < n → ((∃ k : ℕ, step^[k] n=1) ↔ n ∈ entries) := by
  have back (n : ℕ) (hn : 0 < n) (mem : step n ∈ entries) : n ∈ entries := by
    by_cases d : n.divisors.card ∣ n
    · have positive : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hn.ne'⟩
      rw [step,if_pos d] at mem
      have eq := Nat.div_mul_cancel d
      simpa only [eq] using (allClosed _ mem).1 n.divisors.card positive (by rw [eq])
    · simpa [step,d] using mem
  have stays (n : ℕ) (hn : 0 < n) : 0 < step n := by
    unfold step
    split_ifs with d
    · apply Nat.div_pos (Nat.le_of_dvd hn d)
      exact Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hn.ne'⟩
    · exact hn
  intro n hn
  constructor
  · rintro ⟨k,hk⟩
    induction k generalizing n with
    | zero =>
      have eq : n=1 := hk
      rw [eq]
      exact List.mem_cons_self
    | succ k ih =>
      rw [Function.iterate_succ_apply] at hk
      exact back n hn (ih _ (stays n hn) hk)
  · intro mem
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases eq : n=1
      · exact ⟨0,eq⟩
      obtain ⟨mem',lt⟩ := (allClosed n mem).2 eq
      obtain ⟨k,hk⟩ := ih _ lt (stays n hn) mem'
      exact ⟨k+1,by rw [Function.iterate_succ_apply]; exact hk⟩

/-- A target, its rough part and divisor count, its six small-prime exponents,
the allowed inverse multipliers, and factorizations for the final divisor counts. -/
structure Cert where
  m : ℕ
  r : ℕ
  mt : ℕ
  ss : Specs
  allowed : List ℕ
  cs : List (ℕ × Specs)

def Cert.valid (c : Cert) : Prop :=
  0 < c.m ∧ checkSpec c.m c.ss ∧ (c.ss.map (fun v => v.1^v.2)).prod*c.r=c.m ∧
  (c.ss.map (fun v => v.2+1)).prod*c.r.divisors.card=c.mt ∧ Squarefree c.r ∧
  4*c.mt^2 < 17^11 ∧ 4*c.mt^2 < 2^43 ∧ checkedRows c.r c.cs=true ∧
  (∀ t ∈ c.allowed,c.m*t ∈ entries) ∧
  (c.m≠1 → c.mt ∣ c.m ∧ c.m/c.mt ∈ entries ∧ c.m/c.mt<c.m)
instance (c : Cert) : Decidable c.valid := by unfold Cert.valid; infer_instance

def Cert.scanned (c : Cert) : Prop := boundedScan c.r.divisors.card (4*c.mt^2) c.allowed (lookupRows c.cs) c.ss 1 1 1=true

lemma cert_closed (c : Cert) (valid : c.valid) (scan : c.scanned) : ClosedAt c.m := by
  obtain ⟨hm,spec,rEq,tEq,free,lim,lim',tab,back,fwd⟩ := valid
  have rough := match_rough hm c.ss spec rEq
  have card := match_count hm c.ss spec rough tEq
  constructor
  · intro t ht he
    exact back t (inverse_scan c.m c.r c.mt _ c.ss c.allowed _ hm spec rough card free rfl ⟨lim,lim'⟩
      (checked_sound tab) scan t ht he)
  · intro ne
    obtain ⟨d,mem,lt⟩ := fwd ne
    simpa [step,card,d] using And.intro mem lt

lemma K (c : Cert) (v : c.valid := by set_option maxRecDepth 100000 in set_option maxHeartbeats 10000000 in decide +kernel)
    (s : c.scanned := by unfold Cert.scanned; set_option maxRecDepth 100000 in set_option maxHeartbeats 10000000 in decide +kernel) : ClosedAt c.m := cert_closed c v s

def c0 : Cert := ⟨1,1,1,[(2,0),(3,0),(5,0),(7,0),(11,0),(13,0)],[1,2],[(1,[])]⟩
theorem closed0 : ClosedAt 1 := K c0

def c1 : Cert := ⟨2,1,2,[(2,1),(3,0),(5,0),(7,0),(11,0),(13,0)],[4,6],[(1,[])]⟩
theorem closed1 : ClosedAt 2 := K c1

def c2 : Cert := ⟨8,1,4,[(2,3),(3,0),(5,0),(7,0),(11,0),(13,0)],[10,12],[(1,[])]⟩
theorem closed2 : ClosedAt 8 := K c2

def c3 : Cert := ⟨12,1,6,[(2,2),(3,1),(5,0),(7,0),(11,0),(13,0)],[20],[(1,[])]⟩
theorem closed3 : ClosedAt 12 := K c3

def c4 : Cert := ⟨80,1,10,[(2,4),(3,0),(5,1),(7,0),(11,0),(13,0)],[28,45],[(1,[])]⟩
theorem closed4 : ClosedAt 80 := K c4

def c5 : Cert := ⟨96,1,12,[(2,5),(3,1),(5,0),(7,0),(11,0),(13,0)],[42],[(1,[])]⟩
theorem closed5 : ClosedAt 96 := K c5

def c6 : Cert := ⟨240,1,20,[(2,4),(3,1),(5,1),(7,0),(11,0),(13,0)],[84],[(1,[])]⟩
theorem closed6 : ClosedAt 240 := K c6

def c7 : Cert := ⟨2240,1,28,[(2,6),(3,0),(5,1),(7,1),(11,0),(13,0)],[96,120],[(1,[])]⟩
theorem closed7 : ClosedAt 2240 := K c7

def c8 : Cert := ⟨3600,1,45,[(2,4),(3,2),(5,2),(7,0),(11,0),(13,0)],[],[]⟩
theorem closed8 : ClosedAt 3600 := K c8

def c9 : Cert := ⟨4032,1,42,[(2,6),(3,2),(5,0),(7,1),(11,0),(13,0)],[96,108,180],[(1,[])]⟩
theorem closed9 : ClosedAt 4032 := K c9

def c10 : Cert := ⟨20160,1,84,[(2,6),(3,2),(5,1),(7,1),(11,0),(13,0)],[315],[(1,[])]⟩
theorem closed10 : ClosedAt 20160 := K c10

def c11 : Cert := ⟨215040,1,96,[(2,11),(3,1),(5,1),(7,1),(11,0),(13,0)],[360],[(1,[]),(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed11 : ClosedAt 215040 := K c11

def c12 : Cert := ⟨268800,1,120,[(2,9),(3,1),(5,2),(7,1),(11,0),(13,0)],[],[]⟩
theorem closed12 : ClosedAt 268800 := K c12

def c13 : Cert := ⟨387072,1,96,[(2,11),(3,3),(5,0),(7,1),(11,0),(13,0)],[252,360,420],[(1,[]),(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed13 : ClosedAt 387072 := K c13

def c14 : Cert := ⟨435456,1,108,[(2,8),(3,5),(5,0),(7,1),(11,0),(13,0)],[216],[(1,[])]⟩
theorem closed14 : ClosedAt 435456 := K c14

def c15 : Cert := ⟨725760,1,180,[(2,8),(3,4),(5,1),(7,1),(11,0),(13,0)],[384,504,624,630],[(1,[])]⟩
theorem closed15 : ClosedAt 725760 := K c15

def c16 : Cert := ⟨6350400,1,315,[(2,6),(3,4),(5,2),(7,2),(11,0),(13,0)],[864],[(1,[])]⟩
theorem closed16 : ClosedAt 6350400 := K c16

def c17 : Cert := ⟨77414400,1,360,[(2,14),(3,3),(5,2),(7,1),(11,0),(13,0)],[800],[(1,[]),(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed17 : ClosedAt 77414400 := K c17

def c18 : Cert := ⟨94058496,1,216,[(2,11),(3,8),(5,0),(7,1),(11,0),(13,0)],[],[(17,[(17,1)])]⟩
theorem closed18 : ClosedAt 94058496 := K c18

def c19 : Cert := ⟨97542144,1,252,[(2,13),(3,5),(5,0),(7,2),(11,0),(13,0)],[],[(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed19 : ClosedAt 97542144 := K c19

def c20 : Cert := ⟨139345920,1,360,[(2,14),(3,5),(5,1),(7,1),(11,0),(13,0)],[1428],[(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed20 : ClosedAt 139345920 := K c20

def c21 : Cert := ⟨162570240,1,420,[(2,13),(3,4),(5,1),(7,2),(11,0),(13,0)],[1008],[(1,[]),(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed21 : ClosedAt 162570240 := K c21

def c22 : Cert := ⟨278691840,1,384,[(2,15),(3,5),(5,1),(7,1),(11,0),(13,0)],[],[(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed22 : ClosedAt 278691840 := K c22

def c23 : Cert := ⟨365783040,1,504,[(2,11),(3,6),(5,1),(7,2),(11,0),(13,0)],[1632],[(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed23 : ClosedAt 365783040 := K c23

def c24 : Cert := ⟨452874240,1,624,[(2,12),(3,5),(5,1),(7,1),(11,0),(13,1)],[],[(17,[(17,1)]),(19,[(19,1)])]⟩
theorem closed24 : ClosedAt 452874240 := K c24

def c25 : Cert := ⟨457228800,1,630,[(2,9),(3,6),(5,2),(7,2),(11,0),(13,0)],[],[]⟩
theorem closed25 : ClosedAt 457228800 := K c25

def c26 : Cert := ⟨5486745600,1,864,[(2,11),(3,7),(5,2),(7,2),(11,0),(13,0)],[],[(17,[(17,1)])]⟩
theorem closed26 : ClosedAt 5486745600 := K c26

def c27 : Cert := ⟨61931520000,1,800,[(2,19),(3,3),(5,4),(7,1),(11,0),(13,0)],[2760],[(23,[(23,1)])]⟩
theorem closed27 : ClosedAt 61931520000 := K c27

def c28 : Cert := ⟨163870801920,1,1008,[(2,17),(3,6),(5,1),(7,3),(11,0),(13,0)],[3500],[(1,[]),(19,[(19,1)]),(23,[(23,1)])]⟩
theorem closed28 : ClosedAt 163870801920 := K c28

def c29 : Cert := ⟨198985973760,17,1428,[(2,16),(3,6),(5,1),(7,2),(11,0),(13,0)],[4416],[(1,[(17,1)]),(19,[(17,1),(19,1)]),(23,[(17,1),(23,1)])]⟩
theorem closed29 : ClosedAt 198985973760 := K c29

def c30 : Cert := ⟨596957921280,17,1632,[(2,16),(3,7),(5,1),(7,2),(11,0),(13,0)],[5040],[(1,[(17,1)]),(19,[(17,1),(19,1)]),(23,[(17,1),(23,1)])]⟩
theorem closed30 : ClosedAt 596957921280 := K c30

def c31 : Cert := ⟨170930995200000,23,2760,[(2,22),(3,4),(5,5),(7,1),(11,0),(13,0)],[7840],[(1,[(23,1)]),(23,[(23,2)]),(29,[(23,1),(29,1)])]⟩
theorem closed31 : ClosedAt 170930995200000 := K c31

def c32 : Cert := ⟨573547806720000,1,3500,[(2,19),(3,6),(5,4),(7,4),(11,0),(13,0)],[12480],[(1,[]),(23,[(23,1)])]⟩
theorem closed32 : ClosedAt 573547806720000 := K c32

def c33 : Cert := ⟨878722060124160,391,4416,[(2,22),(3,7),(5,1),(7,2),(11,0),(13,0)],[],[(1,[(17,1),(23,1)]),(23,[(17,1),(23,2)]),(29,[(17,1),(23,1),(29,1)]),(31,[(17,1),(23,1),(31,1)])]⟩
theorem closed33 : ClosedAt 878722060124160 := K c33

def c34 : Cert := ⟨3008667923251200,17,5040,[(2,20),(3,9),(5,2),(7,3),(11,0),(13,0)],[10240],[(1,[(17,1)]),(23,[(17,1),(23,1)]),(29,[(17,1),(29,1)]),(31,[(17,1),(31,1)]),(391,[(17,2),(23,1)])]⟩
theorem closed34 : ClosedAt 3008667923251200 := K c34

def c35 : Cert := ⟨1340099002368000000,23,7840,[(2,27),(3,4),(5,6),(7,3),(11,0),(13,0)],[],[(17,[(17,1),(23,1)]),(19,[(19,1),(23,1)]),(29,[(23,1),(29,1)]),(31,[(23,1),(31,1)]),(37,[(23,1),(37,1)])]⟩
theorem closed35 : ClosedAt 1340099002368000000 := K c35

def c36 : Cert := ⟨7157876627865600000,1,12480,[(2,25),(3,7),(5,5),(7,4),(11,0),(13,1)],[],[(17,[(17,1)]),(29,[(29,1)]),(31,[(31,1)])]⟩
theorem closed36 : ClosedAt 7157876627865600000 := K c36

def c37 : Cert := ⟨30808759534092288000,17,10240,[(2,31),(3,9),(5,3),(7,3),(11,0),(13,0)],[46200,54912],[(1,[(17,1)]),(17,[(17,2)]),(19,[(17,1),(19,1)]),(37,[(17,1),(37,1)]),(41,[(17,1),(41,1)])]⟩
theorem closed37 : ClosedAt 30808759534092288000 := K c37

def c38 : Cert := ⟨1423364690475063705600000,17,46200,[(2,34),(3,10),(5,5),(7,4),(11,1),(13,0)],[],[(19,[(17,1),(19,1)]),(37,[(17,1),(37,1)]),(41,[(17,1),(41,1)]),(43,[(17,1),(43,1)]),(629,[(17,2),(37,1)])]⟩
theorem closed38 : ClosedAt 1423364690475063705600000 := K c38

def c39 : Cert := ⟨1691770603536075718656000,17,54912,[(2,38),(3,10),(5,3),(7,3),(11,1),(13,1)],[129600,180480,205920],[(1,[(17,1)]),(23,[(17,1),(23,1)]),(41,[(17,1),(41,1)]),(43,[(17,1),(43,1)]),(47,[(17,1),(47,1)]),(53,[(17,1),(53,1)]),(391,[(17,2),(23,1)]),(731,[(17,2),(43,1)])]⟩
theorem closed39 : ClosedAt 1691770603536075718656000 := K c39

def c40 : Cert := ⟨219253470218275413137817600000,17,129600,[(2,44),(3,14),(5,5),(7,3),(11,1),(13,1)],[366336],[(1,[(17,1)]),(17,[(17,2)]),(19,[(17,1),(19,1)]),(29,[(17,1),(29,1)]),(47,[(17,1),(47,1)]),(53,[(17,1),(53,1)]),(59,[(17,1),(59,1)]),(289,[(17,3)]),(323,[(17,2),(19,1)]),(391,[(17,2),(23,1)]),(493,[(17,2),(29,1)]),(799,[(17,2),(47,1)]),(893,[(17,1),(19,1),(47,1)]),(901,[(17,2),(53,1)]),(1003,[(17,2),(59,1)]),(1007,[(17,1),(19,1),(53,1)])]⟩
theorem closed40 : ClosedAt 219253470218275413137817600000 := K c40

def c41 : Cert := ⟨305330758526190945703034880000,799,180480,[(2,46),(3,11),(5,4),(7,3),(11,1),(13,1)],[],[(1,[(17,1),(47,1)]),(17,[(17,2),(47,1)]),(19,[(17,1),(19,1),(47,1)]),(29,[(17,1),(29,1),(47,1)]),(47,[(17,1),(47,2)]),(53,[(17,1),(47,1),(53,1)]),(289,[(17,3),(47,1)]),(901,[(17,2),(47,1),(53,1)])]⟩
theorem closed41 : ClosedAt 305330758526190945703034880000 := K c41

def c42 : Cert := ⟨348369402680148711985643520000,17,205920,[(2,43),(3,12),(5,4),(7,3),(11,2),(13,2)],[],[(17,[(17,2)]),(19,[(17,1),(19,1)]),(23,[(17,1),(23,1)]),(47,[(17,1),(47,1)]),(53,[(17,1),(53,1)]),(289,[(17,3)]),(391,[(17,2),(23,1)]),(437,[(17,1),(19,1),(23,1)]),(799,[(17,2),(47,1)]),(893,[(17,1),(19,1),(47,1)]),(901,[(17,2),(53,1)])]⟩
theorem closed42 : ClosedAt 348369402680148711985643520000 := K c42

def c43 : Cert := ⟨80320439265882141747255548313600000,901,366336,[(2,52),(3,17),(5,5),(7,3),(11,1),(13,1)],[846720],[(1,[(17,1),(53,1)]),(19,[(17,1),(19,1),(53,1)]),(23,[(17,1),(23,1),(53,1)]),(29,[(17,1),(29,1),(53,1)]),(31,[(17,1),(31,1),(53,1)]),(59,[(17,1),(53,1),(59,1)]),(61,[(17,1),(53,1),(61,1)]),(323,[(17,2),(19,1),(53,1)]),(361,[(17,1),(19,2),(53,1)]),(437,[(17,1),(19,1),(23,1),(53,1)]),(551,[(17,1),(19,1),(29,1),(53,1)]),(589,[(17,1),(19,1),(31,1),(53,1)]),(667,[(17,1),(23,1),(29,1),(53,1)]),(713,[(17,1),(23,1),(31,1),(53,1)]),(1121,[(17,1),(19,1),(53,1),(59,1)]),(1159,[(17,1),(19,1),(53,1),(61,1)]),(1219,[(17,1),(23,1),(53,2)]),(1273,[(17,1),(19,1),(53,1),(67,1)]),(1357,[(17,1),(23,1),(53,1),(59,1)]),(1403,[(17,1),(23,1),(53,1),(61,1)])]⟩
theorem closed43 : ClosedAt 80320439265882141747255548313600000 := K c43

def c44 : Cert := ⟨68008922335207727060236217868091392000000,901,846720,[(2,59),(3,20),(5,6),(7,5),(11,1),(13,1)],[],[(1,[(17,1),(53,1)]),(17,[(17,2),(53,1)]),(23,[(17,1),(23,1),(53,1)]),(31,[(17,1),(31,1),(53,1)]),(61,[(17,1),(53,1),(61,1)]),(67,[(17,1),(53,1),(67,1)]),(71,[(17,1),(53,1),(71,1)]),(73,[(17,1),(53,1),(73,1)]),(391,[(17,2),(23,1),(53,1)]),(529,[(17,1),(23,2),(53,1)]),(713,[(17,1),(23,1),(31,1),(53,1)]),(851,[(17,1),(23,1),(37,1),(53,1)]),(1403,[(17,1),(23,1),(53,1),(61,1)]),(1541,[(17,1),(23,1),(53,1),(67,1)]),(1633,[(17,1),(23,1),(53,1),(71,1)]),(1679,[(17,1),(23,1),(53,1),(73,1)])]⟩
theorem closed44 : ClosedAt 68008922335207727060236217868091392000000 := K c44

end Inverse330

open Inverse330 in
theorem OMA.solution : type_of% @OMA.S_oeis_a330816.main := by
  apply from_closed
  intro m h
  simp only [OMA.S_oeis_a330816.entries,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [closed0, closed1, closed2, closed3, closed4, closed5, closed6, closed7, closed8, closed9, closed10, closed11, closed12, closed13, closed14, closed15, closed16, closed17, closed18, closed19, closed20, closed21, closed22, closed23, closed24, closed25, closed26, closed27, closed28, closed29, closed30, closed31, closed32, closed33, closed34, closed35, closed36, closed37, closed38, closed39, closed40, closed41, closed42, closed43, closed44]
