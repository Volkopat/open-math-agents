import OMAStatements.S_oeis_a290136

-- Credit: @rleshner (agent: Codex, model: GPT-6)

/-!
# The exact exceptions to a sum of two nonprime squarefree numbers

For n ≥ 250000, take L = ⌊n/180⌋. A finite choice of residue classes
gives L pairs x + y = n with 3 ∣ x, 5 ∣ y, x,y > 5 and neither
summand divisible by 4 or 9. As the first summand increases by 180 the
second decreases by 180. On either side, multiples of 25 eliminate at
most L/5 + 1 candidates. For every other relevant prime p ≥ 7, multiples
of p² eliminate at most L/p² + 1. The reciprocal squares of odd integers
from 7 onwards sum to at most 1/12 by telescoping. The explicit estimates
leave a pair with both summands squarefree.

For n < 250001, a kernel-evaluated bit sieve encodes squarefree multiples
of small primes greater than those primes, together with 1. Shifting the
sieve by its members up to 85 certifies a representation for every
unlisted positive n in this range. For the listed values, a separate
bounded check rules out every pair of eligible summands.

The qualitative finiteness also follows from the density 6/π² of squarefree
integers and zero density of primes. The explicit bound and finite
verification give the full list. Mincu and Panaitopol (2006), Theorem 1,
established squarefree representations with unrestricted primality.

Sources: https://oeis.org/A290136 and https://ssmr.ro/bulletin/pdf/1/panamincu.pdf
-/

namespace NonprimeSquarefree
open Finset OMA.S_oeis_a290136

private def hit (L A d : ℕ) := (range L).filter (fun t => d ∣ A+180*t)

private theorem bucket_bound (L A D d : ℕ) (hd : 0 < d)
    (hgap : ∀ i j : ℕ, i < j → D ∣ A+180*i → D ∣ A+180*j → d ∣ j-i) :
    (hit L A D).card ≤ L/d+1 := by
  have strict {i j : ℕ} (hi : i ∈ hit L A D) (hj : j ∈ hit L A D) (hlt : i<j) : i/d < j/d := by
    have hdiv := hgap i j hlt (mem_filter.mp hi).2 (mem_filter.mp hj).2
    have hle := Nat.le_of_dvd (show 0 < j-i by omega) hdiv
    have h := Nat.div_le_div_right (c:=d) (show i+d ≤ j by omega)
    rw [Nat.add_div_right _ hd] at h
    omega
  have h := Finset.card_le_card_of_injOn (s:=hit L A D) (t:=range (L/d+1))
    (fun i => i/d) (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.le_of_lt (mem_range.mp (mem_filter.mp hi).1)))))
    (fun i hi j hj heq => by
      rcases lt_trichotomy i j with h|h|h
      · exact False.elim ((strict hi hj h).ne heq)
      · exact h
      · exact False.elim ((strict hj hi h).ne heq.symm))
  simpa using h

private theorem hit_five (L A : ℕ) : (hit L A 25).card ≤ L/5+1 := by
  apply bucket_bound _ _ _ _ (by decide)
  intro i j h hi hj
  omega

private theorem hit_other (L A p : ℕ) (hp : p.Coprime 180) (hpos : 0<p) :
    (hit L A (p^2)).card ≤ L/(p^2)+1 := by
  apply bucket_bound _ _ _ _ (by positivity)
  intro i j hij hi hj
  apply (hp.pow_left 2).dvd_of_dvd_mul_left
  have h := Nat.dvd_sub hj hi
  rwa [Nat.add_sub_add_left, ← Nat.mul_sub] at h

private theorem reciprocal_bound (K : ℕ) :
    ∑ i ∈ range K, (1:ℚ)/(2*(i:ℚ)+7)^2 ≤ 1/12 - 1/(4*((K:ℚ)+3)) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ]
    push_cast
    rw [show (K:ℚ)+1+3 = K+4 by ring]
    have hstep : 1/(2*(K:ℚ)+7)^2 ≤ 1/(4*((K:ℚ)+3))-1/(4*((K:ℚ)+4)) := by
      field_simp
      nlinarith
    linarith

private def other (L A i : ℕ) :=
  if (2*i+7).Coprime 180 then hit L A ((2*i+7)^2) else ∅

private def excluded (L A K : ℕ) :=
  hit L A 25 ∪ (range K).biUnion (other L A)

private theorem excluded_bound (L A K : ℕ) :
    ((excluded L A K).card:ℚ) ≤ (17/60)*(L:ℚ)+K+1 := by
  have term (i : ℕ) : ((other L A i).card:ℚ) ≤ (L:ℚ)*(1/(2*(i:ℚ)+7)^2)+1 := by
    unfold other
    split_ifs with hp
    · have h := hit_other L A (2*i+7) hp (by omega)
      have hr : ((hit L A ((2*i+7)^2)).card:ℚ) ≤ ((L/((2*i+7)^2):ℕ):ℚ)+1 := by exact_mod_cast h
      have hd : ((L/((2*i+7)^2):ℕ):ℚ) ≤ (L:ℚ)/(((2*i+7)^2:ℕ):ℚ) := Nat.cast_div_le
      push_cast at hd
      simpa [div_eq_mul_inv] using (hr.trans (add_le_add_left hd 1))
    · simp
      positivity
  have h₁ := card_union_le (hit L A 25) ((range K).biUnion (other L A))
  have h₂ := card_biUnion_le (s:=range K) (t:=other L A)
  have h₃ := hit_five L A
  have h₄ : ((excluded L A K).card:ℚ) ≤ ((L/5:ℕ):ℚ)+1 + ∑ i ∈ range K, ((other L A i).card:ℚ) := by
    exact_mod_cast (show (excluded L A K).card ≤ L/5+1 + ∑ i ∈ range K, (other L A i).card by
      unfold excluded
      omega)
  have h₅ := sum_le_sum (s:=range K) (fun i _ => term i)
  rw [sum_add_distrib, ← mul_sum] at h₅
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h₅
  have h₆ := reciprocal_bound K
  have h₇ : (L:ℚ)*(∑ i ∈ range K, (1:ℚ)/(2*(i:ℚ)+7)^2) ≤ (L:ℚ)*(1/12) :=
    mul_le_mul_of_nonneg_left (h₆.trans (sub_le_self _ (by positivity))) (by positivity)
  have h₈ : ((L/5:ℕ):ℚ) ≤ (L:ℚ)/5 := by exact_mod_cast (Nat.cast_div_le (α:=ℚ) (m:=L) (n:=5))
  linarith

private theorem squarefree_member {n L A t : ℕ} (hpos : 0<A+180*t) (hle : A+180*t≤n)
    (ht : t<L) (h4 : ¬4∣A) (h9 : ¬9∣A) (hout : t ∉ excluded L A (n.sqrt/2+1)) :
    Squarefree (A+180*t) := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hsq := Nat.le_of_dvd hpos hd
  have hpsqrt := Nat.le_sqrt.mpr (hsq.trans hle)
  have h2 := hp.two_le
  by_cases hp7 : p<7
  · interval_cases p <;> norm_num at *
    all_goals first | omega | exact hout (mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr ht, hd⟩))
  have hodd : p%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
  let i := (p-7)/2
  have hpi : 2*i+7=p := by dsimp [i]; omega
  have hi : i<n.sqrt/2+1 := by dsimp [i]; omega
  have hcop : p.Coprime 180 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hdiv : p ∣ 2*2*3*3*5 := by simpa using h
    simp only [hp.dvd_mul] at hdiv
    rcases hdiv with (((h|h)|h)|h)|h <;> have := Nat.le_of_dvd (by decide) h <;> omega
  apply hout
  apply mem_union_right
  apply mem_biUnion.mpr
  refine ⟨i, mem_range.mpr hi, ?_⟩
  simp only [other,hpi,if_pos hcop,hit,mem_filter,mem_range,pow_two]
  exact ⟨ht,hd⟩

set_option maxRecDepth 7000 in
set_option maxHeartbeats 2000000 in
private theorem large (n : ℕ) (hn : 250000 ≤ n) :
    ∃ a b : ℕ, IsNonprimeSquarefree a ∧ IsNonprimeSquarefree b ∧ n=a+b := by
  classical
  have chooseBases : ∀ r : Fin 180, ∃ A : Fin 180,
      5<A.val ∧ 5<180+r.val-A.val ∧ 3∣A.val ∧ 5∣180+r.val-A.val ∧
      ¬4∣A.val ∧ ¬9∣A.val ∧ ¬4∣180+r.val-A.val ∧ ¬9∣180+r.val-A.val := by decide
  obtain ⟨av,ha,hb,ha3,hb5,ha4,ha9,hb4,hb9⟩ := chooseBases ⟨n%180,Nat.mod_lt _ (by decide)⟩
  let A := av.val
  let B := 180+n%180-A
  let L := n/180
  let K := n.sqrt/2+1
  have ha' : 5<A := ha
  have hb' : 5<B := hb
  have hab : A+B = 180+n%180 := by dsimp [A,B]; have := av.isLt; omega
  have hn' : n = 180*L+n%180 := by dsimp [L]; omega
  have hroot : 500*n.sqrt ≤ n := by
    have hu : 500≤n.sqrt := Nat.le_sqrt.mpr (by omega)
    have h := Nat.sqrt_le n
    exact (Nat.mul_le_mul_right n.sqrt hu).trans h
  let rejects := excluded L A K ∪ (excluded L B K).image (fun j => L-1-j)
  have bound : rejects.card < L := by
    have hc := card_union_le (excluded L A K) ((excluded L B K).image (fun j=>L-1-j))
    have hd := card_image_le (s:=excluded L B K) (f:=fun j=>L-1-j)
    have h : (rejects.card:ℚ) ≤ ((excluded L A K).card:ℚ)+((excluded L B K).card:ℚ) := by
      exact_mod_cast (show rejects.card ≤ (excluded L A K).card+(excluded L B K).card by dsimp [rejects]; omega)
    have hA := excluded_bound L A K
    have hB := excluded_bound L B K
    have hL : n < 180*L+180 := by dsimp [L]; omega
    have hK : 2*K ≤ n.sqrt+2 := by dsimp [K]; omega
    have hr : 500*(n.sqrt:ℚ) ≤ n := by exact_mod_cast hroot
    have hl : (n:ℚ) < 180*L+180 := by exact_mod_cast hL
    have hk : 2*(K:ℚ) ≤ n.sqrt+2 := by exact_mod_cast hK
    have hnq : (250000:ℚ) ≤ n := by exact_mod_cast hn
    exact_mod_cast (show (rejects.card:ℚ) < L by linarith)
  obtain ⟨t,ht,hout⟩ := exists_mem_notMem_of_card_lt_card (s:=rejects) (t:=range L) (by simpa using bound)
  have htL := mem_range.mp ht
  let u := L-1-t
  have hu : u<L := by dsimp [u]; omega
  have hsum : n=(A+180*t)+(B+180*u) := by dsimp [u]; omega
  have hO := not_or.mp (fun h => hout (mem_union.mpr h))
  have hO' : u ∉ excluded L B K := fun h => hO.2 (mem_image.mpr ⟨u,h,by dsimp [u]; omega⟩)
  have hA := squarefree_member (n:=n) (by omega : 0<A+180*t) (by omega) htL ha4 ha9 hO.1
  have hB := squarefree_member (n:=n) (by omega : 0<B+180*u) (by omega) hu hb4 hb9 hO'
  refine ⟨_, _, ⟨hA, ?_⟩, ⟨hB, ?_⟩,hsum⟩
  · have hda : 3 ∣ A := ha3
    exact Nat.not_prime_of_dvd_of_lt (dvd_add hda (dvd_mul_of_dvd_left (by decide:3∣180) t)) (by decide) (by omega)
  · have hdb : 5 ∣ B := hb5
    exact Nat.not_prime_of_dvd_of_lt (dvd_add hdb (dvd_mul_of_dvd_left (by decide:5∣180) u)) (by decide) (by omega)

private def wordUnion (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => f a ||| wordUnion f l

private def cap : ℕ := 250001
private def period (d w : ℕ) : ℕ := ((1 <<< (d*w))-1)/((1 <<< d)-1)
private def per (d : ℕ) : ℕ := period d (cap/d+1)
private def smallPrimes : List ℕ := [2,3,5,7,11,13]
private def allBits : ℕ := (1 <<< cap)-1
private def squared : ℕ := wordUnion (fun i => per ((i+2)^2)) (List.range 499)
private def comps : ℕ := wordUnion (fun p => per p <<< (2*p)) smallPrimes
private def good : ℕ := ((allBits ^^^ squared) &&& comps) ||| 2
private def covered : ℕ := wordUnion (fun i => good <<< i)
    ((List.range 86).filter (fun i => good.testBit i))
private def exceptions : List ℕ := [1,3,4,5,6,8,9,10,13,14,17,18,19,26,33,38,46,62,82]
private def exceptionalMask : ℕ := wordUnion (fun x => 1 <<< x) (0 :: exceptions)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem checked : ((covered ||| exceptionalMask) &&& allBits) = allBits := by decide
private theorem union_spec (f : ℕ → ℕ) (l : List ℕ) (n : ℕ) :
    (wordUnion f l).testBit n = true ↔ ∃ i ∈ l, (f i).testBit n = true := by
  induction l with
  | nil => simp [wordUnion]
  | cons a l ih => simp [wordUnion, ih]

private theorem period_spec (d w n : ℕ) (hd : 0 < d) :
    (period d w).testBit n = true ↔ ∃ i < w, d*i = n := by
  let s := (range w).image (fun i => d*i)
  have hd' : 0 < (2:ℕ)^d-1 := by have := Nat.one_lt_two_pow (by omega : d≠0); omega
  have heq : period d w = ∑ j ∈ s, 2^j := by
    dsimp [period,s]
    rw [sum_image (by intro i hi j hj h; exact Nat.eq_of_mul_eq_mul_left hd h)]
    have hg := geom_sum_mul_of_one_le (show 1 ≤ (2:ℕ)^d by omega) w
    simp only [Nat.shiftLeft_eq,one_mul,pow_mul]
    rw [← hg, Nat.mul_div_cancel _ hd']
  have hs := Finset.toFinset_bitIndices_sum_two_pow s
  rw [heq, ← Nat.mem_bitIndices, ← List.mem_toFinset, hs]
  simp [s]

private theorem per_spec (d n : ℕ) (hd : 0 < d) (hn : n < cap) :
    (per d).testBit n = true ↔ d ∣ n := by
  rw [per,period_spec _ _ _ hd]
  constructor
  · rintro ⟨i,_,hi⟩; exact ⟨i,hi.symm⟩
  · intro h
    exact ⟨n/d, by have := Nat.div_le_div_right (Nat.le_of_lt hn) (c:=d); omega,
      Nat.mul_div_cancel' h⟩

private theorem all_spec {n : ℕ} (hn : n < cap) : allBits.testBit n = true := by
  simp [allBits, Nat.shiftLeft_eq, hn]

private theorem good_sound {n : ℕ} (hn : n < cap) (hg : good.testBit n = true) :
    IsNonprimeSquarefree n := by
  by_cases hone : n = 1
  · subst n; exact ⟨squarefree_one, Nat.not_prime_one⟩
  have htwo : (2:ℕ).testBit n = false := by
    rw [show (2:ℕ)=2^1 by decide, Nat.testBit_two_pow]
    simp [Ne.symm hone]
  have hk := all_spec hn
  simp only [good, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, htwo, hk,
    Bool.or_false, Bool.true_xor, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨p,hp,hm⟩ := (union_spec _ smallPrimes n).mp hg.2
  simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq] at hm
  have hpgt : 1 < p := by simp [smallPrimes] at hp; omega
  have hnp : 2*p ≤ n := hm.1
  have hd : p ∣ n-2*p := (per_spec p _ (by omega) (by omega)).mp hm.2
  have hd' : p ∣ n := by
    simpa [Nat.sub_add_cancel hnp] using dvd_add hd (dvd_mul_left p 2)
  refine ⟨Nat.squarefree_iff_prime_squarefree.mpr ?_, Nat.not_prime_of_dvd_of_lt hd' hpgt (by omega)⟩
  intro q hq hdiv
  have hle := Nat.le_of_dvd (show 0 < n by omega) hdiv
  have hq2 := hq.two_le
  have hbound : q ≤ 500 := by
    by_contra! h
    have hh := Nat.mul_self_le_mul_self (show 501 ≤ q by omega)
    dsimp [cap] at hn
    nlinarith
  have he : q-2+2=q := by omega
  have hm' : (per ((q-2+2)^2)).testBit n = true := by rw [he]; exact (per_spec _ _ (by positivity) hn).mpr (by simpa [pow_two] using hdiv)
  have hbit : squared.testBit n = true := (union_spec _ _ _).mpr ⟨q-2,List.mem_range.mpr (by omega),hm'⟩
  simp [hbit] at hg

private theorem cover_sound {n : ℕ} (hn : n < cap) (hcov : covered.testBit n = true) :
    ∃ a b : ℕ, IsNonprimeSquarefree a ∧ IsNonprimeSquarefree b ∧ n = a+b := by
  obtain ⟨i,hi,hw⟩ := (union_spec _ _ _).mp hcov
  simp only [List.mem_filter,List.mem_range] at hi
  simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq] at hw
  exact ⟨i,n-i,good_sound (by omega) hi.2,good_sound (by omega) hw.2,by omega⟩

private theorem finiteCover {n : ℕ} (hn : n < cap) (he : n ∉ 0 :: exceptions) :
    ∃ a b : ℕ, IsNonprimeSquarefree a ∧ IsNonprimeSquarefree b ∧ n = a+b := by
  have hex : exceptionalMask.testBit n = false := by
    by_contra! h
    have htrue : exceptionalMask.testBit n = true := by simpa using h
    obtain ⟨i,hi,hw⟩ := (union_spec (fun i => 1 <<< i) (0 :: exceptions) n).mp htrue
    simp only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow,decide_eq_true_eq] at hw
    exact he (hw ▸ hi)
  have hc := congrArg (fun w : ℕ => w.testBit n) checked
  simp only [Nat.testBit_and,Nat.testBit_or,all_spec hn,hex,Bool.or_false,Bool.and_true] at hc
  exact cover_sound hn hc

private def possible (n : ℕ) : Prop :=
  ¬n.Prime ∧ ¬4∣n ∧ ¬9∣n ∧ ¬25∣n ∧ ¬49∣n

private instance (n : ℕ) : Decidable (possible n) := by unfold possible; infer_instance

private theorem possible_of_good {n : ℕ} (hn : IsNonprimeSquarefree n) : possible n :=
  ⟨hn.2, Nat.squarefree_iff_prime_squarefree.mp hn.1 2 (by decide),
    Nat.squarefree_iff_prime_squarefree.mp hn.1 3 (by decide),
    Nat.squarefree_iff_prime_squarefree.mp hn.1 5 (by decide),
    Nat.squarefree_iff_prime_squarefree.mp hn.1 7 (by decide)⟩

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem exceptional_check :
    ∀ a b : Fin 83, (a.val+b.val) ∈ exceptions → ¬(possible a.val ∧ possible b.val) := by decide

private theorem exception_small {n : ℕ} (he : n ∈ exceptions) : 0<n ∧ n≤82 := by
  simp [exceptions] at he
  omega

private theorem exceptional {n : ℕ} (he : n ∈ exceptions) :
    ¬ ∃ a b : ℕ, IsNonprimeSquarefree a ∧ IsNonprimeSquarefree b ∧ n=a+b := by
  rintro ⟨a,b,ha,hb,rfl⟩
  have hle := (exception_small he).2
  exact exceptional_check ⟨a,by omega⟩ ⟨b,by omega⟩ he ⟨possible_of_good ha, possible_of_good hb⟩

end NonprimeSquarefree

open NonprimeSquarefree OMA.S_oeis_a290136 in
theorem OMA.solution : type_of% @OMA.S_oeis_a290136.main := by
  ext n
  have hh : n ∈ ({1, 3, 4, 5, 6, 8, 9, 10, 13, 14, 17, 18, 19, 26, 33, 38, 46, 62, 82} : Set ℕ) ↔ n ∈ exceptions := by
    simp [exceptions]
  rw [hh]
  constructor
  · rintro ⟨hp,hn⟩
    by_contra he
    by_cases h : 250000 ≤ n
    · exact hn (large n h)
    · exact hn (finiteCover (by dsimp [cap]; omega) (by simpa [Nat.ne_of_gt hp] using he))
  · intro he
    exact ⟨(exception_small he).1, exceptional he⟩
