import OMAStatements.S_oeis_a076070

namespace A76070
open Finset
noncomputable section

private def residues (q : ℕ) [NeZero q] : ℕ → Finset (ZMod q)
  | 0 => {0}
  | k+1 => let s := residues q k
           s ∪ s.image (fun x => x+100^k)

private lemma zero_mem (q : ℕ) [NeZero q] (k : ℕ) : 0 ∈ residues q k := by
  induction k with
  | zero => simp [residues]
  | succ k ih => exact mem_union_left _ ih

private lemma add_closed (q : ℕ) [NeZero q] (s : Finset (ZMod q)) (u : ZMod q)
    (hu : IsUnit u) (h0 : 0 ∈ s) (h : ∀ x ∈ s, x+u ∈ s) : s=univ := by
  obtain ⟨v,rfl⟩ := hu
  have all (j : ℕ) : (j:ZMod q)*(v:ZMod q) ∈ s := by
    induction j with
    | zero => simpa using h0
    | succ j ih => simpa [Nat.cast_succ,add_mul] using h _ ih
  apply Finset.eq_univ_of_forall
  intro x
  simpa [mul_assoc] using all (x*(↑(v⁻¹):ZMod q)).val

private lemma coverage (q : ℕ) [NeZero q] (hc : Nat.Coprime 10 q) (k : ℕ) :
    min q (k+1) ≤ (residues q k).card := by
  have h10 : IsUnit (10:ZMod q) := (ZMod.isUnit_iff_coprime 10 q).mpr hc
  have h100 : IsUnit (100:ZMod q) := by simpa only [show (100:ZMod q)=10*10 by norm_num] using h10.mul h10
  induction k with
  | zero => simp [residues]
  | succ k ih =>
    let s := residues q k
    by_cases h : s=univ
    · apply le_trans (min_le_left _ _)
      change q ≤ (s ∪ _).card
      have eq : s.card=q := by rw [h,Finset.card_univ,ZMod.card]
      exact eq.ge.trans (Finset.card_le_card Finset.subset_union_left)
    have bad : ¬ ∀ x ∈ s, x+100^k ∈ s := fun e => h (add_closed q s _ (h100.pow k) (zero_mem q k) e)
    push Not at bad
    obtain ⟨x,hx,hout⟩ := bad
    have lt : s.card < (residues q (k+1)).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_of_subset (Finset.subset_union_left) |>.mpr
      exact ⟨x+100^k,mem_union_right _ (mem_image.mpr ⟨x,hx,rfl⟩),hout⟩
    change min q (k+1) ≤ s.card at ih
    omega

def word : List ℕ → (ℕ → Bool) → List ℕ
  | [], _ => []
  | d::ds, b => word ds b ++ (if b ds.length then [d,d+1] else [d+1,d])

private lemma word_length (ds : List ℕ) (b : ℕ → Bool) : (word ds b).length=2*ds.length := by
  induction ds with
  | nil => simp [word]
  | cons d ds ih => simp [word,ih];split <;> simp <;> omega

private lemma word_agree {ds : List ℕ} {b c : ℕ → Bool} (h : ∀ j < ds.length,b j=c j) :
    word ds b=word ds c := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [word,word,ih (fun j hj => h j (by simp;omega)),h ds.length (by simp)]

private lemma word_bag (ds : List ℕ) (b c : ℕ → Bool) :
   (word ds b : Multiset ℕ) = (word ds c : Multiset ℕ) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [word,← Multiset.coe_add];rw [ih]
    cases b ds.length <;> cases c ds.length <;> simp <;> exact List.Perm.append_left _ (List.Perm.swap _ _ _)

def val (l : List ℕ) : ℕ := Nat.ofDigits 10 l

private lemma realize (q : ℕ) [NeZero q] (ds : List ℕ) (v : ZMod q)
    (hv : v ∈ residues q ds.length) :
    ∃ b : ℕ → Bool, (val (word ds b):ZMod q) =
      ↑(val (word ds (fun _ => false)))+9*v := by
  induction ds generalizing v with
  | nil =>
    simp [residues] at hv;subst v;exact ⟨fun _ => false, by simp [word,val]⟩
  | cons d ds ih =>
    have finish (x : ZMod q) (hx : x ∈ residues q ds.length) (on : Bool) :
        ∃ b : ℕ → Bool, (val (word (d::ds) b):ZMod q) =
          ↑(val (word (d::ds) (fun _ => false)))+9*(if on then x+100^ds.length else x) := by
      obtain ⟨b,hb⟩ := ih x hx
      let c (j : ℕ) := if j=ds.length then on else b j
      have sub : word ds c=word ds b := word_agree fun j hj => by simp [c,ne_of_lt hj]
      refine ⟨c,?_⟩
      have ce : c ds.length = on := by simp [c]
      simp only [word,ce,Bool.false_eq_true,if_false,val,Nat.ofDigits_append,word_length,
        Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,sub]
      unfold val at hb
      rw [hb]
      have pw : (10:ZMod q)^(2*ds.length)=(100:ZMod q)^ds.length := by rw [pow_mul];norm_num
      cases on <;> simp [Nat.ofDigits_cons,pw] <;> push_cast <;> ring
    rcases mem_union.mp hv with h | h
    · exact finish v h false
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      exact finish x hx true
end
end A76070

namespace A76070
theorem split_modulus (n : ℕ) (hn : 0 < n) :
    ∃ g q t : ℕ, n=g*q ∧ g ∣ 10^t ∧ Nat.Coprime 10 q ∧ 2^t ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have peel (p : ℕ) (hp : p=2 ∨ p=5) (hd : p ∣ n) :
        ∃ g q t : ℕ, n=g*q ∧ g ∣ 10^t ∧ Nat.Coprime 10 q ∧ 2^t ≤ n := by
      obtain ⟨m,hm⟩ := hd
      have pos : 0 < m := by rcases hp with rfl|rfl <;> omega
      have less : m < n := by rcases hp with rfl|rfl <;> omega
      obtain ⟨g,q,t,eq,dvd,cop,bound⟩ := ih m less pos
      refine ⟨p*g,q,t+1,by rw [mul_assoc,←eq,←hm],?_,cop,?_⟩
      · rw [pow_succ,mul_comm]
        exact Nat.mul_dvd_mul dvd (by rcases hp with rfl|rfl <;> decide)
      · rw [pow_succ];rcases hp with rfl|rfl <;> omega
    by_cases h2 : 2 ∣ n
    · exact peel 2 (Or.inl rfl) h2
    by_cases h5 : 5 ∣ n
    · exact peel 5 (Or.inr rfl) h5
    refine ⟨1,n,0,by simp,by simp,?_,by omega⟩
    exact (Nat.coprime_mul_iff_left.mpr
      ⟨Nat.prime_two.coprime_iff_not_dvd.mpr h2, Nat.prime_five.coprime_iff_not_dvd.mpr h5⟩ : Nat.Coprime (2*5) n)

end A76070

namespace A76070
theorem zeros_budget (n t : ℕ) (h : 2^t ≤ n) : t ≤ n/100+10 := by
  have aux (k : ℕ) : 100*(k+1) < 2^(k+10) := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+10=(k+10)+1 by omega,pow_succ]
      omega
  by_contra hn
  have smaller : 2^(n/100+10) ≤ 2^t := Nat.pow_le_pow_right (by decide) (by omega)
  have := aux (n/100)
  omega

theorem paired_capacity (n : ℕ) (hn : 2000 ≤ n) :
    n/5+1+(n/100+10) ≤ n/10+10*(n/100)+100*(n/1000) ∧
    n-1 ≤ 5*(n/5+1) := by omega
end A76070

namespace A76070
def prefixCount (x d u : ℕ) := x/(10*u)*u + min u (x%(10*u)-d*u)

theorem prefix_step (x d u : ℕ) (hd : d < 10) (hu : u=1 ∨ u=10 ∨ u=100) :
    prefixCount (x+1) d u = prefixCount x d u + if x/u%10=d then 1 else 0 := by
  rcases hu with rfl|rfl|rfl <;> unfold prefixCount <;>
    split <;> (try simp only [Nat.mul_one,Nat.div_one] at *) <;> omega

theorem prefix_floor (x n d u : ℕ) (hu : u=1 ∨ u=10 ∨ u=100) :
    u*(n/(10*u)) ≤ prefixCount (x+n) d u-prefixCount x d u := by
  rcases hu with rfl|rfl|rfl <;> unfold prefixCount <;>
    (try simp only [Nat.mul_one,Nat.one_mul]) <;> omega

end A76070

namespace A76070
def lowerCount (a n d : ℕ) : ℕ :=
  prefixCount (a+n) d 1 - prefixCount a d 1 +
  (prefixCount (a+n) d 10 - prefixCount a d 10) +
  (prefixCount (a+n) d 100 - prefixCount a d 100)

theorem prefix_mono (a n d u : ℕ) (hd : d < 10) (hu : u=1 ∨ u=10 ∨ u=100) :
    prefixCount a d u ≤ prefixCount (a+n) d u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [←Nat.add_assoc,prefix_step _ _ _ hd hu]; omega

theorem lowerCount_valid (a n d : ℕ) (ha : 100 ≤ a) (hd : d < 10) :
    lowerCount a n d ≤ ((List.range n).flatMap fun i => Nat.digits 10 (a+i)).count d := by
  induction n with
  | zero => simp [lowerCount]
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.count_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    have hx : 100 ≤ a+n := by omega
    have dig : Nat.digits 10 (a+n) =
        (a+n)%10 :: ((a+n)/10)%10 :: ((a+n)/100)%10 :: Nat.digits 10 ((a+n)/100/10) := by
      nth_rw 1 [Nat.digits_def' (by decide : 1 < 10) (by omega : 0 < a+n)]
      rw [Nat.digits_def' (by decide : 1 < 10) (by omega : 0 < (a+n)/10)]
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.digits_def' (by decide : 1 < 10) (by omega : 0 < (a+n)/100)]
    rw [dig]
    simp only [List.count_cons]
    unfold lowerCount at *
    rw [←Nat.add_assoc,prefix_step _ _ 1 hd (by decide),prefix_step _ _ 10 hd (by decide),
      prefix_step _ _ 100 hd (by decide)]
    have := prefix_mono a n d 1 hd (by decide)
    have := prefix_mono a n d 10 hd (by decide)
    have := prefix_mono a n d 100 hd (by decide)
    simp only [Nat.div_one,beq_iff_eq]
    omega
end A76070

namespace A76070
noncomputable section
open Finset
private lemma cancel_baseline (q V : ℕ) (h : Nat.gcd 9 q ∣ V) :
    ∃ v : ZMod q, (V : ZMod q)+9*v=0 := by
  obtain ⟨u,rfl⟩ := h
  have bez := congrArg (fun z : ℤ => (z : ZMod q)) (Nat.gcd_eq_gcd_ab 9 q)
  push_cast at bez
  rw [ZMod.natCast_self] at bez
  refine ⟨-((Nat.gcdA 9 q : ℤ) : ZMod q)*u,?_⟩
  push_cast
  linear_combination (u : ZMod q)*bez

theorem arrange_mod (q : ℕ) [NeZero q] (cop : Nat.Coprime 10 q) (ds high : List ℕ)
    (hpairs : q-1 ≤ ds.length)
    (hbase : Nat.gcd 9 q ∣ val (word ds (fun _ => false) ++ high)) :
    ∃ b : ℕ → Bool, q ∣ val (word ds b ++ high) := by
  obtain ⟨v,hv⟩ := cancel_baseline _ _ hbase
  have bound := coverage q cop ds.length
  rw [min_eq_left (by omega)] at bound
  have all : residues q ds.length = univ := Finset.eq_univ_of_card _ (by
    apply Nat.le_antisymm (Finset.card_le_univ _)
    simpa [ZMod.card] using bound)
  obtain ⟨b,hb⟩ := realize _ ds v (by simp [all])
  refine ⟨b,(ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  simp only [val,Nat.ofDigits_append,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    word_length] at hv ⊢
  unfold val at hb
  rw [hb]
  linear_combination hv
end
end A76070

namespace A76070
def block (a n : ℕ) := (List.range n).flatMap fun i => Nat.digits 10 (a+i)

private lemma block_sum_mod (a n : ℕ) :
    ((List.range n).map (a+·)).sum ≡ (block a n).sum [MOD 9] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.sum_range_succ]
    unfold block
    rw [List.range_succ,List.flatMap_append,List.sum_append]
    simpa [block] using ih.add (Nat.modEq_nine_digits_sum (a+n))

private lemma twice_sum (a n : ℕ) :
    2*((List.range n).map (a+·)).sum+n = n*(2*a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ]
    nlinarith

theorem gcd_dvd_sum (a n q : ℕ) (hq : q ∣ n) : Nat.gcd 9 q ∣ (block a n).sum := by
  let e := Nat.gcd 9 q
  have en : e ∣ n := (Nat.gcd_dvd_right ..).trans hq
  have e9 : e ∣ 9 := Nat.gcd_dvd_left .. 
  let S := ((List.range n).map (a+·)).sum
  have key : e ∣ 2*S+n := by rw [show 2*S+n=n*(2*a+n) from twice_sum a n];exact dvd_mul_of_dvd_left en _
  have es : e ∣ 2*S := (Nat.dvd_add_iff_left en).mpr key
  have eS : e ∣ S := (Nat.Coprime.coprime_dvd_left e9 (by decide : Nat.Coprime 9 2)).dvd_of_dvd_mul_left es
  exact Nat.modEq_zero_iff_dvd.mp (((block_sum_mod a n).of_dvd e9).symm.trans (Nat.modEq_zero_iff_dvd.mpr eS))
end A76070

namespace A76070
private lemma zeros_val (t : ℕ) : val (List.replicate t 0)=0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ,val,Nat.ofDigits_cons,show Nat.ofDigits 10 (List.replicate t 0)=0 from ih]

theorem build_multiple (a n g q t leader : ℕ) [NeZero q] (ds spare : List ℕ)
    (fac : n=g*q) (gt : g ∣ 10^t) (cop : Nat.Coprime 10 q) (hpairs : q-1 ≤ ds.length)
    (positive : leader ≠ 0)
    (bag : (List.replicate t 0 ++ word ds (fun _ => false) ++ spare ++ [leader]).Perm (block a n)) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m).Perm (block a n) := by
  let high := spare ++ [leader]
  have e9 := Nat.gcd_dvd_left 9 q
  have hsum := gcd_dvd_sum a n q (by rw [fac];exact dvd_mul_left ..)
  rw [←bag.sum_eq] at hsum
  have zeroSum : (List.replicate t (0:ℕ)).sum=0 := by simp
  simp only [List.sum_append,zeroSum,zero_add] at hsum
  have hbase : Nat.gcd 9 q ∣ val (word ds (fun _ => false) ++ high) := by
    have m9 := Nat.ofDigits_modEq' 10 1 9 (by decide) (word ds (fun _ => false) ++ high)
    rw [Nat.ofDigits_one] at m9
    apply Nat.modEq_zero_iff_dvd.mp ((m9.of_dvd e9).trans ?_)
    apply Nat.modEq_zero_iff_dvd.mpr
    simpa only [high,List.sum_append,Nat.add_assoc] using hsum
  obtain ⟨b,hb⟩ := arrange_mod q cop ds high hpairs hbase
  let w := List.replicate t 0 ++ (word ds b ++ high)
  have perm : w.Perm (block a n) := by
    apply List.Perm.trans _ bag
    simp only [w,high,List.append_assoc]
    apply List.Perm.append_left
    apply List.Perm.append_right
    exact Quotient.exact (word_bag ds b (fun _ => false))
  have digs : Nat.digits 10 (val w) = w := by
    apply Nat.digits_ofDigits _ (by decide)
    · intro i hi
      have := perm.mem_iff.mp hi
      obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp this
      exact Nat.digits_lt_base (by decide) hj
    · intro h
      simpa [w,high] using positive
  refine ⟨val w,?_,?_,by rw [digs];exact perm⟩
  · by_contra! hn
    have z : val w=0 := by omega
    rw [z,Nat.digits_zero] at digs
    simp [w,high] at digs
  · change n ∣ Nat.ofDigits 10 (List.replicate t 0 ++ (word ds b ++ high))
    rw [Nat.ofDigits_append,show Nat.ofDigits 10 (List.replicate t 0)=0 from zeros_val t,
      zero_add,List.length_replicate,fac]
    exact Nat.mul_dvd_mul gt hb
end A76070

namespace A76070
theorem build_counted (a n g q t : ℕ) [NeZero q] (ds : List ℕ)
    (fac : n=g*q) (gt : g ∣ 10^t) (cop : Nat.Coprime 10 q) (hpairs : q-1 ≤ ds.length)
    (counts : ∀ d, (List.replicate t 0 ++ word ds (fun _ => false) ++ [9]).count d ≤
      (block a n).count d) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m).Perm (block a n) := by
  let all : Multiset ℕ := block a n
  let need : Multiset ℕ := ((List.replicate t 0 ++ word ds (fun _ => false) ++ [9]) : List ℕ)
  have sub : need ≤ all := Multiset.le_iff_count.mpr (by simpa only [all,need,Multiset.coe_count] using counts)
  let spare := (all-need).toList
  apply build_multiple a n g q t 9 ds spare fac gt cop hpairs (by decide)
  apply Multiset.coe_eq_coe.mp
  change _ = all
  have eq := Multiset.sub_add_cancel sub
  unfold need at eq
  simp only [←Multiset.coe_add] at eq ⊢
  simp only [spare,Multiset.coe_toList]
  unfold need
  simp only [←Multiset.coe_add]
  convert eq using 1; ac_rfl

private lemma count_word (ds : List ℕ) (d : ℕ) :
    (word ds (fun _ => false)).count d = ds.count d + (ds.map (·+1)).count d := by
  induction ds with
  | nil => rfl
  | cons j js ih => simp [word,List.count_cons,ih];omega

def groups (u v w x y : ℕ) := List.replicate u 0 ++ List.replicate v 2 ++ List.replicate w 4 ++
  List.replicate x 6 ++ List.replicate y 8

def needCount (t u v w x y d : ℕ) : ℕ :=
  [t+u,u,v,v,w,w,x,x,y,y+1][d]?.getD 0

theorem groups_count (t u v w x y d : ℕ) :
    (List.replicate t 0 ++ word (groups u v w x y) (fun _ => false) ++ [9]).count d =
      needCount t u v w x y d := by
  simp only [List.count_append,count_word,groups,List.map_append,List.map_replicate]
  by_cases hd : d < 10
  · interval_cases d <;> simp [List.count_replicate,needCount]
  · have ne (i : ℕ) (hi : i < 10) : i ≠ d := by omega
    have ng : ([t+u,u,v,v,w,w,x,x,y,y+1]:List ℕ)[d]?=none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hd)
    simp [needCount,ng,List.count_replicate,ne _ (by decide : 0 < 10),ne _ (by decide : 1 < 10),
      ne _ (by decide : 2 < 10),ne _ (by decide : 3 < 10),ne _ (by decide : 4 < 10),
      ne _ (by decide : 5 < 10),ne _ (by decide : 6 < 10),ne _ (by decide : 7 < 10),
      ne _ (by decide : 8 < 10),ne _ (by decide : 9 < 10)]
end A76070

namespace A76070
def start (n : ℕ) := n*(n-1)/2+1
def Works (n : ℕ) := ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m).Perm (block (start n) n)

theorem from_counts (n g q t u v w x y : ℕ)
    (ha : 100 ≤ start n) (qn : q≠0) (fac : n=g*q) (gt : g ∣ 10^t)
    (cop : Nat.Coprime 10 q) (hpairs : q-1 ≤ u+v+w+x+y)
    (hc : ∀ d : Fin 10, needCount t u v w x y d ≤ lowerCount (start n) n d) : Works n := by
  have : NeZero q := ⟨qn⟩
  apply build_counted (start n) n g q t (groups u v w x y) fac gt cop
  · simpa [groups,Nat.add_assoc] using hpairs
  · intro d
    rw [groups_count]
    by_cases hd : d < 10
    · exact (hc ⟨d,hd⟩).trans (lowerCount_valid _ _ _ ha hd)
    · have ng : ([t+u,u,v,v,w,w,x,x,y,y+1]:List ℕ)[d]?=none :=
        List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hd)
      simp [needCount,ng]

theorem large (n : ℕ) (hn : 2000 ≤ n) : Works n := by
  obtain ⟨g,q,t,fac,gt,cop,bound⟩ := split_modulus n (by omega)
  have hq : q≠0 := by intro h;rw [h,mul_zero] at fac;omega
  have hg : 0 < g := by
    by_contra! h
    have e : g=0 := by omega
    rw [e,zero_mul] at fac
    omega
  have qle : q ≤ n := by rw [fac]; exact Nat.le_mul_of_pos_left q hg
  have ha : 100 ≤ start n := by
    unfold start
    have hmul := Nat.mul_le_mul (show 2000 ≤ n from hn) (show 1999 ≤ n-1 by omega)
    omega
  let k := n/5+1
  apply from_counts n g q t k k k k k ha hq fac gt cop
  · have := (paired_capacity _ hn).2; dsimp [k];omega
  · intro d
    have z := zeros_budget n t bound
    have cap := (paired_capacity _ hn).1
    have low : n/10+10*(n/100)+100*(n/1000) ≤ lowerCount (start n) n d := by
      have s := prefix_floor (start n) n d 1 (by decide)
      have h := prefix_floor (start n) n d 10 (by decide)
      have t := prefix_floor (start n) n d 100 (by decide)
      unfold lowerCount
      omega
    apply le_trans _ low
    have hd := d.isLt
    generalize (d:ℕ)=j at *
    interval_cases j <;> simp [needCount,k] <;> omega
end A76070

namespace A76070
structure Certificate where
  g : ℕ
  q : ℕ
  t : ℕ
  u : ℕ
  v : ℕ
  w : ℕ
  x : ℕ
  y : ℕ

def certificate (n : ℕ) : Certificate := Id.run do
  let g := Nat.gcd n (10^12)
  let q := n/g
  let t := ((List.range 13).find? (fun t => 10^t%g==0)).getD 13
  let c := lowerCount (start n) n
  return ⟨g,q,t,min (c 0-t) (c 1),min (c 2) (c 3),min (c 4) (c 5),
          min (c 6) (c 7),min (c 8) (c 9-1)⟩

def checkCert (n : ℕ) : Bool := Id.run do
  let ⟨g,q,t,u,v,w,x,y⟩ := certificate n
  return decide (100 ≤ start n ∧ q≠0 ∧ n=g*q ∧ g ∣ 10^t ∧ Nat.Coprime 10 q ∧
    q-1 ≤ u+v+w+x+y ∧ ∀ d : Fin 10, needCount t u v w x y d ≤ lowerCount (start n) n d)

private theorem works_of_check {n : ℕ} (h : checkCert n=true) : Works n := by
  unfold checkCert at h
  generalize he : certificate n=c at h
  obtain ⟨g,q,t,u,v,w,x,y⟩ := c
  change decide _ = true at h
  obtain ⟨ha,hq,hn,ht,hc,hp,hd⟩ := of_decide_eq_true h
  exact from_counts n g q t u v w x y ha hq hn ht hc hp hd

private def boundedDigits : ℕ → ℕ → List ℕ
  | 0,_ => []
  | f+1,n => if n=0 then [] else n%10 :: boundedDigits f (n/10)

private theorem bounded_eq (f n : ℕ) (h : n < 10^f) : boundedDigits f n = Nat.digits 10 n := by
  induction f generalizing n with
  | zero =>
    have : n=0 := by simpa using h
    simp [this,boundedDigits]
  | succ f ih =>
    by_cases z : n=0
    · simp [z,boundedDigits]
    · rw [boundedDigits,if_neg z,Nat.digits_def' (by decide) (Nat.pos_of_ne_zero z)]
      rw [ih]
      rw [pow_succ] at h
      omega

private def boundedBlock (n : ℕ) := (List.range n).flatMap fun i => boundedDigits 8 (start n+i)
private lemma bounded_block_eq (n : ℕ) (h : start n+n < 10^8) : boundedBlock n=block (start n) n := by
  unfold boundedBlock block
  apply List.flatMap_congr
  intro i hi
  exact bounded_eq _ _ (by have := List.mem_range.mp hi;omega)

private theorem explicit_witness (n m f : ℕ) (h : 0 < m ∧ n ∣ m ∧ m < 10^f ∧ start n+n < 10^8)
    (eq : ∀ d : Fin 10, (boundedDigits f m).count d.val=(boundedBlock n).count d.val) : Works n := by
  refine ⟨m,h.1,h.2.1,?_⟩
  rw [List.perm_iff_count]
  intro d
  by_cases hd : d < 10
  · simpa [bounded_eq f m h.2.2.1,bounded_block_eq n h.2.2.2] using eq ⟨d,hd⟩
  · have l : d ∉ Nat.digits 10 m := fun h => hd (Nat.digits_lt_base (by decide) h)
    have r : d ∉ block (start n) n := by
      intro h
      obtain ⟨_,_,h⟩ := List.mem_flatMap.mp h
      exact hd (Nat.digits_lt_base (by decide) h)
    simp [List.count_eq_zero_of_not_mem l,List.count_eq_zero_of_not_mem r]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_1 : Works 1 :=
  explicit_witness _ 1 1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_2 : Works 2 :=
  explicit_witness _ 32 2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_3 : Works 3 :=
  explicit_witness _ 564 3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_4 : Works 4 :=
  explicit_witness _ 19708 5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_5 : Works 5 :=
  explicit_witness _ 4111211135 10 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_6 : Works 6 :=
  explicit_witness _ 619271821110 12 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_7 : Works 7 :=
  explicit_witness _ 46222222328275 14 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_8 : Works 8 :=
  explicit_witness _ 2333639533034312 16 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_9 : Works 9 :=
  explicit_witness _ 384245434474340391 18 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_10 : Works 10 :=
  explicit_witness _ 51545448657235459540 20 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_11 : Works 11 :=
  explicit_witness _ 6668696545735056615266 22 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_12 : Works 12 :=
  explicit_witness _ 677467778930687771277576 24 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_13 : Works 13 :=
  explicit_witness _ 82858463898888089991778108 26 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_14 : Works 14 :=
  explicit_witness _ 1042506199199400319580129039197910 34 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_16 : Works 16 :=
  explicit_witness _ 148126223911436313112323123155131111271202121312 48 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_17 : Works 17 :=
  explicit_witness _ 114994311221541118130175741315614804313514514144411 51 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_19 : Works 19 :=
  explicit_witness _ 591171118811271777088167148126498311831017881811189787715 57 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_21 : Works 21 :=
  explicit_witness _ 217222298034251226312191251212122823422221022227222212612221322 63 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_23 : Works 23 :=
  explicit_witness _ 272222676222621232257525620276822206982276642547517225375662576692564 69 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_27 : Works 27 :=
  explicit_witness _ 675733664667355635065338360926943373833137333533355736373633752633374132867773355 81 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_29 : Works 29 :=
  explicit_witness _ 194444040802507563716422024114141144404322823444434374221434141354491941314244442234428 87 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_31 : Works 31 :=
  explicit_witness _ 444449847443941444486944352487987477508447979721756864964844087672476148849476690484483489444 93 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_33 : Works 33 :=
  explicit_witness _ 833554665555435307543254015555359436545334555159023555461532445251595587385555445059456553555557555 99 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_39 : Works 39 :=
  explicit_witness _ 749465777767775674777678779758777706774777571660653657075237774887575764774348926145517775577745777679720377766744277 117 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_41 : Works 41 :=
  explicit_witness _ 383888848423084879858428883280835821285281531189988884858070255688843278458389324138828368254683884568758834425456583248868 123 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_43 : Works 43 :=
  explicit_witness _ 999089909498312915613291994994643333351249903392229999971295961049941952999279199993500231297490994994329302111731998049662809499 129 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_49 : Works 49 :=
  explicit_witness _ 1917114211114221198212921918501180916121131114111116281112920911113110252192119972227112101221212161801414217122510911122171217111113100312012018111111282018113199088118217592818201102181689522171 196 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_61 : Works 61 :=
  explicit_witness _ 8185117881888046141618874187410516846118531371117411817088988858618267485180810184381159817514383112886379178881881897718328846881618181811583890841181831966818898848833861618248837518188811118118558167181211173885818284116346587854511513918188 244 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_63 : Works 63 :=
  explicit_witness _ 962106309819902899599119110912151217992564917121997106299117869954078691299739140112241909566819580799690859389002901409605919971211735111827941010991109901092702173181901112916166510199229091612835519206809916275199899077890101681940109179229119010891 252 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_67 : Works 67 :=
  explicit_witness _ 2216225242242422222242622242122772825321224592232525172237226623222243742754222172212522225202662222292222226227922733523926422242261225224022297316225125577626727222623222803222221022222226222222222221275122222222528828422562223423023282532816223027242222436122242229 268 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_73 : Works 73 :=
  explicit_witness _ 2641262322436266260660936729522626735280626628675232668267122682376325659246662028622315857226973266976696926622642662226454622667627262226232986966423656226043226925166166698322683423224646472594660629226926622964272666606266862362058272587276804740567685627226127966526669182329166286242568 292 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_77 : Works 77 :=
  explicit_witness _ 95182459992226592290259224989129422273292247074182999292997943967797090252949294837999596443650992129009229923989209566027639292988299799358594232632522294922467286549232929923922927269920277259725988928822999439992099693300929359686292299212499990239353092929081623872228722292349691229229822993929635292271 308 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_83 : Works 83 :=
  explicit_witness _ 34428148437846438734546333417353848433334834820443413444343433137043138741144642033333744439334352460663494343132334409324054742400441471323583433624149363442433533344553754345433650139343365533323632443334464633624354074733844446331343446331473675335459443324444419144434033944433444043244385333843247544430744410336823342173374867 332 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_87 : Works 87 :=
  explicit_witness _ 770432837384583238803307836837073638389418787300633276885989783273787835573837375032333733805777107433781234730737261778311976093737713483433837533533787762728333133176738835517077338443397738033753590817994787873620387739343337741737983138308998416283325870373397625733873276303731493363712855775877333119588392349363667375748436677677837237887723 348 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_89 : Works 89 :=
  explicit_witness _ 59304699529394599935493693923994304922933148391493893333309139393379035792337809506233399973387333933303399333133919909980820385443838333390445073504914669499914947969325964993992869339983994993933399923391753735933339594293999477396018430834899993559789523069729753569939876997332999926081630233943333893939399321381639033437309343369759603993239932396739 356 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_111 : Works 111 :=
  explicit_witness _ 161611630666111102166960616830546626719661516615262628116165715206266122167114661660181062166698662160949615616266001961137879181111606156356102256263165468336661666111566111676663141161151619961128626112451396117661344142061151315614812392772265901042663761487056116663946210663316661166116164127516916110711212646716962419016662157171210866616266108716211611161168666804643668303018626169014426161166681172668668191839161121651756746979861312 444 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_113 : Works 113 :=
  explicit_witness _ 83166416803660363446364934336636612124263424933334537360636261236592744643636066646366361133064256333644877643533373426369147194328223366664636533756644864434345466633413636646946963635086639684396937616524638975439746169666698716834333333646863983462333653429784533044444353135476608266343666266693562636374576743164466501634066634677860964633262330695453803269666135640766634361060160660414667626333833603409643660665766816636463038666946638333843164 452 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_123 : Works 123 :=
  explicit_witness _ 495578424755555777767696551707645755625637786767584067657622550775550677755567577567457257573777959670355670671655725216817775795285057549578767199817114751453085775576055097301937087067658754577532255655775717556570732987601257565777313751457760545776755074856771753775710796776677597284549915775278777559365711371478755776301257755085471551817701601552565537696272777777377579765856225537750776047724773775235552501704677578325752226757765175255777117575150957439678579016789627456346755857 492 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_137 : Works 137 :=
  explicit_witness _ 34623918309939449330479943498854144924934994993343999312139949346966335329949873443594910414995913313372909990999939439230929839066649341944119499033443290330482343190979234994403095999439993893353167889413295613539399343123946319976604903060339793340196949328339539931513844324943934994982694293999684583799293699232158493399439944223938934324395201729341938298649799930993349899473552793934959349483423274237439436995432325294419949477093499935494449379133499359459339555389533949708599993433363670197339929937498490694192939373394474965439389799 548 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_143 : Works 143 :=
  explicit_witness _ 2280691812213141019101412201528160410632121916611131215222123181037215211152648002118908201000960108022211160311012002200085201419112300812207003221021157005004137204109071241111182211121912126291721003921771081101191012087520221007510230027219127821604201011101970146001011820500080737211276111201101022112577660010000301024600617100805102106109110026911032001709862101806936812321080005082102920414021074221200516850126410782118111078409310162201091290021106501140002110010000011191115241110201802211101042152327406211122021001110013912011472691260181512507125105770258990321101240711246102407155500211121110106102010701078231812118221360100261609158062212097711009100122211112011811120905125210311111491365021215 715 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_147 : Works 147 :=
  explicit_witness _ 807680710718311721871877106122518051352707761181817196740111041880071932368080777777151013180777221117000404948101707850507008101610700568011001019508413776567084307715100104702377880170720500760136080827411608101101085303888781611701309801172707600418716181516172718187811370170068107054888407101702001141100411107897011007001218311188010995000077688537101818809059003108578713710801198108883988701018005614011678818100035002351810481876039014744707043474130581107401017181428795009019872711101830411907283517101160005578890078187268614030118882010060783818104810771705100746178381010016701687510080106005774810887912503111787104161071041882806608012041717701000318710810070160930071103418806970758141892808153405591017115921610811180 735 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem witness_151 : Works 151 :=
  explicit_witness _ 14477111913123116113142171401123061561133153491816147131416131131111114141641345374311144311434141431114111110431311053111651111194315913142183194211711143081318211411349343134531845412011137111728189115196450813634111411641341411136481711332421001842311854111111114489414108061131114157335134526417125733383111101661101395101595141373341111551194318161361514940138109031141331161377111711164117375233111132321428541144181315313140114284411511111174971121144135361424417117346712118462481311143211911983431311164111130111113011126315331111143311461853111466714935645731113424141211933157461649644114119437161116418111111111711117411332481331131124319101414134131611145113111143961404113311311444413113701302111341351114114137171169441345134311111139144501 755 (by decide +kernel) (by decide +kernel)
private def exceptions : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,19,21,23,27,29,31,33,39,41,43,49,61,63,67,73,77,83,87,89,111,113,123,137,143,147,151]
private theorem known_exception (n : ℕ) (h : n ∈ exceptions) : Works n := by
  simp only [exceptions,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7
  · exact witness_8
  · exact witness_9
  · exact witness_10
  · exact witness_11
  · exact witness_12
  · exact witness_13
  · exact witness_14
  · exact witness_16
  · exact witness_17
  · exact witness_19
  · exact witness_21
  · exact witness_23
  · exact witness_27
  · exact witness_29
  · exact witness_31
  · exact witness_33
  · exact witness_39
  · exact witness_41
  · exact witness_43
  · exact witness_49
  · exact witness_61
  · exact witness_63
  · exact witness_67
  · exact witness_73
  · exact witness_77
  · exact witness_83
  · exact witness_87
  · exact witness_89
  · exact witness_111
  · exact witness_113
  · exact witness_123
  · exact witness_137
  · exact witness_143
  · exact witness_147
  · exact witness_151
private def covered (n : ℕ) := checkCert n || exceptions.contains n || n==0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_0 : ∀ j : Fin 50, covered (0+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_1 : ∀ j : Fin 50, covered (50+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_2 : ∀ j : Fin 50, covered (100+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_3 : ∀ j : Fin 50, covered (150+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_4 : ∀ j : Fin 50, covered (200+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_5 : ∀ j : Fin 50, covered (250+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_6 : ∀ j : Fin 50, covered (300+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_7 : ∀ j : Fin 50, covered (350+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_8 : ∀ j : Fin 50, covered (400+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_9 : ∀ j : Fin 50, covered (450+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_10 : ∀ j : Fin 50, covered (500+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_11 : ∀ j : Fin 50, covered (550+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_12 : ∀ j : Fin 50, covered (600+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_13 : ∀ j : Fin 50, covered (650+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_14 : ∀ j : Fin 50, covered (700+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_15 : ∀ j : Fin 50, covered (750+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_16 : ∀ j : Fin 50, covered (800+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_17 : ∀ j : Fin 50, covered (850+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_18 : ∀ j : Fin 50, covered (900+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_19 : ∀ j : Fin 50, covered (950+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_20 : ∀ j : Fin 50, covered (1000+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_21 : ∀ j : Fin 50, covered (1050+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_22 : ∀ j : Fin 50, covered (1100+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_23 : ∀ j : Fin 50, covered (1150+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_24 : ∀ j : Fin 50, covered (1200+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_25 : ∀ j : Fin 50, covered (1250+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_26 : ∀ j : Fin 50, covered (1300+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_27 : ∀ j : Fin 50, covered (1350+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_28 : ∀ j : Fin 50, covered (1400+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_29 : ∀ j : Fin 50, covered (1450+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_30 : ∀ j : Fin 50, covered (1500+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_31 : ∀ j : Fin 50, covered (1550+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_32 : ∀ j : Fin 50, covered (1600+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_33 : ∀ j : Fin 50, covered (1650+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_34 : ∀ j : Fin 50, covered (1700+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_35 : ∀ j : Fin 50, covered (1750+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_36 : ∀ j : Fin 50, covered (1800+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_37 : ∀ j : Fin 50, covered (1850+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_38 : ∀ j : Fin 50, covered (1900+j.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem batch_39 : ∀ j : Fin 50, covered (1950+j.val) = true := by decide +kernel
theorem all_works (n : ℕ) (hn : 0 < n) : Works n := by
  by_cases big : 2000 ≤ n
  · exact large n big
  have hb : n/50 < 40 := by omega
  have cover : covered n=true := by
    let j : Fin 50 := ⟨n%50,by omega⟩
    generalize e : n/50=k at hb
    interval_cases k
    · have h := batch_0 j
      rwa [show 0+j.val=n by dsimp [j];omega] at h
    · have h := batch_1 j
      rwa [show 50+j.val=n by dsimp [j];omega] at h
    · have h := batch_2 j
      rwa [show 100+j.val=n by dsimp [j];omega] at h
    · have h := batch_3 j
      rwa [show 150+j.val=n by dsimp [j];omega] at h
    · have h := batch_4 j
      rwa [show 200+j.val=n by dsimp [j];omega] at h
    · have h := batch_5 j
      rwa [show 250+j.val=n by dsimp [j];omega] at h
    · have h := batch_6 j
      rwa [show 300+j.val=n by dsimp [j];omega] at h
    · have h := batch_7 j
      rwa [show 350+j.val=n by dsimp [j];omega] at h
    · have h := batch_8 j
      rwa [show 400+j.val=n by dsimp [j];omega] at h
    · have h := batch_9 j
      rwa [show 450+j.val=n by dsimp [j];omega] at h
    · have h := batch_10 j
      rwa [show 500+j.val=n by dsimp [j];omega] at h
    · have h := batch_11 j
      rwa [show 550+j.val=n by dsimp [j];omega] at h
    · have h := batch_12 j
      rwa [show 600+j.val=n by dsimp [j];omega] at h
    · have h := batch_13 j
      rwa [show 650+j.val=n by dsimp [j];omega] at h
    · have h := batch_14 j
      rwa [show 700+j.val=n by dsimp [j];omega] at h
    · have h := batch_15 j
      rwa [show 750+j.val=n by dsimp [j];omega] at h
    · have h := batch_16 j
      rwa [show 800+j.val=n by dsimp [j];omega] at h
    · have h := batch_17 j
      rwa [show 850+j.val=n by dsimp [j];omega] at h
    · have h := batch_18 j
      rwa [show 900+j.val=n by dsimp [j];omega] at h
    · have h := batch_19 j
      rwa [show 950+j.val=n by dsimp [j];omega] at h
    · have h := batch_20 j
      rwa [show 1000+j.val=n by dsimp [j];omega] at h
    · have h := batch_21 j
      rwa [show 1050+j.val=n by dsimp [j];omega] at h
    · have h := batch_22 j
      rwa [show 1100+j.val=n by dsimp [j];omega] at h
    · have h := batch_23 j
      rwa [show 1150+j.val=n by dsimp [j];omega] at h
    · have h := batch_24 j
      rwa [show 1200+j.val=n by dsimp [j];omega] at h
    · have h := batch_25 j
      rwa [show 1250+j.val=n by dsimp [j];omega] at h
    · have h := batch_26 j
      rwa [show 1300+j.val=n by dsimp [j];omega] at h
    · have h := batch_27 j
      rwa [show 1350+j.val=n by dsimp [j];omega] at h
    · have h := batch_28 j
      rwa [show 1400+j.val=n by dsimp [j];omega] at h
    · have h := batch_29 j
      rwa [show 1450+j.val=n by dsimp [j];omega] at h
    · have h := batch_30 j
      rwa [show 1500+j.val=n by dsimp [j];omega] at h
    · have h := batch_31 j
      rwa [show 1550+j.val=n by dsimp [j];omega] at h
    · have h := batch_32 j
      rwa [show 1600+j.val=n by dsimp [j];omega] at h
    · have h := batch_33 j
      rwa [show 1650+j.val=n by dsimp [j];omega] at h
    · have h := batch_34 j
      rwa [show 1700+j.val=n by dsimp [j];omega] at h
    · have h := batch_35 j
      rwa [show 1750+j.val=n by dsimp [j];omega] at h
    · have h := batch_36 j
      rwa [show 1800+j.val=n by dsimp [j];omega] at h
    · have h := batch_37 j
      rwa [show 1850+j.val=n by dsimp [j];omega] at h
    · have h := batch_38 j
      rwa [show 1900+j.val=n by dsimp [j];omega] at h
    · have h := batch_39 j
      rwa [show 1950+j.val=n by dsimp [j];omega] at h
  simp only [covered,Bool.or_eq_true,List.contains_iff_mem,beq_iff_eq] at cover
  rcases cover with (h|h)|h
  · exact works_of_check h
  · exact known_exception _ h
  · omega
end A76070

namespace A76070
private lemma bag_sum (a n : ℕ) : (block a n : Multiset ℕ) =
    (Finset.range n).sum (fun i => (Nat.digits 10 (a+i) : Multiset ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ,←ih]
    simp [block,List.range_succ,Multiset.coe_add]

private theorem exact_block (n : ℕ) (hn : 0 < n) :
    (block (start n) n : Multiset ℕ) = OMA.S_oeis_a076070.nextDigits n := by
  unfold OMA.S_oeis_a076070.nextDigits
  rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,bag_sum]
  congr 2
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_sub_one]
  have e : (m+1)*(m+1+1)=(m+1)*m+2*(m+1) := by ring
  change _ = ((m+1)*(m+1+1)/2+1)-((m+1)*m/2+1)
  rw [e]
  omega
end A76070

theorem OMA.solution : type_of% @OMA.S_oeis_a076070.main := by
  intro n hn
  obtain ⟨m,hm,hd,hbag⟩ := A76070.all_works n hn
  have hw : ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ)=OMA.S_oeis_a076070.nextDigits n :=
    ⟨m,hm,hd,(Multiset.coe_eq_coe.mpr hbag).trans (A76070.exact_block n hn)⟩
  exact (Nat.sInf_mem hw).1.ne'
