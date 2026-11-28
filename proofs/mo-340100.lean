import OMAStatements.S_mo_340100
namespace OMA.S_mo_340100
open Finset

private def adj {n : ℕ} (p : Equiv.Perm (Pos n)) : Board n := fun i j => decide (p i=j)

private lemma gap_set {n : ℕ} (p : Equiv.Perm (Pos n)) (k : ℕ) :
    gaps (adj p) k = initial n k \ (initial n k).image p := by
  ext j
  simp [gaps,adj,Finset.mem_image]

private lemma inverse_gaps {n : ℕ} (p : Equiv.Perm (Pos n)) (k : ℕ) :
    gaps (adj p.symm) k = (initial n k).filter (fun j => p j∉initial n k) := by
  rw [gap_set]
  ext j
  simp [Equiv.symm_apply_eq]

private lemma same_gap_count {n : ℕ} (p : Equiv.Perm (Pos n)) (k : ℕ) :
    (gaps (adj p) k).card=(gaps (adj p.symm) k).card := by
  rw [gap_set,inverse_gaps]
  let S:=initial n k
  change (S \ S.image p).card = (S.filter (fun j => p j∉S)).card
  rw [Finset.card_sdiff_comm (show S.card=(S.image p).card from (card_image_of_injective _ p.injective).symm)]
  have he : S.image p \ S = (S.filter (fun j => p j∉S)).image p := by
    ext j
    simp [Finset.mem_image,Equiv.apply_eq_iff_eq_symm_apply]
  rw [he,card_image_of_injective _ p.injective]

private def labelStep {n : ℕ} (w : Equiv.Perm (Pos n)) : Equiv.Perm (Pos n) :=
  (w.symm.trans (Equiv.addRight 1)).trans w

private lemma step_apply {n : ℕ} (w : Equiv.Perm (Pos n)) (j : Pos n) :
    labelStep w (w j) = w (j+1) := by simp [labelStep]

private lemma width_bound {n r : ℕ} (w : Equiv.Perm (Pos n)) (hw : interleaving w≤r) (k : ℕ) (hk : k≤n+1) :
    (gaps (adj (labelStep w)) k).card≤r ∧ (gaps (adj (labelStep w).symm) k).card≤r := by
  let S:=initial n k
  let T:=univ.filter (fun j => w j∈S)
  have h0 : arc (0:Pos n) k = S := by simp [arc,S]
  have hc : runs T ≤ r := by
    apply le_trans _ hw
    apply le_trans _ (le_sup (s:=univ) (f:=fun a : Pos n => (range (n+2)).sup fun l =>
      runs (univ.filter (fun j => w j ∈ arc a l))) (mem_univ 0))
    simpa [h0,T] using (le_sup (f:=fun l => runs (univ.filter (fun j => w j∈arc (0:Pos n) l))) (mem_range.mpr (by omega : k<n+2)))
  suffices h : (gaps (adj (labelStep w).symm) k).card≤r by
    exact ⟨(same_gap_count (labelStep w) k).le.trans h,h⟩
  rw [inverse_gaps]
  apply le_trans _ hc
  apply Finset.card_le_card_of_injOn w.symm _ w.symm.injective.injOn
  intro i hi
  have hi' := mem_filter.mp hi
  apply mem_filter.mpr
  constructor
  · simp [T,S,hi'.1]
  · right
    intro he
    have ha : w (w.symm i+1)∈S := (mem_filter.mp he).2
    apply hi'.2
    simpa [labelStep] using ha

end OMA.S_mo_340100
namespace OMA.S_mo_340100
open Finset Fin.NatCast

private def key {n : ℕ} (p : Equiv.Perm (Pos n)) (i : Pos n) : ℕ :=
  if p i=i then 0 else if i < p i then 1 else (gaps (adj p) i.val).sort.idxOf (p i)+2

private lemma available {n : ℕ} (p : Equiv.Perm (Pos n)) (i : Pos n) (h : p i < i) :
    p i ∈ gaps (adj p) i.val := by
  simp [gaps,initial,adj,p.injective.eq_iff]
  grind [Fin.lt_def]

private lemma key_lt {n r : ℕ} (p : Equiv.Perm (Pos n)) (i : Pos n)
    (h : (gaps (adj p) i.val).card ≤ r) : key p i < r+2 := by
  unfold key
  split_ifs with he hl
  · omega
  · omega
  · have hm := available p i (lt_of_le_of_ne (le_of_not_gt hl) he)
    have hm' : p i ∈ (gaps (adj p) i.val).sort := by simpa using hm
    have hh := List.idxOf_lt_length_iff.mpr hm'
    rw [Finset.length_sort] at hh
    omega

private lemma key_zero {n : ℕ} (p : Equiv.Perm (Pos n)) (i : Pos n) :
    (key p i = 0) ↔ p i=i := by unfold key; split_ifs <;> simp_all

private lemma match_key {n : ℕ} (p : Equiv.Perm (Pos n)) (i j : Pos n) (hji : j < i) :
    rankMatch (gaps (adj p) i.val) j (key p i)=adj p i j := by
  let S:=gaps (adj p) i.val
  change decide (j∈S ∧ key p i=S.sort.idxOf j+2) = decide (p i=j)
  congr 1
  apply propext
  by_cases h : p i < i
  · have hm : p i∈S := available p i h
    rw [key,if_neg h.ne,if_neg (not_lt.mpr h.le)]
    change (j∈S ∧ S.sort.idxOf (p i)+2=S.sort.idxOf j+2) ↔ _
    rw [Nat.add_right_cancel_iff, List.idxOf_inj ((Finset.mem_sort _).mpr hm)]
    exact ⟨And.right,fun e => ⟨e ▸ hm,e⟩⟩
  · have ne : p i ≠ j := fun e => h (e ▸ hji)
    have hl : key p i ≤ 1 := by
      by_cases he : p i=i
      · simp [key,he]
      · have hh : i < p i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm he)
        simp [key,he,hh]
    have hn : key p i ≠ S.sort.idxOf j+2 := by omega
    simp [ne,hn]

private lemma gaps_congr {n : ℕ} {B C : Board n} {k : ℕ}
    (h : ∀ i j : Pos n, i.val < k → j.val < k → B i j=C i j) : gaps B k = gaps C k := by
  ext j
  simp only [gaps,mem_filter,initial,mem_univ,true_and]
  constructor <;> rintro ⟨hj,ht⟩ <;> refine ⟨hj,fun i hi => ?_⟩
  · rw [← h i j hi hj]; exact ht i hi
  · rw [h i j hi hj]; exact ht i hi

private lemma transpose_adj {n : ℕ} (p : Equiv.Perm (Pos n)) (i j : Pos n) :
    adj p j i = adj p.symm i j := by
  have he : (p j=i) ↔ (p.symm i=j) := by rw [p.symm_apply_eq]; exact eq_comm
  simp only [adj,he]

private lemma exposure {n r : ℕ} (p : Equiv.Perm (Pos n)) (c : Code n r)
    (hc : ∀ i, (c i).1.val=key p i) (hc' : ∀ i, (c i).2.val=key p.symm i) :
    expose c (n+1) = adj p := by
  have square (k : ℕ) : ∀ i j : Pos n, i.val < k → j.val < k → expose c k i j=adj p i j := by
    induction k with
    | zero => intro i j hi; omega
    | succ k ih =>
      intro i j hi hj
      have hA := gaps_congr ih
      have hB : gaps (fun x y => expose c k y x) k=gaps (adj p.symm) k :=
        gaps_congr (fun x y hx hy => (ih y x hy hx).trans (transpose_adj p x y))
      unfold expose
      by_cases hi' : i.val=k
      · by_cases hj' : j.val=k
        · have hij := Fin.ext (hi'.trans hj'.symm)
          subst j
          simp [hi',hc,key_zero,adj]
        · have hlt : j.val < i.val := by omega
          simp only [hi',hj',false_and,and_false,if_false,show j.val < k from by omega,
            and_self,if_true,true_and,hA,hc]
          simpa [hi'] using match_key p i j hlt
      · by_cases hj' : j.val=k
        · have hlt : i.val < j.val := by omega
          simp only [hi',hj',false_and,and_false,if_false,show i.val < k from by omega,
            and_self,if_true,true_and,hB,hc']
          rw [transpose_adj p j i]
          simpa [hj'] using match_key p.symm j i hlt
        · simpa [hi',hj'] using ih i j (by omega) (by omega)
  funext i j
  exact square _ i j i.isLt j.isLt

private lemma nextOn_adj {n : ℕ} (p : Equiv.Perm (Pos n)) : nextOn (adj p) = p := by
  funext i
  have hs : univ.filter (fun j => adj p i j=true) = {p i} := by ext j; simp [adj,eq_comm]
  rw [nextOn,hs]
  rfl

private lemma recoverable {n r : ℕ} (v : Word n) (hv : rooted v) (hr : interleaving v≤r) :
    ∃ c : Code n r, recover c=v := by
  classical
  let w := Equiv.ofBijective v hv.2
  let p := labelStep w
  have lim (i : Pos n) := width_bound w hr i.val i.isLt.le
  let c : Code n r := fun i => (⟨key p i,key_lt p i (lim i).1⟩,⟨key p.symm i,key_lt p.symm i (lim i).2⟩)
  refine ⟨c,?_⟩
  have hd := exposure p c (fun _ => rfl) (fun _ => rfl)
  have iter (k : ℕ) : p^[k] (w 0)=w (k:Pos n) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply',ih,step_apply,Nat.cast_succ]
  funext j
  simp only [recover,hd,nextOn_adj]
  have e:=iter j.val
  rw [show w 0=0 from hv.1] at e
  simpa [w] using e

end OMA.S_mo_340100
namespace OMA.S_mo_340100
open Finset Fin.NatCast

private def desc {n : ℕ} (w : Word n) : ℕ :=
  (univ.filter (fun i : Pos n => w (i+1) < w i)).card

private lemma winding {n : ℕ} (w : Word n) :
    (∑ i : Pos n, ((w (i+1)-w i).val : ℤ)) = (n+1:ℕ)*(desc w : ℤ) := by
  simp_rw [Fin.intCast_val_sub_eq_sub_add_ite]
  rw [sum_add_distrib,sum_sub_distrib]
  have e := Equiv.sum_comp (Equiv.addRight (1:Pos n)) (fun i => ((w i).val:ℤ))
  change (∑ i : Pos n, ((w (i+1)).val:ℤ)) = ∑ i : Pos n, ((w i).val:ℤ) at e
  rw [e,sub_self,zero_add]
  have flip (i : Pos n) : ((if w i ≤ w (i+1) then (0:ℕ) else n+1 : ℕ) : ℤ) = (if w (i+1) < w i then ((n+1:ℕ):ℤ) else (0:ℤ)) := by
    by_cases h : w (i+1) < w i
    · simp [h,not_le.mpr h]
    · simp [h,le_of_not_gt h]
  simp_rw [flip]
  rw [← sum_filter]
  simp [desc,mul_comm]

private lemma rotated_desc {n : ℕ} (w : Word n) (a : Pos n) : desc (fun i => w i-a)=desc w := by
  have h:= (winding (fun i => w i-a)).symm.trans (by simpa only [sub_sub_sub_cancel_right] using winding w)
  exact_mod_cast (mul_left_cancel₀ (by positivity : ((n+1:ℕ):ℤ)≠0) h)

private lemma runs_le_enter {n : ℕ} (T : Finset (Pos n)) :
    runs T ≤ (univ.filter (fun i : Pos n => i∉T ∧ i+1∈T)).card+1 := by
  let s : Equiv.Perm (Pos n) := Equiv.addRight 1
  let O:=T.filter (fun i : Pos n => i+1∉T)
  have he : (O.image s).card = O.card := card_image_of_injective _ s.injective
  have ha : O.image s=(T.image s) \ T := by
    ext j; simp [O,s]
  have hb : (univ.filter (fun i : Pos n => i∉T ∧ i+1∈T)).image s = T \ T.image s := by
    ext j
    simp only [mem_image,mem_filter,mem_univ,true_and,mem_sdiff,not_exists]
    change (∃ i, (i∉ T ∧ s i∈T) ∧ s i=j) ↔ j∈T ∧ _
    constructor
    · rintro ⟨i,⟨hi,hj⟩,rfl⟩
      refine ⟨hj,fun z hz => hi ?_⟩
      simpa only [s.injective hz.2] using hz.1
    · rintro ⟨hj,hj'⟩
      refine ⟨s.symm j,⟨?_,by simpa using hj⟩,by simp⟩
      intro hm
      exact hj' _ ⟨hm,by simp⟩
  have eq : O.card=(univ.filter (fun i : Pos n => i∉T ∧ i+1∈T)).card := by
    rw [←he,ha,card_sdiff_comm (card_image_of_injective _ s.injective),←hb,card_image_of_injective _ s.injective]
  rw [←eq]
  have incl : T.filter (fun i => i.val=n ∨ i+1∉T) ⊆ insert (Fin.last n) O := by
    intro i hi
    rcases mem_filter.mp hi with ⟨ht,hl|hr⟩
    · exact mem_insert.mpr (Or.inl (Fin.ext hl))
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨ht,hr⟩))
  exact (card_le_card incl).trans (card_insert_le _ _)

private lemma interleaving_le_desc {n : ℕ} (w : Word n) : interleaving w ≤ desc w+1 := by
  apply Finset.sup_le
  intro a _
  apply Finset.sup_le
  intro k _
  let T:=univ.filter (fun i => w i∈arc a k)
  have memT (i : Pos n) : i∈T ↔ (w i-a).val < k := by
    simp only [T,mem_filter,mem_univ,true_and,arc,mem_image,initial]
    constructor
    · rintro ⟨j,hj,he⟩
      rw [←he,add_sub_cancel_left]
      exact hj
    · intro hi
      exact ⟨w i-a,hi,add_sub_cancel _ _⟩
  apply (runs_le_enter T).trans
  rw [←rotated_desc w a]
  apply Nat.add_le_add_right
  apply card_le_card
  intro i hi
  have he := (mem_filter.mp hi).2
  have hl : (w (i+1)-a).val < k := (memT _).mp he.2
  have hh : k ≤ (w i-a).val := le_of_not_gt (fun h => he.1 ((memT _).mpr h))
  exact mem_filter.mpr ⟨mem_univ _,show (w (i+1)-a).val < (w i-a).val from hl.trans_le hh⟩

end OMA.S_mo_340100
namespace OMA.S_mo_340100
open Finset Fin.NatCast

private def shuffle {m : ℕ} (u : Fin m → Fin 2) (j : Pos (2*m)) : Pos (2*m) :=
  if h0 : j.val=0 then 0
  else if h : j.val ≤ m then
    let i : Fin m := ⟨j.val-1,by omega⟩
    ⟨2*i.val+1+(u i).val,by have := (u i).isLt; omega⟩
  else
    let i : Fin m := ⟨j.val-m-1,by omega⟩
    ⟨2*i.val+2-(u i).val,by have := (u i).isLt; omega⟩

private lemma shuffle_positive {m : ℕ} (u : Fin m→Fin 2) (j : Pos (2*m)) (h : j.val≠0) :
    0 < (shuffle u j).val := by
  simp only [shuffle,dif_neg h]
  split <;> dsimp only
  · omega
  · have hh := (u ⟨j.val-m-1,by omega⟩).isLt
    omega

private lemma shuffle_rooted {m : ℕ} (u : Fin m→Fin 2) : rooted (shuffle u) := by
  refine ⟨by simp [shuffle],Finite.injective_iff_bijective.mp ?_⟩
  intro i j hij
  by_cases hi : i.val=0
  · by_contra! hne
    have hj : j.val≠0 := fun hh => hne (Fin.ext (hi.trans hh.symm))
    have hp := shuffle_positive u j hj
    have he : shuffle u i=0 := by simp [shuffle,hi]
    rw [←hij,he] at hp
    simp at hp
  by_cases hj : j.val=0
  · have hp:=shuffle_positive u i hi
    have he : shuffle u j=0 := by simp [shuffle,hj]
    rw [hij,he] at hp
    simp at hp
  apply Fin.ext
  have he := congrArg Fin.val hij
  simp only [shuffle,dif_neg hi,dif_neg hj] at he
  split at he <;> split at he <;> dsimp only at he
  · rename_i hi' hj'
    have a := (u ⟨i.val-1,by omega⟩).isLt
    have b := (u ⟨j.val-1,by omega⟩).isLt
    omega
  · rename_i hi' hj'
    let a : Fin m:=⟨i.val-1,by omega⟩
    let b : Fin m:=⟨j.val-m-1,by omega⟩
    have ee : 2*a.val+1+(u a).val=2*b.val+2-(u b).val := he
    have ha:=(u a).isLt
    have hb:=(u b).isLt
    have hab : a=b := Fin.ext (by omega)
    rw [hab] at ee
    omega
  · rename_i hi' hj'
    let a : Fin m:=⟨i.val-m-1,by omega⟩
    let b : Fin m:=⟨j.val-1,by omega⟩
    have ee : 2*a.val+2-(u a).val=2*b.val+1+(u b).val := he
    have ha:=(u a).isLt
    have hb:=(u b).isLt
    have hab : a=b := Fin.ext (by omega)
    rw [hab] at ee
    omega
  · rename_i hi' hj'
    have a := (u ⟨i.val-m-1,by omega⟩).isLt
    have b := (u ⟨j.val-m-1,by omega⟩).isLt
    omega

private lemma shuffle_faithful {m : ℕ} : Function.Injective (shuffle (m:=m)) := by
  intro u v h
  funext i
  let j : Pos (2*m):=⟨i.val+1,by omega⟩
  have e:=congrArg Fin.val (congrFun h j)
  simp [shuffle,j,show i.val+1 ≤ m from i.isLt] at e
  exact Fin.ext e

private lemma shuffle_small {m : ℕ} (u : Fin m→Fin 2) : desc (shuffle u) ≤ 2 := by
  let a : Pos (2*m) := ⟨m,by omega⟩
  let b := Fin.last (2*m)
  have incl : univ.filter (fun i : Pos (2*m) => shuffle u (i+1) < shuffle u i) ⊆ {a,b} := by
    intro i hi
    have lt := (mem_filter.mp hi).2
    by_contra! bad
    have hh : i.val≠m ∧ i.val≠2*m := by
      simpa [a,b,Fin.ext_iff] using bad
    have inc : (i+1).val=i.val+1 := by rw [Fin.val_add_one]; split <;> simp_all [Fin.ext_iff]
    have hn : (i+1).val≠0 := by omega
    by_cases hz : i.val=0
    · have he : shuffle u i=0 := by simp [shuffle,hz]
      rw [he] at lt; exact (Fin.not_lt_zero _ lt)
    have e : (shuffle u (i+1)).val < (shuffle u i).val := lt
    simp only [shuffle,dif_neg hn,dif_neg hz] at e
    split at e <;> split at e <;> dsimp only at e
    · rename_i h₁ h₂
      have hb:=(u ⟨i.val-1,by omega⟩).isLt
      omega
    · omega
    · omega
    · rename_i h₁ h₂
      have hb:=(u ⟨(i+1).val-m-1,by omega⟩).isLt
      omega
  exact (card_le_card incl).trans (card_insert_le _ _ |>.trans (by simp))

private lemma exponential_family (m : ℕ) : 2^m ≤ (eligible (2*m) 3).card := by
  have incl : univ.image (shuffle (m:=m)) ⊆ eligible (2*m) 3 := by
    intro w hw
    obtain ⟨u,_,rfl⟩:=mem_image.mp hw
    simp only [eligible,mem_filter,mem_univ,true_and]
    exact ⟨shuffle_rooted u,(interleaving_le_desc _).trans (Nat.add_le_add_right (shuffle_small u) 1)⟩
  have h:=card_le_card incl
  rw [card_image_of_injective _ shuffle_faithful] at h
  simpa using h

end OMA.S_mo_340100
namespace OMA.S_mo_340100
open Finset

private lemma enumerate_all (n r : ℕ) : eligible n r = candidates n r := by
  ext w
  simp only [eligible,candidates,mem_filter,mem_univ,true_and,mem_image]
  constructor
  · intro h
    obtain ⟨c,hc⟩:=recoverable w h.1 h.2
    exact ⟨⟨c,hc⟩,h⟩
  · exact And.right

private lemma upper_count (n r : ℕ) : (eligible n r).card ≤ (r+2)^(2*(n+1)) := by
  rw [enumerate_all,candidates]
  apply (card_filter_le _ _).trans
  apply card_image_le.trans
  simp [Code,Pos,Fintype.card_prod,←sq,pow_mul]

private lemma exact_count (n r : ℕ) :
    exactCount n (r+1)=(eligible n (r+1)).card-(eligible n r).card := by
  have e : univ.filter (fun w : Word n => rooted w ∧ interleaving w=r+1) =
      eligible n (r+1) \ eligible n r := by
    ext w
    simp only [eligible,mem_filter,mem_univ,true_and,mem_sdiff]
    grind
  have h : eligible n r ⊆ eligible n (r+1) := by
    intro w hw
    simp only [eligible,mem_filter,mem_univ,true_and] at hw ⊢
    exact ⟨hw.1,hw.2.trans (Nat.le_succ _)⟩
  rw [exactCount,e,card_sdiff_of_subset h]

private lemma rarity (r : ℕ) (C : ℝ) (hC : 0≤C) : Filter.Tendsto
    (fun n : ℕ => C^n*((eligible n r).card:ℝ)/(n.factorial:ℝ)) Filter.atTop (nhds 0) := by
  let D : ℝ := ((r:ℝ)+2)^2
  have ht := (FloorSemiring.tendsto_pow_div_factorial_atTop (C*D)).const_mul D
  rw [mul_zero] at ht
  apply squeeze_zero (fun n => by positivity) _ ht
  intro n
  have h : ((eligible n r).card:ℝ) ≤ D^(n+1) := by
    have q : ((eligible n r).card:ℝ) ≤ ((r:ℝ)+2)^(2*(n+1)) := by exact_mod_cast upper_count n r
    simpa [D,pow_mul] using q
  calc C^n*((eligible n r).card:ℝ)/(n.factorial:ℝ) ≤ C^n*D^(n+1)/(n.factorial:ℝ) := by gcongr
       _ = _ := by rw [pow_succ,mul_pow]; ring

end OMA.S_mo_340100

theorem OMA.solution : type_of% @OMA.S_mo_340100.main :=
  ⟨fun n r => ⟨OMA.S_mo_340100.enumerate_all n r,OMA.S_mo_340100.upper_count n r,OMA.S_mo_340100.exact_count n r⟩,OMA.S_mo_340100.rarity,OMA.S_mo_340100.exponential_family⟩
