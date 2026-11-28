import OMAStatements.S_oeis_a182220
import Mathlib.Data.Nat.Size
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
Each out-neighborhood is a subset of the non-sources, so injectivity gives
a powerset bound. The matching graph uses the binary digits of each vertex
label for its out-neighborhood. The tree and arithmetic descriptions
follow from the same bounds between successive powers of two.
-/

namespace OMA.S_oeis_a182220

open Finset

private def used {N : ℕ} (D : Digraph N) : Finset (Fin N) := univ.biUnion D

private theorem card_difference {α : Type*} [DecidableEq α] {s t : Finset α} (h : s⊆t) :
    (t \ s).card=t.card-s.card := by
  first
  | exact Finset.card_sdiff h
  | rw [Finset.card_sdiff,Finset.inter_eq_left.mpr h]

private theorem ncard_finset {α : Type*} (s : Finset α) : (s : Set α).ncard=s.card := by simp

private theorem source_formula {N : ℕ} (D : Digraph N) :
    sourceCount D=N-(used D).card := by
  unfold sourceCount used
  rw [card_difference (subset_univ _),card_univ,Fintype.card_fin]

private theorem powerset_bound {N : ℕ} (D : Digraph N) (hi : Function.Injective D) :
    N ≤ 2^(used D).card := by
  let e (x : Fin N) : (used D).powerset :=
    ⟨D x, mem_powerset.mpr (fun y hy => mem_biUnion.mpr ⟨x,mem_univ _,hy⟩)⟩
  have he : Function.Injective e := by
    intro x y h
    exact hi (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fin,Fintype.card_coe,card_powerset] using h

private def bits {N : ℕ} (t : ℕ) (x : Fin N) : Finset (Fin N) :=
  univ.filter fun y => y.val<t ∧ x.val.testBit y.val = true

private theorem bits_injective {N t : ℕ} (hN : N≤2^t) (ht : t≤N) :
    Function.Injective (bits (N := N) t) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<t
  · let j : Fin N := ⟨i,by omega⟩
    have he : j∈bits t x ↔ j∈bits t y := by rw [h]
    change _ ↔ _ at he
    simp only [bits,mem_filter,mem_univ,true_and] at he
    change (i<t ∧ x.val.testBit i = true) ↔ (i<t ∧ y.val.testBit i=true) at he
    simp only [hi,true_and] at he
    cases hx : x.val.testBit i <;> cases hy : y.val.testBit i <;> simp_all
  · have hh : 2^t≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le (hN.trans hh)),
      Nat.testBit_lt_two_pow (y.isLt.trans_le (hN.trans hh))]

private theorem bits_acyclic {N : ℕ} (t : ℕ) : acyclic (bits (N := N) t) := by
  have hstep {x y : Fin N} (h : y∈bits t x) : y.val<x.val := by
    have hb : x.val.testBit y.val=true := (mem_filter.mp h).2.2
    have hp : 2^y.val≤x.val := by
      by_contra hh
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_not_ge hh)] at hb
      contradiction
    exact (show y.val < 2^y.val from Nat.lt_two_pow_self).trans_le hp
  have hpath {x y : Fin N} (h : Relation.TransGen (fun u v => v∈bits t u) x y) : y.val<x.val := by
    induction h with
    | single h => exact hstep h
    | tail _ h ih => exact (hstep h).trans ih
  intro v hv
  exact (Nat.lt_irrefl _) (hpath hv)

private theorem bits_used {N t : ℕ} (hpow : ∀ i<t, 2^i<N) :
    used (bits (N := N) t) = univ.filter fun x : Fin N => x.val<t := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,_,hy⟩ := mem_biUnion.mp hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2.1⟩
  · intro hx
    have hi := (mem_filter.mp hx).2
    let y : Fin N := ⟨2^x.val,hpow _ hi⟩
    apply mem_biUnion.mpr
    refine ⟨y,mem_univ _,mem_filter.mpr ⟨mem_univ _,hi,?_⟩⟩
    exact Nat.testBit_two_pow_self

private theorem initial_count {N t : ℕ} (ht : t≤N) :
    (univ.filter fun x : Fin N => x.val<t).card=t := by
  let e : Fin t ↪ Fin N := ⟨fun x => ⟨x.val,x.isLt.trans_le ht⟩,
    by intro x y h; exact Fin.ext (congrArg (fun z : Fin N => z.val) h)⟩
  have he : (univ.filter fun x : Fin N => x.val<t)=univ.map e := by
    ext x
    rw [mem_filter,mem_map]
    constructor
    · rintro ⟨_,hx⟩
      exact ⟨⟨x.val,hx⟩,mem_univ _,Fin.ext rfl⟩
    · rintro ⟨y,_,rfl⟩
      exact ⟨mem_univ _,y.isLt⟩
  rw [he,card_map,card_univ,Fintype.card_fin]

private theorem best_sources (n : ℕ) :
    IsGreatest (attainable (n+1)) (if n=0 then 1 else n-n.log2) := by
  let t := if n=0 then 0 else n.log2+1
  have ht : t≤n+1 := by
    by_cases h : n=0
    · simp [t,h]
    · simp only [t,h,if_false]
      exact Nat.succ_le_succ (Nat.log2_le_self n)
  have hN : n+1≤2^t := by
    by_cases h : n=0
    · simp [t,h]
    · simp only [t,h,if_false]
      exact Nat.lt_log2_self
  have hpow (i : ℕ) (hi : i<t) : 2^i<n+1 := by
    by_cases h : n=0
    · simp [t,h] at hi
    · have hl : i≤n.log2 := by simp only [t,h,if_false] at hi; omega
      exact (Nat.pow_le_pow_right (by decide) hl).trans_lt (Nat.lt_succ_of_le (Nat.log2_self_le h))
  have hf : (if n=0 then 1 else n-n.log2)=n+1-t := by
    by_cases h : n=0 <;> simp [t,h]
  rw [hf]
  constructor
  · refine ⟨bits t,bits_injective hN ht,bits_acyclic t,?_⟩
    rw [source_formula,bits_used hpow,initial_count ht]
  · rintro k ⟨D,hD,_,rfl⟩
    rw [source_formula]
    apply Nat.sub_le_sub_left
    by_cases h : n=0
    · simp [t,h]
    · have hl : n.log2<(used D).card := (Nat.log2_lt h).2 (powerset_bound D hD)
      simpa [t,h] using Nat.succ_le_of_lt hl


private theorem tree_size_bounds (t : BinaryTree Unit) :
    t.height≤t.numNodes ∧ t.numNodes+1≤2^t.height := by
  induction t with
  | nil => decide
  | node a l r hl hr =>
    change l.height≤l.numNodes ∧ l.numNodes+1≤2^l.height at hl
    change r.height≤r.numNodes ∧ r.numNodes+1≤2^r.height at hr
    change max l.height r.height+1≤l.numNodes+r.numNodes+1 ∧
      l.numNodes+r.numNodes+1+1≤2^(max l.height r.height+1)
    have hL := hl.2.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left l.height r.height))
    have hR := hr.2.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right l.height r.height))
    rw [pow_succ]
    omega

private theorem split_nodes (h n : ℕ) (hc : n+2≤2^(h+1)) :
    ∃ l r : ℕ, l+r=n ∧ l+1≤2^h ∧ r+1≤2^h ∧ (h≤n → h≤l) := by
  let p := 2^h-1
  let l := min n p
  have hpos : 0 < 2^h := Nat.two_pow_pos h
  have hh : h<2^h := Nat.lt_two_pow_self
  rw [pow_succ] at hc
  refine ⟨l,n-l,?_⟩
  dsimp [l,p]
  omega

private theorem tree_at_most (h n : ℕ) (hc : n+1≤2^h) :
    ∃ t : BinaryTree Unit, t.numNodes=n ∧ t.height≤h := by
  induction h generalizing n with
  | zero =>
    have hn : n=0 := by simp only [pow_zero] at hc; omega
    exact ⟨.nil,by rw [hn]; rfl,by decide⟩
  | succ h ih =>
    cases n with
    | zero => exact ⟨.nil,rfl,by change 0 ≤ h+1; omega⟩
    | succ n =>
      obtain ⟨l,r,hsize,hl,hr,_⟩ := split_nodes h n hc
      obtain ⟨tl,hln,hlt⟩ := ih l hl
      obtain ⟨tr,hrn,hrt⟩ := ih r hr
      refine ⟨.node () tl tr, ?_, ?_⟩
      · change tl.numNodes+tr.numNodes+1=n+1
        omega
      · change max tl.height tr.height+1≤h+1
        omega

private theorem tree_exact (h n : ℕ) (hh : h≤n) (hc : n+1≤2^h) :
    ∃ t : BinaryTree Unit, t.numNodes=n ∧ t.height=h := by
  induction h generalizing n with
  | zero =>
    have hn : n=0 := by simp only [pow_zero] at hc; omega
    exact ⟨.nil,by rw [hn]; rfl,rfl⟩
  | succ h ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨l,r,hsize,hl,hr,hChoose⟩ := split_nodes h n hc
      obtain ⟨tl,hln,hlt⟩ := ih l (hChoose (by omega)) hl
      obtain ⟨tr,hrn,hrt⟩ := tree_at_most h r hr
      refine ⟨.node () tl tr, ?_, ?_⟩
      · change tl.numNodes+tr.numNodes+1=n+1
        omega
      · change max tl.height tr.height+1=h+1
        omega

private theorem tree_heights (n : ℕ) (hn : 0 < n) :
    treeHeights n = Set.Icc n.log2 (n-1) := by
  ext h
  constructor
  · rintro ⟨t,hN,hH⟩
    have hb := tree_size_bounds t
    rw [hN,hH] at hb
    exact ⟨by have hl := (Nat.log2_lt (by omega : n≠0)).2 (by omega : n<2^(h+1)); omega,
      by omega⟩
  · rintro ⟨hl,hu⟩
    apply tree_exact (h+1) n (by omega)
    have hp : 2^(n.log2+1)≤2^(h+1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_log2_self.trans_le hp

private theorem height_count (n : ℕ) (hn : 0 < n) :
    (treeHeights n).ncard = n-n.log2 := by
  rw [tree_heights n hn]
  have h : Set.Icc n.log2 (n-1) = (Finset.Icc n.log2 (n-1) : Set ℕ) := by
    ext k
    simp
  rw [h,ncard_finset,Nat.card_Icc]
  omega

private theorem nonpower_count (n : ℕ) :
    {k : ℕ | k≤n ∧ ¬∃ e : ℕ, k=2^e}.ncard = if n=0 then 1 else n-n.log2 := by
  by_cases h : n=0
  · subst n
    have hset : {k : ℕ | k≤0 ∧ ¬∃ e : ℕ, k=2^e} = {0} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        omega
      · rintro rfl
        refine ⟨le_rfl,?_⟩
        rintro ⟨e,he⟩
        exact (Nat.ne_of_gt (Nat.two_pow_pos e)) he.symm
    rw [hset]
    simp
  · rw [if_neg h]
    let P : Finset ℕ := (range (n.log2+1)).image (fun e => 2^e)
    have hP (k : ℕ) : k∈P ↔ ∃ e : ℕ, e≤n.log2 ∧ k=2^e := by
      unfold P
      rw [mem_image]
      constructor
      · rintro ⟨e,he,he'⟩
        exact ⟨e,by have hh := mem_range.1 he; omega,he'.symm⟩
      · rintro ⟨e,he,he'⟩
        exact ⟨e,mem_range.2 (by omega),he'.symm⟩
    have hsub : P⊆Iic n := by
      intro k hk
      obtain ⟨e,he,rfl⟩ := (hP k).1 hk
      exact mem_Iic.2 ((Nat.le_log2 h).1 he)
    have hcard : P.card=n.log2+1 := by
      unfold P
      rw [card_image_of_injective,card_range]
      intro i j he
      have hg := congrArg Nat.log2 he
      simpa only [Nat.log2_two_pow] using hg
    have he : {k : ℕ | k≤n ∧ ¬∃ e : ℕ, k=2^e} = ((Iic n \ P : Finset ℕ) : Set ℕ) := by
      ext k
      simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_sdiff, mem_Iic, hP]
      constructor
      · rintro ⟨hk,hn⟩
        exact ⟨hk,fun ⟨e,he,he'⟩ => hn ⟨e,he'⟩⟩
      · rintro ⟨hk,hn⟩
        refine ⟨hk,?_⟩
        rintro ⟨e,rfl⟩
        exact hn ⟨e,(Nat.le_log2 h).2 hk,rfl⟩
    rw [he,ncard_finset,card_difference hsub,hcard,Nat.card_Iic]
    omega


private theorem count_positive_quotients (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Icc 1 (n+1), if 0<n/2^i then 1 else 0)=n.log2 := by
  have he (i : ℕ) : 0<n/2^i ↔ i≤n.log2 := by
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (Nat.two_pow_pos i),
      Nat.zero_add,Nat.one_mul,Nat.le_log2 (by omega : n≠0)]
  simp_rw [he]
  have hf : (Icc 1 (n+1)).filter (fun i => i≤n.log2)=Icc 1 n.log2 := by
    ext i
    simp only [mem_filter,mem_Icc]
    have hl := Nat.log2_le_self n
    omega
  rw [←sum_filter,hf,sum_const,Nat.card_Icc]
  simp

private theorem digit_size (i : ℕ) (hi : i≠0) : i.size=i.log2+1 := by
  apply Nat.le_antisymm
  · exact Nat.size_le.2 Nat.lt_log2_self
  · exact Nat.succ_le_of_lt (Nat.lt_size.2 (Nat.log2_self_le hi))

private theorem size_sum (n : ℕ) :
    (∑ i ∈ range n, i.size) = ∑ i ∈ range n, (i.log2+(if i=0 then 0 else 1)) := by
  apply sum_congr rfl
  intro i _
  by_cases h : i=0
  · subst i
    simp
  · rw [digit_size i h,if_neg h]

private theorem size_difference (n : ℕ) (hn : 0<n) :
    (∑ i ∈ range n, i.size)+1-(∑ i ∈ range (n+1), i.log2)=n-n.log2 := by
  rw [size_sum,sum_add_distrib,sum_range_succ]
  have h :
      (∑ i ∈ range n, if i=0 then 0 else 1)=n-1 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (show 1≤n by omega)
    rw [Nat.add_comm 1 m,sum_range_succ']
    simp
  rw [h]
  omega

private theorem jump_iff_power (n : ℕ) (hn : 0<n) :
    (n+1).log2=n.log2+1 ↔ ∃ e : ℕ, n+1=2^e := by
  constructor
  · intro h
    have hlow := Nat.log2_self_le (show n+1≠0 by omega)
    rw [h] at hlow
    have hhigh := Nat.lt_log2_self (n:=n)
    exact ⟨n.log2+1,by omega⟩
  · rintro ⟨e,he⟩
    have hlog : (n+1).log2=e := by rw [he,Nat.log2_two_pow]
    have he' : 0<e := by
      by_contra h
      have hzero : e=0 := by omega
      rw [hzero,pow_zero] at he
      omega
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show 1≤e by omega)
    have hed : e=d+1 := by omega
    have hupper : n.log2<d+1 := (Nat.log2_lt (show n≠0 by omega)).2 (by rw [←hed,←he]; omega)
    have hlower : d≤n.log2 := by
      apply (Nat.le_log2 (show n≠0 by omega)).2
      rw [hed,pow_succ] at he
      have hpos := Nat.two_pow_pos d
      omega
    omega

private theorem arithmetic (n : ℕ) :
    arithmeticDescriptions n (if n=0 then 1 else n-n.log2) := by
  by_cases h : n=0
  · subst n
    refine ⟨by omega,by omega,?_⟩
    constructor
    · intro _
      exact ⟨0,by decide⟩
    · intro _
      have h1 : (1 : ℕ).log2 = 0 := by simpa using (Nat.log2_two_pow (n := 0))
      simp [h1]
  · have hn : 0<n := by omega
    simp only [if_neg h]
    unfold arithmeticDescriptions
    refine ⟨fun _ => by rw [count_positive_quotients n hn],fun _ => (size_difference n hn).symm,?_⟩
    have h1 := Nat.log2_le_self n
    have h2 := Nat.log2_le_self (n+1)
    rw [←jump_iff_power n hn]
    omega

end OMA.S_oeis_a182220

open OMA.S_oeis_a182220 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182220.main := by
  intro n
  exact ⟨best_sources n,nonpower_count n,arithmetic n,fun hn =>
    ⟨tree_heights n hn,by simpa [show n≠0 by omega] using height_count n hn⟩⟩
