import OMAStatements.S_oeis_a362861
import Mathlib

/-!
# Zhi-Wei Sun's fixed-base distinct-summand conjectures in OEIS A362861

The final theorem proves both clauses of Conjecture 1(i), proposed May 5, 2023.
The independent `three_seven` theorem proves the distinct-summand clause of 1(ii).
The finite checks use a proved subset-sum bit recurrence. Disjoint geometric
rows of distinct summands extend the verified intervals without bound.
https://oeis.org/A362861
-/

/-! A contiguous interval of subsums extends along disjoint geometric rows. -/

namespace SunDistinctPowers

def RepIn (P : ℕ → Prop) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ x ∈ s, P x) ∧ ∑ x ∈ s, x = n

def Covers (P : ℕ → Prop) (L W : ℕ) : Prop := ∀ n, L≤n → n≤L+W → RepIn P n

theorem RepIn.mono {P Q : ℕ → Prop} {n : ℕ} (h : RepIn P n) (hp : ∀ x, P x → Q x) :
    RepIn Q n := by
  obtain ⟨s,hs,he⟩ := h
  exact ⟨s,fun x hx => hp x (hs x hx),he⟩

private theorem add_row {P : ℕ → Prop} {L W : ℕ} (seed : Covers P L W) (r : Finset ℕ)
    (fresh : ∀ x∈r, ¬ P x) (small : ∀ x∈r, x≤W+1) :
    Covers (fun x => P x ∨ x∈r) L (W+∑ x∈r,x) := by
  classical
  induction r using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, add_zero, Finset.notMem_empty, or_false] using seed
  | @insert x r hx ih =>
    have hi := ih (fun y hy => fresh y (Finset.mem_insert_of_mem hy))
      (fun y hy => small y (Finset.mem_insert_of_mem hy))
    intro n hn htop
    rw [Finset.sum_insert hx] at htop
    by_cases fixed : n ≤ L+(W+∑ y∈r,y)
    · exact (hi n hn fixed).mono fun y hy => hy.imp_right Finset.mem_insert_of_mem
    · have hsm := small x (Finset.mem_insert_self x r)
      obtain ⟨s,hs,he⟩ := hi (n-x) (by omega) (by omega)
      have hxs : x ∉ s := fun h => (hs x h).elim (fresh x (Finset.mem_insert_self x r)) hx
      refine ⟨insert x s, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl|hy
        · exact Or.inr (Finset.mem_insert_self _ _)
        · exact (hs y hy).imp_right Finset.mem_insert_of_mem
      · rw [Finset.sum_insert hxs, he]; omega

def mass (rows : ℕ → Finset ℕ) (i : ℕ) : ℕ := ∑ j∈Finset.range i, ∑ x∈rows j, x

theorem extend_rows {P : ℕ → Prop} {L W : ℕ} (rows : ℕ → Finset ℕ)
    (seed : Covers (fun x => P x ∧ ∀ j, x∉rows j) L W)
    (members : ∀ i x, x∈rows i → P x)
    (apart : ∀ i j, i<j → Disjoint (rows i) (rows j))
    (small : ∀ i x, x∈rows i → x ≤ W+mass rows i+1)
    (positive : ∀ i, 0 < ∑ x∈rows i, x) : ∀ n≥L, RepIn P n := by
  let allow (i x : ℕ) := P x ∧ ∀ j, i≤j → x∉rows j
  have hc : ∀ i, Covers (allow i) L (W+mass rows i) := by
    intro i
    induction i with
    | zero => simpa [allow,mass] using seed
    | succ i ih =>
      have hf : ∀ x∈rows i, ¬allow i x := fun x hx hh => hh.2 i (le_refl i) hx
      have ha := add_row ih (rows i) hf (small i)
      intro n hn ht
      have hsub := ha n hn (by simpa [mass, Finset.sum_range_succ, Nat.add_assoc] using ht)
      apply hsub.mono
      intro x hx
      rcases hx with hh|hh
      · exact ⟨hh.1,fun j hj => hh.2 j (by omega)⟩
      · exact ⟨members i x hh,fun j hj => Finset.disjoint_left.mp (apart i j (by omega)) hh⟩
  have hm : ∀ i, i ≤ mass rows i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hstep : mass rows (i+1) = mass rows i + ∑ x∈rows i,x := by simp only [mass, Finset.sum_range_succ]
      have hpos := positive i
      omega
  intro n hn
  exact (hc n n hn (by have := hm n; omega)).mono fun _ h => h.1

theorem extend_geometric {P : ℕ → Prop} {L W A C k g : ℕ} (rows : ℕ → Finset ℕ)
    (hk : 2≤k) (hg : 0<g) (hW : k^A+C ≤ g*W)
    (seed : Covers (fun x => P x ∧ ∀ j, x∉rows j) L W)
    (members : ∀ i x, x∈rows i → P x)
    (apart : ∀ i j, i<j → Disjoint (rows i) (rows j))
    (upper : ∀ i x, x∈rows i → g*x ≤ k^(A+i)+C)
    (lower : ∀ i, (k-1)*k^(A+i) ≤ g*(∑ x∈rows i, x)) : ∀ n≥L, RepIn P n := by
  have grow : ∀ i, k^(A+i)+C ≤ g*(W+mass rows i) := by
    intro i
    induction i with
    | zero => simpa [mass] using hW
    | succ i ih =>
      have he : k^(A+(i+1)) = k^(A+i)+(k-1)*k^(A+i) := by
        rw [show A+(i+1)=(A+i)+1 by omega, pow_succ]
        calc
          k^(A+i)*k = (1+(k-1))*k^(A+i) := by rw [show 1+(k-1)=k by omega, Nat.mul_comm]
          _ = _ := by ring
      have hm : mass rows (i+1) = mass rows i + ∑ x∈rows i,x := by simp only [mass, Finset.sum_range_succ]
      have h := Nat.add_le_add ih (lower i)
      rw [he,hm,Nat.left_distrib, Nat.left_distrib]
      rw [Nat.left_distrib] at h
      omega
  apply extend_rows rows seed members apart
  · intro i x hx
    have h := (upper i x hx).trans (grow i)
    have := Nat.le_of_mul_le_mul_left h hg
    omega
  · intro i
    have hpos : 0 < (k-1)*k^(A+i) := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    by_contra! hf
    have h := lower i
    rw [show (∑ x∈rows i,x)=0 by omega,mul_zero] at h
    omega

end SunDistinctPowers

namespace SunDistinctPowers

/-- Sums from different rows or columns are distinct when all columns are smaller than
the first row power. This applies at once to switches, reserved column zero and tail rows. -/
theorem rectangle_inj {k m A M : ℕ} (hk : 2≤k) (hm : 2 ≤ m) (hsep : m^M<k^A) :
    Set.InjOn (fun x : ℕ×ℕ => k^x.1+m^x.2) {x | A≤x.1 ∧ x.2≤M} := by
  have hrow {x y : ℕ×ℕ} (hx : A≤x.1 ∧ x.2≤M) (hxy : x.1<y.1) :
      k^x.1+m^x.2 < k^y.1+m^y.2 := by
    have hsmall := ((Nat.pow_le_pow_right (by omega : 0 < m) hx.2).trans_lt hsep).trans_le
      (Nat.pow_le_pow_right (by omega : 0<k) hx.1)
    have hpow := Nat.pow_le_pow_right (by omega : 0<k) (by omega : x.1+1≤y.1)
    rw [pow_succ] at hpow
    have hbig := Nat.mul_le_mul_left (k^x.1) hk
    omega
  intro x hx y hy he
  change k^x.1+m^x.2 = k^y.1+m^y.2 at he
  have h : x.1=y.1 := by
    rcases lt_trichotomy x.1 y.1 with h|h|h
    · exact False.elim ((hrow hx h).ne he)
    · exact h
    · exact False.elim ((hrow hy h).ne he.symm)
  rw [h] at he
  exact Prod.ext h ((Nat.pow_right_injective (by omega : 1 < m)) (Nat.add_left_cancel he))

end SunDistinctPowers

namespace SunFixedOdd
open SunDistinctPowers

def Good (k m n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ v∈s, ∃ a b : ℕ, v=k^a+m^b) ∧ ∑ v∈s,v=2*n

def exceptions : Finset ℕ := {2,7,10,11,12,27,35,50,51,52,55,60,135,255}

def normTerm (k m x : ℕ) : Prop := ∃ a b : ℕ, 2*x=k^a+m^b

theorem good_of_norm {k m n} (h : RepIn (normTerm k m) n) : Good k m n := by
  obtain ⟨s,hs,he⟩ := h
  refine ⟨s.image (2*·),?_,?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact hs x hx
  · rw [Finset.sum_image (fun a _ b _ hh => by omega), ←Finset.mul_sum, he]

/-- Bit `n` records whether a subset of the supplied distinct denominations sums to `n`. -/
def coinBits : List ℕ → ℕ
  | [] => 1
  | x::xs => let prev := coinBits xs; prev ||| (prev <<< x)

theorem bits_iff {ds : List ℕ} (nd : ds.Nodup) (n : ℕ) :
    (coinBits ds).testBit n = true ↔ RepIn (fun x => x∈ds) n := by
  induction ds generalizing n with
  | nil =>
    rw [coinBits,Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro rfl; exact ⟨∅,by simp,by simp⟩
    · rintro ⟨s,hs,he⟩
      have hh : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by simpa using hs x hx)
      simpa [hh] using he.symm
  | cons x ds ih =>
    obtain ⟨hx,hds⟩ := List.nodup_cons.mp nd
    rw [coinBits,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,ih hds,ih hds]
    constructor
    · rintro (hh|⟨hle,s,hs,he⟩)
      · exact hh.mono fun y hy => List.mem_cons_of_mem _ hy
      · have hn : x∉s := fun h => hx (hs x h)
        refine ⟨insert x s,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|ho
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hs y ho)
        · rw [Finset.sum_insert hn,he]; omega
    · rintro ⟨s,hs,he⟩
      by_cases hh : x∈s
      · have hsum := Finset.sum_erase_add s (fun y => y) hh
        refine Or.inr ⟨by omega,s.erase x,?_,by omega⟩
        intro y hy
        have hE := Finset.mem_erase.mp hy
        exact (List.mem_cons.mp (hs y hE.2)).resolve_left hE.1
      · refine Or.inl ⟨s,?_,he⟩
        intro y hy
        exact (List.mem_cons.mp (hs y hy)).resolve_left (fun h => hh (h ▸ hy))

end SunFixedOdd

namespace SunFixedOdd
open SunDistinctPowers

def coins (k m g u v : ℕ) : List ℕ :=
  ((List.range u).flatMap (fun a => (List.range v).map fun b => (k^a+m^b)/g)).dedup

theorem coins_nd (k m g u v : ℕ) : (coins k m g u v).Nodup := List.nodup_dedup _

theorem mem_coins {k m g u v x : ℕ} : x∈coins k m g u v ↔
    ∃ a<u, ∃ b<v, (k^a+m^b)/g=x := by simp [coins]

theorem coins_give {k m u v x : ℕ} (hk : Odd k) (hm : Odd m) (hx : x∈coins k m 2 u v) :
    normTerm k m x := by
  obtain ⟨a,_,b,_,rfl⟩ := mem_coins.mp hx
  exact ⟨a,b,Nat.mul_div_cancel' ((hk.pow.add_odd hm.pow).two_dvd)⟩

private def seedOK (ds : List ℕ) (L W : ℕ) : Bool :=
  (List.range (W+1)).all fun j => (coinBits ds).testBit (L+j)

theorem checked_seed {k m u v A L W : ℕ} (hk : Odd k) (hm : Odd m)
    (bound : (coins k m 2 u v).all (fun x => decide (2*x<k^A+1)) = true)
    (h : seedOK (coins k m 2 u v) L W = true) :
    Covers (fun x => normTerm k m x ∧ 2*x<k^A+1) L W := by
  intro n hn ht
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  apply ((bits_iff (coins_nd k m 2 u v) _).mp _).mono
  · intro x hx
    exact ⟨coins_give hk hm hx, of_decide_eq_true (List.all_eq_true.mp bound x hx)⟩
  · exact List.all_eq_true.mp h j (List.mem_range.mpr (by omega))

theorem five_seed : Covers (fun x => normTerm 5 5 x ∧ 2*x<5^5+1) 256 1831 :=
  checked_seed (u:=5) (v:=5) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem ternary_seed : Covers (fun x => normTerm 3 3 x ∧ 2*x<3^2+1) 0 6 :=
  checked_seed (u:=2) (v:=2) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem mixed_seed : Covers (fun x => normTerm 3 7 x ∧ 2*x<3^3+1) 0 20 :=
  checked_seed (u:=3) (v:=2) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exceptional_bounds {n : ℕ} (he : n∈exceptions) : n<256 := by
  have h : ∀ x∈exceptions, x<256 := by decide +kernel
  exact h n he

theorem small_five {n : ℕ} (hn : n<256) (he : n∉exceptions) : Good 5 5 n := by
  have h : (List.range 256).all (fun t => decide (t∈exceptions) ||
      (coinBits (coins 5 5 2 5 5)).testBit t) = true := by decide +kernel
  have hh := List.all_eq_true.mp h n (List.mem_range.mpr hn)
  simp only [Bool.or_eq_true,decide_eq_true_eq] at hh
  exact good_of_norm (((bits_iff (coins_nd _ _ _ _ _) _).mp (hh.resolve_left he)).mono
    (fun _ hx => coins_give (by decide) (by decide) hx))

theorem no_exception {n : ℕ} (he : n∈exceptions) : ¬Good 5 5 n := by
  have hbad : ∀ t∈exceptions, (coinBits (coins 5 5 1 5 5)).testBit (2*t)=false := by decide +kernel
  have hl := exceptional_bounds he
  rintro ⟨s,hs,hsum⟩
  have hrep : RepIn (fun x => x∈coins 5 5 1 5 5) (2*n) := by
    refine ⟨s,?_,hsum⟩
    intro x hx
    obtain ⟨a,b,heq⟩ := hs x hx
    have hu : x≤∑ i∈s,i := Finset.single_le_sum (fun i _ => Nat.zero_le i) hx
    have cut {i : ℕ} (h : 5^i≤x) : i<5 := by
      by_contra! hbig
      have := Nat.pow_le_pow_right (by decide : 0<5) hbig
      norm_num at this
      omega
    exact mem_coins.mpr ⟨a,cut (by rw [heq]; exact Nat.le_add_right _ _),
      b,cut (by rw [heq]; exact Nat.le_add_left _ _),by simpa using heq.symm⟩
  have ht := (bits_iff (coins_nd 5 5 1 5 5) _).mpr hrep
  rw [hbad n he] at ht
  contradiction

end SunFixedOdd

namespace SunFixedOdd
open SunDistinctPowers

theorem complete_fixed {k m A L W : ℕ} (hk : 2≤k) (hm : 2 ≤ m) (ho : Odd k) (ho' : Odd m)
    (separated : m^(k-2)<k^A) (width : k^A+m^(k-2)≤2*W)
    (seed : Covers (fun x => normTerm k m x ∧ 2*x<k^A+1) L W) :
    ∀ n≥L, Good k m n := by
  classical
  let val (i j : ℕ) := (k^(A+i)+m^j)/2
  let rows (i : ℕ) := (Finset.range (k-1)).image (val i)
  have eqv (i j : ℕ) : 2*val i j=k^(A+i)+m^j :=
    Nat.mul_div_cancel' ((ho.pow.add_odd ho'.pow).two_dvd)
  have inj := rectangle_inj hk hm separated
  have same {i j d e : ℕ} (hd : d∈Finset.range (k-1)) (he : e∈Finset.range (k-1))
      (h : val i d=val j e) : (A+i,d)=(A+j,e) := by
    have h₁ := Finset.mem_range.mp hd
    have h₂ := Finset.mem_range.mp he
    apply inj (x₁:=(A+i,d)) (x₂:=(A+j,e)) ⟨by simp,by change d≤k-2; omega⟩
      ⟨by simp,by change e≤k-2; omega⟩
    change k^(A+i)+m^d=k^(A+j)+m^e
    rw [←eqv,←eqv,h]
  have result : ∀ n≥L, RepIn (normTerm k m) n := by
    apply extend_geometric rows hk (by decide : 0<2) width
    · intro n hn ht
      apply (seed n hn ht).mono
      rintro x ⟨hx,hlt⟩
      refine ⟨hx,?_⟩
      intro i hi
      obtain ⟨j,_,he⟩ := Finset.mem_image.mp hi
      have hrow := eqv i j
      rw [he] at hrow
      have := Nat.pow_le_pow_right (by omega : 0<k) (show A≤A+i by omega)
      have := pow_pos (by omega : 0 < m) j
      omega
    · intro i x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨A+i,j,eqv i j⟩
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨d,hd,hh⟩ := Finset.mem_image.mp hx
      obtain ⟨e,he,hh'⟩ := Finset.mem_image.mp hy
      have := congrArg Prod.fst (same hd he (hh.trans hh'.symm))
      change A+i=A+j at this
      omega
    · intro i x hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      have := Finset.mem_range.mp hj
      rw [eqv]
      exact Nat.add_le_add_left (Nat.pow_le_pow_right (by omega : 0 < m) (by omega : j≤k-2)) _
    · intro i
      have hsz : (rows i).card=k-1 := by
        change ((Finset.range (k-1)).image (val i)).card = k-1
        rw [Finset.card_image_of_injOn, Finset.card_range]
        intro d hd e he hv
        exact congrArg Prod.snd (same hd he hv)
      calc
        (k-1)*k^(A+i) = ∑ _∈rows i,k^(A+i) := by simp [hsz]
        _ ≤ ∑ x∈rows i,2*x := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
          rw [eqv]; omega
        _ = 2*∑ x∈rows i,x := (Finset.mul_sum _ _ _).symm
  exact fun n hn => good_of_norm (result n hn)

end SunFixedOdd

namespace SunFixedOdd

theorem five_five (n : ℕ) : Good 5 5 n ↔ n∉exceptions := by
  constructor
  · exact fun good h => no_exception h good
  · intro h
    by_cases small : n<256
    · exact small_five small h
    · exact complete_fixed (k:=5) (m:=5) (A:=5) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) five_seed n (by omega)

theorem three_three (n : ℕ) : Good 3 3 n :=
  complete_fixed (k:=3) (m:=3) (A:=2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ternary_seed n (Nat.zero_le n)

theorem three_seven (n : ℕ) : Good 3 7 n :=
  complete_fixed (k:=3) (m:=7) (A:=3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) mixed_seed n (Nat.zero_le n)

end SunFixedOdd

theorem OMA.solution : type_of% @OMA.S_oeis_a362861.main := by
  constructor
  · intro n _
    change (¬ SunFixedOdd.Good 5 5 n) ↔ _
    rw [SunFixedOdd.five_five, not_not]
    simp [SunFixedOdd.exceptions]
  · intro n _
    exact SunFixedOdd.three_three n
