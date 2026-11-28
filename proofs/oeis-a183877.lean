import OMAStatements.S_oeis_a183877

/-!
A183877: valid ternary words, their closed count, recurrence, and generating function.
Source: https://oeis.org/A183877
Closed count: Vaclav Kotesovec; recurrence and generating function: Colin Barker.
Robert Israel identified the complement classes in the OEIS entry.
The letter-count criterion used here was independently isolated by @nerotulip90
in project note #155666. We prove that criterion below, then verify a 36-state
transfer calculation. All cached rows are checked by their transition equations.
-/

namespace Arrange
abbrev State := Fin 4 × Fin 3 × Fin 3
def zero : State := (0,0,0)
def step (s : State) (i : Fin 3) : State :=
  (⟨min 3 ((s.1).val + if i = 0 then 1 else 0), by omega⟩,
   ⟨min 2 ((s.2.1).val + if i=1 then 1 else 0), by omega⟩,
   ⟨min 2 ((s.2.2).val + if i=2 then 1 else 0), by omega⟩)
def accept (s : State) : Bool := decide (
  ((s.1).val = 0 ∨ 3 ≤ (s.1).val ∨ (1 ≤ (s.2.1).val ∧ 1 ≤ (s.2.2).val)) ∧
  ((s.2.1).val = 0 ∨ (1 ≤ (s.1).val ∧ 2 ≤ (s.2.1).val) ∨ 2 ≤ (s.2.2).val) ∧
  ((s.2.2).val = 0 ∨ (1 ≤ (s.1).val ∧ 2 ≤ (s.2.2).val) ∨ 2 ≤ (s.2.1).val))
def count : ℕ → State → ℤ
  | 0,s => if accept s then 1 else 0
  | n+1,s => count n (step s 0)+count n (step s 1)+count n (step s 2)

def table (n : ℕ) (s : State) : ℤ :=
  ((#[#[1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1,1,0,0,0,0,0,1,0,1,1,1,0,1,0,0,1,1,1,1],
#[0,0,0,0,0,2,0,2,3,0,0,1,0,2,3,1,3,3,1,0,2,0,2,3,2,3,3,1,1,3,1,2,3,3,3,3],
#[0,0,3,0,6,8,3,8,9,1,3,6,3,8,9,6,9,9,1,5,8,5,8,9,8,9,9,3,6,9,6,8,9,9,9,9],
#[1,12,17,12,24,26,17,26,27,7,19,23,19,26,27,23,27,27,13,22,26,22,26,27,26,27,27,15,23,27,23,26,27,27,27,27],
#[31,60,66,60,78,80,66,80,81,51,71,76,71,80,81,76,81,81,59,75,80,75,80,81,80,81,81,61,76,81,76,80,81,81,81,81],
#[171,215,222,215,240,242,222,242,243,201,231,237,231,242,243,237,243,243,211,236,242,236,242,243,242,243,243,213,237,243,237,242,243,243,243,243],
#[631,693,701,693,726,728,701,728,729,673,715,722,715,728,729,722,729,729,685,721,728,721,728,729,728,729,729,687,722,729,722,728,729,729,729,729],
#[2059,2142,2151,2142,2184,2186,2151,2186,2187,2115,2171,2179,2171,2186,2187,2179,2187,2187,2129,2178,2186,2178,2186,2187,2186,2187,2187,2131,2179,2187,2179,2186,2187,2187,2187,2187],
#[6399,6506,6516,6506,6558,6560,6516,6560,6561,6471,6543,6552,6543,6560,6561,6552,6561,6561,6487,6551,6560,6551,6560,6561,6560,6561,6561,6489,6552,6561,6552,6560,6561,6561,6561,6561]] : Array (Array ℤ)).getD n #[]).getD
    (s.1.val*9+s.2.1.val*3+s.2.2.val) 0

lemma table_zero : ∀ s : State, count 0 s=table 0 s := by decide +kernel
lemma table_step : ∀ n : Fin 8, ∀ s : State,
    table (n.val+1) s=table n.val (step s 0)+table n.val (step s 1)+table n.val (step s 2) := by
  decide +kernel

lemma count_table : ∀ n : ℕ, n≤8 → ∀ s : State, count n s=table n s
  | 0,_,s => table_zero s
  | n+1,h,s => by
    rw [count,count_table n (by omega),count_table n (by omega),count_table n (by omega)]
    exact (table_step ⟨n,by omega⟩ s).symm

lemma recurrence_base : ∀ s : State,
    count 8 s+12*count 6 s+3*count 4 s=6*count 7 s+10*count 5 s := by
  intro s
  rw [count_table 8 (by decide),count_table 6 (by decide),count_table 4 (by decide),
    count_table 7 (by decide),count_table 5 (by decide)]
  have h : ∀ s : State, table 8 s+12*table 6 s+3*table 4 s=6*table 7 s+10*table 5 s := by
    decide +kernel
  exact h s

lemma recurrence (n : ℕ) (hn : 4 ≤ n) : ∀ s : State,
    count (n+4) s+12*count (n+2) s+3*count n s =
      6*count (n+3) s+10*count (n+1) s := by
  induction n,hn using Nat.le_induction with
  | base => exact recurrence_base
  | succ n hn ih =>
    intro s
    have h0 := ih (step s 0)
    have h1 := ih (step s 1)
    have h2 := ih (step s 2)
    change
      (count (n+4) (step s 0)+count (n+4) (step s 1)+count (n+4) (step s 2))+
      12*(count (n+2) (step s 0)+count (n+2) (step s 1)+count (n+2) (step s 2))+
      3*(count n (step s 0)+count n (step s 1)+count n (step s 2)) =
      6*(count (n+3) (step s 0)+count (n+3) (step s 1)+count (n+3) (step s 2))+
      10*(count (n+1) (step s 0)+count (n+1) (step s 1)+count (n+1) (step s 2))
    linarith

theorem closed_count (n : ℕ) (hn : 4 ≤ n) : count n zero=3^n-2*(n+1:ℤ)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<8
    · interval_cases n <;> rw [count_table _ (by decide)] <;> decide +kernel
    · let k := n-4
      have hk : 4 ≤ k := by dsimp [k];omega
      have hn' : n=k+4 := by dsimp [k];omega
      have h0 := ih k (by omega) hk
      have h1 := ih (k+1) (by omega) (by omega)
      have h2 := ih (k+2) (by omega) (by omega)
      have h3 := ih (k+3) (by omega) (by omega)
      have hc := recurrence k hk zero
      rw [h0,h1,h2,h3] at hc
      rw [hn']
      simp only [pow_add, Nat.cast_add, Nat.cast_ofNat] at hc ⊢
      norm_num at hc ⊢
      nlinarith
end Arrange

namespace Arrange
open Finset OMA.S_oeis_a183877
def letters {m : ℕ} (w : Fin m → Fin 3) (a : Fin 3) : Finset (Fin m) :=
  univ.filter (fun i => w i=a)
def freq {m : ℕ} (w : Fin m → Fin 3) (a : Fin 3) : ℕ := (letters w a).card
def remaining {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (a : Fin 3) : Finset (Fin m) :=
  (letters w a).erase i
lemma freq_pos {m : ℕ} (w : Fin m → Fin 3) (a : Fin 3) :
    0<freq w a ↔ ∃ i, w i=a := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := card_pos.mp h
    exact ⟨i,(mem_filter.mp hi).2⟩
  · rintro ⟨i,hi⟩
    exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ i,hi⟩⟩
lemma remaining_add {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (a : Fin 3) :
    (remaining w i a).card + (if w i=a then 1 else 0) = freq w a := by
  unfold remaining freq
  by_cases h : w i=a
  · have hi : i∈letters w a := by simp [letters,h]
    rw [card_erase_of_mem hi,if_pos h]
    have hp := card_pos.mpr ⟨i,hi⟩
    omega
  · have hi : i∉letters w a := by simp [letters,h]
    rw [erase_eq_of_notMem hi,if_neg h,add_zero]

def Pairable {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (u v : Fin 3) : Prop :=
  ∃ j k, j≠i ∧ k≠i ∧ j≠k ∧ w j=u ∧ w k=v

lemma pair_iff {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (u v : Fin 3) :
    Pairable w i u v ↔
      if u=v then 2≤(remaining w i u).card
      else 0<(remaining w i u).card ∧ 0<(remaining w i v).card := by
  by_cases huv : u=v
  · subst v
    rw [if_pos rfl]
    constructor
    · rintro ⟨j,k,hji,hki,hjk,hj,hk⟩
      have h : 1<(remaining w i u).card := one_lt_card.mpr ⟨j,by simp [remaining,letters,hji,hj],
        k,by simp [remaining,letters,hki,hk],hjk⟩
      omega
    · intro h
      obtain ⟨j,hj,k,hk,hjk⟩ := one_lt_card.mp (show 1<(remaining w i u).card by omega)
      change j∈(letters w u).erase i at hj
      change k∈(letters w u).erase i at hk
      simp only [letters,mem_erase,mem_filter,mem_univ,true_and] at hj hk
      exact ⟨j,k,hj.1,hk.1,hjk,hj.2,hk.2⟩
  · rw [if_neg huv]
    constructor
    · rintro ⟨j,k,hji,hki,hjk,hj,hk⟩
      exact ⟨card_pos.mpr ⟨j,by simp [remaining,letters,hji,hj]⟩,
        card_pos.mpr ⟨k,by simp [remaining,letters,hki,hk]⟩⟩
    · rintro ⟨hu,hv⟩
      obtain ⟨j,hj⟩ := card_pos.mp hu
      obtain ⟨k,hk⟩ := card_pos.mp hv
      simp only [remaining,letters,mem_erase,mem_filter,mem_univ,true_and] at hj hk
      refine ⟨j,k,hj.1,hk.1,?_,hj.2,hk.2⟩
      intro h
      exact huv (hj.2.symm.trans ((congrArg w h).trans hk.2))

lemma at_iff {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) :
    (∃ j k, j≠i ∧ k≠i ∧ j≠k ∧ w j+w k=w i) ↔
      ∃ u v : Fin 3, u+v=w i ∧
        if u=v then 2≤(remaining w i u).card
        else 0<(remaining w i u).card ∧ 0<(remaining w i v).card := by
  constructor
  · rintro ⟨j,k,hji,hki,hjk,hs⟩
    exact ⟨w j,w k,hs,(pair_iff w i (w j) (w k)).mp ⟨j,k,hji,hki,hjk,rfl,rfl⟩⟩
  · rintro ⟨u,v,hs,hp⟩
    obtain ⟨j,k,hji,hki,hjk,hj,hk⟩ := (pair_iff w i u v).mpr hp
    exact ⟨j,k,hji,hki,hjk,by rw [hj,hk];exact hs⟩

lemma at_zero {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (hi : w i=0) :
    (∃ j k, j≠i ∧ k≠i ∧ j≠k ∧ w j+w k=w i) ↔
      3≤freq w 0 ∨ (1≤freq w 1 ∧ 1≤freq w 2) := by
  rw [at_iff,hi]
  have h0 := remaining_add w i 0
  have h1 := remaining_add w i 1
  have h2 := remaining_add w i 2
  simp [hi] at h0 h1 h2
  constructor
  · rintro ⟨u,v,hs,hp⟩
    rcases (show u=0 ∨ u=1 ∨ u=2 by omega) with rfl | rfl | rfl <;>
      rcases (show v=0 ∨ v=1 ∨ v=2 by omega) with rfl | rfl | rfl <;>
      norm_num [Fin.add_def] at hs <;> split_ifs at hp <;> omega
  · rintro (h | h)
    · refine ⟨0,0,by decide,?_⟩
      change 2≤(remaining w i 0).card
      omega
    · refine ⟨1,2,by decide,?_⟩
      change 0<(remaining w i 1).card ∧ 0<(remaining w i 2).card
      omega

lemma at_one {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (hi : w i=1) :
    (∃ j k, j≠i ∧ k≠i ∧ j≠k ∧ w j+w k=w i) ↔
      (1≤freq w 0 ∧ 2≤freq w 1) ∨ 2≤freq w 2 := by
  rw [at_iff,hi]
  have h0 := remaining_add w i 0
  have h1 := remaining_add w i 1
  have h2 := remaining_add w i 2
  simp [hi] at h0 h1 h2
  constructor
  · rintro ⟨u,v,hs,hp⟩
    rcases (show u=0 ∨ u=1 ∨ u=2 by omega) with rfl | rfl | rfl <;>
      rcases (show v=0 ∨ v=1 ∨ v=2 by omega) with rfl | rfl | rfl <;>
      norm_num [Fin.add_def] at hs <;> split_ifs at hp <;> omega
  · rintro (h | h)
    · refine ⟨0,1,by decide,?_⟩
      change 0<(remaining w i 0).card ∧ 0<(remaining w i 1).card
      omega
    · refine ⟨2,2,by decide,?_⟩
      change 2≤(remaining w i 2).card
      omega

lemma at_two {m : ℕ} (w : Fin m → Fin 3) (i : Fin m) (hi : w i=2) :
    (∃ j k, j≠i ∧ k≠i ∧ j≠k ∧ w j+w k=w i) ↔
      (1≤freq w 0 ∧ 2≤freq w 2) ∨ 2≤freq w 1 := by
  rw [at_iff,hi]
  have h0 := remaining_add w i 0
  have h1 := remaining_add w i 1
  have h2 := remaining_add w i 2
  simp [hi] at h0 h1 h2
  constructor
  · rintro ⟨u,v,hs,hp⟩
    rcases (show u=0 ∨ u=1 ∨ u=2 by omega) with rfl | rfl | rfl <;>
      rcases (show v=0 ∨ v=1 ∨ v=2 by omega) with rfl | rfl | rfl <;>
      norm_num [Fin.add_def] at hs <;> split_ifs at hp <;> omega
  · rintro (h | h)
    · refine ⟨0,2,by decide,?_⟩
      change 0<(remaining w i 0).card ∧ 0<(remaining w i 2).card
      omega
    · refine ⟨1,1,by decide,?_⟩
      change 2≤(remaining w i 1).card
      omega


def Good {m : ℕ} (w : Fin m → Fin 3) : Prop :=
  (freq w 0=0 ∨ 3≤freq w 0 ∨ (1≤freq w 1 ∧ 1≤freq w 2)) ∧
  (freq w 1=0 ∨ (1≤freq w 0 ∧ 2≤freq w 1) ∨ 2≤freq w 2) ∧
  (freq w 2=0 ∨ (1≤freq w 0 ∧ 2≤freq w 2) ∨ 2≤freq w 1)

theorem valid_iff_good {m : ℕ} (w : Fin m → Fin 3) : Valid w ↔ Good w := by
  constructor
  · intro h
    constructor
    · by_cases hz : freq w 0=0
      · exact Or.inl hz
      · obtain ⟨i,hi⟩ := (freq_pos w 0).mp (by omega)
        exact Or.inr ((at_zero w i hi).mp (h i))
    · constructor
      · by_cases hz : freq w 1=0
        · exact Or.inl hz
        · obtain ⟨i,hi⟩ := (freq_pos w 1).mp (by omega)
          exact Or.inr ((at_one w i hi).mp (h i))
      · by_cases hz : freq w 2=0
        · exact Or.inl hz
        · obtain ⟨i,hi⟩ := (freq_pos w 2).mp (by omega)
          exact Or.inr ((at_two w i hi).mp (h i))
  · rintro ⟨h0,h1,h2⟩ i
    have hc : w i=0 ∨ w i=1 ∨ w i=2 := by omega
    rcases hc with hc | hc | hc
    · apply (at_zero w i hc).mpr
      have hp := (freq_pos w 0).mpr ⟨i,hc⟩
      omega
    · apply (at_one w i hc).mpr
      have hp := (freq_pos w 1).mpr ⟨i,hc⟩
      omega
    · apply (at_two w i hc).mpr
      have hp := (freq_pos w 2).mpr ⟨i,hc⟩
      omega
end Arrange

namespace Arrange
open Finset OMA.S_oeis_a183877
def stateWord {m : ℕ} (s : State) (w : Fin m → Fin 3) : State :=
  (⟨min 3 ((s.1).val+freq w 0),by omega⟩,
   ⟨min 2 ((s.2.1).val+freq w 1),by omega⟩,
   ⟨min 2 ((s.2.2).val+freq w 2),by omega⟩)

lemma freq_cons {m : ℕ} (v : Fin 3) (w : Fin m → Fin 3) (b : Fin 3) :
    freq (Fin.cons v w) b=(if v=b then 1 else 0)+freq w b := by
  simp only [freq,letters,card_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]

lemma stateWord_cons {m : ℕ} (s : State) (v : Fin 3) (w : Fin m → Fin 3) :
    stateWord s (Fin.cons v w)=stateWord (step s v) w := by
  apply Prod.ext
  · apply Fin.ext
    simp only [stateWord,step,Prod.fst,Fin.val_mk,freq_cons]
    omega
  · apply Prod.ext
    · apply Fin.ext
      simp only [stateWord,step,Prod.fst,Prod.snd,Fin.val_mk,freq_cons]
      omega
    · apply Fin.ext
      simp only [stateWord,step,Prod.fst,Prod.snd,Fin.val_mk,freq_cons]
      omega

lemma stateWord_empty (s : State) (w : Fin 0 → Fin 3) : stateWord s w=s := by
  apply Prod.ext
  · apply Fin.ext
    simp [stateWord,freq,letters,Nat.min_eq_right (Nat.le_of_lt_succ s.1.isLt)]
  · apply Prod.ext
    · apply Fin.ext
      simp [stateWord,freq,letters,Nat.min_eq_right (Nat.le_of_lt_succ s.2.1.isLt)]
    · apply Fin.ext
      simp [stateWord,freq,letters,Nat.min_eq_right (Nat.le_of_lt_succ s.2.2.isLt)]

lemma accepted_iff {m : ℕ} (w : Fin m → Fin 3) :
    accept (stateWord zero w)=true ↔ Good w := by
  simp only [accept,stateWord,zero,Good,Prod.fst,Prod.snd,Fin.val_mk,Fin.val_zero,Nat.zero_add,decide_eq_true_eq]
  omega

def total (m : ℕ) (s : State) : ℤ :=
  ∑ w : Fin m → Fin 3, if accept (stateWord s w) then 1 else 0

lemma total_zero (s : State) : total 0 s=count 0 s := by
  unfold total
  simp [stateWord_empty,count]

lemma total_succ (m : ℕ) (s : State) :
    total (m+1) s=total m (step s 0)+total m (step s 1)+total m (step s 2) := by
  unfold total
  rw [←(Fin.consEquiv (fun _ : Fin (m+1) => Fin 3)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ v : Fin 3, ∑ w : Fin m → Fin 3,
    if accept (stateWord s (Fin.cons v w)) then 1 else 0)=_
  simp_rw [stateWord_cons]
  rw [Fin.sum_univ_three]

lemma total_count (m : ℕ) (s : State) : total m s=count m s := by
  induction m generalizing s with
  | zero => exact total_zero s
  | succ m ih =>
    rw [total_succ,ih,ih,ih]
    rfl

noncomputable def numberValid (m : ℕ) : ℕ := by
  classical
  exact ((univ : Finset (Fin m → Fin 3)).filter Valid).card

theorem numberValid_eq (m : ℕ) : (numberValid m : ℤ)=count m zero := by
  classical
  rw [←total_count]
  unfold total
  simp_rw [accepted_iff,←valid_iff_good]
  simp [numberValid]
end Arrange

namespace ArrangeAlgebra
lemma recurrence (a : ℕ → ℕ)
    (hc : ∀ n, 2≤n → (a n:ℤ)=3^(n+2)-2*(n+3:ℤ)^2)
    (n : ℕ) (hn : 5<n) :
    (a n:ℤ)=6*a (n-1)-12*a (n-2)+10*a (n-3)-3*a (n-4) := by
  let k:=n-4
  have hk : 2≤k := by dsimp [k];omega
  have hn' : n=k+4 := by dsimp [k];omega
  rw [hn']
  rw [show k+4-1=k+3 by omega,show k+4-2=k+2 by omega,
    show k+4-3=k+1 by omega,show k+4-4=k by omega]
  rw [hc (k+4) (by omega),hc (k+3) (by omega),hc (k+2) (by omega),
    hc (k+1) (by omega),hc k hk]
  simp only [pow_add,Nat.cast_add,Nat.cast_ofNat]
  norm_num
  ring

theorem generating_function (a : ℕ → ℕ) (h1 : a 1=1)
    (hc : ∀ n, 2≤n → (a n:ℤ)=3^(n+2)-2*(n+3:ℤ)^2) :
    (PowerSeries.mk (fun n => if n=0 then 0 else (a n:ℤ))) *
      ((1-PowerSeries.X)^3*(1-3*PowerSeries.X)) =
      PowerSeries.X*(1+25*PowerSeries.X-3*PowerSeries.X^2-33*PowerSeries.X^3+18*PowerSeries.X^4) := by
  open PowerSeries in
  let F := PowerSeries.mk (fun n => if n=0 then 0 else (a n:ℤ))
  change F * _ = _
  have he : F*((1-PowerSeries.X)^3*(1-3*PowerSeries.X)) =
      F-PowerSeries.C 6*(F*PowerSeries.X^1)+PowerSeries.C 12*(F*PowerSeries.X^2)-
      PowerSeries.C 10*(F*PowerSeries.X^3)+PowerSeries.C 3*(F*PowerSeries.X^4) := by
    simp only [map_ofNat,map_one]
    ring
  have hp : (PowerSeries.X*(1+25*PowerSeries.X-3*PowerSeries.X^2-33*PowerSeries.X^3+18*PowerSeries.X^4) : PowerSeries ℤ) =
      PowerSeries.C 1*PowerSeries.X^1+PowerSeries.C 25*PowerSeries.X^2-
      PowerSeries.C 3*PowerSeries.X^3-PowerSeries.C 33*PowerSeries.X^4+
      PowerSeries.C 18*PowerSeries.X^5 := by
    simp only [map_ofNat,map_one]
    ring
  rw [he,hp]
  ext n
  simp only [map_add,map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C,PowerSeries.coeff_mk,F]
  by_cases hn : 6≤n
  · have hr := recurrence a hc n (by omega)
    simp (disch := omega) only [if_pos,if_neg]
    linarith
  · have h2:=hc 2 (by decide)
    have h3:=hc 3 (by decide)
    have h4:=hc 4 (by decide)
    have h5:=hc 5 (by decide)
    norm_num at h2 h3 h4 h5
    interval_cases n <;> norm_num [h1,h2,h3,h4,h5]
end ArrangeAlgebra


namespace Arrange
open OMA.S_oeis_a183877
lemma a_eq_count (n : ℕ) : (a n:ℤ)=count (n+2) zero := by
  classical
  simpa only [a,numberValid] using numberValid_eq (n+2)

lemma a_one : a 1=1 := by
  have h : (a 1:ℤ)=1 := by
    rw [a_eq_count,count_table 3 (by decide)]
    decide +kernel
  exact_mod_cast h

theorem closed (n : ℕ) (hn : 2≤n) :
    (a n:ℤ)=3^(n+2)-2*(n+3:ℤ)^2 := by
  have h := closed_count (n+2) (by omega)
  rw [←a_eq_count n] at h
  convert h using 1 <;> push_cast <;> ring

theorem solution : type_of% @OMA.S_oeis_a183877.main := by
  refine ⟨a_one,closed,?_,?_⟩
  · exact ArrangeAlgebra.recurrence a closed
  · simpa only [gf] using ArrangeAlgebra.generating_function a a_one closed
end Arrange

theorem OMA.solution : type_of% @OMA.S_oeis_a183877.main := Arrange.solution
