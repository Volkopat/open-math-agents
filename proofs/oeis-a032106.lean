import OMAStatements.S_oeis_a032106

namespace OMA.S_oeis_a032106
open Finset

private abbrev Half (n : ℕ) := Fin (n-1)
private abbrev Pos (n : ℕ) := Half n ⊕ Half n ⊕ Unit

private def pack {n : ℕ} (w : Word n) : Finset (Pos n) := w.1.disjSum (w.2.1.disjSum w.2.2)
private def unpack {n : ℕ} (s : Finset (Pos n)) : Word n := (s.toLeft,s.toRight.toLeft,s.toRight.toRight)

private theorem pack_card {n : ℕ} (w : Word n) : (pack (n:=n) w).card = blackCount (n:=n) w := by
  simp [pack,blackCount,add_assoc]

private theorem mem_words {n : ℕ} {w : Word n} : w ∈ words n ↔ blackCount (n:=n) w = n := by
  simp [words]

private def allEquiv (n : ℕ) : ↥(words n) ≃ ↥((univ : Finset (Pos n)).powersetCard n) where
  toFun w := ⟨pack w.val,by simp [pack_card,mem_words.mp w.property]⟩
  invFun s := ⟨unpack s.val, by
    rw [mem_words, ← pack_card]
    simpa [pack,unpack,toLeft_disjSum_toRight] using (mem_powersetCard.mp s.property).2⟩
  left_inv _ := by apply Subtype.ext; simp [unpack,pack]
  right_inv _ := by apply Subtype.ext; simp [unpack,pack,toLeft_disjSum_toRight]

private theorem total_count (n : ℕ) (hn : 0<n) : (words n).card = (2*n-1).choose n := by
  have he := Fintype.card_congr (allEquiv n)
  simpa [Pos,Half,show (n-1)+(n-1+1)=2*n-1 by omega] using he

private def center (n : ℕ) : Finset Unit := if n%2=0 then ∅ else {()}

private theorem center_card (n : ℕ) : (center n).card = n%2 := by
  unfold center
  split_ifs with h <;> simp <;> omega

private theorem unit_cases (s : Finset Unit) : s=∅ ∨ s={()} := by
  by_cases hu : ()∈s
  · right; ext u; cases u; simp [hu]
  · left; ext u; cases u; simp [hu]

private def fixed (n : ℕ) := (words n).filter fun w => w.1=w.2.1

private theorem fixed_info {n : ℕ} {w : Word n} (hw : w ∈ fixed n) :
    w.1=w.2.1 ∧ w.1.card=n/2 ∧ w.2.2=center n := by
  obtain ⟨hc,hpal⟩ := mem_filter.mp hw
  have he := mem_words.mp hc
  unfold blackCount at he
  rw [← hpal] at he
  refine ⟨hpal,?_⟩
  rcases unit_cases w.2.2 with hh|hh <;> rw [hh] at he ⊢ <;> simp at he
  · have hpar : n % 2=0 := by omega
    simp [center,hpar]; omega
  · have hpar : n % 2≠0 := by omega
    simp [center,hpar]; omega

private def fixedEquiv (n : ℕ) : ↥(fixed n) ≃ ↥((univ : Finset (Half n)).powersetCard (n/2)) where
  toFun w := ⟨w.val.1,by simp [(fixed_info w.property).2.1]⟩
  invFun s := ⟨(s.val,s.val,center n),by
    apply mem_filter.mpr
    refine ⟨mem_words.mpr ?_,rfl⟩
    have hh := (mem_powersetCard.mp s.property).2
    simp [blackCount,center_card,hh]
    omega⟩
  left_inv w := by
    obtain ⟨he,_,hc⟩ := fixed_info w.property
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext he hc.symm)
  right_inv _ := rfl

private theorem fixed_count (n : ℕ) : (fixed n).card = (n-1).choose (n/2) := by
  simpa [Half] using Fintype.card_congr (fixedEquiv n)

private theorem key_injective {m : ℕ} : Function.Injective (halfKey (m:=m)) := by
  intro s t h
  have he := List.ofFn_inj.mp h
  ext i
  simpa using congrArg (· = true) (congrFun he i)

private def rev {n : ℕ} (w : Word n) : Word n := (w.2.1,w.1,w.2.2)

private theorem reversal_count (n : ℕ) :
    2*((words n).filter fun w => halfKey w.1 < halfKey w.2.1).card + (fixed n).card = (words n).card := by
  classical
  let A := (words n).filter fun w => halfKey w.1 < halfKey w.2.1
  let B := (words n).filter fun w => halfKey w.2.1 < halfKey w.1
  have hpair : A.card=B.card := by
    apply card_nbij' (rev (n:=n)) (rev (n:=n))
    · intro w hw
      simpa [A,B,rev,mem_words,blackCount,add_comm,add_left_comm,add_assoc] using hw
    · intro w hw
      simpa [A,B,rev,mem_words,blackCount,add_comm,add_left_comm,add_assoc] using hw
    · intro w _; rfl
    · intro w _; rfl
  change 2*A.card + _ = _
  rw [two_mul,show A.card + A.card = A.card+B.card from congrArg (A.card+·) hpair]
  unfold A B fixed
  simp only [card_filter, ← sum_add_distrib]
  calc
    _ = ∑ _w ∈ words n, 1 := by
      apply sum_congr rfl
      intro w _
      rcases lt_trichotomy (halfKey w.1) (halfKey w.2.1) with h|h|h
      · have hh : w.1 ≠ w.2.1 := fun e => (ne_of_lt h) (congrArg halfKey e)
        simp [h,hh,not_lt_of_gt h]
      · have hh := key_injective h
        simp [hh]
      · have hh : w.1 ≠ w.2.1 := fun e => (ne_of_gt h) (congrArg halfKey e)
        simp [h,hh,not_lt_of_gt h]
    _ = _ := by simp

private theorem middle_double (n : ℕ) (hn : 0<n) :
    (2*n).choose n = 2*((2*n-1).choose n) := by
  obtain _|k := n
  · omega
  rw [show 2*(k+1)=(2*k+1)+1 by omega,Nat.choose_succ_succ']
  simp only [Nat.add_sub_cancel, Nat.choose_symm_half]
  omega

private theorem count_result (n : ℕ) (hn : 1<n) : beadCount n =
    if Even n then ((2*n).choose n - n.choose (n/2))/4
    else ((2*n-1).choose (n-1) - (n-1).choose ((n-1)/2))/2 := by
  have h := reversal_count n
  have hc : beadCount n = ((words n).filter fun w => halfKey w.1 < halfKey w.2.1).card := by
    simp [beadCount,show n≠1 by omega]
  rw [← hc,fixed_count,total_count n (by omega)] at h
  have hs : (2*n-1).choose (n-1)=(2*n-1).choose n := Nat.choose_symm_of_eq_add (by omega)
  split_ifs with he
  · have he' := Nat.even_iff.mp he
    have hs' := middle_double (n/2) (by omega)
    rw [show 2*(n/2)=n by omega] at hs'
    rw [middle_double n (by omega),hs']
    omega
  · rw [Nat.even_iff] at he
    rw [hs,show (n-1)/2=n/2 by omega]
    omega

end OMA.S_oeis_a032106

open OMA.S_oeis_a032106 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032106.main := by
  refine ⟨?_,count_result⟩
  simpa [beadCount] using total_count 1 (by decide)
