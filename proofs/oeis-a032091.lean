import OMAStatements.S_oeis_a032091

namespace OMA.S_oeis_a032091
open Finset

private abbrev Half (l : ℕ) := Fin (l/2)
private abbrev Pos (l : ℕ) := Half l ⊕ Half l ⊕ Fin (l%2)

private def pack {l : ℕ} (w : Word l) : Finset (Pos l) :=
  w.1.disjSum (w.2.1.disjSum w.2.2)

private def unpack {l : ℕ} (s : Finset (Pos l)) : Word l :=
  (s.toLeft,s.toRight.toLeft,s.toRight.toRight)

private theorem pack_card {l : ℕ} (w : Word l) : (pack (l:=l) w).card = blackCount (l:=l) w := by
  simp [pack,blackCount,add_assoc]

private theorem mem_words {l : ℕ} {w : Word l} : w ∈ words l ↔ blackCount (l:=l) w = 4 := by
  simp [words]

private def allEquiv (l : ℕ) : ↥(words l) ≃ ↥((univ : Finset (Pos l)).powersetCard 4) where
  toFun w := ⟨pack w.val,by simp [pack_card,mem_words.mp w.property]⟩
  invFun s := ⟨unpack s.val, by
    rw [mem_words, ← pack_card]
    simpa [pack,unpack,toLeft_disjSum_toRight] using (mem_powersetCard.mp s.property).2⟩
  left_inv _ := by apply Subtype.ext; simp [unpack,pack]
  right_inv _ := by apply Subtype.ext; simp [unpack,pack,toLeft_disjSum_toRight]

private theorem total_count (l : ℕ) : (words l).card = l.choose 4 := by
  simpa [Pos,Half,show l/2+(l/2+l%2)=l by omega] using Fintype.card_congr (allEquiv l)

private def fixed (l : ℕ) := (words l).filter fun w => w.1=w.2.1

private theorem fixed_info {l : ℕ} {w : Word l} (hw : w ∈ fixed l) :
    w.1=w.2.1 ∧ w.1.card=2 ∧ w.2.2=∅ := by
  obtain ⟨hc,he⟩ := mem_filter.mp hw
  have h := mem_words.mp hc
  unfold blackCount at h
  rw [← he] at h
  have hb : w.2.2.card ≤ l%2 := by simpa using card_le_univ w.2.2
  exact ⟨he,by omega,card_eq_zero.mp (by omega)⟩

private def fixedEquiv (l : ℕ) : ↥(fixed l) ≃ ↥((univ : Finset (Half l)).powersetCard 2) where
  toFun w := ⟨w.val.1,by simp [(fixed_info w.property).2.1]⟩
  invFun s := ⟨(s.val,s.val,∅),by
    apply mem_filter.mpr
    refine ⟨mem_words.mpr ?_,rfl⟩
    simp [blackCount,(mem_powersetCard.mp s.property).2]⟩
  left_inv w := by
    obtain ⟨he,_,hc⟩ := fixed_info w.property
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext he hc.symm)
  right_inv _ := rfl

private theorem fixed_count (l : ℕ) : (fixed l).card = (l/2).choose 2 := by
  simpa [Half] using Fintype.card_congr (fixedEquiv l)

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

private theorem choose_four (m : ℕ) (hm : 3 ≤ m) :
    24*(m.choose 4 : ℚ) = (m:ℚ)*(m-1)*(m-2)*(m-3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 4
  norm_num [Nat.descFactorial_succ] at h
  have ht : (24 * m.choose 4 : ℚ) =
      ((m-3:ℕ):ℚ)*(((m-2:ℕ):ℚ)*(((m-1:ℕ):ℚ)*m)) := by exact_mod_cast h.symm
  push_cast [Nat.cast_sub (by omega : 3 ≤ m),Nat.cast_sub (by omega : 2 ≤ m),
    Nat.cast_sub (by omega : 1 ≤ m)] at ht
  linarith only [ht]

private theorem choose_two (m : ℕ) (hm : 1 ≤ m) :
    2*(m.choose 2 : ℚ) = (m:ℚ)*(m-1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 2
  norm_num [Nat.descFactorial_succ] at h
  have ht : (2 * m.choose 2 : ℚ) = ((m-1:ℕ):ℚ)*m := by exact_mod_cast h.symm
  simpa [Nat.cast_sub hm,mul_comm] using ht

private theorem polynomial (n : ℕ) (hn : 6 ≤ n) :
    (beadCount n : ℚ) =
    if Even n then ((n:ℚ)^4 - 10*n^3 + 32*n^2 - 32*n)/48
    else ((n:ℚ)^4 - 10*n^3 + 32*n^2 - 38*n + 15)/48 := by
  let l := n-1
  have hr := reversal_count l
  change 2 * beadCount n + _ = _ at hr
  rw [fixed_count,total_count] at hr
  have h : 2*(beadCount n:ℚ) + ((l/2).choose 2:ℚ) = (l.choose 4:ℚ) := by exact_mod_cast hr
  have hl : (l:ℚ) = (n:ℚ)-1 := Nat.cast_sub (by omega : 1≤n)
  have h4 := choose_four l (by dsimp [l]; omega)
  have h2 := choose_two (l/2) (by dsimp [l]; omega)
  rw [hl] at h4
  split_ifs with he
  · rw [Nat.even_iff] at he
    have hh : 2*(l/2)+2=n := by dsimp [l]; omega
    have hc : 2*((l/2:ℕ):ℚ)+2=n := by exact_mod_cast hh
    have hdiv : ((l/2:ℕ):ℚ)=((n:ℚ)-2)/2 := by linarith
    rw [hdiv] at h2
    linear_combination h / 2 + h4 / 48 - h2 / 4
  · rw [Nat.even_iff] at he
    have hh : 2*(l/2)+1=n := by dsimp [l]; omega
    have hc : 2*((l/2:ℕ):ℚ)+1=n := by exact_mod_cast hh
    have hdiv : ((l/2:ℕ):ℚ)=((n:ℚ)-1)/2 := by linarith
    rw [hdiv] at h2
    linear_combination h / 2 + h4 / 48 - h2 / 4

end OMA.S_oeis_a032091

theorem OMA.solution : type_of% @OMA.S_oeis_a032091.main := OMA.S_oeis_a032091.polynomial
