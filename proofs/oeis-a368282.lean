import OMAStatements.S_oeis_a368282

/-!
Every completed substitution block contributes exactly d ones. Inside
block i, dividing the number of preceding ones by d gives i at a one
and i+1 at the possible final zero.
-/

namespace OMA.S_oeis_a368282

private theorem offset_next (w : ℕ → Bool) (d i : ℕ) :
    offset w d (i+1) = offset w d i + (d+(w i).toNat) := by
  unfold offset
  rw [ones,Nat.mul_add,Nat.mul_one]
  omega

private theorem ones_run (w : ℕ → Bool) (d i j : ℕ) (h : Fixed w d) (hj : j≤d) :
    ones w (offset w d i+j)=ones w (offset w d i)+j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : offset w d i+(j+1)=(offset w d i+j)+1 := by omega
    rw [he,ones,h.1 i j (by omega),ih (by omega)]
    rfl

private theorem ones_offset (w : ℕ → Bool) (d i : ℕ) (h : Fixed w d) :
    ones w (offset w d i)=d*i := by
  induction i with
  | zero => simp [offset,ones]
  | succ i ih =>
    rw [offset_next]
    cases hi : w i with
    | false =>
      change ones w (offset w d i+(d+0))=d*(i+1)
      rw [Nat.add_zero,ones_run w d i d h le_rfl,ih,Nat.mul_add,Nat.mul_one]
    | true =>
      change ones w (offset w d i+(d+1))=d*(i+1)
      rw [show offset w d i+(d+1)=(offset w d i+d)+1 by omega,
        ones,h.2 i hi,ones_run w d i d h le_rfl,ih,Nat.mul_add,Nat.mul_one]
      rfl

private theorem block_index (w : ℕ → Bool) (d k : ℕ) (hd : 0<d) :
    ∃ i j : ℕ, k=offset w d i+j ∧ j<d+(w i).toNat := by
  induction k with
  | zero =>
    refine ⟨0,0,by simp [offset,ones],by omega⟩
  | succ k ih =>
    obtain ⟨i,j,hk,hj⟩ := ih
    by_cases hb : j+1<d+(w i).toNat
    · exact ⟨i,j+1,by omega,hb⟩
    · refine ⟨i+1,0,?_,by omega⟩
      rw [offset_next]
      omega

private theorem prefix_rec (w : ℕ → Bool) (d k : ℕ) (hd : 0<d) (h : Fixed w d) :
    ones w (k+1)=(k+1)-ones w (ones w k/d) := by
  obtain ⟨i,j,rfl,hj⟩ := block_index w d k hd
  by_cases ht : j<d
  · have hb := ones_run w d i j h (by omega)
    have hb' := ones_run w d i (j+1) h (by omega)
    rw [ones_offset w d i h] at hb hb'
    rw [hb,Nat.mul_add_div hd,Nat.div_eq_of_lt ht,
      show offset w d i+j+1=offset w d i+(j+1) by omega,hb']
    simp only [Nat.add_zero]
    unfold offset
    omega
  · have hw : w i=true := by
      cases he : w i with
      | false => simp only [he,Bool.toNat_false,Nat.add_zero] at hj; omega
      | true => rfl
    have he : j=d := by simp only [hw,Bool.toNat_true] at hj; omega
    subst j
    have hb := ones_run w d i d h le_rfl
    rw [ones_offset w d i h] at hb
    rw [ones,h.2 i hw,hb,Nat.mul_add_div hd,Nat.div_self (by omega)]
    have hi : ones w (i+1)=ones w i+1 := by rw [ones,hw]; rfl
    rw [hi]
    simp only [Bool.toNat_false,Nat.add_zero]
    unfold offset
    omega

end OMA.S_oeis_a368282

open OMA.S_oeis_a368282 in
theorem OMA.solution : type_of% @OMA.S_oeis_a368282.main := by
  intro d hd w h
  exact ⟨rfl,fun k => prefix_rec w d k hd h⟩
