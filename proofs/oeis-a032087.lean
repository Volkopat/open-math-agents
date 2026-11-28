import OMAStatements.S_oeis_a032087

namespace OMA.S_oeis_a032087
open Finset

private theorem reverse_twice {n : ℕ} (w : Word n) : reverseWord (reverseWord w) = w := by
  funext i
  simp [reverseWord]

private def halfIndex {n : ℕ} (i : Fin n) : Fin ((n+1)/2) :=
  ⟨min i.val i.rev.val,by rw [Fin.val_rev]; omega⟩

private def includeIndex {n : ℕ} (i : Fin ((n+1)/2)) : Fin n := ⟨i.val,by omega⟩

private theorem half_reverse {n : ℕ} (i : Fin n) : halfIndex i.rev = halfIndex i := by
  ext
  simp [halfIndex,min_comm]

private def palindromeEquiv (n : ℕ) : {w : Word n // reverseWord w = w} ≃ (Fin ((n+1)/2) → Fin 4) where
  toFun w j := w.val (includeIndex j)
  invFun h := ⟨fun i => h (halfIndex i), by funext i; simp [reverseWord,half_reverse]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    change w.val (includeIndex (halfIndex i)) = w.val i
    by_cases hi : i.val ≤ i.rev.val
    · have he : includeIndex (halfIndex i) = i := Fin.ext (min_eq_left hi)
      rw [he]
    · have he : includeIndex (halfIndex i) = i.rev := Fin.ext (min_eq_right (by omega))
      rw [he]
      exact congrFun w.property i
  right_inv w := by
    funext j
    change w (halfIndex (includeIndex j)) = w j
    congr 1
    apply Fin.ext
    change min j.val (includeIndex j).rev.val = j.val
    rw [Fin.val_rev]
    apply min_eq_left
    change j.val ≤ n-(j.val+1)
    omega

private theorem pal_count (n : ℕ) :
    (univ.filter fun w : Word n => reverseWord w = w).card = 4^((n+1)/2) := by
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_congr (palindromeEquiv n)

private def forward {n : ℕ} (w : Word n) : Prop := List.ofFn w < List.ofFn (reverseWord w)
private def backward {n : ℕ} (w : Word n) : Prop := List.ofFn (reverseWord w) < List.ofFn w

local instance {n : ℕ} (w : Word n) : Decidable (forward w) := inferInstanceAs (Decidable (_ < _))
local instance {n : ℕ} (w : Word n) : Decidable (backward w) := inferInstanceAs (Decidable (_ < _))

private theorem paired_count (n : ℕ) :
    (univ.filter (forward (n:=n))).card = (univ.filter (backward (n:=n))).card := by
  classical
  apply card_nbij' reverseWord reverseWord
  · intro a ha
    simpa [forward,backward,reverse_twice] using ha
  · intro a ha
    simpa [forward,backward,reverse_twice] using ha
  · intro a _
    exact reverse_twice a
  · intro a _
    exact reverse_twice a

private theorem reversal_count (n : ℕ) :
    2*(univ.filter (forward (n:=n))).card + 4^((n+1)/2) = 4^n := by
  classical
  rw [two_mul]
  rw [show (univ.filter (forward (n:=n))).card + (univ.filter forward).card =
      (univ.filter (forward (n:=n))).card + (univ.filter backward).card from
      congrArg ((univ.filter (forward (n:=n))).card + ·) (paired_count n)]
  rw [← pal_count]
  simp only [card_filter, ← sum_add_distrib]
  calc
    _ = ∑ _w : Word n, 1 := by
      apply sum_congr rfl
      intro w _
      rcases lt_trichotomy (List.ofFn w) (List.ofFn (reverseWord w)) with h|h|h
      · have hh : reverseWord w ≠ w := by intro he; rw [he] at h; exact lt_irrefl _ h
        simp [forward,backward,h,not_lt_of_gt h,hh]
      · have hh : reverseWord w = w := (List.ofFn_inj.mp h).symm
        simp [forward,backward,hh]
      · have hh : reverseWord w ≠ w := by intro he; rw [he] at h; exact lt_irrefl _ h
        simp [forward,backward,h,not_lt_of_gt h,hh]
    _ = _ := by simp [Word]

private theorem count_formula (n : ℕ) (hn : 1<n) :
    beadCount n = (4^n - (if Even n then 2^n else 2^(n+1))) / 2 := by
  classical
  have he := reversal_count n
  have hh : 4^((n+1)/2) = (if Even n then 2^n else 2^(n+1)) := by
    rw [show (4:ℕ)=2^2 by decide, ← pow_mul]
    split_ifs with hp
    · rw [Nat.even_iff] at hp
      congr 1
      omega
    · rw [Nat.even_iff] at hp
      congr 1
      omega
  rw [hh] at he
  have hc : beadCount n=(univ.filter (forward (n:=n))).card := by
    unfold beadCount
    apply congrArg Finset.card
    ext w
    simp [forward,show n≠1 by omega]
  omega

end OMA.S_oeis_a032087

open OMA.S_oeis_a032087 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032087.main :=
  ⟨by simp [beadCount, Word], count_formula⟩
