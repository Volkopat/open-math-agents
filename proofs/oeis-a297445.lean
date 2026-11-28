import OMAStatements.S_oeis_a297445

/-! Least witnesses for the threshold on ternary digit up-variation. -/
-- Shorter proof: @STARDUSTLC666. First catalogue proof: @jleguina.

namespace TernaryUpVariation

open OMA.S_oeis_a297445

private lemma recurrence (n : ℕ) : a (n+2) = 9*a n+2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change a (n+2) + 9*a (n+1) - 9*a n = 9*a (n+1)+2
    omega

-- The two new digits account for at most two additional units of up-variation.
private lemma digits_pair (q t u : ℕ) (hq : 0 < q) (ht : t < 3) (hu : u < 3) :
    upVar (u+3*(t+3*q)) = (u-t) + (t-q%3) + upVar q := by
  unfold upVar
  rw [Nat.digits_add 3 (by decide) u (t+3*q) hu (Or.inr (by omega)),
    Nat.digits_add 3 (by decide) t q ht (Or.inr hq.ne'),
    Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hq.ne']
  simp only [upv]
  omega

private lemma least_threshold (n : ℕ) : ∃ w : ℕ, (w : ℤ) = a n ∧
    0 < w ∧ upVar w = n ∧ ∀ m : ℕ, 0 < m → n ≤ upVar m → w ≤ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => exact ⟨1,rfl,by decide,by decide,fun _ pos _ => pos⟩
    | 1 =>
      refine ⟨5,rfl,by decide,by decide,?_⟩
      intro m _ high
      by_contra! small
      exact (not_lt_of_ge high) ((by decide : ∀ j : Fin 5, upVar j < 1) ⟨m,small⟩)
    | k+2 =>
      obtain ⟨w,eq,pos,value,bound⟩ := ih k (by omega)
      have added := digits_pair w 0 2 pos (by decide) (by decide)
      refine ⟨9*w+2,by rw [recurrence,← eq]; push_cast; rfl,by omega,?_,?_⟩
      · rw [show 9*w+2 = 2+3*(0+3*w) by omega,added,value]
        omega
      · intro m hm high
        have large : 9 ≤ m := by
          by_contra! small
          have h := (by decide : ∀ j : Fin 9, upVar j < 2) ⟨m,small⟩
          change upVar m < 2 at h
          omega
        let q := m/9
        let t := m/3%3
        let u := m%3
        have split : u+3*(t+3*q) = m := by dsimp [q,t,u]; omega
        have ht : t < 3 := Nat.mod_lt _ (by decide)
        have hu : u < 3 := Nat.mod_lt _ (by decide)
        have qp : 0 < q := by dsimp [q]; omega
        have gain := digits_pair q t u qp ht hu
        rw [split] at gain
        have up : (u-t)+(t-q%3) ≤ 2 := by omega
        have low := bound q qp (by omega)
        by_cases same : q = w
        · rw [same,value] at gain
          omega
        · omega

end TernaryUpVariation

theorem OMA.solution : type_of% @OMA.S_oeis_a297445.main := by
  intro n
  obtain ⟨w,eq,pos,value,bound⟩ := TernaryUpVariation.least_threshold n
  exact ⟨w,eq,⟨pos,value⟩,fun m hm => bound m hm.1 hm.2.ge⟩
