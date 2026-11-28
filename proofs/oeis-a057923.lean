import OMAStatements.S_oeis_a057923

open OMA.S_oeis_a057923

private lemma remove (x y : ℕ) :
    y + Nat.ldiff x y = y ||| x ∧ Nat.ldiff x y ≤ x ∧
      y ||| Nat.ldiff x y = y ||| x := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp [Nat.ldiff]
  | bit a x ih =>
    cases y using Nat.bitCasesOn with
    | bit b y =>
      obtain ⟨h₁, h₂, h₃⟩ := ih y
      simp only [Nat.ldiff_bit, Nat.lor_bit]
      cases a <;> cases b <;> simp [Nat.bit] <;> omega

private lemma least (y t : ℕ) : y ||| pick y t = y + pick y t := by
  obtain ⟨hs, hl, ho⟩ := remove (pick y t) y
  have hv := Nat.find_spec (candidate y t)
  have hm := Nat.find_min' (candidate y t) (ho.symm ▸ hv)
  unfold pick at *
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a057923.main := by
  intro n
  have hp : (pair n).1 ||| (pair n).2 = (pair n).1 + (pair n).2 := by
    cases n with
    | zero => decide
    | succ n => exact least _ _
  have hn := least (pair n).2 ((pair n).1 ||| (pair n).2)
  have hv := Nat.find_spec (candidate (pair n).2 ((pair n).1 ||| (pair n).2))
  change (pair n).1 < pick (pair n).2 ((pair n).1 ||| (pair n).2)
  unfold pick at *
  omega
