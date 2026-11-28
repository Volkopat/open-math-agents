import OMAStatements.S_oeis_a319674

/-! Six-term blocks of A319674 and the ranks of its two auxiliary residue classes. -/
-- Credit: @STARDUSTLC666

namespace SixTermSum

open OMA.S_oeis_a319674

private def blockValue (q : ℤ) : ℕ → ℤ
  | 0 => -9*q
  | 1 => 1-3*q
  | 2 => 3+3*q
  | 3 => 6+9*q
  | 4 => 2+3*q
  | _ => -3-3*q

private lemma step (n : ℕ) :
    a (n+1) = a n + ((n : ℤ)+1) * (if n%6 < 3 then 1 else -1) := by
  simp only [a, Finset.sum_Icc_succ_top (show 1 ≤ n+1 by omega), Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  rw [neg_one_pow_eq_pow_mod_two]
  split
  · rw [show n/3%2 = 0 by omega, pow_zero]
  · rw [show n/3%2 = 1 by omega, pow_one]

private lemma closed (n : ℕ) : a n = blockValue (n/6 : ℕ) (n%6) := by
  induction n with
  | zero => norm_num [a, blockValue]
  | succ n ih =>
    have divstep : (n+1)/6 = n/6 + (if n%6 = 5 then 1 else 0) := by split <;> omega
    have modstep : (n+1)%6 = (n%6+1)%6 := by omega
    rw [step, ih, divstep, modstep, Nat.cast_add]
    have decomp : (n : ℤ) = 6*(n/6 : ℕ) + (n%6 : ℕ) := by omega
    have bound := Nat.mod_lt n (by decide : 0 < 6)
    generalize hr : n%6 = r at decomp bound ⊢
    interval_cases r <;> norm_num [blockValue] at * <;> omega

private lemma signs (n : ℕ) (hn : 2 ≤ n) :
    (0 < a n →
      (n%6 = 2 ∧ 2*a n = (n : ℤ)+4) ∨ (n%6 = 3 ∧ 2*a n = 3*((n : ℤ)+1)) ∨
        (n%6 = 4 ∧ 2*a n = (n : ℤ))) ∧
    (a n < 0 →
      (n%6 = 0 ∧ 2*a n = -3*(n : ℤ)) ∨ (n%6 = 1 ∧ 2*a n = 3-(n : ℤ)) ∨
        (n%6 = 5 ∧ 2*a n = -(n : ℤ)-1)) := by
  have formula := closed n
  have decomp : (n : ℤ) = 6*(n/6 : ℕ) + (n%6 : ℕ) := by omega
  have bound := Nat.mod_lt n (by decide : 0 < 6)
  generalize hr : n%6 = r at formula decomp bound ⊢
  interval_cases r <;> norm_num [blockValue] at formula ⊢ <;> omega

-- The zero-based enumeration lists b and c in that order in every block of six.
private def pairAt (b c j : ℕ) : ℕ := 6*(j/2) + if j%2 = 0 then b else c

private lemma pairNth {b c : ℕ} (bc : b < c) (c6 : c < 6) (j : ℕ) :
    Nat.nth (fun x => x%6 = b ∨ x%6 = c) j = pairAt b c j := by
  have mono : StrictMono (pairAt b c) := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [pairAt]
    split <;> split <;> omega
  have mem (i : ℕ) : (pairAt b c i)%6 = b ∨ (pairAt b c i)%6 = c := by
    unfold pairAt
    split <;> omega
  have onto (x : ℕ) (hx : x%6 = b ∨ x%6 = c) : x ∈ Set.range (pairAt b c) := by
    rcases hx with hb | hc
    · exact ⟨2*(x/6), by unfold pairAt; split <;> omega⟩
    · exact ⟨2*(x/6)+1, by unfold pairAt; split <;> omega⟩
  have inf : (Set.ofPred (fun x : ℕ => x%6 = b ∨ x%6 = c)).Infinite :=
    (Set.infinite_range_of_injective mono.injective).mono (by
      rintro _ ⟨i, rfl⟩
      exact mem i)
  have h := Nat.nth_comp_of_strictMono (n := j) mono onto (fun hf => (inf hf).elim)
  rw [Nat.nth_of_forall (fun i _ => mem i)] at h
  exact h.symm

private lemma rank {b c m n : ℕ} (bc : b < c) (c6 : c < 6) (hm : 1 ≤ m)
    (h : Nat.nth (fun x => x%6 = b ∨ x%6 = c) (m-1) = n) :
    (n%6 = b ∧ m%2 = 1) ∨ (n%6 = c ∧ m%2 = 0) := by
  rw [pairNth bc c6, pairAt] at h
  split at h <;> omega

private lemma missing {b c n : ℕ} (bc : b < c) (c6 : c < 6)
    (h : ∀ m : ℕ, 1 ≤ m → Nat.nth (fun x => x%6 = b ∨ x%6 = c) (m-1) ≠ n) :
    n%6 ≠ b ∧ n%6 ≠ c := by
  constructor
  · intro hb
    apply h (2*(n/6)+1) (by omega)
    rw [pairNth bc c6, pairAt]
    split <;> omega
  · intro hc
    apply h (2*(n/6)+2) (by omega)
    rw [pairNth bc c6, pairAt]
    split <;> omega

end SixTermSum

open SixTermSum OMA.S_oeis_a319674

theorem OMA.solution : type_of% @OMA.S_oeis_a319674.main := by
  intro n hn
  obtain ⟨pos, neg⟩ := signs n hn
  constructor
  · intro hp
    specialize pos hp
    constructor
    · intro m hm he
      have h := rank (b := 2) (c := 4) (by decide) (by decide) hm he
      have hi : 2*a n = (n : ℤ)+4*(m%2 : ℕ) := by omega
      generalize hbit : m%2 = bit at hi ⊢
      have hq := congrArg (fun z : ℤ => (z : ℚ)) hi
      push_cast at hq ⊢
      linarith
    · intro absent
      have h := missing (b := 2) (c := 4) (by decide) (by decide) absent
      have hi : 2*a n = 3*((n : ℤ)+1) := by omega
      have hq : 2*(a n : ℚ) = 3*((n : ℚ)+1) := by exact_mod_cast hi
      linarith
  · intro hn'
    specialize neg hn'
    constructor
    · intro m hm he
      have h := rank (b := 1) (c := 5) (by decide) (by decide) hm he
      have hi : 2*a n = -(n : ℤ)-1+4*(m%2 : ℕ) := by omega
      generalize hbit : m%2 = bit at hi ⊢
      have hq := congrArg (fun z : ℤ => (z : ℚ)) hi
      push_cast at hq ⊢
      linarith
    · intro absent
      have h := missing (b := 1) (c := 5) (by decide) (by decide) absent
      have hi : 2*a n = -3*(n : ℤ) := by omega
      have hq : 2*(a n : ℚ) = -3*(n : ℚ) := by exact_mod_cast hi
      linarith
