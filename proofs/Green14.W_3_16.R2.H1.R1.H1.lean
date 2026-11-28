import OMAReductions.R_Green14_W_3_16_R2_H1_R1

-- Step Green14.W_3_16.R2.H1.R1.H1: hypothesis H1 of reduction Green14.W_3_16.R2.H1.R1.
-- Written with Claude Code (AI-assisted).
-- An explicit reflection-symmetric 2-coloring of {0, ..., 230} (found with a SAT solver): the
-- `true` positions contain no 3-term progression and the `false` positions no 16-term one.
-- The coloring is the bit pattern of the number `M`; it is checked by a Boolean checker, with a
-- soundness lemma, evaluated by the kernel.

namespace OMA.G14W316H1b

def M : Nat := 105415954105051622863246535537913902584431136677165610424602738688

def col (i : Nat) : Bool := M.testBit i

def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f k && allBelow k f

def anyBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | k + 1, f => f k || anyBelow k f

theorem allBelow_sound : ∀ (n : Nat) (f : Nat → Bool), allBelow n f = true → ∀ k < n, f k = true
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, f, h, k, hk => by
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact allBelow_sound n f h.2 k hk
    · exact h.1

theorem anyBelow_sound : ∀ (n : Nat) (f : Nat → Bool), anyBelow n f = true → ∃ k < n, f k = true
  | 0, _, h => by simp [anyBelow] at h
  | n + 1, f, h => by
    simp only [anyBelow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨n, Nat.lt_succ_self n, h⟩
    · obtain ⟨k, hk, hf⟩ := anyBelow_sound n f h
      exact ⟨k, Nat.lt_succ_of_lt hk, hf⟩

def len (b : Bool) : Nat := if b then 16 else 3

def apOK (b : Bool) (a d : Nat) : Bool :=
  d == 0 || decide (231 ≤ a + (len b - 1) * d) || anyBelow (len b) (fun t => col (a + t * d) == b)

theorem symm_ok : allBelow 231 (fun x => col (231 - 1 - x) == col x) = true := by decide +kernel

theorem ap_false : allBelow 231 (fun a => allBelow 231 (fun d => apOK false a d)) = true := by
  decide +kernel

theorem ap_true : allBelow 231 (fun a => allBelow 231 (fun d => apOK true a d)) = true := by
  decide +kernel

theorem good : (∀ x < 231, col (231 - 1 - x) = col x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d →
      a + ((if b then 16 else 3) - 1) * d < 231 →
      ∃ t < (if b then 16 else 3), col (a + t * d) = b := by
  refine ⟨fun x hx => ?_, fun b a d hd hfit => ?_⟩
  · have := allBelow_sound _ _ symm_ok x hx
    simpa using this
  · have hd' : d < 231 := by
      have : d ≤ ((if b then 16 else 3) - 1) * d := by
        apply Nat.le_mul_of_pos_left; split <;> decide
      omega
    have ha : a < 231 := by omega
    have hall : allBelow 231 (fun a => allBelow 231 (fun d => apOK b a d)) = true := by
      cases b
      · exact ap_false
      · exact ap_true
    have h1 := allBelow_sound _ _ (allBelow_sound _ _ hall a ha) d hd'
    simp only [apOK, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    have hlen : len b = (if b then 16 else 3) := rfl
    rcases h1 with (h1 | h1) | h1
    · omega
    · rw [hlen] at h1; omega
    · obtain ⟨t, ht, hc⟩ := anyBelow_sound _ _ h1
      exact ⟨t, hlen ▸ ht, by simpa using hc⟩

end OMA.G14W316H1b

theorem OMA.solution : OMA.R_Green14_W_3_16_R2_H1_R1.H1 := ⟨OMA.G14W316H1b.col, OMA.G14W316H1b.good⟩
