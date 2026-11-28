import OMAReductions.R_Green14_W_3_16_R2

/-! Centered subintervals preserve reflection symmetry and progression avoidance. -/

namespace OMA.R_Green14_W_3_16_R2_H1_R1

private def Good (n : Nat) (c : Nat → Bool) : Prop :=
  (∀ x < n, c (n - 1 - x) = c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d →
      a + ((if b then 16 else 3) - 1) * d < n →
      ∃ t < (if b then 16 else 3), c (a + t*d) = b

private theorem crop {m n : Nat} (hm : m ≤ n) (parity : m % 2 = n % 2)
    {c : Nat → Bool} (good : Good n c) : ∃ f, Good m f := by
  let offset := (n - m) / 2
  have size : n = m + 2 * offset := by dsimp [offset]; omega
  refine ⟨fun i => c (offset+i), ?_, ?_⟩
  · intro x hx
    have reflection : offset + (m - 1 - x) = n - 1 - (offset + x) := by omega
    change c (offset + (m - 1 - x)) = c (offset + x)
    rw [reflection]
    exact good.1 _ (by omega)
  · intro b a d hd fit
    obtain ⟨t, ht, htColor⟩ := good.2 b (offset+a) d hd (by omega)
    exact ⟨t, ht, by simpa only [Nat.add_assoc] using htColor⟩

def H1 : Prop := ∃ c, Good 231 c

def H2 : Prop := ∀ c, ¬ Good 233 c

theorem main : H1 → H2 → OMA.R_Green14_W_3_16_R2.H1 := by
  intro lower upper n odd
  change (∃ c, Good n c) ↔ n ≤ 231
  constructor
  · rintro ⟨c, hc⟩
    by_contra! large
    have fits : 233 ≤ n := by omega
    obtain ⟨f, hf⟩ := crop fits (by simpa using odd.symm) hc
    exact upper f hf
  · intro small
    obtain ⟨c, hc⟩ := lower
    exact crop small (by simpa using odd) hc

end OMA.R_Green14_W_3_16_R2_H1_R1