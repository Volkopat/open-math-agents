import OMAReductions.R_oeis_a085495_R1

-- Credit: @AlfredMelson
/-!
In the five small even dimensions, separate the construction of the large rational
matrix groups from the upper bounds for determinant-one groups. The GL orders
are the entries of OEIS A085495. The existing determinant-kernel lemma supplies
both the missing SL witnesses and the upper bounds for GL.
-/

namespace OMA.R_oeis_a085495_R1_H1_R1

open Matrix OMA.S_oeis_a085495

/-- Construct a rational matrix group of the tabulated order in each dimension. -/
def H1 : Prop := ∀ n b : ℕ, (n,b) ∈ [(2,6), (4,576), (6,51840), (8,348364800), (10,4180377600)] →
  ∃ G : Subgroup (GL (Fin n) ℚ), Finite G ∧ Nat.card G = 2 * b

/-- Bound every finite rational determinant-one group in the five dimensions. -/
def H2 : Prop := ∀ n b : ℕ, (n,b) ∈ [(2,6), (4,576), (6,51840), (8,348364800), (10,4180377600)] →
  ∀ H : Subgroup (SpecialLinearGroup (Fin n) ℚ), Finite H → Nat.card H ≤ b

theorem main : H1 → H2 → OMA.R_oeis_a085495_R1.H1 := by
  intro construct bound n he hlo hhi
  obtain ⟨b, entry⟩ : ∃ b : ℕ, (n,b) ∈ [(2,6), (4,576), (6,51840), (8,348364800), (10,4180377600)] := by
    obtain ⟨k, rfl⟩ := he
    have hk : k ≤ 5 := by omega
    interval_cases k <;> simp_all <;> norm_num at *
  set A := {k : ℕ | ∃ G : Subgroup (GL (Fin n) ℚ), Finite G ∧ Nat.card G = k}
  set B := {k : ℕ | ∃ H : Subgroup (SpecialLinearGroup (Fin n) ℚ), Finite H ∧ Nat.card H = k}
  have capB : ∀ k ∈ B, k ≤ b := by
    rintro _ ⟨H, hH, rfl⟩
    exact bound n b entry H hH
  have capA : ∀ k ∈ A, k ≤ 2 * b := by
    rintro _ ⟨G, hG, rfl⟩
    obtain ⟨H, hH, hle⟩ := OMA.R_oeis_a085495_R1.halve G
    exact hle.trans (Nat.mul_le_mul_left 2 (bound n b entry H hH))
  obtain ⟨G, hG, hsize⟩ := construct n b entry
  obtain ⟨H, hH, hle⟩ := OMA.R_oeis_a085495_R1.halve G
  have hub := bound n b entry H hH
  have topB : b ∈ B := ⟨H, hH, by omega⟩
  have topA : 2 * b ∈ A := ⟨G, hG, hsize⟩
  change 2 * sSup B = sSup A
  rw [show sSup B = b from
        le_antisymm (csSup_le ⟨_, topB⟩ capB) (le_csSup ⟨_, capB⟩ topB),
      show sSup A = 2 * b from
        le_antisymm (csSup_le ⟨_, topA⟩ capA) (le_csSup ⟨_, capA⟩ topA)]

end OMA.R_oeis_a085495_R1_H1_R1
