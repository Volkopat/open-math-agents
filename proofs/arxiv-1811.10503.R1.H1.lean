import OMAReductions.R_arxiv_1811_10503_R1
import Mathlib

/-! In a linearly ordered commutative group, enumerate `A` so that the element of largest absolute
value `|·|ₘ` comes last, inductively. If `x ^ (m+1) = b ^ (i+1)` with `i < m` and `|b|ₘ ≤ |x|ₘ`,
then `|x|ₘ ^ (m+1) = |b|ₘ ^ (i+1) ≤ |x|ₘ ^ (i+1)`, so `|x|ₘ = 1`, hence `x = 1 = b`. -/

theorem OMA.solution : OMA.R_arxiv_1811_10503_R1.H1 := by
  intro G _ _ _ n A hA
  classical
  subst hA
  induction A using Finset.induction_on_max_value (fun x : G => |x|ₘ) with
  | empty =>
    rw [Finset.card_empty]
    exact ⟨Fin.elim0, fun i => i.elim0, by simp, fun i => i.elim0⟩
  | insert x s hx hmax ih =>
    obtain ⟨b, hb, hbr, hbp⟩ := ih
    have memb : ∀ j, b j ∈ s := fun j => by
      have : b j ∈ Set.range b := ⟨j, rfl⟩
      rw [hbr] at this; exact this
    have last_ne : ∀ j : Fin s.card, x ^ (s.card + 1) ≠ b j ^ (j.val + 1) := by
      intro j h
      have h1 := congrArg (fun z => |z|ₘ) h
      simp only [mabs_pow] at h1
      have hle : |b j|ₘ ≤ |x|ₘ := hmax _ (memb j)
      rcases (one_le_mabs x).lt_or_eq with hx1 | hx1
      · have l1 : |x|ₘ ^ (j.val + 1) < |x|ₘ ^ (s.card + 1) := pow_lt_pow_right' hx1 (by omega)
        have l2 : |b j|ₘ ^ (j.val + 1) ≤ |x|ₘ ^ (j.val + 1) := pow_le_pow_left' hle _
        exact absurd h1 (ne_of_gt (lt_of_le_of_lt l2 l1))
      · have hx1' : x = 1 := mabs_eq_one.mp hx1.symm
        have hb1 : b j = 1 := mabs_eq_one.mp (le_antisymm (hx1 ▸ hle) (one_le_mabs _))
        exact hx (hx1' ▸ hb1 ▸ memb j)
    rw [Finset.card_insert_of_notMem hx]
    refine ⟨Fin.snoc (α := fun _ => G) b x, ?_, ?_, ?_⟩
    · intro i j h
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
      · rfl
      · exact absurd (h ▸ memb _) hx
      · exact absurd (h ▸ memb _) hx
      · exact congrArg _ (hb h)
    · ext y
      simp only [Set.mem_range, Finset.coe_insert, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, rfl⟩
        induction i using Fin.lastCases
        · simp
        · right; simpa using memb _
      · rintro (rfl | hy)
        · exact ⟨Fin.last _, by simp⟩
        · have : y ∈ Set.range b := by rw [hbr]; exact hy
          obtain ⟨j, rfl⟩ := this
          exact ⟨j.castSucc, by simp⟩
    · intro i j h
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.coe_castSucc] at h
      · rfl
      · exact absurd h (last_ne _)
      · exact absurd h.symm (last_ne _)
      · exact congrArg _ (hbp h)
