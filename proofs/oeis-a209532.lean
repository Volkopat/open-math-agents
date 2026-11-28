import OMAStatements.S_oeis_a209532
import Mathlib.Tactic

namespace OMA.P_oeis_a209532

open OMA.S_oeis_a209532

private lemma validBlock_iff (a b c d : Fin 3) :
    validBlock a b c d ↔
      (a = 0 ∧ b = 2 ∧ c = 2 ∧ d = 0) ∨
      (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 2) ∨
      (a = 1 ∧ d = 1 ∧ b ≠ 1 ∧ c ≠ 1) ∨
      (b = 1 ∧ c = 1 ∧ a ≠ 1 ∧ d ≠ 1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private def isValid (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 6),
    validBlock (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
      (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩))

private instance (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Decidable (isValid n A) := by
  unfold isValid; infer_instance

private def isChecker02 (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Prop :=
  (∀ p : Fin (n + 1) × Fin 7, A p = if Even (p.1.1 + p.2.1) then 0 else 2) ∨
  (∀ p : Fin (n + 1) × Fin 7, A p = if Even (p.1.1 + p.2.1) then 2 else 0)

private def isEvenOne (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Prop :=
  ∀ p : Fin (n + 1) × Fin 7, if Even (p.1.1 + p.2.1) then A p = 1 else A p ≠ 1

private def isOddOne (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Prop :=
  ∀ p : Fin (n + 1) × Fin 7, if Even (p.1.1 + p.2.1) then A p ≠ 1 else A p = 1

private instance (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Decidable (isChecker02 n A) := by
  unfold isChecker02; infer_instance
private instance (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Decidable (isEvenOne n A) := by
  unfold isEvenOne; infer_instance
private instance (n : ℕ) (A : Fin (n + 1) × Fin 7 → Fin 3) : Decidable (isOddOne n A) := by
  unfold isOddOne; infer_instance

private lemma isValid_iff (n : ℕ) (hn : 1 ≤ n) (A : Fin (n + 1) × Fin 7 → Fin 3) :
    isValid n A ↔ isChecker02 n A ∨ isEvenOne n A ∨ isOddOne n A := by
  constructor
  · intro hA
    -- Block-level propagation helpers
    have h00 := (validBlock_iff _ _ _ _).mp (hA ⟨0, by omega⟩ ⟨0, by omega⟩)
    rcases h00 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hd, hb, hc⟩ | ⟨hb, hc, ha, hd⟩
    · -- Case 1: B(0,0) = (0, 2, 2, 0) => checker0
      left; left
      have hblock : ∀ (i : Fin n) (j : Fin 6),
          A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩) = (if Even (i.1 + j.1) then 0 else 2) ∧
          A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩) = (if Even (i.1 + j.1) then 2 else 0) ∧
          A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩) = (if Even (i.1 + j.1) then 2 else 0) ∧
          A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩) = (if Even (i.1 + j.1) then 0 else 2) := by
        intro ⟨i, hi⟩ ⟨j, hj⟩
        induction i with
        | zero =>
          induction j with
          | zero => dsimp at ha hb hc hd ⊢; exact ⟨ha, hb, hc, hd⟩
          | succ j ih =>
            have hprev := ih (by omega)
            have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨0, by omega⟩ ⟨j + 1, hj⟩)
            by_cases hev : Even (0 + j)
            · have ho : ¬ Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_pos hev] at hprev
              simp only [if_neg ho]
              rcases hprev with ⟨_, h1, _, h2⟩
              rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨_, c3, _, _⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · exact ⟨c1, c2, c3, c4⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h2] at c3; exact absurd c3 (by decide)
            · have he : Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_neg hev] at hprev
              simp only [if_pos he]
              rcases hprev with ⟨_, h1, _, h2⟩
              rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨_, c3, _, _⟩
              · exact ⟨c1, c2, c3, c4⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h2] at c3; exact absurd c3 (by decide)
        | succ i ih =>
          have hprev := ih (by omega)
          have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨i + 1, hi⟩ ⟨j, hj⟩)
          by_cases hev : Even (i + j)
          · have ho : ¬ Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at hprev
            simp only [if_neg ho]
            rcases hprev with ⟨_, _, h1, h2⟩
            rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨c2, _, _, _⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · exact ⟨c1, c2, c3, c4⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h2] at c2; exact absurd c2 (by decide)
          · have he : Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at hprev
            simp only [if_pos he]
            rcases hprev with ⟨_, _, h1, h2⟩
            rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨c2, _, _, _⟩
            · exact ⟨c1, c2, c3, c4⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h2] at c2; exact absurd c2 (by decide)
      intro ⟨x, y⟩
      by_cases hx : x.1 < n
      · by_cases hy : y.1 < 6
        · exact (hblock ⟨x.1, hx⟩ ⟨y.1, hy⟩).1
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := (hblock ⟨x.1, hx⟩ ⟨5, by omega⟩).2.1
          by_cases hev : Even (x.1 + 5)
          · have ho : ¬ Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, ho] using h
          · have he : Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, he] using h
      · have hxn : x = ⟨n, by omega⟩ := Fin.ext (by have := x.isLt; dsimp; omega)
        rw [hxn]
        have hi : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by dsimp; omega)
        by_cases hy : y.1 < 6
        · have h := (hblock ⟨n - 1, by omega⟩ ⟨y.1, hy⟩).2.2.1
          rw [hi] at h
          by_cases hev : Even (n - 1 + y.1)
          · have ho : ¬ Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, ho] using h
          · have he : Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, he] using h
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := (hblock ⟨n - 1, by omega⟩ ⟨5, by omega⟩).2.2.2
          rw [hi] at h
          by_cases hev : Even (n - 1 + 5)
          · have he : Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, he] using h
          · have ho : ¬ Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, ho] using h
    · -- Case 2: B(0,0) = (2, 0, 0, 2) => checker2
      left; right
      have hblock : ∀ (i : Fin n) (j : Fin 6),
          A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩) = (if Even (i.1 + j.1) then 2 else 0) ∧
          A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩) = (if Even (i.1 + j.1) then 0 else 2) ∧
          A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩) = (if Even (i.1 + j.1) then 0 else 2) ∧
          A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩) = (if Even (i.1 + j.1) then 2 else 0) := by
        intro ⟨i, hi⟩ ⟨j, hj⟩
        induction i with
        | zero =>
          induction j with
          | zero => dsimp at ha hb hc hd ⊢; exact ⟨ha, hb, hc, hd⟩
          | succ j ih =>
            have hprev := ih (by omega)
            have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨0, by omega⟩ ⟨j + 1, hj⟩)
            by_cases hev : Even (0 + j)
            · have ho : ¬ Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_pos hev] at hprev
              simp only [if_neg ho]
              rcases hprev with ⟨_, h1, _, h2⟩
              rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨_, c3, _, _⟩
              · exact ⟨c1, c2, c3, c4⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h2] at c3; exact absurd c3 (by decide)
            · have he : Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_neg hev] at hprev
              simp only [if_pos he]
              rcases hprev with ⟨_, h1, _, h2⟩
              rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨_, c3, _, _⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · exact ⟨c1, c2, c3, c4⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h2] at c3; exact absurd c3 (by decide)
        | succ i ih =>
          have hprev := ih (by omega)
          have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨i + 1, hi⟩ ⟨j, hj⟩)
          by_cases hev : Even (i + j)
          · have ho : ¬ Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at hprev
            simp only [if_neg ho]
            rcases hprev with ⟨_, _, h1, h2⟩
            rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨c2, _, _, _⟩
            · exact ⟨c1, c2, c3, c4⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h2] at c2; exact absurd c2 (by decide)
          · have he : Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at hprev
            simp only [if_pos he]
            rcases hprev with ⟨_, _, h1, h2⟩
            rcases hcur with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩ | ⟨c2, _, _, _⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · exact ⟨c1, c2, c3, c4⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h2] at c2; exact absurd c2 (by decide)
      intro ⟨x, y⟩
      by_cases hx : x.1 < n
      · by_cases hy : y.1 < 6
        · exact (hblock ⟨x.1, hx⟩ ⟨y.1, hy⟩).1
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := (hblock ⟨x.1, hx⟩ ⟨5, by omega⟩).2.1
          by_cases hev : Even (x.1 + 5)
          · have ho : ¬ Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, ho] using h
          · have he : Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, he] using h
      · have hxn : x = ⟨n, by omega⟩ := Fin.ext (by have := x.isLt; dsimp; omega)
        rw [hxn]
        have hi : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by dsimp; omega)
        by_cases hy : y.1 < 6
        · have h := (hblock ⟨n - 1, by omega⟩ ⟨y.1, hy⟩).2.2.1
          rw [hi] at h
          by_cases hev : Even (n - 1 + y.1)
          · have ho : ¬ Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, ho] using h
          · have he : Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, he] using h
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := (hblock ⟨n - 1, by omega⟩ ⟨5, by omega⟩).2.2.2
          rw [hi] at h
          by_cases hev : Even (n - 1 + 5)
          · have he : Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, he] using h
          · have ho : ¬ Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simpa [hev, ho] using h
    · -- Case 3: B(0,0) has A(0,0)=1 => isEvenOne
      right; left
      have hblock : ∀ (i : Fin n) (j : Fin 6),
          if Even (i.1 + j.1) then
            A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩) = 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩) = 1 ∧
            A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩) ≠ 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩) ≠ 1
          else
            A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩) = 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩) = 1 ∧
            A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩) ≠ 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩) ≠ 1 := by
        intro ⟨i, hi⟩ ⟨j, hj⟩
        induction i with
        | zero =>
          induction j with
          | zero => dsimp at ha hb hc hd ⊢; exact ⟨ha, hd, hb, hc⟩
          | succ j ih =>
            have hprev := ih (by omega)
            have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨0, by omega⟩ ⟨j + 1, hj⟩)
            by_cases hev : Even (0 + j)
            · have ho : ¬ Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_pos hev] at hprev; simp only [if_neg ho]
              rcases hprev with ⟨_, h1, h2, _⟩
              rcases hcur with ⟨_, _, c3, _⟩ | ⟨_, _, c3, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩
              · rw [h1] at c3; exact absurd c3 (by decide)
              · rw [h1] at c3; exact absurd c3 (by decide)
              · exact (h2 c1).elim
              · exact ⟨c1, c2, c3, c4⟩
            · have he : Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_neg hev] at hprev; simp only [if_pos he]
              rcases hprev with ⟨h1, _, _, h2⟩
              rcases hcur with ⟨c1, _, _, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩ | ⟨_, c2, _, _⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h1] at c1; exact absurd c1 (by decide)
              · exact ⟨c1, c2, c3, c4⟩
              · exact (h2 c2).elim
        | succ i ih =>
          have hprev := ih (by omega)
          have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨i + 1, hi⟩ ⟨j, hj⟩)
          by_cases hev : Even (i + j)
          · have ho : ¬ Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at hprev; simp only [if_neg ho]
            rcases hprev with ⟨_, h1, _, h2⟩
            rcases hcur with ⟨_, c2, _, _⟩ | ⟨_, c2, _, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩
            · rw [h1] at c2; exact absurd c2 (by decide)
            · rw [h1] at c2; exact absurd c2 (by decide)
            · exact (h2 c1).elim
            · exact ⟨c1, c2, c3, c4⟩
          · have he : Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at hprev; simp only [if_pos he]
            rcases hprev with ⟨_, h1, _, h2⟩
            rcases hcur with ⟨c1, _, _, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h1] at c1; exact absurd c1 (by decide)
            · exact ⟨c1, c2, c3, c4⟩
            · exact (h2 c1).elim
      intro ⟨x, y⟩
      by_cases hx : x.1 < n
      · by_cases hy : y.1 < 6
        · have h := hblock ⟨x.1, hx⟩ ⟨y.1, hy⟩
          by_cases hev : Even (x.1 + y.1)
          · simp only [if_pos hev] at h ⊢; exact h.1
          · simp only [if_neg hev] at h ⊢; exact h.2.2.1
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := hblock ⟨x.1, hx⟩ ⟨5, by omega⟩
          by_cases hev : Even (x.1 + 5)
          · have ho : ¬ Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at h; simp only [if_neg ho]; exact h.2.2.1
          · have he : Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at h; simp only [if_pos he]; exact h.1
      · have hxn : x = ⟨n, by omega⟩ := Fin.ext (by have := x.isLt; dsimp; omega)
        rw [hxn]
        have hi : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by dsimp; omega)
        by_cases hy : y.1 < 6
        · have h := hblock ⟨n - 1, by omega⟩ ⟨y.1, hy⟩
          by_cases hev : Even (n - 1 + y.1)
          · have ho : ¬ Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at h; simp only [if_neg ho]; rw [← hi]; exact h.2.2.2
          · have he : Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at h; simp only [if_pos he]; rw [← hi]; exact h.2.1
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := hblock ⟨n - 1, by omega⟩ ⟨5, by omega⟩
          by_cases hev : Even (n - 1 + 5)
          · have he : Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at h; simp only [if_pos he]; rw [← hi]; exact h.2.1
          · have ho : ¬ Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at h; simp only [if_neg ho]; rw [← hi]; exact h.2.2.2
    · -- Case 4: B(0,0) has A(0,1)=1 => isOddOne
      right; right
      have hblock : ∀ (i : Fin n) (j : Fin 6),
          if Even (i.1 + j.1) then
            A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩) = 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩) = 1 ∧
            A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩) ≠ 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩) ≠ 1
          else
            A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩) = 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩) = 1 ∧
            A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩) ≠ 1 ∧
            A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩) ≠ 1 := by
        intro ⟨i, hi⟩ ⟨j, hj⟩
        induction i with
        | zero =>
          induction j with
          | zero => dsimp at ha hb hc hd ⊢; exact ⟨hb, hc, ha, hd⟩
          | succ j ih =>
            have hprev := ih (by omega)
            have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨0, by omega⟩ ⟨j + 1, hj⟩)
            by_cases hev : Even (0 + j)
            · have ho : ¬ Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_pos hev] at hprev; simp only [if_neg ho]
              rcases hprev with ⟨h1, _, _, h2⟩
              rcases hcur with ⟨c1, _, _, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩ | ⟨_, c2, _, _⟩
              · rw [h1] at c1; exact absurd c1 (by decide)
              · rw [h1] at c1; exact absurd c1 (by decide)
              · exact ⟨c1, c2, c3, c4⟩
              · exact (h2 c2).elim
            · have he : Even (0 + (j + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
              simp only [if_neg hev] at hprev; simp only [if_pos he]
              rcases hprev with ⟨_, h1, h2, _⟩
              rcases hcur with ⟨_, _, c3, _⟩ | ⟨_, _, c3, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩
              · rw [h1] at c3; exact absurd c3 (by decide)
              · rw [h1] at c3; exact absurd c3 (by decide)
              · exact (h2 c1).elim
              · exact ⟨c1, c2, c3, c4⟩
        | succ i ih =>
          have hprev := ih (by omega)
          have hcur := (validBlock_iff _ _ _ _).mp (hA ⟨i + 1, hi⟩ ⟨j, hj⟩)
          by_cases hev : Even (i + j)
          · have ho : ¬ Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at hprev; simp only [if_neg ho]
            rcases hprev with ⟨_, h1, _, h2⟩
            rcases hcur with ⟨c1, _, _, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, _, _, _⟩
            · rw [h1] at c1; exact absurd c1 (by decide)
            · rw [h1] at c1; exact absurd c1 (by decide)
            · exact ⟨c1, c2, c3, c4⟩
            · exact (h2 c1).elim
          · have he : Even (i + 1 + j) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at hprev; simp only [if_pos he]
            rcases hprev with ⟨_, h1, _, h2⟩
            rcases hcur with ⟨_, c2, _, _⟩ | ⟨_, c2, _, _⟩ | ⟨c1, _, _, _⟩ | ⟨c1, c2, c3, c4⟩
            · rw [h1] at c2; exact absurd c2 (by decide)
            · rw [h1] at c2; exact absurd c2 (by decide)
            · exact (h2 c1).elim
            · exact ⟨c1, c2, c3, c4⟩
      intro ⟨x, y⟩
      by_cases hx : x.1 < n
      · by_cases hy : y.1 < 6
        · have h := hblock ⟨x.1, hx⟩ ⟨y.1, hy⟩
          by_cases hev : Even (x.1 + y.1)
          · simp only [if_pos hev] at h ⊢; exact h.2.2.1
          · simp only [if_neg hev] at h ⊢; exact h.1
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := hblock ⟨x.1, hx⟩ ⟨5, by omega⟩
          by_cases hev : Even (x.1 + 5)
          · have ho : ¬ Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at h; simp only [if_neg ho]; exact h.1
          · have he : Even (x.1 + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at h; simp only [if_pos he]; exact h.2.2.1
      · have hxn : x = ⟨n, by omega⟩ := Fin.ext (by have := x.isLt; dsimp; omega)
        rw [hxn]
        have hi : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by dsimp; omega)
        by_cases hy : y.1 < 6
        · have h := hblock ⟨n - 1, by omega⟩ ⟨y.1, hy⟩
          by_cases hev : Even (n - 1 + y.1)
          · have ho : ¬ Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at h; simp only [if_neg ho]; rw [← hi]; exact h.2.1
          · have he : Even (n + y.1) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at h; simp only [if_pos he]; rw [← hi]; exact h.2.2.2
        · have hy4 : y = ⟨6, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
          rw [hy4]
          have h := hblock ⟨n - 1, by omega⟩ ⟨5, by omega⟩
          by_cases hev : Even (n - 1 + 5)
          · have he : Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_pos hev] at h; simp only [if_pos he]; rw [← hi]; exact h.2.2.2
          · have ho : ¬ Even (n + 6) := by rw [Nat.even_iff] at hev ⊢; omega
            simp only [if_neg hev] at h; simp only [if_neg ho]; rw [← hi]; exact h.2.1
  · rintro ((h0 | h2) | he | ho) i j
    · rw [validBlock_iff]
      have ha := h0 (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)
      have hb := h0 (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      have hc := h0 (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)
      have hd := h0 (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      by_cases hev : Even (i.1 + j.1)
      · have h1 : ¬ Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : ¬ Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_pos hev, if_neg h1, if_neg h2, if_pos h3] at ha hb hc hd
        exact Or.inl ⟨ha, hb, hc, hd⟩
      · have h1 : Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : ¬ Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_neg hev, if_pos h1, if_pos h2, if_neg h3] at ha hb hc hd
        exact Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)
    · rw [validBlock_iff]
      have ha := h2 (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)
      have hb := h2 (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      have hc := h2 (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)
      have hd := h2 (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      by_cases hev : Even (i.1 + j.1)
      · have h1 : ¬ Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : ¬ Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_pos hev, if_neg h1, if_neg h2, if_pos h3] at ha hb hc hd
        exact Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)
      · have h1 : Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : ¬ Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_neg hev, if_pos h1, if_pos h2, if_neg h3] at ha hb hc hd
        exact Or.inl ⟨ha, hb, hc, hd⟩
    · rw [validBlock_iff]
      have ha := he (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)
      have hb := he (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      have hc := he (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)
      have hd := he (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      by_cases hev : Even (i.1 + j.1)
      · have h1 : ¬ Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : ¬ Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_pos hev, if_neg h1, if_neg h2, if_pos h3] at ha hb hc hd
        exact Or.inr (Or.inr (Or.inl ⟨ha, hd, hb, hc⟩))
      · have h1 : Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : ¬ Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_neg hev, if_pos h1, if_pos h2, if_neg h3] at ha hb hc hd
        exact Or.inr (Or.inr (Or.inr ⟨hb, hc, ha, hd⟩))
    · rw [validBlock_iff]
      have ha := ho (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)
      have hb := ho (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      have hc := ho (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)
      have hd := ho (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)
      by_cases hev : Even (i.1 + j.1)
      · have h1 : ¬ Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : ¬ Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_pos hev, if_neg h1, if_neg h2, if_pos h3] at ha hb hc hd
        exact Or.inr (Or.inr (Or.inr ⟨hb, hc, ha, hd⟩))
      · have h1 : Even (i.1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2 : Even (i.1 + 1 + j.1) := by rw [Nat.even_iff] at hev ⊢; omega
        have h3 : ¬ Even (i.1 + 1 + (j.1 + 1)) := by rw [Nat.even_iff] at hev ⊢; omega
        simp only [if_neg hev, if_pos h1, if_pos h2, if_neg h3] at ha hb hc hd
        exact Or.inr (Or.inr (Or.inl ⟨ha, hd, hb, hc⟩))

private lemma card_checker02 (n : ℕ) :
    (Finset.univ.filter (isChecker02 n)).card = 2 := by
  let A0 : Fin (n + 1) × Fin 7 → Fin 3 := fun p => if Even (p.1.1 + p.2.1) then 0 else 2
  let A2 : Fin (n + 1) × Fin 7 → Fin 3 := fun p => if Even (p.1.1 + p.2.1) then 2 else 0
  have hne : A0 ≠ A2 := fun h => by
    have := congrFun h (0, 0); simp [A0, A2] at this
  have heq : Finset.univ.filter (isChecker02 n) = {A0, A2} := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    unfold isChecker02
    constructor
    · rintro (h | h)
      · exact Or.inl (funext h)
      · exact Or.inr (funext h)
    · rintro (rfl | rfl)
      · exact Or.inl (fun _ => rfl)
      · exact Or.inr (fun _ => rfl)
  rw [heq, Finset.card_pair hne]

private lemma card_even_cells (n : ℕ) :
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => Even (p.1.1 + p.2.1))).card =
      if Even n then 7 * (n / 2) + 4 else 7 * ((n + 1) / 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsplit : (Finset.univ.filter (fun p : Fin (n + 2) × Fin 7 => Even (p.1.1 + p.2.1))).card =
        (Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => Even (p.1.1 + p.2.1))).card +
        (Finset.univ.filter (fun j : Fin 7 => Even ((n + 1) + j.1))).card := by
      have h1 : ∀ m : ℕ,
          (Finset.univ.filter (fun p : Fin m × Fin 7 => Even (p.1.1 + p.2.1))).card =
          ∑ i : Fin m, (Finset.univ.filter (fun j : Fin 7 => Even (i.1 + j.1))).card := by
        intro m
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hp ⊢; exact hp
        · intro p1 _ p2 _ h; cases p1; cases p2; simp_all
        · intro ⟨i, j⟩ h; refine ⟨(i, j), ?_, rfl⟩
          simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter] at h ⊢; exact h
      rw [h1 (n + 2), h1 (n + 1), Fin.sum_univ_castSucc]
      rfl
    rw [hsplit, ih]
    by_cases hev : Even n
    · have ho : ¬ Even (n + 1) := by rw [Nat.even_iff] at hev ⊢; omega
      have hrow : (Finset.univ.filter (fun j : Fin 7 => Even ((n + 1) + j.1))).card = 3 := by
        have : ∀ j : Fin 7, Even ((n + 1) + j.1) ↔ ¬ Even j.1 := by
          intro j; rw [Nat.even_iff, Nat.even_iff]; rw [Nat.even_iff] at hev; omega
        simp_rw [this]; decide
      rw [if_pos hev, if_neg ho, hrow]; omega
    · have he : Even (n + 1) := by rw [Nat.even_iff] at hev ⊢; omega
      have hrow : (Finset.univ.filter (fun j : Fin 7 => Even ((n + 1) + j.1))).card = 4 := by
        have : ∀ j : Fin 7, Even ((n + 1) + j.1) ↔ Even j.1 := by
          intro j; rw [Nat.even_iff, Nat.even_iff]; rw [Nat.even_iff] at hev; omega
        simp_rw [this]; decide
      rw [if_neg hev, if_pos he, hrow]

private lemma card_odd_cells (n : ℕ) :
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => ¬ Even (p.1.1 + p.2.1))).card =
      if Even n then 7 * (n / 2) + 3 else 7 * ((n + 1) / 2) := by
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (n + 1) × Fin 7)))
    (p := fun p => Even (p.1.1 + p.2.1))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at htot
  rw [card_even_cells n] at htot
  by_cases hev : Even n
  · rw [if_pos hev] at htot ⊢; rw [Nat.even_iff] at hev; omega
  · rw [if_neg hev] at htot ⊢; rw [Nat.even_iff] at hev; omega

private lemma card_isEvenOne (n : ℕ) :
    (Finset.univ.filter (isEvenOne n)).card =
      2 ^ (Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => ¬ Even (p.1.1 + p.2.1))).card := by
  set Sodd := Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => ¬ Even (p.1.1 + p.2.1))
  have hcard : 2 ^ Sodd.card = Fintype.card ({p // p ∈ Sodd} → Bool) := by
    simp [Fintype.card_bool]
  rw [hcard, ← Finset.card_univ]
  refine Finset.card_bij (fun A _ => fun p : {p // p ∈ Sodd} => decide (A p.1 = 2)) ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro A1 h1 A2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    funext p
    have h1p := h1 p; have h2p := h2 p
    by_cases hev : Even (p.1.1 + p.2.1)
    · simp only [if_pos hev] at h1p h2p; rw [h1p, h2p]
    · simp only [if_neg hev] at h1p h2p
      have hp : p ∈ Sodd := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩
      have hval := congrFun heq ⟨p, hp⟩
      generalize hx1 : A1 p = x1 at h1p hval ⊢
      generalize hx2 : A2 p = x2 at h2p hval ⊢
      fin_cases x1 <;> fin_cases x2 <;> simp_all
  · intro f _
    let A : Fin (n + 1) × Fin 7 → Fin 3 := fun p =>
      if h : p ∈ Sodd then (if f ⟨p, h⟩ then 2 else 0) else 1
    refine ⟨A, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro p
      by_cases hev : Even (p.1.1 + p.2.1)
      · have hnot : p ∉ Sodd := by simp [Sodd]; exact hev
        simp [A, hev, hnot]
      · have hmem : p ∈ Sodd := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩
        simp only [if_neg hev, A, dif_pos hmem]
        cases f ⟨p, hmem⟩ <;> decide
    · funext ⟨p, hp⟩
      simp only [A, dif_pos hp]
      cases f ⟨p, hp⟩ <;> decide

private lemma card_isOddOne (n : ℕ) :
    (Finset.univ.filter (isOddOne n)).card =
      2 ^ (Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => Even (p.1.1 + p.2.1))).card := by
  set Seven := Finset.univ.filter (fun p : Fin (n + 1) × Fin 7 => Even (p.1.1 + p.2.1))
  have hcard : 2 ^ Seven.card = Fintype.card ({p // p ∈ Seven} → Bool) := by
    simp [Fintype.card_bool]
  rw [hcard, ← Finset.card_univ]
  refine Finset.card_bij (fun A _ => fun p : {p // p ∈ Seven} => decide (A p.1 = 2)) ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro A1 h1 A2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    funext p
    have h1p := h1 p; have h2p := h2 p
    by_cases hev : Even (p.1.1 + p.2.1)
    · simp only [if_pos hev] at h1p h2p
      have hp : p ∈ Seven := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩
      have hval := congrFun heq ⟨p, hp⟩
      generalize hx1 : A1 p = x1 at h1p hval ⊢
      generalize hx2 : A2 p = x2 at h2p hval ⊢
      fin_cases x1 <;> fin_cases x2 <;> simp_all
    · simp only [if_neg hev] at h1p h2p; rw [h1p, h2p]
  · intro f _
    let A : Fin (n + 1) × Fin 7 → Fin 3 := fun p =>
      if h : p ∈ Seven then (if f ⟨p, h⟩ then 2 else 0) else 1
    refine ⟨A, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro p
      by_cases hev : Even (p.1.1 + p.2.1)
      · have hmem : p ∈ Seven := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩
        simp only [if_pos hev, A, dif_pos hmem]
        cases f ⟨p, hmem⟩ <;> decide
      · have hnot : p ∉ Seven := fun h => hev (Finset.mem_filter.mp h).2
        simp [A, hev, hnot]
    · funext ⟨p, hp⟩
      simp only [A, dif_pos hp]
      cases f ⟨p, hp⟩ <;> decide

private lemma A209532_closed (n : ℕ) (hn : 1 ≤ n) :
    if Even n then A209532 n = 3 * 2 ^ ((7 * n) / 2 + 2) + 1
    else A209532 n = 2 ^ ((7 * (n + 1)) / 2) + 1 := by
  have hraw : (Finset.univ.filter (isValid n)).card =
      (Finset.univ.filter (isChecker02 n)).card +
      (Finset.univ.filter (isEvenOne n)).card +
      (Finset.univ.filter (isOddOne n)).card := by
    have hunion : Finset.univ.filter (isValid n) =
        (Finset.univ.filter (isChecker02 n) ∪ Finset.univ.filter (isEvenOne n)) ∪
        Finset.univ.filter (isOddOne n) := by
      ext A
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [isValid_iff n hn, or_assoc]
    have hd1 : Disjoint (Finset.univ.filter (isChecker02 n)) (Finset.univ.filter (isEvenOne n)) := by
      rw [Finset.disjoint_left]; intro A h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have he0 := h2 (0, 0); simp at he0
      rcases h1 with hc | hc <;> { have := hc (0, 0); simp [he0] at this }
    have hd2 : Disjoint (Finset.univ.filter (isChecker02 n) ∪ Finset.univ.filter (isEvenOne n))
        (Finset.univ.filter (isOddOne n)) := by
      rw [Finset.disjoint_left]; intro A h1 h2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have ho0 := h2 (0, 0); simp at ho0
      have ho1 := h2 (0, 1); simp at ho1
      rcases h1 with (hc | hc) | he
      · have := hc (0, 1); simp [ho1] at this
      · have := hc (0, 1); simp [ho1] at this
      · have := he (0, 0); simp at this; exact ho0 this
    rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hdef : A209532 n = (Finset.univ.filter (isValid n)).card / 2 := rfl
  rw [hdef, hraw, card_checker02, card_isEvenOne, card_isOddOne, card_odd_cells, card_even_cells]
  by_cases hev : Even n
  · rw [if_pos hev, if_pos hev, if_pos hev]
    have hdiv : (7 * n) / 2 = 7 * (n / 2) := by rw [Nat.even_iff] at hev; omega
    have hp2 : 2 ^ (7 * (n / 2) + 4) = 4 * 2 ^ (7 * (n / 2) + 2) := by
      rw [show 7 * (n / 2) + 4 = (7 * (n / 2) + 2) + 2 by omega, pow_add]; ring
    have hp1 : 2 ^ (7 * (n / 2) + 3) = 2 * 2 ^ (7 * (n / 2) + 2) := by
      rw [show 7 * (n / 2) + 3 = (7 * (n / 2) + 2) + 1 by omega, pow_succ]; ring
    rw [hdiv, hp2, hp1]; omega
  · rw [if_neg hev, if_neg hev, if_neg hev]
    have hdiv : (7 * (n + 1)) / 2 = 7 * ((n + 1) / 2) := by rw [Nat.even_iff] at hev; omega
    rw [hdiv]; omega

private lemma A209532_small : A209532 1 = 129 ∧ A209532 2 = 1537 ∧ A209532 3 = 16385 := by
  have h1 := A209532_closed 1 (by omega)
  have h2 := A209532_closed 2 (by omega)
  have h3 := A209532_closed 3 (by omega)
  have ho1 : ¬ Even 1 := by decide
  have he2 : Even 2 := by decide
  have ho3 : ¬ Even 3 := by decide
  simp only [ho1, he2, ho3, ↓reduceIte] at h1 h2 h3
  omega

private lemma A209532_rec (m : ℕ) :
    (A209532 (m + 4) : ℤ) = A209532 (m + 3) + 128 * A209532 (m + 2) - 128 * A209532 (m + 1) := by
  have h4 := A209532_closed (m + 4) (by omega)
  have h3 := A209532_closed (m + 3) (by omega)
  have h2 := A209532_closed (m + 2) (by omega)
  have h1 := A209532_closed (m + 1) (by omega)
  by_cases hev : Even (m + 4)
  · have h3o : ¬ Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
    have h2e : Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
    have h1o : ¬ Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
    simp only [if_pos hev, if_neg h3o, if_pos h2e, if_neg h1o] at h4 h3 h2 h1
    have hp4 : 2 ^ (7 * (m + 4) / 2 + 2) = 128 * 2 ^ (7 * (m + 2) / 2 + 2) := by
      rw [show 7 * (m + 4) / 2 + 2 = (7 * (m + 2) / 2 + 2) + 7 by omega, pow_add]; ring
    have hp3 : 2 ^ (7 * (m + 3 + 1) / 2) = 128 * 2 ^ (7 * (m + 1 + 1) / 2) := by
      rw [show 7 * (m + 3 + 1) / 2 = 7 * (m + 1 + 1) / 2 + 7 by omega, pow_add]; ring
    rw [hp4] at h4; rw [hp3] at h3
    omega
  · have h3e : Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
    have h2o : ¬ Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
    have h1e : Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
    simp only [if_neg hev, if_pos h3e, if_neg h2o, if_pos h1e] at h4 h3 h2 h1
    have hp4 : 2 ^ (7 * (m + 4 + 1) / 2) = 128 * 2 ^ (7 * (m + 2 + 1) / 2) := by
      rw [show 7 * (m + 4 + 1) / 2 = 7 * (m + 2 + 1) / 2 + 7 by omega, pow_add]; ring
    have hp3 : 2 ^ (7 * (m + 3) / 2 + 2) = 128 * 2 ^ (7 * (m + 1) / 2 + 2) := by
      rw [show 7 * (m + 3) / 2 + 2 = (7 * (m + 1) / 2 + 2) + 7 by omega, pow_add]; ring
    rw [hp4] at h4; rw [hp3] at h3
    omega

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A209532_gf :
    (1 - PowerSeries.X) * (1 - 128 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A209532 n : ℤ)) =
      PowerSeries.X * (129 + 1408 * PowerSeries.X - 1664 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A209532 n : ℤ))
  have hlhs : (1 - PowerSeries.X) * (1 - 128 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.X ^ 1 * F - PowerSeries.C 128 * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C 128 * (PowerSeries.X ^ 3 * F) := by
    have h32 : PowerSeries.C (128 : ℤ) = (128 : PowerSeries ℤ) := rfl
    rw [h32, pow_one]; ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) *
        (129 + 1408 * PowerSeries.X - 1664 * PowerSeries.X ^ 2) =
      PowerSeries.C 129 * PowerSeries.X + PowerSeries.C 1408 * PowerSeries.X ^ 2 -
      PowerSeries.C 1664 * PowerSeries.X ^ 3 := by
    have h33 : PowerSeries.C (129 : ℤ) = (129 : PowerSeries ℤ) := rfl
    have h160 : PowerSeries.C (1408 : ℤ) = (1408 : PowerSeries ℤ) := rfl
    have h224 : PowerSeries.C (1664 : ℤ) = (1664 : PowerSeries ℤ) := rfl
    rw [h33, h160, h224]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A209532_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A209532_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

end OMA.P_oeis_a209532

theorem OMA.solution : type_of% @OMA.S_oeis_a209532.main :=
  ⟨OMA.P_oeis_a209532.A209532_gf, OMA.P_oeis_a209532.A209532_closed⟩
