import OMAStatements.S_oeis_a390007
import Mathlib.Tactic.Linarith

-- Problem: A390007 (Rodrigo): for every integer n ≥ 3, the square of side n has a unique minimum-defect
--   set of three distinct rectangular tiles, except n = 4.
-- First proof: @alan-phobos-claude (the mathematics below is theirs). Shorter version.
-- The optimum is the tee `S n` with a = ⌊(n+1)/3⌋ and b = ⌊(n−1)/2⌋. Writing n = 6q + r, its defect is at
--   most D = 8q, 5q+1, 8q+2, 4q+2, 8q+6, 5q+4 for r = 0, …, 5. A tee (a, b) with defect at most D has the
--   optimal b (otherwise n − 2b ≥ c with c = 4 for even n, 3 for odd n, which is impossible), and then the
--   optimal a. Strips cost n(z − x) ≥ 2n > D. At n = 4 the tees (1, 1) and (2, 1) tie with defect 6.
-- All six residue classes are treated by one argument: the constants are substituted once.

open OMA.S_oeis_a390007

def S (n : ℤ) : TileSet := .tee ((n + 1) / 3) ((n - 1) / 2)

lemma K (n : ℤ) (hn : 3 ≤ n) : defect n (S n) < 2 * n ∧
    ∀ a b, valid n (.tee a b) → n ≠ 4 → defect n (.tee a b) ≤ defect n (S n) →
      a = (n + 1) / 3 ∧ b = (n - 1) / 2 := by
  simp only [defect, S, valid]
  generalize hA : (n + 1) / 3 = A
  generalize hB : (n - 1) / 2 = B
  obtain ⟨q, D, c, k, h⟩ : ∃ q D c k : ℤ,
      D = 8*q ∧ c = 4 ∧ k = 1 ∧ n = 6*q ∧ A = 2*q ∧ B = 3*q-1 ∨
      D = 5*q+1 ∧ c = 3 ∧ k = 1 ∧ n = 6*q+1 ∧ A = 2*q ∧ B = 3*q ∨
      D = 8*q+2 ∧ c = 4 ∧ k = 1 ∧ n = 6*q+2 ∧ A = 2*q+1 ∧ B = 3*q ∨
      D = 4*q+2 ∧ c = 3 ∧ k = 0 ∧ n = 6*q+3 ∧ A = 2*q+1 ∧ B = 3*q+1 ∨
      D = 8*q+6 ∧ c = 4 ∧ k = 1 ∧ n = 6*q+4 ∧ A = 2*q+1 ∧ B = 3*q+1 ∨
      D = 5*q+4 ∧ c = 3 ∧ k = 0 ∧ n = 6*q+5 ∧ A = 2*q+2 ∧ B = 3*q+2 := by
    rcases (by omega : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5) with
      r | r | r | r | r | r <;> exact ⟨n / 6, _, _, _, by
        repeat (first | ((try left); exact ⟨rfl, rfl, rfl, by omega⟩) | right)⟩
  clear hA hB
  have d : spread (n * A) (B * (n - A)) ((n - B) * (n - A)) ≤ D := by
    refine max_le ?_ (max_le ?_ ?_) <;> casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> nlinarith
  refine ⟨by omega, fun a b w h4 hd => ?_⟩
  have e := hd.trans d
  simp only [spread, max_le_iff] at e
  have x : k ≤ q := by omega
  have z : (0:ℤ) ≤ q := by omega
  have y : (0:ℤ) ≤ n := by omega
  have m : (0:ℤ) ≤ n - a := by omega
  have g : b ≠ B → (0:ℤ) ≤ n - 2*b - c := fun i => by omega
  have t : b ≠ B → c * (n - a) ≤ D := fun i => by nlinarith [mul_nonneg (g i) m, e.1]
  have o : ¬ b ≠ B → b = B := not_not.1
  casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;>
    (have hb := o fun i => by
       nlinarith [mul_nonneg y (sub_nonneg.2 (t i)), mul_nonneg (g i) m, mul_self_nonneg q]
     subst hb
     exact ⟨le_antisymm (not_lt.1 fun j => by nlinarith [mul_nonneg (sub_nonneg.2 j) z])
       (not_lt.1 fun j => by nlinarith [mul_nonneg (sub_nonneg.2 j) z]), rfl⟩)

lemma F (a : ℤ) (ha : a = 1 ∨ a = 2) : optimal 4 (.tee a 1) := by
  refine ⟨by simp only [valid]; omega, fun t ht => ?_⟩
  cases t with
  | strips x y z => simp only [valid] at ht; omega
  | tee c d =>
    simp only [valid] at ht
    obtain rfl : d = 1 := by omega
    rcases ha with rfl | rfl <;> rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl <;> decide

theorem OMA.solution : type_of% @OMA.S_oeis_a390007.main := by
  intro n hn
  obtain ⟨l, u⟩ := K n hn
  have v : valid n (S n) := by simp only [S, valid]; omega
  have g : n ≠ 4 → ∀ t, valid n t → t ≠ S n → defect n (S n) < defect n t := by
    intro h4 t ht hne
    cases t with
    | strips x y z =>
      simp only [valid] at ht
      rw [show defect n (.strips x y z) = n * (z - x) from rfl]
      nlinarith [mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ z - x by omega) (show (0:ℤ) ≤ n by omega)]
    | tee a b =>
      by_contra hle
      obtain ⟨rfl, rfl⟩ := u a b ht h4 (not_lt.1 hle)
      exact hne rfl
  constructor
  · rintro ⟨s, -, hu⟩ rfl
    cases (hu _ (F 1 (.inl rfl))).trans (hu _ (F 2 (.inr rfl))).symm
  · intro h4
    refine ⟨S n, ⟨v, fun t ht => ?_⟩, fun s hs => ?_⟩
    · by_cases he : t = S n
      · rw [he]
      · exact (g h4 t ht he).le
    · by_contra hne
      exact absurd (hs.2 _ v) (not_le.2 (g h4 s hs.1 hne))
