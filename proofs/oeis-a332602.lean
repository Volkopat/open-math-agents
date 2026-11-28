import OMAStatements.S_oeis_a332602
import Mathlib

open OMA.S_oeis_a332602


def cnt (H : ℤ) (L : ℕ) (h : ℤ) : ℕ := (Finset.univ.filter fun s : Fin L → Bool =>
  (∀ j ≤ L, 0 ≤ ht s j ∧ ht s j ≤ H) ∧ ht s L = h).card

def dl (b : Bool) : ℤ := if b then 1 else -1

theorem ht_snoc_le {L : ℕ} (s : Fin L → Bool) (b : Bool) (j : ℕ) (hj : j ≤ L) :
    ht (Fin.snoc s b : Fin (L + 1) → Bool) j = ht s j := by
  unfold ht
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_neg (by omega), add_zero]

theorem ht_snoc_last {L : ℕ} (s : Fin L → Bool) (b : Bool) :
    ht (Fin.snoc s b : Fin (L + 1) → Bool) (L + 1) = ht s L + dl b := by
  unfold ht dl
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_pos (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [if_pos (by omega), if_pos i.isLt]

theorem valid_snoc (H : ℤ) {L : ℕ} (s : Fin L → Bool) (b : Bool) :
    (∀ j ≤ L + 1, 0 ≤ ht (Fin.snoc s b : Fin (L + 1) → Bool) j ∧
        ht (Fin.snoc s b : Fin (L + 1) → Bool) j ≤ H) ↔
      (∀ j ≤ L, 0 ≤ ht s j ∧ ht s j ≤ H) ∧ 0 ≤ ht s L + dl b ∧ ht s L + dl b ≤ H := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← ht_snoc_le s b j hj]; exact h j (by omega)
    · rw [← ht_snoc_last]; exact h (L + 1) le_rfl
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge j (L + 1) with hl | hl
    · rw [ht_snoc_le s b j (by omega)]; exact h1 j (by omega)
    · obtain rfl : j = L + 1 := by omega
      rw [ht_snoc_last]; exact h2

theorem cnt_zero (H : ℤ) (hH : 0 ≤ H) (h : ℤ) : cnt H 0 h = if h = 0 then 1 else 0 := by
  unfold cnt
  have e : ∀ s : Fin 0 → Bool, ∀ j : ℕ, ht s j = 0 := by
    intro s j; simp [ht]
  simp only [e]
  by_cases h0 : h = 0
  · subst h0; simp [hH]
  · simp [h0, Ne.symm h0]

theorem cnt_succ (H : ℤ) (L : ℕ) (h : ℤ) :
    cnt H (L + 1) h = if 0 ≤ h ∧ h ≤ H then cnt H L (h - 1) + cnt H L (h + 1) else 0 := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  have e : ∀ (b : Bool) (s : Fin L → Bool),
      (if (∀ j ≤ L + 1, 0 ≤ ht ((Fin.snocEquiv (fun _ => Bool)) (b, s)) j ∧
          ht ((Fin.snocEquiv (fun _ => Bool)) (b, s)) j ≤ H) ∧
          ht ((Fin.snocEquiv (fun _ => Bool)) (b, s)) (L + 1) = h then 1 else 0) =
      (if ((∀ j ≤ L, 0 ≤ ht s j ∧ ht s j ≤ H) ∧ ht s L = h - dl b) ∧ (0 ≤ h ∧ h ≤ H) then 1 else 0) := by
    intro b s
    apply if_congr _ rfl rfl
    show ((∀ j ≤ L + 1, 0 ≤ ht (Fin.snoc s b : Fin (L + 1) → Bool) j ∧
        ht (Fin.snoc s b : Fin (L + 1) → Bool) j ≤ H) ∧
        ht (Fin.snoc s b : Fin (L + 1) → Bool) (L + 1) = h) ↔ _
    rw [valid_snoc, ht_snoc_last]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, by omega⟩, by omega, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by omega, by omega⟩, by omega⟩
  rw [Finset.sum_congr rfl (fun s _ => e true s), Finset.sum_congr rfl (fun s _ => e false s)]
  by_cases hh : 0 ≤ h ∧ h ≤ H
  · rw [if_pos hh]
    simp only [hh, and_true, dl]
    congr 1
  · rw [if_neg hh]
    simp only [hh, and_false, if_false, Finset.sum_const_zero, add_zero]

theorem cnt_neg (H : ℤ) (hH : 0 ≤ H) (L : ℕ) (h : ℤ) (hh : h < 0 ∨ H < h) : cnt H L h = 0 := by
  cases L with
  | zero => rw [cnt_zero H hH]; rw [if_neg (by omega)]
  | succ L => rw [cnt_succ]; rw [if_neg (by omega)]

theorem A080937_eq (n : ℕ) : (A080937 n : ℤ) = cnt 5 (2 * n) 0 := rfl
theorem A080938_eq (n : ℕ) : (A080938 n : ℤ) = cnt 7 (2 * n) 0 := rfl

theorem two_case : ∀ n : ℕ, (Msub 2 ^ n) 0 0 = A001519 n ∧ (Msub 2 ^ (n + 1)) 0 0 = A001519 (n + 1) ∧
    (Msub 2 ^ n) 1 0 = (Msub 2 ^ (n + 1)) 0 0 - (Msub 2 ^ n) 0 0 := by
  intro n
  induction n with
  | zero =>
    simp [A001519, pow_one]; decide
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have r0 : ∀ k, (Msub 2 ^ (k + 1)) 0 0 = (Msub 2 ^ k) 0 0 + (Msub 2 ^ k) 1 0 := by
      intro k; rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]; simp [Msub]
    have r1 : ∀ k, (Msub 2 ^ (k + 1)) 1 0 = (Msub 2 ^ k) 0 0 + 2 * (Msub 2 ^ k) 1 0 := by
      intro k; rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]; simp [Msub]
    refine ⟨h2, ?_, ?_⟩
    · rw [show n + 1 + 1 = n + 2 by ring, A001519, ← h1, ← h2, r0 (n + 1), r1 n]
      rw [r0 n] at h3 ⊢
      linarith
    · rw [r0 (n + 1)]; ring

theorem three_case : ∀ n : ℕ, (Msub 3 ^ n) 0 0 = cnt 5 (2 * n) 0 ∧ (Msub 3 ^ n) 1 0 = cnt 5 (2 * n) 2 ∧
    (Msub 3 ^ n) 2 0 = cnt 5 (2 * n) 4 ∧ cnt 5 (2 * n) 1 = 0 ∧ cnt 5 (2 * n) 3 = 0 ∧
    cnt 5 (2 * n) 5 = 0 := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, cnt_zero 5 (by norm_num)]
    decide
  | succ n ih =>
    obtain ⟨h0, h2, h4, h1, h3, h5⟩ := ih
    have hm : ∀ i : Fin 3, (Msub 3 ^ (n + 1)) i 0 = ∑ k : Fin 3, Msub 3 i k * (Msub 3 ^ n) k 0 := by
      intro i; rw [pow_succ', Matrix.mul_apply]
    have e2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e2]
    simp only [cnt_succ]
    norm_num
    have n1 : cnt 5 (2 * n) (-1) = 0 := cnt_neg 5 (by norm_num) _ _ (by norm_num)
    have n6 : cnt 5 (2 * n) 6 = 0 := cnt_neg 5 (by norm_num) _ _ (by norm_num)
    refine ⟨?_, ?_, ?_, ⟨⟨n1, h1⟩, h1, h3⟩, ⟨h1, h3⟩, h3, h5⟩
    · rw [hm 0]; simp [Fin.sum_univ_three, Msub]; rw [h0, h2]
    · rw [hm 1]; simp [Fin.sum_univ_three, Msub]; rw [h0, h2, h4]; ring
    · rw [hm 2]; simp [Fin.sum_univ_three, Msub]; rw [h2, h4, n6]; push_cast; ring

theorem four_case : ∀ n : ℕ, (Msub 4 ^ n) 0 0 = cnt 7 (2 * n) 0 ∧ (Msub 4 ^ n) 1 0 = cnt 7 (2 * n) 2 ∧
    (Msub 4 ^ n) 2 0 = cnt 7 (2 * n) 4 ∧ (Msub 4 ^ n) 3 0 = cnt 7 (2 * n) 6 ∧
    cnt 7 (2 * n) 1 = 0 ∧ cnt 7 (2 * n) 3 = 0 ∧ cnt 7 (2 * n) 5 = 0 ∧ cnt 7 (2 * n) 7 = 0 := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, cnt_zero 7 (by norm_num)]
    decide
  | succ n ih =>
    obtain ⟨h0, h2, h4, h6, h1, h3, h5, h7⟩ := ih
    have hm : ∀ i : Fin 4, (Msub 4 ^ (n + 1)) i 0 = ∑ k : Fin 4, Msub 4 i k * (Msub 4 ^ n) k 0 := by
      intro i; rw [pow_succ', Matrix.mul_apply]
    have e2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e2]
    simp only [cnt_succ]
    norm_num
    have n1 : cnt 7 (2 * n) (-1) = 0 := cnt_neg 7 (by norm_num) _ _ (by norm_num)
    have n8 : cnt 7 (2 * n) 8 = 0 := cnt_neg 7 (by norm_num) _ _ (by norm_num)
    simp only [n1, n8, h1, h3, h5, h7, and_self, and_true, Nat.cast_zero, add_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hm 0]; simp [Fin.sum_univ_four, Msub]; rw [h0, h2]
    · rw [hm 1]; simp [Fin.sum_univ_four, Msub]; rw [h0, h2, h4]; ring
    · rw [hm 2]; simp [Fin.sum_univ_four, Msub]; rw [h2, h4, h6]; ring
    · rw [hm 3]; simp [Fin.sum_univ_four, Msub]; rw [h4, h6]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a332602.main := by
  intro n
  exact ⟨(two_case n).1, by rw [A080937_eq]; exact (three_case n).1,
    by rw [A080938_eq]; exact (four_case n).1⟩
