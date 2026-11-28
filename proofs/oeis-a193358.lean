import OMAStatements.S_oeis_a193358
import Mathlib
open OMA.S_oeis_a193358
def OMA.g193 (n : ℕ) : ℕ :=
  if n - ((Nat.sqrt (4*n+1) - 1)/2)*((Nat.sqrt (4*n+1) - 1)/2+1) = 2*((Nat.sqrt (4*n+1) - 1)/2)
  then 2*((Nat.sqrt (4*n+1) - 1)/2)+1 else 2*((Nat.sqrt (4*n+1) - 1)/2)+2
theorem OMA.g193_eq (k i : ℕ) (hi : i < 2*k+2) :
    OMA.g193 (k*(k+1)+i) = if i = 2*k then 2*k+1 else 2*k+2 := by
  have hs : (Nat.sqrt (4*(k*(k+1)+i)+1) - 1)/2 = k := by
    have h1 : 2*k+1 ≤ Nat.sqrt (4*(k*(k+1)+i)+1) := Nat.le_sqrt.2 (by nlinarith)
    have h2 : Nat.sqrt (4*(k*(k+1)+i)+1) < 2*k+3 := Nat.sqrt_lt.2 (by nlinarith)
    omega
  unfold OMA.g193
  rw [hs, Nat.add_sub_cancel_left]
theorem OMA.g193_dec (n : ℕ) : ∃ k i, i < 2*k+2 ∧ n = k*(k+1)+i := by
  induction n with
  | zero => exact ⟨0, 0, by omega, by ring⟩
  | succ n ih =>
    obtain ⟨k, i, hi, rfl⟩ := ih
    by_cases h : i + 1 < 2*k+2
    · exact ⟨k, i+1, h, by ring⟩
    · exact ⟨k+1, 0, by omega, by
        have : i = 2*k+1 := by omega
        subst this; ring⟩
theorem OMA.g193_pos (n : ℕ) : 1 ≤ OMA.g193 n := by
  obtain ⟨k, i, hi, rfl⟩ := OMA.g193_dec n
  rw [OMA.g193_eq k i hi]; split_ifs <;> omega
theorem OMA.g193_rec (n : ℕ) (hn : 2 ≤ n) :
    OMA.g193 n = OMA.g193 (n - OMA.g193 (n - 2)) + 2 := by
  obtain ⟨k, i, hi, rfl⟩ := OMA.g193_dec n
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
    rcases k with _ | k
    · simp at hn; omega
    · omega⟩
  have hk : (j+1)*(j+1+1) = j*(j+1) + 2*j + 2 := by ring
  have L := OMA.g193_eq (j+1) i hi
  rcases Nat.lt_or_ge i 2 with h | h
  · have e0 := OMA.g193_eq j (2*j) (by omega)
    have e1 := OMA.g193_eq j (2*j+1) (by omega)
    have e2 := OMA.g193_eq j 1 (by omega)
    rw [if_neg (show i ≠ 2*(j+1) by omega)] at L
    rw [if_pos rfl] at e0
    rw [if_neg (show 2*j+1 ≠ 2*j by omega)] at e1
    rw [if_neg (show 1 ≠ 2*j by omega)] at e2
    rw [hk] at L ⊢
    generalize j*(j+1) = P at *
    rw [L]
    interval_cases i
    · rw [show P+2*j+2+0-2 = P+2*j by omega, e0, show P+2*j+2+0-(2*j+1) = P+1 by omega, e2]; omega
    · rw [show P+2*j+2+1-2 = P+(2*j+1) by omega, e1, show P+2*j+2+1-(2*j+2) = P+1 by omega, e2]; omega
  · have L2 := OMA.g193_eq (j+1) (i-2) (by omega)
    have e3 := OMA.g193_eq j (i-2) (by omega)
    rw [if_neg (show i-2 ≠ 2*(j+1) by omega)] at L2
    rw [hk] at L L2 ⊢
    generalize j*(j+1) = P at *
    rw [L, show P+2*j+2+i-2 = P+2*j+2+(i-2) by omega, L2,
      show P+2*j+2+i-(2*(j+1)+2) = P+(i-2) by omega, e3]
    split_ifs <;> omega
theorem OMA.g193_unique (f : ℕ → ℕ) (hf : IsA193358 f) : ∀ n, f n = OMA.g193 n := by
  obtain ⟨h0, h1, hr⟩ := hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · rw [h0, show (0:ℕ) = 0*(0+1)+0 by rfl, OMA.g193_eq 0 0 (by omega)]; rfl
      · rw [h1, show (1:ℕ) = 0*(0+1)+1 by rfl, OMA.g193_eq 0 1 (by omega)]; rfl
    · rw [hr n h, ih (n-2) (by omega), ih _ (by have := OMA.g193_pos (n-2); omega),
        ← OMA.g193_rec n h]
theorem OMA.solution : type_of% @OMA.S_oeis_a193358.main := by
  refine ⟨⟨OMA.g193, ?_, ?_, fun n hn => OMA.g193_rec n hn⟩, ?_⟩
  · rw [show (0:ℕ) = 0*(0+1)+0 by rfl, OMA.g193_eq 0 0 (by omega)]; rfl
  · rw [show (1:ℕ) = 0*(0+1)+1 by rfl, OMA.g193_eq 0 1 (by omega)]; rfl
  intro f hf
  have hfg := OMA.g193_unique f hf
  simp only [hfg]
  refine ⟨?_, ?_⟩
  · intro k hk
    obtain ⟨j, hj⟩ : ∃ j, k = 2*j+1 ∨ k = 2*j+2 := ⟨(k-1)/2, by omega⟩
    rcases hj with rfl | rfl
    · exact ⟨j*(j+1)+2*j, by rw [OMA.g193_eq j (2*j) (by omega), if_pos rfl]⟩
    · exact ⟨j*(j+1)+(2*j+1), by rw [OMA.g193_eq j (2*j+1) (by omega), if_neg (by omega)]⟩
  · have key : ∀ m, OMA.g193 m % 2 = 1 → m = ((OMA.g193 m - 1)/2) * ((OMA.g193 m - 1)/2 + 1)
        + 2 * ((OMA.g193 m - 1)/2) := by
      intro m hm
      obtain ⟨k, i, hi, rfl⟩ := OMA.g193_dec m
      rw [OMA.g193_eq k i hi] at hm ⊢
      split_ifs at hm ⊢ with h
      · subst h
        rw [show (2*k+1-1)/2 = k by omega]
      · omega
    intro m n hmn hm
    rw [key m hm, key n (hmn ▸ hm), hmn]
