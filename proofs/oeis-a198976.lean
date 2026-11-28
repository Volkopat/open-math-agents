import OMAStatements.S_oeis_a198976
import Mathlib

/-!
# oeis-a198976: closed form for the proper two-column arrays with at most 6 colors

For distinct `a, b < t + 2` the value `extensions 6 n t a b` depends only on `t`: every sum in
the recursion runs over a set whose size depends only on `t`, and its terms are again values at
distinct pairs. By induction on `n` the five values are `21^n` (`t = 4` and `t = 3`),
`(21^n + 7^n) / 2` (`t = 2`), `21^n / 6 + 7^n / 2 + 3^n / 3` (`t = 1`) and
`21^n / 24 + 7^n / 4 + 3^n / 3 + 3 / 8` (`t = 0`). The last one gives
Barker's closed form, and the recurrence follows from it.

Source: OEIS A198976, https://oeis.org/A198976.
-/
namespace OMA.P_oeis_a198976

open OMA.S_oeis_a198976 Finset

lemma sum1 (k b : ℕ) (hb : b < k) (F : ℕ → ℚ) (c : ℚ) (h : ∀ y, y < k → y ≠ b → F y = c) :
    ∑ y ∈ (range k).erase b, F y = ((k : ℚ) - 1) * c := by
  rw [Finset.sum_congr rfl fun y hy => h y (mem_range.1 (mem_of_mem_erase hy)) (ne_of_mem_erase hy)]
  rw [sum_const, card_erase_of_mem (mem_range.2 hb), card_range, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma sum2 (k a b : ℕ) (ha : a < k) (hb : b < k) (hab : a ≠ b) (F : ℕ → ℕ → ℚ) (c : ℚ)
    (h : ∀ x y, x < k → y < k → x ≠ y → F x y = c) :
    ∑ x ∈ ((range k).erase a).erase b, ∑ y ∈ ((range k).erase b).erase x, F x y =
      ((k : ℚ) - 2) * (((k : ℚ) - 2) * c) := by
  have inner : ∀ x ∈ ((range k).erase a).erase b,
      ∑ y ∈ ((range k).erase b).erase x, F x y = ((k : ℚ) - 2) * c := by
    intro x hx
    have hxb : x ≠ b := ne_of_mem_erase hx
    have hxk : x < k := mem_range.1 (mem_of_mem_erase (mem_of_mem_erase hx))
    rw [Finset.sum_congr rfl fun y hy => h x y hxk
      (mem_range.1 (mem_of_mem_erase (mem_of_mem_erase hy))) (Ne.symm (ne_of_mem_erase hy))]
    rw [sum_const, card_erase_of_mem (mem_erase.2 ⟨hxb, mem_range.2 hxk⟩),
      card_erase_of_mem (mem_range.2 hb), card_range, nsmul_eq_mul]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [Finset.sum_congr rfl inner]
  rw [sum_const, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hab, mem_range.2 hb⟩),
    card_erase_of_mem (mem_range.2 ha), card_range, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

/-- The value of `extensions 6 n t a b` at distinct `a, b < t + 2`. -/
def G (t n : ℕ) : ℚ :=
  if t = 0 then (21 : ℚ) ^ n / 24 + (7 : ℚ) ^ n / 4 + (3 : ℚ) ^ n / 3 + 3 / 8
  else if t = 1 then (21 : ℚ) ^ n / 6 + (7 : ℚ) ^ n / 2 + (3 : ℚ) ^ n / 3
  else if t = 2 then ((21 : ℚ) ^ n + (7 : ℚ) ^ n) / 2 else (21 : ℚ) ^ n

def P (n : ℕ) : Prop :=
  ∀ t a b, t ≤ 4 → a < t + 2 → b < t + 2 → a ≠ b → (extensions 6 n t a b : ℚ) = G t n

lemma ext_succ (n t a b : ℕ) : (extensions 6 (n + 1) t a b : ℚ) =
    (∑ y ∈ (range (t + 2)).erase b, (extensions 6 n t b y : ℚ)) +
    (∑ x ∈ ((range (t + 2)).erase a).erase b, ∑ y ∈ ((range (t + 2)).erase b).erase x,
      (extensions 6 n t x y : ℚ)) +
    (if t + 2 < 6 then
       (∑ y ∈ (range (t + 2)).erase b, (extensions 6 n (t + 1) (t + 2) y : ℚ)) +
       (∑ x ∈ (range (t + 2)).erase a, (extensions 6 n (t + 1) x (t + 2) : ℚ)) else 0) +
    (if t + 3 < 6 then (extensions 6 n (t + 2) (t + 2) (t + 3) : ℚ) else 0) := by
  rw [extensions]
  push_cast
  split_ifs <;> simp

theorem allP (n : ℕ) : P n := by
  induction n with
  | zero =>
    intro t a b ht _ _ _
    simp only [extensions, Int.cast_one, G, pow_zero]
    interval_cases t <;> norm_num
  | succ n ih =>
    intro t a b ht ha hb hab
    rw [ext_succ]
    have e1 := sum1 (t + 2) b hb (fun y => (extensions 6 n t b y : ℚ)) (G t n)
      (fun y hy hyb => ih t b y ht hb hy (Ne.symm hyb))
    have e2 := sum2 (t + 2) a b ha hb hab (fun x y => (extensions 6 n t x y : ℚ)) (G t n)
      (fun x y hx hy hxy => ih t x y ht hx hy hxy)
    rw [e1, e2]
    interval_cases t
    · have e3 := sum1 2 b hb (fun y => (extensions 6 n 1 2 y : ℚ)) (G 1 n)
        (fun y hy _ => ih 1 2 y (by norm_num) (by norm_num) (by omega) (by omega))
      have e4 := sum1 2 a ha (fun x => (extensions 6 n 1 x 2 : ℚ)) (G 1 n)
        (fun x hx _ => ih 1 x 2 (by norm_num) (by omega) (by norm_num) (by omega))
      have e5 := ih 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num only [e3, e4, e5]
      simp only [G]; norm_num; ring
    · have e3 := sum1 3 b hb (fun y => (extensions 6 n 2 3 y : ℚ)) (G 2 n)
        (fun y hy _ => ih 2 3 y (by norm_num) (by norm_num) (by omega) (by omega))
      have e4 := sum1 3 a ha (fun x => (extensions 6 n 2 x 3 : ℚ)) (G 2 n)
        (fun x hx _ => ih 2 x 3 (by norm_num) (by omega) (by norm_num) (by omega))
      have e5 := ih 3 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num only [e3, e4, e5]
      simp only [G]; norm_num; ring
    · have e3 := sum1 4 b hb (fun y => (extensions 6 n 3 4 y : ℚ)) (G 3 n)
        (fun y hy _ => ih 3 4 y (by norm_num) (by norm_num) (by omega) (by omega))
      have e4 := sum1 4 a ha (fun x => (extensions 6 n 3 x 4 : ℚ)) (G 3 n)
        (fun x hx _ => ih 3 x 4 (by norm_num) (by omega) (by norm_num) (by omega))
      have e5 := ih 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num only [e3, e4, e5]
      simp only [G]; norm_num; ring
    · have e3 := sum1 5 b hb (fun y => (extensions 6 n 4 5 y : ℚ)) (G 4 n)
        (fun y hy _ => ih 4 5 y (by norm_num) (by norm_num) (by omega) (by omega))
      have e4 := sum1 5 a ha (fun x => (extensions 6 n 4 x 5 : ℚ)) (G 4 n)
        (fun x hx _ => ih 4 x 5 (by norm_num) (by omega) (by norm_num) (by omega))
      norm_num only [e3, e4]
      simp only [G]; norm_num; ring
    · norm_num only
      simp only [G]; norm_num; ring

lemma sv (m : ℕ) : (sequence (m + 1) : ℚ) = (189 + 56 * 3 ^ (m + 1) + 18 * 7 ^ (m + 1) + 21 ^ (m + 1)) / 504 := by
  rw [show sequence (m + 1) = extensions 6 m 0 0 1 from rfl]
  rw [allP m 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [G, if_true]; ring

lemma sv_int (m : ℕ) : 504 * sequence (m + 1) = 189 + 56 * 3 ^ (m + 1) + 18 * 7 ^ (m + 1) + 21 ^ (m + 1) := by
  have h := sv m
  have : (504 * sequence (m + 1) : ℚ) = 189 + 56 * 3 ^ (m + 1) + 18 * 7 ^ (m + 1) + 21 ^ (m + 1) := by
    rw [h]; ring
  exact_mod_cast this

theorem full :
    (∀ m : ℕ, 504 * sequence (m+1) = 189 + 56*3^(m+1) + 18*7^(m+1) + 21^(m+1)) ∧
    (∀ n : ℕ, delayed 0 n - 32*delayed 1 n + 262*delayed 2 n - 672*delayed 3 n + 441*delayed 4 n = numerator n) := by
  refine ⟨sv_int, fun n => ?_⟩
  have s0 : sequence 0 = 0 := rfl
  have s1 : sequence 1 = 1 := by have := sv_int 0; norm_num at this; omega
  have s2 : sequence 2 = 4 := by have := sv_int 1; norm_num at this; omega
  have s3 : sequence 3 = 34 := by have := sv_int 2; norm_num at this; omega
  have s4 : sequence 4 = 481 := by have := sv_int 3; norm_num at this; omega
  match n with
  | 0 => simp [delayed, numerator, s0]
  | 1 => simp [delayed, numerator, s0, s1]
  | 2 => simp [delayed, numerator, s0, s1, s2]
  | 3 => simp [delayed, numerator, s0, s1, s2, s3]
  | 4 => simp [delayed, numerator, s0, s1, s2, s3, s4]
  | k + 5 =>
    simp only [delayed, numerator, show 0 ≤ k + 5 by omega, show 1 ≤ k + 5 by omega,
      show 2 ≤ k + 5 by omega, show 3 ≤ k + 5 by omega, show 4 ≤ k + 5 by omega, if_true,
      show k + 5 ≠ 1 by omega, show k + 5 ≠ 2 by omega, show k + 5 ≠ 3 by omega,
      show k + 5 ≠ 4 by omega, if_false,
      show k + 5 - 0 = (k + 4) + 1 by omega, show k + 5 - 1 = (k + 3) + 1 by omega,
      show k + 5 - 2 = (k + 2) + 1 by omega, show k + 5 - 3 = (k + 1) + 1 by omega,
      show k + 5 - 4 = k + 1 by omega]
    qify
    rw [sv, sv, sv, sv, sv]
    ring

end OMA.P_oeis_a198976

theorem OMA.solution : type_of% @OMA.S_oeis_a198976.main := OMA.P_oeis_a198976.full
