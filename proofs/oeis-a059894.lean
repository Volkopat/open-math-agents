import OMAStatements.S_oeis_a059894
import Mathlib

/-!
Write D for the binary digits of n without the top bit and M = reverse (map (1 - ·) D), so that
a(n) = ofDigits (M ++ [1]). The digits of 2n + x are x :: digits n, hence M(2n+x) = M(n) ++ [1-x],
which gives the first conjecture. For the second, digits (ofDigits (L ++ [1])) = L ++ [1] for a
0/1 list L, rev n = ofDigits (map (1 - ·) D ++ [1]) because ofDigits D + ofDigits (map (1 - ·) D)
= 2^|D| - 1, and the sum of map (1 - ·) D is the number of zeros of D.
-/

namespace R059894
open OMA.S_oeis_a059894

def M (n : ℕ) : List ℕ := (((Nat.digits 2 n).dropLast).map (fun b => 1 - b)).reverse

theorem a_def (n : ℕ) : a n = Nat.ofDigits 2 (M n ++ [1]) := rfl

theorem lenM (n : ℕ) (hn : n ≠ 0) : (M n).length = Nat.log 2 n := by
  unfold M
  rw [List.length_reverse, List.length_map, List.length_dropLast,
    Nat.length_digits 2 n (by norm_num) hn, Nat.add_sub_cancel]

theorem M_step (n x : ℕ) (hn : n ≠ 0) (hx : x < 2) : M (2 * n + x) = M n ++ [1 - x] := by
  unfold M
  rw [show 2 * n + x = x + 2 * n by ring, Nat.digits_add 2 (by norm_num) x n hx (Or.inr hn),
    List.dropLast_cons_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hn), List.map_cons,
    List.reverse_cons]

theorem a_split (n : ℕ) (hn : n ≠ 0) : a n = Nat.ofDigits 2 (M n) + 2 ^ Nat.log 2 n := by
  rw [a_def, Nat.ofDigits_append, lenM n hn, Nat.ofDigits_singleton, mul_one]

theorem a_step (n x : ℕ) (hn : n ≠ 0) (hx : x < 2) :
    a (2 * n + x) = Nat.ofDigits 2 (M n) + 2 ^ Nat.log 2 n * (1 - x) + 2 ^ (Nat.log 2 n + 1) := by
  rw [a_def, M_step n x hn hx, Nat.ofDigits_append, Nat.ofDigits_append, List.length_append,
    lenM n hn, Nat.ofDigits_singleton, Nat.ofDigits_singleton, List.length_singleton, mul_one]

theorem a_one : a 1 = 1 := by
  rw [a_split 1 one_ne_zero]
  unfold M
  rw [Nat.digits_of_lt 2 1 one_ne_zero one_lt_two]
  simp

theorem digits_split (n : ℕ) (hn : n ≠ 0) :
    Nat.digits 2 n = (Nat.digits 2 n).dropLast ++ [1] := by
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hl : (Nat.digits 2 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hn
  have hlt : (Nat.digits 2 n).getLast hne < 2 :=
    Nat.digits_lt_base (by norm_num) (List.getLast_mem hne)
  have h1 : (Nat.digits 2 n).getLast hne = 1 := by omega
  have := List.dropLast_concat_getLast hne
  rw [h1] at this
  exact this.symm

theorem pair (D : List ℕ) (hD : ∀ d ∈ D, d < 2) :
    Nat.ofDigits 2 D + Nat.ofDigits 2 (D.map (fun b => 1 - b)) + 1 = 2 ^ D.length ∧
      (D.map (fun b => 1 - b)).sum = D.count 0 := by
  induction D with
  | nil => simp [Nat.ofDigits]
  | cons d D ih =>
    have hd : d < 2 := hD d (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (fun e he => hD e (List.mem_cons_of_mem d he))
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, List.sum_cons, List.count_cons]
    constructor
    · rw [pow_succ, ← h1]
      omega
    · rw [h2]
      interval_cases d <;> simp <;> omega

theorem bits_map (D : List ℕ) : ∀ l ∈ D.map (fun b => 1 - b), l < 2 := by
  intro l hl
  rw [List.mem_map] at hl
  obtain ⟨b, -, rfl⟩ := hl
  omega

theorem wt_bits (L : List ℕ) (hL : ∀ l ∈ L, l < 2) :
    wt (Nat.ofDigits 2 (L ++ [1])) = L.sum + 1 := by
  have w1 : ∀ l ∈ L ++ [1], l < 2 := by
    intro l hl
    rw [List.mem_append, List.mem_singleton] at hl
    rcases hl with h | h
    · exact hL l h
    · omega
  have w2 : ∀ h : L ++ [1] ≠ [], (L ++ [1]).getLast h ≠ 0 := by
    intro h
    simp
  unfold wt
  rw [Nat.digits_ofDigits 2 (by norm_num) _ w1 w2, List.sum_append, List.sum_singleton]

theorem part3 : ∀ n : ℕ, 1 ≤ n → wt (a n) = wt (rev n) ∧ wt (rev n) = zeros n + 1 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hsplit := digits_split n hn0
  have hM : M n = ((Nat.digits 2 n).dropLast.map (fun b => 1 - b)).reverse := rfl
  generalize hD : (Nat.digits 2 n).dropLast = D at hsplit hM
  have hDb : ∀ d ∈ D, d < 2 := by
    intro d hd
    have : d ∈ Nat.digits 2 n := by
      rw [hsplit]
      exact List.mem_append_left _ hd
    exact Nat.digits_lt_base (by norm_num) this
  have hlen : D.length = Nat.log 2 n := by
    have := congrArg List.length hsplit
    rw [List.length_append, List.length_singleton, Nat.length_digits 2 n (by norm_num) hn0] at this
    omega
  obtain ⟨p1, p2⟩ := pair D hDb
  rw [hlen] at p1
  have hnD : n = Nat.ofDigits 2 D + 2 ^ Nat.log 2 n := by
    have := Nat.ofDigits_digits 2 n
    rw [hsplit, Nat.ofDigits_append, hlen, Nat.ofDigits_singleton, mul_one] at this
    omega
  have hrev : rev n = Nat.ofDigits 2 (D.map (fun b => 1 - b) ++ [1]) := by
    rw [Nat.ofDigits_append, List.length_map, hlen, Nat.ofDigits_singleton, mul_one]
    unfold rev
    rw [pow_succ]
    omega
  have hrb : ∀ l ∈ (D.map (fun b => 1 - b)).reverse, l < 2 :=
    fun l hl => bits_map D l (List.mem_reverse.mp hl)
  refine ⟨?_, ?_⟩
  · rw [a_def, hM, hrev, wt_bits _ hrb, wt_bits _ (bits_map D), List.sum_reverse]
  · rw [hrev, wt_bits _ (bits_map D), p2]
    unfold zeros
    rw [hsplit, List.count_append]
    simp

end R059894

theorem OMA.solution : type_of% @OMA.S_oeis_a059894.main := by
  refine ⟨R059894.a_one, fun n hn => ⟨?_, ?_⟩, R059894.part3⟩
  · have h := R059894.a_step n 0 (by omega) (by norm_num)
    simp only [add_zero, Nat.sub_zero, mul_one] at h
    rw [h, R059894.a_split n (by omega)]
  · rw [R059894.a_step n 1 (by omega) (by norm_num), R059894.a_split n (by omega), pow_succ]
    simp only [Nat.sub_self, mul_zero, add_zero]
    ring
