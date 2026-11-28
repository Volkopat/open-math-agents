import OMAStatements.S_oeis_a090996
import Mathlib

/-!
Let t(n) = 2^(w(n)+1) - 1 - n (the complement of n in w(n)+1 bits) and F(n) = w(n)+1 if t(n) = 0,
F(n) = w(n) - w(t(n)) otherwise. Since digits(2m+x) = x :: digits(m), the leading-ones count
satisfies a(2m+x) = a(m) + x if m is all ones (a(m) = w(m)+1) and a(2m+x) = a(m) otherwise.
As w(2m+x) = w(m)+1 and t(2m+x) = 2 t(m) + 1 - x, F satisfies the same recursion, so a = F
by strong induction. Finally w(n+1) is w(n)+1 or w(n) according as t(n) = 0 or not, and in both
cases the right-hand side of the conjecture equals F(n).
-/

namespace R090996
open OMA.S_oeis_a090996

def t (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n + 1) - 1 - n

def F (n : ℕ) : ℕ := if t n = 0 then Nat.log 2 n + 1 else Nat.log 2 n - Nat.log 2 (t n)

theorem a_step (m x : ℕ) (hm : m ≠ 0) (hx : x < 2) :
    a (2 * m + x) = if a m = Nat.log 2 m + 1 then a m + x else a m := by
  unfold a
  rw [show 2 * m + x = x + 2 * m by ring, Nat.digits_add 2 (by norm_num) x m hx (Or.inr hm),
    List.reverse_cons, List.takeWhile_append, List.length_reverse,
    Nat.length_digits 2 m (by norm_num) hm]
  split_ifs with h
  · rw [List.length_append, List.length_reverse, Nat.length_digits 2 m (by norm_num) hm, h]
    interval_cases x <;> simp [List.takeWhile]
  all_goals rfl

theorem a_one : a 1 = 1 := by
  unfold a
  rw [Nat.digits_of_lt 2 1 one_ne_zero one_lt_two]
  rfl

theorem n_lt (n : ℕ) : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n

theorem t_lt (n : ℕ) (hn : n ≠ 0) : t n < 2 ^ Nat.log 2 n := by
  unfold t
  have h1 := Nat.pow_log_le_self 2 hn
  have h2 : 0 < 2 ^ Nat.log 2 n := by positivity
  rw [pow_succ]
  omega

theorem log_double (m x : ℕ) (hm : m ≠ 0) (hx : x < 2) :
    Nat.log 2 (2 * m + x) = Nat.log 2 m + 1 := by
  rw [Nat.log_of_one_lt_of_le (b := 2) (by norm_num) (by omega : 2 ≤ 2 * m + x),
    show (2 * m + x) / 2 = m by omega]

theorem t_double (m x : ℕ) (hm : m ≠ 0) (hx : x < 2) : t (2 * m + x) = 2 * t m + 1 - x := by
  unfold t
  rw [log_double m x hm hx]
  have := n_lt m
  rw [pow_succ 2 (Nat.log 2 m + 1)]
  omega

theorem main_F : ∀ n : ℕ, n ≠ 0 → a n = F n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    rw [a_one]
    unfold F t
    simp
  · obtain ⟨m, x, hx, rfl, hm⟩ : ∃ m x, x < 2 ∧ n = 2 * m + x ∧ m ≠ 0 :=
      ⟨n / 2, n % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 2).symm, by omega⟩
    have ihm := ih m (by omega) hm
    rw [a_step m x hm hx, ihm]
    unfold F
    rw [t_double m x hm hx, log_double m x hm hx]
    have htl := t_lt m hm
    by_cases h0 : t m = 0
    · rw [h0]
      interval_cases x <;> simp
    · have h1 : 2 * t m + 1 - x ≠ 0 := by omega
      have hlt : Nat.log 2 (2 * t m + 1 - x) = Nat.log 2 (t m) + 1 := by
        rw [Nat.log_of_one_lt_of_le (b := 2) (by norm_num) (by omega : 2 ≤ 2 * t m + 1 - x),
          show (2 * t m + 1 - x) / 2 = t m by omega]
      have hlog : Nat.log 2 (t m) < Nat.log 2 m := Nat.log_lt_of_lt_pow h0 htl
      simp only [h0, h1, hlt, ↓reduceIte]
      split_ifs with h2
      · omega
      · omega

end R090996

theorem OMA.solution : type_of% @OMA.S_oeis_a090996.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  rw [R090996.main_F n hn0]
  have htl := R090996.t_lt n hn0
  unfold R090996.F R090996.t OMA.S_oeis_a090996.w
  unfold R090996.t at htl
  have h1 := Nat.pow_log_le_self 2 hn0
  have h2 := R090996.n_lt n
  by_cases hc : n + 1 = 2 ^ (Nat.log 2 n + 1)
  · have hw : Nat.log 2 (n + 1) = Nat.log 2 n + 1 := by
      rw [hc, Nat.log_pow (b := 2) (by norm_num)]
    have ht : 2 ^ (Nat.log 2 n + 1) - 1 - n = 0 := by omega
    have hw2 : Nat.log 2 (2 ^ (Nat.log 2 n + 1 + 1) - n - 1) = Nat.log 2 n + 1 := by
      rw [show 2 ^ (Nat.log 2 n + 1 + 1) - n - 1 = 2 ^ (Nat.log 2 n + 1) by
        rw [pow_succ 2 (Nat.log 2 n + 1)]; omega, Nat.log_pow (b := 2) (by norm_num)]
    rw [hw, hw2, if_pos ht]
    push_cast
    ring
  · have hlt : n + 1 < 2 ^ (Nat.log 2 n + 1) := by omega
    have hw : Nat.log 2 (n + 1) = Nat.log 2 n :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt
    have ht : 2 ^ (Nat.log 2 n + 1) - 1 - n ≠ 0 := by omega
    have hle : Nat.log 2 (2 ^ (Nat.log 2 n + 1) - 1 - n) < Nat.log 2 n :=
      Nat.log_lt_of_lt_pow ht htl
    rw [hw, if_neg ht, show 2 ^ (Nat.log 2 n + 1) - n - 1 = 2 ^ (Nat.log 2 n + 1) - 1 - n by omega]
    have e : ((Nat.log 2 n : ℕ) : ℤ) * ((Nat.log 2 n : ℤ) - (Nat.log 2 n : ℤ) + 1) =
        (Nat.log 2 n : ℤ) := by ring
    rw [e]
    omega
