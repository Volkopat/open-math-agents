import OMAStatements.S_oeis_a308187

-- Problem: A308187: Fixed point (beginning with a) of the morphism a -> aab, b -> b, over the alphabet {a,b} = {0,1}.
-- Upstream: formal-conjectures statements/oeis-a308187.lean:0 (declaration OMA.S_oeis_a308187.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: W (k+1) = W k ++ W k ++ [1]. For f = A005187, f is strictly increasing,
-- f (2^k) = 2^(k+1) - 1 = length of W k, and f (j + 2^k) = f j + 2^(k+1) - 1 for j < 2^k.
-- By induction on k: for i < length (W k), the letter at i is 0 or 1, and it is 0 iff i is a
-- value of f.

namespace L02A308187

open OMA.S_oeis_a308187

theorem W_rec (k : ℕ) : W (k + 1) = W k ++ W k ++ [1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc W (k + 1 + 1) = (W (k + 1)).flatMap mor := rfl
      _ = (W k ++ W k ++ [1]).flatMap mor := by rw [ih]
      _ = (W k).flatMap mor ++ (W k).flatMap mor ++ [1].flatMap mor := by
        rw [List.flatMap_append, List.flatMap_append]
      _ = W (k + 1) ++ W (k + 1) ++ [1] := rfl

theorem len_W (k : ℕ) : (W k).length + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [W_rec k, List.length_append, List.length_append, List.length_singleton, pow_succ]
    omega

theorem getD_left (u v : List ℕ) (i : ℕ) (h : i < u.length) :
    (u ++ v).getD i 0 = u.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_right (u v : List ℕ) (i : ℕ) (h : u.length ≤ i) :
    (u ++ v).getD i 0 = v.getD (i - u.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem f_eqn (n : ℕ) : A005187 n = if _h : n = 0 then 0 else A005187 (n / 2) + n := by
  rw [A005187]

theorem f_zero : A005187 0 = 0 := by
  rw [f_eqn 0, dif_pos (rfl : (0 : ℕ) = 0)]

theorem f_half (m : ℕ) : A005187 m = A005187 (m / 2) + m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h, Nat.zero_div, Nat.add_zero]
  · rw [f_eqn m, dif_neg (show ¬ m = 0 by omega)]

theorem f_shift (k : ℕ) : ∀ j : ℕ, j < 2 ^ k → A005187 (j + 2 ^ k) + 1 = A005187 j + 2 ^ (k + 1) := by
  induction k with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by
      rw [pow_zero] at hj
      omega
    subst hj0
    have h1 := f_half 1
    have h3 : (1 : ℕ) / 2 = 0 := by norm_num
    rw [h3] at h1
    have h2 : A005187 (0 + 2 ^ 0) = A005187 1 := by norm_num
    have h4 : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
    have h5 := f_zero
    omega
  | succ k ih =>
    intro j hj
    have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hp2 : (2 : ℕ) ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
    have h1 := f_half (j + 2 ^ (k + 1))
    have h2 : (j + 2 ^ (k + 1)) / 2 = j / 2 + 2 ^ k := by
      rw [hp]
      omega
    rw [h2] at h1
    have h3 := ih (j / 2) (by omega)
    have h4 := f_half j
    omega

theorem f_two_pow (k : ℕ) : A005187 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h := f_shift k 0 (by positivity)
  rw [Nat.zero_add, f_zero] at h
  omega

theorem f_lt_succ (m : ℕ) : A005187 m < A005187 (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := f_half m
    have h2 := f_half (m + 1)
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [show m / 2 = t by omega] at h1
      rw [show (m + 1) / 2 = t by omega] at h2
      omega
    · rw [show m / 2 = t by omega] at h1
      rw [show (m + 1) / 2 = t + 1 by omega] at h2
      have h3 := ih t (by omega)
      omega

theorem f_mono : StrictMono A005187 := strictMono_nat_of_lt_succ f_lt_succ

theorem ex_shift (k L i : ℕ) (hL : L + 1 = 2 ^ (k + 1)) (h1 : L ≤ i) (h2 : i < L + L) :
    (∃ j, A005187 j = i - L) ↔ (∃ j, A005187 j = i) := by
  have hF := f_two_pow k
  have hF2 := f_two_pow (k + 1)
  have hP : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hP2 : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
  constructor
  · rintro ⟨j, hj⟩
    have hjk : j < 2 ^ k := f_mono.lt_iff_lt.mp (by omega)
    have hs := f_shift k j hjk
    exact ⟨j + 2 ^ k, by omega⟩
  · rintro ⟨j, hj⟩
    have hjk : 2 ^ k ≤ j := f_mono.le_iff_le.mp (by omega)
    have hjk2 : j < 2 ^ (k + 1) := f_mono.lt_iff_lt.mp (by omega)
    have hs := f_shift k (j - 2 ^ k) (by omega)
    rw [Nat.sub_add_cancel hjk] at hs
    exact ⟨j - 2 ^ k, by omega⟩

theorem ex_top (k L : ℕ) (hL : L + 1 = 2 ^ (k + 1)) : ¬ ∃ j, A005187 j = L + L := by
  rintro ⟨j, hj⟩
  have hF := f_two_pow k
  have hF2 := f_two_pow (k + 1)
  have hP : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hP2 : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
  have hjk : 2 ^ k ≤ j := f_mono.le_iff_le.mp (by omega)
  have hjk2 : j < 2 ^ (k + 1) := f_mono.lt_iff_lt.mp (by omega)
  have hs := f_shift k (j - 2 ^ k) (by omega)
  rw [Nat.sub_add_cancel hjk] at hs
  have hlt : A005187 (j - 2 ^ k) < A005187 (2 ^ k) := f_mono.lt_iff_lt.mpr (by omega)
  omega

theorem W_letters (k : ℕ) : ∀ i : ℕ, i < (W k).length →
    (((W k).getD i 0 = 0 ↔ ∃ j, A005187 j = i) ∧ ((W k).getD i 0 = 0 ∨ (W k).getD i 0 = 1)) := by
  induction k with
  | zero =>
    intro i hi
    have h1 : (W 0).length = 1 := rfl
    have hi0 : i = 0 := by omega
    subst hi0
    have hg : (W 0).getD 0 0 = 0 := rfl
    rw [hg]
    exact ⟨⟨fun _ => ⟨0, f_zero⟩, fun _ => rfl⟩, Or.inl rfl⟩
  | succ k ih =>
    intro i hi
    have hL := len_W k
    have hW := W_rec k
    have hlen : (W (k + 1)).length = (W k).length + (W k).length + 1 := by
      rw [hW, List.length_append, List.length_append, List.length_singleton]
    rw [hW]
    rcases Nat.lt_or_ge i (W k).length with h1 | h1
    · rw [getD_left (W k ++ W k) [1] i (by rw [List.length_append]; omega),
        getD_left (W k) (W k) i h1]
      exact ih i h1
    · rcases Nat.lt_or_ge i ((W k).length + (W k).length) with h2 | h2
      · rw [getD_left (W k ++ W k) [1] i (by rw [List.length_append]; omega),
          getD_right (W k) (W k) i h1]
        rw [← ex_shift k (W k).length i hL h1 h2]
        exact ih (i - (W k).length) (by omega)
      · have hi2 : i = (W k).length + (W k).length := by omega
        rw [getD_right (W k ++ W k) [1] i (by rw [List.length_append]; omega), List.length_append]
        rw [show i - ((W k).length + (W k).length) = 0 by omega]
        have hg : [1].getD 0 0 = 1 := rfl
        rw [hg, hi2]
        exact ⟨⟨fun h => absurd h (by norm_num), fun h => absurd h (ex_top k (W k).length hL)⟩,
          Or.inr rfl⟩

theorem lt_two_pow_l02 (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    omega

end L02A308187

open OMA.S_oeis_a308187 L02A308187 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308187.main := by
  intro n _hn
  have hlen := len_W n
  have hp := lt_two_pow_l02 (n + 1)
  have hlt : n - 1 < (W n).length := by omega
  obtain ⟨h1, h2⟩ := W_letters n (n - 1) hlt
  unfold a
  constructor
  · show (W n).getD (n - 1) 0 = 1 ↔ ∀ j, A005187 j ≠ n - 1
    constructor
    · intro h j hj
      have h3 := h1.mpr ⟨j, hj⟩
      omega
    · intro h
      rcases h2 with h3 | h3
      · exact absurd (h1.mp h3) (fun ⟨j, hj⟩ => h j hj)
      · exact h3
  · show (W n).getD (n - 1) 0 = 0 ↔ ¬ ∀ j, A005187 j ≠ n - 1
    rw [h1]
    constructor
    · rintro ⟨j, hj⟩ h
      exact h j hj
    · intro h
      by_contra hne
      exact h (fun j hj => hne ⟨j, hj⟩)
