import OMAStatements.S_oeis_a079450
import Mathlib

/-!
# OEIS A079450: a(n+1) = 3 a(n) exactly at the greedy powers of 2/3

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2); the Lean text was written by
Codex from that proof sketch.

For `n ≥ 1`, `1 ≤ u n < 2`, so `⌊(3/2) u n⌋` is 1 or 2 and `a (n+1) = 3 a n` holds exactly when
`u n < 4/3`; call such `n` picked. Since `u n * 2^(n-1)` is an integer, `u n` is never `4/3`. The
quantity `R n = (2 - u (n+1)) * (2/3)^n` starts at 1 and drops by `(2/3)^n` exactly at the picked
`n`, which are exactly the `n` with `(2/3)^n ≤ R (n-1)`; moreover `0 < R n < (2/3)^n` for `n ≥ 1`.
So `R n` is 1 minus the sum of `(2/3)^k` over the picked `k ≤ n`, the list of picked `k ≤ n` is a
greedy list in the statement's sense, and conversely every greedy list is such a list.
-/

open OMA.S_oeis_a079450

namespace OMA.A079450Proof

abbrev x : ℚ := 2 / 3

lemma u_range (n : ℕ) : 1 ≤ u (n + 1) ∧ u (n + 1) < 2 := by
  cases n with
  | zero => norm_num [u]
  | succ n =>
    change 1 ≤ Int.fract ((3 / 2 : ℚ) * u (n + 1)) + 1 ∧
      Int.fract ((3 / 2 : ℚ) * u (n + 1)) + 1 < 2
    constructor
    · linarith [Int.fract_nonneg ((3 / 2 : ℚ) * u (n + 1))]
    · linarith [Int.fract_lt_one ((3 / 2 : ℚ) * u (n + 1))]

lemma u_step_small (n : ℕ) (h : u (n + 1) < 4 / 3) :
    u (n + 2) = (3 / 2 : ℚ) * u (n + 1) := by
  have hr := u_range n
  have hf : ⌊(3 / 2 : ℚ) * u (n + 1)⌋ = (1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  rw [u, ← Int.self_sub_floor, hf]
  norm_num

lemma u_step_large (n : ℕ) (h : ¬ u (n + 1) < 4 / 3) :
    u (n + 2) = (3 / 2 : ℚ) * u (n + 1) - 1 := by
  have hr := u_range n
  have hf : ⌊(3 / 2 : ℚ) * u (n + 1)⌋ = (2 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  rw [u, ← Int.self_sub_floor, hf]
  norm_num
  ring

lemma u_dyadic (n : ℕ) : ∃ z : ℤ, u (n + 1) * (2 : ℚ) ^ n = z := by
  induction n with
  | zero => exact ⟨1, by norm_num [u]⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    by_cases h : u (n + 1) < 4 / 3
    · refine ⟨3 * z, ?_⟩
      rw [u_step_small n h, pow_succ]
      push_cast
      nlinarith [hz]
    · refine ⟨3 * z - 2 ^ (n + 1), ?_⟩
      rw [u_step_large n h, pow_succ]
      push_cast
      rw [pow_succ]
      nlinarith [hz]

lemma u_ne_four_thirds (n : ℕ) : u (n + 1) ≠ 4 / 3 := by
  intro h
  obtain ⟨z, hz⟩ := u_dyadic n
  rw [h] at hz
  have hq : (3 : ℚ) * z = 2 ^ (n + 2) := by
    rw [pow_add]
    norm_num
    linarith
  have hi : (3 : ℤ) * z = 2 ^ (n + 2) := by exact_mod_cast hq
  have hd : (3 : ℤ) ∣ 2 ^ (n + 2) := ⟨z, hi.symm⟩
  have hn := Int.Prime.dvd_pow Nat.prime_three hd
  norm_num at hn

lemma u_gt_one (n : ℕ) : 1 < u (n + 2) := by
  have hr := u_range n
  have hn := u_ne_four_thirds n
  by_cases h : u (n + 1) < 4 / 3
  · rw [u_step_small n h]
    linarith
  · rw [u_step_large n h]
    have : 4 / 3 < u (n + 1) := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hn)
    linarith

lemma a_eq_iff (n : ℕ) :
    a (n + 2) = 3 * a (n + 1) ↔ u (n + 1) < 4 / 3 := by
  have hp : 0 < (2 : ℚ) ^ n := by positivity
  have hn : n + 2 - 1 = n + 1 := by omega
  by_cases h : u (n + 1) < 4 / 3
  · simp only [a, hn, Nat.add_sub_cancel, u_step_small n h, pow_succ]
    constructor
    · intro _; exact h
    · intro _; ring
  · simp only [a, hn, Nat.add_sub_cancel, u_step_large n h, pow_succ]
    constructor
    · intro he
      nlinarith
    · exact fun hc => (h hc).elim

def R (n : ℕ) : ℚ := (2 - u (n + 1)) * x ^ n

lemma R_zero : R 0 = 1 := by norm_num [R, u]

lemma x_pos : 0 < x := by norm_num [x]

lemma x_pow_pos (n : ℕ) : 0 < x ^ n := pow_pos x_pos n

lemma x_pow_anti {k n : ℕ} (h : k ≤ n) : x ^ n ≤ x ^ k :=
  pow_le_pow_of_le_one (le_of_lt x_pos) (by norm_num [x]) h

lemma R_pos (n : ℕ) : 0 < R n := by
  unfold R
  exact mul_pos (by linarith [(u_range n).2]) (x_pow_pos n)

lemma R_lt (n : ℕ) : R (n + 1) < x ^ (n + 1) := by
  have h : 2 - u (n + 2) < (1 : ℚ) := by linarith [u_gt_one n]
  have hm := mul_lt_mul_of_pos_right h (x_pow_pos (n + 1))
  simpa only [R, one_mul] using hm

lemma R_step (n : ℕ) :
    R (n + 1) = if u (n + 1) < 4 / 3 then R n - x ^ (n + 1) else R n := by
  by_cases h : u (n + 1) < 4 / 3
  · simp only [R, if_pos h, u_step_small n h, pow_succ]
    dsimp [x]
    ring
  · simp only [R, if_neg h, u_step_large n h, pow_succ]
    dsimp [x]
    ring

lemma R_fit (n : ℕ) : x ^ (n + 1) ≤ R n ↔ u (n + 1) < 4 / 3 := by
  have hp := x_pow_pos n
  have hn := u_ne_four_thirds n
  simp only [R, pow_succ]
  dsimp [x] at *
  constructor
  · intro h
    have hu : u (n + 1) ≤ 4 / 3 := by nlinarith
    exact lt_of_le_of_ne hu hn
  · intro h
    nlinarith

def L : ℕ → List ℕ
  | 0 => []
  | n + 1 => if u (n + 1) < 4 / 3 then L n ++ [n + 1] else L n

lemma mem_L (n k : ℕ) : k ∈ L n ↔ 1 ≤ k ∧ k ≤ n ∧ u k < 4 / 3 := by
  induction n with
  | zero =>
    simp only [L, List.not_mem_nil, false_iff]
    rintro ⟨hk, hk0, _⟩
    omega
  | succ n ih =>
    by_cases h : u (n + 1) < 4 / 3
    · rw [L, if_pos h]
      simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨hk, hkn, hu⟩ | rfl)
        · exact ⟨hk, by omega, hu⟩
        · exact ⟨by omega, le_rfl, h⟩
      · rintro ⟨hk, hkn, hu⟩
        by_cases he : k = n + 1
        · exact Or.inr he
        · exact Or.inl ⟨hk, by omega, hu⟩
    · rw [L, if_neg h, ih]
      constructor
      · rintro ⟨hk, hkn, hu⟩
        exact ⟨hk, by omega, hu⟩
      · rintro ⟨hk, hkn, hu⟩
        have he : k ≠ n + 1 := by intro he; subst k; exact h hu
        exact ⟨hk, by omega, hu⟩

lemma sum_L (n : ℕ) : ((L n).map fun j => x ^ j).sum = 1 - R n := by
  induction n with
  | zero => norm_num [L, R_zero]
  | succ n ih =>
    by_cases h : u (n + 1) < 4 / 3
    · rw [L, if_pos h, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      rw [ih, R_step, if_pos h]
      ring
    · rw [L, if_neg h, ih, R_step, if_neg h]

lemma fit_gt (m k : ℕ) (hk : 1 ≤ k) (hf : x ^ k ≤ R m) : m < k := by
  by_contra hn
  have hkm : k ≤ m := by omega
  cases m with
  | zero => omega
  | succ m =>
    have ha := x_pow_anti hkm
    have hr := R_lt m
    linarith

lemma L_greedy (n : ℕ) : Greedy (L n) := by
  induction n with
  | zero => exact Greedy.nil
  | succ n ih =>
    by_cases h : u (n + 1) < 4 / 3
    · rw [L, if_pos h]
      apply Greedy.snoc (L n) (n + 1) ih
      constructor
      · change 1 ≤ n + 1 ∧ ((L n).map fun j => x ^ j).sum + x ^ (n + 1) ≤ 1
        rw [sum_L]
        exact ⟨by omega, by linarith [(R_fit n).mpr h]⟩
      · intro k hk
        change 1 ≤ k ∧ ((L n).map fun j => x ^ j).sum + x ^ k ≤ 1 at hk
        rw [sum_L] at hk
        have hf : x ^ k ≤ R n := by linarith [hk.2]
        exact fit_gt n k hk.1 hf
    · rw [L, if_neg h]
      exact ih

lemma next_scan (m e : ℕ)
    (he : IsLeast {k : ℕ | 1 ≤ k ∧
      ((L m).map fun j => x ^ j).sum + x ^ k ≤ 1} e) :
    L e = L m ++ [e] := by
  have he1 : 1 ≤ e := he.1.1
  have hef : x ^ e ≤ R m := by
    have h := he.1.2
    rw [sum_L] at h
    linarith
  have hme : m < e := fit_gt m e he1 hef
  have hmin : ∀ k : ℕ, 1 ≤ k → x ^ k ≤ R m → e ≤ k := by
    intro k hk hf
    apply he.2
    change 1 ≤ k ∧ ((L m).map fun j => x ^ j).sum + x ^ k ≤ 1
    rw [sum_L]
    exact ⟨hk, by linarith⟩
  have hs : ∀ j : ℕ, m + j < e → R (m + j) = R m ∧ L (m + j) = L m := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hp : ¬ u (m + j + 1) < 4 / 3 := by
        intro hp
        have hf := (R_fit (m + j)).mpr hp
        rw [hi.1] at hf
        have := hmin (m + j + 1) (by omega) hf
        omega
      constructor
      · rw [Nat.add_succ, R_step, if_neg hp, hi.1]
      · rw [Nat.add_succ, L, if_neg hp, hi.2]
  have hidx : m + (e - 1 - m) = e - 1 := by omega
  have hstable : R (e - 1) = R m ∧ L (e - 1) = L m := by
    have h := hs (e - 1 - m) (by omega)
    simpa only [hidx] using h
  have heq : e - 1 + 1 = e := by omega
  have hp : u (e - 1 + 1) < 4 / 3 := by
    apply (R_fit (e - 1)).mp
    rw [heq, hstable.1]
    exact hef
  calc
    L e = L (e - 1 + 1) := by rw [heq]
    _ = L (e - 1) ++ [e - 1 + 1] := by rw [L, if_pos hp]
    _ = L m ++ [e] := by rw [hstable.2, heq]

lemma greedy_is_scan {l : List ℕ} (h : Greedy l) : ∃ m, l = L m := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | snoc l e hl he ih =>
    obtain ⟨m, rfl⟩ := ih
    exact ⟨e, (next_scan m e he).symm⟩

lemma picked_iff_greedy (n : ℕ) (hn : 1 ≤ n) :
    u n < 4 / 3 ↔ IsGreedyPower n := by
  constructor
  · intro h
    exact ⟨L n, L_greedy n, (mem_L n n).mpr ⟨hn, le_rfl, h⟩⟩
  · rintro ⟨l, hl, hmem⟩
    obtain ⟨m, rfl⟩ := greedy_is_scan hl
    exact ((mem_L m n).mp hmem).2.2

end OMA.A079450Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a079450.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (OMA.A079450Proof.a_eq_iff m).trans
    (OMA.A079450Proof.picked_iff_greedy (m + 1) hn)
