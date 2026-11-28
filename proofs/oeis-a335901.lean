import OMAStatements.S_oeis_a335901
import Mathlib

/-!
# OEIS A335901: the least index where each power of two appears is A117261

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2); the Lean text was written by
Codex from that proof sketch.

Write `D j = A117261 j`, so `D 0 = 1` and `D (j+1) = 2^j * D j + 1`, and let `C 0 = 1`,
`C (i+1) = 2^(i+2) * (C i + 1)`. By strong induction on `n ≥ 1`, three facts hold together:
`a n` is a power of two; `n < D (j+1) → a n ≤ 2^j`; and `C i < n → 2^(i+1) ≤ a n`. The upper bound
at `n` uses the lower bound at `n - 1` to show that the index `(n-1) / a (n-1)` is below `D j`; the
lower bound at `n` uses the upper bound at `n - 1` to show that this index is above `C (i-1)`. Two
arithmetic facts link the two sequences: `C s < 2^s * D (s+1)` and
`2^(s+3) * (C s + 1) + 3 ≤ D (s+3)`. Both bounds give `a (2^j * D j) = 2^j`, hence
`a (D (j+1)) = 2 * a (D j)`, and the upper bound says no smaller index reaches that value.
-/

open OMA.S_oeis_a335901

namespace OMA.A335901Proof

abbrev D := A117261

lemma D_zero : D 0 = 1 := by
  norm_num [D, A117261]

lemma triangle_mono {k j : ℕ} (h : k ≤ j) :
    k * (k - 1) / 2 ≤ j * (j - 1) / 2 := by
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1))

lemma D_succ (j : ℕ) : D (j + 1) = 2 ^ j * D j + 1 := by
  unfold D A117261
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by simpa using hk
  have ht := triangle_mono hkj
  rw [Nat.triangle_succ]
  have he : j * (j - 1) / 2 + j - k * (k - 1) / 2 =
      j + (j * (j - 1) / 2 - k * (k - 1) / 2) := by omega
  rw [he, pow_add]

lemma pow_pos (j : ℕ) : 0 < (2 : ℕ) ^ j := by positivity

lemma pow_step_lt (j : ℕ) : (2 : ℕ) ^ j < 2 ^ (j + 1) := by
  rw [pow_succ]
  have := pow_pos j
  omega

lemma D_pos (j : ℕ) : 1 ≤ D j := by
  cases j with
  | zero => rw [D_zero]
  | succ j => rw [D_succ]; omega

lemma D_strict : StrictMono D := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [D_succ]
  have := pow_pos j
  nlinarith

lemma D_pow_lower (j : ℕ) : 2 ^ j ≤ D j := by
  cases j with
  | zero => norm_num [D_zero]
  | succ j =>
    by_cases hj : j = 0
    · subst j
      norm_num [D_succ, D_zero]
    · have hd : 2 ≤ D j := by
        have := D_strict (show 0 < j by omega)
        rw [D_zero] at this
        omega
      rw [D_succ, pow_succ]
      have hmul := Nat.mul_le_mul_left (2 ^ j) hd
      omega

def C : ℕ → ℕ
  | 0 => 1
  | i + 1 => 2 ^ (i + 2) * (C i + 1)

lemma C_zero : C 0 = 1 := rfl

lemma C_succ (i : ℕ) : C (i + 1) = 2 ^ (i + 2) * (C i + 1) := rfl

lemma C_strict : StrictMono C := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [C_succ]
  have := pow_pos (i + 2)
  nlinarith

lemma C_pos (i : ℕ) : 1 ≤ C i := by
  have := C_strict.monotone (Nat.zero_le i)
  simpa only [C_zero] using this

lemma C_lt (s : ℕ) : C s < 2 ^ s * D (s + 1) := by
  induction s with
  | zero => norm_num [C_zero, D_succ, D_zero]
  | succ s ih =>
    have hc : C s + 1 ≤ 2 ^ s * D (s + 1) := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (s + 2)) hc
    change C (s + 1) < 2 ^ (s + 1) * D ((s + 1) + 1)
    rw [C_succ, D_succ]
    simp only [pow_succ] at hm ⊢
    have := pow_pos s
    nlinarith

lemma D_C_bound (s : ℕ) : 2 ^ (s + 3) * (C s + 1) + 3 ≤ D (s + 3) := by
  induction s with
  | zero => norm_num [C_zero, D_succ, D_zero]
  | succ s ih =>
    have hm := Nat.mul_le_mul_left (2 ^ (s + 3)) ih
    change 2 ^ (s + 1 + 3) * (C (s + 1) + 1) + 3 ≤ D ((s + 3) + 1)
    rw [C_succ, D_succ]
    simp only [pow_succ] at hm ⊢
    have := pow_pos s
    nlinarith

lemma a_one : a 1 = 1 := by rw [a]

lemma a_succ (m : ℕ) (hm : 1 ≤ m) : a (m + 1) = 2 * a (m / a m) := by
  cases m with
  | zero => omega
  | succ m => rw [a]

lemma index_lower (m s : ℕ) (hm : 1 ≤ m) (ha : a m = 2 ^ s)
    (hu : ∀ j, m < D (j + 1) → a m ≤ 2 ^ j) : D s ≤ m := by
  cases s with
  | zero => simpa only [D_zero] using hm
  | succ s =>
    by_contra h
    have hb := hu s (by omega)
    have hp := pow_step_lt s
    rw [ha] at hb
    omega

-- The power property and both bounds are proved together at positive indices.
theorem inv : ∀ n : ℕ, 1 ≤ n →
    (∃ s, a n = 2 ^ s) ∧
    (∀ j, n < D (j + 1) → a n ≤ 2 ^ j) ∧
    (∀ i, C i < n → 2 ^ (i + 1) ≤ a n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        rw [a_one]
        refine ⟨⟨0, by norm_num⟩, ?_, ?_⟩
        · intro j hj
          exact pow_pos j
        · intro i hi
          have := C_pos i
          omega
      | succ m =>
        have hm := ih (m + 1) (by omega) (by omega)
        obtain ⟨s, hs⟩ := hm.1
        have hDm : D s ≤ m + 1 := index_lower (m + 1) s (by omega) hs hm.2.1
        have hpm : 2 ^ s ≤ m + 1 := le_trans (D_pow_lower s) hDm
        have hmC : m + 1 ≤ C s := by
          by_contra h
          have hb := hm.2.2 s (by omega)
          have hp := pow_step_lt s
          rw [hs] at hb
          omega
        let q := (m + 1) / 2 ^ s
        have hqpos : 1 ≤ q := Nat.div_pos hpm (pow_pos s)
        have hqlt : q < m + 2 := by
          have h : q ≤ m + 1 := Nat.div_le_self _ _
          omega
        have hq := ih q hqlt hqpos
        have ha : a (m + 2) = 2 * a q := by
          rw [a_succ (m + 1) (by omega), hs]
        change (∃ r, a (m + 2) = 2 ^ r) ∧
          (∀ j, m + 2 < D (j + 1) → a (m + 2) ≤ 2 ^ j) ∧
          (∀ i, C i < m + 2 → 2 ^ (i + 1) ≤ a (m + 2))
        rw [ha]
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨r, hr⟩ := hq.1
          exact ⟨r + 1, by rw [hr, pow_succ, Nat.mul_comm]⟩
        · intro j hj
          have hprod : m + 1 < 2 ^ j * D j := by
            rw [D_succ] at hj
            omega
          cases j with
          | zero => norm_num [D_zero] at hprod
          | succ j =>
            have hqD : q < D (j + 1) := by
              apply (Nat.div_lt_iff_lt_mul (pow_pos s)).2
              by_cases hsj : j + 1 ≤ s
              · have hp : 2 ^ (j + 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hsj
                have hm := Nat.mul_le_mul_right (D (j + 1)) hp
                nlinarith
              · have hsj' : s + 1 ≤ j + 1 := by omega
                have hc := C_lt s
                have hd := D_strict.monotone hsj'
                have hm := Nat.mul_le_mul_left (2 ^ s) hd
                nlinarith
            have hu := hq.2.1 j hqD
            rw [pow_succ]
            omega
        · intro i hi
          cases i with
          | zero =>
            obtain ⟨r, hr⟩ := hq.1
            have hp := pow_pos r
            rw [hr]
            norm_num
            omega
          | succ i =>
            have hmul : (C i + 1) * 2 ^ s ≤ m + 1 := by
              by_cases hsi : s ≤ i + 2
              · have hc : 2 ^ (i + 2) * (C i + 1) ≤ m + 1 := by
                  rw [C_succ] at hi
                  omega
                have hp : 2 ^ s ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by omega) hsi
                have hm := Nat.mul_le_mul_right (C i + 1) hp
                nlinarith
              · have hsbig : i + 3 ≤ s := by omega
                have hshift : s - 3 + 3 = s := by omega
                have hb := D_C_bound (s - 3)
                rw [hshift] at hb
                have hc := C_strict.monotone (show i ≤ s - 3 by omega)
                have hm := Nat.mul_le_mul_left (2 ^ s) (Nat.add_le_add_right hc 1)
                nlinarith
            have hdiv : C i + 1 ≤ q := (Nat.le_div_iff_mul_le (pow_pos s)).2 hmul
            have hb := hq.2.2 i (by omega)
            change 2 ^ ((i + 1) + 1) ≤ 2 * a q
            rw [pow_succ]
            omega

lemma at_D (j : ℕ) : a (D j) = 2 ^ j := by
  induction j with
  | zero => norm_num [D_zero, a_one]
  | succ j ih =>
    let m := 2 ^ j * D j
    have hm : 1 ≤ m := by
      dsimp [m]
      have := D_pos j
      have := pow_pos j
      nlinarith
    have hmD : m < D (j + 1) := by
      rw [D_succ]
      dsimp [m]
      omega
    have hinv := inv m hm
    have hupper := hinv.2.1 j hmD
    have hlower : 2 ^ j ≤ a m := by
      cases j with
      | zero =>
        obtain ⟨r, hr⟩ := hinv.1
        rw [hr]
        exact pow_pos r
      | succ j =>
        apply hinv.2.2 j
        have hc := C_lt j
        have hp := pow_pos j
        have hd := D_pos (j + 1)
        dsimp [m]
        rw [pow_succ]
        nlinarith
    have ham : a m = 2 ^ j := le_antisymm hupper hlower
    have hdiv : m / a m = D j := by
      rw [ham]
      exact Nat.mul_div_cancel_left _ (pow_pos j)
    calc
      a (D (j + 1)) = a (m + 1) := by rw [D_succ]
      _ = 2 * a (m / a m) := a_succ m hm
      _ = 2 ^ (j + 1) := by rw [hdiv, ih, pow_succ, Nat.mul_comm]

end OMA.A335901Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a335901.main := by
  intro n
  change IsLeast {k : ℕ | 1 ≤ k ∧ a k = 2 ^ n} (OMA.A335901Proof.D n)
  constructor
  · exact ⟨OMA.A335901Proof.D_pos n, OMA.A335901Proof.at_D n⟩
  · intro k hk
    exact OMA.A335901Proof.index_lower k n hk.1 hk.2 (OMA.A335901Proof.inv k hk.1).2.1
