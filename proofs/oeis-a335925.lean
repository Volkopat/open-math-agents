import OMAStatements.S_oeis_a335925
import Mathlib

/-!
# OEIS A335925: the least index where each value appears is A000522

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2); the Lean text was written by
Codex from that proof sketch.

Write `E j = A000522 j`, so `E 0 = 1` and `E (j+1) = (j+1) * E j + 1`, and let `C 0 = 0`, `C 1 = 1`,
`C (i+2) = (i+3) * (C (i+1) + 1)`. By strong induction on `n ≥ 1`, two bounds hold together (`inv`):
`n < E j → a n ≤ j`, and `C i < n → i + 1 ≤ a n`. The upper bound at `n` uses the lower bound at
`n - 1` to show that the index `(n-1) / a (n-1)` is below `E (j-1)`; the lower bound at `n` uses the
upper bound at `n - 1` to show that this index is above `C (i-1)`. Two arithmetic facts link the two
sequences: `C i < i * E i` and `(s+4) * (C (s+1) + 1) ≤ E (s+3)`. Both bounds give
`a ((j+1) * E j) = j + 1`, hence `a (E (j+1)) = a (E j) + 1` (`at_E`), and the upper bound says no
smaller index reaches that value.
-/

open OMA.S_oeis_a335925

namespace OMA.A335925Proof

abbrev E := A000522

lemma E_zero : E 0 = 1 := by
  norm_num [E, A000522]

lemma E_succ (j : ℕ) : E (j + 1) = (j + 1) * E j + 1 := by
  unfold E A000522
  rw [Finset.sum_range_succ]
  rw [Nat.div_self (Nat.factorial_pos _)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ,
    Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (by simpa using hk))]

lemma E_pos (j : ℕ) : 1 ≤ E j := by
  cases j with
  | zero => rw [E_zero]
  | succ j => rw [E_succ]; omega

lemma E_strict : StrictMono E := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [E_succ]
  nlinarith [E_pos j]

lemma E_lower (j : ℕ) : j + 1 ≤ E j := by
  induction j with
  | zero => rw [E_zero]
  | succ j ih =>
    have h : E j < E (j + 1) := E_strict (Nat.lt_succ_self j)
    omega

def C : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 => (i + 3) * (C (i + 1) + 1)

lemma C_zero : C 0 = 0 := rfl

lemma C_one : C 1 = 1 := rfl

lemma C_step (i : ℕ) : C (i + 2) = (i + 3) * (C (i + 1) + 1) := by
  rfl

lemma C_strict : StrictMono C := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero => norm_num [C]
  | succ i =>
    change C (i + 1) < C (i + 2)
    rw [C_step]
    nlinarith

lemma C_lower (i : ℕ) : i ≤ C i := by
  induction i with
  | zero => omega
  | succ i ih =>
    have h : C i < C (i + 1) := C_strict (Nat.lt_succ_self i)
    omega

lemma C_lower_two (i : ℕ) : i + 6 ≤ C (i + 2) := by
  rw [C_step]
  have := C_lower (i + 1)
  nlinarith

lemma C_lt (i : ℕ) (hi : 1 ≤ i) : C i < i * E i := by
  cases i with
  | zero => omega
  | succ i =>
    induction i with
    | zero => norm_num [C, E_succ, E_zero]
    | succ i ih =>
      have hc : C (i + 1) + 1 ≤ (i + 1) * E (i + 1) := by
        have := ih (by omega)
        omega
      have hm := Nat.mul_le_mul_left (i + 3) hc
      have hp := E_pos (i + 1)
      change C (i + 2) < (i + 2) * E ((i + 1) + 1)
      rw [C_step, E_succ]
      nlinarith

lemma E_C_bound (s : ℕ) : (s + 4) * (C (s + 1) + 1) ≤ E (s + 3) := by
  cases s with
  | zero => norm_num [E_succ, E_zero, C]
  | succ s =>
    induction s with
    | zero => norm_num [E_succ, E_zero, C]
    | succ s ih =>
      have hc := C_lower_two s
      have hm := Nat.mul_le_mul_left (s + 5) ih
      have he := E_succ (s + 4)
      have hr := C_step (s + 1)
      have hnorm : s.succ.succ + 1 = s + 3 := by omega
      have hnorm2 : s.succ.succ + 3 = (s + 4) + 1 := by omega
      rw [hnorm, hnorm2, he, hr]
      nlinarith

lemma a_one : a 1 = 1 := by
  rw [a]

lemma a_succ (m : ℕ) (hm : 1 ≤ m) : a (m + 1) = a (m / a m) + 1 := by
  cases m with
  | zero => omega
  | succ m => rw [a]

-- The upper and lower bounds are proved together at every positive index.
theorem inv : ∀ n : ℕ, 1 ≤ n →
    (∀ j, n < E j → a n ≤ j) ∧ (∀ i, C i < n → i + 1 ≤ a n) := by
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
        constructor
        · intro j hj
          by_contra h
          have hj0 : j = 0 := by omega
          rw [hj0, E_zero] at hj
          omega
        · intro i hi
          have := C_lower i
          omega
      | succ m =>
        have hm := ih (m + 1) (by omega) (by omega)
        let t := a (m + 1)
        have ht : 1 ≤ t := hm.2 0 (by rw [C_zero]; omega)
        have het : E (t - 1) ≤ m + 1 := by
          by_contra h
          have hupper : t ≤ t - 1 := hm.1 (t - 1) (by omega)
          omega
        have htm : t ≤ m + 1 := by
          have := E_lower (t - 1)
          omega
        have hmct : m + 1 ≤ C t := by
          by_contra h
          have hlower : t + 1 ≤ t := hm.2 t (by omega)
          omega
        let q := (m + 1) / t
        have hqpos : 1 ≤ q := Nat.div_pos htm (by omega)
        have hqlt : q < m + 2 := by
          have h : q ≤ m + 1 := Nat.div_le_self _ _
          omega
        have hq := ih q hqlt hqpos
        have ha : a (m + 2) = a q + 1 := a_succ (m + 1) (by omega)
        change (∀ j, m + 2 < E j → a (m + 2) ≤ j) ∧
          (∀ i, C i < m + 2 → i + 1 ≤ a (m + 2))
        rw [ha]
        constructor
        · intro j hj
          cases j with
          | zero => rw [E_zero] at hj; omega
          | succ j =>
            have hprod : m + 1 < (j + 1) * E j := by
              rw [E_succ] at hj
              omega
            have hqE : q < E j := by
              apply (Nat.div_lt_iff_lt_mul (by omega : 0 < t)).2
              by_cases htj : j + 1 ≤ t
              · have hmul := Nat.mul_le_mul_right (E j) htj
                nlinarith
              · have htj' : t ≤ j := by omega
                have hc := C_lt t ht
                have he := E_strict.monotone htj'
                have hmul := Nat.mul_le_mul_left t he
                nlinarith
            have := hq.1 j hqE
            omega
        · intro i hi
          cases i with
          | zero => omega
          | succ i =>
            have hCq : C i < q := by
              cases i with
              | zero => rw [C_zero]; omega
              | succ i =>
                have hmul : (C (i + 1) + 1) * t ≤ m + 1 := by
                  by_cases hti : t ≤ i + 3
                  · have hc : (i + 3) * (C (i + 1) + 1) ≤ m + 1 := by
                      rw [C_step] at hi
                      omega
                    have hprod := Nat.mul_le_mul_right (C (i + 1) + 1) hti
                    nlinarith
                  · have htbig : i + 4 ≤ t := by omega
                    have hshift : t - 4 + 4 = t := by omega
                    have hshift1 : t - 4 + 1 = t - 3 := by omega
                    have hshift3 : t - 4 + 3 = t - 1 := by omega
                    have hb := E_C_bound (t - 4)
                    rw [hshift, hshift1, hshift3] at hb
                    have hci := C_strict.monotone (show i + 1 ≤ t - 3 by omega)
                    have hprod := Nat.mul_le_mul_left t (Nat.add_le_add_right hci 1)
                    nlinarith
                have hdiv : C (i + 1) + 1 ≤ q :=
                  (Nat.le_div_iff_mul_le (by omega : 0 < t)).2 hmul
                omega
            have := hq.2 i hCq
            omega

lemma at_E (j : ℕ) : a (E j) = j + 1 := by
  induction j with
  | zero => rw [E_zero, a_one]
  | succ j ih =>
    let m := (j + 1) * E j
    have hm : 1 ≤ m := by
      dsimp [m]
      have := E_pos j
      nlinarith
    have hmE : m < E (j + 1) := by
      rw [E_succ]
      dsimp [m]
      omega
    have hCm : C j < m := by
      dsimp [m]
      cases j with
      | zero => norm_num [C_zero, E_zero]
      | succ j =>
        have hc := C_lt (j + 1) (by omega)
        have hp := E_pos (j + 1)
        nlinarith
    have ham : a m = j + 1 :=
      le_antisymm ((inv m hm).1 (j + 1) hmE) ((inv m hm).2 j hCm)
    have hdiv : m / a m = E j := by
      rw [ham]
      exact Nat.mul_div_cancel_left _ (by omega)
    calc
      a (E (j + 1)) = a (m + 1) := by rw [E_succ]
      _ = a (m / a m) + 1 := a_succ m hm
      _ = j + 1 + 1 := by rw [hdiv, ih]

end OMA.A335925Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a335925.main := by
  intro n hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = j + 1 := by omega
  rw [hn']
  change IsLeast {k : ℕ | 1 ≤ k ∧ a k = j + 1} (OMA.A335925Proof.E j)
  constructor
  · exact ⟨OMA.A335925Proof.E_pos j, OMA.A335925Proof.at_E j⟩
  · intro k hk
    by_contra h
    have hu := (OMA.A335925Proof.inv k hk.1).1 j (by omega)
    have he := hk.2
    omega
