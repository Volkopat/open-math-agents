import OMAStatements.S_oeis_a341763
import Mathlib

/-!
# OEIS A341763: every positive multiple of 3 reaches a narcissistic number greater than nine (namely 153) under the sum-of-cubes-of-digits map

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. (1) F(n) = n mod 3 since d^3 = d mod 3 and 10 = 1 mod 3; F(n) > 0 for n > 0. So positive multiples
of 3 stay positive multiples of 3. (2) A d-digit number has F(n) <= 729d, and 729d < 10^(d-1) for d
>= 5; for 2916 < n <= 9999, F(n) <= 2916 < n. So F(n) < n for all n > 2916, and every trajectory
enters [1, 2916]. (3) Finite check: for each of the 972 multiples of 3 in [3, 2916], the 13th
iterate is 153. (4) 153 = 1 + 125 + 27 is a 3-digit narcissistic number and a fixed point of F.
-/

open OMA.S_oeis_a341763

namespace OMA.A341763Proof

-- Structural recursion makes the finite certificate reducible by the kernel.
def cubeSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else (n % 10) ^ 3 + cubeSum f (n / 10)

lemma step_zero : step 0 = 0 := by
  simp [step]

lemma step_eq (n : ℕ) (hn : 0 < n) : step n = (n % 10) ^ 3 + step (n / 10) := by
  simp [step, Nat.digits_def' (by norm_num : 1 < 10) hn]

lemma cubeSum_eq (f n : ℕ) (h : n < f) : cubeSum f n = step n := by
  induction f generalizing n with
  | zero => omega
  | succ f ih =>
    by_cases hn : n = 0
    · simp [hn, cubeSum, step_zero]
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      have hd : n / 10 < n := Nat.div_lt_self hp (by norm_num)
      rw [cubeSum, if_neg hn, ih (n / 10) (by omega), step_eq n hp]

def fastStep (n : ℕ) : ℕ := cubeSum (n + 1) n

lemma fastStep_eq : fastStep = step := by
  funext n
  exact cubeSum_eq (n + 1) n (by omega)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma finite_check : ∀ k < 972, fastStep^[13] (3 * (k + 1)) = 153 := by
  decide +kernel

lemma step_pos (n : ℕ) (hn : 0 < n) : 0 < step n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [step_eq n hn]
    by_cases hq : 0 < n / 10
    · have := ih (n / 10) (Nat.div_lt_self hn (by norm_num)) hq
      omega
    · have hr : 0 < n % 10 := by omega
      have : 0 < (n % 10) ^ 3 := pow_pos hr 3
      omega

lemma cube_mod (d : ℕ) : d ^ 3 % 3 = d % 3 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt d (by norm_num : 0 < 3)
  interval_cases hd : d % 3 <;> norm_num

lemma sum_cube_mod (l : List ℕ) : (l.map (fun d => d ^ 3)).sum % 3 = l.sum % 3 := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [List.map_cons, List.sum_cons]
    calc
      (d ^ 3 + (l.map (fun x => x ^ 3)).sum) % 3 =
          (d ^ 3 % 3 + (l.map (fun x => x ^ 3)).sum % 3) % 3 := Nat.add_mod _ _ _
      _ = (d % 3 + l.sum % 3) % 3 := by rw [cube_mod, ih]
      _ = (d + l.sum) % 3 := (Nat.add_mod _ _ _).symm

lemma step_mod (n : ℕ) : step n % 3 = n % 3 := by
  exact (sum_cube_mod (Nat.digits 10 n)).trans (Nat.modEq_three_digits_sum n).symm

lemma step_dvd (n : ℕ) (hn : 3 ∣ n) : 3 ∣ step n := by
  apply Nat.dvd_of_mod_eq_zero
  rw [step_mod, Nat.mod_eq_zero_of_dvd hn]

lemma list_cube_bound (l : List ℕ) (hl : ∀ d ∈ l, d < 10) :
    (l.map (fun d => d ^ 3)).sum ≤ 729 * l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd : d ≤ 9 := by have := hl d (by simp); omega
    have hp : d ^ 3 ≤ 729 := by
      calc
        d ^ 3 ≤ 9 ^ 3 := Nat.pow_le_pow_left hd 3
        _ = 729 := by norm_num
    have ht := ih (fun x hx => hl x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

lemma step_bound (n : ℕ) : step n ≤ 729 * (Nat.digits 10 n).length := by
  exact list_cube_bound _ (fun d hd => Nat.digits_lt_base (by norm_num) hd)

-- This is the digit-length inequality multiplied by ten.
lemma power_bound (d : ℕ) (hd : 5 ≤ d) : 7290 * d < 10 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    rw [pow_succ]
    nlinarith

lemma step_lt (n : ℕ) (hn : 2916 < n) : step n < n := by
  have hb := step_bound n
  by_cases hd : (Nat.digits 10 n).length ≤ 4
  · omega
  · have hp := power_bound (Nat.digits 10 n).length (by omega)
    have hnz : n ≠ 0 := by omega
    have hpow := Nat.base_pow_length_digits_le 10 n (by norm_num) hnz
    omega

lemma reaches_small (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) (hb : n ≤ 2916) :
    ∃ t : ℕ, step^[t] n = 153 := by
  obtain ⟨k, rfl⟩ := h3
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨13, ?_⟩
  rw [← fastStep_eq]
  exact finite_check j (by omega)

lemma reaches (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) :
    ∃ t : ℕ, step^[t] n = 153 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hb : n ≤ 2916
    · exact reaches_small n hn h3 hb
    · obtain ⟨t, ht⟩ := ih (step n) (step_lt n (by omega)) (step_pos n hn) (step_dvd n h3)
      exact ⟨t + 1, by rw [Function.iterate_succ_apply, ht]⟩

lemma endpoint : Narcissistic 153 := by
  norm_num [Narcissistic, Nat.digits_def']

end OMA.A341763Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a341763.main := by
  intro n hn h3
  obtain ⟨t, ht⟩ := OMA.A341763Proof.reaches n hn h3
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    norm_num
  · rw [ht]
    exact OMA.A341763Proof.endpoint
