import OMAStatements.S_oeis_a000436
import Mathlib

/-!
# Proof of OEIS A000436 Conjecture

Let `c(j) = 1` if `j ≡ 0 (mod 3)`, `0` if `j ≡ 1 (mod 3)`, `-1` if `j ≡ 2 (mod 3)`.
Since `(1 + u) / (1 + u + u^2) = ∑_{j >= 0} c(j) u^j`, setting `u = exp(2*i*x) - 1` gives
`a(n) = (-4)^n * ∑_{j = 0..2n} c(j) * j! * S(2*n, j)`.

1. We prove `a(n) = f(n)` by strong induction using finite differences `Δ^j` on `H(r) = (r - 1)^(2n)`:
   `(r + 1)^(2n) + (r - 1)^(2n) - r^(2n) = ((1 + Δ + Δ^2) H)(r)`, and since
   `c(j) + c(j - 1) + c(j - 2) = 0` for all `j >= 2`, the sum telescopes to `H(1) = 0` for `n >= 1`.
2. Since `j! ∣ Δ^j (·^(2n)) (0)`, modulo any `k >= 1` all `j >= k` terms vanish.
3. For each `j < k`, `(-4)^n * Δ^j (·^(2n)) (0) = ∑_{r=0..j} (-1)^(j-r) * C(j, r) * (-4 * r^2)^n`,
   and by Euler's theorem `(-4 * r^2)^(n + phi(k)) ≡ (-4 * r^2)^n [ZMOD k]` for all `n >= k`.
-/

namespace OeisA000436Proof

open Finset

private def c (j : ℕ) : ℤ :=
  if j % 3 = 0 then 1 else if j % 3 = 2 then -1 else 0

private lemma c_recurrence (j : ℕ) : c (j + 2) + c (j + 1) + c j = 0 := by
  unfold c
  have h : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases h with h | h | h
  · have h1 : (j + 1) % 3 = 1 := by omega
    have h2 : (j + 2) % 3 = 2 := by omega
    simp [h, h1, h2]
  · have h1 : (j + 1) % 3 = 2 := by omega
    have h2 : (j + 2) % 3 = 0 := by omega
    simp [h, h1, h2]
  · have h1 : (j + 1) % 3 = 0 := by omega
    have h2 : (j + 2) % 3 = 1 := by omega
    simp [h, h1, h2]

private def Δ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) : ℤ :=
  ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + r)

private lemma Δ_zero (g : ℤ → ℤ) (x : ℤ) : Δ g 0 x = g x := by
  simp [Δ]

private lemma Δ_succ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ g (j + 1) x = Δ g j (x + 1) - Δ g j x := by
  unfold Δ
  rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * g (x + r))]
  rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * g (x + r))]
  rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + 1 + r))]
  rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + r))]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
             Nat.choose_zero_right, Nat.cast_zero, add_zero, Nat.cast_add]
  have hlast : x + ((j : ℤ) + 1) = x + 1 + (j : ℤ) := by ring
  rw [hlast]
  have hmid : ∑ r ∈ Finset.range j,
      (-1 : ℤ) ^ (j + 1 - (r + 1)) * (Nat.choose (j + 1) (r + 1) : ℤ) * g (x + ((r : ℤ) + 1)) =
      (∑ r ∈ Finset.range j, (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + 1 + (r : ℤ))) -
      (∑ r ∈ Finset.range j, (-1 : ℤ) ^ (j - (r + 1)) * (Nat.choose j (r + 1) : ℤ) * g (x + ((r : ℤ) + 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r < j := Finset.mem_range.mp hr
    have h1 : j + 1 - (r + 1) = j - r := by omega
    have h2 : j - r = (j - (r + 1)) + 1 := by omega
    have harg : x + ((r : ℤ) + 1) = x + 1 + (r : ℤ) := by ring
    rw [h1, Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.cast_add, harg, h2, pow_succ]
    ring
  rw [hmid, pow_succ]
  ring

private lemma Δ_shift (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g (y + 1)) j x = Δ g j x + Δ g (j + 1) x := by
  have h1 : Δ (fun y => g (y + 1)) j x = Δ g j (x + 1) := by
    unfold Δ
    apply Finset.sum_congr rfl
    intro r _
    congr 1; ring
  rw [h1, Δ_succ]
  ring

private lemma Δ_add (g₁ g₂ : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g₁ y + g₂ y) j x = Δ g₁ j x + Δ g₂ j x := by
  unfold Δ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_sub (g₁ g₂ : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g₁ y - g₂ y) j x = Δ g₁ j x - Δ g₂ j x := by
  unfold Δ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_const_mul (a : ℤ) (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => a * g y) j x = a * Δ g j x := by
  unfold Δ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_pow_eq_zero_of_lt (d j : ℕ) (hdj : d < j) :
    ∀ x : ℤ, Δ (fun y => y ^ d) j x = 0 := by
  induction d using Nat.strong_induction_on generalizing j with
  | h d ih =>
    intro x
    cases j with
    | zero => omega
    | succ j =>
      rw [Δ_succ]
      cases d with
      | zero =>
        have hconst : ∀ m : ℕ, ∀ y : ℤ, Δ (fun _ => (1 : ℤ)) m y = if m = 0 then 1 else 0 := by
          intro m
          induction m with
          | zero => intro y; simp [Δ]
          | succ m ihm => intro y; rw [Δ_succ, ihm, ihm]; simp
        simp only [pow_zero]
        rw [hconst, hconst]; simp
      | succ d =>
        have hbin : (fun y : ℤ => (y + 1) ^ (d + 1) - y ^ (d + 1)) =
            fun y : ℤ => ∑ i ∈ Finset.range (d + 1), (Nat.choose (d + 1) i : ℤ) * y ^ i := by
          ext y
          rw [add_pow, Finset.sum_range_succ]
          simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
          apply Finset.sum_congr rfl
          intro i _; ring
        have hstep : Δ (fun y => y ^ (d + 1)) j (x + 1) - Δ (fun y => y ^ (d + 1)) j x =
            Δ (fun y => (y + 1) ^ (d + 1) - y ^ (d + 1)) j x := by
          rw [Δ_sub]
          congr 1
          unfold Δ
          apply Finset.sum_congr rfl
          intro r _; congr 2; ring
        rw [hstep, hbin]
        have hsum : ∀ s : Finset ℕ, (∀ i ∈ s, i < d + 1) → (∀ i ∈ s, i < j) →
            Δ (fun y => ∑ i ∈ s, (Nat.choose (d + 1) i : ℤ) * y ^ i) j x = 0 := by
          intro s
          induction s using Finset.induction_on with
          | empty => intro _ _; simp [Δ]
          | @insert a s ha ihs =>
            intro hltd hlt
            have hfun : (fun y : ℤ => ∑ i ∈ insert a s, (Nat.choose (d + 1) i : ℤ) * y ^ i) =
                fun y : ℤ => (Nat.choose (d + 1) a : ℤ) * y ^ a +
                  ∑ i ∈ s, (Nat.choose (d + 1) i : ℤ) * y ^ i := by
              ext y; rw [Finset.sum_insert ha]
            rw [hfun, Δ_add, Δ_const_mul,
                ih a (hltd a (Finset.mem_insert_self a s)) j (hlt a (Finset.mem_insert_self a s)) x,
                mul_zero, zero_add]
            exact ihs (fun i hi => hltd i (Finset.mem_insert_of_mem hi))
              (fun i hi => hlt i (Finset.mem_insert_of_mem hi))
        exact hsum (Finset.range (d + 1))
          (fun i hi => Finset.mem_range.mp hi)
          (fun i hi => by have := Finset.mem_range.mp hi; omega)

private lemma Δ_shift_pow_eq_zero_of_lt (d j : ℕ) (hdj : d < j) (x : ℤ) :
    Δ (fun y => (y - 1) ^ d) j x = 0 := by
  have h : Δ (fun y => (y - 1) ^ d) j x = Δ (fun y => y ^ d) j (x - 1) := by
    unfold Δ
    apply Finset.sum_congr rfl
    intro r _
    congr 2; ring
  rw [h]
  exact Δ_pow_eq_zero_of_lt d j hdj (x - 1)

private lemma Δ_pow_zero_eq_stirling (n j : ℕ) :
    Δ (fun y => y ^ n) j 0 = (j.factorial * Nat.stirlingSecond n j : ℕ) := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [Δ]
    | succ j =>
      rw [Δ_pow_eq_zero_of_lt 0 (j + 1) (by omega) 0]
      simp [Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases j with
    | zero =>
      simp [Δ, zero_pow (Nat.succ_ne_zero n)]
    | succ j =>
      have hrec : Δ (fun y => y ^ (n + 1)) (j + 1) 0 =
          ((j + 1 : ℕ) : ℤ) * (Δ (fun y => y ^ n) (j + 1) 0 + Δ (fun y => y ^ n) j 0) := by
        have hstep1 : Δ (fun y => y ^ (n + 1)) (j + 1) 0 =
            ((j + 1 : ℕ) : ℤ) * Δ (fun y => (y + 1) ^ n) j 0 := by
          unfold Δ
          simp only [zero_add]
          rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ (n + 1))]
          simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          have hsub : j + 1 - (r + 1) = j - r := by omega
          have hch : (r + 1) * Nat.choose (j + 1) (r + 1) = (j + 1) * Nat.choose j r := by
            have := Nat.add_one_mul_choose_eq j r
            linarith
          have hchz : ((r + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r + 1) : ℤ) =
              ((j + 1 : ℕ) : ℤ) * (Nat.choose j r : ℤ) := by
            exact_mod_cast hch
          rw [hsub, pow_succ ((r + 1 : ℕ) : ℤ) n]
          push_cast
          calc (-1 : ℤ) ^ (j - r) * (Nat.choose (j + 1) (r + 1) : ℤ) * (((r : ℤ) + 1) ^ n * ((r : ℤ) + 1))
              = (-1 : ℤ) ^ (j - r) * (((r + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r + 1) : ℤ)) * ((r : ℤ) + 1) ^ n := by
                push_cast; ring
            _ = (-1 : ℤ) ^ (j - r) * (((j + 1 : ℕ) : ℤ) * (Nat.choose j r : ℤ)) * ((r : ℤ) + 1) ^ n := by
                rw [hchz]
            _ = ((j : ℤ) + 1) * ((-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * ((r : ℤ) + 1) ^ n) := by
                push_cast; ring
        rw [hstep1, Δ_shift (fun y => y ^ n) j 0]
        ring
      rw [hrec, ih (j + 1), ih j, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

private lemma fact_dvd_Δ_pow (n j : ℕ) :
    (j.factorial : ℤ) ∣ Δ (fun y => y ^ n) j 0 := by
  rw [Δ_pow_zero_eq_stirling]
  push_cast
  exact dvd_mul_right _ _

private lemma two_mul_even_binom_sum (r : ℤ) (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ℤ) * r ^ (2 * k) =
    (r + 1) ^ (2 * n) + (r - 1) ^ (2 * n) := by
  have h1 : (r + 1) ^ (2 * n) = ∑ i ∈ Finset.range (2 * n + 1), (Nat.choose (2 * n) i : ℤ) * r ^ i := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]
  have h2 : (r - 1) ^ (2 * n) = ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * (Nat.choose (2 * n) i : ℤ) * r ^ i := by
    have hneg : (r - 1) ^ (2 * n) = ((-r) + 1) ^ (2 * n) := by
      have : r - 1 = -((-r) + 1) := by ring
      rw [this, neg_pow, pow_mul]
      norm_num
    rw [hneg, add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  have hgen : ∀ m : ℕ, (g : ℕ → ℤ) →
      (∑ i ∈ Finset.range (2 * m + 1), (g i + (-1 : ℤ) ^ i * g i)) =
      2 * ∑ k ∈ Finset.range (m + 1), g (2 * k) := by
    intro m g
    induction m with
    | zero => simp; ring
    | succ m ihm =>
      have hsplit : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ, ihm]
      conv_rhs => rw [Finset.sum_range_succ]
      have hp1 : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      have hp2 : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]; norm_num
      rw [hp1, hp2, show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
      ring
  have hres := hgen n (fun i => (Nat.choose (2 * n) i : ℤ) * r ^ i)
  rw [← hres]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma c_telescope (D : ℕ → ℤ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range (N + 1), c j * (D j + D (j + 1) + D (j + 2))) =
    D 0 + D 1 + (c N + c (N - 1)) * D (N + 1) + c N * D (N + 2) := by
  induction N with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have hc0 : c 0 = 1 := by decide
      have hc1 : c 1 = 0 := by decide
      rw [hc0, hc1]
      ring
    | succ m =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have hrec := c_recurrence m
      have hsub1 : m + 1 - 1 = m := by omega
      have hsub2 : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hsub1, hsub2]
      calc D 0 + D 1 + (c (m + 1) + c m) * D (m + 1 + 1) + c (m + 1) * D (m + 1 + 2) +
            c (m + 1 + 1) * (D (m + 1 + 1) + D (m + 1 + 1 + 1) + D (m + 1 + 1 + 2))
          = D 0 + D 1 + (c (m + 2) + c (m + 1) + c m) * D (m + 2) +
            (c (m + 2) + c (m + 1)) * D (m + 3) + c (m + 2) * D (m + 4) := by ring
        _ = D 0 + D 1 + (c (m + 1 + 1) + c (m + 1)) * D (m + 1 + 1 + 1) +
            c (m + 1 + 1) * D (m + 1 + 1 + 2) := by rw [hrec]; ring

private def f (n : ℕ) : ℤ :=
  (-4 : ℤ) ^ n * ∑ j ∈ Finset.range (2 * n + 1), c j * Δ (fun y => y ^ (2 * n)) j 0

private lemma f_zero : f 0 = 1 := by
  unfold f
  rw [Finset.sum_range_one, Δ_zero]
  have hc0 : c 0 = 1 := by decide
  rw [hc0]
  norm_num

private lemma f_extend (k N : ℕ) (hkN : k ≤ N) :
    f k = (-4 : ℤ) ^ k * ∑ j ∈ Finset.range (2 * N + 1), c j * Δ (fun y => y ^ (2 * k)) j 0 := by
  unfold f
  congr 1
  have hsplit : Finset.range (2 * N + 1) =
      Finset.range (2 * k + 1) ∪ (Finset.range (2 * N + 1) \ Finset.range (2 * k + 1)) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
  rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
  have htail : ∑ j ∈ Finset.range (2 * N + 1) \ Finset.range (2 * k + 1),
      c j * Δ (fun y => y ^ (2 * k)) j 0 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_range] at hj
    rw [Δ_pow_eq_zero_of_lt (2 * k) j (by omega) 0, mul_zero]
  rw [htail, add_zero]

private lemma f_recurrence (n : ℕ) (hn : 1 ≤ n) :
    f n = 2 * ∑ k ∈ Finset.range n,
      (-1 : ℤ) ^ (n - 1 - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) * f k := by
  suffices hzero :
      2 * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) * f k) - f n = 0 by
    rw [Finset.sum_range_succ] at hzero
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, mul_one] at hzero
    have hneg : ∑ k ∈ Finset.range n,
        (-1 : ℤ) ^ (n - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) * f k =
        -(∑ k ∈ Finset.range n,
          (-1 : ℤ) ^ (n - 1 - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) * f k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hsub : n - k = (n - 1 - k) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    rw [hneg] at hzero
    linarith
  -- Substitute f_extend k n into the sum
  have hsum1 : 2 * ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) * f k =
      (-4 : ℤ) ^ n * ∑ j ∈ Finset.range (2 * n + 1),
        c j * Δ (fun y => (y + 1) ^ (2 * n) + (y - 1) ^ (2 * n)) j 0 := by
    have hstep1 : ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) * f k =
        ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (2 * n + 1),
          (-4 : ℤ) ^ n * c j * ((Nat.choose (2 * n) (2 * k) : ℤ) * Δ (fun y => y ^ (2 * k)) j 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [f_extend k n hkn, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hpow : (-1 : ℤ) ^ (n - k) * 4 ^ (n - k) * (-4 : ℤ) ^ k = (-4 : ℤ) ^ n := by
        rw [← mul_pow, show (-1 : ℤ) * 4 = -4 by norm_num, ← pow_add, Nat.sub_add_cancel hkn]
      calc (-1 : ℤ) ^ (n - k) * (Nat.choose (2 * n) (2 * k) : ℤ) * 4 ^ (n - k) *
            ((-4 : ℤ) ^ k * (c j * Δ (fun y => y ^ (2 * k)) j 0))
          = ((-1 : ℤ) ^ (n - k) * 4 ^ (n - k) * (-4 : ℤ) ^ k) * c j *
            ((Nat.choose (2 * n) (2 * k) : ℤ) * Δ (fun y => y ^ (2 * k)) j 0) := by ring
        _ = (-4 : ℤ) ^ n * c j * ((Nat.choose (2 * n) (2 * k) : ℤ) * Δ (fun y => y ^ (2 * k)) j 0) := by
            rw [hpow]
    rw [hstep1, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    rw [show 2 * ((-4 : ℤ) ^ n * c j * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℤ) * Δ (fun y => y ^ (2 * k)) j 0) =
        (-4 : ℤ) ^ n * (c j * (2 * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℤ) * Δ (fun y => y ^ (2 * k)) j 0)) by ring]
    congr 2
    -- Show 2 * ∑_{k=0..n} C(2n, 2k) * Δ (·^(2k)) j 0 = Δ (fun y => (y+1)^(2n) + (y-1)^(2n)) j 0
    unfold Δ
    simp only [zero_add]
    have hinner : ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ℤ) *
        ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * (r : ℤ) ^ (2 * k) =
        ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) *
          ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ℤ) * (r : ℤ) ^ (2 * k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hinner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [← two_mul_even_binom_sum (r : ℤ) n]
    ring
  rw [hsum1]
  unfold f
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hH : ∀ j : ℕ,
      c j * Δ (fun y => (y + 1) ^ (2 * n) + (y - 1) ^ (2 * n)) j 0 -
      c j * Δ (fun y => y ^ (2 * n)) j 0 =
      c j * (Δ (fun y => (y - 1) ^ (2 * n)) j 0 +
             Δ (fun y => (y - 1) ^ (2 * n)) (j + 1) 0 +
             Δ (fun y => (y - 1) ^ (2 * n)) (j + 2) 0) := by
    intro j
    rw [← mul_sub, ← Δ_sub]
    congr 1
    set H : ℤ → ℤ := fun y => (y - 1) ^ (2 * n)
    have hfun : (fun y : ℤ => (y + 1) ^ (2 * n) + (y - 1) ^ (2 * n) - y ^ (2 * n)) =
        fun y : ℤ => H (y + 2) - H (y + 1) + H y := by
      ext y; simp only [H]; ring
    rw [hfun, Δ_add, Δ_sub]
    have h1 : Δ (fun y => H (y + 1)) j 0 = Δ H j 0 + Δ H (j + 1) 0 := Δ_shift H j 0
    have h2 : Δ (fun y => H (y + 2)) j 0 = Δ H j 0 + 2 * Δ H (j + 1) 0 + Δ H (j + 2) 0 := by
      have : (fun y : ℤ => H (y + 2)) = fun y => (fun z => H (z + 1)) (y + 1) := by
        ext y; congr 1; ring
      rw [this, Δ_shift (fun z => H (z + 1)) j 0, Δ_shift H j 0, Δ_shift H (j + 1) 0]
      ring
    rw [h1, h2]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hH j)]
  rw [c_telescope (fun j => Δ (fun y => (y - 1) ^ (2 * n)) j 0) (2 * n) (by omega)]
  rw [Δ_shift_pow_eq_zero_of_lt (2 * n) (2 * n + 1) (by omega) 0,
      Δ_shift_pow_eq_zero_of_lt (2 * n) (2 * n + 2) (by omega) 0]
  rw [Δ_zero, Δ_succ, Δ_zero, Δ_zero]
  simp [zero_pow (by omega : 2 * n ≠ 0)]

private lemma a_eq_f (n : ℕ) : OMA.S_oeis_a000436.a n = f n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [OMA.S_oeis_a000436.a, f_zero]
    | succ n =>
      rw [OMA.S_oeis_a000436.a, f_recurrence (n + 1) (by omega)]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih k.1 k.2]
      simp

private lemma pow_add_totient_modEq (r : ℕ) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → r ^ (n + Nat.totient k) ≡ r ^ n [MOD k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    by_cases hk1 : k = 1
    · subst hk1; exact Nat.modEq_one
    · set p := k.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      set e := k.factorization p
      have he_pos : 1 ≤ e :=
        (Nat.Prime.dvd_iff_one_le_factorization hp (by omega)).mp (Nat.minFac_dvd k)
      set q := p ^ e
      have hq_dvd : q ∣ k := Nat.ordProj_dvd k p
      set m := k / q
      have hqm : q * m = k := Nat.mul_div_cancel' hq_dvd
      have hcop : Nat.Coprime q m := by
        have hpm : ¬ p ∣ m := by
          intro hpm
          have hpow1 : p ^ (e + 1) ∣ k := by
            rcases hpm with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc k = p ^ e * m := hqm.symm
              _ = p ^ e * (p * t) := by rw [ht]
              _ = p ^ (e + 1) * t := by rw [pow_succ]; ring
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hpow1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, mul_zero] at hqm; omega
        · exact hpos
      have hm_lt : m < k := by
        have hq_gt1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
        nlinarith
      suffices h : r ^ (n + Nat.totient k) ≡ r ^ n [MOD q * m] by rwa [hqm] at h
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      constructor
      · by_cases hpr : p ∣ r
        · have he_le : e ≤ n := by
            have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
            have h2 : q ≤ k := Nat.le_of_dvd (by omega) hq_dvd
            omega
          have hd1 : q ∣ r ^ n := by
            rcases hpr with ⟨t, rfl⟩
            rw [mul_pow]
            exact dvd_mul_of_dvd_left (pow_dvd_pow p he_le) _
          have hd2 : q ∣ r ^ (n + Nat.totient k) :=
            dvd_trans hd1 (pow_dvd_pow r (Nat.le_add_right n _))
          rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd1, Nat.mod_eq_zero_of_dvd hd2]
        · have hcop_rq : Nat.Coprime r q := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right e
          have heuler : r ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop_rq
          have htdvd : Nat.totient q ∣ Nat.totient k := Nat.totient_dvd_of_dvd hq_dvd
          rcases htdvd with ⟨t, ht⟩
          have hphi : r ^ Nat.totient k ≡ 1 [MOD q] := by
            rw [ht, pow_mul]
            simpa using heuler.pow t
          rw [pow_add]
          simpa using (Nat.ModEq.refl (r ^ n)).mul hphi
      · have hm_dvd : m ∣ k := ⟨q, by linarith⟩
        have htdvd : Nat.totient m ∣ Nat.totient k := Nat.totient_dvd_of_dvd hm_dvd
        rcases htdvd with ⟨t, ht⟩
        rw [ht]
        have hiter : ∀ s : ℕ, r ^ (n + Nat.totient m * s) ≡ r ^ n [MOD m] := by
          intro s
          induction s with
          | zero => simp [Nat.ModEq]
          | succ s ihs =>
            have hstep : r ^ (n + Nat.totient m * s + Nat.totient m) ≡
                r ^ (n + Nat.totient m * s) [MOD m] :=
              ih m hm_lt hm_pos (n + Nat.totient m * s) (by omega)
            rw [show n + Nat.totient m * (s + 1) = n + Nat.totient m * s + Nat.totient m by ring]
            exact hstep.trans ihs
        exact hiter t

private lemma neg_one_pow_totient (k : ℕ) (hk : 1 ≤ k) :
    ((-1 : ℤ) ^ Nat.totient k : ZMod k) = 1 := by
  by_cases hk1 : k = 1
  · subst hk1; exact Subsingleton.elim _ _
  · by_cases hk2 : k = 2
    · subst hk2; decide
    · have hev : Even (Nat.totient k) := Nat.totient_even (by omega)
      rcases hev with ⟨m, hm⟩
      rw [hm, show m + m = 2 * m by omega, pow_mul]
      norm_num

end OeisA000436Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000436.main := by
  intro k hk
  refine ⟨k, fun n hn => ?_⟩
  rw [OeisA000436Proof.a_eq_f, OeisA000436Proof.a_eq_f]
  rw [← ZMod.intCast_eq_intCast_iff]
  have htrunc : ∀ m : ℕ, k ≤ m →
      (OeisA000436Proof.f m : ZMod k) =
      (-4 : ZMod k) ^ m * ∑ j ∈ Finset.range k,
        (OeisA000436Proof.c j : ZMod k) * (OeisA000436Proof.Δ (fun y => y ^ (2 * m)) j 0 : ZMod k) := by
    intro m hm
    unfold OeisA000436Proof.f
    push_cast
    congr 1
    have hsplit : Finset.range (2 * m + 1) =
        Finset.range k ∪ (Finset.range (2 * m + 1) \ Finset.range k) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have htail : ∑ j ∈ Finset.range (2 * m + 1) \ Finset.range k,
        (OeisA000436Proof.c j : ZMod k) * (OeisA000436Proof.Δ (fun y => y ^ (2 * m)) j 0 : ZMod k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_range] at hj
      have hdvd : (k : ℤ) ∣ OeisA000436Proof.Δ (fun y => y ^ (2 * m)) j 0 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hk (by omega)))
          (OeisA000436Proof.fact_dvd_Δ_pow (2 * m) j)
      have h0 : (OeisA000436Proof.Δ (fun y => y ^ (2 * m)) j 0 : ZMod k) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mpr hdvd
      rw [h0, mul_zero]
    rw [htail, add_zero]
  rw [htrunc (n + Nat.totient k) (by omega), htrunc n hn]
  have hneg4 : (-4 : ZMod k) ^ (n + Nat.totient k) = (-4 : ZMod k) ^ n := by
    have h4 : (4 : ZMod k) ^ (n + Nat.totient k) = (4 : ZMod k) ^ n := by
      have := OeisA000436Proof.pow_add_totient_modEq 4 k hk n hn
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ k).mpr this
    have hsign : (-1 : ZMod k) ^ (n + Nat.totient k) = (-1 : ZMod k) ^ n := by
      rw [pow_add]
      have h1 := OeisA000436Proof.neg_one_pow_totient k hk
      push_cast at h1
      rw [h1, mul_one]
    have hmul : (-4 : ZMod k) = (-1 : ZMod k) * (4 : ZMod k) := by ring
    rw [hmul, mul_pow, mul_pow, hsign, h4]
  rw [hneg4]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold OeisA000436Proof.Δ
  simp only [zero_add]
  push_cast
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have hr : (r ^ 2 : ZMod k) ^ (n + Nat.totient k) = (r ^ 2 : ZMod k) ^ n := by
    have := OeisA000436Proof.pow_add_totient_modEq (r ^ 2) k hk n hn
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ k).mpr this
  rw [show 2 * (n + Nat.totient k) = 2 * (n + Nat.totient k) from rfl, pow_mul, pow_mul]
  exact hr
