import OMAStatements.S_oeis_a245322
import Mathlib

/-!
# Proof of OEIS A245322 Conjectures

Using the `sOdd n m = m! * partOdd n m` engine (where `(2 : ℤ)^m * sOdd n m = ∑ (-1)^(m-r) C(m,r) (2r-m)^n`):
1. For `p = 2`, all `m >= 2` terms vanish mod 2 (`2 ∣ m!`), leaving `m = 1` where
   `partOdd k 1 = if k % 2 = 1 then 1 else 0`, so `a(2n)` is even and `a(2n - 1)` is odd.
2. For `p ≡ 1 (mod 4)`, `4 ∣ (p - 1)`, so `(-1)^((n + (p - 1) - m) / 2) = (-1)^((n - m) / 2)`,
   and both `m^n` and `sOdd n m` are `(p - 1)`-periodic mod `p`.
3. For `p ≡ 3 (mod 4)`, `4 ∣ 2 * (p - 1)`, so `(-1)^((n + 2 * (p - 1) - m) / 2) = (-1)^((n - m) / 2)`,
   and both `m^n` and `sOdd n m` are `2 * (p - 1)`-periodic mod `p`.
-/

namespace OeisA245322Proof

open Finset

private lemma partOdd_zero_zero : OMA.S_oeis_a245322.partOdd 0 0 = 1 := by
  rw [OMA.S_oeis_a245322.partOdd]

private lemma partOdd_succ_zero (n : ℕ) : OMA.S_oeis_a245322.partOdd (n + 1) 0 = 0 := by
  rw [OMA.S_oeis_a245322.partOdd]

private lemma partOdd_zero_succ (m : ℕ) : OMA.S_oeis_a245322.partOdd 0 (m + 1) = 0 := by
  rw [OMA.S_oeis_a245322.partOdd]

private lemma partOdd_succ_succ (n m : ℕ) :
    OMA.S_oeis_a245322.partOdd (n + 1) (m + 1) =
      ∑ j ∈ Finset.range (n / 2 + 1),
        Nat.choose n (2 * j) * OMA.S_oeis_a245322.partOdd (n - 2 * j) m := by
  rw [OMA.S_oeis_a245322.partOdd]

private lemma partOdd_eq_zero_of_lt :
    ∀ n m : ℕ, n < m → OMA.S_oeis_a245322.partOdd n m = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m hnm
    cases n with
    | zero =>
      cases m with
      | zero => omega
      | succ m => exact partOdd_zero_succ m
    | succ n =>
      cases m with
      | zero => omega
      | succ m =>
        rw [partOdd_succ_succ]
        apply Finset.sum_eq_zero
        intro j _
        rw [ih (n - 2 * j) (by omega) m (by omega), mul_zero]

private def sOdd : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | n, m + 1 => ∑ k ∈ Finset.range (n + 1),
      Nat.choose n k * (if k % 2 = 1 then 1 else 0) * sOdd (n - k) m

private lemma sOdd_zero_succ (m : ℕ) : sOdd 0 (m + 1) = 0 := by
  simp [sOdd]

private lemma sum_odd_eq_sum_even (n : ℕ) (g : ℕ → ℕ) :
    ∑ k ∈ Finset.range (n + 1), (if (k + 1) % 2 = 1 then 1 else 0) * g k =
      ∑ j ∈ Finset.range (n / 2 + 1), g (2 * j) := by
  have hfilter : ∑ k ∈ Finset.range (n + 1), (if (k + 1) % 2 = 1 then 1 else 0) * g k =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 2 = 0), g k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k % 2 = 0
    · have : (k + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : ¬ (k + 1) % 2 = 1 := by omega
      simp [h, this]
  rw [hfilter]
  refine Finset.sum_bij (fun k _ => k / 2) ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
  · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2; omega
  · intro j hj
    refine ⟨2 * j, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
  · intro k hk
    simp only [Finset.mem_filter] at hk
    rw [show 2 * (k / 2) = k by omega]

private lemma choose_comm_sub (n a b : ℕ) (_hab : a + b ≤ n) :
    Nat.choose n a * Nat.choose (n - a) b = Nat.choose n b * Nat.choose (n - b) a := by
  have h1 : Nat.choose n (a + b) * Nat.choose (a + b) a = Nat.choose n a * Nat.choose (n - a) b := by
    have := Nat.choose_mul (n := n) (k := a + b) (s := a) (by omega)
    rwa [Nat.add_sub_cancel_left] at this
  have h2 : Nat.choose n (b + a) * Nat.choose (b + a) b = Nat.choose n b * Nat.choose (n - b) a := by
    have := Nat.choose_mul (n := n) (k := b + a) (s := b) (by omega)
    rwa [Nat.add_sub_cancel_left] at this
  rw [← h1, ← h2, add_comm b a]
  congr 1
  have hsym := Nat.choose_symm (n := a + b) (k := a) (by omega)
  rw [Nat.add_sub_cancel_left] at hsym
  exact hsym.symm

private lemma sOdd_succ_succ :
    ∀ m n : ℕ, sOdd (n + 1) (m + 1) =
      (m + 1) * ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * j) * sOdd (n - 2 * j) m := by
  intro m
  induction m with
  | zero =>
    intro n
    rw [sOdd, Nat.zero_add, one_mul]
    rw [Finset.sum_range_succ']
    have hz : (if 0 % 2 = 1 then 1 else 0) = 0 := by decide
    rw [hz, mul_zero, zero_mul, add_zero]
    have h1 : ∑ k ∈ Finset.range (n + 1),
          Nat.choose (n + 1) (k + 1) * (if (k + 1) % 2 = 1 then 1 else 0) * sOdd (n + 1 - (k + 1)) 0 =
        ∑ k ∈ Finset.range (n + 1),
          (if (k + 1) % 2 = 1 then 1 else 0) * (Nat.choose n k * sOdd (n - k) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.add_sub_add_right, Nat.choose_succ_succ]
      by_cases hkn_eq : k = n
      · subst hkn_eq; simp
      · have h0 : sOdd (n - k) 0 = 0 := by
          have : ∃ t, n - k = t + 1 := ⟨n - k - 1, by omega⟩
          rcases this with ⟨t, ht⟩; rw [ht]; rfl
        simp [h0]
    rw [h1, sum_odd_eq_sum_even]
  | succ m ih =>
    intro n
    conv_lhs => rw [sOdd]
    rw [Finset.sum_range_succ']
    have hz : (if 0 % 2 = 1 then 1 else 0) = 0 := by decide
    rw [hz, mul_zero, zero_mul, add_zero]
    have hsplit : ∑ k ∈ Finset.range (n + 1),
          Nat.choose (n + 1) (k + 1) * (if (k + 1) % 2 = 1 then 1 else 0) * sOdd (n + 1 - (k + 1)) (m + 1) =
        (∑ k ∈ Finset.range (n + 1),
          (if (k + 1) % 2 = 1 then 1 else 0) * (Nat.choose n k * sOdd (n - k) (m + 1))) +
        (∑ k ∈ Finset.range (n + 1),
          Nat.choose n (k + 1) * (if (k + 1) % 2 = 1 then 1 else 0) * sOdd (n - k) (m + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_sub_add_right, Nat.choose_succ_succ]
      ring
    rw [hsplit, sum_odd_eq_sum_even]
    have hsecond : ∑ k ∈ Finset.range (n + 1),
          Nat.choose n (k + 1) * (if (k + 1) % 2 = 1 then 1 else 0) * sOdd (n - k) (m + 1) =
        (m + 1) * ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * j) * sOdd (n - 2 * j) (m + 1) := by
      have hreidx : ∑ k ∈ Finset.range (n + 1),
            Nat.choose n (k + 1) * (if (k + 1) % 2 = 1 then 1 else 0) * sOdd (n - k) (m + 1) =
          ∑ r ∈ Finset.range (n + 1),
            Nat.choose n r * (if r % 2 = 1 then 1 else 0) * sOdd (n - r + 1) (m + 1) := by
        rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), zero_mul, zero_mul, add_zero]
        rw [Finset.sum_range_succ']
        rw [hz, mul_zero, zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro k hk
        have : k < n := Finset.mem_range.mp hk
        rw [show n - k = n - (k + 1) + 1 by omega]
      rw [hreidx]
      have hexp : ∑ r ∈ Finset.range (n + 1),
            Nat.choose n r * (if r % 2 = 1 then 1 else 0) * sOdd (n - r + 1) (m + 1) =
          (m + 1) * ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.range ((n - r) / 2 + 1),
            Nat.choose n r * (if r % 2 = 1 then 1 else 0) *
              (Nat.choose (n - r) (2 * j) * sOdd (n - r - 2 * j) m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [ih (n - r), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring
      rw [hexp]
      congr 1
      have hswap :
          ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.range ((n - r) / 2 + 1),
            Nat.choose n r * (if r % 2 = 1 then 1 else 0) *
              (Nat.choose (n - r) (2 * j) * sOdd (n - r - 2 * j) m) =
          ∑ j ∈ Finset.range (n / 2 + 1), ∑ r ∈ Finset.range (n - 2 * j + 1),
            Nat.choose n (2 * j) *
              (Nat.choose (n - 2 * j) r * (if r % 2 = 1 then 1 else 0) * sOdd (n - 2 * j - r) m) := by
        trans (∑ x ∈ (Finset.range (n + 1)).sigma (fun r => Finset.range ((n - r) / 2 + 1)),
            Nat.choose n x.1 * (if x.1 % 2 = 1 then 1 else 0) *
              (Nat.choose (n - x.1) (2 * x.2) * sOdd (n - x.1 - 2 * x.2) m))
        · exact Finset.sum_sigma' (Finset.range (n + 1)) (fun r => Finset.range ((n - r) / 2 + 1))
            (fun r j => Nat.choose n r * (if r % 2 = 1 then 1 else 0) *
              (Nat.choose (n - r) (2 * j) * sOdd (n - r - 2 * j) m))
        · trans (∑ y ∈ (Finset.range (n / 2 + 1)).sigma (fun j => Finset.range (n - 2 * j + 1)),
              Nat.choose n (2 * y.1) *
                (Nat.choose (n - 2 * y.1) y.2 * (if y.2 % 2 = 1 then 1 else 0) * sOdd (n - 2 * y.1 - y.2) m))
          · refine Finset.sum_bij (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
            · intro ⟨r, j⟩ hx
              simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
              omega
            · intro ⟨r1, j1⟩ _ ⟨r2, j2⟩ _ heq
              simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
              rcases heq with ⟨rfl, rfl⟩
              rfl
            · intro ⟨j, r⟩ hy
              refine ⟨⟨r, j⟩, ?_, rfl⟩
              simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
              omega
            · intro ⟨r, j⟩ hx
              simp only [Finset.mem_sigma, Finset.mem_range] at hx
              have hch := choose_comm_sub n r (2 * j) (by omega)
              have hsub : n - r - 2 * j = n - 2 * j - r := by omega
              rw [hsub]
              calc Nat.choose n r * (if r % 2 = 1 then 1 else 0) *
                    (Nat.choose (n - r) (2 * j) * sOdd (n - 2 * j - r) m)
                  = (Nat.choose n r * Nat.choose (n - r) (2 * j)) *
                      (if r % 2 = 1 then 1 else 0) * sOdd (n - 2 * j - r) m := by ring
                _ = (Nat.choose n (2 * j) * Nat.choose (n - 2 * j) r) *
                      (if r % 2 = 1 then 1 else 0) * sOdd (n - 2 * j - r) m := by rw [hch]
                _ = Nat.choose n (2 * j) *
                      (Nat.choose (n - 2 * j) r * (if r % 2 = 1 then 1 else 0) * sOdd (n - 2 * j - r) m) := by ring
          · exact (Finset.sum_sigma' (Finset.range (n / 2 + 1)) (fun j => Finset.range (n - 2 * j + 1))
              (fun j r => Nat.choose n (2 * j) *
                (Nat.choose (n - 2 * j) r * (if r % 2 = 1 then 1 else 0) * sOdd (n - 2 * j - r) m))).symm
      rw [hswap]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      congr 1
      cases (n - 2 * j) <;> simp [sOdd]
    rw [hsecond]; ring

private lemma sOdd_eq_fact_mul_partOdd :
    ∀ n m : ℕ, sOdd n m = m.factorial * OMA.S_oeis_a245322.partOdd n m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m
    cases m with
    | zero =>
      cases n with
      | zero => simp [sOdd, partOdd_zero_zero]
      | succ n => simp [sOdd, partOdd_succ_zero]
    | succ m =>
      cases n with
      | zero => simp [sOdd_zero_succ, partOdd_zero_succ]
      | succ n =>
        rw [sOdd_succ_succ, partOdd_succ_succ, Nat.factorial_succ, mul_assoc, Finset.mul_sum, Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [ih (n - 2 * j) (by omega) m]
        ring

private lemma two_mul_odd_binom_sum (x : ℤ) (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * x ^ (n - k) =
      (x + 1) ^ n - (x - 1) ^ n := by
  have h1 : (x + 1) ^ n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * x ^ (n - k) := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _; rw [one_pow, one_mul, mul_comm]
  have h2 : (x - 1) ^ n = ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * x ^ (n - k) := by
    have : x - 1 = (-1) + x := by ring
    rw [this, add_pow]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [h1, h2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k % 2 = 1
  · have hneg : (-1 : ℤ) ^ k = -1 := by
      have : k = 2 * (k / 2) + 1 := by omega
      rw [this, pow_succ, pow_mul]; norm_num
    simp only [hk, ↓reduceIte, hneg]; ring
  · have hpos : (-1 : ℤ) ^ k = 1 := by
      have : k = 2 * (k / 2) := by omega
      rw [this, pow_mul]; norm_num
    simp only [hk, ↓reduceIte, hpos]; ring

private lemma two_pow_mul_sOdd :
    ∀ m n : ℕ, (2 : ℤ) ^ m * (sOdd n m : ℤ) =
      ∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * (r : ℤ) - (m : ℤ)) ^ n := by
  intro m
  induction m with
  | zero =>
    intro n
    cases n with
    | zero => simp [sOdd]
    | succ n => simp [sOdd]
  | succ m ih =>
    intro n
    simp only [sOdd]
    push_cast
    rw [pow_succ, mul_comm ((2 : ℤ) ^ m) 2, mul_assoc, Finset.mul_sum]
    have hstep1 : (2 : ℤ) ^ m * ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (sOdd (n - k) m : ℤ) =
        ∑ k ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) *
            ((Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (2 * (r : ℤ) - (m : ℤ)) ^ (n - k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hterm := ih (n - k)
      calc (2 : ℤ) ^ m * ((Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (sOdd (n - k) m : ℤ))
          = ((Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0)) * ((2 : ℤ) ^ m * (sOdd (n - k) m : ℤ)) := by ring
        _ = ((Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0)) *
              ∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * (r : ℤ) - (m : ℤ)) ^ (n - k) := by
                rw [hterm]
        _ = ∑ r ∈ Finset.range (m + 1),
              (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) *
                ((Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (2 * (r : ℤ) - (m : ℤ)) ^ (n - k)) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
    rw [← Finset.mul_sum, hstep1, Finset.sum_comm, Finset.mul_sum]
    have hstep2 : ∑ r ∈ Finset.range (m + 1),
          2 * ∑ k ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) *
              ((Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (2 * (r : ℤ) - (m : ℤ)) ^ (n - k)) =
        (∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n) -
        (∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * (r : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.mul_sum]
      have hbin := two_mul_odd_binom_sum (2 * (r : ℤ) - (m : ℤ)) n
      have hadd1 : 2 * (r : ℤ) - (m : ℤ) + 1 = 2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      have hsub1 : 2 * (r : ℤ) - (m : ℤ) - 1 = 2 * (r : ℤ) - ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hadd1, hsub1] at hbin
      calc 2 * ((-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) *
              ∑ k ∈ Finset.range (n + 1),
                (Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (2 * (r : ℤ) - (m : ℤ)) ^ (n - k))
          = (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) *
              (2 * ∑ k ∈ Finset.range (n + 1),
                (Nat.choose n k : ℤ) * (if k % 2 = 1 then (1 : ℤ) else 0) * (2 * (r : ℤ) - (m : ℤ)) ^ (n - k)) := by ring
        _ = (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) *
              ((2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n - (2 * (r : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n) := by rw [hbin]
        _ = _ := by ring
    rw [hstep2]
    have hrhs_cast : ∑ x ∈ Finset.range (m + 1 + 1),
          (-1 : ℤ) ^ (m + 1 - x) * (Nat.choose (m + 1) x : ℤ) * (2 * (x : ℤ) - ((m : ℤ) + 1)) ^ n =
        ∑ r ∈ Finset.range (m + 1 + 1),
          (-1 : ℤ) ^ (m + 1 - r) * (Nat.choose (m + 1) r : ℤ) * (2 * (r : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n := by
      push_cast; rfl
    rw [hrhs_cast]
    rw [Finset.sum_range_succ' (fun r => (-1 : ℤ) ^ (m + 1 - r) * (Nat.choose (m + 1) r : ℤ) * (2 * (r : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n)]
    rw [Finset.sum_range_succ' (fun r => (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * (r : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n)]
    rw [Finset.sum_range_succ (fun r => (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n)]
    rw [Finset.sum_range_succ (fun r => (-1 : ℤ) ^ (m + 1 - (r + 1)) * (Nat.choose (m + 1) (r + 1) : ℤ) * (2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n)]
    simp only [Nat.sub_zero, Nat.sub_self, pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul,
               Nat.add_sub_add_right]
    have hmid : ∑ r ∈ Finset.range m,
          (-1 : ℤ) ^ (m - r) * (Nat.choose m r : ℤ) * (2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n -
        ∑ r ∈ Finset.range m,
          (-1 : ℤ) ^ (m - (r + 1)) * (Nat.choose m (r + 1) : ℤ) * (2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n =
        ∑ r ∈ Finset.range m,
          (-1 : ℤ) ^ (m - r) * (Nat.choose (m + 1) (r + 1) : ℤ) * (2 * ((r + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r < m := Finset.mem_range.mp hr
      have hsign : (-1 : ℤ) ^ (m - r) = -((-1 : ℤ) ^ (m - (r + 1))) := by
        have : m - r = (m - (r + 1)) + 1 := by omega
        rw [this, pow_succ]; ring
      have hch : (Nat.choose (m + 1) (r + 1) : ℤ) = (Nat.choose m r : ℤ) + (Nat.choose m (r + 1) : ℤ) := by
        exact_mod_cast Nat.choose_succ_succ m r
      rw [hch, hsign]; ring
    have hsign0 : (-1 : ℤ) ^ (m + 1) = -((-1 : ℤ) ^ m) := by rw [pow_succ]; ring
    have h1 : (2 * ((0 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n = (-(m + 1 : ℤ)) ^ n := by push_cast; ring
    linear_combination hmid + (2 * ((0 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) ^ n * hsign0

private lemma zmod_pow_add_pred {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (x : ZMod p) :
    x ^ (n + (p - 1)) = x ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · subst hx
    simp [zero_pow (by omega : n + (p - 1) ≠ 0), zero_pow (by omega : n ≠ 0)]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]



private lemma partOdd_one (k : ℕ) :
    OMA.S_oeis_a245322.partOdd k 1 = if k % 2 = 1 then 1 else 0 := by
  cases k with
  | zero => simp [partOdd_zero_succ]
  | succ k =>
    rw [partOdd_succ_succ]
    have h1 : ∑ j ∈ Finset.range (k / 2 + 1),
        Nat.choose k (2 * j) * OMA.S_oeis_a245322.partOdd (k - 2 * j) 0 =
        if k % 2 = 0 then 1 else 0 := by
      by_cases hk : k % 2 = 0
      · rw [if_pos hk, Finset.sum_range_succ]
        have hzero : ∑ j ∈ Finset.range (k / 2),
            Nat.choose k (2 * j) * OMA.S_oeis_a245322.partOdd (k - 2 * j) 0 = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjlt : j < k / 2 := Finset.mem_range.mp hj
          have : ∃ t, k - 2 * j = t + 1 := ⟨k - 2 * j - 1, by omega⟩
          rcases this with ⟨t, ht⟩
          rw [ht, partOdd_succ_zero, mul_zero]
        rw [hzero, zero_add, show 2 * (k / 2) = k by omega, Nat.choose_self, Nat.sub_self,
            partOdd_zero_zero, mul_one]
      · rw [if_neg hk]
        apply Finset.sum_eq_zero
        intro j hj
        have hjle : j ≤ k / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have : ∃ t, k - 2 * j = t + 1 := ⟨k - 2 * j - 1, by omega⟩
        rcases this with ⟨t, ht⟩
        rw [ht, partOdd_succ_zero, mul_zero]
    rw [h1]
    by_cases hk : k % 2 = 0
    · have : (k + 1) % 2 = 1 := by omega
      simp [hk, this]
    · have : ¬ (k + 1) % 2 = 1 := by omega
      simp [hk, this]

private lemma a_mod_two (k : ℕ) (hk : 1 ≤ k) :
    (OMA.S_oeis_a245322.a k : ZMod 2) = if k % 2 = 1 then 1 else 0 := by
  unfold OMA.S_oeis_a245322.a
  push_cast
  have hsplit : Finset.range (k + 1) = Finset.range 2 ∪ (Finset.range (k + 1) \ Finset.range 2) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
  rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
  have htail : ∑ m ∈ Finset.range (k + 1) \ Finset.range 2,
      ((-1 : ZMod 2) ^ ((k - m) / 2) *
        ((m : ZMod 2) ^ k * (m.factorial : ZMod 2) * (OMA.S_oeis_a245322.partOdd k m : ZMod 2))) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_sdiff, Finset.mem_range] at hm
    have h0 : (m.factorial : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ 2).mpr (Nat.dvd_factorial (by decide) (by omega))
    rw [h0, mul_zero, zero_mul, mul_zero]
  rw [htail, add_zero, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.cast_zero, zero_pow (by omega : k ≠ 0), zero_mul, mul_zero, zero_add,
             Nat.cast_one, one_pow, Nat.factorial_one, one_mul, partOdd_one]
  have hneg1 : (-1 : ZMod 2) = 1 := by decide
  rw [hneg1, one_pow, one_mul]
  split_ifs <;> simp

private lemma periodic_step {p n t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (ht_dvd : (p - 1) ∣ t) (ht4 : 4 ∣ t) :
    OMA.S_oeis_a245322.a (n + t) ≡ OMA.S_oeis_a245322.a n [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  have htrunc : ∀ k : ℕ, 1 ≤ k →
      (OMA.S_oeis_a245322.a k : ZMod p) =
      ∑ m ∈ Finset.range p,
        ((-1 : ZMod p) ^ ((k - m) / 2) * ((m : ZMod p) ^ k * (sOdd k m : ZMod p))) := by
    intro k hk
    unfold OMA.S_oeis_a245322.a
    push_cast
    by_cases hkp : k + 1 ≤ p
    · have hsplit : Finset.range p = Finset.range (k + 1) ∪ (Finset.range p \ Finset.range (k + 1)) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have htail : ∑ m ∈ Finset.range p \ Finset.range (k + 1),
          ((-1 : ZMod p) ^ ((k - m) / 2) * ((m : ZMod p) ^ k * (sOdd k m : ZMod p))) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        simp only [Finset.mem_sdiff, Finset.mem_range] at hm
        rw [sOdd_eq_fact_mul_partOdd, partOdd_eq_zero_of_lt k m (by omega),
            mul_zero, Nat.cast_zero, mul_zero, mul_zero]
      rw [htail, add_zero]
      apply Finset.sum_congr rfl
      intro m _
      rw [sOdd_eq_fact_mul_partOdd, Nat.cast_mul, mul_assoc]
    · have hsplit : Finset.range (k + 1) = Finset.range p ∪ (Finset.range (k + 1) \ Finset.range p) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have htail : ∑ m ∈ Finset.range (k + 1) \ Finset.range p,
          ((-1 : ZMod p) ^ ((k - m) / 2) *
            ((m : ZMod p) ^ k * (m.factorial : ZMod p) * (OMA.S_oeis_a245322.partOdd k m : ZMod p))) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        simp only [Finset.mem_sdiff, Finset.mem_range] at hm
        have h0 : (m.factorial : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ p).mpr (Nat.dvd_factorial hp.pos (by omega))
        rw [h0, mul_zero, zero_mul, mul_zero]
      rw [htail, add_zero]
      apply Finset.sum_congr rfl
      intro m _
      rw [sOdd_eq_fact_mul_partOdd, Nat.cast_mul, mul_assoc]
  have hpow_t : ∀ x : ZMod p, x ^ (n + t) = x ^ n := by
    intro x
    clear ht4
    rcases ht_dvd with ⟨c, rfl⟩
    induction c with
    | zero => simp
    | succ c ihc =>
      rw [show n + (p - 1) * (c + 1) = (n + (p - 1) * c) + (p - 1) by ring]
      rw [zmod_pow_add_pred hp (by omega), ihc]
  rw [htrunc (n + t) (by omega), htrunc n hn]
  apply Finset.sum_congr rfl
  intro m _
  have hm_pow : (m : ZMod p) ^ (n + t) = (m : ZMod p) ^ n := hpow_t (m : ZMod p)
  have h2_ne : (2 : ZMod p) ^ m ≠ 0 := by
    apply pow_ne_zero
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  have hsOdd_eq : (sOdd (n + t) m : ZMod p) = (sOdd n m : ZMod p) := by
    apply mul_left_cancel₀ h2_ne
    have h1 := congrArg (Int.cast (R := ZMod p)) (two_pow_mul_sOdd m (n + t))
    have h2 := congrArg (Int.cast (R := ZMod p)) (two_pow_mul_sOdd m n)
    push_cast at h1 h2
    rw [h1, h2]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    exact hpow_t (2 * (r : ZMod p) - (m : ZMod p))
  by_cases hmn : m ≤ n
  · have hsign : (-1 : ZMod p) ^ ((n + t - m) / 2) = (-1 : ZMod p) ^ ((n - m) / 2) := by
      rcases ht4 with ⟨q, rfl⟩
      have hdiv : (n + 4 * q - m) / 2 = (n - m) / 2 + 2 * q := by omega
      rw [hdiv, pow_add, pow_mul]
      norm_num
    rw [hsign, hm_pow, hsOdd_eq]
  · have h0 : sOdd n m = 0 := by
      rw [sOdd_eq_fact_mul_partOdd, partOdd_eq_zero_of_lt n m (by omega), mul_zero]
    simp [hsOdd_eq, h0]

end OeisA245322Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a245322.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    constructor
    · have h := OeisA245322Proof.a_mod_two (2 * n) (by omega)
      have hmod : (2 * n) % 2 = 0 := by omega
      simp [hmod] at h
      have hdvd : (2 : ℤ) ∣ OMA.S_oeis_a245322.a (2 * n) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h
      rcases hdvd with ⟨q, hq⟩
      exact ⟨q, by linarith⟩
    · have h := OeisA245322Proof.a_mod_two (2 * n - 1) (by omega)
      have hmod : (2 * n - 1) % 2 = 1 := by omega
      simp only [hmod, ↓reduceIte] at h
      have hsub : ((OMA.S_oeis_a245322.a (2 * n - 1) - 1 : ℤ) : ZMod 2) = 0 := by
        rw [Int.cast_sub, Int.cast_one, h, sub_self]
      have hdvd : (2 : ℤ) ∣ (OMA.S_oeis_a245322.a (2 * n - 1) - 1) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hsub
      rcases hdvd with ⟨q, hq⟩
      exact ⟨q, by linarith⟩
  · intro p n hp hmod hn
    exact OeisA245322Proof.periodic_step hp (by omega) hn (dvd_refl _) ⟨(p - 1) / 4, by omega⟩
  · intro p n hp hmod hn
    exact OeisA245322Proof.periodic_step hp (by omega) hn (dvd_mul_left _ 2) ⟨(p - 1) / 2, by omega⟩
