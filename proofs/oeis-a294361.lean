import OMAStatements.S_oeis_a294361
import Mathlib

/-!
# Proof of OEIS A294361 Conjectures

We prove the general periodicity theorem `a(n + k) ≡ a(n) [MOD k]` for any e.g.f.
`exp(x + G(x))` with `G(x) = Sum_{m >= 2} f(m) * x^m` via the binomial decomposition
`a(n) = Sum_{j=0..n} C(n, j) * b(j)` where `t ∣ b(j)` for all `1 <= t <= j`.
The mod 6 and mod 10 conjectures then follow from the base values `a(0)..a(5)`.
-/

namespace OeisA294361Proof

open Finset

private def gPow (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j => ∑ r ∈ Finset.Icc 2 j, f r * gPow f i (j - r)

private lemma gPow_eq_zero_of_lt (f : ℕ → ℕ) : ∀ i j : ℕ, j < 2 * i → gPow f i j = 0 := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj
    simp only [gPow]
    apply Finset.sum_eq_zero
    intro r hr
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrj : r ≤ j := (Finset.mem_Icc.mp hr).2
    rw [ih (j - r) (by omega), mul_zero]

private lemma mul_gPow_eq (f : ℕ → ℕ) :
    ∀ i j : ℕ, 1 ≤ i →
      j * gPow f i j = i * ∑ r ∈ Finset.Icc 2 j, r * f r * gPow f (i - 1) (j - r) := by
  intro i
  induction i with
  | zero => intro j h; omega
  | succ i ih =>
    intro j _
    cases i with
    | zero =>
      simp only [Nat.zero_add, Nat.sub_self, one_mul, gPow]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hrj : r ≤ j := (Finset.mem_Icc.mp hr).2
      by_cases h : j - r = 0
      · have hr_eq : r = j := by omega
        subst hr_eq; simp
      · simp [h]
    | succ i' =>
      set m := i' + 1
      have hm_pos : 1 ≤ m := by omega
      simp only [Nat.add_sub_cancel]
      have hsplit : j * gPow f (m + 1) j =
          (∑ r ∈ Finset.Icc 2 j, r * f r * gPow f m (j - r)) +
          (∑ r ∈ Finset.Icc 2 j, f r * ((j - r) * gPow f m (j - r))) := by
        simp only [gPow]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        have hrj : r ≤ j := (Finset.mem_Icc.mp hr).2
        have hjr : r + (j - r) = j := by omega
        calc j * (f r * gPow f m (j - r))
            = (r + (j - r)) * (f r * gPow f m (j - r)) := by rw [hjr]
          _ = r * f r * gPow f m (j - r) + f r * ((j - r) * gPow f m (j - r)) := by ring
      have hsecond :
          ∑ r ∈ Finset.Icc 2 j, f r * ((j - r) * gPow f m (j - r)) =
          m * ∑ s ∈ Finset.Icc 2 j, s * f s * gPow f m (j - s) := by
        have h1 : ∑ r ∈ Finset.Icc 2 j, f r * ((j - r) * gPow f m (j - r)) =
            m * ∑ r ∈ Finset.Icc 2 j, ∑ s ∈ Finset.Icc 2 (j - r),
              f r * (s * f s * gPow f (m - 1) (j - r - s)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [ih (j - r) hm_pos]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
        rw [h1]
        congr 1
        have hswap :
            ∑ r ∈ Finset.Icc 2 j, ∑ s ∈ Finset.Icc 2 (j - r),
              f r * (s * f s * gPow f (m - 1) (j - r - s)) =
            ∑ s ∈ Finset.Icc 2 j, ∑ r ∈ Finset.Icc 2 (j - s),
              s * f s * (f r * gPow f (m - 1) (j - s - r)) := by
          trans (∑ x ∈ (Finset.Icc 2 j).sigma (fun r => Finset.Icc 2 (j - r)),
              f x.1 * (x.2 * f x.2 * gPow f (m - 1) (j - x.1 - x.2)))
          · exact Finset.sum_sigma' (Finset.Icc 2 j) (fun r => Finset.Icc 2 (j - r))
              (fun r s => f r * (s * f s * gPow f (m - 1) (j - r - s)))
          · trans (∑ y ∈ (Finset.Icc 2 j).sigma (fun s => Finset.Icc 2 (j - s)),
                y.1 * f y.1 * (f y.2 * gPow f (m - 1) (j - y.1 - y.2)))
            · refine Finset.sum_bij (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
              · intro ⟨r, s⟩ hx
                simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
                omega
              · intro ⟨r1, s1⟩ _ ⟨r2, s2⟩ _ heq
                simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
                rcases heq with ⟨rfl, rfl⟩
                rfl
              · intro ⟨s, r⟩ hy
                refine ⟨⟨r, s⟩, ?_, rfl⟩
                simp only [Finset.mem_sigma, Finset.mem_Icc] at hy ⊢
                omega
              · intro ⟨r, s⟩ _
                have hsub : j - r - s = j - s - r := by omega
                rw [hsub]; ring
            · exact (Finset.sum_sigma' (Finset.Icc 2 j) (fun s => Finset.Icc 2 (j - s))
                (fun s r => s * f s * (f r * gPow f (m - 1) (j - s - r)))).symm
        rw [hswap]
        apply Finset.sum_congr rfl
        intro s _
        rw [← Finset.mul_sum]
        have hm_eq : m = (m - 1) + 1 := by omega
        have hg : gPow f m (j - s) = ∑ r ∈ Finset.Icc 2 (j - s), f r * gPow f (m - 1) (j - s - r) := by
          conv_lhs => rw [hm_eq]
          rfl
        rw [hg]
      rw [hsplit, hsecond]
      ring

private def bSeq (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (j + 1), (j.factorial / i.factorial) * gPow f i j

private lemma bSeq_zero (f : ℕ → ℕ) : bSeq f 0 = 1 := by
  simp [bSeq, gPow]

private lemma fact_div_succ_mul (j i : ℕ) (hi : i ≤ j) :
    ((j + 1).factorial / (i + 1).factorial) * (i + 1) = (j + 1) * (j.factorial / i.factorial) := by
  have hd1 : (i + 1).factorial ∣ (j + 1).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hd2 : i.factorial ∣ j.factorial := Nat.factorial_dvd_factorial hi
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos i)
  calc ((j + 1).factorial / (i + 1).factorial) * (i + 1) * i.factorial
      = ((j + 1).factorial / (i + 1).factorial) * (i + 1).factorial := by
          rw [Nat.factorial_succ i]; ring
    _ = (j + 1).factorial := Nat.div_mul_cancel hd1
    _ = (j + 1) * j.factorial := Nat.factorial_succ j
    _ = (j + 1) * (j.factorial / i.factorial * i.factorial) := by
          rw [Nat.div_mul_cancel hd2]
    _ = (j + 1) * (j.factorial / i.factorial) * i.factorial := by ring

private lemma fact_div_mul_r (j r i : ℕ) (hr2 : 2 ≤ r) (hrj : r ≤ j + 1) (hi : i ≤ j + 1 - r) :
    (j.factorial / i.factorial) * r =
      Nat.choose j (r - 1) * r.factorial * ((j + 1 - r).factorial / i.factorial) := by
  have h1 : i ≤ j := by omega
  have hd1 : i.factorial ∣ j.factorial := Nat.factorial_dvd_factorial h1
  have hd2 : i.factorial ∣ (j + 1 - r).factorial := Nat.factorial_dvd_factorial hi
  have hpos : 0 < (r - 1).factorial * (j + 1 - r).factorial * i.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hch : Nat.choose j (r - 1) * (r - 1).factorial * (j + 1 - r).factorial = j.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show r - 1 ≤ j by omega)
    rwa [show j - (r - 1) = j + 1 - r by omega] at this
  have hrf : r.factorial = r * (r - 1).factorial := by
    have hr_eq : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr_eq, Nat.factorial_succ]
    rw [← hr_eq]
  calc (j.factorial / i.factorial) * r * ((r - 1).factorial * (j + 1 - r).factorial * i.factorial)
      = (j.factorial / i.factorial * i.factorial) * r * (r - 1).factorial * (j + 1 - r).factorial := by ring
    _ = j.factorial * r * (r - 1).factorial * (j + 1 - r).factorial := by rw [Nat.div_mul_cancel hd1]
    _ = (Nat.choose j (r - 1) * (r - 1).factorial * (j + 1 - r).factorial) *
          r * (r - 1).factorial * (j + 1 - r).factorial := by rw [← hch]
    _ = Nat.choose j (r - 1) * (r * (r - 1).factorial) * (j + 1 - r).factorial *
          ((r - 1).factorial * (j + 1 - r).factorial) := by ring
    _ = Nat.choose j (r - 1) * r.factorial * ((j + 1 - r).factorial / i.factorial * i.factorial) *
          ((r - 1).factorial * (j + 1 - r).factorial) := by rw [← hrf, Nat.div_mul_cancel hd2]
    _ = Nat.choose j (r - 1) * r.factorial * ((j + 1 - r).factorial / i.factorial) *
          ((r - 1).factorial * (j + 1 - r).factorial * i.factorial) := by ring

private lemma bSeq_succ (f : ℕ → ℕ) (j : ℕ) :
    bSeq f (j + 1) =
      ∑ k ∈ Finset.Icc 1 j,
        Nat.choose j k * (k + 1).factorial * f (k + 1) * bSeq f (j - k) := by
  unfold bSeq
  rw [Finset.sum_range_succ']
  have h0 : gPow f 0 (j + 1) = 0 := by simp [gPow]
  rw [h0, mul_zero, add_zero]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      ((j + 1).factorial / (i + 1).factorial) * gPow f (i + 1) (j + 1) =
        ∑ r ∈ Finset.Icc 2 (j + 1),
          (j.factorial / i.factorial) * r * f r * gPow f i (j + 1 - r) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j)
    calc (j + 1) * (((j + 1).factorial / (i + 1).factorial) * gPow f (i + 1) (j + 1))
        = ((j + 1).factorial / (i + 1).factorial) * ((j + 1) * gPow f (i + 1) (j + 1)) := by ring
      _ = ((j + 1).factorial / (i + 1).factorial) *
            ((i + 1) * ∑ r ∈ Finset.Icc 2 (j + 1), r * f r * gPow f i (j + 1 - r)) := by
              rw [mul_gPow_eq f (i + 1) (j + 1) (by omega), Nat.add_sub_cancel]
      _ = (((j + 1).factorial / (i + 1).factorial) * (i + 1)) *
            ∑ r ∈ Finset.Icc 2 (j + 1), r * f r * gPow f i (j + 1 - r) := by ring
      _ = (j + 1) * (j.factorial / i.factorial) *
            ∑ r ∈ Finset.Icc 2 (j + 1), r * f r * gPow f i (j + 1 - r) := by
              rw [fact_div_succ_mul j i hij]
      _ = (j + 1) * ∑ r ∈ Finset.Icc 2 (j + 1),
            (j.factorial / i.factorial) * r * f r * gPow f i (j + 1 - r) := by
              rw [mul_assoc, Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro r _; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_bij (fun r _ => r - 1) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_Icc] at hr1 hr2
    omega
  · intro k hk
    refine ⟨k + 1, ?_, by omega⟩
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    have hr1 : r - 1 + 1 = r := by omega
    have hsub : j - (r - 1) = j + 1 - r := by omega
    rw [hr1, hsub, Finset.mul_sum]
    have hsplit : Finset.range (j + 1) =
        Finset.range (j + 1 - r + 1) ∪ (Finset.range (j + 1) \ Finset.range (j + 1 - r + 1)) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have hzero : ∑ i ∈ Finset.range (j + 1) \ Finset.range (j + 1 - r + 1),
        (j.factorial / i.factorial) * r * f r * gPow f i (j + 1 - r) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_range] at hi
      rw [gPow_eq_zero_of_lt f i (j + 1 - r) (by omega), mul_zero]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ j + 1 - r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [fact_div_mul_r j r i hr.1 hr.2 hi_le]
    ring

private lemma dvd_bSeq (f : ℕ → ℕ) (j t : ℕ) (ht1 : 1 ≤ t) (htj : t ≤ j) : t ∣ bSeq f j := by
  unfold bSeq
  apply Finset.dvd_sum
  intro i _
  by_cases h2i : j < 2 * i
  · rw [gPow_eq_zero_of_lt f i j h2i, mul_zero]; exact dvd_zero t
  · apply dvd_mul_of_dvd_left
    have hex : ∃ m : ℕ, i < m ∧ m ≤ j ∧ t ∣ m := by
      by_cases ht_half : 2 * t ≤ j
      · refine ⟨t * (j / t), ?_, Nat.mul_div_le j t, dvd_mul_right t (j / t)⟩
        have hmod : j % t < t := Nat.mod_lt j (by omega)
        have hdiv : t * (j / t) + j % t = j := Nat.div_add_mod j t
        omega
      · exact ⟨t, by omega, htj, dvd_refl t⟩
    rcases hex with ⟨m, him, hmj, htm⟩
    have hm1 : i ≤ m - 1 := by omega
    have hm_eq : m = (m - 1) + 1 := by omega
    have hd1 : i.factorial * m ∣ m.factorial := by
      conv_rhs => rw [hm_eq, Nat.factorial_succ]
      rw [← hm_eq, mul_comm m]
      exact mul_dvd_mul_right (Nat.factorial_dvd_factorial hm1) m
    have hd2 : i.factorial * m ∣ j.factorial :=
      dvd_trans hd1 (Nat.factorial_dvd_factorial hmj)
    have hmdvd : m ∣ j.factorial / i.factorial := by
      rcases hd2 with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have hi_pos : 0 < i.factorial := Nat.factorial_pos i
      apply Nat.eq_of_mul_eq_mul_left hi_pos
      rw [Nat.mul_div_cancel' (Nat.factorial_dvd_factorial (by omega : i ≤ j))]
      linarith
    exact dvd_trans htm hmdvd

private lemma a_eq_binom_bSeq (f : ℕ → ℕ) (hf1 : f 1 = 1) (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (hasucc : ∀ n : ℕ, a (n + 1) = ∑ j ∈ Finset.range (n + 1),
        Nat.choose n j * (j + 1).factorial * f (j + 1) * a (n - j)) :
    ∀ n : ℕ, a n = ∑ j ∈ Finset.range (n + 1), Nat.choose n j * bSeq f j := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [ha0, bSeq_zero]
    | succ n =>
      have hsplit : ∑ j ∈ Finset.range (n + 2), Nat.choose (n + 1) j * bSeq f j =
          (∑ j ∈ Finset.range (n + 1), Nat.choose n j * bSeq f j) +
          (∑ r ∈ Finset.range (n + 1), Nat.choose n r * bSeq f (r + 1)) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, one_mul]
        have h1 : ∑ j ∈ Finset.range (n + 1), Nat.choose (n + 1) (j + 1) * bSeq f (j + 1) =
            (∑ j ∈ Finset.range (n + 1), Nat.choose n (j + 1) * bSeq f (j + 1)) +
            (∑ j ∈ Finset.range (n + 1), Nat.choose n j * bSeq f (j + 1)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [Nat.choose_succ_succ, add_mul, add_comm]
        rw [h1]
        have h2 : ∑ j ∈ Finset.range (n + 1), Nat.choose n j * bSeq f j =
            bSeq f 0 + ∑ j ∈ Finset.range (n + 1), Nat.choose n (j + 1) * bSeq f (j + 1) := by
          conv_rhs =>
            rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), zero_mul, add_zero]
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, one_mul, add_comm]
        omega
      have hterm0 : ∑ j ∈ Finset.range (n + 1), Nat.choose n j * bSeq f j = a n :=
        (ih n (Nat.lt_succ_self n)).symm
      have hterm1 : ∑ r ∈ Finset.range (n + 1), Nat.choose n r * bSeq f (r + 1) =
          ∑ k ∈ Finset.Icc 1 n,
            Nat.choose n k * (k + 1).factorial * f (k + 1) * a (n - k) := by
        have hstep1 : ∑ r ∈ Finset.range (n + 1), Nat.choose n r * bSeq f (r + 1) =
            ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 r,
              Nat.choose n r * (Nat.choose r k * (k + 1).factorial * f (k + 1) * bSeq f (r - k)) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [bSeq_succ, Finset.mul_sum]
        rw [hstep1]
        have hswap :
            ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 r,
              Nat.choose n r * (Nat.choose r k * (k + 1).factorial * f (k + 1) * bSeq f (r - k)) =
            ∑ k ∈ Finset.Icc 1 n, ∑ s ∈ Finset.range (n - k + 1),
              Nat.choose n k * (k + 1).factorial * f (k + 1) *
                (Nat.choose (n - k) s * bSeq f s) := by
          trans (∑ x ∈ (Finset.range (n + 1)).sigma (fun r => Finset.Icc 1 r),
              Nat.choose n x.1 * (Nat.choose x.1 x.2 * (x.2 + 1).factorial * f (x.2 + 1) * bSeq f (x.1 - x.2)))
          · exact Finset.sum_sigma' (Finset.range (n + 1)) (fun r => Finset.Icc 1 r)
              (fun r k => Nat.choose n r * (Nat.choose r k * (k + 1).factorial * f (k + 1) * bSeq f (r - k)))
          · trans (∑ y ∈ (Finset.Icc 1 n).sigma (fun k => Finset.range (n - k + 1)),
                Nat.choose n y.1 * (y.1 + 1).factorial * f (y.1 + 1) *
                  (Nat.choose (n - y.1) y.2 * bSeq f y.2))
            · refine Finset.sum_bij (fun x _ => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_
              · intro ⟨r, k⟩ hx
                simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hx ⊢
                omega
              · intro ⟨r1, k1⟩ hx1 ⟨r2, k2⟩ hx2 heq
                simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hx1 hx2
                simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
                rcases heq with ⟨rfl, hs⟩
                have : r1 = r2 := by omega
                subst this; rfl
              · intro ⟨k, s⟩ hy
                refine ⟨⟨k + s, k⟩, ?_, ?_⟩
                · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hy ⊢
                  omega
                · simp
              · intro ⟨r, k⟩ hx
                simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hx
                have hch : Nat.choose n r * Nat.choose r k = Nat.choose n k * Nat.choose (n - k) (r - k) :=
                  Nat.choose_mul (n := n) (k := r) (s := k) (by omega)
                calc Nat.choose n r * (Nat.choose r k * (k + 1).factorial * f (k + 1) * bSeq f (r - k))
                    = (Nat.choose n r * Nat.choose r k) * (k + 1).factorial * f (k + 1) * bSeq f (r - k) := by ring
                  _ = (Nat.choose n k * Nat.choose (n - k) (r - k)) * (k + 1).factorial * f (k + 1) * bSeq f (r - k) := by rw [hch]
                  _ = Nat.choose n k * (k + 1).factorial * f (k + 1) * (Nat.choose (n - k) (r - k) * bSeq f (r - k)) := by ring
            · exact (Finset.sum_sigma' (Finset.Icc 1 n) (fun k => Finset.range (n - k + 1))
                (fun k s => Nat.choose n k * (k + 1).factorial * f (k + 1) * (Nat.choose (n - k) s * bSeq f s))).symm
        rw [hswap]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [← Finset.mul_sum, ← ih (n - k) (by omega)]
      rw [hasucc n, hsplit, hterm0, hterm1]
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, zero_add, Nat.factorial_one, one_mul, hf1, Nat.sub_zero]
      rw [add_comm (a n)]
      congr 1
      refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
      · intro j1 _ j2 _ h; omega
      · intro k hk; refine ⟨k - 1, ?_, ?_⟩
        · simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
        · simp only [Finset.mem_Icc] at hk; omega
      · intro j _; rfl

private lemma a_add_modEq (f : ℕ → ℕ) (hf1 : f 1 = 1) (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (hasucc : ∀ n : ℕ, a (n + 1) = ∑ j ∈ Finset.range (n + 1),
        Nat.choose n j * (j + 1).factorial * f (j + 1) * a (n - j))
    (k n : ℕ) (hk : 1 ≤ k) : a (n + k) ≡ a n [MOD k] := by
  rw [a_eq_binom_bSeq f hf1 a ha0 hasucc (n + k), a_eq_binom_bSeq f hf1 a ha0 hasucc n]
  have hdiff : ∑ j ∈ Finset.range (n + k + 1), Nat.choose (n + k) j * bSeq f j =
      (∑ j ∈ Finset.range (n + 1), Nat.choose n j * bSeq f j) +
      ∑ j ∈ Finset.range (n + k + 1),
        (∑ t ∈ Finset.Icc 1 j, Nat.choose n (j - t) * Nat.choose k t) * bSeq f j := by
    have hvand : ∀ j : ℕ, Nat.choose (n + k) j =
        Nat.choose n j + ∑ t ∈ Finset.Icc 1 j, Nat.choose n (j - t) * Nat.choose k t := by
      intro j
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => Nat.choose n x * Nat.choose k y)]
      have hrev : ∑ t ∈ Finset.range (j + 1), Nat.choose n t * Nat.choose k (j - t) =
          ∑ t ∈ Finset.range (j + 1), Nat.choose n (j - t) * Nat.choose k t := by
        refine Finset.sum_bij (fun t _ => j - t) ?_ ?_ ?_ ?_
        · intro t ht; simp only [Finset.mem_range] at ht ⊢; omega
        · intro t1 ht1 t2 ht2 h; simp only [Finset.mem_range] at ht1 ht2; omega
        · intro t ht; refine ⟨j - t, ?_, ?_⟩
          · simp only [Finset.mem_range] at ht ⊢; omega
          · simp only [Finset.mem_range] at ht; omega
        · intro t ht; simp only [Finset.mem_range] at ht; rw [show j - (j - t) = t by omega]
      rw [hrev, Finset.sum_range_succ']
      simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one]
      rw [add_comm (Nat.choose n j)]
      congr 1
      refine Finset.sum_bij (fun t _ => t + 1) ?_ ?_ ?_ ?_
      · intro t ht; simp only [Finset.mem_range, Finset.mem_Icc] at ht ⊢; omega
      · intro t1 _ t2 _ h; omega
      · intro t ht; refine ⟨t - 1, ?_, ?_⟩
        · simp only [Finset.mem_Icc, Finset.mem_range] at ht ⊢; omega
        · simp only [Finset.mem_Icc] at ht; omega
      · intro t _; rfl
    have h1 : ∑ j ∈ Finset.range (n + k + 1), Nat.choose (n + k) j * bSeq f j =
        (∑ j ∈ Finset.range (n + k + 1), Nat.choose n j * bSeq f j) +
        ∑ j ∈ Finset.range (n + k + 1),
          (∑ t ∈ Finset.Icc 1 j, Nat.choose n (j - t) * Nat.choose k t) * bSeq f j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hvand j, add_mul]
    rw [h1]
    congr 1
    have hsplit : Finset.range (n + k + 1) =
        Finset.range (n + 1) ∪ (Finset.range (n + k + 1) \ Finset.range (n + 1)) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have hzero : ∑ j ∈ Finset.range (n + k + 1) \ Finset.range (n + 1),
        Nat.choose n j * bSeq f j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    rw [hzero, add_zero]
  rw [hdiff]
  have hdvd : k ∣ ∑ j ∈ Finset.range (n + k + 1),
      (∑ t ∈ Finset.Icc 1 j, Nat.choose n (j - t) * Nat.choose k t) * bSeq f j := by
    apply Finset.dvd_sum
    intro j _
    rw [Finset.sum_mul]
    apply Finset.dvd_sum
    intro t ht
    simp only [Finset.mem_Icc] at ht
    obtain ⟨q, hq⟩ := dvd_bSeq f j t ht.1 ht.2
    have hkt : Nat.choose k t * t = k * Nat.choose (k - 1) (t - 1) := by
      have hk1 : k = (k - 1) + 1 := by omega
      have ht1 : t = (t - 1) + 1 := by omega
      conv_lhs => rw [hk1, ht1]
      have := Nat.add_one_mul_choose_eq (k - 1) (t - 1)
      rw [← hk1, ← ht1] at this ⊢
      linarith
    rw [hq]
    refine ⟨Nat.choose n (j - t) * Nat.choose (k - 1) (t - 1) * q, ?_⟩
    calc Nat.choose n (j - t) * Nat.choose k t * (t * q)
        = Nat.choose n (j - t) * (Nat.choose k t * t) * q := by ring
      _ = Nat.choose n (j - t) * (k * Nat.choose (k - 1) (t - 1)) * q := by rw [hkt]
      _ = k * (Nat.choose n (j - t) * Nat.choose (k - 1) (t - 1) * q) := by ring
  rcases hdvd with ⟨m, hm⟩
  rw [hm, Nat.ModEq, Nat.add_mul_mod_self_left]


private lemma sigma1_one : OMA.S_oeis_a294361.sigma1 1 = 1 := by decide

private lemma a_zero : OMA.S_oeis_a294361.a 0 = 1 := by
  rw [OMA.S_oeis_a294361.a]

private lemma a_succ (n : ℕ) : OMA.S_oeis_a294361.a (n + 1) =
    ∑ j ∈ Finset.range (n + 1),
      Nat.choose n j * (j + 1).factorial * OMA.S_oeis_a294361.sigma1 (j + 1) *
        OMA.S_oeis_a294361.a (n - j) := by
  rw [OMA.S_oeis_a294361.a]

private lemma main_modEq (k n : ℕ) (hk : 1 ≤ k) :
    OMA.S_oeis_a294361.a (n + k) ≡ OMA.S_oeis_a294361.a n [MOD k] :=
  a_add_modEq OMA.S_oeis_a294361.sigma1 sigma1_one OMA.S_oeis_a294361.a a_zero a_succ k n hk

private lemma modEq_mod (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, OMA.S_oeis_a294361.a n % k = OMA.S_oeis_a294361.a (n % k) % k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < k
    · rw [Nat.mod_eq_of_lt hlt]
    · have hge : k ≤ n := by omega
      have h1 : OMA.S_oeis_a294361.a n % k = OMA.S_oeis_a294361.a (n - k) % k := by
        have := main_modEq k (n - k) hk
        rwa [Nat.sub_add_cancel hge] at this
      have h2 : (n - k) % k = n % k := by
        conv_rhs => rw [show n = (n - k) + k by omega]
        exact (Nat.add_mod_right (n - k) k).symm
      rw [h1, ih (n - k) (by omega), h2]

private lemma a_val0 : OMA.S_oeis_a294361.a 0 = 1 := a_zero
private lemma a_val1 : OMA.S_oeis_a294361.a 1 = 1 := by
  rw [a_succ]; simp [a_val0]; decide
private lemma a_val2 : OMA.S_oeis_a294361.a 2 = 7 := by
  rw [a_succ]; simp [Finset.sum_range_succ, a_val0, a_val1]; decide
private lemma a_val3 : OMA.S_oeis_a294361.a 3 = 43 := by
  rw [a_succ]; simp [Finset.sum_range_succ, a_val0, a_val1, a_val2]; decide
private lemma a_val4 : OMA.S_oeis_a294361.a 4 = 409 := by
  rw [a_succ]; simp [Finset.sum_range_succ, a_val0, a_val1, a_val2, a_val3]; decide
private lemma a_val5 : OMA.S_oeis_a294361.a 5 = 3841 := by
  rw [a_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             Nat.reduceSub, a_val0, a_val1, a_val2, a_val3, a_val4]
  decide

private lemma init_mod6 : ∀ r : Fin 6, OMA.S_oeis_a294361.a r.val % 6 = 1 := by
  intro ⟨r, hr⟩
  interval_cases r
  · rw [a_val0]
  · rw [a_val1]
  · rw [a_val2]
  · rw [a_val3]
  · rw [a_val4]
  · rw [a_val5]

end OeisA294361Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a294361.main := by
  have hmod6 : ∀ n : ℕ, OMA.S_oeis_a294361.a n % 6 = 1 := by
    intro n
    rw [OeisA294361Proof.modEq_mod 6 (by decide) n]
    exact OeisA294361Proof.init_mod6 ⟨n % 6, Nat.mod_lt n (by decide)⟩
  refine ⟨hmod6, ?_, fun k hk n => OeisA294361Proof.main_modEq k n (by omega)⟩
  intro n
  have h5 : OMA.S_oeis_a294361.a (n + 5) % 5 = OMA.S_oeis_a294361.a n % 5 :=
    OeisA294361Proof.main_modEq 5 n (by decide)
  have h2a : OMA.S_oeis_a294361.a (n + 5) % 2 = 1 := by have := hmod6 (n + 5); omega
  have h2b : OMA.S_oeis_a294361.a n % 2 = 1 := by have := hmod6 n; omega
  omega
