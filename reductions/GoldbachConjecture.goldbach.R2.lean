import FormalConjectures.Wikipedia.GoldbachConjecture
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log

-- Reduction GoldbachConjecture.goldbach.R2 of Goldbach's conjecture
-- Credit: @nisbenz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Goldbach's conjecture: exact integer Mobius-von Mangoldt divisor-cutoff reduction

For even `n > 50000`, set the Bombieri-Vinogradov-scale cutoff
`D = Nat.sqrt (n / Nat.sqrt (Nat.sqrt n))` (`~ n^(3/8)`).

* `H1`: every even `n` with `2 < n <= 50000` is a sum of two primes.
* `H2`: the short-divisor sum `S_D(n)` exceeds `(4 / 5) * n` for every even `n > 50000`
  (asymptotically `n * S(n) >= 1.32 * n` unconditionally by Bombieri-Vinogradov).
* `H3`: the long-divisor Mobius tail `T_D(n)` is at most `(1 / 2) * n` for every even `n > 50000`
  (the integer analogue of the function-field long-divisor tail in Gou-Wang-Xu).

`main` proves inside Lean both the exact divisor-cutoff identity
`R_prime(n) + P_pp(n) = S_D(n) - T_D(n)` and the explicit prime-power bound
`P_pp(n) <= (Nat.sqrt n / 2 + 1) * (Real.log n)^2 <= (3 / 10) * n` for all `n > 50000`.
-/

namespace OMA.R_GoldbachConjecture_goldbach_R2

open Finset ArithmeticFunction

/-- Finite verification up to 50000. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → Even n → n ≤ 50000 → ∃ p q, Prime p ∧ Prime q ∧ n = p + q

/-- Unconditional Bombieri-Vinogradov-scale short-divisor lower bound. -/
def H2 : Prop :=
  ∀ n : ℕ, 50000 < n → Even n →
    (4 : ℝ) / 5 * n <
      -(∑ d ∈ (Finset.Icc 1 (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)))).filter (fun d => Nat.Coprime d n),
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ d ∣ (n - x)),
            Real.log (x : ℝ))

/-- One-sided aggregate bound on the long-divisor Mobius tail. -/
def H3 : Prop :=
  ∀ n : ℕ, 50000 < n → Even n →
    ∑ k ∈ (Finset.Icc 1 ((n - 1) / (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)) + 1))).filter
        (fun k => Nat.Coprime k n),
      ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
          (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ k ∣ (n - x) ∧
            x + k * Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)) < n),
        Real.log (x : ℝ) * (ArithmeticFunction.moebius ((n - x) / k) : ℝ) *
          Real.log (((n - x) / k : ℕ) : ℝ) ≤
      (1 : ℝ) / 2 * n

lemma coprime_sub_of_coprime {x n : ℕ} (hx : x ≤ n) (hcop : Nat.Coprime x n) :
    Nat.Coprime (n - x) n := by
  rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
  have h1 : Nat.gcd (n - x) n ∣ x := by
    have hd1 : Nat.gcd (n - x) n ∣ n - x := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (n - x) n ∣ n := Nat.gcd_dvd_right _ _
    have hd3 : Nat.gcd (n - x) n ∣ n - (n - x) := Nat.dvd_sub hd2 hd1
    rwa [Nat.sub_sub_self hx] at hd3
  have h2 : Nat.gcd (n - x) n ∣ Nat.gcd x n := Nat.dvd_gcd h1 (Nat.gcd_dvd_right _ _)
  rw [hcop] at h2
  exact Nat.dvd_one.mp h2

lemma vonMangoldt_divisor_split {m D : ℕ} :
    ArithmeticFunction.vonMangoldt m =
      -(∑ d ∈ m.divisors.filter (fun d => d ≤ D), (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) -
      (∑ d ∈ m.divisors.filter (fun d => D < d), (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) := by
  have h := @ArithmeticFunction.sum_moebius_mul_log_eq m
  have hsplit : ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) =
      (∑ d ∈ m.divisors.filter (fun d => d ≤ D), (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) +
      (∑ d ∈ m.divisors.filter (fun d => D < d), (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) := by
    have hs := Finset.sum_filter_add_sum_filter_not m.divisors (fun d => d ≤ D)
      (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ))
    have hnot : m.divisors.filter (fun d => ¬d ≤ D) = m.divisors.filter (fun d => D < d) := by
      ext d; simp [not_le]
    rw [hnot] at hs
    exact hs.symm
  have h' : (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
      -ArithmeticFunction.vonMangoldt m := by
    simpa [ArithmeticFunction.log_apply] using h
  linarith

lemma divisor_cutoff_identity (n D : ℕ) (hn : 4 ≤ n) :
    ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
        Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) =
      -(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ d ∣ (n - x)),
            Real.log (x : ℝ)) -
      ∑ k ∈ (Finset.Icc 1 ((n - 1) / (D + 1))).filter (fun k => Nat.Coprime k n),
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ k ∣ (n - x) ∧ x + k * D < n),
          Real.log (x : ℝ) * (ArithmeticFunction.moebius ((n - x) / k) : ℝ) *
            Real.log (((n - x) / k : ℕ) : ℝ) := by
  have hpt :
      ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
        Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) =
      -(∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
        ∑ d ∈ (n - x).divisors.filter (fun d => d ≤ D),
          Real.log (x : ℝ) * ((ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ))) -
      (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
        ∑ d ∈ (n - x).divisors.filter (fun d => D < d),
          Real.log (x : ℝ) * ((ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ))) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    rw [vonMangoldt_divisor_split (D := D), mul_sub, mul_neg, Finset.mul_sum, Finset.mul_sum]
  rw [hpt]
  congr 1
  · congr 1
    have hshort :
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
          ∑ d ∈ (n - x).divisors.filter (fun d => d ≤ D),
            Real.log (x : ℝ) * ((ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
            if d ∣ (n - x) then
              (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) * Real.log (x : ℝ)
            else 0 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      have hpos : 0 < n - x := by omega
      have hcop : Nat.Coprime (n - x) n := coprime_sub_of_coprime (by omega) hx.2.2
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun d _ => by ring
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hdle⟩
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hpos
        exact ⟨⟨⟨hdpos, hdle⟩, hcop.coprime_dvd_left hdvd⟩, hdvd⟩
      · rintro ⟨⟨⟨_, hdle⟩, _⟩, hdvd⟩
        exact ⟨⟨hdvd, Nat.ne_of_gt hpos⟩, hdle⟩
    rw [hshort, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun x _ => rfl
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto
  · have hlong :
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
          ∑ d ∈ (n - x).divisors.filter (fun d => D < d),
            Real.log (x : ℝ) * ((ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
          ∑ k ∈ (Finset.Icc 1 ((n - 1) / (D + 1))).filter (fun k => Nat.Coprime k n),
            if k ∣ (n - x) ∧ x + k * D < n then
              Real.log (x : ℝ) * (ArithmeticFunction.moebius ((n - x) / k) : ℝ) *
                Real.log (((n - x) / k : ℕ) : ℝ)
            else 0 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      have hpos : 0 < n - x := by omega
      have hcop : Nat.Coprime (n - x) n := coprime_sub_of_coprime (by omega) hx.2.2
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun d _ => (n - x) / d) ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
        obtain ⟨⟨hdvd, _⟩, hdgt⟩ := hd
        have hdpos : 0 < d := by omega
        have hk_mul : (n - x) / d * d = n - x := Nat.div_mul_cancel hdvd
        have hk_dvd : (n - x) / d ∣ n - x := ⟨d, hk_mul.symm⟩
        have hk_pos : 1 ≤ (n - x) / d := Nat.div_pos (Nat.le_of_dvd hpos hdvd) hdpos
        have hk_le : (n - x) / d ≤ (n - 1) / (D + 1) := by
          rw [Nat.le_div_iff_mul_le (by omega : 0 < D + 1)]
          have h1 : (n - x) / d * (D + 1) ≤ (n - x) / d * d :=
            Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdgt)
          omega
        have hk_lt : x + (n - x) / d * D < n := by
          have h1 : (n - x) / d * D < (n - x) / d * d :=
            Nat.mul_lt_mul_of_pos_left hdgt (by omega)
          omega
        exact ⟨⟨⟨hk_pos, hk_le⟩, hcop.coprime_dvd_left hk_dvd⟩, hk_dvd, hk_lt⟩
      · intro d1 hd1 d2 hd2 heq
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd1 hd2
        have h1 : (n - x) / d1 * d1 = n - x := Nat.div_mul_cancel hd1.1.1
        have h2 : (n - x) / d2 * d2 = n - x := Nat.div_mul_cancel hd2.1.1
        rw [heq] at h1
        have hkpos : 0 < (n - x) / d2 :=
          Nat.div_pos (Nat.le_of_dvd hpos hd2.1.1) (Nat.pos_of_dvd_of_pos hd2.1.1 hpos)
        exact Nat.eq_of_mul_eq_mul_left hkpos (h1.trans h2.symm)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors] at hk ⊢
        obtain ⟨⟨⟨hkpos, _⟩, _⟩, hkdvd, hklt⟩ := hk
        refine ⟨(n - x) / k, ?_, ?_⟩
        · have hd_mul : k * ((n - x) / k) = n - x := Nat.mul_div_cancel' hkdvd
          have hd_dvd : (n - x) / k ∣ n - x := ⟨k, by rw [mul_comm, hd_mul]⟩
          have hd_gt : D < (n - x) / k := by
            by_contra hle
            push Not at hle
            have h1 : k * ((n - x) / k) ≤ k * D := Nat.mul_le_mul_left k hle
            omega
          exact ⟨⟨hd_dvd, Nat.ne_of_gt hpos⟩, hd_gt⟩
        · exact Nat.div_div_self hkdvd (Nat.ne_of_gt hpos)
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        have hdd : (n - x) / ((n - x) / d) = d := Nat.div_div_self hd.1.1 (Nat.ne_of_gt hpos)
        rw [hdd]
        ring
    rw [hlong, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun x _ => rfl
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto

lemma card_base_set_le (n : ℕ) :
    ((Finset.Icc 2 (Nat.sqrt n)).filter (fun p => p = 2 ∨ p % 2 = 1)).card ≤
      Nat.sqrt n / 2 + 1 := by
  have hsub : (Finset.Icc 2 (Nat.sqrt n)).filter (fun p => p = 2 ∨ p % 2 = 1) ⊆
      insert 2 ((Finset.Icc 1 (Nat.sqrt n / 2)).image (fun j => 2 * j + 1)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_image] at hp ⊢
    rcases hp.2 with rfl | hodd
    · exact Or.inl rfl
    · right
      refine ⟨p / 2, ⟨by omega, by omega⟩, by omega⟩
  calc ((Finset.Icc 2 (Nat.sqrt n)).filter (fun p => p = 2 ∨ p % 2 = 1)).card
      ≤ (insert 2 ((Finset.Icc 1 (Nat.sqrt n / 2)).image (fun j => 2 * j + 1))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 (Nat.sqrt n / 2)).image (fun j => 2 * j + 1)).card + 1 :=
        Finset.card_insert_le (2 : ℕ) ((Finset.Icc 1 (Nat.sqrt n / 2)).image (fun j => 2 * j + 1))
    _ ≤ (Finset.Icc 1 (Nat.sqrt n / 2)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
    _ = Nat.sqrt n / 2 + 1 := by simp

lemma prime_pow_sum_le (n : ℕ) (hn : 4 ≤ n) :
    ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
        (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
        Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) ≤
      ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hstep1' :
      ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
          (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
        Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) ≤
      Real.log (n : ℝ) *
        ∑ m ∈ (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m),
          ArithmeticFunction.vonMangoldt m := by
    have hle1 :
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) ≤
        Real.log (n : ℝ) *
          ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
              (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x) ∧ IsPrimePow (n - x)),
            ArithmeticFunction.vonMangoldt (n - x) := by
      rw [Finset.mul_sum]
      have hzero :
          ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
              (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
            Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) =
          ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
              (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x) ∧ IsPrimePow (n - x)),
            Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) := by
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h1 : Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)
        · by_cases h2 : IsPrimePow (n - x)
          · simp [h1, h2]
          · simp [h1, h2, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h2]
        · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, h.2.1, h.2.2.1⟩)]
      rw [hzero]
      refine Finset.sum_le_sum fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      refine mul_le_mul_of_nonneg_right ?_ ArithmeticFunction.vonMangoldt_nonneg
      exact Real.log_le_log (by exact_mod_cast hx.1.1) (by exact_mod_cast (by omega : x ≤ n))
    refine hle1.trans (mul_le_mul_of_nonneg_left ?_ hlogn_nn)
    let S := (Finset.Icc 1 (n - 2)).filter
      (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x) ∧ IsPrimePow (n - x))
    have hinj : Set.InjOn (fun x => n - x) (S : Set ℕ) := by
      intro a ha b hb hab
      dsimp only at hab
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
      omega
    have himg : S.image (fun x => n - x) ⊆
        (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m) := by
      intro m hm
      simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      obtain ⟨x, ⟨⟨_, _⟩, _, _, hnp, hpp⟩, rfl⟩ := hm
      exact ⟨⟨by omega, by omega⟩, hpp, hnp⟩
    calc ∑ x ∈ S, ArithmeticFunction.vonMangoldt (n - x)
        = ∑ m ∈ S.image (fun x => n - x), ArithmeticFunction.vonMangoldt m :=
          (Finset.sum_image (fun a ha b hb h => hinj ha hb h)).symm
      _ ≤ ∑ m ∈ (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m),
            ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hstep2 :
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m),
        ArithmeticFunction.vonMangoldt m ≤
      ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * Real.log (n : ℝ) := by
    let M := (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m)
    let B := (Finset.Icc 2 (Nat.sqrt n)).filter (fun p => p = 2 ∨ p % 2 = 1)
    have hmaps : ∀ m ∈ M, Nat.minFac m ∈ B := by
      intro m hm
      simp only [M, B, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      obtain ⟨⟨hm1, hmn⟩, hpp, hnp⟩ := hm
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1
        simp only [pow_one] at hnp
        exact hnp hp
      have hmf : Nat.minFac (p ^ k) = p := by
        rw [Nat.pow_minFac (by omega), hp.minFac_eq]
      rw [hmf]
      have hpsq : p * p ≤ n := by
        calc p * p = p ^ 2 := (sq p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
          _ ≤ n := hmn
      have hple : p ≤ Nat.sqrt n := Nat.le_sqrt.mpr hpsq
      have hpar : p = 2 ∨ p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h2 | hodd
        · exact Or.inl h2
        · exact Or.inr hodd
      exact ⟨⟨hp.two_le, hple⟩, hpar⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ p ∈ B, ∑ m ∈ M.filter (fun m => Nat.minFac m = p), ArithmeticFunction.vonMangoldt m
        ≤ ∑ _p ∈ B, Real.log (n : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [B, Finset.mem_filter, Finset.mem_Icc] at hp
          by_cases hprime : Nat.Prime p
          · have hfib_sub : M.filter (fun m => Nat.minFac m = p) ⊆
                (Finset.Icc 2 (Nat.log p n)).image (fun k => p ^ k) := by
              intro m hm
              simp only [M, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hm ⊢
              obtain ⟨⟨⟨_, hmn⟩, hpp, hnp⟩, hmf⟩ := hm
              obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
              have hqmf : Nat.minFac (q ^ k) = q := by
                rw [Nat.pow_minFac (by omega), hq.minFac_eq]
              rw [hqmf] at hmf
              subst hmf
              have hk2 : 2 ≤ k := by
                by_contra hlt
                have hk1 : k = 1 := by omega
                subst hk1
                simp only [pow_one] at hnp
                exact hnp hq
              have hkle : k ≤ Nat.log q n := Nat.le_log_of_pow_le hq.one_lt hmn
              exact ⟨k, ⟨hk2, hkle⟩, rfl⟩
            calc ∑ m ∈ M.filter (fun m => Nat.minFac m = p), ArithmeticFunction.vonMangoldt m
                ≤ ∑ m ∈ (Finset.Icc 2 (Nat.log p n)).image (fun k => p ^ k),
                    ArithmeticFunction.vonMangoldt m :=
                  Finset.sum_le_sum_of_subset_of_nonneg hfib_sub
                    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
              _ ≤ ∑ k ∈ Finset.Icc 2 (Nat.log p n), ArithmeticFunction.vonMangoldt (p ^ k) :=
                  Finset.sum_image_le_of_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
              _ = ∑ _k ∈ Finset.Icc 2 (Nat.log p n), Real.log (p : ℝ) := by
                  refine Finset.sum_congr rfl fun k hk => ?_
                  simp only [Finset.mem_Icc] at hk
                  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
                    ArithmeticFunction.vonMangoldt_apply_prime hprime]
              _ = ((Finset.Icc 2 (Nat.log p n)).card : ℝ) * Real.log (p : ℝ) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (Nat.log p n : ℝ) * Real.log (p : ℝ) := by
                  have hcard : (Finset.Icc 2 (Nat.log p n)).card ≤ Nat.log p n := by
                    simp
                  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
                    (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))
              _ = Real.log (((p ^ Nat.log p n : ℕ) : ℝ)) := by
                  rw [Nat.cast_pow, Real.log_pow]
              _ ≤ Real.log (n : ℝ) := by
                  refine Real.log_le_log ?_ ?_
                  · exact_mod_cast Nat.pow_pos hprime.pos
                  · exact_mod_cast Nat.pow_log_le_self p (by omega)
          · have hempty : M.filter (fun m => Nat.minFac m = p) = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro m hm
              simp only [M, Finset.mem_filter, Finset.mem_Icc] at hm
              obtain ⟨⟨_, hpp, _⟩, hmf⟩ := hm
              have hmne1 : m ≠ 1 := hpp.ne_one
              exact hprime (hmf ▸ Nat.minFac_prime hmne1)
            rw [hempty, Finset.sum_empty]
            exact hlogn_nn
      _ = (B.card : ℝ) * Real.log (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * Real.log (n : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogn_nn
          exact_mod_cast card_base_set_le n
  calc ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
          (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
        Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x)
      ≤ Real.log (n : ℝ) *
          ∑ m ∈ (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m),
            ArithmeticFunction.vonMangoldt m := hstep1'
    _ ≤ Real.log (n : ℝ) * (((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 hlogn_nn
    _ = ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by ring

lemma log_sq_prime_pow_bound (n : ℕ) (hn : 50000 < n) :
    ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (3 : ℝ) / 10 * n := by
  have hnR : (50000 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  set u : ℝ := (n : ℝ) ^ ((1 : ℝ) / 10)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hn_pos _
  have hu10 : u ^ 10 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hu_ge : (295 : ℝ) / 100 ≤ u := by
    by_contra hlt
    push Not at hlt
    have h10 : u ^ 10 < ((295 : ℝ) / 100) ^ 10 :=
      pow_lt_pow_left₀ hlt hu_pos.le (by norm_num)
    rw [hu10] at h10
    norm_num at h10
    linarith
  have he : (2718 : ℝ) / 1000 < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have hlog : Real.log (n : ℝ) ≤ (368 : ℝ) / 100 * u := by
    have h1 : Real.log (n : ℝ) = 10 * Real.log u := by
      rw [← hu10, Real.log_pow]
      norm_num
    have h2 : Real.log u = 1 + Real.log (u / Real.exp 1) := by
      rw [Real.log_div hu_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
      ring
    have h3 : Real.log (u / Real.exp 1) ≤ u / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hu_pos (Real.exp_pos 1))
    have h4 : u / Real.exp 1 ≤ u / ((2718 : ℝ) / 1000) :=
      div_le_div_of_nonneg_left hu_pos.le (by norm_num) he.le
    rw [h1, h2]
    linarith
  have hsqrt_le : (Nat.sqrt n : ℝ) ≤ u ^ 5 := by
    have hsq : ((Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) := by
      have hnat : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
      have hcast : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
      nlinarith
    have hu5_sq : (u ^ 5) ^ 2 = (n : ℝ) := by
      rw [← pow_mul]; norm_num; exact hu10
    nlinarith [pow_nonneg hu_pos.le 5, Nat.cast_nonneg (α := ℝ) (Nat.sqrt n)]
  have hhalf : ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) ≤ u ^ 5 / 2 + 1 := by
    have hnat : 2 * (Nat.sqrt n / 2) ≤ Nat.sqrt n := Nat.mul_div_le (Nat.sqrt n) 2
    have hcast : (2 : ℝ) * ((Nat.sqrt n / 2 : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hnat
    push_cast
    linarith
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog_sq : (Real.log (n : ℝ)) ^ 2 ≤ ((368 : ℝ) / 100 * u) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog 2
  have hbase_nn : 0 ≤ ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) := by positivity
  have hprod : ((Nat.sqrt n / 2 + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
      (u ^ 5 / 2 + 1) * ((368 : ℝ) / 100 * u) ^ 2 :=
    mul_le_mul hhalf hlog_sq (sq_nonneg _) (by positivity)
  refine hprod.trans ?_
  rw [← hu10]
  have hu2 : (295 : ℝ) / 100 ≤ u := hu_ge
  have hu3 : ((295 : ℝ) / 100) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu2 3
  have hu5 : ((295 : ℝ) / 100) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu2 5
  have hpoly : (u ^ 5 / 2 + 1) * ((368 : ℝ) / 100 * u) ^ 2 ≤ (3 : ℝ) / 10 * u ^ 10 := by
    have hcoef1 : (1 / 2 : ℝ) * ((368 : ℝ) / 100) ^ 2 * u ^ 7 ≤ (28 : ℝ) / 100 * u ^ 10 := by
      have hc : (1 / 2 : ℝ) * ((368 : ℝ) / 100) ^ 2 ≤ (28 : ℝ) / 100 * u ^ 3 := by
        norm_num at hu3 ⊢; linarith
      have := mul_le_mul_of_nonneg_right hc (pow_nonneg hu_pos.le 7)
      linarith [show u ^ 3 * u ^ 7 = u ^ 10 by ring]
    have hcoef2 : ((368 : ℝ) / 100) ^ 2 * u ^ 2 ≤ (2 : ℝ) / 100 * u ^ 10 := by
      have hu8 : ((295 : ℝ) / 100) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu2 8
      have hc : ((368 : ℝ) / 100) ^ 2 ≤ (2 : ℝ) / 100 * u ^ 8 := by
        norm_num at hu8 ⊢; linarith
      have := mul_le_mul_of_nonneg_right hc (pow_nonneg hu_pos.le 2)
      linarith [show u ^ 8 * u ^ 2 = u ^ 10 by ring]
    nlinarith
  exact hpoly

theorem main : H1 → H2 → H3 → type_of% @GoldbachConjecture.goldbach := by
  intro h1 h2 h3 n hn he
  by_cases hle : n ≤ 50000
  · exact h1 n hn he hle
  · push Not at hle
    have h4 : 4 ≤ n := by omega
    set D := Nat.sqrt (n / Nat.sqrt (Nat.sqrt n))
    have hshort := h2 n hle he
    have hlong := h3 n hle he
    have hid := divisor_cutoff_identity n D h4
    have hpp := (prime_pow_sum_le n h4).trans (log_sq_prime_pow_bound n hle)
    have hfull_pos :
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) <
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) := by
      linarith
    have hsplit :
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) =
        (∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ Nat.Prime (n - x)),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x)) +
        (∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x)) := by
      have hs := Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n))
        (fun x => Nat.Prime (n - x))
        (fun x => Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x))
      have ha : ((Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n)).filter
          (fun x => Nat.Prime (n - x)) =
          (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ Nat.Prime (n - x)) := by
        ext x; simp only [Finset.mem_filter]; tauto
      have hb : ((Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n)).filter
          (fun x => ¬Nat.Prime (n - x)) =
          (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ ¬Nat.Prime (n - x)) := by
        ext x; simp only [Finset.mem_filter]; tauto
      rw [ha, hb] at hs
      exact hs.symm
    have hpr_pos :
        0 < ∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ Nat.Prime (n - x)),
          Real.log (x : ℝ) * ArithmeticFunction.vonMangoldt (n - x) := by
      linarith
    have hne : ((Finset.Icc 1 (n - 2)).filter
        (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ Nat.Prime (n - x))).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at hpr_pos
      exact lt_irrefl 0 hpr_pos
    obtain ⟨x, hx⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    exact ⟨x, n - x, Nat.prime_iff.mp hx.2.1, Nat.prime_iff.mp hx.2.2.2, by omega⟩

end OMA.R_GoldbachConjecture_goldbach_R2
