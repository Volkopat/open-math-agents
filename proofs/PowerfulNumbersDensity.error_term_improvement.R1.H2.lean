import OMAReductions.R_PowerfulNumbersDensity_error_term_improvement_R1
import Mathlib

/-! # Large divisors in the powerful-number convolution

The variable-cutoff transfer below is adapted from Sky (ChironTheCentaur),
rh-lab-powerful-numbers, LargeD and ErrorTerm, Apache-2.0. The combinatorial
identity uses the port by senamakel in the Bateman–Grosswald submission.
-/
/-
PowerfulNumbers (standalone package)
Copyright 2026 Sky (GitHub: ChironTheCentaur)

The original work in this package (PowerfulFC/, LeanClassics/, PowerfulNumbers.lean, check.py, AxiomAudit.lean,
PlantedSorry.lean, controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

The statements of `asymptotic_erdos_szekeres`, `asymptotic_bateman_grosswald` and the conclusion of
`error_term_improvement`, and the definitions `Q`, `A`, `B` and `Nat.Full` / `Nat.Powerful`
(PowerfulFC/Defs.lean, PowerfulFC/Main.lean, PowerfulFC/BatemanGrosswald.lean, PowerfulFC/ErrorTerm.lean) are copied verbatim from google-deepmind/formal-conjectures
(FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean and FormalConjecturesForMathlib/Data/Nat/Full.lean,
commit ea8e3e19), Copyright The Formal Conjectures Authors, licensed under the Apache License, Version 2.0.

Zeta23/ is a subset of zeta-23-lean, Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0
(LICENSE.zeta23, NOTICE.zeta23), as ported to Lean v4.35.0 / Mathlib 56a005855ea1. It is not relicensed.

Mathlib and the Lean toolchain packages are fetched at build time and are not included.
-/
-- ===== PowerfulFC.Decomp =====
section
/-
# Powerful numbers are exactly `a² b³` with `b` squarefree, uniquely
-/

namespace PowerfulFC

lemma powerful_sq_mul_cube (a b : ℕ) : (a ^ 2 * b ^ 3).Powerful := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ a ^ 2 * b ^ 3 := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
  · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 2) _
  · refine Dvd.dvd.mul_left ?_ _
    exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 3)

/-- The exponent of `p` in `m² s` with `s` squarefree has parity `s.factorization p`. -/
lemma factorization_sq_mul_sqfree {m s : ℕ} (hm : m ≠ 0) (hs : Squarefree s) (p : ℕ) :
    s.factorization p = (m ^ 2 * s).factorization p % 2 := by
  have hs0 : s ≠ 0 := hs.ne_zero
  rw [Nat.factorization_mul (pow_ne_zero 2 hm) hs0, Nat.factorization_pow]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : s.factorization p ≤ 1 := hs.natFactorization_le_one p
  omega

lemma sqfree_unique {m s m' s' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0) (hs : Squarefree s)
    (hs' : Squarefree s') (h : m ^ 2 * s = m' ^ 2 * s') : s = s' := by
  apply Nat.eq_of_factorization_eq hs.ne_zero hs'.ne_zero
  intro p
  rw [factorization_sq_mul_sqfree hm hs, factorization_sq_mul_sqfree hm' hs', h]

lemma decomp_unique {a b c d : ℕ} (ha : a ≠ 0) (hc : c ≠ 0) (hb : Squarefree b) (hd : Squarefree d)
    (h : a ^ 2 * b ^ 3 = c ^ 2 * d ^ 3) : a = c ∧ b = d := by
  have hb0 : b ≠ 0 := hb.ne_zero
  have hd0 : d ≠ 0 := hd.ne_zero
  have hbd : b = d := by
    refine sqfree_unique (m := a * b) (m' := c * d) (mul_ne_zero ha hb0) (mul_ne_zero hc hd0) hb hd ?_
    calc (a * b) ^ 2 * b = a ^ 2 * b ^ 3 := by ring
      _ = c ^ 2 * d ^ 3 := h
      _ = (c * d) ^ 2 * d := by ring
  subst hbd
  refine ⟨?_, rfl⟩
  have h2 : a ^ 2 = c ^ 2 := Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hb0) 3) h
  exact Nat.pow_left_injective (by norm_num) h2

lemma exists_decomp {n : ℕ} (hn : n ≠ 0) (hP : n.Powerful) :
    ∃ a b : ℕ, 0 < a ∧ Squarefree b ∧ a ^ 2 * b ^ 3 = n := by
  obtain ⟨s, m, hs0, hm0, hmn, hs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  -- every prime factor of `s` divides `m`
  have hsm : s ∣ m := by
    rw [← Nat.factorization_le_iff_dvd hs0.ne' hm0.ne']
    intro p
    have h1 : s.factorization p ≤ 1 := hs.natFactorization_le_one p
    rcases Nat.lt_or_ge (s.factorization p) 1 with h0 | h0
    · omega
    · have hps : p ∣ s := Nat.dvd_of_factorization_pos (by omega)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization s ▸
        Finsupp.mem_support_iff.2 (by omega))
      have hpn : p ∣ n := hmn ▸ Dvd.dvd.mul_left hps _
      have hp2 : p ^ 2 ∣ m ^ 2 * s := hmn ▸ hP p (Nat.mem_primeFactors.2 ⟨hpp, hpn, hn⟩)
      have hpm : p ∣ m := by
        by_contra hpm
        have hcop : (p ^ 2).Coprime (m ^ 2) :=
          Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpm)
        have : p * p ∣ s := by
          rw [← pow_two]; exact hcop.dvd_of_dvd_mul_left hp2
        exact hpp.one_lt.ne' (Nat.isUnit_iff.1 (hs p this))
      have := (Nat.Prime.factorization_pos_of_dvd hpp hm0.ne' hpm)
      omega
  obtain ⟨c, rfl⟩ := hsm
  refine ⟨c, s, Nat.pos_of_ne_zero (by rintro rfl; simp at hm0), hs, ?_⟩
  rw [← hmn]; ring

end PowerfulFC
end

-- ===== PowerfulFC.Count =====
section
/-
# `#{n ≤ N powerful} = ∑_{b ≤ K squarefree} ⌊√(N / b³)⌋`
-/

open Finset

namespace PowerfulFC

lemma card_filter_sq_mul_cube_le (N b : ℕ) (hb : 0 < b) :
    #{a ∈ Icc 1 N | a ^ 2 * b ^ 3 ≤ N} = Nat.sqrt (N / b ^ 3) := by
  have hb3 : 0 < b ^ 3 := pow_pos hb 3
  have : ({a ∈ Icc 1 N | a ^ 2 * b ^ 3 ≤ N} : Finset ℕ) = Icc 1 (Nat.sqrt (N / b ^ 3)) := by
    ext a
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hb3]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      calc a ≤ a ^ 2 := by nlinarith
        _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ hb3
        _ ≤ N := h3
  rw [this, Nat.card_Icc]; omega

/-- The count of powerful numbers in `[1, N]`, given any `K` with `b³ ≤ N → b ≤ K`. -/
theorem card_powerful_eq_sum (N K : ℕ) (hK : ∀ b, 1 ≤ b → b ^ 3 ≤ N → b ≤ K) :
    #{n ∈ Icc 1 N | n.Powerful} =
      ∑ b ∈ {b ∈ Icc 1 K | Squarefree b}, Nat.sqrt (N / b ^ 3) := by
  set T : Finset (ℕ × ℕ) :=
    {p ∈ Icc 1 N ×ˢ Icc 1 K | Squarefree p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ N} with hT
  have himage : T.image (fun p => p.1 ^ 2 * p.2 ^ 3) = {n ∈ Icc 1 N | n.Powerful} := by
    ext n
    simp only [hT, mem_image, mem_filter, mem_product, mem_Icc, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨⟨⟨ha1, _⟩, hb1, _⟩, _, hle⟩, rfl⟩
      refine ⟨⟨?_, hle⟩, powerful_sq_mul_cube a b⟩
      exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
    · rintro ⟨⟨hn1, hnN⟩, hP⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := exists_decomp (by omega) hP
      have hb0 : 0 < b := Nat.pos_of_ne_zero hb.ne_zero
      have hb3 : 0 < b ^ 3 := pow_pos hb0 3
      have ha2 : 0 < a ^ 2 := pow_pos ha 2
      refine ⟨a, b, ⟨⟨⟨ha, ?_⟩, hb0, hK b hb0 ?_⟩, hb, hnN⟩, rfl⟩
      · calc a ≤ a ^ 2 := by nlinarith
          _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ hb3
          _ ≤ N := hnN
      · calc b ^ 3 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ ha2
          _ ≤ N := hnN
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 ^ 2 * p.2 ^ 3) T := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    simp only [hT, coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at hab hcd
    obtain ⟨h1, h2⟩ := decomp_unique (by omega) (by omega) hab.2.1 hcd.2.1 h
    exact Prod.ext h1 h2
  rw [← himage, card_image_of_injOn hinj]
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := {b ∈ Icc 1 K | Squarefree b})]
  · refine sum_congr rfl fun b hb => ?_
    simp only [mem_filter, mem_Icc] at hb
    rw [← card_filter_sq_mul_cube_le N b (by omega)]
    refine card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [hT, mem_filter, mem_product, mem_Icc] at hp ⊢
      obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _, h4⟩, h5⟩ := hp
      exact ⟨⟨h1, h2⟩, h5 ▸ h4⟩
    · intro p hp q hq h
      simp only [hT, mem_filter] at hp hq
      exact Prod.ext h (hp.2.trans hq.2.symm)
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha
      refine ⟨(a, b), ?_, rfl⟩
      simp only [hT, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨ha.1, hb.1⟩, hb.2, ha.2⟩, trivial⟩
  · intro p hp
    simp only [hT, coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at hp
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
    exact ⟨hp.1.2, hp.2.1⟩

end PowerfulFC
end

-- ===== LeanClassics.SquarefreeCount =====
section
/-
# Squarefree numbers: `#{n ≤ N squarefree} = 6N/π² + O(√N)`

`abs_card_squarefree_sub_le`: for `N ≥ 1`, `|#{1 ≤ n ≤ N : n squarefree} − 6N/π²| ≤ 5 √N`.

Proof. `μ(n)² = ∑_{d² ∣ n} μ(d)` (`sum_moebius_sq_dvd`, writing `n = b² a` with `a` squarefree,
so that `d² ∣ n ↔ d ∣ b`), hence `∑_{n ≤ N} μ(n)² = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`
(`sum_moebius_sq_eq`). Then `∑_d μ(d)/d² = 1/ζ(2) = 6/π²` (`tsum_moebius_div_sq`, from Mathlib's
`LSeries_zeta_mul_Lseries_moebius` and `riemannZeta_two`), whose tail beyond `M` is at most `1/M`
(`tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeCount

/-- With `a` squarefree, `d² ∣ b² a ↔ d ∣ b`. -/
lemma sq_dvd_iff {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0) :
    d * d ∣ b ^ 2 * a ↔ d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  constructor
  · intro h
    rw [← Nat.factorization_le_iff_dvd hd hb]
    rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)] at h
    intro p
    have hp := h p
    have h1 := ha.natFactorization_le_one p
    rw [Nat.factorization_mul hd hd, Nat.factorization_mul (pow_ne_zero 2 hb) ha0,
      Nat.factorization_pow] at hp
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hp
    omega
  · intro h
    exact (Nat.mul_dvd_mul h h).trans (by rw [sq]; exact Dvd.intro a rfl)

/-- `∑_{d² ∣ n} μ(d) = μ(n)²` for `n ≠ 0`. -/
lemma sum_moebius_sq_dvd {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with d * d ∣ n, (μ d : ℤ) = μ n ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have hb : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have hfil : n.divisors.filter (fun d => d * d ∣ n) = b.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hn h
      exact ⟨(sq_dvd_iff ha hb hd).mp (hab ▸ h), hb⟩
    · rintro ⟨h, -⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hb h
      have h2 := (sq_dvd_iff ha hb hd).mpr h
      rw [hab] at h2
      exact ⟨⟨(Dvd.intro d rfl).trans h2, hn⟩, h2⟩
  rw [hfil, moebius_sq]
  have hz : ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f b) moebius_mul_coe_zeta
    simp only [coe_mul_zeta_apply, one_apply] at this
    exact this
  rw [hz]
  by_cases hb1 : b = 1
  · subst hb1
    simp only [one_pow, one_mul] at hab
    simp [hab ▸ ha]
  · have hns : ¬ Squarefree n := fun hs => hb1 (Nat.isUnit_iff.mp
      (hs b (by rw [← hab, sq]; exact Dvd.intro a rfl)))
    simp [hb1, hns]

end LeanClassics.SquarefreeCount
end
end

-- ===== PowerfulFC.Main =====
section
/-
# Erdős–Szekeres: `Q(x) = (ζ(3/2)/ζ(3)) x^{1/2} + O(x^{1/3})`, in formal-conjectures' wording

The definitions `Q`, `A`, `B` and the statement `asymptotic_erdos_szekeres` are copied token for token from
google-deepmind/formal-conjectures `FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean` (commit `ea8e3e19`),
under the same `open` line.

Proof. Every powerful `n ≥ 1` is `a² b³` with `b` squarefree, uniquely (`PowerfulFC.Decomp`), so
`Q(x) = ∑_{b ≤ x^{1/3}} μ²(b) ⌊√(x/b³)⌋` (`PowerfulFC.Count`). Each floor is within 1 of `√x / b^{3/2}`
(`sqrt_floor_div_cube`), and `∑_{b > K} b^{-3/2} ≤ 2/√K` (`tail_le`), so with `K = ⌊x^{1/3}⌋`,
`|Q(x) − √x ∑_b μ²(b) b^{-3/2}| ≤ 5 x^{1/3}` for `x ≥ 1`. Finally `∑ μ²(b) b^{-3/2} = ζ(3/2)/ζ(3)`
(`LeanClassics.SquarefreeLSeries.LSeries_moebius_sq` at `s = 3/2`).
-/

open Filter Asymptotics Real


namespace PowerfulFC

open PowerfulNumbersDensity Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma Q_eq_card {x : ℝ} (hx : 0 ≤ x) : Q x = #{n ∈ Icc 1 ⌊x⌋₊ | n.Powerful} := by
  unfold Q
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
  rw [Nat.le_floor_iff hx, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  tauto

end PowerfulFC

end

open Finset Real

noncomputable section

namespace PowerfulFC.BG1

/-- `S N = #{(a, b) : a, b ≥ 1, a² b³ ≤ N}`. -/
def S (N : ℕ) : ℕ := #{p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N}
section moebius

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `S M = ∑_{c ≤ M} ⌊√(M / c³)⌋`. -/
lemma S_eq_sum (M : ℕ) : S M = ∑ c ∈ Icc 1 M, Nat.sqrt (M / c ^ 3) := by
  unfold S
  rw [card_filter, sum_product_right]
  refine sum_congr rfl fun c hc => ?_
  rw [← card_filter_sq_mul_cube_le M c (mem_Icc.1 hc).1, card_filter]

lemma sqrt_ne_zero_imp {N b : ℕ} (h : Nat.sqrt (N / b ^ 3) ≠ 0) : b ^ 3 ≤ N := by
  by_contra hc
  push Not at hc
  exact h (by rw [Nat.div_eq_of_lt hc]; rfl)

/-- **Möbius over sixth powers.** `#{n ∈ [1, N] powerful} = ∑_{d ≤ N} μ(d) S(N / d⁶)`. -/
theorem card_powerful_eq_sum_moebius (N : ℕ) :
    (#{n ∈ Icc 1 N | n.Powerful} : ℤ) = ∑ d ∈ Icc 1 N, μ d * S (N / d ^ 6) := by
  have hK : ∀ b, 1 ≤ b → b ^ 3 ≤ N → b ≤ N := fun b _ h => (Nat.le_self_pow (by norm_num) b).trans h
  rw [card_powerful_eq_sum N N hK, sum_filter]
  push_cast
  -- `1[b squarefree] = μ(b)² = ∑_{d² ∣ b} μ(d)`
  have h1 : ∀ b ∈ Icc 1 N, ((if Squarefree b then (Nat.sqrt (N / b ^ 3) : ℤ) else 0))
      = ∑ d ∈ b.divisors with d * d ∣ b, μ d * (Nat.sqrt (N / b ^ 3) : ℤ) := by
    intro b hb
    have hb0 : b ≠ 0 := by have := (mem_Icc.1 hb).1; omega
    rw [← sum_mul, LeanClassics.SquarefreeCount.sum_moebius_sq_dvd hb0]
    split_ifs with h
    · have := abs_moebius_eq_one_of_squarefree h
      have h2 : (μ b) ^ 2 = 1 := by rw [← sq_abs, this]; norm_num
      rw [h2, one_mul]
    · rw [moebius_eq_zero_of_not_squarefree h]; simp
  rw [sum_congr rfl h1, sum_sigma']
  simp_rw [S_eq_sum, Nat.cast_sum, mul_sum]
  rw [sum_sigma']
  refine sum_bij_ne_zero (fun x _ _ => ⟨x.2, x.1 / (x.2 * x.2)⟩) ?_ ?_ ?_ ?_
  · rintro ⟨b, d⟩ hx hne
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hb1, hbN⟩, ⟨hdb, -⟩, hdd⟩ := hx
    have hb0 : 0 < b := by omega
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb hb0
    have hb3 : b ^ 3 ≤ N := sqrt_ne_zero_imp (right_ne_zero_of_mul hne |> fun h => by exact_mod_cast h)
    obtain ⟨c, rfl⟩ := hdd
    have hdd0 : 0 < d * d := Nat.mul_pos hd0 hd0
    rw [Nat.mul_div_cancel_left c hdd0]
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hb0)
    refine ⟨⟨hd0, (Nat.le_of_dvd hb0 hdb).trans hbN⟩, hc0, ?_⟩
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc c * d ^ 6 ≤ c ^ 3 * d ^ 6 := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) c)
      _ = (d * d * c) ^ 3 := by ring
      _ ≤ N := hb3
  · rintro ⟨b, d⟩ hx hne ⟨b', d'⟩ hx' hne' h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [mem_sigma, mem_filter] at hx hx'
    have e1 := Nat.div_mul_cancel hx.2.2
    have e2 := Nat.div_mul_cancel hx'.2.2
    have : b = b' := by
      rw [← e1, ← e2]; exact congrArg (· * (d * d)) (eq_of_heq h2)
    subst this; rfl
  · rintro ⟨d, c⟩ hx hne
    simp only [mem_sigma, mem_Icc] at hx
    obtain ⟨⟨hd1, -⟩, hc1, hcN⟩ := hx
    have hd0 : 0 < d := hd1
    have hb0 : 0 < d * d * c := by positivity
    have hne' : Nat.sqrt (N / d ^ 6 / c ^ 3) ≠ 0 := by
      intro h; apply hne; simp [h]
    rw [Nat.div_div_eq_div_mul] at hne'
    have hb3 : (d * d * c) ^ 3 ≤ N := by
      exact sqrt_ne_zero_imp (b := d * d * c) (N := N) (by
        rw [show (d * d * c) ^ 3 = d ^ 6 * c ^ 3 by ring]; exact hne')
    refine ⟨⟨d * d * c, d⟩, ?_, ?_, ?_⟩
    · simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors]
      refine ⟨⟨hb0, (Nat.le_self_pow (by norm_num) _).trans hb3⟩, ⟨⟨c * d, by ring⟩, hb0.ne'⟩,
        ⟨c, by ring⟩⟩
    · simp only at hne ⊢
      refine mul_ne_zero (left_ne_zero_of_mul hne) ?_
      rw [show (d * d * c) ^ 3 = d ^ 6 * c ^ 3 by ring]
      exact_mod_cast hne'
    · simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Nat.mul_div_cancel_left c (Nat.mul_pos hd0 hd0)
  · rintro ⟨b, d⟩ hx hne
    simp only [mem_sigma, mem_filter, mem_Icc, Nat.mem_divisors] at hx
    obtain ⟨⟨hb1, -⟩, ⟨hdb, -⟩, c, rfl⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb (by omega)
    simp only
    rw [Nat.mul_div_cancel_left c (Nat.mul_pos hd0 hd0), Nat.div_div_eq_div_mul]
    congr 4
    ring

/-- **Möbius over sixth powers, FC's `Q`.** For real `x ≥ 0`, `Q(x) = ∑_{d ≤ x} μ(d) S⌊x / d⁶⌋`
(terms with `d⁶ > x` vanish). -/
theorem Q_eq_sum_moebius_S {x : ℝ} (hx : 0 ≤ x) :
    (PowerfulNumbersDensity.Q x : ℤ) = ∑ d ∈ Icc 1 ⌊x⌋₊, μ d * S ⌊x / ((d ^ 6 : ℕ) : ℝ)⌋₊ := by
  rw [Q_eq_card hx, card_powerful_eq_sum_moebius]
  refine sum_congr rfl fun d _ => ?_
  rw [Nat.floor_div_natCast]

end moebius

end PowerfulFC.BG1
end

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeRH

open LeanClassics.SquarefreeCount

/-- The Mertens function `M(n) = ∑_{k ≤ n} μ(k)`, as a real number. -/
def mert (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, (μ k : ℝ)
lemma sum_rpow_neg_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (K : ℕ) :
    ∑ m ∈ Ioc 0 K, (m : ℝ) ^ (-b) ≤ (K : ℝ) ^ (1 - b) / (1 - b) := by
  have h1b : 0 < 1 - b := by linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp only [Finset.Ioc_self, sum_empty, Nat.cast_zero]; positivity
  have hsplit : ∑ m ∈ Ioc 0 K, (m : ℝ) ^ (-b) = 1 + ∑ i ∈ Ico 1 K, ((i + 1 : ℕ) : ℝ) ^ (-b) := by
    have : Ioc 0 K = insert 1 ((Ico 1 K).map ⟨(· + 1), add_left_injective 1⟩) := by
      ext m; simp only [mem_Ioc, mem_insert, mem_map, mem_Ico, Function.Embedding.coeFn_mk]
      constructor
      · intro h
        rcases eq_or_ne m 1 with rfl | h1
        · exact Or.inl rfl
        · exact Or.inr ⟨m - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro (rfl | ⟨i, hi, rfl⟩) <;> omega
    rw [this, sum_insert, sum_map]
    · simp
    · simp only [mem_map, mem_Ico, Function.Embedding.coeFn_mk, not_exists, not_and]
      intro i hi; omega
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-b)) (Set.Icc (1 : ℕ) K) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le one_pos (by simpa using hx.1)
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hint := hanti.sum_le_integral_Ico hK
  have hI : ∫ x in ((1 : ℕ) : ℝ)..(K : ℝ), x ^ (-b) = ((K : ℝ) ^ (1 - b) - 1) / (1 - b) := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp only [Nat.cast_one, Real.one_rpow]
    rw [show -b + 1 = 1 - b by ring]
  rw [hI] at hint
  rw [hsplit]
  have hle : (1 : ℝ) ≤ 1 / (1 - b) := by rw [le_div_iff₀ h1b]; linarith
  have : 1 + ((K : ℝ) ^ (1 - b) - 1) / (1 - b) ≤ (K : ℝ) ^ (1 - b) / (1 - b) := by
    rw [sub_div]; linarith [show (1 : ℝ) / (1 - b) = 1 / (1 - b) from rfl]
  linarith

lemma abs_sum_Ioc_moebius_le (y r : ℕ) :
    |∑ d ∈ Ioc y r, (μ d : ℝ)| ≤ if y < r then |mert r| + |mert y| else 0 := by
  split_ifs with h
  · have e := sum_Ioc_consecutive (fun d => (μ d : ℝ)) (Nat.zero_le y) h.le
    have : ∑ d ∈ Ioc y r, (μ d : ℝ) = mert r - mert y := by rw [mert, mert, ← e]; ring
    rw [this]; exact abs_sub _ _
  · rw [Finset.Ioc_eq_empty h, sum_empty, abs_zero]


end LeanClassics.SquarefreeRH
end

/-
# Error-term improvement, rung R1: the large-`d` part under a Mertens bound

`Q(N) = ∑_{d ≤ N} μ(d) S(N / d⁶)` (`BG1.card_powerful_eq_sum_moebius`). Split the `d`-sum at `E`.
Writing `S(N / d⁶) = #{(a, b) ∈ [1, N]² : d⁶ a²b³ ≤ N}` and swapping the sums,

`∑_{E < d ≤ N} μ(d) S(N / d⁶) = ∑_{(a, b) ∈ [1, N]²} (M(r) − M(E))`, `r = max{d ≤ N : d⁶ a²b³ ≤ N}`

(`sum_split`; Dirichlet's hyperbola trick, no third term). A pair contributes only if `r > E`, i.e.
`(E + 1)⁶ a²b³ ≤ N`, and then `|M(r) − M(E)| ≤ 2C r^a ≤ 2C (N / a²b³)^{a/6}` when `|M(n)| ≤ C n^a`.
With the elementary `∑_{a²b³ ≤ K} (a²b³)^{−θ} ≤ 3 K^{1/2−θ} / (1 − 2θ)` (`sum_wt_rpow_le`, `θ < 1/2`):

`|∑_{d ≤ N} μ(d) S(N/d⁶) − ∑_{d ≤ E} μ(d) S(N/d⁶)| ≤ 6C/(1 − a/3) · N^{1/2} (E + 1)^{a−3}`
(`abs_sum_sub_small_le`, `0 ≤ a < 3`).

**Unconditional**: the Mertens bound is a hypothesis `hM`. Under RH it holds with `a = 1/2 + ε`
(`LeanClassics.SquarefreeRH.exists_mert_le`), giving `N^{1/2} E^{−5/2+ε}`.
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace PowerfulFC
open Real

lemma telescope_step {m : ℝ} (hm : 1 ≤ m) :
    1 / ((m + 1) * √(m + 1)) ≤ 2 * (1 / √m - 1 / √(m + 1)) := by
  have hm0 : 0 < m := by linarith
  set s := √m with hs
  set t := √(m + 1) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 hm0
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = m := Real.sq_sqrt hm0.le
  have ht2 : t ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have hm1 : m + 1 = t ^ 2 := ht2.symm
  rw [hm1]
  have e : 2 * (1 / s - 1 / t) = 2 * (t - s) / (s * t) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  -- 1 * (s t) ≤ 2 (t - s) t² t, using (t - s)(t + s) = 1
  have hdiff : (t - s) * (t + s) = 1 := by nlinarith
  have htms : 0 < t - s := by nlinarith
  nlinarith [mul_pos hs0 ht0, mul_pos htms ht0, mul_pos (mul_pos htms ht0) ht0]

lemma rpow_three_halves {n : ℕ} : (n : ℝ) ^ ((3 : ℝ) / 2) = n * √n := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' (Nat.cast_nonneg n) (by norm_num),
    Real.rpow_one, Real.sqrt_eq_rpow]

end PowerfulFC

namespace PowerfulFC.ETI

open PowerfulFC.BG1 (S)
open LeanClassics.SquarefreeRH (mert sum_rpow_neg_le abs_sum_Ioc_moebius_le)

/-- `r N m`: the largest `d ≤ N` with `d⁶ m ≤ N`. -/
def r (N m : ℕ) : ℕ := Nat.findGreatest (fun d => d ^ 6 * m ≤ N) N

lemma r_spec (N m : ℕ) : r N m ^ 6 * m ≤ N :=
  Nat.findGreatest_spec (P := fun d => d ^ 6 * m ≤ N) (Nat.zero_le N) (by simp)

lemma le_r {N m d : ℕ} (hdN : d ≤ N) (h : d ^ 6 * m ≤ N) : d ≤ r N m :=
  Nat.le_findGreatest hdN h

lemma filter_Ioc_eq (N m E : ℕ) : {d ∈ Ioc E N | d ^ 6 * m ≤ N} = Ioc E (r N m) := by
  ext d
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, le_r h2 h3⟩
  · rintro ⟨h1, h2⟩
    have hrN : r N m ≤ N := Nat.findGreatest_le N
    exact ⟨⟨h1, h2.trans hrN⟩, (Nat.mul_le_mul_right m (Nat.pow_le_pow_left h2 6)).trans (r_spec N m)⟩

/-- The box `[1, N]²` of pairs `(a, b)`. -/
abbrev box (N : ℕ) : Finset (ℕ × ℕ) := Icc 1 N ×ˢ Icc 1 N

/-- The weight `a² b³` of a pair. -/
abbrev wt (p : ℕ × ℕ) : ℕ := p.1 ^ 2 * p.2 ^ 3

lemma le_wt {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : a ≤ a ^ 2 * b ^ 3 ∧ b ≤ a ^ 2 * b ^ 3 := by
  constructor
  · calc a ≤ a ^ 2 := Nat.le_self_pow two_ne_zero a
      _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
  · calc b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
      _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)

lemma one_le_wt {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ box N) : 1 ≤ wt p := by
  simp only [mem_product, mem_Icc] at hp
  exact (le_wt hp.1.1 hp.2.1).1 |> le_trans hp.1.1

/-- `S(N / d⁶)` counts the pairs of the full box `[1, N]²` with `d⁶ a²b³ ≤ N`. -/
lemma S_div_eq (N d : ℕ) (hd : 1 ≤ d) : S (N / d ^ 6) = #{p ∈ box N | d ^ 6 * wt p ≤ N} := by
  unfold S
  have hd6 : 0 < d ^ 6 := by positivity
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha1, haM⟩, hb1, hbM⟩, h⟩
    have hM : N / d ^ 6 ≤ N := Nat.div_le_self _ _
    refine ⟨⟨⟨ha1, haM.trans hM⟩, hb1, hbM.trans hM⟩, ?_⟩
    rw [Nat.le_div_iff_mul_le hd6] at h
    linarith
  · rintro ⟨⟨⟨ha1, -⟩, hb1, -⟩, h⟩
    have h' : a ^ 2 * b ^ 3 ≤ N / d ^ 6 := (Nat.le_div_iff_mul_le hd6).2 (by linarith)
    obtain ⟨ha, hb⟩ := le_wt ha1 hb1
    exact ⟨⟨⟨ha1, ha.trans h'⟩, hb1, hb.trans h'⟩, h'⟩

/-- **The `d`-hyperbola split.** For `E ≤ N`:
`∑_{d ≤ N} μ(d) S(N/d⁶) = ∑_{d ≤ E} μ(d) S(N/d⁶) + ∑_{(a,b) ∈ [1,N]²} ∑_{E < d ≤ r(N, a²b³)} μ(d)`. -/
theorem sum_split (N E : ℕ) (hE : E ≤ N) :
    ∑ d ∈ Icc 1 N, μ d * (S (N / d ^ 6) : ℤ) =
      ∑ d ∈ Icc 1 E, μ d * (S (N / d ^ 6) : ℤ) + ∑ p ∈ box N, ∑ d ∈ Ioc E (r N (wt p)), μ d := by
  have hsplit : Icc 1 N = Icc 1 E ∪ Ioc E N := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 E) (Ioc E N) :=
    disjoint_left.2 fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  congr 1
  calc ∑ d ∈ Ioc E N, μ d * (S (N / d ^ 6) : ℤ)
      = ∑ d ∈ Ioc E N, ∑ p ∈ box N, if d ^ 6 * wt p ≤ N then μ d else 0 := by
        refine sum_congr rfl fun d hd => ?_
        rw [S_div_eq N d (by have := (mem_Ioc.1 hd).1; omega), card_filter, Nat.cast_sum, mul_sum]
        refine sum_congr rfl fun p _ => ?_
        split_ifs <;> simp
    _ = ∑ p ∈ box N, ∑ d ∈ Ioc E N, if d ^ 6 * wt p ≤ N then μ d else 0 := sum_comm
    _ = ∑ p ∈ box N, ∑ d ∈ Ioc E (r N (wt p)), μ d := by
        refine sum_congr rfl fun p _ => ?_
        rw [← sum_filter, filter_Ioc_eq]

lemma rpow_r_le {N m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 ≤ a) :
    (r N m : ℝ) ^ a ≤ ((N : ℝ) / m) ^ (a / 6) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h6 : (r N m : ℝ) ^ (6 : ℕ) ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ hm0]; exact_mod_cast r_spec N m
  calc (r N m : ℝ) ^ a = ((r N m : ℝ) ^ (6 : ℕ)) ^ (a / 6) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h6 (by positivity)

/-- One pair's contribution: zero unless `(E + 1)⁶ m ≤ N`, and then `≤ 2C (N / m)^{a/6}`. -/
lemma abs_inner_le {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hM : ∀ n : ℕ, |mert n| ≤ C * (n : ℝ) ^ a)
    (N E m : ℕ) (hm : 1 ≤ m) :
    |∑ d ∈ Ioc E (r N m), (μ d : ℝ)| ≤
      if (E + 1) ^ 6 * m ≤ N then 2 * C * ((N : ℝ) / m) ^ (a / 6) else 0 := by
  have h := abs_sum_Ioc_moebius_le E (r N m)
  split_ifs at h with hEr
  · have hc : (E + 1) ^ 6 * m ≤ N :=
      (Nat.mul_le_mul_right m (Nat.pow_le_pow_left hEr 6)).trans (r_spec N m)
    simp only [hc, ↓reduceIte]
    have h1 := hM (r N m)
    have h2 := hM E
    have h3 : (E : ℝ) ^ a ≤ (r N m : ℝ) ^ a :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hEr.le) ha
    have h4 := rpow_r_le (N := N) hm ha
    calc _ ≤ |mert (r N m)| + |mert E| := h
      _ ≤ C * (r N m : ℝ) ^ a + C * (r N m : ℝ) ^ a := by
          have := mul_le_mul_of_nonneg_left h3 hC
          linarith
      _ = 2 * C * (r N m : ℝ) ^ a := by ring
      _ ≤ _ := by gcongr
  · split_ifs
    · exact h.trans (by positivity)
    · exact h

lemma wt_rpow (a b : ℕ) (θ : ℝ) :
    (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ^ (-θ) = (a : ℝ) ^ (-(2 * θ)) * (b : ℝ) ^ (-(3 * θ)) := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    show ((a : ℝ) ^ 2) = (a : ℝ) ^ (2 : ℝ) by norm_cast,
    show ((b : ℝ) ^ 3) = (b : ℝ) ^ (3 : ℝ) by norm_cast,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  congr 1 <;> congr 1 <;> ring

lemma sum_inv_three_halves_le (n : ℕ) :
    ∑ b ∈ Icc 1 (n + 1), 1 / ((b : ℝ) * √b) ≤ 3 - 2 / √((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h := PowerfulFC.telescope_step (m := (n : ℝ) + 1) (by have := n.cast_nonneg (α := ℝ); linarith)
    push_cast at ih h ⊢
    have e : (n : ℝ) + 1 + 1 = (n + 1 : ℝ) + 1 := by ring
    rw [e]
    have hx : 2 / √((n : ℝ) + 1) = 2 * (1 / √((n : ℝ) + 1)) := by ring
    have hy : 2 / √((n : ℝ) + 1 + 1) = 2 * (1 / √((n : ℝ) + 1 + 1)) := by ring
    rw [hx] at ih; rw [hy]
    linarith

lemma sum_rpow_three_halves_le (N : ℕ) : ∑ b ∈ Icc 1 N, (b : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have e : ∀ b ∈ Icc 1 (n + 1), (b : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((b : ℝ) * √b) := by
    intro b _
    rw [Real.rpow_neg (by positivity), PowerfulFC.rpow_three_halves, one_div]
  rw [sum_congr rfl e]
  have := sum_inv_three_halves_le n
  have : 0 ≤ 2 / √((n : ℝ) + 1) := by positivity
  linarith

/-- For fixed `b ≥ 1`: `∑_{a : a²b³ ≤ K} (a²b³)^{−θ} ≤ K^{1/2−θ} b^{−3/2} / (1 − 2θ)`. -/
lemma sum_a_le {θ K : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hK : 0 ≤ K) (N b : ℕ) (hb : 1 ≤ b) :
    ∑ a ∈ Icc 1 N, (if (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ≤ K then (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ^ (-θ) else 0)
      ≤ 1 / (1 - 2 * θ) * K ^ (1 / 2 - θ) * (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h2θ : 0 < 1 - 2 * θ := by linarith
  set t : ℝ := √(K / (b : ℝ) ^ 3) with ht
  have hterm : ∀ a ∈ Icc 1 N,
      (if (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ≤ K then (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ^ (-θ) else 0) ≤
        (b : ℝ) ^ (-(3 * θ)) * (if a ∈ Ioc 0 ⌊t⌋₊ then (a : ℝ) ^ (-(2 * θ)) else 0) := by
    intro a ham
    have ha1 : 1 ≤ a := (mem_Icc.1 ham).1
    split_ifs with h1 h2
    · rw [wt_rpow]; apply le_of_eq; ring
    · exfalso; apply h2
      refine mem_Ioc.2 ⟨ha1, Nat.le_floor ?_⟩
      rw [ht, Real.le_sqrt (by positivity) (by positivity), le_div_iff₀ (by positivity)]
      push_cast at h1; linarith
    · positivity
    · simp
  calc _ ≤ ∑ a ∈ Icc 1 N, (b : ℝ) ^ (-(3 * θ)) * (if a ∈ Ioc 0 ⌊t⌋₊ then (a : ℝ) ^ (-(2 * θ)) else 0) :=
        sum_le_sum hterm
    _ = (b : ℝ) ^ (-(3 * θ)) * ∑ a ∈ Icc 1 N ∩ Ioc 0 ⌊t⌋₊, (a : ℝ) ^ (-(2 * θ)) := by
        rw [← mul_sum, sum_ite_mem]
    _ ≤ (b : ℝ) ^ (-(3 * θ)) * ∑ a ∈ Ioc 0 ⌊t⌋₊, (a : ℝ) ^ (-(2 * θ)) := by
        exact mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun i _ _ => by positivity)) (by positivity)
    _ ≤ (b : ℝ) ^ (-(3 * θ)) * ((⌊t⌋₊ : ℝ) ^ (1 - 2 * θ) / (1 - 2 * θ)) := by
        gcongr; exact sum_rpow_neg_le (by linarith) (by linarith) _
    _ ≤ (b : ℝ) ^ (-(3 * θ)) * (t ^ (1 - 2 * θ) / (1 - 2 * θ)) := by
        gcongr
        exact Nat.floor_le (by positivity)
    _ = 1 / (1 - 2 * θ) * K ^ (1 / 2 - θ) * (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [ht, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.div_rpow hK (by positivity),
          show ((b : ℝ) ^ 3) = (b : ℝ) ^ (3 : ℝ) by norm_cast, ← Real.rpow_mul hb0.le]
        have e1 : (1 / 2 : ℝ) * (1 - 2 * θ) = 1 / 2 - θ := by ring
        rw [e1]
        have e2 : (b : ℝ) ^ (-(3 / 2 : ℝ)) = (b : ℝ) ^ (-(3 * θ)) / (b : ℝ) ^ (3 * (1 / 2 - θ)) := by
          rw [← Real.rpow_sub hb0]; congr 1; ring
        rw [e2]
        field_simp

/-- **Elementary count.** `∑_{(a,b) ∈ [1,N]², a²b³ ≤ K} (a²b³)^{−θ} ≤ 3 K^{1/2−θ} / (1 − 2θ)`, `0 ≤ θ < 1/2`. -/
lemma sum_wt_rpow_le {θ K : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hK : 0 ≤ K) (N : ℕ) :
    ∑ p ∈ box N, (if (wt p : ℝ) ≤ K then (wt p : ℝ) ^ (-θ) else 0) ≤
      3 / (1 - 2 * θ) * K ^ (1 / 2 - θ) := by
  have h2θ : 0 < 1 - 2 * θ := by linarith
  rw [sum_product_right]
  calc _ ≤ ∑ b ∈ Icc 1 N, 1 / (1 - 2 * θ) * K ^ (1 / 2 - θ) * (b : ℝ) ^ (-(3 / 2 : ℝ)) :=
        sum_le_sum fun b hb => sum_a_le hθ0 hθ hK N b (mem_Icc.1 hb).1
    _ = 1 / (1 - 2 * θ) * K ^ (1 / 2 - θ) * ∑ b ∈ Icc 1 N, (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [mul_sum]
    _ ≤ 1 / (1 - 2 * θ) * K ^ (1 / 2 - θ) * 3 := by
        gcongr; exact sum_rpow_three_halves_le N
    _ = 3 / (1 - 2 * θ) * K ^ (1 / 2 - θ) := by ring

/-- **Rung R1.** If `|M(n)| ≤ C n^a` for all `n` (`0 ≤ a < 3`), then for `E ≤ N`
`|∑_{d ≤ N} μ(d) S(N/d⁶) − ∑_{d ≤ E} μ(d) S(N/d⁶)| ≤ 6C/(1 − a/3) · N^{1/2} (E + 1)^{a−3}`. -/
theorem abs_sum_sub_small_le {C a : ℝ} (hC : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a < 3)
    (hM : ∀ n : ℕ, |mert n| ≤ C * (n : ℝ) ^ a) (N E : ℕ) (hE : E ≤ N) :
    |(∑ d ∈ Icc 1 N, (μ d : ℝ) * S (N / d ^ 6)) - ∑ d ∈ Icc 1 E, (μ d : ℝ) * S (N / d ^ 6)| ≤
      6 * C / (1 - a / 3) * (N : ℝ) ^ ((1 : ℝ) / 2) * ((E : ℝ) + 1) ^ (a - 3) := by
  have hid := congrArg (fun z : ℤ => (z : ℝ)) (sum_split N E hE)
  push_cast at hid
  have hidR : (∑ d ∈ Icc 1 N, (μ d : ℝ) * S (N / d ^ 6)) - ∑ d ∈ Icc 1 E, (μ d : ℝ) * S (N / d ^ 6)
      = ∑ p ∈ box N, ∑ d ∈ Ioc E (r N (wt p)), (μ d : ℝ) := by
    rw [hid]; ring
  rw [hidR]
  have hE1 : (0 : ℝ) < (E : ℝ) + 1 := by positivity
  set K : ℝ := (N : ℝ) / ((E : ℝ) + 1) ^ 6 with hK
  have hK0 : 0 ≤ K := by positivity
  have h3 : 0 < 1 - a / 3 := by linarith
  calc |∑ p ∈ box N, ∑ d ∈ Ioc E (r N (wt p)), (μ d : ℝ)|
      ≤ ∑ p ∈ box N, |∑ d ∈ Ioc E (r N (wt p)), (μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ box N, 2 * C * (N : ℝ) ^ (a / 6) *
          (if (wt p : ℝ) ≤ K then (wt p : ℝ) ^ (-(a / 6)) else 0) := by
        refine sum_le_sum fun p hp => ?_
        have hm := one_le_wt hp
        have hm0 : (0 : ℝ) < wt p := by exact_mod_cast hm
        refine (abs_inner_le hC ha0 hM N E (wt p) hm).trans ?_
        split_ifs with h1 h2
        · rw [Real.div_rpow (by positivity) hm0.le, Real.rpow_neg hm0.le]
          apply le_of_eq; ring
        · exfalso; apply h2
          rw [hK, le_div_iff₀ (by positivity)]
          have h1' : (((E + 1) ^ 6 : ℕ) : ℝ) * (wt p : ℝ) ≤ N := by exact_mod_cast h1
          rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h1'
          linarith
        · positivity
        · simp
    _ = 2 * C * (N : ℝ) ^ (a / 6) *
          ∑ p ∈ box N, (if (wt p : ℝ) ≤ K then (wt p : ℝ) ^ (-(a / 6)) else 0) := by
        rw [mul_sum]
    _ ≤ 2 * C * (N : ℝ) ^ (a / 6) * (3 / (1 - 2 * (a / 6)) * K ^ (1 / 2 - a / 6)) := by
        gcongr
        exact sum_wt_rpow_le (by positivity) (by linarith) hK0 N
    _ = 6 * C / (1 - a / 3) * (N : ℝ) ^ ((1 : ℝ) / 2) * ((E : ℝ) + 1) ^ (a - 3) := by
        rw [hK, Real.div_rpow (by positivity) (by positivity),
          show ((E : ℝ) + 1) ^ 6 = ((E : ℝ) + 1) ^ (6 : ℝ) by norm_cast, ← Real.rpow_mul hE1.le]
        have e1 : (N : ℝ) ^ (a / 6) * (N : ℝ) ^ (1 / 2 - a / 6) = (N : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add' (by positivity) (by norm_num)]; congr 1; ring
        have e2 : ((E : ℝ) + 1) ^ (a - 3) = 1 / ((E : ℝ) + 1) ^ (6 * (1 / 2 - a / 6)) := by
          rw [one_div, ← Real.rpow_neg hE1.le]; congr 1; ring
        rw [e2, show (1 : ℝ) - 2 * (a / 6) = 1 - a / 3 by ring, ← e1]
        field_simp
        ring

end PowerfulFC.ETI

end

open Finset Real PowerfulNumbersDensity PowerfulFC.BG1
open scoped ArithmeticFunction.Moebius

theorem OMA.solution : OMA.R_PowerfulNumbersDensity_error_term_improvement_R1.H2 := by
  intro a C t ha ha1 hC ht ht6 hM
  let K := 6 * C / (1 - a / 3)
  have hK : 0 ≤ K := div_nonneg (by positivity) (by linarith)
  refine ⟨K, hK, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  let N := ⌊x⌋₊
  let D := ⌊x ^ t⌋₊
  have hDN : D ≤ N := Nat.floor_le_floor (Real.rpow_le_self_of_one_le hx (by linarith))
  have hQ : (Q x : ℝ) = ∑ d ∈ Icc 1 N, (μ d : ℝ) * S (N / d ^ 6) := by
    have e := congrArg (Int.cast : ℤ → ℝ) (card_powerful_eq_sum_moebius N)
    push_cast at e
    rw [PowerfulFC.Q_eq_card hx0.le]
    exact_mod_cast e
  change |(Q x : ℝ) - ∑ d ∈ Icc 1 D, (μ d : ℝ) * S (N / d ^ 6)| ≤ _
  rw [hQ]
  refine (PowerfulFC.ETI.abs_sum_sub_small_le hC ha (by linarith) hM N D hDN).trans ?_
  have hN : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ x ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0.le) (by norm_num)
  have hD : ((D : ℝ) + 1) ^ (a - 3) ≤ (x ^ t) ^ (a - 3) :=
    Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx0 _) (Nat.lt_floor_add_one _).le (by linarith)
  change K * _ * _ ≤ _
  calc
    _ ≤ K * x ^ ((1 : ℝ) / 2) * (x ^ t) ^ (a - 3) := by gcongr
    _ = K * x ^ (1 / 2 + (a - 3) * t) := by
      rw [← Real.rpow_mul hx0.le, mul_assoc, ← Real.rpow_add hx0, mul_comm t (a - 3)]
