import OMAReductions.R_Erdos360_erdos_360_variants_alon_erdos_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand

/-!
# Alon-Erdős Upper Bound for Erdős Problem 360

Proves `OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1.H2`:
`Erdos360.f n = O(n^(1/3) / (log n)^(1/3) * (log log n)^(1/3))`.

The proof is completely elementary and self-contained:
1. **3-step coloring bound** (adapted from `proofs/Erdos360.erdos_360.R1.H1.lean`, Credit:
   @OrangeHeadz, following Conlon-Fox-Pham): for any `n ≥ 2`, prime `d ∤ n`, and finite set `S`
   of primes not dividing `n` with `d ∈ S`, letting `R' := (Icc 1 (n / d)).filter (∀ p ∈ S, ¬ p ∣ ·)`,
   `Erdos360.f n ≤ S.card + 2 * d.totient + (R'.card / d + 1)`.
2. **Elementary prime-counting and Mertens upper bounds** from `Chebyshev.theta_le_log4_mul_x`
   and Legendre's divisibility `∏_{p ≤ L} p^(L / p) ∣ L!`:
   - `π(y) ≤ 6 * y / log y` for all `y ≥ 2`,
   - `∑_{p ≤ L} 1 / p ≤ log (log L) + 6` for all `L ≥ 3`,
   - `∏_{p ∣ n} (1 - 1 / p)⁻¹ ≤ exp 9 * log (log n)` for `⌊log n⌋₊ ≥ 3`.
3. **No-sieve smooth+prime decomposition of `R'`**: choosing `D = ⌊g(n)⌋₊`, four applications
   of Bertrand's postulate find a prime `d ∈ (D, 16 * D]` with `¬ d ∣ n`. Setting
   `y = 16 * D * ⌈log n⌉₊` gives `n / d < y ^ 2`, so every `t ∈ R'` factors as `t = u * v`
   with `u` being `n`-smooth and either `v = 1` (bounded via Rankin's trick) or `v` prime in
   `(y, (n / d) / u]` (bounded via `π` and the Euler product `∏_{p ∣ n} (1 - 1 / p)⁻¹`).
-/

open Finset Filter Asymptotics
open scoped BigOperators

namespace Erdos360Upper

/- ### Part 1: Three-step coloring bound (adapted from Erdos360.erdos_360.R1.H1) -/

private lemma f_le_of_coloring {γ : Type} [DecidableEq γ] (n : ℕ) (c : ℕ → γ) (T : Finset γ)
    (hT : ∀ t ∈ Icc 1 (n - 1), c t ∈ T)
    (hc : ∀ B : Finset ℕ, B ⊆ Icc 1 (n - 1) → (∀ t ∈ B, ∀ u ∈ B, c t = c u) →
      ∑ t ∈ B, t ≠ n) :
    Erdos360.f n ≤ T.card := by
  classical
  have hindep : (T.image (fun k => (Icc 1 (n - 1)).filter (fun t => c t = k))).SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hA)
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hB)
    show Disjoint ((Icc 1 (n - 1)).filter (fun t => c t = k))
      ((Icc 1 (n - 1)).filter (fun t => c t = l))
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    apply hAB
    rw [← (mem_filter.mp ht1).2, ← (mem_filter.mp ht2).2]
  have hsup : (T.image (fun k => (Icc 1 (n - 1)).filter (fun t => c t = k))).sup id
      = Icc 1 (n - 1) := by
    ext t
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨A, hA, ht⟩
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hA
      exact (mem_filter.mp ht).1
    · intro ht
      exact ⟨_, Finset.mem_image.mpr ⟨c t, hT t ht, rfl⟩, mem_filter.mpr ⟨ht, rfl⟩⟩
  have hcard : (Finpartition.ofErase _ hindep hsup).parts.card ≤ T.card :=
    (Finset.card_erase_le).trans Finset.card_image_le
  refine le_trans (Nat.sInf_le ⟨Finpartition.ofErase _ hindep hsup, rfl, ?_⟩) hcard
  intro A hA hn
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hA)
  obtain ⟨B, hB, hsum⟩ := hn
  have hmem : ∀ t ∈ B, t ∈ (Icc 1 (n - 1)).filter (fun t => c t = k) :=
    fun t ht => Finset.mem_coe.mp (hB (Finset.mem_coe.mpr ht))
  exact hc B (fun t ht => (mem_filter.mp (hmem t ht)).1)
    (fun t ht u hu => ((mem_filter.mp (hmem t ht)).2).trans ((mem_filter.mp (hmem u hu)).2).symm)
    hsum.symm

private def col (n d : ℕ) (S R : Finset ℕ) (t : ℕ) : ℕ ⊕ (ℕ ⊕ (ℕ × Bool)) :=
  if h : ∃ p, p ∈ S ∧ p ∣ t then Sum.inl (Nat.find h)
  else if t ≤ n / d then Sum.inr (Sum.inl ((R.filter (· < t)).card / d))
  else Sum.inr (Sum.inr (t % d, decide (∃ j, j < d ∧ (j * t) % d = n % d ∧ j * t < n)))

private def colSet (d : ℕ) (S R : Finset ℕ) : Finset (ℕ ⊕ (ℕ ⊕ (ℕ × Bool))) :=
  S.disjSum ((range (R.card / d + 1)).disjSum
    (((range d).filter (fun a => d.Coprime a)) ×ˢ (Finset.univ : Finset Bool)))

private lemma colSet_card (d : ℕ) (S R : Finset ℕ) :
    (colSet d S R).card = S.card + ((R.card / d + 1) + d.totient * 2) := by
  unfold colSet
  rw [Finset.card_disjSum, Finset.card_disjSum, Finset.card_product, Finset.card_range,
    Nat.totient_eq_card_coprime]
  simp

private lemma col_inl {n d : ℕ} {S R : Finset ℕ} {t p : ℕ} (h : col n d S R t = Sum.inl p) :
    p ∈ S ∧ p ∣ t := by
  unfold col at h
  split_ifs at h with h1 h2
  have h3 := Sum.inl.inj h
  subst h3
  exact Nat.find_spec h1

private lemma col_mid {n d : ℕ} {S R : Finset ℕ} {t i : ℕ}
    (h : col n d S R t = Sum.inr (Sum.inl i)) :
    (∀ p ∈ S, ¬ p ∣ t) ∧ t ≤ n / d ∧ (R.filter (· < t)).card / d = i := by
  unfold col at h
  split_ifs at h with h1 h2
  all_goals first
    | exact ⟨fun p hp hpt => h1 ⟨p, hp, hpt⟩, h2, Sum.inl.inj (Sum.inr.inj h)⟩
    | cases h

private lemma col_big {n d : ℕ} {S R : Finset ℕ} {t a : ℕ} {s : Bool}
    (h : col n d S R t = Sum.inr (Sum.inr (a, s))) :
    (∀ p ∈ S, ¬ p ∣ t) ∧ n / d < t ∧ t % d = a ∧
      (s = true ↔ ∃ j, j < d ∧ (j * t) % d = n % d ∧ j * t < n) := by
  unfold col at h
  split_ifs at h with h1 h2
  all_goals first
    | (obtain ⟨ha, hs⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
       refine ⟨fun p hp hpt => h1 ⟨p, hp, hpt⟩, by omega, ha, ?_⟩
       rw [← hs]
       exact decide_eq_true_iff)
    | cases h

private lemma rank_lt (R : Finset ℕ) {t u : ℕ} (ht : t ∈ R) (h : t < u) :
    (R.filter (· < t)).card < (R.filter (· < u)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨t, mem_filter.mpr ⟨ht, h⟩, fun h' => lt_irrefl _ (mem_filter.mp h').2⟩
  · intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩

private lemma col_mem {n d : ℕ} {S R : Finset ℕ} (hd : 1 ≤ d)
    (hdS : ∀ p : ℕ, p.Prime → p ∣ d → p ∈ S)
    (hR : R = (Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t)) {t : ℕ} (ht : 1 ≤ t) :
    col n d S R t ∈ colSet d S R := by
  unfold col colSet
  split_ifs with h1 h2
  · exact Finset.inl_mem_disjSum.mpr (Nat.find_spec h1).1
  · refine Finset.inr_mem_disjSum.mpr (Finset.inl_mem_disjSum.mpr ?_)
    rw [mem_range]
    have htR : t ∈ R := by
      rw [hR, mem_filter, mem_Icc]
      exact ⟨⟨ht, h2⟩, fun p hp hpt => h1 ⟨p, hp, hpt⟩⟩
    have hlt : (R.filter (· < t)).card < R.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨t, htR, fun h' => lt_irrefl _ (mem_filter.mp h').2⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt hlt))
  · refine Finset.inr_mem_disjSum.mpr (Finset.inr_mem_disjSum.mpr ?_)
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have hcop : Nat.Coprime d t :=
      Nat.coprime_of_dvd (fun k hk hkd hkt => h1 ⟨k, hdS k hk hkd, hkt⟩)
    rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
    exact hcop

private lemma case_mid {n d i : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hdn : Nat.Coprime d n)
    (R B : Finset ℕ) (hB : B ⊆ Icc 1 (n - 1))
    (h : ∀ t ∈ B, t ∈ R ∧ t ≤ n / d ∧ (R.filter (· < t)).card / d = i) :
    ∑ t ∈ B, t ≠ n := by
  intro hsum
  have hcard : B.card ≤ d := by
    have hle : B.card ≤ (Ico (i * d) (i * d + d)).card := by
      apply Finset.card_le_card_of_injOn (fun t => (R.filter (· < t)).card)
      · intro t ht
        obtain ⟨-, -, h3⟩ := h t ht
        have h6 : (R.filter (· < t)).card ∈ Ico (i * d) (i * d + d) := by
          rw [mem_Ico, ← h3]
          exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (by omega)⟩
        simpa using h6
      · intro t ht u hu htu
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · exact absurd htu (ne_of_lt (rank_lt R (h t ht).1 hlt))
        · exact absurd htu.symm (ne_of_lt (rank_lt R (h u hu).1 hlt))
    simpa using hle
  have hle : ∑ t ∈ B, t ≤ B.card * (n / d) := by
    simpa [smul_eq_mul] using
      Finset.sum_le_card_nsmul B (fun t => t) (n / d) (fun t ht => (h t ht).2.1)
  have h1 : d * (n / d) ≤ n := Nat.mul_div_le n d
  have h2 : B.card * (n / d) ≤ d * (n / d) := Nat.mul_le_mul_right _ hcard
  have h3 : d * (n / d) = n := by omega
  have hd1 : d = 1 := Nat.Coprime.eq_one_of_dvd hdn (Dvd.intro _ h3)
  subst hd1
  have hle' : ∑ t ∈ B, t ≤ B.card * (n - 1) := by
    simpa [smul_eq_mul] using
      Finset.sum_le_card_nsmul B (fun t => t) (n - 1) (fun t ht => (mem_Icc.mp (hB ht)).2)
  have h4 : B.card * (n - 1) ≤ 1 * (n - 1) := Nat.mul_le_mul_right _ hcard
  omega

private lemma case_big {n d a : ℕ} {s : Bool} (hn : 2 ≤ n) (hd : 1 ≤ d) (B : Finset ℕ)
    (hB : B ⊆ Icc 1 (n - 1))
    (h : ∀ t ∈ B, Nat.Coprime d t ∧ n / d < t ∧ t % d = a ∧
      (s = true ↔ ∃ j, j < d ∧ (j * t) % d = n % d ∧ j * t < n)) :
    ∑ t ∈ B, t ≠ n := by
  intro hsum
  have hne : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hsum
    omega
  have hlow : B.card * (n / d + 1) ≤ ∑ t ∈ B, t := by
    simpa [smul_eq_mul] using
      Finset.card_nsmul_le_sum B (fun t => t) (n / d + 1) (fun t ht => (h t ht).2.1)
  have hlt : B.card < d := by
    by_contra hge'
    have hge := not_lt.mp hge'
    have h1 : d * (n / d + 1) ≤ B.card * (n / d + 1) := Nat.mul_le_mul_right _ hge
    have h2 : n < d * (n / d + 1) := Nat.lt_mul_div_succ n (by omega)
    omega
  have hmod : ∀ t ∈ B, (B.card * t) % d = n % d := by
    intro t ht
    have e1 : n % d = (B.card * a) % d := by
      rw [← hsum, Finset.sum_nat_mod, Finset.sum_congr rfl (fun u hu => (h u hu).2.2.1)]
      simp [Finset.sum_const, smul_eq_mul]
    have e2 : t ≡ a [MOD d] := by
      unfold Nat.ModEq
      rw [← (h t ht).2.2.1, Nat.mod_mod]
    rw [e1]
    exact Nat.ModEq.mul_left _ e2
  have hsumj : ∑ t ∈ B, B.card * t = B.card * n := by rw [← Finset.mul_sum, hsum]
  cases s with
  | true =>
    have hall : ∀ t ∈ B, B.card * t < n := by
      intro t ht
      obtain ⟨hcop, -, -, hs⟩ := h t ht
      obtain ⟨j, hjd, hjmod, hjlt⟩ := hs.mp rfl
      have hj : j = B.card := by
        have hme : j * t ≡ B.card * t [MOD d] := by
          unfold Nat.ModEq
          rw [hjmod, hmod t ht]
        have hme' := Nat.ModEq.cancel_right_of_coprime hcop hme
        unfold Nat.ModEq at hme'
        rwa [Nat.mod_eq_of_lt hjd, Nat.mod_eq_of_lt hlt] at hme'
      rw [← hj]
      exact hjlt
    have hlt' : ∑ t ∈ B, B.card * t < ∑ _t ∈ B, n := Finset.sum_lt_sum_of_nonempty hne hall
    rw [hsumj, Finset.sum_const, smul_eq_mul] at hlt'
    exact lt_irrefl _ hlt'
  | false =>
    have hall : ∀ t ∈ B, n ≤ B.card * t := by
      intro t ht
      obtain ⟨-, -, -, hs⟩ := h t ht
      by_contra hlt'
      exact Bool.false_ne_true (hs.mpr ⟨B.card, hlt, hmod t ht, not_le.mp hlt'⟩)
    have heq : ∀ t ∈ B, B.card * t = n := by
      intro t ht
      by_contra hne'
      have hlt' : n < B.card * t := lt_of_le_of_ne (hall t ht) (Ne.symm hne')
      have hlt'' : ∑ _u ∈ B, n < ∑ u ∈ B, B.card * u := Finset.sum_lt_sum hall ⟨t, ht, hlt'⟩
      rw [hsumj, Finset.sum_const, smul_eq_mul] at hlt''
      exact lt_irrefl _ hlt''
    obtain ⟨t0, ht0⟩ := hne
    have ht0n : t0 ≤ n - 1 := (mem_Icc.mp (hB ht0)).2
    have hc2 : 1 < B.card := by
      by_contra hle'
      have hle := not_lt.mp hle'
      have h0 := heq t0 ht0
      have h1 : B.card * t0 ≤ 1 * t0 := Nat.mul_le_mul_right _ hle
      omega
    obtain ⟨t1, ht1, hne1⟩ := Finset.exists_mem_ne hc2 t0
    have h2 := (heq t1 ht1).trans (heq t0 ht0).symm
    exact hne1 (Nat.eq_of_mul_eq_mul_left (by omega) h2)

lemma f_le_coloring_bound {n d : ℕ} {S : Finset ℕ} (hn : 2 ≤ n) (hd : d.Prime) (hdn : ¬ d ∣ n)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ n) (hdS : d ∈ S) :
    let R' := (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t)
    Erdos360.f n ≤ S.card + 2 * d + (R'.card / d + 1) := by
  intro R'
  have hR : R' = (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t) := rfl
  have hd1 : 1 ≤ d := hd.one_le
  have hcop : Nat.Coprime d n := hd.coprime_iff_not_dvd.mpr hdn
  have hd_fac : ∀ p : ℕ, p.Prime → p ∣ d → p ∈ S := by
    intro p hp hpd
    have : p = d := (Nat.prime_dvd_prime_iff_eq hp hd).mp hpd
    exact this ▸ hdS
  have key : Erdos360.f n ≤ (colSet d S R').card := by
    apply f_le_of_coloring n (col n d S R')
    · intro t ht
      exact col_mem hd1 hd_fac hR (Finset.mem_Icc.mp ht).1
    · intro B hB hmono
      rcases B.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩
      · simp; omega
      · rcases hc0 : col n d S R' t0 with p | i | ⟨a, s⟩
        · have hall : ∀ t ∈ B, p ∣ t :=
            fun t ht => (col_inl ((hmono t ht t0 ht0).trans hc0)).2
          have hp := (col_inl hc0).1
          intro hsum
          exact (hS p hp).2 (hsum ▸ Finset.dvd_sum hall)
        · apply case_mid hn hd1 hcop R' B hB (i := i)
          intro t ht
          obtain ⟨h1, h2, h3⟩ := col_mid ((hmono t ht t0 ht0).trans hc0)
          refine ⟨?_, h2, h3⟩
          rw [hR, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨(Finset.mem_Icc.mp (hB ht)).1, h2⟩, h1⟩
        · apply case_big hn hd1 B hB (a := a) (s := s)
          intro t ht
          obtain ⟨h1, h2, h3, h4⟩ := col_big ((hmono t ht t0 ht0).trans hc0)
          exact ⟨Nat.coprime_of_dvd (fun k hk hkd hkt => h1 k (hd_fac k hk hkd) hkt), h2, h3, h4⟩
  rw [colSet_card] at key
  have htot : d.totient ≤ d := Nat.totient_le d
  omega

/- ### Part 2: Elementary prime counting and Mertens upper bounds -/

private lemma log_four_lt_two : Real.log 4 < 2 := by
  have h2 : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h4 : (4 : ℝ) < Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith
  calc Real.log 4 < Real.log (Real.exp 2) := Real.log_lt_log (by norm_num) h4
    _ = 2 := Real.log_exp 2

private lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have h3 : Real.exp 1 < (3 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) h3

private lemma sum_primes_log_le (m : ℕ) :
    ∑ p ∈ (Finset.Icc 1 m).filter Nat.Prime, Real.log (p : ℝ) ≤ Real.log 4 * (m : ℝ) := by
  have heq : (Finset.Icc 1 m).filter Nat.Prime = (Finset.Icc 0 m).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨⟨hp.one_le, h2⟩, hp⟩
  rw [heq]
  have hth := Chebyshev.theta_eq_sum_Icc (m : ℝ)
  rw [Nat.floor_natCast] at hth
  rw [← hth]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg m)

private lemma prime_card_le (y : ℕ) (hy : 2 ≤ y) :
    (((Finset.Icc 1 y).filter Nat.Prime).card : ℝ) ≤ 6 * (y : ℝ) / Real.log (y : ℝ) := by
  have hy_pos : (0 : ℝ) < y := by positivity
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  set s := Nat.sqrt y
  set P := (Finset.Icc 1 y).filter Nat.Prime
  set P_lo := P.filter (· ≤ s)
  set P_hi := P.filter (fun p => ¬ p ≤ s)
  have hsplit : P.card = P_lo.card + P_hi.card := (Finset.card_filter_add_card_filter_not _).symm
  have hlo : (P_lo.card : ℝ) ≤ 2 * (y : ℝ) / Real.log (y : ℝ) := by
    have hsub : P_lo ⊆ Finset.Icc 1 s := by
      intro p hp
      have hp1 := (Finset.mem_filter.mp hp).1
      have hp2 := (Finset.mem_filter.mp hp).2
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).1, hp2⟩
    have hcard : P_lo.card ≤ s := by
      calc P_lo.card ≤ (Finset.Icc 1 s).card := Finset.card_le_card hsub
        _ = s := by simp
    have hs_le : (s : ℝ) ≤ Real.sqrt (y : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg s) hy_pos.le, sq]
      exact_mod_cast Nat.sqrt_le y
    have hsq_pos : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr hy_pos
    have hlog_sq : Real.log (y : ℝ) ≤ 2 * Real.sqrt (y : ℝ) := by
      have h1 : Real.log (Real.sqrt (y : ℝ)) ≤ Real.sqrt (y : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hsq_pos
      rw [Real.log_sqrt hy_pos.le] at h1
      linarith
    have hmul : Real.sqrt (y : ℝ) * Real.log (y : ℝ) ≤ 2 * (y : ℝ) := by
      calc Real.sqrt (y : ℝ) * Real.log (y : ℝ)
          ≤ Real.sqrt (y : ℝ) * (2 * Real.sqrt (y : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_sq hsq_pos.le
        _ = 2 * (Real.sqrt (y : ℝ) * Real.sqrt (y : ℝ)) := by ring
        _ = 2 * (y : ℝ) := by rw [Real.mul_self_sqrt hy_pos.le]
    calc (P_lo.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hcard
      _ ≤ Real.sqrt (y : ℝ) := hs_le
      _ ≤ 2 * (y : ℝ) / Real.log (y : ℝ) := (le_div_iff₀ hlogy_pos).mpr hmul
  have hhi : (P_hi.card : ℝ) ≤ 4 * (y : ℝ) / Real.log (y : ℝ) := by
    have hlog_ge : ∀ p ∈ P_hi, (1 / 2 : ℝ) * Real.log (y : ℝ) ≤ Real.log (p : ℝ) := by
      intro p hp
      have hp_gt : s < p := not_le.mp (Finset.mem_filter.mp hp).2
      have hp_sq : y < p * p := by
        have h1 : y < (s + 1) * (s + 1) := Nat.lt_succ_sqrt y
        have h2 : (s + 1) * (s + 1) ≤ p * p := Nat.mul_le_mul hp_gt hp_gt
        omega
      have hp_real : Real.sqrt (y : ℝ) < (p : ℝ) := by
        have hp_pos : (0 : ℝ) < p := by
          exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos
        rw [Real.sqrt_lt' hp_pos, sq]
        have : (y : ℝ) < ((p * p : ℕ) : ℝ) := by exact_mod_cast hp_sq
        push_cast at this
        linarith
      have hlog_eq : (1 / 2 : ℝ) * Real.log (y : ℝ) = Real.log (Real.sqrt (y : ℝ)) := by
        rw [Real.log_sqrt hy_pos.le]; ring
      rw [hlog_eq]
      exact Real.log_le_log (Real.sqrt_pos.mpr hy_pos) hp_real.le
    have hsum1 : (P_hi.card : ℝ) * ((1 / 2 : ℝ) * Real.log (y : ℝ)) ≤
        ∑ p ∈ P_hi, Real.log (p : ℝ) := by
      calc (P_hi.card : ℝ) * ((1 / 2 : ℝ) * Real.log (y : ℝ))
          = ∑ _p ∈ P_hi, ((1 / 2 : ℝ) * Real.log (y : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ P_hi, Real.log (p : ℝ) := Finset.sum_le_sum hlog_ge
    have hsum2 : ∑ p ∈ P_hi, Real.log (p : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
    have hsum3 : ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log 4 * (y : ℝ) := sum_primes_log_le y
    have hsum4 : Real.log 4 * (y : ℝ) ≤ 2 * (y : ℝ) :=
      mul_le_mul_of_nonneg_right log_four_lt_two.le hy_pos.le
    rw [le_div_iff₀ hlogy_pos]
    linarith
  have hcast : (P.card : ℝ) = (P_lo.card : ℝ) + (P_hi.card : ℝ) := by exact_mod_cast hsplit
  have hsum : 2 * (y : ℝ) / Real.log (y : ℝ) + 4 * (y : ℝ) / Real.log (y : ℝ) =
      6 * (y : ℝ) / Real.log (y : ℝ) := by ring
  linarith

private lemma prod_coprime_dvd {S : Finset ℕ} {f : ℕ → ℕ} {N : ℕ}
    (hcop : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime (f a) (f b))
    (hdvd : ∀ a ∈ S, f a ∣ N) :
    ∏ a ∈ S, f a ∣ N := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx]
    have hx_dvd : f x ∣ N := hdvd x (Finset.mem_insert_self x s)
    have hs_dvd : ∏ a ∈ s, f a ∣ N :=
      ih (fun a ha b hb => hcop a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))
         (fun a ha => hdvd a (Finset.mem_insert_of_mem ha))
    have hcop_xs : Nat.Coprime (f x) (∏ a ∈ s, f a) :=
      Nat.Coprime.prod_right fun a ha =>
        hcop x (Finset.mem_insert_self x s) a (Finset.mem_insert_of_mem ha) (fun h => hx (h ▸ ha))
    exact hcop_xs.mul_dvd_of_dvd_of_dvd hx_dvd hs_dvd

private lemma prime_pow_div_dvd_factorial {L p : ℕ} (hp : p.Prime) :
    p ^ (L / p) ∣ L.factorial := by
  have hfac : L.factorial = ∏ k ∈ Finset.Icc 1 L, k := by
    induction L with
    | zero => simp
    | succ n ih =>
      rw [Nat.factorial_succ, ih]
      have hsub : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.prod_insert (by simp)]
  rw [hfac]
  set B := (Finset.Icc 1 (L / p)).image (· * p)
  have hsub : B ⊆ Finset.Icc 1 L := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.mul_pos hk1 hp.pos
    · exact (Nat.mul_le_mul_right p hk2).trans (Nat.div_mul_le_self L p)
  have hdvd1 : ∏ x ∈ B, x ∣ ∏ k ∈ Finset.Icc 1 L, k :=
    Finset.prod_dvd_prod_of_subset B (Finset.Icc 1 L) id hsub
  have hprodB : ∏ x ∈ B, x = (∏ k ∈ Finset.Icc 1 (L / p), k) * p ^ (L / p) := by
    rw [Finset.prod_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hp.pos h),
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  rw [hprodB] at hdvd1
  exact dvd_trans (dvd_mul_left _ _) hdvd1

private lemma mertens_log_sum_le (L : ℕ) (hL : 1 ≤ L) :
    ∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (L : ℝ) + Real.log 4 := by
  set P := (Finset.Icc 1 L).filter Nat.Prime
  have hLpos : (0 : ℝ) < L := by positivity
  have hdvd : ∏ p ∈ P, p ^ (L / p) ∣ L.factorial := by
    apply prod_coprime_dvd
    · intro p hp q hq hpq
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hqq : q.Prime := (Finset.mem_filter.mp hq).2
      exact ((Nat.coprime_primes hpp hqq).mpr hpq).pow _ _
    · intro p hp
      exact prime_pow_div_dvd_factorial (Finset.mem_filter.mp hp).2
  have hle_fac : ∏ p ∈ P, p ^ (L / p) ≤ L ^ L := by
    have h1 : ∏ p ∈ P, p ^ (L / p) ≤ L.factorial := Nat.le_of_dvd (Nat.factorial_pos L) hdvd
    have h2 : L.factorial ≤ L ^ L := Nat.factorial_le_pow L
    exact h1.trans h2
  have hlog_le : ∑ p ∈ P, ((L / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤ (L : ℝ) * Real.log (L : ℝ) := by
    have hpos_lhs : (0 : ℝ) < ((∏ p ∈ P, p ^ (L / p) : ℕ) : ℝ) := by
      have : 0 < ∏ p ∈ P, p ^ (L / p) := Finset.prod_pos fun p hp =>
        pow_pos (Finset.mem_filter.mp hp).2.pos _
      exact_mod_cast this
    have hlog1 : Real.log ((∏ p ∈ P, p ^ (L / p) : ℕ) : ℝ) ≤ Real.log ((L ^ L : ℕ) : ℝ) :=
      Real.log_le_log hpos_lhs (by exact_mod_cast hle_fac)
    have hlhs : Real.log ((∏ p ∈ P, p ^ (L / p) : ℕ) : ℝ) =
        ∑ p ∈ P, ((L / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.cast_pow, Real.log_pow]
      · intro p hp
        have : 0 < p ^ (L / p) := pow_pos (Finset.mem_filter.mp hp).2.pos _
        exact_mod_cast this.ne'
    have hrhs : Real.log ((L ^ L : ℕ) : ℝ) = (L : ℝ) * Real.log (L : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
    rwa [hlhs, hrhs] at hlog1
  have hterm : ∀ p ∈ P, (L : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ) ≤
      ((L / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
    have hdiv : (L : ℝ) / (p : ℝ) - 1 ≤ ((L / p : ℕ) : ℝ) := by
      have hnat : L < (L / p + 1) * p := by
        have := Nat.lt_div_mul_add (a := L) hp_prime.pos
        linarith
      have hreal : (L : ℝ) < (((L / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hnat
      rw [sub_le_iff_le_add, div_le_iff₀ hp_pos]
      linarith
    calc (L : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)
        = ((L : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) := by ring
      _ ≤ ((L / p : ℕ) : ℝ) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hdiv hlogp
  have hsum_sub : (L : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - ∑ p ∈ P, Real.log (p : ℝ) ≤
      (L : ℝ) * Real.log (L : ℝ) := by
    calc (L : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - ∑ p ∈ P, Real.log (p : ℝ)
        = ∑ p ∈ P, ((L : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)) := by
          rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ p ∈ P, ((L / p : ℕ) : ℝ) * Real.log (p : ℝ) := Finset.sum_le_sum hterm
      _ ≤ (L : ℝ) * Real.log (L : ℝ) := hlog_le
  have htheta : ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log 4 * (L : ℝ) := sum_primes_log_le L
  have hmul : (L : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤
      (L : ℝ) * (Real.log (L : ℝ) + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left hmul hLpos

private lemma abel_sum_Icc (A f : ℕ → ℝ) (L : ℕ) (hL : 3 ≤ L) :
    ∑ k ∈ Finset.Icc 3 L, (A k - A (k - 1)) * f k =
      A L * f L - A 2 * f 3 + ∑ k ∈ Finset.Icc 3 (L - 1), A k * (f k - f (k + 1)) := by
  induction L, hL using Nat.le_induction with
  | base => simp; ring
  | succ m hm ih =>
    have hIcc1 : Finset.Icc 3 (m + 1) = insert (m + 1) (Finset.Icc 3 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIcc2 : Finset.Icc 3 m = insert m (Finset.Icc 3 (m - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot1 : m + 1 ∉ Finset.Icc 3 m := by simp
    have hnot2 : m ∉ Finset.Icc 3 (m - 1) := by simp; omega
    rw [hIcc1, Finset.sum_insert hnot1, ih, Nat.add_sub_cancel, hIcc2, Finset.sum_insert hnot2]
    ring

private lemma tele_sum_Icc (F : ℕ → ℝ) (L : ℕ) (hL : 3 ≤ L) :
    ∑ k ∈ Finset.Icc 3 (L - 1), (F (k + 1) - F k) = F L - F 3 := by
  induction L, hL using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 3 m = insert m (Finset.Icc 3 (m - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m ∉ Finset.Icc 3 (m - 1) := by simp; omega
    rw [Nat.add_sub_cancel, hIcc, Finset.sum_insert hnot, ih]
    ring

private lemma sum_inv_primes_le (L : ℕ) (hL : 3 ≤ L) :
    ∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log (Real.log (L : ℝ)) + 6 := by
  let a : ℕ → ℝ := fun k => if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0
  let A : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 1 m, a k
  have hA_eq : ∀ m : ℕ, A m = ∑ p ∈ (Finset.Icc 1 m).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
    intro m
    dsimp only [A, a]
    rw [Finset.sum_filter]
  have hA_le : ∀ m : ℕ, 1 ≤ m → A m ≤ Real.log (m : ℝ) + Real.log 4 := fun m hm => by
    rw [hA_eq m]; exact mertens_log_sum_le m hm
  have hA_nonneg : ∀ m : ℕ, 0 ≤ A m := fun m => by
    rw [hA_eq m]
    refine Finset.sum_nonneg fun p hp => ?_
    have hpp := (Finset.mem_filter.mp hp).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p)
  have hdiff : ∀ k : ℕ, 3 ≤ k → A k - A (k - 1) = a k := by
    intro k hk
    dsimp only [A]
    have hIcc : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Icc 1 (k - 1) := by simp; omega
    rw [hIcc, Finset.sum_insert hnot]
    ring
  have hsplit : ∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
      (1 / 2 : ℝ) + ∑ k ∈ Finset.Icc 3 L, (A k - A (k - 1)) * ((Real.log (k : ℝ))⁻¹) := by
    rw [Finset.sum_filter]
    have hIcc : Finset.Icc 1 L = insert 1 (insert 2 (Finset.Icc 3 L)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have h1np : ¬ Nat.Prime 1 := Nat.not_prime_one
    have h2p : Nat.Prime 2 := Nat.prime_two
    simp only [h1np, ↓reduceIte, h2p, zero_add, Nat.cast_ofNat]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [hdiff k hk3]
    dsimp only [a]
    by_cases hkp : k.Prime
    · simp only [hkp, ↓reduceIte]
      have hlogk : Real.log (k : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < k by omega))).ne'
      field_simp [hlogk]
    · simp [hkp]
  rw [hsplit, abel_sum_Icc A (fun k => (Real.log (k : ℝ))⁻¹) L hL]
  have hlog3 : 1 < Real.log (3 : ℝ) := one_lt_log_three
  have hlogL : 1 < Real.log (L : ℝ) := lt_of_lt_of_le hlog3
    (Real.log_le_log (by norm_num) (by exact_mod_cast hL))
  have hA2_term : 0 ≤ A 2 * (Real.log (3 : ℝ))⁻¹ :=
    mul_nonneg (hA_nonneg 2) (inv_nonneg.mpr (by linarith))
  have hfirst : A L * (Real.log (L : ℝ))⁻¹ ≤ 1 + Real.log 4 := by
    calc A L * (Real.log (L : ℝ))⁻¹
        ≤ (Real.log (L : ℝ) + Real.log 4) * (Real.log (L : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right (hA_le L (by omega)) (inv_nonneg.mpr (by linarith))
      _ = 1 + Real.log 4 * (Real.log (L : ℝ))⁻¹ := by
          rw [add_mul, mul_inv_cancel₀ (by linarith)]
      _ ≤ 1 + Real.log 4 * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hlogL.le)
            (Real.log_nonneg (by norm_num)))
      _ = 1 + Real.log 4 := by ring
  have hstep : ∀ k ∈ Finset.Icc 3 (L - 1),
      A k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
        (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
          Real.log 4 * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) := by
    intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    have hlogk : 1 < Real.log (k : ℝ) := lt_of_lt_of_le hlog3
      (Real.log_le_log (by norm_num) (by exact_mod_cast hk3))
    have hlogk1 : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show k ≤ k + 1 by omega))
    have hinv_diff : 0 ≤ (Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ :=
      sub_nonneg.mpr (inv_anti₀ (by linarith) hlogk1)
    have h1 : A k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
        (Real.log (k : ℝ) + Real.log 4) * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_right (hA_le k (by omega)) hinv_diff
    have h2 : Real.log (k : ℝ) * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
        Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
      have hu : 0 < Real.log (k : ℝ) := by linarith
      have hv : 0 < Real.log ((k + 1 : ℕ) : ℝ) := by linarith
      have hlog_ineq : Real.log (Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ)) ≤
          Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hu hv)
      rw [Real.log_div hu.ne' hv.ne'] at hlog_ineq
      have hmul_eq : Real.log (k : ℝ) * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) =
          1 - Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) := by
        rw [mul_sub, mul_inv_cancel₀ hu.ne', div_eq_mul_inv]
      linarith
    linarith [add_mul (Real.log (k : ℝ)) (Real.log 4)
      ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹)]
  have htele : ∀ (F : ℕ → ℝ),
      ∑ k ∈ Finset.Icc 3 (L - 1), (F (k + 1) - F k) = F L - F 3 := fun F => tele_sum_Icc F L hL
  have hsum_le : ∑ k ∈ Finset.Icc 3 (L - 1),
      A k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
      Real.log (Real.log (L : ℝ)) + Real.log 4 := by
    calc ∑ k ∈ Finset.Icc 3 (L - 1),
          A k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹)
        ≤ ∑ k ∈ Finset.Icc 3 (L - 1),
          ((Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
            Real.log 4 * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹)) :=
          Finset.sum_le_sum hstep
      _ = (∑ k ∈ Finset.Icc 3 (L - 1),
            (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)))) +
          Real.log 4 * (∑ k ∈ Finset.Icc 3 (L - 1),
            ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (Real.log (Real.log (L : ℝ)) - Real.log (Real.log (3 : ℝ))) +
          Real.log 4 * ((Real.log (3 : ℝ))⁻¹ - (Real.log (L : ℝ))⁻¹) := by
          rw [htele (fun k => Real.log (Real.log (k : ℝ)))]
          have htele2 := htele (fun k => -(Real.log (k : ℝ))⁻¹)
          have hsub_eq : ∑ k ∈ Finset.Icc 3 (L - 1),
              ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) =
              (Real.log (3 : ℝ))⁻¹ - (Real.log (L : ℝ))⁻¹ := by
            have hsum_eq : ∑ k ∈ Finset.Icc 3 (L - 1),
                ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) =
                ∑ k ∈ Finset.Icc 3 (L - 1),
                  (-(Real.log ((k + 1 : ℕ) : ℝ))⁻¹ - -(Real.log (k : ℝ))⁻¹) :=
              Finset.sum_congr rfl fun k _ => by ring
            rw [hsum_eq, htele2]
            push_cast
            ring
          rw [hsub_eq]
          push_cast
          rfl
      _ ≤ Real.log (Real.log (L : ℝ)) + Real.log 4 := by
          have hll3 : 0 ≤ Real.log (Real.log (3 : ℝ)) := Real.log_nonneg hlog3.le
          have hinv3 : (Real.log (3 : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog3.le
          have hinvL : 0 ≤ (Real.log (L : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
          have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          nlinarith
  have hlog4_lt : Real.log 4 < 2 := log_four_lt_two
  linarith

private lemma sum_inv_mul_pred_le (L : ℕ) :
    ∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : (Finset.Icc 1 L).filter Nat.Prime ⊆ Finset.Icc 2 L := by
    intro p hp
    have ⟨hI, hP⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hP.two_le, (Finset.mem_Icc.mp hI).2⟩
  have h1 : ∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ k ∈ Finset.Icc 2 L, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k hk _
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
  refine h1.trans ?_
  have htele : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.Icc 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / (m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ r hr ih =>
      have hIcc : Finset.Icc 2 (r + 1) = insert (r + 1) (Finset.Icc 2 r) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      push_cast
      have hr0 : (r : ℝ) ≠ 0 := by positivity
      have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
      have hrsub : ((r : ℝ) + 1) - 1 = (r : ℝ) := by ring
      rw [hrsub]
      field_simp
      ring
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · simp
  · rw [htele L hLpos]
    have : 0 ≤ 1 / (L : ℝ) := by positivity
    linarith

private lemma prod_one_sub_inv_primesLE (L : ℕ) (hL : 3 ≤ L) :
    ∏ p ∈ (Finset.Icc 1 L).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp 7 * Real.log (L : ℝ) := by
  set P := (Finset.Icc 1 L).filter Nat.Prime
  have hfactor : ∀ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have heq : (1 - 1 / (p : ℝ))⁻¹ = 1 + (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [heq, add_comm 1]
    exact Real.add_one_le_exp _
  calc ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹
      ≤ ∏ p ∈ P, Real.exp (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
          have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          exact inv_nonneg.mpr (by linarith)
        · exact hfactor
    _ = Real.exp (∑ p ∈ P, (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) :=
        (Real.exp_sum P _).symm
    _ ≤ Real.exp (Real.log (Real.log (L : ℝ)) + 7) := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_add_distrib]
        linarith [sum_inv_primes_le L hL, sum_inv_mul_pred_le L]
    _ = Real.exp 7 * Real.log (L : ℝ) := by
        rw [Real.exp_add, mul_comm, Real.exp_log]
        exact lt_trans zero_lt_one (lt_of_lt_of_le one_lt_log_three
          (Real.log_le_log (by norm_num) (by exact_mod_cast hL)))

private lemma prod_one_sub_inv_primeFactors (n : ℕ) (hn : 25 ≤ n) :
    ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp 9 * Real.log (Real.log (n : ℝ)) := by
  have hn_pos : 0 < n := by omega
  have hlog3 : (3 : ℝ) ≤ Real.log (n : ℝ) := by
    have he3 : Real.exp 3 < (25 : ℝ) := by
      have h1 : Real.exp 1 < 2.8 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hsq : Real.exp 1 * Real.exp 1 < 7.84 := by nlinarith only [h1, Real.exp_pos 1]
      have h3 : Real.exp 3 = (Real.exp 1 * Real.exp 1) * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      rw [h3]
      nlinarith only [hsq, h1, Real.exp_pos 1]
    have hlt : Real.exp 3 < (n : ℝ) := lt_of_lt_of_le he3 (by exact_mod_cast hn)
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 3) hlt.le
  set L := ⌊Real.log (n : ℝ)⌋₊
  have hL3 : 3 ≤ L := Nat.le_floor (by push_cast; exact hlog3)
  have hL_le : (L : ℝ) ≤ Real.log (n : ℝ) := Nat.floor_le (by linarith)
  have hlog_lt : Real.log (n : ℝ) < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  set P_lo := n.primeFactors.filter (· ≤ L)
  set P_hi := n.primeFactors.filter (fun p => ¬ p ≤ L)
  have hsplit : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ P_lo, (1 - 1 / (p : ℝ))⁻¹) * (∏ p ∈ P_hi, (1 - 1 / (p : ℝ))⁻¹) :=
    (Finset.prod_filter_mul_prod_filter_not n.primeFactors (· ≤ L) _).symm
  rw [hsplit]
  have hlo : ∏ p ∈ P_lo, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp 7 * Real.log (Real.log (n : ℝ)) := by
    have hsub : P_lo ⊆ (Finset.Icc 1 L).filter Nat.Prime := by
      intro p hp
      have hp1 := (Finset.mem_filter.mp hp).1
      have hp2 := (Finset.mem_filter.mp hp).2
      have hpp := Nat.prime_of_mem_primeFactors hp1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.one_le, hp2⟩, hpp⟩
    have h1 : ∏ p ∈ P_lo, (1 - 1 / (p : ℝ))⁻¹ ≤
        ∏ p ∈ (Finset.Icc 1 L).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹ := by
      have hfactor_ge1 : ∀ p ∈ (Finset.Icc 1 L).filter Nat.Prime, 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := by
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        have hpos : 0 < 1 - 1 / (p : ℝ) := by
          have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          linarith
        exact (one_le_inv₀ hpos).mpr (by linarith [div_pos zero_lt_one (show (0 : ℝ) < p by linarith)])
      rw [← Finset.prod_sdiff hsub]
      have hge1 : 1 ≤ ∏ p ∈ ((Finset.Icc 1 L).filter Nat.Prime) \ P_lo, (1 - 1 / (p : ℝ))⁻¹ :=
        Finset.one_le_prod fun p hp => hfactor_ge1 p (Finset.mem_sdiff.mp hp).1
      have hnn : 0 ≤ ∏ p ∈ P_lo, (1 - 1 / (p : ℝ))⁻¹ :=
        Finset.prod_nonneg fun p hp => (zero_le_one.trans (hfactor_ge1 p (hsub hp)))
      nlinarith only [hge1, hnn]
    have h2 := prod_one_sub_inv_primesLE L hL3
    have h3 : Real.log (L : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log (by positivity) hL_le
    exact (h1.trans h2).trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos 7).le)
  have hhi : ∏ p ∈ P_hi, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp 2 := by
    have hpow_le : (L + 1) ^ P_hi.card ≤ n := by
      have hdvd : ∏ p ∈ P_hi, p ∣ n := by
        apply prod_coprime_dvd
        · intro p hp q hq hpq
          exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).mpr hpq
        · intro p hp
          exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      calc (L + 1) ^ P_hi.card = ∏ _p ∈ P_hi, (L + 1) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ P_hi, p := Finset.prod_le_prod' fun p hp => not_le.mp (Finset.mem_filter.mp hp).2
        _ ≤ n := Nat.le_of_dvd hn_pos hdvd
    have hcard_le : (P_hi.card : ℝ) ≤ (L : ℝ) + 1 := by
      have hlogL1 : (1 : ℝ) < Real.log ((L + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ L + 1 by omega)))
      have hlog_pow : (P_hi.card : ℝ) * Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
        have h1 : Real.log (((L + 1) ^ P_hi.card : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hpow_le)
        rwa [Nat.cast_pow, Real.log_pow] at h1
      nlinarith
    have hterm : ∀ p ∈ P_hi, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp (1 / (L : ℝ)) := by
      intro p hp
      have hpL : L + 1 ≤ p := not_le.mp (Finset.mem_filter.mp hp).2
      have hp_real : (L : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpL
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have heq : (1 - 1 / (p : ℝ))⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
      have hle1 : 1 / ((p : ℝ) - 1) ≤ 1 / (L : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      rw [heq]
      exact (by linarith : 1 + 1 / ((p : ℝ) - 1) ≤ 1 / (L : ℝ) + 1).trans (Real.add_one_le_exp _)
    calc ∏ p ∈ P_hi, (1 - 1 / (p : ℝ))⁻¹
        ≤ ∏ _p ∈ P_hi, Real.exp (1 / (L : ℝ)) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp2 : (2 : ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
            exact inv_nonneg.mpr (by linarith)
          · exact hterm
      _ = Real.exp ((P_hi.card : ℝ) / (L : ℝ)) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul, mul_one_div]
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          rw [div_le_iff₀ (by positivity)]
          have hL3r : (3 : ℝ) ≤ L := by exact_mod_cast hL3
          linarith
  have hlo_nonneg : 0 ≤ ∏ p ∈ P_lo, (1 - 1 / (p : ℝ))⁻¹ :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
      have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      exact inv_nonneg.mpr (by linarith)
  have hhi_nonneg : 0 ≤ ∏ p ∈ P_hi, (1 - 1 / (p : ℝ))⁻¹ :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
      have hlt : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      exact inv_nonneg.mpr (by linarith)
  calc (∏ p ∈ P_lo, (1 - 1 / (p : ℝ))⁻¹) * (∏ p ∈ P_hi, (1 - 1 / (p : ℝ))⁻¹)
      ≤ (Real.exp 7 * Real.log (Real.log (n : ℝ))) * Real.exp 2 :=
        mul_le_mul hlo hhi hhi_nonneg (mul_nonneg (Real.exp_pos 7).le
          (Real.log_nonneg (by linarith)))
    _ = Real.exp 9 * Real.log (Real.log (n : ℝ)) := by
        have : Real.exp 7 * Real.exp 2 = Real.exp 9 := by rw [← Real.exp_add]; norm_num
        rw [← this]
        ring

/- ### Part 3: Unified Euler product bound and Rankin's trick -/

private lemma prod_primeFactors_eq_of_subset {u : ℕ} {P : Finset ℕ}
    (hu : u ≠ 0) (hsub : u.primeFactors ⊆ P) :
    ∏ p ∈ P, p ^ (u.factorization p) = u := by
  rw [← Finset.prod_subset hsub]
  · exact Nat.prod_factorization_pow_eq_self hu
  · intro p _ hp
    have h0 : u.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hp
    simp [h0]

private lemma euler_product_le (P : Finset ℕ) (M : ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ p ∈ P, 0 ≤ f p) (hf1 : ∀ p ∈ P, f p < 1) :
    let U := (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ P)
    ∑ u ∈ U, ∏ p ∈ P, (f p) ^ (u.factorization p) ≤ ∏ p ∈ P, (1 - f p)⁻¹ := by
  classical
  intro U
  have hexp_lt : ∀ u ∈ U, ∀ p : P, u.factorization p.1 < M + 1 := by
    intro u hu p
    have ⟨hu1, huM⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1
    by_cases hp : p.1 ∈ u.primeFactors
    · have hprime : p.1.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : p.1 ^ (u.factorization p.1) ∣ u := Nat.ordProj_dvd u p.1
      have hle : p.1 ^ (u.factorization p.1) ≤ u := Nat.le_of_dvd (by omega) hdvd
      have h2 : 2 ^ (u.factorization p.1) ≤ p.1 ^ (u.factorization p.1) :=
        Nat.pow_le_pow_left hprime.two_le _
      have hlt := Nat.lt_two_pow_self (n := u.factorization p.1)
      omega
    · have h0 : u.factorization p.1 = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp
      omega
  let Φ : { u : ℕ // u ∈ U } → (P → Fin (M + 1)) := fun u p =>
    ⟨u.1.factorization p.1, hexp_lt u.1 u.2 p⟩
  have hΦ_inj : Function.Injective Φ := by
    intro u₁ u₂ h
    apply Subtype.ext
    have hu1 : u₁.1 ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp u₁.2).1).1; omega
    have hu2 : u₂.1 ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp u₂.2).1).1; omega
    rw [← prod_primeFactors_eq_of_subset hu1 (Finset.mem_filter.mp u₁.2).2,
        ← prod_primeFactors_eq_of_subset hu2 (Finset.mem_filter.mp u₂.2).2]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hval := congrArg (fun g : P → Fin (M + 1) => (g ⟨p, hp⟩).1) h
    dsimp only [Φ] at hval
    rw [hval]
  have hsum_le : ∑ u ∈ U, ∏ p ∈ P, (f p) ^ (u.factorization p) ≤
      ∑ g : P → Fin (M + 1), ∏ p : P, (f p.1) ^ (g p).1 := by
    have h1 : ∑ u ∈ U, ∏ p ∈ P, (f p) ^ (u.factorization p) =
        ∑ u : { u : ℕ // u ∈ U }, ∏ p : P, (f p.1) ^ (Φ u p).1 := by
      rw [← Finset.sum_attach U]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.prod_attach P]
      rfl
    rw [h1]
    calc ∑ u : { u : ℕ // u ∈ U }, ∏ p : P, (f p.1) ^ (Φ u p).1
        = ∑ g ∈ (Finset.univ : Finset { u : ℕ // u ∈ U }).image Φ, ∏ p : P, (f p.1) ^ (g p).1 := by
          rw [Finset.sum_image (fun a _ b _ hab => hΦ_inj hab)]
      _ ≤ ∑ g : P → Fin (M + 1), ∏ p : P, (f p.1) ^ (g p).1 :=
          Finset.sum_le_univ_sum_of_nonneg fun g =>
            Finset.prod_nonneg fun p _ => pow_nonneg (hf0 p.1 p.2) _
  have hprod_sum : ∑ g : P → Fin (M + 1), ∏ p : P, (f p.1) ^ (g p).1 =
      ∏ p : P, ∑ e : Fin (M + 1), (f p.1) ^ e.1 :=
    (Fintype.prod_sum (fun (p : P) (e : Fin (M + 1)) => (f p.1) ^ e.1)).symm
  calc ∑ u ∈ U, ∏ p ∈ P, (f p) ^ (u.factorization p)
      ≤ ∏ p : P, ∑ e : Fin (M + 1), (f p.1) ^ e.1 := hprod_sum ▸ hsum_le
    _ = ∏ p ∈ P, ∑ e ∈ Finset.range (M + 1), (f p) ^ e := by
        rw [← Finset.prod_attach P]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Fin.sum_univ_eq_sum_range]
    _ ≤ ∏ p ∈ P, (1 - f p)⁻¹ := by
        apply Finset.prod_le_prod
        · intro p hp
          exact Finset.sum_nonneg fun e _ => pow_nonneg (hf0 p hp) e
        · intro p hp
          have hne : f p ≠ 1 := (hf1 p hp).ne
          rw [geom_sum_eq hne]
          have hpos : 0 < 1 - f p := by linarith [hf1 p hp]
          have hpow : 0 ≤ (f p) ^ (M + 1) := pow_nonneg (hf0 p hp) _
          have hrew : ((f p) ^ (M + 1) - 1) / (f p - 1) = (1 - (f p) ^ (M + 1)) / (1 - f p) := by
            have : f p - 1 ≠ 0 := by linarith [hf1 p hp]
            field_simp
            ring
          rw [hrew, inv_eq_one_div]
          exact div_le_div_of_nonneg_right (by linarith) hpos.le

private lemma smooth_inv_sum_le (n M : ℕ) (hn : 25 ≤ n) :
    let U := (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ n.primeFactors)
    ∑ u ∈ U, (1 : ℝ) / (u : ℝ) ≤ Real.exp 9 * Real.log (Real.log (n : ℝ)) := by
  intro U
  have h1 : ∑ u ∈ U, (1 : ℝ) / (u : ℝ) =
      ∑ u ∈ U, ∏ p ∈ n.primeFactors, ((1 : ℝ) / (p : ℝ)) ^ (u.factorization p) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1; omega
    have hsub := (Finset.mem_filter.mp hu).2
    have hprod : ∏ p ∈ n.primeFactors, ((1 : ℝ) / (p : ℝ)) ^ (u.factorization p) =
        (1 : ℝ) / ((∏ p ∈ n.primeFactors, p ^ (u.factorization p) : ℕ) : ℝ) := by
      simp_rw [one_div, inv_pow, Finset.prod_inv_distrib]
      rw [Nat.cast_prod]
      congr 1
      refine Finset.prod_congr rfl fun p _ => by rw [Nat.cast_pow]
    rw [hprod, prod_primeFactors_eq_of_subset hu0 hsub]
  rw [h1]
  have hf0 : ∀ p ∈ n.primeFactors, 0 ≤ (1 : ℝ) / (p : ℝ) := fun p _ => by positivity
  have hf1 : ∀ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) < 1 := fun p hp => by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact (div_lt_one (by linarith)).mpr (by linarith)
  exact (euler_product_le n.primeFactors M (fun p => (1 : ℝ) / (p : ℝ)) hf0 hf1).trans
    (prod_one_sub_inv_primeFactors n hn)

private lemma exp_quarter_lt : Real.exp (1 / 4 : ℝ) < 4 / 3 := by
  have hpos : 0 < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
  have h4 : (Real.exp (1 / 4 : ℝ)) ^ (4 : ℕ) < (4 / 3 : ℝ) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    have h1 : (4 : ℕ) * (1 / 4 : ℝ) = 1 := by norm_num
    rw [h1]
    calc Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      _ < (4 / 3 : ℝ) ^ (4 : ℕ) := by norm_num
  by_contra h
  push Not at h
  have := pow_le_pow_left₀ (by norm_num) h 4
  linarith

private lemma two_rpow_neg_three_quarters_lt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 3 / 4 := by
  have h4 : ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ (4 : ℕ) < (3 / 4 : ℝ) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have h1 : -(3 / 4 : ℝ) * (4 : ℕ) = -3 := by norm_num
    rw [h1]
    have h2 : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2]
    norm_num
  by_contra h
  push Not at h
  have := pow_le_pow_left₀ (by norm_num) h 4
  linarith

private lemma smooth_card_rankin (n M : ℕ) (hM : 1 ≤ M)
    (hL : 4 ≤ Real.log (n : ℝ)) (hLL : 2 ≤ Real.log (Real.log (n : ℝ))) :
    let U := (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ n.primeFactors)
    let δ := 1 / (8 * Real.log (Real.log (n : ℝ)))
    (U.card : ℝ) ≤ (M : ℝ) * Real.exp (-δ * Real.log (M : ℝ)) *
      (32 * Real.exp 20 * (Real.log (Real.log (n : ℝ))) ^ 3) := by
  intro U δ
  set L := Real.log (n : ℝ)
  set LL := Real.log L
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  have hδ_le : δ ≤ 1 / 4 := by
    dsimp only [δ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set α := 1 - δ
  have hα_ge : (3 / 4 : ℝ) ≤ α := by dsimp only [α]; linarith
  have hα_pos : 0 < α := by linarith
  have hM_pos : (0 : ℝ) < M := by positivity
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    dsimp only [L] at hL
    rw [hn0] at hL
    simp at hL
    linarith
  have hcard_le : (U.card : ℝ) ≤
      (M : ℝ) ^ α * ∑ u ∈ U, (u : ℝ) ^ (-α) := by
    rw [Finset.mul_sum]
    calc (U.card : ℝ) = ∑ _u ∈ U, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ u ∈ U, (M : ℝ) ^ α * (u : ℝ) ^ (-α) := by
          refine Finset.sum_le_sum fun u hu => ?_
          have ⟨hu1, huM⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1
          have hu_pos : (0 : ℝ) < u := by positivity
          have hle : (u : ℝ) ^ α ≤ (M : ℝ) ^ α :=
            Real.rpow_le_rpow hu_pos.le (by exact_mod_cast huM) hα_pos.le
          have hmul : (u : ℝ) ^ α * (u : ℝ) ^ (-α) = 1 := by
            rw [← Real.rpow_add hu_pos, add_neg_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (u : ℝ) ^ α * (u : ℝ) ^ (-α) := hmul.symm
            _ ≤ (M : ℝ) ^ α * (u : ℝ) ^ (-α) :=
              mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hu_pos.le _)
  have hsum_rpow : ∑ u ∈ U, (u : ℝ) ^ (-α) ≤
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-α))⁻¹ := by
    have heq : ∑ u ∈ U, (u : ℝ) ^ (-α) =
        ∑ u ∈ U, ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (-α)) ^ (u.factorization p) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      have hu0 : u ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1; omega
      have hsub := (Finset.mem_filter.mp hu).2
      have hprod : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (-α)) ^ (u.factorization p) =
          ((∏ p ∈ n.primeFactors, p ^ (u.factorization p) : ℕ) : ℝ) ^ (-α) := by
        rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp_pos : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp_pos,
          ← Real.rpow_natCast ((p : ℝ) ^ (-α)), ← Real.rpow_mul hp_pos, mul_comm]
      rw [hprod, prod_primeFactors_eq_of_subset hu0 hsub]
    rw [heq]
    apply euler_product_le
    · intro p _; exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      calc (p : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-α) := by
            rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
            exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
              (Real.rpow_le_rpow (by norm_num) hp2 hα_pos.le)
        _ < (2 : ℝ) ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        _ = 1 := Real.rpow_zero 2
  set L₂ := ⌊L ^ 2⌋₊
  have hL₂_ge : 16 ≤ L₂ := Nat.le_floor (by push_cast; nlinarith)
  have hL₂_le : (L₂ : ℝ) ≤ L ^ 2 := Nat.floor_le (by positivity)
  have hL₂_gt : L ^ 2 < (L₂ : ℝ) + 1 := Nat.lt_floor_add_one _
  set P_lo := n.primeFactors.filter (· ≤ L₂)
  set P_hi := n.primeFactors.filter (fun p => ¬ p ≤ L₂)
  have hprod_split : ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-α))⁻¹ =
      (∏ p ∈ P_lo, (1 - (p : ℝ) ^ (-α))⁻¹) * (∏ p ∈ P_hi, (1 - (p : ℝ) ^ (-α))⁻¹) :=
    (Finset.prod_filter_mul_prod_filter_not n.primeFactors (· ≤ L₂) _).symm
  have hfac_pos : ∀ p ∈ n.primeFactors, 0 < 1 - (p : ℝ) ^ (-α) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hlt : (p : ℝ) ^ (-α) < 1 := by
      calc (p : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-α) := by
            rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
            exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
              (Real.rpow_le_rpow (by norm_num) hp2 hα_pos.le)
        _ < 1 := by
            calc (2 : ℝ) ^ (-α) < (2 : ℝ) ^ (0 : ℝ) :=
                  Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
              _ = 1 := Real.rpow_zero 2
    linarith
  have hlo : ∏ p ∈ P_lo, (1 - (p : ℝ) ^ (-α))⁻¹ ≤ 32 * Real.exp 18 * LL ^ 3 := by
    set P_lo3 := P_lo.filter (· ≠ 2)
    have hsplit2 : ∏ p ∈ P_lo, (1 - (p : ℝ) ^ (-α))⁻¹ ≤
        4 * ∏ p ∈ P_lo3, (1 - (p : ℝ) ^ (-α))⁻¹ := by
      by_cases h2 : 2 ∈ P_lo
      · have herase : P_lo3 = P_lo.erase 2 := by
          ext p; simp [P_lo3, Finset.mem_erase, and_comm]
        rw [herase, ← Finset.mul_prod_erase P_lo _ h2]
        have h2_bound : (1 - (2 : ℝ) ^ (-α))⁻¹ ≤ 4 := by
          have h2a : (2 : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have h2b : (2 : ℝ) ^ (-α) < 3 / 4 := lt_of_le_of_lt h2a two_rpow_neg_three_quarters_lt
          rw [inv_le_iff_one_le_mul₀ (by linarith)]
          linarith
        exact mul_le_mul_of_nonneg_right h2_bound
          (Finset.prod_nonneg fun p hp =>
            inv_nonneg.mpr (hfac_pos p (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).1).le)
      · have heq : P_lo3 = P_lo := by
          ext p
          simp only [P_lo3, Finset.mem_filter, and_iff_left_iff_imp]
          intro hp h2p; exact h2 (h2p ▸ hp)
        rw [heq]
        have hnn : 0 ≤ ∏ p ∈ P_lo, (1 - (p : ℝ) ^ (-α))⁻¹ :=
          Finset.prod_nonneg fun p hp => inv_nonneg.mpr (hfac_pos p (Finset.mem_filter.mp hp).1).le
        linarith
    have hlo3 : ∏ p ∈ P_lo3, (1 - (p : ℝ) ^ (-α))⁻¹ ≤ 8 * Real.exp 18 * LL ^ 3 := by
      have hterm : ∀ p ∈ P_lo3, (1 - (p : ℝ) ^ (-α))⁻¹ ≤ Real.exp (3 / (p : ℝ)) := by
        intro p hp
        have hp_lo := (Finset.mem_filter.mp hp).1
        have hp_ne2 := (Finset.mem_filter.mp hp).2
        have hp_pf := (Finset.mem_filter.mp hp_lo).1
        have hp_le := (Finset.mem_filter.mp hp_lo).2
        have hp_prime := Nat.prime_of_mem_primeFactors hp_pf
        have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
        have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        have hp_pos : (0 : ℝ) < p := by linarith
        have hpδ : (p : ℝ) ^ δ < 4 / 3 := by
          have hlogp : Real.log (p : ℝ) ≤ 2 * LL := by
            calc Real.log (p : ℝ) ≤ Real.log (L ^ 2) :=
                  Real.log_le_log hp_pos ((by exact_mod_cast hp_le : (p : ℝ) ≤ L₂).trans hL₂_le)
              _ = 2 * LL := by rw [Real.log_pow]; push_cast; rfl
          have hprod_le : δ * Real.log (p : ℝ) ≤ 1 / 4 := by
            dsimp only [δ]
            calc 1 / (8 * LL) * Real.log (p : ℝ) ≤ 1 / (8 * LL) * (2 * LL) :=
                  mul_le_mul_of_nonneg_left hlogp (by positivity)
              _ = 1 / 4 := by field_simp; ring
          rw [Real.rpow_def_of_pos hp_pos, mul_comm (Real.log (p : ℝ))]
          exact (Real.exp_le_exp.mpr hprod_le).trans_lt exp_quarter_lt
        have hpα : (p : ℝ) ^ (-α) ≤ (4 / 3 : ℝ) / (p : ℝ) := by
          have heq : (p : ℝ) ^ (-α) = (p : ℝ) ^ δ / (p : ℝ) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hp_pos]
            congr 1; dsimp only [α]; ring
          rw [heq]
          exact div_le_div_of_nonneg_right hpδ.le hp_pos.le
        have hpα_lt : (p : ℝ) ^ (-α) ≤ 4 / 9 := by
          calc (p : ℝ) ^ (-α) ≤ (4 / 3 : ℝ) / (p : ℝ) := hpα
            _ ≤ (4 / 3 : ℝ) / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3r
            _ = 4 / 9 := by norm_num
        have hinv_le : (1 - (p : ℝ) ^ (-α))⁻¹ ≤ 1 + 3 / (p : ℝ) := by
          rw [inv_le_iff_one_le_mul₀ (by linarith)]
          have h3p : (p : ℝ) ^ (-α) * (p : ℝ) ≤ 4 / 3 := (le_div_iff₀ hp_pos).mp hpα
          have hmul : (1 + 3 / (p : ℝ)) * (1 - (p : ℝ) ^ (-α)) =
              1 + (3 - (p : ℝ) ^ (-α) * (p : ℝ) - 3 * (p : ℝ) ^ (-α)) / (p : ℝ) := by
            field_simp; ring
          rw [hmul]
          have hnum : 0 ≤ 3 - (p : ℝ) ^ (-α) * (p : ℝ) - 3 * (p : ℝ) ^ (-α) := by linarith
          linarith [div_nonneg hnum hp_pos.le]
        exact hinv_le.trans (by rw [add_comm]; exact Real.add_one_le_exp _)
      have hsub : P_lo3 ⊆ (Finset.Icc 1 L₂).filter Nat.Prime := by
        intro p hp
        have hp_lo := (Finset.mem_filter.mp hp).1
        have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp_lo).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_le, (Finset.mem_filter.mp hp_lo).2⟩,
          hp_prime⟩
      have hsum_le : ∑ p ∈ P_lo3, (3 : ℝ) / (p : ℝ) ≤ 3 * (Real.log (Real.log (L₂ : ℝ)) + 6) := by
        have h1 : ∑ p ∈ P_lo3, (3 : ℝ) / (p : ℝ) ≤
            ∑ p ∈ (Finset.Icc 1 L₂).filter Nat.Prime, (3 : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        have h2 : ∑ p ∈ (Finset.Icc 1 L₂).filter Nat.Prime, (3 : ℝ) / (p : ℝ) =
            3 * ∑ p ∈ (Finset.Icc 1 L₂).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (sum_inv_primes_le L₂ (by omega)) (by norm_num))
      have hlogL2 : Real.log (L₂ : ℝ) ≤ 2 * LL := by
        calc Real.log (L₂ : ℝ) ≤ Real.log (L ^ 2) := Real.log_le_log (by positivity) hL₂_le
          _ = 2 * LL := by rw [Real.log_pow]; push_cast; rfl
      have hlogL2_pos : 0 < Real.log (L₂ : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < L₂ by omega))
      calc ∏ p ∈ P_lo3, (1 - (p : ℝ) ^ (-α))⁻¹
          ≤ ∏ p ∈ P_lo3, Real.exp (3 / (p : ℝ)) :=
            Finset.prod_le_prod (fun p hp =>
              inv_nonneg.mpr (hfac_pos p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).le)
              hterm
        _ = Real.exp (∑ p ∈ P_lo3, (3 : ℝ) / (p : ℝ)) := (Real.exp_sum P_lo3 _).symm
        _ ≤ Real.exp (3 * (Real.log (Real.log (L₂ : ℝ)) + 6)) := Real.exp_le_exp.mpr hsum_le
        _ = Real.exp 18 * (Real.log (L₂ : ℝ)) ^ (3 : ℕ) := by
            have hrew : 3 * (Real.log (Real.log (L₂ : ℝ)) + 6) =
                18 + (3 : ℕ) * Real.log (Real.log (L₂ : ℝ)) := by norm_num; ring
            rw [hrew, Real.exp_add, Real.exp_nat_mul, Real.exp_log hlogL2_pos]
        _ ≤ Real.exp 18 * (2 * LL) ^ (3 : ℕ) := by
            gcongr
        _ = 8 * Real.exp 18 * LL ^ 3 := by ring
    linarith
  have hhi : ∏ p ∈ P_hi, (1 - (p : ℝ) ^ (-α))⁻¹ ≤ Real.exp 2 := by
    have hpow_le : (L₂ + 1) ^ P_hi.card ≤ n := by
      have hdvd : ∏ p ∈ P_hi, p ∣ n := by
        apply prod_coprime_dvd
        · intro p hp q hq hpq
          exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).mpr hpq
        · intro p hp
          exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      calc (L₂ + 1) ^ P_hi.card = ∏ _p ∈ P_hi, (L₂ + 1) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ P_hi, p := Finset.prod_le_prod' fun p hp => not_le.mp (Finset.mem_filter.mp hp).2
        _ ≤ n := Nat.le_of_dvd hn_pos hdvd
    have hcard_le : (P_hi.card : ℝ) ≤ L := by
      have hlogL21 : (1 : ℝ) < Real.log ((L₂ + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_lt_log_three
        (Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ L₂ + 1 by omega)))
      have hlog_pow : (P_hi.card : ℝ) * Real.log ((L₂ + 1 : ℕ) : ℝ) ≤ L := by
        have h1 : Real.log (((L₂ + 1) ^ P_hi.card : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hpow_le)
        rwa [Nat.cast_pow, Real.log_pow] at h1
      nlinarith
    have hterm : ∀ p ∈ P_hi, (1 - (p : ℝ) ^ (-α))⁻¹ ≤ Real.exp (2 / L) := by
      intro p hp
      have hpL2 : L ^ 2 ≤ (p : ℝ) := by
        have : L₂ + 1 ≤ p := not_le.mp (Finset.mem_filter.mp hp).2
        have : ((L₂ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith
      have hp_pos : (0 : ℝ) < p := by nlinarith
      have hpα : (p : ℝ) ^ (-α) ≤ 1 / L := by
        have h1 : (p : ℝ) ^ (-α) ≤ (L ^ 2) ^ (-(3 / 4 : ℝ)) := by
          calc (p : ℝ) ^ (-α) ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith)
            _ ≤ (L ^ 2) ^ (-(3 / 4 : ℝ)) := by
                rw [Real.rpow_neg hp_pos.le, Real.rpow_neg (by positivity)]
                exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
                  (Real.rpow_le_rpow (by positivity) hpL2 (by norm_num))
        have h2 : (L ^ 2) ^ (-(3 / 4 : ℝ)) = L ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL_pos.le]
          congr 1; norm_num
        have h3 : L ^ (-(3 / 2 : ℝ)) ≤ L ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        rw [Real.rpow_neg_one, ← one_div] at h3
        exact h1.trans (h2 ▸ h3)
      have h1L : 1 / L ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hL_pos (by norm_num)]; linarith
      have hinv_le : (1 - (p : ℝ) ^ (-α))⁻¹ ≤ 1 + 2 / L := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        have : (1 - (p : ℝ) ^ (-α)) * (1 + 2 / L) ≥ (1 - 1 / L) * (1 + 2 / L) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have hquad : (1 - 1 / L) * (1 + 2 / L) = 1 + (1 - 2 / L) / L := by field_simp; ring
        have h2L : 2 / L ≤ 1 := (div_le_one hL_pos).mpr (by linarith)
        have hnn : 0 ≤ (1 - 2 / L) / L := div_nonneg (by linarith) hL_pos.le
        linarith
      exact hinv_le.trans (by rw [add_comm]; exact Real.add_one_le_exp _)
    calc ∏ p ∈ P_hi, (1 - (p : ℝ) ^ (-α))⁻¹
        ≤ ∏ _p ∈ P_hi, Real.exp (2 / L) :=
          Finset.prod_le_prod (fun p hp =>
            inv_nonneg.mpr (hfac_pos p (Finset.mem_filter.mp hp).1).le) hterm
      _ = Real.exp ((P_hi.card : ℝ) * (2 / L)) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          rw [mul_div_assoc', div_le_iff₀ hL_pos]
          linarith
  have hM_rpow : (M : ℝ) ^ α = (M : ℝ) * Real.exp (-δ * Real.log (M : ℝ)) := by
    dsimp only [α]
    rw [sub_eq_add_neg, Real.rpow_add hM_pos, Real.rpow_one, Real.rpow_def_of_pos hM_pos,
      mul_comm (Real.log (M : ℝ))]
  have hprod_le : ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-α))⁻¹ ≤
      32 * Real.exp 20 * LL ^ 3 := by
    rw [hprod_split]
    have hhi_nn : 0 ≤ ∏ p ∈ P_hi, (1 - (p : ℝ) ^ (-α))⁻¹ :=
      Finset.prod_nonneg fun p hp => inv_nonneg.mpr (hfac_pos p (Finset.mem_filter.mp hp).1).le
    calc (∏ p ∈ P_lo, (1 - (p : ℝ) ^ (-α))⁻¹) * (∏ p ∈ P_hi, (1 - (p : ℝ) ^ (-α))⁻¹)
        ≤ (32 * Real.exp 18 * LL ^ 3) * Real.exp 2 :=
          mul_le_mul hlo hhi hhi_nn (by positivity)
      _ = 32 * Real.exp 20 * LL ^ 3 := by
          have : Real.exp 18 * Real.exp 2 = Real.exp 20 := by rw [← Real.exp_add]; norm_num
          rw [← this]
          ring
  calc (U.card : ℝ)
      ≤ (M : ℝ) ^ α * ∑ u ∈ U, (u : ℝ) ^ (-α) := hcard_le
    _ ≤ (M : ℝ) ^ α * (32 * Real.exp 20 * LL ^ 3) :=
        mul_le_mul_of_nonneg_left (hsum_rpow.trans hprod_le) (Real.rpow_nonneg hM_pos.le _)
    _ = (M : ℝ) * Real.exp (-δ * Real.log (M : ℝ)) * (32 * Real.exp 20 * LL ^ 3) := by
        rw [hM_rpow]

/- ### Part 4: Four-step Bertrand prime selection and no-sieve R' decomposition -/

private lemma exists_prime_not_dvd_in_window {n D : ℕ} (hn : 0 < n) (hD : 1 ≤ D)
    (hD4 : n < D ^ 4) : ∃ d : ℕ, d.Prime ∧ D < d ∧ d ≤ 16 * D ∧ ¬ d ∣ n := by
  obtain ⟨p₁, hp₁, h1lo, h1hi⟩ := Nat.exists_prime_lt_and_le_two_mul D (by omega)
  obtain ⟨p₂, hp₂, h2lo, h2hi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * D) (by omega)
  obtain ⟨p₃, hp₃, h3lo, h3hi⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * D) (by omega)
  obtain ⟨p₄, hp₄, h4lo, h4hi⟩ := Nat.exists_prime_lt_and_le_two_mul (8 * D) (by omega)
  by_cases d1 : ¬ p₁ ∣ n
  · exact ⟨p₁, hp₁, h1lo, by omega, d1⟩
  · by_cases d2 : ¬ p₂ ∣ n
    · exact ⟨p₂, hp₂, by omega, by omega, d2⟩
    · by_cases d3 : ¬ p₃ ∣ n
      · exact ⟨p₃, hp₃, by omega, by omega, d3⟩
      · by_cases d4 : ¬ p₄ ∣ n
        · exact ⟨p₄, hp₄, by omega, by omega, d4⟩
        · exfalso
          push Not at d1 d2 d3 d4
          have h12 : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp₁ hp₂).mpr (by omega)
          have h13 : Nat.Coprime p₁ p₃ := (Nat.coprime_primes hp₁ hp₃).mpr (by omega)
          have h14 : Nat.Coprime p₁ p₄ := (Nat.coprime_primes hp₁ hp₄).mpr (by omega)
          have h23 : Nat.Coprime p₂ p₃ := (Nat.coprime_primes hp₂ hp₃).mpr (by omega)
          have h24 : Nat.Coprime p₂ p₄ := (Nat.coprime_primes hp₂ hp₄).mpr (by omega)
          have h34 : Nat.Coprime p₃ p₄ := (Nat.coprime_primes hp₃ hp₄).mpr (by omega)
          have hdvd12 : p₁ * p₂ ∣ n := h12.mul_dvd_of_dvd_of_dvd d1 d2
          have hdvd123 : (p₁ * p₂) * p₃ ∣ n :=
            (h13.mul_left h23).mul_dvd_of_dvd_of_dvd hdvd12 d3
          have hdvd1234 : ((p₁ * p₂) * p₃) * p₄ ∣ n :=
            ((h14.mul_left h24).mul_left h34).mul_dvd_of_dvd_of_dvd hdvd123 d4
          have hle : ((p₁ * p₂) * p₃) * p₄ ≤ n := Nat.le_of_dvd hn hdvd1234
          have hgt : D ^ 4 < ((p₁ * p₂) * p₃) * p₄ := by
            have : D ^ 4 = ((D * D) * D) * D := by ring
            rw [this]
            have h12' : D * D < p₁ * p₂ := Nat.mul_lt_mul'' h1lo (by omega)
            have h123' : (D * D) * D < (p₁ * p₂) * p₃ := Nat.mul_lt_mul'' h12' (by omega)
            exact Nat.mul_lt_mul'' h123' (by omega)
          omega

private lemma R'_card_le {n d y : ℕ} (hn : 25 ≤ n) (_hd : 1 ≤ d) (hy : 2 ≤ y)
    (hMy : n / d < y ^ 2) :
    let S := (Finset.Icc 1 y).filter (fun p => p.Prime ∧ ¬ p ∣ n)
    let R' := (Finset.Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t)
    let U := (Finset.Icc 1 (n / d)).filter (fun u => u.primeFactors ⊆ n.primeFactors)
    (R'.card : ℝ) ≤ (U.card : ℝ) +
      (6 * ((n / d : ℕ) : ℝ) / Real.log (y : ℝ)) * (Real.exp 9 * Real.log (Real.log (n : ℝ))) := by
  classical
  intro S R' U
  set M := n / d
  have hlog_y_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  set R₁ := R'.filter (fun t => t ∈ U)
  set R₂ := R'.filter (fun t => t ∉ U)
  have hR_split : R'.card = R₁.card + R₂.card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hR1 : R₁.card ≤ U.card := Finset.card_le_card (fun t ht => (Finset.mem_filter.mp ht).2)
  let Q (u : ℕ) : Finset ℕ := (Finset.Icc 1 (M / u)).filter (fun q => q.Prime ∧ y < q)
  have hR2 : R₂.card ≤ ∑ u ∈ U, (Q u).card := by
    have hsub : R₂ ⊆ U.biUnion (fun u => (Q u).image (fun q => u * q)) := by
      intro t ht
      have htR := (Finset.mem_filter.mp ht).1
      have htnotU := (Finset.mem_filter.mp ht).2
      have htIcc := (Finset.mem_filter.mp htR).1
      have htnoS := (Finset.mem_filter.mp htR).2
      have ⟨ht1, htM⟩ := Finset.mem_Icc.mp htIcc
      have hno : ∀ p : ℕ, p.Prime → p ≤ y → ¬ p ∣ n → ¬ p ∣ t := by
        intro p hp hpy hpn
        exact htnoS p (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpy⟩, hp, hpn⟩)
      -- Factor t = u * v directly with n ≠ 0
      have ht0 : t ≠ 0 := by omega
      let P₁ := t.primeFactors.filter (· ∣ n)
      let P₂ := t.primeFactors.filter (fun p => ¬ p ∣ n)
      let u := ∏ p ∈ P₁, p ^ (t.factorization p)
      let v := ∏ p ∈ P₂, p ^ (t.factorization p)
      have ht_eq : u * v = t := by
        calc u * v = ∏ p ∈ t.primeFactors, p ^ (t.factorization p) :=
              Finset.prod_filter_mul_prod_filter_not t.primeFactors (· ∣ n) _
          _ = t := Nat.prod_factorization_pow_eq_self ht0
      have hu_pos : 0 < u := Finset.prod_pos fun p hp =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
      have hv_pos : 0 < v := Finset.prod_pos fun p hp =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
      have hu_le : u ≤ M := by
        have : u ≤ u * v := Nat.le_mul_of_pos_right u hv_pos
        omega
      have hu_pf : u.primeFactors ⊆ n.primeFactors := by
        intro q hq
        have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hq_dvd_u : q ∣ u := Nat.dvd_of_mem_primeFactors hq
        obtain ⟨p, hp, hqp⟩ := (hq_prime.prime.dvd_finsetProd_iff _).mp hq_dvd_u
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
          (hq_prime.dvd_of_dvd_pow hqp)
        exact Nat.mem_primeFactors.mpr ⟨hq_prime, hqeq ▸ (Finset.mem_filter.mp hp).2, by omega⟩
      have huU : u ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu_pos, hu_le⟩, hu_pf⟩
      have hv_ne1 : v ≠ 1 := by
        intro hv1
        have htu : t = u := by rw [← ht_eq, hv1, mul_one]
        exact htnotU (htu ▸ huU)
      have hv_pf_gt : ∀ q : ℕ, q.Prime → q ∣ v → y < q := by
        intro q hq hqv
        obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqv
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp_prime).mp (hq.dvd_of_dvd_pow hqp)
        have hp_ndvd : ¬ p ∣ n := (Finset.mem_filter.mp hp).2
        have hp_dvd_t : p ∣ t := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        by_contra hle
        subst hqeq
        exact hno q hp_prime (not_lt.mp hle) hp_ndvd hp_dvd_t
      have hv_prime : v.Prime := by
        obtain ⟨q, hq, hqv⟩ := Nat.exists_prime_and_dvd hv_ne1
        have hqy : y < q := hv_pf_gt q hq hqv
        obtain ⟨r, hr⟩ := hqv
        by_cases hr1 : r = 1
        · rw [hr, hr1, mul_one]; exact hq
        · exfalso
          have hr0 : r ≠ 0 := by intro h; rw [h, mul_zero] at hr; omega
          obtain ⟨q', hq', hq'r⟩ := Nat.exists_prime_and_dvd hr1
          have hq'y : y < q' := hv_pf_gt q' hq' (dvd_trans hq'r ⟨q, by rw [mul_comm, hr]⟩)
          have hq'le : q' ≤ r := Nat.le_of_dvd (by omega) hq'r
          have hqq' : y ^ 2 < v := by
            have : y * y < q * q' := Nat.mul_lt_mul'' hqy hq'y
            have : q * q' ≤ q * r := Nat.mul_le_mul_left q hq'le
            rw [sq]; omega
          have hvM : v ≤ M := by
            have : v ≤ u * v := Nat.le_mul_of_pos_left v hu_pos
            omega
          omega
      have hv_gt : y < v := hv_pf_gt v hv_prime dvd_rfl
      have hv_le : v ≤ M / u := by
        rw [Nat.le_div_iff_mul_le hu_pos, mul_comm]; omega
      exact Finset.mem_biUnion.mpr ⟨u, huU, Finset.mem_image.mpr
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hv_prime.one_le, hv_le⟩, hv_prime, hv_gt⟩,
          ht_eq⟩⟩
    calc R₂.card
        ≤ (U.biUnion (fun u => (Q u).image (fun q => u * q))).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ U, ((Q u).image (fun q => u * q)).card := Finset.card_biUnion_le
      _ ≤ ∑ u ∈ U, (Q u).card := Finset.sum_le_sum fun u _ => Finset.card_image_le
  have hQ_bound : ∀ u ∈ U, ((Q u).card : ℝ) ≤ (6 * (M : ℝ) / Real.log (y : ℝ)) * ((1 : ℝ) / (u : ℝ)) := by
    intro u hu
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1
    by_cases hMu : y < M / u
    · have hMu2 : 2 ≤ M / u := by omega
      have hsub : Q u ⊆ (Finset.Icc 1 (M / u)).filter Nat.Prime := fun q hq => by
        have ⟨hI, hP, _⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hI, hP⟩
      have h1 : ((Q u).card : ℝ) ≤ 6 * ((M / u : ℕ) : ℝ) / Real.log ((M / u : ℕ) : ℝ) :=
        (by exact_mod_cast Finset.card_le_card hsub : ((Q u).card : ℝ) ≤ _).trans
          (prime_card_le (M / u) hMu2)
      have hdiv_le : ((M / u : ℕ) : ℝ) ≤ (M : ℝ) / (u : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self M u
      have hlog_ge : Real.log (y : ℝ) ≤ Real.log ((M / u : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hMu.le)
      calc ((Q u).card : ℝ)
          ≤ 6 * ((M / u : ℕ) : ℝ) / Real.log ((M / u : ℕ) : ℝ) := h1
        _ ≤ 6 * ((M : ℝ) / (u : ℝ)) / Real.log (y : ℝ) := by
            have hnum : 6 * ((M / u : ℕ) : ℝ) ≤ 6 * ((M : ℝ) / (u : ℝ)) := by linarith
            exact div_le_div₀ (by positivity) hnum hlog_y_pos hlog_ge
        _ = (6 * (M : ℝ) / Real.log (y : ℝ)) * ((1 : ℝ) / (u : ℝ)) := by ring
    · have hempty : Q u = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro q hq
        have hqle := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
        have hqgt := (Finset.mem_filter.mp hq).2.2
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
  have hR2_real : (R₂.card : ℝ) ≤
      (6 * (M : ℝ) / Real.log (y : ℝ)) * (Real.exp 9 * Real.log (Real.log (n : ℝ))) := by
    calc (R₂.card : ℝ) ≤ ∑ u ∈ U, ((Q u).card : ℝ) := by exact_mod_cast hR2
      _ ≤ ∑ u ∈ U, (6 * (M : ℝ) / Real.log (y : ℝ)) * ((1 : ℝ) / (u : ℝ)) :=
          Finset.sum_le_sum hQ_bound
      _ = (6 * (M : ℝ) / Real.log (y : ℝ)) * ∑ u ∈ U, (1 : ℝ) / (u : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (6 * (M : ℝ) / Real.log (y : ℝ)) * (Real.exp 9 * Real.log (Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (smooth_inv_sum_le n M hn) (by positivity)
  have hcast : (R'.card : ℝ) = (R₁.card : ℝ) + (R₂.card : ℝ) := by exact_mod_cast hR_split
  have hR1_real : (R₁.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hR1
  linarith

/- ### Part 5: Asymptotic parameters and final BigO assembly -/

private noncomputable def targetFn (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (1 / 3 : ℝ)

private lemma eventually_log_le_rpow {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ r := by
  have ho := (isLittleO_log_rpow_atTop hr).bound (show (0 : ℝ) < 1 by norm_num)
  have hnat := tendsto_natCast_atTop_atTop.eventually ho
  filter_upwards [hnat, eventually_ge_atTop 2] with n hn hn2
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  rw [Real.norm_of_nonneg hlog_nn,
    Real.norm_of_nonneg (Real.rpow_nonneg hn_pos.le r), one_mul] at hn
  exact hn

private lemma eventually_loglog_le_log_rpow {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (Real.log (n : ℝ)) ≤ (Real.log (n : ℝ)) ^ r := by
  have ho := (isLittleO_log_rpow_atTop hr).bound (show (0 : ℝ) < 1 by norm_num)
  have hlog_tend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcomp := hlog_tend.eventually ho
  have hge2 := hlog_tend.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hcomp, hge2] with n hn hL2
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith
  have hLL_nn : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg hLL_nn,
    Real.norm_of_nonneg (Real.rpow_nonneg hL_pos.le r), one_mul] at hn
  exact hn

private lemma decay_beats_poly (L : ℝ) (hL_big : (100 : ℝ) ^ 3 ≤ L)
    (hLL2 : 2 ≤ Real.log L) (hLL_rpow : Real.log L ≤ L ^ (1 / 3 : ℝ)) :
    Real.exp (-(1 / 16 : ℝ) * L / Real.log L) * (32 * Real.exp 20 * (Real.log L) ^ 3) ≤ 1 / L := by
  set LL := Real.log L
  have hL_pos : 0 < L := by linarith [show (100 : ℝ) ^ 3 = 1000000 by norm_num]
  have hLL_pos : 0 < LL := by linarith
  have hdecay_beats : 32 * Real.exp 20 * L * LL ^ 3 ≤ Real.exp ((1 / 16 : ℝ) * L / LL) := by
    have hlog_lhs : Real.log (32 * Real.exp 20 * L * LL ^ 3) ≤ 24 + 4 * L ^ (1 / 3 : ℝ) := by
      have h32 : Real.log 32 < 4 := by
        have h32e : (32 : ℝ) < Real.exp 4 := by
          have h25 : (2.5 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
          have hsq : (6.25 : ℝ) < Real.exp 1 * Real.exp 1 := by nlinarith only [h25]
          have h4 : Real.exp 4 = (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) := by
            rw [← Real.exp_add, ← Real.exp_add]; norm_num
          rw [h4]
          nlinarith only [hsq]
        calc Real.log 32 < Real.log (Real.exp 4) := Real.log_lt_log (by norm_num) h32e
          _ = 4 := Real.log_exp 4
      have hlogLL : Real.log LL ≤ LL := (Real.log_le_sub_one_of_pos hLL_pos).trans (by linarith)
      rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) hL_pos.ne',
          Real.log_mul (by norm_num) (Real.exp_pos 20).ne',
          Real.log_exp 20, Real.log_pow]
      push_cast
      linarith only [h32, hlogLL, hLL_rpow]
    have hL13_ge : (100 : ℝ) ≤ L ^ (1 / 3 : ℝ) := by
      have heq : (100 : ℝ) = ((100 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [heq]
      exact Real.rpow_le_rpow (by positivity) hL_big (by norm_num)
    have hL_div : L ^ (2 / 3 : ℝ) ≤ L / LL := by
      rw [le_div_iff₀ hLL_pos]
      calc L ^ (2 / 3 : ℝ) * LL ≤ L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hLL_rpow (Real.rpow_nonneg hL_pos.le _)
        _ = L := by rw [← Real.rpow_add hL_pos]; norm_num
    have hL23_eq : L ^ (2 / 3 : ℝ) = L ^ (1 / 3 : ℝ) * L ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hL_pos]; congr 1; norm_num
    have h16 : (1 / 16 : ℝ) * L ^ (2 / 3 : ℝ) ≤ (1 / 16 : ℝ) * L / LL := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hL_div (by norm_num)
    have hrhs_ge : 24 + 4 * L ^ (1 / 3 : ℝ) ≤ (1 / 16 : ℝ) * L / LL := by
      nlinarith only [hL13_ge, hL23_eq, h16]
    rw [← Real.exp_log (show 0 < 32 * Real.exp 20 * L * LL ^ 3 by positivity)]
    exact Real.exp_le_exp.mpr (hlog_lhs.trans hrhs_ge)
  have hneg : Real.exp (-(1 / 16 : ℝ) * L / LL) = (Real.exp ((1 / 16 : ℝ) * L / LL))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hneg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one_div, le_div_iff₀ hL_pos]
  linarith only [hdecay_beats]

end Erdos360Upper

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1.H2 := by
  open Erdos360Upper in
  unfold OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1.H2
  rw [Asymptotics.isBigO_iff]
  refine ⟨805 + 96 * Real.exp 9, ?_⟩
  have hlog_tend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL_tend : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_tend
  filter_upwards [
    eventually_ge_atTop (32 ^ 6),
    hlog_tend.eventually (eventually_ge_atTop ((100 : ℝ) ^ 3)),
    hLL_tend.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_log_le_rpow (r := 1 / 12) (by norm_num),
    eventually_loglog_le_log_rpow (r := 1 / 3) (by norm_num)
  ] with n hn_big hL_big hLL2 hL_rpow hLL_rpow
  set L := Real.log (n : ℝ)
  set LL := Real.log L
  set g := targetFn n
  set D := ⌊g⌋₊
  have hn25 : 25 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by positivity
  have hL4 : 4 ≤ L := by linarith [show (100 : ℝ) ^ 3 = 1000000 by norm_num]
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hg_pos : 0 < g := by dsimp only [g, targetFn]; positivity
  -- Lower bound on g: g ≥ 2 * n^(1/4)
  have hg_ge : 2 * (n : ℝ) ^ (1 / 4 : ℝ) < g := by
    have h1 : (n : ℝ) ^ (1 / 4 : ℝ) * 2 < (n : ℝ) ^ (11 / 36 : ℝ) := by
      have hpow : (2 : ℝ) < (n : ℝ) ^ (1 / 18 : ℝ) := by
        have h218 : (2 : ℝ) ^ (18 : ℕ) < (n : ℝ) := by
          have : 2 ^ 18 < 32 ^ 6 := by decide
          exact_mod_cast lt_of_lt_of_le this hn_big
        have h2eq : (2 : ℝ) = ((2 : ℝ) ^ (18 : ℕ)) ^ (1 / 18 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        rw [h2eq]
        exact Real.rpow_lt_rpow (by positivity) h218 (by norm_num)
      calc (n : ℝ) ^ (1 / 4 : ℝ) * 2
          < (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 18 : ℝ) :=
            mul_lt_mul_of_pos_left hpow (Real.rpow_pos_of_pos hn_pos _)
        _ = (n : ℝ) ^ (11 / 36 : ℝ) := by
            rw [← Real.rpow_add hn_pos]; congr 1; norm_num
    have hL13 : L ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 36 : ℝ) := by
      calc L ^ (1 / 3 : ℝ) ≤ ((n : ℝ) ^ (1 / 12 : ℝ)) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow hL_pos.le hL_rpow (by norm_num)
        _ = (n : ℝ) ^ (1 / 36 : ℝ) := by
            rw [← Real.rpow_mul hn_pos.le]; congr 1; norm_num
    have hLL13 : 1 ≤ LL ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hdiv : (n : ℝ) ^ (11 / 36 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / L ^ (1 / 3 : ℝ) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hL_pos _)]
      calc (n : ℝ) ^ (11 / 36 : ℝ) * L ^ (1 / 3 : ℝ)
          ≤ (n : ℝ) ^ (11 / 36 : ℝ) * (n : ℝ) ^ (1 / 36 : ℝ) :=
            mul_le_mul_of_nonneg_left hL13 (Real.rpow_nonneg hn_pos.le _)
        _ = (n : ℝ) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_add hn_pos]; congr 1; norm_num
    have hmul : (n : ℝ) ^ (11 / 36 : ℝ) ≤ g := by
      dsimp only [g, targetFn]
      calc (n : ℝ) ^ (11 / 36 : ℝ)
          ≤ (n : ℝ) ^ (1 / 3 : ℝ) / L ^ (1 / 3 : ℝ) := hdiv
        _ = (n : ℝ) ^ (1 / 3 : ℝ) / L ^ (1 / 3 : ℝ) * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) / L ^ (1 / 3 : ℝ) * LL ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hLL13 (by positivity)
    linarith
  have hn14_ge : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have h24 : (2 : ℝ) ^ (4 : ℕ) ≤ (n : ℝ) := by
      have : 2 ^ 4 ≤ 32 ^ 6 := by decide
      exact_mod_cast le_trans this hn_big
    have h2eq : (2 : ℝ) = ((2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2eq]
    exact Real.rpow_le_rpow (by positivity) h24 (by norm_num)
  have hg2 : 2 ≤ g := by linarith
  have hD_le_g : (D : ℝ) ≤ g := Nat.floor_le hg_pos.le
  have hg_lt_D1 : g < (D : ℝ) + 1 := Nat.lt_floor_add_one g
  have hD_ge_half : g / 2 ≤ (D : ℝ) := by linarith
  have hD_pos : 1 ≤ D := Nat.le_floor (by push_cast; linarith)
  have hD_gt_n14 : (n : ℝ) ^ (1 / 4 : ℝ) < (D : ℝ) := by linarith
  have hD4 : n < D ^ 4 := by
    have h1 : (n : ℝ) < ((D ^ 4 : ℕ) : ℝ) := by
      have hpow : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
      rw [← hpow, Nat.cast_pow]
      exact pow_lt_pow_left₀ hD_gt_n14 (Real.rpow_nonneg hn_pos.le _) (by norm_num)
    exact_mod_cast h1
  -- Upper bound on g: g ≤ n^(1/3), hence 32 * g ≤ n^(1/2)
  have hg_le_n13 : g ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hLL_le_L : LL ≤ L := (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
    have hratio : LL ^ (1 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hLL_pos.le hLL_le_L (by norm_num)
    dsimp only [g, targetFn]
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hL_pos _)]
    exact mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hn_pos.le _)
  have h32g_le : 32 * g ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have h32 : (32 : ℝ) ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by
      have h32_6 : (32 : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn_big
      have heq : (32 : ℝ) = ((32 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [heq]
      exact Real.rpow_le_rpow (by positivity) h32_6 (by norm_num)
    calc 32 * g ≤ (n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul h32 hg_le_n13 hg_pos.le (Real.rpow_nonneg hn_pos.le _)
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hn_pos]; congr 1; norm_num
  -- Pick prime d ∈ (D, 16 * D] not dividing n
  obtain ⟨d, hd_prime, hd_gt, hd_le, hdn⟩ := exists_prime_not_dvd_in_window (by omega) hD_pos hD4
  set y := 16 * D * ⌈L⌉₊
  have hceil_ge : 1 ≤ ⌈L⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hL_pos).ne'
  have hceil_le : (⌈L⌉₊ : ℝ) ≤ 2 * L := by
    have : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL_pos.le
    linarith
  have hd_le_y : d ≤ y := by
    have : 16 * D ≤ 16 * D * ⌈L⌉₊ := Nat.le_mul_of_pos_right _ hceil_ge
    omega
  have hy2 : 2 ≤ y := by omega
  have hy_le : (y : ℝ) ≤ 32 * (D : ℝ) * L := by
    have : (y : ℝ) = 16 * (D : ℝ) * (⌈L⌉₊ : ℝ) := by dsimp only [y]; push_cast; rfl
    rw [this]
    nlinarith
  have hlogy_ge : (1 / 4 : ℝ) * L ≤ Real.log (y : ℝ) := by
    have hDy : (D : ℝ) ≤ (y : ℝ) := by exact_mod_cast (show D ≤ y by omega)
    have hn14_y : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (y : ℝ) := hD_gt_n14.le.trans hDy
    calc (1 / 4 : ℝ) * L = Real.log ((n : ℝ) ^ (1 / 4 : ℝ)) := by rw [Real.log_rpow hn_pos]
      _ ≤ Real.log (y : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hn_pos _) hn14_y
  -- Check M = n / d < y^2
  set M := n / d
  have hMy : M < y ^ 2 := by
    have h1 : (n : ℝ) < (y : ℝ) ^ 2 * (d : ℝ) := by
      have hg3 : g ^ 3 = (n : ℝ) * LL / L := by
        have hg_eq : g ^ (3 : ℕ) = ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) /
            (L ^ (1 / 3 : ℝ)) ^ (3 : ℕ) * (LL ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
          dsimp only [g, targetFn]; rw [mul_pow, div_pow]
        rw [hg_eq]
        have r3 (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
        rw [r3 _ hn_pos.le, r3 _ hL_pos.le, r3 _ hLL_pos.le]
        ring
      have hy_ge : 16 * (D : ℝ) * L ≤ (y : ℝ) := by
        have hL_ceil : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
        have : (y : ℝ) = 16 * (D : ℝ) * (⌈L⌉₊ : ℝ) := by dsimp only [y]; push_cast; rfl
        rw [this]
        nlinarith
      have hD3 : g ^ 3 / 8 ≤ (D : ℝ) ^ 3 := by
        have : (g / 2) ^ 3 ≤ (D : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hD_ge_half 3
        linarith
      have hy2d : 32 * (n : ℝ) * L * LL ≤ (y : ℝ) ^ 2 * (d : ℝ) := by
        have hd_real : (D : ℝ) < (d : ℝ) := by exact_mod_cast hd_gt
        calc 32 * (n : ℝ) * L * LL
            = 256 * (g ^ 3 / 8) * L ^ 2 := by rw [hg3]; field_simp; ring
          _ ≤ 256 * (D : ℝ) ^ 3 * L ^ 2 := by
              have : 0 ≤ 256 * L ^ 2 := by positivity
              nlinarith
          _ = (16 * (D : ℝ) * L) ^ 2 * (D : ℝ) := by ring
          _ ≤ (y : ℝ) ^ 2 * (d : ℝ) := by
              have hsq : (16 * (D : ℝ) * L) ^ 2 ≤ (y : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hy_ge 2
              exact mul_le_mul hsq hd_real.le (by positivity) (by positivity)
      have h32n : (n : ℝ) < 32 * (n : ℝ) * L * LL := by
        have hL1 : (1 : ℝ) ≤ L * LL := by nlinarith only [hL4, hLL2]
        nlinarith only [hn_pos, hL1]
      linarith only [h32n, hy2d]
    have hnat : n < y ^ 2 * d := by exact_mod_cast h1
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hnat)
  -- Check M ≥ n^(1/2)
  have hM_ge_sqrt : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (M : ℝ) := by
    have hd_real : (d : ℝ) ≤ 16 * g := by
      have : (d : ℝ) ≤ 16 * (D : ℝ) := by exact_mod_cast hd_le
      linarith
    have hnd_ge : 2 * (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hd_prime.pos)]
      calc 2 * (n : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ)
          ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) * (16 * g) :=
            mul_le_mul_of_nonneg_left hd_real (by positivity)
        _ = (n : ℝ) ^ (1 / 2 : ℝ) * (32 * g) := by ring
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left h32g_le (Real.rpow_nonneg hn_pos.le _)
        _ = (n : ℝ) := by rw [← Real.rpow_add hn_pos]; norm_num
    have hM_sub : (n : ℝ) / (d : ℝ) - 1 < (M : ℝ) := by
      have hlt : n < (M + 1) * d := by
        have := Nat.lt_div_mul_add (a := n) hd_prime.pos
        dsimp only [M]
        linarith
      have hreal : (n : ℝ) < ((M : ℝ) + 1) * (d : ℝ) := by exact_mod_cast hlt
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by exact_mod_cast hd_prime.pos)]
      exact hreal
    have hsqrt_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
    linarith
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := le_trans
      (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)) hM_ge_sqrt
    exact_mod_cast this
  -- Apply 3-step coloring bound
  set S := (Finset.Icc 1 y).filter (fun p => p.Prime ∧ ¬ p ∣ n)
  set R' := (Finset.Icc 1 M).filter (fun t => ∀ p ∈ S, ¬ p ∣ t)
  set U := (Finset.Icc 1 M).filter (fun u => u.primeFactors ⊆ n.primeFactors)
  have hf_bound : Erdos360.f n ≤ S.card + 2 * d + (R'.card / d + 1) :=
    f_le_coloring_bound (by omega) hd_prime hdn
      (fun p hp => (Finset.mem_filter.mp hp).2)
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_prime.one_le, hd_le_y⟩, hd_prime, hdn⟩)
  -- Bound S.card ≤ 768 * g
  have hS_bound : (S.card : ℝ) ≤ 768 * g := by
    have hsub : S ⊆ (Finset.Icc 1 y).filter Nat.Prime := fun p hp => by
      have ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨h1, h2⟩
    have h1 : (S.card : ℝ) ≤ 6 * (y : ℝ) / Real.log (y : ℝ) :=
      (by exact_mod_cast Finset.card_le_card hsub : (S.card : ℝ) ≤ _).trans (prime_card_le y hy2)
    have h2 : 6 * (y : ℝ) / Real.log (y : ℝ) ≤ 768 * (D : ℝ) := by
      calc 6 * (y : ℝ) / Real.log (y : ℝ)
          ≤ 6 * (32 * (D : ℝ) * L) / ((1 / 4 : ℝ) * L) :=
            div_le_div₀ (by positivity) (by linarith) (by positivity) hlogy_ge
        _ = 768 * (D : ℝ) := by field_simp; ring
    linarith
  -- Bound 2 * d ≤ 32 * g
  have hd_bound : (2 * d : ℝ) ≤ 32 * g := by
    have : (d : ℝ) ≤ 16 * (D : ℝ) := by exact_mod_cast hd_le
    linarith
  -- Bound U.card ≤ M / L via Rankin's trick
  have hU_bound : (U.card : ℝ) ≤ (M : ℝ) / L := by
    set δ := 1 / (8 * LL)
    have hrank := smooth_card_rankin n M hM1 hL4 hLL2
    have hlogM : (1 / 2 : ℝ) * L ≤ Real.log (M : ℝ) := by
      calc (1 / 2 : ℝ) * L = Real.log ((n : ℝ) ^ (1 / 2 : ℝ)) := by rw [Real.log_rpow hn_pos]
        _ ≤ Real.log (M : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hn_pos _) hM_ge_sqrt
    have hexp_decay : Real.exp (-δ * Real.log (M : ℝ)) ≤ Real.exp (-(1 / 16 : ℝ) * L / LL) := by
      apply Real.exp_le_exp.mpr
      dsimp only [δ]
      have h1 : -(1 / (8 * LL)) * Real.log (M : ℝ) = -(1 / (8 * LL) * Real.log (M : ℝ)) := by ring
      have h2 : -(1 / 16 : ℝ) * L / LL = -(1 / (8 * LL) * ((1 / 2 : ℝ) * L)) := by ring
      have hmul : 1 / (8 * LL) * ((1 / 2 : ℝ) * L) ≤ 1 / (8 * LL) * Real.log (M : ℝ) :=
        mul_le_mul_of_nonneg_left hlogM (by positivity)
      linarith only [h1, h2, hmul]
    have hprod_le : Real.exp (-(1 / 16 : ℝ) * L / LL) * (32 * Real.exp 20 * LL ^ 3) ≤ 1 / L :=
      decay_beats_poly L hL_big hLL2 hLL_rpow
    calc (U.card : ℝ)
        ≤ (M : ℝ) * Real.exp (-δ * Real.log (M : ℝ)) * (32 * Real.exp 20 * LL ^ 3) := hrank
      _ ≤ (M : ℝ) * (Real.exp (-(1 / 16 : ℝ) * L / LL) * (32 * Real.exp 20 * LL ^ 3)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hexp_decay (by positivity)) (by positivity)
      _ ≤ (M : ℝ) * (1 / L) := mul_le_mul_of_nonneg_left hprod_le (by positivity)
      _ = (M : ℝ) / L := by ring
  -- Bound R'.card / d
  have hR'_div : ((R'.card / d : ℕ) : ℝ) ≤ (4 + 96 * Real.exp 9) * g := by
    have hdiv_le : ((R'.card / d : ℕ) : ℝ) ≤ (R'.card : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hd_prime.pos)]
      exact_mod_cast Nat.div_mul_le_self R'.card d
    have hR' := R'_card_le hn25 hd_prime.one_le hy2 hMy
    have hM_le : (M : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hd_prime.pos)]
      exact_mod_cast Nat.div_mul_le_self n d
    have hR'_le : (R'.card : ℝ) ≤
        (n : ℝ) / ((d : ℝ) * L) +
        (24 * Real.exp 9 * (n : ℝ) * LL) / ((d : ℝ) * L) := by
      have hterm1 : (U.card : ℝ) ≤ (n : ℝ) / ((d : ℝ) * L) := by
        calc (U.card : ℝ) ≤ (M : ℝ) / L := hU_bound
          _ ≤ ((n : ℝ) / (d : ℝ)) / L := div_le_div_of_nonneg_right hM_le hL_pos.le
          _ = (n : ℝ) / ((d : ℝ) * L) := by rw [div_div]
      have hterm2 : (6 * (M : ℝ) / Real.log (y : ℝ)) * (Real.exp 9 * LL) ≤
          (24 * Real.exp 9 * (n : ℝ) * LL) / ((d : ℝ) * L) := by
        have hmy : 6 * (M : ℝ) / Real.log (y : ℝ) ≤ 24 * (n : ℝ) / ((d : ℝ) * L) := by
          calc 6 * (M : ℝ) / Real.log (y : ℝ)
              ≤ 6 * ((n : ℝ) / (d : ℝ)) / ((1 / 4 : ℝ) * L) :=
                div_le_div₀ (by positivity) (by linarith) (by positivity) hlogy_ge
            _ = 24 * (n : ℝ) / ((d : ℝ) * L) := by
                have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd_prime.pos.ne'
                field_simp; ring
        calc (6 * (M : ℝ) / Real.log (y : ℝ)) * (Real.exp 9 * LL)
            ≤ (24 * (n : ℝ) / ((d : ℝ) * L)) * (Real.exp 9 * LL) :=
              mul_le_mul_of_nonneg_right hmy (by positivity)
          _ = (24 * Real.exp 9 * (n : ℝ) * LL) / ((d : ℝ) * L) := by ring
      linarith
    have hkey_alg : (n : ℝ) * LL / (g ^ 2 * L) = g := by
      have hg3 : g ^ 3 = (n : ℝ) * LL / L := by
        have hg_eq : g ^ (3 : ℕ) = ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) /
            (L ^ (1 / 3 : ℝ)) ^ (3 : ℕ) * (LL ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
          dsimp only [g, targetFn]; rw [mul_pow, div_pow]
        rw [hg_eq]
        have r3 (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
        rw [r3 _ hn_pos.le, r3 _ hL_pos.le, r3 _ hLL_pos.le]
        ring
      have hg0 : g ≠ 0 := hg_pos.ne'
      calc (n : ℝ) * LL / (g ^ 2 * L) = ((n : ℝ) * LL / L) / g ^ 2 := by ring
        _ = g ^ 3 / g ^ 2 := by rw [hg3]
        _ = g := by field_simp
    have hd2_ge : g ^ 2 / 4 ≤ (d : ℝ) ^ 2 := by
      have : g / 2 ≤ (d : ℝ) := hD_ge_half.trans (by exact_mod_cast hd_gt.le)
      have := pow_le_pow_left₀ (by positivity) this 2
      linarith
    have hnd2 : (n : ℝ) / ((d : ℝ) ^ 2 * L) ≤ 4 * g / LL := by
      calc (n : ℝ) / ((d : ℝ) ^ 2 * L)
          ≤ (n : ℝ) / ((g ^ 2 / 4) * L) :=
            div_le_div_of_nonneg_left hn_pos.le (by positivity)
              (mul_le_mul_of_nonneg_right hd2_ge hL_pos.le)
        _ = 4 * ((n : ℝ) * LL / (g ^ 2 * L)) / LL := by
            have hLL0 : LL ≠ 0 := hLL_pos.ne'
            field_simp
        _ = 4 * g / LL := by rw [hkey_alg]
    have hnd2_LL : (n : ℝ) * LL / ((d : ℝ) ^ 2 * L) ≤ 4 * g := by
      calc (n : ℝ) * LL / ((d : ℝ) ^ 2 * L)
          = (n : ℝ) / ((d : ℝ) ^ 2 * L) * LL := by ring
        _ ≤ (4 * g / LL) * LL := mul_le_mul_of_nonneg_right hnd2 hLL_pos.le
        _ = 4 * g := div_mul_cancel₀ _ hLL_pos.ne'
    have hnd2_1 : (n : ℝ) / ((d : ℝ) ^ 2 * L) ≤ 4 * g := by
      have : 4 * g / LL ≤ 4 * g := div_le_self (by positivity) (by linarith)
      exact hnd2.trans this
    calc ((R'.card / d : ℕ) : ℝ)
        ≤ (R'.card : ℝ) / (d : ℝ) := hdiv_le
      _ ≤ ((n : ℝ) / ((d : ℝ) * L) +
            (24 * Real.exp 9 * (n : ℝ) * LL) / ((d : ℝ) * L)) / (d : ℝ) :=
          div_le_div_of_nonneg_right hR'_le (by exact_mod_cast hd_prime.pos.le)
      _ = (n : ℝ) / ((d : ℝ) ^ 2 * L) + 24 * Real.exp 9 * ((n : ℝ) * LL / ((d : ℝ) ^ 2 * L)) := by
          have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd_prime.pos.ne'
          field_simp
      _ ≤ 4 * g + 24 * Real.exp 9 * (4 * g) := by
          have : 0 ≤ 24 * Real.exp 9 := by positivity
          nlinarith
      _ = (4 + 96 * Real.exp 9) * g := by ring
  -- Combine all bounds
  have hf_real : (Erdos360.f n : ℝ) ≤ (805 + 96 * Real.exp 9) * g := by
    have hcast : (Erdos360.f n : ℝ) ≤
        (S.card : ℝ) + (2 * d : ℝ) + ((R'.card / d : ℕ) : ℝ) + 1 := by
      have : ((Erdos360.f n : ℕ) : ℝ) ≤ ((S.card + 2 * d + (R'.card / d + 1) : ℕ) : ℝ) := by
        exact_mod_cast hf_bound
      push_cast at this
      linarith
    linarith
  change ‖(Erdos360.f n : ℝ)‖ ≤ (805 + 96 * Real.exp 9) * ‖g‖
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hg_pos.le]
  exact hf_real
