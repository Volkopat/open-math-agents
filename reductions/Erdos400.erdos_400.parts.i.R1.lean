import FormalConjectures.ErdosProblems.«400»

/-! # A square-root prime sieve for the summatory factorial excess -/

-- Reduction Erdos400.erdos_400.parts.i.R1 of Erdős Problem 400 — i
-- Credit: @Pixelstorm44

namespace OMA.R_Erdos400_erdos_400_parts_i_R1

open Nat Finset Filter
open scoped Asymptotics Topology Classical

private lemma large_prime {p m : ℕ} (hp : p.Prime) (hm : m < p ^ 2) :
    (m !).factorization p = m / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hm)]
  simp [show Ico 1 2 = ({1} : Finset ℕ) by decide]

private lemma budgets {k n : ℕ} (a : Fin k → ℕ) :
    (∏ i, (a i)!) ∣ n ! ↔ ∀ p : ℕ, p.Prime →
      (∑ i, ((a i)!).factorization p) ≤ (n !).factorization p := by
  rw [← Nat.factorization_prime_le_iff_dvd (Finset.prod_ne_zero_iff.mpr
    (fun i _ => Nat.factorial_ne_zero (a i))) (Nat.factorial_ne_zero n)]
  simp_rw [Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero (a i))]

private lemma coord_bound {k n : ℕ} (hn : 0 < n) (a : Fin k → ℕ)
    (ha : (∏ i, (a i)!) ∣ n !) : ∀ i, a i ≤ n := by
  intro i
  have hd := (Finset.dvd_prod_of_mem (fun j => (a j)!) (mem_univ i)).trans ha
  exact le_of_not_gt fun h => (Nat.le_of_dvd (Nat.factorial_pos n) hd).not_gt
    ((Nat.factorial_lt hn).2 h)

private lemma sum_bound {k n : ℕ} {a : Fin k → ℕ} (ha : ∀ i, a i ≤ n) :
    ∑ i, a i ≤ k * n := by
  simpa using Finset.sum_le_sum (s := univ) (fun i _ => ha i)

/-- Trim coordinates to hit a prescribed total without increasing a factorial. -/
private lemma trim {k : ℕ} (a : Fin k → ℕ) (m : ℕ) (hm : m ≤ ∑ i, a i) :
    ∃ b : Fin k → ℕ, (∀ i, b i ≤ a i) ∧ ∑ i, b i = m := by
  induction k generalizing m with
  | zero =>
    simp at hm
    exact ⟨a, fun _ => le_rfl, by simp [hm]⟩
  | succ k ih =>
    rw [Fin.sum_univ_succ] at hm
    obtain ⟨b, hba, hb⟩ := ih (fun i => a i.succ) (m - a 0) (by omega)
    refine ⟨Fin.cons (min m (a 0)) b, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using hba j
    · rw [Fin.sum_univ_succ]
      simpa [hb] using (show min m (a 0) + (m - a 0) = m by omega)

/-- For an exact level, a large prime fails precisely when the total residue is
at least one full prime below the available remainder plus the excess. -/
private lemma carry_iff {k n t p : ℕ} (a : Fin k → ℕ) (hp : p.Prime)
    (he : n + t = ∑ i, a i) :
    n / p < ∑ i, a i / p ↔ p + (∑ i, a i % p) ≤ n % p + t := by
  have hsum : (∑ i, a i % p) + p * (∑ i, a i / p) = n + t := by
    rw [he, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [Nat.mod_add_div]
  have hn := Nat.mod_add_div n p
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_left p (show n / p + 1 ≤ ∑ i, a i / p from h)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · intro h
    have hmul : p * (n / p + 1) ≤ p * (∑ i, a i / p) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact Nat.le_of_mul_le_mul_left hmul hp.pos

private lemma g_levels {k n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    t ≤ Erdos400.g k n ↔ ∃ a : Fin k → ℕ, n + t = ∑ i, a i ∧ (∏ i, (a i)!) ∣ n ! := by
  let S : Set ℕ := { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i)!) ∣ n !) }
  change t ≤ sSup S ↔ _
  have hb : BddAbove S := by
    refine ⟨k * n, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (Nat.sub_le _ _).trans (sum_bound (coord_bound hn a ha))
  have hne : S.Nonempty := ⟨0, fun _ => 0, by simp, by simp⟩
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := Nat.sSup_mem hne hb
    obtain ⟨b, hba, hb⟩ := trim a (n + t) (by omega)
    exact ⟨b, hb.symm, (Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
      Nat.factorial_dvd_factorial (hba i)).trans ha⟩
  · rintro ⟨a, he, ha⟩
    have h := le_csSup hb (show (∑ i, a i) - n ∈ S from ⟨a, ha, rfl⟩)
    omega

/-- Count positive levels of the maximum, removing precisely the levels for which every
small-prime candidate exceeds at least one of the remaining floor budgets. -/
theorem level_identity (k n : ℕ) (hn : 0 < n) :
  let candidate (n t : ℕ) (a : Fin k → ℕ) : Prop :=
    (∀ i, a i ≤ n) ∧ n + t = ∑ i, a i ∧
    ∀ p : ℕ, p.Prime → p ^ 2 ≤ n →
      (∑ i, ((a i)!).factorization p) ≤ (n !).factorization p
  let levels (n : ℕ) := (Icc 1 (k * n)).filter fun t => ∃ a, candidate n t a
  let obstructed (n t : ℕ) := ∀ a, candidate n t a →
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p + (∑ i, a i % p) ≤ n % p + t
  let losses (n : ℕ) := ((levels n).filter (obstructed n)).card
  Erdos400.g k n + losses n = (levels n).card := by
  intro candidate levels obstructed losses
  have hs : ((levels n).filter fun t => ¬ obstructed n t) = Icc 1 (Erdos400.g k n) := by
    ext t
    simp only [mem_filter, levels, mem_Icc]
    constructor
    · rintro ⟨⟨⟨ht, _⟩, _⟩, hgood⟩
      dsimp only [obstructed] at hgood
      push Not at hgood
      obtain ⟨a, ha, hbig⟩ := hgood
      refine ⟨ht, (g_levels hn ht).2 ⟨a, ha.2.1, (budgets a).2 ?_⟩⟩
      intro p hp
      by_cases h : p ^ 2 ≤ n
      · exact ha.2.2 p hp h
      · have hpn := lt_of_not_ge h
        simp only [large_prime hp hpn, large_prime hp ((ha.1 _).trans_lt hpn)]
        exact le_of_not_gt fun hf => (not_le_of_gt (hbig p hp hpn))
          ((carry_iff a hp ha.2.1).1 hf)
    · rintro ⟨ht, hg⟩
      obtain ⟨a, he, hd⟩ := (g_levels hn ht).1 hg
      have hc := coord_bound hn a hd
      have hb := (budgets a).1 hd
      have ha : candidate n t a := ⟨hc, he, fun p hp _ => hb p hp⟩
      refine ⟨⟨⟨ht, (Nat.le_add_left t n).trans (he.le.trans (sum_bound hc))⟩, a, ha⟩, ?_⟩
      intro hall
      obtain ⟨p, hp, hpn, hbad⟩ := hall a ha
      have h := hb p hp
      simp only [large_prime hp hpn, large_prime hp ((hc _).trans_lt hpn)] at h
      exact (not_lt_of_ge h) ((carry_iff a hp he).2 hbad)
  have hc := (levels n).card_filter_add_card_filter_not (obstructed n)
  rw [hs, Nat.card_Icc] at hc
  dsimp only [losses]
  omega

/-- The summatory law for the optimization using only primes at most the square root. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
  let candidate (n t : ℕ) (a : Fin k → ℕ) : Prop :=
    (∀ i, a i ≤ n) ∧ n + t = ∑ i, a i ∧
    ∀ p : ℕ, p.Prime → p ^ 2 ≤ n →
      (∑ i, ((a i)!).factorization p) ≤ (n !).factorization p
  let levels (n : ℕ) := (Icc 1 (k * n)).filter fun t => ∃ a, candidate n t a
  Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, ((levels n).card : ℝ)) / (x * Real.log x))
    atTop (𝓝 c)

/-- The aggregate number of levels blocked by the remaining floor tests is negligible. -/
def H2 : Prop := ∀ k : ℕ, 2 ≤ k →
  let candidate (n t : ℕ) (a : Fin k → ℕ) : Prop :=
    (∀ i, a i ≤ n) ∧ n + t = ∑ i, a i ∧
    ∀ p : ℕ, p.Prime → p ^ 2 ≤ n →
      (∑ i, ((a i)!).factorization p) ≤ (n !).factorization p
  let levels (n : ℕ) := (Icc 1 (k * n)).filter fun t => ∃ a, candidate n t a
  let obstructed (n t : ℕ) := ∀ a, candidate n t a →
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p + (∑ i, a i % p) ≤ n % p + t
  let losses (n : ℕ) := ((levels n).filter (obstructed n)).card
  Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, (losses n : ℝ)) / (x * Real.log x))
    atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @Erdos400.erdos_400.parts.i := by
  intro hsmall hloss k hk
  let candidate (n t : ℕ) (a : Fin k → ℕ) : Prop :=
    (∀ i, a i ≤ n) ∧ n + t = ∑ i, a i ∧
    ∀ p : ℕ, p.Prime → p ^ 2 ≤ n →
      (∑ i, ((a i)!).factorization p) ≤ (n !).factorization p
  let levels (n : ℕ) := (Icc 1 (k * n)).filter fun t => ∃ a, candidate n t a
  let obstructed (n t : ℕ) := ∀ a, candidate n t a →
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p + (∑ i, a i % p) ≤ n % p + t
  let losses (n : ℕ) := ((levels n).filter (obstructed n)).card
  obtain ⟨c, hc, hlim⟩ := hsmall k hk
  refine ⟨c, Asymptotics.isEquivalent_of_tendsto_one ?_⟩
  have he (x : ℕ) : (∑ n ∈ Icc 1 x, ((levels n).card : ℝ)) -
      (∑ n ∈ Icc 1 x, (losses n : ℝ)) = ∑ n ∈ Icc 1 x, (Erdos400.g k n : ℝ) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have h : (Erdos400.g k n : ℝ) + (losses n : ℝ) = ((levels n).card : ℝ) := by
      exact_mod_cast level_identity k n (mem_Icc.mp hn).1
    linarith
  change Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, ((levels n).card : ℝ)) / (x * Real.log x))
    atTop (𝓝 c) at hlim
  have hl : Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, (losses n : ℝ)) / (x * Real.log x))
    atTop (𝓝 0) := hloss k hk
  have h := (hlim.sub hl).div_const c
  rw [sub_zero, div_self hc.ne'] at h
  apply h.congr
  intro x
  change ((_ / _ - _ / _) / c) = _ / (c * (x : ℝ) * Real.log x)
  rw [← sub_div, he, div_div]
  ring_nf

end OMA.R_Erdos400_erdos_400_parts_i_R1
