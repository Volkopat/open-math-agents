import FormalConjectures.ErdosProblems.«11»

-- Reduction Erdos11.erdos_11.variants.finite_bound2.R1 of Erdős Problem 11 — finite bound2
-- Credit: @justusklocke-cloud
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos11_erdos_11_variants_finite_bound2_R1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem checkSmall : ((List.range 4095).all fun j =>
    let n := 2 * j + 3
    (List.range 6).any fun l => decide (2 ^ l ≤ n) && (n - 2 ^ l).minSqFac.isNone) = true := by
  decide +kernel

/-- Every odd `n` with `1 < n ≤ 2^13` is a squarefree number plus a power of two. -/
theorem small (n : ℕ) (hn : Odd n) (hbound : n ≤ 2 ^ 13) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  obtain ⟨m, hm⟩ := hn
  let j := m - 1
  have hbound' : n ≤ 8192 := hbound
  have hj : j < 4095 := by dsimp [j]; omega
  have hval : n = 2 * j + 3 := by dsimp [j]; omega
  have hcert := List.all_eq_true.mp checkSmall j (List.mem_range.mpr hj)
  change ((List.range 6).any fun l =>
    decide (2 ^ l ≤ 2 * j + 3) && (2 * j + 3 - 2 ^ l).minSqFac.isNone) = true at hcert
  rw [← hval] at hcert
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp hcert
  obtain ⟨hle, hs⟩ := Bool.and_eq_true_iff.mp hl
  exact ⟨n - 2 ^ l, l, Nat.squarefree_iff_minSqFac.mpr (Option.isNone_iff_eq_none.mp hs),
    (Nat.sub_add_cancel (of_decide_eq_true hle)).symm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkRepeatedPrime :
    ∀ (d : Fin 13) (p : Fin 64), 0 < d.val → p.val.Prime → p.val ≠ 2 →
      p.val ^ 2 ∣ 2 ^ d.val - 1 → p.val = 3 := by
  decide +kernel

private theorem repeatedPrime {n p i j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 13) (hn : 2 ^ j ≤ n)
    (hpi : p ^ 2 ∣ n - 2 ^ i) (hpj : p ^ 2 ∣ n - 2 ^ j) : p = 3 := by
  let d := j - i
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have hd' : d < 13 := by omega
  have hjd : j = i + d := by omega
  have hpows : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hij.le
  have hdiff : p ^ 2 ∣ 2 ^ j - 2 ^ i := by
    rw [← show (n - 2 ^ i) - (n - 2 ^ j) = 2 ^ j - 2 ^ i by omega]
    exact Nat.dvd_sub hpi hpj
  have hfactor : 2 ^ j - 2 ^ i = 2 ^ i * (2 ^ d - 1) := by
    rw [hjd, pow_add, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hfactor] at hdiff
  have hc : p.Coprime 2 :=
    hp.coprime_iff_not_dvd.mpr fun h ↦ hp2 ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp h).symm
  have hsmall : p ^ 2 ∣ 2 ^ d - 1 := ((hc.pow_left 2).pow_right i).dvd_of_dvd_mul_left hdiff
  have hdpos : 1 < (2 : ℕ) ^ d := by
    simpa using (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hd)
  have hple := Nat.le_of_dvd (Nat.sub_pos_of_lt hdpos) hsmall
  have hupper : 2 ^ d ≤ (2 : ℕ) ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
  have hp_lt : p < 64 := by
    by_contra! h
    have hpow := Nat.pow_le_pow_left h 2
    omega
  exact checkRepeatedPrime ⟨d, hd'⟩ ⟨p, hp_lt⟩ hd hp hp2 hsmall


/-- When three divides the target, all thirteen shifts require distinct primes above three. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 2 ^ 13 < n → n < 2 ^ 50 → 3 ∣ n →
    ∀ p : Fin 13 → ℕ, Function.Injective p →
      (∀ i, (p i).Prime ∧ 3 < p i ∧ p i < 2 ^ 25 ∧ p i ^ 2 ∣ n - 2 ^ (i.val + 1)) →
      False

/-- Otherwise it suffices to cover the shifts whose difference is not already a multiple of nine. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 2 ^ 13 < n → n < 2 ^ 50 → ¬ 3 ∣ n →
    ∀ p : Fin 13 → ℕ,
      Set.InjOn p {i | ¬ 3 ^ 2 ∣ n - 2 ^ (i.val + 1)} →
      (∀ i, ¬ 3 ^ 2 ∣ n - 2 ^ (i.val + 1) →
        (p i).Prime ∧ 3 < p i ∧ p i < 2 ^ 25 ∧ p i ^ 2 ∣ n - 2 ^ (i.val + 1)) →
      False

theorem main : H1 → H2 → type_of% @Erdos11.erdos_11.variants.finite_bound2 := by
  intro h1 h2 n hn hbound hn'
  by_cases hsmall : n ≤ 2 ^ 13
  · exact small n hn hsmall hn'
  have hnlarge : 2 ^ 13 < n := Nat.lt_of_not_ge hsmall
  have hshift (i : Fin 13) : 2 ^ (i.val + 1) < n :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)).trans_lt hnlarge
  by_contra hno
  have hbad (i : Fin 13) : ¬ Squarefree (n - 2 ^ (i.val + 1)) := by
    intro hs
    exact hno ⟨_, i.val + 1, hs, (Nat.sub_add_cancel (hshift i).le).symm⟩
  have hwitness (i : Fin 13) : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n - 2 ^ (i.val + 1) := by
    have hi := hbad i
    rw [Nat.squarefree_iff_prime_squarefree] at hi
    push Not at hi
    simpa only [pow_two] using hi
  choose p hp hd using hwitness
  have hp2 (i : Fin 13) : p i ≠ 2 := by
    intro heq
    have ha : 2 ∣ n - 2 ^ (i.val + 1) :=
      (show 2 ∣ p i ^ 2 by rw [heq]; decide).trans (hd i)
    have hb : 2 ∣ 2 ^ (i.val + 1) := dvd_pow_self 2 (Nat.succ_ne_zero _)
    have hc := Nat.dvd_add ha hb
    rw [Nat.sub_add_cancel (hshift i).le] at hc
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hc)
  have hpUpper (i : Fin 13) : p i < 2 ^ 25 := by
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt (hshift i)) (hd i)
    by_contra! hlarge
    have hpow := Nat.pow_le_pow_left hlarge 2
    rw [← pow_mul] at hpow
    exact (not_le_of_gt hbound) (hpow.trans (hle.trans (Nat.sub_le _ _)))
  have hpGtThree (i : Fin 13) (h3 : p i ≠ 3) : 3 < p i := by
    have := (hp i).two_le
    have := hp2 i
    omega
  have heqPrime {i j : Fin 13} (hij : i.val < j.val) (heq : p i = p j) : p i = 3 := by
    exact repeatedPrime (hp i) (hp2 i) (by omega) (by omega) (by omega)
      (hshift j).le (hd i) (heq ▸ hd j)
  have hinj (i j : Fin 13) (hi : p i ≠ 3) (hj : p j ≠ 3) (heq : p i = p j) : i = j := by
    rcases lt_trichotomy i.val j.val with hlt | he | hgt
    · exact (hi (heqPrime hlt heq)).elim
    · exact Fin.ext he
    · exact (hj (heqPrime hgt heq.symm)).elim
  by_cases hthree : 3 ∣ n
  · have hp3 (i : Fin 13) : p i ≠ 3 := by
      intro heq
      have ha : 3 ∣ n - 2 ^ (i.val + 1) :=
        (show 3 ∣ p i ^ 2 by rw [heq]; decide).trans (hd i)
      have hb := Nat.dvd_sub hthree ha
      rw [Nat.sub_sub_self (hshift i).le] at hb
      exact (by decide : ¬ (3 : ℕ) ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hb)
    exact h1 n hn hnlarge hbound hthree p (fun {i j} => hinj i j (hp3 i) (hp3 j))
      (fun i => ⟨hp i, hpGtThree i (hp3 i), hpUpper i, hd i⟩)
  · have hp3 (i : Fin 13) (hi : ¬ 3 ^ 2 ∣ n - 2 ^ (i.val + 1)) : p i ≠ 3 := by
      intro heq
      exact hi (heq ▸ hd i)
    exact h2 n hn hnlarge hbound hthree p (fun {i} hi {j} hj => hinj i j (hp3 i hi) (hp3 j hj))
      (fun i hi => ⟨hp i, hpGtThree i (hp3 i hi), hpUpper i, hd i⟩)

end OMA.R_Erdos11_erdos_11_variants_finite_bound2_R1
