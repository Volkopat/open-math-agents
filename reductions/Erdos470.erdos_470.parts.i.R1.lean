import FormalConjectures.ErdosProblems.«470»

/-!
# A prime-pair reduction for Erdős problem 470(i)

Credit: @ellisjr.

Use an almost-perfect core as in G. Melfi, J. Number Theory 147 (2015),
508–514, section 4. If the divisor sum of m is s = 2m − 1, adjoining the
primes s + u and s + v gives an excess of s + (s² − uv). When s² is
strictly between uv and u(v + 1), this excess exceeds s and is smaller
than the first new prime. For each u the only possible v is ⌊s²/u⌋.
The existence of the odd core and the assertion about prime pairs are
the two unproved hypotheses.
-/

namespace OMA.R_Erdos470_erdos_470_parts_i_R1

open Finset

-- An odd almost-perfect square larger than one.
def H1 : Prop := ∃ t : ℕ, 1 < t ∧ Odd t ∧
    (∑ d ∈ (t ^ 2).divisors, d) + 1 = 2 * t ^ 2

-- This finite search for each t only involves primes and integer products.
def H2 : Prop := ∀ t : ℕ, 1 < t → Odd t →
    let s := 2 * t ^ 2 - 1
    ∃ u v : ℕ, 0 < u ∧ u < v ∧ (s + u).Prime ∧ (s + v).Prime ∧
      u * v < s ^ 2 ∧ s ^ 2 < u * (v + 1)

-- A set of divisors with sum below both fresh primes uses only divisors of m.
lemma small_divisor_sum {m p q : ℕ} (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (t : Finset ℕ) (ht : t ⊆ (m * p * q).divisors)
    (htp : ∑ d ∈ t, d < p) (htq : ∑ d ∈ t, d < q) :
    ∑ d ∈ t, d ≤ ∑ d ∈ m.divisors, d := by
  apply Finset.sum_le_sum_of_subset
  intro d hd
  have hpos := Nat.pos_of_mem_divisors (ht hd)
  have hle : d ≤ ∑ x ∈ t, x :=
    Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hd
  have hnp : ¬ p ∣ d := fun h => (not_le_of_gt (hle.trans_lt htp)) (Nat.le_of_dvd hpos h)
  have hnq : ¬ q ∣ d := fun h => (not_le_of_gt (hle.trans_lt htq)) (Nat.le_of_dvd hpos h)
  have hdp := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
  have hdq := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnq).symm
  have hdiv := Nat.dvd_of_mem_divisors (ht hd)
  exact Nat.mem_divisors.mpr
    ⟨hdp.dvd_of_dvd_mul_right (hdq.dvd_of_dvd_mul_right hdiv), hm.ne'⟩

lemma prime_pair_weird {m s u v : ℕ} (hm : 1 < m)
    (hsum : (∑ d ∈ m.divisors, d) = s) (hs : s + 1 = 2 * m)
    (hu : 0 < u) (huv : u < v) (hp : (s + u).Prime) (hq : (s + v).Prime)
    (hlo : u * v < s ^ 2) (hhi : s ^ 2 < u * (v + 1)) :
    (m * (s + u) * (s + v)).Weird := by
  let p := s + u
  let q := s + v
  let e := s + (s ^ 2 - u * v)
  change (m * p * q).Weird
  change p.Prime at hp
  change q.Prime at hq
  rw [Nat.mul_add, Nat.mul_one] at hhi
  have hexcess : s < e := by dsimp [e]; omega
  have hgap : e < p := by dsimp [p, e]; omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hmp : m < p := by dsimp [p]; omega
  have hcopP : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    (fun h => (not_le_of_gt hmp) (Nat.le_of_dvd (by omega) h))).symm
  have hcopQ : m.Coprime q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr
    (fun h => (not_le_of_gt (hmp.trans hpq)) (Nat.le_of_dvd (by omega) h))).symm
  have hpqCop := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hbalance : s * (p + 1) * (q + 1) + u * v = 2 * (m * p * q) + s + s ^ 2 := by
    calc
      _ = (s + 1) * (p * q) + s + s ^ 2 := by dsimp [p, q]; ring
      _ = _ := by rw [hs]; ring
  have htotal : (∑ d ∈ (m * p * q).divisors, d) = 2 * (m * p * q) + e := by
    calc
      _ = s * (p + 1) * (q + 1) := by
        rw [mul_assoc, Nat.Coprime.sum_divisors_mul (hcopP.mul_right hcopQ),
          Nat.Coprime.sum_divisors_mul hpqCop, hp.sum_divisors, hq.sum_divisors, hsum, mul_assoc]
      _ = _ := by dsimp [e]; omega
  refine ⟨?_, ?_⟩
  · rw [Nat.abundant_iff_sum_divisors, htotal]
    omega
  · rintro ⟨_, t, ht, htSum⟩
    let rest := (m * p * q).properDivisors \ t
    have hrest : (∑ d ∈ rest, d) = e := by
      have hsplit := Finset.sum_sdiff ht (f := fun x => x)
      have hproper := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m * p * q)
      dsimp [rest]
      omega
    have hsub : rest ⊆ (m * p * q).divisors :=
      Finset.sdiff_subset.trans Nat.properDivisors_subset_divisors
    have hbound := small_divisor_sum (by omega : 0 < m) hp hq rest hsub
      (hrest.trans_lt hgap) (hrest.trans_lt (hgap.trans hpq))
    omega

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.parts.i := by
  rintro ⟨t, ht, htOdd, hsum⟩ pairs
  obtain ⟨u, v, hu, huv, hp, hq, hlo, hhi⟩ := pairs t ht htOdd
  let s := 2 * t ^ 2 - 1
  have htSq : 1 < t ^ 2 := by nlinarith
  have hs : s + 1 = 2 * t ^ 2 := by dsimp [s]; omega
  have hw := prime_pair_weird htSq (s := s) (by omega) hs hu huv hp hq hlo hhi
  change (s + u).Prime at hp
  change (s + v).Prime at hq
  exact ⟨t ^ 2 * (s + u) * (s + v), hw, ((htOdd.pow).mul (hp.odd_of_ne_two (by omega))).mul
    (hq.odd_of_ne_two (by omega))⟩

end OMA.R_Erdos470_erdos_470_parts_i_R1
