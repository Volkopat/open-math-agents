import OMAStatements.S_oeis_a142591
import Mathlib

namespace OMA.A142591Proof

open OMA.S_oeis_a142591

-- j n is a member of its defining set when n is positive
lemma j_mem {n : ℕ} (hn : 0 < n) :
    j n ∈ (n.divisors).filter (fun d => d * d ≤ n) := by
  have hne : ((n.divisors).filter (fun d => d * d ≤ n)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 (by omega), by omega⟩⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  unfold j
  rw [heq]
  exact hi

-- every divisor d with d * d ≤ n is at most j n
lemma le_j {n d : ℕ} (hd : d ∈ n.divisors) (hdd : d * d ≤ n) : d ≤ j n := by
  unfold j
  exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hd, hdd⟩)

-- a divisor of n with 1 < d < (minFac n)^2 is prime
lemma prime_of_dvd_lt {n d : ℕ} (hd : d ∣ n) (h1 : 1 < d)
    (hlt : d < n.minFac * n.minFac) : d.Prime := by
  by_contra hnp
  have hsq : d.minFac ^ 2 ≤ d := Nat.minFac_sq_le_self (by omega) hnp
  have hmp : d.minFac.Prime := Nat.minFac_prime (by omega)
  have hle : n.minFac ≤ d.minFac :=
    Nat.minFac_le_of_dvd hmp.two_le (Nat.dvd_trans (Nat.minFac_dvd d) hd)
  have h2 : n.minFac * n.minFac ≤ d.minFac * d.minFac := Nat.mul_le_mul hle hle
  rw [pow_two] at hsq
  omega

-- the divisors of a product of two primes
lemma dvd_pq {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hk : k ∣ p * q) :
    k = 1 ∨ k = p ∨ k = q ∨ k = p * q := by
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.1 hk
  rcases (Nat.dvd_prime hp).1 ha with h | h <;> rcases (Nat.dvd_prime hq).1 hb with h' | h' <;>
    rw [h, h'] at hab
  · left
    omega
  · right; right; left
    omega
  · right; left
    omega
  · right; right; right
    exact hab.symm

-- forward direction: a composite term of A143578 is such a semiprime
lemma forward {n : ℕ} (h : inA143578 n) (h2 : 2 ≤ n) (hnp : ¬ n.Prime) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q ∧ (p + q) ∣ (p * q + 1) := by
  unfold inA143578 at h
  obtain ⟨hn, hall⟩ := h
  have hJmem := j_mem hn
  rw [Finset.mem_filter] at hJmem
  obtain ⟨hJdiv, -⟩ := hJmem
  have h1 := hall 1 (Nat.one_mem_divisors.2 (by omega))
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  have h2' := hall n.minFac (Nat.mem_divisors.2 ⟨hpn, by omega⟩)
  have hJK0 : j n * (n / j n) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hJdiv)
  obtain ⟨J, hJ⟩ : ∃ J, j n = J := ⟨_, rfl⟩
  rw [hJ] at h1 h2' hJK0
  obtain ⟨K, hK⟩ : ∃ K, n / J = K := ⟨_, rfl⟩
  rw [hK] at h1 h2' hJK0
  rw [Nat.div_one] at h1
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpp : n.minFac * (n.minFac + n / n.minFac) = n.minFac * n.minFac + n := by
    rw [Nat.mul_add, Nat.mul_div_cancel' hpn]
  have h3 : (J + K) ∣ n.minFac * n.minFac + n := by
    rw [← hpp]
    exact Nat.dvd_trans h2' (Nat.dvd_mul_left _ _)
  have h4 : (J + K) ∣ (n.minFac * n.minFac + n) - (1 + n) := Nat.dvd_sub h3 h1
  have h5 : (n.minFac * n.minFac + n) - (1 + n) = n.minFac * n.minFac - 1 := by omega
  rw [h5] at h4
  have hp2 : 2 ≤ n.minFac := hp.two_le
  have hpp4 : 2 * 2 ≤ n.minFac * n.minFac := Nat.mul_le_mul hp2 hp2
  have h6 : J + K ≤ n.minFac * n.minFac - 1 := Nat.le_of_dvd (by omega) h4
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mul] at hJK0
    omega
  have hK0 : K ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hJK0
    omega
  have hJlt : J < n.minFac * n.minFac := by omega
  have hKlt : K < n.minFac * n.minFac := by omega
  have hJn : J ∣ n := ⟨K, hJK0.symm⟩
  have hKn : K ∣ n := ⟨J, by rw [Nat.mul_comm K J]; exact hJK0.symm⟩
  have hJ1 : J ≠ 1 := by
    intro hJ1
    rw [hJ1, Nat.one_mul] at hJK0
    have hKp : K.Prime := prime_of_dvd_lt hKn (by omega) hKlt
    rw [hJK0] at hKp
    exact hnp hKp
  have hK1 : K ≠ 1 := by
    intro hK1
    rw [hK1, Nat.mul_one] at hJK0
    have hJp : J.Prime := prime_of_dvd_lt hJn (by omega) hJlt
    rw [hJK0] at hJp
    exact hnp hJp
  refine ⟨J, K, prime_of_dvd_lt hJn (by omega) hJlt, prime_of_dvd_lt hKn (by omega) hKlt,
    hJK0.symm, ?_⟩
  rw [hJK0, Nat.add_comm n 1]
  exact h1

-- converse for p < q: the semiprime p * q is a term of A143578
lemma conv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (hd : (p + q) ∣ (p * q + 1)) : inA143578 (p * q) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq4 : 2 * 2 ≤ p * q := Nat.mul_le_mul hp2 hq2
  have hn0 : p * q ≠ 0 := by omega
  have hjp : j (p * q) = p := by
    have hmem := j_mem (n := p * q) (by omega)
    rw [Finset.mem_filter] at hmem
    obtain ⟨hdiv, hsq⟩ := hmem
    have hge : p ≤ j (p * q) :=
      le_j (Nat.mem_divisors.2 ⟨Nat.dvd_mul_right p q, hn0⟩) (Nat.mul_le_mul (le_refl p) hlt.le)
    rcases dvd_pq hp hq (Nat.dvd_of_mem_divisors hdiv) with h | h | h | h
    · omega
    · exact h
    · exfalso
      rw [h] at hsq
      nlinarith
    · exfalso
      rw [h] at hsq
      nlinarith
  unfold inA143578
  refine ⟨by omega, fun k hk => ?_⟩
  rw [hjp, Nat.mul_div_cancel_left q hp.pos]
  rcases dvd_pq hp hq (Nat.dvd_of_mem_divisors hk) with h | h | h | h
  · rw [h, Nat.div_one, Nat.add_comm 1 (p * q)]
    exact hd
  · rw [h]
    exact ⟨1, by rw [Nat.mul_div_cancel_left q hp.pos, Nat.mul_one]⟩
  · rw [h]
    exact ⟨1, by rw [Nat.mul_div_cancel p hq.pos, Nat.mul_one, Nat.add_comm q p]⟩
  · have hpos : 0 < p * q := by omega
    rw [h, Nat.div_self hpos]
    exact hd

end OMA.A142591Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a142591.main := by
  intro n
  constructor
  · rintro ⟨h, h2, hnp⟩
    exact OMA.A142591Proof.forward h h2 hnp
  · rintro ⟨p, q, hp, hq, rfl, hd⟩
    have hne : p ≠ q := by
      intro hpq
      rw [← hpq] at hd
      have h1 : p ∣ p * p + 1 := Nat.dvd_trans (Nat.dvd_add (Nat.dvd_refl p) (Nat.dvd_refl p)) hd
      have h2 : p ∣ 1 := (Nat.dvd_add_right (Nat.dvd_mul_right p p)).1 h1
      have h3 := Nat.le_of_dvd Nat.one_pos h2
      have h4 := hp.two_le
      omega
    refine ⟨?_, ?_, Nat.not_prime_mul hp.ne_one hq.ne_one⟩
    · rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact OMA.A142591Proof.conv hp hq hlt hd
      · rw [Nat.mul_comm p q]
        refine OMA.A142591Proof.conv hq hp hlt ?_
        rw [Nat.add_comm q p, Nat.mul_comm q p]
        exact hd
    · have h4 := Nat.mul_le_mul hp.two_le hq.two_le
      omega
