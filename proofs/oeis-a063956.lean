import OMAStatements.S_oeis_a063956
import Mathlib

/-!
# A063956: an identity for the sum of the unitary prime divisors

a(n) is the sum of the primes in P1(n) = {p : v_p(n) = 1}. Split P1(n) = A ⊔ B by whether p ∣ m and
P1(m) = C ⊔ D by whether p ∣ n. Since v_p(mn) = v_p(m) + v_p(n), P1(mn) = C ⊔ A. Since
v_p(gcd(n², m)) = min(2v_p(n), v_p(m)) and 2v_p(n) ≠ 1, P1(gcd(n², m)) = D; likewise
P1(gcd(n, m²)) = B. Summing gives a(mn) + a(gcd(n², m)) + a(gcd(n, m²)) = a(n) + a(m).
-/

namespace PA063956

/-- The primes dividing `n` exactly once. -/
def P1 (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => n.factorization p = 1)

theorem a_eq (n : ℕ) : OMA.S_oeis_a063956.a n = ∑ p ∈ P1 n, p := by
  unfold OMA.S_oeis_a063956.a P1
  rw [Finset.sum_filter]

theorem mem_P1 (n p : ℕ) : p ∈ P1 n ↔ n.factorization p = 1 := by
  unfold P1
  rw [Finset.mem_filter, ← Nat.support_factorization, Finsupp.mem_support_iff]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

theorem prime_of_fact {n p : ℕ} (h : n.factorization p = 1) : p.Prime := by
  have : p ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
  exact Nat.prime_of_mem_primeFactors this

theorem fact_zero_iff {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) : n.factorization p = 0 ↔ ¬ p ∣ n := by
  rw [hp.dvd_iff_one_le_factorization hn]; omega

end PA063956

open PA063956 in
theorem OMA.solution : type_of% @OMA.S_oeis_a063956.main := by
  intro m n hm hn
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  set A := (P1 n).filter (fun p => ¬ p ∣ m)
  set B := (P1 n).filter (fun p => p ∣ m)
  set C := (P1 m).filter (fun p => ¬ p ∣ n)
  set D := (P1 m).filter (fun p => p ∣ n)
  have hmn : P1 (m * n) = C ∪ A := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, mem_P1, C, A]
    rw [Nat.factorization_mul hm0 hn0, Finsupp.add_apply]
    constructor
    · intro h
      rcases (by omega : m.factorization p = 1 ∧ n.factorization p = 0 ∨
          m.factorization p = 0 ∧ n.factorization p = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, (fact_zero_iff (prime_of_fact h1) hn0).mp h2⟩
      · right; exact ⟨h2, (fact_zero_iff (prime_of_fact h2) hm0).mp h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have := (fact_zero_iff (prime_of_fact h1) hn0).mpr h2; omega
      · have := (fact_zero_iff (prime_of_fact h1) hm0).mpr h2; omega
  have hAC : Disjoint C A := by
    rw [Finset.disjoint_left]
    intro p hC hA
    have h1 : p ∣ n := by
      have hpn := (mem_P1 n p).mp (Finset.mem_filter.mp hA).1
      exact ((prime_of_fact hpn).dvd_iff_one_le_factorization hn0).mpr (by omega)
    exact (Finset.mem_filter.mp hC).2 h1
  have hg1 : P1 ((n ^ 2).gcd m) = D := by
    ext p
    simp only [Finset.mem_filter, mem_P1, D]
    rw [Nat.factorization_gcd (pow_ne_zero 2 hn0) hm0, Finsupp.inf_apply, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul]
    constructor
    · intro h
      have h1 : m.factorization p = 1 := by
        rcases le_total (2 * n.factorization p) (m.factorization p) with hle | hle
        · rw [inf_eq_left.mpr hle] at h; omega
        · rw [inf_eq_right.mpr hle] at h; exact h
      refine ⟨h1, ((prime_of_fact h1).dvd_iff_one_le_factorization hn0).mpr ?_⟩
      rcases le_total (2 * n.factorization p) (m.factorization p) with hle | hle
      · rw [inf_eq_left.mpr hle] at h; omega
      · omega
    · rintro ⟨h1, h2⟩
      have := ((prime_of_fact h1).dvd_iff_one_le_factorization hn0).mp h2
      rw [inf_eq_right.mpr (by omega)]
      exact h1
  have hg2 : P1 (n.gcd (m ^ 2)) = B := by
    ext p
    simp only [Finset.mem_filter, mem_P1, B]
    rw [Nat.factorization_gcd hn0 (pow_ne_zero 2 hm0), Finsupp.inf_apply, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul]
    constructor
    · intro h
      have h1 : n.factorization p = 1 := by
        rcases le_total (n.factorization p) (2 * m.factorization p) with hle | hle
        · rw [inf_eq_left.mpr hle] at h; exact h
        · rw [inf_eq_right.mpr hle] at h; omega
      refine ⟨h1, ((prime_of_fact h1).dvd_iff_one_le_factorization hm0).mpr ?_⟩
      rcases le_total (n.factorization p) (2 * m.factorization p) with hle | hle
      · omega
      · rw [inf_eq_right.mpr hle] at h; omega
    · rintro ⟨h1, h2⟩
      have := ((prime_of_fact h1).dvd_iff_one_le_factorization hm0).mp h2
      rw [inf_eq_left.mpr (by omega)]
      exact h1
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, hmn, hg1, hg2, Finset.sum_union hAC,
    ← Finset.sum_filter_add_sum_filter_not (P1 n) (fun p => p ∣ m),
    ← Finset.sum_filter_add_sum_filter_not (P1 m) (fun p => p ∣ n)]
  ring
