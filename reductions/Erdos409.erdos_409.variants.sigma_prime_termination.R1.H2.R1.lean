import OMAReductions.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1

/-! Split divisor-sum termination into odd inputs and the even inputs whose odd prime
exponents are all even. Every remaining even input enters the odd class in one step. -/

namespace OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1_H2_R1
open Finset
open scoped ArithmeticFunction.sigma

private theorem geometric_odd {p : ℕ} (hp : Odd p) (e : ℕ) :
    Odd (∑ k ∈ range (e+1), p^k) ↔ Even e := by
  rw [odd_sum_iff_odd_card_odd]
  simpa [hp.pow] using (Nat.odd_add_one : Odd (e + 1) ↔ ¬ Odd e) |>.trans Nat.not_odd_iff_even

private theorem exponents_even {n : ℕ} (hn : n ≠ 0) (hs : Odd (σ 1 n)) :
    ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  intro p hp htwo
  have prime := Nat.prime_of_mem_primeFactors hp
  have odd := prime.odd_of_ne_two htwo
  have hprod : Odd (∏ q ∈ n.primeFactors, ∑ j ∈ range (n.factorization q + 1), q^j) := by
    rwa [← Nat.sum_divisors hn, ← ArithmeticFunction.sigma_one_apply]
  have dvd : (∑ j ∈ range (n.factorization p + 1), p^j) ∣
      ∏ q ∈ n.primeFactors, ∑ j ∈ range (n.factorization q + 1), q^j :=
    dvd_prod_of_mem _ hp
  obtain ⟨t, ht⟩ := dvd
  rw [ht] at hprod
  exact (geometric_odd odd _).mp (Nat.odd_mul.mp hprod).1

private theorem step_ge (n : ℕ) (hn : 1 < n) : n ≤ σ 1 n - 1 := by
  have members : ({1,n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with h | h
    · rw [h]
      exact Nat.one_mem_divisors.mpr (by omega)
    · rw [h]
      exact Nat.mem_divisors_self n (by omega)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => d) members (by intros; omega)
  rw [sum_pair (by omega : (1 : ℕ) ≠ n), ← ArithmeticFunction.sigma_one_apply] at hsum
  omega


/-- The odd starting values form the first remaining orbit class. -/
def H1 : Prop := ∀ n : ℕ, 300 < n → Odd n →
  ∃ i, ((fun m => ArithmeticFunction.sigma 1 m - 1)^[i] n).Prime

/-- The even inputs with square odd part form the exceptional orbit class. -/
def H2 : Prop := ∀ n : ℕ, 300 < n → Even n →
  (∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)) →
  ∃ i, ((fun m => ArithmeticFunction.sigma 1 m - 1)^[i] n).Prime

theorem main : H1 → H2 →
    OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1.H2 := by
  intro oddInputs exceptional n hn
  by_cases ho : Odd n
  · exact oddInputs n hn ho
  have even : Even n := Nat.not_odd_iff_even.mp ho
  by_cases hs : Odd (σ 1 n)
  · exact exceptional n hn even (exponents_even (by omega) hs)
  have grows := step_ge n (by omega)
  have nextOdd : Odd (σ 1 n - 1) :=
    Nat.Even.sub_odd (by omega) (Nat.not_odd_iff_even.mp hs) (by decide)
  obtain ⟨i, hi⟩ := oddInputs (σ 1 n - 1) (by omega) nextOdd
  exact ⟨i + 1, by simpa only [Function.iterate_succ_apply] using hi⟩

end OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1_H2_R1
