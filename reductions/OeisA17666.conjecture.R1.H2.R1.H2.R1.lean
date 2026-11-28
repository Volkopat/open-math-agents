import OMAReductions.R_OeisA17666_conjecture_R1_H2_R1
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.Ring.GeomSum

/-! Euler-part restrictions for odd multiperfect numbers, using the valuation
identity in Shi-Chao Chen and Hao Luo, Odd multiperfect numbers, Theorems 2.1
and 2.2, https://doi.org/10.1017/S0004972712000858. -/

/- The 2-adic valuation in Chen and Luo's structure theorem for odd
multiperfect numbers. -/

namespace OMA.OddMultiperfect

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma BigOperators

private def weight (p e : ℕ) : ℕ :=
  if Even e then 0 else (p + 1).factorization 2 + (e + 1).factorization 2 - 1

private theorem geometric_parity {p : ℕ} (hp : Odd p) (m : ℕ) :
    (∑ j ∈ range m, p ^ j) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp (hp.pow (n := m))]
    omega

private theorem odd_not_two_dvd {n : ℕ} (hn : Odd n) : ¬ 2 ∣ n := by
  rw [← even_iff_two_dvd]
  exact Nat.not_even_iff_odd.mpr hn

theorem prime_power_weight {p e : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (σ 1 (p ^ e)).factorization 2 = weight p e := by
  by_cases he : Even e
  · rw [weight, if_pos he]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    rw [sigma_one_apply_prime_pow hp, geometric_parity hodd] at hm
    have hh := Nat.even_iff.mp he
    omega
  · rw [weight, if_neg he]
    have heven : Even (e + 1) := by
      rw [Nat.even_iff] at he ⊢
      omega
    have hsub : 2 ∣ p - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hval := Nat.odd_iff.mp hodd
      omega
    have hgeom : σ 1 (p ^ e) * (p - 1) = p ^ (e + 1) - 1 := by
      rw [sigma_one_apply_prime_pow hp]
      exact geom_sum_mul_of_one_le hp.one_lt.le (e + 1)
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hv := padicValNat.pow_two_sub_pow hp.one_lt hsub (odd_not_two_dvd hodd)
      (Nat.succ_ne_zero e) heven
    rw [one_pow, ← hgeom,
      padicValNat.mul (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
        (Nat.sub_ne_zero_of_lt hp.one_lt)] at hv
    simp only [Nat.factorization_def _ Nat.prime_two]
    simp only [Nat.succ_eq_add_one] at hv
    omega

theorem prime_divisor_odd {n p : ℕ} (hn : Odd n) (hp : p ∈ n.primeFactors) : Odd p := by
  apply (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two
  rintro rfl
  exact odd_not_two_dvd hn (Nat.dvd_of_mem_primeFactors hp)

theorem sigma_factorization_two {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    (σ 1 n).factorization 2 = ∑ p ∈ n.primeFactors, weight p (n.factorization p) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  rw [Nat.factorization_prod_apply (fun p hp => (sigma_pos 1 _
    (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne')]
  change (∑ p ∈ n.primeFactors, (σ 1 (p ^ n.factorization p)).factorization 2) = _
  exact Finset.sum_congr rfl fun p hp => prime_power_weight
    (Nat.prime_of_mem_primeFactors hp) (prime_divisor_odd hodd hp)

theorem multiplicity_identity {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hodd : Odd n) (hs : σ 1 n = k * n) :
    (∑ p ∈ n.primeFactors, weight p (n.factorization p)) = k.factorization 2 := by
  rw [← sigma_factorization_two hn hodd, hs]
  rw [Nat.factorization_mul hk hn, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (odd_not_two_dvd hodd), add_zero]

private theorem first_valuation {m : ℕ} (hm : m % 4 = 2) : m.factorization 2 = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by omega
  have hpos : 1 ≤ padicValNat 2 m := by
    apply one_le_padicValNat_of_dvd hm0
    omega
  have hlt : padicValNat 2 m < 2 := by
    by_contra! h
    have hd := (padicValNat_dvd_iff_le hm0).mpr h
    change 4 ∣ m at hd
    omega
  rw [Nat.factorization_def _ Nat.prime_two]
  omega

private theorem value_one_mod_four {m : ℕ} (hm : m ≠ 0) (hval : m.factorization 2 = 1) :
    m % 4 = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two] at hval
  have h2 : 2 ∣ m := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 m)
  have h4 : ¬ 4 ∣ m := by
    intro h
    have hc : 2 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm).mp h
    omega
  omega

theorem weight_eq_zero {p e : ℕ} (hp : Odd p) : weight p e = 0 ↔ Even e := by
  by_cases he : Even e
  · simp [weight, he]
  · have hp2 : 2 ∣ p + 1 := by
      have h := Nat.odd_iff.mp hp
      omega
    have he2 : 2 ∣ e + 1 := by
      rw [Nat.even_iff] at he
      omega
    have hp1 : 0 < (p + 1).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd (by omega) hp2
    have he1 : 0 < (e + 1).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd (by omega) he2
    rw [weight, if_neg he]
    constructor
    · intro h
      omega
    · exact fun h => (he h).elim

theorem weight_one_cases {p e : ℕ} (hp : Odd p) (hw : weight p e = 1) :
    p % 4 = 1 ∧ e % 4 = 1 := by
  have he : ¬ Even e := by
    intro hev
    rw [weight, if_pos hev] at hw
    omega
  have hp2 : 2 ∣ p + 1 := by
    have h := Nat.odd_iff.mp hp
    omega
  have he2 : 2 ∣ e + 1 := by
    rw [Nat.even_iff] at he
    omega
  have hp1 : 0 < (p + 1).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd (by omega) hp2
  have he1 : 0 < (e + 1).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd (by omega) he2
  rw [weight, if_neg he] at hw
  have hp4 := value_one_mod_four (Nat.succ_ne_zero p) (by omega :
    (p + 1).factorization 2 = 1)
  have he4 := value_one_mod_four (Nat.succ_ne_zero e) (by omega :
    (e + 1).factorization 2 = 1)
  omega

theorem odd_index_cases {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) (hnOdd : Odd n)
    (hkOdd : Odd k) (hs : σ 1 n = k * n) :
    ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
  have hsum := multiplicity_identity hn hk hnOdd hs
  rw [Nat.factorization_eq_zero_of_not_dvd (odd_not_two_dvd hkOdd)] at hsum
  intro p hp
  have hle := Finset.single_le_sum (f := fun p => weight p (n.factorization p))
    (fun _ _ => Nat.zero_le _) hp
  exact (weight_eq_zero (prime_divisor_odd hnOdd hp)).mp (by omega)

theorem square_of_even_exponents {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, Even (n.factorization p)) :
    ∃ m : ℕ, n = m ^ 2 := by
  let m := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  refine ⟨m, ?_⟩
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Nat.prod_primeFactors_pow_factorization hn
    _ = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p / 2)) ^ 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      have hEven := Nat.even_iff.mp (h p hp)
      congr 1
      omega
    _ = m ^ 2 := Finset.prod_pow _ _ _

theorem single_euler_factor {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hnOdd : Odd n) (hk4 : k % 4 = 2) (hs : σ 1 n = k * n) :
    ∃ p ∈ n.primeFactors, p % 4 = 1 ∧ n.factorization p % 4 = 1 ∧
      ∀ q ∈ n.primeFactors, q ≠ p → Even (n.factorization q) := by
  classical
  let f := fun p => weight p (n.factorization p)
  have hsum := multiplicity_identity hn hk hnOdd hs
  rw [first_valuation hk4] at hsum
  change (∑ p ∈ n.primeFactors, f p) = 1 at hsum
  have hex : ∃ p ∈ n.primeFactors, f p ≠ 0 := by
    by_contra! h
    have hz : (∑ p ∈ n.primeFactors, f p) = 0 := Finset.sum_eq_zero h
    omega
  obtain ⟨p, hp, hpos⟩ := hex
  have hsplit := Finset.add_sum_erase n.primeFactors f hp
  have hp1 : f p = 1 := by omega
  have hrest : (∑ q ∈ n.primeFactors.erase p, f q) = 0 := by omega
  obtain ⟨hp4, he4⟩ := weight_one_cases (prime_divisor_odd hnOdd hp) hp1
  refine ⟨p, hp, hp4, he4, ?_⟩
  intro q hq hqp
  have hle := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.mpr ⟨hqp, hq⟩)
  exact (weight_eq_zero (prime_divisor_odd hnOdd hq)).mp (by
    change f q = 0
    omega)

end OMA.OddMultiperfect

namespace OMA.R_OeisA17666_conjecture_R1_H2_R1_H2_R1

open ArithmeticFunction OMA.OddMultiperfect
open scoped ArithmeticFunction.sigma BigOperators

private theorem euler_decomposition {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hodd : Odd n) (hk4 : k % 4 = 2) (hs : σ 1 n = k * n) :
    ∃ p e m : ℕ, p.Prime ∧ p % 4 = 1 ∧ e % 4 = 1 ∧ p.Coprime m ∧ n = p ^ e * m ^ 2 := by
  obtain ⟨p, hp, hp4, he4, hEven⟩ := single_euler_factor hn hk hodd hk4 hs
  let e := n.factorization p
  let R := n.primeFactors.erase p
  let m := ∏ q ∈ R, q ^ (n.factorization q / 2)
  have hprime := Nat.prime_of_mem_primeFactors hp
  refine ⟨p, e, m, hprime, hp4, he4, ?_, ?_⟩
  · apply Nat.Coprime.prod_right
    intro q hq
    have hq' := Finset.mem_erase.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hq'.2
    have hcp : p.Coprime q := (hprime.coprime_iff_not_dvd).mpr fun hd =>
      hq'.1 ((Nat.prime_dvd_prime_iff_eq hprime hqprime).mp hd).symm
    exact hcp.pow_right _
  · calc
      n = ∏ q ∈ n.primeFactors, q ^ n.factorization q := Nat.prod_primeFactors_pow_factorization hn
      _ = p ^ e * ∏ q ∈ R, q ^ n.factorization q :=
        (Finset.mul_prod_erase n.primeFactors (fun q => q ^ n.factorization q) hp).symm
      _ = p ^ e * ∏ q ∈ R, (q ^ (n.factorization q / 2)) ^ 2 := by
        congr 1
        apply Finset.prod_congr rfl
        intro q hq
        have hq' := Finset.mem_erase.mp hq
        have he := Nat.even_iff.mp (hEven q hq'.2 hq'.1)
        rw [← pow_mul]
        congr 1
        omega
      _ = p ^ e * m ^ 2 := by rw [Finset.prod_pow]

/-- The odd-index case is supported on squares. -/
def H1 : Prop := ∀ n k : ℕ, 1 < n → Odd n → 3 ≤ k → 7 ≤ n.primeFactors.card →
  Odd k → (∃ m : ℕ, n = m ^ 2) → σ 1 n ≠ k * n

/-- The indices congruent to two modulo four have a single Euler factor. -/
def H2 : Prop := ∀ n k : ℕ, 1 < n → Odd n → 3 ≤ k → 7 ≤ n.primeFactors.card →
  k % 4 = 2 →
  (∃ p e m : ℕ, p.Prime ∧ p % 4 = 1 ∧ e % 4 = 1 ∧ p.Coprime m ∧ n = p ^ e * m ^ 2) →
  σ 1 n ≠ k * n

/-- The remaining even indices carry the exact sum of their 2-adic contributions. -/
def H3 : Prop := ∀ n k : ℕ, 1 < n → Odd n → 3 ≤ k → 7 ≤ n.primeFactors.card →
  4 ∣ k →
  (∑ p ∈ n.primeFactors, weight p (n.factorization p)) = k.factorization 2 →
  σ 1 n ≠ k * n

theorem main : H1 → H2 → H3 → OMA.R_OeisA17666_conjecture_R1_H2_R1.H2 := by
  intro hSquare hEuler hHigher n k hn hodd hk hcard hs
  have hn0 : n ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  by_cases hkOdd : Odd k
  · have hEven := odd_index_cases hn0 hk0 hodd hkOdd hs
    exact hSquare n k hn hodd hk hcard hkOdd (square_of_even_exponents hn0 hEven) hs
  by_cases hk4 : 4 ∣ k
  · exact hHigher n k hn hodd hk hcard hk4 (multiplicity_identity hn0 hk0 hodd hs) hs
  have hk2 : k % 4 = 2 := by
    rw [Nat.odd_iff] at hkOdd
    omega
  exact hEuler n k hn hodd hk hcard hk2 (euler_decomposition hn0 hk0 hodd hk2 hs) hs

end OMA.R_OeisA17666_conjecture_R1_H2_R1_H2_R1
