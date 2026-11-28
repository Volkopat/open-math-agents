import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1
import Mathlib

namespace OddWeirdRepeatedReuse

open Finset ArithmeticFunction

theorem excess_of_pseudoperfect {n : ℕ} (certificate : n.Pseudoperfect) :
    let E : ℤ := (sigma 1 n : ℤ) - 2 * (n : ℤ)
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E),
      (∑ d ∈ s, (d : ℤ)) = E := by
  classical
  let E : ℤ := (sigma 1 n : ℤ) - 2 * (n : ℤ)
  obtain ⟨_, chosen, represented, amount⟩ := certificate
  let rest := n.properDivisors \ chosen
  have chosen_sum : (∑ d ∈ chosen, (d : ℤ)) = (n : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun x : ℕ => (x : ℤ)) amount
  have total : (sigma 1 n : ℤ) = (∑ d ∈ n.properDivisors, (d : ℤ)) + n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have split := Finset.sum_sdiff represented (f := fun d : ℕ => (d : ℤ))
  have rest_sum : (∑ d ∈ rest, (d : ℤ)) = E := by
    dsimp [E,rest]
    linarith only [chosen_sum,total,split]
  change ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E),
    (∑ d ∈ s, (d : ℤ)) = E
  refine ⟨rest, ?_, rest_sum⟩
  intro d hd
  have le : (d : ℤ) ≤ ∑ x ∈ rest, (x : ℤ) :=
    Finset.single_le_sum (fun x _ => Int.natCast_nonneg x) hd
  rw [rest_sum] at le
  exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hd,le⟩

end OddWeirdRepeatedReuse

namespace OddWeirdRepeatedReuse

open Finset ArithmeticFunction

private theorem sigma_split (n : ℕ) :
    (sigma 1 n : ℤ) = (∑ d ∈ n.properDivisors, (d : ℤ)) + n := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  simp

private theorem deficient_excess {n : ℕ} (deficient : n.Deficient) :
    (sigma 1 n : ℤ) - 2 * (n : ℤ) < 0 := by
  have h : (∑ d ∈ n.properDivisors, d) < n := deficient
  have cast : ((∑ d ∈ n.properDivisors, d : ℕ) : ℤ) < n := by exact_mod_cast h
  have proper : (∑ d ∈ n.properDivisors, (d : ℤ)) < n := by
    simpa only [Nat.cast_sum] using cast
  rw [sigma_split]
  omega

private theorem closed_excess {P D q : ℤ} (E : ℕ → ℤ)
    (atZero : E 0 = -D) (step : ∀ k, E (k+1) = q*E k + (2*P+D)) (k : ℕ) :
    (q-1)*E k = q^k*(2*P-D*(q-2)) - (2*P+D) := by
  induction k with
  | zero => rw [atZero,pow_zero]; ring
  | succ k ih =>
    rw [step,pow_succ]
    calc
      _ = q*((q-1)*E k)+(q-1)*(2*P+D) := by ring
      _ = _ := by rw [ih]; ring

theorem repeated_index {b q j : ℕ} (bp : 1 < b) (hq : q.Prime) (cop : b.Coprime q)
    (abundant : (b*q^(j+2)).Abundant)
    (primitive : ∀ d ∈ (b*q^(j+2)).properDivisors, d.Deficient) :
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let D := (b : ℤ)-P
    let r := (2*P)%D
    0 < D ∧ 0 < r ∧ (q : ℤ) = (2*P)/D + 2 ∧
      r*(q:ℤ)^(j+1) < 2*P+D ∧ 2*P+D < r*(q:ℤ)^(j+2) := by
  let P : ℤ := ∑ d ∈ b.properDivisors, (d : ℤ)
  let D : ℤ := (b : ℤ)-P
  let E (k : ℕ) : ℤ := (sigma 1 (b*q^k) : ℤ) - 2*(b*q^k : ℕ)
  have sig : (sigma 1 b : ℤ) = 2*P+D := by
    rw [sigma_split]
    dsimp [P,D]
    ring
  have sigma_power (k : ℕ) : (sigma 1 (b*q^k) : ℤ) =
      (sigma 1 b : ℤ) * ∑ i ∈ Finset.range (k+1), (q:ℤ)^i := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right k), sigma_one_apply_prime_pow hq]
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow]
  have sum_step (k : ℕ) : (∑ i ∈ Finset.range (k+1+1), (q:ℤ)^i) =
      (q:ℤ)*(∑ i ∈ Finset.range (k+1), (q:ℤ)^i) + 1 := by
    rw [Finset.sum_range_succ' (fun i => (q:ℤ)^i) (k+1)]
    simp only [pow_succ', Finset.mul_sum, pow_zero]
  have step (k : ℕ) : E (k+1) = (q:ℤ)*E k + (2*P+D) := by
    simp only [E, sigma_power, sum_step, Nat.cast_mul, Nat.cast_pow, pow_succ', ← sig]
    ring
  have atZero : E 0 = -D := by
    simp only [E,pow_zero,mul_one,sig]
    dsimp [D]
    ring
  have earlier (k : ℕ) (hk : k < j+2) : E k < 0 := by
    have proper : b*q^k ∈ (b*q^(j+2)).properDivisors := by
      exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left b (pow_dvd_pow q hk.le),
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) (by omega)⟩
    exact deficient_excess (primitive _ proper)
  have final : 0 < E (j+2) := by
    have ab := Nat.abundant_iff_sum_divisors.mp abundant
    rw [← ArithmeticFunction.sigma_one_apply] at ab
    have cast : 2 * ((b*q^(j+2) : ℕ) : ℤ) < (sigma 1 (b*q^(j+2)) : ℤ) := by
      exact_mod_cast ab
    exact sub_pos.mpr cast
  have dpos : 0 < D := by
    have h := earlier 0 (by omega)
    rw [atZero] at h
    omega
  have q1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have spos : 0 < 2*P+D := by
    rw [← sig]
    exact_mod_cast (sigma_pos_iff.mpr (by omega : 0 < b) : 0 < sigma 1 b)
  obtain ⟨low,high,_⟩ :=
    OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1.OddWeirdRepeatedFinal.repeat_from_excess
      (q:=(q:ℤ)) (by omega) spos E atZero step (j+1)
      (earlier 1 (by omega)) (earlier (j+1) (by omega)) (by simpa [Nat.add_assoc] using final)
  have lowDiv : (q:ℤ)-2 ≤ (2*P)/D :=
    Int.le_ediv_of_mul_le dpos (by simpa only [mul_comm] using low.le)
  have highDiv : (2*P)/D < (q:ℤ)-1 :=
    Int.ediv_lt_of_lt_mul dpos (by simpa only [mul_comm] using high)
  have qEq : (2*P)/D = (q:ℤ)-2 := by omega
  have residue : (2*P)%D = 2*P-D*((q:ℤ)-2) := by
    have decomp := Int.emod_add_mul_ediv (2*P) D
    rw [qEq] at decomp
    omega
  have before := closed_excess E atZero step (j+1)
  have after := closed_excess E atZero step (j+2)
  have beforeSign := mul_neg_of_pos_of_neg (by omega : 0 < (q:ℤ)-1) (earlier (j+1) (by omega))
  have afterSign := mul_pos (by omega : 0 < (q:ℤ)-1) final
  rw [← residue, mul_comm ((q:ℤ)^(j+1))] at before
  rw [← residue, mul_comm ((q:ℤ)^(j+2))] at after
  change 0 < D ∧ 0 < (2*P)%D ∧ (q:ℤ) = (2*P)/D+2 ∧
    ((2*P)%D)*(q:ℤ)^(j+1) < 2*P+D ∧ 2*P+D < ((2*P)%D)*(q:ℤ)^(j+2)
  exact ⟨dpos, by omega, by omega, by omega, by omega⟩

end OddWeirdRepeatedReuse

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1

open Finset ArithmeticFunction

def H1 : Prop :=
  ∀ b q j : ℕ, q.Prime →
    let n := b*q^(j+2)
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    n.primeFactors.card ≤ 4 → n.Pseudoperfect

def H2 : Prop :=
  ∀ b q j : ℕ, 1 < b → q.Prime → 3 ≤ q → b.Coprime q →
    (∀ p ∈ b.primeFactors, p < q) →
    let n := b*q^(j+2)
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    4 < n.primeFactors.card →
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let D := (b : ℤ)-P
    let r := (2*P)%D
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    let G : ℤ := Nat.gcd (sigma 1 b) (2*b)
    0 < D → 0 < r → (q : ℤ) = (2*P)/D+2 →
    r*(q:ℤ)^(j+1) < 2*P+D → 2*P+D < r*(q:ℤ)^(j+2) →
    (¬ ∃ s ⊆ b.divisors, (∑ d ∈ s, (d : ℤ)) = E) →
    G ∣ E → 0 < E →
    (∀ L g : ℤ, 1 ≤ L → 1 ≤ g → (2*g+1)*(2*L+8*g+8) ≤ P →
      (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
      (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
      E < L ∧ G < L) →
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1.H2 := by
  intro solvedCases otherCases b q j bp hp q3 cop largest
  dsimp only
  intro size odd abundant primitive three missing divides positive noInterval
  by_cases small : (b*q^(j+2)).primeFactors.card ≤ 4
  · exact OddWeirdRepeatedReuse.excess_of_pseudoperfect
      (solvedCases b q j hp size odd abundant primitive three small)
  · obtain ⟨ds,rs,nextPrime,before,after⟩ :=
      OddWeirdRepeatedReuse.repeated_index bp hp cop abundant primitive
    exact otherCases b q j bp hp q3 cop largest size odd abundant primitive three
      (by omega) ds rs nextPrime before after missing divides positive noInterval

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1