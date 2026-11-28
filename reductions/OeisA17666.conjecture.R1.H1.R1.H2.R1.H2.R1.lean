import OMAReductions.R_OeisA17666_conjecture_R1_H1_R1_H2_R1
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.ZMod.Basic

/-! The divisor-sum factorization gives one Euler prime. Its exponent is one
modulo four and the rest of the number is a square. -/

namespace OMA.R_OeisA17666_conjecture_R1_H1_R1_H2_R1_H2_R1

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma BigOperators

private theorem even_geometric_iff {p e : ℕ} (oddp : Odd p) :
    (2 ∣ ∑ i ∈ range (e + 1), p ^ i) ↔ Odd e := by
  have hcast : ((↑(∑ i ∈ range (e + 1), p ^ i) : ZMod 2)) = (↑(e + 1) : ZMod 2) := by
    push_cast
    simp [oddp.natCast_zmod_two]
  rw [← ZMod.natCast_eq_zero_iff _ 2, hcast, ZMod.natCast_eq_zero_iff,
    Nat.dvd_iff_mod_eq_zero, Nat.odd_iff]
  omega

private theorem alternating_sum_zero (p : ZMod 4) (hp : p = -1) (k : ℕ) :
    (∑ i ∈ range (2 * k), p ^ i) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, sum_range_succ, sum_range_succ,
      ih, zero_add, pow_succ, hp]
    ring

/-- The prime with odd exponent is unique, and both that prime and its exponent
are one modulo four. -/
private theorem euler_factor {n : ℕ} (hn : 1 < n) (ho : Odd n) (perfect : σ 1 n = 2 * n) :
    ∃ p ∈ n.primeFactors, p % 4 = 1 ∧ n.factorization p % 4 = 1 ∧
      ∀ q ∈ n.primeFactors, q ≠ p → Even (n.factorization q) := by
  let g (p : ℕ) := ∑ i ∈ range (n.factorization p + 1), p ^ i
  have product : σ 1 n = ∏ p ∈ n.primeFactors, g p := by
    simpa only [g, mul_one] using
      (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) (by omega : n ≠ 0))
  have odd_factor (q : ℕ) (hq : q ∈ n.primeFactors) : Odd q := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hq
    exact (Nat.odd_mul.mp (hm ▸ ho)).1
  have no4 : ¬ 4 ∣ σ 1 n := by
    rw [perfect, Nat.odd_iff] at *
    rintro ⟨k,h⟩
    omega
  have two : 2 ∣ ∏ p ∈ n.primeFactors, g p := by
    rw [← product, perfect]
    exact dvd_mul_right 2 n
  have pTwo : Prime (2 : ℕ) := Nat.prime_iff.mp Nat.prime_two
  obtain ⟨p, hp, htwo⟩ := (pTwo.dvd_finsetProd_iff g).mp two
  have hg4 : ¬ 4 ∣ g p := fun h => no4 (product.symm ▸ h.trans (dvd_prod_of_mem g hp))
  have odd_exp : Odd (n.factorization p) := (even_geometric_iff (odd_factor p hp)).mp htwo
  have primeMod : p % 4 = 1 := by
    have oddp : p % 2 = 1 := Nat.odd_iff.mp (odd_factor p hp)
    by_contra neq
    have p3 : p % 4 = 3 := by omega
    have neg : (p : ZMod 4) = -1 := by
      calc
        _ = (3 : ZMod 4) := (ZMod.natCast_eq_natCast_iff' p 3 4).mpr (by simpa using p3)
        _ = _ := by decide
    obtain ⟨k,hk⟩ := odd_exp
    have hsize : n.factorization p + 1 = 2 * (k + 1) := by omega
    apply hg4
    apply (ZMod.natCast_eq_zero_iff (g p) 4).mp
    dsimp only [g]
    push_cast
    rw [hsize]
    exact alternating_sum_zero (p : ZMod 4) neg _
  have expMod : n.factorization p % 4 = 1 := by
    have p1 : (p : ZMod 4) = 1 :=
      (ZMod.natCast_eq_natCast_iff' p 1 4).mpr (by simpa using primeMod)
    have hcast : (g p : ZMod 4) = (↑(n.factorization p + 1) : ZMod 4) := by
      dsimp only [g]
      push_cast
      simp [p1]
    have hc := (ZMod.natCast_eq_natCast_iff' (g p) (n.factorization p + 1) 4).mp hcast
    have h2 := Nat.dvd_iff_mod_eq_zero.mp htwo
    have hn4 := fun h : g p % 4 = 0 => hg4 (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  refine ⟨p,hp,primeMod,expMod,?_⟩
  intro q hq hne
  by_contra he
  have hq2 : 2 ∣ g q :=
    (even_geometric_iff (odd_factor q hq)).mpr (Nat.not_even_iff_odd.mp he)
  have tail : 2 ∣ ∏ r ∈ n.primeFactors.erase p, g r :=
    hq2.trans (dvd_prod_of_mem g (mem_erase.mpr ⟨hne,hq⟩))
  have four : 4 ∣ (∏ r ∈ n.primeFactors.erase p, g r) * g p :=
    mul_dvd_mul tail htwo
  apply no4
  rw [product, ← prod_erase_mul _ g hp]
  exact four

private theorem euler_form {n : ℕ} (hn : 1 < n) (ho : Odd n) (perf : σ 1 n = 2 * n) :
    ∃ p a m : ℕ, p.Prime ∧ p % 4 = 1 ∧ a % 4 = 1 ∧ ¬ p ∣ m ∧ n = p ^ a * m ^ 2 := by
  obtain ⟨p,hp,hpm,hem,heven⟩ := euler_factor hn ho perf
  let s := n.primeFactors.erase p
  let m := ∏ q ∈ s, q ^ (n.factorization q / 2)
  have prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have square : m ^ 2 = ∏ q ∈ s, q ^ n.factorization q := by
    rw [show m = ∏ q ∈ s, q ^ (n.factorization q / 2) by rfl, ← Finset.prod_pow]
    apply prod_congr rfl
    intro q hq
    obtain ⟨hne,hqn⟩ := mem_erase.mp hq
    rw [← pow_mul]
    congr 1
    have ev := Nat.even_iff.mp (heven q hqn hne)
    omega
  have factor : (∏ q ∈ n.primeFactors, q ^ n.factorization q) = n := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      (Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0))
  have coprimePrime : ¬ p ∣ m := by
    intro h
    obtain ⟨q,hq,hd⟩ := ((Nat.prime_iff.mp prime).dvd_finsetProd_iff
      (fun q => q ^ (n.factorization q / 2))).mp h
    obtain ⟨hnq,hqn⟩ := mem_erase.mp hq
    have qprime := Nat.prime_of_mem_primeFactors hqn
    exact hnq ((Nat.prime_dvd_prime_iff_eq prime qprime).mp (prime.dvd_of_dvd_pow hd)).symm
  refine ⟨p,n.factorization p,m,prime,hpm,hem,coprimePrime,?_⟩
  rw [square, mul_comm, show s = n.primeFactors.erase p by rfl, prod_erase_mul _ _ hp, factor]

/-- The Euler prime occurs to its first power. -/
def H1 : Prop := ∀ n p m : ℕ, 1 < n → Odd n → 4 ≤ n.primeFactors.card →
  p.Prime → p % 4 = 1 → ¬ p ∣ m → n = p * m^2 → σ 1 n ≠ 2 * n

/-- Higher exponents of the Euler prime occur in the sequence 5, 9, 13, … . -/
def H2 : Prop := ∀ n p a m : ℕ, 1 < n → Odd n → 4 ≤ n.primeFactors.card →
  p.Prime → p % 4 = 1 → 5 ≤ a → a % 4 = 1 → ¬ p ∣ m → n = p^a * m^2 → σ 1 n ≠ 2 * n

theorem main : H1 → H2 → OMA.R_OeisA17666_conjecture_R1_H1_R1_H2_R1.H2 := by
  intro first higher n hn ho hcount perf
  obtain ⟨p,a,m,hp,hpm,ha,hc,heq⟩ := euler_form hn ho perf
  by_cases one : a = 1
  · exact first n p m hn ho hcount hp hpm hc (by simpa [one] using heq) perf
  · exact higher n p a m hn ho hcount hp hpm (by omega) ha hc heq perf

end OMA.R_OeisA17666_conjecture_R1_H1_R1_H2_R1_H2_R1
