import OMAReductions.R_OeisA245212_conjecture_R1_H2_R1

/-! Eliminate the power of two from the even cofactor's linear quotient.
For b=2^k*u, a candidate denominator divides (k+1) times an integer
depending only on the odd core u. This gives a finite logarithmic search. -/
namespace OMA.R_OeisA245212_conjecture_R1_H2_R1_H2_R1
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
/-- An admissible denominator divides a number depending only linearly on k;
the dyadic exponent is logarithmically bounded in the odd cofactor moments. -/
def H1 : Prop := ∀ k u : ℕ, Odd u →
  let W (b : ℕ) := ∑ d ∈ b.divisors, d*d.divisors.card
  let S (b : ℕ) := σ 1 b
  let T (b : ℕ) := b*b.divisors.card
  let N (b : ℕ) := W b+S b
  let D (b : ℕ) := 4*b*b.divisors.card-(2*W b+S b)
  let C (u : ℕ) := W u+(W u-S u)
  let K (u : ℕ) := W u*S u+2*T u*(W u-S u)
  0<D (2^k*u) → D (2^k*u)∣N (2^k*u) →
    D (2^k*u)∣(k+1)*K u ∧ (k+1)/2≤Nat.log 2 (C u+K u) ∧
    N (2^k*u)/D (2^k*u) ≤ k*W u+S u+(k+1)*K u

/-- For each odd core, only finitely many dyadic exponents and one quotient per exponent remain. -/
def H2 : Prop := ∀ u : ℕ, Odd u → 1<u →
  let W (b : ℕ) := ∑ d ∈ b.divisors, d*d.divisors.card
  let S (b : ℕ) := σ 1 b
  let T (b : ℕ) := b*b.divisors.card
  let N (b : ℕ) := W b+S b
  let D (b : ℕ) := 4*b*b.divisors.card-(2*W b+S b)
  let C (u : ℕ) := W u+(W u-S u)
  let K (u : ℕ) := W u*S u+2*T u*(W u-S u)
  ∀ k ∈ Icc 1 (2*Nat.log 2 (C u+K u)),
    let b := 2^k*u
    let p := N b/D b
    D b∣(k+1)*K u → p≤k*W u+S u+(k+1)*K u →
    ¬ (0<D b ∧ D b∣N b ∧ p.Prime ∧ Odd p ∧ p.Coprime b)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H2_R1.H2 := by
  let W (b : ℕ) := ∑ d ∈ b.divisors, d*d.divisors.card
  let S (b : ℕ) := σ 1 b
  let T (b : ℕ) := b*b.divisors.card
  let N (b : ℕ) := W b+S b
  let D (b : ℕ) := 4*b*b.divisors.card-(2*W b+S b)
  let C (u : ℕ) := W u+(W u-S u)
  let K (u : ℕ) := W u*S u+2*T u*(W u-S u)
  intro screen residual b hb even
  change ¬(0<D b ∧ D b∣N b ∧ (N b/D b).Prime ∧ Odd (N b/D b) ∧ (N b/D b).Coprime b)
  intro claim
  obtain ⟨k,u,nd,rep⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' 2 (by decide)
  subst b
  have odd := Nat.not_even_iff_odd.mp (fun he => nd (even_iff_two_dvd.mp he))
  have hk : 1≤k := by
    by_contra! h; have z : k=0 := by omega
    simp only [z,pow_zero,one_mul] at even
    exact nd (even_iff_two_dvd.mp even)
  change 0<D (2^k*u) ∧ D (2^k*u)∣N (2^k*u) ∧ _ at claim
  obtain ⟨dv,cap,pcap⟩ := screen k u odd claim.1 claim.2.1
  change (k+1)/2≤Nat.log 2 (C u+K u) at cap
  by_cases one : u=1
  · subst u
    have cu : C 1=1 := by simp [C,W,S]
    have ku : K 1=1 := by simp [K,T,W,S]
    rw [cu,ku] at cap
    norm_num at cap
    have kk : k=1 ∨ k=2 := by omega
    rcases kk with rfl|rfl <;> exact (by decide +kernel : ¬D _∣N _) claim.2.1
  · have ki : k∈Icc 1 (2*Nat.log 2 (C u+K u)) := mem_Icc.mpr ⟨hk,by omega⟩
    exact residual u odd (by have := odd.pos; omega) k ki dv pcap claim

end OMA.R_OeisA245212_conjecture_R1_H2_R1_H2_R1
