import OMAReductions.R_OeisA245212_conjecture_R1

/-! An effective search by distinct-prime rank for the odd case of A245212.
At a nonresonant prefix h the search absorbs one WHOLE bounded prime power.
A first resonance still has a bounded prefix and a bounded Euler subproduct;
only its extensions can remain unbounded at a fixed rank. The explicit
ceiling is very large. The finite test below is per rank, not one finite test
for all ranks. Credit for the original odd-input reduction: project PR 488. -/
namespace OMA.R_OeisA245212_conjecture_R1_H1_R2
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Effective dichotomy. At fixed rank the two alternatives give either a
bounded integer, or a bounded proper prefix and a finite Euler subproduct
whose largest prime divides the prefix divisor count. -/
def H1 : Prop :=
  let moment := fun h : ℕ => ∑ d ∈ h.divisors, d * d.divisors.card
  let budget := fun A : ℕ => Nat.rec (motive := fun _ => ℕ) 1
    (fun j b => max (2*b) ((2 + 2*A*2^j*b)^(j+1)))
  let ceiling := Nat.rec (motive := fun _ => ℕ → ℕ) (fun h => h) (fun k next h =>
    let r := k+1
    let A := moment h
    let D := 2 * (h * σ 0 h)
    let E := budget A r * (2*A*r*2^r + 2*σ 1 h)
    let P := max (E+1) (r*D*(σ 1 h+1)/(D-A))
    ((range (P+1)).product (range (E+1))).sup (fun b => next (h*b.1^b.2)))
  ∀ n : ℕ, 1 < n → Odd n → OeisA245212.a n = (σ 1 n : ℤ) →
    let B := ceiling n.primeFactors.card 1
    n ≤ B ∨ ∃ u v : ℕ, ∃ T : Finset ℕ, ∃ non : T.Nonempty,
      u*v = n ∧ 1 < u ∧ 1 < v ∧ u ≤ B ∧ B < n ∧ u.Coprime v ∧
      u ∣ moment u ∧ moment u < 2*(u*σ 0 u) ∧ T ⊆ v.primeFactors ∧
      moment u * (∏ p ∈ T, p) = 2*(u*σ 0 u) * (∏ p ∈ T, (p-1)) ∧ T.max' non ∣ σ 0 u

/-- A finite negative test at each specified rank. Known odd prime powers
are not part of the search. -/
def H2 : Prop :=
  let moment := fun h : ℕ => ∑ d ∈ h.divisors, d * d.divisors.card
  let budget := fun A : ℕ => Nat.rec (motive := fun _ => ℕ) 1
    (fun j b => max (2*b) ((2 + 2*A*2^j*b)^(j+1)))
  let ceiling := Nat.rec (motive := fun _ => ℕ → ℕ) (fun h => h) (fun k next h =>
    let r := k+1
    let A := moment h
    let D := 2 * (h * σ 0 h)
    let E := budget A r * (2*A*r*2^r + 2*σ 1 h)
    let P := max (E+1) (r*D*(σ 1 h+1)/(D-A))
    ((range (P+1)).product (range (E+1))).sup (fun b => next (h*b.1^b.2)))
  ∀ r : ℕ, ∀ n ∈ Icc 2 (ceiling r 1), n.primeFactors.card = r →
    Odd n → ¬IsPrimePow n → OeisA245212.a n ≠ (σ 1 n : ℤ)

/-- Resonant extensions beyond the finite test. At rank r, both the prefix
u and the largest prime in T range over finite explicit intervals. -/
def H3 : Prop :=
  let moment := fun h : ℕ => ∑ d ∈ h.divisors, d * d.divisors.card
  let budget := fun A : ℕ => Nat.rec (motive := fun _ => ℕ) 1
    (fun j b => max (2*b) ((2 + 2*A*2^j*b)^(j+1)))
  let ceiling := Nat.rec (motive := fun _ => ℕ → ℕ) (fun h => h) (fun k next h =>
    let r := k+1
    let A := moment h
    let D := 2 * (h * σ 0 h)
    let E := budget A r * (2*A*r*2^r + 2*σ 1 h)
    let P := max (E+1) (r*D*(σ 1 h+1)/(D-A))
    ((range (P+1)).product (range (E+1))).sup (fun b => next (h*b.1^b.2)))
  ∀ u v : ℕ, 1 < u → 1 < v → Odd (u*v) → u.Coprime v →
    let B := ceiling (u*v).primeFactors.card 1
    u ≤ B → B < u*v → u ∣ moment u → moment u < 2*(u*σ 0 u) →
    ∀ T ⊆ v.primeFactors, ∀ non : T.Nonempty,
      moment u * (∏ p ∈ T, p) = 2*(u*σ 0 u) * (∏ p ∈ T, (p-1)) →
      T.max' non ∣ σ 0 u → OeisA245212.a (u*v) ≠ (σ 1 (u*v) : ℤ)

theorem main : H1 → H2 → H3 → OMA.R_OeisA245212_conjecture_R1.H1 := by
  intro dichotomy finiteTest resonant n big odd composite eqn
  rcases dichotomy n big odd eqn with small | ⟨u,v,T,non,factor,u1,v1,bound,large,cop,divides,below,sub,hit,dvd⟩
  · exact finiteTest _ n (mem_Icc.mpr ⟨big,small⟩) rfl odd composite eqn
  · subst n
    exact resonant u v u1 v1 odd cop bound large divides below T sub non hit dvd eqn

end OMA.R_OeisA245212_conjecture_R1_H1_R2
