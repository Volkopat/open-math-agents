import OMAReductions.R_arxiv_2009_03418_R1_H2_R2_H1_R1
import Mathlib

/-!
Proof of hypothesis H1 of reduction arxiv-2009.03418.R1.H2.R2.H1.R1.

The mathematical development below is the Lean formalization by OpenAI
(github.com/openai/math, directory lean/OAI/Combinatorics/CompleteCrossing and its
dependencies in lean/OAI/Combinatorics/Crossing), released under the Apache License 2.0.
It is ported here with small edits (lemma renames, helper lemmas) and concatenated into
one file. The final theorem is glue code connecting the OpenAI endpoint to the step.
-/

namespace OAI

theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    (if hc : c then a hc else b hc) = a h := dif_pos h

theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    (if hc : c then a hc else b hc) = b h := dif_neg h

end OAI


namespace OAI

/-! Symmetric double and quadruple sums over unordered pairs. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

def upperPairSum {α : Type*} [Fintype α] [LinearOrder α] (f : α → α → ℝ) : ℝ :=
  ∑ i, ∑ p, if i < p then f i p else 0

theorem upperPairSum_mul {α : Type*} [Fintype α] [LinearOrder α]
    (r : ℝ) (f : α → α → ℝ) :
    upperPairSum (fun i p => r * f i p) = r * upperPairSum f := by
  simp only [upperPairSum, Finset.mul_sum, mul_ite, mul_zero]

theorem sum_symmetric_pair {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → ℝ) (hsym : ∀ i p, f p i = f i p) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ p, f i p) = 2 * upperPairSum f := by
  have hpoint (i p : α) : f i p =
      (if i < p then f i p else 0) + (if p < i then f i p else 0) := by
    rcases lt_trichotomy i p with h | rfl | h
    · simp [h, not_lt_of_ge h.le]
    · simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  have hsum : (∑ i, ∑ p, f i p) =
      upperPairSum f + ∑ i, ∑ p, if p < i then f i p else 0 := by
    calc
      _ = ∑ i, ∑ p, ((if i < p then f i p else 0) +
          (if p < i then f i p else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro p _
        exact hpoint i p
      _ = _ := by simp only [upperPairSum, Finset.sum_add_distrib]
  rw [hsum, Finset.sum_comm]
  have he : (∑ p, ∑ i, if p < i then f i p else 0) = upperPairSum f := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym]
  rw [he]
  ring

theorem sum_symmetric_quad {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → α → α → ℝ)
    (hfirst : ∀ i p k q, f p i k q = f i p k q)
    (hsecond : ∀ i p k q, f i p q k = f i p k q)
    (hdiag₁ : ∀ i k q, f i i k q = 0) (hdiag₂ : ∀ i p k, f i p k k = 0) :
    (∑ i, ∑ p, ∑ k, ∑ q, f i p k q) =
      4 * upperPairSum (fun i p => upperPairSum (f i p)) := by
  have hs (i p : α) : (∑ k, ∑ q, f p i k q) = ∑ k, ∑ q, f i p k q := by
    simp only [hfirst]
  have hd (i : α) : (∑ k, ∑ q, f i i k q) = 0 := by simp [hdiag₁]
  rw [sum_symmetric_pair _ hs hd]
  have he : (fun i p => ∑ k, ∑ q, f i p k q) =
      (fun i p => 2 * upperPairSum (f i p)) := by
    funext i p
    exact sum_symmetric_pair _ (hsecond i p) (hdiag₂ i p)
  rw [he, upperPairSum_mul]
  ring

end Paper170

end
end

end OAI

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def nodePolynomial (node : ι → ℝ) : ℝ[X] := ∏ i, (X-C (node i))

def derivativeAtNode (node : ι → ℝ) (i : ι) : ℝ :=
  (nodePolynomial node).derivative.eval (node i)

theorem derivativeAtNode_eq_prod (node : ι → ℝ) (i : ι) :
    derivativeAtNode node i = ∏ j ∈ Finset.univ.erase i, (node i-node j) := by
  unfold derivativeAtNode nodePolynomial
  change (Lagrange.nodal Finset.univ node).derivative.eval (node i) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

theorem derivativeAtNode_ne_zero (node : ι → ℝ) (hn : Function.Injective node) (i : ι) :
    derivativeAtNode node i ≠ 0 := by
  rw [derivativeAtNode_eq_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hn hij).symm

theorem node_polynomial_moment (node : ι → ℝ) (hn : Function.Injective node)
    (P : ℝ[X]) (hP : P.degree < (Fintype.card ι - 1 : ℕ)) :
    (∑ i, P.eval (node i) / derivativeAtNode node i) = 0 := by
  by_cases hcard : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  have hp' : P.degree < (Finset.univ : Finset ι).card :=
    hP.trans_le (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1)
  have he := Lagrange.coeff_eq_sum (s := Finset.univ) (v := node) hn.injOn hp'
  rw [Finset.card_univ, coeff_eq_zero_of_degree_lt hP] at he
  simpa only [Finset.card_univ, derivativeAtNode_eq_prod] using he.symm

theorem node_power_moment (node : ι → ℝ) (hn : Function.Injective node)
    (k : ℕ) (hk : k+1 < Fintype.card ι) :
    (∑ i, node i ^ k / derivativeAtNode node i) = 0 := by
  have hdeg : (X^k : ℝ[X]).degree < (Fintype.card ι - 1 : ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast (show k < Fintype.card ι-1 by omega)
  simpa only [eval_pow, eval_X] using node_polynomial_moment node hn (X^k) hdeg

end Zarankiewicz

end

end OAI

namespace OAI

/-! Polynomial spaces, interpolation weights, crossing tensors, and support evaluation. -/

section

/-! Polynomial spaces and crossing tensors for complete graphs.

These definitions contain no mathematical theorem assumptions. -/

open scoped BigOperators Classical

noncomputable section

namespace Paper170

abbrev Poly2 := MvPolynomial (Fin 2) ℝ
abbrev Poly4 := MvPolynomial (Fin 4) ℝ

def nodeWeight {ι : Type*} [Fintype ι] (node : ι → ℝ) (i : ι) : ℝ :=
  (Zarankiewicz.derivativeAtNode node i)⁻¹

def omittedNodePolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (node j))

def rectangle (a b : ℕ) : Submodule ℝ Poly2 :=
  MvPolynomial.degreesLE ℝ (Fin 2)
    (Multiset.replicate a 0 + Multiset.replicate b 1)

def box4 (d : ℕ) : Submodule ℝ Poly4 :=
  MvPolynomial.degreesLE ℝ (Fin 4) (d • (Finset.univ : Finset (Fin 4)).val)

def swapFirstPair : Poly4 →ₗ[ℝ] Poly4 :=
  (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)).toLinearMap

def swapSecondPair : Poly4 →ₗ[ℝ] Poly4 :=
  (MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)).toLinearMap

def endpointSymmetricSpace (s : ℕ) : Submodule ℝ Poly4 :=
  box4 (s - 2) ⊓ LinearMap.ker (swapFirstPair - LinearMap.id) ⊓
    LinearMap.ker (swapSecondPair - LinearMap.id)

def evalTwo (u v : ℝ) : Poly2 →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval ![u, v]).toLinearMap

def evalFour (x u y v : ℝ) : Poly4 →ₗ[ℝ] ℝ :=
  (MvPolynomial.aeval ![x, u, y, v]).toLinearMap

/-- The manuscript's one-based L_s, translated to zero-based Fin indices. -/
def evenTriangle (s : ℕ) : Finset (Fin (2 * s) × Fin (2 * s)) :=
  Finset.univ.filter fun pq =>
    (pq.1.val < s ∧ pq.2 < pq.1) ∨ (s ≤ pq.1.val ∧ pq.1 < pq.2)

abbrev EvenTriangleCoord (s : ℕ) := ↥(evenTriangle s)

def triangleEvaluation (s a b : ℕ) (node : Fin (2 * s) → ℝ) :
    rectangle a b →ₗ[ℝ] (EvenTriangleCoord s → ℝ) :=
  LinearMap.pi fun pq =>
    (evalTwo (node pq.val.1) (node pq.val.2)).comp (rectangle a b).subtype

def halfOrder {ι : Type*} (order : LinearOrder ι) (p q : ι) : ℝ :=
  letI := order
  if p < q then 1 / 2 else if q < p then -(1 / 2) else 0

def weightedPairing {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (K : ι → ι → ℝ) (A B : Poly2) : ℝ :=
  ∑ p, ∑ q, K p q * (node p - node q) /
    (Zarankiewicz.derivativeAtNode node p * Zarankiewicz.derivativeAtNode node q) *
    evalTwo (node p) (node q) A * evalTwo (node p) (node q) B

def orderPairing {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (order : LinearOrder ι) (A B : Poly2) : ℝ :=
  weightedPairing node (halfOrder order) A B

abbrev CrossingTensor (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

def chainBoundary {n : ℕ} (z : Fin n → Fin n → ℝ) (v : Fin n) : ℝ :=
  (∑ i, z i v) - ∑ p, z v p

def chainPairing {n : ℕ} (J : CrossingTensor n)
    (z z' : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q, J i p k q * z i p * z' k q

def polynomialTest {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (H : Poly4) : ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q, J i p k q * nodeWeight node i * nodeWeight node p *
    nodeWeight node k * nodeWeight node q * evalFour (node i) (node p) (node k) (node q) H

/-- Canonical orientation within each edge; the two edges remain ordered. -/
def supportedPairs {n : ℕ} (J : CrossingTensor n) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  Finset.univ.filter fun a =>
    a.1.1 < a.1.2 ∧ a.2.1 < a.2.2 ∧
    a.1.1 ≠ a.2.1 ∧ a.1.1 ≠ a.2.2 ∧
    a.1.2 ≠ a.2.1 ∧ a.1.2 ≠ a.2.2 ∧
    J a.1.1 a.1.2 a.2.1 a.2.2 ≠ 0

abbrev SupportCoord {n : ℕ} (J : CrossingTensor n) := ↥(supportedPairs J)

def supportEvaluation {n : ℕ} (s : ℕ) (node : Fin n → ℝ) (J : CrossingTensor n) :
    endpointSymmetricSpace s →ₗ[ℝ] (SupportCoord J → ℝ) :=
  LinearMap.pi fun a => (evalFour (node a.val.1.1) (node a.val.1.2)
    (node a.val.2.1) (node a.val.2.2)).comp (endpointSymmetricSpace s).subtype

/-- C=(x-y)(x-v)(u-y)(u-v), with coordinates x,u,y,v. -/
def collisionFactor : Poly4 :=
  (MvPolynomial.X 0 - MvPolynomial.X 2) *
  (MvPolynomial.X 0 - MvPolynomial.X 3) *
  (MvPolynomial.X 1 - MvPolynomial.X 2) *
  (MvPolynomial.X 1 - MvPolynomial.X 3)

/-- The complete six-difference product in the source's stated order. -/
def fullDifference : Poly4 :=
  (MvPolynomial.X 0 - MvPolynomial.X 1) *
  (MvPolynomial.X 2 - MvPolynomial.X 3) * collisionFactor

/-- Substitute x=y=t, leaving u,v as the two variables. -/
def vertexSpecialization (t : ℝ) : Poly4 →ₐ[ℝ] Poly2 :=
  MvPolynomial.aeval ![MvPolynomial.C t, MvPolynomial.X 0,
    MvPolynomial.C t, MvPolynomial.X 1]

/-- Substitute y=x, leaving x,u,v as three variables. -/
def diagonalSpecialization : Poly4 →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1,
    MvPolynomial.X 0, MvPolynomial.X 2]

def supportDiagonal {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (a : SupportCoord J) : ℝ :=
  J a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2 *
    nodeWeight node a.val.1.1 * nodeWeight node a.val.1.2 *
    nodeWeight node a.val.2.1 * nodeWeight node a.val.2.2 *
    evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1) (node a.val.2.2)
      fullDifference

def supportBilinear {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) :
    LinearMap.BilinForm ℝ (SupportCoord J → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal (supportDiagonal node J))

def weightedChain {n : ℕ} (node : Fin n → ℝ) (a b : ℕ) (i p : Fin n) : ℝ :=
  nodeWeight node i * nodeWeight node p * node i ^ a * node p ^ b

def collisionFactors : Fin 4 → Poly4 :=
  ![MvPolynomial.X 0 - MvPolynomial.X 2,
    MvPolynomial.X 0 - MvPolynomial.X 3,
    MvPolynomial.X 1 - MvPolynomial.X 2,
    MvPolynomial.X 1 - MvPolynomial.X 3]

def liftUnivariate (i : Fin 4) (U : Polynomial ℝ) : Poly4 :=
  Polynomial.aeval (MvPolynomial.X i) U

def liftBivariate (i j : Fin 4) (B : Poly2) : Poly4 :=
  MvPolynomial.aeval ![MvPolynomial.X i, MvPolynomial.X j] B

def localTestPolynomial (P : Poly4) (U V : Polynomial ℝ) (B : Poly2) : Poly4 :=
  P * (MvPolynomial.X 1 - MvPolynomial.X 3) *
    (MvPolynomial.X 1 - MvPolynomial.X 2) * (MvPolynomial.X 3 - MvPolynomial.X 0) *
    liftUnivariate 0 U * liftUnivariate 2 V * liftBivariate 1 3 B

end Paper170

end
end

end OAI

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

def Bounded (k : ℕ) (p : PolynomialModule ℝ W) : Prop :=
  ∀ n, k ≤ n → p.coeff n = 0

theorem bounded_zero (k : ℕ) : Bounded k (0 : PolynomialModule ℝ W) := by
  intro n hn
  simp

theorem bounded_mono {k l : ℕ} {p : PolynomialModule ℝ W}
    (hp : Bounded k p) (hkl : k ≤ l) : Bounded l p :=
  fun n hn => hp n (hkl.trans hn)

theorem bounded_add {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p + q) := by
  intro n hn
  simp [hp n hn, hq n hn]

theorem bounded_sub {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p - q) := by
  intro n hn
  change p.coeff n - q.coeff n = 0
  rw [hp n hn, hq n hn, sub_self]

theorem bounded_single {k n : ℕ} (hn : n < k) (w : W) :
    Bounded k (single ℝ n w) := by
  intro j hj
  simp [show n ≠ j by omega]

theorem bounded_zero_iff (p : PolynomialModule ℝ W) : Bounded 0 p ↔ p = 0 := by
  constructor
  · intro h
    ext n
    exact h n (Nat.zero_le n)
  · rintro rfl
    exact bounded_zero 0

def mulRoot (t : ℝ) (p : PolynomialModule ℝ W) : PolynomialModule ℝ W :=
  (Polynomial.X - Polynomial.C t) • p

theorem mulRoot_coeff_zero (t : ℝ) (p : PolynomialModule ℝ W) :
    (mulRoot t p).coeff 0 = -t • p.coeff 0 := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff 0 -
    (Polynomial.C t • p).coeff 0) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem mulRoot_coeff_succ (t : ℝ) (p : PolynomialModule ℝ W) (n : ℕ) :
    (mulRoot t p).coeff (n+1) = p.coeff n - t • p.coeff (n+1) := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff (n+1) -
    (Polynomial.C t • p).coeff (n+1)) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem eval_mulRoot (t u : ℝ) (p : PolynomialModule ℝ W) :
    eval u (mulRoot t p) = (u-t) • eval u p := by
  simp [mulRoot]

theorem bounded_mulRoot {k : ℕ} {p : PolynomialModule ℝ W}
    (t : ℝ) (hp : Bounded k p) : Bounded (k+1) (mulRoot t p) := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [mulRoot_coeff_succ, hp j (by omega), hp (j+1) (by omega)]
  simp

theorem eq_constant_of_bounded_one {p : PolynomialModule ℝ W} (hp : Bounded 1 p) :
    p = single ℝ 0 (p.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [hp (n+1) (by omega)]

theorem exists_mulRoot_of_eval_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded (k+1) p) (he : eval t p = 0) :
    ∃ q, Bounded k q ∧ mulRoot t q = p := by
  induction k generalizing p with
  | zero =>
    have hc := eq_constant_of_bounded_one hp
    have hz : p.coeff 0 = 0 := by
      rw [hc] at he
      simpa only [eval_single, pow_zero, one_smul] using he
    refine ⟨0, bounded_zero 0, ?_⟩
    have hp0 : p = 0 := hc.trans (by rw [hz, single_zero])
    simp [mulRoot, hp0]
  | succ k ih =>
    let q₀ := single ℝ k (p.coeff (k+1))
    have hq₀ : Bounded (k+1) q₀ := bounded_single (by omega) _
    let r := p - mulRoot t q₀
    have hr : Bounded (k+1) r := by
      intro n hn
      rcases eq_or_lt_of_le hn with rfl | hn'
      · change p.coeff (k+1) - (mulRoot t q₀).coeff (k+1) = 0
        rw [mulRoot_coeff_succ]
        simp [q₀]
      · exact bounded_sub hp (bounded_mulRoot t hq₀) n (by omega)
    have er : eval t r = 0 := by simp [r, eval_mulRoot, he]
    obtain ⟨q, hq, eq⟩ := ih r hr er
    refine ⟨q + q₀, bounded_add (bounded_mono hq (by omega)) hq₀, ?_⟩
    change (Polynomial.X - Polynomial.C t) • (q + q₀) = p
    rw [smul_add]
    change mulRoot t q + mulRoot t q₀ = p
    rw [eq]
    exact sub_add_cancel p _

theorem eq_zero_of_mulRoot_eq_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded k p) (he : mulRoot t p = 0) : p = 0 := by
  induction k with
  | zero => exact (bounded_zero_iff p).mp hp
  | succ k ih =>
    have hc : p.coeff k = 0 := by
      have hh := congrArg (fun q : PolynomialModule ℝ W => q.coeff (k+1)) he
      rw [mulRoot_coeff_succ, hp (k+1) (by omega)] at hh
      simpa using hh
    apply ih
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hn'
    · exact hc
    · exact hp n (by omega)

def mulRootLinear (t : ℝ) : PolynomialModule ℝ W →ₗ[ℝ] PolynomialModule ℝ W where
  toFun := mulRoot t
  map_add' _ _ := smul_add _ _ _
  map_smul' c p := smul_comm _ c p

variable {ι : Type*}

def constrained (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (k : ℕ) : Submodule ℝ (PolynomialModule ℝ Z) where
  carrier := {p | Bounded k p ∧ ∀ i, Z.subtype (eval (node i) p) ∈ U i}
  zero_mem' := ⟨bounded_zero k, by simp⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨bounded_add hp.1 hq.1, ?_⟩
    intro i
    simpa using (U i).add_mem (hp.2 i) (hq.2 i)
  smul_mem' := by
    intro c p hp
    refine ⟨?_, ?_⟩
    · intro n hn
      change c • p.coeff n = 0
      rw [hp.1 n hn, smul_zero]
    · intro i
      simpa using (U i).smul_mem c (hp.2 i)

variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def constrainedEval (k : ℕ) (t : ℝ) : constrained U node Z k →ₗ[ℝ] Z :=
  (eval t).comp (constrained U node Z k).subtype

def toEvalKernel (k : ℕ) (t : ℝ) :
    constrained U node Z k →ₗ[ℝ] LinearMap.ker (constrainedEval U node Z (k+1) t) where
  toFun p := ⟨⟨mulRoot t p.val, bounded_mulRoot t p.property.1, by
    intro i
    have hi := (U i).smul_mem (node i-t) (p.property.2 i)
    simpa only [eval_mulRoot, _root_.map_smul] using hi⟩, by
      change eval t (mulRoot t p.val) = 0
      simp [eval_mulRoot]⟩
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mulRootLinear t).map_add p.val q.val
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (mulRootLinear t).map_smul c p.val

theorem toEvalKernel_injective (k : ℕ) (t : ℝ) :
    Function.Injective (toEvalKernel U node Z k t) := by
  intro p q he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_mulRoot_eq_zero t k (p.val-q.val)
  · exact bounded_sub p.property.1 q.property.1
  · have hh := congrArg (fun r : LinearMap.ker (constrainedEval U node Z (k+1) t) => r.val.val) he
    change mulRoot t p.val = mulRoot t q.val at hh
    change (mulRootLinear t) (p.val-q.val) = 0
    rw [map_sub, show mulRootLinear t p.val = mulRootLinear t q.val from hh, sub_self]

theorem toEvalKernel_surjective (k : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    Function.Surjective (toEvalKernel U node Z k t) := by
  intro p
  obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero t k p.val.val p.val.property.1 p.property
  have hqU : ∀ i, Z.subtype (eval (node i) q) ∈ U i := by
    intro i
    have hp := p.val.property.2 i
    rw [← eq, eval_mulRoot] at hp
    exact (U i).smul_mem_iff (sub_ne_zero.mpr (ht i)) |>.mp hp
  refine ⟨⟨q, hq, hqU⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact eq

def evalKernelEquiv (k : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    constrained U node Z k ≃ₗ[ℝ] LinearMap.ker (constrainedEval U node Z (k+1) t) :=
  LinearEquiv.ofBijective (toEvalKernel U node Z k t)
    ⟨toEvalKernel_injective U node Z k t, toEvalKernel_surjective U node Z k t ht⟩

def constrainedCoefficients (k : ℕ) : constrained U node Z k →ₗ[ℝ] (Fin k → Z) where
  toFun p n := p.val.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constrainedCoefficients_injective (k : ℕ) :
    Function.Injective (constrainedCoefficients U node Z k) := by
  intro p q he
  apply Subtype.ext
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro n
  by_cases hn : n < k
  · exact congrFun he ⟨n, hn⟩
  · rw [p.property.1 n (by omega), q.property.1 n (by omega)]

instance constrained_finiteDimensional [FiniteDimensional ℝ W] (k : ℕ) :
    FiniteDimensional ℝ (constrained U node Z k) :=
  FiniteDimensional.of_injective (constrainedCoefficients U node Z k)
    (constrainedCoefficients_injective U node Z k)

def rankIncrement (h : ℕ) : ℕ :=
  Module.finrank ℝ (constrained U node Z (h+1)) - Module.finrank ℝ (constrained U node Z h)

theorem finrank_eval_range [FiniteDimensional ℝ W] (h : ℕ) (t : ℝ)
    (ht : ∀ i, node i ≠ t) :
    Module.finrank ℝ (LinearMap.range (constrainedEval U node Z (h+1) t)) =
      rankIncrement U node Z h := by
  have he := (evalKernelEquiv U node Z h t ht).finrank_eq
  have hr := (constrainedEval U node Z (h+1) t).finrank_range_add_finrank_ker
  unfold rankIncrement
  omega

end Zarankiewicz

end

end OAI

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ι : Type*}

theorem bounded_sum (s : Finset ι) (p : ι → PolynomialModule ℝ W) (k : ℕ)
    (hp : ∀ i ∈ s, Bounded k (p i)) : Bounded k (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero (W := W) k
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bounded_add (hp a (Finset.mem_insert_self a s))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem eq_zero_of_node_roots (node : ι → ℝ) (hn : Function.Injective node)
    (s : Finset ι) (p : PolynomialModule ℝ W) (hp : Bounded s.card p)
    (he : ∀ i ∈ s, eval (node i) p = 0) : p = 0 := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact (bounded_zero_iff p).mp hp
  | @insert a s ha ih =>
    have hp' : Bounded (s.card+1) p := by simpa [Finset.card_insert_of_notMem ha] using hp
    obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero (node a) s.card p hp'
      (he a (Finset.mem_insert_self a s))
    have hqe : ∀ i ∈ s, eval (node i) q = 0 := by
      intro i hi
      have h := he i (Finset.mem_insert_of_mem hi)
      rw [← eq, eval_mulRoot] at h
      have hia : node i - node a ≠ 0 := sub_ne_zero.mpr (fun e => ha (hn e ▸ hi))
      exact (smul_eq_zero.mp h).resolve_left hia
    have hq0 := ih q hq hqe
    rw [← eq, hq0]
    simp [mulRoot]

variable [Fintype ι]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def nodeEvaluation : constrained U node Z (Fintype.card ι) →ₗ[ℝ] (∀ i, ↥(U i ⊓ Z)) where
  toFun p i := ⟨Z.subtype (eval (node i) p.val), p.property.2 i,
    (eval (node i) p.val).property⟩
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

theorem nodeEvaluation_injective (hn : Function.Injective node) :
    Function.Injective (nodeEvaluation U node Z) := by
  intro p q he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_node_roots node hn Finset.univ (p.val-q.val)
  · simpa using bounded_sub p.property.1 q.property.1
  · intro i hi
    rw [map_sub, sub_eq_zero]
    apply Subtype.ext
    exact congrArg (fun x : ↥(U i ⊓ Z) => x.val) (congrFun he i)

def vectorInterpolant (z : ∀ i, ↥(U i ⊓ Z)) : PolynomialModule ℝ Z :=
  by
    classical
    exact ∑ i, Lagrange.basis Finset.univ node i • single ℝ 0 ⟨(z i).val, (z i).property.2⟩

theorem eval_vectorInterpolant (hn : Function.Injective node) (z : ∀ i, ↥(U i ⊓ Z)) (i : ι) :
    eval (node i) (vectorInterpolant U node Z z) = ⟨(z i).val, (z i).property.2⟩ := by
  classical
  simp only [vectorInterpolant, map_sum, eval_smul, eval_single, pow_zero, one_smul]
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_basis_self hn.injOn (Finset.mem_univ i), one_smul]
  · intro j hj hji
    rw [Lagrange.eval_basis_of_ne hji (Finset.mem_univ i), zero_smul]
  · simp

theorem bounded_vectorInterpolant (hn : Function.Injective node) (z : ∀ i, ↥(U i ⊓ Z)) :
    Bounded (Fintype.card ι) (vectorInterpolant U node Z z) := by
  classical
  apply bounded_sum
  intro i hi n hge
  rw [smul_single_apply]
  simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
  · exact zero_smul _ _
  · have hc : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [Lagrange.natDegree_basis hn.injOn hi, Finset.card_univ]
    omega

theorem nodeEvaluation_surjective (hn : Function.Injective node) :
    Function.Surjective (nodeEvaluation U node Z) := by
  intro z
  have hu : ∀ i, Z.subtype (eval (node i) (vectorInterpolant U node Z z)) ∈ U i := by
    intro i
    rw [eval_vectorInterpolant U node Z hn z i]
    exact (z i).property.1
  refine ⟨⟨vectorInterpolant U node Z z, bounded_vectorInterpolant U node Z hn z, hu⟩, ?_⟩
  funext i
  apply Subtype.ext
  exact congrArg Z.subtype (eval_vectorInterpolant U node Z hn z i)

def nodeEvaluationEquiv (hn : Function.Injective node) :
    constrained U node Z (Fintype.card ι) ≃ₗ[ℝ] (∀ i, ↥(U i ⊓ Z)) :=
  LinearEquiv.ofBijective (nodeEvaluation U node Z)
    ⟨nodeEvaluation_injective U node Z hn, nodeEvaluation_surjective U node Z hn⟩

theorem finrank_constrained_zero
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    : Module.finrank ℝ (constrained U node Z 0) = 0 := by
  have hz : constrained U node Z 0 = ⊥ := by
    apply le_antisymm _ bot_le
    intro p hp
    exact (Submodule.mem_bot ℝ).mpr ((bounded_zero_iff p).mp hp.1)
  rw [hz]
  simp

theorem constrained_finrank_mono
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    [FiniteDimensional ℝ W] :
    Monotone (fun k => Module.finrank ℝ (constrained U node Z k)) := by
  intro k l hkl
  exact Submodule.finrank_mono (fun p hp => ⟨bounded_mono hp.1 hkl, hp.2⟩)

theorem sum_rankIncrement [FiniteDimensional ℝ W] (m : ℕ) :
    ∑ h ∈ Finset.range m, rankIncrement U node Z h =
      Module.finrank ℝ (constrained U node Z m) := by
  unfold rankIncrement
  rw [Finset.sum_range_tsub (constrained_finrank_mono U node Z), finrank_constrained_zero,
    Nat.sub_zero]

theorem interpolation_identity [FiniteDimensional ℝ W] (hn : Function.Injective node) :
    ∑ h ∈ Finset.range (Fintype.card ι), rankIncrement U node Z h =
      ∑ i, Module.finrank ℝ ↥(U i ⊓ Z) := by
  rw [sum_rankIncrement, (nodeEvaluationEquiv U node Z hn).finrank_eq,
    Module.finrank_pi_fintype]

end Zarankiewicz

end

end OAI

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

abbrev BiPoly := PolynomialModule ℝ (PolynomialModule ℝ ℝ)

def biCoeff (p : BiPoly) (a b : ℕ) : ℝ := (p.coeff a).coeff b

def biEval (u v : ℝ) : BiPoly →ₗ[ℝ] ℝ := (eval v).comp (eval u)

def BiBounded (r s : ℕ) (p : BiPoly) : Prop :=
  Bounded r p ∧ ∀ a, Bounded s (p.coeff a)

def flattenBi : BiPoly ≃ₗ[ℝ] (ℕ × ℕ →₀ ℝ) :=
  ((coeffLinearEquiv ℝ ℝ).trans
    (Finsupp.mapRange.linearEquiv (coeffLinearEquiv ℝ ℝ))).trans
    (Finsupp.curryLinearEquiv ℝ).symm

theorem flattenBi_apply (p : BiPoly) (a b : ℕ) : flattenBi p (a,b) = biCoeff p a b := rfl

def swapBi : BiPoly ≃ₗ[ℝ] BiPoly :=
  (flattenBi.trans (Finsupp.mapDomain.linearEquiv ℝ ℝ (Equiv.prodComm ℕ ℕ))).trans
    flattenBi.symm

theorem biCoeff_swap (p : BiPoly) (a b : ℕ) : biCoeff (swapBi p) a b = biCoeff p b a := by
  rw [← flattenBi_apply]
  change flattenBi (flattenBi.symm _) (a,b) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_equiv_apply (flattenBi p) (a,b)

theorem bi_ext {p q : BiPoly} (h : ∀ a b, biCoeff p a b = biCoeff q a b) : p = q := by
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro a
  apply PolynomialModule.ext
  apply Finsupp.ext
  exact h a

theorem swapBi_swapBi (p : BiPoly) : swapBi (swapBi p) = p := by
  apply bi_ext
  intro a b
  rw [biCoeff_swap, biCoeff_swap]

theorem swapBi_single (a b : ℕ) (c : ℝ) :
    swapBi (single ℝ a (single ℝ b c)) = single ℝ b (single ℝ a c) := by
  apply bi_ext
  intro i j
  rw [biCoeff_swap]
  simp [biCoeff, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem biEval_swap (p : BiPoly) (u v : ℝ) : biEval u v (swapBi p) = biEval v u p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single a q =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [single_add, map_add, hp, hq]
    | single b c =>
      rw [swapBi_single]
      simp [biEval, eval_single, smul_eq_mul]
      ring

theorem biBounded_swap {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) :
    BiBounded s r (swapBi p) := by
  constructor
  · intro a ha
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro b
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    exact hp.2 b a ha
  · intro a b hb
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    simp [biCoeff, hp.1 b hb]

def boundedSpace (k : ℕ) : Submodule ℝ (PolynomialModule ℝ ℝ) where
  carrier := {p | Bounded k p}
  zero_mem' := bounded_zero k
  add_mem' := bounded_add
  smul_mem' := by
    intro c p hp n hn
    change c • p.coeff n = 0
    rw [hp n hn, smul_zero]

theorem coefficients_of_mulRoot {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Z : Submodule ℝ W) (t : ℝ) (k : ℕ) (q : PolynomialModule ℝ W)
    (hq : Bounded k q) (hc : ∀ n, (mulRoot t q).coeff n ∈ Z) :
    ∀ n, q.coeff n ∈ Z := by
  have aux : ∀ d n, k-n = d → q.coeff n ∈ Z := by
    intro d
    induction d with
    | zero =>
      intro n hn
      rw [hq n (by omega)]
      exact Z.zero_mem
    | succ d ih =>
      intro n hn
      have hh := Z.add_mem (hc (n+1)) (Z.smul_mem t (ih (n+1) (by omega)))
      simpa only [mulRoot_coeff_succ, sub_add_cancel] using hh
  intro n
  exact aux (k-n) n rfl

theorem bi_factor_row (r s : ℕ) (p : BiPoly) (hp : BiBounded (r+1) s p)
    (t : ℝ) (hz : eval t p = 0) :
    ∃ q : BiPoly, BiBounded r s q ∧ mulRoot t q = p := by
  obtain ⟨q, hq, he⟩ := exists_mulRoot_of_eval_zero t r p hp.1 hz
  refine ⟨q, ⟨hq, ?_⟩, he⟩
  apply coefficients_of_mulRoot (boundedSpace s) t r q hq
  intro n
  rw [he]
  exact hp.2 n

theorem biEval_mulRoot (t u v : ℝ) (p : BiPoly) :
    biEval u v (mulRoot t p) = (u-t) * biEval u v p := by
  change eval v (eval u (mulRoot t p)) = _
  rw [eval_mulRoot, _root_.map_smul]
  rfl

theorem bounded_eval_outer {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) (u : ℝ) :
    Bounded s (eval u p) := by
  change eval u p ∈ boundedSpace s
  change p.coeff.sum (fun a c => u^a • c) ∈ boundedSpace s
  apply Submodule.sum_mem
  intro a ha
  exact (boundedSpace s).smul_mem (u^a) (hp.2 a)

end Zarankiewicz

end

end OAI

namespace OAI

namespace Zarankiewicz
open Finset

def lowerTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.2 < z.1)

def upperTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc (s+2) (2*s+1)) ×ˢ (Icc (s+2) (2*s+1))).filter (fun z => z.1 < z.2)

def twoTriangle (s : ℕ) : Finset (ℕ × ℕ) := lowerTriangle s ∪ upperTriangle s

theorem mem_lowerTriangle (s p q : ℕ) :
    (p,q) ∈ lowerTriangle s ↔ 1 ≤ q ∧ q < p ∧ p ≤ s+1 := by
  simp only [lowerTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_upperTriangle (s p q : ℕ) :
    (p,q) ∈ upperTriangle s ↔ s+1 < p ∧ p < q ∧ q ≤ 2*s+1 := by
  simp only [upperTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_twoTriangle (s p q : ℕ) :
    (p,q) ∈ twoTriangle s ↔
      (1 ≤ q ∧ q < p ∧ p ≤ s+1) ∨ (s+1 < p ∧ p < q ∧ q ≤ 2*s+1) := by
  rw [twoTriangle, mem_union, mem_lowerTriangle, mem_upperTriangle]

theorem disjoint_triangles (s : ℕ) : Disjoint (lowerTriangle s) (upperTriangle s) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨p,q⟩ hp hq
  rw [mem_lowerTriangle] at hp
  rw [mem_upperTriangle] at hq
  omega

theorem card_lowerTriangle (s : ℕ) : (lowerTriangle s).card = (s+1).choose 2 := by
  have hswap : (lowerTriangle s).card =
      (((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.1 < z.2)).card :=
    Finset.card_equiv (Equiv.prodComm ℕ ℕ) (by
      intro z
      simp [lowerTriangle, and_comm, and_left_comm, and_assoc])
  rw [hswap, Finset.card_product_filter_lt]
  simp

theorem card_upperTriangle (s : ℕ) : (upperTriangle s).card = s.choose 2 := by
  have h := Finset.card_product_filter_lt (s := Icc (s+2) (2*s+1))
  have hc : (Icc (s+2) (2*s+1)).card = s := by simp; omega
  simpa [upperTriangle, hc] using h

theorem adjacent_choose_two (s : ℕ) : (s+1).choose 2 + s.choose 2 = s*s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ha : (s+2).choose 2 = (s+1).choose 2 + (s+1) := by
      calc
        (s+2).choose 2 = (s+1).choose 1 + (s+1).choose 2 := Nat.choose_succ_succ (s+1) 1
        _ = (s+1).choose 2 + (s+1) := by rw [Nat.choose_one_right]; omega
    have hb : (s+1).choose 2 = s.choose 2 + s := by
      simpa [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.choose_succ_succ s 1)
    have : s+1+1 = s+2 := by omega
    rw [this, ha]
    nlinarith

theorem card_twoTriangle (s : ℕ) : (twoTriangle s).card = s*s := by
  rw [twoTriangle, card_union_of_disjoint (disjoint_triangles s), card_lowerTriangle,
    card_upperTriangle, adjacent_choose_two]

def triangleRelabel (s k : ℕ) : ℕ := if k ≤ s then s+1+k else k-s+1

theorem triangleRelabel_injective_on (s : ℕ) :
    Set.InjOn (triangleRelabel s) (Set.Icc 1 (2*s-1)) := by
  intro p hp q hq he
  simp only [Set.mem_Icc] at hp hq
  unfold triangleRelabel at he
  split_ifs at he <;> omega

theorem triangleRelabel_range (s k : ℕ) (hk : k ∈ Icc 1 (2*s-1)) :
    triangleRelabel s k ∈ Icc 1 (2*s+1) ∧
      triangleRelabel s k ≠ s+1 ∧ triangleRelabel s k ≠ 1 := by
  simp only [mem_Icc] at hk ⊢
  unfold triangleRelabel
  split_ifs <;> omega

theorem relabel_twoTriangle (s : ℕ) (hs : 1 ≤ s) (p q : ℕ)
    (hpq : (p,q) ∈ twoTriangle (s-1)) :
    (triangleRelabel s q, triangleRelabel s p) ∈ twoTriangle s ∧
      triangleRelabel s q ≠ s+1 ∧ triangleRelabel s p ≠ 1 := by
  rw [mem_twoTriangle] at hpq ⊢
  unfold triangleRelabel
  split_ifs <;> omega

end Zarankiewicz

end OAI

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open Finset

theorem eq_zero_of_roots_injOn {W : Type*} [AddCommGroup W] [Module ℝ W]
    (node : ℕ → ℝ) (S : Finset ℕ) (hn : Set.InjOn node (S : Set ℕ))
    (p : PolynomialModule ℝ W) (hp : Bounded S.card p)
    (he : ∀ i ∈ S, eval (node i) p = 0) : p = 0 := by
  let x : S → ℝ := fun i => node i.val
  have hx : Function.Injective x := by
    intro i j hij
    exact Subtype.ext (hn i.property j.property hij)
  apply eq_zero_of_node_roots x hx Finset.univ p
  · simpa using hp
  · intro i hi
    exact he i.val i.property

theorem twoTriangle_unisolvent (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p : BiPoly)
    (hp : BiBounded s s p)
    (hv : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = 0) : p = 0 := by
  induction s generalizing node p with
  | zero => exact (bounded_zero_iff p).mp hp.1
  | succ k ih =>
    have node_ne : ∀ a b, a ∈ Icc 1 (2*(k+1)+1) → b ∈ Icc 1 (2*(k+1)+1) →
        a ≠ b → node a ≠ node b := by
      intro a b ha hb hab he
      exact hab (hn (by simpa only [mem_Icc, Set.mem_Icc] using ha)
        (by simpa only [mem_Icc, Set.mem_Icc] using hb) he)

    have hrow : eval (node (k+2)) p = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 1 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer hp (node (k+2))
      · intro q hq
        apply hv (k+2) q
        rw [mem_twoTriangle]
        simp only [mem_Icc] at hq
        left
        omega
    obtain ⟨p₁, hp₁, he₁⟩ := bi_factor_row k (k+1) p hp (node (k+2)) hrow

    have hcol : eval (node 1) (swapBi p₁) = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 2 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer (biBounded_swap hp₁) (node 1)
      · intro a ha
        change biEval (node 1) (node a) (swapBi p₁) = 0
        rw [biEval_swap]
        have hpa : biEval (node a) (node 1) p = 0 := by
          apply hv
          rw [mem_twoTriangle]
          simp only [mem_Icc] at ha
          left
          omega
        rw [← he₁, biEval_mulRoot] at hpa
        apply (mul_eq_zero.mp hpa).resolve_left
        apply sub_ne_zero.mpr
        apply node_ne a (k+2) <;> simp only [mem_Icc] at * <;> omega
    obtain ⟨r, hr, her⟩ := bi_factor_row k k (swapBi p₁) (biBounded_swap hp₁) (node 1) hcol

    let y : ℕ → ℝ := fun i => node (triangleRelabel (k+1) i)
    have hyrange : ∀ a, a ∈ Icc 1 (2*k+1) →
        triangleRelabel (k+1) a ∈ Icc 1 (2*(k+1)+1) ∧
          triangleRelabel (k+1) a ≠ k+2 ∧ triangleRelabel (k+1) a ≠ 1 := by
      intro a ha
      simpa only [show k+1+1 = k+2 from rfl] using
        triangleRelabel_range (k+1) a (by simp only [mem_Icc] at *; omega)
    have hyn : Set.InjOn y (Set.Icc 1 (2*k+1)) := by
      intro a ha b hb he
      have ha' : a ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using ha
      have hb' : b ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using hb
      apply triangleRelabel_injective_on (k+1)
      · simp only [Set.mem_Icc] at *
        omega
      · simp only [Set.mem_Icc] at *
        omega
      · exact hn (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange a ha').1)
          (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange b hb').1) he
    have hrv : ∀ a b, (a,b) ∈ twoTriangle k → biEval (y a) (y b) r = 0 := by
      intro a b hab
      have ha : a ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hb : b ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hpattern := relabel_twoTriangle (k+1) (by omega) a b (by simpa using hab)
      have hval := hv (triangleRelabel (k+1) b) (triangleRelabel (k+1) a) hpattern.1
      rw [← he₁, biEval_mulRoot] at hval
      have hfirst : node (triangleRelabel (k+1) b) - node (k+2) ≠ 0 :=
        sub_ne_zero.mpr (node_ne _ _ (hyrange b hb).1 (by simp) (hyrange b hb).2.1)
      have hp₁val := (mul_eq_zero.mp hval).resolve_left hfirst
      have hswap : p₁ = swapBi (mulRoot (node 1) r) := by rw [her, swapBi_swapBi]
      rw [hswap, biEval_swap, biEval_mulRoot] at hp₁val
      apply (mul_eq_zero.mp hp₁val).resolve_left
      exact sub_ne_zero.mpr (node_ne _ _ (hyrange a ha).1 (by simp) (hyrange a ha).2.2)
    have hr0 := ih y hyn r hr hrv
    have hp₁0 : p₁ = 0 := by
      apply swapBi.injective
      rw [← her, hr0]
      simp [mulRoot]
    rw [← he₁, hp₁0]
    simp [mulRoot]

theorem twoTriangle_evaluation_injective (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p q : BiPoly)
    (hp : BiBounded s s p) (hq : BiBounded s s q)
    (he : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = biEval (node a) (node b) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply twoTriangle_unisolvent s node hn (p-q)
  · refine ⟨bounded_sub hp.1 hq.1, ?_⟩
    intro a
    exact bounded_sub (hp.2 a) (hq.2 a)
  · intro a b hab
    rw [map_sub, he a b hab, sub_self]

end Zarankiewicz

end

end OAI

namespace OAI

/-! Bivariate interpolation degrees, spaces, pairings, and polynomial tests. -/

section

/-! Degree conventions and interpolation weights.
 -/

open scoped BigOperators
noncomputable section

namespace Paper170

theorem rectangle_membership (a b : ℕ) (P : Poly2) :
    P ∈ rectangle a b ↔ P.degreeOf 0 ≤ a ∧ P.degreeOf 1 ≤ b := by
  change P.degrees ≤ _ ↔ _
  rw [Multiset.le_iff_count]
  simp [← MvPolynomial.degreeOf_def, Fin.forall_fin_two, Multiset.count_replicate]

theorem box4_membership (d : ℕ) (P : Poly4) :
    P ∈ box4 d ↔ ∀ i, P.degreeOf i ≤ d := by
  change P.degrees ≤ _ ↔ _
  rw [Multiset.le_iff_count]
  simp [← MvPolynomial.degreeOf_def]

theorem symmetric_space_membership (s : ℕ) (P : Poly4) :
    P ∈ endpointSymmetricSpace s ↔
      (∀ i, P.degreeOf i ≤ s - 2) ∧ swapFirstPair P = P ∧ swapSecondPair P = P := by
  simp [endpointSymmetricSpace, box4_membership, sub_eq_zero, and_assoc]

theorem derivative_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) :
    Zarankiewicz.derivativeAtNode node i = ∏ j ∈ Finset.univ.erase i, (node i - node j) :=
  Zarankiewicz.derivativeAtNode_eq_prod node i

theorem weight_nonzero {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (i : ι) : nodeWeight node i ≠ 0 := by
  classical
  exact inv_ne_zero (Zarankiewicz.derivativeAtNode_ne_zero node hn i)

theorem interpolation_weights {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (A : Polynomial ℝ)
    (hA : A.degree < (Fintype.card ι - 1 : ℕ)) :
    (∑ i, A.eval (node i) / Zarankiewicz.derivativeAtNode node i) = 0 := by
  classical
  exact Zarankiewicz.node_polynomial_moment node hn A hA

theorem omitted_node_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) (i p : ι) (hip : i ≠ p) :
    (node p - node i) * nodeWeight node p =
      ((omittedNodePolynomial node i).derivative.eval (node p))⁻¹ := by
  have hF : Zarankiewicz.nodePolynomial node =
      (Polynomial.X - Polynomial.C (node i)) * omittedNodePolynomial node i :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)
  have hzero : (omittedNodePolynomial node i).eval (node p) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hip.symm, Finset.mem_univ p⟩)
  have hd : Zarankiewicz.derivativeAtNode node p = (node p - node i) *
      (omittedNodePolynomial node i).derivative.eval (node p) := by
    rw [Zarankiewicz.derivativeAtNode, hF, Polynomial.derivative_mul]
    simp [hzero]
  have hdiff : node p - node i ≠ 0 := sub_ne_zero.mpr (hn.ne hip.symm)
  rw [nodeWeight, hd, mul_inv, ← mul_assoc, mul_inv_cancel₀ hdiff, one_mul]

theorem weighted_chain_boundary {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (a b : ℕ) (ha : a + 1 < n) (hb : b + 1 < n) :
    ∀ v, chainBoundary (weightedChain node a b) v = 0 := by
  have hsum (k : ℕ) (hk : k + 1 < n) : ∑ i, nodeWeight node i * node i ^ k = 0 := by
    simpa only [nodeWeight, div_eq_mul_inv, mul_comm] using
      Zarankiewicz.node_power_moment node hn k (by simpa using hk)
  have hz (i p : Fin n) : weightedChain node a b i p =
      (nodeWeight node i * node i ^ a) * (nodeWeight node p * node p ^ b) := by
    unfold weightedChain
    ring
  intro v
  simp only [chainBoundary, hz, ← Finset.sum_mul, ← Finset.mul_sum, hsum a ha, hsum b hb,
    zero_mul, mul_zero, sub_self]

end Paper170

end
end

section

/-! Separate degree bounds for the local four-variable test polynomial. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem degreeOf_mul_bound {i : Fin 4} {P Q : Poly4} {a b : ℕ}
    (hP : P.degreeOf i ≤ a) (hQ : Q.degreeOf i ≤ b) : (P*Q).degreeOf i ≤ a+b :=
  (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add hP hQ)

theorem degreeOf_liftUnivariate (i k : Fin 4) (U : Polynomial ℝ) :
    (liftUnivariate i U).degreeOf k ≤ if k=i then U.natDegree else 0 := by
  classical
  unfold liftUnivariate
  conv_lhs => rw [← Polynomial.sum_monomial_eq U, Polynomial.sum, map_sum]
  apply (MvPolynomial.degreeOf_sum_le k _ _).trans
  apply Finset.sup_le
  intro a ha
  rw [Polynomial.aeval_monomial]
  change (MvPolynomial.C (U.coeff a) * MvPolynomial.X i ^ a).degreeOf k ≤ _
  apply (MvPolynomial.degreeOf_C_mul_le _ k _).trans
  by_cases h : k=i
  · subst k
    simpa using Polynomial.le_natDegree_of_mem_supp a ha
  · simp only [ite_eq_right h, MvPolynomial.degreeOf_X_pow_of_ne a h]
    exact Nat.le_refl 0

theorem liftBivariate_eq_rename (i j : Fin 4) (B : Poly2) :
    liftBivariate i j B = MvPolynomial.rename ![i,j] B := by
  have hf : (MvPolynomial.X ∘ (![i,j] : Fin 2 → Fin 4)) =
      (![MvPolynomial.X i, MvPolynomial.X j] : Fin 2 → Poly4) := by
    funext k
    fin_cases k <;> rfl
  simp only [liftBivariate, MvPolynomial.rename_eq_aeval, hf]

theorem degreeOf_rename_zero {σ : Type*} (f : σ → Fin 4) (B : MvPolynomial σ ℝ)
    (k : Fin 4) (hk : ∀i, f i ≠ k) : (MvPolynomial.rename f B).degreeOf k = 0 := by
  by_contra h
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename f B
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact hk i hi

theorem degreeOf_liftBivariate13 (B : Poly2) (k : Fin 4) :
    (liftBivariate 1 3 B).degreeOf k = ![0,B.degreeOf 0,0,B.degreeOf 1] k := by
  have hi : Function.Injective (![1,3] : Fin 2 → Fin 4) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
  rw [liftBivariate_eq_rename]
  fin_cases k
  · exact degreeOf_rename_zero _ B 0 (by intro i; fin_cases i <;> decide)
  · exact MvPolynomial.degreeOf_rename_of_injective hi 0
  · exact degreeOf_rename_zero _ B 2 (by intro i; fin_cases i <;> decide)
  · exact MvPolynomial.degreeOf_rename_of_injective hi 1

theorem degreeOf_difference_bound (i j k : Fin 4) :
    (MvPolynomial.X i - MvPolynomial.X j : Poly4).degreeOf k ≤
      max (if k=i then 1 else 0) (if k=j then 1 else 0) := by
  simpa only [MvPolynomial.degreeOf_X] using
    MvPolynomial.degreeOf_sub_le k (MvPolynomial.X i : Poly4) (MvPolynomial.X j)

theorem local_test_degree (s : ℕ) (hs : 2 ≤ s) (P : Poly4)
    (hP : P ∈ endpointSymmetricSpace s) (U V : Polynomial ℝ)
    (hU : U.natDegree ≤ s) (hV : V.natDegree ≤ s) (B : Poly2)
    (hB : B ∈ rectangle (s-1) (s-1)) :
    localTestPolynomial P U V B ∈ box4 (2*s-1) := by
  apply (box4_membership _ _).mpr
  intro k
  have hP := ((symmetric_space_membership s P).mp hP).1 k
  have hB := (rectangle_membership _ _ B).mp hB
  have h := degreeOf_mul_bound
    (degreeOf_mul_bound
      (degreeOf_mul_bound
        (degreeOf_mul_bound
          (degreeOf_mul_bound
            (degreeOf_mul_bound hP (degreeOf_difference_bound 1 3 k))
            (degreeOf_difference_bound 1 2 k))
          (degreeOf_difference_bound 3 0 k))
        (degreeOf_liftUnivariate 0 k U))
      (degreeOf_liftUnivariate 2 k V))
    (Nat.le_of_eq (degreeOf_liftBivariate13 B k))
  change (localTestPolynomial P U V B).degreeOf k ≤ _ at h
  fin_cases k <;> norm_num [Fin.ext_iff] at h ⊢ <;> omega

end Paper170

end
end

section

/-! Interpolation moments remove row and column perturbations from the order pairing. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalTwo_monomial (u v : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    evalTwo u v (MvPolynomial.monomial m c) = c*(u^m 0*v^m 1) := by
  simp only [evalTwo, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]
  · intro i
    simp

theorem weighted_evalTwo_second_zero {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (u : ℝ) (P : Poly2)
    (hP : P.degreeOf 1 + 1 < Fintype.card ι) :
    (∑q, evalTwo u (node q) P / Zarankiewicz.derivativeAtNode node q) = 0 := by
  classical
  rw [P.as_sum]
  simp only [map_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdeg := MvPolynomial.le_degreeOf_of_mem_support 1 hm
  have hz := Zarankiewicz.node_power_moment node hn (m 1) (by omega)
  calc
    (∑q, evalTwo u (node q) (MvPolynomial.monomial m (P.coeff m)) /
        Zarankiewicz.derivativeAtNode node q) =
      (P.coeff m*u^m 0) * ∑q, node q^m 1 / Zarankiewicz.derivativeAtNode node q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [evalTwo_monomial]
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem weighted_evalTwo_first_zero {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (v : ℝ) (P : Poly2)
    (hP : P.degreeOf 0 + 1 < Fintype.card ι) :
    (∑p, evalTwo (node p) v P / Zarankiewicz.derivativeAtNode node p) = 0 := by
  classical
  rw [P.as_sum]
  simp only [map_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdeg := MvPolynomial.le_degreeOf_of_mem_support 0 hm
  have hz := Zarankiewicz.node_power_moment node hn (m 0) (by omega)
  calc
    (∑p, evalTwo (node p) v (MvPolynomial.monomial m (P.coeff m)) /
        Zarankiewicz.derivativeAtNode node p) =
      (P.coeff m*v^m 1) * ∑p, node p^m 0 / Zarankiewicz.derivativeAtNode node p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [evalTwo_monomial]
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem weightedPairing_add {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (K L : ι → ι → ℝ) (A B : Poly2) :
    weightedPairing node (fun p q => K p q+L p q) A B =
      weightedPairing node K A B + weightedPairing node L A B := by
  simp [weightedPairing, add_mul, add_div, Finset.sum_add_distrib]

theorem evalTwo_difference_mul (u v : ℝ) (A B : Poly2) :
    evalTwo u v ((MvPolynomial.X 0-MvPolynomial.X 1)*A*B) =
      (u-v)*evalTwo u v A*evalTwo u v B := by
  simp [evalTwo]

theorem pairing_row_column_invariant {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (K : ι → ι → ℝ)
    (r c : ι → ℝ) (A B : Poly2)
    (hA : A ∈ rectangle (s-1) (s-2))
    (hB : B ∈ rectangle (s-2) (s-1)) :
    weightedPairing node (fun p q => K p q+r p+c q) A B =
      weightedPairing node K A B := by
  classical
  let C : Poly2 := (MvPolynomial.X 0-MvPolynomial.X 1)*A*B
  have hC (i : Fin 2) : C.degreeOf i + 1 < Fintype.card ι := by
    have hA := (rectangle_membership _ _ A).mp hA
    have hB := (rectangle_membership _ _ B).mp hB
    have h1 := MvPolynomial.degreeOf_mul_le i ((MvPolynomial.X 0-MvPolynomial.X 1)*A) B
    have h2 := MvPolynomial.degreeOf_mul_le i (MvPolynomial.X 0-MvPolynomial.X 1) A
    have h3 := MvPolynomial.degreeOf_sub_le i (MvPolynomial.X 0 : Poly2) (MvPolynomial.X 1)
    change C.degreeOf i ≤ _ at h1
    rw [hc]
    fin_cases i <;> norm_num [MvPolynomial.degreeOf_X, Fin.ext_iff] at h1 h2 h3 ⊢ <;> omega
  have hr : weightedPairing node (fun p _ => r p) A B = 0 := by
    unfold weightedPairing
    apply Finset.sum_eq_zero
    intro p _
    calc
      (∑q, r p*(node p-node q)/
        (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q)*
        evalTwo (node p) (node q) A*evalTwo (node p) (node q) B) =
        (r p/Zarankiewicz.derivativeAtNode node p) *
        ∑q, evalTwo (node p) (node q) C/Zarankiewicz.derivativeAtNode node q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          rw [show evalTwo (node p) (node q) C = _ from evalTwo_difference_mul _ _ A B]
          ring
      _ = 0 := by rw [weighted_evalTwo_second_zero node hn _ C (hC 1), mul_zero]
  have hcol : weightedPairing node (fun _ q => c q) A B = 0 := by
    unfold weightedPairing
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    calc
      (∑p, c q*(node p-node q)/
        (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q)*
        evalTwo (node p) (node q) A*evalTwo (node p) (node q) B) =
        (c q/Zarankiewicz.derivativeAtNode node q) *
        ∑p, evalTwo (node p) (node q) C/Zarankiewicz.derivativeAtNode node p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          rw [show evalTwo (node p) (node q) C = _ from evalTwo_difference_mul _ _ A B]
          ring
      _ = 0 := by rw [weighted_evalTwo_first_zero node hn _ C (hC 0), mul_zero]
  rw [weightedPairing_add, weightedPairing_add, hr, hcol, add_zero, add_zero]

end Paper170

end
end

section

/-! Coefficient spaces for the even-node interpolation argument. -/
noncomputable section
open scoped BigOperators
open Module
namespace Paper170

def exponentPair : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ where
  toFun m := (m 0, m 1)
  invFun p := Finsupp.equivFunOnFinite.symm ![p.1, p.2]
  left_inv m := by
    ext i
    fin_cases i <;> simp
  right_inv p := by simp

@[simp] theorem exponentPair_symm_zero (a b : ℕ) : exponentPair.symm (a,b) 0 = a := rfl
@[simp] theorem exponentPair_symm_one (a b : ℕ) : exponentPair.symm (a,b) 1 = b := rfl

theorem rectangle_eq_restrictSupport (a b : ℕ) :
    rectangle a b = MvPolynomial.restrictSupport ℝ {m | m 0 ≤ a ∧ m 1 ≤ b} := by
  ext P
  rw [rectangle_membership, MvPolynomial.mem_restrictSupport_iff]
  simp only [MvPolynomial.degreeOf_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  exact ⟨fun h m hm => ⟨h.1 m hm, h.2 m hm⟩,
    fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩⟩

def rectangleExponentEquiv (a b : ℕ) :
    {m : Fin 2 →₀ ℕ // m 0 ≤ a ∧ m 1 ≤ b} ≃ Fin (a+1) × Fin (b+1) where
  toFun m := (⟨m.val 0, by omega⟩, ⟨m.val 1, by omega⟩)
  invFun p := ⟨exponentPair.symm (p.1.val,p.2.val), by simp; omega⟩
  left_inv m := by
    apply Subtype.ext
    exact exponentPair.symm_apply_apply m.val
  right_inv p := by rfl

def rectangleBasis (a b : ℕ) : Basis (Fin (a+1) × Fin (b+1)) ℝ (rectangle a b) :=
  ((MvPolynomial.basisRestrictSupport ℝ _).reindex (rectangleExponentEquiv a b)).map
    (LinearEquiv.ofEq _ _ (rectangle_eq_restrictSupport a b).symm)

theorem rectangle_finite (a b : ℕ) : FiniteDimensional ℝ (rectangle a b) :=
  Module.Finite.of_basis (rectangleBasis a b)

theorem rectangle_dimension (a b : ℕ) :
    Module.finrank ℝ (rectangle a b) = (a+1)*(b+1) := by
  rw [Module.finrank_eq_card_basis (rectangleBasis a b)]
  simp

/-- The coefficient-preserving bridge to the existing bivariate interpolation library. -/
def toBiPolynomial : Poly2 ≃ₗ[ℝ] Zarankiewicz.BiPoly :=
  ((MvPolynomial.basisMonomials (Fin 2) ℝ).repr.trans
    (Finsupp.domLCongr exponentPair)).trans Zarankiewicz.flattenBi.symm

theorem toBiPolynomial_coeff (P : Poly2) (a b : ℕ) :
    Zarankiewicz.biCoeff (toBiPolynomial P) a b =
      P.coeff (exponentPair.symm (a,b)) := by
  rw [← Zarankiewicz.flattenBi_apply]
  change (Zarankiewicz.flattenBi (Zarankiewicz.flattenBi.symm _)) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem toBiPolynomial_monomial (m : Fin 2 →₀ ℕ) (c : ℝ) :
    toBiPolynomial (MvPolynomial.monomial m c) =
      PolynomialModule.single ℝ (m 0) (PolynomialModule.single ℝ (m 1) c) := by
  apply Zarankiewicz.bi_ext
  intro a b
  rw [toBiPolynomial_coeff]
  simp only [MvPolynomial.coeff_monomial, Zarankiewicz.biCoeff,
    PolynomialModule.coeff_single, Finsupp.single_apply]
  by_cases hm : m = exponentPair.symm (a,b)
  · subst m
    simp
  · have hne : m 0 ≠ a ∨ m 1 ≠ b := by
      by_contra h
      simp only [not_or, not_not] at h
      apply hm
      apply exponentPair.injective
      exact Prod.ext h.1 h.2
    rcases hne with h | h
    · simp [hm, h]
    · by_cases ha : m 0 = a <;> simp [hm, h, ha]

theorem toBiPolynomial_eval (P : Poly2) (u v : ℝ) :
    Zarankiewicz.biEval u v (toBiPolynomial P) = evalTwo u v P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial m c =>
    rw [toBiPolynomial_monomial]
    simp only [Zarankiewicz.biEval, LinearMap.comp_apply, PolynomialModule.eval_single,
      map_smul, smul_eq_mul]
    simp only [evalTwo, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
      ring
    · intro i
      simp

theorem toBiPolynomial_bounded (a b : ℕ) (P : Poly2) (hP : P ∈ rectangle a b) :
    Zarankiewicz.BiBounded (a+1) (b+1) (toBiPolynomial P) := by
  obtain ⟨ha,hb⟩ := (rectangle_membership a b P).mp hP
  constructor
  · intro k hk
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro j
    change Zarankiewicz.biCoeff (toBiPolynomial P) k j = 0
    rw [toBiPolynomial_coeff]
    by_contra h
    have := MvPolynomial.degreeOf_le_iff.mp ha _ (MvPolynomial.mem_support_iff.mpr h)
    simp only [exponentPair_symm_zero] at this
    omega
  · intro k j hj
    change Zarankiewicz.biCoeff (toBiPolynomial P) k j = 0
    rw [toBiPolynomial_coeff]
    by_contra h
    have := MvPolynomial.degreeOf_le_iff.mp hb _ (MvPolynomial.mem_support_iff.mpr h)
    simp only [exponentPair_symm_one] at this
    omega

end Paper170

end
end

section

/-! Polynomial cycle tests and the span of products of bounded-degree polynomials. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def polynomialTestLinear {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) : Poly4 →ₗ[ℝ] ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q,
    (J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q) •
      evalFour (node i) (node p) (node k) (node q)

theorem polynomialTestLinear_apply {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (P : Poly4) :
    polynomialTestLinear node J P = polynomialTest node J P := by
  simp [polynomialTestLinear, polynomialTest]

theorem evalFour_monomial (x u y v : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    evalFour x u y v (MvPolynomial.monomial m c) = c * (x^m 0 * u^m 1 * y^m 2 * v^m 3) := by
  simp only [evalFour, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four]
  · intro i
    simp

theorem polynomialTest_monomial {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (m : Fin 4 →₀ ℕ) (c : ℝ) :
    polynomialTest node J (MvPolynomial.monomial m c) = c *
      chainPairing J (weightedChain node (m 0) (m 1)) (weightedChain node (m 2) (m 3)) := by
  simp only [polynomialTest, evalFour_monomial, chainPairing, Finset.mul_sum, weightedChain]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem polynomial_cycle_tests {n : ℕ} (hn : 2 ≤ n) (node : Fin n → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor n)
    (hcycles : ∀ z z' : Fin n → Fin n → ℝ,
      (∀ v, chainBoundary z v = 0) → (∀ v, chainBoundary z' v = 0) →
        chainPairing J z z' = 0)
    (H : Poly4) (hH : H ∈ box4 (n-2)) : polynomialTest node J H = 0 := by
  rw [← polynomialTestLinear_apply, H.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [polynomialTestLinear_apply, polynomialTest_monomial]
  have hb (i : Fin 4) : m i + 1 < n := by
    have := MvPolynomial.degreeOf_le_iff.mp ((box4_membership (n-2) H).mp hH i) m hm
    omega
  rw [hcycles _ _ (weighted_chain_boundary node hnode _ _ (hb 0) (hb 1))
    (weighted_chain_boundary node hnode _ _ (hb 2) (hb 3)), mul_zero]

theorem products_span_degree (s : ℕ) :
    Submodule.span ℝ {P : Polynomial ℝ | ∃ U V : Polynomial ℝ,
      U.natDegree ≤ s ∧ V.natDegree ≤ s ∧ P = U * V} = Polynomial.degreeLT ℝ (2*s+1) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro P ⟨U,V,hU,hV,rfl⟩
    change U * V ∈ Polynomial.degreeLT ℝ (2*s+1)
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := Polynomial.natDegree_mul_le_of_le hU hV
    omega
  · rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
    intro P hP
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hP
    have hk : k ≤ 2*s := by rw [Finset.mem_range] at hk; omega
    apply Submodule.subset_span
    refine ⟨Polynomial.X ^ min k s, Polynomial.X ^ (k-min k s), ?_, ?_, ?_⟩
    · simp only [Polynomial.natDegree_X_pow]
      exact min_le_right _ _
    · simp only [Polynomial.natDegree_X_pow]
      omega
    · rw [← pow_add, Nat.add_sub_of_le (min_le_left k s)]

end Paper170

end
end

end OAI

namespace OAI

/-! Coordinate symmetry, polynomial quotients, collision divisibility, and specialization. -/

section

noncomputable section
open MvPolynomial
namespace Paper170

lemma substitution_difference_dvd {σ : Type*} (f : MvPolynomial σ ℝ)
    (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ)
    (hX : ∀ i, f ∣ X i - φ (X i)) (P : MvPolynomial σ ℝ) : f ∣ P - φ P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    have h := dvd_add hP hQ
    simpa only [map_add, sub_add_sub_comm] using h
  | mul_X P i hP =>
    have h := dvd_add (dvd_mul_of_dvd_left hP (X i))
      (dvd_mul_of_dvd_right (hX i) (φ P))
    convert h using 1
    rw [map_mul]
    ring

private def reinsertDiagonal : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Poly4 :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 3]

theorem diagonal_vanishing_iff_divisible (P : Poly4) :
    diagonalSpecialization P = 0 ↔ (X 0 - X 2 : Poly4) ∣ P := by
  let φ : Poly4 →ₐ[ℝ] Poly4 := reinsertDiagonal.comp diagonalSpecialization
  have hX : ∀ i, (X 0 - X 2 : Poly4) ∣ X i - φ (X i) := by
    intro i
    fin_cases i <;> simp [φ, reinsertDiagonal, diagonalSpecialization,
      Matrix.cons_val_two, Matrix.cons_val_three]
    exact ⟨-1, by ring⟩
  constructor
  · intro hP
    have h := substitution_difference_dvd (X 0 - X 2) φ hX P
    simpa [φ, hP] using h
  · rintro ⟨Q, rfl⟩
    simp [diagonalSpecialization, Matrix.cons_val_two]

end Paper170

end
end

section

noncomputable section
open MvPolynomial
namespace Paper170

lemma difference_coefficient (i j : Fin 4) (hij : i ≠ j) :
    (X i - X j : Poly4).coeff (Finsupp.single i 1) = 1 := by
  simp [coeff_X, Finsupp.single_left_inj, Ne.symm hij]

lemma difference_degree (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    (X i - X j : Poly4).degreeOf k = if k = i ∨ k = j then 1 else 0 := by
  have hupper := degreeOf_sub_le k (X i : Poly4) (X j)
  simp only [degreeOf_X] at hupper
  by_cases hki : k = i
  · subst k
    rw [ite_eq_left (Or.inl rfl)]
    apply Nat.le_antisymm
    · simpa [hij] using hupper
    · have hm : Finsupp.single i 1 ∈ (X i - X j : Poly4).support :=
        mem_support_iff.mpr (by rw [difference_coefficient i j hij]; norm_num)
      simpa using monomial_le_degreeOf i hm
  · by_cases hkj : k = j
    · subst k
      rw [ite_eq_left (Or.inr rfl)]
      apply Nat.le_antisymm
      · simpa [hki] using hupper
      · have hc : (X i - X j : Poly4).coeff (Finsupp.single j 1) = -1 := by
          simp [coeff_X, Finsupp.single_left_inj, hij]
        have hm : Finsupp.single j 1 ∈ (X i - X j : Poly4).support :=
          mem_support_iff.mpr (by rw [hc]; norm_num)
        simpa using monomial_le_degreeOf j hm
    · rw [ite_eq_right (not_or.mpr ⟨hki, hkj⟩)]
      exact Nat.eq_zero_of_le_zero (by simpa [hki, hkj] using hupper)

theorem difference_prime (i j : Fin 4) (hij : i ≠ j) :
    Prime (X i - X j : Poly4) := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  apply irreducible_of_totalDegree_eq_one
  · apply Nat.le_antisymm
    · simpa using totalDegree_sub (X i : Poly4) (X j)
    · have h := degreeOf_le_totalDegree (X i - X j : Poly4) i
      simpa [difference_degree i j hij] using h
  · intro r hr
    apply isUnit_of_dvd_one
    simpa only [difference_coefficient i j hij] using hr (Finsupp.single i 1)

theorem collision_factors_nonassociate :
    Pairwise (fun i j : Fin 4 => ¬ Associated (collisionFactors i) (collisionFactors j)) := by
  let w : Fin 4 → Fin 4 → ℝ := ![![0, 1, 0, 2], ![0, 1, 2, 0],
    ![1, 0, 0, 2], ![1, 0, 2, 0]]
  intro i j hij ha
  have hi : eval (w i) (collisionFactors i) = 0 := by
    fin_cases i <;> norm_num [w, collisionFactors, Matrix.cons_val_two, Matrix.cons_val_three]
  have hj : eval (w i) (collisionFactors j) ≠ 0 := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | norm_num [w, collisionFactors,
      Matrix.cons_val_two, Matrix.cons_val_three]
  obtain ⟨Q, hQ⟩ := ha.dvd
  have h := congrArg (eval (w i)) hQ
  simp only [eval_mul, hi, zero_mul] at h
  exact hj h

theorem collision_factor_properties :
    collisionFactor ≠ 0 ∧ swapFirstPair collisionFactor = collisionFactor ∧
      swapSecondPair collisionFactor = collisionFactor ∧
      ∀ i : Fin 4, collisionFactor.degreeOf i = 2 := by
  have h02 := (difference_prime 0 2 (by decide)).ne_zero
  have h03 := (difference_prime 0 3 (by decide)).ne_zero
  have h12 := (difference_prime 1 2 (by decide)).ne_zero
  have h13 := (difference_prime 1 3 (by decide)).ne_zero
  refine ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero h02 h03) h12) h13, ?_, ?_, ?_⟩
  · norm_num [collisionFactor, swapFirstPair, Equiv.swap_apply_def, Fin.ext_iff]
    ring
  · norm_num [collisionFactor, swapSecondPair, Equiv.swap_apply_def, Fin.ext_iff]
    ring
  · intro i
    rw [collisionFactor, degreeOf_mul_eq (mul_ne_zero (mul_ne_zero h02 h03) h12) h13,
      degreeOf_mul_eq (mul_ne_zero h02 h03) h12, degreeOf_mul_eq h02 h03]
    fin_cases i <;> norm_num [difference_degree, Fin.ext_iff, show (0 : Fin 4) ≠ 2 by decide,
      show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
      show (1 : Fin 4) ≠ 3 by decide]

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open Module MvPolynomial
namespace Paper170

abbrev BoundedExponents (d : ℕ) := Fin 4 → Fin (d + 1)

def tupleExponent {d : ℕ} (t : BoundedExponents d) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (t i).val)

@[simp] lemma tupleExponent_apply {d : ℕ} (t : BoundedExponents d) (i : Fin 4) :
    tupleExponent t i = (t i).val := rfl

def boxExponentEquiv (d : ℕ) :
    {m : Fin 4 →₀ ℕ // ∀ i, m i ≤ d} ≃ BoundedExponents d where
  toFun m i := ⟨m.val i, Nat.lt_succ_of_le (m.property i)⟩
  invFun t := ⟨tupleExponent t, fun i => Nat.le_of_lt_succ (t i).isLt⟩
  left_inv m := by apply Subtype.ext; ext i; rfl
  right_inv t := rfl

lemma box_eq_restrictSupport (d : ℕ) :
    box4 d = MvPolynomial.restrictSupport ℝ {m | ∀ i, m i ≤ d} := by
  ext P
  rw [box4_membership, MvPolynomial.mem_restrictSupport_iff]
  simp only [degreeOf_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  exact ⟨fun h m hm i => h i m hm, fun h i m hm => h m hm i⟩

def boxBasis (d : ℕ) : Basis (BoundedExponents d) ℝ (box4 d) :=
  ((MvPolynomial.basisRestrictSupport ℝ _).reindex (boxExponentEquiv d)).map
    (LinearEquiv.ofEq _ _ (box_eq_restrictSupport d).symm)

lemma box_finite (d : ℕ) : FiniteDimensional ℝ (box4 d) :=
  Module.Finite.of_basis (boxBasis d)

@[simp] lemma boxBasis_repr (d : ℕ) (P : box4 d) (t : BoundedExponents d) :
    (boxBasis d).repr P t = P.val.coeff (tupleExponent t) := by
  rfl

theorem symmetric_space_finite (s : ℕ) :
    FiniteDimensional ℝ (endpointSymmetricSpace s) := by
  let := box_finite (s - 2)
  let f : endpointSymmetricSpace s →ₗ[ℝ] box4 (s - 2) :=
    Submodule.inclusion (inf_le_left.trans inf_le_left)
  exact FiniteDimensional.of_injective f (Submodule.inclusion_injective _)

end Paper170

end
end

section

noncomputable section
namespace Paper170

@[simp] lemma swapFirstPair_mul (P Q : Poly4) :
    swapFirstPair (P * Q) = swapFirstPair P * swapFirstPair Q := by
  exact map_mul (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1)) P Q

@[simp] lemma swapSecondPair_mul (P Q : Poly4) :
    swapSecondPair (P * Q) = swapSecondPair P * swapSecondPair Q := by
  exact map_mul (MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)) P Q

theorem collision_quotient (s : ℕ) (_hs : 2 ≤ s) (P : Poly4)
    (hP : P ∈ endpointSymmetricSpace s) (hP0 : P ≠ 0) (hdiv : collisionFactor ∣ P) :
    ∃ Q : Poly4, Q ≠ 0 ∧ P = collisionFactor * Q ∧
      Q ∈ endpointSymmetricSpace s ∧
      (∀ i : Fin 4, Q.degreeOf i + 2 = P.degreeOf i) ∧
      Q.degreeOf 0 < P.degreeOf 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hP0
    simp [h, hQ]
  rcases collision_factor_properties with ⟨hc, hc1, hc2, hcd⟩
  rcases (symmetric_space_membership s P).mp hP with ⟨hpdeg, hp1, hp2⟩
  have hdeg (i : Fin 4) : Q.degreeOf i + 2 = P.degreeOf i := by
    rw [hQ, MvPolynomial.degreeOf_mul_eq hc hQ0, hcd, add_comm]
  have hfirst : swapFirstPair Q = Q := by
    apply mul_left_cancel₀ hc
    calc
      collisionFactor * swapFirstPair Q = swapFirstPair (collisionFactor * Q) := by
        rw [swapFirstPair_mul, hc1]
      _ = collisionFactor * Q := by rw [← hQ, hp1, hQ]
  have hsecond : swapSecondPair Q = Q := by
    apply mul_left_cancel₀ hc
    calc
      collisionFactor * swapSecondPair Q = swapSecondPair (collisionFactor * Q) := by
        rw [swapSecondPair_mul, hc2]
      _ = collisionFactor * Q := by rw [← hQ, hp2, hQ]
  refine ⟨Q, hQ0, hQ, (symmetric_space_membership s Q).mpr ⟨?_, hfirst, hsecond⟩,
    hdeg, ?_⟩
  · intro i
    have := hdeg i
    have := hpdeg i
    omega
  · have := hdeg 0
    omega

end Paper170

end
end

section

noncomputable section
open MvPolynomial
namespace Paper170

/-- The three extra factors in the local test have the degree vector printed in the paper. -/
theorem local_weight_degrees (i : Fin 4) :
    ((X 1 - X 3) * (X 1 - X 2) * (X 3 - X 0) : Poly4).degreeOf i =
      (![1, 2, 1, 2] : Fin 4 → ℕ) i := by
  have h13 := (difference_prime 1 3 (by decide)).ne_zero
  have h12 := (difference_prime 1 2 (by decide)).ne_zero
  have h30 := (difference_prime 3 0 (by decide)).ne_zero
  rw [degreeOf_mul_eq (mul_ne_zero h13 h12) h30, degreeOf_mul_eq h13 h12]
  fin_cases i <;> norm_num [difference_degree, Fin.ext_iff,
    show (1 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
    show (3 : Fin 4) ≠ 0 by decide]

/-- Identifying any two variables leaves a polynomial ring in the other three. -/
theorem difference_quotient_polynomial (i j : Fin 4) (hij : i ≠ j) :
    Nonempty ((Poly4 ⧸ Ideal.span ({X i - X j} : Set Poly4)) ≃ₐ[ℝ]
      MvPolynomial (Fin 3) ℝ) := by
  classical
  let collapse : Fin 4 → {k : Fin 4 // k ≠ i} := fun k =>
    if h : k = i then ⟨j, hij.symm⟩ else ⟨k, h⟩
  let φ : Poly4 →ₐ[ℝ] MvPolynomial {k : Fin 4 // k ≠ i} ℝ := rename collapse
  let insert : MvPolynomial {k : Fin 4 // k ≠ i} ℝ →ₐ[ℝ] Poly4 := rename Subtype.val
  have hs : Function.Surjective φ := by
    apply rename_surjective
    intro k
    refine ⟨k.val, ?_⟩
    simp [collapse, k.property]
  have hk : RingHom.ker φ.toRingHom = Ideal.span ({X i - X j} : Set Poly4) := by
    ext P
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    change φ P = 0 ↔ (X i - X j : Poly4) ∣ P
    constructor
    · intro hp
      have hx : ∀k, (X i - X j : Poly4) ∣ X k - (insert.comp φ) (X k) := by
        intro k
        by_cases hki : k = i
        · subst k
          simp [insert, φ, collapse]
        · simp [insert, φ, collapse, hki]
      have h := substitution_difference_dvd (X i - X j) (insert.comp φ) hx P
      simpa [hp] using h
    · rintro ⟨Q, rfl⟩
      simp [φ, collapse, hij.symm]
  exact ⟨(Ideal.quotientEquivAlgOfEq ℝ hk.symm).trans
    ((Ideal.quotientKerAlgEquivOfSurjective hs).trans
      (renameEquiv ℝ (finSuccAboveEquiv (p := i)).symm))⟩

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

def diagonalUnivariate (u v : ℝ) : Poly4 →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C u, Polynomial.X, Polynomial.C v]

lemma diagonalUnivariate_monomial (u v : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    diagonalUnivariate u v (monomial m c) =
      Polynomial.C (c * u ^ m 1 * v ^ m 3) * Polynomial.X ^ (m 0 + m 2) := by
  simp only [diagonalUnivariate, MvPolynomial.aeval_monomial,
    Polynomial.algebraMap_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four, pow_add]
    ring
  · intro i
    simp

lemma diagonalUnivariate_bound (s : ℕ) (P : endpointSymmetricSpace s) (u v : ℝ) :
    (diagonalUnivariate u v P.val).natDegree ≤ 2 * (s - 2) := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).1
  rw [P.val.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [diagonalUnivariate_monomial]
  have h0 := degreeOf_le_iff.mp (hp 0) m hm
  have h2 := degreeOf_le_iff.mp (hp 2) m hm
  calc
    (Polynomial.C (P.val.coeff m * u ^ m 1 * v ^ m 3) *
      Polynomial.X ^ (m 0 + m 2)).natDegree ≤ m 0 + m 2 := by
        simpa using Polynomial.natDegree_C_mul_le (P.val.coeff m * u ^ m 1 * v ^ m 3)
          (Polynomial.X ^ (m 0 + m 2) : Polynomial ℝ)
    _ ≤ 2 * (s - 2) := by omega

lemma diagonalUnivariate_eval (u v x : ℝ) (P : Poly4) :
    (diagonalUnivariate u v P).eval x = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalUnivariate, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul, Polynomial.eval_mul]
    rw [hP]
    fin_cases i <;> simp [diagonalUnivariate, evalFour, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma diagonal_eval (P : Poly4) (x u v : ℝ) :
    MvPolynomial.eval ![x, u, v] (diagonalSpecialization P) = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalSpecialization, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [diagonalSpecialization, evalFour, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma vertex_eval (P : Poly4) (x u v : ℝ) :
    evalTwo u v (vertexSpecialization x P) = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [vertexSpecialization, evalFour, evalTwo]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    change MvPolynomial.aeval ![u, v] _ = MvPolynomial.aeval ![x, u, x, v] _
    change MvPolynomial.aeval ![u, v] _ = MvPolynomial.aeval ![x, u, x, v] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [vertexSpecialization, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma diagonal_zero_of_vertices (s : ℕ) (node : Fin (2 * s + 1) → ℝ)
    (hn : Function.Injective node) (P : endpointSymmetricSpace s)
    (hP : ∀ i, vertexSpecialization (node i) P.val = 0) :
    diagonalSpecialization P.val = 0 := by
  have hpoly (u v : ℝ) : diagonalUnivariate u v P.val = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hn
    · intro i
      rw [diagonalUnivariate_eval, ← vertex_eval, hP, map_zero]
    · have h := diagonalUnivariate_bound s P u v
      simp only [Fintype.card_fin]
      omega
  apply MvPolynomial.funext
  intro t
  have ht : t = ![t 0, t 1, t 2] := by ext i; fin_cases i <;> rfl
  rw [ht, diagonal_eval, ← diagonalUnivariate_eval, hpoly]
  simp

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem box_rename {d : ℕ} {P : Poly4} (hP : P ∈ box4 d) (e : Equiv.Perm (Fin 4)) :
    rename e P ∈ box4 d := by
  apply (box4_membership _ _).mpr
  intro i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [degreeOf_rename_of_injective e.injective]
  exact (box4_membership _ _).mp hP j

theorem coeff_rename_tuple {d : ℕ} (e : Equiv.Perm (Fin 4)) (P : Poly4)
    (t : BoundedExponents d) :
    (rename e P).coeff (tupleExponent t) =
      P.coeff (tupleExponent (fun i => t (e i))) := by
  have he : (tupleExponent (fun i => t (e i))).mapDomain e = tupleExponent t := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  rw [← he, coeff_rename_mapDomain e e.injective]

theorem box_coeff_ext {d : ℕ} {P Q : Poly4} (hP : P ∈ box4 d) (hQ : Q ∈ box4 d)
    (h : ∀ t : BoundedExponents d, P.coeff (tupleExponent t) = Q.coeff (tupleExponent t)) :
    P = Q := by
  have he : (⟨P, hP⟩ : box4 d) = ⟨Q, hQ⟩ := by
    apply (boxBasis d).repr.injective
    ext t
    exact h t
  exact congrArg Subtype.val he

theorem tuple4_eta {α : Type*} (t : Fin 4 → α) : ![t 0, t 1, t 2, t 3] = t := by
  funext i
  fin_cases i <;> simp

abbrev SymmetricCoordinate (d : ℕ) := Sym2 (Fin (d + 1)) × Sym2 (Fin (d + 1))

def tupleOrbit {d : ℕ} (t : BoundedExponents d) : SymmetricCoordinate d :=
  (s(t 0, t 1), s(t 2, t 3))

theorem tupleOrbit_swap_first {d : ℕ} (t : BoundedExponents d) :
    tupleOrbit (fun i => t (Equiv.swap (0 : Fin 4) 1 i)) = tupleOrbit t := by
  change (s(t 1, t 0), s(t 2, t 3)) = (s(t 0, t 1), s(t 2, t 3))
  exact Prod.ext Sym2.eq_swap rfl

theorem tupleOrbit_swap_second {d : ℕ} (t : BoundedExponents d) :
    tupleOrbit (fun i => t (Equiv.swap (2 : Fin 4) 3 i)) = tupleOrbit t := by
  change (s(t 0, t 1), s(t 3, t 2)) = (s(t 0, t 1), s(t 2, t 3))
  exact Prod.ext rfl Sym2.eq_swap

theorem symmetric_coeff_first {s : ℕ} (P : endpointSymmetricSpace s)
    (a b c d : Fin (s - 2 + 1)) :
    P.val.coeff (tupleExponent ![a, b, c, d]) = P.val.coeff (tupleExponent ![b, a, c, d]) := by
  have he : (fun i => (![a, b, c, d] : BoundedExponents (s - 2))
      (Equiv.swap (0 : Fin 4) 1 i)) = ![b, a, c, d] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.1
  change rename (Equiv.swap (0 : Fin 4) 1) P.val = P.val at hp
  have hc := coeff_rename_tuple (Equiv.swap (0 : Fin 4) 1) P.val ![a, b, c, d]
  rwa [he, hp] at hc

theorem symmetric_coeff_second {s : ℕ} (P : endpointSymmetricSpace s)
    (a b c d : Fin (s - 2 + 1)) :
    P.val.coeff (tupleExponent ![a, b, c, d]) = P.val.coeff (tupleExponent ![a, b, d, c]) := by
  have he : (fun i => (![a, b, c, d] : BoundedExponents (s - 2))
      (Equiv.swap (2 : Fin 4) 3 i)) = ![a, b, d, c] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.2
  change rename (Equiv.swap (2 : Fin 4) 3) P.val = P.val at hp
  have hc := coeff_rename_tuple (Equiv.swap (2 : Fin 4) 3) P.val ![a, b, c, d]
  rwa [he, hp] at hc

def symmetricCoefficients {s : ℕ} (P : endpointSymmetricSpace s) :
    SymmetricCoordinate (s - 2) → ℝ := fun q =>
  Sym2.lift₂ ⟨(fun a b c d => P.val.coeff (tupleExponent ![a, b, c, d])),
    fun a b c d => ⟨symmetric_coeff_first P a b c d, symmetric_coeff_second P a b c d⟩⟩ q.1 q.2

@[simp] theorem symmetricCoefficients_orbit {s : ℕ} (P : endpointSymmetricSpace s)
    (t : BoundedExponents (s - 2)) :
    symmetricCoefficients P (tupleOrbit t) = P.val.coeff (tupleExponent t) := by
  simp [symmetricCoefficients, tupleOrbit, tuple4_eta]

def realizeBox (d : ℕ) (f : SymmetricCoordinate d → ℝ) : box4 d :=
  (boxBasis d).equivFun.symm (fun t => f (tupleOrbit t))

@[simp] theorem realizeBox_coeff (d : ℕ) (f : SymmetricCoordinate d → ℝ)
    (t : BoundedExponents d) :
    (realizeBox d f).val.coeff (tupleExponent t) = f (tupleOrbit t) := by
  change (boxBasis d).equivFun ((boxBasis d).equivFun.symm _) t = _
  rw [LinearEquiv.apply_symm_apply]

theorem realizeBox_symmetric (s : ℕ) (f : SymmetricCoordinate (s - 2) → ℝ) :
    (realizeBox (s - 2) f).val ∈ endpointSymmetricSpace s := by
  apply (symmetric_space_membership _ _).mpr
  refine ⟨(box4_membership _ _).mp (realizeBox (s - 2) f).property, ?_, ?_⟩
  · apply box_coeff_ext (box_rename (realizeBox (s - 2) f).property _)
      (realizeBox (s - 2) f).property
    intro t
    change (rename (Equiv.swap (0 : Fin 4) 1) _).coeff (tupleExponent t) = _
    rw [coeff_rename_tuple, realizeBox_coeff, realizeBox_coeff, tupleOrbit_swap_first]
  · apply box_coeff_ext (box_rename (realizeBox (s - 2) f).property _)
      (realizeBox (s - 2) f).property
    intro t
    change (rename (Equiv.swap (2 : Fin 4) 3) _).coeff (tupleExponent t) = _
    rw [coeff_rename_tuple, realizeBox_coeff, realizeBox_coeff, tupleOrbit_swap_second]

def realizeSymmetric (s : ℕ) (f : SymmetricCoordinate (s - 2) → ℝ) : endpointSymmetricSpace s :=
  ⟨(realizeBox (s - 2) f).val, realizeBox_symmetric s f⟩

def symmetricCoordinatesEquiv (s : ℕ) :
    endpointSymmetricSpace s ≃ₗ[ℝ] (SymmetricCoordinate (s - 2) → ℝ) where
  toFun := symmetricCoefficients
  invFun := realizeSymmetric s
  left_inv P := by
    apply Subtype.ext
    apply box_coeff_ext (realizeBox (s - 2) (symmetricCoefficients P)).property
      ((box4_membership _ _).mpr ((symmetric_space_membership _ _).mp P.property).1)
    intro t
    rw [realizeBox_coeff, symmetricCoefficients_orbit]
  right_inv f := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients, realizeSymmetric, realizeBox_coeff, tupleOrbit]
  map_add' P Q := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients]
  map_smul' c P := by
    funext q
    rcases q with ⟨a, b⟩
    induction a using Sym2.ind
    induction b using Sym2.ind
    simp [symmetricCoefficients]

theorem symmetric_space_dimension (s : ℕ) (hs : 2 ≤ s) :
    Module.finrank ℝ (endpointSymmetricSpace s) = (Nat.choose s 2) ^ 2 := by
  rw [(symmetricCoordinatesEquiv s).finrank_eq, Module.finrank_pi]
  simp only [SymmetricCoordinate, Fintype.card_prod, Sym2.card, Fintype.card_fin]
  have he : s - 2 + 1 + 1 = s := by omega
  rw [he]
  ring

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

lemma collisionFactors_prime (i : Fin 4) : Prime (collisionFactors i) := by
  fin_cases i <;> exact difference_prime _ _ (by decide)

lemma collisionFactors_coprime :
    Pairwise (fun i j : Fin 4 => IsRelPrime (collisionFactors i) (collisionFactors j)) := by
  intro i j hij
  rw [(collisionFactors_prime i).irreducible.isRelPrime_iff_not_dvd,
    (collisionFactors_prime i).dvd_prime_iff_associated (collisionFactors_prime j)]
  exact collision_factors_nonassociate hij

lemma collision_divides_of_diagonal_vanishing (s : ℕ) (P : endpointSymmetricSpace s)
    (hP : diagonalSpecialization P.val = 0) : collisionFactor ∣ P.val := by
  have h02 := (diagonal_vanishing_iff_divisible P.val).mp hP
  rcases (symmetric_space_membership s P.val).mp P.property with ⟨_, hp1, hp2⟩
  have h03 : (X 0 - X 3 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h02
    refine ⟨swapSecondPair Q, ?_⟩
    have h := congrArg swapSecondPair hQ
    rw [hp2, swapSecondPair_mul] at h
    simpa [swapSecondPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have h12 : (X 1 - X 2 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h02
    refine ⟨swapFirstPair Q, ?_⟩
    have h := congrArg swapFirstPair hQ
    rw [hp1, swapFirstPair_mul] at h
    simpa [swapFirstPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have h13 : (X 1 - X 3 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h03
    refine ⟨swapFirstPair Q, ?_⟩
    have h := congrArg swapFirstPair hQ
    rw [hp1, swapFirstPair_mul] at h
    simpa [swapFirstPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have hdvd (i : Fin 4) : collisionFactors i ∣ P.val := by
    fin_cases i
    · exact h02
    · exact h03
    · exact h12
    · exact h13
  have h := Finset.prod_dvd_of_isRelPrime
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) j _ hij =>
      collisionFactors_coprime hij) (fun i _ => hdvd i)
  simpa [Fin.prod_univ_four, collisionFactors, collisionFactor,
    Matrix.cons_val_two, Matrix.cons_val_three] using h

end Paper170

end
end

end OAI

namespace OAI

/-! The support form, injectivity criterion, and support-space dimension. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem collision_nonzero_on_support {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) (a : SupportCoord J) :
    evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1) (node a.val.2.2)
      collisionFactor ≠ 0 := by
  rcases (Finset.mem_filter.mp a.property).2 with ⟨_, _, h02, h03, h12, h13, _⟩
  simpa [evalFour, collisionFactor, Matrix.cons_val_two, Matrix.cons_val_three] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hn.ne h02))
      (sub_ne_zero.mpr (hn.ne h03))) (sub_ne_zero.mpr (hn.ne h12)))
      (sub_ne_zero.mpr (hn.ne h13))

lemma support_diagonal_nonzero {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) (a : SupportCoord J) :
    supportDiagonal node J a ≠ 0 := by
  rcases (Finset.mem_filter.mp a.property).2 with ⟨h01, h23, _, _, _, _, hJ⟩
  have hc := collision_nonzero_on_support node hn J a
  have hf : evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1)
      (node a.val.2.2) fullDifference ≠ 0 := by
    simpa [fullDifference, evalFour, Matrix.cons_val_two, Matrix.cons_val_three] using
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hn.ne (ne_of_lt h01)))
        (sub_ne_zero.mpr (hn.ne (ne_of_lt h23)))) hc
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hJ
    (weight_nonzero node hn _)) (weight_nonzero node hn _))
      (weight_nonzero node hn _)) (weight_nonzero node hn _)) hf

theorem support_bilinear_nondegenerate {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) :
    (supportBilinear node J).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => support_diagonal_nonzero node hn J a

theorem isotropic_dimension {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℝ (ι → ℝ)) (hB : B.Nondegenerate)
    (W : Submodule ℝ (ι → ℝ)) (hW : W ≤ B.orthogonal W) :
    2 * Module.finrank ℝ W ≤ Fintype.card ι := by
  have hle := Submodule.finrank_mono hW
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at hle
  have hdim := Submodule.finrank_le W
  have hv : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by simp
  rw [hv] at hle hdim
  omega

end Paper170

end
end

section

noncomputable section
namespace Paper170

@[simp] lemma evalFour_mul (x u y v : ℝ) (P Q : Poly4) :
    evalFour x u y v (P * Q) = evalFour x u y v P * evalFour x u y v Q :=
  map_mul (MvPolynomial.aeval ![x, u, y, v]) P Q

lemma support_evaluation_injective_of_collision {n s : ℕ} (hs : 2 ≤ s)
    (node : Fin n → ℝ) (hn : Function.Injective node) (J : CrossingTensor n)
    (hdiv : ∀ P : endpointSymmetricSpace s,
      supportEvaluation s node J P = 0 → collisionFactor ∣ P.val) :
    Function.Injective (supportEvaluation s node J) := by
  have hzero : ∀ d (P : endpointSymmetricSpace s), P.val.degreeOf 0 = d →
      supportEvaluation s node J P = 0 → P.val = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hd hP
      by_contra hP0
      obtain ⟨Q, hQ0, heq, hQmem, _, hQdeg⟩ := collision_quotient s hs P.val
        P.property hP0 (hdiv P hP)
      have hQ : supportEvaluation s node J ⟨Q, hQmem⟩ = 0 := by
        funext a
        have hp := congrFun hP a
        change evalFour (node a.val.1.1) (node a.val.1.2)
          (node a.val.2.1) (node a.val.2.2) P.val = 0 at hp
        rw [heq, evalFour_mul] at hp
        exact (mul_eq_zero.mp hp).resolve_left (collision_nonzero_on_support node hn J a)
      exact hQ0 (ih (Q.degreeOf 0) (by omega) ⟨Q, hQmem⟩ rfl hQ)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  exact Subtype.ext (hzero _ P rfl hP)

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma support_cardinality_of_injective_isotropic {n s : ℕ} (hs : 2 ≤ s)
    (node : Fin n → ℝ) (hn : Function.Injective node) (J : CrossingTensor n)
    (hi : Function.Injective (supportEvaluation s node J))
    (ho : ∀ P Q : endpointSymmetricSpace s,
      supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) = 0) :
    2 * (Nat.choose s 2) ^ 2 ≤ (supportedPairs J).card := by
  let := symmetric_space_finite s
  let f := supportEvaluation s node J
  have hr : f.range ≤ (supportBilinear node J).orthogonal f.range := by
    rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
    exact ho Q P
  have hd := isotropic_dimension (supportBilinear node J)
    (support_bilinear_nondegenerate node hn J) f.range hr
  have he : Module.finrank ℝ f.range = Module.finrank ℝ (endpointSymmetricSpace s) :=
    (LinearEquiv.ofInjective f hi).finrank_eq.symm
  rw [he, symmetric_space_dimension s hs, Fintype.card_coe] at hd
  exact hd

end Paper170

end
end

end OAI

namespace OAI

/-! Isotropic evaluation image and order-pairing identities. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem evalFour_swap_first (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapFirstPair P) = evalFour u x y v P := by
  change aeval ![x, u, y, v] (rename (Equiv.swap (0 : Fin 4) 1) P) = aeval ![u, x, y, v] P
  rw [aeval_rename]
  congr 2
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

theorem evalFour_swap_second (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapSecondPair P) = evalFour x u v y P := by
  change aeval ![x, u, y, v] (rename (Equiv.swap (2 : Fin 4) 3) P) = aeval ![x, u, v, y] P
  rw [aeval_rename]
  congr 2
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

theorem evalFour_fullDifference (x u y v : ℝ) :
    evalFour x u y v fullDifference =
      (x - u) * (y - v) * (x - y) * (x - v) * (u - y) * (u - v) := by
  simp [evalFour, fullDifference, collisionFactor]
  ring

def isotropicTerm {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (P Q : Poly4)
    (i p k q : Fin n) : ℝ :=
  J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q *
    evalFour (node i) (node p) (node k) (node q) fullDifference *
    evalFour (node i) (node p) (node k) (node q) P *
    evalFour (node i) (node p) (node k) (node q) Q

theorem isotropicTerm_first {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hJ : ∀ i p k q, J p i k q = -J i p k q) (P Q : endpointSymmetricSpace s)
    (i p k q : Fin n) :
    isotropicTerm node J P.val Q.val p i k q = isotropicTerm node J P.val Q.val i p k q := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.1
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).2.1
  have hep := evalFour_swap_first P.val (node i) (node p) (node k) (node q)
  have heq := evalFour_swap_first Q.val (node i) (node p) (node k) (node q)
  rw [hp] at hep
  rw [hq] at heq
  unfold isotropicTerm
  rw [hJ i p k q, ← hep, ← heq]
  simp only [evalFour_fullDifference]
  ring

theorem isotropicTerm_second {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hJ : ∀ i p k q, J i p q k = -J i p k q) (P Q : endpointSymmetricSpace s)
    (i p k q : Fin n) :
    isotropicTerm node J P.val Q.val i p q k = isotropicTerm node J P.val Q.val i p k q := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.2
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).2.2
  have hep := evalFour_swap_second P.val (node i) (node p) (node k) (node q)
  have heq := evalFour_swap_second Q.val (node i) (node p) (node k) (node q)
  rw [hp] at hep
  rw [hq] at heq
  unfold isotropicTerm
  rw [hJ i p k q, ← hep, ← heq]
  simp only [evalFour_fullDifference]
  ring

theorem isotropicTerm_vanish {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (P Q : Poly4) (i p k q : Fin n)
    (h : i = p ∨ k = q ∨ i = k ∨ i = q ∨ p = k ∨ p = q ∨ J i p k q = 0) :
    isotropicTerm node J P Q i p k q = 0 := by
  rcases h with h | h | h | h | h | h | h <;>
    simp [isotropicTerm, evalFour_fullDifference, h]

theorem support_sum_eq_upper {n : ℕ} (J : CrossingTensor n)
    (f : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hzero : ∀ i p k q, i = k ∨ i = q ∨ p = k ∨ p = q ∨ J i p k q = 0 → f i p k q = 0) :
    (∑ a : SupportCoord J, f a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2) =
      upperPairSum (fun i p => upperPairSum (f i p)) := by
  let F (a : (Fin n × Fin n) × (Fin n × Fin n)) := f a.1.1 a.1.2 a.2.1 a.2.2
  change (∑ a : SupportCoord J, F a.val) = _
  rw [Finset.sum_coe_sort (supportedPairs J) F]
  simp only [supportedPairs, Finset.sum_filter, Fintype.sum_prod_type, upperPairSum, F]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hip : i < p
  · simp only [hip, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hkq : k < q
    · simp only [hkq, true_and, ite_true]
      by_cases hgood : i ≠ k ∧ i ≠ q ∧ p ≠ k ∧ p ≠ q ∧ J i p k q ≠ 0
      · simp [hgood]
      · have hz : f i p k q = 0 := hzero i p k q (by tauto)
        simp [hz]
    · simp [hkq]
  · simp [hip]

theorem supportBilinear_eq_isotropicSum {n s : ℕ} (node : Fin n → ℝ)
    (J : CrossingTensor n) (P Q : endpointSymmetricSpace s) :
    supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) =
      upperPairSum (fun i p => upperPairSum (isotropicTerm node J P.val Q.val i p)) := by
  calc
    _ = ∑ a : SupportCoord J, isotropicTerm node J P.val Q.val
        a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2 := by
      simp only [supportBilinear, Matrix.toBilin'_apply, Matrix.diagonal_apply,
        mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      apply Finset.sum_congr rfl
      intro a _
      change evalFour _ _ _ _ P.val * supportDiagonal node J a * evalFour _ _ _ _ Q.val = _
      unfold supportDiagonal isotropicTerm
      ring
    _ = _ := support_sum_eq_upper J _ (fun i p k q h =>
      isotropicTerm_vanish node J P.val Q.val i p k q (Or.inr (Or.inr h)))

theorem isotropic_test_degree {s : ℕ} (hs : 2 ≤ s) (P Q : endpointSymmetricSpace s) :
    P.val * Q.val * fullDifference ∈ box4 (2 * s - 1) := by
  apply (box4_membership _ _).mpr
  intro i
  have hΔ : fullDifference.degreeOf i ≤ 3 := by
    have h := degreeOf_mul_bound
      (degreeOf_mul_bound (degreeOf_difference_bound 0 1 i) (degreeOf_difference_bound 2 3 i))
      (le_of_eq (collision_factor_properties.2.2.2 i))
    fin_cases i <;> norm_num [fullDifference] at h ⊢ <;> exact h
  have hp := ((symmetric_space_membership s P.val).mp P.property).1 i
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).1 i
  exact (degreeOf_mul_bound (degreeOf_mul_bound hp hq) hΔ).trans (by omega)

theorem polynomialTest_isotropic {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hfirst : ∀ i p k q, J p i k q = -J i p k q)
    (hsecond : ∀ i p k q, J i p q k = -J i p k q)
    (P Q : endpointSymmetricSpace s) :
    polynomialTest node J (P.val * Q.val * fullDifference) =
      4 * supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) := by
  rw [supportBilinear_eq_isotropicSum]
  have hterm : polynomialTest node J (P.val * Q.val * fullDifference) =
      ∑ i, ∑ p, ∑ k, ∑ q, isotropicTerm node J P.val Q.val i p k q := by
    unfold polynomialTest
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    rw [evalFour_mul, evalFour_mul]
    unfold isotropicTerm
    ring
  rw [hterm]
  exact sum_symmetric_quad _ (isotropicTerm_first node J hfirst P Q)
    (isotropicTerm_second node J hsecond P Q)
    (fun i k q => isotropicTerm_vanish node J P.val Q.val i i k q (Or.inl rfl))
    (fun i p k => isotropicTerm_vanish node J P.val Q.val i p k k (Or.inr (Or.inl rfl)))

theorem evaluation_image_isotropic {s : ℕ} (hs : 2 ≤ s) (node : Fin (2 * s + 1) → ℝ)
    (_hnode : Function.Injective node) (J : CrossingTensor (2 * s + 1))
    (_orders : ∀ i : Fin (2 * s + 1), LinearOrder {j : Fin (2 * s + 1) // j ≠ i})
    (_hloopLeft : ∀ i k q, J i i k q = 0)
    (_hloopRight : ∀ i p k, J i p k k = 0)
    (hreverseLeft : ∀ i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀ i p k q, J i p q k = -J i p k q)
    (_hskew : ∀ i p k q, J k q i p = -J i p k q)
    (_hlocal : ∀ i (p q : {j : Fin (2 * s + 1) // j ≠ i}),
      J i p.val i q.val = halfOrder (_orders i) p q)
    (htests : ∀ H ∈ box4 (2 * s - 1), polynomialTest node J H = 0)
    (P Q : endpointSymmetricSpace s) :
    supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) = 0 := by
  have h := htests _ (isotropic_test_degree hs P Q)
  rw [polynomialTest_isotropic node J hreverseLeft hreverseRight P Q] at h
  linarith

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

theorem weightedPairing_diagonal_invariant {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (K L : ι → ι → ℝ) (h : ∀p q, p≠q → K p q=L p q)
    (A B : Poly2) : weightedPairing node K A B=weightedPairing node L A B := by
  unfold weightedPairing
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : p=q
  · subst q
    simp
  · rw [h p q hpq]

theorem support_swap_mem {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q)
    (a : SupportCoord J) : (a.val.2,a.val.1)∈supportedPairs J := by
  obtain ⟨h01,h23,h02,h03,h12,h13,hJ⟩ := (Finset.mem_filter.mp a.property).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,h23,h01,h02.symm,h12.symm,h03.symm,h13.symm,?_⟩
  rwa [hskew,neg_ne_zero]

def supportEdgeSwap {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) : SupportCoord J :=
  ⟨(a.val.2,a.val.1),support_swap_mem J hskew a⟩

theorem supportEdgeSwap_involutive {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) :
    Function.Involutive (supportEdgeSwap J hskew) := fun _ => Subtype.ext rfl

theorem supportEdgeSwap_ne {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) :
    supportEdgeSwap J hskew a ≠ a := by
  intro he
  have h02 := (Finset.mem_filter.mp a.property).2.2.2.1
  exact h02 (congrArg (fun a : SupportCoord J => a.val.1.1) he).symm

theorem supportDiagonal_swap {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) :
    supportDiagonal node J (supportEdgeSwap J hskew a) = -supportDiagonal node J a := by
  unfold supportDiagonal supportEdgeSwap
  dsimp only
  rw [hskew]
  simp only [evalFour_fullDifference]
  ring

theorem supportBilinear_symmetric {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (x y : SupportCoord J → ℝ) : supportBilinear node J x y=supportBilinear node J y x := by
  simp only [supportBilinear,Matrix.toBilin'_apply,Matrix.diagonal_apply,
    mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem supportDiagonal_swap_block {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) :
    (Matrix.diagonal (supportDiagonal node J)).submatrix
      ![a,supportEdgeSwap J hskew a] ![a,supportEdgeSwap J hskew a] =
      Matrix.diagonal ![supportDiagonal node J a,-supportDiagonal node J a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix,Matrix.diagonal_apply,supportEdgeSwap_ne,
      Ne.symm (supportEdgeSwap_ne J hskew a),supportDiagonal_swap]

end Paper170

end
end

end OAI

namespace OAI

/-! Even triangular interpolation and unisolvence. -/

section

/-! The even two-triangle set, as actual ordered interpolation coordinates. -/
noncomputable section
namespace Paper170

theorem mem_evenTriangle (s : ℕ) (p q : Fin (2*s)) :
    (p,q) ∈ evenTriangle s ↔
      (p.val < s ∧ q < p) ∨ (s ≤ p.val ∧ p < q) := by
  simp [evenTriangle]

def evenTriangleOffDiagEquiv (s : ℕ) :
    EvenTriangleCoord s ≃ ↥((Finset.univ : Finset (Fin s)).offDiag) where
  toFun pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq := (mem_evenTriangle s p q).mp hpq
    by_cases h : p.val < s
    · exact ⟨(⟨p.val, h⟩, ⟨q.val, by rcases hpq with hq | hq <;> omega⟩), by
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, ne_eq, Fin.mk.injEq]
        rcases hpq with hq | hq <;> omega⟩
    · exact ⟨(⟨p.val-s, by omega⟩, ⟨q.val-s, by omega⟩), by
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, ne_eq, Fin.mk.injEq]
        rcases hpq with hq | hq <;> omega⟩
  invFun pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq : p ≠ q := (Finset.mem_offDiag.mp hpq).2.2
    by_cases h : q < p
    · exact ⟨(⟨p.val, by omega⟩, ⟨q.val, by omega⟩),
        (mem_evenTriangle s _ _).mpr (Or.inl ⟨p.isLt,h⟩)⟩
    · exact ⟨(⟨p.val+s, by omega⟩, ⟨q.val+s, by omega⟩),
        (mem_evenTriangle s _ _).mpr (Or.inr ⟨by change s ≤ p.val+s; omega,by
          have hpq := Fin.val_ne_of_ne hpq
          change p.val+s < q.val+s
          omega⟩)⟩
  left_inv pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq := (mem_evenTriangle s p q).mp hpq
    apply Subtype.ext
    dsimp
    split_ifs with h h' h'
    · rfl
    · change ¬q.val < p.val at h'
      simp only [Fin.lt_def] at hpq
      omega
    · change q.val-s < p.val-s at h'
      simp only [Fin.lt_def] at hpq
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;>
        simp only [Fin.lt_def] at hpq <;> omega
  right_inv pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    apply Subtype.ext
    dsimp
    split_ifs with h h' h'
    · rfl
    · change ¬p.val < s at h'
      omega
    · change p.val+s < s at h'
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

theorem even_triangle_card (s : ℕ) : (evenTriangle s).card = s*(s-1) := by
  have hc := Fintype.card_congr (evenTriangleOffDiagEquiv s)
  simp only [EvenTriangleCoord, Fintype.card_coe] at hc
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hc
  simpa only [Nat.mul_sub_left_distrib, mul_one] using hc

end Paper170

end
end

section

/-! Even-node interpolation by adjoining one fresh node to the checked odd-node theorem. -/
noncomputable section
open PolynomialModule
open Zarankiewicz
namespace Paper170

theorem biBounded_mulRoot {r s : ℕ} {P : BiPoly} (hP : BiBounded r s P) (t : ℝ) :
    BiBounded (r+1) s (mulRoot t P) := by
  refine ⟨bounded_mulRoot t hP.1, ?_⟩
  intro a
  cases a with
  | zero =>
    rw [mulRoot_coeff_zero]
    exact (boundedSpace s).smul_mem _ (hP.2 0)
  | succ a =>
    rw [mulRoot_coeff_succ]
    exact bounded_sub (hP.2 a) ((boundedSpace s).smul_mem _ (hP.2 (a+1)))

theorem insertNode_injective {n : ℕ} (r : Fin (n+1)) (node : Fin n → ℝ)
    (hn : Function.Injective node) (t : ℝ) (ht : ∀i, node i ≠ t) :
    Function.Injective (Fin.insertNth r t node) := by
  intro a b
  refine Fin.succAboveCases r ?_ (fun a => ?_) a
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · intro
      rfl
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro h
      exact (ht b h.symm).elim
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro h
      exact (ht a h).elim
    · simp only [Fin.insertNth_apply_succAbove]
      intro h
      exact congrArg r.succAbove (hn h)

theorem oddTriangle_unisolvent_fin (s : ℕ) (node : Fin (2*s+1) → ℝ)
    (hn : Function.Injective node) (P : BiPoly) (hP : BiBounded s s P)
    (hv : ∀a b : Fin (2*s+1),
      (b < a ∧ a.val ≤ s) ∨ (s < a.val ∧ a < b) → biEval (node a) (node b) P = 0) :
    P = 0 := by
  let x : ℕ → ℝ := fun k => if h : 1 ≤ k ∧ k ≤ 2*s+1 then node ⟨k-1,by omega⟩ else 0
  have hx : Set.InjOn x (Set.Icc 1 (2*s+1)) := by
    intro a ha b hb he
    simp only [Set.mem_Icc] at ha hb
    simp only [x, dite_eq_left ha, dite_eq_left hb] at he
    have := congrArg Fin.val (hn he)
    dsimp at this
    omega
  apply twoTriangle_unisolvent s x hx P hP
  intro a b hab
  rw [mem_twoTriangle] at hab
  have ha : 1 ≤ a ∧ a ≤ 2*s+1 := by omega
  have hb : 1 ≤ b ∧ b ≤ 2*s+1 := by omega
  simp only [x, dite_eq_left ha, dite_eq_left hb]
  apply hv
  change (b-1 < a-1 ∧ a-1 ≤ s) ∨ (s < a-1 ∧ a-1 < b-1)
  omega

theorem evenTriangle_unisolvent_first (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded s (s-1) P)
    (hv : ∀a b, (a,b) ∈ evenTriangle s → biEval (node a) (node b) P = 0) : P = 0 := by
  obtain ⟨t,ht⟩ := (Set.finite_range node).exists_notMem
  have hnt : ∀i, node i ≠ t := fun i h => ht ⟨i,h⟩
  let x : Fin (2*s+1) → ℝ := Fin.insertNth (0 : Fin (2*s+1)) t node
  let Q := swapBi (mulRoot t (swapBi P))
  have hQ : BiBounded s s Q := by
    have hb := biBounded_swap (biBounded_mulRoot (biBounded_swap hP) t)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using hb
  have hev (u v : ℝ) : biEval u v Q = (v-t)*biEval u v P := by
    simp only [Q, biEval_swap, biEval_mulRoot]
  have hzero : Q = 0 := by
    apply oddTriangle_unisolvent_fin s x (insertNode_injective _ node hn t hnt) Q hQ
    intro a b
    refine Fin.succAboveCases (0 : Fin (2*s+1)) ?_ (fun a => ?_) a
    · intro h
      have : False := by simp only [Fin.lt_def, Fin.val_zero] at h; omega
      exact this.elim
    · refine Fin.succAboveCases (0 : Fin (2*s+1)) ?_ (fun b => ?_) b
      · intro _
        simp only [hev, x, Fin.insertNth_apply_same, sub_self, zero_mul]
      · intro hab
        simp only [x, Fin.insertNth_apply_succAbove, hev]
        rw [hv a b]
        · exact mul_zero _
        · rw [mem_evenTriangle]
          simp only [Fin.succAbove_zero, Fin.val_succ, Fin.lt_def] at hab
          simp only [Fin.lt_def]
          omega
  have hroot : mulRoot t (swapBi P) = 0 := by
    apply swapBi.injective
    simpa only [map_zero] using hzero
  have hpzero := eq_zero_of_mulRoot_eq_zero t (s-1) (swapBi P) (biBounded_swap hP).1 hroot
  apply swapBi.injective
  simpa only [map_zero] using hpzero

theorem evenTriangle_unisolvent_second (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded (s-1) s P)
    (hv : ∀a b, (a,b) ∈ evenTriangle s → biEval (node a) (node b) P = 0) : P = 0 := by
  obtain ⟨t,ht⟩ := (Set.finite_range node).exists_notMem
  have hnt : ∀i, node i ≠ t := fun i h => ht ⟨i,h⟩
  let r : Fin (2*s+1) := ⟨s,by omega⟩
  let x : Fin (2*s+1) → ℝ := Fin.insertNth r t node
  have hQ : BiBounded s s (mulRoot t P) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using biBounded_mulRoot hP t
  apply eq_zero_of_mulRoot_eq_zero t (s-1) P hP.1
  apply oddTriangle_unisolvent_fin s x (insertNode_injective r node hn t hnt) _ hQ
  intro a b
  refine Fin.succAboveCases r ?_ (fun a => ?_) a
  · intro _
    simp only [biEval_mulRoot, x, Fin.insertNth_apply_same, sub_self, zero_mul]
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · intro hab
      have : False := by
        simp only [Fin.lt_def, r] at hab
        omega
      exact this.elim
    · intro hab
      simp only [x, Fin.insertNth_apply_succAbove, biEval_mulRoot]
      rw [hv a b]
      · exact mul_zero _
      · rw [mem_evenTriangle]
        simp only [Fin.lt_def, r, Fin.succAbove, Fin.val_castSucc] at hab
        simp only [Fin.lt_def]
        split_ifs at hab <;> simp only [Fin.val_castSucc, Fin.val_succ] at hab <;> omega

end Paper170

end
end

section

/-! Bijective interpolation on both even-node degree rectangles. -/
noncomputable section
namespace Paper170

theorem evenTriangle_vanish_first (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P ∈ rectangle (s-1) (s-2))
    (hv : ∀a b, (a,b) ∈ evenTriangle s → evalTwo (node a) (node b) P = 0) : P = 0 := by
  apply toBiPolynomial.injective
  rw [map_zero]
  apply evenTriangle_unisolvent_first s hs node hn (toBiPolynomial P)
  · convert toBiPolynomial_bounded (s-1) (s-2) P hP using 1 <;> omega
  · intro a b hab
    rw [toBiPolynomial_eval]
    exact hv a b hab

theorem evenTriangle_vanish_second (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P ∈ rectangle (s-2) (s-1))
    (hv : ∀a b, (a,b) ∈ evenTriangle s → evalTwo (node a) (node b) P = 0) : P = 0 := by
  apply toBiPolynomial.injective
  rw [map_zero]
  apply evenTriangle_unisolvent_second s hs node hn (toBiPolynomial P)
  · convert toBiPolynomial_bounded (s-2) (s-1) P hP using 1 <;> omega
  · intro a b hab
    rw [toBiPolynomial_eval]
    exact hv a b hab

theorem triangleEvaluation_bijective_of_unisolvent (s a b : ℕ) (node : Fin (2*s) → ℝ)
    (hdim : (a+1)*(b+1) = s*(s-1))
    (hv : ∀P ∈ rectangle a b,
      (∀i j, (i,j) ∈ evenTriangle s → evalTwo (node i) (node j) P = 0) → P=0) :
    Function.Bijective (triangleEvaluation s a b node) := by
  let := rectangle_finite a b
  have hi : Function.Injective (triangleEvaluation s a b node) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    apply hv P.val P.property
    intro i j hij
    exact congrFun hP ⟨(i,j),hij⟩
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  rw [rectangle_dimension, Module.finrank_fintype_fun_eq_card]
  have hc : Fintype.card (EvenTriangleCoord s) = s*(s-1) := by
    rw [Fintype.card_coe, even_triangle_card]
  rw [hc,hdim]

theorem two_triangle_interpolation (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) :
    Function.Bijective (triangleEvaluation s (s-1) (s-2) node) ∧
      Function.Bijective (triangleEvaluation s (s-2) (s-1) node) := by
  constructor
  · apply triangleEvaluation_bijective_of_unisolvent
    · congr 1 <;> omega
    · exact evenTriangle_vanish_first s hs node hn
  · apply triangleEvaluation_bijective_of_unisolvent
    · rw [Nat.mul_comm]
      congr 1 <;> omega
    · exact evenTriangle_vanish_second s hs node hn

end Paper170

end
end

end OAI

namespace OAI

/-! Triangular evaluation indices, division, and determinant factorization. -/

section

noncomputable section
open scoped Classical
namespace Paper170

def triangleMiddleEmbedding (s : ℕ) (hs : 2 ≤ s) (p : Fin (2*(s-1))) : Fin (2*s) :=
  ⟨if p.val<s-1 then p.val else p.val+2, by split_ifs <;> omega⟩

def triangleEndEmbedding (s : ℕ) (hs : 2 ≤ s) (p : Fin (2*(s-1))) : Fin (2*s) :=
  ⟨p.val+1, by omega⟩

theorem triangleMiddleEmbedding_strictMono (s : ℕ) (hs : 2 ≤ s) :
    StrictMono (triangleMiddleEmbedding s hs) := by
  intro p q hpq
  change (if p.val<s-1 then p.val else p.val+2) <
    (if q.val<s-1 then q.val else q.val+2)
  change p.val<q.val at hpq
  split_ifs <;> omega

theorem triangleEndEmbedding_strictMono (s : ℕ) (hs : 2 ≤ s) :
    StrictMono (triangleEndEmbedding s hs) := by
  intro p q hpq
  change p.val+1<q.val+1
  exact Nat.add_lt_add_right hpq 1

theorem triangleMiddleEmbedding_avoids (s : ℕ) (hs : 2 ≤ s) (p : Fin (2*(s-1))) :
    (triangleMiddleEmbedding s hs p).val ≠ s-1 ∧
      (triangleMiddleEmbedding s hs p).val ≠ s := by
  dsimp [triangleMiddleEmbedding]
  split_ifs <;> omega

theorem triangleEndEmbedding_avoids (s : ℕ) (hs : 2 ≤ s) (p : Fin (2*(s-1))) :
    (triangleEndEmbedding s hs p).val ≠ 0 ∧
      (triangleEndEmbedding s hs p).val ≠ 2*s-1 := by
  dsimp [triangleEndEmbedding]
  omega

theorem evenTriangle_delete_middle (s : ℕ) (hs : 2 ≤ s) (p q : Fin (2*(s-1))) :
    (triangleMiddleEmbedding s hs p,triangleMiddleEmbedding s hs q)∈evenTriangle s ↔
      (p,q)∈evenTriangle (s-1) := by
  simp only [mem_evenTriangle,triangleMiddleEmbedding,Fin.lt_def]
  split_ifs <;> omega

theorem evenTriangle_delete_ends (s : ℕ) (hs : 2 ≤ s) (p q : Fin (2*(s-1))) :
    (triangleEndEmbedding s hs p,triangleEndEmbedding s hs q)∈evenTriangle s ↔
      (p,q)∈evenTriangle (s-1) := by
  simp only [mem_evenTriangle,triangleEndEmbedding,Fin.lt_def]
  omega

theorem evenTriangle_middle_left_row (s : ℕ) (hs : 2 ≤ s) (q : Fin (2*s)) :
    (⟨s-1,by omega⟩,q)∈evenTriangle s ↔ q.val<s-1 := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem evenTriangle_middle_right_row (s : ℕ) (hs : 2 ≤ s) (q : Fin (2*s)) :
    (⟨s,by omega⟩,q)∈evenTriangle s ↔ s<q.val := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem evenTriangle_first_column (s : ℕ) (hs : 2 ≤ s) (p : Fin (2*s)) :
    (p,⟨0,by omega⟩)∈evenTriangle s ↔ 0<p.val ∧ p.val<s := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem evenTriangle_last_column (s : ℕ) (hs : 2 ≤ s) (p : Fin (2*s)) :
    (p,⟨2*s-1,by omega⟩)∈evenTriangle s ↔ s ≤ p.val ∧ p.val<2*s-1 := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem triangleMiddleEmbedding_range (s : ℕ) (hs : 2 ≤ s) (i : Fin (2*s)) :
    (∃p, triangleMiddleEmbedding s hs p=i) ↔ i.val≠s-1 ∧ i.val≠s := by
  constructor
  · rintro ⟨p,rfl⟩
    exact triangleMiddleEmbedding_avoids s hs p
  · intro h
    by_cases hi : i.val<s-1
    · refine ⟨⟨i.val,by omega⟩,?_⟩
      apply Fin.ext
      simp [triangleMiddleEmbedding,hi]
    · refine ⟨⟨i.val-2,by omega⟩,?_⟩
      apply Fin.ext
      simp only [triangleMiddleEmbedding]
      split_ifs <;> omega

theorem triangleEndEmbedding_range (s : ℕ) (hs : 2 ≤ s) (i : Fin (2*s)) :
    (∃p, triangleEndEmbedding s hs p=i) ↔ i.val≠0 ∧ i.val≠2*s-1 := by
  constructor
  · rintro ⟨p,rfl⟩
    exact triangleEndEmbedding_avoids s hs p
  · intro h
    refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [triangleEndEmbedding]
    omega

theorem evenTriangle_middle_left_card (s : ℕ) (hs : 2 ≤ s) :
    (Finset.univ.filter (fun q : Fin (2*s) => (⟨s-1,by omega⟩,q)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun q : Fin (2*s) => (⟨s-1,by omega⟩,q)∈evenTriangle s)=
      Finset.Iio (⟨s-1,by omega⟩ : Fin (2*s)) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,
      evenTriangle_middle_left_row s hs,Fin.lt_def]
  rw [he,Fin.card_Iio]

theorem evenTriangle_middle_right_card (s : ℕ) (hs : 2 ≤ s) :
    (Finset.univ.filter (fun q : Fin (2*s) => (⟨s,by omega⟩,q)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun q : Fin (2*s) => (⟨s,by omega⟩,q)∈evenTriangle s)=
      Finset.Ioi (⟨s,by omega⟩ : Fin (2*s)) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ioi,
      evenTriangle_middle_right_row s hs,Fin.lt_def]
  rw [he,Fin.card_Ioi]
  dsimp
  omega

theorem evenTriangle_first_column_card (s : ℕ) (hs : 2 ≤ s) :
    (Finset.univ.filter (fun p : Fin (2*s) => (p,⟨0,by omega⟩)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun p : Fin (2*s) => (p,⟨0,by omega⟩)∈evenTriangle s)=
      Finset.Ioo (⟨0,by omega⟩ : Fin (2*s)) ⟨s,by omega⟩ := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ioo,
      evenTriangle_first_column s hs,Fin.lt_def]
  rw [he,Fin.card_Ioo]
  simp

theorem evenTriangle_last_column_card (s : ℕ) (hs : 2 ≤ s) :
    (Finset.univ.filter (fun p : Fin (2*s) => (p,⟨2*s-1,by omega⟩)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun p : Fin (2*s) => (p,⟨2*s-1,by omega⟩)∈evenTriangle s)=
      Finset.Ico (⟨s,by omega⟩ : Fin (2*s)) ⟨2*s-1,by omega⟩ := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ico,
      evenTriangle_last_column s hs,Fin.le_def,Fin.lt_def]
  rw [he,Fin.card_Ico]
  dsimp
  omega

theorem evenTriangle_two : evenTriangle 2 = {((1 : Fin 4),0),(2,3)} := by
  ext ⟨p,q⟩
  fin_cases p <;> fin_cases q <;> decide

theorem evenTriangle_two_distinct_coordinates (node : Fin 4 → ℝ)
    (hn : Function.Injective node) : node 1≠node 2 ∧ node 0≠node 3 := by
  constructor <;> exact hn.ne (by decide)

end Paper170

end
end

section

/-! The literal row and column elimination used in the even-node proof. -/
noncomputable section
open PolynomialModule Zarankiewicz
namespace Paper170

theorem mem_rectangle_of_toBiPolynomial_bounded (a b : ℕ) (P : Poly2)
    (hP : BiBounded (a+1) (b+1) (toBiPolynomial P)) : P∈rectangle a b := by
  rw [rectangle_membership]
  constructor
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    by_contra h
    have hz := hP.1 (m 0) (by omega)
    have hc : biCoeff (toBiPolynomial P) (m 0) (m 1)=0 := by
      simp [biCoeff,hz]
    rw [toBiPolynomial_coeff] at hc
    have he : exponentPair.symm (m 0,m 1)=m := exponentPair.symm_apply_apply m
    rw [he] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    by_contra h
    have hc := hP.2 (m 0) (m 1) (by omega)
    change biCoeff (toBiPolynomial P) (m 0) (m 1)=0 at hc
    rw [toBiPolynomial_coeff] at hc
    have he : exponentPair.symm (m 0,m 1)=m := exponentPair.symm_apply_apply m
    rw [he] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem bi_factor_two_rows (r s : ℕ) (P : BiPoly)
    (hP : BiBounded (r+2) s P) (a b : ℝ) (hab : a≠b)
    (ha : eval a P=0) (hb : eval b P=0) :
    ∃R : BiPoly, BiBounded r s R ∧ mulRoot a (mulRoot b R)=P := by
  obtain ⟨Q,hQ,hQP⟩ := bi_factor_row (r+1) s P hP a ha
  have hbQ : eval b Q=0 := by
    rw [←hQP,eval_mulRoot] at hb
    exact (smul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hab.symm)
  obtain ⟨R,hR,hRQ⟩ := bi_factor_row r s Q hQ b hbQ
  exact ⟨R,hR,by rw [hRQ,hQP]⟩

theorem evenTriangle_middle_rows_zero (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded s (s-1) P)
    (hv : ∀p q, (p,q)∈evenTriangle s → biEval (node p) (node q) P=0) :
    eval (node ⟨s-1,by omega⟩) P=0 ∧ eval (node ⟨s,by omega⟩) P=0 := by
  constructor
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨i.val,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      exact Fin.ext (show i.val=j.val from congrArg (fun x : Fin (2*s) => x.val) h))) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer hP (node ⟨s-1,by omega⟩)
    · intro i _
      apply hv
      rw [evenTriangle_middle_left_row s hs]
      exact i.isLt
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨s+1+i.val,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [f] at this
      omega)) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer hP (node ⟨s,by omega⟩)
    · intro i _
      apply hv
      rw [evenTriangle_middle_right_row s hs]
      dsimp [f]
      omega

theorem evenTriangle_end_columns_zero (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded (s-1) s P)
    (hv : ∀p q, (p,q)∈evenTriangle s → biEval (node p) (node q) P=0) :
    eval (node ⟨0,by omega⟩) (swapBi P)=0 ∧
      eval (node ⟨2*s-1,by omega⟩) (swapBi P)=0 := by
  constructor
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨i.val+1,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [f] at this
      omega)) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer (biBounded_swap hP) (node ⟨0,by omega⟩)
    · intro i _
      change biEval _ _ (swapBi P)=0
      rw [biEval_swap]
      apply hv
      rw [evenTriangle_first_column s hs]
      dsimp [f]
      omega
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨s+i.val,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [f] at this
      omega)) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer (biBounded_swap hP) (node ⟨2*s-1,by omega⟩)
    · intro i _
      change biEval _ _ (swapBi P)=0
      rw [biEval_swap]
      apply hv
      rw [evenTriangle_last_column s hs]
      dsimp [f]
      omega

end Paper170

end
end

section

noncomputable section
open PolynomialModule Zarankiewicz MvPolynomial
namespace Paper170

theorem evalTwo_ext {P Q : Poly2} (h : ∀u v, evalTwo u v P=evalTwo u v Q) : P=Q := by
  apply MvPolynomial.funext
  intro t
  have ht : t = ![t 0,t 1] := by ext i; fin_cases i <;> rfl
  rw [ht]
  exact h (t 0) (t 1)

theorem evenTriangle_row_factorization (s : ℕ) (hs : 3 ≤ s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P∈rectangle (s-1) (s-2))
    (hv : ∀p q, (p,q)∈evenTriangle s → evalTwo (node p) (node q) P=0) :
    ∃R : Poly2, R∈rectangle (s-3) (s-2) ∧
      P=(X 0-C (node ⟨s-1,by omega⟩))*(X 0-C (node ⟨s,by omega⟩))*R ∧
      ∀p q, (p,q)∈evenTriangle (s-1) →
        evalTwo (node (triangleMiddleEmbedding s (by omega) p))
          (node (triangleMiddleEmbedding s (by omega) q)) R=0 := by
  have hB : BiBounded s (s-1) (toBiPolynomial P) := by
    convert toBiPolynomial_bounded (s-1) (s-2) P hP using 1 <;> omega
  have hV : ∀p q, (p,q)∈evenTriangle s →
      biEval (node p) (node q) (toBiPolynomial P)=0 := by
    simpa only [toBiPolynomial_eval] using hv
  obtain ⟨hleft,hright⟩ := evenTriangle_middle_rows_zero s (by omega) node hn _ hB hV
  obtain ⟨Q,hQ,hQP⟩ := bi_factor_two_rows (s-2) (s-1) (toBiPolynomial P)
    (by convert hB using 1; omega) (node ⟨s-1,by omega⟩) (node ⟨s,by omega⟩)
    (hn.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)) hleft hright
  let R := toBiPolynomial.symm Q
  have hR : R∈rectangle (s-3) (s-2) := by
    apply mem_rectangle_of_toBiPolynomial_bounded
    dsimp [R]
    rw [LinearEquiv.apply_symm_apply]
    convert hQ using 1 <;> omega
  have hf : P=(X 0-C (node ⟨s-1,by omega⟩))*(X 0-C (node ⟨s,by omega⟩))*R := by
    apply evalTwo_ext
    intro u v
    rw [←toBiPolynomial_eval,hQP.symm,biEval_mulRoot,biEval_mulRoot]
    have hQR : biEval u v Q=evalTwo u v R := by
      rw [←toBiPolynomial_eval]
      simp only [R,LinearEquiv.apply_symm_apply]
    rw [hQR]
    simp [evalTwo,mul_assoc]
  refine ⟨R,hR,hf,?_⟩
  intro p q hpq
  have hzero := hv (triangleMiddleEmbedding s (by omega) p)
    (triangleMiddleEmbedding s (by omega) q)
    ((evenTriangle_delete_middle s (by omega) p q).mpr hpq)
  rw [hf] at hzero
  have ha := triangleMiddleEmbedding_avoids s (by omega) p
  have h₁ : node (triangleMiddleEmbedding s (by omega) p)-node ⟨s-1,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.1 (congrArg Fin.val h)))
  have h₂ : node (triangleMiddleEmbedding s (by omega) p)-node ⟨s,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.2 (congrArg Fin.val h)))
  change (MvPolynomial.aeval _ _) = 0 at hzero
  simp only [map_mul,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
    Matrix.cons_val_zero,Algebra.algebraMap_self,RingHom.id_apply] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero h₁ h₂)

theorem evenTriangle_column_factorization (s : ℕ) (hs : 3 ≤ s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P∈rectangle (s-2) (s-1))
    (hv : ∀p q, (p,q)∈evenTriangle s → evalTwo (node p) (node q) P=0) :
    ∃R : Poly2, R∈rectangle (s-2) (s-3) ∧
      P=(X 1-C (node ⟨0,by omega⟩))*(X 1-C (node ⟨2*s-1,by omega⟩))*R ∧
      ∀p q, (p,q)∈evenTriangle (s-1) →
        evalTwo (node (triangleEndEmbedding s (by omega) p))
          (node (triangleEndEmbedding s (by omega) q)) R=0 := by
  have hB : BiBounded (s-1) s (toBiPolynomial P) := by
    convert toBiPolynomial_bounded (s-2) (s-1) P hP using 1 <;> omega
  have hV : ∀p q, (p,q)∈evenTriangle s →
      biEval (node p) (node q) (toBiPolynomial P)=0 := by
    simpa only [toBiPolynomial_eval] using hv
  obtain ⟨hleft,hright⟩ := evenTriangle_end_columns_zero s (by omega) node hn _ hB hV
  obtain ⟨Q,hQ,hQP⟩ := bi_factor_two_rows (s-2) (s-1) (swapBi (toBiPolynomial P))
    (by convert biBounded_swap hB using 1; omega)
    (node ⟨0,by omega⟩) (node ⟨2*s-1,by omega⟩)
    (hn.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)) hleft hright
  let R := toBiPolynomial.symm (swapBi Q)
  have hR : R∈rectangle (s-2) (s-3) := by
    apply mem_rectangle_of_toBiPolynomial_bounded
    dsimp [R]
    rw [LinearEquiv.apply_symm_apply]
    convert biBounded_swap hQ using 1 <;> omega
  have hf : P=(X 1-C (node ⟨0,by omega⟩))*(X 1-C (node ⟨2*s-1,by omega⟩))*R := by
    apply evalTwo_ext
    intro u v
    rw [←toBiPolynomial_eval,←biEval_swap (toBiPolynomial P),hQP.symm,
      biEval_mulRoot,biEval_mulRoot]
    have hQR : biEval v u Q=evalTwo u v R := by
      rw [←toBiPolynomial_eval]
      simp only [R,LinearEquiv.apply_symm_apply,biEval_swap]
    rw [hQR]
    simp [evalTwo,mul_assoc]
  refine ⟨R,hR,hf,?_⟩
  intro p q hpq
  have hzero := hv (triangleEndEmbedding s (by omega) p)
    (triangleEndEmbedding s (by omega) q)
    ((evenTriangle_delete_ends s (by omega) p q).mpr hpq)
  rw [hf] at hzero
  have ha := triangleEndEmbedding_avoids s (by omega) q
  have h₁ : node (triangleEndEmbedding s (by omega) q)-node ⟨0,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.1 (congrArg Fin.val h)))
  have h₂ : node (triangleEndEmbedding s (by omega) q)-node ⟨2*s-1,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.2 (congrArg Fin.val h)))
  change (MvPolynomial.aeval _ _) = 0 at hzero
  simp only [map_mul,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
    Matrix.cons_val_one,Matrix.cons_val_zero,Algebra.algebraMap_self,RingHom.id_apply] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero h₁ h₂)

end Paper170

end
end

end OAI

namespace OAI

/-! Order-detecting interpolation and its kernel. -/

section

/-! The order pairing as a nonzero diagonal pairing on the even two-triangle set. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def evenTriangleWeight (s : ℕ) (node : Fin (2*s) → ℝ) (a : EvenTriangleCoord s) : ℝ :=
  (if a.val.1.val < s then -1 else 1) * (node a.val.1-node a.val.2) /
    (Zarankiewicz.derivativeAtNode node a.val.1 * Zarankiewicz.derivativeAtNode node a.val.2)

theorem evenTriangleWeight_ne_zero (s : ℕ) (node : Fin (2*s) → ℝ)
    (hn : Function.Injective node) (a : EvenTriangleCoord s) : evenTriangleWeight s node a ≠ 0 := by
  have ha := (mem_evenTriangle s a.val.1 a.val.2).mp a.property
  have hne : a.val.1 ≠ a.val.2 := by rcases ha with ha | ha; exact ne_of_gt ha.2; exact ne_of_lt ha.2
  unfold evenTriangleWeight
  apply div_ne_zero
  · apply mul_ne_zero
    · split_ifs <;> norm_num
    · exact sub_ne_zero.mpr (hn.ne hne)
  · exact mul_ne_zero (Zarankiewicz.derivativeAtNode_ne_zero node hn _)
      (Zarankiewicz.derivativeAtNode_ne_zero node hn _)

theorem shifted_halfOrder (s : ℕ) (node : Fin (2*s) → ℝ) (p q : Fin (2*s)) :
    (halfOrder inferInstance p q + (if p.val < s then -(1/2) else 1/2)) * (node p-node q) =
      if (p,q) ∈ evenTriangle s then
        (if p.val < s then -1 else 1) * (node p-node q) else 0 := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have hqp := not_lt_of_ge (le_of_lt hpq)
    by_cases hp : p.val < s <;>
      simp [halfOrder, hpq, hqp, mem_evenTriangle, hp, not_lt.mp]
    ring
  · simp [halfOrder]
  · have hpq := not_lt_of_ge (le_of_lt hqp)
    by_cases hp : p.val < s <;>
      simp [halfOrder, hpq, hqp, mem_evenTriangle, hp, not_lt.mp]
    ring

theorem orderPairing_triangle (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) (A B : Poly2)
    (hA : A ∈ rectangle (s-1) (s-2)) (hB : B ∈ rectangle (s-2) (s-1)) :
    orderPairing node inferInstance A B = ∑ a : EvenTriangleCoord s,
      evenTriangleWeight s node a * evalTwo (node a.val.1) (node a.val.2) A *
        evalTwo (node a.val.1) (node a.val.2) B := by
  have hshift := pairing_row_column_invariant s hs (by simp) node hn (halfOrder inferInstance)
    (fun p => if p.val < s then -(1/2) else 1/2) (fun _ => 0) A B hA hB
  simp only [add_zero] at hshift
  rw [orderPairing, ← hshift]
  let F (a : Fin (2*s) × Fin (2*s)) : ℝ :=
    (if a.1.val < s then -1 else 1) * (node a.1-node a.2) /
      (Zarankiewicz.derivativeAtNode node a.1 * Zarankiewicz.derivativeAtNode node a.2) *
      evalTwo (node a.1) (node a.2) A * evalTwo (node a.1) (node a.2) B
  change _ = ∑ a : EvenTriangleCoord s, F a.val
  calc
    _ = ∑ a ∈ evenTriangle s, F a := by
      unfold weightedPairing
      simp_rw [shifted_halfOrder]
      rw [evenTriangle, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      by_cases ha : (p,q) ∈ evenTriangle s
      · have hh := (mem_evenTriangle s p q).mp ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hh, F]
      · have hh := (mem_evenTriangle s p q).not.mp ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_right hh, zero_div, zero_mul]
    _ = ∑ a : EvenTriangleCoord s, F a.val := (Finset.sum_coe_sort (evenTriangle s) F).symm

theorem derivativeAtNode_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (node : ι → ℝ) (e : κ ≃ ι) (p : κ) :
    Zarankiewicz.derivativeAtNode (node ∘ e) p = Zarankiewicz.derivativeAtNode node (e p) := by
  classical
  have h : Zarankiewicz.nodePolynomial (node ∘ e) = Zarankiewicz.nodePolynomial node := by
    unfold Zarankiewicz.nodePolynomial
    exact e.prod_comp (fun i => (Polynomial.X-Polynomial.C (node i) : Polynomial ℝ))
  simp only [Zarankiewicz.derivativeAtNode, h, Function.comp_apply]

theorem weightedPairing_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (node : ι → ℝ) (e : κ ≃ ι) (K : ι → ι → ℝ) (A B : Poly2) :
    weightedPairing (node ∘ e) (fun p q => K (e p) (e q)) A B = weightedPairing node K A B := by
  unfold weightedPairing
  simp_rw [derivativeAtNode_equiv, Function.comp_apply]
  let F (p q : ι) : ℝ := K p q * (node p-node q) /
    (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q) *
    evalTwo (node p) (node q) A * evalTwo (node p) (node q) B
  change (∑p : κ, ∑q : κ, F (e p) (e q)) = ∑p : ι, ∑q : ι, F p q
  calc
    _ = ∑p : κ, ∑q : ι, F (e p) q := by
      apply Finset.sum_congr rfl
      intro p _
      exact e.sum_comp (F (e p))
    _ = _ := e.sum_comp (fun p => ∑q, F p q)

theorem orderPairing_orderIso {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (node : ι → ℝ) (e : κ ≃o ι) (A B : Poly2) :
    orderPairing (node ∘ e) inferInstance A B = orderPairing node inferInstance A B := by
  have h : (fun p q => halfOrder inferInstance (e p) (e q)) = halfOrder (inferInstance : LinearOrder κ) := by
    funext p q
    simp only [halfOrder, e.lt_iff_lt]
  rw [orderPairing, ← h]
  exact weightedPairing_equiv node e.toEquiv _ A B

end Paper170

end
end

section

/-! Nonsingularity of the weighted half-order pairing for every node order. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem order_pairing_nonsingular_fin (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) :
    (∀ A ∈ rectangle (s-1) (s-2),
      (∀ B ∈ rectangle (s-2) (s-1), orderPairing node inferInstance A B = 0) → A=0) ∧
    (∀ B ∈ rectangle (s-2) (s-1),
      (∀ A ∈ rectangle (s-1) (s-2), orderPairing node inferInstance A B = 0) → B=0) := by
  classical
  obtain ⟨hfirst,hsecond⟩ := two_triangle_interpolation s hs node hn
  constructor
  · intro A hA hz
    apply evenTriangle_vanish_first s hs node hn A hA
    intro i j hij
    let a : EvenTriangleCoord s := ⟨(i,j),hij⟩
    obtain ⟨B,hB⟩ := hsecond.surjective (Pi.single a (1:ℝ))
    have he (b : EvenTriangleCoord s) : evalTwo (node b.val.1) (node b.val.2) B.val =
        (Pi.single a (1:ℝ) : EvenTriangleCoord s → ℝ) b := congrFun hB b
    have hzero := hz B.val B.property
    rw [orderPairing_triangle s hs node hn A B.val hA B.property] at hzero
    simp_rw [he] at hzero
    have hv : evenTriangleWeight s node a * evalTwo (node i) (node j) A = 0 := by
      simpa [Pi.single_apply, mul_ite, a] using hzero
    exact (mul_eq_zero.mp hv).resolve_left (evenTriangleWeight_ne_zero s node hn a)
  · intro B hB hz
    apply evenTriangle_vanish_second s hs node hn B hB
    intro i j hij
    let a : EvenTriangleCoord s := ⟨(i,j),hij⟩
    obtain ⟨A,hA⟩ := hfirst.surjective (Pi.single a (1:ℝ))
    have he (b : EvenTriangleCoord s) : evalTwo (node b.val.1) (node b.val.2) A.val =
        (Pi.single a (1:ℝ) : EvenTriangleCoord s → ℝ) b := congrFun hA b
    have hzero := hz A.val A.property
    rw [orderPairing_triangle s hs node hn A.val B A.property hB] at hzero
    simp_rw [he] at hzero
    have hv : evenTriangleWeight s node a * evalTwo (node i) (node j) B = 0 := by
      simpa [Pi.single_apply, mul_ite, ite_mul, a] using hzero
    exact (mul_eq_zero.mp hv).resolve_left (evenTriangleWeight_ne_zero s node hn a)

theorem order_pairing_nonsingular {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (order : LinearOrder ι) :
    (∀ A ∈ rectangle (s-1) (s-2),
      (∀ B ∈ rectangle (s-2) (s-1), orderPairing node order A B = 0) → A=0) ∧
    (∀ B ∈ rectangle (s-2) (s-1),
      (∀ A ∈ rectangle (s-1) (s-2), orderPairing node order A B = 0) → B=0) := by
  let := order
  let e : Fin (2*s) ≃o ι := Fintype.orderIsoFinOfCardEq ι hc
  obtain ⟨hfirst,hsecond⟩ := order_pairing_nonsingular_fin s hs (node ∘ e) (hn.comp e.injective)
  constructor
  · intro A hA hz
    apply hfirst A hA
    intro B hB
    rw [orderPairing_orderIso node e]
    exact hz B hB
  · intro B hB hz
    apply hsecond B hB
    intro A hA
    rw [orderPairing_orderIso node e]
    exact hz A hA

theorem order_detector {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (order : LinearOrder ι)
    (A : Poly2) (hA : A ∈ rectangle (s-2) (s-2))
    (hzero : ∀ B ∈ rectangle (s-1) (s-1), orderPairing node order A B = 0) : A=0 := by
  apply (order_pairing_nonsingular s hs hc node hn order).1 A
  · rw [rectangle_membership] at hA ⊢
    exact ⟨hA.1.trans (by omega), hA.2⟩
  · intro B hB
    apply hzero B
    rw [rectangle_membership] at hB ⊢
    exact ⟨hB.1.trans (by omega), hB.2⟩

end Paper170

end
end

end OAI

namespace OAI

/-! Vertex specialization, local interpolation tests, and kernel vanishing. -/

section

/-! Evaluation symmetries and genuine degree bounds after fixing a vertex. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalFour_swapFirst (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapFirstPair P) = evalFour u x y v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [swapFirstPair, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [swapFirstPair, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.rename_X] at hP ⊢
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![u,x,y,v] _
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![u,x,y,v] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

theorem evalFour_swapSecond (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapSecondPair P) = evalFour x u v y P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [swapSecondPair, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [swapSecondPair, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.rename_X] at hP ⊢
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![x,u,v,y] _
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![x,u,v,y] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

theorem vertexSpecialization_monomial (x : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    vertexSpecialization x (MvPolynomial.monomial m c) =
      MvPolynomial.C (c*x^m 0*x^m 2) * MvPolynomial.X 0^m 1 * MvPolynomial.X 1^m 3 := by
  simp only [vertexSpecialization, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four]
    ring
  · intro i
    simp

theorem vertexSpecialization_rectangle (s : ℕ) (P : endpointSymmetricSpace s) (x : ℝ) :
    vertexSpecialization x P.val ∈ rectangle (s-2) (s-2) := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).1
  have hb (k : Fin 2) : (vertexSpecialization x P.val).degreeOf k ≤ s-2 := by
    rw [P.val.as_sum, map_sum]
    apply (MvPolynomial.degreeOf_sum_le k _ _).trans
    apply Finset.sup_le
    intro m hm
    rw [vertexSpecialization_monomial]
    have h1 := MvPolynomial.degreeOf_le_iff.mp (hp 1) m hm
    have h3 := MvPolynomial.degreeOf_le_iff.mp (hp 3) m hm
    have hmul := MvPolynomial.degreeOf_mul_le k
      (MvPolynomial.C (P.val.coeff m*x^m 0*x^m 2)*MvPolynomial.X 0^m 1)
      (MvPolynomial.X 1^m 3)
    have hC := MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X 0^m 1 : Poly2) k
      (P.val.coeff m*x^m 0*x^m 2)
    have hpow0 := MvPolynomial.degreeOf_pow_le k (MvPolynomial.X 0 : Poly2) (m 1)
    have hpow1 := MvPolynomial.degreeOf_pow_le k (MvPolynomial.X 1 : Poly2) (m 3)
    fin_cases k <;> norm_num [MvPolynomial.degreeOf_X, Fin.ext_iff] at hpow0 hpow1 hmul hC ⊢ <;> omega
  exact (rectangle_membership _ _ _).mpr ⟨hb 0,hb 1⟩

theorem neighbor_nodePolynomial {n : ℕ} (node : Fin n → ℝ) (i : Fin n) :
    Zarankiewicz.nodePolynomial (fun p : {j : Fin n // j ≠ i} => node p.val) =
      omittedNodePolynomial node i := by
  classical
  unfold Zarankiewicz.nodePolynomial omittedNodePolynomial
  exact (Finset.prod_subtype (Finset.univ.erase i) (by simp)
    (fun j => Polynomial.X-Polynomial.C (node j))).symm

theorem neighbor_nodeWeight {n : ℕ} (node : Fin n → ℝ) (hn : Function.Injective node)
    (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    nodeWeight (fun q : {j : Fin n // j ≠ i} => node q.val) p =
      (node p.val-node i)*nodeWeight node p.val := by
  classical
  rw [omitted_node_weight node hn i p.val p.property.symm]
  unfold nodeWeight Zarankiewicz.derivativeAtNode
  rw [neighbor_nodePolynomial]

theorem sum_away {n : ℕ} (i : Fin n) (f : Fin n → ℝ) (hi : f i=0) :
    (∑j, f j) = ∑j : {j : Fin n // j ≠ i}, f j.val := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi, add_zero]
  exact Finset.sum_subtype (Finset.univ.erase i) (by simp) f

end Paper170

end
end

section

/-! The kernel vanishes on every orientation of an independent supported edge pair. -/
noncomputable section
namespace Paper170

theorem kernel_ordered_eval_zero {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P = 0)
    {i p k q : Fin n} (hip : i<p) (hkq : k<q) (hik : i≠k) (hiq : i≠q)
    (hpk : p≠k) (hpq : p≠q) (hJ : J i p k q ≠ 0) :
    evalFour (node i) (node p) (node k) (node q) P.val = 0 := by
  classical
  let a : SupportCoord J := ⟨((i,p),(k,q)), by
    simp only [supportedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hip,hkq,hik,hiq,hpk,hpq,hJ⟩⟩
  exact congrFun hP a

theorem kernel_independent_eval_zero {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P = 0)
    {i p k q : Fin n} (hip : i≠p) (hkq : k≠q) (hik : i≠k) (hiq : i≠q)
    (hpk : p≠k) (hpq : p≠q) (hJ : J i p k q ≠ 0) :
    evalFour (node i) (node p) (node k) (node q) P.val = 0 := by
  have hsym := (symmetric_space_membership s P.val).mp P.property
  have he1 (x u y v : ℝ) : evalFour x u y v P.val = evalFour u x y v P.val := by
    rw [← evalFour_swapFirst, hsym.2.1]
  have he2 (x u y v : ℝ) : evalFour x u y v P.val = evalFour x u v y P.val := by
    rw [← evalFour_swapSecond, hsym.2.2]
  rcases lt_or_gt_of_ne hip with hip | hpi
  · rcases lt_or_gt_of_ne hkq with hkq | hqk
    · exact kernel_ordered_eval_zero node J P hP hip hkq hik hiq hpk hpq hJ
    · rw [he2]
      apply kernel_ordered_eval_zero node J P hP hip hqk hiq hik hpq hpk
      rw [hreverseRight i p k q]
      exact neg_ne_zero.mpr hJ
  · rw [he1]
    rcases lt_or_gt_of_ne hkq with hkq | hqk
    · apply kernel_ordered_eval_zero node J P hP hpi hkq hpk hpq hik hiq
      rw [hreverseLeft i p k q]
      exact neg_ne_zero.mpr hJ
    · rw [he2]
      apply kernel_ordered_eval_zero node J P hP hpi hqk hpq hpk hiq hik
      rw [hreverseLeft i p q k, hreverseRight i p k q, neg_neg]
      exact hJ

end Paper170

end
end

section

/-! The local test polynomial reduces the global tensor sum to its adjacent-edge pairings. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalFour_liftUnivariate (x u y v : ℝ) (i : Fin 4) (U : Polynomial ℝ) :
    evalFour x u y v (liftUnivariate i U) = U.eval (![x,u,y,v] i) := by
  change MvPolynomial.aeval ![x,u,y,v] (Polynomial.aeval (MvPolynomial.X i) U) = _
  rw [← Polynomial.aeval_algHom_apply]
  simp

theorem evalFour_liftBivariate13 (x u y v : ℝ) (B : Poly2) :
    evalFour x u y v (liftBivariate 1 3 B) = evalTwo u v B := by
  have h : (MvPolynomial.aeval ![x,u,y,v]).comp
      (MvPolynomial.aeval ![MvPolynomial.X 1,MvPolynomial.X 3] : Poly2 →ₐ[ℝ] Poly4) =
      MvPolynomial.aeval ![u,v] := by
    ext i
    fin_cases i <;> simp
  exact congrArg (fun f : Poly2 →ₐ[ℝ] ℝ => f B) h

theorem evalFour_localTestPolynomial (x u y v : ℝ) (P : Poly4)
    (U V : Polynomial ℝ) (B : Poly2) :
    evalFour x u y v (localTestPolynomial P U V B) =
      evalFour x u y v P * (u-v) * (u-y) * (v-x) *
        U.eval x * V.eval y * evalTwo u v B := by
  have hm (Q R : Poly4) : evalFour x u y v (Q*R) = evalFour x u y v Q*evalFour x u y v R :=
    map_mul (MvPolynomial.aeval ![x,u,y,v]) Q R
  simp only [localTestPolynomial, hm, evalFour_liftUnivariate, evalFour_liftBivariate13]
  simp [evalFour]

def vertexTestSummand {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (H : Poly4)
    (i p k q : Fin n) : ℝ :=
  J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q *
    evalFour (node i) (node p) (node k) (node q) H

theorem vertexTestSummand_offDiagonal {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P=0)
    (U V : Polynomial ℝ) (B : Poly2) (i p k q : Fin n) (hik : i≠k) :
    vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q = 0 := by
  by_cases hip : i=p
  · subst p
    simp [vertexTestSummand, hloopLeft]
  by_cases hkq : k=q
  · subst q
    simp [vertexTestSummand, hloopRight]
  by_cases hpq : p=q
  · subst q
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hpk : p=k
  · subst k
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hiq : i=q
  · subst q
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hJ : J i p k q=0
  · simp [vertexTestSummand, hJ]
  have hz := kernel_independent_eval_zero node J hreverseLeft hreverseRight P hP
    hip hkq hik hiq hpk hpq hJ
  simp [vertexTestSummand, evalFour_localTestPolynomial, hz]

theorem orderPairing_weight_form {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (order : LinearOrder ι) (A B : Poly2) :
    orderPairing node order A B = ∑p, ∑q,
      halfOrder order p q * (node p-node q) * nodeWeight node p * nodeWeight node q *
        evalTwo (node p) (node q) A * evalTwo (node p) (node q) B := by
  simp only [orderPairing, weightedPairing, nodeWeight, div_eq_mul_inv, mul_inv]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem vertexTestSummand_diagonal {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i})
    (hlocal : ∀i (p q : {j : Fin n // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (P : Poly4) (U V : Polynomial ℝ) (B : Poly2) (i : Fin n)
    (p q : {j : Fin n // j≠i}) :
    vertexTestSummand node J (localTestPolynomial P U V B) i p.val i q.val =
      (nodeWeight node i)^2 * U.eval (node i) * V.eval (node i) *
      (halfOrder (orders i) p q * (node p.val-node q.val) *
        nodeWeight (fun j : {j : Fin n // j≠i} => node j.val) p *
        nodeWeight (fun j : {j : Fin n // j≠i} => node j.val) q *
        evalTwo (node p.val) (node q.val) (vertexSpecialization (node i) P) *
        evalTwo (node p.val) (node q.val) B) := by
  rw [vertexTestSummand, evalFour_localTestPolynomial, hlocal]
  rw [neighbor_nodeWeight node hn, neighbor_nodeWeight node hn, vertex_eval]
  ring

theorem polynomialTest_local_reduction {n s : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i})
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (hlocal : ∀i (p q : {j : Fin n // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P=0)
    (U V : Polynomial ℝ) (B : Poly2) :
    polynomialTest node J (localTestPolynomial P.val U V B) =
      ∑i, (nodeWeight node i)^2 * U.eval (node i) * V.eval (node i) *
        orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P.val) B := by
  change (∑i, ∑p, ∑k, ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q)=_
  apply Finset.sum_congr rfl
  intro i _
  have hk (p : Fin n) :
      (∑k, ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q) =
      ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p i q := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro q _
      exact vertexTestSummand_offDiagonal node J hloopLeft hloopRight hreverseLeft hreverseRight
        P hP U V B i p k q hki.symm
    · simp
  simp_rw [hk]
  rw [sum_away i _ (by simp [vertexTestSummand,hloopLeft])]
  have hq (p : {j : Fin n // j≠i}) :
      (∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p.val i q) =
      ∑q : {j : Fin n // j≠i}, vertexTestSummand node J (localTestPolynomial P.val U V B) i p.val i q.val :=
    sum_away i _ (by simp [vertexTestSummand,hloopRight])
  simp_rw [hq, vertexTestSummand_diagonal node hn J orders hlocal]
  rw [orderPairing_weight_form]
  simp only [Finset.mul_sum]

end Paper170

end
end

section

/-! Lagrange isolation of each vertex and the full kernel vertex-vanishing theorem. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def vertexPairingFunctional {n : ℕ} (node : Fin n → ℝ)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i}) (P : Poly4) (B : Poly2) :
    Polynomial ℝ →ₗ[ℝ] ℝ :=
  ∑i, ((nodeWeight node i)^2 *
    orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
      (vertexSpecialization (node i) P) B) • (Polynomial.aeval (node i)).toLinearMap

theorem vertexPairingFunctional_apply {n : ℕ} (node : Fin n → ℝ)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i}) (P : Poly4) (B : Poly2)
    (W : Polynomial ℝ) :
    vertexPairingFunctional node orders P B W =
      ∑i, (nodeWeight node i)^2 * W.eval (node i) *
        orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P) B := by
  simp only [vertexPairingFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

section CrossingTensor
variable {s : ℕ} (hs : 2 ≤ s) (node : Fin (2*s+1) → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor (2*s+1))
    (orders : ∀i : Fin (2*s+1), LinearOrder {j : Fin (2*s+1) // j≠i})
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (hskew : ∀i p k q, J k q i p = -J i p k q)
    (hlocal : ∀i (p q : {j : Fin (2*s+1) // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (htests : ∀H ∈ box4 (2*s-1), polynomialTest node J H=0)

include hs hnode hloopLeft hloopRight hreverseLeft hreverseRight hlocal htests in
theorem vertexPairingFunctional_zero (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) (B : Poly2) (hB : B∈rectangle (s-1) (s-1))
    (W : Polynomial ℝ) (hW : W∈Polynomial.degreeLT ℝ (2*s+1)) :
    vertexPairingFunctional node orders P.val B W=0 := by
  have hspan : Submodule.span ℝ {Q : Polynomial ℝ | ∃U V : Polynomial ℝ,
      U.natDegree ≤ s ∧ V.natDegree ≤ s ∧ Q=U*V} ≤
        LinearMap.ker (vertexPairingFunctional node orders P.val B) := by
    rw [Submodule.span_le]
    rintro Q ⟨U,V,hU,hV,rfl⟩
    change vertexPairingFunctional node orders P.val B (U*V)=0
    have hz := htests (localTestPolynomial P.val U V B) (local_test_degree s hs P.val P.property U V hU hV B hB)
    rw [polynomialTest_local_reduction node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hlocal P hP U V B] at hz
    rw [vertexPairingFunctional_apply]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul]
    ring
  rw [products_span_degree] at hspan
  exact hspan hW

include hs hnode hloopLeft hloopRight hreverseLeft hreverseRight hlocal htests in
theorem kernel_local_pairing_zero (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) (i : Fin (2*s+1)) (B : Poly2)
    (hB : B∈rectangle (s-1) (s-1)) :
    orderPairing (fun j : {j : Fin (2*s+1) // j≠i} => node j.val) (orders i)
      (vertexSpecialization (node i) P.val) B = 0 := by
  classical
  let W := Lagrange.basis Finset.univ node i
  have hW : W∈Polynomial.degreeLT ℝ (2*s+1) := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Lagrange.degree_basis hnode.injOn (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel_right]
    exact_mod_cast (show 2*s < 2*s+1 by omega)
  have hz := vertexPairingFunctional_zero hs node hnode J orders hloopLeft hloopRight
    hreverseLeft hreverseRight hlocal htests P hP B hB W hW
  rw [vertexPairingFunctional_apply] at hz
  have heq : (∑j, (nodeWeight node j)^2 * W.eval (node j) *
      orderPairing (fun k : {k : Fin (2*s+1) // k≠j} => node k.val) (orders j)
        (vertexSpecialization (node j) P.val) B) =
      (nodeWeight node i)^2 *
        orderPairing (fun j : {j : Fin (2*s+1) // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P.val) B := by
    rw [Finset.sum_eq_single i]
    · rw [show W.eval (node i)=1 from Lagrange.eval_basis_self hnode.injOn (Finset.mem_univ i), mul_one]
    · intro j _ hji
      rw [show W.eval (node j)=0 from Lagrange.eval_basis_of_ne hji.symm (Finset.mem_univ j)]
      simp
    · simp
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (weight_nonzero node hnode i))

include hs hnode orders hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests in
theorem kernel_vertex_vanishing (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) : ∀i, vertexSpecialization (node i) P.val=0 := by
  have hlocal' : ∀j (p q : {j' : Fin (2*s+1) // j'≠j}),
      J j p.val j q.val=halfOrder (orders j) p q := by
    intro j p q
    by_cases hpq : p=q
    · subst q
      have hh := hskew j p.val j p.val
      have hz : J j p.val j p.val=0 := by linarith
      have hpp := @lt_irrefl _ (orders j).toPartialOrder.toPreorder p
      simp only [hz,halfOrder,ite_eq_right hpp]
    · exact hlocal j p q
  intro i
  apply order_detector s hs (by simp [Fintype.card_subtype_compl])
    (fun j : {j : Fin (2*s+1) // j≠i} => node j.val)
    (hnode.comp Subtype.val_injective) (orders i) _ (vertexSpecialization_rectangle s P (node i))
  intro B hB
  exact kernel_local_pairing_zero hs node hnode J orders hloopLeft hloopRight
    hreverseLeft hreverseRight hlocal' htests P hP i B hB

end CrossingTensor
end Paper170

end
end

end OAI

namespace OAI

/-! Polynomial injectivity and the lower bound on crossing-tensor support. -/

section

/-! The polynomial lower-bound argument for complete graphs. -/
noncomputable section
namespace Paper170
section CrossingTensor

variable {s : ℕ} (hs : 2 ≤ s) (node : Fin (2 * s + 1) → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor (2 * s + 1))
    (orders : ∀ i : Fin (2 * s + 1), LinearOrder {j : Fin (2 * s + 1) // j ≠ i})
    (hloopLeft : ∀ i k q, J i i k q = 0)
    (hloopRight : ∀ i p k, J i p k k = 0)
    (hreverseLeft : ∀ i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀ i p k q, J i p q k = -J i p k q)
    (hskew : ∀ i p k q, J k q i p = -J i p k q)
    (hlocal : ∀ i (p q : {j : Fin (2 * s + 1) // j ≠ i}),
      J i p.val i q.val = halfOrder (orders i) p q)
    (htests : ∀ H ∈ box4 (2 * s - 1), polynomialTest node J H = 0)

include hs hnode orders hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests

theorem kernel_diagonal_vanishing (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P = 0) :
    diagonalSpecialization P.val = 0 :=
  diagonal_zero_of_vertices s node hnode P (kernel_vertex_vanishing hs node hnode J orders
    hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests P hP)

theorem kernel_collision_divisibility (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P = 0) : collisionFactor ∣ P.val :=
  collision_divides_of_diagonal_vanishing s P (kernel_diagonal_vanishing hs node hnode J orders
    hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests P hP)

theorem support_evaluation_injective : Function.Injective (supportEvaluation s node J) :=
  support_evaluation_injective_of_collision hs node hnode J
    (kernel_collision_divisibility hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)

theorem support_cardinality_lower_bound :
    2 * (Nat.choose s 2) ^ 2 ≤ (supportedPairs J).card :=
  support_cardinality_of_injective_isotropic hs node hnode J
    (support_evaluation_injective hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)
    (evaluation_image_isotropic hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)

end CrossingTensor
end Paper170

end
end

end OAI

theorem OMA.solution : OMA.R_arxiv_2009_03418_R1_H2_R2_H1_R1.H1 := by
  intro s hs n T good supp J hJ
  obtain ⟨orders, hll, hlr, hrl, hrr, hsk, hloc, hcyc⟩ := hJ
  let node : Fin (2 * s + 1) → ℝ := fun i => (i.val : ℝ)
  have hn : Function.Injective node := fun i j h => Fin.ext (Nat.cast_injective h)
  have ht : ∀ H ∈ OAI.Paper170.box4 (2 * s - 1),
      OAI.Paper170.polynomialTest node J H = 0 := by
    intro H hH
    have he : 2 * s + 1 - 2 = 2 * s - 1 := by omega
    exact OAI.Paper170.polynomial_cycle_tests (by omega) node hn J hcyc H (he ▸ hH)
  have hl := OAI.Paper170.support_cardinality_lower_bound hs node hn J orders hll hlr hrl hrr
    hsk (fun i p q => by rw [hloc]; rfl) ht
  refine le_of_le_of_eq hl ?_
  unfold OAI.Paper170.supportedPairs
  congr 1
