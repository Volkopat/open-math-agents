import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1
import Mathlib

/-!
# Terminal ports for arbitrary primary pseudoperfect factor counts

Han Wang, arXiv:2605.21518v1, Section 19, uses a five-prime filling
to append four primes to an ambient port, retaining the largest new
prime as the next terminal prime. This reduction starts from the
port `(6,1,7)` and checks the cofactor arithmetic, local solubility,
iteration and exact reciprocal inequalities in Lean.

The remaining inputs are the unbounded positive real witnesses and
prime realization for the resulting five-variable equation.
-/

open Finset

namespace TerminalPort

private def product (S : Finset ℕ) : ℕ := ∏ x ∈ S, x

private def derivative (S : Finset ℕ) : ℕ := ∑ x ∈ S, product (S.erase x)

theorem product_union {S T : Finset ℕ} (hd : Disjoint S T) :
    product (S ∪ T) = product S * product T :=
  Finset.prod_union hd

theorem derivative_union {S T : Finset ℕ} (hd : Disjoint S T) :
    derivative (S ∪ T) = derivative S * product T + product S * derivative T := by
  unfold derivative
  rw [Finset.sum_union hd, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    have hb : x ∉ T := fun ht => Finset.disjoint_left.mp hd hx ht
    have d : Disjoint (S.erase x) T :=
      Disjoint.mono_left (Finset.erase_subset x S) hd
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hb, product_union d]
  · apply Finset.sum_congr rfl
    intro x hx
    have ha : x ∉ S := fun hs => Finset.disjoint_left.mp hd hs hx
    have d : Disjoint S (T.erase x) :=
      Disjoint.mono_right (Finset.erase_subset x T) hd
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem ha, product_union d]

theorem product_erase_mul {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    product (S.erase p) * p = product S :=
  Finset.prod_erase_mul S id hp

theorem congruences_from_identity {S : Finset ℕ} (he : product S = 1 + derivative S) :
    ∀ x ∈ S, x ∣ product (S.erase x) + 1 := by
  intro x hx
  have hdprod : x ∣ product S := Finset.dvd_prod_of_mem id hx
  have hdrest : x ∣ ∑ r ∈ S.erase x, product (S.erase r) := by
    apply Finset.dvd_sum
    intro r hr
    apply Finset.dvd_prod_of_mem id
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1.symm, hx⟩
  have hs := Finset.sum_erase_add S (fun r => product (S.erase r)) hx
  change _ + product (S.erase x) = derivative S at hs
  have hdiff : product S - (∑ r ∈ S.erase x, product (S.erase r)) =
      product (S.erase x) + 1 := by omega
  rw [← hdiff]
  exact Nat.dvd_sub hdprod hdrest

theorem reciprocal_from_identity {S : Finset ℕ}
    (primes : ∀ x ∈ S, x.Prime) (he : product S = 1 + derivative S) :
    (∑ p ∈ S, (1 : ℚ)/p) < 1 := by
  have hp : 0 < product S := Finset.prod_pos (fun x hx => (primes x hx).pos)
  have hpq : (0 : ℚ) < product S := by exact_mod_cast hp
  have hsum : (∑ p ∈ S, (1 : ℚ)/p) * (product S : ℚ) = (derivative S : ℚ) := by
    rw [Finset.sum_mul]
    unfold derivative
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hm
    have part := congrArg (fun n : ℕ => (n : ℚ)) (product_erase_mul hm)
    rw [Nat.cast_mul] at part
    rw [← part]
    have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast (primes p hm).ne_zero
    field_simp
  have hnum : (product S : ℚ) = 1 + derivative S := by exact_mod_cast he
  apply lt_of_mul_lt_mul_right _ hpq.le
  rw [one_mul, hsum]
  linarith

private def ambient (S : Finset ℕ) (c p : ℕ) : Prop :=
  4 < product S ∧ 3 < p ∧ p.Prime ∧
    (∀ q ∈ S, q.Prime ∧ q < p) ∧
    product S = c + derivative S ∧ c*p = product S+1

theorem complete {S : Finset ℕ} {c p : ℕ} (h : ambient S c p) :
    product (insert p S) = 1 + derivative (insert p S) := by
  obtain ⟨_,_,_,hs,hambient,hclose⟩ := h
  have hp : p ∉ S := fun hm => (hs p hm).2.false
  have hd : Disjoint S {p} := Finset.disjoint_singleton_right.mpr hp
  have hset : S ∪ {p} = insert p S := by
    ext q
    simp
  rw [← hset, product_union hd, derivative_union hd]
  have pp : product {p} = p := by simp [product]
  have dd : derivative {p} = 1 := by simp [derivative,product]
  rw [pp,dd,mul_one]
  calc
    product S * p = (c + derivative S) * p := by rw [hambient]
    _ = c*p + derivative S*p := by ring
    _ = 1 + (derivative S*p + product S) := by rw [hclose]; omega

theorem split_fill {S A : Finset ℕ} {c p u : ℕ}
    (h : ambient S c p) (newPrime : u.Prime) (hu : p < u)
    (ordered : ∀ x ∈ A, x.Prime ∧ p < x ∧ x < u)
    (fill : c*(product A*u) = product S*(derivative A*u + product A)+1) :
    ∃ d, ambient (S ∪ A) d u := by
  obtain ⟨hR,hp3,hp,old,hambient,hclose⟩ := h
  have hd : Disjoint S A := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (old x hx).2.le) (ordered x hy).2.1
  let R := product S
  let Q := product A
  let M := R*derivative A
  let d := c*Q-M
  have uq : 0 < u := newPrime.pos
  have res : c*Q*u = M*u + R*Q + 1 := by
    change c * (Q*u) = R * (derivative A*u + Q) + 1 at fill
    calc
      c*Q*u = c*(Q*u) := by ring
      _ = R*(derivative A*u + Q)+1 := fill
      _ = M*u + R*Q + 1 := by dsimp [M]; ring
  have hle : M ≤ c*Q := by
    apply Nat.le_of_mul_le_mul_right _ uq
    rw [res]
    omega
  have hsub : d+M = c*Q := Nat.sub_add_cancel hle
  have close' : d*u = R*Q+1 := by
    have split : d*u + M*u = c*Q*u := by rw [← Nat.add_mul,hsub]
    omega
  have pdis : product (S ∪ A) = R*Q := product_union hd
  have ddis : derivative (S ∪ A) = derivative S*Q + M := derivative_union hd
  have Qpos : 0 < Q := Finset.prod_pos fun x hx => (ordered x hx).1.pos
  have grow : 4 < product (S ∪ A) := by
    rw [pdis]
    exact hR.trans_le (by simpa using Nat.mul_le_mul_left R Qpos)
  refine ⟨d,grow,hp3.trans hu,newPrime,?_,?_,by simpa only [pdis] using close'⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨(old x hx).1, (old x hx).2.trans hu⟩
    · exact ⟨(ordered x hx).1, (ordered x hx).2.2⟩
  · rw [pdis,ddis]
    change R = c + derivative S at hambient
    calc
      R*Q = (c+derivative S)*Q := by rw [hambient]
      _ = (c*Q)+derivative S*Q := by ring
      _ = d+(derivative S*Q+M) := by omega

private def equation {K : Type*} [CommSemiring K] (R c : K) (x : Fin 5 → K) : Prop :=
  c * (∏ i, x i) = R * (∑ i : Fin 5, ∏ j ∈ Finset.univ.erase i, x j) + 1

private theorem product_image {ι : Type*} (E : Finset ι) (x : ι → ℕ)
    (hx : Function.Injective x) :
    product (E.image x) = ∏ i ∈ E, x i := by
  unfold product
  exact Finset.prod_image (fun i _ j _ he => hx he)

private theorem derivative_image {ι : Type*} [DecidableEq ι] (E : Finset ι)
    (x : ι → ℕ) (hx : Function.Injective x) :
    derivative (E.image x) = ∑ i ∈ E, ∏ j ∈ E.erase i, x j := by
  unfold derivative
  rw [Finset.sum_image (fun i _ j _ he => hx he)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.image_erase hx E i]
  exact product_image _ _ hx

theorem successor {S : Finset ℕ} {c p : ℕ} (h : ambient S c p)
    (x : Fin 5 → ℕ) (hx : Function.Injective x) (prime : ∀ i, (x i).Prime)
    (above : ∀ i, p < x i) (fill : equation (product S) c x) :
    ∃ S' c' p', S'.card = S.card+4 ∧ ambient S' c' p' := by
  classical
  let T := Finset.univ.image x
  have hcard : T.card = 5 := by
    change (Finset.univ.image x).card = 5
    rw [Finset.card_image_of_injective _ hx]
    simp
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  let u := T.max' hT
  have hum : u ∈ T := Finset.max'_mem _ _
  let A := T.erase u
  have union : A ∪ {u} = T := by
    ext t
    change t ∈ T.erase u ∪ {u} ↔ t ∈ T
    simp only [Finset.mem_union,Finset.mem_erase,Finset.mem_singleton]
    constructor
    · rintro (⟨_,ht⟩ | rfl)
      · exact ht
      · exact hum
    · intro ht
      by_cases e : t=u
      · exact Or.inr e
      · exact Or.inl ⟨e,ht⟩
  have tprime (q : ℕ) (hq : q ∈ T) : q.Prime ∧ p < q := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨prime i, above i⟩
  have aorder (q : ℕ) (hq : q ∈ A) : q.Prime ∧ p < q ∧ q < u := by
    obtain ⟨he,hq'⟩ := Finset.mem_erase.mp hq
    exact ⟨(tprime q hq').1, (tprime q hq').2,
      lt_of_le_of_ne (T.le_max' _ hq') he⟩
  have hd : Disjoint A {u} := Finset.disjoint_singleton_right.mpr (Finset.notMem_erase _ _)
  have hprod : product T = product A*u := by
    rw [← union, product_union hd]
    simp [product]
  have hderiv : derivative T = derivative A*u + product A := by
    rw [← union, derivative_union hd]
    simp [derivative,product]
  have fill' : c*product T = product S*derivative T+1 := by
    rw [product_image _ _ hx, derivative_image _ _ hx]
    exact fill
  rw [hprod,hderiv] at fill'
  obtain ⟨d,ha⟩ := split_fill h (tprime u hum).1 (tprime u hum).2 aorder fill'
  have disjoint : Disjoint S A := Finset.disjoint_left.mpr (fun q hs ht =>
    (not_lt_of_ge (h.2.2.2.1 q hs).2.le) (aorder q ht).2.1)
  refine ⟨S ∪ A, d, u, ?_, ha⟩
  rw [Finset.card_union_of_disjoint disjoint]
  have hAc : A.card = 4 := by
    change (T.erase u).card = 4
    rw [Finset.card_erase_of_mem hum, hcard]
  rw [hAc]

end TerminalPort

namespace WangLocalSolubility

open Finset

/-- Two pairs of opposite coordinates cancel in the sum of reciprocals. -/
private theorem paired_witness {K : Type*} [Field K] (t u : K) (ht : t ≠ 0) (hu : u ≠ 0) :
    ∃ x : Fin 5 → K, (∀ i, x i ≠ 0) ∧ (∏ i, x i) = t * u ^ 2 ∧
      (∑ i : Fin 5, ∏ j ∈ Finset.univ.erase i, x j) = u ^ 2 := by
  let x : Fin 5 → K := ![t, 1, -1, u, -u]
  have hx (i : Fin 5) : x i ≠ 0 := by
    fin_cases i <;> simp [x, ht, hu]
  have hprod : (∏ i, x i) = t * u ^ 2 := by
    simp [Fin.prod_univ_succ, x, pow_two]
  have hinv : (∑ i, (x i)⁻¹) = t⁻¹ := by
    simp [Fin.sum_univ_succ, x]
  have herase (i : Fin 5) : (∏ j ∈ Finset.univ.erase i, x j) = (∏ j, x j) * (x i)⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff (hx i)]
    exact Finset.prod_erase_mul Finset.univ x (Finset.mem_univ i)
  refine ⟨x, hx, hprod, ?_⟩
  simp_rw [herase]
  rw [← Finset.mul_sum, hinv, hprod, mul_comm t (u ^ 2), mul_assoc, mul_inv_cancel₀ ht, mul_one]

/-- Every prime residue field has a nonzero solution of the five-splitting
equation attached to a terminal port. -/
theorem finite_local_solubility {R c p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hport : c * p = R + 1)
    (q : ℕ) (hq : q.Prime) :
    ∃ x : Fin 5 → ZMod q, (∀ i, x i ≠ 0) ∧
      (c : ZMod q) * (∏ i, x i) =
        (R : ZMod q) * (∑ i : Fin 5, ∏ j ∈ Finset.univ.erase i, x j) + 1 := by
  by_cases hqp : q = p
  · subst q
    let : Fact p.Prime := ⟨hp⟩
    have hcast : (c : ZMod p) * (p : ZMod p) = (R : ZMod p) + 1 := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        congrArg (fun m : ℕ => (m : ZMod p)) hport
    have hR : (R : ZMod p) = -1 := by
      rw [ZMod.natCast_self, mul_zero] at hcast
      exact eq_neg_of_add_eq_zero_left hcast.symm
    by_cases hc : (c : ZMod p) = 0
    · obtain ⟨x, hx, _, hsum⟩ :=
        paired_witness (1 : ZMod p) 1 one_ne_zero one_ne_zero
      exact ⟨x, hx, by simp [hsum, hc, hR]⟩
    · have htwo : (2 : ZMod p) ≠ 0 := by
        intro h
        have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
        have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
        omega
      have hthree : (3 : ZMod p) ≠ 0 := by
        intro h
        have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
        have hle := Nat.le_of_dvd (by decide : 0 < 3) hdiv
        omega
      let t : ZMod p := -3 / ((c : ZMod p) * (2 : ZMod p) ^ 2)
      have hden : (c : ZMod p) * (2 : ZMod p) ^ 2 ≠ 0 := mul_ne_zero hc (pow_ne_zero 2 htwo)
      have ht : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hthree) hden
      obtain ⟨x, hx, hprod, hsum⟩ := paired_witness t (2 : ZMod p) ht htwo
      refine ⟨x, hx, ?_⟩
      rw [hprod, hsum, hR]
      calc
        (c : ZMod p) * (t * (2 : ZMod p) ^ 2) = t * ((c : ZMod p) * (2 : ZMod p) ^ 2) := by ring
        _ = -3 := div_mul_cancel₀ _ hden
        _ = _ := by ring
  · let : Fact q.Prime := ⟨hq⟩
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro h
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp ((ZMod.natCast_eq_zero_iff p q).mp h))
    obtain ⟨x, hx, hprod, hsum⟩ := paired_witness (p : ZMod q) 1 hp0 one_ne_zero
    refine ⟨x, hx, ?_⟩
    rw [hprod, hsum, one_pow, mul_one, mul_one]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      congrArg (fun m : ℕ => (m : ZMod q)) hport

end WangLocalSolubility

namespace OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1_H2_R1

/-- Terminal ports have real witnesses with arbitrarily large fifth coordinate. -/
def H1 : Prop :=
  ∀ R c p : ℕ, 4 < R → 3 < p → c*p = R+1 →
    ∀ B : ℝ, ∃ x : Fin 5 → ℝ, (∀ i, (p:ℝ) < x i) ∧ B < x 4 ∧
      TerminalPort.equation (R:ℝ) (c:ℝ) x

/-- Prime realization for the five-variable terminal-port equation. -/
def H2 : Prop :=
  ∀ R c p : ℕ, 4 < R → 3 < p → p.Prime → c*p = R+1 →
    (∀ B : ℝ, ∃ x : Fin 5 → ℝ, (∀ i, (p:ℝ) < x i) ∧ B < x 4 ∧
      TerminalPort.equation (R:ℝ) (c:ℝ) x) →
    (∀ q : ℕ, q.Prime → ∃ x : Fin 5 → ZMod q, (∀ i, x i ≠ 0) ∧
      TerminalPort.equation (R:ZMod q) (c:ZMod q) x) →
    ∃ x : Fin 5 → ℕ, Function.Injective x ∧ (∀ i, (x i).Prime) ∧
      (∀ i, p < x i) ∧ TerminalPort.equation R c x

theorem main : H1 → H2 →
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1.H2 := by
  intro realPoints primePoints k _
  have iterate : ∀ j : ℕ, ∃ S c p, S.card = 2+4*j ∧ TerminalPort.ambient S c p := by
    intro j
    induction j with
    | zero =>
      refine ⟨{2,3},1,7,by decide,?_⟩
      refine ⟨by decide +kernel, by decide, by decide, ?_, by decide +kernel, by decide +kernel⟩
      intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> decide
    | succ j ih =>
      obtain ⟨S,c,p,hcard,ha⟩ := ih
      have hR := ha.1
      have hp3 := ha.2.1
      have hp := ha.2.2.1
      have hclose := ha.2.2.2.2.2
      have hreal := realPoints (TerminalPort.product S) c p hR hp3 hclose
      have hlocal : ∀ q : ℕ, q.Prime → ∃ x : Fin 5 → ZMod q,
          (∀ i, x i ≠ 0) ∧ TerminalPort.equation (TerminalPort.product S : ZMod q) (c : ZMod q) x := by
        intro q hq
        exact WangLocalSolubility.finite_local_solubility hp hp3 hclose q hq
      obtain ⟨x,inj,allPrimes,above,fill⟩ :=
        primePoints (TerminalPort.product S) c p hR hp3 hp hclose hreal hlocal
      obtain ⟨T,d,u,hT,ht⟩ := TerminalPort.successor ha x inj allPrimes above fill
      exact ⟨T,d,u,by omega,ht⟩
  obtain ⟨S,c,p,hcard,ha⟩ := iterate k
  let P := insert p S
  have size : k ≤ P.card := by
    have hle : S.card ≤ P.card :=
      Finset.card_le_card (Finset.subset_insert _ _)
    omega
  have positive : P.Nonempty := Finset.card_pos.mp (by omega)
  have primes : ∀ q ∈ P, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ha.2.2.1
    · exact (ha.2.2.2.1 q hq).1
  have eqn := TerminalPort.complete ha
  exact ⟨P,size,positive,primes,TerminalPort.congruences_from_identity eqn,
    TerminalPort.reciprocal_from_identity primes eqn⟩

end OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1_H2_R1
