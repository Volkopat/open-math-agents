import Mathlib

/-!
# A317534: numbers whose poset of factorizations is not a lattice

Source: https://oeis.org/A317534
Credit: @avivorly

A317534 (%N): Numbers k such that the poset of factorizations of k, ordered by refinement, is not a lattice.

Conjecture (David A. Corneth, Jul 31 2018, %C of the entry): Conjecture: Let S be the set of all numbers whose prime
signature is either {1,3}, {5}, or {1,1,2}. Then the sequence consists of all multiples of elements of S.

The entry's example (%e): In the poset of factorizations of 24, the factorizations (2*2*6) and (2*3*4) have two
least-upper bounds, namely (2*12) and (4*6), so this poset is not a lattice.

Conventions:
- A factorization of `k` is a finite multiset of integers `≥ 2` (order does not matter) whose product is `k`
  (`IsFact k F`). So `1` has exactly one factorization, the empty one, and `0` has none.
- `Refines F G` (`F` refines `G`, `F` lies below `G`): `F` splits into blocks whose products are exactly the factors of
  `G`, i.e. there is a multiset `H` of multisets with `H.join = F` and `H.map Multiset.prod = G`. This is the order of
  the entry's example, where (2*2*6) and (2*3*4) lie below (2*12) and below (4*6). On the factorizations of `k` it is a
  partial order whose least element is the prime factorization of `k` and whose greatest element is `{k}` (for `k ≥ 2`).
- `IsLatticeFact k` says that this poset is a lattice: any two factorizations `x, y` of `k` have a least upper bound
  `z` and a greatest lower bound `w` among the factorizations of `k`, for `Refines`.
- Prime signature `{5}` means `p ^ 5`, `{1,3}` means `p * q ^ 3`, and `{1,1,2}` means `p * q * r ^ 2`, where `p, q, r`
  are distinct primes (`InS s`).
- The sequence is the set of numbers `k ≥ 1` whose poset of factorizations is not a lattice; the claim is that this set
  is exactly the set of multiples of elements of S.
-/

namespace OMA.S_oeis_a317534

/-- `F` is a factorization of `k`: a multiset of integers `≥ 2` with product `k`. -/
def IsFact (k : ℕ) (F : Multiset ℕ) : Prop :=
  (∀ x ∈ F, 2 ≤ x) ∧ F.prod = k

/-- `F` refines `G`: `F` splits into blocks (the members of `H`) whose products are the factors of `G`. -/
def Refines (F G : Multiset ℕ) : Prop :=
  ∃ H : Multiset (Multiset ℕ), H.join = F ∧ H.map Multiset.prod = G

/-- The factorizations of `k`, ordered by refinement, form a lattice: every two of them have a least upper bound and
a greatest lower bound among the factorizations of `k`. -/
def IsLatticeFact (k : ℕ) : Prop :=
  ∀ x y : Multiset ℕ, IsFact k x → IsFact k y →
    (∃ z, IsFact k z ∧ Refines x z ∧ Refines y z ∧
      ∀ u, IsFact k u → Refines x u → Refines y u → Refines z u) ∧
    (∃ w, IsFact k w ∧ Refines w x ∧ Refines w y ∧
      ∀ u, IsFact k u → Refines u x → Refines u y → Refines u w)

/-- `s` has prime signature `{5}`, `{1,3}` or `{1,1,2}`. -/
def InS (s : ℕ) : Prop :=
  (∃ p, p.Prime ∧ s = p ^ 5) ∨
  (∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ s = p * q ^ 3) ∨
  (∃ p q r, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ s = p * q * r ^ 2)

theorem main : ∀ k : ℕ, 1 ≤ k → (¬ IsLatticeFact k ↔ ∃ s, InS s ∧ s ∣ k) := by
  sorry

end OMA.S_oeis_a317534
