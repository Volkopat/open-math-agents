import Mathlib

/-!
# Cap set

Source: https://en.wikipedia.org/wiki/cap_set
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_cap_set

/-!
The source's precise statement formalized here:

* "a cap set is a subset of the affine space Z_3^n (the n-dimensional affine space over
  the three-element field) where no three elements sum to the zero vector."
  Points of Z_3^n are formalized as functions `Fin n → ZMod 3`; "no three elements"
  means no three *distinct* elements of the subset sum to the zero vector.
* "The cap set problem is the problem of finding the size of the largest possible cap
  set, as a function of n." This is a request for the maximum size r(n); the faithful
  precise content is the defining property of that maximum: for every n, the maximum
  exists and is attained by some cap set, and no cap set is larger. (Same convention as
  wp-zarankiewicz-problem in this repo.)
* n ranges over all of ℕ: the source states the sizes "as a function of n" with no
  restriction, and its sequence 1, 2, 4, 9, 20, 45, 112 (A090245) starts at n = 0.
* The OEIS values 1, 2, 4, 9, 20, 45, 112 are data reported by the source, not the
  problem statement, so they are not asserted in `main`.
-/

/-- The affine space Z_3^n: points are n-tuples over the three-element field `ZMod 3`. -/
abbrev CapSpace (n : ℕ) : Type := Fin n → ZMod 3

/-- A cap set: a subset `S` of the affine space `Z_3^n` where no three elements sum to
the zero vector — i.e. whenever `x, y, z ∈ S` satisfy `x + y + z = 0`, two of them are
equal (so the three are not distinct). -/
def IsCapSet (n : ℕ) (S : Finset (CapSpace n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y + z = 0 → x = y ∨ x = z ∨ y = z

/-- The set of sizes of cap sets in `Z_3^n` (the finite set of all subsets of `Z_3^n`,
mapped to their cardinalities). -/
def capSetSizes (n : ℕ) : Set ℕ :=
  (Finset.image (fun S : Finset (CapSpace n) => S.card)
    (Finset.univ : Finset (Finset (CapSpace n))) :
    Set ℕ)

/-- The size of the largest possible cap set in `Z_3^n`, as a function of `n`. -/
noncomputable def capSetMaxSize (n : ℕ) : ℕ := sSup (capSetSizes n)

/-- (Cap set problem) The size of the largest possible cap set in `Z_3^n` is well-defined
as a function of `n`: for every `n`, the maximum size `capSetMaxSize n` is attained by
some cap set, and no cap set in `Z_3^n` has more elements. -/
theorem main :
    ∀ n : ℕ,
      (∃ S : Finset (CapSpace n), IsCapSet n S ∧ S.card = capSetMaxSize n) ∧
        (∀ S : Finset (CapSpace n), IsCapSet n S → S.card ≤ capSetMaxSize n) := by
  sorry

end OMA.S_wp_cap_set
