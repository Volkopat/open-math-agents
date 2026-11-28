import Mathlib

/-!
# Property B

Source: https://en.wikipedia.org/wiki/Property_B
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_property_b

/-!
The source's precise statement formalized here:

* "given a finite set $X$, a collection $C$ of subsets of $X$ has Property B if we can
  partition $X$ into two disjoint subsets $Y$ and $Z$ such that every set in $C$ meets
  both $Y$ and $Z$."
  Formalized as: `X` is a finite type, `C : Finset (Set X)`, and there are sets `Y`, `Z`
  that are disjoint, cover `X`, and every `S ∈ C` has nonempty intersection with both.
  ("Meets" = nonempty intersection; the meets-both condition forces `Y` and `Z` nonempty
  whenever `C` is nonempty, so no extra nonemptiness clause is added.)
* "The smallest number of sets in a collection of sets of size $n$ such that $C$ does not
  have Property B is denoted by $m(n)$." The source does NOT fix the ground set, so the
  minimum ranges over all finite ground sets (taken as `Fin N` for all `N : ℕ`);
  "sets of size $n$" is `S.ncard = n`; "number of sets" is `C.card`; "smallest" is the
  least element of the set of achievable cardinals.
* The source's unsolved-problem box — "What is the smallest collection of $n$-uniform
  sets without Property B for all $n$?" — is a question, not a proposition. The faithful
  formalization of the source's precise assertible content is the defining property of
  $m(n)$: the minimum exists and is attained (an $n$-uniform collection of $m(n)$ sets
  without Property B exists), and every $n$-uniform collection with fewer sets has
  Property B. `main` states exactly this.
* The source's listed values m(1)=1, m(2)=3, m(3)=7, m(4)=23 and 29 ≤ m(5) ≤ 51 are
  stated as partial answers (known results), not as the problem statement; they are
  recorded here in comments only.
-/

/-- `C` has Property B (source: "given a finite set X, a collection C of subsets of X
has Property B if we can partition X into two disjoint subsets Y and Z such that every
set in C meets both Y and Z"). -/
def HasPropertyB {X : Type*} [Fintype X] (C : Finset (Set X)) : Prop :=
  ∃ Y Z : Set X,
    Disjoint Y Z ∧ Y ∪ Z = Set.univ ∧
      ∀ S ∈ C, (S ∩ Y).Nonempty ∧ (S ∩ Z).Nonempty

/-- The set of numbers `k` such that there is a collection `C` of `k` sets of size `n`
(on some finite ground set `Fin N`) that does NOT have Property B. -/
def noPropertyBSizes (n : ℕ) : Set ℕ :=
  { k | ∃ (N : ℕ) (C : Finset (Set (Fin N))),
      C.card = k ∧ (∀ S ∈ C, S.ncard = n) ∧ ¬HasPropertyB C }

/-- `m(n)`: the smallest number of sets in a collection of sets of size `n` such that
the collection does not have Property B (least element of `noPropertyBSizes n`). -/
noncomputable def m (n : ℕ) : ℕ := sInf (noPropertyBSizes n)

/-- The defining property of `m(n)` from the source: for every `n`, the smallest number
of sets in a collection of sets of size `n` without Property B exists and is attained —
there is an `n`-uniform collection of `m(n)` sets without Property B, and every
`n`-uniform collection with fewer than `m(n)` sets has Property B. -/
theorem main :
    ∀ n : ℕ,
      (∃ (N : ℕ) (C : Finset (Set (Fin N))),
          C.card = m n ∧ (∀ S ∈ C, S.ncard = n) ∧ ¬HasPropertyB C) ∧
        (∀ k : ℕ, k < m n →
            ∀ (N : ℕ) (C : Finset (Set (Fin N))),
              (∀ S ∈ C, S.ncard = n) → C.card = k → HasPropertyB C) := by
  sorry

end OMA.S_wp_property_b
