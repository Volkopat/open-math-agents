import FormalConjectures.GreensOpenProblems.«76»

-- Reduction Green76.green_76.variants.exists_constant.R1 of Green's Problem 76 with a constant threshold
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Green 76 with a constant: any ratio below one is enough

The target asks for a constant `k` such that every finite set `A` of points in the plane has a set
`A'` of at most `|A| / 2` points that meets every closed axis-parallel rectangle containing at
least `k` points of `A` (Pach and Tardos, 2nd Emlektabla Workshop (2011), Problem 5; Green,
100 open problems, Problem 76).

* `H1` (the open core, a weaker form of the target): the same with `|A| / 2` replaced by `c |A|`
  for some constant `c < 1`. The target gives `H1` with `c = 1 / 2`, so `H1` is no stronger than
  the target; with `main` the two are equivalent.
* `H2` (elementary): if `B` meets every rectangle with at least `K` points of `A`, then every
  rectangle with at least `4 ^ r (K + 1)` points of `A` contains at least `r + 1` points of `B`.
  Proof: induction on `r`. Take a point `q` of `B` in the rectangle. The other points of `A` in
  the rectangle lie left of `q`, right of `q`, straight above `q` or straight below `q`, and each
  of these four parts lies in a closed subrectangle that misses `q`. One part has at least
  `4 ^ (r - 1) (K + 1)` points, so its subrectangle holds `r` points of `B`, none of them `q`.

`main` iterates `H1`: apply it to `A`, then to the set just found, and so on. After `j` rounds the
set has at most `c ^ j |A|` points, and by `H2` it still meets every rectangle that contains
enough points of `A` (the threshold grows with `j`, but `j` depends only on `c`). Take `j` with
`c ^ j ≤ 1 / 2`.

The sets `A'` are not required to be subsets of `A`. With that requirement the same iteration
works and the statement is false for every `c < 1`, by Pach and Tardos, Tight lower bounds for
the size of epsilon-nets, J. Amer. Math. Soc. 26 (2013).
-/

namespace OMA.R_Green76_green_76_variants_exists_constant_R1

open scoped Finset

/-- The open core: a constant threshold with `|A'| ≤ c |A|` for some constant `c < 1`. -/
def H1 : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∃ k : ℕ, ∀ A : Finset (ℝ × ℝ), ∃ A' : Finset (ℝ × ℝ),
    (#A' : ℝ) ≤ c * #A ∧ Green76.HitsRichRectangles k A A'

/-- Elementary: a rectangle with `4 ^ r (K + 1)` points of `A` holds `r + 1` points of `B`. -/
def H2 : Prop :=
  ∀ (K : ℕ) (A B : Finset (ℝ × ℝ)), Green76.HitsRichRectangles K A B →
    ∀ (r : ℕ) (a b : ℝ × ℝ), 4 ^ r * (K + 1) ≤ #{p ∈ A | p ∈ Set.Icc a b} →
      r + 1 ≤ #{p ∈ B | p ∈ Set.Icc a b}

/-- Iterating `H1`: after `j` rounds the ratio is `c ^ j`, with some constant threshold. -/
lemma iterate (c : ℝ) (k : ℕ)
    (hk : ∀ A : Finset (ℝ × ℝ), ∃ A' : Finset (ℝ × ℝ),
      (#A' : ℝ) ≤ c * #A ∧ Green76.HitsRichRectangles k A A')
    (h2 : H2) (j : ℕ) :
    ∃ K : ℕ, ∀ A : Finset (ℝ × ℝ), ∃ A' : Finset (ℝ × ℝ),
      (#A' : ℝ) ≤ (max c 0) ^ j * #A ∧ Green76.HitsRichRectangles K A A' := by
  induction j with
  | zero =>
    exact ⟨1, fun A => ⟨A, by simp, Green76.hitsRichRectangles_self one_pos A⟩⟩
  | succ j ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨4 ^ k * (K + 1), fun A => ?_⟩
    obtain ⟨B, hB, hBhit⟩ := hK A
    obtain ⟨B', hB', hB'hit⟩ := hk B
    refine ⟨B', ?_, ?_⟩
    · have h1 : (#B' : ℝ) ≤ max c 0 * #B :=
        hB'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
      calc (#B' : ℝ) ≤ max c 0 * #B := h1
        _ ≤ max c 0 * ((max c 0) ^ j * #A) := mul_le_mul_of_nonneg_left hB (le_max_right _ _)
        _ = (max c 0) ^ (j + 1) * #A := by ring
    · intro a b hab
      have h3 := h2 K A B hBhit k a b hab
      exact hB'hit a b (by omega)

theorem main : H1 → H2 → type_of% @Green76.green_76.variants.exists_constant := by
  rintro ⟨c, hc1, k, hk⟩ h2
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 2 by norm_num)
    (show max c 0 < 1 from max_lt hc1 one_pos)
  obtain ⟨K, hK⟩ := iterate c k hk h2 j
  refine ⟨K, fun A => ?_⟩
  obtain ⟨A', hA', hhit⟩ := hK A
  refine ⟨A', ?_, hhit⟩
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : (#A' : ℝ) ≤ 1 / 2 * #A :=
    hA'.trans (mul_le_mul_of_nonneg_right hj.le (Nat.cast_nonneg _))
  have h2 : ((#A' * 2 : ℕ) : ℝ) ≤ (#A : ℕ) := by
    push_cast
    linarith
  exact_mod_cast h2

end OMA.R_Green76_green_76_variants_exists_constant_R1
