import Mathlib

/-!
# 3-dimensional vectors satisfying certain equalities

Source: https://mathoverflow.net/questions/230766
Credit: @koolkao

Question (Slava, MathOverflow 230766, 2016; CC BY-SA 3.0). Are there 5 distinct vectors
`u, v, w, x, y ∈ ℝ^3`, all on the unit sphere (i.e. `‖u‖ = ‖v‖ = ‖w‖ = ‖x‖ = ‖y‖ = 1`), such that
`‖u + v + x‖ = ‖u + v + y‖ = ‖u + w + x‖ = ‖u + w + y‖ = 1`? Also, what is the answer if the
vectors are taken from `ℝ^d` for `d > 3`?

`main` states that the answer is yes in `ℝ^3` and in every `ℝ^d` with `d > 3`, that is, in every
dimension `d ≥ 3`. A disproof shows that some such dimension admits no five such vectors.

Translation choices:
* `ℝ^d` is `EuclideanSpace ℝ (Fin d)` with its Euclidean norm;
* "5 distinct vectors" means pairwise distinct, `[u, v, w, x, y].Nodup`, as literally asked. (The
  accepted reading matters: an answer on MathOverflow by Steffen Kionke points out that if
  "distinct" were strengthened to exclude antipodal pairs such as `v = -u`, the answer in `ℝ^3`
  would change; that stronger reading is not what the question says and is not formalized);
* the two parts of the question (`d = 3`, and `d > 3`) are combined into one statement over all
  `d ≥ 3`; the motivating question about integer sets avoiding a linear system is not formalized.
-/

namespace OMA.S_mo_230766

/-- In `ℝ^d` there are 5 pairwise distinct unit vectors `u, v, w, x, y` with
`‖u + v + x‖ = ‖u + v + y‖ = ‖u + w + x‖ = ‖u + w + y‖ = 1`. -/
def Admits (d : ℕ) : Prop :=
  ∃ u v w x y : EuclideanSpace ℝ (Fin d), [u, v, w, x, y].Nodup ∧
    ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    ‖u + v + x‖ = 1 ∧ ‖u + v + y‖ = 1 ∧ ‖u + w + x‖ = 1 ∧ ‖u + w + y‖ = 1

/-- Yes in `ℝ^3`, and yes in `ℝ^d` for every `d > 3`. -/
theorem main : Admits 3 ∧ ∀ d : ℕ, 3 < d → Admits d := by
  sorry

end OMA.S_mo_230766
