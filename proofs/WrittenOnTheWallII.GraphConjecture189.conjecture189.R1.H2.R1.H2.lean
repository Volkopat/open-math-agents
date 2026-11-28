import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H2_R1
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- Step WrittenOnTheWallII.GraphConjecture189.conjecture189.R1.H2.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R1.H2.R1
-- Credit: @rudyschnare-tech

/-!
# Written on the Wall II, Conjecture 189: diameter five cannot occur

The hypotheses of this step are contradictory, so the step holds vacuously. Only four of them are
used: connectedness, diameter five, the low endpoint of every pair at distance five, and the
bound `distEven x ≤ 1 + σ` (σ the second-smallest degree). The triangle, the two size bounds and
the neighbourhood condition are not needed.

Setting. Take `x0, x5` at distance five with `deg x0 < σ`, and a shortest path `x0 x1 x2 x3 x4 x5`.
Every vertex other than `x0` has degree at least `σ`, so two vertices other than `x0` are at
distance at most four. Give each vertex `y` its profile
`(dist x0 y, dist x1 y, dist x3 y, dist x5 y)`; the triangle inequality leaves 95 possible
profiles (`OMA.D5Prof`). A vertex `t` with a known profile constrains `dist t y` for every `y`
(`OMA.D5Wit`).

Counting. For a vertex `e`, `distEven e` is the number of `y` with `dist e y` even, written as
`∑ y, (dist e y + 1) % 2`. For a vertex `d`, `deg d + 1` is the number of `y` with `dist d y ≤ 1`,
written as `∑ y, (1 - dist d y / 2)`. In each of the twelve cases below we pick vertices
`e_1, …, e_m` and `d_1, …, d_m` (none of the `d_i` is `x0`) and one extra vertex `s`, and check for
every profile that

  `[dist d_1 y ≤ 1] + … + [dist d_m y ≤ 1] + [y = s] ≤ [dist e_1 y even] + … + [dist e_m y even]`.

Summing over `y` gives `m (σ + 1) + 1 ≤ m (σ + 1)`, a contradiction. The pointwise inequality is
the lemma `OMA.d5_arith_n`: it splits over the 95 profiles and each one is linear arithmetic.

Cases. They branch on whether some vertex has a given profile. Write `A = (1,1,2,4)`,
`B = (5,4,3,1)`, `C = (5,4,2,1)`, `D = (1,1,3,4)`; `x2` has profile `(2,1,1,3)` and `x4` has
`(4,3,1,1)`. Below, a profile stands for a vertex with that profile.

 1. A, B, C, D exist: e = x0, x1, x3, x5; d = D, x2, B, x4.
 2. A, B, C exist, D does not, (3,3,1,2) and (2,1,3,3) exist: e = x0, x1, x3, x5;
    d = x2, (2,1,3,3), B, x4.
 3. As 2, but (2,1,3,3) does not exist: e = x0, x3, x5, x4; d = x1, x1, (3,3,1,2), B.
 4. A, B, C exist, D and (3,3,1,2) do not: e = x0, x1, x3; d = A, B, x4.
 5. A, B exist, C does not: e = x0, x5, x4; d = x1, x3, B.
 6. A, C, D exist, B does not, (4,4,3,1) exists: e = x0, x1, x3, x5; d = D, x2, (4,4,3,1), x4.
 7. A, C, D exist, B and (4,4,3,1) do not, (3,2,1,3) and (4,3,3,1) exist: e = x0, x1, x3, x5;
    d = D, x2, x4, (4,3,3,1).
 8. As 7, but (4,3,3,1) does not exist: e = x0, x1, x3, x2; d = x5, D, C, (3,2,1,3).
 9. A, C, D exist, B, (4,4,3,1) and (3,2,1,3) do not: e = x0, x3, x5; d = D, x2, C.
10. A, C exist, B and D do not: e = x0, x3; d = x1, x5.
11. A exists, B and C do not: e = x0; d = x5. Here every neighbour of `x5` is at distance four
    from `x0`, and `x0, x2` are two more vertices at even distance from `x0`.
12. A does not exist: e = x0, x1; d = x5, x2.

The case tree and the choice of vertices were found by a computer search (a linear program per
case); nothing here depends on that search, since every case is checked by the kernel.
-/

def OMA.D5Prof (a0 a1 a3 a5 : ℕ) : Prop :=
  a0 ≤ 5 ∧
  a0 ≤ a1 + 1 ∧ a1 ≤ a0 + 1 ∧ 1 ≤ a0 + a1 ∧
  a0 ≤ a3 + 3 ∧ a3 ≤ a0 + 3 ∧ 3 ≤ a0 + a3 ∧
  a0 ≤ a5 + 5 ∧ a5 ≤ a0 + 5 ∧ 5 ≤ a0 + a5 ∧
  a1 ≤ a3 + 2 ∧ a3 ≤ a1 + 2 ∧ 2 ≤ a1 + a3 ∧
  a1 ≤ a5 + 4 ∧ a5 ≤ a1 + 4 ∧ 4 ≤ a1 + a5 ∧
  a3 ≤ a5 + 2 ∧ a5 ≤ a3 + 2 ∧ 2 ≤ a3 + a5 ∧
  (1 ≤ a0 → a1 ≤ 4) ∧ (1 ≤ a0 → a3 ≤ 4) ∧ (1 ≤ a0 → a5 ≤ 4)

def OMA.D5Wit (t0 t1 t3 t5 a0 a1 a3 a5 w : ℕ) : Prop :=
  w ≤ t0 + a0 ∧ a0 ≤ t0 + w ∧ t0 ≤ a0 + w ∧
  w ≤ t1 + a1 ∧ a1 ≤ t1 + w ∧ t1 ≤ a1 + w ∧
  w ≤ t3 + a3 ∧ a3 ≤ t3 + w ∧ t3 ≤ a3 + w ∧
  w ≤ t5 + a5 ∧ a5 ≤ t5 + w ∧ t5 ≤ a5 + w ∧
  (1 ≤ a0 → w ≤ 4)

theorem OMA.d5_arith_1 (a0 a1 a3 a5 w1134 w2113 w4311 w5431 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 1 1 3 4 a0 a1 a3 a5 w1134)
    (hW1 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hW2 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW3 : OMA.D5Wit 5 4 3 1 a0 a1 a3 a5 w5431)
    : (1 - w1134 / 2) + (1 - w2113 / 2) + (1 - w5431 / 2) + (1 - w4311 / 2) + (1 - a1) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 + (a3 + 1) % 2 + (a5 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2 hW3
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_2 (a0 a1 a3 a5 w2113 w2133 w4311 w5431 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hW1 : OMA.D5Wit 2 1 3 3 a0 a1 a3 a5 w2133)
    (hW2 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW3 : OMA.D5Wit 5 4 3 1 a0 a1 a3 a5 w5431)
    (hE0 : ¬(a0 = 1 ∧ a1 = 1 ∧ a3 = 3 ∧ a5 = 4))
    : (1 - w2113 / 2) + (1 - w2133 / 2) + (1 - w5431 / 2) + (1 - w4311 / 2) + (1 - a0) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 + (a3 + 1) % 2 + (a5 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2 hW3
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_3 (a0 a1 a3 a5 w3312 w4311 w5431 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 3 3 1 2 a0 a1 a3 a5 w3312)
    (hW1 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW2 : OMA.D5Wit 5 4 3 1 a0 a1 a3 a5 w5431)
    (hE0 : ¬(a0 = 1 ∧ a1 = 1 ∧ a3 = 3 ∧ a5 = 4))
    (hE1 : ¬(a0 = 2 ∧ a1 = 1 ∧ a3 = 3 ∧ a5 = 3))
    : (1 - a1 / 2) + (1 - a1 / 2) + (1 - w3312 / 2) + (1 - w5431 / 2) + (1 - a3) ≤ (a0 + 1) % 2 + (a3 + 1) % 2 + (a5 + 1) % 2 + (w4311 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_4 (a0 a1 a3 a5 w1124 w4311 w5431 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 1 1 2 4 a0 a1 a3 a5 w1124)
    (hW1 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW2 : OMA.D5Wit 5 4 3 1 a0 a1 a3 a5 w5431)
    (hE0 : ¬(a0 = 1 ∧ a1 = 1 ∧ a3 = 3 ∧ a5 = 4))
    (hE1 : ¬(a0 = 3 ∧ a1 = 3 ∧ a3 = 1 ∧ a5 = 2))
    : (1 - w1124 / 2) + (1 - w5431 / 2) + (1 - w4311 / 2) + (1 - a1) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 + (a3 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_5 (a0 a1 a3 a5 w4311 w5431 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW1 : OMA.D5Wit 5 4 3 1 a0 a1 a3 a5 w5431)
    (hE0 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 2 ∧ a5 = 1))
    : (1 - a1 / 2) + (1 - a3 / 2) + (1 - w5431 / 2) + (1 - a0) ≤ (a0 + 1) % 2 + (a5 + 1) % 2 + (w4311 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_6 (a0 a1 a3 a5 w1134 w2113 w4311 w4431 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 1 1 3 4 a0 a1 a3 a5 w1134)
    (hW1 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hW2 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW3 : OMA.D5Wit 4 4 3 1 a0 a1 a3 a5 w4431)
    (hE0 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    : (1 - w1134 / 2) + (1 - w2113 / 2) + (1 - w4431 / 2) + (1 - w4311 / 2) + (1 - a1) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 + (a3 + 1) % 2 + (a5 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2 hW3
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_7 (a0 a1 a3 a5 w1134 w2113 w4311 w4331 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 1 1 3 4 a0 a1 a3 a5 w1134)
    (hW1 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hW2 : OMA.D5Wit 4 3 1 1 a0 a1 a3 a5 w4311)
    (hW3 : OMA.D5Wit 4 3 3 1 a0 a1 a3 a5 w4331)
    (hE0 : ¬(a0 = 4 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    (hE1 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    : (1 - w1134 / 2) + (1 - w2113 / 2) + (1 - w4311 / 2) + (1 - w4331 / 2) + (1 - a1) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 + (a3 + 1) % 2 + (a5 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2 hW3
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_8 (a0 a1 a3 a5 w1134 w2113 w3213 w5421 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 1 1 3 4 a0 a1 a3 a5 w1134)
    (hW1 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hW2 : OMA.D5Wit 3 2 1 3 a0 a1 a3 a5 w3213)
    (hW3 : OMA.D5Wit 5 4 2 1 a0 a1 a3 a5 w5421)
    (hE0 : ¬(a0 = 4 ∧ a1 = 3 ∧ a3 = 3 ∧ a5 = 1))
    (hE1 : ¬(a0 = 4 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    (hE2 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    : (1 - a5 / 2) + (1 - w1134 / 2) + (1 - w5421 / 2) + (1 - w3213 / 2) + (1 - a0) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 + (a3 + 1) % 2 + (w2113 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2 hW3
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_9 (a0 a1 a3 a5 w1134 w2113 w5421 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 1 1 3 4 a0 a1 a3 a5 w1134)
    (hW1 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hW2 : OMA.D5Wit 5 4 2 1 a0 a1 a3 a5 w5421)
    (hE0 : ¬(a0 = 3 ∧ a1 = 2 ∧ a3 = 1 ∧ a5 = 3))
    (hE1 : ¬(a0 = 4 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    (hE2 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    : (1 - w1134 / 2) + (1 - w2113 / 2) + (1 - w5421 / 2) + (1 - a3) ≤ (a0 + 1) % 2 + (a3 + 1) % 2 + (a5 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0 hW1 hW2
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_10 (a0 a1 a3 a5 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hE0 : ¬(a0 = 1 ∧ a1 = 1 ∧ a3 = 3 ∧ a5 = 4))
    (hE1 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    : (1 - a1 / 2) + (1 - a5 / 2) + (1 - a3) ≤ (a0 + 1) % 2 + (a3 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_11 (a0 a1 a3 a5 w2113 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hE0 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 2 ∧ a5 = 1))
    (hE1 : ¬(a0 = 5 ∧ a1 = 4 ∧ a3 = 3 ∧ a5 = 1))
    : (1 - a5 / 2) + (1 - a0) + (1 - w2113) ≤ (a0 + 1) % 2 + (1 - a5) := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_arith_12 (a0 a1 a3 a5 w2113 : ℕ)
    (hP : OMA.D5Prof a0 a1 a3 a5)
    (hW0 : OMA.D5Wit 2 1 1 3 a0 a1 a3 a5 w2113)
    (hE0 : ¬(a0 = 1 ∧ a1 = 1 ∧ a3 = 2 ∧ a5 = 4))
    : (1 - a5 / 2) + (1 - w2113 / 2) + (1 - a0) ≤ (a0 + 1) % 2 + (a1 + 1) % 2 := by
  unfold OMA.D5Prof at hP
  unfold OMA.D5Wit at hW0
  have h0 : a0 = 0 ∨ a0 = 1 ∨ a0 = 2 ∨ a0 = 3 ∨ a0 = 4 ∨ a0 = 5 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : a1 = 1 := by omega
    subst h1
    have h2 : a3 = 3 := by omega
    subst h2
    have h3 : a5 = 5 := by omega
    subst h3
    omega
  · have h1 : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 2 := by omega
      subst h2
      have h3 : a5 = 4 := by omega
      subst h3
      omega
    · have h2 : a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
      · have h3 : a5 = 4 := by omega
        subst h3
        omega
  · have h1 : a1 = 1 ∨ a1 = 2 ∨ a1 = 3 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 3 := by omega
        subst h3
        omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
  · have h1 : a1 = 2 ∨ a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl | rfl
    · have h2 : a3 = 0 ∨ a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 := by omega
        subst h3
        omega
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 3 ∨ a1 = 4 := by omega
    rcases h1 with rfl | rfl
    · have h2 : a3 = 1 ∨ a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
    · have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
      rcases h2 with rfl | rfl | rfl
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
      · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
        rcases h3 with rfl | rfl | rfl
        · omega
        · omega
        · omega
  · have h1 : a1 = 4 := by omega
    subst h1
    have h2 : a3 = 2 ∨ a3 = 3 ∨ a3 = 4 := by omega
    rcases h2 with rfl | rfl | rfl
    · have h3 : a5 = 0 ∨ a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 1 ∨ a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    · have h3 : a5 = 2 ∨ a5 = 3 ∨ a5 = 4 := by omega
      rcases h3 with rfl | rfl | rfl
      · omega
      · omega
      · omega

theorem OMA.d5_even_count {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V) :
    SimpleGraph.distEven G x = ∑ y : V, (G.dist x y + 1) % 2 := by
  unfold SimpleGraph.distEven
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs with h
  · rw [Nat.even_iff] at h
    omega
  · rw [Nat.even_iff] at h
    omega

theorem OMA.d5_deg_count {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (x : V) : ∑ y : V, (1 - G.dist x y / 2) = G.degree x + 1 := by
  rw [← OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.dist_le_one_count hc x]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs with h
  · omega
  · omega

theorem OMA.d5_self_count {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hc : G.Connected) (u : V) : ∑ y : V, (1 - G.dist u y) = 1 := by
  rw [Finset.sum_eq_single u]
  · rw [SimpleGraph.dist_self]
  · intro y _ hy
    have h : G.dist u y ≠ 0 := fun h => hy ((hc.dist_eq_zero_iff).mp h).symm
    omega
  · intro h
    exact absurd (Finset.mem_univ u) h

theorem OMA.d5_wit {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hc : G.Connected) (x0 x1 x3 x5 : V)
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (t : V) (t0 t1 t3 t5 : ℕ)
    (h : G.dist x0 t = t0 ∧ G.dist x1 t = t1 ∧ G.dist x3 t = t3 ∧ G.dist x5 t = t5)
    (ht : 1 ≤ t0) (y : V) :
    OMA.D5Wit t0 t1 t3 t5 (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y) (G.dist t y) := by
  have tri : ∀ a : V, G.dist t y ≤ G.dist a t + G.dist a y ∧ G.dist a y ≤ G.dist a t + G.dist t y ∧
      G.dist a t ≤ G.dist a y + G.dist t y := by
    intro a
    have h1 := hc.dist_triangle (u := t) (v := a) (w := y)
    have h2 := hc.dist_triangle (u := a) (v := t) (w := y)
    have h3 := hc.dist_triangle (u := a) (v := y) (w := t)
    rw [SimpleGraph.dist_comm (u := t) (v := a)] at h1
    rw [SimpleGraph.dist_comm (u := y) (v := t)] at h3
    exact ⟨h1, h2, h3⟩
  have T0 := tri x0
  have T1 := tri x1
  have T3 := tri x3
  have T5 := tri x5
  have hcp : 1 ≤ G.dist x0 y → G.dist t y ≤ 4 := fun hy => hcap t y (by omega) hy
  obtain ⟨h0, h1, h3, h5⟩ := h
  rw [h0] at T0
  rw [h1] at T1
  rw [h3] at T3
  rw [h5] at T5
  unfold OMA.D5Wit
  exact ⟨T0.1, T0.2.1, T0.2.2, T1.1, T1.2.1, T1.2.2, T3.1, T3.2.1, T3.2.2, T5.1, T5.2.1, T5.2.2, hcp⟩

theorem OMA.d5_leaf_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (t1134 : V) (h1134 : G.dist x0 t1134 = 1 ∧ G.dist x1 t1134 = 1 ∧ G.dist x3 t1134 = 3 ∧ G.dist x5 t1134 = 4)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t5431 : V) (h5431 : G.dist x0 t5431 = 5 ∧ G.dist x1 t5431 = 4 ∧ G.dist x3 t5431 = 3 ∧ G.dist x5 t5431 = 1)
    : False := by
  have hpt : ∀ y : V, (1 - G.dist t1134 y / 2) + (1 - G.dist t2113 y / 2) + (1 - G.dist t5431 y / 2) + (1 - G.dist t4311 y / 2) + (1 - G.dist x1 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist x5 y + 1) % 2 := fun y =>
    OMA.d5_arith_1 _ _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t1134 1 1 3 4 h1134 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5431 5 4 3 1 h5431 (by omega) y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x3
  rw [OMA.d5_even_count] at e3
  have e4 := hyp x5
  rw [OMA.d5_even_count] at e4
  have d1 := OMA.d5_deg_count G hc t1134
  have f1 := hdeg t1134 (by omega)
  have d2 := OMA.d5_deg_count G hc t2113
  have f2 := hdeg t2113 (by omega)
  have d3 := OMA.d5_deg_count G hc t5431
  have f3 := hdeg t5431 (by omega)
  have d4 := OMA.d5_deg_count G hc t4311
  have f4 := hdeg t4311 (by omega)
  have b1 := OMA.d5_self_count G hc x1
  omega

theorem OMA.d5_leaf_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t2133 : V) (h2133 : G.dist x0 t2133 = 2 ∧ G.dist x1 t2133 = 1 ∧ G.dist x3 t2133 = 3 ∧ G.dist x5 t2133 = 3)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t5431 : V) (h5431 : G.dist x0 t5431 = 5 ∧ G.dist x1 t5431 = 4 ∧ G.dist x3 t5431 = 3 ∧ G.dist x5 t5431 = 1)
    (n1134 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 4))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist t2113 y / 2) + (1 - G.dist t2133 y / 2) + (1 - G.dist t5431 y / 2) + (1 - G.dist t4311 y / 2) + (1 - G.dist x0 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist x5 y + 1) % 2 := fun y =>
    OMA.d5_arith_2 _ _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2133 2 1 3 3 h2133 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5431 5 4 3 1 h5431 (by omega) y)
      (n1134 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x3
  rw [OMA.d5_even_count] at e3
  have e4 := hyp x5
  rw [OMA.d5_even_count] at e4
  have d1 := OMA.d5_deg_count G hc t2113
  have f1 := hdeg t2113 (by omega)
  have d2 := OMA.d5_deg_count G hc t2133
  have f2 := hdeg t2133 (by omega)
  have d3 := OMA.d5_deg_count G hc t5431
  have f3 := hdeg t5431 (by omega)
  have d4 := OMA.d5_deg_count G hc t4311
  have f4 := hdeg t4311 (by omega)
  have b1 := OMA.d5_self_count G hc x0
  omega

theorem OMA.d5_leaf_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (t3312 : V) (h3312 : G.dist x0 t3312 = 3 ∧ G.dist x1 t3312 = 3 ∧ G.dist x3 t3312 = 1 ∧ G.dist x5 t3312 = 2)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t5431 : V) (h5431 : G.dist x0 t5431 = 5 ∧ G.dist x1 t5431 = 4 ∧ G.dist x3 t5431 = 3 ∧ G.dist x5 t5431 = 1)
    (n1134 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 4))
    (n2133 : ∀ y : V, ¬(G.dist x0 y = 2 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 3))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist x1 y / 2) + (1 - G.dist x1 y / 2) + (1 - G.dist t3312 y / 2) + (1 - G.dist t5431 y / 2) + (1 - G.dist x3 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist x5 y + 1) % 2 + (G.dist t4311 y + 1) % 2 := fun y =>
    OMA.d5_arith_3 _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t3312 3 3 1 2 h3312 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5431 5 4 3 1 h5431 (by omega) y)
      (n1134 y)
      (n2133 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x3
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x5
  rw [OMA.d5_even_count] at e3
  have e4 := hyp t4311
  rw [OMA.d5_even_count] at e4
  have d1 := OMA.d5_deg_count G hc x1
  have f1 := hdeg x1 (by omega)
  have d2 := OMA.d5_deg_count G hc t3312
  have f2 := hdeg t3312 (by omega)
  have d3 := OMA.d5_deg_count G hc t5431
  have f3 := hdeg t5431 (by omega)
  have b1 := OMA.d5_self_count G hc x3
  omega

theorem OMA.d5_leaf_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (t1124 : V) (h1124 : G.dist x0 t1124 = 1 ∧ G.dist x1 t1124 = 1 ∧ G.dist x3 t1124 = 2 ∧ G.dist x5 t1124 = 4)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t5431 : V) (h5431 : G.dist x0 t5431 = 5 ∧ G.dist x1 t5431 = 4 ∧ G.dist x3 t5431 = 3 ∧ G.dist x5 t5431 = 1)
    (n1134 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 4))
    (n3312 : ∀ y : V, ¬(G.dist x0 y = 3 ∧ G.dist x1 y = 3 ∧ G.dist x3 y = 1 ∧ G.dist x5 y = 2))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist t1124 y / 2) + (1 - G.dist t5431 y / 2) + (1 - G.dist t4311 y / 2) + (1 - G.dist x1 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 + (G.dist x3 y + 1) % 2 := fun y =>
    OMA.d5_arith_4 _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t1124 1 1 2 4 h1124 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5431 5 4 3 1 h5431 (by omega) y)
      (n1134 y)
      (n3312 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x3
  rw [OMA.d5_even_count] at e3
  have d1 := OMA.d5_deg_count G hc t1124
  have f1 := hdeg t1124 (by omega)
  have d2 := OMA.d5_deg_count G hc t5431
  have f2 := hdeg t5431 (by omega)
  have d3 := OMA.d5_deg_count G hc t4311
  have f3 := hdeg t4311 (by omega)
  have b1 := OMA.d5_self_count G hc x1
  omega

theorem OMA.d5_leaf_5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t5431 : V) (h5431 : G.dist x0 t5431 = 5 ∧ G.dist x1 t5431 = 4 ∧ G.dist x3 t5431 = 3 ∧ G.dist x5 t5431 = 1)
    (n5421 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 2 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist x1 y / 2) + (1 - G.dist x3 y / 2) + (1 - G.dist t5431 y / 2) + (1 - G.dist x0 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x5 y + 1) % 2 + (G.dist t4311 y + 1) % 2 := fun y =>
    OMA.d5_arith_5 _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5431 5 4 3 1 h5431 (by omega) y)
      (n5421 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x5
  rw [OMA.d5_even_count] at e2
  have e3 := hyp t4311
  rw [OMA.d5_even_count] at e3
  have d1 := OMA.d5_deg_count G hc x1
  have f1 := hdeg x1 (by omega)
  have d2 := OMA.d5_deg_count G hc x3
  have f2 := hdeg x3 (by omega)
  have d3 := OMA.d5_deg_count G hc t5431
  have f3 := hdeg t5431 (by omega)
  have b1 := OMA.d5_self_count G hc x0
  omega

theorem OMA.d5_leaf_6 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (t1134 : V) (h1134 : G.dist x0 t1134 = 1 ∧ G.dist x1 t1134 = 1 ∧ G.dist x3 t1134 = 3 ∧ G.dist x5 t1134 = 4)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t4431 : V) (h4431 : G.dist x0 t4431 = 4 ∧ G.dist x1 t4431 = 4 ∧ G.dist x3 t4431 = 3 ∧ G.dist x5 t4431 = 1)
    (n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist t1134 y / 2) + (1 - G.dist t2113 y / 2) + (1 - G.dist t4431 y / 2) + (1 - G.dist t4311 y / 2) + (1 - G.dist x1 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist x5 y + 1) % 2 := fun y =>
    OMA.d5_arith_6 _ _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t1134 1 1 3 4 h1134 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4431 4 4 3 1 h4431 (by omega) y)
      (n5431 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x3
  rw [OMA.d5_even_count] at e3
  have e4 := hyp x5
  rw [OMA.d5_even_count] at e4
  have d1 := OMA.d5_deg_count G hc t1134
  have f1 := hdeg t1134 (by omega)
  have d2 := OMA.d5_deg_count G hc t2113
  have f2 := hdeg t2113 (by omega)
  have d3 := OMA.d5_deg_count G hc t4431
  have f3 := hdeg t4431 (by omega)
  have d4 := OMA.d5_deg_count G hc t4311
  have f4 := hdeg t4311 (by omega)
  have b1 := OMA.d5_self_count G hc x1
  omega

theorem OMA.d5_leaf_7 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (t1134 : V) (h1134 : G.dist x0 t1134 = 1 ∧ G.dist x1 t1134 = 1 ∧ G.dist x3 t1134 = 3 ∧ G.dist x5 t1134 = 4)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1)
    (t4331 : V) (h4331 : G.dist x0 t4331 = 4 ∧ G.dist x1 t4331 = 3 ∧ G.dist x3 t4331 = 3 ∧ G.dist x5 t4331 = 1)
    (n4431 : ∀ y : V, ¬(G.dist x0 y = 4 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    (n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist t1134 y / 2) + (1 - G.dist t2113 y / 2) + (1 - G.dist t4311 y / 2) + (1 - G.dist t4331 y / 2) + (1 - G.dist x1 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist x5 y + 1) % 2 := fun y =>
    OMA.d5_arith_7 _ _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t1134 1 1 3 4 h1134 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4311 4 3 1 1 h4311 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t4331 4 3 3 1 h4331 (by omega) y)
      (n4431 y)
      (n5431 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x3
  rw [OMA.d5_even_count] at e3
  have e4 := hyp x5
  rw [OMA.d5_even_count] at e4
  have d1 := OMA.d5_deg_count G hc t1134
  have f1 := hdeg t1134 (by omega)
  have d2 := OMA.d5_deg_count G hc t2113
  have f2 := hdeg t2113 (by omega)
  have d3 := OMA.d5_deg_count G hc t4311
  have f3 := hdeg t4311 (by omega)
  have d4 := OMA.d5_deg_count G hc t4331
  have f4 := hdeg t4331 (by omega)
  have b1 := OMA.d5_self_count G hc x1
  omega

theorem OMA.d5_leaf_8 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (t1134 : V) (h1134 : G.dist x0 t1134 = 1 ∧ G.dist x1 t1134 = 1 ∧ G.dist x3 t1134 = 3 ∧ G.dist x5 t1134 = 4)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t3213 : V) (h3213 : G.dist x0 t3213 = 3 ∧ G.dist x1 t3213 = 2 ∧ G.dist x3 t3213 = 1 ∧ G.dist x5 t3213 = 3)
    (t5421 : V) (h5421 : G.dist x0 t5421 = 5 ∧ G.dist x1 t5421 = 4 ∧ G.dist x3 t5421 = 2 ∧ G.dist x5 t5421 = 1)
    (n4331 : ∀ y : V, ¬(G.dist x0 y = 4 ∧ G.dist x1 y = 3 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    (n4431 : ∀ y : V, ¬(G.dist x0 y = 4 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    (n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist x5 y / 2) + (1 - G.dist t1134 y / 2) + (1 - G.dist t5421 y / 2) + (1 - G.dist t3213 y / 2) + (1 - G.dist x0 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist t2113 y + 1) % 2 := fun y =>
    OMA.d5_arith_8 _ _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t1134 1 1 3 4 h1134 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t3213 3 2 1 3 h3213 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5421 5 4 2 1 h5421 (by omega) y)
      (n4331 y)
      (n4431 y)
      (n5431 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x3
  rw [OMA.d5_even_count] at e3
  have e4 := hyp t2113
  rw [OMA.d5_even_count] at e4
  have d1 := OMA.d5_deg_count G hc x5
  have f1 := hdeg x5 (by omega)
  have d2 := OMA.d5_deg_count G hc t1134
  have f2 := hdeg t1134 (by omega)
  have d3 := OMA.d5_deg_count G hc t5421
  have f3 := hdeg t5421 (by omega)
  have d4 := OMA.d5_deg_count G hc t3213
  have f4 := hdeg t3213 (by omega)
  have b1 := OMA.d5_self_count G hc x0
  omega

theorem OMA.d5_leaf_9 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (t1134 : V) (h1134 : G.dist x0 t1134 = 1 ∧ G.dist x1 t1134 = 1 ∧ G.dist x3 t1134 = 3 ∧ G.dist x5 t1134 = 4)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t5421 : V) (h5421 : G.dist x0 t5421 = 5 ∧ G.dist x1 t5421 = 4 ∧ G.dist x3 t5421 = 2 ∧ G.dist x5 t5421 = 1)
    (n3213 : ∀ y : V, ¬(G.dist x0 y = 3 ∧ G.dist x1 y = 2 ∧ G.dist x3 y = 1 ∧ G.dist x5 y = 3))
    (n4431 : ∀ y : V, ¬(G.dist x0 y = 4 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    (n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist t1134 y / 2) + (1 - G.dist t2113 y / 2) + (1 - G.dist t5421 y / 2) + (1 - G.dist x3 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x3 y + 1) % 2 + (G.dist x5 y + 1) % 2 := fun y =>
    OMA.d5_arith_9 _ _ _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t1134 1 1 3 4 h1134 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t5421 5 4 2 1 h5421 (by omega) y)
      (n3213 y)
      (n4431 y)
      (n5431 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x3
  rw [OMA.d5_even_count] at e2
  have e3 := hyp x5
  rw [OMA.d5_even_count] at e3
  have d1 := OMA.d5_deg_count G hc t1134
  have f1 := hdeg t1134 (by omega)
  have d2 := OMA.d5_deg_count G hc t2113
  have f2 := hdeg t2113 (by omega)
  have d3 := OMA.d5_deg_count G hc t5421
  have f3 := hdeg t5421 (by omega)
  have b1 := OMA.d5_self_count G hc x3
  omega

theorem OMA.d5_leaf_10 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (n1134 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 4))
    (n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist x1 y / 2) + (1 - G.dist x5 y / 2) + (1 - G.dist x3 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x3 y + 1) % 2 := fun y =>
    OMA.d5_arith_10 _ _ _ _ (hP y)
      (n1134 y)
      (n5431 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x3
  rw [OMA.d5_even_count] at e2
  have d1 := OMA.d5_deg_count G hc x1
  have f1 := hdeg x1 (by omega)
  have d2 := OMA.d5_deg_count G hc x5
  have f2 := hdeg x5 (by omega)
  have b1 := OMA.d5_self_count G hc x3
  omega

theorem OMA.d5_leaf_11 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (n5421 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 2 ∧ G.dist x5 y = 1))
    (n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist x5 y / 2) + (1 - G.dist x0 y) + (1 - G.dist t2113 y)
      ≤ (G.dist x0 y + 1) % 2 + (1 - G.dist x5 y) := fun y =>
    OMA.d5_arith_11 _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (n5421 y)
      (n5431 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have d1 := OMA.d5_deg_count G hc x5
  have f1 := hdeg x5 (by omega)
  have b1 := OMA.d5_self_count G hc x0
  have b2 := OMA.d5_self_count G hc t2113
  have b3 := OMA.d5_self_count G hc x5
  omega

theorem OMA.d5_leaf_12 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (n1124 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 2 ∧ G.dist x5 y = 4))
    : False := by
  have hpt : ∀ y : V, (1 - G.dist x5 y / 2) + (1 - G.dist t2113 y / 2) + (1 - G.dist x0 y)
      ≤ (G.dist x0 y + 1) % 2 + (G.dist x1 y + 1) % 2 := fun y =>
    OMA.d5_arith_12 _ _ _ _ _ (hP y)
      (OMA.d5_wit G hc x0 x1 x3 x5 hcap t2113 2 1 1 3 h2113 (by omega) y)
      (n1124 y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) => hpt y)
  simp only [Finset.sum_add_distrib] at hsum
  have e1 := hyp x0
  rw [OMA.d5_even_count] at e1
  have e2 := hyp x1
  rw [OMA.d5_even_count] at e2
  have d1 := OMA.d5_deg_count G hc x5
  have f1 := hdeg x5 (by omega)
  have d2 := OMA.d5_deg_count G hc t2113
  have f2 := hdeg t2113 (by omega)
  have b1 := OMA.d5_self_count G hc x0
  omega

theorem OMA.d5_tree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (k : ℕ) (x0 x1 x3 x5 : V)
    (hP : ∀ y : V, OMA.D5Prof (G.dist x0 y) (G.dist x1 y) (G.dist x3 y) (G.dist x5 y))
    (hcap : ∀ u w : V, 1 ≤ G.dist x0 u → 1 ≤ G.dist x0 w → G.dist u w ≤ 4)
    (hdeg : ∀ y : V, 1 ≤ G.dist x0 y → k ≤ G.degree y)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + k)
    (hr : 1 ≤ G.dist x0 x1 ∧ 1 ≤ G.dist x0 x3 ∧ 1 ≤ G.dist x0 x5)
    (t2113 : V) (h2113 : G.dist x0 t2113 = 2 ∧ G.dist x1 t2113 = 1 ∧ G.dist x3 t2113 = 1 ∧ G.dist x5 t2113 = 3)
    (t4311 : V) (h4311 : G.dist x0 t4311 = 4 ∧ G.dist x1 t4311 = 3 ∧ G.dist x3 t4311 = 1 ∧ G.dist x5 t4311 = 1) : False := by
  by_cases hq : ∃ t : V, G.dist x0 t = 1 ∧ G.dist x1 t = 1 ∧ G.dist x3 t = 2 ∧ G.dist x5 t = 4
  · obtain ⟨t1124, h1124⟩ := hq
    by_cases hq : ∃ t : V, G.dist x0 t = 5 ∧ G.dist x1 t = 4 ∧ G.dist x3 t = 3 ∧ G.dist x5 t = 1
    · obtain ⟨t5431, h5431⟩ := hq
      by_cases hq : ∃ t : V, G.dist x0 t = 5 ∧ G.dist x1 t = 4 ∧ G.dist x3 t = 2 ∧ G.dist x5 t = 1
      · obtain ⟨t5421, h5421⟩ := hq
        by_cases hq : ∃ t : V, G.dist x0 t = 1 ∧ G.dist x1 t = 1 ∧ G.dist x3 t = 3 ∧ G.dist x5 t = 4
        · obtain ⟨t1134, h1134⟩ := hq
          exact OMA.d5_leaf_1 G hc k x0 x1 x3 x5 hP hcap hdeg hyp t1134 h1134 t2113 h2113 t4311 h4311 t5431 h5431
        · have n1134 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 4) := fun y hy => hq ⟨y, hy⟩
          by_cases hq : ∃ t : V, G.dist x0 t = 3 ∧ G.dist x1 t = 3 ∧ G.dist x3 t = 1 ∧ G.dist x5 t = 2
          · obtain ⟨t3312, h3312⟩ := hq
            by_cases hq : ∃ t : V, G.dist x0 t = 2 ∧ G.dist x1 t = 1 ∧ G.dist x3 t = 3 ∧ G.dist x5 t = 3
            · obtain ⟨t2133, h2133⟩ := hq
              exact OMA.d5_leaf_2 G hc k x0 x1 x3 x5 hP hcap hdeg hyp t2113 h2113 t2133 h2133 t4311 h4311 t5431 h5431 n1134
            · have n2133 : ∀ y : V, ¬(G.dist x0 y = 2 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 3) := fun y hy => hq ⟨y, hy⟩
              exact OMA.d5_leaf_3 G hc k x0 x1 x3 x5 hP hcap hdeg hyp hr t3312 h3312 t4311 h4311 t5431 h5431 n1134 n2133
          · have n3312 : ∀ y : V, ¬(G.dist x0 y = 3 ∧ G.dist x1 y = 3 ∧ G.dist x3 y = 1 ∧ G.dist x5 y = 2) := fun y hy => hq ⟨y, hy⟩
            exact OMA.d5_leaf_4 G hc k x0 x1 x3 x5 hP hcap hdeg hyp t1124 h1124 t4311 h4311 t5431 h5431 n1134 n3312
      · have n5421 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 2 ∧ G.dist x5 y = 1) := fun y hy => hq ⟨y, hy⟩
        exact OMA.d5_leaf_5 G hc k x0 x1 x3 x5 hP hcap hdeg hyp hr t4311 h4311 t5431 h5431 n5421
    · have n5431 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1) := fun y hy => hq ⟨y, hy⟩
      by_cases hq : ∃ t : V, G.dist x0 t = 5 ∧ G.dist x1 t = 4 ∧ G.dist x3 t = 2 ∧ G.dist x5 t = 1
      · obtain ⟨t5421, h5421⟩ := hq
        by_cases hq : ∃ t : V, G.dist x0 t = 1 ∧ G.dist x1 t = 1 ∧ G.dist x3 t = 3 ∧ G.dist x5 t = 4
        · obtain ⟨t1134, h1134⟩ := hq
          by_cases hq : ∃ t : V, G.dist x0 t = 4 ∧ G.dist x1 t = 4 ∧ G.dist x3 t = 3 ∧ G.dist x5 t = 1
          · obtain ⟨t4431, h4431⟩ := hq
            exact OMA.d5_leaf_6 G hc k x0 x1 x3 x5 hP hcap hdeg hyp t1134 h1134 t2113 h2113 t4311 h4311 t4431 h4431 n5431
          · have n4431 : ∀ y : V, ¬(G.dist x0 y = 4 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1) := fun y hy => hq ⟨y, hy⟩
            by_cases hq : ∃ t : V, G.dist x0 t = 3 ∧ G.dist x1 t = 2 ∧ G.dist x3 t = 1 ∧ G.dist x5 t = 3
            · obtain ⟨t3213, h3213⟩ := hq
              by_cases hq : ∃ t : V, G.dist x0 t = 4 ∧ G.dist x1 t = 3 ∧ G.dist x3 t = 3 ∧ G.dist x5 t = 1
              · obtain ⟨t4331, h4331⟩ := hq
                exact OMA.d5_leaf_7 G hc k x0 x1 x3 x5 hP hcap hdeg hyp t1134 h1134 t2113 h2113 t4311 h4311 t4331 h4331 n4431 n5431
              · have n4331 : ∀ y : V, ¬(G.dist x0 y = 4 ∧ G.dist x1 y = 3 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 1) := fun y hy => hq ⟨y, hy⟩
                exact OMA.d5_leaf_8 G hc k x0 x1 x3 x5 hP hcap hdeg hyp hr t1134 h1134 t2113 h2113 t3213 h3213 t5421 h5421 n4331 n4431 n5431
            · have n3213 : ∀ y : V, ¬(G.dist x0 y = 3 ∧ G.dist x1 y = 2 ∧ G.dist x3 y = 1 ∧ G.dist x5 y = 3) := fun y hy => hq ⟨y, hy⟩
              exact OMA.d5_leaf_9 G hc k x0 x1 x3 x5 hP hcap hdeg hyp t1134 h1134 t2113 h2113 t5421 h5421 n3213 n4431 n5431
        · have n1134 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 3 ∧ G.dist x5 y = 4) := fun y hy => hq ⟨y, hy⟩
          exact OMA.d5_leaf_10 G hc k x0 x1 x3 x5 hP hdeg hyp hr n1134 n5431
      · have n5421 : ∀ y : V, ¬(G.dist x0 y = 5 ∧ G.dist x1 y = 4 ∧ G.dist x3 y = 2 ∧ G.dist x5 y = 1) := fun y hy => hq ⟨y, hy⟩
        exact OMA.d5_leaf_11 G hc k x0 x1 x3 x5 hP hcap hdeg hyp hr t2113 h2113 n5421 n5431
  · have n1124 : ∀ y : V, ¬(G.dist x0 y = 1 ∧ G.dist x1 y = 1 ∧ G.dist x3 y = 2 ∧ G.dist x5 y = 4) := fun y hy => hq ⟨y, hy⟩
    exact OMA.d5_leaf_12 G hc k x0 x1 x3 x5 hP hcap hdeg hyp hr t2113 h2113 n1124

theorem OMA.d5_core {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hc : G.Connected) (hle5 : ∀ u w : V, G.dist u w ≤ 5)
    (hlow : ∀ a b : V, G.dist a b = 5 →
      G.degree a < G.secondSmallestDegree ∨ G.degree b < G.secondSmallestDegree)
    (hyp : ∀ x : V, SimpleGraph.distEven G x ≤ 1 + G.secondSmallestDegree)
    (a b : V) (hab : G.dist a b = 5) (ha : G.degree a < G.secondSmallestDegree) : False := by
  have hdeg0 : ∀ y : V, y ≠ a → G.secondSmallestDegree ≤ G.degree y := by
    intro y hy
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G := G) a y (Ne.symm hy) with h | h
    · omega
    · exact h
  have hcap0 : ∀ u w : V, u ≠ a → w ≠ a → G.dist u w ≤ 4 := by
    intro u w hu hw
    by_contra hgt
    have h5 : G.dist u w = 5 := by
      have := hle5 u w
      omega
    rcases hlow u w h5 with h | h
    · have := hdeg0 u hu
      omega
    · have := hdeg0 w hw
      omega
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  have hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (p.getVert i) (p.getVert j) = j - i :=
    fun i j hij hj => OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.geodesic hc p hp i j hij (by omega)
  have hv0 : p.getVert 0 = a := p.getVert_zero
  have hne : ∀ u : V, 1 ≤ G.dist (p.getVert 0) u → u ≠ a := by
    intro u hu e
    rw [hv0, e, SimpleGraph.dist_self] at hu
    omega
  have hcap : ∀ u w : V, 1 ≤ G.dist (p.getVert 0) u → 1 ≤ G.dist (p.getVert 0) w →
      G.dist u w ≤ 4 := fun u w hu hw => hcap0 u w (hne u hu) (hne w hw)
  have hdeg : ∀ y : V, 1 ≤ G.dist (p.getVert 0) y → G.secondSmallestDegree ≤ G.degree y :=
    fun y hy => hdeg0 y (hne y hy)
  have g01 := hg 0 1 (by omega) (by omega)
  have g02 := hg 0 2 (by omega) (by omega)
  have g03 := hg 0 3 (by omega) (by omega)
  have g04 := hg 0 4 (by omega) (by omega)
  have g05 := hg 0 5 (by omega) (by omega)
  have g12 := hg 1 2 (by omega) (by omega)
  have g14 := hg 1 4 (by omega) (by omega)
  have g23 := hg 2 3 (by omega) (by omega)
  have g25 := hg 2 5 (by omega) (by omega)
  have g34 := hg 3 4 (by omega) (by omega)
  have g45 := hg 4 5 (by omega) (by omega)
  have g32 : G.dist (p.getVert 3) (p.getVert 2) = G.dist (p.getVert 2) (p.getVert 3) :=
    SimpleGraph.dist_comm
  have g52 : G.dist (p.getVert 5) (p.getVert 2) = G.dist (p.getVert 2) (p.getVert 5) :=
    SimpleGraph.dist_comm
  have g54 : G.dist (p.getVert 5) (p.getVert 4) = G.dist (p.getVert 4) (p.getVert 5) :=
    SimpleGraph.dist_comm
  have hP : ∀ y : V, OMA.D5Prof (G.dist (p.getVert 0) y) (G.dist (p.getVert 1) y)
      (G.dist (p.getVert 3) y) (G.dist (p.getVert 5) y) := by
    intro y
    have b01 := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.profile_bounds hc p.getVert hg y 0 1 (by omega) (by omega)
    have b03 := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.profile_bounds hc p.getVert hg y 0 3 (by omega) (by omega)
    have b05 := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.profile_bounds hc p.getVert hg y 0 5 (by omega) (by omega)
    have b13 := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.profile_bounds hc p.getVert hg y 1 3 (by omega) (by omega)
    have b15 := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.profile_bounds hc p.getVert hg y 1 5 (by omega) (by omega)
    have b35 := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.profile_bounds hc p.getVert hg y 3 5 (by omega) (by omega)
    have h5 := hle5 (p.getVert 0) y
    have c1 : 1 ≤ G.dist (p.getVert 0) y → G.dist (p.getVert 1) y ≤ 4 :=
      fun hy => hcap (p.getVert 1) y (by omega) hy
    have c3 : 1 ≤ G.dist (p.getVert 0) y → G.dist (p.getVert 3) y ≤ 4 :=
      fun hy => hcap (p.getVert 3) y (by omega) hy
    have c5 : 1 ≤ G.dist (p.getVert 0) y → G.dist (p.getVert 5) y ≤ 4 :=
      fun hy => hcap (p.getVert 5) y (by omega) hy
    unfold OMA.D5Prof
    refine ⟨h5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c1, c3, c5⟩ <;> omega
  exact OMA.d5_tree G hc G.secondSmallestDegree (p.getVert 0) (p.getVert 1) (p.getVert 3)
    (p.getVert 5) hP hcap hdeg hyp (by omega) (p.getVert 2) (by omega) (p.getVert 4) (by omega)

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H2_R1.H2 := by
  unfold OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H2_R1.H2
  intro V _ _ _ G _ hc hdiam _ hlow _ _ hyp _
  exfalso
  have hne : G.ediam ≠ ⊤ := SimpleGraph.ediam_ne_top_of_diam_ne_zero (by omega)
  have hle5 : ∀ u w : V, G.dist u w ≤ 5 := by
    intro u w
    have := SimpleGraph.dist_le_diam hne (u := u) (v := w)
    omega
  obtain ⟨a, b, hab⟩ := SimpleGraph.exists_dist_eq_diam (G := G)
  rw [hdiam] at hab
  rcases hlow a b hab with h | h
  · exact OMA.d5_core G hc hle5 hlow hyp a b hab h
  · exact OMA.d5_core G hc hle5 hlow hyp b a (by rw [SimpleGraph.dist_comm]; exact hab) h
