import OMAReductions.R_UnionClosed_union_closed_variants_univ_card_R1_H2_R1
import Mathlib
-- Credit: @LordMike
-- The lemmas indexed_sum, indicator_join, indicator_force, decode_union and the whole FranklGlobal block
-- (weight_sum, reassemble, weight_witness, slice_data, coordinates, weight_from_fibers, nonempty_full) are
-- taken from the merged proof proofs/UnionClosed.union_closed.variants.univ_card.R1.H3.lean (itself adapted
-- from the reduction UnionClosed.union_closed.variants.univ_card.R2), with the minimum size 5 replaced by 4.

/-!
Row 32 of Table I of Vuckovic and Zivkovic, The 12-Element Case of Frankl's Conjecture (2017):
a 4-set S with weight 5 on S and 2 elsewhere (target weight 18). The fiber over a set K outside S is a
union-closed family on the 16 subsets of S; its score is bounded below by -16 for K empty, by 16 for K
the whole complement, and by 0 otherwise. The exclusions used are: no 4-set inside a 5-set (row 30) and
no two 4-sets meeting in exactly two points (row 31). The layer certificates were generated afresh.
-/

namespace FranklFour

lemma layer4_0 (v : ℕ → ℤ) (_bit : ∀ i, v i=0 ∨ v i=1)
    (_join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (small : ∀ i ∈ ([1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([0,15] : List ℕ), v i=1) :
    (-16 : ℤ) ≤ (-18) * v 0 + (-13) * v 1 + (-13) * v 2 + (-8) * v 3 + (-13) * v 4 + (-8) * v 5 + (-8) * v 6 + (-3) * v 7 + (-13) * v 8 + (-8) * v 9 + (-8) * v 10 + (-3) * v 11 + (-8) * v 12 + (-3) * v 13 + (-3) * v 14 + 2 * v 15 := by
  have o0 : v 0 = 1 := fixed 0 (by decide)
  have z1 : v 1 = 0 := small 1 (by decide)
  have z2 : v 2 = 0 := small 2 (by decide)
  have z3 : v 3 = 0 := small 3 (by decide)
  have z4 : v 4 = 0 := small 4 (by decide)
  have z5 : v 5 = 0 := small 5 (by decide)
  have z6 : v 6 = 0 := small 6 (by decide)
  have z7 : v 7 = 0 := small 7 (by decide)
  have z8 : v 8 = 0 := small 8 (by decide)
  have z9 : v 9 = 0 := small 9 (by decide)
  have z10 : v 10 = 0 := small 10 (by decide)
  have z11 : v 11 = 0 := small 11 (by decide)
  have z12 : v 12 = 0 := small 12 (by decide)
  have z13 : v 13 = 0 := small 13 (by decide)
  have z14 : v 14 = 0 := small 14 (by decide)
  have o15 : v 15 = 1 := fixed 15 (by decide)
  omega

lemma layer4_1 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (_join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (small : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12,15] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([(7,15),(11,15),(13,15),(14,15)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-16) * v 0 + (-11) * v 1 + (-11) * v 2 + (-6) * v 3 + (-11) * v 4 + (-6) * v 5 + (-6) * v 6 + (-1) * v 7 + (-11) * v 8 + (-6) * v 9 + (-6) * v 10 + (-1) * v 11 + (-6) * v 12 + (-1) * v 13 + (-1) * v 14 + 4 * v 15 := by
  have z0 : v 0 = 0 := small 0 (by decide)
  have z1 : v 1 = 0 := small 1 (by decide)
  have z2 : v 2 = 0 := small 2 (by decide)
  have z3 : v 3 = 0 := small 3 (by decide)
  have z4 : v 4 = 0 := small 4 (by decide)
  have z5 : v 5 = 0 := small 5 (by decide)
  have z6 : v 6 = 0 := small 6 (by decide)
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have z8 : v 8 = 0 := small 8 (by decide)
  have z9 : v 9 = 0 := small 9 (by decide)
  have z10 : v 10 = 0 := small 10 (by decide)
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have z12 : v 12 = 0 := small 12 (by decide)
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have z15 : v 15 = 0 := small 15 (by decide)
  have o15 : v 15 = 1 := fixed 15 (by decide)
  omega

lemma layer4_2 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (_join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (small : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([(3,7),(3,11),(3,12),(5,7),(5,10),(5,13),(6,7),(6,9),(6,14),(9,11),(9,13),(10,11),(10,14),(12,13),(12,14)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-14) * v 0 + (-9) * v 1 + (-9) * v 2 + (-4) * v 3 + (-9) * v 4 + (-4) * v 5 + (-4) * v 6 + 1 * v 7 + (-9) * v 8 + (-4) * v 9 + (-4) * v 10 + 1 * v 11 + (-4) * v 12 + 1 * v 13 + 1 * v 14 + 6 * v 15 := by
  have z0 : v 0 = 0 := small 0 (by decide)
  have z1 : v 1 = 0 := small 1 (by decide)
  have z2 : v 2 = 0 := small 2 (by decide)
  have z3 : v 3 = 0 := small 3 (by decide)
  have z4 : v 4 = 0 := small 4 (by decide)
  have z5 : v 5 = 0 := small 5 (by decide)
  have z6 : v 6 = 0 := small 6 (by decide)
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have z8 : v 8 = 0 := small 8 (by decide)
  have z9 : v 9 = 0 := small 9 (by decide)
  have z10 : v 10 = 0 := small 10 (by decide)
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have z12 : v 12 = 0 := small 12 (by decide)
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  omega

lemma layer4_3 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (small : ∀ i ∈ ([0] : List ℕ), v i=0)
    (apart : ∀ i j, (i,j) ∈ ([(1,3),(1,5),(1,9),(2,3),(2,6),(2,10),(4,5),(4,6),(4,12),(8,9),(8,10),(8,12)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-12) * v 0 + (-7) * v 1 + (-7) * v 2 + (-2) * v 3 + (-7) * v 4 + (-2) * v 5 + (-2) * v 6 + 3 * v 7 + (-7) * v 8 + (-2) * v 9 + (-2) * v 10 + 3 * v 11 + (-2) * v 12 + 3 * v 13 + 3 * v 14 + 8 * v 15 := by
  have z0 : v 0 = 0 := small 0 (by decide)
  have l1 : 0 ≤ v 1 := by rcases bit 1 with h|h <;> omega
  have u1 : v 1 ≤ 1 := by rcases bit 1 with h|h <;> omega
  have l2 : 0 ≤ v 2 := by rcases bit 2 with h|h <;> omega
  have u2 : v 2 ≤ 1 := by rcases bit 2 with h|h <;> omega
  have l3 : 0 ≤ v 3 := by rcases bit 3 with h|h <;> omega
  have u3 : v 3 ≤ 1 := by rcases bit 3 with h|h <;> omega
  have l4 : 0 ≤ v 4 := by rcases bit 4 with h|h <;> omega
  have u4 : v 4 ≤ 1 := by rcases bit 4 with h|h <;> omega
  have l5 : 0 ≤ v 5 := by rcases bit 5 with h|h <;> omega
  have u5 : v 5 ≤ 1 := by rcases bit 5 with h|h <;> omega
  have l6 : 0 ≤ v 6 := by rcases bit 6 with h|h <;> omega
  have u6 : v 6 ≤ 1 := by rcases bit 6 with h|h <;> omega
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have l8 : 0 ≤ v 8 := by rcases bit 8 with h|h <;> omega
  have u8 : v 8 ≤ 1 := by rcases bit 8 with h|h <;> omega
  have l9 : 0 ≤ v 9 := by rcases bit 9 with h|h <;> omega
  have u9 : v 9 ≤ 1 := by rcases bit 9 with h|h <;> omega
  have l10 : 0 ≤ v 10 := by rcases bit 10 with h|h <;> omega
  have u10 : v 10 ≤ 1 := by rcases bit 10 with h|h <;> omega
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have l12 : 0 ≤ v 12 := by rcases bit 12 with h|h <;> omega
  have u12 : v 12 ≤ 1 := by rcases bit 12 with h|h <;> omega
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  rcases bit 1 with h1 | h1
  · rcases bit 2 with h2 | h2
    · rcases bit 4 with h4 | h4
      · rcases bit 8 with h8 | h8
        · rcases bit 3 with h3 | h3
          · rcases bit 5 with h5 | h5
            · omega
            · rcases bit 6 with h6 | h6
              · omega
              · have jn_6_5 : v 6 + v 5 - v 7 ≤ 1 := join 6 5
                omega
          · rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · omega
              · have jn_6_3 : v 6 + v 3 - v 7 ≤ 1 := join 6 3
                omega
            · have jn_5_3 : v 5 + v 3 - v 7 ≤ 1 := join 5 3
              rcases bit 6 with h6 | h6
              · omega
              · rcases bit 9 with h9 | h9
                · omega
                · have jn_9_3 : v 9 + v 3 - v 11 ≤ 1 := join 9 3
                  have jn_9_5 : v 9 + v 5 - v 13 ≤ 1 := join 9 5
                  omega
        · rcases bit 3 with h3 | h3
          · rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · rcases bit 12 with h12 | h12
                    · omega
                    · have ap_8_12 : v 8 + v 12 ≤ 1 := apart 8 12 (by decide)
                      omega
                  · have ap_8_10 : v 8 + v 10 ≤ 1 := apart 8 10 (by decide)
                    omega
                · have ap_8_9 : v 8 + v 9 ≤ 1 := apart 8 9 (by decide)
                  omega
              · have jn_6_8 : v 6 + v 8 - v 14 ≤ 1 := join 6 8
                rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · omega
                  · have ap_8_10 : v 8 + v 10 ≤ 1 := apart 8 10 (by decide)
                    omega
                · have ap_8_9 : v 8 + v 9 ≤ 1 := apart 8 9 (by decide)
                  omega
            · have jn_5_8 : v 5 + v 8 - v 13 ≤ 1 := join 5 8
              rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · omega
                  · have ap_8_10 : v 8 + v 10 ≤ 1 := apart 8 10 (by decide)
                    omega
                · have ap_8_9 : v 8 + v 9 ≤ 1 := apart 8 9 (by decide)
                  omega
              · have jn_6_5 : v 6 + v 5 - v 7 ≤ 1 := join 6 5
                have jn_6_8 : v 6 + v 8 - v 14 ≤ 1 := join 6 8
                omega
          · have jn_3_8 : v 3 + v 8 - v 11 ≤ 1 := join 3 8
            rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · omega
                  · have ap_8_10 : v 8 + v 10 ≤ 1 := apart 8 10 (by decide)
                    omega
                · have ap_8_9 : v 8 + v 9 ≤ 1 := apart 8 9 (by decide)
                  omega
              · have jn_6_3 : v 6 + v 3 - v 7 ≤ 1 := join 6 3
                have jn_6_8 : v 6 + v 8 - v 14 ≤ 1 := join 6 8
                omega
            · have jn_5_3 : v 5 + v 3 - v 7 ≤ 1 := join 5 3
              have jn_5_8 : v 5 + v 8 - v 13 ≤ 1 := join 5 8
              rcases bit 6 with h6 | h6
              · omega
              · have jn_6_8 : v 6 + v 8 - v 14 ≤ 1 := join 6 8
                omega
      · rcases bit 8 with h8 | h8
        · rcases bit 3 with h3 | h3
          · rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · rcases bit 12 with h12 | h12
                    · omega
                    · have ap_4_12 : v 4 + v 12 ≤ 1 := apart 4 12 (by decide)
                      omega
                  · have jn_10_4 : v 10 + v 4 - v 14 ≤ 1 := join 10 4
                    omega
                · have jn_9_4 : v 9 + v 4 - v 13 ≤ 1 := join 9 4
                  rcases bit 10 with h10 | h10
                  · omega
                  · have jn_10_4 : v 10 + v 4 - v 14 ≤ 1 := join 10 4
                    have jn_10_9 : v 10 + v 9 - v 11 ≤ 1 := join 10 9
                    omega
              · have ap_4_6 : v 4 + v 6 ≤ 1 := apart 4 6 (by decide)
                omega
            · have ap_4_5 : v 4 + v 5 ≤ 1 := apart 4 5 (by decide)
              omega
          · have jn_3_4 : v 3 + v 4 - v 7 ≤ 1 := join 3 4
            rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · omega
                  · have jn_10_3 : v 10 + v 3 - v 11 ≤ 1 := join 10 3
                    have jn_10_4 : v 10 + v 4 - v 14 ≤ 1 := join 10 4
                    omega
                · have jn_9_3 : v 9 + v 3 - v 11 ≤ 1 := join 9 3
                  have jn_9_4 : v 9 + v 4 - v 13 ≤ 1 := join 9 4
                  omega
              · have ap_4_6 : v 4 + v 6 ≤ 1 := apart 4 6 (by decide)
                omega
            · have ap_4_5 : v 4 + v 5 ≤ 1 := apart 4 5 (by decide)
              omega
        · have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
          have ap_4_12 : v 4 + v 12 ≤ 1 := apart 4 12 (by decide)
          omega
    · rcases bit 4 with h4 | h4
      · rcases bit 8 with h8 | h8
        · rcases bit 3 with h3 | h3
          · rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · rcases bit 12 with h12 | h12
                    · omega
                    · have jn_12_2 : v 12 + v 2 - v 14 ≤ 1 := join 12 2
                      omega
                  · have ap_2_10 : v 2 + v 10 ≤ 1 := apart 2 10 (by decide)
                    omega
                · have jn_9_2 : v 9 + v 2 - v 11 ≤ 1 := join 9 2
                  rcases bit 10 with h10 | h10
                  · omega
                  · have ap_2_10 : v 2 + v 10 ≤ 1 := apart 2 10 (by decide)
                    omega
              · have ap_2_6 : v 2 + v 6 ≤ 1 := apart 2 6 (by decide)
                omega
            · have jn_5_2 : v 5 + v 2 - v 7 ≤ 1 := join 5 2
              rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · omega
                  · have ap_2_10 : v 2 + v 10 ≤ 1 := apart 2 10 (by decide)
                    omega
                · have jn_9_2 : v 9 + v 2 - v 11 ≤ 1 := join 9 2
                  have jn_9_5 : v 9 + v 5 - v 13 ≤ 1 := join 9 5
                  omega
              · have ap_2_6 : v 2 + v 6 ≤ 1 := apart 2 6 (by decide)
                omega
          · have ap_2_3 : v 2 + v 3 ≤ 1 := apart 2 3 (by decide)
            omega
        · have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
          have ap_2_10 : v 2 + v 10 ≤ 1 := apart 2 10 (by decide)
          omega
      · have jn_4_2 : v 4 + v 2 - v 6 ≤ 1 := join 4 2
        have ap_2_6 : v 2 + v 6 ≤ 1 := apart 2 6 (by decide)
        omega
  · rcases bit 2 with h2 | h2
    · rcases bit 4 with h4 | h4
      · rcases bit 8 with h8 | h8
        · rcases bit 3 with h3 | h3
          · rcases bit 5 with h5 | h5
            · rcases bit 6 with h6 | h6
              · rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · rcases bit 12 with h12 | h12
                    · omega
                    · have jn_12_1 : v 12 + v 1 - v 13 ≤ 1 := join 12 1
                      omega
                  · have jn_10_1 : v 10 + v 1 - v 11 ≤ 1 := join 10 1
                    omega
                · have ap_1_9 : v 1 + v 9 ≤ 1 := apart 1 9 (by decide)
                  omega
              · have jn_6_1 : v 6 + v 1 - v 7 ≤ 1 := join 6 1
                rcases bit 9 with h9 | h9
                · rcases bit 10 with h10 | h10
                  · omega
                  · have jn_10_1 : v 10 + v 1 - v 11 ≤ 1 := join 10 1
                    have jn_10_6 : v 10 + v 6 - v 14 ≤ 1 := join 10 6
                    omega
                · have ap_1_9 : v 1 + v 9 ≤ 1 := apart 1 9 (by decide)
                  omega
            · have ap_1_5 : v 1 + v 5 ≤ 1 := apart 1 5 (by decide)
              omega
          · have ap_1_3 : v 1 + v 3 ≤ 1 := apart 1 3 (by decide)
            omega
        · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
          have ap_1_9 : v 1 + v 9 ≤ 1 := apart 1 9 (by decide)
          omega
      · have jn_4_1 : v 4 + v 1 - v 5 ≤ 1 := join 4 1
        have ap_1_5 : v 1 + v 5 ≤ 1 := apart 1 5 (by decide)
        omega
    · have jn_2_1 : v 2 + v 1 - v 3 ≤ 1 := join 2 1
      have ap_1_3 : v 1 + v 3 ≤ 1 := apart 1 3 (by decide)
      omega

lemma layer4_4 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (_small : ∀ i ∈ ([] : List ℕ), v i=0)
    (apart : ∀ i j, (i,j) ∈ ([(0,1),(0,2),(0,4),(0,8)] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-10) * v 0 + (-5) * v 1 + (-5) * v 2 + 0 * v 3 + (-5) * v 4 + 0 * v 5 + 0 * v 6 + 5 * v 7 + (-5) * v 8 + 0 * v 9 + 0 * v 10 + 5 * v 11 + 0 * v 12 + 5 * v 13 + 5 * v 14 + 10 * v 15 := by
  have l0 : 0 ≤ v 0 := by rcases bit 0 with h|h <;> omega
  have u0 : v 0 ≤ 1 := by rcases bit 0 with h|h <;> omega
  have l1 : 0 ≤ v 1 := by rcases bit 1 with h|h <;> omega
  have u1 : v 1 ≤ 1 := by rcases bit 1 with h|h <;> omega
  have l2 : 0 ≤ v 2 := by rcases bit 2 with h|h <;> omega
  have u2 : v 2 ≤ 1 := by rcases bit 2 with h|h <;> omega
  have l3 : 0 ≤ v 3 := by rcases bit 3 with h|h <;> omega
  have u3 : v 3 ≤ 1 := by rcases bit 3 with h|h <;> omega
  have l4 : 0 ≤ v 4 := by rcases bit 4 with h|h <;> omega
  have u4 : v 4 ≤ 1 := by rcases bit 4 with h|h <;> omega
  have l5 : 0 ≤ v 5 := by rcases bit 5 with h|h <;> omega
  have u5 : v 5 ≤ 1 := by rcases bit 5 with h|h <;> omega
  have l6 : 0 ≤ v 6 := by rcases bit 6 with h|h <;> omega
  have u6 : v 6 ≤ 1 := by rcases bit 6 with h|h <;> omega
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have l8 : 0 ≤ v 8 := by rcases bit 8 with h|h <;> omega
  have u8 : v 8 ≤ 1 := by rcases bit 8 with h|h <;> omega
  have l9 : 0 ≤ v 9 := by rcases bit 9 with h|h <;> omega
  have u9 : v 9 ≤ 1 := by rcases bit 9 with h|h <;> omega
  have l10 : 0 ≤ v 10 := by rcases bit 10 with h|h <;> omega
  have u10 : v 10 ≤ 1 := by rcases bit 10 with h|h <;> omega
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have l12 : 0 ≤ v 12 := by rcases bit 12 with h|h <;> omega
  have u12 : v 12 ≤ 1 := by rcases bit 12 with h|h <;> omega
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  rcases bit 0 with h0 | h0
  · rcases bit 1 with h1 | h1
    · rcases bit 2 with h2 | h2
      · omega
      · rcases bit 4 with h4 | h4
        · omega
        · have jn_4_2 : v 4 + v 2 - v 6 ≤ 1 := join 4 2
          rcases bit 8 with h8 | h8
          · omega
          · have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
            have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
            have jn_8_6 : v 8 + v 6 - v 14 ≤ 1 := join 8 6
            omega
    · rcases bit 2 with h2 | h2
      · rcases bit 4 with h4 | h4
        · omega
        · have jn_4_1 : v 4 + v 1 - v 5 ≤ 1 := join 4 1
          rcases bit 8 with h8 | h8
          · omega
          · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
            have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
            have jn_8_5 : v 8 + v 5 - v 13 ≤ 1 := join 8 5
            omega
      · have jn_2_1 : v 2 + v 1 - v 3 ≤ 1 := join 2 1
        rcases bit 4 with h4 | h4
        · rcases bit 8 with h8 | h8
          · omega
          · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
            have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
            have jn_8_3 : v 8 + v 3 - v 11 ≤ 1 := join 8 3
            omega
        · have jn_4_1 : v 4 + v 1 - v 5 ≤ 1 := join 4 1
          have jn_4_2 : v 4 + v 2 - v 6 ≤ 1 := join 4 2
          have jn_4_3 : v 4 + v 3 - v 7 ≤ 1 := join 4 3
          rcases bit 8 with h8 | h8
          · omega
          · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
            have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
            have jn_8_3 : v 8 + v 3 - v 11 ≤ 1 := join 8 3
            have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
            have jn_8_5 : v 8 + v 5 - v 13 ≤ 1 := join 8 5
            have jn_8_6 : v 8 + v 6 - v 14 ≤ 1 := join 8 6
            omega
  · rcases bit 1 with h1 | h1
    · rcases bit 2 with h2 | h2
      · rcases bit 4 with h4 | h4
        · rcases bit 8 with h8 | h8
          · omega
          · have ap_0_8 : v 0 + v 8 ≤ 1 := apart 0 8 (by decide)
            omega
        · have ap_0_4 : v 0 + v 4 ≤ 1 := apart 0 4 (by decide)
          omega
      · have ap_0_2 : v 0 + v 2 ≤ 1 := apart 0 2 (by decide)
        omega
    · have ap_0_1 : v 0 + v 1 ≤ 1 := apart 0 1 (by decide)
      omega

lemma layer4_5 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (_small : ∀ i ∈ ([] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-8) * v 0 + (-3) * v 1 + (-3) * v 2 + 2 * v 3 + (-3) * v 4 + 2 * v 5 + 2 * v 6 + 7 * v 7 + (-3) * v 8 + 2 * v 9 + 2 * v 10 + 7 * v 11 + 2 * v 12 + 7 * v 13 + 7 * v 14 + 12 * v 15 := by
  have l0 : 0 ≤ v 0 := by rcases bit 0 with h|h <;> omega
  have u0 : v 0 ≤ 1 := by rcases bit 0 with h|h <;> omega
  have l1 : 0 ≤ v 1 := by rcases bit 1 with h|h <;> omega
  have u1 : v 1 ≤ 1 := by rcases bit 1 with h|h <;> omega
  have l2 : 0 ≤ v 2 := by rcases bit 2 with h|h <;> omega
  have u2 : v 2 ≤ 1 := by rcases bit 2 with h|h <;> omega
  have l3 : 0 ≤ v 3 := by rcases bit 3 with h|h <;> omega
  have u3 : v 3 ≤ 1 := by rcases bit 3 with h|h <;> omega
  have l4 : 0 ≤ v 4 := by rcases bit 4 with h|h <;> omega
  have u4 : v 4 ≤ 1 := by rcases bit 4 with h|h <;> omega
  have l5 : 0 ≤ v 5 := by rcases bit 5 with h|h <;> omega
  have u5 : v 5 ≤ 1 := by rcases bit 5 with h|h <;> omega
  have l6 : 0 ≤ v 6 := by rcases bit 6 with h|h <;> omega
  have u6 : v 6 ≤ 1 := by rcases bit 6 with h|h <;> omega
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have l8 : 0 ≤ v 8 := by rcases bit 8 with h|h <;> omega
  have u8 : v 8 ≤ 1 := by rcases bit 8 with h|h <;> omega
  have l9 : 0 ≤ v 9 := by rcases bit 9 with h|h <;> omega
  have u9 : v 9 ≤ 1 := by rcases bit 9 with h|h <;> omega
  have l10 : 0 ≤ v 10 := by rcases bit 10 with h|h <;> omega
  have u10 : v 10 ≤ 1 := by rcases bit 10 with h|h <;> omega
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have l12 : 0 ≤ v 12 := by rcases bit 12 with h|h <;> omega
  have u12 : v 12 ≤ 1 := by rcases bit 12 with h|h <;> omega
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  rcases bit 0 with h0 | h0
  · omega
  · rcases bit 1 with h1 | h1
    · rcases bit 2 with h2 | h2
      · rcases bit 4 with h4 | h4
        · omega
        · rcases bit 8 with h8 | h8
          · omega
          · have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
            omega
      · rcases bit 4 with h4 | h4
        · rcases bit 8 with h8 | h8
          · omega
          · have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
            omega
        · have jn_4_2 : v 4 + v 2 - v 6 ≤ 1 := join 4 2
          rcases bit 8 with h8 | h8
          · omega
          · have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
            have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
            have jn_8_6 : v 8 + v 6 - v 14 ≤ 1 := join 8 6
            omega
    · rcases bit 2 with h2 | h2
      · rcases bit 4 with h4 | h4
        · rcases bit 8 with h8 | h8
          · omega
          · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
            omega
        · have jn_4_1 : v 4 + v 1 - v 5 ≤ 1 := join 4 1
          rcases bit 8 with h8 | h8
          · omega
          · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
            have jn_8_4 : v 8 + v 4 - v 12 ≤ 1 := join 8 4
            have jn_8_5 : v 8 + v 5 - v 13 ≤ 1 := join 8 5
            omega
      · have jn_2_1 : v 2 + v 1 - v 3 ≤ 1 := join 2 1
        rcases bit 4 with h4 | h4
        · rcases bit 8 with h8 | h8
          · omega
          · have jn_8_1 : v 8 + v 1 - v 9 ≤ 1 := join 8 1
            have jn_8_2 : v 8 + v 2 - v 10 ≤ 1 := join 8 2
            have jn_8_3 : v 8 + v 3 - v 11 ≤ 1 := join 8 3
            omega
        · have jn_4_1 : v 4 + v 1 - v 5 ≤ 1 := join 4 1
          have jn_4_2 : v 4 + v 2 - v 6 ≤ 1 := join 4 2
          have jn_4_3 : v 4 + v 3 - v 7 ≤ 1 := join 4 3
          omega

lemma layer4_6 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (_join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (_small : ∀ i ∈ ([] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-6) * v 0 + (-1) * v 1 + (-1) * v 2 + 4 * v 3 + (-1) * v 4 + 4 * v 5 + 4 * v 6 + 9 * v 7 + (-1) * v 8 + 4 * v 9 + 4 * v 10 + 9 * v 11 + 4 * v 12 + 9 * v 13 + 9 * v 14 + 14 * v 15 := by
  have l0 : 0 ≤ v 0 := by rcases bit 0 with h|h <;> omega
  have u0 : v 0 ≤ 1 := by rcases bit 0 with h|h <;> omega
  have l1 : 0 ≤ v 1 := by rcases bit 1 with h|h <;> omega
  have u1 : v 1 ≤ 1 := by rcases bit 1 with h|h <;> omega
  have l2 : 0 ≤ v 2 := by rcases bit 2 with h|h <;> omega
  have u2 : v 2 ≤ 1 := by rcases bit 2 with h|h <;> omega
  have l3 : 0 ≤ v 3 := by rcases bit 3 with h|h <;> omega
  have u3 : v 3 ≤ 1 := by rcases bit 3 with h|h <;> omega
  have l4 : 0 ≤ v 4 := by rcases bit 4 with h|h <;> omega
  have u4 : v 4 ≤ 1 := by rcases bit 4 with h|h <;> omega
  have l5 : 0 ≤ v 5 := by rcases bit 5 with h|h <;> omega
  have u5 : v 5 ≤ 1 := by rcases bit 5 with h|h <;> omega
  have l6 : 0 ≤ v 6 := by rcases bit 6 with h|h <;> omega
  have u6 : v 6 ≤ 1 := by rcases bit 6 with h|h <;> omega
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have l8 : 0 ≤ v 8 := by rcases bit 8 with h|h <;> omega
  have u8 : v 8 ≤ 1 := by rcases bit 8 with h|h <;> omega
  have l9 : 0 ≤ v 9 := by rcases bit 9 with h|h <;> omega
  have u9 : v 9 ≤ 1 := by rcases bit 9 with h|h <;> omega
  have l10 : 0 ≤ v 10 := by rcases bit 10 with h|h <;> omega
  have u10 : v 10 ≤ 1 := by rcases bit 10 with h|h <;> omega
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have l12 : 0 ≤ v 12 := by rcases bit 12 with h|h <;> omega
  have u12 : v 12 ≤ 1 := by rcases bit 12 with h|h <;> omega
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  omega

lemma layer4_7 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (_join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (_small : ∀ i ∈ ([] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (0 : ℤ) ≤ (-4) * v 0 + 1 * v 1 + 1 * v 2 + 6 * v 3 + 1 * v 4 + 6 * v 5 + 6 * v 6 + 11 * v 7 + 1 * v 8 + 6 * v 9 + 6 * v 10 + 11 * v 11 + 6 * v 12 + 11 * v 13 + 11 * v 14 + 16 * v 15 := by
  have l0 : 0 ≤ v 0 := by rcases bit 0 with h|h <;> omega
  have u0 : v 0 ≤ 1 := by rcases bit 0 with h|h <;> omega
  have l1 : 0 ≤ v 1 := by rcases bit 1 with h|h <;> omega
  have u1 : v 1 ≤ 1 := by rcases bit 1 with h|h <;> omega
  have l2 : 0 ≤ v 2 := by rcases bit 2 with h|h <;> omega
  have u2 : v 2 ≤ 1 := by rcases bit 2 with h|h <;> omega
  have l3 : 0 ≤ v 3 := by rcases bit 3 with h|h <;> omega
  have u3 : v 3 ≤ 1 := by rcases bit 3 with h|h <;> omega
  have l4 : 0 ≤ v 4 := by rcases bit 4 with h|h <;> omega
  have u4 : v 4 ≤ 1 := by rcases bit 4 with h|h <;> omega
  have l5 : 0 ≤ v 5 := by rcases bit 5 with h|h <;> omega
  have u5 : v 5 ≤ 1 := by rcases bit 5 with h|h <;> omega
  have l6 : 0 ≤ v 6 := by rcases bit 6 with h|h <;> omega
  have u6 : v 6 ≤ 1 := by rcases bit 6 with h|h <;> omega
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have l8 : 0 ≤ v 8 := by rcases bit 8 with h|h <;> omega
  have u8 : v 8 ≤ 1 := by rcases bit 8 with h|h <;> omega
  have l9 : 0 ≤ v 9 := by rcases bit 9 with h|h <;> omega
  have u9 : v 9 ≤ 1 := by rcases bit 9 with h|h <;> omega
  have l10 : 0 ≤ v 10 := by rcases bit 10 with h|h <;> omega
  have u10 : v 10 ≤ 1 := by rcases bit 10 with h|h <;> omega
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have l12 : 0 ≤ v 12 := by rcases bit 12 with h|h <;> omega
  have u12 : v 12 ≤ 1 := by rcases bit 12 with h|h <;> omega
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  omega

lemma layer4_8 (v : ℕ → ℤ) (bit : ∀ i, v i=0 ∨ v i=1)
    (_join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (_small : ∀ i ∈ ([] : List ℕ), v i=0)
    (_apart : ∀ i j, (i,j) ∈ ([] : List (ℕ × ℕ)) → v i + v j ≤ 1)
    (fixed : ∀ i ∈ ([15] : List ℕ), v i=1) :
    (16 : ℤ) ≤ (-2) * v 0 + 3 * v 1 + 3 * v 2 + 8 * v 3 + 3 * v 4 + 8 * v 5 + 8 * v 6 + 13 * v 7 + 3 * v 8 + 8 * v 9 + 8 * v 10 + 13 * v 11 + 8 * v 12 + 13 * v 13 + 13 * v 14 + 18 * v 15 := by
  have l0 : 0 ≤ v 0 := by rcases bit 0 with h|h <;> omega
  have u0 : v 0 ≤ 1 := by rcases bit 0 with h|h <;> omega
  have l1 : 0 ≤ v 1 := by rcases bit 1 with h|h <;> omega
  have u1 : v 1 ≤ 1 := by rcases bit 1 with h|h <;> omega
  have l2 : 0 ≤ v 2 := by rcases bit 2 with h|h <;> omega
  have u2 : v 2 ≤ 1 := by rcases bit 2 with h|h <;> omega
  have l3 : 0 ≤ v 3 := by rcases bit 3 with h|h <;> omega
  have u3 : v 3 ≤ 1 := by rcases bit 3 with h|h <;> omega
  have l4 : 0 ≤ v 4 := by rcases bit 4 with h|h <;> omega
  have u4 : v 4 ≤ 1 := by rcases bit 4 with h|h <;> omega
  have l5 : 0 ≤ v 5 := by rcases bit 5 with h|h <;> omega
  have u5 : v 5 ≤ 1 := by rcases bit 5 with h|h <;> omega
  have l6 : 0 ≤ v 6 := by rcases bit 6 with h|h <;> omega
  have u6 : v 6 ≤ 1 := by rcases bit 6 with h|h <;> omega
  have l7 : 0 ≤ v 7 := by rcases bit 7 with h|h <;> omega
  have u7 : v 7 ≤ 1 := by rcases bit 7 with h|h <;> omega
  have l8 : 0 ≤ v 8 := by rcases bit 8 with h|h <;> omega
  have u8 : v 8 ≤ 1 := by rcases bit 8 with h|h <;> omega
  have l9 : 0 ≤ v 9 := by rcases bit 9 with h|h <;> omega
  have u9 : v 9 ≤ 1 := by rcases bit 9 with h|h <;> omega
  have l10 : 0 ≤ v 10 := by rcases bit 10 with h|h <;> omega
  have u10 : v 10 ≤ 1 := by rcases bit 10 with h|h <;> omega
  have l11 : 0 ≤ v 11 := by rcases bit 11 with h|h <;> omega
  have u11 : v 11 ≤ 1 := by rcases bit 11 with h|h <;> omega
  have l12 : 0 ≤ v 12 := by rcases bit 12 with h|h <;> omega
  have u12 : v 12 ≤ 1 := by rcases bit 12 with h|h <;> omega
  have l13 : 0 ≤ v 13 := by rcases bit 13 with h|h <;> omega
  have u13 : v 13 ≤ 1 := by rcases bit 13 with h|h <;> omega
  have l14 : 0 ≤ v 14 := by rcases bit 14 with h|h <;> omega
  have u14 : v 14 ≤ 1 := by rcases bit 14 with h|h <;> omega
  have o15 : v 15 = 1 := fixed 15 (by decide)
  omega

open Finset UnionClosed

lemma indexed_sum {α : Type} [Fintype α] [DecidableEq α] (D : Finset α) (I : List ℕ)
    (d : ℕ → α) (s : α → ℤ) (all : (I.map d).toFinset=univ) (nd : (I.map d).Nodup) :
    ∑ u ∈ D, s u = (I.map (fun i => s (d i) * (if d i ∈ D then (1:ℤ) else 0))).sum := by
  have h : (univ.filter (· ∈ D) : Finset α) = D := by ext; simp
  calc
    _ = ∑ u : α, if u∈D then s u else 0 := by rw [← sum_filter,h]
    _ = ((I.map d).map (fun u => if u∈D then s u else 0)).sum := by
      rw [← List.sum_toFinset _ nd, all]
    _ = _ := by simp [List.map_map,Function.comp_def,mul_ite]

lemma indicator_join {α : Type} [DecidableEq α] (D : Finset (Finset α))
    (closed : IsUnionClosed D) (d : ℕ → Finset α) (du : ∀ i j, d (i|||j)=d i∪d j) (i j : ℕ) :
    (if d i∈D then (1:ℤ) else 0) + (if d j∈D then 1 else 0) - (if d (i|||j)∈D then 1 else 0) ≤ 1 := by
  rw [du]
  by_cases a : d i∈D <;> by_cases b : d j∈D
  · simp [a,b,closed _ a _ b]
  all_goals split_ifs <;> omega

lemma indicator_force {α : Type} [DecidableEq α] (D : Finset (Finset α)) (d : ℕ → Finset α)
    (du : ∀ i j, d (i|||j)=d i∪d j) {t : ℕ} (h : ∀ U∈D, U∪d t∈D) (i : ℕ) :
    (if d i∈D then (1:ℤ) else 0) ≤ (if d (i|||t)∈D then 1 else 0) := by
  rw [du]
  by_cases hi : d i∈D
  · simp [hi,h _ hi]
  · simp [hi]; split <;> decide

lemma decode_union (b i j : ℕ) :
    (univ.filter (fun a : Fin b => (i|||j).testBit a.val)) =
    (univ.filter (fun a : Fin b => i.testBit a.val)) ∪
    (univ.filter (fun a : Fin b => j.testBit a.val)) := by ext; simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
lemma fiber4 (k : ℕ) (hk : k ≤ 8) (D : Finset (Finset (Fin 4)))
    (closed : IsUnionClosed D) (full : univ∈D) (zero : k=0 → ∅∈D)
    (minSize : ∀ U∈D, k+U.card=0 ∨ 4≤k+U.card)
    (avoid : ∀ U∈D, ¬((k=1 ∧ U.card=4) ∨ (k=2 ∧ U.card=2)))
    (apart : ∀ U∈D, ∀ V∈D, U≠V → ¬((k+U.card=4 ∧ k+V.card=4 ∧ k+(U∩V).card=2) ∨ (k+U.card=4 ∧ k+V.card=5 ∧ U ⊆ V))) :
    (if k=0 then -16 else if k=8 then 16 else 0 : ℤ) ≤ ∑ U ∈ D, (5*(U.card:ℤ)+2*k-18) := by
  let d (i : ℕ) : Finset (Fin 4) := univ.filter (fun a => i.testBit a.val)
  let v (i : ℕ) : ℤ := if d i∈D then 1 else 0
  have du := decode_union 4
  have bit (i) : v i=0 ∨ v i=1 := by dsimp [v]; split <;> simp
  have join := indicator_join D closed d du
  have stable : ∀ i, d i=univ ∨ (k=0 ∧ d i=∅) → v i=1 := by
    intro i h
    have hD : d i∈D := by
      rcases h with hi|⟨hk,hi⟩
      · exact hi ▸ full
      · exact hi ▸ zero hk
    simp [v,hD]
  have exclude (i : ℕ) (bad : (0<k+(d i).card ∧ k+(d i).card<4) ∨ ((k=1 ∧ (d i).card=4) ∨ (k=2 ∧ (d i).card=2))) : v i=0 := by
    have hn : d i∉D := by
      intro h
      have size := minSize _ h
      rcases bad with a|b
      · omega
      · exact avoid _ h b
    simp [v,hn]
  have separate (i j : ℕ) (h : d i≠d j ∧ ((k+(d i).card=4 ∧ k+(d j).card=4 ∧ k+((d i)∩(d j)).card=2) ∨ (k+(d i).card=4 ∧ k+(d j).card=5 ∧ d i ⊆ d j))) : v i + v j ≤ 1 := by
    by_cases h1 : d i∈D <;> by_cases h2 : d j∈D
    · exact (apart _ h1 _ h2 h.1 h.2).elim
    all_goals simp [v,h1,h2]
  have all : ((List.range 16).map d).toFinset=univ := by decide +kernel
  have nd : ((List.range 16).map d).Nodup := by decide +kernel
  rw [indexed_sum D _ d _ all nd]
  change _ ≤ ((List.range 16).map (fun i => (5*((d i).card:ℤ)+2*(k:ℤ)-18)*v i)).sum
  interval_cases k
  · have hsm : ∀ i ∈ ([1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List ℕ), (0<0+(d i).card ∧ 0+(d i).card<4) ∨ ((0=1 ∧ (d i).card=4) ∨ (0=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((0+(d u.1).card=4 ∧ 0+(d u.2).card=4 ∧ 0+((d u.1)∩(d u.2)).card=2) ∨ (0+(d u.1).card=4 ∧ 0+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([0,15] : List ℕ), d i=univ ∨ (0=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_0 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (-16 : ℤ) ≤ ((-18 : ℤ)*v 0 + ((-13 : ℤ)*v 1 + ((-13 : ℤ)*v 2 + ((-8 : ℤ)*v 3 + ((-13 : ℤ)*v 4 + ((-8 : ℤ)*v 5 + ((-8 : ℤ)*v 6 + ((-3 : ℤ)*v 7 + ((-13 : ℤ)*v 8 + ((-8 : ℤ)*v 9 + ((-8 : ℤ)*v 10 + ((-3 : ℤ)*v 11 + ((-8 : ℤ)*v 12 + ((-3 : ℤ)*v 13 + ((-3 : ℤ)*v 14 + ((2 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12,15] : List ℕ), (0<1+(d i).card ∧ 1+(d i).card<4) ∨ ((1=1 ∧ (d i).card=4) ∨ (1=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([(7,15),(11,15),(13,15),(14,15)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((1+(d u.1).card=4 ∧ 1+(d u.2).card=4 ∧ 1+((d u.1)∩(d u.2)).card=2) ∨ (1+(d u.1).card=4 ∧ 1+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (1=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_1 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-16 : ℤ)*v 0 + ((-11 : ℤ)*v 1 + ((-11 : ℤ)*v 2 + ((-6 : ℤ)*v 3 + ((-11 : ℤ)*v 4 + ((-6 : ℤ)*v 5 + ((-6 : ℤ)*v 6 + ((-1 : ℤ)*v 7 + ((-11 : ℤ)*v 8 + ((-6 : ℤ)*v 9 + ((-6 : ℤ)*v 10 + ((-1 : ℤ)*v 11 + ((-6 : ℤ)*v 12 + ((-1 : ℤ)*v 13 + ((-1 : ℤ)*v 14 + ((4 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0,1,2,3,4,5,6,8,9,10,12] : List ℕ), (0<2+(d i).card ∧ 2+(d i).card<4) ∨ ((2=1 ∧ (d i).card=4) ∨ (2=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([(3,7),(3,11),(3,12),(5,7),(5,10),(5,13),(6,7),(6,9),(6,14),(9,11),(9,13),(10,11),(10,14),(12,13),(12,14)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((2+(d u.1).card=4 ∧ 2+(d u.2).card=4 ∧ 2+((d u.1)∩(d u.2)).card=2) ∨ (2+(d u.1).card=4 ∧ 2+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (2=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_2 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-14 : ℤ)*v 0 + ((-9 : ℤ)*v 1 + ((-9 : ℤ)*v 2 + ((-4 : ℤ)*v 3 + ((-9 : ℤ)*v 4 + ((-4 : ℤ)*v 5 + ((-4 : ℤ)*v 6 + ((1 : ℤ)*v 7 + ((-9 : ℤ)*v 8 + ((-4 : ℤ)*v 9 + ((-4 : ℤ)*v 10 + ((1 : ℤ)*v 11 + ((-4 : ℤ)*v 12 + ((1 : ℤ)*v 13 + ((1 : ℤ)*v 14 + ((6 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([0] : List ℕ), (0<3+(d i).card ∧ 3+(d i).card<4) ∨ ((3=1 ∧ (d i).card=4) ∨ (3=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([(1,3),(1,5),(1,9),(2,3),(2,6),(2,10),(4,5),(4,6),(4,12),(8,9),(8,10),(8,12)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((3+(d u.1).card=4 ∧ 3+(d u.2).card=4 ∧ 3+((d u.1)∩(d u.2)).card=2) ∨ (3+(d u.1).card=4 ∧ 3+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (3=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_3 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-12 : ℤ)*v 0 + ((-7 : ℤ)*v 1 + ((-7 : ℤ)*v 2 + ((-2 : ℤ)*v 3 + ((-7 : ℤ)*v 4 + ((-2 : ℤ)*v 5 + ((-2 : ℤ)*v 6 + ((3 : ℤ)*v 7 + ((-7 : ℤ)*v 8 + ((-2 : ℤ)*v 9 + ((-2 : ℤ)*v 10 + ((3 : ℤ)*v 11 + ((-2 : ℤ)*v 12 + ((3 : ℤ)*v 13 + ((3 : ℤ)*v 14 + ((8 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([] : List ℕ), (0<4+(d i).card ∧ 4+(d i).card<4) ∨ ((4=1 ∧ (d i).card=4) ∨ (4=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([(0,1),(0,2),(0,4),(0,8)] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((4+(d u.1).card=4 ∧ 4+(d u.2).card=4 ∧ 4+((d u.1)∩(d u.2)).card=2) ∨ (4+(d u.1).card=4 ∧ 4+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (4=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_4 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-10 : ℤ)*v 0 + ((-5 : ℤ)*v 1 + ((-5 : ℤ)*v 2 + ((0 : ℤ)*v 3 + ((-5 : ℤ)*v 4 + ((0 : ℤ)*v 5 + ((0 : ℤ)*v 6 + ((5 : ℤ)*v 7 + ((-5 : ℤ)*v 8 + ((0 : ℤ)*v 9 + ((0 : ℤ)*v 10 + ((5 : ℤ)*v 11 + ((0 : ℤ)*v 12 + ((5 : ℤ)*v 13 + ((5 : ℤ)*v 14 + ((10 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([] : List ℕ), (0<5+(d i).card ∧ 5+(d i).card<4) ∨ ((5=1 ∧ (d i).card=4) ∨ (5=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((5+(d u.1).card=4 ∧ 5+(d u.2).card=4 ∧ 5+((d u.1)∩(d u.2)).card=2) ∨ (5+(d u.1).card=4 ∧ 5+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (5=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_5 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-8 : ℤ)*v 0 + ((-3 : ℤ)*v 1 + ((-3 : ℤ)*v 2 + ((2 : ℤ)*v 3 + ((-3 : ℤ)*v 4 + ((2 : ℤ)*v 5 + ((2 : ℤ)*v 6 + ((7 : ℤ)*v 7 + ((-3 : ℤ)*v 8 + ((2 : ℤ)*v 9 + ((2 : ℤ)*v 10 + ((7 : ℤ)*v 11 + ((2 : ℤ)*v 12 + ((7 : ℤ)*v 13 + ((7 : ℤ)*v 14 + ((12 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([] : List ℕ), (0<6+(d i).card ∧ 6+(d i).card<4) ∨ ((6=1 ∧ (d i).card=4) ∨ (6=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((6+(d u.1).card=4 ∧ 6+(d u.2).card=4 ∧ 6+((d u.1)∩(d u.2)).card=2) ∨ (6+(d u.1).card=4 ∧ 6+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (6=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_6 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-6 : ℤ)*v 0 + ((-1 : ℤ)*v 1 + ((-1 : ℤ)*v 2 + ((4 : ℤ)*v 3 + ((-1 : ℤ)*v 4 + ((4 : ℤ)*v 5 + ((4 : ℤ)*v 6 + ((9 : ℤ)*v 7 + ((-1 : ℤ)*v 8 + ((4 : ℤ)*v 9 + ((4 : ℤ)*v 10 + ((9 : ℤ)*v 11 + ((4 : ℤ)*v 12 + ((9 : ℤ)*v 13 + ((9 : ℤ)*v 14 + ((14 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([] : List ℕ), (0<7+(d i).card ∧ 7+(d i).card<4) ∨ ((7=1 ∧ (d i).card=4) ∨ (7=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((7+(d u.1).card=4 ∧ 7+(d u.2).card=4 ∧ 7+((d u.1)∩(d u.2)).card=2) ∨ (7+(d u.1).card=4 ∧ 7+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (7=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_7 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (0 : ℤ) ≤ ((-4 : ℤ)*v 0 + ((1 : ℤ)*v 1 + ((1 : ℤ)*v 2 + ((6 : ℤ)*v 3 + ((1 : ℤ)*v 4 + ((6 : ℤ)*v 5 + ((6 : ℤ)*v 6 + ((11 : ℤ)*v 7 + ((1 : ℤ)*v 8 + ((6 : ℤ)*v 9 + ((6 : ℤ)*v 10 + ((11 : ℤ)*v 11 + ((6 : ℤ)*v 12 + ((11 : ℤ)*v 13 + ((11 : ℤ)*v 14 + ((16 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]
  · have hsm : ∀ i ∈ ([] : List ℕ), (0<8+(d i).card ∧ 8+(d i).card<4) ∨ ((8=1 ∧ (d i).card=4) ∨ (8=2 ∧ (d i).card=2)) := by decide +kernel
    have hab : ∀ u ∈ ([] : List (ℕ × ℕ)), d u.1 ≠ d u.2 ∧ ((8+(d u.1).card=4 ∧ 8+(d u.2).card=4 ∧ 8+((d u.1)∩(d u.2)).card=2) ∨ (8+(d u.1).card=4 ∧ 8+(d u.2).card=5 ∧ d u.1 ⊆ d u.2)) := by decide +kernel
    have hfx : ∀ i ∈ ([15] : List ℕ), d i=univ ∨ (8=0 ∧ d i=∅) := by decide +kernel
    have cert := layer4_8 v bit join (fun i hi => exclude i (hsm i hi)) (fun i j hij => separate i j (hab (i,j) hij)) (fun i hi => stable i (hfx i hi))
    change (16 : ℤ) ≤ ((-2 : ℤ)*v 0 + ((3 : ℤ)*v 1 + ((3 : ℤ)*v 2 + ((8 : ℤ)*v 3 + ((3 : ℤ)*v 4 + ((8 : ℤ)*v 5 + ((8 : ℤ)*v 6 + ((13 : ℤ)*v 7 + ((3 : ℤ)*v 8 + ((8 : ℤ)*v 9 + ((8 : ℤ)*v 10 + ((13 : ℤ)*v 11 + ((8 : ℤ)*v 12 + ((13 : ℤ)*v 13 + ((13 : ℤ)*v 14 + ((18 : ℤ)*v 15 + 0))))))))))))))))
    linarith only [cert]

end FranklFour

namespace FranklFourGlobal
open Finset UnionClosed

lemma weight_sum {V : Type} [DecidableEq V] (X B : Finset V) (a d : ℕ) :
    (∑ i ∈ X, if i ∈ B then a else d) = a*(X∩B).card + d*(X\B).card := by
  have yes : X.filter (· ∈ B) = X∩B := by ext; simp
  have no : X.filter (· ∉ B) = X\B := by ext; simp
  rw [sum_ite,yes,no]
  simp [mul_comm]

lemma reassemble {V : Type} [Fintype V] [DecidableEq V] (F : Finset (Finset V))
    (B : Finset V) (f : Finset V → ℤ) (offset : ℤ)
    (bound : ∀ K ∈ (univ\B).powerset,
       (if K=univ\B then offset else 0) - (if K=∅ then offset else 0) ≤
       ∑ X ∈ F.filter (fun X => X\B=K), f X) : 0 ≤ ∑ X ∈ F, f X := by
  have h := sum_le_sum bound
  have maps (x : Finset V) (_ : x∈F) : x\B ∈ (univ\B).powerset := by
    apply mem_powerset.mpr
    exact sdiff_subset_sdiff (subset_univ _) (Subset.rfl)
  rw [sum_fiberwise_of_maps_to maps, sum_sub_distrib] at h
  simpa using h

lemma weight_witness (F : Finset (Finset (Fin 12))) (B : Finset (Fin 12)) (a d t : ℕ)
    (pa : 0<a) (pd : 0<d) (total : a*B.card+d*(univ\B).card = 2*t)
    (nonneg : (0:ℤ) ≤ ∑ X ∈ F, (((a*(X∩B).card + d*(X\B).card : ℕ) : ℤ) - (t:ℤ))) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  let w (i : Fin 12) := if i∈B then a else d
  have sum (X : Finset (Fin 12)) : (∑ i ∈ X, w i) = a*(X∩B).card+d*(X\B).card := weight_sum X B a d
  have tot : (∑ i, w i) = 2*t := by simpa using (sum univ).trans (by simpa using total)
  refine ⟨w,Finset.sum_pos (fun i _ => by dsimp [w]; split <;> assumption) univ_nonempty,?_⟩
  rw [tot]
  simp only [← sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at nonneg
  have h : F.card*t ≤ ∑ X ∈ F, ∑ i ∈ X, w i := by exact_mod_cast (sub_nonneg.mp nonneg)
  nlinarith

/-- Encode all sets with the same outside part as a family on the distinguished coordinates. -/
lemma slice_data {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (closed : IsUnionClosed F) (empty : ∅∈F) (fullSet : univ∈F)
    (minSize : ∀ X∈F, X.Nonempty → 4 ≤ X.card)
    (hK : K ⊆ univ \ (univ.map e)) :
    let B := univ.map e
    let X (U : Finset (Fin b)) := K ∪ U.map e
    let D := univ.filter fun U => X U ∈ F
    IsUnionClosed D ∧ (K=∅ → ∅∈D) ∧ (K=univ\B → univ∈D) ∧
    (∀ U∈D, K.card+U.card=0 ∨ 4≤K.card+U.card) ∧
    (∀ H : Finset (Fin b), H.map e∈F → ∀ U∈D, U∪H∈D) ∧
    (∀ U V : Finset (Fin b), (X U∩X V).card=K.card+(U∩V).card) ∧
    (∀ U : Finset (Fin b), (X U).card=K.card+U.card) ∧
    (∀ U : Finset (Fin b), X U∩B=U.map e) ∧ Function.Injective X ∧
    (∀ s : ℕ → ℤ, (∑ Y ∈ F.filter (fun Y => Y\B=K), s (Y∩B).card) = ∑ U ∈ D, s U.card) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  let X (U : Finset (Fin b)) := K ∪ U.map e
  let D := (univ : Finset (Finset (Fin b))).filter fun U => X U ∈ F
  have mem (U) : U∈D ↔ X U∈F := by simp [D]
  have inner (U : Finset (Fin b)) : U.map e ⊆ B := map_subset_map.mpr (subset_univ _)
  have dis : Disjoint K B := by
    apply disjoint_left.mpr
    intro i hi hb; exact (mem_sdiff.mp (hK hi)).2 hb
  have ins (U) : X U∩B=U.map e := by
    ext i; simp only [X,mem_inter,mem_union]; constructor
    · rintro ⟨h|h,hb⟩
      · exact (disjoint_left.mp dis h hb).elim
      · exact h
    · exact fun h => ⟨Or.inr h,inner U h⟩
  have out (U) : X U\B=K := by
    ext i; simp only [X,mem_sdiff,mem_union]; constructor
    · rintro ⟨h|h,hb⟩
      · exact h
      · exact (hb (inner U h)).elim
    · exact fun h => ⟨Or.inl h,disjoint_left.mp dis h⟩
  have cardX (U) : (X U).card=K.card+U.card := by
    change (K ∪ U.map e).card = _
    rw [card_union_of_disjoint (dis.mono_right (inner U)),card_map]
  have inject : Function.Injective X := by
    intro U V eq
    exact Finset.map_injective e <| (ins U).symm.trans ((congrArg (· ∩ B) eq).trans (ins V))
  change IsUnionClosed D ∧ _
  refine ⟨?_,?_,?_,?_,?_,?_,cardX,ins,inject,?_⟩
  · intro U hu V hv
    apply (mem _).mpr
    have := closed (X U) ((mem U).mp hu) (X V) ((mem V).mp hv)
    simpa [X,map_union,union_assoc,union_left_comm,union_comm] using this
  · intro z; apply (mem _).mpr; simpa [X,z] using empty
  · intro z; apply (mem _).mpr
    have eq : X univ=univ := by ext i; simp [X,z]
    rwa [eq]
  · intro U hu
    by_cases h : (X U).Nonempty
    · exact Or.inr ((cardX U) ▸ minSize _ ((mem _).mp hu) h)
    · have z : X U = ∅ := not_nonempty_iff_eq_empty.mp h
      exact Or.inl (by simpa [z] using (cardX U).symm)
  · intro H hH U hu
    apply (mem _).mpr
    have := closed _ ((mem _).mp hu) _ hH
    simpa [X,map_union,union_assoc] using this
  · intro U V
    have eq : X U∩X V=X (U∩V) := by ext i; simp [X,map_inter]; tauto
    rw [eq,cardX]
  · intro score
    have eq : D.image X = F.filter (fun Y => Y\B=K) := by
      ext Y
      constructor
      · rintro hy
        obtain ⟨U,hu,rfl⟩ := mem_image.mp hy
        exact mem_filter.mpr ⟨(mem _).mp hu,out U⟩
      · intro hy
        obtain ⟨hf,base⟩ := mem_filter.mp hy
        let U := univ.filter (fun i : Fin b => e i∈Y)
        have val : X U=Y := by
          ext a
          simp only [X,mem_union]
          by_cases h : a∈B
          · obtain ⟨i,_,rfl⟩ := mem_map.mp h
            have nk : e i ∉ K := fun hm => disjoint_left.mp dis hm (inner univ (mem_map.mpr ⟨i,mem_univ _,rfl⟩))
            simp [U,nk]
          · have : a∈K ↔ a∈Y := by rw [←base]; simp [h]
            have hn : a∉U.map e := fun hu => h (inner U hu)
            simp [hn,this]
        exact mem_image.mpr ⟨U,(mem _).mpr (val ▸ hf),val⟩
    rw [←eq,sum_image (fun _ _ _ _ eq => inject eq)]
    apply sum_congr rfl
    intro U hu; rw [ins,card_map]
lemma coordinates {V : Type} [DecidableEq V] (B : Finset V) {b : ℕ} (size : B.card=b) :
    ∃ e : Fin b ↪ V, univ.map e=B := by
  classical
  let h : Fin b ≃ B := Fintype.equivOfCardEq (by simpa using size.symm)
  let e := h.toEmbedding.trans (Function.Embedding.subtype (· ∈ B))
  refine ⟨e,?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := mem_map.mp hv
    exact (h i).2
  · intro hv
    exact mem_map.mpr ⟨h.symm ⟨v,hv⟩,mem_univ _,congrArg Subtype.val (h.apply_symm_apply _)⟩

lemma weight_from_fibers {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12)
    (closed : IsUnionClosed F) (empty : ∅∈F) (full : univ∈F)
    (minSize : ∀ X∈F, X.Nonempty → 4 ≤ X.card)
    (a d t : ℕ) (pa : 0<a) (pd : 0<d) (balance : a*b+d*(12-b)=2*t)
    (c : ℤ) (pc : 0≤c)
    (bound : ∀ K ⊆ univ\(univ.map e),
      let D := (univ : Finset (Finset (Fin b))).filter fun U => K∪U.map e∈F
      D.Nonempty → (if K=univ\(univ.map e) then c else 0) - (if K=∅ then c else 0) ≤
        ∑ U ∈ D, ((a:ℤ)*U.card+(d:ℤ)*K.card-(t:ℤ))) :
    ∃ w : Fin 12 → ℕ, 0<∑ i, w i ∧ F.card*(∑ i,w i) ≤ 2*(∑ X∈F,∑ i∈X,w i) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  have bsize : B.card=b := by simp [B]
  have osize : (univ\B).card=12-b := by rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,bsize]
  apply weight_witness F B a d t pa pd (by simpa only [bsize,osize] using balance)
  apply reassemble F B _ c
  intro K hK
  have sub := mem_powerset.mp hK
  let D := (univ : Finset (Finset (Fin b))).filter fun U => K ∪ U.map e ∈ F
  obtain ⟨_,_,top,_,_,_,_,_,_,sums⟩ := slice_data F e K closed empty full minSize sub
  have eq : (∑ X∈F.filter (fun X => X\B=K), (((a*(X∩B).card+d*(X\B).card:ℕ):ℤ)-(t:ℤ))) =
    ∑ U∈D, ((a:ℤ)*U.card+(d:ℤ)*K.card-(t:ℤ)) := by
    calc
      _ = ∑ X∈F.filter (fun X => X\B=K), ((a:ℤ)*(X∩B).card+(d:ℤ)*K.card-(t:ℤ)) := by
        apply sum_congr rfl
        intro X hx
        have z := (mem_filter.mp hx).2
        push_cast; rw [z]
      _ = _ := sums (fun j => (a:ℤ)*j+(d:ℤ)*K.card-(t:ℤ))
  rw [eq]
  by_cases nonempty : D.Nonempty
  · exact bound K sub nonempty
  · have ne : K≠univ\B := fun same => nonempty ⟨univ,top same⟩
    have z := not_nonempty_iff_eq_empty.mp nonempty
    rw [z,sum_empty,if_neg ne]; split <;> omega

lemma nonempty_full {b : ℕ} (D : Finset (Finset (Fin b))) (nonempty : D.Nonempty)
    (stable : ∀ U∈D, U∪univ∈D) : univ∈D := by
  obtain ⟨U,hu⟩ := nonempty
  simpa only [union_eq_right.mpr (subset_univ U)] using stable U hu


lemma four_isolated (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅∈F) (full : univ∈F) (minSize : ∀ X∈F, X.Nonempty → 4≤X.card)
    (S : Finset (Fin 12)) (hS : S∈F) (s : S.card=4)
    (no30 : ∀ U∈F, ∀ V∈F, U.card=4 → V.card=5 → ¬ U ⊆ V)
    (no31 : ∀ U∈F, ∀ V∈F, U.card=4 → V.card=4 → (U∩V).card≠2) :
    ∃ w : Fin 12 → ℕ, 0<∑ i,w i ∧ F.card*(∑ i,w i) ≤ 2*(∑ X∈F,∑ i∈X,w i) := by
  classical
  obtain ⟨e,eqS⟩ := coordinates S s
  apply weight_from_fibers F e closed empty full minSize 5 2 18 (by decide) (by decide) (by decide) 16 (by decide)
  intro K sub
  let B := (univ : Finset (Fin 4)).map e
  let X (U : Finset (Fin 4)) := K∪U.map e
  let D := (univ : Finset (Finset (Fin 4))).filter (fun U => X U∈F)
  change D.Nonempty → _
  intro nonempty
  obtain ⟨uc,zero,_,small,fix,inter,size,inside,_,_⟩ := slice_data F e K closed empty full minSize sub
  have mem (U) : U∈D ↔ X U∈F := by simp [D]
  have top : univ∈D := nonempty_full D nonempty (fix univ (eqS ▸ hS))
  have cap : (univ\B).card=8 := by rw [card_sdiff_of_subset (subset_univ _)]; simp [B]
  have hk : K.card≤8 := (card_le_card sub).trans_eq cap
  have lo : K=∅ ↔ K.card=0 := card_eq_zero.symm
  have hi : K=univ\B ↔ K.card=8 := ⟨fun h => h ▸ cap,fun h => eq_of_subset_of_card_le sub (by omega)⟩
  have avoid (U) (hu : U∈D) : ¬((K.card=1 ∧ U.card=4) ∨ (K.card=2 ∧ U.card=2)) := by
    rintro (⟨one,four⟩|⟨two,pair⟩)
    · have sz : (X U).card=5 := by rw [size,one,four]
      have cross : (X U∩S).card=4 := by rw [←eqS,inside,card_map,four]
      have eq : X U∩S = S := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact no30 S hS _ ((mem _).mp hu) s sz (inter_eq_right.mp eq)
    · have sz : (X U).card=4 := by rw [size,two,pair]
      have cross : (X U∩S).card=2 := by rw [←eqS,inside,card_map,pair]
      exact no31 _ ((mem _).mp hu) S hS sz s cross
  have apart (U) (hu : U∈D) (V) (hv : V∈D) (_ : U≠V) :
      ¬((K.card+U.card=4 ∧ K.card+V.card=4 ∧ K.card+(U∩V).card=2) ∨ (K.card+U.card=4 ∧ K.card+V.card=5 ∧ U ⊆ V)) := by
    rintro (⟨u4,v4,bad⟩|⟨u4,v5,uv⟩)
    · exact no31 _ ((mem _).mp hu) _ ((mem _).mp hv) ((size U).trans u4) ((size V).trans v4) ((inter U V).trans bad)
    · exact no30 _ ((mem _).mp hu) _ ((mem _).mp hv) ((size U).trans u4) ((size V).trans v5)
        (union_subset_union_right (map_subset_map.mpr uv))
  have res := FranklFour.fiber4 K.card hk D uc top (fun h => zero (lo.mpr h)) small avoid apart
  change (if K=univ\B then (16:ℤ) else 0) - (if K=∅ then 16 else 0) ≤ _
  have offset : (if K=univ\B then (16:ℤ) else 0) - (if K=∅ then 16 else 0) =
      (if K.card=0 then -16 else if K.card=8 then 16 else 0) := by
    simp only [hi,lo]; split_ifs <;> omega
  rw [offset]
  exact res

end FranklFourGlobal

theorem OMA.solution : OMA.R_UnionClosed_union_closed_variants_univ_card_R1_H2_R1.H4 := by
  intro F closed empty full low four p30 p31
  obtain ⟨S,hS,s⟩ := four
  exact FranklFourGlobal.four_isolated F closed empty full low S hS s
    (fun A ha B hb a b sub => p30 ⟨A,ha,B,hb,a,b,sub⟩)
    (fun A ha B hb a b c => p31 ⟨A,ha,B,hb,a,b,c⟩)
