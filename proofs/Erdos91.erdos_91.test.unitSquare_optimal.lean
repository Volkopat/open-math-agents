import FormalConjectures.ErdosProblems.«91»

-- Problem: Erdős Problem 91 — unitSquare optimal
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/91.lean:120 (declaration Erdos91.erdos_91.test.unitSquare_optimal)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# The unit square is an optimal four-point configuration

The unit square has four points and its distances are `1` and `√2`, so it determines at most two
distinct distances. Conversely, four points of the plane never determine a single distance: if all
six distances were equal, the three difference vectors from one of the points would have a
nonsingular Gram matrix, which is impossible for three vectors in dimension two. Hence the minimum
number of distinct distances over four-point sets is two, and the unit square attains it.
-/

open EuclideanGeometry

namespace OMA.UnitSquare

/-- Three vectors `u`, `v`, `w` of the plane have a singular Gram matrix. So they cannot all have
squared norm `D` and pairwise inner products `D / 2` unless `D = 0`. -/
lemma gram_aux (u1 u2 v1 v2 w1 w2 D : ℝ)
    (huu : u1 ^ 2 + u2 ^ 2 = D) (hvv : v1 ^ 2 + v2 ^ 2 = D) (hww : w1 ^ 2 + w2 ^ 2 = D)
    (huv : u1 * v1 + u2 * v2 = D / 2) (huw : u1 * w1 + u2 * w2 = D / 2)
    (hvw : v1 * w1 + v2 * w2 = D / 2) : D = 0 := by
  -- The determinant of the Gram matrix of `u`, `v`, `w` vanishes identically.
  have key : (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) * (w1 ^ 2 + w2 ^ 2)
      + 2 * (u1 * v1 + u2 * v2) * (u1 * w1 + u2 * w2) * (v1 * w1 + v2 * w2)
      - (u1 ^ 2 + u2 ^ 2) * (v1 * w1 + v2 * w2) ^ 2
      - (v1 ^ 2 + v2 ^ 2) * (u1 * w1 + u2 * w2) ^ 2
      - (w1 ^ 2 + w2 ^ 2) * (u1 * v1 + u2 * v2) ^ 2 = 0 := by ring
  -- With the prescribed entries that determinant is `D ^ 3 / 2`.
  rw [huu, hvv, hww, huv, huw, hvw] at key
  have h3 : D ^ 3 = 0 := by linear_combination 2 * key
  exact (pow_eq_zero_iff (by norm_num)).mp h3

/-- The squared distance between two points of the plane, in coordinates. -/
lemma dist_sq (p q : ℝ²) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Four points of the plane determine at least two distinct distances. -/
lemma two_le_distinctDistances (S : Finset ℝ²) (hS : S.card = 4) :
    2 ≤ distinctDistances S := by
  by_contra! h
  have hc : (distanceSet S).card ≤ 1 := Nat.le_of_lt_succ h
  let e : Fin 4 ≃ S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  let p (i : Fin 4) : ℝ² := (e i).1
  have hi : Function.Injective p := Subtype.val_injective.comp e.injective
  let D := dist (p 0) (p 1)^2
  have hd (i j : Fin 4) (hne : i ≠ j) : dist (p i) (p j) ∈ distanceSet S :=
    Finset.mem_image.mpr ⟨(p i, p j), Finset.mem_offDiag.mpr ⟨(e i).2, (e j).2, hi.ne hne⟩, rfl⟩
  have he (i j : Fin 4) (hne : i ≠ j) : (p i 0 - p j 0)^2 + (p i 1 - p j 1)^2 = D := by
    rw [← dist_sq]
    exact congrArg (·^2) (Finset.card_le_one.mp hc _ (hd i j hne) _ (hd 0 1 (by decide)))
  have e01 := he 0 1 (by decide)
  have e02 := he 0 2 (by decide)
  have e03 := he 0 3 (by decide)
  have e12 := he 1 2 (by decide)
  have e13 := he 1 3 (by decide)
  have e23 := he 2 3 (by decide)
  exact pow_ne_zero 2 (dist_ne_zero.mpr (hi.ne (by decide : (0 : Fin 4) ≠ 1))) <|
    gram_aux (p 1 0 - p 0 0) (p 1 1 - p 0 1) (p 2 0 - p 0 0) (p 2 1 - p 0 1)
      (p 3 0 - p 0 0) (p 3 1 - p 0 1) D
      (by linear_combination e01) (by linear_combination e02) (by linear_combination e03)
      (by linear_combination (e01 + e02 - e12) / 2)
      (by linear_combination (e01 + e03 - e13) / 2)
      (by linear_combination (e02 + e03 - e23) / 2)

/-- The unit square has four points. -/
lemma card_unitSquare : Erdos91.unitSquare.card = 4 := by
  simp [Erdos91.unitSquare]

/-- Every distance determined by the unit square is `1` or `√2`. -/
lemma distanceSet_unitSquare_subset :
    distanceSet Erdos91.unitSquare ⊆ ({1, Real.sqrt 2} : Finset ℝ) := by
  intro r hr
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hr
  simp only [Erdos91.unitSquare, Finset.mem_offDiag, Finset.mem_insert,
    Finset.mem_singleton] at hpq
  obtain ⟨hp, hq, hne⟩ := hpq
  rw [← Real.sqrt_sq (dist_nonneg : 0 ≤ dist p q), dist_sq]
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | norm_num

end OMA.UnitSquare

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.unitSquare_optimal := by
  have hc : Erdos91.unitSquare.card = 4 := OMA.UnitSquare.card_unitSquare
  have hle : distinctDistances Erdos91.unitSquare ≤ 2 :=
    (Finset.card_le_card OMA.UnitSquare.distanceSet_unitSquare_subset).trans Finset.card_le_two
  have h2 : distinctDistances Erdos91.unitSquare = 2 :=
    le_antisymm hle (OMA.UnitSquare.two_le_distinctDistances _ hc)
  refine ⟨hc, ?_⟩
  rw [h2]
  unfold minimalDistinctDistances
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, Erdos91.unitSquare, hc, rfl⟩
    · rintro m ⟨S, hS, rfl⟩
      exact OMA.UnitSquare.two_le_distinctDistances S hS
  · exact Nat.sInf_le ⟨Erdos91.unitSquare, hc, h2⟩
