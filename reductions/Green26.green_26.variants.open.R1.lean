import FormalConjectures.GreensOpenProblems.«26»

-- Reduction Green26.green_26.variants.open.R1 of the additive basis conjecture over F_p
-- Source: N. Alon, N. Linial, R. Meshulam, Additive bases of vector spaces over prime fields,
-- J. Combin. Theory Ser. A 57 (1991), 203-210, Section 3.
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The additive basis conjecture from the permanent conjecture of Alon, Linial and Meshulam

The target asks, for every prime `p`, for a constant `C` such that any `C` cubes in `𝔽 p n`
sum to the whole space. The route is the one of Alon, Linial and Meshulam [ALM91, Section 3]:

* `H1` (Yu 2025): four cubes suffice in `𝔽₃ n`. This is the statement of
  `Green26.green_26.variants.yu25`, which is known.
* `H2` (the permanent conjecture of [ALM91], for `p ≥ 5`): among the columns of `C` invertible
  `n × n` matrices over `ZMod p` one can choose `(p - 1) n` distinct columns such that `p - 1`
  stacked copies of the chosen `n × (p - 1) n` matrix have a nonzero permanent. This is the open
  core.
* `H3` (the permanent lemma of Alon): if a square matrix `M` over a field has a nonzero permanent,
  then for every vector `b` there is a `0`-`1` vector `x` such that `M x` differs from `b` in
  every coordinate. It follows from the Combinatorial Nullstellensatz.

`main` treats `p = 2` directly (a cube is the whole space) and `p = 3` with `H1`. For `p ≥ 5` it
applies `H3` to the stacked matrix of `H2`. Row `(k, r)` forbids the value `v r + (k + 1)`, so
the `p - 1` copies of row `r` forbid every value except `v r`. The `0`-`1` vector then writes `v`
as a sum of one point from each cube.
-/

namespace OMA.R_Green26_green_26_variants_open_R1

open scoped Pointwise

/-- Yu 2025: any four cubes in `𝔽₃ n` sum to the whole space. -/
def H1 : Prop :=
  ∀ n : ℕ, ∀ A : Fin 4 → Set (𝔽₃ n), (∀ i, Green26.IsCube (A i)) → ∑ i, A i = Set.univ

/-- The permanent conjecture of Alon, Linial and Meshulam for primes `p ≥ 5`. The embedding `σ`
chooses `(p - 1) n` distinct columns of the block matrix `[B 0, …, B (C - 1)]`, and the matrix
below consists of `p - 1` stacked copies of the chosen columns. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∃ C : ℕ, ∀ n : ℕ,
    ∀ B : Fin C → Matrix (Fin n) (Fin n) (ZMod p), (∀ i, IsUnit (B i).det) →
      ∃ σ : Fin (p - 1) × Fin n ↪ Fin C × Fin n,
        (Matrix.of fun r c : Fin (p - 1) × Fin n => B (σ c).1 r.2 (σ c).2).permanent ≠ 0

/-- The permanent lemma of Alon: a square matrix with nonzero permanent over a field misses any
prescribed vector in every coordinate at some `0`-`1` vector. -/
def H3 : Prop :=
  ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F),
    M.permanent ≠ 0 → ∀ b : ι → F,
      ∃ x : ι → F, (∀ j, x j = 0 ∨ x j = 1) ∧ ∀ i, M.mulVec x i ≠ b i

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod_two_cases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide

/-- Over `ZMod 2` the standard cube is the whole space. -/
lemma standardCube_two [Fact (Nat.Prime 2)] (n : ℕ) :
    Green26.StandardCube (p := 2) n = Set.univ :=
  Set.eq_univ_of_forall fun x i => zmod_two_cases (x i)

/-- The case `p ≥ 5` of the target, from `H2` and `H3`. -/
lemma large_prime (h2 : H2) (h3 : H3) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∃ C, ∀ n, ∀ A : Fin C → Set (𝔽 p n), (∀ i, Green26.IsCube (A i)) → ∑ i, A i = Set.univ := by
  classical
  have hprime : p.Prime := hp.out
  have : NeZero p := ⟨hprime.ne_zero⟩
  obtain ⟨C, hC⟩ := h2 p hprime h5
  refine ⟨C, fun n A hA => ?_⟩
  choose φ hφ using hA
  let B : Fin C → Matrix (Fin n) (Fin n) (ZMod p) :=
    fun i => LinearMap.toMatrix' (φ i : 𝔽 p n →ₗ[ZMod p] 𝔽 p n)
  have hB : ∀ i, IsUnit (B i).det := by
    intro i
    apply Matrix.isUnit_det_of_right_inverse
      (B := LinearMap.toMatrix' ((φ i).symm : 𝔽 p n →ₗ[ZMod p] 𝔽 p n))
    rw [← LinearMap.toMatrix'_comp]
    simp
  obtain ⟨σ, hσ⟩ := hC n B hB
  refine Set.eq_univ_of_forall fun v => ?_
  rw [Set.mem_fintype_sum]
  obtain ⟨x, hx01, hx⟩ := h3 (ZMod p) (Fin (p - 1) × Fin n) _ hσ
    (fun kr => v kr.2 + ((kr.1.val + 1 : ℕ) : ZMod p))
  -- the `p - 1` copies of row `r` force coordinate `r` to equal `v r`
  have hy : ∀ r, ∑ c, B (σ c).1 r (σ c).2 * x c = v r := by
    intro r
    by_contra hne
    have hd0 : ∑ c, B (σ c).1 r (σ c).2 * x c - v r ≠ 0 := sub_ne_zero.mpr hne
    have hval : 0 < (∑ c, B (σ c).1 r (σ c).2 * x c - v r).val := (ZMod.val_pos).mpr hd0
    have hlt : (∑ c, B (σ c).1 r (σ c).2 * x c - v r).val < p := ZMod.val_lt _
    have hk : (∑ c, B (σ c).1 r (σ c).2 * x c - v r).val - 1 < p - 1 := by omega
    apply hx (⟨(∑ c, B (σ c).1 r (σ c).2 * x c - v r).val - 1, hk⟩, r)
    show ∑ c, B (σ c).1 r (σ c).2 * x c
      = v r + (((∑ c, B (σ c).1 r (σ c).2 * x c - v r).val - 1 + 1 : ℕ) : ZMod p)
    rw [Nat.sub_add_cancel hval, ZMod.natCast_zmod_val]
    ring
  -- spread the chosen columns over the `C` cubes
  let w : Fin C × Fin n → ZMod p := fun q => ∑ c, if σ c = q then x c else 0
  have hw01 : ∀ q, w q = 0 ∨ w q = 1 := by
    intro q
    by_cases hq : ∃ c₀, σ c₀ = q
    · obtain ⟨c₀, rfl⟩ := hq
      have hwc : w (σ c₀) = x c₀ := by
        simp only [w, σ.injective.eq_iff]
        simp
      rw [hwc]
      exact hx01 c₀
    · left
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg (fun h => hq ⟨c, h⟩)]
  refine ⟨fun i => φ i (fun j => w (i, j)), fun i => ?_, ?_⟩
  · rw [hφ i]
    exact ⟨fun j => w (i, j), fun j => hw01 (i, j), rfl⟩
  · funext r
    rw [← hy r, Finset.sum_apply]
    have key : ∀ i, φ i (fun j => w (i, j)) r = ∑ j, B i r j * w (i, j) := by
      intro i
      exact (congrFun (LinearMap.toMatrix'_mulVec (φ i : 𝔽 p n →ₗ[ZMod p] 𝔽 p n)
        (fun j => w (i, j))) r).symm
    simp_rw [key]
    rw [← Fintype.sum_prod_type']
    simp only [w, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp

theorem main : H1 → H2 → H3 → type_of% @Green26.green_26.variants.open := by
  intro h1 h2 h3 p hp
  have hprime : p.Prime := hp.out
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, fun n A hA => ?_⟩
    obtain ⟨φ, hφ⟩ := hA 0
    rw [Fin.sum_univ_one, hφ, standardCube_two, Set.image_univ]
    exact Set.range_eq_univ.mpr φ.surjective
  by_cases hp3 : p = 3
  · subst hp3
    exact ⟨4, h1⟩
  have h5 : 5 ≤ p := by
    have h2le := hprime.two_le
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hprime (by decide)
  exact large_prime h2 h3 p h5

end OMA.R_Green26_green_26_variants_open_R1
