import OMAStatements.S_oeis_a334386
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proof of OEIS A334386: `(triangles n).card ≡ 4 * (n - 1) [MOD 12]`

We establish the congruence for all `n > 0` by combining two symmetry actions on `triangles n`:

1. **Mod 3 via a 3-cycle**: Rotating the first three coordinates fixes no vertex of any
   equilateral triangle (its fixed points are collinear in the affine slice), so every fixed
   triangle is a single 3-orbit lying on the fourth face `x 3 = 0` and meeting the other three
   faces. These fixed triangles are in bijection with `Fin (n - 1)`, yielding
   `(triangles n).card ≡ n - 1 [MOD 3]`.
2. **Mod 4 via the Klein four-group**: Each double transposition in `V_4` acts without fixed
   points on `triangles n`: any fixed triangle would have one fixed vertex and two swapped
   vertices, leading to `2 * S^2 = 3 * (D^2 + E^2)` in `ℤ`, which has only the trivial solution
   by 3-adic descent. Partitioning into orbits of size 4 gives `4 ∣ (triangles n).card`.
3. **Chinese Remainder Theorem**: Combining `(triangles n).card ≡ n - 1 [MOD 3]` and
   `4 ∣ (triangles n).card` yields `(triangles n).card ≡ 4 * (n - 1) [MOD 12]`.
-/

namespace OMA.A334386

open Finset OMA.S_oeis_a334386

/-! ### Coordinate permutation action on grid points and triangles -/

def actPt {n : ℕ} (σ : Equiv.Perm (Fin 4)) (x : Point n) : Point n :=
  fun i => x (σ.symm i)

lemma actPt_one {n : ℕ} (x : Point n) : actPt (1 : Equiv.Perm (Fin 4)) x = x := rfl

lemma actPt_mul {n : ℕ} (σ τ : Equiv.Perm (Fin 4)) (x : Point n) :
    actPt (σ * τ) x = actPt σ (actPt τ x) := by
  ext i
  change (x ((τ.trans σ).symm i)).val = (x (τ.symm (σ.symm i))).val
  rfl

lemma actPt_injective {n : ℕ} (σ : Equiv.Perm (Fin 4)) :
    Function.Injective (actPt (n := n) σ) := by
  intro x y h
  have h' := congrArg (actPt σ⁻¹) h
  simpa [← actPt_mul, actPt_one] using h'

lemma actPt_mem_grid {n : ℕ} (σ : Equiv.Perm (Fin 4)) {x : Point n} (hx : x ∈ grid n) :
    actPt σ x ∈ grid n := by
  simp only [grid, mem_filter, mem_univ, true_and] at hx ⊢
  simpa [actPt] using (Equiv.sum_comp σ.symm (fun i => (x i).val)).trans hx

lemma squaredDist_comm {n : ℕ} (x y : Point n) : squaredDist x y = squaredDist y x := by
  simp only [squaredDist, Nat.dist_comm]

lemma squaredDist_actPt {n : ℕ} (σ : Equiv.Perm (Fin 4)) (x y : Point n) :
    squaredDist (actPt σ x) (actPt σ y) = squaredDist x y := by
  simpa [squaredDist, actPt] using
    Equiv.sum_comp σ.symm (fun i => (Nat.dist (x i).val (y i).val) ^ 2)

def actTri {n : ℕ} (σ : Equiv.Perm (Fin 4)) (t : Finset (Point n)) : Finset (Point n) :=
  t.image (actPt σ)

lemma actTri_one {n : ℕ} (t : Finset (Point n)) : actTri (1 : Equiv.Perm (Fin 4)) t = t := by
  ext x
  simp [actTri, actPt_one]

lemma actTri_mul {n : ℕ} (σ τ : Equiv.Perm (Fin 4)) (t : Finset (Point n)) :
    actTri (σ * τ) t = actTri σ (actTri τ t) := by
  ext y
  simp only [actTri, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨actPt τ x, ⟨x, hx, rfl⟩, (actPt_mul σ τ x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, actPt_mul σ τ x⟩

lemma actTri_mem_triangles {n : ℕ} (σ : Equiv.Perm (Fin 4)) {t : Finset (Point n)}
    (ht : t ∈ triangles n) : actTri σ t ∈ triangles n := by
  simp only [triangles, mem_filter, mem_powersetCard] at ht ⊢
  rcases ht with ⟨⟨hsub, hcard⟩, hfaces, heq⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    rcases mem_image.mp hy with ⟨x, hx, rfl⟩
    exact actPt_mem_grid σ (hsub hx)
  · rw [actTri, card_image_of_injective _ (actPt_injective σ), hcard]
  · intro i
    rcases hfaces (σ.symm i) with ⟨x, hx, hx0⟩
    exact ⟨actPt σ x, mem_image_of_mem _ hx, hx0⟩
  · intro y₁ hy₁ y₂ hy₂ y₃ hy₃ h12 h23 h31
    rcases mem_image.mp hy₁ with ⟨x₁, hx₁, rfl⟩
    rcases mem_image.mp hy₂ with ⟨x₂, hx₂, rfl⟩
    rcases mem_image.mp hy₃ with ⟨x₃, hx₃, rfl⟩
    rw [squaredDist_actPt, squaredDist_actPt]
    exact heq x₁ hx₁ x₂ hx₂ x₃ hx₃
      (fun h => h12 (congrArg _ h))
      (fun h => h23 (congrArg _ h))
      (fun h => h31 (congrArg _ h))

/-! ### Orbit-counting lemmas for order-3 and Klein-4 actions -/

lemma card_mod_three_of_order_three {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α)
    (hmap : ∀ x ∈ S, f x ∈ S)
    (hord : ∀ x ∈ S, f (f (f x)) = x) :
    S.card ≡ (S.filter (fun x => f x = x)).card [MOD 3] := by
  classical
  let U := S.filter (fun x => f x ≠ x)
  have hpart : S.card = (S.filter (fun x => f x = x)).card + U.card := by
    simpa [U] using (Finset.card_filter_add_card_filter_not (s := S) (p := fun x => f x = x)).symm
  have hUmap : ∀ x ∈ U, f x ∈ U := by
    intro x hx
    rcases mem_filter.mp hx with ⟨hxS, hne⟩
    refine mem_filter.mpr ⟨hmap x hxS, ?_⟩
    intro hff
    have h1 := congrArg f hff
    rw [hord x hxS] at h1
    exact hne (h1.trans hff).symm
  let orb : α → Finset α := fun x => {x, f x, f (f x)}
  have horb_ne : ∀ x ∈ U, x ≠ f x ∧ f x ≠ f (f x) ∧ f (f x) ≠ x := by
    intro x hx
    rcases mem_filter.mp hx with ⟨hxS, hne⟩
    have h1 : x ≠ f x := Ne.symm hne
    have h2 : f x ≠ f (f x) := by
      intro h
      have h3 := congrArg f h
      rw [hord x hxS] at h3
      exact hne (h.trans h3)
    have h3 : f (f x) ≠ x := by
      intro h
      have h4 := congrArg f h
      rw [hord x hxS] at h4
      exact h1 h4
    exact ⟨h1, h2, h3⟩
  have horb_card : ∀ x ∈ U, (orb x).card = 3 := by
    intro x hx
    rcases horb_ne x hx with ⟨h1, h2, h3⟩
    simp [orb, h1, h2, h3.symm]
  have horb_eq : ∀ x ∈ U, ∀ y ∈ orb x, orb y = orb x := by
    intro x hx y hy
    have hxS : x ∈ S := (mem_filter.mp hx).1
    have h3 : f (f (f x)) = x := hord x hxS
    simp only [orb, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · rfl
    · ext z; simp only [orb, mem_insert, mem_singleton, h3]; tauto
    · ext z
      simp only [orb, mem_insert, mem_singleton, h3]; tauto
  have hU_eq : U = (U.image orb).biUnion id := by
    ext x
    simp only [mem_biUnion, mem_image, id_eq]
    constructor
    · intro hx
      exact ⟨orb x, ⟨x, hx, rfl⟩, by simp [orb]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hx⟩
      simp only [orb, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · exact hUmap y hy
      · exact hUmap (f y) (hUmap y hy)
  have hdisj : ((U.image orb) : Set (Finset α)).PairwiseDisjoint id := by
    intro A hA B hB hne
    rcases mem_image.mp hA with ⟨x, hx, rfl⟩
    rcases mem_image.mp hB with ⟨y, hy, rfl⟩
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro z hzx hzy
    exact hne ((horb_eq x hx z hzx).symm.trans (horb_eq y hy z hzy))
  have hcardU : U.card = (U.image orb).card * 3 := by
    conv_lhs => rw [hU_eq]
    rw [card_biUnion hdisj]
    have hsum : ∑ O ∈ U.image orb, (id O).card = ∑ _O ∈ U.image orb, 3 := by
      refine Finset.sum_congr rfl fun O hO => ?_
      rcases mem_image.mp hO with ⟨x, hx, rfl⟩
      exact horb_card x hx
    rw [hsum, sum_const, smul_eq_mul]
  rw [Nat.ModEq, hpart, hcardU]
  omega

lemma four_dvd_card_of_klein {α : Type*} [DecidableEq α]
    (S : Finset α) (f₁ f₂ f₃ : α → α)
    (hm1 : ∀ x ∈ S, f₁ x ∈ S) (hm2 : ∀ x ∈ S, f₂ x ∈ S) (hm3 : ∀ x ∈ S, f₃ x ∈ S)
    (hi1 : ∀ x ∈ S, f₁ (f₁ x) = x) (hi2 : ∀ x ∈ S, f₂ (f₂ x) = x) (hi3 : ∀ x ∈ S, f₃ (f₃ x) = x)
    (hn1 : ∀ x ∈ S, f₁ x ≠ x) (hn2 : ∀ x ∈ S, f₂ x ≠ x) (hn3 : ∀ x ∈ S, f₃ x ≠ x)
    (h12 : ∀ x ∈ S, f₁ (f₂ x) = f₃ x) (h21 : ∀ x ∈ S, f₂ (f₁ x) = f₃ x)
    (h13 : ∀ x ∈ S, f₁ (f₃ x) = f₂ x) (h31 : ∀ x ∈ S, f₃ (f₁ x) = f₂ x)
    (h23 : ∀ x ∈ S, f₂ (f₃ x) = f₁ x) (h32 : ∀ x ∈ S, f₃ (f₂ x) = f₁ x) :
    4 ∣ S.card := by
  classical
  let orb : α → Finset α := fun x => {x, f₁ x, f₂ x, f₃ x}
  have horb_card : ∀ x ∈ S, (orb x).card = 4 := by
    intro x hx
    have h01 : x ≠ f₁ x := Ne.symm (hn1 x hx)
    have h02 : x ≠ f₂ x := Ne.symm (hn2 x hx)
    have h03 : x ≠ f₃ x := Ne.symm (hn3 x hx)
    have h12' : f₁ x ≠ f₂ x := by
      intro h; have := congrArg f₁ h; rw [hi1 x hx, h12 x hx] at this; exact h03 this
    have h13' : f₁ x ≠ f₃ x := by
      intro h; have := congrArg f₁ h; rw [hi1 x hx, h13 x hx] at this; exact h02 this
    have h23' : f₂ x ≠ f₃ x := by
      intro h; have := congrArg f₂ h; rw [hi2 x hx, h23 x hx] at this; exact h01 this
    simp [orb, h01, h02, h03, h12', h13', h23']
  have horb_eq : ∀ x ∈ S, ∀ y ∈ orb x, orb y = orb x := by
    intro x hx y hy
    simp only [orb, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rfl
    · ext z; simp only [orb, mem_insert, mem_singleton, hi1 x hx, h21 x hx, h31 x hx]; tauto
    · ext z; simp only [orb, mem_insert, mem_singleton, hi2 x hx, h12 x hx, h32 x hx]; tauto
    · ext z; simp only [orb, mem_insert, mem_singleton, hi3 x hx, h13 x hx, h23 x hx]; tauto
  have hS_eq : S = (S.image orb).biUnion id := by
    ext x
    simp only [mem_biUnion, mem_image, id_eq]
    constructor
    · intro hx
      exact ⟨orb x, ⟨x, hx, rfl⟩, by simp [orb]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hx⟩
      simp only [orb, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hy
      · exact hm1 y hy
      · exact hm2 y hy
      · exact hm3 y hy
  have hdisj : ((S.image orb) : Set (Finset α)).PairwiseDisjoint id := by
    intro A hA B hB hne
    rcases mem_image.mp hA with ⟨x, hx, rfl⟩
    rcases mem_image.mp hB with ⟨y, hy, rfl⟩
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro z hzx hzy
    exact hne ((horb_eq x hx z hzx).symm.trans (horb_eq y hy z hzy))
  have hcardS : S.card = (S.image orb).card * 4 := by
    conv_lhs => rw [hS_eq]
    rw [card_biUnion hdisj]
    have hsum : ∑ O ∈ S.image orb, (id O).card = ∑ _O ∈ S.image orb, 4 := by
      refine Finset.sum_congr rfl fun O hO => ?_
      rcases mem_image.mp hO with ⟨x, hx, rfl⟩
      exact horb_card x hx
    rw [hsum, sum_const, smul_eq_mul]
  exact ⟨(S.image orb).card, by omega⟩

/-! ### Elementary arithmetic helpers -/

lemma nat_dist_sq_eq_sub_sq (a b : ℕ) :
    ((Nat.dist a b : ℕ) : ℤ) ^ 2 = ((a : ℤ) - (b : ℤ)) ^ 2 := by
  unfold Nat.dist
  by_cases h : a ≤ b
  · have h1 : a - b = 0 := Nat.sub_eq_zero_of_le h
    rw [h1, zero_add, Nat.cast_sub h]
    ring
  · have hlt : b ≤ a := Nat.le_of_not_le h
    have h2 : b - a = 0 := Nat.sub_eq_zero_of_le hlt
    rw [h2, add_zero, Nat.cast_sub hlt]

lemma no_three_equidistant_nat (a b c : ℕ)
    (h1 : Nat.dist a b = Nat.dist a c)
    (h2 : Nat.dist a b = Nat.dist b c) :
    a = b := by
  have h1' : ((a : ℤ) - b) ^ 2 = ((a : ℤ) - c) ^ 2 := by
    rw [← nat_dist_sq_eq_sub_sq, ← nat_dist_sq_eq_sub_sq, h1]
  have h2' : ((a : ℤ) - b) ^ 2 = ((b : ℤ) - c) ^ 2 := by
    rw [← nat_dist_sq_eq_sub_sq, ← nat_dist_sq_eq_sub_sq, h2]
  have hf1 : ((a : ℤ) - b - ((a : ℤ) - c)) * ((a : ℤ) - b + ((a : ℤ) - c)) = 0 := by linarith
  have hf2 : ((a : ℤ) - b - ((b : ℤ) - c)) * ((a : ℤ) - b + ((b : ℤ) - c)) = 0 := by linarith
  rcases mul_eq_zero.mp hf1 with h1a | h1b <;> rcases mul_eq_zero.mp hf2 with h2a | h2b <;> omega

lemma descent_two_sq_eq_three_sum_sq :
    ∀ k : ℕ, ∀ S D E : ℤ, S.natAbs + D.natAbs + E.natAbs ≤ k →
      2 * S ^ 2 = 3 * (D ^ 2 + E ^ 2) → S = 0 ∧ D = 0 ∧ E = 0 := by
  intro k
  induction k with
  | zero =>
    intro S D E hk _
    have hS : S.natAbs = 0 := by omega
    have hD : D.natAbs = 0 := by omega
    have hE : E.natAbs = 0 := by omega
    exact ⟨Int.natAbs_eq_zero.mp hS, Int.natAbs_eq_zero.mp hD, Int.natAbs_eq_zero.mp hE⟩
  | succ k ih =>
    intro S D E hk heq
    by_cases hzero : S = 0 ∧ D = 0 ∧ E = 0
    · exact hzero
    · have hS3 : ∃ S', S = 3 * S' := by
        obtain ⟨q, r, hS, hr⟩ : ∃ q r : ℤ, S = 3 * q + r ∧ (r = 0 ∨ r = 1 ∨ r = 2) :=
          ⟨S / 3, S % 3, by omega, by omega⟩
        rcases hr with rfl | rfl | rfl
        · exact ⟨q, by omega⟩
        · have : 2 * S ^ 2 = 3 * (6 * q ^ 2 + 4 * q) + 2 := by rw [hS]; ring
          omega
        · have : 2 * S ^ 2 = 3 * (6 * q ^ 2 + 8 * q + 2) + 2 := by rw [hS]; ring
          omega
      obtain ⟨S', rfl⟩ := hS3
      have heq2 : 6 * S' ^ 2 = D ^ 2 + E ^ 2 := by linarith
      have hDE3 : (∃ D', D = 3 * D') ∧ (∃ E', E = 3 * E') := by
        obtain ⟨qD, rD, hD, hrD⟩ : ∃ q r : ℤ, D = 3 * q + r ∧ (r = 0 ∨ r = 1 ∨ r = 2) :=
          ⟨D / 3, D % 3, by omega, by omega⟩
        obtain ⟨qE, rE, hE, hrE⟩ : ∃ q r : ℤ, E = 3 * q + r ∧ (r = 0 ∨ r = 1 ∨ r = 2) :=
          ⟨E / 3, E % 3, by omega, by omega⟩
        have hsq : ∀ x q r : ℤ, x = 3 * q + r →
            (r = 0 → ∃ m, x ^ 2 = 3 * m) ∧
            (r = 1 → ∃ m, x ^ 2 = 3 * m + 1) ∧
            (r = 2 → ∃ m, x ^ 2 = 3 * m + 1) := by
          intro x q r hx
          refine ⟨fun h => ⟨3 * q ^ 2, by rw [hx, h]; ring⟩,
            fun h => ⟨3 * q ^ 2 + 2 * q, by rw [hx, h]; ring⟩,
            fun h => ⟨3 * q ^ 2 + 4 * q + 1, by rw [hx, h]; ring⟩⟩
        rcases hsq D qD rD hD with ⟨hD0, hD1, hD2⟩
        rcases hsq E qE rE hE with ⟨hE0, hE1, hE2⟩
        rcases hrD with rfl | rfl | rfl <;> rcases hrE with rfl | rfl | rfl
        · exact ⟨⟨qD, by omega⟩, ⟨qE, by omega⟩⟩
        · obtain ⟨m1, hm1⟩ := hD0 rfl; obtain ⟨m2, hm2⟩ := hE1 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD0 rfl; obtain ⟨m2, hm2⟩ := hE2 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD1 rfl; obtain ⟨m2, hm2⟩ := hE0 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD1 rfl; obtain ⟨m2, hm2⟩ := hE1 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD1 rfl; obtain ⟨m2, hm2⟩ := hE2 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD2 rfl; obtain ⟨m2, hm2⟩ := hE0 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD2 rfl; obtain ⟨m2, hm2⟩ := hE1 rfl; omega
        · obtain ⟨m1, hm1⟩ := hD2 rfl; obtain ⟨m2, hm2⟩ := hE2 rfl; omega
      obtain ⟨⟨D', rfl⟩, ⟨E', rfl⟩⟩ := hDE3
      have heq3 : 2 * S' ^ 2 = 3 * (D' ^ 2 + E' ^ 2) := by linarith
      have hpos : 0 < S'.natAbs + D'.natAbs + E'.natAbs := by
        by_contra h
        have hS' : S' = 0 := Int.natAbs_eq_zero.mp (by omega)
        have hD' : D' = 0 := Int.natAbs_eq_zero.mp (by omega)
        have hE' : E' = 0 := Int.natAbs_eq_zero.mp (by omega)
        exact hzero ⟨by simp [hS'], by simp [hD'], by simp [hE']⟩
      have hlt : S'.natAbs + D'.natAbs + E'.natAbs ≤ k := by
        have hSabs : (3 * S').natAbs = 3 * S'.natAbs := by rw [Int.natAbs_mul]; rfl
        have hDabs : (3 * D').natAbs = 3 * D'.natAbs := by rw [Int.natAbs_mul]; rfl
        have hEabs : (3 * E').natAbs = 3 * E'.natAbs := by rw [Int.natAbs_mul]; rfl
        omega
      rcases ih S' D' E' hlt heq3 with ⟨hS', hD', hE'⟩
      exact ⟨by simp [hS'], by simp [hD'], by simp [hE']⟩

/-! ### Part 1: Modulo 3 via the 3-cycle `(0 1 2)` -/

def rho : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

lemma rho_cube : rho * rho * rho = 1 := by
  ext i; fin_cases i <;> rfl

lemma actPt_rho_0 {n : ℕ} (x : Point n) : actPt rho x 0 = x 2 := rfl
lemma actPt_rho_1 {n : ℕ} (x : Point n) : actPt rho x 1 = x 0 := rfl
lemma actPt_rho_2 {n : ℕ} (x : Point n) : actPt rho x 2 = x 1 := rfl
lemma actPt_rho_3 {n : ℕ} (x : Point n) : actPt rho x 3 = x 3 := rfl
lemma actPt_rho_sq_0 {n : ℕ} (x : Point n) : actPt (rho * rho) x 0 = x 1 := rfl
lemma actPt_rho_sq_1 {n : ℕ} (x : Point n) : actPt (rho * rho) x 1 = x 2 := rfl
lemma actPt_rho_sq_2 {n : ℕ} (x : Point n) : actPt (rho * rho) x 2 = x 0 := rfl
lemma actPt_rho_sq_3 {n : ℕ} (x : Point n) : actPt (rho * rho) x 3 = x 3 := rfl

lemma equilateral_of_three_eq {n : ℕ} {x y z : Point n}
    (h1 : squaredDist x y = squaredDist y z)
    (h2 : squaredDist x y = squaredDist z x) :
    ∀ u ∈ ({x, y, z} : Finset (Point n)),
    ∀ v ∈ ({x, y, z} : Finset (Point n)),
    ∀ w ∈ ({x, y, z} : Finset (Point n)),
      u ≠ v → v ≠ w → w ≠ u → squaredDist u v = squaredDist u w := by
  intro u hu v hv w hw huv hvw hwu
  have hpair : ∀ p q : Point n, p ∈ ({x, y, z} : Finset (Point n)) →
      q ∈ ({x, y, z} : Finset (Point n)) → p ≠ q → squaredDist p q = squaredDist x y := by
    intro p q hp hq hpq
    simp only [mem_insert, mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact absurd rfl hpq
    · rfl
    · rw [squaredDist_comm, h2]
    · rw [squaredDist_comm]
    · exact absurd rfl hpq
    · exact h1.symm
    · exact h2.symm
    · rw [squaredDist_comm, h1]
    · exact absurd rfl hpq
  rw [hpair u v hu hv huv, hpair u w hu hw hwu.symm]

lemma no_fixed_vertex_in_rho_fixed_tri {n : ℕ} {t : Finset (Point n)}
    (ht : t ∈ triangles n) (hfix : actTri rho t = t) :
    ∀ x ∈ t, actPt rho x ≠ x := by
  simp only [triangles, mem_filter, mem_powersetCard] at ht
  rcases ht with ⟨⟨hsub, hcard⟩, _, heq⟩
  intro x hx hfx
  obtain ⟨a, b, c, hab, hac, hbc, ht3⟩ := Finset.card_eq_three.mp hcard
  have hmem_map : ∀ u ∈ t, actPt rho u ∈ t := by
    intro u hu
    rw [← hfix]
    exact mem_image_of_mem _ hu
  have hall_fix : ∀ u ∈ t, actPt rho u = u := by
    have hcase : ∀ y z : Point n, t = {x, y, z} → x ≠ y → y ≠ z → x ≠ z →
        actPt rho y = y ∧ actPt rho z = z := by
      intro y z hxyz hxy hyz hxz
      have hy_mem : actPt rho y ∈ t := hmem_map y (by rw [hxyz]; simp)
      have hz_mem : actPt rho z ∈ t := hmem_map z (by rw [hxyz]; simp)
      rw [hxyz] at hy_mem hz_mem
      simp only [mem_insert, mem_singleton] at hy_mem hz_mem
      have hy_nex : actPt rho y ≠ x := by
        intro h; exact hxy ((actPt_injective rho) (hfx.trans h.symm))
      have hz_nex : actPt rho z ≠ x := by
        intro h; exact hxz ((actPt_injective rho) (hfx.trans h.symm))
      rcases hy_mem with h | h | h
      · exact absurd h hy_nex
      · refine ⟨h, ?_⟩
        rcases hz_mem with h' | h' | h'
        · exact absurd h' hz_nex
        · exact absurd ((actPt_injective rho) (h'.trans h.symm)) hyz.symm
        · exact h'
      · rcases hz_mem with h' | h' | h'
        · exact absurd h' hz_nex
        · have h3 : actPt rho (actPt rho (actPt rho y)) = y := by
            rw [← actPt_mul, ← actPt_mul, rho_cube, actPt_one]
          rw [h, h', h] at h3
          exact absurd h3 hyz.symm
        · exact absurd ((actPt_injective rho) (h.trans h'.symm)) hyz
    have hxmem : x ∈ ({a, b, c} : Finset (Point n)) := by rw [← ht3]; exact hx
    simp only [mem_insert, mem_singleton] at hxmem
    rcases hxmem with rfl | rfl | rfl
    · have ⟨hb, hc⟩ := hcase b c ht3 hab hbc hac
      intro u hu; rw [ht3] at hu; simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    · have ht3' : t = {x, a, c} := by rw [ht3]; ext u; simp only [mem_insert, mem_singleton]; tauto
      have ⟨ha, hc⟩ := hcase a c ht3' hab.symm hac hbc
      intro u hu; rw [ht3'] at hu; simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    · have ht3' : t = {x, a, b} := by rw [ht3]; ext u; simp only [mem_insert, mem_singleton]; tauto
      have ⟨ha, hb⟩ := hcase a b ht3' hac.symm hab hbc.symm
      intro u hu; rw [ht3'] at hu; simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
  have hdist_fix : ∀ u v : Point n, u ∈ t → v ∈ t →
      squaredDist u v = 12 * (Nat.dist (u 0).val (v 0).val) ^ 2 := by
    intro u v hu hv
    have hu01 : (u 1).val = (u 0).val := congrArg Fin.val (congrFun (hall_fix u hu) 1).symm
    have hu02 : (u 2).val = (u 0).val := by
      have := congrArg Fin.val (congrFun (hall_fix u hu) 2).symm
      rw [actPt_rho_2, hu01] at this; exact this
    have hv01 : (v 1).val = (v 0).val := congrArg Fin.val (congrFun (hall_fix v hv) 1).symm
    have hv02 : (v 2).val = (v 0).val := by
      have := congrArg Fin.val (congrFun (hall_fix v hv) 2).symm
      rw [actPt_rho_2, hv01] at this; exact this
    have hug : (u 0).val + (u 1).val + (u 2).val + (u 3).val = n - 1 := by
      have := (mem_filter.mp (hsub hu)).2
      simpa [Fin.sum_univ_four] using this
    have hvg : (v 0).val + (v 1).val + (v 2).val + (v 3).val = n - 1 := by
      have := (mem_filter.mp (hsub hv)).2
      simpa [Fin.sum_univ_four] using this
    have hsd : (squaredDist u v : ℤ) =
        ((u 0).val - (v 0).val : ℤ) ^ 2 + ((u 1).val - (v 1).val : ℤ) ^ 2 +
        ((u 2).val - (v 2).val : ℤ) ^ 2 + ((u 3).val - (v 3).val : ℤ) ^ 2 := by
      simp only [squaredDist, Fin.sum_univ_four, Nat.cast_add, Nat.cast_pow, nat_dist_sq_eq_sub_sq]
    have hsd' : (squaredDist u v : ℤ) = 12 * ((Nat.dist (u 0).val (v 0).val : ℕ) : ℤ) ^ 2 := by
      rw [hsd, nat_dist_sq_eq_sub_sq]
      have : ((u 3).val : ℤ) - (v 3).val = -3 * (((u 0).val : ℤ) - (v 0).val) := by omega
      rw [hu01, hu02, hv01, hv02, this]
      ring
    exact Int.ofNat.inj (by simpa using hsd')
  have ha : a ∈ t := by rw [ht3]; simp
  have hb : b ∈ t := by rw [ht3]; simp
  have hc : c ∈ t := by rw [ht3]; simp
  have habc : squaredDist a b = squaredDist a c := heq a ha b hb c hc hab hbc hac.symm
  have hbac : squaredDist b a = squaredDist b c := heq b hb a ha c hc hab.symm hac hbc.symm
  rw [squaredDist_comm b a] at hbac
  rw [hdist_fix a b ha hb, hdist_fix a c ha hc] at habc
  rw [hdist_fix a b ha hb, hdist_fix b c hb hc] at hbac
  have hd1 : Nat.dist (a 0).val (b 0).val = Nat.dist (a 0).val (c 0).val := by
    have : (Nat.dist (a 0).val (b 0).val) ^ 2 = (Nat.dist (a 0).val (c 0).val) ^ 2 := by omega
    nlinarith
  have hd2 : Nat.dist (a 0).val (b 0).val = Nat.dist (b 0).val (c 0).val := by
    have : (Nat.dist (a 0).val (b 0).val) ^ 2 = (Nat.dist (b 0).val (c 0).val) ^ 2 := by omega
    nlinarith
  have h0eq : (a 0).val = (b 0).val := no_three_equidistant_nat _ _ _ hd1 hd2
  have ha01 : (a 1).val = (a 0).val := congrArg Fin.val (congrFun (hall_fix a ha) 1).symm
  have ha02 : (a 2).val = (a 0).val := by
    have := congrArg Fin.val (congrFun (hall_fix a ha) 2).symm
    rw [actPt_rho_2, ha01] at this; exact this
  have hb01 : (b 1).val = (b 0).val := congrArg Fin.val (congrFun (hall_fix b hb) 1).symm
  have hb02 : (b 2).val = (b 0).val := by
    have := congrArg Fin.val (congrFun (hall_fix b hb) 2).symm
    rw [actPt_rho_2, hb01] at this; exact this
  have hag : (a 0).val + (a 1).val + (a 2).val + (a 3).val = n - 1 := by
    have := (mem_filter.mp (hsub ha)).2
    simpa [Fin.sum_univ_four] using this
  have hbg : (b 0).val + (b 1).val + (b 2).val + (b 3).val = n - 1 := by
    have := (mem_filter.mp (hsub hb)).2
    simpa [Fin.sum_univ_four] using this
  apply hab
  ext i
  fin_cases i <;> dsimp <;> omega

def mkPt (n : ℕ) (hn : 0 < n) (b : Fin (n - 1)) : Point n :=
  ![⟨0, hn⟩, ⟨b.val, by omega⟩, ⟨n - 1 - b.val, by omega⟩, ⟨0, hn⟩]

def mkTri (n : ℕ) (hn : 0 < n) (b : Fin (n - 1)) : Finset (Point n) :=
  {mkPt n hn b, actPt rho (mkPt n hn b), actPt (rho * rho) (mkPt n hn b)}

lemma mkTri_mem_fixed (n : ℕ) (hn : 0 < n) (b : Fin (n - 1)) :
    mkTri n hn b ∈ (triangles n).filter (fun t => actTri rho t = t) := by
  let x := mkPt n hn b
  have hx_grid : x ∈ grid n := by
    simp only [grid, mem_filter, mem_univ, true_and, Fin.sum_univ_four, x, mkPt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    omega
  have h0 : (x 0).val = 0 := rfl
  have h2 : (x 2).val = n - 1 - b.val := rfl
  have h3 : (x 3).val = 0 := rfl
  have hm_pos : 0 < n - 1 - b.val := by omega
  have hne01 : x ≠ actPt rho x := by
    intro h
    have := congrArg Fin.val (congrFun h 0)
    rw [actPt_rho_0, h0, h2] at this
    omega
  have hne02 : x ≠ actPt (rho * rho) x := by
    intro h
    have := congrArg Fin.val (congrFun h 2)
    rw [actPt_rho_sq_2, h2, h0] at this
    omega
  have hne12 : actPt rho x ≠ actPt (rho * rho) x := by
    intro h
    have := congrArg Fin.val (congrFun h 1)
    rw [actPt_rho_1, actPt_rho_sq_1, h0, h2] at this
    omega
  have hfix : actTri rho (mkTri n hn b) = mkTri n hn b := by
    ext y
    simp only [actTri, mkTri, mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨u, rfl | rfl | rfl, rfl⟩
      · right; left; rfl
      · right; right; rw [← actPt_mul]
      · left; rw [← actPt_mul, ← mul_assoc, rho_cube, actPt_one]
    · rintro (rfl | rfl | rfl)
      · exact ⟨actPt (rho * rho) (mkPt n hn b), by simp, by rw [← actPt_mul, ← mul_assoc, rho_cube, actPt_one]⟩
      · exact ⟨mkPt n hn b, by simp, rfl⟩
      · exact ⟨actPt rho (mkPt n hn b), by simp, by rw [← actPt_mul]⟩
  refine mem_filter.mpr ⟨?_, hfix⟩
  simp only [triangles, mem_filter, mem_powersetCard]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu
    simp only [mkTri, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hx_grid
    · exact actPt_mem_grid rho hx_grid
    · exact actPt_mem_grid (rho * rho) hx_grid
  · change ({x, actPt rho x, actPt (rho * rho) x} : Finset (Point n)).card = 3
    simp [hne01, hne02, hne12]
  · intro i
    fin_cases i
    · exact ⟨x, by simp [mkTri, x], h0⟩
    · exact ⟨actPt rho x, by simp [mkTri, x], by dsimp; rw [actPt_rho_1, h0]⟩
    · exact ⟨actPt (rho * rho) x, by simp [mkTri, x], by dsimp; rw [actPt_rho_sq_2, h0]⟩
    · exact ⟨x, by simp [mkTri, x], h3⟩
  · have hd01_12 : squaredDist x (actPt rho x) = squaredDist (actPt rho x) (actPt (rho * rho) x) := by
      have := squaredDist_actPt rho x (actPt rho x)
      rw [← actPt_mul] at this
      exact this.symm
    have hd01_20 : squaredDist x (actPt rho x) = squaredDist (actPt (rho * rho) x) x := by
      have := squaredDist_actPt (rho * rho) x (actPt rho x)
      rw [← actPt_mul, rho_cube, actPt_one] at this
      exact this.symm
    exact equilateral_of_three_eq hd01_12 hd01_20

lemma fixed_tri_card_eq (n : ℕ) (hn : 0 < n) :
    ((triangles n).filter (fun t => actTri rho t = t)).card = n - 1 := by
  symm
  have hfin : (Finset.univ : Finset (Fin (n - 1))).card = n - 1 := Fintype.card_fin (n - 1)
  rw [← hfin]
  refine Finset.card_bij (fun b _ => mkTri n hn b) ?_ ?_ ?_
  · intro b _
    exact mkTri_mem_fixed n hn b
  · intro b₁ _ b₂ _ heq
    have hmem : mkPt n hn b₁ ∈ mkTri n hn b₂ := by
      rw [← heq]; simp [mkTri]
    simp only [mkTri, mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact Fin.ext (show b₁.val = b₂.val from congrArg (fun p : Fin n => p.val) (congrFun h 1))
    · have h0 := congrArg Fin.val (congrFun h 0)
      have : (mkPt n hn b₁ 0).val = 0 := rfl
      have : (actPt rho (mkPt n hn b₂) 0).val = n - 1 - b₂.val := rfl
      omega
    · have h2 := congrArg Fin.val (congrFun h 2)
      have : (mkPt n hn b₁ 2).val = n - 1 - b₁.val := rfl
      have : (actPt (rho * rho) (mkPt n hn b₂) 2).val = 0 := rfl
      omega
  · intro t ht_filt
    rcases mem_filter.mp ht_filt with ⟨ht, hfix⟩
    have hnofix := no_fixed_vertex_in_rho_fixed_tri ht hfix
    simp only [triangles, mem_filter, mem_powersetCard] at ht
    rcases ht with ⟨⟨hsub, hcard⟩, hfaces, _⟩
    rcases hfaces 0 with ⟨v, hv, hv0⟩
    have hv_ne1 : v ≠ actPt rho v := (hnofix v hv).symm
    have hmem1 : actPt rho v ∈ t := by rw [← hfix]; exact mem_image_of_mem _ hv
    have hmem2 : actPt (rho * rho) v ∈ t := by
      rw [← hfix, actPt_mul]; exact mem_image_of_mem _ hmem1
    have hv_ne2 : v ≠ actPt (rho * rho) v := by
      intro h
      have := congrArg (actPt rho) h
      rw [← actPt_mul, ← mul_assoc, rho_cube, actPt_one] at this
      exact hv_ne1 this.symm
    have hv1_ne2 : actPt rho v ≠ actPt (rho * rho) v := by
      intro h
      exact hv_ne1 ((actPt_injective rho) (by simpa [actPt_mul] using h))
    have ht_eq : t = {v, actPt rho v, actPt (rho * rho) v} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl | rfl <;> assumption
      · rw [hcard]
        have : ({v, actPt rho v, actPt (rho * rho) v} : Finset (Point n)).card = 3 := by
          simp [hv_ne1, hv_ne2, hv1_ne2]
        omega
    rcases hfaces 3 with ⟨w, hw, hw3⟩
    have hv3 : (v 3).val = 0 := by
      rw [ht_eq] at hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hw3
      · simpa [actPt_rho_3] using hw3
      · simpa [actPt_rho_sq_3] using hw3
    have hvg : (v 0).val + (v 1).val + (v 2).val + (v 3).val = n - 1 := by
      have := (mem_filter.mp (hsub hv)).2
      simpa [Fin.sum_univ_four] using this
    by_cases hv2 : (v 2).val = 0
    · have hv1_eq : (v 1).val = n - 1 := by omega
      have hm_pos : 0 < n - 1 := by
        by_contra h0
        have : (v 1).val = 0 := by omega
        apply hv_ne1
        ext i
        fin_cases i
        · change (v 0).val = (v 2).val; omega
        · change (v 1).val = (v 0).val; omega
        · change (v 2).val = (v 1).val; omega
        · rfl
      refine ⟨⟨0, hm_pos⟩, mem_univ _, ?_⟩
      have hw_eq : actPt rho v = mkPt n hn ⟨0, hm_pos⟩ := by
        ext i
        fin_cases i
        · change (v 2).val = 0; exact hv2
        · change (v 0).val = 0; exact hv0
        · change (v 1).val = n - 1 - 0; omega
        · change (v 3).val = 0; exact hv3
      rw [ht_eq, mkTri, ← hw_eq]
      ext u
      simp only [mem_insert, mem_singleton]
      have h1 : actPt rho (actPt rho v) = actPt (rho * rho) v := (actPt_mul rho rho v).symm
      have h2 : actPt (rho * rho) (actPt rho v) = v := by
        rw [← actPt_mul, rho_cube, actPt_one]
      rw [h1, h2]
      tauto
    · have hb_lt : (v 1).val < n - 1 := by omega
      refine ⟨⟨(v 1).val, hb_lt⟩, mem_univ _, ?_⟩
      have hv_eq : v = mkPt n hn ⟨(v 1).val, hb_lt⟩ := by
        ext i; fin_cases i <;> dsimp [mkPt] <;> omega
      rw [ht_eq, mkTri, ← hv_eq]

lemma card_mod_three (n : ℕ) (hn : 0 < n) :
    (triangles n).card ≡ n - 1 [MOD 3] := by
  have hmod := card_mod_three_of_order_three (triangles n) (actTri rho)
    (fun t ht => actTri_mem_triangles rho ht)
    (fun t _ => by rw [← actTri_mul, ← actTri_mul, rho_cube, actTri_one])
  rwa [fixed_tri_card_eq n hn] at hmod

/-! ### Part 2: Modulo 4 via the Klein four-group `V_4` -/

def sigma1 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def sigma2 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def sigma3 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def tau2 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def tau3 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 2, 1]
  invFun := ![0, 3, 2, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

lemma sigma1_sq : sigma1 * sigma1 = 1 := by ext i; fin_cases i <;> rfl
lemma sigma2_sq : sigma2 * sigma2 = 1 := by ext i; fin_cases i <;> rfl
lemma sigma3_sq : sigma3 * sigma3 = 1 := by ext i; fin_cases i <;> rfl
lemma sigma1_mul_sigma2 : sigma1 * sigma2 = sigma3 := by ext i; fin_cases i <;> rfl
lemma sigma2_mul_sigma1 : sigma2 * sigma1 = sigma3 := by ext i; fin_cases i <;> rfl
lemma sigma1_mul_sigma3 : sigma1 * sigma3 = sigma2 := by ext i; fin_cases i <;> rfl
lemma sigma3_mul_sigma1 : sigma3 * sigma1 = sigma2 := by ext i; fin_cases i <;> rfl
lemma sigma2_mul_sigma3 : sigma2 * sigma3 = sigma1 := by ext i; fin_cases i <;> rfl
lemma sigma3_mul_sigma2 : sigma3 * sigma2 = sigma1 := by ext i; fin_cases i <;> rfl
lemma tau2_conj : sigma1 * tau2 = tau2 * sigma2 := by ext i; fin_cases i <;> rfl
lemma tau3_conj : sigma1 * tau3 = tau3 * sigma3 := by ext i; fin_cases i <;> rfl

lemma not_all_fixed_sigma1 {n : ℕ} {t : Finset (Point n)}
    (ht : t ∈ triangles n) {x y z : Point n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ht3 : t = {x, y, z})
    (hfx : actPt sigma1 x = x) (hfy : actPt sigma1 y = y) (hfz : actPt sigma1 z = z) :
    False := by
  simp only [triangles, mem_filter, mem_powersetCard] at ht
  rcases ht with ⟨⟨hsub, _⟩, _, heq⟩
  have hdist : ∀ u v : Point n, u ∈ t → v ∈ t →
      actPt sigma1 u = u → actPt sigma1 v = v →
      squaredDist u v = 4 * (Nat.dist (u 0).val (v 0).val) ^ 2 := by
    intro u v hu hv hfu hfv
    have hu01 : (u 1).val = (u 0).val := congrArg Fin.val (congrFun hfu 0)
    have hu23 : (u 3).val = (u 2).val := congrArg Fin.val (congrFun hfu 2)
    have hv01 : (v 1).val = (v 0).val := congrArg Fin.val (congrFun hfv 0)
    have hv23 : (v 3).val = (v 2).val := congrArg Fin.val (congrFun hfv 2)
    have hug : (u 0).val + (u 1).val + (u 2).val + (u 3).val = n - 1 := by
      have := (mem_filter.mp (hsub hu)).2; simpa [Fin.sum_univ_four] using this
    have hvg : (v 0).val + (v 1).val + (v 2).val + (v 3).val = n - 1 := by
      have := (mem_filter.mp (hsub hv)).2; simpa [Fin.sum_univ_four] using this
    have hsd : (squaredDist u v : ℤ) =
        ((u 0).val - (v 0).val : ℤ) ^ 2 + ((u 1).val - (v 1).val : ℤ) ^ 2 +
        ((u 2).val - (v 2).val : ℤ) ^ 2 + ((u 3).val - (v 3).val : ℤ) ^ 2 := by
      simp only [squaredDist, Fin.sum_univ_four, Nat.cast_add, Nat.cast_pow, nat_dist_sq_eq_sub_sq]
    have hsd' : (squaredDist u v : ℤ) = 4 * ((Nat.dist (u 0).val (v 0).val : ℕ) : ℤ) ^ 2 := by
      rw [hsd, nat_dist_sq_eq_sub_sq]
      have : ((u 2).val : ℤ) - (v 2).val = -(((u 0).val : ℤ) - (v 0).val) := by omega
      rw [hu01, hu23, hv01, hv23, this]
      ring
    exact Int.ofNat.inj (by simpa using hsd')
  have hx : x ∈ t := by rw [ht3]; simp
  have hy : y ∈ t := by rw [ht3]; simp
  have hz : z ∈ t := by rw [ht3]; simp
  have h1 := heq x hx y hy z hz hxy hyz hxz.symm
  have h2 := heq y hy x hx z hz hxy.symm hxz hyz.symm
  rw [squaredDist_comm y x] at h2
  rw [hdist x y hx hy hfx hfy, hdist x z hx hz hfx hfz] at h1
  rw [hdist x y hx hy hfx hfy, hdist y z hy hz hfy hfz] at h2
  have hd1 : Nat.dist (x 0).val (y 0).val = Nat.dist (x 0).val (z 0).val := by
    have : (Nat.dist (x 0).val (y 0).val) ^ 2 = (Nat.dist (x 0).val (z 0).val) ^ 2 := by omega
    nlinarith
  have hd2 : Nat.dist (x 0).val (y 0).val = Nat.dist (y 0).val (z 0).val := by
    have : (Nat.dist (x 0).val (y 0).val) ^ 2 = (Nat.dist (y 0).val (z 0).val) ^ 2 := by omega
    nlinarith
  have h0eq : (x 0).val = (y 0).val := no_three_equidistant_nat _ _ _ hd1 hd2
  have hx01 : (x 1).val = (x 0).val := congrArg Fin.val (congrFun hfx 0)
  have hx23 : (x 3).val = (x 2).val := congrArg Fin.val (congrFun hfx 2)
  have hy01 : (y 1).val = (y 0).val := congrArg Fin.val (congrFun hfy 0)
  have hy23 : (y 3).val = (y 2).val := congrArg Fin.val (congrFun hfy 2)
  have hxg : (x 0).val + (x 1).val + (x 2).val + (x 3).val = n - 1 := by
    have := (mem_filter.mp (hsub hx)).2; simpa [Fin.sum_univ_four] using this
  have hyg : (y 0).val + (y 1).val + (y 2).val + (y 3).val = n - 1 := by
    have := (mem_filter.mp (hsub hy)).2; simpa [Fin.sum_univ_four] using this
  apply hxy
  ext i; fin_cases i <;> dsimp <;> omega

lemma not_one_fixed_two_swapped_sigma1 {n : ℕ} {t : Finset (Point n)}
    (ht : t ∈ triangles n) {u v w : Point n}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t)
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u)
    (hfu : actPt sigma1 u = u) (hfvw : actPt sigma1 v = w) : False := by
  simp only [triangles, mem_filter, mem_powersetCard] at ht
  rcases ht with ⟨⟨hsub, _⟩, _, heq⟩
  have hdist_eq : squaredDist u v = squaredDist v w := by
    rw [squaredDist_comm u v]
    exact heq v hv u hu w hw huv.symm hwu.symm hvw.symm
  have hu01 : (u 1).val = (u 0).val := congrArg Fin.val (congrFun hfu 0)
  have hu23 : (u 3).val = (u 2).val := congrArg Fin.val (congrFun hfu 2)
  have hw0 : (w 0).val = (v 1).val := congrArg Fin.val (congrFun hfvw.symm 0)
  have hw1 : (w 1).val = (v 0).val := congrArg Fin.val (congrFun hfvw.symm 1)
  have hw2 : (w 2).val = (v 3).val := congrArg Fin.val (congrFun hfvw.symm 2)
  have hw3 : (w 3).val = (v 2).val := congrArg Fin.val (congrFun hfvw.symm 3)
  have hug : (u 0).val + (u 1).val + (u 2).val + (u 3).val = n - 1 := by
    have := (mem_filter.mp (hsub hu)).2; simpa [Fin.sum_univ_four] using this
  have hvg : (v 0).val + (v 1).val + (v 2).val + (v 3).val = n - 1 := by
    have := (mem_filter.mp (hsub hv)).2; simpa [Fin.sum_univ_four] using this
  let a : ℤ := (u 0).val
  let b : ℤ := (u 2).val
  let p : ℤ := (v 0).val
  let q : ℤ := (v 1).val
  let r : ℤ := (v 2).val
  let s : ℤ := (v 3).val
  have hsum : 2 * a + 2 * b = p + q + r + s := by omega
  have hduv : (squaredDist u v : ℤ) =
      (a - p) ^ 2 + (a - q) ^ 2 + (b - r) ^ 2 + (b - s) ^ 2 := by
    simp only [squaredDist, Fin.sum_univ_four, Nat.cast_add, Nat.cast_pow,
      nat_dist_sq_eq_sub_sq, hu01, hu23, a, b, p, q, r, s]
  have hdvw : (squaredDist v w : ℤ) =
      (p - q) ^ 2 + (q - p) ^ 2 + (r - s) ^ 2 + (s - r) ^ 2 := by
    simp only [squaredDist, Fin.sum_univ_four, Nat.cast_add, Nat.cast_pow,
      nat_dist_sq_eq_sub_sq, hw0, hw1, hw2, hw3, p, q, r, s]
  have hcast : (squaredDist u v : ℤ) = (squaredDist v w : ℤ) := by exact_mod_cast hdist_eq
  rw [hduv, hdvw] at hcast
  let S : ℤ := 2 * a - p - q
  let D : ℤ := p - q
  let E : ℤ := r - s
  have hSDE : 2 * S ^ 2 = 3 * (D ^ 2 + E ^ 2) := by
    have h2b : 2 * b - r - s = -S := by omega
    have h1 : 2 * ((a - p) ^ 2 + (a - q) ^ 2) = S ^ 2 + D ^ 2 := by
      simp only [S, D]; ring
    have h2 : 2 * ((b - r) ^ 2 + (b - s) ^ 2) = S ^ 2 + E ^ 2 := by
      have : 2 * ((b - r) ^ 2 + (b - s) ^ 2) = (2 * b - r - s) ^ 2 + (r - s) ^ 2 := by ring
      rw [this, h2b]; simp only [E]; ring
    have h3 : (p - q) ^ 2 + (q - p) ^ 2 + (r - s) ^ 2 + (s - r) ^ 2 = 2 * (D ^ 2 + E ^ 2) := by
      simp only [D, E]; ring
    linarith
  have ⟨_, hD0, hE0⟩ := descent_two_sq_eq_three_sum_sq
    (S.natAbs + D.natAbs + E.natAbs) S D E le_rfl hSDE
  apply hvw
  ext i
  fin_cases i <;> dsimp <;> omega

lemma no_fixed_tri_sigma1 {n : ℕ} {t : Finset (Point n)}
    (ht : t ∈ triangles n) : actTri sigma1 t ≠ t := by
  intro hfix
  have hcard : t.card = 3 := (mem_powersetCard.mp (mem_filter.mp ht).1).2
  obtain ⟨x, y, z, hxy, hxz, hyz, ht3⟩ := Finset.card_eq_three.mp hcard
  have hmap : ∀ u ∈ t, actPt sigma1 u ∈ t := by
    intro u hu; rw [← hfix]; exact mem_image_of_mem _ hu
  have hinv : ∀ u : Point n, actPt sigma1 (actPt sigma1 u) = u := by
    intro u; rw [← actPt_mul, sigma1_sq, actPt_one]
  have hx : x ∈ t := by rw [ht3]; simp
  have hy : y ∈ t := by rw [ht3]; simp
  have hz : z ∈ t := by rw [ht3]; simp
  have hfx := hmap x hx
  have hfy := hmap y hy
  have hfz := hmap z hz
  rw [ht3] at hfx hfy hfz
  simp only [mem_insert, mem_singleton] at hfx hfy hfz
  rcases hfx with hfx | hfx | hfx
  · rcases hfy with hfy | hfy | hfy
    · exact hxy ((actPt_injective sigma1) (hfx.trans hfy.symm))
    · rcases hfz with hfz | hfz | hfz
      · exact hxz ((actPt_injective sigma1) (hfx.trans hfz.symm))
      · exact hyz ((actPt_injective sigma1) (hfy.trans hfz.symm))
      · exact not_all_fixed_sigma1 ht hxy hxz hyz ht3 hfx hfy hfz
    · exact not_one_fixed_two_swapped_sigma1 ht hx hy hz hxy hyz hxz.symm hfx hfy
  · have hfz' : actPt sigma1 z = z := by
      rcases hfz with hfz | hfz | hfz
      · have := congrArg (actPt sigma1) hfz; rw [hinv, hfx] at this; exact absurd this hyz.symm
      · exact absurd ((actPt_injective sigma1) (hfx.trans hfz.symm)) hxz
      · exact hfz
    exact not_one_fixed_two_swapped_sigma1 ht hz hx hy hxz.symm hxy hyz hfz' hfx
  · have hfy' : actPt sigma1 y = y := by
      rcases hfy with hfy | hfy | hfy
      · have := congrArg (actPt sigma1) hfy; rw [hinv, hfx] at this; exact absurd this hyz
      · exact hfy
      · exact absurd ((actPt_injective sigma1) (hfx.trans hfy.symm)) hxy
    exact not_one_fixed_two_swapped_sigma1 ht hy hx hz hxy.symm hxz hyz.symm hfy' hfx

lemma no_fixed_tri_sigma2 {n : ℕ} {t : Finset (Point n)}
    (ht : t ∈ triangles n) : actTri sigma2 t ≠ t := by
  intro hfix
  have ht' : actTri tau2 t ∈ triangles n := actTri_mem_triangles tau2 ht
  apply no_fixed_tri_sigma1 ht'
  rw [← actTri_mul, tau2_conj, actTri_mul, hfix]

lemma no_fixed_tri_sigma3 {n : ℕ} {t : Finset (Point n)}
    (ht : t ∈ triangles n) : actTri sigma3 t ≠ t := by
  intro hfix
  have ht' : actTri tau3 t ∈ triangles n := actTri_mem_triangles tau3 ht
  apply no_fixed_tri_sigma1 ht'
  rw [← actTri_mul, tau3_conj, actTri_mul, hfix]

lemma four_dvd_card (n : ℕ) : 4 ∣ (triangles n).card := by
  refine four_dvd_card_of_klein (triangles n) (actTri sigma1) (actTri sigma2) (actTri sigma3)
    (fun _ ht => actTri_mem_triangles sigma1 ht)
    (fun _ ht => actTri_mem_triangles sigma2 ht)
    (fun _ ht => actTri_mem_triangles sigma3 ht)
    (fun _ _ => by rw [← actTri_mul, sigma1_sq, actTri_one])
    (fun _ _ => by rw [← actTri_mul, sigma2_sq, actTri_one])
    (fun _ _ => by rw [← actTri_mul, sigma3_sq, actTri_one])
    (fun _ ht => no_fixed_tri_sigma1 ht)
    (fun _ ht => no_fixed_tri_sigma2 ht)
    (fun _ ht => no_fixed_tri_sigma3 ht)
    (fun _ _ => by rw [← actTri_mul, sigma1_mul_sigma2])
    (fun _ _ => by rw [← actTri_mul, sigma2_mul_sigma1])
    (fun _ _ => by rw [← actTri_mul, sigma1_mul_sigma3])
    (fun _ _ => by rw [← actTri_mul, sigma3_mul_sigma1])
    (fun _ _ => by rw [← actTri_mul, sigma2_mul_sigma3])
    (fun _ _ => by rw [← actTri_mul, sigma3_mul_sigma2])

end OMA.A334386

theorem OMA.solution : type_of% @OMA.S_oeis_a334386.main := by
  intro n hn
  have h3 : (OMA.S_oeis_a334386.triangles n).card % 3 = (n - 1) % 3 :=
    OMA.A334386.card_mod_three n hn
  obtain ⟨k, hk⟩ := OMA.A334386.four_dvd_card n
  rw [Nat.ModEq]
  omega
