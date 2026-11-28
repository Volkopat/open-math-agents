import FormalConjectures.OEIS.«255916»

/-! Completing the squares for the heptagonal, octagonal and nonagonal
summands gives the diagonal form with coefficients 21, 280 and 15.
The correct heptagonal residue follows from its parity and the norm
modulo five, by choosing the sign of that coordinate. -/

namespace OMA.R_OeisA255916_conjecture_1_R1

open Finset

private theorem heptagonal_twice (k : ℤ) :
    (2 : ℤ) * (Nat.generalizedPolygonalNumber 7 k : ℤ) = 5 * k ^ 2 - 3 * k := by
  have hnonneg : (0 : ℤ) ≤ 5 * k ^ 2 - 3 * k := by
    by_cases hk : k ≤ 0
    · nlinarith [sq_nonneg k]
    · have hk' : 1 ≤ k := by omega
      nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ 5 * k - 3 by omega)]
  have hquot : 0 ≤ (5 * k ^ 2 - 3 * k) / 2 := Int.ediv_nonneg hnonneg (by decide)
  have hdvd : (2 : ℤ) ∣ 5 * k ^ 2 - 3 * k := by
    by_cases h : k % 2 = 0
    · use 10 * (k / 2) ^ 2 - 3 * (k / 2)
      have eq : k = 2 * (k / 2) := by omega
      conv_lhs => rw [eq]
      ring
    · use 10 * (k / 2) ^ 2 + 7 * (k / 2) + 1
      have eq : k = 2 * (k / 2) + 1 := by omega
      conv_lhs => rw [eq]
      ring
  have eq : (Nat.generalizedPolygonalNumber 7 k : ℤ) = (5 * k ^ 2 - 3 * k) / 2 := by
    unfold Nat.generalizedPolygonalNumber
    norm_num
    exact hquot
  rw [eq, mul_comm]
  exact Int.ediv_mul_cancel hdvd

private theorem twice_polygonal (m x : ℕ) :
    2 * Nat.polygonalNumber m x = (m - 2) * x * (x - 1) + 2 * x := by
  have evenProduct : Even (x * (x - 1)) := by
    rcases Nat.even_or_odd x with he | ho
    · exact he.mul_right _
    · have hp : Even (x - 1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
      exact hp.mul_left _
  have ev : Even ((m - 2) * x * (x - 1)) := by
    rw [mul_assoc]
    exact evenProduct.mul_left _
  have rem := Nat.even_iff.mp ev
  unfold Nat.polygonalNumber
  have hdiv := Nat.mod_add_div ((m - 2) * x * (x - 1)) 2
  omega

private theorem octagonal_square (x : ℕ) :
    (3 : ℤ) * (Nat.polygonalNumber 8 x : ℤ) + 1 = (3 * (x : ℤ) - 1) ^ 2 := by
  cases x with
  | zero => norm_num
  | succ x =>
    have h := twice_polygonal 8 (x + 1)
    have e : (2 : ℤ) * (Nat.polygonalNumber 8 (x + 1) : ℤ) =
        6 * ((x : ℤ) + 1) * x + 2 * ((x : ℤ) + 1) := by
      simp only [show (8 : ℕ) - 2 = 6 by decide, Nat.add_sub_cancel] at h
      exact_mod_cast h
    push_cast
    nlinarith only [e]

private theorem nonagonal_square (y : ℕ) :
    (56 : ℤ) * (Nat.polygonalNumber 9 y : ℤ) + 25 = (14 * (y : ℤ) - 5) ^ 2 := by
  cases y with
  | zero => norm_num
  | succ y =>
    have h := twice_polygonal 9 (y + 1)
    have e : (2 : ℤ) * (Nat.polygonalNumber 9 (y + 1) : ℤ) =
        7 * ((y : ℤ) + 1) * y + 2 * ((y : ℤ) + 1) := by
      simp only [show (9 : ℕ) - 2 = 7 by decide, Nat.add_sub_cancel] at h
      exact_mod_cast h
    push_cast
    nlinarith only [e]

private theorem positive_of_coordinates (n : ℕ) (u v w : ℤ)
    (h : 21 * u ^ 2 + 280 * v ^ 2 + 15 * w ^ 2 = 840 * (n : ℤ) + 844)
    (hu : u % 10 = 7) (hv : v % 3 = 2) (hvmin : -1 ≤ v)
    (hw : w % 14 = 9) (hwmin : -5 ≤ w) : 0 < OeisA255916.a n := by
  let k := (u + 3) / 10
  let x := ((v + 1) / 3).toNat
  let y := ((w + 5) / 14).toNat
  have he₁ : u = 10 * k - 3 := by dsimp [k]; omega
  have xc : (x : ℤ) = (v + 1) / 3 := Int.toNat_of_nonneg (by omega)
  have yc : (y : ℤ) = (w + 5) / 14 := Int.toNat_of_nonneg (by omega)
  have he₂ : v = 3 * (x : ℤ) - 1 := by omega
  have he₃ : w = 14 * (y : ℤ) - 5 := by omega
  have hs₁ := heptagonal_twice k
  have hs₂ := octagonal_square x
  have hs₃ := nonagonal_square y
  have hs₇ : (40 : ℤ) * (Nat.generalizedPolygonalNumber 7 k : ℤ) + 9 = u ^ 2 := by
    rw [he₁]
    nlinarith only [hs₁]
  rw [← he₂] at hs₂
  rw [← he₃] at hs₃
  rw [← hs₇, ← hs₂, ← hs₃] at h
  have hsum : Nat.generalizedPolygonalNumber 7 k + Nat.polygonalNumber 8 x +
      Nat.polygonalNumber 9 y = n := by
    exact_mod_cast (by linarith only [h] : (Nat.generalizedPolygonalNumber 7 k : ℤ) +
      (Nat.polygonalNumber 8 x : ℤ) + (Nat.polygonalNumber 9 y : ℤ) = (n : ℤ))
  have hx : x < n + 1 := by
    have h := twice_polygonal 8 x
    omega
  have hy : y < n + 1 := by
    have h := twice_polygonal 9 y
    omega
  have hkle : k ≤ (n : ℤ) := by
    by_cases hₖ : k ≤ 0
    · omega
    · have hp : 0 ≤ k * (k - 1) := mul_nonneg (by omega) (by omega)
      have hk : k ≤ (Nat.generalizedPolygonalNumber 7 k : ℤ) := by nlinarith only [hp, hs₁]
      omega
  have hkge : -(n : ℤ) ≤ k := by
    by_cases hₖ : 0 ≤ k
    · omega
    · have hn : 0 ≤ 5 * k ^ 2 - k := by nlinarith [sq_nonneg k]
      have hk : -k ≤ (Nat.generalizedPolygonalNumber 7 k : ℤ) := by linarith only [hn, hs₁]
      omega
  let i := (k + (n : ℤ) + 1).toNat
  have hi : (i : ℤ) = k + (n : ℤ) + 1 := Int.toNat_of_nonneg (by omega)
  have himem : i ∈ range (2 * n + 3) := mem_range.mpr (by omega)
  have hxmem : x ∈ range (n + 1) := mem_range.mpr hx
  have hymem : y ∈ range (n + 1) := mem_range.mpr hy
  let contribution (j : ℕ) : ℕ :=
    ∑ t ∈ range (n + 1), ∑ z ∈ range (n + 1),
      if Nat.generalizedPolygonalNumber 7 ((j : ℤ) - (n + 1 : ℤ)) +
          Nat.polygonalNumber 8 t + Nat.polygonalNumber 9 z = n then 1 else 0
  change 0 < ∑ j ∈ range (2 * n + 3), contribution j
  apply lt_of_lt_of_le (show 0 < (1 : ℕ) by decide)
  calc 1 = (if Nat.generalizedPolygonalNumber 7 ((i : ℤ) - (n + 1 : ℤ)) +
        Nat.polygonalNumber 8 x + Nat.polygonalNumber 9 y = n then 1 else 0) := by
          rw [show (i : ℤ) - (n + 1 : ℤ) = k by omega, if_pos hsum]
    _ ≤ ∑ j ∈ range (n + 1), (if Nat.generalizedPolygonalNumber 7 ((i : ℤ) - (n + 1 : ℤ)) +
        Nat.polygonalNumber 8 x + Nat.polygonalNumber 9 j = n then 1 else 0) :=
      Finset.single_le_sum
        (f := fun j ↦ if Nat.generalizedPolygonalNumber 7 ((i : ℤ) - (n + 1 : ℤ)) +
            Nat.polygonalNumber 8 x + Nat.polygonalNumber 9 j = n then 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hymem
    _ ≤ ∑ t ∈ range (n + 1), ∑ j ∈ range (n + 1),
        (if Nat.generalizedPolygonalNumber 7 ((i : ℤ) - (n + 1 : ℤ)) +
          Nat.polygonalNumber 8 t + Nat.polygonalNumber 9 j = n then 1 else 0) :=
      Finset.single_le_sum
        (f := fun t ↦ ∑ j ∈ range (n + 1),
          if Nat.generalizedPolygonalNumber 7 ((i : ℤ) - (n + 1 : ℤ)) +
            Nat.polygonalNumber 8 t + Nat.polygonalNumber 9 j = n then 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hxmem
    _ ≤ _ := Finset.single_le_sum (f := contribution) (fun _ _ ↦ Nat.zero_le _) himem

private theorem heptagonal_residue {n : ℕ} {u v w : ℤ}
    (h : 21 * u ^ 2 + 280 * v ^ 2 + 15 * w ^ 2 = 840 * (n : ℤ) + 844)
    (ho : u % 2 = 1) : u % 10 = 7 ∨ (-u) % 10 = 7 := by
  have hu : (u * u) % 5 = 4 := by rw [← pow_two]; omega
  rw [Int.mul_emod] at hu
  have hlow : 0 ≤ u % 5 := Int.emod_nonneg _ (by decide)
  have hhigh : u % 5 < 5 := Int.emod_lt_of_pos _ (by decide)
  interval_cases hr : u % 5 <;> norm_num [hr] at hu <;> omega

/-- The ternary form represents the progression with an odd heptagonal coordinate. -/
def H1 : Prop :=
  ∀ n : ℕ, ∃ u v w : ℤ, 21 * u ^ 2 + 280 * v ^ 2 + 15 * w ^ 2 = 840 * (n : ℤ) + 844 ∧
    u % 2 = 1

/-- The octagonal and nonagonal coordinates can be put in their specified
residue classes and the half-lines corresponding to nonnegative indices. -/
def H2 : Prop :=
  ∀ n : ℕ, (∃ u v w : ℤ, 21 * u ^ 2 + 280 * v ^ 2 + 15 * w ^ 2 = 840 * (n : ℤ) + 844 ∧
      u % 2 = 1) →
    ∃ u v w : ℤ, 21 * u ^ 2 + 280 * v ^ 2 + 15 * w ^ 2 = 840 * (n : ℤ) + 844 ∧
      u % 2 = 1 ∧ v % 3 = 2 ∧ -1 ≤ v ∧ w % 14 = 9 ∧ -5 ≤ w

theorem main : H1 → H2 → type_of% @OeisA255916.conjecture_1 := by
  intro seed normalize n
  obtain ⟨u, v, w, h, ho, hv, hvl, hw, hwl⟩ := normalize n (seed n)
  rcases heptagonal_residue h ho with h₁ | h₂
  · exact positive_of_coordinates n u v w h h₁ hv hvl hw hwl
  · exact positive_of_coordinates n (-u) v w (by simpa using h) h₂ hv hvl hw hwl

end OMA.R_OeisA255916_conjecture_1_R1
