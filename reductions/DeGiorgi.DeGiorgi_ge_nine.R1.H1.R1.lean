import OMAReductions.R_DeGiorgi_DeGiorgi_ge_nine_R1

/-!
Reduction of `DeGiorgi.DeGiorgi_ge_nine.R1.H1` (counterexample to De Giorgi's conjecture in
dimension 9, del Pino-Kowalczyk-Wei, *Annals of Mathematics* 174 (2011), Theorem 1) to two
classical geometric-PDE pillars in dimension 8 and dimension 9:

- `H1`: Bombieri-De Giorgi-Giusti (1969), *Invent. Math.* 7, Theorem A: existence of a smooth,
  non-planar, `O(4) x O(4)`-invariant, block-swap anti-symmetric entire minimal graph over `R^8`
  solving the minimal surface equation `(1 + |grad F|^2) Delta F - sum_{i,j} F_i F_j F_{ij} = 0`.
- `H2`: del Pino-Kowalczyk-Wei (2011), *Annals of Mathematics* 174, Theorem 1: existence of a
  bounded entire classical solution `u : R^9 -> R` to the Allen-Cahn equation
  `Delta u + u - u^3 = 0` with strictly positive derivative along `e_0`, `O(4) x O(4)` radial
  symmetry and block-swap skew-symmetry, and non-vanishing restriction on `{x_0 = 0}`, built
  from the `O(4) x O(4)`-invariant minimal graph in `H1`.

In `main` and the private geometric lemmas below, we prove completely in Lean 4:
1. Horizontal reflection symmetry `R(x) = 2 * (x 0) * e_0 - x` is an involution preserving the
   zeroth coordinate and negating coordinates `1..8`, and every `O(4) x O(4)`-radial skew-symmetric
   function `u` satisfies `u 0 = 0` and `u (R x) = u x`.
2. Non-planarity of any `O(4) x O(4)`-radial skew-symmetric non-zero function on `R^8`.
3. Strict monotonicity along every vertical line `t |-> u (x + t * e_0)` directly from
   `DeGiorgi.HasPositiveDeriv u`.
4. Hyperplane characterization: any linear hyperplane `W <= R^9` transverse to `e_0` (`e_0 notin W`)
   and invariant under horizontal reflection `R` MUST coincide identically with `{x | x 0 = 0}`.
5. Obstruction to `DeGiorgi.HasHyperplaneLevelSets u`: if `u^{-1}({0})` were an affine hyperplane
   `S`, then `0 in S` forces `S = S.direction`, `e_0 notin S.direction` by strict monotonicity,
   and horizontal reflection invariance forces `S.direction = {x | x 0 = 0}`, contradicting
   `exists y, y 0 = 0 and u y != 0`.
-/

open scoped Laplacian

namespace OMA.R_DeGiorgi_DeGiorgi_ge_nine_R1_H1_R1

/- Bombieri-De Giorgi-Giusti (1969, Invent. Math. 7): existence of a C^3, O(4) x O(4)-invariant,
block-swap anti-symmetric, non-zero entire solution to the minimal surface equation on R^8. -/
def H1 : Prop :=
  ∃ F : EuclideanSpace ℝ (Fin 8) → ℝ,
    ContDiff ℝ 3 F ∧
    (∃ f : ℝ → ℝ → ℝ,
      (∀ w : EuclideanSpace ℝ (Fin 8),
        F w = f (∑ i : Fin 4, (w ⟨i.val, by omega⟩) ^ 2)
                (∑ i : Fin 4, (w ⟨i.val + 4, by omega⟩) ^ 2)) ∧
      (∀ r s : ℝ, f s r = -f r s)) ∧
    (∃ w : EuclideanSpace ℝ (Fin 8), F w ≠ 0) ∧
    (∀ w : EuclideanSpace ℝ (Fin 8),
      (1 + ∑ i : Fin 8, (lineDeriv ℝ F w (EuclideanSpace.single i 1)) ^ 2) * (Δ F w) -
        ∑ i : Fin 8, ∑ j : Fin 8,
          lineDeriv ℝ F w (EuclideanSpace.single i 1) *
          lineDeriv ℝ F w (EuclideanSpace.single j 1) *
          lineDeriv ℝ (fun z => lineDeriv ℝ F z (EuclideanSpace.single i 1)) w
            (EuclideanSpace.single j 1) = 0)

/- del Pino-Kowalczyk-Wei (2011, Annals of Math. 174, Theorem 1): given an entire O(4) x O(4)-
invariant anti-symmetric non-zero minimal graph on R^8, there exists a bounded monotone entire
Allen-Cahn solution on R^9 sharing O(4) x O(4) radial skew-symmetry and non-trivial on {x 0 = 0}. -/
def H2 : Prop :=
  ∀ F : EuclideanSpace ℝ (Fin 8) → ℝ,
    ContDiff ℝ 3 F →
    (∃ f : ℝ → ℝ → ℝ,
      (∀ w : EuclideanSpace ℝ (Fin 8),
        F w = f (∑ i : Fin 4, (w ⟨i.val, by omega⟩) ^ 2)
                (∑ i : Fin 4, (w ⟨i.val + 4, by omega⟩) ^ 2)) ∧
      (∀ r s : ℝ, f s r = -f r s)) →
    (∃ w : EuclideanSpace ℝ (Fin 8), F w ≠ 0) →
    (∀ w : EuclideanSpace ℝ (Fin 8),
      (1 + ∑ i : Fin 8, (lineDeriv ℝ F w (EuclideanSpace.single i 1)) ^ 2) * (Δ F w) -
        ∑ i : Fin 8, ∑ j : Fin 8,
          lineDeriv ℝ F w (EuclideanSpace.single i 1) *
          lineDeriv ℝ F w (EuclideanSpace.single j 1) *
          lineDeriv ℝ (fun z => lineDeriv ℝ F z (EuclideanSpace.single i 1)) w
            (EuclideanSpace.single j 1) = 0) →
    ∃ u : EuclideanSpace ℝ (Fin 9) → ℝ,
      DeGiorgi.IsBoundedSolution u ∧
      DeGiorgi.HasPositiveDeriv u ∧
      (∃ U : ℝ → ℝ → ℝ → ℝ,
        (∀ x : EuclideanSpace ℝ (Fin 9),
          u x = U (x 0)
                  (∑ i : Fin 4, (x ⟨i.val + 1, by omega⟩) ^ 2)
                  (∑ i : Fin 4, (x ⟨i.val + 5, by omega⟩) ^ 2)) ∧
        (∀ t r s : ℝ, U (-t) s r = -U t r s)) ∧
      (∃ y : EuclideanSpace ℝ (Fin 9), y 0 = 0 ∧ u y ≠ 0)

section

private lemma zero_eq_of_radial_skew_eight
    {F : EuclideanSpace ℝ (Fin 8) → ℝ} {f : ℝ → ℝ → ℝ}
    (hF : ∀ w : EuclideanSpace ℝ (Fin 8),
      F w = f (∑ i : Fin 4, (w ⟨i.val, by omega⟩) ^ 2)
              (∑ i : Fin 4, (w ⟨i.val + 4, by omega⟩) ^ 2))
    (hskew : ∀ r s : ℝ, f s r = -f r s) :
    F 0 = 0 := by
  rw [hF 0]
  have hsum : (∑ i : Fin 4, ((0 : EuclideanSpace ℝ (Fin 8)) ⟨i.val, by omega⟩) ^ 2) = 0 := by
    simp
  have hsum2 : (∑ i : Fin 4, ((0 : EuclideanSpace ℝ (Fin 8)) ⟨i.val + 4, by omega⟩) ^ 2) = 0 := by
    simp
  rw [hsum, hsum2]
  have h0 := hskew 0 0
  linarith

private lemma even_of_radial_eight
    {F : EuclideanSpace ℝ (Fin 8) → ℝ} {f : ℝ → ℝ → ℝ}
    (hF : ∀ w : EuclideanSpace ℝ (Fin 8),
      F w = f (∑ i : Fin 4, (w ⟨i.val, by omega⟩) ^ 2)
              (∑ i : Fin 4, (w ⟨i.val + 4, by omega⟩) ^ 2))
    (w : EuclideanSpace ℝ (Fin 8)) :
    F (-w) = F w := by
  rw [hF (-w), hF w]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp

private lemma not_affine_of_radial_skew_nonzero
    {F : EuclideanSpace ℝ (Fin 8) → ℝ} {f : ℝ → ℝ → ℝ}
    (hF : ∀ w : EuclideanSpace ℝ (Fin 8),
      F w = f (∑ i : Fin 4, (w ⟨i.val, by omega⟩) ^ 2)
              (∑ i : Fin 4, (w ⟨i.val + 4, by omega⟩) ^ 2))
    (hskew : ∀ r s : ℝ, f s r = -f r s)
    (hne : ∃ w : EuclideanSpace ℝ (Fin 8), F w ≠ 0) :
    ¬ ∃ (L : EuclideanSpace ℝ (Fin 8) →ₗ[ℝ] ℝ) (c : ℝ), ∀ w, F w = L w + c := by
  rintro ⟨L, c, haff⟩
  have hF0 : F 0 = 0 := zero_eq_of_radial_skew_eight hF hskew
  have hc : c = 0 := by
    have h0 := haff 0
    rw [hF0, map_zero, zero_add] at h0
    exact h0.symm
  obtain ⟨w, hw⟩ := hne
  have hev : F (-w) = F w := even_of_radial_eight hF w
  have h1 := haff w
  have h2 := haff (-w)
  rw [hc, add_zero] at h1 h2
  rw [map_neg] at h2
  exact hw (by linarith)

private lemma horizontalReflect_apply_zero (x : EuclideanSpace ℝ (Fin 9)) :
    ((2 : ℝ) • (x 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - x) 0 = x 0 := by
  simp
  ring

private lemma horizontalReflect_apply_ne_zero (x : EuclideanSpace ℝ (Fin 9))
    {i : Fin 9} (hi : i ≠ 0) :
    ((2 : ℝ) • (x 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - x) i = -x i := by
  simp [hi]

private lemma u_zero_eq_zero_of_radial_skew
    {u : EuclideanSpace ℝ (Fin 9) → ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hu : ∀ x : EuclideanSpace ℝ (Fin 9),
      u x = U (x 0)
              (∑ i : Fin 4, (x ⟨i.val + 1, by omega⟩) ^ 2)
              (∑ i : Fin 4, (x ⟨i.val + 5, by omega⟩) ^ 2))
    (hskew : ∀ t r s : ℝ, U (-t) s r = -U t r s) :
    u 0 = 0 := by
  rw [hu 0]
  have h0 : ((0 : EuclideanSpace ℝ (Fin 9)) 0) = 0 := rfl
  have hsum1 : (∑ i : Fin 4, ((0 : EuclideanSpace ℝ (Fin 9)) ⟨i.val + 1, by omega⟩) ^ 2) = 0 := by
    simp
  have hsum2 : (∑ i : Fin 4, ((0 : EuclideanSpace ℝ (Fin 9)) ⟨i.val + 5, by omega⟩) ^ 2) = 0 := by
    simp
  rw [h0, hsum1, hsum2]
  have h := hskew 0 0 0
  rw [neg_zero] at h
  linarith

private lemma u_horizontalReflect_eq_of_radial
    {u : EuclideanSpace ℝ (Fin 9) → ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hu : ∀ x : EuclideanSpace ℝ (Fin 9),
      u x = U (x 0)
              (∑ i : Fin 4, (x ⟨i.val + 1, by omega⟩) ^ 2)
              (∑ i : Fin 4, (x ⟨i.val + 5, by omega⟩) ^ 2))
    (x : EuclideanSpace ℝ (Fin 9)) :
    u ((2 : ℝ) • (x 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - x) = u x := by
  let r : EuclideanSpace ℝ (Fin 9) :=
    (2 : ℝ) • (x 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - x
  change u r = u x
  rw [hu r, hu x]
  have hr0 : r 0 = x 0 := horizontalReflect_apply_zero x
  have hsum1 :
      (∑ i : Fin 4, (r ⟨i.val + 1, by omega⟩) ^ 2) =
      (∑ i : Fin 4, (x ⟨i.val + 1, by omega⟩) ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : (⟨i.val + 1, by omega⟩ : Fin 9) ≠ 0 := by
      intro h
      have hv : i.val + 1 = 0 := congrArg Fin.val h
      omega
    rw [horizontalReflect_apply_ne_zero x hne, neg_sq]
  have hsum2 :
      (∑ i : Fin 4, (r ⟨i.val + 5, by omega⟩) ^ 2) =
      (∑ i : Fin 4, (x ⟨i.val + 5, by omega⟩) ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : (⟨i.val + 5, by omega⟩ : Fin 9) ≠ 0 := by
      intro h
      have hv : i.val + 5 = 0 := congrArg Fin.val h
      omega
    rw [horizontalReflect_apply_ne_zero x hne, neg_sq]
  rw [hr0, hsum1, hsum2]

private lemma strictMono_vertical_of_hasPositiveDeriv
    {u : EuclideanSpace ℝ (Fin 9) → ℝ} (hu_pos : DeGiorgi.HasPositiveDeriv u)
    (x : EuclideanSpace ℝ (Fin 9)) :
    StrictMono (fun t : ℝ => u (x + t • EuclideanSpace.single (0 : Fin 9) (1 : ℝ))) := by
  let e₀ : EuclideanSpace ℝ (Fin 9) := EuclideanSpace.single (0 : Fin 9) (1 : ℝ)
  refine strictMono_of_deriv_pos fun t => ?_
  have hpos : 0 < lineDeriv ℝ u (x + t • e₀) e₀ := hu_pos (x + t • e₀)
  have hshift :
      deriv (fun s : ℝ => u (x + s • e₀)) (t + 0) =
      deriv (fun s : ℝ => u (x + (t + s) • e₀)) 0 :=
    (deriv_comp_const_add (f := fun s : ℝ => u (x + s • e₀)) t 0).symm
  rw [add_zero] at hshift
  have hfun :
      (fun s : ℝ => u (x + (t + s) • e₀)) =
      (fun s : ℝ => u ((x + t • e₀) + s • e₀)) := by
    funext s
    rw [add_smul, add_assoc]
  rw [hshift, hfun]
  exact hpos

private lemma mem_affineSubspace_iff_mem_direction_of_zero_mem
    {S : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 9))}
    (h0 : (0 : EuclideanSpace ℝ (Fin 9)) ∈ S) (x : EuclideanSpace ℝ (Fin 9)) :
    x ∈ S ↔ x ∈ S.direction := by
  constructor
  · intro hx
    have h := AffineSubspace.vsub_mem_direction hx h0
    rwa [vsub_eq_sub, sub_zero] at h
  · intro hx
    have h := AffineSubspace.vadd_mem_of_mem_direction hx h0
    rwa [vadd_eq_add, add_zero] at h

private lemma sup_span_single_zero_eq_top
    {W : Submodule ℝ (EuclideanSpace ℝ (Fin 9))}
    (hdim : Module.finrank ℝ W = 8)
    (he₀ : EuclideanSpace.single (0 : Fin 9) (1 : ℝ) ∉ W) :
    W ⊔ Submodule.span ℝ {EuclideanSpace.single (0 : Fin 9) (1 : ℝ)} = ⊤ := by
  let e₀ : EuclideanSpace ℝ (Fin 9) := EuclideanSpace.single (0 : Fin 9) (1 : ℝ)
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin 9)) := W ⊔ Submodule.span ℝ {e₀}
  have hlt : W < U := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hmem : e₀ ∈ U :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self e₀)
    rw [← heq] at hmem
    exact he₀ hmem
  have hrank_lt : Module.finrank ℝ W < Module.finrank ℝ U :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hrank_le : Module.finrank ℝ U ≤
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 9)) :=
    Submodule.finrank_le _
  have hfin9 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 9)) = 9 := by
    simp
  have hrank_eq : Module.finrank ℝ U =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 9)) := by
    omega
  exact Submodule.eq_top_of_finrank_eq hrank_eq

private lemma mem_hyperplane_iff_coord_zero
    {W : Submodule ℝ (EuclideanSpace ℝ (Fin 9))}
    (hdim : Module.finrank ℝ W = 8)
    (he₀ : EuclideanSpace.single (0 : Fin 9) (1 : ℝ) ∉ W)
    (hrefl : ∀ v ∈ W, (2 : ℝ) • (v 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - v ∈ W)
    (x : EuclideanSpace ℝ (Fin 9)) :
    x ∈ W ↔ x 0 = 0 := by
  let e₀ : EuclideanSpace ℝ (Fin 9) := EuclideanSpace.single (0 : Fin 9) (1 : ℝ)
  have hcoord : ∀ v ∈ W, v 0 = 0 := by
    intro v hv
    have hv' : (2 : ℝ) • (v 0 • e₀) - v ∈ W := hrefl v hv
    have hsum : v + ((2 : ℝ) • (v 0 • e₀) - v) ∈ W := W.add_mem hv hv'
    have hsimp : v + ((2 : ℝ) • (v 0 • e₀) - v) = (2 * v 0) • e₀ := by
      module
    rw [hsimp] at hsum
    by_contra hv0
    have h2v0 : (2 * v 0 : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hv0
    have he₀W : e₀ ∈ W := by
      have hsmul := W.smul_mem (2 * v 0)⁻¹ hsum
      rw [smul_smul, inv_mul_cancel₀ h2v0, one_smul] at hsmul
      exact hsmul
    exact he₀ he₀W
  constructor
  · exact hcoord x
  · intro hx0
    have htop : W ⊔ Submodule.span ℝ {e₀} = ⊤ := sup_span_single_zero_eq_top hdim he₀
    have hx_mem : x ∈ W ⊔ Submodule.span ℝ {e₀} := by
      rw [htop]
      trivial
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx_mem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hv0 : v 0 = 0 := hcoord v hv
    have hc : c = 0 := by
      have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 9) => z 0) hvw
      simp [e₀, hv0, hx0] at h0
      exact h0
    rw [hc, zero_smul, add_zero] at hvw
    rw [← hvw]
    exact hv

private lemma not_hasHyperplaneLevelSets_of_even_nonflat
    {u : EuclideanSpace ℝ (Fin 9) → ℝ}
    (hu_pos : DeGiorgi.HasPositiveDeriv u)
    (hu0 : u 0 = 0)
    (heven : ∀ x : EuclideanSpace ℝ (Fin 9),
      u ((2 : ℝ) • (x 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - x) = u x)
    (hnonflat : ∃ y : EuclideanSpace ℝ (Fin 9), y 0 = 0 ∧ u y ≠ 0) :
    ¬ DeGiorgi.HasHyperplaneLevelSets u := by
  intro hhyp
  let e₀ : EuclideanSpace ℝ (Fin 9) := EuclideanSpace.single (0 : Fin 9) (1 : ℝ)
  have h0_range : (0 : ℝ) ∈ Set.range u := ⟨0, hu0⟩
  obtain ⟨S, hS_eq, hS_dim⟩ := hhyp 0 h0_range
  have hmem_S : ∀ x : EuclideanSpace ℝ (Fin 9), u x = 0 ↔ x ∈ S := fun x => by
    have h := Set.ext_iff.mp hS_eq x
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe] using h
  have h0S : (0 : EuclideanSpace ℝ (Fin 9)) ∈ S := (hmem_S 0).mp hu0
  have hmem_dir : ∀ x : EuclideanSpace ℝ (Fin 9), u x = 0 ↔ x ∈ S.direction := fun x =>
    (hmem_S x).trans (mem_affineSubspace_iff_mem_direction_of_zero_mem h0S x)
  have he₀_not_mem : e₀ ∉ S.direction := by
    intro he₀_mem
    have hu_e₀ : u e₀ = 0 := (hmem_dir e₀).mpr he₀_mem
    have hmono := strictMono_vertical_of_hasPositiveDeriv hu_pos 0
    have hlt := hmono (show (0 : ℝ) < 1 by norm_num)
    simp only [zero_add, zero_smul, one_smul] at hlt
    change u 0 < u e₀ at hlt
    linarith
  have hrefl : ∀ v ∈ S.direction, (2 : ℝ) • (v 0 • e₀) - v ∈ S.direction := by
    intro v hv
    rw [← hmem_dir]
    rw [heven v]
    exact (hmem_dir v).mpr hv
  obtain ⟨y, hy0, huy⟩ := hnonflat
  have hy_dir : y ∈ S.direction :=
    (mem_hyperplane_iff_coord_zero hS_dim he₀_not_mem hrefl y).mpr hy0
  exact huy ((hmem_dir y).mpr hy_dir)

end

theorem main : H1 → H2 → OMA.R_DeGiorgi_DeGiorgi_ge_nine_R1.H1 := by
  intro h1 h2 hconcl
  obtain ⟨F, hF_smooth, ⟨f, hF_rad, hF_skew⟩, hF_ne, hF_pde⟩ := h1
  have _hF_nonaff := not_affine_of_radial_skew_nonzero hF_rad hF_skew hF_ne
  obtain ⟨u, hu_sol, hu_pos, ⟨U, hu_rad, hu_skew⟩, hnonflat⟩ :=
    h2 F hF_smooth ⟨f, hF_rad, hF_skew⟩ hF_ne hF_pde
  have hu0 : u 0 = 0 := u_zero_eq_zero_of_radial_skew hu_rad hu_skew
  have heven : ∀ x : EuclideanSpace ℝ (Fin 9),
      u ((2 : ℝ) • (x 0 • EuclideanSpace.single (0 : Fin 9) (1 : ℝ)) - x) = u x :=
    u_horizontalReflect_eq_of_radial hu_rad
  exact not_hasHyperplaneLevelSets_of_even_nonflat hu_pos hu0 heven hnonflat
    (hconcl u ⟨hu_sol, hu_pos⟩)

end OMA.R_DeGiorgi_DeGiorgi_ge_nine_R1_H1_R1
