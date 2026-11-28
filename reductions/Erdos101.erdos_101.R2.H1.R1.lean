import OMAReductions.R_Erdos101_erdos_101_R2

-- Reduction Erdos101.erdos_101.R2.H1.R1 of step Erdos101.erdos_101.R2.H1
-- Credit: @ubuwaits

/-!
# Center-dependent division ratios on homogeneous representatives

The geometric extraction asks for one nonzero representative of each plane
point and one division ratio for each starting point of a marked triple.
The second step is a finite inverse theorem about these representatives. A
dense family with center-dependent ratios contains a dense constant-ratio
subfamily. On this subfamily the vertex factors cancel around every triangle.
-/

namespace OMA.R_Erdos101_erdos_101_R2_H1_R1

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles
open scoped Classical

/-- Geometric extraction of compatible representatives on four-point lines. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    δ*(S.card : ℝ)^2 ≤ (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ T : Finset (S × S × S), ExplicitDisjoint T ∧ ρ*(S.card : ℝ)^2 ≤ T.card ∧
      (T : Set (S × S × S)).InjOn (fun e => line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)]) ∧
      (∀ e ∈ T, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
        line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²)) ∧
      ∃ h s : ℝ² → ℝˣ, (∀ x ∈ S, s x ≠ 1) ∧
        let X (x : S) : ℝ × ℝ² := ((h x : ℝ), (h x : ℝ) • (x : ℝ²))
        ∀ e ∈ T, X e.2.2 = (1-(s e.1 : ℝ)) • X e.1 + (s e.1 : ℝ) • X e.2.1

/-- A positive proportion of a dense family of marked triples with one
division ratio per starting point share a single division ratio. -/
def H2 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) → ∀ T : Finset (S × S × S),
    ExplicitDisjoint T → ρ*(S.card : ℝ)^2 ≤ T.card →
    ∀ h s : ℝ² → ℝˣ, (∀ x ∈ S, s x ≠ 1) →
    (let X (x : S) : ℝ × ℝ² := ((h x : ℝ), (h x : ℝ) • (x : ℝ²))
     ∀ e ∈ T, X e.2.2 = (1-(s e.1 : ℝ)) • X e.1 + (s e.1 : ℝ) • X e.2.1) →
    ∃ r : ℝˣ, r ≠ 1 ∧ ∃ U ⊆ T, η*(S.card : ℝ)^2 ≤ U.card ∧ ∀ e ∈ U, s e.1 = r

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R2.H1 := by
  intro extraction concentration δ hδ
  obtain ⟨ρ,hρ,N,find⟩ := extraction δ hδ
  obtain ⟨η,hη,M,concentrate⟩ := concentration ρ hρ
  refine ⟨1,η,hη,max N M,?_⟩
  intro S hn cap dense
  obtain ⟨T,hd,size,lines,marks,h,s,hs,weight⟩ := find S ((le_max_left ..).trans hn) cap dense
  obtain ⟨r,hr,U,sub,hu,hits⟩ := concentrate S ((le_max_right ..).trans hn) cap T hd size h s hs weight
  have du : ExplicitDisjoint U := ⟨fun _ _ _ _ a b => hd.inj₀ (sub a) (sub b),
    fun _ _ _ _ a b => hd.inj₁ (sub a) (sub b),fun _ _ _ _ a b => hd.inj₂ (sub a) (sub b)⟩
  have hr' : (r : ℝ) ≠ 1 := fun e => hr (Units.ext e)
  let q : ℝˣ := Units.mk0 (1-(r : ℝ)) (sub_ne_zero.mpr hr'.symm)
  let a (x z : S) := q*h x/h z
  let b (y z : S) := r*h y/h z
  let d (x y : S) := r*h y/(q*h x)
  have acoef (x z : S) : (h z : ℝ)*(a x z : ℝ) = (1-(r : ℝ))*(h x : ℝ) := by
    simp [a,q]
    field_simp
  have bcoef (y z : S) : (h z : ℝ)*(b y z : ℝ) = (r : ℝ)*(h y : ℝ) := by
    simp [b]
    field_simp
  have cancel (x y z : S) : a x z*d x y = b y z := by
    apply Units.ext
    simp [a,b,d]
  refine ⟨U,du,hu,lines.mono (Finset.coe_subset.mpr sub),fun e he => marks e (sub he),a,b,d,?_,
    {1},by simp,?_⟩
  · intro e he
    have weights := weight e (sub he)
    rw [hits e he] at weights
    have scalar := congrArg Prod.fst weights
    have vector := congrArg Prod.snd weights
    change (h e.2.2 : ℝ) = (1-(r : ℝ))*(h e.1 : ℝ)+(r : ℝ)*(h e.2.1 : ℝ) at scalar
    change (h e.2.2 : ℝ) • (e.2.2 : ℝ²) =
      (1-(r : ℝ)) • ((h e.1 : ℝ) • (e.1 : ℝ²))+(r : ℝ) • ((h e.2.1 : ℝ) • (e.2.1 : ℝ²)) at vector
    refine ⟨?_,?_,eq_div_iff_mul_eq''.mpr (cancel e.1 e.2.1 e.2.2)⟩
    · apply mul_left_cancel₀ (h e.2.2).ne_zero
      rw [mul_add,acoef,bcoef,mul_one]
      exact scalar.symm
    · apply smul_right_injective ℝ² (h e.2.2).ne_zero
      dsimp only
      rw [smul_add,smul_smul,smul_smul,acoef,bcoef]
      simpa only [smul_smul] using vector.symm
  · intro x y z _ _ _
    simp only [Finset.mem_singleton,div_eq_one]
    exact cancel x y z

end OMA.R_Erdos101_erdos_101_R2_H1_R1
