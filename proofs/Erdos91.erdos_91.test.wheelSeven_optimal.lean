import FormalConjectures.ErdosProblems.«91»
/-! # A polynomial bound for planar two-distance sets -/
-- Credit: @steveDOTdigital
open Finset EuclideanGeometry
namespace OMA.Wheel
private theorem quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ i j, i ≠ j → let d := (x i - x j)^2 + (y i - y j)^2; d = a ∨ d = b) :
    Fintype.card ι ≤ 6 := by
  classical
  -- Seven points admit a nonzero relation annihilating the six quadratic monomials.
  let v (i : ι) : Fin 6 → ℝ := ![1, x i, y i, x i ^ 2, x i * y i, y i ^ 2]
  by_contra! hcard
  have hdep : ¬ LinearIndependent ℝ v := fun hl => by
    have := hl.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let L (f : ι → ℝ) := ∑ i, c i * f i
  let T (F : ι → ι → ℝ) := L (fun i => L (F i))
  let prod (f g : ι → ℝ) (i j : ι) := f i * g j
  have hL (k : Fin 6) : L (fun i => v i k) = 0 := by
    simpa [L, Finset.sum_apply] using congrFun hc k
  have hAdd (F G : ι → ι → ℝ) : T (F + G) = T F + T G := by
    simp [T, L, mul_add, sum_add_distrib]
  have hProd (f g : ι → ℝ) : T (prod f g) = L f * L g := by
    simp only [T, L, prod, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  let K (i j : ι) := (((x i-x j)^2+(y i-y j)^2)-a)*(((x i-x j)^2+(y i-y j)^2)-b)
  let q (i : ι) := x i^2 + y i^2
  let one : ι → ℝ := fun _ => 1
  have hq : L q = 0 := by
    have e : L q = L (fun i => x i^2) + L (fun i => y i^2) := by simp [L,q,mul_add,sum_add_distrib]
    rw [e, show L (fun i => x i^2) = 0 from hL 3, show L (fun i => y i^2) = 0 from hL 5, add_zero]
  -- Every summand separates, with a factor of degree at most two in one point.
  have he : K = prod (fun i => q i^2 - (a+b)*q i + a*b) one +
      prod one (fun i => q i^2 - (a+b)*q i) +
      prod (fun i => 2*q i) q +
      prod (fun i => (a+b-4*q i)*x i) x +
      prod x (fun i => (a+b-4*q i)*x i) +
      prod (fun i => (a+b-4*q i)*y i) y +
      prod y (fun i => (a+b-4*q i)*y i) +
      prod (fun i => 4*x i^2) (fun i => x i^2) +
      prod (fun i => 8*x i*y i) (fun i => x i*y i) +
      prod (fun i => 4*y i^2) (fun i => y i^2) := by
    funext i j
    simp only [K, prod, q, one, Pi.add_apply]
    ring
  have hzero : T K = 0 := by
    rw [he]
    simp only [hAdd, hProd, hq, show L one = 0 from hL 0,
      show L x = 0 from hL 1, show L y = 0 from hL 2,
      show L (fun i => x i^2) = 0 from hL 3, show L (fun i => x i*y i) = 0 from hL 4,
      show L (fun i => y i^2) = 0 from hL 5, zero_mul, mul_zero, add_zero]
  have hdiag (i j : ι) : K i j = if i = j then a*b else 0 := by
    split_ifs with hij
    · subst j; simp [K]
    · rcases h i j hij with hh | hh <;> simp [K, hh]
  have hpos : 0 < T K := by
    have eqn : T K = ∑ i, c i ^ 2 * (a*b) := by
      simp [T, L, hdiag, mul_ite, sq, mul_assoc]
    rw [eqn]
    exact Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, mem_univ _, by positivity⟩
  linarith
private theorem cover {s : Finset ℝ} (hc : s.card ≤ 2) (hp : ∀ t ∈ s, 0 < t) :
    ∃ r > 0, ∃ u > 0, ∀ t ∈ s, t = r ∨ t = u := by
  rcases Nat.eq_zero_or_pos s.card with hz | hz
  · exact ⟨1, one_pos, 1, one_pos, by simp [Finset.card_eq_zero.mp hz]⟩
  by_cases ho : s.card = 1
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp ho
    subst s
    exact ⟨r, hp r (by simp), r, hp r (by simp), by simp⟩
  obtain ⟨r,u,_,hr⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
  subst s
  exact ⟨r,hp r (by simp),u,hp u (by simp),by simp⟩

private theorem seven_lower (A : Finset ℝ²) (hc : A.card = 7) : 3 ≤ distinctDistances A := by
  classical
  by_contra! hsmall
  have hp (t : ℝ) (ht : t ∈ distanceSet A) : 0 < t := by
    obtain ⟨⟨p,q⟩,h,rfl⟩ := Finset.mem_image.mp ht
    exact dist_pos.mpr (Finset.mem_offDiag.mp h).2.2
  obtain ⟨r,hr,u,hu,h⟩ := cover (s := distanceSet A) (by change distinctDistances A ≤ 2; omega) hp
  have hsize := quadratic_bound (ι := A) (fun p => p.val 0) (fun p => p.val 1)
    (r^2) (u^2) (sq_pos_of_pos hr) (sq_pos_of_pos hu) (by
      intro i j hij
      have hd : dist i.val j.val ∈ distanceSet A := Finset.mem_image.mpr
        ⟨(i.val,j.val), Finset.mem_offDiag.mpr ⟨i.property,j.property,fun e => hij (Subtype.ext e)⟩,rfl⟩
      have hsq : dist i.val j.val ^ 2 = (i.val 0-j.val 0)^2+(i.val 1-j.val 1)^2 := by
        rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
        simp [Real.dist_eq, sq_abs]
      rcases h _ hd with e | e <;> rw [e] at hsq
      · exact Or.inl hsq.symm
      · exact Or.inr hsq.symm)
  simpa [hc] using hsize

private def xy : Fin 7 → ℤ × ℤ := ![(2,1),(4,1),(3,2),(1,2),(0,1),(1,0),(3,0)]
private noncomputable def pt (i : Fin 7) : ℝ² :=
  !₂[(xy i).1 / (2 : ℝ), ((xy i).2 : ℝ) * Real.sqrt 3 / 2]
private def sq4 (i j : Fin 7) : ℤ :=
  ((xy i).1 - (xy j).1)^2 + 3 * ((xy i).2 - (xy j).2)^2
private theorem wheel_enum : Erdos91.wheelSeven = Finset.univ.image pt := by
  have hu : (Finset.univ : Finset (Fin 7)) = {0,1,2,3,4,5,6} := by decide
  rw [hu]
  simp only [Finset.image_insert, Finset.image_singleton]
  have h0 : xy 0 = (2,1) := rfl
  have h1 : xy 1 = (4,1) := rfl
  have h2 : xy 2 = (3,2) := rfl
  have h3 : xy 3 = (1,2) := rfl
  have h4 : xy 4 = (0,1) := rfl
  have h5 : xy 5 = (1,0) := rfl
  have h6 : xy 6 = (3,0) := rfl
  norm_num [Erdos91.wheelSeven, pt, h0, h1, h2, h3, h4, h5, h6, mul_comm (2 : ℝ)]
private theorem pt_inj : Function.Injective pt := by
  have hxy : ∀ i j : Fin 7, xy i = xy j → i = j := by decide
  intro i j e
  apply hxy
  have hx := congrArg (fun p : ℝ² => p 0) e
  have hy := congrArg (fun p : ℝ² => p 1) e
  simp [pt] at hx hy
  apply Prod.ext
  · exact_mod_cast hx
  · exact hy
private theorem sqdist (i j : Fin 7) :
    4 * dist (pt i) (pt j)^2 = ((sq4 i j : ℤ) : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [pt, Real.dist_eq, sq_abs, sq4]
  ring_nf
  norm_num
  ring
private theorem upper : distinctDistances Erdos91.wheelSeven ≤ 3 := by
  classical
  have hcases : ∀ i j : Fin 7, i ≠ j → sq4 i j = 4 ∨ sq4 i j = 12 ∨ sq4 i j = 16 := by decide
  have hsub : distanceSet Erdos91.wheelSeven ⊆ {1,Real.sqrt 3,2} := by
    intro t ht
    obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hp,hq,hne⟩ := Finset.mem_offDiag.mp hpq
    rw [wheel_enum] at hp hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    have hs := sqdist i j
    have h₀ := dist_nonneg (x := pt i) (y := pt j)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcases i j (fun h => hne (congrArg pt h)) with h | h | h <;> rw [h] at hs <;> norm_num at hs
    · left; rcases hs with h | h <;> linarith
    · right; left; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3,
        sq_nonneg (dist (pt i) (pt j) - Real.sqrt 3)]
    · right; right; nlinarith
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

theorem optimal : Erdos91.IsOptimal Erdos91.wheelSeven 7 := by
  classical
  have hc : Erdos91.wheelSeven.card = 7 := by
    rw [wheel_enum, Finset.card_image_of_injective _ pt_inj]; simp
  refine ⟨hc, le_antisymm ?_ (Nat.sInf_le ⟨_,hc,rfl⟩)⟩
  apply le_trans upper
  apply le_csInf
  · exact ⟨_, Erdos91.wheelSeven, hc, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact seven_lower A hA

end OMA.Wheel

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.wheelSeven_optimal := OMA.Wheel.optimal
