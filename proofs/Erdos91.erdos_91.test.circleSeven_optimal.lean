import FormalConjectures.ErdosProblems.«91»
/-! # A polynomial bound for planar two-distance sets -/
-- Credit: @steveDOTdigital
open Finset EuclideanGeometry
namespace OMA.Heptagon
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


private noncomputable def rad : ℝ := 1 / (2 * Real.sin (Real.pi / 7))
private noncomputable def angle (k : ℕ) : ℝ := 2 * Real.pi * k / 7
private noncomputable def vertex (k : ℕ) : ℝ² :=
  !₂[rad * Real.cos (angle k) + rad * Real.cos (Real.pi / 7),
     rad * Real.sin (angle k) + rad * Real.sin (4 * Real.pi / 7)]
private noncomputable def chord (k : ℕ) : ℝ := 2 * rad * Real.sin (Real.pi * k / 7)
private theorem chord_pos {k : ℕ} (hk : 0 < k) (hk' : k < 7) : 0 < chord k := by
  have hr : 0 < Real.sin (Real.pi / 7) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hl : (k : ℝ) < 7 := by exact_mod_cast hk'
  have hs := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi * k / 7) (by positivity) (by nlinarith [mul_lt_mul_of_pos_left hl Real.pi_pos])
  dsimp [chord, rad]
  positivity
private theorem vertex_dist {i j : ℕ} (hij : i < j) (hj : j < 7) :
    dist (vertex i) (vertex j) = chord (j-i) := by
  apply (sq_eq_sq₀ dist_nonneg (chord_pos (by omega : 0 < j-i) (by omega)).le).mp
  let t := Real.pi * (↑(j-i) : ℝ) / 7
  have hab : angle j - angle i = 2 * t := by
    dsimp [angle,t]; rw [Nat.cast_sub hij.le]; ring
  have hcos := Real.cos_sub (angle j) (angle i)
  rw [hab, Real.cos_two_mul_eq_one_sub] at hcos
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [vertex, Real.dist_eq, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, chord]
  change (_ + _) = (2 * rad * Real.sin t)^2
  linear_combination (norm := ring_nf) rad^2 * (Real.sin_sq_add_cos_sq (angle i)) +
    rad^2 * (Real.sin_sq_add_cos_sq (angle j)) + 2*rad^2*hcos
private theorem chord_mem {k : ℕ} (hk : 0 < k) (hk' : k < 7) :
    chord k ∈ ({chord 1, chord 2, chord 3} : Finset ℝ) := by
  classical
  have hs (n m : ℕ) (hnm : n+m=7) : chord n = chord m := by
    have he : Real.pi * n / 7 = Real.pi - Real.pi * m / 7 := by
      have hm : (n : ℝ)+m=7 := by exact_mod_cast hnm
      linear_combination Real.pi / 7 * hm
    simp only [chord, he, Real.sin_pi_sub]
  interval_cases k <;> simp [hs 4 3 (by decide),hs 5 2 (by decide),hs 6 1 (by decide)]
private theorem circle_card : Erdos91.circleSeven.card = 7 := by
  change ((range 7).image vertex).card = 7
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  by_contra hn
  wlog h : i < j generalizing i j
  · exact this hj hi he.symm (Ne.symm hn) (by omega)
  have hpos := chord_pos (k := j-i) (by omega) (by have := mem_range.mp hj; omega)
  rw [← vertex_dist h (mem_range.mp hj), he, dist_self] at hpos
  exact (lt_irrefl _ hpos)

private theorem circle_upper : distinctDistances Erdos91.circleSeven ≤ 3 := by
  classical
  have sub : distanceSet Erdos91.circleSeven ⊆ {chord 1,chord 2,chord 3} := by
    intro t ht
    obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hp,hq,hne⟩ := Finset.mem_offDiag.mp hpq
    change p ∈ (range 7).image vertex at hp
    change q ∈ (range 7).image vertex at hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    have h₁ := mem_range.mp hi
    have h₂ := mem_range.mp hj
    change dist (vertex i) (vertex j) ∈ _
    rcases lt_trichotomy i j with h | h | h
    · rw [vertex_dist h h₂]; exact chord_mem (by omega) (by omega)
    · exact False.elim (hne (congrArg vertex h))
    · rw [dist_comm, vertex_dist h h₁]; exact chord_mem (by omega) (by omega)
  exact (Finset.card_le_card sub).trans Finset.card_le_three

theorem optimal : Erdos91.IsOptimal Erdos91.circleSeven 7 := by
  classical
  refine ⟨circle_card, le_antisymm ?_ (Nat.sInf_le ⟨_,circle_card,rfl⟩)⟩
  apply le_trans circle_upper
  apply le_csInf
  · exact ⟨_, Erdos91.circleSeven, circle_card, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact seven_lower A hA

end OMA.Heptagon

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.circleSeven_optimal := OMA.Heptagon.optimal
