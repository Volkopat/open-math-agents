import OMAStatements.S_mo_383940
import Mathlib

open OMA.S_mo_383940

lemma dsq (x c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (h : dist x c = r) :
    (x 0 - c 0)^2 + (x 1 - c 1)^2 = r^2 := by
  rw [← h, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma rsq (r : ℝ) (h0 : 0 ≤ r) (h : r^2 = 5) : r = Real.sqrt 5 := by
  rw [← h, Real.sqrt_sq h0]


lemma gen (a1 a2 b1 b2 d1 d2 x y r : ℝ) (h0 : 0 ≤ r)
    (e1 : (a1 - x)^2 + (a2 - y)^2 = r^2) (e2 : (b1 - x)^2 + (b2 - y)^2 = r^2)
    (e3 : (d1 - x)^2 + (d2 - y)^2 = r^2)
    (hD : (b1 - a1) * (d2 - a2) - (b2 - a2) * (d1 - a1) ≠ 0)
    (hv : (a1 - ((b1^2 + b2^2 - a1^2 - a2^2) * (d2 - a2) - (d1^2 + d2^2 - a1^2 - a2^2) * (b2 - a2))
            / (2 * ((b1 - a1) * (d2 - a2) - (b2 - a2) * (d1 - a1))))^2 +
          (a2 - ((b1 - a1) * (d1^2 + d2^2 - a1^2 - a2^2) - (d1 - a1) * (b1^2 + b2^2 - a1^2 - a2^2))
            / (2 * ((b1 - a1) * (d2 - a2) - (b2 - a2) * (d1 - a1))))^2 = 5) :
    r = Real.sqrt 5 := by
  have L1 : 2 * (b1 - a1) * x + 2 * (b2 - a2) * y = b1^2 + b2^2 - a1^2 - a2^2 := by
    linear_combination e1 - e2
  have L2 : 2 * (d1 - a1) * x + 2 * (d2 - a2) * y = d1^2 + d2^2 - a1^2 - a2^2 := by
    linear_combination e1 - e3
  have hD2 : 2 * ((b1 - a1) * (d2 - a2) - (b2 - a2) * (d1 - a1)) ≠ 0 := mul_ne_zero two_ne_zero hD
  have hx : x = ((b1^2 + b2^2 - a1^2 - a2^2) * (d2 - a2) - (d1^2 + d2^2 - a1^2 - a2^2) * (b2 - a2))
            / (2 * ((b1 - a1) * (d2 - a2) - (b2 - a2) * (d1 - a1))) := by
    rw [eq_div_iff hD2]; linear_combination (d2 - a2) * L1 - (b2 - a2) * L2
  have hy : y = ((b1 - a1) * (d1^2 + d2^2 - a1^2 - a2^2) - (d1 - a1) * (b1^2 + b2^2 - a1^2 - a2^2))
            / (2 * ((b1 - a1) * (d2 - a2) - (b2 - a2) * (d1 - a1))) := by
    rw [eq_div_iff hD2]; linear_combination (b1 - a1) * L2 - (d1 - a1) * L1
  apply rsq r h0
  rw [← e1, hx, hy, hv]

lemma rad (f : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (hf : f = ![!₂[(0:ℝ), 0], !₂[(4:ℝ), 0], !₂[(1:ℝ), 3], !₂[(1:ℝ), 1]])
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2)
    (hs : Set.range s.points ⊆ Set.range f) : s.circumradius = Real.sqrt 5 := by
  have hd : ∀ i, dist (s.points i) s.circumcenter = s.circumradius :=
    s.dist_circumcenter_eq_circumradius
  have hm : ∀ i, s.points i ∈ Set.range f := fun i => hs ⟨i, rfl⟩
  have hinj := s.independent.injective
  have n01 : s.points 0 ≠ s.points 1 := fun h => absurd (hinj h) (by decide)
  have n02 : s.points 0 ≠ s.points 2 := fun h => absurd (hinj h) (by decide)
  have n12 : s.points 1 ≠ s.points 2 := fun h => absurd (hinj h) (by decide)
  have h0 : 0 ≤ s.circumradius := s.circumradius_nonneg
  have e0 := hd 0
  have e1 := hd 1
  have e2 := hd 2
  obtain ⟨j0, hj0⟩ := hm 0
  obtain ⟨j1, hj1⟩ := hm 1
  obtain ⟨j2, hj2⟩ := hm 2
  rw [← hj0] at e0 n01 n02
  rw [← hj1] at e1 n01 n12
  rw [← hj2] at e2 n02 n12
  have k01 : j0 ≠ j1 := fun h => n01 (by rw [h])
  have k02 : j0 ≠ j2 := fun h => n02 (by rw [h])
  have k12 : j1 ≠ j2 := fun h => n12 (by rw [h])
  clear hd hm hinj hs n01 n02 n12 hj0 hj1 hj2
  generalize s.circumcenter = c at *
  generalize s.circumradius = r at *
  subst hf
  fin_cases j0 <;> fin_cases j1 <;> fin_cases j2
  all_goals first
    | exact absurd rfl k01 | exact absurd rfl k02 | exact absurd rfl k12
    | exact gen _ _ _ _ _ _ (c 0) (c 1) r h0 (dsq _ _ _ e0) (dsq _ _ _ e1) (dsq _ _ _ e2)
        (by simp <;> norm_num) (by simp <;> norm_num)

lemma dist5 (a b c d : ℝ) (h : (a - c)^2 + (b - d)^2 = 5) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d] = Real.sqrt 5 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs, h]

lemma ne_pt (a b c d : ℝ) (h : a ≠ c ∨ b ≠ d) :
    (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) ≠ !₂[c, d] := by
  intro e
  have e0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) e
  have e1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) e
  simp at e0 e1
  rcases h with h | h
  · exact h e0
  · exact h e1

lemma span_top (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ affineSpan ℝ (Set.range s.points) := by
  rw [s.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)]
  exact AffineSubspace.mem_top _ _ _

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_383940.main) := by
  intro h
  set f : Fin 4 → EuclideanSpace ℝ (Fin 2) :=
    ![!₂[(0:ℝ), 0], !₂[(4:ℝ), 0], !₂[(1:ℝ), 3], !₂[(1:ℝ), 1]] with hf
  have hrad : ∀ s t : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2,
      Set.range s.points ⊆ Set.range f → Set.range t.points ⊆ Set.range f →
      s.circumradius = t.circumradius :=
    fun s t hs ht => (rad f hf s hs).trans (rad f hf t ht).symm
  have i1 : AffineIndependent ℝ ![!₂[(0:ℝ), 0], !₂[(4:ℝ), 0], !₂[(1:ℝ), 3]] := by
    refine EuclideanGeometry.Cospherical.affineIndependent_of_ne
      ⟨!₂[(2:ℝ), 1], Real.sqrt 5, ?_⟩ (ne_pt _ _ _ _ (by norm_num)) (ne_pt _ _ _ _ (by norm_num))
      (ne_pt _ _ _ _ (by norm_num))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl) <;> exact dist5 _ _ _ _ (by norm_num)
  have i2 : AffineIndependent ℝ ![!₂[(0:ℝ), 0], !₂[(4:ℝ), 0], !₂[(1:ℝ), 1]] := by
    refine EuclideanGeometry.Cospherical.affineIndependent_of_ne
      ⟨!₂[(2:ℝ), -1], Real.sqrt 5, ?_⟩ (ne_pt _ _ _ _ (by norm_num)) (ne_pt _ _ _ _ (by norm_num))
      (ne_pt _ _ _ _ (by norm_num))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl) <;> exact dist5 _ _ _ _ (by norm_num)
  let s1 : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨_, i1⟩
  let s2 : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨_, i2⟩
  have c1 : s1.circumcenter = !₂[(2:ℝ), 1] := by
    refine (s1.eq_circumcenter_of_dist_eq (span_top s1 _) (r := Real.sqrt 5) ?_).symm
    intro i; fin_cases i <;> exact dist5 _ _ _ _ (by norm_num)
  have c2 : s2.circumcenter = !₂[(2:ℝ), -1] := by
    refine (s2.eq_circumcenter_of_dist_eq (span_top s2 _) (r := Real.sqrt 5) ?_).symm
    intro i; fin_cases i <;> exact dist5 _ _ _ _ (by norm_num)
  have r1 : Set.range s1.points ⊆ Set.range f := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have r2 : Set.range s2.points ⊆ Set.range f := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
  have key := h 2 (Set.range f) (Set.finite_range f) hrad s1 s2 r1 r2
  rw [c1, c2] at key
  exact ne_pt _ _ _ _ (by norm_num) key
