import OMAReductions.R_Erdos101_erdos_101_R1

/-!
# Four-point lines on reducible curves

The component argument in Elekes and Szabó, *On Triple Lines and Cubic
Curves*, Theorem 4.3, reduces the problem to triple lines on irreducible
curves. Here the degree bound is uniform in the coefficients, repeated factors
are allowed, and a point may lie on several components.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H2_R1

open EuclideanGeometry MvPolynomial
open scoped Classical Pointwise

/-- The single-component case for irreducible curves of degree at least four. -/
def H1 : Prop :=
  ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F : MvPolynomial (Fin 2) ℝ, Irreducible F → 4 ≤ F.totalDegree → F.totalDegree ≤ d →
        (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (n : ℝ)^2

/-- The mixed-component triple-line estimate. The first two nonlinear
irreducible factors are distinct up to multiplication by a unit.
The third may be either of them or a third component. -/
def H2 : Prop :=
  ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F G H : MvPolynomial (Fin 2) ℝ,
        Irreducible F → Irreducible G → Irreducible H → ¬ Associated F G →
        2 ≤ F.totalDegree → 2 ≤ G.totalDegree → 2 ≤ H.totalDegree →
        F.totalDegree ≤ d → G.totalDegree ≤ d → H.totalDegree ≤ d →
        ∀ A : Finset (AffineSubspace ℝ ℝ²),
          (∀ L ∈ A, ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
            eval (fun i => x i) F = 0 ∧ eval (fun i => y i) G = 0 ∧
            eval (fun i => z i) H = 0 ∧ line[ℝ,x,y] = L ∧ z ∈ L) →
          (A.card : ℝ) ≤ ε * (n : ℝ)^2

/-- A nonconstant irreducible factor consumes at least one unit of total degree. -/
lemma irreducible_degree_pos {F : MvPolynomial (Fin 2) ℝ} (h : Irreducible F) :
    0 < F.totalDegree := by
  by_contra! hdeg
  have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
  have hc : F.coeff 0 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at he
    exact h.ne_zero he
  exact h.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)

lemma count_factors_le_degree (s : Multiset (MvPolynomial (Fin 2) ℝ))
    (hs : ∀ F ∈ s, Irreducible F) : s.card ≤ s.prod.totalDegree := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons F s ih =>
    have hF := hs F (by simp)
    have hr : ∀ G ∈ s, Irreducible G := fun G hG => hs G (by simp [hG])
    have hn : s.prod ≠ 0 := fun he => (hr 0 (Multiset.prod_eq_zero_iff.mp he)).ne_zero rfl
    rw [Multiset.card_cons, Multiset.prod_cons, totalDegree_mul_of_isDomain hF.ne_zero hn]
    have := irreducible_degree_pos hF
    have := ih hr
    omega

/-- The zero set of a nonzero polynomial of degree d is covered by at most
d irreducible factors. Their degrees and their number are controlled even
when the input has repeated factors. -/
lemma component_cover {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0) :
    ∃ C : Finset (MvPolynomial (Fin 2) ℝ), C.card ≤ F.totalDegree ∧
      (∀ G ∈ C, Irreducible G ∧ G.totalDegree ≤ F.totalDegree) ∧
      ∀ p : ℝ², eval (fun i => p i) F = 0 → ∃ G ∈ C, eval (fun i => p i) G = 0 := by
  classical
  obtain ⟨s, hprime, hassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors F hF
  have hirr : ∀ G ∈ s, Irreducible G := fun G hG => (hprime G hG).irreducible
  refine ⟨s.toFinset, (Multiset.toFinset_card_le _).trans ((count_factors_le_degree s hirr).trans
    (totalDegree_le_of_dvd_of_isDomain hassoc.dvd hF)), ?_, ?_⟩
  · intro G hG
    have hm := Multiset.mem_toFinset.mp hG
    exact ⟨hirr G hm,
      totalDegree_le_of_dvd_of_isDomain ((Multiset.dvd_prod hm).trans hassoc.dvd) hF⟩
  · intro p hp
    let e := eval (fun i => p i)
    have hz : e s.prod = 0 := (Associated.map e hassoc).eq_zero_iff.mpr hp
    rw [← Multiset.prod_hom s e] at hz
    obtain ⟨G, hG, he⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
    exact ⟨G, Multiset.mem_toFinset.mpr hG, he⟩

lemma affine_polynomial_form {F : MvPolynomial (Fin 2) ℝ} (hd : F.totalDegree ≤ 1) :
    ∃ a b c : ℝ, F = C c + C a * X 0 + C b * X 1 := by
  classical
  let u : Fin 2 →₀ ℕ := Finsupp.single 0 1
  let v : Fin 2 →₀ ℕ := Finsupp.single 1 1
  have hu : u ≠ 0 := by simp [u]
  have hv : v ≠ 0 := by simp [v]
  have huv : u ≠ v := by
    intro he
    have := DFunLike.congr_fun he 0
    simp [u,v] at this
  refine ⟨F.coeff u, F.coeff v, F.coeff 0, ?_⟩
  apply MvPolynomial.ext
  intro w
  rw [C_mul_X_eq_monomial, C_mul_X_eq_monomial]
  simp only [C_apply, coeff_add, coeff_monomial]
  change F.coeff w = (if 0 = w then F.coeff 0 else 0) +
    (if u = w then F.coeff u else 0) + (if v = w then F.coeff v else 0)
  by_cases h0 : w = 0
  · simp [h0, hu, hv]
  by_cases h1 : w = u
  · simp [h1,hu.symm,huv.symm]
  by_cases h2 : w = v
  · simp [h2,hv.symm,huv]
  simp only [if_neg (Ne.symm h0), if_neg (Ne.symm h1), if_neg (Ne.symm h2), add_zero]
  by_contra hne
  have he := (le_totalDegree (mem_support_iff.mpr hne)).trans hd
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at he
  have hcases : (w 0 = 0 ∧ w 1 = 0) ∨ (w 0 = 1 ∧ w 1 = 0) ∨ (w 0 = 0 ∧ w 1 = 1) := by omega
  rcases hcases with h | h | h
  · apply h0
    ext i
    fin_cases i <;> simp [h]
  · apply h1
    ext i
    fin_cases i <;> simp [u,h]
  · apply h2
    ext i
    fin_cases i <;> simp [v,h]

/-- The points on a single linear factor form a collinear set, including
the case of a horizontal or vertical component. -/
lemma linear_zeros_collinear {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0)
    (hd : F.totalDegree ≤ 1) :
    Collinear ℝ {p : ℝ² | eval (fun i => p i) F = 0} := by
  obtain ⟨a,b,c,rfl⟩ := affine_polynomial_form hd
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      have hc : c ≠ 0 := by rintro rfl; simp at hF
      exact ⟨0, 0, fun p hp => False.elim (hc (by simpa using hp))⟩
    refine ⟨!₂[0,-c/b], !₂[1,0], ?_⟩
    intro p hp
    have h : c + b*p 1 = 0 := by simpa using hp
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp
      exact (eq_div_iff hb).mpr (by linarith)
  · refine ⟨!₂[-c/a,0], !₂[-b/a,1], ?_⟩
    intro p hp
    have h : c + a * p 0 + b * p 1 = 0 := by simpa using hp
    refine ⟨p 1, ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      linarith
    · simp

lemma linear_component_card {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0)
    (hd : F.totalDegree ≤ 1) {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) :
    (S.filter (fun p => eval (fun i => p i) F = 0)).card ≤ 4 := by
  by_contra! h
  obtain ⟨T, hT, hsize⟩ := Finset.exists_subset_card_eq
    (show 5 ≤ (S.filter (fun p => eval (fun i => p i) F = 0)).card by omega)
  apply hcap (T : Set ℝ²) (Finset.coe_subset.mpr (hT.trans (Finset.filter_subset ..)))
    T.finite_toSet (by simpa using hsize)
  exact Collinear.subset (fun p hp => (Finset.mem_filter.mp (hT hp)).2) (linear_zeros_collinear hF hd)

/-- A union of k linear factors contains at most 4k points of the configuration. -/
lemma linear_union_card (C : Finset (MvPolynomial (Fin 2) ℝ)) (S : Finset ℝ²)
    (hcap : NonCollinearFor 5 (S : Set ℝ²)) (hC : ∀ G ∈ C, G ≠ 0 ∧ G.totalDegree ≤ 1) :
    (C.biUnion (fun G => S.filter (fun p => eval (fun i => p i) G = 0))).card ≤ C.card * 4 := by
  calc
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ C, 4 := Finset.sum_le_sum (fun G hG =>
      linear_component_card (hC G hG).1 (hC G hG).2 hcap)
    _ = _ := by simp

/-- An arbitrary cubic together with k straight-line components supports only
linearly many four-point lines, with an explicit bound. -/
theorem cubic_and_linear_components (S : Finset ℝ²) (F : MvPolynomial (Fin 2) ℝ)
    (C : Finset (MvPolynomial (Fin 2) ℝ)) (hcap : NonCollinearFor 5 (S : Set ℝ²))
    (hF : F ≠ 0) (hd : F.totalDegree ≤ 3) (hC : ∀ G ∈ C, G ≠ 0 ∧ G.totalDegree ≤ 1)
    (hcover : ∀ p ∈ S, eval (fun i => p i) F = 0 ∨ ∃ G ∈ C, eval (fun i => p i) G = 0) :
    3 * (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤
      3 * F.totalDegree + (C.card * 4) * (S.card - 1) := by
  have hsub : S.filter (fun p => eval (fun i => p i) F ≠ 0) ⊆
      C.biUnion (fun G => S.filter (fun p => eval (fun i => p i) G = 0)) := by
    intro p hp
    obtain ⟨hpS, hn⟩ := Finset.mem_filter.mp hp
    obtain ⟨G, hG, hzero⟩ := (hcover p hpS).resolve_left hn
    exact Finset.mem_biUnion.mpr ⟨G,hG,Finset.mem_filter.mpr ⟨hpS,hzero⟩⟩
  exact (OMA.R_Erdos101_erdos_101_R1.four_lines_near_cubic S F hF hd).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans
      (linear_union_card C S hcap hC))) _)

/-- Discarding at most 4d points leaves a cover by at most d nonlinear
irreducible factors. Its members need not have disjoint zero sets. -/
lemma nonlinear_cover {F : MvPolynomial (Fin 2) ℝ} (hF : F ≠ 0) (S : Finset ℝ²)
    (hcap : NonCollinearFor 5 (S : Set ℝ²)) (hS : ∀ p ∈ S, eval (fun i => p i) F = 0) :
    ∃ D : Finset (MvPolynomial (Fin 2) ℝ), ∃ T : Finset ℝ², T ⊆ S ∧
      D.card ≤ F.totalDegree ∧ (S \ T).card ≤ F.totalDegree * 4 ∧
      (∀ G ∈ D, Irreducible G ∧ 2 ≤ G.totalDegree ∧ G.totalDegree ≤ F.totalDegree) ∧
      ∀ p ∈ T, ∃ G ∈ D, eval (fun i => p i) G = 0 := by
  obtain ⟨C,hnum,hC,hzero⟩ := component_cover hF
  let D := C.filter (fun G => 2 ≤ G.totalDegree)
  let E := C.filter (fun G => G.totalDegree ≤ 1)
  let T := S.filter (fun p => ∃ G ∈ D, eval (fun i => p i) G = 0)
  refine ⟨D,T,Finset.filter_subset ..,(Finset.card_filter_le ..).trans hnum,?_,?_,
    fun _ hp => (Finset.mem_filter.mp hp).2⟩
  · have hsub : S \ T ⊆ E.biUnion (fun G => S.filter (fun p => eval (fun i => p i) G = 0)) := by
      intro p hp
      obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨G,hG,he⟩ := hzero p (hS p hpS)
      have hd : G.totalDegree ≤ 1 := by
        by_contra! hhigh
        exact hpT (Finset.mem_filter.mpr ⟨hpS,G,Finset.mem_filter.mpr ⟨hG,hhigh⟩,he⟩)
      exact Finset.mem_biUnion.mpr
        ⟨G,Finset.mem_filter.mpr ⟨hG,hd⟩,Finset.mem_filter.mpr ⟨hpS,he⟩⟩
    have hline : ∀ G ∈ E, G ≠ 0 ∧ G.totalDegree ≤ 1 := by
      intro G hG
      obtain ⟨hs,hd⟩ := Finset.mem_filter.mp hG
      exact ⟨(hC G hs).1.ne_zero,hd⟩
    exact (Finset.card_le_card hsub).trans ((linear_union_card E S hcap hline).trans
      (Nat.mul_le_mul_right 4 ((Finset.card_filter_le ..).trans hnum)))
  · intro G hG
    obtain ⟨hs,hd⟩ := Finset.mem_filter.mp hG
    exact ⟨(hC G hs).1,hd,(hC G hs).2⟩

/-- Every surviving four-point line belongs to one component, or has three
distinct marked points on components whose first two are nonassociate. -/
lemma classify_line {T : Finset ℝ²} {D : Finset (MvPolynomial (Fin 2) ℝ)}
    (hcover : ∀ p ∈ T, ∃ G ∈ D, eval (fun i => p i) G = 0)
    {L : AffineSubspace ℝ ℝ²} (hL : L ∈ linesWithPointsFor 4 (T : Set ℝ²)) :
    (∃ G ∈ D, L ∈ linesWithPointsFor 4
      (↑(T.filter (fun p => eval (fun i => p i) G = 0)) : Set ℝ²)) ∨
    (∃ F ∈ D, ∃ G ∈ D, ∃ H ∈ D, ¬ Associated F G ∧
      ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
        eval (fun i => x i) F = 0 ∧ eval (fun i => y i) G = 0 ∧ eval (fun i => z i) H = 0 ∧
        line[ℝ,x,y] = L ∧ z ∈ L) := by
  let U := T.filter (fun p => p ∈ L)
  have hsize : U.card = 4 := OMA.R_Erdos101_erdos_101_R1.four_points hL
  by_cases hall : ∃ G ∈ D, ∀ p ∈ U, eval (fun i => p i) G = 0
  · obtain ⟨G,hG,hall⟩ := hall
    left
    refine ⟨G,hG,OMA.R_Erdos101_erdos_101_R1.mem_after_restriction (Finset.filter_subset ..) hL ?_⟩
    exact fun p hp hpL => Finset.mem_filter.mpr ⟨hp,hall p (Finset.mem_filter.mpr ⟨hp,hpL⟩)⟩
  · right
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
    obtain ⟨hxT,hxL⟩ := Finset.mem_filter.mp hx
    obtain ⟨F,hF,hFx⟩ := hcover x hxT
    have hmiss : ∃ y ∈ U, eval (fun i => y i) F ≠ 0 := by
      by_contra! h
      exact hall ⟨F,hF,h⟩
    obtain ⟨y,hy,hFy⟩ := hmiss
    obtain ⟨hyT,hyL⟩ := Finset.mem_filter.mp hy
    obtain ⟨G,hG,hGy⟩ := hcover y hyT
    have hFG : ¬ Associated F G := fun h => hFy ((Associated.map (eval (fun i => y i)) h).eq_zero_iff.mpr hGy)
    have hxy : x ≠ y := by rintro rfl; exact hFy hFx
    have hy' := Finset.mem_erase.mpr ⟨hxy.symm,hy⟩
    have hleft : ((U.erase x).erase y).card = 2 := by
      rw [Finset.card_erase_of_mem hy',Finset.card_erase_of_mem hx,hsize]
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < ((U.erase x).erase y).card by omega)
    obtain ⟨hzy,hz'⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzx,hz''⟩ := Finset.mem_erase.mp hz'
    obtain ⟨hzT,hzL⟩ := Finset.mem_filter.mp hz''
    obtain ⟨H,hH,hHz⟩ := hcover z hzT
    exact ⟨F,hF,G,hG,H,hH,hFG,x,hxT,y,hyT,z,hzT,hxy,hzx,hzy,hFx,hGy,hHz,
      OMA.R_Erdos101_erdos_101_R1.line_through hL hxL hyL hxy,hzL⟩

/-- For degrees at most three the unconditional bound is absorbed by the same
quadratic error used for the higher irreducible degrees. -/
lemma single_component_estimate (h₁ : H1) (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset ℝ², S.card ≤ n →
      NonCollinearFor 5 (S : Set ℝ²) → ∀ F : MvPolynomial (Fin 2) ℝ,
        Irreducible F → F.totalDegree ≤ d → (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ η * (n : ℝ)^2 := by
  obtain ⟨N,hN⟩ := h₁ d η hη
  obtain ⟨K,hK⟩ := exists_nat_gt (3/η)
  refine ⟨max N (max 1 K), ?_⟩
  intro n hn S hSn hcap F hF hd hzero
  by_cases hlow : F.totalDegree ≤ 3
  · have hnK : (K : ℝ) ≤ n := by exact_mod_cast (show K ≤ n by omega)
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hconst : (3 : ℝ) ≤ η * K := by linarith [(div_lt_iff₀ hη).mp hK]
    calc
      _ ≤ (3 : ℝ) := by exact_mod_cast
        (OMA.R_Erdos101_erdos_101_R1.four_lines_on_cubic S F hF.ne_zero hlow hzero).trans hlow
      _ ≤ η * K := hconst
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hnK.trans (by nlinarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)) (sub_nonneg.mpr hn₁)]))
        hη.le
  · exact hN n ((le_max_left ..).trans hn) S hSn hcap F hF (by omega) hd hzero

/-- A cover by at most d nonlinear components needs at most d one-component
families and d cubed ordered families of mixed triple lines. -/
lemma nonlinear_estimate (h₁ : H1) (h₂ : H2) (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T : Finset ℝ², T.card ≤ n →
      NonCollinearFor 5 (T : Set ℝ²) → ∀ D : Finset (MvPolynomial (Fin 2) ℝ), D.card ≤ d →
      (∀ G ∈ D, Irreducible G ∧ 2 ≤ G.totalDegree ∧ G.totalDegree ≤ d) →
      (∀ p ∈ T, ∃ G ∈ D, eval (fun i => p i) G = 0) →
      ((linesWithPointsFor 4 (T : Set ℝ²)).ncard : ℝ) ≤
        ((d + d^3 : ℕ) : ℝ) * (η * (n : ℝ)^2) := by
  classical
  obtain ⟨N₁,hsingle⟩ := single_component_estimate h₁ d η hη
  obtain ⟨N₂,hmixed⟩ := h₂ d η hη
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn T hT hcap D hnum hD hcover
  let A := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite T).toFinset
  let M (G : MvPolynomial (Fin 2) ℝ) :=
    (OMA.R_Erdos101_erdos_101_R1.four_lines_finite (T.filter (fun p => eval (fun i => p i) G = 0))).toFinset
  let W := D ×ˢ D ×ˢ D
  let B (c : MvPolynomial (Fin 2) ℝ × MvPolynomial (Fin 2) ℝ × MvPolynomial (Fin 2) ℝ) :=
    A.filter (fun L => ¬ Associated c.1 c.2.1 ∧ ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T,
      x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ eval (fun i => x i) c.1 = 0 ∧ eval (fun i => y i) c.2.1 = 0 ∧
      eval (fun i => z i) c.2.2 = 0 ∧ line[ℝ,x,y] = L ∧ z ∈ L)
  have hsub : A ⊆ D.biUnion M ∪ W.biUnion B := by
    intro L hL
    rcases classify_line hcover ((OMA.R_Erdos101_erdos_101_R1.four_lines_finite T).mem_toFinset.mp hL) with h | h
    · obtain ⟨G,hG,hL'⟩ := h
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨G,hG,
        (OMA.R_Erdos101_erdos_101_R1.four_lines_finite _).mem_toFinset.mpr hL'⟩)
    · obtain ⟨F,hF,G,hG,H,hH,hobs⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(F,G,H),
        Finset.mem_product.mpr ⟨hF, Finset.mem_product.mpr ⟨hG,hH⟩⟩,
        Finset.mem_filter.mpr ⟨hL,hobs⟩⟩)
  let b := η * (n : ℝ)^2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hm (G) (hG : G ∈ D) : ((M G).card : ℝ) ≤ b := by
    rw [show (M G).card = (linesWithPointsFor 4
      (↑(T.filter (fun p => eval (fun i => p i) G = 0)) : Set ℝ²)).ncard from
      (Set.ncard_eq_toFinset_card _ (OMA.R_Erdos101_erdos_101_R1.four_lines_finite _)).symm]
    exact hsingle n ((le_max_left ..).trans hn) _ ((Finset.card_filter_le ..).trans hT)
      (NonCollinearFor.subset (Finset.coe_subset.mpr (Finset.filter_subset ..)) hcap)
      G (hD G hG).1 (hD G hG).2.2 (fun _ hp => (Finset.mem_filter.mp hp).2)
  have ht (c) (hc : c ∈ W) : ((B c).card : ℝ) ≤ b := by
    obtain ⟨hF,hGH⟩ := Finset.mem_product.mp hc
    obtain ⟨hG,hH⟩ := Finset.mem_product.mp hGH
    by_cases he : Associated c.1 c.2.1
    · have hnil : B c = ∅ := Finset.filter_eq_empty_iff.mpr (fun _ _ h => h.1 he)
      simpa [hnil] using hb
    exact hmixed n ((le_max_right ..).trans hn) T hT hcap c.1 c.2.1 c.2.2
      (hD _ hF).1 (hD _ hG).1 (hD _ hH).1 he
      (hD _ hF).2.1 (hD _ hG).2.1 (hD _ hH).2.1
      (hD _ hF).2.2 (hD _ hG).2.2 (hD _ hH).2.2 (B c)
      (fun _ h => (Finset.mem_filter.mp h).2.2)
  have hcount : A.card ≤ (∑ G ∈ D, (M G).card) + ∑ c ∈ W, (B c).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le ..).trans
      (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le))
  have hc : D.card + W.card ≤ d + d^3 := by
    have hw : W.card = D.card^3 := by simp [W]; ring
    rw [hw]
    exact Nat.add_le_add hnum (Nat.pow_le_pow_left hnum 3)
  rw [Set.ncard_eq_toFinset_card _ (OMA.R_Erdos101_erdos_101_R1.four_lines_finite T)]
  calc
    (A.card : ℝ) ≤ (∑ G ∈ D, ((M G).card : ℝ)) + ∑ c ∈ W, ((B c).card : ℝ) := by exact_mod_cast hcount
    _ ≤ (∑ _ ∈ D, b) + ∑ _ ∈ W, b := add_le_add (Finset.sum_le_sum hm) (Finset.sum_le_sum ht)
    _ = ((D.card + W.card : ℕ) : ℝ) * b := by simp [add_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hb

/-- A dense family of triple lines forces three nonlinear irreducible curves
onto a common cubic in the algebraic form of Elekes–Szabó, Theorem 4.1.
This lemma takes that rigidity assertion as an explicit premise and derives
both incidence estimates, allowing the three factors to coincide. -/
theorem estimates_of_triple_rigidity
    (rigidity : ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F G H : MvPolynomial (Fin 2) ℝ,
        Irreducible F → Irreducible G → Irreducible H →
        2 ≤ F.totalDegree → 2 ≤ G.totalDegree → 2 ≤ H.totalDegree →
        F.totalDegree ≤ d → G.totalDegree ≤ d → H.totalDegree ≤ d →
        ∀ A : Finset (AffineSubspace ℝ ℝ²),
          (∀ L ∈ A, ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
            eval (fun i => x i) F = 0 ∧ eval (fun i => y i) G = 0 ∧
            eval (fun i => z i) H = 0 ∧ line[ℝ,x,y] = L ∧ z ∈ L) →
          ε * (n : ℝ)^2 < (A.card : ℝ) →
          ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 3 ∧ F ∣ P ∧ G ∣ P ∧ H ∣ P) :
    H1 ∧ H2 := by
  classical
  constructor
  · intro d ε hε
    obtain ⟨N,hN⟩ := rigidity d ε hε
    refine ⟨N, ?_⟩
    intro n hn S hS hcap F hF hdeg hd hzero
    let finiteLines := OMA.R_Erdos101_erdos_101_R1.four_lines_finite S
    rw [Set.ncard_eq_toFinset_card _ finiteLines]
    by_contra! hdense
    have htwo : 2 ≤ F.totalDegree := by omega
    obtain ⟨P,hP,hcubic,hdiv,_⟩ :=
      hN n hn S hS hcap F F F hF hF hF htwo htwo htwo hd hd hd finiteLines.toFinset
        (by
          intro L hL
          have hm := finiteLines.mem_toFinset.mp hL
          have hsize := OMA.R_Erdos101_erdos_101_R1.four_points hm
          obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp
            (show 2 < (S.filter (fun p => p ∈ L)).card by omega)
          obtain ⟨hxS,hxL⟩ := Finset.mem_filter.mp hx
          obtain ⟨hyS,hyL⟩ := Finset.mem_filter.mp hy
          obtain ⟨hzS,hzL⟩ := Finset.mem_filter.mp hz
          exact ⟨x,hxS,y,hyS,z,hzS,hxy,hxz.symm,hyz.symm,hzero x hxS,hzero y hyS,hzero z hzS,
            OMA.R_Erdos101_erdos_101_R1.line_through hm hxL hyL hxy,hzL⟩) hdense
    have := totalDegree_le_of_dvd_of_isDomain hdiv hP
    omega
  · intro d ε hε
    obtain ⟨N,hN⟩ := rigidity d ε hε
    refine ⟨N, ?_⟩
    intro n hn S hS hcap F G H hF hG hH hFG h₂F h₂G h₂H hdF hdG hdH A hA
    by_contra! hdense
    obtain ⟨P,hP,hcubic,⟨Q,hQ⟩,hGP,_⟩ :=
      hN n hn S hS hcap F G H hF hG hH h₂F h₂G h₂H hdF hdG hdH A hA hdense
    rw [hQ] at hGP
    have hnot : ¬ G ∣ F := fun h => hFG (hG.associated_of_dvd hF h).symm
    obtain ⟨R,hR⟩ := ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hG).dvd_mul.mp hGP).resolve_left hnot
    have hprod : F * G ∣ P := ⟨R, by rw [hQ,hR,mul_assoc]⟩
    have h := totalDegree_le_of_dvd_of_isDomain hprod hP
    rw [totalDegree_mul_of_isDomain hF.ne_zero hG.ne_zero] at h
    omega

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1.H2 := by
  intro h₁ h₂ d ε hε
  let k := d + d^3
  let η := ε / (2 * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N,hN⟩ := nonlinear_estimate h₁ h₂ d η hη
  obtain ⟨J,hJ⟩ := exists_nat_gt (((d*4 : ℕ) : ℝ) / ε)
  refine ⟨max N J,?_⟩
  intro n hn S hSn hcap F hF _ hFd hzero
  obtain ⟨D,T,hTS,hDnum,hoff,hD,hT⟩ := nonlinear_cover hF S hcap hzero
  have hTbound := hN n ((le_max_left ..).trans hn) T ((Finset.card_le_card hTS).trans hSn)
    (NonCollinearFor.subset (Finset.coe_subset.mpr hTS) hcap) D (hDnum.trans hFd)
    (fun G hG => ⟨(hD G hG).1,(hD G hG).2.1,(hD G hG).2.2.trans hFd⟩) hT
  have hk : (k : ℝ) * η ≤ ε/2 := by
    have hnorm : ((k:ℝ)+1)*η = ε/2 := by dsimp [η]; field_simp
    rw [← hnorm]
    exact mul_le_mul_of_nonneg_right (by linarith) hη.le
  have hsmall : ((linesWithPointsFor 4 (T : Set ℝ²)).ncard : ℝ) ≤ (ε/2)*(n : ℝ)^2 := by
    change _ ≤ (k : ℝ)*(η*(n:ℝ)^2) at hTbound
    exact hTbound.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hk (sq_nonneg _))
  have hnat := (OMA.R_Erdos101_erdos_101_R1.delete_points_bound hTS).trans
    (Nat.add_le_add_left (Nat.mul_le_mul
      (hoff.trans (Nat.mul_le_mul_right 4 hFd)) ((Nat.sub_le ..).trans hSn)) _)
  have hreal : 3 * ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤
      3 * ((linesWithPointsFor 4 (T : Set ℝ²)).ncard : ℝ) + ((d*4 : ℕ) : ℝ)*n := by
    exact_mod_cast hnat
  have hnJ : (J : ℝ) ≤ n := by exact_mod_cast (le_max_right N J).trans hn
  have hd : ((d*4 : ℕ) : ℝ) ≤ ε*n :=
    (by linarith [(div_lt_iff₀ hε).mp hJ] : ((d*4 : ℕ) : ℝ) ≤ ε*J).trans
      (mul_le_mul_of_nonneg_left hnJ hε.le)
  have herr := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n : 0 ≤ (n:ℝ))
  nlinarith only [hreal,hsmall,herr,mul_nonneg hε.le (sq_nonneg (n:ℝ))]

end OMA.R_Erdos101_erdos_101_R1_H2_R1
