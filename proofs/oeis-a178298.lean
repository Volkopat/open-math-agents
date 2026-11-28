import OMAStatements.S_oeis_a178298

/-!
Proof of R. J. Mathar's closed form for OEIS A178298:
Every collinear 3-element subset of {0..4}^n orders along its line as {x0, x1, x2}
with x1 = x0 + q * (x2 - x0) for a reduced rational 0 < q < 1 whose denominator
divides every coordinate difference Delta_i in [-4, 4]. Thus q.den in {2, 3, 4},
splitting the collinear 3-subsets into three disjoint classes:
- Class 2 (q = 1/2): 2-to-1 from (13^n - 5^n) valid pairs (x0, d)
- Class 3 (q in {1/3, 2/3}): 1-to-1 from (9^n - 5^n) valid pairs
- Class 4 (q in {1/4, 3/4}): 1-to-1 from (7^n - 5^n) valid pairs
Hence 2 * a(n) = (13^n - 5^n) + 2*(9^n - 5^n) + 2*(7^n - 5^n)
               = 2*7^n - 5*5^n + 13^n + 2*9^n.
-/

namespace OMA.P_oeis_a178298

private lemma toReal_inj {n : ℕ} {x y : Fin n → Fin 5}
    (h : OMA.S_oeis_a178298.toReal x = OMA.S_oeis_a178298.toReal y) : x = y := by
  ext i
  have hi : (((x i : ℕ) : ℝ)) = ((y i : ℕ) : ℝ) := congrFun h i
  exact_mod_cast hi

private def intIcc (b : ℤ) : Finset ℤ :=
  (Finset.range (2 * b.toNat + 1)).image (fun j : ℕ => (j : ℤ) - b)

private lemma mem_intIcc {b x : ℤ} (hb : 0 ≤ b) : x ∈ intIcc b ↔ -b ≤ x ∧ x ≤ b := by
  rw [intIcc, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(x + b).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega

private def coordFinset (k : ℕ) (b : ℤ) : Finset (Fin 5 × ℤ) :=
  (Finset.univ ×ˢ intIcc b).filter
    (fun p => 0 ≤ (p.1 : ℤ) + (k : ℤ) * p.2 ∧ (p.1 : ℤ) + (k : ℤ) * p.2 ≤ 4)

private lemma coordFinset_2_2 : (coordFinset 2 2).card = 13 := by decide
private lemma coordFinset_3_1 : (coordFinset 3 1).card = 9 := by decide
private lemma coordFinset_4_1 : (coordFinset 4 1).card = 7 := by decide

private def pairFinset (n k : ℕ) (b : ℤ) : Finset (Fin n → ↥(coordFinset k b)) :=
  Finset.univ.filter (fun f => ∃ i, (f i).1.2 ≠ 0)

private lemma pairFinset_card (n k : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    5 ^ n ≤ (coordFinset k b).card ^ n ∧
      (pairFinset n k b).card = (coordFinset k b).card ^ n - 5 ^ n := by
  let zeroSet : Finset (Fin n → ↥(coordFinset k b)) :=
    Finset.univ.filter (fun f => ∀ i, (f i).1.2 = 0)
  have hzero_card : zeroSet.card = 5 ^ n := by
    have hbij : zeroSet.card = (Finset.univ : Finset (Fin n → Fin 5)).card := by
      refine Finset.card_nbij'
        (fun f i => (f i).1.1)
        (fun x i => ⟨(x i, 0), by
          simp only [coordFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            mem_intIcc hb, true_and]
          have hx := (x i).isLt
          refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩⟩)
        ?_ ?_ ?_ ?_
      · intro f _; simp
      · intro x _
        simp [zeroSet]
      · intro f hf
        simp only [zeroSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        ext i
        · rfl
        · exact (hf i).symm
      · intro x _; rfl
    rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have huniv :
      (Finset.univ : Finset (Fin n → ↥(coordFinset k b))).card = (coordFinset k b).card ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hunion : pairFinset n k b ∪ zeroSet = Finset.univ := by
    ext f
    simp only [pairFinset, zeroSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _; by_cases h : ∃ i, (f i).1.2 ≠ 0
      · exact Or.inl h
      · push Not at h; exact Or.inr h
  have hdisj : Disjoint (pairFinset n k b) zeroSet := by
    rw [Finset.disjoint_left]
    intro f hf1 hf2
    simp only [pairFinset, zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf1 hf2
    rcases hf1 with ⟨i, hi⟩
    exact hi (hf2 i)
  have hadd : (pairFinset n k b).card + zeroSet.card = (coordFinset k b).card ^ n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, huniv]
  rw [hzero_card] at hadd
  exact ⟨by omega, by omega⟩

private def mkX0 {n k : ℕ} {b : ℤ} (f : Fin n → ↥(coordFinset k b)) : Fin n → Fin 5 :=
  fun i => (f i).1.1

private def mkX1 {n k : ℕ} (hk : 1 ≤ k) {b : ℤ} (f : Fin n → ↥(coordFinset k b)) :
    Fin n → Fin 5 :=
  fun i => ⟨(((f i).1.1 : ℤ) + (f i).1.2).toNat, by
    have hp := (Finset.mem_filter.mp (f i).2).2
    have hx := (f i).1.1.isLt
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hbounds : 0 ≤ ((f i).1.1 : ℤ) + (f i).1.2 ∧ ((f i).1.1 : ℤ) + (f i).1.2 ≤ 4 := by
      by_cases hd : 0 ≤ (f i).1.2 <;> constructor <;> nlinarith
    omega⟩

private def mkX2 {n k : ℕ} {b : ℤ} (f : Fin n → ↥(coordFinset k b)) : Fin n → Fin 5 :=
  fun i => ⟨(((f i).1.1 : ℤ) + (k : ℤ) * (f i).1.2).toNat, by
    have hp := (Finset.mem_filter.mp (f i).2).2
    omega⟩

private lemma mkX1_val {n k : ℕ} (hk : 1 ≤ k) {b : ℤ}
    (f : Fin n → ↥(coordFinset k b)) (i : Fin n) :
    ((mkX1 hk f i : ℕ) : ℤ) = ((mkX0 f i : ℕ) : ℤ) + (f i).1.2 := by
  have hp := (Finset.mem_filter.mp (f i).2).2
  have hx := (f i).1.1.isLt
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have h0 : 0 ≤ ((f i).1.1 : ℤ) + (f i).1.2 := by by_cases hd : 0 ≤ (f i).1.2 <;> nlinarith
  simp only [mkX1, mkX0, Fin.val_mk]
  exact Int.toNat_of_nonneg h0

private lemma mkX2_val {n k : ℕ} {b : ℤ}
    (f : Fin n → ↥(coordFinset k b)) (i : Fin n) :
    ((mkX2 f i : ℕ) : ℤ) = ((mkX0 f i : ℕ) : ℤ) + (k : ℤ) * (f i).1.2 := by
  have hp := (Finset.mem_filter.mp (f i).2).2
  simp only [mkX2, mkX0, Fin.val_mk]
  exact Int.toNat_of_nonneg hp.1

private def mkTriple {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (b : ℤ)
    (f : Fin n → ↥(coordFinset k b)) : Finset (Fin n → Fin 5) :=
  {mkX0 f, mkX1 hk f, mkX2 f}

private lemma mkTriple_mem {n k : ℕ} (hk : 2 ≤ k) {b : ℤ}
    {f : Fin n → ↥(coordFinset k b)} (hf : f ∈ pairFinset n k b) :
    (mkTriple k (by omega) b f).card = 3 ∧
      Collinear ℝ (OMA.S_oeis_a178298.toReal '' (mkTriple k (by omega) b f : Set (Fin n → Fin 5))) := by
  simp only [pairFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  rcases hf with ⟨i₀, hi₀⟩
  have h01 : mkX0 f ≠ mkX1 (by omega) f := by
    intro heq
    have hv := congrArg (fun g => ((g i₀ : ℕ) : ℤ)) heq
    rw [mkX1_val] at hv
    exact hi₀ (by omega)
  have h02 : mkX0 f ≠ mkX2 f := by
    intro heq
    have hv := congrArg (fun g => ((g i₀ : ℕ) : ℤ)) heq
    rw [mkX2_val] at hv
    have : (k : ℤ) * (f i₀).1.2 = 0 := by omega
    rcases mul_eq_zero.mp this with hk0 | hd0
    · omega
    · exact hi₀ hd0
  have h12 : mkX1 (by omega) f ≠ mkX2 f := by
    intro heq
    have hv := congrArg (fun g => ((g i₀ : ℕ) : ℤ)) heq
    rw [mkX1_val, mkX2_val] at hv
    have : ((k : ℤ) - 1) * (f i₀).1.2 = 0 := by linarith
    rcases mul_eq_zero.mp this with hk0 | hd0
    · omega
    · exact hi₀ hd0
  have hcard : (mkTriple k (by omega) b f).card = 3 := by
    dsimp [mkTriple]
    rw [Finset.card_insert_of_notMem, Finset.card_pair h12]
    simp [h01, h02]
  refine ⟨hcard, ?_⟩
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨OMA.S_oeis_a178298.toReal (mkX0 f),
    OMA.S_oeis_a178298.toReal (mkX2 f) - OMA.S_oeis_a178298.toReal (mkX0 f), ?_⟩
  rintro p ⟨x, hx, rfl⟩
  simp only [mkTriple, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨0, by simp⟩
  · refine ⟨1 / (k : ℝ), ?_⟩
    ext i
    simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      OMA.S_oeis_a178298.toReal]
    have hv1 : ((mkX1 (by omega) f i : ℕ) : ℝ) = ((mkX0 f i : ℕ) : ℝ) + ((f i).1.2 : ℝ) := by
      exact_mod_cast mkX1_val (by omega) f i
    have hv2 : ((mkX2 f i : ℕ) : ℝ) = ((mkX0 f i : ℕ) : ℝ) + (k : ℝ) * ((f i).1.2 : ℝ) := by
      exact_mod_cast mkX2_val f i
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    rw [hv1, hv2]
    field_simp [hk_ne]
    ring
  · refine ⟨1, by simp⟩

private lemma betweenness {n : ℕ} {x0 x1 x2 y0 y1 y2 : Fin n → Fin 5}
    {qx qy : ℚ} (hqx0 : 0 < qx) (hqx1 : qx < 1) (hqy0 : 0 < qy) (hqy1 : qy < 1)
    (hx_ne : x0 ≠ x2)
    (hx_eq : OMA.S_oeis_a178298.toReal x1 =
      OMA.S_oeis_a178298.toReal x0 + (qx : ℝ) • (OMA.S_oeis_a178298.toReal x2 - OMA.S_oeis_a178298.toReal x0))
    (hy_eq : OMA.S_oeis_a178298.toReal y1 =
      OMA.S_oeis_a178298.toReal y0 + (qy : ℝ) • (OMA.S_oeis_a178298.toReal y2 - OMA.S_oeis_a178298.toReal y0))
    (hset : ({x0, x1, x2} : Finset (Fin n → Fin 5)) = {y0, y1, y2}) :
    y1 = x1 ∧ ((y0 = x0 ∧ y2 = x2) ∨ (y0 = x2 ∧ y2 = x0)) := by
  have hi₀ : ∃ i₀ : Fin n, x0 i₀ ≠ x2 i₀ := by
    by_contra h
    push Not at h
    exact hx_ne (funext h)
  rcases hi₀ with ⟨i₀, hi₀⟩
  have hx_i₀ : ((x1 i₀ : ℕ) : ℝ) - ((x0 i₀ : ℕ) : ℝ) =
      (qx : ℝ) * (((x2 i₀ : ℕ) : ℝ) - ((x0 i₀ : ℕ) : ℝ)) := by
    have := congrFun hx_eq i₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, OMA.S_oeis_a178298.toReal] at this
    linarith
  have hy_i₀ : ((y1 i₀ : ℕ) : ℝ) - ((y0 i₀ : ℕ) : ℝ) =
      (qy : ℝ) * (((y2 i₀ : ℕ) : ℝ) - ((y0 i₀ : ℕ) : ℝ)) := by
    have := congrFun hy_eq i₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, OMA.S_oeis_a178298.toReal] at this
    linarith
  have hqx0R : (0 : ℝ) < (qx : ℝ) := by exact_mod_cast hqx0
  have hqx1R : (qx : ℝ) < 1 := by exact_mod_cast hqx1
  have hqy0R : (0 : ℝ) < (qy : ℝ) := by exact_mod_cast hqy0
  have hqy1R : (qy : ℝ) < 1 := by exact_mod_cast hqy1
  have hx_ord : ((x0 i₀ : ℕ) < (x1 i₀ : ℕ) ∧ (x1 i₀ : ℕ) < (x2 i₀ : ℕ)) ∨
      ((x2 i₀ : ℕ) < (x1 i₀ : ℕ) ∧ (x1 i₀ : ℕ) < (x0 i₀ : ℕ)) := by
    have hne : ((x0 i₀ : ℕ) : ℝ) ≠ ((x2 i₀ : ℕ) : ℝ) := by exact_mod_cast Fin.val_ne_of_ne hi₀
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have h1 : ((x0 i₀ : ℕ) : ℝ) < ((x1 i₀ : ℕ) : ℝ) := by nlinarith
      have h2 : ((x1 i₀ : ℕ) : ℝ) < ((x2 i₀ : ℕ) : ℝ) := by nlinarith
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · right
      have h1 : ((x2 i₀ : ℕ) : ℝ) < ((x1 i₀ : ℕ) : ℝ) := by nlinarith
      have h2 : ((x1 i₀ : ℕ) : ℝ) < ((x0 i₀ : ℕ) : ℝ) := by nlinarith
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hxs_ne : x0 i₀ ≠ x1 i₀ ∧ x1 i₀ ≠ x2 i₀ ∧ x0 i₀ ≠ x2 i₀ := by
    rcases hx_ord with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> refine ⟨?_, ?_, hi₀⟩ <;>
      exact Fin.ne_of_val_ne (by omega)
  have himg :
      ({x0 i₀, x1 i₀, x2 i₀} : Finset (Fin 5)) = {y0 i₀, y1 i₀, y2 i₀} := by
    have h := congrArg (fun s : Finset (Fin n → Fin 5) => s.image (fun f => f i₀)) hset
    simpa [Finset.image_insert, Finset.image_singleton] using h
  have hy02_ne : y0 i₀ ≠ y2 i₀ := by
    intro heq
    have hy10 : y1 i₀ = y0 i₀ := by
      have hR : ((y0 i₀ : ℕ) : ℝ) = ((y2 i₀ : ℕ) : ℝ) := by
        exact_mod_cast congrArg Fin.val heq
      rw [hR, sub_self, mul_zero, sub_eq_zero] at hy_i₀
      have hy12 : y1 i₀ = y2 i₀ := Fin.ext (by exact_mod_cast hy_i₀)
      exact hy12.trans heq.symm
    have hcard_le : ({y0 i₀, y1 i₀, y2 i₀} : Finset (Fin 5)).card ≤ 1 := by
      rw [hy10, heq]
      simp
    have hcard3 : ({x0 i₀, x1 i₀, x2 i₀} : Finset (Fin 5)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hxs_ne.2.1]
      simp [hxs_ne.1, hxs_ne.2.2]
    rw [himg] at hcard3
    omega
  have hy_ord : ((y0 i₀ : ℕ) < (y1 i₀ : ℕ) ∧ (y1 i₀ : ℕ) < (y2 i₀ : ℕ)) ∨
      ((y2 i₀ : ℕ) < (y1 i₀ : ℕ) ∧ (y1 i₀ : ℕ) < (y0 i₀ : ℕ)) := by
    have hne : ((y0 i₀ : ℕ) : ℝ) ≠ ((y2 i₀ : ℕ) : ℝ) := by exact_mod_cast Fin.val_ne_of_ne hy02_ne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have h1 : ((y0 i₀ : ℕ) : ℝ) < ((y1 i₀ : ℕ) : ℝ) := by nlinarith
      have h2 : ((y1 i₀ : ℕ) : ℝ) < ((y2 i₀ : ℕ) : ℝ) := by nlinarith
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · right
      have h1 : ((y2 i₀ : ℕ) : ℝ) < ((y1 i₀ : ℕ) : ℝ) := by nlinarith
      have h2 : ((y1 i₀ : ℕ) : ℝ) < ((y0 i₀ : ℕ) : ℝ) := by nlinarith
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hy1_mem : y1 i₀ ∈ ({x0 i₀, x1 i₀, x2 i₀} : Finset (Fin 5)) := by
    rw [himg]; simp
  have hy0_mem : y0 i₀ ∈ ({x0 i₀, x1 i₀, x2 i₀} : Finset (Fin 5)) := by
    rw [himg]; simp
  have hy2_mem : y2 i₀ ∈ ({x0 i₀, x1 i₀, x2 i₀} : Finset (Fin 5)) := by
    rw [himg]; simp
  have hy1_i₀ : y1 i₀ = x1 i₀ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy1_mem hy0_mem hy2_mem
    rcases hy1_mem with hy1x0 | hy1x1 | hy1x2
    · exfalso
      rcases hy_ord with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx_ord with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases hy0_mem with hy0x0 | hy0x1 | hy0x2 <;>
        rcases hy2_mem with hy2x0 | hy2x1 | hy2x2 <;>
        omega
    · exact hy1x1
    · exfalso
      rcases hy_ord with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx_ord with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases hy0_mem with hy0x0 | hy0x1 | hy0x2 <;>
        rcases hy2_mem with hy2x0 | hy2x1 | hy2x2 <;>
        omega
  have hy1_eq : y1 = x1 := by
    have hy1_s : y1 ∈ ({x0, x1, x2} : Finset (Fin n → Fin 5)) := by rw [hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy1_s
    rcases hy1_s with rfl | rfl | rfl
    · exact absurd hy1_i₀ hxs_ne.1
    · rfl
    · exact absurd hy1_i₀ hxs_ne.2.1.symm
  refine ⟨hy1_eq, ?_⟩
  have hy0_s : y0 ∈ ({x0, x1, x2} : Finset (Fin n → Fin 5)) := by rw [hset]; simp
  have hy2_s : y2 ∈ ({x0, x1, x2} : Finset (Fin n → Fin 5)) := by rw [hset]; simp
  have hy0_ne1 : y0 ≠ y1 := by
    intro h; rw [h, hy1_eq] at hy_ord; rcases hy_ord with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
  have hy2_ne1 : y2 ≠ y1 := by
    intro h; rw [h, hy1_eq] at hy_ord; rcases hy_ord with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega
  have hy0_ne2 : y0 ≠ y2 := fun h => hy02_ne (congrFun h i₀)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy0_s hy2_s
  rw [hy1_eq] at hy0_ne1 hy2_ne1
  rcases hy0_s with rfl | rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    rcases hy2_s with h | h | h
    · exact absurd h.symm hy0_ne2
    · exact absurd h hy2_ne1
    · exact h
  · exact absurd rfl hy0_ne1
  · right; refine ⟨rfl, ?_⟩
    rcases hy2_s with h | h | h
    · exact h
    · exact absurd h hy2_ne1
    · exact absurd h.symm hy0_ne2

private lemma mkTriple_eq_iff {n k₁ k₂ : ℕ} {b₁ b₂ : ℤ}
    (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {f : Fin n → ↥(coordFinset k₁ b₁)} {g : Fin n → ↥(coordFinset k₂ b₂)}
    (hf : f ∈ pairFinset n k₁ b₁) (_hg : g ∈ pairFinset n k₂ b₂)
    (heq : mkTriple k₁ (by omega) b₁ f = mkTriple k₂ (by omega) b₂ g) :
    (k₁ = k₂ ∧ (∀ i, (f i).1 = (g i).1)) ∨
      (k₁ = 2 ∧ k₂ = 2 ∧ (∀ i, (g i).1.1 = mkX2 f i ∧ (g i).1.2 = -(f i).1.2)) := by
  have hxf_eq :
      OMA.S_oeis_a178298.toReal (mkX1 (by omega) f) =
        OMA.S_oeis_a178298.toReal (mkX0 f) +
          ((1 / (k₁ : ℚ) : ℚ) : ℝ) •
            (OMA.S_oeis_a178298.toReal (mkX2 f) - OMA.S_oeis_a178298.toReal (mkX0 f)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      OMA.S_oeis_a178298.toReal, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    have hv1 : ((mkX1 (by omega) f i : ℕ) : ℝ) = ((mkX0 f i : ℕ) : ℝ) + ((f i).1.2 : ℝ) := by
      exact_mod_cast mkX1_val (by omega) f i
    have hv2 : ((mkX2 f i : ℕ) : ℝ) = ((mkX0 f i : ℕ) : ℝ) + (k₁ : ℝ) * ((f i).1.2 : ℝ) := by
      exact_mod_cast mkX2_val f i
    have hk_ne : (k₁ : ℝ) ≠ 0 := by positivity
    rw [hv1, hv2]
    field_simp [hk_ne]
    ring
  have hxg_eq :
      OMA.S_oeis_a178298.toReal (mkX1 (by omega) g) =
        OMA.S_oeis_a178298.toReal (mkX0 g) +
          ((1 / (k₂ : ℚ) : ℚ) : ℝ) •
            (OMA.S_oeis_a178298.toReal (mkX2 g) - OMA.S_oeis_a178298.toReal (mkX0 g)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      OMA.S_oeis_a178298.toReal, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    have hv1 : ((mkX1 (by omega) g i : ℕ) : ℝ) = ((mkX0 g i : ℕ) : ℝ) + ((g i).1.2 : ℝ) := by
      exact_mod_cast mkX1_val (by omega) g i
    have hv2 : ((mkX2 g i : ℕ) : ℝ) = ((mkX0 g i : ℕ) : ℝ) + (k₂ : ℝ) * ((g i).1.2 : ℝ) := by
      exact_mod_cast mkX2_val g i
    have hk_ne : (k₂ : ℝ) ≠ 0 := by positivity
    rw [hv1, hv2]
    field_simp [hk_ne]
    ring
  simp only [pairFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  rcases hf with ⟨i₀, hi₀⟩
  have hx02_ne : mkX0 f ≠ mkX2 f := by
    intro h
    have hv := congrArg (fun p => ((p i₀ : ℕ) : ℤ)) h
    rw [mkX2_val] at hv
    have : (k₁ : ℤ) * (f i₀).1.2 = 0 := by omega
    rcases mul_eq_zero.mp this with hk0 | hd0
    · omega
    · exact hi₀ hd0
  have hqx0 : (0 : ℚ) < 1 / (k₁ : ℚ) := by positivity
  have hqx1 : (1 / (k₁ : ℚ) : ℚ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : 1 < k₁)
  have hqy0 : (0 : ℚ) < 1 / (k₂ : ℚ) := by positivity
  have hqy1 : (1 / (k₂ : ℚ) : ℚ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : 1 < k₂)
  obtain ⟨hy1, hor⟩ := betweenness hqx0 hqx1 hqy0 hqy1 hx02_ne hxf_eq hxg_eq heq
  rcases hor with ⟨hy0, hy2⟩ | ⟨hy0, hy2⟩
  · have hdg : ∀ i, (g i).1.2 = (f i).1.2 := by
      intro i
      have hv1 := congrArg (fun p => ((p i : ℕ) : ℤ)) hy1
      have hv0 := congrArg (fun p => ((p i : ℕ) : ℤ)) hy0
      rw [mkX1_val, mkX1_val] at hv1
      omega
    have hk_eq : k₁ = k₂ := by
      have hv2 := congrArg (fun p => ((p i₀ : ℕ) : ℤ)) hy2
      have hv0 := congrArg (fun p => ((p i₀ : ℕ) : ℤ)) hy0
      rw [mkX2_val, mkX2_val] at hv2
      have hmul : (k₂ : ℤ) * (g i₀).1.2 = (k₁ : ℤ) * (f i₀).1.2 := by omega
      rw [hdg i₀] at hmul
      exact_mod_cast (mul_right_cancel₀ hi₀ hmul).symm
    left
    refine ⟨hk_eq, fun i => Prod.ext (congrFun hy0.symm i) (hdg i).symm⟩
  · have hdg : ∀ i, (g i).1.2 = (1 - (k₁ : ℤ)) * (f i).1.2 := by
      intro i
      have hv1 := congrArg (fun p => ((p i : ℕ) : ℤ)) hy1
      have hv0 := congrArg (fun p => ((p i : ℕ) : ℤ)) hy0
      rw [mkX1_val, mkX1_val] at hv1
      rw [mkX2_val] at hv0
      linarith
    have hmul : (k₂ : ℤ) * (1 - (k₁ : ℤ)) * (f i₀).1.2 = -(k₁ : ℤ) * (f i₀).1.2 := by
      have hv2 := congrArg (fun p => ((p i₀ : ℕ) : ℤ)) hy2
      have hv0 := congrArg (fun p => ((p i₀ : ℕ) : ℤ)) hy0
      rw [mkX2_val] at hv2
      rw [mkX2_val] at hv0
      have h1 : (k₂ : ℤ) * (g i₀).1.2 = -(k₁ : ℤ) * (f i₀).1.2 := by linarith
      rw [hdg i₀] at h1
      linarith
    have hk_rel : (k₂ : ℤ) * (1 - (k₁ : ℤ)) = -(k₁ : ℤ) :=
      mul_right_cancel₀ hi₀ (by linarith [hmul])
    have hk12 : k₁ = 2 ∧ k₂ = 2 := by
      have hk1z : (2 : ℤ) ≤ (k₁ : ℤ) := by exact_mod_cast hk₁
      have hk2z : (2 : ℤ) ≤ (k₂ : ℤ) := by exact_mod_cast hk₂
      have hpos : (k₂ : ℤ) * ((k₁ : ℤ) - 1) = (k₁ : ℤ) := by linarith
      have hle : 2 * ((k₁ : ℤ) - 1) ≤ (k₁ : ℤ) := by nlinarith
      have : (k₁ : ℤ) = 2 := by omega
      have : (k₂ : ℤ) = 2 := by nlinarith
      exact ⟨by exact_mod_cast ‹(k₁ : ℤ) = 2›, by exact_mod_cast ‹(k₂ : ℤ) = 2›⟩
    right
    refine ⟨hk12.1, hk12.2, fun i => ⟨congrFun hy0 i, ?_⟩⟩
    have hk1z : (k₁ : ℤ) = 2 := by exact_mod_cast hk12.1
    rw [hdg i, hk1z]
    ring

private lemma collinear_exists_triple {n : ℕ} {s : Finset (Fin n → Fin 5)}
    (hs3 : s.card = 3)
    (hscol : Collinear ℝ (OMA.S_oeis_a178298.toReal '' (s : Set (Fin n → Fin 5)))) :
    ∃ x0 x1 x2 : Fin n → Fin 5, ∃ q : ℚ,
      0 < q ∧ q < 1 ∧ s = {x0, x1, x2} ∧ x0 ≠ x2 ∧
      OMA.S_oeis_a178298.toReal x1 =
        OMA.S_oeis_a178298.toReal x0 +
          (q : ℝ) • (OMA.S_oeis_a178298.toReal x2 - OMA.S_oeis_a178298.toReal x0) := by
  rw [Finset.card_eq_three] at hs3
  rcases hs3 with ⟨u, v, w, huv, huw, hvw, rfl⟩
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hscol
  rcases hscol with ⟨p₀, dir, hdir⟩
  have hu : ∃ ru : ℝ, OMA.S_oeis_a178298.toReal u = ru • dir +ᵥ p₀ := hdir _ (by simp)
  have hv : ∃ rv : ℝ, OMA.S_oeis_a178298.toReal v = rv • dir +ᵥ p₀ := hdir _ (by simp)
  have hw : ∃ rw_ : ℝ, OMA.S_oeis_a178298.toReal w = rw_ • dir +ᵥ p₀ := hdir _ (by simp)
  rcases hu with ⟨ru, hru⟩
  rcases hv with ⟨rv, hrv⟩
  rcases hw with ⟨rw_, hrw⟩
  have h_sort : ∀ a b c : Fin n → Fin 5, ∀ ra rb rc : ℝ,
      a ≠ b → a ≠ c → b ≠ c →
      OMA.S_oeis_a178298.toReal a = ra • dir +ᵥ p₀ →
      OMA.S_oeis_a178298.toReal b = rb • dir +ᵥ p₀ →
      OMA.S_oeis_a178298.toReal c = rc • dir +ᵥ p₀ →
      ra < rb → rb < rc →
      ∃ q : ℚ, 0 < q ∧ q < 1 ∧
        OMA.S_oeis_a178298.toReal b =
          OMA.S_oeis_a178298.toReal a +
            (q : ℝ) • (OMA.S_oeis_a178298.toReal c - OMA.S_oeis_a178298.toReal a) := by
    intro a b c ra rb rc hab hac hbc ha hb hc hrab hrbc
    have hi₀ : ∃ i₀ : Fin n, a i₀ ≠ c i₀ := by
      by_contra h
      push Not at h
      exact hac (funext h)
    rcases hi₀ with ⟨i₀, hi₀⟩
    have hdiff_ac : OMA.S_oeis_a178298.toReal c - OMA.S_oeis_a178298.toReal a =
        (rc - ra) • dir := by
      rw [hc, ha]
      simp [vadd_eq_add, sub_smul]
    have hdiff_ab : OMA.S_oeis_a178298.toReal b - OMA.S_oeis_a178298.toReal a =
        (rb - ra) • dir := by
      rw [hb, ha]
      simp [vadd_eq_add, sub_smul]
    have hα : (rb - ra) / (rc - ra) =
        (((b i₀ : ℕ) : ℝ) - ((a i₀ : ℕ) : ℝ)) / (((c i₀ : ℕ) : ℝ) - ((a i₀ : ℕ) : ℝ)) := by
      have hac_i₀ := congrFun hdiff_ac i₀
      have hab_i₀ := congrFun hdiff_ab i₀
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, OMA.S_oeis_a178298.toReal] at hac_i₀ hab_i₀
      have hca_ne : ((c i₀ : ℕ) : ℝ) - ((a i₀ : ℕ) : ℝ) ≠ 0 := by
        intro h0
        have : ((c i₀ : ℕ) : ℝ) = ((a i₀ : ℕ) : ℝ) := by linarith
        exact hi₀ (Fin.ext (by exact_mod_cast this)).symm
      have hrc_ne : rc - ra ≠ 0 := by linarith
      field_simp [hca_ne, hrc_ne]
      rw [hab_i₀, hac_i₀]
      ring
    let q : ℚ := (((b i₀ : ℤ) - (a i₀ : ℤ) : ℤ) : ℚ) / (((c i₀ : ℤ) - (a i₀ : ℤ) : ℤ) : ℚ)
    have hqR : (q : ℝ) = (rb - ra) / (rc - ra) := by
      rw [hα]
      dsimp [q]
      push_cast
      rfl
    have hq0 : 0 < q := by
      have : (0 : ℝ) < (q : ℝ) := by rw [hqR]; exact div_pos (by linarith) (by linarith)
      exact_mod_cast this
    have hq1 : q < 1 := by
      have : (q : ℝ) < 1 := by rw [hqR, div_lt_one (by linarith)]; linarith
      exact_mod_cast this
    refine ⟨q, hq0, hq1, ?_⟩
    rw [hqR, ← sub_eq_iff_eq_add', hdiff_ab, hdiff_ac, smul_smul, div_mul_cancel₀ _ (by linarith)]
  have huv_ne : ru ≠ rv := fun h => huv (toReal_inj (by rw [hru, hrv, h]))
  have huw_ne : ru ≠ rw_ := fun h => huw (toReal_inj (by rw [hru, hrw, h]))
  have hvw_ne : rv ≠ rw_ := fun h => hvw (toReal_inj (by rw [hrv, hrw, h]))
  rcases lt_or_gt_of_ne huv_ne with huv_lt | hvu_lt
  · rcases lt_or_gt_of_ne huw_ne with huw_lt | hwu_lt
    · rcases lt_or_gt_of_ne hvw_ne with hvw_lt | hwv_lt
      · obtain ⟨q, hq0, hq1, heq⟩ := h_sort u v w ru rv rw_ huv huw hvw hru hrv hrw huv_lt hvw_lt
        exact ⟨u, v, w, q, hq0, hq1, rfl, huw, heq⟩
      · obtain ⟨q, hq0, hq1, heq⟩ := h_sort u w v ru rw_ rv huw huv hvw.symm hru hrw hrv huw_lt hwv_lt
        exact ⟨u, w, v, q, hq0, hq1, by ext x; simp; tauto, huv, heq⟩
    · obtain ⟨q, hq0, hq1, heq⟩ := h_sort w u v rw_ ru rv huw.symm hvw.symm huv hrw hru hrv hwu_lt huv_lt
      exact ⟨w, u, v, q, hq0, hq1, by ext x; simp; tauto, hvw.symm, heq⟩
  · rcases lt_or_gt_of_ne hvw_ne with hvw_lt | hwv_lt
    · rcases lt_or_gt_of_ne huw_ne with huw_lt | hwu_lt
      · obtain ⟨q, hq0, hq1, heq⟩ := h_sort v u w rv ru rw_ huv.symm hvw huw hrv hru hrw hvu_lt huw_lt
        exact ⟨v, u, w, q, hq0, hq1, by ext x; simp; tauto, hvw, heq⟩
      · obtain ⟨q, hq0, hq1, heq⟩ := h_sort v w u rv rw_ ru hvw huv.symm huw.symm hrv hrw hru hvw_lt hwu_lt
        exact ⟨v, w, u, q, hq0, hq1, by ext x; simp; tauto, huv.symm, heq⟩
    · obtain ⟨q, hq0, hq1, heq⟩ := h_sort w v u rw_ rv ru hvw.symm huw.symm huv.symm hrw hrv hru hwv_lt hvu_lt
      exact ⟨w, v, u, q, hq0, hq1, by ext x; simp; tauto, huw.symm, heq⟩

private lemma collinear_mem_classes {n : ℕ} {s : Finset (Fin n → Fin 5)}
    (hs3 : s.card = 3)
    (hscol : Collinear ℝ (OMA.S_oeis_a178298.toReal '' (s : Set (Fin n → Fin 5)))) :
    s ∈ (pairFinset n 2 2).image (mkTriple 2 (by omega) 2) ∨
      s ∈ (pairFinset n 3 1).image (mkTriple 3 (by omega) 1) ∨
      s ∈ (pairFinset n 4 1).image (mkTriple 4 (by omega) 1) := by
  obtain ⟨x0, x1, x2, q, hq0, hq1, rfl, hx02, hqeq⟩ := collinear_exists_triple hs3 hscol
  have hrel : ∀ i : Fin n,
      q.num * ((x2 i : ℤ) - (x0 i : ℤ)) = (q.den : ℤ) * ((x1 i : ℤ) - (x0 i : ℤ)) := by
    intro i
    have hR := congrFun hqeq i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      OMA.S_oeis_a178298.toReal] at hR
    have hQ : ((((x1 i : ℕ) : ℤ) - ((x0 i : ℕ) : ℤ) : ℤ) : ℚ) =
        q * ((((x2 i : ℕ) : ℤ) - ((x0 i : ℕ) : ℤ) : ℤ) : ℚ) := by
      have hR' : ((((((x1 i : ℕ) : ℤ) - ((x0 i : ℕ) : ℤ) : ℤ) : ℚ)) : ℝ) =
          ((q * (((((x2 i : ℕ) : ℤ) - ((x0 i : ℕ) : ℤ) : ℤ) : ℚ)) : ℚ) : ℝ) := by
        push_cast
        linarith
      exact Rat.cast_inj.mp hR'
    have hq_eq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    rw [hq_eq] at hQ
    have hQ' : (q.den : ℚ) * ((((x1 i : ℕ) : ℤ) - ((x0 i : ℕ) : ℤ) : ℤ) : ℚ) =
        (q.num : ℚ) * ((((x2 i : ℕ) : ℤ) - ((x0 i : ℕ) : ℤ) : ℤ) : ℚ) := by
      field_simp [hden_ne] at hQ
      linarith
    exact_mod_cast hQ'.symm
  have hdvd : ∀ i : Fin n, (q.den : ℤ) ∣ ((x2 i : ℤ) - (x0 i : ℤ)) := by
    intro i
    have hmul : (q.den : ℤ) ∣ q.num * ((x2 i : ℤ) - (x0 i : ℤ)) :=
      ⟨(x1 i : ℤ) - (x0 i : ℤ), hrel i⟩
    have hnat : q.den ∣ q.num.natAbs * ((x2 i : ℤ) - (x0 i : ℤ)).natAbs := by
      have h1 := Int.natAbs_dvd_natAbs.mpr hmul
      simpa [Int.natAbs_mul] using h1
    have hnat2 : q.den ∣ ((x2 i : ℤ) - (x0 i : ℤ)).natAbs :=
      q.reduced.symm.dvd_of_dvd_mul_left hnat
    exact Int.natCast_dvd.mpr hnat2
  have hi₀ : ∃ i₀ : Fin n, x0 i₀ ≠ x2 i₀ := by
    by_contra h
    push Not at h
    exact hx02 (funext h)
  rcases hi₀ with ⟨i₀, hi₀⟩
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
  have hnum_lt : q.num < (q.den : ℤ) := by
    have hq_eq : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    have hlt1 : (q.num : ℚ) / (q.den : ℚ) < 1 := hq_eq.symm ▸ hq1
    have hd : (0 : ℚ) < (q.den : ℚ) := Nat.cast_pos.mpr q.pos
    exact_mod_cast (div_lt_one hd).mp hlt1
  have hden_ge2 : 2 ≤ q.den := by omega
  have hden_le4 : q.den ≤ 4 := by
    have hd_i₀ := hdvd i₀
    have hnat : q.den ∣ ((x2 i₀ : ℤ) - (x0 i₀ : ℤ)).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hd_i₀
    have hpos_diff : 0 < ((x2 i₀ : ℤ) - (x0 i₀ : ℤ)).natAbs := by
      have h1 : (x0 i₀ : ℕ) ≠ (x2 i₀ : ℕ) := Fin.val_ne_of_ne hi₀
      omega
    have hle4_diff : ((x2 i₀ : ℤ) - (x0 i₀ : ℤ)).natAbs ≤ 4 := by
      have h0 := (x0 i₀).isLt
      have h2 := (x2 i₀).isLt
      omega
    exact le_trans (Nat.le_of_dvd hpos_diff hnat) hle4_diff
  have build_mem : ∀ k : ℕ, ∀ hk : 2 ≤ k, ∀ b : ℤ,
      q.den = k → (q.num = 1 ∨ q.num = (k : ℤ) - 1) →
      (∀ i : Fin n, -b ≤ ((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ) ∧
        ((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ) ≤ b) →
      ({x0, x1, x2} : Finset (Fin n → Fin 5)) ∈
        (pairFinset n k b).image (mkTriple k (Nat.le_of_succ_le hk) b) := by
    intro k hk b hden hnum hb_bound
    rcases hnum with hnum1 | hnum_rev
    · let f : Fin n → ↥(coordFinset k b) := fun i =>
        ⟨(x0 i, ((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ)), by
          have hb0 : 0 ≤ b := by have := hb_bound i; omega
          simp only [coordFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            mem_intIcc hb0, true_and]
          have hdi := hdvd i
          rw [hden] at hdi
          have hmul : (k : ℤ) * (((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ)) = (x2 i : ℤ) - (x0 i : ℤ) := by
            rw [mul_comm]
            exact Int.ediv_mul_cancel hdi
          have h2lt := (x2 i).isLt
          refine ⟨hb_bound i, ?_, ?_⟩ <;> omega⟩
      refine Finset.mem_image.mpr ⟨f, ?_, ?_⟩
      · simp only [pairFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨i₀, ?_⟩
        have hdi₀ := hdvd i₀
        rw [hden] at hdi₀
        have hmul := Int.ediv_mul_cancel hdi₀
        have hne : (x2 i₀ : ℤ) - (x0 i₀ : ℤ) ≠ 0 := by
          have := Fin.val_ne_of_ne hi₀
          omega
        intro h0
        dsimp [f] at h0
        rw [h0, zero_mul] at hmul
        exact hne hmul.symm
      · have hx0f : mkX0 f = x0 := rfl
        have hx2f : mkX2 f = x2 := by
          ext i
          have hv := mkX2_val f i
          have hdi := hdvd i
          rw [hden] at hdi
          have hmul := Int.ediv_mul_cancel hdi
          have hv' : ((mkX2 f i : ℕ) : ℤ) = ((x0 i : ℕ) : ℤ) +
              (k : ℤ) * (((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ)) := hv
          rw [mul_comm (k : ℤ), hmul] at hv'
          exact_mod_cast (by omega : ((mkX2 f i : ℕ) : ℤ) = ((x2 i : ℕ) : ℤ))
        have hx1f : mkX1 (Nat.le_of_succ_le hk) f = x1 := by
          ext i
          have hv := mkX1_val (Nat.le_of_succ_le hk) f i
          have hr := hrel i
          rw [hnum1, hden, one_mul] at hr
          have hdi := hdvd i
          rw [hden] at hdi
          have hmul := Int.ediv_mul_cancel hdi
          have hkd : (((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ)) * (k : ℤ) = (k : ℤ) * ((x1 i : ℤ) - (x0 i : ℤ)) :=
            hmul.trans hr
          have hdeq : ((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ) = (x1 i : ℤ) - (x0 i : ℤ) := by
            nlinarith
          have hv' : ((mkX1 (Nat.le_of_succ_le hk) f i : ℕ) : ℤ) =
              ((x0 i : ℕ) : ℤ) + ((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ) := hv
          rw [hdeq] at hv'
          exact_mod_cast (by omega : ((mkX1 (Nat.le_of_succ_le hk) f i : ℕ) : ℤ) = ((x1 i : ℕ) : ℤ))
        simp only [mkTriple, hx0f, hx1f, hx2f]
    · let f : Fin n → ↥(coordFinset k b) := fun i =>
        ⟨(x2 i, ((x0 i : ℤ) - (x2 i : ℤ)) / (k : ℤ)), by
          have hb0 : 0 ≤ b := by have := hb_bound i; omega
          simp only [coordFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            mem_intIcc hb0, true_and]
          have hdi : (k : ℤ) ∣ ((x0 i : ℤ) - (x2 i : ℤ)) := by
            have := hdvd i
            rw [hden] at this
            simpa [neg_sub] using dvd_neg.mpr this
          have hmul : (k : ℤ) * (((x0 i : ℤ) - (x2 i : ℤ)) / (k : ℤ)) = (x0 i : ℤ) - (x2 i : ℤ) := by
            rw [mul_comm]
            exact Int.ediv_mul_cancel hdi
          have hneg : ((x0 i : ℤ) - (x2 i : ℤ)) / (k : ℤ) =
              -(((x2 i : ℤ) - (x0 i : ℤ)) / (k : ℤ)) := by
            have hd2 := hdvd i
            rw [hden] at hd2
            have hm2 := Int.ediv_mul_cancel hd2
            nlinarith
          have hb := hb_bound i
          have h0lt := (x0 i).isLt
          refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩ <;> omega⟩
      refine Finset.mem_image.mpr ⟨f, ?_, ?_⟩
      · simp only [pairFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨i₀, ?_⟩
        have hdi₀ : (k : ℤ) ∣ ((x0 i₀ : ℤ) - (x2 i₀ : ℤ)) := by
          have := hdvd i₀
          rw [hden] at this
          simpa [neg_sub] using dvd_neg.mpr this
        have hmul := Int.ediv_mul_cancel hdi₀
        have hne : (x0 i₀ : ℤ) - (x2 i₀ : ℤ) ≠ 0 := by
          have := Fin.val_ne_of_ne hi₀
          omega
        intro h0
        dsimp [f] at h0
        rw [h0, zero_mul] at hmul
        exact hne hmul.symm
      · have hx0f : mkX0 f = x2 := rfl
        have hx2f : mkX2 f = x0 := by
          ext i
          have hv := mkX2_val f i
          have hdi : (k : ℤ) ∣ ((x0 i : ℤ) - (x2 i : ℤ)) := by
            have := hdvd i
            rw [hden] at this
            simpa [neg_sub] using dvd_neg.mpr this
          have hmul := Int.ediv_mul_cancel hdi
          have hv' : ((mkX2 f i : ℕ) : ℤ) = ((x2 i : ℕ) : ℤ) +
              (k : ℤ) * (((x0 i : ℤ) - (x2 i : ℤ)) / (k : ℤ)) := hv
          rw [mul_comm (k : ℤ), hmul] at hv'
          exact_mod_cast (by omega : ((mkX2 f i : ℕ) : ℤ) = ((x0 i : ℕ) : ℤ))
        have hx1f : mkX1 (Nat.le_of_succ_le hk) f = x1 := by
          ext i
          have hv := mkX1_val (Nat.le_of_succ_le hk) f i
          have hr := hrel i
          rw [hnum_rev, hden] at hr
          have hdi : (k : ℤ) ∣ ((x0 i : ℤ) - (x2 i : ℤ)) := by
            have := hdvd i
            rw [hden] at this
            simpa [neg_sub] using dvd_neg.mpr this
          have hmul := Int.ediv_mul_cancel hdi
          have hdeq : ((x0 i : ℤ) - (x2 i : ℤ)) / (k : ℤ) = (x1 i : ℤ) - (x2 i : ℤ) := by
            nlinarith
          have hv' : ((mkX1 (Nat.le_of_succ_le hk) f i : ℕ) : ℤ) =
              ((x2 i : ℕ) : ℤ) + ((x0 i : ℤ) - (x2 i : ℤ)) / (k : ℤ) := hv
          rw [hdeq] at hv'
          exact_mod_cast (by omega : ((mkX1 (Nat.le_of_succ_le hk) f i : ℕ) : ℤ) = ((x1 i : ℕ) : ℤ))
        rw [mkTriple, hx0f, hx1f, hx2f]
        ext z; simp; tauto
  rcases (by omega : q.den = 2 ∨ q.den = 3 ∨ q.den = 4) with h2 | h3 | h4
  · left
    apply build_mem 2 (by omega) 2 h2 (by omega)
    intro i
    have hdi := hdvd i
    rw [h2] at hdi
    have hmul := Int.ediv_mul_cancel hdi
    have h0 := (x0 i).isLt
    have h2l := (x2 i).isLt
    omega
  · right; left
    apply build_mem 3 (by omega) 1 h3 (by omega)
    intro i
    have hdi := hdvd i
    rw [h3] at hdi
    have hmul := Int.ediv_mul_cancel hdi
    have h0 := (x0 i).isLt
    have h2l := (x2 i).isLt
    omega
  · right; right
    have hcop4 := q.reduced
    rw [h4] at hcop4
    have hne2 : q.num ≠ 2 := by
      intro hq2
      rw [hq2] at hcop4
      norm_num at hcop4
    apply build_mem 4 (by omega) 1 h4 (by omega)
    intro i
    have hdi := hdvd i
    rw [h4] at hdi
    have hmul := Int.ediv_mul_cancel hdi
    have h0 := (x0 i).isLt
    have h2l := (x2 i).isLt
    omega

end OMA.P_oeis_a178298

theorem OMA.solution : type_of% @OMA.S_oeis_a178298.main := by
  intro n
  let S2 := (OMA.P_oeis_a178298.pairFinset n 2 2).image
    (OMA.P_oeis_a178298.mkTriple 2 (by omega) 2)
  let S3 := (OMA.P_oeis_a178298.pairFinset n 3 1).image
    (OMA.P_oeis_a178298.mkTriple 3 (by omega) 1)
  let S4 := (OMA.P_oeis_a178298.pairFinset n 4 1).image
    (OMA.P_oeis_a178298.mkTriple 4 (by omega) 1)
  have hset_eq :
      {s : Finset (Fin n → Fin 5) |
        s.card = 3 ∧ Collinear ℝ (OMA.S_oeis_a178298.toReal '' (s : Set (Fin n → Fin 5)))} =
        (↑(S2 ∪ S3 ∪ S4) : Set (Finset (Fin n → Fin 5))) := by
    ext s
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, S2, S3, S4, Finset.mem_union]
    constructor
    · rintro ⟨hs3, hscol⟩
      have hm := OMA.P_oeis_a178298.collinear_mem_classes hs3 hscol
      tauto
    · rintro ((hs2 | hs3) | hs4)
      · rcases Finset.mem_image.mp hs2 with ⟨f, hf, rfl⟩
        exact OMA.P_oeis_a178298.mkTriple_mem (by omega) hf
      · rcases Finset.mem_image.mp hs3 with ⟨f, hf, rfl⟩
        exact OMA.P_oeis_a178298.mkTriple_mem (by omega) hf
      · rcases Finset.mem_image.mp hs4 with ⟨f, hf, rfl⟩
        exact OMA.P_oeis_a178298.mkTriple_mem (by omega) hf
  have ha_card : OMA.S_oeis_a178298.a n = (S2 ∪ S3 ∪ S4).card := by
    rw [OMA.S_oeis_a178298.a, hset_eq, Set.ncard_coe_finset]
  have hdisj23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro s hs2 hs3
    rcases Finset.mem_image.mp hs2 with ⟨f, hf, rfl⟩
    rcases Finset.mem_image.mp hs3 with ⟨g, hg, heq⟩
    have h := OMA.P_oeis_a178298.mkTriple_eq_iff (by omega) (by omega) hf hg heq.symm
    rcases h with ⟨h23, _⟩ | ⟨_, h23, _⟩ <;> omega
  have hdisj24 : Disjoint S2 S4 := by
    rw [Finset.disjoint_left]
    intro s hs2 hs4
    rcases Finset.mem_image.mp hs2 with ⟨f, hf, rfl⟩
    rcases Finset.mem_image.mp hs4 with ⟨g, hg, heq⟩
    have h := OMA.P_oeis_a178298.mkTriple_eq_iff (by omega) (by omega) hf hg heq.symm
    rcases h with ⟨h24, _⟩ | ⟨_, h24, _⟩ <;> omega
  have hdisj34 : Disjoint S3 S4 := by
    rw [Finset.disjoint_left]
    intro s hs3 hs4
    rcases Finset.mem_image.mp hs3 with ⟨f, hf, rfl⟩
    rcases Finset.mem_image.mp hs4 with ⟨g, hg, heq⟩
    have h := OMA.P_oeis_a178298.mkTriple_eq_iff (by omega) (by omega) hf hg heq.symm
    rcases h with ⟨h34, _⟩ | ⟨h32, _, _⟩ <;> omega
  have hcard_all : (S2 ∪ S3 ∪ S4).card = S2.card + S3.card + S4.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj24, hdisj34⟩),
      Finset.card_union_of_disjoint hdisj23]
  have hS3_card : S3.card = (OMA.P_oeis_a178298.pairFinset n 3 1).card := by
    refine Finset.card_image_of_injOn ?_
    intro f hf g hg heq
    have h := OMA.P_oeis_a178298.mkTriple_eq_iff (by omega) (by omega) hf hg heq
    rcases h with ⟨_, hfg⟩ | ⟨h32, _, _⟩
    · exact funext (fun i => Subtype.ext (hfg i))
    · omega
  have hS4_card : S4.card = (OMA.P_oeis_a178298.pairFinset n 4 1).card := by
    refine Finset.card_image_of_injOn ?_
    intro f hf g hg heq
    have h := OMA.P_oeis_a178298.mkTriple_eq_iff (by omega) (by omega) hf hg heq
    rcases h with ⟨_, hfg⟩ | ⟨h42, _, _⟩
    · exact funext (fun i => Subtype.ext (hfg i))
    · omega
  have hS2_card : 2 * S2.card = (OMA.P_oeis_a178298.pairFinset n 2 2).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := OMA.P_oeis_a178298.pairFinset n 2 2)
      (t := S2)
      (f := OMA.P_oeis_a178298.mkTriple 2 (by omega) 2)
      (fun f hf => Finset.mem_image_of_mem _ hf)
    have htwo : ∀ s ∈ S2,
        ((OMA.P_oeis_a178298.pairFinset n 2 2).filter
          (fun g => OMA.P_oeis_a178298.mkTriple 2 (by omega) 2 g = s)).card = 2 := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨f, hf, rfl⟩
      let f' : Fin n → ↥(OMA.P_oeis_a178298.coordFinset 2 2) := fun i =>
        ⟨(OMA.P_oeis_a178298.mkX2 f i, -(f i).1.2), by
          simp only [OMA.P_oeis_a178298.coordFinset, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, OMA.P_oeis_a178298.mem_intIcc (by omega : (0 : ℤ) ≤ 2), true_and]
          have hp := (Finset.mem_filter.mp (f i).2).2
          have hv2 := OMA.P_oeis_a178298.mkX2_val f i
          dsimp [OMA.P_oeis_a178298.mkX0] at hv2
          have hx0 := (f i).1.1.isLt
          refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩ <;> omega⟩
      have hf' : f' ∈ OMA.P_oeis_a178298.pairFinset n 2 2 := by
        simp only [OMA.P_oeis_a178298.pairFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        rcases hf with ⟨i, hi⟩
        exact ⟨i, by dsimp [f']; omega⟩
      have hff' : f ≠ f' := by
        intro heq
        simp only [OMA.P_oeis_a178298.pairFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rcases hf with ⟨i, hi⟩
        have h2 := congrArg (fun p => (p i).1.2) heq
        dsimp [f'] at h2
        omega
      have heq_f' :
          OMA.P_oeis_a178298.mkTriple 2 (by omega) 2 f' =
            OMA.P_oeis_a178298.mkTriple 2 (by omega) 2 f := by
        have hx0 : OMA.P_oeis_a178298.mkX0 f' = OMA.P_oeis_a178298.mkX2 f := rfl
        have hx2 : OMA.P_oeis_a178298.mkX2 f' = OMA.P_oeis_a178298.mkX0 f := by
          ext i
          have hv := OMA.P_oeis_a178298.mkX2_val f' i
          have hv2 := OMA.P_oeis_a178298.mkX2_val f i
          dsimp [f', OMA.P_oeis_a178298.mkX0] at hv hv2 ⊢
          omega
        have hx1 : OMA.P_oeis_a178298.mkX1 (by omega) f' = OMA.P_oeis_a178298.mkX1 (by omega) f := by
          ext i
          have hv := OMA.P_oeis_a178298.mkX1_val (by omega) f' i
          have hv1 := OMA.P_oeis_a178298.mkX1_val (by omega) f i
          have hv2 := OMA.P_oeis_a178298.mkX2_val f i
          dsimp [f', OMA.P_oeis_a178298.mkX0] at hv hv1 hv2 ⊢
          omega
        simp only [OMA.P_oeis_a178298.mkTriple, hx0, hx1, hx2]
        ext z; simp; tauto
      have hset_eq :
          (OMA.P_oeis_a178298.pairFinset n 2 2).filter
              (fun g => OMA.P_oeis_a178298.mkTriple 2 (by omega) 2 g =
                OMA.P_oeis_a178298.mkTriple 2 (by omega) 2 f) = {f, f'} := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hg, hgeq⟩
          have h := OMA.P_oeis_a178298.mkTriple_eq_iff (by omega) (by omega) hf hg hgeq.symm
          rcases h with ⟨_, hfg⟩ | ⟨_, _, hfg⟩
          · left; exact funext (fun i => Subtype.ext (hfg i).symm)
          · right; exact funext (fun i => Subtype.ext (Prod.ext (hfg i).1 (hfg i).2))
        · rintro (rfl | rfl)
          · exact ⟨hf, rfl⟩
          · exact ⟨hf', heq_f'⟩
      rw [hset_eq, Finset.card_pair hff']
    rw [hfib, Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul]
    ring
  obtain ⟨h2le, h2card⟩ := OMA.P_oeis_a178298.pairFinset_card n 2 2 (by norm_num)
  obtain ⟨h3le, h3card⟩ := OMA.P_oeis_a178298.pairFinset_card n 3 1 (by norm_num)
  obtain ⟨h4le, h4card⟩ := OMA.P_oeis_a178298.pairFinset_card n 4 1 (by norm_num)
  rw [OMA.P_oeis_a178298.coordFinset_2_2] at h2le h2card
  rw [OMA.P_oeis_a178298.coordFinset_3_1] at h3le h3card
  rw [OMA.P_oeis_a178298.coordFinset_4_1] at h4le h4card
  have hfinalN :
      2 * OMA.S_oeis_a178298.a n =
        (13 ^ n - 5 ^ n) + 2 * (9 ^ n - 5 ^ n) + 2 * (7 ^ n - 5 ^ n) := by
    rw [ha_card, hcard_all, mul_add, mul_add, hS2_card, hS3_card, hS4_card, h2card, h3card, h4card]
  have hfinalZ :
      2 * (OMA.S_oeis_a178298.a n : ℤ) =
        ((13 ^ n - 5 ^ n : ℕ) : ℤ) + 2 * ((9 ^ n - 5 ^ n : ℕ) : ℤ) +
          2 * ((7 ^ n - 5 ^ n : ℕ) : ℤ) := by
    exact_mod_cast hfinalN
  rw [Int.ofNat_sub h2le, Int.ofNat_sub h3le, Int.ofNat_sub h4le] at hfinalZ
  push_cast at hfinalZ
  linarith
