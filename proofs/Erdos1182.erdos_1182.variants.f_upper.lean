import FormalConjectures.ErdosProblems.«1182»

/-! An alteration-method upper bound for the number of edges of a triangle-good graph. -/

open scoped Classical

namespace OMA

lemma weight_subset {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ)
    (T : Finset (Sym2 V)) :
    ∑ S ∈ (Finset.univ : Finset (Sym2 V)).powerset.filter (fun S => T ⊆ S),
        p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 V) - S.card) = p ^ T.card := by
  let E : Finset (Sym2 V) := Finset.univ
  let g : Sym2 V → ℝ := fun i => if i ∈ T then 0 else 1 - p
  have hsum : ∑ S ∈ E.powerset, (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i = p ^ T.card := by
    rw [← Finset.prod_add (fun _ : Sym2 V => p) g E]
    have hterm : ∀ i : Sym2 V, p + g i = if i ∈ T then p else 1 := by
      intro i
      by_cases hi : i ∈ T <;> simp [g, hi]
    simp_rw [hterm]
    rw [Finset.prod_ite_mem_eq]
    simp
  change ∑ S ∈ E.powerset.filter (fun S => T ⊆ S),
      p ^ S.card * (1 - p) ^ (E.card - S.card) = p ^ T.card
  have hzero : ∀ S ∈ E.powerset, ¬ T ⊆ S →
      (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i = 0 := by
    intro S hS hnot
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hnot
    have hiES : i ∈ E \ S := by simp [E, hiS]
    have hz : (∏ j ∈ E \ S, g j) = 0 := Finset.prod_eq_zero hiES (by simp [g, hiT])
    simp [hz]
  calc
    ∑ S ∈ E.powerset.filter (fun S => T ⊆ S),
        p ^ S.card * (1 - p) ^ (E.card - S.card) =
        ∑ S ∈ E.powerset.filter (fun S => T ⊆ S),
          (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i := by
            apply Finset.sum_congr rfl
            intro S hS
            have hsub : S ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
            have hTS : T ⊆ S := (Finset.mem_filter.mp hS).2
            have hg : (∏ i ∈ E \ S, g i) = (1 - p) ^ (E \ S).card := by
              calc
                (∏ i ∈ E \ S, g i) = ∏ i ∈ E \ S, (1 - p) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  have hiT : i ∉ T := fun h => (Finset.mem_sdiff.mp hi).2 (hTS h)
                  simp [g, hiT]
                _ = (1 - p) ^ (E \ S).card := by simp
            rw [Finset.prod_const, hg, Finset.card_sdiff_of_subset hsub]
    _ = ∑ S ∈ E.powerset, (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i := by
            apply Eq.symm
            calc
              ∑ S ∈ E.powerset, (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i =
                  ∑ S ∈ E.powerset, if T ⊆ S then
                    (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i else 0 := by
                      apply Finset.sum_congr rfl
                      intro S hS
                      by_cases h : T ⊆ S
                      · simp [h]
                      · have hz := hzero S hS h
                        rw [if_neg h, hz]
              _ = ∑ S ∈ E.powerset.filter (fun S => T ⊆ S),
                    (∏ i ∈ S, p) * ∏ i ∈ E \ S, g i := by
                      rw [Finset.sum_filter]
    _ = p ^ T.card := hsum

lemma weight_chernoff {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ)
    (F : Finset (Sym2 V)) :
    ∑ S ∈ (Finset.univ : Finset (Sym2 V)).powerset,
        p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 V) - S.card) *
          (1 / 2 : ℝ) ^ (S ∩ F).card = (1 - p / 2) ^ F.card := by
  let E : Finset (Sym2 V) := Finset.univ
  let f : Sym2 V → ℝ := fun i => if i ∈ F then p / 2 else p
  let g : Sym2 V → ℝ := fun _ => 1 - p
  calc
    ∑ S ∈ E.powerset, p ^ S.card * (1 - p) ^ (E.card - S.card) *
          (1 / 2 : ℝ) ^ (S ∩ F).card =
        ∑ S ∈ E.powerset, (∏ i ∈ S, f i) * ∏ i ∈ E \ S, g i := by
          apply Finset.sum_congr rfl
          intro S hS
          have hsub : S ⊆ E := Finset.mem_powerset.mp hS
          rw [← Finset.card_sdiff_of_subset hsub]
          have hfprod : (∏ i ∈ S, f i) = p ^ S.card * (1 / 2 : ℝ) ^ (S ∩ F).card := by
            have hf' : ∀ i, f i = p * (if i ∈ F then (1 / 2 : ℝ) else 1) := by
              intro i
              by_cases hi : i ∈ F <;> simp [f, hi, div_eq_mul_inv]
            simp_rw [hf']
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            have hite : (∏ x ∈ S, if x ∈ F then (1 / 2 : ℝ) else 1) =
                (1 / 2 : ℝ) ^ (S ∩ F).card := by
              rw [← Finset.prod_filter_mul_prod_filter_not S (fun x => x ∈ F)
                (fun x => if x ∈ F then (1 / 2 : ℝ) else 1)]
              have h1 : (∏ x ∈ S with x ∈ F,
                  if x ∈ F then (1 / 2 : ℝ) else 1) = (1 / 2 : ℝ) ^ (S ∩ F).card := by
                calc
                  (∏ x ∈ S with x ∈ F, if x ∈ F then (1 / 2 : ℝ) else 1) =
                      ∏ x ∈ S with x ∈ F, (1 / 2 : ℝ) := by
                        apply Finset.prod_congr rfl
                        intro x hx
                        simp [(Finset.mem_filter.mp hx).2]
                  _ = (1 / 2 : ℝ) ^ (S.filter (fun x => x ∈ F)).card := by simp
                  _ = (1 / 2 : ℝ) ^ (S ∩ F).card := by rfl
              have h2 : (∏ x ∈ S with ¬ x ∈ F,
                  if x ∈ F then (1 / 2 : ℝ) else 1) = 1 := by
                apply Finset.prod_eq_one
                intro x hx
                simp [(Finset.mem_filter.mp hx).2]
              rw [h1, h2, mul_one]
            rw [hite]
          rw [hfprod]
          simp [g, Finset.prod_const]
          ring
    _ = ∏ i ∈ E, (f i + g i) := (Finset.prod_add f g E).symm
    _ = (1 - p / 2) ^ F.card := by
      have hfg : ∀ i : Sym2 V, f i + g i = if i ∈ F then 1 - p / 2 else 1 := by
        intro i
        by_cases hi : i ∈ F
        · simp [f, g, hi, div_eq_mul_inv]
          ring
        · simp [f, g, hi, div_eq_mul_inv]
      simp_rw [hfg]
      rw [Finset.prod_ite_mem_eq]
      simp

def tE {N : ℕ} (abc : Fin N × Fin N × Fin N) : Finset (Sym2 (Fin N)) :=
  {s(abc.1, abc.2.1), s(abc.1, abc.2.2), s(abc.2.1, abc.2.2)}

def ts (N : ℕ) : Finset (Fin N × Fin N × Fin N) :=
  Finset.univ.filter fun abc => abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2

lemma tripleEdges_card {N : ℕ} {abc : Fin N × Fin N × Fin N}
    (h : abc ∈ ts N) : (tE abc).card = 3 := by
  rcases abc with ⟨a, b, c⟩
  simp only [ts, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hab_ac : s(a, b) ≠ s(a, c) := by
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, hbc⟩ | ⟨hac, hba⟩ <;> subst_vars <;> simp_all
  have hab_bc : s(a, b) ≠ s(b, c) := by
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hab, hbc⟩ | ⟨hac, _⟩ <;> subst_vars <;> simp_all
  have hac_bc : s(a, c) ≠ s(b, c) := by
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hab, _⟩ | ⟨hac, hcb⟩ <;> subst_vars <;> simp_all
  simp [tE, hab_ac, hab_bc, hac_bc]

lemma weight_triples {N : ℕ} (p : ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Sym2 (Fin N))).powerset,
        p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 (Fin N)) - S.card) *
          ((ts N).filter (fun abc => tE abc ⊆ S)).card =
      ((ts N).card : ℝ) * p ^ 3 := by
  classical
  let Ω := (Finset.univ : Finset (Sym2 (Fin N))).powerset
  let w : Finset (Sym2 (Fin N)) → ℝ := fun S =>
    p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 (Fin N)) - S.card)
  calc
    ∑ S ∈ Ω, w S * ((ts N).filter (fun abc => tE abc ⊆ S)).card =
        ∑ S ∈ Ω, w S * ∑ abc ∈ ts N,
          (if tE abc ⊆ S then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [← Finset.sum_boole (fun abc => tE abc ⊆ S) (ts N)]
    _ = ∑ abc ∈ ts N, ∑ S ∈ Ω,
          w S * (if tE abc ⊆ S then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro abc habc
            rw [Finset.mul_sum]
    _ = ∑ abc ∈ ts N, p ^ 3 := by
            apply Finset.sum_congr rfl
            intro abc habc
            have hcard := tripleEdges_card habc
            calc
              ∑ S ∈ Ω, w S * (if tE abc ⊆ S then (1 : ℝ) else 0) =
                  ∑ S ∈ Ω.filter (fun S => tE abc ⊆ S), w S := by
                    rw [Finset.sum_filter]
                    apply Finset.sum_congr rfl
                    intro S hS
                    by_cases h : tE abc ⊆ S <;> simp [h]
              _ = p ^ (tE abc).card := by
                    simpa [Ω, w] using weight_subset p (tE abc)
              _ = p ^ 3 := by rw [hcard]
    _ = ((ts N).card : ℝ) * p ^ 3 := by simp

lemma embedding_card_le (n N : ℕ) : Fintype.card (Fin n ↪ Fin N) ≤ N ^ n := by
  calc
    Fintype.card (Fin n ↪ Fin N) ≤ Fintype.card (Fin n → Fin N) := by
      apply Fintype.card_le_of_injective (fun f : Fin n ↪ Fin N => (f : Fin n → Fin N))
      intro f g h
      ext i
      exact congrArg Fin.val (congrFun h i)
    _ = N ^ n := by simp

noncomputable def Astat (n : ℕ) : ℝ := (n : ℝ) ^ (5 / 3 : ℝ) * (Real.log n) ^ (2 / 3 : ℝ)

lemma astat_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Astat n := by
  unfold Astat
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  positivity

lemma log_le_sq (n : ℕ) : Real.log n ≤ (n : ℝ) ^ 2 := by
  by_cases h0 : n = 0
  · subst n
    norm_num
  · have hp : 0 < (n : ℝ) := by norm_cast; omega
    have h := Real.log_le_sub_one_of_pos hp
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

lemma not_good_of_sample (n N : ℕ) (hn : 2 ≤ n) (hN : N = 2 * n - 1)
    (G : SimpleGraph (Fin n))
    (S0 : Finset (Sym2 (Fin N)))
    (htri : (((ts N).filter (fun abc => tE abc ⊆ S0)).card : ℝ) <
      10 * (n : ℝ) * Real.log n)
    (hF : ∀ φ : Fin n ↪ Fin N,
      10 * (n : ℝ) * Real.log n <
        ((S0 ∩ G.edgeFinset.image (Sym2.map (φ : Fin n → Fin N))).card : ℝ)) :
    ¬ Erdos1182.IsTriangleGood G := by
  classical
  subst N
  let N : ℕ := 2 * n - 1
  let Bad := (ts N).filter (fun abc => tE abc ⊆ S0)
  let D : Finset (Sym2 (Fin N)) := Bad.image (fun abc => s(abc.1, abc.2.1))
  let S1 : Finset (Sym2 (Fin N)) := S0 \ D
  let H : SimpleGraph (Fin N) := SimpleGraph.fromEdgeSet (S1 : Set (Sym2 (Fin N)))
  have hDs0 : D ⊆ S0 := by
    intro e he
    obtain ⟨abc, habc, rfl⟩ := Finset.mem_image.mp he
    have hsub : tE abc ⊆ S0 := (Finset.mem_filter.mp habc).2
    exact hsub (by simp [tE])
  have hDcard : D.card ≤ Bad.card := Finset.card_image_le
  have hS1tri : ∀ {a b c : Fin N}, a ≠ b → a ≠ c → b ≠ c →
      ¬ (s(a, b) ∈ S1 ∧ s(a, c) ∈ S1 ∧ s(b, c) ∈ S1) := by
    intro a b c hab hac hbc hmem
    let abc : Fin N × Fin N × Fin N := (a, b, c)
    have habc : abc ∈ Bad := by
      apply Finset.mem_filter.mpr
      constructor
      · simp [abc, ts, hab, hac, hbc]
      · intro e he
        simp only [tE, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact (Finset.mem_sdiff.mp hmem.1).1
        · exact (Finset.mem_sdiff.mp hmem.2.1).1
        · exact (Finset.mem_sdiff.mp hmem.2.2).1
    have hDmem : s(a, b) ∈ D := Finset.mem_image.mpr ⟨abc, habc, rfl⟩
    exact (Finset.mem_sdiff.mp hmem.1).2 hDmem
  have hnoK3 : ¬ SimpleGraph.IsContained (⊤ : SimpleGraph (Fin 3)) H := by
    rintro ⟨f⟩
    have h01 : s(f 0, f 1) ∈ S1 := by
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj (0 : Fin 3) 1 := by simp
      have hH := f.toHom.map_adj hadj
      simpa [H, SimpleGraph.fromEdgeSet_adj] using hH.1
    have h02 : s(f 0, f 2) ∈ S1 := by
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj (0 : Fin 3) 2 := by simp
      have hH := f.toHom.map_adj hadj
      simpa [H, SimpleGraph.fromEdgeSet_adj] using hH.1
    have h12 : s(f 1, f 2) ∈ S1 := by
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj (1 : Fin 3) 2 := by simp
      have hH := f.toHom.map_adj hadj
      simpa [H, SimpleGraph.fromEdgeSet_adj] using hH.1
    exact hS1tri
      (fun h => by have := f.injective h; omega)
      (fun h => by have := f.injective h; omega)
      (fun h => by have := f.injective h; omega)
      ⟨h01, h02, h12⟩
  have hnoG : ¬ SimpleGraph.IsContained G Hᶜ := by
    rintro ⟨φ⟩
    let ιφ : Fin n ↪ Fin N := φ.toEmbedding
    let Fφ : Finset (Sym2 (Fin N)) := G.edgeFinset.image (Sym2.map (ιφ : Fin n → Fin N))
    have hsub : S0 ∩ Fφ ⊆ (S1 ∩ Fφ) ∪ (D ∩ Fφ) := by
      intro e he
      have heS0 : e ∈ S0 := (Finset.mem_inter.mp he).1
      have heF : e ∈ Fφ := (Finset.mem_inter.mp he).2
      by_cases heD : e ∈ D
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨heD, heF⟩))
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨heS0, heD⟩, heF⟩))
    have hcard : (S0 ∩ Fφ).card ≤ (S1 ∩ Fφ).card + D.card := by
      calc
        (S0 ∩ Fφ).card ≤ ((S1 ∩ Fφ) ∪ (D ∩ Fφ)).card := Finset.card_le_card hsub
        _ ≤ (S1 ∩ Fφ).card + (D ∩ Fφ).card := Finset.card_union_le _ _
        _ ≤ (S1 ∩ Fφ).card + D.card := add_le_add_right (Finset.card_le_card (Finset.inter_subset_left)) _
    have htri' : (Bad.card : ℝ) < 10 * (n : ℝ) * Real.log n := by simpa [Bad] using htri
    have hDleR : (D.card : ℝ) ≤ (Bad.card : ℝ) := by exact_mod_cast hDcard
    have hDlt : (D.card : ℝ) < 10 * (n : ℝ) * Real.log n := lt_of_le_of_lt hDleR htri'
    have hSlarge : 0 < (S1 ∩ Fφ).card := by
      by_contra hz
      have hzero : (S1 ∩ Fφ).card = 0 := Nat.eq_zero_of_not_pos hz
      have hle : ((S0 ∩ Fφ).card : ℝ) ≤ (D.card : ℝ) := by
        exact_mod_cast (by simpa [hzero] using hcard)
      linarith [hF ιφ]
    obtain ⟨e, he⟩ := Finset.card_pos.mp hSlarge
    have heS1 : e ∈ S1 := (Finset.mem_inter.mp he).1
    have heF : e ∈ Fφ := (Finset.mem_inter.mp he).2
    obtain ⟨g, hg, hge⟩ := Finset.mem_image.mp heF
    have hex : ∃ a b : Fin n, s(a, b) = g := by
      refine Sym2.inductionOn g ?_
      intro a b
      exact ⟨a, b, rfl⟩
    obtain ⟨a, b, hgab⟩ := hex
    have hgset : g ∈ G.edgeSet := by simpa using hg
    have hAdjG : G.Adj a b := by
      rw [← SimpleGraph.mem_edgeSet]
      rw [hgab]
      exact hgset
    have hSym : s(ιφ a, ιφ b) ∈ S1 := by
      have hmap : Sym2.map (ιφ : Fin n → Fin N) s(a, b) = e := by
        rw [hgab, hge]
      rw [← Sym2.map_mk (ιφ : Fin n → Fin N) a b]
      rw [hmap]
      exact heS1
    have hadjH : H.Adj (φ a) (φ b) := by
      change (SimpleGraph.fromEdgeSet (S1 : Set (Sym2 (Fin N)))).Adj (φ a) (φ b)
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hSym, fun h => hAdjG.ne (ιφ.injective h)⟩
    have hnot : ¬ H.Adj (φ a) (φ b) :=
      ((SimpleGraph.compl_adj H (φ a) (φ b)).mp (φ.toHom.map_adj hAdjG)).2
    exact hnot hadjH
  unfold Erdos1182.IsTriangleGood SimpleGraph.graphRamsey
  let good : Set ℕ := {N | ∀ C : SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ}
  change sInf good ≠ 2 * n - 1
  intro heq
  by_cases hne : good.Nonempty
  · have hmem' : ∀ C : SimpleGraph (Fin (2 * n - 1)),
        (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ := by
      change 2 * n - 1 ∈ good
      simpa [heq] using (Nat.sInf_mem hne : sInf good ∈ good)
    exact (hmem' H).elim hnoK3 hnoG
  · have hempty : good = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at heq
    simp at heq
    omega

noncomputable def prob (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-2 / 3 : ℝ) * (Real.log n) ^ (1 / 3 : ℝ)

lemma prob_nonneg (n : ℕ) : 0 ≤ prob n := by
  unfold prob
  positivity

lemma prob_le_one (n : ℕ) (hn : 2 ≤ n) : prob n ≤ 1 := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlogle := log_le_sq n
  have hroot : (Real.log n) ^ (1 / 3 : ℝ) ≤ ((n : ℝ) ^ 2) ^ (1 / 3 : ℝ) := by
    exact Real.rpow_le_rpow hlpos.le hlogle (by norm_num)
  have hroot_eq : ((n : ℝ) ^ 2) ^ (1 / 3 : ℝ) = (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hnpos.le]
    norm_num
  rw [hroot_eq] at hroot
  unfold prob
  calc
    (n : ℝ) ^ (-2 / 3 : ℝ) * (Real.log n) ^ (1 / 3 : ℝ) ≤
        (n : ℝ) ^ (-2 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = 1 := by
      rw [← Real.rpow_add hnpos]
      norm_num

lemma cube_prob (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ 3 * (prob n) ^ 3 = (n : ℝ) * Real.log n := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hn3 : ((n : ℝ) ^ (-2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hl3 : ((Real.log n) ^ (1 / 3 : ℝ)) ^ 3 = Real.log n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlpos.le]
    norm_num
  unfold prob
  rw [mul_pow, hn3, hl3, ← mul_assoc]
  have hnp : (n : ℝ) ^ 3 * (n : ℝ) ^ (-2 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
    norm_num
  rw [hnp]

lemma prob_mul_astat (n : ℕ) (hn : 2 ≤ n) :
    prob n * Astat n = (n : ℝ) * Real.log n := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  unfold prob Astat
  calc
    _ = ((n : ℝ) ^ (-2 / 3 : ℝ) * (n : ℝ) ^ (5 / 3 : ℝ)) *
          ((Real.log n) ^ (1 / 3 : ℝ) * (Real.log n) ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hnpos, ← Real.rpow_add hlpos]
      norm_num <;> simp

lemma triangle_expect_bound (n : ℕ) (hn : 2 ≤ n) :
    let N := 2 * n - 1
    let Ω := (Finset.univ : Finset (Sym2 (Fin N))).powerset
    ∑ S ∈ Ω, (prob n) ^ S.card * (1 - prob n) ^ (Fintype.card (Sym2 (Fin N)) - S.card) *
      ((ts N).filter (fun abc => tE abc ⊆ S)).card ≤
        8 * (n : ℝ) * Real.log n := by
  classical
  dsimp only
  let N := 2 * n - 1
  have htri_card : (ts N).card ≤ N ^ 3 := by
    calc
      (ts N).card ≤ (Finset.univ : Finset (Fin N × Fin N × Fin N)).card :=
        Finset.card_le_card (by intro x hx; simp)
      _ = N ^ 3 := by simp [pow_succ, mul_assoc]
  have hNle : N ≤ 2 * n := by dsimp [N]; omega
  have htriR : ((ts N).card : ℝ) ≤ 8 * (n : ℝ) ^ 3 := by
    have h1 : ((ts N).card : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast htri_card
    have h2 : (N : ℝ) ^ 3 ≤ (2 * (n : ℝ)) ^ 3 := by
      gcongr
      exact_mod_cast hNle
    have h3 : (2 * (n : ℝ)) ^ 3 = 8 * (n : ℝ) ^ 3 := by ring
    linarith
  have hexp := weight_triples (prob n) (N := N)
  calc
    ∑ S ∈ (Finset.univ : Finset (Sym2 (Fin N))).powerset,
        (prob n) ^ S.card * (1 - prob n) ^ (Fintype.card (Sym2 (Fin N)) - S.card) *
          ((ts N).filter (fun abc => tE abc ⊆ S)).card =
        ((ts N).card : ℝ) * (prob n) ^ 3 := hexp
    _ ≤ (8 * (n : ℝ) ^ 3) * (prob n) ^ 3 := by
      exact mul_le_mul_of_nonneg_right htriR (pow_nonneg (prob_nonneg n) 3)
    _ = 8 * ((n : ℝ) ^ 3 * (prob n) ^ 3) := by ring
    _ = 8 * ((n : ℝ) * Real.log n) := by rw [cube_prob n hn]
    _ = 8 * (n : ℝ) * Real.log n := by ring

lemma triangle_bad_weight (n : ℕ) (hn : 2 ≤ n) :
    let N := 2 * n - 1
    let Ω := (Finset.univ : Finset (Sym2 (Fin N))).powerset
    let c : ℝ := 10 * (n : ℝ) * Real.log n
    ∑ S ∈ Ω.filter (fun S => c ≤
        (((ts N).filter (fun abc => tE abc ⊆ S)).card : ℝ)),
        (prob n) ^ S.card * (1 - prob n) ^ (Fintype.card (Sym2 (Fin N)) - S.card) ≤ 4 / 5 := by
  classical
  dsimp only
  let N := 2 * n - 1
  let Ω := (Finset.univ : Finset (Sym2 (Fin N))).powerset
  let p := prob n
  let w : Finset (Sym2 (Fin N)) → ℝ := fun S =>
    p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 (Fin N)) - S.card)
  let c : ℝ := 10 * (n : ℝ) * Real.log n
  let T : Finset (Sym2 (Fin N)) → ℕ := fun S =>
    ((ts N).filter (fun abc => tE abc ⊆ S)).card
  have hp0 : 0 ≤ p := by dsimp [p]; exact prob_nonneg n
  have hp1 : p ≤ 1 := by dsimp [p]; exact prob_le_one n hn
  have hw : ∀ S, 0 ≤ w S := by
    intro S
    dsimp [w]
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  have hlpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hmarkov : c * (∑ S ∈ Ω.filter (fun S => c ≤ (T S : ℝ)), w S) ≤
      ∑ S ∈ Ω, w S * (T S : ℝ) := by
    calc
      c * (∑ S ∈ Ω.filter (fun S => c ≤ (T S : ℝ)), w S) =
          ∑ S ∈ Ω.filter (fun S => c ≤ (T S : ℝ)), c * w S := by rw [Finset.mul_sum]
      _ ≤ ∑ S ∈ Ω.filter (fun S => c ≤ (T S : ℝ)), w S * (T S : ℝ) := by
        apply Finset.sum_le_sum
        intro S hS
        have hcT : c ≤ (T S : ℝ) := (Finset.mem_filter.mp hS).2
        have hw0 := hw S
        nlinarith
      _ ≤ ∑ S ∈ Ω, w S * (T S : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          exact (Finset.mem_filter.mp hS).1
        · intro S hS hnot
          exact mul_nonneg (hw S) (by positivity : 0 ≤ (T S : ℝ))
  have hexp : ∑ S ∈ Ω, w S * (T S : ℝ) ≤ 8 * (n : ℝ) * Real.log n := by
    simpa [Ω, w, p, T, N] using triangle_expect_bound n hn
  have htot : c * (∑ S ∈ Ω.filter (fun S => c ≤ (T S : ℝ)), w S) ≤
      8 * (n : ℝ) * Real.log n := le_trans hmarkov hexp
  have hceq : 8 * (n : ℝ) * Real.log n = (4 / 5 : ℝ) * c := by
    dsimp [c]
    ring
  have hres : ∑ S ∈ Ω.filter (fun S => c ≤ (T S : ℝ)), w S ≤ 4 / 5 := by
    nlinarith
  simpa [Ω, w, p, T, c, N] using hres

lemma chernoff_tail_real {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset (Sym2 V)) (m : ℝ) (_hm0 : 0 ≤ m) :
    ∑ S ∈ (Finset.univ : Finset (Sym2 V)).powerset.filter
        (fun S => ((S ∩ F).card : ℝ) ≤ m),
        p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 V) - S.card) ≤
      (2 : ℝ) ^ m * (1 - p / 2) ^ F.card := by
  classical
  let Ω := (Finset.univ : Finset (Sym2 V)).powerset
  let w : Finset (Sym2 V) → ℝ := fun S =>
    p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 V) - S.card)
  have hw : ∀ S, 0 ≤ w S := by
    intro S
    dsimp [w]
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  have hterm : ∀ S ∈ Ω.filter (fun S => ((S ∩ F).card : ℝ) ≤ m),
      w S ≤ (2 : ℝ) ^ m * (w S * (1 / 2 : ℝ) ^ (S ∩ F).card) := by
    intro S hS
    have hk : ((S ∩ F).card : ℝ) ≤ m := (Finset.mem_filter.mp hS).2
    have hpowk : (2 : ℝ) ^ ((S ∩ F).card : ℝ) ≤ (2 : ℝ) ^ m :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
    have hkpow : (2 : ℝ) ^ ((S ∩ F).card : ℝ) = (2 : ℝ) ^ (S ∩ F).card :=
      Real.rpow_natCast _ _
    rw [hkpow] at hpowk
    have hcancel : (2 : ℝ) ^ (S ∩ F).card * (1 / 2 : ℝ) ^ (S ∩ F).card = 1 := by
      rw [← mul_pow]
      norm_num
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (S ∩ F).card := by positivity
    have hone : 1 ≤ (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (S ∩ F).card := by
      have hmul := mul_le_mul_of_nonneg_right hpowk hnonneg
      nlinarith
    have hw0 := hw S
    nlinarith
  calc
    ∑ S ∈ Ω.filter (fun S => ((S ∩ F).card : ℝ) ≤ m), w S ≤
        ∑ S ∈ Ω.filter (fun S => ((S ∩ F).card : ℝ) ≤ m),
          (2 : ℝ) ^ m * (w S * (1 / 2 : ℝ) ^ (S ∩ F).card) := by
            exact Finset.sum_le_sum hterm
    _ ≤ ∑ S ∈ Ω, (2 : ℝ) ^ m * (w S * (1 / 2 : ℝ) ^ (S ∩ F).card) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro S hS
              exact (Finset.mem_filter.mp hS).1
            · intro S hS hnot
              positivity
    _ = (2 : ℝ) ^ m * ∑ S ∈ Ω, w S * (1 / 2 : ℝ) ^ (S ∩ F).card := by
            rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ m * (1 - p / 2) ^ F.card := by
            rw [show ∑ S ∈ Ω, w S * (1 / 2 : ℝ) ^ (S ∩ F).card =
              (1 - p / 2) ^ F.card by simpa [Ω, w] using weight_chernoff p F]

lemma sym2_map_injective {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro x y hxy
  revert hxy
  refine Sym2.inductionOn₂ x y ?_
  intro a b c d hcd
  rw [Sym2.map_mk, Sym2.map_mk] at hcd
  rw [Sym2.eq_iff] at hcd ⊢
  rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hf h1, hf h2⟩
  · exact Or.inr ⟨hf h1, hf h2⟩

lemma tail_exp_bound (n : ℕ) (hn : 2 ≤ n) (q : ℕ)
    (hq : 1000 * Astat n ≤ (q : ℝ)) :
    (2 : ℝ) ^ (10 * (n : ℝ) * Real.log n) * (1 - prob n / 2) ^ q ≤
      Real.exp (-490 * (n : ℝ) * Real.log n) := by
  have hp0 : 0 ≤ prob n := prob_nonneg n
  have hp1 : prob n ≤ 1 := prob_le_one n hn
  have hlpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hc0 : 0 ≤ 10 * (n : ℝ) * Real.log n := by positivity
  have hbase0 : 0 ≤ 1 - prob n / 2 := by nlinarith
  have hbase_le : 1 - prob n / 2 ≤ Real.exp (-(prob n) / 2) := by
    have h := Real.add_one_le_exp (-(prob n) / 2)
    nlinarith
  have hpow_le : (1 - prob n / 2) ^ q ≤ (Real.exp (-(prob n) / 2)) ^ q :=
    pow_le_pow_left₀ hbase0 hbase_le q
  have hmul0 := mul_le_mul_of_nonneg_right hq hp0
  have hleft : (1000 * Astat n) * prob n = 1000 * ((n : ℝ) * Real.log n) := by
    have hpA := prob_mul_astat n hn
    nlinarith
  rw [hleft] at hmul0
  have hexp_pow : (Real.exp (-(prob n) / 2)) ^ q =
      Real.exp (-((q : ℝ) * prob n) / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hneg : -((q : ℝ) * prob n) / 2 ≤ -500 * (n : ℝ) * Real.log n := by
    nlinarith
  have hpow_final : (1 - prob n / 2) ^ q ≤ Real.exp (-500 * (n : ℝ) * Real.log n) := by
    exact le_trans hpow_le (by
      rw [hexp_pow]
      exact Real.exp_le_exp.mpr hneg)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have htwopow : (2 : ℝ) ^ (10 * (n : ℝ) * Real.log n) ≤
      Real.exp (10 * (n : ℝ) * Real.log n) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg hlog2nonneg hc0,
      mul_nonneg (sub_nonneg.mpr hlog2le) hc0]
  calc
    (2 : ℝ) ^ (10 * (n : ℝ) * Real.log n) * (1 - prob n / 2) ^ q ≤
        Real.exp (10 * (n : ℝ) * Real.log n) * Real.exp (-500 * (n : ℝ) * Real.log n) := by
          exact mul_le_mul htwopow hpow_final (pow_nonneg hbase0 q) (Real.exp_pos _).le
    _ = Real.exp (-490 * (n : ℝ) * Real.log n) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma embeddings_le_exp (n : ℕ) (hn : 2 ≤ n) :
    (Fintype.card (Fin n ↪ Fin (2 * n - 1)) : ℝ) ≤
      Real.exp (2 * (n : ℝ) * Real.log n) := by
  have hcard := embedding_card_le n (2 * n - 1)
  have hcardR : (Fintype.card (Fin n ↪ Fin (2 * n - 1)) : ℝ) ≤
      ((2 * n - 1 : ℕ) : ℝ) ^ n := by exact_mod_cast hcard
  have hNle : ((2 * n - 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show 2 * n - 1 ≤ 2 * n by omega)
  have hpowN : (((2 * n - 1 : ℕ) : ℝ) ^ n) ≤ (2 * (n : ℝ)) ^ n := by
    gcongr
  have hlogmul : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log n := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
    have hlog2lelogn : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hpoweq : (2 * (n : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log (2 * (n : ℝ))) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have hpowle : Real.exp ((n : ℝ) * Real.log (2 * (n : ℝ))) ≤
      Real.exp (2 * (n : ℝ) * Real.log n) := by
    apply Real.exp_le_exp.mpr
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  exact le_trans (le_trans hcardR hpowN) (by rw [hpoweq]; exact hpowle)

lemma edgeFinset_card_eq_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.edgeFinset.card = G.edgeSet.ncard := by
  classical
  simpa [SimpleGraph.edgeFinset] using (Set.ncard_eq_toFinset_card G.edgeSet).symm

lemma exp_small (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-488 * (n : ℝ) * Real.log n) < 1 / 5 := by
  have hlog5_le : Real.log 5 ≤ 3 * Real.log 2 := by
    have hlog_mono : Real.log (5 : ℝ) ≤ Real.log 8 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2lelogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) hn2
  have h1 : 2 * Real.log 2 ≤ (n : ℝ) * Real.log n := by
    have hm := mul_le_mul hlog2lelogn hn2 (by norm_num : (0 : ℝ) ≤ 2)
      (Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)))
    nlinarith
  have hbig : Real.log 5 < 488 * (n : ℝ) * Real.log n := by
    nlinarith
  have hlt : Real.exp (-488 * (n : ℝ) * Real.log n) < Real.exp (-Real.log 5) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hexplog5 : Real.exp (-Real.log 5) = (1 / 5 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    norm_num
  rw [hexplog5] at hlt
  exact hlt

lemma sample_exists (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hq : 1000 * Astat n ≤ (G.edgeSet.ncard : ℝ)) :
    ∃ S0 ∈ (Finset.univ : Finset (Sym2 (Fin (2 * n - 1)))).powerset,
      (((ts (2 * n - 1)).filter (fun abc => tE abc ⊆ S0)).card : ℝ) <
        10 * (n : ℝ) * Real.log n ∧
      ∀ φ : Fin n ↪ Fin (2 * n - 1),
        10 * (n : ℝ) * Real.log n <
          ((S0 ∩ G.edgeFinset.image (Sym2.map (φ : Fin n → Fin (2 * n - 1)))).card : ℝ) := by
  classical
  let N := 2 * n - 1
  let Ω := (Finset.univ : Finset (Sym2 (Fin N))).powerset
  let p := prob n
  let w : Finset (Sym2 (Fin N)) → ℝ := fun S =>
    p ^ S.card * (1 - p) ^ (Fintype.card (Sym2 (Fin N)) - S.card)
  let c : ℝ := 10 * (n : ℝ) * Real.log n
  let T : Finset (Sym2 (Fin N)) → ℕ := fun S =>
    ((ts N).filter (fun abc => tE abc ⊆ S)).card
  let Fφ : (Fin n ↪ Fin N) → Finset (Sym2 (Fin N)) := fun φ =>
    G.edgeFinset.image (Sym2.map (φ : Fin n → Fin N))
  let Bφ : (Fin n ↪ Fin N) → Finset (Finset (Sym2 (Fin N))) := fun φ =>
    Ω.filter (fun S => ((S ∩ Fφ φ).card : ℝ) ≤ c)
  let A := Ω.filter (fun S => c ≤ (T S : ℝ))
  let B := Finset.univ.biUnion Bφ
  have hp0 : 0 ≤ p := by dsimp [p]; exact prob_nonneg n
  have hp1 : p ≤ 1 := by dsimp [p]; exact prob_le_one n hn
  have hw : ∀ S, 0 ≤ w S := by
    intro S
    dsimp [w]
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  have hA : ∑ S ∈ A, w S ≤ 4 / 5 := by
    simpa [A, Ω, w, p, c, T, N] using triangle_bad_weight n hn
  have hFcard : ∀ φ : Fin n ↪ Fin N, (Fφ φ).card = G.edgeSet.ncard := by
    intro φ
    dsimp [Fφ]
    rw [Finset.card_image_of_injective]
    · exact edgeFinset_card_eq_ncard G
    · exact sym2_map_injective (φ : Fin n → Fin N) φ.injective
  have hBφ_bound : ∀ φ : Fin n ↪ Fin N,
      ∑ S ∈ Bφ φ, w S ≤ Real.exp (-490 * (n : ℝ) * Real.log n) := by
    intro φ
    calc
      ∑ S ∈ Bφ φ, w S ≤ (2 : ℝ) ^ c * (1 - p / 2) ^ (Fφ φ).card := by
        simpa [Bφ, Ω, w, p, c] using
          chernoff_tail_real p hp0 hp1 (Fφ φ) c (by positivity)
      _ = (2 : ℝ) ^ c * (1 - p / 2) ^ (G.edgeSet.ncard) := by rw [hFcard φ]
      _ ≤ Real.exp (-490 * (n : ℝ) * Real.log n) := by
        simpa [p, c] using tail_exp_bound n hn (G.edgeSet.ncard) hq
  have hB : ∑ S ∈ B, w S < 1 / 5 := by
    have hBsub : B ⊆ Ω := by
      intro S hS
      obtain ⟨φ, -, hSφ⟩ := Finset.mem_biUnion.mp hS
      exact (Finset.mem_filter.mp hSφ).1
    have hBle : ∑ S ∈ B, w S ≤ ∑ φ : Fin n ↪ Fin N, ∑ S ∈ Bφ φ, w S := by
      calc
        ∑ S ∈ B, w S ≤ ∑ S ∈ B, ∑ φ : Fin n ↪ Fin N,
            (if ((S ∩ Fφ φ).card : ℝ) ≤ c then w S else 0) := by
          apply Finset.sum_le_sum
          intro S hSB
          obtain ⟨φ, -, hSφ⟩ := Finset.mem_biUnion.mp hSB
          have hcond : ((S ∩ Fφ φ).card : ℝ) ≤ c := (Finset.mem_filter.mp hSφ).2
          have hone : w S ≤ (if ((S ∩ Fφ φ).card : ℝ) ≤ c then w S else 0) := by
            simp [hcond]
          exact le_trans hone (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin n ↪ Fin N)))
            (f := fun ψ : Fin n ↪ Fin N =>
              (if ((S ∩ Fφ ψ).card : ℝ) ≤ c then w S else 0))
            (fun ψ hψ => by
              by_cases hc : ((S ∩ Fφ ψ).card : ℝ) ≤ c
              · simp [hc, hw S]
              · simp [hc])
            (a := φ) (by simp))
        _ = ∑ φ : Fin n ↪ Fin N, ∑ S ∈ B,
            (if ((S ∩ Fφ φ).card : ℝ) ≤ c then w S else 0) := by
          rw [Finset.sum_comm]
        _ ≤ ∑ φ : Fin n ↪ Fin N, ∑ S ∈ Ω,
            (if ((S ∩ Fφ φ).card : ℝ) ≤ c then w S else 0) := by
          apply Finset.sum_le_sum
          intro φ hφ
          apply Finset.sum_le_sum_of_subset_of_nonneg hBsub
          intro S hS hnot
          by_cases hc : ((S ∩ Fφ φ).card : ℝ) ≤ c
          · simp [hc, hw S]
          · simp [hc]
        _ = ∑ φ : Fin n ↪ Fin N, ∑ S ∈ Bφ φ, w S := by
          apply Finset.sum_congr rfl
          intro φ hφ
          rw [Finset.sum_filter]
    have hsumle : ∑ φ : Fin n ↪ Fin N, ∑ S ∈ Bφ φ, w S ≤
        (Fintype.card (Fin n ↪ Fin N) : ℝ) * Real.exp (-490 * (n : ℝ) * Real.log n) := by
      calc
        ∑ φ : Fin n ↪ Fin N, ∑ S ∈ Bφ φ, w S ≤
            ∑ φ : Fin n ↪ Fin N, Real.exp (-490 * (n : ℝ) * Real.log n) := by
          apply Finset.sum_le_sum
          intro φ hφ
          exact hBφ_bound φ
        _ = (Fintype.card (Fin n ↪ Fin N) : ℝ) *
            Real.exp (-490 * (n : ℝ) * Real.log n) := by simp
    have hemb := embeddings_le_exp n hn
    have hprod : (Fintype.card (Fin n ↪ Fin N) : ℝ) *
        Real.exp (-490 * (n : ℝ) * Real.log n) ≤
        Real.exp (2 * (n : ℝ) * Real.log n) *
          Real.exp (-490 * (n : ℝ) * Real.log n) := by
      exact mul_le_mul_of_nonneg_right hemb (Real.exp_pos _).le
    have hexptotal : Real.exp (2 * (n : ℝ) * Real.log n) *
        Real.exp (-490 * (n : ℝ) * Real.log n) =
        Real.exp (-488 * (n : ℝ) * Real.log n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsmall := exp_small n hn
    linarith
  have hABsub : A ∪ B ⊆ Ω := by
    intro S hS
    rcases Finset.mem_union.mp hS with hSA | hSB
    · exact (Finset.mem_filter.mp hSA).1
    · obtain ⟨φ, -, hSφ⟩ := Finset.mem_biUnion.mp hSB
      exact (Finset.mem_filter.mp hSφ).1
  have hABsum : ∑ S ∈ A ∪ B, w S ≤ ∑ S ∈ A, w S + ∑ S ∈ B, w S := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun S _ => hw S)
  have hABlt : ∑ S ∈ A ∪ B, w S < 1 := by nlinarith
  have htotal : ∑ S ∈ Ω, w S = 1 := by
    simpa [Ω, w, p] using
      (weight_chernoff p (∅ : Finset (Sym2 (Fin N))))
  have hcomp : 0 < ∑ S ∈ Ω \ (A ∪ B), w S := by
    have hsplit : (∑ S ∈ Ω \ (A ∪ B), w S) + (∑ S ∈ A ∪ B, w S) =
        ∑ S ∈ Ω, w S := Finset.sum_sdiff hABsub
    nlinarith
  have hcompne : (Ω \ (A ∪ B)).Nonempty := by
    by_contra hne
    have hempty : Ω \ (A ∪ B) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hz : ∑ S ∈ Ω \ (A ∪ B), w S = 0 := by simp [hempty]
    linarith
  obtain ⟨S0, hS0⟩ := hcompne
  have hS0Ω : S0 ∈ Ω := (Finset.mem_sdiff.mp hS0).1
  have hnotAB : S0 ∉ A ∪ B := (Finset.mem_sdiff.mp hS0).2
  refine ⟨S0, ?_, ?_, ?_⟩
  · change S0 ∈ Ω
    exact hS0Ω
  · have hnotA : S0 ∉ A := fun h => hnotAB (Finset.mem_union_left B h)
    have hnotc : ¬ c ≤ (T S0 : ℝ) := by
      intro hc
      exact hnotA (Finset.mem_filter.mpr ⟨hS0Ω, hc⟩)
    have hlt : (T S0 : ℝ) < c := lt_of_not_ge hnotc
    simpa [T, c, N] using hlt
  · intro φ
    have hnotB : S0 ∉ B := fun h => hnotAB (Finset.mem_union_right A h)
    have hnotle : ¬ ((S0 ∩ Fφ φ).card : ℝ) ≤ c := by
      intro hle
      apply hnotB
      exact Finset.mem_biUnion.mpr ⟨φ, Finset.mem_univ φ,
        Finset.mem_filter.mpr ⟨hS0Ω, hle⟩⟩
    have hgt : c < ((S0 ∩ Fφ φ).card : ℝ) := lt_of_not_ge hnotle
    simpa [Fφ, c, N] using hgt

lemma not_good_large (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hq : 1000 * Astat n ≤ (G.edgeSet.ncard : ℝ)) : ¬ Erdos1182.IsTriangleGood G := by
  obtain ⟨S0, hS0mem, htri, hF⟩ := sample_exists n hn G hq
  exact not_good_of_sample n (2 * n - 1) hn rfl G S0 htri hF

end OMA

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.f_upper := by
  refine ⟨2000, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  let K : ℕ := ⌊1000 * Astat n⌋₊
  have hKnonneg : 0 ≤ 1000 * Astat n := by
    have hapos := astat_pos n hn
    positivity
  have hbound : ∀ q ∈ {q : ℕ | ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ G.edgeSet.ncard = q ∧ Erdos1182.IsTriangleGood G}, q ≤ K := by
    intro q hq
    obtain ⟨G, hGc, rfl, hGgood⟩ := hq
    by_contra hnot
    have hltfloor : K < G.edgeSet.ncard := Nat.lt_of_not_ge hnot
    have hltreal : 1000 * Astat n < (G.edgeSet.ncard : ℝ) :=
      (Nat.floor_lt hKnonneg).mp (by simpa [K] using hltfloor)
    exact (not_good_large n hn G (le_of_lt hltreal)) hGgood
  have hf_le : Erdos1182.f n ≤ K := by
    unfold Erdos1182.f
    by_cases hne : {q : ℕ | ∃ G : SimpleGraph (Fin n),
        G.Connected ∧ G.edgeSet.ncard = q ∧ Erdos1182.IsTriangleGood G}.Nonempty
    · exact csSup_le hne hbound
    · have hempty : {q : ℕ | ∃ G : SimpleGraph (Fin n),
          G.Connected ∧ G.edgeSet.ncard = q ∧ Erdos1182.IsTriangleGood G} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp
  have hfloor : (K : ℝ) ≤ 1000 * Astat n := by
    dsimp [K]
    exact Nat.floor_le hKnonneg
  have hApos : 0 < Astat n := astat_pos n hn
  have hf_real : (Erdos1182.f n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hf_le
  rw [mul_assoc]
  change (Erdos1182.f n : ℝ) < 2000 * Astat n
  nlinarith
