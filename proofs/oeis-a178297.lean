import OMAStatements.S_oeis_a178297

/-!
Double-counting proof of Mathar's closed form for collinear 6-point subsets
of the 7^n grid (OEIS A178297): every collinear 6-subset has step either 5
or 6 along its minimal affine line, giving an exact 2-to-1 correspondence
from directed step-5 and step-6 parameterizations onto collinear 6-subsets.
-/

private def x05 : Fin 11 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 1, 5, 6]
private def d5 : Fin 11 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1]
private def rev5 : Fin 11 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 9, 10, 7, 8]

private def step5 (c : Fin 11) (k : Fin 6) : Fin 7 :=
  ⟨(((x05 c : ℕ) : ℤ) + (k : ℕ) * d5 c).toNat, by
    fin_cases c <;> fin_cases k <;> decide⟩

private def x06 : Fin 9 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 6]
private def d6 : Fin 9 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1, -1]
private def rev6 : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 8, 7]
private def idx6 : Fin 5 → Fin 6 → ℤ
  | ⟨0, _⟩ => ![0, 2, 3, 4, 5, 6]
  | ⟨1, _⟩ => ![0, 1, 3, 4, 5, 6]
  | ⟨2, _⟩ => ![0, 1, 2, 4, 5, 6]
  | ⟨3, _⟩ => ![0, 1, 2, 3, 5, 6]
  | ⟨4, _⟩ => ![0, 1, 2, 3, 4, 6]

private def revM : Fin 5 → Fin 5 := ![4, 3, 2, 1, 0]

private def step6 (c : Fin 9) (m : Fin 5) (k : Fin 6) : Fin 7 :=
  ⟨(((x06 c : ℕ) : ℤ) + idx6 m k * d6 c).toNat, by
    fin_cases c <;> fin_cases m <;> fin_cases k <;> decide⟩

private lemma step5_val (c : Fin 11) (k : Fin 6) :
    ((step5 c k : ℕ) : ℤ) = ((x05 c : ℕ) : ℤ) + (k : ℕ) * d5 c := by
  fin_cases c <;> fin_cases k <;> decide

private lemma step6_val (c : Fin 9) (m : Fin 5) (k : Fin 6) :
    ((step6 c m k : ℕ) : ℤ) = ((x06 c : ℕ) : ℤ) + idx6 m k * d6 c := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma rev5_invol (c : Fin 11) : rev5 (rev5 c) = c := by
  fin_cases c <;> decide

private lemma rev6_invol (c : Fin 9) : rev6 (rev6 c) = c := by
  fin_cases c <;> decide

private lemma revM_invol (m : Fin 5) : revM (revM m) = m := by
  fin_cases m <;> decide

private lemma step5_rev (c : Fin 11) (k : Fin 6) :
    step5 (rev5 c) ⟨5 - k.val, by omega⟩ = step5 c k := by
  fin_cases c <;> fin_cases k <;> decide

private lemma step6_rev (c : Fin 9) (m : Fin 5) (k : Fin 6) :
    step6 (rev6 c) (revM m) ⟨5 - k.val, by omega⟩ = step6 c m k := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma d5_rev (c : Fin 11) : d5 (rev5 c) = -d5 c := by
  fin_cases c <;> decide

private lemma d6_rev (c : Fin 9) : d6 (rev6 c) = -d6 c := by
  fin_cases c <;> decide

private lemma d5_cases (c : Fin 11) : d5 c = 0 ∨ d5 c = 1 ∨ d5 c = -1 := by
  fin_cases c <;> decide

private lemma d6_cases (c : Fin 9) : d6 c = 0 ∨ d6 c = 1 ∨ d6 c = -1 := by
  fin_cases c <;> decide

private lemma rev5_ne (c : Fin 11) (hc : d5 c ≠ 0) : rev5 c ≠ c := by
  fin_cases c <;> simp_all [d5, rev5]

private lemma rev6_ne (c : Fin 9) (hc : d6 c ≠ 0) : rev6 c ≠ c := by
  fin_cases c <;> simp_all [d6, rev6]

private lemma step5_inj_of_d_ne (c : Fin 11) (hc : d5 c ≠ 0) :
    Function.Injective (step5 c) := by
  fin_cases c <;> simp_all [d5] <;> decide

private lemma step6_inj_of_d_ne (c : Fin 9) (m : Fin 5) (hc : d6 c ≠ 0) :
    Function.Injective (step6 c m) := by
  fin_cases c <;> fin_cases m <;> simp_all [d6] <;> decide

private lemma step6_has_zero_six (c : Fin 9) (m : Fin 5) (hc : d6 c ≠ 0) :
    (∃ k : Fin 6, step6 c m k = 0) ∧ (∃ k : Fin 6, step6 c m k = 6) := by
  fin_cases c <;> fin_cases m <;> simp_all [d6] <;> decide

private lemma step5_diam_le_five (c : Fin 11) (k0 k5 : Fin 6) :
    (step5 c k5 : ℕ) - (step5 c k0 : ℕ) ≤ 5 := by
  have h0 := step5_val c k0
  have h5 := step5_val c k5
  have hk0 := k0.isLt
  have hk5 := k5.isLt
  rcases d5_cases c with h | h | h <;> rw [h] at h0 h5 <;> omega

private lemma d5_zero_iff (c : Fin 11) : d5 c = 0 ↔ c.val < 7 := by
  fin_cases c <;> decide

private lemma d6_zero_iff (c : Fin 9) : d6 c = 0 ↔ c.val < 7 := by
  fin_cases c <;> decide

private lemma exists_u5_of (a b : Fin 7) (h : ∃ k : ℤ, (b : ℤ) - (a : ℤ) = 5 * k) :
    ∃ c : Fin 11, x05 c = a ∧ 5 * d5 c = (b : ℤ) - (a : ℤ) := by
  rcases h with ⟨k, hk⟩
  fin_cases a <;> fin_cases b <;> first | (simp at hk; omega) | decide

private lemma uniq_u5 (c1 c2 : Fin 11) (hx : x05 c1 = x05 c2) (hd : 5 * d5 c1 = 5 * d5 c2) :
    c1 = c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all [x05, d5]

private lemma exists_u6_of (a b : Fin 7) (h : ∃ k : ℤ, (b : ℤ) - (a : ℤ) = 6 * k) :
    ∃ c : Fin 9, x06 c = a ∧ 6 * d6 c = (b : ℤ) - (a : ℤ) := by
  rcases h with ⟨k, hk⟩
  fin_cases a <;> fin_cases b <;> first | (simp at hk; omega) | decide

private lemma uniq_u6 (c1 c2 : Fin 9) (hx : x06 c1 = x06 c2) (hd : 6 * d6 c1 = 6 * d6 c2) :
    c1 = c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all [x06, d6]

private lemma fin6_strictMono_eq {f g : Fin 6 → ℕ} (hf : StrictMono f) (hg : StrictMono g)
    (him : Finset.univ.image f = Finset.univ.image g) : ∀ k : Fin 6, f k = g k := by
  have haux : ∀ n : ℕ, (hn : n < 6) → f ⟨n, hn⟩ = g ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hfm : f ⟨n, hn⟩ ∈ Finset.univ.image g := by
        rw [← him]
        exact Finset.mem_image_of_mem f (Finset.mem_univ _)
      obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hfm
      have hgm : g ⟨n, hn⟩ ∈ Finset.univ.image f := by
        rw [him]
        exact Finset.mem_image_of_mem g (Finset.mem_univ _)
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hgm
      have hmn : m.val = n := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have heq := ih m.val hlt m.isLt
          have hltf : f m < f ⟨n, hn⟩ := hf (Fin.mk_lt_mk.mpr hlt)
          rw [heq, hm] at hltf
          exact lt_irrefl _ hltf
        · have hln : n ≤ l.val := by
            by_contra hln_lt
            push Not at hln_lt
            have heq := ih l.val hln_lt l.isLt
            have hltg : g l < g ⟨n, hn⟩ := hg (Fin.mk_lt_mk.mpr hln_lt)
            rw [← heq, hl] at hltg
            exact lt_irrefl _ hltg
          have hle : f ⟨n, hn⟩ ≤ f l := hf.monotone (Fin.mk_le_mk.mpr hln)
          have hltg : g ⟨n, hn⟩ < g m := hg (Fin.mk_lt_mk.mpr hgt)
          rw [hl] at hle
          rw [hm] at hltg
          omega
      have hmeq : m = ⟨n, hn⟩ := Fin.ext hmn
      rw [hmeq] at hm
      exact hm.symm
  intro k
  exact haux k.val k.isLt

theorem OMA.solution : type_of% @OMA.S_oeis_a178297.main := by
  classical
  intro n
  let G : Finset (Finset (Fin n → Fin 7)) :=
    Finset.univ.filter fun s =>
      s.card = 6 ∧ Collinear ℝ (OMA.S_oeis_a178297.toReal '' (s : Set (Fin n → Fin 7)))
  have ha_eq : OMA.S_oeis_a178297.a n = G.card := by
    dsimp [OMA.S_oeis_a178297.a]
    rw [← Set.ncard_coe_finset G]
    congr 1
    ext s
    simp [G]
  let W5 : Finset (Fin n → Fin 11) :=
    Finset.univ.filter fun u => ∃ i : Fin n, d5 (u i) ≠ 0
  let W6 : Finset (Fin n → Fin 9) :=
    Finset.univ.filter fun u => ∃ i : Fin n, d6 (u i) ≠ 0
  have hW5_card : W5.card + 7 ^ n = 11 ^ n := by
    let Z5 : Finset (Fin n → Fin 11) := Finset.univ.filter fun u => ∀ i : Fin n, d5 (u i) = 0
    have hZ5_eq : Z5 = (Finset.univ : Finset (Fin n → Fin 7)).image
        (fun f i => ⟨(f i).val, by omega⟩) := by
      ext u
      simp only [Z5, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, d5_zero_iff]
      constructor
      · intro hu
        refine ⟨fun i => ⟨(u i).val, hu i⟩, funext fun i => Fin.ext rfl⟩
      · rintro ⟨f, rfl⟩ i
        exact (f i).isLt
    have hZ5_card : Z5.card = 7 ^ n := by
      rw [hZ5_eq, Finset.card_image_of_injective]
      · simp
      · intro f g hfg
        ext i
        exact congrArg (fun h => (h i).val) hfg
    have hpart : W5.card + Z5.card = (Finset.univ : Finset (Fin n → Fin 11)).card := by
      dsimp [W5, Z5]
      simpa [not_exists] using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Fin 11))) (p := fun u => ∃ i : Fin n, d5 (u i) ≠ 0)
    rw [hZ5_card] at hpart
    simpa using hpart
  have hW6_card : W6.card + 7 ^ n = 9 ^ n := by
    let Z6 : Finset (Fin n → Fin 9) := Finset.univ.filter fun u => ∀ i : Fin n, d6 (u i) = 0
    have hZ6_eq : Z6 = (Finset.univ : Finset (Fin n → Fin 7)).image
        (fun f i => ⟨(f i).val, by omega⟩) := by
      ext u
      simp only [Z6, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, d6_zero_iff]
      constructor
      · intro hu
        refine ⟨fun i => ⟨(u i).val, hu i⟩, funext fun i => Fin.ext rfl⟩
      · rintro ⟨f, rfl⟩ i
        exact (f i).isLt
    have hZ6_card : Z6.card = 7 ^ n := by
      rw [hZ6_eq, Finset.card_image_of_injective]
      · simp
      · intro f g hfg
        ext i
        exact congrArg (fun h => (h i).val) hfg
    have hpart : W6.card + Z6.card = (Finset.univ : Finset (Fin n → Fin 9)).card := by
      dsimp [W6, Z6]
      simpa [not_exists] using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Fin 9))) (p := fun u => ∃ i : Fin n, d6 (u i) ≠ 0)
    rw [hZ6_card] at hpart
    simpa using hpart
  let W : Finset ((Fin n → Fin 11) ⊕ ((Fin n → Fin 9) × Fin 5)) :=
    W5.disjSum (W6 ×ˢ (Finset.univ : Finset (Fin 5)))
  have hW_card : W.card = W5.card + 5 * W6.card := by
    dsimp [W]
    rw [Finset.card_disjSum, Finset.card_product, Finset.card_fin]
    ring
  let p5 : (Fin n → Fin 11) → Fin 6 → (Fin n → Fin 7) := fun u k i => step5 (u i) k
  let p6 : (Fin n → Fin 9) × Fin 5 → Fin 6 → (Fin n → Fin 7) :=
    fun w k i => step6 (w.1 i) w.2 k
  let Φ : (Fin n → Fin 11) ⊕ ((Fin n → Fin 9) × Fin 5) → Finset (Fin n → Fin 7)
    | Sum.inl u => Finset.univ.image (p5 u)
    | Sum.inr w => Finset.univ.image (p6 w)
  let revW : (Fin n → Fin 11) ⊕ ((Fin n → Fin 9) × Fin 5) →
      (Fin n → Fin 11) ⊕ ((Fin n → Fin 9) × Fin 5)
    | Sum.inl u => Sum.inl (fun i => rev5 (u i))
    | Sum.inr (u, m) => Sum.inr (fun i => rev6 (u i), revM m)
  have hrev_mem : ∀ w ∈ W, revW w ∈ W := by
    intro w hw
    rcases Finset.mem_disjSum.mp hw with ⟨u, hu, rfl⟩ | ⟨⟨u, m⟩, hwm, rfl⟩
    · refine Finset.mem_disjSum.mpr (Or.inl ⟨fun i => rev5 (u i), ?_, rfl⟩)
      simp only [W5, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      obtain ⟨i, hi⟩ := hu
      exact ⟨i, by rw [d5_rev]; omega⟩
    · refine Finset.mem_disjSum.mpr (Or.inr ⟨(fun i => rev6 (u i), revM m), ?_, rfl⟩)
      simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        at hwm ⊢
      obtain ⟨i, hi⟩ := hwm
      exact ⟨i, by rw [d6_rev]; omega⟩
  have hrev_ne : ∀ w ∈ W, revW w ≠ w := by
    intro w hw heq
    rcases Finset.mem_disjSum.mp hw with ⟨u, hu, rfl⟩ | ⟨⟨u, m⟩, hwm, rfl⟩
    · simp only [W5, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨i, hi⟩ := hu
      have h1 : rev5 (u i) = u i :=
        congrArg (fun x => match x with | Sum.inl v => v i | _ => u i) heq
      exact rev5_ne (u i) hi h1
    · simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        at hwm
      obtain ⟨i, hi⟩ := hwm
      have h1 : rev6 (u i) = u i :=
        congrArg (fun x => match x with | Sum.inr p => p.1 i | _ => u i) heq
      exact rev6_ne (u i) hi h1
  have hPhi_rev : ∀ w, Φ (revW w) = Φ w := by
    rintro (u | ⟨u, m⟩)
    · ext x
      simp only [Φ, revW, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨⟨5 - k.val, by omega⟩, funext fun i => ?_⟩
        have h := step5_rev (rev5 (u i)) k
        rwa [rev5_invol] at h
      · rintro ⟨k, rfl⟩
        refine ⟨⟨5 - k.val, by omega⟩, funext fun i => ?_⟩
        exact step5_rev (u i) k
    · ext x
      simp only [Φ, revW, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨⟨5 - k.val, by omega⟩, funext fun i => ?_⟩
        have h := step6_rev (rev6 (u i)) (revM m) k
        rwa [rev6_invol, revM_invol] at h
      · rintro ⟨k, rfl⟩
        refine ⟨⟨5 - k.val, by omega⟩, funext fun i => ?_⟩
        exact step6_rev (u i) m k
  have hPhi_mem : ∀ w ∈ W, Φ w ∈ G := by
    intro w hw
    rcases Finset.mem_disjSum.mp hw with ⟨u, hu, rfl⟩ | ⟨⟨u, m⟩, hwm, rfl⟩
    · simp only [W5, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨i₀, hi₀⟩ := hu
      have hinj : Function.Injective (p5 u) := by
        intro j k hjk
        exact step5_inj_of_d_ne (u i₀) hi₀ (congrFun hjk i₀)
      have hcard : (Φ (Sum.inl u)).card = 6 := by
        dsimp [Φ]
        rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
      have hcol : Collinear ℝ
          (OMA.S_oeis_a178297.toReal '' (Φ (Sum.inl u) : Set (Fin n → Fin 7))) := by
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨fun i => ((x05 (u i) : ℕ) : ℝ), fun i => (d5 (u i) : ℝ), ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        simp only [Φ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨k, rfl⟩ := hx
        refine ⟨(k : ℝ), funext fun i => ?_⟩
        dsimp [OMA.S_oeis_a178297.toReal, p5]
        have hv : ((step5 (u i) k : ℕ) : ℝ) = ((x05 (u i) : ℕ) : ℝ) + (k : ℝ) * (d5 (u i) : ℝ) := by
          exact_mod_cast step5_val (u i) k
        simpa [vadd_eq_add, add_comm] using hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hcol⟩
    · simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        at hwm
      obtain ⟨i₀, hi₀⟩ := hwm
      have hinj : Function.Injective (p6 (u, m)) := by
        intro j k hjk
        exact step6_inj_of_d_ne (u i₀) m hi₀ (congrFun hjk i₀)
      have hcard : (Φ (Sum.inr (u, m))).card = 6 := by
        dsimp [Φ]
        rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
      have hcol : Collinear ℝ (OMA.S_oeis_a178297.toReal ''
          (Φ (Sum.inr (u, m)) : Set (Fin n → Fin 7))) := by
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨fun i => ((x06 (u i) : ℕ) : ℝ), fun i => (d6 (u i) : ℝ), ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        simp only [Φ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨k, rfl⟩ := hx
        refine ⟨(idx6 m k : ℝ), funext fun i => ?_⟩
        dsimp [OMA.S_oeis_a178297.toReal, p6]
        have hv : ((step6 (u i) m k : ℕ) : ℝ) =
            ((x06 (u i) : ℕ) : ℝ) + (idx6 m k : ℝ) * (d6 (u i) : ℝ) := by
          exact_mod_cast step6_val (u i) m k
        simpa [vadd_eq_add, add_comm] using hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hcol⟩
  have hfiber_pair : ∀ s ∈ G, ∃ w ∈ W, Φ w = s ∧ ∀ w' ∈ W, Φ w' = s → w' = w ∨ w' = revW w := by
    intro s hs
    obtain ⟨hs_card, hs_col⟩ := (Finset.mem_filter.mp hs).2
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hs_col
    obtain ⟨p₀, v, hv⟩ := hs_col
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hsub1 : s.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨ra, hra⟩ := hv _ ⟨a, ha, rfl⟩
        obtain ⟨rb, hrb⟩ := hv _ ⟨b, hb, rfl⟩
        have htr : OMA.S_oeis_a178297.toReal a = OMA.S_oeis_a178297.toReal b := by
          rw [hra, hrb, hv0, smul_zero, smul_zero]
        exact funext fun i => Fin.ext (by
          have := congrFun htr i
          dsimp [OMA.S_oeis_a178297.toReal] at this
          exact_mod_cast this)
      omega
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, v i₀ ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hv_ne (funext h0)
    have hcoord_inj : Set.InjOn (fun x : Fin n → Fin 7 => x i₀) (s : Set (Fin n → Fin 7)) := by
      intro a ha b hb hab
      obtain ⟨ra, hra⟩ := hv _ ⟨a, ha, rfl⟩
      obtain ⟨rb, hrb⟩ := hv _ ⟨b, hb, rfl⟩
      have ha0 := congrFun hra i₀
      have hb0 := congrFun hrb i₀
      have hab0 : a i₀ = b i₀ := hab
      have htr0 : OMA.S_oeis_a178297.toReal a i₀ = OMA.S_oeis_a178297.toReal b i₀ := by
        dsimp [OMA.S_oeis_a178297.toReal]
        rw [hab0]
      rw [ha0, hb0] at htr0
      have hr : ra = rb := by
        have : (ra - rb) * v i₀ = 0 := by
          simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at htr0
          linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hi₀
      have htr : OMA.S_oeis_a178297.toReal a = OMA.S_oeis_a178297.toReal b := by
        rw [hra, hrb, hr]
      exact funext fun i => Fin.ext (by
        have := congrFun htr i
        dsimp [OMA.S_oeis_a178297.toReal] at this
        exact_mod_cast this)
    let T : Finset (Fin 7) := s.image (fun x => x i₀)
    have hT_card : T.card = 6 := by
      dsimp [T]
      rw [Finset.card_image_of_injOn hcoord_inj, hs_card]
    let eT : Fin 6 ≃o T := T.orderIsoOfFin hT_card
    have hx_ex : ∀ k : Fin 6, ∃! x ∈ s, x i₀ = (eT k).1 := by
      intro k
      have hkT : (eT k).1 ∈ T := (eT k).2
      dsimp [T] at hkT
      obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hkT
      exact ⟨x, ⟨hx, hxi⟩, fun y ⟨hy, hyi⟩ => hcoord_inj hy hx (hyi.trans hxi.symm)⟩
    let x : Fin 6 → (Fin n → Fin 7) := fun k => Classical.choose (hx_ex k)
    have hx_mem : ∀ k : Fin 6, x k ∈ s := fun k => (Classical.choose_spec (hx_ex k)).1.1
    have hx_coord : ∀ k : Fin 6, x k i₀ = (eT k).1 := fun k => (Classical.choose_spec (hx_ex k)).1.2
    have hx_mono : StrictMono (fun k : Fin 6 => (x k i₀ : ℕ)) := by
      intro j k hjk
      dsimp only
      rw [hx_coord j, hx_coord k]
      exact eT.strictMono hjk
    have hs_eq : s = Finset.univ.image x := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        have hyT : y i₀ ∈ T := Finset.mem_image_of_mem _ hy
        let k := eT.symm ⟨y i₀, hyT⟩
        have hk : (eT k).1 = y i₀ := congrArg Subtype.val (eT.apply_symm_apply ⟨y i₀, hyT⟩)
        have hxy : x k = y := hcoord_inj (hx_mem k) hy ((hx_coord k).trans hk)
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hxy⟩
      · rw [hs_card, Finset.card_image_of_injective]
        · rw [Finset.card_fin]
        · intro j k hjk
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact (hx_mono h).ne (congrArg (fun f => (f i₀ : ℕ)) hjk)
          · exact (hx_mono h).ne.symm (congrArg (fun f => (f i₀ : ℕ)) hjk)
    have hline : ∀ (k : Fin 6) (i : Fin n),
        (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) * (((x 5 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
        (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) * (((x 5 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by
      intro k i
      obtain ⟨r0, hr0⟩ := hv _ ⟨x 0, hx_mem 0, rfl⟩
      obtain ⟨rk, hrk⟩ := hv _ ⟨x k, hx_mem k, rfl⟩
      obtain ⟨r5, hr5⟩ := hv _ ⟨x 5, hx_mem 5, rfl⟩
      have h0i := congrFun hr0 i
      have hki := congrFun hrk i
      have h5i := congrFun hr5 i
      have h00 := congrFun hr0 i₀
      have hk0 := congrFun hrk i₀
      have h50 := congrFun hr5 i₀
      simp only [OMA.S_oeis_a178297.toReal, vadd_eq_add, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at h0i hki h5i h00 hk0 h50
      have hreal : ((((x k i : ℕ) : ℝ) - ((x 0 i : ℕ) : ℝ)) *
            (((x 5 i₀ : ℕ) : ℝ) - ((x 0 i₀ : ℕ) : ℝ))) =
          ((((x k i₀ : ℕ) : ℝ) - ((x 0 i₀ : ℕ) : ℝ)) *
            (((x 5 i : ℕ) : ℝ) - ((x 0 i : ℕ) : ℝ))) := by
        rw [hki, h0i, h50, h00, hk0, h5i]
        ring
      exact_mod_cast hreal
    have h0lt1 : (x 0 i₀ : ℕ) < (x 1 i₀ : ℕ) := hx_mono (by decide : (0 : Fin 6) < 1)
    have h1lt2 : (x 1 i₀ : ℕ) < (x 2 i₀ : ℕ) := hx_mono (by decide : (1 : Fin 6) < 2)
    have h2lt3 : (x 2 i₀ : ℕ) < (x 3 i₀ : ℕ) := hx_mono (by decide : (2 : Fin 6) < 3)
    have h3lt4 : (x 3 i₀ : ℕ) < (x 4 i₀ : ℕ) := hx_mono (by decide : (3 : Fin 6) < 4)
    have h4lt5 : (x 4 i₀ : ℕ) < (x 5 i₀ : ℕ) := hx_mono (by decide : (4 : Fin 6) < 5)
    have h5le6 : (x 5 i₀ : ℕ) ≤ 6 := Nat.lt_succ_iff.mp (x 5 i₀).isLt
    have hA : (x 5 i₀ : ℕ) - (x 0 i₀ : ℕ) = 5 ∨ (x 5 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6 := by omega
    rcases hA with hA5 | hA6
    · have hdvd5 : ∀ i : Fin n, ∃ q : ℤ, ((x 5 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) = 5 * q := by
        intro i
        have h1 := hline 1 i
        have hA_z : ((x 5 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 5 := by omega
        have hp1_z : ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 1 := by omega
        rw [hA_z, hp1_z, one_mul] at h1
        exact ⟨((x 1 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ), by linarith⟩
      let u : Fin n → Fin 11 := fun i => Classical.choose (exists_u5_of (x 0 i) (x 5 i) (hdvd5 i))
      have hu_spec : ∀ i : Fin n, x05 (u i) = x 0 i ∧
          5 * d5 (u i) = ((x 5 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) :=
        fun i => Classical.choose_spec (exists_u5_of (x 0 i) (x 5 i) (hdvd5 i))
      have huW : Sum.inl u ∈ W := by
        refine Finset.mem_disjSum.mpr (Or.inl ⟨u, ?_, rfl⟩)
        simp only [W5, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨i₀, ?_⟩
        have h := (hu_spec i₀).2
        omega
      have hu_step : ∀ k : Fin 6, p5 u k = x k := by
        intro k
        ext i
        have hlk := hline k i
        have hA_z : ((x 5 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 5 := by omega
        have hpk_z : ((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = (k : ℕ) := by
          fin_cases k <;> simp <;> omega
        rw [hA_z, hpk_z] at hlk
        have hsv := step5_val (u i) k
        have hsp := hu_spec i
        have h0_eq : ((x05 (u i) : ℕ) : ℤ) = ((x 0 i : ℕ) : ℤ) := by rw [hsp.1]
        rw [← hsp.2] at hlk
        have h5_eq : ((x k i : ℕ) : ℤ) = ((step5 (u i) k : ℕ) : ℤ) := by
          linarith [show ((k : ℕ) : ℤ) * (5 * d5 (u i)) = 5 * (((k : ℕ) : ℤ) * d5 (u i)) by ring]
        exact_mod_cast h5_eq.symm
      have hPhi_u : Φ (Sum.inl u) = s := by
        rw [hs_eq]
        dsimp [Φ]
        exact Finset.image_congr fun k _ => hu_step k
      refine ⟨Sum.inl u, huW, hPhi_u, ?_⟩
      rintro (u' | ⟨u', m'⟩) hw' hPhi'
      · have hu'_ne : d5 (u' i₀) ≠ 0 := by
          intro hd0
          have himg : s.image (fun y => y i₀) ⊆ {x05 (u' i₀)} := by
            intro z hz
            rw [← hPhi'] at hz
            simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
            rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
            simp only [Finset.mem_singleton]
            apply Fin.ext
            have := step5_val (u' i₀) k
            rw [hd0, mul_zero, add_zero] at this
            exact_mod_cast this
          have := Finset.card_le_card himg
          rw [Finset.card_singleton] at this
          change T.card ≤ 1 at this
          omega
        have hor : d5 (u' i₀) = 1 ∨ d5 (u' i₀) = -1 := by
          rcases d5_cases (u' i₀) with h0 | h1 | h2
          · exact absurd h0 hu'_ne
          · exact Or.inl h1
          · exact Or.inr h2
        have hcheck_pos : ∀ v : Fin n → Fin 11, Φ (Sum.inl v) = s → d5 (v i₀) = 1 → v = u := by
          intro v hPhiv hv1
          have hv_step : ∀ k : Fin 6, p5 v k = x k := by
            have hmonov : StrictMono (fun k : Fin 6 => (p5 v k i₀ : ℕ)) := by
              intro a b hab
              dsimp [p5]
              have hab' : (a : ℕ) < (b : ℕ) := hab
              have ha := step5_val (v i₀) a
              have hb := step5_val (v i₀) b
              rw [hv1] at ha hb
              omega
            have himg_eq : Finset.univ.image (fun k : Fin 6 => (p5 v k i₀ : ℕ)) =
                Finset.univ.image (fun k : Fin 6 => (x k i₀ : ℕ)) := by
              have h1 : Finset.univ.image (fun k : Fin 6 => (p5 v k i₀ : ℕ)) =
                  (Φ (Sum.inl v)).image (fun y => (y i₀ : ℕ)) := by
                ext z; simp [Φ]
              have h2 : Finset.univ.image (fun k : Fin 6 => (x k i₀ : ℕ)) =
                  s.image (fun y => (y i₀ : ℕ)) := by
                ext z; simp [hs_eq]
              rw [h1, h2, hPhiv]
            have hcoord_eq : ∀ k : Fin 6, p5 v k i₀ = x k i₀ := by
              have hc := fin6_strictMono_eq hmonov hx_mono himg_eq
              intro k; exact Fin.ext (hc k)
            intro k
            have hmem : p5 v k ∈ s := by
              rw [← hPhiv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
            exact hcoord_inj hmem (hx_mem k) (hcoord_eq k)
          funext i
          refine uniq_u5 (v i) (u i) ?_ ?_
          · have h0 := congrFun (hv_step 0) i
            have hv0 := step5_val (v i) 0
            have hk0 : (((0 : Fin 6) : ℕ) : ℤ) = 0 := rfl
            rw [hk0, zero_mul, add_zero] at hv0
            rw [(hu_spec i).1, ← h0]
            exact Fin.ext (by dsimp [p5]; exact_mod_cast hv0.symm)
          · have h0 := congrFun (hv_step 0) i
            have h5 := congrFun (hv_step 5) i
            have hv0 := step5_val (v i) 0
            have hv5 := step5_val (v i) 5
            have hk0 : (((0 : Fin 6) : ℕ) : ℤ) = 0 := rfl
            have hk5 : (((5 : Fin 6) : ℕ) : ℤ) = 5 := rfl
            rw [hk0, zero_mul, add_zero] at hv0
            rw [hk5] at hv5
            have h0_z : ((x 0 i : ℕ) : ℤ) = ((x05 (v i) : ℕ) : ℤ) := by
              dsimp [p5] at h0; rw [← h0]; exact_mod_cast hv0
            have h5_z : ((x 5 i : ℕ) : ℤ) = ((step5 (v i) 5 : ℕ) : ℤ) := by
              dsimp [p5] at h5; rw [← h5]
            rw [(hu_spec i).2]
            linarith
        rcases hor with hv1 | hv_neg
        · exact Or.inl (congrArg Sum.inl (hcheck_pos u' hPhi' hv1))
        · have hrev_d : d5 (rev5 (u' i₀)) = 1 := by rw [d5_rev, hv_neg]; norm_num
          have hrev_eq := hcheck_pos (fun i => rev5 (u' i))
            ((hPhi_rev (Sum.inl u')).trans hPhi') hrev_d
          right
          congr 1
          funext i
          have := congrFun hrev_eq i
          rw [← this, rev5_invol]
      · exfalso
        have hu'_ne : d6 (u' i₀) ≠ 0 := by
          intro hd0
          have himg : s.image (fun y => y i₀) ⊆ {x06 (u' i₀)} := by
            intro z hz
            rw [← hPhi'] at hz
            simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
            rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
            simp only [Finset.mem_singleton]
            apply Fin.ext
            have := step6_val (u' i₀) m' k
            rw [hd0, mul_zero, add_zero] at this
            exact_mod_cast this
          have := Finset.card_le_card himg
          rw [Finset.card_singleton] at this
          change T.card ≤ 1 at this
          omega
        obtain ⟨⟨k0, hk0_eq⟩, ⟨k6, hk6_eq⟩⟩ := step6_has_zero_six (u' i₀) m' hu'_ne
        have hp0_mem : p6 (u', m') k0 ∈ s := by
          rw [← hPhi']; exact Finset.mem_image_of_mem _ (Finset.mem_univ k0)
        have hp6_mem : p6 (u', m') k6 ∈ s := by
          rw [← hPhi']; exact Finset.mem_image_of_mem _ (Finset.mem_univ k6)
        rw [hs_eq, Finset.mem_image] at hp0_mem hp6_mem
        obtain ⟨j0, _, hj0⟩ := hp0_mem
        obtain ⟨j6, _, hj6⟩ := hp6_mem
        have hj0_val : (x j0 i₀ : ℕ) = 0 := by
          have := congrFun hj0 i₀
          dsimp [p6] at this
          rw [hk0_eq] at this
          simpa using congrArg Fin.val this
        have hj6_val : (x j6 i₀ : ℕ) = 6 := by
          have := congrFun hj6 i₀
          dsimp [p6] at this
          rw [hk6_eq] at this
          simpa using congrArg Fin.val this
        have hle0 : (x 0 i₀ : ℕ) ≤ (x j0 i₀ : ℕ) := hx_mono.monotone (Fin.zero_le j0)
        have hle6 : (x j6 i₀ : ℕ) ≤ (x 5 i₀ : ℕ) := hx_mono.monotone (Fin.le_last j6)
        omega
    · have hx0_eq : (x 0 i₀ : ℕ) = 0 := by omega
      have hx5_eq : (x 5 i₀ : ℕ) = 6 := by omega
      have hdvd6 : ∀ i : Fin n, ∃ q : ℤ, ((x 5 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) = 6 * q := by
        intro i
        have hA_z : ((x 5 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 6 := by omega
        by_cases hx1 : (x 1 i₀ : ℕ) = 1
        · have h1 := hline 1 i
          have hp1_z : ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 1 := by omega
          rw [hA_z, hp1_z, one_mul] at h1
          exact ⟨((x 1 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ), by linarith⟩
        · have hx4 : (x 4 i₀ : ℕ) = 5 := by omega
          have h4 := hline 4 i
          have hp4_z : ((x 4 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 5 := by omega
          rw [hA_z, hp4_z] at h4
          exact ⟨((x 5 i : ℕ) : ℤ) - ((x 4 i : ℕ) : ℤ), by linarith⟩
      let m : Fin 5 :=
        if (x 1 i₀ : ℕ) = 2 then 0
        else if (x 2 i₀ : ℕ) = 3 then 1
        else if (x 3 i₀ : ℕ) = 4 then 2
        else if (x 4 i₀ : ℕ) = 5 then 3
        else 4
      have hm_spec : ∀ k : Fin 6, idx6 m k = ((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) := by
        intro k
        dsimp [m]
        split_ifs <;> fin_cases k <;> simp [idx6] <;> omega
      let u : Fin n → Fin 9 := fun i => Classical.choose (exists_u6_of (x 0 i) (x 5 i) (hdvd6 i))
      have hu_spec : ∀ i : Fin n, x06 (u i) = x 0 i ∧
          6 * d6 (u i) = ((x 5 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) :=
        fun i => Classical.choose_spec (exists_u6_of (x 0 i) (x 5 i) (hdvd6 i))
      have huW : Sum.inr (u, m) ∈ W := by
        refine Finset.mem_disjSum.mpr (Or.inr ⟨(u, m), ?_, rfl⟩)
        simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        refine ⟨i₀, ?_⟩
        have h := (hu_spec i₀).2
        omega
      have hu_step : ∀ k : Fin 6, p6 (u, m) k = x k := by
        intro k
        ext i
        have hlk := hline k i
        have hA_z : ((x 5 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 6 := by omega
        rw [hA_z, ← hm_spec k] at hlk
        have hsv := step6_val (u i) m k
        have hsp := hu_spec i
        have h0_eq : ((x06 (u i) : ℕ) : ℤ) = ((x 0 i : ℕ) : ℤ) := by rw [hsp.1]
        rw [← hsp.2] at hlk
        have h6_eq : ((x k i : ℕ) : ℤ) = ((step6 (u i) m k : ℕ) : ℤ) := by
          linarith [show idx6 m k * (6 * d6 (u i)) = 6 * (idx6 m k * d6 (u i)) by ring]
        exact_mod_cast h6_eq.symm
      have hPhi_u : Φ (Sum.inr (u, m)) = s := by
        rw [hs_eq]
        dsimp [Φ]
        exact Finset.image_congr fun k _ => hu_step k
      refine ⟨Sum.inr (u, m), huW, hPhi_u, ?_⟩
      rintro (u' | ⟨u', m'⟩) hw' hPhi'
      · exfalso
        have himg_eq : (Φ (Sum.inl u')).image (fun y => (y i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by rw [hPhi']
        have h0_mem : 0 ∈ (Φ (Sum.inl u')).image (fun y => (y i₀ : ℕ)) := by
          rw [himg_eq, hs_eq]
          exact Finset.mem_image.mpr ⟨x 0, Finset.mem_image_of_mem _ (Finset.mem_univ 0), hx0_eq⟩
        have h6_mem : 6 ∈ (Φ (Sum.inl u')).image (fun y => (y i₀ : ℕ)) := by
          rw [himg_eq, hs_eq]
          exact Finset.mem_image.mpr ⟨x 5, Finset.mem_image_of_mem _ (Finset.mem_univ 5), hx5_eq⟩
        simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at h0_mem h6_mem
        rcases h0_mem with ⟨_, ⟨k0, rfl⟩, hk0⟩
        rcases h6_mem with ⟨_, ⟨k5, rfl⟩, hk5⟩
        have hdiam := step5_diam_le_five (u' i₀) k0 k5
        dsimp [p5] at hk0 hk5
        omega
      · have hu'_ne : d6 (u' i₀) ≠ 0 := by
          intro hd0
          have himg : s.image (fun y => y i₀) ⊆ {x06 (u' i₀)} := by
            intro z hz
            rw [← hPhi'] at hz
            simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
            rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
            simp only [Finset.mem_singleton]
            apply Fin.ext
            have := step6_val (u' i₀) m' k
            rw [hd0, mul_zero, add_zero] at this
            exact_mod_cast this
          have := Finset.card_le_card himg
          rw [Finset.card_singleton] at this
          change T.card ≤ 1 at this
          omega
        have hor : d6 (u' i₀) = 1 ∨ d6 (u' i₀) = -1 := by
          rcases d6_cases (u' i₀) with h0 | h1 | h2
          · exact absurd h0 hu'_ne
          · exact Or.inl h1
          · exact Or.inr h2
        have hcheck_pos : ∀ (v : Fin n → Fin 9) (mv : Fin 5),
            Φ (Sum.inr (v, mv)) = s → d6 (v i₀) = 1 → (v, mv) = (u, m) := by
          intro v mv hPhiv hv1
          have hidx_mono : StrictMono (idx6 mv) := by
            fin_cases mv <;> decide
          have hmonov : StrictMono (fun k : Fin 6 => (p6 (v, mv) k i₀ : ℕ)) := by
            intro a b hab
            dsimp [p6]
            have ha := step6_val (v i₀) mv a
            have hb := step6_val (v i₀) mv b
            rw [hv1] at ha hb
            have hlt : idx6 mv a < idx6 mv b := hidx_mono hab
            omega
          have himg_eq : Finset.univ.image (fun k : Fin 6 => (p6 (v, mv) k i₀ : ℕ)) =
              Finset.univ.image (fun k : Fin 6 => (x k i₀ : ℕ)) := by
            have h1 : Finset.univ.image (fun k : Fin 6 => (p6 (v, mv) k i₀ : ℕ)) =
                (Φ (Sum.inr (v, mv))).image (fun y => (y i₀ : ℕ)) := by
              ext z; simp [Φ]
            have h2 : Finset.univ.image (fun k : Fin 6 => (x k i₀ : ℕ)) =
                s.image (fun y => (y i₀ : ℕ)) := by
              ext z; simp [hs_eq]
            rw [h1, h2, hPhiv]
          have hv_step : ∀ k : Fin 6, p6 (v, mv) k = x k := by
            have hc := fin6_strictMono_eq hmonov hx_mono himg_eq
            intro k
            have hmem : p6 (v, mv) k ∈ s := by
              rw [← hPhiv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
            exact hcoord_inj hmem (hx_mem k) (Fin.ext (hc k))
          have hmv_eq : mv = m := by
            have h1 : idx6 mv 1 = idx6 m 1 := by
              have hst1 := step6_val (v i₀) mv 1
              have hst0 := step6_val (v i₀) mv 0
              have h0_eq : ((p6 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 0) i₀]
              have h1_eq : ((p6 (v, mv) 1 i₀ : ℕ) : ℤ) = ((x 1 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 1) i₀]
              have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
              rw [hv1] at hst1 hst0
              rw [hi0] at hst0
              dsimp [p6] at h0_eq h1_eq
              rw [hm_spec 1]
              linarith
            have h2 : idx6 mv 2 = idx6 m 2 := by
              have hst2 := step6_val (v i₀) mv 2
              have hst0 := step6_val (v i₀) mv 0
              have h0_eq : ((p6 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 0) i₀]
              have h2_eq : ((p6 (v, mv) 2 i₀ : ℕ) : ℤ) = ((x 2 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 2) i₀]
              have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
              rw [hv1] at hst2 hst0
              rw [hi0] at hst0
              dsimp [p6] at h0_eq h2_eq
              rw [hm_spec 2]
              linarith
            have h3 : idx6 mv 3 = idx6 m 3 := by
              have hst3 := step6_val (v i₀) mv 3
              have hst0 := step6_val (v i₀) mv 0
              have h0_eq : ((p6 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 0) i₀]
              have h3_eq : ((p6 (v, mv) 3 i₀ : ℕ) : ℤ) = ((x 3 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 3) i₀]
              have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
              rw [hv1] at hst3 hst0
              rw [hi0] at hst0
              dsimp [p6] at h0_eq h3_eq
              rw [hm_spec 3]
              linarith
            have h4 : idx6 mv 4 = idx6 m 4 := by
              have hst4 := step6_val (v i₀) mv 4
              have hst0 := step6_val (v i₀) mv 0
              have h0_eq : ((p6 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 0) i₀]
              have h4_eq : ((p6 (v, mv) 4 i₀ : ℕ) : ℤ) = ((x 4 i₀ : ℕ) : ℤ) := by
                rw [congrFun (hv_step 4) i₀]
              have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
              rw [hv1] at hst4 hst0
              rw [hi0] at hst0
              dsimp [p6] at h0_eq h4_eq
              rw [hm_spec 4]
              linarith
            have hfin : ∀ a b : Fin 5, idx6 a 1 = idx6 b 1 → idx6 a 2 = idx6 b 2 →
                idx6 a 3 = idx6 b 3 → idx6 a 4 = idx6 b 4 → a = b := by
              intro a b ha hb hc hd
              fin_cases a <;> fin_cases b <;> revert ha hb hc hd <;> decide
            exact hfin mv m h1 h2 h3 h4
          refine Prod.ext (funext fun i => ?_) hmv_eq
          refine uniq_u6 (v i) (u i) ?_ ?_
          · have h0 := congrFun (hv_step 0) i
            have hv0 := step6_val (v i) mv 0
            have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
            rw [hi0, zero_mul, add_zero] at hv0
            rw [(hu_spec i).1, ← h0]
            exact Fin.ext (by dsimp [p6]; exact_mod_cast hv0.symm)
          · have h0 := congrFun (hv_step 0) i
            have h5 := congrFun (hv_step 5) i
            have hv0 := step6_val (v i) mv 0
            have hv5 := step6_val (v i) mv 5
            have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
            have hi5 : idx6 mv 5 = 6 := by fin_cases mv <;> rfl
            rw [hi0, zero_mul, add_zero] at hv0
            rw [hi5] at hv5
            have h0_z : ((x 0 i : ℕ) : ℤ) = ((x06 (v i) : ℕ) : ℤ) := by
              dsimp [p6] at h0; rw [← h0]; exact_mod_cast hv0
            have h5_z : ((x 5 i : ℕ) : ℤ) = ((step6 (v i) mv 5 : ℕ) : ℤ) := by
              dsimp [p6] at h5; rw [← h5]
            rw [(hu_spec i).2]
            linarith
        rcases hor with hv1 | hv_neg
        · exact Or.inl (congrArg Sum.inr (hcheck_pos u' m' hPhi' hv1))
        · have hrev_d : d6 (rev6 (u' i₀)) = 1 := by rw [d6_rev, hv_neg]; norm_num
          have hrev_eq := hcheck_pos (fun i => rev6 (u' i)) (revM m')
            ((hPhi_rev (Sum.inr (u', m'))).trans hPhi') hrev_d
          right
          have h1 := congrArg Prod.fst hrev_eq
          have h2 := congrArg Prod.snd hrev_eq
          dsimp only at h1 h2
          refine congrArg Sum.inr (Prod.ext ?_ ?_)
          · funext i
            dsimp only
            have := congrFun h1 i
            rw [← this, rev6_invol]
          · dsimp only
            rw [← h2, revM_invol]
  have hcard_eq : W.card = 2 * G.card := by
    rw [Finset.card_eq_sum_card_fiberwise hPhi_mem]
    have hfib2 : ∀ s ∈ G, (W.filter fun w => Φ w = s).card = 2 := by
      intro s hs
      obtain ⟨w, hw, hPhiw, huniq⟩ := hfiber_pair s hs
      have hset : W.filter (fun w' => Φ w' = s) = {w, revW w} := by
        ext w'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hw', hPhiw'⟩
          exact huniq w' hw' hPhiw'
        · rintro (rfl | rfl)
          · exact ⟨hw, hPhiw⟩
          · exact ⟨hrev_mem w hw, (hPhi_rev w).trans hPhiw⟩
      rw [hset, Finset.card_pair (hrev_ne w hw).symm]
    rw [Finset.sum_congr rfl hfib2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hz5 : (W5.card : ℤ) + 7 ^ n = 11 ^ n := by exact_mod_cast hW5_card
  have hz6 : (W6.card : ℤ) + 7 ^ n = 9 ^ n := by exact_mod_cast hW6_card
  have hzW : (W.card : ℤ) = (W5.card : ℤ) + 5 * (W6.card : ℤ) := by exact_mod_cast hW_card
  have hzc : (W.card : ℤ) = 2 * (G.card : ℤ) := by exact_mod_cast hcard_eq
  rw [ha_eq]
  linarith
