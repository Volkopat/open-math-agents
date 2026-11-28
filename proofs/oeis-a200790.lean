import OMAStatements.S_oeis_a200790

namespace OMA.P_oeis_a200790

open OMA.S_oeis_a200790

private def P {m : ℕ} (x : Fin 8 → Fin m) : Prop :=
  ∀ i : Fin 6, ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 1, by omega⟩ < x ⟨i.1 + 2, by omega⟩)

private instance {m : ℕ} (x : Fin 8 → Fin m) : Decidable (P x) := by
  unfold P; infer_instance

private lemma P_comp {r m : ℕ} (f : Fin r ↪o Fin m) (y : Fin 8 → Fin r) :
    P (f ∘ y) ↔ P y := by
  unfold P
  simp only [Function.comp_apply, f.lt_iff_lt]

private def cnt (m : ℕ) : ℕ :=
  Fintype.card {x : Fin 8 → Fin m // P x}

private def surjCnt (r : ℕ) : ℕ :=
  Fintype.card {y : Fin 8 → Fin r // Function.Surjective y ∧ P y}

private lemma cnt_eq_sum_choose (m : ℕ) :
    cnt m = ∑ r ∈ Finset.range 9, surjCnt r * Nat.choose m r := by
  unfold cnt
  let φ : (Σ r : Fin 9, {S : Finset (Fin m) // S.card = r.1} ×
        {y : Fin 8 → Fin r.1 // Function.Surjective y ∧ P y}) →
      {x : Fin 8 → Fin m // P x} :=
    fun ⟨_, ⟨S, hS⟩, ⟨y, _, hy⟩⟩ => ⟨(S.orderEmbOfFin hS) ∘ y, (P_comp (S.orderEmbOfFin hS) y).mpr hy⟩
  have hφ_img : ∀ (r : Fin 9) (S : Finset (Fin m)) (hS : S.card = r.1)
      (y : Fin 8 → Fin r.1) (_hsurj : Function.Surjective y),
      Finset.univ.image ((S.orderEmbOfFin hS) ∘ y) = S := by
    intro r S hS y hsurj
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem S hS (y i)
    · intro hv
      have hmem : v ∈ Set.range (S.orderEmbOfFin hS) := by rw [Finset.range_orderEmbOfFin]; exact hv
      rcases hmem with ⟨j, rfl⟩
      rcases hsurj j with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨r1, hr1⟩, ⟨S1, hS1⟩, ⟨y1, hs1, hy1⟩⟩ ⟨⟨r2, hr2⟩, ⟨S2, hS2⟩, ⟨y2, hs2, hy2⟩⟩ heq
      have hfun : (S1.orderEmbOfFin hS1) ∘ y1 = (S2.orderEmbOfFin hS2) ∘ y2 := congrArg Subtype.val heq
      have hS_eq : S1 = S2 := by
        rw [← hφ_img ⟨r1, hr1⟩ S1 hS1 y1 hs1, ← hφ_img ⟨r2, hr2⟩ S2 hS2 y2 hs2, hfun]
      subst hS_eq
      have hr_eq : r1 = r2 := hS1.symm.trans hS2
      subst hr_eq
      congr 1
      refine Prod.ext rfl ?_
      apply Subtype.ext; funext i
      exact (S1.orderEmbOfFin hS1).injective (congrFun hfun i)
    · rintro ⟨x, hx⟩
      obtain ⟨S, hS_eq⟩ : ∃ S : Finset (Fin m), S = Finset.univ.image x := ⟨_, rfl⟩
      have hSle : S.card ≤ 8 := by
        rw [hS_eq]
        calc (Finset.univ.image x).card ≤ (Finset.univ : Finset (Fin 8)).card := Finset.card_image_le
          _ = 8 := Fintype.card_fin 8
      have hmem : ∀ i : Fin 8, x i ∈ S := fun i => hS_eq.symm ▸ Finset.mem_image_of_mem x (Finset.mem_univ i)
      let iso := S.orderIsoOfFin rfl
      let y : Fin 8 → Fin S.card := fun i => iso.symm ⟨x i, hmem i⟩
      have hcomp : (S.orderEmbOfFin rfl) ∘ y = x := by
        funext i
        rw [Function.comp_apply, Finset.orderEmbOfFin]
        exact congrArg Subtype.val (iso.apply_symm_apply ⟨x i, hmem i⟩)
      have hsurj : Function.Surjective y := by
        intro j
        have hj : (iso j).1 ∈ Finset.univ.image x := hS_eq ▸ (iso j).2
        rcases Finset.mem_image.mp hj with ⟨i, _, hi⟩
        refine ⟨i, ?_⟩
        dsimp [y]; apply iso.injective; rw [iso.apply_symm_apply]; exact Subtype.ext hi
      have hPy : P y := (P_comp (S.orderEmbOfFin rfl) y).mp (hcomp.symm ▸ hx)
      exact ⟨⟨⟨S.card, by omega⟩, ⟨S, rfl⟩, ⟨y, hsurj, hPy⟩⟩, Subtype.ext hcomp⟩
  let e := (Equiv.ofBijective φ hbij).symm
  rw [Fintype.card_congr e, Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun r => Fintype.card ({S : Finset (Fin m) // S.card = r} × {y : Fin 8 → Fin r // Function.Surjective y ∧ P y}))]
  apply Finset.sum_congr rfl; intro r _
  rw [Fintype.card_prod, mul_comm]
  congr 1
  rw [Fintype.card_subtype]
  have hpc : Finset.univ.filter (fun S : Finset (Fin m) => S.card = r) = Finset.powersetCard r (Finset.univ : Finset (Fin m)) := by
    ext S; simp [Finset.mem_powersetCard]
  rw [hpc, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def Δ (g : ℕ → ℤ) (m : ℕ) : ℤ := g (m + 1) - g m

private lemma delta_iter_add (d : ℕ) (f g : ℕ → ℤ) (m : ℕ) :
    (Δ^[d]) (fun x => f x + g x) m = (Δ^[d]) f m + (Δ^[d]) g m := by
  induction d generalizing f g m with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hfun : Δ (fun x => f x + g x) = fun x => Δ f x + Δ g x := by
      funext x; simp only [Δ]; ring
    rw [hfun, ih]

private lemma delta_iter_const_mul (d : ℕ) (c : ℤ) (f : ℕ → ℤ) (m : ℕ) :
    (Δ^[d]) (fun x => c * f x) m = c * (Δ^[d]) f m := by
  induction d generalizing f m with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hfun : Δ (fun x => c * f x) = fun x => c * Δ f x := by
      funext x; simp only [Δ]; ring
    rw [hfun, ih]

private lemma delta_iter_zero (d : ℕ) (m : ℕ) :
    (Δ^[d]) (fun _ => (0 : ℤ)) m = 0 := by
  induction d generalizing m with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    have hfun : Δ (fun _ => (0 : ℤ)) = fun _ => (0 : ℤ) := by funext x; simp [Δ]
    rw [hfun, ih]

private lemma delta_iter_sum {ι : Type*} (s : Finset ι) (d : ℕ) (f : ι → ℕ → ℤ) (m : ℕ) :
    (Δ^[d]) (fun x => ∑ i ∈ s, f i x) m = ∑ i ∈ s, (Δ^[d]) (f i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [delta_iter_zero]
  | insert a s ha ih =>
    have hfun : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; exact Finset.sum_insert ha
    rw [hfun, delta_iter_add, ih, Finset.sum_insert ha]

private lemma delta_iter_choose_eq_zero (r d : ℕ) (hr : r < d) (m : ℕ) :
    (Δ^[d]) (fun x => (Nat.choose x r : ℤ)) m = 0 := by
  induction d generalizing r m with
  | zero => omega
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    cases r with
    | zero =>
      have hfun : Δ (fun x => (Nat.choose x 0 : ℤ)) = fun _ => (0 : ℤ) := by
        funext x; simp [Δ]
      rw [hfun, delta_iter_zero]
    | succ r =>
      have hfun : Δ (fun x => (Nat.choose x (r + 1) : ℤ)) = fun x => (Nat.choose x r : ℤ) := by
        funext x; simp only [Δ, Nat.choose_succ_succ]; push_cast; ring
      rw [hfun]
      exact ih r (by omega) m

private lemma delta_iter_cnt_eq_zero (m : ℕ) :
    (Δ^[9]) (fun x => (cnt x : ℤ)) m = 0 := by
  have hfun : (fun x => (cnt x : ℤ)) = fun x => ∑ r ∈ Finset.range 9, (surjCnt r : ℤ) * (Nat.choose x r : ℤ) := by
    funext x; rw [cnt_eq_sum_choose]; push_cast; rfl
  rw [hfun, delta_iter_sum]
  apply Finset.sum_eq_zero; intro r hr
  rw [Finset.mem_range] at hr
  rw [delta_iter_const_mul, delta_iter_choose_eq_zero r 9 (by omega) m, mul_zero]

private lemma delta_expand (g : ℕ → ℤ) (m : ℕ) :
    (Δ^[9]) g m = g (m + 9) - 9 * g (m + 8) + 36 * g (m + 7) - 84 * g (m + 6) + 126 * g (m + 5) - 126 * g (m + 4) + 84 * g (m + 3) - 36 * g (m + 2) + 9 * g (m + 1) - g m := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id, Δ]
  ring

-- Fast DP to evaluate cnt (n + 1) for n = 1..9
private def prefixValid {m r : ℕ} (x : Fin r → Fin m) : Prop :=
  ∀ i : Fin (r - 2), ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 1, by omega⟩ < x ⟨i.1 + 2, by omega⟩)

private instance {m r : ℕ} (x : Fin r → Fin m) : Decidable (prefixValid x) := by
  unfold prefixValid; infer_instance

private def dp (m : ℕ) : ℕ → Fin m → Bool → ℕ
  | 0, _, inc => if inc then 0 else 1
  | r + 1, u, inc =>
      ∑ v : Fin m, if decide (v.1 < u.1) = inc then
        dp m r v false + (if v.1 < u.1 then 0 else dp m r v true)
      else 0

private lemma dp_correct (m : ℕ) (r : ℕ) :
    ∀ (u : Fin m) (inc : Bool),
      Fintype.card {x : Fin (r + 1) → Fin m //
        prefixValid x ∧ x (Fin.last r) = u ∧
        (if _h : r = 0 then false else decide ((x ⟨r - 1, by omega⟩).1 < (x (Fin.last r)).1)) = inc} =
      dp m r u inc := by
  induction r with
  | zero =>
    intro u inc
    simp only [dp, ↓reduceDIte]
    by_cases hinc : inc = true
    · subst hinc; simp only [↓reduceIte, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, _, _, h⟩ => by simp at h⟩
    · have hf : inc = false := by cases inc <;> simp_all
      subst hf; simp only [Bool.false_eq_true, ↓reduceIte]
      refine Fintype.card_eq_one_iff.mpr ⟨⟨fun _ => u, fun i => i.elim0, rfl, trivial⟩, fun ⟨x, _, hu, _⟩ => ?_⟩
      apply Subtype.ext; funext i; fin_cases i; exact hu
  | succ r ih =>
    intro u inc
    simp only [dp]
    let S := {x : Fin (r + 2) → Fin m //
      prefixValid x ∧ x (Fin.last (r + 1)) = u ∧
      decide ((x ⟨r, by omega⟩).1 < (x (Fin.last (r + 1))).1) = inc}
    have hLHS : Fintype.card {x : Fin (r + 2) → Fin m //
        prefixValid x ∧ x (Fin.last (r + 1)) = u ∧
        (if h : r + 1 = 0 then false else decide ((x ⟨r + 1 - 1, by omega⟩).1 < (x (Fin.last (r + 1))).1)) = inc} =
        Fintype.card S := by
      refine Fintype.card_congr ⟨fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, by simpa using h3⟩,
        fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, by simpa using h3⟩, fun ⟨_, _, _, _⟩ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩
    rw [hLHS]
    let e : S ≃ Σ v : Fin m, Σ b : Bool,
        {y : Fin (r + 1) → Fin m //
          prefixValid y ∧ y (Fin.last r) = v ∧
          (if h : r = 0 then false else decide ((y ⟨r - 1, by omega⟩).1 < (y (Fin.last r)).1)) = b ∧
          decide (v.1 < u.1) = inc ∧
          (b = true → ¬(v.1 < u.1))} :=
      { toFun := fun ⟨x, hpx, hlast, hinc⟩ =>
          let y : Fin (r + 1) → Fin m := fun i => x i.castSucc
          let v : Fin m := y (Fin.last r)
          let b : Bool := if h : r = 0 then false else decide ((y ⟨r - 1, by omega⟩).1 < (y (Fin.last r)).1)
          have hpy : prefixValid y := fun i => hpx ⟨i.1, by omega⟩
          have hcond : b = true → ¬(v.1 < u.1) := by
            intro hb hforb
            by_cases hr0 : r = 0
            · simp [b, hr0] at hb
            · simp only [b, hr0, ↓reduceDIte, decide_eq_true_eq] at hb
              have h := hpx ⟨r - 1, by omega⟩
              have e0 : x ⟨r - 1, by omega⟩ = y ⟨r - 1, by omega⟩ := rfl
              have e1 : x ⟨r - 1 + 1, by omega⟩ = v := by
                have : (⟨r - 1 + 1, by omega⟩ : Fin (r + 2)) = (Fin.last r).castSucc := by ext; simp [Fin.last]; omega
                rw [this]
              have e2 : x ⟨r - 1 + 2, by omega⟩ = u := by
                have : (⟨r - 1 + 2, by omega⟩ : Fin (r + 2)) = Fin.last (r + 1) := by ext; simp [Fin.last]; omega
                rw [this]; exact hlast
              rw [e0, e1, e2] at h
              exact h ⟨hb, hforb⟩
          ⟨v, b, ⟨y, hpy, rfl, rfl, by
            have hv : x ⟨r, by omega⟩ = v := rfl
            rw [hv, hlast] at hinc; exact hinc, hcond⟩⟩
        invFun := fun ⟨v, b, ⟨y, hpy, hyv, hyb, hvu, hcond⟩⟩ =>
          let x : Fin (r + 2) → Fin m := Fin.snoc y u
          have hpx : prefixValid x := by
            by_cases hr0 : r = 0
            · subst hr0; intro i; exact i.elim0
            · intro i
              by_cases hlt : i.1 < r - 1
              · have := hpy ⟨i.1, by omega⟩
                have h0 : (⟨i.1, by omega⟩ : Fin (r + 2)) = (⟨i.1, by omega⟩ : Fin (r + 1)).castSucc := rfl
                have h1 : (⟨i.1 + 1, by omega⟩ : Fin (r + 2)) = (⟨i.1 + 1, by omega⟩ : Fin (r + 1)).castSucc := rfl
                have h2 : (⟨i.1 + 2, by omega⟩ : Fin (r + 2)) = (⟨i.1 + 2, by omega⟩ : Fin (r + 1)).castSucc := rfl
                dsimp [x]; rw [h0, h1, h2, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
                exact this
              · have hi_eq : i.1 = r - 1 := by omega
                have h0 : (⟨i.1, by omega⟩ : Fin (r + 2)) = (⟨r - 1, by omega⟩ : Fin (r + 1)).castSucc := by ext; simp; omega
                have h1' : (⟨i.1 + 1, by omega⟩ : Fin (r + 2)) = (Fin.last r).castSucc := by ext; simp [Fin.last]; omega
                have h2' : (⟨i.1 + 2, by omega⟩ : Fin (r + 2)) = Fin.last (r + 1) := by ext; simp [Fin.last]; omega
                dsimp [x]; rw [h0, h1', h2', Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
                intro ⟨h1, h2⟩
                have hb : b = true := by
                  rw [← hyb, dif_neg hr0, decide_eq_true_eq]; exact h1
                rw [hyv] at h2
                exact hcond hb h2
          ⟨x, hpx, by simp [x], by
            have h1 : x ⟨r, by omega⟩ = v := by
              have : (⟨r, by omega⟩ : Fin (r + 2)) = (Fin.last r).castSucc := rfl
              dsimp [x]; rw [this, Fin.snoc_castSucc, hyv]
            have h2 : x (Fin.last (r + 1)) = u := by simp [x]
            rw [h1, h2]; exact hvu⟩
        left_inv := fun ⟨x, _, hlast, _⟩ => by
          apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
          · simp [hlast]
          · intro j; simp
        right_inv := fun ⟨v, b, ⟨y, _, hyv, hyb, _, _⟩⟩ => by
          have hy : (fun i : Fin (r + 1) => (Fin.snoc y u : Fin (r + 2) → Fin m) i.castSucc) = y := by funext i; simp
          have hv : (fun i : Fin (r + 1) => (Fin.snoc y u : Fin (r + 2) → Fin m) i.castSucc) (Fin.last r) = v := by
            rw [hy]; exact hyv
          refine Sigma.ext hv ?_
          subst hv
          have hb : (if h : r = 0 then false else decide (((Fin.snoc y u : Fin (r + 2) → Fin m) (⟨r - 1, by omega⟩ : Fin (r + 1)).castSucc).1 < ((Fin.snoc y u : Fin (r + 2) → Fin m) (Fin.last r).castSucc).1)) = b := by
            by_cases hr0 : r = 0
            · simpa [hr0] using hyb
            · simp only [hr0, ↓reduceDIte, Fin.snoc_castSucc] at hyb ⊢; exact hyb
          refine heq_of_eq (Sigma.ext hb ?_)
          subst hb
          apply heq_of_eq; apply Subtype.ext; exact hy }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro v _
    rw [Fintype.card_sigma, Fintype.sum_bool]
    by_cases hvu : decide (v.1 < u.1) = inc
    · rw [if_pos hvu, add_comm]
      congr 1
      · rw [← ih v false]
        refine Fintype.card_congr ⟨fun ⟨y, h1, h2, h3, _, _⟩ => ⟨y, h1, h2, h3⟩,
          fun ⟨y, h1, h2, h3⟩ => ⟨y, h1, h2, h3, hvu, by simp⟩,
          fun ⟨_, _, _, _, _, _⟩ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩
      · by_cases hforb : v.1 < u.1
        · rw [if_pos hforb, Fintype.card_eq_zero_iff]
          exact ⟨fun ⟨_, _, _, _, _, hc⟩ => hc rfl hforb⟩
        · rw [if_neg hforb, ← ih v true]
          refine Fintype.card_congr ⟨fun ⟨y, h1, h2, h3, _, _⟩ => ⟨y, h1, h2, h3⟩,
            fun ⟨y, h1, h2, h3⟩ => ⟨y, h1, h2, h3, hvu, fun _ => hforb⟩,
            fun ⟨_, _, _, _, _, _⟩ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩
    · rw [if_neg hvu]
      have hz : ∀ b : Bool, Fintype.card {y : Fin (r + 1) → Fin m //
          prefixValid y ∧ y (Fin.last r) = v ∧
          (if h : r = 0 then false else decide ((y ⟨r - 1, by omega⟩).1 < (y (Fin.last r)).1)) = b ∧
          decide (v.1 < u.1) = inc ∧
          (b = true → ¬(v.1 < u.1))} = 0 := by
        intro b; rw [Fintype.card_eq_zero_iff]; exact ⟨fun ⟨_, _, _, _, h, _⟩ => hvu h⟩
      rw [hz true, hz false]

private lemma cnt_eq_dp (m : ℕ) :
    cnt m = ∑ u : Fin m, (dp m 7 u false + dp m 7 u true) := by
  unfold cnt
  have hp_iff : ∀ x : Fin 8 → Fin m, P x ↔ prefixValid x := fun _ => Iff.rfl
  let e : {x : Fin 8 → Fin m // P x} ≃
      Σ u : Fin m, Σ b : Bool,
        {x : Fin 8 → Fin m //
          prefixValid x ∧ x (Fin.last 7) = u ∧
          (if h : 7 = 0 then false else decide ((x ⟨7 - 1, by omega⟩).1 < (x (Fin.last 7)).1)) = b} :=
    { toFun := fun ⟨x, hx⟩ => ⟨x (Fin.last 7), _, ⟨x, (hp_iff x).mp hx, rfl, rfl⟩⟩
      invFun := fun ⟨_, _, ⟨x, hx, _, _⟩⟩ => ⟨x, (hp_iff x).mpr hx⟩
      left_inv := fun _ => rfl
      right_inv := fun ⟨u, b, ⟨x, _, hu, hb⟩⟩ => by
        subst hu; subst hb; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro u _
  rw [Fintype.card_sigma, Fintype.sum_bool, add_comm, dp_correct m 7 u false, dp_correct m 7 u true]

private lemma a_eq_cnt (n : ℕ) (hn : 1 ≤ n) : a n = cnt (n + 1) := by
  unfold a cnt; rw [if_neg (by omega)]
  refine Fintype.card_congr ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩, fun _ => rfl, fun _ => rfl⟩

private lemma a_eq_dp (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ u : Fin (n + 1), (dp (n + 1) 7 u false + dp (n + 1) 7 u true) := by
  rw [a_eq_cnt n hn, cnt_eq_dp]

private lemma a_zero : a 0 = 0 := by unfold a; simp

private lemma a_val_1 : a 1 = 256 := by rw [a_eq_dp 1 (by omega)]; decide
private lemma a_val_2 : a 2 = 5157 := by rw [a_eq_dp 2 (by omega)]; decide
private lemma a_val_3 : a 3 = 43681 := by rw [a_eq_dp 3 (by omega)]; decide
private lemma a_val_4 : a 4 = 232275 := by rw [a_eq_dp 4 (by omega)]; decide
private lemma a_val_5 : a 5 = 919413 := by rw [a_eq_dp 5 (by omega)]; decide
private lemma a_val_6 : a 6 = 2964416 := by rw [a_eq_dp 6 (by omega)]; decide
private lemma a_val_7 : a 7 = 8216484 := by rw [a_eq_dp 7 (by omega)]; decide
private lemma a_val_8 : a 8 = 20273247 := by rw [a_eq_dp 8 (by omega)]; decide
private lemma a_val_9 : a 9 = 45611500 := by rw [a_eq_dp 9 (by omega)]; decide

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a200790.main := by
  have hrec : ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ) := by
    intro n hn
    have h0 := delta_iter_cnt_eq_zero (n - 9 + 1)
    rw [delta_expand] at h0
    have hcnt : ∀ j : ℕ, j ≤ 9 → cnt (n - 9 + 1 + (9 - j)) = a (n - j) := by
      intro j hj
      rw [a_eq_cnt (n - j) (by omega)]
      congr 1; omega
    simp only [hcnt 0 (by omega), hcnt 1 (by omega), hcnt 2 (by omega), hcnt 3 (by omega), hcnt 4 (by omega), hcnt 5 (by omega), hcnt 6 (by omega), hcnt 7 (by omega), hcnt 8 (by omega), hcnt 9 (by omega),
      Nat.sub_zero] at h0
    linarith
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 9 = 1 - PowerSeries.C 9 * PowerSeries.X ^ 1 + PowerSeries.C 36 * PowerSeries.X ^ 2 - PowerSeries.C 84 * PowerSeries.X ^ 3 + PowerSeries.C 126 * PowerSeries.X ^ 4 - PowerSeries.C 126 * PowerSeries.X ^ 5 + PowerSeries.C 84 * PowerSeries.X ^ 6 - PowerSeries.C 36 * PowerSeries.X ^ 7 + PowerSeries.C 9 * PowerSeries.X ^ 8 - PowerSeries.X ^ 9 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (256 + 2853 * PowerSeries.X + 6484 * PowerSeries.X ^ 2 + 3294 * PowerSeries.X ^ 3 + 522 * PowerSeries.X ^ 4 - 79 * PowerSeries.X ^ 5 + 36 * PowerSeries.X ^ 6 - 9 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8) = PowerSeries.C 256 * PowerSeries.X ^ 1 + PowerSeries.C 2853 * PowerSeries.X ^ 2 + PowerSeries.C 6484 * PowerSeries.X ^ 3 + PowerSeries.C 3294 * PowerSeries.X ^ 4 + PowerSeries.C 522 * PowerSeries.X ^ 5 - PowerSeries.C 79 * PowerSeries.X ^ 6 + PowerSeries.C 36 * PowerSeries.X ^ 7 - PowerSeries.C 9 * PowerSeries.X ^ 8 + PowerSeries.X ^ 9 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]; try norm_num
  · simp [a_zero, a_val_1, a_val_2]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]; try norm_num
  · have hgt : 9 < m + 10 := by omega
    have hr := hrec (m + 10) hgt
    have hrq : (a (m + 10) : ℚ) = 9 * (a (m + 9) : ℚ) - 36 * (a (m + 8) : ℚ) + 84 * (a (m + 7) : ℚ) - 126 * (a (m + 6) : ℚ) + 126 * (a (m + 5) : ℚ) - 84 * (a (m + 4) : ℚ) + 36 * (a (m + 3) : ℚ) - 9 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, show 3 ≤ m + 10 by omega, show 4 ≤ m + 10 by omega, show 5 ≤ m + 10 by omega, show 6 ≤ m + 10 by omega, show 7 ≤ m + 10 by omega, show 8 ≤ m + 10 by omega, show 9 ≤ m + 10 by omega, ↓reduceIte,
      show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega,
      show ¬(m + 10 = 1) by omega, show ¬(m + 10 = 2) by omega, show ¬(m + 10 = 3) by omega, show ¬(m + 10 = 4) by omega, show ¬(m + 10 = 5) by omega, show ¬(m + 10 = 6) by omega, show ¬(m + 10 = 7) by omega, show ¬(m + 10 = 8) by omega, show ¬(m + 10 = 9) by omega]
    linarith

end OMA.P_oeis_a200790

theorem OMA.solution : type_of% @OMA.S_oeis_a200790.main :=
  OMA.P_oeis_a200790.solution
