import OMAStatements.S_oeis_a270924
import Mathlib

namespace OMA.S_oeis_a270924

open PowerSeries BigOperators

private lemma zmod_prime_pow_card_sub_fix_dvd
    {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    {X : Type*} [Fintype X] [DecidableEq X]
    (act : ZMod (p ^ r) → X → X)
    (hact_zero : ∀ x, act 0 x = x)
    (hact_add : ∀ g₁ g₂ x, act (g₁ + g₂) x = act g₁ (act g₂ x)) :
    (p ^ r : ℕ) ∣
      (Fintype.card X -
        (Finset.univ.filter fun x : X => act ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) x = x).card) := by
  let q := p ^ r
  let q' := p ^ (r - 1)
  have hq_pos : 0 < q := pow_pos hp.pos r
  have hq'_pos : 0 < q' := pow_pos hp.pos (r - 1)
  have : NeZero q := ⟨hq_pos.ne'⟩
  have hqq' : q = p * q' := by
    simp only [q, q']; rw [← pow_succ', Nat.sub_add_cancel hr]
  let g₀ : ZMod q := (q' : ZMod q)
  let Fix : Finset X := Finset.univ.filter fun x => act g₀ x = x
  let Free : Finset X := Finset.univ.filter fun x => act g₀ x ≠ x
  have hcard_split : Fintype.card X = Fix.card + Free.card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (p := fun x => act g₀ x = x)
    simpa [Fix, Free] using h.symm
  change q ∣ Fintype.card X - Fix.card
  rw [hcard_split, Nat.add_sub_cancel_left]
  have hact_nsmul : ∀ (n : ℕ) (g : ZMod q) (x : X), act g x = x → act (n • g) x = x := by
    intro n g x hx
    induction n with
    | zero => simpa using hact_zero x
    | succ n ih => rw [succ_nsmul, hact_add, hx, ih]
  have hfree_triv : ∀ x ∈ Free, ∀ g : ZMod q, act g x = x → g = 0 := by
    intro x hx g hg
    by_contra hg0
    have hxfree : act g₀ x ≠ x := (Finset.mem_filter.mp hx).2
    set k := g.val
    have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h => hg0 ((ZMod.val_eq_zero g).mp h)
    have hk_lt : k < q := ZMod.val_lt g
    set v := k.factorization p
    have hv_lt : v < r := by
      by_contra hge; push Not at hge
      have hdvd : q ∣ k := dvd_trans (Nat.pow_dvd_pow p hge) (Nat.ordProj_dvd k p)
      exact absurd (Nat.le_of_dvd hk_pos hdvd) (not_le_of_gt hk_lt)
    obtain ⟨u, hku⟩ := Nat.ordProj_dvd k p
    have hpu : ¬ p ∣ u := by
      intro ⟨w, hw⟩
      have h1 : p ^ (v + 1) ∣ k := ⟨w, by rw [hku, hw, pow_succ]; ring⟩
      have h2 := (hp.pow_dvd_iff_le_factorization hk_pos.ne').mp h1
      omega
    have hcop : Nat.Coprime u q := (hp.coprime_iff_not_dvd.mpr hpu).symm.pow_right r
    set w : ℕ := ((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod q)ˣ).val.val
    have huw : (u : ZMod q) * (w : ZMod q) = 1 := by
      have hw : (w : ZMod q) = (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod q)ˣ) : ZMod q) := by
        simp [w]
      have hu : (u : ZMod q) = ((ZMod.unitOfCoprime u hcop : (ZMod q)ˣ) : ZMod q) := rfl
      rw [hu, hw, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmul_eq : (p ^ (r - 1 - v) * w) • g = g₀ := by
      rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val g]
      change ((p ^ (r - 1 - v) * w : ℕ) : ZMod q) * (k : ZMod q) = (q' : ZMod q)
      rw [← Nat.cast_mul, hku]
      have hre : p ^ (r - 1 - v) * w * (p ^ v * u) = q' * (u * w) := by
        have hpow_add : p ^ (r - 1 - v) * p ^ v = q' := by
          rw [← pow_add]; simp only [q']; congr 1; omega
        calc p ^ (r - 1 - v) * w * (p ^ v * u)
            = (p ^ (r - 1 - v) * p ^ v) * (u * w) := by ring
          _ = q' * (u * w) := by rw [hpow_add]
      rw [hre, Nat.cast_mul, Nat.cast_mul, huw, mul_one]
    exact hxfree (hmul_eq ▸ hact_nsmul (p ^ (r - 1 - v) * w) g x hg)
  let orb (x : X) : Finset X := Finset.univ.image fun g : ZMod q => act g x
  have horb_sub : ∀ x ∈ Free, orb x ⊆ Free := by
    intro x hx y hy
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hfix => ?_⟩
    have h1 : act g (act g₀ x) = act g x := by rw [← hact_add, add_comm g g₀, hact_add, hfix]
    have h2 := congr_arg (act (-g)) h1
    rw [← hact_add (-g) g (act g₀ x), ← hact_add (-g) g x, neg_add_cancel, hact_zero, hact_zero] at h2
    exact (Finset.mem_filter.mp hx).2 h2
  have horb_card : ∀ x ∈ Free, (orb x).card = q := by
    intro x hx
    rw [Finset.card_image_of_injective _ (fun g₁ g₂ heq => by
      have h1 := congr_arg (act (-g₂)) heq
      rw [← hact_add, ← hact_add, neg_add_cancel, hact_zero] at h1
      exact eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact hfree_triv x hx (-g₂ + g₁) h1))]
    rw [Finset.card_univ, ZMod.card]
  have horb_eq_or_disj : ∀ x₁ x₂ : X, orb x₁ = orb x₂ ∨ Disjoint (orb x₁) (orb x₂) := by
    intro x₁ x₂
    by_cases h : ∃ y, y ∈ orb x₁ ∧ y ∈ orb x₂
    · left
      obtain ⟨y, hy1, hy2⟩ := h
      obtain ⟨g₁, _, rfl⟩ := Finset.mem_image.mp hy1
      obtain ⟨g₂, _, heq⟩ := Finset.mem_image.mp hy2
      have hx2 : x₂ = act (g₁ - g₂) x₁ := by
        have := congr_arg (act (-g₂)) heq
        rw [← hact_add, ← hact_add, neg_add_cancel, hact_zero] at this
        simpa [sub_eq_neg_add] using this
      ext z
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨g, rfl⟩; exact ⟨g - (g₁ - g₂), by rw [hx2, ← hact_add, sub_add_cancel]⟩
      · rintro ⟨g, rfl⟩; exact ⟨g + (g₁ - g₂), by rw [hx2, ← hact_add]⟩
    · right; rw [Finset.disjoint_left]; intro y h1 h2; exact h ⟨y, h1, h2⟩
  let S : Finset (Finset X) := Free.image orb
  have hFree_eq : Free = S.biUnion id := by
    ext x
    simp only [S, Finset.mem_biUnion, Finset.mem_image, id_eq]
    constructor
    · intro hx; exact ⟨orb x, ⟨x, hx, rfl⟩, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hact_zero x⟩⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩; exact horb_sub y hy hxy
  have hS_disj : (S : Set (Finset X)).PairwiseDisjoint id := by
    intro O₁ hO₁ O₂ hO₂ hne
    obtain ⟨x₁, _, rfl⟩ := Finset.mem_image.mp hO₁
    obtain ⟨x₂, _, rfl⟩ := Finset.mem_image.mp hO₂
    exact (horb_eq_or_disj x₁ x₂).resolve_left hne
  rw [hFree_eq, Finset.card_biUnion hS_disj]
  have hsum : ∑ O ∈ S, O.card = ∑ _O ∈ S, q := by
    refine Finset.sum_congr rfl fun O hO => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
    exact horb_card x hx
  simp only [id_eq]; rw [hsum, Finset.sum_const, smul_eq_mul]
  exact dvd_mul_left q S.card


/-! ### Part 2: Universal Gauss Congruence for `[X^n] F(X)^n` via Cyclic `ZMod (p^r)` Action -/

private lemma coeff_pow_eq_sum_fin (F : PowerSeries ℕ) :
    ∀ (k m : ℕ), PowerSeries.coeff m (F ^ k) =
      ∑ d ∈ (Finset.univ : Finset (Fin k → Fin (m + 1))).filter (fun d => ∑ i, (d i).val = m),
        ∏ i, PowerSeries.coeff (d i).val F := by
  intro k
  induction k with
  | zero =>
      intro m
      rw [pow_zero, PowerSeries.coeff_one]
      by_cases hm : m = 0
      · subst hm
        rw [if_pos rfl]
        have h1 : (Finset.univ : Finset (Fin 0 → Fin 1)).filter (fun d => ∑ i, (d i).val = 0) = {Fin.elim0} := by
          ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Finset.univ_eq_empty, Finset.sum_empty, true_iff]
          funext i; exact Fin.elim0 i
        rw [h1, Finset.sum_singleton]; simp
      · rw [if_neg hm]
        have h0 : (Finset.univ : Finset (Fin 0 → Fin (m + 1))).filter (fun d => ∑ i, (d i).val = m) = ∅ := by
          ext d; simp [Ne.symm hm]
        rw [h0, Finset.sum_empty]
  | succ k ih =>
      intro m
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (F ^ k) * PowerSeries.coeff b F)]
      -- Rewrite each `coeff a (F ^ k)` using `ih a`, then lift `Fin (a + 1)` to `Fin (m + 1)`!
      have hlift : ∀ a ≤ m, PowerSeries.coeff a (F ^ k) =
          ∑ d ∈ (Finset.univ : Finset (Fin k → Fin (m + 1))).filter (fun d => ∑ i, (d i).val = a),
            ∏ i, PowerSeries.coeff (d i).val F := by
        intro a ha
        rw [ih a]
        refine Finset.sum_nbij (fun d i => ⟨(d i).val, by omega⟩) ?_ ?_ ?_ ?_
        · intro d hd; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢; exact hd
        · intro d1 _ d2 _ h12; funext i; exact Fin.ext (by have := congrArg Fin.val (congrFun h12 i); simpa using this)
        · intro d hd
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd
          have hle : ∀ i, (d i).val ≤ a := fun i => by
            rw [← hd]; exact Finset.single_le_sum (f := fun j => (d j).val) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          refine ⟨fun i => ⟨(d i).val, by have := hle i; omega⟩, ?_, ?_⟩
          · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]; exact hd
          · funext i; rfl
        · intro d _; rfl
      have h1 : ∑ a ∈ Finset.range (m + 1), PowerSeries.coeff a (F ^ k) * PowerSeries.coeff (m - a) F =
          ∑ p ∈ (Finset.range (m + 1)).sigma (fun a =>
            (Finset.univ : Finset (Fin k → Fin (m + 1))).filter (fun d => ∑ i, (d i).val = a)),
            (∏ i, PowerSeries.coeff (p.2 i).val F) * PowerSeries.coeff (m - p.1) F := by
        rw [← Finset.sum_sigma' (Finset.range (m + 1))
          (fun a => (Finset.univ : Finset (Fin k → Fin (m + 1))).filter (fun d => ∑ i, (d i).val = a))
          (fun a d => (∏ i, PowerSeries.coeff (d i).val F) * PowerSeries.coeff (m - a) F)]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [hlift a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)), Finset.sum_mul]
      rw [h1]
      refine Finset.sum_nbij (fun p => Fin.snoc p.2 ⟨m - p.1, by omega⟩) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, hp.2]
        omega
      · intro p1 hp1 p2 hp2 h12
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
          Finset.mem_univ, true_and] at hp1 hp2
        have hlast := congrArg Fin.val (congrFun h12 (Fin.last k))
        simp only [Fin.snoc_last] at hlast
        have hp12 : p1.1 = p2.1 := by omega
        have hd12 : p1.2 = p2.2 := by
          funext i
          have hi := congrFun h12 i.castSucc
          simpa only [Fin.snoc_castSucc] using hi
        exact Sigma.ext hp12 (heq_of_eq hd12)
      · intro d hd
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        set a := ∑ i : Fin k, (d i.castSucc).val
        have ha_eq : a + (d (Fin.last k)).val = m := by rwa [Fin.sum_univ_castSucc] at hd
        refine ⟨⟨a, fun i => d i.castSucc⟩, ?_, ?_⟩
        · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨by omega, rfl⟩
        · funext i
          refine Fin.lastCases ?_ (fun j => by simp) i
          simp only [Fin.snoc_last]
          apply Fin.ext; dsimp only; omega
      · intro p _
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]

private lemma coeff_pow_eq_card_sigma (F : PowerSeries ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    PowerSeries.coeff m (F ^ Fintype.card ι) =
      Fintype.card (Σ d : {d : ι → Fin (m + 1) // ∑ i, (d i).val = m}, ∀ i : ι, Fin (PowerSeries.coeff (d.1 i).val F)) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]
  have hsub : ∑ x : {d : ι → Fin (m + 1) // ∑ i, (d i).val = m}, ∏ i, PowerSeries.coeff (x.1 i).val F =
      ∑ d ∈ (Finset.univ : Finset (ι → Fin (m + 1))).filter (fun d => ∑ i, (d i).val = m),
        ∏ i, PowerSeries.coeff (d i).val F := by
    refine Finset.sum_nbij (fun x => x.1) ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
    · intro a _ b _ hab; exact Subtype.ext hab
    · intro d hd; exact ⟨⟨d, (Finset.mem_filter.mp hd).2⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
    · intro _ _; rfl
  rw [hsub, coeff_pow_eq_sum_fin]
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  symm
  refine Finset.sum_nbij (fun d => fun j => d (e.symm j)) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans hd
  · intro d1 _ d2 _ h12
    funext i
    have := congrFun h12 (e i)
    simpa using this
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    refine ⟨fun i => d (e i), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans hd
    · funext j; simp
  · intro d _
    exact (Fintype.prod_equiv e.symm _ _ (fun _ => rfl)).symm

private lemma coeff_pow_gauss_cong (F : PowerSeries ℕ) {p r m : ℕ}
    (hp : p.Prime) (hr : 1 ≤ r) (_hm : 1 ≤ m) :
    ((p ^ r : ℕ) : ℤ) ∣
      ((PowerSeries.coeff (m * p ^ r) (F ^ (m * p ^ r)) : ℕ) : ℤ) -
      ((PowerSeries.coeff (m * p ^ (r - 1)) (F ^ (m * p ^ (r - 1))) : ℕ) : ℤ) := by
  let q := p ^ r
  let q' := p ^ (r - 1)
  have hq_pos : 0 < q := pow_pos hp.pos r
  have hq'_pos : 0 < q' := pow_pos hp.pos (r - 1)
  have : NeZero q := ⟨hq_pos.ne'⟩
  have : NeZero q' := ⟨hq'_pos.ne'⟩
  have hqq' : q = p * q' := by
    simp only [q, q']; rw [← pow_succ', Nat.sub_add_cancel hr]
  have hdvd_qq' : q' ∣ q := ⟨p, by rw [hqq', mul_comm]⟩
  let N := m * q
  let N' := m * q'
  have hNN' : N = p * N' := by simp only [N, N', hqq']; ring
  let X := Σ d : {d : ZMod q × Fin m → Fin (N + 1) // ∑ i, (d i).val = N},
    ∀ i : ZMod q × Fin m, Fin (PowerSeries.coeff (d.1 i).val F)
  let X' := Σ d : {d : ZMod q' × Fin m → Fin (N' + 1) // ∑ i, (d i).val = N'},
    ∀ i : ZMod q' × Fin m, Fin (PowerSeries.coeff (d.1 i).val F)
  have hcardX : Fintype.card X = PowerSeries.coeff N (F ^ N) := by
    have hcard_idx : Fintype.card (ZMod q × Fin m) = N := by
      simp [Fintype.card_prod, ZMod.card, N, mul_comm]
    have h := coeff_pow_eq_card_sigma F (ι := ZMod q × Fin m) N
    rw [hcard_idx] at h
    exact h.symm
  have hcardX' : Fintype.card X' = PowerSeries.coeff N' (F ^ N') := by
    have hcard_idx : Fintype.card (ZMod q' × Fin m) = N' := by
      simp [Fintype.card_prod, ZMod.card, N', mul_comm]
    have h := coeff_pow_eq_card_sigma F (ι := ZMod q' × Fin m) N'
    rw [hcard_idx] at h
    exact h.symm
  let act : ZMod q → X → X := fun g x =>
    ⟨⟨fun p => x.1.1 (p.1 + g, p.2), by
      have hbij : ∑ p : ZMod q × Fin m, (x.1.1 (p.1 + g, p.2)).val = ∑ p : ZMod q × Fin m, (x.1.1 p).val :=
        Fintype.sum_equiv ((Equiv.addRight g).prodCongr (Equiv.refl (Fin m))) _ _ (fun _ => rfl)
      rw [hbij, x.1.2]⟩,
     fun p => x.2 (p.1 + g, p.2)⟩
  have hact_zero : ∀ x : X, act 0 x = x := by
    intro ⟨⟨d, hd⟩, w⟩
    refine Sigma.ext (Subtype.ext (funext fun ⟨z, j⟩ => by simp [act])) ?_
    refine Function.hfunext rfl fun ⟨z, j⟩ ⟨z', j'⟩ hzz => ?_
    cases hzz
    dsimp only [act]; rw [add_zero]
  have hact_add : ∀ g₁ g₂ x, act (g₁ + g₂) x = act g₁ (act g₂ x) := by
    intro g₁ g₂ ⟨⟨d, hd⟩, w⟩
    refine Sigma.ext (Subtype.ext (funext fun ⟨z, j⟩ => by simp [act, add_assoc, add_comm g₁ g₂])) ?_
    refine Function.hfunext rfl fun ⟨z, j⟩ ⟨z', j'⟩ hzz => ?_
    cases hzz
    dsimp only [act]; rw [add_assoc, add_comm g₁ g₂]
  -- Now show `Fix = {x : X // act (q' : ZMod q) x = x}` has cardinality `Fintype.card X'`!
  let g₀ : ZMod q := (q' : ZMod q)
  let proj : ZMod q →+* ZMod q' := ZMod.castHom hdvd_qq' (ZMod q')
  have hproj_g₀ : proj g₀ = 0 := by
    simp [proj, g₀]
  have hproj_sum : ∀ (f : ZMod q' → ℕ), ∑ z : ZMod q, f (proj z) = p * ∑ z' : ZMod q', f z' := by
    intro f
    -- Reindex `z : ZMod q` as `(a : Fin p, b : Fin q') ↦ (a * q' + b : ZMod q)`!
    let e : Fin p × ZMod q' ≃ ZMod q :=
      { toFun := fun ab => ((ab.1.val * q' + ab.2.val : ℕ) : ZMod q)
        invFun := fun z => (⟨z.val / q', Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hqq']; exact ZMod.val_lt z)⟩,
                            proj z)
        left_inv := fun ⟨a, b⟩ => by
          have hb : b.val < q' := ZMod.val_lt b
          have hlt : a.val * q' + b.val < q := by
            have ha : a.val + 1 ≤ p := a.isLt
            calc a.val * q' + b.val < a.val * q' + q' := Nat.add_lt_add_left hb _
              _ = (a.val + 1) * q' := by ring
              _ ≤ p * q' := Nat.mul_le_mul_right q' ha
              _ = q := hqq'.symm
          have hval : (((a.val * q' + b.val : ℕ) : ZMod q)).val = a.val * q' + b.val :=
            ZMod.val_natCast_of_lt hlt
          refine Prod.ext (Fin.ext ?_) ?_
          · dsimp only
            rw [hval, mul_comm a.val q', Nat.mul_add_div hq'_pos, Nat.div_eq_of_lt hb, add_zero]
          · dsimp only [proj]
            rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
                ZMod.natCast_zmod_val]
        right_inv := fun z => by
          have hval_proj : (proj z).val = z.val % q' := by
            have h1 : proj z = ((z.val : ℕ) : ZMod q') := by
              rw [← ZMod.natCast_zmod_val z]; simp [proj]
            rw [h1, ZMod.val_natCast]
          dsimp only
          rw [hval_proj, mul_comm (z.val / q'), Nat.div_add_mod, ZMod.natCast_zmod_val] }
    rw [← Fintype.sum_equiv e (fun ab => f (proj (e ab))) (fun z => f (proj z)) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hconst : ∀ a : Fin p, ∑ b : ZMod q', f (proj (e (a, b))) = ∑ b : ZMod q', f b := by
      intro a
      refine Finset.sum_congr rfl fun b _ => ?_
      have he : proj (e (a, b)) = b := by
        change proj ((a.val * q' + b.val : ℕ) : ZMod q) = b
        rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
            ZMod.natCast_zmod_val]
      rw [he]
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hfix_card : (Finset.univ.filter fun x : X => act g₀ x = x).card = Fintype.card X' := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun ⟨x, hx⟩ =>
          have hfix : act g₀ x = x := (Finset.mem_filter.mp hx).2
          have hd_per : ∀ z j, x.1.1 (z + g₀, j) = x.1.1 (z, j) := fun z j => by
            have h1 := congrArg (fun y : X => y.1.1 (z, j)) hfix
            exact h1
          have hd_mod : ∀ z j, x.1.1 (z, j) = x.1.1 (((proj z).val : ZMod q), j) := by
            intro z j
            have hz : z = ((proj z).val : ZMod q) + ((z.val / q' : ℕ) : ZMod q) * g₀ := by
              have hval_proj : (proj z).val = z.val % q' := by
                have h1 : proj z = ((z.val : ℕ) : ZMod q') := by
                  rw [← ZMod.natCast_zmod_val z]; simp [proj]
                rw [h1, ZMod.val_natCast]
              rw [hval_proj]
              simp only [g₀, ← Nat.cast_mul, ← Nat.cast_add]
              rw [add_comm, mul_comm, Nat.div_add_mod, ZMod.natCast_zmod_val]
            have hiter : ∀ (t : ℕ) (w : ZMod q), x.1.1 (w + (t : ZMod q) * g₀, j) = x.1.1 (w, j) := by
              intro t; induction t with
              | zero => intro w; simp
              | succ t iht =>
                  intro w
                  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, hd_per, iht]
            conv_lhs => rw [hz]
            exact hiter (z.val / q') _
          have hsum' : ∑ p' : ZMod q' × Fin m, (x.1.1 ((p'.1.val : ZMod q), p'.2)).val = N' := by
            have htot := x.1.2
            rw [Fintype.sum_prod_type] at htot ⊢
            have hrew : ∑ z : ZMod q, ∑ j : Fin m, (x.1.1 (z, j)).val =
                ∑ z : ZMod q, ∑ j : Fin m, (x.1.1 (((proj z).val : ZMod q), j)).val :=
              Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j _ => by rw [hd_mod z j]
            rw [hrew, hproj_sum (fun z' => ∑ j : Fin m, (x.1.1 ((z'.val : ZMod q), j)).val)] at htot
            exact Nat.eq_of_mul_eq_mul_left hp.pos (htot.trans hNN')
          ⟨⟨fun p' => ⟨(x.1.1 ((p'.1.val : ZMod q), p'.2)).val, by
              have hle : (x.1.1 ((p'.1.val : ZMod q), p'.2)).val ≤ N' := by
                rw [← hsum']
                exact Finset.single_le_sum (f := fun p' : ZMod q' × Fin m => (x.1.1 ((p'.1.val : ZMod q), p'.2)).val)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ p')
              omega⟩, hsum'⟩,
           fun p' => x.2 ((p'.1.val : ZMod q), p'.2)⟩
        invFun := fun y =>
          ⟨⟨⟨fun p => ⟨(y.1.1 (proj p.1, p.2)).val, by
              have hle : (y.1.1 (proj p.1, p.2)).val ≤ N' := by
                have := (y.1.1 (proj p.1, p.2)).isLt; omega
              have hN'N : N' ≤ N := by rw [hNN']; exact Nat.le_mul_of_pos_left N' hp.pos
              omega⟩, by
            rw [Fintype.sum_prod_type]
            have h1 := hproj_sum (fun z' => ∑ j : Fin m, (y.1.1 (z', j)).val)
            have hy := y.1.2
            rw [Fintype.sum_prod_type] at hy
            rw [h1, hy, ← hNN']⟩,
           fun p => y.2 (proj p.1, p.2)⟩, by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            refine Sigma.ext (Subtype.ext (funext fun ⟨z, j⟩ => by
              simp only [act, map_add, hproj_g₀, add_zero])) ?_
            refine Function.hfunext rfl fun ⟨z, j⟩ ⟨z', j'⟩ hzz => ?_
            cases hzz
            dsimp only [act]; rw [map_add, hproj_g₀, add_zero]⟩
        left_inv := fun ⟨x, hx⟩ => by
          have hfix : act g₀ x = x := (Finset.mem_filter.mp hx).2
          have hiter : ∀ (t : ℕ), act ((t : ZMod q) * g₀) x = x := by
            intro t; induction t with
            | zero => simpa using hact_zero x
            | succ t iht =>
                rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hact_add, hfix, iht]
          have hproj_val : ∀ z : ZMod q, z = ((proj z).val : ZMod q) + ((z.val / q' : ℕ) : ZMod q) * g₀ := by
            intro z
            have hval_proj : (proj z).val = z.val % q' := by
              have h1 : proj z = ((z.val : ℕ) : ZMod q') := by
                rw [← ZMod.natCast_zmod_val z]; simp [proj]
              rw [h1, ZMod.val_natCast]
            rw [hval_proj]
            simp only [g₀, ← Nat.cast_mul, ← Nat.cast_add]
            rw [add_comm, mul_comm, Nat.div_add_mod, ZMod.natCast_zmod_val]
          apply Subtype.ext
          refine Sigma.ext (Subtype.ext (funext fun ⟨z, j⟩ => ?_)) ?_
          · apply Fin.ext
            dsimp only
            have hx_eq := congrArg (fun y : X => (y.1.1 (((proj z).val : ZMod q), j)).val) (hiter (z.val / q'))
            dsimp only [act] at hx_eq
            rw [← hproj_val z] at hx_eq
            exact hx_eq.symm
          · refine Function.hfunext rfl fun ⟨z, j⟩ ⟨z', j'⟩ hzz => ?_
            cases hzz
            have hx_eq := hiter (z.val / q')
            have h1 : (act (((z.val / q' : ℕ) : ZMod q) * g₀) x).2 (((proj z).val : ZMod q), j) ≍
                x.2 (((proj z).val : ZMod q), j) := by
              rw [hx_eq]
            dsimp only [act] at h1
            rw [← hproj_val z] at h1
            exact h1.symm
        right_inv := fun ⟨⟨d, hd⟩, w⟩ => by
          have hproj_id : ∀ z' : ZMod q', proj ((z'.val : ZMod q)) = z' := fun z' => by
            simp [proj]
          refine Sigma.ext (Subtype.ext (funext fun ⟨z', j⟩ => ?_)) ?_
          · apply Fin.ext; dsimp only; rw [hproj_id]
          · refine Function.hfunext rfl fun ⟨z', j⟩ ⟨z'', j'⟩ hzz => ?_
            cases hzz
            dsimp only
            rw [hproj_id] }
  have hdvd_nat := zmod_prime_pow_card_sub_fix_dvd hp hr act hact_zero hact_add
  have hle : (Finset.univ.filter fun x : X => act g₀ x = x).card ≤ Fintype.card X :=
    Finset.card_le_univ _
  rw [hcardX, hfix_card, hcardX'] at hdvd_nat hle
  have hdvd_int : ((p ^ r : ℕ) : ℤ) ∣ (((PowerSeries.coeff N (F ^ N) - PowerSeries.coeff N' (F ^ N') : ℕ) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd_nat
  rwa [Nat.cast_sub hle] at hdvd_int

theorem main_proof :
    ∀ (p n k : ℕ), p.Prime → 1 ≤ n → 1 ≤ k →
      ((p ^ k : ℕ) : ℤ) ∣ ((a270924 (n * p ^ k) : ℤ) - (a270924 (n * p ^ (k - 1)) : ℤ)) := by
  intro p n k hp hn hk
  exact coeff_pow_gauss_cong prodSeries hp hk hn

end OMA.S_oeis_a270924

theorem OMA.solution : type_of% @OMA.S_oeis_a270924.main :=
  OMA.S_oeis_a270924.main_proof
