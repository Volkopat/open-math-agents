import OMAStatements.S_oeis_a032312
import Mathlib

/-
  Proof of OEIS A032312 (Bala Gauss congruences for the EGJ transform of 2, 2, 2, ...).
  We interpret a(n) combinatorially as the number of 2-colored set partitions of Fin n
  into blocks of pairwise distinct sizes, then decompose under the cyclic ZMod (p ^ k) action
  on Fin n * ZMod (p ^ k): elements not fixed by the order-p element p^(k-1) have trivial
  stabilizer and hence orbits of size p ^ k, while fixed points biject with configurations
  on Fin n * ZMod (p ^ (k - 1)).
-/

namespace OeisA032312Proof

private structure Config (T : Type*) [Fintype T] [DecidableEq T] where
  assign : T → Fin (Fintype.card T + 1)
  color : Fin (Fintype.card T + 1) → Bool
  hblock : ∀ m : Fin (Fintype.card T + 1),
    ((Finset.univ.filter (fun t => assign t = m)).card = 0 ∧ color m = false) ∨
      (0 < m.1 ∧ (Finset.univ.filter (fun t => assign t = m)).card = m.1)

private lemma Config.ext {T : Type*} [Fintype T] [DecidableEq T] {c₁ c₂ : Config T}
    (ha : c₁.assign = c₂.assign) (hc : c₁.color = c₂.color) : c₁ = c₂ := by
  cases c₁
  cases c₂
  simp only [Config.mk.injEq]
  exact ⟨ha, hc⟩

private instance {T : Type*} [Fintype T] [DecidableEq T] : DecidableEq (Config T) :=
  fun a b => decidable_of_iff (a.assign = b.assign ∧ a.color = b.color)
    ⟨fun h => Config.ext h.1 h.2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

private instance {T : Type*} [Fintype T] [DecidableEq T] : Fintype (Config T) :=
  Fintype.ofEquiv
    { p : (T → Fin (Fintype.card T + 1)) × (Fin (Fintype.card T + 1) → Bool) //
        ∀ m : Fin (Fintype.card T + 1),
          ((Finset.univ.filter (fun t => p.1 t = m)).card = 0 ∧ p.2 m = false) ∨
            (0 < m.1 ∧ (Finset.univ.filter (fun t => p.1 t = m)).card = m.1) }
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun c => ⟨(c.assign, c.color), c.hblock⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma card_config_congr {T₁ T₂ : Type*} [Fintype T₁] [DecidableEq T₁]
    [Fintype T₂] [DecidableEq T₂] (e : T₁ ≃ T₂) :
    Fintype.card (Config T₁) = Fintype.card (Config T₂) := by
  have hcard : Fintype.card T₁ = Fintype.card T₂ := Fintype.card_congr e
  refine Fintype.card_congr ?_
  refine
    { toFun := fun c =>
        { assign := fun t₂ => ⟨(c.assign (e.symm t₂)).1, by omega⟩
          color := fun m => c.color ⟨m.1, by omega⟩
          hblock := ?_ }
      invFun := fun c =>
        { assign := fun t₁ => ⟨(c.assign (e t₁)).1, by omega⟩
          color := fun m => c.color ⟨m.1, by omega⟩
          hblock := ?_ }
      left_inv := fun c => by
        apply Config.ext
        · ext t₁; simp
        · ext m; simp
      right_inv := fun c => by
        apply Config.ext
        · ext t₂; simp
        · ext m; simp }
  · intro m
    have hb := c.hblock ⟨m.1, by omega⟩
    have hfilt :
        Finset.univ.filter (fun t₂ : T₂ => (⟨(c.assign (e.symm t₂)).1, by omega⟩ : Fin (Fintype.card T₂ + 1)) = m) =
          (Finset.univ.filter (fun t₁ : T₁ => c.assign t₁ = ⟨m.1, by omega⟩)).map e.toEmbedding := by
      ext t₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · intro h
        exact ⟨e.symm t₂, Fin.ext (by simpa using congrArg Fin.val h), by simp⟩
      · rintro ⟨t₁, h1, rfl⟩
        exact Fin.ext (by simpa using congrArg Fin.val h1)
    rw [hfilt, Finset.card_map]
    exact hb
  · intro m
    have hb := c.hblock ⟨m.1, by omega⟩
    have hfilt :
        Finset.univ.filter (fun t₁ : T₁ => (⟨(c.assign (e t₁)).1, by omega⟩ : Fin (Fintype.card T₁ + 1)) = m) =
          (Finset.univ.filter (fun t₂ : T₂ => c.assign t₂ = ⟨m.1, by omega⟩)).map e.symm.toEmbedding := by
      ext t₁
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · intro h
        exact ⟨e t₁, Fin.ext (by simpa using congrArg Fin.val h), by simp⟩
      · rintro ⟨t₂, h1, rfl⟩
        exact Fin.ext (by simpa using congrArg Fin.val h1)
    rw [hfilt, Finset.card_map]
    exact hb

private def FiberAssign (T : Type*) [Fintype T] [DecidableEq T] (S : Finset ℕ) : Type _ :=
  { f : T → ℕ // (∀ t, f t ∈ S) ∧ ∀ m ∈ S, (Finset.univ.filter (fun t => f t = m)).card = m }

private lemma FiberAssign.ext {T : Type*} [Fintype T] [DecidableEq T] {S : Finset ℕ}
    {f₁ f₂ : FiberAssign T S} (h : f₁.1 = f₂.1) : f₁ = f₂ := Subtype.ext h

private instance {T : Type*} [Fintype T] [DecidableEq T] (S : Finset ℕ) :
    Fintype (FiberAssign T S) :=
  Fintype.ofEquiv
    { f : T → S // ∀ m : S, (Finset.univ.filter (fun t => f t = m)).card = m.1 }
    { toFun := fun f =>
        ⟨fun t => (f.1 t).1, fun t => (f.1 t).2, fun m hm => by
          have h := f.2 ⟨m, hm⟩
          convert h using 2
          ext t
          simp [Subtype.ext_iff]⟩
      invFun := fun f =>
        ⟨fun t => ⟨f.1 t, f.2.1 t⟩, fun m => by
          have h := f.2.2 m.1 m.2
          convert h using 2
          ext t
          simp [Subtype.ext_iff]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma card_fiber_assign :
    ∀ (S : Finset ℕ) (T : Type*) [Fintype T] [DecidableEq T],
      (∀ m ∈ S, 1 ≤ m) → S.sum id = Fintype.card T →
      Fintype.card (FiberAssign T S) * (∏ m ∈ S, m.factorial) = (Fintype.card T).factorial := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T _ _ _ hsum
    simp only [Finset.sum_empty] at hsum
    have hempty : IsEmpty T := Fintype.card_eq_zero_iff.mp hsum.symm
    have huniq : Fintype.card (FiberAssign T ∅) = 1 := by
      refine Fintype.card_eq_one_iff.mpr ?_
      refine ⟨⟨fun t => (hempty.false t).elim, fun t => (hempty.false t).elim, fun _ hm => (Finset.notMem_empty _ hm).elim⟩, ?_⟩
      intro f
      apply FiberAssign.ext
      ext t
      exact (hempty.false t).elim
    rw [huniq, ← hsum, Finset.prod_empty, mul_one, Nat.factorial_zero]
  | @insert a S ha ih =>
    intro T _ _ hpos hsum
    rw [Finset.sum_insert ha, id_eq] at hsum
    have ha_le : a ≤ Fintype.card T := by omega
    have hsumS : S.sum id = Fintype.card T - a := by
      change ∑ x ∈ S, id x = Fintype.card T - a
      omega
    let slice : FiberAssign T (insert a S) → Finset.powersetCard a (Finset.univ : Finset T) :=
      fun f => ⟨Finset.univ.filter (fun t => f.1 t = a),
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, f.2.2 a (Finset.mem_insert_self a S)⟩⟩
    have hfib_eq :
        Fintype.card (FiberAssign T (insert a S)) =
          ∑ A : Finset.powersetCard a (Finset.univ : Finset T),
            Fintype.card { f : FiberAssign T (insert a S) // slice f = A } := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv slice).symm
    have hfib_card :
        ∀ A : Finset.powersetCard a (Finset.univ : Finset T),
          Fintype.card { f : FiberAssign T (insert a S) // slice f = A } * (∏ m ∈ S, m.factorial) =
            (Fintype.card T - a).factorial := by
      intro A
      have hcard_compl : Fintype.card { t : T // t ∉ A.1 } = Fintype.card T - a := by
        have hA : A.1.card = a := (Finset.mem_powersetCard.mp A.2).2
        rw [Fintype.card_subtype_compl, Fintype.card_coe, hA]
      have heq_sub :
          Fintype.card { f : FiberAssign T (insert a S) // slice f = A } =
            Fintype.card (FiberAssign { t : T // t ∉ A.1 } S) := by
        refine Fintype.card_congr ?_
        refine
          { toFun := fun f =>
              ⟨fun t => f.1.1 t.1,
                fun t => by
                  have hm := f.1.2.1 t.1
                  rcases Finset.mem_insert.mp hm with heq | hmem
                  · exfalso
                    have hsub : Finset.univ.filter (fun x : T => f.1.1 x = a) = A.1 := congrArg Subtype.val f.2
                    have htmem : t.1 ∈ Finset.univ.filter (fun x : T => f.1.1 x = a) :=
                      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
                    rw [hsub] at htmem
                    exact t.2 htmem

                  · exact hmem,
                fun m hm => by
                  have hne : m ≠ a := fun h => ha (h ▸ hm)
                  have horig := f.1.2.2 m (Finset.mem_insert_of_mem hm)
                  calc
                    (Finset.univ.filter (fun t : { t : T // t ∉ A.1 } => f.1.1 t.1 = m)).card
                        = (Finset.univ.filter (fun t : T => f.1.1 t = m)).card := by
                            refine Finset.card_bij (fun t _ => t.1) ?_ ?_ ?_
                            · intro t ht
                              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
                              exact ht
                            · intro t₁ _ t₂ _ h; exact Subtype.ext h
                            · intro t ht
                              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
                              have hnot : t ∉ A.1 := by
                                intro htA
                                have hsub : Finset.univ.filter (fun x : T => f.1.1 x = a) = A.1 := congrArg Subtype.val f.2
                                rw [← hsub] at htA
                                have hfa : f.1.1 t = a := (Finset.mem_filter.mp htA).2
                                exact hne (ht.symm.trans hfa)
                              exact ⟨⟨t, hnot⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
                    _ = m := horig⟩
            invFun := fun g =>
              ⟨⟨fun t => if ht : t ∈ A.1 then a else g.1 ⟨t, ht⟩,
                fun t => by
                  by_cases ht : t ∈ A.1
                  · simp [ht]
                  · simp [ht, Finset.mem_insert_of_mem (g.2.1 ⟨t, ht⟩)],
                fun m hm => by
                  rcases Finset.mem_insert.mp hm with rfl | hmS
                  · calc
                      (Finset.univ.filter (fun t : T => (if ht : t ∈ A.1 then m else g.1 ⟨t, ht⟩) = m)).card
                          = A.1.card := by
                              congr 1
                              ext t
                              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                              constructor
                              · intro h
                                by_contra hnt
                                simp only [dif_neg hnt] at h
                                exact ha (h ▸ g.2.1 ⟨t, hnt⟩)
                              · intro ht
                                simp [dif_pos ht]
                      _ = m := (Finset.mem_powersetCard.mp A.2).2
                  · have hne : m ≠ a := fun h => ha (h ▸ hmS)
                    calc
                      (Finset.univ.filter (fun t : T => (if ht : t ∈ A.1 then a else g.1 ⟨t, ht⟩) = m)).card
                          = (Finset.univ.filter (fun t : { t : T // t ∉ A.1 } => g.1 t = m)).card := by
                              refine Finset.card_bij (fun t ht => ⟨t, by
                                intro htA
                                simp only [Finset.mem_filter, Finset.mem_univ, true_and, dif_pos htA] at ht
                                exact hne ht.symm⟩) ?_ ?_ ?_
                              · intro t ht
                                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
                                by_cases htA : t ∈ A.1
                                · simp [htA] at ht; exact (hne ht.symm).elim
                                · simpa [dif_neg htA] using ht
                              · intro t₁ _ t₂ _ h; exact congrArg Subtype.val h
                              · intro t ht
                                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
                                refine ⟨t.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
                                simp [dif_neg t.2, ht]
                      _ = m := g.2.2 m hmS⟩,
                by
                  ext t
                  simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro h
                    by_contra hnt
                    simp only [dif_neg hnt] at h
                    exact ha (h ▸ g.2.1 ⟨t, hnt⟩)
                  · intro ht
                    simp [dif_pos ht]⟩
            left_inv := fun f => by
              apply Subtype.ext
              apply FiberAssign.ext
              ext t
              dsimp only
              split_ifs with ht
              · have hsub : Finset.univ.filter (fun x : T => f.1.1 x = a) = A.1 := congrArg Subtype.val f.2
                rw [← hsub] at ht
                exact (Finset.mem_filter.mp ht).2.symm
              · rfl
            right_inv := fun g => by
              apply FiberAssign.ext
              ext t
              dsimp only
              rw [dif_neg t.2] }
      rw [heq_sub, ih { t : T // t ∉ A.1 } (fun m hm => hpos m (Finset.mem_insert_of_mem hm)) (by rw [hcard_compl]; exact hsumS),
        hcard_compl]
    have hsum_fib :
        (∑ A : Finset.powersetCard a (Finset.univ : Finset T),
          Fintype.card { f : FiberAssign T (insert a S) // slice f = A }) * (∏ m ∈ S, m.factorial) =
          (Fintype.card T).choose a * (Fintype.card T - a).factorial := by
      rw [Finset.sum_mul]
      simp_rw [hfib_card]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]
    rw [Finset.prod_insert ha, hfib_eq]
    calc
      (∑ A : Finset.powersetCard a (Finset.univ : Finset T),
          Fintype.card { f : FiberAssign T (insert a S) // slice f = A }) * (a.factorial * ∏ m ∈ S, m.factorial)
          = ((∑ A : Finset.powersetCard a (Finset.univ : Finset T),
              Fintype.card { f : FiberAssign T (insert a S) // slice f = A }) * (∏ m ∈ S, m.factorial)) * a.factorial := by ring
      _ = ((Fintype.card T).choose a * (Fintype.card T - a).factorial) * a.factorial := by rw [hsum_fib]
      _ = (Fintype.card T).choose a * a.factorial * (Fintype.card T - a).factorial := by ring
      _ = (Fintype.card T).factorial := Nat.choose_mul_factorial_mul_factorial ha_le

private lemma a_eq_card_config (N : ℕ) :
    OMA.S_oeis_a032312.a N = (Fintype.card (Config (Fin N)) : ℚ) := by
  unfold OMA.S_oeis_a032312.a
  have hprod_reindex :
      ∏ k ∈ Finset.range N, (1 + Polynomial.C (2 / ((k + 1).factorial : ℚ)) * Polynomial.X ^ (k + 1)) =
        ∏ m ∈ Finset.Icc 1 N, (1 + Polynomial.C (2 / (m.factorial : ℚ)) * Polynomial.X ^ m) := by
    refine Finset.prod_bij (fun k _ => k + 1) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro k hk
      have hklt : k < N := Finset.mem_range.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm1, hmN⟩
      exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
  rw [hprod_reindex, Finset.prod_one_add, Polynomial.finsetSum_coeff]
  let FS : Finset (Finset ℕ) := (Finset.Icc 1 N).powerset.filter (fun S => S.sum id = N)
  have hpoly :
      ∑ S ∈ (Finset.Icc 1 N).powerset,
          (∏ m ∈ S, (Polynomial.C (2 / (m.factorial : ℚ)) * Polynomial.X ^ m)).coeff N =
        ∑ S ∈ FS, ((2 : ℚ) ^ S.card / ∏ m ∈ S, (m.factorial : ℚ)) := by
    have hterm :
        ∀ S ∈ (Finset.Icc 1 N).powerset,
          (∏ m ∈ S, (Polynomial.C (2 / (m.factorial : ℚ)) * Polynomial.X ^ m)).coeff N =
            if S.sum id = N then (2 : ℚ) ^ S.card / ∏ m ∈ S, (m.factorial : ℚ) else 0 := by
      intro S _
      rw [Finset.prod_mul_distrib, ← map_prod Polynomial.C, Finset.prod_pow_eq_pow_sum,
        Polynomial.coeff_C_mul_X_pow]
      have hif : (N = ∑ i ∈ S, i) ↔ (S.sum id = N) := by simp [eq_comm]
      simp only [hif]
      split_ifs with hsum
      · rw [Finset.prod_div_distrib, Finset.prod_const]
      · rfl
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  rw [hpoly, Finset.mul_sum]
  have hNcard : Fintype.card (Fin N) = N := Fintype.card_fin N
  let supp : Config (Fin N) → FS := fun c =>
    let S : Finset ℕ :=
      (Finset.Icc 1 N).filter (fun m => ∃ h : m < Fintype.card (Fin N) + 1,
        0 < (Finset.univ.filter (fun t : Fin N => c.assign t = ⟨m, h⟩)).card)
    have hS_sub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
    have hS_mem : ∀ t : Fin N, (c.assign t).1 ∈ S := by
      intro t
      have ht_pos : 0 < (Finset.univ.filter (fun u : Fin N => c.assign u = c.assign t)).card :=
        Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      have hbt := c.hblock (c.assign t)
      have hm_pos : 0 < (c.assign t).1 := by
        rcases hbt with ⟨h0, _⟩ | ⟨hm, _⟩
        · omega
        · exact hm
      have hm_card : (Finset.univ.filter (fun u : Fin N => c.assign u = c.assign t)).card = (c.assign t).1 := by
        rcases hbt with ⟨h0, _⟩ | ⟨_, hc⟩
        · omega
        · exact hc
      have hm_le : (c.assign t).1 ≤ N := by
        calc
          (c.assign t).1 = (Finset.univ.filter (fun u : Fin N => c.assign u = c.assign t)).card := hm_card.symm
          _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_filter_le _ _
          _ = N := hNcard
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, ⟨(c.assign t).2, ?_⟩⟩
      simpa using ht_pos
    have hS_sum : S.sum id = N := by
      have hcardN : (Finset.univ : Finset (Fin N)).card =
          ∑ m ∈ S, (Finset.univ.filter (fun t : Fin N => (c.assign t).1 = m)).card := by
        simpa using Finset.card_eq_sum_card_fiberwise (f := fun t : Fin N => (c.assign t).1)
          (s := (Finset.univ : Finset (Fin N))) (t := S) (fun t _ => hS_mem t)
      conv_lhs at hcardN => rw [Finset.card_univ, hNcard]
      rw [hcardN]
      refine Finset.sum_congr rfl fun m hm => ?_
      rcases (Finset.mem_filter.mp hm).2 with ⟨hlt, hpos⟩
      have hbt := c.hblock ⟨m, hlt⟩
      have hcard_eq : (Finset.univ.filter (fun t : Fin N => c.assign t = ⟨m, hlt⟩)).card = m := by
        rcases hbt with ⟨h0, _⟩ | ⟨_, hc⟩
        · omega
        · exact hc
      calc
        id m = (Finset.univ.filter (fun t : Fin N => c.assign t = ⟨m, hlt⟩)).card := hcard_eq.symm
        _ = (Finset.univ.filter (fun t : Fin N => (c.assign t).1 = m)).card := by
              congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS_sub, hS_sum⟩⟩
  have hcfg_eq :
      Fintype.card (Config (Fin N)) = ∑ S : FS, Fintype.card { c : Config (Fin N) // supp c = S } := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv supp).symm
  have hfib_eq :
      ∀ S : FS,
        Fintype.card { c : Config (Fin N) // supp c = S } =
          Fintype.card (FiberAssign (Fin N) S.1) * 2 ^ S.1.card := by
    intro S
    have hS_icc : S.1 ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
    have hS_pos : ∀ m ∈ S.1, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp (hS_icc hm)).1
    have hS_lt : ∀ m ∈ S.1, m < Fintype.card (Fin N) + 1 := fun m hm => by
      have := (Finset.mem_Icc.mp (hS_icc hm)).2
      omega
    have heqv :
        { c : Config (Fin N) // supp c = S } ≃ FiberAssign (Fin N) S.1 × (S.1 → Bool) :=
      { toFun := fun c =>
          (⟨fun t => (c.1.assign t).1,
            fun t => by
              have hmem : (c.1.assign t).1 ∈ (supp c.1).1 := by
                have ht_pos : 0 < (Finset.univ.filter (fun u : Fin N => c.1.assign u = c.1.assign t)).card :=
                  Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
                have hbt := c.1.hblock (c.1.assign t)
                have hm_pos : 0 < (c.1.assign t).1 := by
                  rcases hbt with ⟨h0, _⟩ | ⟨hm, _⟩
                  · omega
                  · exact hm
                have hm_card : (Finset.univ.filter (fun u : Fin N => c.1.assign u = c.1.assign t)).card = (c.1.assign t).1 := by
                  rcases hbt with ⟨h0, _⟩ | ⟨_, hc⟩
                  · omega
                  · exact hc
                have hm_le : (c.1.assign t).1 ≤ N := by
                  calc
                    (c.1.assign t).1 = (Finset.univ.filter (fun u : Fin N => c.1.assign u = c.1.assign t)).card := hm_card.symm
                    _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_filter_le _ _
                    _ = N := hNcard
                refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, ⟨(c.1.assign t).2, ?_⟩⟩
                simpa using ht_pos
              rw [c.2] at hmem
              exact hmem,
            fun m hm => by
              have hm' : m ∈ (supp c.1).1 := by rw [c.2]; exact hm
              rcases (Finset.mem_filter.mp hm').2 with ⟨hlt, hpos⟩
              have hbt := c.1.hblock ⟨m, hlt⟩
              have hce : (Finset.univ.filter (fun t : Fin N => c.1.assign t = ⟨m, hlt⟩)).card = m := by
                rcases hbt with ⟨h0, _⟩ | ⟨_, hc⟩
                · omega
                · exact hc
              calc
                (Finset.univ.filter (fun t : Fin N => (c.1.assign t).1 = m)).card
                    = (Finset.univ.filter (fun t : Fin N => c.1.assign t = ⟨m, hlt⟩)).card := by
                        congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
                _ = m := hce⟩,
           fun m => c.1.color ⟨m.1, hS_lt m.1 m.2⟩)
        invFun := fun ⟨f, col⟩ =>
          ⟨{ assign := fun t => ⟨f.1 t, hS_lt (f.1 t) (f.2.1 t)⟩
             color := fun m => if hm : m.1 ∈ S.1 then col ⟨m.1, hm⟩ else false
             hblock := fun m => by
               by_cases hm : m.1 ∈ S.1
               · right
                 refine ⟨hS_pos m.1 hm, ?_⟩
                 calc
                   (Finset.univ.filter (fun t : Fin N => (⟨f.1 t, hS_lt (f.1 t) (f.2.1 t)⟩ : Fin (Fintype.card (Fin N) + 1)) = m)).card
                       = (Finset.univ.filter (fun t : Fin N => f.1 t = m.1)).card := by
                           congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
                   _ = m.1 := f.2.2 m.1 hm
               · left
                 refine ⟨?_, by simp [hm]⟩
                 rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                 intro t _ ht
                 have heq : f.1 t = m.1 := congrArg Fin.val ht
                 exact hm (heq ▸ f.2.1 t) },
           by
             apply Subtype.ext
             ext m
             simp only [supp, Finset.mem_filter]
             constructor
             · rintro ⟨_, hlt, hpos⟩
               rcases Finset.card_pos.mp hpos with ⟨t, ht⟩
               have hfeq : f.1 t = m := congrArg Fin.val (Finset.mem_filter.mp ht).2
               exact hfeq ▸ f.2.1 t
             · intro hm
               refine ⟨hS_icc hm, hS_lt m hm, ?_⟩
               have hpos : 0 < m := hS_pos m hm
               calc
                 0 < m := hpos
                 _ = (Finset.univ.filter (fun t : Fin N => f.1 t = m)).card := (f.2.2 m hm).symm
                 _ = (Finset.univ.filter (fun t : Fin N => (⟨f.1 t, hS_lt (f.1 t) (f.2.1 t)⟩ : Fin (Fintype.card (Fin N) + 1)) = ⟨m, hS_lt m hm⟩)).card := by
                       congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]⟩
        left_inv := fun c => by
          apply Subtype.ext
          apply Config.ext
          · rfl
          · ext m
            dsimp only
            split_ifs with hm
            · rfl
            · rcases c.1.hblock m with ⟨_, hcol⟩ | ⟨hpos, hcard⟩
              · exact hcol.symm
              · exfalso
                have hsupp : m.1 ∈ (supp c.1).1 := by
                  have hle : m.1 ≤ N := by
                    calc
                      m.1 = (Finset.univ.filter (fun u : Fin N => c.1.assign u = m)).card := hcard.symm
                      _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_filter_le _ _
                      _ = N := hNcard
                  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩, ⟨m.2, ?_⟩⟩
                  simpa [hcard] using hpos
                rw [c.2] at hsupp
                exact hm hsupp
        right_inv := fun ⟨f, col⟩ => by
          apply Prod.ext
          · apply FiberAssign.ext
            rfl
          · ext m
            dsimp only
            rw [dif_pos m.2] }
    rw [Fintype.card_congr heqv, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rw [hcfg_eq, Nat.cast_sum, ← Finset.sum_attach FS]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hfib := hfib_eq S
  rw [hfib, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hS_icc : S.1 ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
  have hS_sum : S.1.sum id = N := (Finset.mem_filter.mp S.2).2
  have hS_pos : ∀ m ∈ S.1, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp (hS_icc hm)).1
  have hnat := card_fiber_assign S.1 (Fin N) hS_pos (by simpa [hNcard] using hS_sum)
  rw [hNcard] at hnat
  have hq : (Fintype.card (FiberAssign (Fin N) S.1) : ℚ) * (∏ m ∈ S.1, (m.factorial : ℚ)) = (N.factorial : ℚ) := by
    exact_mod_cast hnat
  have hne : (∏ m ∈ S.1, (m.factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun m _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hq' := (eq_div_iff hne).mpr hq
  rw [hq']
  ring

private instance {n M : ℕ} [NeZero M] : SMul (Multiplicative (ZMod M)) (Config (Fin n × ZMod M)) where
  smul h c :=
    { assign := fun t => c.assign (t.1, t.2 - Multiplicative.toAdd h)
      color := c.color
      hblock := fun m => by
        have hb := c.hblock m
        let fEmb : (Fin n × ZMod M) ↪ (Fin n × ZMod M) :=
          ⟨fun t => (t.1, t.2 + Multiplicative.toAdd h), fun a b hab => by
            simp only [Prod.ext_iff] at hab
            exact Prod.ext hab.1 (add_right_cancel hab.2)⟩
        have hfilt :
            Finset.univ.filter (fun t : Fin n × ZMod M => c.assign (t.1, t.2 - Multiplicative.toAdd h) = m) =
              (Finset.univ.filter (fun t : Fin n × ZMod M => c.assign t = m)).map fEmb := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
          constructor
          · intro ht
            exact ⟨(t.1, t.2 - Multiplicative.toAdd h), ht, Prod.ext rfl (sub_add_cancel _ _)⟩
          · rintro ⟨u, hu, rfl⟩
            change c.assign (u.1, (u.2 + Multiplicative.toAdd h) - Multiplicative.toAdd h) = m
            simpa [add_sub_cancel_right] using hu
        rw [hfilt, Finset.card_map]
        exact hb }

private instance {n M : ℕ} [NeZero M] : MulAction (Multiplicative (ZMod M)) (Config (Fin n × ZMod M)) where
  one_smul c := by
    apply Config.ext
    · funext t
      show c.assign (t.1, t.2 - Multiplicative.toAdd (1 : Multiplicative (ZMod M))) = c.assign t
      simp
    · rfl
  mul_smul h₁ h₂ c := by
    apply Config.ext
    · funext t
      show c.assign (t.1, t.2 - Multiplicative.toAdd (h₁ * h₂)) =
        c.assign (t.1, (t.2 - Multiplicative.toAdd h₁) - Multiplicative.toAdd h₂)
      simp [sub_sub]
    · rfl

private lemma dvd_nonfixed_card {p n k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) [NeZero (p ^ k)] :
    p ^ k ∣ (Finset.univ.filter (fun c : Config (Fin n × ZMod (p ^ k)) =>
      Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k)) • c ≠ c)).card := by
  classical
  let tau : Multiplicative (ZMod (p ^ k)) := Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k))
  let U := Finset.univ.filter (fun c : Config (Fin n × ZMod (p ^ k)) => tau • c ≠ c)
  letI : SMul (Multiplicative (ZMod (p ^ k))) ↥U :=
    ⟨fun h c => ⟨h • c.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      intro heq
      have hcomm : tau * h = h * tau := mul_comm tau h
      have heq2 : h • (tau • c.1) = h • c.1 := by
        calc
          h • (tau • c.1) = (h * tau) • c.1 := (mul_smul h tau c.1).symm
          _ = (tau * h) • c.1 := by rw [hcomm]
          _ = tau • (h • c.1) := mul_smul tau h c.1
          _ = h • c.1 := heq
      have heq3 : tau • c.1 = c.1 := by
        have := congrArg (fun x : Config (Fin n × ZMod (p ^ k)) => h⁻¹ • x) heq2
        simpa [← mul_smul] using this
      exact (Finset.mem_filter.mp c.2).2 heq3⟩⟩⟩
  have hmulU : ∀ (h₁ h₂ : Multiplicative (ZMod (p ^ k))) (c : ↥U),
      (h₁ * h₂) • c = h₁ • (h₂ • c) := fun h₁ h₂ c => Subtype.ext (mul_smul h₁ h₂ c.1)
  letI : MulAction (Multiplicative (ZMod (p ^ k))) ↥U :=
    { one_smul := fun c => Subtype.ext (one_smul (Multiplicative (ZMod (p ^ k))) c.1)
      mul_smul := hmulU }
  have hstab_bot : ∀ c : ↥U, MulAction.stabilizer (Multiplicative (ZMod (p ^ k))) c = ⊥ := by
    intro c
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    by_contra hne
    let g : ZMod (p ^ k) := Multiplicative.toAdd h
    have hgne : g ≠ 0 := fun hz => hne (by simpa [g] using hz)
    have hgpos : 0 < g.val := by
      rcases Nat.eq_zero_or_pos g.val with h0 | hpos
      · exfalso; exact hgne ((ZMod.val_eq_zero g).mp h0)
      · exact hpos
    have hglt : g.val < p ^ k := ZMod.val_lt g
    have hndvdM : ¬ p ^ k ∣ g.val := Nat.not_dvd_of_pos_of_lt hgpos hglt
    let j := g.val.factorization p
    have hpj_dvd : p ^ j ∣ g.val := by
      rw [← Nat.factorization_le_iff_dvd (pow_ne_zero j hp.ne_zero) hgpos.ne']
      intro q
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization]
      by_cases hq : q = p
      · subst hq; simp [j]
      · simp [hq]
    have hjk : j < k := by
      by_contra hge
      exact hndvdM (dvd_trans (pow_dvd_pow p (Nat.le_of_not_lt hge)) hpj_dvd)
    rcases hpj_dvd with ⟨u, hu⟩
    have hndvd_u : ¬ p ∣ u := by
      intro hd
      have hpj1 : p ^ (j + 1) ∣ g.val := by
        rcases hd with ⟨w, rfl⟩
        exact ⟨w, by rw [hu, pow_succ]; ring⟩
      have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero (j + 1) hp.ne_zero) hgpos.ne').mpr hpj1 p
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization, Finsupp.single_eq_same, mul_one] at hle
      omega
    have hcop : Nat.Coprime u (p ^ k) := (hp.coprime_iff_not_dvd.mpr hndvd_u).symm.pow_right k
    let uu := ZMod.unitOfCoprime u hcop
    let mZ : ZMod (p ^ k) := ↑(uu⁻¹) * (p ^ (k - 1 - j) : ZMod (p ^ k))
    let m := mZ.val
    have hm_mul : (m : ZMod (p ^ k)) * g = (p ^ (k - 1) : ZMod (p ^ k)) := by
      have hmcast : (m : ZMod (p ^ k)) = mZ := ZMod.natCast_zmod_val mZ
      have hgcast : g = (g.val : ZMod (p ^ k)) := (ZMod.natCast_zmod_val g).symm
      have huucast : (uu : ZMod (p ^ k)) = (u : ZMod (p ^ k)) := ZMod.coe_unitOfCoprime u hcop
      rw [hmcast, hgcast, hu]
      push_cast
      have hsplit : (↑(uu⁻¹) : ZMod (p ^ k)) * ↑uu = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc
        (↑(uu⁻¹) * (p : ZMod (p ^ k)) ^ (k - 1 - j)) * ((p : ZMod (p ^ k)) ^ j * (u : ZMod (p ^ k)))
            = (↑(uu⁻¹) * ↑uu) * ((p : ZMod (p ^ k)) ^ (k - 1 - j) * (p : ZMod (p ^ k)) ^ j) := by
                rw [huucast]; ring
        _ = (1 : ZMod (p ^ k)) * (p : ZMod (p ^ k)) ^ ((k - 1 - j) + j) := by
                rw [hsplit, pow_add]
        _ = (p : ZMod (p ^ k)) ^ (k - 1) := by
                rw [one_mul, Nat.sub_add_cancel (by omega)]
    have hpow_tau : h ^ m = tau := by
      apply Multiplicative.toAdd.injective
      change m • g = (p ^ (k - 1) : ZMod (p ^ k))
      rw [nsmul_eq_mul, hm_mul]
    have hpow_mem : h ^ m ∈ MulAction.stabilizer (Multiplicative (ZMod (p ^ k))) c := Subgroup.pow_mem _ hh m
    rw [hpow_tau, MulAction.mem_stabilizer_iff] at hpow_mem
    have htau_eq : tau • c.1 = c.1 := congrArg Subtype.val hpow_mem
    exact (Finset.mem_filter.mp c.2).2 htau_eq
  have horbit_card : ∀ c : ↥U, Fintype.card (MulAction.orbit (Multiplicative (ZMod (p ^ k))) c) = p ^ k := by
    intro c
    have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Multiplicative (ZMod (p ^ k))) c
    have hcard_stab : Fintype.card ↥(MulAction.stabilizer (Multiplicative (ZMod (p ^ k))) c) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨1, fun x => Subtype.ext ?_⟩
      change (x : Multiplicative (ZMod (p ^ k))) = 1
      rw [← Subgroup.mem_bot, ← hstab_bot c]
      exact x.2
    have hcardH : Fintype.card (Multiplicative (ZMod (p ^ k))) = p ^ k :=
      (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card (p ^ k))
    rw [hcard_stab, mul_one, hcardH] at hmul
    exact hmul
  change p ^ k ∣ U.card
  rw [← Fintype.card_coe U]
  have hq_eq :
      Fintype.card ↥U =
        ∑ q : Quotient (MulAction.orbitRel (Multiplicative (ZMod (p ^ k))) ↥U),
          Fintype.card { x : ↥U // Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod (p ^ k))) ↥U) x = q } := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod (p ^ k))) ↥U))).symm
  rw [hq_eq]
  refine Finset.dvd_sum fun q _ => ?_
  induction q using Quotient.inductionOn with
  | h c =>
    have heqo :
        { x : ↥U // Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod (p ^ k))) ↥U) x =
            Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod (p ^ k))) ↥U) c } ≃
          MulAction.orbit (Multiplicative (ZMod (p ^ k))) c :=
      { toFun := fun x => ⟨x.1, by
          have hrel : (MulAction.orbitRel (Multiplicative (ZMod (p ^ k))) ↥U).r x.1 c := Quotient.exact x.2
          exact MulAction.orbitRel_apply.mp hrel⟩
        invFun := fun x => ⟨x.1, Quotient.sound (MulAction.orbitRel_apply.mpr x.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr heqo, horbit_card c]

private lemma zmod_cast_fiber_card {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    [NeZero (p ^ k)] [NeZero (p ^ (k - 1))] (z : ZMod (p ^ (k - 1))) :
    (Finset.univ.filter (fun y : ZMod (p ^ k) =>
      ZMod.castHom (pow_dvd_pow p (Nat.sub_le k 1)) (ZMod (p ^ (k - 1))) y = z)).card = p := by
  let π := ZMod.castHom (pow_dvd_pow p (Nat.sub_le k 1)) (ZMod (p ^ (k - 1)))
  change (Finset.univ.filter (fun y : ZMod (p ^ k) => π y = z)).card = p
  trans Fintype.card (Fin p)
  swap
  · exact Fintype.card_fin p
  symm
  have hkM : p * p ^ (k - 1) = p ^ k := by
    have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    conv_rhs => rw [hk1, pow_succ']
  refine Finset.card_bij (fun (r : Fin p) _ => ((z.val + r.1 * p ^ (k - 1) : ℕ) : ZMod (p ^ k))) ?_ ?_ ?_
  · intro r _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [π]
    rw [ZMod.cast_natCast (pow_dvd_pow p (Nat.sub_le k 1))]
    push_cast
    have hM0zero : (p : ZMod (p ^ (k - 1))) ^ (k - 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hM0zero, mul_zero, add_zero, ZMod.natCast_zmod_val]
  · intro r₁ _ r₂ _ hr
    have hbound1 : z.val + r₁.1 * p ^ (k - 1) < p ^ k := by
      have hz : z.val < p ^ (k - 1) := ZMod.val_lt z
      have hr1 : r₁.1 + 1 ≤ p := r₁.2
      nlinarith
    have hbound2 : z.val + r₂.1 * p ^ (k - 1) < p ^ k := by
      have hz : z.val < p ^ (k - 1) := ZMod.val_lt z
      have hr2 : r₂.1 + 1 ≤ p := r₂.2
      nlinarith
    have hv := congrArg ZMod.val hr
    rw [ZMod.val_natCast_of_lt hbound1, ZMod.val_natCast_of_lt hbound2] at hv
    have hM0pos : 0 < p ^ (k - 1) := pow_pos hp.pos (k - 1)
    have : r₁.1 * p ^ (k - 1) = r₂.1 * p ^ (k - 1) := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hM0pos this)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hmod : y.val % p ^ (k - 1) = z.val := by
      have hv := congrArg ZMod.val hy
      dsimp [π] at hv
      rwa [← ZMod.natCast_zmod_val y, ZMod.cast_natCast (pow_dvd_pow p (Nat.sub_le k 1)) y.val,
        ZMod.val_natCast] at hv
    have hdiv : y.val / p ^ (k - 1) < p := by
      apply Nat.div_lt_of_lt_mul
      rw [mul_comm, hkM]
      exact ZMod.val_lt y
    refine ⟨⟨y.val / p ^ (k - 1), hdiv⟩, Finset.mem_univ _, ?_⟩
    have heq_nat : z.val + (y.val / p ^ (k - 1)) * p ^ (k - 1) = y.val := by
      rw [← hmod, add_comm, mul_comm]
      exact Nat.div_add_mod y.val (p ^ (k - 1))
    rw [heq_nat, ZMod.natCast_zmod_val]

private lemma fix_card_eq_config {p n k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    [NeZero (p ^ k)] [NeZero (p ^ (k - 1))] :
    (Finset.univ.filter (fun c : Config (Fin n × ZMod (p ^ k)) =>
      Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k)) • c = c)).card =
      Fintype.card (Config (Fin n × ZMod (p ^ (k - 1)))) := by
  let π : ZMod (p ^ k) →+* ZMod (p ^ (k - 1)) :=
    ZMod.castHom (pow_dvd_pow p (Nat.sub_le k 1)) (ZMod (p ^ (k - 1)))
  let lift : ZMod (p ^ (k - 1)) → ZMod (p ^ k) := fun z => (z.val : ZMod (p ^ k))
  have hπ_lift : ∀ z : ZMod (p ^ (k - 1)), π (lift z) = z := by
    intro z
    dsimp [π, lift]
    rw [ZMod.cast_natCast (pow_dvd_pow p (Nat.sub_le k 1)) z.val, ZMod.natCast_zmod_val]
  have hπ_fib : ∀ z : ZMod (p ^ (k - 1)), (Finset.univ.filter (fun y : ZMod (p ^ k) => π y = z)).card = p :=
    zmod_cast_fiber_card hp hk
  have hfib_prod :
      ∀ {α : Type} [DecidableEq α] (f : (Fin n × ZMod (p ^ (k - 1))) → α) (v : α),
        (Finset.univ.filter (fun t : Fin n × ZMod (p ^ k) => f (t.1, π t.2) = v)).card =
          p * (Finset.univ.filter (fun t0 : Fin n × ZMod (p ^ (k - 1)) => f t0 = v)).card := by
    intro α _ f v
    let S1 := Finset.univ.filter (fun t : Fin n × ZMod (p ^ k) => f (t.1, π t.2) = v)
    let S0 := Finset.univ.filter (fun t0 : Fin n × ZMod (p ^ (k - 1)) => f t0 = v)
    have hmap : ∀ t ∈ S1, (t.1, π t.2) ∈ S0 := fun t ht =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    have hconst : ∀ t0 ∈ S0, (S1.filter (fun t : Fin n × ZMod (p ^ k) => (t.1, π t.2) = t0)).card = p := by
      intro t0 ht0
      have hv0 : f t0 = v := (Finset.mem_filter.mp ht0).2
      trans (Finset.univ.filter (fun y : ZMod (p ^ k) => π y = t0.2)).card
      swap
      · exact hπ_fib t0.2
      refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
      · intro t ht
        have ht1 := (Finset.mem_filter.mp ht).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.snd ht1⟩
      · intro a ha b hb hab
        have ha1 := (Finset.mem_filter.mp ha).2
        have hb1 := (Finset.mem_filter.mp hb).2
        exact Prod.ext ((congrArg Prod.fst ha1).trans (congrArg Prod.fst hb1).symm) hab
      · intro y hy
        have hy2 : π y = t0.2 := (Finset.mem_filter.mp hy).2
        refine ⟨(t0.1, y), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩, rfl⟩
        · dsimp; rw [hy2, hv0]
        · exact Prod.ext rfl hy2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  let tau : Multiplicative (ZMod (p ^ k)) := Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k))
  have hfix_inv :
      ∀ c : Config (Fin n × ZMod (p ^ k)), tau • c = c →
        ∀ (i : Fin n) (y : ZMod (p ^ k)), c.assign (i, y) = c.assign (i, lift (π y)) := by
    intro c htau i y
    have hstep : ∀ i y, c.assign (i, y - (p ^ (k - 1) : ZMod (p ^ k))) = c.assign (i, y) := fun i y => by
      have h := congrArg (fun x : Config (Fin n × ZMod (p ^ k)) => x.assign (i, y)) htau
      exact h
    have hstep_add : ∀ i y, c.assign (i, y + (p ^ (k - 1) : ZMod (p ^ k))) = c.assign (i, y) := fun i y => by
      have h := hstep i (y + (p ^ (k - 1) : ZMod (p ^ k)))
      simpa using h.symm
    have hmul_step : ∀ (r : ℕ) (i : Fin n) (y : ZMod (p ^ k)),
        c.assign (i, y + ((r * p ^ (k - 1) : ℕ) : ZMod (p ^ k))) = c.assign (i, y) := by
      intro r
      induction r with
      | zero => intro i y; simp
      | succ r ih =>
        intro i y
        have heq : (((r + 1) * p ^ (k - 1) : ℕ) : ZMod (p ^ k)) =
            ((r * p ^ (k - 1) : ℕ) : ZMod (p ^ k)) + (p ^ (k - 1) : ZMod (p ^ k)) := by
          push_cast; ring
        rw [heq, ← add_assoc, hstep_add, ih]
    let diff : ZMod (p ^ k) := y - lift (π y)
    have hπ_diff : π diff = 0 := by
      dsimp [diff]; rw [map_sub, hπ_lift, sub_self]
    have hdvd_diff : p ^ (k - 1) ∣ diff.val := by
      rw [← ZMod.natCast_eq_zero_iff diff.val (p ^ (k - 1))]
      have hv := hπ_diff
      dsimp [π] at hv
      rwa [← ZMod.natCast_zmod_val diff, ZMod.cast_natCast (pow_dvd_pow p (Nat.sub_le k 1)) diff.val] at hv
    rcases hdvd_diff with ⟨r, hr⟩
    have hy_eq : y = lift (π y) + ((r * p ^ (k - 1) : ℕ) : ZMod (p ^ k)) := by
      have h1 : diff = (diff.val : ZMod (p ^ k)) := (ZMod.natCast_zmod_val diff).symm
      rw [hr, mul_comm (p ^ (k - 1)) r] at h1
      dsimp [diff] at h1
      calc
        y = lift (π y) + (y - lift (π y)) := by ring
        _ = lift (π y) + ((r * p ^ (k - 1) : ℕ) : ZMod (p ^ k)) := by rw [h1]
    conv_lhs => rw [hy_eq]
    rw [hmul_step]
  have hp_assign_dvd : ∀ c : Config (Fin n × ZMod (p ^ k)), tau • c = c → ∀ t : Fin n × ZMod (p ^ k), p ∣ (c.assign t).1 := by
    intro c hc t
    let g : (Fin n × ZMod (p ^ (k - 1))) → ℕ := fun t0 => (c.assign (t0.1, lift t0.2)).1
    let m := c.assign t
    have hf_eq :
        Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.assign u = m) =
          Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => g (u.1, π u.2) = m.1) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hfix_inv c hc u.1 u.2]
      exact Fin.ext_iff
    have hfib_p : (Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.assign u = m)).card =
        p * (Finset.univ.filter (fun u0 : Fin n × ZMod (p ^ (k - 1)) => g u0 = m.1)).card := by
      rw [hf_eq]
      exact hfib_prod g m.1
    have hm_pos : (Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.assign u = m)).card = m.1 := by
      rcases c.hblock m with ⟨h0, _⟩ | ⟨_, hc0⟩
      · exfalso
        have hmem : t ∈ Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.assign u = m) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        rw [Finset.card_eq_zero.mp h0] at hmem
        exact Finset.notMem_empty _ hmem
      · exact hc0
    rw [← hm_pos, hfib_p]
    exact dvd_mul_right p _
  have hcardT : Fintype.card (Fin n × ZMod (p ^ k)) = n * p ^ k := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  have hcardT0 : Fintype.card (Fin n × ZMod (p ^ (k - 1))) = n * p ^ (k - 1) := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  have hkM : p ^ k = p * p ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    conv_lhs => rw [hk1, pow_succ']
  have hT_mul : Fintype.card (Fin n × ZMod (p ^ k)) = p * Fintype.card (Fin n × ZMod (p ^ (k - 1))) := by
    rw [hcardT, hcardT0, hkM]; ring
  rw [← Fintype.card_coe]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun c =>
        let g : (Fin n × ZMod (p ^ (k - 1))) → ℕ := fun t0 => (c.1.assign (t0.1, lift t0.2)).1
        have hfix : tau • c.1 = c.1 := (Finset.mem_filter.mp c.2).2
        have hg_dvd : ∀ t0, p ∣ g t0 := fun t0 => hp_assign_dvd c.1 hfix (t0.1, lift t0.2)
        have hg_bound : ∀ t0, g t0 / p < Fintype.card (Fin n × ZMod (p ^ (k - 1))) + 1 := by
          intro t0
          let m := c.1.assign (t0.1, lift t0.2)
          have hm_pos : (Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.1.assign u = m)).card = m.1 := by
            rcases c.1.hblock m with ⟨h0, _⟩ | ⟨_, hc0⟩
            · exfalso
              have hmem : (t0.1, lift t0.2) ∈ Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.1.assign u = m) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
              rw [Finset.card_eq_zero.mp h0] at hmem
              exact Finset.notMem_empty _ hmem
            · exact hc0
          have hle : m.1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := by
            calc
              m.1 = (Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.1.assign u = m)).card := hm_pos.symm
              _ ≤ (Finset.univ : Finset (Fin n × ZMod (p ^ k))).card := Finset.card_filter_le _ _
              _ = Fintype.card (Fin n × ZMod (p ^ k)) := Finset.card_univ
          exact Nat.lt_succ_of_le (Nat.div_le_of_le_mul (by rw [← hT_mul]; exact hle))
        { assign := fun t0 => ⟨g t0 / p, hg_bound t0⟩
          color := fun m0 => c.1.color ⟨p * m0.1, by
            have hm0_lt : m0.1 ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.lt_succ_iff.mp m0.2
            have : p * m0.1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := by rw [hT_mul]; exact Nat.mul_le_mul_left p hm0_lt
            omega⟩
          hblock := fun m0 => by
            let m : Fin (Fintype.card (Fin n × ZMod (p ^ k)) + 1) := ⟨p * m0.1, by
              have hm0_lt : m0.1 ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.lt_succ_iff.mp m0.2
              have : p * m0.1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := by rw [hT_mul]; exact Nat.mul_le_mul_left p hm0_lt
              omega⟩
            have hfilt_eq :
                Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.1.assign u = m) =
                  Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => g (u.1, π u.2) = m.1) := by
              ext u
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [hfix_inv c.1 hfix u.1 u.2]
              exact Fin.ext_iff
            have hfilt0_eq :
                Finset.univ.filter (fun u0 : Fin n × ZMod (p ^ (k - 1)) =>
                    (⟨g u0 / p, hg_bound u0⟩ : Fin (Fintype.card (Fin n × ZMod (p ^ (k - 1))) + 1)) = m0) =
                  Finset.univ.filter (fun u0 : Fin n × ZMod (p ^ (k - 1)) => g u0 = m.1) := by
              ext u0
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
              constructor
              · intro h
                calc
                  g u0 = p * (g u0 / p) := (Nat.mul_div_cancel' (hg_dvd u0)).symm
                  _ = p * m0.1 := by rw [h]
              · intro h
                change g u0 / p = m0.1
                rw [h]
                exact Nat.mul_div_right m0.1 hp.pos
            have hcard_mul :
                (Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.1.assign u = m)).card =
                  p * (Finset.univ.filter (fun u0 : Fin n × ZMod (p ^ (k - 1)) =>
                    (⟨g u0 / p, hg_bound u0⟩ : Fin (Fintype.card (Fin n × ZMod (p ^ (k - 1))) + 1)) = m0)).card := by
              rw [hfilt_eq, hfilt0_eq]
              exact hfib_prod g m.1
            rcases c.1.hblock m with ⟨h0, hcol⟩ | ⟨hm_pos, hm_card⟩
            · left
              refine ⟨?_, hcol⟩
              rw [h0] at hcard_mul
              exact (Nat.mul_eq_zero.mp hcard_mul.symm).resolve_left hp.ne_zero
            · right
              refine ⟨Nat.pos_of_ne_zero fun hz => by simp [m, hz] at hm_pos, ?_⟩
              rw [hm_card] at hcard_mul
              exact Nat.eq_of_mul_eq_mul_left hp.pos hcard_mul.symm }
      invFun := fun c0 =>
        ⟨{ assign := fun t => ⟨p * (c0.assign (t.1, π t.2)).1, by
             have hlt : (c0.assign (t.1, π t.2)).1 ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.lt_succ_iff.mp (c0.assign _).2
             have : p * (c0.assign (t.1, π t.2)).1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := by
               rw [hT_mul]; exact Nat.mul_le_mul_left p hlt
             omega⟩
           color := fun m => if hm : p ∣ m.1 then c0.color ⟨m.1 / p, by
             have hle : m.1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := Nat.lt_succ_iff.mp m.2
             have : m.1 / p ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.div_le_of_le_mul (by rw [← hT_mul]; exact hle)
             omega⟩ else false
           hblock := fun m => by
             by_cases hdvd : p ∣ m.1
             · let m0 : Fin (Fintype.card (Fin n × ZMod (p ^ (k - 1))) + 1) := ⟨m.1 / p, by
                 have hle : m.1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := Nat.lt_succ_iff.mp m.2
                 have : m.1 / p ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.div_le_of_le_mul (by rw [← hT_mul]; exact hle)
                 omega⟩
               have hf_eq :
                   Finset.univ.filter (fun t : Fin n × ZMod (p ^ k) => (⟨p * (c0.assign (t.1, π t.2)).1, by
                       have hlt : (c0.assign (t.1, π t.2)).1 ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.lt_succ_iff.mp (c0.assign _).2
                       have : p * (c0.assign (t.1, π t.2)).1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := by
                         rw [hT_mul]; exact Nat.mul_le_mul_left p hlt
                       omega⟩ : Fin (Fintype.card (Fin n × ZMod (p ^ k)) + 1)) = m) =
                     Finset.univ.filter (fun t : Fin n × ZMod (p ^ k) => c0.assign (t.1, π t.2) = m0) := by
                 ext t
                 simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
                 constructor
                 · intro h
                   change (c0.assign (t.1, π t.2)).1 = m.1 / p
                   rw [← h, Nat.mul_div_right _ hp.pos]
                 · intro h
                   calc
                     p * (c0.assign (t.1, π t.2)).1 = p * (m.1 / p) := by rw [h]
                     _ = m.1 := Nat.mul_div_cancel' hdvd
               have hcard_mul :
                   (Finset.univ.filter (fun t : Fin n × ZMod (p ^ k) => (⟨p * (c0.assign (t.1, π t.2)).1, by
                       have hlt : (c0.assign (t.1, π t.2)).1 ≤ Fintype.card (Fin n × ZMod (p ^ (k - 1))) := Nat.lt_succ_iff.mp (c0.assign _).2
                       have : p * (c0.assign (t.1, π t.2)).1 ≤ Fintype.card (Fin n × ZMod (p ^ k)) := by
                         rw [hT_mul]; exact Nat.mul_le_mul_left p hlt
                       omega⟩ : Fin (Fintype.card (Fin n × ZMod (p ^ k)) + 1)) = m)).card =
                     p * (Finset.univ.filter (fun t0 : Fin n × ZMod (p ^ (k - 1)) => c0.assign t0 = m0)).card := by
                 rw [hf_eq]
                 exact hfib_prod c0.assign m0
               rcases c0.hblock m0 with ⟨h0, hcol⟩ | ⟨hm0_pos, hm0_card⟩
               · left
                 refine ⟨by rw [hcard_mul, h0, mul_zero], ?_⟩
                 simp [hdvd, m0, hcol]
               · right
                 refine ⟨?_, ?_⟩
                 · have : 0 < m.1 / p := hm0_pos
                   have hmp := Nat.mul_div_cancel' hdvd
                   nlinarith [hp.pos]
                 · rw [hcard_mul, hm0_card]
                   change p * (m.1 / p) = m.1
                   exact Nat.mul_div_cancel' hdvd
             · left
               refine ⟨?_, by simp [hdvd]⟩
               rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
               intro t _ ht
               have heq : p * (c0.assign (t.1, π t.2)).1 = m.1 := congrArg Fin.val ht
               exact hdvd ⟨_, heq.symm⟩ },
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
           apply Config.ext
           · funext t
             apply Fin.ext
             dsimp only
             have hπ_sub : π (t.2 - Multiplicative.toAdd (Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k)))) = π t.2 := by
               rw [toAdd_ofAdd, map_sub]
               have h0 : π ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) = 0 := by
                 dsimp [π]
                 rw [ZMod.cast_natCast (pow_dvd_pow p (Nat.sub_le k 1)) (p ^ (k - 1)), ZMod.natCast_self]
               have h0' : π (p ^ (k - 1) : ZMod (p ^ k)) = 0 := by simpa using h0
               rw [h0', sub_zero]
             change p * (c0.assign (t.1, π (t.2 - Multiplicative.toAdd (Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k)))))).1 =
               p * (c0.assign (t.1, π t.2)).1
             rw [hπ_sub]
           · rfl⟩⟩
      left_inv := fun c => by
        apply Subtype.ext
        have hfix : tau • c.1 = c.1 := (Finset.mem_filter.mp c.2).2
        apply Config.ext
        · funext t
          apply Fin.ext
          change p * ((c.1.assign (t.1, lift (π t.2))).1 / p) = (c.1.assign t).1
          rw [← hfix_inv c.1 hfix t.1 t.2]
          exact Nat.mul_div_cancel' (hp_assign_dvd c.1 hfix t)
        · ext m
          dsimp only
          split_ifs with hdvd
          · congr 1
            ext
            exact Nat.mul_div_cancel' hdvd
          · rcases c.1.hblock m with ⟨_, hcol⟩ | ⟨_, hcard⟩
            · exact hcol.symm
            · exfalso
              have hpos : 0 < (Finset.univ.filter (fun u : Fin n × ZMod (p ^ k) => c.1.assign u = m)).card := by
                rcases m with ⟨tv, htlt⟩
                rw [hcard]
                by_contra h0
                have htv : tv = 0 := by omega
                subst htv
                exact hdvd (dvd_zero p)
              rcases Finset.card_pos.mp hpos with ⟨u, hu⟩
              have heq := (Finset.mem_filter.mp hu).2
              rw [← heq] at hdvd
              exact hdvd (hp_assign_dvd c.1 hfix u)
      right_inv := fun c0 => by
        apply Config.ext
        · funext t0
          apply Fin.ext
          change (p * (c0.assign (t0.1, π (lift t0.2))).1) / p = (c0.assign t0).1
          rw [hπ_lift, Nat.mul_div_right _ hp.pos]
        · ext m0
          dsimp only
          rw [dif_pos (dvd_mul_right p m0.1)]
          congr 1
          ext
          exact Nat.mul_div_right m0.1 hp.pos }

private lemma cong_config_zmod_pow {p n k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    [NeZero (p ^ k)] [NeZero (p ^ (k - 1))] :
    ∃ z : ℤ, (Fintype.card (Config (Fin n × ZMod (p ^ k))) : ℤ) -
        (Fintype.card (Config (Fin n × ZMod (p ^ (k - 1)))) : ℤ) = (p : ℤ) ^ k * z := by
  let tau : Multiplicative (ZMod (p ^ k)) := Multiplicative.ofAdd (p ^ (k - 1) : ZMod (p ^ k))
  let Fix := Finset.univ.filter (fun c : Config (Fin n × ZMod (p ^ k)) => tau • c = c)
  let U := Finset.univ.filter (fun c : Config (Fin n × ZMod (p ^ k)) => tau • c ≠ c)
  have hpart : Fix.card + U.card = Fintype.card (Config (Fin n × ZMod (p ^ k))) := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hdvdU : p ^ k ∣ U.card := dvd_nonfixed_card hp hk
  have hfix : Fix.card = Fintype.card (Config (Fin n × ZMod (p ^ (k - 1)))) := fix_card_eq_config hp hk
  rcases hdvdU with ⟨z, hz⟩
  refine ⟨(z : ℤ), ?_⟩
  have h1 : (Fintype.card (Config (Fin n × ZMod (p ^ k))) : ℤ) -
      (Fintype.card (Config (Fin n × ZMod (p ^ (k - 1)))) : ℤ) = (U.card : ℤ) := by
    omega
  rw [h1, hz]
  push_cast
  rfl

end OeisA032312Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a032312.main := by
  intro p n k hp _hn hk
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ (k - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have e1 : Fin (n * p ^ k) ≃ Fin n × ZMod (p ^ k) :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_prod, Fintype.card_fin, ZMod.card])).symm
  have e0 : Fin (n * p ^ (k - 1)) ≃ Fin n × ZMod (p ^ (k - 1)) :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_prod, Fintype.card_fin, ZMod.card])).symm
  rw [OeisA032312Proof.a_eq_card_config, OeisA032312Proof.a_eq_card_config,
    OeisA032312Proof.card_config_congr e1, OeisA032312Proof.card_config_congr e0]
  rcases OeisA032312Proof.cong_config_zmod_pow (n := n) hp hk with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hz_rat : ((Fintype.card (OeisA032312Proof.Config (Fin n × ZMod (p ^ k))) : ℤ) : ℚ) -
      ((Fintype.card (OeisA032312Proof.Config (Fin n × ZMod (p ^ (k - 1)))) : ℤ) : ℚ) =
      (p : ℚ) ^ k * (z : ℚ) := by
    exact_mod_cast hz
  simpa using hz_rat
