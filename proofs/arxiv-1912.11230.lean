import OMAStatements.S_arxiv_1912_11230

/-!
# Proof of Conjecture 31 of Best and Wanless (arXiv 1912.11230)

For a Latin square `L` of order `n`, with `t_ij` the number of transversals of the array obtained by
deleting row `i` and column `j`: `t_ac + t_bc + t_ad + t_bd = 0 (mod 4)` for all `a, b, c, d`.

Outline. For a set `U` of rows, a set `T` of columns and a symbol `s`, let `c_s(U,T)` be the number of
cells of `U x T` with symbol `s`, and `F_(U,T)(z) = prod_s (z + c_s(U,T))`.
* Part A: expanding the product over partial maps symbol -> row and summing over `U` with the signs
  `([a not in U] - [b not in U]) (-1)^|U|` leaves an affine function `alpha_T + beta_T z` of `z`, and
  `t_ac - t_bc = sum over T not containing c of (-1)^|T| beta_T`.
* Part B: complementing `U` gives `beta_T (2z + |T|) = 2 sum_(U contains b, not a) (-1)^|U|
  (F_U(z) - F_U(-z-|T|))`. Evaluating at suitable `z` shows that `beta_T` is even and determines
  `beta_T` modulo 4 by parities of the `c_s(U,T)`; comparing `T` with its complement gives
  `beta_T = beta_(T^c) (mod 4)`.
* Part C: pairing `T` with its complement in the sum for `t_ac - t_bc - t_ad + t_bd` gives divisibility
  by 4; with the equal parity of all `t_ij` this is the conjectured congruence.
-/

namespace LSQ

open Finset OMA.S_arxiv_1912_11230

variable {n : ℕ}

/-- `c_s(U,T)`: the number of cells of `U × T` carrying the symbol `s`. -/
def cnt (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (s : Fin n) : ℤ :=
  ((((U ×ˢ T).filter (fun p : Fin n × Fin n => L p.1 p.2 = s)).card : ℕ) : ℤ)

/-- `F_{U,T}(z) = ∏_s (z + c_s(U,T))`. -/
def Fz (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (z : ℤ) : ℤ :=
  ∏ s : Fin n, (z + cnt L U T s)

/-- The cells selected by a partial map `symbol ↦ row`. -/
def cells (L : Fin n → Fin n → Fin n) (g : Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter (fun p : Fin n × Fin n => g (L p.1 p.2) = some p.1)

/-- The number of symbols not used by `g`. -/
def mz (g : Fin n → Option (Fin n)) : ℕ := (univ.filter (fun s => g s = none)).card

def rws (L : Fin n → Fin n → Fin n) (g : Fin n → Option (Fin n)) : Finset (Fin n) :=
  (cells L g).image Prod.fst

def cls (L : Fin n → Fin n → Fin n) (g : Fin n → Option (Fin n)) : Finset (Fin n) :=
  (cells L g).image Prod.snd

def hfun (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (z : ℤ) (s : Fin n) :
    Option (Fin n) → ℤ
  | none => z
  | some r => if r ∈ U ∧ ∃ j ∈ T, L r j = s then 1 else 0

theorem mem_cells {L : Fin n → Fin n → Fin n} {g : Fin n → Option (Fin n)} {p : Fin n × Fin n} :
    p ∈ cells L g ↔ g (L p.1 p.2) = some p.1 := by
  unfold cells
  rw [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem cnt_eq_sum {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (U T : Finset (Fin n)) (s : Fin n) :
    cnt L U T s = ∑ r : Fin n, (if r ∈ U ∧ ∃ j ∈ T, L r j = s then (1:ℤ) else 0) := by
  rw [Finset.sum_boole]
  unfold cnt
  have himg : ((U ×ˢ T).filter (fun p : Fin n × Fin n => L p.1 p.2 = s)).image Prod.fst
      = univ.filter (fun r => r ∈ U ∧ ∃ j ∈ T, L r j = s) := by
    ext r
    constructor
    · intro h
      obtain ⟨p, hp, rfl⟩ := mem_image.1 h
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      obtain ⟨h1, h2⟩ := mem_product.1 hp1
      exact mem_filter.2 ⟨mem_univ _, h1, p.2, h2, hp2⟩
    · intro h
      obtain ⟨_, hr, j, hj, hs⟩ := mem_filter.1 h
      exact mem_image.2 ⟨(r, j), mem_filter.2 ⟨mem_product.2 ⟨hr, hj⟩, hs⟩, rfl⟩
  have hinj : Set.InjOn Prod.fst
      (((U ×ˢ T).filter (fun p : Fin n × Fin n => L p.1 p.2 = s) : Finset (Fin n × Fin n)) :
        Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    have hp' := (mem_filter.1 (mem_coe.1 hp)).2
    have hq' := (mem_filter.1 (mem_coe.1 hq)).2
    have h1 : p.1 = q.1 := hpq
    have h2 : p.2 = q.2 := by
      apply hrow p.1
      rw [hp', h1, hq']
    exact Prod.ext h1 h2
  rw [← himg, card_image_of_injOn hinj]

theorem hsum {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (U T : Finset (Fin n)) (z : ℤ) (s : Fin n) :
    z + cnt L U T s = ∑ o : Option (Fin n), hfun L U T z s o := by
  rw [Fintype.sum_option, cnt_eq_sum hrow U T s]
  rfl

theorem prod_h {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (U T : Finset (Fin n)) (z : ℤ) (g : Fin n → Option (Fin n)) :
    ∏ s, hfun L U T z s (g s) = z ^ mz g * (if cells L g ⊆ U ×ˢ T then 1 else 0) := by
  have hpt : ∀ s, hfun L U T z s (g s) = (if g s = none then z else 1) *
      (if (∀ r, g s = some r → (r ∈ U ∧ ∃ j ∈ T, L r j = s)) then 1 else 0) := by
    intro s
    cases h : g s with
    | none => simp [hfun]
    | some r => simp [hfun]
  have hiff : (∀ s ∈ (univ : Finset (Fin n)), ∀ r, g s = some r → (r ∈ U ∧ ∃ j ∈ T, L r j = s)) ↔
      cells L g ⊆ U ×ˢ T := by
    constructor
    · intro h p hp
      have hp' := mem_cells.1 hp
      obtain ⟨h1, j, hj, hs⟩ := h (L p.1 p.2) (mem_univ _) p.1 hp'
      have hjp : j = p.2 := hrow p.1 hs
      rw [hjp] at hj
      exact mem_product.2 ⟨h1, hj⟩
    · intro h s _ r hr
      obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 (hrow r)) s
      have hmem : (r, j) ∈ cells L g := by
        rw [mem_cells]
        show g (L r j) = some r
        rw [hj]; exact hr
      obtain ⟨h1, h2⟩ := mem_product.1 (h hmem)
      exact ⟨h1, j, h2, hj⟩
  rw [Finset.prod_congr rfl (fun s _ => hpt s), Finset.prod_mul_distrib, ← Finset.prod_filter,
    Finset.prod_const, Finset.prod_boole]
  simp only [hiff]
  rfl

theorem Fz_expand {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (U T : Finset (Fin n)) (z : ℤ) :
    Fz L U T z = ∑ g : Fin n → Option (Fin n),
      z ^ mz g * (if cells L g ⊆ U ×ˢ T then 1 else 0) := by
  calc Fz L U T z = ∏ s, ∑ o : Option (Fin n), hfun L U T z s o :=
        Finset.prod_congr rfl (fun s _ => hsum hrow U T z s)
    _ = ∑ g : Fin n → Option (Fin n), ∏ s, hfun L U T z s (g s) :=
        Fintype.prod_sum (fun s o => hfun L U T z s o)
    _ = _ := Finset.sum_congr rfl (fun g _ => prod_h hrow U T z g)

theorem subset_iff {L : Fin n → Fin n → Fin n} (g : Fin n → Option (Fin n))
    (U T : Finset (Fin n)) : cells L g ⊆ U ×ˢ T ↔ rws L g ⊆ U ∧ cls L g ⊆ T := by
  constructor
  · intro h
    exact ⟨image_subset_iff.2 (fun p hp => (mem_product.1 (h hp)).1),
      image_subset_iff.2 (fun p hp => (mem_product.1 (h hp)).2)⟩
  · rintro ⟨h1, h2⟩ p hp
    exact mem_product.2 ⟨h1 (mem_image_of_mem _ hp), h2 (mem_image_of_mem _ hp)⟩

/-- Signed sum over the supersets of `R` that avoid `a`. -/
theorem nu_sum (a : Fin n) (R : Finset (Fin n)) :
    ∑ U : Finset (Fin n), (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * (if R ⊆ U then 1 else 0)
      = if R = {a}ᶜ then (-1) ^ (n - 1) else 0 := by
  by_cases hR : R = {a}ᶜ
  · rw [if_pos hR]
    rw [Finset.sum_eq_single ({a}ᶜ : Finset (Fin n))]
    · have h1 : a ∉ ({a}ᶜ : Finset (Fin n)) := by
        rw [mem_compl]; exact fun h => h (mem_singleton_self a)
      have h2 : ({a}ᶜ : Finset (Fin n)).card = n - 1 := by
        rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      have h3 : R ⊆ ({a}ᶜ : Finset (Fin n)) := by rw [hR]
      rw [if_neg h1, if_pos h3, h2]; ring
    · intro U _ hU
      by_cases ha : a ∈ U
      · rw [if_pos ha]; ring
      · have hns : ¬ R ⊆ U := by
          intro hsub
          apply hU
          apply Finset.Subset.antisymm
          · intro x hx
            rw [mem_compl, mem_singleton]
            intro hxa
            rw [hxa] at hx
            exact ha hx
          · rw [← hR]; exact hsub
        rw [if_neg hns]; ring
    · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hR]
    by_cases haR : a ∈ R
    · apply Finset.sum_eq_zero
      intro U _
      by_cases ha : a ∈ U
      · rw [if_pos ha]; ring
      · have hns : ¬ R ⊆ U := fun h => ha (h haR)
        rw [if_neg hns]; ring
    · have hex : ∃ e, e ∉ R ∧ e ≠ a := by
        by_contra hcon
        apply hR
        apply Finset.Subset.antisymm
        · intro x hx
          rw [mem_compl, mem_singleton]
          intro hxa
          rw [hxa] at hx
          exact haR hx
        · intro x hx
          rw [mem_compl, mem_singleton] at hx
          by_contra hxR
          exact hcon ⟨x, hxR, hx⟩
      obtain ⟨e, heR, hea⟩ := hex
      have hae : a ≠ e := fun h => hea h.symm
      apply Finset.sum_involution (fun U _ => if e ∈ U then U.erase e else insert e U)
      · intro U _
        by_cases he : e ∈ U
        · rw [if_pos he]
          have h1 : (a ∈ U.erase e ↔ a ∈ U) := by
            rw [mem_erase]; exact ⟨fun h => h.2, fun h => ⟨hae, h⟩⟩
          have h2 : (R ⊆ U.erase e ↔ R ⊆ U) := by
            constructor
            · intro h; exact h.trans (erase_subset _ _)
            · intro h x hx
              exact mem_erase.2 ⟨fun hxe => heR (hxe ▸ hx), h hx⟩
          have h3 : U.card = (U.erase e).card + 1 := by
            have hpos : 0 < U.card := card_pos.2 ⟨e, he⟩
            rw [card_erase_of_mem he]; omega
          rw [h3, pow_succ]
          simp only [h1, h2]
          ring
        · rw [if_neg he]
          have h1 : (a ∈ insert e U ↔ a ∈ U) := by
            rw [mem_insert]; exact ⟨fun h => h.resolve_left hae, fun h => Or.inr h⟩
          have h2 : (R ⊆ insert e U ↔ R ⊆ U) := by
            constructor
            · intro h x hx
              rcases mem_insert.1 (h hx) with hxe | hxU
              · exact absurd (hxe ▸ hx) heR
              · exact hxU
            · intro h; exact h.trans (subset_insert _ _)
          have h3 : (insert e U).card = U.card + 1 := card_insert_of_notMem he
          rw [h3, pow_succ]
          simp only [h1, h2]
          ring
      · intro U _ _
        by_cases he : e ∈ U
        · rw [if_pos he]
          intro h
          have : e ∈ U.erase e := by rw [h]; exact he
          exact (notMem_erase e U) this
        · rw [if_neg he]
          intro h
          have : e ∈ U := by rw [← h]; exact mem_insert_self e U
          exact he this
      · intro U _
        by_cases he : e ∈ U
        · simp only [if_pos he, notMem_erase, if_false]
          exact insert_erase he
        · simp only [if_neg he, mem_insert_self, if_true]
          exact erase_insert he
      · intro U _; exact mem_univ _

/-- The one-sided signed sum of `F_{U,T}(z)` over the row sets avoiding `a`. -/
theorem PhiA_expand {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (a : Fin n) (T : Finset (Fin n)) (z : ℤ) :
    ∑ U : Finset (Fin n), (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * Fz L U T z
      = (-1) ^ (n - 1) * ∑ g : Fin n → Option (Fin n),
          z ^ mz g * ((if cls L g ⊆ T then 1 else 0) * (if rws L g = {a}ᶜ then 1 else 0)) := by
  have hsplit : ∀ (g : Fin n → Option (Fin n)) (U : Finset (Fin n)),
      (if cells L g ⊆ U ×ˢ T then (1:ℤ) else 0)
        = (if rws L g ⊆ U then 1 else 0) * (if cls L g ⊆ T then 1 else 0) := by
    intro g U
    by_cases h1 : rws L g ⊆ U
    · by_cases h2 : cls L g ⊆ T
      · rw [if_pos h1, if_pos h2, if_pos ((subset_iff g U T).2 ⟨h1, h2⟩)]; ring
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 ((subset_iff g U T).1 h).2)]; ring
    · rw [if_neg h1, if_neg (fun h => h1 ((subset_iff g U T).1 h).1)]; ring
  calc ∑ U : Finset (Fin n), (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * Fz L U T z
      = ∑ U : Finset (Fin n), ∑ g : Fin n → Option (Fin n),
          (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card *
            (z ^ mz g * (if cells L g ⊆ U ×ˢ T then 1 else 0)) := by
        refine Finset.sum_congr rfl (fun U _ => ?_)
        rw [Fz_expand hrow, Finset.mul_sum]
    _ = ∑ g : Fin n → Option (Fin n), ∑ U : Finset (Fin n),
          (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card *
            (z ^ mz g * (if cells L g ⊆ U ×ˢ T then 1 else 0)) := Finset.sum_comm
    _ = ∑ g : Fin n → Option (Fin n), (-1) ^ (n - 1) *
          (z ^ mz g * ((if cls L g ⊆ T then 1 else 0) * (if rws L g = {a}ᶜ then 1 else 0))) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        have hn := nu_sum a (rws L g)
        calc ∑ U : Finset (Fin n), (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card *
              (z ^ mz g * (if cells L g ⊆ U ×ˢ T then 1 else 0))
            = ∑ U : Finset (Fin n), (z ^ mz g * (if cls L g ⊆ T then 1 else 0)) *
                ((if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * (if rws L g ⊆ U then 1 else 0)) := by
              refine Finset.sum_congr rfl (fun U _ => ?_)
              rw [hsplit g U]; ring
          _ = (z ^ mz g * (if cls L g ⊆ T then 1 else 0)) *
                ∑ U : Finset (Fin n),
                  (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * (if rws L g ⊆ U then 1 else 0) :=
              (Finset.mul_sum _ _ _).symm
          _ = _ := by
              rw [hn]
              by_cases hr : rws L g = {a}ᶜ
              · rw [if_pos hr, if_pos hr]; ring
              · rw [if_neg hr, if_neg hr]; ring
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem cells_card_add {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (g : Fin n → Option (Fin n)) : (cells L g).card + mz g = n := by
  have himg : (cells L g).image (fun p : Fin n × Fin n => L p.1 p.2)
      = univ.filter (fun s => ¬ g s = none) := by
    ext s
    constructor
    · intro h
      obtain ⟨p, hp, rfl⟩ := mem_image.1 h
      have hp' := mem_cells.1 hp
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [hp']
      exact Option.some_ne_none _
    · intro h
      have hs := (mem_filter.1 h).2
      cases hgs : g s with
      | none => exact absurd hgs hs
      | some r =>
        obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 (hrow r)) s
        refine mem_image.2 ⟨(r, j), ?_, hj⟩
        rw [mem_cells]
        show g (L r j) = some r
        rw [hj]; exact hgs
  have hinj : Set.InjOn (fun p : Fin n × Fin n => L p.1 p.2)
      ((cells L g : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    have hp' := mem_cells.1 (mem_coe.1 hp)
    have hq' := mem_cells.1 (mem_coe.1 hq)
    have hpq' : L p.1 p.2 = L q.1 q.2 := hpq
    rw [hpq'] at hp'
    have h1 : p.1 = q.1 := Option.some.inj (hp'.symm.trans hq')
    have h2 : p.2 = q.2 := by
      apply hrow p.1
      rw [hpq', h1]
    exact Prod.ext h1 h2
  have hc : (cells L g).card = (univ.filter (fun s => ¬ g s = none)).card := by
    rw [← himg, card_image_of_injOn hinj]
  have hadd := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun s => g s = none)
  rw [card_univ, Fintype.card_fin] at hadd
  unfold mz
  omega

/-- The counts behind the constant and the linear coefficient. -/
def NA (L : Fin n → Fin n → Fin n) (a : Fin n) (T : Finset (Fin n)) (m : ℕ) : ℤ :=
  ∑ g : Fin n → Option (Fin n), (if mz g = m ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ then 1 else 0)

theorem PhiA_affine {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (a : Fin n) (T : Finset (Fin n)) (z : ℤ) :
    ∑ U : Finset (Fin n), (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * Fz L U T z
      = (-1) ^ (n - 1) * (NA L a T 0 + NA L a T 1 * z) := by
  rw [PhiA_expand hrow]
  congr 1
  unfold NA
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases hc : cls L g ⊆ T
  · by_cases hr : rws L g = {a}ᶜ
    · have hn : 0 < n := Fin.pos a
      have h1 : (rws L g).card = n - 1 := by
        rw [hr, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      have h2 : (rws L g).card ≤ (cells L g).card := Finset.card_image_le
      have h3 := cells_card_add hrow g
      have hm : mz g = 0 ∨ mz g = 1 := by omega
      rcases hm with hm | hm
      · rw [if_pos hc, if_pos hr,
          if_pos (show mz g = 0 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ from ⟨hm, hc, hr⟩),
          if_neg (fun h : mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => by have h' := h.1; omega), hm]
        ring
      · rw [if_pos hc, if_pos hr,
          if_neg (fun h : mz g = 0 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => by have h' := h.1; omega),
          if_pos (show mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ from ⟨hm, hc, hr⟩), hm]
        ring
    · rw [if_neg hr, if_neg (fun h : mz g = 0 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => hr h.2.2),
        if_neg (fun h : mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => hr h.2.2)]
      ring
  · rw [if_neg hc, if_neg (fun h : mz g = 0 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => hc h.2.1),
      if_neg (fun h : mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => hc h.2.1)]
    ring

end LSQ

namespace LSQ

open Finset OMA.S_arxiv_1912_11230

variable {n : ℕ}

theorem G_to_T {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i)) (a c : Fin n)
    (g : Fin n → Option (Fin n)) (hm : mz g = 1) (hc : cls L g = {c}ᶜ) (hr : rws L g = {a}ᶜ) :
    IsTransversalOfMinor L a c (cells L g) := by
  have hn : 0 < n := Fin.pos a
  have h3 := cells_card_add hrow g
  have hcard : (cells L g).card = n - 1 := by omega
  have hr1 : (rws L g).card = n - 1 := by
    rw [hr, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hc1 : (cls L g).card = n - 1 := by
    rw [hc, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hinj1 : Set.InjOn Prod.fst ((cells L g : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) :=
    Finset.card_image_iff.1 (by
      show (rws L g).card = (cells L g).card
      rw [hr1, hcard])
  have hinj2 : Set.InjOn Prod.snd ((cells L g : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) :=
    Finset.card_image_iff.1 (by
      show (cls L g).card = (cells L g).card
      rw [hc1, hcard])
  refine ⟨hcard, ?_, ?_⟩
  · intro p hp
    have h1 : p.1 ∈ rws L g := mem_image_of_mem _ hp
    have h2 : p.2 ∈ cls L g := mem_image_of_mem _ hp
    rw [hr, mem_compl, mem_singleton] at h1
    rw [hc, mem_compl, mem_singleton] at h2
    exact ⟨h1, h2⟩
  · intro p hp q hq hpq
    have hne1 : p.1 ≠ q.1 := fun h => hpq (hinj1 (mem_coe.2 hp) (mem_coe.2 hq) h)
    have hne2 : p.2 ≠ q.2 := fun h => hpq (hinj2 (mem_coe.2 hp) (mem_coe.2 hq) h)
    refine ⟨hne1, hne2, ?_⟩
    intro hs
    have hp' := mem_cells.1 hp
    have hq' := mem_cells.1 hq
    rw [hs] at hp'
    exact hne1 (Option.some.inj (hp'.symm.trans hq'))

theorem cells_inj {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (g g' : Fin n → Option (Fin n)) (h : cells L g = cells L g') : g = g' := by
  have key : ∀ (f : Fin n → Option (Fin n)) (s r j : Fin n), L r j = s →
      (f s = some r ↔ (r, j) ∈ cells L f) := by
    intro f s r j hj
    rw [mem_cells]
    show f s = some r ↔ f (L r j) = some r
    rw [hj]
  funext s
  cases hg : g s with
  | none =>
    cases hg' : g' s with
    | none => rfl
    | some r =>
      obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 (hrow r)) s
      have h1 := (key g' s r j hj).1 hg'
      rw [← h] at h1
      have h2 := (key g s r j hj).2 h1
      rw [hg] at h2
      exact (Option.some_ne_none r h2.symm).elim
  | some r =>
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 (hrow r)) s
    have h1 := (key g s r j hj).1 hg
    rw [h] at h1
    exact ((key g' s r j hj).2 h1).symm

/-- The partial map `symbol ↦ row` of a set of cells with distinct symbols. -/
noncomputable def gOf (L : Fin n → Fin n → Fin n) (F : Finset (Fin n × Fin n)) (s : Fin n) :
    Option (Fin n) :=
  if h : ∃ p ∈ F, L p.1 p.2 = s then some (Classical.choose h).1 else none

theorem gOf_mem {L : Fin n → Fin n → Fin n} {F : Finset (Fin n × Fin n)}
    (hrain : ∀ p ∈ F, ∀ q ∈ F, L p.1 p.2 = L q.1 q.2 → p = q) {p : Fin n × Fin n} (hp : p ∈ F) :
    gOf L F (L p.1 p.2) = some p.1 := by
  have h : ∃ q ∈ F, L q.1 q.2 = L p.1 p.2 := ⟨p, hp, rfl⟩
  unfold gOf
  rw [dif_pos h]
  have hc := Classical.choose_spec h
  have he : Classical.choose h = p := hrain _ hc.1 _ hp hc.2
  rw [he]

theorem gOf_some {L : Fin n → Fin n → Fin n} {F : Finset (Fin n × Fin n)} {s r : Fin n}
    (h : gOf L F s = some r) : ∃ p ∈ F, L p.1 p.2 = s ∧ p.1 = r := by
  unfold gOf at h
  by_cases hex : ∃ p ∈ F, L p.1 p.2 = s
  · rw [dif_pos hex] at h
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1, (Classical.choose_spec hex).2,
      Option.some.inj h⟩
  · rw [dif_neg hex] at h
    exact (Option.some_ne_none r h.symm).elim

theorem cells_gOf {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    {F : Finset (Fin n × Fin n)}
    (hrain : ∀ p ∈ F, ∀ q ∈ F, L p.1 p.2 = L q.1 q.2 → p = q) : cells L (gOf L F) = F := by
  ext p
  rw [mem_cells]
  constructor
  · intro h
    obtain ⟨q, hq, hs, h1⟩ := gOf_some h
    have h2 : q.2 = p.2 := by
      apply hrow q.1
      rw [hs, h1]
    have hqp : q = p := Prod.ext h1 h2
    rw [← hqp]; exact hq
  · intro hp; exact gOf_mem hrain hp

theorem T_to_G {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i)) (a c : Fin n)
    (F : Finset (Fin n × Fin n)) (hF : IsTransversalOfMinor L a c F) :
    (mz (gOf L F) = 1 ∧ cls L (gOf L F) = {c}ᶜ ∧ rws L (gOf L F) = {a}ᶜ) ∧
      cells L (gOf L F) = F := by
  obtain ⟨hcard, hav, hpw⟩ := hF
  have hn : 0 < n := Fin.pos a
  have hrain : ∀ p ∈ F, ∀ q ∈ F, L p.1 p.2 = L q.1 q.2 → p = q := by
    intro p hp q hq hs
    by_contra hne
    exact (hpw p hp q hq hne).2.2 hs
  have hcells := cells_gOf hrow hrain
  have h3 := cells_card_add hrow (gOf L F)
  rw [hcells] at h3
  have hinj1 : Set.InjOn Prod.fst ((F : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    by_contra hne
    exact (hpw p (mem_coe.1 hp) q (mem_coe.1 hq) hne).1 hpq
  have hinj2 : Set.InjOn Prod.snd ((F : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    by_contra hne
    exact (hpw p (mem_coe.1 hp) q (mem_coe.1 hq) hne).2.1 hpq
  have hm : mz (gOf L F) = 1 := by omega
  refine ⟨⟨hm, ?_, ?_⟩, hcells⟩
  · show (cells L (gOf L F)).image Prod.snd = {c}ᶜ
    rw [hcells]
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      rw [mem_compl, mem_singleton]; exact (hav p hp).2
    · have e1 : ({c}ᶜ : Finset (Fin n)).card = n - 1 := by
        rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      have e2 : (F.image Prod.snd).card = n - 1 := by
        rw [card_image_of_injOn hinj2, hcard]
      exact le_of_eq (e1.trans e2.symm)
  · show (cells L (gOf L F)).image Prod.fst = {a}ᶜ
    rw [hcells]
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      rw [mem_compl, mem_singleton]; exact (hav p hp).1
    · have e1 : ({a}ᶜ : Finset (Fin n)).card = n - 1 := by
        rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      have e2 : (F.image Prod.fst).card = n - 1 := by
        rw [card_image_of_injOn hinj1, hcard]
      exact le_of_eq (e1.trans e2.symm)

theorem card_G_eq_t {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (a c : Fin n) :
    (univ.filter (fun g : Fin n → Option (Fin n) =>
      mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ)).card = t L a c := by
  unfold t
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_eq_of_bijective
    (fun g : {g : Fin n → Option (Fin n) // mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ} =>
      (⟨cells L g.1, G_to_T hrow a c g.1 g.2.1 g.2.2.1 g.2.2.2⟩ :
        {F : Finset (Fin n × Fin n) // IsTransversalOfMinor L a c F}))
  constructor
  · intro g g' h
    have h' : cells L g.1 = cells L g'.1 := congrArg Subtype.val h
    exact Subtype.ext (cells_inj hrow g.1 g'.1 h')
  · intro F
    obtain ⟨hQ, hc⟩ := T_to_G hrow a c F.1 F.2
    exact ⟨⟨gOf L F.1, hQ⟩, Subtype.ext hc⟩

theorem t_eq {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i)) (a c : Fin n) :
    (t L a c : ℤ) = ∑ T : Finset (Fin n),
      (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * ((-1) ^ (n - 1) * NA L a T 1) := by
  rw [← card_G_eq_t hrow a c]
  unfold NA
  have hterm : ∀ (g : Fin n → Option (Fin n)) (T : Finset (Fin n)),
      (if mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ then (1:ℤ) else 0)
        = (if mz g = 1 ∧ rws L g = {a}ᶜ then 1 else 0) * (if cls L g ⊆ T then 1 else 0) := by
    intro g T
    by_cases h1 : mz g = 1 ∧ rws L g = {a}ᶜ
    · by_cases h2 : cls L g ⊆ T
      · rw [if_pos h1, if_pos h2,
          if_pos (show mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ from ⟨h1.1, h2, h1.2⟩)]
        ring
      · rw [if_pos h1, if_neg h2,
          if_neg (fun h : mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => h2 h.2.1)]
        ring
    · rw [if_neg h1, if_neg (fun h : mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ => h1 ⟨h.1, h.2.2⟩)]
      ring
  have hsq : ((-1:ℤ) ^ (n - 1)) * ((-1) ^ (n - 1)) = 1 := by
    rw [← mul_pow]; norm_num
  calc ((univ.filter (fun g : Fin n → Option (Fin n) =>
          mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ)).card : ℤ)
      = ∑ g : Fin n → Option (Fin n),
          (if mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ then (1:ℤ) else 0) := by
        rw [Finset.sum_boole]
    _ = ∑ g : Fin n → Option (Fin n), (-1) ^ (n - 1) *
          ((if mz g = 1 ∧ rws L g = {a}ᶜ then 1 else 0) *
            ∑ T : Finset (Fin n),
              (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * (if cls L g ⊆ T then 1 else 0)) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [nu_sum c (cls L g)]
        by_cases h1 : mz g = 1 ∧ rws L g = {a}ᶜ
        · by_cases h2 : cls L g = {c}ᶜ
          · rw [if_pos h1, if_pos h2,
              if_pos (show mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ from ⟨h1.1, h2, h1.2⟩)]
            linear_combination -hsq
          · rw [if_pos h1, if_neg h2,
              if_neg (fun h : mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ => h2 h.2.1)]
            ring
        · rw [if_neg h1,
            if_neg (fun h : mz g = 1 ∧ cls L g = {c}ᶜ ∧ rws L g = {a}ᶜ => h1 ⟨h.1, h.2.2⟩)]
          ring
    _ = ∑ g : Fin n → Option (Fin n), ∑ T : Finset (Fin n),
          (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * ((-1) ^ (n - 1) *
            (if mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ then 1 else 0)) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [hterm g T]; ring
    _ = ∑ T : Finset (Fin n), ∑ g : Fin n → Option (Fin n),
          (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * ((-1) ^ (n - 1) *
            (if mz g = 1 ∧ cls L g ⊆ T ∧ rws L g = {a}ᶜ then 1 else 0)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]

/-- `eps_ab(U) = [a ∉ U] - [b ∉ U]`. -/
def eps (a b : Fin n) (U : Finset (Fin n)) : ℤ :=
  (if a ∈ U then 0 else 1) - (if b ∈ U then 0 else 1)

def alpha (L : Fin n → Fin n → Fin n) (a b : Fin n) (T : Finset (Fin n)) : ℤ :=
  (-1) ^ (n - 1) * (NA L a T 0 - NA L b T 0)

def beta (L : Fin n → Fin n → Fin n) (a b : Fin n) (T : Finset (Fin n)) : ℤ :=
  (-1) ^ (n - 1) * (NA L a T 1 - NA L b T 1)

def Phi (L : Fin n → Fin n → Fin n) (a b : Fin n) (T : Finset (Fin n)) (z : ℤ) : ℤ :=
  ∑ U : Finset (Fin n), eps a b U * (-1) ^ U.card * Fz L U T z

theorem Phi_affine {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (a b : Fin n) (T : Finset (Fin n)) (z : ℤ) :
    Phi L a b T z = alpha L a b T + beta L a b T * z := by
  have h : Phi L a b T z =
      (∑ U : Finset (Fin n), (if a ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * Fz L U T z)
        - ∑ U : Finset (Fin n), (if b ∈ U then (0:ℤ) else 1) * (-1) ^ U.card * Fz L U T z := by
    unfold Phi eps
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    ring
  rw [h, PhiA_affine hrow a, PhiA_affine hrow b]
  unfold alpha beta
  ring

theorem t_diff {L : Fin n → Fin n → Fin n} (hrow : ∀ i, Function.Injective (L i))
    (a b c : Fin n) :
    (t L a c : ℤ) - (t L b c : ℤ) = ∑ T : Finset (Fin n),
      (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T := by
  rw [t_eq hrow a c, t_eq hrow b c, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  unfold beta
  ring

end LSQ

namespace LSQ

open Finset OMA.S_arxiv_1912_11230

variable {n : ℕ}

/-! ### Line sums -/

theorem cnt_eq_sum_col {L : Fin n → Fin n → Fin n}
    (hcol : ∀ j, Function.Injective (fun i => L i j)) (U T : Finset (Fin n)) (s : Fin n) :
    cnt L U T s = ∑ j : Fin n, (if j ∈ T ∧ ∃ i ∈ U, L i j = s then (1:ℤ) else 0) := by
  rw [Finset.sum_boole]
  unfold cnt
  have himg : ((U ×ˢ T).filter (fun p : Fin n × Fin n => L p.1 p.2 = s)).image Prod.snd
      = univ.filter (fun j => j ∈ T ∧ ∃ i ∈ U, L i j = s) := by
    ext j
    constructor
    · intro h
      obtain ⟨p, hp, rfl⟩ := mem_image.1 h
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      obtain ⟨h1, h2⟩ := mem_product.1 hp1
      exact mem_filter.2 ⟨mem_univ _, h2, p.1, h1, hp2⟩
    · intro h
      obtain ⟨_, hj, i, hi, hs⟩ := mem_filter.1 h
      exact mem_image.2 ⟨(i, j), mem_filter.2 ⟨mem_product.2 ⟨hi, hj⟩, hs⟩, rfl⟩
  have hinj : Set.InjOn Prod.snd
      (((U ×ˢ T).filter (fun p : Fin n × Fin n => L p.1 p.2 = s) : Finset (Fin n × Fin n)) :
        Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    have hp' := (mem_filter.1 (mem_coe.1 hp)).2
    have hq' := (mem_filter.1 (mem_coe.1 hq)).2
    have h2 : p.2 = q.2 := hpq
    have h1 : p.1 = q.1 := by
      apply hcol p.2
      show L p.1 p.2 = L q.1 p.2
      rw [hp', h2, hq']
    exact Prod.ext h1 h2
  rw [← himg, card_image_of_injOn hinj]

theorem cnt_compl_rows {L : Fin n → Fin n → Fin n}
    (hcol : ∀ j, Function.Injective (fun i => L i j)) (U T : Finset (Fin n)) (s : Fin n) :
    cnt L Uᶜ T s = (T.card : ℤ) - cnt L U T s := by
  have h : cnt L U T s + cnt L Uᶜ T s = (T.card : ℤ) := by
    rw [cnt_eq_sum_col hcol, cnt_eq_sum_col hcol, ← Finset.sum_add_distrib]
    have hpt : ∀ j : Fin n, (if j ∈ T ∧ ∃ i ∈ U, L i j = s then (1:ℤ) else 0)
        + (if j ∈ T ∧ ∃ i ∈ Uᶜ, L i j = s then (1:ℤ) else 0) = if j ∈ T then 1 else 0 := by
      intro j
      obtain ⟨i0, hi0⟩ := (Finite.injective_iff_surjective.1 (hcol j)) s
      have hi0' : L i0 j = s := hi0
      have huniq : ∀ i, L i j = s → i = i0 := by
        intro i his
        apply hcol j
        show L i j = L i0 j
        rw [his, hi0']
      by_cases hj : j ∈ T
      · by_cases hU : i0 ∈ U
        · have h1 : j ∈ T ∧ ∃ i ∈ U, L i j = s := ⟨hj, i0, hU, hi0'⟩
          have h2 : ¬ (j ∈ T ∧ ∃ i ∈ Uᶜ, L i j = s) := by
            rintro ⟨_, i, hi, his⟩
            rw [huniq i his, mem_compl] at hi
            exact hi hU
          rw [if_pos h1, if_neg h2, if_pos hj]; norm_num
        · have h1 : ¬ (j ∈ T ∧ ∃ i ∈ U, L i j = s) := by
            rintro ⟨_, i, hi, his⟩
            rw [huniq i his] at hi
            exact hU hi
          have h2 : j ∈ T ∧ ∃ i ∈ Uᶜ, L i j = s := ⟨hj, i0, mem_compl.2 hU, hi0'⟩
          rw [if_neg h1, if_pos h2, if_pos hj]; norm_num
      · rw [if_neg (fun h : j ∈ T ∧ ∃ i ∈ U, L i j = s => hj h.1),
          if_neg (fun h : j ∈ T ∧ ∃ i ∈ Uᶜ, L i j = s => hj h.1), if_neg hj]
        norm_num
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_boole]
    simp
  linarith

theorem cnt_compl_cols {L : Fin n → Fin n → Fin n}
    (hrow : ∀ i, Function.Injective (L i)) (U T : Finset (Fin n)) (s : Fin n) :
    cnt L U Tᶜ s = (U.card : ℤ) - cnt L U T s := by
  have h : cnt L U T s + cnt L U Tᶜ s = (U.card : ℤ) := by
    rw [cnt_eq_sum hrow, cnt_eq_sum hrow, ← Finset.sum_add_distrib]
    have hpt : ∀ r : Fin n, (if r ∈ U ∧ ∃ j ∈ T, L r j = s then (1:ℤ) else 0)
        + (if r ∈ U ∧ ∃ j ∈ Tᶜ, L r j = s then (1:ℤ) else 0) = if r ∈ U then 1 else 0 := by
      intro r
      obtain ⟨j0, hj0⟩ := (Finite.injective_iff_surjective.1 (hrow r)) s
      have huniq : ∀ j, L r j = s → j = j0 := by
        intro j hjs
        apply hrow r
        rw [hjs, hj0]
      by_cases hr : r ∈ U
      · by_cases hT : j0 ∈ T
        · have h1 : r ∈ U ∧ ∃ j ∈ T, L r j = s := ⟨hr, j0, hT, hj0⟩
          have h2 : ¬ (r ∈ U ∧ ∃ j ∈ Tᶜ, L r j = s) := by
            rintro ⟨_, j, hj, hjs⟩
            rw [huniq j hjs, mem_compl] at hj
            exact hj hT
          rw [if_pos h1, if_neg h2, if_pos hr]; norm_num
        · have h1 : ¬ (r ∈ U ∧ ∃ j ∈ T, L r j = s) := by
            rintro ⟨_, j, hj, hjs⟩
            rw [huniq j hjs] at hj
            exact hT hj
          have h2 : r ∈ U ∧ ∃ j ∈ Tᶜ, L r j = s := ⟨hr, j0, mem_compl.2 hT, hj0⟩
          rw [if_neg h1, if_pos h2, if_pos hr]; norm_num
      · rw [if_neg (fun h : r ∈ U ∧ ∃ j ∈ T, L r j = s => hr h.1),
          if_neg (fun h : r ∈ U ∧ ∃ j ∈ Tᶜ, L r j = s => hr h.1), if_neg hr]
        norm_num
    rw [Finset.sum_congr rfl (fun r _ => hpt r), Finset.sum_boole]
    simp
  linarith

theorem cnt_sum (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) :
    ∑ s : Fin n, cnt L U T s = (U.card : ℤ) * T.card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => L p.1 p.2)
    (s := U ×ˢ T) (t := (univ : Finset (Fin n))) (fun p _ => by simp)
  unfold cnt
  rw [← Nat.cast_sum, ← h, card_product]
  push_cast
  ring

theorem card_compl_add (U : Finset (Fin n)) : (Uᶜ).card + U.card = n := by
  have h1 := Finset.card_compl U
  have h2 := Finset.card_le_univ U
  rw [Fintype.card_fin] at h1 h2
  omega

theorem neg_one_pow_compl (U : Finset (Fin n)) :
    ((-1:ℤ)) ^ (Uᶜ).card = (-1) ^ n * (-1) ^ U.card := by
  have h := card_compl_add U
  have hsq : ((-1:ℤ) ^ U.card) * ((-1) ^ U.card) = 1 := by rw [← mul_pow]; norm_num
  calc ((-1:ℤ)) ^ (Uᶜ).card = (-1) ^ (Uᶜ).card * ((-1) ^ U.card * (-1) ^ U.card) := by
        rw [hsq, mul_one]
    _ = (-1) ^ ((Uᶜ).card + U.card) * (-1) ^ U.card := by rw [pow_add]; ring
    _ = _ := by rw [h]

theorem Fz_compl {L : Fin n → Fin n → Fin n}
    (hcol : ∀ j, Function.Injective (fun i => L i j)) (U T : Finset (Fin n)) (z : ℤ) :
    Fz L Uᶜ T z = (-1) ^ n * Fz L U T (-z - (T.card : ℤ)) := by
  unfold Fz
  calc ∏ s : Fin n, (z + cnt L Uᶜ T s)
      = ∏ s : Fin n, ((-1) * ((-z - (T.card : ℤ)) + cnt L U T s)) := by
        refine Finset.prod_congr rfl (fun s _ => ?_)
        rw [cnt_compl_rows hcol]; ring
    _ = (∏ _s : Fin n, (-1:ℤ)) * ∏ s : Fin n, ((-z - (T.card : ℤ)) + cnt L U T s) :=
        Finset.prod_mul_distrib
    _ = _ := by rw [Finset.prod_const, card_univ, Fintype.card_fin]

/-! ### Pairing a set with its complement -/

theorem pair_sum (x y : Fin n) (f : Finset (Fin n) → ℤ)
    (hf : ∀ U : Finset (Fin n), (x ∈ U ↔ y ∈ U) → f U = 0) :
    ∑ U : Finset (Fin n), f U
      = ∑ U ∈ univ.filter (fun U : Finset (Fin n) => y ∈ U ∧ x ∉ U), (f U + f Uᶜ) := by
  have hpt : ∀ U : Finset (Fin n), f U
      = (if y ∈ U ∧ x ∉ U then f U else 0) + (if x ∈ U ∧ y ∉ U then f U else 0) := by
    intro U
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · rw [if_neg (fun h : y ∈ U ∧ x ∉ U => h.2 hx), if_neg (fun h : x ∈ U ∧ y ∉ U => h.2 hy),
          hf U ⟨fun _ => hy, fun _ => hx⟩]
        ring
      · rw [if_neg (fun h : y ∈ U ∧ x ∉ U => h.2 hx),
          if_pos (show x ∈ U ∧ y ∉ U from ⟨hx, hy⟩)]
        ring
    · by_cases hy : y ∈ U
      · rw [if_pos (show y ∈ U ∧ x ∉ U from ⟨hy, hx⟩),
          if_neg (fun h : x ∈ U ∧ y ∉ U => hx h.1)]
        ring
      · rw [if_neg (fun h : y ∈ U ∧ x ∉ U => hy h.1), if_neg (fun h : x ∈ U ∧ y ∉ U => hx h.1),
          hf U ⟨fun h => absurd h hx, fun h => absurd h hy⟩]
        ring
  have himg : (univ.filter (fun U : Finset (Fin n) => y ∈ U ∧ x ∉ U)).image compl
      = univ.filter (fun U : Finset (Fin n) => x ∈ U ∧ y ∉ U) := by
    ext U
    constructor
    · intro h
      obtain ⟨V, hV, rfl⟩ := mem_image.1 h
      obtain ⟨_, hy, hx⟩ := mem_filter.1 hV
      exact mem_filter.2 ⟨mem_univ _, mem_compl.2 hx, fun h' => (mem_compl.1 h') hy⟩
    · intro h
      obtain ⟨_, hx, hy⟩ := mem_filter.1 h
      exact mem_image.2 ⟨Uᶜ, mem_filter.2 ⟨mem_univ _, mem_compl.2 hy,
        fun h' => (mem_compl.1 h') hx⟩, compl_compl U⟩
  calc ∑ U : Finset (Fin n), f U
      = ∑ U : Finset (Fin n), ((if y ∈ U ∧ x ∉ U then f U else 0)
          + (if x ∈ U ∧ y ∉ U then f U else 0)) := Finset.sum_congr rfl (fun U _ => hpt U)
    _ = (∑ U ∈ univ.filter (fun U : Finset (Fin n) => y ∈ U ∧ x ∉ U), f U)
          + ∑ U ∈ univ.filter (fun U : Finset (Fin n) => x ∈ U ∧ y ∉ U), f U := by
        rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ = (∑ U ∈ univ.filter (fun U : Finset (Fin n) => y ∈ U ∧ x ∉ U), f U)
          + ∑ U ∈ univ.filter (fun U : Finset (Fin n) => y ∈ U ∧ x ∉ U), f Uᶜ := by
        rw [← himg, Finset.sum_image (fun U _ V _ h => compl_injective h)]
    _ = _ := Finset.sum_add_distrib.symm

/-- The row sets containing `b` and not `a`. -/
def Ub (a b : Fin n) : Finset (Finset (Fin n)) :=
  univ.filter (fun U : Finset (Fin n) => b ∈ U ∧ a ∉ U)

theorem Phi_eq_Xi {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (z : ℤ) :
    Phi L a b T z
      = ∑ U ∈ Ub a b, (-1) ^ U.card * (Fz L U T z - Fz L U T (-z - (T.card : ℤ))) := by
  unfold Phi Ub
  rw [pair_sum a b (fun U => eps a b U * (-1) ^ U.card * Fz L U T z)]
  · refine Finset.sum_congr rfl (fun U hU => ?_)
    obtain ⟨_, hb, ha⟩ := mem_filter.1 hU
    have e1 : eps a b U = 1 := by
      unfold eps
      rw [if_neg ha, if_pos hb]; ring
    have e2 : eps a b Uᶜ = -1 := by
      unfold eps
      rw [if_pos (mem_compl.2 ha), if_neg (fun h => (mem_compl.1 h) hb)]; ring
    have hsq : ((-1:ℤ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    show eps a b U * (-1) ^ U.card * Fz L U T z
      + eps a b Uᶜ * (-1) ^ (Uᶜ).card * Fz L Uᶜ T z = _
    rw [e1, e2, neg_one_pow_compl, Fz_compl hL.2]
    linear_combination (-((-1:ℤ) ^ U.card) * Fz L U T (-z - (T.card : ℤ))) * hsq
  · intro U hU
    have h0 : eps a b U = 0 := by
      unfold eps
      by_cases ha : a ∈ U
      · rw [if_pos ha, if_pos (hU.1 ha)]; ring
      · rw [if_neg ha, if_neg (fun h => ha (hU.2 h))]; ring
    show eps a b U * (-1) ^ U.card * Fz L U T z = 0
    rw [h0]; ring

/-- The master identity: `beta_T (2z + |T|) = 2 Σ_{U ∋ b, U ∌ a} (-1)^|U| (F_U(z) - F_U(-z-|T|))`. -/
theorem master {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (z : ℤ) :
    beta L a b T * (2 * z + (T.card : ℤ))
      = 2 * ∑ U ∈ Ub a b, (-1) ^ U.card * (Fz L U T z - Fz L U T (-z - (T.card : ℤ))) := by
  have h1 := Phi_affine hL.1 a b T z
  have h2 := Phi_affine hL.1 a b T (-z - (T.card : ℤ))
  rw [Phi_eq_Xi hL] at h1 h2
  have h3 : ∑ U ∈ Ub a b, (-1:ℤ) ^ U.card *
        (Fz L U T (-z - (T.card : ℤ)) - Fz L U T (-(-z - (T.card : ℤ)) - (T.card : ℤ)))
      = - ∑ U ∈ Ub a b, (-1:ℤ) ^ U.card * (Fz L U T z - Fz L U T (-z - (T.card : ℤ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    have e : -(-z - (T.card : ℤ)) - (T.card : ℤ) = z := by ring
    rw [e]; ring
  rw [h3] at h2
  linear_combination h2 - h1

/-! ### Parity tools -/

theorem odd_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ) :
    Odd (∏ i ∈ S, f i) ↔ ∀ i ∈ S, Odd (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Int.odd_mul, ih, Finset.forall_mem_insert]

theorem odd_congr {x y w : ℤ} (h : x - y = 2 * w) : Odd x ↔ Odd y := by
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r - w, by linarith⟩
  · rintro ⟨r, hr⟩; exact ⟨r + w, by linarith⟩

theorem neg_one_pow_cases (k : ℕ) : ((-1:ℤ)) ^ k = 1 ∨ ((-1:ℤ)) ^ k = -1 := by
  rcases Nat.even_or_odd k with h | h
  · left; exact Even.neg_one_pow h
  · right; exact Odd.neg_one_pow h

theorem sign_dvd2 (k : ℕ) (D : ℤ) (P : Prop) [Decidable P] (h : Odd D ↔ P) :
    (2:ℤ) ∣ (-1) ^ k * D - (if P then 1 else 0) := by
  by_cases hP : P
  · rw [if_pos hP]
    obtain ⟨m, hm⟩ := h.2 hP
    rcases neg_one_pow_cases k with hs | hs <;> rw [hs] <;> omega
  · rw [if_neg hP]
    have he : Even D := Int.not_odd_iff_even.1 (fun ho => hP (h.1 ho))
    obtain ⟨m, hm⟩ := he
    rcases neg_one_pow_cases k with hs | hs <;> rw [hs] <;> omega

theorem sign_dvd4 (k : ℕ) (D E : ℤ) (h : (4:ℤ) ∣ D - 2 * E) :
    (4:ℤ) ∣ (-1) ^ k * D - 2 * E := by
  rcases neg_one_pow_cases k with hs | hs <;> rw [hs] <;> omega

/-- The three states of a pair `(∏ (1 + f), ∏ (1 - f))` modulo 4. -/
def K0 (A B : ℤ) : Prop := ∃ c d : ℤ, A - B = 4 * c ∧ A = 2 * d + 1
def K1 (A B : ℤ) : Prop := ∃ c d e : ℤ, A + B - 2 = 4 * c ∧ A = 2 * d ∧ B = 2 * e
def K2 (A B : ℤ) : Prop := ∃ c d : ℤ, A = 4 * c ∧ B = 4 * d

theorem stepE0 {A B x : ℤ} (hx : Even x) (h : K0 A B) : K0 ((1 + x) * A) ((1 - x) * B) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨c, d, h1, h2⟩ := h
  have hB : B = 2 * d + 1 - 4 * c := by linarith
  subst hm; subst h2; subst hB
  exact ⟨(2 * d + 1) * m + c * (1 - 2 * m), d + 2 * d * m + m, by ring, by ring⟩

theorem stepE1 {A B x : ℤ} (hx : Even x) (h : K1 A B) : K1 ((1 + x) * A) ((1 - x) * B) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨c, d, e, h1, h2, h3⟩ := h
  subst hm; subst h2; subst h3
  exact ⟨c + m * (d - e), d * (1 + 2 * m), e * (1 - 2 * m), by linear_combination h1,
    by ring, by ring⟩

theorem step2 {A B : ℤ} (x : ℤ) (h : K2 A B) : K2 ((1 + x) * A) ((1 - x) * B) := by
  obtain ⟨c, d, h1, h2⟩ := h
  subst h1; subst h2
  exact ⟨(1 + x) * c, (1 - x) * d, by ring, by ring⟩

theorem stepO0 {A B x : ℤ} (hx : Odd x) (h : K0 A B) : K1 ((1 + x) * A) ((1 - x) * B) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨c, d, h1, h2⟩ := h
  have hB : B = 2 * d + 1 - 4 * c := by linarith
  subst hm; subst h2; subst hB
  exact ⟨d + 2 * m * c, (2 * d + 1) * (m + 1), -m * (2 * d + 1 - 4 * c), by ring, by ring,
    by ring⟩

theorem stepO1 {A B x : ℤ} (hx : Odd x) (h : K1 A B) : K2 ((1 + x) * A) ((1 - x) * B) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨c, d, e, h1, h2, h3⟩ := h
  subst hm; subst h2; subst h3
  exact ⟨d * (m + 1), -e * m, by ring, by ring⟩

theorem prod_inv {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ) :
    ((S.filter (fun i => Odd (f i))).card = 0 →
        K0 (∏ i ∈ S, (1 + f i)) (∏ i ∈ S, (1 - f i))) ∧
    ((S.filter (fun i => Odd (f i))).card = 1 →
        K1 (∏ i ∈ S, (1 + f i)) (∏ i ∈ S, (1 - f i))) ∧
    (2 ≤ (S.filter (fun i => Odd (f i))).card →
        K2 (∏ i ∈ S, (1 + f i)) (∏ i ∈ S, (1 - f i))) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ⟨0, 0, by simp, by simp⟩, fun h => ?_, fun h => ?_⟩
    · simp at h
    · simp at h
  | insert i S hi ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.filter_insert]
    by_cases hodd : Odd (f i)
    · rw [if_pos hodd]
      have hni : i ∉ S.filter (fun i => Odd (f i)) := fun h => hi (mem_filter.1 h).1
      rw [Finset.card_insert_of_notMem hni]
      refine ⟨fun h => by omega, fun h => ?_, fun h => ?_⟩
      · exact stepO0 hodd (ih0 (by omega))
      · rcases Nat.lt_or_ge (S.filter (fun i => Odd (f i))).card 2 with hlt | hge
        · exact stepO1 hodd (ih1 (by omega))
        · exact step2 (f i) (ih2 hge)
    · rw [if_neg hodd]
      have heven : Even (f i) := Int.not_odd_iff_even.1 hodd
      exact ⟨fun h => stepE0 heven (ih0 h), fun h => stepE1 heven (ih1 h),
        fun h => step2 (f i) (ih2 h)⟩

theorem prod_plus {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ) :
    (4:ℤ) ∣ (∏ i ∈ S, (1 + f i) + ∏ i ∈ S, (1 - f i))
      - 2 * (if (S.filter (fun i => Odd (f i))).card ≤ 1 then 1 else 0) := by
  obtain ⟨h0, h1, h2⟩ := prod_inv S f
  rcases Nat.lt_or_ge (S.filter (fun i => Odd (f i))).card 2 with hlt | hge
  · rw [if_pos (by omega)]
    rcases Nat.eq_zero_or_pos (S.filter (fun i => Odd (f i))).card with hz | hp
    · obtain ⟨c, d, e1, e2⟩ := h0 hz
      exact ⟨d - c, by linarith⟩
    · obtain ⟨c, d, e, e1, e2, e3⟩ := h1 (by omega)
      exact ⟨c, by linarith⟩
  · rw [if_neg (by omega)]
    obtain ⟨c, d, e1, e2⟩ := h2 hge
    exact ⟨c + d, by linarith⟩

theorem prod_minus {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ) :
    (4:ℤ) ∣ (∏ i ∈ S, (1 + f i) - ∏ i ∈ S, (1 - f i))
      - 2 * (if (S.filter (fun i => Odd (f i))).card = 1 then 1 else 0) := by
  obtain ⟨h0, h1, h2⟩ := prod_inv S f
  rcases Nat.lt_or_ge (S.filter (fun i => Odd (f i))).card 2 with hlt | hge
  · rcases Nat.eq_zero_or_pos (S.filter (fun i => Odd (f i))).card with hz | hp
    · rw [if_neg (by omega)]
      obtain ⟨c, d, e1, e2⟩ := h0 hz
      exact ⟨c, by linarith⟩
    · rw [if_pos (by omega)]
      obtain ⟨c, d, e, e1, e2, e3⟩ := h1 (by omega)
      exact ⟨c - e, by linarith⟩
  · rw [if_neg (by omega)]
    obtain ⟨c, d, e1, e2⟩ := h2 hge
    exact ⟨c - d, by linarith⟩

theorem card_odd_parity {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    (2:ℤ) ∣ (∑ i ∈ S, f i) - ((S.filter (fun i => Odd (f i))).card : ℤ) := by
  have h : ((S.filter (fun i => Odd (f i))).card : ℤ)
      = ∑ i ∈ S, (if Odd (f i) then (1:ℤ) else 0) := by
    rw [Finset.sum_boole]
  rw [h, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  by_cases ho : Odd (f i)
  · rw [if_pos ho]
    obtain ⟨m, hm⟩ := ho
    exact ⟨m, by linarith⟩
  · rw [if_neg ho]
    obtain ⟨m, hm⟩ := Int.not_odd_iff_even.1 ho
    exact ⟨m, by linarith⟩

end LSQ

namespace LSQ

open Finset OMA.S_arxiv_1912_11230

variable {n : ℕ}

/-- The number of symbols `s` with `c_s(U,T) + m` odd. -/
def Kc (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (m : ℤ) : ℕ :=
  (univ.filter (fun s : Fin n => Odd (cnt L U T s + m))).card

theorem Kc_le (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (m : ℤ) : Kc L U T m ≤ n := by
  unfold Kc
  have h := Finset.card_filter_le (univ : Finset (Fin n))
    (fun s : Fin n => Odd (cnt L U T s + m))
  rw [card_univ, Fintype.card_fin] at h
  exact h

theorem Kc_even (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) {m : ℤ} (hm : Even m) :
    Kc L U T m = Kc L U T 0 := by
  obtain ⟨r, hr⟩ := hm
  unfold Kc
  congr 1
  apply Finset.filter_congr
  intro s _
  exact odd_congr (w := r) (by rw [hr]; ring)

theorem Kc_odd (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) {m : ℤ} (hm : Odd m) :
    Kc L U T m + Kc L U T 0 = n := by
  obtain ⟨r, hr⟩ := hm
  unfold Kc
  have hfil : univ.filter (fun s : Fin n => Odd (cnt L U T s + m))
      = univ.filter (fun s : Fin n => ¬ Odd (cnt L U T s + 0)) := by
    apply Finset.filter_congr
    intro s _
    rw [Int.not_odd_iff_even]
    constructor
    · rintro ⟨w, hw⟩; exact ⟨w - r, by linarith⟩
    · rintro ⟨w, hw⟩; exact ⟨w + r, by linarith⟩
  rw [hfil]
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun s : Fin n => Odd (cnt L U T s + 0))
  rw [card_univ, Fintype.card_fin] at h
  omega

theorem Kc_eq_n_iff (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (m : ℤ) :
    Kc L U T m = n ↔ ∀ s : Fin n, Odd (cnt L U T s + m) := by
  unfold Kc
  constructor
  · intro h s
    have hfil : univ.filter (fun s : Fin n => Odd (cnt L U T s + m)) = univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [h, card_univ, Fintype.card_fin]
    have hs : s ∈ univ.filter (fun s : Fin n => Odd (cnt L U T s + m)) := by
      rw [hfil]; exact mem_univ s
    exact (mem_filter.1 hs).2
  · intro h
    rw [Finset.filter_true_of_mem (fun s _ => h s), card_univ, Fintype.card_fin]

theorem Kc_parity (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (m : ℤ) :
    (2:ℤ) ∣ ((U.card : ℤ) * T.card + n * m) - (Kc L U T m : ℤ) := by
  have hpar := card_odd_parity (univ : Finset (Fin n)) (fun s => cnt L U T s + m)
  have hsum : ∑ s : Fin n, (cnt L U T s + m) = (U.card : ℤ) * T.card + n * m := by
    rw [Finset.sum_add_distrib, cnt_sum, Finset.sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hsum] at hpar
  exact hpar

theorem Kc_compl {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (U T : Finset (Fin n))
    (m : ℤ) : Kc L U Tᶜ m = Kc L U T ((U.card : ℤ) + m) := by
  unfold Kc
  congr 1
  apply Finset.filter_congr
  intro s _
  rw [cnt_compl_cols hL.1]
  exact odd_congr (w := -cnt L U T s) (by ring)

theorem Fz_odd (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (z : ℤ) :
    Odd (Fz L U T z) ↔ Kc L U T z = n := by
  unfold Fz
  rw [odd_prod, Kc_eq_n_iff]
  constructor
  · intro h s
    have := h s (mem_univ s)
    rwa [add_comm] at this
  · intro h s _
    have := h s
    rwa [add_comm] at this

theorem odd_diff (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (hn : 0 < n) (z : ℤ) :
    Odd (Fz L U T z - Fz L U T (z - 1)) ↔ (Kc L U T 0 = 0 ∨ Kc L U T 0 = n) := by
  rw [Int.odd_sub, ← Int.not_odd_iff_even, Fz_odd, Fz_odd]
  have hle := Kc_le L U T 0
  rcases Int.even_or_odd z with hz | hz
  · have h1 := Kc_even L U T hz
    have h2 := Kc_odd L U T (m := z - 1) (by
      obtain ⟨r, hr⟩ := hz
      exact ⟨r - 1, by linarith⟩)
    constructor
    · intro h
      by_contra hcon
      have hkz : ¬ Kc L U T z = n := by omega
      have hk1 : Kc L U T (z - 1) = n := by
        by_contra h'
        exact hkz (h.2 h')
      omega
    · intro h
      constructor
      · intro h'; omega
      · intro h'; omega
  · have h1 := Kc_odd L U T hz
    have h2 := Kc_even L U T (m := z - 1) (by
      obtain ⟨r, hr⟩ := hz
      exact ⟨r, by linarith⟩)
    constructor
    · intro h
      by_contra hcon
      have hkz : ¬ Kc L U T z = n := by omega
      have hk1 : Kc L U T (z - 1) = n := by
        by_contra h'
        exact hkz (h.2 h')
      omega
    · intro h
      constructor
      · intro h'; omega
      · intro h'; omega

theorem Fz_plus (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (m : ℤ) :
    Fz L U T (1 + m) = ∏ s : Fin n, (1 + (cnt L U T s + m)) := by
  unfold Fz
  exact Finset.prod_congr rfl (fun s _ => by ring)

theorem Fz_minus (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (m : ℤ) :
    Fz L U T (-1 + m) = (-1) ^ n * ∏ s : Fin n, (1 - (cnt L U T s + m)) := by
  unfold Fz
  calc ∏ s : Fin n, (-1 + m + cnt L U T s)
      = ∏ s : Fin n, ((-1) * (1 - (cnt L U T s + m))) :=
        Finset.prod_congr rfl (fun s _ => by ring)
    _ = (∏ _s : Fin n, (-1:ℤ)) * ∏ s : Fin n, (1 - (cnt L U T s + m)) :=
        Finset.prod_mul_distrib
    _ = _ := by rw [Finset.prod_const, card_univ, Fintype.card_fin]

theorem pm_odd (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (hn : Odd n) (m : ℤ) :
    (4:ℤ) ∣ (Fz L U T (1 + m) - Fz L U T (-1 + m))
      - 2 * (if Kc L U T m ≤ 1 then 1 else 0) := by
  rw [Fz_plus, Fz_minus, Odd.neg_one_pow hn]
  have h := prod_plus (univ : Finset (Fin n)) (fun s => cnt L U T s + m)
  have e : (∏ s : Fin n, (1 + (cnt L U T s + m)) - (-1) * ∏ s : Fin n, (1 - (cnt L U T s + m)))
      = (∏ s : Fin n, (1 + (cnt L U T s + m)) + ∏ s : Fin n, (1 - (cnt L U T s + m))) := by
    ring
  rw [e]
  exact h

theorem pm_even (L : Fin n → Fin n → Fin n) (U T : Finset (Fin n)) (hn : Even n) (m : ℤ) :
    (4:ℤ) ∣ (Fz L U T (1 + m) - Fz L U T (-1 + m))
      - 2 * (if Kc L U T m = 1 then 1 else 0) := by
  rw [Fz_plus, Fz_minus, Even.neg_one_pow hn, one_mul]
  exact prod_minus (univ : Finset (Fin n)) (fun s => cnt L U T s + m)

/-! ### The coefficient `beta_T` modulo 4 -/

theorem R1 {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (hT : Odd T.card) :
    (4:ℤ) ∣ beta L a b T
      - 2 * ∑ U ∈ Ub a b, (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0) := by
  have hn : 0 < n := Fin.pos a
  obtain ⟨q, hq⟩ := hT
  have hτ : (T.card : ℤ) = 2 * (q:ℤ) + 1 := by exact_mod_cast hq
  have hm := master hL a b T (-(q:ℤ))
  have e1 : (2 * (-(q:ℤ)) + (T.card : ℤ)) = 1 := by rw [hτ]; ring
  have e2 : (-(-(q:ℤ)) - (T.card : ℤ)) = -(q:ℤ) - 1 := by rw [hτ]; ring
  rw [e1, e2, mul_one] at hm
  have h2 : (2:ℤ) ∣ ∑ U ∈ Ub a b,
      ((-1) ^ U.card * (Fz L U T (-(q:ℤ)) - Fz L U T (-(q:ℤ) - 1))
        - (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0)) := by
    apply Finset.dvd_sum
    intro U _
    exact sign_dvd2 _ _ _ (odd_diff L U T hn (-(q:ℤ)))
  rw [Finset.sum_sub_distrib] at h2
  obtain ⟨w, hw⟩ := h2
  exact ⟨w, by linarith⟩

theorem beta_even_form {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (m : ℤ) (hτ : (T.card : ℤ) = -2 * m) :
    beta L a b T
      = ∑ U ∈ Ub a b, (-1) ^ U.card * (Fz L U T (1 + m) - Fz L U T (-1 + m)) := by
  have hm := master hL a b T (1 + m)
  have e1 : (2 * (1 + m) + (T.card : ℤ)) = 2 := by rw [hτ]; ring
  have e2 : (-(1 + m) - (T.card : ℤ)) = -1 + m := by rw [hτ]; ring
  rw [e1, e2] at hm
  linarith

theorem R2 {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (hn : Even n) (hT : Even T.card) : (4:ℤ) ∣ beta L a b T := by
  obtain ⟨q, hq⟩ := hT
  have hq' : (T.card : ℤ) = (q:ℤ) + q := by exact_mod_cast hq
  have hτ : (T.card : ℤ) = -2 * (-(q:ℤ)) := by linarith
  rw [beta_even_form hL a b T (-(q:ℤ)) hτ]
  apply Finset.dvd_sum
  intro U _
  apply Dvd.dvd.mul_left
  have h := pm_even L U T hn (-(q:ℤ))
  have hpar := Kc_parity L U T (-(q:ℤ))
  obtain ⟨r, hr⟩ := hn
  have hn' : (n:ℤ) = (r:ℤ) + r := by exact_mod_cast hr
  obtain ⟨x, hx⟩ : ∃ x : ℤ, (U.card : ℤ) * T.card + n * (-(q:ℤ)) = 2 * x :=
    ⟨(U.card : ℤ) * q - r * q, by rw [hq', hn']; ring⟩
  rw [hx] at hpar
  have hK : Kc L U T (-(q:ℤ)) ≠ 1 := by
    intro hK1
    omega
  rw [if_neg hK] at h
  simpa using h

theorem R3 {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (hn : Odd n) (m : ℤ) (hτ : (T.card : ℤ) = -2 * m) :
    (4:ℤ) ∣ beta L a b T
      - 2 * ∑ U ∈ Ub a b, (if Kc L U T m ≤ 1 then (1:ℤ) else 0) := by
  rw [beta_even_form hL a b T m hτ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro U _
  exact sign_dvd4 _ _ _ (pm_odd L U T hn m)

theorem R4 {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (hn : Odd n) :
    (2:ℤ) ∣ beta L a b T - ∑ U ∈ Ub a b,
      ((if Kc L U T 0 ≤ 1 then (1:ℤ) else 0)
        + (if Kc L U T (-(T.card : ℤ)) ≤ 1 then (1:ℤ) else 0)) := by
  have hm1 := master hL a b T 1
  have hm2 := master hL a b T (-1)
  have e1 : (-(1:ℤ) - (T.card : ℤ)) = -1 + (-(T.card : ℤ)) := by ring
  have e2 : (-(-1:ℤ) - (T.card : ℤ)) = 1 + (-(T.card : ℤ)) := by ring
  rw [e1] at hm1
  rw [e2] at hm2
  have hG : ∀ U ∈ Ub a b, (4:ℤ) ∣ (-1) ^ U.card *
        ((Fz L U T 1 - Fz L U T (-1))
          + (Fz L U T (1 + (-(T.card : ℤ))) - Fz L U T (-1 + (-(T.card : ℤ)))))
      - 2 * ((if Kc L U T 0 ≤ 1 then (1:ℤ) else 0)
          + (if Kc L U T (-(T.card : ℤ)) ≤ 1 then (1:ℤ) else 0)) := by
    intro U _
    apply sign_dvd4
    have h0 := pm_odd L U T hn 0
    have h1 := pm_odd L U T hn (-(T.card : ℤ))
    simp only [add_zero] at h0
    obtain ⟨x, hx⟩ := h0
    obtain ⟨y, hy⟩ := h1
    exact ⟨x + y, by linarith⟩
  have hS := Finset.dvd_sum hG
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hS
  have hcomb : ∑ U ∈ Ub a b, (-1:ℤ) ^ U.card *
        ((Fz L U T 1 - Fz L U T (-1))
          + (Fz L U T (1 + (-(T.card : ℤ))) - Fz L U T (-1 + (-(T.card : ℤ)))))
      = (∑ U ∈ Ub a b, (-1:ℤ) ^ U.card * (Fz L U T 1 - Fz L U T (-1 + (-(T.card : ℤ)))))
        - ∑ U ∈ Ub a b, (-1:ℤ) ^ U.card * (Fz L U T (-1) - Fz L U T (1 + (-(T.card : ℤ)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    ring
  rw [hcomb] at hS
  obtain ⟨w, hw⟩ := hS
  have h4 : 4 * (beta L a b T - ∑ U ∈ Ub a b,
      ((if Kc L U T 0 ≤ 1 then (1:ℤ) else 0)
        + (if Kc L U T (-(T.card : ℤ)) ≤ 1 then (1:ℤ) else 0))) = 4 * (2 * w) := by
    linear_combination hm1 - hm2 + 2 * hw
  exact ⟨w, by linarith⟩

/-! ### Comparing `T` with its complement -/

theorem diff_even_odd {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (hn : Even n) (hT : Odd T.card) :
    (4:ℤ) ∣ beta L a b T - beta L a b Tᶜ := by
  have hc := card_compl_add T
  have hT' : Odd (Tᶜ).card := by
    obtain ⟨q, hq⟩ := hT
    obtain ⟨r, hr⟩ := hn
    exact ⟨r - q - 1, by omega⟩
  have h1 := R1 hL a b T hT
  have h2 := R1 hL a b Tᶜ hT'
  have hsum : ∑ U ∈ Ub a b, (if Kc L U Tᶜ 0 = 0 ∨ Kc L U Tᶜ 0 = n then (1:ℤ) else 0)
      = ∑ U ∈ Ub a b, (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0) := by
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [Kc_compl hL]
    have hk := Kc_le L U T 0
    rcases Int.even_or_odd ((U.card : ℤ) + 0) with hM | hM
    · rw [Kc_even L U T hM]
    · have hK := Kc_odd L U T hM
      split_ifs <;> omega
  rw [hsum] at h2
  omega

theorem diff_odd {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) (hn : Odd n) (hT : Odd T.card) :
    (4:ℤ) ∣ beta L a b T - beta L a b Tᶜ := by
  have hc := card_compl_add T
  obtain ⟨q, hq⟩ := hT
  obtain ⟨r, hr⟩ := hn
  have hnodd : Odd n := ⟨r, hr⟩
  have hτ : (T.card : ℤ) = 2 * (q:ℤ) + 1 := by exact_mod_cast hq
  obtain ⟨m', hm'⟩ : ∃ m' : ℤ, m' = (q:ℤ) - r := ⟨_, rfl⟩
  have hτ' : ((Tᶜ).card : ℤ) = -2 * m' := by
    rw [hm']; omega
  have h1 := R1 hL a b T ⟨q, hq⟩
  have h3 := R3 hL a b Tᶜ hnodd m' hτ'
  have h4 := R4 hL a b T hnodd
  have hpt : ∀ U ∈ Ub a b,
      (Even m' → (if Kc L U Tᶜ m' ≤ 1 then (1:ℤ) else 0)
          = (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0)) ∧
      (Odd m' → (if Kc L U Tᶜ m' ≤ 1 then (1:ℤ) else 0)
          + (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0)
          = (if Kc L U T 0 ≤ 1 then (1:ℤ) else 0)
            + (if Kc L U T (-(T.card : ℤ)) ≤ 1 then (1:ℤ) else 0)) := by
    intro U _
    have hk := Kc_le L U T 0
    have hk'' := Kc_odd L U T (m := -(T.card : ℤ)) ⟨-(q:ℤ) - 1, by rw [hτ]; ring⟩
    have hpar := Kc_parity L U T 0
    obtain ⟨x, hx⟩ : ∃ x : ℤ, (U.card : ℤ) * T.card + n * 0 = 2 * x + U.card :=
      ⟨(q:ℤ) * U.card, by rw [hτ]; ring⟩
    rw [hx] at hpar
    rw [Kc_compl hL]
    constructor
    · rintro ⟨v, hv⟩
      rcases Nat.even_or_odd U.card with hU | hU
      · obtain ⟨u, hu⟩ := hU
        have hUc : (U.card : ℤ) = (u:ℤ) + u := by exact_mod_cast hu
        have hM : Even ((U.card : ℤ) + m') := ⟨(u:ℤ) + v, by rw [hUc, hv]; ring⟩
        rw [Kc_even L U T hM]
        split_ifs <;> omega
      · obtain ⟨u, hu⟩ := hU
        have hUc : (U.card : ℤ) = 2 * (u:ℤ) + 1 := by exact_mod_cast hu
        have hM : Odd ((U.card : ℤ) + m') := ⟨(u:ℤ) + v, by rw [hUc, hv]; ring⟩
        have hK := Kc_odd L U T hM
        split_ifs <;> omega
    · rintro ⟨v, hv⟩
      rcases Nat.even_or_odd U.card with hU | hU
      · obtain ⟨u, hu⟩ := hU
        have hUc : (U.card : ℤ) = (u:ℤ) + u := by exact_mod_cast hu
        have hM : Odd ((U.card : ℤ) + m') := ⟨(u:ℤ) + v, by rw [hUc, hv]; ring⟩
        have hK := Kc_odd L U T hM
        split_ifs <;> omega
      · obtain ⟨u, hu⟩ := hU
        have hUc : (U.card : ℤ) = 2 * (u:ℤ) + 1 := by exact_mod_cast hu
        have hM : Even ((U.card : ℤ) + m') := ⟨(u:ℤ) + v + 1, by rw [hUc, hv]; ring⟩
        rw [Kc_even L U T hM]
        split_ifs <;> omega
  rcases Int.even_or_odd m' with hme | hmo
  · have hsum : ∑ U ∈ Ub a b, (if Kc L U Tᶜ m' ≤ 1 then (1:ℤ) else 0)
        = ∑ U ∈ Ub a b, (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0) :=
      Finset.sum_congr rfl (fun U hU => (hpt U hU).1 hme)
    rw [hsum] at h3
    omega
  · have hsum : (∑ U ∈ Ub a b, (if Kc L U Tᶜ m' ≤ 1 then (1:ℤ) else 0))
        + ∑ U ∈ Ub a b, (if Kc L U T 0 = 0 ∨ Kc L U T 0 = n then (1:ℤ) else 0)
        = ∑ U ∈ Ub a b, ((if Kc L U T 0 ≤ 1 then (1:ℤ) else 0)
            + (if Kc L U T (-(T.card : ℤ)) ≤ 1 then (1:ℤ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun U hU => (hpt U hU).2 hmo)
    omega

theorem beta_props {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b : Fin n)
    (T : Finset (Fin n)) :
    (2:ℤ) ∣ beta L a b T ∧ (4:ℤ) ∣ beta L a b T - beta L a b Tᶜ := by
  have hc := card_compl_add T
  rcases Nat.even_or_odd n with hn | hn
  · rcases Nat.even_or_odd T.card with hT | hT
    · have hT' : Even (Tᶜ).card := by
        obtain ⟨q, hq⟩ := hT
        obtain ⟨r, hr⟩ := hn
        exact ⟨r - q, by omega⟩
      have h1 := R2 hL a b T hn hT
      have h2 := R2 hL a b Tᶜ hn hT'
      constructor <;> omega
    · have h1 := R1 hL a b T hT
      have h3 := diff_even_odd hL a b T hn hT
      exact ⟨by omega, h3⟩
  · rcases Nat.even_or_odd T.card with hT | hT
    · have hT' : Odd (Tᶜ).card := by
        obtain ⟨q, hq⟩ := hT
        obtain ⟨r, hr⟩ := hn
        exact ⟨r - q, by omega⟩
      have h3 := diff_odd hL a b Tᶜ hn hT'
      rw [compl_compl] at h3
      have hev : (2:ℤ) ∣ beta L a b T := by
        obtain ⟨q, hq⟩ := hT
        have hq' : (T.card : ℤ) = (q:ℤ) + q := by exact_mod_cast hq
        have hτ : (T.card : ℤ) = -2 * (-(q:ℤ)) := by linarith
        have h5 := R3 hL a b T hn (-(q:ℤ)) hτ
        omega
      exact ⟨hev, by omega⟩
    · have h1 := R1 hL a b T hT
      have h3 := diff_odd hL a b T hn hT
      exact ⟨by omega, h3⟩

end LSQ

namespace LSQ

open Finset OMA.S_arxiv_1912_11230

variable {n : ℕ}

/-- `t_ac ≡ t_bc (mod 2)`: two entries of `t` in the same column have the same parity. -/
theorem t_parity_col {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b c : Fin n) :
    (2:ℤ) ∣ (t L a c : ℤ) - (t L b c : ℤ) := by
  rw [t_diff hL.1 a b c]
  apply Finset.dvd_sum
  intro T _
  exact Dvd.dvd.mul_left (beta_props hL a b T).1 _

/-- The mixed second difference of `t` is divisible by 4. -/
theorem D_dvd {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) (a b c d : Fin n) :
    (4:ℤ) ∣ ((t L a c : ℤ) - (t L b c : ℤ)) - ((t L a d : ℤ) - (t L b d : ℤ)) := by
  rw [t_diff hL.1 a b c, t_diff hL.1 a b d, ← Finset.sum_sub_distrib]
  rw [pair_sum c d (fun T => (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T
    - (if d ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T)]
  · apply Finset.dvd_sum
    intro T hT
    obtain ⟨_, hd, hc⟩ := mem_filter.1 hT
    obtain ⟨hp1, hp2⟩ := beta_props hL a b T
    show (4:ℤ) ∣ ((if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T
        - (if d ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T)
      + ((if c ∈ Tᶜ then (0:ℤ) else 1) * (-1) ^ (Tᶜ).card * beta L a b Tᶜ
        - (if d ∈ Tᶜ then (0:ℤ) else 1) * (-1) ^ (Tᶜ).card * beta L a b Tᶜ)
    rw [if_neg hc, if_pos hd, if_pos (mem_compl.2 hc),
      if_neg (fun h : d ∈ Tᶜ => (mem_compl.1 h) hd)]
    rcases neg_one_pow_cases T.card with h1 | h1 <;>
      rcases neg_one_pow_cases (Tᶜ).card with h2 | h2 <;> rw [h1, h2] <;> omega
  · intro T hT
    show (if c ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T
      - (if d ∈ T then (0:ℤ) else 1) * (-1) ^ T.card * beta L a b T = 0
    by_cases hc : c ∈ T
    · rw [if_pos hc, if_pos (hT.1 hc)]; ring
    · rw [if_neg hc, if_neg (fun h => hc (hT.2 h))]; ring

/-- Transposing the square and the cells. -/
theorem swap_trans (L : Fin n → Fin n → Fin n) (i j : Fin n) (F : Finset (Fin n × Fin n))
    (h : IsTransversalOfMinor (fun x y => L y x) i j F) :
    IsTransversalOfMinor L j i (F.image Prod.swap) := by
  obtain ⟨hcard, hav, hpw⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Prod.swap_injective, hcard]
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    exact ⟨(hav q hq).2, (hav q hq).1⟩
  · intro p hp p' hp' hne
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    obtain ⟨q', hq', rfl⟩ := mem_image.1 hp'
    have hqq : q ≠ q' := fun h => hne (by rw [h])
    obtain ⟨h1, h2, h3⟩ := hpw q hq q' hq' hqq
    exact ⟨h2, h1, h3⟩

theorem t_transpose (L : Fin n → Fin n → Fin n) (i j : Fin n) :
    t (fun x y => L y x) i j = t L j i := by
  unfold t
  apply Nat.card_eq_of_bijective
    (fun F : {F : Finset (Fin n × Fin n) // IsTransversalOfMinor (fun x y => L y x) i j F} =>
      (⟨F.1.image Prod.swap, swap_trans L i j F.1 F.2⟩ :
        {G : Finset (Fin n × Fin n) // IsTransversalOfMinor L j i G}))
  constructor
  · intro F F' h
    have h' : F.1.image Prod.swap = F'.1.image Prod.swap := congrArg Subtype.val h
    exact Subtype.ext (Finset.image_injective Prod.swap_injective h')
  · intro G
    refine ⟨⟨G.1.image Prod.swap, swap_trans (fun x y => L y x) j i G.1 G.2⟩, ?_⟩
    apply Subtype.ext
    show (G.1.image Prod.swap).image Prod.swap = G.1
    rw [Finset.image_image, Prod.swap_swap_eq, Finset.image_id]

theorem main_thm (n : ℕ) (L : Fin n → Fin n → Fin n) (hL : IsLatinSquare L) (a b c d : Fin n) :
    (t L a c + t L b c + t L a d + t L b d) % 4 = 0 := by
  have hD := D_dvd hL a b c d
  have h1 := t_parity_col hL a b c
  have hL' : IsLatinSquare (fun x y => L y x) := ⟨hL.2, hL.1⟩
  have h3 := t_parity_col hL' c d a
  rw [t_transpose L c a, t_transpose L d a] at h3
  omega

end LSQ

theorem OMA.solution : type_of% @OMA.S_arxiv_1912_11230.main :=
  fun n L hL a b c d => LSQ.main_thm n L hL a b c d

