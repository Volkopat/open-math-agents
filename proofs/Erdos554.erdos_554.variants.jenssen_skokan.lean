import FormalConjectures.ErdosProblems.«554»

/-!
Exact multicolour Ramsey numbers of odd cycles (Jenssen–Skokan 2021): for every `k ≥ 2`,
`multicolourGraphRamsey k (cycleGraph (2 * n + 1)) = n * 2 ^ k + 1` for all sufficiently large `n`.
-/

namespace JenssenSkokan

open SimpleGraph Finset Fintype Filter Topology

lemma cycleGraph_isContained_of_fun {V : Type*} {G : SimpleGraph V} {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (f : Fin r → V) (hinj : Function.Injective f)
    (hadj : ∀ i : Fin r, G.Adj (f i) (f (i + 1))) :
    (cycleGraph r).IsContained G := by
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro a b hab
  cases r with
  | zero => omega
  | succ r1 =>
    cases r1 with
    | zero => omega
    | succ r2 =>
      change a - b = 1 ∨ b - a = 1 at hab
      rcases hab with h | h
      · have ha : a = b + 1 := by
          calc a = (a - b) + b := (sub_add_cancel a b).symm
            _ = 1 + b := by rw [h]
            _ = b + 1 := add_comm 1 b
        subst ha
        exact (hadj b).symm
      · have hb : b = a + 1 := by
          calc b = (b - a) + a := (sub_add_cancel b a).symm
            _ = 1 + a := by rw [h]
            _ = a + 1 := add_comm 1 a
        subst hb
        exact hadj a
lemma exists_cycle_fun_of_isContained {V : Type*} {G : SimpleGraph V} {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (h : (cycleGraph r).IsContained G) :
    ∃ f : Fin r → V, Function.Injective f ∧ ∀ i : Fin r, G.Adj (f i) (f (i + 1)) := by
  obtain ⟨c⟩ := h
  refine ⟨c.toHom, c.injective', fun i => ?_⟩
  apply c.toHom.map_rel'
  cases r with
  | zero => omega
  | succ r1 =>
    cases r1 with
    | zero => omega
    | succ r2 =>
      change i - (i + 1) = 1 ∨ (i + 1) - i = 1
      right
      simp
lemma exists_colouring_avoiding_odd_cycle (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∃ C : TopEdgeLabeling (Fin (n * 2 ^ k)) (Fin k),
      ∀ c : Fin k, ¬ (cycleGraph (2 * n + 1)).IsContained (C.labelGraph c) := by
  classical
  let blk : Fin (n * 2 ^ k) → ℕ := fun v => v.val / n
  have hblk_lt : ∀ v : Fin (n * 2 ^ k), blk v < 2 ^ k := by
    intro v
    exact Nat.div_lt_of_lt_mul (by linarith [v.isLt])
  let colFn : Fin (n * 2 ^ k) → Fin (n * 2 ^ k) → Fin k := fun u v =>
    if h : blk u / 2 = blk v / 2 then ⟨0, by omega⟩
    else ⟨Nat.log 2 (blk u ^^^ blk v), by
      have hxor : blk u ^^^ blk v < 2 ^ k := Nat.xor_lt_two_pow (hblk_lt u) (hblk_lt v)
      exact Nat.log_lt_of_lt_pow (by
        intro h0
        have heq : blk u = blk v := Nat.xor_eq_zero_iff.mp h0
        exact h (by rw [heq])) hxor⟩
  have hsym : ∀ u v, colFn u v = colFn v u := by
    intro u v
    dsimp only [colFn]
    by_cases h : blk u / 2 = blk v / 2
    · rw [dif_pos h, dif_pos h.symm]
    · rw [dif_neg h, dif_neg (Ne.symm h)]
      congr 1
      rw [Nat.xor_comm]
  let C : TopEdgeLabeling (Fin (n * 2 ^ k)) (Fin k) :=
    EdgeLabeling.mk (fun u v _ => colFn u v) (fun u v _ => hsym v u)
  refine ⟨C, fun c hc => ?_⟩
  obtain ⟨f, hinj, hadj⟩ := exists_cycle_fun_of_isContained (by omega) hc
  have hcol_adj : ∀ i : Fin (2 * n + 1), colFn (f i) (f (i + 1)) = c := by
    intro i
    have h1 := hadj i
    rw [TopEdgeLabeling.labelGraph_adj] at h1
    obtain ⟨hne, hlbl⟩ := h1
    exact hlbl
  by_cases hc0 : c.val = 0
  ·
    have hsame : ∀ i : Fin (2 * n + 1), blk (f i) / 2 = blk (f (i + 1)) / 2 := by
      intro i
      have hci := hcol_adj i
      dsimp only [colFn] at hci
      by_contra hne
      rw [dif_neg hne] at hci
      have hlog0 : Nat.log 2 (blk (f i) ^^^ blk (f (i + 1))) = 0 := by
        have := congrArg Fin.val hci
        simpa [hc0] using this
      have hlt2 : blk (f i) ^^^ blk (f (i + 1)) < 2 := by
        by_contra hge
        have hge' : 2 ≤ blk (f i) ^^^ blk (f (i + 1)) := by omega
        have : 1 ≤ Nat.log 2 (blk (f i) ^^^ blk (f (i + 1))) :=
          Nat.le_log_of_pow_le (by omega) (by simpa using hge')
        omega
      have hdiv : blk (f i) / 2 = blk (f (i + 1)) / 2 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.testBit_div_two, Nat.testBit_div_two]
        have htb := Nat.testBit_xor (blk (f i)) (blk (f (i + 1))) (j + 1)
        have hlt_bit : (blk (f i) ^^^ blk (f (i + 1))).testBit (j + 1) = false := by
          apply Nat.testBit_lt_two_pow
          calc blk (f i) ^^^ blk (f (i + 1)) < 2 := hlt2
            _ = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [hlt_bit] at htb
        cases hb1 : (blk (f i)).testBit (j + 1) <;> cases hb2 : (blk (f (i + 1))).testBit (j + 1) <;>
          simp_all
      exact hne hdiv
    have hall : ∀ (t : ℕ) (ht : t < 2 * n + 1),
        blk (f ⟨t, ht⟩) / 2 = blk (f ⟨0, by omega⟩) / 2 := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hstep := hsame ⟨t, by omega⟩
        have hadd : (⟨t, by omega⟩ : Fin (2 * n + 1)) + 1 = ⟨t + 1, ht⟩ := by
          ext; simp [Fin.val_add]; omega
        rw [hadd] at hstep
        exact hstep.symm.trans hprev
    let q := blk (f ⟨0, by omega⟩) / 2
    let B : Finset (Fin (n * 2 ^ k)) := Finset.univ.filter (fun v => blk v / 2 = q)
    have hsub : Finset.univ.image f ⊆ B := by
      intro v hv
      rcases mem_image.mp hv with ⟨i, _, rfl⟩
      simp only [B, mem_filter, mem_univ, true_and]
      exact hall i.val i.isLt
    have hcard_img : (Finset.univ.image f).card = 2 * n + 1 := by
      rw [card_image_of_injective _ hinj, Finset.card_fin]
    have hcard_B : B.card ≤ 2 * n := by
      have hmaps : ∀ v ∈ B, v.val ∈ Finset.Ico (q * (2 * n)) (q * (2 * n) + 2 * n) := by
        intro v hv
        simp only [B, mem_filter, mem_univ, true_and] at hv
        simp only [Finset.mem_Ico]
        have h1 : blk v / 2 = q := hv
        have h2 : q * 2 ≤ blk v ∧ blk v < q * 2 + 2 := by omega
        have h3 : blk v * n ≤ v.val ∧ v.val < (blk v + 1) * n := by
          dsimp only [blk]
          exact ⟨Nat.div_mul_le_self v.val n, Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) (by omega)⟩
        constructor <;> nlinarith
      calc B.card
          = (B.image Fin.val).card := (card_image_of_injective _ Fin.val_injective).symm
        _ ≤ (Finset.Ico (q * (2 * n)) (q * (2 * n) + 2 * n)).card :=
            card_le_card (Finset.image_subset_iff.mpr hmaps)
        _ = 2 * n := by simp
    have hle := card_le_card hsub
    omega
  ·
    have hflip : ∀ i : Fin (2 * n + 1),
        (blk (f (i + 1))).testBit c.val = !(blk (f i)).testBit c.val := by
      intro i
      have hci := hcol_adj i
      dsimp only [colFn] at hci
      have hne : blk (f i) / 2 ≠ blk (f (i + 1)) / 2 := by
        intro h
        rw [dif_pos h] at hci
        exact hc0 (congrArg Fin.val hci).symm
      rw [dif_neg hne] at hci
      have hlog : Nat.log 2 (blk (f i) ^^^ blk (f (i + 1))) = c.val := congrArg Fin.val hci
      have hpos : 0 < blk (f i) ^^^ blk (f (i + 1)) := by
        by_contra h0
        have heq : blk (f i) = blk (f (i + 1)) := Nat.xor_eq_zero_iff.mp (by omega)
        exact hne (by rw [heq])
      have hbit : (blk (f i) ^^^ blk (f (i + 1))).testBit c.val = true := by
        rw [← hlog, Nat.testBit_eq_decide_div_mod_eq]
        set z := blk (f i) ^^^ blk (f (i + 1))
        have hlo : 2 ^ Nat.log 2 z ≤ z := Nat.pow_log_le_self 2 hpos.ne'
        have hhi : z < 2 ^ (Nat.log 2 z + 1) := Nat.lt_pow_succ_log_self (by omega) z
        have hpow_pos : 0 < 2 ^ Nat.log 2 z := Nat.pow_pos (by omega)
        have hdiv : z / 2 ^ Nat.log 2 z = 1 := by
          have h1 : 1 ≤ z / 2 ^ Nat.log 2 z := (Nat.le_div_iff_mul_le hpow_pos).mpr (by simpa using hlo)
          have h2 : z / 2 ^ Nat.log 2 z < 2 := (Nat.div_lt_iff_lt_mul hpow_pos).mpr (by
            simpa [Nat.pow_succ, mul_comm] using hhi)
          omega
        simp [hdiv]
      rw [Nat.testBit_xor] at hbit
      cases hb1 : (blk (f i)).testBit c.val <;> cases hb2 : (blk (f (i + 1))).testBit c.val <;>
        simp_all
    have halt : ∀ (t : ℕ) (ht : t < 2 * n + 1),
        (blk (f ⟨t, ht⟩)).testBit c.val =
          if t % 2 = 0 then (blk (f ⟨0, by omega⟩)).testBit c.val
          else !(blk (f ⟨0, by omega⟩)).testBit c.val := by
      intro t
      induction t with
      | zero => intro _; simp
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hstep := hflip ⟨t, by omega⟩
        have hadd : (⟨t, by omega⟩ : Fin (2 * n + 1)) + 1 = ⟨t + 1, ht⟩ := by
          ext
          rw [Fin.val_add]
          have h1 : (1 : Fin (2 * n + 1)).val = 1 := by
            rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
          rw [h1]
          exact Nat.mod_eq_of_lt ht
        rw [hadd] at hstep
        rw [hstep, hprev]
        by_cases hev : t % 2 = 0
        · have hodd : (t + 1) % 2 ≠ 0 := by omega
          simp [hev, hodd]
        · have hev2 : (t + 1) % 2 = 0 := by omega
          simp [hev, hev2]
    have h2n := halt (2 * n) (by omega)
    have hmod : (2 * n) % 2 = 0 := by omega
    rw [if_pos hmod] at h2n
    have hwrap := hflip ⟨2 * n, by omega⟩
    have hadd_wrap : (⟨2 * n, by omega⟩ : Fin (2 * n + 1)) + 1 = ⟨0, by omega⟩ := by
      ext
      rw [Fin.val_add]
      have h1 : (1 : Fin (2 * n + 1)).val = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.mod_self]
    rw [hadd_wrap, h2n] at hwrap
    cases h0 : (blk (f ⟨0, by omega⟩)).testBit c.val <;> rw [h0] at hwrap <;> simp at hwrap
lemma not_forces_odd_cycle_of_le (k n m : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hm : m ≤ n * 2 ^ k) :
    ¬ ∀ C : TopEdgeLabeling (Fin m) (Fin k),
      ∃ c, (cycleGraph (2 * n + 1)).IsContained (C.labelGraph c) := by
  intro hall
  obtain ⟨C, hC⟩ := exists_colouring_avoiding_odd_cycle k n hk hn
  let ι : Fin m ↪ Fin (n * 2 ^ k) := Fin.castLEEmb hm
  let C' : TopEdgeLabeling (Fin m) (Fin k) :=
    EdgeLabeling.mk (fun u v huv => C.get (ι u) (ι v) (ι.injective.ne huv))
      (fun u v huv => by
        change C ⟨s(ι v, ι u), _⟩ = C ⟨s(ι u, ι v), _⟩
        congr 1; exact Subtype.ext Sym2.eq_swap)
  obtain ⟨c, hc⟩ := hall C'
  apply hC c
  obtain ⟨f, hinj, hadj⟩ := exists_cycle_fun_of_isContained (by omega) hc
  refine cycleGraph_isContained_of_fun (by omega) (fun i => ι (f i)) (ι.injective.comp hinj) ?_
  intro i
  have h1 := hadj i
  rw [TopEdgeLabeling.labelGraph_adj] at h1 ⊢
  obtain ⟨hne, hlbl⟩ := h1
  exact ⟨ι.injective.ne hne, hlbl⟩
lemma exists_cycle_of_high_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm4 : 4 ≤ Fintype.card V)
    (hdeg : ∀ v : V, 3 * Fintype.card V < 4 * (G.neighborFinset v).card) :
    ∀ r : ℕ, 3 ≤ r → r ≤ Fintype.card V → (cycleGraph r).IsContained G := by
  classical
  have hsmall : ∀ r : ℕ, 3 ≤ r → 2 * r ≤ Fintype.card V + 2 → (cycleGraph r).IsContained G := by
    intro r hr hrm
    have : NeZero r := ⟨by omega⟩
    have hpath : ∀ t : ℕ, 1 ≤ t → t ≤ r - 1 →
        ∃ p : Fin t → V, Function.Injective p ∧
          ∀ (j : ℕ) (hj : j + 1 < t), G.Adj (p ⟨j, by omega⟩) (p ⟨j + 1, hj⟩) := by
      intro t ht htr
      induction t with
      | zero => omega
      | succ t ih =>
        by_cases ht0 : t = 0
        · subst ht0
          have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
          exact ⟨fun _ => Classical.arbitrary V, fun a b _ => Fin.ext (by omega),
            fun j hj => by omega⟩
        · obtain ⟨p, hp_inj, hp_adj⟩ := ih (by omega) (by omega)
          let used : Finset V := Finset.univ.image p
          have hused_card : used.card = t := by
            rw [card_image_of_injective _ hp_inj, Finset.card_fin]
          let last : V := p ⟨t - 1, by omega⟩
          have hcand : ((G.neighborFinset last) \ used).Nonempty := by
            rw [nonempty_iff_ne_empty]
            intro hemp
            have hle : (G.neighborFinset last).card ≤ used.card := by
              have hsub : G.neighborFinset last ⊆ used := sdiff_eq_empty_iff_subset.mp hemp
              exact card_le_card hsub
            have hd := hdeg last
            omega
          obtain ⟨nxt, hnxt⟩ := hcand
          rw [Finset.mem_sdiff, mem_neighborFinset] at hnxt
          let p' : Fin (t + 1) → V := fun i =>
            if hi : i.val < t then p ⟨i.val, hi⟩ else nxt
          refine ⟨p', ?_, ?_⟩
          · intro a b hab
            by_cases ha : a.val < t <;> by_cases hb : b.val < t
            · simp only [p', dif_pos ha, dif_pos hb] at hab
              have hval : a.val = b.val := congrArg (Fin.val : Fin t → ℕ) (hp_inj hab)
              exact Fin.ext hval
            · simp only [p', dif_pos ha, dif_neg hb] at hab
              exfalso
              exact hnxt.2 (hab ▸ Finset.mem_image_of_mem p (mem_univ _))
            · simp only [p', dif_neg ha, dif_pos hb] at hab
              exfalso
              exact hnxt.2 (hab.symm ▸ Finset.mem_image_of_mem p (mem_univ _))
            · ext; omega
          · intro j hj
            by_cases hj1 : j + 1 < t
            · simp only [p', dif_pos (by omega : j < t), dif_pos hj1]
              exact hp_adj j hj1
            · have hjeq : j = t - 1 := by omega
              simp only [p', dif_pos (by omega : j < t), dif_neg (by omega : ¬ j + 1 < t)]
              convert hnxt.1 using 1
              congr 1; ext; omega
    obtain ⟨p, hp_inj, hp_adj⟩ := hpath (r - 1) (by omega) (le_refl _)
    let used : Finset V := Finset.univ.image p
    let v0 : V := p ⟨0, by omega⟩
    let vlast : V := p ⟨r - 2, by omega⟩
    have hcommon : ((G.neighborFinset v0 ∩ G.neighborFinset vlast) \ used).Nonempty := by
      have h1 : (G.neighborFinset v0 ∩ G.neighborFinset vlast).card +
          (G.neighborFinset v0 ∪ G.neighborFinset vlast).card =
          (G.neighborFinset v0).card + (G.neighborFinset vlast).card :=
        Finset.card_inter_add_card_union _ _
      have h2 : (G.neighborFinset v0 ∪ G.neighborFinset vlast).card ≤ Fintype.card V :=
        card_le_univ _
      have h3 : (used.erase v0 |>.erase vlast).card ≤ r - 3 := by
        have huc : used.card = r - 1 := by
          rw [card_image_of_injective _ hp_inj, Finset.card_fin]
        have hv0 : v0 ∈ used := Finset.mem_image_of_mem p (mem_univ _)
        have hvl : vlast ∈ used.erase v0 := by
          rw [mem_erase]
          refine ⟨?_, Finset.mem_image_of_mem p (mem_univ _)⟩
          intro hEq
          have hval : (⟨r - 2, by omega⟩ : Fin (r - 1)).val = (⟨0, by omega⟩ : Fin (r - 1)).val :=
            congrArg Fin.val (hp_inj hEq)
          dsimp at hval
          omega
        rw [card_erase_of_mem hvl, card_erase_of_mem hv0, huc]
        omega
      have hsub : (G.neighborFinset v0 ∩ G.neighborFinset vlast) ∩ used ⊆
          (used.erase v0).erase vlast := by
        intro x hx
        simp only [mem_inter, mem_neighborFinset] at hx
        rw [mem_erase, mem_erase]
        refine ⟨?_, ?_, hx.2⟩
        · rintro rfl; exact G.ne_of_adj hx.1.2 rfl
        · rintro rfl; exact G.ne_of_adj hx.1.1 rfl
      have hcard_inter : ((G.neighborFinset v0 ∩ G.neighborFinset vlast) ∩ used).card ≤ r - 3 :=
        (card_le_card hsub).trans h3
      have hsdiff : ((G.neighborFinset v0 ∩ G.neighborFinset vlast) \ used).card +
          ((G.neighborFinset v0 ∩ G.neighborFinset vlast) ∩ used).card =
          (G.neighborFinset v0 ∩ G.neighborFinset vlast).card :=
        Finset.card_sdiff_add_card_inter _ _
      have hd0 := hdeg v0
      have hdl := hdeg vlast
      exact card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hcommon
    rw [Finset.mem_sdiff, mem_inter, mem_neighborFinset, mem_neighborFinset] at hw
    let f : Fin r → V := fun i => if hi : i.val < r - 1 then p ⟨i.val, hi⟩ else w
    refine cycleGraph_isContained_of_fun hr f ?_ ?_
    · intro a b hab
      by_cases ha : a.val < r - 1 <;> by_cases hb : b.val < r - 1
      · simp only [f, dif_pos ha, dif_pos hb] at hab
        exact Fin.ext (congrArg (Fin.val : Fin (r - 1) → ℕ) (hp_inj hab))
      · simp only [f, dif_pos ha, dif_neg hb] at hab
        exfalso; exact hw.2 (hab ▸ Finset.mem_image_of_mem p (mem_univ _))
      · simp only [f, dif_neg ha, dif_pos hb] at hab
        exfalso; exact hw.2 (hab.symm ▸ Finset.mem_image_of_mem p (mem_univ _))
      · ext; omega
    · intro i
      have h1r : (1 : Fin r).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      by_cases hi1 : i.val + 1 < r - 1
      · have hadd : (i + 1).val = i.val + 1 := by
          rw [Fin.val_add, h1r]; exact Nat.mod_eq_of_lt (by omega)
        simp only [f, dif_pos (by omega : i.val < r - 1), dif_pos (by omega : (i + 1).val < r - 1)]
        convert hp_adj i.val hi1 using 2
        ext; exact hadd
      · by_cases hi2 : i.val = r - 2
        · have hadd : (i + 1).val = r - 1 := by
            rw [Fin.val_add, hi2, h1r]
            have : r - 2 + 1 = r - 1 := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          simp only [f, dif_pos (by omega : i.val < r - 1), dif_neg (by omega : ¬ (i + 1).val < r - 1)]
          have heq : p ⟨i.val, by omega⟩ = vlast := by
            dsimp only [vlast]; congr 1; ext; omega
          rw [heq]
          exact hw.1.2
        · have hi3 : i.val = r - 1 := by omega
          have hadd : (i + 1).val = 0 := by
            rw [Fin.val_add, hi3, h1r]
            have : r - 1 + 1 = r := by omega
            rw [this, Nat.mod_self]
          simp only [f, dif_neg (by omega : ¬ i.val < r - 1), dif_pos (by omega : (i + 1).val < r - 1)]
          have heq : p ⟨(i + 1).val, by omega⟩ = v0 := by
            dsimp only [v0]; congr 1; ext; exact hadd
          rw [heq]
          exact hw.1.1.symm
  have hstep : ∀ r : ℕ, 3 ≤ r → Fintype.card V ≤ 2 * r → r < Fintype.card V →
      (cycleGraph r).IsContained G → (cycleGraph (r + 1)).IsContained G := by
    intro r hr h2r hrm hc
    have : NeZero r := ⟨by omega⟩
    obtain ⟨f, hf_inj, hf_adj⟩ := exists_cycle_fun_of_isContained hr hc
    let S : Finset V := Finset.univ.image f
    have hScard : S.card = r := by
      rw [card_image_of_injective _ hf_inj, Finset.card_fin]
    have hout : (Finset.univ \ S).Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro hemp
      have : Fintype.card V ≤ S.card := by
        have := sdiff_eq_empty_iff_subset.mp hemp
        simpa using card_le_card this
      omega
    obtain ⟨x, hx⟩ := hout
    rw [Finset.mem_sdiff] at hx
    have hxS : x ∉ S := hx.2
    have hNxS : r < 2 * (G.neighborFinset x ∩ S).card := by
      have hsub : G.neighborFinset x ⊆ (G.neighborFinset x ∩ S) ∪ ((Finset.univ \ S).erase x) := by
        intro y hy
        by_cases hyS : y ∈ S
        · exact mem_union_left _ (mem_inter.mpr ⟨hy, hyS⟩)
        · refine mem_union_right _ (mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨mem_univ _, hyS⟩⟩)
          rintro rfl
          exact G.ne_of_adj ((mem_neighborFinset G y y).mp hy) rfl
      have hle := card_le_card hsub
      have hle2 := hle.trans (card_union_le _ _)
      have herase : ((Finset.univ \ S).erase x).card = Fintype.card V - r - 1 := by
        rw [card_erase_of_mem (Finset.mem_sdiff.mpr ⟨mem_univ _, hxS⟩),
          Finset.card_sdiff_of_subset (subset_univ _), card_univ, hScard]
      have hd := hdeg x
      omega
    let A : Finset (Fin r) := Finset.univ.filter (fun i => G.Adj x (f i))
    let B : Finset (Fin r) := Finset.univ.filter (fun i => G.Adj x (f (i + 1)))
    have hAcard : A.card = (G.neighborFinset x ∩ S).card := by
      have himg : A.image f = G.neighborFinset x ∩ S := by
        ext v
        simp only [A, S, mem_image, mem_filter, mem_univ, true_and,
          mem_inter, mem_neighborFinset]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i, rfl⟩
        · rintro ⟨hv, i, rfl⟩; exact ⟨i, hv, rfl⟩
      rw [← himg, card_image_of_injective _ hf_inj]
    have hBcard : B.card = A.card := by
      let sh : Fin r ≃ Fin r := Equiv.addRight (1 : Fin r)
      have hBimg : B.image sh = A := by
        ext j
        simp only [B, A, sh, Equiv.coe_addRight, mem_image, mem_filter,
          mem_univ, true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact hi
        · intro hj; exact ⟨j - 1, by simpa using hj, by simp⟩
      rw [← hBimg, card_image_of_injective _ sh.injective]
    have hAB : (A ∩ B).Nonempty := by
      have hu := Finset.card_inter_add_card_union A B
      have hle : (A ∪ B).card ≤ r := by
        simpa using card_le_univ (A ∪ B)
      exact card_pos.mp (by omega)
    obtain ⟨i0, hi0⟩ := hAB
    rw [mem_inter, mem_filter, mem_filter] at hi0
    have hxi0 : G.Adj x (f i0) := hi0.1.2
    have hxi1 : G.Adj x (f (i0 + 1)) := hi0.2.2
    let g : Fin (r + 1) → V := fun j =>
      if hj : j.val < r then f (i0 + 1 + ⟨j.val, hj⟩) else x
    refine cycleGraph_isContained_of_fun (by omega) g ?_ ?_
    · intro a b hab
      by_cases ha : a.val < r <;> by_cases hb : b.val < r
      · simp only [g, dif_pos ha, dif_pos hb] at hab
        have heq := add_left_cancel (hf_inj hab)
        exact Fin.ext (congrArg (Fin.val : Fin r → ℕ) heq)
      · simp only [g, dif_pos ha, dif_neg hb] at hab
        exfalso; exact hxS (hab ▸ Finset.mem_image_of_mem f (mem_univ _))
      · simp only [g, dif_neg ha, dif_pos hb] at hab
        exfalso; exact hxS (hab.symm ▸ Finset.mem_image_of_mem f (mem_univ _))
      · ext; omega
    · intro j
      have h1r : (1 : Fin r).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      have h1r1 : (1 : Fin (r + 1)).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      by_cases hj1 : j.val + 1 < r
      · have hadd : (j + 1).val = j.val + 1 := by
          rw [Fin.val_add, h1r1]; exact Nat.mod_eq_of_lt (by omega)
        simp only [g, dif_pos (by omega : j.val < r), dif_pos (by omega : (j + 1).val < r)]
        have hstep_idx : i0 + 1 + ⟨(j + 1).val, by omega⟩ = (i0 + 1 + ⟨j.val, by omega⟩) + 1 := by
          have h1step : (⟨(j + 1).val, by omega⟩ : Fin r) = ⟨j.val, by omega⟩ + 1 := by
            ext
            rw [hadd, Fin.val_add, h1r]
            exact (Nat.mod_eq_of_lt (by omega)).symm
          rw [h1step, ← add_assoc]
        rw [hstep_idx]
        exact hf_adj _
      · by_cases hj2 : j.val = r - 1
        · have hadd : (j + 1).val = r := by
            rw [Fin.val_add, hj2, h1r1]
            have : r - 1 + 1 = r := by omega
            rw [this]; exact Nat.mod_eq_of_lt (by omega)
          simp only [g, dif_pos (by omega : j.val < r), dif_neg (by omega : ¬ (j + 1).val < r)]
          have hlast : i0 + 1 + ⟨j.val, by omega⟩ = i0 := by
            have hsum : (1 : Fin r) + ⟨j.val, by omega⟩ = 0 := by
              ext
              rw [Fin.val_add, hj2, h1r]
              have : 1 + (r - 1) = r := by omega
              simp [this]
            rw [add_assoc, hsum, add_zero]
          rw [hlast]
          exact hxi0.symm
        · have hj3 : j.val = r := by omega
          have hadd : (j + 1).val = 0 := by
            rw [Fin.val_add, hj3, h1r1, Nat.mod_self]
          simp only [g, dif_neg (by omega : ¬ j.val < r), dif_pos (by omega : (j + 1).val < r)]
          have hzero : (⟨(j + 1).val, by omega⟩ : Fin r) = 0 := by ext; exact hadd
          rw [hzero, add_zero]
          exact hxi1
  intro r hr hrm
  by_cases hle : 2 * r ≤ Fintype.card V + 2
  · exact hsmall r hr hle
  ·
    let r0 := Fintype.card V / 2 + 1
    have hr0_ge : 3 ≤ r0 := by omega
    have hr0_small : 2 * r0 ≤ Fintype.card V + 2 := by omega
    have h2r0 : Fintype.card V ≤ 2 * r0 := by omega
    have hbase : (cycleGraph r0).IsContained G := hsmall r0 hr0_ge hr0_small
    have hdiff : ∀ d : ℕ, r0 + d ≤ Fintype.card V → (cycleGraph (r0 + d)).IsContained G := by
      intro d
      induction d with
      | zero => intro _; simpa using hbase
      | succ d ih =>
        intro hd
        exact hstep (r0 + d) (by omega) (by omega) (by omega) (ih (by omega))
    have hreq : r = r0 + (r - r0) := by omega
    rw [hreq]
    exact hdiff (r - r0) (by omega)
def IsMatching {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, ¬ (v ∈ e₁ ∧ v ∈ e₂))
lemma two_mul_card_edges_le_matching_mul_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : ℕ)
    (hν : ∀ M : Finset (Sym2 V), IsMatching G M → M.card ≤ ν) :
    2 * G.edgeFinset.card ≤ 2 * ν * Fintype.card V := by
  classical
  let allM : Finset (Finset (Sym2 V)) := G.edgeFinset.powerset.filter (fun M => IsMatching G M)
  have hallM_ne : allM.Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    exact ⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _)⟩
  obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_max_image allM Finset.card hallM_ne
  have hM : IsMatching G M := (mem_filter.mp hM_mem).2
  have hm_le : M.card ≤ ν := hν M hM
  let S : Finset V := Finset.univ.filter (fun v => ∃ e ∈ M, v ∈ e)
  let I : Finset V := Finset.univ \ S
  have hM_not_diag : ∀ e ∈ M, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hM.1 e he)
  have hScard : S.card = 2 * M.card := by
    have hS_eq : S = M.biUnion (fun e => e.toFinset) := by
      ext v
      simp only [S, mem_filter, mem_univ, true_and, mem_biUnion,
        Sym2.mem_toFinset]
    rw [hS_eq, card_biUnion]
    · calc ∑ e ∈ M, e.toFinset.card
          = ∑ _e ∈ M, 2 := Finset.sum_congr rfl fun e he => Sym2.card_toFinset_of_not_isDiag e (hM_not_diag e he)
        _ = 2 * M.card := by simp [mul_comm]
    · intro e₁ he₁ e₂ he₂ hne
      change Disjoint e₁.toFinset e₂.toFinset
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact hM.2 e₁ he₁ e₂ he₂ hne v ⟨Sym2.mem_toFinset.mp hv1, Sym2.mem_toFinset.mp hv2⟩
  have hIcard : S.card + I.card = Fintype.card V := by
    have h1 := card_sdiff_add_card_eq_card (subset_univ S)
    rw [card_univ] at h1
    change I.card + S.card = Fintype.card V at h1
    omega
  have hno_I : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    intro u hu v hv huv
    have huS : u ∉ S := (Finset.mem_sdiff.mp hu).2
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have hnotmem : s(u, v) ∉ M := by
      intro hmem
      exact huS (mem_filter.mpr ⟨mem_univ _, s(u, v), hmem, Sym2.mem_mk_left u v⟩)
    let M' := insert s(u, v) M
    have hM' : IsMatching G M' := by
      refine ⟨?_, ?_⟩
      · intro e he
        rcases mem_insert.mp he with rfl | heM
        · exact huv
        · exact hM.1 e heM
      · intro e₁ he₁ e₂ he₂ hne x ⟨hx1, hx2⟩
        rcases mem_insert.mp he₁ with rfl | he1M <;>
        rcases mem_insert.mp he₂ with rfl | he2M
        · exact hne rfl
        · rcases Sym2.mem_iff.mp hx1 with rfl | rfl
          · exact huS (mem_filter.mpr ⟨mem_univ _, e₂, he2M, hx2⟩)
          · exact hvS (mem_filter.mpr ⟨mem_univ _, e₂, he2M, hx2⟩)
        · rcases Sym2.mem_iff.mp hx2 with rfl | rfl
          · exact huS (mem_filter.mpr ⟨mem_univ _, e₁, he1M, hx1⟩)
          · exact hvS (mem_filter.mpr ⟨mem_univ _, e₁, he1M, hx1⟩)
        · exact hM.2 e₁ he1M e₂ he2M hne x ⟨hx1, hx2⟩
    have hM'_in : M' ∈ allM := by
      refine mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hM'⟩
      intro e he; exact mem_edgeFinset.mpr (hM'.1 e he)
    have hle := hM_max M' hM'_in
    rw [Finset.card_insert_of_notMem hnotmem] at hle
    omega
  let E_SS : Finset (Sym2 V) := G.edgeFinset.filter (fun f => ∀ x ∈ f, x ∈ S)
  let E_e : Sym2 V → Finset (Sym2 V) := fun e =>
    G.edgeFinset.filter (fun f => (∃ a ∈ e, a ∈ f) ∧ (∃ w ∈ I, w ∈ f))
  have hcover : G.edgeFinset ⊆ E_SS ∪ M.biUnion E_e := by
    intro f hf
    induction f using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := mem_edgeFinset.mp hf
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
      · refine mem_union_left _ (mem_filter.mpr ⟨hf, fun x hx => ?_⟩)
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
      · obtain ⟨e, heM, hue⟩ := (mem_filter.mp hu).2
        refine mem_union_right _ (mem_biUnion.mpr ⟨e, heM, ?_⟩)
        exact mem_filter.mpr ⟨hf, ⟨u, hue, Sym2.mem_mk_left u v⟩,
          ⟨v, Finset.mem_sdiff.mpr ⟨mem_univ _, hv⟩, Sym2.mem_mk_right u v⟩⟩
      · obtain ⟨e, heM, hve⟩ := (mem_filter.mp hv).2
        refine mem_union_right _ (mem_biUnion.mpr ⟨e, heM, ?_⟩)
        exact mem_filter.mpr ⟨hf, ⟨v, hve, Sym2.mem_mk_right u v⟩,
          ⟨u, Finset.mem_sdiff.mpr ⟨mem_univ _, hu⟩, Sym2.mem_mk_left u v⟩⟩
      · exfalso
        exact hno_I u (Finset.mem_sdiff.mpr ⟨mem_univ _, hu⟩)
          v (Finset.mem_sdiff.mpr ⟨mem_univ _, hv⟩) huv
  have hE_SS : 2 * E_SS.card ≤ S.card * (S.card - 1) := by
    let D_SS : Finset (V × V) := S.offDiag.filter (fun p => G.Adj p.1 p.2)
    have hD_le : D_SS.card ≤ S.card * (S.card - 1) := by
      calc D_SS.card ≤ S.offDiag.card := card_filter_le _ _
        _ = S.card * S.card - S.card := S.offDiag_card
        _ = S.card * (S.card - 1) := by rw [Nat.mul_sub_one]
    have h2 : 2 * E_SS.card ≤ D_SS.card := by
      have hcard_sum : D_SS.card = ∑ f ∈ E_SS, (D_SS.filter (fun p => s(p.1, p.2) = f)).card := by
        rw [← card_biUnion]
        · congr 1
          ext ⟨u, v⟩
          simp only [D_SS, E_SS, mem_biUnion, mem_filter, mem_offDiag,
            mem_edgeFinset]
          constructor
          · rintro ⟨⟨hu, hv, _⟩, huv⟩
            refine ⟨s(u, v), ⟨huv, fun x hx => by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩,
              ⟨⟨hu, hv, G.ne_of_adj huv⟩, huv⟩, rfl⟩
          · rintro ⟨_, _, h1, _⟩; exact h1
        · intro f₁ _ f₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          exact hne ((mem_filter.mp hp1).2.symm.trans (mem_filter.mp hp2).2)
      rw [hcard_sum]
      calc 2 * E_SS.card = ∑ _f ∈ E_SS, 2 := by simp [mul_comm]
        _ ≤ ∑ f ∈ E_SS, (D_SS.filter (fun p => s(p.1, p.2) = f)).card := by
          apply sum_le_sum
          intro f hf
          induction f using Sym2.ind with
          | _ u v =>
            have h1 := mem_filter.mp hf
            have huv : G.Adj u v := mem_edgeFinset.mp h1.1
            have huS : u ∈ S := h1.2 u (Sym2.mem_mk_left u v)
            have hvS : v ∈ S := h1.2 v (Sym2.mem_mk_right u v)
            have hne : u ≠ v := G.ne_of_adj huv
            have hsub : ({(u, v), (v, u)} : Finset (V × V)) ⊆
                D_SS.filter (fun p => s(p.1, p.2) = s(u, v)) := by
              intro p hp
              rcases mem_insert.mp hp with rfl | hp'
              · exact mem_filter.mpr ⟨mem_filter.mpr
                  ⟨mem_offDiag.mpr ⟨huS, hvS, hne⟩, huv⟩, rfl⟩
              · rw [mem_singleton] at hp'; subst hp'
                exact mem_filter.mpr ⟨mem_filter.mpr
                  ⟨mem_offDiag.mpr ⟨hvS, huS, hne.symm⟩, huv.symm⟩, Sym2.eq_swap⟩
            have hpair : ({(u, v), (v, u)} : Finset (V × V)).card = 2 := by
              rw [card_pair]
              intro heq; exact hne (congrArg Prod.fst heq)
            exact hpair ▸ card_le_card hsub
    exact h2.trans hD_le
  have hEe : ∀ e ∈ M, (E_e e).card ≤ I.card + 1 := by
    intro e heM
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := hM.1 _ heM
      have huv_ne : u ≠ v := G.ne_of_adj huv
      let Au : Finset V := I.filter (fun w => G.Adj u w)
      let Av : Finset V := I.filter (fun w => G.Adj v w)
      have hsub : E_e s(u, v) ⊆ Au.image (fun w => s(u, w)) ∪ Av.image (fun w => s(v, w)) := by
        intro f hf
        have hf' := mem_filter.mp hf
        obtain ⟨a, hae, haf⟩ := hf'.2.1
        obtain ⟨w, hwI, hwf⟩ := hf'.2.2
        have haw : a ≠ w := by
          rintro rfl
          have haS : a ∈ S := mem_filter.mpr ⟨mem_univ _, s(u, v), heM, hae⟩
          exact (Finset.mem_sdiff.mp hwI).2 haS
        have hfeq : f = s(a, w) := by
          induction f using Sym2.ind with
          | _ x y =>
            rcases Sym2.mem_iff.mp haf with rfl | rfl <;>
            rcases Sym2.mem_iff.mp hwf with rfl | rfl
            · exact absurd rfl haw
            · rfl
            · exact Sym2.eq_swap
            · exact absurd rfl haw
        have hadj : G.Adj a w := by
          rw [hfeq] at hf'
          exact mem_edgeFinset.mp hf'.1
        rcases Sym2.mem_iff.mp hae with rfl | rfl
        · exact mem_union_left _ (mem_image.mpr ⟨w, mem_filter.mpr ⟨hwI, hadj⟩, hfeq.symm⟩)
        · exact mem_union_right _ (mem_image.mpr ⟨w, mem_filter.mpr ⟨hwI, hadj⟩, hfeq.symm⟩)
      have hcard_le : (E_e s(u, v)).card ≤ Au.card + Av.card :=
        (card_le_card hsub).trans ((card_union_le _ _).trans
          (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
      by_cases hAu : Au.Nonempty
      · by_cases hAv : Av.Nonempty
        ·
          obtain ⟨w1, hw1⟩ := hAu
          obtain ⟨w2, hw2⟩ := hAv
          have hall_eq : ∀ x ∈ Au, ∀ y ∈ Av, x = y := by
            intro x hx y hy
            by_contra hxy
            have hx' := mem_filter.mp hx
            have hy' := mem_filter.mp hy
            have hxS : x ∉ S := (Finset.mem_sdiff.mp hx'.1).2
            have hyS : y ∉ S := (Finset.mem_sdiff.mp hy'.1).2
            let M' := insert s(u, x) (insert s(v, y) (M.erase s(u, v)))
            have hM'_match : IsMatching G M' := by
              have hdisj_er : ∀ e' ∈ M.erase s(u, v), u ∉ e' ∧ v ∉ e' ∧ x ∉ e' ∧ y ∉ e' := by
                intro e' he'
                have he'M := Finset.mem_of_mem_erase he'
                have he'ne := Finset.ne_of_mem_erase he'
                refine ⟨fun hu' => hM.2 e' he'M s(u, v) heM he'ne u ⟨hu', Sym2.mem_mk_left u v⟩,
                  fun hv' => hM.2 e' he'M s(u, v) heM he'ne v ⟨hv', Sym2.mem_mk_right u v⟩,
                  fun hx' => hxS (mem_filter.mpr ⟨mem_univ _, e', he'M, hx'⟩),
                  fun hy' => hyS (mem_filter.mpr ⟨mem_univ _, e', he'M, hy'⟩)⟩
              have hux_ne_vy : ∀ z, ¬ (z ∈ s(u, x) ∧ z ∈ s(v, y)) := by
                intro z ⟨hz1, hz2⟩
                rcases Sym2.mem_iff.mp hz1 with h1 | h1 <;>
                rcases Sym2.mem_iff.mp hz2 with h2 | h2
                · exact huv_ne (h1.symm.trans h2)
                · exact hyS ((h2.symm.trans h1) ▸ mem_filter.mpr ⟨mem_univ _, s(u, v), heM, Sym2.mem_mk_left u v⟩)
                · exact hxS ((h1.symm.trans h2) ▸ mem_filter.mpr ⟨mem_univ _, s(u, v), heM, Sym2.mem_mk_right u v⟩)
                · exact hxy (h1.symm.trans h2)
              refine ⟨?_, ?_⟩
              · intro f hf
                rcases mem_insert.mp hf with rfl | hf1
                · exact hx'.2
                · rcases mem_insert.mp hf1 with rfl | hf2
                  · exact hy'.2
                  · exact hM.1 f (Finset.mem_of_mem_erase hf2)
              · intro e₁ he₁ e₂ he₂ hne z ⟨hz1, hz2⟩
                rcases mem_insert.mp he₁ with rfl | he1a
                · rcases mem_insert.mp he₂ with rfl | he2a
                  · exact hne rfl
                  · rcases mem_insert.mp he2a with rfl | he2b
                    · exact hux_ne_vy z ⟨hz1, hz2⟩
                    · rcases Sym2.mem_iff.mp hz1 with rfl | rfl
                      · exact (hdisj_er e₂ he2b).1 hz2
                      · exact (hdisj_er e₂ he2b).2.2.1 hz2
                · rcases mem_insert.mp he1a with rfl | he1b
                  · rcases mem_insert.mp he₂ with rfl | he2a
                    · exact hux_ne_vy z ⟨hz2, hz1⟩
                    · rcases mem_insert.mp he2a with rfl | he2b
                      · exact hne rfl
                      · rcases Sym2.mem_iff.mp hz1 with rfl | rfl
                        · exact (hdisj_er e₂ he2b).2.1 hz2
                        · exact (hdisj_er e₂ he2b).2.2.2 hz2
                  · rcases mem_insert.mp he₂ with rfl | he2a
                    · rcases Sym2.mem_iff.mp hz2 with rfl | rfl
                      · exact (hdisj_er e₁ he1b).1 hz1
                      · exact (hdisj_er e₁ he1b).2.2.1 hz1
                    · rcases mem_insert.mp he2a with rfl | he2b
                      · rcases Sym2.mem_iff.mp hz2 with rfl | rfl
                        · exact (hdisj_er e₁ he1b).2.1 hz1
                        · exact (hdisj_er e₁ he1b).2.2.2 hz1
                      · exact hM.2 e₁ (Finset.mem_of_mem_erase he1b) e₂ (Finset.mem_of_mem_erase he2b)
                          hne z ⟨hz1, hz2⟩
            have hM'_in : M' ∈ allM := by
              refine mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hM'_match⟩
              intro f hf; exact mem_edgeFinset.mpr (hM'_match.1 f hf)
            have hle := hM_max M' hM'_in
            have hnot1 : s(v, y) ∉ M.erase s(u, v) := by
              intro hmem
              exact hyS (mem_filter.mpr ⟨mem_univ _, s(v, y),
                Finset.mem_of_mem_erase hmem, Sym2.mem_mk_right v y⟩)
            have hnot2 : s(u, x) ∉ insert s(v, y) (M.erase s(u, v)) := by
              intro hmem
              rcases mem_insert.mp hmem with heq | hmem'
              · have : u ∈ s(v, y) := heq ▸ Sym2.mem_mk_left u x
                rcases Sym2.mem_iff.mp this with rfl | rfl
                · exact huv_ne rfl
                · exact hyS (mem_filter.mpr ⟨mem_univ _, s(u, v), heM, Sym2.mem_mk_left u v⟩)
              · exact hxS (mem_filter.mpr ⟨mem_univ _, s(u, x),
                  Finset.mem_of_mem_erase hmem', Sym2.mem_mk_right u x⟩)
            have hcard_M' : M'.card = M.card + 1 := by
              rw [Finset.card_insert_of_notMem hnot2, Finset.card_insert_of_notMem hnot1,
                card_erase_of_mem heM]
              have hpos : 1 ≤ M.card := card_pos.mpr ⟨_, heM⟩
              omega
            omega
          have hAu1 : Au.card ≤ 1 := card_le_one.mpr fun a ha b hb =>
            (hall_eq a ha w2 hw2).trans (hall_eq b hb w2 hw2).symm
          have hAv1 : Av.card ≤ 1 := card_le_one.mpr fun a ha b hb =>
            (hall_eq w1 hw1 a ha).symm.trans (hall_eq w1 hw1 b hb)
          have hIpos : 1 ≤ I.card := card_pos.mpr ⟨w1, (mem_filter.mp hw1).1⟩
          omega
        · rw [not_nonempty_iff_eq_empty] at hAv
          have : Au.card ≤ I.card := card_filter_le _ _
          rw [hAv, Finset.card_empty] at hcard_le
          omega
      · rw [not_nonempty_iff_eq_empty] at hAu
        have : Av.card ≤ I.card := card_filter_le _ _
        rw [hAu, Finset.card_empty] at hcard_le
        omega
  have htotal : G.edgeFinset.card ≤ E_SS.card + ∑ e ∈ M, (E_e e).card :=
    (card_le_card hcover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have hsum_Ee : ∑ e ∈ M, (E_e e).card ≤ M.card * (I.card + 1) := by
    calc ∑ e ∈ M, (E_e e).card
        ≤ ∑ _e ∈ M, (I.card + 1) := sum_le_sum hEe
      _ = M.card * (I.card + 1) := by simp
  have hfinal_M : 2 * G.edgeFinset.card ≤ 2 * M.card * Fintype.card V := by
    by_cases hM0 : M.card = 0
    · have hS0 : S.card = 0 := by omega
      have hESS0 : E_SS.card = 0 := by rw [hS0] at hE_SS; omega
      have hsum0 : ∑ e ∈ M, (E_e e).card = 0 := by
        rw [Finset.card_eq_zero.mp hM0]; simp
      omega
    · have hSpos : 1 ≤ S.card := by omega
      have h1 : 2 * G.edgeFinset.card ≤ S.card * (S.card - 1) + 2 * (M.card * (I.card + 1)) := by
        omega
      have h2 : S.card * (S.card - 1) + 2 * (M.card * (I.card + 1)) = 2 * M.card * Fintype.card V := by
        zify [hSpos]
        have hSc : (S.card : ℤ) = 2 * (M.card : ℤ) := by exact_mod_cast hScard
        have hIc : (S.card : ℤ) + (I.card : ℤ) = (Fintype.card V : ℤ) := by exact_mod_cast hIcard
        nlinarith
      omega
  exact hfinal_M.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hm_le))
abbrev Subcube (k : ℕ) := Fin k → Fin 3
def weight {k : ℕ} (τ : Subcube k) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => τ i = 2)).card
def subcubeSet {k : ℕ} (τ : Subcube k) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun c => ∀ i : Fin k, (τ i = 0 → c i = false) ∧ (τ i = 1 → c i = true))
def distinguishable {k : ℕ} (σ τ : Subcube k) : Prop :=
  ∃ i : Fin k, (σ i = 0 ∧ τ i = 1) ∨ (σ i = 1 ∧ τ i = 0)
instance {k : ℕ} : DecidableRel (@distinguishable k) := by
  intro σ τ; unfold distinguishable; infer_instance
def compatible {k : ℕ} (σ τ : Subcube k) : Prop :=
  distinguishable σ τ ∨ ∃ i : Fin k, σ i = 2 ∧ τ i = 2
instance {k : ℕ} : DecidableRel (@compatible k) := by
  intro σ τ; unfold compatible; infer_instance
lemma distinguishable_symm {k : ℕ} {σ τ : Subcube k} :
    distinguishable σ τ ↔ distinguishable τ σ := by
  constructor
  · rintro ⟨i, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩
    · exact ⟨i, Or.inr ⟨h1, h0⟩⟩
    · exact ⟨i, Or.inl ⟨h0, h1⟩⟩
  · rintro ⟨i, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩
    · exact ⟨i, Or.inr ⟨h1, h0⟩⟩
    · exact ⟨i, Or.inl ⟨h0, h1⟩⟩
lemma compatible_symm {k : ℕ} {σ τ : Subcube k} :
    compatible σ τ ↔ compatible τ σ := by
  constructor <;> rintro (h | ⟨i, h1, h2⟩)
  · exact Or.inl (distinguishable_symm.mp h)
  · exact Or.inr ⟨i, h2, h1⟩
  · exact Or.inl (distinguishable_symm.mp h)
  · exact Or.inr ⟨i, h2, h1⟩
lemma not_distinguishable_self {k : ℕ} (τ : Subcube k) : ¬ distinguishable τ τ := by
  rintro ⟨i, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩ <;> simp_all
lemma card_subcubeSet {k : ℕ} (τ : Subcube k) : (subcubeSet τ).card = 2 ^ weight τ := by
  classical
  let W := Finset.univ.filter (fun i : Fin k => τ i = 2)
  have hbij : (subcubeSet τ).card = Fintype.card (W → Bool) := by
    refine Finset.card_bij (fun c _ => fun i : W => c i.val) ?_ ?_ ?_
    · intro _ _; exact mem_univ _
    · intro c₁ hc₁ c₂ hc₂ heq
      have h1 := (mem_filter.mp hc₁).2
      have h2 := (mem_filter.mp hc₂).2
      funext i
      by_cases hi : τ i = 2
      · exact congrFun heq ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
      · have h01 : τ i = 0 ∨ τ i = 1 := by
          have := (τ i).isLt; omega
        rcases h01 with h0 | h1'
        · rw [(h1 i).1 h0, (h2 i).1 h0]
        · rw [(h1 i).2 h1', (h2 i).2 h1']
    · intro g _
      let c : Fin k → Bool := fun i =>
        if hi : τ i = 2 then g ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
        else decide (τ i = 1)
      refine ⟨c, mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩, ?_⟩
      · constructor
        · intro h0; simp [c, h0]
        · intro h1; simp [c, h1]
      · funext ⟨i, hi⟩
        have hi2 : τ i = 2 := (mem_filter.mp hi).2
        simp [c, hi2]
  rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rfl
lemma distinguishable_iff_disjoint_subcubeSet {k : ℕ} (σ τ : Subcube k) :
    distinguishable σ τ ↔ Disjoint (subcubeSet σ) (subcubeSet τ) := by
  rw [Finset.disjoint_left]
  constructor
  · rintro ⟨i, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩ c hcσ hcτ
    · have hc1 := ((mem_filter.mp hcσ).2 i).1 h0
      have hc2 := ((mem_filter.mp hcτ).2 i).2 h1
      simp [hc1] at hc2
    · have hc1 := ((mem_filter.mp hcσ).2 i).2 h1
      have hc2 := ((mem_filter.mp hcτ).2 i).1 h0
      simp [hc1] at hc2
  · intro hdisj
    by_contra hnd
    let c : Fin k → Bool := fun i =>
      if σ i = 1 ∨ τ i = 1 then true else false
    have hcσ : c ∈ subcubeSet σ := by
      refine mem_filter.mpr ⟨mem_univ _, fun i => ⟨?_, ?_⟩⟩
      · intro h0
        have hτ1 : τ i ≠ 1 := fun h1 => hnd ⟨i, Or.inl ⟨h0, h1⟩⟩
        simp [c, h0, hτ1]
      · intro h1; simp [c, h1]
    have hcτ : c ∈ subcubeSet τ := by
      refine mem_filter.mpr ⟨mem_univ _, fun i => ⟨?_, ?_⟩⟩
      · intro h0
        have hσ1 : σ i ≠ 1 := fun h1 => hnd ⟨i, Or.inr ⟨h1, h0⟩⟩
        simp [c, h0, hσ1]
      · intro h1; simp [c, h1]
    exact hdisj hcσ hcτ
lemma subcubeSet_subset_of_compat_weight_one {k : ℕ} {σ τ : Subcube k}
    (hnd : ¬ distinguishable σ τ) (hcomp : compatible σ τ) (hw : weight τ = 1) :
    subcubeSet τ ⊆ subcubeSet σ := by
  obtain ⟨j, hσj, hτj⟩ : ∃ j, σ j = 2 ∧ τ j = 2 := hcomp.resolve_left hnd
  intro c hc
  have hcτ := (mem_filter.mp hc).2
  refine mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩
  by_cases hij : i = j
  · subst hij; simp [hσj]
  · have hτne2 : τ i ≠ 2 := by
      intro hi2
      have hcard : 2 ≤ weight τ := by
        have hsub : ({i, j} : Finset (Fin k)) ⊆ Finset.univ.filter (fun t => τ t = 2) := by
          intro t ht
          rcases mem_insert.mp ht with rfl | ht'
          · exact mem_filter.mpr ⟨mem_univ _, hi2⟩
          · rw [mem_singleton] at ht'; subst ht'
            exact mem_filter.mpr ⟨mem_univ _, hτj⟩
        unfold weight
        simpa [card_pair hij] using card_le_card hsub
      omega
    have hτ01 : τ i = 0 ∨ τ i = 1 := by have := (τ i).isLt; omega
    constructor
    · intro hσ0
      rcases hτ01 with hτ0 | hτ1
      · exact (hcτ i).1 hτ0
      · exact absurd ⟨i, Or.inl ⟨hσ0, hτ1⟩⟩ hnd
    · intro hσ1
      rcases hτ01 with hτ0 | hτ1
      · exact absurd ⟨i, Or.inr ⟨hσ1, hτ0⟩⟩ hnd
      · exact (hcτ i).2 hτ1
def quadForm {k : ℕ} (x : Subcube k → ℝ) : ℝ :=
  (∑ τ : Subcube k, x τ) ^ 2
    - ∑ σ : Subcube k, ∑ τ : Subcube k, (if distinguishable σ τ then x σ * x τ else 0)
    - ∑ τ : Subcube k, (weight τ : ℝ) * x τ
def l1Sum {k : ℕ} (x : Subcube k → ℝ) : ℝ := ∑ τ : Subcube k, x τ
def l1Dist {k : ℕ} (x y : Subcube k → ℝ) : ℝ := ∑ τ : Subcube k, |x τ - y τ|
def InX {k : ℕ} (γ : ℝ) (x : Subcube k → ℝ) : Prop :=
  (∀ τ, 0 ≤ x τ) ∧
  quadForm x ≤ γ ∧
  (∀ τ, weight τ = 1 → x τ ≤ 1 + γ) ∧
  (∀ σ τ, ¬ compatible σ τ → x σ * x τ ≤ γ)
lemma InX_zero_weight_zero {k : ℕ} {x : Subcube k → ℝ} (hx : InX 0 x)
    {τ : Subcube k} (h0 : weight τ = 0) : x τ = 0 := by
  have hnc : ¬ compatible τ τ := by
    rintro (hd | ⟨i, hi, _⟩)
    · exact not_distinguishable_self τ hd
    · have hpos : 0 < weight τ :=
        card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
      omega
  have hle := hx.2.2.2 τ τ hnc
  have hsq : x τ ^ 2 ≤ 0 := by simpa [sq] using hle
  nlinarith [sq_nonneg (x τ)]
def IsBipartiteComponent {V : Type*} (G : SimpleGraph V) (C : Set V) : Prop :=
  ∃ col : V → Bool, ∀ u ∈ C, ∀ v ∈ C, G.Adj u v → col u ≠ col v
def NoLargeOddConnMatching {V : Type*} (G : SimpleGraph V) (M : ℝ) : Prop :=
  ∀ (C : G.ConnectedComponent), ¬ IsBipartiteComponent G C.supp →
    ∀ (m : Finset (Sym2 V)), IsMatching G m → (∀ e ∈ m, ∀ v ∈ e, v ∈ C.supp) →
      (2 * m.card : ℝ) < M
structure ProfilePartition {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (col : Fin k → SimpleGraph V) where
  assign : V → Subcube k
  bipartite_edge : ∀ i u v, (col i).Adj u v → assign u i ≠ 2 →
    (assign u i = 0 ∧ assign v i = 1) ∨ (assign u i = 1 ∧ assign v i = 0)
  nonbipartite_comp : ∀ i v, assign v i = 2 ↔
    ¬ IsBipartiteComponent (col i) ((col i).connectedComponentMk v).supp
lemma exists_profilePartition {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (col : Fin k → SimpleGraph V) :
    Nonempty (ProfilePartition G col) := by
  classical
  let bip : ∀ (i : Fin k) (C : (col i).ConnectedComponent), V → Bool := fun i C =>
    if h : IsBipartiteComponent (col i) C.supp then h.choose else fun _ => false
  let assign : V → Subcube k := fun v i =>
    let C := (col i).connectedComponentMk v
    if IsBipartiteComponent (col i) C.supp then
      if bip i C v then 1 else 0
    else 2
  refine ⟨⟨assign, ?_, ?_⟩⟩
  · intro i u v huv hu2
    have hcomp : (col i).connectedComponentMk u = (col i).connectedComponentMk v :=
      ConnectedComponent.eq.mpr (Adj.reachable huv)
    have hbip : IsBipartiteComponent (col i) ((col i).connectedComponentMk u).supp := by
      by_contra hnb
      apply hu2
      simp [assign, hnb]
    have hbip_v : IsBipartiteComponent (col i) ((col i).connectedComponentMk v).supp :=
      hcomp ▸ hbip
    have hspec := hbip.choose_spec
    have hne : bip i ((col i).connectedComponentMk u) u ≠
        bip i ((col i).connectedComponentMk u) v := by
      simp only [bip, dif_pos hbip]
      exact hspec u rfl v hcomp.symm huv
    simp only [assign, if_pos hbip, if_pos hbip_v, ← hcomp]
    cases hb1 : bip i ((col i).connectedComponentMk u) u <;>
    cases hb2 : bip i ((col i).connectedComponentMk u) v <;> simp_all
  · intro i v
    simp only [assign]
    split_ifs with h1 h2
    · constructor <;> intro h
      · exact absurd h (by decide)
      · exact absurd h1 h
    · constructor <;> intro h
      · exact absurd h (by decide)
      · exact absurd h1 h
    · exact ⟨fun _ => h1, fun _ => rfl⟩
def ProfilePartition.vec {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    {G : SimpleGraph V} {col : Fin k → SimpleGraph V} (P : ProfilePartition G col) :
    Subcube k → ℕ :=
  fun τ => (Finset.univ.filter (fun v => P.assign v = τ)).card
lemma ProfilePartition.sum_vec {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    {G : SimpleGraph V} {col : Fin k → SimpleGraph V} (P : ProfilePartition G col) :
    ∑ τ : Subcube k, P.vec τ = Fintype.card V := by
  classical
  simp only [ProfilePartition.vec]
  rw [← card_biUnion]
  · congr 1
    ext v
    simp
  · intro τ₁ _ τ₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    exact hne ((mem_filter.mp hv1).2.symm.trans (mem_filter.mp hv2).2)
set_option maxHeartbeats 600000 in
lemma profile_constraints {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : Fin k → SimpleGraph V) [∀ i, DecidableRel (col i).Adj]
    (hcover : ∀ u v, G.Adj u v → ∃ i, (col i).Adj u v)
    (hsub : ∀ i u v, (col i).Adj u v → G.Adj u v)
    (P : ProfilePartition G col)
    {C δ n : ℝ} (hC : 1 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 / δ < n)
    (hN : (Fintype.card V : ℝ) = C * n)
    (hdense : (1 - δ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2) ≤ G.edgeFinset.card)
    (hnomatch : ∀ i : Fin k, NoLargeOddConnMatching (col i) ((1 + δ) * n)) :
    let v : Subcube k → ℝ := fun τ => (P.vec τ : ℝ) / n
    quadForm v ≤ 3 * δ * k * C ^ 2 ∧
    (∀ τ, weight τ = 1 → v τ ≤ 1 + 2 * Real.sqrt δ * C) ∧
    (∀ σ τ, ¬ compatible σ τ → v σ * v τ ≤ 2 * δ * C ^ 2) := by
  classical
  have hn_pos : 0 < n := lt_trans (by positivity) hn
  have hN_pos : 0 < (Fintype.card V : ℝ) := by rw [hN]; positivity
  let E_bip : Finset (Sym2 V) :=
    G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ distinguishable (P.assign u) (P.assign v))
  let E_nb : Finset (Sym2 V) := G.edgeFinset \ E_bip
  have hE_split : G.edgeFinset.card = E_bip.card + E_nb.card := by
    have hsub_bip : E_bip ⊆ G.edgeFinset := filter_subset _ _
    have h1 := card_sdiff_add_card_eq_card hsub_bip
    change E_nb.card + E_bip.card = G.edgeFinset.card at h1
    omega
  have hEbip_le : (2 * E_bip.card : ℝ) ≤
      ∑ σ : Subcube k, ∑ τ : Subcube k,
        if distinguishable σ τ then (P.vec σ : ℝ) * (P.vec τ : ℝ) else 0 := by
    let D_bip : Finset (V × V) :=
      Finset.univ.filter (fun p : V × V => distinguishable (P.assign p.1) (P.assign p.2))
    have h2 : 2 * E_bip.card ≤ D_bip.card := by
      have hsum : ∑ e ∈ E_bip, (D_bip.filter (fun p => s(p.1, p.2) = e)).card ≤ D_bip.card := by
        rw [← card_biUnion]
        · exact card_le_card (biUnion_subset.mpr fun _ _ => filter_subset _ _)
        · intro e₁ _ e₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          exact hne ((mem_filter.mp hp1).2.symm.trans (mem_filter.mp hp2).2)
      calc 2 * E_bip.card = ∑ _e ∈ E_bip, 2 := by simp [mul_comm]
        _ ≤ ∑ e ∈ E_bip, (D_bip.filter (fun p => s(p.1, p.2) = e)).card := by
          apply sum_le_sum
          intro e he
          have he' := mem_filter.mp he
          obtain ⟨u, v, rfl, hdist⟩ := he'.2
          have hne : u ≠ v := fun h => by subst h; exact not_distinguishable_self _ hdist
          have hsub_p : ({(u, v), (v, u)} : Finset (V × V)) ⊆
              D_bip.filter (fun p => s(p.1, p.2) = s(u, v)) := by
            intro p hp
            rcases mem_insert.mp hp with rfl | hp'
            · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hdist⟩, rfl⟩
            · rw [mem_singleton] at hp'; subst hp'
              exact mem_filter.mpr ⟨mem_filter.mpr
                ⟨mem_univ _, distinguishable_symm.mp hdist⟩, Sym2.eq_swap⟩
          have hpair : ({(u, v), (v, u)} : Finset (V × V)).card = 2 := by
            rw [card_pair]; intro h; exact hne (congrArg Prod.fst h)
          exact hpair ▸ card_le_card hsub_p
        _ ≤ D_bip.card := hsum
    have hD_eq : (D_bip.card : ℝ) = ∑ σ : Subcube k, ∑ τ : Subcube k,
        if distinguishable σ τ then (P.vec σ : ℝ) * (P.vec τ : ℝ) else 0 := by
      have hD_nat : D_bip.card = ∑ σ : Subcube k, ∑ τ : Subcube k,
          if distinguishable σ τ then P.vec σ * P.vec τ else 0 := by
        have hpart : D_bip = Finset.univ.biUnion (fun p : Subcube k × Subcube k =>
            if distinguishable p.1 p.2 then
              (Finset.univ.filter (fun u => P.assign u = p.1)) ×ˢ
              (Finset.univ.filter (fun v => P.assign v = p.2))
            else ∅) := by
          ext ⟨u, v⟩
          simp only [D_bip, mem_filter, mem_univ, true_and, mem_biUnion,
            Prod.exists]
          constructor
          · intro hd
            refine ⟨P.assign u, P.assign v, ?_⟩
            rw [if_pos hd]
            simp
          · rintro ⟨σ, τ, hmem⟩
            by_cases hd : distinguishable σ τ
            · rw [if_pos hd, mem_product, mem_filter, mem_filter] at hmem
              rwa [hmem.1.2, hmem.2.2]
            · rw [if_neg hd] at hmem; exact absurd hmem (notMem_empty _)
        rw [hpart, card_biUnion]
        · rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
          split_ifs
          · simp [ProfilePartition.vec, card_product]
          · simp
        · intro ⟨σ₁, τ₁⟩ _ ⟨σ₂, τ₂⟩ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro ⟨u, v⟩ h1 h2
          dsimp only at h1 h2
          split_ifs at h1 h2 with hd1 hd2
          · simp only [mem_product, mem_filter, mem_univ, true_and] at h1 h2
            exact hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
          · exact absurd h2 (notMem_empty _)
          · exact absurd h1 (notMem_empty _)
          · exact absurd h1 (notMem_empty _)
      exact_mod_cast hD_nat
    rw [← hD_eq]
    exact_mod_cast h2
  have hEnb_sub : E_nb ⊆ Finset.univ.biUnion (fun i : Fin k =>
      (col i).edgeFinset.filter (fun e => ∀ v ∈ e, P.assign v i = 2)) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := mem_edgeFinset.mp he.1
      obtain ⟨i, hi⟩ := hcover u v huv
      refine mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_edgeFinset.mpr hi, ?_⟩⟩
      intro x hx
      have hu2 : P.assign u i = 2 := by
        by_contra hne2
        have hbip := P.bipartite_edge i u v hi hne2
        exact he.2 (mem_filter.mpr ⟨he.1, u, v, rfl, ⟨i, hbip⟩⟩)
      have hv2 : P.assign v i = 2 := by
        by_contra hne2
        have hbip := P.bipartite_edge i v u hi.symm hne2
        exact he.2 (mem_filter.mpr ⟨he.1, u, v, rfl,
          distinguishable_symm.mp ⟨i, hbip⟩⟩)
      rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
  have hcol_nb : ∀ i : Fin k,
      (2 * ((col i).edgeFinset.filter (fun e => ∀ v ∈ e, P.assign v i = 2)).card : ℝ) ≤
        ((1 + δ) * n) * ((Finset.univ.filter (fun v => P.assign v i = 2)).card : ℝ) := by
    intro i
    let E_i := (col i).edgeFinset.filter (fun e => ∀ v ∈ e, P.assign v i = 2)
    let V_i := Finset.univ.filter (fun v => P.assign v i = 2)
    let nbComps : Finset ((col i).ConnectedComponent) :=
      Finset.univ.filter (fun C => ¬ IsBipartiteComponent (col i) C.supp)
    have hVi_card : V_i.card = ∑ C ∈ nbComps, (Finset.univ.filter (fun v => (col i).connectedComponentMk v = C)).card := by
      rw [← card_biUnion]
      · congr 1
        ext v
        simp only [V_i, nbComps, mem_filter, mem_univ, true_and, mem_biUnion]
        rw [P.nonbipartite_comp i v]
        constructor
        · intro hnb; exact ⟨(col i).connectedComponentMk v, hnb, rfl⟩
        · rintro ⟨C, hC, rfl⟩; exact hC
      · intro C₁ _ C₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        exact hne ((mem_filter.mp hv1).2.symm.trans (mem_filter.mp hv2).2)
    have hEi_le : E_i.card ≤ ∑ C ∈ nbComps,
        (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)).card := by
      rw [← card_biUnion]
      · apply card_le_card
        intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have he' := mem_filter.mp he
          have huv : (col i).Adj u v := mem_edgeFinset.mp he'.1
          have hCu : ¬ IsBipartiteComponent (col i) ((col i).connectedComponentMk u).supp :=
            (P.nonbipartite_comp i u).mp (he'.2 u (Sym2.mem_mk_left u v))
          have hEq : (col i).connectedComponentMk v = (col i).connectedComponentMk u :=
            (ConnectedComponent.eq.mpr (Adj.reachable huv)).symm
          refine mem_biUnion.mpr ⟨(col i).connectedComponentMk u,
            mem_filter.mpr ⟨mem_univ _, hCu⟩, mem_filter.mpr ⟨he, ?_⟩⟩
          intro x hx
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · rfl
          · exact hEq
      · intro C₁ _ C₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e he1 he2
        induction e using Sym2.ind with
        | _ u v =>
          exact hne (((mem_filter.mp he1).2 u (Sym2.mem_mk_left u v)).symm.trans
            ((mem_filter.mp he2).2 u (Sym2.mem_mk_left u v)))
    have hcomp_bound : ∀ C ∈ nbComps,
        (2 * (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)).card : ℝ) ≤
          ((1 + δ) * n) * ((Finset.univ.filter (fun v => (col i).connectedComponentMk v = C)).card : ℝ) := by
      intro C hC
      have hCnb : ¬ IsBipartiteComponent (col i) C.supp := (mem_filter.mp hC).2
      let VC := {v : V // (col i).connectedComponentMk v = C}
      let GC : SimpleGraph VC := (col i).induce {v : V | (col i).connectedComponentMk v = C}
      let ν := Nat.floor (((1 + δ) * n) / 2)
      have hν_le : (2 * ν : ℝ) ≤ (1 + δ) * n := by
        have hfl := Nat.floor_le (show 0 ≤ ((1 + δ) * n) / 2 by positivity)
        linarith
      have hGC_match : ∀ M : Finset (Sym2 VC), IsMatching GC M → M.card ≤ ν := by
        intro M hM
        let M' : Finset (Sym2 V) := M.image (Sym2.map Subtype.val)
        have hM'_card : M'.card = M.card :=
          card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
        have hM'_match : IsMatching (col i) M' := by
          refine ⟨?_, ?_⟩
          · intro e he
            rcases mem_image.mp he with ⟨e0, he0, rfl⟩
            induction e0 using Sym2.ind with
            | _ a b => exact hM.1 _ he0
          · intro e₁ he₁ e₂ he₂ hne x ⟨hx1, hx2⟩
            rcases mem_image.mp he₁ with ⟨a₁, ha₁, rfl⟩
            rcases mem_image.mp he₂ with ⟨a₂, ha₂, rfl⟩
            have hne' : a₁ ≠ a₂ := fun h => hne (by rw [h])
            obtain ⟨y₁, hy₁, rfl⟩ := Sym2.mem_map.mp hx1
            obtain ⟨y₂, hy₂, heqy⟩ := Sym2.mem_map.mp hx2
            have hyeq : y₁ = y₂ := Subtype.ext heqy.symm
            exact hM.2 a₁ ha₁ a₂ ha₂ hne' y₁ ⟨hy₁, hyeq ▸ hy₂⟩
        have hM'_supp : ∀ e ∈ M', ∀ v ∈ e, v ∈ C.supp := by
          intro e he v hv
          rcases mem_image.mp he with ⟨e0, _, rfl⟩
          obtain ⟨y, _, rfl⟩ := Sym2.mem_map.mp hv
          exact y.property
        have hlt := hnomatch i C hCnb M' hM'_match hM'_supp
        rw [hM'_card] at hlt
        exact Nat.le_floor (by linarith)
      have hbound := two_mul_card_edges_le_matching_mul_card GC ν hGC_match
      have hE_le_GC : (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)).card ≤
          GC.edgeFinset.card := by
        have hinj : (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)) ⊆
            GC.edgeFinset.image (Sym2.map Subtype.val) := by
          intro e he
          induction e using Sym2.ind with
          | _ u v =>
            have h1 := mem_filter.mp he
            have huv : (col i).Adj u v := mem_edgeFinset.mp (mem_filter.mp h1.1).1
            have huC : (col i).connectedComponentMk u = C := h1.2 u (Sym2.mem_mk_left u v)
            have hvC : (col i).connectedComponentMk v = C := h1.2 v (Sym2.mem_mk_right u v)
            exact mem_image.mpr ⟨s(⟨u, huC⟩, ⟨v, hvC⟩), mem_edgeFinset.mpr huv, rfl⟩
        exact (card_le_card hinj).trans Finset.card_image_le
      have hcard_VC : Fintype.card VC =
          (Finset.univ.filter (fun v => (col i).connectedComponentMk v = C)).card := by
        simp [VC, Fintype.card_subtype]
      rw [hcard_VC] at hbound
      have hnat : 2 * (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)).card ≤
          2 * ν * (Finset.univ.filter (fun v => (col i).connectedComponentMk v = C)).card :=
        (Nat.mul_le_mul_left 2 hE_le_GC).trans hbound
      calc (2 * (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)).card : ℝ)
          ≤ (2 * ν : ℝ) * ((Finset.univ.filter (fun v => (col i).connectedComponentMk v = C)).card : ℝ) := by
            exact_mod_cast hnat
        _ ≤ ((1 + δ) * n) * _ := by gcongr
    calc (2 * E_i.card : ℝ)
        ≤ ∑ C ∈ nbComps, (2 * (E_i.filter (fun e => ∀ v ∈ e, (col i).connectedComponentMk v = C)).card : ℝ) := by
          rw [← mul_sum]; exact_mod_cast Nat.mul_le_mul_left 2 hEi_le
      _ ≤ ∑ C ∈ nbComps, ((1 + δ) * n) * ((Finset.univ.filter (fun v => (col i).connectedComponentMk v = C)).card : ℝ) :=
          sum_le_sum hcomp_bound
      _ = ((1 + δ) * n) * (V_i.card : ℝ) := by
          rw [← mul_sum, hVi_card, Nat.cast_sum]
  have hEnb_bound : (2 * E_nb.card : ℝ) ≤
      (1 + δ) * n * ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ) := by
    have hsum_V : ∑ i : Fin k, ((Finset.univ.filter (fun v => P.assign v i = 2)).card : ℝ) =
        ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ) := by
      have hnat : ∑ i : Fin k, (Finset.univ.filter (fun v => P.assign v i = 2)).card =
          ∑ τ : Subcube k, weight τ * P.vec τ := by
        calc ∑ i : Fin k, (Finset.univ.filter (fun v => P.assign v i = 2)).card
            = ∑ i : Fin k, ∑ v : V, if P.assign v i = 2 then 1 else 0 := by
              refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.card_filter]
          _ = ∑ v : V, ∑ i : Fin k, if P.assign v i = 2 then 1 else 0 := Finset.sum_comm
          _ = ∑ v : V, weight (P.assign v) := by
              refine Finset.sum_congr rfl fun v _ => ?_; rw [weight, Finset.card_filter]
          _ = ∑ τ : Subcube k, ∑ v ∈ Finset.univ.filter (fun v => P.assign v = τ), weight τ := by
              rw [← Finset.sum_fiberwise_of_maps_to (g := P.assign) (fun _ _ => mem_univ _)]
              refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun v hv => ?_
              rw [(mem_filter.mp hv).2]
          _ = ∑ τ : Subcube k, weight τ * P.vec τ := by
              simp [ProfilePartition.vec, mul_comm]
      exact_mod_cast hnat
    have hle1 : (2 * E_nb.card : ℝ) ≤
        ∑ i : Fin k, (2 * ((col i).edgeFinset.filter (fun e => ∀ v ∈ e, P.assign v i = 2)).card : ℝ) := by
      have hcard := (card_le_card hEnb_sub).trans card_biUnion_le
      rw [← mul_sum]
      exact_mod_cast Nat.mul_le_mul_left 2 hcard
    calc (2 * E_nb.card : ℝ)
        ≤ ∑ i : Fin k, ((1 + δ) * n) * ((Finset.univ.filter (fun v => P.assign v i = 2)).card : ℝ) :=
          hle1.trans (sum_le_sum fun i _ => hcol_nb i)
      _ = (1 + δ) * n * ∑ i : Fin k, ((Finset.univ.filter (fun v => P.assign v i = 2)).card : ℝ) := by
          rw [← mul_sum]
      _ = (1 + δ) * n * ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ) := by rw [hsum_V]
  have hsum_x : (∑ τ : Subcube k, (P.vec τ : ℝ)) = C * n := by
    rw [← hN]; exact_mod_cast P.sum_vec
  have hN_gt : 1 / δ < (Fintype.card V : ℝ) := by
    rw [hN]; nlinarith
  have h2G : (1 - 2 * δ) * (Fintype.card V : ℝ) ^ 2 ≤ 2 * (G.edgeFinset.card : ℝ) := by
    have h1 : (1 : ℝ) < δ * (Fintype.card V : ℝ) := (div_lt_iff₀ hδ0).mp hN_gt |>.trans_eq (mul_comm _ _)
    nlinarith
  have hc1 : quadForm (fun τ => (P.vec τ : ℝ) / n) ≤ 3 * δ * k * C ^ 2 := by
    have h2Enb_lo : (Fintype.card V : ℝ) ^ 2 - 2 * δ * (Fintype.card V : ℝ) ^ 2 -
        (∑ σ : Subcube k, ∑ τ : Subcube k,
          if distinguishable σ τ then (P.vec σ : ℝ) * (P.vec τ : ℝ) else 0) ≤
        2 * (E_nb.card : ℝ) := by
      have hsplit : (2 * G.edgeFinset.card : ℝ) = 2 * (E_bip.card : ℝ) + 2 * (E_nb.card : ℝ) := by
        rw [hE_split]; push_cast; ring
      linarith
    have hw_le_k : ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ) ≤ (k : ℝ) * (Fintype.card V : ℝ) := by
      calc ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ)
          ≤ ∑ τ : Subcube k, (k : ℝ) * (P.vec τ : ℝ) := by
            apply sum_le_sum; intro τ _
            have hwk : weight τ ≤ k := by
              simpa [weight] using card_filter_le Finset.univ (fun i : Fin k => τ i = 2)
            gcongr
        _ = (k : ℝ) * ∑ τ : Subcube k, (P.vec τ : ℝ) := by rw [← mul_sum]
        _ = (k : ℝ) * (Fintype.card V : ℝ) := by rw [hsum_x, hN]
    have hraw : (∑ τ : Subcube k, (P.vec τ : ℝ)) ^ 2 -
        (∑ σ : Subcube k, ∑ τ : Subcube k,
          if distinguishable σ τ then (P.vec σ : ℝ) * (P.vec τ : ℝ) else 0) -
        n * ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ) ≤
        2 * δ * (Fintype.card V : ℝ) ^ 2 + δ * n * ((k : ℝ) * (Fintype.card V : ℝ)) := by
      have hsq : (∑ τ : Subcube k, (P.vec τ : ℝ)) ^ 2 = (Fintype.card V : ℝ) ^ 2 := by
        rw [hsum_x, hN]
      have hmul : δ * n * ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ) ≤
          δ * n * ((k : ℝ) * (Fintype.card V : ℝ)) :=
        mul_le_mul_of_nonneg_left hw_le_k (mul_nonneg hδ0.le hn_pos.le)
      linarith [h2Enb_lo, hEnb_bound, hsq, hmul]
    have hq_eq : quadForm (fun τ => (P.vec τ : ℝ) / n) =
        ((∑ τ : Subcube k, (P.vec τ : ℝ)) ^ 2 -
          (∑ σ : Subcube k, ∑ τ : Subcube k,
            if distinguishable σ τ then (P.vec σ : ℝ) * (P.vec τ : ℝ) else 0) -
          n * ∑ τ : Subcube k, (weight τ : ℝ) * (P.vec τ : ℝ)) / n ^ 2 := by
      unfold quadForm
      rw [← sum_div, div_pow, sub_div, sub_div]
      congr 1
      · congr 1
        rw [sum_div]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [sum_div]
        refine Finset.sum_congr rfl fun τ _ => ?_
        split_ifs
        · ring
        · simp
      · rw [mul_sum, sum_div]
        refine Finset.sum_congr rfl fun τ _ => ?_
        field_simp
    rw [hq_eq, div_le_iff₀ (sq_pos_of_pos hn_pos)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hbound2 : 2 * δ * (Fintype.card V : ℝ) ^ 2 + δ * n * ((k : ℝ) * (Fintype.card V : ℝ)) ≤
        3 * δ * (k : ℝ) * C ^ 2 * n ^ 2 := by
      rw [hN]
      have h1 : 2 * C ^ 2 ≤ 2 * (k : ℝ) * C ^ 2 := by nlinarith
      have h2 : (k : ℝ) * C ≤ (k : ℝ) * C ^ 2 := by nlinarith
      have h3 : (2 * C ^ 2 + (k : ℝ) * C) ≤ 3 * (k : ℝ) * C ^ 2 := by linarith
      have h4 : δ * n ^ 2 * (2 * C ^ 2 + (k : ℝ) * C) ≤ δ * n ^ 2 * (3 * (k : ℝ) * C ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hδ0.le (sq_nonneg n))
      linarith
    exact hraw.trans hbound2
  have hc2 : ∀ τ, weight τ = 1 → (P.vec τ : ℝ) / n ≤ 1 + 2 * Real.sqrt δ * C := by
    intro τ hτ
    have hex : ∃ j : Fin k, τ j = 2 := by
      have hne : (Finset.univ.filter (fun i : Fin k => τ i = 2)).Nonempty :=
        card_pos.mp (by rw [← weight, hτ]; omega)
      obtain ⟨j, hj⟩ := hne
      exact ⟨j, (mem_filter.mp hj).2⟩
    obtain ⟨j, hj2⟩ := hex
    have huniq : ∀ i : Fin k, τ i = 2 → i = j := by
      intro i hi2
      by_contra hne
      have hsub2 : ({i, j} : Finset (Fin k)) ⊆ Finset.univ.filter (fun t => τ t = 2) := by
        intro t ht
        rcases mem_insert.mp ht with rfl | ht'
        · exact mem_filter.mpr ⟨mem_univ _, hi2⟩
        · rw [mem_singleton] at ht'; subst ht'
          exact mem_filter.mpr ⟨mem_univ _, hj2⟩
      have := card_le_card hsub2
      rw [card_pair hne] at this
      have : 2 ≤ weight τ := this
      omega
    let Vτ := Finset.univ.filter (fun v => P.assign v = τ)
    let Eτ := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ Vτ)
    have hmiss : (Vτ.card * (Vτ.card - 1) : ℝ) / 2 - δ * (Fintype.card V : ℝ) ^ 2 ≤ Eτ.card := by
      let nonE : Finset (Sym2 V) :=
        (⊤ : SimpleGraph V).edgeFinset \ G.edgeFinset
      let nonEτ : Finset (Sym2 V) := nonE.filter (fun e => ∀ v ∈ e, v ∈ Vτ)
      have htop_card : (⊤ : SimpleGraph V).edgeFinset.card =
          Fintype.card V * (Fintype.card V - 1) / 2 := by
        have h1 : 2 * (⊤ : SimpleGraph V).edgeFinset.card = Fintype.card V * (Fintype.card V - 1) := by
          have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (⊤ : SimpleGraph V)
          have hdeg_top : ∀ v : V, (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
            intro v
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            have heq : (⊤ : SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
              ext w; simp [ne_comm]
            rw [heq, card_erase_of_mem (mem_univ v), card_univ]
          simp only [hdeg_top, sum_const, card_univ, smul_eq_mul] at hsum
          omega
        omega
      have htopτ_card : ((⊤ : SimpleGraph V).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ Vτ)).card =
          Vτ.card * (Vτ.card - 1) / 2 := by
        let Gtopτ : SimpleGraph Vτ := ⊤
        have h1 : 2 * Gtopτ.edgeFinset.card = Vτ.card * (Vτ.card - 1) := by
          have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges Gtopτ
          have hdeg_top : ∀ v : Vτ, Gtopτ.degree v = Vτ.card - 1 := by
            intro v
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            have heq : Gtopτ.neighborFinset v = Finset.univ.erase v := by
              ext w; simp [Gtopτ, ne_comm]
            rw [heq, card_erase_of_mem (mem_univ v), card_univ, Fintype.card_coe]
          simp only [hdeg_top, sum_const, card_univ, smul_eq_mul, Fintype.card_coe] at hsum
          omega
        have hbij : ((⊤ : SimpleGraph V).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ Vτ)).card =
            Gtopτ.edgeFinset.card := by
          symm
          refine Finset.card_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
          · intro e he
            induction e using Sym2.ind with
            | _ a b =>
              have hab : a ≠ b := mem_edgeFinset.mp he
              refine mem_filter.mpr ⟨mem_edgeFinset.mpr (Subtype.val_injective.ne hab), ?_⟩
              intro x hx
              rcases Sym2.mem_iff.mp hx with rfl | rfl
              · exact a.property
              · exact b.property
          · intro e₁ _ e₂ _ heq
            exact Sym2.map.injective Subtype.val_injective heq
          · intro e he
            induction e using Sym2.ind with
            | _ u v =>
              have h1 := mem_filter.mp he
              have huv : u ≠ v := mem_edgeFinset.mp h1.1
              have hu : u ∈ Vτ := h1.2 u (Sym2.mem_mk_left u v)
              have hv : v ∈ Vτ := h1.2 v (Sym2.mem_mk_right u v)
              exact ⟨s(⟨u, hu⟩, ⟨v, hv⟩), mem_edgeFinset.mpr (fun h => huv (congrArg Subtype.val h)), rfl⟩
        rw [hbij]; omega
      have hpartτ : (⊤ : SimpleGraph V).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ Vτ) = Eτ ∪ nonEτ := by
        ext e
        simp only [Eτ, nonEτ, nonE, mem_union, mem_filter, Finset.mem_sdiff,
          mem_edgeFinset]
        constructor
        · intro ⟨hne, hall⟩
          by_cases hG : e ∈ G.edgeSet
          · exact Or.inl ⟨hG, hall⟩
          · exact Or.inr ⟨⟨hne, hG⟩, hall⟩
        · rintro (⟨hG, hall⟩ | ⟨⟨hne, _⟩, hall⟩)
          · exact ⟨by induction e using Sym2.ind with | _ a b => exact G.ne_of_adj hG, hall⟩
          · exact ⟨hne, hall⟩
      have hdisjτ : Disjoint Eτ nonEτ := by
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact (Finset.mem_sdiff.mp (mem_filter.mp he2).1).2 (mem_filter.mp he1).1
      have hcard_part : Vτ.card * (Vτ.card - 1) / 2 = Eτ.card + nonEτ.card := by
        rw [← htopτ_card, hpartτ, card_union_of_disjoint hdisjτ]
      have hnonE_le : (nonEτ.card : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 2 / 2 := by
        have h1 : nonEτ.card ≤ nonE.card := card_filter_le _ _
        have h2 : nonE.card + G.edgeFinset.card = (⊤ : SimpleGraph V).edgeFinset.card :=
          card_sdiff_add_card_eq_card (fun e he => mem_edgeFinset.mpr (by
            induction e using Sym2.ind with | _ a b => exact G.ne_of_adj (mem_edgeFinset.mp he)))
        have h2r : (nonE.card : ℝ) + (G.edgeFinset.card : ℝ) =
            (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
          have hdiv : 2 * (Fintype.card V * (Fintype.card V - 1) / 2) =
              Fintype.card V * (Fintype.card V - 1) := by
            have := Nat.even_mul_pred_self (Fintype.card V)
            exact Nat.mul_div_cancel' (even_iff_two_dvd.mp this)
          have hcast : ((Fintype.card V * (Fintype.card V - 1) / 2 : ℕ) : ℝ) =
              (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
            have hN1 : 1 ≤ Fintype.card V := by
              by_contra h0; simp [Nat.lt_one_iff.mp (not_le.mp h0)] at hN_pos
            have : (2 : ℝ) * ((Fintype.card V * (Fintype.card V - 1) / 2 : ℕ) : ℝ) =
                (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
              rw [← Nat.cast_ofNat, ← Nat.cast_mul, hdiv, Nat.cast_mul, Nat.cast_sub hN1, Nat.cast_one]
            linarith
          rw [← hcast, ← htop_card]
          exact_mod_cast h2
        have h1r : (nonEτ.card : ℝ) ≤ (nonE.card : ℝ) := by exact_mod_cast h1
        nlinarith
      have hdivτ : ((Vτ.card * (Vτ.card - 1) / 2 : ℕ) : ℝ) =
          (Vτ.card : ℝ) * ((Vτ.card : ℝ) - 1) / 2 := by
        by_cases h0 : Vτ.card = 0
        · simp [h0]
        · have hdiv := Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self Vτ.card))
          have : (2 : ℝ) * ((Vτ.card * (Vτ.card - 1) / 2 : ℕ) : ℝ) =
              (Vτ.card : ℝ) * ((Vτ.card : ℝ) - 1) := by
            rw [← Nat.cast_ofNat, ← Nat.cast_mul, hdiv, Nat.cast_mul,
              Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h0), Nat.cast_one]
          linarith
      have hpart_r : (Vτ.card : ℝ) * ((Vτ.card : ℝ) - 1) / 2 = (Eτ.card : ℝ) + (nonEτ.card : ℝ) := by
        rw [← hdivτ]; exact_mod_cast hcard_part
      nlinarith
    have hEτ_in_j : Eτ ⊆ (col j).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ Vτ) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have h1 := mem_filter.mp he
        have huv : G.Adj u v := mem_edgeFinset.mp h1.1
        have hu : P.assign u = τ := (mem_filter.mp (h1.2 u (Sym2.mem_mk_left u v))).2
        have hv : P.assign v = τ := (mem_filter.mp (h1.2 v (Sym2.mem_mk_right u v))).2
        obtain ⟨i, hi⟩ := hcover u v huv
        have hij : i = j := by
          apply huniq i
          by_contra hi2
          have hbip := P.bipartite_edge i u v hi (by rw [hu]; exact hi2)
          rw [hu, hv] at hbip
          rcases hbip with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> (rw [h0] at h1; exact absurd h1 (by decide))
        subst hij
        exact mem_filter.mpr ⟨mem_edgeFinset.mpr hi, h1.2⟩
    have hEτ_ub : (2 * Eτ.card : ℝ) ≤ ((1 + δ) * n) * (Vτ.card : ℝ) := by
      let Gτ : SimpleGraph Vτ := (col j).induce (Vτ : Set V)
      let nbComps : Finset ((col j).ConnectedComponent) :=
        Finset.univ.filter (fun C => ¬ IsBipartiteComponent (col j) C.supp)
      have hVτ_sum : Vτ.card = ∑ C ∈ nbComps,
          (Vτ.filter (fun v => (col j).connectedComponentMk v = C)).card := by
        rw [← card_biUnion]
        · congr 1
          ext v
          simp only [mem_biUnion, mem_filter, nbComps, mem_univ, true_and]
          constructor
          · intro hv
            have hv2 : P.assign v j = 2 := by
              rw [(mem_filter.mp hv).2]; exact hj2
            exact ⟨(col j).connectedComponentMk v, (P.nonbipartite_comp j v).mp hv2, hv, rfl⟩
          · rintro ⟨_, _, hv, _⟩; exact hv
        · intro C₁ _ C₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro v hv1 hv2
          exact hne ((mem_filter.mp hv1).2.symm.trans (mem_filter.mp hv2).2)
      have hEτ_sum : Eτ.card ≤ ∑ C ∈ nbComps,
          (Eτ.filter (fun e => ∀ v ∈ e, (col j).connectedComponentMk v = C)).card := by
        rw [← card_biUnion]
        · apply card_le_card
          intro e he
          induction e using Sym2.ind with
          | _ u v =>
            have h1 := mem_filter.mp (hEτ_in_j he)
            have huv : (col j).Adj u v := mem_edgeFinset.mp h1.1
            have hu2 : P.assign u j = 2 := by
              rw [(mem_filter.mp (h1.2 u (Sym2.mem_mk_left u v))).2]; exact hj2
            have hEq : (col j).connectedComponentMk v = (col j).connectedComponentMk u :=
              (ConnectedComponent.eq.mpr (Adj.reachable huv)).symm
            refine mem_biUnion.mpr ⟨(col j).connectedComponentMk u,
              mem_filter.mpr ⟨mem_univ _, (P.nonbipartite_comp j u).mp hu2⟩,
              mem_filter.mpr ⟨he, ?_⟩⟩
            intro x hx; rcases Sym2.mem_iff.mp hx with rfl | rfl
            · rfl
            · exact hEq
        · intro C₁ _ C₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro e he1 he2
          induction e using Sym2.ind with
          | _ u v =>
            exact hne (((mem_filter.mp he1).2 u (Sym2.mem_mk_left u v)).symm.trans
              ((mem_filter.mp he2).2 u (Sym2.mem_mk_left u v)))
      have hcomp_τ : ∀ C ∈ nbComps,
          (2 * (Eτ.filter (fun e => ∀ v ∈ e, (col j).connectedComponentMk v = C)).card : ℝ) ≤
            ((1 + δ) * n) * ((Vτ.filter (fun v => (col j).connectedComponentMk v = C)).card : ℝ) := by
        intro C hC
        have hCnb : ¬ IsBipartiteComponent (col j) C.supp := (mem_filter.mp hC).2
        let VC := {v : V // v ∈ Vτ ∧ (col j).connectedComponentMk v = C}
        let GC : SimpleGraph VC := (col j).induce {v : V | v ∈ Vτ ∧ (col j).connectedComponentMk v = C}
        let ν := Nat.floor (((1 + δ) * n) / 2)
        have hν_le : (2 * ν : ℝ) ≤ (1 + δ) * n := by
          have := Nat.floor_le (show 0 ≤ ((1 + δ) * n) / 2 by positivity); linarith
        have hGC_match : ∀ M : Finset (Sym2 VC), IsMatching GC M → M.card ≤ ν := by
          intro M hM
          let M' : Finset (Sym2 V) := M.image (Sym2.map Subtype.val)
          have hM'_card : M'.card = M.card :=
            card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
          have hM'_match : IsMatching (col j) M' := by
            refine ⟨?_, ?_⟩
            · intro e he
              rcases mem_image.mp he with ⟨e0, he0, rfl⟩
              induction e0 using Sym2.ind with | _ a b => exact hM.1 _ he0
            · intro e₁ he₁ e₂ he₂ hne x ⟨hx1, hx2⟩
              rcases mem_image.mp he₁ with ⟨a₁, ha₁, rfl⟩
              rcases mem_image.mp he₂ with ⟨a₂, ha₂, rfl⟩
              obtain ⟨y₁, hy₁, rfl⟩ := Sym2.mem_map.mp hx1
              obtain ⟨y₂, hy₂, heqy⟩ := Sym2.mem_map.mp hx2
              exact hM.2 a₁ ha₁ a₂ ha₂ (fun h => hne (by rw [h])) y₁ ⟨hy₁, Subtype.ext heqy.symm ▸ hy₂⟩
          have hM'_supp : ∀ e ∈ M', ∀ v ∈ e, v ∈ C.supp := by
            intro e he v hv
            rcases mem_image.mp he with ⟨e0, _, rfl⟩
            obtain ⟨y, _, rfl⟩ := Sym2.mem_map.mp hv
            exact y.property.2
          have hlt := hnomatch j C hCnb M' hM'_match hM'_supp
          rw [hM'_card] at hlt
          exact Nat.le_floor (by linarith)
        have hbound := two_mul_card_edges_le_matching_mul_card GC ν hGC_match
        have hE_le : (Eτ.filter (fun e => ∀ v ∈ e, (col j).connectedComponentMk v = C)).card ≤
            GC.edgeFinset.card := by
          have hinj : (Eτ.filter (fun e => ∀ v ∈ e, (col j).connectedComponentMk v = C)) ⊆
              GC.edgeFinset.image (Sym2.map Subtype.val) := by
            intro e he
            induction e using Sym2.ind with
            | _ u v =>
              have h1 := mem_filter.mp he
              have h2 := mem_filter.mp (hEτ_in_j h1.1)
              have huv : (col j).Adj u v := mem_edgeFinset.mp h2.1
              have hu : u ∈ Vτ ∧ (col j).connectedComponentMk u = C :=
                ⟨h2.2 u (Sym2.mem_mk_left u v), h1.2 u (Sym2.mem_mk_left u v)⟩
              have hv : v ∈ Vτ ∧ (col j).connectedComponentMk v = C :=
                ⟨h2.2 v (Sym2.mem_mk_right u v), h1.2 v (Sym2.mem_mk_right u v)⟩
              exact mem_image.mpr ⟨s(⟨u, hu⟩, ⟨v, hv⟩), mem_edgeFinset.mpr huv, rfl⟩
          exact (card_le_card hinj).trans Finset.card_image_le
        have hcard_VC : Fintype.card VC =
            (Vτ.filter (fun v => (col j).connectedComponentMk v = C)).card := by
          rw [Fintype.card_subtype]
          congr 1
          ext x
          simp only [mem_filter, mem_univ, true_and]
        rw [hcard_VC] at hbound
        have hnat := (Nat.mul_le_mul_left 2 hE_le).trans hbound
        calc (2 * (Eτ.filter (fun e => ∀ v ∈ e, (col j).connectedComponentMk v = C)).card : ℝ)
            ≤ (2 * ν : ℝ) * ((Vτ.filter (fun v => (col j).connectedComponentMk v = C)).card : ℝ) := by
              exact_mod_cast hnat
          _ ≤ ((1 + δ) * n) * _ := by gcongr
      calc (2 * Eτ.card : ℝ)
          ≤ ∑ C ∈ nbComps, (2 * (Eτ.filter (fun e => ∀ v ∈ e, (col j).connectedComponentMk v = C)).card : ℝ) := by
            rw [← mul_sum]; exact_mod_cast Nat.mul_le_mul_left 2 hEτ_sum
        _ ≤ ∑ C ∈ nbComps, ((1 + δ) * n) * ((Vτ.filter (fun v => (col j).connectedComponentMk v = C)).card : ℝ) :=
            sum_le_sum hcomp_τ
        _ = ((1 + δ) * n) * (Vτ.card : ℝ) := by
            rw [← mul_sum, hVτ_sum, Nat.cast_sum]
    set x : ℝ := (P.vec τ : ℝ)
    have hx_eq : x = (Vτ.card : ℝ) := rfl
    have hquad_x : x ^ 2 - (1 + δ) * n * x - x ≤ 2 * δ * (Fintype.card V : ℝ) ^ 2 := by
      rw [hx_eq]; linarith
    set vτ := x / n
    have h1n : 1 / n < δ := by
      rw [div_lt_iff₀ hn_pos]
      have := (div_lt_iff₀ hδ0).mp hn
      linarith
    have hquad_v : vτ ^ 2 - (1 + 2 * δ) * vτ ≤ 2 * δ * C ^ 2 := by
      have hv0 : 0 ≤ vτ := by positivity
      have hdiv : (x ^ 2 - (1 + δ) * n * x - x) / n ^ 2 ≤ 2 * δ * C ^ 2 := by
        rw [div_le_iff₀ (sq_pos_of_pos hn_pos)]
        calc x ^ 2 - (1 + δ) * n * x - x
            ≤ 2 * δ * (Fintype.card V : ℝ) ^ 2 := hquad_x
          _ = 2 * δ * C ^ 2 * n ^ 2 := by rw [hN]; ring
      have hlhs : (x ^ 2 - (1 + δ) * n * x - x) / n ^ 2 = vτ ^ 2 - (1 + δ + 1 / n) * vτ := by
        dsimp only [vτ]; field_simp; ring
      rw [hlhs] at hdiv
      nlinarith
    by_contra hgt
    have hgt' : 1 + 2 * Real.sqrt δ * C < vτ := lt_of_not_ge hgt
    have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
    have hsqδ : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
    by_cases hδ4 : 1 / 4 ≤ δ
    · have hs4 : (1 / 2 : ℝ) ≤ Real.sqrt δ := by
        have : (1 / 2 : ℝ) ^ 2 ≤ δ := by norm_num; linarith
        exact (Real.le_sqrt (by norm_num) hδ0.le).mpr this
      have hv_le_C : vτ ≤ C := by
        have hxN : x ≤ (Fintype.card V : ℝ) := by
          have hle_nat : P.vec τ ≤ Fintype.card V := by
            rw [← P.sum_vec]
            exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ τ)
          dsimp only [x]
          exact_mod_cast hle_nat
        rw [hN] at hxN
        exact (div_le_iff₀ hn_pos).mpr hxN
      nlinarith
    · have hδ4' : δ < 1 / 4 := lt_of_not_ge hδ4
      have hδ_lt_sδ : δ < Real.sqrt δ := by nlinarith only [hsqδ, hδ0, hδ4', hsδ]
      have h2δ_lt : 2 * δ < 2 * Real.sqrt δ * C := by nlinarith only [hδ_lt_sδ, hC, hsδ]
      have hpos1 : 0 < vτ - (1 + 2 * δ) := by linarith only [hgt', h2δ_lt]
      have hmul : (1 + 2 * Real.sqrt δ * C) * (2 * Real.sqrt δ * C - 2 * δ) <
          vτ ^ 2 - (1 + 2 * δ) * vτ := by
        have h1 : (1 + 2 * Real.sqrt δ * C) * (2 * Real.sqrt δ * C - 2 * δ) <
            vτ * (vτ - (1 + 2 * δ)) :=
          mul_lt_mul'' hgt' (by linarith only [hgt']) (by positivity) (by linarith only [h2δ_lt])
        linarith only [h1, show vτ * (vτ - (1 + 2 * δ)) = vτ ^ 2 - (1 + 2 * δ) * vτ by ring]
      have hA : 0 < 2 * δ * (C ^ 2 - 1) := mul_pos (by positivity) (by nlinarith only [hC])
      have hB : 0 < 2 * Real.sqrt δ * C * (1 - 2 * δ) :=
        mul_pos (by positivity) (by linarith only [hδ4'])
      have hident : (1 + 2 * Real.sqrt δ * C) * (2 * Real.sqrt δ * C - 2 * δ) - 2 * δ * C ^ 2 =
          2 * δ * (C ^ 2 - 1) + 2 * Real.sqrt δ * C * (1 - 2 * δ) := by
        linear_combination 4 * C ^ 2 * hsqδ
      linarith only [hquad_v, hmul, hA, hB, hident]
  have hc3 : ∀ σ τ, ¬ compatible σ τ → ((P.vec σ : ℝ) / n) * ((P.vec τ : ℝ) / n) ≤ 2 * δ * C ^ 2 := by
    intro σ τ hnc
    let Vσ := Finset.univ.filter (fun v => P.assign v = σ)
    let Vτ := Finset.univ.filter (fun v => P.assign v = τ)
    have hno_edge : ∀ u ∈ Vσ, ∀ v ∈ Vτ, ¬ G.Adj u v := by
      intro u hu v hv huv
      have huσ : P.assign u = σ := (mem_filter.mp hu).2
      have hvτ : P.assign v = τ := (mem_filter.mp hv).2
      obtain ⟨i, hi⟩ := hcover u v huv
      by_cases hσ2 : σ i = 2
      · have hτ2 : τ i = 2 := by
          by_contra hne2
          have hbip := P.bipartite_edge i v u hi.symm (by rw [hvτ]; exact hne2)
          rw [huσ] at hbip
          rcases hbip with ⟨_, h1⟩ | ⟨_, h0⟩
          · rw [hσ2] at h1; exact absurd h1 (by decide)
          · rw [hσ2] at h0; exact absurd h0 (by decide)
        exact hnc (Or.inr ⟨i, hσ2, hτ2⟩)
      · have hbip := P.bipartite_edge i u v hi (by rw [huσ]; exact hσ2)
        rw [huσ, hvτ] at hbip
        exact hnc (Or.inl ⟨i, hbip⟩)
    let nonD : Finset (V × V) :=
      Finset.univ.offDiag.filter (fun p => ¬ G.Adj p.1 p.2)
    have hnonD_le : (nonD.card : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
      have htot : nonD.card + ((Finset.univ : Finset V).offDiag.filter (fun p : V × V => G.Adj p.1 p.2)).card =
          (Finset.univ : Finset V).offDiag.card := by
        simpa [nonD, add_comm] using card_filter_add_card_filter_not
          (s := (Finset.univ : Finset V).offDiag) (p := fun p : V × V => G.Adj p.1 p.2)
      have hG_dir : ((Finset.univ : Finset V).offDiag.filter (fun p : V × V => G.Adj p.1 p.2)).card =
          2 * G.edgeFinset.card := by
        have hsum : ((Finset.univ : Finset V).offDiag.filter (fun p : V × V => G.Adj p.1 p.2)).card =
            ∑ u : V, (G.neighborFinset u).card := by
          rw [← Finset.card_sigma]
          refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
          · intro ⟨u, v⟩ hp
            simp only [mem_filter, mem_offDiag, mem_univ, true_and] at hp
            exact Finset.mem_sigma.mpr ⟨mem_univ _, (mem_neighborFinset G u v).mpr hp.2⟩
          · intro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ h
            cases h; rfl
          · intro ⟨u, v⟩ h
            simp only [Finset.mem_sigma, mem_univ, true_and, mem_neighborFinset] at h
            exact ⟨(u, v), mem_filter.mpr ⟨mem_offDiag.mpr
              ⟨mem_univ _, mem_univ _, G.ne_of_adj h⟩, h⟩, rfl⟩
        rw [hsum]
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using G.sum_degrees_eq_twice_card_edges
      have hoff : (Finset.univ : Finset V).offDiag.card = Fintype.card V * (Fintype.card V - 1) := by
        rw [offDiag_card, card_univ, Nat.mul_sub_one]
      have hN1 : 1 ≤ Fintype.card V := by
        by_contra h0; simp [Nat.lt_one_iff.mp (not_le.mp h0)] at hN_pos
      have htot_r : (nonD.card : ℝ) + 2 * (G.edgeFinset.card : ℝ) =
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        have hnat : nonD.card + 2 * G.edgeFinset.card = Fintype.card V * (Fintype.card V - 1) := by
          rw [← hG_dir]; exact htot.trans hoff
        have hcast : ((nonD.card + 2 * G.edgeFinset.card : ℕ) : ℝ) =
            ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_sub hN1, Nat.cast_one] at hcast
        exact hcast
      nlinarith
    by_cases hστ : σ = τ
    · subst hστ
      have hsub_off : Vσ.offDiag ⊆ nonD := by
        intro ⟨u, v⟩ hp
        simp only [mem_offDiag] at hp
        exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _, mem_univ _, hp.2.2⟩,
          hno_edge u hp.1 v hp.2.1⟩
      have hle : (Vσ.card * (Vσ.card - 1) : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
        have h1 : Vσ.offDiag.card ≤ nonD.card := card_le_card hsub_off
        rw [offDiag_card] at h1
        have h2 : (Vσ.card : ℝ) * ((Vσ.card : ℝ) - 1) ≤ (nonD.card : ℝ) := by
          by_cases h0 : Vσ.card = 0
          · simp [h0]
          · have hpos : 1 ≤ Vσ.card := Nat.one_le_iff_ne_zero.mpr h0
            have : Vσ.card * Vσ.card - Vσ.card = Vσ.card * (Vσ.card - 1) := by rw [Nat.mul_sub_one]
            rw [this] at h1
            have h1r : ((Vσ.card * (Vσ.card - 1) : ℕ) : ℝ) ≤ (nonD.card : ℝ) := by exact_mod_cast h1
            rwa [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one] at h1r
        exact h2.trans hnonD_le
      have hVσ_le_N : (Vσ.card : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast card_le_univ Vσ
      have h1_lt : (1 : ℝ) < δ * (Fintype.card V : ℝ) := by
        have := (div_lt_iff₀ hδ0).mp hN_gt; linarith
      have hsq : (Vσ.card : ℝ) * (Vσ.card : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) ^ 2 := by nlinarith
      rw [div_mul_div_comm, ← sq n, div_le_iff₀ (sq_pos_of_pos hn_pos)]
      calc (P.vec σ : ℝ) * (P.vec σ : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) ^ 2 := hsq
        _ = 2 * δ * C ^ 2 * n ^ 2 := by rw [hN]; ring
    ·
      have hsub_prod : Vσ ×ˢ Vτ ⊆ nonD := by
        intro ⟨u, v⟩ hp
        rw [mem_product] at hp
        have hne : u ≠ v := by
          rintro rfl
          exact hστ ((mem_filter.mp hp.1).2.symm.trans (mem_filter.mp hp.2).2)
        exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _, mem_univ _, hne⟩,
          hno_edge u hp.1 v hp.2⟩
      have hle : (Vσ.card : ℝ) * (Vτ.card : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
        have h1 : Vσ.card * Vτ.card ≤ nonD.card := by
          rw [← card_product]; exact card_le_card hsub_prod
        exact (by exact_mod_cast h1 : (Vσ.card : ℝ) * (Vτ.card : ℝ) ≤ nonD.card).trans hnonD_le
      rw [div_mul_div_comm, ← sq n, div_le_iff₀ (sq_pos_of_pos hn_pos)]
      calc (P.vec σ : ℝ) * (P.vec τ : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 2 := hle
        _ ≤ 2 * δ * (Fintype.card V : ℝ) ^ 2 := by nlinarith
        _ = 2 * δ * C ^ 2 * n ^ 2 := by rw [hN]; ring
  exact ⟨hc1, hc2, hc3⟩

def IsDistinguishableSet {k : ℕ} (D : Finset (Subcube k)) : Prop :=
  (∀ τ ∈ D, 1 ≤ weight τ) ∧ (∀ σ ∈ D, ∀ τ ∈ D, σ ≠ τ → distinguishable σ τ)
def IsDecomposition {k : ℕ} (D : Finset (Subcube k)) : Prop :=
  IsDistinguishableSet D ∧ D.biUnion subcubeSet = Finset.univ
lemma sum_two_pow_weight_le {k : ℕ} {D : Finset (Subcube k)} (hD : IsDistinguishableSet D) :
    ∑ τ ∈ D, 2 ^ weight τ ≤ 2 ^ k ∧
      (∑ τ ∈ D, 2 ^ weight τ = 2 ^ k ↔ IsDecomposition D) := by
  have hdisj : (D : Set (Subcube k)).PairwiseDisjoint subcubeSet := by
    intro σ hσ τ hτ hne
    change Disjoint (subcubeSet σ) (subcubeSet τ)
    exact (distinguishable_iff_disjoint_subcubeSet σ τ).mp (hD.2 σ hσ τ hτ hne)
  have hcard_biU : (D.biUnion subcubeSet).card = ∑ τ ∈ D, 2 ^ weight τ := by
    rw [card_biUnion hdisj]
    exact Finset.sum_congr rfl fun τ _ => card_subcubeSet τ
  have huniv : (Finset.univ : Finset (Fin k → Bool)).card = 2 ^ k := by
    simp [Fintype.card_fun, Fintype.card_bool]
  refine ⟨?_, ?_⟩
  · rw [← hcard_biU, ← huniv]
    exact card_le_univ _
  · constructor
    · intro heq
      refine ⟨hD, Finset.eq_univ_of_card _ ?_⟩
      rw [hcard_biU, heq, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    · intro hdec
      rw [← hcard_biU, hdec.2, huniv]
def InO {k : ℕ} (x : Subcube k → ℝ) : Prop :=
  ∃ D : Finset (Subcube k), IsDecomposition D ∧
    (∀ τ ∈ D, (weight τ = 1 ∧ x τ = 1) ∨ (weight τ = 2 ∧ x τ = 2)) ∧
    (∀ τ, τ ∉ D → x τ = 0)
def InOStar {k : ℕ} (x : Subcube k → ℝ) : Prop :=
  ∃ D : Finset (Subcube k), IsDecomposition D ∧
    (∀ τ ∈ D, weight τ = 1 ∧ x τ = 1) ∧
    (∀ τ, τ ∉ D → x τ = 0)
lemma quadForm_eq_indistinguishable {k : ℕ} (x : Subcube k → ℝ) :
    quadForm x =
      ∑ σ : Subcube k, ∑ τ : Subcube k, (if distinguishable σ τ then 0 else x σ * x τ)
        - ∑ τ : Subcube k, (weight τ : ℝ) * x τ := by
  unfold quadForm
  have hsq : (∑ τ : Subcube k, x τ) ^ 2 =
      ∑ σ : Subcube k, ∑ τ : Subcube k, x σ * x τ := by
    rw [sq, sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_sum]
  rw [hsq, ← sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs <;> ring
lemma InO_mem_InX_and_sum {k : ℕ} (hk : 1 ≤ k) {x : Subcube k → ℝ} (hx : InO x) :
    InX 0 x ∧ l1Sum x = (2 : ℝ) ^ (k - 1) := by
  obtain ⟨D, hdec, hDval, hout⟩ := hx
  have hnonneg : ∀ τ, 0 ≤ x τ := by
    intro τ
    by_cases hτ : τ ∈ D
    · rcases hDval τ hτ with ⟨_, h1⟩ | ⟨_, h2⟩ <;> linarith
    · rw [hout τ hτ]
  have hw0 : ∀ τ, weight τ = 0 → x τ = 0 := by
    intro τ h0
    by_cases hτ : τ ∈ D
    · have := hdec.1.1 τ hτ; omega
    · exact hout τ hτ
  have hquad : quadForm x = 0 := by
    rw [quadForm_eq_indistinguishable]
    have h1 : ∑ σ : Subcube k, ∑ τ : Subcube k, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) =
        ∑ τ ∈ D, x τ ^ 2 := by
      rw [← Finset.sum_subset (subset_univ D)]
      · refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [Finset.sum_eq_single σ]
        · simp [not_distinguishable_self, sq]
        · intro τ _ hne
          by_cases hτ : τ ∈ D
          · rw [if_pos (hdec.1.2 σ hσ τ hτ hne.symm)]
          · rw [hout τ hτ, mul_zero, ite_self]
        · intro h; exact absurd (mem_univ σ) h
      · intro σ _ hσ
        refine sum_eq_zero fun τ _ => ?_
        rw [hout σ hσ, zero_mul, ite_self]
    have h2 : ∑ τ : Subcube k, (weight τ : ℝ) * x τ = ∑ τ ∈ D, (weight τ : ℝ) * x τ := by
      symm
      exact Finset.sum_subset (subset_univ D) fun τ _ hτ => by rw [hout τ hτ, mul_zero]
    rw [h1, h2, ← sum_sub_distrib]
    refine sum_eq_zero fun τ hτ => ?_
    rcases hDval τ hτ with ⟨hw, hv⟩ | ⟨hw, hv⟩ <;> simp [hw, hv] <;> norm_num
  have hw1 : ∀ τ, weight τ = 1 → x τ ≤ 1 + 0 := by
    intro τ h1
    by_cases hτ : τ ∈ D
    · rcases hDval τ hτ with ⟨_, hv⟩ | ⟨hw, _⟩
      · linarith
      · omega
    · rw [hout τ hτ]; norm_num
  have hcompat : ∀ σ τ, ¬ compatible σ τ → x σ * x τ ≤ 0 := by
    intro σ τ hnc
    by_cases hσ : σ ∈ D
    · by_cases hτ : τ ∈ D
      · by_cases heq : σ = τ
        · subst heq
          have hw := hdec.1.1 σ hσ
          have hex : ∃ i, σ i = 2 := by
            have := card_pos.mp (by rw [← weight]; omega : 0 < (Finset.univ.filter (fun i : Fin k => σ i = 2)).card)
            obtain ⟨i, hi⟩ := this; exact ⟨i, (mem_filter.mp hi).2⟩
          obtain ⟨i, hi⟩ := hex
          exact absurd (Or.inr ⟨i, hi, hi⟩) hnc
        · exact absurd (Or.inl (hdec.1.2 σ hσ τ hτ heq)) hnc
      · rw [hout τ hτ, mul_zero]
    · rw [hout σ hσ, zero_mul]
  have hsum : l1Sum x = (2 : ℝ) ^ (k - 1) := by
    unfold l1Sum
    have hsumD : ∑ τ : Subcube k, x τ = ∑ τ ∈ D, x τ := by
      symm; exact Finset.sum_subset (subset_univ D) fun τ _ hτ => hout τ hτ
    rw [hsumD]
    have h2x : 2 * ∑ τ ∈ D, x τ = (∑ τ ∈ D, 2 ^ weight τ : ℕ) := by
      rw [mul_sum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rcases hDval τ hτ with ⟨hw, hv⟩ | ⟨hw, hv⟩ <;> simp [hw, hv] <;> norm_num
    have htot := (sum_two_pow_weight_le hdec.1).2.mpr hdec
    rw [htot, Nat.cast_pow, Nat.cast_ofNat] at h2x
    have hpow : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ']
    linarith
  exact ⟨⟨hnonneg, hquad.le, hw1, hcompat⟩, hsum⟩
noncomputable def suppFinset {k : ℕ} (x : Subcube k → ℝ) : Finset (Subcube k) :=
  Finset.univ.filter (fun τ => x τ ≠ 0)
lemma InX_coord_le {k : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) {x : Subcube k → ℝ} (hx : InX γ x) (τ : Subcube k) :
    x τ ≤ (3 : ℝ) ^ k * ((k : ℝ) + γ + 1) := by
  have hquad := hx.2.1
  rw [quadForm_eq_indistinguishable] at hquad
  have hsum_sq : ∑ σ : Subcube k, x σ ^ 2 ≤
      ∑ σ : Subcube k, ∑ ρ : Subcube k, (if distinguishable σ ρ then (0 : ℝ) else x σ * x ρ) := by
    apply sum_le_sum
    intro σ _
    have hterm : x σ ^ 2 = (if distinguishable σ σ then (0 : ℝ) else x σ * x σ) := by
      simp [not_distinguishable_self, sq]
    rw [hterm]
    exact single_le_sum (f := fun ρ => if distinguishable σ ρ then (0 : ℝ) else x σ * x ρ)
      (fun ρ _ => by
        split_ifs
        · exact le_refl 0
        · exact mul_nonneg (hx.1 σ) (hx.1 ρ)) (mem_univ σ)
  have hw_le : ∑ σ : Subcube k, (weight σ : ℝ) * x σ ≤ (k : ℝ) * l1Sum x := by
    unfold l1Sum
    rw [mul_sum]
    apply sum_le_sum
    intro σ _
    have hwk : weight σ ≤ k := by
      simpa [weight] using card_filter_le Finset.univ (fun i : Fin k => σ i = 2)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hwk) (hx.1 σ)
  have hcs : (l1Sum x) ^ 2 ≤ (3 : ℝ) ^ k * ∑ σ : Subcube k, x σ ^ 2 := by
    unfold l1Sum
    have hcard : (Fintype.card (Subcube k) : ℝ) = (3 : ℝ) ^ k := by
      simp [Subcube, Fintype.card_fin]
    rw [← hcard]
    have hnn : 0 ≤ ∑ σ : Subcube k, ∑ ρ : Subcube k, (x σ - x ρ) ^ 2 :=
      sum_nonneg fun σ _ => sum_nonneg fun ρ _ => sq_nonneg _
    have hexp : ∑ σ : Subcube k, ∑ ρ : Subcube k, (x σ - x ρ) ^ 2 =
        2 * ((Fintype.card (Subcube k) : ℝ) * ∑ σ : Subcube k, x σ ^ 2 - (∑ σ : Subcube k, x σ) ^ 2) := by
      simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const,
        card_univ, nsmul_eq_mul, ← mul_sum, ← sum_mul]
      have h2x : ∑ σ : Subcube k, 2 * x σ = 2 * ∑ σ : Subcube k, x σ := by rw [mul_sum]
      rw [h2x]; ring
    linarith
  have hS : (l1Sum x) ^ 2 ≤ (3 : ℝ) ^ k * ((k : ℝ) * l1Sum x + γ) := by
    have h1 : ∑ σ : Subcube k, x σ ^ 2 ≤ (k : ℝ) * l1Sum x + γ := by linarith
    exact hcs.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  have hS_le : l1Sum x ≤ (3 : ℝ) ^ k * ((k : ℝ) + γ + 1) := by
    by_contra hgt
    have hgt' : (3 : ℝ) ^ k * ((k : ℝ) + γ + 1) < l1Sum x := lt_of_not_ge hgt
    have h3pos : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hSpos : 1 ≤ l1Sum x := by nlinarith
    have hγl : γ ≤ γ * l1Sum x := by nlinarith only [hγ, hSpos]
    have h1 : (3 : ℝ) ^ k * ((k : ℝ) * l1Sum x + γ) < (l1Sum x) ^ 2 := by
      have hmul : (3 : ℝ) ^ k * ((k : ℝ) + γ + 1) * l1Sum x < l1Sum x * l1Sum x :=
        mul_lt_mul_of_pos_right hgt' (by linarith)
      nlinarith only [hmul, h3pos, hSpos, hγl]
    linarith
  have hle_sum : x τ ≤ l1Sum x :=
    single_le_sum (fun σ _ => hx.1 σ) (mem_univ τ)
  exact hle_sum.trans hS_le
lemma isCompact_InX_clean {k : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) :
    IsCompact {x : Subcube k → ℝ | InX γ x} := by
  have hclosed : IsClosed {x : Subcube k → ℝ | InX γ x} := by
    have hq_cont : Continuous (@quadForm k) := by
      unfold quadForm
      refine Continuous.sub (Continuous.sub ?_ ?_) ?_
      · exact (continuous_finsetSum _ fun τ _ => continuous_apply τ).pow 2
      · exact continuous_finsetSum _ fun σ _ => continuous_finsetSum _ fun τ _ => by
          by_cases hd : distinguishable σ τ
          · simp only [if_pos hd]; exact (continuous_apply σ).mul (continuous_apply τ)
          · simp only [if_neg hd]; exact continuous_const
      · exact continuous_finsetSum _ fun τ _ => continuous_const.mul (continuous_apply τ)
    have h1 : IsClosed {x : Subcube k → ℝ | ∀ τ, 0 ≤ x τ} := by
      convert isClosed_iInter fun τ : Subcube k =>
        isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply τ)
      ext x; simp
    have h3 : IsClosed {x : Subcube k → ℝ | quadForm x ≤ γ} :=
      isClosed_le hq_cont continuous_const
    have h4 : IsClosed {x : Subcube k → ℝ | ∀ τ, weight τ = 1 → x τ ≤ 1 + γ} := by
      convert isClosed_iInter fun τ : Subcube k => isClosed_iInter fun _ : weight τ = 1 =>
        isClosed_le (continuous_apply τ) (continuous_const (y := 1 + γ))
      ext x; simp
    have h5 : IsClosed {x : Subcube k → ℝ | ∀ σ τ, ¬ compatible σ τ → x σ * x τ ≤ γ} := by
      convert isClosed_iInter fun σ : Subcube k => isClosed_iInter fun τ : Subcube k =>
        isClosed_iInter fun _ : ¬ compatible σ τ =>
          isClosed_le ((continuous_apply σ).mul (continuous_apply τ)) (continuous_const (y := γ))
      ext x; simp
    exact h1.inter (h3.inter (h4.inter h5))
  have hsub : {x : Subcube k → ℝ | InX γ x} ⊆
      Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) ((3 : ℝ) ^ k * ((k : ℝ) + γ + 1))) :=
    fun x hx τ _ => ⟨hx.1 τ, InX_coord_le hγ hx τ⟩
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub
def IsOptimal {k : ℕ} (x : Subcube k → ℝ) : Prop :=
  InX 0 x ∧ ∀ z : Subcube k → ℝ, InX 0 z → l1Sum z ≤ l1Sum x
lemma exists_optimal {k : ℕ} : ∃ x : Subcube k → ℝ, IsOptimal x := by
  have hne : {x : Subcube k → ℝ | InX 0 x}.Nonempty := by
    refine ⟨0, fun _ => le_refl 0, ?_, fun _ _ => by norm_num, fun _ _ _ => by simp⟩
    simp [quadForm]
  have hcont : ContinuousOn (@l1Sum k) {x : Subcube k → ℝ | InX 0 x} :=
    (continuous_finsetSum _ fun τ _ => continuous_apply τ).continuousOn
  obtain ⟨x, hx, hmax⟩ := (isCompact_InX_clean (le_refl 0)).exists_isMaxOn hne hcont
  exact ⟨x, hx, fun z hz => hmax hz⟩
lemma compatible_of_InX_zero {k : ℕ} {x : Subcube k → ℝ} (hx : InX 0 x)
    {σ τ : Subcube k} (hσ : x σ ≠ 0) (hτ : x τ ≠ 0) : compatible σ τ := by
  by_contra hnc
  have hle := hx.2.2.2 σ τ hnc
  have hpos : 0 < x σ * x τ := mul_pos (lt_of_le_of_ne (hx.1 σ) hσ.symm) (lt_of_le_of_ne (hx.1 τ) hτ.symm)
  linarith
lemma eq_of_weight_one_compat {k : ℕ} {σ τ : Subcube k}
    (hnd : ¬ distinguishable σ τ) (hcomp : compatible σ τ) (hσ : weight σ = 1) (hτ : weight τ = 1) :
    σ = τ := by
  have hsub1 := subcubeSet_subset_of_compat_weight_one hnd hcomp hτ
  have hsub2 := subcubeSet_subset_of_compat_weight_one (fun h => hnd (distinguishable_symm.mp h))
    (compatible_symm.mp hcomp) hσ
  have heq_set : subcubeSet σ = subcubeSet τ := Finset.Subset.antisymm hsub2 hsub1
  funext i
  by_contra hne
  have h01 : ¬ ((σ i = 0 ∧ τ i = 1) ∨ (σ i = 1 ∧ τ i = 0)) := fun h => hnd ⟨i, h⟩
  have hboth : ∀ (α : Subcube k) (j : Fin k), α j = 2 →
      (∃ c ∈ subcubeSet α, c j = true) ∧ (∃ c ∈ subcubeSet α, c j = false) := by
    intro α j hj
    constructor
    · refine ⟨fun t => if t = j then true else decide (α t = 1),
        mem_filter.mpr ⟨mem_univ _, fun t => ?_⟩, by simp⟩
      by_cases ht : t = j
      · subst ht; simp [hj]
      · simp [ht]; intro h0; simp [h0]
    · refine ⟨fun t => if t = j then false else decide (α t = 1),
        mem_filter.mpr ⟨mem_univ _, fun t => ?_⟩, by simp⟩
      by_cases ht : t = j
      · subst ht; simp [hj]
      · simp [ht]; intro h0; simp [h0]
  have hcases : (σ i = 2 ∧ (τ i = 0 ∨ τ i = 1)) ∨ (τ i = 2 ∧ (σ i = 0 ∨ σ i = 1)) := by
    generalize hσi : σ i = a at hne h01 ⊢
    generalize hτi : τ i = b at hne h01 ⊢
    fin_cases a <;> fin_cases b <;> simp_all
  rcases hcases with ⟨hσ2, hτ0 | hτ1⟩ | ⟨hτ2, hσ0 | hσ1⟩
  · obtain ⟨⟨c, hc, hct⟩, _⟩ := hboth σ i hσ2
    rw [heq_set] at hc
    have := ((mem_filter.mp hc).2 i).1 hτ0
    simp [hct] at this
  · obtain ⟨_, ⟨c, hc, hcf⟩⟩ := hboth σ i hσ2
    rw [heq_set] at hc
    have := ((mem_filter.mp hc).2 i).2 hτ1
    simp [hcf] at this
  · obtain ⟨⟨c, hc, hct⟩, _⟩ := hboth τ i hτ2
    rw [← heq_set] at hc
    have := ((mem_filter.mp hc).2 i).1 hσ0
    simp [hct] at this
  · obtain ⟨_, ⟨c, hc, hcf⟩⟩ := hboth τ i hτ2
    rw [← heq_set] at hc
    have := ((mem_filter.mp hc).2 i).2 hσ1
    simp [hcf] at this
lemma quadForm_eq_zero_of_optimal {k : ℕ} (hk : 1 ≤ k) {x : Subcube k → ℝ} (hx : IsOptimal x) :
    quadForm x = 0 := by
  have hle : quadForm x ≤ 0 := hx.1.2.1
  by_contra hne
  have hlt : quadForm x < 0 := lt_of_le_of_ne hle hne
  have hbump : ∀ τ : Subcube k, x τ ≠ 0 → (2 ≤ weight τ ∨ x τ < 1) → False := by
    intro τ hτne hroom
    let f : ℝ → ℝ := fun α => quadForm (Function.update x τ (x τ + α))
    have hf_cont : Continuous f := by
      unfold f quadForm
      have hupd : ∀ σ : Subcube k, Continuous (fun α : ℝ => Function.update x τ (x τ + α) σ) := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp only [Function.update_self]; exact continuous_const.add continuous_id
        · simp only [Function.update_of_ne h]; exact continuous_const
      refine Continuous.sub (Continuous.sub ?_ ?_) ?_
      · exact (continuous_finset_sum _ fun σ _ => hupd σ).pow 2
      · exact continuous_finset_sum _ fun σ _ => continuous_finset_sum _ fun ρ _ => by
          by_cases hd : distinguishable σ ρ
          · simp only [if_pos hd]; exact (hupd σ).mul (hupd ρ)
          · simp only [if_neg hd]; exact continuous_const
      · exact continuous_finset_sum _ fun σ _ => continuous_const.mul (hupd σ)
    have hf0 : f 0 < 0 := by simpa [f] using hlt
    have hev : ∀ᶠ α in 𝓝 (0 : ℝ), f α < 0 := hf_cont.continuousAt.eventually (gt_mem_nhds hf0)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    let α : ℝ := min (δ / 2) (if 2 ≤ weight τ then 1 else (1 - x τ) / 2)
    have hαpos : 0 < α := by
      dsimp only [α]
      apply lt_min (by positivity)
      split_ifs with h2
      · norm_num
      · have : x τ < 1 := hroom.resolve_left h2
        linarith
    have hαlt : dist α 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hαpos]
      exact (min_le_left _ _).trans_lt (by linarith)
    let x' := Function.update x τ (x τ + α)
    have hx'F : quadForm x' ≤ 0 := (hδ hαlt).le
    have hx'_in : InX 0 x' := by
      refine ⟨?_, hx'F, ?_, ?_⟩
      · intro σ
        by_cases h : σ = τ
        · subst h; simp only [x', Function.update_self]; linarith [hx.1.1 σ]
        · simp only [x', Function.update_of_ne h]; exact hx.1.1 σ
      · intro σ h1
        by_cases h : σ = τ
        · subst h; simp only [x', Function.update_self, add_zero]
          have hnot2 : ¬ 2 ≤ weight σ := by omega
          have hαle : α ≤ (1 - x σ) / 2 := by
            dsimp only [α]
            rw [if_neg hnot2]
            exact min_le_right _ _
          have hlt1 : x σ < 1 := hroom.resolve_left hnot2
          linarith
        · simp only [x', Function.update_of_ne h]; exact hx.1.2.2.1 σ h1
      · intro σ ρ hnc
        have hzero : ∀ s, x' s ≠ 0 → x s ≠ 0 := by
          intro s hs
          by_cases h : s = τ
          · subst h; exact hτne
          · simpa [x', Function.update_of_ne h] using hs
        by_cases h1 : x' σ = 0
        · rw [h1, zero_mul]
        · by_cases h2 : x' ρ = 0
          · rw [h2, mul_zero]
          · exact absurd (compatible_of_InX_zero hx.1 (hzero σ h1) (hzero ρ h2)) hnc
    have hsum_gt : l1Sum x < l1Sum x' := by
      unfold l1Sum
      have heq : ∑ σ : Subcube k, x' σ = (∑ σ : Subcube k, x σ) + α := by
        rw [← Finset.add_sum_erase _ _ (mem_univ τ),
            ← Finset.add_sum_erase _ x (mem_univ τ)]
        have hrest : ∑ σ ∈ Finset.univ.erase τ, x' σ = ∑ σ ∈ Finset.univ.erase τ, x σ :=
          Finset.sum_congr rfl fun σ hσ => Function.update_of_ne (Finset.ne_of_mem_erase hσ) _ _
        rw [hrest]
        simp only [x', Function.update_self]
        ring
      linarith
    linarith [hx.2 x' hx'_in]
  by_cases hge2 : ∃ τ : Subcube k, x τ ≠ 0 ∧ 2 ≤ weight τ
  · obtain ⟨τ, hne, hw⟩ := hge2
    exact hbump τ hne (Or.inl hw)
  ·
    have hall1 : ∀ τ : Subcube k, x τ ≠ 0 → weight τ = 1 := by
      intro τ hne
      have hnot2 : ¬ 2 ≤ weight τ := fun h => hge2 ⟨τ, hne, h⟩
      have hne0 : weight τ ≠ 0 := fun h0 => hne (InX_zero_weight_zero hx.1 h0)
      omega
    have hF_eq : quadForm x = ∑ τ : Subcube k, (x τ ^ 2 - x τ) := by
      rw [quadForm_eq_indistinguishable, ← sum_sub_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hσ : x σ = 0
      · simp [hσ]
      · have hwσ : weight σ = 1 := hall1 σ hσ
        have hrow : ∑ τ : Subcube k, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) = x σ ^ 2 := by
          rw [Finset.sum_eq_single σ]
          · simp [not_distinguishable_self, sq]
          · intro τ _ hne
            by_cases hτ : x τ = 0
            · simp [hτ]
            · have hcomp := compatible_of_InX_zero hx.1 hσ hτ
              have hdist : distinguishable σ τ := by
                by_contra hnd
                exact hne (eq_of_weight_one_compat hnd hcomp hwσ (hall1 τ hτ)).symm
              simp [hdist]
          · intro h; exact absurd (mem_univ σ) h
        rw [hrow, hwσ, Nat.cast_one, one_mul]
    rw [hF_eq] at hlt
    have hex_neg : ∃ τ : Subcube k, x τ ^ 2 - x τ < 0 := by
      by_contra hall
      push Not at hall
      have : 0 ≤ ∑ τ : Subcube k, (x τ ^ 2 - x τ) := sum_nonneg fun τ _ => hall τ
      linarith
    obtain ⟨τ, hτneg⟩ := hex_neg
    have hτne : x τ ≠ 0 := by intro h0; rw [h0] at hτneg; norm_num at hτneg
    have hτlt1 : x τ < 1 := by nlinarith [hx.1.1 τ]
    exact hbump τ hτne (Or.inr hτlt1)
noncomputable def compress {k : ℕ} (x : Subcube k → ℝ) (π ρ : Subcube k) : Subcube k → ℝ :=
  if 2 ≤ weight ρ ∨ x π + x ρ < 1 then
    Function.update (Function.update x π 0) ρ (x π + x ρ)
  else
    Function.update (Function.update x π (x π + x ρ - 1)) ρ 1
lemma compress_l1Sum {k : ℕ} (x : Subcube k → ℝ) {π ρ : Subcube k} (hne : π ≠ ρ) :
    l1Sum (compress x π ρ) = l1Sum x := by
  unfold l1Sum compress
  have hsum2 : ∀ a b : ℝ, a + b = x π + x ρ →
      ∑ τ : Subcube k, Function.update (Function.update x π a) ρ b τ = ∑ τ : Subcube k, x τ := by
    intro a b hab
    rw [← Finset.add_sum_erase _ _ (mem_univ ρ),
        ← Finset.add_sum_erase _ x (mem_univ ρ)]
    have hπ_in : π ∈ Finset.univ.erase ρ := mem_erase.mpr ⟨hne, mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hπ_in, ← Finset.add_sum_erase _ x hπ_in]
    have hrest : ∑ τ ∈ (Finset.univ.erase ρ).erase π,
        Function.update (Function.update x π a) ρ b τ =
        ∑ τ ∈ (Finset.univ.erase ρ).erase π, x τ := by
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have h1 : τ ≠ π := Finset.ne_of_mem_erase hτ
      have h2 : τ ≠ ρ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)
      rw [Function.update_of_ne h2, Function.update_of_ne h1]
    rw [hrest, Function.update_self, Function.update_of_ne hne, Function.update_self]
    linarith
  split_ifs
  · exact hsum2 0 (x π + x ρ) (by ring)
  · exact hsum2 (x π + x ρ - 1) 1 (by ring)
lemma quadForm_shift_indistinguishable {k : ℕ} (x : Subcube k → ℝ)
    {π ρ : Subcube k} (hne : π ≠ ρ) (hnd : ¬ distinguishable π ρ) (t : ℝ) :
    let x' := Function.update (Function.update x π (x π - t)) ρ (x ρ + t)
    quadForm x' - quadForm x =
      t * (((weight π : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable π τ then x τ else 0)
         - ((weight ρ : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable ρ τ then x τ else 0)) := by
  intro x'
  have hsum_eq : ∑ τ : Subcube k, x' τ = ∑ τ : Subcube k, x τ := by
    rw [← Finset.add_sum_erase _ _ (mem_univ ρ),
        ← Finset.add_sum_erase _ x (mem_univ ρ)]
    have hπ_in : π ∈ Finset.univ.erase ρ := mem_erase.mpr ⟨hne, mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hπ_in, ← Finset.add_sum_erase _ x hπ_in]
    have hrest : ∑ τ ∈ (Finset.univ.erase ρ).erase π, x' τ =
        ∑ τ ∈ (Finset.univ.erase ρ).erase π, x τ := by
      refine Finset.sum_congr rfl fun τ hτ => ?_
      dsimp only [x']
      rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)),
          Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
    rw [hrest]
    simp only [x', Function.update_self, Function.update_of_ne hne]
    ring
  let d : Subcube k → ℝ := fun τ => if τ = ρ then t else if τ = π then -t else 0
  have hx'_eq : ∀ τ, x' τ = x τ + d τ := by
    intro τ
    by_cases h1 : τ = ρ
    · subst h1; simp [x', d]
    · by_cases h2 : τ = π
      · subst h2; simp [x', d, h1]; ring
      · simp [x', d, h1, h2]
  have hdist_diff :
      (∑ σ : Subcube k, ∑ τ : Subcube k, if distinguishable σ τ then x' σ * x' τ else 0) -
      (∑ σ : Subcube k, ∑ τ : Subcube k, if distinguishable σ τ then x σ * x τ else 0) =
      2 * t * ((∑ τ : Subcube k, if distinguishable ρ τ then x τ else 0) -
               (∑ τ : Subcube k, if distinguishable π τ then x τ else 0)) := by
    have h1 : (∑ σ : Subcube k, ∑ τ : Subcube k, if distinguishable σ τ then x' σ * x' τ else 0) -
        (∑ σ : Subcube k, ∑ τ : Subcube k, if distinguishable σ τ then x σ * x τ else 0) =
        ∑ σ : Subcube k, ∑ τ : Subcube k,
          (if distinguishable σ τ then d σ * x τ else 0) +
        ∑ σ : Subcube k, ∑ τ : Subcube k,
          (if distinguishable σ τ then x σ * d τ else 0) +
        ∑ σ : Subcube k, ∑ τ : Subcube k,
          (if distinguishable σ τ then d σ * d τ else 0) := by
      rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hx'_eq σ, hx'_eq τ]
      split_ifs <;> ring
    have hdd : ∑ σ : Subcube k, ∑ τ : Subcube k,
        (if distinguishable σ τ then d σ * d τ else 0) = 0 := by
      refine sum_eq_zero fun σ _ => sum_eq_zero fun τ _ => ?_
      split_ifs with hd
      · by_cases hσ1 : σ = ρ
        · rw [hσ1] at hd ⊢
          by_cases hτ1 : τ = ρ
          · rw [hτ1] at hd; exact absurd hd (not_distinguishable_self _)
          · by_cases hτ2 : τ = π
            · rw [hτ2] at hd; exact absurd (distinguishable_symm.mp hd) hnd
            · simp [d, hτ1, hτ2]
        · by_cases hσ2 : σ = π
          · rw [hσ2] at hd ⊢
            by_cases hτ1 : τ = ρ
            · rw [hτ1] at hd; exact absurd hd hnd
            · by_cases hτ2 : τ = π
              · rw [hτ2] at hd; exact absurd hd (not_distinguishable_self _)
              · simp [d, hτ1, hτ2]
          · simp [d, hσ1, hσ2]
      · rfl
    have hdx : ∑ σ : Subcube k, ∑ τ : Subcube k,
        (if distinguishable σ τ then d σ * x τ else 0) =
        t * ((∑ τ : Subcube k, if distinguishable ρ τ then x τ else 0) -
             (∑ τ : Subcube k, if distinguishable π τ then x τ else 0)) := by
      have hterm : ∀ σ : Subcube k,
          (∑ τ : Subcube k, if distinguishable σ τ then d σ * x τ else 0) =
          d σ * ∑ τ : Subcube k, if distinguishable σ τ then x τ else 0 := by
        intro σ; rw [mul_sum]; refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> ring
      simp_rw [hterm]
      rw [← Finset.add_sum_erase _ _ (mem_univ ρ)]
      have hπ_in : π ∈ Finset.univ.erase ρ := mem_erase.mpr ⟨hne, mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hπ_in]
      have hrest : ∑ σ ∈ (Finset.univ.erase ρ).erase π,
          d σ * ∑ τ : Subcube k, (if distinguishable σ τ then x τ else 0) = 0 := by
        refine sum_eq_zero fun σ hσ => ?_
        have h1' : σ ≠ π := Finset.ne_of_mem_erase hσ
        have h2' : σ ≠ ρ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ)
        simp [d, h1', h2']
      rw [hrest, add_zero]
      simp [d, hne]
      ring
    have hxd : ∑ σ : Subcube k, ∑ τ : Subcube k,
        (if distinguishable σ τ then x σ * d τ else 0) =
        ∑ σ : Subcube k, ∑ τ : Subcube k,
        (if distinguishable σ τ then d σ * x τ else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
      by_cases hd : distinguishable τ σ
      · rw [if_pos hd, if_pos (distinguishable_symm.mp hd), mul_comm]
      · rw [if_neg hd, if_neg (fun h => hd (distinguishable_symm.mp h))]
    rw [h1, hdd, hxd, hdx]
    ring
  have hw_diff : (∑ τ : Subcube k, (weight τ : ℝ) * x' τ) - (∑ τ : Subcube k, (weight τ : ℝ) * x τ) =
      t * ((weight ρ : ℝ) - (weight π : ℝ)) := by
    rw [← sum_sub_distrib]
    have hterm : ∀ τ : Subcube k, (weight τ : ℝ) * x' τ - (weight τ : ℝ) * x τ = (weight τ : ℝ) * d τ := by
      intro τ; rw [hx'_eq τ]; ring
    simp_rw [hterm]
    rw [← Finset.add_sum_erase _ _ (mem_univ ρ)]
    have hπ_in : π ∈ Finset.univ.erase ρ := mem_erase.mpr ⟨hne, mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hπ_in]
    have hrest : ∑ τ ∈ (Finset.univ.erase ρ).erase π, (weight τ : ℝ) * d τ = 0 := by
      refine sum_eq_zero fun τ hτ => ?_
      simp [d, Finset.ne_of_mem_erase hτ, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)]
    rw [hrest, add_zero]
    simp [d, hne]; ring
  unfold quadForm
  rw [hsum_eq]
  linarith [hdist_diff, hw_diff]
def compEdge {k : ℕ} (x : Subcube k → ℝ) (π ρ : Subcube k) : Prop :=
  x π ≠ 0 ∧ x ρ ≠ 0 ∧ π ≠ ρ ∧ ¬ distinguishable π ρ ∧ InX 0 (compress x π ρ)
def IsCompressed {k : ℕ} (x : Subcube k → ℝ) : Prop :=
  IsOptimal x ∧ ∀ π ρ, compEdge x π ρ → compress x π ρ = x
lemma compress_eq_shift {k : ℕ} {x : Subcube k → ℝ} (hx : InX 0 x) {π ρ : Subcube k}
    (hne : π ≠ ρ) (hxρ : x ρ ≠ 0) :
    let t : ℝ := if 2 ≤ weight ρ ∨ x π + x ρ < 1 then x π else 1 - x ρ
    compress x π ρ = Function.update (Function.update x π (x π - t)) ρ (x ρ + t) ∧
    0 ≤ t ∧ (t = 0 ↔ compress x π ρ = x) ∧
    (∀ τ, 0 ≤ compress x π ρ τ) ∧
    (∀ τ, weight τ = 1 → compress x π ρ τ ≤ 1 + 0) ∧
    (∀ σ τ, ¬ compatible σ τ → compress x π ρ σ * compress x π ρ τ ≤ 0) := by
  intro t
  have hρ_le1 : ¬ 2 ≤ weight ρ → x ρ ≤ 1 := by
    intro hnot2
    by_cases h0 : weight ρ = 0
    · exact absurd (InX_zero_weight_zero hx h0) hxρ
    · have h1 : weight ρ = 1 := by omega
      simpa using hx.2.2.1 ρ h1
  have ht_nonneg : 0 ≤ t := by
    dsimp only [t]
    split_ifs with h
    · exact hx.1 π
    · push_neg at h; linarith [hρ_le1 (not_le.mpr h.1)]
  have hcomp_eq : compress x π ρ = Function.update (Function.update x π (x π - t)) ρ (x ρ + t) := by
    unfold compress
    dsimp only [t]
    split_ifs <;> (ext τ; by_cases h1 : τ = ρ <;> by_cases h2 : τ = π <;> simp [h1, h2] <;> ring)
  have hzero_iff : t = 0 ↔ compress x π ρ = x := by
    rw [hcomp_eq]
    constructor
    · intro ht0; rw [ht0]; ext τ
      by_cases h1 : τ = ρ
      · subst h1; simp
      · by_cases h2 : τ = π
        · subst h2; simp [h1]
        · simp [h1, h2]
    · intro heq
      have hρeq := congrFun heq ρ
      simp only [Function.update_self] at hρeq
      linarith
  have hnonneg : ∀ τ, 0 ≤ compress x π ρ τ := by
    intro τ
    unfold compress
    split_ifs with h
    · by_cases h1 : τ = ρ
      · rw [h1]; simp; linarith [hx.1 π, hx.1 ρ]
      · by_cases h2 : τ = π
        · rw [h2]; simp [hne]
        · simp [h1, h2, hx.1 τ]
    · push Not at h
      by_cases h1 : τ = ρ
      · rw [h1]; simp
      · by_cases h2 : τ = π
        · rw [h2]; simp [hne]; linarith
        · simp [h1, h2, hx.1 τ]
  have hsupp_sub : ∀ τ, compress x π ρ τ ≠ 0 → x τ ≠ 0 := by
    intro τ hne0
    by_cases h1 : τ = ρ
    · subst h1; exact hxρ
    · by_cases h2 : τ = π
      · subst h2
        intro hxπ0
        apply hne0
        unfold compress
        split_ifs with h
        · simp [h1]
        · push_neg at h
          have hρ1 : x ρ ≤ 1 := hρ_le1 (not_le.mpr h.1)
          simp [h1]; linarith
      · unfold compress at hne0
        split_ifs at hne0 <;> simpa [h1, h2] using hne0
  have hw1 : ∀ τ, weight τ = 1 → compress x π ρ τ ≤ 1 + 0 := by
    intro τ h1
    by_cases hτ1 : τ = ρ
    · subst hτ1
      unfold compress
      split_ifs with h
      · simp only [Function.update_self, add_zero]
        have hnot2 : ¬ 2 ≤ weight τ := by omega
        linarith [h.resolve_left hnot2]
      · simp only [Function.update_self, add_zero]; exact le_refl 1
    · by_cases hτ2 : τ = π
      · subst hτ2
        rw [hcomp_eq, Function.update_of_ne hτ1, Function.update_self]
        have := hx.2.2.1 τ h1
        linarith
      · rw [hcomp_eq, Function.update_of_ne hτ1, Function.update_of_ne hτ2]
        exact hx.2.2.1 τ h1
  have hcompat : ∀ σ τ, ¬ compatible σ τ → compress x π ρ σ * compress x π ρ τ ≤ 0 := by
    intro σ τ hnc
    by_cases h1 : compress x π ρ σ = 0
    · rw [h1, zero_mul]
    · by_cases h2 : compress x π ρ τ = 0
      · rw [h2, mul_zero]
      · exact absurd (compatible_of_InX_zero hx (hsupp_sub σ h1) (hsupp_sub τ h2)) hnc
  exact ⟨hcomp_eq, ht_nonneg, hzero_iff, hnonneg, hw1, hcompat⟩
lemma lemma_compress {k : ℕ} (hk : 1 ≤ k) {x : Subcube k → ℝ} (hx : IsOptimal x)
    {π ρ : Subcube k} (hxπ : x π ≠ 0) (hxρ : x ρ ≠ 0) (hne : π ≠ ρ)
    (hnd : ¬ distinguishable π ρ) :
    (compress x π ρ = x ∧ x ρ = 1 ∧ weight ρ = 1 ∧ 2 ≤ weight π ∧ ¬ compEdge x ρ π) ∨
    (compress x ρ π = x ∧ x π = 1 ∧ weight π = 1 ∧ 2 ≤ weight ρ ∧ ¬ compEdge x π ρ) ∨
    (compEdge x π ρ ∧ compEdge x ρ π) := by
  have hF0 : quadForm x = 0 := quadForm_eq_zero_of_optimal hk hx
  let A : ℝ := (weight ρ : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable ρ τ then x τ else 0
  let B : ℝ := (weight π : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable π τ then x τ else 0
  have hcomp_πρ := compress_eq_shift hx.1 hne hxρ
  have hcomp_ρπ := compress_eq_shift hx.1 hne.symm hxπ
  have hF_πρ : quadForm (compress x π ρ) - quadForm x =
      (if 2 ≤ weight ρ ∨ x π + x ρ < 1 then x π else 1 - x ρ) * (B - A) := by
    rw [hcomp_πρ.1]
    exact quadForm_shift_indistinguishable x hne hnd _
  have hF_ρπ : quadForm (compress x ρ π) - quadForm x =
      (if 2 ≤ weight π ∨ x ρ + x π < 1 then x ρ else 1 - x π) * (A - B) := by
    rw [hcomp_ρπ.1]
    exact quadForm_shift_indistinguishable x hne.symm (fun h => hnd (distinguishable_symm.mp h)) _
  have hBA_edge : B ≤ A → compEdge x π ρ := by
    intro hBA
    refine ⟨hxπ, hxρ, hne, hnd, hcomp_πρ.2.2.2.1, ?_, hcomp_πρ.2.2.2.2.1, hcomp_πρ.2.2.2.2.2⟩
    have hmul : (if 2 ≤ weight ρ ∨ x π + x ρ < 1 then x π else 1 - x ρ) * (B - A) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcomp_πρ.2.1 (by linarith)
    linarith
  have hAB_edge : A ≤ B → compEdge x ρ π := by
    intro hAB
    refine ⟨hxρ, hxπ, hne.symm, fun h => hnd (distinguishable_symm.mp h),
      hcomp_ρπ.2.2.2.1, ?_, hcomp_ρπ.2.2.2.2.1, hcomp_ρπ.2.2.2.2.2⟩
    have hmul : (if 2 ≤ weight π ∨ x ρ + x π < 1 then x ρ else 1 - x π) * (A - B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcomp_ρπ.2.1 (by linarith)
    linarith
  rcases lt_trichotomy B A with hlt | heq | hgt
  · left
    have hedge := hBA_edge hlt.le
    have ht0 : (if 2 ≤ weight ρ ∨ x π + x ρ < 1 then x π else 1 - x ρ) = 0 := by
      by_contra htne
      have htpos : 0 < (if 2 ≤ weight ρ ∨ x π + x ρ < 1 then x π else 1 - x ρ) :=
        lt_of_le_of_ne hcomp_πρ.2.1 (Ne.symm htne)
      have hFneg : quadForm (compress x π ρ) < 0 := by nlinarith
      have hopt' : IsOptimal (compress x π ρ) :=
        ⟨hedge.2.2.2.2, fun z hz => by rw [compress_l1Sum x hne]; exact hx.2 z hz⟩
      linarith [quadForm_eq_zero_of_optimal hk hopt']
    have hfix : compress x π ρ = x := hcomp_πρ.2.2.1.mp ht0
    have hnot2ρ : ¬ 2 ≤ weight ρ := by
      intro h2
      rw [if_pos (Or.inl h2)] at ht0
      exact hxπ ht0
    have hwρ1 : weight ρ = 1 := by
      have h0 : weight ρ ≠ 0 := fun h => hxρ (InX_zero_weight_zero hx.1 h)
      omega
    have hxρ1 : x ρ = 1 := by
      by_cases hsum : x π + x ρ < 1
      · rw [if_pos (Or.inr hsum)] at ht0; exact absurd ht0 hxπ
      · rw [if_neg (not_or.mpr ⟨hnot2ρ, hsum⟩)] at ht0; linarith
    have hwπ2 : 2 ≤ weight π := by
      have h0 : weight π ≠ 0 := fun h => hxπ (InX_zero_weight_zero hx.1 h)
      by_contra hlt2
      have hwπ1 : weight π = 1 := by omega
      exact hne (eq_of_weight_one_compat hnd (compatible_of_InX_zero hx.1 hxπ hxρ) hwπ1 hwρ1)
    have hno_rev : ¬ compEdge x ρ π := by
      intro hrev
      have hFrev : quadForm (compress x ρ π) ≤ 0 := hrev.2.2.2.2.2.1
      rw [if_pos (Or.inl hwπ2)] at hF_ρπ
      have hxρ_pos : 0 < x ρ := lt_of_le_of_ne (hx.1.1 ρ) hxρ.symm
      nlinarith
    exact ⟨hfix, hxρ1, hwρ1, hwπ2, hno_rev⟩
  · right; right
    exact ⟨hBA_edge heq.le, hAB_edge heq.ge⟩
  · right; left
    have hedge := hAB_edge hgt.le
    have ht0 : (if 2 ≤ weight π ∨ x ρ + x π < 1 then x ρ else 1 - x π) = 0 := by
      by_contra htne
      have htpos : 0 < (if 2 ≤ weight π ∨ x ρ + x π < 1 then x ρ else 1 - x π) :=
        lt_of_le_of_ne hcomp_ρπ.2.1 (Ne.symm htne)
      have hFneg : quadForm (compress x ρ π) < 0 := by nlinarith
      have hopt' : IsOptimal (compress x ρ π) :=
        ⟨hedge.2.2.2.2, fun z hz => by rw [compress_l1Sum x hne.symm]; exact hx.2 z hz⟩
      linarith [quadForm_eq_zero_of_optimal hk hopt']
    have hfix : compress x ρ π = x := hcomp_ρπ.2.2.1.mp ht0
    have hnot2π : ¬ 2 ≤ weight π := by
      intro h2
      rw [if_pos (Or.inl h2)] at ht0
      exact hxρ ht0
    have hwπ1 : weight π = 1 := by
      have h0 : weight π ≠ 0 := fun h => hxπ (InX_zero_weight_zero hx.1 h)
      omega
    have hxπ1 : x π = 1 := by
      by_cases hsum : x ρ + x π < 1
      · rw [if_pos (Or.inr hsum)] at ht0; exact absurd ht0 hxρ
      · rw [if_neg (not_or.mpr ⟨hnot2π, hsum⟩)] at ht0; linarith
    have hwρ2 : 2 ≤ weight ρ := by
      have h0 : weight ρ ≠ 0 := fun h => hxρ (InX_zero_weight_zero hx.1 h)
      by_contra hlt2
      have hwρ1 : weight ρ = 1 := by omega
      exact hne (eq_of_weight_one_compat hnd (compatible_of_InX_zero hx.1 hxπ hxρ) hwπ1 hwρ1)
    have hno_fwd : ¬ compEdge x π ρ := by
      intro hfwd
      have hFfwd : quadForm (compress x π ρ) ≤ 0 := hfwd.2.2.2.2.2.1
      rw [if_pos (Or.inl hwρ2)] at hF_πρ
      have hxπ_pos : 0 < x π := lt_of_le_of_ne (hx.1.1 π) hxπ.symm
      nlinarith
    exact ⟨hfix, hxπ1, hwπ1, hwρ2, hno_fwd⟩
lemma exists_compression_step {k : ℕ} (hk : 1 ≤ k) {x : Subcube k → ℝ}
    (hx : IsOptimal x) (hnc : ¬ IsCompressed x) :
    ∃ π ρ : Subcube k, compEdge x π ρ ∧ 2 ≤ weight ρ ∧
      IsOptimal (compress x π ρ) ∧ (compress x π ρ) π = 0 ∧
      (suppFinset (compress x π ρ)).card < (suppFinset x).card := by
  have hex : ∃ π ρ, compEdge x π ρ ∧ compress x π ρ ≠ x := by
    by_contra hall
    push Not at hall
    exact hnc ⟨hx, hall⟩
  obtain ⟨π, ρ, hEdge, hne_x⟩ := hex
  have hxπ : x π ≠ 0 := hEdge.1
  have hxρ : x ρ ≠ 0 := hEdge.2.1
  have hne : π ≠ ρ := hEdge.2.2.1
  have hnd : ¬ distinguishable π ρ := hEdge.2.2.2.1
  rcases lemma_compress hk hx hxπ hxρ hne hnd with h1 | h2 | ⟨he1, he2⟩
  · exact absurd h1.1 hne_x
  · exact absurd hEdge h2.2.2.2.2
  ·
    have h2or : 2 ≤ weight ρ ∨ 2 ≤ weight π := by
      by_contra hlt
      push Not at hlt
      have h0π : weight π ≠ 0 := fun h => hxπ (InX_zero_weight_zero hx.1 h)
      have h0ρ : weight ρ ≠ 0 := fun h => hxρ (InX_zero_weight_zero hx.1 h)
      exact hne (eq_of_weight_one_compat hnd (compatible_of_InX_zero hx.1 hxπ hxρ) (by omega) (by omega))
    have hshrink : ∀ a b, compEdge x a b → 2 ≤ weight b →
        IsOptimal (compress x a b) ∧ (compress x a b) a = 0 ∧
        (suppFinset (compress x a b)).card < (suppFinset x).card := by
      intro a b hab hwb
      have hopt' : IsOptimal (compress x a b) :=
        ⟨hab.2.2.2.2, fun z hz => by rw [compress_l1Sum x hab.2.2.1]; exact hx.2 z hz⟩
      have ha0 : compress x a b a = 0 := by
        unfold compress; rw [if_pos (Or.inl hwb), Function.update_of_ne hab.2.2.1, Function.update_self]
      have hssub : suppFinset (compress x a b) ⊂ suppFinset x := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro τ hτ
          rw [suppFinset, mem_filter] at hτ ⊢
          refine ⟨mem_univ _, ?_⟩
          by_cases h1 : τ = b
          · subst h1; exact hab.2.1
          · by_cases h2 : τ = a
            · subst h2; exact absurd ha0 hτ.2
            · unfold compress at hτ
              rw [if_pos (Or.inl hwb), Function.update_of_ne h1, Function.update_of_ne h2] at hτ
              exact hτ.2
        · intro heq
          have ha_in : a ∈ suppFinset x := mem_filter.mpr ⟨mem_univ _, hab.1⟩
          rw [← heq, suppFinset, mem_filter] at ha_in
          exact ha_in.2 ha0
      exact ⟨hopt', ha0, Finset.card_lt_card hssub⟩
    rcases h2or with hρ2 | hπ2
    · exact ⟨π, ρ, he1, hρ2, hshrink π ρ he1 hρ2⟩
    · exact ⟨ρ, π, he2, hπ2, hshrink ρ π he2 hπ2⟩
lemma exists_compressed_from_optimal {k : ℕ} (hk : 1 ≤ k) (x : Subcube k → ℝ) (hx : IsOptimal x) :
    IsCompressed x ∨
      ∃ (y : Subcube k → ℝ) (π ρ : Subcube k), IsOptimal y ∧ compEdge y π ρ ∧ 2 ≤ weight ρ ∧
        IsCompressed (compress y π ρ) ∧ (compress y π ρ) π = 0 := by
  suffices h : ∀ m : ℕ, ∀ x : Subcube k → ℝ, (suppFinset x).card = m → IsOptimal x →
      IsCompressed x ∨
        ∃ (y : Subcube k → ℝ) (π ρ : Subcube k), IsOptimal y ∧ compEdge y π ρ ∧ 2 ≤ weight ρ ∧
          IsCompressed (compress y π ρ) ∧ (compress y π ρ) π = 0 by
    exact h (suppFinset x).card x rfl hx
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro x hcard hx
    by_cases hc : IsCompressed x
    · exact Or.inl hc
    · obtain ⟨π, ρ, hEdge, hwρ, hopt', hπ0, hlt⟩ := exists_compression_step hk hx hc
      rw [hcard] at hlt
      rcases ih (suppFinset (compress x π ρ)).card hlt (compress x π ρ) rfl hopt' with hc' | hstep
      · exact Or.inr ⟨x, π, ρ, hx, hEdge, hwρ, hc', hπ0⟩
      · exact Or.inr hstep
lemma star_props {k : ℕ} (hk : 1 ≤ k) {x : Subcube k → ℝ} (hx : IsCompressed x) :
    (∀ ρ π, compEdge x ρ π → 2 ≤ weight ρ ∧ weight π = 1 ∧ x π = 1 ∧ ¬ compEdge x π ρ) ∧
    (∀ ρ₁ ρ₂ π, compEdge x ρ₁ π → compEdge x ρ₂ π → ρ₁ = ρ₂) := by
  have h1 : ∀ ρ π, compEdge x ρ π → 2 ≤ weight ρ ∧ weight π = 1 ∧ x π = 1 ∧ ¬ compEdge x π ρ := by
    intro ρ π hE
    have hnotrev : ¬ compEdge x π ρ := by
      intro hrev
      have hf1 : compress x ρ π = x := hx.2 ρ π hE
      have hf2 : compress x π ρ = x := hx.2 π ρ hrev
      have hwπ1 : weight π = 1 := by
        by_contra hne1
        have h0 : weight π ≠ 0 := fun h => hE.2.1 (InX_zero_weight_zero hx.1.1 h)
        have h2 : 2 ≤ weight π := by omega
        have hρ0 : compress x ρ π ρ = 0 := by
          unfold compress; rw [if_pos (Or.inl h2), Function.update_of_ne hE.2.2.1, Function.update_self]
        rw [hf1] at hρ0
        exact hE.1 hρ0
      have hwρ1 : weight ρ = 1 := by
        by_contra hne1
        have h0 : weight ρ ≠ 0 := fun h => hE.1 (InX_zero_weight_zero hx.1.1 h)
        have h2 : 2 ≤ weight ρ := by omega
        have hπ0 : compress x π ρ π = 0 := by
          unfold compress; rw [if_pos (Or.inl h2), Function.update_of_ne hrev.2.2.1, Function.update_self]
        rw [hf2] at hπ0
        exact hE.2.1 hπ0
      exact hE.2.2.1 (eq_of_weight_one_compat hE.2.2.2.1 (compatible_of_InX_zero hx.1.1 hE.1 hE.2.1) hwρ1 hwπ1)
    rcases lemma_compress hk hx.1 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2.1 with hA | hB | hC
    · exact ⟨hA.2.2.2.1, hA.2.2.1, hA.2.1, hnotrev⟩
    · exact absurd hE hB.2.2.2.2
    · exact absurd hC.2 hnotrev
  have h2 : ∀ ρ₁ ρ₂ π, compEdge x ρ₁ π → compEdge x ρ₂ π → ρ₁ = ρ₂ := by
    intro ρ₁ ρ₂ π hE1 hE2
    by_contra hne
    have hp1 := h1 ρ₁ π hE1
    have hp2 := h1 ρ₂ π hE2
    have hsub1 : subcubeSet π ⊆ subcubeSet ρ₁ :=
      subcubeSet_subset_of_compat_weight_one hE1.2.2.2.1
        (compatible_of_InX_zero hx.1.1 hE1.1 hE1.2.1) hp1.2.1
    have hsub2 : subcubeSet π ⊆ subcubeSet ρ₂ :=
      subcubeSet_subset_of_compat_weight_one hE2.2.2.2.1
        (compatible_of_InX_zero hx.1.1 hE2.1 hE2.2.1) hp2.2.1
    have hnd12 : ¬ distinguishable ρ₁ ρ₂ := by
      rw [distinguishable_iff_disjoint_subcubeSet, Finset.not_disjoint_iff]
      have hne_set : (subcubeSet π).Nonempty := card_pos.mp (by rw [card_subcubeSet]; positivity)
      obtain ⟨c, hc⟩ := hne_set
      exact ⟨c, hsub1 hc, hsub2 hc⟩
    rcases lemma_compress hk hx.1 hE1.1 hE2.1 hne hnd12 with hA | hB | hC
    · exact absurd hp2.1 (by omega)
    · exact absurd hp1.1 (by omega)
    · exact absurd (h1 ρ₁ ρ₂ hC.1).2.1 (by omega)
  exact ⟨h1, h2⟩
open scoped Classical in
noncomputable def leavesFinset {k : ℕ} (x : Subcube k → ℝ) : Finset (Subcube k) :=
  (suppFinset x).filter (fun π => ∃ ρ, compEdge x ρ π)
noncomputable def rootsFinset {k : ℕ} (x : Subcube k → ℝ) : Finset (Subcube k) :=
  suppFinset x \ leavesFinset x
open scoped Classical in
noncomputable def outDeg {k : ℕ} (x : Subcube k → ℝ) (ρ : Subcube k) : ℕ :=
  ((suppFinset x).filter (fun π => compEdge x ρ π)).card
set_option maxHeartbeats 800000 in
lemma compressed_sphere_and_degrees {k : ℕ} (hk : 1 ≤ k) {x : Subcube k → ℝ} (hx : IsCompressed x) :
    IsDistinguishableSet (rootsFinset x) ∧
    (∀ ρ ∈ rootsFinset x, outDeg x ρ ≤ weight ρ ∧ (weight ρ = 1 → outDeg x ρ = 0)) ∧
    l1Sum x = (∑ ρ ∈ rootsFinset x, x ρ) + (∑ ρ ∈ rootsFinset x, (outDeg x ρ : ℝ)) ∧
    ∑ ρ ∈ rootsFinset x, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) = 0 := by
  classical
  have ⟨hstar1, hstar2⟩ := star_props hk hx
  have hR_dist : IsDistinguishableSet (rootsFinset x) := by
    refine ⟨?_, ?_⟩
    · intro τ hτ
      have hne0 : x τ ≠ 0 := (mem_filter.mp (Finset.mem_sdiff.mp hτ).1).2
      have hw0 : weight τ ≠ 0 := fun h => hne0 (InX_zero_weight_zero hx.1.1 h)
      omega
    · intro σ hσ τ hτ hne
      by_contra hnd
      have hxσ : x σ ≠ 0 := (mem_filter.mp (Finset.mem_sdiff.mp hσ).1).2
      have hxτ : x τ ≠ 0 := (mem_filter.mp (Finset.mem_sdiff.mp hτ).1).2
      have hσ_nL : σ ∉ leavesFinset x := (Finset.mem_sdiff.mp hσ).2
      have hτ_nL : τ ∉ leavesFinset x := (Finset.mem_sdiff.mp hτ).2
      rcases lemma_compress hk hx.1 hxσ hxτ hne hnd with hA | hB | hC
      ·
        have hE : compEdge x σ τ := ⟨hxσ, hxτ, hne, hnd, by rw [hA.1]; exact hx.1.1⟩
        exact hτ_nL (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hxτ⟩, σ, hE⟩)
      · have hE : compEdge x τ σ :=
          ⟨hxτ, hxσ, hne.symm, fun h => hnd (distinguishable_symm.mp h), by rw [hB.1]; exact hx.1.1⟩
        exact hσ_nL (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hxσ⟩, τ, hE⟩)
      · exact hτ_nL (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hxτ⟩, σ, hC.1⟩)
  have hleaf_root : ∀ π ∈ leavesFinset x, ∃! ρ ∈ rootsFinset x, compEdge x ρ π := by
    intro π hπ
    obtain ⟨ρ, hE⟩ := (mem_filter.mp hπ).2
    have hρ_in_R : ρ ∈ rootsFinset x := by
      refine Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hE.1⟩, ?_⟩
      intro hρL
      obtain ⟨ρ', hE'⟩ := (mem_filter.mp hρL).2
      have hwρ2 := (hstar1 ρ π hE).1
      have hwρ1 := (hstar1 ρ' ρ hE').2.1
      omega
    exact ⟨ρ, ⟨hρ_in_R, hE⟩, fun ρ' ⟨_, hE'⟩ => hstar2 ρ' ρ π hE' hE⟩
  let L_of : Subcube k → Finset (Subcube k) := fun ρ => (suppFinset x).filter (fun π => compEdge x ρ π)
  have hL_part : leavesFinset x = (rootsFinset x).biUnion L_of := by
    ext π
    simp only [mem_biUnion, L_of, mem_filter]
    constructor
    · intro hπ
      obtain ⟨ρ, ⟨hρR, hE⟩, _⟩ := hleaf_root π hπ
      exact ⟨ρ, hρR, (mem_filter.mp hπ).1, hE⟩
    · rintro ⟨ρ, _, hπs, hE⟩
      exact mem_filter.mpr ⟨hπs, ρ, hE⟩
  have hL_disj : ((rootsFinset x) : Set (Subcube k)).PairwiseDisjoint L_of := by
    intro ρ₁ _ ρ₂ _ hne
    change Disjoint (L_of ρ₁) (L_of ρ₂)
    rw [Finset.disjoint_left]
    intro π h1 h2
    exact hne (hstar2 ρ₁ ρ₂ π (mem_filter.mp h1).2 (mem_filter.mp h2).2)
  have hl1 : l1Sum x = (∑ ρ ∈ rootsFinset x, x ρ) + (∑ ρ ∈ rootsFinset x, (outDeg x ρ : ℝ)) := by
    have hsupp_eq : l1Sum x = ∑ τ ∈ suppFinset x, x τ := by
      unfold l1Sum
      symm
      exact Finset.sum_subset (subset_univ _) fun τ _ hτ => by
        by_contra hne0; exact hτ (mem_filter.mpr ⟨mem_univ _, hne0⟩)
    have hsplit : suppFinset x = rootsFinset x ∪ leavesFinset x := by
      unfold rootsFinset
      exact (Finset.sdiff_union_of_subset (filter_subset _ _)).symm
    have hdisj_RL : Disjoint (rootsFinset x) (leavesFinset x) := Finset.sdiff_disjoint
    rw [hsupp_eq, hsplit, Finset.sum_union hdisj_RL]
    congr 1
    rw [hL_part, Finset.sum_biUnion hL_disj]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    calc ∑ π ∈ L_of ρ, x π = ∑ _π ∈ L_of ρ, (1 : ℝ) :=
          Finset.sum_congr rfl fun π hπ => (hstar1 ρ π (mem_filter.mp hπ).2).2.2.1
      _ = (outDeg x ρ : ℝ) := by simp [outDeg, L_of]
  have hsphere : ∑ ρ ∈ rootsFinset x, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) = 0 := by
    have hF0 : quadForm x = 0 := quadForm_eq_zero_of_optimal hk hx.1
    rw [← hF0, quadForm_eq_indistinguishable]
    have hpair : ∑ σ : Subcube k, ∑ τ : Subcube k, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) =
        (∑ τ ∈ suppFinset x, x τ ^ 2) + 2 * ∑ ρ ∈ rootsFinset x, (outDeg x ρ : ℝ) * x ρ := by
      have h1 : ∑ σ : Subcube k, ∑ τ : Subcube k, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) =
          ∑ σ ∈ suppFinset x, ∑ τ ∈ suppFinset x, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) := by
        rw [← Finset.sum_subset (subset_univ (suppFinset x))]
        · refine Finset.sum_congr rfl fun σ _ => ?_
          symm
          exact Finset.sum_subset (subset_univ (suppFinset x)) fun τ _ hτ => by
            have h0 : x τ = 0 := by by_contra h; exact hτ (mem_filter.mpr ⟨mem_univ _, h⟩)
            simp [h0]
        · intro σ _ hσ
          have h0 : x σ = 0 := by by_contra h; exact hσ (mem_filter.mpr ⟨mem_univ _, h⟩)
          exact sum_eq_zero fun τ _ => by simp [h0]
      rw [h1]
      have hdiag : ∀ σ ∈ suppFinset x,
          ∑ τ ∈ suppFinset x, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) =
          x σ ^ 2 + ∑ τ ∈ (suppFinset x).erase σ, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) := by
        intro σ hσ
        rw [← Finset.add_sum_erase _ _ hσ]
        simp [not_distinguishable_self, sq]
      rw [Finset.sum_congr rfl hdiag, sum_add_distrib]
      congr 1
      have hoff_iff : ∀ σ ∈ suppFinset x, ∀ τ ∈ suppFinset x, σ ≠ τ →
          (¬ distinguishable σ τ ↔ compEdge x σ τ ∨ compEdge x τ σ) := by
        intro σ hσ τ hτ hne
        have hxσ := (mem_filter.mp hσ).2
        have hxτ := (mem_filter.mp hτ).2
        constructor
        · intro hnd
          rcases lemma_compress hk hx.1 hxσ hxτ hne hnd with hA | hB | hC
          · exact Or.inl ⟨hxσ, hxτ, hne, hnd, by rw [hA.1]; exact hx.1.1⟩
          · exact Or.inr ⟨hxτ, hxσ, hne.symm, fun h => hnd (distinguishable_symm.mp h),
              by rw [hB.1]; exact hx.1.1⟩
          · exact Or.inl hC.1
        · rintro (hE | hE)
          · exact hE.2.2.2.1
          · exact fun h => hE.2.2.2.1 (distinguishable_symm.mp h)
      have hsplit : suppFinset x = rootsFinset x ∪ leavesFinset x :=
        (Finset.sdiff_union_of_subset (filter_subset _ _)).symm
      have hdisj_RL : Disjoint (rootsFinset x) (leavesFinset x) := Finset.sdiff_disjoint
      have htot_eq :
          (∑ σ ∈ suppFinset x, ∑ τ ∈ (suppFinset x).erase σ, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ)) =
          (∑ σ ∈ rootsFinset x, ∑ τ ∈ (suppFinset x).erase σ, (if distinguishable σ τ then (0 : ℝ) else x σ * x τ)) +
          (∑ π ∈ leavesFinset x, ∑ τ ∈ (suppFinset x).erase π, (if distinguishable π τ then (0 : ℝ) else x π * x τ)) := by
        rw [← Finset.sum_union hdisj_RL, ← hsplit]
      rw [htot_eq]
      have hR_sum : ∑ σ ∈ rootsFinset x, ∑ τ ∈ (suppFinset x).erase σ,
          (if distinguishable σ τ then (0 : ℝ) else x σ * x τ) =
          ∑ ρ ∈ rootsFinset x, (outDeg x ρ : ℝ) * x ρ := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hρs : ρ ∈ suppFinset x := (Finset.mem_sdiff.mp hρ).1
        have hsub : L_of ρ ⊆ (suppFinset x).erase ρ := fun π hπ =>
          mem_erase.mpr ⟨(mem_filter.mp hπ).2.2.2.1.symm, (mem_filter.mp hπ).1⟩
        rw [← Finset.sum_subset hsub]
        · calc ∑ π ∈ L_of ρ, (if distinguishable ρ π then (0 : ℝ) else x ρ * x π)
              = ∑ π ∈ L_of ρ, x ρ := by
                refine Finset.sum_congr rfl fun π hπ => ?_
                have hE := (mem_filter.mp hπ).2
                rw [if_neg hE.2.2.2.1, (hstar1 ρ π hE).2.2.1, mul_one]
            _ = (outDeg x ρ : ℝ) * x ρ := by simp [outDeg, L_of]
        · intro τ hτ hnotL
          have hτs := Finset.mem_of_mem_erase hτ
          have hne := (Finset.ne_of_mem_erase hτ).symm
          by_cases hd : distinguishable ρ τ
          · rw [if_pos hd]
          · exfalso
            rcases (hoff_iff ρ hρs τ hτs hne).mp hd with hE | hE
            · exact hnotL (mem_filter.mpr ⟨hτs, hE⟩)
            · exact (Finset.mem_sdiff.mp hρ).2 (mem_filter.mpr ⟨hρs, τ, hE⟩)
      have hL_sum : ∑ π ∈ leavesFinset x, ∑ τ ∈ (suppFinset x).erase π,
          (if distinguishable π τ then (0 : ℝ) else x π * x τ) =
          ∑ ρ ∈ rootsFinset x, (outDeg x ρ : ℝ) * x ρ := by
        rw [hL_part, Finset.sum_biUnion hL_disj]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        calc ∑ π ∈ L_of ρ, ∑ τ ∈ (suppFinset x).erase π,
              (if distinguishable π τ then (0 : ℝ) else x π * x τ)
            = ∑ π ∈ L_of ρ, x ρ := by
              refine Finset.sum_congr rfl fun π hπ => ?_
              have hE := (mem_filter.mp hπ).2
              have hπs := (mem_filter.mp hπ).1
              have hρ_in : ρ ∈ (suppFinset x).erase π :=
                mem_erase.mpr ⟨hE.2.2.1, (Finset.mem_sdiff.mp hρ).1⟩
              rw [Finset.sum_eq_single ρ]
              · rw [if_neg (fun h => hE.2.2.2.1 (distinguishable_symm.mp h)),
                    (hstar1 ρ π hE).2.2.1, one_mul]
              · intro τ hτ hneρ
                have hτs := Finset.mem_of_mem_erase hτ
                have hneπ := (Finset.ne_of_mem_erase hτ).symm
                by_cases hd : distinguishable π τ
                · rw [if_pos hd]
                · exfalso
                  rcases (hoff_iff π hπs τ hτs hneπ).mp hd with hE' | hE'
                  · have hwπ2 := (hstar1 π τ hE').1
                    have hwπ1 := (hstar1 ρ π hE).2.1
                    omega
                  · exact hneρ (hstar2 τ ρ π hE' hE)
              · intro h; exact absurd hρ_in h
          _ = (outDeg x ρ : ℝ) * x ρ := by simp [outDeg, L_of]
      rw [hR_sum, hL_sum]; ring
    have hw_sum : ∑ τ : Subcube k, (weight τ : ℝ) * x τ = ∑ τ ∈ suppFinset x, (weight τ : ℝ) * x τ := by
      symm
      exact Finset.sum_subset (subset_univ _) fun τ _ hτ => by
        have h0 : x τ = 0 := by by_contra h; exact hτ (mem_filter.mpr ⟨mem_univ _, h⟩)
        simp [h0]
    have hsplit : suppFinset x = rootsFinset x ∪ leavesFinset x :=
      (Finset.sdiff_union_of_subset (filter_subset _ _)).symm
    have hL_cancel : ∑ π ∈ leavesFinset x, x π ^ 2 = ∑ π ∈ leavesFinset x, (weight π : ℝ) * x π := by
      refine Finset.sum_congr rfl fun π hπ => ?_
      obtain ⟨ρ, hE⟩ := (mem_filter.mp hπ).2
      have hp := hstar1 ρ π hE
      rw [hp.2.1, hp.2.2.1]; norm_num
    have hdisj_RL : Disjoint (rootsFinset x) (leavesFinset x) := Finset.sdiff_disjoint
    rw [hpair, hw_sum, hsplit, Finset.sum_union hdisj_RL,
        Finset.sum_union hdisj_RL, hL_cancel]
    have hcomb : ((∑ τ ∈ rootsFinset x, x τ ^ 2) + ∑ π ∈ leavesFinset x, (weight π : ℝ) * x π) +
        2 * ∑ ρ ∈ rootsFinset x, (outDeg x ρ : ℝ) * x ρ -
        ((∑ τ ∈ rootsFinset x, (weight τ : ℝ) * x τ) + ∑ π ∈ leavesFinset x, (weight π : ℝ) * x π) =
        ∑ ρ ∈ rootsFinset x, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) := by
      rw [mul_sum]
      have h1 : (∑ τ ∈ rootsFinset x, x τ ^ 2) + (∑ ρ ∈ rootsFinset x, 2 * ((outDeg x ρ : ℝ) * x ρ)) -
          (∑ τ ∈ rootsFinset x, (weight τ : ℝ) * x τ) =
          ∑ ρ ∈ rootsFinset x, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) := by
        rw [← sum_add_distrib, ← sum_sub_distrib]
        refine Finset.sum_congr rfl fun ρ _ => by ring
      linarith
    exact hcomb.symm
  have hdeg0 : ∀ ρ ∈ rootsFinset x, outDeg x ρ ≤ 2 ^ (weight ρ - 1) := by
    intro ρ hρ
    by_cases hd0 : outDeg x ρ = 0
    · rw [hd0]; exact Nat.zero_le _
    · have hL_dist : (L_of ρ : Set (Subcube k)).PairwiseDisjoint subcubeSet := by
        intro π₁ hπ₁ π₂ hπ₂ hne
        change Disjoint (subcubeSet π₁) (subcubeSet π₂)
        rw [← distinguishable_iff_disjoint_subcubeSet]
        by_contra hnd
        have hE1 := (mem_filter.mp hπ₁).2
        have hE2 := (mem_filter.mp hπ₂).2
        have hp1 := hstar1 ρ π₁ hE1
        have hp2 := hstar1 ρ π₂ hE2
        exact hne (eq_of_weight_one_compat hnd (compatible_of_InX_zero hx.1.1 hE1.2.1 hE2.2.1) hp1.2.1 hp2.2.1)
      have hsub_Q : (L_of ρ).biUnion subcubeSet ⊆ subcubeSet ρ := by
        rw [biUnion_subset]
        intro π hπ
        have hE := (mem_filter.mp hπ).2
        exact subcubeSet_subset_of_compat_weight_one hE.2.2.2.1
          (compatible_of_InX_zero hx.1.1 hE.1 hE.2.1) (hstar1 ρ π hE).2.1
      have hcard_le := card_le_card hsub_Q
      rw [card_biUnion hL_dist, card_subcubeSet] at hcard_le
      have hlhs : ∑ π ∈ L_of ρ, (subcubeSet π).card = 2 * outDeg x ρ := by
        calc ∑ π ∈ L_of ρ, (subcubeSet π).card
            = ∑ π ∈ L_of ρ, 2 := Finset.sum_congr rfl fun π hπ => by
              rw [card_subcubeSet, (hstar1 ρ π (mem_filter.mp hπ).2).2.1]; norm_num
          _ = 2 * outDeg x ρ := by simp [outDeg, L_of, mul_comm]
      rw [hlhs] at hcard_le
      have hwρ1 : 1 ≤ weight ρ := hR_dist.1 ρ hρ
      have hpow : 2 ^ weight ρ = 2 * 2 ^ (weight ρ - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hwρ1, pow_succ']
      omega
  have hdeg : ∀ ρ ∈ rootsFinset x, outDeg x ρ ≤ weight ρ ∧ (weight ρ = 1 → outDeg x ρ = 0) := by
    intro σ hσ
    have hw1_0 : weight σ = 1 → outDeg x σ = 0 := by
      intro hw1
      rw [outDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro π _ hE
      have := (hstar1 σ π hE).1
      omega
    refine ⟨?_, hw1_0⟩
    by_contra hgt
    push Not at hgt
    have h0 := hdeg0 σ hσ
    have hwσ3 : 3 ≤ weight σ := by
      by_contra hlt3
      have h1 := hR_dist.1 σ hσ
      have : weight σ = 1 ∨ weight σ = 2 := by omega
      rcases this with hw1 | hw2
      · have := hw1_0 hw1; omega
      · rw [hw2] at h0; norm_num at h0; omega
    let Wσ := Finset.univ.filter (fun i : Fin k => σ i = 2)
    have hWσ_card : 3 ≤ Wσ.card := hwσ3
    obtain ⟨i1, hi1⟩ := card_pos.mp (by omega : 0 < Wσ.card)
    obtain ⟨i2, hi2⟩ := card_pos.mp (by rw [card_erase_of_mem hi1]; omega : 0 < (Wσ.erase i1).card)
    have hi12 : i1 ≠ i2 := (Finset.ne_of_mem_erase hi2).symm
    have hσi1 : σ i1 = 2 := (mem_filter.mp hi1).2
    have hσi2 : σ i2 = 2 := (mem_filter.mp (Finset.mem_of_mem_erase hi2)).2
    let π_new : Subcube k := fun i =>
      if i = i1 ∨ i = i2 then 2 else if σ i = 2 then 0 else σ i
    have hπ_w : weight π_new = 2 := by
      have heq : Finset.univ.filter (fun i : Fin k => π_new i = 2) = {i1, i2} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, π_new]
        split_ifs with h1 h2
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
        · exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
      rw [weight, heq, card_pair hi12]
    let Q1 : Finset (Subcube k) :=
      Finset.univ.filter (fun τ : Subcube k =>
        τ i1 = 2 ∧ ∀ i : Fin k, i ≠ i1 → (σ i = 2 → τ i = 0 ∨ τ i = 1) ∧ (σ i ≠ 2 → τ i = σ i))
    have hQ1_w1 : ∀ τ ∈ Q1, weight τ = 1 := by
      intro τ hτ
      have h := (mem_filter.mp hτ).2
      have heq : Finset.univ.filter (fun i : Fin k => τ i = 2) = {i1} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hi2'
          by_contra hne
          by_cases hσ2 : σ i = 2
          · rcases (h.2 i hne).1 hσ2 with h0' | h1' <;> simp_all
          · rw [(h.2 i hne).2 hσ2] at hi2'; exact hσ2 hi2'
        · rintro rfl; exact h.1
      rw [weight, heq, card_singleton]
    have hQ1_card : Q1.card = 2 ^ (weight σ - 1) := by
      let Wrest := Wσ.erase i1
      have hbij : Q1.card = Fintype.card (Wrest → Bool) := by
        refine Finset.card_bij (fun τ _ => fun i : Wrest => decide (τ i.val = 1)) ?_ ?_ ?_
        · intro _ _; exact mem_univ _
        · intro τ₁ hτ₁ τ₂ hτ₂ heq
          have h1 := (mem_filter.mp hτ₁).2
          have h2 := (mem_filter.mp hτ₂).2
          funext i
          by_cases hi : i = i1
          · subst hi; rw [h1.1, h2.1]
          · by_cases hσ2 : σ i = 2
            · have hiW : i ∈ Wrest := mem_erase.mpr ⟨hi, mem_filter.mpr ⟨mem_univ _, hσ2⟩⟩
              have hb := congrFun heq ⟨i, hiW⟩
              rcases (h1.2 i hi).1 hσ2 with a | a <;> rcases (h2.2 i hi).1 hσ2 with b | b <;> simp_all
            · rw [(h1.2 i hi).2 hσ2, (h2.2 i hi).2 hσ2]
        · intro g _
          let τ : Subcube k := fun i =>
            if hi : i = i1 then 2
            else if h2 : σ i = 2 then
              if g ⟨i, mem_erase.mpr ⟨hi, mem_filter.mpr ⟨mem_univ _, h2⟩⟩⟩ then 1 else 0
            else σ i
          refine ⟨τ, mem_filter.mpr ⟨mem_univ _, by simp [τ], fun i hi => ?_⟩, ?_⟩
          · constructor
            · intro h2; simp only [τ, dif_neg hi, dif_pos h2]; split_ifs <;> simp
            · intro h2; simp only [τ, dif_neg hi, dif_neg h2]
          · funext ⟨i, hi⟩
            have hne := Finset.ne_of_mem_erase hi
            have h2 := (mem_filter.mp (Finset.mem_of_mem_erase hi)).2
            simp only [τ, dif_neg hne, dif_pos h2]
            cases g ⟨i, hi⟩ <;> simp
      rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
          card_erase_of_mem hi1]
      rfl
    have hQ1_dist : ∀ τ₁ ∈ Q1, ∀ τ₂ ∈ Q1, τ₁ ≠ τ₂ → distinguishable τ₁ τ₂ := by
      intro τ₁ h1 τ₂ h2 hne
      have hp1 := (mem_filter.mp h1).2
      have hp2 := (mem_filter.mp h2).2
      have hex_i : ∃ i, τ₁ i ≠ τ₂ i := by
        by_contra hall; push Not at hall; exact hne (funext hall)
      obtain ⟨i, hi⟩ := hex_i
      have hne1 : i ≠ i1 := by rintro rfl; exact hi (hp1.1.trans hp2.1.symm)
      have hσ2 : σ i = 2 := by
        by_contra hn2; exact hi ((hp1.2 i hne1).2 hn2 |>.trans ((hp2.2 i hne1).2 hn2).symm)
      rcases (hp1.2 i hne1).1 hσ2 with a | a <;> rcases (hp2.2 i hne1).1 hσ2 with b | b
      · exact absurd (a.trans b.symm) hi
      · exact ⟨i, Or.inl ⟨a, b⟩⟩
      · exact ⟨i, Or.inr ⟨a, b⟩⟩
      · exact absurd (a.trans b.symm) hi
    have hsub_Q1 : ∀ τ ∈ Q1, subcubeSet τ ⊆ subcubeSet σ := by
      intro τ hτ c hc
      have hp := (mem_filter.mp hτ).2
      have hcτ := (mem_filter.mp hc).2
      refine mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩
      by_cases hi : i = i1
      · subst hi; simp [hσi1]
      · by_cases hσ2 : σ i = 2
        · simp [hσ2]
        · rw [← (hp.2 i hi).2 hσ2]; exact hcτ i
    have hsub_π : subcubeSet π_new ⊆ subcubeSet σ := by
      intro c hc
      have hcπ := (mem_filter.mp hc).2
      refine mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩
      by_cases hσ2 : σ i = 2
      · simp [hσ2]
      · have hne12 : ¬ (i = i1 ∨ i = i2) := by rintro (rfl | rfl) <;> contradiction
        have heq : π_new i = σ i := by simp [π_new, hne12, hσ2]
        rw [← heq]; exact hcπ i
    let Q1_ind : Finset (Subcube k) := Q1.filter (fun τ => ¬ distinguishable π_new τ)
    have hQ1_ind_card : Q1_ind.card = 2 := by
      let τ0 : Subcube k := fun i => if i = i1 then 2 else if σ i = 2 then 0 else σ i
      let τ1 : Subcube k := fun i => if i = i1 then 2 else if i = i2 then 1 else if σ i = 2 then 0 else σ i
      have hne01 : τ0 ≠ τ1 := by
        intro heq
        have := congrFun heq i2
        simp [τ0, τ1, hi12.symm, hσi2] at this
      have heq_set : Q1_ind = {τ0, τ1} := by
        ext τ
        simp only [Q1_ind, mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hτQ1, hnd⟩
          have hp := (mem_filter.mp hτQ1).2
          have hrest0 : ∀ i, i ≠ i1 → i ≠ i2 → σ i = 2 → τ i = 0 := by
            intro i h1 h2 hσ2
            rcases (hp.2 i h1).1 hσ2 with h0' | h1'
            · exact h0'
            · exfalso; apply hnd; refine ⟨i, Or.inl ⟨?_, h1'⟩⟩
              simp [π_new, h1, h2, hσ2]
          rcases (hp.2 i2 hi12.symm).1 hσi2 with hi2_0 | hi2_1
          · left; funext i
            by_cases h1 : i = i1
            · subst h1; simp [τ0, hp.1]
            · by_cases h2 : i = i2
              · subst h2; simp [τ0, h1, hσi2, hi2_0]
              · by_cases hσ2 : σ i = 2
                · simp [τ0, h1, hσ2, hrest0 i h1 h2 hσ2]
                · simp [τ0, h1, hσ2, (hp.2 i h1).2 hσ2]
          · right; funext i
            by_cases h1 : i = i1
            · subst h1; simp [τ1, hp.1]
            · by_cases h2 : i = i2
              · subst h2; simp [τ1, h1, hi2_1]
              · by_cases hσ2 : σ i = 2
                · simp [τ1, h1, h2, hσ2, hrest0 i h1 h2 hσ2]
                · simp [τ1, h1, h2, hσ2, (hp.2 i h1).2 hσ2]
        · rintro (rfl | rfl)
          · refine ⟨mem_filter.mpr ⟨mem_univ _, by simp [τ0], fun i hi => ?_⟩, ?_⟩
            · constructor
              · intro h2; left; simp [τ0, hi, h2]
              · intro h2; simp [τ0, hi, h2]
            · rintro ⟨i, ⟨h0', h1'⟩ | ⟨h1', h0'⟩⟩
              · dsimp only [π_new, τ0] at h0' h1'
                by_cases hi1' : i = i1 <;> by_cases hi2' : i = i2 <;> by_cases hσ2 : σ i = 2 <;>
                simp only [hi1', hi2', hσ2, or_true, true_or, or_false, false_or, ite_true, ite_false] at h0' h1' <;>
                first | exact absurd h0' (by decide) | exact absurd h1' (by decide) | exact absurd (h0'.symm.trans h1') (by decide)
              · dsimp only [π_new, τ0] at h0' h1'
                by_cases hi1' : i = i1 <;> by_cases hi2' : i = i2 <;> by_cases hσ2 : σ i = 2 <;>
                simp only [hi1', hi2', hσ2, or_true, true_or, or_false, false_or, ite_true, ite_false] at h0' h1' <;>
                first | exact absurd h0' (by decide) | exact absurd h1' (by decide) | exact absurd (h0'.symm.trans h1') (by decide)
          · refine ⟨mem_filter.mpr ⟨mem_univ _, by simp [τ1], fun i hi => ?_⟩, ?_⟩
            · constructor
              · intro h2; simp only [τ1, if_neg hi, if_pos h2]; split_ifs <;> simp
              · intro h2
                have hne2 : i ≠ i2 := by rintro rfl; exact h2 hσi2
                simp [τ1, hi, hne2, h2]
            · rintro ⟨i, ⟨h0', h1'⟩ | ⟨h1', h0'⟩⟩
              · dsimp only [π_new, τ1] at h0' h1'
                by_cases hi1' : i = i1 <;> by_cases hi2' : i = i2 <;> by_cases hσ2 : σ i = 2 <;>
                simp only [hi1', hi2', hσ2, or_true, true_or, or_false, false_or, ite_true, ite_false] at h0' h1' <;>
                first | exact absurd h0' (by decide) | exact absurd h1' (by decide) | exact absurd (h0'.symm.trans h1') (by decide)
              · dsimp only [π_new, τ1] at h0' h1'
                by_cases hi1' : i = i1 <;> by_cases hi2' : i = i2 <;> by_cases hσ2 : σ i = 2 <;>
                simp only [hi1', hi2', hσ2, or_true, true_or, or_false, false_or, ite_true, ite_false] at h0' h1' <;>
                first | exact absurd h0' (by decide) | exact absurd h1' (by decide) | exact absurd (h0'.symm.trans h1') (by decide)
      rw [heq_set, card_pair hne01]
    let R_rest := (rootsFinset x).erase σ
    let S_rest := R_rest ∪ R_rest.biUnion L_of
    have hrest_dist_σ : ∀ τ ∈ S_rest, distinguishable σ τ := by
      intro τ hτ
      rcases mem_union.mp hτ with hR | hL
      · exact hR_dist.2 σ hσ τ (Finset.mem_of_mem_erase hR) (Finset.ne_of_mem_erase hR).symm
      · rcases mem_biUnion.mp hL with ⟨ρ, hρ, hπ⟩
        have hρR := Finset.mem_of_mem_erase hρ
        have hne := (Finset.ne_of_mem_erase hρ).symm
        have hdist_σρ : distinguishable σ ρ := hR_dist.2 σ hσ ρ hρR hne
        rw [distinguishable_iff_disjoint_subcubeSet] at hdist_σρ ⊢
        have hE := (mem_filter.mp hπ).2
        exact hdist_σρ.mono_right (subcubeSet_subset_of_compat_weight_one hE.2.2.2.1
          (compatible_of_InX_zero hx.1.1 hE.1 hE.2.1) (hstar1 ρ τ hE).2.1)
    have hnew_dist_rest : ∀ α ∈ insert π_new Q1, ∀ τ ∈ S_rest, distinguishable α τ := by
      intro α hα τ hτ
      have hσd := hrest_dist_σ τ hτ
      rw [distinguishable_iff_disjoint_subcubeSet] at hσd ⊢
      rcases mem_insert.mp hα with rfl | hQ
      · exact hσd.mono_left hsub_π
      · exact hσd.mono_left (hsub_Q1 α hQ)
    have hπ_not_Q1 : π_new ∉ Q1 := fun h => by have := hQ1_w1 π_new h; omega
    let x' : Subcube k → ℝ := fun τ =>
      if τ = π_new then x σ
      else if τ ∈ Q1 then 1
      else if τ ∈ S_rest then x τ
      else 0
    have hx'_nonneg : ∀ τ, 0 ≤ x' τ := by
      intro τ; dsimp only [x']; split_ifs <;> linarith [hx.1.1.1 σ, hx.1.1.1 τ]
    have hx'_w0 : ∀ τ, weight τ = 0 → x' τ = 0 := by
      intro τ h0
      dsimp only [x']
      split_ifs with h1 h2 h3
      · subst h1; omega
      · have := hQ1_w1 τ h2; omega
      · exact InX_zero_weight_zero hx.1.1 h0
      · rfl
    have hx'_w1 : ∀ τ, weight τ = 1 → x' τ ≤ 1 + 0 := by
      intro τ h1
      dsimp only [x']
      split_ifs with ha hb hc
      · subst ha; omega
      · norm_num
      · exact hx.1.1.2.2.1 τ h1
      · norm_num
    have hx'_compat : ∀ α β, ¬ compatible α β → x' α * x' β ≤ 0 := by
      intro α β hnc
      by_cases ha : α ∈ insert π_new Q1
      · by_cases hb : β ∈ insert π_new Q1
        ·
          have hi1a : α i1 = 2 := by
            rcases mem_insert.mp ha with rfl | hQ
            · simp [π_new]
            · exact (mem_filter.mp hQ).2.1
          have hi1b : β i1 = 2 := by
            rcases mem_insert.mp hb with rfl | hQ
            · simp [π_new]
            · exact (mem_filter.mp hQ).2.1
          exact absurd (Or.inr ⟨i1, hi1a, hi1b⟩) hnc
        · by_cases hbS : β ∈ S_rest
          · exact absurd (Or.inl (hnew_dist_rest α ha β hbS)) hnc
          · have hβ0 : x' β = 0 := by
              have h1 : β ≠ π_new := fun h => hb (mem_insert.mpr (Or.inl h))
              have h2 : β ∉ Q1 := fun h => hb (mem_insert.mpr (Or.inr h))
              simp [x', h1, h2, hbS]
            rw [hβ0, mul_zero]
      · by_cases haS : α ∈ S_rest
        · by_cases hb : β ∈ insert π_new Q1
          · exact absurd (Or.inl (distinguishable_symm.mp (hnew_dist_rest β hb α haS))) hnc
          · by_cases hbS : β ∈ S_rest
            · have hα_eq : x' α = x α := by
                have h1 : α ≠ π_new := fun h => ha (mem_insert.mpr (Or.inl h))
                have h2 : α ∉ Q1 := fun h => ha (mem_insert.mpr (Or.inr h))
                simp [x', h1, h2, haS]
              have hβ_eq : x' β = x β := by
                have h1 : β ≠ π_new := fun h => hb (mem_insert.mpr (Or.inl h))
                have h2 : β ∉ Q1 := fun h => hb (mem_insert.mpr (Or.inr h))
                simp [x', h1, h2, hbS]
              rw [hα_eq, hβ_eq]; exact hx.1.1.2.2.2 α β hnc
            · have hβ0 : x' β = 0 := by
                have h1 : β ≠ π_new := fun h => hb (mem_insert.mpr (Or.inl h))
                have h2 : β ∉ Q1 := fun h => hb (mem_insert.mpr (Or.inr h))
                simp [x', h1, h2, hbS]
              rw [hβ0, mul_zero]
        · have hα0 : x' α = 0 := by
            have h1 : α ≠ π_new := fun h => ha (mem_insert.mpr (Or.inl h))
            have h2 : α ∉ Q1 := fun h => ha (mem_insert.mpr (Or.inr h))
            simp [x', h1, h2, haS]
          rw [hα0, zero_mul]
    have hdisj_new_rest : Disjoint (insert π_new Q1) S_rest := by
      rw [Finset.disjoint_left]
      intro τ h1 h2
      exact not_distinguishable_self τ (hnew_dist_rest τ h1 τ h2)
    have hFx' : quadForm x' =
        (x σ ^ 2 + 2 * x σ) +
        ∑ ρ ∈ R_rest, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) := by
      rw [quadForm_eq_indistinguishable]
      let U := insert π_new Q1 ∪ S_rest
      have hout0 : ∀ τ, τ ∉ U → x' τ = 0 := by
        intro τ hτ
        have h1 : τ ≠ π_new := fun h => hτ (mem_union_left _ (mem_insert.mpr (Or.inl h)))
        have h2 : τ ∉ Q1 := fun h => hτ (mem_union_left _ (mem_insert.mpr (Or.inr h)))
        have h3 : τ ∉ S_rest := fun h => hτ (mem_union_right _ h)
        simp [x', h1, h2, h3]
      have hquad_split :
          (∑ α : Subcube k, ∑ β : Subcube k, if distinguishable α β then (0 : ℝ) else x' α * x' β) -
          (∑ τ : Subcube k, (weight τ : ℝ) * x' τ) =
          ((∑ α ∈ insert π_new Q1, ∑ β ∈ insert π_new Q1, if distinguishable α β then (0 : ℝ) else x' α * x' β) -
            ∑ τ ∈ insert π_new Q1, (weight τ : ℝ) * x' τ) +
          ((∑ α ∈ S_rest, ∑ β ∈ S_rest, if distinguishable α β then (0 : ℝ) else x' α * x' β) -
            ∑ τ ∈ S_rest, (weight τ : ℝ) * x' τ) := by
        have hsum1 : ∑ α : Subcube k, ∑ β : Subcube k, (if distinguishable α β then (0 : ℝ) else x' α * x' β) =
            ∑ α ∈ U, ∑ β ∈ U, (if distinguishable α β then (0 : ℝ) else x' α * x' β) := by
          rw [← Finset.sum_subset (subset_univ U)]
          · refine Finset.sum_congr rfl fun α _ => ?_
            symm
            exact Finset.sum_subset (subset_univ U) fun β _ hβ => by rw [hout0 β hβ, mul_zero, ite_self]
          · intro α _ hα
            exact sum_eq_zero fun β _ => by rw [hout0 α hα, zero_mul, ite_self]
        have hsum2 : ∑ τ : Subcube k, (weight τ : ℝ) * x' τ = ∑ τ ∈ U, (weight τ : ℝ) * x' τ := by
          symm
          exact Finset.sum_subset (subset_univ U) fun τ _ hτ => by rw [hout0 τ hτ, mul_zero]
        rw [hsum1, hsum2, Finset.sum_union hdisj_new_rest, Finset.sum_union hdisj_new_rest]
        have hA : ∑ α ∈ insert π_new Q1, ∑ β ∈ U, (if distinguishable α β then (0 : ℝ) else x' α * x' β) =
            ∑ α ∈ insert π_new Q1, ∑ β ∈ insert π_new Q1, (if distinguishable α β then (0 : ℝ) else x' α * x' β) := by
          refine Finset.sum_congr rfl fun α hα => ?_
          rw [Finset.sum_union hdisj_new_rest]
          have h0 : ∑ β ∈ S_rest, (if distinguishable α β then (0 : ℝ) else x' α * x' β) = 0 :=
            sum_eq_zero fun β hβ => by rw [if_pos (hnew_dist_rest α hα β hβ)]
          linarith
        have hB : ∑ α ∈ S_rest, ∑ β ∈ U, (if distinguishable α β then (0 : ℝ) else x' α * x' β) =
            ∑ α ∈ S_rest, ∑ β ∈ S_rest, (if distinguishable α β then (0 : ℝ) else x' α * x' β) := by
          refine Finset.sum_congr rfl fun α hα => ?_
          rw [Finset.sum_union hdisj_new_rest]
          have h0 : ∑ β ∈ insert π_new Q1, (if distinguishable α β then (0 : ℝ) else x' α * x' β) = 0 :=
            sum_eq_zero fun β hβ => by rw [if_pos (distinguishable_symm.mp (hnew_dist_rest β hβ α hα))]
          linarith
        rw [hA, hB]; ring
      rw [hquad_split]
      have hpart1 :
          (∑ α ∈ insert π_new Q1, ∑ β ∈ insert π_new Q1, if distinguishable α β then (0 : ℝ) else x' α * x' β) -
          ∑ τ ∈ insert π_new Q1, (weight τ : ℝ) * x' τ = x σ ^ 2 + 2 * x σ := by
        have hx'π : x' π_new = x σ := by simp [x']
        have hx'Q1 : ∀ τ ∈ Q1, x' τ = 1 := fun τ hτ => by
          have hne : τ ≠ π_new := fun h => hπ_not_Q1 (h ▸ hτ)
          simp [x', hne, hτ]
        have hrow_π : ∑ β ∈ insert π_new Q1, (if distinguishable π_new β then (0 : ℝ) else x' π_new * x' β) =
            x σ ^ 2 + 2 * x σ := by
          rw [sum_insert hπ_not_Q1, if_neg (not_distinguishable_self _), hx'π, ← sq]
          congr 1
          calc ∑ β ∈ Q1, (if distinguishable π_new β then (0 : ℝ) else x σ * x' β)
              = ∑ β ∈ Q1, (if ¬ distinguishable π_new β then x σ else 0) := by
                refine Finset.sum_congr rfl fun β hβ => ?_
                rw [hx'Q1 β hβ, mul_one]
                split_ifs <;> simp_all
            _ = (Q1_ind.card : ℝ) * x σ := by
                rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
            _ = 2 * x σ := by rw [hQ1_ind_card]; norm_num
        have hrows_Q1 : ∑ α ∈ Q1, ∑ β ∈ insert π_new Q1,
            (if distinguishable α β then (0 : ℝ) else x' α * x' β) =
            2 * x σ + (Q1.card : ℝ) := by
          have hrow : ∀ α ∈ Q1, ∑ β ∈ insert π_new Q1, (if distinguishable α β then (0 : ℝ) else x' α * x' β) =
              (if distinguishable α π_new then (0 : ℝ) else x σ) + 1 := by
            intro α hα
            rw [sum_insert hπ_not_Q1, hx'Q1 α hα, hx'π, one_mul]
            congr 1
            rw [Finset.sum_eq_single α]
            · simp [not_distinguishable_self, hx'Q1 α hα]
            · intro β hβ hne
              rw [if_pos (hQ1_dist α hα β hβ hne.symm)]
            · intro h; exact absurd hα h
          rw [Finset.sum_congr rfl hrow, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
          congr 1
          calc ∑ α ∈ Q1, (if distinguishable α π_new then (0 : ℝ) else x σ)
              = ∑ α ∈ Q1, (if ¬ distinguishable π_new α then x σ else 0) := by
                refine Finset.sum_congr rfl fun α _ => ?_
                by_cases hd : distinguishable π_new α
                · rw [if_pos (distinguishable_symm.mp hd), if_neg (not_not.mpr hd)]
                · rw [if_neg (fun h => hd (distinguishable_symm.mp h)), if_pos hd]
            _ = (Q1_ind.card : ℝ) * x σ := by
                rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
            _ = 2 * x σ := by rw [hQ1_ind_card]; norm_num
        have hw_Q1 : ∑ τ ∈ Q1, (weight τ : ℝ) * x' τ = (Q1.card : ℝ) := by
          calc ∑ τ ∈ Q1, (weight τ : ℝ) * x' τ = ∑ _τ ∈ Q1, (1 : ℝ) :=
                Finset.sum_congr rfl fun τ hτ => by rw [hQ1_w1 τ hτ, hx'Q1 τ hτ]; norm_num
            _ = (Q1.card : ℝ) := by simp
        have houter1 := sum_insert
          (f := fun α => ∑ β ∈ insert π_new Q1, if distinguishable α β then (0 : ℝ) else x' α * x' β) hπ_not_Q1
        have houter2 := sum_insert (f := fun τ => (weight τ : ℝ) * x' τ) hπ_not_Q1
        rw [houter1, houter2, hrow_π, hrows_Q1, hw_Q1, hx'π, hπ_w]
        norm_num
      have hpart2 :
          (∑ α ∈ S_rest, ∑ β ∈ S_rest, if distinguishable α β then (0 : ℝ) else x' α * x' β) -
          ∑ τ ∈ S_rest, (weight τ : ℝ) * x' τ =
          ∑ ρ ∈ R_rest, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) := by
        have hx'S : ∀ τ ∈ S_rest, x' τ = x τ := fun τ hτ => by
          have hnot : τ ∉ insert π_new Q1 := Finset.disjoint_right.mp hdisj_new_rest hτ
          have h1 : τ ≠ π_new := fun h => hnot (mem_insert.mpr (Or.inl h))
          have h2 : τ ∉ Q1 := fun h => hnot (mem_insert.mpr (Or.inr h))
          simp [x', h1, h2, hτ]
        have hS_eq : ∀ f : Subcube k → Subcube k → ℝ,
            (∑ α ∈ S_rest, ∑ β ∈ S_rest, f α β) = ∑ α ∈ S_rest, ∑ β ∈ S_rest, f α β := fun _ => rfl
        have h1 : ∑ α ∈ S_rest, ∑ β ∈ S_rest, (if distinguishable α β then (0 : ℝ) else x' α * x' β) =
            ∑ α ∈ S_rest, ∑ β ∈ S_rest, (if distinguishable α β then (0 : ℝ) else x α * x β) :=
          Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β hβ => by rw [hx'S α hα, hx'S β hβ]
        have h2 : ∑ τ ∈ S_rest, (weight τ : ℝ) * x' τ = ∑ τ ∈ S_rest, (weight τ : ℝ) * x τ :=
          Finset.sum_congr rfl fun τ hτ => by rw [hx'S τ hτ]
        rw [h1, h2]
        have hdisj_RL : Disjoint (rootsFinset x) (leavesFinset x) := Finset.sdiff_disjoint
        have hdisj_RL' : Disjoint R_rest (R_rest.biUnion L_of) :=
          Disjoint.mono (Finset.erase_subset σ _)
            (by rw [hL_part]; exact Finset.biUnion_subset_biUnion_of_subset_left L_of (Finset.erase_subset σ _))
            hdisj_RL
        have hL_disj' : (R_rest : Set (Subcube k)).PairwiseDisjoint L_of :=
          hL_disj.subset (Finset.erase_subset σ _)
        have hS_sub : S_rest ⊆ suppFinset x := by
          refine union_subset ((Finset.erase_subset σ _).trans (sdiff_subset)) ?_
          rw [biUnion_subset]
          intro ρ _
          exact filter_subset _ _
        have hquad_S : ∑ α ∈ S_rest, ∑ β ∈ S_rest, (if distinguishable α β then (0 : ℝ) else x α * x β) =
            (∑ τ ∈ S_rest, x τ ^ 2) + 2 * ∑ ρ ∈ R_rest, (outDeg x ρ : ℝ) * x ρ := by
          have hdiag' : ∀ α ∈ S_rest,
              ∑ β ∈ S_rest, (if distinguishable α β then (0 : ℝ) else x α * x β) =
              x α ^ 2 + ∑ β ∈ S_rest.erase α, (if distinguishable α β then (0 : ℝ) else x α * x β) := by
            intro α hα; rw [← Finset.add_sum_erase _ _ hα]; simp [not_distinguishable_self, sq]
          rw [Finset.sum_congr rfl hdiag', sum_add_distrib]
          congr 1
          rw [Finset.sum_union hdisj_RL']
          have hR' : ∑ ρ ∈ R_rest, ∑ β ∈ S_rest.erase ρ, (if distinguishable ρ β then (0 : ℝ) else x ρ * x β) =
              ∑ ρ ∈ R_rest, (outDeg x ρ : ℝ) * x ρ := by
            refine Finset.sum_congr rfl fun ρ hρ => ?_
            have hρR := Finset.mem_of_mem_erase hρ
            have hsub : L_of ρ ⊆ S_rest.erase ρ := fun π hπ =>
              mem_erase.mpr ⟨(mem_filter.mp hπ).2.2.2.1.symm,
                mem_union_right _ (mem_biUnion.mpr ⟨ρ, hρ, hπ⟩)⟩
            rw [← Finset.sum_subset hsub]
            · calc ∑ π ∈ L_of ρ, (if distinguishable ρ π then (0 : ℝ) else x ρ * x π)
                  = ∑ π ∈ L_of ρ, x ρ := Finset.sum_congr rfl fun π hπ => by
                    have hE := (mem_filter.mp hπ).2
                    rw [if_neg hE.2.2.2.1, (hstar1 ρ π hE).2.2.1, mul_one]
                _ = (outDeg x ρ : ℝ) * x ρ := by simp [outDeg, L_of]
            · intro τ hτ hnotL
              have hτs := hS_sub (Finset.mem_of_mem_erase hτ)
              have hρs := (Finset.mem_sdiff.mp hρR).1
              have hne := (Finset.ne_of_mem_erase hτ).symm
              by_cases hd : distinguishable ρ τ
              · rw [if_pos hd]
              · exfalso
                rcases lemma_compress hk hx.1 (mem_filter.mp hρs).2 (mem_filter.mp hτs).2 hne hd with hA | hB | hC
                · exact hnotL (mem_filter.mpr ⟨hτs, (mem_filter.mp hρs).2, (mem_filter.mp hτs).2, hne, hd, by rw [hA.1]; exact hx.1.1⟩)
                · exact (Finset.mem_sdiff.mp hρR).2 (mem_filter.mpr ⟨hρs, τ, (mem_filter.mp hτs).2, (mem_filter.mp hρs).2, hne.symm, fun h => hd (distinguishable_symm.mp h), by rw [hB.1]; exact hx.1.1⟩)
                · exact hnotL (mem_filter.mpr ⟨hτs, hC.1⟩)
          have hL' : ∑ π ∈ R_rest.biUnion L_of, ∑ β ∈ S_rest.erase π, (if distinguishable π β then (0 : ℝ) else x π * x β) =
              ∑ ρ ∈ R_rest, (outDeg x ρ : ℝ) * x ρ := by
            rw [Finset.sum_biUnion hL_disj']
            refine Finset.sum_congr rfl fun ρ hρ => ?_
            calc ∑ π ∈ L_of ρ, ∑ β ∈ S_rest.erase π, (if distinguishable π β then (0 : ℝ) else x π * x β)
                = ∑ π ∈ L_of ρ, x ρ := by
                  refine Finset.sum_congr rfl fun π hπ => ?_
                  have hE := (mem_filter.mp hπ).2
                  have hπs := (mem_filter.mp hπ).1
                  have hρ_in : ρ ∈ S_rest.erase π :=
                    mem_erase.mpr ⟨hE.2.2.1, mem_union_left _ hρ⟩
                  rw [Finset.sum_eq_single ρ]
                  · rw [if_neg (fun h => hE.2.2.2.1 (distinguishable_symm.mp h)), (hstar1 ρ π hE).2.2.1, one_mul]
                  · intro τ hτ hneρ
                    have hτs := hS_sub (Finset.mem_of_mem_erase hτ)
                    have hneπ := (Finset.ne_of_mem_erase hτ).symm
                    by_cases hd : distinguishable π τ
                    · rw [if_pos hd]
                    · exfalso
                      rcases lemma_compress hk hx.1 (mem_filter.mp hπs).2 (mem_filter.mp hτs).2 hneπ hd with hA | hB | hC
                      · have hwπ2 := hA.2.2.2.1; have hwπ1 := (hstar1 ρ π hE).2.1; omega
                      · exact hneρ (hstar2 τ ρ π ⟨(mem_filter.mp hτs).2, (mem_filter.mp hπs).2, hneπ.symm, fun h => hd (distinguishable_symm.mp h), by rw [hB.1]; exact hx.1.1⟩ hE)
                      · have hwπ2 := (hstar1 π τ hC.1).1; have hwπ1 := (hstar1 ρ π hE).2.1; omega
                  · intro h; exact absurd hρ_in h
              _ = (outDeg x ρ : ℝ) * x ρ := by simp [outDeg, L_of]
          rw [hR', hL']; ring
        rw [hquad_S]
        have hL_cancel' : ∑ π ∈ R_rest.biUnion L_of, x π ^ 2 = ∑ π ∈ R_rest.biUnion L_of, (weight π : ℝ) * x π := by
          refine Finset.sum_congr rfl fun π hπ => ?_
          rcases mem_biUnion.mp hπ with ⟨ρ, _, hπ'⟩
          have hp := hstar1 ρ π (mem_filter.mp hπ').2
          rw [hp.2.1, hp.2.2.1]; norm_num
        rw [Finset.sum_union hdisj_RL', Finset.sum_union hdisj_RL', hL_cancel', mul_sum]
        have hcomb : (∑ τ ∈ R_rest, x τ ^ 2) + (∑ ρ ∈ R_rest, 2 * ((outDeg x ρ : ℝ) * x ρ)) -
            (∑ τ ∈ R_rest, (weight τ : ℝ) * x τ) =
            ∑ ρ ∈ R_rest, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) := by
          rw [← sum_add_distrib, ← sum_sub_distrib]
          refine Finset.sum_congr rfl fun ρ _ => by ring
        linarith
      rw [hpart1, hpart2]
    have hFx'_neg : quadForm x' < 0 := by
      have hsplit_F : ∑ ρ ∈ rootsFinset x, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) =
          (x σ ^ 2 + (2 * (outDeg x σ : ℝ) - (weight σ : ℝ)) * x σ) +
          ∑ ρ ∈ R_rest, (x ρ ^ 2 + (2 * (outDeg x ρ : ℝ) - (weight ρ : ℝ)) * x ρ) :=
        (Finset.add_sum_erase _ _ hσ).symm
      have hxσ_pos : 0 < x σ := lt_of_le_of_ne (hx.1.1.1 σ) (mem_filter.mp (Finset.mem_sdiff.mp hσ).1).2.symm
      have hcoeff : (1 : ℝ) ≤ 2 * (outDeg x σ : ℝ) - (weight σ : ℝ) - 2 := by
        have h1 : weight σ + 1 ≤ outDeg x σ := hgt
        have h1r : (weight σ : ℝ) + 1 ≤ (outDeg x σ : ℝ) := by exact_mod_cast h1
        have h3r : (3 : ℝ) ≤ (weight σ : ℝ) := by exact_mod_cast hwσ3
        linarith
      nlinarith
    have hx'_in : InX 0 x' := ⟨hx'_nonneg, hFx'_neg.le, hx'_w1, hx'_compat⟩
    have hl1_x' : l1Sum x ≤ l1Sum x' := by
      have hx'_sum : l1Sum x' = x σ + (Q1.card : ℝ) + ∑ τ ∈ S_rest, x τ := by
        unfold l1Sum
        let U := insert π_new Q1 ∪ S_rest
        have hout0 : ∀ τ, τ ∉ U → x' τ = 0 := by
          intro τ hτ
          have h1 : τ ≠ π_new := fun h => hτ (mem_union_left _ (mem_insert.mpr (Or.inl h)))
          have h2 : τ ∉ Q1 := fun h => hτ (mem_union_left _ (mem_insert.mpr (Or.inr h)))
          have h3 : τ ∉ S_rest := fun h => hτ (mem_union_right _ h)
          simp [x', h1, h2, h3]
        rw [← Finset.sum_subset (subset_univ U) fun τ _ hτ => hout0 τ hτ,
            Finset.sum_union hdisj_new_rest, sum_insert hπ_not_Q1]
        have h1 : x' π_new = x σ := by simp [x']
        have h2 : ∑ τ ∈ Q1, x' τ = (Q1.card : ℝ) := by
          calc ∑ τ ∈ Q1, x' τ = ∑ _τ ∈ Q1, (1 : ℝ) := Finset.sum_congr rfl fun τ hτ => by
                have hne : τ ≠ π_new := fun h => hπ_not_Q1 (h ▸ hτ)
                simp [x', hne, hτ]
            _ = (Q1.card : ℝ) := by simp
        have h3 : ∑ τ ∈ S_rest, x' τ = ∑ τ ∈ S_rest, x τ :=
          Finset.sum_congr rfl fun τ hτ => by
            have hnot := Finset.disjoint_right.mp hdisj_new_rest hτ
            have ha : τ ≠ π_new := fun h => hnot (mem_insert.mpr (Or.inl h))
            have hb : τ ∉ Q1 := fun h => hnot (mem_insert.mpr (Or.inr h))
            simp [x', ha, hb, hτ]
        rw [h1, h2, h3]
      have hx_sum : l1Sum x = x σ + (outDeg x σ : ℝ) + ∑ τ ∈ S_rest, x τ := by
        have hdisj_RL : Disjoint (rootsFinset x) (leavesFinset x) := Finset.sdiff_disjoint
        have hdisj_RL' : Disjoint R_rest (R_rest.biUnion L_of) :=
          Disjoint.mono (Finset.erase_subset σ _)
            (by rw [hL_part]; exact Finset.biUnion_subset_biUnion_of_subset_left L_of (Finset.erase_subset σ _))
            hdisj_RL
        have hL_disj' : (R_rest : Set (Subcube k)).PairwiseDisjoint L_of :=
          hL_disj.subset (Finset.erase_subset σ _)
        have hS_sum : ∑ τ ∈ S_rest, x τ = (∑ ρ ∈ R_rest, x ρ) + (∑ ρ ∈ R_rest, (outDeg x ρ : ℝ)) := by
          rw [Finset.sum_union hdisj_RL', Finset.sum_biUnion hL_disj']
          congr 1
          refine Finset.sum_congr rfl fun ρ _ => ?_
          calc ∑ π ∈ L_of ρ, x π = ∑ _π ∈ L_of ρ, (1 : ℝ) :=
                Finset.sum_congr rfl fun π hπ => (hstar1 ρ π (mem_filter.mp hπ).2).2.2.1
            _ = (outDeg x ρ : ℝ) := by simp [outDeg, L_of]
        rw [hl1, ← Finset.add_sum_erase _ x hσ, ← Finset.add_sum_erase _ (fun ρ => (outDeg x ρ : ℝ)) hσ, hS_sum]
        ring
      have hcard_ge : (outDeg x σ : ℝ) ≤ (Q1.card : ℝ) := by
        rw [hQ1_card]; exact_mod_cast h0
      linarith
    have hopt' : IsOptimal x' := ⟨hx'_in, fun z hz => (hx.1.2 z hz).trans hl1_x'⟩
    linarith [quadForm_eq_zero_of_optimal hk hopt']
  exact ⟨hR_dist, hdeg, hl1, hsphere⟩
lemma lemma_lag {α : Type*} [DecidableEq α] (I L : Finset α) (hLI : L ⊆ I)
    (a : α → ℤ) (haL : ∀ i ∈ L, a i = 1) (x : α → ℝ)
    (hsphere : ∑ i ∈ I, (x i ^ 2 - (a i : ℝ) * x i) ≤ 0)
    (hxL : ∀ i ∈ L, x i ≤ 1) :
    let R := I \ L
    let m : ℝ := (I.card : ℝ)
    let l : ℝ := (L.card : ℝ)
    let SI : ℝ := ∑ i ∈ I, ((a i : ℝ)) ^ 2
    let SR : ℝ := ∑ i ∈ R, ((a i : ℝ)) ^ 2
    (m < SI →
      (∑ i ∈ I, x i ≤ l + (1 / 2) * ((∑ i ∈ R, (a i : ℝ)) + Real.sqrt ((m - l) * SR))) ∧
      (∑ i ∈ I, x i = l + (1 / 2) * ((∑ i ∈ R, (a i : ℝ)) + Real.sqrt ((m - l) * SR)) →
        (∀ i ∈ L, x i = 1) ∧
        (∀ i ∈ R, x i = (1 / 2) * ((a i : ℝ) + Real.sqrt (SR / (m - l)))))) ∧
    (SI ≤ m →
      (∑ i ∈ I, x i ≤ (1 / 2) * ((∑ i ∈ I, (a i : ℝ)) + Real.sqrt (m * SI)))) := by
  intro R m l SI SR
  have hI_split : I = L ∪ R := (Finset.union_sdiff_of_subset hLI).symm
  have hdisj : Disjoint L R := disjoint_sdiff
  have hcard_R : (R.card : ℝ) = m - l := by
    have hnat : L.card + R.card = I.card := by
      simpa [add_comm] using card_sdiff_add_card_eq_card hLI
    have hr : l + (R.card : ℝ) = m := by dsimp only [l, m]; exact_mod_cast hnat
    linarith
  have hSI_split : SI = l + SR := by
    dsimp only [SI, SR]
    rw [hI_split, Finset.sum_union hdisj]
    congr 1
    calc ∑ i ∈ L, ((a i : ℝ)) ^ 2 = ∑ _i ∈ L, (1 : ℝ) :=
          Finset.sum_congr rfl fun i hi => by rw [haL i hi]; norm_num
      _ = l := by simp [l]
  constructor
  ·
    intro hmSI
    have hml_lt_SR : m - l < SR := by linarith
    have hR_pos : 0 < m - l := by
      rw [← hcard_R]
      by_contra h0
      have hR0 : R.card = 0 := by
        have : (R.card : ℝ) ≤ 0 := not_lt.mp h0
        exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
      have hSR0 : SR = 0 := by simp [SR, Finset.card_eq_zero.mp hR0]
      have hml0 : m - l = 0 := by rw [← hcard_R, hR0]; simp
      linarith
    have hSR_pos : 0 < SR := lt_trans hR_pos hml_lt_SR
    let μ : ℝ := Real.sqrt (SR / (m - l))
    have hμ_sq : μ ^ 2 = SR / (m - l) := Real.sq_sqrt (div_nonneg hSR_pos.le hR_pos.le)
    have hμ_gt1 : 1 < μ := by
      have h1 : 1 < SR / (m - l) := (one_lt_div hR_pos).mpr hml_lt_SR
      have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
      nlinarith [hμ_sq]
    have hμ_pos : 0 < μ := by linarith
    have hL_term : ∀ i ∈ L,
        x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) =
          1 + (1 - 1 / μ) * (x i - 1) - (1 / μ) * (x i - 1) ^ 2 := by
      intro i hi; rw [haL i hi]; push_cast; ring
    have hR_term : ∀ i ∈ R,
        x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) =
          (a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4) -
            (1 / μ) * (x i - ((a i : ℝ) + μ) / 2) ^ 2 := by
      intro i _; field_simp; ring
    have hL_le : ∀ i ∈ L, x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) ≤ 1 := by
      intro i hi
      rw [hL_term i hi]
      have h1 : (1 - 1 / μ) * (x i - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by rw [sub_nonneg, div_le_one hμ_pos]; exact hμ_gt1.le)
          (by linarith [hxL i hi])
      have h2 : 0 ≤ (1 / μ) * (x i - 1) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
      linarith
    have hR_le : ∀ i ∈ R, x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) ≤
        (a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4) := by
      intro i hi
      rw [hR_term i hi]
      have h2 : 0 ≤ (1 / μ) * (x i - ((a i : ℝ) + μ) / 2) ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      linarith
    have hrhs_eq : l + ∑ i ∈ R, ((a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4)) =
        l + (1 / 2) * ((∑ i ∈ R, (a i : ℝ)) + Real.sqrt ((m - l) * SR)) := by
      have hsqrt_eq : SR / (4 * μ) + (m - l) * μ / 4 = (1 / 2) * Real.sqrt ((m - l) * SR) := by
        have hmul : (m - l) * μ = Real.sqrt ((m - l) * SR) := by
          have h1 : (m - l) * μ = Real.sqrt ((m - l) ^ 2 * (SR / (m - l))) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR_pos.le]
          rw [h1]
          congr 1; field_simp
        have hSR_eq : SR = (m - l) * μ ^ 2 := by
          rw [hμ_sq]; field_simp
        conv_lhs => rw [hSR_eq]
        have : (m - l) * μ ^ 2 / (4 * μ) + (m - l) * μ / 4 = (1 / 2) * ((m - l) * μ) := by
          field_simp; ring
        rw [this, hmul]
      rw [sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div,
          sum_const, nsmul_eq_mul, hcard_R]
      change l + ((∑ i ∈ R, (a i : ℝ)) / 2 + (SR / (4 * μ) + (m - l) * (μ / 4))) = _
      have h4 : (m - l) * (μ / 4) = (m - l) * μ / 4 := by ring
      rw [h4, hsqrt_eq]; ring
    have hsum_step : ∑ i ∈ I, x i ≤
        ∑ i ∈ I, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) := by
      rw [sum_sub_distrib, ← mul_sum]
      have hnonpos : (1 / μ) * ∑ i ∈ I, (x i ^ 2 - (a i : ℝ) * x i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hsphere
      linarith
    have hsum_L : ∑ i ∈ L, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) ≤ l := by
      calc ∑ i ∈ L, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))
          ≤ ∑ _i ∈ L, (1 : ℝ) := sum_le_sum hL_le
        _ = l := by simp [l]
    have hsum_R : ∑ i ∈ R, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) ≤
        ∑ i ∈ R, ((a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4)) :=
      sum_le_sum hR_le
    have hmain : ∑ i ∈ I, x i ≤ l + (1 / 2) * ((∑ i ∈ R, (a i : ℝ)) + Real.sqrt ((m - l) * SR)) := by
      rw [← hrhs_eq]
      calc ∑ i ∈ I, x i ≤ ∑ i ∈ I, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) := hsum_step
        _ = (∑ i ∈ L, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))) +
            (∑ i ∈ R, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))) := by
              rw [hI_split, Finset.sum_union hdisj]
        _ ≤ l + ∑ i ∈ R, ((a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4)) := add_le_add hsum_L hsum_R
    refine ⟨hmain, fun heq => ?_⟩
    have hL_eq : ∑ i ∈ L, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) = l := by
      have hsplit2 : ∑ i ∈ I, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) =
          (∑ i ∈ L, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))) +
          (∑ i ∈ R, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))) := by
        rw [hI_split, Finset.sum_union hdisj]
      linarith
    have hR_eq : ∑ i ∈ R, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) =
        ∑ i ∈ R, ((a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4)) := by
      have hsplit2 : ∑ i ∈ I, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) =
          (∑ i ∈ L, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))) +
          (∑ i ∈ R, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i))) := by
        rw [hI_split, Finset.sum_union hdisj]
      linarith
    constructor
    · intro i hi
      have heqi : x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) = 1 := by
        have hsum1 : ∑ j ∈ L, (1 - (x j - (1 / μ) * (x j ^ 2 - (a j : ℝ) * x j))) = 0 := by
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]; linarith
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by linarith [hL_le j hj])).mp hsum1 i hi
        linarith
      rw [hL_term i hi] at heqi
      have h1 : (1 - 1 / μ) * (x i - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by rw [sub_nonneg, div_le_one hμ_pos]; exact hμ_gt1.le)
          (by linarith [hxL i hi])
      have hsq0 : (1 / μ) * (x i - 1) ^ 2 = 0 := by
        have := sq_nonneg (x i - 1)
        have : 0 ≤ (1 / μ) * (x i - 1) ^ 2 := by positivity
        linarith
      have h0 : (x i - 1) ^ 2 = 0 := (mul_eq_zero.mp hsq0).resolve_left (by positivity)
      linarith [sq_eq_zero_iff.mp h0]
    · intro i hi
      have heqi : x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) =
          (a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4) := by
        have hsum1 : ∑ j ∈ R, (((a j : ℝ) / 2 + ((a j : ℝ) ^ 2 / (4 * μ) + μ / 4)) -
            (x j - (1 / μ) * (x j ^ 2 - (a j : ℝ) * x j))) = 0 := by
          rw [sum_sub_distrib]; linarith
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by linarith [hR_le j hj])).mp hsum1 i hi
        linarith
      rw [hR_term i hi] at heqi
      have hsq0 : (1 / μ) * (x i - ((a i : ℝ) + μ) / 2) ^ 2 = 0 := by linarith
      have h0 : (x i - ((a i : ℝ) + μ) / 2) ^ 2 = 0 := (mul_eq_zero.mp hsq0).resolve_left (by positivity)
      have := sq_eq_zero_iff.mp h0
      linarith
  ·
    intro hSIm
    by_cases hSI0 : SI = 0
    · have ha0 : ∀ i ∈ I, (a i : ℝ) = 0 := by
        intro i hi
        exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hSI0 i hi)
      have hx0 : ∀ i ∈ I, x i = 0 := by
        have hsum_sq : ∑ i ∈ I, x i ^ 2 ≤ 0 := by
          calc ∑ i ∈ I, x i ^ 2 = ∑ i ∈ I, (x i ^ 2 - (a i : ℝ) * x i) :=
                Finset.sum_congr rfl fun i hi => by rw [ha0 i hi]; ring
            _ ≤ 0 := hsphere
        have heq0 : ∑ i ∈ I, x i ^ 2 = 0 := le_antisymm hsum_sq (sum_nonneg fun _ _ => sq_nonneg _)
        intro i hi
        exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp heq0 i hi)
      rw [sum_eq_zero hx0, sum_eq_zero ha0, hSI0]; simp
    · have hSI_pos : 0 < SI := lt_of_le_of_ne (sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hSI0)
      have hm_pos : 0 < m := lt_of_lt_of_le hSI_pos hSIm
      let μ : ℝ := Real.sqrt (SI / m)
      have hμ_sq : μ ^ 2 = SI / m := Real.sq_sqrt (div_nonneg hSI_pos.le hm_pos.le)
      have hμ_pos : 0 < μ := Real.sqrt_pos.mpr (div_pos hSI_pos hm_pos)
      have hI_le : ∀ i ∈ I, x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) ≤
          (a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4) := by
        intro i _
        have hid : x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i) =
            (a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4) -
              (1 / μ) * (x i - ((a i : ℝ) + μ) / 2) ^ 2 := by field_simp; ring
        rw [hid]
        have : 0 ≤ (1 / μ) * (x i - ((a i : ℝ) + μ) / 2) ^ 2 :=
          mul_nonneg (div_nonneg zero_le_one hμ_pos.le) (sq_nonneg _)
        linarith
      have hrhs_eq : ∑ i ∈ I, ((a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4)) =
          (1 / 2) * ((∑ i ∈ I, (a i : ℝ)) + Real.sqrt (m * SI)) := by
        have hsqrt_eq : SI / (4 * μ) + m * μ / 4 = (1 / 2) * Real.sqrt (m * SI) := by
          have hmul : m * μ = Real.sqrt (m * SI) := by
            have h1 : m * μ = Real.sqrt (m ^ 2 * (SI / m)) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm_pos.le]
            rw [h1]; congr 1; field_simp
          have hSI_eq : SI = m * μ ^ 2 := by rw [hμ_sq]; field_simp
          conv_lhs => rw [hSI_eq]
          have : m * μ ^ 2 / (4 * μ) + m * μ / 4 = (1 / 2) * (m * μ) := by field_simp; ring
          rw [this, hmul]
        rw [sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div,
            sum_const, nsmul_eq_mul]
        change (∑ i ∈ I, (a i : ℝ)) / 2 + (SI / (4 * μ) + m * (μ / 4)) = _
        have h4 : m * (μ / 4) = m * μ / 4 := by ring
        rw [h4, hsqrt_eq]; ring
      calc ∑ i ∈ I, x i
          ≤ ∑ i ∈ I, (x i - (1 / μ) * (x i ^ 2 - (a i : ℝ) * x i)) := by
            rw [sum_sub_distrib, ← mul_sum]
            have : (1 / μ) * ∑ i ∈ I, (x i ^ 2 - (a i : ℝ) * x i) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_one hμ_pos.le) hsphere
            linarith
        _ ≤ ∑ i ∈ I, ((a i : ℝ) / 2 + ((a i : ℝ) ^ 2 / (4 * μ) + μ / 4)) := sum_le_sum hI_le
        _ = (1 / 2) * ((∑ i ∈ I, (a i : ℝ)) + Real.sqrt (m * SI)) := hrhs_eq
lemma lemma_shift (L : List ℕ) (hL : ∀ a ∈ L, 2 ≤ a) :
    ((L.map (fun a : ℕ => (a : ℝ))).sum +
      Real.sqrt ((L.length : ℝ) * (L.map (fun a : ℕ => (a : ℝ) ^ 2)).sum) ≤
      (L.map (fun a : ℕ => (2 : ℝ) ^ a)).sum) ∧
    ((L.map (fun a : ℕ => (a : ℝ))).sum +
      Real.sqrt ((L.length : ℝ) * (L.map (fun a : ℕ => (a : ℝ) ^ 2)).sum) =
      (L.map (fun a : ℕ => (2 : ℝ) ^ a)).sum → ∀ a ∈ L, a = 2) := by
  suffices h : ∀ S : ℕ, ∀ L : List ℕ, (∀ a ∈ L, 2 ≤ a) →
      (L.map (fun a => 2 ^ (a - 2) - 1)).sum = S →
      ((L.map (fun a : ℕ => (a : ℝ))).sum +
        Real.sqrt ((L.length : ℝ) * (L.map (fun a : ℕ => (a : ℝ) ^ 2)).sum) ≤
        (L.map (fun a : ℕ => (2 : ℝ) ^ a)).sum) ∧
      (S > 0 →
        (L.map (fun a : ℕ => (a : ℝ))).sum +
        Real.sqrt ((L.length : ℝ) * (L.map (fun a : ℕ => (a : ℝ) ^ 2)).sum) <
        (L.map (fun a : ℕ => (2 : ℝ) ^ a)).sum) by
    obtain ⟨hle, hlt⟩ := h _ L hL rfl
    refine ⟨hle, fun heq a ha => ?_⟩
    by_contra hne2
    have ha3 : 3 ≤ a := by have := hL a ha; omega
    have hSpos : 0 < (L.map (fun x => 2 ^ (x - 2) - 1)).sum := by
      have hmem : 2 ^ (a - 2) - 1 ∈ L.map (fun x => 2 ^ (x - 2) - 1) := List.mem_map_of_mem ha
      have hge1 : 1 ≤ 2 ^ (a - 2) - 1 := by
        have : 2 ≤ 2 ^ (a - 2) := Nat.le_self_pow (by omega) 2
        omega
      exact lt_of_lt_of_le (by omega) (List.le_sum_of_mem hmem)
    linarith [hlt hSpos]
  intro S
  induction S with
  | zero =>
    intro L hL hS0
    have hall2 : ∀ a ∈ L, a = 2 := by
      intro a ha
      have h0 : 2 ^ (a - 2) - 1 = 0 := by
        have hmem : 2 ^ (a - 2) - 1 ∈ L.map (fun x => 2 ^ (x - 2) - 1) := List.mem_map_of_mem ha
        have := List.le_sum_of_mem hmem
        omega
      have ha2 := hL a ha
      by_contra hne2
      have : 2 ≤ 2 ^ (a - 2) := Nat.le_self_pow (by omega) 2
      omega
    have hs1 : (L.map (fun a : ℕ => (a : ℝ))).sum = 2 * (L.length : ℝ) := by
      have : L.map (fun a : ℕ => (a : ℝ)) = List.replicate L.length (2 : ℝ) := by
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hi : i < L.length := by simpa using hi1
        simp only [List.getElem_map, List.getElem_replicate]
        have h2 : L[i]'hi = 2 := hall2 _ (List.getElem_mem hi)
        rw [h2]; norm_num
      rw [this, List.sum_replicate, nsmul_eq_mul]; ring
    have hs2 : (L.map (fun a : ℕ => (a : ℝ) ^ 2)).sum = 4 * (L.length : ℝ) := by
      have : L.map (fun a : ℕ => (a : ℝ) ^ 2) = List.replicate L.length (4 : ℝ) := by
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hi : i < L.length := by simpa using hi1
        simp only [List.getElem_map, List.getElem_replicate]
        have h2 : L[i]'hi = 2 := hall2 _ (List.getElem_mem hi)
        rw [h2]; norm_num
      rw [this, List.sum_replicate, nsmul_eq_mul]; ring
    have hs3 : (L.map (fun a : ℕ => (2 : ℝ) ^ a)).sum = 4 * (L.length : ℝ) := by
      have : L.map (fun a : ℕ => (2 : ℝ) ^ a) = List.replicate L.length (4 : ℝ) := by
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hi : i < L.length := by simpa using hi1
        simp only [List.getElem_map, List.getElem_replicate]
        have h2 : L[i]'hi = 2 := hall2 _ (List.getElem_mem hi)
        rw [h2]; norm_num
      rw [this, List.sum_replicate, nsmul_eq_mul]; ring
    rw [hs1, hs2, hs3]
    have hsq : Real.sqrt ((L.length : ℝ) * (4 * (L.length : ℝ))) = 2 * (L.length : ℝ) := by
      rw [show (L.length : ℝ) * (4 * (L.length : ℝ)) = (2 * (L.length : ℝ)) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
    rw [hsq]
    exact ⟨by linarith, fun h => absurd h (by omega)⟩
  | succ S ih =>
    intro L hL hS
    have hex : ∃ a ∈ L, 3 ≤ a := by
      by_contra hall
      push Not at hall
      have h0 : (L.map (fun x => 2 ^ (x - 2) - 1)).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro y hy
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        have h1 := hL x hx; have h2 := hall x hx
        have : x = 2 := by omega
        simp [this]
      omega
    obtain ⟨a, haL, ha3⟩ := hex
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem haL
    let L' := L1 ++ [a - 1, a - 1] ++ L2
    have hL' : ∀ x ∈ L', 2 ≤ x := by
      intro x hx
      simp only [L', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (h1 | rfl | rfl) | h2
      · exact hL x (by simp [h1])
      · omega
      · omega
      · exact hL x (by simp [h2])
    have hS' : (L'.map (fun x => 2 ^ (x - 2) - 1)).sum = S := by
      have hpow : 2 ^ (a - 2) = 2 * 2 ^ (a - 1 - 2) := by
        have hsub : a - 2 = (a - 1 - 2) + 1 := by omega
        rw [hsub, pow_succ']
      have hpos : 1 ≤ 2 ^ (a - 1 - 2) := Nat.one_le_pow _ _ (by omega)
      simp only [L', List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil] at hS ⊢
      omega
    have hih := (ih L' hL' hS').1
    have hlen : L'.length = (L1 ++ a :: L2).length + 1 := by simp [L']; omega
    have h1a : 1 ≤ a := by omega
    have ha1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub h1a, Nat.cast_one]
    have hsum1 : (L'.map (fun x : ℕ => (x : ℝ))).sum =
        ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ))).sum + ((a : ℝ) - 2) := by
      simp only [L', List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      rw [ha1]; ring
    have hsum2 : (L'.map (fun x : ℕ => (x : ℝ) ^ 2)).sum =
        ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ) ^ 2)).sum + ((a : ℝ) ^ 2 - 4 * (a : ℝ) + 2) := by
      simp only [L', List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      rw [ha1]; ring
    have hsum3 : (L'.map (fun x : ℕ => (2 : ℝ) ^ x)).sum =
        ((L1 ++ a :: L2).map (fun x : ℕ => (2 : ℝ) ^ x)).sum := by
      simp only [L', List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      have hpow : (2 : ℝ) ^ a = (2 : ℝ) ^ (a - 1) + (2 : ℝ) ^ (a - 1) := by
        have hsub : a = (a - 1) + 1 := by omega
        conv_lhs => rw [hsub, pow_succ]
        ring
      linarith
    have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha3
    have hquad_ge : (-1 : ℝ) ≤ (a : ℝ) ^ 2 - 4 * (a : ℝ) + 2 := by nlinarith
    have hsq_sum_gt : ((L1 ++ a :: L2).length : ℝ) + 1 < ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ) ^ 2)).sum := by
      have h4 : 4 * ((L1 ++ a :: L2).length : ℝ) ≤ ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ) ^ 2)).sum := by
        have hle_list : ∀ M : List ℕ, (∀ x ∈ M, 2 ≤ x) → 4 * (M.length : ℝ) ≤ (M.map (fun x : ℕ => (x : ℝ) ^ 2)).sum := by
          intro M hM
          induction M with
          | nil => simp
          | cons hd tl iht =>
            simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
            have hhd : (2 : ℝ) ≤ (hd : ℝ) := by exact_mod_cast hM hd (List.mem_cons_self ..)
            have htl := iht (fun x hx => hM x (List.mem_cons_of_mem _ hx))
            nlinarith
        exact hle_list (L1 ++ a :: L2) hL
      have hlen1 : (1 : ℝ) ≤ ((L1 ++ a :: L2).length : ℝ) := by simp; linarith
      linarith
    have hrad_lt : ((L1 ++ a :: L2).length : ℝ) * ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ) ^ 2)).sum <
        (L'.length : ℝ) * (L'.map (fun x : ℕ => (x : ℝ) ^ 2)).sum := by
      rw [hlen, Nat.cast_add, Nat.cast_one, hsum2]
      have hlen_pos : (0 : ℝ) < ((L1 ++ a :: L2).length : ℝ) + 1 := by positivity
      nlinarith
    have hsqrt_lt : Real.sqrt (((L1 ++ a :: L2).length : ℝ) * ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ) ^ 2)).sum) <
        Real.sqrt ((L'.length : ℝ) * (L'.map (fun x : ℕ => (x : ℝ) ^ 2)).sum) :=
      Real.sqrt_lt_sqrt (mul_nonneg (Nat.cast_nonneg _) (List.sum_nonneg (by
        intro y hy; rcases List.mem_map.mp hy with ⟨x, _, rfl⟩; exact sq_nonneg _))) hrad_lt
    have hstrict : ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ))).sum +
        Real.sqrt (((L1 ++ a :: L2).length : ℝ) * ((L1 ++ a :: L2).map (fun x : ℕ => (x : ℝ) ^ 2)).sum) <
        ((L1 ++ a :: L2).map (fun x : ℕ => (2 : ℝ) ^ x)).sum := by
      rw [← hsum3]
      linarith
    exact ⟨hstrict.le, fun _ => hstrict⟩
set_option maxHeartbeats 600000 in
lemma proposition_convex {k : ℕ} (hk : 1 ≤ k) (D : Finset (Subcube k))
    (hD : IsDistinguishableSet D) (d : Subcube k → ℕ)
    (hd : ∀ τ ∈ D, d τ ≤ weight τ ∧ (weight τ = 1 → d τ = 0))
    (x : Subcube k → ℝ) (hsupp : ∀ τ ∈ D, 0 < x τ) (hout : ∀ τ, τ ∉ D → x τ = 0)
    (hsphere : ∑ τ ∈ D, (x τ ^ 2 + (2 * (d τ : ℝ) - (weight τ : ℝ)) * x τ) = 0)
    (hx1 : ∀ τ ∈ D, weight τ = 1 → x τ ≤ 1) :
    (∑ τ ∈ D, x τ ≤ (2 : ℝ) ^ (k - 1) - ∑ τ ∈ D, (d τ : ℝ)) ∧
    (∑ τ ∈ D, x τ = (2 : ℝ) ^ (k - 1) - ∑ τ ∈ D, (d τ : ℝ) → InO x ∧ ∀ τ ∈ D, d τ = 0) := by
  classical
  let a : Subcube k → ℤ := fun τ => (weight τ : ℤ) - 2 * (d τ : ℤ)
  let L : Finset (Subcube k) := D.filter (fun τ => weight τ = 1)
  let D' : Finset (Subcube k) := D \ L
  have hLD : L ⊆ D := filter_subset _ _
  have haL : ∀ τ ∈ L, a τ = 1 := by
    intro τ hτ
    have hw := (mem_filter.mp hτ).2
    have hd0 := (hd τ (hLD hτ)).2 hw
    simp [a, hw, hd0]
  have hsphere' : ∑ τ ∈ D, (x τ ^ 2 - (a τ : ℝ) * x τ) ≤ 0 := by
    have heq : ∑ τ ∈ D, (x τ ^ 2 - (a τ : ℝ) * x τ) =
        ∑ τ ∈ D, (x τ ^ 2 + (2 * (d τ : ℝ) - (weight τ : ℝ)) * x τ) :=
      Finset.sum_congr rfl fun τ _ => by simp only [a]; push_cast; ring
    rw [heq, hsphere]
  have hlag := lemma_lag D L hLD a haL x hsphere' (fun τ hτ => hx1 τ (hLD hτ) (mem_filter.mp hτ).2)
  have hdist := sum_two_pow_weight_le hD
  have h2k : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ']
  have hD_split : D = L ∪ D' := (Finset.union_sdiff_of_subset hLD).symm
  have hD_disj : Disjoint L D' := disjoint_sdiff
  have hsum_d_eq : ∑ τ ∈ D', (d τ : ℝ) = ∑ τ ∈ D, (d τ : ℝ) := by
    rw [hD_split, Finset.sum_union hD_disj]
    have hL0 : ∑ τ ∈ L, (d τ : ℝ) = 0 :=
      sum_eq_zero fun τ hτ => by rw [(hd τ (hLD hτ)).2 (mem_filter.mp hτ).2]; simp
    linarith
  have hD'_ge2 : ∀ τ ∈ D', 2 ≤ weight τ := by
    intro τ hτ
    have h1 := hD.1 τ (Finset.mem_sdiff.mp hτ).1
    have hne1 : weight τ ≠ 1 := fun hw1 =>
      (Finset.mem_sdiff.mp hτ).2 (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hτ).1, hw1⟩)
    omega
  have hsum_2pow_D' : ∑ τ ∈ D', (2 : ℝ) ^ weight τ ≤ (2 : ℝ) ^ k - 2 * (L.card : ℝ) := by
    have h1 : (∑ τ ∈ D, (2 : ℝ) ^ weight τ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hdist.1
    rw [hD_split, Finset.sum_union hD_disj] at h1
    have hL2 : ∑ τ ∈ L, (2 : ℝ) ^ weight τ = 2 * (L.card : ℝ) := by
      calc ∑ τ ∈ L, (2 : ℝ) ^ weight τ = ∑ _τ ∈ L, (2 : ℝ) :=
            Finset.sum_congr rfl fun τ hτ => by rw [(mem_filter.mp hτ).2]; norm_num
        _ = 2 * (L.card : ℝ) := by simp [mul_comm]
    linarith
  by_cases hcase : (D.card : ℝ) < ∑ τ ∈ D, ((a τ : ℝ)) ^ 2
  ·
    obtain ⟨hb1, heq1⟩ := hlag.1 hcase
    have hcard_D' : (D.card : ℝ) - (L.card : ℝ) = (D'.card : ℝ) := by
      have hnat : L.card + D'.card = D.card := by
        simpa [add_comm] using card_sdiff_add_card_eq_card hLD
      have hr : (L.card : ℝ) + (D'.card : ℝ) = (D.card : ℝ) := by exact_mod_cast hnat
      linarith
    have ha_sq_le : ∀ τ ∈ D', ((a τ : ℝ)) ^ 2 ≤ (weight τ : ℝ) ^ 2 := by
      intro τ hτ
      have hdle : (d τ : ℝ) ≤ (weight τ : ℝ) := by exact_mod_cast (hd τ (Finset.mem_sdiff.mp hτ).1).1
      have hd0 : (0 : ℝ) ≤ (d τ : ℝ) := Nat.cast_nonneg _
      have ha_eq : (a τ : ℝ) = (weight τ : ℝ) - 2 * (d τ : ℝ) := by simp [a]
      rw [ha_eq]
      nlinarith
    have hsum_a_sq : ∑ τ ∈ D', ((a τ : ℝ)) ^ 2 ≤ ∑ τ ∈ D', (weight τ : ℝ) ^ 2 :=
      sum_le_sum ha_sq_le
    let wL : List ℕ := D'.toList.map weight
    have hwL_ge2 : ∀ w ∈ wL, 2 ≤ w := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨τ, hτ, rfl⟩
      exact hD'_ge2 τ (Finset.mem_toList.mp hτ)
    have hshift := lemma_shift wL hwL_ge2
    have hlen_wL : (wL.length : ℝ) = (D'.card : ℝ) := by simp [wL]
    have hlist_sum : ∀ f : Subcube k → ℝ, (D'.toList.map f).sum = ∑ τ ∈ D', f τ := fun f => by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
    have hsum_wL1 : (wL.map (fun w : ℕ => (w : ℝ))).sum = ∑ τ ∈ D', (weight τ : ℝ) := by
      simp only [wL, List.map_map]; exact hlist_sum (fun τ => (weight τ : ℝ))
    have hsum_wL2 : (wL.map (fun w : ℕ => (w : ℝ) ^ 2)).sum = ∑ τ ∈ D', (weight τ : ℝ) ^ 2 := by
      simp only [wL, List.map_map]; exact hlist_sum (fun τ => (weight τ : ℝ) ^ 2)
    have hsum_wL3 : (wL.map (fun w : ℕ => (2 : ℝ) ^ w)).sum = ∑ τ ∈ D', (2 : ℝ) ^ weight τ := by
      simp only [wL, List.map_map]; exact hlist_sum (fun τ => (2 : ℝ) ^ weight τ)
    have hshift_le : (∑ τ ∈ D', (weight τ : ℝ)) +
        Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2) ≤ ∑ τ ∈ D', (2 : ℝ) ^ weight τ := by
      have h1 := hshift.1
      rwa [hlen_wL, hsum_wL1, hsum_wL2, hsum_wL3] at h1
    have hsum_a_eq : ∑ τ ∈ D', (a τ : ℝ) = (∑ τ ∈ D', (weight τ : ℝ)) - 2 * ∑ τ ∈ D, (d τ : ℝ) := by
      rw [← hsum_d_eq, mul_sum, ← sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => by simp [a]
    have hb2 : (L.card : ℝ) + (1 / 2) * ((∑ τ ∈ D', (a τ : ℝ)) +
          Real.sqrt (((D.card : ℝ) - (L.card : ℝ)) * ∑ τ ∈ D', ((a τ : ℝ)) ^ 2)) ≤
        (L.card : ℝ) + (1 / 2) * ((∑ τ ∈ D', (weight τ : ℝ)) +
          Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2)) - ∑ τ ∈ D, (d τ : ℝ) := by
      rw [hcard_D', hsum_a_eq]
      have hsq : Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', ((a τ : ℝ)) ^ 2) ≤
          Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum_a_sq (Nat.cast_nonneg _))
      linarith
    have hb3 : (L.card : ℝ) + (1 / 2) * ((∑ τ ∈ D', (weight τ : ℝ)) +
          Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2)) - ∑ τ ∈ D, (d τ : ℝ) ≤
        (L.card : ℝ) + (1 / 2) * (∑ τ ∈ D', (2 : ℝ) ^ weight τ) - ∑ τ ∈ D, (d τ : ℝ) := by
      linarith [hshift_le]
    have hb4 : (L.card : ℝ) + (1 / 2) * (∑ τ ∈ D', (2 : ℝ) ^ weight τ) - ∑ τ ∈ D, (d τ : ℝ) ≤
        (2 : ℝ) ^ (k - 1) - ∑ τ ∈ D, (d τ : ℝ) := by
      linarith [hsum_2pow_D', h2k]
    refine ⟨hb1.trans (hb2.trans (hb3.trans hb4)), fun heq => ?_⟩
    have hEq1 : ∑ τ ∈ D, x τ = (L.card : ℝ) + (1 / 2) * ((∑ τ ∈ D', (a τ : ℝ)) +
        Real.sqrt (((D.card : ℝ) - (L.card : ℝ)) * ∑ τ ∈ D', ((a τ : ℝ)) ^ 2)) := by linarith
    have hEq3 : (∑ τ ∈ D', (weight τ : ℝ)) +
        Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2) = ∑ τ ∈ D', (2 : ℝ) ^ weight τ := by linarith
    have hEq4 : ∑ τ ∈ D', (2 : ℝ) ^ weight τ = (2 : ℝ) ^ k - 2 * (L.card : ℝ) := by linarith
    have hD'_all2 : ∀ τ ∈ D', weight τ = 2 := by
      intro τ hτ
      have hmem : weight τ ∈ wL := List.mem_map_of_mem (Finset.mem_toList.mpr hτ)
      have h2 := hshift.2
      rw [hlen_wL, hsum_wL1, hsum_wL2, hsum_wL3] at h2
      exact h2 hEq3 _ hmem
    have hEq_sq : ∑ τ ∈ D', ((a τ : ℝ)) ^ 2 = ∑ τ ∈ D', (weight τ : ℝ) ^ 2 := by
      have hsqrt_eq : Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', ((a τ : ℝ)) ^ 2) =
          Real.sqrt ((D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2) := by
        rw [hcard_D', hsum_a_eq] at hEq1
        linarith
      have hD'pos : (0 : ℝ) < (D'.card : ℝ) := by
        rw [← hcard_D']
        by_contra h0
        have hD'0 : D'.card = 0 := by
          have : (D'.card : ℝ) ≤ 0 := by linarith
          exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
        have hSI_eq : ∑ τ ∈ D, ((a τ : ℝ)) ^ 2 = (L.card : ℝ) := by
          rw [hD_split, Finset.sum_union hD_disj, Finset.card_eq_zero.mp hD'0]
          simp only [Finset.sum_empty, add_zero]
          calc ∑ τ ∈ L, ((a τ : ℝ)) ^ 2 = ∑ _τ ∈ L, (1 : ℝ) :=
                Finset.sum_congr rfl fun τ hτ => by rw [haL τ hτ]; norm_num
            _ = (L.card : ℝ) := by simp
        have : (L.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast card_le_card hLD
        linarith
      have hmul_eq : (D'.card : ℝ) * ∑ τ ∈ D', ((a τ : ℝ)) ^ 2 =
          (D'.card : ℝ) * ∑ τ ∈ D', (weight τ : ℝ) ^ 2 := by
        have := congrArg (· ^ 2) hsqrt_eq
        rwa [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)),
             Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _))] at this
      exact mul_left_cancel₀ hD'pos.ne' hmul_eq
    have ha_eq_pm : ∀ τ ∈ D', d τ = 0 ∨ d τ = 2 := by
      intro τ hτ
      have hzero : (weight τ : ℝ) ^ 2 - ((a τ : ℝ)) ^ 2 = 0 := by
        have hsum0 : ∑ σ ∈ D', ((weight σ : ℝ) ^ 2 - ((a σ : ℝ)) ^ 2) = 0 := by
          rw [sum_sub_distrib]; linarith
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun σ hσ => by linarith [ha_sq_le σ hσ])).mp hsum0 τ hτ
      have hw2 := hD'_all2 τ hτ
      have ha_eq : (a τ : ℝ) = 2 - 2 * (d τ : ℝ) := by simp [a, hw2]
      rw [hw2, ha_eq] at hzero
      norm_num at hzero
      have hd_or : (d τ : ℝ) = 0 ∨ (d τ : ℝ) = 2 := by
        have : (d τ : ℝ) * ((d τ : ℝ) - 2) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h0 | h2
        · exact Or.inl h0
        · exact Or.inr (by linarith)
      rcases hd_or with h0 | h2
      · left; exact_mod_cast h0
      · right; exact_mod_cast h2
    obtain ⟨hxL_eq, hxR_eq⟩ := heq1 hEq1
    have hrms2 : Real.sqrt ((∑ τ ∈ D', ((a τ : ℝ)) ^ 2) / ((D.card : ℝ) - (L.card : ℝ))) = 2 := by
      rw [hcard_D', hEq_sq]
      have h4 : ∑ τ ∈ D', (weight τ : ℝ) ^ 2 = 4 * (D'.card : ℝ) := by
        calc ∑ τ ∈ D', (weight τ : ℝ) ^ 2 = ∑ _τ ∈ D', (4 : ℝ) :=
              Finset.sum_congr rfl fun τ hτ => by rw [hD'_all2 τ hτ]; norm_num
          _ = 4 * (D'.card : ℝ) := by simp [mul_comm]
      have hD'ne : (D'.card : ℝ) ≠ 0 := by
        intro h0
        have hD'0 : D'.card = 0 := by exact_mod_cast h0
        have hSI_eq : ∑ τ ∈ D, ((a τ : ℝ)) ^ 2 = (L.card : ℝ) := by
          rw [hD_split, Finset.sum_union hD_disj, Finset.card_eq_zero.mp hD'0]
          simp only [Finset.sum_empty, add_zero]
          calc ∑ τ ∈ L, ((a τ : ℝ)) ^ 2 = ∑ _τ ∈ L, (1 : ℝ) :=
                Finset.sum_congr rfl fun τ hτ => by rw [haL τ hτ]; norm_num
            _ = (L.card : ℝ) := by simp
        have : (L.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast card_le_card hLD
        linarith
      rw [h4, mul_div_cancel_right₀ _ hD'ne]
      norm_num
    have hd_all0 : ∀ τ ∈ D, d τ = 0 := by
      intro τ hτ
      by_cases hL : τ ∈ L
      · exact (hd τ hτ).2 (mem_filter.mp hL).2
      · have hτ' : τ ∈ D' := Finset.mem_sdiff.mpr ⟨hτ, hL⟩
        rcases ha_eq_pm τ hτ' with h0 | h2
        · exact h0
        · exfalso
          have hxτ := hxR_eq τ hτ'
          rw [hrms2] at hxτ
          have ha_neg : (a τ : ℝ) = -2 := by simp [a, hD'_all2 τ hτ', h2]
          rw [ha_neg] at hxτ
          linarith [hsupp τ hτ]
    have hdec : IsDecomposition D := by
      rw [← hdist.2]
      have hnat_eq : (∑ τ ∈ D, (2 : ℝ) ^ weight τ) = (2 : ℝ) ^ k := by
        rw [hD_split, Finset.sum_union hD_disj, hEq4]
        have hL2 : ∑ τ ∈ L, (2 : ℝ) ^ weight τ = 2 * (L.card : ℝ) := by
          calc ∑ τ ∈ L, (2 : ℝ) ^ weight τ = ∑ _τ ∈ L, (2 : ℝ) :=
                Finset.sum_congr rfl fun τ hτ => by rw [(mem_filter.mp hτ).2]; norm_num
            _ = 2 * (L.card : ℝ) := by simp [mul_comm]
        linarith
      exact_mod_cast hnat_eq
    refine ⟨⟨D, hdec, fun τ hτ => ?_, hout⟩, hd_all0⟩
    by_cases hL : τ ∈ L
    · exact Or.inl ⟨(mem_filter.mp hL).2, hxL_eq τ hL⟩
    · have hτ' : τ ∈ D' := Finset.mem_sdiff.mpr ⟨hτ, hL⟩
      have hw2 := hD'_all2 τ hτ'
      have hxτ := hxR_eq τ hτ'
      rw [hrms2] at hxτ
      have ha2 : (a τ : ℝ) = 2 := by simp [a, hw2, hd_all0 τ hτ]
      rw [ha2] at hxτ
      exact Or.inr ⟨hw2, by linarith⟩
  ·
    have hle_m : ∑ τ ∈ D, ((a τ : ℝ)) ^ 2 ≤ (D.card : ℝ) := not_lt.mp hcase
    have hb1 := hlag.2 hle_m
    have hsqrt_le : Real.sqrt ((D.card : ℝ) * ∑ τ ∈ D, ((a τ : ℝ)) ^ 2) ≤ (D.card : ℝ) := by
      calc Real.sqrt ((D.card : ℝ) * ∑ τ ∈ D, ((a τ : ℝ)) ^ 2)
          ≤ Real.sqrt ((D.card : ℝ) * (D.card : ℝ)) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle_m (Nat.cast_nonneg _))
        _ = (D.card : ℝ) := by rw [← sq, Real.sqrt_sq (Nat.cast_nonneg _)]
    have hsum_a : ∑ τ ∈ D, (a τ : ℝ) = (∑ τ ∈ D, (weight τ : ℝ)) - 2 * ∑ τ ∈ D, (d τ : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => by simp [a]
    have hw_le_pow : ∀ τ ∈ D, (weight τ : ℝ) ≤ (2 : ℝ) ^ (weight τ - 1) := by
      intro τ hτ
      have h1 := hD.1 τ hτ
      have hnat : weight τ ≤ 2 ^ (weight τ - 1) := by
        have : ∀ n : ℕ, 1 ≤ n → n ≤ 2 ^ (n - 1) := by
          intro n hn
          induction n with
          | zero => omega
          | succ m ihm =>
            cases m with
            | zero => norm_num
            | succ m' =>
              have := ihm (by omega)
              simp only [Nat.add_sub_cancel] at this ⊢
              rw [pow_succ]; omega
        exact this _ h1
      exact_mod_cast hnat
    have hcard_le : 2 * (D.card : ℝ) ≤ ∑ τ ∈ D, (2 : ℝ) ^ weight τ := by
      calc 2 * (D.card : ℝ) = ∑ _τ ∈ D, (2 : ℝ) := by simp [mul_comm]
        _ ≤ ∑ τ ∈ D, (2 : ℝ) ^ weight τ := sum_le_sum fun τ hτ => by
            have : 2 ≤ 2 ^ weight τ := Nat.le_self_pow (by have := hD.1 τ hτ; omega) 2
            exact_mod_cast this
    have hpow_le : (∑ τ ∈ D, (2 : ℝ) ^ weight τ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hdist.1
    have hD_le : (D.card : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by linarith
    have hhalf_pow : ∑ τ ∈ D, (2 : ℝ) ^ (weight τ - 1) = (1 / 2) * ∑ τ ∈ D, (2 : ℝ) ^ weight τ := by
      rw [mul_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have h1 := hD.1 τ hτ
      have : (2 : ℝ) ^ weight τ = 2 * (2 : ℝ) ^ (weight τ - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ']
      linarith
    have hw_sum_le : ∑ τ ∈ D, (weight τ : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by
      calc ∑ τ ∈ D, (weight τ : ℝ)
          ≤ ∑ τ ∈ D, (2 : ℝ) ^ (weight τ - 1) := sum_le_sum hw_le_pow
        _ = (1 / 2) * ∑ τ ∈ D, (2 : ℝ) ^ weight τ := hhalf_pow
        _ ≤ (2 : ℝ) ^ (k - 1) := by linarith
    have hmain : ∑ τ ∈ D, x τ ≤ (2 : ℝ) ^ (k - 1) - ∑ τ ∈ D, (d τ : ℝ) := by
      rw [hsum_a] at hb1; linarith
    refine ⟨hmain, fun heq => ?_⟩
    have hD_eq : (D.card : ℝ) = (2 : ℝ) ^ (k - 1) := by rw [hsum_a] at hb1; linarith
    have hpow_eq : ∑ τ ∈ D, (2 : ℝ) ^ weight τ = (2 : ℝ) ^ k := by linarith
    have hdec : IsDecomposition D := hdist.2.mp (by exact_mod_cast hpow_eq)
    have hall1 : ∀ τ ∈ D, weight τ = 1 := by
      intro τ hτ
      have hsum0 : ∑ σ ∈ D, ((2 : ℝ) ^ weight σ - 2) = 0 := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; linarith
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun σ hσ => by
        have : 2 ≤ 2 ^ weight σ := Nat.le_self_pow (by have := hD.1 σ hσ; omega) 2
        have : (2 : ℝ) ≤ (2 : ℝ) ^ weight σ := by exact_mod_cast this
        linarith).mp hsum0 τ hτ
      have hnat : 2 ^ weight τ = 2 := by exact_mod_cast (show (2 : ℝ) ^ weight τ = 2 by linarith)
      have h1 := hD.1 τ hτ
      by_contra hne1
      have hge4 : 4 ≤ 2 ^ weight τ := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ weight τ := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hd_all0 : ∀ τ ∈ D, d τ = 0 := fun τ hτ => (hd τ hτ).2 (hall1 τ hτ)
    have hx_all1 : ∀ τ ∈ D, x τ = 1 := by
      have hd0_sum : ∑ τ ∈ D, (d τ : ℝ) = 0 := sum_eq_zero fun τ hτ => by rw [hd_all0 τ hτ]; simp
      have hsum0 : ∑ τ ∈ D, (1 - x τ) = 0 := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]; linarith
      intro τ hτ
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun σ hσ => by
        linarith [hx1 σ hσ (hall1 σ hσ)]).mp hsum0 τ hτ
      linarith
    exact ⟨⟨D, hdec, fun τ hτ => Or.inl ⟨hall1 τ hτ, hx_all1 τ hτ⟩, hout⟩, hd_all0⟩
lemma corollary_Ocompress {k : ℕ} (hk : 1 ≤ k) :
    (∀ x : Subcube k → ℝ, IsCompressed x → InO x) ∧
    (∀ x : Subcube k → ℝ, InX 0 x → l1Sum x ≤ (2 : ℝ) ^ (k - 1)) := by
  have hexO : ∃ z : Subcube k → ℝ, InO z := by
    let D0 : Finset (Subcube k) := Finset.univ.filter (fun τ =>
      τ ⟨0, by omega⟩ = 2 ∧ ∀ i : Fin k, i ≠ ⟨0, by omega⟩ → τ i = 0 ∨ τ i = 1)
    have hD0_dec : IsDecomposition D0 := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro τ hτ
        have h := (mem_filter.mp hτ).2
        have hmem : (⟨0, by omega⟩ : Fin k) ∈ Finset.univ.filter (fun i : Fin k => τ i = 2) :=
          mem_filter.mpr ⟨mem_univ _, h.1⟩
        exact card_pos.mpr ⟨_, hmem⟩
      · intro σ hσ τ hτ hne
        have hp1 := (mem_filter.mp hσ).2
        have hp2 := (mem_filter.mp hτ).2
        have hex_i : ∃ i, σ i ≠ τ i := by by_contra hall; push Not at hall; exact hne (funext hall)
        obtain ⟨i, hi⟩ := hex_i
        have hne0 : i ≠ ⟨0, by omega⟩ := by rintro rfl; exact hi (hp1.1.trans hp2.1.symm)
        rcases hp1.2 i hne0 with a | a <;> rcases hp2.2 i hne0 with b | b
        · exact absurd (a.trans b.symm) hi
        · exact ⟨i, Or.inl ⟨a, b⟩⟩
        · exact ⟨i, Or.inr ⟨a, b⟩⟩
        · exact absurd (a.trans b.symm) hi
      · ext c
        simp only [mem_biUnion, mem_univ, iff_true]
        let τ : Subcube k := fun i => if i = ⟨0, by omega⟩ then 2 else if c i then 1 else 0
        refine ⟨τ, mem_filter.mpr ⟨mem_univ _, by simp [τ], fun i hi => ?_⟩, ?_⟩
        · simp only [τ, if_neg hi]; split_ifs <;> simp
        · refine mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩
          by_cases hi : i = ⟨0, by omega⟩
          · subst hi; simp [τ]
          · simp only [τ, if_neg hi]; cases c i <;> simp
    have hD0_w1 : ∀ τ ∈ D0, weight τ = 1 := by
      intro τ hτ
      have h := (mem_filter.mp hτ).2
      have heq : Finset.univ.filter (fun i : Fin k => τ i = 2) = {⟨0, by omega⟩} := by
        ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hi2; by_contra hne
          rcases h.2 i hne with h0 | h1 <;> simp_all
        · rintro rfl; exact h.1
      rw [weight, heq, card_singleton]
    exact ⟨fun τ => if τ ∈ D0 then 1 else 0, D0, hD0_dec,
      fun τ hτ => Or.inl ⟨hD0_w1 τ hτ, if_pos hτ⟩, fun τ hτ => if_neg hτ⟩
  obtain ⟨z0, hz0O⟩ := hexO
  obtain ⟨hz0X, hz0_sum⟩ := InO_mem_InX_and_sum hk hz0O
  have hcomp_in_O : ∀ x : Subcube k → ℝ, IsCompressed x → InO x := by
    classical
    intro x hx
    obtain ⟨hR_dist, hdeg, hl1, hsphere⟩ := compressed_sphere_and_degrees hk hx
    let xR : Subcube k → ℝ := fun τ => if τ ∈ rootsFinset x then x τ else 0
    have hxR_pos : ∀ τ ∈ rootsFinset x, 0 < xR τ := fun τ hτ => by
      dsimp only [xR]; rw [if_pos hτ]
      exact lt_of_le_of_ne (hx.1.1.1 τ) (mem_filter.mp (Finset.mem_sdiff.mp hτ).1).2.symm
    have hxR_out : ∀ τ, τ ∉ rootsFinset x → xR τ = 0 := fun τ hτ => if_neg hτ
    have hsphereR : ∑ τ ∈ rootsFinset x, (xR τ ^ 2 + (2 * (outDeg x τ : ℝ) - (weight τ : ℝ)) * xR τ) = 0 := by
      rw [← hsphere]
      exact Finset.sum_congr rfl fun τ hτ => by dsimp only [xR]; rw [if_pos hτ]
    have hxR1 : ∀ τ ∈ rootsFinset x, weight τ = 1 → xR τ ≤ 1 := fun τ hτ hw1 => by
      dsimp only [xR]; rw [if_pos hτ]; simpa using hx.1.1.2.2.1 τ hw1
    obtain ⟨hle, heq_iff⟩ := proposition_convex hk (rootsFinset x) hR_dist (outDeg x) hdeg
      xR hxR_pos hxR_out hsphereR hxR1
    have hsum_xR : ∑ τ ∈ rootsFinset x, xR τ = ∑ τ ∈ rootsFinset x, x τ :=
      Finset.sum_congr rfl fun τ hτ => if_pos hτ
    rw [hsum_xR] at hle heq_iff
    have hge : (2 : ℝ) ^ (k - 1) ≤ l1Sum x := hz0_sum ▸ hx.1.2 z0 hz0X
    have heq_R : ∑ τ ∈ rootsFinset x, x τ = (2 : ℝ) ^ (k - 1) - ∑ τ ∈ rootsFinset x, (outDeg x τ : ℝ) := by
      linarith
    obtain ⟨hxRO, hd0⟩ := heq_iff heq_R
    have hx_eq_xR : x = xR := by
      funext τ
      dsimp only [xR]
      by_cases hR : τ ∈ rootsFinset x
      · rw [if_pos hR]
      · rw [if_neg hR]
        by_contra hne0
        have hτs : τ ∈ suppFinset x := mem_filter.mpr ⟨mem_univ _, hne0⟩
        have hτL : τ ∈ leavesFinset x := by
          by_contra hnotL; exact hR (Finset.mem_sdiff.mpr ⟨hτs, hnotL⟩)
        obtain ⟨ρ, hE⟩ := (mem_filter.mp hτL).2
        have ⟨hstar1, _⟩ := star_props hk hx
        have hρR : ρ ∈ rootsFinset x := by
          refine Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hE.1⟩, ?_⟩
          intro hρL; obtain ⟨ρ', hE'⟩ := (mem_filter.mp hρL).2
          have := (hstar1 ρ τ hE).1; have := (hstar1 ρ' ρ hE').2.1; omega
        have hpos : 0 < outDeg x ρ := card_pos.mpr ⟨τ, mem_filter.mpr ⟨hτs, hE⟩⟩
        have := hd0 ρ hρR
        omega
    rwa [hx_eq_xR]
  have hle_all : ∀ x : Subcube k → ℝ, InX 0 x → l1Sum x ≤ (2 : ℝ) ^ (k - 1) := by
    obtain ⟨xopt, hxopt⟩ := exists_optimal (k := k)
    have hcomp_ex : ∃ z : Subcube k → ℝ, IsCompressed z := by
      rcases exists_compressed_from_optimal hk xopt hxopt with hc | ⟨y, π, ρ, _, _, _, hc, _⟩
      · exact ⟨xopt, hc⟩
      · exact ⟨compress y π ρ, hc⟩
    obtain ⟨z, hz⟩ := hcomp_ex
    have hzO := hcomp_in_O z hz
    have hz_sum := (InO_mem_InX_and_sum hk hzO).2
    intro x hx
    exact (hz.1.2 x hx).trans hz_sum.le
  exact ⟨hcomp_in_O, hle_all⟩
lemma proposition_props2 {k : ℕ} (hk : 1 ≤ k) (x : Subcube k → ℝ) (hx : InX 0 x) :
    l1Sum x ≤ (2 : ℝ) ^ (k - 1) ∧ (l1Sum x = (2 : ℝ) ^ (k - 1) ↔ InO x) := by
  obtain ⟨hcomp_O, hle_all⟩ := corollary_Ocompress hk
  refine ⟨hle_all x hx, ⟨?_, fun hO => (InO_mem_InX_and_sum hk hO).2⟩⟩
  intro heq
  have hopt : IsOptimal x := ⟨hx, fun z hz => (hle_all z hz).trans heq.ge⟩
  rcases exists_compressed_from_optimal hk x hopt with hc | ⟨y, π, ρ, hy_opt, hEdge, hwρ, hz_comp, hπ0⟩
  · exact hcomp_O x hc
  ·
    exfalso
    set z := compress y π ρ
    have hzO : InO z := hcomp_O z hz_comp
    obtain ⟨D, hdec, hDval, hout⟩ := hzO
    have hne : π ≠ ρ := hEdge.2.2.1
    have hnd : ¬ distinguishable π ρ := hEdge.2.2.2.1
    have hy_shift : y = Function.update (Function.update z π (z π - (- y π))) ρ (z ρ + (- y π)) := by
      have hz_eq : z = Function.update (Function.update y π 0) ρ (y π + y ρ) := by
        dsimp only [z, compress]; rw [if_pos (Or.inl hwρ)]
      funext τ
      by_cases h1 : τ = ρ
      · subst h1; simp [hz_eq]
      · by_cases h2 : τ = π
        · subst h2; simp [hz_eq, h1]
        · simp [hz_eq, h1, h2]
    have hFy0 : quadForm y = 0 := quadForm_eq_zero_of_optimal hk hy_opt
    have hFz0 : quadForm z = 0 := quadForm_eq_zero_of_optimal hk hz_comp.1
    have hshift := quadForm_shift_indistinguishable z hne hnd (- y π)
    dsimp only at hshift
    rw [← hy_shift, hFy0, hFz0, sub_self] at hshift
    have hyπ_ne : y π ≠ 0 := hEdge.1
    have hgrad : ((weight π : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable π τ then z τ else 0) =
        ((weight ρ : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable ρ τ then z τ else 0) := by
      have h0 : (- y π) * (((weight π : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable π τ then z τ else 0)
         - ((weight ρ : ℝ) + 2 * ∑ τ : Subcube k, if distinguishable ρ τ then z τ else 0)) = 0 := hshift.symm
      have := (mul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr hyπ_ne)
      linarith
    have hsum_z : ∑ τ : Subcube k, z τ = (2 : ℝ) ^ (k - 1) := (InO_mem_InX_and_sum hk ⟨D, hdec, hDval, hout⟩).2
    have hsplit_ind : ∀ α : Subcube k,
        (∑ τ : Subcube k, if distinguishable α τ then z τ else 0) =
        (2 : ℝ) ^ (k - 1) - (∑ τ ∈ D, if distinguishable α τ then 0 else z τ) := by
      intro α
      have h1 : (∑ τ : Subcube k, if distinguishable α τ then z τ else 0) +
          (∑ τ : Subcube k, if distinguishable α τ then 0 else z τ) = ∑ τ : Subcube k, z τ := by
        rw [← sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> ring
      have h2 : ∑ τ : Subcube k, (if distinguishable α τ then (0 : ℝ) else z τ) =
          ∑ τ ∈ D, (if distinguishable α τ then (0 : ℝ) else z τ) := by
        symm; exact Finset.sum_subset (subset_univ D) fun τ _ hτ => by rw [hout τ hτ, ite_self]
      linarith
    rw [hsplit_ind π, hsplit_ind ρ] at hgrad
    have hρD : ρ ∈ D := by
      by_contra hnot
      have h0 : z ρ = 0 := hout ρ hnot
      have hpos : 0 < y π + y ρ := add_pos (lt_of_le_of_ne (hy_opt.1.1 π) hyπ_ne.symm)
        (lt_of_le_of_ne (hy_opt.1.1 ρ) hEdge.2.1.symm)
      have hzρ : z ρ = y π + y ρ := by dsimp only [z, compress]; rw [if_pos (Or.inl hwρ)]; simp
      linarith
    have hwρ2 : weight ρ = 2 ∧ z ρ = 2 := by
      rcases hDval ρ hρD with ⟨hw1, _⟩ | h2
      · omega
      · exact h2
    have hρ_sum : ∑ τ ∈ D, (if distinguishable ρ τ then (0 : ℝ) else z τ) = 2 := by
      rw [Finset.sum_eq_single ρ]
      · simp [not_distinguishable_self, hwρ2.2]
      · intro τ hτ hne'
        rw [if_pos (hdec.1.2 ρ hρD τ hτ hne'.symm)]
      · intro h; exact absurd hρD h
    let Iπ := D.filter (fun τ => ¬ distinguishable π τ)
    have hπ_sum : ∑ τ ∈ D, (if distinguishable π τ then (0 : ℝ) else z τ) = ∑ τ ∈ Iπ, z τ := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    rw [hρ_sum, hwρ2.1, hπ_sum] at hgrad
    have hkey_eq : 2 * ∑ τ ∈ Iπ, z τ - (weight π : ℝ) = 2 := by norm_num at hgrad; linarith
    have h2z_pow : 2 * ∑ τ ∈ Iπ, z τ = ∑ τ ∈ Iπ, (2 : ℝ) ^ weight τ := by
      rw [mul_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rcases hDval τ (mem_filter.mp hτ).1 with ⟨hw, hv⟩ | ⟨hw, hv⟩ <;> simp [hw, hv] <;> norm_num
    have hQπ_sub : subcubeSet π ⊆ Iπ.biUnion subcubeSet := by
      intro c hc
      have hcU : c ∈ D.biUnion subcubeSet := by rw [hdec.2]; exact mem_univ c
      rcases mem_biUnion.mp hcU with ⟨τ, hτD, hcτ⟩
      refine mem_biUnion.mpr ⟨τ, mem_filter.mpr ⟨hτD, ?_⟩, hcτ⟩
      rw [distinguishable_iff_disjoint_subcubeSet, Finset.not_disjoint_iff]
      exact ⟨c, hc, hcτ⟩
    have hdisj_Iπ : (Iπ : Set (Subcube k)).PairwiseDisjoint subcubeSet := by
      intro τ₁ h₁ τ₂ h₂ hne'
      change Disjoint (subcubeSet τ₁) (subcubeSet τ₂)
      exact (distinguishable_iff_disjoint_subcubeSet τ₁ τ₂).mp
        (hdec.1.2 τ₁ (mem_filter.mp h₁).1 τ₂ (mem_filter.mp h₂).1 hne')
    have hcard_le : 2 ^ weight π ≤ ∑ τ ∈ Iπ, 2 ^ weight τ := by
      have h1 := card_le_card hQπ_sub
      rw [card_subcubeSet, card_biUnion hdisj_Iπ] at h1
      simpa [card_subcubeSet] using h1
    have hcard_le_R : (2 : ℝ) ^ weight π ≤ ∑ τ ∈ Iπ, (2 : ℝ) ^ weight τ := by exact_mod_cast hcard_le
    have hρ_in_Iπ : ρ ∈ Iπ := mem_filter.mpr ⟨hρD, hnd⟩
    have hge4 : (4 : ℝ) ≤ ∑ τ ∈ Iπ, (2 : ℝ) ^ weight τ := by
      have h1 : (2 : ℝ) ^ weight ρ ≤ ∑ τ ∈ Iπ, (2 : ℝ) ^ weight τ :=
        single_le_sum (f := fun τ => (2 : ℝ) ^ weight τ) (fun _ _ => by positivity) hρ_in_Iπ
      rw [hwρ2.1] at h1; norm_num at h1; exact h1
    have hwπ_ge2 : 2 ≤ weight π := by
      have : (2 : ℝ) ≤ (weight π : ℝ) := by linarith
      exact_mod_cast this
    have hwπ_le2 : weight π ≤ 2 := by
      by_contra hgt2
      have hge3 : 3 ≤ weight π := by omega
      have hpow_gt : ∀ m : ℕ, 3 ≤ m → m + 3 ≤ 2 ^ m := by
        intro m hm
        induction m with
        | zero => omega
        | succ n ihn =>
          by_cases hn3 : 3 ≤ n
          · have := ihn hn3; rw [pow_succ]; omega
          · have : n = 2 := by omega
            subst this; norm_num
      have h1 : (weight π : ℝ) + 3 ≤ (2 : ℝ) ^ weight π := by exact_mod_cast hpow_gt _ hge3
      linarith
    have hwπ2 : weight π = 2 := by omega
    have hsum_eq4 : ∑ τ ∈ Iπ, 2 ^ weight τ = 4 := by
      have : ∑ τ ∈ Iπ, (2 : ℝ) ^ weight τ = 4 := by rw [hwπ2] at hkey_eq; norm_num at hkey_eq; linarith
      exact_mod_cast this
    have hIπ_eq : Iπ = {ρ} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hρ_in_Iπ, fun τ hτ => ?_⟩
      by_contra hne'
      have hpair : ({ρ, τ} : Finset (Subcube k)) ⊆ Iπ := by
        intro u hu; rcases mem_insert.mp hu with rfl | hu'
        · exact hρ_in_Iπ
        · rw [mem_singleton] at hu'; exact hu' ▸ hτ
      have hsum_sub := Finset.sum_le_sum_of_subset_of_nonneg (f := fun σ => 2 ^ weight σ) hpair (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair (Ne.symm hne'), hwρ2.1] at hsum_sub
      have hτ_pos : 2 ≤ 2 ^ weight τ := Nat.le_self_pow (by have := hdec.1.1 τ (mem_filter.mp hτ).1; omega) 2
      omega
    rw [hIπ_eq, Finset.singleton_biUnion] at hQπ_sub
    have hQeq : subcubeSet π = subcubeSet ρ :=
      Finset.eq_of_subset_of_card_le hQπ_sub (by rw [card_subcubeSet, card_subcubeSet, hwπ2, hwρ2.1])
    apply hne
    funext i
    by_contra hneq
    have hboth : ∀ (α : Subcube k) (j : Fin k), α j = 2 →
        (∃ c ∈ subcubeSet α, c j = true) ∧ (∃ c ∈ subcubeSet α, c j = false) := by
      intro α j hj
      constructor
      · refine ⟨fun t => if t = j then true else decide (α t = 1),
          mem_filter.mpr ⟨mem_univ _, fun t => ?_⟩, by simp⟩
        by_cases ht : t = j
        · subst ht; simp [hj]
        · simp [ht]; intro h0; simp [h0]
      · refine ⟨fun t => if t = j then false else decide (α t = 1),
          mem_filter.mpr ⟨mem_univ _, fun t => ?_⟩, by simp⟩
        by_cases ht : t = j
        · subst ht; simp [hj]
        · simp [ht]; intro h0; simp [h0]
    have hcases : (π i = 2 ∧ (ρ i = 0 ∨ ρ i = 1)) ∨ (ρ i = 2 ∧ (π i = 0 ∨ π i = 1)) := by
      have h01 : ¬ ((π i = 0 ∧ ρ i = 1) ∨ (π i = 1 ∧ ρ i = 0)) := fun h => hnd ⟨i, h⟩
      generalize hπi : π i = a at hneq h01 ⊢
      generalize hρi : ρ i = b at hneq h01 ⊢
      fin_cases a <;> fin_cases b <;>
        first
        | exact absurd rfl hneq
        | exact absurd (Or.inl ⟨rfl, rfl⟩) h01
        | exact absurd (Or.inr ⟨rfl, rfl⟩) h01
        | exact Or.inl ⟨rfl, Or.inl rfl⟩
        | exact Or.inl ⟨rfl, Or.inr rfl⟩
        | exact Or.inr ⟨rfl, Or.inl rfl⟩
        | exact Or.inr ⟨rfl, Or.inr rfl⟩
    rcases hcases with ⟨hπ2, hρ0 | hρ1⟩ | ⟨hρ2, hπ0 | hπ1⟩
    · obtain ⟨⟨c, hc, hct⟩, _⟩ := hboth π i hπ2
      rw [hQeq] at hc; have := ((mem_filter.mp hc).2 i).1 hρ0; simp [hct] at this
    · obtain ⟨_, ⟨c, hc, hcf⟩⟩ := hboth π i hπ2
      rw [hQeq] at hc; have := ((mem_filter.mp hc).2 i).2 hρ1; simp [hcf] at this
    · obtain ⟨⟨c, hc, hct⟩, _⟩ := hboth ρ i hρ2
      rw [← hQeq] at hc; have := ((mem_filter.mp hc).2 i).1 hπ0; simp [hct] at this
    · obtain ⟨_, ⟨c, hc, hcf⟩⟩ := hboth ρ i hρ2
      rw [← hQeq] at hc; have := ((mem_filter.mp hc).2 i).2 hπ1; simp [hcf] at this
lemma continuous_l1Dist {k : ℕ} (y : Subcube k → ℝ) : Continuous (fun x => l1Dist x y) :=
  continuous_finset_sum _ fun τ _ => ((continuous_apply τ).sub continuous_const).abs
lemma stability_close1 {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x : Subcube k → ℝ, InX γ x → l1Sum x = (2 : ℝ) ^ (k - 1) →
      ∃ xStar : Subcube k → ℝ, InO xStar ∧ l1Dist x xStar < ε := by
  by_contra hno
  push Not at hno
  have hseq : ∀ m : ℕ, ∃ x : Subcube k → ℝ, InX (1 / ((m : ℝ) + 1)) x ∧
      l1Sum x = (2 : ℝ) ^ (k - 1) ∧ ∀ xStar, InO xStar → ε ≤ l1Dist x xStar :=
    fun m => hno (1 / ((m : ℝ) + 1)) (by positivity)
  choose x hx_in hx_sum hx_far using hseq
  have hx_in1 : ∀ m : ℕ, x m ∈ {z : Subcube k → ℝ | InX 1 z} := fun m => by
    have hle1 : 1 / ((m : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by positivity)
    exact ⟨(hx_in m).1, (hx_in m).2.1.trans hle1,
      fun τ hw => (hx_in m).2.2.1 τ hw |>.trans (by linarith),
      fun σ τ hnc => (hx_in m).2.2.2 σ τ hnc |>.trans hle1⟩
  obtain ⟨x0, _, φ, hφ_mono, hφ_lim⟩ :=
    (isCompact_InX_clean (k := k) (γ := 1) zero_le_one).tendsto_subseq hx_in1
  have hlim_zero : Tendsto (fun m : ℕ => 1 / (((φ m : ℕ) : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ_mono.tendsto_atTop
  have hcoord : ∀ τ : Subcube k, Tendsto (fun m => x (φ m) τ) atTop (𝓝 (x0 τ)) :=
    fun τ => (continuous_apply τ).continuousAt.tendsto.comp hφ_lim
  have hx0_in0 : InX 0 x0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro τ
      exact ge_of_tendsto (hcoord τ) (Eventually.of_forall fun m => (hx_in (φ m)).1 τ)
    · have hq_cont : Continuous (@quadForm k) := by
        unfold quadForm
        refine Continuous.sub (Continuous.sub ?_ ?_) ?_
        · exact (continuous_finsetSum _ fun τ _ => continuous_apply τ).pow 2
        · exact continuous_finsetSum _ fun σ _ => continuous_finsetSum _ fun τ _ => by
            by_cases hd : distinguishable σ τ
            · simp only [if_pos hd]; exact (continuous_apply σ).mul (continuous_apply τ)
            · simp only [if_neg hd]; exact continuous_const
        · exact continuous_finsetSum _ fun τ _ => continuous_const.mul (continuous_apply τ)
      exact le_of_tendsto_of_tendsto (hq_cont.continuousAt.tendsto.comp hφ_lim) hlim_zero
        (Eventually.of_forall fun m => (hx_in (φ m)).2.1)
    · intro τ h1
      have hlim1 : Tendsto (fun m : ℕ => 1 + 1 / (((φ m : ℕ) : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add hlim_zero
      exact le_of_tendsto_of_tendsto (hcoord τ) hlim1
        (Eventually.of_forall fun m => (hx_in (φ m)).2.2.1 τ h1)
    · intro σ τ hnc
      exact le_of_tendsto_of_tendsto ((hcoord σ).mul (hcoord τ)) hlim_zero
        (Eventually.of_forall fun m => (hx_in (φ m)).2.2.2 σ τ hnc)
  have hx0_sum : l1Sum x0 = (2 : ℝ) ^ (k - 1) := by
    have hcont : Continuous (@l1Sum k) := continuous_finsetSum _ fun τ _ => continuous_apply τ
    have h1 : Tendsto (fun m => l1Sum (x (φ m))) atTop (𝓝 (l1Sum x0)) :=
      hcont.continuousAt.tendsto.comp hφ_lim
    have h2 : (fun m => l1Sum (x (φ m))) = fun _ => (2 : ℝ) ^ (k - 1) := funext fun m => hx_sum (φ m)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hx0_O : InO x0 := (proposition_props2 hk x0 hx0_in0).2.mp hx0_sum
  have hdist_lim : Tendsto (fun m => l1Dist (x (φ m)) x0) atTop (𝓝 0) := by
    have h0 : l1Dist x0 x0 = 0 := by simp [l1Dist]
    rw [← h0]
    exact (continuous_l1Dist x0).continuousAt.tendsto.comp hφ_lim
  obtain ⟨m, hm⟩ := (hdist_lim.eventually (gt_mem_nhds hε)).exists
  linarith [hx_far (φ m) x0 hx0_O]
lemma fact_simple_dense_subgraph_exact {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {δ : ℝ} (hδ0 : 0 < δ)
    (hdense : (1 - δ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2) ≤ H.edgeFinset.card) :
    ∃ S : Finset V, (1 - Real.sqrt δ) * (Fintype.card V : ℝ) ≤ (S.card : ℝ) ∧
      ∀ v ∈ S, (1 - 2 * Real.sqrt δ) * (Fintype.card V : ℝ) - 1 ≤ ((H.neighborFinset v ∩ S).card : ℝ) := by
  classical
  let t : ℝ := (Fintype.card V : ℝ)
  by_cases ht1 : Fintype.card V ≤ 1
  · refine ⟨Finset.univ, ?_, fun v _ => ?_⟩
    · rw [card_univ]; nlinarith [Real.sqrt_nonneg δ, Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
    · have ht_le1 : t ≤ 1 := by dsimp only [t]; exact_mod_cast ht1
      have : (0 : ℝ) ≤ ((H.neighborFinset v ∩ Finset.univ).card : ℝ) := Nat.cast_nonneg _
      nlinarith [Real.sqrt_nonneg δ]
  · have ht_gt1 : (1 : ℝ) < t := by dsimp only [t]; exact_mod_cast (show 1 < Fintype.card V by omega)
    let S : Finset V := Finset.univ.filter (fun v => (1 - Real.sqrt δ) * (t - 1) ≤ ((H.neighborFinset v).card : ℝ))
    let B : Finset V := Finset.univ \ S
    have hSB : S.card + B.card = Fintype.card V := by
      have := card_sdiff_add_card_eq_card (subset_univ S)
      rw [card_univ] at this
      change B.card + S.card = Fintype.card V at this
      omega
    have hsum_deg : ∑ v : V, ((H.neighborFinset v).card : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
      have h := H.sum_degrees_eq_twice_card_edges
      simp_rw [← SimpleGraph.card_neighborFinset_eq_degree] at h
      exact_mod_cast h
    have hmiss_nonneg : ∀ v : V, 0 ≤ t - 1 - ((H.neighborFinset v).card : ℝ) := by
      intro v
      have hle : (H.neighborFinset v).card ≤ Fintype.card V - 1 := by
        have hsub : H.neighborFinset v ⊆ Finset.univ.erase v := fun w hw =>
          mem_erase.mpr ⟨(H.ne_of_adj ((mem_neighborFinset H v w).mp hw)).symm, mem_univ _⟩
        have := card_le_card hsub
        rwa [card_erase_of_mem (mem_univ v), card_univ] at this
      have h1 : ((H.neighborFinset v).card : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by exact_mod_cast hle
      rw [Nat.cast_sub (by omega), Nat.cast_one] at h1
      linarith
    have hB_le : (B.card : ℝ) ≤ Real.sqrt δ * t := by
      have h1 : (B.card : ℝ) * (Real.sqrt δ * (t - 1)) ≤ ∑ v ∈ B, (t - 1 - ((H.neighborFinset v).card : ℝ)) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun v hv => ?_
        have hnotS : ¬ (1 - Real.sqrt δ) * (t - 1) ≤ ((H.neighborFinset v).card : ℝ) := by
          intro h; exact (Finset.mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
        linarith
      have h2 : ∑ v ∈ B, (t - 1 - ((H.neighborFinset v).card : ℝ)) ≤
          ∑ v : V, (t - 1 - ((H.neighborFinset v).card : ℝ)) :=
        sum_le_univ_sum_of_nonneg hmiss_nonneg
      have h3 : ∑ v : V, (t - 1 - ((H.neighborFinset v).card : ℝ)) ≤ δ * t * (t - 1) := by
        rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hsum_deg]
        change t * (t - 1) - 2 * (H.edgeFinset.card : ℝ) ≤ δ * t * (t - 1)
        linarith
      have hpos : 0 < Real.sqrt δ * (t - 1) := mul_pos (Real.sqrt_pos.mpr hδ0) (by linarith)
      have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
      have h4 : (B.card : ℝ) * (Real.sqrt δ * (t - 1)) ≤ (Real.sqrt δ * t) * (Real.sqrt δ * (t - 1)) := by
        have heq : (Real.sqrt δ * t) * (Real.sqrt δ * (t - 1)) = δ * t * (t - 1) := by
          linear_combination t * (t - 1) * hsq
        linarith
      exact le_of_mul_le_mul_right h4 hpos
    refine ⟨S, ?_, ?_⟩
    · have hSBr : (S.card : ℝ) + (B.card : ℝ) = t := by dsimp only [t]; exact_mod_cast hSB
      linarith
    · intro v hv
      have hdv : (1 - Real.sqrt δ) * (t - 1) ≤ ((H.neighborFinset v).card : ℝ) :=
        (mem_filter.mp hv).2
      have hsub : H.neighborFinset v ⊆ (H.neighborFinset v ∩ S) ∪ B := fun w hw => by
        by_cases hwS : w ∈ S
        · exact mem_union_left _ (mem_inter.mpr ⟨hw, hwS⟩)
        · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨mem_univ _, hwS⟩)
      have hcard := (card_le_card hsub).trans (card_union_le _ _)
      have hcard_r : ((H.neighborFinset v).card : ℝ) ≤ ((H.neighborFinset v ∩ S).card : ℝ) + (B.card : ℝ) := by
        exact_mod_cast hcard
      have hspos : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
      linarith
set_option maxHeartbeats 800000 in
lemma two_colour_connected_matching {V : Type*} [Fintype V] [DecidableEq V]
    (H R B : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj] [DecidableRel B.Adj]
    (hcover : ∀ u v, H.Adj u v → R.Adj u v ∨ B.Adj u v)
    (hRsub : ∀ u v, R.Adj u v → H.Adj u v)
    (hBsub : ∀ u v, B.Adj u v → H.Adj u v)
    {δ n : ℝ} (hδ0 : 0 < δ) (hδ_small : δ ≤ 1 / 40000) (hn : 1000 ≤ n)
    (hN : (18 / 10 : ℝ) * n ≤ (Fintype.card V : ℝ))
    (hdense : (1 - δ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2) ≤ H.edgeFinset.card) :
    (∃ C : R.ConnectedComponent, ∃ M : Finset (Sym2 V),
      IsMatching R M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ C.supp) ∧ (21 / 20 : ℝ) * n ≤ (2 * M.card : ℝ)) ∨
    (∃ C : B.ConnectedComponent, ∃ M : Finset (Sym2 V),
      IsMatching B M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ C.supp) ∧ (21 / 20 : ℝ) * n ≤ (2 * M.card : ℝ)) := by
  classical
  have hsδ_le : Real.sqrt δ ≤ 1 / 200 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by linarith⟩
  obtain ⟨S, hScard, hSdeg⟩ := fact_simple_dense_subgraph_exact H hδ0 hdense
  have hN_pos : 0 < (Fintype.card V : ℝ) := by linarith
  let N : ℝ := (Fintype.card V : ℝ)
  let N' : ℝ := (S.card : ℝ)
  have hN'_ge : (178 / 100 : ℝ) * n ≤ N' := by
    have h1 : (199 / 200 : ℝ) * N ≤ N' := by nlinarith
    nlinarith
  have hmiss_S : ∀ v ∈ S, ((S \ H.neighborFinset v).card : ℝ) ≤ (1 / 50 : ℝ) * N' := by
    intro v hv
    have hdeg_v := hSdeg v hv
    have h1 : (S \ H.neighborFinset v).card + (H.neighborFinset v ∩ S).card = S.card := by
      rw [Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter S (H.neighborFinset v)
    have h1r : ((S \ H.neighborFinset v).card : ℝ) + ((H.neighborFinset v ∩ S).card : ℝ) = N' := by
      dsimp only [N']; exact_mod_cast h1
    have hN_le : N ≤ (200 / 199 : ℝ) * N' := by
      have : (199 / 200 : ℝ) * N ≤ N' := by nlinarith only [hScard, hsδ_le, hN_pos]
      linarith
    have hN'_le_N : N' ≤ N := by dsimp only [N', N]; exact_mod_cast card_le_univ S
    have h1_le : (1 : ℝ) ≤ (1 / 1000 : ℝ) * N' := by linarith
    change (1 - 2 * Real.sqrt δ) * N - 1 ≤ _ at hdeg_v
    have hdeg_num : (198 / 200 : ℝ) * N - 1 ≤ ((H.neighborFinset v ∩ S).card : ℝ) := by
      nlinarith only [hdeg_v, hsδ_le, hN_pos]
    linarith only [h1r, hdeg_num, hN'_le_N, hN_le, h1_le]
  have hbig_comp :
      (∃ C : R.ConnectedComponent, (47 / 50 : ℝ) * N' ≤ ((S.filter (fun v => R.connectedComponentMk v = C)).card : ℝ)) ∨
      (∃ C : B.ConnectedComponent, (47 / 50 : ℝ) * N' ≤ ((S.filter (fun v => B.connectedComponentMk v = C)).card : ℝ)) := by
    by_cases hRbig : ∃ C : R.ConnectedComponent,
        (47 / 50 : ℝ) * N' ≤ ((S.filter (fun v => R.connectedComponentMk v = C)).card : ℝ)
    · exact Or.inl hRbig
    · right
      push Not at hRbig
      have hex_A : ∃ A ⊆ S, (3 / 50 : ℝ) * N' < (A.card : ℝ) ∧ (A.card : ℝ) < (47 / 50 : ℝ) * N' ∧
          ∀ u ∈ A, ∀ v ∈ S \ A, ¬ R.Adj u v := by
        by_cases hmed : ∃ C : R.ConnectedComponent,
            (3 / 50 : ℝ) * N' < ((S.filter (fun v => R.connectedComponentMk v = C)).card : ℝ)
        · obtain ⟨C, hCgt⟩ := hmed
          refine ⟨S.filter (fun v => R.connectedComponentMk v = C), filter_subset _ _,
            hCgt, hRbig C, fun u hu v hv huv => ?_⟩
          have hCu : R.connectedComponentMk u = C := (mem_filter.mp hu).2
          have hCv : R.connectedComponentMk v = C :=
            (ConnectedComponent.eq.mpr (Adj.reachable huv)).symm.trans hCu
          exact (Finset.mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hCv⟩)
        · push Not at hmed
          let allC : Finset R.ConnectedComponent := S.image R.connectedComponentMk
          let unionOf : Finset R.ConnectedComponent → Finset V :=
            fun T => S.filter (fun v => R.connectedComponentMk v ∈ T)
          have hall_eq : unionOf allC = S := by
            ext v; simp only [unionOf, allC, mem_filter, mem_image]
            exact ⟨fun h => h.1, fun hv => ⟨hv, v, hv, rfl⟩⟩
          let bigT : Finset (Finset R.ConnectedComponent) :=
            allC.powerset.filter (fun T => (3 / 50 : ℝ) * N' < ((unionOf T).card : ℝ))
          have hbig_ne : bigT.Nonempty := by
            refine ⟨allC, mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩⟩
            rw [hall_eq]; linarith
          obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image bigT Finset.card hbig_ne
          have hTgt : (3 / 50 : ℝ) * N' < ((unionOf T).card : ℝ) := (mem_filter.mp hTmem).2
          have hTne : T.Nonempty := by
            by_contra hemp
            rw [not_nonempty_iff_eq_empty] at hemp
            rw [hemp] at hTgt
            have : (unionOf ∅).card = 0 := by simp [unionOf]
            rw [this] at hTgt; norm_num at hTgt; linarith
          obtain ⟨C0, hC0⟩ := hTne
          have hT_er_le : ((unionOf (T.erase C0)).card : ℝ) ≤ (3 / 50 : ℝ) * N' := by
            by_contra hgt
            push Not at hgt
            have hmem' : T.erase C0 ∈ bigT := mem_filter.mpr
              ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp (mem_filter.mp hTmem).1)), hgt⟩
            have := hTmin (T.erase C0) hmem'
            have := Finset.card_erase_lt_of_mem hC0
            omega
          have hcard_le : ((unionOf T).card : ℝ) ≤ (6 / 50 : ℝ) * N' := by
            have hsub : unionOf T ⊆ unionOf (T.erase C0) ∪ S.filter (fun v => R.connectedComponentMk v = C0) := by
              intro v hv
              have hv' := mem_filter.mp hv
              by_cases hEq : R.connectedComponentMk v = C0
              · exact mem_union_right _ (mem_filter.mpr ⟨hv'.1, hEq⟩)
              · exact mem_union_left _ (mem_filter.mpr ⟨hv'.1, mem_erase.mpr ⟨hEq, hv'.2⟩⟩)
            have hle := (card_le_card hsub).trans (card_union_le _ _)
            have hle_r : ((unionOf T).card : ℝ) ≤ ((unionOf (T.erase C0)).card : ℝ) +
                ((S.filter (fun v => R.connectedComponentMk v = C0)).card : ℝ) := by exact_mod_cast hle
            linarith [hmed C0]
          refine ⟨unionOf T, filter_subset _ _, hTgt, by linarith, fun u hu v hv huv => ?_⟩
          have hEq : R.connectedComponentMk v = R.connectedComponentMk u :=
            (ConnectedComponent.eq.mpr (Adj.reachable huv)).symm
          exact (Finset.mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,
            hEq ▸ (mem_filter.mp hu).2⟩)
      obtain ⟨A, hAS, hA_lo, hA_hi, hnoR⟩ := hex_A
      let A' := S \ A
      have hA'_lo : (3 / 50 : ℝ) * N' < (A'.card : ℝ) := by
        have h1 := card_sdiff_add_card_eq_card hAS
        have h1r : (A'.card : ℝ) + (A.card : ℝ) = N' := by dsimp only [A', N']; exact_mod_cast h1
        linarith
      have hA_ne : A.Nonempty := card_pos.mp (by
        have : (0 : ℝ) < (A.card : ℝ) := by linarith
        exact_mod_cast this)
      obtain ⟨a0, ha0⟩ := hA_ne
      refine ⟨B.connectedComponentMk a0, ?_⟩
      have hall_in : S.filter (fun v => B.connectedComponentMk v = B.connectedComponentMk a0) = S := by
        rw [Finset.filter_eq_self]
        intro v hv
        apply ConnectedComponent.eq.mpr
        by_cases hvA : v ∈ A
        ·
          have hne_c : (A' ∩ H.neighborFinset v ∩ H.neighborFinset a0).Nonempty := by
            have hsub : A' ⊆ (A' ∩ H.neighborFinset v ∩ H.neighborFinset a0) ∪
                (S \ H.neighborFinset v) ∪ (S \ H.neighborFinset a0) := by
              intro w hw
              have hwS : w ∈ S := (Finset.mem_sdiff.mp hw).1
              by_cases h1 : w ∈ H.neighborFinset v
              · by_cases h2 : w ∈ H.neighborFinset a0
                · exact mem_union_left _ (mem_union_left _
                    (mem_inter.mpr ⟨mem_inter.mpr ⟨hw, h1⟩, h2⟩))
                · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwS, h2⟩)
              · exact mem_union_left _ (mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwS, h1⟩))
            have hle := (card_le_card hsub).trans ((card_union_le _ _).trans
              (Nat.add_le_add_right (card_union_le _ _) _))
            have hle_r : (A'.card : ℝ) ≤ ((A' ∩ H.neighborFinset v ∩ H.neighborFinset a0).card : ℝ) +
                ((S \ H.neighborFinset v).card : ℝ) + ((S \ H.neighborFinset a0).card : ℝ) := by
              exact_mod_cast hle
            have hpos_r : (0 : ℝ) < ((A' ∩ H.neighborFinset v ∩ H.neighborFinset a0).card : ℝ) := by
              linarith [hmiss_S v hv, hmiss_S a0 (hAS ha0)]
            exact card_pos.mp (by exact_mod_cast hpos_r)
          obtain ⟨w, hw⟩ := hne_c
          simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hw
          have hBvw : B.Adj v w := (hcover v w hw.1.2).resolve_left (hnoR v hvA w hw.1.1)
          have hBa0w : B.Adj a0 w := (hcover a0 w hw.2).resolve_left (hnoR a0 ha0 w hw.1.1)
          exact hBvw.reachable.trans hBa0w.symm.reachable
        ·
          have hvA' : v ∈ A' := Finset.mem_sdiff.mpr ⟨hv, hvA⟩
          have hne_u : (A ∩ H.neighborFinset v).Nonempty := by
            have hsub : A ⊆ (A ∩ H.neighborFinset v) ∪ (S \ H.neighborFinset v) := fun u hu => by
              by_cases h1 : u ∈ H.neighborFinset v
              · exact mem_union_left _ (mem_inter.mpr ⟨hu, h1⟩)
              · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAS hu, h1⟩)
            have hle := (card_le_card hsub).trans (card_union_le _ _)
            have hle_r : (A.card : ℝ) ≤ ((A ∩ H.neighborFinset v).card : ℝ) +
                ((S \ H.neighborFinset v).card : ℝ) := by exact_mod_cast hle
            have hpos_r : (0 : ℝ) < ((A ∩ H.neighborFinset v).card : ℝ) := by
              linarith [hmiss_S v hv]
            exact card_pos.mp (by exact_mod_cast hpos_r)
          obtain ⟨u, hu⟩ := hne_u
          rw [mem_inter, SimpleGraph.mem_neighborFinset] at hu
          have hBvu : B.Adj v u := (hcover v u hu.2).resolve_left (fun h => hnoR u hu.1 v hvA' h.symm)
          have hne_c : (A' ∩ H.neighborFinset u ∩ H.neighborFinset a0).Nonempty := by
            have hsub : A' ⊆ (A' ∩ H.neighborFinset u ∩ H.neighborFinset a0) ∪
                (S \ H.neighborFinset u) ∪ (S \ H.neighborFinset a0) := fun w hw => by
              have hwS := (Finset.mem_sdiff.mp hw).1
              by_cases h1 : w ∈ H.neighborFinset u
              · by_cases h2 : w ∈ H.neighborFinset a0
                · exact mem_union_left _ (mem_union_left _
                    (mem_inter.mpr ⟨mem_inter.mpr ⟨hw, h1⟩, h2⟩))
                · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwS, h2⟩)
              · exact mem_union_left _ (mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwS, h1⟩))
            have hle := (card_le_card hsub).trans ((card_union_le _ _).trans
              (Nat.add_le_add_right (card_union_le _ _) _))
            have hle_r : (A'.card : ℝ) ≤ ((A' ∩ H.neighborFinset u ∩ H.neighborFinset a0).card : ℝ) +
                ((S \ H.neighborFinset u).card : ℝ) + ((S \ H.neighborFinset a0).card : ℝ) := by
              exact_mod_cast hle
            have hpos_r : (0 : ℝ) < ((A' ∩ H.neighborFinset u ∩ H.neighborFinset a0).card : ℝ) := by
              linarith [hmiss_S u (hAS hu.1), hmiss_S a0 (hAS ha0)]
            exact card_pos.mp (by exact_mod_cast hpos_r)
          obtain ⟨w, hw⟩ := hne_c
          simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hw
          have hBuw : B.Adj u w := (hcover u w hw.1.2).resolve_left (hnoR u hu.1 w hw.1.1)
          have hBa0w : B.Adj a0 w := (hcover a0 w hw.2).resolve_left (hnoR a0 ha0 w hw.1.1)
          exact hBvu.reachable.trans (hBuw.reachable.trans hBa0w.symm.reachable)
      rw [hall_in]; linarith
  have hbuild : ∀ (G1 G2 : SimpleGraph V) [DecidableRel G1.Adj] [DecidableRel G2.Adj],
      (∀ u v, H.Adj u v → G1.Adj u v ∨ G2.Adj u v) →
      (∃ C1 : G1.ConnectedComponent, (47 / 50 : ℝ) * N' ≤ ((S.filter (fun v => G1.connectedComponentMk v = C1)).card : ℝ)) →
      (∃ C : G1.ConnectedComponent, ∃ M : Finset (Sym2 V),
        IsMatching G1 M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ C.supp) ∧ (21 / 20 : ℝ) * n ≤ (2 * M.card : ℝ)) ∨
      (∃ C : G2.ConnectedComponent, ∃ M : Finset (Sym2 V),
        IsMatching G2 M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ C.supp) ∧ (21 / 20 : ℝ) * n ≤ (2 * M.card : ℝ)) := by
    intro G1 G2 _ _ hcov12 ⟨C1, hC1⟩
    let S1 : Finset V := S.filter (fun v => G1.connectedComponentMk v = C1)
    have hS1_card : (167 / 100 : ℝ) * n ≤ (S1.card : ℝ) := by
      have : (47 / 50 : ℝ) * ((178 / 100 : ℝ) * n) ≤ (S1.card : ℝ) := by nlinarith
      linarith
    let allM : Finset (Finset (Sym2 V)) :=
      G1.edgeFinset.powerset.filter (fun M => IsMatching G1 M ∧ ∀ e ∈ M, ∀ v ∈ e, v ∈ S1)
    have hallM_ne : allM.Nonempty := ⟨∅, mem_filter.mpr ⟨Finset.empty_mem_powerset _,
      ⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _)⟩,
      fun _ h => absurd h (notMem_empty _)⟩⟩
    obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_max_image allM Finset.card hallM_ne
    have hM_spec := (mem_filter.mp hM_mem).2
    have hM : IsMatching G1 M := hM_spec.1
    have hM_S1 : ∀ e ∈ M, ∀ v ∈ e, v ∈ S1 := hM_spec.2
    by_cases hM_big : (21 / 20 : ℝ) * n ≤ (2 * M.card : ℝ)
    · exact Or.inl ⟨C1, M, hM, fun e he v hv => (mem_filter.mp (hM_S1 e he v hv)).2, hM_big⟩
    · right
      push Not at hM_big
      let U : Finset V := S1.filter (fun v => ∃ e ∈ M, v ∈ e)
      let I : Finset V := S1 \ U
      have hU_card : U.card = 2 * M.card := by
        have hU_eq : U = M.biUnion Sym2.toFinset := by
          ext v; simp only [U, mem_filter, mem_biUnion, Sym2.mem_toFinset]
          exact ⟨fun h => h.2, fun ⟨e, he, hv⟩ => ⟨hM_S1 e he v hv, e, he, hv⟩⟩
        rw [hU_eq, card_biUnion]
        · calc ∑ e ∈ M, e.toFinset.card = ∑ _e ∈ M, 2 :=
                Finset.sum_congr rfl fun e he => Sym2.card_toFinset_of_not_isDiag e (G1.not_isDiag_of_mem_edgeSet (hM.1 e he))
            _ = 2 * M.card := by simp [mul_comm]
        · intro e₁ he₁ e₂ he₂ hne
          change Disjoint _ _; rw [Finset.disjoint_left]
          intro v hv1 hv2; exact hM.2 e₁ he₁ e₂ he₂ hne v ⟨Sym2.mem_toFinset.mp hv1, Sym2.mem_toFinset.mp hv2⟩
      have hI_card : (57 / 100 : ℝ) * n ≤ (I.card : ℝ) := by
        have h1 := card_sdiff_add_card_eq_card (filter_subset (fun v => ∃ e ∈ M, v ∈ e) S1)
        have h1r : (I.card : ℝ) + (U.card : ℝ) = (S1.card : ℝ) := by exact_mod_cast h1
        have hUr : (U.card : ℝ) = (2 * M.card : ℝ) := by exact_mod_cast hU_card
        linarith
      have hnoG1_I : ∀ u ∈ I, ∀ v ∈ I, ¬ G1.Adj u v := by
        intro u hu v hv huv
        have huU : u ∉ U := (Finset.mem_sdiff.mp hu).2
        have hvU : v ∉ U := (Finset.mem_sdiff.mp hv).2
        have huS1 : u ∈ S1 := (Finset.mem_sdiff.mp hu).1
        have hvS1 : v ∈ S1 := (Finset.mem_sdiff.mp hv).1
        have hnot : s(u, v) ∉ M := fun hm => huU (mem_filter.mpr ⟨huS1, s(u, v), hm, Sym2.mem_mk_left u v⟩)
        let M' := insert s(u, v) M
        have hM' : IsMatching G1 M' := by
          refine ⟨fun e he => by rcases mem_insert.mp he with rfl | heM; exact huv; exact hM.1 e heM,
            fun e₁ he₁ e₂ he₂ hne x ⟨hx1, hx2⟩ => ?_⟩
          rcases mem_insert.mp he₁ with rfl | he1M <;>
          rcases mem_insert.mp he₂ with rfl | he2M
          · exact hne rfl
          · rcases Sym2.mem_iff.mp hx1 with rfl | rfl
            · exact huU (mem_filter.mpr ⟨huS1, e₂, he2M, hx2⟩)
            · exact hvU (mem_filter.mpr ⟨hvS1, e₂, he2M, hx2⟩)
          · rcases Sym2.mem_iff.mp hx2 with rfl | rfl
            · exact huU (mem_filter.mpr ⟨huS1, e₁, he1M, hx1⟩)
            · exact hvU (mem_filter.mpr ⟨hvS1, e₁, he1M, hx1⟩)
          · exact hM.2 e₁ he1M e₂ he2M hne x ⟨hx1, hx2⟩
        have hM'_in : M' ∈ allM := mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (fun e he => mem_edgeFinset.mpr (hM'.1 e he)), hM', fun e he x hx => by
            rcases mem_insert.mp he with rfl | heM
            · rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
            · exact hM_S1 e heM x hx⟩
        have := hM_max M' hM'_in
        rw [Finset.card_insert_of_notMem hnot] at this
        omega
      let U1 : Finset V := U.filter (fun u => 2 ≤ (G1.neighborFinset u ∩ I).card)
      let U2 : Finset V := U \ U1
      have hU1_le : U1.card ≤ M.card := by
        have hU1_sub : U1 ⊆ M.biUnion (fun e => e.toFinset.filter (fun u => u ∈ U1)) := fun u hu => by
          obtain ⟨e, heM, hue⟩ := (mem_filter.mp (mem_filter.mp hu).1).2
          exact mem_biUnion.mpr ⟨e, heM, mem_filter.mpr ⟨Sym2.mem_toFinset.mpr hue, hu⟩⟩
        have h1 : U1.card ≤ ∑ e ∈ M, (e.toFinset.filter (fun u => u ∈ U1)).card :=
          (card_le_card hU1_sub).trans card_biUnion_le
        refine h1.trans ?_
        calc ∑ e ∈ M, (e.toFinset.filter (fun u => u ∈ U1)).card
            ≤ ∑ _e ∈ M, 1 := sum_le_sum fun e heM => ?_
          _ = M.card := by simp
        induction e using Sym2.ind with
        | _ u v =>
          rw [card_le_one]
          intro a ha b hb
          have ha' := mem_filter.mp ha
          have hb' := mem_filter.mp hb
          by_contra hab
          have hu1 : a ∈ U1 := ha'.2
          have hv1 : b ∈ U1 := hb'.2
          have heq_e : s(u, v) = s(a, b) := by
            rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp ha'.1) with rfl | rfl <;>
            rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hb'.1) with rfl | rfl
            · exact absurd rfl hab
            · rfl
            · exact Sym2.eq_swap
            · exact absurd rfl hab
          rw [heq_e] at heM
          have hNa : 2 ≤ (G1.neighborFinset a ∩ I).card := (mem_filter.mp hu1).2
          have hNb : 2 ≤ (G1.neighborFinset b ∩ I).card := (mem_filter.mp hv1).2
          obtain ⟨w1, hw1⟩ := card_pos.mp (by omega : 0 < (G1.neighborFinset a ∩ I).card)
          obtain ⟨w2, hw2⟩ := card_pos.mp (by
            have hle := Finset.card_erase_le (s := G1.neighborFinset b ∩ I) (a := w1)
            by_cases hm : w1 ∈ G1.neighborFinset b ∩ I
            · rw [card_erase_of_mem hm]; omega
            · rw [Finset.erase_eq_of_notMem hm]; omega : 0 < ((G1.neighborFinset b ∩ I).erase w1).card)
          have hw12 : w1 ≠ w2 := (Finset.ne_of_mem_erase hw2).symm
          have hw1' := mem_inter.mp hw1
          have hw2' := mem_inter.mp (Finset.mem_of_mem_erase hw2)
          have ha_adj : G1.Adj a w1 := (mem_neighborFinset G1 a w1).mp hw1'.1
          have hb_adj : G1.Adj b w2 := (mem_neighborFinset G1 b w2).mp hw2'.1
          have hw1U : w1 ∉ U := (Finset.mem_sdiff.mp hw1'.2).2
          have hw2U : w2 ∉ U := (Finset.mem_sdiff.mp hw2'.2).2
          let M' := insert s(a, w1) (insert s(b, w2) (M.erase s(a, b)))
          have hdisj_er : ∀ e' ∈ M.erase s(a, b), a ∉ e' ∧ b ∉ e' ∧ w1 ∉ e' ∧ w2 ∉ e' := by
            intro e' he'
            have he'M := Finset.mem_of_mem_erase he'
            have he'ne := Finset.ne_of_mem_erase he'
            exact ⟨fun h => hM.2 e' he'M s(a, b) heM he'ne a ⟨h, Sym2.mem_mk_left a b⟩,
              fun h => hM.2 e' he'M s(a, b) heM he'ne b ⟨h, Sym2.mem_mk_right a b⟩,
              fun h => hw1U (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw1'.2).1, e', he'M, h⟩),
              fun h => hw2U (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw2'.2).1, e', he'M, h⟩)⟩
          have haw_bw : ∀ z, ¬ (z ∈ s(a, w1) ∧ z ∈ s(b, w2)) := by
            intro z ⟨hz1, hz2⟩
            rcases Sym2.mem_iff.mp hz1 with h1' | h1' <;> rcases Sym2.mem_iff.mp hz2 with h2' | h2'
            · exact hab (h1'.symm.trans h2')
            · exact hw2U ((h2'.symm.trans h1') ▸ (mem_filter.mp hu1).1)
            · exact hw1U ((h1'.symm.trans h2') ▸ (mem_filter.mp hv1).1)
            · exact hw12 (h1'.symm.trans h2')
          have hM' : IsMatching G1 M' := by
            refine ⟨fun f hf => ?_, fun e₁ he₁ e₂ he₂ hne z ⟨hz1, hz2⟩ => ?_⟩
            · rcases mem_insert.mp hf with rfl | hf1
              · exact ha_adj
              · rcases mem_insert.mp hf1 with rfl | hf2
                · exact hb_adj
                · exact hM.1 f (Finset.mem_of_mem_erase hf2)
            · rcases mem_insert.mp he₁ with rfl | he1a
              · rcases mem_insert.mp he₂ with rfl | he2a
                · exact hne rfl
                · rcases mem_insert.mp he2a with rfl | he2b
                  · exact haw_bw z ⟨hz1, hz2⟩
                  · rcases Sym2.mem_iff.mp hz1 with rfl | rfl
                    · exact (hdisj_er e₂ he2b).1 hz2
                    · exact (hdisj_er e₂ he2b).2.2.1 hz2
              · rcases mem_insert.mp he1a with rfl | he1b
                · rcases mem_insert.mp he₂ with rfl | he2a
                  · exact haw_bw z ⟨hz2, hz1⟩
                  · rcases mem_insert.mp he2a with rfl | he2b
                    · exact hne rfl
                    · rcases Sym2.mem_iff.mp hz1 with rfl | rfl
                      · exact (hdisj_er e₂ he2b).2.1 hz2
                      · exact (hdisj_er e₂ he2b).2.2.2 hz2
                · rcases mem_insert.mp he₂ with rfl | he2a
                  · rcases Sym2.mem_iff.mp hz2 with rfl | rfl
                    · exact (hdisj_er e₁ he1b).1 hz1
                    · exact (hdisj_er e₁ he1b).2.2.1 hz1
                  · rcases mem_insert.mp he2a with rfl | he2b
                    · rcases Sym2.mem_iff.mp hz2 with rfl | rfl
                      · exact (hdisj_er e₁ he1b).2.1 hz1
                      · exact (hdisj_er e₁ he1b).2.2.2 hz1
                    · exact hM.2 e₁ (Finset.mem_of_mem_erase he1b) e₂ (Finset.mem_of_mem_erase he2b) hne z ⟨hz1, hz2⟩
          have hM'_in : M' ∈ allM := mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (fun f hf => mem_edgeFinset.mpr (hM'.1 f hf)), hM', fun f hf z hz => by
              rcases mem_insert.mp hf with rfl | hf1
              · rcases Sym2.mem_iff.mp hz with rfl | rfl
                · exact (mem_filter.mp (mem_filter.mp hu1).1).1
                · exact (Finset.mem_sdiff.mp hw1'.2).1
              · rcases mem_insert.mp hf1 with rfl | hf2
                · rcases Sym2.mem_iff.mp hz with rfl | rfl
                  · exact (mem_filter.mp (mem_filter.mp hv1).1).1
                  · exact (Finset.mem_sdiff.mp hw2'.2).1
                · exact hM_S1 f (Finset.mem_of_mem_erase hf2) z hz⟩
          have hnot1 : s(b, w2) ∉ M.erase s(a, b) := fun hm =>
            hw2U (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw2'.2).1, s(b, w2),
              Finset.mem_of_mem_erase hm, Sym2.mem_mk_right b w2⟩)
          have hnot2 : s(a, w1) ∉ insert s(b, w2) (M.erase s(a, b)) := fun hm => by
            rcases mem_insert.mp hm with heq | hm'
            · exact haw_bw a ⟨Sym2.mem_mk_left a w1, heq ▸ Sym2.mem_mk_left a w1⟩
            · exact hw1U (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw1'.2).1, s(a, w1),
                Finset.mem_of_mem_erase hm', Sym2.mem_mk_right a w1⟩)
          have hcard' : M'.card = M.card + 1 := by
            rw [Finset.card_insert_of_notMem hnot2, Finset.card_insert_of_notMem hnot1,
                card_erase_of_mem heM]
            have hpos := card_pos.mpr ⟨_, heM⟩; omega
          have := hM_max M' hM'_in
          omega
      have hG2_deg_I : ∀ x ∈ I ∪ U2, ((G2.neighborFinset x ∩ I).card : ℝ) ≥ (I.card : ℝ) - (1 / 50 : ℝ) * N' - 1 := by
        intro x hx
        have hxS : x ∈ S := by
          rcases mem_union.mp hx with hI | hU2
          · exact (mem_filter.mp (Finset.mem_sdiff.mp hI).1).1
          · exact (mem_filter.mp (mem_filter.mp (Finset.mem_sdiff.mp hU2).1).1).1
        have hG1_le1 : (G1.neighborFinset x ∩ I).card ≤ 1 := by
          rcases mem_union.mp hx with hI | hU2
          · rw [Nat.le_one_iff_eq_zero_or_eq_one]; left
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro y hy
            rw [mem_inter, mem_neighborFinset] at hy
            exact hnoG1_I x hI y hy.2 hy.1
          · have hnotU1 : x ∉ U1 := (Finset.mem_sdiff.mp hU2).2
            have : ¬ 2 ≤ (G1.neighborFinset x ∩ I).card := fun h =>
              hnotU1 (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hU2).1, h⟩)
            omega
        have hsub : I ⊆ (G2.neighborFinset x ∩ I) ∪ (G1.neighborFinset x ∩ I) ∪ (S \ H.neighborFinset x) := by
          intro y hy
          have hyS : y ∈ S := (mem_filter.mp (Finset.mem_sdiff.mp hy).1).1
          by_cases hH : H.Adj x y
          · rcases hcov12 x y hH with h1 | h2
            · exact mem_union_left _ (mem_union_right _
                (mem_inter.mpr ⟨(mem_neighborFinset G1 x y).mpr h1, hy⟩))
            · exact mem_union_left _ (mem_union_left _
                (mem_inter.mpr ⟨(mem_neighborFinset G2 x y).mpr h2, hy⟩))
          · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyS, fun hm => hH ((mem_neighborFinset H x y).mp hm)⟩)
        have hle := (card_le_card hsub).trans ((card_union_le _ _).trans
          (Nat.add_le_add_right (card_union_le _ _) _))
        have hle_r : (I.card : ℝ) ≤ ((G2.neighborFinset x ∩ I).card : ℝ) +
            ((G1.neighborFinset x ∩ I).card : ℝ) + ((S \ H.neighborFinset x).card : ℝ) := by exact_mod_cast hle
        have hG1_r : ((G1.neighborFinset x ∩ I).card : ℝ) ≤ 1 := by exact_mod_cast hG1_le1
        linarith [hmiss_S x hxS]
      have hN'_le_S1 : N' ≤ (50 / 47 : ℝ) * (S1.card : ℝ) := by linarith
      have hN'_le_2n : (1 / 50 : ℝ) * N' ≤ (1 / 40 : ℝ) * (S1.card : ℝ) := by linarith
      have hI_vs_N' : (32 / 100 : ℝ) * N' ≤ (I.card : ℝ) := by
        have h1 := card_sdiff_add_card_eq_card (filter_subset (fun v => ∃ e ∈ M, v ∈ e) S1)
        have h1r : (I.card : ℝ) + (U.card : ℝ) = (S1.card : ℝ) := by exact_mod_cast h1
        have hUr : (U.card : ℝ) = (2 * M.card : ℝ) := by exact_mod_cast hU_card
        have hn_le_N' : n ≤ (100 / 178 : ℝ) * N' := by linarith
        nlinarith
      have hI_ne : I.Nonempty := card_pos.mp (by
        have : (0 : ℝ) < (I.card : ℝ) := by linarith
        exact_mod_cast this)
      obtain ⟨w0, hw0⟩ := hI_ne
      let C2 : G2.ConnectedComponent := G2.connectedComponentMk w0
      have hall_in_C2 : ∀ x ∈ I ∪ U2, x ∈ C2.supp := by
        intro x hx
        show G2.connectedComponentMk x = G2.connectedComponentMk w0
        apply ConnectedComponent.eq.mpr
        have hdeg_x := hG2_deg_I x hx
        have hdeg_w0 := hG2_deg_I w0 (mem_union_left _ hw0)
        have hne_c : ((G2.neighborFinset x ∩ I) ∩ (G2.neighborFinset w0 ∩ I)).Nonempty := by
          have h1 := Finset.card_inter_add_card_union (G2.neighborFinset x ∩ I) (G2.neighborFinset w0 ∩ I)
          have h2 : ((G2.neighborFinset x ∩ I) ∪ (G2.neighborFinset w0 ∩ I)).card ≤ I.card :=
            card_le_card (union_subset inter_subset_right inter_subset_right)
          have h1r : (((G2.neighborFinset x ∩ I) ∩ (G2.neighborFinset w0 ∩ I)).card : ℝ) +
              (((G2.neighborFinset x ∩ I) ∪ (G2.neighborFinset w0 ∩ I)).card : ℝ) =
              ((G2.neighborFinset x ∩ I).card : ℝ) + ((G2.neighborFinset w0 ∩ I).card : ℝ) := by exact_mod_cast h1
          have h2r : (((G2.neighborFinset x ∩ I) ∪ (G2.neighborFinset w0 ∩ I)).card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast h2
          have hN'_big : (1000 : ℝ) ≤ N' := by linarith
          have hpos_r : (0 : ℝ) < (((G2.neighborFinset x ∩ I) ∩ (G2.neighborFinset w0 ∩ I)).card : ℝ) := by linarith
          exact card_pos.mp (by exact_mod_cast hpos_r)
        obtain ⟨z, hz⟩ := hne_c
        simp only [mem_inter, mem_neighborFinset] at hz
        exact hz.1.1.reachable.trans hz.2.1.symm.reachable
      let b : ℕ := Nat.floor ((1 / 50 : ℝ) * N') + 2
      have hb_le : (b : ℝ) ≤ (1 / 50 : ℝ) * N' + 2 := by
        dsimp only [b]; push_cast; linarith [Nat.floor_le (show 0 ≤ (1 / 50 : ℝ) * N' by linarith)]
      have hdeg_nat : ∀ x ∈ I ∪ U2, I.card - b < (G2.neighborFinset x ∩ I).card := by
        intro x hx
        have hd := hG2_deg_I x hx
        have hfl : (1 / 50 : ℝ) * N' < (Nat.floor ((1 / 50 : ℝ) * N') : ℝ) + 1 := Nat.lt_floor_add_one _
        have hbr : (1 / 50 : ℝ) * N' + 1 < (b : ℝ) := by dsimp only [b]; push_cast; linarith
        by_cases hIb : b ≤ I.card
        · have hsub_r : ((I.card - b : ℕ) : ℝ) = (I.card : ℝ) - (b : ℝ) := Nat.cast_sub hIb
          have hlt_r : ((I.card - b : ℕ) : ℝ) < ((G2.neighborFinset x ∩ I).card : ℝ) := by linarith
          exact_mod_cast hlt_r
        · have h0 : I.card - b = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hIb)
          rw [h0]
          have hpos_r : (0 : ℝ) < ((G2.neighborFinset x ∩ I).card : ℝ) := by
            have hN'big : (1000 : ℝ) ≤ N' := by linarith
            linarith
          exact_mod_cast hpos_r
      have hphase1 : ∀ (T : Finset V), T ⊆ U2 → T.card ≤ I.card - b →
          ∃ M1 : Finset (Sym2 V), IsMatching G2 M1 ∧ M1.card = T.card ∧
            (∀ e ∈ M1, ∀ v ∈ e, v ∈ T ∪ I) ∧
            (I.filter (fun w => ∃ e ∈ M1, w ∈ e)).card = T.card := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          intro _ _
          exact ⟨∅, ⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _)⟩,
            by simp, fun _ h => absurd h (notMem_empty _), by simp⟩
        | insert u T huT ih =>
          intro hsub hcard
          have hTsub : T ⊆ U2 := (Finset.subset_insert u T).trans hsub
          have huU2 : u ∈ U2 := hsub (Finset.mem_insert_self u T)
          have hcard' : T.card + 1 ≤ I.card - b := by rwa [Finset.card_insert_of_notMem huT] at hcard
          obtain ⟨M1, hM1, hM1_card, hM1_supp, hM1_I⟩ := ih hTsub (by omega)
          let usedI := I.filter (fun w => ∃ e ∈ M1, w ∈ e)
          have hcand : ((G2.neighborFinset u ∩ I) \ usedI).Nonempty := by
            rw [nonempty_iff_ne_empty]
            intro hemp
            have hle := card_le_card (sdiff_eq_empty_iff_subset.mp hemp)
            have hlt := hdeg_nat u (mem_union_right _ huU2)
            have hused_c : usedI.card = T.card := hM1_I
            omega
          obtain ⟨w, hw⟩ := hcand
          rw [Finset.mem_sdiff, mem_inter, mem_neighborFinset] at hw
          have hu_notI : u ∉ I := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp huU2).1
          have hw_notU2 : w ∉ U2 := fun h => (Finset.mem_sdiff.mp hw.1.2).2 (Finset.mem_sdiff.mp h).1
          have hu_notM1 : ∀ e ∈ M1, u ∉ e := fun e he hue => by
            rcases mem_union.mp (hM1_supp e he u hue) with h1 | h2
            · exact huT h1
            · exact hu_notI h2
          have hw_notM1 : ∀ e ∈ M1, w ∉ e := fun e he hwe =>
            hw.2 (mem_filter.mpr ⟨hw.1.2, e, he, hwe⟩)
          have hnot_in : s(u, w) ∉ M1 := fun hm => hu_notM1 s(u, w) hm (Sym2.mem_mk_left u w)
          refine ⟨insert s(u, w) M1, ?_, ?_, ?_, ?_⟩
          · refine ⟨fun e he => by rcases mem_insert.mp he with rfl | he1; exact hw.1.1; exact hM1.1 e he1,
              fun e₁ he₁ e₂ he₂ hne x ⟨hx1, hx2⟩ => ?_⟩
            rcases mem_insert.mp he₁ with rfl | h1 <;>
            rcases mem_insert.mp he₂ with rfl | h2
            · exact hne rfl
            · rcases Sym2.mem_iff.mp hx1 with rfl | rfl
              · exact hu_notM1 e₂ h2 hx2
              · exact hw_notM1 e₂ h2 hx2
            · rcases Sym2.mem_iff.mp hx2 with rfl | rfl
              · exact hu_notM1 e₁ h1 hx1
              · exact hw_notM1 e₁ h1 hx1
            · exact hM1.2 e₁ h1 e₂ h2 hne x ⟨hx1, hx2⟩
          · rw [Finset.card_insert_of_notMem hnot_in, Finset.card_insert_of_notMem huT, hM1_card]
          · intro e he x hx
            rcases mem_insert.mp he with rfl | he1
            · rcases Sym2.mem_iff.mp hx with hx' | hx'
              · rw [hx']; exact mem_union_left _ (Finset.mem_insert_self u T)
              · rw [hx']; exact mem_union_right _ hw.1.2
            · rcases mem_union.mp (hM1_supp e he1 x hx) with h1 | h2
              · exact mem_union_left _ (Finset.mem_insert_of_mem h1)
              · exact mem_union_right _ h2
          · have heq_used : I.filter (fun y => ∃ e ∈ insert s(u, w) M1, y ∈ e) = insert w usedI := by
              ext y
              simp only [usedI, mem_filter, mem_insert]
              constructor
              · rintro ⟨hyI, e, rfl | he1, hye⟩
                · rcases Sym2.mem_iff.mp hye with hyu | hyw
                  · rw [hyu] at hyI; exact absurd hyI hu_notI
                  · exact Or.inl hyw
                · exact Or.inr ⟨hyI, e, he1, hye⟩
              · rintro (hyw | ⟨hyI, e, he1, hye⟩)
                · rw [hyw]; exact ⟨hw.1.2, s(u, w), Or.inl rfl, Sym2.mem_mk_right u w⟩
                · exact ⟨hyI, e, Or.inr he1, hye⟩
            rw [heq_used, Finset.card_insert_of_notMem hw.2, hM1_I, Finset.card_insert_of_notMem huT]
      by_cases hcaseA : I.card - b ≤ U2.card
      · obtain ⟨T, hTU2, hTcard⟩ := exists_subset_card_eq hcaseA
        obtain ⟨M1, hM1, hM1_card, hM1_supp, _⟩ := hphase1 T hTU2 hTcard.le
        refine ⟨C2, M1, hM1, fun e he v hv => hall_in_C2 v ?_, ?_⟩
        · rcases mem_union.mp (hM1_supp e he v hv) with hT | hI
          · exact mem_union_right _ (hTU2 hT)
          · exact mem_union_left _ hI
        · rw [hM1_card, hTcard]
          have hb_lt_I : b ≤ I.card := by
            have hN'big : (1000 : ℝ) ≤ N' := by linarith
            have : (b : ℝ) ≤ (I.card : ℝ) := by linarith
            exact_mod_cast this
          have hsub_r : ((I.card - b : ℕ) : ℝ) = (I.card : ℝ) - (b : ℝ) := Nat.cast_sub hb_lt_I
          rw [hsub_r]
          have hI_lo : (47 / 50 : ℝ) * N' - (21 / 20 : ℝ) * n ≤ (I.card : ℝ) := by
            have h1 := card_sdiff_add_card_eq_card (filter_subset (fun v => ∃ e ∈ M, v ∈ e) S1)
            have h1r : (I.card : ℝ) + (U.card : ℝ) = (S1.card : ℝ) := by exact_mod_cast h1
            have hUr : (U.card : ℝ) = (2 * M.card : ℝ) := by exact_mod_cast hU_card
            linarith
          linarith
      ·
        have hU2_le : U2.card ≤ I.card - b := le_of_not_ge hcaseA
        obtain ⟨M1, hM1, hM1_card, hM1_supp, hM1_I⟩ := hphase1 U2 (Finset.Subset.refl _) hU2_le
        let usedI : Finset V := I.filter (fun w => ∃ e ∈ M1, w ∈ e)
        let I' : Finset V := I \ usedI
        have hI'_card : I'.card + U2.card = I.card := by
          have := card_sdiff_add_card_eq_card (filter_subset (fun w => ∃ e ∈ M1, w ∈ e) I)
          rwa [hM1_I] at this
        have hdeg_J : ∀ (J : Finset V), J ⊆ I → b < J.card → ∀ x ∈ J, J.card - b < (G2.neighborFinset x ∩ J).card := by
          intro J hJI hJb x hxJ
          have hxI : x ∈ I := hJI hxJ
          have hsub : G2.neighborFinset x ∩ I ⊆ (G2.neighborFinset x ∩ J) ∪ (I \ J) := fun y hy => by
            by_cases hyJ : y ∈ J
            · exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hy).1, hyJ⟩)
            · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨(mem_inter.mp hy).2, hyJ⟩)
          have hle := (card_le_card hsub).trans (card_union_le _ _)
          have hJIc := card_sdiff_add_card_eq_card hJI
          have hlt := hdeg_nat x (mem_union_left _ hxI)
          omega
        have hphase2 : ∀ (J : Finset V), J ⊆ I →
            ∃ M2 : Finset (Sym2 V), IsMatching G2 M2 ∧
              (∀ e ∈ M2, ∀ v ∈ e, v ∈ J) ∧ J.card ≤ 2 * M2.card + b := by
          intro J
          induction J using Finset.strongInduction with
          | H J ih =>
            intro hJI
            by_cases hsmall : J.card ≤ b
            · exact ⟨∅, ⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _)⟩,
                fun _ h => absurd h (notMem_empty _), by omega⟩
            · obtain ⟨x, hxJ⟩ := card_pos.mp (by omega : 0 < J.card)
              have hdegx := hdeg_J J hJI (by omega) x hxJ
              obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < (G2.neighborFinset x ∩ J).card)
              rw [mem_inter, mem_neighborFinset] at hy
              have hxy : x ≠ y := G2.ne_of_adj hy.1
              let J' := (J.erase x).erase y
              have hJ'_ssub : J' ⊂ J := by
                have hy_er : y ∈ J.erase x := mem_erase.mpr ⟨hxy.symm, hy.2⟩
                exact (Finset.erase_ssubset hy_er).trans (Finset.erase_ssubset hxJ)
              have hJ'_card : J'.card + 2 = J.card := by
                have hy_er : y ∈ J.erase x := mem_erase.mpr ⟨hxy.symm, hy.2⟩
                rw [card_erase_of_mem hy_er, card_erase_of_mem hxJ]
                have h2 : 2 ≤ J.card := by
                  have hpair : ({x, y} : Finset V) ⊆ J := by
                    intro z hz; rcases mem_insert.mp hz with rfl | hz'
                    · exact hxJ
                    · rw [mem_singleton] at hz'; exact hz' ▸ hy.2
                  simpa [card_pair hxy] using card_le_card hpair
                omega
              obtain ⟨M2, hM2, hM2_supp, hM2_card⟩ := ih J' hJ'_ssub (hJ'_ssub.subset.trans hJI)
              have hx_notJ' : x ∉ J' := fun h => (mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
              have hy_notJ' : y ∉ J' := fun h => (mem_erase.mp h).1 rfl
              have hnot_in : s(x, y) ∉ M2 := fun hm => hx_notJ' (hM2_supp s(x, y) hm x (Sym2.mem_mk_left x y))
              refine ⟨insert s(x, y) M2, ?_, ?_, ?_⟩
              · refine ⟨fun e he => by rcases mem_insert.mp he with rfl | he2; exact hy.1; exact hM2.1 e he2,
                  fun e₁ he₁ e₂ he₂ hne z ⟨hz1, hz2⟩ => ?_⟩
                rcases mem_insert.mp he₁ with rfl | h1 <;>
                rcases mem_insert.mp he₂ with rfl | h2
                · exact hne rfl
                · rcases Sym2.mem_iff.mp hz1 with rfl | rfl
                  · exact hx_notJ' (hM2_supp e₂ h2 z hz2)
                  · exact hy_notJ' (hM2_supp e₂ h2 z hz2)
                · rcases Sym2.mem_iff.mp hz2 with rfl | rfl
                  · exact hx_notJ' (hM2_supp e₁ h1 z hz1)
                  · exact hy_notJ' (hM2_supp e₁ h1 z hz1)
                · exact hM2.2 e₁ h1 e₂ h2 hne z ⟨hz1, hz2⟩
              · intro e he z hz
                rcases mem_insert.mp he with rfl | he2
                · rcases Sym2.mem_iff.mp hz with rfl | rfl
                  · exact hxJ
                  · exact hy.2
                · exact hJ'_ssub.subset (hM2_supp e he2 z hz)
              · rw [Finset.card_insert_of_notMem hnot_in]; omega
        obtain ⟨M2, hM2, hM2_supp, hM2_card⟩ := hphase2 I' sdiff_subset
        have hM12_vdisj : ∀ e₁ ∈ M1, ∀ e₂ ∈ M2, ∀ z, ¬ (z ∈ e₁ ∧ z ∈ e₂) := by
          intro e₁ he₁ e₂ he₂ z ⟨hz1, hz2⟩
          have hzI' : z ∈ I' := hM2_supp e₂ he₂ z hz2
          exact (Finset.mem_sdiff.mp hzI').2 (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzI').1, e₁, he₁, hz1⟩)
        have hM12_disj : Disjoint M1 M2 := by
          rw [Finset.disjoint_left]
          intro e he1 he2
          induction e using Sym2.ind with
          | _ a b => exact hM12_vdisj _ he1 _ he2 a ⟨Sym2.mem_mk_left a b, Sym2.mem_mk_left a b⟩
        refine ⟨C2, M1 ∪ M2, ?_, ?_, ?_⟩
        · refine ⟨fun e he => by rcases mem_union.mp he with h1 | h2; exact hM1.1 e h1; exact hM2.1 e h2,
            fun e₁ he₁ e₂ he₂ hne z ⟨hz1, hz2⟩ => ?_⟩
          rcases mem_union.mp he₁ with h1 | h1 <;>
          rcases mem_union.mp he₂ with h2 | h2
          · exact hM1.2 e₁ h1 e₂ h2 hne z ⟨hz1, hz2⟩
          · exact hM12_vdisj e₁ h1 e₂ h2 z ⟨hz1, hz2⟩
          · exact hM12_vdisj e₂ h2 e₁ h1 z ⟨hz2, hz1⟩
          · exact hM2.2 e₁ h1 e₂ h2 hne z ⟨hz1, hz2⟩
        · intro e he z hz
          rcases mem_union.mp he with h1 | h2
          · rcases mem_union.mp (hM1_supp e h1 z hz) with hU | hI
            · exact hall_in_C2 z (mem_union_right _ hU)
            · exact hall_in_C2 z (mem_union_left _ hI)
          · exact hall_in_C2 z (mem_union_left _ (Finset.mem_sdiff.mp (hM2_supp e h2 z hz)).1)
        ·
          rw [card_union_of_disjoint hM12_disj, hM1_card]
          have hS1_eq : I.card + U2.card + U1.card = S1.card := by
            have h1 := card_sdiff_add_card_eq_card (filter_subset (fun v => ∃ e ∈ M, v ∈ e) S1)
            have h2 := card_sdiff_add_card_eq_card (filter_subset (fun u => 2 ≤ (G1.neighborFinset u ∩ I).card) U)
            change I.card + U.card = S1.card at h1
            change U2.card + U1.card = U.card at h2
            omega
          have hnat : S1.card ≤ 2 * (U2.card + M2.card) + U1.card + b := by omega
          have hr : (S1.card : ℝ) ≤ (2 * (U2.card + M2.card) : ℝ) + (U1.card : ℝ) + (b : ℝ) := by exact_mod_cast hnat
          have hU1r : (U1.card : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast hU1_le
          have h2Mr : (2 * (U2.card + M2.card) : ℝ) = 2 * ((U2.card + M2.card : ℕ) : ℝ) := by push_cast; ring
          rw [← h2Mr]
          linarith
  rcases hbig_comp with hR | hB
  · exact hbuild R B hcover hR
  · rcases hbuild B R (fun u v h => (hcover u v h).symm) hB with h1 | h2
    · exact Or.inr h1
    · exact Or.inl h2
lemma card_top_edgeFinset {W : Type*} [Fintype W] [DecidableEq W] :
    (⊤ : SimpleGraph W).edgeFinset.card = Fintype.card W * (Fintype.card W - 1) / 2 := by
  classical
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (⊤ : SimpleGraph W)
  have hdeg : ∀ w : W, (⊤ : SimpleGraph W).degree w = Fintype.card W - 1 := by
    intro w; rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (⊤ : SimpleGraph W).neighborFinset w = Finset.univ.erase w := by ext u; simp [ne_comm]
    rw [this, card_erase_of_mem (mem_univ w), card_univ]
  simp only [hdeg, sum_const, card_univ, smul_eq_mul] at hsum
  omega
set_option maxHeartbeats 800000 in
lemma theorem_red {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε0 : 0 < ε) (hε_small : ε ≤ 1 / 10) :
    ∃ δ1 : ℝ, 0 < δ1 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (col : Fin k → SimpleGraph V) [∀ i, DecidableRel (col i).Adj],
        (∀ u v, G.Adj u v → ∃ i, (col i).Adj u v) →
        (∀ i u v, (col i).Adj u v → G.Adj u v) →
        ∀ (P : ProfilePartition G col) (δ n : ℝ),
          0 < δ → δ ≤ δ1 → max 1000 (2 / δ) ≤ n →
          (Fintype.card V : ℝ) = (2 : ℝ) ^ (k - 1) * n →
          (1 - δ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2) ≤ G.edgeFinset.card →
          (∀ i : Fin k, NoLargeOddConnMatching (col i) ((1 + δ) * n)) →
          ∃ xStar : Subcube k → ℝ, InOStar xStar ∧
            l1Dist (fun τ => (P.vec τ : ℝ) / n) xStar < ε := by
  classical
  obtain ⟨γ, hγpos, hclose⟩ := stability_close1 (k := k) (by omega) hε0
  let C : ℝ := (2 : ℝ) ^ (k - 1)
  have hC_gt1 : 1 < C := by
    have : 2 ≤ 2 ^ (k - 1) := Nat.le_self_pow (by omega) 2
    have : (2 : ℝ) ≤ C := by dsimp only [C]; exact_mod_cast this
    linarith
  let δ0 : ℝ := min (1 / 40000) (min (γ / (3 * (k : ℝ) * C ^ 2 + 1)) ((γ / (2 * C + 1)) ^ 2))
  have hδ0_pos : 0 < δ0 := by
    dsimp only [δ0]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  let δ1 : ℝ := min δ0 (1 / (40000 * (2 * C ^ 2)))
  have hδ1_pos : 0 < δ1 := lt_min hδ0_pos (by positivity)
  refine ⟨δ1, hδ1_pos, ?_⟩
  intro V _ _ G _ col _ hcover hsub P δ n hδpos hδle hnle hN hdense hnomatch
  have hδ_le_δ0 : δ ≤ δ0 := hδle.trans (min_le_left _ _)
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt (hδ_le_δ0.trans (min_le_left _ _)) (by norm_num)
  have hn_ge1000 : 1000 ≤ n := (le_max_left _ _).trans hnle
  have hn_gt : 1 / δ < n := lt_of_lt_of_le (by rw [div_lt_div_iff_of_pos_right hδpos]; norm_num)
    ((le_max_right _ _).trans hnle)
  have hn_pos : 0 < n := by linarith
  obtain ⟨hc1, hc2, hc3⟩ := profile_constraints (by omega) G col hcover hsub P hC_gt1 hδpos hδ_lt1 hn_gt hN hdense hnomatch
  let v : Subcube k → ℝ := fun τ => (P.vec τ : ℝ) / n
  have h3kC : 3 * δ * (k : ℝ) * C ^ 2 ≤ γ := by
    have h1 : δ ≤ γ / (3 * (k : ℝ) * C ^ 2 + 1) :=
      (hδ_le_δ0.trans (min_le_right _ _)).trans (min_le_left _ _)
    have h2 : δ * (3 * (k : ℝ) * C ^ 2 + 1) ≤ γ := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  have h2sC : 2 * Real.sqrt δ * C ≤ γ := by
    have h1 : δ ≤ (γ / (2 * C + 1)) ^ 2 :=
      (hδ_le_δ0.trans (min_le_right _ _)).trans (min_le_right _ _)
    have h2 : Real.sqrt δ ≤ γ / (2 * C + 1) :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, h1⟩
    have h3 : Real.sqrt δ * (2 * C + 1) ≤ γ := (le_div_iff₀ (by positivity)).mp h2
    nlinarith [Real.sqrt_nonneg δ]
  have h2C2 : 2 * δ * C ^ 2 ≤ γ := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith
  have hv_in : InX γ v := by
    refine ⟨fun τ => by dsimp only [v]; positivity, hc1.trans h3kC,
      fun τ h1 => (hc2 τ h1).trans (by linarith), fun σ τ hnc => (hc3 σ τ hnc).trans h2C2⟩
  have hv_sum : l1Sum v = (2 : ℝ) ^ (k - 1) := by
    unfold l1Sum
    dsimp only [v]
    rw [← sum_div]
    have htot : (∑ τ : Subcube k, (P.vec τ : ℝ)) = (2 : ℝ) ^ (k - 1) * n := by
      rw [← hN]; exact_mod_cast P.sum_vec
    rw [htot, mul_div_cancel_right₀ _ hn_pos.ne']
  obtain ⟨xStar, hxO, hdist⟩ := hclose v hv_in hv_sum
  obtain ⟨D, hdec, hDval, hout⟩ := hxO
  refine ⟨xStar, ⟨D, hdec, fun τ hτ => ?_, hout⟩, hdist⟩
  rcases hDval τ hτ with h1 | ⟨hw2, hx2⟩
  · exact h1
  ·
    exfalso
    have hdiff : |v τ - xStar τ| < ε :=
      lt_of_le_of_lt (single_le_sum (f := fun σ => |v σ - xStar σ|) (fun _ _ => abs_nonneg _) (mem_univ τ)) hdist
    rw [hx2, abs_lt] at hdiff
    have hvτ_ge : (18 / 10 : ℝ) ≤ v τ := by linarith
    have hVτ_card : (18 / 10 : ℝ) * n ≤ (P.vec τ : ℝ) := by
      dsimp only [v] at hvτ_ge
      rwa [le_div_iff₀ hn_pos] at hvτ_ge
    let Wτ := Finset.univ.filter (fun i : Fin k => τ i = 2)
    have hWτ_card : Wτ.card = 2 := hw2
    obtain ⟨i1, hi1⟩ := card_pos.mp (by omega : 0 < Wτ.card)
    obtain ⟨i2, hi2⟩ := card_pos.mp (by rw [card_erase_of_mem hi1]; omega : 0 < (Wτ.erase i1).card)
    have hi12 : i1 ≠ i2 := (Finset.ne_of_mem_erase hi2).symm
    have hτi1 : τ i1 = 2 := (mem_filter.mp hi1).2
    have hτi2 : τ i2 = 2 := (mem_filter.mp (Finset.mem_of_mem_erase hi2)).2
    have hWτ_eq : Wτ = {i1, i2} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi'
        · exact hi1
        · rw [mem_singleton] at hi'; exact hi' ▸ Finset.mem_of_mem_erase hi2
      · rw [card_pair hi12, hWτ_card]
    let Vτ := {u : V // P.assign u = τ}
    let Hτ : SimpleGraph Vτ := G.induce {u : V | P.assign u = τ}
    let Rτ : SimpleGraph Vτ := (col i1).induce {u : V | P.assign u = τ}
    let Bτ : SimpleGraph Vτ := (col i2).induce {u : V | P.assign u = τ}
    have hcovτ : ∀ u v : Vτ, Hτ.Adj u v → Rτ.Adj u v ∨ Bτ.Adj u v := by
      intro u v huv
      obtain ⟨i, hi⟩ := hcover u.val v.val huv
      have hiW : i ∈ Wτ := by
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        by_contra hne2
        have hbip := P.bipartite_edge i u.val v.val hi (by rw [u.property]; exact hne2)
        rw [u.property, v.property] at hbip
        rcases hbip with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> (rw [h0] at h1; exact absurd h1 (by decide))
      rw [hWτ_eq, mem_insert, mem_singleton] at hiW
      rcases hiW with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
    have hcard_Vτ : Fintype.card Vτ = P.vec τ := by
      simp [Vτ, ProfilePartition.vec, Fintype.card_subtype]
    have hVτ_ge : (18 / 10 : ℝ) * n ≤ (Fintype.card Vτ : ℝ) := by
      rw [hcard_Vτ]; exact hVτ_card
    have hHτ_dense : (1 - (1 / 40000 : ℝ)) * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1) / 2) ≤
        (Hτ.edgeFinset.card : ℝ) := by
      let nonH : Finset (Sym2 Vτ) := (⊤ : SimpleGraph Vτ).edgeFinset \ Hτ.edgeFinset
      let nonG : Finset (Sym2 V) := (⊤ : SimpleGraph V).edgeFinset \ G.edgeFinset
      have hnonH_le : nonH.card ≤ nonG.card := by
        have hsub_img : nonH.image (Sym2.map Subtype.val) ⊆ nonG := by
          intro e he
          rcases mem_image.mp he with ⟨e0, he0, rfl⟩
          induction e0 using Sym2.ind with
          | _ a b =>
            rw [Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset] at he0 ⊢
            exact ⟨Subtype.val_injective.ne he0.1, he0.2⟩
        rw [← card_image_of_injective nonH (Sym2.map.injective Subtype.val_injective)]
        exact card_le_card hsub_img
      have hcast_half : ∀ m : ℕ, ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
        intro m
        by_cases hm : m = 0
        · simp [hm]
        · have hdiv := Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))
          have h1 : (2 : ℝ) * ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
            rw [← Nat.cast_ofNat, ← Nat.cast_mul, hdiv, Nat.cast_mul,
                Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm), Nat.cast_one]
          linarith
      have hnonG_eq : (nonG.card : ℝ) + (G.edgeFinset.card : ℝ) =
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
        have h1 := card_sdiff_add_card_eq_card (s := G.edgeFinset) (t := (⊤ : SimpleGraph V).edgeFinset)
          (fun e he => mem_edgeFinset.mpr (by induction e using Sym2.ind with | _ a b => exact G.ne_of_adj (mem_edgeFinset.mp he)))
        rw [card_top_edgeFinset] at h1
        have h1r : (nonG.card : ℝ) + (G.edgeFinset.card : ℝ) =
            ((Fintype.card V * (Fintype.card V - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
        rwa [hcast_half] at h1r
      have hnonH_eq : (nonH.card : ℝ) + (Hτ.edgeFinset.card : ℝ) =
          (Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1) / 2 := by
        have h1 := card_sdiff_add_card_eq_card (s := Hτ.edgeFinset) (t := (⊤ : SimpleGraph Vτ).edgeFinset)
          (fun e he => mem_edgeFinset.mpr (by induction e using Sym2.ind with | _ a b => exact Hτ.ne_of_adj (mem_edgeFinset.mp he)))
        rw [card_top_edgeFinset] at h1
        have h1r : (nonH.card : ℝ) + (Hτ.edgeFinset.card : ℝ) =
            ((Fintype.card Vτ * (Fintype.card Vτ - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
        rwa [hcast_half] at h1r
      have hnonH_ub : (nonH.card : ℝ) ≤ δ * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2) := by
        have h1 : (nonH.card : ℝ) ≤ (nonG.card : ℝ) := by exact_mod_cast hnonH_le
        linarith only [h1, hnonG_eq, hdense]
      have hδ_tiny : δ * (2 * C ^ 2) ≤ 1 / 40000 := by
        have h1 : δ ≤ 1 / (40000 * (2 * C ^ 2)) := hδle.trans (min_le_right _ _)
        have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 40000 * (2 * C ^ 2))).mp h1
        linarith only [h2]
      have hratio : (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) ≤
          (2 * C ^ 2) * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1)) := by
        have h1 : (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) ≤ C ^ 2 * n ^ 2 := by
          have hVeq : (Fintype.card V : ℝ) = C * n := hN
          have hC0 : 0 ≤ C := by linarith only [hC_gt1]
          nlinarith only [hVeq, hC0, hn_pos]
        have h2 : n ^ 2 ≤ 2 * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1)) := by
          nlinarith only [hVτ_ge, hn_ge1000]
        nlinarith only [h1, h2, sq_nonneg C]
      have hnonH_final : (nonH.card : ℝ) ≤ (1 / 40000 : ℝ) * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1) / 2) := by
        calc (nonH.card : ℝ) ≤ δ * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2) := hnonH_ub
          _ ≤ δ * ((2 * C ^ 2) * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1)) / 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hratio (by norm_num)) hδpos.le
          _ = (δ * (2 * C ^ 2)) * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1) / 2) := by ring
          _ ≤ (1 / 40000 : ℝ) * ((Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1) / 2) := by
            have hnn : 0 ≤ (Fintype.card Vτ : ℝ) * ((Fintype.card Vτ : ℝ) - 1) / 2 := by
              nlinarith only [hVτ_ge, hn_ge1000]
            exact mul_le_mul_of_nonneg_right hδ_tiny hnn
      linarith only [hnonH_eq, hnonH_final]
    have h2cm := two_colour_connected_matching Hτ Rτ Bτ hcovτ
      (fun u v h => hsub i1 u.val v.val h) (fun u v h => hsub i2 u.val v.val h)
      (by norm_num : (0 : ℝ) < 1 / 40000) (le_refl _) hn_ge1000 hVτ_ge hHτ_dense
    have hlift : ∀ (j : Fin k) (hj2 : τ j = 2),
        ∀ (C0 : ((col j).induce {u : V | P.assign u = τ}).ConnectedComponent)
          (M : Finset (Sym2 Vτ)),
          IsMatching ((col j).induce {u : V | P.assign u = τ}) M →
          (∀ e ∈ M, ∀ v ∈ e, v ∈ C0.supp) →
          (21 / 20 : ℝ) * n ≤ (2 * M.card : ℝ) → False := by
      intro j hj2 C0 M hM hMC0 hMbig
      have hMne : M.Nonempty := card_pos.mp (by
        have : (0 : ℝ) < (M.card : ℝ) := by linarith
        exact_mod_cast this)
      obtain ⟨e0, he0⟩ := hMne
      induction e0 using Sym2.ind with
      | _ u0 _ =>
        have hu0C0 : u0 ∈ C0.supp := hMC0 _ he0 u0 (Sym2.mem_mk_left u0 _)
        let Cbig : (col j).ConnectedComponent := (col j).connectedComponentMk u0.val
        have hCbig_nb : ¬ IsBipartiteComponent (col j) Cbig.supp :=
          (P.nonbipartite_comp j u0.val).mp (by rw [u0.property]; exact hj2)
        let M' : Finset (Sym2 V) := M.image (Sym2.map Subtype.val)
        have hM'_card : M'.card = M.card :=
          card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
        have hM'_match : IsMatching (col j) M' := by
          refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ hne x ⟨hx1, hx2⟩ => ?_⟩
          · rcases mem_image.mp he with ⟨e1, he1, rfl⟩
            induction e1 using Sym2.ind with | _ a b => exact hM.1 _ he1
          · rcases mem_image.mp he₁ with ⟨a₁, ha₁, rfl⟩
            rcases mem_image.mp he₂ with ⟨a₂, ha₂, rfl⟩
            obtain ⟨y₁, hy₁, rfl⟩ := Sym2.mem_map.mp hx1
            obtain ⟨y₂, hy₂, heqy⟩ := Sym2.mem_map.mp hx2
            exact hM.2 a₁ ha₁ a₂ ha₂ (fun h => hne (by rw [h])) y₁ ⟨hy₁, Subtype.ext heqy.symm ▸ hy₂⟩
        have hM'_supp : ∀ e ∈ M', ∀ v ∈ e, v ∈ Cbig.supp := by
          intro e he v hv
          rcases mem_image.mp he with ⟨e1, he1, rfl⟩
          obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hv
          have hyC0 : y ∈ C0.supp := hMC0 e1 he1 y hy
          have hreach_ind : ((col j).induce {u : V | P.assign u = τ}).Reachable y u0 :=
            ConnectedComponent.eq.mp (hyC0.trans hu0C0.symm)
          obtain ⟨w⟩ := hreach_ind
          exact ConnectedComponent.eq.mpr ⟨w.map (Embedding.induce _).toHom⟩
        have hlt := hnomatch j Cbig hCbig_nb M' hM'_match hM'_supp
        rw [hM'_card] at hlt
        have hδ_lt_05 : δ < 1 / 20 := lt_of_le_of_lt (hδ_le_δ0.trans (min_le_left _ _)) (by norm_num)
        nlinarith
    rcases h2cm with ⟨C0, M, hM, hMC0, hMbig⟩ | ⟨C0, M, hM, hMC0, hMbig⟩
    · exact hlift i1 hτi1 C0 M hM hMC0 hMbig
    · exact hlift i2 hτi2 C0 M hM hMC0 hMbig

set_option maxHeartbeats 600000 in
private lemma energy_chunk_other_pair {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {P : Finpartition (Finset.univ : Finset α)} (hP : P.IsEquipartition)
    (G H : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {ε : ℝ} (hε0 : 0 < ε) {k : ℕ} (hk : 1 ≤ k)
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ Fintype.card α)
    (hPεk : 100 * (k : ℝ) ≤ (4 : ℝ) ^ P.parts.card * ε ^ 5)
    (hPG : ¬ P.IsUniform G ε)
    {U V : Finset α} (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / (25 * (k : ℝ)) ≤
      (∑ ab ∈ (SzemerediRegularity.chunk hP G ε hU).parts ×ˢ
              (SzemerediRegularity.chunk hP G ε hV).parts,
        (H.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / (16 : ℝ) ^ P.parts.card := by
  let m : ℕ := Fintype.card α / SzemerediRegularity.stepBound P.parts.card
  have hstep_pos : 0 < SzemerediRegularity.stepBound P.parts.card :=
    SzemerediRegularity.stepBound_pos (P.nonempty_of_not_uniform hPG).card_pos
  have h4_le_m : 4 ^ P.parts.card ≤ m := by
    rw [Nat.le_div_iff_mul_le hstep_pos]
    calc 4 ^ P.parts.card * SzemerediRegularity.stepBound P.parts.card
        = P.parts.card * (4 ^ P.parts.card * 4 ^ P.parts.card) := by
            rw [SzemerediRegularity.stepBound]; ring
      _ = P.parts.card * 16 ^ P.parts.card := by rw [← mul_pow]; norm_num
      _ ≤ Fintype.card α := hPα
  have hm_pos : 0 < m := lt_of_lt_of_le (by positivity) h4_le_m
  have hm_r : (4 : ℝ) ^ P.parts.card ≤ (m : ℝ) := by exact_mod_cast h4_le_m
  have hm_eps : 100 * (k : ℝ) ≤ (m : ℝ) * ε ^ 5 :=
    hPεk.trans (mul_le_mul_of_nonneg_right hm_r (by positivity))
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hm_pos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have h1_sub : 1 - ε ^ 5 / (50 * (k : ℝ)) ≤ ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 := by
    have hdiff : 1 - ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 = (2 * (m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2 := by
      field_simp; ring
    have hle2m : (2 * (m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2 ≤ 2 / (m : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hm_pos_r]; nlinarith
    have h2m_le : 2 / (m : ℝ) ≤ ε ^ 5 / (50 * (k : ℝ)) := by
      rw [div_le_div_iff₀ hm_pos_r (by positivity)]; linarith
    linarith
  let CU := (SzemerediRegularity.chunk hP G ε hU).parts
  let CV := (SzemerediRegularity.chunk hP G ε hV).parts
  have hCU_card : CU.card = 4 ^ P.parts.card := SzemerediRegularity.card_chunk hm_pos.ne'
  have hCV_card : CV.card = 4 ^ P.parts.card := SzemerediRegularity.card_chunk hm_pos.ne'
  have hprod_card : (CU ×ˢ CV).card = 16 ^ P.parts.card := by
    rw [card_product, hCU_card, hCV_card, ← mul_pow]; norm_num
  have hU_ge : CU.card * m ≤ U.card := by
    have hsum : ∑ x ∈ CU, x.card = U.card := by
      simpa [CU] using (SzemerediRegularity.chunk hP G ε hU).sum_card_parts
    rw [← hsum]
    calc CU.card * m = ∑ _x ∈ CU, m := by simp
      _ ≤ ∑ x ∈ CU, x.card := sum_le_sum fun x hx =>
          SzemerediRegularity.m_le_card_of_mem_chunk_parts hx
  have hV_ge : CV.card * m ≤ V.card := by
    have hsum : ∑ y ∈ CV, y.card = V.card := by
      simpa [CV] using (SzemerediRegularity.chunk hP G ε hV).sum_card_parts
    rw [← hsum]
    calc CV.card * m = ∑ _y ∈ CV, m := by simp
      _ ≤ ∑ y ∈ CV, y.card := sum_le_sum fun y hy =>
          SzemerediRegularity.m_le_card_of_mem_chunk_parts hy
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast (P.nonempty_of_mem_parts hU).card_pos
  have hV_pos : (0 : ℝ) < (V.card : ℝ) := by exact_mod_cast (P.nonempty_of_mem_parts hV).card_pos
  have hd_le1 : (H.edgeDensity U V : ℝ) ≤ 1 := by exact_mod_cast H.edgeDensity_le_one U V
  have hd_nn : (0 : ℝ) ≤ (H.edgeDensity U V : ℝ) := by exact_mod_cast H.edgeDensity_nonneg U V
  have hlin : (H.edgeDensity U V : ℝ) - ε ^ 5 / (50 * (k : ℝ)) ≤
      (∑ ab ∈ CU ×ˢ CV, (H.edgeDensity ab.1 ab.2 : ℝ)) / (16 : ℝ) ^ P.parts.card := by
    have h1 : (H.edgeDensity U V : ℝ) - ε ^ 5 / (50 * (k : ℝ)) ≤
        ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 * (H.edgeDensity U V : ℝ) := by
      have h1a : (H.edgeDensity U V : ℝ) - ε ^ 5 / (50 * (k : ℝ)) ≤
          (1 - ε ^ 5 / (50 * (k : ℝ))) * (H.edgeDensity U V : ℝ) := by
        have : (H.edgeDensity U V : ℝ) * (ε ^ 5 / (50 * (k : ℝ))) ≤ ε ^ 5 / (50 * (k : ℝ)) :=
          mul_le_of_le_one_left (by positivity) hd_le1
        linarith
      exact h1a.trans (mul_le_mul_of_nonneg_right h1_sub hd_nn)
    refine h1.trans ?_
    have hinter : (H.interedges U V).card = ∑ ab ∈ CU ×ˢ CV, (H.interedges ab.1 ab.2).card := by
      simpa [SimpleGraph.interedges, CU, CV] using
        Rel.card_interedges_finpartition H.Adj (SzemerediRegularity.chunk hP G ε hU)
          (SzemerediRegularity.chunk hP G ε hV)
    have hprod_eq : ((CU.card : ℝ) * (CV.card : ℝ)) = (16 : ℝ) ^ P.parts.card := by
      rw [← Nat.cast_mul, ← card_product, hprod_card]; norm_cast
    rw [edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
        Rat.cast_natCast, Rat.cast_natCast, hinter, Nat.cast_sum, sum_div, mul_sum,
        sum_div]
    refine sum_le_sum fun ab hab => ?_
    rcases mem_product.mp hab with ⟨hx, hy⟩
    have hx_pos : (0 : ℝ) < (ab.1.card : ℝ) := by
      exact_mod_cast ((SzemerediRegularity.chunk hP G ε hU).nonempty_of_mem_parts hx).card_pos
    have hy_pos : (0 : ℝ) < (ab.2.card : ℝ) := by
      exact_mod_cast ((SzemerediRegularity.chunk hP G ε hV).nonempty_of_mem_parts hy).card_pos
    have hx_le : (ab.1.card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast SzemerediRegularity.card_le_m_add_one_of_mem_chunk_parts hx
    have hy_le : (ab.2.card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast SzemerediRegularity.card_le_m_add_one_of_mem_chunk_parts hy
    have hU_ge_r : (CU.card : ℝ) * (m : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hU_ge
    have hV_ge_r : (CV.card : ℝ) * (m : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hV_ge
    have hCU_pos : (0 : ℝ) < (CU.card : ℝ) := by rw [hCU_card]; positivity
    have hCV_pos : (0 : ℝ) < (CV.card : ℝ) := by rw [hCV_card]; positivity
    have hcoeff : ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 / ((U.card : ℝ) * (V.card : ℝ)) ≤
        1 / ((ab.1.card : ℝ) * (ab.2.card : ℝ) * (16 : ℝ) ^ P.parts.card) := by
      rw [← hprod_eq, div_le_div_iff₀ (mul_pos hU_pos hV_pos) (mul_pos (mul_pos hx_pos hy_pos) (mul_pos hCU_pos hCV_pos))]
      rw [sq, div_mul_div_comm, div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by linarith) (by linarith))]
      have h1' : (m : ℝ) * (ab.1.card : ℝ) * (CU.card : ℝ) ≤ ((m : ℝ) + 1) * (U.card : ℝ) := by
        nlinarith [hU_ge_r, hx_le, hCU_pos]
      have h2' : (m : ℝ) * (ab.2.card : ℝ) * (CV.card : ℝ) ≤ ((m : ℝ) + 1) * (V.card : ℝ) := by
        nlinarith [hV_ge_r, hy_le, hCV_pos]
      have hmul := mul_le_mul h1' h2' (by positivity) (by positivity)
      linarith
    rw [edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
        Rat.cast_natCast, Rat.cast_natCast, div_div]
    have hc_nn : (0 : ℝ) ≤ ((H.interedges ab.1 ab.2).card : ℝ) := Nat.cast_nonneg _
    calc ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 * (((H.interedges ab.1 ab.2).card : ℝ) / ((U.card : ℝ) * (V.card : ℝ)))
        = ((H.interedges ab.1 ab.2).card : ℝ) * (((m : ℝ) / ((m : ℝ) + 1)) ^ 2 / ((U.card : ℝ) * (V.card : ℝ))) := by ring
      _ ≤ ((H.interedges ab.1 ab.2).card : ℝ) * (1 / ((ab.1.card : ℝ) * (ab.2.card : ℝ) * (16 : ℝ) ^ P.parts.card)) :=
          mul_le_mul_of_nonneg_left hcoeff hc_nn
      _ = ((H.interedges ab.1 ab.2).card : ℝ) / ((ab.1.card : ℝ) * (ab.2.card : ℝ) * (16 : ℝ) ^ P.parts.card) := by ring
  have hsq_lin : (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / (25 * (k : ℝ)) ≤
      ((∑ ab ∈ CU ×ˢ CV, (H.edgeDensity ab.1 ab.2 : ℝ)) / (16 : ℝ) ^ P.parts.card) ^ 2 := by
    by_cases hsmall : (H.edgeDensity U V : ℝ) ≤ ε ^ 5 / (50 * (k : ℝ))
    · have hle : (H.edgeDensity U V : ℝ) ^ 2 ≤ ε ^ 5 / (25 * (k : ℝ)) := by
        have : (H.edgeDensity U V : ℝ) ^ 2 ≤ (H.edgeDensity U V : ℝ) := by nlinarith
        have : ε ^ 5 / (50 * (k : ℝ)) ≤ ε ^ 5 / (25 * (k : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hε0 5]
        linarith
      linarith [sq_nonneg ((∑ ab ∈ CU ×ˢ CV, (H.edgeDensity ab.1 ab.2 : ℝ)) / (16 : ℝ) ^ P.parts.card)]
    · have hnn : 0 ≤ (H.edgeDensity U V : ℝ) - ε ^ 5 / (50 * (k : ℝ)) := by linarith
      have hsq := mul_self_le_mul_self hnn hlin
      rw [← sq, ← sq] at hsq
      have h2 : 2 * (ε ^ 5 / (50 * (k : ℝ))) = ε ^ 5 / (25 * (k : ℝ)) := by ring
      have hmul : (H.edgeDensity U V : ℝ) * (ε ^ 5 / (25 * (k : ℝ))) ≤ ε ^ 5 / (25 * (k : ℝ)) :=
        mul_le_of_le_one_left (by positivity) hd_le1
      have hbase : (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / (25 * (k : ℝ)) ≤
          ((H.edgeDensity U V : ℝ) - ε ^ 5 / (50 * (k : ℝ))) ^ 2 := by
        have hsq_exp : ((H.edgeDensity U V : ℝ) - ε ^ 5 / (50 * (k : ℝ))) ^ 2 =
            (H.edgeDensity U V : ℝ) ^ 2 - (H.edgeDensity U V : ℝ) * (ε ^ 5 / (25 * (k : ℝ))) +
              (ε ^ 5 / (50 * (k : ℝ))) ^ 2 := by ring
        linarith [hsq_exp, hmul, sq_nonneg (ε ^ 5 / (50 * (k : ℝ)))]
      exact hbase.trans hsq
  have hcs : ((∑ ab ∈ CU ×ˢ CV, (H.edgeDensity ab.1 ab.2 : ℝ)) / (16 : ℝ) ^ P.parts.card) ^ 2 ≤
      (∑ ab ∈ CU ×ˢ CV, (H.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / (16 : ℝ) ^ P.parts.card := by
    have hcard_r : ((CU ×ˢ CV).card : ℝ) = (16 : ℝ) ^ P.parts.card := by rw [hprod_card]; norm_cast
    have hnn : 0 ≤ ∑ x ∈ CU ×ˢ CV, ∑ y ∈ CU ×ˢ CV,
        ((H.edgeDensity x.1 x.2 : ℝ) - (H.edgeDensity y.1 y.2 : ℝ)) ^ 2 :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
    have hexp : ∑ x ∈ CU ×ˢ CV, ∑ y ∈ CU ×ˢ CV,
          ((H.edgeDensity x.1 x.2 : ℝ) - (H.edgeDensity y.1 y.2 : ℝ)) ^ 2 =
        2 * (((CU ×ˢ CV).card : ℝ) * (∑ x ∈ CU ×ˢ CV, (H.edgeDensity x.1 x.2 : ℝ) ^ 2) -
          (∑ x ∈ CU ×ˢ CV, (H.edgeDensity x.1 x.2 : ℝ)) ^ 2) := by
      simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const,
        nsmul_eq_mul, ← mul_sum, ← sum_mul]
      have h2 : ∑ x ∈ CU ×ˢ CV, 2 * (H.edgeDensity x.1 x.2 : ℝ) =
          2 * ∑ x ∈ CU ×ˢ CV, (H.edgeDensity x.1 x.2 : ℝ) := by rw [mul_sum]
      rw [h2]; ring
    have hsq_le : (∑ x ∈ CU ×ˢ CV, (H.edgeDensity x.1 x.2 : ℝ)) ^ 2 ≤
        (16 : ℝ) ^ P.parts.card * ∑ x ∈ CU ×ˢ CV, (H.edgeDensity x.1 x.2 : ℝ) ^ 2 := by
      rw [← hcard_r]; linarith
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 16) P.parts.card]
  exact hsq_lin.trans hcs
lemma energy_increment_other {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {P : Finpartition (Finset.univ : Finset α)} (hP : P.IsEquipartition)
    (G H : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {ε : ℝ} (hε0 : 0 < ε) {k : ℕ} (hk : 1 ≤ k)
    (hPα : P.parts.card * 16 ^ P.parts.card ≤ Fintype.card α)
    (hPεk : 100 * (k : ℝ) ≤ (4 : ℝ) ^ P.parts.card * ε ^ 5)
    (hPG : ¬ P.IsUniform G ε) :
    (P.energy H : ℝ) - ε ^ 5 / (25 * (k : ℝ)) ≤
      ((SzemerediRegularity.increment hP G ε).energy H : ℝ) := by
  let dp : {x // x ∈ P.parts.offDiag} → Finset (Finset α × Finset α) := fun x =>
    (SzemerediRegularity.chunk hP G ε (mem_offDiag.mp x.2).1).parts ×ˢ
    (SzemerediRegularity.chunk hP G ε (mem_offDiag.mp x.2).2.1).parts
  have hdp_sub : P.parts.offDiag.attach.biUnion dp ⊆ (SzemerediRegularity.increment hP G ε).parts.offDiag := by
    rintro ⟨Ui, Vj⟩ hmem
    simp only [dp, SzemerediRegularity.increment, mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, mem_offDiag, mem_product, Finpartition.bind_parts] at hmem ⊢
    rcases hmem with ⟨⟨U, V⟩, ⟨hU, hV, hUV⟩, hUi, hVj⟩
    refine ⟨⟨U, hU, hUi⟩, ⟨V, hV, hVj⟩, ?_⟩
    rintro rfl
    obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ hUi
    exact hUV (P.disjoint.elim_finset hU hV a (Finpartition.le _ hUi ha) (Finpartition.le _ hVj ha))
  have hdp_disj : (P.parts.offDiag.attach : Set {x // x ∈ P.parts.offDiag}).PairwiseDisjoint dp := by
    intro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst
    change Disjoint (dp ⟨(s₁, s₂), hs⟩) (dp ⟨(t₁, t₂), ht⟩)
    rw [Finset.disjoint_left]
    rintro ⟨u, v⟩ h1 h2
    simp only [dp, mem_product] at h1 h2
    rw [mem_offDiag] at hs ht
    obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ h1.1
    obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ h1.2
    exact hst (Subtype.ext (Prod.ext
      (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ h1.1 ha) (Finpartition.le _ h2.1 ha))
      (P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ h1.2 hb) (Finpartition.le _ h2.2 hb))))
  have hP_pos : (0 : ℝ) < (P.parts.card : ℝ) := by
    exact_mod_cast (P.nonempty_of_not_uniform hPG).card_pos
  have hcard_inc : ((SzemerediRegularity.increment hP G ε).parts.card : ℝ) ^ 2 =
      (P.parts.card : ℝ) ^ 2 * (16 : ℝ) ^ P.parts.card := by
    rw [SzemerediRegularity.card_increment hPα hPG, SzemerediRegularity.coe_stepBound,
        mul_pow, ← pow_mul, mul_comm P.parts.card 2, pow_mul]
    norm_num
  have hoff_le : (P.parts.offDiag.card : ℝ) ≤ (P.parts.card : ℝ) ^ 2 := by
    rw [offDiag_card, sq]
    exact_mod_cast Nat.sub_le (P.parts.card * P.parts.card) P.parts.card
  calc (P.energy H : ℝ) - ε ^ 5 / (25 * (k : ℝ))
      = ((∑ x ∈ P.parts.offDiag, (H.edgeDensity x.1 x.2 : ℝ) ^ 2) -
          (P.parts.card : ℝ) ^ 2 * (ε ^ 5 / (25 * (k : ℝ)))) / (P.parts.card : ℝ) ^ 2 := by
          rw [Finpartition.coe_energy, sub_div, mul_div_cancel_left₀ _ (by positivity)]
    _ ≤ ((∑ x ∈ P.parts.offDiag, (H.edgeDensity x.1 x.2 : ℝ) ^ 2) -
          (P.parts.offDiag.card : ℝ) * (ε ^ 5 / (25 * (k : ℝ)))) / (P.parts.card : ℝ) ^ 2 := by
          gcongr
    _ = (∑ x ∈ P.parts.offDiag.attach, ((H.edgeDensity x.1.1 x.1.2 : ℝ) ^ 2 - ε ^ 5 / (25 * (k : ℝ)))) /
          (P.parts.card : ℝ) ^ 2 := by
          rw [sum_attach P.parts.offDiag (fun x => (H.edgeDensity x.1 x.2 : ℝ) ^ 2 - ε ^ 5 / (25 * (k : ℝ))),
              sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ (∑ x ∈ P.parts.offDiag.attach,
          (∑ ab ∈ dp x, (H.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / (16 : ℝ) ^ P.parts.card) /
          (P.parts.card : ℝ) ^ 2 := by
          gcongr with x _
          exact energy_chunk_other_pair hP G H hε0 hk hPα hPεk hPG
            (mem_offDiag.mp x.2).1 (mem_offDiag.mp x.2).2.1
    _ = (∑ x ∈ P.parts.offDiag.attach, ∑ ab ∈ dp x, (H.edgeDensity ab.1 ab.2 : ℝ) ^ 2) /
          ((SzemerediRegularity.increment hP G ε).parts.card : ℝ) ^ 2 := by
          rw [← sum_div, div_div, mul_comm ((16 : ℝ) ^ P.parts.card), hcard_inc]
    _ ≤ ((SzemerediRegularity.increment hP G ε).energy H : ℝ) := by
          rw [Finpartition.coe_energy]
          gcongr
          rw [← Finset.sum_biUnion hdp_disj]
          exact Finset.sum_le_sum_of_subset_of_nonneg hdp_sub fun _ _ _ => sq_nonneg _
lemma multicolour_szemeredi_regularity {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (t0 : ℕ) (ht0 : 1 ≤ t0) :
    ∃ (T0 N0 : ℕ), t0 ≤ T0 ∧
      ∀ (α : Type*) [Fintype α] [DecidableEq α]
        (col : Fin k → SimpleGraph α) [∀ c, DecidableRel (col c).Adj],
        N0 ≤ Fintype.card α →
        ∃ (t m : ℕ) (V : Fin t → Finset α),
          t0 ≤ t ∧ t ≤ T0 ∧ 1 ≤ m ∧
          (∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j)) ∧
          (∀ i : Fin t, (V i).card = m) ∧
          (Fintype.card α : ℝ) - (t * m : ℝ) ≤ ε * (Fintype.card α : ℝ) ∧
          ∀ c : Fin k,
            (((Finset.univ : Finset (Fin t)).offDiag.filter
              (fun ij => ¬ (col c).IsUniform ε (V ij.1) (V ij.2))).card : ℝ) ≤ ε * (t : ℝ) ^ 2 := by
  let ε' : ℝ := ε / 2
  have hε'0 : 0 < ε' := by positivity
  have hε'1 : ε' ≤ 1 := by dsimp only [ε']; linarith
  let t_init : ℕ := max (max t0 7) (Nat.ceil (100 * (k : ℝ) / ε' ^ 5))
  let steps : ℕ := Nat.floor (5 * (k : ℝ) / ε' ^ 5) + 1
  let T0 : ℕ := SzemerediRegularity.stepBound^[steps] t_init
  let N0 : ℕ := max (T0 * 16 ^ T0) (max (Nat.ceil ((T0 : ℝ) / ε) + T0) 1)
  have hstep_mono : ∀ a b : ℕ, a ≤ b → SzemerediRegularity.stepBound^[a] t_init ≤ SzemerediRegularity.stepBound^[b] t_init := by
    intro a b hab
    induction b with
    | zero =>
      have ha : a = 0 := by omega
      subst ha; exact le_refl _
    | succ b ih =>
      by_cases he : a = b + 1
      · subst he; exact le_refl _
      · rw [Function.iterate_succ_apply']
        exact (ih (by omega)).trans (SzemerediRegularity.le_stepBound _)
  have ht_init_le_T0 : t_init ≤ T0 := hstep_mono 0 steps (Nat.zero_le _)
  have ht0_le_T0 : t0 ≤ T0 := ((le_max_left t0 7).trans (le_max_left _ _)).trans ht_init_le_T0
  refine ⟨T0, N0, ht0_le_T0, ?_⟩
  intro α _ _ col _ hcard
  have hneα : Nonempty α := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by omega) ((le_max_right _ _).trans ((le_max_right _ _).trans hcard)))
  have hN0_reg : T0 * 16 ^ T0 ≤ Fintype.card α := (le_max_left _ _).trans hcard
  have ht_init_le_card : t_init ≤ (Finset.univ : Finset α).card := by
    rw [card_univ]
    calc t_init ≤ T0 := ht_init_le_T0
      _ ≤ T0 * 16 ^ T0 := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ Fintype.card α := hN0_reg
  have ht_init_pos : 0 < t_init := lt_of_lt_of_le (by omega) ((le_max_right t0 7).trans (le_max_left _ _))
  obtain ⟨dum, hdum_eq, hdum_card⟩ := Finpartition.exists_equipartition_card_eq (Finset.univ : Finset α)
    ht_init_pos.ne' ht_init_le_card
  have hind : ∀ i : ℕ, i ≤ steps →
      ∃ P : Finpartition (Finset.univ : Finset α),
        P.IsEquipartition ∧ t_init ≤ P.parts.card ∧
        P.parts.card ≤ SzemerediRegularity.stepBound^[i] t_init ∧
        ((∀ c : Fin k, P.IsUniform (col c) ε') ∨
          (i : ℝ) * (ε' ^ 5 / 5) ≤ ∑ c : Fin k, (P.energy (col c) : ℝ)) := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨dum, hdum_eq, hdum_card.ge, hdum_card.le, Or.inr ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      exact sum_nonneg fun c _ => by exact_mod_cast dum.energy_nonneg (col c)
    | succ i ih =>
      obtain ⟨P, hPeq, hPlo, hPhi, hPor⟩ := ih (Nat.le_of_succ_le hi)
      by_cases hall : ∀ c : Fin k, P.IsUniform (col c) ε'
      · refine ⟨P, hPeq, hPlo, ?_, Or.inl hall⟩
        rw [Function.iterate_succ_apply']
        exact hPhi.trans (SzemerediRegularity.le_stepBound _)
      · have hE := hPor.resolve_left hall
        push Not at hall
        obtain ⟨c0, hc0⟩ := hall
        have hP_le_T0 : P.parts.card ≤ T0 := hPhi.trans (hstep_mono i steps (Nat.le_of_succ_le hi))
        have hPα : P.parts.card * 16 ^ P.parts.card ≤ Fintype.card α :=
          (Nat.mul_le_mul hP_le_T0 (Nat.pow_le_pow_right (by norm_num) hP_le_T0)).trans hN0_reg
        have hP7 : 7 ≤ P.parts.card := ((le_max_right t0 7).trans (le_max_left _ _)).trans hPlo
        have hPεk : 100 * (k : ℝ) ≤ (4 : ℝ) ^ P.parts.card * ε' ^ 5 := by
          have h1 : 100 * (k : ℝ) / ε' ^ 5 ≤ (t_init : ℝ) := by
            have hceil : Nat.ceil (100 * (k : ℝ) / ε' ^ 5) ≤ t_init := le_max_right _ _
            exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
          have h2 : (t_init : ℝ) ≤ (P.parts.card : ℝ) := by exact_mod_cast hPlo
          have h3 : (P.parts.card : ℝ) ≤ (4 : ℝ) ^ P.parts.card := by
            have h4n : ∀ n : ℕ, n ≤ 4 ^ n := fun n => by
              induction n with
              | zero => norm_num
              | succ n ihn =>
                have h1p : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
                rw [pow_succ]; omega
            exact_mod_cast h4n P.parts.card
          have h4 : 100 * (k : ℝ) / ε' ^ 5 ≤ (4 : ℝ) ^ P.parts.card := h1.trans (h2.trans h3)
          exact (div_le_iff₀ (by positivity)).mp h4
        have hPε : 100 ≤ (4 : ℝ) ^ P.parts.card * ε' ^ 5 := by
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          nlinarith
        let P' := SzemerediRegularity.increment hPeq (col c0) ε'
        have hP'eq : P'.IsEquipartition := SzemerediRegularity.increment_isEquipartition hPeq (col c0) ε'
        have hP'card : P'.parts.card = SzemerediRegularity.stepBound P.parts.card :=
          SzemerediRegularity.card_increment hPα hc0
        have hEc0 : (P.energy (col c0) : ℝ) + ε' ^ 5 / 4 ≤ (P'.energy (col c0) : ℝ) :=
          SzemerediRegularity.energy_increment hPeq hP7 hPε hPα hc0 hε'0.le hε'1
        have hEother : ∀ c : Fin k, c ≠ c0 →
            (P.energy (col c) : ℝ) - ε' ^ 5 / (25 * (k : ℝ)) ≤ (P'.energy (col c) : ℝ) := fun c _ =>
          energy_increment_other hPeq (col c0) (col c) hε'0 hk hPα hPεk hc0
        have hsum_inc : (∑ c : Fin k, (P.energy (col c) : ℝ)) + ε' ^ 5 / 5 ≤
            ∑ c : Fin k, (P'.energy (col c) : ℝ) := by
          rw [← Finset.add_sum_erase _ _ (mem_univ c0),
              ← Finset.add_sum_erase _ (fun c => (P'.energy (col c) : ℝ)) (mem_univ c0)]
          have hrest : (∑ c ∈ Finset.univ.erase c0, (P.energy (col c) : ℝ)) -
              ((k - 1 : ℕ) : ℝ) * (ε' ^ 5 / (25 * (k : ℝ))) ≤
              ∑ c ∈ Finset.univ.erase c0, (P'.energy (col c) : ℝ) := by
            have hcard_er : (Finset.univ.erase c0).card = k - 1 := by
              rw [card_erase_of_mem (mem_univ c0), card_univ, Fintype.card_fin]
            calc (∑ c ∈ Finset.univ.erase c0, (P.energy (col c) : ℝ)) -
                  ((k - 1 : ℕ) : ℝ) * (ε' ^ 5 / (25 * (k : ℝ)))
                = ∑ c ∈ Finset.univ.erase c0, ((P.energy (col c) : ℝ) - ε' ^ 5 / (25 * (k : ℝ))) := by
                    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard_er]
              _ ≤ ∑ c ∈ Finset.univ.erase c0, (P'.energy (col c) : ℝ) :=
                    sum_le_sum fun c hc => hEother c (Finset.ne_of_mem_erase hc)
          have hloss : ((k - 1 : ℕ) : ℝ) * (ε' ^ 5 / (25 * (k : ℝ))) ≤ ε' ^ 5 / 25 := by
            have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            have hk1_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
            calc ((k - 1 : ℕ) : ℝ) * (ε' ^ 5 / (25 * (k : ℝ)))
                ≤ (k : ℝ) * (ε' ^ 5 / (25 * (k : ℝ))) := mul_le_mul_of_nonneg_right hk1_le (by positivity)
              _ = ε' ^ 5 / 25 := by field_simp
          linarith [pow_pos hε'0 5]
        refine ⟨P', hP'eq, ?_, ?_, Or.inr ?_⟩
        · rw [hP'card]; exact hPlo.trans (SzemerediRegularity.le_stepBound _)
        · rw [hP'card, Function.iterate_succ_apply']; exact SzemerediRegularity.stepBound_mono hPhi
        · rw [Nat.cast_succ, add_mul, one_mul]; linarith
  obtain ⟨P, hPeq, hPlo, hPhi, hPor⟩ := hind steps (le_refl steps)
  have hPunif : ∀ c : Fin k, P.IsUniform (col c) ε' := hPor.resolve_right fun hE => by
    have hsum_le_k : ∑ c : Fin k, (P.energy (col c) : ℝ) ≤ (k : ℝ) := by
      calc ∑ c : Fin k, (P.energy (col c) : ℝ) ≤ ∑ _c : Fin k, (1 : ℝ) :=
            sum_le_sum fun c _ => by exact_mod_cast P.energy_le_one (col c)
        _ = (k : ℝ) := by simp
    have hgt : (k : ℝ) < (steps : ℝ) * (ε' ^ 5 / 5) := by
      have hfl : 5 * (k : ℝ) / ε' ^ 5 < (steps : ℝ) := by
        dsimp only [steps]; push_cast; exact Nat.lt_floor_add_one _
      have hmul := mul_lt_mul_of_pos_right hfl (by positivity : 0 < ε' ^ 5 / 5)
      have heq : 5 * (k : ℝ) / ε' ^ 5 * (ε' ^ 5 / 5) = (k : ℝ) := by field_simp
      linarith
    linarith
  let t : ℕ := P.parts.card
  let m : ℕ := Fintype.card α / t
  have ht_ge_t0 : t0 ≤ t := ((le_max_left t0 7).trans (le_max_left _ _)).trans hPlo
  have ht_le_T0 : t ≤ T0 := hPhi
  have ht_pos : 0 < t := lt_of_lt_of_le ht0 ht_ge_t0
  have hm_ge1 : 1 ≤ m := Nat.div_pos (ht_le_T0.trans ((Nat.le_mul_of_pos_right T0 (by positivity)).trans hN0_reg)) ht_pos
  have heq_bounds : ∀ U ∈ P.parts, m ≤ U.card ∧ U.card ≤ m + 1 := by
    obtain ⟨r, hr⟩ := Set.equitableOn_iff_exists_eq_eq_add_one.mp hPeq
    have hsum : ∑ U ∈ P.parts, U.card = Fintype.card α := by
      simpa [card_univ] using P.sum_card_parts
    have hlo : t * r ≤ Fintype.card α := by
      rw [← hsum]
      calc t * r = ∑ _U ∈ P.parts, r := by simp [t]
        _ ≤ ∑ U ∈ P.parts, U.card := sum_le_sum fun U hU => by rcases hr U hU with h | h <;> omega
    have hhi : Fintype.card α ≤ t * (r + 1) := by
      rw [← hsum]
      calc ∑ U ∈ P.parts, U.card ≤ ∑ _U ∈ P.parts, (r + 1) :=
            sum_le_sum fun U hU => by rcases hr U hU with h | h <;> omega
        _ = t * (r + 1) := by simp [t]
    have hm_r : m = r ∨ (m = r + 1 ∧ ∀ U ∈ P.parts, U.card = r + 1) := by
      by_cases heq : Fintype.card α = t * (r + 1)
      · right
        refine ⟨by dsimp only [m]; rw [heq, Nat.mul_div_cancel_left _ ht_pos], fun U hU => ?_⟩
        by_contra hne
        have hUr : U.card = r := (hr U hU).resolve_right hne
        have hlt : ∑ W ∈ P.parts, W.card < t * (r + 1) := by
          rw [← Finset.add_sum_erase _ _ hU, hUr]
          have hrest : ∑ W ∈ P.parts.erase U, W.card ≤ (t - 1) * (r + 1) := by
            calc ∑ W ∈ P.parts.erase U, W.card ≤ ∑ _W ∈ P.parts.erase U, (r + 1) :=
                  sum_le_sum fun W hW => by rcases hr W (Finset.mem_of_mem_erase hW) with h | h <;> omega
              _ = (t - 1) * (r + 1) := by simp [card_erase_of_mem hU, t]
          have : r + (t - 1) * (r + 1) < t * (r + 1) := by
            have : t = (t - 1) + 1 := by omega
            conv_rhs => rw [this, add_mul, one_mul]
            omega
          omega
        omega
      · left
        have hlt : Fintype.card α < t * (r + 1) := lt_of_le_of_ne hhi heq
        have h1 : r ≤ m := (Nat.le_div_iff_mul_le ht_pos).mpr (by rw [mul_comm]; exact hlo)
        have h2 : m < r + 1 := (Nat.div_lt_iff_lt_mul ht_pos).mpr (by rw [mul_comm]; exact hlt)
        omega
    intro U hU
    rcases hm_r with hmr | ⟨hmr, hall⟩
    · rcases hr U hU with h | h <;> omega
    · have := hall U hU; omega
  let e : Fin t ≃ P.parts := (Fintype.equivFinOfCardEq (Fintype.card_coe P.parts)).symm
  have hexV : ∀ i : Fin t, ∃ s ⊆ (e i).val, s.card = m :=
    fun i => exists_subset_card_eq (heq_bounds (e i).val (e i).property).1
  choose V hVsub hVcard using hexV
  refine ⟨t, m, V, ht_ge_t0, ht_le_T0, hm_ge1, ?_, hVcard, ?_, ?_⟩
  · intro i j hij
    have hne : (e i).val ≠ (e j).val := fun h => hij (e.injective (Subtype.ext h))
    exact Disjoint.mono (hVsub i) (hVsub j) (P.disjoint (e i).property (e j).property hne)
  · have hrem : Fintype.card α - t * m ≤ t := by
      have hdiv := Nat.div_add_mod (Fintype.card α) t
      have hmod := Nat.mod_lt (Fintype.card α) ht_pos
      dsimp only [m]; omega
    have htm_le : t * m ≤ Fintype.card α := Nat.mul_div_le (Fintype.card α) t
    have hrem_r : (Fintype.card α : ℝ) - (t * m : ℝ) ≤ (t : ℝ) := by
      have h1 : ((Fintype.card α - t * m : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrem
      rwa [Nat.cast_sub htm_le, Nat.cast_mul] at h1
    have ht_le_eps : (t : ℝ) ≤ ε * (Fintype.card α : ℝ) := by
      have h1 : (T0 : ℝ) / ε ≤ (Fintype.card α : ℝ) := by
        have ha : Nat.ceil ((T0 : ℝ) / ε) ≤ Fintype.card α :=
          (Nat.le_add_right _ T0).trans ((le_max_left _ 1).trans ((le_max_right _ _).trans hcard))
        exact (Nat.le_ceil _).trans (by exact_mod_cast ha)
      have h2 : (T0 : ℝ) ≤ ε * (Fintype.card α : ℝ) := by rw [mul_comm]; exact (div_le_iff₀ hε0).mp h1
      have h3 : (t : ℝ) ≤ (T0 : ℝ) := by exact_mod_cast ht_le_T0
      linarith
    linarith
  · intro c
    have htrans : ∀ i j : Fin t,
        (col c).IsUniform ε' (e i).val (e j).val → (col c).IsUniform ε (V i) (V j) := by
      intro i j hunif A hA B hB hAcard hBcard
      have hUi_le : ((e i).val.card : ℝ) ≤ 2 * (m : ℝ) := by
        have h1 := (heq_bounds (e i).val (e i).property).2
        have h2 : (e i).val.card ≤ 2 * m := by omega
        exact_mod_cast h2
      have hUj_le : ((e j).val.card : ℝ) ≤ 2 * (m : ℝ) := by
        have h1 := (heq_bounds (e j).val (e j).property).2
        have h2 : (e j).val.card ≤ 2 * m := by omega
        exact_mod_cast h2
      have hVi_big : ((e i).val.card : ℝ) * ε' ≤ (V i).card := by
        rw [hVcard i]; dsimp only [ε']; nlinarith
      have hVj_big : ((e j).val.card : ℝ) * ε' ≤ (V j).card := by
        rw [hVcard j]; dsimp only [ε']; nlinarith
      have hA_big : ((e i).val.card : ℝ) * ε' ≤ A.card := by
        rw [hVcard i] at hAcard; dsimp only [ε']; nlinarith
      have hB_big : ((e j).val.card : ℝ) * ε' ≤ B.card := by
        rw [hVcard j] at hBcard; dsimp only [ε']; nlinarith
      have hd1 := hunif (hA.trans (hVsub i)) (hB.trans (hVsub j)) hA_big hB_big
      have hd2 := hunif (hVsub i) (hVsub j) hVi_big hVj_big
      have htri : |((col c).edgeDensity A B : ℝ) - ((col c).edgeDensity (V i) (V j) : ℝ)| ≤
          |((col c).edgeDensity A B : ℝ) - ((col c).edgeDensity (e i).val (e j).val : ℝ)| +
          |((col c).edgeDensity (V i) (V j) : ℝ) - ((col c).edgeDensity (e i).val (e j).val : ℝ)| := by
        rw [abs_sub_comm ((col c).edgeDensity (V i) (V j) : ℝ)]
        exact abs_sub_le _ _ _
      dsimp only [ε'] at hd1 hd2
      linarith
    let bad := (Finset.univ : Finset (Fin t)).offDiag.filter
      (fun ij => ¬ (col c).IsUniform ε (V ij.1) (V ij.2))
    have hcard_le : bad.card ≤ (P.nonUniforms (col c) ε').card := by
      refine card_le_card_of_injOn (fun ij => ((e ij.1).val, (e ij.2).val)) ?_ ?_
      · intro ij hij
        rw [mem_coe, mem_filter, mem_offDiag] at hij
        rw [mem_coe, Finpartition.mk_mem_nonUniforms]
        refine ⟨(e ij.1).property, (e ij.2).property,
          fun h => hij.1.2.2 (e.injective (Subtype.ext h)), fun hu => hij.2 (htrans ij.1 ij.2 hu)⟩
      · intro p1 _ p2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (e.injective (Subtype.ext heq.1)) (e.injective (Subtype.ext heq.2))
    have h1 : (bad.card : ℝ) ≤ ((P.nonUniforms (col c) ε').card : ℝ) := by exact_mod_cast hcard_le
    have h2 : ((P.nonUniforms (col c) ε').card : ℝ) ≤ ((t * (t - 1) : ℕ) : ℝ) * ε' := hPunif c
    have h3 : ((t * (t - 1) : ℕ) : ℝ) ≤ (t : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast Nat.mul_le_mul_left t (Nat.sub_le t 1)
    change (bad.card : ℝ) ≤ ε * (t : ℝ) ^ 2
    dsimp only [ε'] at h2
    nlinarith [hε0]
lemma typical_degree_bound_le {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {A B B' : Finset α}
    (hunif : G.IsUniform ε A B) (hB' : B' ⊆ B) (hB'card : (B.card : ℝ) * ε ≤ (B'.card : ℝ)) :
    ((A.filter (fun u => ((G.neighborFinset u ∩ B').card : ℝ) <
      ((G.edgeDensity A B : ℝ) - ε) * (B'.card : ℝ))).card : ℝ) ≤ (A.card : ℝ) * ε := by
  by_cases hA : A.Nonempty
  · by_contra hgt
    push Not at hgt
    let S := A.filter (fun u => ((G.neighborFinset u ∩ B').card : ℝ) <
      ((G.edgeDensity A B : ℝ) - ε) * (B'.card : ℝ))
    have hε0 : 0 < ε := hunif.pos
    have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
    have hSpos : (0 : ℝ) < (S.card : ℝ) := lt_trans (mul_pos hApos hε0) hgt
    have hSne : S.Nonempty := card_pos.mp (by exact_mod_cast hSpos)
    have hdev := hunif (filter_subset _ _) hB' hgt.le hB'card
    have hB'pos : (0 : ℝ) < (B'.card : ℝ) := by
      by_contra hle
      have hB'0 : B'.card = 0 := by
        have : (B'.card : ℝ) ≤ 0 := not_lt.mp hle
        exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
      obtain ⟨u, hu⟩ := hSne
      have hlt := (mem_filter.mp hu).2
      rw [hB'0, Nat.cast_zero, mul_zero] at hlt
      linarith [Nat.cast_nonneg (α := ℝ) (G.neighborFinset u ∩ B').card]
    have hinter_eq : (G.interedges S B').card = ∑ u ∈ S, (G.neighborFinset u ∩ B').card := by
      have hbi : G.interedges S B' = S.biUnion (fun u => (G.neighborFinset u ∩ B').image (fun v => (u, v))) := by
        ext ⟨u, v⟩
        simp only [SimpleGraph.interedges, Rel.interedges, mem_filter, mem_product,
          mem_biUnion, mem_image, mem_inter, mem_neighborFinset, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hu, hv⟩, huv⟩; exact ⟨u, hu, v, ⟨huv, hv⟩, rfl, rfl⟩
        · rintro ⟨u', hu', v', ⟨huv, hv'⟩, rfl, rfl⟩; exact ⟨⟨hu', hv'⟩, huv⟩
      rw [hbi, card_biUnion]
      · refine Finset.sum_congr rfl fun u _ =>
          card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro u₁ _ u₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        rcases mem_image.mp h1 with ⟨_, _, h1'⟩
        rcases mem_image.mp h2 with ⟨_, _, h2'⟩
        exact hne ((Prod.mk.inj h1').1.trans (Prod.mk.inj h2').1.symm)
    have hsum_lt : ((G.interedges S B').card : ℝ) <
        (S.card : ℝ) * (((G.edgeDensity A B : ℝ) - ε) * (B'.card : ℝ)) := by
      rw [hinter_eq, Nat.cast_sum]
      calc ∑ u ∈ S, ((G.neighborFinset u ∩ B').card : ℝ)
          < ∑ _u ∈ S, (((G.edgeDensity A B : ℝ) - ε) * (B'.card : ℝ)) :=
            sum_lt_sum_of_nonempty hSne fun u hu => (mem_filter.mp hu).2
        _ = (S.card : ℝ) * (((G.edgeDensity A B : ℝ) - ε) * (B'.card : ℝ)) := by simp
    have hd_lt : (G.edgeDensity S B' : ℝ) < (G.edgeDensity A B : ℝ) - ε := by
      rw [edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
          Rat.cast_natCast, Rat.cast_natCast, div_lt_iff₀ (mul_pos hSpos hB'pos)]
      linarith
    rw [abs_lt] at hdev
    linarith
  · rw [not_nonempty_iff_eq_empty] at hA
    subst hA; simp
def IsSimplePath {α : Type*} (G : SimpleGraph α) (p : List α) (L : ℕ) (u w : α) : Prop :=
  p.Nodup ∧ p.length = L + 1 ∧ p.head? = some u ∧ p.getLast? = some w ∧ p.IsChain G.Adj
lemma isSimplePath_singleton {α : Type*} (G : SimpleGraph α) (u : α) :
    IsSimplePath G [u] 0 u u :=
  ⟨List.nodup_singleton u, rfl, rfl, rfl, List.isChain_singleton u⟩
lemma isSimplePath_cons {α : Type*} {G : SimpleGraph α} {p : List α} {L : ℕ} {u v w : α}
    (hp : IsSimplePath G p L v w) (huv : G.Adj u v) (hu : u ∉ p) :
    IsSimplePath G (u :: p) (L + 1) u w := by
  rcases hp with ⟨hnd, hlen, hhead, hlast, hch⟩
  cases p with
  | nil => simp at hlen
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    refine ⟨List.nodup_cons.mpr ⟨hu, hnd⟩, by simp [hlen], rfl, ?_, List.isChain_cons_cons.mpr ⟨huv, hch⟩⟩
    simpa [List.getLast?_cons] using hlast
private lemma isChain_append_of_last_head {α : Type*} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, l₁.IsChain R → l₂.IsChain R →
      (∀ x, l₁.getLast? = some x → ∀ y, l₂.head? = some y → R x y) → (l₁ ++ l₂).IsChain R
  | [], _, _, h₂, _ => h₂
  | [a], [], h₁, _, _ => by simpa using h₁
  | [a], b :: t, _, h₂, h => List.isChain_cons_cons.mpr ⟨h a rfl b rfl, h₂⟩
  | a :: c :: r, l₂, h₁, h₂, h => by
    have ⟨hac, hcr⟩ := List.isChain_cons_cons.mp h₁
    exact List.isChain_cons_cons.mpr ⟨hac, isChain_append_of_last_head hcr h₂ (fun x hx y hy => h x (by simpa [List.getLast?_cons] using hx) y hy)⟩
private lemma isChain_reverse_symm {α : Type*} {G : SimpleGraph α} :
    ∀ {l : List α}, l.IsChain G.Adj → l.reverse.IsChain G.Adj
  | [], _ => List.isChain_nil
  | [a], _ => List.isChain_singleton a
  | a :: b :: t, h => by
    have ⟨hab, hbt⟩ := List.isChain_cons_cons.mp h
    rw [List.reverse_cons]
    refine isChain_append_of_last_head (isChain_reverse_symm hbt) (List.isChain_singleton a) ?_
    intro x hx y hy
    rw [List.getLast?_reverse] at hx
    simp only [List.head?_cons, Option.some.injEq] at hx hy
    subst hx; subst hy; exact hab.symm
lemma isSimplePath_reverse {α : Type*} {G : SimpleGraph α} {p : List α} {L : ℕ} {u w : α}
    (hp : IsSimplePath G p L u w) : IsSimplePath G p.reverse L w u := by
  rcases hp with ⟨hnd, hlen, hhead, hlast, hch⟩
  exact ⟨List.nodup_reverse.mpr hnd, by simp [hlen], by rwa [List.head?_reverse],
    by rwa [List.getLast?_reverse], isChain_reverse_symm hch⟩
lemma isSimplePath_append {α : Type*} {G : SimpleGraph α} {p1 p2 : List α} {L1 L2 : ℕ} {u v w : α}
    (hp1 : IsSimplePath G p1 L1 u v) (hp2 : IsSimplePath G p2 L2 v w)
    (hinter : ∀ x ∈ p1, x ∈ p2 → x = v) :
    IsSimplePath G (p1 ++ p2.tail) (L1 + L2) u w := by
  rcases hp1 with ⟨hnd1, hlen1, hh1, hl1, hch1⟩
  rcases hp2 with ⟨hnd2, hlen2, hh2, hl2, hch2⟩
  cases p2 with
  | nil => simp at hlen2
  | cons b t =>
    simp only [List.head?_cons, Option.some.injEq] at hh2
    subst hh2
    simp only [List.tail_cons]
    have hnd2' := List.nodup_cons.mp hnd2
    have hdisj : ∀ x ∈ p1, ∀ y ∈ t, x ≠ y := fun x hx1 y hyt hxy =>
      hnd2'.1 (hinter x hx1 (List.mem_cons_of_mem _ (hxy ▸ hyt)) ▸ (hxy ▸ hyt))
    refine ⟨List.nodup_append.mpr ⟨hnd1, hnd2'.2, hdisj⟩, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, hlen1]; simp only [List.length_cons] at hlen2; omega
    · cases p1 with
      | nil => simp at hlen1
      | cons a s => simpa using hh1
    · cases t with
      | nil =>
        have hbw : b = w := Option.some.inj hl2
        subst hbw; simpa using hl1
      | cons c r => simpa [List.getLast?_append] using hl2
    · cases t with
      | nil => simpa using hch1
      | cons c r =>
        have ⟨hbc, hcr⟩ := List.isChain_cons_cons.mp hch2
        refine isChain_append_of_last_head hch1 hcr fun x hx y hy => ?_
        have hxb : x = b := Option.some.inj (hx.symm.trans hl1)
        have hyc : y = c := Option.some.inj hy.symm
        subst hxb; subst hyc; exact hbc
lemma mem_append_tail_iff {α : Type*} {p1 p2 : List α} {x y : α} (hp2 : p2.head? = some y) (hy : y ∈ p1) :
    x ∈ p1 ++ p2.tail ↔ x ∈ p1 ∨ x ∈ p2 := by
  cases p2 with
  | nil => simp at hp2
  | cons b t =>
    simp only [List.head?_cons, Option.some.injEq] at hp2
    subst hp2
    simp only [List.tail_cons, List.mem_append, List.mem_cons]
    constructor
    · rintro (h | h); exact Or.inl h; exact Or.inr (Or.inr h)
    · rintro (h | rfl | h); exact Or.inl h; exact Or.inl hy; exact Or.inr h
lemma head_mem_of_isSimplePath {α : Type*} {G : SimpleGraph α} {p : List α} {L : ℕ} {u w : α}
    (hp : IsSimplePath G p L u w) : u ∈ p := List.mem_of_head? hp.2.2.1
lemma last_mem_of_isSimplePath {α : Type*} {G : SimpleGraph α} {p : List α} {L : ℕ} {u w : α}
    (hp : IsSimplePath G p L u w) : w ∈ p := List.mem_of_getLast? hp.2.2.2.1
set_option maxHeartbeats 600000 in
lemma luczak_bipartite_path {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {V1 V2 Forb : Finset α} {m L : ℕ} {δ d : ℝ}
    (hdisj : Disjoint V1 V2)
    (hV1 : V1.card = m) (hV2 : V2.card = m)
    (hδ0 : 0 < δ) (hd0 : 0 < d) (hd1 : d ≤ 1) (hδd : 12 * δ ≤ d ^ 2)
    (hm_big : 100 / δ ≤ (m : ℝ))
    (hunif : G.IsUniform δ V1 V2) (hdens : d ≤ (G.edgeDensity V1 V2 : ℝ))
    (hForb : (Forb.card : ℝ) ≤ δ * (m : ℝ))
    {u w : α} (hu : u ∈ V1) (huF : u ∉ Forb) (hw : w ∈ V2) (hwF : w ∉ Forb)
    (hdu : d / 2 * (m : ℝ) ≤ ((G.neighborFinset u ∩ V2).card : ℝ))
    (hdw : d / 2 * (m : ℝ) ≤ ((G.neighborFinset w ∩ V1).card : ℝ))
    (hL1 : 1 ≤ L) (hLmax : (L : ℝ) ≤ (1 - 6 * δ / d) * (m : ℝ)) :
    ∃ p : List α, IsSimplePath G p (2 * L + 1) u w ∧ ∀ x ∈ p, x ∈ V1 ∪ V2 ∧ x ∉ Forb := by
  let r : ℕ := Nat.ceil (δ * (m : ℝ))
  have hr_ge : δ * (m : ℝ) ≤ (r : ℝ) := Nat.le_ceil _
  have hr_le : (r : ℝ) ≤ δ * (m : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hδ_le_d : δ ≤ d / 12 := by nlinarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hm_big
  have h1_le_δm : 1 ≤ δ * (m : ℝ) / 100 := by have := (div_le_iff₀ hδ0).mp hm_big; linarith
  have hδ_le_δd : δ ≤ δ / d := le_div_self hδ0.le hd0 hd1
  have h1_le_δdm : 1 ≤ (δ / d) * (m : ℝ) / 100 := by
    have := mul_le_mul_of_nonneg_right hδ_le_δd hm_pos.le; linarith
  have hcand_R1 : r ≤ ((G.neighborFinset w ∩ V1) \ insert u Forb).card := by
    have hsub : (G.neighborFinset w ∩ V1) ⊆ ((G.neighborFinset w ∩ V1) \ insert u Forb) ∪ insert u Forb :=
      fun x hx => by by_cases h : x ∈ insert u Forb; exact mem_union_right _ h; exact mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 : (insert u Forb).card ≤ Forb.card + 1 := card_insert_le u Forb
    have h1r : ((G.neighborFinset w ∩ V1).card : ℝ) ≤
        (((G.neighborFinset w ∩ V1) \ insert u Forb).card : ℝ) + (Forb.card : ℝ) + 1 := by
      have : (G.neighborFinset w ∩ V1).card ≤ ((G.neighborFinset w ∩ V1) \ insert u Forb).card + Forb.card + 1 := by omega
      exact_mod_cast this
    have hgoal_r : (r : ℝ) ≤ (((G.neighborFinset w ∩ V1) \ insert u Forb).card : ℝ) := by nlinarith
    exact_mod_cast hgoal_r
  obtain ⟨R1, hR1_sub, hR1_card⟩ := exists_subset_card_eq hcand_R1
  have hR1_V1 : R1 ⊆ V1 := hR1_sub.trans (sdiff_subset.trans inter_subset_right)
  have hR1_nw : ∀ x ∈ R1, G.Adj w x := fun x hx =>
    (mem_neighborFinset G w x).mp (mem_inter.mp (Finset.mem_sdiff.mp (hR1_sub hx)).1).1
  have hR1_notF : ∀ x ∈ R1, x ∉ Forb := fun x hx hF =>
    (Finset.mem_sdiff.mp (hR1_sub hx)).2 (Finset.mem_insert_of_mem hF)
  have hR1_notu : u ∉ R1 := fun huR =>
    (Finset.mem_sdiff.mp (hR1_sub huR)).2 (Finset.mem_insert_self u Forb)
  have hbuild : ∀ j : ℕ, j ≤ L - 1 →
      ∃ (a : α) (p : List α),
        IsSimplePath G p (2 * j) u a ∧ a ∈ V1 ∧
        (p.toFinset ∩ V1).card ≤ j + 1 ∧ (p.toFinset ∩ V2).card ≤ j ∧
        (∀ x ∈ p, x ∈ V1 ∪ V2 ∧ x ∉ Forb ∧ x ∉ R1 ∧ x ≠ w) ∧
        δ * (m : ℝ) < ((G.neighborFinset a ∩ (V2 \ (Forb ∪ {w} ∪ p.toFinset))).card : ℝ) := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨u, [u], isSimplePath_singleton G u, hu,
        (card_le_card inter_subset_left).trans (by simp),
        by have : ({u} ∩ V2 : Finset α) = ∅ := disjoint_iff_inter_eq_empty.mp
             (disjoint_singleton_left.mpr (Finset.disjoint_left.mp hdisj hu)); simp [this],
        fun x hx => by
          rw [List.mem_singleton.mp hx]
          exact ⟨mem_union_left _ hu, huF, hR1_notu, fun h => Finset.disjoint_left.mp hdisj hu (h ▸ hw)⟩, ?_⟩
      have hsub : G.neighborFinset u ∩ V2 ⊆
          (G.neighborFinset u ∩ (V2 \ (Forb ∪ {w} ∪ [u].toFinset))) ∪ (Forb ∪ ({w, u} : Finset α)) := by
        intro x hx
        by_cases h1 : x ∈ Forb
        · exact mem_union_right _ (mem_union_left _ h1)
        · by_cases h2 : x = w
          · exact mem_union_right _ (mem_union_right _ (by simp [h2]))
          · by_cases h3 : x = u
            · exact mem_union_right _ (mem_union_right _ (by simp [h3]))
            · refine mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hx).1,
                Finset.mem_sdiff.mpr ⟨(mem_inter.mp hx).2, by simp [h1, h2, h3]⟩⟩)
      have hle := (card_le_card hsub).trans (card_union_le _ _)
      have hF2 : (Forb ∪ ({w, u} : Finset α)).card ≤ Forb.card + 2 :=
        (card_union_le _ _).trans (Nat.add_le_add_left ((card_insert_le _ _).trans (by simp)) _)
      have hcard_r : ((G.neighborFinset u ∩ V2).card : ℝ) ≤
          ((G.neighborFinset u ∩ (V2 \ (Forb ∪ {w} ∪ [u].toFinset))).card : ℝ) + (Forb.card : ℝ) + 2 := by
        have : (G.neighborFinset u ∩ V2).card ≤
            (G.neighborFinset u ∩ (V2 \ (Forb ∪ {w} ∪ [u].toFinset))).card + Forb.card + 2 := by omega
        exact_mod_cast this
      nlinarith
    | succ j ih =>
      obtain ⟨a, p, hp, haV1, hpV1, hpV2, hp_ok, hda⟩ := ih (Nat.le_of_succ_le hj)
      let used : Finset α := p.toFinset
      let U1 : Finset α := V1 \ (R1 ∪ Forb ∪ used)
      let U2 : Finset α := V2 \ (Forb ∪ {w} ∪ used)
      have hj_le_L : (j : ℝ) + 1 ≤ (1 - 6 * δ / d) * (m : ℝ) := by
        have h : ((j + 1 : ℕ) : ℝ) ≤ (1 - 6 * δ / d) * (m : ℝ) :=
          (Nat.cast_le.mpr (show j + 1 ≤ L by omega)).trans hLmax
        push_cast at h; exact h
      have hδm_le : δ * (m : ℝ) ≤ (δ / d) * (m : ℝ) := mul_le_mul_of_nonneg_right hδ_le_δd hm_pos.le
      have hU1_card : (35 / 10 : ℝ) * (δ / d) * (m : ℝ) ≤ (U1.card : ℝ) := by
        have hsub : V1 ⊆ U1 ∪ R1 ∪ Forb ∪ (used ∩ V1) := by
          intro x hx
          by_cases h1 : x ∈ R1
          · exact mem_union_left _ (mem_union_left _ (mem_union_right _ h1))
          · by_cases h2 : x ∈ Forb
            · exact mem_union_left _ (mem_union_right _ h2)
            · by_cases h3 : x ∈ used
              · exact mem_union_right _ (mem_inter.mpr ⟨h3, hx⟩)
              · exact mem_union_left _ (mem_union_left _ (mem_union_left _
                  (Finset.mem_sdiff.mpr ⟨hx, by simp [h1, h2, h3]⟩)))
        have hle := (card_le_card hsub).trans ((card_union_le _ _).trans
          (Nat.add_le_add_right ((card_union_le _ _).trans
            (Nat.add_le_add_right (card_union_le _ _) _)) _))
        rw [hV1, hR1_card] at hle
        have hpV1' : (used ∩ V1).card ≤ j + 1 := hpV1
        have hler : (m : ℝ) ≤ (U1.card : ℝ) + (r : ℝ) + (Forb.card : ℝ) + ((j + 1 : ℕ) : ℝ) := by
          have : m ≤ U1.card + r + Forb.card + (j + 1) := by omega
          exact_mod_cast this
        rw [Nat.cast_add, Nat.cast_one] at hler
        have h6 : (1 - 6 * δ / d) * (m : ℝ) = (m : ℝ) - 6 * ((δ / d) * (m : ℝ)) := by ring
        linarith [hδm_le, h1_le_δdm, hr_le, hForb, hj_le_L, h6, hler]
      have hU2_card : (35 / 10 : ℝ) * (δ / d) * (m : ℝ) + 1 ≤ (U2.card : ℝ) := by
        have hsub : V2 ⊆ U2 ∪ Forb ∪ {w} ∪ (used ∩ V2) := by
          intro x hx
          by_cases h1 : x ∈ Forb
          · exact mem_union_left _ (mem_union_left _ (mem_union_right _ h1))
          · by_cases h2 : x = w
            · exact mem_union_left _ (mem_union_right _ (mem_singleton.mpr h2))
            · by_cases h3 : x ∈ used
              · exact mem_union_right _ (mem_inter.mpr ⟨h3, hx⟩)
              · exact mem_union_left _ (mem_union_left _ (mem_union_left _
                  (Finset.mem_sdiff.mpr ⟨hx, by simp [h1, h2, h3]⟩)))
        have hle := (card_le_card hsub).trans ((card_union_le _ _).trans
          (Nat.add_le_add_right ((card_union_le _ _).trans
            (Nat.add_le_add_right (card_union_le _ _) _)) _))
        rw [hV2, card_singleton] at hle
        have hpV2' : (used ∩ V2).card ≤ j := hpV2
        have hler : (m : ℝ) ≤ (U2.card : ℝ) + (Forb.card : ℝ) + 1 + (j : ℝ) := by
          have : m ≤ U2.card + Forb.card + 1 + j := by omega
          exact_mod_cast this
        have h6 : (1 - 6 * δ / d) * (m : ℝ) = (m : ℝ) - 6 * ((δ / d) * (m : ℝ)) := by ring
        linarith [hδm_le, h1_le_δdm, hForb, hj_le_L, h6, hler]
      have hU1_ge_δm : (V1.card : ℝ) * δ ≤ (U1.card : ℝ) := by rw [hV1]; nlinarith [hδ_le_δd, hm_pos]
      let Bad2 := V2.filter (fun b => ((G.neighborFinset b ∩ U1).card : ℝ) <
        ((G.edgeDensity V2 V1 : ℝ) - δ) * (U1.card : ℝ))
      have hBad2_le : (Bad2.card : ℝ) ≤ δ * (m : ℝ) := by
        have h := typical_degree_bound_le G hunif.symm (sdiff_subset : U1 ⊆ V1) hU1_ge_δm
        rw [hV2] at h; linarith
      have hcand_b : ((G.neighborFinset a ∩ U2) \ Bad2).Nonempty := by
        rw [nonempty_iff_ne_empty]; intro hemp
        have hler : ((G.neighborFinset a ∩ U2).card : ℝ) ≤ (Bad2.card : ℝ) := by
          exact_mod_cast card_le_card (sdiff_eq_empty_iff_subset.mp hemp)
        linarith
      obtain ⟨b, hb⟩ := hcand_b
      rw [Finset.mem_sdiff, mem_inter, mem_neighborFinset] at hb
      have hbV2 : b ∈ V2 := (Finset.mem_sdiff.mp hb.1.2).1
      have hb_notF : b ∉ Forb := fun h => (Finset.mem_sdiff.mp hb.1.2).2 (mem_union_left _ (mem_union_left _ h))
      have hb_new : b ≠ w := fun h => (Finset.mem_sdiff.mp hb.1.2).2 (mem_union_left _ (mem_union_right _ (mem_singleton.mpr h)))
      have hb_notp : b ∉ p := fun h => (Finset.mem_sdiff.mp hb.1.2).2 (mem_union_right _ (List.mem_toFinset.mpr h))
      have hb_notR1 : b ∉ R1 := fun h => Finset.disjoint_left.mp hdisj (hR1_V1 h) hbV2
      have hdb : δ * (m : ℝ) < ((G.neighborFinset b ∩ U1).card : ℝ) := by
        have hge : ((G.edgeDensity V2 V1 : ℝ) - δ) * (U1.card : ℝ) ≤ ((G.neighborFinset b ∩ U1).card : ℝ) := by
          by_contra hlt; push Not at hlt; exact hb.2 (mem_filter.mpr ⟨hbV2, hlt⟩)
        have hd_symm : d ≤ (G.edgeDensity V2 V1 : ℝ) := by rwa [edgeDensity_comm]
        have hdd : (d - δ) * ((35 / 10 : ℝ) * (δ / d) * (m : ℝ)) = (35 / 10 : ℝ) * (1 - δ / d) * (δ * (m : ℝ)) := by field_simp
        have hmul := mul_le_mul (show d - δ ≤ (G.edgeDensity V2 V1 : ℝ) - δ by linarith) hU1_card (by positivity) (by linarith)
        have hδdiv : δ / d ≤ 1 / 12 := by rw [div_le_iff₀ hd0]; linarith
        nlinarith [mul_pos hδ0 hm_pos]
      let U2' : Finset α := U2.erase b
      have hU2'_card : (35 / 10 : ℝ) * (δ / d) * (m : ℝ) ≤ (U2'.card : ℝ) := by
        have h1 : U2'.card + 1 = U2.card := by
          rw [card_erase_of_mem hb.1.2]; exact Nat.sub_add_cancel (card_pos.mpr ⟨b, hb.1.2⟩)
        have h1r : (U2'.card : ℝ) + 1 = (U2.card : ℝ) := by exact_mod_cast h1
        linarith
      have hU2'_ge_δm : (V2.card : ℝ) * δ ≤ (U2'.card : ℝ) := by rw [hV2]; nlinarith [hδ_le_δd, hm_pos]
      let Bad1 := V1.filter (fun a' => ((G.neighborFinset a' ∩ U2').card : ℝ) <
        ((G.edgeDensity V1 V2 : ℝ) - δ) * (U2'.card : ℝ))
      have hBad1_le : (Bad1.card : ℝ) ≤ δ * (m : ℝ) := by
        have h := typical_degree_bound_le G hunif ((Finset.erase_subset b U2).trans sdiff_subset) hU2'_ge_δm
        rw [hV1] at h; linarith
      have hcand_a' : ((G.neighborFinset b ∩ U1) \ Bad1).Nonempty := by
        rw [nonempty_iff_ne_empty]; intro hemp
        have hler : ((G.neighborFinset b ∩ U1).card : ℝ) ≤ (Bad1.card : ℝ) := by
          exact_mod_cast card_le_card (sdiff_eq_empty_iff_subset.mp hemp)
        linarith
      obtain ⟨a', ha'⟩ := hcand_a'
      rw [Finset.mem_sdiff, mem_inter, mem_neighborFinset] at ha'
      have ha'V1 : a' ∈ V1 := (Finset.mem_sdiff.mp ha'.1.2).1
      have ha'_notR1 : a' ∉ R1 := fun h => (Finset.mem_sdiff.mp ha'.1.2).2 (mem_union_left _ (mem_union_left _ h))
      have ha'_notF : a' ∉ Forb := fun h => (Finset.mem_sdiff.mp ha'.1.2).2 (mem_union_left _ (mem_union_right _ h))
      have ha'_notp : a' ∉ p := fun h => (Finset.mem_sdiff.mp ha'.1.2).2 (mem_union_right _ (List.mem_toFinset.mpr h))
      have ha'_new : a' ≠ w := fun h => Finset.disjoint_left.mp hdisj ha'V1 (h ▸ hw)
      have ha'_neb : a' ≠ b := fun h => Finset.disjoint_left.mp hdisj ha'V1 (h ▸ hbV2)
      have hda' : δ * (m : ℝ) < ((G.neighborFinset a' ∩ U2').card : ℝ) := by
        have hge : ((G.edgeDensity V1 V2 : ℝ) - δ) * (U2'.card : ℝ) ≤ ((G.neighborFinset a' ∩ U2').card : ℝ) := by
          by_contra hlt; push Not at hlt; exact ha'.2 (mem_filter.mpr ⟨ha'V1, hlt⟩)
        have hdd : (d - δ) * ((35 / 10 : ℝ) * (δ / d) * (m : ℝ)) = (35 / 10 : ℝ) * (1 - δ / d) * (δ * (m : ℝ)) := by field_simp
        have hmul := mul_le_mul (show d - δ ≤ (G.edgeDensity V1 V2 : ℝ) - δ by linarith) hU2'_card (by positivity) (by linarith)
        have hδdiv : δ / d ≤ 1 / 12 := by rw [div_le_iff₀ hd0]; linarith
        nlinarith [mul_pos hδ0 hm_pos]
      have hseg : IsSimplePath G [a, b, a'] 2 a a' :=
        isSimplePath_cons (isSimplePath_cons (isSimplePath_singleton G a') ha'.1.1 (by simp [ha'_neb.symm]))
          hb.1.1 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨G.ne_of_adj hb.1.1, fun h => ha'_notp (h ▸ last_mem_of_isSimplePath hp)⟩)
      have hp' := isSimplePath_append hp hseg fun x hxp hx3 => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx3
        rcases hx3 with rfl | rfl | rfl
        · rfl
        · exact absurd hxp hb_notp
        · exact absurd hxp ha'_notp
      have hp'_eq : p ++ [a, b, a'].tail = p ++ [b, a'] := rfl
      rw [hp'_eq] at hp'
      have hU2'_eq : U2' = V2 \ (Forb ∪ {w} ∪ (p ++ [b, a']).toFinset) := by
        ext x
        simp only [U2', U2, used, mem_erase, Finset.mem_sdiff, mem_union,
          mem_singleton, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨hxb, hxV2, hnot⟩
          refine ⟨hxV2, fun h => ?_⟩
          rcases h with (hF | hxw) | (hxp | rfl | rfl)
          · exact hnot (Or.inl (Or.inl hF))
          · exact hnot (Or.inl (Or.inr hxw))
          · exact hnot (Or.inr hxp)
          · exact hxb rfl
          · exact Finset.disjoint_left.mp hdisj ha'V1 hxV2
        · rintro ⟨hxV2, hnot⟩
          exact ⟨fun h => hnot (Or.inr (Or.inr (Or.inl h))), hxV2, fun h => by
            rcases h with (hF | hxw) | hxp
            · exact hnot (Or.inl (Or.inl hF))
            · exact hnot (Or.inl (Or.inr hxw))
            · exact hnot (Or.inr (Or.inl hxp))⟩
      refine ⟨a', p ++ [b, a'], by simpa [Nat.mul_succ] using hp', ha'V1, ?_, ?_, fun x hx => ?_, hU2'_eq ▸ hda'⟩
      · have hsub : (p ++ [b, a']).toFinset ∩ V1 ⊆ insert a' (p.toFinset ∩ V1) := by
          intro x hx
          simp only [mem_inter, List.mem_toFinset, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, mem_insert] at hx ⊢
          rcases hx.1 with hxp | rfl | rfl
          · exact Or.inr ⟨hxp, hx.2⟩
          · exact absurd hx.2 (Finset.disjoint_right.mp hdisj hbV2)
          · exact Or.inl rfl
        exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by omega))
      · have hsub : (p ++ [b, a']).toFinset ∩ V2 ⊆ insert b (p.toFinset ∩ V2) := by
          intro x hx
          simp only [mem_inter, List.mem_toFinset, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, mem_insert] at hx ⊢
          rcases hx.1 with hxp | rfl | rfl
          · exact Or.inr ⟨hxp, hx.2⟩
          · exact Or.inl rfl
          · exact absurd hx.2 (Finset.disjoint_left.mp hdisj ha'V1)
        exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by omega))
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hxp | rfl | rfl
        · exact hp_ok x hxp
        · exact ⟨mem_union_right _ hbV2, hb_notF, hb_notR1, hb_new⟩
        · exact ⟨mem_union_left _ ha'V1, ha'_notF, ha'_notR1, ha'_new⟩
  obtain ⟨a, p, hp, haV1, _, _, hp_ok, hda⟩ := hbuild (L - 1) (le_refl _)
  let Y : Finset α := G.neighborFinset a ∩ (V2 \ (Forb ∪ {w} ∪ p.toFinset))
  have hY_V2 : Y ⊆ V2 := inter_subset_right.trans sdiff_subset
  have hR1_big : (V1.card : ℝ) * δ ≤ (R1.card : ℝ) := by rw [hV1, hR1_card]; linarith
  have hY_big : (V2.card : ℝ) * δ ≤ (Y.card : ℝ) := by rw [hV2]; linarith
  have hdev := hunif hR1_V1 hY_V2 hR1_big hY_big
  rw [abs_lt] at hdev
  have hd_pos : (0 : ℝ) < (G.edgeDensity R1 Y : ℝ) := by linarith
  have hinter_ne : (G.interedges R1 Y).Nonempty := by
    by_contra hemp; rw [not_nonempty_iff_eq_empty] at hemp
    have : (G.edgeDensity R1 Y : ℝ) = 0 := by simp [edgeDensity_def, hemp]
    linarith
  obtain ⟨⟨a_last, b_last⟩, hab⟩ := hinter_ne
  rw [mem_interedges_iff] at hab
  rcases hab with ⟨haR1, hbY, hadj_ab⟩
  have hb_adj_a : G.Adj a b_last := (mem_neighborFinset G a b_last).mp (mem_inter.mp hbY).1
  have hb_sdiff := Finset.mem_sdiff.mp (mem_inter.mp hbY).2
  have hbV2 : b_last ∈ V2 := hb_sdiff.1
  have hb_notF : b_last ∉ Forb := fun h => hb_sdiff.2 (mem_union_left _ (mem_union_left _ h))
  have hb_new : b_last ≠ w := fun h => hb_sdiff.2 (mem_union_left _ (mem_union_right _ (mem_singleton.mpr h)))
  have hb_notp : b_last ∉ p := fun h => hb_sdiff.2 (mem_union_right _ (List.mem_toFinset.mpr h))
  have ha_last_V1 : a_last ∈ V1 := hR1_V1 haR1
  have ha_last_notF : a_last ∉ Forb := hR1_notF a_last haR1
  have ha_last_new : a_last ≠ w := fun h => Finset.disjoint_left.mp hdisj ha_last_V1 (h ▸ hw)
  have ha_last_neb : a_last ≠ b_last := fun h => Finset.disjoint_left.mp hdisj ha_last_V1 (h ▸ hbV2)
  have ha_last_notp : a_last ∉ p := fun h => (hp_ok a_last h).2.2.1 haR1
  have hw_notp : w ∉ p := fun h => (hp_ok w h).2.2.2 rfl
  have htail : IsSimplePath G [a, b_last, a_last, w] 3 a w :=
    isSimplePath_cons
      (isSimplePath_cons
        (isSimplePath_cons (isSimplePath_singleton G w) (hR1_nw a_last haR1).symm (by simp [ha_last_new]))
        hadj_ab.symm (by simp [ha_last_neb.symm, hb_new]))
      hb_adj_a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨G.ne_of_adj hb_adj_a, fun h => ha_last_notp (h ▸ last_mem_of_isSimplePath hp),
          fun h => hw_notp (h ▸ last_mem_of_isSimplePath hp)⟩)
  have hfin := isSimplePath_append hp htail fun x hxp hx4 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx4
    rcases hx4 with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hxp hb_notp
    · exact absurd hxp ha_last_notp
    · exact absurd hxp hw_notp
  have hlen_eq : 2 * (L - 1) + 3 = 2 * L + 1 := by omega
  rw [hlen_eq] at hfin
  refine ⟨p ++ [b_last, a_last, w], hfin, fun x hx => ?_⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxp | rfl | rfl | rfl
  · exact ⟨(hp_ok x hxp).1, (hp_ok x hxp).2.1⟩
  · exact ⟨mem_union_right _ hbV2, hb_notF⟩
  · exact ⟨mem_union_left _ ha_last_V1, ha_last_notF⟩
  · exact ⟨mem_union_right _ hw, hwF⟩
lemma realize_walk_to_good {α : Type*} [Fintype α] [DecidableEq α] {t m : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (V : Fin t → Finset α) (R : SimpleGraph (Fin t))
    {δ d : ℝ} (hδ0 : 0 < δ) (hd0 : 0 < d) (hδd : 12 * δ ≤ d ^ 2) (hd1 : d ≤ 1)
    (hVcard : ∀ i : Fin t, (V i).card = m)
    (hReg : ∀ i j : Fin t, R.Adj i j → G.IsUniform δ (V i) (V j) ∧ d ≤ (G.edgeDensity (V i) (V j) : ℝ))
    {c0 clast : Fin t} (W : R.Walk c0 clast) :
    ∀ (S0 Bad_last Used : Finset α),
      S0 ⊆ V c0 → (d / 4) * (m : ℝ) ≤ (S0.card : ℝ) →
      (Bad_last.card : ℝ) ≤ δ * (m : ℝ) →
      (Used.card : ℝ) + (W.length : ℝ) + 1 ≤ (δ / 2) * (m : ℝ) →
      ∃ (v0 vlast : α) (p : List α),
        IsSimplePath G p W.length v0 vlast ∧
        v0 ∈ S0 ∧ vlast ∈ V clast ∧ vlast ∉ Bad_last ∧ ∀ x ∈ p, x ∉ Used := by
  have hδ_le_d : δ ≤ d / 12 := by nlinarith
  induction W with
  | nil =>
    intro S0 Bad_last Used hS0 hS0c hBadc hUsed
    have hcand : (S0 \ (Used ∪ Bad_last)).Nonempty := by
      rw [nonempty_iff_ne_empty]; intro hemp
      have hler : (S0.card : ℝ) ≤ (Used.card : ℝ) + (Bad_last.card : ℝ) := by
        exact_mod_cast (card_le_card (sdiff_eq_empty_iff_subset.mp hemp)).trans (card_union_le _ _)
      have hm_pos : (0 : ℝ) < (m : ℝ) := by
        have : (0 : ℝ) < (δ / 2) * (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) Used.card]
        nlinarith
      nlinarith
    obtain ⟨v0, hv0⟩ := hcand
    rw [Finset.mem_sdiff, mem_union] at hv0
    refine ⟨v0, v0, [v0], isSimplePath_singleton G v0, hv0.1, hS0 hv0.1,
      fun h => hv0.2 (Or.inr h), fun x hx h => hv0.2 (Or.inl (List.mem_singleton.mp hx ▸ h))⟩
  | @cons a b c hab W' ih =>
    intro S0 Bad_last Used hS0 hS0c hBadc hUsed
    obtain ⟨hunif, hdens⟩ := hReg a b hab
    let Bad_step := (V a).filter (fun u => ((G.neighborFinset u ∩ V b).card : ℝ) <
      ((G.edgeDensity (V a) (V b) : ℝ) - δ) * ((V b).card : ℝ))
    have hBad_step : (Bad_step.card : ℝ) ≤ δ * (m : ℝ) := by
      have h := typical_degree_bound_le G hunif (Finset.Subset.refl (V b))
        (by rw [hVcard b]; nlinarith [Nat.cast_nonneg (α := ℝ) m])
      rw [hVcard a] at h; linarith
    have hcand : (S0 \ (Used ∪ Bad_step)).Nonempty := by
      rw [nonempty_iff_ne_empty]; intro hemp
      have hler : (S0.card : ℝ) ≤ (Used.card : ℝ) + (Bad_step.card : ℝ) := by
        exact_mod_cast (card_le_card (sdiff_eq_empty_iff_subset.mp hemp)).trans (card_union_le _ _)
      have hm_pos : (0 : ℝ) < (m : ℝ) := by
        have : (0 : ℝ) < (δ / 2) * (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) Used.card]
        nlinarith
      simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one] at hUsed
      nlinarith
    obtain ⟨v0, hv0⟩ := hcand
    rw [Finset.mem_sdiff, mem_union] at hv0
    have hv0_deg : (d / 4) * (m : ℝ) ≤ ((G.neighborFinset v0 ∩ V b).card : ℝ) := by
      have hge : ((G.edgeDensity (V a) (V b) : ℝ) - δ) * ((V b).card : ℝ) ≤ ((G.neighborFinset v0 ∩ V b).card : ℝ) := by
        by_contra hlt; push Not at hlt; exact hv0.2 (Or.inr (mem_filter.mpr ⟨hS0 hv0.1, hlt⟩))
      rw [hVcard b] at hge; nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hUsed' : ((insert v0 Used).card : ℝ) + (W'.length : ℝ) + 1 ≤ (δ / 2) * (m : ℝ) := by
      have h1r : ((insert v0 Used).card : ℝ) ≤ (Used.card : ℝ) + 1 := by exact_mod_cast card_insert_le v0 Used
      simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one] at hUsed
      linarith
    obtain ⟨v1, vlast, p', hp', hv1S, hvlastV, hvlastBad, hp'_out⟩ :=
      ih (G.neighborFinset v0 ∩ V b) Bad_last (insert v0 Used) inter_subset_right hv0_deg hBadc hUsed'
    have hv0_adj_v1 : G.Adj v0 v1 := (mem_neighborFinset G v0 v1).mp (mem_inter.mp hv1S).1
    have hv0_notp' : v0 ∉ p' := fun h => hp'_out v0 h (Finset.mem_insert_self v0 Used)
    refine ⟨v0, vlast, v0 :: p', isSimplePath_cons hp' hv0_adj_v1 hv0_notp', hv0.1, hvlastV, hvlastBad,
      fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hxp'
    · exact fun h => hv0.2 (Or.inl h)
    · exact fun h => hp'_out x hxp' (Finset.mem_insert_of_mem h)
lemma exists_bounded_sum_decomp (s M T : ℕ) (hlo : s ≤ T) (hhi : T ≤ s * M) :
    ∃ L : Fin s → ℕ, (∀ r, 1 ≤ L r ∧ L r ≤ M) ∧ ∑ r : Fin s, L r = T := by
  induction s generalizing T with
  | zero =>
    have hT0 : T = 0 := by omega
    exact ⟨fun r => Fin.elim0 r, fun r => Fin.elim0 r, by simp [hT0]⟩
  | succ s ih =>
    have hM1 : 1 ≤ M := by nlinarith
    let x : ℕ := min M (T - s)
    have hx1 : 1 ≤ x := by dsimp only [x]; omega
    have hxM : x ≤ M := min_le_left _ _
    have hrem_lo : s ≤ T - x := by dsimp only [x]; omega
    have hrem_hi : T - x ≤ s * M := by
      have hsM : s ≤ s * M := Nat.le_mul_of_pos_right s hM1
      dsimp only [x]; rw [Nat.succ_mul] at hhi; simp only [min_def]; split_ifs <;> omega
    obtain ⟨L', hL'b, hL's⟩ := ih (T - x) hrem_lo hrem_hi
    refine ⟨Fin.cons x L', fun r => Fin.cases ⟨hx1, hxM⟩ hL'b r, ?_⟩
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [hL's]; dsimp only [x]; omega
set_option maxHeartbeats 800000 in
lemma luczak_path_through_matching {α : Type*} [Fintype α] [DecidableEq α] {t m s : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (V : Fin t → Finset α) (R : SimpleGraph (Fin t))
    {δ d : ℝ} (hδ0 : 0 < δ) (hd0 : 0 < d) (hd1 : d ≤ 1) (hδd : 12 * δ ≤ d ^ 2)
    (hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j))
    (hVcard : ∀ i : Fin t, (V i).card = m)
    (hReg : ∀ i j : Fin t, R.Adj i j → G.IsUniform δ (V i) (V j) ∧ d ≤ (G.edgeDensity (V i) (V j) : ℝ))
    (hs1 : 1 ≤ s) (A B : Fin s → Fin t)
    (hAB_adj : ∀ r : Fin s, R.Adj (A r) (B r))
    (hA_inj : Function.Injective A) (hB_inj : Function.Injective B)
    (hAB_ne : ∀ r1 r2 : Fin s, A r1 ≠ B r2)
    {c_start c_end : Fin t}
    (P_start : R.Walk c_start (A ⟨0, hs1⟩))
    (P_mid : ∀ r : Fin (s - 1), R.Walk (B ⟨r.val, by omega⟩) (A ⟨r.val + 1, by omega⟩))
    (P_end : R.Walk (B ⟨s - 1, by omega⟩) c_end)
    {S_start S_end Forb : Finset α}
    (hSs_sub : S_start ⊆ V c_start) (hSs_card : (d / 4) * (m : ℝ) ≤ (S_start.card : ℝ))
    (hSe_sub : S_end ⊆ V c_end) (hSe_card : (d / 4) * (m : ℝ) ≤ (S_end.card : ℝ))
    (hForb : Forb.card ≤ 2)
    (hm_big : (4 * ((P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s + 10 : ℕ) : ℝ) + 100) / δ ≤ (m : ℝ))
    {L : ℕ}
    (hL_par : L % 2 = (P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s) % 2)
    (hL_lo : P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + 3 * s ≤ L)
    (hL_hi : L ≤ P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s +
        2 * s * Nat.floor ((1 - 6 * δ / d) * (m : ℝ))) :
    ∃ (v_start v_end : α) (p : List α),
      IsSimplePath G p L v_start v_end ∧ v_start ∈ S_start ∧ v_end ∈ S_end ∧ ∀ x ∈ p, x ∉ Forb := by
  let L_sk : ℕ := P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length
  let cap_used : ℕ := L_sk + s + 10
  have hcap_le : (cap_used : ℝ) ≤ (δ / 4) * (m : ℝ) := by
    have h1 := (div_le_iff₀ hδ0).mp hm_big; dsimp only [cap_used, L_sk] at h1 ⊢; linarith
  have hm_100 : 100 / δ ≤ (m : ℝ) := by
    have h1 := (div_le_iff₀ hδ0).mp hm_big; rw [div_le_iff₀ hδ0]
    linarith [Nat.cast_nonneg (α := ℝ) (P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s + 10)]
  let BadOf : ∀ i j : Fin t, Finset α := fun i j =>
    (V i).filter (fun u => ((G.neighborFinset u ∩ V j).card : ℝ) < (d / 2) * (m : ℝ))
  have hBadOf_le : ∀ i j : Fin t, R.Adj i j → ((BadOf i j).card : ℝ) ≤ δ * (m : ℝ) := by
    intro i j hij
    obtain ⟨hunif, hdens⟩ := hReg i j hij
    have hδ_le_d : δ ≤ d / 12 := by nlinarith
    have hsub : BadOf i j ⊆ (V i).filter (fun u => ((G.neighborFinset u ∩ V j).card : ℝ) <
        ((G.edgeDensity (V i) (V j) : ℝ) - δ) * ((V j).card : ℝ)) := fun u hu => by
      rw [mem_filter] at hu ⊢
      exact ⟨hu.1, lt_of_lt_of_le hu.2 (by rw [hVcard j]; nlinarith [Nat.cast_nonneg (α := ℝ) m])⟩
    have h1 : ((BadOf i j).card : ℝ) ≤
        (((V i).filter (fun u => ((G.neighborFinset u ∩ V j).card : ℝ) <
          ((G.edgeDensity (V i) (V j) : ℝ) - δ) * ((V j).card : ℝ))).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have h2 := typical_degree_bound_le G hunif (Finset.Subset.refl (V j))
      (by rw [hVcard j]; nlinarith [Nat.cast_nonneg (α := ℝ) m])
    rw [hVcard i] at h2; linarith
  have hU0 : (Forb.card : ℝ) + (P_start.length : ℝ) + 1 ≤ (δ / 2) * (m : ℝ) := by
    have : (Forb.card : ℝ) + (P_start.length : ℝ) + 1 ≤ (cap_used : ℝ) := by
      exact_mod_cast (show Forb.card + P_start.length + 1 ≤ cap_used by dsimp only [cap_used, L_sk]; omega)
    linarith [hcap_le]
  obtain ⟨v_start, u0, p_start, hp_start, hv_start_S, hu0_V, hu0_good, hp_start_out⟩ :=
    realize_walk_to_good G V R hδ0 hd0 hδd hd1 hVcard hReg P_start
      S_start (BadOf (A ⟨0, hs1⟩) (B ⟨0, hs1⟩)) Forb
      hSs_sub hSs_card (hBadOf_le _ _ (hAB_adj ⟨0, hs1⟩)) hU0
  let Used1 : Finset α := Forb ∪ p_start.toFinset
  have hUsed1_card : Used1.card ≤ Forb.card + (P_start.length + 1) :=
    (card_union_le _ _).trans (Nat.add_le_add_left (List.toFinset_card_le p_start |>.trans (by rw [hp_start.2.1])) _)
  have hU1 : (Used1.card : ℝ) + (P_end.reverse.length : ℝ) + 1 ≤ (δ / 2) * (m : ℝ) := by
    rw [Walk.length_reverse]
    have : (Used1.card : ℝ) + (P_end.length : ℝ) + 1 ≤ (cap_used : ℝ) := by
      exact_mod_cast (show Used1.card + P_end.length + 1 ≤ cap_used by dsimp only [cap_used, L_sk]; omega)
    linarith [hcap_le]
  obtain ⟨v_end, w_last, p_end_rev, hp_end_rev, hv_end_S, hw_last_V, hw_last_good, hp_end_rev_out⟩ :=
    realize_walk_to_good G V R hδ0 hd0 hδd hd1 hVcard hReg P_end.reverse
      S_end (BadOf (B ⟨s - 1, by omega⟩) (A ⟨s - 1, by omega⟩)) Used1
      hSe_sub hSe_card (hBadOf_le _ _ (hAB_adj ⟨s - 1, by omega⟩).symm) hU1
  let p_end : List α := p_end_rev.reverse
  have hp_end : IsSimplePath G p_end P_end.length w_last v_end := by
    have := isSimplePath_reverse hp_end_rev
    rwa [Walk.length_reverse] at this
  have hp_end_out : ∀ x ∈ p_end, x ∉ Used1 := fun x hx => hp_end_rev_out x (List.mem_reverse.mp hx)
  let Used2 : Finset α := Used1 ∪ p_end.toFinset
  have hUsed2_card : Used2.card ≤ Forb.card + P_start.length + P_end.length + 2 := by
    have h1 : Used2.card ≤ Used1.card + p_end.toFinset.card := card_union_le Used1 p_end.toFinset
    have h2 : p_end.toFinset.card ≤ P_end.length + 1 := (List.toFinset_card_le p_end).trans (by rw [hp_end.2.1])
    omega
  have hmid_build : ∀ (j : ℕ) (hj : j ≤ s - 1),
      ∃ (W_v U_v : Fin j → α) (P_m : Fin j → List α),
        (∀ r : Fin j, IsSimplePath G (P_m r) (P_mid ⟨r.val, by omega⟩).length (W_v r) (U_v r)) ∧
        (∀ r : Fin j, W_v r ∈ V (B ⟨r.val, by omega⟩) ∧ W_v r ∉ BadOf (B ⟨r.val, by omega⟩) (A ⟨r.val, by omega⟩)) ∧
        (∀ r : Fin j, U_v r ∈ V (A ⟨r.val + 1, by omega⟩) ∧ U_v r ∉ BadOf (A ⟨r.val + 1, by omega⟩) (B ⟨r.val + 1, by omega⟩)) ∧
        (∀ r : Fin j, ∀ x ∈ P_m r, x ∉ Used2) ∧
        (∀ r1 r2 : Fin j, r1 ≠ r2 → ∀ x ∈ P_m r1, x ∉ P_m r2) := by
    intro j hj
    induction j with
    | zero =>
      exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun r => Fin.elim0 r, fun r => Fin.elim0 r,
        fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩
    | succ j ih =>
      obtain ⟨W_v, U_v, P_m, hPsp, hWok, hUok, hOut2, hPdisj⟩ := ih (Nat.le_of_succ_le hj)
      let Used_prev : Finset α := Used2 ∪ (Finset.univ : Finset (Fin j)).biUnion (fun r => (P_m r).toFinset)
      have hUsed_prev_card : Used_prev.card ≤ Forb.card + P_start.length + P_end.length + 2 +
          ∑ r : Fin j, ((P_mid ⟨r.val, by omega⟩).length + 1) := by
        refine (card_union_le _ _).trans (Nat.add_le_add hUsed2_card ?_)
        refine card_biUnion_le.trans (sum_le_sum fun r _ => ?_)
        exact (List.toFinset_card_le _).trans (hPsp r).2.1.le
      have hsum_le : (∑ r : Fin j, (P_mid ⟨r.val, by omega⟩).length) + (P_mid ⟨j, by omega⟩).length ≤
          ∑ r : Fin (s - 1), (P_mid r).length := by
        let subS : Finset (Fin (s - 1)) := Finset.univ.filter (fun r : Fin (s - 1) => r.val ≤ j)
        have h1 : (∑ r : Fin j, (P_mid ⟨r.val, by omega⟩).length) + (P_mid ⟨j, by omega⟩).length =
            ∑ r ∈ subS, (P_mid r).length := by
          let subLt : Finset (Fin (s - 1)) := Finset.univ.filter (fun r : Fin (s - 1) => r.val < j)
          have hsplit : subS = insert ⟨j, by omega⟩ subLt := by
            ext r; simp only [subS, subLt, mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
          have hnot : (⟨j, by omega⟩ : Fin (s - 1)) ∉ subLt := by simp [subLt]
          rw [hsplit, sum_insert hnot, add_comm]
          congr 1
          refine sum_bij (fun (r : Fin j) _ => (⟨r.val, by omega⟩ : Fin (s - 1)))
            (fun r _ => mem_filter.mpr ⟨mem_univ _, r.isLt⟩)
            (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
            (fun r hr => ⟨⟨r.val, (mem_filter.mp hr).2⟩, mem_univ _, Fin.ext rfl⟩)
            (fun _ _ => rfl)
        rw [h1]; exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      have hUsed_le : (Used_prev.card : ℝ) + ((P_mid ⟨j, by omega⟩).length : ℝ) + 1 ≤ (δ / 2) * (m : ℝ) := by
        have hsum_add : ∑ r : Fin j, ((P_mid ⟨r.val, by omega⟩).length + 1) =
            (∑ r : Fin j, (P_mid ⟨r.val, by omega⟩).length) + j := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        have hler : (Used_prev.card : ℝ) + ((P_mid ⟨j, by omega⟩).length : ℝ) + 1 ≤ (cap_used : ℝ) := by
          exact_mod_cast (show Used_prev.card + (P_mid ⟨j, by omega⟩).length + 1 ≤ cap_used by dsimp only [cap_used, L_sk]; omega)
        linarith [hcap_le]
      let S_j : Finset α := V (B ⟨j, by omega⟩) \ BadOf (B ⟨j, by omega⟩) (A ⟨j, by omega⟩)
      have hSj_card : (d / 4) * (m : ℝ) ≤ (S_j.card : ℝ) := by
        have h1 : S_j.card + (BadOf (B ⟨j, by omega⟩) (A ⟨j, by omega⟩)).card = (V (B ⟨j, by omega⟩)).card :=
          card_sdiff_add_card_eq_card (filter_subset (fun u => ((G.neighborFinset u ∩ V (A ⟨j, by omega⟩)).card : ℝ) < (d / 2) * (m : ℝ)) (V (B ⟨j, by omega⟩)))
        have h1r : (S_j.card : ℝ) + ((BadOf (B ⟨j, by omega⟩) (A ⟨j, by omega⟩)).card : ℝ) = (m : ℝ) := by
          rw [hVcard] at h1; exact_mod_cast h1
        have h2 := hBadOf_le _ _ (hAB_adj ⟨j, by omega⟩).symm
        have hδ_le_d : δ ≤ d / 12 := by nlinarith
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      obtain ⟨wj, uj1, pj, hpj, hwj_S, huj1_V, huj1_good, hpj_out⟩ :=
        realize_walk_to_good G V R hδ0 hd0 hδd hd1 hVcard hReg (P_mid ⟨j, by omega⟩)
          S_j (BadOf (A ⟨j + 1, by omega⟩) (B ⟨j + 1, by omega⟩)) Used_prev
          sdiff_subset hSj_card (hBadOf_le _ _ (hAB_adj ⟨j + 1, by omega⟩)) hUsed_le
      refine ⟨fun r => if h : r.val < j then W_v ⟨r.val, h⟩ else wj,
              fun r => if h : r.val < j then U_v ⟨r.val, h⟩ else uj1,
              fun r => if h : r.val < j then P_m ⟨r.val, h⟩ else pj, ?_, ?_, ?_, ?_, ?_⟩
      · intro r; dsimp only; split_ifs with h
        · exact hPsp ⟨r.val, h⟩
        · have hrj : (⟨r.val, by omega⟩ : Fin (s - 1)) = ⟨j, by omega⟩ := Fin.ext (by simp; omega)
          have hlen : (P_mid ⟨r.val, by omega⟩).length = (P_mid ⟨j, by omega⟩).length :=
            congrArg (fun k : Fin (s - 1) => (P_mid k).length) hrj
          rw [hlen]; exact hpj
      · intro r; dsimp only; split_ifs with h
        · exact hWok ⟨r.val, h⟩
        · have he : (⟨r.val, by omega⟩ : Fin s) = ⟨j, by omega⟩ := Fin.ext (by simp; omega)
          rw [he]; exact Finset.mem_sdiff.mp hwj_S
      · intro r; dsimp only; split_ifs with h
        · exact hUok ⟨r.val, h⟩
        · have he : (⟨r.val + 1, by omega⟩ : Fin s) = ⟨j + 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [he]; exact ⟨huj1_V, huj1_good⟩
      · intro r x hx; dsimp only at hx; split_ifs at hx with h
        · exact hOut2 ⟨r.val, h⟩ x hx
        · exact fun hm => hpj_out x hx (mem_union_left _ hm)
      · intro r1 r2 hne x hx1 hx2
        dsimp only at hx1 hx2
        by_cases h1 : r1.val < j <;> by_cases h2 : r2.val < j
        · simp only [dif_pos h1, dif_pos h2] at hx1 hx2
          exact hPdisj ⟨r1.val, h1⟩ ⟨r2.val, h2⟩ (fun h => hne (Fin.ext (by simpa using congrArg Fin.val h))) x hx1 hx2
        · simp only [dif_pos h1, dif_neg h2] at hx1 hx2
          exact hpj_out x hx2 (mem_union_right _ (mem_biUnion.mpr ⟨⟨r1.val, h1⟩, mem_univ _, List.mem_toFinset.mpr hx1⟩))
        · simp only [dif_neg h1, dif_pos h2] at hx1 hx2
          exact hpj_out x hx1 (mem_union_right _ (mem_biUnion.mpr ⟨⟨r2.val, h2⟩, mem_univ _, List.mem_toFinset.mpr hx2⟩))
        · exact hne (Fin.ext (by omega))
  obtain ⟨W_v, U_v, P_m, hPsp, hWok, hUok, hOut2, hPdisj⟩ := hmid_build (s - 1) (le_refl _)
  let Used_all : Finset α := Used2 ∪ (Finset.univ : Finset (Fin (s - 1))).biUnion (fun r => (P_m r).toFinset)
  have hUsed_all_le : (Used_all.card : ℝ) ≤ δ * (m : ℝ) := by
    have h1 : Used_all.card ≤ Forb.card + P_start.length + P_end.length + 2 +
        ∑ r : Fin (s - 1), ((P_mid r).length + 1) := by
      refine (card_union_le _ _).trans (Nat.add_le_add hUsed2_card ?_)
      refine card_biUnion_le.trans (sum_le_sum fun r _ => (List.toFinset_card_le _).trans (hPsp r).2.1.le)
    have h2 : ∑ r : Fin (s - 1), ((P_mid r).length + 1) = (∑ r : Fin (s - 1), (P_mid r).length) + (s - 1) := by
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have hr : (Used_all.card : ℝ) ≤ (cap_used : ℝ) := by
      exact_mod_cast (show Used_all.card ≤ cap_used by dsimp only [cap_used, L_sk]; omega)
    linarith [hcap_le]
  let u_match : Fin s → α := fun r => if h : r.val = 0 then u0 else U_v ⟨r.val - 1, by omega⟩
  let w_match : Fin s → α := fun r => if h : r.val < s - 1 then W_v ⟨r.val, h⟩ else w_last
  have hu_in_sk : ∀ r : Fin s, u_match r ∈ Used_all := fun r => by
    dsimp only [u_match]; split_ifs with h0
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr (last_mem_of_isSimplePath hp_start))))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨⟨r.val - 1, by omega⟩, mem_univ _, List.mem_toFinset.mpr (last_mem_of_isSimplePath (hPsp _))⟩)
  have hw_not_Forb : ∀ r : Fin s, w_match r ∉ Forb := fun r hF => by
    dsimp only [w_match] at hF; split_ifs at hF with hlt
    · exact hOut2 ⟨r.val, hlt⟩ _ (head_mem_of_isSimplePath (hPsp _)) (mem_union_left _ (mem_union_left _ hF))
    · exact hp_end_out _ (head_mem_of_isSimplePath hp_end) (mem_union_left _ hF)
  have hu_not_Forb : ∀ r : Fin s, u_match r ∉ Forb := fun r hF => by
    dsimp only [u_match] at hF; split_ifs at hF with h0
    · exact hp_start_out _ (last_mem_of_isSimplePath hp_start) hF
    · exact hOut2 ⟨r.val - 1, by omega⟩ _ (last_mem_of_isSimplePath (hPsp _)) (mem_union_left _ (mem_union_left _ hF))
  let M_cap : ℕ := Nat.floor ((1 - 6 * δ / d) * (m : ℝ))
  let T : ℕ := (L - L_sk - s) / 2
  have hT_eq : 2 * T + L_sk + s = L := by omega
  have hT_hi : T ≤ s * M_cap := by
    have hhi' : L ≤ L_sk + s + 2 * (s * M_cap) := by simpa [L_sk, M_cap, mul_assoc] using hL_hi
    dsimp only [T]; omega
  obtain ⟨L_r, hLr_bounds, hLr_sum⟩ := exists_bounded_sum_decomp s M_cap T (by omega) hT_hi
  have hfill : ∀ r : Fin s,
      ∃ q : List α, IsSimplePath G q (2 * L_r r + 1) (u_match r) (w_match r) ∧
        ∀ x ∈ q, x ∈ V (A r) ∪ V (B r) ∧ (x ∈ Used_all → x = u_match r ∨ x = w_match r) := by
    intro r
    let Forb_r : Finset α := Used_all \ {u_match r, w_match r}
    have hFr_card : (Forb_r.card : ℝ) ≤ δ * (m : ℝ) :=
      (Nat.cast_le.mpr (card_le_card sdiff_subset)).trans hUsed_all_le
    have hu_in_V : u_match r ∈ V (A r) ∧ u_match r ∉ BadOf (A r) (B r) := by
      dsimp only [u_match]; split_ifs with h0
      · have hr0 : r = ⟨0, hs1⟩ := Fin.ext h0; rw [hr0]; exact ⟨hu0_V, hu0_good⟩
      · have h := hUok ⟨r.val - 1, by omega⟩
        have hr' : (⟨r.val - 1 + 1, by omega⟩ : Fin s) = r := Fin.ext (by simp; omega)
        rwa [hr'] at h
    have hw_in_V : w_match r ∈ V (B r) ∧ w_match r ∉ BadOf (B r) (A r) := by
      dsimp only [w_match]; split_ifs with hlt
      · exact hWok ⟨r.val, hlt⟩
      · have hrl : r = ⟨s - 1, by omega⟩ := Fin.ext (by simp; omega); rw [hrl]; exact ⟨hw_last_V, hw_last_good⟩
    have hdu : (d / 2) * (m : ℝ) ≤ ((G.neighborFinset (u_match r) ∩ V (B r)).card : ℝ) := by
      by_contra hlt; push Not at hlt; exact hu_in_V.2 (mem_filter.mpr ⟨hu_in_V.1, hlt⟩)
    have hdw : (d / 2) * (m : ℝ) ≤ ((G.neighborFinset (w_match r) ∩ V (A r)).card : ℝ) := by
      by_contra hlt; push Not at hlt; exact hw_in_V.2 (mem_filter.mpr ⟨hw_in_V.1, hlt⟩)
    have hLr_real : (L_r r : ℝ) ≤ (1 - 6 * δ / d) * (m : ℝ) := by
      have h1 : (L_r r : ℝ) ≤ (M_cap : ℝ) := by exact_mod_cast (hLr_bounds r).2
      have hnn : 0 ≤ (1 - 6 * δ / d) * (m : ℝ) := by
        have hδdiv : δ / d ≤ 1 / 12 := by rw [div_le_iff₀ hd0]; nlinarith
        have h6 : 0 ≤ 1 - 6 * δ / d := by rw [mul_div_assoc]; linarith
        exact mul_nonneg h6 (Nat.cast_nonneg _)
      exact h1.trans (Nat.floor_le hnn)
    obtain ⟨q, hq_sp, hq_ok⟩ := luczak_bipartite_path G (hVdisj _ _ (hAB_ne r r)) (hVcard (A r)) (hVcard (B r))
      hδ0 hd0 hd1 hδd hm_100 (hReg _ _ (hAB_adj r)).1 (hReg _ _ (hAB_adj r)).2 hFr_card
      hu_in_V.1 (by simp [Forb_r]) hw_in_V.1 (by simp [Forb_r]) hdu hdw (hLr_bounds r).1 hLr_real
    refine ⟨q, hq_sp, fun x hx => ⟨(hq_ok x hx).1, fun hU => ?_⟩⟩
    by_contra hne; push Not at hne
    exact (hq_ok x hx).2 (Finset.mem_sdiff.mpr ⟨hU, by simp [hne.1, hne.2]⟩)
  choose Q_m hQsp hQm using hfill
  have hQ_not_end : ∀ (r : Fin s) (x : α), x ∈ Q_m r → x ∈ p_end → r.val = s - 1 ∧ x = w_last := by
    intro r x hxQ hxe
    have hU : x ∈ Used_all := mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hxe))
    rcases (hQm r x hxQ).2 hU with rfl | rfl
    · exfalso; dsimp only [u_match] at hxe; split_ifs at hxe with h0
      · exact hp_end_out _ hxe (mem_union_right _ (List.mem_toFinset.mpr (last_mem_of_isSimplePath hp_start)))
      · exact hOut2 ⟨r.val - 1, by omega⟩ _ (last_mem_of_isSimplePath (hPsp _))
          (mem_union_right _ (List.mem_toFinset.mpr hxe))
    · dsimp only [w_match] at hxe ⊢; split_ifs at hxe with hlt
      · exfalso; exact hOut2 ⟨r.val, hlt⟩ _ (head_mem_of_isSimplePath (hPsp _))
          (mem_union_right _ (List.mem_toFinset.mpr hxe))
      · exact ⟨by omega, by simp [w_match, hlt]⟩
  have hQ_not_mid : ∀ (r : Fin s) (k : Fin (s - 1)) (x : α), x ∈ Q_m r → x ∈ P_m k →
      (k.val + 1 = r.val ∧ x = u_match r) ∨ (k.val = r.val ∧ x = w_match r) := by
    intro r k x hxQ hxk
    have hU : x ∈ Used_all := mem_union_right _ (mem_biUnion.mpr ⟨k, mem_univ _, List.mem_toFinset.mpr hxk⟩)
    rcases (hQm r x hxQ).2 hU with rfl | rfl
    · left; refine ⟨?_, rfl⟩
      dsimp only [u_match] at hxk; split_ifs at hxk with h0
      · exfalso; exact hOut2 k _ hxk (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr (last_mem_of_isSimplePath hp_start))))
      · by_contra hne
        exact hPdisj ⟨r.val - 1, by omega⟩ k (fun h => hne (by have h' := congrArg Fin.val h; simp at h'; omega)) _ (last_mem_of_isSimplePath (hPsp _)) hxk
    · right; refine ⟨?_, rfl⟩
      dsimp only [w_match] at hxk; split_ifs at hxk with hlt
      · by_contra hne
        exact hPdisj ⟨r.val, hlt⟩ k (fun h => hne (by have h' := congrArg Fin.val h; simp at h'; omega)) _ (head_mem_of_isSimplePath (hPsp _)) hxk
      · exfalso; exact hOut2 k _ hxk (mem_union_right _ (List.mem_toFinset.mpr (head_mem_of_isSimplePath hp_end)))
  have hQ_disj : ∀ (r1 r2 : Fin s), r1 ≠ r2 → ∀ x ∈ Q_m r1, x ∉ Q_m r2 := fun r1 r2 hne x h1 h2 => by
    rcases mem_union.mp (hQm r1 x h1).1 with hA1 | hB1 <;>
    rcases mem_union.mp (hQm r2 x h2).1 with hA2 | hB2
    · exact Finset.disjoint_left.mp (hVdisj _ _ (fun h => hne (hA_inj h))) hA1 hA2
    · exact Finset.disjoint_left.mp (hVdisj _ _ (hAB_ne r1 r2)) hA1 hB2
    · exact Finset.disjoint_left.mp (hVdisj _ _ (hAB_ne r2 r1).symm) hB1 hA2
    · exact Finset.disjoint_left.mp (hVdisj _ _ (fun h => hne (hB_inj h))) hB1 hB2
  have hchain : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjs : j ≤ s),
      ∃ (P_j : List α),
        IsSimplePath G P_j
          (P_start.length + (∑ r : Fin (j - 1), (P_mid ⟨r.val, by omega⟩).length) +
            ∑ r : Fin j, (2 * L_r ⟨r.val, by omega⟩ + 1))
          v_start (w_match ⟨j - 1, by omega⟩) ∧
        ∀ x ∈ P_j, x ∈ p_start ∨ (∃ r : Fin j, x ∈ Q_m ⟨r.val, by omega⟩) ∨
          (∃ r : Fin (j - 1), x ∈ P_m ⟨r.val, by omega⟩) := by
    intro j hj1 hjs
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        have hp1 := isSimplePath_append hp_start (by simpa [u_match] using hQsp ⟨0, hs1⟩) fun x hxs hxQ => by
          have hU : x ∈ Used_all := mem_union_left _ (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hxs)))
          rcases (hQm ⟨0, hs1⟩ x hxQ).2 hU with rfl | rfl
          · simp [u_match]
          · exfalso; dsimp only [w_match] at hxs; split_ifs at hxs with hlt
            · exact hOut2 ⟨0, hlt⟩ _ (head_mem_of_isSimplePath (hPsp _))
                (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hxs)))
            · exact hp_end_out _ (head_mem_of_isSimplePath hp_end) (mem_union_right _ (List.mem_toFinset.mpr hxs))
        refine ⟨p_start ++ (Q_m ⟨0, hs1⟩).tail, by simpa using hp1, fun x hx => ?_⟩
        rcases (mem_append_tail_iff (by simpa [u_match] using (hQsp ⟨0, hs1⟩).2.2.1) (last_mem_of_isSimplePath hp_start)).mp hx with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inl ⟨⟨0, by omega⟩, h2⟩)
      · obtain ⟨P_j, hPj, hPj_mem⟩ := ih (by omega) (by omega)
        let r_prev : Fin (s - 1) := ⟨j - 1, by omega⟩
        let r_cur : Fin s := ⟨j, hjs⟩
        have hPm_sp : IsSimplePath G (P_m r_prev) (P_mid r_prev).length (w_match ⟨j - 1, by omega⟩) (u_match r_cur) := by
          have hw : w_match ⟨j - 1, by omega⟩ = W_v r_prev := by dsimp only [w_match, r_prev]; rw [dif_pos (by omega)]
          have hu : u_match r_cur = U_v r_prev := by dsimp only [u_match, r_cur, r_prev]; rw [dif_neg (by omega)]
          rw [hw, hu]; exact hPsp r_prev
        have hPj_mid := isSimplePath_append hPj hPm_sp fun x hxP hxM => by
          rcases hPj_mem x hxP with hxs | ⟨r, hxQ⟩ | ⟨r, hxm⟩
          · exact absurd (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hxs))) (hOut2 r_prev x hxM)
          · rcases hQ_not_mid ⟨r.val, by omega⟩ r_prev x hxQ hxM with ⟨hbad, _⟩ | ⟨heq, hx⟩
            · dsimp only [r_prev] at hbad; omega
            · have : (⟨r.val, by omega⟩ : Fin s) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; dsimp only [r_prev] at heq; omega)
              rwa [this] at hx
          · exact absurd hxM (hPdisj ⟨r.val, by omega⟩ r_prev (fun h => by have := congrArg Fin.val h; dsimp only [r_prev] at this; omega) x hxm)
        have hPj_mid_mem : ∀ x ∈ P_j ++ (P_m r_prev).tail, x ∈ p_start ∨ (∃ r : Fin j, x ∈ Q_m ⟨r.val, by omega⟩) ∨
            (∃ r : Fin j, x ∈ P_m ⟨r.val, by omega⟩) := fun x hx => by
          rcases (mem_append_tail_iff hPm_sp.2.2.1 (last_mem_of_isSimplePath hPj)).mp hx with h1 | h2
          · rcases hPj_mem x h1 with hxs | ⟨r, hxQ⟩ | ⟨r, hxm⟩
            · exact Or.inl hxs
            · exact Or.inr (Or.inl ⟨r, hxQ⟩)
            · exact Or.inr (Or.inr ⟨⟨r.val, by omega⟩, hxm⟩)
          · exact Or.inr (Or.inr ⟨⟨j - 1, by omega⟩, h2⟩)
        have hP_next := isSimplePath_append hPj_mid (hQsp r_cur) fun x hxP hxQ => by
          rcases hPj_mid_mem x hxP with hxs | ⟨r, hxQ'⟩ | ⟨r, hxm⟩
          · have hU : x ∈ Used_all := mem_union_left _ (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hxs)))
            rcases (hQm r_cur x hxQ).2 hU with rfl | rfl
            · rfl
            · exfalso; dsimp only [w_match, r_cur] at hxs; split_ifs at hxs with hlt
              · exact hOut2 ⟨j, hlt⟩ _ (head_mem_of_isSimplePath (hPsp _))
                  (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hxs)))
              · exact hp_end_out _ (head_mem_of_isSimplePath hp_end) (mem_union_right _ (List.mem_toFinset.mpr hxs))
          · exact absurd hxQ (hQ_disj ⟨r.val, by omega⟩ r_cur (fun h => by have := congrArg Fin.val h; dsimp only [r_cur] at this; omega) x hxQ')
          · rcases hQ_not_mid r_cur ⟨r.val, by omega⟩ x hxQ hxm with ⟨_, hx⟩ | ⟨hbad, _⟩
            · exact hx
            · dsimp only [r_cur] at hbad; omega
        have hlen_eq : P_start.length + (∑ r : Fin (j - 1), (P_mid ⟨r.val, by omega⟩).length) +
              (∑ r : Fin j, (2 * L_r ⟨r.val, by omega⟩ + 1)) + (P_mid r_prev).length + (2 * L_r r_cur + 1) =
            P_start.length + (∑ r : Fin j, (P_mid ⟨r.val, by omega⟩).length) +
              ∑ r : Fin (j + 1), (2 * L_r ⟨r.val, by omega⟩ + 1) := by
          have hs1' : ∑ r : Fin j, (P_mid ⟨r.val, by omega⟩).length =
              (∑ r : Fin (j - 1), (P_mid ⟨r.val, by omega⟩).length) + (P_mid r_prev).length := by
            calc ∑ r : Fin j, (P_mid ⟨r.val, by omega⟩).length
                = ∑ r : Fin ((j - 1) + 1), (P_mid ⟨r.val, by omega⟩).length :=
                  sum_bij (fun r _ => ⟨r.val, by omega⟩) (fun _ _ => mem_univ _)
                    (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
                    (fun r _ => ⟨⟨r.val, by omega⟩, mem_univ _, Fin.ext rfl⟩) (fun _ _ => rfl)
              _ = (∑ r : Fin (j - 1), (P_mid ⟨r.val, by omega⟩).length) + (P_mid r_prev).length := by
                  rw [Fin.sum_univ_castSucc]; rfl
          have hs2' : ∑ r : Fin (j + 1), (2 * L_r ⟨r.val, by omega⟩ + 1) =
              (∑ r : Fin j, (2 * L_r ⟨r.val, by omega⟩ + 1)) + (2 * L_r r_cur + 1) := by
            rw [Fin.sum_univ_castSucc]; rfl
          omega
        rw [hlen_eq] at hP_next
        refine ⟨(P_j ++ (P_m r_prev).tail) ++ (Q_m r_cur).tail, hP_next, fun x hx => ?_⟩
        rcases (mem_append_tail_iff (hQsp r_cur).2.2.1 (last_mem_of_isSimplePath hPj_mid)).mp hx with h1 | h2
        · rcases hPj_mid_mem x h1 with hxs | ⟨r, hxQ⟩ | ⟨r, hxm⟩
          · exact Or.inl hxs
          · exact Or.inr (Or.inl ⟨⟨r.val, by omega⟩, hxQ⟩)
          · exact Or.inr (Or.inr ⟨r, hxm⟩)
        · exact Or.inr (Or.inl ⟨⟨j, by omega⟩, h2⟩)
  obtain ⟨P_s, hPs, hPs_mem⟩ := hchain s hs1 (le_refl s)
  have hw_end_eq : w_match ⟨s - 1, by omega⟩ = w_last := by dsimp only [w_match]; rw [dif_neg (by omega)]
  rw [hw_end_eq] at hPs
  have hP_fin := isSimplePath_append hPs hp_end fun x hxP hxe => by
    rcases hPs_mem x hxP with hxs | ⟨r, hxQ⟩ | ⟨r, hxm⟩
    · exact absurd (mem_union_right _ (List.mem_toFinset.mpr hxs)) (hp_end_out x hxe)
    · exact (hQ_not_end r x hxQ hxe).2
    · exact absurd (mem_union_right _ (List.mem_toFinset.mpr hxe)) (hOut2 r x hxm)
  have hlen_fin : P_start.length + (∑ r : Fin (s - 1), (P_mid ⟨r.val, by omega⟩).length) +
      (∑ r : Fin s, (2 * L_r ⟨r.val, by omega⟩ + 1)) + P_end.length = L := by
    have hsum_L : ∑ r : Fin s, (2 * L_r r + 1) = 2 * T + s := by
      rw [sum_add_distrib, ← mul_sum, hLr_sum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    change P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + (∑ r : Fin s, (2 * L_r r + 1)) + P_end.length = L
    rw [hsum_L]; dsimp only [L_sk] at hT_eq; omega
  rw [hlen_fin] at hP_fin
  refine ⟨v_start, v_end, P_s ++ p_end.tail, hP_fin, hv_start_S, hv_end_S, fun x hx hF => ?_⟩
  rcases (mem_append_tail_iff hp_end.2.2.1 (last_mem_of_isSimplePath hPs)).mp hx with h1 | h2
  · rcases hPs_mem x h1 with hxs | ⟨r, hxQ⟩ | ⟨r, hxm⟩
    · exact hp_start_out x hxs hF
    · have hU : x ∈ Used_all := mem_union_left _ (mem_union_left _ (mem_union_left _ hF))
      rcases (hQm r x hxQ).2 hU with rfl | rfl
      · exact hu_not_Forb r hF
      · exact hw_not_Forb r hF
    · exact hOut2 r x hxm (mem_union_left _ (mem_union_left _ hF))
  · exact hp_end_out x h2 (mem_union_left _ hF)
private lemma chain'_getElem {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → ∀ (i : ℕ) (hi : i + 1 < l.length), R l[i] l[i + 1]
  | [], _, _, hi => by simp at hi
  | [_], _, _, hi => by simp at hi
  | a :: b :: t, h, 0, _ => (List.isChain_cons_cons.mp h).1
  | a :: b :: t, h, i + 1, hi =>
    chain'_getElem (List.isChain_cons_cons.mp h).2 i (by simp at hi ⊢; omega)
lemma odd_cycle_of_path_and_vertex {α : Type*} {G : SimpleGraph α} {n : ℕ} (hn : 1 ≤ n)
    {v u w : α} (hvu : G.Adj v u) (hvw : G.Adj v w)
    {p : List α} (hp : IsSimplePath G p (2 * n - 1) u w) (hnotv : v ∉ p) :
    cycleGraph (2 * n + 1) ⊑ G := by
  let Lc : List α := v :: p
  have hlen : Lc.length = 2 * n + 1 := by simp [Lc, hp.2.1]; omega
  have hnd : Lc.Nodup := List.nodup_cons.mpr ⟨hnotv, hp.1⟩
  have hch : Lc.IsChain G.Adj := (isSimplePath_cons hp hvu hnotv).2.2.2.2
  let f : Fin (2 * n + 1) → α := fun i => Lc[i.val]'(by omega)
  refine cycleGraph_isContained_of_fun (by omega) f ?_ ?_
  · intro i j heq
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp heq)
  · intro i
    by_cases hlast : i.val = 2 * n
    · have hi1 : i + 1 = ⟨0, by omega⟩ := Fin.ext (by
        rw [Fin.val_add]; simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * n + 1), hlast])
      have hf1 : f (i + 1) = v := by rw [hi1]; simp [f, Lc]
      have hf0 : f i = w := by
        have hgl : Lc.getLast? = some w := (isSimplePath_cons hp hvu hnotv).2.2.2.1
        rw [List.getLast?_eq_getElem?] at hgl
        have hi : i.val = Lc.length - 1 := by omega
        have hget := List.getElem?_eq_getElem (by omega : Lc.length - 1 < Lc.length)
        have hlast_eq : Lc[Lc.length - 1]'(by omega) = w := Option.some.inj (hget.symm.trans hgl)
        dsimp only [f]
        have heq_idx : Lc[i.val]'(by omega) = Lc[Lc.length - 1]'(by omega) := by simp only [hi]
        exact heq_idx.trans hlast_eq
      rw [hf0, hf1]; exact hvw.symm
    · have hi1 : (i + 1).val = i.val + 1 := by
        rw [Fin.val_add]; simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * n + 1),
          Nat.mod_eq_of_lt (by omega : i.val + 1 < 2 * n + 1)]
      have hadj := chain'_getElem hch i.val (by omega)
      simpa [f, hi1] using hadj
lemma odd_cycle_of_path_and_edge {α : Type*} {G : SimpleGraph α} {n : ℕ} (hn : 2 ≤ n)
    {x y u w : α} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyw : G.Adj y w)
    {p : List α} (hp : IsSimplePath G p (2 * n - 2) u w) (hnotx : x ∉ p) (hnoty : y ∉ p) :
    cycleGraph (2 * n + 1) ⊑ G := by
  have hp' := isSimplePath_append hp (isSimplePath_cons (isSimplePath_singleton G y) hyw.symm (by simp [G.ne_of_adj hyw.symm]))
    fun z hzp hz2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz2
      rcases hz2 with rfl | rfl; rfl; exact absurd hzp hnoty
  have hlen' : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  rw [hlen'] at hp'
  exact odd_cycle_of_path_and_vertex (by omega) hxu hxy hp' fun h => by
    rcases (mem_append_tail_iff rfl (last_mem_of_isSimplePath hp)).mp h with h1 | h2
    · exact hnotx h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl
      · exact hnotx (last_mem_of_isSimplePath hp)
      · exact G.ne_of_adj hxy rfl
lemma exists_short_odd_closed_walk {t : ℕ} (R : SimpleGraph (Fin t))
    (C : R.ConnectedComponent) (hnb : ¬ IsBipartiteComponent R C.supp) {b : Fin t} (hb : b ∈ C.supp) :
    ∃ W : R.Walk b b, W.length % 2 = 1 ∧ W.length ≤ 2 * t := by
  classical
  by_contra hno
  push Not at hno
  let dist : Fin t → ℕ := fun v =>
    if h : R.Reachable b v then
      Nat.find (show ∃ L, ∃ W : R.Walk b v, W.length = L from by obtain ⟨W⟩ := h; exact ⟨W.length, W, rfl⟩)
    else 0
  have hdist_spec : ∀ v, v ∈ C.supp → ∃ W : R.Walk b v, W.length = dist v ∧ W.length < t := by
    intro v hv
    have hr : R.Reachable b v := ConnectedComponent.eq.mp (hb.trans hv.symm)
    obtain ⟨W, hW⟩ := Nat.find_spec (show ∃ L, ∃ W : R.Walk b v, W.length = L from
      by obtain ⟨W⟩ := hr; exact ⟨W.length, W, rfl⟩)
    have hlt : W.bypass.length < t := by
      have hle := W.bypass_isPath.support_nodup.length_le_card
      rw [Walk.length_support, Fintype.card_fin] at hle; omega
    have hmin := Nat.find_min' (show ∃ L, ∃ W : R.Walk b v, W.length = L from
      by obtain ⟨W⟩ := hr; exact ⟨W.length, W, rfl⟩) ⟨W.bypass, rfl⟩
    refine ⟨W, ?_, by omega⟩
    dsimp only [dist]; rw [dif_pos hr]; exact hW
  apply hnb
  refine ⟨fun v => decide (dist v % 2 = 1), fun u hu v hv huv heq => ?_⟩
  have hpar : dist u % 2 = dist v % 2 := by
    have : (dist u % 2 = 1) ↔ (dist v % 2 = 1) := by simpa using heq
    omega
  obtain ⟨Wu, hWu_len, hWu_lt⟩ := hdist_spec u hu
  obtain ⟨Wv, hWv_len, hWv_lt⟩ := hdist_spec v hv
  let Wc : R.Walk b b := (Wu.append (.cons huv .nil)).append Wv.reverse
  have hWc_len : Wc.length = dist u + 1 + dist v := by
    simp [Wc, Walk.length_append, Walk.length_reverse, hWu_len, hWv_len]
  exact absurd (show Wc.length ≤ 2 * t by omega) (not_le.mpr (hno Wc (by omega)))
lemma exists_short_walk {t : ℕ} {R : SimpleGraph (Fin t)} {u v : Fin t} (h : R.Reachable u v) :
    ∃ W : R.Walk u v, W.length < t := by
  obtain ⟨W⟩ := h
  refine ⟨W.bypass, ?_⟩
  have hle := W.bypass_isPath.support_nodup.length_le_card
  rw [Walk.length_support, Fintype.card_fin] at hle; omega
lemma matching_to_fin_pairs {t : ℕ} {R : SimpleGraph (Fin t)} {M : Finset (Sym2 (Fin t))}
    (hM : IsMatching R M) :
    ∃ A B : Fin M.card → Fin t,
      (∀ r, R.Adj (A r) (B r)) ∧ Function.Injective A ∧ Function.Injective B ∧
      (∀ r1 r2, A r1 ≠ B r2) ∧ ∀ r, s(A r, B r) ∈ M := by
  classical
  let e : Fin M.card ≃ M := (Fintype.equivFinOfCardEq (Fintype.card_coe M)).symm
  have hex : ∀ r : Fin M.card, ∃ a b : Fin t, s(a, b) = (e r).val :=
    fun r => by induction (e r).val using Sym2.ind with | _ a b => exact ⟨a, b, rfl⟩
  choose A B hAB using hex
  have hmem : ∀ r, s(A r, B r) ∈ M := fun r => (hAB r).symm ▸ (e r).property
  have hadj : ∀ r, R.Adj (A r) (B r) := fun r => hM.1 _ (hmem r)
  have hAinj : Function.Injective A := fun r1 r2 heq => by
    by_contra hne
    have hne_e : s(A r1, B r1) ≠ s(A r2, B r2) := fun h => hne (e.injective (Subtype.ext ((hAB r1).symm.trans (h.trans (hAB r2)))))
    exact hM.2 _ (hmem r1) _ (hmem r2) hne_e (A r1) ⟨Sym2.mem_mk_left _ _, heq ▸ Sym2.mem_mk_left _ _⟩
  have hBinj : Function.Injective B := fun r1 r2 heq => by
    by_contra hne
    have hne_e : s(A r1, B r1) ≠ s(A r2, B r2) := fun h => hne (e.injective (Subtype.ext ((hAB r1).symm.trans (h.trans (hAB r2)))))
    exact hM.2 _ (hmem r1) _ (hmem r2) hne_e (B r1) ⟨Sym2.mem_mk_right _ _, heq ▸ Sym2.mem_mk_right _ _⟩
  have hne : ∀ r1 r2, A r1 ≠ B r2 := fun r1 r2 heq => by
    by_cases h12 : r1 = r2
    · subst h12; exact R.ne_of_adj (hadj r1) heq
    · have hne_e : s(A r1, B r1) ≠ s(A r2, B r2) := fun h => h12 (e.injective (Subtype.ext ((hAB r1).symm.trans (h.trans (hAB r2)))))
      exact hM.2 _ (hmem r1) _ (hmem r2) hne_e (A r1) ⟨Sym2.mem_mk_left _ _, heq ▸ Sym2.mem_mk_right _ _⟩
  exact ⟨A, B, hadj, hAinj, hBinj, hne, hmem⟩
lemma luczak_odd_cycle_of_odd_conn_matching {α : Type*} [Fintype α] [DecidableEq α] {t m n : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (V : Fin t → Finset α) (R : SimpleGraph (Fin t))
    {δ d : ℝ} (hδ0 : 0 < δ) (hd0 : 0 < d) (hd1 : d ≤ 1) (hδd : 12 * δ ≤ d ^ 2)
    (hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j))
    (hVcard : ∀ i : Fin t, (V i).card = m)
    (hReg : ∀ i j : Fin t, R.Adj i j → G.IsUniform δ (V i) (V j) ∧ d ≤ (G.edgeDensity (V i) (V j) : ℝ))
    (C : R.ConnectedComponent) (hnb : ¬ IsBipartiteComponent R C.supp)
    (M : Finset (Sym2 (Fin t))) (hM : IsMatching R M) (hMC : ∀ e ∈ M, ∀ v ∈ e, v ∈ C.supp)
    (hM_ne : M.Nonempty)
    (hm_big : (4 * ((t * t + 4 * t + 10 : ℕ) : ℝ) + 100) / δ ≤ (m : ℝ))
    (hn_lo : t * t + 6 * t + 10 ≤ 2 * n)
    (hn_hi : 2 * n ≤ 2 * M.card * Nat.floor ((1 - 6 * δ / d) * (m : ℝ))) :
    cycleGraph (2 * n + 1) ⊑ G := by
  obtain ⟨A, B, hAB_adj, hA_inj, hB_inj, hAB_ne, hAB_mem⟩ := matching_to_fin_pairs hM
  let s := M.card
  have hs1 : 1 ≤ s := card_pos.mpr hM_ne
  have hs_le_t : s ≤ t := by simpa [s] using Fintype.card_le_of_injective A hA_inj
  have hδ_le_d : δ ≤ d / 12 := by nlinarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hm_big
  obtain ⟨hunif0, hdens0⟩ := hReg (A ⟨0, hs1⟩) (B ⟨0, hs1⟩) (hAB_adj ⟨0, hs1⟩)
  let Bad0 := (V (A ⟨0, hs1⟩)).filter (fun u => ((G.neighborFinset u ∩ V (B ⟨0, hs1⟩)).card : ℝ) <
    ((G.edgeDensity (V (A ⟨0, hs1⟩)) (V (B ⟨0, hs1⟩)) : ℝ) - δ) * ((V (B ⟨0, hs1⟩)).card : ℝ))
  have hBad0 : (Bad0.card : ℝ) ≤ δ * (m : ℝ) := by
    have h := typical_degree_bound_le G hunif0 (Finset.Subset.refl _)
      (by rw [hVcard]; nlinarith [Nat.cast_nonneg (α := ℝ) m, hδ_le_d, hd1])
    rw [hVcard (A ⟨0, hs1⟩)] at h; linarith
  have hv0_ex : (V (A ⟨0, hs1⟩) \ Bad0).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro hemp
    have hle : (m : ℝ) ≤ (Bad0.card : ℝ) := by
      rw [← hVcard (A ⟨0, hs1⟩)]; exact_mod_cast card_le_card (sdiff_eq_empty_iff_subset.mp hemp)
    nlinarith
  obtain ⟨v0, hv0⟩ := hv0_ex
  rw [Finset.mem_sdiff] at hv0
  let S0 := G.neighborFinset v0 ∩ V (B ⟨0, hs1⟩)
  have hS0_card : (d / 4) * (m : ℝ) ≤ (S0.card : ℝ) := by
    have hge : ((G.edgeDensity (V (A ⟨0, hs1⟩)) (V (B ⟨0, hs1⟩)) : ℝ) - δ) * ((V (B ⟨0, hs1⟩)).card : ℝ) ≤ (S0.card : ℝ) := by
      by_contra hlt; push Not at hlt; exact hv0.2 (mem_filter.mpr ⟨hv0.1, hlt⟩)
    rw [hVcard] at hge; nlinarith
  let P_start : R.Walk (B ⟨0, hs1⟩) (A ⟨0, hs1⟩) := .cons (hAB_adj ⟨0, hs1⟩).symm .nil
  have hreach : ∀ r1 r2 : Fin s, R.Reachable (B r1) (A r2) := fun r1 r2 =>
    ConnectedComponent.eq.mp
      ((hMC _ (hAB_mem r1) _ (Sym2.mem_mk_right _ _)).trans (hMC _ (hAB_mem r2) _ (Sym2.mem_mk_left _ _)).symm)
  have hex_mid : ∀ r : Fin (s - 1), ∃ W : R.Walk (B ⟨r.val, by omega⟩) (A ⟨r.val + 1, by omega⟩), W.length < t :=
    fun r => exists_short_walk (hreach ⟨r.val, by omega⟩ ⟨r.val + 1, by omega⟩)
  choose P_mid hPmid_lt using hex_mid
  have hreach_end : R.Reachable (B ⟨s - 1, by omega⟩) (B ⟨0, hs1⟩) :=
    ConnectedComponent.eq.mp
      ((hMC _ (hAB_mem ⟨s - 1, by omega⟩) _ (Sym2.mem_mk_right _ _)).trans
       (hMC _ (hAB_mem ⟨0, hs1⟩) _ (Sym2.mem_mk_right _ _)).symm)
  obtain ⟨P_end0, hPend0_lt⟩ := exists_short_walk hreach_end
  obtain ⟨W_odd, hWodd_par, hWodd_le⟩ :=
    exists_short_odd_closed_walk R C hnb (hMC _ (hAB_mem ⟨0, hs1⟩) _ (Sym2.mem_mk_right _ _))
  let sumMid : ℕ := ∑ r : Fin (s - 1), (P_mid r).length
  have hsumMid_le : sumMid ≤ (s - 1) * t := by
    calc sumMid ≤ ∑ _r : Fin (s - 1), t := sum_le_sum fun r _ => (hPmid_lt r).le
      _ = (s - 1) * t := by simp
  let P_end : R.Walk (B ⟨s - 1, by omega⟩) (B ⟨0, hs1⟩) :=
    if (P_start.length + sumMid + P_end0.length + s) % 2 = 1 then P_end0 else P_end0.append W_odd
  have hPend_le : P_end.length ≤ 3 * t := by
    dsimp only [P_end]; split_ifs
    · omega
    · rw [Walk.length_append]; omega
  have hpar_odd : (P_start.length + sumMid + P_end.length + s) % 2 = 1 := by
    dsimp only [P_end]; split_ifs with h
    · exact h
    · rw [Walk.length_append]; omega
  have hLsk_le : P_start.length + sumMid + P_end.length + s ≤ t * t + 4 * t := by
    have hPs : P_start.length = 1 := rfl
    have hst : (s - 1) * t + s ≤ t * t := by zify [hs1]; nlinarith
    omega
  have hm_cond : (4 * ((P_start.length + sumMid + P_end.length + s + 10 : ℕ) : ℝ) + 100) / δ ≤ (m : ℝ) := by
    refine le_trans ?_ hm_big
    apply div_le_div_of_nonneg_right _ hδ0.le
    have hr : ((P_start.length + sumMid + P_end.length + s + 10 : ℕ) : ℝ) ≤ ((t * t + 4 * t + 10 : ℕ) : ℝ) := by
      exact_mod_cast (show P_start.length + sumMid + P_end.length + s + 10 ≤ t * t + 4 * t + 10 by omega)
    linarith
  have hpar_odd' : (2 * n - 1) % 2 = (P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s) % 2 := by
    dsimp only [sumMid] at hpar_odd; omega
  have hlo' : P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + 3 * s ≤ 2 * n - 1 := by
    dsimp only [sumMid] at hLsk_le; omega
  have hhi' : 2 * n - 1 ≤ P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s +
      2 * s * Nat.floor ((1 - 6 * δ / d) * (m : ℝ)) := by
    have h2s : 2 * s * Nat.floor ((1 - 6 * δ / d) * (m : ℝ)) = 2 * M.card * Nat.floor ((1 - 6 * δ / d) * (m : ℝ)) := rfl
    omega
  obtain ⟨u, w, p, hp, huS, hwS, hp_notv⟩ :=
    luczak_path_through_matching G V R hδ0 hd0 hd1 hδd hVdisj hVcard hReg hs1 A B hAB_adj
      hA_inj hB_inj hAB_ne P_start P_mid P_end (S_start := S0) (S_end := S0) (Forb := {v0})
      inter_subset_right hS0_card inter_subset_right hS0_card (by simp) hm_cond
      (L := 2 * n - 1) hpar_odd' hlo' hhi'
  exact odd_cycle_of_path_and_vertex (by omega)
    ((mem_neighborFinset G v0 u).mp (mem_inter.mp huS).1)
    ((mem_neighborFinset G v0 w).mp (mem_inter.mp hwS).1)
    hp (fun h => hp_notv v0 h (Finset.mem_singleton_self v0))
lemma luczak_odd_cycle_of_edge_and_matching {α : Type*} [Fintype α] [DecidableEq α] {t m n s : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (V : Fin t → Finset α) (R : SimpleGraph (Fin t))
    {δ d : ℝ} (hδ0 : 0 < δ) (hd0 : 0 < d) (hd1 : d ≤ 1) (hδd : 12 * δ ≤ d ^ 2)
    (hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j))
    (hVcard : ∀ i : Fin t, (V i).card = m)
    (hReg : ∀ i j : Fin t, R.Adj i j → G.IsUniform δ (V i) (V j) ∧ d ≤ (G.edgeDensity (V i) (V j) : ℝ))
    (hs1 : 1 ≤ s) (A B : Fin s → Fin t)
    (hAB_adj : ∀ r : Fin s, R.Adj (A r) (B r))
    (hA_inj : Function.Injective A) (hB_inj : Function.Injective B)
    (hAB_ne : ∀ r1 r2 : Fin s, A r1 ≠ B r2)
    {c1 c2 : Fin t}
    (P_start : R.Walk c1 (A ⟨0, hs1⟩))
    (P_mid : ∀ r : Fin (s - 1), R.Walk (B ⟨r.val, by omega⟩) (A ⟨r.val + 1, by omega⟩))
    (P_end : R.Walk (B ⟨s - 1, by omega⟩) c2)
    (heven : (P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s) % 2 = 0)
    {x y : α} (hxy : G.Adj x y)
    (hx_deg : (d / 4) * (m : ℝ) ≤ ((G.neighborFinset x ∩ V c1).card : ℝ))
    (hy_deg : (d / 4) * (m : ℝ) ≤ ((G.neighborFinset y ∩ V c2).card : ℝ))
    (hm_big : (4 * ((P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s + 10 : ℕ) : ℝ) + 100) / δ ≤ (m : ℝ))
    (hn_lo : P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + 3 * s + 4 ≤ 2 * n)
    (hn_hi : 2 * n ≤ 2 * s * Nat.floor ((1 - 6 * δ / d) * (m : ℝ))) :
    cycleGraph (2 * n + 1) ⊑ G := by
  obtain ⟨u, w, p, hp, huS, hwS, hp_out⟩ :=
    luczak_path_through_matching G V R hδ0 hd0 hd1 hδd hVdisj hVcard hReg hs1 A B hAB_adj
      hA_inj hB_inj hAB_ne P_start P_mid P_end
      (S_start := G.neighborFinset x ∩ V c1) (S_end := G.neighborFinset y ∩ V c2) (Forb := {x, y})
      inter_subset_right hx_deg inter_subset_right hy_deg
      ((card_insert_le _ _).trans (by simp)) hm_big
      (L := 2 * n - 2) (by omega) (by omega) (by omega)
  exact odd_cycle_of_path_and_edge (by omega) hxy
    ((mem_neighborFinset G x u).mp (mem_inter.mp huS).1)
    ((mem_neighborFinset G y w).mp (mem_inter.mp hwS).1)
    hp (fun h => hp_out x h (Finset.mem_insert_self x {y}))
    (fun h => hp_out y h (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
lemma luczak_odd_cycle_of_vertex_and_matching {α : Type*} [Fintype α] [DecidableEq α] {t m n s : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (V : Fin t → Finset α) (R : SimpleGraph (Fin t))
    {δ d : ℝ} (hδ0 : 0 < δ) (hd0 : 0 < d) (hd1 : d ≤ 1) (hδd : 12 * δ ≤ d ^ 2)
    (hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j))
    (hVcard : ∀ i : Fin t, (V i).card = m)
    (hReg : ∀ i j : Fin t, R.Adj i j → G.IsUniform δ (V i) (V j) ∧ d ≤ (G.edgeDensity (V i) (V j) : ℝ))
    (hs1 : 1 ≤ s) (A B : Fin s → Fin t)
    (hAB_adj : ∀ r : Fin s, R.Adj (A r) (B r))
    (hA_inj : Function.Injective A) (hB_inj : Function.Injective B)
    (hAB_ne : ∀ r1 r2 : Fin s, A r1 ≠ B r2)
    {c1 c2 : Fin t}
    (P_start : R.Walk c1 (A ⟨0, hs1⟩))
    (P_mid : ∀ r : Fin (s - 1), R.Walk (B ⟨r.val, by omega⟩) (A ⟨r.val + 1, by omega⟩))
    (P_end : R.Walk (B ⟨s - 1, by omega⟩) c2)
    (hodd : (P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s) % 2 = 1)
    {v : α}
    (hv1_deg : (d / 4) * (m : ℝ) ≤ ((G.neighborFinset v ∩ V c1).card : ℝ))
    (hv2_deg : (d / 4) * (m : ℝ) ≤ ((G.neighborFinset v ∩ V c2).card : ℝ))
    (hm_big : (4 * ((P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + s + 10 : ℕ) : ℝ) + 100) / δ ≤ (m : ℝ))
    (hn_lo : P_start.length + (∑ r : Fin (s - 1), (P_mid r).length) + P_end.length + 3 * s + 4 ≤ 2 * n)
    (hn_hi : 2 * n ≤ 2 * s * Nat.floor ((1 - 6 * δ / d) * (m : ℝ))) :
    cycleGraph (2 * n + 1) ⊑ G := by
  obtain ⟨u, w, p, hp, huS, hwS, hp_out⟩ :=
    luczak_path_through_matching G V R hδ0 hd0 hd1 hδd hVdisj hVcard hReg hs1 A B hAB_adj
      hA_inj hB_inj hAB_ne P_start P_mid P_end
      (S_start := G.neighborFinset v ∩ V c1) (S_end := G.neighborFinset v ∩ V c2) (Forb := {v})
      inter_subset_right hv1_deg inter_subset_right hv2_deg
      (by simp) hm_big
      (L := 2 * n - 1) (by omega) (by omega) (by omega)
  exact odd_cycle_of_path_and_vertex (by omega)
    ((mem_neighborFinset G v u).mp (mem_inter.mp huS).1)
    ((mem_neighborFinset G v w).mp (mem_inter.mp hwS).1)
    hp (fun h => hp_out v h (Finset.mem_singleton_self v))

private lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
lemma exists_bipartite_matching_of_high_min_deg {α : Type*} [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    {X Y : Finset α} {s : ℕ} (hX : X.card = s) (hY : Y.card = s)
    (hdegX : ∀ a ∈ X, s < 2 * (Y.filter (H.Adj a)).card)
    (hdegY : ∀ b ∈ Y, s < 2 * (X.filter (H.Adj b)).card) :
    ∃ A B : Fin s → α, Function.Injective A ∧ Function.Injective B ∧
      (∀ r, A r ∈ X) ∧ (∀ r, B r ∈ Y) ∧ ∀ r, H.Adj (A r) (B r) := by
  classical
  let tFun : X → Finset α := fun a => Y.filter (H.Adj a.val)
  have hHall : ∀ S : Finset X, S.card ≤ (S.biUnion tFun).card := by
    intro S
    by_cases hS0 : S = ∅
    · simp [hS0]
    · by_cases hSsmall : 2 * S.card ≤ s
      · obtain ⟨a, haS⟩ := nonempty_iff_ne_empty.mpr hS0
        have hsub : tFun a ⊆ S.biUnion tFun := subset_biUnion_of_mem tFun haS
        have hdeg := hdegX a.val a.property
        have hle := card_le_card hsub
        dsimp only [tFun] at hle ⊢; omega
      · have hYsub : Y ⊆ S.biUnion tFun := by
          intro b hb
          let Sval : Finset α := S.image Subtype.val
          have hSval_card : Sval.card = S.card := card_image_of_injective S Subtype.val_injective
          have hSval_sub : Sval ⊆ X := fun x hx => by
            rcases mem_image.mp hx with ⟨a, _, rfl⟩; exact a.property
          have hinter : (Sval ∩ X.filter (H.Adj b)).Nonempty := by
            by_contra hemp
            rw [not_nonempty_iff_eq_empty] at hemp
            have hdisj : Disjoint Sval (X.filter (H.Adj b)) := disjoint_iff_inter_eq_empty.mpr hemp
            have hle := card_le_card (union_subset hSval_sub (filter_subset (H.Adj b) X))
            rw [card_union_of_disjoint hdisj, hX, hSval_card] at hle
            have hdb := hdegY b hb
            omega
          obtain ⟨x, hx⟩ := hinter
          rw [mem_inter, mem_filter] at hx
          rcases mem_image.mp hx.1 with ⟨a, haS, rfl⟩
          exact mem_biUnion.mpr ⟨a, haS, mem_filter.mpr ⟨hb, hx.2.2.symm⟩⟩
        have hle1 : S.card ≤ s := by
          have : S.card ≤ Fintype.card X := card_le_univ S
          rwa [Fintype.card_coe, hX] at this
        have hle2 := card_le_card hYsub
        rw [hY] at hle2; omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective tFun).mp hHall
  let e : Fin s ≃ X := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hX])).symm
  refine ⟨fun r => (e r).val, fun r => f (e r),
    Subtype.val_injective.comp e.injective, hfinj.comp e.injective,
    fun r => (e r).property,
    fun r => (mem_filter.mp (hfmem (e r))).1,
    fun r => (mem_filter.mp (hfmem (e r))).2⟩
lemma exists_internal_matching_of_high_min_deg {α : Type*} [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    {X : Finset α} (hX6 : 6 ≤ X.card)
    (hdeg : ∀ a ∈ X, 4 * X.card < 5 * (X.filter (H.Adj a)).card) :
    ∃ M : Finset (Sym2 α), IsMatching H M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ X) ∧ M.card = X.card / 2 := by
  classical
  let s : ℕ := X.card / 2
  have hs_le : s ≤ X.card := Nat.div_le_self X.card 2
  obtain ⟨X1, hX1_sub, hX1_card⟩ := exists_subset_card_eq hs_le
  have hrem_card : s ≤ (X \ X1).card := by
    have h1 := card_sdiff_add_card_eq_card hX1_sub
    rw [hX1_card] at h1; dsimp only [s] at h1 ⊢; omega
  obtain ⟨X2, hX2_sub, hX2_card⟩ := exists_subset_card_eq hrem_card
  have hX2_X : X2 ⊆ X := hX2_sub.trans sdiff_subset
  have hdisj : Disjoint X1 X2 := Disjoint.mono_right hX2_sub disjoint_sdiff
  have hdeg_half : ∀ (A B : Finset α), A ⊆ X → B ⊆ X → B.card = s →
      ∀ a ∈ A, s < 2 * (B.filter (H.Adj a)).card := by
    intro A B hAX hBX hBcard a ha
    have haX := hAX ha
    have hnon : (B \ B.filter (H.Adj a)).card ≤ (X \ X.filter (H.Adj a)).card := by
      apply card_le_card
      intro x hx
      rw [Finset.mem_sdiff, mem_filter] at hx ⊢
      exact ⟨hBX hx.1, fun h => hx.2 ⟨hx.1, h.2⟩⟩
    have h1 := card_sdiff_add_card_eq_card (filter_subset (H.Adj a) B)
    have h2 := card_sdiff_add_card_eq_card (filter_subset (H.Adj a) X)
    have hd := hdeg a haX
    rw [hBcard] at h1
    dsimp only [s] at h1 ⊢
    omega
  obtain ⟨A, B, hAinj, hBinj, hAX1, hBX2, hAB⟩ :=
    exists_bipartite_matching_of_high_min_deg H hX1_card hX2_card
      (hdeg_half X1 X2 hX1_sub hX2_X hX2_card) (hdeg_half X2 X1 hX2_X hX1_sub hX1_card)
  let f : Fin s → Sym2 α := fun r => s(A r, B r)
  have hfinj : Function.Injective f := by
    intro r1 r2 heq
    have hmem : A r1 ∈ s(A r2, B r2) := by
      change s(A r1, B r1) = s(A r2, B r2) at heq
      rw [← heq]; exact Sym2.mem_mk_left (A r1) (B r1)
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact hAinj h
    · exact absurd (h ▸ hBX2 r2) (Finset.disjoint_left.mp hdisj (hAX1 r1))
  refine ⟨Finset.univ.image f, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro e he
    rcases mem_image.mp he with ⟨r, _, rfl⟩
    exact hAB r
  · intro e₁ he₁ e₂ he₂ hne z ⟨hz1, hz2⟩
    rcases mem_image.mp he₁ with ⟨r1, _, rfl⟩
    rcases mem_image.mp he₂ with ⟨r2, _, rfl⟩
    have hrne : r1 ≠ r2 := fun h => hne (by rw [h])
    rcases Sym2.mem_iff.mp hz1 with rfl | rfl <;> rcases Sym2.mem_iff.mp hz2 with h | h
    · exact hrne (hAinj h)
    · exact Finset.disjoint_left.mp hdisj (hAX1 r1) (h ▸ hBX2 r2)
    · exact Finset.disjoint_left.mp hdisj (h ▸ hAX1 r2) (hBX2 r1)
    · exact hrne (hBinj h)
  · intro e he v hv
    rcases mem_image.mp he with ⟨r, _, rfl⟩
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hX1_sub (hAX1 r)
    · exact hX2_X (hBX2 r)
  · rw [card_image_of_injective _ hfinj, Finset.card_fin]
lemma exists_len2_walk_bipartite {α : Type*} [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    {X Y : Finset α} {s : ℕ} (hY : Y.card = s)
    (hdegX : ∀ a ∈ X, s < 2 * (Y.filter (H.Adj a)).card)
    {x1 x2 : α} (hx1 : x1 ∈ X) (hx2 : x2 ∈ X) :
    ∃ W : H.Walk x1 x2, W.length = 2 := by
  have hinter : (Y.filter (H.Adj x1) ∩ Y.filter (H.Adj x2)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hle := card_le_card (union_subset (filter_subset (H.Adj x1) Y) (filter_subset (H.Adj x2) Y))
    rw [card_union_of_disjoint (disjoint_iff_inter_eq_empty.mpr hemp), hY] at hle
    have h1 := hdegX x1 hx1; have h2 := hdegX x2 hx2; omega
  obtain ⟨y, hy⟩ := hinter
  rw [mem_inter, mem_filter, mem_filter] at hy
  exact ⟨.cons hy.1.2 (.cons hy.2.2.symm .nil), rfl⟩
lemma exists_len3_walk_bipartite {α : Type*} [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    {X Y : Finset α} {s : ℕ} (hX : X.card = s) (hY : Y.card = s)
    (hdegX : ∀ a ∈ X, s < 2 * (Y.filter (H.Adj a)).card)
    (hdegY : ∀ b ∈ Y, s < 2 * (X.filter (H.Adj b)).card)
    {x y : α} (hx : x ∈ X) (hy : y ∈ Y) :
    ∃ W : H.Walk x y, W.length = 3 := by
  have hnx : (Y.filter (H.Adj x)).Nonempty := card_pos.mp (by have := hdegX x hx; omega)
  obtain ⟨y', hy'⟩ := hnx
  rw [mem_filter] at hy'
  obtain ⟨W2, hW2⟩ := exists_len2_walk_bipartite H hX hdegY hy'.1 hy
  exact ⟨.cons hy'.2 W2, by simp [hW2]⟩
lemma walk_parity_of_profile {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    {G : SimpleGraph V} {col : Fin k → SimpleGraph V} (P : ProfilePartition G col)
    (j : Fin k) {u v : V} (W : (col j).Walk u v) (hu : P.assign u j ≠ 2) :
    P.assign v j ≠ 2 ∧ (W.length % 2 = 0 ↔ P.assign u j = P.assign v j) := by
  induction W with
  | nil => exact ⟨hu, by simp⟩
  | @cons a b c hab W' ih =>
    have hbip := P.bipartite_edge j a b hab hu
    have hb : P.assign b j ≠ 2 := by
      rcases hbip with ⟨_, h1⟩ | ⟨_, h0⟩
      · rw [h1]; decide
      · rw [h0]; decide
    obtain ⟨hc, hpar⟩ := ih hb
    refine ⟨hc, ?_⟩
    rw [Walk.length_cons]
    have hc01 : P.assign c j = 0 ∨ P.assign c j = 1 := by
      rcases fin3_cases (P.assign c j) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hc
    rcases hbip with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw [ha0]; rw [hb1] at hpar
      rcases hc01 with hc0 | hc1
      · rw [hc0] at hpar ⊢
        have hne : (1 : Fin 3) ≠ 0 := by decide
        have : ¬ W'.length % 2 = 0 := fun h => hne (hpar.mp h)
        constructor <;> intro _ <;> first | rfl | omega
      · rw [hc1] at hpar ⊢
        have h0 : W'.length % 2 = 0 := hpar.mpr rfl
        have hne : (0 : Fin 3) ≠ 1 := by decide
        constructor <;> intro h <;> first | omega | exact absurd h hne
    · rw [ha1]; rw [hb0] at hpar
      rcases hc01 with hc0 | hc1
      · rw [hc0] at hpar ⊢
        have h0 : W'.length % 2 = 0 := hpar.mpr rfl
        have hne : (1 : Fin 3) ≠ 0 := by decide
        constructor <;> intro h <;> first | omega | exact absurd h hne
      · rw [hc1] at hpar ⊢
        have hne : (0 : Fin 3) ≠ 1 := by decide
        have : ¬ W'.length % 2 = 0 := fun h => hne (hpar.mp h)
        constructor <;> intro _ <;> first | rfl | omega
lemma exists_cube_partner {k : ℕ} {D : Finset (Subcube k)}
    (hdec : IsDecomposition D) (hw1 : ∀ τ ∈ D, weight τ = 1) (j : Fin k) :
    let B0 := D.filter (fun σ => σ j = 0)
    let B1 := D.filter (fun σ => σ j = 1)
    ∃ e : B0 ≃ B1, ∀ σ : B0,
      ∀ i : Fin k, i ≠ j → ¬ ((σ.val i = 0 ∧ (e σ).val i = 1) ∨ (σ.val i = 1 ∧ (e σ).val i = 0)) := by
  classical
  intro B0 B1
  let flipJ : (Fin k → Bool) → (Fin k → Bool) := fun x i => if i = j then !x i else x i
  have hflip_invol : Function.Involutive flipJ := fun x => by
    funext i; dsimp only [flipJ]; split_ifs <;> simp
  have hflip_inj : Function.Injective flipJ := hflip_invol.injective
  have hcard_B : B0.card = B1.card := by
    let Q0 : Finset (Fin k → Bool) := Finset.univ.filter (fun x => x j = false)
    let Q1 : Finset (Fin k → Bool) := Finset.univ.filter (fun x => x j = true)
    have hQeq : Q0.card = Q1.card := by
      have himg : Q0.image flipJ = Q1 := by
        ext y; simp only [Q0, Q1, mem_image, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, rfl⟩; simp [flipJ, hx]
        · intro hy; exact ⟨flipJ y, by simp [flipJ, hy], hflip_invol y⟩
      rw [← himg, card_image_of_injective _ hflip_inj]
    have hdisj : (D : Set (Subcube k)).PairwiseDisjoint subcubeSet := fun σ hσ τ hτ hne =>
      (distinguishable_iff_disjoint_subcubeSet σ τ).mp (hdec.1.2 σ hσ τ hτ hne)
    have hQ0_sum : Q0.card = ∑ τ ∈ D, (subcubeSet τ ∩ Q0).card := by
      have heq : Q0 = D.biUnion (fun τ => subcubeSet τ ∩ Q0) := by
        ext x; simp only [mem_biUnion, mem_inter]
        constructor
        · intro hx
          have hmem : x ∈ D.biUnion subcubeSet := by rw [hdec.2]; exact mem_univ x
          rcases mem_biUnion.mp hmem with ⟨τ, hτ, hxτ⟩
          exact ⟨τ, hτ, hxτ, hx⟩
        · rintro ⟨_, _, _, hx⟩; exact hx
      conv_lhs => rw [heq]
      rw [card_biUnion]
      intro σ hσ τ hτ hne
      exact Disjoint.mono inter_subset_left inter_subset_left (hdisj hσ hτ hne)
    have hQ1_sum : Q1.card = ∑ τ ∈ D, (subcubeSet τ ∩ Q1).card := by
      have heq : Q1 = D.biUnion (fun τ => subcubeSet τ ∩ Q1) := by
        ext x; simp only [mem_biUnion, mem_inter]
        constructor
        · intro hx
          have hmem : x ∈ D.biUnion subcubeSet := by rw [hdec.2]; exact mem_univ x
          rcases mem_biUnion.mp hmem with ⟨τ, hτ, hxτ⟩
          exact ⟨τ, hτ, hxτ, hx⟩
        · rintro ⟨_, _, _, hx⟩; exact hx
      conv_lhs => rw [heq]
      rw [card_biUnion]
      intro σ hσ τ hτ hne
      exact Disjoint.mono inter_subset_left inter_subset_left (hdisj hσ hτ hne)
    have hsplit : ∀ τ ∈ D,
        (subcubeSet τ ∩ Q0).card = (if τ j = 0 then 2 else if τ j = 1 then 0 else 1) ∧
        (subcubeSet τ ∩ Q1).card = (if τ j = 1 then 2 else if τ j = 0 then 0 else 1) := by
      intro τ hτ
      have hcard2 : (subcubeSet τ).card = 2 := by rw [card_subcubeSet, hw1 τ hτ]; norm_num
      have hsub_u : subcubeSet τ = (subcubeSet τ ∩ Q0) ∪ (subcubeSet τ ∩ Q1) := by
        ext x; simp only [Q0, Q1, mem_union, mem_inter, mem_filter, mem_univ, true_and]
        cases x j <;> simp
      have hd01 : Disjoint (subcubeSet τ ∩ Q0) (subcubeSet τ ∩ Q1) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        have h1' := (mem_filter.mp (mem_inter.mp h1).2).2
        have h2' := (mem_filter.mp (mem_inter.mp h2).2).2
        rw [h1'] at h2'; exact Bool.false_ne_true h2'
      rcases fin3_cases (τ j) with hj | hj | hj
      · have h0 : subcubeSet τ ∩ Q0 = subcubeSet τ := Finset.inter_eq_left.mpr fun x hx =>
          mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hx).2 j).1 hj⟩
        have h1 : subcubeSet τ ∩ Q1 = ∅ := by
          ext x; simp only [Q1, mem_inter, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨hx, hxj⟩
          have := ((mem_filter.mp hx).2 j).1 hj
          rw [this] at hxj; exact Bool.false_ne_true hxj
        simp [hj, h0, h1, hcard2]
      · have h1 : subcubeSet τ ∩ Q1 = subcubeSet τ := Finset.inter_eq_left.mpr fun x hx =>
          mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hx).2 j).2 hj⟩
        have h0 : subcubeSet τ ∩ Q0 = ∅ := by
          ext x; simp only [Q0, mem_inter, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨hx, hxj⟩
          have := ((mem_filter.mp hx).2 j).2 hj
          rw [this] at hxj; exact Bool.false_ne_true hxj.symm
        simp [hj, h0, h1, hcard2]
      · have hbij : (subcubeSet τ ∩ Q0).image flipJ = subcubeSet τ ∩ Q1 := by
          ext y; simp only [Q0, Q1, subcubeSet, mem_image, mem_inter, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨x, ⟨hx, hxj⟩, rfl⟩
            refine ⟨fun i => ?_, by simp [flipJ, hxj]⟩
            by_cases hij : i = j
            · subst hij; rw [hj]; constructor <;> intro h <;> exact absurd h (by decide)
            · simpa [flipJ, hij] using hx i
          · rintro ⟨hy, hyj⟩
            refine ⟨flipJ y, ⟨fun i => ?_, by simp [flipJ, hyj]⟩, hflip_invol y⟩
            by_cases hij : i = j
            · subst hij; rw [hj]; constructor <;> intro h <;> exact absurd h (by decide)
            · simpa [flipJ, hij] using hy i
        have heq_c : (subcubeSet τ ∩ Q0).card = (subcubeSet τ ∩ Q1).card := by
          rw [← hbij, card_image_of_injective _ hflip_inj]
        have hadd : (subcubeSet τ ∩ Q0).card + (subcubeSet τ ∩ Q1).card = 2 := by
          rw [← card_union_of_disjoint hd01, ← hsub_u, hcard2]
        have h1 : (subcubeSet τ ∩ Q0).card = 1 := by omega
        have h2 : (subcubeSet τ ∩ Q1).card = 1 := by omega
        simp [hj, h1, h2]
    let Ij := D.filter (fun σ => σ j = 2)
    have h0eq : Q0.card = 2 * B0.card + Ij.card := by
      rw [hQ0_sum, Finset.sum_congr rfl fun τ hτ => (hsplit τ hτ).1]
      have hsum : ∑ τ ∈ D, (if τ j = 0 then 2 else if τ j = 1 then 0 else 1) =
          ∑ τ ∈ D, ((if τ j = 0 then 2 else 0) + (if τ j = 2 then 1 else 0)) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rcases fin3_cases (τ j) with h | h | h <;> simp [h]
      rw [hsum, sum_add_distrib, ← sum_filter, ← sum_filter]
      simp [B0, Ij, mul_comm]
    have h1eq : Q1.card = 2 * B1.card + Ij.card := by
      rw [hQ1_sum, Finset.sum_congr rfl fun τ hτ => (hsplit τ hτ).2]
      have hsum : ∑ τ ∈ D, (if τ j = 1 then 2 else if τ j = 0 then 0 else 1) =
          ∑ τ ∈ D, ((if τ j = 1 then 2 else 0) + (if τ j = 2 then 1 else 0)) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rcases fin3_cases (τ j) with h | h | h <;> simp [h]
      rw [hsum, sum_add_distrib, ← sum_filter, ← sum_filter]
      simp [B1, Ij, mul_comm]
    omega
  let rel : Subcube k → Subcube k → Prop := fun σ τ =>
    ∀ i : Fin k, i ≠ j → ¬ ((σ i = 0 ∧ τ i = 1) ∨ (σ i = 1 ∧ τ i = 0))
  let tFun : B0 → Finset (Subcube k) := fun σ => B1.filter (rel σ.val)
  have hHall : ∀ S : Finset B0, S.card ≤ (S.biUnion tFun).card := by
    intro S
    let Lset : Finset (Fin k → Bool) := S.biUnion (fun σ => subcubeSet σ.val)
    let Rset : Finset (Fin k → Bool) := (S.biUnion tFun).biUnion subcubeSet
    have hLcard : Lset.card = 2 * S.card := by
      rw [card_biUnion]
      · rw [Finset.sum_congr rfl (fun σ _ => by rw [card_subcubeSet, hw1 σ.val (mem_filter.mp σ.property).1])]
        simp [mul_comm]
      · intro σ₁ _ σ₂ _ hne
        exact (distinguishable_iff_disjoint_subcubeSet _ _).mp
          (hdec.1.2 σ₁.val (mem_filter.mp σ₁.property).1 σ₂.val (mem_filter.mp σ₂.property).1
            (fun h => hne (Subtype.ext h)))
    have hRcard : Rset.card ≤ 2 * (S.biUnion tFun).card := by
      calc Rset.card ≤ ∑ τ ∈ S.biUnion tFun, (subcubeSet τ).card := card_biUnion_le
        _ = ∑ _τ ∈ S.biUnion tFun, 2 := Finset.sum_congr rfl fun τ hτ => by
            rcases mem_biUnion.mp hτ with ⟨_, _, hτ'⟩
            rw [card_subcubeSet, hw1 τ (mem_filter.mp (mem_filter.mp hτ').1).1]; norm_num
        _ = 2 * (S.biUnion tFun).card := by simp [mul_comm]
    have himg_sub : Lset.image flipJ ⊆ Rset := by
      intro y hy
      rcases mem_image.mp hy with ⟨x, hxL, rfl⟩
      rcases mem_biUnion.mp hxL with ⟨σ, hσS, hxσ⟩
      have hσD : σ.val ∈ D := (mem_filter.mp σ.property).1
      have hσj : σ.val j = 0 := (mem_filter.mp σ.property).2
      have hxj : x j = false := ((mem_filter.mp hxσ).2 j).1 hσj
      have hmem : flipJ x ∈ D.biUnion subcubeSet := by rw [hdec.2]; exact mem_univ _
      rcases mem_biUnion.mp hmem with ⟨τ, hτD, hfxτ⟩
      have hτj1 : τ j = 1 := by
        rcases fin3_cases (τ j) with hj | hj | hj
        · have := ((mem_filter.mp hfxτ).2 j).1 hj
          simp [flipJ, hxj] at this
        · exact hj
        · have hxτ : x ∈ subcubeSet τ := by
            refine mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩
            by_cases hij : i = j
            · subst hij; rw [hj]; constructor <;> intro h <;> exact absurd h (by decide)
            · have := (mem_filter.mp hfxτ).2 i
              simpa [flipJ, hij] using this
          have hστ : σ.val = τ := by
            by_contra hne
            exact Finset.disjoint_left.mp
              ((distinguishable_iff_disjoint_subcubeSet _ _).mp (hdec.1.2 _ hσD _ hτD hne)) hxσ hxτ
          rw [← hστ, hσj] at hj; exact absurd hj (by decide)
      have hrel : rel σ.val τ := by
        intro i hij hbad
        have hx1 := (mem_filter.mp hxσ).2 i
        have hx2 := (mem_filter.mp hfxτ).2 i
        have hfx_i : flipJ x i = x i := by simp [flipJ, hij]
        rw [hfx_i] at hx2
        rcases hbad with ⟨h0, h1⟩ | ⟨h1, h0⟩
        · have a := hx1.1 h0; have b := hx2.2 h1; rw [a] at b; exact Bool.false_ne_true b
        · have a := hx1.2 h1; have b := hx2.1 h0; rw [a] at b; exact Bool.false_ne_true b.symm
      exact mem_biUnion.mpr ⟨τ, mem_biUnion.mpr ⟨σ, hσS, mem_filter.mpr
        ⟨mem_filter.mpr ⟨hτD, hτj1⟩, hrel⟩⟩, hfxτ⟩
    have hle := card_le_card himg_sub
    rw [card_image_of_injective _ hflip_inj, hLcard] at hle
    omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective tFun).mp hHall
  let fB1 : B0 → B1 := fun σ => ⟨f σ, (mem_filter.mp (hfmem σ)).1⟩
  have hfB1_inj : Function.Injective fB1 := fun a b h => hfinj (congrArg Subtype.val h)
  have hfB1_bij : Function.Bijective fB1 :=
    (Fintype.bijective_iff_injective_and_card fB1).mpr ⟨hfB1_inj, by rw [Fintype.card_coe, Fintype.card_coe, hcard_B]⟩
  exact ⟨Equiv.ofBijective fB1 hfB1_bij, fun σ => (mem_filter.mp (hfmem σ)).2⟩
structure ReducedSetup (k n : ℕ) (C : TopEdgeLabeling (Fin (n * 2 ^ k + 1)) (Fin k)) where
  d : ℝ
  ε_stab : ℝ
  δ_red : ℝ
  ε_reg : ℝ
  t : ℕ
  m : ℕ
  V : Fin t → Finset (Fin (n * 2 ^ k + 1))
  R : SimpleGraph (Fin t)
  R_col : Fin k → SimpleGraph (Fin t)
  P : ProfilePartition R R_col
  D : Finset (Subcube k)
  hd_eq : d = 1 / (4 * (k : ℝ))
  hε_stab_eq : ε_stab = 1 / (1000 * ((2 ^ (k - 1) : ℕ) : ℝ))
  hδ_red_pos : 0 < δ_red
  hδ_red_small : δ_red ≤ 1 / (1000 * (k : ℝ) * ((2 ^ (k - 1) : ℕ) : ℝ))
  hε_reg_pos : 0 < ε_reg
  hε_reg_d2 : 12 * ε_reg ≤ d ^ 2
  hε_reg_6d : 6 * ε_reg / d ≤ δ_red / 4
  hε_reg_dens : 2 * (k : ℝ) * ε_reg ≤ δ_red / 2
  hε_reg_tiny : ε_reg ≤ 1 / ((2000 : ℝ) ^ 2 * (k : ℝ) * ((2 ^ (k - 1) : ℕ) : ℝ) ^ 4)
  ht_pos : 0 < t
  hm_pos : 0 < m
  hn_ge100 : 100 ≤ n
  hn_ge_t : t * t + 10 * t + 100 ≤ n
  hn'_ge : max 1000 (2 / δ_red) ≤ (t : ℝ) / ((2 ^ (k - 1) : ℕ) : ℝ)
  hm_big : (4 * ((t * t + 8 * t + 20 : ℕ) : ℝ) + 100) / ε_reg ≤ (m : ℝ)
  hm_ge_8δ : 8 / δ_red ≤ (m : ℝ)
  hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j)
  hVcard : ∀ i : Fin t, (V i).card = m
  htm_le : t * m ≤ n * 2 ^ k + 1
  hcover_m : ((n * 2 ^ k + 1 : ℕ) : ℝ) - (t : ℝ) * (m : ℝ) ≤ ε_reg * ((n * 2 ^ k + 1 : ℕ) : ℝ)
  hR_reg : ∀ c i j, (R_col c).Adj i j → (C.labelGraph c).IsUniform ε_reg (V i) (V j) ∧
    d ≤ ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ)
  hR_cover : ∀ i j, R.Adj i j → ∃ c : Fin k, (R_col c).Adj i j
  hR_sub : ∀ c i j, (R_col c).Adj i j → R.Adj i j
  hnonR_card : ∀ [DecidableRel R.Adj], ((((Finset.univ : Finset (Fin t)).offDiag.filter (fun ij : Fin t × Fin t => ¬ R.Adj ij.1 ij.2)).card : ℝ)) ≤
    (k : ℝ) * ε_reg * (t : ℝ) ^ 2
  hnomatch : ∀ c : Fin k, NoLargeOddConnMatching (R_col c) ((1 + δ_red) * ((t : ℝ) / ((2 ^ (k - 1) : ℕ) : ℝ)))
  hdec : IsDecomposition D
  hD_w1 : ∀ τ ∈ D, weight τ = 1
  hD_close : ∀ τ ∈ D, (1 - ε_stab) * ((t : ℝ) / ((2 ^ (k - 1) : ℕ) : ℝ)) < (P.vec τ : ℝ)
set_option maxHeartbeats 1200000 in
lemma build_reduced_setup (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ C : TopEdgeLabeling (Fin (n * 2 ^ k + 1)) (Fin k),
        (¬ ∃ c : Fin k, (cycleGraph (2 * n + 1)).IsContained (C.labelGraph c)) →
        Nonempty (ReducedSetup k n C) := by
  classical
  let K : ℕ := 2 ^ (k - 1)
  have hK_pos : 0 < K := Nat.pow_pos (by omega)
  have h2K : 2 * K = 2 ^ k := by
    dsimp only [K]; conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega), pow_succ']
  have hKr_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have hkr_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let ε_stab : ℝ := 1 / (1000 * (K : ℝ))
  have hε_stab_pos : 0 < ε_stab := by positivity
  have hε_stab_le : ε_stab ≤ 1 / 10 := by
    have hK2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 2 ≤ K from Nat.le_self_pow (by omega) 2)
    dsimp only [ε_stab]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨δ1, hδ1_pos, hred⟩ := theorem_red (k := k) hk hε_stab_pos hε_stab_le
  let d : ℝ := 1 / (4 * (k : ℝ))
  have hd0 : 0 < d := by positivity
  have hd1 : d ≤ 1 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    dsimp only [d]; rw [div_le_one (by positivity)]; linarith
  let δ_red : ℝ := min δ1 (1 / (1000 * (k : ℝ) * (K : ℝ)))
  have hδ_red_pos : 0 < δ_red := lt_min hδ1_pos (by positivity)
  have hδ_red_le1 : δ_red ≤ δ1 := min_le_left _ _
  have hδ_red_small : δ_red ≤ 1 / (1000 * (k : ℝ) * (K : ℝ)) := min_le_right _ _
  let ε_reg : ℝ := min (min (δ_red / (4 * (k : ℝ))) (d ^ 2 / 12))
    (min (d * δ_red / 24) (1 / ((2000 : ℝ) ^ 2 * (k : ℝ) * (K : ℝ) ^ 4)))
  have hε_reg_pos : 0 < ε_reg := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hε_reg_le1 : ε_reg ≤ 1 := by
    have h1 : ε_reg ≤ d ^ 2 / 12 := (min_le_left _ _).trans (min_le_right _ _)
    nlinarith [sq_nonneg d]
  have hε_reg_d2 : 12 * ε_reg ≤ d ^ 2 := by
    have h1 : ε_reg ≤ d ^ 2 / 12 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hε_reg_6d : 6 * ε_reg / d ≤ δ_red / 4 := by
    have h1 : ε_reg ≤ d * δ_red / 24 := (min_le_right _ _).trans (min_le_left _ _)
    rw [div_le_iff₀ hd0]; linarith
  have hε_reg_dens : 2 * (k : ℝ) * ε_reg ≤ δ_red / 2 := by
    have h1 : ε_reg ≤ δ_red / (4 * (k : ℝ)) := (min_le_left _ _).trans (min_le_left _ _)
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))).mp h1
    linarith
  have hε_reg_tiny : ε_reg ≤ 1 / ((2000 : ℝ) ^ 2 * (k : ℝ) * (K : ℝ) ^ 4) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let t0 : ℕ := max 1000 (Nat.ceil ((max 1000 (2 / δ_red)) * (K : ℝ)) + 1000 * K)
  have ht0_ge1 : 1 ≤ t0 := le_trans (by omega) (le_max_left _ _)
  obtain ⟨T0, N0, ht0_le_T0, hreg_lem⟩ :=
    multicolour_szemeredi_regularity (k := k) (by omega) hε_reg_pos hε_reg_le1 t0 ht0_ge1
  let M_req : ℕ := Nat.ceil ((4 * ((T0 * T0 + 8 * T0 + 20 : ℕ) : ℝ) + 100) / ε_reg) + 1000 +
    Nat.ceil (8 / δ_red)
  let N_thr : ℕ := max (max N0 (T0 * M_req + 100)) (max (T0 * T0 + 10 * T0 + 100) 100)
  rw [Filter.eventually_atTop]
  refine ⟨N_thr, fun n hn C hno => ?_⟩
  let N : ℕ := n * 2 ^ k + 1
  have hN_eq : N = 2 * K * n + 1 := by dsimp only [N]; rw [← h2K]; ring
  have hN_ge_N0 : N0 ≤ Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    have h1 : N0 ≤ N_thr := (le_max_left _ _).trans (le_max_left _ _)
    have h2 : n ≤ N := by dsimp only [N]; have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); nlinarith
    omega
  obtain ⟨t, m, V, ht_lo, ht_hi, hm1, hVdisj, hVcard, hcover_m, hreg_c⟩ :=
    hreg_lem (Fin N) (fun c => C.labelGraph c) hN_ge_N0
  rw [Fintype.card_fin] at hcover_m
  have ht_pos : 0 < t := by omega
  have hmr_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have htm_le_N : t * m ≤ N := by
    have hsum : (Finset.univ.biUnion V).card = t * m := by
      rw [card_biUnion (fun i _ j _ hij => hVdisj i j hij)]
      simp [hVcard]
    rw [← hsum]
    simpa [Fintype.card_fin] using card_le_univ (Finset.univ.biUnion V)
  have hm_ge_Mreq : (M_req : ℝ) ≤ (m : ℝ) := by
    have hN_ge_2TM : (2 * T0 * M_req : ℝ) ≤ (N : ℝ) := by
      have h1 : T0 * M_req ≤ n := le_trans (by omega) ((le_max_right N0 _).trans ((le_max_left _ _).trans hn))
      have h2 : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
      have h3 : 2 * T0 * M_req ≤ N := by dsimp only [N]; nlinarith
      exact_mod_cast h3
    have hε_lt_half : ε_reg ≤ 1 / 2 := by
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hKp : (1 : ℝ) ≤ (K : ℝ) ^ 4 := one_le_pow₀ hK1
      have hden : (2 : ℝ) ≤ (2000 : ℝ) ^ 2 * (k : ℝ) * (K : ℝ) ^ 4 := by nlinarith
      exact hε_reg_tiny.trans (one_div_le_one_div_of_le (by norm_num) hden)
    have htm_ge : (N : ℝ) / 2 ≤ (t : ℝ) * (m : ℝ) := by nlinarith
    have ht_le_T0_r : (t : ℝ) ≤ (T0 : ℝ) := by exact_mod_cast ht_hi
    have hT0_pos : (0 : ℝ) < (T0 : ℝ) := by exact_mod_cast (lt_of_lt_of_le ht0_ge1 ht0_le_T0)
    nlinarith
  have hm_big_base : (4 * ((t * t + 8 * t + 20 : ℕ) : ℝ) + 100) / ε_reg ≤ (m : ℝ) := by
    have h1 : (4 * ((T0 * T0 + 8 * T0 + 20 : ℕ) : ℝ) + 100) / ε_reg ≤ (M_req : ℝ) := by
      have hle_nat : Nat.ceil ((4 * ((T0 * T0 + 8 * T0 + 20 : ℕ) : ℝ) + 100) / ε_reg) ≤ M_req := by
        dsimp only [M_req]; omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast hle_nat)
    have h2 : (4 * ((t * t + 8 * t + 20 : ℕ) : ℝ) + 100) / ε_reg ≤
        (4 * ((T0 * T0 + 8 * T0 + 20 : ℕ) : ℝ) + 100) / ε_reg := by
      apply div_le_div_of_nonneg_right _ hε_reg_pos.le
      have : t * t + 8 * t + 20 ≤ T0 * T0 + 8 * T0 + 20 := by nlinarith
      have hr : ((t * t + 8 * t + 20 : ℕ) : ℝ) ≤ ((T0 * T0 + 8 * T0 + 20 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    exact (h2.trans h1).trans hm_ge_Mreq
  have hm_ge_8δ : 8 / δ_red ≤ (m : ℝ) := by
    have hle_nat : Nat.ceil (8 / δ_red) ≤ M_req := by dsimp only [M_req]; omega
    exact ((Nat.le_ceil _).trans (by exact_mod_cast hle_nat)).trans hm_ge_Mreq
  let R : SimpleGraph (Fin t) :=
    { Adj := fun i j => i ≠ j ∧ ∀ c : Fin k, (C.labelGraph c).IsUniform ε_reg (V i) (V j)
      symm := ⟨fun _ _ ⟨hne, hunif⟩ => ⟨hne.symm, fun c => (hunif c).symm⟩⟩
      loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩ }
  let R_col : Fin k → SimpleGraph (Fin t) := fun c =>
    { Adj := fun i j => R.Adj i j ∧ d ≤ ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ)
      symm := ⟨fun _ _ ⟨hadj, hd⟩ => ⟨hadj.symm, by rwa [edgeDensity_comm]⟩⟩
      loopless := ⟨fun _ ⟨hadj, _⟩ => R.loopless.irrefl _ hadj⟩ }
  have hR_sub : ∀ c u v, (R_col c).Adj u v → R.Adj u v := fun _ _ _ h => h.1
  have hR_cover : ∀ u v, R.Adj u v → ∃ c : Fin k, (R_col c).Adj u v := by
    intro i j hij
    have hsum_inter : ∑ c : Fin k, ((C.labelGraph c).interedges (V i) (V j)).card = m * m := by
      have hpart : (V i ×ˢ V j) = Finset.univ.biUnion (fun c : Fin k => (C.labelGraph c).interedges (V i) (V j)) := by
        ext ⟨u, v⟩
        simp only [mem_product, mem_biUnion, mem_univ, true_and,
          mem_interedges_iff, TopEdgeLabeling.labelGraph_adj]
        constructor
        · rintro ⟨hu, hv⟩
          have huv : u ≠ v := fun h => Finset.disjoint_left.mp (hVdisj i j hij.1) hu (h ▸ hv)
          exact ⟨C.get u v huv, hu, hv, huv, rfl⟩
        · rintro ⟨_, hu, hv, _⟩; exact ⟨hu, hv⟩
      have hdisj_c : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
          (fun c => (C.labelGraph c).interedges (V i) (V j)) := by
        intro c1 _ c2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        rintro ⟨u, v⟩ h1 h2
        rw [mem_interedges_iff, TopEdgeLabeling.labelGraph_adj] at h1 h2
        exact hne (h1.2.2.2.symm.trans h2.2.2.2)
      rw [← card_biUnion hdisj_c, ← hpart, card_product, hVcard i, hVcard j]
    have hsum_dens : ∑ c : Fin k, ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ) = 1 := by
      have h1 : ∀ c : Fin k, ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ) =
          (((C.labelGraph c).interedges (V i) (V j)).card : ℝ) / ((m : ℝ) * (m : ℝ)) := by
        intro c
        rw [edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
            Rat.cast_natCast, Rat.cast_natCast, hVcard i, hVcard j]
      simp_rw [h1, ← sum_div, ← Nat.cast_sum, hsum_inter, Nat.cast_mul]
      exact div_self (mul_ne_zero hmr_pos.ne' hmr_pos.ne')
    by_contra hall
    push Not at hall
    have hlt_all : ∀ c : Fin k, ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ) < d := fun c => by
      by_contra hge; push Not at hge; exact hall c ⟨hij, hge⟩
    have hsum_lt : ∑ c : Fin k, ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ) < (k : ℝ) * d := by
      have hne_k : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
      calc ∑ c : Fin k, ((C.labelGraph c).edgeDensity (V i) (V j) : ℝ)
          < ∑ _c : Fin k, d := sum_lt_sum_of_nonempty hne_k fun c _ => hlt_all c
        _ = (k : ℝ) * d := by simp
    have hkd : (k : ℝ) * d = 1 / 4 := by dsimp only [d]; field_simp
    linarith
  let nonR_ord : Finset (Fin t × Fin t) := (Finset.univ : Finset (Fin t)).offDiag.filter (fun ij => ¬ R.Adj ij.1 ij.2)
  have hnonR_ord_card : (nonR_ord.card : ℝ) ≤ (k : ℝ) * ε_reg * (t : ℝ) ^ 2 := by
    have hsub : nonR_ord ⊆ Finset.univ.biUnion (fun c : Fin k =>
        (Finset.univ : Finset (Fin t)).offDiag.filter (fun ij => ¬ (C.labelGraph c).IsUniform ε_reg (V ij.1) (V ij.2))) := by
      intro ij hij
      rw [mem_filter, mem_offDiag] at hij
      have hnot : ¬ ∀ c : Fin k, (C.labelGraph c).IsUniform ε_reg (V ij.1) (V ij.2) :=
        fun h => hij.2 ⟨hij.1.2.2, h⟩
      push Not at hnot
      obtain ⟨c, hc⟩ := hnot
      exact mem_biUnion.mpr ⟨c, mem_univ _, mem_filter.mpr ⟨mem_offDiag.mpr hij.1, hc⟩⟩
    calc (nonR_ord.card : ℝ)
        ≤ ((Finset.univ.biUnion (fun c : Fin k =>
            (Finset.univ : Finset (Fin t)).offDiag.filter
              (fun ij => ¬ (C.labelGraph c).IsUniform ε_reg (V ij.1) (V ij.2)))).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ c : Fin k, (((Finset.univ : Finset (Fin t)).offDiag.filter
            (fun ij => ¬ (C.labelGraph c).IsUniform ε_reg (V ij.1) (V ij.2))).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _c : Fin k, ε_reg * (t : ℝ) ^ 2 := sum_le_sum fun c _ => hreg_c c
      _ = (k : ℝ) * ε_reg * (t : ℝ) ^ 2 := by simp [mul_assoc]
  have hR_dense : (1 - δ_red) * ((Fintype.card (Fin t) : ℝ) * ((Fintype.card (Fin t) : ℝ) - 1) / 2) ≤
      (R.edgeFinset.card : ℝ) := by
    rw [Fintype.card_fin]
    have h2R : 2 * R.edgeFinset.card + nonR_ord.card = t * (t - 1) := by
      have hoff_card : (Finset.univ : Finset (Fin t)).offDiag.card = t * (t - 1) := by
        rw [offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub_left_distrib, mul_one]
      let R_ord := (Finset.univ : Finset (Fin t)).offDiag.filter (fun ij => R.Adj ij.1 ij.2)
      have hsplit : R_ord.card + nonR_ord.card = (Finset.univ : Finset (Fin t)).offDiag.card :=
        card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin t)).offDiag) (p := fun ij => R.Adj ij.1 ij.2)
      have hRord_eq : R_ord.card = 2 * R.edgeFinset.card := by
        have hbij : R_ord.card = ∑ e ∈ R.edgeFinset, (R_ord.filter (fun ij => s(ij.1, ij.2) = e)).card := by
          rw [← card_biUnion]
          · congr 1; ext ⟨a, b⟩
            simp only [R_ord, mem_biUnion, mem_filter, mem_offDiag, mem_univ,
              true_and, mem_edgeFinset]
            constructor
            · rintro ⟨hab_ne, hab⟩; exact ⟨s(a, b), hab, ⟨hab_ne, hab⟩, rfl⟩
            · rintro ⟨_, _, h1, _⟩; exact h1
          · intro e₁ _ e₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
            intro p h1 h2; exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
        rw [hbij]
        have h2each : ∀ e ∈ R.edgeFinset, (R_ord.filter (fun ij => s(ij.1, ij.2) = e)).card = 2 := by
          intro e he
          induction e using Sym2.ind with
          | _ a b =>
            have hab : R.Adj a b := mem_edgeFinset.mp he
            have hne : a ≠ b := R.ne_of_adj hab
            have heq : R_ord.filter (fun ij => s(ij.1, ij.2) = s(a, b)) = {(a, b), (b, a)} := by
              ext ⟨u, v⟩
              simp only [R_ord, mem_filter, mem_offDiag, mem_univ, true_and,
                mem_insert, mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
              constructor
              · rintro ⟨_, h⟩; exact h
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · exact ⟨⟨hne, hab⟩, Or.inl ⟨rfl, rfl⟩⟩
                · exact ⟨⟨hne.symm, hab.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
            rw [heq, card_pair (fun h => hne (congrArg Prod.fst h))]
        rw [Finset.sum_congr rfl h2each]; simp [mul_comm]
      omega
    have h2Rr : 2 * (R.edgeFinset.card : ℝ) + (nonR_ord.card : ℝ) = (t : ℝ) * ((t : ℝ) - 1) := by
      have ht1 : 1 ≤ t := by omega
      have hcast : ((t * (t - 1) : ℕ) : ℝ) = (t : ℝ) * ((t : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub ht1, Nat.cast_one]
      rw [← hcast]; exact_mod_cast h2R
    have ht2 : (t : ℝ) ^ 2 ≤ 2 * ((t : ℝ) * ((t : ℝ) - 1)) := by
      have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 2 ≤ t by omega)
      nlinarith
    have htt_nn : 0 ≤ (t : ℝ) * ((t : ℝ) - 1) := by
      have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
      nlinarith
    have hnon_le : (nonR_ord.card : ℝ) ≤ δ_red * ((t : ℝ) * ((t : ℝ) - 1)) := by
      calc (nonR_ord.card : ℝ) ≤ (k : ℝ) * ε_reg * (t : ℝ) ^ 2 := hnonR_ord_card
        _ ≤ (k : ℝ) * ε_reg * (2 * ((t : ℝ) * ((t : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ = (2 * (k : ℝ) * ε_reg) * ((t : ℝ) * ((t : ℝ) - 1)) := by ring
        _ ≤ δ_red * ((t : ℝ) * ((t : ℝ) - 1)) := mul_le_mul_of_nonneg_right (by linarith) htt_nn
    linarith
  let n' : ℝ := (t : ℝ) / (K : ℝ)
  have hn'_pos : 0 < n' := by positivity
  have hnomatch : ∀ c : Fin k, NoLargeOddConnMatching (R_col c) ((1 + δ_red) * n') := by
    intro c Ccomp hnb M hM hMC
    by_contra hge
    push Not at hge
    have hMne : M.Nonempty := card_pos.mp (by
      have : (0 : ℝ) < (M.card : ℝ) := by nlinarith
      exact_mod_cast this)
    have hfloor_ge : (1 - δ_red / 4) * (m : ℝ) - 1 ≤ (Nat.floor ((1 - 6 * ε_reg / d) * (m : ℝ)) : ℝ) := by
      have h1 : (1 - δ_red / 4) * (m : ℝ) ≤ (1 - 6 * ε_reg / d) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hmr_pos.le
      linarith [Nat.sub_one_lt_floor ((1 - 6 * ε_reg / d) * (m : ℝ))]
    have h1_le_δm : 1 ≤ (δ_red / 8) * (m : ℝ) := by
      have := (div_le_iff₀ hδ_red_pos).mp hm_ge_8δ; linarith
    have hfloor_ge2 : (1 - 3 * δ_red / 8) * (m : ℝ) ≤ (Nat.floor ((1 - 6 * ε_reg / d) * (m : ℝ)) : ℝ) := by linarith
    have hε_le_δ4 : ε_reg ≤ δ_red / 4 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith [hε_reg_dens]
    have htm_ge_N : (1 - δ_red / 4) * (N : ℝ) ≤ (t : ℝ) * (m : ℝ) := by nlinarith [hcover_m, hε_le_δ4]
    have h2n_lt_NK : (2 * n : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
      rw [le_div_iff₀ hKr_pos]
      have hNr : (N : ℝ) = 2 * (K : ℝ) * (n : ℝ) + 1 := by exact_mod_cast hN_eq
      linarith
    have hprod_ge : (2 * n : ℝ) ≤ ((2 * M.card * Nat.floor ((1 - 6 * ε_reg / d) * (m : ℝ)) : ℕ) : ℝ) := by
      push_cast
      have hδ_lt_half : δ_red ≤ 1 / 100 := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
        have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
        have hden : (100 : ℝ) ≤ 1000 * (k : ℝ) * (K : ℝ) := by nlinarith
        exact hδ_red_small.trans (one_div_le_one_div_of_le (by norm_num) hden)
      have hcoeff : 1 ≤ (1 + δ_red) * (1 - 3 * δ_red / 8) * (1 - δ_red / 4) := by nlinarith [sq_nonneg δ_red]
      have hnm : (1 - δ_red / 4) * ((N : ℝ) / (K : ℝ)) ≤ n' * (m : ℝ) := by
        dsimp only [n']; rw [← mul_div_assoc, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right htm_ge_N hKr_pos.le
      have hmul1 : (1 + δ_red) * n' * ((1 - 3 * δ_red / 8) * (m : ℝ)) ≤
          (2 * (M.card : ℝ)) * (Nat.floor ((1 - 6 * ε_reg / d) * (m : ℝ)) : ℝ) :=
        mul_le_mul hge hfloor_ge2 (by nlinarith) (by positivity)
      have hmul2 : (1 + δ_red) * (1 - 3 * δ_red / 8) * (1 - δ_red / 4) * ((N : ℝ) / (K : ℝ)) ≤
          (1 + δ_red) * n' * ((1 - 3 * δ_red / 8) * (m : ℝ)) := by
        have hre : (1 + δ_red) * n' * ((1 - 3 * δ_red / 8) * (m : ℝ)) =
            (1 + δ_red) * (1 - 3 * δ_red / 8) * (n' * (m : ℝ)) := by ring
        rw [hre, mul_assoc ((1 + δ_red) * (1 - 3 * δ_red / 8))]
        exact mul_le_mul_of_nonneg_left hnm (by nlinarith)
      have hmul3 : (N : ℝ) / (K : ℝ) ≤ (1 + δ_red) * (1 - 3 * δ_red / 8) * (1 - δ_red / 4) * ((N : ℝ) / (K : ℝ)) :=
        le_mul_of_one_le_left (div_nonneg (Nat.cast_nonneg _) hKr_pos.le) hcoeff
      exact h2n_lt_NK.trans (hmul3.trans (hmul2.trans hmul1))
    have hn_hi_nat : 2 * n ≤ 2 * M.card * Nat.floor ((1 - 6 * ε_reg / d) * (m : ℝ)) := by exact_mod_cast hprod_ge
    have hn_lo_nat : t * t + 6 * t + 10 ≤ 2 * n := by
      have h1 : T0 * T0 + 10 * T0 + 100 ≤ n := le_trans (le_max_left _ _) ((le_max_right _ _).trans hn)
      nlinarith
    have hm_big_nat : (4 * ((t * t + 4 * t + 10 : ℕ) : ℝ) + 100) / ε_reg ≤ (m : ℝ) := by
      refine le_trans ?_ hm_big_base
      apply div_le_div_of_nonneg_right _ hε_reg_pos.le
      have hr : ((t * t + 4 * t + 10 : ℕ) : ℝ) ≤ ((t * t + 8 * t + 20 : ℕ) : ℝ) := by
        exact_mod_cast (show t * t + 4 * t + 10 ≤ t * t + 8 * t + 20 by omega)
      linarith
    exact hno ⟨c, luczak_odd_cycle_of_odd_conn_matching (C.labelGraph c) V (R_col c)
      hε_reg_pos hd0 hd1 hε_reg_d2 hVdisj hVcard (fun i j hij => ⟨hij.1.2 c, hij.2⟩)
      Ccomp hnb M hM hMC hMne hm_big_nat hn_lo_nat hn_hi_nat⟩
  obtain ⟨P⟩ := exists_profilePartition R R_col
  have hn'_ge : max 1000 (2 / δ_red) ≤ n' := by
    have ht_ge : Nat.ceil ((max 1000 (2 / δ_red)) * (K : ℝ)) ≤ t :=
      le_trans (by omega) ((le_max_right 1000 _).trans ht_lo)
    have htr_ge : (max 1000 (2 / δ_red)) * (K : ℝ) ≤ (t : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast ht_ge)
    dsimp only [n']; exact (le_div_iff₀ hKr_pos).mpr htr_ge
  have hcard_t : (Fintype.card (Fin t) : ℝ) = (2 : ℝ) ^ (k - 1) * n' := by
    rw [Fintype.card_fin]; dsimp only [n', K]; push_cast; field_simp
  obtain ⟨xStar, hxStar, hdist⟩ := hred (Fin t) R R_col hR_cover hR_sub P δ_red n'
    hδ_red_pos hδ_red_le1 hn'_ge hcard_t hR_dense hnomatch
  obtain ⟨D, hdec, hDval, _⟩ := hxStar
  have hD_close : ∀ τ ∈ D, (1 - ε_stab) * n' < (P.vec τ : ℝ) := fun τ hτ => by
    have hdiff : |(P.vec τ : ℝ) / n' - xStar τ| < ε_stab :=
      lt_of_le_of_lt (single_le_sum (f := fun ρ => |(P.vec ρ : ℝ) / n' - xStar ρ|)
        (fun _ _ => abs_nonneg _) (mem_univ τ)) hdist
    rw [(hDval τ hτ).2, abs_lt] at hdiff
    exact (lt_div_iff₀ hn'_pos).mp (by linarith)
  have hn_ge100 : 100 ≤ n := le_trans (le_max_right _ _) ((le_max_right _ _).trans hn)
  have hn_ge_t : t * t + 10 * t + 100 ≤ n := by
    have h1 : T0 * T0 + 10 * T0 + 100 ≤ n := le_trans (le_max_left _ _) ((le_max_right _ _).trans hn)
    nlinarith
  exact ⟨⟨d, ε_stab, δ_red, ε_reg, t, m, V, R, R_col, P, D,
    rfl, rfl, hδ_red_pos, hδ_red_small, hε_reg_pos, hε_reg_d2, hε_reg_6d, hε_reg_dens, hε_reg_tiny,
    ht_pos, hm1, hn_ge100, hn_ge_t, hn'_ge, hm_big_base, hm_ge_8δ, hVdisj, hVcard, htm_le_N, hcover_m,
    fun c i j hij => ⟨hij.1.2 c, hij.2⟩, hR_cover, hR_sub, by intro _; convert hnonR_ord_card, hnomatch, hdec,
    fun τ hτ => (hDval τ hτ).1, hD_close⟩⟩
set_option maxHeartbeats 800000 in
lemma build_cores_and_good_part {k n : ℕ} (hk : 2 ≤ k)
    (C : TopEdgeLabeling (Fin (n * 2 ^ k + 1)) (Fin k))
    (hno : ¬ ∃ c : Fin k, (cycleGraph (2 * n + 1)).IsContained (C.labelGraph c))
    (S : ReducedSetup k n C) :
    let K : ℕ := 2 ^ (k - 1)
    let n' : ℝ := (S.t : ℝ) / (K : ℝ)
    let s0 : ℕ := Nat.floor ((1 - 2 * S.ε_stab) * n')
    ∃ (colOf : Subcube k → Fin k) (W' : Subcube k → Finset (Fin S.t))
      (Wtilde : Subcube k → Finset (Fin (n * 2 ^ k + 1))),
      (∀ σ ∈ S.D, (W' σ).card = s0) ∧
      (∀ σ ∈ S.D, ∀ τ ∈ S.D, σ ≠ τ → Disjoint (Wtilde σ) (Wtilde τ)) ∧
      (∀ σ ∈ S.D, Wtilde σ ⊆ (W' σ).biUnion S.V) ∧
      (∀ σ ∈ S.D, (s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ) ≤ ((Wtilde σ).card : ℝ)) ∧
      (∀ σ ∈ S.D, ∀ x ∈ Wtilde σ, ∀ y ∈ Wtilde σ, x ≠ y → (C.labelGraph (colOf σ)).Adj x y) ∧
      (∀ v : Fin (n * 2 ^ k + 1), ∃ σ ∈ S.D, ∀ j : Fin k, j ≠ colOf σ →
        ∀ i ∈ W' σ, (((C.labelGraph j).neighborFinset v ∩ S.V i).card : ℝ) < (S.d / 4) * (S.m : ℝ)) := by
  classical
  let K : ℕ := 2 ^ (k - 1)
  have hK_pos : 0 < K := Nat.pow_pos (by omega)
  have h2K : 2 * K = 2 ^ k := by
    dsimp only [K]; conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega), pow_succ']
  have hKr_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have hkr_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have htr_pos : (0 : ℝ) < (S.t : ℝ) := by exact_mod_cast S.ht_pos
  have hmr_pos : (0 : ℝ) < (S.m : ℝ) := by exact_mod_cast S.hm_pos
  let n' : ℝ := (S.t : ℝ) / (K : ℝ)
  have hn'_pos : 0 < n' := by positivity
  have hd0 : 0 < S.d := by rw [S.hd_eq]; positivity
  have hd1 : S.d ≤ 1 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    rw [S.hd_eq, div_le_one (by positivity)]; linarith
  have hε_reg_le1 : S.ε_reg ≤ 1 := by nlinarith [S.hε_reg_d2, sq_nonneg S.d]
  have hε_stab_lt : S.ε_stab < 1 / 10 := by
    have hK2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 2 ≤ K from Nat.le_self_pow (by omega) 2)
    rw [S.hε_stab_eq, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  let N : ℕ := n * 2 ^ k + 1
  have hN_eq : N = 2 * K * n + 1 := by dsimp only [N]; rw [← h2K]; ring
  have hex_col : ∀ σ : Subcube k, σ ∈ S.D → ∃ c : Fin k, σ c = 2 := fun σ hσ => by
    have hpos : 0 < (Finset.univ.filter (fun i : Fin k => σ i = 2)).card := by
      rw [← weight, S.hD_w1 σ hσ]; norm_num
    obtain ⟨c, hc⟩ := card_pos.mp hpos
    exact ⟨c, (mem_filter.mp hc).2⟩
  let colOf : Subcube k → Fin k := fun σ => if h : σ ∈ S.D then (hex_col σ h).choose else ⟨0, by omega⟩
  have hcolOf_eq : ∀ σ ∈ S.D, σ (colOf σ) = 2 := fun σ hσ => by
    dsimp only [colOf]; rw [dif_pos hσ]; exact (hex_col σ hσ).choose_spec
  have hcolOf_uniq : ∀ σ ∈ S.D, ∀ j : Fin k, σ j = 2 → j = colOf σ := fun σ hσ j hj => by
    have hcard1 : (Finset.univ.filter (fun i : Fin k => σ i = 2)).card = 1 := S.hD_w1 σ hσ
    exact card_le_one.mp hcard1.le
      j (mem_filter.mpr ⟨mem_univ _, hj⟩)
      (colOf σ) (mem_filter.mpr ⟨mem_univ _, hcolOf_eq σ hσ⟩)
  let η : ℝ := 1 / (2000 * (K : ℝ) ^ 2)
  have hη_pos : 0 < η := by positivity
  have hηt : η * (S.t : ℝ) = (S.ε_stab / 2) * n' := by
    rw [S.hε_stab_eq]; dsimp only [η, n', K]; field_simp; ring
  let nonR_ord := (Finset.univ : Finset (Fin S.t)).offDiag.filter (fun ij => ¬ S.R.Adj ij.1 ij.2)
  have hnonR_η : (nonR_ord.card : ℝ) ≤ η ^ 2 * (S.t : ℝ) ^ 2 := by
    have hke : (k : ℝ) * S.ε_reg ≤ η ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left S.hε_reg_tiny hkr_pos.le
      have h2 : (k : ℝ) * (1 / ((2000 : ℝ) ^ 2 * (k : ℝ) * (K : ℝ) ^ 4)) = η ^ 2 := by
        dsimp only [η, K]; field_simp
      linarith
    exact S.hnonR_card.trans (mul_le_mul_of_nonneg_right hke (sq_nonneg _))
  let GoodR : Finset (Fin S.t) := Finset.univ.filter (fun i =>
    (((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card : ℝ) ≤ η * (S.t : ℝ)))
  have hBadR_card : ((Finset.univ \ GoodR).card : ℝ) ≤ η * (S.t : ℝ) := by
    have hsum_le : ∑ i ∈ Finset.univ \ GoodR, ((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card : ℝ) ≤
        (nonR_ord.card : ℝ) := by
      have hnat : ∑ i ∈ Finset.univ \ GoodR, (Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card ≤
          nonR_ord.card := by
        have hsub : (Finset.univ \ GoodR).biUnion (fun i =>
            (Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).image (fun j => (i, j))) ⊆ nonR_ord := by
          intro ij hij
          rcases mem_biUnion.mp hij with ⟨i, _, hmem⟩
          rcases mem_image.mp hmem with ⟨j, hj, rfl⟩
          rw [mem_filter] at hj
          exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _, mem_univ _, hj.2.1.symm⟩, hj.2.2⟩
        calc ∑ i ∈ Finset.univ \ GoodR, (Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card
            = ∑ i ∈ Finset.univ \ GoodR, ((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).image (fun j => (i, j))).card :=
              Finset.sum_congr rfl fun i _ => (card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)).symm
          _ = ((Finset.univ \ GoodR).biUnion (fun i =>
                (Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).image (fun j => (i, j)))).card := by
              rw [card_biUnion]
              intro i₁ _ i₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
              intro p h1 h2
              rcases mem_image.mp h1 with ⟨_, _, rfl⟩
              rcases mem_image.mp h2 with ⟨_, _, heq⟩
              exact hne (congrArg Prod.fst heq).symm
          _ ≤ nonR_ord.card := card_le_card hsub
      exact_mod_cast hnat
    have hlow : ((Finset.univ \ GoodR).card : ℝ) * (η * (S.t : ℝ)) ≤
        ∑ i ∈ Finset.univ \ GoodR, ((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card : ℝ) := by
      calc ((Finset.univ \ GoodR).card : ℝ) * (η * (S.t : ℝ))
          = ∑ _i ∈ Finset.univ \ GoodR, η * (S.t : ℝ) := by simp
        _ ≤ ∑ i ∈ Finset.univ \ GoodR, ((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          rw [Finset.mem_sdiff, mem_filter] at hi
          have : ¬ ((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card : ℝ) ≤ η * (S.t : ℝ) :=
            fun h => hi.2 ⟨mem_univ _, h⟩
          linarith
    have hsq : η ^ 2 * (S.t : ℝ) ^ 2 = (η * (S.t : ℝ)) * (η * (S.t : ℝ)) := by ring
    exact le_of_mul_le_mul_right (by linarith [hnonR_η, hsum_le, hlow, hsq]) (mul_pos hη_pos htr_pos)
  let s0 : ℕ := Nat.floor ((1 - 2 * S.ε_stab) * n')
  have hs0_ge : (1 - 2 * S.ε_stab) * n' - 1 ≤ (s0 : ℝ) := by
    dsimp only [s0]; linarith [Nat.sub_one_lt_floor ((1 - 2 * S.ε_stab) * n')]
  have hs0_le : (s0 : ℝ) ≤ (1 - 2 * S.ε_stab) * n' :=
    Nat.floor_le (by nlinarith [hε_stab_lt, hn'_pos])
  have hs0_big : 100 ≤ s0 := by
    have h1 : (1000 : ℝ) ≤ n' := (le_max_left _ _).trans S.hn'_ge
    have h2 : (100 : ℝ) ≤ (s0 : ℝ) := by nlinarith
    exact_mod_cast h2
  have hex_W' : ∀ σ : Subcube k, σ ∈ S.D →
      ∃ T : Finset (Fin S.t), T ⊆ GoodR.filter (fun i => S.P.assign i = σ) ∧ T.card = s0 := by
    intro σ hσ
    apply exists_subset_card_eq
    have hW_ge : (1 - S.ε_stab) * n' < (S.P.vec σ : ℝ) := S.hD_close σ hσ
    have hsub : Finset.univ.filter (fun i => S.P.assign i = σ) ⊆
        GoodR.filter (fun i => S.P.assign i = σ) ∪ (Finset.univ \ GoodR) := by
      intro i hi
      by_cases hg : i ∈ GoodR
      · exact mem_union_left _ (mem_filter.mpr ⟨hg, (mem_filter.mp hi).2⟩)
      · exact mem_union_right _ (Finset.mem_sdiff.mpr ⟨mem_univ _, hg⟩)
    have hcard_r : (S.P.vec σ : ℝ) ≤ ((GoodR.filter (fun i => S.P.assign i = σ)).card : ℝ) + ((Finset.univ \ GoodR).card : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hge_r : (s0 : ℝ) ≤ ((GoodR.filter (fun i => S.P.assign i = σ)).card : ℝ) := by linarith
    exact_mod_cast hge_r
  let W' : Subcube k → Finset (Fin S.t) := fun σ => if h : σ ∈ S.D then (hex_W' σ h).choose else ∅
  have hW'_sub : ∀ σ ∈ S.D, W' σ ⊆ GoodR.filter (fun i => S.P.assign i = σ) := fun σ hσ => by
    dsimp only [W']; rw [dif_pos hσ]; exact (hex_W' σ hσ).choose_spec.1
  have hW'_card : ∀ σ ∈ S.D, (W' σ).card = s0 := fun σ hσ => by
    dsimp only [W']; rw [dif_pos hσ]; exact (hex_W' σ hσ).choose_spec.2
  have hW'_assign : ∀ σ ∈ S.D, ∀ i ∈ W' σ, S.P.assign i = σ := fun σ hσ i hi =>
    (mem_filter.mp (hW'_sub σ hσ hi)).2
  have hW'_good : ∀ σ ∈ S.D, ∀ i ∈ W' σ, i ∈ GoodR := fun σ hσ i hi =>
    (mem_filter.mp (hW'_sub σ hσ hi)).1
  have hW'_disj : ∀ σ ∈ S.D, ∀ τ ∈ S.D, σ ≠ τ → Disjoint (W' σ) (W' τ) := fun σ hσ τ hτ hne => by
    rw [Finset.disjoint_left]; intro i h1 h2
    exact hne ((hW'_assign σ hσ i h1).symm.trans (hW'_assign τ hτ i h2))
  have hW'_Rdeg : ∀ σ ∈ S.D, ∀ τ ∈ S.D, ∀ i ∈ W' σ,
      (9 / 10 : ℝ) * (s0 : ℝ) < (((W' τ).filter (S.R.Adj i)).card : ℝ) := by
    intro σ hσ τ hτ i hi
    have hnon_sub : (W' τ) \ (W' τ).filter (S.R.Adj i) ⊆
        insert i (Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)) := by
      intro j hj
      rw [Finset.mem_sdiff, mem_filter] at hj
      by_cases hji : j = i
      · exact mem_insert.mpr (Or.inl hji)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, hji, fun h => hj.2 ⟨hj.1, h⟩⟩))
    have h1 := card_sdiff_add_card_eq_card (filter_subset (S.R.Adj i) (W' τ))
    have h2 : ((W' τ) \ (W' τ).filter (S.R.Adj i)).card ≤
        (Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card + 1 :=
      (card_le_card hnon_sub).trans (card_insert_le _ _)
    have hgood := (mem_filter.mp (hW'_good σ hσ i hi)).2
    have h1r : (((W' τ) \ (W' τ).filter (S.R.Adj i)).card : ℝ) + (((W' τ).filter (S.R.Adj i)).card : ℝ) = (s0 : ℝ) := by
      rw [hW'_card τ hτ] at h1; exact_mod_cast h1
    have h2r : (((W' τ) \ (W' τ).filter (S.R.Adj i)).card : ℝ) ≤ η * (S.t : ℝ) + 1 := by
      have : (((W' τ) \ (W' τ).filter (S.R.Adj i)).card : ℝ) ≤
          ((Finset.univ.filter (fun j : Fin S.t => j ≠ i ∧ ¬ S.R.Adj i j)).card : ℝ) + 1 := by exact_mod_cast h2
      linarith
    have hn'1000 : (1000 : ℝ) ≤ n' := (le_max_left _ _).trans S.hn'_ge
    nlinarith [hs0_ge, hs0_le, hηt, hε_stab_lt]
  have hW'_mono : ∀ σ ∈ S.D, ∀ i ∈ W' σ, ∀ l ∈ W' σ, S.R.Adj i l → (S.R_col (colOf σ)).Adj i l := by
    intro σ hσ i hi l hl hil
    obtain ⟨c, hc⟩ := S.hR_cover i l hil
    have hc_eq : c = colOf σ := by
      apply hcolOf_uniq σ hσ c
      by_contra hne2
      have hbip := S.P.bipartite_edge c i l hc (by rw [hW'_assign σ hσ i hi]; exact hne2)
      rw [hW'_assign σ hσ i hi, hW'_assign σ hσ l hl] at hbip
      rcases hbip with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> (rw [h0] at h1; exact absurd h1 (by decide))
    rwa [← hc_eq]
  have hW'_no_same_col : ∀ σ ∈ S.D, ∀ τ ∈ S.D, σ ≠ τ → ∀ c : Fin k, σ c = 2 → τ c = 2 →
      ∀ i ∈ W' σ, ∀ l ∈ W' τ, ¬ (S.R_col c).Adj i l := by
    intro σ hσ τ hτ hne c hσc hτc i hi l hl hil
    have hcs : colOf σ = c := (hcolOf_uniq σ hσ c hσc).symm
    have hct : colOf τ = c := (hcolOf_uniq τ hτ c hτc).symm
    have hdeg_in : ∀ ρ ∈ S.D, colOf ρ = c → ∀ a ∈ W' ρ, 4 * (W' ρ).card < 5 * ((W' ρ).filter ((S.R_col c).Adj a)).card := by
      intro ρ hρ hcr a ha
      have hsub : (W' ρ).filter (S.R.Adj a) ⊆ (W' ρ).filter ((S.R_col c).Adj a) := fun b hb => by
        rw [mem_filter] at hb ⊢
        exact ⟨hb.1, hcr ▸ hW'_mono ρ hρ a ha b hb.1 hb.2⟩
      have h1 := hW'_Rdeg ρ hρ ρ hρ a ha
      have hle : (((W' ρ).filter (S.R.Adj a)).card : ℝ) ≤ (((W' ρ).filter ((S.R_col c).Adj a)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
      rw [hW'_card ρ hρ]
      have hgoal : (4 * s0 : ℝ) < (5 * ((W' ρ).filter ((S.R_col c).Adj a)).card : ℝ) := by linarith
      exact_mod_cast hgoal
    obtain ⟨M1, hM1, hM1_sub, hM1_card⟩ :=
      exists_internal_matching_of_high_min_deg (S.R_col c) (by rw [hW'_card σ hσ]; omega) (hdeg_in σ hσ hcs)
    obtain ⟨M2, hM2, hM2_sub, hM2_card⟩ :=
      exists_internal_matching_of_high_min_deg (S.R_col c) (by rw [hW'_card τ hτ]; omega) (hdeg_in τ hτ hct)
    let Cbig := (S.R_col c).connectedComponentMk i
    have hCbig_nb : ¬ IsBipartiteComponent (S.R_col c) Cbig.supp :=
      (S.P.nonbipartite_comp c i).mp (by rw [hW'_assign σ hσ i hi]; exact hσc)
    have hreach_in : ∀ ρ ∈ S.D, colOf ρ = c → ∀ a ∈ W' ρ, ∀ b ∈ W' ρ, (S.R_col c).Reachable a b := by
      intro ρ hρ hcr a ha b hb
      have hsub : ∀ x ∈ W' ρ, s0 < 2 * ((W' ρ).filter ((S.R_col c).Adj x)).card := fun x hx => by
        have h := hdeg_in ρ hρ hcr x hx; rw [hW'_card ρ hρ] at h; omega
      obtain ⟨W2, _⟩ := exists_len2_walk_bipartite (S.R_col c) (hW'_card ρ hρ) hsub ha hb
      exact ⟨W2⟩
    have hM_disj : Disjoint M1 M2 := by
      rw [Finset.disjoint_left]; intro e he1 he2
      induction e using Sym2.ind with
      | _ a b =>
        exact Finset.disjoint_left.mp (hW'_disj σ hσ τ hτ hne)
          (hM1_sub _ he1 a (Sym2.mem_mk_left a b)) (hM2_sub _ he2 a (Sym2.mem_mk_left a b))
    have hM12_match : IsMatching (S.R_col c) (M1 ∪ M2) := by
      refine ⟨fun e he => by rcases mem_union.mp he with h | h; exact hM1.1 e h; exact hM2.1 e h,
        fun e₁ he₁ e₂ he₂ hne' z ⟨hz1, hz2⟩ => ?_⟩
      rcases mem_union.mp he₁ with h1 | h1 <;> rcases mem_union.mp he₂ with h2 | h2
      · exact hM1.2 e₁ h1 e₂ h2 hne' z ⟨hz1, hz2⟩
      · exact Finset.disjoint_left.mp (hW'_disj σ hσ τ hτ hne) (hM1_sub e₁ h1 z hz1) (hM2_sub e₂ h2 z hz2)
      · exact Finset.disjoint_left.mp (hW'_disj σ hσ τ hτ hne) (hM1_sub e₂ h2 z hz2) (hM2_sub e₁ h1 z hz1)
      · exact hM2.2 e₁ h1 e₂ h2 hne' z ⟨hz1, hz2⟩
    have hM12_supp : ∀ e ∈ M1 ∪ M2, ∀ v ∈ e, v ∈ Cbig.supp := by
      intro e he v hv
      rcases mem_union.mp he with h1 | h2
      · exact ConnectedComponent.eq.mpr (hreach_in σ hσ hcs v (hM1_sub e h1 v hv) i hi)
      · exact ConnectedComponent.eq.mpr
          ((hreach_in τ hτ hct v (hM2_sub e h2 v hv) l hl).trans (Adj.reachable hil.symm))
    have hlt := S.hnomatch c Cbig hCbig_nb (M1 ∪ M2) hM12_match hM12_supp
    rw [card_union_of_disjoint hM_disj, hM1_card, hM2_card, hW'_card σ hσ, hW'_card τ hτ] at hlt
    have h2ge : (15 / 10 : ℝ) * n' ≤ ((2 * (s0 / 2 + s0 / 2) : ℕ) : ℝ) := by
      have h1 : (s0 : ℝ) ≤ ((2 * (s0 / 2) : ℕ) : ℝ) + 1 := by exact_mod_cast (show s0 ≤ 2 * (s0 / 2) + 1 by omega)
      have hn'1000 : (1000 : ℝ) ≤ n' := (le_max_left _ _).trans S.hn'_ge
      have h2s : ((2 * (s0 / 2 + s0 / 2) : ℕ) : ℝ) = 2 * ((2 * (s0 / 2) : ℕ) : ℝ) := by
        exact_mod_cast (show 2 * (s0 / 2 + s0 / 2) = 2 * (2 * (s0 / 2)) by omega)
      nlinarith [hs0_ge, hε_stab_lt]
    have hδ_lt_half : S.δ_red ≤ 1 / 10 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
      have hden : (10 : ℝ) ≤ 1000 * (k : ℝ) * (K : ℝ) := by nlinarith
      exact S.hδ_red_small.trans (one_div_le_one_div_of_le (by norm_num) hden)
    have hcast_lt : ((2 * (s0 / 2 + s0 / 2) : ℕ) : ℝ) < (1 + S.δ_red) * n' := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlt
    nlinarith
  have hex_partner_all : ∀ j : Fin k,
      let B0 := S.D.filter (fun σ => σ j = 0)
      let B1 := S.D.filter (fun σ => σ j = 1)
      ∃ e : B0 ≃ B1, ∀ σ : B0,
        ∀ i : Fin k, i ≠ j → ¬ ((σ.val i = 0 ∧ (e σ).val i = 1) ∨ (σ.val i = 1 ∧ (e σ).val i = 0)) :=
    fun j => exists_cube_partner S.hdec S.hD_w1 j
  choose ePart hePart using hex_partner_all
  let partner : Fin k → Subcube k → Subcube k := fun j σ =>
    if h0 : σ ∈ S.D.filter (fun ρ => ρ j = 0) then (ePart j ⟨σ, h0⟩).val
    else if h1 : σ ∈ S.D.filter (fun ρ => ρ j = 1) then ((ePart j).symm ⟨σ, h1⟩).val
    else σ
  have hpartner_mem : ∀ j σ, σ ∈ S.D → σ j ≠ 2 →
      partner j σ ∈ S.D ∧ ((σ j = 0 ∧ partner j σ j = 1) ∨ (σ j = 1 ∧ partner j σ j = 0)) ∧
      (∀ i : Fin k, i ≠ j → ¬ ((σ i = 0 ∧ partner j σ i = 1) ∨ (σ i = 1 ∧ partner j σ i = 0))) := by
    intro j σ hσ hne2
    rcases fin3_cases (σ j) with hj | hj | hj
    · have h0 : σ ∈ S.D.filter (fun ρ => ρ j = 0) := mem_filter.mpr ⟨hσ, hj⟩
      have hpeq : partner j σ = (ePart j ⟨σ, h0⟩).val := by dsimp only [partner]; rw [dif_pos h0]
      rw [hpeq]
      have hmem1 := mem_filter.mp (ePart j ⟨σ, h0⟩).property
      exact ⟨hmem1.1, Or.inl ⟨hj, hmem1.2⟩, hePart j ⟨σ, h0⟩⟩
    · have h0 : σ ∉ S.D.filter (fun ρ => ρ j = 0) := fun h => by
        have := (mem_filter.mp h).2; rw [hj] at this; exact absurd this (by decide)
      have h1 : σ ∈ S.D.filter (fun ρ => ρ j = 1) := mem_filter.mpr ⟨hσ, hj⟩
      have hpeq : partner j σ = ((ePart j).symm ⟨σ, h1⟩).val := by dsimp only [partner]; rw [dif_neg h0, dif_pos h1]
      rw [hpeq]
      have hmem0 := mem_filter.mp ((ePart j).symm ⟨σ, h1⟩).property
      refine ⟨hmem0.1, Or.inr ⟨hj, hmem0.2⟩, fun i hij hbad => ?_⟩
      have hspec := hePart j ((ePart j).symm ⟨σ, h1⟩) i hij
      rw [Equiv.apply_symm_apply] at hspec
      exact hspec (hbad.elim (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩) (fun ⟨a, b⟩ => Or.inl ⟨b, a⟩))
    · exact absurd hj hne2
  have hpartner_col : ∀ j σ, σ ∈ S.D → σ j ≠ 2 →
      ∀ a ∈ W' σ, ∀ b ∈ W' (partner j σ), S.R.Adj a b → (S.R_col j).Adj a b := by
    intro j σ hσ hne2 a ha b hb hab
    obtain ⟨hτD, hτj, hΔ⟩ := hpartner_mem j σ hσ hne2
    obtain ⟨c, hc⟩ := S.hR_cover a b hab
    have hcj : c = j := by
      by_contra hne
      by_cases hσc : σ c = 2
      · by_cases hτc : partner j σ c = 2
        · have hστ : σ ≠ partner j σ := fun h => by
            rcases hτj with ⟨h0, h1⟩ | ⟨h1, h0⟩
            · rw [← h, h0] at h1; exact absurd h1 (by decide)
            · rw [← h, h1] at h0; exact absurd h0 (by decide)
          exact hW'_no_same_col σ hσ (partner j σ) hτD hστ c hσc hτc a ha b hb hc
        · have hbip := S.P.bipartite_edge c b a hc.symm (by rw [hW'_assign _ hτD b hb]; exact hτc)
          rw [hW'_assign _ hτD b hb, hW'_assign σ hσ a ha, hσc] at hbip
          rcases hbip with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
      · have hbip := S.P.bipartite_edge c a b hc (by rw [hW'_assign σ hσ a ha]; exact hσc)
        rw [hW'_assign σ hσ a ha, hW'_assign _ hτD b hb] at hbip
        exact hΔ c hne hbip
    rwa [← hcj]
  have hpartner_deg : ∀ j σ, σ ∈ S.D → σ j ≠ 2 →
      (∀ a ∈ W' σ, s0 < 2 * ((W' (partner j σ)).filter ((S.R_col j).Adj a)).card) ∧
      (∀ b ∈ W' (partner j σ), s0 < 2 * ((W' σ).filter ((S.R_col j).Adj b)).card) := by
    intro j σ hσ hne2
    obtain ⟨hτD, _, _⟩ := hpartner_mem j σ hσ hne2
    constructor
    · intro a ha
      have hsub : (W' (partner j σ)).filter (S.R.Adj a) ⊆ (W' (partner j σ)).filter ((S.R_col j).Adj a) :=
        fun b hb => mem_filter.mpr ⟨(mem_filter.mp hb).1,
          hpartner_col j σ hσ hne2 a ha b (mem_filter.mp hb).1 (mem_filter.mp hb).2⟩
      have h1 := hW'_Rdeg σ hσ (partner j σ) hτD a ha
      have hle : (((W' (partner j σ)).filter (S.R.Adj a)).card : ℝ) ≤
          (((W' (partner j σ)).filter ((S.R_col j).Adj a)).card : ℝ) := by exact_mod_cast card_le_card hsub
      have hr : (s0 : ℝ) < 2 * (((W' (partner j σ)).filter ((S.R_col j).Adj a)).card : ℝ) := by linarith
      exact_mod_cast hr
    · intro b hb
      have hsub : (W' σ).filter (S.R.Adj b) ⊆ (W' σ).filter ((S.R_col j).Adj b) :=
        fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1,
          (hpartner_col j σ hσ hne2 a (mem_filter.mp ha).1 b hb (mem_filter.mp ha).2.symm).symm⟩
      have h1 := hW'_Rdeg (partner j σ) hτD σ hσ b hb
      have hle : (((W' σ).filter (S.R.Adj b)).card : ℝ) ≤ (((W' σ).filter ((S.R_col j).Adj b)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
      have hr : (s0 : ℝ) < 2 * (((W' σ).filter ((S.R_col j).Adj b)).card : ℝ) := by linarith
      exact_mod_cast hr
  have h2n_le_2s0 : 2 * n ≤ 2 * s0 * Nat.floor ((1 - 6 * S.ε_reg / S.d) * (S.m : ℝ)) := by
    have hfloor_ge : (1 - 3 * S.δ_red / 8) * (S.m : ℝ) ≤ (Nat.floor ((1 - 6 * S.ε_reg / S.d) * (S.m : ℝ)) : ℝ) := by
      have h1 : (1 - S.δ_red / 4) * (S.m : ℝ) ≤ (1 - 6 * S.ε_reg / S.d) * (S.m : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [S.hε_reg_6d]) hmr_pos.le
      have h2 : 1 ≤ (S.δ_red / 8) * (S.m : ℝ) := by have := (div_le_iff₀ S.hδ_red_pos).mp S.hm_ge_8δ; linarith
      linarith [Nat.sub_one_lt_floor ((1 - 6 * S.ε_reg / S.d) * (S.m : ℝ))]
    have hδ_lt_half : S.δ_red ≤ 1 / 10 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
      have hden : (10 : ℝ) ≤ 1000 * (k : ℝ) * (K : ℝ) := by nlinarith
      exact S.hδ_red_small.trans (one_div_le_one_div_of_le (by norm_num) hden)
    have hε_le_half : S.ε_reg ≤ 1 / 10 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith [S.hε_reg_dens]
    have htm_ge : (9 / 10 : ℝ) * (N : ℝ) ≤ (S.t : ℝ) * (S.m : ℝ) := by nlinarith [S.hcover_m]
    have hnm_ge : (9 / 10 : ℝ) * ((N : ℝ) / (K : ℝ)) ≤ n' * (S.m : ℝ) := by
      have h1 := div_le_div_of_nonneg_right htm_ge hKr_pos.le
      dsimp only [n']
      linarith [show (9 / 10 : ℝ) * ((N : ℝ) / (K : ℝ)) = (9 / 10 : ℝ) * (N : ℝ) / (K : ℝ) by ring,
        show (S.t : ℝ) / (K : ℝ) * (S.m : ℝ) = (S.t : ℝ) * (S.m : ℝ) / (K : ℝ) by ring]
    have h2n_le_NK : (2 * n : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
      rw [le_div_iff₀ hKr_pos]
      have hNr : (N : ℝ) = 2 * (K : ℝ) * (n : ℝ) + 1 := by exact_mod_cast hN_eq
      linarith only [hNr, show 2 * (n : ℝ) * (K : ℝ) = 2 * (K : ℝ) * (n : ℝ) by ring]
    have hs0_ge_half : (3 / 4 : ℝ) * n' ≤ (s0 : ℝ) := by
      have hn'1000 : (1000 : ℝ) ≤ n' := (le_max_left _ _).trans S.hn'_ge
      nlinarith [hs0_ge, hε_stab_lt]
    have hf_ge_half : (3 / 4 : ℝ) * (S.m : ℝ) ≤ (Nat.floor ((1 - 6 * S.ε_reg / S.d) * (S.m : ℝ)) : ℝ) := by nlinarith
    have hmul : (9 / 8 : ℝ) * (n' * (S.m : ℝ)) ≤ 2 * (s0 : ℝ) * (Nat.floor ((1 - 6 * S.ε_reg / S.d) * (S.m : ℝ)) : ℝ) := by
      have := mul_le_mul hs0_ge_half hf_ge_half (by positivity) (by positivity); nlinarith
    have hgoal_r : (2 * n : ℝ) ≤ ((2 * s0 * Nat.floor ((1 - 6 * S.ε_reg / S.d) * (S.m : ℝ)) : ℕ) : ℝ) := by
      push_cast; nlinarith [div_nonneg (Nat.cast_nonneg (α := ℝ) N) hKr_pos.le]
    exact_mod_cast hgoal_r
  have hex_nb : ∀ (σ : Subcube k) (hσ : σ ∈ S.D) (j : Fin k) (hj : σ j ≠ 2) (i : Fin S.t) (hi : i ∈ W' σ),
      ∃ l ∈ W' (partner j σ), (S.R_col j).Adj i l := fun σ hσ j hj i hi => by
    have hpos : 0 < ((W' (partner j σ)).filter ((S.R_col j).Adj i)).card := by
      have := (hpartner_deg j σ hσ hj).1 i hi; omega
    obtain ⟨l, hl⟩ := card_pos.mp hpos
    exact ⟨l, (mem_filter.mp hl).1, (mem_filter.mp hl).2⟩
  let V' : ∀ (σ : Subcube k) (_ : σ ∈ S.D) (i : Fin S.t) (_ : i ∈ W' σ), Finset (Fin N) := fun σ hσ i hi =>
    S.V i \ (Finset.univ.filter (fun j : Fin k => j ≠ colOf σ)).biUnion (fun j =>
      if hj : σ j ≠ 2 then
        (S.V i).filter (fun u =>
          (((C.labelGraph j).neighborFinset u ∩ S.V (hex_nb σ hσ j hj i hi).choose).card : ℝ) < (S.d / 4) * (S.m : ℝ))
      else ∅)
  have hV'_sub : ∀ σ hσ i hi, V' σ hσ i hi ⊆ S.V i := fun _ _ _ _ => sdiff_subset
  have hV'_card : ∀ σ hσ i hi, (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ) ≤ ((V' σ hσ i hi).card : ℝ) := by
    intro σ hσ i hi
    let BadU := (Finset.univ.filter (fun j : Fin k => j ≠ colOf σ)).biUnion (fun j =>
      if hj : σ j ≠ 2 then
        (S.V i).filter (fun u =>
          (((C.labelGraph j).neighborFinset u ∩ S.V (hex_nb σ hσ j hj i hi).choose).card : ℝ) < (S.d / 4) * (S.m : ℝ))
      else ∅)
    have hBadU_sub : BadU ⊆ S.V i := biUnion_subset.mpr fun j _ => by
      split_ifs; exact filter_subset _ _; exact empty_subset _
    have hBadU_card : (BadU.card : ℝ) ≤ (k : ℝ) * S.ε_reg * (S.m : ℝ) := by
      calc (BadU.card : ℝ)
          ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ colOf σ),
              ((if hj : σ j ≠ 2 then
                (S.V i).filter (fun u =>
                  (((C.labelGraph j).neighborFinset u ∩ S.V (hex_nb σ hσ j hj i hi).choose).card : ℝ) < (S.d / 4) * (S.m : ℝ))
              else ∅).card : ℝ) := by exact_mod_cast card_biUnion_le
        _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin k => j ≠ colOf σ), S.ε_reg * (S.m : ℝ) := by
            refine sum_le_sum fun j _ => ?_
            split_ifs with hj
            · let l := (hex_nb σ hσ j hj i hi).choose
              have hadj : (S.R_col j).Adj i l := (hex_nb σ hσ j hj i hi).choose_spec.2
              have hreg := S.hR_reg j i l hadj
              have hδ_le_d : S.ε_reg ≤ S.d / 12 := by nlinarith [S.hε_reg_d2, hd1]
              have hsub : (S.V i).filter (fun u => (((C.labelGraph j).neighborFinset u ∩ S.V l).card : ℝ) < (S.d / 4) * (S.m : ℝ)) ⊆
                  (S.V i).filter (fun u => (((C.labelGraph j).neighborFinset u ∩ S.V l).card : ℝ) <
                    (((C.labelGraph j).edgeDensity (S.V i) (S.V l) : ℝ) - S.ε_reg) * ((S.V l).card : ℝ)) := by
                intro u hu; rw [mem_filter] at hu ⊢
                exact ⟨hu.1, lt_of_lt_of_le hu.2 (by rw [S.hVcard l]; nlinarith [hreg.2, hmr_pos])⟩
              have h1 : (((S.V i).filter (fun u => (((C.labelGraph j).neighborFinset u ∩ S.V l).card : ℝ) < (S.d / 4) * (S.m : ℝ))).card : ℝ) ≤
                  (((S.V i).filter (fun u => (((C.labelGraph j).neighborFinset u ∩ S.V l).card : ℝ) <
                    (((C.labelGraph j).edgeDensity (S.V i) (S.V l) : ℝ) - S.ε_reg) * ((S.V l).card : ℝ))).card : ℝ) := by
                exact_mod_cast card_le_card hsub
              have h2 := typical_degree_bound_le (C.labelGraph j) hreg.1 (Finset.Subset.refl (S.V l))
                (by rw [S.hVcard l]; nlinarith [hmr_pos, hε_reg_le1])
              rw [S.hVcard i] at h2; linarith
            · simp; exact mul_nonneg S.hε_reg_pos.le hmr_pos.le
        _ ≤ ∑ _j : Fin k, S.ε_reg * (S.m : ℝ) := sum_le_univ_sum_of_nonneg (fun _ => mul_nonneg S.hε_reg_pos.le hmr_pos.le)
        _ = (k : ℝ) * S.ε_reg * (S.m : ℝ) := by simp [mul_assoc]
    have hsplit := card_sdiff_add_card_eq_card hBadU_sub
    have hsplit_r : ((V' σ hσ i hi).card : ℝ) + (BadU.card : ℝ) = (S.m : ℝ) := by
      change ((S.V i \ BadU).card : ℝ) + (BadU.card : ℝ) = (S.m : ℝ)
      rw [S.hVcard i] at hsplit; exact_mod_cast hsplit
    linarith
  let Wtilde : Subcube k → Finset (Fin N) := fun σ =>
    if hσ : σ ∈ S.D then (W' σ).attach.biUnion (fun i => V' σ hσ i.val i.property) else ∅
  have hWtilde_eq : ∀ σ (hσ : σ ∈ S.D), Wtilde σ = (W' σ).attach.biUnion (fun i => V' σ hσ i.val i.property) :=
    fun σ hσ => dif_pos hσ
  have hWtilde_sub_V : ∀ σ ∈ S.D, Wtilde σ ⊆ (W' σ).biUnion S.V := by
    intro σ hσ x hx
    rw [hWtilde_eq σ hσ] at hx
    rcases mem_biUnion.mp hx with ⟨i, _, hxi⟩
    exact mem_biUnion.mpr ⟨i.val, i.property, hV'_sub σ hσ i.val i.property hxi⟩
  have hWtilde_disj : ∀ σ ∈ S.D, ∀ τ ∈ S.D, σ ≠ τ → Disjoint (Wtilde σ) (Wtilde τ) := by
    intro σ hσ τ hτ hne
    rw [Finset.disjoint_left]; intro x h1 h2
    rcases mem_biUnion.mp (hWtilde_sub_V σ hσ h1) with ⟨i1, hi1, hx1⟩
    rcases mem_biUnion.mp (hWtilde_sub_V τ hτ h2) with ⟨i2, hi2, hx2⟩
    have hi_ne : i1 ≠ i2 := fun h => Finset.disjoint_left.mp (hW'_disj σ hσ τ hτ hne) hi1 (h ▸ hi2)
    exact Finset.disjoint_left.mp (S.hVdisj i1 i2 hi_ne) hx1 hx2
  have hWtilde_card : ∀ σ ∈ S.D, (s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ) ≤ ((Wtilde σ).card : ℝ) := by
    intro σ hσ
    rw [hWtilde_eq σ hσ]
    have hdisj_i : ((W' σ).attach : Set {i // i ∈ W' σ}).PairwiseDisjoint (fun i => V' σ hσ i.val i.property) := by
      intro i1 _ i2 _ hne
      exact Disjoint.mono (hV'_sub σ hσ i1.val i1.property) (hV'_sub σ hσ i2.val i2.property)
        (S.hVdisj i1.val i2.val (fun h => hne (Subtype.ext h)))
    rw [card_biUnion hdisj_i, Nat.cast_sum]
    calc (s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ)
        = ∑ _i ∈ (W' σ).attach, (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ) := by
            rw [sum_const, card_attach, hW'_card σ hσ, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ (W' σ).attach, ((V' σ hσ i.val i.property).card : ℝ) :=
            sum_le_sum fun i _ => hV'_card σ hσ i.val i.property
  have hcomp : ∀ σ ∈ S.D, ∀ x ∈ Wtilde σ, ∀ y ∈ Wtilde σ, x ≠ y → (C.labelGraph (colOf σ)).Adj x y := by
    intro σ hσ x hx y hy hxy
    let j := C.get x y hxy
    have hxy_j : (C.labelGraph j).Adj x y := by rw [TopEdgeLabeling.labelGraph_adj]; exact ⟨hxy, rfl⟩
    suffices hj_eq : j = colOf σ by rwa [← hj_eq]
    by_contra hj_ne
    have hσj_ne2 : σ j ≠ 2 := fun h2 => hj_ne (hcolOf_uniq σ hσ j h2)
    rw [hWtilde_eq σ hσ] at hx hy
    rcases mem_biUnion.mp hx with ⟨ix, _, hxv⟩
    rcases mem_biUnion.mp hy with ⟨iy, _, hyv⟩
    let τ := partner j σ
    obtain ⟨hτD, hτj, _⟩ := hpartner_mem j σ hσ hσj_ne2
    have hστ : σ ≠ τ := fun h => by
      dsimp only [τ] at h
      rcases hτj with ⟨h0, h1⟩ | ⟨h1, h0⟩
      · rw [← h, h0] at h1; exact absurd h1 (by decide)
      · rw [← h, h1] at h0; exact absurd h0 (by decide)
    let c1 : Fin S.t := (hex_nb σ hσ j hσj_ne2 ix.val ix.property).choose
    have hc1_mem : c1 ∈ W' τ := (hex_nb σ hσ j hσj_ne2 ix.val ix.property).choose_spec.1
    let c2 : Fin S.t := (hex_nb σ hσ j hσj_ne2 iy.val iy.property).choose
    have hc2_mem : c2 ∈ W' τ := (hex_nb σ hσ j hσj_ne2 iy.val iy.property).choose_spec.1
    have hx_deg : (S.d / 4) * (S.m : ℝ) ≤ (((C.labelGraph j).neighborFinset x ∩ S.V c1).card : ℝ) := by
      by_contra hlt; push Not at hlt
      exact (Finset.mem_sdiff.mp hxv).2 (mem_biUnion.mpr
        ⟨j, mem_filter.mpr ⟨mem_univ _, hj_ne⟩, by
          rw [dif_pos hσj_ne2]; exact mem_filter.mpr ⟨(Finset.mem_sdiff.mp hxv).1, hlt⟩⟩)
    have hy_deg : (S.d / 4) * (S.m : ℝ) ≤ (((C.labelGraph j).neighborFinset y ∩ S.V c2).card : ℝ) := by
      by_contra hlt; push Not at hlt
      exact (Finset.mem_sdiff.mp hyv).2 (mem_biUnion.mpr
        ⟨j, mem_filter.mpr ⟨mem_univ _, hj_ne⟩, by
          rw [dif_pos hσj_ne2]; exact mem_filter.mpr ⟨(Finset.mem_sdiff.mp hyv).1, hlt⟩⟩)
    obtain ⟨A, B, hAinj, hBinj, hAW, hBW, hAB_adj⟩ :=
      exists_bipartite_matching_of_high_min_deg (S.R_col j) (hW'_card σ hσ) (hW'_card τ hτD)
        (hpartner_deg j σ hσ hσj_ne2).1 (hpartner_deg j σ hσ hσj_ne2).2
    have hAB_ne : ∀ r1 r2 : Fin s0, A r1 ≠ B r2 := fun r1 r2 h =>
      Finset.disjoint_left.mp (hW'_disj σ hσ τ hτD hστ) (hAW r1) (h ▸ hBW r2)
    have hs0_1 : 1 ≤ s0 := by omega
    obtain ⟨P_start, hPs_len⟩ := exists_len3_walk_bipartite (S.R_col j) (hW'_card σ hσ) (hW'_card τ hτD)
      (hpartner_deg j σ hσ hσj_ne2).1 (hpartner_deg j σ hσ hσj_ne2).2 (hAW ⟨0, hs0_1⟩) hc1_mem
    let P_start' : (S.R_col j).Walk c1 (A ⟨0, hs0_1⟩) := P_start.reverse
    have hPs'_len : P_start'.length = 3 := by rw [Walk.length_reverse, hPs_len]
    have hex_mid : ∀ r : Fin (s0 - 1), ∃ W : (S.R_col j).Walk (B ⟨r.val, by omega⟩) (A ⟨r.val + 1, by omega⟩), W.length = 3 :=
      fun r => by
        obtain ⟨W, hW⟩ := exists_len3_walk_bipartite (S.R_col j) (hW'_card σ hσ) (hW'_card τ hτD)
          (hpartner_deg j σ hσ hσj_ne2).1 (hpartner_deg j σ hσ hσj_ne2).2
          (hAW ⟨r.val + 1, by omega⟩) (hBW ⟨r.val, by omega⟩)
        exact ⟨W.reverse, by rw [Walk.length_reverse, hW]⟩
    choose P_mid hPmid_len using hex_mid
    obtain ⟨P_end, hPend_len⟩ := exists_len2_walk_bipartite (S.R_col j) (hW'_card σ hσ)
      (hpartner_deg j σ hσ hσj_ne2).2 (hBW ⟨s0 - 1, by omega⟩) hc2_mem
    have hsum_mid : ∑ r : Fin (s0 - 1), (P_mid r).length = 3 * (s0 - 1) := by
      rw [Finset.sum_congr rfl fun r _ => hPmid_len r]; simp [mul_comm]
    have hs0_le_t : s0 ≤ S.t := by rw [← hW'_card σ hσ]; exact (card_le_univ _).trans (by simp)
    have hLsk_le : P_start'.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + s0 + 10 ≤ S.t * S.t + 8 * S.t + 20 := by
      rw [hPs'_len, hsum_mid, hPend_len]; omega
    have hm_cond : (4 * ((P_start'.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + s0 + 10 : ℕ) : ℝ) + 100) / S.ε_reg ≤ (S.m : ℝ) := by
      refine le_trans ?_ S.hm_big
      apply div_le_div_of_nonneg_right _ S.hε_reg_pos.le
      have hr : ((P_start'.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + s0 + 10 : ℕ) : ℝ) ≤
          ((S.t * S.t + 8 * S.t + 20 : ℕ) : ℝ) := by exact_mod_cast hLsk_le
      linarith
    have hn_lo : P_start'.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + 3 * s0 + 4 ≤ 2 * n := by
      have := S.hn_ge_t; rw [hPs'_len, hsum_mid, hPend_len]; omega
    exact hno ⟨j, luczak_odd_cycle_of_edge_and_matching (C.labelGraph j) S.V (S.R_col j)
      S.hε_reg_pos hd0 hd1 S.hε_reg_d2 S.hVdisj S.hVcard (S.hR_reg j)
      hs0_1 A B hAB_adj hAinj hBinj hAB_ne P_start' P_mid P_end
      (by rw [hPs'_len, hsum_mid, hPend_len]; omega)
      hxy_j hx_deg hy_deg hm_cond hn_lo h2n_le_2s0⟩
  let IsHeavy : Fin N → Fin k → Subcube k → Prop := fun v j σ =>
    ∃ i ∈ W' σ, (S.d / 4) * (S.m : ℝ) ≤ (((C.labelGraph j).neighborFinset v ∩ S.V i).card : ℝ)
  have hW'_conn : ∀ j σ, σ ∈ S.D → σ j ≠ 2 → ∀ a ∈ W' σ, ∀ b ∈ W' σ, (S.R_col j).Reachable a b := by
    intro j σ hσ hne2 a ha b hb
    obtain ⟨hτD, _, _⟩ := hpartner_mem j σ hσ hne2
    obtain ⟨W2, _⟩ := exists_len2_walk_bipartite (S.R_col j) (hW'_card (partner j σ) hτD)
      (hpartner_deg j σ hσ hne2).1 ha hb
    exact ⟨W2⟩
  have hW'_ne : ∀ σ ∈ S.D, (W' σ).Nonempty := fun σ hσ => card_pos.mp (by rw [hW'_card σ hσ]; omega)
  have hno_both_heavy : ∀ (v : Fin N) (j : Fin k) (σ τ : Subcube k) (hσ : σ ∈ S.D) (hτ : τ ∈ S.D),
      σ j = 0 → τ j = 1 →
      (S.R_col j).connectedComponentMk (hW'_ne σ hσ).choose = (S.R_col j).connectedComponentMk (hW'_ne τ hτ).choose →
      IsHeavy v j σ → IsHeavy v j τ → False := by
    intro v j σ τ hσ hτ hσ0 hτ1 hsame ⟨c1, hc1W, hv1⟩ ⟨c2, hc2W, hv2⟩
    have hσ_ne2 : σ j ≠ 2 := by rw [hσ0]; decide
    let τ0 := partner j σ
    obtain ⟨hτ0D, hτ0j, _⟩ := hpartner_mem j σ hσ hσ_ne2
    have hτ01 : τ0 j = 1 := by
      rcases hτ0j with ⟨_, h1⟩ | ⟨h1, _⟩; exact h1; rw [hσ0] at h1; exact absurd h1 (by decide)
    have hστ0 : σ ≠ τ0 := fun h => by rw [← h, hσ0] at hτ01; exact absurd hτ01 (by decide)
    obtain ⟨A, B, hAinj, hBinj, hAW, hBW, hAB_adj⟩ :=
      exists_bipartite_matching_of_high_min_deg (S.R_col j) (hW'_card σ hσ) (hW'_card τ0 hτ0D)
        (hpartner_deg j σ hσ hσ_ne2).1 (hpartner_deg j σ hσ hσ_ne2).2
    have hAB_ne : ∀ r1 r2 : Fin s0, A r1 ≠ B r2 := fun r1 r2 h =>
      Finset.disjoint_left.mp (hW'_disj σ hσ τ0 hτ0D hστ0) (hAW r1) (h ▸ hBW r2)
    have hs0_1 : 1 ≤ s0 := by omega
    obtain ⟨P_start, hPs_len⟩ := exists_len2_walk_bipartite (S.R_col j) (hW'_card τ0 hτ0D)
      (hpartner_deg j σ hσ hσ_ne2).1 hc1W (hAW ⟨0, hs0_1⟩)
    have hex_mid : ∀ r : Fin (s0 - 1), ∃ W : (S.R_col j).Walk (B ⟨r.val, by omega⟩) (A ⟨r.val + 1, by omega⟩), W.length = 3 :=
      fun r => by
        obtain ⟨W, hW⟩ := exists_len3_walk_bipartite (S.R_col j) (hW'_card σ hσ) (hW'_card τ0 hτ0D)
          (hpartner_deg j σ hσ hσ_ne2).1 (hpartner_deg j σ hσ hσ_ne2).2
          (hAW ⟨r.val + 1, by omega⟩) (hBW ⟨r.val, by omega⟩)
        exact ⟨W.reverse, by rw [Walk.length_reverse, hW]⟩
    choose P_mid hPmid_len using hex_mid
    have hreach_end : (S.R_col j).Reachable (B ⟨s0 - 1, by omega⟩) c2 := by
      have h1 : (S.R_col j).Reachable (B ⟨s0 - 1, by omega⟩) (A ⟨s0 - 1, by omega⟩) :=
        Adj.reachable (hAB_adj ⟨s0 - 1, by omega⟩).symm
      have h2 : (S.R_col j).Reachable (A ⟨s0 - 1, by omega⟩) (hW'_ne σ hσ).choose :=
        hW'_conn j σ hσ hσ_ne2 _ (hAW ⟨s0 - 1, by omega⟩) _ (hW'_ne σ hσ).choose_spec
      have h3 : (S.R_col j).Reachable (hW'_ne σ hσ).choose (hW'_ne τ hτ).choose :=
        ConnectedComponent.eq.mp hsame
      have h4 : (S.R_col j).Reachable (hW'_ne τ hτ).choose c2 :=
        hW'_conn j τ hτ (by rw [hτ1]; decide) _ (hW'_ne τ hτ).choose_spec _ hc2W
      exact ((h1.trans h2).trans h3).trans h4
    obtain ⟨P_end, hPend_lt⟩ := exists_short_walk hreach_end
    have hPend_even : P_end.length % 2 = 0 := by
      have hB1 : S.P.assign (B ⟨s0 - 1, by omega⟩) j = 1 := by
        rw [hW'_assign τ0 hτ0D _ (hBW ⟨s0 - 1, by omega⟩)]; exact hτ01
      have hc2_1 : S.P.assign c2 j = 1 := by rw [hW'_assign τ hτ _ hc2W]; exact hτ1
      exact (walk_parity_of_profile S.P j P_end (by rw [hB1]; decide)).2.mpr (hB1.trans hc2_1.symm)
    have hsum_mid : ∑ r : Fin (s0 - 1), (P_mid r).length = 3 * (s0 - 1) := by
      rw [Finset.sum_congr rfl fun r _ => hPmid_len r]; simp [mul_comm]
    have hs0_le_t : s0 ≤ S.t := by rw [← hW'_card σ hσ]; exact (card_le_univ _).trans (by simp)
    have hLsk_le : P_start.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + s0 + 10 ≤ S.t * S.t + 8 * S.t + 20 := by
      rw [hPs_len, hsum_mid]; omega
    have hm_cond : (4 * ((P_start.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + s0 + 10 : ℕ) : ℝ) + 100) / S.ε_reg ≤ (S.m : ℝ) := by
      refine le_trans ?_ S.hm_big
      apply div_le_div_of_nonneg_right _ S.hε_reg_pos.le
      have hr : ((P_start.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + s0 + 10 : ℕ) : ℝ) ≤
          ((S.t * S.t + 8 * S.t + 20 : ℕ) : ℝ) := by exact_mod_cast hLsk_le
      linarith
    have hn_lo : P_start.length + (∑ r : Fin (s0 - 1), (P_mid r).length) + P_end.length + 3 * s0 + 4 ≤ 2 * n := by
      have := S.hn_ge_t; rw [hPs_len, hsum_mid]; omega
    exact hno ⟨j, luczak_odd_cycle_of_vertex_and_matching (C.labelGraph j) S.V (S.R_col j)
      S.hε_reg_pos hd0 hd1 S.hε_reg_d2 S.hVdisj S.hVcard (S.hR_reg j)
      hs0_1 A B hAB_adj hAinj hBinj hAB_ne P_start P_mid P_end
      (by rw [hPs_len, hsum_mid]; omega)
      hv1 hv2 hm_cond hn_lo h2n_le_2s0⟩
  have hD_card : S.D.card = K := by
    have hsum := (sum_two_pow_weight_le S.hdec.1).2.mpr S.hdec
    have h2D : ∑ τ ∈ S.D, 2 ^ weight τ = 2 * S.D.card := by
      rw [Finset.sum_congr rfl (fun τ hτ => by rw [S.hD_w1 τ hτ])]; simp [mul_comm]
    rw [h2D] at hsum; omega
  have hex_good_part : ∀ v : Fin N, ∃ σ ∈ S.D, ∀ j : Fin k, j ≠ colOf σ →
      ∀ i ∈ W' σ, (((C.labelGraph j).neighborFinset v ∩ S.V i).card : ℝ) < (S.d / 4) * (S.m : ℝ) := by
    intro v
    let flipComp : ∀ (j : Fin k), (S.R_col j).ConnectedComponent → Bool := fun j Ccomp =>
      decide (∃ τ : Subcube k, ∃ hτ : τ ∈ S.D, τ j = 1 ∧
        (S.R_col j).connectedComponentMk (hW'_ne τ hτ).choose = Ccomp ∧ IsHeavy v j τ)
    let φ : Subcube k → Subcube k := fun σ j =>
      if hσ : σ ∈ S.D then
        if σ j = 2 then 2
        else if flipComp j ((S.R_col j).connectedComponentMk (hW'_ne σ hσ).choose) then
          if σ j = 0 then 1 else 0
        else σ j
      else σ j
    have hφ_w1 : ∀ σ ∈ S.D, weight (φ σ) = 1 := fun σ hσ => by
      have heq : Finset.univ.filter (fun j : Fin k => φ σ j = 2) = Finset.univ.filter (fun j : Fin k => σ j = 2) := by
        ext j; simp only [mem_filter, mem_univ, true_and, φ, dif_pos hσ]
        by_cases h2 : σ j = 2
        · simp [h2]
        · simp only [if_neg h2]; split_ifs <;> simp [h2]
      change (Finset.univ.filter (fun j : Fin k => φ σ j = 2)).card = 1
      rw [heq]; exact S.hD_w1 σ hσ
    have hφ_dist : ∀ σ ∈ S.D, ∀ τ ∈ S.D, σ ≠ τ → distinguishable (φ σ) (φ τ) := by
      intro σ hσ τ hτ hne
      let a := (hW'_ne σ hσ).choose
      have ha : a ∈ W' σ := (hW'_ne σ hσ).choose_spec
      have hpos : 0 < ((W' τ).filter (S.R.Adj a)).card := by
        have h := hW'_Rdeg σ hσ τ hτ a ha
        have : (0 : ℝ) < (((W' τ).filter (S.R.Adj a)).card : ℝ) := by linarith
        exact_mod_cast this
      obtain ⟨b, hb⟩ := card_pos.mp hpos
      rw [mem_filter] at hb
      obtain ⟨j, hj_adj⟩ := S.hR_cover a b hb.2
      have hσj_ne2 : σ j ≠ 2 := by
        intro h2
        by_cases hτ2 : τ j = 2
        · exact hW'_no_same_col σ hσ τ hτ hne j h2 hτ2 a ha b hb.1 hj_adj
        · have hbip := S.P.bipartite_edge j b a hj_adj.symm (by rw [hW'_assign τ hτ b hb.1]; exact hτ2)
          rw [hW'_assign τ hτ b hb.1, hW'_assign σ hσ a ha, h2] at hbip
          rcases hbip with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)
      have hbip := S.P.bipartite_edge j a b hj_adj (by rw [hW'_assign σ hσ a ha]; exact hσj_ne2)
      rw [hW'_assign σ hσ a ha, hW'_assign τ hτ b hb.1] at hbip
      have hτj_ne2 : τ j ≠ 2 := by
        rcases hbip with ⟨_, h1⟩ | ⟨_, h0⟩
        · rw [h1]; decide
        · rw [h0]; decide
      have hsame_comp : (S.R_col j).connectedComponentMk (hW'_ne σ hσ).choose =
          (S.R_col j).connectedComponentMk (hW'_ne τ hτ).choose := by
        have h1 : (S.R_col j).Reachable a b := Adj.reachable hj_adj
        have h2 : (S.R_col j).Reachable b (hW'_ne τ hτ).choose :=
          hW'_conn j τ hτ hτj_ne2 b hb.1 _ (hW'_ne τ hτ).choose_spec
        exact ConnectedComponent.eq.mpr (h1.trans h2)
      refine ⟨j, ?_⟩
      dsimp only [φ]
      rw [dif_pos hσ, dif_pos hτ, if_neg hσj_ne2, if_neg hτj_ne2, hsame_comp]
      cases flipComp j ((S.R_col j).connectedComponentMk (hW'_ne τ hτ).choose) <;>
        rcases hbip with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> simp [h0, h1]
    have hφ_inj : Set.InjOn φ S.D := fun σ hσ τ hτ heq => by
      by_contra hne
      exact not_distinguishable_self (φ σ) (heq ▸ hφ_dist σ hσ τ hτ hne)
    let D' : Finset (Subcube k) := S.D.image φ
    have hD'_dist : IsDistinguishableSet D' := by
      refine ⟨fun ρ hρ => by rcases mem_image.mp hρ with ⟨σ, hσ, rfl⟩; rw [hφ_w1 σ hσ],
        fun ρ1 hρ1 ρ2 hρ2 hne => by
        rcases mem_image.mp hρ1 with ⟨σ1, hσ1, rfl⟩
        rcases mem_image.mp hρ2 with ⟨σ2, hσ2, rfl⟩
        exact hφ_dist σ1 hσ1 σ2 hσ2 (fun h => hne (by rw [h]))⟩
    have hD'_dec : IsDecomposition D' := by
      apply (sum_two_pow_weight_le hD'_dist).2.mp
      have hsum : ∑ ρ ∈ D', 2 ^ weight ρ = ∑ _ρ ∈ D', 2 := Finset.sum_congr rfl fun ρ hρ => by
        rcases mem_image.mp hρ with ⟨σ, hσ, rfl⟩; rw [hφ_w1 σ hσ]; norm_num
      rw [hsum, sum_const, smul_eq_mul, card_image_of_injOn hφ_inj, hD_card]
      omega
    have hallT : (fun _ : Fin k => true) ∈ D'.biUnion subcubeSet := by rw [hD'_dec.2]; exact mem_univ _
    rcases mem_biUnion.mp hallT with ⟨ρ, hρD', hTρ⟩
    rcases mem_image.mp hρD' with ⟨σ, hσ, rfl⟩
    refine ⟨σ, hσ, fun j hj_ne i hi => ?_⟩
    by_contra hge; push Not at hge
    have hheavy : IsHeavy v j σ := ⟨i, hi, hge⟩
    have hσj_ne2 : σ j ≠ 2 := fun h2 => hj_ne (hcolOf_uniq σ hσ j h2)
    have hφ_ne0 : φ σ j ≠ 0 := fun h0 => Bool.false_ne_true (((mem_filter.mp hTρ).2 j).1 h0).symm
    dsimp only [φ] at hφ_ne0
    rw [dif_pos hσ, if_neg hσj_ne2] at hφ_ne0
    rcases fin3_cases (σ j) with hj | hj | hj
    · have hfl : flipComp j ((S.R_col j).connectedComponentMk (hW'_ne σ hσ).choose) = true := by
        cases hfc : flipComp j ((S.R_col j).connectedComponentMk (hW'_ne σ hσ).choose)
        · rw [hfc, hj] at hφ_ne0; simp at hφ_ne0
        · rfl
      rw [decide_eq_true_eq] at hfl
      obtain ⟨τ, hτ, hτ1, hsame, hτheavy⟩ := hfl
      exact hno_both_heavy v j σ τ hσ hτ hj hτ1 hsame.symm hheavy hτheavy
    · have hfl : flipComp j ((S.R_col j).connectedComponentMk (hW'_ne σ hσ).choose) = true :=
        decide_eq_true ⟨σ, hσ, hj, rfl, hheavy⟩
      rw [hfl, hj] at hφ_ne0; simp at hφ_ne0
    · exact hσj_ne2 hj
  exact ⟨colOf, W', Wtilde, hW'_card, hWtilde_disj, hWtilde_sub_V, hWtilde_card, hcomp, hex_good_part⟩
set_option maxHeartbeats 800000 in
lemma jenssen_skokan_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ C : TopEdgeLabeling (Fin (n * 2 ^ k + 1)) (Fin k),
        ∃ c : Fin k, (cycleGraph (2 * n + 1)).IsContained (C.labelGraph c) := by
  classical
  let K : ℕ := 2 ^ (k - 1)
  have hK_pos : 0 < K := Nat.pow_pos (by omega)
  have h2K : 2 * K = 2 ^ k := by
    dsimp only [K]; conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega), pow_succ']
  have hKr_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have hkr_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  filter_upwards [build_reduced_setup k hk] with n hsetup C
  by_contra hno
  obtain ⟨S⟩ := hsetup C hno
  obtain ⟨colOf, W', Wtilde, hW'_card, hWtilde_disj, hWtilde_sub_V, hWtilde_card, hcomp, hex_good_part⟩ :=
    build_cores_and_good_part hk C hno S
  let N : ℕ := n * 2 ^ k + 1
  have hN_eq : N = 2 * K * n + 1 := by dsimp only [N]; rw [← h2K]; ring
  let n' : ℝ := (S.t : ℝ) / (K : ℝ)
  have htr_pos : (0 : ℝ) < (S.t : ℝ) := by exact_mod_cast S.ht_pos
  have hn'_pos : 0 < n' := div_pos htr_pos hKr_pos
  let s0 : ℕ := Nat.floor ((1 - 2 * S.ε_stab) * n')
  have hmr_pos : (0 : ℝ) < (S.m : ℝ) := by exact_mod_cast S.hm_pos
  have hε_stab_pos : 0 < S.ε_stab := by rw [S.hε_stab_eq]; positivity
  have hε_stab_lt : S.ε_stab < 1 / 10 := by
    have hK2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 2 ≤ K from Nat.le_self_pow (by omega) 2)
    rw [S.hε_stab_eq, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hs0_ge : (1 - 2 * S.ε_stab) * n' - 1 ≤ (s0 : ℝ) := by
    dsimp only [s0]; linarith [Nat.sub_one_lt_floor ((1 - 2 * S.ε_stab) * n')]
  have hs0_le : (s0 : ℝ) ≤ (1 - 2 * S.ε_stab) * n' :=
    Nat.floor_le (by nlinarith [hε_stab_lt, hn'_pos])
  have hD_card : S.D.card = K := by
    have hsum := (sum_two_pow_weight_le S.hdec.1).2.mpr S.hdec
    have h2D : ∑ τ ∈ S.D, 2 ^ weight τ = 2 * S.D.card := by
      rw [Finset.sum_congr rfl (fun τ hτ => by rw [S.hD_w1 τ hτ])]; simp [mul_comm]
    rw [h2D] at hsum; omega
  have hKs0 : (1 - 3 * S.ε_stab) * (S.t : ℝ) ≤ (K : ℝ) * (s0 : ℝ) := by
    have h2δ : 2 / S.δ_red ≤ n' := (le_max_right _ _).trans S.hn'_ge
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hδ_le : S.δ_red ≤ S.ε_stab := by
      rw [S.hε_stab_eq]
      have : 1000 * (K : ℝ) ≤ 1000 * (k : ℝ) * (K : ℝ) := by nlinarith
      exact S.hδ_red_small.trans (one_div_le_one_div_of_le (by positivity) this)
    have h2 : 2 ≤ n' * S.δ_red := (div_le_iff₀ S.hδ_red_pos).mp h2δ
    have h1' : 1 ≤ S.ε_stab * n' := by nlinarith [hn'_pos]
    have hs0' : (1 - 3 * S.ε_stab) * n' ≤ (s0 : ℝ) := by linarith
    have hK_n' : (K : ℝ) * n' = (S.t : ℝ) := by dsimp only [n']; field_simp
    have hmul := mul_le_mul_of_nonneg_left hs0' hKr_pos.le
    nlinarith
  have hke_le : (k : ℝ) * S.ε_reg ≤ S.ε_stab := by
    have h1 := mul_le_mul_of_nonneg_left S.hε_reg_tiny hkr_pos.le
    have h2 : (k : ℝ) * (1 / ((2000 : ℝ) ^ 2 * (k : ℝ) * (K : ℝ) ^ 4)) = 1 / ((2000 : ℝ) ^ 2 * (K : ℝ) ^ 4) := by
      field_simp
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
    have hKp : (K : ℝ) ≤ (K : ℝ) ^ 4 := by
      have : (K : ℝ) ^ 1 ≤ (K : ℝ) ^ 4 := pow_le_pow_right₀ hK1 (by omega)
      simpa using this
    have h3 : 1 / ((2000 : ℝ) ^ 2 * (K : ℝ) ^ 4) ≤ 1 / (1000 * (K : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    rw [S.hε_stab_eq]; linarith
  have hε_le_es : S.ε_reg ≤ S.ε_stab := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith [S.hε_reg_pos]
  have htm_ge : (1 - S.ε_stab) * (N : ℝ) ≤ (S.t : ℝ) * (S.m : ℝ) := by nlinarith [S.hcover_m]
  have hprod_core : (1 - 1 / (50 * (K : ℝ))) * (N : ℝ) ≤
      (K : ℝ) * ((s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ)) := by
    have hprod1 : (1 - 3 * S.ε_stab) * (1 - S.ε_stab) * ((S.t : ℝ) * (S.m : ℝ)) ≤
        (K : ℝ) * ((s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ)) := by
      have hm_le : (1 - S.ε_stab) * (S.m : ℝ) ≤ (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hmr_pos.le
      have h1 := mul_le_mul hKs0 hm_le (by nlinarith) (by positivity)
      linarith
    have h50 : 1 - 1 / (50 * (K : ℝ)) ≤ (1 - 3 * S.ε_stab) * (1 - S.ε_stab) * (1 - S.ε_stab) := by
      have h1 : 1 / (50 * (K : ℝ)) = 20 * S.ε_stab := by rw [S.hε_stab_eq]; field_simp; ring
      nlinarith [sq_nonneg S.ε_stab, hε_stab_lt, hε_stab_pos]
    have ha : (1 - 3 * S.ε_stab) * (1 - S.ε_stab) * ((1 - S.ε_stab) * (N : ℝ)) ≤
        (1 - 3 * S.ε_stab) * (1 - S.ε_stab) * ((S.t : ℝ) * (S.m : ℝ)) :=
      mul_le_mul_of_nonneg_left htm_ge (by nlinarith)
    have hb : (1 - 1 / (50 * (K : ℝ))) * (N : ℝ) ≤
        (1 - 3 * S.ε_stab) * (1 - S.ε_stab) * (1 - S.ε_stab) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right h50 (Nat.cast_nonneg _)
    linarith
  let assignV : Fin N → Subcube k := fun v =>
    if h : ∃ σ ∈ S.D, v ∈ Wtilde σ then h.choose else (hex_good_part v).choose
  have hassign_mem : ∀ v : Fin N, assignV v ∈ S.D := fun v => by
    dsimp only [assignV]; split_ifs with h
    · exact h.choose_spec.1
    · exact (hex_good_part v).choose_spec.1
  have hWtilde_sub_U : ∀ σ ∈ S.D, Wtilde σ ⊆ Finset.univ.filter (fun v => assignV v = σ) := by
    intro σ hσ v hv
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hex : ∃ ρ ∈ S.D, v ∈ Wtilde ρ := ⟨σ, hσ, hv⟩
    dsimp only [assignV]; rw [dif_pos hex]
    by_contra hne
    exact Finset.disjoint_left.mp (hWtilde_disj _ hex.choose_spec.1 σ hσ hne) hex.choose_spec.2 hv
  let Core : Finset (Fin N) := S.D.biUnion Wtilde
  have hCore_card : (1 - 1 / (50 * (K : ℝ))) * (N : ℝ) ≤ (Core.card : ℝ) := by
    have hdisj_D : (S.D : Set (Subcube k)).PairwiseDisjoint Wtilde :=
      fun σ1 hσ1 σ2 hσ2 hne => hWtilde_disj σ1 hσ1 σ2 hσ2 hne
    rw [show (Core.card : ℝ) = ∑ σ ∈ S.D, ((Wtilde σ).card : ℝ) by
      dsimp only [Core]; rw [card_biUnion hdisj_D, Nat.cast_sum]]
    calc (1 - 1 / (50 * (K : ℝ))) * (N : ℝ)
        ≤ (K : ℝ) * ((s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ)) := hprod_core
      _ = ∑ _σ ∈ S.D, (s0 : ℝ) * (1 - (k : ℝ) * S.ε_reg) * (S.m : ℝ) := by
            rw [sum_const, hD_card, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ S.D, ((Wtilde σ).card : ℝ) := sum_le_sum fun σ hσ => hWtilde_card σ hσ
  have hex_big_U : ∃ σ0 ∈ S.D, 2 * n + 1 ≤ (Finset.univ.filter (fun v : Fin N => assignV v = σ0)).card := by
    by_contra hno_big; push Not at hno_big
    have hsum_U : ∑ σ ∈ S.D, (Finset.univ.filter (fun v : Fin N => assignV v = σ)).card = N := by
      rw [← card_biUnion]
      · have heq : S.D.biUnion (fun σ => Finset.univ.filter (fun v : Fin N => assignV v = σ)) = Finset.univ := by
          ext v; simp only [mem_biUnion, mem_filter, mem_univ, true_and, iff_true]
          exact ⟨assignV v, hassign_mem v, rfl⟩
        rw [heq, card_univ, Fintype.card_fin]
      · intro σ1 _ σ2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
        intro v h1 h2; exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    have hle : ∑ σ ∈ S.D, (Finset.univ.filter (fun v : Fin N => assignV v = σ)).card ≤ K * (2 * n) := by
      calc ∑ σ ∈ S.D, (Finset.univ.filter (fun v : Fin N => assignV v = σ)).card
          ≤ ∑ _σ ∈ S.D, (2 * n) := sum_le_sum fun σ hσ => Nat.lt_succ_iff.mp (hno_big σ hσ)
        _ = K * (2 * n) := by rw [sum_const, hD_card, smul_eq_mul]
    have hK2n : K * (2 * n) = 2 * K * n := by ring
    rw [hsum_U, hN_eq, hK2n] at hle; omega
  obtain ⟨σ0, hσ0, hU0_big⟩ := hex_big_U
  let U0 : Finset (Fin N) := Finset.univ.filter (fun v : Fin N => assignV v = σ0)
  let c0 : Fin k := colOf σ0
  let G0 := (C.labelGraph c0).induce (U0 : Set (Fin N))
  have hU0_sdiff_le : ((U0 \ Wtilde σ0).card : ℝ) ≤ (1 / (50 * (K : ℝ))) * (N : ℝ) := by
    have hsub : U0 \ Wtilde σ0 ⊆ Finset.univ \ Core := by
      intro v hv
      rw [Finset.mem_sdiff] at hv ⊢
      refine ⟨mem_univ _, fun hC => ?_⟩
      rcases mem_biUnion.mp hC with ⟨ρ, hρ, hvρ⟩
      have hassign_eq : assignV v = ρ := (mem_filter.mp (hWtilde_sub_U ρ hρ hvρ)).2
      have hv_eq : assignV v = σ0 := (mem_filter.mp hv.1).2
      have hρσ : ρ = σ0 := hassign_eq.symm.trans hv_eq
      subst hρσ; exact hv.2 hvρ
    have h1 := card_sdiff_add_card_eq_card (subset_univ Core)
    have h1r : ((Finset.univ \ Core).card : ℝ) + (Core.card : ℝ) = (N : ℝ) := by
      rw [card_univ, Fintype.card_fin] at h1; exact_mod_cast h1
    have hle : ((U0 \ Wtilde σ0).card : ℝ) ≤ ((Finset.univ \ Core).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    linarith
  have hWtilde0_ge : (19 / 20 : ℝ) * ((N : ℝ) / (K : ℝ)) ≤ ((Wtilde σ0).card : ℝ) := by
    have h1 := hWtilde_card σ0 hσ0
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
    have h95 : (19 / 20 : ℝ) ≤ 1 - 1 / (50 * (K : ℝ)) := by
      have : 1 / (50 * (K : ℝ)) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have h1K := mul_le_mul_of_nonneg_left h1 hKr_pos.le
    have h95N : (19 / 20 : ℝ) * (N : ℝ) ≤ (1 - 1 / (50 * (K : ℝ))) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right h95 (Nat.cast_nonneg _)
    rw [← mul_div_assoc, div_le_iff₀ hKr_pos]
    linarith [hprod_core, h1K, h95N]
  have hU0_le : (U0.card : ℝ) ≤ ((Wtilde σ0).card : ℝ) + (1 / 50 : ℝ) * ((N : ℝ) / (K : ℝ)) := by
    have h1 := card_sdiff_add_card_eq_card (hWtilde_sub_U σ0 hσ0)
    have h1r : ((U0 \ Wtilde σ0).card : ℝ) + ((Wtilde σ0).card : ℝ) = (U0.card : ℝ) := by exact_mod_cast h1
    have hre : (1 / (50 * (K : ℝ))) * (N : ℝ) = (1 / 50 : ℝ) * ((N : ℝ) / (K : ℝ)) := by ring
    linarith
  have hcard_U0_eq : Fintype.card (U0 : Set (Fin N)) = U0.card := by
    convert Fintype.card_coe U0; exact mem_coe
  have hdeg_G0 : ∀ v : (U0 : Set (Fin N)), 3 * Fintype.card (U0 : Set (Fin N)) < 4 * (G0.neighborFinset v).card := by
    intro v
    rw [hcard_U0_eq]
    have hdeg_ge_W : ((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card ≤ (G0.neighborFinset v).card := by
      have hmaps : Set.MapsTo (fun (w : Fin N) => if hw : w ∈ U0 then (⟨w, hw⟩ : (U0 : Set (Fin N))) else v)
          ((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val) : Set (Fin N))
          (G0.neighborFinset v : Set (U0 : Set (Fin N))) := by
        intro w hw
        rw [mem_coe, mem_filter] at hw
        have hwU : w ∈ U0 := hWtilde_sub_U σ0 hσ0 hw.1
        rw [mem_coe, mem_neighborFinset]
        dsimp only; rw [dif_pos hwU]
        exact hw.2
      exact card_le_card_of_injOn (fun w => if hw : w ∈ U0 then (⟨w, hw⟩ : (U0 : Set (Fin N))) else v) hmaps
        (fun a ha b hb heq => by
          rw [mem_coe, mem_filter] at ha hb
          dsimp only at heq
          rw [dif_pos (hWtilde_sub_U σ0 hσ0 ha.1), dif_pos (hWtilde_sub_U σ0 hσ0 hb.1)] at heq
          exact congrArg Subtype.val heq)
    have hgoal_r : (3 * (U0.card : ℝ)) < 4 * (((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card : ℝ) := by
      by_cases hvW : v.val ∈ Wtilde σ0
      · have hsub : (Wtilde σ0).erase v.val ⊆ (Wtilde σ0).filter ((C.labelGraph c0).Adj v.val) := by
          intro w hw
          rw [mem_erase] at hw
          exact mem_filter.mpr ⟨hw.2, hcomp σ0 hσ0 v.val hvW w hw.2 hw.1.symm⟩
        have hcard_ge : ((Wtilde σ0).card : ℝ) - 1 ≤ (((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card : ℝ) := by
          have h1 : (Wtilde σ0).card - 1 ≤ ((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card := by
            rw [← card_erase_of_mem hvW]; exact card_le_card hsub
          have hpos : 1 ≤ (Wtilde σ0).card := card_pos.mpr ⟨v.val, hvW⟩
          have h1r : (((Wtilde σ0).card - 1 : ℕ) : ℝ) ≤ (((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card : ℝ) := by
            exact_mod_cast h1
          rw [Nat.cast_sub hpos, Nat.cast_one] at h1r; exact h1r
        have hNK_ge : (200 : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
          rw [le_div_iff₀ hKr_pos]
          have hNr : (N : ℝ) = 2 * (K : ℝ) * (n : ℝ) + 1 := by exact_mod_cast hN_eq
          have hn100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast S.hn_ge100
          nlinarith
        linarith
      · have hnot_ex : ¬ ∃ ρ ∈ S.D, v.val ∈ Wtilde ρ := by
          intro hex
          have hvU := (mem_filter.mp v.property).2
          dsimp only [assignV] at hvU; rw [dif_pos hex] at hvU
          exact hvW (hvU ▸ hex.choose_spec.2)
        have hnot_heavy : ∀ j : Fin k, j ≠ c0 →
            ∀ i ∈ W' σ0, (((C.labelGraph j).neighborFinset v.val ∩ S.V i).card : ℝ) < (S.d / 4) * (S.m : ℝ) := by
          have hvU := (mem_filter.mp v.property).2
          dsimp only [assignV] at hvU; rw [dif_neg hnot_ex] at hvU
          have hspec := (hex_good_part v.val).choose_spec.2
          rw [hvU] at hspec; exact hspec
        let BadN : Finset (Fin N) := (Wtilde σ0) \ (Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)
        have hBadN_sub : BadN ⊆ (Finset.univ.filter (fun j : Fin k => j ≠ c0)).biUnion (fun j =>
            (W' σ0).biUnion (fun i => (C.labelGraph j).neighborFinset v.val ∩ S.V i)) := by
          intro w hw
          rw [Finset.mem_sdiff, mem_filter] at hw
          have hvw : v.val ≠ w := fun h => hvW (h ▸ hw.1)
          let j := C.get v.val w hvw
          have hj_ne : j ≠ c0 := fun h => hw.2 ⟨hw.1, by rw [TopEdgeLabeling.labelGraph_adj]; exact ⟨hvw, h⟩⟩
          rcases mem_biUnion.mp (hWtilde_sub_V σ0 hσ0 hw.1) with ⟨i, hi, hwi⟩
          exact mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj_ne⟩,
            mem_biUnion.mpr ⟨i, hi, mem_inter.mpr
              ⟨(mem_neighborFinset _ _ _).mpr (by rw [TopEdgeLabeling.labelGraph_adj]; exact ⟨hvw, rfl⟩), hwi⟩⟩⟩
        have hBadN_le : (BadN.card : ℝ) ≤ (1 / 16 : ℝ) * ((s0 : ℝ) * (S.m : ℝ)) := by
          have hd0 : 0 < S.d := by rw [S.hd_eq]; positivity
          have hW'c : (W' σ0).card = s0 := hW'_card σ0 hσ0
          calc (BadN.card : ℝ)
              ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ c0),
                  ∑ i ∈ W' σ0, (((C.labelGraph j).neighborFinset v.val ∩ S.V i).card : ℝ) := by
                have h1 : BadN.card ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ c0),
                    ((W' σ0).biUnion (fun i => (C.labelGraph j).neighborFinset v.val ∩ S.V i)).card :=
                  (card_le_card hBadN_sub).trans card_biUnion_le
                have h2 : ∀ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ c0),
                    ((W' σ0).biUnion (fun i => (C.labelGraph j).neighborFinset v.val ∩ S.V i)).card ≤
                    ∑ i ∈ W' σ0, ((C.labelGraph j).neighborFinset v.val ∩ S.V i).card :=
                  fun _ _ => card_biUnion_le
                exact_mod_cast h1.trans (sum_le_sum h2)
            _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ c0), ∑ _i ∈ W' σ0, (S.d / 4) * (S.m : ℝ) :=
                sum_le_sum fun j hj => sum_le_sum fun i hi =>
                  (hnot_heavy j (mem_filter.mp hj).2 i hi).le
            _ = (((Finset.univ.filter (fun j : Fin k => j ≠ c0)).card : ℝ) * (S.d / 4)) * ((s0 : ℝ) * (S.m : ℝ)) := by
                rw [sum_const, sum_const, hW'c, nsmul_eq_mul, nsmul_eq_mul]; ring
            _ ≤ ((k : ℝ) * (S.d / 4)) * ((s0 : ℝ) * (S.m : ℝ)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact_mod_cast (card_filter_le Finset.univ _).trans (by simp)
            _ = (1 / 16 : ℝ) * ((s0 : ℝ) * (S.m : ℝ)) := by rw [S.hd_eq]; field_simp; ring
        have hsplit := card_sdiff_add_card_eq_card (filter_subset ((C.labelGraph c0).Adj v.val) (Wtilde σ0))
        have hsplit_r : (BadN.card : ℝ) + (((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card : ℝ) =
            ((Wtilde σ0).card : ℝ) := by exact_mod_cast hsplit
        have hs0m_le : (s0 : ℝ) * (S.m : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
          rw [le_div_iff₀ hKr_pos]
          have hK_n' : (K : ℝ) * n' = (S.t : ℝ) := by dsimp only [n']; field_simp
          have h1 : (K : ℝ) * (s0 : ℝ) ≤ (S.t : ℝ) := by nlinarith [hs0_le, hε_stab_pos, hn'_pos]
          have h2 : (S.t : ℝ) * (S.m : ℝ) ≤ (N : ℝ) := by exact_mod_cast S.htm_le
          nlinarith
        have hNK_pos : (0 : ℝ) < (N : ℝ) / (K : ℝ) := div_pos (by exact_mod_cast (show 0 < N by omega)) hKr_pos
        linarith
    have hfinal_r : 3 * (U0.card : ℝ) < 4 * ((G0.neighborFinset v).card : ℝ) := by
      have : (((Wtilde σ0).filter ((C.labelGraph c0).Adj v.val)).card : ℝ) ≤ ((G0.neighborFinset v).card : ℝ) := by
        exact_mod_cast hdeg_ge_W
      linarith
    exact_mod_cast hfinal_r
  have hcard_U0 : 2 * n + 1 ≤ Fintype.card (U0 : Set (Fin N)) := by
    rw [hcard_U0_eq]; exact hU0_big
  have hn_ge2 : 2 ≤ n := by have := S.hn_ge100; omega
  have hcyc_G0 : (cycleGraph (2 * n + 1)).IsContained G0 :=
    exists_cycle_of_high_min_degree G0 (by omega) hdeg_G0 (2 * n + 1) (by omega) hcard_U0
  obtain ⟨f, hf_inj, hf_adj⟩ := exists_cycle_fun_of_isContained (by omega) hcyc_G0
  exact hno ⟨c0, cycleGraph_isContained_of_fun (by omega) (fun i => (f i).val)
    (Subtype.val_injective.comp hf_inj) (fun i => hf_adj i)⟩
end JenssenSkokan
theorem OMA.solution : type_of% @Erdos554.erdos_554.variants.jenssen_skokan := by
  intro k hk
  filter_upwards [JenssenSkokan.jenssen_skokan_upper_bound k hk, Filter.eventually_ge_atTop 1] with n hup hn1
  have hne : {m : ℕ | ∀ C : SimpleGraph.TopEdgeLabeling (Fin m) (Fin k),
      ∃ c, (SimpleGraph.cycleGraph (2 * n + 1)).IsContained (C.labelGraph c)}.Nonempty :=
    ⟨n * 2 ^ k + 1, hup⟩
  apply le_antisymm
  · exact Nat.sInf_le hup
  · refine le_csInf hne fun m hm => ?_
    by_contra hlt
    exact JenssenSkokan.not_forces_odd_cycle_of_le k n m (by omega) hn1 (by omega) hm
