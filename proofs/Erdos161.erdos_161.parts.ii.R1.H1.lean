import OMAReductions.R_Erdos161_erdos_161_parts_ii_R1
import Mathlib

/-!
# Proof of Step H1: Conlon--Fox--Sudakov (2011), Theorem 1 (2-color case)

We prove `OMA.R_Erdos161_erdos_161_parts_ii_R1.H1`: for every `α ∈ (0, 1/2)`, there exists
`c > 0` such that for all sufficiently large `n`, every 2-coloring of the 3-subsets of `Fin n`
contains a subset `X` of size at least `c * √(log n)` in which some color has fewer than
`α * (|X|.choose 3)` triples.

Following Conlon, Fox, and Sudakov (*Israel J. Math.* 181 (2011), 423--432), we prove that
every 2-coloring of the 3-subsets of `Fin n` with `n ≥ 2^(C_r * m^2)` contains a monochromatic
complete `d`-partite 3-uniform hypergraph `K_d^(3)(m)`, via:
1. The 2-color graph Ramsey theorem (`ramsey2_finset`).
2. Two Kővári--Sós--Turán style density lemmas proved directly by Markov and pigeonhole
   (`kst_bipartite_half` and `kst_graph_complete_bipartite`).
3. An `r`-round iterative subset-extraction induction (`cfs_rounds`).
4. Crossing-triple counting on `d` disjoint parts of size `m` (`crossing_triples_card`).
-/

-- Credit: @preternatural-tocsin

namespace CFS11

open Filter Finset

/- ### Part 1: 2-color Graph Ramsey Theorem -/

lemma ramsey2_finset {α : Type*} [LinearOrder α] :
    ∀ k : ℕ, ∀ a b : ℕ, a + b = k →
      ∀ (S : Finset α) (f : α → α → Bool),
        (a + b).choose a ≤ S.card →
        (∃ A ⊆ S, A.card = a ∧ ∀ x ∈ A, ∀ y ∈ A, x < y → f x y = true) ∨
        (∃ B ⊆ S, B.card = b ∧ ∀ x ∈ B, ∀ y ∈ B, x < y → f x y = false) := by
  intro k
  induction k with
  | zero =>
    intro a b hab S _ _
    have ha : a = 0 := by omega
    subst ha
    left
    exact ⟨∅, empty_subset S, rfl, by simp⟩
  | succ k ih =>
    intro a b hab S f hS
    cases a with
    | zero =>
      left
      exact ⟨∅, empty_subset S, rfl, by simp⟩
    | succ a =>
      cases b with
      | zero =>
        right
        exact ⟨∅, empty_subset S, rfl, by simp⟩
      | succ b =>
        have hpos : 0 < S.card := by
          have hc : 0 < (a + 1 + (b + 1)).choose (a + 1) := Nat.choose_pos (by omega)
          omega
        have hne : S.Nonempty := card_pos.mp hpos
        let v := S.min' hne
        have hvS : v ∈ S := min'_mem S hne
        let S' := S.erase v
        let S1 := S'.filter (fun w ↦ f v w = true)
        let S0 := S'.filter (fun w ↦ f v w = false)
        have hS'card : S'.card = S.card - 1 := card_erase_of_mem hvS
        have hpart : S1.card + S0.card = S'.card := by
          have h0 : S0 = S'.filter (fun w ↦ ¬ (f v w = true)) := by
            ext w
            simp [S0]
          rw [h0]
          simpa using Finset.sum_filter_add_sum_filter_not S' (fun w ↦ f v w = true) (fun _ ↦ (1 : ℕ))
        have hpascal : (a + 1 + (b + 1)).choose (a + 1) =
            (a + (b + 1)).choose a + (a + 1 + b).choose (a + 1) := by
          have h1 : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
          have h2 : a + (b + 1) = a + b + 1 := by omega
          have h3 : a + 1 + b = a + b + 1 := by omega
          rw [h1, h2, h3, Nat.choose_succ_succ]
        have hbranch : (a + (b + 1)).choose a ≤ S1.card ∨ (a + 1 + b).choose (a + 1) ≤ S0.card := by
          omega
        rcases hbranch with h1 | h0
        · rcases ih a (b + 1) (by omega) S1 f h1 with ⟨A, hAS1, hAcard, hAcol⟩ | ⟨B, hBS1, hBcard, hBcol⟩
          · left
            have hvA : v ∉ A := fun hv ↦ (mem_erase.mp (mem_filter.mp (hAS1 hv)).1).1 rfl
            refine ⟨insert v A, insert_subset hvS (hAS1.trans ((filter_subset _ _).trans (erase_subset _ _))),
              by rw [card_insert_of_notMem hvA, hAcard], ?_⟩
            intro x hx y hy hxy
            rcases mem_insert.mp hx with rfl | hxA
            · rcases mem_insert.mp hy with rfl | hyA
              · exact absurd hxy (lt_irrefl _)
              · exact (mem_filter.mp (hAS1 hyA)).2
            · rcases mem_insert.mp hy with rfl | hyA
              · have hle : v ≤ x := min'_le S x ((erase_subset _ _) (filter_subset _ _ (hAS1 hxA)))
                exact absurd (lt_of_le_of_lt hle hxy) (lt_irrefl _)
              · exact hAcol x hxA y hyA hxy
          · right
            exact ⟨B, hBS1.trans ((filter_subset _ _).trans (erase_subset _ _)), hBcard, hBcol⟩
        · rcases ih (a + 1) b (by omega) S0 f h0 with ⟨A, hAS0, hAcard, hAcol⟩ | ⟨B, hBS0, hBcard, hBcol⟩
          · left
            exact ⟨A, hAS0.trans ((filter_subset _ _).trans (erase_subset _ _)), hAcard, hAcol⟩
          · right
            have hvB : v ∉ B := fun hv ↦ (mem_erase.mp (mem_filter.mp (hBS0 hv)).1).1 rfl
            refine ⟨insert v B, insert_subset hvS (hBS0.trans ((filter_subset _ _).trans (erase_subset _ _))),
              by rw [card_insert_of_notMem hvB, hBcard], ?_⟩
            intro x hx y hy hxy
            rcases mem_insert.mp hx with rfl | hxB
            · rcases mem_insert.mp hy with rfl | hyB
              · exact absurd hxy (lt_irrefl _)
              · exact (mem_filter.mp (hBS0 hyB)).2
            · rcases mem_insert.mp hy with rfl | hyB
              · have hle : v ≤ x := min'_le S x ((erase_subset _ _) (filter_subset _ _ (hBS0 hxB)))
                exact absurd (lt_of_le_of_lt hle hxy) (lt_irrefl _)
              · exact hBcol x hxB y hyB hxy

lemma ramsey2_fin (k : ℕ) (f : ℕ → ℕ → Bool) :
    ∃ b : Bool, ∃ I ⊆ Finset.range ((2 * k).choose k),
      I.card = k ∧ ∀ i ∈ I, ∀ j ∈ I, i < j → f i j = b := by
  have hcard : (k + k).choose k ≤ (Finset.range ((2 * k).choose k)).card := by
    rw [card_range, two_mul]
  rcases ramsey2_finset (k + k) k k rfl (Finset.range ((2 * k).choose k)) f hcard with
    ⟨A, hA, hc, hcol⟩ | ⟨B, hB, hc, hcol⟩
  · exact ⟨true, A, hA, hc, hcol⟩
  · exact ⟨false, B, hB, hc, hcol⟩

/- ### Part 2: Elementary KST Lemmas (Markov + Pigeonhole) -/

lemma kst_bipartite_quarter {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop) [∀ u w, Decidable (R u w)]
    (a : ℕ) (ha : A.card = 4 * a) (ha_pos : 0 < a)
    (hdense : A.card * B.card ≤ 2 * ∑ w ∈ B, (A.filter (fun u ↦ R u w)).card) :
    ∃ A' ⊆ A, A'.card = a ∧
      ∃ B' ⊆ B, B.card ≤ 4 * 2 ^ A.card * B'.card ∧
        ∀ u ∈ A', ∀ w ∈ B', R u w := by
  let Bhi := B.filter (fun w ↦ a ≤ (A.filter (fun u ↦ R u w)).card)
  have hBhi_card : B.card ≤ 4 * Bhi.card := by
    have hsplit :
        ∑ w ∈ B, (A.filter (fun u ↦ R u w)).card =
          ∑ w ∈ Bhi, (A.filter (fun u ↦ R u w)).card +
          ∑ w ∈ B.filter (fun w ↦ ¬ (a ≤ (A.filter (fun u ↦ R u w)).card)),
            (A.filter (fun u ↦ R u w)).card :=
      (sum_filter_add_sum_filter_not B (fun w ↦ a ≤ (A.filter (fun u ↦ R u w)).card) _).symm
    have h1 : ∑ w ∈ Bhi, (A.filter (fun u ↦ R u w)).card ≤ Bhi.card * A.card := by
      calc
        ∑ w ∈ Bhi, (A.filter (fun u ↦ R u w)).card ≤ ∑ _w ∈ Bhi, A.card :=
          sum_le_sum (fun w _ ↦ card_filter_le A _)
        _ = Bhi.card * A.card := by simp
    have h2 : ∑ w ∈ B.filter (fun w ↦ ¬ (a ≤ (A.filter (fun u ↦ R u w)).card)),
        (A.filter (fun u ↦ R u w)).card ≤ B.card * a := by
      calc
        ∑ w ∈ B.filter (fun w ↦ ¬ (a ≤ (A.filter (fun u ↦ R u w)).card)),
            (A.filter (fun u ↦ R u w)).card
            ≤ ∑ _w ∈ B.filter (fun w ↦ ¬ (a ≤ (A.filter (fun u ↦ R u w)).card)), a := by
              refine sum_le_sum ?_
              intro w hw
              rw [mem_filter] at hw
              omega
        _ = (B.filter (fun w ↦ ¬ (a ≤ (A.filter (fun u ↦ R u w)).card))).card * a := by simp
        _ ≤ B.card * a := Nat.mul_le_mul_right a (card_filter_le B _)
    have hcomb : 4 * a * B.card ≤ 2 * (Bhi.card * (4 * a) + B.card * a) := by
      rw [ha] at hdense h1
      omega
    have hcomb2 : 2 * a * B.card ≤ 8 * a * Bhi.card := by linarith
    have hdiv : 2 * B.card ≤ 8 * Bhi.card :=
      Nat.le_of_mul_le_mul_left (by linarith : a * (2 * B.card) ≤ a * (8 * Bhi.card)) ha_pos
    omega
  have hpick : ∀ w ∈ Bhi, ∃ A' ∈ A.powersetCard a, ∀ u ∈ A', R u w := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨A', hA'sub, hA'card⟩ := exists_subset_card_eq hw.2
    refine ⟨A', mem_powersetCard.mpr ⟨hA'sub.trans (filter_subset _ _), hA'card⟩, ?_⟩
    intro u hu
    exact (mem_filter.mp (hA'sub hu)).2
  classical
  let f : β → Finset α := fun w ↦ if hw : w ∈ Bhi then Classical.choose (hpick w hw) else ∅
  have hf_mem : ∀ w ∈ Bhi, f w ∈ A.powersetCard a := by
    intro w hw
    dsimp [f]
    rw [dif_pos hw]
    exact (Classical.choose_spec (hpick w hw)).1
  have hf_R : ∀ w ∈ Bhi, ∀ u ∈ f w, R u w := by
    intro w hw u hu
    dsimp [f] at hu
    rw [dif_pos hw] at hu
    exact (Classical.choose_spec (hpick w hw)).2 u hu
  have hpow_le : (A.powersetCard a).card ≤ 2 ^ A.card := by
    have hsub : A.powersetCard a ⊆ A.powerset := fun s hs ↦ mem_powerset.mpr (mem_powersetCard.mp hs).1
    simpa [card_powerset] using card_le_card hsub
  have hsum_fibers :
      Bhi.card = ∑ A' ∈ A.powersetCard a, (Bhi.filter (fun w ↦ f w = A')).card := by
    rw [card_eq_sum_card_fiberwise hf_mem]
  have hex_fiber : ∃ A' ∈ A.powersetCard a,
      Bhi.card ≤ 2 ^ A.card * (Bhi.filter (fun w ↦ f w = A')).card := by
    by_contra h
    push Not at h
    have hne : (A.powersetCard a).Nonempty := by
      rw [← card_pos, card_powersetCard]
      exact Nat.choose_pos (by omega)
    have hlt :
        ∑ A' ∈ A.powersetCard a, 2 ^ A.card * (Bhi.filter (fun w ↦ f w = A')).card <
          ∑ _A' ∈ A.powersetCard a, Bhi.card :=
      sum_lt_sum_of_nonempty hne (fun A' hA' ↦ h A' hA')
    rw [← mul_sum, ← hsum_fibers, sum_const, smul_eq_mul] at hlt
    have hle : (A.powersetCard a).card * Bhi.card ≤ 2 ^ A.card * Bhi.card :=
      Nat.mul_le_mul_right Bhi.card hpow_le
    omega
  obtain ⟨A', hA'mem, hA'fib⟩ := hex_fiber
  rw [mem_powersetCard] at hA'mem
  refine ⟨A', hA'mem.1, hA'mem.2, Bhi.filter (fun w ↦ f w = A'),
    (filter_subset _ _).trans (filter_subset _ _), ?_, ?_⟩
  · calc
      B.card ≤ 4 * Bhi.card := hBhi_card
      _ ≤ 4 * (2 ^ A.card * (Bhi.filter (fun w ↦ f w = A')).card) := Nat.mul_le_mul_left 4 hA'fib
      _ = 4 * 2 ^ A.card * (Bhi.filter (fun w ↦ f w = A')).card := by ring
  · intro u hu w hw
    rw [mem_filter] at hw
    rw [← hw.2] at hu
    exact hf_R w hw.1 u hu

lemma kst_graph_complete_bipartite {n : ℕ}
    (S : Finset (Fin n)) (G : Finset (Finset (Fin n))) (hGsub : G ⊆ S.powersetCard 2)
    (D t : ℕ) (ht_pos : 0 < t)
    (hG_dense : S.card ^ 2 ≤ 2 ^ D * G.card)
    (hS_large : 2 * t * 2 ^ D ≤ S.card) :
    ∃ U ⊆ S, U.card = t ∧
      ∃ W ⊆ S, Disjoint U W ∧
        S.card ≤ (2 ^ (D + 1)) ^ (t + 1) * W.card ∧
        ∀ u ∈ U, ∀ w ∈ W, ({u, w} : Finset (Fin n)) ∈ G := by
  let deg : Fin n → ℕ := fun v ↦ (S.filter (fun w ↦ ({v, w} : Finset (Fin n)) ∈ G)).card
  have hsum_deg : ∑ v ∈ S, deg v = 2 * G.card := by
    have h1 : ∑ v ∈ S, deg v =
        ∑ v ∈ S, ∑ e ∈ G, if v ∈ e then 1 else 0 := by
      refine sum_congr rfl ?_
      intro v hv
      rw [sum_boole, Nat.cast_id]
      dsimp [deg]
      refine Finset.card_bij (fun w _ ↦ ({v, w} : Finset (Fin n))) ?_ ?_ ?_
      · intro w hw
        rw [mem_filter] at hw
        rw [mem_filter]
        exact ⟨hw.2, mem_insert_self v {w}⟩
      · intro w₁ hw₁ w₂ hw₂ hEq
        rw [mem_filter] at hw₁ hw₂
        have h2₁ : ({v, w₁} : Finset (Fin n)).card = 2 := (mem_powersetCard.mp (hGsub hw₁.2)).2
        have h2₂ : ({v, w₂} : Finset (Fin n)).card = 2 := (mem_powersetCard.mp (hGsub hw₂.2)).2
        have hne₁ : v ≠ w₁ := fun h ↦ by subst h; simp at h2₁
        have hmem : w₁ ∈ ({v, w₂} : Finset (Fin n)) := by
          rw [← hEq]; simp
        rcases mem_insert.mp hmem with h | h
        · exact absurd h.symm hne₁
        · exact mem_singleton.mp h
      · intro e he
        rw [mem_filter] at he
        have he2 := mem_powersetCard.mp (hGsub he.1)
        obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he2.2
        rcases mem_insert.mp he.2 with rfl | hvy
        · refine ⟨y, ?_, rfl⟩
          rw [mem_filter]
          exact ⟨he2.1 (by simp), he.1⟩
        · have hveq : v = y := mem_singleton.mp hvy
          subst hveq
          refine ⟨x, ?_, pair_comm v x⟩
          rw [mem_filter]
          exact ⟨he2.1 (by simp), by rw [pair_comm]; exact he.1⟩
    rw [h1, sum_comm]
    have h2 : ∑ e ∈ G, ∑ v ∈ S, (if v ∈ e then 1 else 0) = ∑ _e ∈ G, 2 := by
      refine sum_congr rfl ?_
      intro e he
      have he2 := mem_powersetCard.mp (hGsub he)
      rw [sum_boole, Nat.cast_id]
      have hfilt : S.filter (fun v ↦ v ∈ e) = e := by
        ext v
        simp only [mem_filter]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨he2.1 h, h⟩⟩
      rw [hfilt, he2.2]
    rw [h2, sum_const, smul_eq_mul, mul_comm]
  let Shi := S.filter (fun v ↦ S.card ≤ 2 ^ D * deg v)
  have hShi_card : S.card ≤ 2 ^ D * Shi.card := by
    have hsplit :
        ∑ v ∈ S, deg v =
          ∑ v ∈ Shi, deg v + ∑ v ∈ S.filter (fun v ↦ ¬ (S.card ≤ 2 ^ D * deg v)), deg v :=
      (sum_filter_add_sum_filter_not S (fun v ↦ S.card ≤ 2 ^ D * deg v) deg).symm
    have h1 : ∑ v ∈ Shi, deg v ≤ Shi.card * S.card := by
      calc
        ∑ v ∈ Shi, deg v ≤ ∑ _v ∈ Shi, S.card := sum_le_sum (fun v _ ↦ card_filter_le S _)
        _ = Shi.card * S.card := by simp
    have h2 : 2 ^ D * ∑ v ∈ S.filter (fun v ↦ ¬ (S.card ≤ 2 ^ D * deg v)), deg v ≤ S.card ^ 2 := by
      rw [mul_sum]
      calc
        ∑ v ∈ S.filter (fun v ↦ ¬ (S.card ≤ 2 ^ D * deg v)), 2 ^ D * deg v
            ≤ ∑ _v ∈ S.filter (fun v ↦ ¬ (S.card ≤ 2 ^ D * deg v)), S.card := by
              refine sum_le_sum ?_
              intro v hv
              rw [mem_filter] at hv
              omega
        _ = (S.filter (fun v ↦ ¬ (S.card ≤ 2 ^ D * deg v))).card * S.card := by simp
        _ ≤ S.card * S.card := Nat.mul_le_mul_right S.card (card_filter_le S _)
        _ = S.card ^ 2 := (sq S.card).symm
    have htot : 2 * S.card ^ 2 ≤ 2 ^ D * ∑ v ∈ S, deg v := by
      rw [hsum_deg]
      have := Nat.mul_le_mul_left 2 hG_dense
      linarith
    have hSpos : 0 < S.card := by
      have : 0 < 2 ^ D := by positivity
      have : 0 < 2 * t * 2 ^ D := by positivity
      omega
    have hineq : S.card * S.card ≤ (2 ^ D * Shi.card) * S.card := by
      have : 2 ^ D * ∑ v ∈ S, deg v ≤ 2 ^ D * (Shi.card * S.card) + S.card ^ 2 := by
        rw [hsplit, mul_add]
        have := Nat.mul_le_mul_left (2 ^ D) h1
        omega
      nlinarith
    exact Nat.le_of_mul_le_mul_right hineq hSpos
  have hdesc_hi : ∀ v ∈ Shi, S.card ^ t ≤ (2 ^ (D + 1)) ^ t * ((deg v).descFactorial t) := by
    intro v hv
    rw [mem_filter] at hv
    have hdeg_ge : S.card ≤ 2 ^ D * deg v := hv.2
    have hloop : ∀ k : ℕ, k ≤ t → S.card ^ k ≤ (2 ^ (D + 1)) ^ k * ((deg v).descFactorial k) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_succ, Nat.descFactorial_succ]
        have hstep : S.card ≤ 2 ^ (D + 1) * (deg v - k) := by
          have h2 : 2 * k * 2 ^ D ≤ S.card := by
            have : 2 * k ≤ 2 * t := by omega
            calc
              2 * k * 2 ^ D ≤ 2 * t * 2 ^ D := Nat.mul_le_mul_right (2 ^ D) this
              _ ≤ S.card := hS_large
          have h3 : 2 * k ≤ deg v := by
            have h2Dpos : 0 < 2 ^ D := by positivity
            have : 2 * k * 2 ^ D ≤ deg v * 2 ^ D := by linarith
            exact Nat.le_of_mul_le_mul_right this h2Dpos
          have h4 : 2 * (deg v - k) ≥ deg v := by omega
          have hpow : 2 ^ (D + 1) = 2 ^ D * 2 := pow_succ 2 D
          rw [hpow, mul_assoc]
          calc
            S.card ≤ 2 ^ D * deg v := hdeg_ge
            _ ≤ 2 ^ D * (2 * (deg v - k)) := Nat.mul_le_mul_left (2 ^ D) h4
        calc
          S.card ^ k * S.card
              ≤ ((2 ^ (D + 1)) ^ k * (deg v).descFactorial k) * (2 ^ (D + 1) * (deg v - k)) :=
                Nat.mul_le_mul (ih (by omega)) hstep
          _ = (2 ^ (D + 1)) ^ k * 2 ^ (D + 1) * ((deg v - k) * (deg v).descFactorial k) := by ring
    exact hloop t le_rfl
  let Wof : Finset (Fin n) → Finset (Fin n) :=
    fun U ↦ S.filter (fun v ↦ ∀ u ∈ U, ({u, v} : Finset (Fin n)) ∈ G)
  have hdouble :
      ∑ v ∈ Shi, (deg v).choose t ≤ ∑ U ∈ S.powersetCard t, (Wof U).card := by
    have hL :
        ∑ v ∈ Shi, (deg v).choose t =
          ∑ v ∈ Shi, ∑ U ∈ S.powersetCard t, if ∀ u ∈ U, ({u, v} : Finset (Fin n)) ∈ G then 1 else 0 := by
      refine sum_congr rfl ?_
      intro v _
      rw [sum_boole, Nat.cast_id]
      have hfilt : (S.powersetCard t).filter (fun U ↦ ∀ u ∈ U, ({u, v} : Finset (Fin n)) ∈ G) =
          (S.filter (fun w ↦ ({v, w} : Finset (Fin n)) ∈ G)).powersetCard t := by
        ext U
        simp only [mem_filter, mem_powersetCard]
        constructor
        · rintro ⟨⟨hUS, hUt⟩, hUadj⟩
          refine ⟨?_, hUt⟩
          intro u hu
          rw [mem_filter]
          exact ⟨hUS hu, by rw [pair_comm]; exact hUadj u hu⟩
        · rintro ⟨hUsub, hUt⟩
          refine ⟨⟨hUsub.trans (filter_subset _ _), hUt⟩, ?_⟩
          intro u hu
          rw [pair_comm]
          exact (mem_filter.mp (hUsub hu)).2
      rw [hfilt, card_powersetCard]
    rw [hL, sum_comm]
    refine sum_le_sum ?_
    intro U _
    rw [sum_boole, Nat.cast_id]
    refine card_le_card ?_
    intro v hv
    rw [mem_filter] at hv
    rw [mem_filter]
    exact ⟨(filter_subset _ _) hv.1, hv.2⟩
  have hsum_lower :
      S.card ^ (t + 1) ≤
        (2 ^ (D + 1)) ^ (t + 1) * (t.factorial * ∑ U ∈ S.powersetCard t, (Wof U).card) := by
    have h1 : Shi.card * S.card ^ t ≤
        (2 ^ (D + 1)) ^ t * (t.factorial * ∑ v ∈ Shi, (deg v).choose t) := by
      rw [mul_sum, mul_sum]
      calc
        Shi.card * S.card ^ t = ∑ _v ∈ Shi, S.card ^ t := by simp
        _ ≤ ∑ v ∈ Shi, (2 ^ (D + 1)) ^ t * ((deg v).descFactorial t) := sum_le_sum hdesc_hi
        _ = ∑ v ∈ Shi, (2 ^ (D + 1)) ^ t * (t.factorial * (deg v).choose t) := by
              refine sum_congr rfl ?_
              intro v _
              rw [Nat.descFactorial_eq_factorial_mul_choose]
    have h2 : S.card ^ (t + 1) ≤ 2 ^ (D + 1) * (Shi.card * S.card ^ t) := by
      have hpow : 2 ^ D ≤ 2 ^ (D + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc
        S.card ^ (t + 1) = S.card * S.card ^ t := by rw [pow_succ, mul_comm]
        _ ≤ (2 ^ D * Shi.card) * S.card ^ t := Nat.mul_le_mul_right _ hShi_card
        _ ≤ (2 ^ (D + 1) * Shi.card) * S.card ^ t :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)
        _ = 2 ^ (D + 1) * (Shi.card * S.card ^ t) := by ring
    calc
      S.card ^ (t + 1) ≤ 2 ^ (D + 1) * (Shi.card * S.card ^ t) := h2
      _ ≤ 2 ^ (D + 1) * ((2 ^ (D + 1)) ^ t * (t.factorial * ∑ v ∈ Shi, (deg v).choose t)) :=
            Nat.mul_le_mul_left _ h1
      _ = (2 ^ (D + 1)) ^ (t + 1) * (t.factorial * ∑ v ∈ Shi, (deg v).choose t) := by
            rw [pow_succ]; ring
      _ ≤ (2 ^ (D + 1)) ^ (t + 1) * (t.factorial * ∑ U ∈ S.powersetCard t, (Wof U).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdouble)
  have hne : (S.powersetCard t).Nonempty := by
    rw [← card_pos, card_powersetCard]
    have h2D : 1 ≤ 2 ^ D := Nat.one_le_pow D 2 (by norm_num)
    have htS : t ≤ S.card := by
      have : t ≤ 2 * t * 2 ^ D := by nlinarith
      omega
    exact Nat.choose_pos htS
  have hexU : ∃ U ∈ S.powersetCard t, S.card ≤ (2 ^ (D + 1)) ^ (t + 1) * (Wof U).card := by
    by_contra h
    push Not at h
    have hlt :
        ∑ U ∈ S.powersetCard t, (2 ^ (D + 1)) ^ (t + 1) * (Wof U).card <
          ∑ _U ∈ S.powersetCard t, S.card :=
      sum_lt_sum_of_nonempty hne (fun U hU ↦ h U hU)
    rw [← mul_sum, sum_const, smul_eq_mul, card_powersetCard] at hlt
    have hlt2 := Nat.mul_lt_mul_of_pos_left hlt (Nat.factorial_pos t)
    have hfact_choose : t.factorial * S.card.choose t ≤ S.card ^ t := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow S.card t
    have hupper : t.factorial * (S.card.choose t * S.card) ≤ S.card ^ (t + 1) := by
      calc
        t.factorial * (S.card.choose t * S.card)
            = (t.factorial * S.card.choose t) * S.card := by ring
        _ ≤ S.card ^ t * S.card := Nat.mul_le_mul_right S.card hfact_choose
        _ = S.card ^ (t + 1) := (pow_succ S.card t).symm
    have hswap :
        t.factorial * ((2 ^ (D + 1)) ^ (t + 1) * ∑ U ∈ S.powersetCard t, (Wof U).card) =
          (2 ^ (D + 1)) ^ (t + 1) * (t.factorial * ∑ U ∈ S.powersetCard t, (Wof U).card) := by
      ring
    omega
  obtain ⟨U, hUmem, hUW⟩ := hexU
  rw [mem_powersetCard] at hUmem
  refine ⟨U, hUmem.1, hUmem.2, Wof U, filter_subset _ _, ?_, hUW, ?_⟩
  · rw [Finset.disjoint_left]
    intro u huU huW
    rw [mem_filter] at huW
    have hmemG : ({u, u} : Finset (Fin n)) ∈ G := huW.2 u huU
    have hcard2 := (mem_powersetCard.mp (hGsub hmemG)).2
    simp at hcard2
  · intro u hu w hw
    exact (mem_filter.mp hw).2 u hu

/- ### Part 3: Conlon--Fox--Sudakov Iterative Extraction -/

lemma cfs_inner_loop {n : ℕ} (col : Finset (Fin n) → Bool)
    (m_next : ℕ) (hm_pos : 0 < m_next)
    (S : Finset (Fin n)) (G0 : Finset (Finset (Fin n))) (_hG0sub : G0 ⊆ S.powersetCard 2) :
    ∀ k : ℕ, ∀ V : ℕ → Finset (Fin n),
      (∀ h < k, (V h).card = 4 * m_next ∧ Disjoint (V h) S) →
      ∃ (V' : ℕ → Finset (Fin n)) (χ : ℕ → Bool) (Gk : Finset (Finset (Fin n))),
        Gk ⊆ G0 ∧
        G0.card ≤ (2 ^ (4 * m_next + 2)) ^ k * Gk.card ∧
        (∀ h < k, V' h ⊆ V h ∧ (V' h).card = m_next ∧
          ∀ u ∈ V' h, ∀ e ∈ Gk, col (insert u e) = χ h) := by
  intro k
  induction k with
  | zero =>
    intro V _
    refine ⟨V, fun _ ↦ false, G0, Subset.rfl, by simp, ?_⟩
    intro h hh
    omega
  | succ k ih =>
    intro V hV
    obtain ⟨V', χ, Gk, hGksub, hGkcard, hV'⟩ := ih V (fun h hh ↦ hV h (by omega))
    have hVk := hV k (by omega)
    let A := V k
    have hsum_colors :
        (∑ e ∈ Gk, (A.filter (fun u ↦ col (insert u e) = true)).card) +
        (∑ e ∈ Gk, (A.filter (fun u ↦ col (insert u e) = false)).card) =
          A.card * Gk.card := by
      rw [← sum_add_distrib]
      have hterm : ∀ e ∈ Gk,
          (A.filter (fun u ↦ col (insert u e) = true)).card +
          (A.filter (fun u ↦ col (insert u e) = false)).card = A.card := by
        intro e _
        have hfalse : A.filter (fun u ↦ col (insert u e) = false) =
            A.filter (fun u ↦ ¬ (col (insert u e) = true)) := by
          ext u; simp
        rw [hfalse]
        simpa using Finset.sum_filter_add_sum_filter_not A (fun u ↦ col (insert u e) = true) (fun _ ↦ (1 : ℕ))
      rw [sum_congr rfl hterm, sum_const, smul_eq_mul, mul_comm]
    have hex_col : ∃ c : Bool,
        A.card * Gk.card ≤ 2 * ∑ e ∈ Gk, (A.filter (fun u ↦ col (insert u e) = c)).card := by
      by_cases h : A.card * Gk.card ≤
          2 * ∑ e ∈ Gk, (A.filter (fun u ↦ col (insert u e) = true)).card
      · exact ⟨true, h⟩
      · exact ⟨false, by omega⟩
    obtain ⟨c, hc⟩ := hex_col
    obtain ⟨Ak', hAk'sub, hAk'card, Gnext, hGnextsub, hGnextcard, hAk'col⟩ :=
      kst_bipartite_quarter A Gk (fun u e ↦ col (insert u e) = c) m_next hVk.1 hm_pos hc
    refine ⟨fun h ↦ if h = k then Ak' else V' h,
            fun h ↦ if h = k then c else χ h,
            Gnext, hGnextsub.trans hGksub, ?_, ?_⟩
    · have hpow : 4 * 2 ^ A.card = 2 ^ (4 * m_next + 2) := by
        rw [hVk.1, pow_add]
        norm_num
        ring
      calc
        G0.card ≤ (2 ^ (4 * m_next + 2)) ^ k * Gk.card := hGkcard
        _ ≤ (2 ^ (4 * m_next + 2)) ^ k * (4 * 2 ^ A.card * Gnext.card) :=
              Nat.mul_le_mul_left _ hGnextcard
        _ = (2 ^ (4 * m_next + 2)) ^ (k + 1) * Gnext.card := by
              rw [hpow, pow_succ]; ring
    · intro h hh
      by_cases hhk : h = k
      · subst hhk
        simp only [↓reduceIte]
        exact ⟨hAk'sub, hAk'card, hAk'col⟩
      · simp only [hhk, ↓reduceIte]
        have hprev := hV' h (by omega)
        exact ⟨hprev.1, hprev.2.1, fun u hu e he ↦ hprev.2.2 u hu e (hGnextsub he)⟩

lemma cfs_rounds {n : ℕ} (col : Finset (Fin n) → Bool)
    (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (E : ℕ) (hE : 2 + r * (4 ^ r * m + 2) ≤ E * m)
    (hn : 2 ^ ((r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4) * m ^ 2) ≤ n) :
    ∀ i : ℕ, 1 ≤ i → i ≤ r →
      ∃ (V : ℕ → Finset (Fin n)) (S : Finset (Fin n)) (χ : ℕ → ℕ → Bool),
        (∀ a < i, (V a).card = 4 ^ (r - i) * m) ∧
        (∀ a < i, ∀ b < i, a ≠ b → Disjoint (V a) (V b)) ∧
        (∀ a < i, Disjoint (V a) S) ∧
        n ≤ 2 ^ ((i * (E + 1) * (4 ^ r + 1)) * m ^ 2) * S.card ∧
        (∀ a < i, ∀ b < i, a < b →
          (∀ c < i, b < c → ∀ x ∈ V a, ∀ y ∈ V b, ∀ z ∈ V c, col {x, y, z} = χ a b) ∧
          (∀ x ∈ V a, ∀ y ∈ V b, ∀ z ∈ S, col {x, y, z} = χ a b)) := by
  intro i hi hir
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hi0 : i = 0
    · subst hi0
      have hm1_le : 4 ^ (r - 1) * m ≤ n := by
        have h1 : 4 ^ (r - 1) * m ≤ 2 ^ (4 ^ r * m ^ 2) := by
          have h4 : 4 ^ (r - 1) ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hlin : 4 ^ (r - 1) * m ≤ 4 ^ r * m ^ 2 :=
            Nat.mul_le_mul h4 (by nlinarith)
          exact le_trans hlin (Nat.le_of_lt (Nat.lt_two_pow_self))
        have h2 : 4 ^ r * m ^ 2 ≤ (r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4) * m ^ 2 :=
          Nat.mul_le_mul_right (m ^ 2) (by omega)
        exact le_trans h1 (le_trans (Nat.pow_le_pow_right (by norm_num) h2) hn)
      have h2m1_le : 2 * (4 ^ (r - 1) * m) ≤ n := by
        have hlin : 2 * (4 ^ (r - 1) * m) ≤ (4 ^ r + 4) * m ^ 2 := by
          have h4' : 2 * 4 ^ (r - 1) ≤ 4 ^ r := by
            have : 4 ^ r = 4 * 4 ^ (r - 1) := by
              conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ, mul_comm]
            omega
          calc
            2 * (4 ^ (r - 1) * m) = (2 * 4 ^ (r - 1)) * m := by ring
            _ ≤ (4 ^ r + 4) * m ^ 2 := Nat.mul_le_mul (by omega) (by nlinarith)
        have h1 : 2 * (4 ^ (r - 1) * m) ≤ 2 ^ ((4 ^ r + 4) * m ^ 2) :=
          le_trans hlin (Nat.le_of_lt Nat.lt_two_pow_self)
        have h2 : (4 ^ r + 4) * m ^ 2 ≤ (r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4) * m ^ 2 :=
          Nat.mul_le_mul_right (m ^ 2) (by omega)
        exact le_trans h1 (le_trans (Nat.pow_le_pow_right (by norm_num) h2) hn)
      obtain ⟨V0, _, hV0card⟩ :=
        exists_subset_card_eq (show 4 ^ (r - 1) * m ≤ (Finset.univ : Finset (Fin n)).card by
          simpa using hm1_le)
      let S1 := (Finset.univ : Finset (Fin n)) \ V0
      refine ⟨fun _ ↦ V0, S1, fun _ _ ↦ false, ?_, ?_, ?_, ?_, ?_⟩
      · intro a ha; exact hV0card
      · intro a ha b hb hab; omega
      · intro a _; exact disjoint_sdiff
      · have hS1card : S1.card = n - 4 ^ (r - 1) * m := by
          rw [card_sdiff_of_subset (subset_univ V0), card_univ, Fintype.card_fin, hV0card]
        have hn2 : n ≤ 2 * S1.card := by omega
        have hpow : 2 ≤ 2 ^ ((1 * (E + 1) * (4 ^ r + 1)) * m ^ 2) := by
          have hexp : 1 ≤ (1 * (E + 1) * (4 ^ r + 1)) * m ^ 2 :=
            Nat.succ_le_of_lt (by positivity)
          calc
            2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ ((1 * (E + 1) * (4 ^ r + 1)) * m ^ 2) :=
              Nat.pow_le_pow_right (by norm_num) hexp
        exact le_trans hn2 (Nat.mul_le_mul_right S1.card hpow)
      · intro a ha b hb hab; omega
    · have hi1 : 1 ≤ i := by omega
      obtain ⟨V, S, χ, hVcard, hVdisj, hVSdisj, hScard, hVcol⟩ := ih hi1 (by omega)
      let m_next := 4 ^ (r - (i + 1)) * m
      have hm_next_pos : 0 < m_next := by positivity
      have hm_step : 4 ^ (r - i) * m = 4 * m_next := by
        dsimp [m_next]
        have hsub : r - i = (r - (i + 1)) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      have hV4 : ∀ a < i, (V a).card = 4 * m_next ∧ Disjoint (V a) S := fun a ha ↦
        ⟨by rw [hVcard a ha, hm_step], hVSdisj a ha⟩
      let G0 := S.powersetCard 2
      obtain ⟨V', χnew, Gi, hGisub, hGicard, hV'⟩ :=
        cfs_inner_loop col m_next hm_next_pos S G0 Subset.rfl i V hV4
      have hS_big : 2 ^ ((E + 4 ^ r + 4) * m ^ 2) ≤ S.card := by
        have hK_le : i * (E + 1) * (4 ^ r + 1) * m ^ 2 + (E + 4 ^ r + 4) * m ^ 2 ≤
            (r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4) * m ^ 2 := by
          have hir' : i ≤ r := by omega
          have h1 : i * (E + 1) * (4 ^ r + 1) ≤ r * (E + 1) * (4 ^ r + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hir')
          nlinarith
        have hpow_le := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hK_le
        rw [pow_add] at hpow_le
        have hmul : 2 ^ (i * (E + 1) * (4 ^ r + 1) * m ^ 2) * 2 ^ ((E + 4 ^ r + 4) * m ^ 2) ≤
            2 ^ (i * (E + 1) * (4 ^ r + 1) * m ^ 2) * S.card :=
          le_trans hpow_le (le_trans hn hScard)
        exact Nat.le_of_mul_le_mul_left hmul (by positivity)
      have hS_ge2 : 2 ≤ S.card := by
        have h1 : 1 ≤ (E + 4 ^ r + 4) * m ^ 2 := Nat.succ_le_of_lt (by positivity)
        calc
          2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ ((E + 4 ^ r + 4) * m ^ 2) := Nat.pow_le_pow_right (by norm_num) h1
          _ ≤ S.card := hS_big
      have hG0_dense : S.card ^ 2 ≤ 4 * G0.card := by
        rw [card_powersetCard, Nat.choose_two_right]
        have h2 : S.card * (S.card - 1) ≤ 2 * (S.card * (S.card - 1) / 2) := by
          have heven : Even (S.card * (S.card - 1)) := Nat.even_mul_pred_self S.card
          rcases heven with ⟨q, hq⟩
          omega
        have h3 : S.card ^ 2 ≤ 2 * (S.card * (S.card - 1)) := by
          calc
            S.card ^ 2 = S.card * S.card := sq _
            _ ≤ S.card * (2 * (S.card - 1)) := Nat.mul_le_mul_left S.card (by omega)
            _ = 2 * (S.card * (S.card - 1)) := by ring
        omega
      have hD_bound : 2 + i * (4 * m_next + 2) ≤ E * m := by
        have h4m : 4 * m_next ≤ 4 ^ r * m := by
          rw [← hm_step]
          exact Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by norm_num) (by omega))
        have h1 : 2 + i * (4 * m_next + 2) ≤ 2 + r * (4 ^ r * m + 2) := by
          have : i * (4 * m_next + 2) ≤ r * (4 ^ r * m + 2) :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
        exact le_trans h1 hE
      let D := E * m
      have hGi_dense : S.card ^ 2 ≤ 2 ^ D * Gi.card := by
        have hpow_step : 4 * (2 ^ (4 * m_next + 2)) ^ i = 2 ^ (2 + i * (4 * m_next + 2)) := by
          rw [← pow_mul, pow_add]
          norm_num
          ring
        have hpow_le : 2 ^ (2 + i * (4 * m_next + 2)) ≤ 2 ^ D :=
          Nat.pow_le_pow_right (by norm_num) hD_bound
        calc
          S.card ^ 2 ≤ 4 * G0.card := hG0_dense
          _ ≤ 4 * ((2 ^ (4 * m_next + 2)) ^ i * Gi.card) := Nat.mul_le_mul_left 4 hGicard
          _ = (4 * (2 ^ (4 * m_next + 2)) ^ i) * Gi.card := by ring
          _ = 2 ^ (2 + i * (4 * m_next + 2)) * Gi.card := by rw [hpow_step]
          _ ≤ 2 ^ D * Gi.card := Nat.mul_le_mul_right Gi.card hpow_le
      have hS_large : 2 * m_next * 2 ^ D ≤ S.card := by
        have hm_le : 2 * m_next ≤ 2 ^ ((4 ^ r + 4) * m ^ 2) := by
          have hlin : 2 * m_next ≤ (4 ^ r + 4) * m ^ 2 := by
            dsimp [m_next]
            have h4' : 2 * 4 ^ (r - (i + 1)) ≤ 4 ^ r := by
              have : 4 ^ r = 4 * 4 ^ (r - 1) := by
                conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ, mul_comm]
              have : 4 ^ (r - (i + 1)) ≤ 4 ^ (r - 1) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
            calc
              2 * (4 ^ (r - (i + 1)) * m) = (2 * 4 ^ (r - (i + 1))) * m := by ring
              _ ≤ (4 ^ r + 4) * m ^ 2 := Nat.mul_le_mul (by omega) (by nlinarith)
          exact le_trans hlin (Nat.le_of_lt Nat.lt_two_pow_self)
        have hD_le : D ≤ E * m ^ 2 := by
          dsimp [D]
          have : m ≤ m ^ 2 := by nlinarith
          exact Nat.mul_le_mul_left E this
        calc
          2 * m_next * 2 ^ D ≤ 2 ^ ((4 ^ r + 4) * m ^ 2) * 2 ^ (E * m ^ 2) :=
            Nat.mul_le_mul hm_le (Nat.pow_le_pow_right (by norm_num) hD_le)
          _ = 2 ^ ((E + 4 ^ r + 4) * m ^ 2) := by
            rw [← pow_add]; congr 1; ring
          _ ≤ S.card := hS_big
      obtain ⟨U, hUS, hUcard, W, hWS, hUWdisj, hWcard, hUWedge⟩ :=
        kst_graph_complete_bipartite S Gi hGisub D m_next hm_next_pos hGi_dense hS_large
      let Vnew : ℕ → Finset (Fin n) := fun a ↦ if a = i then U else V' a
      let χfull : ℕ → ℕ → Bool := fun a b ↦ if b = i then χnew a else χ a b
      refine ⟨Vnew, W, χfull, ?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        dsimp [Vnew]
        by_cases hai : a = i
        · simp [hai, hUcard, m_next]
        · simp only [hai, ↓reduceIte]
          exact (hV' a (by omega)).2.1
      · intro a ha b hb hab
        dsimp [Vnew]
        by_cases hai : a = i
        · have hbi : b ≠ i := by omega
          simp only [hai, hbi, ↓reduceIte]
          exact (hVSdisj b (by omega)).symm.mono hUS (hV' b (by omega)).1
        · by_cases hbi : b = i
          · simp only [hai, hbi, ↓reduceIte]
            exact (hVSdisj a (by omega)).mono (hV' a (by omega)).1 hUS
          · simp only [hai, hbi, ↓reduceIte]
            exact (hVdisj a (by omega) b (by omega) hab).mono
              (hV' a (by omega)).1 (hV' b (by omega)).1
      · intro a ha
        dsimp [Vnew]
        by_cases hai : a = i
        · simp only [hai, ↓reduceIte]
          exact hUWdisj
        · simp only [hai, ↓reduceIte]
          exact (hVSdisj a (by omega)).mono (hV' a (by omega)).1 hWS
      · have hexp_shrink : (D + 1) * (m_next + 1) ≤ (E + 1) * (4 ^ r + 1) * m ^ 2 := by
          have h1 : D + 1 ≤ (E + 1) * m := by
            dsimp [D]
            calc
              E * m + 1 ≤ E * m + m := Nat.add_le_add_left hm _
              _ = (E + 1) * m := by ring
          have h2 : m_next + 1 ≤ (4 ^ r + 1) * m := by
            dsimp [m_next]
            have h4 : 4 ^ (r - (i + 1)) ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
            calc
              4 ^ (r - (i + 1)) * m + 1 ≤ 4 ^ r * m + m :=
                Nat.add_le_add (Nat.mul_le_mul_right m h4) hm
              _ = (4 ^ r + 1) * m := by ring
          calc
            (D + 1) * (m_next + 1) ≤ ((E + 1) * m) * ((4 ^ r + 1) * m) := Nat.mul_le_mul h1 h2
            _ = (E + 1) * (4 ^ r + 1) * m ^ 2 := by ring
        have hpow_shrink : (2 ^ (D + 1)) ^ (m_next + 1) ≤ 2 ^ ((E + 1) * (4 ^ r + 1) * m ^ 2) := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) hexp_shrink
        calc
          n ≤ 2 ^ ((i * (E + 1) * (4 ^ r + 1)) * m ^ 2) * S.card := hScard
          _ ≤ 2 ^ ((i * (E + 1) * (4 ^ r + 1)) * m ^ 2) *
                ((2 ^ (D + 1)) ^ (m_next + 1) * W.card) :=
                Nat.mul_le_mul_left _ hWcard
          _ ≤ 2 ^ ((i * (E + 1) * (4 ^ r + 1)) * m ^ 2) *
                (2 ^ ((E + 1) * (4 ^ r + 1) * m ^ 2) * W.card) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right W.card hpow_shrink)
          _ = 2 ^ (((i + 1) * (E + 1) * (4 ^ r + 1)) * m ^ 2) * W.card := by
                rw [← mul_assoc, ← pow_add]
                congr 2
                ring
      · intro a ha b hb hab
        by_cases hbi : b = i
        · subst hbi
          have hai : a ≠ b := by omega
          constructor
          · intro c hc hbc; omega
          · intro x hx y hy z hz
            dsimp [Vnew, χfull] at hx hy ⊢
            simp only [hai, ↓reduceIte] at hx ⊢
            simp only [↓reduceIte] at hy
            have hedge : ({y, z} : Finset (Fin n)) ∈ Gi := hUWedge y hy z hz
            have hcol := (hV' a (by omega)).2.2 x hx {y, z} hedge
            simpa using hcol
        · have hbi_lt : b < i := by omega
          have hai : a ≠ i := by omega
          have hprev := hVcol a (by omega) b hbi_lt hab
          constructor
          · intro c hc hbc x hx y hy z hz
            dsimp [Vnew, χfull] at hx hy hz ⊢
            simp only [hai, hbi, ↓reduceIte] at hx hy ⊢
            by_cases hci : c = i
            · simp only [hci, ↓reduceIte] at hz
              exact hprev.2 x ((hV' a (by omega)).1 hx) y ((hV' b hbi_lt).1 hy) z (hUS hz)
            · simp only [hci, ↓reduceIte] at hz
              exact hprev.1 c (by omega) hbc
                x ((hV' a (by omega)).1 hx) y ((hV' b hbi_lt).1 hy) z ((hV' c (by omega)).1 hz)
          · intro x hx y hy z hz
            dsimp [Vnew, χfull] at hx hy ⊢
            simp only [hai, hbi, ↓reduceIte] at hx hy ⊢
            exact hprev.2 x ((hV' a (by omega)).1 hx) y ((hV' b hbi_lt).1 hy) z (hWS hz)

/- ### Part 4: Monochromatic Complete d-Partite 3-Graph -> Almost-Monochromatic Subset -/

lemma exists_monochromatic_multipartite {n : ℕ} (col : Finset (Fin n) → Bool)
    (d m : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m) :
    let r := (2 * (d - 1)).choose (d - 1)
    let E := 2 + r * (4 ^ r + 2)
    let C := r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4
    2 ^ (C * m ^ 2) ≤ n →
    ∃ b : Bool, ∃ P : Fin d → Finset (Fin n),
      (∀ i, (P i).card = m) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ i j k : Fin d, i < j → j < k →
        ∀ x ∈ P i, ∀ y ∈ P j, ∀ z ∈ P k, col {x, y, z} = b) := by
  intro r E C hn
  have hr : 1 ≤ r := Nat.choose_pos (by omega)
  have hE : 2 + r * (4 ^ r * m + 2) ≤ E * m := by
    dsimp [E]
    nlinarith
  obtain ⟨V, S, χ, hVcard, hVdisj, hVSdisj, hScard, hVcol⟩ :=
    cfs_rounds col r m hr hm E hE hn r hr le_rfl
  have hm_le_S : m ≤ S.card := by
    have h1 : r * (E + 1) * (4 ^ r + 1) * m ^ 2 + m ≤ C * m ^ 2 := by
      dsimp [C]
      have hm2 : m ≤ m ^ 2 := by nlinarith
      have hpos : 0 < E + 4 ^ r + 4 := by positivity
      calc
        r * (E + 1) * (4 ^ r + 1) * m ^ 2 + m
            ≤ r * (E + 1) * (4 ^ r + 1) * m ^ 2 + (E + 4 ^ r + 4) * m ^ 2 :=
              Nat.add_le_add_left (le_trans hm2 (Nat.le_mul_of_pos_left _ hpos)) _
        _ = (r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4) * m ^ 2 := by ring
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h1
    rw [pow_add] at hpow
    have h2 : 2 ^ (r * (E + 1) * (4 ^ r + 1) * m ^ 2) * m ≤
        2 ^ (r * (E + 1) * (4 ^ r + 1) * m ^ 2) * S.card :=
      le_trans (Nat.mul_le_mul_left _ (Nat.le_of_lt Nat.lt_two_pow_self))
        (le_trans hpow (le_trans hn hScard))
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  obtain ⟨Vr, hVrS, hVrcard⟩ := exists_subset_card_eq hm_le_S
  obtain ⟨b, I, hIsub, hIcard, hIcol⟩ := ramsey2_fin (d - 1) χ
  have hI_order : (I.orderEmbOfFin hIcard).toFun = I.orderEmbOfFin hIcard := rfl
  let idx : Fin d → ℕ := fun i ↦
    if hi : i.1 < d - 1 then I.orderEmbOfFin hIcard ⟨i.1, hi⟩ else r
  let P : Fin d → Finset (Fin n) := fun i ↦
    if i.1 < d - 1 then V (idx i) else Vr
  have hidx_lt : ∀ i : Fin d, i.1 < d - 1 → idx i < r := by
    intro i hi
    dsimp [idx]
    rw [dif_pos hi]
    exact mem_range.mp (hIsub (orderEmbOfFin_mem I hIcard ⟨i.1, hi⟩))
  have hidx_mono : ∀ i j : Fin d, i < j → idx i < idx j := by
    intro i j hij
    have hi : i.1 < d - 1 := by omega
    by_cases hj : j.1 < d - 1
    · dsimp [idx]
      rw [dif_pos hi, dif_pos hj]
      exact (I.orderEmbOfFin hIcard).strictMono (show (⟨i.1, hi⟩ : Fin (d - 1)) < ⟨j.1, hj⟩ from hij)
    · dsimp [idx]
      rw [dif_pos hi, dif_neg hj]
      exact mem_range.mp (hIsub (orderEmbOfFin_mem I hIcard ⟨i.1, hi⟩))
  refine ⟨b, P, ?_, ?_, ?_⟩
  · intro i
    dsimp [P]
    by_cases hi : i.1 < d - 1
    · rw [if_pos hi]
      have h := hVcard (idx i) (hidx_lt i hi)
      simpa [Nat.sub_self] using h
    · rw [if_neg hi]
      exact hVrcard
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi : i.1 < d - 1 := by omega
      dsimp [P]
      rw [if_pos hi]
      by_cases hj : j.1 < d - 1
      · rw [if_pos hj]
        exact hVdisj (idx i) (hidx_lt i hi) (idx j) (hidx_lt j hj) (ne_of_lt (hidx_mono i j hlt))
      · rw [if_neg hj]
        exact (hVSdisj (idx i) (hidx_lt i hi)).mono_right hVrS
    · have hj : j.1 < d - 1 := by omega
      dsimp [P]
      rw [if_pos hj]
      by_cases hi : i.1 < d - 1
      · rw [if_pos hi]
        exact hVdisj (idx i) (hidx_lt i hi) (idx j) (hidx_lt j hj) (ne_of_gt (hidx_mono j i hgt))
      · rw [if_neg hi]
        exact (hVSdisj (idx j) (hidx_lt j hj)).symm.mono_left hVrS
  · intro i j k hij hjk x hx y hy z hz
    have hi : i.1 < d - 1 := by omega
    have hj : j.1 < d - 1 := by omega
    dsimp [P] at hx hy hz
    rw [if_pos hi] at hx
    rw [if_pos hj] at hy
    have hidx_i_mem : idx i ∈ I := by
      dsimp [idx]; rw [dif_pos hi]; exact orderEmbOfFin_mem I hIcard ⟨i.1, hi⟩
    have hidx_j_mem : idx j ∈ I := by
      dsimp [idx]; rw [dif_pos hj]; exact orderEmbOfFin_mem I hIcard ⟨j.1, hj⟩
    have hchi : χ (idx i) (idx j) = b :=
      hIcol (idx i) hidx_i_mem (idx j) hidx_j_mem (hidx_mono i j hij)
    rw [← hchi]
    by_cases hk : k.1 < d - 1
    · rw [if_pos hk] at hz
      exact (hVcol (idx i) (hidx_lt i hi) (idx j) (hidx_lt j hj) (hidx_mono i j hij)).1
        (idx k) (hidx_lt k hk) (hidx_mono j k hjk) x hx y hy z hz
    · rw [if_neg hk] at hz
      exact (hVcol (idx i) (hidx_lt i hi) (idx j) (hidx_lt j hj) (hidx_mono i j hij)).2
        x hx y hy z (hVrS hz)

lemma crossing_triples_le_mono {n d m : ℕ} (col : Finset (Fin n) → Bool)
    (b : Bool) (P : Fin d → Finset (Fin n))
    (hcard : ∀ i, (P i).card = m)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcol : ∀ i j k : Fin d, i < j → j < k →
      ∀ x ∈ P i, ∀ y ∈ P j, ∀ z ∈ P k, col {x, y, z} = b) :
    let X := Finset.univ.biUnion P
    X.card = d * m ∧
      d.choose 3 * m ^ 3 ≤ ((X.powersetCard 3).filter (fun e ↦ col e = b)).card := by
  intro X
  have hXcard : X.card = d * m := by
    rw [card_biUnion (fun i _ j _ hij ↦ hdisj i j hij)]
    simp [hcard]
  refine ⟨hXcard, ?_⟩
  let T : Finset (Finset (Fin d)) := (Finset.univ : Finset (Fin d)).powersetCard 3
  let crossOf : Finset (Fin d) → Finset (Finset (Fin n)) := fun s ↦
    if hs : s.card = 3 then
      let i := s.orderEmbOfFin hs ⟨0, by norm_num⟩
      let j := s.orderEmbOfFin hs ⟨1, by norm_num⟩
      let k := s.orderEmbOfFin hs ⟨2, by norm_num⟩
      ((P i ×ˢ P j) ×ˢ P k).image (fun t ↦ ({t.1.1, t.1.2, t.2} : Finset (Fin n)))
    else ∅
  have hcross_sub : ∀ s ∈ T, crossOf s ⊆ (X.powersetCard 3).filter (fun e ↦ col e = b) := by
    intro s hs
    have hscard : s.card = 3 := (mem_powersetCard.mp hs).2
    intro e he
    dsimp [crossOf] at he
    rw [dif_pos hscard] at he
    rcases mem_image.mp he with ⟨⟨⟨x, y⟩, z⟩, hmem, rfl⟩
    rw [mem_product, mem_product] at hmem
    rcases hmem with ⟨⟨hx, hy⟩, hz⟩
    set i := s.orderEmbOfFin hscard ⟨0, by norm_num⟩
    set j := s.orderEmbOfFin hscard ⟨1, by norm_num⟩
    set k := s.orderEmbOfFin hscard ⟨2, by norm_num⟩
    have hij : i < j := (s.orderEmbOfFin hscard).strictMono (by decide)
    have hjk : j < k := (s.orderEmbOfFin hscard).strictMono (by decide)
    have hik : i < k := lt_trans hij hjk
    have hxy : x ≠ y := fun h ↦ Finset.disjoint_left.mp (hdisj i j (ne_of_lt hij)) hx (h ▸ hy)
    have hxz : x ≠ z := fun h ↦ Finset.disjoint_left.mp (hdisj i k (ne_of_lt hik)) hx (h ▸ hz)
    have hyz : y ≠ z := fun h ↦ Finset.disjoint_left.mp (hdisj j k (ne_of_lt hjk)) hy (h ▸ hz)
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, hcol i j k hij hjk x hx y hy z hz⟩
    · intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact mem_biUnion.mpr ⟨i, mem_univ i, hx⟩
      · rcases mem_insert.mp hw with rfl | hw
        · exact mem_biUnion.mpr ⟨j, mem_univ j, hy⟩
        · rw [mem_singleton.mp hw]
          exact mem_biUnion.mpr ⟨k, mem_univ k, hz⟩
    · rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [hyz]
      · simp [hxy, hxz]
  have hcross_card : ∀ s ∈ T, (crossOf s).card = m ^ 3 := by
    intro s hs
    have hscard : s.card = 3 := (mem_powersetCard.mp hs).2
    dsimp [crossOf]
    rw [dif_pos hscard]
    set i := s.orderEmbOfFin hscard ⟨0, by norm_num⟩
    set j := s.orderEmbOfFin hscard ⟨1, by norm_num⟩
    set k := s.orderEmbOfFin hscard ⟨2, by norm_num⟩
    have hij : i < j := (s.orderEmbOfFin hscard).strictMono (by decide)
    have hjk : j < k := (s.orderEmbOfFin hscard).strictMono (by decide)
    have hik : i < k := lt_trans hij hjk
    rw [card_image_of_injOn]
    · simp [card_product, hcard, pow_succ]
    · intro t₁ ht₁ t₂ ht₂ hEq
      simp only [mem_coe, mem_product] at ht₁ ht₂
      rcases t₁ with ⟨⟨x₁, y₁⟩, z₁⟩
      rcases t₂ with ⟨⟨x₂, y₂⟩, z₂⟩
      dsimp only at hEq
      have hx_eq : x₁ = x₂ := by
        have hmem : x₁ ∈ ({x₂, y₂, z₂} : Finset (Fin n)) := by rw [← hEq]; simp
        rcases mem_insert.mp hmem with h | h
        · exact h
        · rcases mem_insert.mp h with h | h
          · exact absurd (h ▸ ht₂.1.2) (Finset.disjoint_left.mp (hdisj i j (ne_of_lt hij)) ht₁.1.1)
          · exact absurd (mem_singleton.mp h ▸ ht₂.2)
              (Finset.disjoint_left.mp (hdisj i k (ne_of_lt hik)) ht₁.1.1)
      have hy_eq : y₁ = y₂ := by
        have hmem : y₁ ∈ ({x₂, y₂, z₂} : Finset (Fin n)) := by rw [← hEq]; simp
        rcases mem_insert.mp hmem with h | h
        · exact absurd (h ▸ ht₂.1.1) (Finset.disjoint_left.mp (hdisj j i (ne_of_gt hij)) ht₁.1.2)
        · rcases mem_insert.mp h with h | h
          · exact h
          · exact absurd (mem_singleton.mp h ▸ ht₂.2)
              (Finset.disjoint_left.mp (hdisj j k (ne_of_lt hjk)) ht₁.1.2)
      have hz_eq : z₁ = z₂ := by
        have hmem : z₁ ∈ ({x₂, y₂, z₂} : Finset (Fin n)) := by rw [← hEq]; simp
        rcases mem_insert.mp hmem with h | h
        · exact absurd (h ▸ ht₂.1.1) (Finset.disjoint_left.mp (hdisj k i (ne_of_gt hik)) ht₁.2)
        · rcases mem_insert.mp h with h | h
          · exact absurd (h ▸ ht₂.1.2) (Finset.disjoint_left.mp (hdisj k j (ne_of_gt hjk)) ht₁.2)
          · exact mem_singleton.mp h
      subst hx_eq; subst hy_eq; subst hz_eq; rfl
  have hcross_disj : Set.PairwiseDisjoint (T : Set (Finset (Fin d))) crossOf := by
    intro s₁ hs₁ s₂ hs₂ hne
    change Disjoint (crossOf s₁) (crossOf s₂)
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    have hs₁c : s₁.card = 3 := (mem_powersetCard.mp hs₁).2
    have hs₂c : s₂.card = 3 := (mem_powersetCard.mp hs₂).2
    dsimp [crossOf] at he₁ he₂
    rw [dif_pos hs₁c] at he₁
    rw [dif_pos hs₂c] at he₂
    rcases mem_image.mp he₁ with ⟨⟨⟨x₁, y₁⟩, z₁⟩, hm₁, rfl⟩
    rcases mem_image.mp he₂ with ⟨⟨⟨x₂, y₂⟩, z₂⟩, hm₂, hEq⟩
    rw [mem_product, mem_product] at hm₁ hm₂
    have huniq : ∀ p q : Fin d, ∀ w : Fin n, w ∈ P p → w ∈ P q → p = q := by
      intro p q w hp hq
      by_contra hpq
      exact Finset.disjoint_left.mp (hdisj p q hpq) hp hq
    have hpart_mem : ∀ a ∈ s₁, a ∈ s₂ := by
      intro a ha
      obtain ⟨idx, hidx⟩ : ∃ idx : Fin 3, s₁.orderEmbOfFin hs₁c idx = a := by
        have hrange : Set.range (s₁.orderEmbOfFin hs₁c) = (s₁ : Set (Fin d)) :=
          range_orderEmbOfFin s₁ hs₁c
        have : a ∈ Set.range (s₁.orderEmbOfFin hs₁c) := by rw [hrange]; exact ha
        exact this
      have hmem2 : ∀ w ∈ ({x₂, y₂, z₂} : Finset (Fin n)),
          ∃ j : Fin 3, w ∈ P (s₂.orderEmbOfFin hs₂c j) := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact ⟨⟨0, by norm_num⟩, hm₂.1.1⟩
        · rcases mem_insert.mp hw with rfl | hw
          · exact ⟨⟨1, by norm_num⟩, hm₂.1.2⟩
          · rw [mem_singleton.mp hw]; exact ⟨⟨2, by norm_num⟩, hm₂.2⟩
      fin_cases idx
      · have hx1 : x₁ ∈ ({x₂, y₂, z₂} : Finset (Fin n)) := by rw [hEq]; simp
        obtain ⟨j, hj⟩ := hmem2 x₁ hx1
        have heq := huniq (s₁.orderEmbOfFin hs₁c ⟨0, by norm_num⟩) (s₂.orderEmbOfFin hs₂c j) x₁ hm₁.1.1 hj
        rw [← hidx, heq]
        exact orderEmbOfFin_mem s₂ hs₂c j
      · have hy1 : y₁ ∈ ({x₂, y₂, z₂} : Finset (Fin n)) := by rw [hEq]; simp
        obtain ⟨j, hj⟩ := hmem2 y₁ hy1
        have heq := huniq (s₁.orderEmbOfFin hs₁c ⟨1, by norm_num⟩) (s₂.orderEmbOfFin hs₂c j) y₁ hm₁.1.2 hj
        rw [← hidx, heq]
        exact orderEmbOfFin_mem s₂ hs₂c j
      · have hz1 : z₁ ∈ ({x₂, y₂, z₂} : Finset (Fin n)) := by rw [hEq]; simp
        obtain ⟨j, hj⟩ := hmem2 z₁ hz1
        have heq := huniq (s₁.orderEmbOfFin hs₁c ⟨2, by norm_num⟩) (s₂.orderEmbOfFin hs₂c j) z₁ hm₁.2 hj
        rw [← hidx, heq]
        exact orderEmbOfFin_mem s₂ hs₂c j
    have hs_eq : s₁ = s₂ := Finset.eq_of_subset_of_card_le hpart_mem (by omega)
    exact hne hs_eq
  have hbiUnion_sub : T.biUnion crossOf ⊆ (X.powersetCard 3).filter (fun e ↦ col e = b) :=
    biUnion_subset.mpr hcross_sub
  calc
    d.choose 3 * m ^ 3 = T.card * m ^ 3 := by simp [T, card_powersetCard]
    _ = ∑ s ∈ T, (crossOf s).card := by rw [sum_congr rfl hcross_card, sum_const, smul_eq_mul]
    _ = (T.biUnion crossOf).card := (card_biUnion hcross_disj).symm
    _ ≤ ((X.powersetCard 3).filter (fun e ↦ col e = b)).card := card_le_card hbiUnion_sub

lemma density_gap_three {d m : ℕ} {α : ℝ}
    (hd : 6 ≤ d) (hm : 1 ≤ m) (hα : 12 < α * (d : ℝ)) :
    ((d * m).choose 3 - d.choose 3 * m ^ 3 : ℝ) < α * ((d * m).choose 3 : ℝ) := by
  have hchoose_dm : 6 * (d * m).choose 3 = d * m * (d * m - 1) * (d * m - 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (d * m) 3
    have hf : (3 : ℕ).factorial = 6 := by decide
    rw [hf] at h
    rw [← h]
    simp [Nat.descFactorial_succ, mul_assoc]
    ring
  have hchoose_d : 6 * d.choose 3 = d * (d - 1) * (d - 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose d 3
    have hf : (3 : ℕ).factorial = 6 := by decide
    rw [hf] at h
    rw [← h]
    simp [Nat.descFactorial_succ, mul_assoc]
    ring
  have hdm_ge6 : 6 ≤ d * m := by nlinarith
  have hdm_R : (6 : ℝ) * ((d * m).choose 3 : ℝ) =
      (d : ℝ) * (m : ℝ) * ((d : ℝ) * (m : ℝ) - 1) * ((d : ℝ) * (m : ℝ) - 2) := by
    have h : ((6 * (d * m).choose 3 : ℕ) : ℝ) =
        ((d * m * (d * m - 1) * (d * m - 2) : ℕ) : ℝ) := by exact_mod_cast hchoose_dm
    push_cast [Nat.cast_sub (show 1 ≤ d * m by omega), Nat.cast_sub (show 2 ≤ d * m by omega)] at h
    exact h
  have hd_R : (6 : ℝ) * (d.choose 3 : ℝ) = (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) := by
    have h : ((6 * d.choose 3 : ℕ) : ℝ) = ((d * (d - 1) * (d - 2) : ℕ) : ℝ) := by
      exact_mod_cast hchoose_d
    push_cast [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_sub (show 2 ≤ d by omega)] at h
    exact h
  have hd_ge6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdm_ge6R : (6 : ℝ) ≤ (d : ℝ) * (m : ℝ) := by nlinarith
  have hdm_upper : (6 : ℝ) * ((d * m).choose 3 : ℝ) ≤ (d : ℝ) ^ 3 * (m : ℝ) ^ 3 := by
    rw [hdm_R]
    have h1 : (d : ℝ) * (m : ℝ) - 1 ≤ (d : ℝ) * (m : ℝ) := by linarith
    have h2 : (d : ℝ) * (m : ℝ) - 2 ≤ (d : ℝ) * (m : ℝ) := by linarith
    have hpos1 : 0 ≤ (d : ℝ) * (m : ℝ) := by positivity
    have hpos2 : 0 ≤ (d : ℝ) * (m : ℝ) - 1 := by linarith
    have hpos3 : 0 ≤ (d : ℝ) * (m : ℝ) - 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos1, mul_le_mul_of_nonneg_left h2 (mul_nonneg hpos1 hpos2)]
  have hdm_lower : (d : ℝ) ^ 3 * (m : ℝ) ^ 3 / 4 ≤ (6 : ℝ) * ((d * m).choose 3 : ℝ) := by
    rw [hdm_R]
    have h1 : (d : ℝ) * (m : ℝ) / 2 ≤ (d : ℝ) * (m : ℝ) - 1 := by linarith
    have h2 : (d : ℝ) * (m : ℝ) / 2 ≤ (d : ℝ) * (m : ℝ) - 2 := by linarith
    have hpos : 0 ≤ (d : ℝ) * (m : ℝ) := by positivity
    have hmul : ((d : ℝ) * (m : ℝ) / 2) * ((d : ℝ) * (m : ℝ) / 2) ≤
        ((d : ℝ) * (m : ℝ) - 1) * ((d : ℝ) * (m : ℝ) - 2) :=
      mul_le_mul h1 h2 (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hmul hpos]
  have hdiff : (6 : ℝ) * (((d * m).choose 3 : ℝ) - (d.choose 3 : ℝ) * (m : ℝ) ^ 3) ≤
      3 * (d : ℝ) ^ 2 * (m : ℝ) ^ 3 := by
    have hsub : (6 : ℝ) * (d.choose 3 : ℝ) * (m : ℝ) ^ 3 =
        ((d : ℝ) ^ 3 - 3 * (d : ℝ) ^ 2 + 2 * (d : ℝ)) * (m : ℝ) ^ 3 := by
      rw [hd_R]; ring
    have hm3 : 0 ≤ (m : ℝ) ^ 3 := by positivity
    nlinarith [mul_nonneg (show 0 ≤ 2 * (d : ℝ) by positivity) hm3]
  have hgoal : (6 : ℝ) * (((d * m).choose 3 : ℝ) - (d.choose 3 : ℝ) * (m : ℝ) ^ 3) <
      (6 : ℝ) * (α * ((d * m).choose 3 : ℝ)) := by
    have hα_pos : 0 < α := by nlinarith
    have h1 : 3 * (d : ℝ) ^ 2 * (m : ℝ) ^ 3 < α * ((d : ℝ) ^ 3 * (m : ℝ) ^ 3 / 4) := by
      have hdm3_pos : 0 < (d : ℝ) ^ 2 * (m : ℝ) ^ 3 := by positivity
      have hlt : (3 : ℝ) < α * (d : ℝ) / 4 := by linarith
      nlinarith [mul_lt_mul_of_pos_right hlt hdm3_pos]
    have h2 : α * ((d : ℝ) ^ 3 * (m : ℝ) ^ 3 / 4) ≤ α * ((6 : ℝ) * ((d * m).choose 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdm_lower hα_pos.le
    linarith
  linarith

end CFS11

theorem OMA.solution : OMA.R_Erdos161_erdos_161_parts_ii_R1.H1 := by
  intro α hα0 _hα1
  let d : ℕ := max 6 (Nat.ceil (12 / α) + 1)
  have hd6 : 6 ≤ d := le_max_left _ _
  have hd3 : 3 ≤ d := by omega
  have hαd : 12 < α * (d : ℝ) := by
    have h1 : (Nat.ceil (12 / α) + 1 : ℕ) ≤ d := le_max_right _ _
    have h2 : 12 / α < (d : ℝ) := by
      have hceil : 12 / α ≤ (Nat.ceil (12 / α) : ℝ) := Nat.le_ceil (12 / α)
      have h1R : ((Nat.ceil (12 / α) : ℝ) + 1) ≤ (d : ℝ) := by exact_mod_cast h1
      linarith
    have := mul_lt_mul_of_pos_left h2 hα0
    rwa [mul_div_cancel₀ _ (ne_of_gt hα0)] at this
  let r := (2 * (d - 1)).choose (d - 1)
  let E := 2 + r * (4 ^ r + 2)
  let C := r * (E + 1) * (4 ^ r + 1) + E + 4 ^ r + 4
  have hC_pos : (0 : ℝ) < (C : ℝ) := by
    have : 0 < C := by dsimp [C]; positivity
    exact_mod_cast this
  let c : ℝ := (d : ℝ) / (2 * Real.sqrt (C : ℝ))
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, ?_⟩
  have hsqrt_top : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [
    Filter.eventually_ge_atTop 2,
    hsqrt_top.eventually (Filter.eventually_ge_atTop (2 * Real.sqrt (C : ℝ)))
  ] with n hn2 hsqrt_ge
  intro col
  set x : ℝ := Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (C : ℝ)
  have hx_ge2 : 2 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hC_pos)]
    exact hsqrt_ge
  set m : ℕ := Nat.floor x
  have hm_ge1 : 1 ≤ m := by
    have : (1 : ℕ) ≤ Nat.floor x := Nat.le_floor (by norm_num; linarith)
    exact this
  have hm_le_x : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hm_ge_half : x / 2 ≤ (m : ℝ) := by
    have hlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  have hlog2_lt1 : Real.log 2 < 1 := by
    have h2e : (2 : ℝ) < Real.exp 1 := by
      linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    calc
      Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  have hpow_le_n : 2 ^ (C * m ^ 2) ≤ n := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hCm2 : (C : ℝ) * (m : ℝ) ^ 2 ≤ Real.log (n : ℝ) := by
      have hm2 : (m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hm_le_x 2
      have hx2 : x ^ 2 = Real.log (n : ℝ) / (C : ℝ) := by
        dsimp [x]
        rw [div_pow, Real.sq_sqrt hlogn_nonneg, Real.sq_sqrt hC_pos.le]
      rw [hx2] at hm2
      have := mul_le_mul_of_nonneg_left hm2 hC_pos.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hC_pos)] at this
    have hR : ((2 ^ (C * m ^ 2) : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have h2eq : (2 : ℝ) ^ (C * m ^ 2) = Real.exp (((C * m ^ 2 : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [h2eq, ← Real.exp_log hn_pos]
      apply Real.exp_le_exp.mpr
      push_cast
      have hnonneg : 0 ≤ (C : ℝ) * (m : ℝ) ^ 2 := by positivity
      calc
        (C : ℝ) * (m : ℝ) ^ 2 * Real.log 2 ≤ (C : ℝ) * (m : ℝ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hlog2_lt1.le hnonneg
        _ = (C : ℝ) * (m : ℝ) ^ 2 := mul_one _
        _ ≤ Real.log (n : ℝ) := hCm2
    exact_mod_cast hR
  obtain ⟨b, P, hPcard, hPdisj, hPcol⟩ :=
    CFS11.exists_monochromatic_multipartite col d m hd3 hm_ge1 hpow_le_n
  obtain ⟨hXcard, hmono⟩ := CFS11.crossing_triples_le_mono col b P hPcard hPdisj hPcol
  let X := Finset.univ.biUnion P
  refine ⟨X, ?_, !b, ?_⟩
  · have hXcardR : (X.card : ℝ) = (d : ℝ) * (m : ℝ) := by exact_mod_cast hXcard
    rw [hXcardR]
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    calc
      c * Real.sqrt (Real.log (n : ℝ)) = (d : ℝ) * (x / 2) := by
        dsimp [c, x]; ring
      _ ≤ (d : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_left hm_ge_half hd_nonneg
  · have hpart :
        ((X.powersetCard 3).filter (fun e ↦ col e = b)).card +
        ((X.powersetCard 3).filter (fun e ↦ col e = !b)).card = X.card.choose 3 := by
      have hneg : (X.powersetCard 3).filter (fun e ↦ col e = !b) =
          (X.powersetCard 3).filter (fun e ↦ ¬ (col e = b)) := by
        ext e
        simp only [Finset.mem_filter]
        cases col e <;> cases b <;> simp
      rw [hneg]
      have hsum : ((X.powersetCard 3).filter (fun e ↦ col e = b)).card +
          ((X.powersetCard 3).filter (fun e ↦ ¬ (col e = b))).card = (X.powersetCard 3).card := by
        simpa using Finset.sum_filter_add_sum_filter_not (X.powersetCard 3) (fun e ↦ col e = b) (fun _ ↦ (1 : ℕ))
      rw [hsum, Finset.card_powersetCard]
    have hnotb_le :
        (((X.powersetCard 3).filter (fun e ↦ col e = !b)).card : ℝ) ≤
          ((d * m).choose 3 : ℝ) - (d.choose 3 : ℝ) * (m : ℝ) ^ 3 := by
      have hpartR :
          (((X.powersetCard 3).filter (fun e ↦ col e = b)).card : ℝ) +
          (((X.powersetCard 3).filter (fun e ↦ col e = !b)).card : ℝ) =
            ((d * m).choose 3 : ℝ) := by
        rw [← hXcard]
        exact_mod_cast hpart
      have hmonoR : (d.choose 3 : ℝ) * (m : ℝ) ^ 3 ≤
          (((X.powersetCard 3).filter (fun e ↦ col e = b)).card : ℝ) := by
        exact_mod_cast hmono
      linarith
    have hgap := CFS11.density_gap_three hd6 hm_ge1 hαd
    rw [hXcard]
    linarith
