import OMAStatements.S_oeis_a222001

-- Problem: A222001: Number of n x 3 arrays of permutations of 1..3 with downsteps nondecreasing and rows lex-nonincreasing.
-- Credit: @ceejcake
-- Proof: Lex-nonincreasing forces downsteps nonincreasing, so all rows have the same downstep count (0, 1, or 2):
-- 1 array with downsteps 2, 1 array with downsteps 0, and C(n+3, 3) weakly decreasing arrays in the 4 downstep-1 rows.

namespace ProofA222001

open OMA.S_oeis_a222001

-- Enumerate the 4 downstep-1 permutations of Fin 3 in strictly decreasing lex order
private def midRow : Fin 4 → (Fin 3 → Fin 3)
  | 0 => ![2, 0, 1]
  | 1 => ![1, 2, 0]
  | 2 => ![1, 0, 2]
  | 3 => ![0, 2, 1]

private def topRow : Fin 3 → Fin 3 := ![2, 1, 0]
private def botRow : Fin 3 → Fin 3 := ![0, 1, 2]

private lemma lexGE_imp_downsteps_ge :
    ∀ r s : Fin 3 → Fin 3, Function.Bijective r → Function.Bijective s →
      lexGE r s → downsteps s ≤ downsteps r := by
  intro r s hr hs h
  revert hr hs h
  unfold lexGE
  revert r s
  decide

private lemma downsteps_eq_two_iff :
    ∀ r : Fin 3 → Fin 3, Function.Bijective r → (downsteps r = 2 ↔ r = topRow) := by
  decide

private lemma downsteps_eq_zero_iff :
    ∀ r : Fin 3 → Fin 3, Function.Bijective r → (downsteps r = 0 ↔ r = botRow) := by
  decide

private lemma downsteps_le_two (r : Fin 3 → Fin 3) : downsteps r ≤ 2 := by
  unfold downsteps; split_ifs <;> omega

private lemma downsteps_eq_one_iff :
    ∀ r : Fin 3 → Fin 3, Function.Bijective r → (downsteps r = 1 ↔ ∃ k : Fin 4, r = midRow k) := by
  decide

private lemma midRow_inj : Function.Injective midRow := by
  decide

private lemma midRow_bij : ∀ k : Fin 4, Function.Bijective (midRow k) := by
  decide

private lemma midRow_downsteps : ∀ k : Fin 4, downsteps (midRow k) = 1 := by
  decide

private lemma midRow_lexGE_iff : ∀ j k : Fin 4, lexGE (midRow j) (midRow k) ↔ j ≤ k := by
  unfold lexGE; decide

private lemma topRow_bij : Function.Bijective topRow := by decide
private lemma botRow_bij : Function.Bijective botRow := by decide
private lemma topRow_lex : lexGE topRow topRow := by unfold lexGE; decide
private lemma botRow_lex : lexGE botRow botRow := by unfold lexGE; decide

private lemma topRow_valid (n : ℕ) : isValid n (fun _ => topRow) :=
  ⟨fun _ => topRow_bij, fun _ _ => le_rfl, fun _ _ => topRow_lex⟩

private lemma botRow_valid (n : ℕ) : isValid n (fun _ => botRow) :=
  ⟨fun _ => botRow_bij, fun _ _ => le_rfl, fun _ _ => botRow_lex⟩

section Counting
open scoped Classical

-- Weakly increasing functions Fin n → Fin m (with m = 4) have cardinality C(n + m - 1, m - 1)
private def monoFin (n m : ℕ) : Finset (Fin n → Fin m) :=
  Finset.univ.filter (fun f => ∀ (i : Fin n) (h : i.1 + 1 < n), f i ≤ f ⟨i.1 + 1, h⟩)

private lemma card_monoFin : ∀ m n : ℕ, (monoFin n (m + 1)).card = Nat.choose (n + m) m := by
  intro m
  induction m with
  | zero =>
    intro n
    simp only [Nat.add_zero, Nat.choose_zero_right]
    have h : monoFin n 1 = {fun _ => 0} := by
      ext f
      simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.eq_zero (f i)
      · rintro rfl _ _; exact le_rfl
    rw [h, Finset.card_singleton]
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      simp only [Nat.zero_add, Nat.choose_self]
      have h : monoFin 0 (m + 2) = {Fin.elim0} := by
        ext f
        simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _; funext i; exact Fin.elim0 i
        · rintro rfl i; exact Fin.elim0 i
      rw [h, Finset.card_singleton]
    | succ n ihn =>
      have hsplit : monoFin (n + 1) (m + 2) =
          (monoFin (n + 1) (m + 2)).filter (fun f => f (Fin.last n) = Fin.last (m + 1)) ∪
          (monoFin (n + 1) (m + 2)).filter (fun f => f (Fin.last n) ≠ Fin.last (m + 1)) := by
        ext f; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      have hdisj : Disjoint
          ((monoFin (n + 1) (m + 2)).filter (fun f => f (Fin.last n) = Fin.last (m + 1)))
          ((monoFin (n + 1) (m + 2)).filter (fun f => f (Fin.last n) ≠ Fin.last (m + 1))) := by
        rw [Finset.disjoint_left]; intro f h1 h2
        simp only [Finset.mem_filter] at h1 h2; exact h2.2 h1.2
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      have hc1 : ((monoFin (n + 1) (m + 2)).filter (fun f => f (Fin.last n) = Fin.last (m + 1))).card =
          (monoFin n (m + 2)).card := by
        refine Finset.card_bij (fun f _ i => f i.castSucc) ?_ ?_ ?_
        · intro f hf
          simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          intro i hi
          exact hf.1 i.castSucc (by simp only [Fin.val_castSucc]; omega)
        · intro f1 hf1 f2 hf2 h
          simp only [Finset.mem_filter] at hf1 hf2
          funext i
          by_cases hi : i.1 < n
          · exact congr_fun h ⟨i.1, hi⟩
          · have hlast : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast, hf1.2, hf2.2]
        · intro g hg
          simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and] at hg
          let f : Fin (n + 1) → Fin (m + 2) := fun i =>
            if h : i.1 < n then g ⟨i.1, h⟩ else Fin.last (m + 1)
          refine ⟨f, ?_, ?_⟩
          · simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun i hi => ?_, ?_⟩
            · dsimp only [f]
              by_cases h1 : i.1 + 1 < n
              · rw [dif_pos (by omega), dif_pos h1]; exact hg ⟨i.1, by omega⟩ h1
              · rw [dif_pos (by omega), dif_neg h1]; exact Fin.le_last _
            · dsimp only [f]; rw [dif_neg (by simp [Fin.last])]
          · funext i; dsimp only [f]; simp only [Fin.val_castSucc, i.2, ↓reduceDIte]
      have hc2 : ((monoFin (n + 1) (m + 2)).filter (fun f => f (Fin.last n) ≠ Fin.last (m + 1))).card =
          (monoFin (n + 1) (m + 1)).card := by
        have hmono_le : ∀ f ∈ monoFin (n + 1) (m + 2), ∀ i : Fin (n + 1), f i ≤ f (Fin.last n) := by
          intro f hf i
          simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          suffices ∀ k : ℕ, ∀ hk : i.1 + k < n + 1, f i ≤ f ⟨i.1 + k, hk⟩ by
            have h := this (n - i.1) (by omega)
            have heq : (⟨i.1 + (n - i.1), by omega⟩ : Fin (n + 1)) = Fin.last n :=
              Fin.ext (by simp only [Fin.val_last]; omega)
            rwa [heq] at h
          intro k
          induction k with
          | zero => intro _; exact le_rfl
          | succ k ihk =>
            intro hk
            exact le_trans (ihk (by omega)) (hf ⟨i.1 + k, by omega⟩ hk)
        refine Finset.card_bij
          (fun f hf i => ⟨(f i).1, by
            have hle := hmono_le f (Finset.mem_filter.mp hf).1 i
            have hne := (Finset.mem_filter.mp hf).2
            have hlt : (f (Fin.last n)).1 < m + 1 := by
              have := (f (Fin.last n)).2
              have : (f (Fin.last n)).1 ≠ m + 1 := fun h => hne (Fin.ext (by simp only [Fin.val_last]; exact h))
              omega
            exact Nat.lt_of_le_of_lt hle hlt⟩) ?_ ?_ ?_
        · intro f hf
          simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          intro i hi; exact hf.1 i hi
        · intro f1 _ f2 _ h
          funext i
          exact Fin.ext (Fin.mk.inj (congr_fun h i))
        · intro g hg
          simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and] at hg
          refine ⟨fun i => (g i).castSucc, ?_, ?_⟩
          · simp only [monoFin, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun i hi => ?_, ?_⟩
            · exact Fin.castSucc_le_castSucc_iff.mpr (hg i hi)
            · intro h
              have := congr_arg Fin.val h
              simp [Fin.last] at this
              omega
          · funext i; rfl
      rw [hc1, hc2, ihn, ihm (n + 1)]
      have hch : Nat.choose (n + 1 + (m + 1)) (m + 1) =
          Nat.choose (n + (m + 1)) (m + 1) + Nat.choose (n + 1 + m) m := by
        have e1 : n + 1 + (m + 1) = (n + m + 1) + 1 := by omega
        have e2 : n + (m + 1) = n + m + 1 := by omega
        have e3 : n + 1 + m = n + m + 1 := by omega
        rw [e1, e2, e3, Nat.choose_succ_succ, add_comm]
      exact hch.symm

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = 2 + (1 + n) * (2 + n) * (3 + n) / 6 := by
  intro n hn
  have ha : a n = (Finset.univ.filter (isValid n)).card := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ha]
  have hconst : ∀ A : Fin n → Fin 3 → Fin 3, isValid n A →
      ∀ i : Fin n, downsteps (A i) = downsteps (A ⟨0, by omega⟩) := by
    intro A hA i
    rcases hA with ⟨hbij, hup, hlex⟩
    have hstep : ∀ j : Fin n, ∀ hj : j.1 + 1 < n, downsteps (A ⟨j.1 + 1, hj⟩) = downsteps (A j) := by
      intro j hj
      have h1 := hup j hj
      have h2 := lexGE_imp_downsteps_ge _ _ (hbij j) (hbij ⟨j.1 + 1, hj⟩) (hlex j hj)
      omega
    rcases i with ⟨k, hk⟩
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hstep ⟨k, by omega⟩ hk, ih (by omega)]
  let S := Finset.univ.filter (isValid n)
  let S0 : Finset (Fin n → Fin 3 → Fin 3) := {fun _ => topRow, fun _ => botRow}
  let S1 : Finset (Fin n → Fin 3 → Fin 3) := (monoFin n 4).image (fun f i => midRow (f i))
  have hS : S = S0 ∪ S1 := by
    ext A
    simp only [S, S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, monoFin]
    constructor
    · intro hA
      have hc := hconst A hA
      have hd0 : downsteps (A ⟨0, by omega⟩) ≤ 2 := downsteps_le_two _
      have hcases : downsteps (A ⟨0, by omega⟩) = 2 ∨
          downsteps (A ⟨0, by omega⟩) = 0 ∨
          downsteps (A ⟨0, by omega⟩) = 1 := by omega
      rcases hcases with h2 | h0 | h1
      · left; left; funext i
        exact (downsteps_eq_two_iff (A i) (hA.1 i)).mp ((hc i).trans h2)
      · left; right; funext i
        exact (downsteps_eq_zero_iff (A i) (hA.1 i)).mp ((hc i).trans h0)
      · right
        have hex : ∀ i : Fin n, ∃ k : Fin 4, A i = midRow k := fun i =>
          (downsteps_eq_one_iff (A i) (hA.1 i)).mp ((hc i).trans h1)
        choose f hf using hex
        refine ⟨f, fun i hi => ?_, ?_⟩
        · have hl := hA.2.2 i hi
          rw [hf i, hf ⟨i.1 + 1, hi⟩] at hl
          exact (midRow_lexGE_iff _ _).mp hl
        · funext i; exact (hf i).symm
    · rintro ((rfl | rfl) | ⟨f, hf, rfl⟩)
      · exact topRow_valid n
      · exact botRow_valid n
      · refine ⟨fun i => midRow_bij (f i),
                fun i hi => by rw [midRow_downsteps, midRow_downsteps],
                fun i hi => (midRow_lexGE_iff _ _).mpr (hf i hi)⟩
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]; intro A hA0 hA1
    simp only [S0, S1, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hA0 hA1
    rcases hA1 with ⟨f, _, rfl⟩
    have h0 : downsteps (midRow (f ⟨0, by omega⟩)) = 1 := midRow_downsteps _
    rcases hA0 with h | h
    · have := congr_fun h ⟨0, by omega⟩
      rw [this] at h0
      exact absurd h0 (by decide)
    · have := congr_fun h ⟨0, by omega⟩
      rw [this] at h0
      exact absurd h0 (by decide)
  have hne : (fun _ : Fin n => topRow) ≠ (fun _ : Fin n => botRow) := by
    intro h
    have := congr_fun (congr_fun h ⟨0, by omega⟩) 0
    exact absurd this (by decide)
  have hcS0 : S0.card = 2 := Finset.card_pair hne
  have hcS1 : S1.card = (monoFin n 4).card := by
    refine Finset.card_image_of_injective _ ?_
    intro f1 f2 h
    funext i
    exact midRow_inj (congr_fun h i)
  change S.card = _
  rw [hS, Finset.card_union_of_disjoint hdisj, hcS0, hcS1, card_monoFin 3 n]
  have hch : Nat.choose (n + 3) 3 = (1 + n) * (2 + n) * (3 + n) / 6 := by
    have h6 : ∀ k : ℕ, 6 * Nat.choose (k + 3) 3 = (1 + k) * (2 + k) * (3 + k) := by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        have h2 : ∀ j : ℕ, 2 * Nat.choose (j + 2) 2 = (j + 1) * (j + 2) := by
          intro j; induction j with
          | zero => decide
          | succ j ihj =>
            rw [show j + 1 + 2 = (j + 2) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
            nlinarith
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, Nat.choose_succ_succ]
        have := h2 (k + 1)
        nlinarith
    have := h6 n
    omega
  rw [hch]

end Counting
end ProofA222001

theorem OMA.solution : type_of% @OMA.S_oeis_a222001.main :=
  ProofA222001.main
