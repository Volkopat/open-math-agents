import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! Cutting a marked rim at the ends of an interval gives a virtual closing edge.
A connected 2-factor on the interval supplies a matching covering its interior.
Rotating paths with the closing edge fixed changes the interval path while
preserving the rest of the Hamilton cycle. The fixed-edge rotation argument and
walk construction are adapted from open-math-agents PR #5313. -/
namespace OMA.SheehanIntervalComponent
open SimpleGraph Finset LovaszPlummerConjecture


private def rotIdx (n k j : ℕ) : ℕ :=
  if j ≤ k then j else n + k - j

private lemma rotIdx_lt {n k j : ℕ} (_hk : k + 2 < n) (hj : j < n) : rotIdx n k j < n := by
  unfold rotIdx
  split_ifs <;> omega

private lemma rotIdx_invol {n k j : ℕ} (_hk : k + 2 < n) (hj : j < n) :
    rotIdx n k (rotIdx n k j) = j := by
  unfold rotIdx
  split_ifs <;> omega

private lemma rotIdx_eq_iff {n k j₁ j₂ : ℕ} (hk : k + 2 < n) (h1 : j₁ < n) (h2 : j₂ < n) :
    rotIdx n k j₁ = rotIdx n k j₂ ↔ j₁ = j₂ := by
  constructor
  · intro h
    have := congrArg (rotIdx n k) h
    rwa [rotIdx_invol hk h1, rotIdx_invol hk h2] at this
  · rintro rfl; rfl

private def rotFin {n : ℕ} (P : Fin n → Fin n) (k : ℕ) (hk : k + 2 < n) : Fin n → Fin n :=
  fun j => P ⟨rotIdx n k j.val, rotIdx_lt hk j.isLt⟩

private lemma rotFin_invol {n : ℕ} (P : Fin n → Fin n) (k : ℕ) (hk : k + 2 < n) :
    rotFin (rotFin P k hk) k hk = P := by
  ext ⟨j, hj⟩
  simp only [rotFin, rotIdx_invol hk hj]

private lemma rotFin_inj {n : ℕ} {P : Fin n → Fin n} (hP : Function.Injective P)
    {k : ℕ} (hk : k + 2 < n) : Function.Injective (rotFin P k hk) := by
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ h
  have h1 := hP h
  simp only [Fin.mk.injEq, rotIdx_eq_iff hk hj₁ hj₂] at h1
  exact Fin.ext h1

private lemma walkOfChain_exists {V : Type*} (G : SimpleGraph V) (l : List V) (hl : l ≠ [])
    (hadj : ∀ i : ℕ, (hi : i + 1 < l.length) → G.Adj l[i] l[i + 1]) :
    ∃ p : G.Walk (l.head hl) (l.getLast hl),
      p.support = l ∧ p.length + 1 = l.length ∧
      ∀ e, e ∈ p.edges ↔ ∃ i : ℕ, ∃ (hi : i + 1 < l.length), e = s(l[i], l[i + 1]) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    cases t with
    | nil =>
      refine ⟨Walk.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | cons b t' =>
      have ht_ne : b :: t' ≠ [] := List.cons_ne_nil _ _
      have hadj_t : ∀ i : ℕ, (hi : i + 1 < (b :: t').length) →
          G.Adj (b :: t')[i] (b :: t')[i + 1] := by
        intro i hi
        have h1 := hadj (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa only [List.getElem_cons_succ] using h1
      obtain ⟨q, hq_sup, hq_len, hq_edges⟩ := ih ht_ne hadj_t
      have hab : G.Adj a ((b :: t').head ht_ne) := hadj 0 (by simp)
      refine ⟨(Walk.cons hab q).copy (List.head_cons (a := a) (l := b :: t') (h := hl)).symm
          (List.getLast_cons ht_ne).symm, ?_, ?_, ?_⟩
      · simp only [Walk.support_copy, Walk.support_cons, hq_sup]
      · rw [Walk.length_copy, Walk.length_cons, hq_len]
        rfl
      · intro e
        simp only [Walk.edges_copy, Walk.edges_cons, List.mem_cons, hq_edges]
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨0, by simp, rfl⟩
          · exact ⟨i + 1, by simp only [List.length_cons] at hi ⊢; omega, by simp⟩
        · rintro ⟨i, hi, rfl⟩
          cases i with
          | zero => left; rfl
          | succ i' =>
            right
            exact ⟨i', by simp only [List.length_cons] at hi ⊢; omega, by simp⟩

private lemma second_ordering (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : ∀ i : Fin n, G.Adj i (i + 1))
    (oddAway : ∀ z : Fin n, z ≠ 0 → z ≠ 1 → G.degree z % 2 = 1) :
    ∃ (p : Fin n → Fin n), Function.Injective p ∧
      p ⟨0, by omega⟩ = 0 ∧ p ⟨1, by omega⟩ = 1 ∧
      (∀ i : ℕ, (hi : i + 1 < n) → G.Adj (p ⟨i, by omega⟩) (p ⟨i + 1, hi⟩)) ∧
      G.Adj (p ⟨n - 1, by omega⟩) 0 ∧
      ∃ i : ℕ, ∃ (hi : i < n), p ⟨i, hi⟩ ≠ ⟨i, hi⟩ := by
  classical
  let IsGood (P : Fin n → Fin n) : Prop :=
    Function.Injective P ∧
    P ⟨0, by omega⟩ = 0 ∧
    P ⟨1, by omega⟩ = 1 ∧
    (∀ i : ℕ, (hi : i + 1 < n) → G.Adj (P ⟨i, by omega⟩) (P ⟨i + 1, hi⟩))
  let LVert := { P : Fin n → Fin n // IsGood P }
  let LAdj : LVert → LVert → Prop := fun P Q =>
    ∃ k : ℕ, ∃ hk : k + 2 < n, 1 ≤ k ∧
      G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) ∧
      Q.1 = rotFin P.1 k hk
  have hL_symm : ∀ P Q, LAdj P Q → LAdj Q P := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ ⟨k, hk, hk1, hadj, hQ_eq⟩
    dsimp only at hadj hQ_eq
    refine ⟨k, hk, hk1, ?_, ?_⟩
    · have hQ_n1 : Q ⟨n - 1, by omega⟩ = P ⟨k + 1, by omega⟩ := by
        rw [hQ_eq]
        dsimp only [rotFin]
        have hidx : (⟨rotIdx n k (n - 1), rotIdx_lt hk (by omega : n - 1 < n)⟩ : Fin n) =
            ⟨k + 1, by omega⟩ := by
          ext; simp only [rotIdx, show ¬ (n - 1 ≤ k) by omega, ↓reduceIte]; omega
        rw [hidx]
      have hQ_k : Q ⟨k, by omega⟩ = P ⟨k, by omega⟩ := by
        rw [hQ_eq]
        dsimp only [rotFin]
        have hidx : (⟨rotIdx n k k, rotIdx_lt hk (by omega : k < n)⟩ : Fin n) =
            ⟨k, by omega⟩ := by
          ext; simp only [rotIdx, le_refl, ↓reduceIte]
        rw [hidx]
      change G.Adj (Q ⟨n - 1, by omega⟩) (Q ⟨k, by omega⟩)
      rw [hQ_n1, hQ_k]
      exact (hP.2.2.2 k (by omega)).symm
    · exact (rotFin_invol P k hk).symm.trans (congrArg (fun f => rotFin f k hk) hQ_eq.symm)
  have hL_irrefl : ∀ P, ¬ LAdj P P := by
    rintro ⟨P, hP⟩ ⟨k, hk, _, _, hP_eq⟩
    dsimp only at hP_eq
    have hv := congrArg (fun f => f ⟨k + 1, by omega⟩) hP_eq
    have hidx : (⟨rotIdx n k (k + 1), rotIdx_lt hk (by omega : k + 1 < n)⟩ : Fin n) =
        ⟨n - 1, by omega⟩ := by
      ext; simp only [rotIdx, show ¬ (k + 1 ≤ k) by omega, ↓reduceIte]; omega
    have hrot : rotFin P k hk ⟨k + 1, by omega⟩ = P ⟨n - 1, by omega⟩ := by
      dsimp only [rotFin]; rw [hidx]
    rw [hrot] at hv
    have hval := congrArg Fin.val (hP.1 hv)
    simp at hval
    omega
  let L : SimpleGraph LVert := ⟨LAdj, ⟨fun _ _ => hL_symm _ _⟩, ⟨hL_irrefl⟩⟩
  have hrot_good : ∀ (P : LVert) (k : ℕ) (hk : k + 2 < n), 1 ≤ k →
      G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) →
      IsGood (rotFin P.1 k hk) := by
    intro ⟨P, hP⟩ k hk hk1 hadj
    dsimp only at hadj
    refine ⟨rotFin_inj hP.1 hk, ?_, ?_, ?_⟩
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k 0, rotIdx_lt hk (by omega : 0 < n)⟩ : Fin n) = ⟨0, by omega⟩ := by
        ext; simp [rotIdx]
      rw [hidx]; exact hP.2.1
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k 1, rotIdx_lt hk (by omega : 1 < n)⟩ : Fin n) = ⟨1, by omega⟩ := by
        ext; simp [rotIdx, hk1]
      rw [hidx]; exact hP.2.2.1
    · intro i hi
      dsimp only [rotFin]
      by_cases hik : i + 1 ≤ k
      · have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp [rotIdx, show i ≤ k by omega]
        have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp [rotIdx, hik]
        rw [hidx1, hidx2]
        exact hP.2.2.2 i hi
      · by_cases hik0 : i ≤ k
        · have hik_eq : i = k := by omega
          subst i
          have hidx1 : (⟨rotIdx n k k, rotIdx_lt hk (by omega : k < n)⟩ : Fin n) = ⟨k, by omega⟩ := by
            ext; simp [rotIdx]
          have hidx2 : (⟨rotIdx n k (k + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
            ext; simp only [rotIdx, show ¬ (k + 1 ≤ k) by omega, ↓reduceIte]; omega
          rw [hidx1, hidx2]
          exact hadj.symm
        · have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) =
              ⟨n + k - i, by omega⟩ := by
            ext; simp [rotIdx, hik0]
          have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) =
              ⟨n + k - (i + 1), by omega⟩ := by
            ext; simp [rotIdx, hik]
          rw [hidx1, hidx2]
          have hm_lt : n + k - (i + 1) + 1 < n := by omega
          have hchain := (hP.2.2.2 (n + k - (i + 1)) hm_lt).symm
          convert hchain using 2 <;> ext <;> dsimp <;> omega
  have hP0_good : IsGood (fun i : Fin n => i) := by
    refine ⟨Function.injective_id, rfl, by ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)], ?_⟩
    intro i hi
    have hnext : (⟨i, by omega⟩ : Fin n) + 1 = ⟨i + 1, hi⟩ := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hi]
    exact hnext ▸ hc ⟨i, by omega⟩
  let P0 : LVert := ⟨fun i : Fin n => i, hP0_good⟩
  have hdeg_eq : ∀ P : LVert, L.degree P =
      (Finset.univ.filter fun k : Fin n =>
        1 ≤ k.val ∧ k.val < n - 2 ∧ G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card := by
    intro P
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    have hmap :
        (Finset.univ.filter fun k : Fin n =>
          1 ≤ k.val ∧ k.val < n - 2 ∧ G.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card =
        (L.neighborSet P).toFinset.card := by
      have inj_lt : ∀ (a b : Fin n), 1 ≤ a.val → ∀ (hlt : a.val < b.val) (hb2 : b.val + 2 < n),
          rotFin P.1 a.val (lt_trans (Nat.add_lt_add_right hlt 2) hb2) ≠
            rotFin P.1 b.val hb2 := by
        intro a b _ hlt hb2 heq
        have ha2 : a.val + 2 < n := lt_trans (Nat.add_lt_add_right hlt 2) hb2
        have hv := congrArg (fun f => f ⟨a.val + 1, by omega⟩) heq
        have hidx1 : (⟨rotIdx n a.val (a.val + 1), rotIdx_lt ha2
            (by omega : a.val + 1 < n)⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          ext; simp only [rotIdx, show ¬ (a.val + 1 ≤ a.val) by omega, ↓reduceIte]; omega
        have hidx2 : (⟨rotIdx n b.val (a.val + 1), rotIdx_lt hb2
            (by omega : a.val + 1 < n)⟩ : Fin n) = ⟨a.val + 1, by omega⟩ := by
          ext; simp only [rotIdx, show a.val + 1 ≤ b.val by omega, ↓reduceIte]
        have h1 : rotFin P.1 a.val ha2 ⟨a.val + 1, by omega⟩ = P.1 ⟨n - 1, by omega⟩ := by
          dsimp only [rotFin]; rw [hidx1]
        have h2 : rotFin P.1 b.val hb2 ⟨a.val + 1, by omega⟩ = P.1 ⟨a.val + 1, by omega⟩ := by
          dsimp only [rotFin]; rw [hidx2]
        rw [h1, h2] at hv
        have hval := congrArg Fin.val (P.2.1 hv)
        simp at hval; omega
      refine Finset.card_bij
        (fun k hk =>
          have hkm := (mem_filter.mp hk).2
          have hk2 : k.val + 2 < n := by omega
          ⟨rotFin P.1 k.val hk2, hrot_good P k.val hk2 hkm.1 hkm.2.2⟩)
        ?_ ?_ ?_
      · intro k hk
        have hkm := (mem_filter.mp hk).2
        rw [Set.mem_toFinset, mem_neighborSet]
        exact ⟨k.val, by omega, hkm.1, hkm.2.2, rfl⟩
      · intro k₁ hk₁ k₂ hk₂ heq
        have hk1_mem := (mem_filter.mp hk₁).2
        have hk2_mem := (mem_filter.mp hk₂).2
        have hfun : rotFin P.1 k₁.val (by omega) = rotFin P.1 k₂.val (by omega) :=
          congrArg Subtype.val heq
        rcases lt_trichotomy k₁.val k₂.val with hlt | heqv | hgt
        · exact absurd hfun (inj_lt k₁ k₂ hk1_mem.1 hlt (by omega))
        · exact Fin.ext heqv
        · exact absurd hfun.symm (inj_lt k₂ k₁ hk2_mem.1 hgt (by omega))
      · rintro ⟨Q, hQ⟩ hmem
        rw [Set.mem_toFinset, mem_neighborSet] at hmem
        rcases hmem with ⟨k, hk, hk1, hadj, hQ_eq⟩
        refine ⟨⟨k, by omega⟩, mem_filter.mpr ⟨mem_univ _, hk1, by simp; omega, hadj⟩, ?_⟩
        exact Subtype.ext hQ_eq.symm
    exact hmap.symm.trans (by simp)
  have hdeg_char : ∀ P : LVert,
      (Odd (L.degree P) ↔ G.Adj (P.1 ⟨n - 1, by omega⟩) 0) := by
    intro P
    rw [hdeg_eq P]
    set z := P.1 ⟨n - 1, by omega⟩
    have hzOdd : G.degree z % 2 = 1 := by
      apply oddAway
      · intro h
        have heq := P.2.1 (h.trans P.2.2.1.symm)
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
      · intro h
        have heq := P.2.1 (h.trans P.2.2.2.1.symm)
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
    have hP_bij : Function.Bijective P.1 := (Fintype.bijective_iff_injective_and_card _).mpr ⟨P.2.1, rfl⟩
    let S_idx : Finset (Fin n) := (Finset.univ.filter fun i : Fin n => G.Adj z (P.1 i))
    have hS_card : S_idx.card = G.degree z := by
      have : S_idx.card = (G.neighborFinset z).card := by
        refine Finset.card_bij (fun i _ => P.1 i) ?_ ?_ ?_
        · intro i hi; rw [mem_neighborFinset]; exact (mem_filter.mp hi).2
        · intro i₁ _ i₂ _ h; exact P.2.1 h
        · intro w hw
          rw [mem_neighborFinset] at hw
          obtain ⟨i, rfl⟩ := hP_bij.2 w
          exact ⟨i, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
      exact this
    let nm2 : Fin n := ⟨n - 2, by omega⟩
    have hnm2_mem : nm2 ∈ S_idx := by
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hnm1_eq : (⟨n - 2 + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        ext; simp; omega
      have hadj_nm2 := (P.2.2.2.2 (n - 2) (by omega)).symm
      rwa [hnm1_eq] at hadj_nm2
    have hS_sub : ∀ i ∈ S_idx, i = nm2 ∨ i = ⟨0, by omega⟩ ∨ (1 ≤ i.val ∧ i.val < n - 2) := by
      intro i hi
      by_cases h1 : i = nm2
      · left; exact h1
      · by_cases h0 : i = ⟨0, by omega⟩
        · right; left; exact h0
        · right; right
          have hne_last : i ≠ ⟨n - 1, by omega⟩ := by
            intro heq
            exact G.loopless.irrefl z (by simpa [z, heq] using (mem_filter.mp hi).2)
          have hiv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
          have hiv2 : i.val ≠ n - 2 := fun h => h1 (Fin.ext h)
          have hiv1 : i.val ≠ n - 1 := fun h => hne_last (Fin.ext h)
          omega
    let K_idx : Finset (Fin n) := Finset.univ.filter fun i : Fin n =>
      1 ≤ i.val ∧ i.val < n - 2 ∧ G.Adj z (P.1 i)
    change Odd K_idx.card ↔ G.Adj z 0
    have hS_part : (S_idx.erase nm2).card = G.degree z - 1 := by
      rw [Finset.card_erase_of_mem hnm2_mem, hS_card]
    by_cases hadj0 : G.Adj z 0
    · have h0_mem : (⟨0, by omega⟩ : Fin n) ∈ S_idx.erase nm2 := by
        rw [mem_erase, mem_filter]
        refine ⟨?_, mem_univ _, by rw [P.2.2.1]; exact hadj0⟩
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only [nm2] at hval
        omega
      have hK_eq_erase : K_idx = (S_idx.erase nm2).erase ⟨0, by omega⟩ := by
        ext i
        simp only [K_idx, S_idx, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2, hiH⟩
          refine ⟨fun h => by have hv : i.val = 0 := congrArg Fin.val h; omega,
            fun h => by have hv : i.val = n - 2 := congrArg Fin.val h; omega, hiH⟩
        · rintro ⟨h0, h2, hiH⟩
          have hiS : i ∈ S_idx := mem_filter.mpr ⟨mem_univ _, hiH⟩
          rcases hS_sub i hiS with rfl | rfl | hk
          · exact absurd rfl h2
          · exact absurd rfl h0
          · exact ⟨hk.1, hk.2, hiH⟩
      rw [hK_eq_erase, Finset.card_erase_of_mem h0_mem, hS_part]
      have hpos := Finset.card_pos.mpr ⟨_, h0_mem⟩
      rw [hS_part] at hpos
      simp only [hadj0, iff_true, Nat.odd_iff]
      omega
    · have hK_eq_erase : K_idx = S_idx.erase nm2 := by
        ext i
        simp only [K_idx, S_idx, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨_, h2, hiH⟩
          exact ⟨fun h => by have hv : i.val = n - 2 := congrArg Fin.val h; omega, hiH⟩
        · rintro ⟨h2, hiH⟩
          have hiS : i ∈ S_idx := mem_filter.mpr ⟨mem_univ _, hiH⟩
          rcases hS_sub i hiS with rfl | rfl | hk
          · exact absurd rfl h2
          · exfalso
            apply hadj0
            rwa [P.2.2.1] at hiH
          · exact ⟨hk.1, hk.2, hiH⟩
      rw [hK_eq_erase, hS_part]
      simp only [hadj0, iff_false, Nat.odd_iff]
      omega
  have hP0_odd : Odd (L.degree P0) := by
    rw [hdeg_char P0]
    change G.Adj ⟨n - 1, by omega⟩ 0
    have wrap : (⟨n - 1, by omega⟩ : Fin n) + 1 = 0 := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
    exact wrap ▸ hc ⟨n - 1, by omega⟩
  obtain ⟨P1, hP1_ne, hP1_odd⟩ := L.exists_ne_odd_degree_of_exists_odd_degree P0 hP0_odd
  have hP1_closes : G.Adj (P1.1 ⟨n - 1, by omega⟩) 0 := (hdeg_char P1).mp hP1_odd
  have hP1_ne_fun : P1.1 ≠ fun i : Fin n => i := by
    intro heq
    exact hP1_ne (Subtype.ext heq)
  have hdiff : ∃ i : Fin n, P1.1 i ≠ i := by
    by_contra h
    push Not at h
    exact hP1_ne_fun (funext h)
  rcases hdiff with ⟨i_diff, hi_diff⟩
  exact ⟨P1.1, P1.2.1, P1.2.2.1, P1.2.2.2.1, P1.2.2.2.2, hP1_closes,
    i_diff.val, i_diff.isLt, hi_diff⟩

private theorem cycle_from_order {V : Type} [Fintype V] [DecidableEq V]
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph V)
    {v : V} (c : G.Walk v v) (e : Fin n ≃ V)
    (he_edges : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y) = s(e i, e (i+1)))
    (p : Fin n → Fin n) (hp_inj : Function.Injective p)
    (hp0 : p ⟨0, by omega⟩ = 0) (hp1 : p ⟨1, by omega⟩ = 1)
    (hp_adj : ∀ i : ℕ, (hi : i + 1 < n) →
      G.Adj (e (p ⟨i, by omega⟩)) (e (p ⟨i+1, hi⟩)))
    (hp_last : G.Adj (e (p ⟨n-1, by omega⟩)) (e 0))
    (i_diff : ℕ) (hi_diff_lt : i_diff < n)
    (hi_diff : p ⟨i_diff, hi_diff_lt⟩ ≠ ⟨i_diff, hi_diff_lt⟩) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  let l : List V := List.ofFn fun i : Fin n => e (p i)
  have hl_ne : l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [l] at this
    omega
  have hl_len : l.length = n := by simp [l]
  have hl_nodup : l.Nodup := by
    rw [List.nodup_ofFn]
    exact e.injective.comp hp_inj
  have hl_adj : ∀ i : ℕ, (hi : i + 1 < l.length) → G.Adj l[i] l[i + 1] := by
    intro i hi
    rw [hl_len] at hi
    simp only [l, List.getElem_ofFn]
    exact hp_adj i hi
  obtain ⟨q, hq_sup, hq_len, hq_edges⟩ := walkOfChain_exists G l hl_ne hl_adj
  have hhead : l.head hl_ne = e ⟨0, by omega⟩ := by
    rw [List.head_eq_getElem_zero]
    simp only [l, List.getElem_ofFn, hp0]
    rfl
  have hlast : l.getLast hl_ne = e (p ⟨n - 1, by omega⟩) := by
    rw [List.getLast_eq_getElem]
    simp only [l, hl_len, List.getElem_ofFn]
  have hadj_close : G.Adj (l.head hl_ne) (l.getLast hl_ne) := by
    rw [hhead, hlast]
    exact hp_last.symm
  let c' : G.Walk (l.head hl_ne) (l.head hl_ne) := Walk.cons hadj_close q.reverse
  have hc'_edge_not : s(l.head hl_ne, l.getLast hl_ne) ∉ q.reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse, hq_edges]
    rintro ⟨i, hi, heq⟩
    rw [hl_len] at hi
    simp only [l, List.getElem_ofFn] at heq
    rw [hhead, hlast] at heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hp1' : p ⟨0, by omega⟩ = p ⟨i, by omega⟩ := hp0.symm ▸ e.injective h1
      have hv1 := congrArg Fin.val (hp_inj hp1')
      simp only at hv1
      have hv2 := congrArg Fin.val (hp_inj (e.injective h2))
      simp only at hv2
      omega
    · have hp1' : p ⟨0, by omega⟩ = p ⟨i + 1, hi⟩ := hp0.symm ▸ e.injective h1
      have hv1 := congrArg Fin.val (hp_inj hp1')
      simp only at hv1
      have hv2 := congrArg Fin.val (hp_inj (e.injective h2))
      simp only at hv2
      omega
  have hc'_cyc : c'.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨?_, hc'_edge_not⟩
    rw [Walk.isPath_def, Walk.support_reverse, hq_sup]
    exact List.nodup_reverse.mpr hl_nodup
  have hc'_ham : ∀ w : V, w ∈ c'.support := by
    intro w
    simp only [c', Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse, hq_sup]
    right
    have hp_bij : Function.Bijective p := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hp_inj, rfl⟩
    obtain ⟨i, hi⟩ := (e.bijective.comp hp_bij).2 w
    rw [← hi]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  refine ⟨l.head hl_ne, c', ⟨hc'_cyc, hc'_ham⟩, ?_⟩
  intro hfin
  have hedge_sub : ∀ i : ℕ, (hi : i + 1 < n) →
      ∃ j : Fin n, s(e (p ⟨i, by omega⟩), e (p ⟨i + 1, hi⟩)) = s(e j, e (j + 1)) := by
    intro i hi
    have hmem : s(e (p ⟨i, by omega⟩), e (p ⟨i + 1, hi⟩)) ∈ c'.edges.toFinset := by
      rw [List.mem_toFinset]
      simp only [c', Walk.edges_cons, List.mem_cons, Walk.edges_reverse, List.mem_reverse, hq_edges]
      right
      refine ⟨i, by rw [hl_len]; exact hi, ?_⟩
      simp [l]
    rw [hfin, List.mem_toFinset] at hmem
    exact (he_edges _ _).mp hmem
  have hp_eq_id : ∀ k : ℕ, (hk : k < n) → p ⟨k, hk⟩ = ⟨k, hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk0
      · exact hp0
      · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk0)) with rfl | hk1
        · exact hp1.trans (by ext; simp [Nat.mod_eq_of_lt hk])
        · have hk_m1 : k - 1 < k := by omega
          have hk_m2 : k - 2 < k := by omega
          have hpm1 := ih (k - 1) hk_m1 (by omega)
          have hpm2 := ih (k - 2) hk_m2 (by omega)
          obtain ⟨j, hj⟩ := hedge_sub (k - 1) (by omega)
          rw [Sym2.eq_iff] at hj
          have hstep : p ⟨k, hk⟩ = p ⟨k - 1, by omega⟩ + 1 ∨
              p ⟨k - 1, by omega⟩ = p ⟨k, hk⟩ + 1 := by
            rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left
              have ha := e.injective h1
              have hb := e.injective h2
              have hc : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
              rw [hc] at hb
              rw [ha, hb]
            · right
              have ha := e.injective h1
              have hb := e.injective h2
              have hc : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
              rw [hc] at hb
              rw [ha, hb]
          rw [hpm1] at hstep
          rcases hstep with hplus | hminus
          · have h1val : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
            rw [hplus, Fin.ext_iff, Fin.val_add, h1val]
            change (k - 1 + 1) % n = k
            rw [Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.mod_eq_of_lt hk]
          · exfalso
            have hkp : p ⟨k, hk⟩ = ⟨k - 2, by omega⟩ := by
              have h1 := congrArg (· - 1) hminus
              have h2 : p ⟨k, hk⟩ = (⟨k - 1, by omega⟩ : Fin n) - 1 := by
                simpa using h1.symm
              rw [h2]
              ext
              have hv : ((⟨k - 1, by omega⟩ : Fin n) - 1).val = k - 2 := by
                rw [Fin.val_sub_one_of_ne_zero (by intro h; have := congrArg Fin.val h; simp at this; omega)]
                simp; omega
              exact hv
            have heq := hp_inj (hkp.trans hpm2.symm)
            have hval := congrArg Fin.val heq
            simp at hval; omega
  exact hi_diff (hp_eq_id i_diff hi_diff_lt)

/-- The cyclic order of the retained vertices after inserting k vertices
between positions 0 and 1. -/
def slot {m : ℕ} (k : ℕ) (i : Fin m) : Fin (m + k) :=
  ⟨if i.val = 0 then 0 else k+i.val, by have := i.isLt; split <;> omega⟩

private theorem slot_injective {m : ℕ} (k : ℕ) : Function.Injective (@slot m k) := by
  intro i j h
  have hval := congrArg Fin.val h
  simp only [slot] at hval
  apply Fin.ext
  split at hval <;> split at hval <;> omega

/-- Parity on the compressed interval produces a second Hamiltonian cycle in
the full graph, preserving the complementary arc. The odd-degree condition is
required only at interior vertices of the interval. -/
theorem second_cycle_of_interval_order {V : Type} [Fintype V] [DecidableEq V]
    (m k : ℕ) [NeZero m] [NeZero (m+k)] (hm : 3 ≤ m)
    (G : SimpleGraph V) {v : V} (c : G.Walk v v) (e : Fin (m+k) ≃ V)
    (red : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin (m+k), s(x,y) = s(e i, e (i+1)))
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (p : Fin m → Fin m) (pinj : Function.Injective p)
    (pzero : p ⟨0,by omega⟩ = 0) (pone : p ⟨1,by omega⟩ = 1)
    (pedges : ∀ i : ℕ, (hi : i + 1 < m) → H.Adj (p ⟨i,by omega⟩) (p ⟨i+1,hi⟩))
    (pclose : H.Adj (p ⟨m-1,by omega⟩) 0)
    (j : ℕ) (hj : j < m) (pdiff : p ⟨j,hj⟩ ≠ ⟨j,hj⟩)
    (liftEdge : ∀ a b : Fin m, H.Adj a b → s(a,b) ≠ s((0 : Fin m),1) →
      G.Adj (e (slot k a)) (e (slot k b))) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  have hm1 : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  have hn1 : (1 : Fin (m+k)).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m+k)
  have p0 : p 0 = 0 := pzero
  have p1 : p 1 = 1 := by
    convert pone using 2
    exact Fin.ext hm1
  have pnz (a : Fin m) (ha : 0 < a.val) : 0 < (p a).val := by
    by_contra! h
    have hp : p a = p 0 := by rw [p0]; exact Fin.ext (by simpa using h)
    have hy := congrArg Fin.val (pinj hp)
    simp at hy
    omega
  let q (x : Fin (m+k)) : Fin (m+k) :=
    if hx : x.val ≤ k then x else
      ⟨k + (p ⟨x.val-k, by have := x.isLt; omega⟩).val, by
        have := (p ⟨x.val-k, by have := x.isLt; omega⟩).isLt; omega⟩
  have qprefix (x : Fin (m+k)) (hx : x.val ≤ k+1) : q x = x := by
    by_cases low : x.val ≤ k
    · simp [q, low]
    · have hxk : x.val-k = 1 := by omega
      have hidx : (⟨x.val-k, by have := x.isLt; omega⟩ : Fin m) = 1 :=
        Fin.ext (hxk.trans hm1.symm)
      apply Fin.ext
      simp only [q, dif_neg low, hidx, p1, hm1]
      omega
  have qslot (a : Fin m) : q (slot k a) = slot k (p a) := by
    by_cases ha : a.val = 0
    · have az : a = 0 := Fin.ext ha
      rw [az, p0]
      apply qprefix
      simp [slot]
    · have hpa := pnz a (by omega)
      have hslot : (slot k a).val = k+a.val := by simp [slot, ha]
      have hhigh : ¬ (slot k a).val ≤ k := by omega
      have hh : (⟨(slot k a).val-k, by rw [hslot]; simp⟩ : Fin m) = a := by
        ext
        simp [hslot]
      apply Fin.ext
      simp only [q, dif_neg hhigh, hh]
      simp [slot, Nat.ne_of_gt hpa]
  have qinj : Function.Injective q := by
    intro x y hxy
    have hval := congrArg Fin.val hxy
    by_cases hx : x.val ≤ k <;> by_cases hy : y.val ≤ k
    · simpa [q, hx, hy] using hxy
    · have hp := pnz ⟨y.val-k, by have := y.isLt; omega⟩ (by dsimp; omega)
      simp [q, hx, hy] at hval
      omega
    · have hp := pnz ⟨x.val-k, by have := x.isLt; omega⟩ (by dsimp; omega)
      simp [q, hx, hy] at hval
      omega
    · simp only [q, dif_neg hx, dif_neg hy, Nat.add_left_cancel_iff] at hval
      have heq := congrArg Fin.val (pinj (Fin.ext hval))
      apply Fin.ext
      dsimp at heq
      omega
  have qadj (i : ℕ) (hi : i+1 < m+k) :
      G.Adj (e (q ⟨i, by omega⟩)) (e (q ⟨i+1, hi⟩)) := by
    by_cases early : i ≤ k
    · rw [qprefix _ (by dsimp; omega), qprefix _ (by dsimp; omega)]
      have hsucc : (⟨i, by omega⟩ : Fin (m+k)) + 1 = ⟨i+1, hi⟩ := by
        ext
        simp only [Fin.val_add, hn1, Nat.mod_eq_of_lt hi]
      change s(e ⟨i, by omega⟩, e ⟨i+1, hi⟩) ∈ G.edgeSet
      apply c.edges_subset_edgeSet
      exact (red _ _).mpr ⟨⟨i, by omega⟩, by rw [hsucc]⟩
    · let a : Fin m := ⟨i-k, by omega⟩
      let b : Fin m := ⟨(i-k)+1, by omega⟩
      have ha : 0 < a.val := by dsimp [a]; omega
      have hb : 0 < b.val := by dsimp [b]; omega
      have sa : slot k a = ⟨i, by omega⟩ := by
        apply Fin.ext
        simp only [slot, if_neg (Nat.ne_of_gt ha), a]
        omega
      have sb : slot k b = ⟨i+1, hi⟩ := by
        apply Fin.ext
        simp only [slot, if_neg (Nat.ne_of_gt hb), b]
        omega
      rw [← sa, ← sb, qslot, qslot]
      apply liftEdge _ _ (pedges (i-k) (by omega))
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h0,_⟩ | ⟨_,h0⟩
      · have := pnz a ha; rw [h0] at this; simp at this
      · have := pnz b hb; rw [h0] at this; simp at this
  let last : Fin m := ⟨m-1, by omega⟩
  have lastval : 0 < last.val := by dsimp [last]; omega
  have slast : slot k last = ⟨m+k-1, by omega⟩ := by
    apply Fin.ext
    simp only [slot, if_neg (Nat.ne_of_gt lastval), last]
    omega
  have szero : slot k (0 : Fin m) = 0 := by ext; simp [slot]
  have qclose : G.Adj (e (q ⟨m+k-1, by omega⟩)) (e 0) := by
    rw [← slast, qslot, ← szero]
    apply liftEdge _ _ pclose
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, bad⟩ | ⟨bad,_⟩
    · have hv := congrArg Fin.val bad
      simp at hv
      omega
    · have he := pinj (bad.trans p1.symm)
      have hv := congrArg Fin.val he
      change m-1 = (1 : Fin m).val at hv
      omega
  let a : Fin m := ⟨j,hj⟩
  have qdiff : q (slot k a) ≠ slot k a := by
    rw [qslot]
    exact fun h => pdiff (slot_injective k h)
  exact cycle_from_order (by omega) G c e red q qinj
    (by rw [qprefix _ (by dsimp; omega)]; rfl)
    (by rw [qprefix _ (by dsimp; omega)]; exact Fin.ext hn1.symm)
    qadj qclose (slot k a).val (slot k a).isLt qdiff

theorem second_cycle_of_interval_parity {V : Type} [Fintype V] [DecidableEq V]
    (m k : ℕ) [NeZero m] [NeZero (m+k)] (hm : 3 ≤ m)
    (G : SimpleGraph V) {v : V} (c : G.Walk v v) (e : Fin (m+k) ≃ V)
    (red : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin (m+k), s(x,y) = s(e i, e (i+1)))
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (hcycle : ∀ i : Fin m, H.Adj i (i+1))
    (odd : ∀ i : Fin m, i ≠ 0 → i ≠ 1 → H.degree i % 2 = 1)
    (liftEdge : ∀ a b : Fin m, H.Adj a b → s(a,b) ≠ s((0 : Fin m),1) →
      G.Adj (e (slot k a)) (e (slot k b))) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  obtain ⟨p, pinj, pzero, pone, pedges, pclose, j, hj, pdiff⟩ :=
    second_ordering m hm H hcycle odd
  exact second_cycle_of_interval_order m k hm G c e red H p pinj pzero pone pedges pclose j hj pdiff liftEdge

private theorem rim_iff {m : ℕ} [NeZero m] (hm : 3 ≤ m) (a b : Fin m) :
    (cycleGraph m).Adj a b ↔ a = b+1 ∨ b = a+1 := by
  have hone : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  calc
    _ ↔ a-b = 1 ∨ b-a = 1 := by
      rw [cycleGraph_adj']
      simp only [Fin.ext_iff, hone]
    _ ↔ _ := by rw [sub_eq_iff_eq_add', sub_eq_iff_eq_add']

private theorem slot_succ {m : ℕ} [NeZero m] (hm : 3 ≤ m) (k : ℕ) [NeZero (m+k)]
    (i : Fin m) (hi : i ≠ 0) : slot k (i+1) = slot k i + 1 := by
  have im : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  have it : (1 : Fin (m+k)).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m+k)
  have hpos : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have hv : (slot k i).val = k+i.val := by simp [slot, hpos]
  apply Fin.ext
  rw [Fin.val_add, hv, it]
  by_cases last : i.val + 1 = m
  · have wrap : (i+1).val = 0 := by simp only [Fin.val_add, im, last, Nat.mod_self]
    have htotal : k+i.val+1 = m+k := by omega
    simp [slot, wrap, htotal]
  · have small : i.val+1 < m := by have := i.isLt; omega
    have jval : (i+1).val = i.val+1 := by rw [Fin.val_add, im, Nat.mod_eq_of_lt small]
    simp only [slot, jval, Nat.add_one_ne_zero, if_false, Nat.add_assoc]
    exact (Nat.mod_eq_of_lt (by omega : k+(i.val+1) < m+k)).symm

private theorem rim_degree {m : ℕ} (hm : 3 ≤ m) (i : Fin m) : (cycleGraph m).degree i = 2 := by
  match m with
  | 0 | 1 | 2 => omega
  | t+3 => exact cycleGraph_degree_three_le

/-- A matching of chords contained in a segment and covering all its interior
vertices supplies an alternative Hamiltonian cycle. The two terminals may be
matched or unmatched. The complement of the segment can have any length k. -/
theorem second_cycle_of_interval_matching {V : Type} [Fintype V] [DecidableEq V]
    (m k : ℕ) [NeZero m] [NeZero (m+k)] (hm : 3 ≤ m)
    (G : SimpleGraph V) {v : V} (c : G.Walk v v) (e : Fin (m+k) ≃ V)
    (red : ∀ x y : V, s(x,y) ∈ c.edges ↔ ∃ i : Fin (m+k), s(x,y) = s(e i, e (i+1)))
    (M : SimpleGraph (Fin m)) [DecidableRel M.Adj] (disj : Disjoint (cycleGraph m) M)
    (covers : ∀ i : Fin m, i ≠ 0 → i ≠ 1 → M.degree i = 1)
    (chord : ∀ a b : Fin m, M.Adj a b → G.Adj (e (slot k a)) (e (slot k b))) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset := by
  classical
  let H := cycleGraph m ⊔ M
  have cyc (i : Fin m) : H.Adj i (i+1) := Or.inl ((rim_iff hm _ _).mpr (Or.inr rfl))
  have odd (i : Fin m) (hz : i ≠ 0) (ho : i ≠ 1) : H.degree i % 2 = 1 := by
    change (cycleGraph m ⊔ M).degree i % 2 = 1
    rw [← card_neighborFinset_eq_degree, neighborFinset_sup_of_disjoint i disj,
      Finset.card_disjUnion, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree,
      rim_degree hm, covers i hz ho]
  apply second_cycle_of_interval_parity m k hm G c e red H cyc odd
  intro a b ab realEdge
  have forward (i : Fin m) (ine : i ≠ 0) : G.Adj (e (slot k i)) (e (slot k (i+1))) := by
    change s(e (slot k i), e (slot k (i+1))) ∈ G.edgeSet
    apply c.edges_subset_edgeSet
    exact (red _ _).mpr ⟨slot k i, by rw [slot_succ hm k i ine]⟩
  rcases ab with rim | inM
  · rcases (rim_iff hm _ _).mp rim with rfl | rfl
    · apply (forward b ?_).symm
      rintro rfl
      apply realEdge
      simp
    · apply forward a
      rintro rfl
      apply realEdge
      simp
  · exact chord a b inM

private def PartialMatching {V : Type} (M : SimpleGraph V) : Prop :=
  ∀ x y z, M.Adj x y → M.Adj x z → y = z

private lemma single_partial {V : Type} (a b : V) : PartialMatching (edge a b) := by
  intro x y z u v
  simp only [edge_adj] at u v
  grind

private lemma merged_partial {V : Type} {M N : SimpleGraph V}
    (left : PartialMatching M) (right : PartialMatching N)
    (disj : ∀ x y z, M.Adj x y → N.Adj x z → False) : PartialMatching (M ⊔ N) := by
  rintro x y z (h | h) (k | k)
  · exact left _ _ _ h k
  · exact (disj _ _ _ h k).elim
  · exact (disj _ _ _ k h).elim
  · exact right _ _ _ h k

private theorem matching_path {V : Type} {H : SimpleGraph V} {u v : V}
    (p : H.Walk u v) (hp : p.IsPath) :
    ∃ M : SimpleGraph V, M ≤ H ∧ PartialMatching M ∧
      (∀ x y, M.Adj x y → x ∈ p.support) ∧
      ∀ x ∈ p.support, x ≠ v → ∃ y, M.Adj x y := by
  classical
  cases p with
  | nil =>
    refine ⟨⊥,bot_le,?_,?_,?_⟩
    · intro x y z h; exact h.elim
    · intro x y h; exact h.elim
    · intro x hx ne; exact (ne (by simpa using hx)).elim
  | @cons _ b _ ab q =>
    have eab : (edge u b).Adj u b := by simp [edge_adj,ab.ne]
    have under : edge u b ≤ H := by rw [edge_le_iff]; exact Or.inr ab
    have ends {x y : V} (h : (edge u b).Adj x y) : x=u ∨ x=b := by
      simp only [edge_adj] at h
      grind
    cases q with
    | nil =>
      refine ⟨edge u v,under,single_partial _ _,?_,?_⟩
      · intro x y h; simpa using ends h
      · intro x hx ne
        simp at hx
        rcases hx with rfl | rfl
        · exact ⟨_,eab⟩
        · exact (ne rfl).elim
    | @cons _ d _ bd r =>
      have nd := hp.support_nodup
      simp only [Walk.support_cons,List.nodup_cons] at nd
      have disja : u ∉ r.support := fun h => nd.1 (List.mem_cons_of_mem _ h)
      have disjb : b ∉ r.support := nd.2.1
      obtain ⟨M,sub,ma,supp,covers⟩ := matching_path r ((Walk.isPath_def _).mpr nd.2.2)
      have apart (x y z : V) (h : (edge u b).Adj x y) (k : M.Adj x z) : False := by
        have mem := supp x z k
        rcases ends h with rfl | rfl
        · exact disja mem
        · exact disjb mem
      refine ⟨edge u b ⊔ M,sup_le under sub,merged_partial (single_partial _ _) ma apart,?_,?_⟩
      · rintro x y (h | h)
        · rcases ends h with rfl | rfl <;> simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (supp _ _ h))
      · intro x hx ne
        simp only [Walk.support_cons,List.mem_cons] at hx
        rcases hx with rfl | rfl | hr
        · exact ⟨_,Or.inl eab⟩
        · exact ⟨_,Or.inl eab.symm⟩
        · obtain ⟨y,hy⟩ := covers _ hr ne
          exact ⟨y,Or.inr hy⟩
termination_by p.length
decreasing_by simp_all [Walk.length_cons]

private theorem component_matching {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (two : ∀ x, F.degree x = 2) (a : V) :
    ∃ M : SimpleGraph V, M ≤ F ∧ PartialMatching M ∧
      (∀ x y, M.Adj x y → F.connectedComponentMk x = F.connectedComponentMk a) ∧
      ∀ x, F.connectedComponentMk x = F.connectedComponentMk a → x ≠ a → ∃ y, M.Adj x y := by
  classical
  have cycles : F.IsCycles := by
    intro u _
    rw [Set.ncard_eq_toFinset_card']
    exact (F.card_neighborFinset_eq_degree u).trans (two u)
  have atA : a ∈ (F.connectedComponentMk a).supp := by
    rw [ConnectedComponent.mem_supp_iff]
  have neighbors : (F.neighborSet a).Nonempty := (SimpleGraph.degree_pos_iff_nonempty (G := F) (v := a)).mp (by rw [two]; decide)
  obtain ⟨p,hp,verts⟩ := cycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp atA neighbors
  have cover (x : V) : x ∈ p.tail.support ↔ F.connectedComponentMk x = F.connectedComponentMk a := by
    rw [← ConnectedComponent.mem_supp_iff,← verts,p.mem_verts_toSubgraph]
    have eq : a :: p.tail.support = p.support := by
      rw [p.support_tail_of_not_nil hp.not_nil]
      exact p.cons_tail_support
    rw [← eq]
    constructor
    · exact List.mem_cons_of_mem _
    · intro hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ p.tail.end_mem_support
      · exact hx
  obtain ⟨M,sub,matching,support,all⟩ := matching_path p.tail hp.isPath_tail
  exact ⟨M,sub,matching,fun x y h => (cover x).mp (support x y h),
    fun x hx ne => all x ((cover x).mpr hx) ne⟩

private theorem degree_one {V : Type} [Fintype V] [DecidableEq V] (M : SimpleGraph V)
    [DecidableRel M.Adj] (matching : PartialMatching M) {x y : V} (h : M.Adj x y) :
    M.degree x = 1 := degree_eq_one_iff_existsUnique_adj.mpr ⟨y,h,fun z hz => matching x z y hz h⟩

private lemma rim_degree_ambient {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} {c : G.Walk v v} (hc : IsHamiltonianCycle G c) (x : V) :
    letI := Classical.decRel c.toSubgraph.spanningCoe.Adj
    c.toSubgraph.spanningCoe.degree x = 2 := by
  classical
  let R := c.toSubgraph.spanningCoe
  have card : (R.neighborSet x).ncard = R.degree x := by
    rw [Set.ncard_eq_toFinset_card']
    exact R.card_neighborFinset_eq_degree x
  exact card.symm.trans (hc.1.ncard_neighborSet_toSubgraph_eq_two (hc.2 x))

variable {V : Type} [Fintype V] [DecidableEq V]

open scoped Classical in
theorem unused_cycle_degree (G : SimpleGraph V) [DecidableRel G.Adj] (four : ∀ z,G.degree z=4)
    {v : V} (c : G.Walk v v) (hc : IsHamiltonianCycle G c) (z : V) :
    (G \ c.toSubgraph.spanningCoe).degree z=2 := by
  classical
  let R := c.toSubgraph.spanningCoe
  have val : (G \ R).degree z=2 := by
    have sub : R.neighborFinset z ⊆ G.neighborFinset z := by
      intro i hi
      exact (G.mem_neighborFinset _ _).mpr (c.toSubgraph.spanningCoe_le ((R.mem_neighborFinset _ _).mp hi))
    rw [←card_neighborFinset_eq_degree,neighborFinset_sdiff,card_sdiff_of_subset sub,
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,four]
    have degree : R.degree z=2 := rim_degree_ambient hc z
    rw [degree]
  refine Eq.trans ?_ val
  simp only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
  rfl

theorem segment_of_connected_factor (m k : ℕ) [NeZero m] [NeZero (m+k)] (hm : 3 ≤ m)
    (G : SimpleGraph V) {v : V} (c : G.Walk v v) (e : Fin (m+k) ≃ V)
    (red : ∀ x y : V,s(x,y)∈c.edges ↔ ∃ i : Fin (m+k),s(x,y)=s(e i,e (i+1)))
    (Q : SimpleGraph (Fin m)) [DecidableRel Q.Adj] (two : ∀ z,Q.degree z=2) (connected : Q.Preconnected)
    (overlap : ∀ x y,Q.Adj x y → (cycleGraph m).Adj x y → (edge (0 : Fin m) 1).Adj x y)
    (chord : ∀ x y,Q.Adj x y → G.Adj (e (slot k x)) (e (slot k y))) :
    ∃ w,∃ d : G.Walk w w,IsHamiltonianCycle G d ∧ d.edges.toFinset≠c.edges.toFinset := by
  classical
  obtain ⟨J,part,matching,_,covered⟩ := component_matching Q two 0
  let M := J\edge 0 1
  have off : Disjoint (cycleGraph m) M := by
    rw [←disjoint_edgeSet,Set.disjoint_left,Sym2.forall]
    intro x y rim unused
    exact unused.2 (overlap x y (part unused.1) rim)
  apply second_cycle_of_interval_matching m k hm G c e red M off _ (fun _ _ xy => chord _ _ (part xy.1))
  intro x x0 x1
  have same : M.neighborFinset x=J.neighborFinset x := by
    ext y
    simp only [mem_neighborFinset]
    refine ⟨And.left,fun g => ⟨g,?_⟩⟩
    intro cap
    rcases (edge_adj ..).mp cap |>.1 with h|h
    · exact x0 h.1
    · exact x1 h.1
  obtain ⟨y,adj⟩ := covered x (ConnectedComponent.sound (connected x 0)) x0
  rw [←card_neighborFinset_eq_degree,same,card_neighborFinset_eq_degree]
  exact degree_one J matching adj

theorem component_sector (m k : ℕ) [NeZero m] [NeZero (m+k)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (four : ∀ x,G.degree x=4)
    {v : V} (c : G.Walk v v) (hc : IsHamiltonianCycle G c) (e : Fin (m+k) ≃ V)
    (red : ∀ x y : V,s(x,y)∈c.edges ↔ ∃ i : Fin (m+k),s(x,y)=s(e i,e (i+1)))
    (q : (G\c.toSubgraph.spanningCoe).ConnectedComponent)
    (image : ∀ x : V,x∈q.supp ↔ ∃ i : Fin m,e (slot k i)=x) :
    ∃ w,∃ d : G.Walk w w,IsHamiltonianCycle G d ∧ d.edges.toFinset≠c.edges.toFinset := by
  classical
  let F := G\c.toSubgraph.spanningCoe
  let emb : Fin m ↪ V := ⟨fun i => e (slot k i),e.injective.comp (slot_injective k)⟩
  let Q := F.comap emb
  have incl (i : Fin m) : emb i∈q.supp := (image _).mpr ⟨i,rfl⟩
  let toComponent (i : Fin m) : q.supp := ⟨emb i,incl i⟩
  have bij : Function.Bijective toComponent := by
    refine ⟨fun i j eq => emb.injective (congrArg Subtype.val eq),?_⟩
    rintro ⟨z,hz⟩
    obtain ⟨i,hi⟩ := (image z).mp hz
    exact ⟨i,Subtype.ext hi⟩
  let iso : Q ≃g q.toSimpleGraph := ⟨Equiv.ofBijective toComponent bij,Iff.rfl⟩
  have connected : Q.Preconnected := iso.preconnected_iff.mpr q.connected_toSimpleGraph.preconnected
  have two (i : Fin m) : Q.degree i=2 := by
    have neighbors : (Q.neighborFinset i).map emb=F.neighborFinset (emb i) := by
      ext z
      simp only [mem_map,mem_neighborFinset]
      constructor
      · rintro ⟨j,adj,rfl⟩
        exact adj
      · intro adj
        obtain ⟨j,hj⟩ := (image z).mp (q.mem_supp_of_adj_mem_supp (incl i) adj)
        refine ⟨j,?_,hj⟩
        change F.Adj (emb i) (e (slot k j))
        rw [hj]
        exact adj
    have num := congrArg Finset.card neighbors
    rw [card_map,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at num
    exact num.trans (unused_cycle_degree G four c hc (emb i))
  have hm : 3 ≤ m := by
    have lt := Q.degree_lt_card_verts 0
    rw [two,Fintype.card_fin] at lt
    omega
  have start (i : Fin m) (adj : Q.Adj i (i+1)) : i=0 := by
    by_contra other
    have equality := slot_succ hm k i other
    have on : s(e (slot k i),e (slot k (i+1)))∈c.edges := (red ..).mpr ⟨slot k i,by rw [equality]⟩
    exact adj.2 (Walk.adj_toSubgraph_iff_mem_edges.mpr on)
  apply segment_of_connected_factor m k hm G c e red Q two connected _ (fun _ _ xy => xy.1)
  intro a b chord rim
  rcases (rim_iff hm a b).mp rim with rfl|rfl
  · have bz := start b chord.symm
    exact (edge_adj ..).mpr ⟨Or.inr ⟨by simp [bz],bz⟩,chord.ne⟩
  · have az := start a chord
    exact (edge_adj ..).mpr ⟨Or.inl ⟨az,by simp [az]⟩,chord.ne⟩

private theorem cast_succ {p n : ℕ} [NeZero p] [NeZero n] (eq : p=n) (i : Fin p) :
    finCongr eq (i+1)=finCongr eq i+1 := by subst n; rfl

theorem linear_sector {n : ℕ} [NeZero n] (G : SimpleGraph V) [DecidableRel G.Adj]
    (four : ∀ x,G.degree x=4) {v : V} (c : G.Walk v v) (hc : IsHamiltonianCycle G c)
    (e : Fin n ≃ V) (red : ∀ x y : V,s(x,y)∈c.edges ↔ ∃ i : Fin n,s(x,y)=s(e i,e (i+1)))
    (q : (G\c.toSubgraph.spanningCoe).ConnectedComponent) (lo hi : Fin n) (le : lo≤hi)
    (block : ∀ j : Fin n,e j∈q.supp ↔ lo≤j ∧ j≤hi) :
    ∃ w,∃ d : G.Walk w w,IsHamiltonianCycle G d ∧ d.edges.toFinset≠c.edges.toFinset := by
  classical
  let m := hi.val-lo.val+1
  let k := n-m
  have low := lo.isLt
  have high := hi.isLt
  have order : lo.val≤hi.val := le
  have pos : 0 < m := by dsimp [m]; omega
  have size : m+k=n := by dsimp [m,k]; omega
  let _ : NeZero m := ⟨by omega⟩
  let _ : NeZero (m+k) := ⟨by omega⟩
  let turn : Fin (m+k) ≃ Fin n := (finCongr size).trans (Equiv.addRight hi)
  let e' := turn.trans e
  have next (j : Fin (m+k)) : turn (j+1)=turn j+1 := by
    change finCongr size (j+1)+hi=finCongr size j+hi+1
    rw [cast_succ]
    abel
  have red' (x y : V) : s(x,y)∈c.edges ↔ ∃ j : Fin (m+k),s(x,y)=s(e' j,e' (j+1)) := by
    rw [red]
    constructor
    · rintro ⟨j,h⟩
      refine ⟨turn.symm j,?_⟩
      simpa only [e',Equiv.trans_apply,next,Equiv.apply_symm_apply] using h
    · rintro ⟨j,h⟩
      exact ⟨turn j,by simpa only [e',Equiv.trans_apply,next] using h⟩
  have val (i : Fin m) : (turn (slot k i)).val=if i.val=0 then hi.val else lo.val+i.val-1 := by
    change ((finCongr size (slot k i))+hi).val=_
    rw [Fin.val_add]
    change ((slot k i).val+hi.val)%n=_
    by_cases zero : i.val=0
    · simp [slot,zero,Nat.mod_eq_of_lt high]
    · have short := i.isLt
      change i.val<hi.val-lo.val+1 at short
      have small : lo.val+i.val-1<n := by omega
      have eq : k+i.val+hi.val=lo.val+i.val-1+n := by dsimp [k,m]; omega
      simp [slot,zero,eq,Nat.mod_eq_of_lt small]
  have range (j : Fin n) : (∃ i : Fin m,turn (slot k i)=j) ↔ lo≤j ∧ j≤hi := by
    constructor
    · rintro ⟨i,rfl⟩
      change lo.val≤(turn (slot k i)).val ∧ (turn (slot k i)).val≤hi.val
      rw [val]
      have short := i.isLt
      change i.val<hi.val-lo.val+1 at short
      split <;> omega
    · rintro ⟨left,right⟩
      change lo.val≤j.val at left
      change j.val≤hi.val at right
      by_cases last : j.val=hi.val
      · exact ⟨0,Fin.ext (by rw [val]; simpa using last.symm)⟩
      · let i : Fin m := ⟨j.val-lo.val+1,by dsimp [m]; omega⟩
        refine ⟨i,Fin.ext ?_⟩
        rw [val]
        change (if j.val-lo.val+1=0 then hi.val else lo.val+(j.val-lo.val+1)-1)=j.val
        split <;> omega
  apply component_sector m k G four c hc e' red' q
  intro z
  obtain ⟨j,rfl⟩ := e.surjective z
  rw [block,←range]
  exact exists_congr (fun i => e.injective.eq_iff.symm)

end OMA.SheehanIntervalComponent

theorem OMA.solution : OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro V _ _ G _ four v c hc n _ e rim q lo hi le block
  exact OMA.SheehanIntervalComponent.linear_sector G four c hc e rim q lo hi le block
