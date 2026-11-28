import OMAStatements.S_oeis_a183629
import Mathlib.Tactic

namespace OMA.P_oeis_a183629

open OMA.S_oeis_a183629

private def rowAdj (r : Fin 7 → Fin 3) : Fin 6 → ℕ :=
  fun j => (r ⟨j.1, by omega⟩).1 + (r ⟨j.1 + 1, by omega⟩).1

private def compAdj (s : Fin 6 → ℕ) : Fin 6 → ℕ :=
  fun j => 4 - s j

private def compRow (r : Fin 7 → Fin 3) : Fin 7 → Fin 3 :=
  fun j => ⟨2 - (r j).1, by have := (r j).isLt; omega⟩

private lemma compRow_invol (r : Fin 7 → Fin 3) : compRow (compRow r) = r := by
  funext j; apply Fin.ext; dsimp [compRow]; have := (r j).isLt; omega

private lemma rowAdj_compRow (r : Fin 7 → Fin 3) : rowAdj (compRow r) = compAdj (rowAdj r) := by
  funext j; dsimp [rowAdj, compAdj, compRow]
  have h1 := (r ⟨j.1, by omega⟩).isLt
  have h2 := (r ⟨j.1 + 1, by omega⟩).isLt
  omega

private lemma rowAdj_le4 (r : Fin 7 → Fin 3) (j : Fin 6) : rowAdj r j ≤ 4 := by
  dsimp [rowAdj]
  have h1 := (r ⟨j.1, by omega⟩).isLt
  have h2 := (r ⟨j.1 + 1, by omega⟩).isLt
  omega

private def fiber (s : Fin 6 → ℕ) : Finset (Fin 7 → Fin 3) :=
  Finset.univ.filter (fun r => rowAdj r = s)

private lemma card_fiber_compAdj (s : Fin 6 → ℕ) (hs : ∀ j, s j ≤ 4) :
    (fiber (compAdj s)).card = (fiber s).card := by
  refine Finset.card_bij (fun r _ => compRow r) ?_ ?_ ?_
  · intro r hr
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [rowAdj_compRow, hr]
    funext j; dsimp [compAdj]; have := hs j; omega
  · intro r1 _ r2 _ h
    have := congrArg compRow h
    rwa [compRow_invol, compRow_invol] at this
  · intro r hr
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    refine ⟨compRow r, ?_, compRow_invol r⟩
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rowAdj_compRow, hr]

private lemma valid_imp_rowAdj {n : ℕ} (A : Fin (n + 1) × Fin 7 → Fin 3)
    (hA : ∀ (i : Fin n) (j : Fin 6),
      (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)).1 +
      (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 +
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)).1 +
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 = 4)
    (i : Fin (n + 1)) :
    rowAdj (fun j => A (i, j)) =
      if Even i.1 then rowAdj (fun j => A (0, j)) else compAdj (rowAdj (fun j => A (0, j))) := by
  induction hi : i.1 generalizing i with
  | zero =>
    have hi0 : i = 0 := Fin.ext hi
    subst hi0; rw [if_pos Even.zero]
  | succ m ih =>
    have hm : m < n + 1 := by have := i.isLt; omega
    have hprev := ih ⟨m, hm⟩ rfl
    funext j
    have hsub := hA ⟨m, by omega⟩ j
    have hprej := congrFun hprev j
    have hi_eq : (⟨m + 1, by omega⟩ : Fin (n + 1)) = i := Fin.ext hi.symm
    rw [hi_eq] at hsub
    have hm_eq : (⟨(⟨m, by omega⟩ : Fin n).1, by omega⟩ : Fin (n + 1)) = ⟨m, hm⟩ := rfl
    rw [hm_eq] at hsub
    by_cases hmev : Even m
    · have hms : ¬ Even (m + 1) := by rwa [Nat.even_add_one, not_not]
      rw [if_pos hmev] at hprej
      rw [if_neg hms]
      simp only [rowAdj, compAdj] at hprej ⊢
      omega
    · have hms : Even (m + 1) := by rwa [Nat.even_add_one]
      rw [if_neg hmev] at hprej
      rw [if_pos hms]
      simp only [rowAdj, compAdj] at hprej ⊢
      have hle := rowAdj_le4 (fun j => A (0, j)) j
      dsimp [rowAdj] at hle
      omega

private lemma card_valid_with_init (n : ℕ) (r0 : Fin 7 → Fin 3) :
    (Finset.univ.filter (fun A : Fin (n + 1) × Fin 7 → Fin 3 =>
      (∀ (i : Fin n) (j : Fin 6),
        (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩)).1 +
        (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 +
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩)).1 +
        (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)).1 = 4) ∧
      rowAdj (fun j => A (0, j)) = rowAdj r0)).card =
      (fiber (rowAdj r0)).card ^ (n + 1) := by
  let s := rowAdj r0
  let target (i : Fin (n + 1)) : Fin 6 → ℕ := if Even i.1 then s else compAdj s
  have hpi : (Fintype.piFinset (fun i : Fin (n + 1) => fiber (target i))).card =
      (fiber s).card ^ (n + 1) := by
    rw [Fintype.card_piFinset]
    have hprod : ∀ i : Fin (n + 1), (fiber (target i)).card = (fiber s).card := by
      intro i; dsimp [target]
      split_ifs
      · rfl
      · exact card_fiber_compAdj s (rowAdj_le4 r0)
    simp only [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hpi]
  refine Finset.card_bij (fun A _ i j => A (i, j)) ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    simp only [Fintype.mem_piFinset, fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [valid_imp_rowAdj A hA.1 i, hA.2]
  · intro A1 _ A2 _ h
    funext ⟨i, j⟩
    exact congrFun (congrFun h i) j
  · intro f hf
    simp only [Fintype.mem_piFinset, fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨fun p => f p.1 p.2, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i j => ?_, ?_⟩
    · have h1 := congrFun (hf ⟨i.1, by omega⟩) j
      have h2 := congrFun (hf ⟨i.1 + 1, by omega⟩) j
      dsimp only [target] at h1 h2
      have hle := rowAdj_le4 r0 j; dsimp [rowAdj] at hle
      by_cases hev : Even i.1
      · have hev' : ¬ Even (i.1 + 1) := by rwa [Nat.even_add_one, not_not]
        rw [if_pos hev] at h1; rw [if_neg hev'] at h2
        simp only [rowAdj, compAdj, s] at h1 h2; omega
      · have hev' : Even (i.1 + 1) := by rwa [Nat.even_add_one]
        rw [if_neg hev] at h1; rw [if_pos hev'] at h2
        simp only [rowAdj, compAdj, s] at h1 h2; omega
    · have hf0 := hf 0
      simp only [Fin.val_zero, Even.zero, ↓reduceIte, target] at hf0
      exact hf0

private lemma A183629_eq_sum_fiber_pow (n : ℕ) :
    A183629 n = ∑ s ∈ (Finset.univ : Finset (Fin 7 → Fin 3)).image rowAdj,
      (fiber s).card ^ (n + 1) := by
  unfold A183629
  rw [Finset.card_eq_sum_card_fiberwise (f := fun A : Fin (n + 1) × Fin 7 → Fin 3 =>
        rowAdj (fun j => A (0, j)))
      (t := (Finset.univ : Finset (Fin 7 → Fin 3)).image rowAdj)
      (fun A _ => Finset.mem_image_of_mem rowAdj (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
  rcases hs with ⟨r0, rfl⟩
  rw [Finset.filter_filter]
  exact card_valid_with_init n r0

private lemma rowAdj_eq_iff (r1 r2 : Fin 7 → Fin 3) :
    rowAdj r1 = rowAdj r2 ↔
      ∀ j : Fin 7, ((r2 j).1 : ℤ) - ((r1 j).1 : ℤ) =
        if Even j.1 then ((r2 0).1 : ℤ) - ((r1 0).1 : ℤ)
        else ((r1 0).1 : ℤ) - ((r2 0).1 : ℤ) := by
  constructor
  · intro h j
    induction hj : j.1 generalizing j with
    | zero =>
      have hj0 : j = 0 := Fin.ext hj
      subst hj0; simp
    | succ m ih =>
      have hm : m < 7 := by have := j.isLt; omega
      have hprev := ih ⟨m, hm⟩ rfl
      have hstep := congrFun h ⟨m, by omega⟩
      dsimp [rowAdj] at hstep
      have hj_eq : (⟨m + 1, by omega⟩ : Fin 7) = j := Fin.ext hj.symm
      rw [hj_eq] at hstep
      by_cases hmev : Even m
      · have hms : ¬ Even (m + 1) := by rwa [Nat.even_add_one, not_not]
        rw [if_pos hmev] at hprev; rw [if_neg hms]; omega
      · have hms : Even (m + 1) := by rwa [Nat.even_add_one]
        rw [if_neg hmev] at hprev; rw [if_pos hms]; omega
  · intro h
    funext j
    have h1 := h ⟨j.1, by omega⟩
    have h2 := h ⟨j.1 + 1, by omega⟩
    dsimp [rowAdj] at h1 h2 ⊢
    by_cases hev : Even j.1
    · have hev' : ¬ Even (j.1 + 1) := by rwa [Nat.even_add_one, not_not]
      rw [if_pos hev] at h1; rw [if_neg hev'] at h2; omega
    · have hev' : Even (j.1 + 1) := by rwa [Nat.even_add_one]
      rw [if_neg hev] at h1; rw [if_pos hev'] at h2; omega

private def shiftUp (r : Fin 7 → Fin 3) : Prop :=
  ∀ j : Fin 7, if Even j.1 then (r j).1 < 2 else 0 < (r j).1

private instance (r : Fin 7 → Fin 3) : Decidable (shiftUp r) := by
  unfold shiftUp; infer_instance

private def shiftDn (r : Fin 7 → Fin 3) : Prop :=
  ∀ j : Fin 7, if Even j.1 then 0 < (r j).1 else (r j).1 < 2

private instance (r : Fin 7 → Fin 3) : Decidable (shiftDn r) := by
  unfold shiftDn; infer_instance

private def upRow (r : Fin 7 → Fin 3) : Fin 7 → Fin 3 :=
  fun j => if Even j.1 then ⟨min 2 ((r j).1 + 1), by omega⟩ else ⟨(r j).1 - 1, by have := (r j).isLt; omega⟩

private lemma rowAdj_upRow (r : Fin 7 → Fin 3) (hr : shiftUp r) :
    rowAdj (upRow r) = rowAdj r := by
  rw [rowAdj_eq_iff]
  intro j
  have hj := hr j
  have h0 := hr 0
  simp only [Fin.val_zero, Even.zero, ↓reduceIte] at h0
  have hu0 : (upRow r 0).1 = (r 0).1 + 1 := by
    simp only [upRow, Fin.val_zero, Even.zero, ↓reduceIte]
    exact Nat.min_eq_right (by omega)
  by_cases hev : Even j.1
  · have huj : (upRow r j).1 = (r j).1 + 1 := by
      simp only [upRow, hev, ↓reduceIte]
      rw [if_pos hev] at hj
      exact Nat.min_eq_right (by omega)
    rw [if_pos hev, hu0, huj]; push_cast; ring
  · have huj : (upRow r j).1 = (r j).1 - 1 := by
      simp only [upRow, hev, ↓reduceIte]
    rw [if_neg hev] at hj ⊢
    rw [hu0, huj]
    have hsub : (((r j).1 - 1 : ℕ) : ℤ) = ((r j).1 : ℤ) - 1 := Nat.cast_sub (by omega)
    rw [hsub]; push_cast; ring

private def rAll1 : Fin 7 → Fin 3 := fun _ => 1
private def rAlt0 : Fin 7 → Fin 3 := fun j => if Even j.1 then 0 else 2
private def rAlt2 : Fin 7 → Fin 3 := fun j => if Even j.1 then 2 else 0

private lemma fiber_rAll1 : fiber (rowAdj rAll1) = {rAlt0, rAll1, rAlt2} := by
  ext r
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, rowAdj_eq_iff]
  constructor
  · intro h
    have h0 := (r 0).isLt
    interval_cases hr0 : (r 0).1
    · left; funext j; apply Fin.ext
      have hj := h j; dsimp [rAll1, rAlt0] at hj ⊢
      split_ifs at hj ⊢ <;> omega
    · right; left; funext j; apply Fin.ext
      have hj := h j; dsimp [rAll1] at hj ⊢
      split_ifs at hj <;> omega
    · right; right; funext j; apply Fin.ext
      have hj := h j; dsimp [rAll1, rAlt2] at hj ⊢
      split_ifs at hj ⊢ <;> omega
  · rintro (rfl | rfl | rfl) <;> intro j <;> dsimp [rAll1, rAlt0, rAlt2] <;> split_ifs <;> omega

private lemma card_fiber_rAll1 : (fiber (rowAdj rAll1)).card = 3 := by
  rw [fiber_rAll1]
  have h1 : rAlt0 ≠ rAll1 := by intro h; have := congrArg (fun f => (f 0).1) h; simp [rAlt0, rAll1] at this
  have h2 : rAlt0 ≠ rAlt2 := by intro h; have := congrArg (fun f => (f 0).1) h; simp [rAlt0, rAlt2] at this
  have h3 : rAll1 ≠ rAlt2 := by intro h; have := congrArg (fun f => (f 0).1) h; simp [rAll1, rAlt2] at this
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]

private lemma fiber_eq_pair_of_shiftUp (r : Fin 7 → Fin 3)
    (hup : shiftUp r) (hne1 : r ≠ rAll1) (hne0 : r ≠ rAlt0) :
    fiber (rowAdj r) = {r, upRow r} ∧ r ≠ upRow r := by
  have hne_up : r ≠ upRow r := by
    intro h
    have h0 := congrArg (fun f => (f 0).1) h
    have hu0 := hup 0
    simp only [Fin.val_zero, Even.zero, ↓reduceIte, upRow, Fin.val_mk] at h0 hu0
    omega
  refine ⟨?_, hne_up⟩
  ext r'
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hadj
    rw [rowAdj_eq_iff] at hadj
    have hd : ((r' 0).1 : ℤ) - ((r 0).1 : ℤ) = 0 ∨ ((r' 0).1 : ℤ) - ((r 0).1 : ℤ) = 1 := by
      have hr0 := (r 0).isLt; have hr'0 := (r' 0).isLt
      have hu0 := hup 0; simp only [Fin.val_zero, Even.zero, ↓reduceIte] at hu0
      by_cases hneg : ((r' 0).1 : ℤ) - ((r 0).1 : ℤ) = -1
      · exfalso; apply hne1; funext j; apply Fin.ext
        have hj := hadj j; have huj := hup j; have hr'j := (r' j).isLt
        dsimp [rAll1] at hj ⊢; split_ifs at hj huj <;> omega
      · by_cases h2 : ((r' 0).1 : ℤ) - ((r 0).1 : ℤ) = 2
        · exfalso; apply hne0; funext j; apply Fin.ext
          have hj := hadj j; have hr'j := (r' j).isLt
          dsimp [rAlt0] at hj ⊢; split_ifs at hj ⊢ <;> omega
        · omega
    rcases hd with hd0 | hd1
    · left; funext j; apply Fin.ext
      have hj := hadj j; split_ifs at hj <;> omega
    · right; funext j; apply Fin.ext
      have hj := hadj j; have huj := hup j; dsimp only [upRow]
      split_ifs at hj huj ⊢ <;> dsimp only <;> omega
  · rintro (rfl | rfl)
    · rfl
    · exact rowAdj_upRow r hup

private lemma card_shiftUp :
    (Finset.univ.filter shiftUp).card = 2 ^ 7 := by
  have heq : Finset.univ.filter shiftUp =
      Fintype.piFinset (fun j : Fin 7 =>
        if Even j.1 then ({0, 1} : Finset (Fin 3)) else ({1, 2} : Finset (Fin 3))) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, shiftUp]
    refine forall_congr' fun j => ?_
    have hj := (r j).isLt
    split_ifs <;> simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_zero, Fin.val_one, Fin.val_two] <;> omega
  rw [heq, Fintype.card_piFinset]
  have h2 : ∀ j : Fin 7,
      (if Even j.1 then ({0, 1} : Finset (Fin 3)) else ({1, 2} : Finset (Fin 3))).card = 2 := by
    intro j; split_ifs <;> decide
  simp [h2]

private lemma A183629_closed_all (n : ℕ) :
    A183629 n = 1932 + 126 * 2 ^ (n + 1) + 3 ^ (n + 1) := by
  rw [A183629_eq_sum_fiber_pow]
  set S : Finset (Fin 6 → ℕ) := (Finset.univ : Finset (Fin 7 → Fin 3)).image rowAdj
  set R2 : Finset (Fin 7 → Fin 3) := ((Finset.univ.filter shiftUp).erase rAll1).erase rAlt0
  set S2 : Finset (Fin 6 → ℕ) := R2.image rowAdj
  set s3 : Fin 6 → ℕ := rowAdj rAll1
  have hrAll1_up : shiftUp rAll1 := by intro j; dsimp [rAll1]; split_ifs <;> omega
  have hrAlt0_up : shiftUp rAlt0 := by intro j; dsimp [rAlt0]; split_ifs <;> omega
  have hne_01 : rAlt0 ≠ rAll1 := by
    intro h; have := congrArg (fun f => (f 0).1) h; simp [rAlt0, rAll1] at this
  have hcard_R2 : R2.card = 126 := by
    have h1 : rAll1 ∈ Finset.univ.filter shiftUp := by simp [hrAll1_up]
    have h2 : rAlt0 ∈ (Finset.univ.filter shiftUp).erase rAll1 := by
      rw [Finset.mem_erase]; exact ⟨hne_01, by simp [hrAlt0_up]⟩
    rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1, card_shiftUp]; norm_num
  have hcard_S2_fib : ∀ s ∈ S2, (fiber s).card = 2 := by
    intro s hs
    simp only [S2, Finset.mem_image] at hs
    rcases hs with ⟨r, hr, rfl⟩
    simp only [R2, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rcases hr with ⟨hne0, hne1, hup⟩
    obtain ⟨hfib, hne_up⟩ := fiber_eq_pair_of_shiftUp r hup hne1 hne0
    rw [hfib, Finset.card_pair hne_up]
  have hcard_S2 : S2.card = 126 := by
    rw [Finset.card_image_of_injOn]
    · exact hcard_R2
    · intro r1 hr1 r2 hr2 hadj
      simp only [Finset.mem_coe, R2, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
      rcases hr1 with ⟨hne01, hne11, hup1⟩
      rcases hr2 with ⟨hne02, hne12, hup2⟩
      obtain ⟨hfib, _⟩ := fiber_eq_pair_of_shiftUp r1 hup1 hne11 hne01
      have hmem : r2 ∈ fiber (rowAdj r1) := by simp [fiber, hadj]
      rw [hfib, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · rfl
      · exfalso; apply hne01
        funext j; apply Fin.ext
        have hu1 := hup1 j; have hu2 := hup2 j
        dsimp only [upRow, rAlt0] at hu2 ⊢
        split_ifs at hu1 hu2 ⊢ <;> dsimp only at hu2 ⊢ <;> omega
  have hs3_mem : s3 ∈ S := Finset.mem_image_of_mem rowAdj (Finset.mem_univ rAll1)
  have hS2_sub : S2 ⊆ S := Finset.image_subset_image (Finset.subset_univ R2)
  have hs3_notMem : s3 ∉ S2 := by
    intro h; have := hcard_S2_fib s3 h; rw [card_fiber_rAll1] at this; omega
  set S1 : Finset (Fin 6 → ℕ) := (S.erase s3) \ S2
  have hcard_S1_fib : ∀ s ∈ S1, (fiber s).card = 1 := by
    intro s hs
    simp only [S1, Finset.mem_sdiff, Finset.mem_erase, S, Finset.mem_image, Finset.mem_univ, true_and] at hs
    rcases hs with ⟨⟨hne_s3, ⟨r, rfl⟩⟩, hnotS2⟩
    have hmem_r : r ∈ fiber (rowAdj r) := by simp [fiber]
    have hsub_sing : fiber (rowAdj r) = {r} := by
      ext r'
      simp only [Finset.mem_singleton]
      constructor
      · intro hr'
        by_contra hne
        simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hr'
        have hdiff := (rowAdj_eq_iff r r').mp hr'.symm
        have h0ne : (r' 0).1 ≠ (r 0).1 := by
          intro h0; apply hne; funext j; apply Fin.ext
          have hj := hdiff j; split_ifs at hj <;> omega
        have hex_up : ∃ u : Fin 7 → Fin 3, shiftUp u ∧ rowAdj u = rowAdj r := by
          by_cases hlt : (r 0).1 < (r' 0).1
          · refine ⟨r, ?_, rfl⟩
            intro j; have hj := hdiff j; have hr'j := (r' j).isLt; split_ifs at hj ⊢ <;> omega
          · refine ⟨r', ?_, hr'⟩
            intro j; have hj := hdiff j; have hrj := (r j).isLt; split_ifs at hj ⊢ <;> omega
        rcases hex_up with ⟨u, hu, huadj⟩
        by_cases hu1 : u = rAll1
        · subst hu1; exact hne_s3 huadj.symm
        · by_cases hu0 : u = rAlt0
          · subst hu0
            have h01 : rowAdj rAlt0 = rowAdj rAll1 := by
              rw [rowAdj_eq_iff]; intro j; dsimp [rAlt0, rAll1]; split_ifs <;> omega
            exact hne_s3 (huadj.symm.trans h01)
          · apply hnotS2
            simp only [S2, Finset.mem_image]
            refine ⟨u, ?_, huadj⟩
            simp only [R2, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hu0, hu1, hu⟩
      · rintro rfl; exact hmem_r
    rw [hsub_sing, Finset.card_singleton]
  have hpart : ∀ f : (Fin 6 → ℕ) → ℕ,
      ∑ s ∈ S, f s = f s3 + ∑ s ∈ S2, f s + ∑ s ∈ S1, f s := by
    intro f
    have h1 : ∑ s ∈ S, f s = f s3 + ∑ s ∈ S.erase s3, f s :=
      (Finset.add_sum_erase S f hs3_mem).symm
    have hS2_sub' : S2 ⊆ S.erase s3 := by
      intro s hs; rw [Finset.mem_erase]; exact ⟨fun h => hs3_notMem (h ▸ hs), hS2_sub hs⟩
    have h2 : ∑ s ∈ S.erase s3, f s = ∑ s ∈ S2, f s + ∑ s ∈ S1, f s := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hS2_sub']
    omega
  have htot : ∑ s ∈ S, (fiber s).card = 3 ^ 7 := by
    have h1 : (Finset.univ : Finset (Fin 7 → Fin 3)).card = ∑ s ∈ S, (fiber s).card := by
      exact Finset.card_eq_sum_card_image rowAdj Finset.univ
    rw [← h1, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hcard_S1 : S1.card = 1932 := by
    have h := hpart (fun s => (fiber s).card)
    rw [htot, card_fiber_rAll1, Finset.sum_congr rfl hcard_S2_fib, Finset.sum_const, smul_eq_mul,
      hcard_S2, Finset.sum_congr rfl hcard_S1_fib, Finset.sum_const, smul_eq_mul, mul_one] at h
    omega
  rw [hpart (fun s => (fiber s).card ^ (n + 1)), card_fiber_rAll1]
  have hsum2 : ∑ s ∈ S2, (fiber s).card ^ (n + 1) = 126 * 2 ^ (n + 1) := by
    rw [Finset.sum_congr rfl (fun s hs => by rw [hcard_S2_fib s hs]), Finset.sum_const,
      smul_eq_mul, hcard_S2]
  have hsum1 : ∑ s ∈ S1, (fiber s).card ^ (n + 1) = 1932 := by
    rw [Finset.sum_congr rfl (fun s hs => by rw [hcard_S1_fib s hs, one_pow]), Finset.sum_const,
      smul_eq_mul, mul_one, hcard_S1]
  rw [hsum2, hsum1]; omega

private lemma A183629_closed (n : ℕ) (_hn : 1 ≤ n) :
    A183629 n = 3 * (644 + 21 * 2 ^ (2 + n) + 3 ^ n) := by
  rw [A183629_closed_all]
  have h2 : 2 ^ (2 + n) = 2 * 2 ^ (n + 1) := by rw [show 2 + n = (n + 1) + 1 by omega, pow_succ]; ring
  have h3 : 3 ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ]; ring
  rw [h2, h3]; ring

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A183629_gf :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183629 n : ℤ)) =
      3 * PowerSeries.X * (815 - 3901 * PowerSeries.X + 4374 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183629 n : ℤ))
  have hlhs : (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * F =
      F - PowerSeries.C 6 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 11 * (PowerSeries.X ^ 2 * F) - PowerSeries.C 6 * (PowerSeries.X ^ 3 * F) := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h11 : PowerSeries.C (11 : ℤ) = (11 : PowerSeries ℤ) := rfl
    rw [h6, h11, pow_one]; ring
  have hrhs : 3 * (PowerSeries.X : PowerSeries ℤ) * (815 - 3901 * PowerSeries.X + 4374 * PowerSeries.X ^ 2) =
      PowerSeries.C 2445 * PowerSeries.X - PowerSeries.C 11703 * PowerSeries.X ^ 2 +
      PowerSeries.C 13122 * PowerSeries.X ^ 3 := by
    have h1 : PowerSeries.C (2445 : ℤ) = (2445 : PowerSeries ℤ) := rfl
    have h2 : PowerSeries.C (11703 : ℤ) = (11703 : PowerSeries ℤ) := rfl
    have h3 : PowerSeries.C (13122 : ℤ) = (13122 : PowerSeries ℤ) := rfl
    rw [h1, h2, h3]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, A183629_closed_all]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero, A183629_closed_all]
    push_cast
    have h2a : (2 : ℤ) ^ (n + 1) = 8 * (2 : ℤ) ^ (n - 2) := by
      rw [show n + 1 = (n - 2) + 3 by omega, pow_add]; ring
    have h2b : (2 : ℤ) ^ (n - 1 + 1) = 4 * (2 : ℤ) ^ (n - 2) := by
      rw [show n - 1 + 1 = (n - 2) + 2 by omega, pow_add]; ring
    have h2c : (2 : ℤ) ^ (n - 2 + 1) = 2 * (2 : ℤ) ^ (n - 2) := by
      rw [show n - 2 + 1 = (n - 2) + 1 by omega, pow_add]; ring
    have h2d : (2 : ℤ) ^ (n - 3 + 1) = (2 : ℤ) ^ (n - 2) := by
      rw [show n - 3 + 1 = n - 2 by omega]
    have h3a : (3 : ℤ) ^ (n + 1) = 27 * (3 : ℤ) ^ (n - 2) := by
      rw [show n + 1 = (n - 2) + 3 by omega, pow_add]; ring
    have h3b : (3 : ℤ) ^ (n - 1 + 1) = 9 * (3 : ℤ) ^ (n - 2) := by
      rw [show n - 1 + 1 = (n - 2) + 2 by omega, pow_add]; ring
    have h3c : (3 : ℤ) ^ (n - 2 + 1) = 3 * (3 : ℤ) ^ (n - 2) := by
      rw [show n - 2 + 1 = (n - 2) + 1 by omega, pow_add]; ring
    have h3d : (3 : ℤ) ^ (n - 3 + 1) = (3 : ℤ) ^ (n - 2) := by
      rw [show n - 3 + 1 = n - 2 by omega]
    rw [h2a, h2b, h2c, h2d, h3a, h3b, h3c, h3d]; ring

end OMA.P_oeis_a183629

theorem OMA.solution : type_of% @OMA.S_oeis_a183629.main :=
  ⟨OMA.P_oeis_a183629.A183629_closed, OMA.P_oeis_a183629.A183629_gf⟩
