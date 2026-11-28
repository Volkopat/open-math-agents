import OMAStatements.S_oeis_a187853

namespace OMA.S_oeis_a187853

open Finset




instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance


/-! ## Tours as a starting square and a displacement sequence -/

/-- Prefix sums of a displacement sequence. -/
def preN {m : ℕ} (D : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => 0
  | i + 1 => preN D i + (if h : i < m then D ⟨i, h⟩ else 0)

def pre {m : ℕ} (D : Fin m → ℤ × ℤ) (i : Fin (m + 1)) : ℤ × ℤ := preN D i.val

/-- The displacements of a walk. -/
def disp {n m : ℕ} (p : Fin (m + 1) → Fin n × Fin n) (j : Fin m) : ℤ × ℤ :=
  toZ (p j.succ) - toZ (p j.castSucc)

lemma toZ_inj {n : ℕ} {q q' : Fin n × Fin n} (h : toZ q = toZ q') : q = q' := by
  unfold toZ at h
  simp only [Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

lemma pos_eq {n m : ℕ} (p : Fin (m + 1) → Fin n × Fin n) :
    ∀ i : Fin (m + 1), toZ (p i) = toZ (p 0) + pre (disp p) i := by
  intro i
  induction i using Fin.induction with
  | zero => simp [pre, preN]
  | succ j ih =>
    have e : pre (disp p) j.succ = pre (disp p) j.castSucc + disp p j := by
      simp only [pre, Fin.val_succ, Fin.coe_castSucc, preN, dif_pos j.isLt]
    rw [e, ← add_assoc, ← ih]
    simp only [disp]
    abel

/-- `z` lies on the n X n board. -/
def InB (n : ℕ) (z : ℤ × ℤ) : Prop := 0 ≤ z.1 ∧ z.1 < n ∧ 0 ≤ z.2 ∧ z.2 < n

instance (n : ℕ) (z : ℤ × ℤ) : Decidable (InB n z) := by unfold InB; infer_instance

lemma toZ_inB {n : ℕ} (q : Fin n × Fin n) : InB n (toZ q) := by
  unfold InB toZ
  dsimp only
  exact ⟨by positivity, by exact_mod_cast q.1.isLt, by positivity, by exact_mod_cast q.2.isLt⟩

/-- The square with integer coordinates `z`, when `z` is on the board. -/
def sqOf {n : ℕ} (z : ℤ × ℤ) (h : InB n z) : Fin n × Fin n :=
  (⟨z.1.toNat, by have := h.2.1; have := h.1; omega⟩, ⟨z.2.toNat, by have := h.2.2.2; have := h.2.2.1; omega⟩)

lemma toZ_sqOf {n : ℕ} (z : ℤ × ℤ) (h : InB n z) : toZ (sqOf z h) = z := by
  unfold toZ sqOf
  ext
  · simp only; exact Int.toNat_of_nonneg h.1
  · simp only; exact Int.toNat_of_nonneg h.2.2.1

lemma isTour_iff {n m : ℕ} (p : Fin (m + 1) → Fin n × Fin n) :
    IsTour n (m + 1) p ↔ Function.Injective p ∧ ∀ j : Fin m, disp p j ∈ moves := by
  unfold IsTour disp
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨hi, fun j => hs j.castSucc j.succ (by simp)⟩
  · rintro ⟨hi, hs⟩
    refine ⟨hi, fun i j hij => ?_⟩
    have hi' : i.val < m := by have := j.isLt; omega
    have e1 : i = (⟨i.val, hi'⟩ : Fin m).castSucc := Fin.ext rfl
    have e2 : j = (⟨i.val, hi'⟩ : Fin m).succ := Fin.ext (by simp [hij])
    rw [e1, e2]
    exact hs ⟨i.val, hi'⟩

/-- The starting squares of a walk with displacements `D` that stay on the board. -/
def starts (n : ℕ) {m : ℕ} (D : Fin m → ℤ × ℤ) : Finset (Fin n × Fin n) :=
  univ.filter (fun s => ∀ i : Fin (m + 1), InB n (toZ s + pre D i))

theorem count_eq (n m : ℕ) :
    ((univ : Finset (Fin (m + 1) → Fin n × Fin n)).filter (IsTour n (m + 1))).card =
      ∑ D ∈ Fintype.piFinset (fun _ : Fin m => moves.toFinset),
        if Function.Injective (pre D) then (starts n D).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := disp) (t := Fintype.piFinset
    (fun _ : Fin m => moves.toFinset))]
  · refine Finset.sum_congr rfl (fun D hD => ?_)
    rw [Fintype.mem_piFinset] at hD
    split_ifs with hSA
    · refine Finset.card_bij' (fun p _ => p 0)
        (fun s hs => fun i => sqOf (toZ s + pre D i) ((Finset.mem_filter.1 hs).2 i)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [starts, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun i => ?_⟩
        rw [← hp.2, ← pos_eq]
        exact toZ_inB _
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨(isTour_iff _).2 ⟨?_, ?_⟩, ?_⟩
        · intro i i' h
          have h' := congrArg toZ h
          rw [toZ_sqOf, toZ_sqOf] at h'
          exact hSA (add_left_cancel h')
        · intro j
          simp only [disp, toZ_sqOf]
          have e : pre D j.succ = pre D j.castSucc + D j := by
            simp only [pre, Fin.val_succ, Fin.val_castSucc, preN, dif_pos j.isLt]
          rw [e]
          simpa [List.mem_toFinset] using hD j
        · funext j
          simp only [disp, toZ_sqOf]
          have e : pre D j.succ = pre D j.castSucc + D j := by
            simp only [pre, Fin.val_succ, Fin.val_castSucc, preN, dif_pos j.isLt]
          rw [e]
          abel
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        funext i
        apply toZ_inj
        rw [toZ_sqOf, ← hp.2, ← pos_eq]
      · intro s hs
        apply toZ_inj
        rw [toZ_sqOf]
        have e : pre D 0 = 0 := rfl
        rw [e, add_zero]
    · rw [Finset.card_eq_zero]
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hp, hd⟩
      apply hSA
      intro i i' h
      have hi := ((isTour_iff p).1 hp).1
      apply hi
      apply toZ_inj
      rw [pos_eq p i, pos_eq p i', hd, h]
  · intro p hp
    have hp' : IsTour n (m + 1) p := (Finset.mem_filter.1 hp).2
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    simpa [List.mem_toFinset] using ((isTour_iff p).1 hp').2 j

/-! ## Counting the starting squares -/

/-- The squares `x` of a line of length n with `0 ≤ x + c i < n` for every `i`. -/
def line (n : ℕ) {m : ℕ} (c : Fin (m + 1) → ℤ) : Finset (Fin n) :=
  univ.filter (fun x => ∀ i, 0 ≤ (x : ℤ) + c i ∧ (x : ℤ) + c i < n)

lemma starts_eq (n : ℕ) {m : ℕ} (D : Fin m → ℤ × ℤ) :
    (starts n D).card = (line n (fun i => (pre D i).1)).card * (line n (fun i => (pre D i).2)).card := by
  have e : starts n D = line n (fun i => (pre D i).1) ×ˢ line n (fun i => (pre D i).2) := by
    ext s
    simp only [starts, line, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · intro h
      exact ⟨fun i => ⟨(h i).1, (h i).2.1⟩, fun i => ⟨(h i).2.2.1, (h i).2.2.2⟩⟩
    · rintro ⟨h1, h2⟩ i
      exact ⟨(h1 i).1, (h1 i).2, (h2 i).1, (h2 i).2⟩
  rw [e, Finset.card_product]

/-- The width of the offsets `c`: largest minus smallest. -/
def width {m : ℕ} (c : Fin (m + 1) → ℤ) : ℕ :=
  ((univ.sup' univ_nonempty c) - (univ.inf' univ_nonempty c)).toNat

lemma card_line (n : ℕ) {m : ℕ} (c : Fin (m + 1) → ℤ) (h0 : c 0 = 0) :
    (line n c).card = n - width c := by
  set S := univ.sup' univ_nonempty c with hS
  set I := univ.inf' univ_nonempty c with hI
  have hle : ∀ i, c i ≤ S := fun i => Finset.le_sup' c (Finset.mem_univ i)
  have hge : ∀ i, I ≤ c i := fun i => Finset.inf'_le c (Finset.mem_univ i)
  obtain ⟨iS, -, hiS⟩ := Finset.exists_mem_eq_sup' univ_nonempty c
  obtain ⟨iI, -, hiI⟩ := Finset.exists_mem_eq_inf' univ_nonempty c
  have hS0 : 0 ≤ S := h0 ▸ hle 0
  have hI0 : I ≤ 0 := h0 ▸ hge 0
  have e : line n c = (univ : Finset (Fin n)).filter
      (fun x => (-I).toNat ≤ x.val ∧ x.val + S.toNat < n) := by
    ext x
    simp only [line, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h1 := (h iI).1
      have h2 := (h iS).2
      rw [← hiI] at h1
      rw [← hiS] at h2
      constructor <;> omega
    · rintro ⟨h1, h2⟩ i
      have := hle i
      have := hge i
      constructor <;> omega
  rw [e]
  have e2 : ((univ : Finset (Fin n)).filter
      (fun x => (-I).toNat ≤ x.val ∧ x.val + S.toNat < n)).map Fin.valEmbedding =
      Finset.Ico (-I).toNat (n - S.toNat) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, ⟨h1, by simp; omega⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e2, Nat.card_Ico]
  unfold width
  rw [← hS, ← hI]
  omega

/-- The width and height of the walk with displacements `D`. -/
def wX {m : ℕ} (D : Fin m → ℤ × ℤ) : ℕ := width (fun i => (pre D i).1)
def wY {m : ℕ} (D : Fin m → ℤ × ℤ) : ℕ := width (fun i => (pre D i).2)

theorem a_formula (n : ℕ) : a n = ∑ D ∈ Fintype.piFinset (fun _ : Fin 4 => moves.toFinset),
    if Function.Injective (pre D) then (n - wX D) * (n - wY D) else 0 := by
  unfold a
  rw [count_eq n 4]
  refine Finset.sum_congr rfl (fun D _ => ?_)
  split_ifs
  · rw [starts_eq, card_line _ _ (by simp [pre, preN]), card_line _ _ (by simp [pre, preN])]
    rfl
  · rfl

/-! ## The entry's formulas -/

/-- The self-avoiding displacement sequences. -/
def SA : Finset (Fin 4 → ℤ × ℤ) :=
  (Fintype.piFinset (fun _ : Fin 4 => moves.toFinset)).filter (fun D => Function.Injective (pre D))

theorem a_formula' (n : ℕ) : a n = ∑ D ∈ SA, (n - wX D) * (n - wY D) := by
  rw [a_formula, SA, Finset.sum_filter]

/-- A sum over the displacement sequences, one move at a time (so the kernel enumerates the
sequences as nested sums over the moves). -/
lemma sum_pi_succ {β : Type*} [AddCommMonoid β] {m : ℕ} (S : Finset (ℤ × ℤ))
    (F : (Fin (m + 1) → ℤ × ℤ) → β) :
    ∑ D ∈ Fintype.piFinset (fun _ : Fin (m + 1) => S), F D =
      ∑ v ∈ S, ∑ D ∈ Fintype.piFinset (fun _ : Fin m => S), F (Fin.cons v D) := by
  rw [← Finset.sum_product' (f := fun v D => F (Fin.cons v D))]
  refine Finset.sum_bij' (fun D _ => (D 0, Fin.tail D)) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hD ⊢
    exact ⟨hD 0, fun i => hD i.succ⟩
  · intro p hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    intro i
    exact Fin.cases (by simpa using hp.1) (fun j => by simpa using hp.2 j) i
  · intro D _
    simp
  · intro p _
    simp
  · intro D _
    simp

lemma sum_pi_zero {β : Type*} [AddCommMonoid β] (S : Finset (ℤ × ℤ)) (F : (Fin 0 → ℤ × ℤ) → β) :
    ∑ D ∈ Fintype.piFinset (fun _ : Fin 0 => S), F D = F Fin.elim0 := by
  have e : Fintype.piFinset (fun _ : Fin 0 => S) = {Fin.elim0} := by
    ext D
    simp only [Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _ i; exact i.elim0
  rw [e, Finset.sum_singleton]

/-! ## Enumerating the move sequences as lists (cheap for the kernel) -/

/-- The squares visited from `p` along the moves `L`. -/
def walkFrom (p : ℤ × ℤ) : List (ℤ × ℤ) → List (ℤ × ℤ)
  | [] => [p]
  | v :: L => p :: walkFrom (p + v) L

/-- Width of a list of integers together with 0: largest minus smallest. -/
def lw (l : List ℤ) : ℕ := (l.foldr max 0 - l.foldr min 0).toNat

/-- All lists of `m` moves. -/
def allL : ℕ → List (List (ℤ × ℤ))
  | 0 => [[]]
  | m + 1 => moves.flatMap (fun v => (allL m).map (v :: ·))

/-- The summand of a statistic `φ (w, h)` for the move list `L` (0 unless self-avoiding). -/
def term {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (L : List (ℤ × ℤ)) : M :=
  if (walkFrom 0 L).Nodup then
    φ (lw ((walkFrom 0 L).map Prod.fst)) (lw ((walkFrom 0 L).map Prod.snd)) else 0

lemma walkFrom_shift (p : ℤ × ℤ) (L : List (ℤ × ℤ)) :
    walkFrom p L = (walkFrom 0 L).map (p + ·) := by
  induction L generalizing p with
  | nil => simp [walkFrom]
  | cons v L ih =>
    rw [walkFrom, walkFrom, ih (p + v), ih (0 + v)]
    simp [List.map_map, Function.comp_def, add_assoc]

lemma preN_cons {m : ℕ} (v : ℤ × ℤ) (D : Fin m → ℤ × ℤ) (i : ℕ) (hi : i ≤ m) :
    preN (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) (i + 1) = v + preN D i := by
  induction i with
  | zero =>
    have e : preN (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) (0 + 1) =
        preN (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) 0 +
          (if h : 0 < m + 1 then (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) ⟨0, h⟩ else 0) := rfl
    rw [e, dif_pos (by omega)]
    have e2 : (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) ⟨0, by omega⟩ = v :=
      Fin.cons_zero (α := fun _ => ℤ × ℤ) v D
    rw [e2]
    simp [preN]
  | succ i ih =>
    have e1 : preN (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) (i + 1 + 1) =
        preN (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) (i + 1) +
          (if h : i + 1 < m + 1 then (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) ⟨i + 1, h⟩ else 0) := rfl
    have e2 : preN D (i + 1) = preN D i + (if h : i < m then D ⟨i, h⟩ else 0) := rfl
    rw [e1, e2, ih (by omega), dif_pos (by omega), dif_pos (by omega)]
    have e3 : (Fin.cons v D : Fin (m + 1) → ℤ × ℤ) ⟨i + 1, by omega⟩ = D ⟨i, by omega⟩ :=
      Fin.cons_succ (α := fun _ => ℤ × ℤ) v D ⟨i, by omega⟩
    rw [e3, add_assoc]

lemma ofFn_pre : ∀ {m : ℕ} (D : Fin m → ℤ × ℤ), List.ofFn (pre D) = walkFrom 0 (List.ofFn D)
  | 0, D => by simp [pre, preN, walkFrom]
  | m + 1, D => by
    have hD : D = Fin.cons (D 0) (Fin.tail D) := (Fin.cons_self_tail D).symm
    have key : ∀ i : Fin (m + 1), pre D i.succ = D 0 + pre (Fin.tail D) i := by
      intro i
      show preN D (i.val + 1) = D 0 + preN (Fin.tail D) i.val
      conv_lhs => rw [hD]
      exact preN_cons (D 0) (Fin.tail D) i.val (by omega)
    rw [List.ofFn_succ (f := pre D)]
    simp only [key]
    rw [show (List.ofFn fun i => D 0 + pre (Fin.tail D) i) =
        (List.ofFn (pre (Fin.tail D))).map (D 0 + ·) from List.map_ofFn.symm,
      ofFn_pre (Fin.tail D), ← walkFrom_shift, List.ofFn_succ (f := D), walkFrom, zero_add]
    rfl

lemma le_foldr_max (l : List ℤ) (b : ℤ) : ∀ x ∈ l, x ≤ l.foldr max b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons, le_max_iff]
    rcases List.mem_cons.1 hx with rfl | hx
    · left; exact le_rfl
    · right; exact ih x hx

lemma foldr_max_le (l : List ℤ) (b M : ℤ) (hb : b ≤ M) (h : ∀ x ∈ l, x ≤ M) :
    l.foldr max b ≤ M := by
  induction l with
  | nil => simpa using hb
  | cons a l ih =>
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨h a (by simp), ih (fun x hx => h x (by simp [hx]))⟩

lemma foldr_min_le (l : List ℤ) (b : ℤ) : ∀ x ∈ l, l.foldr min b ≤ x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons, min_le_iff]
    rcases List.mem_cons.1 hx with rfl | hx
    · left; exact le_rfl
    · right; exact ih x hx

lemma le_foldr_min (l : List ℤ) (b M : ℤ) (hb : M ≤ b) (h : ∀ x ∈ l, M ≤ x) :
    M ≤ l.foldr min b := by
  induction l with
  | nil => simpa using hb
  | cons a l ih =>
    simp only [List.foldr_cons, le_min_iff]
    exact ⟨h a (by simp), ih (fun x hx => h x (by simp [hx]))⟩

lemma width_eq {m : ℕ} (c : Fin (m + 1) → ℤ) (h0 : c 0 = 0) : width c = lw (List.ofFn c) := by
  unfold width lw
  have hmem : ∀ i, c i ∈ List.ofFn c := fun i => by rw [List.mem_ofFn]; exact ⟨i, rfl⟩
  have hmax : univ.sup' univ_nonempty c = (List.ofFn c).foldr max 0 := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => le_foldr_max _ _ (c i) (hmem i))
    · apply foldr_max_le
      · rw [← h0]; exact Finset.le_sup' c (Finset.mem_univ 0)
      · intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact Finset.le_sup' c (Finset.mem_univ i)
  have hmin : univ.inf' univ_nonempty c = (List.ofFn c).foldr min 0 := by
    apply le_antisymm
    · apply le_foldr_min
      · rw [← h0]; exact Finset.inf'_le c (Finset.mem_univ 0)
      · intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact Finset.inf'_le c (Finset.mem_univ i)
    · exact Finset.le_inf' _ _ (fun i _ => foldr_min_le _ _ (c i) (hmem i))
  rw [hmax, hmin]

lemma term_eq {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) {m : ℕ} (D : Fin m → ℤ × ℤ) :
    term φ (List.ofFn D) = if Function.Injective (pre D) then φ (wX D) (wY D) else 0 := by
  unfold term wX wY
  rw [← ofFn_pre, List.map_ofFn, List.map_ofFn,
    width_eq (fun i => (pre D i).1) (by simp [pre, preN]),
    width_eq (fun i => (pre D i).2) (by simp [pre, preN])]
  by_cases h : Function.Injective (pre D)
  · rw [if_pos (List.nodup_ofFn.2 h), if_pos h]
    rfl
  · rw [if_neg (mt List.nodup_ofFn.1 h), if_neg h]

lemma moves_nodup : moves.Nodup := by decide

lemma sum_flatMap_map {M : Type*} [AddCommMonoid M] (l : List (ℤ × ℤ))
    (g : ℤ × ℤ → List (List (ℤ × ℤ))) (F : List (ℤ × ℤ) → M) :
    ((l.flatMap g).map F).sum = (l.map (fun v => ((g v).map F).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma sum_allL {M : Type*} [AddCommMonoid M] : ∀ (m : ℕ) (F : List (ℤ × ℤ) → M),
    ∑ D ∈ Fintype.piFinset (fun _ : Fin m => moves.toFinset), F (List.ofFn D) =
      ((allL m).map F).sum
  | 0, F => by rw [sum_pi_zero]; simp [allL]
  | m + 1, F => by
    rw [sum_pi_succ]
    have e : ∀ v, ∑ D ∈ Fintype.piFinset (fun _ : Fin m => moves.toFinset),
        F (List.ofFn (Fin.cons v D : Fin (m + 1) → ℤ × ℤ)) =
          ((allL m).map (fun L => F (v :: L))).sum := by
      intro v
      rw [← sum_allL m (fun L => F (v :: L))]
      refine Finset.sum_congr rfl (fun D _ => ?_)
      simp [List.ofFn_succ]
    simp only [e]
    rw [List.sum_toFinset _ moves_nodup, allL, sum_flatMap_map]
    simp [List.map_map, Function.comp_def]

/-- A statistic summed over the self-avoiding sequences, as a list computation. -/
lemma sa_sum_list {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) :
    ∑ D ∈ SA, φ (wX D) (wY D) = ((allL 4).map (term φ)).sum := by
  rw [SA, Finset.sum_filter, ← sum_allL]
  exact Finset.sum_congr rfl (fun D _ => (term_eq φ D).symm)

/-! ## Depth-first enumeration: only the self-avoiding walks are visited -/

/-- The squares visited after following the moves `L` from the head of `vis`, most recent first. -/
def ext : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | vis, [] => vis
  | vis, v :: L => ext ((vis.headD 0 + v) :: vis) L

/-- The summand of `φ` for the continuation `L` of the visited squares `vis`. -/
def termV {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (vis L : List (ℤ × ℤ)) : M :=
  if (ext vis L).Nodup then
    φ (lw ((ext vis L).map Prod.fst)) (lw ((ext vis L).map Prod.snd)) else 0

/-- Depth-first sum of `φ (w, h)` over the self-avoiding continuations by `m` moves of the visited
squares `vis` (most recent first); a branch stops at its first repeated square. -/
def dfs {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) : ℕ → List (ℤ × ℤ) → M
  | 0, vis => φ (lw (vis.map Prod.fst)) (lw (vis.map Prod.snd))
  | m + 1, vis => (moves.map (fun v =>
      if vis.headD 0 + v ∈ vis then 0 else dfs φ m ((vis.headD 0 + v) :: vis))).sum

lemma ext_suffix : ∀ (vis L : List (ℤ × ℤ)), ∃ l, ext vis L = l ++ vis
  | vis, [] => ⟨[], rfl⟩
  | vis, v :: L => by
    obtain ⟨l, hl⟩ := ext_suffix ((vis.headD 0 + v) :: vis) L
    exact ⟨l ++ [vis.headD 0 + v], by rw [ext, hl, List.append_assoc, List.singleton_append]⟩

lemma dfs_eq {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) :
    ∀ (m : ℕ) (vis : List (ℤ × ℤ)), vis.Nodup → dfs φ m vis = ((allL m).map (termV φ vis)).sum
  | 0, vis, h => by simp [dfs, allL, termV, ext, h]
  | m + 1, vis, h => by
    rw [dfs, allL, sum_flatMap_map]
    simp only [List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro v _
    have e : ∀ L, termV φ vis (v :: L) = termV φ ((vis.headD 0 + v) :: vis) L := fun L => rfl
    simp only [e]
    by_cases hm : vis.headD 0 + v ∈ vis
    · rw [if_pos hm]
      symm
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨L, _, rfl⟩ := List.mem_map.1 hx
      unfold termV
      rw [if_neg]
      obtain ⟨l, hl⟩ := ext_suffix ((vis.headD 0 + v) :: vis) L
      rw [hl]
      intro hn
      exact (List.nodup_cons.1 (List.nodup_append.1 hn).2.1).1 hm
    · rw [if_neg hm]
      exact dfs_eq φ m _ (List.nodup_cons.2 ⟨hm, h⟩)

lemma ext_cons : ∀ (p : ℤ × ℤ) (vis L : List (ℤ × ℤ)),
    ext (p :: vis) L = (walkFrom p L).reverse ++ vis
  | p, vis, [] => by simp [ext, walkFrom]
  | p, vis, v :: L => by
    rw [ext, List.headD_cons, ext_cons (p + v) (p :: vis) L, walkFrom, List.reverse_cons,
      List.append_assoc]
    rfl

lemma foldr_max_base (l : List ℤ) (b : ℤ) : b ≤ l.foldr max b := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact le_trans ih (le_max_right _ _)

lemma foldr_min_base (l : List ℤ) (b : ℤ) : l.foldr min b ≤ b := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact le_trans (min_le_right _ _) ih

lemma lw_reverse (l : List ℤ) : lw l.reverse = lw l := by
  unfold lw
  have h1 : l.reverse.foldr max 0 = l.foldr max 0 := le_antisymm
    (foldr_max_le l.reverse 0 _ (foldr_max_base l 0)
      (fun x hx => le_foldr_max l 0 x (List.mem_reverse.1 hx)))
    (foldr_max_le l 0 _ (foldr_max_base l.reverse 0)
      (fun x hx => le_foldr_max l.reverse 0 x (List.mem_reverse.2 hx)))
  have h2 : l.reverse.foldr min 0 = l.foldr min 0 := le_antisymm
    (le_foldr_min l 0 _ (foldr_min_base l.reverse 0)
      (fun x hx => foldr_min_le l.reverse 0 x (List.mem_reverse.2 hx)))
    (le_foldr_min l.reverse 0 _ (foldr_min_base l 0)
      (fun x hx => foldr_min_le l 0 x (List.mem_reverse.1 hx)))
  rw [h1, h2]

lemma lw_map_reverse (f : ℤ × ℤ → ℤ) (l : List (ℤ × ℤ)) : lw (l.reverse.map f) = lw (l.map f) := by
  rw [show l.reverse.map f = (l.map f).reverse by simp, lw_reverse]

lemma term_eq_termV {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (L : List (ℤ × ℤ)) :
    term φ L = termV φ [0] L := by
  unfold term termV
  rw [ext_cons, List.append_nil, lw_map_reverse, lw_map_reverse]
  simp only [List.nodup_reverse]

/-- The least and greatest column and row of `vis` together with the origin. -/
def box (vis : List (ℤ × ℤ)) : ℤ × ℤ × ℤ × ℤ :=
  ((vis.map Prod.fst).foldr min 0, (vis.map Prod.fst).foldr max 0,
    (vis.map Prod.snd).foldr min 0, (vis.map Prod.snd).foldr max 0)

/-- `dfs` with the bounding box `b` of `vis` carried along instead of recomputed at the end. -/
def dfsB {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) :
    ℕ → List (ℤ × ℤ) → ℤ × ℤ × ℤ × ℤ → M
  | 0, _, b => φ (b.2.1 - b.1).toNat (b.2.2.2 - b.2.2.1).toNat
  | m + 1, vis, b => (moves.map (fun v =>
      if vis.headD 0 + v ∈ vis then 0 else
        dfsB φ m ((vis.headD 0 + v) :: vis)
          (min (vis.headD 0 + v).1 b.1, max (vis.headD 0 + v).1 b.2.1,
            min (vis.headD 0 + v).2 b.2.2.1, max (vis.headD 0 + v).2 b.2.2.2))).sum

lemma dfsB_eq {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) :
    ∀ (m : ℕ) (vis : List (ℤ × ℤ)), dfsB φ m vis (box vis) = dfs φ m vis
  | 0, vis => rfl
  | m + 1, vis => by
    rw [dfsB, dfs]
    congr 1
    apply List.map_congr_left
    intro v _
    split_ifs
    · rfl
    · exact dfsB_eq φ m _

/-! ## The same search on natural coordinates with the origin at `(B, B)` -/

/-- A move as the natural numbers to add and to subtract in each coordinate. -/
def splitMove (v : ℤ × ℤ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((v.1.toNat, v.2.toNat), ((-v.1).toNat, (-v.2).toNat))

def movesN : List ((ℕ × ℕ) × (ℕ × ℕ)) := moves.map splitMove

/-- One move from `p` in natural coordinates. -/
def stepN (p : ℕ × ℕ) (mv : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (p.1 + mv.1.1 - mv.2.1, p.2 + mv.1.2 - mv.2.2)

/-- `dfsB` in natural coordinates. -/
def dfsN {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (B : ℕ) :
    ℕ → List (ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ → M
  | 0, _, b => φ (b.2.1 - b.1) (b.2.2.2 - b.2.2.1)
  | m + 1, vis, b => (movesN.map (fun mv =>
      if stepN (vis.headD (B, B)) mv ∈ vis then 0 else
        dfsN φ B m (stepN (vis.headD (B, B)) mv :: vis)
          (min (stepN (vis.headD (B, B)) mv).1 b.1, max (stepN (vis.headD (B, B)) mv).1 b.2.1,
            min (stepN (vis.headD (B, B)) mv).2 b.2.2.1,
            max (stepN (vis.headD (B, B)) mv).2 b.2.2.2))).sum

/-- Natural coordinates back to integer coordinates. -/
def unshift (B : ℕ) (p : ℕ × ℕ) : ℤ × ℤ := ((p.1 : ℤ) - B, (p.2 : ℤ) - B)

def unshiftB (B : ℕ) (b : ℕ × ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ × ℤ :=
  ((b.1 : ℤ) - B, (b.2.1 : ℤ) - B, (b.2.2.1 : ℤ) - B, (b.2.2.2 : ℤ) - B)

lemma unshift_injective (B : ℕ) : Function.Injective (unshift B) := by
  intro p q h
  simp only [unshift, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

lemma movesN_le : ∀ mv ∈ movesN, mv.2.1 ≤ 2 ∧ mv.2.2 ≤ 2 := by decide

lemma unshift_step (B : ℕ) (p : ℕ × ℕ) (v : ℤ × ℤ) (h1 : (splitMove v).2.1 ≤ p.1)
    (h2 : (splitMove v).2.2 ≤ p.2) : unshift B (stepN p (splitMove v)) = unshift B p + v := by
  obtain ⟨x, y⟩ := v
  obtain ⟨a, c⟩ := p
  simp only [splitMove, stepN, unshift] at h1 h2 ⊢
  have ex := Int.toNat_sub_toNat_neg x
  have ey := Int.toNat_sub_toNat_neg y
  refine Prod.ext ?_ ?_
  · show ((a + x.toNat - (-x).toNat : ℕ) : ℤ) - B = ((a : ℤ) - B) + x
    push_cast [Nat.cast_sub (show (-x).toNat ≤ a + x.toNat by omega)]
    linarith
  · show ((c + y.toNat - (-y).toNat : ℕ) : ℤ) - B = ((c : ℤ) - B) + y
    push_cast [Nat.cast_sub (show (-y).toNat ≤ c + y.toNat by omega)]
    linarith

lemma headD_unshift (B : ℕ) (vis : List (ℕ × ℕ)) :
    (vis.map (unshift B)).headD 0 = unshift B (vis.headD (B, B)) := by
  cases vis with
  | nil => ext <;> simp [unshift]
  | cons p vis => rfl

lemma dfsN_eq {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (B : ℕ) :
    ∀ (m : ℕ) (vis : List (ℕ × ℕ)) (b : ℕ × ℕ × ℕ × ℕ),
      2 * m ≤ (vis.headD (B, B)).1 → 2 * m ≤ (vis.headD (B, B)).2 → b.1 ≤ b.2.1 →
      b.2.2.1 ≤ b.2.2.2 → dfsN φ B m vis b = dfsB φ m (vis.map (unshift B)) (unshiftB B b)
  | 0, vis, b, _, _, h3, h4 => by
    have e1 : ((b.2.1 : ℤ) - B - ((b.1 : ℤ) - B)).toNat = b.2.1 - b.1 := by
      rw [show (b.2.1 : ℤ) - B - ((b.1 : ℤ) - B) = ((b.2.1 - b.1 : ℕ) : ℤ) by
        push_cast [Nat.cast_sub h3]; ring]
      exact Int.toNat_natCast _
    have e2 : ((b.2.2.2 : ℤ) - B - ((b.2.2.1 : ℤ) - B)).toNat = b.2.2.2 - b.2.2.1 := by
      rw [show (b.2.2.2 : ℤ) - B - ((b.2.2.1 : ℤ) - B) = ((b.2.2.2 - b.2.2.1 : ℕ) : ℤ) by
        push_cast [Nat.cast_sub h4]; ring]
      exact Int.toNat_natCast _
    simp only [dfsN, dfsB, unshiftB]
    rw [e1, e2]
  | m + 1, vis, b, h1, h2, h3, h4 => by
    rw [dfsN, dfsB, movesN, List.map_map]
    congr 1
    apply List.map_congr_left
    intro v hv
    have hle := movesN_le (splitMove v) (List.mem_map_of_mem hv)
    have hs := unshift_step B (vis.headD (B, B)) v (by omega) (by omega)
    simp only [Function.comp_apply]
    rw [headD_unshift, ← hs]
    by_cases hq : stepN (vis.headD (B, B)) (splitMove v) ∈ vis
    · rw [if_pos hq, if_pos (List.mem_map_of_mem hq)]
    · rw [if_neg hq, if_neg (fun h => hq ((List.mem_map_of_injective (unshift_injective B)).1 h))]
      have hq1 : (stepN (vis.headD (B, B)) (splitMove v)).1 =
          (vis.headD (B, B)).1 + (splitMove v).1.1 - (splitMove v).2.1 := rfl
      have hq2 : (stepN (vis.headD (B, B)) (splitMove v)).2 =
          (vis.headD (B, B)).2 + (splitMove v).1.2 - (splitMove v).2.2 := rfl
      rw [dfsN_eq φ B m _ _ (by simp only [List.headD_cons]; omega)
        (by simp only [List.headD_cons]; omega) (by simp only; omega) (by simp only; omega)]
      simp only [List.map_cons, unshiftB, unshift, Nat.cast_min, Nat.cast_max, min_sub_sub_right,
        max_sub_sub_right]

/-! ## The search the kernel evaluates: recursors and `Nat.beq` instead of instances

The kernel's memory grows with the terms it builds; integer pairs compared through the
decidability instances cost about four times as much as natural pairs compared by `Nat.beq`. -/

def memN (q : ℕ × ℕ) (l : List (ℕ × ℕ)) : Bool :=
  List.rec false (fun p _ ih => (Nat.beq q.1 p.1 && Nat.beq q.2 p.2) || ih) l

def sumN {M : Type*} [AddCommMonoid M] (f : (ℕ × ℕ) × (ℕ × ℕ) → M)
    (l : List ((ℕ × ℕ) × (ℕ × ℕ))) : M :=
  List.rec 0 (fun v _ ih => f v + ih) l

def minN (a b : ℕ) : ℕ := bif Nat.ble a b then a else b

def maxN (a b : ℕ) : ℕ := bif Nat.ble a b then b else a

/-- `dfsN` by the recursors. -/
def dfsNR {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (B m : ℕ) :
    List (ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ → M :=
  Nat.rec (motive := fun _ => List (ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ → M)
    (fun _ b => φ (b.2.1 - b.1) (b.2.2.2 - b.2.2.1))
    (fun _ ih vis b => sumN (fun mv =>
      bif memN (stepN (vis.headD (B, B)) mv) vis then 0 else
        ih (stepN (vis.headD (B, B)) mv :: vis)
          (minN (stepN (vis.headD (B, B)) mv).1 b.1, maxN (stepN (vis.headD (B, B)) mv).1 b.2.1,
            minN (stepN (vis.headD (B, B)) mv).2 b.2.2.1,
            maxN (stepN (vis.headD (B, B)) mv).2 b.2.2.2)) movesN)
    m

lemma sumN_eq {M : Type*} [AddCommMonoid M] (f : (ℕ × ℕ) × (ℕ × ℕ) → M) :
    ∀ l : List ((ℕ × ℕ) × (ℕ × ℕ)), sumN f l = (l.map f).sum
  | [] => rfl
  | v :: l => by
    show f v + sumN f l = (List.map f (v :: l)).sum
    rw [sumN_eq f l, List.map_cons, List.sum_cons]

lemma memN_eq (q : ℕ × ℕ) : ∀ l : List (ℕ × ℕ), memN q l = decide (q ∈ l)
  | [] => by simp [memN]
  | p :: l => by
    show ((Nat.beq q.1 p.1 && Nat.beq q.2 p.2) || memN q l) = decide (q ∈ p :: l)
    rw [memN_eq q l]
    apply Bool.eq_iff_iff.2
    simp [Prod.ext_iff]

lemma minN_eq (a b : ℕ) : minN a b = min a b := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; exact Bool.noConfusion h
    simp only [minN, h, cond_false]
    omega
  · have := Nat.le_of_ble_eq_true h
    simp only [minN, h, cond_true]
    omega

lemma maxN_eq (a b : ℕ) : maxN a b = max a b := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; exact Bool.noConfusion h
    simp only [maxN, h, cond_false]
    omega
  · have := Nat.le_of_ble_eq_true h
    simp only [maxN, h, cond_true]
    omega

lemma dfsNR_succ {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (B m : ℕ) (vis : List (ℕ × ℕ))
    (b : ℕ × ℕ × ℕ × ℕ) : dfsNR φ B (m + 1) vis b = sumN (fun mv =>
      bif memN (stepN (vis.headD (B, B)) mv) vis then 0 else
        dfsNR φ B m (stepN (vis.headD (B, B)) mv :: vis)
          (minN (stepN (vis.headD (B, B)) mv).1 b.1, maxN (stepN (vis.headD (B, B)) mv).1 b.2.1,
            minN (stepN (vis.headD (B, B)) mv).2 b.2.2.1,
            maxN (stepN (vis.headD (B, B)) mv).2 b.2.2.2)) movesN := rfl

lemma dfsNR_eq {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (B : ℕ) :
    ∀ (m : ℕ) (vis : List (ℕ × ℕ)) (b : ℕ × ℕ × ℕ × ℕ), dfsNR φ B m vis b = dfsN φ B m vis b
  | 0, vis, b => rfl
  | m + 1, vis, b => by
    rw [dfsNR_succ, sumN_eq, dfsN]
    congr 1
    apply List.map_congr_left
    intro mv _
    simp only [memN_eq, minN_eq, maxN_eq, Bool.cond_decide]
    split_ifs
    · rfl
    · exact dfsNR_eq φ B m _ _

/-- The sum over the move lists as the depth-first search. -/
lemma sum_term_dfs0 {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (m : ℕ) :
    ((allL m).map (term φ)).sum = dfs φ m [0] := by
  rw [dfs_eq φ m [0] (List.nodup_singleton _)]
  congr 1
  exact List.map_congr_left (fun L _ => term_eq_termV φ L)

/-- The sum over the move lists, as the search that the kernel evaluates. -/
lemma sum_term_dfs {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (m : ℕ) :
    ((allL m).map (term φ)).sum =
      dfsNR φ (2 * m) m [(2 * m, 2 * m)] (2 * m, 2 * m, 2 * m, 2 * m) := by
  rw [dfsNR_eq, dfsN_eq φ (2 * m) m _ _ le_rfl le_rfl le_rfl le_rfl]
  have e1 : [(2 * m, 2 * m)].map (unshift (2 * m)) = [0] := by simp [unshift]
  have e2 : unshiftB (2 * m) (2 * m, 2 * m, 2 * m, 2 * m) = box [0] := by simp [unshiftB, box]
  rw [e1, e2, dfsB_eq, sum_term_dfs0]

/-! The statistics packed into one natural number for the kernel, one base 2^25 digit each:
the count, the sums of w + h and w h, the number of walks wider than the bound, and the
small values. The widths are at most four per move, which keeps every digit below the base. -/

lemma moves_abs : ∀ v ∈ moves, |v.1| ≤ 2 ∧ |v.2| ≤ 2 := by decide

lemma preN_abs {m : ℕ} (D : Fin m → ℤ × ℤ) (hD : ∀ i, D i ∈ moves) :
    ∀ i : ℕ, |(preN D i).1| ≤ 2 * (i : ℤ) ∧ |(preN D i).2| ≤ 2 * (i : ℤ)
  | 0 => by simp [preN]
  | i + 1 => by
    obtain ⟨ih1, ih2⟩ := preN_abs D hD i
    have hd : |(if h : i < m then D ⟨i, h⟩ else (0 : ℤ × ℤ)).1| ≤ 2 ∧
        |(if h : i < m then D ⟨i, h⟩ else (0 : ℤ × ℤ)).2| ≤ 2 := by
      split_ifs with h
      · exact moves_abs _ (hD _)
      · simp
    obtain ⟨hd1, hd2⟩ := hd
    have e : preN D (i + 1) = preN D i + (if h : i < m then D ⟨i, h⟩ else 0) := rfl
    rw [e, Prod.fst_add, Prod.snd_add]
    rw [abs_le] at ih1 ih2 hd1 hd2
    push_cast
    exact ⟨abs_le.2 ⟨by linarith [ih1.1, hd1.1], by linarith [ih1.2, hd1.2]⟩,
      abs_le.2 ⟨by linarith [ih2.1, hd2.1], by linarith [ih2.2, hd2.2]⟩⟩

lemma width_le {m : ℕ} (c : Fin (m + 1) → ℤ) (W : ℕ) (h : ∀ i, |c i| ≤ W) :
    width c ≤ 2 * W := by
  unfold width
  have h1 : univ.sup' univ_nonempty c ≤ W := Finset.sup'_le _ _ (fun i _ => (abs_le.1 (h i)).2)
  have h2 : -(W : ℤ) ≤ univ.inf' univ_nonempty c :=
    Finset.le_inf' _ _ (fun i _ => (abs_le.1 (h i)).1)
  omega

lemma SA_moves {D : Fin 4 → ℤ × ℤ} (hD : D ∈ SA) : ∀ i, D i ∈ moves := fun i =>
  List.mem_toFinset.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hD).1 i)

lemma widths_SA (D : Fin 4 → ℤ × ℤ) (hD : D ∈ SA) : wX D ≤ 16 ∧ wY D ≤ 16 := by
  have hb := preN_abs D (SA_moves hD)
  have hi : ∀ i : Fin (4 + 1), (i.val : ℤ) ≤ 4 := fun i => by
    exact_mod_cast Nat.lt_succ_iff.1 i.isLt
  constructor
  · have := width_le (fun i : Fin (4 + 1) => (pre D i).1) 8 (fun i => by
      have h1 := (hb i.val).1
      have h2 := hi i
      show |(preN D i.val).1| ≤ ((8 : ℕ) : ℤ)
      push_cast
      linarith)
    unfold wX
    omega
  · have := width_le (fun i : Fin (4 + 1) => (pre D i).2) 8 (fun i => by
      have h1 := (hb i.val).2
      have h2 := hi i
      show |(preN D i.val).2| ≤ ((8 : ℕ) : ℤ)
      push_cast
      linarith)
    unfold wY
    omega

lemma card_SA : SA.card ≤ 16 ^ 4 := by
  calc SA.card ≤ (Fintype.piFinset (fun _ : Fin 4 => moves.toFinset)).card :=
        Finset.card_filter_le _ _
    _ = 16 ^ 4 := by
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        List.toFinset_card_of_nodup moves_nodup]
      rfl

lemma sum_lt {f : (Fin 4 → ℤ × ℤ) → ℕ} {c : ℕ} (h : ∀ D ∈ SA, f D ≤ c)
    (hc : 16 ^ 4 * c < 33554432) : ∑ D ∈ SA, f D < 33554432 :=
  calc ∑ D ∈ SA, f D ≤ ∑ _D ∈ SA, c := Finset.sum_le_sum h
    _ = SA.card * c := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 16 ^ 4 * c := Nat.mul_le_mul_right _ card_SA
    _ < 33554432 := hc

/-- A digit in front of the others. -/
def pk (a x : ℕ) : ℕ := a + 33554432 * x

lemma sum_pk {α : Type*} (s : Finset α) (f g : α → ℕ) :
    ∑ x ∈ s, pk (f x) (g x) = pk (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  simp only [pk, Finset.sum_add_distrib, Finset.mul_sum]

lemma digit {a x N : ℕ} (ha : a < 33554432) (h : pk a x = N) :
    a = N % 33554432 ∧ x = N / 33554432 := by
  unfold pk at h
  subst h
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha, zero_add]

def enc (w h : ℕ) : ℕ :=
  pk (1) (pk (w + h) (pk (w * h) (pk (if 8 < w ∨ 8 < h then 1 else 0) (pk ((1 - w) * (1 - h)) (pk ((2 - w) * (2 - h)) (pk ((3 - w) * (3 - h)) (pk ((4 - w) * (4 - h)) (pk ((5 - w) * (5 - h)) (pk ((6 - w) * (6 - h)) (((7 - w) * (7 - h))))))))))))

/-! ## Symmetries of the move set: walks starting with moves in one orbit have equal sums -/

/-- The reflections generating the symmetries of the square: swap the coordinates, negate the
column, negate the row. -/
def sw (p : ℤ × ℤ) : ℤ × ℤ := (p.2, p.1)
def nx (p : ℤ × ℤ) : ℤ × ℤ := (-p.1, p.2)
def ny (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

lemma foldr_max_neg (l : List ℤ) : (l.map (fun x => -x)).foldr max 0 = -(l.foldr min 0) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih, max_neg_neg]

lemma foldr_min_neg (l : List ℤ) : (l.map (fun x => -x)).foldr min 0 = -(l.foldr max 0) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih, min_neg_neg]

lemma lw_neg (l : List ℤ) : lw (l.map (fun x => -x)) = lw l := by
  unfold lw
  rw [foldr_max_neg, foldr_min_neg]
  congr 1
  ring

lemma dfs_map {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (g : ℤ × ℤ → ℤ × ℤ)
    (hadd : ∀ p v, g (p + v) = g p + g v) (h0 : g 0 = 0) (hinj : Function.Injective g)
    (hperm : (moves.map g).Perm moves)
    (hφ : ∀ vis : List (ℤ × ℤ), φ (lw ((vis.map g).map Prod.fst)) (lw ((vis.map g).map Prod.snd)) =
      φ (lw (vis.map Prod.fst)) (lw (vis.map Prod.snd))) :
    ∀ (m : ℕ) (vis : List (ℤ × ℤ)), dfs φ m (vis.map g) = dfs φ m vis
  | 0, vis => by
    simp only [dfs]
    exact hφ vis
  | m + 1, vis => by
    have hh : (vis.map g).headD 0 = g (vis.headD 0) := by
      cases vis with
      | nil => simp [h0]
      | cons p vis => rfl
    rw [dfs, dfs, ← (hperm.map _).sum_eq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u _
    simp only [Function.comp_apply, hh, ← hadd]
    by_cases hq : vis.headD 0 + u ∈ vis
    · rw [if_pos ((List.mem_map_of_injective hinj).2 hq), if_pos hq]
    · rw [if_neg (fun h => hq ((List.mem_map_of_injective hinj).1 h)), if_neg hq, ← List.map_cons,
        dfs_map φ g hadd h0 hinj hperm hφ m]

lemma dfs_sw {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (hsym : ∀ w h, φ w h = φ h w)
    (hperm : (moves.map sw).Perm moves) : ∀ (m : ℕ) (vis : List (ℤ × ℤ)),
    dfs φ m (vis.map sw) = dfs φ m vis :=
  dfs_map φ sw (fun p v => Prod.ext (by simp only [sw, Prod.fst_add, Prod.snd_add])
      (by simp only [sw, Prod.fst_add, Prod.snd_add]))
    (by simp [sw])
    (fun p q h => by
      simp only [sw, Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1)
    hperm
    (fun vis => by
      rw [show (vis.map sw).map Prod.fst = vis.map Prod.snd by
          simp [sw, List.map_map, Function.comp_def],
        show (vis.map sw).map Prod.snd = vis.map Prod.fst by
          simp [sw, List.map_map, Function.comp_def]]
      exact hsym _ _)

lemma dfs_nx {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (hperm : (moves.map nx).Perm moves) :
    ∀ (m : ℕ) (vis : List (ℤ × ℤ)), dfs φ m (vis.map nx) = dfs φ m vis :=
  dfs_map φ nx (fun p v => Prod.ext (by simp only [nx, Prod.fst_add]; ring)
      (by simp only [nx, Prod.snd_add]))
    (by simp [nx])
    (fun p q h => by
      simp only [nx, Prod.mk.injEq, neg_inj] at h
      exact Prod.ext h.1 h.2)
    hperm
    (fun vis => by
      rw [show (vis.map nx).map Prod.fst = (vis.map Prod.fst).map (fun x => -x) by
          simp [nx, List.map_map, Function.comp_def],
        show (vis.map nx).map Prod.snd = vis.map Prod.snd by
          simp [nx, List.map_map, Function.comp_def], lw_neg])

lemma dfs_ny {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (hperm : (moves.map ny).Perm moves) :
    ∀ (m : ℕ) (vis : List (ℤ × ℤ)), dfs φ m (vis.map ny) = dfs φ m vis :=
  dfs_map φ ny (fun p v => Prod.ext (by simp only [ny, Prod.fst_add])
      (by simp only [ny, Prod.snd_add]; ring))
    (by simp [ny])
    (fun p q h => by
      simp only [ny, Prod.mk.injEq, neg_inj] at h
      exact Prod.ext h.1 h.2)
    hperm
    (fun vis => by
      rw [show (vis.map ny).map Prod.snd = (vis.map Prod.snd).map (fun x => -x) by
          simp [ny, List.map_map, Function.comp_def],
        show (vis.map ny).map Prod.fst = vis.map Prod.fst by
          simp [ny, List.map_map, Function.comp_def], lw_neg])

lemma moves_ne : ∀ v ∈ moves, v ≠ 0 := by decide

/-- The search from the origin, one sum per first move. -/
lemma dfs_root {M : Type*} [AddCommMonoid M] (φ : ℕ → ℕ → M) (m : ℕ) :
    dfs φ (m + 1) [0] = (moves.map (fun v => dfs φ m [v, 0])).sum := by
  rw [dfs]
  exact congrArg List.sum (List.map_congr_left (fun v hv => by
    simp only [List.headD_cons, zero_add, List.mem_singleton]
    rw [if_neg (moves_ne v hv)]))

lemma enc_symm : ∀ w h, enc w h = enc h w := by
  intro w h
  simp only [enc, Nat.add_comm, Nat.mul_comm, or_comm]

lemma perm_sw : (moves.map sw).Perm moves := by decide

lemma perm_nx : (moves.map nx).Perm moves := by decide

lemma perm_ny : (moves.map ny).Perm moves := by decide

lemma e1 : dfs enc 3 [(-1, 0), 0] = dfs enc 3 [(1, 0), 0] := by
  rw [show ([(-1, 0), 0] : List (ℤ × ℤ)) = (([(1, 0), 0] : List (ℤ × ℤ)).map nx) by decide, dfs_nx enc perm_nx]

lemma e2 : dfs enc 3 [(0, 1), 0] = dfs enc 3 [(1, 0), 0] := by
  rw [show ([(0, 1), 0] : List (ℤ × ℤ)) = (([(1, 0), 0] : List (ℤ × ℤ)).map sw) by decide, dfs_sw enc enc_symm perm_sw]

lemma e3 : dfs enc 3 [(0, -1), 0] = dfs enc 3 [(1, 0), 0] := by
  rw [show ([(0, -1), 0] : List (ℤ × ℤ)) = ((([(1, 0), 0] : List (ℤ × ℤ)).map sw).map ny) by decide, dfs_ny enc perm_ny, dfs_sw enc enc_symm perm_sw]

lemma e5 : dfs enc 3 [(1, -1), 0] = dfs enc 3 [(1, 1), 0] := by
  rw [show ([(1, -1), 0] : List (ℤ × ℤ)) = (([(1, 1), 0] : List (ℤ × ℤ)).map ny) by decide, dfs_ny enc perm_ny]

lemma e6 : dfs enc 3 [(-1, 1), 0] = dfs enc 3 [(1, 1), 0] := by
  rw [show ([(-1, 1), 0] : List (ℤ × ℤ)) = (([(1, 1), 0] : List (ℤ × ℤ)).map nx) by decide, dfs_nx enc perm_nx]

lemma e7 : dfs enc 3 [(-1, -1), 0] = dfs enc 3 [(1, 1), 0] := by
  rw [show ([(-1, -1), 0] : List (ℤ × ℤ)) = ((([(1, 1), 0] : List (ℤ × ℤ)).map nx).map ny) by decide, dfs_ny enc perm_ny, dfs_nx enc perm_nx]

lemma e9 : dfs enc 3 [(2, 1), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(2, 1), 0] : List (ℤ × ℤ)) = (([(1, 2), 0] : List (ℤ × ℤ)).map sw) by decide, dfs_sw enc enc_symm perm_sw]

lemma e10 : dfs enc 3 [(-1, 2), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(-1, 2), 0] : List (ℤ × ℤ)) = (([(1, 2), 0] : List (ℤ × ℤ)).map nx) by decide, dfs_nx enc perm_nx]

lemma e11 : dfs enc 3 [(-2, 1), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(-2, 1), 0] : List (ℤ × ℤ)) = ((([(1, 2), 0] : List (ℤ × ℤ)).map sw).map nx) by decide, dfs_nx enc perm_nx, dfs_sw enc enc_symm perm_sw]

lemma e12 : dfs enc 3 [(1, -2), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(1, -2), 0] : List (ℤ × ℤ)) = (([(1, 2), 0] : List (ℤ × ℤ)).map ny) by decide, dfs_ny enc perm_ny]

lemma e13 : dfs enc 3 [(2, -1), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(2, -1), 0] : List (ℤ × ℤ)) = ((([(1, 2), 0] : List (ℤ × ℤ)).map sw).map ny) by decide, dfs_ny enc perm_ny, dfs_sw enc enc_symm perm_sw]

lemma e14 : dfs enc 3 [(-1, -2), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(-1, -2), 0] : List (ℤ × ℤ)) = ((([(1, 2), 0] : List (ℤ × ℤ)).map nx).map ny) by decide, dfs_ny enc perm_ny, dfs_nx enc perm_nx]

lemma e15 : dfs enc 3 [(-2, -1), 0] = dfs enc 3 [(1, 2), 0] := by
  rw [show ([(-2, -1), 0] : List (ℤ × ℤ)) = (((([(1, 2), 0] : List (ℤ × ℤ)).map sw).map nx).map ny) by decide, dfs_ny enc perm_ny, dfs_nx enc perm_nx, dfs_sw enc enc_symm perm_sw]

lemma r0 : dfs enc 3 [(1, 0), 0] = 96033256398969566558560297823384559940841043212276353683045245121229761999277073 := by
  rw [← dfsB_eq, show box [(1, 0), 0] = unshiftB 8 (8, 9, 8, 8) by decide,
    show ([(1, 0), 0] : List (ℤ × ℤ)) = [(9, 8), (8, 8)].map (unshift 8) by decide,
    ← dfsN_eq enc 8 3 [(9, 8), (8, 8)] (8, 9, 8, 8) (by decide) (by decide) (by decide) (by decide),
    ← dfsNR_eq]
  decide +kernel

lemma r1 : dfs enc 3 [(1, 1), 0] = 87895243444147476432535320917932252336455364260771066530050993423732535057189923 := by
  rw [← dfsB_eq, show box [(1, 1), 0] = unshiftB 8 (8, 9, 8, 9) by decide,
    show ([(1, 1), 0] : List (ℤ × ℤ)) = [(9, 9), (8, 8)].map (unshift 8) by decide,
    ← dfsN_eq enc 8 3 [(9, 9), (8, 8)] (8, 9, 8, 9) (by decide) (by decide) (by decide) (by decide),
    ← dfsNR_eq]
  decide +kernel

lemma r2 : dfs enc 3 [(1, 2), 0] = 76453537372961666653392979187466413544268688625521736660288562854076166988368992 := by
  rw [← dfsB_eq, show box [(1, 2), 0] = unshiftB 8 (8, 9, 8, 10) by decide,
    show ([(1, 2), 0] : List (ℤ × ℤ)) = [(9, 10), (8, 8)].map (unshift 8) by decide,
    ← dfsN_eq enc 8 3 [(9, 10), (8, 8)] (8, 9, 8, 10) (by decide) (by decide) (by decide) (by decide),
    ← dfsNR_eq]
  decide +kernel

/-- The search below each first move, by orbit. -/
def rootval (v : ℤ × ℤ) : ℕ := if v ∈ ([(1, 0), (-1, 0), (0, 1), (0, -1)] : List (ℤ × ℤ)) then 96033256398969566558560297823384559940841043212276353683045245121229761999277073 else if v ∈ ([(1, 1), (1, -1), (-1, 1), (-1, -1)] : List (ℤ × ℤ)) then 87895243444147476432535320917932252336455364260771066530050993423732535057189923 else 76453537372961666653392979187466413544268688625521736660288562854076166988368992

lemma encs : ∑ D ∈ SA, enc (wX D) (wY D) = 1347342298356161505191526308464998557463335138896363574134693457012458524132819920 := by
  rw [sa_sum_list, sum_term_dfs0, dfs_root enc 3]
  have hv : ∀ v ∈ moves, dfs enc 3 [v, 0] = rootval v := by
    intro v hv
    simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r0.trans (by decide +kernel)
    · exact (e1.trans r0).trans (by decide +kernel)
    · exact (e2.trans r0).trans (by decide +kernel)
    · exact (e3.trans r0).trans (by decide +kernel)
    · exact r1.trans (by decide +kernel)
    · exact (e5.trans r1).trans (by decide +kernel)
    · exact (e6.trans r1).trans (by decide +kernel)
    · exact (e7.trans r1).trans (by decide +kernel)
    · exact r2.trans (by decide +kernel)
    · exact (e9.trans r2).trans (by decide +kernel)
    · exact (e10.trans r2).trans (by decide +kernel)
    · exact (e11.trans r2).trans (by decide +kernel)
    · exact (e12.trans r2).trans (by decide +kernel)
    · exact (e13.trans r2).trans (by decide +kernel)
    · exact (e14.trans r2).trans (by decide +kernel)
    · exact (e15.trans r2).trans (by decide +kernel)
  rw [List.map_congr_left hv]
  decide +kernel

lemma bnd0 : ∑ D ∈ SA, (1) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    norm_num)
    (by norm_num)

lemma bnd1 : ∑ D ∈ SA, (wX D + wY D) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    omega)
    (by norm_num)

lemma bnd2 : ∑ D ∈ SA, (wX D * wY D) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul hw hh).trans (by norm_num))
    (by norm_num)

lemma bnd3 : ∑ D ∈ SA, (if 8 < wX D ∨ 8 < wY D then 1 else 0) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    split_ifs <;> norm_num)
    (by norm_num)

lemma bnd4 : ∑ D ∈ SA, ((1 - wX D) * (1 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 1 _) (Nat.sub_le 1 _)).trans (by norm_num))
    (by norm_num)

lemma bnd5 : ∑ D ∈ SA, ((2 - wX D) * (2 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 2 _) (Nat.sub_le 2 _)).trans (by norm_num))
    (by norm_num)

lemma bnd6 : ∑ D ∈ SA, ((3 - wX D) * (3 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 3 _) (Nat.sub_le 3 _)).trans (by norm_num))
    (by norm_num)

lemma bnd7 : ∑ D ∈ SA, ((4 - wX D) * (4 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 4 _) (Nat.sub_le 4 _)).trans (by norm_num))
    (by norm_num)

lemma bnd8 : ∑ D ∈ SA, ((5 - wX D) * (5 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 5 _) (Nat.sub_le 5 _)).trans (by norm_num))
    (by norm_num)

lemma bnd9 : ∑ D ∈ SA, ((6 - wX D) * (6 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 6 _) (Nat.sub_le 6 _)).trans (by norm_num))
    (by norm_num)

lemma bnd10 : ∑ D ∈ SA, ((7 - wX D) * (7 - wY D)) < 33554432 :=
  sum_lt (c := 256) (fun D hD => by
    obtain ⟨hw, hh⟩ := widths_SA D hD
    exact (Nat.mul_le_mul (Nat.sub_le 7 _) (Nat.sub_le 7 _)).trans (by norm_num))
    (by norm_num)

lemma digits :
    ∑ D ∈ SA, (1) = 50128 ∧
    ∑ D ∈ SA, (wX D + wY D) = 312688 ∧
    ∑ D ∈ SA, (wX D * wY D) = 476944 ∧
    ∑ D ∈ SA, (if 8 < wX D ∨ 8 < wY D then 1 else 0) = 0 ∧
    ∑ D ∈ SA, ((1 - wX D) * (1 - wY D)) = 0 ∧
    ∑ D ∈ SA, ((2 - wX D) * (2 - wY D)) = 0 ∧
    ∑ D ∈ SA, ((3 - wX D) * (3 - wY D)) = 5328 ∧
    ∑ D ∈ SA, ((4 - wX D) * (4 - wY D)) = 49776 ∧
    ∑ D ∈ SA, ((5 - wX D) * (5 - wY D)) = 177040 ∧
    ∑ D ∈ SA, ((6 - wX D) * (6 - wY D)) = 408048 ∧
    ∑ D ∈ SA, ((7 - wX D) * (7 - wY D)) = 744696 := by
  have h0 := encs
  simp only [enc, sum_pk] at h0
  obtain ⟨e0, h1⟩ := digit bnd0 h0
  rw [show (1347342298356161505191526308464998557463335138896363574134693457012458524132819920 % 33554432 : ℕ) = 50128 by norm_num] at e0
  rw [show (1347342298356161505191526308464998557463335138896363574134693457012458524132819920 / 33554432 : ℕ) = 40153929542188689267382809772044377251366828051101075832089586764945343856 by norm_num] at h1
  obtain ⟨e1, h2⟩ := digit bnd1 h1
  rw [show (40153929542188689267382809772044377251366828051101075832089586764945343856 % 33554432 : ℕ) = 312688 by norm_num] at e1
  rw [show (40153929542188689267382809772044377251366828051101075832089586764945343856 / 33554432 : ℕ) = 1196680353349110164266312413574587620835507752034100169899749361424 by norm_num] at h2
  obtain ⟨e2, h3⟩ := digit bnd2 h2
  rw [show (1196680353349110164266312413574587620835507752034100169899749361424 % 33554432 : ℕ) = 476944 by norm_num] at e2
  rw [show (1196680353349110164266312413574587620835507752034100169899749361424 / 33554432 : ℕ) = 35663853685531323083231223034101355696782700778070097264640 by norm_num] at h3
  obtain ⟨e3, h4⟩ := digit bnd3 h3
  rw [show (35663853685531323083231223034101355696782700778070097264640 % 33554432 : ℕ) = 0 by norm_num] at e3
  rw [show (35663853685531323083231223034101355696782700778070097264640 / 33554432 : ℕ) = 1062865665123800131178832740607898107075175666155520 by norm_num] at h4
  obtain ⟨e4, h5⟩ := digit bnd4 h4
  rw [show (1062865665123800131178832740607898107075175666155520 % 33554432 : ℕ) = 0 by norm_num] at e4
  rw [show (1062865665123800131178832740607898107075175666155520 / 33554432 : ℕ) = 31675865206831697558725855964657607885455360 by norm_num] at h5
  obtain ⟨e5, h6⟩ := digit bnd5 h5
  rw [show (31675865206831697558725855964657607885455360 % 33554432 : ℕ) = 0 by norm_num] at e5
  rw [show (31675865206831697558725855964657607885455360 / 33554432 : ℕ) = 944014346803179310522253989120054480 by norm_num] at h6
  obtain ⟨e6, h7⟩ := digit bnd6 h6
  rw [show (944014346803179310522253989120054480 % 33554432 : ℕ) = 5328 by norm_num] at e6
  rw [show (944014346803179310522253989120054480 / 33554432 : ℕ) = 28133819902037957624264180336 by norm_num] at h7
  obtain ⟨e7, h8⟩ := digit bnd7 h7
  rw [show (28133819902037957624264180336 % 33554432 : ℕ) = 49776 by norm_num] at e7
  rw [show (28133819902037957624264180336 / 33554432 : ℕ) = 838453170717893768080 by norm_num] at h8
  obtain ⟨e8, h9⟩ := digit bnd8 h8
  rw [show (838453170717893768080 % 33554432 : ℕ) = 177040 by norm_num] at e8
  rw [show (838453170717893768080 / 33554432 : ℕ) = 24987851700720 by norm_num] at h9
  obtain ⟨e9, h10⟩ := digit bnd9 h9
  rw [show (24987851700720 % 33554432 : ℕ) = 408048 by norm_num] at e9
  rw [show (24987851700720 / 33554432 : ℕ) = 744696 by norm_num] at h10
  exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, h10⟩

lemma sa_card : SA.card = 50128 := by
  have h := digits.1
  rw [Finset.card_eq_sum_ones]
  exact h

lemma sa_sum : ∑ D ∈ SA, (wX D + wY D) = 312688 := by
  have h := digits.2.1
  exact h

lemma sa_prod : ∑ D ∈ SA, wX D * wY D = 476944 := by
  have h := digits.2.2.1
  exact h

lemma sa_max : ∀ D ∈ SA, wX D ≤ 8 ∧ wY D ≤ 8 := by
  have h : ∑ D ∈ SA, (if 8 < wX D ∨ 8 < wY D then 1 else 0) = 0 := by
    have h := digits.2.2.2.1
    exact h
  intro D hD
  have := (Finset.sum_eq_zero_iff.1 h) D hD
  by_cases hc : 8 < wX D ∨ 8 < wY D
  · rw [if_pos hc] at this; exact absurd this one_ne_zero
  · omega

/-- The quadratic, for n ≥ 8. -/
theorem quadratic (n : ℕ) (hn : 8 ≤ n) : (a n : ℤ) = 50128 * n ^ 2 - 312688 * n + 476944 := by
  rw [a_formula', Nat.cast_sum]
  have e : ∀ D ∈ SA, (((n - wX D) * (n - wY D) : ℕ) : ℤ) =
      (n : ℤ) ^ 2 - ((wX D + wY D : ℕ) : ℤ) * n + ((wX D * wY D : ℕ) : ℤ) := by
    intro D hD
    have := sa_max D hD
    push_cast [Nat.cast_sub (show wX D ≤ n by omega), Nat.cast_sub (show wY D ≤ n by omega)]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.sum_mul, sa_card]
  have h1 : ∑ D ∈ SA, ((wX D + wY D : ℕ) : ℤ) = 312688 := by exact_mod_cast sa_sum
  have h2 : ∑ D ∈ SA, ((wX D * wY D : ℕ) : ℤ) = 476944 := by exact_mod_cast sa_prod
  rw [h1, h2]
  simp

/-- The values below the quadratic range, computed in the kernel. -/
lemma a_list (n : ℕ) : a n = ((allL 4).map (term (fun w h => (n - w) * (n - h)))).sum := by
  rw [a_formula']
  exact sa_sum_list (fun w h => (n - w) * (n - h))

lemma small1 : a 1 = 0 := by
  have h := digits.2.2.2.2.1
  rw [a_formula']
  exact h

lemma small2 : a 2 = 0 := by
  have h := digits.2.2.2.2.2.1
  rw [a_formula']
  exact h

lemma small3 : a 3 = 5328 := by
  have h := digits.2.2.2.2.2.2.1
  rw [a_formula']
  exact h

lemma small4 : a 4 = 49776 := by
  have h := digits.2.2.2.2.2.2.2.1
  rw [a_formula']
  exact h

lemma small5 : a 5 = 177040 := by
  have h := digits.2.2.2.2.2.2.2.2.1
  rw [a_formula']
  exact h

lemma small6 : a 6 = 408048 := by
  have h := digits.2.2.2.2.2.2.2.2.2.1
  rw [a_formula']
  exact h

lemma small7 : a 7 = 744696 := by
  have h := digits.2.2.2.2.2.2.2.2.2.2
  rw [a_formula']
  exact h

theorem small : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 5328 ∧ a 4 = 49776 ∧ a 5 = 177040 ∧ a 6 = 408048 ∧ a 7 = 744696 :=
  ⟨small1, small2, small3, small4, small5, small6, small7⟩

theorem a_zero : a 0 = 0 := by
  rw [a_formula']
  apply Finset.sum_eq_zero
  intro D _
  simp

theorem vals : (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 0 ∧ (a 2 : ℤ) = 0 ∧ (a 3 : ℤ) = 5328 ∧ (a 4 : ℤ) = 49776 ∧ (a 5 : ℤ) = 177040 ∧ (a 6 : ℤ) = 408048 ∧ (a 7 : ℤ) = 744696 ∧ (a 8 : ℤ) = 1183632 ∧ (a 9 : ℤ) = 1723120 ∧ (a 10 : ℤ) = 2362864 ∧ (a 11 : ℤ) = 3102864 := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := small
  exact ⟨by rw [a_zero]; norm_num,
    by rw [s1]; norm_num,
    by rw [s2]; norm_num,
    by rw [s3]; norm_num,
    by rw [s4]; norm_num,
    by rw [s5]; norm_num,
    by rw [s6]; norm_num,
    by rw [s7]; norm_num,
    by rw [quadratic 8 (by norm_num)]; norm_num,
    by rw [quadratic 9 (by norm_num)]; norm_num,
    by rw [quadratic 10 (by norm_num)]; norm_num,
    by rw [quadratic 11 (by norm_num)]; norm_num⟩

/-- Hardin's empirical quadratic, for n > 7. -/
theorem quadratic' (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 50128 * n ^ 2 - 312688 * n + 476944 := by
  exact quadratic n (by omega)

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rcases Nat.lt_or_ge n 11 with h | h
  · omega
  rw [quadratic n (by omega), quadratic (n - 1) (by omega), quadratic (n - 2) (by omega),
    quadratic (n - 3) (by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)]
  ring

open PowerSeries in
/-- Barker's g.f., with a(0) = 0 for the empty board. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 = 8 * X ^ 3 * (666 + 4224 * X + 5462 * X ^ 2 + 2616 * X ^ 3 + 237 * X ^ 4 - 419 * X ^ 5 - 217 * X ^ 6 - 37 * X ^ 7) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := vals
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have hD : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    rw [h3]; ring
  have hN : (8 * X ^ 3 * (666 + 4224 * X + 5462 * X ^ 2 + 2616 * X ^ 3 + 237 * X ^ 4 - 419 * X ^ 5 - 217 * X ^ 6 - 37 * X ^ 7) : PowerSeries ℤ) =
      C 5328 * X ^ 3 + C 33792 * X ^ 4 + C 43696 * X ^ 5 + C 20928 * X ^ 6 + C 1896 * X ^ 7 - C 3352 * X ^ 8 - C 1736 * X ^ 9 - C 296 * X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 12 with h | h
  · interval_cases n <;>
      simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, coeff_C, pow_zero, Nat.zero_le, Nat.sub_zero, Nat.sub_self, if_true, if_false] <;> norm_num
  · have hq : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
      rw [quadratic n (by omega), quadratic (n - 1) (by omega), quadratic (n - 2) (by omega),
        quadratic (n - 3) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
        Nat.cast_sub (show 3 ≤ n by omega)]
      ring
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 3 by omega, show 3 ≤ n by omega, show n - 3 ≠ 0 by omega, show n ≠ 4 by omega, show 4 ≤ n by omega, show n - 4 ≠ 0 by omega, show n ≠ 5 by omega, show 5 ≤ n by omega, show n - 5 ≠ 0 by omega, show n ≠ 6 by omega, show 6 ≤ n by omega, show n - 6 ≠ 0 by omega, show n ≠ 7 by omega, show 7 ≤ n by omega, show n - 7 ≠ 0 by omega, show n ≠ 8 by omega, show 8 ≤ n by omega, show n - 8 ≠ 0 by omega, show n ≠ 9 by omega, show 9 ≤ n by omega, show n - 9 ≠ 0 by omega, show n ≠ 10 by omega, show 10 ≤ n by omega, show n - 10 ≠ 0 by omega, coeff_C, if_true, if_false]
    linear_combination hq

/-- Controls: the entry's terms a(1..11). -/
theorem controls : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 5328 ∧ a 4 = 49776 ∧ a 5 = 177040 ∧ a 6 = 408048 ∧ a 7 = 744696 ∧ a 8 = 1183632 ∧ a 9 = 1723120 ∧ a 10 = 2362864 ∧ a 11 = 3102864 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := vals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Hardin's quadratic and Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 50128 * n ^ 2 - 312688 * n + 476944) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 8 * PowerSeries.X ^ 3 * (666 + 4224 * PowerSeries.X + 5462 * PowerSeries.X ^ 2 + 2616 * PowerSeries.X ^ 3 + 237 * PowerSeries.X ^ 4 - 419 * PowerSeries.X ^ 5 - 217 * PowerSeries.X ^ 6 - 37 * PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) :=
  ⟨quadratic', gf, recurrence⟩

end OMA.S_oeis_a187853

theorem OMA.solution : type_of% @OMA.S_oeis_a187853.main :=
  OMA.S_oeis_a187853.conjecture
