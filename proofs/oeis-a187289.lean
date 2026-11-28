import OMAStatements.S_oeis_a187289

namespace OMA.S_oeis_a187289

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

theorem a_formula (n : ℕ) : a n = ∑ D ∈ Fintype.piFinset (fun _ : Fin 3 => moves.toFinset),
    if Function.Injective (pre D) then (n - wX D) * (n - wY D) else 0 := by
  unfold a
  rw [count_eq n 3]
  refine Finset.sum_congr rfl (fun D _ => ?_)
  split_ifs
  · rw [starts_eq, card_line _ _ (by simp [pre, preN]), card_line _ _ (by simp [pre, preN])]
    rfl
  · rfl

/-! ## The entry's formulas -/

/-- The self-avoiding displacement sequences. -/
def SA : Finset (Fin 3 → ℤ × ℤ) :=
  (Fintype.piFinset (fun _ : Fin 3 => moves.toFinset)).filter (fun D => Function.Injective (pre D))

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
    ∑ D ∈ SA, φ (wX D) (wY D) = ((allL 3).map (term φ)).sum := by
  rw [SA, Finset.sum_filter, ← sum_allL]
  exact Finset.sum_congr rfl (fun D _ => (term_eq φ D).symm)

/-! The statistics needed, a few at a time in one pass over the move lists each: the count,
the sums of w + h and w h, the number of walks wider than the bound, and the small values. -/

def stat0 (w h : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (1, w + h, w * h, if 6 < w ∨ 6 < h then 1 else 0, (1 - w) * (1 - h), 0)

lemma stats0 : ∑ D ∈ SA, stat0 (wX D) (wY D) =
    (380, 1532, 1224, 0, 0, 0) :=
  (sa_sum_list stat0).trans (by decide +kernel)

def stat1 (w h : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((2 - w) * (2 - h), (3 - w) * (3 - h), (4 - w) * (4 - h), (5 - w) * (5 - h), 0)

lemma stats1 : ∑ D ∈ SA, stat1 (wX D) (wY D) =
    (8, 288, 1256, 3084, 0) :=
  (sa_sum_list stat1).trans (by decide +kernel)

lemma sa_card : SA.card = 380 := by
  have h := congrArg (fun p => p.1) stats0
  simp only [Prod.fst_sum, Prod.snd_sum, stat0] at h
  rw [Finset.card_eq_sum_ones]
  exact h

lemma sa_sum : ∑ D ∈ SA, (wX D + wY D) = 1532 := by
  have h := congrArg (fun p => p.2.1) stats0
  simp only [Prod.fst_sum, Prod.snd_sum, stat0] at h
  exact h

lemma sa_prod : ∑ D ∈ SA, wX D * wY D = 1224 := by
  have h := congrArg (fun p => p.2.2.1) stats0
  simp only [Prod.fst_sum, Prod.snd_sum, stat0] at h
  exact h

lemma sa_max : ∀ D ∈ SA, wX D ≤ 6 ∧ wY D ≤ 6 := by
  have h : ∑ D ∈ SA, (if 6 < wX D ∨ 6 < wY D then 1 else 0) = 0 := by
    have h := congrArg (fun p => p.2.2.2.1) stats0
    simp only [Prod.fst_sum, Prod.snd_sum, stat0] at h
    exact h
  intro D hD
  have := (Finset.sum_eq_zero_iff.1 h) D hD
  by_cases hc : 6 < wX D ∨ 6 < wY D
  · rw [if_pos hc] at this; exact absurd this one_ne_zero
  · omega

/-- The quadratic, for n ≥ 6. -/
theorem quadratic (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = 380 * n ^ 2 - 1532 * n + 1224 := by
  rw [a_formula', Nat.cast_sum]
  have e : ∀ D ∈ SA, (((n - wX D) * (n - wY D) : ℕ) : ℤ) =
      (n : ℤ) ^ 2 - ((wX D + wY D : ℕ) : ℤ) * n + ((wX D * wY D : ℕ) : ℤ) := by
    intro D hD
    have := sa_max D hD
    push_cast [Nat.cast_sub (show wX D ≤ n by omega), Nat.cast_sub (show wY D ≤ n by omega)]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.sum_mul, sa_card]
  have h1 : ∑ D ∈ SA, ((wX D + wY D : ℕ) : ℤ) = 1532 := by exact_mod_cast sa_sum
  have h2 : ∑ D ∈ SA, ((wX D * wY D : ℕ) : ℤ) = 1224 := by exact_mod_cast sa_prod
  rw [h1, h2]
  simp

/-- The values below the quadratic range, computed in the kernel. -/
lemma a_list (n : ℕ) : a n = ((allL 3).map (term (fun w h => (n - w) * (n - h)))).sum := by
  rw [a_formula']
  exact sa_sum_list (fun w h => (n - w) * (n - h))

lemma small1 : a 1 = 0 := by
  have h := congrArg (fun p => p.2.2.2.2.1) stats0
  simp only [Prod.fst_sum, Prod.snd_sum, stat0] at h
  rw [a_formula']
  exact h

lemma small2 : a 2 = 8 := by
  have h := congrArg (fun p => p.1) stats1
  simp only [Prod.fst_sum, Prod.snd_sum, stat1] at h
  rw [a_formula']
  exact h

lemma small3 : a 3 = 288 := by
  have h := congrArg (fun p => p.2.1) stats1
  simp only [Prod.fst_sum, Prod.snd_sum, stat1] at h
  rw [a_formula']
  exact h

lemma small4 : a 4 = 1256 := by
  have h := congrArg (fun p => p.2.2.1) stats1
  simp only [Prod.fst_sum, Prod.snd_sum, stat1] at h
  rw [a_formula']
  exact h

lemma small5 : a 5 = 3084 := by
  have h := congrArg (fun p => p.2.2.2.1) stats1
  simp only [Prod.fst_sum, Prod.snd_sum, stat1] at h
  rw [a_formula']
  exact h

theorem small : a 1 = 0 ∧ a 2 = 8 ∧ a 3 = 288 ∧ a 4 = 1256 ∧ a 5 = 3084 :=
  ⟨small1, small2, small3, small4, small5⟩

theorem a_zero : a 0 = 0 := by
  rw [a_formula']
  apply Finset.sum_eq_zero
  intro D _
  simp

theorem vals : (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 0 ∧ (a 2 : ℤ) = 8 ∧ (a 3 : ℤ) = 288 ∧ (a 4 : ℤ) = 1256 ∧ (a 5 : ℤ) = 3084 ∧ (a 6 : ℤ) = 5712 ∧ (a 7 : ℤ) = 9120 ∧ (a 8 : ℤ) = 13288 ∧ (a 9 : ℤ) = 18216 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := small
  exact ⟨by rw [a_zero]; norm_num,
    by rw [s1]; norm_num,
    by rw [s2]; norm_num,
    by rw [s3]; norm_num,
    by rw [s4]; norm_num,
    by rw [s5]; norm_num,
    by rw [quadratic 6 (by norm_num)]; norm_num,
    by rw [quadratic 7 (by norm_num)]; norm_num,
    by rw [quadratic 8 (by norm_num)]; norm_num,
    by rw [quadratic 9 (by norm_num)]; norm_num⟩

/-- Hardin's empirical quadratic, for n > 5. -/
theorem quadratic' (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 380 * n ^ 2 - 1532 * n + 1224 := by
  exact quadratic n (by omega)

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rcases Nat.lt_or_ge n 9 with h | h
  · omega
  rw [quadratic n (by omega), quadratic (n - 1) (by omega), quadratic (n - 2) (by omega),
    quadratic (n - 3) (by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)]
  ring

open PowerSeries in
/-- Barker's g.f., with a(0) = 0 for the empty board. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 = 4 * X ^ 2 * (2 + 66 * X + 104 * X ^ 2 + 43 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := vals
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have hD : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    rw [h3]; ring
  have hN : (4 * X ^ 2 * (2 + 66 * X + 104 * X ^ 2 + 43 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6) : PowerSeries ℤ) =
      C 8 * X ^ 2 + C 264 * X ^ 3 + C 416 * X ^ 4 + C 172 * X ^ 5 - C 60 * X ^ 6 - C 20 * X ^ 7 - C 20 * X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;>
      simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, coeff_C, pow_zero, Nat.zero_le, Nat.sub_zero, Nat.sub_self, if_true, if_false] <;> norm_num
  · have hq : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
      rw [quadratic n (by omega), quadratic (n - 1) (by omega), quadratic (n - 2) (by omega),
        quadratic (n - 3) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
        Nat.cast_sub (show 3 ≤ n by omega)]
      ring
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 2 by omega, show 2 ≤ n by omega, show n - 2 ≠ 0 by omega, show n ≠ 3 by omega, show 3 ≤ n by omega, show n - 3 ≠ 0 by omega, show n ≠ 4 by omega, show 4 ≤ n by omega, show n - 4 ≠ 0 by omega, show n ≠ 5 by omega, show 5 ≤ n by omega, show n - 5 ≠ 0 by omega, show n ≠ 6 by omega, show 6 ≤ n by omega, show n - 6 ≠ 0 by omega, show n ≠ 7 by omega, show 7 ≤ n by omega, show n - 7 ≠ 0 by omega, show n ≠ 8 by omega, show 8 ≤ n by omega, show n - 8 ≠ 0 by omega, coeff_C, if_true, if_false]
    linear_combination hq

/-- Controls: the entry's terms a(1..9). -/
theorem controls : a 1 = 0 ∧ a 2 = 8 ∧ a 3 = 288 ∧ a 4 = 1256 ∧ a 5 = 3084 ∧ a 6 = 5712 ∧ a 7 = 9120 ∧ a 8 = 13288 ∧ a 9 = 18216 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := vals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Hardin's quadratic and Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 380 * n ^ 2 - 1532 * n + 1224) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 4 * PowerSeries.X ^ 2 * (2 + 66 * PowerSeries.X + 104 * PowerSeries.X ^ 2 + 43 * PowerSeries.X ^ 3 - 15 * PowerSeries.X ^ 4 - 5 * PowerSeries.X ^ 5 - 5 * PowerSeries.X ^ 6) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) :=
  ⟨quadratic', gf, recurrence⟩

end OMA.S_oeis_a187289

theorem OMA.solution : type_of% @OMA.S_oeis_a187289.main :=
  OMA.S_oeis_a187289.conjecture
