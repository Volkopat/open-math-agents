import OMAStatements.S_oeis_a227555

/-!
Proof of Barker's conjectures for OEIS A227555. The rows of the larger array are read from the top
by a finite automaton whose state is the current row together with the set of adjacent columns
that are still equal; an indicator array arises exactly when the automaton accepts it. The subset
construction gives a finite deterministic automaton (its states are bit masks), checked in the
kernel; the count of accepted words then satisfies the (1 - x)^12 recurrence componentwise, and
the generating function follows by comparing coefficients.
-/

namespace OMA.S_oeis_a227555

open PowerSeries Finset

/-! ### Generic part: lexicographic order on 0..1 words -/

theorem cons_le_cons_iff' {α : Type*} [LinearOrder α] (x y : α) (l l' : List α) :
    x :: l ≤ y :: l' ↔ x < y ∨ (x = y ∧ l ≤ l') := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  constructor
  · rintro (h | h)
    · have h' : List.Lex (· < ·) (x :: l) (y :: l') := h
      cases h' with
      | cons h => exact Or.inr ⟨rfl, Or.inl h⟩
      | rel h => exact Or.inl h
    · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
      exact Or.inr ⟨rfl, Or.inr rfl⟩
  · rintro (h | ⟨rfl, h | rfl⟩)
    · exact Or.inl (List.Lex.rel h)
    · exact Or.inl (List.Lex.cons h)
    · exact Or.inr rfl

theorem ofFn_le_iff {α : Type*} [LinearOrder α] : ∀ {m : ℕ} (f g : Fin m → α),
    List.ofFn f ≤ List.ofFn g ↔ ∀ k : Fin m, (∀ k' : Fin m, k' < k → f k' = g k') → f k ≤ g k
  | 0, f, g => by simp [List.ofFn_zero]
  | m + 1, f, g => by
    rw [List.ofFn_succ, List.ofFn_succ, cons_le_cons_iff', ofFn_le_iff]
    constructor
    · rintro (h | ⟨h0, h⟩) k hk
      · refine Fin.cases (fun _ => h.le) (fun k hk => ?_) k hk
        exact absurd (hk 0 (Fin.succ_pos k)) h.ne
      · refine Fin.cases (fun _ => h0.le) (fun k hk => ?_) k hk
        exact h k (fun k' hk' => hk k'.succ (Fin.succ_lt_succ_iff.mpr hk'))
    · intro h
      rcases lt_or_eq_of_le (h 0 (fun k' hk' => absurd hk' (Fin.not_lt_zero k'))) with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ⟨h0, fun k hk => h k.succ (fun k' hk' => ?_)⟩
        refine Fin.cases (fun _ => h0) (fun k'' hk'' => hk k'' (Fin.succ_lt_succ_iff.mp hk'')) k' hk'

/-! ### Generic part: the scanning automaton -/

section Gen

variable (w : ℕ) (pN : ℕ → ℕ → ℕ → ℕ → Bool)

/-- Row codes and flag codes. -/
abbrev Q := Fin (2 ^ (w + 1)) × Fin (2 ^ w)

def dR (ρ : Fin (2 ^ (w + 1))) : Fin (w + 1) → Fin 2 := finFunctionFinEquiv.symm ρ
def dF (φ : Fin (2 ^ w)) : Fin w → Fin 2 := finFunctionFinEquiv.symm φ

def lexOK {k : ℕ} (r r' : Fin k → Fin 2) : Prop :=
  ∀ i : Fin k, (∀ i' : Fin k, i' < i → r i' = r' i') → r i ≤ r' i

def flagOK (e : Fin w → Fin 2) (r' : Fin (w + 1) → Fin 2) : Prop :=
  ∀ j : Fin w, e j = 1 → r' j.castSucc ≤ r' j.succ

def nfF (e : Fin w → Fin 2) (r' : Fin (w + 1) → Fin 2) : Fin w → Fin 2 := fun j =>
  if e j = 1 ∧ r' j.castSucc = r' j.succ then 1 else 0

def outL (r r' : Fin (w + 1) → Fin 2) : Fin w → Fin 2 := fun j =>
  if pN (r j.castSucc) (r j.succ) (r' j.castSucc) (r' j.succ) then 1 else 0

/-- One step of the scan: the row `q'.1` follows the row `q.1`, the flags record which
adjacent columns are still equal, and `b` is the indicator row produced. -/
def T (q : Q w) (b : Fin w → Fin 2) (q' : Q w) : Prop :=
  lexOK (dR w q.1) (dR w q'.1) ∧ flagOK w (dF w q.2) (dR w q'.1) ∧
    q'.2 = finFunctionFinEquiv (nfF w (dF w q.2) (dR w q'.1)) ∧ b = outL w pN (dR w q.1) (dR w q'.1)

def Init (q : Q w) : Prop :=
  flagOK w (fun _ => 1) (dR w q.1) ∧ q.2 = finFunctionFinEquiv (nfF w (fun _ => 1) (dR w q.1))

def indG {n : ℕ} (A : Fin (n + 1) → Fin (w + 1) → Fin 2) : Fin n → Fin w → Fin 2 := fun i j =>
  if pN (A i.castSucc j.castSucc) (A i.castSucc j.succ) (A i.succ j.castSucc) (A i.succ j.succ)
  then 1 else 0

theorem lexOK_iff {k : ℕ} (r r' : Fin k → Fin 2) : List.ofFn r ≤ List.ofFn r' ↔ lexOK r r' :=
  ofFn_le_iff r r'

theorem image_iff {n : ℕ} (B : Fin n → Fin w → Fin 2) :
    B ∈ (univ.filter (fun A : Fin (n + 1) → Fin (w + 1) → Fin 2 => IsSorted A)).image (indG w pN) ↔
      ∃ q : Fin (n + 1) → Q w, Init w (q 0) ∧ ∀ i : Fin n, T w pN (q i.castSucc) (B i) (q i.succ) := by
  constructor
  · simp only [mem_image, mem_filter, mem_univ, true_and]
    rintro ⟨A, ⟨hrow, hcol⟩, rfl⟩
    rw [Fin.monotone_iff_le_succ] at hrow hcol
    have hc : ∀ (j : Fin w) (k : Fin (n + 1)), (∀ k' : Fin (n + 1), k' < k →
        A k' j.castSucc = A k' j.succ) → A k j.castSucc ≤ A k j.succ := fun j =>
      (ofFn_le_iff _ _).mp (hcol j)
    let E : Fin (n + 1) → Fin w → Fin 2 := fun i j =>
      if ∀ i' : Fin (n + 1), i' ≤ i → A i' j.castSucc = A i' j.succ then 1 else 0
    refine ⟨fun i => (finFunctionFinEquiv (A i), finFunctionFinEquiv (E i)), ?_, ?_⟩
    · simp only [Init, dR, Equiv.symm_apply_apply]
      refine ⟨fun j _ => hc j 0 (fun k' hk' => absurd hk' (Fin.not_lt_zero k')), ?_⟩
      congr 1
      funext j
      simp only [nfF, E, true_and]
      congr 1
      apply propext
      constructor
      · intro h; exact h 0 le_rfl
      · intro h i' hi'
        rw [nonpos_iff_eq_zero.mp hi'] at *; exact h
    · intro i
      simp only [T, dR, dF, Equiv.symm_apply_apply]
      refine ⟨(lexOK_iff _ _).mp (hrow i), ?_, ?_, rfl⟩
      · intro j hj
        apply hc j i.succ
        intro k' hk'
        simp only [E] at hj
        split_ifs at hj with h
        · exact h k' (Fin.le_castSucc_iff.mpr hk')
        · exact absurd hj (by decide)
      · congr 1
        funext j
        simp only [nfF, E]
        have key : (∀ i' : Fin (n + 1), i' ≤ i.succ → A i' j.castSucc = A i' j.succ) ↔
            (∀ i' : Fin (n + 1), i' ≤ i.castSucc → A i' j.castSucc = A i' j.succ) ∧
              A i.succ j.castSucc = A i.succ j.succ := by
          constructor
          · intro h
            exact ⟨fun i' hi' => h i' (hi'.trans Fin.castSucc_lt_succ.le), h _ le_rfl⟩
          · rintro ⟨h1, h2⟩ i' hi'
            rcases lt_or_eq_of_le hi' with h3 | h3
            · exact h1 i' (Fin.le_castSucc_iff.mpr h3)
            · rw [h3]; exact h2
        by_cases h1 : ∀ i' : Fin (n + 1), i' ≤ i.castSucc → A i' j.castSucc = A i' j.succ <;>
          by_cases h2 : A i.succ j.castSucc = A i.succ j.succ <;> simp [h1, h2, key]
  · rintro ⟨q, h0, hT⟩
    simp only [mem_image, mem_filter, mem_univ, true_and]
    let A : Fin (n + 1) → Fin (w + 1) → Fin 2 := fun i => dR w (q i).1
    have hE : ∀ (i : Fin (n + 1)) (j : Fin w), dF w (q i).2 j =
        if ∀ i' : Fin (n + 1), i' ≤ i → A i' j.castSucc = A i' j.succ then 1 else 0 := by
      intro i
      induction i using Fin.induction with
      | zero =>
        intro j
        rw [h0.2]
        simp only [dF, Equiv.symm_apply_apply, nfF, true_and]
        congr 1
        apply propext
        constructor
        · intro h i' hi'; rw [nonpos_iff_eq_zero.mp hi']; exact h
        · intro h; exact h 0 le_rfl
      | succ i ih =>
        intro j
        rw [(hT i).2.2.1]
        simp only [dF, Equiv.symm_apply_apply, nfF]
        have key : (∀ i' : Fin (n + 1), i' ≤ i.succ → A i' j.castSucc = A i' j.succ) ↔
            (∀ i' : Fin (n + 1), i' ≤ i.castSucc → A i' j.castSucc = A i' j.succ) ∧
              A i.succ j.castSucc = A i.succ j.succ := by
          constructor
          · intro h
            exact ⟨fun i' hi' => h i' (hi'.trans Fin.castSucc_lt_succ.le), h _ le_rfl⟩
          · rintro ⟨h1, h2⟩ i' hi'
            rcases lt_or_eq_of_le hi' with h3 | h3
            · exact h1 i' (Fin.le_castSucc_iff.mpr h3)
            · rw [h3]; exact h2
        have ih' := ih j
        simp only [dF] at ih'
        rw [ih']
        by_cases h1 : ∀ i' : Fin (n + 1), i' ≤ i.castSucc → A i' j.castSucc = A i' j.succ <;>
          by_cases h2 : A i.succ j.castSucc = A i.succ j.succ <;> simp [h1, h2, key, A]
    refine ⟨A, ⟨?_, ?_⟩, ?_⟩
    · rw [Fin.monotone_iff_le_succ]
      intro i
      exact (lexOK_iff _ _).mpr (hT i).1
    · rw [Fin.monotone_iff_le_succ]
      intro j
      rw [ofFn_le_iff]
      intro k hk
      induction k using Fin.cases with
      | zero => exact h0.1 j rfl
      | succ i =>
        apply (hT i).2.1 j
        rw [hE]
        rw [if_pos]
        intro i' hi'
        exact hk i' (lt_of_le_of_lt hi' Fin.castSucc_lt_succ)
    · funext i j
      rw [(hT i).2.2.2]
      rfl

/-! ### Subset construction and counting -/

open Classical in
noncomputable def δ (S : Finset (Q w)) (b : Fin w → Fin 2) : Finset (Q w) :=
  univ.filter (fun q' => ∃ q ∈ S, T w pN q b q')

open Classical in
theorem mem_δ (S : Finset (Q w)) (b : Fin w → Fin 2) (q' : Q w) :
    q' ∈ δ w pN S b ↔ ∃ q ∈ S, T w pN q b q' := by
  unfold δ; simp

noncomputable def δs : {k : ℕ} → Finset (Q w) → (Fin k → Fin w → Fin 2) → Finset (Q w)
  | 0, S, _ => S
  | _ + 1, S, B => δs (δ w pN S (B 0)) (Fin.tail B)

theorem run_iff : ∀ {k : ℕ} (S : Finset (Q w)) (B : Fin k → Fin w → Fin 2),
    (∃ q : Fin (k + 1) → Q w, q 0 ∈ S ∧ ∀ i : Fin k, T w pN (q i.castSucc) (B i) (q i.succ)) ↔
      (δs w pN S B).Nonempty
  | 0, S, B => by
    simp only [δs]
    constructor
    · rintro ⟨q, hq, -⟩; exact ⟨q 0, hq⟩
    · rintro ⟨x, hx⟩; exact ⟨fun _ => x, hx, fun i => i.elim0⟩
  | k + 1, S, B => by
    simp only [δs]
    rw [← run_iff]
    constructor
    · rintro ⟨q, hq, hT⟩
      refine ⟨fun i => q i.succ, ?_, fun i => ?_⟩
      · simp only [δ, mem_filter, mem_univ, true_and]
        exact ⟨q 0, hq, hT 0⟩
      · have := hT i.succ
        simp only [Fin.tail]
        rwa [← Fin.succ_castSucc] at this
    · rintro ⟨q, hq, hT⟩
      simp only [δ, mem_filter, mem_univ, true_and] at hq
      obtain ⟨q0, hq0, h0⟩ := hq
      refine ⟨Fin.cons q0 q, hq0, fun i => ?_⟩
      induction i using Fin.cases with
      | zero => simpa using h0
      | succ i =>
        have := hT i
        simp only [Fin.tail] at this
        rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact this

noncomputable def V (k : ℕ) (S : Finset (Q w)) : ℕ :=
  ∑ B : Fin k → Fin w → Fin 2, if (δs w pN S B).Nonempty then 1 else 0

theorem V_succ (k : ℕ) (S : Finset (Q w)) :
    V w pN (k + 1) S = ∑ b : Fin w → Fin 2, V w pN k (δ w pN S b) := by
  simp only [V]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin w → Fin 2)).sum_comp, Fintype.sum_prod_type]
  rfl

open Classical in
theorem card_image_eq (n : ℕ) :
    ((univ.filter (fun A : Fin (n + 1) → Fin (w + 1) → Fin 2 => IsSorted A)).image (indG w pN)).card =
      V w pN n (univ.filter (Init w)) := by
  rw [V, ← Finset.card_filter]
  congr 1
  ext B
  rw [image_iff, mem_filter, ← run_iff]
  simp

end Gen

/-! ### Generic part: codes, bit masks and kernel tables -/

section Code

variable (w : ℕ) (pN : ℕ → ℕ → ℕ → ℕ → Bool)

def bit (x j : ℕ) : ℕ := x / 2 ^ j % 2

def cd (q : Q w) : ℕ := q.1 + 2 ^ (w + 1) * q.2

def FS (m : ℕ) : Finset (Q w) := univ.filter (fun q => m.testBit (cd w q) = true)

def lexN (ρ ρ' : ℕ) : Bool :=
  decide (∀ i < w + 1, (∀ i' < i, bit ρ i' = bit ρ' i') → bit ρ i ≤ bit ρ' i)

def flagN (eb : ℕ → ℕ) (ρ' : ℕ) : Bool := decide (∀ j < w, eb j = 1 → bit ρ' j ≤ bit ρ' (j + 1))

def nfN (eb : ℕ → ℕ) (ρ' : ℕ) : ℕ :=
  ∑ j ∈ range w, (if eb j = 1 ∧ bit ρ' j = bit ρ' (j + 1) then 1 else 0) * 2 ^ j

def outN (ρ ρ' : ℕ) : ℕ :=
  ∑ j ∈ range w, (if pN (bit ρ j) (bit ρ (j + 1)) (bit ρ' j) (bit ρ' (j + 1)) then 1 else 0) * 2 ^ j

def orL (l : List ℕ) : ℕ := l.foldr (· ||| ·) 0

theorem testBit_orL (l : List ℕ) (i : ℕ) :
    (orL l).testBit i = true ↔ ∃ x ∈ l, x.testBit i = true := by
  induction l with
  | nil => simp [orL]
  | cons x l ih =>
    simp only [orL, List.foldr_cons, Nat.testBit_lor, Bool.or_eq_true, List.mem_cons,
      exists_eq_or_imp] at *
    rw [ih]

/-- Successor mask of the state with code `c` on the letter with code `β`. -/
def SM (c β : ℕ) : ℕ :=
  orL ((List.range (2 ^ (w + 1))).map fun ρ' =>
    if lexN w (c % 2 ^ (w + 1)) ρ' && flagN w (bit (c / 2 ^ (w + 1))) ρ' &&
        outN w pN (c % 2 ^ (w + 1)) ρ' == β
    then 2 ^ (ρ' + 2 ^ (w + 1) * nfN w (bit (c / 2 ^ (w + 1))) ρ') else 0)

def initM : ℕ :=
  orL ((List.range (2 ^ (w + 1))).map fun ρ =>
    if flagN w (fun _ => 1) ρ then 2 ^ (ρ + 2 ^ (w + 1) * nfN w (fun _ => 1) ρ) else 0)

/-- One subset step on masks, reading the successor masks from a table. -/
def dmGo (m β : ℕ) : ℕ → List (List ℕ) → ℕ
  | _, [] => 0
  | i, row :: rest => (if m.testBit i then row.getD β 0 else 0) ||| dmGo m β (i + 1) rest

theorem testBit_dmGo (m β t : ℕ) : ∀ (i : ℕ) (L : List (List ℕ)),
    (dmGo m β i L).testBit t = true ↔ ∃ c, i ≤ c ∧ c < i + L.length ∧ m.testBit c = true ∧
      ((L.getD (c - i) []).getD β 0).testBit t = true
  | i, [] => by simp [dmGo]
  | i, row :: rest => by
    simp only [dmGo, Nat.testBit_lor, Bool.or_eq_true, testBit_dmGo m β t (i + 1) rest,
      List.length_cons]
    constructor
    · rintro (h | ⟨c, h1, h2, h3, h4⟩)
      · by_cases hm : m.testBit i = true
        · rw [if_pos hm] at h
          exact ⟨i, le_rfl, by omega, hm, by simpa using h⟩
        · rw [if_neg hm] at h; simp at h
      · refine ⟨c, by omega, by omega, h3, ?_⟩
        rw [show c - i = (c - (i + 1)) + 1 by omega]
        simpa using h4
    · rintro ⟨c, h1, h2, h3, h4⟩
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        left
        rw [if_pos h3]
        simpa using h4
      · right
        refine ⟨c, by omega, by omega, h3, ?_⟩
        rw [show c - i = (c - (i + 1)) + 1 by omega] at h4
        simpa using h4

def dm (SMT : List (List ℕ)) (m β : ℕ) : ℕ := dmGo m β 0 SMT

/-! Correspondence between the codes and the automaton. -/

theorem bit_dR (ρ : Fin (2 ^ (w + 1))) (j : Fin (w + 1)) : ((dR w ρ j : Fin 2) : ℕ) = bit ρ j := by
  simp [dR, bit, finFunctionFinEquiv_symm_apply_val]

theorem bit_dF (φ : Fin (2 ^ w)) (j : Fin w) : ((dF w φ j : Fin 2) : ℕ) = bit φ j := by
  simp [dF, bit, finFunctionFinEquiv_symm_apply_val]

theorem cd_mod (q : Q w) : cd w q % 2 ^ (w + 1) = q.1 := by
  simp [cd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt q.1.2]

theorem cd_div (q : Q w) : cd w q / 2 ^ (w + 1) = q.2 := by
  simp only [cd]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt q.1.2, zero_add]

theorem cd_lt (q : Q w) : cd w q < 2 ^ (w + 1) * 2 ^ w := by
  simp only [cd]
  have h1 := q.1.2
  have h2 := q.2.2
  nlinarith

theorem fin2_eq (x y : Fin 2) : x = y ↔ (x : ℕ) = y := Fin.ext_iff
theorem fin2_le (x y : Fin 2) : x ≤ y ↔ (x : ℕ) ≤ y := Fin.le_def

theorem lexN_iff (ρ ρ' : Fin (2 ^ (w + 1))) : lexN w ρ ρ' = true ↔ lexOK (dR w ρ) (dR w ρ') := by
  simp only [lexN, decide_eq_true_eq, lexOK, fin2_eq, fin2_le, bit_dR]
  constructor
  · intro h i hi
    exact h i.1 i.2 (fun i' hi' => hi ⟨i', by omega⟩ hi')
  · intro h i hi hpre
    exact h ⟨i, hi⟩ (fun i' hi' => hpre i'.1 hi')

theorem flagN_iff (e : Fin w → Fin 2) (eb : ℕ → ℕ) (he : ∀ j : Fin w, (e j : ℕ) = eb j)
    (ρ' : Fin (2 ^ (w + 1))) : flagN w eb ρ' = true ↔ flagOK w e (dR w ρ') := by
  simp only [flagN, decide_eq_true_eq, flagOK, fin2_le, bit_dR, Fin.val_castSucc, Fin.val_succ]
  constructor
  · intro h j hj
    exact h j.1 j.2 (by rw [← he, hj]; rfl)
  · intro h j hj hb
    exact h ⟨j, hj⟩ (by rw [fin2_eq]; rw [he]; exact hb)

theorem sum_code (f : Fin w → Fin 2) (g : ℕ → ℕ) (hg : ∀ j : Fin w, (f j : ℕ) = g j) :
    ∑ j ∈ range w, g j * 2 ^ j = (finFunctionFinEquiv f : ℕ) := by
  rw [finFunctionFinEquiv_apply, ← Fin.sum_univ_eq_sum_range (fun j => g j * 2 ^ j)]
  exact Finset.sum_congr rfl (fun j _ => by rw [hg])

theorem nfN_eq (e : Fin w → Fin 2) (eb : ℕ → ℕ) (he : ∀ j : Fin w, (e j : ℕ) = eb j)
    (ρ' : Fin (2 ^ (w + 1))) : nfN w eb ρ' = (finFunctionFinEquiv (nfF w e (dR w ρ')) : ℕ) := by
  apply sum_code
  intro j
  simp only [nfF, fin2_eq, bit_dR, Fin.val_castSucc, Fin.val_succ, ← he]
  split_ifs <;> simp_all

theorem outN_eq (ρ ρ' : Fin (2 ^ (w + 1))) :
    outN w pN ρ ρ' = (finFunctionFinEquiv (outL w pN (dR w ρ) (dR w ρ')) : ℕ) := by
  apply sum_code
  intro j
  simp only [outL, bit_dR, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

theorem cd_eq_iff (q : Q w) (x y : ℕ) (hx : x < 2 ^ (w + 1)) :
    x + 2 ^ (w + 1) * y = cd w q ↔ (q.1 : ℕ) = x ∧ (q.2 : ℕ) = y := by
  constructor
  · intro h
    constructor
    · rw [← cd_mod, ← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    · rw [← cd_div, ← h, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
  · rintro ⟨h1, h2⟩
    simp only [cd, h1, h2]

theorem testBit_orL_pow (g : ℕ → Bool) (y : ℕ → ℕ) (q : Q w) :
    (orL ((List.range (2 ^ (w + 1))).map fun ρ =>
      if g ρ then 2 ^ (ρ + 2 ^ (w + 1) * y ρ) else 0)).testBit (cd w q) = true ↔
      g q.1 = true ∧ (q.2 : ℕ) = y q.1 := by
  simp only [testBit_orL, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨x, ⟨ρ, hρ, rfl⟩, hx⟩
    split_ifs at hx with hc
    · rw [Nat.testBit_two_pow, decide_eq_true_eq, cd_eq_iff w q _ _ hρ] at hx
      rw [hx.1]
      exact ⟨hc, hx.2⟩
    · simp at hx
  · rintro ⟨h1, h2⟩
    refine ⟨_, ⟨q.1, q.1.2, rfl⟩, ?_⟩
    rw [if_pos h1, Nat.testBit_two_pow, decide_eq_true_eq, cd_eq_iff w q _ _ q.1.2]
    exact ⟨rfl, h2⟩

theorem testBit_SM (c β : ℕ) (c' : Q w) :
    (SM w pN c β).testBit (cd w c') = true ↔
      lexN w (c % 2 ^ (w + 1)) c'.1 = true ∧ flagN w (bit (c / 2 ^ (w + 1))) c'.1 = true ∧
        outN w pN (c % 2 ^ (w + 1)) c'.1 = β ∧ (c'.2 : ℕ) = nfN w (bit (c / 2 ^ (w + 1))) c'.1 := by
  rw [SM, testBit_orL_pow]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem decode (c : ℕ) (hc : c < 2 ^ (w + 1) * 2 ^ w) :
    ∃ q : Q w, cd w q = c := by
  refine ⟨(⟨c % 2 ^ (w + 1), Nat.mod_lt _ (by positivity)⟩,
    ⟨c / 2 ^ (w + 1), Nat.div_lt_of_lt_mul hc⟩), ?_⟩
  simp [cd, Nat.mod_add_div]

theorem T_iff (q : Q w) (b : Fin w → Fin 2) (q' : Q w) :
    T w pN q b q' ↔ lexN w (cd w q % 2 ^ (w + 1)) q'.1 = true ∧
      flagN w (bit (cd w q / 2 ^ (w + 1))) q'.1 = true ∧
      outN w pN (cd w q % 2 ^ (w + 1)) q'.1 = (finFunctionFinEquiv b : ℕ) ∧
      (q'.2 : ℕ) = nfN w (bit (cd w q / 2 ^ (w + 1))) q'.1 := by
  rw [cd_mod, cd_div, lexN_iff, flagN_iff w (dF w q.2) _ (bit_dF w q.2),
    nfN_eq w (dF w q.2) _ (bit_dF w q.2), outN_eq]
  simp only [T, ← Fin.ext_iff, (finFunctionFinEquiv).injective.eq_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h4.symm, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h4, h3.symm⟩

open Classical in
theorem FS_initM : FS w (initM w) = univ.filter (Init w) := by
  ext q'
  rw [FS, Finset.mem_filter, Finset.mem_filter, initM, testBit_orL_pow]
  simp only [Finset.mem_univ, true_and, Init]
  rw [flagN_iff w (fun _ => 1) (fun _ => 1) (fun _ => rfl),
    nfN_eq w (fun _ => 1) (fun _ => 1) (fun _ => rfl), Fin.ext_iff]

/-- The subset step on masks agrees with the automaton, given a correct table. -/
theorem δ_FS (SMT : List (List ℕ)) (hlen : SMT.length = 2 ^ (w + 1) * 2 ^ w)
    (hS : ∀ c < 2 ^ (w + 1) * 2 ^ w, ∀ β < 2 ^ w, (SMT.getD c []).getD β 0 = SM w pN c β)
    (m : ℕ) (b : Fin w → Fin 2) :
    δ w pN (FS w m) b = FS w (dm SMT m (finFunctionFinEquiv b)) := by
  ext q'
  rw [mem_δ]
  simp only [FS, Finset.mem_filter, Finset.mem_univ, true_and, dm, testBit_dmGo, zero_add, Nat.sub_zero,
    hlen, zero_le]
  constructor
  · rintro ⟨q, hq, hT⟩
    refine ⟨cd w q, cd_lt w q, hq, ?_⟩
    rw [hS _ (cd_lt w q) _ (finFunctionFinEquiv b).2, testBit_SM]
    exact (T_iff w pN q b q').mp hT
  · rintro ⟨c, hc, hm, hb⟩
    obtain ⟨q, rfl⟩ := decode w c hc
    rw [hS _ hc _ (finFunctionFinEquiv b).2, testBit_SM] at hb
    exact ⟨q, hm, (T_iff w pN q b q').mpr hb⟩

theorem FS_nonempty (m : ℕ) :
    (FS w m).Nonempty ↔ ∃ c < 2 ^ (w + 1) * 2 ^ w, m.testBit c = true := by
  constructor
  · rintro ⟨q, hq⟩
    simp only [FS, mem_filter, mem_univ, true_and] at hq
    exact ⟨cd w q, cd_lt w q, hq⟩
  · rintro ⟨c, hc, hm⟩
    obtain ⟨q, rfl⟩ := decode w c hc
    exact ⟨q, by simp [FS, hm]⟩

end Code

/-! ### Generic part: counts from the subset automaton tables -/

section Tables

variable (w : ℕ) (pN : ℕ → ℕ → ℕ → ℕ → Bool) (SMT : List (List ℕ)) (Rm : List ℕ)
  (NX : List (List ℕ)) (VT : List (List ℕ))

noncomputable def u (k d : ℕ) : ℕ := V w pN k (FS w (Rm.getD d 0))

variable {w pN SMT Rm NX VT}

theorem u_succ (hlen : SMT.length = 2 ^ (w + 1) * 2 ^ w)
    (hS : ∀ c < 2 ^ (w + 1) * 2 ^ w, ∀ β < 2 ^ w, (SMT.getD c []).getD β 0 = SM w pN c β)
    (hNX : ∀ d < Rm.length, ∀ β < 2 ^ w, (NX.getD d []).getD β 0 < Rm.length ∧
      dm SMT (Rm.getD d 0) β = Rm.getD ((NX.getD d []).getD β 0) 0)
    (k d : ℕ) (hd : d < Rm.length) :
    u w pN Rm (k + 1) d = ∑ β ∈ range (2 ^ w), u w pN Rm k ((NX.getD d []).getD β 0) := by
  simp only [u]
  rw [V_succ]
  simp_rw [δ_FS w pN SMT hlen hS]
  have : ∀ b : Fin w → Fin 2, V w pN k (FS w (dm SMT (Rm.getD d 0) (finFunctionFinEquiv b))) =
      (fun β : Fin (2 ^ w) => V w pN k (FS w (Rm.getD ((NX.getD d []).getD β 0) 0)))
        (finFunctionFinEquiv b) := fun b => by
    simp only
    rw [(hNX d hd _ (finFunctionFinEquiv b).2).2]
  simp_rw [this]
  rw [Equiv.sum_comp finFunctionFinEquiv
    (fun β : Fin (2 ^ w) => V w pN k (FS w (Rm.getD ((NX.getD d []).getD β 0) 0)))]
  exact Fin.sum_univ_eq_sum_range (fun β => V w pN k (FS w (Rm.getD ((NX.getD d []).getD β 0) 0))) _

theorem u_zero (d : ℕ) : u w pN Rm 0 d =
    if ∃ c < 2 ^ (w + 1) * 2 ^ w, (Rm.getD d 0).testBit c = true then 1 else 0 := by
  simp only [u, V, Fintype.sum_unique]
  exact if_congr (FS_nonempty w _) rfl rfl

theorem u_VT (hlen : SMT.length = 2 ^ (w + 1) * 2 ^ w)
    (hS : ∀ c < 2 ^ (w + 1) * 2 ^ w, ∀ β < 2 ^ w, (SMT.getD c []).getD β 0 = SM w pN c β)
    (hNX : ∀ d < Rm.length, ∀ β < 2 ^ w, (NX.getD d []).getD β 0 < Rm.length ∧
      dm SMT (Rm.getD d 0) β = Rm.getD ((NX.getD d []).getD β 0) 0)
    (hV0 : ∀ d < Rm.length, (VT.getD 0 []).getD d 0 =
      if ∃ c < 2 ^ (w + 1) * 2 ^ w, (Rm.getD d 0).testBit c = true then 1 else 0)
    (hV : ∀ k < VT.length - 1, ∀ d < Rm.length, (VT.getD (k + 1) []).getD d 0 =
      ∑ β ∈ range (2 ^ w), (VT.getD k []).getD ((NX.getD d []).getD β 0) 0) :
    ∀ k < VT.length, ∀ d < Rm.length, u w pN Rm k d = (VT.getD k []).getD d 0 := by
  intro k
  induction k with
  | zero => intro _ d hd; rw [u_zero, hV0 d hd]
  | succ k ih =>
    intro hk d hd
    rw [u_succ hlen hS hNX k d hd, hV k (by omega) d hd]
    exact Finset.sum_congr rfl (fun β hβ => ih (by omega) _ (hNX d hd β (mem_range.mp hβ)).1)

/-- The componentwise annihilator propagates along the automaton. -/
theorem u_annih (hlen : SMT.length = 2 ^ (w + 1) * 2 ^ w)
    (hS : ∀ c < 2 ^ (w + 1) * 2 ^ w, ∀ β < 2 ^ w, (SMT.getD c []).getD β 0 = SM w pN c β)
    (hNX : ∀ d < Rm.length, ∀ β < 2 ^ w, (NX.getD d []).getD β 0 < Rm.length ∧
      dm SMT (Rm.getD d 0) β = Rm.getD ((NX.getD d []).getD β 0) 0)
    (e : List ℤ) (D k0 : ℕ)
    (h0 : ∀ d < Rm.length, ∑ j ∈ range (D + 1), e.getD j 0 * (u w pN Rm (k0 + D - j) d : ℤ) = 0) :
    ∀ k, k0 ≤ k → ∀ d < Rm.length,
      ∑ j ∈ range (D + 1), e.getD j 0 * (u w pN Rm (k + D - j) d : ℤ) = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h0
  | succ k _ ih =>
    intro d hd
    have : ∀ j ∈ range (D + 1), e.getD j 0 * (u w pN Rm (k + 1 + D - j) d : ℤ) =
        ∑ β ∈ range (2 ^ w), e.getD j 0 * (u w pN Rm (k + D - j) ((NX.getD d []).getD β 0) : ℤ) := by
      intro j hj
      rw [show k + 1 + D - j = (k + D - j) + 1 by have := mem_range.mp hj; omega,
        u_succ hlen hS hNX _ d hd, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    exact Finset.sum_eq_zero (fun β hβ => ih _ (hNX d hd β (mem_range.mp hβ)).1)

end Tables

/-! ### Generic part: from the recurrence to the generating function -/

theorem gf_of_rec (f : ℕ → ℚ) (e nm : List ℤ) (D n0 : ℕ) (hnm : nm.length ≤ n0 + 1)
    (hrec : ∀ n, n0 < n → ∑ j ∈ range (D + 1), (e.getD j 0 : ℚ) * (if j ≤ n then f (n - j) else 0) = 0)
    (hsmall : ∀ n ≤ n0, ∑ j ∈ range (D + 1), (e.getD j 0 : ℚ) * (if j ≤ n then f (n - j) else 0) =
      (nm.getD n 0 : ℚ))
    (P N : ℚ⟦X⟧) (hP : P = ∑ j ∈ range (D + 1), C (e.getD j 0 : ℚ) * X ^ j)
    (hN : N = ∑ j ∈ range nm.length, C (nm.getD j 0 : ℚ) * X ^ j) :
    PowerSeries.mk f * P = N := by
  ext n
  have hL : coeff n (PowerSeries.mk f * P) =
      ∑ j ∈ range (D + 1), (e.getD j 0 : ℚ) * (if j ≤ n then f (n - j) else 0) := by
    rw [hP, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show PowerSeries.mk f * (C (e.getD j 0 : ℚ) * X ^ j) =
      C (e.getD j 0 : ℚ) * (PowerSeries.mk f * X ^ j) by ring, coeff_C_mul, coeff_mul_X_pow']
    split_ifs <;> simp [coeff_mk]
  have hR : coeff n N = (nm.getD n 0 : ℚ) := by
    rw [hN, map_sum]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [List.getD_eq_default _ _ (by simpa using h)]; simp
  rw [hL, hR]
  rcases le_or_gt n n0 with hn | hn
  · exact hsmall n hn
  · rw [hrec n hn, List.getD_eq_default _ _ (by omega)]; simp


/-! ### The data of this sequence -/

def pB (x y z t : ℕ) : Bool := x * t != y * z

theorem hblk (x y z t : Fin 2) : blk x y z t ↔ pB x y z t = true := by
  revert x y z t; decide

theorem ind_eq (n : ℕ) (A : Fin (n + 1) → Fin 4 → Fin 2) : ind A = indG 3 pB A := by
  funext i j
  simp only [ind, indG, hblk]

def SMT : List (List ℕ) :=
  [[65535, 0, 0, 0, 0, 0, 0, 0],
  [8738, 34952, 0, 0, 0, 0, 0, 0],
  [1028, 2570, 16448, 41120, 0, 0, 0, 0],
  [2056, 0, 32896, 0, 0, 0, 0, 0],
  [50, 0, 204, 0, 12800, 0, 52224, 0],
  [32, 0, 0, 136, 8192, 0, 0, 34816],
  [64, 130, 0, 40, 16384, 33280, 0, 10240],
  [128, 0, 0, 0, 32768, 0, 0, 0],
  [3854, 0, 0, 0, 61680, 0, 0, 0],
  [512, 2056, 0, 0, 8224, 32896, 0, 0],
  [1024, 2570, 0, 0, 0, 0, 16448, 41120],
  [2048, 0, 0, 0, 0, 0, 32896, 0],
  [12290, 0, 49164, 0, 544, 0, 3264, 0],
  [8192, 0, 0, 32776, 0, 0, 0, 2176],
  [16384, 32770, 0, 8200, 0, 640, 0, 2080],
  [32768, 0, 0, 0, 0, 0, 0, 0],
  [2576958532, 0, 0, 0, 0, 0, 0, 0],
  [0, 2290614272, 0, 0, 0, 0, 0, 0],
  [1028, 134742016, 16448, 2155872256, 0, 0, 0, 0],
  [134742016, 0, 2155872256, 0, 0, 0, 0, 0],
  [1048576, 0, 8912964, 0, 268435456, 0, 2281718784, 0],
  [0, 0, 0, 8912896, 0, 0, 0, 2281701376],
  [64, 8388608, 0, 524288, 16384, 2147483648, 0, 134217728],
  [8388608, 0, 0, 0, 2147483648, 0, 0, 0],
  [151520260, 0, 0, 0, 2425372736, 0, 0, 0],
  [0, 134742016, 0, 0, 0, 2155872256, 0, 0],
  [1024, 134742016, 0, 0, 0, 0, 16448, 2155872256],
  [134217728, 0, 0, 0, 0, 0, 2155872256, 0],
  [268435456, 0, 2148024324, 0, 0, 0, 142607424, 0],
  [0, 0, 0, 2148007936, 0, 0, 0, 142606336],
  [16384, 2147483648, 0, 524288, 0, 8388608, 0, 134217728],
  [2147483648, 0, 0, 0, 0, 0, 0, 0],
  [215242286051376, 0, 0, 0, 0, 0, 0, 0],
  [2207613198368, 141287244169216, 0, 0, 0, 0, 0, 0],
  [0, 2207613190144, 70643622084608, 141287244177440, 0, 0, 0, 0],
  [0, 0, 141287244169216, 0, 0, 0, 0, 0],
  [8589934640, 0, 824633720832, 0, 2199023267840, 0, 211106232532992, 0],
  [32, 0, 0, 549755813888, 8192, 0, 0, 140737488355328],
  [274877906944, 558345748480, 0, 32, 70368744177664, 142936511610880, 0, 8192],
  [549755813888, 0, 0, 0, 140737488355328, 0, 0, 0],
  [3307124817920, 0, 0, 0, 211930866266160, 0, 0, 0],
  [2199023255552, 0, 0, 0, 8224, 141287244169216, 0, 0],
  [0, 2207613190144, 0, 0, 0, 0, 70643622084608, 141287244177440],
  [0, 0, 0, 0, 0, 0, 141287244169216, 0],
  [8589946880, 0, 211106232532992, 0, 2199023255584, 0, 824633720832, 0],
  [8192, 0, 0, 140737488355328, 0, 0, 0, 549755813888],
  [70368744177664, 140746078289920, 0, 8192, 0, 2748779069440, 0, 32],
  [140737488355328, 0, 0, 0, 0, 0, 0, 0],
  [9331810546779947008, 0, 0, 0, 0, 0, 0, 0],
  [0, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [0, 0, 70643622084608, 9259400833873739776, 0, 0, 0, 0],
  [0, 0, 9259400833873739776, 0, 0, 0, 0, 0],
  [1048576, 0, 36029071896870912, 0, 268435456, 0, 9223442405598953472, 0],
  [0, 0, 0, 36028797018963968, 0, 0, 0, 9223372036854775808],
  [274877906944, 36028797018963968, 0, 0, 70368744177664, 9223372036854775808, 0, 0],
  [36028797018963968, 0, 0, 0, 9223372036854775808, 0, 0, 0],
  [72057594037927936, 0, 0, 0, 9259471477765308416, 0, 0, 0],
  [0, 0, 0, 0, 0, 9259400833873739776, 0, 0],
  [0, 0, 0, 0, 0, 0, 70643622084608, 9259400833873739776],
  [0, 0, 0, 0, 0, 0, 9259400833873739776, 0],
  [268435456, 0, 9223442405598953472, 0, 0, 0, 36029071896870912, 0],
  [0, 0, 0, 9223372036854775808, 0, 0, 0, 36028797018963968],
  [70368744177664, 9223372036854775808, 0, 0, 0, 36028797018963968, 0, 0],
  [9223372036854775808, 0, 0, 0, 0, 0, 0, 0],
  [1133644657049820494565120, 0, 0, 0, 0, 0, 0, 0],
  [151152620939976065942016, 604610483759904263768064, 0, 0, 0, 0, 0, 0],
  [73786976294838207488, 184467440737095518720, 302231454903657293676544, 755578637259143234191360, 0, 0, 0, 0],
  [147573952589676414976, 0, 604462909807314587353088, 0, 0, 0, 0, 0],
  [36893488147419103232, 0, 221360928884514619392, 0, 226673591177742970257920, 0, 906694364710971881032704, 0],
  [0, 0, 0, 147573952589676412928, 151115727451828646838272, 0, 0, 604462909807314587355136],
  [0, 36893488147419103232, 0, 147573952589676412928, 302231454903657293676544, 604462909807314587353600, 0, 151115727451828646840320],
  [0, 0, 0, 0, 604462909807314587353088, 0, 0, 0],
  [258254417031933726464, 0, 0, 0, 1133367955888714851287040, 0, 0, 0],
  [512, 147573952589676414976, 0, 0, 151115727451828646838272, 604462909807314587353088, 0, 0],
  [1024, 184467440737095518720, 0, 0, 0, 0, 302231454903657293676544, 755578637259143234191360],
  [2048, 0, 0, 0, 0, 0, 604462909807314587353088, 0],
  [226710484665890389360640, 0, 906915725639856395649024, 0, 512, 0, 3072, 0],
  [151115727451828646838272, 0, 0, 604610483759904263766016, 0, 0, 0, 2048],
  [302231454903657293676544, 604499803295462006456320, 0, 151263301404418323251200, 0, 512, 0, 2048],
  [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
  [44577024051892101511223706624, 0, 0, 0, 0, 0, 0, 0],
  [0, 39623752663689085830303842304, 0, 0, 0, 0, 0, 0],
  [73786976294838207488, 9671406556917033531867136, 302231454903657293676544, 39614081257132168796771975168, 0, 0, 0, 0],
  [9671406556917033531867136, 0, 39614081257132168796771975168, 0, 0, 0, 0, 0],
  [0, 0, 9671480343893328235855872, 0, 4951760157141521099596496896, 0, 39614383488587072454199870464, 0],
  [0, 0, 0, 9671406556917033397649408, 0, 0, 0, 39614081257132168796906192896],
  [0, 0, 0, 9671406556917033397649408, 302231454903657293676544, 39614081257132168796771975168, 0, 134217728],
  [0, 0, 0, 0, 39614081257132168796771975168, 0, 0, 0],
  [9671480343893328386851840, 0, 0, 0, 44566143645728593553662148608, 0, 0, 0],
  [0, 9671406556917033531867136, 0, 0, 0, 39614081257132168796771975168, 0, 0],
  [1024, 9671406556917033531867136, 0, 0, 0, 0, 302231454903657293676544, 39614081257132168796771975168],
  [134217728, 0, 0, 0, 0, 0, 39614081257132168796771975168, 0],
  [4951760157141521099596496896, 0, 39624054968930965782301507584, 0, 0, 0, 134218752, 0],
  [0, 0, 0, 39623752663689085830169624576, 0, 0, 0, 134217728],
  [302231454903657293676544, 39614081257132168796771975168, 0, 9671406556917033397649408, 0, 0, 0, 134217728],
  [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
  [3894460328615337105591694383906816, 0, 0, 0, 0, 0, 0, 0],
  [158456476144256129214757994496, 2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0],
  [0, 158456325028528677386111156224, 1298074214633706907132624082305024, 2596148429418529541717076811448320, 0, 0, 0, 0],
  [0, 0, 2596148429267413814265248164610048, 0, 0, 0, 0, 0],
  [158456325028528675187087900672, 0, 0, 0, 226673591179941993512960, 0, 3894222643901120721397872246915072, 0],
  [0, 0, 0, 0, 151115727451828646838272, 0, 0, 2596148429267413814265248164610048],
  [0, 158456325028528675187087900672, 0, 0, 1298074214633706907132624082305024, 2596148429267413814267447187865600, 0, 151115727451828646838272],
  [0, 0, 0, 0, 2596148429267413814265248164610048, 0, 0, 0],
  [158456325028528678485622784000, 0, 0, 0, 3894222644127794312575615217172480, 0, 0, 0],
  [2199023255552, 0, 0, 0, 151115727451828646838272, 2596148429267413814265248164610048, 0, 0],
  [0, 158456325028528677386111156224, 0, 0, 0, 0, 1298074214633706907132624082305024, 2596148429418529541717076811448320],
  [0, 0, 0, 0, 0, 0, 2596148429267413814265248164610048, 0],
  [158456551702119852930058158080, 0, 3894222643901120721397872246915072, 0, 2199023255552, 0, 0, 0],
  [151115727451828646838272, 0, 0, 2596148429267413814265248164610048, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 2596306885592442342940435252510720, 0, 151115727451828646838272, 0, 2199023255552, 0, 0],
  [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
  [170147673836494160423436545529930055680, 0, 0, 0, 0, 0, 0, 0],
  [0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [0, 0, 1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0, 0, 0],
  [0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 4951760157141521099596496896, 0, 170142481534683865438594436339966410752, 0],
  [0, 0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728],
  [0, 0, 0, 0, 1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0],
  [0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0],
  [72057594037927936, 0, 0, 0, 170142481539635625595735957439562907648, 0, 0, 0],
  [0, 0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0],
  [0, 0, 0, 0, 0, 0, 1298074214633706907132624082305024, 170141183460469231731687303715884105728],
  [0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728, 0],
  [4951760157141521099596496896, 0, 170142481534683865438594436339966410752, 0, 0, 0, 0, 0],
  [0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0]]

def Rm : List ℕ :=
  [170147673836494160423436545529930055680, 2596306885592442342940435252510720, 39624054968930965782301507584, 151115727451828646838272, 9259471477765308416, 2199023255552, 134218752, 0, 2596306885743558070394462922604544, 2596148429267413814265248164610048, 39624054968930965782435726336, 604647377248051682871808, 39614383488587072454065651712, 755726211211732910604288, 512, 2048, 604610483759904263766016, 141295834103808, 2156412996, 8224, 9223442405867388928, 143486267424768, 2290107456, 141287244169216, 2570, 2155888704, 41120, 604647377248051682871818, 43168, 755763104699880329710080, 604610483759904263768072, 604462909807314587353088, 32896, 604499803295462006456320, 151263301404418323251200, 755726211211732910606336, 2056, 604610483759904263768064, 143494857367584, 140737488355328, 2290631748, 35466, 41128, 2147500032, 33408, 10272, 32904, 8192, 34944, 140746078289920, 2148024324, 2748779069440, 142607424, 32, 140737488363552, 8232, 10794, 34952, 32898, 40960, 755763104699880329718314, 604610483759904263800968, 604462909807314587385984, 32768, 755615530747290653295104, 151263301404418323253248, 43690, 40992, 43176, 32770, 8200, 640, 2080, 32776, 2176, 142945101553696, 2282243076, 35338, 2698, 40, 33280, 136, 34816, 10280, 41634, 604610483759904263798920, 41506, 10248, 34824, 43562, 10922, 2088, 2184]

def NX : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
  [8, 9, 7, 7, 7, 7, 7, 7],
  [10, 11, 12, 13, 7, 14, 7, 15],
  [3, 7, 7, 16, 7, 7, 7, 15],
  [4, 17, 18, 19, 20, 21, 22, 19],
  [5, 7, 7, 7, 19, 23, 7, 7],
  [6, 24, 7, 7, 7, 7, 25, 26],
  [7, 7, 7, 7, 7, 7, 7, 7],
  [8, 9, 7, 16, 19, 23, 7, 15],
  [9, 7, 7, 7, 7, 7, 7, 7],
  [10, 27, 12, 13, 7, 14, 25, 28],
  [29, 30, 31, 7, 19, 32, 32, 7],
  [12, 33, 7, 34, 7, 14, 7, 15],
  [35, 7, 31, 16, 7, 7, 7, 15],
  [14, 36, 7, 7, 19, 32, 7, 7],
  [15, 7, 7, 7, 7, 7, 32, 7],
  [37, 7, 31, 7, 7, 7, 7, 7],
  [38, 23, 7, 7, 39, 7, 7, 7],
  [40, 41, 25, 42, 43, 44, 7, 45],
  [19, 7, 7, 46, 47, 7, 7, 48],
  [20, 49, 50, 47, 7, 51, 52, 53],
  [21, 7, 7, 7, 54, 23, 7, 7],
  [22, 41, 7, 55, 43, 44, 25, 28],
  [23, 7, 7, 7, 39, 7, 7, 7],
  [56, 57, 32, 7, 19, 32, 32, 7],
  [25, 58, 7, 55, 43, 44, 7, 45],
  [26, 7, 7, 46, 59, 7, 7, 48],
  [60, 61, 62, 7, 19, 32, 32, 7],
  [28, 7, 7, 46, 59, 7, 32, 48],
  [29, 30, 31, 16, 19, 32, 32, 15],
  [30, 7, 62, 7, 7, 7, 32, 7],
  [31, 7, 7, 7, 7, 7, 7, 7],
  [32, 7, 7, 7, 63, 7, 7, 7],
  [64, 37, 7, 7, 7, 7, 7, 7],
  [65, 7, 31, 16, 7, 7, 7, 15],
  [35, 7, 31, 16, 7, 7, 32, 15],
  [36, 7, 32, 7, 7, 7, 32, 7],
  [37, 7, 31, 7, 7, 7, 32, 7],
  [38, 23, 7, 46, 54, 23, 7, 48],
  [39, 7, 7, 7, 7, 7, 7, 7],
  [40, 41, 25, 42, 43, 44, 25, 28],
  [66, 57, 32, 7, 67, 32, 32, 7],
  [68, 7, 32, 46, 59, 7, 7, 48],
  [43, 69, 7, 70, 7, 71, 7, 72],
  [44, 36, 7, 7, 67, 32, 7, 7],
  [45, 7, 7, 46, 47, 7, 32, 48],
  [57, 7, 32, 7, 63, 7, 7, 7],
  [47, 7, 7, 73, 7, 7, 7, 74],
  [48, 7, 7, 7, 63, 7, 32, 7],
  [75, 23, 7, 7, 7, 7, 7, 7],
  [76, 77, 25, 42, 7, 71, 7, 72],
  [51, 7, 7, 7, 54, 23, 7, 7],
  [52, 78, 7, 79, 43, 80, 25, 28],
  [53, 7, 7, 81, 47, 7, 7, 82],
  [54, 7, 7, 46, 47, 7, 7, 48],
  [83, 7, 32, 46, 47, 7, 7, 48],
  [56, 57, 32, 46, 19, 32, 32, 48],
  [57, 7, 32, 7, 63, 7, 32, 7],
  [84, 57, 7, 7, 63, 7, 7, 7],
  [59, 7, 7, 73, 7, 7, 7, 74],
  [60, 61, 62, 85, 19, 32, 32, 48],
  [61, 7, 62, 7, 63, 7, 32, 7],
  [62, 7, 7, 7, 63, 7, 7, 7],
  [63, 7, 7, 7, 7, 7, 7, 7],
  [64, 30, 7, 16, 19, 32, 7, 15],
  [65, 7, 31, 16, 7, 7, 32, 15],
  [66, 57, 32, 46, 67, 32, 32, 48],
  [67, 7, 7, 46, 47, 7, 7, 48],
  [68, 7, 32, 46, 59, 7, 32, 48],
  [86, 57, 7, 7, 7, 7, 7, 7],
  [87, 7, 32, 73, 7, 7, 7, 74],
  [71, 36, 7, 7, 67, 32, 7, 7],
  [72, 7, 7, 81, 47, 7, 32, 82],
  [88, 7, 32, 7, 7, 7, 7, 7],
  [74, 7, 7, 7, 63, 7, 32, 7],
  [75, 23, 7, 46, 19, 23, 7, 48],
  [76, 77, 25, 42, 7, 71, 25, 28],
  [89, 57, 32, 7, 19, 32, 32, 7],
  [90, 57, 32, 7, 67, 32, 32, 7],
  [91, 7, 32, 81, 47, 7, 7, 82],
  [80, 36, 7, 7, 19, 32, 7, 7],
  [92, 7, 32, 7, 63, 7, 7, 7],
  [82, 7, 7, 7, 7, 7, 32, 7],
  [83, 7, 32, 46, 47, 7, 32, 48],
  [84, 57, 7, 46, 67, 32, 7, 48],
  [61, 7, 62, 7, 63, 7, 7, 7],
  [86, 57, 7, 46, 19, 32, 7, 48],
  [87, 7, 32, 73, 7, 7, 32, 74],
  [88, 7, 32, 7, 7, 7, 32, 7],
  [89, 57, 32, 46, 19, 32, 32, 48],
  [90, 57, 32, 46, 67, 32, 32, 48],
  [91, 7, 32, 81, 47, 7, 32, 82],
  [92, 7, 32, 7, 63, 7, 32, 7]]

def VT : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [7, 2, 6, 3, 8, 3, 4, 0, 6, 1, 7, 6, 5, 4, 4, 2, 2, 3, 7, 4, 7, 3, 7, 2, 6, 6, 4, 6, 5, 8, 3, 1, 2, 2, 4, 5, 3, 3, 6, 1, 8, 6, 5, 5, 4, 5, 3, 3, 3, 2, 6, 3, 7, 4, 4, 5, 8, 4, 3, 3, 8, 4, 2, 1, 6, 5, 8, 4, 6, 2, 4, 4, 5, 2, 3, 6, 7, 6, 6, 5, 4, 3, 2, 6, 6, 3, 6, 5, 3, 8, 8, 6, 4],
  [33, 7, 28, 7, 43, 9, 20, 0, 17, 1, 37, 20, 17, 10, 13, 4, 4, 9, 39, 13, 32, 9, 38, 3, 22, 28, 13, 22, 16, 24, 7, 1, 3, 9, 10, 12, 7, 6, 20, 1, 45, 22, 17, 20, 13, 16, 7, 8, 6, 8, 33, 9, 38, 12, 13, 17, 28, 9, 11, 8, 28, 9, 3, 1, 19, 12, 28, 13, 19, 10, 12, 13, 15, 5, 6, 20, 39, 22, 22, 16, 13, 7, 4, 19, 22, 7, 22, 14, 7, 28, 28, 18, 9],
  [147, 18, 101, 15, 196, 25, 83, 0, 42, 1, 143, 51, 53, 21, 36, 7, 7, 24, 161, 34, 140, 25, 154, 4, 59, 105, 34, 59, 40, 59, 13, 1, 4, 25, 21, 24, 13, 10, 52, 1, 189, 59, 43, 70, 36, 40, 13, 19, 10, 23, 134, 25, 153, 31, 34, 43, 72, 16, 32, 19, 72, 16, 4, 1, 50, 24, 72, 34, 46, 31, 28, 36, 37, 10, 10, 52, 163, 59, 59, 40, 36, 13, 7, 46, 60, 13, 60, 31, 13, 72, 72, 43, 16],
  [585, 43, 311, 29, 768, 63, 281, 0, 95, 1, 457, 115, 142, 39, 87, 11, 11, 57, 542, 76, 525, 63, 507, 5, 134, 326, 76, 134, 86, 129, 21, 1, 5, 60, 39, 43, 21, 15, 117, 1, 647, 134, 92, 202, 87, 86, 21, 39, 15, 56, 443, 63, 503, 70, 76, 92, 157, 25, 77, 39, 157, 25, 5, 1, 115, 43, 157, 76, 96, 76, 55, 87, 80, 17, 15, 117, 551, 134, 134, 86, 87, 21, 11, 96, 137, 21, 137, 59, 21, 157, 157, 90, 25],
  [2080, 96, 851, 51, 2614, 144, 817, 0, 199, 1, 1271, 237, 339, 66, 189, 16, 16, 123, 1574, 151, 1699, 144, 1434, 6, 273, 870, 151, 273, 166, 259, 31, 1, 6, 130, 66, 71, 31, 21, 239, 1, 1900, 273, 176, 500, 189, 166, 31, 71, 21, 122, 1270, 144, 1424, 141, 151, 176, 309, 36, 163, 71, 309, 36, 6, 1, 239, 71, 309, 151, 181, 162, 96, 189, 156, 26, 21, 239, 1602, 273, 273, 166, 189, 31, 16, 181, 279, 31, 279, 101, 31, 309, 309, 171, 36],
  [6653, 200, 2118, 83, 7890, 301, 2111, 0, 389, 1, 3174, 454, 740, 104, 377, 22, 22, 246, 4074, 274, 4871, 301, 3608, 7, 514, 2064, 274, 514, 295, 486, 43, 1, 7, 260, 104, 110, 43, 28, 454, 1, 4944, 514, 310, 1103, 377, 295, 43, 118, 28, 245, 3266, 301, 3588, 259, 274, 310, 566, 49, 316, 118, 566, 49, 7, 1, 459, 110, 566, 274, 316, 315, 154, 377, 280, 37, 28, 454, 4146, 514, 514, 295, 377, 43, 22, 316, 524, 43, 524, 160, 43, 566, 566, 301, 49],
  [19356, 390, 4871, 127, 21538, 582, 4963, 0, 715, 1, 7268, 818, 1503, 155, 701, 29, 29, 462, 9607, 463, 12648, 582, 8271, 8, 910, 4465, 463, 910, 491, 862, 57, 1, 8, 487, 155, 162, 57, 36, 813, 1, 11671, 910, 512, 2229, 701, 491, 57, 183, 36, 461, 7691, 582, 8236, 442, 463, 512, 981, 64, 574, 183, 981, 64, 8, 1, 827, 162, 981, 463, 519, 573, 232, 701, 470, 50, 36, 813, 9770, 910, 910, 491, 701, 57, 29, 519, 925, 57, 925, 239, 57, 981, 981, 498, 64],
  [51827, 716, 10474, 185, 54034, 1053, 10801, 0, 1245, 1, 15493, 1399, 2875, 221, 1229, 37, 37, 822, 20979, 739, 30243, 1053, 17579, 9, 1532, 8972, 739, 1532, 775, 1457, 73, 1, 9, 863, 221, 229, 73, 45, 1385, 1, 25444, 1532, 803, 4205, 1229, 775, 73, 269, 45, 821, 16828, 1053, 17523, 711, 739, 803, 1625, 81, 990, 269, 1625, 81, 9, 1, 1413, 229, 1625, 739, 811, 989, 333, 1229, 747, 65, 45, 1385, 21314, 1532, 1532, 775, 1229, 73, 37, 811, 1553, 73, 1553, 341, 73, 1625, 1625, 783, 81],
  [129090, 1246, 21254, 259, 126188, 1801, 22044, 0, 2068, 1, 31097, 2288, 5225, 304, 2050, 46, 46, 1395, 42960, 1126, 67448, 1801, 35095, 10, 2472, 16974, 1126, 2472, 1171, 2362, 91, 1, 10, 1458, 304, 313, 91, 55, 2260, 1, 51932, 2472, 1207, 7503, 2050, 1171, 91, 379, 55, 1394, 34597, 1801, 35011, 1090, 1126, 1207, 2590, 100, 1635, 379, 2590, 100, 10, 1, 2308, 313, 2590, 1126, 1216, 1634, 460, 2050, 1135, 82, 55, 2260, 43597, 2472, 2472, 1171, 2050, 91, 46, 1216, 2500, 91, 2500, 469, 91, 2590, 2590, 1180, 100],
  [301882, 2069, 41010, 351, 277139, 2937, 42616, 0, 3297, 1, 59293, 3600, 9083, 406, 3277, 56, 56, 2271, 83309, 1651, 141720, 2937, 66472, 11, 3846, 30540, 1651, 3846, 1706, 3692, 111, 1, 11, 2363, 406, 416, 111, 66, 3552, 1, 100283, 3846, 1751, 12782, 3277, 1706, 111, 516, 66, 2270, 67435, 2937, 66352, 1606, 1651, 1751, 3992, 121, 2601, 516, 3992, 121, 11, 1, 3627, 416, 3992, 1651, 1761, 2600, 616, 3277, 1661, 101, 66, 3552, 84445, 3846, 3846, 1706, 3277, 111, 56, 1761, 3882, 111, 3882, 626, 111, 3992, 3992, 1716, 121],
  [668004, 3298, 75715, 463, 577150, 4599, 78653, 0, 5072, 1, 108151, 5477, 15185, 529, 5050, 67, 67, 3564, 154185, 2344, 282836, 4599, 120374, 12, 5797, 52657, 2344, 5797, 2410, 5589, 133, 1, 12, 3693, 529, 540, 133, 78, 5402, 1, 184725, 5797, 2465, 20936, 5050, 2410, 133, 683, 78, 3563, 125520, 4599, 120209, 2289, 2344, 2465, 5974, 144, 4004, 683, 5974, 144, 12, 1, 5512, 540, 5974, 2344, 2476, 4003, 804, 5050, 2355, 122, 78, 5402, 156105, 5797, 5797, 2410, 5050, 133, 67, 2476, 5842, 133, 5842, 815, 133, 5974, 5974, 2421, 144],
  [1407882, 5073, 134459, 597, 1147396, 6955, 139451, 0, 7563, 1, 189779, 8091, 24524, 675, 7539, 79, 79, 5415, 274040, 3238, 539699, 6955, 209689, 13, 8498, 87522, 3238, 8498, 3316, 8225, 157, 1, 13, 5590, 675, 687, 157, 91, 7981, 1, 326697, 8498, 3382, 33148, 7539, 3316, 157, 883, 91, 5414, 224429, 6955, 209469, 3172, 3238, 3382, 8709, 169, 5987, 883, 8709, 169, 13, 1, 8135, 687, 8709, 3238, 3394, 5986, 1027, 7539, 3250, 145, 91, 7981, 277141, 8498, 8498, 3316, 7539, 157, 79, 3394, 8553, 157, 8553, 1039, 157, 8709, 8709, 3328, 169],
  [2841813, 7564, 230687, 755, 2189670, 10206, 238709, 0, 10973, 1, 321853, 11647, 38407, 846, 10947, 92, 92, 7995, 470102, 4369, 990021, 10206, 353094, 14, 12155, 140894, 4369, 12155, 4460, 11805, 183, 1, 14, 8226, 846, 859, 183, 105, 11493, 1, 557624, 12155, 4538, 50950, 10947, 4460, 183, 1119, 105, 7994, 387332, 10206, 352808, 4291, 4369, 4538, 12403, 196, 8723, 1119, 12403, 196, 14, 1, 11701, 859, 12403, 4369, 4551, 8722, 1288, 10947, 4382, 170, 105, 11493, 474920, 12155, 12155, 4460, 10947, 183, 92, 4551, 12221, 183, 12221, 1301, 183, 12403, 12403, 4473, 196],
  [5519404, 10974, 383792, 939, 4029826, 14589, 396127, 0, 15541, 1, 529562, 16386, 58518, 1044, 15513, 106, 106, 11508, 781568, 5776, 1753771, 14589, 577038, 15, 17010, 220512, 5776, 17010, 5881, 16570, 211, 1, 15, 11806, 1044, 1058, 211, 120, 16178, 1, 922462, 17010, 5972, 76289, 15513, 5881, 211, 1394, 120, 11507, 647836, 14589, 576674, 5685, 5776, 5972, 17298, 225, 12418, 1394, 17298, 225, 15, 1, 16451, 1058, 17298, 5776, 5986, 12417, 1590, 15513, 5790, 197, 120, 16178, 788808, 17010, 17010, 5881, 15513, 211, 106, 5986, 17088, 211, 17088, 1604, 211, 17298, 17298, 5895, 225]]

def ce : List ℤ := [1, -12, 66, -220, 495, -792, 924, -792, 495, -220, 66, -12, 1]

def nm : List ℤ := [0, 7, -51, 213, -541, 967, -1246, 1197, -848, 439, -150, 31]

def aT (n : ℕ) : ℕ := (VT.getD n []).getD 0 0

theorem hlen : SMT.length = 2 ^ (3 + 1) * 2 ^ 3 := by decide +kernel

theorem hRmlen : Rm.length = 93 := by decide +kernel

theorem hVTlen : VT.length = 15 := by decide +kernel

theorem hS : ∀ c < 2 ^ (3 + 1) * 2 ^ 3, ∀ β < 2 ^ 3, (SMT.getD c []).getD β 0 = SM 3 pB c β := by
  decide +kernel

theorem hR0 : Rm.getD 0 0 = initM 3 := by decide +kernel

theorem hNX : ∀ d < Rm.length, ∀ β < 2 ^ 3, (NX.getD d []).getD β 0 < Rm.length ∧
    dm SMT (Rm.getD d 0) β = Rm.getD ((NX.getD d []).getD β 0) 0 := by
  decide +kernel

theorem hV0 : ∀ d < Rm.length, (VT.getD 0 []).getD d 0 =
    if ∃ c < 2 ^ (3 + 1) * 2 ^ 3, (Rm.getD d 0).testBit c = true then 1 else 0 := by
  decide +kernel

theorem hV : ∀ k < VT.length - 1, ∀ d < Rm.length, (VT.getD (k + 1) []).getD d 0 =
    ∑ β ∈ range (2 ^ 3), (VT.getD k []).getD ((NX.getD d []).getD β 0) 0 := by
  decide +kernel

theorem hZ : ∀ d < Rm.length,
    ∑ j ∈ range (12 + 1), ce.getD j 0 * ((VT.getD (2 + 12 - j) []).getD d 0 : ℤ) = 0 := by
  decide +kernel

theorem hsmallrec : ∀ n < 2 + 12, 12 < n →
    ∑ j ∈ range (12 + 1), ce.getD j 0 * (aT (n - j) : ℤ) = 0 := by
  decide +kernel

theorem hsm : ∀ n ≤ 12, ∑ j ∈ range (12 + 1), ce.getD j 0 *
    (if j ≤ n then (if n - j = 0 then 0 else (aT (n - j) : ℤ)) else 0) = nm.getD n 0 := by
  decide +kernel

/-! ### Assembly -/

theorem a_eq_u (n : ℕ) : a n = u 3 pB Rm n 0 := by
  have h : ((univ.filter (fun A : Fin (n + 1) → Fin 4 → Fin 2 => IsSorted A)).image ind) =
      ((univ.filter (fun A : Fin (n + 1) → Fin (3 + 1) → Fin 2 => IsSorted A)).image (indG 3 pB)) := by
    congr 1
    funext A
    exact ind_eq n A
  rw [a, h, card_image_eq, ← FS_initM, ← hR0]
  rfl

theorem a_VT (n : ℕ) (hn : n < 15) : a n = aT n := by
  rw [a_eq_u]
  exact u_VT hlen hS hNX hV0 hV n (by rw [hVTlen]; exact hn) 0 (by rw [hRmlen]; norm_num)

theorem annih (k : ℕ) (hk : 2 ≤ k) :
    ∑ j ∈ range (12 + 1), ce.getD j 0 * (a (k + 12 - j) : ℤ) = 0 := by
  simp only [a_eq_u]
  refine u_annih hlen hS hNX ce 12 2 ?_ k hk 0 (by rw [hRmlen]; norm_num)
  intro d hd
  refine (Finset.sum_congr rfl ?_).trans (hZ d hd)
  intro j hj
  have := mem_range.mp hj
  rw [u_VT hlen hS hNX hV0 hV _ (by rw [hVTlen]; omega) d hd]

theorem rec_all (n : ℕ) (hn : 12 < n) :
    ∑ j ∈ range (12 + 1), ce.getD j 0 * (a (n - j) : ℤ) = 0 := by
  rcases lt_or_ge n (2 + 12) with h | h
  · refine (Finset.sum_congr rfl ?_).trans (hsmallrec n h hn)
    intro j hj
    rw [a_VT _ (by omega)]
  · refine (Finset.sum_congr rfl ?_).trans (annih (n - 12) (by omega))
    intro j hj
    have := mem_range.mp hj
    rw [show n - 12 + 12 - j = n - j by omega]

theorem recurrence (n : ℕ) (hn : 12 < n) : (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) := by
  have h := rec_all n hn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ce, List.getD_cons_zero,
    List.getD_cons_succ, Nat.sub_zero] at h
  linarith

theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 12 =
      X * (7 - 51 * X + 213 * X ^ 2 - 541 * X ^ 3 + 967 * X ^ 4 - 1246 * X ^ 5 + 1197 * X ^ 6 - 848 * X ^ 7 + 439 * X ^ 8 - 150 * X ^ 9 + 31 * X ^ 10) := by
  apply gf_of_rec _ ce nm 12 12 (by decide)
  · intro n hn
    have h := rec_all n hn
    have h' : ∀ j ∈ range (12 + 1), (ce.getD j 0 : ℚ) *
        (if j ≤ n then (if n - j = 0 then (0 : ℚ) else (a (n - j) : ℚ)) else 0) =
        ((ce.getD j 0 * (a (n - j) : ℤ) : ℤ) : ℚ) := by
      intro j hj
      have := mem_range.mp hj
      rw [if_pos (by omega), if_neg (by omega)]
      push_cast; ring
    rw [Finset.sum_congr rfl h', ← Int.cast_sum, h, Int.cast_zero]
  · intro n hn
    have h := hsm n hn
    have h' : ∀ j ∈ range (12 + 1), (ce.getD j 0 : ℚ) *
        (if j ≤ n then (if n - j = 0 then (0 : ℚ) else (a (n - j) : ℚ)) else 0) =
        ((ce.getD j 0 * (if j ≤ n then (if n - j = 0 then 0 else (aT (n - j) : ℤ)) else 0) : ℤ) : ℚ) := by
      intro j hj
      split_ifs with h1 h2
      · simp
      · rw [a_VT _ (by omega)]; push_cast; ring
      · simp
    rw [Finset.sum_congr rfl h', ← Int.cast_sum, h]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, ce, List.getD_cons_zero,
      List.getD_cons_succ]
    simp only [map_neg, map_one, map_ofNat, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
    ring
  · simp only [nm, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_zero, List.getD_cons_succ]
    simp only [map_neg, map_one, map_zero, map_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero,
      Int.cast_ofNat, map_intCast]
    ring

theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 12 =
      X * (7 - 51 * X + 213 * X ^ 2 - 541 * X ^ 3 + 967 * X ^ 4 - 1246 * X ^ 5 + 1197 * X ^ 6 - 848 * X ^ 7 + 439 * X ^ 8 - 150 * X ^ 9 + 31 * X ^ 10) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a227555

theorem OMA.solution : type_of% @OMA.S_oeis_a227555.main :=
  OMA.S_oeis_a227555.conjecture
