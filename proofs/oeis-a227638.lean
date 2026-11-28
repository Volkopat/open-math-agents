import OMAStatements.S_oeis_a227638

/-!
Proof of Barker's conjectures for OEIS A227638. The rows of the larger array are read from the top
by a finite automaton whose state is the current row together with the set of adjacent columns
that are still equal; an indicator array arises exactly when the automaton accepts it. The subset
construction gives a finite deterministic automaton (its states are bit masks), checked in the
kernel; the count of accepted words then satisfies the (1 - x)^10 recurrence componentwise, and
the generating function follows by comparing coefficients.
-/

namespace OMA.S_oeis_a227638

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

def pB (x y z t : ℕ) : Bool := x * t == y * z + 1

theorem hblk (x y z t : Fin 2) : blk x y z t ↔ pB x y z t = true := by
  revert x y z t; decide

theorem ind_eq (n : ℕ) (A : Fin (n + 1) → Fin 4 → Fin 2) : ind A = indG 3 pB A := by
  funext i j
  simp only [ind, indG, hblk]

def SMT : List (List ℕ) :=
  [[65535, 0, 0, 0, 0, 0, 0, 0],
  [8738, 34952, 0, 0, 0, 0, 0, 0],
  [3598, 0, 57568, 0, 0, 0, 0, 0],
  [2056, 0, 32896, 0, 0, 0, 0, 0],
  [254, 0, 0, 0, 65024, 0, 0, 0],
  [32, 136, 0, 0, 8192, 34816, 0, 0],
  [202, 0, 32, 0, 51712, 0, 8192, 0],
  [128, 0, 0, 0, 32768, 0, 0, 0],
  [65534, 0, 0, 0, 0, 0, 0, 0],
  [8736, 34952, 0, 0, 0, 0, 0, 0],
  [3594, 0, 57568, 0, 0, 0, 0, 0],
  [2048, 0, 32896, 0, 0, 0, 0, 0],
  [61678, 0, 0, 0, 3584, 0, 0, 0],
  [8192, 32904, 0, 0, 0, 2048, 0, 0],
  [49290, 0, 8224, 0, 2560, 0, 0, 0],
  [32768, 0, 0, 0, 0, 0, 0, 0],
  [2576958532, 0, 0, 0, 0, 0, 0, 0],
  [0, 2290614272, 0, 0, 0, 0, 0, 0],
  [134743044, 0, 2155888704, 0, 0, 0, 0, 0],
  [134742016, 0, 2155872256, 0, 0, 0, 0, 0],
  [9961540, 0, 0, 0, 2550154240, 0, 0, 0],
  [0, 8912896, 0, 0, 0, 2281701376, 0, 0],
  [8912960, 0, 0, 0, 2281717760, 0, 0, 0],
  [8388608, 0, 0, 0, 2147483648, 0, 0, 0],
  [2576892996, 0, 0, 0, 0, 0, 0, 0],
  [0, 2290614272, 0, 0, 0, 0, 0, 0],
  [134743040, 0, 2155888704, 0, 0, 0, 0, 0],
  [134217728, 0, 2155872256, 0, 0, 0, 0, 0],
  [2424848452, 0, 0, 0, 134218752, 0, 0, 0],
  [0, 2156396544, 0, 0, 0, 134217728, 0, 0],
  [2156412928, 0, 0, 0, 134217728, 0, 0, 0],
  [2147483648, 0, 0, 0, 0, 0, 0, 0],
  [215242286051376, 0, 0, 0, 0, 0, 0, 0],
  [2207613198368, 141287244169216, 0, 0, 0, 0, 0, 0],
  [2207613190144, 0, 211930866262048, 0, 0, 0, 0, 0],
  [0, 0, 141287244169216, 0, 0, 0, 0, 0],
  [833223655472, 0, 0, 0, 213305255800832, 0, 0, 0],
  [32, 549755813888, 0, 0, 8192, 140737488355328, 0, 0],
  [833223655424, 0, 32, 0, 213305255788544, 0, 8192, 0],
  [549755813888, 0, 0, 0, 140737488355328, 0, 0, 0],
  [215237991084080, 0, 0, 0, 0, 0, 0, 0],
  [2199023263776, 141287244169216, 0, 0, 0, 0, 0, 0],
  [2207613190144, 0, 211930866262048, 0, 0, 0, 0, 0],
  [0, 0, 141287244169216, 0, 0, 0, 0, 0],
  [211939456200736, 0, 0, 0, 2199023255552, 0, 0, 0],
  [8192, 141287244169216, 0, 0, 0, 0, 0, 0],
  [211664578281472, 0, 8224, 0, 2199023255552, 0, 0, 0],
  [140737488355328, 0, 0, 0, 0, 0, 0, 0],
  [9331810546779947008, 0, 0, 0, 0, 0, 0, 0],
  [0, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [0, 0, 9259471477495824384, 0, 0, 0, 0, 0],
  [0, 0, 9259400833873739776, 0, 0, 0, 0, 0],
  [36029071897919488, 0, 0, 0, 9223442405867388928, 0, 0, 0],
  [0, 36028797018963968, 0, 0, 0, 9223372036854775808, 0, 0],
  [36029071896870912, 0, 0, 0, 9223442405598953472, 0, 0, 0],
  [36028797018963968, 0, 0, 0, 9223372036854775808, 0, 0, 0],
  [9331529071803236352, 0, 0, 0, 0, 0, 0, 0],
  [0, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [0, 0, 9259471477495824384, 0, 0, 0, 0, 0],
  [0, 0, 9259400833873739776, 0, 0, 0, 0, 0],
  [9259471477764259840, 0, 0, 0, 0, 0, 0, 0],
  [0, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [9259471202617917440, 0, 0, 0, 0, 0, 0, 0],
  [9223372036854775808, 0, 0, 0, 0, 0, 0, 0],
  [1133644657049820494565120, 0, 0, 0, 0, 0, 0, 0],
  [151152620939976065942016, 604610483759904263768064, 0, 0, 0, 0, 0, 0],
  [258254417031933726208, 0, 1057810092162800527867904, 0, 0, 0, 0, 0],
  [147573952589676414976, 0, 604462909807314587353088, 0, 0, 0, 0, 0],
  [258254417031933722624, 0, 0, 0, 1133367955888714851290624, 0, 0, 0],
  [0, 147573952589676412928, 0, 0, 151115727451828646838272, 604462909807314587355136, 0, 0],
  [184467440737095516160, 0, 0, 0, 906694364710971881032192, 0, 151115727451828646838272, 0],
  [0, 0, 0, 0, 604462909807314587353088, 0, 0, 0],
  [1133626210305746785013504, 0, 0, 0, 0, 0, 0, 0],
  [151115727451828646838784, 604610483759904263768064, 0, 0, 0, 0, 0, 0],
  [184467440737095519744, 0, 1057810092162800527867904, 0, 0, 0, 0, 0],
  [2048, 0, 604462909807314587353088, 0, 0, 0, 0, 0],
  [1133626210305746785009664, 0, 0, 0, 3584, 0, 0, 0],
  [151115727451828646838272, 604610483759904263766016, 0, 0, 0, 2048, 0, 0],
  [906878832151708976545792, 0, 151115727451828646838272, 0, 2560, 0, 0, 0],
  [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
  [44577024051892101511223706624, 0, 0, 0, 0, 0, 0, 0],
  [0, 39623752663689085830303842304, 0, 0, 0, 0, 0, 0],
  [9671480343893328370074624, 0, 39614383488587072454065651712, 0, 0, 0, 0, 0],
  [9671406556917033531867136, 0, 39614081257132168796771975168, 0, 0, 0, 0, 0],
  [9671480343893328235855872, 0, 0, 0, 44566143645728593553796367360, 0, 0, 0],
  [0, 9671406556917033397649408, 0, 0, 0, 39614081257132168796906192896, 0, 0],
  [9671406556917033397649408, 0, 0, 0, 39614383488587072454199869440, 0, 0, 0],
  [0, 0, 0, 0, 39614081257132168796771975168, 0, 0, 0],
  [44575815126072486882049000448, 0, 0, 0, 0, 0, 0, 0],
  [0, 39623752663689085830303842304, 0, 0, 0, 0, 0, 0],
  [9671406556917033531868160, 0, 39614383488587072454065651712, 0, 0, 0, 0, 0],
  [134217728, 0, 39614081257132168796771975168, 0, 0, 0, 0, 0],
  [44575815126072486881898004480, 0, 0, 0, 134218752, 0, 0, 0],
  [0, 39623752663689085830169624576, 0, 0, 0, 134217728, 0, 0],
  [39624054895143989487463301120, 0, 0, 0, 134217728, 0, 0, 0],
  [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
  [3894460328615337105591694383906816, 0, 0, 0, 0, 0, 0, 0],
  [158456476144256129214757994496, 2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0],
  [158456325028528677386111156224, 0, 3894222644052236448849700893753344, 0, 0, 0, 0, 0],
  [0, 0, 2596148429267413814265248164610048, 0, 0, 0, 0, 0],
  [158456325028528675187087900672, 0, 0, 0, 3894222644127794312577814240428032, 0, 0, 0],
  [0, 0, 0, 0, 151115727451828646838272, 2596148429267413814265248164610048, 0, 0],
  [158456325028528675187087900672, 0, 0, 0, 3894222643901120721400071270170624, 0, 151115727451828646838272, 0],
  [0, 0, 0, 0, 2596148429267413814265248164610048, 0, 0, 0],
  [3894381100452822841254100839956480, 0, 0, 0, 0, 0, 0, 0],
  [151115727454027670093824, 2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0],
  [158456325028528677386111156224, 0, 3894222644052236448849700893753344, 0, 0, 0, 0, 0],
  [0, 0, 2596148429267413814265248164610048, 0, 0, 0, 0, 0],
  [3894381100452822841250802305073152, 0, 0, 0, 2199023255552, 0, 0, 0],
  [151115727451828646838272, 2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0],
  [3894381100226149250073059334815744, 0, 151115727451828646838272, 0, 2199023255552, 0, 0, 0],
  [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
  [170147673836494160423436545529930055680, 0, 0, 0, 0, 0, 0, 0],
  [0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [0, 0, 170142481534683865438594436339966410752, 0, 0, 0, 0, 0],
  [0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 170142481539635625595735957439562907648, 0, 0, 0],
  [0, 0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0],
  [0, 0, 0, 0, 170142481534683865438594436339966410752, 0, 0, 0],
  [0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0],
  [170142481539635625595808015033600835584, 0, 0, 0, 0, 0, 0, 0],
  [0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [0, 0, 170142481534683865438594436339966410752, 0, 0, 0, 0, 0],
  [0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0],
  [170142481539635625595735957439562907648, 0, 0, 0, 0, 0, 0, 0],
  [0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [170142481534683865438594436339966410752, 0, 0, 0, 0, 0, 0, 0],
  [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0]]

def Rm : List ℕ :=
  [170147673836494160423436545529930055680, 170150270183003807843969923225249382400, 0, 151115727451828646838272, 2199157474304, 170150270183004563607074766602727083588, 2596148429267413814265248164610048, 39615139067224331597299851296, 9223585344660721152, 8192, 604610483759904263766016, 2048, 2199157485098, 141287244169216, 2155929824, 170150270183004563607074766602727124718, 2596148429872024298166439672580232, 39615139067224331599455772896, 9223585344660753920, 39615139251691772334395367456, 604610483759904263798920, 10752, 34816, 9223585903015423726, 141287244204168, 2199157476864, 32904, 604610483759904263768064, 604462909807314587353088, 32896, 140737488355328, 2155929834, 8224, 2147543552, 9223585344660762112, 604462909807314587385984, 140737488388096, 39615139251691772336551289066, 151115727451828646846496, 39615139251691772334395370016, 604610483759904263800968, 755578637259143234191360, 32768, 10784, 34952, 142938793373184, 2155932394, 41120, 2147543722, 2560, 39615139251691772336551291626, 755578637259143234232480, 755578637259143234224256, 142938793373354, 40960, 43520, 43552]

def NX : List (List ℕ) :=
  [[1, 2, 3, 2, 4, 2, 2, 2],
  [5, 6, 7, 2, 8, 2, 9, 2],
  [2, 2, 2, 2, 2, 2, 2, 2],
  [3, 10, 2, 2, 2, 11, 2, 2],
  [12, 13, 14, 2, 2, 2, 2, 2],
  [15, 16, 17, 2, 18, 11, 9, 2],
  [6, 2, 2, 2, 2, 2, 2, 2],
  [19, 20, 3, 2, 21, 22, 2, 2],
  [23, 24, 14, 2, 25, 2, 2, 2],
  [9, 26, 2, 2, 2, 11, 2, 2],
  [27, 2, 28, 2, 2, 2, 2, 2],
  [11, 2, 29, 2, 2, 2, 2, 2],
  [12, 24, 14, 2, 9, 22, 2, 2],
  [13, 2, 2, 2, 30, 2, 2, 2],
  [31, 26, 32, 2, 33, 22, 9, 2],
  [15, 16, 17, 2, 34, 22, 9, 2],
  [16, 2, 35, 2, 36, 2, 2, 2],
  [37, 20, 38, 2, 33, 22, 9, 2],
  [23, 24, 14, 2, 25, 2, 2, 2],
  [39, 40, 41, 2, 21, 22, 2, 2],
  [40, 2, 35, 2, 42, 2, 2, 2],
  [43, 44, 29, 2, 2, 11, 2, 2],
  [22, 2, 29, 2, 2, 2, 2, 2],
  [23, 24, 14, 2, 45, 22, 9, 2],
  [24, 2, 29, 2, 36, 2, 2, 2],
  [12, 24, 14, 2, 2, 2, 2, 2],
  [44, 2, 29, 2, 42, 2, 2, 2],
  [27, 2, 35, 2, 2, 2, 2, 2],
  [28, 2, 2, 2, 2, 2, 2, 2],
  [29, 2, 2, 2, 42, 2, 2, 2],
  [30, 2, 2, 2, 2, 2, 2, 2],
  [46, 44, 47, 2, 33, 22, 9, 2],
  [32, 26, 2, 2, 9, 22, 2, 2],
  [48, 44, 47, 2, 49, 11, 2, 2],
  [23, 24, 14, 2, 25, 11, 2, 2],
  [35, 2, 2, 2, 42, 2, 2, 2],
  [36, 2, 2, 2, 2, 2, 2, 2],
  [50, 40, 51, 2, 33, 22, 9, 2],
  [38, 20, 2, 2, 9, 22, 2, 2],
  [39, 40, 52, 2, 21, 22, 2, 2],
  [40, 2, 35, 2, 42, 2, 2, 2],
  [41, 10, 2, 2, 2, 11, 2, 2],
  [42, 2, 2, 2, 2, 2, 2, 2],
  [43, 44, 29, 2, 9, 22, 2, 2],
  [44, 2, 29, 2, 42, 2, 2, 2],
  [53, 24, 14, 2, 49, 11, 2, 2],
  [46, 44, 47, 2, 33, 22, 9, 2],
  [47, 26, 2, 2, 54, 22, 2, 2],
  [48, 44, 47, 2, 55, 22, 2, 2],
  [43, 44, 29, 2, 2, 2, 2, 2],
  [50, 40, 51, 2, 33, 22, 9, 2],
  [51, 20, 2, 2, 54, 22, 2, 2],
  [52, 10, 2, 2, 42, 11, 2, 2],
  [53, 24, 14, 2, 55, 22, 2, 2],
  [54, 26, 2, 2, 2, 11, 2, 2],
  [56, 44, 29, 2, 2, 11, 2, 2],
  [56, 44, 29, 2, 9, 22, 2, 2]]

def VT : List (List ℕ) :=
  [[1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 5, 0, 3, 3, 6, 1, 5, 4, 3, 2, 2, 5, 2, 6, 6, 3, 6, 4, 5, 3, 4, 2, 6, 3, 3, 3, 2, 1, 2, 1, 6, 4, 5, 5, 2, 1, 6, 4, 5, 3, 3, 1, 5, 3, 5, 6, 4, 5, 3, 6, 4, 4, 5, 3, 4, 5],
  [11, 19, 0, 7, 13, 24, 1, 17, 18, 8, 3, 4, 19, 3, 23, 25, 6, 23, 18, 17, 6, 12, 4, 25, 6, 14, 6, 4, 1, 3, 1, 23, 12, 17, 20, 3, 1, 23, 12, 18, 6, 7, 1, 15, 6, 19, 23, 12, 18, 10, 23, 12, 9, 20, 8, 12, 15],
  [39, 68, 0, 14, 45, 84, 1, 46, 68, 18, 5, 7, 60, 4, 70, 86, 10, 70, 68, 47, 10, 28, 7, 85, 10, 48, 10, 7, 1, 4, 1, 70, 30, 50, 72, 4, 1, 70, 30, 49, 10, 14, 1, 36, 10, 63, 70, 30, 52, 24, 70, 30, 17, 65, 18, 28, 36],
  [127, 217, 0, 26, 134, 259, 1, 106, 213, 35, 8, 11, 165, 5, 185, 263, 15, 185, 213, 108, 15, 57, 11, 253, 15, 140, 15, 11, 1, 5, 1, 185, 65, 123, 220, 5, 1, 185, 65, 111, 15, 26, 1, 75, 15, 176, 185, 65, 127, 50, 185, 65, 30, 180, 35, 57, 75],
  [377, 614, 0, 45, 355, 722, 1, 217, 593, 61, 12, 16, 411, 6, 434, 729, 21, 434, 593, 220, 21, 106, 16, 675, 21, 365, 21, 16, 1, 6, 1, 434, 126, 268, 604, 6, 1, 434, 126, 224, 21, 45, 1, 141, 21, 441, 434, 126, 275, 95, 434, 126, 50, 448, 61, 106, 141],
  [1014, 1594, 0, 73, 851, 1854, 1, 408, 1495, 98, 17, 22, 943, 7, 926, 1865, 28, 926, 1495, 412, 28, 184, 22, 1648, 28, 866, 28, 22, 1, 7, 1, 926, 224, 533, 1511, 7, 1, 926, 224, 417, 28, 73, 1, 245, 28, 1014, 926, 224, 544, 168, 926, 224, 79, 1025, 98, 184, 245],
  [2518, 3856, 0, 112, 1876, 4434, 1, 719, 3468, 148, 23, 29, 2017, 8, 1831, 4450, 36, 1831, 3468, 724, 36, 302, 29, 3736, 36, 1897, 36, 29, 1, 8, 1, 1831, 372, 986, 3490, 8, 1, 1831, 372, 730, 36, 112, 1, 400, 36, 2169, 1831, 372, 1002, 280, 1831, 372, 119, 2185, 148, 302, 400],
  [5844, 8770, 0, 164, 3856, 9962, 1, 1203, 7500, 213, 30, 37, 4061, 9, 3402, 9984, 45, 3402, 7500, 1209, 45, 473, 37, 7949, 45, 3884, 45, 37, 1, 9, 1, 3402, 585, 1719, 7529, 9, 1, 3402, 585, 1216, 45, 164, 1, 621, 45, 4361, 3402, 585, 1741, 444, 3402, 585, 172, 4383, 213, 473, 621],
  [12790, 18879, 0, 231, 7472, 21181, 1, 1928, 15280, 295, 38, 46, 7758, 10, 6001, 21210, 55, 6001, 15280, 1935, 55, 712, 46, 16007, 55, 7508, 55, 46, 1, 10, 1, 6001, 880, 2852, 15317, 10, 1, 6001, 880, 1943, 55, 231, 1, 925, 55, 8311, 6001, 880, 2881, 675, 6001, 880, 240, 8340, 295, 712, 925],
  [26582, 38685, 0, 315, 13769, 42887, 1, 2979, 29571, 396, 47, 56, 14155, 11, 10129, 42924, 66, 10129, 29571, 2987, 66, 1036, 56, 30715, 66, 13814, 66, 56, 1, 11, 1, 10129, 1276, 4537, 29617, 11, 1, 10129, 1276, 2996, 66, 315, 1, 1331, 66, 15117, 10129, 1276, 4574, 990, 10129, 1276, 325, 15154, 396, 1036, 1331],
  [52769, 75834, 0, 418, 24295, 83142, 1, 4460, 54724, 518, 57, 67, 24802, 12, 16460, 83188, 78, 16460, 54724, 4469, 78, 1464, 67, 56479, 78, 24350, 78, 67, 1, 12, 1, 16460, 1794, 6962, 54780, 12, 1, 16460, 1794, 4479, 78, 418, 1, 1860, 78, 26395, 16460, 1794, 7008, 1408, 16460, 1794, 429, 26441, 518, 1464, 1860],
  [100547, 142845, 0, 542, 41274, 155035, 1, 6496, 97367, 663, 68, 79, 41925, 13, 25879, 155091, 91, 25879, 97367, 6506, 91, 2017, 79, 99997, 91, 41340, 91, 79, 1, 13, 1, 25879, 2457, 10355, 97434, 13, 1, 25879, 2457, 6517, 91, 542, 1, 2535, 91, 44454, 25879, 2457, 10411, 1950, 25879, 2457, 554, 44510, 663, 2017, 2535],
  [184661, 259562, 0, 689, 67817, 279170, 1, 9235, 167307, 833, 80, 92, 68637, 14, 39524, 279237, 105, 39524, 167307, 9246, 105, 2718, 92, 171163, 105, 67895, 105, 92, 1, 14, 1, 39524, 3290, 14988, 167386, 14, 1, 39524, 3290, 9258, 105, 689, 1, 3381, 105, 72509, 39524, 3290, 15055, 2639, 39524, 3290, 702, 72576, 833, 2718, 3381],
  [328068, 456546, 0, 861, 108175, 487098, 1, 12850, 278687, 1030, 93, 106, 109191, 15, 58832, 487177, 120, 58832, 278687, 12862, 120, 3592, 106, 284226, 120, 108266, 120, 106, 1, 15, 1, 58832, 4320, 21181, 278779, 15, 1, 58832, 4320, 12875, 120, 861, 1, 4425, 120, 114936, 58832, 4320, 21260, 3500, 58832, 4320, 875, 115015, 1030, 3592, 4425]]

def ce : List ℤ := [1, -10, 45, -120, 210, -252, 210, -120, 45, -10, 1]

def nm : List ℤ := [0, 3, -19, 64, -128, 172, -167, 151, -154, 151, -107, 49, -13, 2]

def aT (n : ℕ) : ℕ := (VT.getD n []).getD 0 0

theorem hlen : SMT.length = 2 ^ (3 + 1) * 2 ^ 3 := by decide +kernel

theorem hRmlen : Rm.length = 57 := by decide +kernel

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
    ∑ j ∈ range (10 + 1), ce.getD j 0 * ((VT.getD (4 + 10 - j) []).getD d 0 : ℤ) = 0 := by
  decide +kernel

theorem hsmallrec : ∀ n < 4 + 10, 13 < n →
    ∑ j ∈ range (10 + 1), ce.getD j 0 * (aT (n - j) : ℤ) = 0 := by
  decide +kernel

theorem hsm : ∀ n ≤ 13, ∑ j ∈ range (10 + 1), ce.getD j 0 *
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

theorem annih (k : ℕ) (hk : 4 ≤ k) :
    ∑ j ∈ range (10 + 1), ce.getD j 0 * (a (k + 10 - j) : ℤ) = 0 := by
  simp only [a_eq_u]
  refine u_annih hlen hS hNX ce 10 4 ?_ k hk 0 (by rw [hRmlen]; norm_num)
  intro d hd
  refine (Finset.sum_congr rfl ?_).trans (hZ d hd)
  intro j hj
  have := mem_range.mp hj
  rw [u_VT hlen hS hNX hV0 hV _ (by rw [hVTlen]; omega) d hd]

theorem rec_all (n : ℕ) (hn : 13 < n) :
    ∑ j ∈ range (10 + 1), ce.getD j 0 * (a (n - j) : ℤ) = 0 := by
  rcases lt_or_ge n (4 + 10) with h | h
  · refine (Finset.sum_congr rfl ?_).trans (hsmallrec n h hn)
    intro j hj
    rw [a_VT _ (by omega)]
  · refine (Finset.sum_congr rfl ?_).trans (annih (n - 10) (by omega))
    intro j hj
    have := mem_range.mp hj
    rw [show n - 10 + 10 - j = n - j by omega]

theorem recurrence (n : ℕ) (hn : 13 < n) : (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  have h := rec_all n hn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ce, List.getD_cons_zero,
    List.getD_cons_succ, Nat.sub_zero] at h
  linarith

theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (3 - 19 * X + 64 * X ^ 2 - 128 * X ^ 3 + 172 * X ^ 4 - 167 * X ^ 5 + 151 * X ^ 6 - 154 * X ^ 7 + 151 * X ^ 8 - 107 * X ^ 9 + 49 * X ^ 10 - 13 * X ^ 11 + 2 * X ^ 12) := by
  apply gf_of_rec _ ce nm 10 13 (by decide)
  · intro n hn
    have h := rec_all n hn
    have h' : ∀ j ∈ range (10 + 1), (ce.getD j 0 : ℚ) *
        (if j ≤ n then (if n - j = 0 then (0 : ℚ) else (a (n - j) : ℚ)) else 0) =
        ((ce.getD j 0 * (a (n - j) : ℤ) : ℤ) : ℚ) := by
      intro j hj
      have := mem_range.mp hj
      rw [if_pos (by omega), if_neg (by omega)]
      push_cast; ring
    rw [Finset.sum_congr rfl h', ← Int.cast_sum, h, Int.cast_zero]
  · intro n hn
    have h := hsm n hn
    have h' : ∀ j ∈ range (10 + 1), (ce.getD j 0 : ℚ) *
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
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (3 - 19 * X + 64 * X ^ 2 - 128 * X ^ 3 + 172 * X ^ 4 - 167 * X ^ 5 + 151 * X ^ 6 - 154 * X ^ 7 + 151 * X ^ 8 - 107 * X ^ 9 + 49 * X ^ 10 - 13 * X ^ 11 + 2 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a227638

theorem OMA.solution : type_of% @OMA.S_oeis_a227638.main :=
  OMA.S_oeis_a227638.conjecture
