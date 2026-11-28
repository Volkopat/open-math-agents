import OMAStatements.S_oeis_a227086

/-!
Proof of Barker's conjectures for OEIS A227086, for the statement of pull request 33303. The rows of the larger array are read from the top
by a finite automaton whose state is the current row together with the set of adjacent columns
that are still equal; an indicator array arises exactly when the automaton accepts it. The subset
construction gives a finite deterministic automaton (its states are bit masks), checked in the
kernel; the count of accepted words then satisfies the (1 - x)^12 recurrence componentwise, and
the generating function follows by comparing coefficients.
-/

namespace OMA.S_oeis_a227086

open PowerSeries Finset

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nondecreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Monotone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

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

def pB (x y z t : ℕ) : Bool := (decide (x < z) || (x == z && decide (y < t))) && (decide (x < y) || (x == y && decide (z < t)))

def SMT : List (List ℕ) :=
  [[32907, 16452, 12336, 0, 2816, 1024, 0, 0],
  [32906, 0, 8224, 0, 2560, 0, 0, 0],
  [16452, 41130, 0, 0, 1024, 2560, 0, 0],
  [32904, 0, 0, 0, 2048, 0, 0, 0],
  [12850, 0, 34952, 17476, 0, 0, 0, 0],
  [8224, 0, 34952, 0, 0, 0, 0, 0],
  [16448, 43690, 0, 0, 0, 0, 0, 0],
  [32896, 0, 0, 0, 0, 0, 0, 0],
  [2826, 1028, 0, 0, 32896, 16448, 12336, 0],
  [2568, 0, 0, 0, 32896, 0, 8224, 0],
  [1024, 2570, 0, 0, 16448, 41120, 0, 0],
  [2048, 0, 0, 0, 32896, 0, 0, 0],
  [12834, 0, 34952, 17476, 0, 0, 0, 0],
  [8192, 0, 34952, 0, 0, 0, 0, 0],
  [16384, 43690, 0, 0, 0, 0, 0, 0],
  [32768, 0, 0, 0, 0, 0, 0, 0],
  [2156462080, 16452, 269484032, 0, 150994944, 1024, 0, 0],
  [2156396544, 0, 0, 0, 134217728, 0, 0, 0],
  [16452, 2156396544, 0, 0, 1024, 134217728, 0, 0],
  [2156396544, 0, 0, 0, 134217728, 0, 0, 0],
  [269484032, 0, 2290614272, 17476, 0, 0, 0, 0],
  [0, 0, 2290614272, 0, 0, 0, 0, 0],
  [16448, 2290614272, 0, 0, 0, 0, 0, 0],
  [2155872256, 0, 0, 0, 0, 0, 0, 0],
  [151519232, 1028, 0, 0, 2155872256, 16448, 269484032, 0],
  [134742016, 0, 0, 0, 2155872256, 0, 0, 0],
  [1024, 134742016, 0, 0, 16448, 2155872256, 0, 0],
  [134217728, 0, 0, 0, 2155872256, 0, 0, 0],
  [268435456, 0, 2290614272, 17476, 0, 0, 0, 0],
  [0, 0, 2290614272, 0, 0, 0, 0, 0],
  [16384, 2290614272, 0, 0, 0, 0, 0, 0],
  [2147483648, 0, 0, 0, 0, 0, 0, 0],
  [141300129071104, 70643622084608, 12336, 0, 3298534883328, 0, 0, 0],
  [141295834103808, 0, 8224, 0, 2199023255552, 0, 0, 0],
  [70643622084608, 141295834112032, 0, 0, 0, 2199023255552, 0, 0],
  [141287244169216, 0, 0, 0, 0, 0, 0, 0],
  [2207613202480, 0, 141287244169216, 70643622084608, 0, 0, 0, 0],
  [8224, 0, 141287244169216, 0, 0, 0, 0, 0],
  [70643622084608, 143494857367584, 0, 0, 0, 0, 0, 0],
  [141287244169216, 0, 0, 0, 0, 0, 0, 0],
  [3307124817920, 0, 0, 0, 141287244169216, 70643622084608, 12336, 0],
  [2199023255552, 0, 0, 0, 141287244169216, 0, 8224, 0],
  [0, 2207613190144, 0, 0, 70643622084608, 141287244177440, 0, 0],
  [0, 0, 0, 0, 141287244169216, 0, 0, 0],
  [2207613202464, 0, 141287244169216, 70643622084608, 0, 0, 0, 0],
  [8192, 0, 141287244169216, 0, 0, 0, 0, 0],
  [70368744177664, 143494857367584, 0, 0, 0, 0, 0, 0],
  [140737488355328, 0, 0, 0, 0, 0, 0, 0],
  [9259682308850450432, 70643622084608, 269484032, 0, 72057594037927936, 0, 0, 0],
  [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
  [70643622084608, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
  [269484032, 0, 9259400833873739776, 70643622084608, 0, 0, 0, 0],
  [0, 0, 9259400833873739776, 0, 0, 0, 0, 0],
  [70643622084608, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
  [72057594037927936, 0, 0, 0, 9259400833873739776, 70643622084608, 269484032, 0],
  [0, 0, 0, 0, 9259400833873739776, 0, 0, 0],
  [0, 0, 0, 0, 70643622084608, 9259400833873739776, 0, 0],
  [0, 0, 0, 0, 9259400833873739776, 0, 0, 0],
  [268435456, 0, 9259400833873739776, 70643622084608, 0, 0, 0, 0],
  [0, 0, 9259400833873739776, 0, 0, 0, 0, 0],
  [70368744177664, 9259400833873739776, 0, 0, 0, 0, 0, 0],
  [9223372036854775808, 0, 0, 0, 0, 0, 0, 0],
  [604665823992125392420864, 302305241879952131883008, 226673591177742970257408, 0, 2816, 1024, 0, 0],
  [604647377248051682869248, 0, 151115727451828646838272, 0, 2560, 0, 0, 0],
  [302305241879952131883008, 755763104699880329707520, 0, 0, 1024, 2560, 0, 0],
  [604610483759904263766016, 0, 0, 0, 2048, 0, 0, 0],
  [226710484665890389361152, 0, 604610483759904263768064, 302305241879952131884032, 0, 0, 0, 0],
  [151115727451828646838272, 0, 604610483759904263768064, 0, 0, 0, 0, 0],
  [302231454903657293676544, 755763104699880329710080, 0, 0, 0, 0, 0, 0],
  [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
  [184467440737095518976, 73786976294838207488, 0, 0, 604462909807314587353088, 302231454903657293676544, 226673591177742970257408, 0],
  [147573952589676415488, 0, 0, 0, 604462909807314587353088, 0, 151115727451828646838272, 0],
  [1024, 184467440737095518720, 0, 0, 302231454903657293676544, 755578637259143234191360, 0, 0],
  [2048, 0, 0, 0, 604462909807314587353088, 0, 0, 0],
  [226710484665890389361152, 0, 604610483759904263768064, 302305241879952131884032, 0, 0, 0, 0],
  [151115727451828646838272, 0, 604610483759904263768064, 0, 0, 0, 0, 0],
  [302231454903657293676544, 755763104699880329710080, 0, 0, 0, 0, 0, 0],
  [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
  [39624961589508700459344330752, 302305241879952131883008, 4951760157141521099596496896, 0, 150994944, 1024, 0, 0],
  [39623752663689085830169624576, 0, 0, 0, 134217728, 0, 0, 0],
  [302305241879952131883008, 39623752663689085830169624576, 0, 0, 1024, 134217728, 0, 0],
  [39623752663689085830169624576, 0, 0, 0, 134217728, 0, 0, 0],
  [4951760157141521099596496896, 0, 39623752663689085830303842304, 302305241879952131884032, 0, 0, 0, 0],
  [0, 0, 39623752663689085830303842304, 0, 0, 0, 0, 0],
  [302231454903657293676544, 39623752663689085830303842304, 0, 0, 0, 0, 0, 0],
  [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
  [9671406556917033548644352, 73786976294838207488, 0, 0, 39614081257132168796771975168, 302231454903657293676544, 4951760157141521099596496896, 0],
  [9671406556917033531867136, 0, 0, 0, 39614081257132168796771975168, 0, 0, 0],
  [1024, 9671406556917033531867136, 0, 0, 302231454903657293676544, 39614081257132168796771975168, 0, 0],
  [134217728, 0, 0, 0, 39614081257132168796771975168, 0, 0, 0],
  [4951760157141521099596496896, 0, 39623752663689085830303842304, 302305241879952131884032, 0, 0, 0, 0],
  [0, 0, 39623752663689085830303842304, 0, 0, 0, 0, 0],
  [302231454903657293676544, 39623752663689085830303842304, 0, 0, 0, 0, 0, 0],
  [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
  [2596386113754956607278028796461056, 1298074214633706907132624082305024, 226673591177742970257408, 0, 3298534883328, 0, 0, 0],
  [2596306885592442342940435252510720, 0, 151115727451828646838272, 0, 2199023255552, 0, 0, 0],
  [1298074214633706907132624082305024, 2596306885743558070392263899348992, 0, 0, 0, 2199023255552, 0, 0],
  [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
  [158456551702119855129081413632, 0, 2596148429267413814265248164610048, 1298074214633706907132624082305024, 0, 0, 0, 0],
  [151115727451828646838272, 0, 2596148429267413814265248164610048, 0, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 2596306885743558070394462922604544, 0, 0, 0, 0, 0, 0],
  [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
  [158456325028528678485622784000, 0, 0, 0, 2596148429267413814265248164610048, 1298074214633706907132624082305024, 226673591177742970257408, 0],
  [2199023255552, 0, 0, 0, 2596148429267413814265248164610048, 0, 151115727451828646838272, 0],
  [0, 158456325028528677386111156224, 0, 0, 1298074214633706907132624082305024, 2596148429418529541717076811448320, 0, 0],
  [0, 0, 0, 0, 2596148429267413814265248164610048, 0, 0, 0],
  [158456551702119855129081413632, 0, 2596148429267413814265248164610048, 1298074214633706907132624082305024, 0, 0, 0, 0],
  [151115727451828646838272, 0, 2596148429267413814265248164610048, 0, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 2596306885743558070394462922604544, 0, 0, 0, 0, 0, 0],
  [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
  [170146375757327766559315834212213325824, 1298074214633706907132624082305024, 4951760157141521099596496896, 0, 72057594037927936, 0, 0, 0],
  [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
  [4951760157141521099596496896, 0, 170141183460469231731687303715884105728, 1298074214633706907132624082305024, 0, 0, 0, 0],
  [0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
  [72057594037927936, 0, 0, 0, 170141183460469231731687303715884105728, 1298074214633706907132624082305024, 4951760157141521099596496896, 0],
  [0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0],
  [0, 0, 0, 0, 1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0],
  [0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0],
  [4951760157141521099596496896, 0, 170141183460469231731687303715884105728, 1298074214633706907132624082305024, 0, 0, 0, 0],
  [0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0],
  [1298074214633706907132624082305024, 170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0],
  [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0]]

def Rm : List ℕ :=
  [170147673836494160423436545529930055680, 3894381100377264977527087004909568, 44575512820830606929900339200, 302305241879952131884032, 9331458427911667712, 70643622084608, 269484032, 0, 2596306885743558070394462922604544, 755726211211732910606336, 143486267424768, 8224, 39623752663689085830303842304, 2290089984, 755763104699880329710090, 17472, 43680, 9259400833873739776, 143494857367584, 2290614272, 17476, 604610483759904263768064, 34944, 141287244169216, 34952, 2155872256, 755763104699880329742986, 755726211211732910614560, 35456, 43690, 16448, 41120, 43688, 32896, 43176, 604610483759904263800968, 35464]

def NX : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
  [1, 8, 9, 7, 10, 7, 11, 7],
  [2, 7, 12, 3, 13, 7, 7, 7],
  [3, 14, 7, 7, 15, 16, 7, 7],
  [4, 7, 7, 7, 17, 5, 6, 7],
  [5, 18, 7, 7, 7, 7, 7, 7],
  [6, 7, 19, 20, 7, 7, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7],
  [8, 7, 9, 7, 10, 7, 11, 7],
  [9, 7, 21, 7, 22, 7, 7, 7],
  [10, 7, 7, 7, 23, 7, 11, 7],
  [11, 7, 24, 7, 7, 7, 7, 7],
  [12, 7, 7, 7, 13, 7, 7, 7],
  [13, 7, 7, 7, 25, 7, 7, 7],
  [26, 7, 27, 7, 28, 7, 11, 7],
  [15, 29, 7, 7, 30, 31, 7, 7],
  [32, 7, 24, 7, 33, 7, 11, 7],
  [17, 7, 7, 7, 7, 7, 7, 7],
  [18, 7, 34, 7, 10, 7, 11, 7],
  [19, 7, 7, 7, 13, 7, 7, 7],
  [20, 29, 7, 7, 15, 16, 7, 7],
  [21, 7, 7, 7, 22, 7, 7, 7],
  [22, 7, 7, 7, 33, 7, 7, 7],
  [23, 7, 7, 7, 7, 7, 7, 7],
  [24, 7, 7, 7, 22, 7, 7, 7],
  [25, 7, 7, 7, 7, 7, 7, 7],
  [26, 7, 27, 7, 28, 7, 11, 7],
  [27, 7, 35, 7, 22, 7, 7, 7],
  [36, 7, 7, 7, 33, 7, 11, 7],
  [29, 7, 34, 7, 28, 7, 11, 7],
  [30, 29, 7, 7, 7, 7, 7, 7],
  [31, 7, 24, 7, 7, 7, 7, 7],
  [32, 7, 24, 7, 22, 7, 11, 7],
  [33, 7, 7, 7, 7, 7, 7, 7],
  [34, 7, 24, 7, 22, 7, 7, 7],
  [35, 7, 7, 7, 22, 7, 7, 7],
  [36, 7, 7, 7, 22, 7, 11, 7]]

def VT : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [7, 5, 4, 4, 4, 2, 3, 0, 4, 3, 3, 2, 2, 2, 4, 4, 4, 1, 4, 2, 4, 2, 2, 1, 2, 1, 4, 3, 3, 4, 2, 2, 4, 1, 3, 2, 3],
  [29, 17, 12, 16, 10, 6, 9, 0, 12, 7, 6, 4, 4, 3, 12, 12, 9, 1, 12, 4, 16, 4, 3, 1, 4, 1, 12, 7, 6, 12, 6, 4, 10, 1, 7, 4, 7],
  [99, 46, 35, 49, 26, 18, 29, 0, 29, 14, 11, 8, 7, 4, 29, 34, 19, 1, 29, 7, 49, 7, 4, 1, 7, 1, 29, 14, 12, 29, 18, 8, 21, 1, 14, 7, 14],
  [302, 108, 95, 131, 74, 47, 85, 0, 62, 25, 20, 15, 11, 5, 63, 89, 37, 1, 62, 11, 131, 11, 5, 1, 11, 1, 63, 25, 23, 63, 47, 15, 40, 1, 25, 11, 26],
  [842, 230, 242, 320, 207, 109, 227, 0, 122, 41, 36, 26, 16, 6, 126, 214, 67, 1, 122, 16, 320, 16, 6, 1, 16, 1, 126, 41, 42, 126, 110, 26, 71, 1, 41, 16, 46],
  [2177, 455, 584, 727, 544, 231, 563, 0, 225, 63, 63, 42, 22, 7, 235, 476, 114, 1, 225, 22, 727, 22, 7, 1, 22, 1, 235, 63, 73, 235, 236, 42, 119, 1, 63, 22, 78],
  [5281, 848, 1340, 1552, 1339, 456, 1312, 0, 393, 92, 106, 64, 29, 8, 413, 989, 184, 1, 393, 29, 1552, 29, 8, 1, 29, 1, 413, 92, 121, 413, 471, 64, 190, 1, 92, 29, 127],
  [12128, 1503, 2929, 3138, 3108, 849, 2893, 0, 655, 129, 171, 93, 37, 9, 690, 1937, 284, 1, 655, 37, 3138, 37, 9, 1, 37, 1, 690, 129, 192, 690, 884, 93, 291, 1, 129, 37, 199],
  [26548, 2551, 6113, 6049, 6851, 1504, 6068, 0, 1048, 175, 265, 130, 46, 10, 1104, 3604, 422, 1, 1048, 46, 6049, 46, 10, 1, 46, 1, 1104, 175, 293, 1104, 1574, 130, 430, 1, 175, 46, 301],
  [55684, 4169, 12218, 11179, 14424, 2552, 12163, 0, 1618, 231, 396, 176, 56, 11, 1702, 6412, 607, 1, 1618, 56, 11179, 56, 11, 1, 56, 1, 1702, 231, 432, 1702, 2678, 176, 616, 1, 231, 56, 441],
  [112389, 6590, 23464, 19900, 29140, 4170, 23398, 0, 2421, 298, 573, 232, 67, 12, 2541, 10968, 849, 1, 2421, 67, 19900, 67, 12, 1, 67, 1, 2541, 298, 618, 2541, 4380, 232, 859, 1, 298, 67, 628],
  [219051, 10114, 43443, 34258, 56709, 6591, 43365, 0, 3524, 377, 806, 299, 79, 13, 3689, 18121, 1159, 1, 3524, 79, 34258, 79, 13, 1, 79, 1, 3689, 377, 861, 3689, 6921, 299, 1170, 1, 377, 79, 872],
  [413531, 15120, 77793, 57227, 106666, 10115, 77702, 0, 5006, 469, 1106, 378, 92, 14, 5226, 29030, 1549, 1, 5006, 92, 57227, 92, 14, 1, 92, 1, 5226, 469, 1172, 5226, 10610, 378, 1561, 1, 469, 92, 1184]]

def ce : List ℤ := [1, -12, 66, -220, 495, -792, 924, -792, 495, -220, 66, -12, 1]

def nm : List ℤ := [0, 7, -55, 213, -512, 837, -964, 794, -468, 197, -58, 11, -1]

def aT (n : ℕ) : ℕ := (VT.getD n []).getD 0 0

theorem hlen : SMT.length = 2 ^ (3 + 1) * 2 ^ 3 := by decide +kernel

theorem hRmlen : Rm.length = 37 := by decide +kernel

theorem hVTlen : VT.length = 14 := by decide +kernel

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
    ∑ j ∈ range (12 + 1), ce.getD j 0 * ((VT.getD (1 + 12 - j) []).getD d 0 : ℤ) = 0 := by
  decide +kernel

theorem hsmallrec : ∀ n < 1 + 12, 12 < n →
    ∑ j ∈ range (12 + 1), ce.getD j 0 * (aT (n - j) : ℤ) = 0 := by
  decide +kernel

theorem hsm : ∀ n ≤ 12, ∑ j ∈ range (12 + 1), ce.getD j 0 *
    (if j ≤ n then (if n - j = 0 then 0 else (aT (n - j) : ℤ)) else 0) = nm.getD n 0 := by
  decide +kernel

/-! ### Assembly -//-- Our count: the image of the indicator map on the sorted arrays. -/
def myA (n : ℕ) : ℕ :=
  ((univ.filter (fun A : Fin (n + 1) → Fin (3 + 1) → Fin 2 => IsSorted A)).image (indG 3 pB)).card

theorem a_eq_u (n : ℕ) : myA n = u 3 pB Rm n 0 := by
  rw [myA, card_image_eq, ← FS_initM, ← hR0]
  rfl

theorem a_VT (n : ℕ) (hn : n < 14) : myA n = aT n := by
  rw [a_eq_u]
  exact u_VT hlen hS hNX hV0 hV n (by rw [hVTlen]; exact hn) 0 (by rw [hRmlen]; norm_num)

theorem annih (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ range (12 + 1), ce.getD j 0 * (myA (k + 12 - j) : ℤ) = 0 := by
  simp only [a_eq_u]
  refine u_annih hlen hS hNX ce 12 1 ?_ k hk 0 (by rw [hRmlen]; norm_num)
  intro d hd
  refine (Finset.sum_congr rfl ?_).trans (hZ d hd)
  intro j hj
  have := mem_range.mp hj
  rw [u_VT hlen hS hNX hV0 hV _ (by rw [hVTlen]; omega) d hd]

theorem rec_all (n : ℕ) (hn : 12 < n) :
    ∑ j ∈ range (12 + 1), ce.getD j 0 * (myA (n - j) : ℤ) = 0 := by
  rcases lt_or_ge n (1 + 12) with h | h
  · refine (Finset.sum_congr rfl ?_).trans (hsmallrec n h hn)
    intro j hj
    rw [a_VT _ (by omega)]
  · refine (Finset.sum_congr rfl ?_).trans (annih (n - 12) (by omega))
    intro j hj
    have := mem_range.mp hj
    rw [show n - 12 + 12 - j = n - j by omega]

theorem recurrence (n : ℕ) (hn : 12 < n) : (myA n : ℤ) = 12 * myA (n - 1) - 66 * myA (n - 2) + 220 * myA (n - 3) - 495 * myA (n - 4) + 792 * myA (n - 5) - 924 * myA (n - 6) + 792 * myA (n - 7) - 495 * myA (n - 8) + 220 * myA (n - 9) - 66 * myA (n - 10) + 12 * myA (n - 11) - myA (n - 12) := by
  have h := rec_all n hn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ce, List.getD_cons_zero,
    List.getD_cons_succ, Nat.sub_zero] at h
  linarith

theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (myA n : ℚ)) * (1 - X) ^ 12 =
      X * (7 - 55 * X + 213 * X ^ 2 - 512 * X ^ 3 + 837 * X ^ 4 - 964 * X ^ 5 + 794 * X ^ 6 - 468 * X ^ 7 + 197 * X ^ 8 - 58 * X ^ 9 + 11 * X ^ 10 - X ^ 11) := by
  apply gf_of_rec _ ce nm 12 12 (by decide)
  · intro n hn
    have h := rec_all n hn
    have h' : ∀ j ∈ range (12 + 1), (ce.getD j 0 : ℚ) *
        (if j ≤ n then (if n - j = 0 then (0 : ℚ) else (myA (n - j) : ℚ)) else 0) =
        ((ce.getD j 0 * (myA (n - j) : ℤ) : ℤ) : ℚ) := by
      intro j hj
      have := mem_range.mp hj
      rw [if_pos (by omega), if_neg (by omega)]
      push_cast; ring
    rw [Finset.sum_congr rfl h', ← Int.cast_sum, h, Int.cast_zero]
  · intro n hn
    have h := hsm n hn
    have h' : ∀ j ∈ range (12 + 1), (ce.getD j 0 : ℚ) *
        (if j ≤ n then (if n - j = 0 then (0 : ℚ) else (myA (n - j) : ℚ)) else 0) =
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


/-! ### The statement's definitions agree with ours -/

theorem hsub (x y z t : Fin 2) : subVal x y z t = if pB x y z t = true then 1 else 0 := by
  revert x y z t; decide

theorem lexCol_iff {m : ℕ} (f g : Fin m → Fin 2) : lexCol m f g ↔ List.ofFn f ≤ List.ofFn g := by
  rw [lexOK_iff]
  unfold lexCol lexOK
  constructor
  · rintro (rfl | ⟨r, hr, hlt⟩) k hk
    · exact le_rfl
    · rcases lt_trichotomy k r with h | h | h
      · exact (hr k h).le
      · subst h; exact hlt.le
      · exact absurd (hk r h) (ne_of_lt hlt)
  · intro h
    by_cases hfg : f = g
    · exact Or.inl hfg
    · right
      have hex : ∃ r, f r ≠ g r := by
        by_contra hc
        simp only [not_exists, ne_eq, not_not] at hc
        exact hfg (funext hc)
      classical
      let s := univ.filter fun r => f r ≠ g r
      have hs : s.Nonempty := ⟨hex.choose, mem_filter.mpr ⟨mem_univ _, hex.choose_spec⟩⟩
      have hr : f (s.min' hs) ≠ g (s.min' hs) := (mem_filter.mp (Finset.min'_mem s hs)).2
      have hpre : ∀ j : Fin m, j.1 < (s.min' hs).1 → f j = g j := by
        intro j hj
        by_contra hne
        exact absurd (Finset.min'_le s j (mem_filter.mpr ⟨mem_univ _, hne⟩)) (not_le.mpr hj)
      exact ⟨s.min' hs, hpre, lt_of_le_of_ne (h _ (fun k hk => hpre k hk)) hr⟩

theorem row_iff (r r' : Fin 4 → Fin 2) :
    lexRow4 (r 0) (r 1) (r 2) (r 3) (r' 0) (r' 1) (r' 2) (r' 3) ↔ List.ofFn r ≤ List.ofFn r' := by
  rw [lexOK_iff]
  unfold lexRow4 lexOK
  revert r r'
  decide

theorem lexValid_iff (n : ℕ) (M : Fin (n + 1) → Fin 4 → Fin 2) :
    isLexValid (n + 1) M ↔ IsSorted M := by
  unfold isLexValid IsSorted
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_succ, Fin.forall_fin_two]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun i => (row_iff _ _).mp (h1 ⟨i.1, by omega⟩), (lexCol_iff _ _).mp h2, (lexCol_iff _ _).mp h3, (lexCol_iff _ _).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun r => (row_iff _ _).mpr (h1 ⟨r.1, by omega⟩), (lexCol_iff _ _).mpr h2, (lexCol_iff _ _).mpr h3, (lexCol_iff _ _).mpr h4⟩

theorem valid_iff (n : ℕ) (A : Fin n → Fin 3 → Fin 2) :
    isValid n A ↔
      A ∈ (univ.filter (fun M : Fin (n + 1) → Fin (3 + 1) → Fin 2 => IsSorted M)).image (indG 3 pB) := by
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨M, hM, hA⟩
    refine ⟨M, (lexValid_iff n M).mp hM, ?_⟩
    funext r c
    rw [hA r c, hsub]
    rfl
  · rintro ⟨M, hM, rfl⟩
    exact ⟨M, (lexValid_iff n M).mpr hM, fun r c => by rw [hsub]; rfl⟩

theorem ha (n : ℕ) (hn : n ≠ 0) : a n = myA n := by
  unfold a
  rw [if_neg hn, Fintype.card_subtype, myA]
  congr 1
  ext A
  rw [mem_filter, valid_iff]
  simp

theorem ha0 : a 0 = 0 := by unfold a; simp

theorem conjecture : type_of% @main := by
  have hf : (fun n => (a n : ℚ)) = fun n => if n = 0 then (0 : ℚ) else (myA n : ℚ) := by
    funext n
    by_cases hn : n = 0
    · subst hn; simp [ha0]
    · rw [if_neg hn, ha n hn]
  refine ⟨?_, ?_⟩
  · rw [hf, gf]
    all_goals ring
  · intro n hn
    have h := recurrence n hn
    rw [ha n (by omega), ha (n - 1) (by omega), ha (n - 2) (by omega), ha (n - 3) (by omega), ha (n - 4) (by omega), ha (n - 5) (by omega), ha (n - 6) (by omega), ha (n - 7) (by omega), ha (n - 8) (by omega), ha (n - 9) (by omega), ha (n - 10) (by omega), ha (n - 11) (by omega), ha (n - 12) (by omega)]
    push_cast at h ⊢
    linarith

end OMA.S_oeis_a227086

theorem OMA.solution : type_of% @OMA.S_oeis_a227086.main :=
  OMA.S_oeis_a227086.conjecture
