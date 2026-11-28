import OMAStatements.S_oeis_a227554

/-!
Proof of Barker's conjectures for OEIS A227554, for the statement of pull request 32413. The rows of the larger array are read from the top
by a finite automaton whose state is the current row together with the set of adjacent columns
that are still equal; an indicator array arises exactly when the automaton accepts it. The subset
construction gives a finite deterministic automaton (its states are bit masks), checked in the
kernel; the count of accepted words then satisfies the (1 - x)^6 recurrence componentwise, and
the generating function follows by comparing coefficients.
-/

namespace OMA.S_oeis_a227554

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

def pB (x y z t : ℕ) : Bool := x * t != y * z

def SMT : List (List ℕ) :=
  [[255, 0, 0, 0],
  [34, 136, 0, 0],
  [4, 10, 64, 160],
  [8, 0, 128, 0],
  [50, 0, 204, 0],
  [32, 0, 0, 136],
  [64, 130, 0, 40],
  [128, 0, 0, 0],
  [39236, 0, 0, 0],
  [0, 34816, 0, 0],
  [4, 2048, 64, 32768],
  [2048, 0, 32768, 0],
  [4096, 0, 34884, 0],
  [0, 0, 0, 34816],
  [64, 32768, 0, 2048],
  [32768, 0, 0, 0],
  [12779568, 0, 0, 0],
  [131104, 8388608, 0, 0],
  [0, 131072, 4194304, 8388640],
  [0, 0, 8388608, 0],
  [131120, 0, 12582912, 0],
  [32, 0, 0, 8388608],
  [4194304, 8519680, 0, 32],
  [8388608, 0, 0, 0],
  [2168459264, 0, 0, 0],
  [0, 2147483648, 0, 0],
  [0, 0, 4194304, 2147483648],
  [0, 0, 2147483648, 0],
  [4096, 0, 2151677952, 0],
  [0, 0, 0, 2147483648],
  [4194304, 2147483648, 0, 0],
  [2147483648, 0, 0, 0]]

def Rm : List ℕ :=
  [2168459264, 8519680, 34884, 32, 8519712, 8388608, 0, 138, 32832, 168, 136, 170, 128, 130, 40, 162]

def NX : List (List ℕ) :=
  [[0, 1, 2, 3],
  [4, 5, 6, 6],
  [2, 7, 8, 9],
  [3, 6, 6, 10],
  [4, 5, 6, 10],
  [5, 6, 6, 6],
  [6, 6, 6, 6],
  [11, 10, 12, 6],
  [8, 13, 6, 14],
  [9, 6, 12, 10],
  [10, 6, 12, 6],
  [11, 10, 12, 10],
  [12, 6, 6, 6],
  [15, 10, 6, 6],
  [14, 6, 12, 10],
  [15, 10, 6, 10]]

def VT : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [4, 2, 4, 2, 3, 1, 0, 3, 3, 3, 2, 4, 1, 2, 3, 3],
  [12, 4, 13, 4, 6, 1, 0, 7, 8, 6, 3, 9, 1, 5, 6, 7],
  [33, 7, 34, 7, 10, 1, 0, 13, 19, 10, 4, 16, 1, 10, 10, 13],
  [81, 11, 76, 11, 15, 1, 0, 21, 39, 15, 5, 25, 1, 17, 15, 21],
  [179, 16, 151, 16, 21, 1, 0, 31, 71, 21, 6, 36, 1, 26, 21, 31],
  [362, 22, 274, 22, 28, 1, 0, 43, 118, 28, 7, 49, 1, 37, 28, 43]]

def ce : List ℤ := [1, -6, 15, -20, 15, -6, 1]

def nm : List ℤ := [0, 4, -12, 21, -17, 8, -1]

def aT (n : ℕ) : ℕ := (VT.getD n []).getD 0 0

theorem hlen : SMT.length = 2 ^ (2 + 1) * 2 ^ 2 := by decide +kernel

theorem hRmlen : Rm.length = 16 := by decide +kernel

theorem hVTlen : VT.length = 7 := by decide +kernel

theorem hS : ∀ c < 2 ^ (2 + 1) * 2 ^ 2, ∀ β < 2 ^ 2, (SMT.getD c []).getD β 0 = SM 2 pB c β := by
  decide +kernel

theorem hR0 : Rm.getD 0 0 = initM 2 := by decide +kernel

theorem hNX : ∀ d < Rm.length, ∀ β < 2 ^ 2, (NX.getD d []).getD β 0 < Rm.length ∧
    dm SMT (Rm.getD d 0) β = Rm.getD ((NX.getD d []).getD β 0) 0 := by
  decide +kernel

theorem hV0 : ∀ d < Rm.length, (VT.getD 0 []).getD d 0 =
    if ∃ c < 2 ^ (2 + 1) * 2 ^ 2, (Rm.getD d 0).testBit c = true then 1 else 0 := by
  decide +kernel

theorem hV : ∀ k < VT.length - 1, ∀ d < Rm.length, (VT.getD (k + 1) []).getD d 0 =
    ∑ β ∈ range (2 ^ 2), (VT.getD k []).getD ((NX.getD d []).getD β 0) 0 := by
  decide +kernel

theorem hZ : ∀ d < Rm.length,
    ∑ j ∈ range (6 + 1), ce.getD j 0 * ((VT.getD (0 + 6 - j) []).getD d 0 : ℤ) = 0 := by
  decide +kernel

theorem hsmallrec : ∀ n < 0 + 6, 6 < n →
    ∑ j ∈ range (6 + 1), ce.getD j 0 * (aT (n - j) : ℤ) = 0 := by
  decide +kernel

theorem hsm : ∀ n ≤ 6, ∑ j ∈ range (6 + 1), ce.getD j 0 *
    (if j ≤ n then (if n - j = 0 then 0 else (aT (n - j) : ℤ)) else 0) = nm.getD n 0 := by
  decide +kernel

/-! ### Assembly -//-- Our count: the image of the indicator map on the sorted arrays. -/
def myA (n : ℕ) : ℕ :=
  ((univ.filter (fun A : Fin (n + 1) → Fin (2 + 1) → Fin 2 => IsSorted A)).image (indG 2 pB)).card

theorem a_eq_u (n : ℕ) : myA n = u 2 pB Rm n 0 := by
  rw [myA, card_image_eq, ← FS_initM, ← hR0]
  rfl

theorem a_VT (n : ℕ) (hn : n < 7) : myA n = aT n := by
  rw [a_eq_u]
  exact u_VT hlen hS hNX hV0 hV n (by rw [hVTlen]; exact hn) 0 (by rw [hRmlen]; norm_num)

theorem annih (k : ℕ) (hk : 0 ≤ k) :
    ∑ j ∈ range (6 + 1), ce.getD j 0 * (myA (k + 6 - j) : ℤ) = 0 := by
  simp only [a_eq_u]
  refine u_annih hlen hS hNX ce 6 0 ?_ k hk 0 (by rw [hRmlen]; norm_num)
  intro d hd
  refine (Finset.sum_congr rfl ?_).trans (hZ d hd)
  intro j hj
  have := mem_range.mp hj
  rw [u_VT hlen hS hNX hV0 hV _ (by rw [hVTlen]; omega) d hd]

theorem rec_all (n : ℕ) (hn : 6 < n) :
    ∑ j ∈ range (6 + 1), ce.getD j 0 * (myA (n - j) : ℤ) = 0 := by
  rcases lt_or_ge n (0 + 6) with h | h
  · refine (Finset.sum_congr rfl ?_).trans (hsmallrec n h hn)
    intro j hj
    rw [a_VT _ (by omega)]
  · refine (Finset.sum_congr rfl ?_).trans (annih (n - 6) (by omega))
    intro j hj
    have := mem_range.mp hj
    rw [show n - 6 + 6 - j = n - j by omega]

theorem recurrence (n : ℕ) (hn : 6 < n) : (myA n : ℤ) = 6 * myA (n - 1) - 15 * myA (n - 2) + 20 * myA (n - 3) - 15 * myA (n - 4) + 6 * myA (n - 5) - myA (n - 6) := by
  have h := rec_all n hn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ce, List.getD_cons_zero,
    List.getD_cons_succ, Nat.sub_zero] at h
  linarith

theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (myA n : ℚ)) * (1 - X) ^ 6 =
      X * (4 - 12 * X + 21 * X ^ 2 - 17 * X ^ 3 + 8 * X ^ 4 - X ^ 5) := by
  apply gf_of_rec _ ce nm 6 6 (by decide)
  · intro n hn
    have h := rec_all n hn
    have h' : ∀ j ∈ range (6 + 1), (ce.getD j 0 : ℚ) *
        (if j ≤ n then (if n - j = 0 then (0 : ℚ) else (myA (n - j) : ℚ)) else 0) =
        ((ce.getD j 0 * (myA (n - j) : ℤ) : ℤ) : ℚ) := by
      intro j hj
      have := mem_range.mp hj
      rw [if_pos (by omega), if_neg (by omega)]
      push_cast; ring
    rw [Finset.sum_congr rfl h', ← Int.cast_sum, h, Int.cast_zero]
  · intro n hn
    have h := hsm n hn
    have h' : ∀ j ∈ range (6 + 1), (ce.getD j 0 : ℚ) *
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

theorem row_iff (r r' : Fin 3 → Fin 2) :
    lexRow3 (r 0) (r 1) (r 2) (r' 0) (r' 1) (r' 2) ↔ List.ofFn r ≤ List.ofFn r' := by
  rw [lexOK_iff]
  unfold lexRow3 lexOK
  revert r r'
  decide

theorem lexValid_iff (n : ℕ) (M : Fin (n + 1) → Fin 3 → Fin 2) :
    isLexValid (n + 1) M ↔ IsSorted M := by
  unfold isLexValid IsSorted
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_two]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i => (row_iff _ _).mp (h1 ⟨i.1, by omega⟩), (lexCol_iff _ _).mp h2,
      (lexCol_iff _ _).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun r => (row_iff _ _).mpr (h1 ⟨r.1, by omega⟩), (lexCol_iff _ _).mpr h2,
      (lexCol_iff _ _).mpr h3⟩

theorem valid_iff (n : ℕ) (A : Fin n → Fin 2 → Fin 2) :
    isValid n A ↔
      A ∈ (univ.filter (fun M : Fin (n + 1) → Fin (2 + 1) → Fin 2 => IsSorted M)).image (indG 2 pB) := by
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
    rw [ha n (by omega), ha (n - 1) (by omega), ha (n - 2) (by omega), ha (n - 3) (by omega), ha (n - 4) (by omega), ha (n - 5) (by omega), ha (n - 6) (by omega)]
    push_cast at h ⊢
    linarith

end OMA.S_oeis_a227554

theorem OMA.solution : type_of% @OMA.S_oeis_a227554.main :=
  OMA.S_oeis_a227554.conjecture
