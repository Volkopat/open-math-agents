import OMAStatements.S_oeis_a321614

/-!
# Proof of OEIS A321614: Generating function and recurrence

We prove both conjectures of Colin Barker (Dec 22 2018) for OEIS A321614 (`OMA.S_oeis_a321614.main`):
1. Partition the `4 × 2n` board into `2n` disjoint `2 × 2` blocks; since each `2 × 2` block holds
   at most one king and there are `2n` kings, every block holds exactly one king.
2. This gives a symmetry-equivariant bijection between valid placements and length-`n` compatible
   sequences over the 12 valid `4 × 2` slices.
3. By Burnside's lemma on the 4-element rectangle symmetry group `{id, V, H, R}`,
   `4 * a n = idCount n + vCount n + hCount n + rCount n`.
4. Exact recurrences for each of the four sequences (`V(n) = n + 1`, `H(2m) = 3^m` and
   `H(2m+1) = 0`, degree-4 transfer recurrence for `id`, and `(1 - 3x^2)(1 - x - x^2)` for `R`)
   yield the generating function identity in `PowerSeries ℤ` and, by extracting coefficients for
   `n > 9`, the order-10 linear recurrence.
-/

namespace OMA.P_oeis_a321614

open OMA.S_oeis_a321614
open scoped BigOperators

/-! ## Section 1: The 12 valid `4 × 2` slices and compatibility -/

/-- A `4 × 2` slice consists of a king in the top `2 × 2` block `(r_t ∈ {0,1}, c_t ∈ {0,1})`
and a king in the bottom `2 × 2` block `(r_b ∈ {0,1} shifted by +2, c_b ∈ {0,1})` that do not
attack each other (equivalently, `¬ (r_t = 1 ∧ r_b = 0)`). -/
abbrev Slice := { p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) // ¬ (p.1.1 = 1 ∧ p.2.1 = 0) }

/-- Top king row in `Fin 4`. -/
def topRow (s : Slice) : Fin 4 := ⟨s.1.1.1.val, by omega⟩

/-- Top king local column in `Fin 2`. -/
def topCol (s : Slice) : Fin 2 := s.1.1.2

/-- Bottom king row in `Fin 4`. -/
def botRow (s : Slice) : Fin 4 := ⟨s.1.2.1.val + 2, by omega⟩

/-- Bottom king local column in `Fin 2`. -/
def botCol (s : Slice) : Fin 2 := s.1.2.2

/-- Two squares in adjacent `4 × 2` slices (left slice at cols `0,1`, right slice at cols `2,3`)
do not attack each other. -/
def pairCompat (r1 : Fin 4) (c1 : Fin 2) (r2 : Fin 4) (c2 : Fin 2) : Bool :=
  !(decide (Nat.dist r1.val r2.val ≤ 1) && decide (Nat.dist c1.val (c2.val + 2) ≤ 1))

/-- Compatibility of two consecutive `4 × 2` slices. -/
def compat (s1 s2 : Slice) : Bool :=
  pairCompat (topRow s1) (topCol s1) (topRow s2) (topCol s2) &&
  pairCompat (topRow s1) (topCol s1) (botRow s2) (botCol s2) &&
  pairCompat (botRow s1) (botCol s1) (topRow s2) (topCol s2) &&
  pairCompat (botRow s1) (botCol s1) (botRow s2) (botCol s2)

/-- Vertical reflection on a slice: `(r, c) ↦ (3 - r, c)`. -/
def flipVSlice (s : Slice) : Slice :=
  ⟨((s.1.2.1.rev, s.1.2.2), (s.1.1.1.rev, s.1.1.2)), by
    intro ⟨h1, h2⟩
    apply s.2
    have h1v := congrArg Fin.val h1
    have h2v := congrArg Fin.val h2
    simp only [Fin.val_rev, Fin.val_one, Fin.val_zero] at h1v h2v
    have hlt1 := s.1.1.1.isLt
    have hlt2 := s.1.2.1.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩⟩

/-- Horizontal reflection on a slice: `(r, c) ↦ (r, 1 - c)`. -/
def flipHSlice (s : Slice) : Slice :=
  ⟨((s.1.1.1, s.1.1.2.rev), (s.1.2.1, s.1.2.2.rev)), s.2⟩

/-- General rectangle symmetry on a slice. -/
def symSlice (v h : Bool) (s : Slice) : Slice :=
  let s1 := if v then flipVSlice s else s
  if h then flipHSlice s1 else s1

lemma symSlice_false_false (s : Slice) : symSlice false false s = s := rfl

lemma flipVSlice_invol (s : Slice) : flipVSlice (flipVSlice s) = s := by
  ext <;> simp [flipVSlice]

lemma flipHSlice_invol (s : Slice) : flipHSlice (flipHSlice s) = s := by
  ext <;> simp [flipHSlice]

lemma flipV_flipH_comm (s : Slice) : flipVSlice (flipHSlice s) = flipHSlice (flipVSlice s) := by
  ext <;> simp [flipVSlice, flipHSlice]

lemma symSlice_comp (v1 h1 v2 h2 : Bool) (s : Slice) :
    symSlice v2 h2 (symSlice v1 h1 s) = symSlice (xor v1 v2) (xor h1 h2) s := by
  cases v1 <;> cases v2 <;> cases h1 <;> cases h2 <;>
    simp [symSlice, flipVSlice_invol, flipHSlice_invol, flipV_flipH_comm]

lemma compat_flipV : ∀ s1 s2 : Slice, compat (flipVSlice s1) (flipVSlice s2) = compat s1 s2 := by
  decide

lemma compat_flipH : ∀ s1 s2 : Slice, compat (flipHSlice s2) (flipHSlice s1) = compat s1 s2 := by
  decide

lemma compat_rot : ∀ s1 s2 : Slice,
    compat (symSlice true true s2) (symSlice true true s1) = compat s1 s2 := by
  decide

/-! ## Section 2: Compatible slice sequences and bijection with valid boards -/

/-- A valid sequence of `n` consecutive `4 × 2` slices. -/
abbrev ValidSeq (n : ℕ) :=
  { f : Fin n → Slice // ∀ j : Fin (n - 1),
      compat (f ⟨j.val, by omega⟩) (f ⟨j.val + 1, by omega⟩) = true }

lemma validSeq_adj {n : ℕ} (f : ValidSeq n) (j : ℕ) (h : j + 1 < n) :
    compat (f.1 ⟨j, by omega⟩) (f.1 ⟨j + 1, h⟩) = true :=
  f.2 ⟨j, by omega⟩

/-- Action of rectangle symmetries on `ValidSeq n`. -/
def symSeq {n : ℕ} (v h : Bool) (f : ValidSeq n) : ValidSeq n :=
  ⟨fun j => symSlice v h (f.1 (if h then j.rev else j)), by
    intro j
    have hj : j.val + 1 < n := by have := j.isLt; omega
    cases h
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases v
      · exact f.2 j
      · exact (compat_flipV _ _).trans (f.2 j)
    · simp only [↓reduceIte]
      have hrev1 : (⟨j.val, by omega⟩ : Fin n).rev = ⟨(n - 2 - j.val) + 1, by omega⟩ := by
        ext; simp [Fin.rev]; omega
      have hrev2 : (⟨j.val + 1, hj⟩ : Fin n).rev = ⟨n - 2 - j.val, by omega⟩ := by
        ext; simp [Fin.rev]; omega
      rw [hrev1, hrev2]
      have hbase := validSeq_adj f (n - 2 - j.val) (by omega)
      cases v
      · exact (compat_flipH _ _).trans hbase
      · exact (compat_rot _ _).trans hbase⟩

/-- Board square of the top king in slice `j`. -/
def topSq {n : ℕ} (j : Fin n) (s : Slice) : Square n :=
  (topRow s, ⟨2 * j.val + (topCol s).val, by have := j.isLt; have := (topCol s).isLt; omega⟩)

/-- Board square of the bottom king in slice `j`. -/
def botSq {n : ℕ} (j : Fin n) (s : Slice) : Square n :=
  (botRow s, ⟨2 * j.val + (botCol s).val, by have := j.isLt; have := (botCol s).isLt; omega⟩)

/-- Convert a `ValidSeq n` to its `Finset (Square n)` of `2n` kings. -/
def seqToFinset {n : ℕ} (f : Fin n → Slice) : Finset (Square n) :=
  (Finset.univ.image fun j : Fin n => topSq j (f j)) ∪
  (Finset.univ.image fun j : Fin n => botSq j (f j))

lemma topSq_ne_botSq {n : ℕ} (j1 j2 : Fin n) (s1 s2 : Slice) :
    topSq j1 s1 ≠ botSq j2 s2 := by
  intro h
  have hr := congrArg (fun p : Square n => p.1.val) h
  dsimp [topSq, botSq, topRow, botRow] at hr
  have := s1.1.1.1.isLt
  omega

lemma topSq_inj {n : ℕ} {f : Fin n → Slice} :
    Function.Injective (fun j : Fin n => topSq j (f j)) := by
  intro j1 j2 h
  have hc := congrArg (fun p : Square n => p.2.val) h
  dsimp [topSq, topCol] at hc
  have h1 := (f j1).1.1.2.isLt
  have h2 := (f j2).1.1.2.isLt
  ext; omega

lemma botSq_inj {n : ℕ} {f : Fin n → Slice} :
    Function.Injective (fun j : Fin n => botSq j (f j)) := by
  intro j1 j2 h
  have hc := congrArg (fun p : Square n => p.2.val) h
  dsimp [botSq, botCol] at hc
  have h1 := (f j1).1.2.2.isLt
  have h2 := (f j2).1.2.2.isLt
  ext; omega

lemma seqToFinset_card {n : ℕ} (f : Fin n → Slice) : (seqToFinset f).card = 2 * n := by
  unfold seqToFinset
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ topSq_inj,
        Finset.card_image_of_injective _ botSq_inj]
    simp; omega
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨j1, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨j2, _, h⟩
    exact topSq_ne_botSq j1 j2 (f j1) (f j2) h.symm

lemma dist_eq_of_pairCompat {r1 r2 : Fin 4} {c1 c2 : Fin 2}
    (hc : pairCompat r1 c1 r2 c2 = true) (j : ℕ) :
    ¬ (Nat.dist r1.val r2.val ≤ 1 ∧ Nat.dist (2 * j + c1.val) (2 * (j + 1) + c2.val) ≤ 1) := by
  simp only [pairCompat, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rintro ⟨hr, hcol⟩
  have hcol' : Nat.dist c1.val (c2.val + 2) ≤ 1 := by
    simp only [Nat.dist] at hcol ⊢; omega
  rcases hc with h | h
  · exact h hr
  · exact h hcol'

lemma dist_symm_nat (x y : ℕ) : Nat.dist x y = Nat.dist y x := Nat.dist_comm x y

lemma seqToFinset_valid {n : ℕ} (f : ValidSeq n) : valid (seqToFinset f.1) := by
  refine ⟨seqToFinset_card f.1, ?_⟩
  intro p hp q hq ⟨hpq, hdr, hdc⟩
  have mem_iff : ∀ x, x ∈ seqToFinset f.1 ↔
      (∃ j : Fin n, x = topSq j (f.1 j)) ∨ (∃ j : Fin n, x = botSq j (f.1 j)) := by
    intro x
    simp [seqToFinset, eq_comm]
  have aux_same : ∀ (j : Fin n),
      ¬ (Nat.dist (topRow (f.1 j)).val (botRow (f.1 j)).val ≤ 1 ∧
         Nat.dist (2 * j.val + (topCol (f.1 j)).val) (2 * j.val + (botCol (f.1 j)).val) ≤ 1) := by
    intro j ⟨hr, _⟩
    apply (f.1 j).2
    dsimp [topRow, botRow] at hr
    have ht := (f.1 j).1.1.1.isLt
    have hb := (f.1 j).1.2.1.isLt
    simp only [Nat.dist] at hr
    constructor <;> ext <;> omega
  have aux_adj : ∀ (j : Fin n) (hj : j.val + 1 < n),
      let s1 := f.1 j
      let s2 := f.1 ⟨j.val + 1, hj⟩
      (¬ (Nat.dist (topRow s1).val (topRow s2).val ≤ 1 ∧
          Nat.dist (2 * j.val + (topCol s1).val) (2 * (j.val + 1) + (topCol s2).val) ≤ 1)) ∧
      (¬ (Nat.dist (topRow s1).val (botRow s2).val ≤ 1 ∧
          Nat.dist (2 * j.val + (topCol s1).val) (2 * (j.val + 1) + (botCol s2).val) ≤ 1)) ∧
      (¬ (Nat.dist (botRow s1).val (topRow s2).val ≤ 1 ∧
          Nat.dist (2 * j.val + (botCol s1).val) (2 * (j.val + 1) + (topCol s2).val) ≤ 1)) ∧
      (¬ (Nat.dist (botRow s1).val (botRow s2).val ≤ 1 ∧
          Nat.dist (2 * j.val + (botCol s1).val) (2 * (j.val + 1) + (botCol s2).val) ≤ 1)) := by
    intro j hj
    have hcomp := validSeq_adj f j.val hj
    simp only [compat, Bool.and_eq_true] at hcomp
    refine ⟨dist_eq_of_pairCompat hcomp.1.1.1 j.val,
            dist_eq_of_pairCompat hcomp.1.1.2 j.val,
            dist_eq_of_pairCompat hcomp.1.2 j.val,
            dist_eq_of_pairCompat hcomp.2 j.val⟩
  have col_far : ∀ (j1 j2 : Fin n) (c1 c2 : Fin 2),
      Nat.dist (2 * j1.val + c1.val) (2 * j2.val + c2.val) ≤ 1 →
      j1 = j2 ∨ j2.val = j1.val + 1 ∨ j1.val = j2.val + 1 := by
    intro j1 j2 c1 c2 h
    have hc1 := c1.isLt; have hc2 := c2.isLt
    simp only [Nat.dist] at h
    by_cases h1 : j1.val = j2.val
    · left; exact Fin.ext h1
    · right; omega
  rw [mem_iff] at hp hq
  rcases hp with ⟨j1, rfl⟩ | ⟨j1, rfl⟩ <;> rcases hq with ⟨j2, rfl⟩ | ⟨j2, rfl⟩
  · rcases col_far j1 j2 _ _ hdc with rfl | h12 | h21
    · exact hpq rfl
    · have hj : j1.val + 1 < n := by omega
      have h2eq : j2 = ⟨j1.val + 1, hj⟩ := Fin.ext h12
      subst h2eq
      exact (aux_adj j1 hj).1 ⟨hdr, hdc⟩
    · have hj : j2.val + 1 < n := by omega
      have h1eq : j1 = ⟨j2.val + 1, hj⟩ := Fin.ext h21
      subst h1eq
      rw [dist_symm_nat] at hdr hdc
      exact (aux_adj j2 hj).1 ⟨hdr, hdc⟩
  · rcases col_far j1 j2 _ _ hdc with rfl | h12 | h21
    · exact aux_same j1 ⟨hdr, hdc⟩
    · have hj : j1.val + 1 < n := by omega
      have h2eq : j2 = ⟨j1.val + 1, hj⟩ := Fin.ext h12
      subst h2eq
      exact (aux_adj j1 hj).2.1 ⟨hdr, hdc⟩
    · have hj : j2.val + 1 < n := by omega
      have h1eq : j1 = ⟨j2.val + 1, hj⟩ := Fin.ext h21
      subst h1eq
      rw [dist_symm_nat] at hdr hdc
      exact (aux_adj j2 hj).2.2.1 ⟨hdr, hdc⟩
  · rcases col_far j1 j2 _ _ hdc with rfl | h12 | h21
    · rw [dist_symm_nat] at hdr hdc
      exact aux_same j1 ⟨hdr, hdc⟩
    · have hj : j1.val + 1 < n := by omega
      have h2eq : j2 = ⟨j1.val + 1, hj⟩ := Fin.ext h12
      subst h2eq
      exact (aux_adj j1 hj).2.2.1 ⟨hdr, hdc⟩
    · have hj : j2.val + 1 < n := by omega
      have h1eq : j1 = ⟨j2.val + 1, hj⟩ := Fin.ext h21
      subst h1eq
      rw [dist_symm_nat] at hdr hdc
      exact (aux_adj j2 hj).2.1 ⟨hdr, hdc⟩
  · rcases col_far j1 j2 _ _ hdc with rfl | h12 | h21
    · exact hpq rfl
    · have hj : j1.val + 1 < n := by omega
      have h2eq : j2 = ⟨j1.val + 1, hj⟩ := Fin.ext h12
      subst h2eq
      exact (aux_adj j1 hj).2.2.2 ⟨hdr, hdc⟩
    · have hj : j2.val + 1 < n := by omega
      have h1eq : j1 = ⟨j2.val + 1, hj⟩ := Fin.ext h21
      subst h1eq
      rw [dist_symm_nat] at hdr hdc
      exact (aux_adj j2 hj).2.2.2 ⟨hdr, hdc⟩

/-- Map a square to its `2 × 2` block index in `Fin 2 × Fin n`. -/
def blockOf {n : ℕ} (p : Square n) : Fin 2 × Fin n :=
  (⟨p.1.val / 2, by have := p.1.isLt; omega⟩, ⟨p.2.val / 2, by have := p.2.isLt; omega⟩)

/-- Every `2 × 2` block contains a unique king in any valid placement of `2n` kings. -/
lemma blockOf_bijective {n : ℕ} (s : {s : Finset (Square n) // valid s}) :
    Function.Bijective (fun p : s.1 => blockOf p.1) := by
  have hinj : Function.Injective (fun p : s.1 => blockOf p.1) := by
    intro ⟨p, hp⟩ ⟨q, hq⟩ h
    by_contra hpq
    have hpq' : p ≠ q := fun h' => hpq (Subtype.ext h')
    have h1 : p.1.val / 2 = q.1.val / 2 := congrArg (fun x : Fin 2 × Fin n => x.1.val) h
    have h2 : p.2.val / 2 = q.2.val / 2 := congrArg (fun x : Fin 2 × Fin n => x.2.val) h
    exact s.2.2 p hp q hq ⟨hpq', by simp [Nat.dist]; omega, by simp [Nat.dist]; omega⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  simp [Fintype.card_coe, s.2.1]

/-- Extract the unique king in `2 × 2` block `(b, j)` from a valid placement. -/
noncomputable def boardToSeq {n : ℕ} (s : {s : Finset (Square n) // valid s}) : ValidSeq n := by
  classical
  let e := Equiv.ofBijective (fun p : s.1 => blockOf p.1) (blockOf_bijective s)
  let topP (j : Fin n) : s.1 := e.symm (0, j)
  let botP (j : Fin n) : s.1 := e.symm (1, j)
  have htopB : ∀ j, blockOf (topP j).1 = (0, j) := fun j => e.apply_symm_apply (0, j)
  have hbotB : ∀ j, blockOf (botP j).1 = (1, j) := fun j => e.apply_symm_apply (1, j)
  let sl (j : Fin n) : Slice :=
    ⟨((⟨(topP j).1.1.val % 2, Nat.mod_lt _ (by omega)⟩,
       ⟨(topP j).1.2.val % 2, Nat.mod_lt _ (by omega)⟩),
      (⟨(botP j).1.1.val % 2, Nat.mod_lt _ (by omega)⟩,
       ⟨(botP j).1.2.val % 2, Nat.mod_lt _ (by omega)⟩)), by
      rintro ⟨ht, hb⟩
      have htr : (topP j).1.1.val / 2 = 0 := congrArg (fun x : Fin 2 × Fin n => x.1.val) (htopB j)
      have htc : (topP j).1.2.val / 2 = j.val := congrArg (fun x : Fin 2 × Fin n => x.2.val) (htopB j)
      have hbr : (botP j).1.1.val / 2 = 1 := congrArg (fun x : Fin 2 × Fin n => x.1.val) (hbotB j)
      have hbc : (botP j).1.2.val / 2 = j.val := congrArg (fun x : Fin 2 × Fin n => x.2.val) (hbotB j)
      have ht' : (topP j).1.1.val % 2 = 1 := congrArg Fin.val ht
      have hb' : (botP j).1.1.val % 2 = 0 := congrArg Fin.val hb
      exact s.2.2 (topP j).1 (topP j).2 (botP j).1 (botP j).2
        ⟨by intro heq; have := congrArg (fun p : Square n => p.1.val) heq; omega,
         by simp [Nat.dist]; omega,
         by simp [Nat.dist]; omega⟩⟩
  refine ⟨sl, ?_⟩
  intro jFin
  let j := jFin.val
  have hj : j + 1 < n := by have := jFin.isLt; omega
  let j1 : Fin n := ⟨j, by omega⟩
  let j2 : Fin n := ⟨j + 1, hj⟩
  have htr1 : (topP j1).1.1.val = (topRow (sl j1)).val := by
    have h0 : (topP j1).1.1.val / 2 = 0 := congrArg (fun x : Fin 2 × Fin n => x.1.val) (htopB j1)
    dsimp [sl, topRow]; omega
  have htc1 : (topP j1).1.2.val = 2 * j + (topCol (sl j1)).val := by
    have h0 : (topP j1).1.2.val / 2 = j := congrArg (fun x : Fin 2 × Fin n => x.2.val) (htopB j1)
    dsimp [sl, topCol]; omega
  have hbr1 : (botP j1).1.1.val = (botRow (sl j1)).val := by
    have h0 : (botP j1).1.1.val / 2 = 1 := congrArg (fun x : Fin 2 × Fin n => x.1.val) (hbotB j1)
    dsimp [sl, botRow]; omega
  have hbc1 : (botP j1).1.2.val = 2 * j + (botCol (sl j1)).val := by
    have h0 : (botP j1).1.2.val / 2 = j := congrArg (fun x : Fin 2 × Fin n => x.2.val) (hbotB j1)
    dsimp [sl, botCol]; omega
  have htr2 : (topP j2).1.1.val = (topRow (sl j2)).val := by
    have h0 : (topP j2).1.1.val / 2 = 0 := congrArg (fun x : Fin 2 × Fin n => x.1.val) (htopB j2)
    dsimp [sl, topRow]; omega
  have htc2 : (topP j2).1.2.val = 2 * (j + 1) + (topCol (sl j2)).val := by
    have h0 : (topP j2).1.2.val / 2 = j + 1 := congrArg (fun x : Fin 2 × Fin n => x.2.val) (htopB j2)
    dsimp [sl, topCol]; omega
  have hbr2 : (botP j2).1.1.val = (botRow (sl j2)).val := by
    have h0 : (botP j2).1.1.val / 2 = 1 := congrArg (fun x : Fin 2 × Fin n => x.1.val) (hbotB j2)
    dsimp [sl, botRow]; omega
  have hbc2 : (botP j2).1.2.val = 2 * (j + 1) + (botCol (sl j2)).val := by
    have h0 : (botP j2).1.2.val / 2 = j + 1 := congrArg (fun x : Fin 2 × Fin n => x.2.val) (hbotB j2)
    dsimp [sl, botCol]; omega
  have mkPC : ∀ (p q : s.1) (r1 r2 : Fin 4) (c1 c2 : Fin 2),
      p.1.1.val = r1.val → p.1.2.val = 2 * j + c1.val →
      q.1.1.val = r2.val → q.1.2.val = 2 * (j + 1) + c2.val →
      pairCompat r1 c1 r2 c2 = true := by
    intro p q r1 r2 c1 c2 hr1 hc1 hr2 hc2
    simp only [pairCompat, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra h
    push Not at h
    apply s.2.2 p.1 p.2 q.1 q.2
    refine ⟨?_, ?_, ?_⟩
    · intro heq; have := congrArg (fun x : Square n => x.2.val) heq; have := c1.isLt; omega
    · rw [hr1, hr2]; exact h.1
    · rw [hc1, hc2]; have := h.2; simp only [Nat.dist] at this ⊢; omega
  simp only [compat, Bool.and_eq_true]
  exact ⟨⟨⟨mkPC (topP j1) (topP j2) _ _ _ _ htr1 htc1 htr2 htc2,
           mkPC (topP j1) (botP j2) _ _ _ _ htr1 htc1 hbr2 hbc2⟩,
          mkPC (botP j1) (topP j2) _ _ _ _ hbr1 hbc1 htr2 htc2⟩,
         mkPC (botP j1) (botP j2) _ _ _ _ hbr1 hbc1 hbr2 hbc2⟩

/-- Explicit equivalence between valid placements on `4 × 2n` and compatible slice sequences. -/
noncomputable def validBoardEquivSeq (n : ℕ) :
    {s : Finset (Square n) // valid s} ≃ ValidSeq n where
  toFun := boardToSeq
  invFun := fun f => ⟨seqToFinset f.1, seqToFinset_valid f⟩
  left_inv := by
    intro s
    apply Subtype.ext
    change seqToFinset (boardToSeq s).1 = s.1
    have hcard : (seqToFinset (boardToSeq s).1).card = s.1.card := by
      rw [seqToFinset_card, s.2.1]
    apply Finset.eq_of_subset_of_card_le _ (le_of_eq hcard.symm)
    intro q hq
    simp only [seqToFinset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hq
    classical
    let e := Equiv.ofBijective (fun p : s.1 => blockOf p.1) (blockOf_bijective s)
    rcases hq with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hB : blockOf (e.symm (0, j)).1 = (0, j) := e.apply_symm_apply (0, j)
      have hr : (e.symm (0, j)).1.1.val / 2 = 0 := congrArg (fun x : Fin 2 × Fin n => x.1.val) hB
      have hc : (e.symm (0, j)).1.2.val / 2 = j.val := congrArg (fun x : Fin 2 × Fin n => x.2.val) hB
      have heq : topSq j ((boardToSeq s).1 j) = (e.symm (0, j)).1 := by
        apply Prod.ext <;> apply Fin.ext
        · change (e.symm (0, j)).1.1.val % 2 = (e.symm (0, j)).1.1.val; omega
        · change 2 * j.val + (e.symm (0, j)).1.2.val % 2 = (e.symm (0, j)).1.2.val; omega
      rw [heq]; exact (e.symm (0, j)).2
    · have hB : blockOf (e.symm (1, j)).1 = (1, j) := e.apply_symm_apply (1, j)
      have hr : (e.symm (1, j)).1.1.val / 2 = 1 := congrArg (fun x : Fin 2 × Fin n => x.1.val) hB
      have hc : (e.symm (1, j)).1.2.val / 2 = j.val := congrArg (fun x : Fin 2 × Fin n => x.2.val) hB
      have heq : botSq j ((boardToSeq s).1 j) = (e.symm (1, j)).1 := by
        apply Prod.ext <;> apply Fin.ext
        · change (e.symm (1, j)).1.1.val % 2 + 2 = (e.symm (1, j)).1.1.val; omega
        · change 2 * j.val + (e.symm (1, j)).1.2.val % 2 = (e.symm (1, j)).1.2.val; omega
      rw [heq]; exact (e.symm (1, j)).2
  right_inv := by
    intro f
    apply Subtype.ext
    funext j
    classical
    let s : {s : Finset (Square n) // valid s} := ⟨seqToFinset f.1, seqToFinset_valid f⟩
    let e := Equiv.ofBijective (fun p : s.1 => blockOf p.1) (blockOf_bijective s)
    have htop_mem : topSq j (f.1 j) ∈ s.1 := by
      simp only [s, seqToFinset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨j, rfl⟩
    have hbot_mem : botSq j (f.1 j) ∈ s.1 := by
      simp only [s, seqToFinset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨j, rfl⟩
    have htop_eq : (e.symm (0, j)).1 = topSq j (f.1 j) := by
      have h : e.symm (0, j) = ⟨topSq j (f.1 j), htop_mem⟩ := by
        apply e.injective
        rw [e.apply_symm_apply]
        simp only [e, Equiv.ofBijective_apply]
        apply Prod.ext <;> apply Fin.ext
        · dsimp [blockOf, topSq, topRow]; have := (f.1 j).1.1.1.isLt; omega
        · dsimp [blockOf, topSq, topCol]; have := (f.1 j).1.1.2.isLt; omega
      exact congrArg Subtype.val h
    have hbot_eq : (e.symm (1, j)).1 = botSq j (f.1 j) := by
      have h : e.symm (1, j) = ⟨botSq j (f.1 j), hbot_mem⟩ := by
        apply e.injective
        rw [e.apply_symm_apply]
        simp only [e, Equiv.ofBijective_apply]
        apply Prod.ext <;> apply Fin.ext
        · dsimp [blockOf, botSq, botRow]; have := (f.1 j).1.2.1.isLt; omega
        · dsimp [blockOf, botSq, botCol]; have := (f.1 j).1.2.2.isLt; omega
      exact congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> apply Fin.ext
    · change (e.symm (0, j)).1.1.val % 2 = (f.1 j).1.1.1.val
      rw [htop_eq]; dsimp [topSq, topRow]; have := (f.1 j).1.1.1.isLt; omega
    · change (e.symm (0, j)).1.2.val % 2 = (f.1 j).1.1.2.val
      rw [htop_eq]; dsimp [topSq, topCol]; have := (f.1 j).1.1.2.isLt; omega
    · change (e.symm (1, j)).1.1.val % 2 = (f.1 j).1.2.1.val
      rw [hbot_eq]; dsimp [botSq, botRow]; have := (f.1 j).1.2.1.isLt; omega
    · change (e.symm (1, j)).1.2.val % 2 = (f.1 j).1.2.2.val
      rw [hbot_eq]; dsimp [botSq, botCol]; have := (f.1 j).1.2.2.isLt; omega

/-- Equivariance of `seqToFinset` under rectangle symmetries. -/
lemma seqToFinset_symSeq {n : ℕ} (v h : Bool) (f : ValidSeq n) :
    seqToFinset (symSeq v h f).1 = symBoard v h (seqToFinset f.1) := by
  have hsq : ∀ (j : Fin n) (s : Slice),
      (v = false → symSquare false h (topSq j s) = topSq (if h then j.rev else j) (symSlice false h s) ∧
                   symSquare false h (botSq j s) = botSq (if h then j.rev else j) (symSlice false h s)) ∧
      (v = true → symSquare true h (topSq j s) = botSq (if h then j.rev else j) (symSlice true h s) ∧
                  symSquare true h (botSq j s) = topSq (if h then j.rev else j) (symSlice true h s)) := by
    intro j s
    constructor
    · intro hv; subst hv
      cases h
      · constructor <;> (ext <;> simp [symSquare, symSlice, topSq, botSq])
      · constructor <;> (ext <;> simp [symSquare, symSlice, flipHSlice, topSq, botSq, topRow, botRow,
          topCol, botCol, Fin.rev] <;> have := j.isLt <;>
          have := s.1.1.2.isLt <;> have := s.1.2.2.isLt <;> omega)
    · intro hv; subst hv
      cases h
      · constructor <;> (ext <;> simp [symSquare, symSlice, flipVSlice, topSq, botSq, topRow, botRow,
          topCol, botCol, Fin.rev] <;> have := s.1.1.1.isLt <;> have := s.1.2.1.isLt <;> omega)
      · constructor <;> (ext <;> simp [symSquare, symSlice, flipVSlice, flipHSlice, topSq, botSq,
          topRow, botRow, topCol, botCol, Fin.rev] <;> have := j.isLt <;>
          have := s.1.1.1.isLt <;> have := s.1.2.1.isLt <;>
          have := s.1.1.2.isLt <;> have := s.1.2.2.isLt <;> omega)
  ext p
  simp only [seqToFinset, symBoard, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · let j' : Fin n := if h then j.rev else j
      have hj' : (if h then j'.rev else j') = j := by cases h <;> simp [j']
      cases hv : v
      · refine ⟨topSq j' (f.1 j'), Or.inl ⟨j', rfl⟩, ?_⟩
        rw [((hsq j' (f.1 j')).1 hv).1, hj']; rfl
      · refine ⟨botSq j' (f.1 j'), Or.inr ⟨j', rfl⟩, ?_⟩
        rw [((hsq j' (f.1 j')).2 hv).2, hj']; rfl
    · let j' : Fin n := if h then j.rev else j
      have hj' : (if h then j'.rev else j') = j := by cases h <;> simp [j']
      cases hv : v
      · refine ⟨botSq j' (f.1 j'), Or.inr ⟨j', rfl⟩, ?_⟩
        rw [((hsq j' (f.1 j')).1 hv).2, hj']; rfl
      · refine ⟨topSq j' (f.1 j'), Or.inl ⟨j', rfl⟩, ?_⟩
        rw [((hsq j' (f.1 j')).2 hv).1, hj']; rfl
  · rintro ⟨q, ⟨j, rfl⟩ | ⟨j, rfl⟩, rfl⟩
    · let j' : Fin n := if h then j.rev else j
      have hj' : (if h then j'.rev else j') = j := by cases h <;> simp [j']
      cases hv : v
      · left; refine ⟨j', ?_⟩; dsimp [symSeq]; rw [hj', ((hsq j (f.1 j)).1 hv).1]
      · right; refine ⟨j', ?_⟩; dsimp [symSeq]; rw [hj', ((hsq j (f.1 j)).2 hv).1]
    · let j' : Fin n := if h then j.rev else j
      have hj' : (if h then j'.rev else j') = j := by cases h <;> simp [j']
      cases hv : v
      · right; refine ⟨j', ?_⟩; dsimp [symSeq]; rw [hj', ((hsq j (f.1 j)).1 hv).2]
      · left; refine ⟨j', ?_⟩; dsimp [symSeq]; rw [hj', ((hsq j (f.1 j)).2 hv).2]

/-! ## Section 3: Burnside's lemma on `ValidSeq n` -/

/-- The 4-element rectangle symmetry group `C₂ × C₂`. -/
abbrev RectG := Multiplicative (ZMod 2 × ZMod 2)

def rectToBools (g : RectG) : Bool × Bool :=
  let p := Multiplicative.toAdd g
  (decide (p.1 = 1), decide (p.2 = 1))

def boolsToRect (v h : Bool) : RectG :=
  Multiplicative.ofAdd (if v then (1 : ZMod 2) else 0, if h then (1 : ZMod 2) else 0)

lemma rectToBools_one : rectToBools 1 = (false, false) := by decide

lemma rectToBools_mul (g1 g2 : RectG) :
    rectToBools (g1 * g2) =
      (xor (rectToBools g1).1 (rectToBools g2).1, xor (rectToBools g1).2 (rectToBools g2).2) := by
  revert g1 g2
  decide

lemma rectToBools_boolsToRect (v h : Bool) : rectToBools (boolsToRect v h) = (v, h) := by
  cases v <;> cases h <;> decide

instance (n : ℕ) : MulAction RectG (ValidSeq n) where
  smul g f := symSeq (rectToBools g).1 (rectToBools g).2 f
  one_smul f := by
    change symSeq (rectToBools 1).1 (rectToBools 1).2 f = f
    apply Subtype.ext; funext j
    simp [symSeq, rectToBools_one, symSlice_false_false]
  mul_smul g1 g2 f := by
    change symSeq (rectToBools (g1 * g2)).1 (rectToBools (g1 * g2)).2 f =
      symSeq (rectToBools g1).1 (rectToBools g1).2
        (symSeq (rectToBools g2).1 (rectToBools g2).2 f)
    apply Subtype.ext; funext j
    dsimp [symSeq]
    rw [rectToBools_mul]
    set v1 := (rectToBools g1).1
    set h1 := (rectToBools g1).2
    set v2 := (rectToBools g2).1
    set h2 := (rectToBools g2).2
    have hidx : (if h2 then (if h1 then j.rev else j).rev else if h1 then j.rev else j) =
        (if xor h1 h2 then j.rev else j) := by
      cases h1 <;> cases h2 <;> simp
    rw [hidx, symSlice_comp, Bool.xor_comm v1 v2, Bool.xor_comm h1 h2]

/-- Number of fixed valid sequences for symmetry `(v, h)`. -/
noncomputable def fixCount (n : ℕ) (v h : Bool) : ℕ := by
  classical
  letI : Fintype (ValidSeq n) := Subtype.fintype _
  exact Fintype.card { f : ValidSeq n // symSeq v h f = f }

/-- Burnside's lemma: `4 * a n = id + V + H + R`. -/
lemma burnside_four_mul (n : ℕ) :
    4 * a n = fixCount n false false + fixCount n true false +
              fixCount n false true + fixCount n true true := by
  classical
  letI : Fintype (ValidSeq n) := Subtype.fintype _
  have hrel : ∀ (f1 f2 : ValidSeq n),
      (symSetoid n).r ((validBoardEquivSeq n).symm f1) ((validBoardEquivSeq n).symm f2) ↔
      (MulAction.orbitRel RectG (ValidSeq n)).r f1 f2 := by
    intro f1 f2
    constructor
    · rintro ⟨v, h, hEq⟩
      change symBoard v h (seqToFinset f1.1) = seqToFinset f2.1 at hEq
      have hEq' : symBoard v h (seqToFinset f2.1) = seqToFinset f1.1 := by
        rw [← hEq]
        ext p
        simp only [symBoard, Finset.mem_image]
        constructor
        · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
          cases v <;> cases h <;> simp [symSquare] at * <;> exact hr
        · intro hp
          refine ⟨symSquare v h p, ⟨p, hp, rfl⟩, ?_⟩
          cases v <;> cases h <;> simp [symSquare]
      refine ⟨boolsToRect v h, ?_⟩
      change symSeq (rectToBools (boolsToRect v h)).1 (rectToBools (boolsToRect v h)).2 f2 = f1
      rw [rectToBools_boolsToRect]
      apply (validBoardEquivSeq n).symm.injective
      apply Subtype.ext
      dsimp [validBoardEquivSeq]
      rw [seqToFinset_symSeq]
      exact hEq'
    · rintro ⟨g, hg⟩
      have h' : symSeq (rectToBools g).1 (rectToBools g).2 f2 = f1 := hg
      have h'' := congrArg (fun x : ValidSeq n => seqToFinset x.1) h'
      rw [seqToFinset_symSeq] at h''
      exact (symSetoid n).symm ⟨(rectToBools g).1, (rectToBools g).2, h''⟩
  let e : Quotient (symSetoid n) ≃ MulAction.orbitRel.Quotient RectG (ValidSeq n) :=
    Quotient.congr (validBoardEquivSeq n) (by
      intro x y
      have := hrel (validBoardEquivSeq n x) (validBoardEquivSeq n y)
      simpa using this)
  have ha : a n = Fintype.card (MulAction.orbitRel.Quotient RectG (ValidSeq n)) := by
    unfold a
    exact Fintype.card_congr e
  rw [ha]
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group RectG (ValidSeq n)
  have hcardG : Fintype.card RectG = 4 := by decide
  rw [hcardG, mul_comm] at hB
  rw [← hB]
  have hfix : ∀ g : RectG,
      Fintype.card (MulAction.fixedBy (ValidSeq n) g) =
      fixCount n (rectToBools g).1 (rectToBools g).2 := by
    intro g
    unfold fixCount
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  simp_rw [hfix]
  have huniv : (Finset.univ : Finset RectG) =
      {boolsToRect false false, boolsToRect true false,
       boolsToRect false true, boolsToRect true true} := by decide
  rw [huniv]
  have h1 : boolsToRect false false ∉
      ({boolsToRect true false, boolsToRect false true, boolsToRect true true} : Finset RectG) := by
    decide
  have h2 : boolsToRect true false ∉
      ({boolsToRect false true, boolsToRect true true} : Finset RectG) := by
    decide
  have h3 : boolsToRect false true ∉ ({boolsToRect true true} : Finset RectG) := by
    decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  simp only [rectToBools_boolsToRect]
  ring

/-! ## Section 4: Transfer operator on `Slice → ℤ` and exact formulas for `id, V, H, R` -/

/-- Left transfer step: `(step v) j = ∑_{compat i j} v i`. -/
def step (v : Slice → ℤ) (j : Slice) : ℤ :=
  ∑ i : Slice, if compat i j then v i else 0

/-- Right (adjoint) transfer step: `(rstep w) i = ∑_{compat i j} w j`. -/
def rstep (w : Slice → ℤ) (i : Slice) : ℤ :=
  ∑ j : Slice, if compat i j then w j else 0

/-- Iterated left transfer starting from the all-ones vector. -/
def iterStep : ℕ → Slice → ℤ
  | 0 => fun _ => 1
  | k + 1 => step (iterStep k)

lemma step_zero (j : Slice) : step (fun _ => 0) j = 0 := by
  simp [step]

lemma dot_step_eq_dot_rstep (u w : Slice → ℤ) :
    (∑ j : Slice, step u j * w j) = ∑ i : Slice, u i * rstep w i := by
  simp only [step, rstep, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

lemma sigma_subtype_ext {α β : Type*} (p : α → β → Prop)
    {a1 a2 : α} {b1 : {x : β // p a1 x}} {b2 : {x : β // p a2 x}}
    (ha : a1 = a2) (hb : b1.1 = b2.1) :
    (⟨a1, b1⟩ : Σ a : α, {x : β // p a x}) = ⟨a2, b2⟩ := by
  subst ha
  congr 1
  exact Subtype.ext hb

/-- Exact count of valid sequences of length `k + 1` ending at slice `j`. -/
lemma card_validSeq_ending (k : ℕ) (j : Slice) :
    (Fintype.card { f : ValidSeq (k + 1) // f.1 ⟨k, Nat.lt_succ_self k⟩ = j } : ℤ) =
      iterStep k j := by
  classical
  induction k generalizing j with
  | zero =>
    have hcard : Fintype.card { f : ValidSeq 1 // f.1 ⟨0, Nat.lt_succ_self 0⟩ = j } = 1 := by
      refine Fintype.card_eq_one_iff.mpr ?_
      refine ⟨⟨⟨fun _ => j, fun i => Fin.elim0 i⟩, rfl⟩, ?_⟩
      rintro ⟨⟨f, hf⟩, h0⟩
      apply Subtype.ext; apply Subtype.ext; funext x
      have hx : x = ⟨0, Nat.lt_succ_self 0⟩ := by ext; have := x.isLt; omega
      rw [hx]; exact h0
    have hcard' : (Fintype.card { f : ValidSeq 1 // f.1 ⟨0, Nat.lt_succ_self 0⟩ = j } : ℤ) = 1 := by
      exact_mod_cast hcard
    exact hcard'
  | succ k ih =>
    let e : { f : ValidSeq (k + 2) // f.1 ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = j } ≃
        Σ i : { i : Slice // compat i j = true },
          { g : ValidSeq (k + 1) // g.1 ⟨k, Nat.lt_succ_self k⟩ = i.1 } :=
      { toFun := fun ⟨f, hf⟩ =>
          ⟨⟨f.1 ⟨k, by omega⟩, by rw [← hf]; exact validSeq_adj f k (by omega)⟩,
           ⟨⟨fun x => f.1 ⟨x.val, by omega⟩, fun m => validSeq_adj f m.val (by have := m.isLt; omega)⟩, rfl⟩⟩
        invFun := fun ⟨⟨i, hi⟩, ⟨g, hg⟩⟩ =>
          ⟨⟨fun x => if hx : x.val < k + 1 then g.1 ⟨x.val, hx⟩ else j, by
              intro m
              have hm : m.val + 1 < k + 2 := by have := m.isLt; omega
              by_cases hm' : m.val + 1 < k + 1
              · simp only [hm', ↓reduceDIte, show m.val < k + 1 by omega]
                exact validSeq_adj g m.val hm'
              · have hmk : m.val = k := by omega
                simp only [hmk, Nat.lt_succ_self, ↓reduceDIte, lt_irrefl]
                rw [hg]; exact hi⟩,
           by simp⟩
        left_inv := by
          rintro ⟨⟨f, hf⟩, hlast⟩
          apply Subtype.ext; apply Subtype.ext; funext x
          by_cases hx : x.val < k + 1
          · simp [hx]
          · have hxeq : x = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ :=
              Fin.ext (by dsimp; have := x.isLt; omega)
            rw [hxeq]
            simp only [lt_irrefl, ↓reduceDIte]
            exact hlast.symm
        right_inv := by
          rintro ⟨⟨i, hi⟩, ⟨⟨g, hg⟩, hglast⟩⟩
          dsimp only at hglast ⊢
          refine sigma_subtype_ext
            (fun (i : { i : Slice // compat i j = true }) (g : ValidSeq (k + 1)) =>
              g.1 ⟨k, Nat.lt_succ_self k⟩ = i.1) ?_ ?_
          · exact Subtype.ext (by dsimp only; rw [dif_pos (Nat.lt_succ_self k)]; exact hglast)
          · apply Subtype.ext; funext x; exact dif_pos x.isLt }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    push_cast
    simp_rw [ih]
    change (∑ i : { i : Slice // compat i j = true }, iterStep k i.1) =
      ∑ i : Slice, if compat i j = true then iterStep k i else 0
    rw [← Finset.sum_filter]
    refine (Finset.sum_subtype (Finset.univ.filter (fun i : Slice => compat i j = true))
      (fun i => by simp) (fun i => iterStep k i)).symm

/-- `id(0) = 1`, and `id(k + 1) = ∑ j, iterStep k j`. -/
lemma fixCount_id_zero : (fixCount 0 false false : ℤ) = 1 := by
  classical
  letI : Fintype (ValidSeq 0) := Subtype.fintype _
  unfold fixCount
  have h : Fintype.card { f : ValidSeq 0 // symSeq false false f = f } = 1 := by
    refine Fintype.card_eq_one_iff.mpr ?_
    refine ⟨⟨⟨fun x => Fin.elim0 x, fun j => Fin.elim0 j⟩, by
      apply Subtype.ext; funext x; exact Fin.elim0 x⟩, ?_⟩
    rintro ⟨⟨f, _⟩, _⟩
    apply Subtype.ext; apply Subtype.ext; funext x; exact Fin.elim0 x
  exact_mod_cast h

lemma fixCount_id_succ (k : ℕ) :
    (fixCount (k + 1) false false : ℤ) = ∑ j : Slice, iterStep k j := by
  classical
  letI : Fintype (ValidSeq (k + 1)) := Subtype.fintype _
  unfold fixCount
  have heq : Fintype.card { f : ValidSeq (k + 1) // symSeq false false f = f } =
      Fintype.card (ValidSeq (k + 1)) := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun f => ⟨f, by apply Subtype.ext; funext x; rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [heq]
  let e : ValidSeq (k + 1) ≃ Σ j : Slice, { f : ValidSeq (k + 1) // f.1 ⟨k, Nat.lt_succ_self k⟩ = j } :=
    { toFun := fun f => ⟨f.1 ⟨k, Nat.lt_succ_self k⟩, ⟨f, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨j, ⟨f, rfl⟩⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  push_cast
  exact Finset.sum_congr rfl fun j _ => card_validSeq_ending k j

/-- Degree-4 base identity for `iterStep` (verified by `decide`). -/
lemma iterStep_rec_base :
    ∀ j : Slice,
      iterStep 4 j - 9 * iterStep 3 j + 28 * iterStep 2 j - 33 * iterStep 1 j + 9 * iterStep 0 j = 0 := by
  decide

/-- Degree-4 linear recurrence for `iterStep k` for all `k`. -/
lemma iterStep_rec (k : ℕ) :
    ∀ j : Slice,
      iterStep (k + 4) j - 9 * iterStep (k + 3) j + 28 * iterStep (k + 2) j -
        33 * iterStep (k + 1) j + 9 * iterStep k j = 0 := by
  induction k with
  | zero => exact iterStep_rec_base
  | succ k ih =>
    intro j
    have hstep : step (fun i =>
        iterStep (k + 4) i - 9 * iterStep (k + 3) i + 28 * iterStep (k + 2) i -
          33 * iterStep (k + 1) i + 9 * iterStep k i) j = 0 := by
      have : (fun i => iterStep (k + 4) i - 9 * iterStep (k + 3) i + 28 * iterStep (k + 2) i -
          33 * iterStep (k + 1) i + 9 * iterStep k i) = fun _ => 0 := funext ih
      rw [this, step_zero]
    have hlin : step (fun i =>
        iterStep (k + 4) i - 9 * iterStep (k + 3) i + 28 * iterStep (k + 2) i -
          33 * iterStep (k + 1) i + 9 * iterStep k i) j =
        iterStep (k + 5) j - 9 * iterStep (k + 4) j + 28 * iterStep (k + 3) j -
          33 * iterStep (k + 2) j + 9 * iterStep (k + 1) j := by
      simp only [iterStep, step]
      have h1 : ∀ (a b c d e : Slice → ℤ),
          (∑ i : Slice, if compat i j then a i - 9 * b i + 28 * c i - 33 * d i + 9 * e i else 0) =
          (∑ i : Slice, if compat i j then a i else 0) -
          9 * (∑ i : Slice, if compat i j then b i else 0) +
          28 * (∑ i : Slice, if compat i j then c i else 0) -
          33 * (∑ i : Slice, if compat i j then d i else 0) +
          9 * (∑ i : Slice, if compat i j then e i else 0) := by
        intro a b c d e
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      exact h1 _ _ _ _ _
    linarith

lemma fixCount_id_rec (k : ℕ) :
    (fixCount (k + 5) false false : ℤ) - 9 * fixCount (k + 4) false false +
      28 * fixCount (k + 3) false false - 33 * fixCount (k + 2) false false +
      9 * fixCount (k + 1) false false = 0 := by
  simp only [fixCount_id_succ]
  calc
    (∑ j : Slice, iterStep (k + 4) j) - 9 * (∑ j : Slice, iterStep (k + 3) j) +
        28 * (∑ j : Slice, iterStep (k + 2) j) - 33 * (∑ j : Slice, iterStep (k + 1) j) +
        9 * (∑ j : Slice, iterStep k j)
      = ∑ j : Slice, (iterStep (k + 4) j - 9 * iterStep (k + 3) j + 28 * iterStep (k + 2) j -
          33 * iterStep (k + 1) j + 9 * iterStep k j) := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    _ = 0 := Finset.sum_eq_zero fun j _ => iterStep_rec k j

/-- Initial values of `id(n)` for `n = 1, 2, 3, 4`. -/
lemma fixCount_id_1 : (fixCount 1 false false : ℤ) = 12 := by rw [fixCount_id_succ 0]; decide
lemma fixCount_id_2 : (fixCount 2 false false : ℤ) = 79 := by rw [fixCount_id_succ 1]; decide
lemma fixCount_id_3 : (fixCount 3 false false : ℤ) = 408 := by rw [fixCount_id_succ 2]; decide
lemma fixCount_id_4 : (fixCount 4 false false : ℤ) = 1847 := by rw [fixCount_id_succ 3]; decide

/-! ### Vertical reflection count: `V(n) = n + 1` -/

def vSlice0 : Slice := ⟨((0, 0), (1, 0)), by decide⟩
def vSlice1 : Slice := ⟨((0, 1), (1, 1)), by decide⟩

lemma flipVSlice_eq_self_iff :
    ∀ s : Slice, flipVSlice s = s ↔ s = vSlice0 ∨ s = vSlice1 := by decide

lemma compat_vSlice00 : compat vSlice0 vSlice0 = true := by decide
lemma compat_vSlice01 : compat vSlice0 vSlice1 = true := by decide
lemma compat_vSlice11 : compat vSlice1 vSlice1 = true := by decide
lemma compat_vSlice10 : compat vSlice1 vSlice0 = false := by decide

lemma fixCount_V (n : ℕ) : (fixCount n true false : ℤ) = n + 1 := by
  classical
  letI : Fintype (ValidSeq n) := Subtype.fintype _
  unfold fixCount
  let toF (k : Fin (n + 1)) : { f : ValidSeq n // symSeq true false f = f } :=
    ⟨⟨fun j => if j.val < k.val then vSlice0 else vSlice1, by
        intro j
        by_cases h1 : j.val < k.val <;> by_cases h2 : j.val + 1 < k.val
        · simp [h1, h2, compat_vSlice00]
        · simp [h1, h2, compat_vSlice01]
        · omega
        · simp [h1, h2, compat_vSlice11]⟩,
     by
      apply Subtype.ext; funext j
      dsimp [symSeq, symSlice]
      split_ifs
      · exact (flipVSlice_eq_self_iff vSlice0).mpr (Or.inl rfl)
      · exact (flipVSlice_eq_self_iff vSlice1).mpr (Or.inr rfl)⟩
  have hbij : Function.Bijective toF := by
    constructor
    · intro k1 k2 h
      have h' : ∀ j : Fin n, (if j.val < k1.val then vSlice0 else vSlice1) =
          (if j.val < k2.val then vSlice0 else vSlice1) :=
        fun j => congrArg (fun x => x.1.1 j) h
      have hne : vSlice0 ≠ vSlice1 := by decide
      ext
      by_contra hneq
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · have hj := h' ⟨k1.val, by have := k2.isLt; omega⟩
        simp [lt_irrefl, hlt, hne.symm] at hj
      · have hj := h' ⟨k2.val, by have := k1.isLt; omega⟩
        simp [lt_irrefl, hgt, hne] at hj
    · rintro ⟨⟨f, hf⟩, hfix⟩
      have hfv : ∀ j : Fin n, f j = vSlice0 ∨ f j = vSlice1 := fun j =>
        (flipVSlice_eq_self_iff (f j)).mp (by
          have := congrArg (fun x : ValidSeq n => x.1 j) hfix
          simpa [symSeq, symSlice] using this)
      have hmono : ∀ (i j : Fin n), i.val ≤ j.val → f i = vSlice1 → f j = vSlice1 := by
        intro i j hij hi
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
        induction d generalizing j with
        | zero =>
          have : i = j := Fin.ext (by omega)
          rw [← this]; exact hi
        | succ d ih =>
          have hjlt := j.isLt
          have hjprev : i.val + d < n := by omega
          have hprev := ih ⟨i.val + d, hjprev⟩ (by dsimp; omega) (by dsimp)
          have hcomp : compat (f ⟨i.val + d, hjprev⟩) (f ⟨i.val + d + 1, by omega⟩) = true :=
            validSeq_adj ⟨f, hf⟩ (i.val + d) (by omega)
          have hjeq : (⟨i.val + d + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
          rw [hprev, hjeq] at hcomp
          rcases hfv j with h0 | h1
          · rw [h0, compat_vSlice10] at hcomp; exact absurd hcomp (by decide)
          · exact h1
      let S := Finset.univ.filter (fun j : Fin n => f j = vSlice0)
      refine ⟨⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext; funext j
      dsimp [toF]
      have hiff : ∀ x : Fin n, x ∈ S ↔ x.val < S.card := by
        have hdown : ∀ (x y : Fin n), x.val ≤ y.val → y ∈ S → x ∈ S := by
          intro x y hxy hy
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          rcases hfv x with h0 | h1
          · exact h0
          · have := hmono x y hxy h1
            rw [this] at hy; exact absurd hy (by decide)
        intro x
        constructor
        · intro hx
          have hsub : Finset.univ.filter (fun y : Fin n => y.val ≤ x.val) ⊆ S := by
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            exact hdown y x hy hx
          have hle := Finset.card_le_card hsub
          have hcardL : (Finset.univ.filter (fun y : Fin n => y.val ≤ x.val)).card = x.val + 1 := by
            have heq : (Finset.univ.filter (fun y : Fin n => y.val ≤ x.val)).image Fin.val =
                Finset.range (x.val + 1) := by
              ext m
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_range]
              constructor
              · rintro ⟨y, hy, rfl⟩; omega
              · intro hm; exact ⟨⟨m, by have := x.isLt; omega⟩, by dsimp; omega, rfl⟩
            rw [← Finset.card_image_of_injective _ Fin.val_injective, heq, Finset.card_range]
          omega
        · intro hlt
          by_contra hx
          have hsub : S ⊆ Finset.univ.filter (fun y : Fin n => y.val < x.val) := by
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hge
            exact hx (hdown x y (by omega) hy)
          have hle := Finset.card_le_card hsub
          have hcardL : (Finset.univ.filter (fun y : Fin n => y.val < x.val)).card = x.val := by
            have heq : (Finset.univ.filter (fun y : Fin n => y.val < x.val)).image Fin.val =
                Finset.range x.val := by
              ext m
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_range]
              constructor
              · rintro ⟨y, hy, rfl⟩; omega
              · intro hm; exact ⟨⟨m, by have := x.isLt; omega⟩, by dsimp; omega, rfl⟩
            rw [← Finset.card_image_of_injective _ Fin.val_injective, heq, Finset.card_range]
          omega
      by_cases hlt : j.val < S.card
      · simp only [hlt, ↓reduceIte]
        have hjS := (hiff j).mpr hlt
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
        exact hjS.symm
      · simp only [hlt, ↓reduceIte]
        have hjS : j ∉ S := fun h => hlt ((hiff j).mp h)
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
        rcases hfv j with h0 | h1
        · exact absurd h0 hjS
        · exact h1.symm
  have hcard := Fintype.card_of_bijective hbij
  rw [Fintype.card_fin] at hcard
  exact_mod_cast hcard.symm

/-! ### Horizontal reflection count: `H(2m) = 3^m`, `H(2m+1) = 0` -/

def isHEven (s : Slice) : Bool := compat s (flipHSlice s)

lemma flipHSlice_ne_self : ∀ s : Slice, flipHSlice s ≠ s := by decide
lemma isHEven_back : ∀ s1 s2 : Slice, compat s1 s2 = true → isHEven s2 = true → isHEven s1 = true := by
  decide
lemma isHEven_compat : ∀ s1 s2 : Slice, isHEven s1 = true → isHEven s2 = true → compat s1 s2 = true := by
  decide
lemma card_isHEven : Fintype.card { s : Slice // isHEven s = true } = 3 := by decide

lemma fixCount_H_odd (m : ℕ) : (fixCount (2 * m + 1) false true : ℤ) = 0 := by
  classical
  letI : Fintype (ValidSeq (2 * m + 1)) := Subtype.fintype _
  unfold fixCount
  have hemp : IsEmpty { f : ValidSeq (2 * m + 1) // symSeq false true f = f } := by
    refine ⟨fun ⟨f, hf⟩ => ?_⟩
    let mid : Fin (2 * m + 1) := ⟨m, by omega⟩
    have hmid : mid.rev = mid := by ext; simp [mid, Fin.rev]; omega
    have h := congrArg (fun x : ValidSeq (2 * m + 1) => x.1 mid) hf
    simp only [symSeq, symSlice, Bool.false_eq_true, ↓reduceIte, hmid] at h
    exact flipHSlice_ne_self (f.1 mid) h
  have h0 : Fintype.card { f : ValidSeq (2 * m + 1) // symSeq false true f = f } = 0 :=
    Fintype.card_eq_zero
  exact_mod_cast h0

lemma fixCount_H_even (m : ℕ) : (fixCount (2 * m) false true : ℤ) = 3 ^ m := by
  classical
  letI : Fintype (ValidSeq (2 * m)) := Subtype.fintype _
  unfold fixCount
  let toF (g : Fin m → { s : Slice // isHEven s = true }) :
      { f : ValidSeq (2 * m) // symSeq false true f = f } :=
    ⟨⟨fun j => if hj : j.val < m then (g ⟨j.val, hj⟩).1
               else flipHSlice (g ⟨2 * m - 1 - j.val, by have := j.isLt; omega⟩).1, by
        intro jFin
        have hj : jFin.val + 1 < 2 * m := by have := jFin.isLt; omega
        by_cases h1 : jFin.val + 1 < m
        · have h0 : jFin.val < m := by omega
          simp only [h0, h1, ↓reduceDIte]
          exact isHEven_compat _ _ (g ⟨jFin.val, h0⟩).2 (g ⟨jFin.val + 1, h1⟩).2
        · by_cases h0 : jFin.val < m
          · have hidx : 2 * m - 1 - (jFin.val + 1) = jFin.val := by omega
            simp only [h0, h1, ↓reduceDIte]
            have hfin : (⟨2 * m - 1 - (jFin.val + 1), by omega⟩ : Fin m) = ⟨jFin.val, h0⟩ :=
              Fin.ext hidx
            rw [hfin]
            exact (g ⟨jFin.val, h0⟩).2
          · simp only [h0, h1, ↓reduceDIte]
            rw [compat_flipH]
            exact isHEven_compat _ _
              (g ⟨2 * m - 1 - (jFin.val + 1), by omega⟩).2 (g ⟨2 * m - 1 - jFin.val, by omega⟩).2⟩,
     by
      apply Subtype.ext; funext j
      dsimp [symSeq, symSlice, Fin.rev]
      have hjlt := j.isLt
      by_cases hj : j.val < m
      · have hrev : ¬ (2 * m - (j.val + 1) < m) := by omega
        simp only [hj, hrev, ↓reduceDIte, flipHSlice_invol]
        exact congrArg (fun k => (g k).1) (Fin.ext (by dsimp; omega))
      · have hrev : 2 * m - (j.val + 1) < m := by omega
        simp only [hj, hrev, ↓reduceDIte]
        exact congrArg (fun k => flipHSlice (g k).1) (Fin.ext (by dsimp; omega))⟩
  have hbij : Function.Bijective toF := by
    constructor
    · intro g1 g2 h
      funext k
      have hk := congrArg (fun x => x.1.1 ⟨k.val, by have := k.isLt; omega⟩) h
      dsimp [toF] at hk
      simp only [k.isLt, ↓reduceDIte] at hk
      exact Subtype.ext hk
    · rintro ⟨⟨f, hf⟩, hfix⟩
      have hsym : ∀ j : Fin (2 * m), flipHSlice (f j.rev) = f j := fun j => by
        simpa [symSeq, symSlice] using congrArg (fun x : ValidSeq (2 * m) => x.1 j) hfix
      have hall : ∀ (k : ℕ) (hk : k < m), isHEven (f ⟨k, by omega⟩) = true := by
        intro k hk
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_sub_one_of_lt hk)
        induction d generalizing k with
        | zero =>
          have hrev : (⟨k + 1, by omega⟩ : Fin (2 * m)).rev = ⟨k, by omega⟩ := by
            ext; simp [Fin.rev]; omega
          have hmid : compat (f ⟨k, by omega⟩) (f ⟨k + 1, by omega⟩) = true :=
            validSeq_adj ⟨f, hf⟩ k (by omega)
          have heq : f ⟨k + 1, by omega⟩ = flipHSlice (f ⟨k, by omega⟩) := by
            rw [← hsym ⟨k + 1, by omega⟩, hrev]
          rw [heq] at hmid
          exact hmid
        | succ d ih =>
          have hnext := ih (k + 1) (by omega) (by omega)
          exact isHEven_back _ _ (validSeq_adj ⟨f, hf⟩ k (by omega)) hnext
      refine ⟨fun k => ⟨f ⟨k.val, by have := k.isLt; omega⟩, hall k.val k.isLt⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext; funext j
      dsimp [toF]
      by_cases hj : j.val < m
      · simp [hj]
      · simp only [hj, ↓reduceDIte]
        have hrev : j.rev = ⟨2 * m - 1 - j.val, by have := j.isLt; omega⟩ := by
          ext; simp [Fin.rev]; omega
        rw [← hrev, hsym j]
  have hcard := Fintype.card_of_bijective hbij
  rw [Fintype.card_fun, card_isHEven, Fintype.card_fin] at hcard
  exact_mod_cast hcard.symm

/-! ### 180-degree rotation count `R(n)` and its recurrence `(1 - 3x^2)(1 - x - x^2)` -/

def isRMid (s : Slice) : Bool := decide (symSlice true true s = s)
def isREven (s : Slice) : Bool := compat s (symSlice true true s)
def vRMid (s : Slice) : ℤ := if isRMid s then 1 else 0
def vREven (s : Slice) : ℤ := if isREven s then 1 else 0

lemma fixCount_R_zero : (fixCount 0 true true : ℤ) = 1 := by
  classical
  letI : Fintype (ValidSeq 0) := Subtype.fintype _
  unfold fixCount
  have h : Fintype.card { f : ValidSeq 0 // symSeq true true f = f } = 1 := by
    refine Fintype.card_eq_one_iff.mpr ?_
    refine ⟨⟨⟨fun x => Fin.elim0 x, fun j => Fin.elim0 j⟩, by
      apply Subtype.ext; funext x; exact Fin.elim0 x⟩, ?_⟩
    rintro ⟨⟨f, _⟩, _⟩
    apply Subtype.ext; apply Subtype.ext; funext x; exact Fin.elim0 x
  exact_mod_cast h

lemma fixCount_R_odd (m : ℕ) :
    (fixCount (2 * m + 1) true true : ℤ) = ∑ j : Slice, iterStep m j * vRMid j := by
  classical
  letI : Fintype (ValidSeq (2 * m + 1)) := Subtype.fintype _
  unfold fixCount
  let e : { f : ValidSeq (2 * m + 1) // symSeq true true f = f } ≃
      Σ j : { j : Slice // isRMid j = true },
        { g : ValidSeq (m + 1) // g.1 ⟨m, Nat.lt_succ_self m⟩ = j.1 } :=
    { toFun := fun ⟨f, hf⟩ =>
        ⟨⟨f.1 ⟨m, by omega⟩, by
            simp only [isRMid, decide_eq_true_eq]
            have hmid : (⟨m, by omega⟩ : Fin (2 * m + 1)).rev = ⟨m, by omega⟩ := by
              ext; simp [Fin.rev]; omega
            have h := congrArg (fun x : ValidSeq (2 * m + 1) => x.1 ⟨m, by omega⟩) hf
            simpa [symSeq, hmid] using h⟩,
         ⟨⟨fun k => f.1 ⟨k.val, by omega⟩, fun j => validSeq_adj f j.val (by have := j.isLt; omega)⟩, rfl⟩⟩
      invFun := fun ⟨⟨j, hj⟩, ⟨g, hg⟩⟩ =>
        ⟨⟨fun x => if hx : x.val < m + 1 then g.1 ⟨x.val, hx⟩
                   else symSlice true true (g.1 ⟨2 * m - x.val, by have := x.isLt; omega⟩), by
            intro kFin
            have hk : kFin.val + 1 < 2 * m + 1 := by have := kFin.isLt; omega
            by_cases h1 : kFin.val + 1 < m + 1
            · simp only [h1, ↓reduceDIte, show kFin.val < m + 1 by omega]
              exact validSeq_adj g kFin.val h1
            · by_cases h0 : kFin.val < m + 1
              · have hkm : kFin.val = m := by omega
                have hnot : ¬ kFin.val + 1 < m + 1 := h1
                simp only [h0, hnot, ↓reduceDIte]
                have hjfix : symSlice true true j = j := by
                  simpa [isRMid, decide_eq_true_eq] using hj
                have hfin1 : (⟨kFin.val, h0⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
                  Fin.ext hkm
                have hfin2 : (⟨2 * m - (kFin.val + 1), by omega⟩ : Fin (m + 1)) =
                    ⟨m - 1, by omega⟩ := Fin.ext (by dsimp; omega)
                rw [hfin1, hfin2, hg]
                have hrev : compat (symSlice true true (g.1 ⟨m, Nat.lt_succ_self m⟩))
                    (symSlice true true (g.1 ⟨m - 1, by omega⟩)) = true := by
                  rw [compat_rot]
                  have hbase := validSeq_adj g (m - 1) (by omega)
                  have heq : (⟨m - 1 + 1, by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
                    Fin.ext (by dsimp; omega)
                  rwa [heq] at hbase
                rw [hg, hjfix] at hrev
                exact hrev
              · simp only [h0, h1, ↓reduceDIte]
                rw [compat_rot]
                have hbase := validSeq_adj g (2 * m - (kFin.val + 1)) (by omega)
                have heq : (⟨2 * m - (kFin.val + 1) + 1, by omega⟩ : Fin (m + 1)) =
                    ⟨2 * m - kFin.val, by omega⟩ := Fin.ext (by dsimp; omega)
                rwa [heq] at hbase⟩,
         by
          apply Subtype.ext; funext x
          dsimp [symSeq, Fin.rev]
          have hxlt := x.isLt
          by_cases hx : x.val < m
          · have hrev : ¬ (2 * m + 1 - (x.val + 1) < m + 1) := by omega
            have hxm : x.val < m + 1 := by omega
            simp only [hrev, hxm, ↓reduceDIte]
            rw [symSlice_comp]
            simp only [Bool.xor_self, symSlice_false_false]
            exact congrArg g.1 (Fin.ext (by dsimp; omega))
          · by_cases hxm : x.val = m
            · have hrev : 2 * m + 1 - (x.val + 1) < m + 1 := by omega
              have hx1 : x.val < m + 1 := by omega
              simp only [hrev, hx1, ↓reduceDIte]
              have hfin : (⟨2 * m + 1 - (x.val + 1), hrev⟩ : Fin (m + 1)) =
                  ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (by dsimp; omega)
              have hfin2 : (⟨x.val, hx1⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hxm
              rw [hfin, hfin2, hg]
              simpa [isRMid, decide_eq_true_eq] using hj
            · have hrev : 2 * m + 1 - (x.val + 1) < m + 1 := by omega
              have hx1 : ¬ (x.val < m + 1) := by omega
              simp only [hrev, hx1, ↓reduceDIte]
              exact congrArg (fun k => symSlice true true (g.1 k)) (Fin.ext (by dsimp; omega))⟩
      left_inv := by
        rintro ⟨⟨f, hf⟩, hfix⟩
        apply Subtype.ext; apply Subtype.ext; funext x
        have hxlt := x.isLt
        by_cases hx : x.val < m + 1
        · simp [hx]
        · simp only [hx, ↓reduceDIte]
          have h := congrArg (fun y : ValidSeq (2 * m + 1) => y.1 x) hfix
          have hrev : x.rev = ⟨2 * m - x.val, by omega⟩ := by ext; simp [Fin.rev]
          simpa [symSeq, hrev] using h
      right_inv := by
        rintro ⟨⟨j, hj⟩, ⟨⟨g, hg⟩, hglast⟩⟩
        dsimp only at hglast ⊢
        refine sigma_subtype_ext
          (fun (j : { j : Slice // isRMid j = true }) (g : ValidSeq (m + 1)) =>
            g.1 ⟨m, Nat.lt_succ_self m⟩ = j.1) ?_ ?_
        · exact Subtype.ext (by dsimp only; rw [dif_pos (Nat.lt_succ_self m)]; exact hglast)
        · apply Subtype.ext; funext k; exact dif_pos k.isLt }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  push_cast
  simp_rw [card_validSeq_ending]
  change (∑ j : { j : Slice // isRMid j = true }, iterStep m j.1) =
    ∑ j : Slice, iterStep m j * vRMid j
  have h1 : (∑ j : Slice, iterStep m j * vRMid j) =
      ∑ j ∈ Finset.univ.filter (fun j : Slice => isRMid j = true), iterStep m j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold vRMid; split_ifs <;> ring
  rw [h1]
  exact (Finset.sum_subtype (Finset.univ.filter (fun j : Slice => isRMid j = true))
    (fun j => by simp) (fun j => iterStep m j)).symm

lemma fixCount_R_even_succ (m : ℕ) :
    (fixCount (2 * (m + 1)) true true : ℤ) = ∑ j : Slice, iterStep m j * vREven j := by
  classical
  letI : Fintype (ValidSeq (2 * (m + 1))) := Subtype.fintype _
  unfold fixCount
  let e : { f : ValidSeq (2 * (m + 1)) // symSeq true true f = f } ≃
      Σ j : { j : Slice // isREven j = true },
        { g : ValidSeq (m + 1) // g.1 ⟨m, Nat.lt_succ_self m⟩ = j.1 } :=
    { toFun := fun ⟨f, hf⟩ =>
        ⟨⟨f.1 ⟨m, by omega⟩, by
            have h := validSeq_adj f m (by omega)
            have hsym := congrArg (fun x : ValidSeq (2 * (m + 1)) => x.1 ⟨m + 1, by omega⟩) hf
            have hrev : (⟨m + 1, by omega⟩ : Fin (2 * (m + 1))).rev = ⟨m, by omega⟩ := by
              ext; simp [Fin.rev]; omega
            simp only [symSeq, ↓reduceIte, hrev] at hsym
            rw [← hsym] at h
            exact h⟩,
         ⟨⟨fun k => f.1 ⟨k.val, by omega⟩, fun j => validSeq_adj f j.val (by have := j.isLt; omega)⟩, rfl⟩⟩
      invFun := fun ⟨⟨j, hj⟩, ⟨g, hg⟩⟩ =>
        ⟨⟨fun x => if hx : x.val < m + 1 then g.1 ⟨x.val, hx⟩
                   else symSlice true true (g.1 ⟨2 * (m + 1) - 1 - x.val, by have := x.isLt; omega⟩), by
            intro kFin
            have hk : kFin.val + 1 < 2 * (m + 1) := by have := kFin.isLt; omega
            by_cases h1 : kFin.val + 1 < m + 1
            · simp only [h1, ↓reduceDIte, show kFin.val < m + 1 by omega]
              exact validSeq_adj g kFin.val h1
            · by_cases h0 : kFin.val < m + 1
              · have hkm : kFin.val = m := by omega
                have hnot : ¬ kFin.val + 1 < m + 1 := h1
                simp only [h0, hnot, ↓reduceDIte]
                have hfin1 : (⟨kFin.val, h0⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
                  Fin.ext hkm
                have hfin2 : (⟨2 * (m + 1) - 1 - (kFin.val + 1), by omega⟩ : Fin (m + 1)) =
                    ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (by dsimp; omega)
                rw [hfin1, hfin2, hg]
                exact hj
              · simp only [h0, h1, ↓reduceDIte]
                rw [compat_rot]
                have hbase := validSeq_adj g (2 * (m + 1) - 1 - (kFin.val + 1)) (by omega)
                have heq : (⟨2 * (m + 1) - 1 - (kFin.val + 1) + 1, by omega⟩ : Fin (m + 1)) =
                    ⟨2 * (m + 1) - 1 - kFin.val, by omega⟩ := Fin.ext (by dsimp; omega)
                rwa [heq] at hbase⟩,
         by
          apply Subtype.ext; funext x
          dsimp [symSeq, Fin.rev]
          have hxlt := x.isLt
          by_cases hx : x.val < m + 1
          · have hrev : ¬ (2 * (m + 1) - (x.val + 1) < m + 1) := by omega
            simp only [hx, hrev, ↓reduceDIte]
            rw [symSlice_comp]
            simp only [Bool.xor_self, symSlice_false_false]
            exact congrArg g.1 (Fin.ext (by dsimp; omega))
          · have hrev : 2 * (m + 1) - (x.val + 1) < m + 1 := by omega
            simp only [hx, hrev, ↓reduceDIte]
            exact congrArg (fun k => symSlice true true (g.1 k)) (Fin.ext (by dsimp; omega))⟩
      left_inv := by
        rintro ⟨⟨f, hf⟩, hfix⟩
        apply Subtype.ext; apply Subtype.ext; funext x
        have hxlt := x.isLt
        by_cases hx : x.val < m + 1
        · simp [hx]
        · simp only [hx, ↓reduceDIte]
          have h := congrArg (fun y : ValidSeq (2 * (m + 1)) => y.1 x) hfix
          have hrev : x.rev = ⟨2 * (m + 1) - 1 - x.val, by omega⟩ := by ext; simp [Fin.rev]; omega
          simpa [symSeq, hrev] using h
      right_inv := by
        rintro ⟨⟨j, hj⟩, ⟨⟨g, hg⟩, hglast⟩⟩
        dsimp only at hglast ⊢
        refine sigma_subtype_ext
          (fun (j : { j : Slice // isREven j = true }) (g : ValidSeq (m + 1)) =>
            g.1 ⟨m, Nat.lt_succ_self m⟩ = j.1) ?_ ?_
        · exact Subtype.ext (by dsimp only; rw [dif_pos (Nat.lt_succ_self m)]; exact hglast)
        · apply Subtype.ext; funext k; exact dif_pos k.isLt }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  push_cast
  simp_rw [card_validSeq_ending]
  change (∑ j : { j : Slice // isREven j = true }, iterStep m j.1) =
    ∑ j : Slice, iterStep m j * vREven j
  have h1 : (∑ j : Slice, iterStep m j * vREven j) =
      ∑ j ∈ Finset.univ.filter (fun j : Slice => isREven j = true), iterStep m j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold vREven; split_ifs <;> ring
  rw [h1]
  exact (Finset.sum_subtype (Finset.univ.filter (fun j : Slice => isREven j = true))
    (fun j => by simp) (fun j => iterStep m j)).symm

/-- Adjoint vectors for the even and odd steps of `R`'s recurrence. -/
def wEven (i : Slice) : ℤ :=
  rstep (rstep vREven) i - rstep (rstep vRMid) i - 4 * rstep vREven i +
    3 * rstep vRMid i + 3 * vREven i

def wOdd (i : Slice) : ℤ :=
  rstep (rstep vRMid) i - rstep vREven i - 4 * rstep vRMid i +
    3 * vREven i + 3 * vRMid i

lemma wEven_eq_zero : ∀ i : Slice, wEven i = 0 := by decide

lemma dot_wOdd_0 : (∑ i : Slice, iterStep 0 i * wOdd i) = 0 := by decide
lemma dot_wOdd_1 : (∑ i : Slice, iterStep 1 i * wOdd i) = 0 := by decide
lemma dot_wOdd_2 : (∑ i : Slice, iterStep 2 i * wOdd i) = 0 := by decide
lemma dot_wOdd_3 : (∑ i : Slice, iterStep 3 i * wOdd i) = 0 := by decide

lemma dot_wOdd_all (k : ℕ) : (∑ i : Slice, iterStep k i * wOdd i) = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => exact dot_wOdd_0
    | 1 => exact dot_wOdd_1
    | 2 => exact dot_wOdd_2
    | 3 => exact dot_wOdd_3
    | m + 4 =>
      have hrec : (∑ i : Slice, (iterStep (m + 4) i - 9 * iterStep (m + 3) i +
          28 * iterStep (m + 2) i - 33 * iterStep (m + 1) i + 9 * iterStep m i) * wOdd i) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [iterStep_rec m i, zero_mul]
      have hexp : (∑ i : Slice, (iterStep (m + 4) i - 9 * iterStep (m + 3) i +
          28 * iterStep (m + 2) i - 33 * iterStep (m + 1) i + 9 * iterStep m i) * wOdd i) =
          (∑ i : Slice, iterStep (m + 4) i * wOdd i) -
          9 * (∑ i : Slice, iterStep (m + 3) i * wOdd i) +
          28 * (∑ i : Slice, iterStep (m + 2) i * wOdd i) -
          33 * (∑ i : Slice, iterStep (m + 1) i * wOdd i) +
          9 * (∑ i : Slice, iterStep m i * wOdd i) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hexp, ih (m + 3) (by omega), ih (m + 2) (by omega),
          ih (m + 1) (by omega), ih m (by omega)] at hrec
      linarith

/-- Initial values of `R(n)` for `n = 1, 2, 3, 4`. -/
lemma fixCount_R_1 : (fixCount 1 true true : ℤ) = 2 := by rw [fixCount_R_odd 0]; decide
lemma fixCount_R_2 : (fixCount 2 true true : ℤ) = 7 := by rw [fixCount_R_even_succ 0]; decide
lemma fixCount_R_3 : (fixCount 3 true true : ℤ) = 12 := by rw [fixCount_R_odd 1]; decide
lemma fixCount_R_4 : (fixCount 4 true true : ℤ) = 31 := by rw [fixCount_R_even_succ 1]; decide

/-- Recurrence for `R(n)` for all `n ≥ 4`. -/
lemma fixCount_R_rec (n : ℕ) (hn : 4 ≤ n) :
    (fixCount n true true : ℤ) - fixCount (n - 1) true true -
      4 * fixCount (n - 2) true true + 3 * fixCount (n - 3) true true +
      3 * fixCount (n - 4) true true = 0 := by
  by_cases h4 : n = 4
  · subst h4
    rw [fixCount_R_4, fixCount_R_3, fixCount_R_2, fixCount_R_1, fixCount_R_zero]
    norm_num
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm3 : 3 ≤ m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have h1 : n - 1 = 2 * (k + 2) + 1 := by omega
      have h2 : n - 2 = 2 * (k + 2) := by omega
      have h3 : n - 3 = 2 * (k + 1) + 1 := by omega
      have h4' : n - 4 = 2 * (k + 1) := by omega
      have hn6 : n = 2 * (k + 3) := by omega
      rw [h1, h2, h3, h4', hn6, fixCount_R_even_succ (k + 2), fixCount_R_odd (k + 2),
          fixCount_R_even_succ (k + 1), fixCount_R_odd (k + 1), fixCount_R_even_succ k]
      simp only [iterStep, dot_step_eq_dot_rstep]
      calc
        (∑ i : Slice, iterStep k i * rstep (rstep vREven) i) -
            (∑ i : Slice, iterStep k i * rstep (rstep vRMid) i) -
            4 * (∑ i : Slice, iterStep k i * rstep vREven i) +
            3 * (∑ i : Slice, iterStep k i * rstep vRMid i) +
            3 * (∑ i : Slice, iterStep k i * vREven i)
          = ∑ i : Slice, iterStep k i * wEven i := by
              simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => by unfold wEven; ring
        _ = 0 := Finset.sum_eq_zero fun i _ => by rw [wEven_eq_zero i, mul_zero]
    · have hm2 : 2 ≤ m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      have h1 : n - 1 = 2 * (k + 2) := by omega
      have h2 : n - 2 = 2 * (k + 1) + 1 := by omega
      have h3 : n - 3 = 2 * (k + 1) := by omega
      have h4' : n - 4 = 2 * k + 1 := by omega
      have hn5 : n = 2 * (k + 2) + 1 := by omega
      rw [h1, h2, h3, h4', hn5, fixCount_R_odd (k + 2), fixCount_R_even_succ (k + 1),
          fixCount_R_odd (k + 1), fixCount_R_even_succ k, fixCount_R_odd k]
      simp only [iterStep, dot_step_eq_dot_rstep]
      calc
        (∑ i : Slice, iterStep k i * rstep (rstep vRMid) i) -
            (∑ i : Slice, iterStep k i * rstep vREven i) -
            4 * (∑ i : Slice, iterStep k i * rstep vRMid i) +
            3 * (∑ i : Slice, iterStep k i * vREven i) +
            3 * (∑ i : Slice, iterStep k i * vRMid i)
          = ∑ i : Slice, iterStep k i * wOdd i := by
              simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => by unfold wOdd; ring
        _ = 0 := dot_wOdd_all k

/-! ## Section 5: Formal power series identities and Colin Barker's conjectures -/

open PowerSeries

private lemma coeff_mul_X_pow (f : PowerSeries ℤ) (k n : ℕ) :
    coeff n (f * X ^ k) = if k ≤ n then coeff (n - k) f else 0 := by
  rw [coeff_mul]
  by_cases hkn : k ≤ n
  · simp only [hkn, ↓reduceIte]
    rw [Finset.sum_eq_single (n - k, k)]
    · simp [coeff_X_pow]
    · rintro ⟨a, b⟩ hab hne
      rw [coeff_X_pow]
      have hbk : b ≠ k := by
        intro hb
        apply hne
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
        ext <;> dsimp <;> omega
      simp [hbk]
    · intro hnot
      exfalso; apply hnot
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  · simp only [hkn, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    rintro ⟨a, b⟩ hab
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [coeff_X_pow, if_neg (by omega), mul_zero]

private lemma series_id :
    PowerSeries.mk (fun n => (fixCount n false false : ℤ)) *
      ((1 - 3 * (X : PowerSeries ℤ)) ^ 2 * (1 - 3 * X + X ^ 2)) =
    1 + 3 * X - X ^ 2 := by
  let S : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n false false : ℤ))
  have hexp :
      S * ((1 - 3 * (X : PowerSeries ℤ)) ^ 2 * (1 - 3 * X + X ^ 2)) =
      S - C 9 * (S * X ^ 1) + C 28 * (S * X ^ 2) - C 33 * (S * X ^ 3) + C 9 * (S * X ^ 4) := by
    simp only [map_ofNat]; ring
  have hrhs : (1 : PowerSeries ℤ) + 3 * X - X ^ 2 = 1 + C 3 * X ^ 1 - X ^ 2 := by
    simp only [map_ofNat]; ring
  rw [show PowerSeries.mk (fun n => (fixCount n false false : ℤ)) = S from rfl, hexp, hrhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow, coeff_one, coeff_X_pow, S, coeff_mk]
  match n with
  | 0 => simp [fixCount_id_zero]
  | 1 => simp [fixCount_id_zero, fixCount_id_1]
  | 2 => simp [fixCount_id_zero, fixCount_id_1, fixCount_id_2]
  | 3 => simp [fixCount_id_zero, fixCount_id_1, fixCount_id_2, fixCount_id_3]
  | 4 => simp [fixCount_id_zero, fixCount_id_1, fixCount_id_2, fixCount_id_3, fixCount_id_4]
  | k + 5 =>
    have hrec := fixCount_id_rec k
    simp only [show 1 ≤ k + 5 by omega, show 2 ≤ k + 5 by omega, show 3 ≤ k + 5 by omega,
      show 4 ≤ k + 5 by omega, ↓reduceIte, show k + 5 ≠ 0 by omega, show k + 5 ≠ 1 by omega,
      show k + 5 ≠ 2 by omega, mul_zero, add_zero, sub_zero]
    have h1 : k + 5 - 1 = k + 4 := by omega
    have h2 : k + 5 - 2 = k + 3 := by omega
    have h3 : k + 5 - 3 = k + 2 := by omega
    have h4 : k + 5 - 4 = k + 1 := by omega
    rw [h1, h2, h3, h4]
    linarith

private lemma series_V :
    PowerSeries.mk (fun n => (fixCount n true false : ℤ)) * (1 - (X : PowerSeries ℤ)) ^ 2 = 1 := by
  let S : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n true false : ℤ))
  have hexp : S * (1 - (X : PowerSeries ℤ)) ^ 2 = S - C 2 * (S * X ^ 1) + S * X ^ 2 := by
    simp only [map_ofNat]; ring
  rw [show PowerSeries.mk (fun n => (fixCount n true false : ℤ)) = S from rfl, hexp]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow, coeff_one, S, coeff_mk]
  match n with
  | 0 => simp [fixCount_V]
  | 1 => simp [fixCount_V]
  | k + 2 =>
    simp only [show 1 ≤ k + 2 by omega, show 2 ≤ k + 2 by omega, ↓reduceIte,
      show k + 2 ≠ 0 by omega, fixCount_V]
    have h1 : k + 2 - 1 = k + 1 := by omega
    have h2 : k + 2 - 2 = k := by omega
    rw [h1, h2]
    push_cast; ring

private lemma series_H :
    PowerSeries.mk (fun n => (fixCount n false true : ℤ)) * (1 - 3 * (X : PowerSeries ℤ) ^ 2) = 1 := by
  let S : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n false true : ℤ))
  have hexp : S * (1 - 3 * (X : PowerSeries ℤ) ^ 2) = S - C 3 * (S * X ^ 2) := by
    simp only [map_ofNat]; ring
  rw [show PowerSeries.mk (fun n => (fixCount n false true : ℤ)) = S from rfl, hexp]
  ext n
  simp only [map_sub, coeff_C_mul, coeff_mul_X_pow, coeff_one, S, coeff_mk]
  match n with
  | 0 => simp [fixCount_H_even 0]
  | 1 => simp [fixCount_H_odd 0]
  | k + 2 =>
    simp only [show 2 ≤ k + 2 by omega, ↓reduceIte, show k + 2 ≠ 0 by omega,
      show k + 2 - 2 = k by omega]
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have h2 : m + m + 2 = 2 * (m + 1) := by omega
      have h0 : m + m = 2 * m := by omega
      rw [h2, h0, fixCount_H_even (m + 1), fixCount_H_even m]
      ring
    · have h2 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
      rw [h2, fixCount_H_odd (m + 1), fixCount_H_odd m]
      ring

private lemma series_R :
    PowerSeries.mk (fun n => (fixCount n true true : ℤ)) *
      ((1 - 3 * (X : PowerSeries ℤ) ^ 2) * (1 - X - X ^ 2)) =
    1 + X + X ^ 2 := by
  let S : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n true true : ℤ))
  have hexp :
      S * ((1 - 3 * (X : PowerSeries ℤ) ^ 2) * (1 - X - X ^ 2)) =
      S - S * X ^ 1 - C 4 * (S * X ^ 2) + C 3 * (S * X ^ 3) + C 3 * (S * X ^ 4) := by
    simp only [map_ofNat]; ring
  have hrhs : (1 : PowerSeries ℤ) + X + X ^ 2 = 1 + X ^ 1 + X ^ 2 := by ring
  rw [show PowerSeries.mk (fun n => (fixCount n true true : ℤ)) = S from rfl, hexp, hrhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow, coeff_one, coeff_X_pow, S, coeff_mk]
  match n with
  | 0 => simp [fixCount_R_zero]
  | 1 => simp [fixCount_R_zero, fixCount_R_1]
  | 2 => simp [fixCount_R_zero, fixCount_R_1, fixCount_R_2]
  | 3 => simp [fixCount_R_zero, fixCount_R_1, fixCount_R_2, fixCount_R_3]
  | k + 4 =>
    have hrec := fixCount_R_rec (k + 4) (by omega)
    simp only [show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega,
      show 4 ≤ k + 4 by omega, ↓reduceIte, show k + 4 ≠ 0 by omega, show k + 4 ≠ 1 by omega,
      show k + 4 ≠ 2 by omega, add_zero]
    linarith

private lemma gf_identity :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - (X : PowerSeries ℤ)) ^ 2 * (1 - 3 * X) ^ 2 *
        (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)) =
    (1 - 2 * X) *
      (1 - 6 * X + 17 * X ^ 2 - 18 * X ^ 3 - 2 * X ^ 4 + 7 * X ^ 5 + 6 * X ^ 6 - 3 * X ^ 7) := by
  let S_a : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  let S_id : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n false false : ℤ))
  let S_V : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n true false : ℤ))
  let S_H : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n false true : ℤ))
  let S_R : PowerSeries ℤ := PowerSeries.mk (fun n => (fixCount n true true : ℤ))
  have hsum : C 4 * S_a = S_id + S_V + S_H + S_R := by
    ext n
    simp only [S_a, S_id, S_V, S_H, S_R, map_add, coeff_C_mul, coeff_mk]
    have hb : ((4 * a n : ℕ) : ℤ) =
        ((fixCount n false false + fixCount n true false +
          fixCount n false true + fixCount n true true : ℕ) : ℤ) :=
      congrArg Nat.cast (burnside_four_mul n)
    push_cast at hb
    exact hb
  let D : PowerSeries ℤ :=
    (1 - X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)
  let N : PowerSeries ℤ :=
    (1 - 2 * X) *
      (1 - 6 * X + 17 * X ^ 2 - 18 * X ^ 3 - 2 * X ^ 4 + 7 * X ^ 5 + 6 * X ^ 6 - 3 * X ^ 7)
  have h4mul : C 4 * (S_a * D) = C 4 * N := by
    calc
      C 4 * (S_a * D) = (C 4 * S_a) * D := by ring
      _ = (S_id + S_V + S_H + S_R) * D := by rw [hsum]
      _ = (S_id * ((1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2))) *
            ((1 - X) ^ 2 * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)) +
          (S_V * (1 - X) ^ 2) *
            ((1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)) +
          (S_H * (1 - 3 * X ^ 2)) *
            ((1 - X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2)) +
          (S_R * ((1 - 3 * X ^ 2) * (1 - X - X ^ 2))) *
            ((1 - X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2)) := by
              dsimp [D]; ring
      _ = (1 + 3 * X - X ^ 2) * ((1 - X) ^ 2 * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)) +
          1 * ((1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)) +
          1 * ((1 - X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2)) +
          (1 + X + X ^ 2) * ((1 - X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 3 * X + X ^ 2)) := by
            rw [series_id, series_V, series_H, series_R]
      _ = C 4 * N := by dsimp [N]; simp only [map_ofNat]; ring
  ext n
  have h := congrArg (coeff n) h4mul
  simp only [coeff_C_mul] at h
  dsimp [S_a, D, N] at h
  linarith

private lemma recurrence_identity :
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 12 * a (n - 1) - 54 * a (n - 2) + 98 * a (n - 3) + 17 * a (n - 4) -
        346 * a (n - 5) + 505 * a (n - 6) - 210 * a (n - 7) - 120 * a (n - 8) +
        126 * a (n - 9) - 27 * a (n - 10) := by
  intro n hn
  let S : PowerSeries ℤ := PowerSeries.mk (fun k => (a k : ℤ))
  have hL :
      S * ((1 - (X : PowerSeries ℤ)) ^ 2 * (1 - 3 * X) ^ 2 *
        (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) * (1 - 3 * X ^ 2)) =
      S - C 12 * (S * X ^ 1) + C 54 * (S * X ^ 2) - C 98 * (S * X ^ 3) - C 17 * (S * X ^ 4) +
        C 346 * (S * X ^ 5) - C 505 * (S * X ^ 6) + C 210 * (S * X ^ 7) + C 120 * (S * X ^ 8) -
        C 126 * (S * X ^ 9) + C 27 * (S * X ^ 10) := by
    simp only [map_ofNat]; ring
  have hR : (1 - 2 * (X : PowerSeries ℤ)) *
        (1 - 6 * X + 17 * X ^ 2 - 18 * X ^ 3 - 2 * X ^ 4 + 7 * X ^ 5 + 6 * X ^ 6 - 3 * X ^ 7) =
      1 - C 8 * X ^ 1 + C 29 * X ^ 2 - C 52 * X ^ 3 + C 34 * X ^ 4 + C 11 * X ^ 5 -
        C 8 * X ^ 6 - C 15 * X ^ 7 + C 6 * X ^ 8 := by
    simp only [map_ofNat]; ring
  have hgf := gf_identity
  change S * _ = _ at hgf
  rw [hL, hR] at hgf
  have hc := congrArg (coeff n) hgf
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow, coeff_one, coeff_X_pow, S, coeff_mk] at hc
  simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
    show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
    show n ≠ 8 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
    show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega,
    ↓reduceIte, mul_zero, add_zero, sub_zero] at hc
  linarith

end OMA.P_oeis_a321614

theorem OMA.solution : type_of% @OMA.S_oeis_a321614.main :=
  ⟨OMA.P_oeis_a321614.gf_identity, OMA.P_oeis_a321614.recurrence_identity⟩
