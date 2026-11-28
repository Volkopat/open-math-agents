import OMAStatements.S_oeis_a092434
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

namespace OMA.S_oeis_a092434_Proof

open OMA.S_oeis_a092434

/-! ### Part 1: Basic properties of `entry` and binary `binEntry` -/

private lemma entry_congr {w₁ w₂ : ℕ → ℕ} :
    ∀ {r i : ℕ}, (∀ j, i ≤ j → j ≤ i + r → w₁ j = w₂ j) →
      entry w₁ r i = entry w₂ r i
  | 0, i, h => h i le_rfl (by omega)
  | r + 1, i, h => by
    simp only [entry]
    rw [entry_congr (r := r) (i := i) (fun j h1 h2 => h j h1 (by omega)),
        entry_congr (r := r) (i := i + 1) (fun j h1 h2 => h j (by omega) (by omega))]

private lemma entry_two_mul (u : ℕ → ℕ) :
    ∀ (r i : ℕ), entry (fun j => 2 * u j) r i = 2 * entry u r i
  | 0, _ => rfl
  | r + 1, i => by
    simp only [entry, entry_two_mul u r i, entry_two_mul u r (i + 1)]
    unfold Nat.dist
    omega

private def binEntry (b : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, i => b i
  | r + 1, i => xor (binEntry b r i) (binEntry b r (i + 1))

private def binExtend {n : ℕ} (b : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then b ⟨i, h⟩ else false

private lemma dist_mod_two (a b : ℕ) :
    (Nat.dist a b % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  have h : Nat.dist a b % 2 = (a % 2 + b % 2) % 2 := by
    unfold Nat.dist
    omega
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  simp [ha, hb]

private lemma entry_mod_two (w : ℕ → ℕ) :
    ∀ (r i : ℕ), (entry w r i % 2 == 1) = binEntry (fun j => w j % 2 == 1) r i
  | 0, _ => rfl
  | r + 1, i => by
    simp only [entry, binEntry, dist_mod_two, entry_mod_two w r i, entry_mod_two w r (i + 1)]

private lemma entry_bool_toNat (b : ℕ → Bool) :
    ∀ (r i : ℕ), entry (fun j => (b j).toNat) r i = (binEntry b r i).toNat
  | 0, _ => rfl
  | r + 1, i => by
    simp only [entry, binEntry, entry_bool_toNat b r i, entry_bool_toNat b r (i + 1)]
    cases binEntry b r i <;> cases binEntry b r (i + 1) <;> rfl

/-! ### Part 2: Symmetric `xor`-triangles and diagonal parameterization of fixed binary words -/

private lemma xor_cancel_left (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

private lemma xor_eq_right_iff (a b : Bool) : xor a b = b ↔ a = false := by
  cases a <;> cases b <;> simp

private lemma binEntry_symm {b : ℕ → Bool} {n : ℕ}
    (hb : ∀ r < n, binEntry b r 0 = b r) :
    ∀ i r, r + i < n → binEntry b r i = binEntry b i r
  | 0, r, hr => by
    simpa [binEntry] using hb r (by omega)
  | i + 1, r, hri => by
    have h1 : binEntry b (r + 1) i = xor (binEntry b r i) (binEntry b r (i + 1)) := rfl
    have h2 : binEntry b r (i + 1) = xor (binEntry b r i) (binEntry b (r + 1) i) := by
      rw [h1, xor_cancel_left]
    rw [h2, binEntry_symm hb i r (by omega), binEntry_symm hb i (r + 1) (by omega)]
    rfl

private lemma binEntry_diag_false {b : ℕ → Bool} {n : ℕ}
    (hb : ∀ r < n, binEntry b r 0 = b r) {j : ℕ} (hj : 2 * j + 1 < n) :
    binEntry b j j = false := by
  have h1 : binEntry b (j + 1) j = binEntry b j (j + 1) :=
    binEntry_symm hb j (j + 1) (by omega)
  have h2 : xor (binEntry b j j) (binEntry b j (j + 1)) = binEntry b j (j + 1) := h1
  exact (xor_eq_right_iff _ _).mp h2

private def tri (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) : ℕ → ℕ → Bool
  | r, 0 =>
    if 2 * r + 1 < n then false
    else if h : r < (n + 1) / 2 then v ⟨r, h⟩ else false
  | r, 1 =>
    if h : r < (n + 1) / 2 then v ⟨r, h⟩ else false
  | r, d + 2 => xor (tri n v r (d + 1)) (tri n v (r + 1) d)

private def symTri (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) (r i : ℕ) : Bool :=
  if r ≤ i then tri n v r (i - r) else tri n v i (r - i)

private lemma symTri_succ (n : ℕ) (v : Fin ((n + 1) / 2) → Bool)
    (r i : ℕ) (h : r + i + 1 < n) :
    symTri n v (r + 1) i = xor (symTri n v r i) (symTri n v r (i + 1)) := by
  unfold symTri
  by_cases hri : r < i
  · have h1 : r + 1 ≤ i := by omega
    have h2 : r ≤ i := by omega
    have h3 : r ≤ i + 1 := by omega
    simp only [h1, h2, h3, ↓reduceIte]
    set d := i - (r + 1)
    have hd1 : i - r = d + 1 := by omega
    have hd2 : i + 1 - r = d + 2 := by omega
    rw [hd1, hd2, tri, xor_cancel_left]
  · by_cases heq : r = i
    · subst heq
      have h1 : ¬ (r + 1 ≤ r) := by omega
      have h2 : r ≤ r := le_rfl
      have h3 : r ≤ r + 1 := by omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.sub_self, Nat.add_sub_cancel_left]
      have h0 : tri n v r 0 = false := by
        simp [tri, show 2 * r + 1 < n by omega]
      rw [h0, Bool.false_xor]
    · have hir : i < r := by omega
      have h1 : ¬ (r + 1 ≤ i) := by omega
      have h2 : ¬ (r ≤ i) := by omega
      simp only [h1, h2, ↓reduceIte]
      set d := r - (i + 1)
      have hd1 : r - i = d + 1 := by omega
      have hd2 : r + 1 - i = d + 2 := by omega
      rw [hd1, hd2, tri]
      by_cases h3 : r ≤ i + 1
      · have hri1 : r = i + 1 := by omega
        have hd0 : d = 0 := by omega
        simp [hd0, hri1]
      · simp [h3]

private def wordFromDiag (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) : Fin n → Bool :=
  fun i => tri n v 0 i.val

private def diagOf (n : ℕ) (b : Fin n → Bool) : Fin ((n + 1) / 2) → Bool :=
  fun j =>
    if 2 * j.val + 1 < n then binEntry (binExtend b) j.val (j.val + 1)
    else binEntry (binExtend b) j.val j.val

private lemma binEntry_wordFromDiag (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) :
    ∀ r i, r + i < n → binEntry (binExtend (wordFromDiag n v)) r i = symTri n v r i
  | 0, i, hi => by
    have hi' : i < n := by omega
    simp [binEntry, binExtend, wordFromDiag, symTri, hi']
  | r + 1, i, hri => by
    simp only [binEntry]
    rw [binEntry_wordFromDiag n v r i (by omega),
        binEntry_wordFromDiag n v r (i + 1) (by omega),
        ← symTri_succ n v r i (by omega)]

private lemma wordFromDiag_fixed (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) (i : Fin n) :
    binEntry (binExtend (wordFromDiag n v)) i.val 0 = wordFromDiag n v i := by
  rw [binEntry_wordFromDiag n v i.val 0 (by omega)]
  unfold symTri wordFromDiag
  by_cases h : i.val ≤ 0
  · have hi0 : i.val = 0 := by omega
    simp [hi0]
  · simp [h]

private lemma diagOf_wordFromDiag (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) :
    diagOf n (wordFromDiag n v) = v := by
  funext j
  unfold diagOf
  split_ifs with h
  · rw [binEntry_wordFromDiag n v j.val (j.val + 1) (by omega)]
    simp [symTri, tri, j.isLt]
  · rw [binEntry_wordFromDiag n v j.val j.val (by omega)]
    simp [symTri, tri, h, j.isLt]

private lemma tri_diagOf {n : ℕ} {b : Fin n → Bool}
    (hb : ∀ i : Fin n, binEntry (binExtend b) i.val 0 = b i) :
    ∀ d r, 2 * r + d < n →
      tri n (diagOf n b) r d = binEntry (binExtend b) r (r + d)
  | 0, r, hr => by
    have hb' : ∀ k < n, binEntry (binExtend b) k 0 = binExtend b k := by
      intro k hk
      simpa [binExtend, hk] using hb ⟨k, hk⟩
    simp only [tri, Nat.add_zero]
    split_ifs with h1 h2
    · exact (binEntry_diag_false hb' h1).symm
    · simp [diagOf, h1]
    · omega
  | 1, r, hr => by
    have hr' : r < (n + 1) / 2 := by omega
    simp [tri, diagOf, hr', hr]
  | d + 2, r, hr => by
    simp only [tri]
    rw [tri_diagOf hb (d + 1) r (by omega),
        tri_diagOf hb d (r + 1) (by omega)]
    have hstep : binEntry (binExtend b) (r + 1) (r + 1 + d) =
        xor (binEntry (binExtend b) r (r + 1 + d))
            (binEntry (binExtend b) r (r + 1 + d + 1)) := rfl
    have heq1 : r + (d + 1) = r + 1 + d := by omega
    have heq2 : r + (d + 2) = r + 1 + d + 1 := by omega
    rw [heq1, heq2, hstep, xor_cancel_left]

private lemma wordFromDiag_diagOf {n : ℕ} {b : Fin n → Bool}
    (hb : ∀ i : Fin n, binEntry (binExtend b) i.val 0 = b i) :
    wordFromDiag n (diagOf n b) = b := by
  funext i
  unfold wordFromDiag
  rw [tri_diagOf hb i.val 0 (by omega)]
  simp [binEntry, binExtend, i.isLt]

/-! ### Part 3: Position of the first `true` bit -/

private def firstOneAux (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let r := firstOneAux b k
    if r < k then r else if b k then k else k + 1

private lemma firstOneAux_le (b : ℕ → Bool) : ∀ n, firstOneAux b n ≤ n
  | 0 => le_rfl
  | k + 1 => by
    dsimp [firstOneAux]
    have := firstOneAux_le b k
    split_ifs <;> omega

private lemma firstOneAux_spec_true (b : ℕ → Bool) :
    ∀ n, firstOneAux b n < n → b (firstOneAux b n) = true
  | 0, h => by omega
  | k + 1, h => by
    dsimp [firstOneAux] at h ⊢
    split_ifs at h ⊢ with h1 h2
    · exact firstOneAux_spec_true b k h1
    · exact h2
    · omega

private lemma firstOneAux_lt_false (b : ℕ → Bool) :
    ∀ n {i : ℕ}, i < firstOneAux b n → b i = false
  | 0, _, h => by simp [firstOneAux] at h
  | k + 1, i, h => by
    dsimp [firstOneAux] at h
    have hle := firstOneAux_le b k
    split_ifs at h with h1 h2
    · exact firstOneAux_lt_false b k h
    · exact firstOneAux_lt_false b k (by omega)
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hlt | rfl
      · exact firstOneAux_lt_false b k (by omega)
      · cases hbi : b i
        · rfl
        · exact False.elim (h2 hbi)

private def firstOne {n : ℕ} (b : Fin n → Bool) : ℕ :=
  firstOneAux (binExtend b) n

private lemma firstOne_le {n : ℕ} (b : Fin n → Bool) : firstOne b ≤ n :=
  firstOneAux_le (binExtend b) n

private lemma firstOne_spec_true {n : ℕ} (b : Fin n → Bool) (h : firstOne b < n) :
    b ⟨firstOne b, h⟩ = true := by
  have h1 := firstOneAux_spec_true (binExtend b) n h
  change binExtend b (firstOne b) = true at h1
  simp only [binExtend, h, ↓reduceDIte] at h1
  exact h1

private lemma firstOne_lt_false {n : ℕ} (b : Fin n → Bool) {i : Fin n} (hi : i.val < firstOne b) :
    b i = false := by
  have := firstOneAux_lt_false (binExtend b) n hi
  simpa [binExtend, i.isLt] using this

private lemma firstOne_eq_n {n : ℕ} (b : Fin n → Bool) (h : ∀ i : Fin n, b i = false) :
    firstOne b = n := by
  by_contra hne
  have hlt : firstOne b < n := lt_of_le_of_ne (firstOne_le b) hne
  have ht := firstOne_spec_true b hlt
  have hf := h ⟨firstOne b, hlt⟩
  rw [ht] at hf
  cases hf

private lemma firstOne_eq_of_spec {n : ℕ} (b : Fin n → Bool) {k : ℕ} (hk : k < n)
    (ht : b ⟨k, hk⟩ = true) (hf : ∀ i : Fin n, i.val < k → b i = false) :
    firstOne b = k := by
  rcases Nat.lt_trichotomy (firstOne b) k with h1 | h2 | h3
  · have hlt : firstOne b < n := lt_trans h1 hk
    have htrue := firstOne_spec_true b hlt
    have hfalse := hf ⟨firstOne b, hlt⟩ h1
    rw [htrue] at hfalse
    cases hfalse
  · exact h2
  · have hfalse := firstOne_lt_false b (i := ⟨k, hk⟩) h3
    rw [ht] at hfalse
    cases hfalse

private def firstOneDiagOfIdx (n k : ℕ) : ℕ :=
  if k < (n + 1) / 2 then
    if 2 * k + 1 < n then 2 * k + 1 else 2 * k
  else n

private def firstOneDiag (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) : ℕ :=
  firstOneDiagOfIdx n (firstOne v)

private lemma firstOneDiagOfIdx_le (n k : ℕ) : firstOneDiagOfIdx n k ≤ n := by
  unfold firstOneDiagOfIdx
  split_ifs <;> omega

private lemma firstOneDiag_le (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) :
    firstOneDiag n v ≤ n :=
  firstOneDiagOfIdx_le n (firstOne v)

private lemma tri_eq_false_lt (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) (j₀ : ℕ)
    (hv : ∀ j : Fin ((n + 1) / 2), j.val < j₀ → v j = false) :
    ∀ d r, 2 * r + d < firstOneDiagOfIdx n j₀ → tri n v r d = false
  | 0, r, hr => by
    unfold firstOneDiagOfIdx at hr
    simp only [tri]
    split_ifs with h1 h2
    · rfl
    · apply hv ⟨r, h2⟩
      dsimp only
      split_ifs at hr <;> omega
    · rfl
  | 1, r, hr => by
    unfold firstOneDiagOfIdx at hr
    simp only [tri]
    split_ifs with h1
    · apply hv ⟨r, h1⟩
      dsimp only
      split_ifs at hr <;> omega
    · rfl
  | d + 2, r, hr => by
    simp only [tri]
    rw [tri_eq_false_lt n v j₀ hv (d + 1) r (by omega),
        tri_eq_false_lt n v j₀ hv d (r + 1) (by omega)]
    rfl

private lemma tri_eq_val_at (n : ℕ) (v : Fin ((n + 1) / 2) → Bool)
    (j₀ : Fin ((n + 1) / 2))
    (hv : ∀ j : Fin ((n + 1) / 2), j.val < j₀.val → v j = false) :
    ∀ d r, 2 * r + d = firstOneDiagOfIdx n j₀.val → tri n v r d = v j₀
  | 0, r, hr => by
    unfold firstOneDiagOfIdx at hr
    simp only [j₀.isLt, ↓reduceIte] at hr
    split_ifs at hr with hodd
    · omega
    · have hrj : r = j₀.val := by omega
      subst hrj
      simp [tri, hodd, j₀.isLt]
  | 1, r, hr => by
    unfold firstOneDiagOfIdx at hr
    simp only [j₀.isLt, ↓reduceIte] at hr
    split_ifs at hr with hodd
    · have hrj : r = j₀.val := by omega
      subst hrj
      simp [tri, j₀.isLt]
    · omega
  | d + 2, r, hr => by
    simp only [tri]
    rw [tri_eq_false_lt n v j₀.val hv (d + 1) r (by omega),
        tri_eq_val_at n v j₀ hv d (r + 1) (by omega)]
    exact Bool.false_xor _

private lemma firstOne_wordFromDiag (n : ℕ) (v : Fin ((n + 1) / 2) → Bool) :
    firstOne (wordFromDiag n v) = firstOneDiag n v := by
  unfold firstOneDiag
  by_cases h : firstOne v < (n + 1) / 2
  · let j₀ : Fin ((n + 1) / 2) := ⟨firstOne v, h⟩
    have hv : ∀ j : Fin ((n + 1) / 2), j.val < j₀.val → v j = false :=
      fun j hj => firstOne_lt_false v hj
    have hklt : firstOneDiagOfIdx n j₀.val < n := by
      unfold firstOneDiagOfIdx
      simp only [j₀, h, ↓reduceIte]
      split_ifs <;> omega
    apply firstOne_eq_of_spec (wordFromDiag n v) hklt
    · unfold wordFromDiag
      rw [tri_eq_val_at n v j₀ hv (firstOneDiagOfIdx n j₀.val) 0 (by omega)]
      exact firstOne_spec_true v h
    · intro i hi
      unfold wordFromDiag
      exact tri_eq_false_lt n v j₀.val hv i.val 0 (by omega)
  · have hEq : firstOne v = (n + 1) / 2 := by
      have := firstOne_le v
      omega
    have hv : ∀ j : Fin ((n + 1) / 2), j.val < firstOne v → v j = false :=
      fun j hj => firstOne_lt_false v hj
    have hdiag : firstOneDiagOfIdx n (firstOne v) = n := by
      unfold firstOneDiagOfIdx
      simp [h]
    rw [hdiag]
    apply firstOne_eq_n
    intro i
    unfold wordFromDiag
    exact tri_eq_false_lt n v (firstOne v) hv i.val 0 (by rw [hdiag]; omega)

/-! ### Part 4: Ternary triangle barrier — no `2` may appear after the first `1` -/

private lemma entry_even_lt {w : ℕ → ℕ} {k : ℕ}
    (hw : ∀ i < k, w i = 0 ∨ w i = 2) :
    ∀ r i, i + r < k → entry w r i = 0 ∨ entry w r i = 2
  | 0, i, hi => hw i (by omega)
  | r + 1, i, hri => by
    simp only [entry]
    have h1 := entry_even_lt hw r i (by omega)
    have h2 := entry_even_lt hw r (i + 1) (by omega)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      simp [h1, h2, Nat.dist]

private lemma entry_antidiag_one {w : ℕ → ℕ} {k : ℕ}
    (hw : ∀ i < k, w i = 0 ∨ w i = 2) (hwk : w k = 1) :
    ∀ r, r ≤ k → entry w r (k - r) = 1
  | 0, _ => by simpa [entry] using hwk
  | r + 1, hr => by
    simp only [entry]
    have hidx : k - (r + 1) + 1 = k - r := by omega
    rw [hidx, entry_antidiag_one hw hwk r (by omega)]
    have hev := entry_even_lt hw r (k - (r + 1)) (by omega)
    rcases hev with hev | hev <;> simp [hev, Nat.dist]

private lemma entry_le_one_between {w : ℕ → ℕ} {k j : ℕ}
    (hw : ∀ i < k, w i = 0 ∨ w i = 2) (hwk : w k = 1)
    (hmid : ∀ i, k ≤ i → i < j → w i ≤ 1) :
    ∀ r i, k ≤ i + r → i + r < j → entry w r i ≤ 1
  | 0, i, h1, h2 => hmid i (by omega) (by omega)
  | r + 1, i, h1, h2 => by
    by_cases hEq : i + (r + 1) = k
    · have hi : i = k - (r + 1) := by omega
      rw [hi, entry_antidiag_one hw hwk (r + 1) (by omega)]
    · simp only [entry]
      have ha := entry_le_one_between hw hwk hmid r i (by omega) (by omega)
      have hb := entry_le_one_between hw hwk hmid r (i + 1) (by omega) (by omega)
      unfold Nat.dist
      omega

private lemma entry_zero_backprop {w : ℕ → ℕ} {s : ℕ}
    (hs : ∀ r, r ≤ s → entry w r (s - r) = 0) :
    ∀ d, d ≤ s → ∀ r i, i + r = s - d → entry w r i = 0
  | 0, _, r, i, hri => by
    have hi : i = s - r := by omega
    rw [hi]
    exact hs r (by omega)
  | d + 1, hd, r, i, hri => by
    have h1 := entry_zero_backprop hs d (by omega) r (i + 1) (by omega)
    have h2 := entry_zero_backprop hs d (by omega) (r + 1) i (by omega)
    simp only [entry, h1] at h2
    unfold Nat.dist at h2
    omega

private lemma entry_antidiag_le_two {w : ℕ → ℕ} {j : ℕ}
    (hwj : w j ≤ 2) (hleft : ∀ r, r < j → entry w r (j - 1 - r) ≤ 1) :
    ∀ r, r ≤ j → entry w r (j - r) ≤ 2
  | 0, _ => by simpa [entry] using hwj
  | r + 1, hr => by
    simp only [entry]
    have hidx1 : j - (r + 1) = j - 1 - r := by omega
    have hidx2 : j - (r + 1) + 1 = j - r := by omega
    rw [hidx2, hidx1]
    have ha := hleft r (by omega)
    have hb := entry_antidiag_le_two hwj hleft r (by omega)
    unfold Nat.dist
    omega

private lemma entry_antidiag_crushed {w : ℕ → ℕ} {j r₀ : ℕ}
    (hleft : ∀ r, r < j → entry w r (j - 1 - r) ≤ 1)
    (hle2 : ∀ r, r ≤ j → entry w r (j - r) ≤ 2)
    (hr0 : r₀ < j) (hone : entry w r₀ (j - 1 - r₀) = 1) :
    ∀ r, r₀ + 1 ≤ r → r ≤ j → entry w r (j - r) ≤ 1
  | 0, h1, _ => by omega
  | r + 1, h1, h2 => by
    simp only [entry]
    have hidx1 : j - (r + 1) = j - 1 - r := by omega
    have hidx2 : j - (r + 1) + 1 = j - r := by omega
    rw [hidx2, hidx1]
    by_cases heq : r = r₀
    · subst heq
      rw [hone]
      have hb := hle2 r (by omega)
      unfold Nat.dist
      omega
    · have ha := hleft r (by omega)
      have hb := entry_antidiag_crushed hleft hle2 hr0 hone r (by omega) (by omega)
      unfold Nat.dist
      omega

private lemma no_two_after_first_one {n k : ℕ} {w : Fin n → Fin 3}
    (hfix : ∀ i : Fin n, entry (extend w) i.val 0 = (w i).val)
    (hk : k < n)
    (hpre : ∀ i < k, extend w i = 0 ∨ extend w i = 2)
    (hwk : extend w k = 1) :
    ∀ j, j < n → k ≤ j → extend w j ≤ 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hjn hkj
    by_cases hEq : j = k
    · subst hEq; omega
    · have hkj' : k < j := by omega
      have hmid : ∀ i, k ≤ i → i < j → extend w i ≤ 1 :=
        fun i h1 h2 => ih i h2 (by omega) h1
      by_contra hgt
      have hwj_lt : extend w j < 3 := by
        simp [extend, hjn]
      have hwj2 : extend w j = 2 := by omega
      have hleft : ∀ r, r < j → entry (extend w) r (j - 1 - r) ≤ 1 := fun r hr =>
        entry_le_one_between hpre hwk hmid r (j - 1 - r) (by omega) (by omega)
      have hex : ∃ r, r < j ∧ entry (extend w) r (j - 1 - r) = 1 := by
        by_contra hall
        have hall0 : ∀ r, r ≤ j - 1 → entry (extend w) r (j - 1 - r) = 0 := by
          intro r hr
          have hle := hleft r (by omega)
          have hne : entry (extend w) r (j - 1 - r) ≠ 1 := fun h1 => hall ⟨r, by omega, h1⟩
          omega
        have hk0 := entry_zero_backprop hall0 (j - 1 - k) (by omega) 0 k (by omega)
        simp only [entry] at hk0
        omega
      rcases hex with ⟨r₀, hr0, hone⟩
      have hle2 := entry_antidiag_le_two (by omega : extend w j ≤ 2) hleft
      have hcr := entry_antidiag_crushed hleft hle2 hr0 hone j (by omega) le_rfl
      simp only [Nat.sub_self] at hcr
      have hfixj : entry (extend w) j 0 = extend w j := by
        simpa [extend, hjn] using hfix ⟨j, hjn⟩
      omega

/-! ### Part 5: Bijection with the diagonal parameter space `Param n` -/

private abbrev Param (n : ℕ) :=
  Σ v : Fin ((n + 1) / 2) → Bool, Fin ((firstOneDiag n v + 1) / 2) → Bool

private def toParam (n : ℕ) (w : Fin n → Fin 3) : Param n :=
  let m : Fin n → Bool := fun i => (w i).val % 2 == 1
  let v := diagOf n m
  let k := firstOneDiag n v
  let p : Fin k → Bool :=
    fun i => (w ⟨i.val, lt_of_lt_of_le i.isLt (firstOneDiag_le n v)⟩).val == 2
  ⟨v, diagOf k p⟩

private def fromParam (n : ℕ) (x : Param n) : Fin n → Fin 3 :=
  let m := wordFromDiag n x.1
  let k := firstOneDiag n x.1
  let p := wordFromDiag k x.2
  fun i =>
    if h : i.val < k then
      if p ⟨i.val, h⟩ then ⟨2, by omega⟩ else ⟨0, by omega⟩
    else
      if m i then ⟨1, by omega⟩ else ⟨0, by omega⟩

private lemma fromParam_lt (n : ℕ) (x : Param n) (i : Fin n) (h : i.val < firstOneDiag n x.1) :
    (fromParam n x i).val = 2 * (wordFromDiag (firstOneDiag n x.1) x.2 ⟨i.val, h⟩).toNat := by
  unfold fromParam
  simp only [h, ↓reduceDIte]
  cases wordFromDiag (firstOneDiag n x.1) x.2 ⟨i.val, h⟩ <;> rfl

private lemma fromParam_ge (n : ℕ) (x : Param n) (i : Fin n) (h : ¬ i.val < firstOneDiag n x.1) :
    (fromParam n x i).val = (wordFromDiag n x.1 i).toNat := by
  unfold fromParam
  simp only [h, ↓reduceDIte]
  cases wordFromDiag n x.1 i <;> rfl

private lemma fromParam_parity (n : ℕ) (x : Param n) :
    (fun i : Fin n => ((fromParam n x i).val % 2 == 1)) = wordFromDiag n x.1 := by
  funext i
  by_cases h1 : i.val < firstOneDiag n x.1
  · rw [fromParam_lt n x i h1]
    have hfalse : wordFromDiag n x.1 i = false := by
      apply firstOne_lt_false (wordFromDiag n x.1)
      rw [firstOne_wordFromDiag]
      exact h1
    rw [hfalse]
    cases wordFromDiag (firstOneDiag n x.1) x.2 ⟨i.val, h1⟩ <;> rfl
  · rw [fromParam_ge n x i h1]
    cases wordFromDiag n x.1 i <;> rfl

private lemma fromParam_mem (n : ℕ) (x : Param n) :
    ∀ i : Fin n, entry (extend (fromParam n x)) i.val 0 = (fromParam n x i).val := by
  let m := wordFromDiag n x.1
  let k := firstOneDiag n x.1
  let p := wordFromDiag k x.2
  let w := fromParam n x
  have hkm : firstOne m = k := firstOne_wordFromDiag n x.1
  have hpar_all : (fun j => extend w j % 2 == 1) = binExtend m := by
    funext j
    by_cases hj : j < n
    · have hpi := congrFun (fromParam_parity n x) ⟨j, hj⟩
      simpa [extend, binExtend, hj, w, m] using hpi
    · simp [extend, binExtend, hj]
  intro i
  by_cases hi : i.val < k
  · have hcongr : entry (extend w) i.val 0 =
        entry (fun j => 2 * (binExtend p j).toNat) i.val 0 := by
      apply entry_congr
      intro j _ hj2
      have hjk : j < k := by omega
      have hjn : j < n := lt_of_lt_of_le hjk (firstOneDiag_le n x.1)
      simp only [extend, binExtend, hjn, hjk, ↓reduceDIte]
      exact fromParam_lt n x ⟨j, hjn⟩ hjk
    rw [hcongr, entry_two_mul, entry_bool_toNat]
    have hpfix : binEntry (binExtend p) i.val 0 = p ⟨i.val, hi⟩ :=
      wordFromDiag_fixed k x.2 ⟨i.val, hi⟩
    rw [hpfix, fromParam_lt n x i hi]
  · have hkn : k < n := by omega
    have hpre : ∀ j < k, extend w j = 0 ∨ extend w j = 2 := by
      intro j hj
      have hjn : j < n := lt_of_lt_of_le hj (firstOneDiag_le n x.1)
      simp only [extend, hjn, ↓reduceDIte]
      rw [fromParam_lt n x ⟨j, hjn⟩ hj]
      cases p ⟨j, hj⟩ <;> simp
    have hmk : m ⟨k, hkn⟩ = true := by
      have := firstOne_spec_true m (by omega)
      simpa [hkm] using this
    have hwk : extend w k = 1 := by
      simp only [extend, hkn, ↓reduceDIte]
      rw [fromParam_ge n x ⟨k, hkn⟩ (by dsimp only; omega)]
      change (m ⟨k, hkn⟩).toNat = 1
      rw [hmk]
      rfl
    have hmid : ∀ j, k ≤ j → j < n → extend w j ≤ 1 := by
      intro j h1 h2
      simp only [extend, h2, ↓reduceDIte]
      rw [fromParam_ge n x ⟨j, h2⟩ (by dsimp only; omega)]
      cases wordFromDiag n x.1 ⟨j, h2⟩ <;> simp
    have hle1 : entry (extend w) i.val 0 ≤ 1 :=
      entry_le_one_between hpre hwk hmid i.val 0 (by omega) (by omega)
    have hmod : (entry (extend w) i.val 0 % 2 == 1) = m i := by
      rw [entry_mod_two, hpar_all]
      exact wordFromDiag_fixed n x.1 i
    rw [fromParam_ge n x i hi]
    change entry (extend w) i.val 0 = (m i).toNat
    cases hmi : m i <;> rw [hmi] at hmod
    · simp only [beq_eq_false_iff_ne, ne_eq] at hmod
      simp only [Bool.toNat_false]
      omega
    · simp only [beq_iff_eq] at hmod
      simp only [Bool.toNat_true]
      omega

private lemma toParam_fromParam_aux (n : ℕ) (v : Fin ((n + 1) / 2) → Bool)
    (u : Fin ((firstOneDiag n v + 1) / 2) → Bool)
    (v' : Fin ((n + 1) / 2) → Bool) (hv : v' = v) :
    (⟨v', diagOf (firstOneDiag n v')
      (fun i => (fromParam n ⟨v, u⟩ ⟨i.val, lt_of_lt_of_le i.isLt (firstOneDiag_le n v')⟩).val == 2)⟩ : Param n) =
    ⟨v, u⟩ := by
  subst hv
  congr 1
  have hp : (fun i : Fin (firstOneDiag n v') =>
      (fromParam n ⟨v', u⟩ ⟨i.val, lt_of_lt_of_le i.isLt (firstOneDiag_le n v')⟩).val == 2) =
      wordFromDiag (firstOneDiag n v') u := by
    funext i
    rw [fromParam_lt n ⟨v', u⟩ ⟨i.val, lt_of_lt_of_le i.isLt (firstOneDiag_le n v')⟩ i.isLt]
    cases wordFromDiag (firstOneDiag n v') u i <;> rfl
  rw [hp, diagOf_wordFromDiag]

private lemma toParam_fromParam (n : ℕ) (x : Param n) :
    toParam n (fromParam n x) = x := by
  rcases x with ⟨v, u⟩
  exact toParam_fromParam_aux n v u _ (by rw [fromParam_parity n ⟨v, u⟩, diagOf_wordFromDiag])

private lemma fromParam_toParam {n : ℕ} {w : Fin n → Fin 3}
    (hfix : ∀ i : Fin n, entry (extend w) i.val 0 = (w i).val) :
    fromParam n (toParam n w) = w := by
  let m : Fin n → Bool := fun i => (w i).val % 2 == 1
  have hm_all : (fun j => extend w j % 2 == 1) = binExtend m := by
    funext j
    by_cases hj : j < n
    · simp [extend, binExtend, hj, m]
    · simp [extend, binExtend, hj]
  have hm_fix : ∀ i : Fin n, binEntry (binExtend m) i.val 0 = m i := by
    intro i
    rw [← hm_all, ← entry_mod_two, hfix i]
  let v := diagOf n m
  have hwm : wordFromDiag n v = m := wordFromDiag_diagOf hm_fix
  let k := firstOneDiag n v
  have hkm : k = firstOne m := by
    show firstOneDiag n v = firstOne m
    rw [← firstOne_wordFromDiag n v, hwm]
  let p : Fin k → Bool :=
    fun i => (w ⟨i.val, lt_of_lt_of_le i.isLt (firstOneDiag_le n v)⟩).val == 2
  have hpre_even : ∀ j < k, extend w j = 0 ∨ extend w j = 2 := by
    intro j hj
    have hjn : j < n := lt_of_lt_of_le hj (firstOneDiag_le n v)
    have hmj : m ⟨j, hjn⟩ = false := firstOne_lt_false m (by rw [← hkm]; exact hj)
    have hlt3 : (w ⟨j, hjn⟩).val < 3 := (w ⟨j, hjn⟩).isLt
    simp only [extend, hjn, ↓reduceDIte]
    simp only [m, beq_eq_false_iff_ne, ne_eq] at hmj
    omega
  have hp_fix : ∀ i : Fin k, binEntry (binExtend p) i.val 0 = p i := by
    intro i
    have hin : i.val < n := lt_of_lt_of_le i.isLt (firstOneDiag_le n v)
    have hcongr : entry (extend w) i.val 0 =
        entry (fun j => 2 * (binExtend p j).toNat) i.val 0 := by
      apply entry_congr
      intro j _ hj2
      have hjk : j < k := by omega
      have hjn : j < n := lt_of_lt_of_le hjk (firstOneDiag_le n v)
      have hev := hpre_even j hjk
      simp only [extend, binExtend, hjn, hjk, ↓reduceDIte, p] at hev ⊢
      rcases hev with h0 | h0 <;> simp [h0]
    rw [entry_two_mul, entry_bool_toNat] at hcongr
    have hfixi := hfix ⟨i.val, hin⟩
    have hevi := hpre_even i.val i.isLt
    simp only [extend, hin, ↓reduceDIte] at hevi
    rw [hfixi] at hcongr
    rcases hevi with h0 | h2
    · rw [h0] at hcongr
      have hpi : p i = false := by simp [p, h0]
      rw [hpi]
      cases hb : binEntry (binExtend p) i.val 0
      · rfl
      · rw [hb] at hcongr
        simp at hcongr
    · rw [h2] at hcongr
      have hpi : p i = true := by simp [p, h2]
      rw [hpi]
      cases hb : binEntry (binExtend p) i.val 0
      · rw [hb] at hcongr
        simp at hcongr
      · rfl
  have hwp : wordFromDiag k (diagOf k p) = p := wordFromDiag_diagOf hp_fix
  have htail_le1 : ∀ i : Fin n, k ≤ i.val → (w i).val ≤ 1 := by
    intro i hi
    have hkn : k < n := by omega
    have hmk : m ⟨k, hkn⟩ = true := by
      have := firstOne_spec_true m (by rw [← hkm]; exact hkn)
      simpa [← hkm] using this
    have hwk : extend w k = 1 := by
      have hlt3 : (w ⟨k, hkn⟩).val < 3 := (w ⟨k, hkn⟩).isLt
      simp only [extend, hkn, ↓reduceDIte]
      simp only [m, beq_iff_eq] at hmk
      omega
    have := no_two_after_first_one hfix hkn hpre_even hwk i.val i.isLt hi
    simpa [extend, i.isLt] using this
  funext i
  apply Fin.ext
  by_cases hi : i.val < k
  · rw [fromParam_lt n (toParam n w) i hi]
    change 2 * (wordFromDiag k (diagOf k p) ⟨i.val, hi⟩).toNat = (w i).val
    rw [hwp]
    have hev := hpre_even i.val hi
    simp only [extend, i.isLt, ↓reduceDIte] at hev
    rcases hev with h0 | h2
    · have hpi : p ⟨i.val, hi⟩ = false := by simp [p, h0]
      rw [hpi, h0]
      rfl
    · have hpi : p ⟨i.val, hi⟩ = true := by simp [p, h2]
      rw [hpi, h2]
      rfl
  · rw [fromParam_ge n (toParam n w) i hi]
    change (wordFromDiag n v i).toNat = (w i).val
    rw [hwm]
    have hle := htail_le1 i (by omega)
    cases hmi : m i
    · simp only [m, beq_eq_false_iff_ne, ne_eq] at hmi
      simp only [Bool.toNat_false]
      omega
    · simp only [m, beq_iff_eq] at hmi
      simp only [Bool.toNat_true]
      omega

private lemma fixedCount_eq_card_param (n : ℕ) :
    fixedCount n = Fintype.card (Param n) := by
  unfold fixedCount
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun w _ => toParam n w) ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro w₁ hw₁ w₂ hw₂ heq
    have h1 := (Finset.mem_filter.mp hw₁).2
    have h2 := (Finset.mem_filter.mp hw₂).2
    rw [← fromParam_toParam h1, ← fromParam_toParam h2, heq]
  · intro x _
    exact ⟨fromParam n x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fromParam_mem n x⟩,
      toParam_fromParam n x⟩

/-! ### Part 6: Exact enumeration of `Param n` -/

private def consBool {M : ℕ} (b : Bool) (t : Fin M → Bool) : Fin (M + 1) → Bool :=
  Fin.cases b t

private def consBoolEquiv (M : ℕ) : Bool × (Fin M → Bool) ≃ (Fin (M + 1) → Bool) where
  toFun p := consBool p.1 p.2
  invFun v := (v 0, fun i => v i.succ)
  left_inv p := by
    rcases p with ⟨b, t⟩
    apply Prod.ext
    · rfl
    · funext i
      rfl
  right_inv v := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl

private lemma firstOne_consBool_true {M : ℕ} (t : Fin M → Bool) :
    firstOne (consBool true t) = 0 := by
  apply firstOne_eq_of_spec (consBool true t) (Nat.zero_lt_succ M)
  · rfl
  · intro i hi
    omega

private lemma firstOne_consBool_false {M : ℕ} (t : Fin M → Bool) :
    firstOne (consBool false t) = firstOne t + 1 := by
  by_cases h : firstOne t < M
  · apply firstOne_eq_of_spec (consBool false t) (Nat.succ_lt_succ h)
    · exact firstOne_spec_true t h
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro _
        rfl
      · intro j hj
        exact firstOne_lt_false t (Nat.lt_of_succ_lt_succ hj)
  · have hEq : firstOne t = M := by
      have := firstOne_le t
      omega
    rw [hEq]
    apply firstOne_eq_n
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      exact firstOne_lt_false t (by rw [hEq]; exact j.isLt)

private lemma sum_by_firstOne :
    ∀ (M : ℕ) (f : ℕ → ℕ),
      ∑ v : Fin M → Bool, f (firstOne v) =
        f M + ∑ j : Fin M, 2 ^ (M - 1 - j.val) * f j.val
  | 0, f => by
    have h0 : ∀ v : Fin 0 → Bool, firstOne v = 0 := fun v =>
      Nat.eq_zero_of_le_zero (firstOne_le v)
    simp [h0]
  | M + 1, f => by
    rw [← Equiv.sum_comp (consBoolEquiv M)]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, consBoolEquiv, Equiv.coe_fn_mk,
      firstOne_consBool_true, firstOne_consBool_false]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul]
    rw [sum_by_firstOne M (fun k => f (k + 1))]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.sub_add_eq]
    have hsub : ∀ j : Fin M, M - 1 - j.val = M - j.val - 1 := fun j => by omega
    simp_rw [hsub]
    omega

private lemma card_param (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Param n) = (n + 2) * 2 ^ ((n - 1) / 2) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hsum := sum_by_firstOne ((n + 1) / 2) (fun k => 2 ^ ((firstOneDiagOfIdx n k + 1) / 2))
  change ∑ v : Fin ((n + 1) / 2) → Bool, 2 ^ ((firstOneDiagOfIdx n (firstOne v) + 1) / 2) = _
  rw [hsum]
  rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hq1 : 1 ≤ q := by omega
    have hM : (n + 1) / 2 = q := by omega
    have hhalf : (n - 1) / 2 = q - 1 := by omega
    rw [hM, hhalf]
    have hlast : firstOneDiagOfIdx n q = n := by
      unfold firstOneDiagOfIdx
      simp [hM]
    rw [hlast, hM]
    have hterm : ∀ j : Fin q,
        2 ^ (q - 1 - j.val) * 2 ^ ((firstOneDiagOfIdx n j.val + 1) / 2) = 2 ^ q := by
      intro j
      have hidx : firstOneDiagOfIdx n j.val = 2 * j.val + 1 := by
        unfold firstOneDiagOfIdx
        have h1 : j.val < (n + 1) / 2 := by omega
        have h2 : 2 * j.val + 1 < n := by omega
        simp [h1, h2]
      rw [hidx]
      have hdiv : (2 * j.val + 1 + 1) / 2 = j.val + 1 := by omega
      rw [hdiv, ← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
      have : q = (q - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [hpow]
    have hn2 : n + 2 = 2 * (q + 1) := by omega
    rw [hn2]
    calc 2 * 2 ^ (q - 1) + q * (2 * 2 ^ (q - 1))
        = (2 + q * 2) * 2 ^ (q - 1) := by simp only [add_mul, mul_assoc]
      _ = 2 * (q + 1) * 2 ^ (q - 1) := by congr 1; omega
  · have hM : (n + 1) / 2 = q + 1 := by omega
    have hhalf : (n - 1) / 2 = q := by omega
    rw [hM, hhalf]
    have hlast : firstOneDiagOfIdx n (q + 1) = n := by
      unfold firstOneDiagOfIdx
      simp [hM]
    rw [hlast, hM, Fin.sum_univ_castSucc]
    have hterm : ∀ j : Fin q,
        2 ^ (q + 1 - 1 - j.castSucc.val) *
          2 ^ ((firstOneDiagOfIdx n j.castSucc.val + 1) / 2) = 2 ^ (q + 1) := by
      intro j
      have hidx : firstOneDiagOfIdx n j.castSucc.val = 2 * j.val + 1 := by
        unfold firstOneDiagOfIdx
        have h1 : j.val < (n + 1) / 2 := by omega
        have h2 : 2 * j.val + 1 < n := by omega
        simp [h1, h2]
      rw [hidx]
      have hdiv : (2 * j.val + 1 + 1) / 2 = j.val + 1 := by omega
      rw [hdiv, ← pow_add]
      congr 1
      simp only [Fin.val_castSucc]
      omega
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    have hfinlast : firstOneDiagOfIdx n (Fin.last q).val = 2 * q := by
      unfold firstOneDiagOfIdx
      simp only [Fin.val_last, hM, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte]
      have hnot : ¬ (2 * q + 1 < n) := by omega
      simp [hnot]
    rw [hfinlast]
    have hdivlast : (2 * q + 1) / 2 = q := by omega
    have hsublast : q + 1 - 1 - (Fin.last q).val = 0 := by simp
    rw [hdivlast, hsublast, pow_zero, one_mul]
    have hpow : 2 ^ (q + 1) = 2 * 2 ^ q := by rw [pow_succ']
    rw [hpow]
    have hn2 : n + 2 = 2 * q + 3 := by omega
    rw [hn2]
    calc 2 * 2 ^ q + (q * (2 * 2 ^ q) + 2 ^ q)
        = (2 + (q * 2 + 1)) * 2 ^ q := by simp only [add_mul, mul_assoc, one_mul]
      _ = (2 * q + 3) * 2 ^ q := by congr 1; omega

end OMA.S_oeis_a092434_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a092434.main := by
  intro n hn
  rw [OMA.S_oeis_a092434_Proof.fixedCount_eq_card_param n,
      OMA.S_oeis_a092434_Proof.card_param n hn]
