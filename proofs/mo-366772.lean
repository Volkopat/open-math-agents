import OMAStatements.S_mo_366772

-- Problem: MathOverflow 366772. With c the Hofstadter-Conway $10000 sequence (A004001) and c* = A287422,
-- c(n) - n/2 >= |c*(n) - n/2| for all n >= 1, i.e. n - c(n) <= c*(n) <= c(n).
-- Credit: @AngelHS12
-- Proof (following the MathOverflow answer of jvvk, with a shorter contact argument): on each dyadic block
-- [2^K, 2^(K+1)] both sequences are prefix counts of Dyck words w_K, v_K (v_K complemented for odd K), with
-- w_(K+1) = F(w_K) and v_(K+1) = F(v_K) or G(v_K) alternately, where F and G are the first- and last-threshold
-- doubling operators. F and G are monotone and preserve symmetry; F preserves irreducibility. With T the
-- perturbation that deletes the first 1 and last 0 and inserts a complementary pair in the middle, the key
-- lemma G(F(T u)) <= T(F(F u)) for symmetric irreducible u gives v_K <= T(w_K) <= w_K on odd blocks and
-- v_K <= w_K on even blocks by induction, which is the conjecture.


/-!
Part 1: Dyck prefix functions and the first doubling operator `F` (threshold characterization,
monotonicity, symmetry, irreducibility).
-/

namespace MO366772

/-- `P` is the prefix-count function of a Dyck word of length `L`, extended by a constant after `L`. -/
structure Dyck (L : ℕ) (P : ℕ → ℕ) : Prop where
  zero : P 0 = 0
  mono : ∀ t, P t ≤ P (t + 1)
  step : ∀ t, P (t + 1) ≤ P t + 1
  const : ∀ t, L ≤ t → P t = P L
  above : ∀ t, t ≤ L → t ≤ 2 * P t
  last : 2 * P L = L

/-- Symmetry `u_{L+1-i} = 1 - u_i` of the word, in terms of prefix counts. -/
def Sym (L : ℕ) (P : ℕ → ℕ) : Prop := ∀ i, i ≤ L → P (L - i) + i = P L + P i

/-- Irreducibility: the path does not return to height zero strictly inside. -/
def Irr (L : ℕ) (P : ℕ → ℕ) : Prop := ∀ t, 0 < t → t < L → t < 2 * P t

namespace Dyck

variable {L : ℕ} {P : ℕ → ℕ}

lemma mono' (h : Dyck L P) {s t : ℕ} (hst : s ≤ t) : P s ≤ P t :=
  monotone_nat_of_le_succ h.mono hst

lemma le_self (h : Dyck L P) (t : ℕ) : P t ≤ t := by
  induction t with
  | zero => simp [h.zero]
  | succ t ih => have := h.step t; omega

lemma le_top (h : Dyck L P) (t : ℕ) : P t ≤ P L := by
  rcases le_total t L with ht | ht
  · exact h.mono' ht
  · exact (h.const t ht).le

lemma one (h : Dyck L P) (hL : 1 ≤ L) : P 1 = 1 := by
  have h1 := h.above 1 hL
  have h2 := h.step 0
  have h3 := h.zero
  simp only [zero_add] at h2
  omega

end Dyck

/-! ### The first threshold operator -/

/-- Raw recursion of the first doubling operator: `A(j) = P(A(j-1)) + P(j - A(j-1))`. -/
def Fr (P : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => P (Fr P j) + P (j + 1 - Fr P j)

/-- The first doubling operator, made constant after `2L`. -/
def Fop (L : ℕ) (P : ℕ → ℕ) (j : ℕ) : ℕ := Fr P (min j (2 * L))

/-- `a` is the first nonnegative threshold of `d_j(a) = a - P(a) - P(j-a)` on its admissible range. -/
structure FInv (P : ℕ → ℕ) (L j a : ℕ) : Prop where
  le_j : a ≤ j
  le_L : a ≤ L
  ge : j ≤ a + L
  lo : P a + P (j - a) ≤ a
  hi : a ≤ P a + P (j - a) + 1
  min : ∀ b, b < a → j ≤ b + L → b < P b + P (j - b)

variable {L : ℕ} {P Q : ℕ → ℕ}

lemma Fr_succ (hP : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) (hI : FInv P L j (Fr P j)) :
    FInv P L (j + 1) (Fr P (j + 1)) ∧ Fr P j ≤ Fr P (j + 1) ∧ Fr P (j + 1) ≤ Fr P j + 1 := by
  have hdef : Fr P (j + 1) = P (Fr P j) + P (j + 1 - Fr P j) := rfl
  rw [hdef]
  generalize Fr P j = a at hI ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  have e1 : j + 1 - a = j - a + 1 := by omega
  rw [e1]
  have hx1 := hP.mono (j - a)
  have hx2 := hP.step (j - a)
  have hA := hP.above a h2
  have hlast := hP.last
  rcases (by omega : P a + P (j - a + 1) + 1 = a ∨ P a + P (j - a + 1) = a ∨
      P a + P (j - a + 1) = a + 1) with hc | hc | hc
  · exfalso
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0; omega
    · by_cases hjL : j = a + L
      · have e : j - a = L := by omega
        rw [e] at h4 h5 hc
        omega
      · have hm := h6 (a - 1) (by omega) (by omega)
        have e2 : j - (a - 1) = j - a + 1 := by omega
        rw [e2] at hm
        have hma := hP.mono (a - 1)
        have e3 : a - 1 + 1 = a := by omega
        rw [e3] at hma
        omega
  · rw [hc]
    refine ⟨⟨by omega, h2, ?_, ?_, ?_, ?_⟩, by omega, by omega⟩
    · by_contra hcon
      have e : j - a + 1 = L + 1 := by omega
      have hc' := hP.const (j - a + 1) (by omega)
      omega
    · rw [e1]; omega
    · rw [e1]; omega
    · intro b hb hbL
      have hm := h6 b hb (by omega)
      have e4 : j + 1 - b = j - b + 1 := by omega
      rw [e4]
      have := hP.mono (j - b)
      omega
  · rw [hc]
    have hsum : P a + P (j - a) = a := by omega
    have hy1 := hP.mono a
    have hy2 := hP.step a
    have e5 : j + 1 - (a + 1) = j - a := by omega
    refine ⟨⟨by omega, ?_, by omega, ?_, ?_, ?_⟩, by omega, by omega⟩
    · by_contra hcon
      have haL : a = L := by omega
      have := hP.le_top (j - a + 1)
      subst haL
      omega
    · rw [e5]; omega
    · rw [e5]; omega
    · intro b hb hbL
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | hb'
      · have hm := h6 b hb' (by omega)
        have e4 : j + 1 - b = j - b + 1 := by omega
        rw [e4]
        have := hP.mono (j - b)
        omega
      · subst hb'
        rw [e1]
        omega

lemma Fr_inv (hP : Dyck L P) : ∀ j, j ≤ 2 * L → FInv P L j (Fr P j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨le_refl _, Nat.zero_le _, by omega, ?_, ?_, ?_⟩
    · simp [Fr, hP.zero]
    · simp [Fr, hP.zero]
    · intro b hb; simp [Fr] at hb
  | succ j ih =>
    intro hj
    exact (Fr_succ hP hj (ih (by omega))).1

lemma Fr_incr (hP : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    Fr P j ≤ Fr P (j + 1) ∧ Fr P (j + 1) ≤ Fr P j + 1 :=
  (Fr_succ hP hj (Fr_inv hP j (by omega))).2

lemma Fr_end (hP : Dyck L P) : Fr P (2 * L) = L := by
  have h := Fr_inv hP (2 * L) le_rfl
  have := h.le_L; have := h.ge; omega

lemma Fr_lt (hP : Dyck L P) {j : ℕ} (hj : j < 2 * L) : j < Fr P j + L := by
  have h := Fr_inv hP j hj.le
  have h1 := h.ge; have h2 := h.lo; have h2' := h.le_L
  by_contra hcon
  have e : j - Fr P j = L := by omega
  rw [e] at h2
  have := hP.above (Fr P j) h2'
  have := hP.last
  omega

lemma FInv_unique {j a₁ a₂ : ℕ} (h₁ : FInv P L j a₁) (h₂ : FInv P L j a₂) : a₁ = a₂ := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := h₂.min a₁ hlt h₁.ge; have := h₁.lo; omega
  · have := h₁.min a₂ hlt h₂.ge; have := h₂.lo; omega

lemma Fr_mono (hP : Dyck L P) (hQ : Dyck L Q) (hPQ : ∀ t, P t ≤ Q t) {j : ℕ} (hj : j ≤ 2 * L) :
    Fr P j ≤ Fr Q j := by
  have hp := Fr_inv hP j hj
  have hq := Fr_inv hQ j hj
  by_contra hcon
  have hm := hp.min (Fr Q j) (by omega) hq.ge
  have := hq.lo
  have := hPQ (Fr Q j); have := hPQ (j - Fr Q j)
  omega

lemma Fop_dyck (hP : Dyck L P) : Dyck (2 * L) (Fop L P) where
  zero := by simp [Fop, Fr]
  mono := by
    intro t
    unfold Fop
    rcases lt_or_ge t (2 * L) with ht | ht
    · rw [min_eq_left ht.le, min_eq_left ht]; exact (Fr_incr hP ht).1
    · rw [min_eq_right ht, min_eq_right (by omega)]
  step := by
    intro t
    unfold Fop
    rcases lt_or_ge t (2 * L) with ht | ht
    · rw [min_eq_left ht.le, min_eq_left ht]; exact (Fr_incr hP ht).2
    · rw [min_eq_right ht, min_eq_right (by omega)]; omega
  const := by
    intro t ht
    unfold Fop
    rw [min_eq_right ht, min_self]
  above := by
    intro t ht
    unfold Fop
    rw [min_eq_left ht]
    have h := Fr_inv hP t ht
    have h1 := hP.above (Fr P t) h.le_L
    have h2 := hP.above (t - Fr P t) (by have := h.ge; omega)
    have := h.lo; have := h.le_j
    omega
  last := by
    unfold Fop
    rw [min_self, Fr_end hP]

lemma Fop_mono (hP : Dyck L P) (hQ : Dyck L Q) (hPQ : ∀ t, P t ≤ Q t) (j : ℕ) :
    Fop L P j ≤ Fop L Q j :=
  Fr_mono hP hQ hPQ (min_le_right _ _)

lemma Fop_end (hP : Dyck L P) : Fop L P (2 * L) = L := by
  unfold Fop; rw [min_self, Fr_end hP]

lemma Fop_irr (hP : Dyck L P) (hI : Irr L P) : Irr (2 * L) (Fop L P) := by
  intro t ht0 htL
  unfold Fop
  rw [min_eq_left htL.le]
  have h := Fr_inv hP t htL.le
  have h1 := (Fop_dyck hP).above t htL.le
  unfold Fop at h1
  rw [min_eq_left htL.le] at h1
  by_contra hcon
  have e : t - Fr P t = Fr P t := by omega
  have hlo := h.lo
  rw [e] at hlo
  have hpos : 0 < Fr P t := by omega
  have hlt : Fr P t < L := by omega
  have := hI (Fr P t) hpos hlt
  omega

/-- Symmetry: the reflected threshold at `2L - j` is `L - j + A(j)`. -/
lemma Fr_sym_aux (hP : Dyck L P) (hS : Sym L P) {j : ℕ} (hj : j ≤ L) :
    FInv P L (2 * L - j) (L - j + Fr P j) := by
  have h := Fr_inv hP j (by omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  generalize Fr P j = a at *
  have hlast := hP.last
  have s1 := hS (j - a) (by omega)
  have s2 := hS a h2
  have e1 : L - (j - a) = L - j + a := by omega
  have e2 : 2 * L - j - (L - j + a) = L - a := by omega
  rw [e1] at s1
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [e2]; omega
  · rw [e2]; omega
  · intro b hb hbL
    have hb0 : L - j ≤ b := by omega
    have hm := h6 (b - (L - j)) (by omega) (by omega)
    have s3 := hS (j - (b - (L - j))) (by omega)
    have s4 := hS (b - (L - j)) (by omega)
    have e3 : L - (j - (b - (L - j))) = b := by omega
    have e4 : L - (b - (L - j)) = 2 * L - j - b := by omega
    rw [e3] at s3
    rw [e4] at s4
    omega

lemma Fr_sym (hP : Dyck L P) (hS : Sym L P) {j : ℕ} (hj : j ≤ L) :
    Fr P (2 * L - j) = L - j + Fr P j :=
  FInv_unique (Fr_inv hP _ (by omega)) (Fr_sym_aux hP hS hj)

lemma Fop_sym (hP : Dyck L P) (hS : Sym L P) : Sym (2 * L) (Fop L P) := by
  intro i hi
  rw [Fop_end hP]
  unfold Fop
  rw [min_eq_left hi, min_eq_left (by omega : 2 * L - i ≤ 2 * L)]
  rcases le_total i L with hiL | hiL
  · rw [Fr_sym hP hS hiL]
    have := (Fr_inv hP i (by omega)).le_j
    omega
  · have h := Fr_sym hP hS (j := 2 * L - i) (by omega)
    have e : 2 * L - (2 * L - i) = i := by omega
    rw [e] at h
    have := (Fr_inv hP (2 * L - i) (by omega)).le_j
    omega


/-! ### The last threshold operator -/

/-- Raw recursion of the second doubling operator: `B(j) = P(B(j-1)+1) + P(j-1-B(j-1))`. -/
def Gr (P : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => P (Gr P j + 1) + P (j - Gr P j)

/-- The second doubling operator, made constant after `2L`. -/
def Gop (L : ℕ) (P : ℕ → ℕ) (j : ℕ) : ℕ := Gr P (min j (2 * L))

/-- `b` is the last nonpositive threshold of `d_j(b) = b - P(b) - P(j-b)` on its admissible range. -/
structure GInv (P : ℕ → ℕ) (L j b : ℕ) : Prop where
  le_j : b ≤ j
  le_L : b ≤ L
  ge : j ≤ b + L
  lo : b ≤ P b + P (j - b)
  hi : P b + P (j - b) ≤ b + 1
  max : ∀ b', b < b' → b' ≤ j → b' ≤ L → P b' + P (j - b') < b'

lemma Gr_succ (hP : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) (hI : GInv P L j (Gr P j)) :
    GInv P L (j + 1) (Gr P (j + 1)) ∧ Gr P j ≤ Gr P (j + 1) ∧ Gr P (j + 1) ≤ Gr P j + 1 := by
  have hdef : Gr P (j + 1) = P (Gr P j + 1) + P (j - Gr P j) := rfl
  rw [hdef]
  generalize Gr P j = b at hI ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  have hy1 := hP.mono b
  have hy2 := hP.step b
  have hlast := hP.last
  have hA := hP.above b h2
  have e1 : j + 1 - b = j - b + 1 := by omega
  have hz1 := hP.mono (j - b)
  have hz2 := hP.step (j - b)
  have hmax' : ∀ b', b + 1 < b' → b' ≤ j + 1 → b' ≤ L → P b' + P (j + 1 - b') < b' := by
    intro b' hb' hbj hbL
    have hm := h6 (b' - 1) (by omega) (by omega) (by omega)
    have e2 : j + 1 - b' = j - (b' - 1) := by omega
    have hs := hP.step (b' - 1)
    have e3 : b' - 1 + 1 = b' := by omega
    rw [e3] at hs
    rw [e2]
    omega
  rcases (by omega : P (b + 1) + P (j - b) = b + 2 ∨ P (b + 1) + P (j - b) = b + 1 ∨
      P (b + 1) + P (j - b) = b) with hc | hc | hc
  · exfalso
    by_cases hbj : b = j
    · subst hbj
      have := hP.le_self b
      simp only [Nat.sub_self, hP.zero] at h4 h5 hc
      omega
    · by_cases hbL : b = L
      · subst hbL
        have := hP.const (b + 1) (by omega)
        omega
      · have hm := h6 (b + 1) (by omega) (by omega) (by omega)
        have hs := hP.step (j - (b + 1))
        have e4 : j - (b + 1) + 1 = j - b := by omega
        rw [e4] at hs
        omega
  · rw [hc]
    refine ⟨⟨by omega, ?_, by omega, ?_, ?_, ?_⟩, by omega, by omega⟩
    · by_contra hcon
      have hbL : b = L := by omega
      subst hbL
      have := hP.const (b + 1) (by omega)
      have := hP.le_top (j - b)
      omega
    · have e5 : j + 1 - (b + 1) = j - b := by omega
      rw [e5]; omega
    · have e5 : j + 1 - (b + 1) = j - b := by omega
      rw [e5]; omega
    · intro b' hb' hbj hbL
      exact hmax' b' hb' hbj hbL
  · rw [hc]
    refine ⟨⟨by omega, h2, ?_, ?_, ?_, ?_⟩, by omega, by omega⟩
    · by_contra hcon
      have e : j - b = L := by omega
      rw [e] at h4 h5 hc
      omega
    · rw [e1]; omega
    · rw [e1]; omega
    · intro b' hb' hbj hbL
      rcases (by omega : b' = b + 1 ∨ b + 1 < b') with hb'' | hb''
      · subst hb''
        have e5 : j + 1 - (b + 1) = j - b := by omega
        rw [e5]; omega
      · exact hmax' b' hb'' hbj hbL

lemma Gr_inv (hP : Dyck L P) : ∀ j, j ≤ 2 * L → GInv P L j (Gr P j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨le_refl _, Nat.zero_le _, by omega, ?_, ?_, ?_⟩
    · simp [Gr, hP.zero]
    · simp [Gr, hP.zero]
    · intro b' hb' hbj; simp [Gr] at hb'; omega
  | succ j ih =>
    intro hj
    exact (Gr_succ hP hj (ih (by omega))).1

lemma Gr_incr (hP : Dyck L P) {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    Gr P j ≤ Gr P (j + 1) ∧ Gr P (j + 1) ≤ Gr P j + 1 :=
  (Gr_succ hP hj (Gr_inv hP j (by omega))).2

lemma Gr_end (hP : Dyck L P) : Gr P (2 * L) = L := by
  have h := Gr_inv hP (2 * L) le_rfl
  have := h.le_L; have := h.ge; omega

lemma GInv_unique {j b₁ b₂ : ℕ} (h₁ : GInv P L j b₁) (h₂ : GInv P L j b₂) : b₁ = b₂ := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := h₁.max b₂ hlt h₂.le_j h₂.le_L; have := h₂.lo; omega
  · have := h₂.max b₁ hlt h₁.le_j h₁.le_L; have := h₁.lo; omega

lemma Gr_mono (hP : Dyck L P) (hQ : Dyck L Q) (hPQ : ∀ t, P t ≤ Q t) {j : ℕ} (hj : j ≤ 2 * L) :
    Gr P j ≤ Gr Q j := by
  have hp := Gr_inv hP j hj
  have hq := Gr_inv hQ j hj
  by_contra hcon
  have hm := hq.max (Gr P j) (by omega) hp.le_j hp.le_L
  have := hp.lo
  have := hPQ (Gr P j); have := hPQ (j - Gr P j)
  omega

lemma Gop_dyck (hP : Dyck L P) : Dyck (2 * L) (Gop L P) where
  zero := by simp [Gop, Gr]
  mono := by
    intro t
    unfold Gop
    rcases lt_or_ge t (2 * L) with ht | ht
    · rw [min_eq_left ht.le, min_eq_left ht]; exact (Gr_incr hP ht).1
    · rw [min_eq_right ht, min_eq_right (by omega)]
  step := by
    intro t
    unfold Gop
    rcases lt_or_ge t (2 * L) with ht | ht
    · rw [min_eq_left ht.le, min_eq_left ht]; exact (Gr_incr hP ht).2
    · rw [min_eq_right ht, min_eq_right (by omega)]; omega
  const := by
    intro t ht
    unfold Gop
    rw [min_eq_right ht, min_self]
  above := by
    intro t ht
    unfold Gop
    rw [min_eq_left ht]
    have h := Gr_inv hP t ht
    by_contra hcon
    have hb1 : Gr P t + 1 ≤ L := by have := h.le_L; omega
    have hm := h.max (Gr P t + 1) (by omega) (by omega) hb1
    have h1 := hP.above (Gr P t + 1) hb1
    have h2 := hP.above (t - (Gr P t + 1)) (by have := h.ge; omega)
    omega
  last := by
    unfold Gop
    rw [min_self, Gr_end hP]

lemma Gop_mono (hP : Dyck L P) (hQ : Dyck L Q) (hPQ : ∀ t, P t ≤ Q t) (j : ℕ) :
    Gop L P j ≤ Gop L Q j :=
  Gr_mono hP hQ hPQ (min_le_right _ _)

lemma Gop_end (hP : Dyck L P) : Gop L P (2 * L) = L := by
  unfold Gop; rw [min_self, Gr_end hP]

lemma Gr_sym_aux (hP : Dyck L P) (hS : Sym L P) {j : ℕ} (hj : j ≤ L) :
    GInv P L (2 * L - j) (L - j + Gr P j) := by
  have h := Gr_inv hP j (by omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  generalize Gr P j = b at *
  have hlast := hP.last
  have s1 := hS (j - b) (by omega)
  have s2 := hS b h2
  have e1 : L - (j - b) = L - j + b := by omega
  have e2 : 2 * L - j - (L - j + b) = L - b := by omega
  rw [e1] at s1
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [e2]; omega
  · rw [e2]; omega
  · intro b' hb' hbj hbL
    have hm := h6 (b' - (L - j)) (by omega) (by omega) (by omega)
    have s3 := hS (j - (b' - (L - j))) (by omega)
    have s4 := hS (b' - (L - j)) (by omega)
    have e3 : L - (j - (b' - (L - j))) = b' := by omega
    have e4 : L - (b' - (L - j)) = 2 * L - j - b' := by omega
    rw [e3] at s3
    rw [e4] at s4
    omega

lemma Gr_sym (hP : Dyck L P) (hS : Sym L P) {j : ℕ} (hj : j ≤ L) :
    Gr P (2 * L - j) = L - j + Gr P j :=
  GInv_unique (Gr_inv hP _ (by omega)) (Gr_sym_aux hP hS hj)

lemma Gop_sym (hP : Dyck L P) (hS : Sym L P) : Sym (2 * L) (Gop L P) := by
  intro i hi
  rw [Gop_end hP]
  unfold Gop
  rw [min_eq_left hi, min_eq_left (by omega : 2 * L - i ≤ 2 * L)]
  rcases le_total i L with hiL | hiL
  · rw [Gr_sym hP hS hiL]
    have := (Gr_inv hP i (by omega)).le_j
    omega
  · have h := Gr_sym hP hS (j := 2 * L - i) (by omega)
    have e : 2 * L - (2 * L - i) = i := by omega
    rw [e] at h
    have := (Gr_inv hP (2 * L - i) (by omega)).le_j
    omega

/-! ### The perturbation `T` -/

/-- `T(u)`: delete the first `1` and the last `0` of `u` and insert a complementary pair in the middle.
In prefix counts: `P(i+1) - 1` before the middle `m = P L`, and `P(i-1)` from the middle on. -/
def Top (L : ℕ) (P : ℕ → ℕ) (i : ℕ) : ℕ := if i < P L then P (i + 1) - 1 else P (i - 1)

section Top

variable (hP : Dyck L P) (hS : Sym L P) (hI : Irr L P) (hL : 4 ≤ L)
include hP hS hL

lemma pred_end : P (L - 1) = P L := by
  have := hS 1 (by omega)
  have := hP.one (by omega)
  omega

omit hS in
lemma Top_le (i : ℕ) : Top L P i ≤ P i := by
  unfold Top
  split_ifs with h
  · have := hP.step i; omega
  · have := hP.mono (i - 1)
    have hl := hP.last
    have e : i - 1 + 1 = i := by omega
    rw [e] at this; exact this

lemma Top_end : Top L P L = P L := by
  unfold Top
  have hl := hP.last
  rw [if_neg (by omega)]
  exact pred_end hP hS hL

include hI in
lemma Top_dyck : Dyck L (Top L P) where
  zero := by
    unfold Top
    have hl := hP.last
    rw [if_pos (by omega), hP.one (by omega)]
  mono := by
    intro t
    have hl := hP.last
    have h1 := hP.mono' (show 1 ≤ t + 1 by omega)
    have ho := hP.one (by omega)
    unfold Top
    split_ifs with ha hb hb
    · have := hP.mono (t + 1); omega
    · have e : t + 1 - 1 = t := by omega
      rw [e]; have := hP.step t; omega
    · omega
    · have e : t + 1 - 1 = t := by omega
      rw [e]
      have := hP.mono (t - 1)
      have e2 : t - 1 + 1 = t := by omega
      rw [e2] at this; exact this
  step := by
    intro t
    have hl := hP.last
    have h1 := hP.mono' (show 1 ≤ t + 1 by omega)
    have ho := hP.one (by omega)
    unfold Top
    split_ifs with ha hb hb
    · have := hP.step (t + 1); omega
    · omega
    · have e : t + 1 - 1 = t := by omega
      rw [e]; have := hP.mono t; omega
    · have e : t + 1 - 1 = t := by omega
      rw [e]
      have := hP.step (t - 1)
      have e2 : t - 1 + 1 = t := by omega
      rw [e2] at this; exact this
  const := by
    intro t ht
    have hl := hP.last
    have hpe := pred_end hP hS hL
    unfold Top
    rw [if_neg (by omega), if_neg (by omega)]
    rcases (by omega : t - 1 = L - 1 ∨ L ≤ t - 1) with h | h
    · rw [h]
    · rw [hP.const (t - 1) h, hpe]
  above := by
    intro t ht
    have hl := hP.last
    have hpe := pred_end hP hS hL
    unfold Top
    split_ifs with h
    · have := hI (t + 1) (by omega) (by omega); omega
    · rcases (by omega : t = L ∨ t < L) with h' | h'
      · subst h'; omega
      · have := hI (t - 1) (by omega) (by omega); omega
  last := by
    have hl := hP.last
    unfold Top
    rw [if_neg (by omega), pred_end hP hS hL, hl]

lemma Top_sym : Sym L (Top L P) := by
  intro i hi
  rw [Top_end hP hS hL]
  have hl := hP.last
  unfold Top
  rcases lt_trichotomy i (P L) with h | h | h
  · rw [if_neg (by omega), if_pos h]
    have s := hS (i + 1) (by omega)
    have e : L - i - 1 = L - (i + 1) := by omega
    rw [e]
    have := hP.mono' (show 1 ≤ i + 1 by omega)
    have := hP.one (by omega)
    omega
  · subst h
    have e : L - P L = P L := by omega
    rw [e]
    omega
  · rw [if_pos (by omega), if_neg (by omega)]
    have s := hS (i - 1) (by omega)
    have e : L - (i - 1) = L - i + 1 := by omega
    rw [e] at s
    have := hP.mono' (show 1 ≤ L - i + 1 by omega)
    have := hP.one (by omega)
    omega

end Top


/-! ### Helpers -/

lemma Dyck.add_le (hP : Dyck L P) {s t : ℕ} (hst : s ≤ t) : P t ≤ P s + (t - s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hP.step (s + k)
    have h2 := ih (Nat.le_add_right s k)
    have e : s + (k + 1) = s + k + 1 := by omega
    rw [e]
    omega

lemma Fop_eq {j : ℕ} (hj : j ≤ 2 * L) : Fop L P j = Fr P j := by
  unfold Fop; rw [min_eq_left hj]

lemma Gop_eq {j : ℕ} (hj : j ≤ 2 * L) : Gop L P j = Gr P j := by
  unfold Gop; rw [min_eq_left hj]

lemma Fop_inv (hP : Dyck L P) {j : ℕ} (hj : j ≤ 2 * L) : FInv P L j (Fop L P j) := by
  rw [Fop_eq hj]; exact Fr_inv hP j hj

lemma Gop_inv (hP : Dyck L P) {j : ℕ} (hj : j ≤ 2 * L) : GInv P L j (Gop L P j) := by
  rw [Gop_eq hj]; exact Gr_inv hP j hj

lemma Fop_succ {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    Fop L P (j + 1) = P (Fop L P j) + P (j + 1 - Fop L P j) := by
  rw [Fop_eq hj, Fop_eq (by omega)]; rfl

lemma Gop_succ {j : ℕ} (hj : j + 1 ≤ 2 * L) :
    Gop L P (j + 1) = P (Gop L P j + 1) + P (j - Gop L P j) := by
  rw [Gop_eq hj, Gop_eq (by omega)]; rfl

/-! ### The key lemma: `G(F(T u)) ≤ T(F(F u))` -/

section Key

variable {u : ℕ → ℕ} (hu : Dyck L u) (hs : Sym L u) (hi : Irr L u) (hL : 4 ≤ L)
include hu hs hi hL

theorem key_core {T H K W Z : ℕ → ℕ} (hTdef : T = Top L u) (hHdef : H = Fop L u)
    (hKdef : K = Fop L T) (hWdef : W = Fop (2 * L) H) (hZdef : Z = Gop (2 * L) K) (t : ℕ) :
    Z t ≤ Top (2 * (2 * L)) W t := by
  -- the objects and their properties
  have hT : Dyck L T := by rw [hTdef]; exact Top_dyck hu hs hi hL
  have hTs : Sym L T := by rw [hTdef]; exact Top_sym hu hs hL
  have hTle : ∀ t, T t ≤ u t := by rw [hTdef]; exact Top_le hu hL
  have hH : Dyck (2 * L) H := by rw [hHdef]; exact Fop_dyck hu
  have hHs : Sym (2 * L) H := by rw [hHdef]; exact Fop_sym hu hs
  have hHi : Irr (2 * L) H := by rw [hHdef]; exact Fop_irr hu hi
  have hK : Dyck (2 * L) K := by rw [hKdef]; exact Fop_dyck hT
  have hKs : Sym (2 * L) K := by rw [hKdef]; exact Fop_sym hT hTs
  have hKH : ∀ t, K t ≤ H t := by rw [hKdef, hHdef]; exact Fop_mono hT hu hTle
  have hW : Dyck (2 * (2 * L)) W := by rw [hWdef]; exact Fop_dyck hH
  have hWs : Sym (2 * (2 * L)) W := by rw [hWdef]; exact Fop_sym hH hHs
  have hWi : Irr (2 * (2 * L)) W := by rw [hWdef]; exact Fop_irr hH hHi
  have hZ : Dyck (2 * (2 * L)) Z := by rw [hZdef]; exact Gop_dyck hK
  have hZs : Sym (2 * (2 * L)) Z := by rw [hZdef]; exact Gop_sym hK hKs
  have hWend : W (2 * (2 * L)) = 2 * L := by rw [hWdef]; exact Fop_end hH
  have hZend : Z (2 * (2 * L)) = 2 * L := by rw [hZdef]; exact Gop_end hK
  have hFW : ∀ j, j ≤ 2 * (2 * L) → FInv H (2 * L) j (W j) := by
    intro j hj; rw [hWdef]; exact Fop_inv hH hj
  have hGZ : ∀ j, j ≤ 2 * (2 * L) → GInv K (2 * L) j (Z j) := by
    intro j hj; rw [hZdef]; exact Gop_inv hK hj
  have hFu : ∀ q, q ≤ 2 * L → FInv u L q (H q) := by
    intro q hq; rw [hHdef]; exact Fop_inv hu hq
  have hFT : ∀ q, q ≤ 2 * L → FInv T L q (K q) := by
    intro q hq; rw [hKdef]; exact Fop_inv hT hq
  have hWsucc : ∀ j, j + 1 ≤ 2 * (2 * L) → W (j + 1) = H (W j) + H (j + 1 - W j) := by
    intro j hj; rw [hWdef]; exact Fop_succ hj
  have hHsucc : ∀ q, q + 1 ≤ 2 * L → H (q + 1) = u (H q) + u (q + 1 - H q) := by
    intro q hq; rw [hHdef]; exact Fop_succ hq
  have hTval : ∀ i, i < u L → T i = u (i + 1) - 1 := by
    intro i hi'; rw [hTdef]; unfold Top; rw [if_pos hi']
  have hulast := hu.last
  have hu1 := hu.one (by omega)
  -- midpoint identity
  have hmid : H (2 * L - W (2 * L)) = u L := by
    have h := hFW (2 * L) (by omega)
    have hs' := hHs (W (2 * L)) (by have := h.le_j; omega)
    have hHend : H (2 * L) = L := by rw [hHdef]; exact Fop_end hu
    have := h.lo; have := h.hi
    omega
  have hbound : ∀ j, j ≤ 2 * L → H (j - W j) ≤ u L := by
    intro j hj
    have h1 := hW.add_le (show j ≤ 2 * L by omega)
    have h2 := hW.mono' (show j ≤ 2 * L by omega)
    have h3 := hH.mono' (show j - W j ≤ 2 * L - W (2 * L) by omega)
    omega
  -- the contact claim
  have hcontact : ∀ j, j ≤ 2 * L → Z j = W j → W (j + 1) = W j + 1 := by
    intro j hj hzw
    have hF := hFW j (by omega)
    have hG := hGZ j (by omega)
    rw [hzw] at hG
    have hWj := hW.above j (by omega)
    have hlo := hF.lo
    have hWle := hF.le_j
    have hlo' := hG.lo
    have hle1 := hKH (W j)
    have hle2 := hKH (j - W j)
    have hHq : H (j - W j) = K (j - W j) := by omega
    have hq2 : j - W j ≤ L := by omega
    have hFu' := hFu (j - W j) (by omega)
    have hFT' := hFT (j - W j) (by omega)
    have hWs1 := hWsucc j (by omega)
    have e1 : j + 1 - W j = j - W j + 1 := by omega
    rw [e1] at hWs1
    have hHs1 := hHsucc (j - W j) (by omega)
    have hyle := hFu'.le_j
    have e2 : j - W j + 1 - H (j - W j) = j - W j - H (j - W j) + 1 := by omega
    rw [e2] at hHs1
    have hincr1 := hW.mono j
    have hincr2 := hW.step j
    have hHabove := hH.above (j - W j) (by omega)
    have hb := hbound j hj
    by_contra hne
    have hzero : u (H (j - W j)) + u (j - W j - H (j - W j) + 1) = H (j - W j) := by omega
    rcases Nat.eq_zero_or_pos (H (j - W j)) with hy0 | hy0
    · have hq0 : j - W j = 0 := by omega
      rw [hy0, hq0] at hzero
      simp only [Nat.zero_sub, zero_add, hu.zero] at hzero
      omega
    · have hmin := hFT'.min (H (j - W j) - 1) (by omega) (by omega)
      have e3 : j - W j - (H (j - W j) - 1) = j - W j - H (j - W j) + 1 := by omega
      rw [e3] at hmin
      have hTy := hTval (H (j - W j) - 1) (by omega)
      have e4 : H (j - W j) - 1 + 1 = H (j - W j) := by omega
      rw [e4] at hTy
      rw [hTy] at hmin
      have h5 := hTle (j - W j - H (j - W j) + 1)
      have h6 := hu.mono' (show 1 ≤ H (j - W j) by omega)
      omega
  -- domination on the first half
  have hdom : ∀ j, j ≤ 2 * L → Z j ≤ W j := by
    intro j
    induction j with
    | zero => intro _; rw [hZ.zero, hW.zero]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hZ.step j
      have h3 := hW.mono j
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · omega
      · have := hcontact j (by omega) h; omega
  have hfirst : ∀ j, j ≤ 2 * L → Z j ≤ Top (2 * (2 * L)) W j := by
    intro j hj
    unfold Top
    rw [hWend]
    rcases Nat.lt_or_eq_of_le hj with hj' | hj'
    · rw [if_pos hj']
      have h1 := hdom j hj
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · have := hW.mono j; omega
      · have := hcontact j hj h; omega
    · subst hj'
      rw [if_neg (by omega)]
      have h1 := hdom (2 * L) le_rfl
      have hstep := hW.step (2 * L - 1)
      have e : 2 * L - 1 + 1 = 2 * L := by omega
      rw [e] at hstep
      have hmono := hW.mono (2 * L - 1)
      rw [e] at hmono
      rcases (by omega : W (2 * L) = W (2 * L - 1) ∨ W (2 * L) = W (2 * L - 1) + 1) with h | h
      · omega
      · have hsym := hWs (2 * L - 1) (by omega)
        rw [hWend] at hsym
        have e2 : 2 * (2 * L) - (2 * L - 1) = 2 * L + 1 := by omega
        rw [e2] at hsym
        by_contra hcon
        have hzw : Z (2 * L) = W (2 * L) := by omega
        have := hcontact (2 * L) le_rfl hzw
        omega
  -- transfer to the second half by symmetry, and past the end by constancy
  have hTW : Dyck (2 * (2 * L)) (Top (2 * (2 * L)) W) := Top_dyck hW hWs hWi (by omega)
  have hTWs : Sym (2 * (2 * L)) (Top (2 * (2 * L)) W) := Top_sym hW hWs (by omega)
  have hTWend : Top (2 * (2 * L)) W (2 * (2 * L)) = 2 * L := by
    rw [Top_end hW hWs (by omega), hWend]
  rcases le_or_gt t (2 * L) with ht | ht
  · exact hfirst t ht
  · rcases le_or_gt t (2 * (2 * L)) with ht' | ht'
    · have h1 := hfirst (2 * (2 * L) - t) (by omega)
      have s1 := hZs (2 * (2 * L) - t) (by omega)
      have s2 := hTWs (2 * (2 * L) - t) (by omega)
      have e : 2 * (2 * L) - (2 * (2 * L) - t) = t := by omega
      rw [e] at s1 s2
      rw [hZend] at s1
      rw [hTWend] at s2
      omega
    · rw [hZ.const t ht'.le, hTW.const t ht'.le, hZend, hTWend]

theorem key (t : ℕ) :
    Gop (2 * L) (Fop L (Top L u)) t ≤ Top (2 * (2 * L)) (Fop (2 * L) (Fop L u)) t :=
  key_core hu hs hi hL rfl rfl rfl rfl rfl t

end Key

end MO366772

/-! ## Part 4: the dyadic blocks of `c` and `c*`, and the conjecture -/

namespace MO366772

open OMA.S_mo_366772

lemma two_pow_succ' (n : ℕ) : 2 ^ (n + 1) = 2 * 2 ^ n := by ring

/-- The word `10`. -/
def p10 (t : ℕ) : ℕ := min t 1

lemma p10_dyck : Dyck 2 p10 where
  zero := rfl
  mono := by intro t; simp only [p10]; omega
  step := by intro t; simp only [p10]; omega
  const := by intro t ht; simp only [p10]; omega
  above := by intro t ht; simp only [p10]; omega
  last := rfl

lemma p10_sym : Sym 2 p10 := by
  intro i hi
  interval_cases i <;> decide

lemma p10_irr : Irr 2 p10 := by
  intro t ht0 ht2
  interval_cases t
  decide

/-- Prefix counts of the increments of `c` on the block `[2^(k+1), 2^(k+2)]`. -/
def Wk : ℕ → ℕ → ℕ
  | 0 => p10
  | k + 1 => Fop (2 ^ (k + 1)) (Wk k)

/-- The same for `c*`, complemented on the blocks `[2^K, 2^(K+1)]` with `K` odd. -/
def Vk : ℕ → ℕ → ℕ
  | 0 => p10
  | k + 1 => if k % 2 = 0 then Fop (2 ^ (k + 1)) (Vk k) else Gop (2 ^ (k + 1)) (Vk k)

lemma Wk_props : ∀ k, Dyck (2 ^ (k + 1)) (Wk k) ∧ Sym (2 ^ (k + 1)) (Wk k) ∧
    Irr (2 ^ (k + 1)) (Wk k)
  | 0 => ⟨p10_dyck, p10_sym, p10_irr⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := Wk_props k
    rw [two_pow_succ' (k + 1)]
    exact ⟨Fop_dyck h1, Fop_sym h1 h2, Fop_irr h1 h3⟩

lemma Vk_props : ∀ k, Dyck (2 ^ (k + 1)) (Vk k) ∧ Sym (2 ^ (k + 1)) (Vk k)
  | 0 => ⟨p10_dyck, p10_sym⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := Vk_props k
    rw [two_pow_succ' (k + 1)]
    simp only [Vk]
    split_ifs
    · exact ⟨Fop_dyck h1, Fop_sym h1 h2⟩
    · exact ⟨Gop_dyck h1, Gop_sym h1 h2⟩

lemma Vk_succ_even {k : ℕ} (hk : k % 2 = 0) : Vk (k + 1) = Fop (2 ^ (k + 1)) (Vk k) := by
  simp only [Vk, if_pos hk]

lemma Vk_succ_odd {k : ℕ} (hk : k % 2 = 1) : Vk (k + 1) = Gop (2 ^ (k + 1)) (Vk k) := by
  simp only [Vk, if_neg (by omega : ¬ k % 2 = 0)]

/-- On the blocks with odd index `K = k + 1 ≥ 3`, `v_K ≤ T(w_K)`. -/
lemma cmp_even : ∀ n t, Vk (2 * n + 2) t ≤ Top (2 ^ (2 * n + 3)) (Wk (2 * n + 2)) t := by
  intro n
  induction n with
  | zero =>
    intro t
    have hV := (Vk_props 2).1
    obtain ⟨hW, hWs, hWi⟩ := Wk_props 2
    have hTW := Top_dyck hW hWs hWi (by norm_num)
    rcases le_or_gt t 8 with ht | ht
    · interval_cases t <;> decide
    · norm_num at hV hTW ⊢
      rw [hV.const t ht.le, hTW.const t ht.le]
      decide
  | succ n ih =>
    intro t
    have hk : (2 * n + 2) % 2 = 0 := by omega
    have hk1 : (2 * n + 2 + 1) % 2 = 1 := by omega
    have hV := (Vk_props (2 * n + 2)).1
    obtain ⟨hW, hWs, hWi⟩ := Wk_props (2 * n + 2)
    have hL4 : 4 ≤ 2 ^ (2 * n + 2 + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n + 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hTW := Top_dyck hW hWs hWi hL4
    have eV : Vk (2 * (n + 1) + 2) =
        Gop (2 * 2 ^ (2 * n + 2 + 1)) (Fop (2 ^ (2 * n + 2 + 1)) (Vk (2 * n + 2))) := by
      have e : 2 * (n + 1) + 2 = 2 * n + 2 + 1 + 1 := by omega
      rw [e, Vk_succ_odd hk1, Vk_succ_even hk, two_pow_succ' (2 * n + 2 + 1)]
    have eW : Wk (2 * (n + 1) + 2) =
        Fop (2 * 2 ^ (2 * n + 2 + 1)) (Fop (2 ^ (2 * n + 2 + 1)) (Wk (2 * n + 2))) := by
      have e : 2 * (n + 1) + 2 = 2 * n + 2 + 1 + 1 := by omega
      rw [e]
      simp only [Wk]
      rw [two_pow_succ' (2 * n + 2 + 1)]
    have eP : 2 ^ (2 * (n + 1) + 3) = 2 * (2 * 2 ^ (2 * n + 2 + 1)) := by ring
    rw [eV, eW, eP]
    calc Gop (2 * 2 ^ (2 * n + 2 + 1)) (Fop (2 ^ (2 * n + 2 + 1)) (Vk (2 * n + 2))) t
        ≤ Gop (2 * 2 ^ (2 * n + 2 + 1)) (Fop (2 ^ (2 * n + 2 + 1))
            (Top (2 ^ (2 * n + 2 + 1)) (Wk (2 * n + 2)))) t :=
          Gop_mono (Fop_dyck hV) (Fop_dyck hTW) (Fop_mono hV hTW (ih)) t
      _ ≤ _ := key hW hWs hWi hL4 t

/-- `v_K ≤ w_K` on every block. -/
lemma cmp_all (k t : ℕ) : Vk k t ≤ Wk k t := by
  have hcases : k = 0 ∨ k = 1 ∨ ∃ n, k = 2 * n + 2 ∨ k = 2 * n + 3 := by
    match k with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr (Or.inl rfl)
    | k + 2 =>
      right; right
      rcases Nat.even_or_odd' k with ⟨n, hn | hn⟩
      · exact ⟨n, Or.inl (by omega)⟩
      · exact ⟨n, Or.inr (by omega)⟩
  rcases hcases with h | h | ⟨n, h | h⟩
  · subst h; exact le_refl _
  · subst h; exact le_refl _
  · subst h
    obtain ⟨hW, hWs, hWi⟩ := Wk_props (2 * n + 2)
    have h1 := cmp_even n t
    have h2 := Top_le hW (show 4 ≤ 2 ^ (2 * n + 2 + 1) by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n + 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) t
    have e : 2 * n + 3 = 2 * n + 2 + 1 := by omega
    rw [e] at h1
    omega
  · subst h
    have hk : (2 * n + 2) % 2 = 0 := by omega
    have hV := (Vk_props (2 * n + 2)).1
    obtain ⟨hW, hWs, hWi⟩ := Wk_props (2 * n + 2)
    have hL4 : 4 ≤ 2 ^ (2 * n + 2 + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n + 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hTW := Top_dyck hW hWs hWi hL4
    have h1 : ∀ s, Vk (2 * n + 2) s ≤ Top (2 ^ (2 * n + 2 + 1)) (Wk (2 * n + 2)) s := by
      intro s
      have := cmp_even n s
      have e : 2 * n + 3 = 2 * n + 2 + 1 := by omega
      rw [e] at this
      exact this
    have e : 2 * n + 3 = 2 * n + 2 + 1 := by omega
    rw [e, Vk_succ_even hk]
    calc Fop (2 ^ (2 * n + 2 + 1)) (Vk (2 * n + 2)) t
        ≤ Fop (2 ^ (2 * n + 2 + 1)) (Top (2 ^ (2 * n + 2 + 1)) (Wk (2 * n + 2))) t :=
          Fop_mono hV hTW h1 t
      _ ≤ Fop (2 ^ (2 * n + 2 + 1)) (Wk (2 * n + 2)) t :=
          Fop_mono hTW hW (Top_le hW hL4) t
      _ = Wk (2 * n + 2 + 1) t := rfl

/-! ### Values of `c` on the blocks -/

lemma c_one : c 1 = 1 := by rw [c]
lemma c_two : c 2 = 1 := by rw [c]
lemma c_succ3 (n : ℕ) :
    c (n + 3) = c (min (c (n + 2)) (n + 2)) + c (n + 3 - max (c (n + 2)) 1) := by
  rw [c]
lemma cStar_one : cStar 1 = 1 := by rw [cStar]
lemma cStar_two : cStar 2 = 1 := by rw [cStar]
lemma cStar_succ3 (n : ℕ) :
    cStar (n + 3) = n + 3 - cStar (min (cStar (n + 2)) (n + 2))
      - cStar (n + 3 - max (cStar (n + 2)) 1) := by
  rw [cStar]

lemma c_three : c 3 = 2 := by
  have := c_succ3 0
  norm_num [c_two, c_one] at this
  exact this

lemma c_four : c 4 = 2 := by
  have := c_succ3 1
  norm_num [c_three, c_two] at this
  exact this

lemma cStar_three : cStar 3 = 1 := by
  have := cStar_succ3 0
  norm_num [cStar_two, cStar_one] at this
  exact this

lemma cStar_four : cStar 4 = 2 := by
  have := cStar_succ3 1
  norm_num [cStar_three, cStar_one] at this
  exact this

lemma c_block_succ (k : ℕ)
    (ih : ∀ t, t ≤ 2 ^ (k + 1) → c (2 ^ (k + 1) + t) = 2 ^ k + Wk k t) :
    ∀ j, j ≤ 2 * 2 ^ (k + 1) →
      c (2 * 2 ^ (k + 1) + j) = 2 ^ (k + 1) + Fop (2 ^ (k + 1)) (Wk k) j := by
  have hW := (Wk_props k).1
  have hLk := two_pow_succ' k
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hlast := hW.last
  intro j
  induction j with
  | zero =>
    intro _
    have e : 2 * 2 ^ (k + 1) + 0 = 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
    rw [e, ih _ le_rfl]
    have : Fop (2 ^ (k + 1)) (Wk k) 0 = 0 := by simp [Fop, Fr]
    rw [this]
    omega
  | succ j ihj =>
    intro hj
    rw [Fop_succ hj]
    have hA := Fop_inv hW (j := j) (by omega)
    have hlt := Fr_lt hW (j := j) (by omega)
    rw [← Fop_eq (L := 2 ^ (k + 1)) (P := Wk k) (j := j) (by omega)] at hlt
    have hprev := ihj (by omega)
    generalize Fop (2 ^ (k + 1)) (Wk k) j = A at hA hlt hprev ⊢
    have hAj := hA.le_j
    have hAL := hA.le_L
    have e : 2 * 2 ^ (k + 1) + (j + 1) = 2 * 2 ^ (k + 1) + j - 2 + 3 := by omega
    rw [e, c_succ3]
    have e2 : 2 * 2 ^ (k + 1) + j - 2 + 2 = 2 * 2 ^ (k + 1) + j := by omega
    rw [e2, hprev, min_eq_left (by omega), max_eq_left (by omega)]
    have e3 : 2 * 2 ^ (k + 1) + j - 2 + 3 - (2 ^ (k + 1) + A) = 2 ^ (k + 1) + (j + 1 - A) := by
      omega
    rw [e3, ih A hAL, ih (j + 1 - A) (by omega)]
    omega

lemma c_block : ∀ k t, t ≤ 2 ^ (k + 1) → c (2 ^ (k + 1) + t) = 2 ^ k + Wk k t := by
  intro k
  induction k with
  | zero =>
    intro t ht
    norm_num at ht ⊢
    interval_cases t
    · simp [Wk, p10, c_two]
    · simp [Wk, p10, c_three]
    · simp [Wk, p10, c_four]
  | succ k ih =>
    intro t ht
    rw [two_pow_succ' (k + 1)] at ht ⊢
    exact c_block_succ k ih t ht

/-! ### Values of `c*` on the blocks -/

lemma cs_step_even (k : ℕ)
    (ih : ∀ t, t ≤ 2 ^ (k + 1) → cStar (2 ^ (k + 1) + t) + Vk k t = 2 ^ k + t) :
    ∀ j, j ≤ 2 * 2 ^ (k + 1) →
      cStar (2 * 2 ^ (k + 1) + j) = 2 ^ (k + 1) + Fop (2 ^ (k + 1)) (Vk k) j := by
  have hV := (Vk_props k).1
  have hLk := two_pow_succ' k
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hlast := hV.last
  intro j
  induction j with
  | zero =>
    intro _
    have e : 2 * 2 ^ (k + 1) + 0 = 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
    have h0 := ih _ le_rfl
    rw [e]
    have : Fop (2 ^ (k + 1)) (Vk k) 0 = 0 := by simp [Fop, Fr]
    rw [this]
    omega
  | succ j ihj =>
    intro hj
    rw [Fop_succ hj]
    have hA := Fop_inv hV (j := j) (by omega)
    have hlt := Fr_lt hV (j := j) (by omega)
    rw [← Fop_eq (L := 2 ^ (k + 1)) (P := Vk k) (j := j) (by omega)] at hlt
    have hprev := ihj (by omega)
    generalize Fop (2 ^ (k + 1)) (Vk k) j = A at hA hlt hprev ⊢
    have hAj := hA.le_j
    have hAL := hA.le_L
    have e : 2 * 2 ^ (k + 1) + (j + 1) = 2 * 2 ^ (k + 1) + j - 2 + 3 := by omega
    rw [e, cStar_succ3]
    have e2 : 2 * 2 ^ (k + 1) + j - 2 + 2 = 2 * 2 ^ (k + 1) + j := by omega
    rw [e2, hprev, min_eq_left (by omega), max_eq_left (by omega)]
    have e3 : 2 * 2 ^ (k + 1) + j - 2 + 3 - (2 ^ (k + 1) + A) = 2 ^ (k + 1) + (j + 1 - A) := by
      omega
    rw [e3]
    have h1 := ih A hAL
    have h2 := ih (j + 1 - A) (by omega)
    have h3 := hV.le_self A
    have h4 := hV.le_self (j + 1 - A)
    omega

lemma cs_step_odd (k : ℕ)
    (ih : ∀ t, t ≤ 2 ^ (k + 1) → cStar (2 ^ (k + 1) + t) = 2 ^ k + Vk k t) :
    ∀ j, j ≤ 2 * 2 ^ (k + 1) →
      cStar (2 * 2 ^ (k + 1) + j) + Gop (2 ^ (k + 1)) (Vk k) j = 2 ^ (k + 1) + j := by
  have hV := (Vk_props k).1
  have hLk := two_pow_succ' k
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hlast := hV.last
  have hV1 := hV.one (by omega)
  have hV0 := hV.zero
  -- one step of the block recursion; the value at `2L+1` may be needed when the threshold is `L`
  have hstep : ∀ j, j + 1 ≤ 2 * 2 ^ (k + 1) →
      cStar (2 * 2 ^ (k + 1) + j) + Gop (2 ^ (k + 1)) (Vk k) j = 2 ^ (k + 1) + j →
      (Gop (2 ^ (k + 1)) (Vk k) j = 2 ^ (k + 1) → cStar (2 * 2 ^ (k + 1) + 1) = 2 ^ (k + 1)) →
      cStar (2 * 2 ^ (k + 1) + (j + 1)) + Gop (2 ^ (k + 1)) (Vk k) (j + 1) =
        2 ^ (k + 1) + (j + 1) := by
    intro j hj hprev hone
    rw [Gop_succ hj]
    have hB := Gop_inv hV (j := j) (by omega)
    generalize Gop (2 ^ (k + 1)) (Vk k) j = B at hB hprev hone ⊢
    have hBj := hB.le_j
    have hBL := hB.le_L
    have hBge := hB.ge
    have e : 2 * 2 ^ (k + 1) + (j + 1) = 2 * 2 ^ (k + 1) + j - 2 + 3 := by omega
    rw [e, cStar_succ3]
    have e2 : 2 * 2 ^ (k + 1) + j - 2 + 2 = 2 * 2 ^ (k + 1) + j := by omega
    have hcur : cStar (2 * 2 ^ (k + 1) + j) = 2 ^ (k + 1) + (j - B) := by omega
    rw [e2, hcur, min_eq_left (by omega), max_eq_left (by omega)]
    have e3 : 2 * 2 ^ (k + 1) + j - 2 + 3 - (2 ^ (k + 1) + (j - B)) = 2 ^ (k + 1) + (B + 1) := by
      omega
    rw [e3, ih (j - B) (by omega)]
    have hc2 : cStar (2 ^ (k + 1) + (B + 1)) = 2 ^ k + Vk k (B + 1) := by
      rcases Nat.lt_or_ge B (2 ^ (k + 1)) with hBl | hBl
      · exact ih (B + 1) (by omega)
      · have hBe : B = 2 ^ (k + 1) := by omega
        have e4 : 2 ^ (k + 1) + (B + 1) = 2 * 2 ^ (k + 1) + 1 := by omega
        rw [e4, hone hBe, hV.const (B + 1) (by omega)]
        omega
    rw [hc2]
    have h3 := hV.le_self (j - B)
    have h4 := hV.le_self (B + 1)
    omega
  have h0 : cStar (2 * 2 ^ (k + 1) + 0) + Gop (2 ^ (k + 1)) (Vk k) 0 = 2 ^ (k + 1) + 0 := by
    have e : 2 * 2 ^ (k + 1) + 0 = 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
    rw [e, ih _ le_rfl]
    have : Gop (2 ^ (k + 1)) (Vk k) 0 = 0 := by simp [Gop, Gr]
    rw [this]
    omega
  have h1 := hstep 0 (by omega) h0 (by
    intro hcon
    have : Gop (2 ^ (k + 1)) (Vk k) 0 = 0 := by simp [Gop, Gr]
    omega)
  have hG1 : Gop (2 ^ (k + 1)) (Vk k) 1 = 1 := by
    rw [Gop_succ (by omega)]
    have : Gop (2 ^ (k + 1)) (Vk k) 0 = 0 := by simp [Gop, Gr]
    rw [this]
    simp [hV1, hV0]
  have hone : cStar (2 * 2 ^ (k + 1) + 1) = 2 ^ (k + 1) := by
    rw [hG1] at h1
    simpa using h1
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ihj =>
    intro hj
    exact hstep j hj (ihj (by omega)) (fun _ => hone)

lemma cs_block : ∀ k t, t ≤ 2 ^ (k + 1) →
    (k % 2 = 0 → cStar (2 ^ (k + 1) + t) + Vk k t = 2 ^ k + t) ∧
    (k % 2 = 1 → cStar (2 ^ (k + 1) + t) = 2 ^ k + Vk k t) := by
  intro k
  induction k with
  | zero =>
    intro t ht
    refine ⟨fun _ => ?_, fun h => by omega⟩
    norm_num at ht ⊢
    interval_cases t
    · simp [Vk, p10, cStar_two]
    · simp [Vk, p10, cStar_three]
    · simp [Vk, p10, cStar_four]
  | succ k ih =>
    intro t ht
    rw [two_pow_succ' (k + 1)] at ht ⊢
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · refine ⟨fun h => by omega, fun _ => ?_⟩
      rw [Vk_succ_even hk]
      exact cs_step_even k (fun s hs => (ih s hs).1 hk) t ht
    · refine ⟨fun _ => ?_, fun h => by omega⟩
      rw [Vk_succ_odd hk]
      exact cs_step_odd k (fun s hs => (ih s hs).2 hk) t ht

/-! ### The conjecture -/

theorem main_nat (n : ℕ) (hn : 1 ≤ n) : cStar n ≤ c n ∧ n ≤ c n + cStar n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    rw [c_one, cStar_one]
    omega
  · obtain ⟨K, hK⟩ : ∃ K, K = Nat.log 2 n := ⟨_, rfl⟩
    have hK1 : 0 < K := by rw [hK]; exact Nat.log_pos (by norm_num) h
    have hlo : 2 ^ K ≤ n := by rw [hK]; exact Nat.pow_log_le_self 2 (by omega)
    have hhi : n < 2 ^ (K + 1) := by rw [hK]; exact Nat.lt_pow_succ_log_self (by norm_num) n
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    have hpow := two_pow_succ' (k + 1)
    have hpow2 := two_pow_succ' k
    obtain ⟨t, rfl⟩ : ∃ t, n = 2 ^ (k + 1) + t := ⟨n - 2 ^ (k + 1), by omega⟩
    have ht : t ≤ 2 ^ (k + 1) := by omega
    have hc := c_block k t ht
    have hcs := cs_block k t ht
    have hVW := cmp_all k t
    have hVd := (Vk_props k).1.above t ht
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · have := hcs.1 hk2; omega
    · have := hcs.2 hk2; omega

theorem main_proof : ∀ n : ℕ, 1 ≤ n → |(cStar n : ℝ) - n / 2| ≤ (c n : ℝ) - n / 2 := by
  intro n hn
  obtain ⟨h1, h2⟩ := main_nat n hn
  have h1' : (cStar n : ℝ) ≤ c n := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ c n + cStar n := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

end MO366772

theorem OMA.solution : type_of% @OMA.S_mo_366772.main := MO366772.main_proof
