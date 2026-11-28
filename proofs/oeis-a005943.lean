import OMAStatements.S_oeis_a005943
import Mathlib

-- Problem: oeis-a005943 (factor complexity of the Golay-Rudin-Shapiro word A020987)
-- Credit: @Aijy0264561
-- Proof (Allouche 1992 style): grs (2k) = grs k and grs (2k+1) = grs k xor (k mod 2), so a factor at
-- position 2j+b is a fixed function of the parity of j and the factor at j. This gives an exact
-- recursion for factors tagged with their position parity, with injective maps from length 3 on,
-- hence 8L - 8 tagged factors of each length L >= 2. No factor of length 8 occurs at both parities
-- (a finite check), so for n >= 8 the tags are determined and a n = 8n - 8; a 0..a 7 are finite checks.

open Finset

namespace OMA.A005943proof

open OMA.S_oeis_a005943

/-- The number of blocks `11` of `n` among bit positions below `N`. -/
def cnt (n N : ℕ) : ℕ :=
  ((Finset.range N).filter fun i => n.testBit i = true ∧ n.testBit (i + 1) = true).card

lemma grs_eq (n : ℕ) : grs n = cnt n n % 2 := rfl

lemma cnt_ext {n N : ℕ} (h : n ≤ N) : cnt n N = cnt n n := by
  unfold cnt
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra hi
    push Not at hi
    have : n < 2 ^ i := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow this] at h1
    exact absurd h1 (by simp)
  · rintro ⟨hi, h1, h2⟩
    exact ⟨lt_of_lt_of_le hi h, h1, h2⟩

lemma cnt_succ (n N : ℕ) : cnt n (N + 1) =
    cnt (n / 2) N + (if n.testBit 0 = true ∧ n.testBit 1 = true then 1 else 0) := by
  unfold cnt
  rw [card_filter, card_filter, sum_range_succ']
  congr 1
  apply sum_congr rfl
  intro i _
  simp only [Nat.testBit_succ]

lemma testBit_two_mul_zero (k : ℕ) : (2 * k).testBit 0 = false := by
  simp [Nat.testBit_zero]

lemma testBit_two_mul_add_one_zero (k : ℕ) : (2 * k + 1).testBit 0 = true := by
  simp [Nat.testBit_zero]

lemma grs_two_mul (k : ℕ) : grs (2 * k) = grs k := by
  have h : (2 * k) / 2 = k := by omega
  rw [grs_eq, grs_eq, ← cnt_ext (show 2 * k ≤ 2 * k + 1 by omega), cnt_succ, h,
    cnt_ext (show k ≤ 2 * k by omega), testBit_two_mul_zero]
  simp

lemma grs_two_mul_add_one (k : ℕ) : grs (2 * k + 1) = (grs k + k % 2) % 2 := by
  have h : (2 * k + 1) / 2 = k := by omega
  have h1 : (2 * k + 1).testBit 1 = k.testBit 0 := by
    rw [Nat.testBit_succ, h]
  rw [grs_eq, grs_eq, ← cnt_ext (show 2 * k + 1 ≤ 2 * k + 1 + 1 by omega), cnt_succ, h,
    cnt_ext (show k ≤ 2 * k + 1 by omega), testBit_two_mul_add_one_zero, h1, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk] <;> omega

/-- The Golay-Rudin-Shapiro word as a Boolean word. -/
def X (k : ℕ) : Bool := grs k == 1

lemma grs_lt (k : ℕ) : grs k < 2 := Nat.mod_lt _ (by norm_num)

lemma X_two_mul (k : ℕ) : X (2 * k) = X k := by
  unfold X; rw [grs_two_mul]

lemma X_two_mul_add_one (k : ℕ) : X (2 * k + 1) = xor (X k) (k % 2 == 1) := by
  unfold X
  rw [grs_two_mul_add_one]
  have := grs_lt k
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
    interval_cases (grs k) <;> simp [hk]

/-- The factor of length `L` of the word `X` at position `j`. -/
def fac (j L : ℕ) : List Bool := (List.range L).map fun t => X (j + t)

/-- The parity of a position. -/
def par (j : ℕ) : Bool := j % 2 == 1

/-- The factor of length `L` at position `2j + b`, read off from the parity `e` of `j` and the
factor `u` at `j`: letter `t` sits at `2 (j + s/2) + s % 2` with `s = b + t`. -/
def Psi (b : ℕ) (e : Bool) (u : List Bool) (L : ℕ) : List Bool :=
  (List.range L).map fun t =>
    xor (u.getD ((b + t) / 2) false) ((b + t) % 2 == 1 && xor e ((b + t) / 2 % 2 == 1))

lemma getD_fac {j L t : ℕ} (h : t < L) : (fac j L).getD t false = X (j + t) := by
  simp [fac, List.getD_eq_getElem?_getD, h]

lemma getD_Psi {b : ℕ} {e : Bool} {u : List Bool} {L t : ℕ} (h : t < L) :
    (Psi b e u L).getD t false =
      xor (u.getD ((b + t) / 2) false) ((b + t) % 2 == 1 && xor e ((b + t) / 2 % 2 == 1)) := by
  simp [Psi, List.getD_eq_getElem?_getD, h]

lemma length_fac (j L : ℕ) : (fac j L).length = L := by simp [fac]

lemma length_Psi (b : ℕ) (e : Bool) (u : List Bool) (L : ℕ) : (Psi b e u L).length = L := by
  simp [Psi]

lemma par_add (a c : ℕ) : par (a + c) = xor (par a) (par c) := by
  unfold par
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;> simp [Nat.add_mod, ha, hc]

lemma X_split (k : ℕ) (s : ℕ) :
    X (2 * k + s) = xor (X (k + s / 2)) (s % 2 == 1 && xor (par k) (s / 2 % 2 == 1)) := by
  have hs : 2 * k + s = 2 * (k + s / 2) + s % 2 := by omega
  rw [hs]
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · rw [h, add_zero, X_two_mul]; simp
  · rw [h, X_two_mul_add_one]
    have := par_add k (s / 2)
    unfold par at this
    simp only [this]
    simp [par]

lemma fac_split (j b L : ℕ) :
    fac (2 * j + b) L = Psi b (par j) (fac j ((L + b + 1) / 2)) L := by
  have hg : ∀ t ∈ List.range L, (fac j ((L + b + 1) / 2)).getD ((b + t) / 2) false =
      X (j + (b + t) / 2) := fun t ht =>
    getD_fac (show (b + t) / 2 < (L + b + 1) / 2 by have := List.mem_range.1 ht; omega)
  unfold Psi
  conv_lhs => unfold fac
  apply List.map_congr_left
  intro t ht
  rw [show 2 * j + b + t = 2 * j + (b + t) by ring, X_split, hg t ht]

lemma par_two_mul_add (j b : ℕ) (hb : b < 2) : par (2 * j + b) = (b == 1) := by
  unfold par; interval_cases b <;> simp [Nat.add_mod]

/-- Factors of length `L` together with the parity of their position. -/
def Q (L : ℕ) : Set (Bool × List Bool) := Set.range fun j => (par j, fac j L)

lemma Q_rec (L : ℕ) : Q L =
    (fun eu : Bool × List Bool => (false, Psi 0 eu.1 eu.2 L)) '' Q ((L + 1) / 2) ∪
    (fun eu : Bool × List Bool => (true, Psi 1 eu.1 eu.2 L)) '' Q ((L + 2) / 2) := by
  ext ⟨b, w⟩
  simp only [Q, Set.mem_union, Set.mem_image, Set.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j', hb, hw⟩
    have hj : j' = 2 * (j' / 2) + j' % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one j' with h | h
    · left
      have e := fac_split (j' / 2) 0 L
      rw [show 2 * (j' / 2) + 0 = j' by omega] at e
      refine ⟨(par (j' / 2), fac (j' / 2) ((L + 1) / 2)), ⟨j' / 2, rfl⟩, ?_, ?_⟩
      · rw [← hb]; unfold par; simp [h]
      · rw [← hw, e]
    · right
      have e := fac_split (j' / 2) 1 L
      rw [show 2 * (j' / 2) + 1 = j' by omega] at e
      refine ⟨(par (j' / 2), fac (j' / 2) ((L + 2) / 2)), ⟨j' / 2, rfl⟩, ?_, ?_⟩
      · rw [← hb]; unfold par; simp [h]
      · rw [← hw, e]
  · rintro (⟨⟨e, u⟩, ⟨j, hj⟩, hb, hw⟩ | ⟨⟨e, u⟩, ⟨j, hj⟩, hb, hw⟩)
    · simp only [Prod.mk.injEq] at hj
      refine ⟨2 * j + 0, ?_, ?_⟩
      · rw [par_two_mul_add j 0 (by norm_num), ← hb]; rfl
      · rw [fac_split, ← hw, hj.1, hj.2]
    · simp only [Prod.mk.injEq] at hj
      refine ⟨2 * j + 1, ?_, ?_⟩
      · rw [par_two_mul_add j 1 (by norm_num), ← hb]; rfl
      · rw [fac_split, ← hw, hj.1, hj.2]

/-! ### Explicit factor sets of small length -/

def QF0 : Finset (Bool × List Bool) := {(false, []), (true, [])}
def QF1 : Finset (Bool × List Bool) :=
  {(false, [false]), (false, [true]), (true, [false]), (true, [true])}
def QF2 : Finset (Bool × List Bool) :=
  {(false, [false, false]), (false, [false, true]), (false, [true, false]), (false, [true, true]),
   (true, [false, false]), (true, [false, true]), (true, [true, false]), (true, [true, true])}

def stepF (L : ℕ) (A B : Finset (Bool × List Bool)) : Finset (Bool × List Bool) :=
  A.image (fun eu => (false, Psi 0 eu.1 eu.2 L)) ∪ B.image (fun eu => (true, Psi 1 eu.1 eu.2 L))

def QF3 := stepF 3 QF2 QF2
def QF4 := stepF 4 QF2 QF3
def QF5 := stepF 5 QF3 QF3
def QF6 := stepF 6 QF3 QF4
def QF7 := stepF 7 QF4 QF4
def QF8 := stepF 8 QF4 QF5

lemma Q_step {L : ℕ} {A B : Finset (Bool × List Bool)} (hA : Q ((L + 1) / 2) = ↑A)
    (hB : Q ((L + 2) / 2) = ↑B) : Q L = ↑(stepF L A B) := by
  rw [Q_rec, hA, hB, stepF, coe_union, coe_image, coe_image]

lemma mem_Q_of {L : ℕ} {p : Bool × List Bool} (j : ℕ) (h : (par j, fac j L) = p) : p ∈ Q L :=
  ⟨j, h⟩

lemma Q0 : Q 0 = ↑QF0 := by
  ext ⟨b, w⟩
  simp only [mem_coe]
  constructor
  · rintro ⟨j, hj⟩
    simp only [Prod.mk.injEq] at hj
    rw [← hj.1, ← hj.2]
    simp only [fac, List.range_zero, List.map_nil]
    cases par j <;> decide
  · intro h
    have h' : (b, w) = (false, []) ∨ (b, w) = (true, []) := by simpa [QF0] using h
    rcases h' with h' | h'
    · exact mem_Q_of 0 (by rw [h']; rfl)
    · exact mem_Q_of 1 (by rw [h']; rfl)

lemma Q1 : Q 1 = ↑QF1 := by
  ext ⟨b, w⟩
  simp only [mem_coe]
  constructor
  · rintro ⟨j, hj⟩
    simp only [Prod.mk.injEq] at hj
    rw [← hj.1, ← hj.2]
    simp only [fac, List.range_one, List.map_cons, List.map_nil, add_zero]
    cases par j <;> cases X j <;> decide
  · intro h
    have key : ∀ p ∈ QF1, ∃ j ∈ range 8, (par j, fac j 1) = p := by decide
    obtain ⟨j, -, hj⟩ := key _ h
    exact mem_Q_of j hj

lemma Q2 : Q 2 = ↑QF2 := by
  ext ⟨b, w⟩
  simp only [mem_coe]
  constructor
  · rintro ⟨j, hj⟩
    simp only [Prod.mk.injEq] at hj
    rw [← hj.1, ← hj.2]
    have : fac j 2 = [X j, X (j + 1)] := by simp [fac, List.range_succ]
    rw [this]
    cases par j <;> cases X j <;> cases X (j + 1) <;> decide
  · intro h
    have key : ∀ p ∈ QF2, ∃ j ∈ range 16, (par j, fac j 2) = p := by decide
    obtain ⟨j, -, hj⟩ := key _ h
    exact mem_Q_of j hj

lemma Q3 : Q 3 = ↑QF3 := Q_step Q2 Q2
lemma Q4 : Q 4 = ↑QF4 := Q_step Q2 Q3
lemma Q5 : Q 5 = ↑QF5 := Q_step Q3 Q3
lemma Q6 : Q 6 = ↑QF6 := Q_step Q3 Q4
lemma Q7 : Q 7 = ↑QF7 := Q_step Q4 Q4
lemma Q8 : Q 8 = ↑QF8 := Q_step Q4 Q5

set_option maxRecDepth 100000 in
lemma recog8 : ∀ p ∈ QF8, ∀ q ∈ QF8, p.2 = q.2 → p.1 = q.1 := by decide

lemma QF2_card : QF2.card = 8 := by decide

lemma vals : (QF0.image Prod.snd).card = 1 ∧ (QF1.image Prod.snd).card = 2 ∧
    (QF2.image Prod.snd).card = 4 ∧ (QF3.image Prod.snd).card = 8 ∧
    (QF4.image Prod.snd).card = 16 ∧ (QF5.image Prod.snd).card = 24 ∧
    (QF6.image Prod.snd).card = 36 ∧ (QF7.image Prod.snd).card = 46 := by decide

/-! ### Injectivity of the factor maps, by explicit decoding -/

def dec0 (m : ℕ) (w : List Bool) : Bool × List Bool :=
  (xor (w.getD 0 false) (w.getD 1 false), (List.range m).map fun i => w.getD (2 * i) false)

def dec1 (m : ℕ) (w : List Bool) : Bool × List Bool :=
  (!(xor (w.getD 1 false) (w.getD 2 false)), (List.range m).map fun i =>
    if i = 0 then xor (w.getD 0 false) (!(xor (w.getD 1 false) (w.getD 2 false)))
    else w.getD (2 * i - 1) false)

lemma getD_eq_getElem' {u : List Bool} {i : ℕ} (h : i < u.length) : u.getD i false = u[i] := by
  simp [List.getD_eq_getElem?_getD, h]

lemma dec0_Psi {L : ℕ} (hL : 2 ≤ L) (e : Bool) {u : List Bool} (hu : u.length = (L + 1) / 2) :
    dec0 ((L + 1) / 2) (Psi 0 e u L) = (e, u) := by
  unfold dec0
  rw [getD_Psi (by omega), getD_Psi (by omega)]
  refine Prod.ext ?_ ?_
  · simp only [Nat.zero_add, Nat.zero_div, Nat.zero_mod, show 1 / 2 = 0 from rfl, Nat.one_mod]
    cases u.getD 0 false <;> cases e <;> decide
  · apply List.ext_getElem (by simp [hu])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [getD_Psi (by simp at h1; omega)]
    have h3 : (0 + 2 * i) / 2 = i := by omega
    have h4 : (0 + 2 * i) % 2 = 0 := by omega
    rw [h3, h4, getD_eq_getElem' h2]
    simp

lemma dec1_Psi {L : ℕ} (hL : 3 ≤ L) (e : Bool) {u : List Bool} (hu : u.length = (L + 2) / 2) :
    dec1 ((L + 2) / 2) (Psi 1 e u L) = (e, u) := by
  unfold dec1
  rw [getD_Psi (by omega), getD_Psi (by omega), getD_Psi (by omega)]
  have he : (!(xor (xor (u.getD ((1 + 1) / 2) false) ((1 + 1) % 2 == 1 && xor e ((1 + 1) / 2 % 2 == 1)))
      (xor (u.getD ((1 + 2) / 2) false) ((1 + 2) % 2 == 1 && xor e ((1 + 2) / 2 % 2 == 1))))) = e := by
    simp only [show (1 + 1) / 2 = 1 by rfl, show (1 + 2) / 2 = 1 by rfl, show (1 + 1) % 2 = 0 by rfl,
      show (1 + 2) % 2 = 1 by rfl]
    cases u.getD 1 false <;> cases e <;> decide
  rw [he]
  refine Prod.ext rfl ?_
  apply List.ext_getElem (by simp [hu])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  split_ifs with hi
  · subst hi
    simp only [show (1 + 0) / 2 = 0 by rfl, show (1 + 0) % 2 = 1 by rfl, Nat.zero_mod]
    rw [getD_eq_getElem' h2]
    cases u[0] <;> cases e <;> decide
  · rw [getD_Psi (by simp at h1; omega)]
    have h3 : (1 + (2 * i - 1)) / 2 = i := by omega
    have h4 : (1 + (2 * i - 1)) % 2 = 0 := by omega
    rw [h3, h4, getD_eq_getElem' h2]
    simp

lemma length_of_mem_Q {L : ℕ} {p : Bool × List Bool} (h : p ∈ Q L) : p.2.length = L := by
  obtain ⟨j, rfl⟩ := h
  exact length_fac j L

lemma Q_finite (L : ℕ) : (Q L).Finite := by
  apply Set.Finite.subset ((Set.finite_univ (α := Bool)).prod (List.finite_length_eq Bool L))
  intro p hp
  exact ⟨Set.mem_univ _, length_of_mem_Q hp⟩

lemma card_Q {L : ℕ} (hL : 2 ≤ L) : (Q L).ncard = 8 * L - 8 := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases Nat.lt_or_ge L 3 with h3 | h3
    · obtain rfl : L = 2 := by omega
      rw [Q2, Set.ncard_coe_finset, QF2_card]
    · rw [Q_rec]
      have hdisj : Disjoint
          ((fun eu : Bool × List Bool => (false, Psi 0 eu.1 eu.2 L)) '' Q ((L + 1) / 2))
          ((fun eu : Bool × List Bool => (true, Psi 1 eu.1 eu.2 L)) '' Q ((L + 2) / 2)) := by
        rw [Set.disjoint_left]
        rintro _ ⟨_, _, rfl⟩ ⟨_, _, h⟩
        simp at h
      rw [Set.ncard_union_eq hdisj ((Q_finite _).image _) ((Q_finite _).image _)]
      have hinj0 : Set.InjOn (fun eu : Bool × List Bool => (false, Psi 0 eu.1 eu.2 L))
          (Q ((L + 1) / 2)) := by
        intro x hx y hy hxy
        simp only [Prod.mk.injEq, true_and] at hxy
        have e1 := dec0_Psi (by omega) x.1 (length_of_mem_Q hx)
        have e2 := dec0_Psi (by omega) y.1 (length_of_mem_Q hy)
        rw [hxy] at e1
        have e3 := e1.symm.trans e2
        exact Prod.ext (congrArg Prod.fst e3) (congrArg Prod.snd e3)
      have hinj1 : Set.InjOn (fun eu : Bool × List Bool => (true, Psi 1 eu.1 eu.2 L))
          (Q ((L + 2) / 2)) := by
        intro x hx y hy hxy
        simp only [Prod.mk.injEq, true_and] at hxy
        have e1 := dec1_Psi h3 x.1 (length_of_mem_Q hx)
        have e2 := dec1_Psi h3 y.1 (length_of_mem_Q hy)
        rw [hxy] at e1
        have e3 := e1.symm.trans e2
        exact Prod.ext (congrArg Prod.fst e3) (congrArg Prod.snd e3)
      rw [hinj0.ncard_image, hinj1.ncard_image,
        ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      omega

/-! ### From factor sets to the counting function `a` -/

def G (n : ℕ) (w : List Bool) : Fin n → ℕ := fun j => if w.getD j false then 1 else 0

lemma grs_eq_ite (k : ℕ) : grs k = if X k then 1 else 0 := by
  unfold X
  have := grs_lt k
  interval_cases (grs k) <;> simp

lemma a_eq (n : ℕ) : a n = (Prod.snd '' Q n).ncard := by
  have hrange : (Set.range fun i : ℕ => fun j : Fin n => grs (i + j)) = G n '' (Prod.snd '' Q n) := by
    ext f
    simp only [Set.mem_range, Set.mem_image, Q]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨fac i n, ⟨(par i, fac i n), ⟨i, rfl⟩, rfl⟩, ?_⟩
      funext j
      simp only [G, getD_fac j.isLt, grs_eq_ite]
    · rintro ⟨w, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      funext j
      simp only [G, getD_fac j.isLt, grs_eq_ite]
  unfold a
  rw [hrange]
  apply Set.InjOn.ncard_image
  rintro w ⟨p, hp, rfl⟩ w' ⟨p', hp', rfl⟩ h
  have l1 := length_of_mem_Q hp
  have l2 := length_of_mem_Q hp'
  apply List.ext_getElem (by rw [l1, l2])
  intro j h1 h2
  have := congrFun h ⟨j, by rw [← l1]; exact h1⟩
  simp only [G, getD_eq_getElem' h1, getD_eq_getElem' h2] at this
  revert this
  cases p.2[j] <;> cases p'.2[j] <;> simp

lemma snd_injOn {n : ℕ} (hn : 8 ≤ n) : Set.InjOn Prod.snd (Q n) := by
  rintro p ⟨j, rfl⟩ q ⟨j', rfl⟩ h
  simp only at h
  have htake : ∀ i, (fac i n).take 8 = fac i 8 := by
    intro i
    unfold fac
    rw [← List.map_take, List.take_range, min_eq_left hn]
  have m1 : (par j, fac j 8) ∈ QF8 := by rw [← mem_coe, ← Q8]; exact ⟨j, rfl⟩
  have m2 : (par j', fac j' 8) ∈ QF8 := by rw [← mem_coe, ← Q8]; exact ⟨j', rfl⟩
  have hp := recog8 _ m1 _ m2 (by simp only; rw [← htake, ← htake, h])
  simp only at hp
  show (par j, fac j n) = (par j', fac j' n)
  rw [hp, h]

lemma a_small {n : ℕ} {F : Finset (Bool × List Bool)} (h : Q n = ↑F) :
    a n = (F.image Prod.snd).card := by
  rw [a_eq, h, ← coe_image, Set.ncard_coe_finset]

theorem a005943 :
    (a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 8 ∧ a 4 = 16 ∧ a 5 = 24 ∧ a 6 = 36 ∧ a 7 = 46) ∧
      ∀ n : ℕ, 8 ≤ n → a n = 8 * n - 8 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := vals
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [a_small Q0, v0]
  · rw [a_small Q1, v1]
  · rw [a_small Q2, v2]
  · rw [a_small Q3, v3]
  · rw [a_small Q4, v4]
  · rw [a_small Q5, v5]
  · rw [a_small Q6, v6]
  · rw [a_small Q7, v7]
  · intro n hn
    rw [a_eq, (snd_injOn hn).ncard_image, card_Q (by omega)]

end OMA.A005943proof

theorem OMA.solution : type_of% @OMA.S_oeis_a005943.main := OMA.A005943proof.a005943
