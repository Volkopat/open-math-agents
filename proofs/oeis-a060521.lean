import OMAStatements.S_oeis_a060521
import Mathlib

/-!
Transfer matrix. A grid is read column by column; each column is a triple of booleans and a word
of columns is valid when no column is constant and no row has three equal consecutive cells. The
state of a word of length at least 2 is its last two columns. Appending a column gives
`S (L + 1) f = S L (T f)`, where `S L f` sums `f` of the state over valid words of length `L + 2`.
With `E k = T^k 1`, `a (L + k + 2) = S L (E k)`, and the identity
`E 4 + E 0 = 2 E 3 + 5 E 2` holds on every reachable state (checked by `decide +kernel`).
The case `n = 1` uses the values `a 1 = 6`, `a 3 = 102`, `a 4 = 378`, `a 5 = 1260`.
-/

namespace R060521
open OMA.S_oeis_a060521

abbrev B3 := Bool × Bool × Bool
abbrev St := B3 × B3

def nt (a b c : Bool) : Bool := !((a == b) && (b == c))

theorem nt_iff (a b c : Bool) : nt a b c = true ↔ ¬ (a = b ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> decide

def CO (c : B3) : Bool := nt c.1 c.2.1 c.2.2

def TO (x y z : B3) : Bool := nt x.1 y.1 z.1 && nt x.2.1 y.2.1 z.2.1 && nt x.2.2 y.2.2 z.2.2

def VW {m : ℕ} (w : Fin m → B3) : Prop :=
  (∀ j, CO (w j) = true) ∧
    ∀ i j k : Fin m, j.val = i.val + 1 → k.val = j.val + 1 → TO (w i) (w j) (w k) = true

instance decVW (m : ℕ) : DecidablePred (@VW m) := fun w => by unfold VW; infer_instance

def gridEquiv (n : ℕ) : (Fin 3 → Fin n → Bool) ≃ (Fin n → B3) where
  toFun g j := (g 0 j, g 1 j, g 2 j)
  invFun w i j := ![(w j).1, (w j).2.1, (w j).2.2] i
  left_inv g := by
    funext i j
    fin_cases i <;> rfl
  right_inv w := by
    funext j
    rfl

theorem gridEquiv_apply (n : ℕ) (g : Fin 3 → Fin n → Bool) (j : Fin n) :
    gridEquiv n g j = (g 0 j, g 1 j, g 2 j) := rfl

theorem valid_iff (n : ℕ) (g : Fin 3 → Fin n → Bool) : ValidGrid n g ↔ VW (gridEquiv n g) := by
  have hT : ∀ a b c : Fin n, TO (gridEquiv n g a) (gridEquiv n g b) (gridEquiv n g c) = true ↔
      ∀ i : Fin 3, ¬ (g i a = g i b ∧ g i b = g i c) := by
    intro a b c
    simp only [gridEquiv_apply, TO, Bool.and_eq_true, nt_iff]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · intro h
      exact ⟨⟨h 0, h 1⟩, h 2⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun a b c hb hc => (hT a b c).2 (fun i => ?_)⟩
    · simp only [gridEquiv_apply, CO, nt_iff]
      exact h1 j
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb'⟩ := b
      obtain ⟨c, hc'⟩ := c
      obtain rfl : b = a + 1 := hb
      obtain rfl : c = a + 1 + 1 := hc
      exact h2 i a hc'
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun i j hj => ?_⟩
    · have := h1 j
      simp only [gridEquiv_apply, CO, nt_iff] at this
      exact this
    · exact (hT _ _ _).1 (h2 ⟨j, by omega⟩ ⟨j + 1, by omega⟩ ⟨j + 2, by omega⟩ rfl rfl) i

theorem a_eq (n : ℕ) : a060521 n = ∑ w : Fin n → B3, if VW w then 1 else 0 := by
  rw [show a060521 n = Nat.card {w : Fin n → B3 // VW w} from
    Nat.card_congr (Equiv.subtypeEquiv (gridEquiv n) (valid_iff n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

def info {L : ℕ} (w : Fin (L + 2) → B3) : St := (w ⟨L, by omega⟩, w ⟨L + 1, by omega⟩)

def ok (s : St) (x : B3) : Bool := CO x && TO s.1 s.2 x

def step (s : St) (x : B3) : St := (s.2, x)

def good (s : St) : Bool := CO s.1 && CO s.2

def sum8 (h : B3 → ℕ) : ℕ :=
  h (false, false, false) + h (false, false, true) + h (false, true, false) +
    h (false, true, true) + h (true, false, false) + h (true, false, true) +
    h (true, true, false) + h (true, true, true)

theorem sum8_eq (h : B3 → ℕ) : sum8 h = ∑ x : B3, h x := by
  simp only [sum8, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

def T (f : St → ℕ) (s : St) : ℕ := sum8 (fun x => if ok s x = true then f (step s x) else 0)

def E : ℕ → St → ℕ
  | 0 => fun _ => 1
  | k + 1 => T (E k)

def S (L : ℕ) (f : St → ℕ) : ℕ := ∑ w : Fin (L + 2) → B3, if VW w then f (info w) else 0

theorem snoc_val {L : ℕ} (w : Fin (L + 2) → B3) (x : B3) (i : Fin (L + 3)) (j : Fin (L + 2))
    (h : i.val = j.val) : (Fin.snoc w x : Fin (L + 3) → B3) i = w j := by
  obtain rfl : i = Fin.castSucc j := Fin.ext h
  exact Fin.snoc_castSucc ..

theorem snoc_val' {L : ℕ} (w : Fin (L + 2) → B3) (x : B3) (i : Fin (L + 3))
    (h : i.val = L + 2) : (Fin.snoc w x : Fin (L + 3) → B3) i = x := by
  obtain rfl : i = Fin.last (L + 2) := Fin.ext h
  exact Fin.snoc_last ..

theorem info_snoc {L : ℕ} (w : Fin (L + 2) → B3) (x : B3) :
    info (Fin.snoc w x : Fin (L + 3) → B3) = step (info w) x := by
  show ((Fin.snoc w x : Fin (L + 3) → B3) ⟨L + 1, by omega⟩,
      (Fin.snoc w x : Fin (L + 3) → B3) ⟨L + 1 + 1, by omega⟩) = (w ⟨L + 1, by omega⟩, x)
  rw [snoc_val w x ⟨L + 1, by omega⟩ ⟨L + 1, by omega⟩ rfl,
    snoc_val' w x ⟨L + 1 + 1, by omega⟩ rfl]

theorem valid_snoc {L : ℕ} (w : Fin (L + 2) → B3) (x : B3) :
    VW (Fin.snoc w x : Fin (L + 3) → B3) ↔ VW w ∧ ok (info w) x = true := by
  have key1 : (∀ j : Fin (L + 3), CO ((Fin.snoc w x : Fin (L + 3) → B3) j) = true) ↔
      (∀ j : Fin (L + 2), CO (w j) = true) ∧ CO x = true := by
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · have := h (Fin.castSucc j)
        rwa [Fin.snoc_castSucc] at this
      · have := h (Fin.last _)
        rwa [Fin.snoc_last] at this
    · rintro ⟨h1, h2⟩ j
      have hj' := j.isLt
      by_cases hj : j.val = L + 2
      · rw [snoc_val' w x j hj]
        exact h2
      · rw [snoc_val w x j ⟨j.val, by omega⟩ rfl]
        exact h1 _
  have key2 : (∀ i j k : Fin (L + 3), j.val = i.val + 1 → k.val = j.val + 1 →
      TO ((Fin.snoc w x : Fin (L + 3) → B3) i) ((Fin.snoc w x : Fin (L + 3) → B3) j)
        ((Fin.snoc w x : Fin (L + 3) → B3) k) = true) ↔
      (∀ i j k : Fin (L + 2), j.val = i.val + 1 → k.val = j.val + 1 →
        TO (w i) (w j) (w k) = true) ∧
      TO (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩) x = true := by
    constructor
    · intro h
      refine ⟨fun i j k hij hjk => ?_, ?_⟩
      · have := h (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc k) (by simpa using hij)
          (by simpa using hjk)
        simpa only [Fin.snoc_castSucc] using this
      · have := h ⟨L, by omega⟩ ⟨L + 1, by omega⟩ ⟨L + 1 + 1, by omega⟩ rfl rfl
        rwa [snoc_val w x ⟨L, by omega⟩ ⟨L, by omega⟩ rfl,
          snoc_val w x ⟨L + 1, by omega⟩ ⟨L + 1, by omega⟩ rfl,
          snoc_val' w x ⟨L + 1 + 1, by omega⟩ rfl] at this
    · rintro ⟨h1, h2⟩ i j k hij hjk
      have hk := k.isLt
      by_cases hkL : k.val = L + 2
      · rw [snoc_val' w x k hkL, snoc_val w x i ⟨L, by omega⟩ (by show i.val = L; omega),
          snoc_val w x j ⟨L + 1, by omega⟩ (by show j.val = L + 1; omega)]
        exact h2
      · rw [snoc_val w x i ⟨i.val, by omega⟩ rfl, snoc_val w x j ⟨j.val, by omega⟩ rfl,
          snoc_val w x k ⟨k.val, by omega⟩ rfl]
        exact h1 _ _ _ hij hjk
  have hC : ok (info w) x = true ↔
      CO x = true ∧ TO (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩) x = true := by
    simp only [ok, info, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a1, a2⟩ := key1.1 h1
    obtain ⟨b1, b2⟩ := key2.1 h2
    exact ⟨⟨a1, b1⟩, hC.2 ⟨a2, b2⟩⟩
  · rintro ⟨⟨a1, b1⟩, hc⟩
    obtain ⟨a2, b2⟩ := hC.1 hc
    exact ⟨key1.2 ⟨a1, a2⟩, key2.2 ⟨b1, b2⟩⟩

theorem pull (L : ℕ) (f : St → ℕ) : S (L + 1) f = S L (T f) := by
  have he : S (L + 1) f = ∑ p : B3 × (Fin (L + 2) → B3),
      if VW (Fin.snoc p.2 p.1 : Fin (L + 3) → B3) then
        f (info (Fin.snoc p.2 p.1 : Fin (L + 3) → B3)) else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => B3) _).symm
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  show _ = ∑ w : Fin (L + 2) → B3, if VW w then T f (info w) else 0
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [valid_snoc, info_snoc, T, sum8_eq]
  by_cases hw : VW w
  · simp only [hw, true_and, ↓reduceIte]
  · simp only [hw, false_and, ↓reduceIte, Finset.sum_const_zero]

theorem iter (k : ℕ) : ∀ L, S (L + k) (fun _ => 1) = S L (E k) := by
  induction k with
  | zero => intro L; rfl
  | succ k ih =>
    intro L
    rw [show L + (k + 1) = L + 1 + k by omega, ih (L + 1)]
    exact pull L (E k)

theorem a_S (L k : ℕ) : a060521 (L + k + 2) = S L (E k) :=
  (a_eq _).trans (iter k L)

theorem good_info {L : ℕ} {w : Fin (L + 2) → B3} (hw : VW w) : good (info w) = true := by
  simp only [good, info, Bool.and_eq_true]
  exact ⟨hw.1 _, hw.1 _⟩

theorem ident : ∀ s : St, good s = true → E 4 s + E 0 s = 2 * E 3 s + 5 * E 2 s := by
  rintro ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩
  revert a0 a1 a2 b0 b1 b2
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 4) + S L (E 0) = 2 * S L (E 3) + 5 * S L (E 2) := by
  simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : VW w
  · simp only [hw, ↓reduceIte]
    exact ident _ (good_info hw)
  · simp only [hw, ↓reduceIte, mul_zero, add_zero]

theorem vw1 (w : Fin 1 → B3) : VW w ↔ CO (w 0) = true := by
  constructor
  · exact fun h => h.1 0
  · intro h
    refine ⟨fun j => ?_, fun i j k hij hjk => ?_⟩
    · rwa [Subsingleton.elim j 0]
    · have := k.isLt
      exact absurd this (by omega)

theorem a1 : a060521 1 = 6 := by
  rw [a_eq]
  refine Eq.trans ?_ ((Equiv.sum_comp (Equiv.funUnique (Fin 1) B3)
    (fun c => if CO c = true then 1 else 0)).trans ?_)
  · refine Fintype.sum_congr _ _ (fun w => ?_)
    show (if VW w then 1 else 0) = if CO (w 0) = true then 1 else 0
    by_cases hw : VW w
    · rw [if_pos hw, if_pos ((vw1 w).1 hw)]
    · rw [if_neg hw, if_neg (fun h => hw ((vw1 w).2 h))]
  · rw [← sum8_eq]
    rfl

theorem vw2 (w : Fin (0 + 2) → B3) : VW w ↔ good (info w) = true := by
  have h3 : ∀ i j k : Fin (0 + 2), j.val = i.val + 1 → k.val = j.val + 1 → False := by
    intro i j k hij hjk
    have := k.isLt
    omega
  simp only [good, info, Bool.and_eq_true]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨h _, h _⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun j => ?_, fun i j k hij hjk => (h3 i j k hij hjk).elim⟩
    obtain ⟨j, hj⟩ := j
    rcases j with _ | _ | j
    · exact h0
    · exact h1
    · exact absurd hj (by omega)

theorem S0 (f : St → ℕ) : S 0 f = ∑ s : St, if good s = true then f s else 0 := by
  refine Eq.trans ?_ (Equiv.sum_comp (piFinTwoEquiv fun _ => B3)
    (fun s : St => if good s = true then f s else 0))
  refine Fintype.sum_congr _ _ (fun w => ?_)
  show (if VW w then f (info w) else 0) = if good (info w) = true then f (info w) else 0
  by_cases hw : VW w
  · rw [if_pos hw, if_pos ((vw2 w).1 hw)]
  · rw [if_neg hw, if_neg (fun h => hw ((vw2 w).2 h))]

theorem sumSt (F : St → ℕ) : ∑ s : St, F s = sum8 (fun a => sum8 (fun b => F (a, b))) := by
  rw [Fintype.sum_prod_type]
  simp only [sum8_eq]

theorem final_rec : ∀ n : ℕ, 1 ≤ n →
    a060521 (n + 4) + a060521 n = 2 * a060521 (n + 3) + 5 * a060521 (n + 2) := by
  intro n hn
  obtain ⟨L, rfl⟩ | rfl : (∃ L, n = L + 2) ∨ n = 1 := by
    rcases n with _ | _ | L
    · omega
    · exact Or.inr rfl
    · exact Or.inl ⟨L, rfl⟩
  · rw [show a060521 (L + 2 + 4) = S L (E 4) from a_S L 4,
      show a060521 (L + 2 + 3) = S L (E 3) from a_S L 3,
      show a060521 (L + 2 + 2) = S L (E 2) from a_S L 2,
      show a060521 (L + 2) = S L (E 0) from a_S L 0]
    exact rec_S L
  · rw [show a060521 (1 + 4) = S 0 (E 3) from a_S 0 3,
      show a060521 (1 + 3) = S 0 (E 2) from a_S 0 2,
      show a060521 (1 + 2) = S 0 (E 1) from a_S 0 1, a1]
    simp only [S0, sumSt]
    decide +kernel

end R060521

theorem OMA.solution : type_of% @OMA.S_oeis_a060521.main := R060521.final_rec
