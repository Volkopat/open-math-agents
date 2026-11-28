import OMAStatements.S_oeis_a253503

namespace OMA.S_oeis_a253503

open PowerSeries Finset






/-! ## Peeling the top row -/

/-- The element in column c of the row r, as an integer, or 0 outside. -/
def v (r : Fin 3 → Fin 2) (c : ℕ) : ℤ := if h : c < 3 then ((r ⟨c, h⟩).val : ℤ) else 0

/-- f2 of the block with rows r, s and left column j. -/
def f2loc (r s : Fin 3 → Fin 2) (j : ℕ) : ℤ := max (v r j) (v s (j + 1)) - min (v r (j + 1)) (v s j)

/-- f3 of the block with rows r, s, t and left column j. -/
def f3loc (r s t : Fin 3 → Fin 2) (j : ℕ) : ℤ :=
  max (max (v r j) (v s (j + 1))) (v t (j + 2)) - min (min (v r (j + 2)) (v s (j + 1))) (v t j)

theorem get_cons_zero (R : ℕ) (r : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) (c : ℕ) :
    get (R + 1) (Fin.cons r y : Fin (R + 1) → Fin 3 → Fin 2) 0 c = v r c := by
  unfold get v
  by_cases hc : c < 3
  · rw [dif_pos ⟨Nat.succ_pos R, hc⟩, dif_pos hc]
    rfl
  · rw [dif_neg (fun h => hc h.2), dif_neg hc]

theorem get_cons_succ (R : ℕ) (r : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) (i c : ℕ) :
    get (R + 1) (Fin.cons r y : Fin (R + 1) → Fin 3 → Fin 2) (i + 1) c = get R y i c := by
  unfold get
  by_cases h : i < R ∧ c < 3
  · rw [dif_pos ⟨by omega, h.2⟩, dif_pos h]
    have e : (⟨i + 1, by omega⟩ : Fin (R + 1)) = Fin.succ ⟨i, h.1⟩ := rfl
    rw [e, Fin.cons_succ]
  · rw [dif_neg (fun h' => h ⟨by omega, h'.2⟩), dif_neg h]

theorem f2_succ (R : ℕ) (r : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) (i j : ℕ) :
    f2 (R + 1) (Fin.cons r y : Fin (R + 1) → Fin 3 → Fin 2) (i + 1) j = f2 R y i j := by
  unfold f2
  simp only [get_cons_succ]

theorem f3_succ (R : ℕ) (r : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) (i j : ℕ) :
    f3 (R + 1) (Fin.cons r y : Fin (R + 1) → Fin 3 → Fin 2) (i + 1) j = f3 R y i j := by
  unfold f3
  simp only [get_cons_succ]

theorem f2_zero (R : ℕ) (r s : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) (j : ℕ) :
    f2 (R + 1 + 1) (Fin.cons r (Fin.cons s y : Fin (R + 1) → Fin 3 → Fin 2) :
      Fin (R + 1 + 1) → Fin 3 → Fin 2) 0 j = f2loc r s j := by
  unfold f2 f2loc
  rw [get_cons_zero, get_cons_zero, get_cons_succ, get_cons_succ, get_cons_zero, get_cons_zero]

theorem f3_zero (R : ℕ) (r s t : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) (j : ℕ) :
    f3 (R + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t y : Fin (R + 1) → Fin 3 → Fin 2) :
      Fin (R + 1 + 1) → Fin 3 → Fin 2) : Fin (R + 1 + 1 + 1) → Fin 3 → Fin 2) 0 j = f3loc r s t j := by
  unfold f3 f3loc
  simp only [get_cons_zero, get_cons_succ]

/-- The new conditions when a row is put on top. -/
theorem good_cons (R : ℕ) (r : Fin 3 → Fin 2) (y : Fin R → Fin 3 → Fin 2) :
    good (R + 1) (Fin.cons r y : Fin (R + 1) → Fin 3 → Fin 2) ↔
      ((∀ j : ℕ, 2 ≤ R + 1 → j + 2 ≤ 3 →
          (j + 3 ≤ 3 → f2 (R + 1) (Fin.cons r y) 0 j ≤ f2 (R + 1) (Fin.cons r y) 0 (j + 1)) ∧
          (3 ≤ R + 1 → f2 (R + 1) (Fin.cons r y) 0 j ≤ f2 (R + 1) (Fin.cons r y) 1 j)) ∧
        (∀ j : ℕ, 3 ≤ R + 1 → j + 3 ≤ 3 →
          (j + 4 ≤ 3 → f3 (R + 1) (Fin.cons r y) 0 j ≤ f3 (R + 1) (Fin.cons r y) 0 (j + 1)) ∧
          (4 ≤ R + 1 → f3 (R + 1) (Fin.cons r y) 0 j ≤ f3 (R + 1) (Fin.cons r y) 1 j))) ∧
      good R y := by
  unfold good
  constructor
  · rintro ⟨H2, H3⟩
    refine ⟨⟨fun j h1 h2 => H2 0 j (by omega) h2, fun j h1 h2 => H3 0 j (by omega) h2⟩, ?_, ?_⟩
    · intro i j hi hj
      have := H2 (i + 1) j (by omega) hj
      rw [f2_succ, f2_succ, f2_succ] at this
      exact ⟨fun h => this.1 h, fun h => this.2 (by omega)⟩
    · intro i j hi hj
      have := H3 (i + 1) j (by omega) hj
      rw [f3_succ, f3_succ, f3_succ] at this
      exact ⟨fun h => this.1 h, fun h => this.2 (by omega)⟩
  · rintro ⟨⟨C2, C3⟩, G2, G3⟩
    refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_⟩
    · rcases i with _ | i
      · exact C2 j (by omega) hj
      · rw [f2_succ, f2_succ, f2_succ]
        exact ⟨fun h => (G2 i j (by omega) hj).1 h, fun h => (G2 i j (by omega) hj).2 (by omega)⟩
    · rcases i with _ | i
      · exact C3 j (by omega) hj
      · rw [f3_succ, f3_succ, f3_succ]
        exact ⟨fun h => (G3 i j (by omega) hj).1 h, fun h => (G3 i j (by omega) hj).2 (by omega)⟩

/-- The conditions of the top window: rows r, s (and t below them). -/
def h2 (r s : Fin 3 → Fin 2) : Prop := f2loc r s 0 ≤ f2loc r s 1

def v2 (r s t : Fin 3 → Fin 2) : Prop := f2loc r s 0 ≤ f2loc s t 0 ∧ f2loc r s 1 ≤ f2loc s t 1

def v3 (r s t u : Fin 3 → Fin 2) : Prop := f3loc r s t 0 ≤ f3loc s t u 0

instance (r s : Fin 3 → Fin 2) : Decidable (h2 r s) := by unfold h2; infer_instance

instance (r s t : Fin 3 → Fin 2) : Decidable (v2 r s t) := by unfold v2; infer_instance

instance (r s t u : Fin 3 → Fin 2) : Decidable (v3 r s t u) := by unfold v3; infer_instance

theorem good_four (m : ℕ) (r s t u : Fin 3 → Fin 2) (y : Fin m → Fin 3 → Fin 2) :
    good (m + 1 + 1 + 1 + 1)
      (Fin.cons r (Fin.cons s (Fin.cons t (Fin.cons u y : Fin (m + 1) → Fin 3 → Fin 2) :
        Fin (m + 1 + 1) → Fin 3 → Fin 2) : Fin (m + 1 + 1 + 1) → Fin 3 → Fin 2) :
        Fin (m + 1 + 1 + 1 + 1) → Fin 3 → Fin 2) ↔
      (h2 r s ∧ v2 r s t ∧ v3 r s t u) ∧
        good (m + 1 + 1 + 1) (Fin.cons s (Fin.cons t (Fin.cons u y : Fin (m + 1) → Fin 3 → Fin 2) :
          Fin (m + 1 + 1) → Fin 3 → Fin 2) : Fin (m + 1 + 1 + 1) → Fin 3 → Fin 2) := by
  rw [good_cons]
  have e20 : ∀ j, f2 (m + 1 + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t (Fin.cons u y)))) 0 j =
      f2loc r s j := fun j => f2_zero _ r s _ j
  have e21 : ∀ j, f2 (m + 1 + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t (Fin.cons u y)))) 1 j =
      f2loc s t j := fun j => by rw [f2_succ, f2_zero]
  have e30 : ∀ j, f3 (m + 1 + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t (Fin.cons u y)))) 0 j =
      f3loc r s t j := fun j => f3_zero _ r s t _ j
  have e31 : ∀ j, f3 (m + 1 + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t (Fin.cons u y)))) 1 j =
      f3loc s t u j := fun j => by rw [f3_succ, f3_zero]
  simp only [e20, e21, e30, e31]
  unfold h2 v2 v3
  constructor
  · rintro ⟨⟨C2, C3⟩, G⟩
    exact ⟨⟨(C2 0 (by omega) (by omega)).1 (by omega),
      ⟨(C2 0 (by omega) (by omega)).2 (by omega), (C2 1 (by omega) (by omega)).2 (by omega)⟩,
      (C3 0 (by omega) (by omega)).2 (by omega)⟩, G⟩
  · rintro ⟨⟨H, ⟨V0, V1⟩, V3⟩, G⟩
    refine ⟨⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩, G⟩
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact ⟨fun _ => H, fun _ => V0⟩
      · exact ⟨fun h => absurd h (by omega), fun _ => V1⟩
    · have hj : j = 0 := by omega
      subst hj
      exact ⟨fun h => absurd h (by omega), fun _ => V3⟩

theorem good_three (r s t : Fin 3 → Fin 2) (y : Fin 0 → Fin 3 → Fin 2) :
    good (0 + 1 + 1 + 1)
      (Fin.cons r (Fin.cons s (Fin.cons t y : Fin (0 + 1) → Fin 3 → Fin 2) :
        Fin (0 + 1 + 1) → Fin 3 → Fin 2) : Fin (0 + 1 + 1 + 1) → Fin 3 → Fin 2) ↔
      h2 r s ∧ v2 r s t ∧ h2 s t := by
  rw [good_cons, good_cons]
  have e20 : ∀ j, f2 (0 + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t y))) 0 j = f2loc r s j :=
    fun j => f2_zero _ r s _ j
  have e21 : ∀ j, f2 (0 + 1 + 1 + 1) (Fin.cons r (Fin.cons s (Fin.cons t y))) 1 j = f2loc s t j :=
    fun j => by rw [f2_succ, f2_zero]
  have e10 : ∀ j, f2 (0 + 1 + 1) (Fin.cons s (Fin.cons t y)) 0 j = f2loc s t j :=
    fun j => f2_zero _ s t _ j
  simp only [e20, e21, e10]
  unfold h2 v2
  have hg : good (0 + 1) (Fin.cons t y : Fin (0 + 1) → Fin 3 → Fin 2) := by
    refine ⟨fun i j hi _ => by omega, fun i j hi _ => by omega⟩
  constructor
  · rintro ⟨⟨C2, _⟩, ⟨D2, _⟩, _⟩
    exact ⟨(C2 0 (by omega) (by omega)).1 (by omega),
      ⟨(C2 0 (by omega) (by omega)).2 (by omega), (C2 1 (by omega) (by omega)).2 (by omega)⟩,
      (D2 0 (by omega) (by omega)).1 (by omega)⟩
  · rintro ⟨H, ⟨V0, V1⟩, H'⟩
    refine ⟨⟨fun j h1 h2 => ?_, fun j h1 h2 => ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩⟩,
      ⟨fun j h1 h2 => ?_, fun j h1 h2 => by omega⟩, hg⟩
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact ⟨fun _ => H, fun _ => V0⟩
      · exact ⟨fun h => absurd h (by omega), fun _ => V1⟩
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact ⟨fun _ => H', fun h => absurd h (by omega)⟩
      · exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

noncomputable instance (R : ℕ) (x : Fin R → Fin 3 → Fin 2) : Decidable (good R x) :=
  Classical.dec _

/-- The ways to put m rows below the rows r, s, t. -/
noncomputable def Mc (r s t : Fin 3 → Fin 2) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3 → Fin 2, if good (m + 1 + 1 + 1)
    (Fin.cons r (Fin.cons s (Fin.cons t y : Fin (m + 1) → Fin 3 → Fin 2) :
      Fin (m + 1 + 1) → Fin 3 → Fin 2) : Fin (m + 1 + 1 + 1) → Fin 3 → Fin 2) then 1 else 0

theorem sum_cons {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 1) → α) → ℕ) :
    ∑ y : Fin (m + 1) → α, f y = ∑ r : α, ∑ y : Fin m → α, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem Mc_zero (r s t : Fin 3 → Fin 2) : Mc r s t 0 = if h2 r s ∧ v2 r s t ∧ h2 s t then 1 else 0 := by
  unfold Mc
  rw [Fintype.sum_unique]
  by_cases h : h2 r s ∧ v2 r s t ∧ h2 s t
  · rw [if_pos ((good_three r s t _).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((good_three r s t _).1 h')), if_neg h]

theorem Mc_succ (r s t : Fin 3 → Fin 2) (m : ℕ) : Mc r s t (m + 1) =
    ∑ u : Fin 3 → Fin 2, if h2 r s ∧ v2 r s t ∧ v3 r s t u then Mc s t u m else 0 := by
  unfold Mc
  rw [sum_cons]
  refine sum_congr rfl (fun u _ => ?_)
  by_cases hw : h2 r s ∧ v2 r s t ∧ v3 r s t u
  · rw [if_pos hw]
    refine sum_congr rfl (fun y _ => ?_)
    by_cases hg : good (m + 1 + 1 + 1) (Fin.cons s (Fin.cons t (Fin.cons u y : Fin (m + 1) → Fin 3 → Fin 2) :
        Fin (m + 1 + 1) → Fin 3 → Fin 2) : Fin (m + 1 + 1 + 1) → Fin 3 → Fin 2)
    · rw [if_pos ((good_four m r s t u y).2 ⟨hw, hg⟩), if_pos hg]
    · rw [if_neg (fun h' => hg ((good_four m r s t u y).1 h').2), if_neg hg]
  · rw [if_neg hw]
    refine sum_eq_zero (fun y _ => ?_)
    rw [if_neg (fun h' => hw ((good_four m r s t u y).1 h').1)]

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 3 → Fin 2, ∑ s : Fin 3 → Fin 2, ∑ t : Fin 3 → Fin 2,
    Mc r s t n := by
  have ha : a (n + 1) = ∑ x : Fin (n + 1 + 1 + 1) → Fin 3 → Fin 2,
      if good (n + 1 + 1 + 1) x then 1 else 0 := by
    rw [← card_filter]
    unfold a
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
  rw [ha, sum_cons]
  refine sum_congr rfl (fun r _ => ?_)
  rw [sum_cons]
  refine sum_congr rfl (fun s _ => ?_)
  rw [sum_cons]
  rfl

/-! ## Codes -/

def dig (c : ℕ) : Fin 3 → Fin 2 := fun j => ⟨c / 2 ^ j.val % 2, Nat.mod_lt _ (by norm_num)⟩

def code (r : Fin 3 → Fin 2) : ℕ := (r 0).val + 2 * (r 1).val + 4 * (r 2).val

theorem dig_code (r : Fin 3 → Fin 2) : dig (code r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  fin_cases j <;> simp [dig, code] <;> omega

theorem code_lt (r : Fin 3 → Fin 2) : code r < 8 := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  unfold code
  omega

theorem code_dig (c : ℕ) (h : c < 8) : code (dig c) = c := by
  simp [code, dig]
  omega

theorem sum_dig (g : (Fin 3 → Fin 2) → ℕ) : ∑ r, g r = ∑ c ∈ range 8, g (dig c) := by
  rw [← (finFunctionFinEquiv (m := 2) (n := 3)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun c => g (dig c)) _

/-- The bit of the row code rc in column c, as an integer, and 0 outside. -/
def vC (rc c : ℕ) : ℤ := if c < 3 then ((rc / 2 ^ c % 2 : ℕ) : ℤ) else 0

def f2C (rc sc j : ℕ) : ℤ := max (vC rc j) (vC sc (j + 1)) - min (vC rc (j + 1)) (vC sc j)

def f3C (rc sc tc j : ℕ) : ℤ :=
  max (max (vC rc j) (vC sc (j + 1))) (vC tc (j + 2)) - min (min (vC rc (j + 2)) (vC sc (j + 1))) (vC tc j)

theorem v_dig (rc c : ℕ) : v (dig rc) c = vC rc c := by
  unfold v vC dig
  by_cases h : c < 3
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

theorem f2_dig (rc sc j : ℕ) : f2loc (dig rc) (dig sc) j = f2C rc sc j := by
  unfold f2loc f2C
  simp only [v_dig]

theorem f3_dig (rc sc tc j : ℕ) : f3loc (dig rc) (dig sc) (dig tc) j = f3C rc sc tc j := by
  unfold f3loc f3C
  simp only [v_dig]

/-- The state code of the rows rc, sc, tc. -/
def enc (rc sc tc : ℕ) : ℕ := rc * 64 + sc * 8 + tc

def guardB (s uc : ℕ) : Bool :=
  decide (f2C (s / 64) (s / 8 % 8) 0 ≤ f2C (s / 64) (s / 8 % 8) 1 ∧
    (f2C (s / 64) (s / 8 % 8) 0 ≤ f2C (s / 8 % 8) (s % 8) 0 ∧
      f2C (s / 64) (s / 8 % 8) 1 ≤ f2C (s / 8 % 8) (s % 8) 1) ∧
    f3C (s / 64) (s / 8 % 8) (s % 8) 0 ≤ f3C (s / 8 % 8) (s % 8) uc 0)

def endB (s : ℕ) : Bool :=
  decide (f2C (s / 64) (s / 8 % 8) 0 ≤ f2C (s / 64) (s / 8 % 8) 1 ∧
    (f2C (s / 64) (s / 8 % 8) 0 ≤ f2C (s / 8 % 8) (s % 8) 0 ∧
      f2C (s / 64) (s / 8 % 8) 1 ≤ f2C (s / 8 % 8) (s % 8) 1) ∧
    f2C (s / 8 % 8) (s % 8) 0 ≤ f2C (s / 8 % 8) (s % 8) 1)

def succS (s uc : ℕ) : ℕ := s % 64 * 8 + uc

def Ncode : ℕ → ℕ → ℕ
  | s, 0 => if endB s = true then 1 else 0
  | s, m + 1 => ∑ uc ∈ range 8, if guardB s uc = true then Ncode (succS s uc) m else 0

theorem Ncode_succ (s m : ℕ) : Ncode s (m + 1) =
    ∑ uc ∈ range 8, if guardB s uc = true then Ncode (succS s uc) m else 0 := rfl

theorem enc_parts (r s t : Fin 3 → Fin 2) : enc (code r) (code s) (code t) / 64 = code r ∧
    enc (code r) (code s) (code t) / 8 % 8 = code s ∧ enc (code r) (code s) (code t) % 8 = code t := by
  have := code_lt r
  have := code_lt s
  have := code_lt t
  unfold enc
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem q2 (a b : Fin 3 → Fin 2) (j : ℕ) : f2C (code a) (code b) j = f2loc a b j := by
  rw [← f2_dig, dig_code, dig_code]

theorem q3 (a b c : Fin 3 → Fin 2) (j : ℕ) : f3C (code a) (code b) (code c) j = f3loc a b c j := by
  rw [← f3_dig, dig_code, dig_code, dig_code]

theorem guard_eq (r s t u : Fin 3 → Fin 2) :
    guardB (enc (code r) (code s) (code t)) (code u) = decide (h2 r s ∧ v2 r s t ∧ v3 r s t u) := by
  obtain ⟨e1, e2, e3⟩ := enc_parts r s t
  unfold guardB
  rw [e1, e2, e3]
  simp only [q2, q3]
  exact decide_eq_decide.mpr Iff.rfl

theorem end_eq (r s t : Fin 3 → Fin 2) :
    endB (enc (code r) (code s) (code t)) = decide (h2 r s ∧ v2 r s t ∧ h2 s t) := by
  obtain ⟨e1, e2, e3⟩ := enc_parts r s t
  unfold endB
  rw [e1, e2, e3]
  simp only [q2]
  exact decide_eq_decide.mpr Iff.rfl

theorem succ_eq (r s t u : Fin 3 → Fin 2) :
    succS (enc (code r) (code s) (code t)) (code u) = enc (code s) (code t) (code u) := by
  have := code_lt r
  have := code_lt s
  have := code_lt t
  unfold succS enc
  omega

theorem M_code (m : ℕ) : ∀ r s t : Fin 3 → Fin 2, Mc r s t m = Ncode (enc (code r) (code s) (code t)) m := by
  induction m with
  | zero =>
    intro r s t
    rw [Mc_zero, Ncode, end_eq]
    by_cases h : h2 r s ∧ v2 r s t ∧ h2 s t
    · rw [if_pos h, if_pos (decide_eq_true h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  | succ m ih =>
    intro r s t
    rw [Mc_succ, sum_dig, Ncode_succ]
    refine sum_congr rfl (fun uc huc => ?_)
    rw [mem_range] at huc
    have hu := code_dig uc huc
    rw [← hu, guard_eq, succ_eq, ← ih, hu]
    by_cases h : h2 r s ∧ v2 r s t ∧ v3 r s t (dig uc)
    · rw [if_pos h, if_pos (decide_eq_true h)]
    · rw [if_neg h, if_neg (by simpa using h)]

/-- The table of Ncode 0: entry s in the bits 1 * s.. of one number. -/
def tab0 (s : ℕ) : ℕ := 9794023061981041775088514025728282196692899085996280296780687033025355271296209465078329551577938174699082736367296788474343964286322337001250537208869107 >>> (1 * s) % 2 ^ 1

/-- The table of Ncode 1: entry s in the bits 4 * s.. of one number. -/
def tab1 (s : ℕ) : ℕ := 12134904120661467319056498071878404007031484591108011079307963183863554760617066885604348052973116516257595386902408228545991780764877110841778137055465884531795661386184622834398407301495905294741669139563578410641836098204621735828708154496136616256860640149935428260900436304006476512159323824510552784011111438334522728066185163476948547925519271127037250959428567260474662797762520457613889293580569541341384015842581750705510145172892652434956643311449757143957877189475721169795005881414917086700561242769456058486631058703904447405950789891041795529422056387880721988939940167205356273696488376784068592926790 >>> (4 * s) % 2 ^ 4

/-- The table of Ncode 2: entry s in the bits 5 * s.. of one number. -/
def tab2 (s : ℕ) : ℕ := 297920625255036660628720235532986373699905358499117262312359122997771078773870217880207262979488865822334294455839954870695481886545647535291107455050480254003700026789964503585300014249312307394364617496946660869482707231370411660435680629898408762000284052268258485219206928436565945056934004936863704941942935192027883714034064975357118483492860506418738588545284316885592756449759829582852609904021220021127390415575021954011656419917146179604649005453565477975880000732387414129318502196288427236368182455653382601453531952058294775785978035613971653846975884597907888801645670753220756225537292862725865310486469769894638397168434751510589680436081645530548352085572458396485685980064186980987188870096958601576614318104451436409265183566293184824058976245754364048 >>> (5 * s) % 2 ^ 5

/-- The table of Ncode 3: entry s in the bits 6 * s.. of one number. -/
def tab3 (s : ℕ) : ℕ := 4720349411444314328828528721690158634720907196055252905343214614699125210911737828166519800466110624288976085513053415221891173800287107541344361985359950935553527625757348555082562448722321399694289184418242894481133179881097627709282548935957818419478821092839279181064848712989860531256052598365651627224027901141484320426966916693546004885329287069680688371772812126744517164129529655903822569266664398976068218431568456320708046386009382021067742246825981731563174801475271289928480143031850329556982881167642230574188596021342081620082117703696861782295171016822051223339780406524053531209153981126431536342608719341730155521265010017155503135924694501092515403409489999651948028914839603879780264053566084602624721538469760783488189352959132861943348429555987029158259359604744537493983356118823155729964838871596958829518973955781077909681547809802778881929427480207822471577034947380186274553169769048809499275559196 >>> (6 * s) % 2 ^ 6

/-- The table of Ncode 4: entry s in the bits 7 * s.. of one number. -/
def tab4 (s : ℕ) : ℕ := 60854825459699900056233107572629835740883989162686322177788831572719732700392447823916696451052837997674987777921294415748651577914666875455450583230514576911220638852932440526016475092053128478126192988054038109672289423021508052081290410008006961181284901149051837329701568060357798914783355204164071332416673576589630285621581231037755374979405187401953276108639231048380809160539919702157497217925990713175597476235552953437184044969735867199280826927167603836570690885091359919940642672281192119570698220762494517050712777302608732687589678139747035148358804983190597714293265672084749440236942163594816165815848754503973158115674619784263386059696716433041983347349201042855808140582329058272506903129884693511884360321729803689245468164685473924066897247033441172765493159408482594321248989912346408514052709241663106620161961041988556705734614801234701112872872949355486591549371689768376554060218145175126959897398861649974666227709376216315672654664408928192322649697523411411901548851725661177114405164179134177750787382165100537133272041782640520650772361743360328234 >>> (7 * s) % 2 ^ 7

/-- The table of Ncode 5: entry s in the bits 8 * s.. of one number. -/
def tab5 (s : ℕ) : ℕ := 677221039864387532365356681599868506407807489160952746538150563582167873422909251465264281207749215102324559208395000301170842891146561770850350449060268949785025708999833179998213157872675464694316975908299416582712128075580516792233217531203105459528323489547315428390995255662117712454981781042039065265195040500156965917319076533714725473471611914316155122687078540773799656447204240318456246017577918276709526237155759334659364851140941549682843853650797885549201186572722995721837995003680341388383300913315178299102407404207230474936913986834532022530275576365183377813925069997570267168575449001863834861981104342593272051301912614267509968167231258523620051241775407980620600807271650172110057277066271933990985956025239299152429313371600002157037794681892083950238327638336938544563601709908978434102344963119071231844610662882545770000470419696945648843039431968540170263346289135207504481601103779218426077863873231609403298756298174252514079745593362914576587163954152486024681528512266880497262950468822160514233468574473635660366397325299164556944770946487272122878938511611543341747116635322926618441942280588540544038766854201350485092062305332911003535841827763088077728853083181185408352612035092047338616358175802 >>> (8 * s) % 2 ^ 8

def crec : Bool := (List.range 512).all fun s => (tab5 s : ℤ) == (3 : ℤ) * (tab4 s : ℤ) + (-3 : ℤ) * (tab3 s : ℤ) + (1 : ℤ) * (tab2 s : ℤ)

def c0 : Bool := (List.range 512).all fun s => tab0 s == if endB s = true then 1 else 0

def c1 : Bool := (List.range 512).all fun s =>
  tab1 s ==
    (if guardB s 0 = true then tab0 (succS s 0) else 0) +
    (if guardB s 1 = true then tab0 (succS s 1) else 0) +
    (if guardB s 2 = true then tab0 (succS s 2) else 0) +
    (if guardB s 3 = true then tab0 (succS s 3) else 0) +
    (if guardB s 4 = true then tab0 (succS s 4) else 0) +
    (if guardB s 5 = true then tab0 (succS s 5) else 0) +
    (if guardB s 6 = true then tab0 (succS s 6) else 0) +
    (if guardB s 7 = true then tab0 (succS s 7) else 0)

def c2 : Bool := (List.range 512).all fun s =>
  tab2 s ==
    (if guardB s 0 = true then tab1 (succS s 0) else 0) +
    (if guardB s 1 = true then tab1 (succS s 1) else 0) +
    (if guardB s 2 = true then tab1 (succS s 2) else 0) +
    (if guardB s 3 = true then tab1 (succS s 3) else 0) +
    (if guardB s 4 = true then tab1 (succS s 4) else 0) +
    (if guardB s 5 = true then tab1 (succS s 5) else 0) +
    (if guardB s 6 = true then tab1 (succS s 6) else 0) +
    (if guardB s 7 = true then tab1 (succS s 7) else 0)

def c3 : Bool := (List.range 512).all fun s =>
  tab3 s ==
    (if guardB s 0 = true then tab2 (succS s 0) else 0) +
    (if guardB s 1 = true then tab2 (succS s 1) else 0) +
    (if guardB s 2 = true then tab2 (succS s 2) else 0) +
    (if guardB s 3 = true then tab2 (succS s 3) else 0) +
    (if guardB s 4 = true then tab2 (succS s 4) else 0) +
    (if guardB s 5 = true then tab2 (succS s 5) else 0) +
    (if guardB s 6 = true then tab2 (succS s 6) else 0) +
    (if guardB s 7 = true then tab2 (succS s 7) else 0)

def c4 : Bool := (List.range 512).all fun s =>
  tab4 s ==
    (if guardB s 0 = true then tab3 (succS s 0) else 0) +
    (if guardB s 1 = true then tab3 (succS s 1) else 0) +
    (if guardB s 2 = true then tab3 (succS s 2) else 0) +
    (if guardB s 3 = true then tab3 (succS s 3) else 0) +
    (if guardB s 4 = true then tab3 (succS s 4) else 0) +
    (if guardB s 5 = true then tab3 (succS s 5) else 0) +
    (if guardB s 6 = true then tab3 (succS s 6) else 0) +
    (if guardB s 7 = true then tab3 (succS s 7) else 0)

def c5 : Bool := (List.range 512).all fun s =>
  tab5 s ==
    (if guardB s 0 = true then tab4 (succS s 0) else 0) +
    (if guardB s 1 = true then tab4 (succS s 1) else 0) +
    (if guardB s 2 = true then tab4 (succS s 2) else 0) +
    (if guardB s 3 = true then tab4 (succS s 3) else 0) +
    (if guardB s 4 = true then tab4 (succS s 4) else 0) +
    (if guardB s 5 = true then tab4 (succS s 5) else 0) +
    (if guardB s 6 = true then tab4 (succS s 6) else 0) +
    (if guardB s 7 = true then tab4 (succS s 7) else 0)

def cval0 : Bool := (∑ x ∈ range 8, ∑ y ∈ range 8, ∑ z ∈ range 8,
    tab0 (enc (code (dig x)) (code (dig y)) (code (dig z)))) == 132

def cval1 : Bool := (∑ x ∈ range 8, ∑ y ∈ range 8, ∑ z ∈ range 8,
    tab1 (enc (code (dig x)) (code (dig y)) (code (dig z)))) == 260

def cval2 : Bool := (∑ x ∈ range 8, ∑ y ∈ range 8, ∑ z ∈ range 8,
    tab2 (enc (code (dig x)) (code (dig y)) (code (dig z)))) == 428

def cval3 : Bool := (∑ x ∈ range 8, ∑ y ∈ range 8, ∑ z ∈ range 8,
    tab3 (enc (code (dig x)) (code (dig y)) (code (dig z)))) == 636

def cval4 : Bool := (∑ x ∈ range 8, ∑ y ∈ range 8, ∑ z ∈ range 8,
    tab4 (enc (code (dig x)) (code (dig y)) (code (dig z)))) == 884

set_option maxRecDepth 100000 in
theorem tabs : (crec && (c0 && (c1 && (c2 && (c3 && (c4 && (c5 && (cval0 && (cval1 && (cval2 && (cval3 && (cval4)))))))))))) = true := by
  decide +kernel

theorem tabs_split : crec = true ∧ c0 = true ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧ c5 = true ∧ cval0 = true ∧ cval1 = true ∧ cval2 = true ∧ cval3 = true ∧ cval4 = true := by
  have h := tabs
  simp only [Bool.and_eq_true] at h
  exact h

theorem succ_lt (s uc : ℕ) (hs : s < 512) (huc : uc < 8) : succS s uc < 512 := by
  unfold succS
  omega

theorem tab_eq0 (s : ℕ) (hs : s < 512) : Ncode s 0 = tab0 s := by
  have h := tabs_split.2.1
  unfold c0 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [beq_iff_eq] at hc
  rw [hc]
  rfl

theorem tab_eq1 (s : ℕ) (hs : s < 512) : Ncode s 1 = tab1 s := by
  have h := tabs_split.2.2.1
  unfold c1 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ uc ∈ range 8, (if guardB s uc = true then Ncode (succS s uc) 0 else 0) =
      (if guardB s uc = true then tab0 (succS s uc) else 0) := by
    intro uc huc
    split_ifs with hg
    · exact tab_eq0 _ (succ_lt s uc hs (mem_range.mp huc))
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq2 (s : ℕ) (hs : s < 512) : Ncode s 2 = tab2 s := by
  have h := tabs_split.2.2.2.1
  unfold c2 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ uc ∈ range 8, (if guardB s uc = true then Ncode (succS s uc) 1 else 0) =
      (if guardB s uc = true then tab1 (succS s uc) else 0) := by
    intro uc huc
    split_ifs with hg
    · exact tab_eq1 _ (succ_lt s uc hs (mem_range.mp huc))
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq3 (s : ℕ) (hs : s < 512) : Ncode s 3 = tab3 s := by
  have h := tabs_split.2.2.2.2.1
  unfold c3 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ uc ∈ range 8, (if guardB s uc = true then Ncode (succS s uc) 2 else 0) =
      (if guardB s uc = true then tab2 (succS s uc) else 0) := by
    intro uc huc
    split_ifs with hg
    · exact tab_eq2 _ (succ_lt s uc hs (mem_range.mp huc))
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq4 (s : ℕ) (hs : s < 512) : Ncode s 4 = tab4 s := by
  have h := tabs_split.2.2.2.2.2.1
  unfold c4 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ uc ∈ range 8, (if guardB s uc = true then Ncode (succS s uc) 3 else 0) =
      (if guardB s uc = true then tab3 (succS s uc) else 0) := by
    intro uc huc
    split_ifs with hg
    · exact tab_eq3 _ (succ_lt s uc hs (mem_range.mp huc))
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq5 (s : ℕ) (hs : s < 512) : Ncode s 5 = tab5 s := by
  have h := tabs_split.2.2.2.2.2.2.1
  unfold c5 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ uc ∈ range 8, (if guardB s uc = true then Ncode (succS s uc) 4 else 0) =
      (if guardB s uc = true then tab4 (succS s uc) else 0) := by
    intro uc huc
    split_ifs with hg
    · exact tab_eq4 _ (succ_lt s uc hs (mem_range.mp huc))
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The recurrence of order 3 of the counts, on every state, from m = 2. -/
theorem Ncode_rec (m : ℕ) : ∀ s, s < 512 → (Ncode s (m + 5) : ℤ) = (3 : ℤ) * (Ncode s (m + 4) : ℤ) + (-3 : ℤ) * (Ncode s (m + 3) : ℤ) + (1 : ℤ) * (Ncode s (m + 2) : ℤ) := by
  induction m with
  | zero =>
    intro s hs
    simp only [zero_add]
    rw [tab_eq5 s hs, tab_eq4 s hs, tab_eq3 s hs, tab_eq2 s hs]
    have h := tabs_split.1
    unfold crec at h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact h s hs
  | succ m ih =>
    intro s hs
    show (Ncode s (m + 1 + 5) : ℤ) = (3 : ℤ) * (Ncode s (m + 1 + 4) : ℤ) + (-3 : ℤ) * (Ncode s (m + 1 + 3) : ℤ) + (1 : ℤ) * (Ncode s (m + 1 + 2) : ℤ)
    rw [Ncode_succ s (m + 5), Ncode_succ s (m + 4), Ncode_succ s (m + 3), Ncode_succ s (m + 2)]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun uc huc => ?_)
    split_ifs with hg
    · exact ih _ (succ_lt s uc hs (mem_range.mp huc))
    · simp

theorem enc_lt (x y z : ℕ) : enc (code (dig x)) (code (dig y)) (code (dig z)) < 512 := by
  have := code_lt (dig x)
  have := code_lt (dig y)
  have := code_lt (dig z)
  unfold enc
  omega

theorem a_code (n : ℕ) : a (n + 1) = ∑ x ∈ range 8, ∑ y ∈ range 8, ∑ z ∈ range 8,
    Ncode (enc (code (dig x)) (code (dig y)) (code (dig z))) n := by
  rw [a_succ]
  simp only [M_code, sum_dig]

theorem av1 : a 1 = 132 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_code]
  simp only [tab_eq0 _ (enc_lt _ _ _)]
  have h := tabs_split.2.2.2.2.2.2.2.1
  unfold cval0 at h
  exact beq_iff_eq.mp h

theorem av2 : a 2 = 260 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_code]
  simp only [tab_eq1 _ (enc_lt _ _ _)]
  have h := tabs_split.2.2.2.2.2.2.2.2.1
  unfold cval1 at h
  exact beq_iff_eq.mp h

theorem av3 : a 3 = 428 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_code]
  simp only [tab_eq2 _ (enc_lt _ _ _)]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.1
  unfold cval2 at h
  exact beq_iff_eq.mp h

theorem av4 : a 4 = 636 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_code]
  simp only [tab_eq3 _ (enc_lt _ _ _)]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.1
  unfold cval3 at h
  exact beq_iff_eq.mp h

theorem av5 : a 5 = 884 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_code]
  simp only [tab_eq4 _ (enc_lt _ _ _)]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2
  unfold cval4 at h
  exact beq_iff_eq.mp h

/-- The recurrence of order 3: a(n) for n >= 6. -/
theorem a_rec (m : ℕ) : (a (m + 6) : ℤ) = (3 : ℤ) * (a (m + 5) : ℤ) + (-3 : ℤ) * (a (m + 4) : ℤ) + (1 : ℤ) * (a (m + 3) : ℤ) := by
  rw [a_code (m + 5), a_code (m + 4), a_code (m + 3), a_code (m + 2)]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => sum_congr rfl (fun z _ => ?_)))
  exact Ncode_rec m _ (enc_lt x y z)

/-- Barker's g.f., as A(x) (1 - x)^3 = 4x (33 - 34x + 11x^2) in Z[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 = 4 * X * (33 - 34 * X + 11 * X ^ 2) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (4 * X * (33 - 34 * X + 11 * X ^ 2) : ℤ⟦X⟧) = X ^ 1 * C 132 - X ^ 2 * C 136 + X ^ 3 * C 44 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [av1, av2, av3, av4, av5]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
    have h := a_rec q
    simp only [show q + 6 - 1 = q + 5 by omega, 
      show 1 ≤ q + 6 by omega, 
      show ¬ q + 5 = 0 by omega, 
      show q + 6 - 2 = q + 4 by omega, 
      show 2 ≤ q + 6 by omega, 
      show ¬ q + 4 = 0 by omega, 
      show q + 6 - 3 = q + 3 by omega, 
      show 3 ≤ q + 6 by omega, 
      show ¬ q + 3 = 0 by omega, 
      show ¬ q + 6 = 0 by omega, 
      show ¬ q + 6 = 1 by omega, 
      show ¬ q + 6 = 2 by omega, 
      show ¬ q + 6 = 3 by omega,
      if_true, if_false]
    rw [h]
    ring

/-- Barker's recurrence, for n > 3. -/
theorem recurrence (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n <;> simp [av1, av2, av3, av4, av5]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega]
    linear_combination a_rec m

/-- Controls: the entry's data a(1..14). -/
theorem controls : a 1 = 132 ∧ a 2 = 260 ∧ a 3 = 428 ∧ a 4 = 636 ∧ a 5 = 884 ∧ a 6 = 1172 ∧ a 7 = 1500 ∧ a 8 = 1868 ∧ a 9 = 2276 ∧ a 10 = 2724 ∧ a 11 = 3212 ∧ a 12 = 3740 ∧ a 13 = 4308 ∧ a 14 = 4916 := by
  have av6 : a 6 = 1172 := by
    have h : (a 6 : ℤ) = (3 : ℤ) * (a 5 : ℤ) + (-3 : ℤ) * (a 4 : ℤ) + (1 : ℤ) * (a 3 : ℤ) := a_rec 0
    rw [av5, av4, av3] at h
    omega
  have av7 : a 7 = 1500 := by
    have h : (a 7 : ℤ) = (3 : ℤ) * (a 6 : ℤ) + (-3 : ℤ) * (a 5 : ℤ) + (1 : ℤ) * (a 4 : ℤ) := a_rec 1
    rw [av6, av5, av4] at h
    omega
  have av8 : a 8 = 1868 := by
    have h : (a 8 : ℤ) = (3 : ℤ) * (a 7 : ℤ) + (-3 : ℤ) * (a 6 : ℤ) + (1 : ℤ) * (a 5 : ℤ) := a_rec 2
    rw [av7, av6, av5] at h
    omega
  have av9 : a 9 = 2276 := by
    have h : (a 9 : ℤ) = (3 : ℤ) * (a 8 : ℤ) + (-3 : ℤ) * (a 7 : ℤ) + (1 : ℤ) * (a 6 : ℤ) := a_rec 3
    rw [av8, av7, av6] at h
    omega
  have av10 : a 10 = 2724 := by
    have h : (a 10 : ℤ) = (3 : ℤ) * (a 9 : ℤ) + (-3 : ℤ) * (a 8 : ℤ) + (1 : ℤ) * (a 7 : ℤ) := a_rec 4
    rw [av9, av8, av7] at h
    omega
  have av11 : a 11 = 3212 := by
    have h : (a 11 : ℤ) = (3 : ℤ) * (a 10 : ℤ) + (-3 : ℤ) * (a 9 : ℤ) + (1 : ℤ) * (a 8 : ℤ) := a_rec 5
    rw [av10, av9, av8] at h
    omega
  have av12 : a 12 = 3740 := by
    have h : (a 12 : ℤ) = (3 : ℤ) * (a 11 : ℤ) + (-3 : ℤ) * (a 10 : ℤ) + (1 : ℤ) * (a 9 : ℤ) := a_rec 6
    rw [av11, av10, av9] at h
    omega
  have av13 : a 13 = 4308 := by
    have h : (a 13 : ℤ) = (3 : ℤ) * (a 12 : ℤ) + (-3 : ℤ) * (a 11 : ℤ) + (1 : ℤ) * (a 10 : ℤ) := a_rec 7
    rw [av12, av11, av10] at h
    omega
  have av14 : a 14 = 4916 := by
    have h : (a 14 : ℤ) = (3 : ℤ) * (a 13 : ℤ) + (-3 : ℤ) * (a 12 : ℤ) + (1 : ℤ) * (a 11 : ℤ) := a_rec 8
    rw [av13, av12, av11] at h
    omega
  exact ⟨av1, av2, av3, av4, av5, av6, av7, av8, av9, av10, av11, av12, av13, av14⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 = 4 * X * (33 - 34 * X + 11 * X ^ 2) ∧
    ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a253503

theorem OMA.solution : type_of% @OMA.S_oeis_a253503.main :=
  OMA.S_oeis_a253503.conjecture
