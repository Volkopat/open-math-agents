import OMAStatements.S_mo_352184

namespace Fairt

open OMA.S_mo_352184

/-- Score of position `i` (0-indexed, 16 vertices) when position `k` has threshold `f k`:
`i` beats the later `k` with `f i < k` and the earlier `k` with `i ≤ f k`. -/
def sc (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  ((Finset.range 16).filter fun k => (i < k ∧ f i < k) ∨ (k < i ∧ i ≤ f k)).card

/-- Set the threshold of position `i` to `ji`. -/
def upd (f : ℕ → ℕ) (i ji : ℕ) : ℕ → ℕ := fun k => if k = i then ji else f k

/-- Exhaustive search: can thresholds for positions `i, i+1, ...` (`fuel` of them) be chosen, after
the thresholds `f` of the earlier positions, so that every score is 3 or 9? -/
def go : ℕ → ℕ → (ℕ → ℕ) → Bool
  | 0, _, _ => true
  | fuel + 1, i, f =>
    (List.range 16).any fun ji =>
      decide (i ≤ ji) && ((sc (upd f i ji) i == 3 || sc (upd f i ji) i == 9) &&
        go fuel (i + 1) (upd f i ji))

theorem go_false : go 16 0 (fun _ => 0) = false := by decide +kernel

theorem sc_congr (f g : ℕ → ℕ) (i : ℕ) (h : ∀ k, k ≤ i → f k = g k) : sc f i = sc g i := by
  unfold sc
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [h i le_rfl]
  by_cases hk : k < i
  · rw [h k hk.le]
  · simp [hk]

theorem go_sound (j : ℕ → ℕ) (hj : ∀ i, i < 16 → i ≤ j i ∧ j i < 16)
    (hs : ∀ i, i < 16 → sc j i = 3 ∨ sc j i = 9) :
    ∀ fuel i (f : ℕ → ℕ), fuel + i = 16 → (∀ k, k < i → f k = j k) → go fuel i f = true := by
  intro fuel
  induction fuel with
  | zero => intro i f _ _; rfl
  | succ fuel ih =>
    intro i f hi hf
    have hi16 : i < 16 := by omega
    have hagree : ∀ k, k ≤ i → upd f i (j i) k = j k := by
      intro k hk
      unfold upd
      by_cases hki : k = i
      · simp [hki]
      · simp only [hki, if_false]
        exact hf k (by omega)
    have hsc : sc (upd f i (j i)) i = sc j i := sc_congr _ _ _ hagree
    have hrec : go fuel (i + 1) (upd f i (j i)) = true :=
      ih (i + 1) _ (by omega) (fun k hk => hagree k (by omega))
    show ((List.range 16).any fun ji =>
      decide (i ≤ ji) && ((sc (upd f i ji) i == 3 || sc (upd f i ji) i == 9) &&
        go fuel (i + 1) (upd f i ji))) = true
    rw [List.any_eq_true]
    refine ⟨j i, List.mem_range.2 (hj i hi16).2, ?_⟩
    rw [hsc, hrec]
    rcases hs i hi16 with h | h <;> simp [h, (hj i hi16).1]

/-- In a fair-indexed tournament with thresholds `jf`, who beats whom is determined by `jf`. -/
theorem adj_iff {T : Digraph (Fin 16)} (hT : IsTournament T) (jf : Fin 16 → Fin 16)
    (hjf : ∀ i, i ≤ jf i ∧ ∀ k, i < k → (T.Adj i k ↔ jf i < k)) (i k : Fin 16) :
    T.Adj i k ↔ (i < k ∧ jf i < k) ∨ (k < i ∧ i ≤ jf k) := by
  rcases lt_trichotomy i k with h | h | h
  · rw [(hjf i).2 k h]
    constructor
    · intro h'
      exact Or.inl ⟨h, h'⟩
    · rintro (⟨_, h'⟩ | ⟨h', _⟩)
      · exact h'
      · exact absurd h (lt_asymm h')
  · subst h
    constructor
    · intro h'
      exact absurd h' (hT.1 i)
    · rintro (⟨h', _⟩ | ⟨h', _⟩) <;> exact absurd h' (lt_irrefl _)
  · rw [hT.2 i k (ne_of_gt h), (hjf k).2 i h, not_lt]
    constructor
    · intro h'
      exact Or.inr ⟨h, h'⟩
    · rintro (⟨h', _⟩ | ⟨_, h'⟩)
      · exact absurd h (lt_asymm h')
      · exact h'

/-- The thresholds as a function on `ℕ`. -/
def toNat (jf : Fin 16 → Fin 16) : ℕ → ℕ := fun k => if h : k < 16 then (jf ⟨k, h⟩ : ℕ) else 0

theorem toNat_coe (jf : Fin 16 → Fin 16) (k : Fin 16) : toNat jf (k : ℕ) = (jf k : ℕ) := by
  unfold toNat
  rw [dif_pos k.isLt]

theorem score_eq {T : Digraph (Fin 16)} (hT : IsTournament T) (jf : Fin 16 → Fin 16)
    (hjf : ∀ i, i ≤ jf i ∧ ∀ k, i < k → (T.Adj i k ↔ jf i < k)) (i : Fin 16) :
    score T i = sc (toNat jf) i := by
  have hset : {k : Fin 16 | T.Adj i k} =
      ↑(Finset.univ.filter fun k : Fin 16 =>
        ((i : ℕ) < (k : ℕ) ∧ toNat jf i < (k : ℕ)) ∨ ((k : ℕ) < (i : ℕ) ∧ (i : ℕ) ≤ toNat jf k)) := by
    ext k
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, toNat_coe]
    rw [adj_iff hT jf hjf i k]
    simp only [Fin.lt_def, Fin.le_def]
  unfold score sc
  rw [hset, Set.ncard_coe_finset, Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range
    (fun k => if ((i : ℕ) < k ∧ toNat jf i < k) ∨ (k < (i : ℕ) ∧ (i : ℕ) ≤ toNat jf k) then 1 else 0) 16

/-- `l` (one of 13, 14, 15) beats `h` (one of 0..11) in the example. -/
def exc (l h : ℕ) : Bool :=
  (l == 13 && h == 0) || (l == 14 && (h == 1 || h == 2)) || (l == 15 && (h == 3 || h == 4 || h == 5))

/-- A tournament on 16 vertices with twelve vertices of score 9 (0..11) and four of score 3. -/
def adj0 (a b : ℕ) : Bool :=
  if a < 12 then
    if b < 12 then
      (decide (1 ≤ (b + 12 - a) % 12) && decide ((b + 12 - a) % 12 ≤ 5)) ||
        (decide (a < 6) && decide (b = a + 6))
    else !(exc b a)
  else
    if b < 12 then exc a b else decide (a < b)

def T0 : Digraph (Fin 16) := ⟨fun a b => adj0 a b = true⟩

theorem adj0_tournament : (∀ v : Fin 16, ¬ adj0 v v = true) ∧
    (∀ u v : Fin 16, u ≠ v → (adj0 u v = true ↔ ¬ adj0 v u = true)) := by
  decide +kernel

theorem T0_tournament : IsTournament T0 := adj0_tournament

theorem T0_card : ∀ i : Fin 16,
    (Finset.univ.filter fun k : Fin 16 => adj0 i k = true).card = 3 ∨
      (Finset.univ.filter fun k : Fin 16 => adj0 i k = true).card = 9 := by
  decide +kernel

theorem T0_score (i : Fin 16) : score T0 i = 3 ∨ score T0 i = 9 := by
  have h : score T0 i = (Finset.univ.filter fun k : Fin 16 => adj0 i k = true).card := by
    unfold score
    have hset : {k : Fin 16 | T0.Adj i k} =
        ↑(Finset.univ.filter fun k : Fin 16 => adj0 i k = true) := by
      ext k
      simp [T0]
    rw [hset, Set.ncard_coe_finset]
  rw [h]
  exact T0_card i

end Fairt

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_352184.main) := by
  intro hmain
  obtain ⟨T, hT, hF, s, hs⟩ := hmain 16 Fairt.T0 Fairt.T0_tournament
  have hF' : ∀ i : Fin 16, ∃ j : Fin 16, i ≤ j ∧ ∀ k : Fin 16, i < k → (T.Adj i k ↔ j < k) := hF
  choose jf hjf using hF'
  have hj : ∀ i, i < 16 → i ≤ Fairt.toNat jf i ∧ Fairt.toNat jf i < 16 := by
    intro i hi
    have h1 : Fairt.toNat jf i = (jf ⟨i, hi⟩ : ℕ) := Fairt.toNat_coe jf ⟨i, hi⟩
    have h2 : i ≤ (jf ⟨i, hi⟩ : ℕ) := (hjf ⟨i, hi⟩).1
    have h3 : (jf ⟨i, hi⟩ : ℕ) < 16 := (jf ⟨i, hi⟩).isLt
    omega
  have hsc : ∀ i, i < 16 → Fairt.sc (Fairt.toNat jf) i = 3 ∨ Fairt.sc (Fairt.toNat jf) i = 9 := by
    intro i hi
    have h1 : OMA.S_mo_352184.score T ⟨i, hi⟩ = Fairt.sc (Fairt.toNat jf) i :=
      Fairt.score_eq hT jf hjf ⟨i, hi⟩
    have h2 := hs (s.symm ⟨i, hi⟩)
    rw [Equiv.apply_symm_apply] at h2
    have h3 := Fairt.T0_score (s.symm ⟨i, hi⟩)
    rw [← h1, ← h2]
    exact h3
  have htrue := Fairt.go_sound (Fairt.toNat jf) hj hsc 16 0 (fun _ => 0) rfl (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [Fairt.go_false] at htrue
  exact Bool.noConfusion htrue
