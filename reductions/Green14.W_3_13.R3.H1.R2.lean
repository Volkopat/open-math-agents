import OMAReductions.R_Green14_W_3_13_R3

/-!
# Extending an anchored coloring by one point

Restrict the 160-point problem to positions 0 through 158. A red point at 159
is obstructed by two earlier red points. A blue point there is obstructed by
twelve earlier blue points. These are separate searches on the same prefix.
The explicit prefix below survives all internal tests and has a unique
obstruction of each kind, with common differences 62 and 13.

The first 159-bit coloring in the parent reduction by MrSeizy comes from
NickLeko's reduction. The witness here changes the color at position 74.
-/
namespace OMA.R_Green14_W_3_13_R3_H1_R2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
/-- This admissible 159-point prefix has a unique obstruction for each final color. -/
theorem sharp_prefix :
  let c := (0x2040021800c08012100140802440400b04002084 : ℕ).testBit
  (17 ≤ 61 ∧ 61 + 8 ≤ 71 ∧ 71 ≤ 61 + 13 ∧ 61 + 71 ≤ 159 ∧
    71 + 6 ≤ 78 ∧ 78 ≤ 71 + 13 ∧ 78 < 159 ∧
    (71 ≤ 62 → 71 + 7 ≤ 78) ∧ (71 ≤ 41 → 71 + 8 ≤ 78)) ∧
  (c 61 = true ∧ c 71 = true ∧ c 78 = true ∧
    (∀ x : Fin 159, 61 < x.val → x.val < 71 → c x.val = false) ∧
    (∀ x : Fin 159, 71 < x.val → x.val < 78 → c x.val = false)) ∧
  (∀ a : Fin 159, ∀ d : Fin 80, 0 < d.val → a.val + 2*d.val < 159 →
    ¬(c a.val = true ∧ c (a.val+d.val) = true ∧ c (a.val+2*d.val) = true)) ∧
  (∀ a : Fin 159, ∀ d : Fin 14, 0 < d.val → a.val + 12*d.val < 159 →
    ∃ i : Fin 13, c (a.val+i.val*d.val) = true) ∧
  (∀ o : Fin 159, ∀ h : Fin 3, 0 < h.val → o.val + 68*h.val < 159 →
    ∃ a : Fin 65, ∀ i : Fin 5, c (o.val+(a.val+i.val)*h.val) = false) ∧
  (∀ d : Fin 80, (0 < d.val ∧ c (159-2*d.val) = true ∧ c (159-d.val) = true) ↔ d.val = 62) ∧
  (∀ d : Fin 14, (0 < d.val ∧ ∀ i : Fin 12, c (159-12*d.val+i.val*d.val) = false) ↔ d.val = 13) := by
  dsimp only
  repeat' apply And.intro
  all_goals decide +kernel

/-- The earlier points of a red triple ending at position 159. -/
def H1 : Prop := ∀ (c : ℕ → Bool) (p q v : ℕ),
  (17 ≤ p ∧ p + 8 ≤ q ∧ q ≤ p + 13 ∧ p + q ≤ 159 ∧
    q + 6 ≤ v ∧ v ≤ q + 13 ∧ v < 159 ∧
    (q ≤ 62 → q + 7 ≤ v) ∧ (q ≤ 41 → q + 8 ≤ v)) →
  (c p = true ∧ c q = true ∧ c v = true ∧
    (∀ x : Fin 159, p < x.val → x.val < q → c x.val = false) ∧
    (∀ x : Fin 159, q < x.val → x.val < v → c x.val = false)) →
  (∀ a : Fin 159, ∀ d : Fin 80, 0 < d.val → a.val + 2*d.val < 159 →
    ¬(c a.val = true ∧ c (a.val+d.val) = true ∧ c (a.val+2*d.val) = true)) →
  (∀ a : Fin 159, ∀ d : Fin 14, 0 < d.val → a.val + 12*d.val < 159 →
    ∃ i : Fin 13, c (a.val+i.val*d.val) = true) →
  (∀ o : Fin 159, ∀ h : Fin 3, 0 < h.val → o.val + 68*h.val < 159 →
    ∃ a : Fin 65, ∀ i : Fin 5, c (o.val+(a.val+i.val)*h.val) = false) →
  ∃ d : Fin 80, 0 < d.val ∧ c (159-2*d.val) = true ∧ c (159-d.val) = true

/-- The earlier points of a blue 13-term progression ending at position 159. -/
def H2 : Prop := ∀ (c : ℕ → Bool) (p q v : ℕ),
  (17 ≤ p ∧ p + 8 ≤ q ∧ q ≤ p + 13 ∧ p + q ≤ 159 ∧
    q + 6 ≤ v ∧ v ≤ q + 13 ∧ v < 159 ∧
    (q ≤ 62 → q + 7 ≤ v) ∧ (q ≤ 41 → q + 8 ≤ v)) →
  (c p = true ∧ c q = true ∧ c v = true ∧
    (∀ x : Fin 159, p < x.val → x.val < q → c x.val = false) ∧
    (∀ x : Fin 159, q < x.val → x.val < v → c x.val = false)) →
  (∀ a : Fin 159, ∀ d : Fin 80, 0 < d.val → a.val + 2*d.val < 159 →
    ¬(c a.val = true ∧ c (a.val+d.val) = true ∧ c (a.val+2*d.val) = true)) →
  (∀ a : Fin 159, ∀ d : Fin 14, 0 < d.val → a.val + 12*d.val < 159 →
    ∃ i : Fin 13, c (a.val+i.val*d.val) = true) →
  (∀ o : Fin 159, ∀ h : Fin 3, 0 < h.val → o.val + 68*h.val < 159 →
    ∃ a : Fin 65, ∀ i : Fin 5, c (o.val+(a.val+i.val)*h.val) = false) →
  ∃ d : Fin 14, 0 < d.val ∧ ∀ i : Fin 12, c (159-12*d.val+i.val*d.val) = false

theorem main : H1 → H2 → OMA.R_Green14_W_3_13_R3.H1 := by
  classical
  intro redEnd blueEnd R p q v widths firstGap secondGap five free meets
  obtain ⟨hp, hpq, hqp, hsum, hqv, hvq, _, h62, h41⟩ := widths
  obtain ⟨rp, rq, gap1⟩ := firstGap
  obtain ⟨_, rv, gap2⟩ := secondGap
  have bv : v < 159 := by omega
  let c (i : ℕ) := decide (R i)
  have colors : c p = true ∧ c q = true ∧ c v = true ∧
      (∀ x : Fin 159, p < x.val → x.val < q → c x.val = false) ∧
      (∀ x : Fin 159, q < x.val → x.val < v → c x.val = false) := by
    refine ⟨decide_eq_true rp, decide_eq_true rq, decide_eq_true rv, ?_, ?_⟩
    · intro x hx hy
      simpa [c] using gap1 x.val hx hy
    · intro x hx hy
      simpa [c] using gap2 x.val hx hy
  have noRed (a : Fin 159) (d : Fin 80) (hd : 0 < d.val) (hn : a.val+2*d.val < 159) :
      ¬(c a.val = true ∧ c (a.val+d.val) = true ∧ c (a.val+2*d.val) = true) := by
    rintro ⟨h₀,h₁,h₂⟩
    exact free a d hd (by omega) (of_decide_eq_true h₀) (of_decide_eq_true h₁)
      (of_decide_eq_true h₂)
  have noBlue (a : Fin 159) (d : Fin 14) (hd : 0 < d.val) (hn : a.val+12*d.val < 159) :
      ∃ i : Fin 13, c (a.val+i.val*d.val) = true := by
    obtain ⟨i,hi⟩ := meets a.val d.val hd (by omega)
    exact ⟨i,decide_eq_true hi⟩
  have runs (o : Fin 159) (h : Fin 3) (hh : 0 < h.val) (hn : o.val+68*h.val < 159) :
      ∃ a : Fin 65, ∀ i : Fin 5, c (o.val+(a.val+i.val)*h.val) = false := by
    obtain ⟨a,ha,hz⟩ := five o.val h.val hh (by omega)
    exact ⟨⟨a,by omega⟩,fun i => by simpa [c] using hz i⟩
  by_cases last : R 159
  · obtain ⟨d,hd,h₀,h₁⟩ := redEnd c p q v ⟨hp,hpq,hqp,hsum,hqv,hvq,bv,h62,h41⟩
        colors noRed noBlue runs
    have he : 159 - 2*d.val + 2*d.val = 159 := by omega
    have hm : 159 - 2*d.val + d.val = 159-d.val := by omega
    apply free (159-2*d.val) d.val hd (by omega) (of_decide_eq_true h₀)
    · rw [hm]
      exact of_decide_eq_true h₁
    · rwa [he]
  · obtain ⟨d,hd,blue⟩ := blueEnd c p q v ⟨hp,hpq,hqp,hsum,hqv,hvq,bv,h62,h41⟩
        colors noRed noBlue runs
    have he : 159-12*d.val+12*d.val = 159 := by omega
    obtain ⟨i,hi⟩ := meets (159-12*d.val) d.val hd (by omega)
    by_cases hi12 : i.val = 12
    · rw [hi12, he] at hi
      exact last hi
    · have clear := blue ⟨i.val,by omega⟩
      change decide (R (159-12*d.val+i.val*d.val)) = false at clear
      exact (of_decide_eq_false clear) hi

end OMA.R_Green14_W_3_13_R3_H1_R2
