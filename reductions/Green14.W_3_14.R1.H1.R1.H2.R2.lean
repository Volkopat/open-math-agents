import OMAReductions.R_Green14_W_3_14_R1_H1_R1

/-!
# Shorter windows for the middle anchor positions of `W(3,14)`

All six cases use subintervals of length at most 183. For first red positions 95, 97
and 98, the subinterval can be centered on the red anchors. Reflection then lets
the first asymmetric pair have blue on the left. Witnesses under either orientation
lift to arithmetic progressions in the original 185-position interval.
-/

namespace OMA.R_Green14_W_3_14_R1_H1_R1_H2_R2

private theorem windowLift (c : ℕ → Bool) (offset width : ℕ)
    (fit : offset + width ≤ 185)
    (result : ∃ (b : Bool) (a d : ℕ), 0 < d ∧
      a + (if b then 2 else 13) * d < width ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (offset + (a + t.val * d)) = b) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 13) * d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a + t.val * d) = b := by
  obtain ⟨b,a,d,hstep,hbound,hcolors⟩ := result
  exact ⟨b, offset + a, d, hstep, by omega, fun t ht => by
    simpa only [Nat.add_assoc] using hcolors t ht⟩

private theorem reflection (c : ℕ → Bool) (width : ℕ)
    (result : ∃ (b : Bool) (a d : ℕ), 0 < d ∧
      a + (if b then 2 else 13) * d < width ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (width - 1 - (a + t.val * d)) = b) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 13) * d < width ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a + t.val * d) = b := by
  obtain ⟨b,a,d,hstep,hbound,hcolors⟩ := result
  let last := if b then 2 else 13
  change a + last * d < width at hbound
  change ∀ t : Fin 14, t.val ≤ last → _ at hcolors
  have hlast : last < 14 := by cases b <;> decide
  refine ⟨b, width - 1 - (a + last * d), d, hstep, ?_, ?_⟩
  · change width - 1 - (a + last * d) + last * d < width
    omega
  · intro t ht
    change t.val ≤ last at ht
    let reverse : Fin 14 := ⟨last - t.val, by omega⟩
    have hsum : (last - t.val) * d + t.val * d = last * d := by
      rw [← Nat.add_mul, Nat.sub_add_cancel ht]
    have hindex : width - 1 - (a + reverse.val * d) =
        width - 1 - (a + last * d) + t.val * d := by
      change width - 1 - (a + (last - t.val) * d) = _
      omega
    rw [← hindex]
    exact hcolors reverse (by dsimp [reverse]; omega)

private theorem orient (c : ℕ → Bool) (width : ℕ) :
    (∀ i : ℕ, 2*i+1 < width →
      (∀ j < i, c j = c (width-1-j)) → c i = true → c (width-1-i) = true) ∨
    (∀ i : ℕ, 2*i+1 < width →
      (∀ j < i, c (width-1-j) = c j) → c (width-1-i) = true → c i = true) := by
  classical
  by_cases failure : ∃ i : ℕ, 2*i+1 < width ∧
      (∀ j < i, c j = c (width-1-j)) ∧ c i = true ∧ c (width-1-i) = false
  · right
    obtain ⟨i, hibound, hiprev, hicol, hiref⟩ := failure
    intro j hjbound hjprev hjref
    rcases lt_trichotomy j i with hj | rfl | hj
    · exact (hiprev j hj).trans hjref
    · exact Bool.false_ne_true (hiref.symm.trans hjref) |>.elim
    · exact Bool.false_ne_true (hiref.symm.trans ((hjprev i hj).trans hicol)) |>.elim
  · left
    intro i hibound hiprev hicol
    cases hiref : c (width-1-i)
    · exact (failure ⟨i, hibound, hiprev, hicol, hiref⟩).elim
    · rfl

private theorem symmetricWindow (c : ℕ → Bool) (width left right : ℕ)
    (order : left < right) (center : left + right + 1 = width)
    (leftRed : c left = true) (rightRed : c right = true)
    (gap : ∀ q, left < q → q < right → c q = false)
    (certificate : ∀ f : ℕ → Bool, f left = true → f right = true →
      (∀ q, left < q → q < right → f q = false) →
      (∀ i : ℕ, 2*i+1 < width →
        (∀ j < i, f j = f (width-1-j)) → f i = true → f (width-1-i) = true) →
      ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 13) * d < width ∧
        ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → f (a + t.val * d) = b) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 13) * d < width ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a + t.val * d) = b := by
  rcases orient c width with normal | reversed
  · exact certificate c leftRed rightRed gap normal
  · apply reflection
    let f (q : ℕ) := c (width - 1 - q)
    have fleft : f left = true := by
      have idx : width - 1 - left = right := by omega
      simpa only [f, idx] using rightRed
    have fright : f right = true := by
      have idx : width - 1 - right = left := by omega
      simpa only [f, idx] using leftRed
    have fgap (q : ℕ) (hlo : left < q) (hhi : q < right) : f q = false :=
      gap _ (by omega) (by omega)
    apply certificate f fleft fright fgap
    intro i hi hp hc
    have involutive (q : ℕ) (hq : q < width) : width - 1 - (width - 1 - q) = q := by omega
    have hc' : c (width - 1 - i) = true := hc
    have hs (j : ℕ) (hj : j < i) : c (width - 1 - j) = c j := by
      simpa only [f, involutive j (by omega)] using hp j hj
    simpa only [f, involutive i (by omega)] using reversed i hi hs hc'

def H1 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 93 = true →
    (∀ q : Nat, 89 < q → q < 93 → c q = false) →
    (∀ i : Nat, 2*i+1 < 183 →
      (∀ j < i, c j = c (182-j)) → c i = true → c (182-i) = true) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 183 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), (p = 97 ∨ p = 98) →
    c (184-p) = true → c 93 = true →
    (∀ q : Nat, 184-p < q → q < 93 → c q = false) →
    (∀ i : Nat, 2*i+1 < 278-p →
      (∀ j < i, c j = c (278-p-1-j)) → c i = true → c (278-p-1-i) = true) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 278-p ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ c : Nat → Bool, c 90 = true → c 95 = true →
    (∀ q : Nat, 90 < q → q < 95 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 183 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), (p = 99 ∨ p = 100) →
    c 88 = true → c (p-3) = true →
    (∀ q : Nat, 88 < q → q < p-3 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 181 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1_H1_R1.H2 := by
  intro at95 at97or98 at96 at99or100 c p hlow hhigh hleft hright hgap
  by_cases p95 : p = 95
  · subst p
    apply windowLift c 2 183 (by decide)
    exact symmetricWindow (fun q => c (2+q)) 183 89 93 (by decide) (by decide)
      hleft hright (fun q hlo hhi => hgap (2+q) (by omega) (by omega)) at95
  by_cases p96 : p = 96
  · subst p
    apply windowLift c 1 183 (by decide)
    exact at96 (fun q => c (1+q)) hleft hright
      (fun q hlo hhi => hgap (1+q) (by omega) (by omega))
  by_cases hmiddle : p = 97 ∨ p = 98
  · let offset := p-93
    have idxLeft : offset + (184-p) = 91 := by dsimp [offset]; omega
    have idxRight : offset + 93 = p := by dsimp [offset]; omega
    have fit : offset + (278-p) ≤ 185 := by dsimp [offset]; omega
    apply windowLift c offset (278-p) fit
    apply symmetricWindow (fun q => c (offset+q)) (278-p) (184-p) 93
      (by omega) (by omega)
    · simpa only [idxLeft] using hleft
    · simpa only [idxRight] using hright
    · intro q hlo hhi
      exact hgap _ (by omega) (by omega)
    · exact fun f => at97or98 f p hmiddle
  · have hlast : p = 99 ∨ p = 100 := by omega
    have idxRight : 3 + (p-3) = p := by omega
    apply windowLift c 3 181 (by decide)
    exact at99or100 (fun q => c (3+q)) p hlast hleft
      (by simpa only [idxRight] using hright)
      (fun q hlo hhi => hgap (3+q) (by omega) (by omega))

end OMA.R_Green14_W_3_14_R1_H1_R1_H2_R2
