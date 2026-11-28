import OMAReductions.R_Green14_W_3_14_R1

/-!
The center gaps share a 185-position window anchored at red position 91.
Only first red 94 is kept at length 186 for either of the original anchors.
-/

namespace OMA.R_Green14_W_3_14_R1_H1_R1

def H1 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), 92 ≤ p → p ≤ 93 →
    c 91 = true → c p = true → (∀ q : Nat, 91 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), 95 ≤ p → p ≤ 100 →
    c 91 = true → c p = true → (∀ q : Nat, 91 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), 101 ≤ p → p ≤ 105 →
    c 91 = true → c p = true → (∀ q : Nat, 91 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (anchor : Nat), 91 ≤ anchor → anchor ≤ 92 →
    c anchor = true → c (anchor+3) = true → c (anchor+1) = false → c (anchor+2) = false →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 186 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1.H1 := by
  classical
  intro early middle late full r j _ jhi red _
  let offset := 1-j.val
  have hoff : offset ≤ 1 := by dsimp [offset]; omega
  have hstart : offset+91 = 92-j.val := by dsimp [offset]; omega
  let c (q : Nat) := r (Fin.ofNat 186 (offset+q))
  have anchor : c 91 = true := by simpa only [c,hstart] using red
  have lift (base width : Nat) (fit : base+width ≤ 186)
      (result : ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < width ∧
        ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) →
          r (Fin.ofNat 186 (base+(a+t.val*d))) = b) :
      ∃ (b : Bool) (a d : Fin 186), 0 < d.val ∧
        a.val + (if b then 2 else 13)*d.val < 186 ∧
        ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) →
          r (Fin.ofNat 186 (a.val+t.val*d.val)) = b := by
    obtain ⟨b,a,d,hd,inside,run⟩ := result
    have dBound : d < 186 := by cases b <;> simp at inside <;> omega
    refine ⟨b, ⟨base+a,by omega⟩, ⟨d,dBound⟩, hd, by dsimp; omega, ?_⟩
    intro t ht
    simpa only [Nat.add_assoc] using run t ht
  by_cases allBlue : ∀ q : Nat, 92 ≤ q → q ≤ 105 → c q = false
  · apply lift offset 185 (by omega)
    refine ⟨false,92,1,by decide,by decide,?_⟩
    intro t _
    simpa [c] using allBlue (92+t.val) (by omega) (by have := t.isLt; omega)
  · push Not at allBlue
    obtain ⟨q,lo,hi,color⟩ := allBlue
    have existsRed : ∃ p : Nat, 92 ≤ p ∧ p ≤ 105 ∧ c p = true :=
      ⟨q,lo,hi,Bool.ne_false_iff.mp color⟩
    let p := Nat.find existsRed
    obtain ⟨lo,hi,hp⟩ : 92 ≤ p ∧ p ≤ 105 ∧ c p = true := Nat.find_spec existsRed
    have gap (q : Nat) (loQ : 91 < q) (hiQ : q < p) : c q = false := by
      apply Bool.eq_false_iff.mpr
      intro hq
      exact Nat.find_min existsRed hiQ ⟨by omega,by omega,hq⟩
    by_cases h94 : p = 94
    · have sol := full (fun q => r (Fin.ofNat 186 q)) (offset+91)
          (by omega) (by omega) anchor
          (by simpa [c,h94,Nat.add_assoc] using hp)
          (by simpa [c,Nat.add_assoc] using gap 92 (by decide) (by omega))
          (by simpa [c,Nat.add_assoc] using gap 93 (by decide) (by omega))
      exact lift 0 186 (by decide) (by simpa using sol)
    · apply lift offset 185 (by omega)
      by_cases h93 : p ≤ 93
      · exact early c p lo h93 anchor hp gap
      by_cases h100 : p ≤ 100
      · exact middle c p (by omega) h100 anchor hp gap
      · exact late c p (by omega) hi anchor hp gap

end OMA.R_Green14_W_3_14_R1_H1_R1