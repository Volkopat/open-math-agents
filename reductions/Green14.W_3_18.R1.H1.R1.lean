import OMAReductions.R_Green14_W_3_18_R1

/-! The red-extension case of W(3,18). A central block of 279 points
forces a blue progression of length 17 once the W(3,17) upper bound
is supplied. Its available flanks are red, giving concrete signed
literals for the remaining certificate. -/

namespace OMA.R_Green14_W_3_18_R1_H1_R1

private theorem ofNat_val {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) :
    (Fin.ofNat n a).val = a :=
  Nat.mod_eq_of_lt h

/-- The W(3,17) upper bound in the finite prefix representation. -/
def H1 : Prop :=
  ∀ r : Fin 279 → Bool,
    (∀ a d : Fin 279, 0 < d.val → a.val + 2 * d.val < 279 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 279 (a.val + t.val * d.val)) = true) →
    ∃ a d : ℕ, 0 < d ∧ a + 16 * d < 279 ∧
      ∀ t : Fin 17, r (Fin.ofNat 279 (a + t.val * d)) = false

/-- The remaining red-endpoint certificate with a specified central blue
17-progression and red flanks whenever those indices exist. -/
def H2 : Prop :=
  ∀ r : Fin 312 → Bool, r (Fin.ofNat 312 311) = true →
    (∀ a d : Fin 312, 0 < d.val → a.val + 2 * d.val < 312 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 312 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 312, 0 < d.val → a.val + 17 * d.val < 312 →
      ¬ ∀ t : Fin 18, r (Fin.ofNat 312 (a.val + t.val * d.val)) = false) →
    ∀ a d : ℕ, 16 ≤ a → 0 < d → a + 16 * d ≤ 294 →
      (∀ t : Fin 17, r (Fin.ofNat 312 (a + t.val * d)) = false) →
      r (Fin.ofNat 312 (a + 17 * d)) = true →
      (d ≤ a → r (Fin.ofNat 312 (a - d)) = true) → False

theorem main : H1 → H2 → OMA.R_Green14_W_3_18_R1.H1 := by
  classical
  intro hcore hcert r hr hb
  by_contra hNo
  let ext (k : Fin 312) : Bool := if h : k.val < 311 then r ⟨k.val, h⟩ else true
  have eq_prefix (i : ℕ) (hi : i < 311) :
      ext (Fin.ofNat 312 i) = r (Fin.ofNat 311 i) := by
    have hv : Fin.ofNat 312 i = ⟨i, by omega⟩ := Fin.ext (ofNat_val (by omega))
    have hu : Fin.ofNat 311 i = ⟨i, hi⟩ := Fin.ext (ofNat_val hi)
    rw [hv, hu]
    simp [ext, hi]
  have endRed : ext (Fin.ofNat 312 311) = true := by
    simp [ext]
  have redFree (a d : Fin 312) (hd : 0 < d.val) (hlim : a.val + 2 * d.val < 312) :
      ¬ ∀ t : Fin 3, ext (Fin.ofNat 312 (a.val + t.val * d.val)) = true := by
    intro mono
    by_cases hin : a.val + 2 * d.val < 311
    · let a' : Fin 311 := ⟨a.val, by omega⟩
      let d' : Fin 311 := ⟨d.val, by omega⟩
      apply hr a' d' hd hin
      intro t
      have hmul := Nat.mul_le_mul_right d.val (show t.val ≤ 2 by omega)
      change r (Fin.ofNat 311 (a.val + t.val * d.val)) = true
      exact (eq_prefix _ (by omega)).symm.trans (mono t)
    · have heq : a.val + 2 * d.val = 311 := by omega
      let d' : Fin 156 := ⟨d.val, by omega⟩
      apply hNo
      refine ⟨d', hd, ?_⟩
      intro t
      have ht : 311 - (2 - t.val) * d'.val = a.val + t.val * d.val := by
        dsimp [d']
        fin_cases t <;> simp <;> omega
      have hmul := Nat.mul_lt_mul_of_pos_right t.isLt hd
      rw [ht, ← eq_prefix _ (by omega)]
      exact mono ⟨t.val, by omega⟩
  have blueFree (a d : Fin 312) (hd : 0 < d.val) (hlim : a.val + 17 * d.val < 312) :
      ¬ ∀ t : Fin 18, ext (Fin.ofNat 312 (a.val + t.val * d.val)) = false := by
    intro mono
    by_cases hin : a.val + 17 * d.val < 311
    · let a' : Fin 311 := ⟨a.val, by omega⟩
      let d' : Fin 311 := ⟨d.val, by omega⟩
      apply hb a' d' hd hin
      intro t
      have hmul := Nat.mul_le_mul_right d.val (show t.val ≤ 17 by omega)
      change r (Fin.ofNat 311 (a.val + t.val * d.val)) = false
      exact (eq_prefix _ (by omega)).symm.trans (mono t)
    · have heq : a.val + 17 * d.val = 311 := by omega
      have hf : ext (Fin.ofNat 312 311) = false := by simpa [heq] using mono (Fin.last 17)
      exact Bool.noConfusion (endRed.symm.trans hf)
  let core (k : Fin 279) := ext (Fin.ofNat 312 (k.val + 16))
  have coreRedFree (a d : Fin 279) (hd : 0 < d.val) (hlim : a.val + 2 * d.val < 279) :
      ¬ ∀ t : Fin 3, core (Fin.ofNat 279 (a.val + t.val * d.val)) = true := by
    intro mono
    let a' : Fin 312 := ⟨a.val + 16, by omega⟩
    let d' : Fin 312 := ⟨d.val, by omega⟩
    apply redFree a' d' hd (by dsimp [a', d']; omega)
    intro t
    have hmul := Nat.mul_le_mul_right d.val (show t.val ≤ 2 by omega)
    have hi : a.val + t.val * d.val < 279 := by omega
    simpa only [core, ofNat_val hi, a', d', Nat.add_right_comm] using mono t
  obtain ⟨a, d, hd, hlim, hblue⟩ := hcore core coreRedFree
  let A := a + 16
  have hA : A + 16 * d ≤ 294 := by dsimp [A]; omega
  have blue (t : Fin 17) : ext (Fin.ofNat 312 (A + t.val * d)) = false := by
    have hmul := Nat.mul_le_mul_right d (show t.val ≤ 16 by omega)
    have hi : a + t.val * d < 279 := by omega
    simpa only [core, ofNat_val hi, A, Nat.add_right_comm] using hblue t
  have right : ext (Fin.ofNat 312 (A + 17 * d)) = true := by
    by_contra! hfalse
    let a' : Fin 312 := ⟨A, by omega⟩
    let d' : Fin 312 := ⟨d, by omega⟩
    apply blueFree a' d' hd (by dsimp [a', d']; omega)
    intro t
    by_cases ht : t.val < 17
    · exact blue ⟨t.val, ht⟩
    · have heq : t.val = 17 := by omega
      simpa only [a', d', heq] using Bool.eq_false_of_not_eq_true hfalse
  have left (hle : d ≤ A) : ext (Fin.ofNat 312 (A - d)) = true := by
    by_contra! hfalse
    let a' : Fin 312 := ⟨A - d, by omega⟩
    let d' : Fin 312 := ⟨d, by omega⟩
    apply blueFree a' d' hd (by dsimp [a', d']; omega)
    intro t
    by_cases ht : t.val = 0
    · simpa only [a', d', ht, Nat.zero_mul, Nat.add_zero] using Bool.eq_false_of_not_eq_true hfalse
    · have hmul : (t.val - 1) * d + d = t.val * d := by
        rw [← Nat.succ_mul]
        congr 1
        omega
      have heq : a'.val + t.val * d'.val = A + (t.val - 1) * d := by
        dsimp [a', d']
        omega
      rw [heq]
      exact blue ⟨t.val - 1, by omega⟩
  exact hcert ext endRed redFree blueFree A d (by dsimp [A]; omega) hd hA blue right left

end OMA.R_Green14_W_3_18_R1_H1_R1
