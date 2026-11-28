import OMAStatements.S_mo_306162


/-!
David G. Stork asked whether Bob can always win the two-level Penney game
with probability above one half (MathOverflow 306162). In a 2018 comment
usul tested Alice's hand THH, HHT by simulation. Encode H by 0 and T by 1.
Alice can use exactly that hand: its two word codes are 4 and 1.

The first two bits initialize the state. Each subsequent bit completes a
three-bit window. Four Boolean flags record which words have appeared.
For each of Bob's fifteen replies the table below is a nonnegative integer
potential with a common denominator. Its numerator dominates the denominator
on winning states. At an undecided state it dominates the mean of the two
successor numerators. The kernel checks every one of these finite inequalities.
Induction on the time horizon bounds the mass of winning prefix cylinders;
continuity from below passes to arbitrary completion times.

Source: https://mathoverflow.net/q/306162
Simulation: https://mathoverflow.net/questions/306162/#comment761104_306162
Credit: @Aryan-Poonacha
-/

open MeasureTheory OMA.S_mo_306162
open scoped ENNReal
namespace TwoLevel

private noncomputable abbrev coin := (PMF.uniformOfFintype Bool).toMeasure
private noncomputable def toss := Measure.infinitePi (fun _ : ℕ => coin)
private theorem fair : fairCoin toss := by
  intro s x
  change toss ((s : Set ℕ).pi (fun i => {x i})) = _
  rw [toss, Measure.infinitePi_pi _ (by measurability)]
  have h (b : Bool) : coin {b} = (2 : ℝ≥0∞)⁻¹ := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
    norm_num
  simp [h]

private def word (j : ℕ) : Word 3 := fun i => j.testBit (2-i.val)
private def hand (a b : ℕ) := ({word a, word b} : Finset (Word 3))
private def alice : Choice 3 := ⟨hand 1 4, by decide⟩
private def replies : Array (ℕ × ℕ) := #[(0,2),(0,3),(0,5),(0,6),(0,7),(2,3),(2,5),(2,6),(2,7),(3,5),(3,6),(3,7),(5,6),(5,7),(6,7)]
private def rpair (j : Fin 15) := replies[j.val]?.getD (0,2)
private theorem exhaustive : ∀ B : Choice 3, disjointChoices alice B →
    ∃ j : Fin 15, B.val = hand (rpair j).1 (rpair j).2 := by
  rintro ⟨B,hB⟩ h
  change alice.val ∩ B = ∅ at h
  have H : ∀ S : Finset (Fin 3 → Bool), S.card = 2 → alice.val ∩ S = ∅ → ∃ j : Fin 15, S = hand (rpair j).1 (rpair j).2 := by
    decide +kernel
  exact H B hB h

private inductive State where
  | start | single (x : Bool) | live (x y a b c d : Bool)
  deriving DecidableEq, Fintype
private def next (j : Fin 15) (s : State) (z : Bool) : State :=
  match s with
  | .start => .single z
  | .single x => .live x z false false false false
  | .live x y a b c d =>
    let v := 4*x.toNat+2*y.toNat+z.toNat
    .live y z (a || decide (v=1)) (b || decide (v=4))
      (c || decide (v=(rpair j).1)) (d || decide (v=(rpair j).2))
private def lost : State → Bool
  | .live _ _ a b _ _ => a && b
  | _ => false
private def won : State → Bool
  | .live _ _ a b c d => !(a && b) && c && d
  | _ => false

private def seen (v : ℕ) (ω : Ω) (t : ℕ) : Bool :=
  decide (∃ q : Fin t, ∀ i : Fin 3, ω (q.val+i.val) = word v i)
private theorem seen_eq (v : ℕ) (ω : Ω) (t : ℕ) :
    seen v ω (t+1) = true ↔ occurredBy (word v) ω t := by
  simp only [seen, decide_eq_true_eq, occurredBy, occurs, Fin.exists_iff]
  constructor
  · rintro ⟨s, hs, hw⟩
    exact ⟨s, by omega, hw⟩
  · rintro ⟨s, hs, hw⟩
    exact ⟨s, by omega, hw⟩

private def actual (j : Fin 15) (ω : Ω) : ℕ → State
  | 0 => .start
  | 1 => .single (ω 0)
  | t+2 => .live (ω t) (ω (t+1)) (seen 1 ω t) (seen 4 ω t)
      (seen (rpair j).1 ω t) (seen (rpair j).2 ω t)

private theorem triple (v : ℕ) (hv : v < 8) (x y z : Bool) :
    (∀ i : Fin 3, (![x,y,z] : Fin 3 → Bool) i = word v i) ↔
    4*x.toNat+2*y.toNat+z.toNat = v := by
  interval_cases v <;> revert x y z <;> decide

private theorem updateSeen (v : ℕ) (hv : v < 8) (ω : Ω) (t : ℕ) :
    seen v ω (t+1) = (seen v ω t || decide (4*(ω t).toNat+2*(ω (t+1)).toNat+(ω (t+2)).toNat=v)) := by
  have hw : (fun i : Fin 3 => ω (t+i.val)) = ![ω t,ω (t+1),ω (t+2)] := by
    funext i; fin_cases i <;> rfl
  apply Bool.eq_iff_iff.mpr
  simp only [seen, decide_eq_true_eq, Bool.or_eq_true, Fin.exists_fin_succ', Fin.val_castSucc,
    Fin.val_last, ← triple v hv, ← hw]
private theorem rsmall : ∀ j : Fin 15, (rpair j).1 < 8 ∧ (rpair j).2 < 8 := by decide
private theorem step_actual (j : Fin 15) (ω : Ω) (t : ℕ) :
    actual j ω (t+1) = next j (actual j ω t) (ω t) := by
  rcases t with _|_|t
  · rfl
  · rfl
  · simp only [actual, next, updateSeen 1 (by decide), updateSeen 4 (by decide),
      updateSeen _ (rsmall j).1, updateSeen _ (rsmall j).2]


private def stateIndex : State → ℕ
  | .start => 0
  | .single x => 1+x.toNat
  | .live x y a b c d => 3+32*x.toNat+16*y.toNat+8*a.toNat+4*b.toNat+2*c.toNat+d.toNat
private def row0 : Array ℕ := #[
  3, 4, 2, 4, 6, 8, 12, 0, 6, 0, 12, 4, 6, 8, 12,
  0, 0, 0, 0, 4, 6, 8, 12, 4, 6, 8, 12, 0, 0, 8,
  12, 0, 0, 0, 0, 2, 6, 4, 12, 2, 6, 4, 12, 0, 0,
  4, 12, 0, 0, 0, 0, 2, 6, 4, 12, 2, 6, 4, 12, 0,
  0, 4, 12, 0, 0, 0, 0]
private def row1 : Array ℕ := #[
  3, 4, 2, 4, 6, 8, 12, 0, 6, 0, 12, 4, 6, 8, 12,
  0, 0, 0, 0, 4, 6, 8, 12, 4, 6, 8, 12, 0, 0, 8,
  12, 0, 0, 0, 0, 2, 6, 4, 12, 2, 6, 4, 12, 0, 0,
  4, 12, 0, 0, 0, 0, 2, 6, 4, 12, 2, 6, 4, 12, 0,
  0, 4, 12, 0, 0, 0, 0]
private def row2 : Array ℕ := #[
  1, 1, 1, 1, 2, 2, 4, 0, 2, 0, 4, 1, 2, 2, 4,
  0, 0, 0, 0, 1, 2, 2, 4, 1, 2, 2, 4, 0, 0, 2,
  4, 0, 0, 0, 0, 1, 2, 2, 4, 1, 2, 2, 4, 0, 0,
  2, 4, 0, 0, 0, 0, 1, 2, 2, 4, 1, 2, 2, 4, 0,
  0, 2, 4, 0, 0, 0, 0]
private def row3 : Array ℕ := #[
  2, 2, 2, 2, 3, 4, 6, 0, 3, 0, 6, 2, 3, 4, 6,
  0, 0, 0, 0, 2, 3, 4, 6, 2, 3, 4, 6, 0, 0, 4,
  6, 0, 0, 0, 0, 1, 3, 2, 6, 1, 3, 2, 6, 0, 0,
  2, 6, 0, 0, 0, 0, 3, 3, 6, 6, 3, 3, 6, 6, 0,
  0, 6, 6, 0, 0, 0, 0]
private def row4 : Array ℕ := #[
  2, 2, 2, 2, 5, 4, 10, 0, 5, 0, 10, 2, 5, 4, 10,
  0, 0, 0, 0, 2, 5, 4, 10, 2, 5, 4, 10, 0, 0, 4,
  10, 0, 0, 0, 0, 1, 5, 2, 10, 1, 5, 2, 10, 0, 0,
  2, 10, 0, 0, 0, 0, 3, 5, 6, 10, 3, 5, 6, 10, 0,
  0, 6, 10, 0, 0, 0, 0]
private def row5 : Array ℕ := #[
  3, 4, 2, 4, 8, 8, 12, 0, 0, 0, 12, 4, 8, 8, 12,
  0, 0, 0, 0, 4, 8, 8, 12, 4, 8, 8, 12, 4, 8, 8,
  12, 0, 0, 0, 0, 2, 4, 4, 12, 2, 4, 4, 12, 2, 4,
  4, 12, 0, 0, 0, 0, 2, 4, 4, 12, 2, 4, 4, 12, 2,
  4, 4, 12, 0, 0, 0, 0]
private def row6 : Array ℕ := #[
  9, 10, 8, 10, 16, 12, 24, 0, 0, 0, 24, 10, 16, 12, 24,
  0, 0, 0, 0, 10, 16, 12, 24, 10, 16, 12, 24, 10, 16, 12,
  24, 0, 0, 0, 0, 8, 8, 12, 24, 8, 8, 12, 24, 8, 8,
  12, 24, 0, 0, 0, 0, 8, 8, 12, 24, 8, 8, 12, 24, 8,
  8, 12, 24, 0, 0, 0, 0]
private def row7 : Array ℕ := #[
  7, 8, 6, 8, 16, 16, 24, 0, 0, 0, 24, 8, 16, 16, 24,
  0, 0, 0, 0, 8, 16, 16, 24, 8, 16, 16, 24, 8, 16, 16,
  24, 0, 0, 0, 0, 4, 8, 8, 24, 4, 8, 8, 24, 4, 8,
  8, 24, 0, 0, 0, 0, 8, 8, 24, 24, 8, 8, 24, 24, 8,
  8, 24, 24, 0, 0, 0, 0]
private def row8 : Array ℕ := #[
  39, 44, 34, 44, 140, 84, 210, 0, 0, 0, 210, 44, 140, 84, 210,
  0, 0, 0, 0, 44, 140, 84, 210, 44, 140, 84, 210, 44, 140, 84,
  210, 0, 0, 0, 0, 22, 70, 42, 210, 22, 70, 42, 210, 22, 70,
  42, 210, 0, 0, 0, 0, 46, 70, 126, 210, 46, 70, 126, 210, 46,
  70, 126, 210, 0, 0, 0, 0]
private def row9 : Array ℕ := #[
  9, 10, 8, 10, 16, 12, 24, 0, 0, 0, 24, 10, 16, 12, 24,
  0, 0, 0, 0, 10, 16, 12, 24, 10, 16, 12, 24, 10, 16, 12,
  24, 0, 0, 0, 0, 8, 8, 12, 24, 8, 8, 12, 24, 8, 8,
  12, 24, 0, 0, 0, 0, 8, 8, 12, 24, 8, 8, 12, 24, 8,
  8, 12, 24, 0, 0, 0, 0]
private def row10 : Array ℕ := #[
  3, 4, 2, 4, 4, 4, 6, 0, 0, 0, 6, 4, 4, 4, 6,
  0, 0, 0, 0, 4, 4, 4, 6, 4, 4, 4, 6, 4, 4, 4,
  6, 0, 0, 0, 0, 2, 2, 2, 6, 2, 2, 2, 6, 2, 2,
  2, 6, 0, 0, 0, 0, 2, 2, 6, 6, 2, 2, 6, 6, 2,
  2, 6, 6, 0, 0, 0, 0]
private def row11 : Array ℕ := #[
  19, 24, 14, 24, 40, 24, 60, 0, 0, 0, 60, 24, 40, 24, 60,
  0, 0, 0, 0, 24, 40, 24, 60, 24, 40, 24, 60, 24, 40, 24,
  60, 0, 0, 0, 0, 12, 20, 12, 60, 12, 20, 12, 60, 12, 20,
  12, 60, 0, 0, 0, 0, 16, 20, 36, 60, 16, 20, 36, 60, 16,
  20, 36, 60, 0, 0, 0, 0]
private def row12 : Array ℕ := #[
  5, 5, 5, 5, 6, 8, 12, 0, 0, 0, 12, 5, 6, 8, 12,
  0, 0, 0, 0, 5, 6, 8, 12, 5, 6, 8, 12, 5, 6, 8,
  12, 0, 0, 0, 0, 4, 6, 4, 12, 4, 6, 4, 12, 4, 6,
  4, 12, 0, 0, 0, 0, 6, 6, 12, 12, 6, 6, 12, 12, 6,
  6, 12, 12, 0, 0, 0, 0]
private def row13 : Array ℕ := #[
  11, 11, 11, 11, 20, 16, 40, 0, 0, 0, 40, 11, 20, 16, 40,
  0, 0, 0, 0, 11, 20, 16, 40, 11, 20, 16, 40, 11, 20, 16,
  40, 0, 0, 0, 0, 8, 20, 8, 40, 8, 20, 8, 40, 8, 20,
  8, 40, 0, 0, 0, 0, 14, 20, 24, 40, 14, 20, 24, 40, 14,
  20, 24, 40, 0, 0, 0, 0]
private def row14 : Array ℕ := #[
  6, 6, 6, 6, 10, 6, 15, 0, 0, 0, 15, 6, 10, 6, 15,
  0, 0, 0, 0, 6, 10, 6, 15, 6, 10, 6, 15, 6, 10, 6,
  15, 0, 0, 0, 0, 3, 5, 3, 15, 3, 5, 3, 15, 3, 5,
  3, 15, 0, 0, 0, 0, 9, 15, 9, 15, 9, 15, 9, 15, 9,
  15, 9, 15, 0, 0, 0, 0]
private def row (j : Fin 15) : Array ℕ :=
  match j.val with
  | 0 => row0
  | 1 => row1
  | 2 => row2
  | 3 => row3
  | 4 => row4
  | 5 => row5
  | 6 => row6
  | 7 => row7
  | 8 => row8
  | 9 => row9
  | 10 => row10
  | 11 => row11
  | 12 => row12
  | 13 => row13
  | _ => row14
private def den (j : Fin 15) : ℕ :=
  match j.val with
  | 0 => 12
  | 1 => 12
  | 2 => 4
  | 3 => 6
  | 4 => 10
  | 5 => 12
  | 6 => 24
  | 7 => 24
  | 8 => 210
  | 9 => 24
  | 10 => 6
  | 11 => 60
  | 12 => 12
  | 13 => 40
  | _ => 15
private def num (j : Fin 15) (s : State) := (row j)[stateIndex s]?.getD 0
private theorem cert : ∀ (j : Fin 15) (s : State),
    0 < den j ∧ 2 * num j .start ≤ den j ∧
    (won s = true → den j ≤ num j s) ∧
    (won s = false → lost s = false →
      num j (next j s false) + num j (next j s true) ≤ 2 * num j s) := by
  intro j
  fin_cases j <;> decide +kernel

private def pref (t : ℕ) (ξ : Ω) : Set Ω := {ω | ∀ i < t, ω i = ξ i}
private theorem mass_pref (t : ℕ) (ξ : Ω) : toss (pref t ξ) = (2 : ℝ≥0∞)⁻¹ ^ t := by
  have hf := fair (Finset.range t) ξ
  simpa [pref] using hf

private def cap (j : Fin 15) (t h : ℕ) : Set Ω :=
  {ω | ∃ r, t ≤ r ∧ r ≤ t+h ∧ won (actual j ω r) = true}
private theorem hist_same (j : Fin 15) (t : ℕ) {ξ ω : Ω} (h : ω ∈ pref t ξ) :
    actual j ω t = actual j ξ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [step_actual, step_actual, ih (fun i hi => h i (by omega)), h t (by omega)]
private theorem staysLost (j : Fin 15) : ∀ s z, lost s = true → lost (next j s z) = true := by
  intro s z
  cases s <;> simp +contextual [lost,next]
private theorem neverWon : ∀ (s : State), lost s = true → won s ≠ true := by decide
private theorem lost_future (j : Fin 15) (ω : Ω) {t r : ℕ} (h : t ≤ r)
    (hl : lost (actual j ω t) = true) : lost (actual j ω r) = true := by
  induction r, h using Nat.le_induction with
  | base => exact hl
  | succ r _ ih => rw [step_actual]; exact staysLost j _ _ ih

private theorem cap_bound (j : Fin 15) (h t : ℕ) (ξ : Ω) :
    toss (pref t ξ ∩ cap j t h) * den j ≤
      (2 : ℝ≥0∞)⁻¹ ^ t * num j (actual j ξ t) := by
  induction h generalizing t ξ with
  | zero =>
    by_cases hwin : won (actual j ξ t) = true
    · calc
        _ ≤ toss (pref t ξ) * den j := mul_le_mul_left (measure_mono Set.inter_subset_left) _
        _ ≤ _ := by
          rw [mass_pref]
          gcongr
          exact_mod_cast (cert j _).2.2.1 hwin
    · have he : pref t ξ ∩ cap j t 0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨hp,r,hr,hr',hw⟩
        obtain rfl : r = t := by omega
        exact hwin ((hist_same j r hp) ▸ hw)
      simp only [he, measure_empty, zero_mul, zero_le]
  | succ h ih =>
    by_cases hwin : won (actual j ξ t) = true
    · calc
        _ ≤ toss (pref t ξ) * den j := mul_le_mul_left (measure_mono Set.inter_subset_left) _
        _ ≤ _ := by
          rw [mass_pref]
          gcongr
          exact_mod_cast (cert j _).2.2.1 hwin
    by_cases hlose : lost (actual j ξ t) = true
    · have he : pref t ξ ∩ cap j t (h+1) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨hp,r,hr,_,hw⟩
        exact neverWon _ (lost_future j ω hr ((hist_same j t hp).symm ▸ hlose)) hw
      simp only [he, measure_empty, zero_mul, zero_le]
    let ext (z : Bool) : Ω := Function.update ξ t z
    have pre {ω : Ω} (hp : ω ∈ pref t ξ) : ω ∈ pref (t+1) (ext (ω t)) := by
      intro i hi
      by_cases e : i=t
      · simp [ext,e]
      · simpa [ext,Function.update_of_ne e] using hp i (by omega)
    have sub : pref t ξ ∩ cap j t (h+1) ⊆
        (pref (t+1) (ext false) ∩ cap j (t+1) h) ∪
        (pref (t+1) (ext true) ∩ cap j (t+1) h) := by
      rintro ω ⟨hp,r,hr,hup,hw⟩
      have hne : r ≠ t := by
        rintro rfl; exact hwin ((hist_same j r hp) ▸ hw)
      have hc : ω ∈ cap j (t+1) h := ⟨r,by omega,by omega,hw⟩
      have he := pre hp
      cases hz : ω t <;> rw [hz] at he
      · exact Or.inl ⟨he,hc⟩
      · exact Or.inr ⟨he,hc⟩
    have upd (z : Bool) : actual j (ext z) (t+1) = next j (actual j ξ t) z := by
      rw [step_actual, hist_same j t (ξ := ξ) (ω := ext z)
        (fun i hi => Function.update_of_ne (by omega : i ≠ t) _ _)]
      simp [ext]
    have hab := (cert j (actual j ξ t)).2.2.2 (by simpa using hwin) (by simpa using hlose)
    calc
      _ ≤ (toss (pref (t+1) (ext false) ∩ cap j (t+1) h) +
          toss (pref (t+1) (ext true) ∩ cap j (t+1) h)) * den j :=
        mul_le_mul_left ((measure_mono sub).trans (measure_union_le _ _)) _
      _ ≤ _ := by
        rw [add_mul]
        apply (add_le_add (ih (t+1) (ext false)) (ih (t+1) (ext true))).trans
        rw [upd,upd,← mul_add,pow_succ,mul_assoc]
        gcongr
        have hc : (num j (next j (actual j ξ t) false) : ℝ≥0∞) +
            num j (next j (actual j ξ t) true) ≤ 2*num j (actual j ξ t) := by exact_mod_cast hab
        calc
          _ ≤ (2 : ℝ≥0∞)⁻¹ * (2*num j (actual j ξ t)) := mul_le_mul_right hc _
          _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero (by finiteness), one_mul]

private theorem cap_prob (j : Fin 15) (h : ℕ) : toss (cap j 0 h) ≤ (2 : ℝ≥0∞)⁻¹ := by
  have H := cap_bound j h 0 (fun _ => false)
  have hpre : pref 0 (fun _ => false) = Set.univ := by ext; simp [pref]
  rw [hpre,Set.univ_inter] at H
  simp only [pow_zero,one_mul,actual] at H
  have hd : (den j : ℝ≥0∞) ≠ 0 := by exact_mod_cast (cert j .start).1.ne'
  have hn : (2 : ℝ≥0∞) * num j .start ≤ den j := by exact_mod_cast (cert j .start).2.1
  have hh : (2 * toss (cap j 0 h)) * den j ≤ 1 * den j := by
    rw [mul_assoc,one_mul]; exact (mul_le_mul_right H 2).trans hn
  have hc := (ENNReal.mul_le_mul_iff_left hd (by finiteness)).mp hh
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero (by finiteness), one_mul, mul_one] using mul_le_mul_right hc ((2 : ℝ≥0∞)⁻¹)

private theorem occurs_hand {A : Choice 3} {a b : ℕ} (hA : A.val = hand a b)
    (ω : Ω) (t : ℕ) : choiceOccurredBy A ω t ↔
        seen a ω (t+1) = true ∧ seen b ω (t+1) = true := by
  simp [choiceOccurredBy,hA,hand,seen_eq]
private theorem wins_subset {B : Choice 3} {j : Fin 15}
    (hB : B.val = hand (rpair j).1 (rpair j).2) :
    {ω | BWins alice B ω} ⊆ ⋃ h : ℕ, cap j 0 h := by
  rintro ω ⟨b,a,hb,ha,hba⟩
  have hbw := (occurs_hand hB ω b).mp hb.1
  have hal := mt (occurs_hand (A := alice) (a := 1) (b := 4) rfl ω b).mpr (ha.2 b hba)
  apply Set.mem_iUnion.mpr
  refine ⟨b+3,b+3,by omega,by omega,?_⟩
  simp only [actual,won,Bool.and_eq_true,Bool.not_eq_true']
  exact ⟨⟨by cases ha1 : seen 1 ω (b+1) <;> cases ha4 : seen 4 ω (b+1) <;> simp_all only [Bool.false_and, Bool.true_and, and_self, not_true_eq_false],hbw.1⟩,hbw.2⟩
private theorem win_prob {B : Choice 3} {j : Fin 15}
    (hB : B.val = hand (rpair j).1 (rpair j).2) :
    BWinProbability toss alice B ≤ (2 : ℝ≥0∞)⁻¹ := by
  have mono : Monotone (cap j 0) := by
    rintro h k hle ω ⟨r,hr,hr',hw⟩
    exact ⟨r,hr,by omega,hw⟩
  exact (measure_mono (μ := toss) (wins_subset hB)).trans
    ((mono.measure_iUnion).le.trans (iSup_le (cap_prob j)))

end TwoLevel

open TwoLevel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_306162.main) := by
  intro h
  obtain ⟨B,hdis,hwin⟩ := h 3 (by decide) toss fair alice
  obtain ⟨j,hj⟩ := exhaustive B hdis
  exact (not_lt_of_ge (win_prob hj)) hwin
