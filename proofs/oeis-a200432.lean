import OMAStatements.S_oeis_a200432
import Mathlib

/-!
# A generating function for constrained five-term arrays

Credit: @jacklarmer

On the zero-sum slice of the box, a consecutive triple vanishes exactly when
the complementary pair vanishes. Inclusion-exclusion over the five edges of
the cycle reduces the count to unrestricted zero-sum boxes in dimensions
three and five. The coefficients of finite geometric series count these
boxes. Substitution gives a quartic, whose fifth finite difference gives
the numerator of the conjectured generating function.
-/

namespace A200432Proof

noncomputable def box (k n : ℕ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

noncomputable def zeroSet (k n : ℕ) : Finset (Fin k → ℤ) :=
  (box k n).filter fun v => ∑ i, v i = 0

def edge (i : Fin 5) (v : Fin 5 → ℤ) : ℤ := v i + v (i + 1)

noncomputable def maskSet (n m : ℕ) : Finset (Fin 5 → ℤ) :=
  (zeroSet 5 n).filter fun v => ∀ i : Fin 5, m.testBit i.val = true → edge i v = 0

end A200432Proof

namespace A200432Proof

lemma cyclic_nonzero_iff (v : Fin 5 → ℤ) (hz : ∑ i, v i = 0) :
    ((∀ i : Fin 4, v i.castSucc + v i.succ ≠ 0) ∧
      (∀ i : Fin 3, v i.castSucc.castSucc + v i.succ.castSucc + v i.succ.succ ≠ 0)) ↔
      ∀ i : Fin 5, v i + v (i + 1) ≠ 0 := by
  have hsum : v 0 + v 1 + v 2 + v 3 + v 4 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hz
  constructor
  · rintro ⟨hp, ht⟩ i
    fin_cases i
    · exact hp 0
    · exact hp 1
    · exact hp 2
    · exact hp 3
    · have hmid : v 1 + v 2 + v 3 ≠ 0 := ht 1
      change v 4 + v 0 ≠ 0
      omega
  · intro h
    constructor
    · intro i
      fin_cases i
      · exact h 0
      · exact h 1
      · exact h 2
      · exact h 3
    · intro i
      fin_cases i
      · have hedge : v 3 + v 4 ≠ 0 := h 3
        change v 0 + v 1 + v 2 ≠ 0
        omega
      · have hedge : v 4 + v 0 ≠ 0 := h 4
        change v 1 + v 2 + v 3 ≠ 0
        omega
      · have hedge : v 0 + v 1 ≠ 0 := h 0
        change v 2 + v 3 + v 4 ≠ 0
        omega

end A200432Proof

namespace A200432Proof

def ieCoeff (m : ℕ) : ℤ :=
  (-1) ^ ((Finset.univ : Finset (Fin 5)).filter (fun i => m.testBit i.val)).card

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
private lemma mask_indicator : ∀ b : Fin 5 → Bool,
    (if ∀ i, b i = false then (1 : ℤ) else 0) =
      ∑ m ∈ Finset.range 32, ieCoeff m *
        (if ∀ i : Fin 5, m.testBit i.val = true → b i = true then (1 : ℤ) else 0) := by
  decide +kernel

lemma inclusion (n : ℕ) : (OMA.S_oeis_a200432.a n : ℤ) =
    ∑ m ∈ Finset.range 32, ieCoeff m * ((maskSet n m).card : ℤ) := by
  have hcard : OMA.S_oeis_a200432.a n =
      ((zeroSet 5 n).filter (fun v => ∀ i, edge i v ≠ 0)).card := by
    unfold OMA.S_oeis_a200432.a zeroSet box
    congr 1
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hz, h⟩
      exact ⟨⟨hv, hz⟩, (cyclic_nonzero_iff v hz).mp h⟩
    · rintro ⟨⟨hv, hz⟩, h⟩
      exact ⟨hv, hz, (cyclic_nonzero_iff v hz).mpr h⟩
  rw [hcard, Finset.natCast_card_filter]
  calc
    _ = ∑ v ∈ zeroSet 5 n, ∑ m ∈ Finset.range 32, ieCoeff m *
          (if ∀ i : Fin 5, m.testBit i.val = true → edge i v = 0 then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa using mask_indicator (fun i => decide (edge i v = 0))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [← Finset.mul_sum, Finset.sum_boole, maskSet]

end A200432Proof

namespace A200432Proof

private theorem rot_mem (n m k : ℕ) (d : Fin 5)
    (hb : ∀ i : Fin 5, k.testBit i.val = m.testBit (i + d).val)
    (v : Fin 5 → ℤ) (hv : v ∈ maskSet n m) :
    (fun i => v (i + d)) ∈ maskSet n k := by
  simp only [maskSet, zeroSet, box, Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
  refine ⟨⟨fun i => hv.1.1 (i + d), ?_⟩, ?_⟩
  · exact (Equiv.sum_comp (Equiv.addRight d) v).trans hv.1.2
  · intro i hi
    have he := hv.2 (i + d) ((hb i).symm.trans hi)
    simpa only [edge, add_right_comm i 1 d] using he

theorem mask_card_rot (n m k : ℕ) (d : Fin 5)
    (hb : ∀ i : Fin 5, k.testBit i.val = m.testBit (i + d).val) :
    (maskSet n m).card = (maskSet n k).card := by
  refine Finset.card_nbij' (fun v i => v (i + d)) (fun v i => v (i + -d))
    (fun v hv => rot_mem n m k d hb v hv) ?_ ?_ ?_
  · intro v hv
    apply rot_mem n k m (-d) _ v hv
    intro i
    simpa [add_assoc] using (hb (i + -d)).symm
  · intro v _
    funext i
    simp [add_assoc]
  · intro v _
    funext i
    simp [add_assoc]

def orbitRep : ℕ → ℕ
  | 0 => 0
  | 1 | 2 | 4 | 8 | 16 => 1
  | 3 | 6 | 12 | 17 | 24 => 3
  | 5 | 9 | 10 | 18 | 20 => 5
  | 7 | 14 | 19 | 25 | 28 => 7
  | 11 | 13 | 21 | 22 | 26 => 11
  | 15 | 23 | 27 | 29 | 30 => 15
  | 31 => 31
  | _ => 0

theorem mask_card_rep (n m : ℕ) (hm : m < 32) :
    (maskSet n m).card = (maskSet n (orbitRep m)).card := by
  have cert : ∀ a : Fin 32, ∃ d : Fin 5, ∀ i : Fin 5,
      (orbitRep a.val).testBit i.val = a.val.testBit (i + d).val := by decide
  obtain ⟨d, hd⟩ := cert ⟨m, hm⟩
  exact mask_card_rot n m (orbitRep m) d hd

end A200432Proof

namespace A200432Proof

private noncomputable def maskInterval (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

private lemma maskInterval_card (n : ℕ) : (maskInterval n).card = 2*n+1 := by
  rw [maskInterval, Int.card_Icc]
  omega

private lemma memMask1 (n : ℕ) (v : Fin 5 → ℤ) :
    v ∈ maskSet n 1 ↔ v ∈ zeroSet 5 n ∧ (v 0 + v 1 = 0) := by
  rw [maskSet, Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact h 0 (by decide)
  · intro h i
    fin_cases i
    · exact fun _ => h
    · exact fun hb => nomatch hb
    · exact fun hb => nomatch hb
    · exact fun hb => nomatch hb
    · exact fun hb => nomatch hb

private lemma memMask3 (n : ℕ) (v : Fin 5 → ℤ) :
    v ∈ maskSet n 3 ↔ v ∈ zeroSet 5 n ∧ (v 0 + v 1 = 0 ∧ v 1 + v 2 = 0) := by
  rw [maskSet, Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide)⟩
  · intro h i
    fin_cases i
    · exact fun _ => h.1
    · exact fun _ => h.2
    · exact fun hb => nomatch hb
    · exact fun hb => nomatch hb
    · exact fun hb => nomatch hb

private lemma memMask5 (n : ℕ) (v : Fin 5 → ℤ) :
    v ∈ maskSet n 5 ↔ v ∈ zeroSet 5 n ∧ (v 0 + v 1 = 0 ∧ v 2 + v 3 = 0) := by
  rw [maskSet, Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 2 (by decide)⟩
  · intro h i
    fin_cases i
    · exact fun _ => h.1
    · exact fun hb => nomatch hb
    · exact fun _ => h.2
    · exact fun hb => nomatch hb
    · exact fun hb => nomatch hb

theorem card_mask_one (n : ℕ) :
    (maskSet n 1).card = (2*n+1) * (zeroSet 3 n).card := by
  rw [← maskInterval_card n, ← Finset.card_product]
  refine Finset.card_nbij' (fun v : Fin 5 → ℤ => (v 0, ![v 2,v 3,v 4]))
    (fun p : ℤ × (Fin 3 → ℤ) => ![p.1,-p.1,p.2 0,p.2 1,p.2 2]) ?_ ?_ ?_ ?_
  · intro v hv
    simp [memMask1, zeroSet, box, maskInterval, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv ⊢
    omega
  · rintro ⟨a,v⟩ hv
    simp [memMask1, zeroSet, box, maskInterval, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv ⊢
    omega
  · intro v hv
    simp [memMask1, zeroSet, box, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv
    funext i
    fin_cases i <;> simp [Fin.isValue]
    omega
  · rintro ⟨a,v⟩ _
    apply Prod.ext
    · rfl
    funext i
    fin_cases i <;> rfl

theorem card_mask_three (n : ℕ) : (maskSet n 3).card = (zeroSet 3 n).card := by
  refine Finset.card_nbij' (fun v : Fin 5 → ℤ => ![v 0,v 3,v 4])
    (fun v : Fin 3 → ℤ => ![v 0,-v 0,v 0,v 1,v 2]) ?_ ?_ ?_ ?_
  · intro v hv
    simp [memMask3, zeroSet, box, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv ⊢
    omega
  · intro v hv
    simp [memMask3, zeroSet, box, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv ⊢
    omega
  · intro v hv
    simp [memMask3, zeroSet, box, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv
    funext i
    fin_cases i <;> simp [Fin.isValue] <;> omega
  · intro v _
    funext i
    fin_cases i <;> rfl

theorem card_mask_five (n : ℕ) : (maskSet n 5).card = (2*n+1)^2 := by
  rw [pow_two, ← maskInterval_card n, ← Finset.card_product]
  refine Finset.card_nbij' (fun v : Fin 5 → ℤ => (v 0, v 2))
    (fun p : ℤ × ℤ => ![p.1,-p.1,p.2,-p.2,0]) ?_ ?_ ?_ ?_
  · intro v hv
    simp [memMask5, zeroSet, box, maskInterval, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv ⊢
    omega
  · rintro ⟨a,b⟩ hv
    simp [memMask5, zeroSet, box, maskInterval, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv ⊢
    omega
  · intro v hv
    simp [memMask5, zeroSet, box, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.isValue] at hv
    funext i
    fin_cases i <;> simp [Fin.isValue] <;> omega
  · intro p _
    rfl

end A200432Proof

namespace A200432Proof

private theorem edge_data {n m : ℕ} {v : Fin 5 → ℤ} (hv : v ∈ maskSet n m) :
    (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧
    v 0 + v 1 + v 2 + v 3 + v 4 = 0 ∧
    ∀ i : Fin 5, m.testBit i.val = true → edge i v = 0 := by
  simp only [maskSet, zeroSet, box, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc] at hv
  exact ⟨hv.1.1, by simpa [Fin.sum_univ_succ, add_assoc] using hv.1.2, hv.2⟩

private theorem edge_intro {n m : ℕ} {v : Fin 5 → ℤ}
    (bounds : ∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n)
    (total : v 0 + v 1 + v 2 + v 3 + v 4 = 0)
    (edges : ∀ i : Fin 5, m.testBit i.val = true → edge i v = 0) : v ∈ maskSet n m := by
  simp only [maskSet, zeroSet, box, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  exact ⟨⟨bounds, by simpa [Fin.sum_univ_succ, add_assoc] using total⟩, edges⟩

private theorem card_mask_line (n m : ℕ) (k : Fin 5) (f : ℤ → Fin 5 → ℤ)
    (surj : ∀ v ∈ maskSet n m, f (v k) = v)
    (fits : ∀ t : ℤ, -(n : ℤ) ≤ t → t ≤ n → f t ∈ maskSet n m)
    (back : ∀ t, f t k = t) : (maskSet n m).card = 2*n+1 := by
  calc
    (maskSet n m).card = (Finset.Icc (-(n : ℤ)) n).card := by
      refine Finset.card_bij' (fun v _ => v k) (fun t _ => f t) ?_ ?_ surj ?_
      · exact fun v hv => Finset.mem_Icc.mpr ((edge_data hv).1 k)
      · intro t ht
        exact fits t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
      · exact fun t _ => back t
    _ = 2*n+1 := by rw [Int.card_Icc]; omega

theorem card_mask_seven (n : ℕ) : (maskSet n 7).card = 2*n+1 := by
  let f (t : ℤ) : Fin 5 → ℤ := ![t,-t,t,-t,0]
  apply card_mask_line n 7 0 f
  · intro v hv
    obtain ⟨_, hz, h⟩ := edge_data hv
    have h0 : v 0 + v 1 = 0 := h 0 (by decide)
    have h1 : v 1 + v 2 = 0 := h 1 (by decide)
    have h2 : v 2 + v 3 = 0 := h 2 (by decide)
    funext i
    fin_cases i <;> simp [f] <;> omega
  · intro t hlo hhi
    apply edge_intro
    · intro i; fin_cases i <;> simp [f] <;> omega
    · simp [f]
    · intro i hi
      fin_cases i
      · change t + -t = 0; omega
      · change -t + t = 0; omega
      · change t + -t = 0; omega
      · exact (by decide : ¬ (7 : ℕ).testBit 3 = true) hi |>.elim
      · exact (by decide : ¬ (7 : ℕ).testBit 4 = true) hi |>.elim
  · intro t; rfl

theorem card_mask_eleven (n : ℕ) : (maskSet n 11).card = 2*n+1 := by
  let f (t : ℤ) : Fin 5 → ℤ := ![0,0,0,t,-t]
  apply card_mask_line n 11 3 f
  · intro v hv
    obtain ⟨_, hz, h⟩ := edge_data hv
    have h0 : v 0 + v 1 = 0 := h 0 (by decide)
    have h1 : v 1 + v 2 = 0 := h 1 (by decide)
    have h3 : v 3 + v 4 = 0 := h 3 (by decide)
    funext i
    fin_cases i <;> simp [f] <;> omega
  · intro t hlo hhi
    apply edge_intro
    · intro i; fin_cases i <;> simp [f] <;> omega
    · simp [f]
    · intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact (by decide : ¬ (11 : ℕ).testBit 2 = true) hi |>.elim
      · change t + -t = 0; omega
      · exact (by decide : ¬ (11 : ℕ).testBit 4 = true) hi |>.elim
  · intro t; rfl

private theorem card_mask_point (n m : ℕ)
    (hbits : ∀ i : Fin 4, m.testBit i.val = true) : (maskSet n m).card = 1 := by
  have heq : maskSet n m = {0} := by
    ext v
    rw [Finset.mem_singleton]
    constructor
    · intro hv
      obtain ⟨_, hz, h⟩ := edge_data hv
      have h0 : v 0 + v 1 = 0 := h 0 (hbits 0)
      have h1 : v 1 + v 2 = 0 := h 1 (hbits 1)
      have h2 : v 2 + v 3 = 0 := h 2 (hbits 2)
      have h3 : v 3 + v 4 = 0 := h 3 (hbits 3)
      funext i; fin_cases i <;> simp <;> omega
    · rintro rfl
      apply edge_intro <;> simp [edge]
  rw [heq, Finset.card_singleton]

theorem card_mask_fifteen (n : ℕ) : (maskSet n 15).card = 1 :=
  card_mask_point n 15 (by decide)

theorem card_mask_thirty_one (n : ℕ) : (maskSet n 31).card = 1 :=
  card_mask_point n 31 (by decide)

end A200432Proof

namespace A200432Proof

private def orbitWeight (k : ℕ) : ℤ :=
  ∑ m ∈ Finset.range 32, if orbitRep m = k then ieCoeff m else 0

private theorem orbit_sum (f : ℕ → ℤ) :
    ∑ m ∈ Finset.range 32, ieCoeff m * f (orbitRep m) =
      f 0 - 5 * f 1 + 5 * f 3 + 5 * f 5 - 5 * f 7 - 5 * f 11 + 5 * f 15 - f 31 := by
  let reps : Finset ℕ := {0, 1, 3, 5, 7, 11, 15, 31}
  have hmem : ∀ i : Fin 32, orbitRep i ∈ reps := by decide +kernel
  have part (m : ℕ) (hm : m ∈ Finset.range 32) :
      ieCoeff m * f (orbitRep m) =
      ∑ k ∈ reps, (if orbitRep m = k then ieCoeff m else 0) * f k := by
    rw [Finset.sum_eq_single_of_mem (orbitRep m) (hmem ⟨m, Finset.mem_range.mp hm⟩)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
  have collapse : ∑ m ∈ Finset.range 32, ieCoeff m * f (orbitRep m) =
      ∑ k ∈ reps, orbitWeight k * f k := by
    calc
      _ = ∑ m ∈ Finset.range 32, ∑ k ∈ reps,
            (if orbitRep m = k then ieCoeff m else 0) * f k := Finset.sum_congr rfl part
      _ = _ := by rw [Finset.sum_comm]; simp only [orbitWeight, Finset.sum_mul]
  have c0 : orbitWeight 0 = 1 := by decide +kernel
  have c1 : orbitWeight 1 = -5 := by decide +kernel
  have c3 : orbitWeight 3 = 5 := by decide +kernel
  have c5 : orbitWeight 5 = 5 := by decide +kernel
  have c7 : orbitWeight 7 = -5 := by decide +kernel
  have c11 : orbitWeight 11 = -5 := by decide +kernel
  have c15 : orbitWeight 15 = 5 := by decide +kernel
  have c31 : orbitWeight 31 = -1 := by decide +kernel
  rw [collapse]
  simp [reps, c0, c1, c3, c5, c7, c11, c15, c31]
  ring

theorem edge_count (n : ℕ) : (OMA.S_oeis_a200432.a n : ℤ) =
    ((zeroSet 5 n).card : ℤ) - 5 * (2*(n:ℤ)+1) * ((zeroSet 3 n).card : ℤ) +
      5 * ((zeroSet 3 n).card : ℤ) + 5 * (2*(n:ℤ)+1)^2 - 10 * (2*(n:ℤ)+1) + 4 := by
  have zeroMask : maskSet n 0 = zeroSet 5 n := by ext v; simp [maskSet]
  calc
    _ = ∑ m ∈ Finset.range 32, ieCoeff m * ((maskSet n (orbitRep m)).card : ℤ) := by
      rw [inclusion]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [mask_card_rep n m (Finset.mem_range.mp hm)]
    _ = _ := by
      rw [orbit_sum (fun m => ((maskSet n m).card : ℤ))]
      simp only [zeroMask, card_mask_one, card_mask_three, card_mask_five, card_mask_seven,
        card_mask_eleven, card_mask_fifteen, card_mask_thirty_one, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
      ring

end A200432Proof

namespace OMA.A200432Count

open PowerSeries

/-- Translate the integer interval into exponents starting at zero. -/
lemma interval_series (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1), (X : PowerSeries ℤ) ^ j) =
      ∑ z ∈ Finset.Icc (-(n : ℤ)) n, (X : PowerSeries ℤ) ^ (z + n).toNat := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have h : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  omega

/-- The total of the translated entries equals `k*n` precisely when the original sum is zero. -/
lemma zero_count_coeff (k n : ℕ) :
    (((Fintype.piFinset fun _ : Fin k => Finset.Icc (-(n : ℤ)) n).filter
        (fun v => ∑ i, v i = 0)).card : ℤ) =
      coeff (k * n) ((∑ j ∈ Finset.range (2*n+1), (X : PowerSeries ℤ)^j)^k) := by
  classical
  rw [interval_series, Finset.sum_pow', map_sum, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.prod_pow_eq_pow_sum, coeff_X_pow]
  have he : (∑ i, ((v i + n).toNat : ℤ)) = ∑ i, v i + (k : ℤ) * n := by
    calc
      _ = ∑ i, (v i + n) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv i)).1
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hp : (∑ i, v i = 0) ↔ k*n = ∑ i, (v i + n).toNat := by
    constructor
    · intro h
      exact_mod_cast (show (k : ℤ)*n = (∑ i, ((v i+n).toNat : ℤ)) by omega)
    · intro h
      have hh : (k : ℤ)*n = (∑ i, ((v i+n).toNat : ℤ)) := by exact_mod_cast h
      omega
  by_cases h : ∑ i, v i = 0
  · simp only [if_pos h, if_pos (hp.mp h)]
  · simp only [if_neg h, if_neg (fun h' => h (hp.mpr h'))]

/-- Coefficients of the bounded five-coordinate box, before imposing edge conditions. -/
theorem geom_coeff (n : ℕ) :
    coeff (R := ℤ) (5 * n) ((∑ j ∈ Finset.range (2 * n + 1), (X : PowerSeries ℤ) ^ j) ^ 5) =
      (Nat.choose (5 * n + 4) 4 : ℤ) - 5 * (Nat.choose (3 * n + 3) 4 : ℤ) +
        10 * (Nat.choose (n + 2) 4 : ℤ) := by
  let k := 2 * n + 1
  let F : PowerSeries ℤ := mk fun m => (Nat.choose (4 + m) 4 : ℤ)
  let G : PowerSeries ℤ := ∑ j ∈ Finset.range k, X ^ j
  have hF : F * (1 - X) ^ 5 = 1 := mk_add_choose_mul_one_sub_pow_eq_one ℤ 4
  have hG : G * (1 - X) = 1 - X ^ k := geom_sum_mul_neg X k
  have hnum : G ^ 5 = F * (1 - X ^ k) ^ 5 := by
    rw [← hG, mul_pow]
    calc G ^ 5 = G ^ 5 * (F * (1 - X) ^ 5) := by rw [hF, mul_one]
         _ = _ := by ring
  have hshift (t : ℕ) : coeff (5 * n) (F * X ^ t) = (Nat.choose (5 * n + 4 - t) 4 : ℤ) := by
    rw [coeff_mul_X_pow']
    split_ifs with h
    · simp only [F, coeff_mk]
      rw [show 4 + (5 * n - t) = 5 * n + 4 - t by omega]
    · rw [Nat.choose_eq_zero_of_lt (by omega : 5 * n + 4 - t < 4)]
      simp
  have hexpand : F * (1 - X ^ k) ^ 5 =
      F - 5 • (F * X ^ k) + 10 • (F * X ^ (k * 2)) - 10 • (F * X ^ (k * 3)) +
      5 • (F * X ^ (k * 4)) - F * X ^ (k * 5) := by
    simp only [pow_mul, nsmul_eq_mul]
    ring
  change coeff (5 * n) (G ^ 5) = _
  rw [hnum, hexpand]
  simp only [map_sub, map_add, map_nsmul, hshift]
  simp only [F, coeff_mk, nsmul_eq_mul]
  rw [show 4 + 5*n = 5*n+4 by omega,
      show 5*n+4-k = 3*n+3 by dsimp [k]; omega,
      show 5*n+4-k*2 = n+2 by dsimp [k]; omega]
  rw [Nat.choose_eq_zero_of_lt (by dsimp [k]; omega : 5*n+4-k*3 < 4),
      Nat.choose_eq_zero_of_lt (by dsimp [k]; omega : 5*n+4-k*4 < 4),
      Nat.choose_eq_zero_of_lt (by dsimp [k]; omega : 5*n+4-k*5 < 4)]
  simp

/-- The zero-sum five-tuples in the box, before excluding adjacent pairs. -/
theorem total_zero (n : ℕ) :
    (((Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter
        (fun v => ∑ i, v i = 0)).card : ℤ) =
      (Nat.choose (5*n+4) 4 : ℤ) - 5 * (Nat.choose (3*n+3) 4 : ℤ) +
        10 * (Nat.choose (n+2) 4 : ℤ) :=
  (zero_count_coeff 5 n).trans (geom_coeff n)

end OMA.A200432Count

namespace A200432Proof

open PowerSeries

theorem boxPower_series (l d : ℕ) :
    (∑ j ∈ Finset.range l, (X : PowerSeries ℤ) ^ j) ^ (d + 1) =
      (mk fun t => (Nat.choose (d + t) d : ℤ)) * (1 - X ^ l) ^ (d + 1) := by
  let s := ∑ j ∈ Finset.range l, (X : PowerSeries ℤ) ^ j
  have h : s = (mk 1 : PowerSeries ℤ) * (1 - X ^ l) := calc
    s = s * ((mk 1 : PowerSeries ℤ) * (1 - X)) := by rw [mk_one_mul_one_sub_eq_one, mul_one]
    _ = (mk 1 : PowerSeries ℤ) * (s * (1 - X)) := by ring
    _ = _ := by rw [show s * (1 - X) = 1 - X ^ l from geom_sum_mul_neg _ _]
  change s ^ (d + 1) = _
  rw [h, mul_pow, mk_one_pow_eq_mk_choose_add]

theorem boxPower_three (n : ℕ) :
    coeff (3 * n) ((∑ j ∈ Finset.range (2*n+1), (X : PowerSeries ℤ)^j)^3) =
      3*(n:ℤ)^2 + 3*(n:ℤ) + 1 := by
  rw [boxPower_series (2*n+1) 2]
  let p := mk fun t => (Nat.choose (2 + t) 2 : ℤ)
  let l := 2*n+1
  change coeff (3*n) (p * (1 - X^l)^3) = _
  rw [show p * (1-X^l)^3 = p - 3 • (p * X^l) + 3 • (p * X^(l*2)) - p * X^(l*3) by
    simp only [nsmul_eq_mul, pow_mul]; ring]
  simp only [map_sub, map_add, map_nsmul, coeff_mul_X_pow', p, coeff_mk]
  cases n with
  | zero => norm_num [l]
  | succ k =>
    simp (disch := dsimp [l]; omega) only [if_neg, if_pos, nsmul_zero, add_zero, sub_zero]
    have hsub : 3 * (k + 1) - l = k := by dsimp [l]; omega
    rw [hsub, nsmul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    ring

end A200432Proof

namespace A200432Proof

lemma choose_four_rational (k : ℕ) :
    (k.choose 4 : ℚ) = (k : ℚ) * (k - 1 : ℚ) * (k - 2 : ℚ) * (k - 3 : ℚ) / 24 := by
  have polys (n : ℕ) :
      (n.choose 2 : ℚ) = (n : ℚ) * (n - 1 : ℚ) / 2 ∧
      (n.choose 3 : ℚ) = (n : ℚ) * (n - 1 : ℚ) * (n - 2 : ℚ) / 6 ∧
      (n.choose 4 : ℚ) = (n : ℚ) * (n - 1 : ℚ) * (n - 2 : ℚ) * (n - 3 : ℚ) / 24 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rcases ih with ⟨h₂, h₃, h₄⟩
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [Nat.choose_succ_succ, Nat.cast_add, h₂, h₃, h₄] <;> ring
  exact (polys k).2.2

theorem polynomial_from_counts (n a b t : ℕ)
    (ha : (a : ℤ) = (b : ℤ) - 5*(2*(n : ℤ)+1)*(t : ℤ) + 5*(t : ℤ) +
      5*(2*(n : ℤ)+1)^2 - 10*(2*(n : ℤ)+1) + 4)
    (hb : (b : ℤ) = ((5*n+4).choose 4 : ℤ) - 5*((3*n+3).choose 4 : ℤ) +
      10*((n+2).choose 4 : ℤ))
    (ht : (t : ℤ) = 3*(n : ℤ)^2 + 3*(n : ℤ) + 1) :
    (a : ℚ) = (115*(n : ℚ)^4 - 130*(n : ℚ)^3 + 65*(n : ℚ)^2 - 50*(n : ℚ))/12 := by
  rw [hb, ht] at ha
  have hq := congrArg (fun z : ℤ => (z : ℚ)) ha
  push_cast at hq
  simp only [choose_four_rational] at hq
  push_cast at hq
  rw [hq]
  ring

end A200432Proof

namespace OMA.A200432

open PowerSeries

/-- The fifth finite difference of the proposed counting polynomial gives the numerator. -/
theorem series_of_polynomial (s : ℕ → ℕ)
    (hs : ∀ n : ℕ, (s n : ℚ) =
      (115 * (n : ℚ) ^ 4 - 130 * (n : ℚ) ^ 3 + 65 * (n : ℚ) ^ 2 - 50 * (n : ℚ)) / 12) :
    (PowerSeries.mk fun n => (s n : ℚ)) * (1 - X) ^ 5 =
      10 * X ^ 2 * (8 + 12 * X + 3 * X ^ 2) := by
  let p := PowerSeries.mk fun n => (s n : ℚ)
  change p * (1 - X) ^ 5 = _
  rw [show p * (1 - X) ^ 5 =
      p - 5 • (p * X ^ 1) + 10 • (p * X ^ 2) - 10 • (p * X ^ 3) +
        5 • (p * X ^ 4) - p * X ^ 5 by simp only [nsmul_eq_mul]; ring]
  rw [show (10 : PowerSeries ℚ) * X ^ 2 * (8 + 12 * X + 3 * X ^ 2) =
      80 • (X ^ 2 : PowerSeries ℚ) + 120 • X ^ 3 + 30 • X ^ 4 by
        simp only [nsmul_eq_mul]; ring]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, p, coeff_mk, hs]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num
  · simp (disch := omega) only [if_pos, if_neg, Nat.cast_sub, Nat.cast_ofNat, nsmul_eq_mul]
    ring

end OMA.A200432

theorem OMA.solution : type_of% @OMA.S_oeis_a200432.main := by
  apply OMA.A200432.series_of_polynomial
  intro n
  apply A200432Proof.polynomial_from_counts n (OMA.S_oeis_a200432.a n)
    (A200432Proof.zeroSet 5 n).card (A200432Proof.zeroSet 3 n).card
  · exact A200432Proof.edge_count n
  · exact OMA.A200432Count.total_zero n
  · exact (OMA.A200432Count.zero_count_coeff 3 n).trans (A200432Proof.boxPower_three n)
