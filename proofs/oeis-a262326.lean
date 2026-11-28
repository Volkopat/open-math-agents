import OMAStatements.S_oeis_a262326

-- Problem: OEIS A262326: binary rectangles with every row and column divisible by three
-- Credit: @ceejcake
-- Proof:
-- 1. Classify the 3 valid 3-bit rows divisible by 3: `000`, `011`, `110`.
-- 2. In every valid row, bit 1 = bit 0 + bit 2, so column 1 equals column 0 + column 2;
--    thus 3 ∣ col0 ∧ 3 ∣ col2 automatically implies 3 ∣ col1.
-- 3. Define `cnt h (x, y)` = number of h-row arrays of valid rows whose (col0, col2) mod 3 is (x, y).
--    Prove the 3-term transition recurrence `cnt (h+1) (x, y) = cnt h (2x, 2y) + cnt h (2x, 2(y-1)) + cnt h (2(x-1), 2y)`.
-- 4. By induction on k, prove the exact closed forms for all 9 states at h = 2k+2 and h = 2k+3,
--    specializing to (0, 0) to obtain both parity formulas and the rational generating function.

namespace ProofA262326

open OMA.S_oeis_a262326 PowerSeries

private def row0 : Row := ⟨fun _ => false, by decide⟩
private def row1 : Row := ⟨fun j => decide (j.1 ≠ 0), by decide⟩
private def row2 : Row := ⟨fun j => decide (j.1 ≠ 2), by decide⟩

private def rowOfFin : Fin 3 → Row
  | 0 => row0
  | 1 => row1
  | 2 => row2

private def finOfRow (r : Row) : Fin 3 :=
  if r.1 0 then 2 else if r.1 2 then 1 else 0

private lemma row_mid_eq : ∀ (f : Fin 3 → Bool), 3 ∣ binaryValue f →
    (if f 1 then (1 : ℕ) else 0) = (if f 0 then 1 else 0) + (if f 2 then 1 else 0) := by
  decide

private lemma row_classify : ∀ (f : Fin 3 → Bool), 3 ∣ binaryValue f →
    (f = row0.1 ∧ ¬ f 0 ∧ ¬ f 2) ∨
    (f = row1.1 ∧ ¬ f 0 ∧ f 2) ∨
    (f = row2.1 ∧ f 0 ∧ ¬ f 2) := by
  decide

private def rowEquiv : Row ≃ Fin 3 where
  toFun := finOfRow
  invFun := rowOfFin
  left_inv r := by
    rcases row_classify r.1 r.2 with ⟨heq, h0, h2⟩ | ⟨heq, h0, h2⟩ | ⟨heq, h0, h2⟩
    · apply Subtype.ext; simp [finOfRow, h0, h2, rowOfFin, heq]
    · apply Subtype.ext; simp [finOfRow, h0, h2, rowOfFin, heq]
    · apply Subtype.ext; simp [finOfRow, h0, rowOfFin, heq]
  right_inv i := by
    fin_cases i <;> decide

private lemma col1_eq_add : ∀ {h : ℕ} (r : Fin h → Row),
    binaryValue (fun i => (r i).1 1) =
      binaryValue (fun i => (r i).1 0) + binaryValue (fun i => (r i).1 2) := by
  intro h
  induction h with
  | zero => intro r; rfl
  | succ h ih =>
    intro r
    simp only [binaryValue]
    rw [ih (fun i => r i.castSucc), row_mid_eq (r (Fin.last h)).1 (r (Fin.last h)).2]
    ring

private def colState {h : ℕ} (r : Fin h → Row) : ZMod 3 × ZMod 3 :=
  ((binaryValue (fun i => (r i).1 0) : ZMod 3), (binaryValue (fun i => (r i).1 2) : ZMod 3))

private lemma valid_iff_state {h : ℕ} (r : Fin h → Row) :
    (∀ j : Fin 3, 3 ∣ binaryValue (fun i => (r i).1 j)) ↔ colState r = (0, 0) := by
  constructor
  · intro hj
    have h0 := hj 0
    have h2 := hj 2
    ext
    · exact (ZMod.natCast_eq_zero_iff _ 3).mpr h0
    · exact (ZMod.natCast_eq_zero_iff _ 3).mpr h2
  · intro hs j
    have h0 : 3 ∣ binaryValue (fun i => (r i).1 0) :=
      (ZMod.natCast_eq_zero_iff _ 3).mp (congr_arg Prod.fst hs)
    have h2 : 3 ∣ binaryValue (fun i => (r i).1 2) :=
      (ZMod.natCast_eq_zero_iff _ 3).mp (congr_arg Prod.snd hs)
    fin_cases j
    · exact h0
    · change 3 ∣ binaryValue (fun i => (r i).1 1); rw [col1_eq_add r]; exact dvd_add h0 h2
    · exact h2

private def cnt (h : ℕ) (s : ZMod 3 × ZMod 3) : ℕ :=
  Fintype.card {r : Fin h → Row // colState r = s}

private lemma a_eq_cnt (n : ℕ) : a n = cnt (n + 1) (0, 0) := by
  unfold a cnt
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun r => valid_iff_state r)

private def prevState (t : Fin 3) (s : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  match t with
  | 0 => (2 * s.1, 2 * s.2)
  | 1 => (2 * s.1, 2 * (s.2 - 1))
  | 2 => (2 * (s.1 - 1), 2 * s.2)

private lemma rowOfFin_bits (t : Fin 3) :
    (if (rowOfFin t).1 0 then (1 : ZMod 3) else 0) = (if t = 2 then 1 else 0) ∧
    (if (rowOfFin t).1 2 then (1 : ZMod 3) else 0) = (if t = 1 then 1 else 0) := by
  fin_cases t <;> decide

private lemma colState_snoc {h : ℕ} (r : Fin h → Row) (t : Fin 3) :
    colState (Fin.snoc (α := fun _ => Row) r (rowOfFin t)) =
      (2 * (colState r).1 + (if t = 2 then 1 else 0),
       2 * (colState r).2 + (if t = 1 then 1 else 0)) := by
  have hcast : ∀ j : Fin 3,
      (fun i : Fin h => (Fin.snoc (α := fun _ => Row) r (rowOfFin t) i.castSucc).1 j) = (fun i => (r i).1 j) := by
    intro j; funext i; simp [Fin.snoc_castSucc]
  have hlast : ∀ j : Fin 3, (Fin.snoc (α := fun _ => Row) r (rowOfFin t) (Fin.last h)).1 j = (rowOfFin t).1 j := by
    intro j; simp [Fin.snoc_last]
  unfold colState
  simp only [binaryValue, hcast, hlast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  fin_cases t <;> simp [rowOfFin, row0, row1, row2]

private lemma step_iff_prev (t : Fin 3) (u s : ZMod 3 × ZMod 3) :
    (2 * u.1 + (if t = 2 then 1 else 0), 2 * u.2 + (if t = 1 then 1 else 0)) = s ↔
      u = prevState t s := by
  rcases u with ⟨u1, u2⟩
  rcases s with ⟨s1, s2⟩
  fin_cases t <;> fin_cases u1 <;> fin_cases u2 <;> fin_cases s1 <;> fin_cases s2 <;> decide

private lemma cnt_zero (s : ZMod 3 × ZMod 3) : cnt 0 s = if s = (0, 0) then 1 else 0 := by
  unfold cnt
  by_cases hs : s = (0, 0)
  · subst hs
    have : Unique {r : Fin 0 → Row // colState r = (0, 0)} :=
      { default := ⟨Fin.elim0, rfl⟩
        uniq := fun ⟨r, _⟩ => Subtype.ext (funext fun i => i.elim0) }
    simp [Fintype.card_unique]
  · simp only [hs, ↓reduceIte]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨r, hr⟩ => hs (by rw [← hr]; rfl)⟩

private lemma cnt_succ (h : ℕ) (s : ZMod 3 × ZMod 3) :
    cnt (h + 1) s = cnt h (2 * s.1, 2 * s.2) + cnt h (2 * s.1, 2 * (s.2 - 1)) + cnt h (2 * (s.1 - 1), 2 * s.2) := by
  unfold cnt
  let e : {r : Fin (h + 1) → Row // colState r = s} ≃
      Σ t : Fin 3, {r' : Fin h → Row // colState r' = prevState t s} :=
    { toFun := fun ⟨r, hr⟩ =>
        ⟨rowEquiv (r (Fin.last h)), ⟨fun i => r i.castSucc, by
          have hsnoc : Fin.snoc (α := fun _ => Row) (fun i : Fin h => r i.castSucc) (rowOfFin (rowEquiv (r (Fin.last h)))) = r := by
            have hinv : rowOfFin (rowEquiv (r (Fin.last h))) = r (Fin.last h) := rowEquiv.left_inv _
            rw [hinv]
            exact Fin.snoc_init_self r
          rw [← hsnoc, colState_snoc] at hr
          exact (step_iff_prev _ _ _).mp hr⟩⟩
      invFun := fun ⟨t, ⟨r', hr'⟩⟩ =>
        ⟨Fin.snoc (α := fun _ => Row) r' (rowOfFin t), by
          rw [colState_snoc]
          exact (step_iff_prev _ _ _).mpr hr'⟩
      left_inv := fun ⟨r, _⟩ => by
        apply Subtype.ext
        dsimp only
        have hinv : rowOfFin (rowEquiv (r (Fin.last h))) = r (Fin.last h) := rowEquiv.left_inv _
        rw [hinv]
        exact Fin.snoc_init_self r
      right_inv := fun ⟨t, ⟨r', _⟩⟩ => by
        have ht : rowEquiv (Fin.snoc (α := fun _ => Row) r' (rowOfFin t) (Fin.last h)) = t := by
          rw [Fin.snoc_last]; exact rowEquiv.right_inv t
        refine Sigma.ext ht ?_
        dsimp only
        rw [Subtype.heq_iff_coe_eq (fun _ => by rw [ht])]
        funext i
        simp [Fin.snoc_castSucc] }
  rw [Fintype.card_congr e, Fintype.card_sigma, Fin.sum_univ_three]
  rfl

private def evenForm (k : ℕ) (s : ZMod 3 × ZMod 3) : ℕ :=
  if s = (0, 0) then 3 ^ (2 * k) + 2 * 3 ^ k
  else if s = (1, 1) ∨ s = (2, 2) then 3 ^ (2 * k) - 3 ^ k
  else 3 ^ (2 * k)

private def oddForm (k : ℕ) (s : ZMod 3 × ZMod 3) : ℕ :=
  if s = (0, 0) ∨ s = (1, 0) ∨ s = (0, 1) then 3 ^ (2 * k + 1) + 2 * 3 ^ k
  else 3 ^ (2 * k + 1) - 3 ^ k

private lemma pow3_le_sq (k : ℕ) : 3 ^ k ≤ 3 ^ (2 * k) :=
  Nat.pow_le_pow_right (by omega) (by omega)

private lemma cnt_even_odd (k : ℕ) :
    (∀ s, cnt (2 * k + 2) s = evenForm k s) ∧ (∀ s, cnt (2 * k + 3) s = oddForm k s) := by
  induction k with
  | zero =>
    have h2 : ∀ s, cnt 2 s = evenForm 0 s := by
      intro ⟨x, y⟩
      rw [cnt_succ, cnt_succ, cnt_succ, cnt_succ]
      simp only [cnt_zero, evenForm]
      fin_cases x <;> fin_cases y <;> decide
    refine ⟨h2, ?_⟩
    intro ⟨x, y⟩
    rw [cnt_succ]
    simp only [h2, evenForm, oddForm]
    fin_cases x <;> fin_cases y <;> decide
  | succ k ih =>
    rcases ih with ⟨_, hodd⟩
    have hle : 3 ^ k ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : ∀ s, cnt (2 * (k + 1) + 2) s = evenForm (k + 1) s := by
      intro ⟨x, y⟩
      have heq : 2 * (k + 1) + 2 = (2 * k + 3) + 1 := by omega
      rw [heq, cnt_succ]
      simp only [hodd, oddForm, evenForm]
      have hp1 : 3 ^ (2 * (k + 1)) = 3 * 3 ^ (2 * k + 1) := by ring
      have hp2 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      fin_cases x <;> fin_cases y <;> simp +decide <;> omega
    refine ⟨h2, ?_⟩
    intro ⟨x, y⟩
    have heq : 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 := by omega
    rw [heq, cnt_succ]
    simp only [h2, evenForm, oddForm]
    have hle2 : 3 ^ (k + 1) ≤ 3 ^ (2 * (k + 1)) := pow3_le_sq (k + 1)
    have hp1 : 3 ^ (2 * (k + 1) + 1) = 3 * 3 ^ (2 * (k + 1)) := by ring
    fin_cases x <;> fin_cases y <;> simp +decide <;> omega

private lemma a_even (n : ℕ) (hn : 1 ≤ n) (he : n % 2 = 0) :
    a n = 2 * 3 ^ (n / 2 - 1) + 3 ^ (n - 1) := by
  let k := n / 2 - 1
  have hnk : n + 1 = 2 * k + 3 := by omega
  have he1 : n - 1 = 2 * k + 1 := by omega
  have he2 : n / 2 - 1 = k := rfl
  rw [a_eq_cnt, hnk, (cnt_even_odd k).2 (0, 0), he2, he1]
  simp only [oddForm, true_or, ↓reduceIte]
  ring

private lemma a_odd (n : ℕ) (hn : 1 ≤ n) (ho : n % 2 = 1) :
    a n = 2 * 3 ^ ((n - 1) / 2) + 3 ^ (n - 1) := by
  let k := (n - 1) / 2
  have hnk : n + 1 = 2 * k + 2 := by omega
  have he1 : n - 1 = 2 * k := by omega
  have he2 : (n - 1) / 2 = k := rfl
  rw [a_eq_cnt, hnk, (cnt_even_odd k).1 (0, 0), he2, he1]
  simp only [evenForm, ↓reduceIte]
  ring

private lemma a_rec (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) - 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + 9 * (a (n - 3) : ℤ) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have h0 := a_even n (by omega) he
    have h1 := a_odd (n - 1) (by omega) (by omega)
    have h2 := a_even (n - 2) (by omega) (by omega)
    have h3 := a_odd (n - 3) (by omega) (by omega)
    let k := n / 2 - 2
    have e0 : n / 2 - 1 = k + 1 := by omega
    have e1 : (n - 1 - 1) / 2 = k + 1 := by omega
    have e2 : (n - 2) / 2 - 1 = k := by omega
    have e3 : (n - 3 - 1) / 2 = k := by omega
    have f0 : n - 1 = 2 * k + 3 := by omega
    have f1 : n - 1 - 1 = 2 * k + 2 := by omega
    have f2 : n - 2 - 1 = 2 * k + 1 := by omega
    have f3 : n - 3 - 1 = 2 * k := by omega
    rw [h0, h1, h2, h3, e1, e2, e3, e0, f1, f2, f3, f0]
    push_cast; ring
  · have h0 := a_odd n (by omega) ho
    have h1 := a_even (n - 1) (by omega) (by omega)
    have h2 := a_odd (n - 2) (by omega) (by omega)
    have h3 := a_even (n - 3) (by omega) (by omega)
    let k := (n - 5) / 2
    have e0 : (n - 1) / 2 = k + 2 := by omega
    have e1 : (n - 1) / 2 - 1 = k + 1 := by omega
    have e2 : (n - 2 - 1) / 2 = k + 1 := by omega
    have e3 : (n - 3) / 2 - 1 = k := by omega
    have f0 : n - 1 = 2 * k + 4 := by omega
    have f1 : n - 1 - 1 = 2 * k + 3 := by omega
    have f2 : n - 2 - 1 = 2 * k + 2 := by omega
    have f3 : n - 3 - 1 = 2 * k + 1 := by omega
    rw [h0, h1, h2, h3, e1, e2, e3, e0, f1, f2, f3, f0]
    push_cast; ring

private lemma a_base : a 1 = 3 ∧ a 2 = 5 ∧ a 3 = 15 := by
  refine ⟨?_, ?_, ?_⟩
  · have := a_odd 1 (by omega) (by omega); norm_num at this; exact this
  · have := a_even 2 (by omega) (by omega); norm_num at this; exact this
  · have := a_odd 3 (by omega) (by omega); norm_num at this; exact this

private lemma gf_eq :
    (1 - C 3 * X) * (1 - C 3 * X ^ 2) * generatingSeries =
      X * (C 3 - C 4 * X - C 9 * X ^ 2) := by
  have hlhs_exp : (1 - C 3 * X) * (1 - C 3 * X ^ 2) * generatingSeries =
      generatingSeries - (3 : ℤ) • (X * generatingSeries) -
        (3 : ℤ) • (X ^ 2 * generatingSeries) + (9 : ℤ) • (X ^ 3 * generatingSeries) := by
    have hC3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
    rw [hC3]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    ring
  have hrhs_exp : (X * (C 3 - C 4 * X - C 9 * X ^ 2) : PowerSeries ℤ) =
      (3 : ℤ) • X - (4 : ℤ) • X ^ 2 - (9 : ℤ) • X ^ 3 := by
    have hC3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
    have hC4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
    have hC9 : (C (9 : ℤ) : PowerSeries ℤ) = 9 := map_ofNat C 9
    rw [hC3, hC4, hC9]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    ring
  rw [hlhs_exp, hrhs_exp]
  ext n
  have hX1 : (PowerSeries.coeff n) (X * generatingSeries) =
      if 1 ≤ n then (PowerSeries.coeff (n - 1)) generatingSeries else 0 := by
    have h1 : X * generatingSeries = X ^ 1 * generatingSeries := by simp
    rw [h1, PowerSeries.coeff_X_pow_mul']
  have hXk : ∀ k : ℕ, (PowerSeries.coeff n) (X ^ k * generatingSeries) =
      if k ≤ n then (PowerSeries.coeff (n - k)) generatingSeries else 0 := by
    intro k; simp [PowerSeries.coeff_X_pow_mul']
  have hX1' : (PowerSeries.coeff n) (X : PowerSeries ℤ) = if n = 1 then 1 else 0 := by
    simp [PowerSeries.coeff_X]
  have hXk' : ∀ k : ℕ, (PowerSeries.coeff n) (X ^ k : PowerSeries ℤ) = if n = k then 1 else 0 := by
    intro k; simp [PowerSeries.coeff_X_pow]
  simp only [map_sub, map_add, map_zsmul]
  rw [hX1, hXk 2, hXk 3]
  simp only [zsmul_eq_mul, Int.cast_id, hX1', hXk', generatingSeries, PowerSeries.coeff_mk]
  rcases a_base with ⟨h1, h2, h3⟩
  by_cases hn : 4 ≤ n
  · have hrec := a_rec n hn
    have hne : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n - 1 ≠ 0 ∧ n - 2 ≠ 0 ∧ n - 3 ≠ 0 := by omega
    have hge : 1 ≤ n ∧ 2 ≤ n ∧ 3 ≤ n := by omega
    simp only [hne, hge, ↓reduceIte]
    omega
  · interval_cases n <;> simp [h1, h2, h3]

end ProofA262326

theorem OMA.solution : type_of% @OMA.S_oeis_a262326.main :=
  ⟨ProofA262326.a_even, ProofA262326.a_odd, ProofA262326.gf_eq⟩
