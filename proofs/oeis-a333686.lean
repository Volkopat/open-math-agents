import OMAStatements.S_oeis_a333686

section Proof

open PowerSeries

/-! Part 1: 5x5 Transfer Matrix Algebra and Generating Function -/

private def T : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![1,1,1,0,1], ![1,1,1,0,0], ![1,1,1,1,0], ![1,0,0,1,0], ![0,0,1,0,1]]

private def M_mid : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![0,1,1,0,1], ![1,1,1,0,0], ![1,1,0,1,0], ![1,0,0,1,0], ![0,0,1,0,1]]

private def L (X : Matrix (Fin 5) (Fin 5) ℤ) : Matrix (Fin 5) (Fin 5) ℤ := T * X * T

private def B (n : ℕ) : Matrix (Fin 5) (Fin 5) ℤ := (L^[n]) M_mid

private lemma B_eq_pow (n : ℕ) : B n = T ^ n * M_mid * T ^ n := by
  induction n with
  | zero => simp [B]
  | succ n ih =>
    rw [B, Function.iterate_succ_apply', ← B, ih, L]
    have h1 : T * (T ^ n * M_mid * T ^ n) * T = (T * T ^ n) * M_mid * (T ^ n * T) := by
      simp only [Matrix.mul_assoc]
    rw [h1, ← pow_succ', ← pow_succ]

private lemma L_add (X Y : Matrix (Fin 5) (Fin 5) ℤ) : L (X + Y) = L X + L Y := by
  simp [L, Matrix.mul_add, Matrix.add_mul]

private lemma L_sub (X Y : Matrix (Fin 5) (Fin 5) ℤ) : L (X - Y) = L X - L Y := by
  simp [L, Matrix.mul_sub, Matrix.sub_mul]

private lemma L_smul (c : ℤ) (X : Matrix (Fin 5) (Fin 5) ℤ) : L (c • X) = c • L X := by
  unfold L
  rw [Matrix.mul_smul, Matrix.smul_mul]

private lemma L_iter_add (n : ℕ) (X Y : Matrix (Fin 5) (Fin 5) ℤ) :
    (L^[n]) (X + Y) = (L^[n]) X + (L^[n]) Y := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, L_add, ih]

private lemma L_iter_sub (n : ℕ) (X Y : Matrix (Fin 5) (Fin 5) ℤ) :
    (L^[n]) (X - Y) = (L^[n]) X - (L^[n]) Y := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, L_sub, ih]

private lemma L_iter_smul (n : ℕ) (c : ℤ) (X : Matrix (Fin 5) (Fin 5) ℤ) :
    (L^[n]) (c • X) = c • (L^[n]) X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, L_smul, ih]

private lemma L_rec0 :
    (L^[6]) M_mid =
      (10 : ℤ) • (L^[5]) M_mid + (10 : ℤ) • (L^[4]) M_mid -
        (10 : ℤ) • (L^[2]) M_mid - (10 : ℤ) • (L^[1]) M_mid + M_mid := by
  decide

private lemma B_rec (n : ℕ) :
    B (n + 6) =
      (10 : ℤ) • B (n + 5) + (10 : ℤ) • B (n + 4) -
        (10 : ℤ) • B (n + 2) - (10 : ℤ) • B (n + 1) + B n := by
  have h := congrArg (L^[n]) L_rec0
  simp only [L_iter_add, L_iter_sub, L_iter_smul, ← Function.iterate_add_apply] at h
  simp only [B]
  simpa [Nat.add_comm] using h

private def b (n : ℕ) : ℤ := B n 0 2

private lemma b_rec (n : ℕ) :
    b (n + 6) = 10 * b (n + 5) + 10 * b (n + 4) - 10 * b (n + 2) - 10 * b (n + 1) + b n := by
  have h := congrFun (congrFun (B_rec n) 0) 2
  simp only [b, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
  exact h

private lemma b_init :
    [b 0, b 1, b 2, b 3, b 4, b 5] = [1, 10, 101, 1105, 12046, 131399] := by
  decide

private lemma coeff_zero_mul_X_pow (f : PowerSeries ℤ) (k : ℕ) :
    coeff 0 (f * X ^ (k + 1)) = 0 := by
  rw [pow_succ, ← mul_assoc, PowerSeries.coeff_zero_mul_X]

private lemma coeff_succ_mul_X_pow (f : PowerSeries ℤ) (m k : ℕ) :
    coeff (m + 1) (f * X ^ (k + 1)) = coeff m (f * X ^ k) := by
  rw [pow_succ, ← mul_assoc, coeff_succ_mul_X]

private lemma b_ogf :
    (let x : PowerSeries ℤ := X
     PowerSeries.mk b * ((1 - x) * (1 + x) * (1 + x + x ^ 2) * (1 - 11 * x + x ^ 2)) =
       (1 - 3 * x - x ^ 2) * (1 + 3 * x + x ^ 2 + x ^ 3)) := by
  dsimp only
  have hD :
      (1 - (X : PowerSeries ℤ)) * (1 + X) * (1 + X + X ^ 2) * (1 - 11 * X + X ^ 2) =
        1 - C 10 * X - C 10 * X ^ 2 + C 10 * X ^ 4 + C 10 * X ^ 5 - X ^ 6 := by
    have h10 : (10 : PowerSeries ℤ) = C 10 := (map_ofNat (C : ℤ →+* PowerSeries ℤ) 10).symm
    rw [← h10]
    ring
  have hN :
      (1 - 3 * (X : PowerSeries ℤ) - X ^ 2) * (1 + 3 * X + X ^ 2 + X ^ 3) =
        1 - C 9 * X ^ 2 - C 5 * X ^ 3 - C 4 * X ^ 4 - X ^ 5 := by
    have h9 : (9 : PowerSeries ℤ) = C 9 := (map_ofNat (C : ℤ →+* PowerSeries ℤ) 9).symm
    have h5 : (5 : PowerSeries ℤ) = C 5 := (map_ofNat (C : ℤ →+* PowerSeries ℤ) 5).symm
    have h4 : (4 : PowerSeries ℤ) = C 4 := (map_ofNat (C : ℤ →+* PowerSeries ℤ) 4).symm
    rw [← h9, ← h5, ← h4]
    ring
  rw [hD, hN]
  have hmulD :
      PowerSeries.mk b *
          (1 - C 10 * X - C 10 * X ^ 2 + C 10 * X ^ 4 + C 10 * X ^ 5 - X ^ 6) =
        PowerSeries.mk b - (PowerSeries.mk b * C 10) * X - (PowerSeries.mk b * C 10) * X ^ 2 +
          (PowerSeries.mk b * C 10) * X ^ 4 + (PowerSeries.mk b * C 10) * X ^ 5 -
          PowerSeries.mk b * X ^ 6 := by
    ring
  have hi := b_init
  simp only [List.cons.injEq, and_true] at hi
  rcases hi with ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩
  ext m
  rw [hmulD]
  rcases m with _ | _ | _ | _ | _ | _ | m
  · simp only [map_sub, map_add, map_one, coeff_zero_eq_constantCoeff,
      map_pow, constantCoeff_X, PowerSeries.coeff_zero_mul_X,
      coeff_zero_mul_X_pow, coeff_mk]
    rw [hb0]
    norm_num
  · simp only [map_sub, map_add, coeff_one, coeff_succ_mul_X, coeff_succ_mul_X_pow,
      coeff_zero_mul_X_pow, coeff_C_mul, coeff_X_pow,
      coeff_mul_C, coeff_mk]
    rw [hb0, hb1]
    norm_num
  · simp only [map_sub, map_add, coeff_one, coeff_succ_mul_X, coeff_succ_mul_X_pow,
      coeff_zero_mul_X_pow, coeff_C_mul, coeff_X_pow,
      coeff_mul_C, coeff_mk, pow_zero, mul_one]
    rw [hb0, hb1, hb2]
    norm_num
  · simp only [map_sub, map_add, coeff_one, coeff_succ_mul_X, coeff_succ_mul_X_pow,
      coeff_zero_mul_X_pow, coeff_C_mul, coeff_X_pow,
      coeff_mul_C, coeff_mk, pow_zero, mul_one]
    rw [hb1, hb2, hb3]
    norm_num
  · simp only [map_sub, map_add, coeff_one, coeff_succ_mul_X, coeff_succ_mul_X_pow,
      coeff_zero_mul_X_pow, coeff_C_mul, coeff_X_pow,
      coeff_mul_C, coeff_mk, pow_zero, mul_one]
    rw [hb0, hb2, hb3, hb4]
    norm_num
  · simp only [map_sub, map_add, coeff_one, coeff_succ_mul_X, coeff_succ_mul_X_pow,
      coeff_zero_mul_X_pow, coeff_C_mul, coeff_X_pow,
      coeff_mul_C, coeff_mk, pow_zero, mul_one]
    rw [hb0, hb1, hb3, hb4, hb5]
    norm_num
  · have hm0 : (1 : PowerSeries ℤ).coeff (m + 6) = 0 := by
      rw [coeff_one]; simp
    have hX2 : coeff (m + 6) (C 9 * (X : PowerSeries ℤ) ^ 2) = 0 := by
      rw [coeff_C_mul, coeff_X_pow]; simp
    have hX3 : coeff (m + 6) (C 5 * (X : PowerSeries ℤ) ^ 3) = 0 := by
      rw [coeff_C_mul, coeff_X_pow]; simp
    have hX4 : coeff (m + 6) (C 4 * (X : PowerSeries ℤ) ^ 4) = 0 := by
      rw [coeff_C_mul, coeff_X_pow]; simp
    have hX5 : coeff (m + 6) ((X : PowerSeries ℤ) ^ 5) = 0 := by
      rw [coeff_X_pow]; simp
    simp only [map_sub, map_add, hm0, hX2, hX3, hX4, hX5, sub_zero, coeff_succ_mul_X_pow,
      coeff_succ_mul_X, coeff_mul_C, coeff_mk, pow_zero, mul_one]
    have hrec := b_rec m
    linarith

/-! Part 2: Finite 5-State Row Transition Kernel -/

private structure RowCfg where
  h01 : Bool
  h12 : Bool
  v0 : Bool
  v1 : Bool
  v2 : Bool
  deriving DecidableEq

private def cfgOfFin (n : Fin 32) : RowCfg :=
  ⟨n.1 % 2 == 1, (n.1 / 2) % 2 == 1, (n.1 / 4) % 2 == 1, (n.1 / 8) % 2 == 1, (n.1 / 16) % 2 == 1⟩

private def finOfCfg (c : RowCfg) : Fin 32 :=
  ⟨c.h01.toNat + 2 * c.h12.toNat + 4 * c.v0.toNat + 8 * c.v1.toNat + 16 * c.v2.toNat, by
    cases c.h01 <;> cases c.h12 <;> cases c.v0 <;> cases c.v1 <;> cases c.v2 <;> decide⟩

private lemma cfgOfFin_finOfCfg (c : RowCfg) : cfgOfFin (finOfCfg c) = c := by
  cases c with | mk a b d e f =>
    cases a <;> cases b <;> cases d <;> cases e <;> cases f <;> decide

private lemma finOfCfg_cfgOfFin : ∀ n : Fin 32, finOfCfg (cfgOfFin n) = n := by
  decide

private instance : Fintype RowCfg :=
  Fintype.ofEquiv (Fin 32)
    ⟨cfgOfFin, finOfCfg, finOfCfg_cfgOfFin, cfgOfFin_finOfCfg⟩

private def topCut (s : Fin 5) (c : Fin 3) : Bool :=
  match s, c with
  | 0, 0 => true | 1, 1 => true | 2, 2 => true
  | 3, _ => true | 4, _ => true | _, _ => false

private def botCut (cfg : RowCfg) (c : Fin 3) : Bool :=
  match c with | 0 => cfg.v0 | 1 => cfg.v1 | 2 => cfg.v2

private def colDeg (s : Fin 5) (cfg : RowCfg) (c : Fin 3) : ℕ :=
  (topCut s c).toNat + (botCut cfg c).toNat +
    match c with
    | 0 => cfg.h01.toNat
    | 1 => cfg.h01.toNat + cfg.h12.toNat
    | 2 => cfg.h12.toNat

private def rowDegOk (s : Fin 5) (cfg : RowCfg) : Bool :=
  (colDeg s cfg 0 == 0 || colDeg s cfg 0 == 2) &&
  (colDeg s cfg 1 == 0 || colDeg s cfg 1 == 2) &&
  (colDeg s cfg 2 == 0 || colDeg s cfg 2 == 2)

private def symAdj (s : Fin 5) (cfg : RowCfg) (u v : Fin 7) : Bool :=
  let a := if u.1 ≤ v.1 then u else v
  let b := if u.1 ≤ v.1 then v else u
  (a == 0 && b == 1 && (cfg.h01 || s == 3)) ||
  (a == 1 && b == 2 && (cfg.h12 || s == 4)) ||
  (b == 3 && ((s == 0 && a == 0) || (s == 1 && a == 1) || (s == 2 && a == 2) ||
             (s == 3 && a == 2) || (s == 4 && a == 0))) ||
  (a == 0 && b == 4 && cfg.v0) ||
  (a == 1 && b == 5 && cfg.v1) ||
  (a == 2 && b == 6 && cfg.v2)

private lemma symAdj_symm_fin : ∀ (s : Fin 5) (n : Fin 32) (u v : Fin 7),
    symAdj s (cfgOfFin n) u v = symAdj s (cfgOfFin n) v u := by
  decide

private lemma symAdj_symm (s : Fin 5) (cfg : RowCfg) (u v : Fin 7) :
    symAdj s cfg u v = symAdj s cfg v u := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact symAdj_symm_fin s (finOfCfg cfg) u v

private def symAdjExpl (s : Fin 5) (cfg : RowCfg) (a b : Fin 7) : Bool :=
  (((a == 0 && b == 1) || (a == 1 && b == 0)) && (cfg.h01 || s == 3)) ||
  ((((a == 1 && b == 2) || (a == 2 && b == 1)) && (cfg.h12 || s == 4)) ||
  ((((a == 3 && b == 0) || (a == 0 && b == 3)) && (s == 0 || s == 4)) ||
  ((((a == 3 && b == 1) || (a == 1 && b == 3)) && (s == 1)) ||
  ((((a == 3 && b == 2) || (a == 2 && b == 3)) && (s == 2 || s == 3)) ||
  ((((a == 0 && b == 4) || (a == 4 && b == 0)) && cfg.v0) ||
  ((((a == 1 && b == 5) || (a == 5 && b == 1)) && cfg.v1) ||
  (((a == 2 && b == 6) || (a == 6 && b == 2)) && cfg.v2)))))))

private lemma symAdj_eq_expl_fin : ∀ (s : Fin 5) (n : Fin 32) (a b : Fin 7),
    symAdj s (cfgOfFin n) a b = symAdjExpl s (cfgOfFin n) a b := by
  decide

private lemma symAdj_spec (s : Fin 5) (cfg : RowCfg) (a b : Fin 7) :
    symAdj s cfg a b = true →
      ((a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) ∧ (cfg.h01 = true ∨ s = 3)) ∨
      ((a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1) ∧ (cfg.h12 = true ∨ s = 4)) ∨
      ((a = 3 ∧ b = 0 ∨ a = 0 ∧ b = 3) ∧ (s = 0 ∨ s = 4)) ∨
      ((a = 3 ∧ b = 1 ∨ a = 1 ∧ b = 3) ∧ s = 1) ∨
      ((a = 3 ∧ b = 2 ∨ a = 2 ∧ b = 3) ∧ (s = 2 ∨ s = 3)) ∨
      ((a = 0 ∧ b = 4 ∨ a = 4 ∧ b = 0) ∧ cfg.v0 = true) ∨
      ((a = 1 ∧ b = 5 ∨ a = 5 ∧ b = 1) ∧ cfg.v1 = true) ∨
      ((a = 2 ∧ b = 6 ∨ a = 6 ∧ b = 2) ∧ cfg.v2 = true) := by
  rw [← cfgOfFin_finOfCfg cfg, symAdj_eq_expl_fin]
  simp only [symAdjExpl, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact id

private lemma fin3_cases : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by
  decide

private def symMask (s : Fin 5) (cfg : RowCfg) (u : Fin 7) : ℕ :=
  let bit (k : ℕ) (b : Bool) : ℕ := if b then 2 ^ k else 0
  match u with
  | 0 => bit 1 (cfg.h01 || s == 3) + bit 3 (s == 0 || s == 4) + bit 4 cfg.v0
  | 1 => bit 0 (cfg.h01 || s == 3) + bit 2 (cfg.h12 || s == 4) + bit 3 (s == 1) + bit 5 cfg.v1
  | 2 => bit 1 (cfg.h12 || s == 4) + bit 3 (s == 2 || s == 3) + bit 6 cfg.v2
  | 3 => bit 0 (s == 0 || s == 4) + bit 1 (s == 1) + bit 2 (s == 2 || s == 3)
  | 4 => bit 0 cfg.v0
  | 5 => bit 1 cfg.v1
  | 6 => bit 2 cfg.v2

private lemma testBit_symMask_fin : ∀ (s : Fin 5) (n : Fin 32) (u v : Fin 7),
    (symMask s (cfgOfFin n) u).testBit v.1 = symAdj s (cfgOfFin n) u v := by
  decide

private lemma testBit_symMask (s : Fin 5) (cfg : RowCfg) (u v : Fin 7) :
    (symMask s cfg u).testBit v.1 = symAdj s cfg u v := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact testBit_symMask_fin s (finOfCfg cfg) u v

private def symStep (s : Fin 5) (cfg : RowCfg) (m : ℕ) : ℕ :=
  m |||
  (if m.testBit 0 then symMask s cfg 0 else 0) |||
  (if m.testBit 1 then symMask s cfg 1 else 0) |||
  (if m.testBit 2 then symMask s cfg 2 else 0) |||
  (if m.testBit 3 then symMask s cfg 3 else 0) |||
  (if m.testBit 4 then symMask s cfg 4 else 0) |||
  (if m.testBit 5 then symMask s cfg 5 else 0) |||
  (if m.testBit 6 then symMask s cfg 6 else 0)

private def symReachMask (s : Fin 5) (cfg : RowCfg) (u : Fin 7) : ℕ :=
  ((symStep s cfg)^[6]) (2 ^ u.1)

private def symReach (s : Fin 5) (cfg : RowCfg) (u v : Fin 7) : Bool :=
  (symReachMask s cfg u).testBit v.1

private def exitsOk (s : Fin 5) (cfg : RowCfg) : Bool :=
  let reachExit (c : Fin 3) : Bool :=
    colDeg s cfg c != 2 ||
    (symReach s cfg ⟨c.1, by omega⟩ 3 ||
      (cfg.v0 && symReach s cfg ⟨c.1, by omega⟩ 4) ||
      (cfg.v1 && symReach s cfg ⟨c.1, by omega⟩ 5) ||
      (cfg.v2 && symReach s cfg ⟨c.1, by omega⟩ 6))
  reachExit 0 && reachExit 1 && reachExit 2

private def outStateOpt (s : Fin 5) (cfg : RowCfg) : Option (Fin 5) :=
  if !(rowDegOk s cfg && exitsOk s cfg) then none
  else match cfg.v0, cfg.v1, cfg.v2 with
  | true, false, false => if symReach s cfg 3 4 then some 0 else none
  | false, true, false => if symReach s cfg 3 5 then some 1 else none
  | false, false, true => if symReach s cfg 3 6 then some 2 else none
  | true, true, true =>
      if symReach s cfg 3 6 && symReach s cfg 4 5 then some 3
      else if symReach s cfg 3 4 && symReach s cfg 5 6 then some 4
      else none
  | _, _, _ => none

private lemma check_always_five_fin : ∀ (s : Fin 5) (n : Fin 32),
    rowDegOk s (cfgOfFin n) = true → exitsOk s (cfgOfFin n) = true →
    (outStateOpt s (cfgOfFin n)).isSome = true := by
  decide

private lemma check_always_five (s : Fin 5) (cfg : RowCfg) :
    rowDegOk s cfg = true → exitsOk s cfg = true → (outStateOpt s cfg).isSome = true := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact check_always_five_fin s (finOfCfg cfg)

private lemma symReachMask_fixed_fin : ∀ (s : Fin 5) (n : Fin 32) (u : Fin 7),
    symStep s (cfgOfFin n) (symReachMask s (cfgOfFin n) u) = symReachMask s (cfgOfFin n) u := by
  decide

private lemma symReachMask_fixed (s : Fin 5) (cfg : RowCfg) (u : Fin 7) :
    symStep s cfg (symReachMask s cfg u) = symReachMask s cfg u := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact symReachMask_fixed_fin s (finOfCfg cfg) u

private lemma symReach_refl_fin : ∀ (s : Fin 5) (n : Fin 32) (u : Fin 7),
    symReach s (cfgOfFin n) u u = true := by
  decide

private lemma symReach_refl (s : Fin 5) (cfg : RowCfg) (u : Fin 7) :
    symReach s cfg u u = true := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact symReach_refl_fin s (finOfCfg cfg) u

private lemma state3_disjoint_fin : ∀ (s : Fin 5) (n : Fin 32),
    rowDegOk s (cfgOfFin n) = true →
    symReach s (cfgOfFin n) 3 6 = true → symReach s (cfgOfFin n) 4 5 = true →
    symReach s (cfgOfFin n) 3 4 = false ∧ symReach s (cfgOfFin n) 3 5 = false := by
  decide

private lemma state3_disjoint (s : Fin 5) (cfg : RowCfg) :
    rowDegOk s cfg = true →
    symReach s cfg 3 6 = true → symReach s cfg 4 5 = true →
    symReach s cfg 3 4 = false ∧ symReach s cfg 3 5 = false := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact state3_disjoint_fin s (finOfCfg cfg)

private lemma state4_disjoint_fin : ∀ (s : Fin 5) (n : Fin 32),
    rowDegOk s (cfgOfFin n) = true →
    symReach s (cfgOfFin n) 3 4 = true → symReach s (cfgOfFin n) 5 6 = true →
    symReach s (cfgOfFin n) 3 5 = false ∧ symReach s (cfgOfFin n) 3 6 = false := by
  decide

private lemma state4_disjoint (s : Fin 5) (cfg : RowCfg) :
    rowDegOk s cfg = true →
    symReach s cfg 3 4 = true → symReach s cfg 5 6 = true →
    symReach s cfg 3 5 = false ∧ symReach s cfg 3 6 = false := by
  rw [← cfgOfFin_finOfCfg cfg]
  exact state4_disjoint_fin s (finOfCfg cfg)

private lemma symStep_testBit (s : Fin 5) (cfg : RowCfg) (m : ℕ) (v : Fin 7) :
    (symStep s cfg m).testBit v.1 = true ↔
      m.testBit v.1 = true ∨ ∃ j : Fin 7, m.testBit j.1 = true ∧ symAdj s cfg j v = true := by
  have hb : ∀ (j : Fin 7),
      (if m.testBit j.1 then symMask s cfg j else 0).testBit v.1 = true ↔
        m.testBit j.1 = true ∧ symAdj s cfg j v = true := fun j => by
    by_cases h : m.testBit j.1 = true
    · simp [h, testBit_symMask]
    · simp [h, Nat.zero_testBit]
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6
  dsimp at h0 h1 h2 h3 h4 h5 h6
  simp only [symStep, Nat.testBit_lor, Bool.or_eq_true, h0, h1, h2, h3, h4, h5, h6]
  constructor
  · rintro (((((((h | h) | h) | h) | h) | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr ⟨0, h⟩
    · exact Or.inr ⟨1, h⟩
    · exact Or.inr ⟨2, h⟩
    · exact Or.inr ⟨3, h⟩
    · exact Or.inr ⟨4, h⟩
    · exact Or.inr ⟨5, h⟩
    · exact Or.inr ⟨6, h⟩
  · rintro (h | ⟨j, h⟩)
    · left; left; left; left; left; left; left; exact h
    · fin_cases j <;> simp_all

private lemma symReach_iff_reflTransGen (s : Fin 5) (cfg : RowCfg) (u v : Fin 7) :
    symReach s cfg u v = true ↔
      Relation.ReflTransGen (fun a b => symAdj s cfg a b = true) u v := by
  constructor
  · intro hv
    have hiter : ∀ k m (w : Fin 7),
        (((symStep s cfg)^[k]) m).testBit w.1 = true →
          ∃ a : Fin 7, m.testBit a.1 = true ∧
            Relation.ReflTransGen (fun x y => symAdj s cfg x y = true) a w := by
      intro k
      induction k with
      | zero =>
        intro m w hw
        exact ⟨w, hw, Relation.ReflTransGen.refl⟩
      | succ k ih =>
        intro m w hw
        rw [Function.iterate_succ_apply'] at hw
        rw [symStep_testBit] at hw
        rcases hw with hw | ⟨j, hj, hstep⟩
        · exact ih m w hw
        · obtain ⟨a, ha, hpath⟩ := ih m j hj
          exact ⟨a, ha, hpath.tail hstep⟩
    obtain ⟨a, ha, hpath⟩ := hiter 6 (2 ^ u.1) v hv
    rw [Nat.testBit_two_pow] at ha
    have hau : u = a := Fin.ext (of_decide_eq_true ha)
    rwa [hau]
  · intro hpath
    induction hpath with
    | refl => exact symReach_refl s cfg u
    | @tail y z _ hyz ih =>
      unfold symReach at ih ⊢
      rw [← symReachMask_fixed s cfg u, symStep_testBit]
      exact Or.inr ⟨y, ih, hyz⟩

private lemma check_T_aux :
    Matrix.of (fun s t : Fin 5 =>
      (((List.finRange 32).countP
        (fun n => outStateOpt s (cfgOfFin n) == some t) : ℕ) : ℤ)) = T := by
  decide

private lemma check_M_mid_aux :
    Matrix.of (fun s t : Fin 5 =>
      (((List.finRange 32).countP
        (fun n => outStateOpt s (cfgOfFin n) == some t && (colDeg s (cfgOfFin n) 1 == 2)) : ℕ) : ℤ)) =
      M_mid := by
  decide

private lemma toFinset_filter_card {α : Type*} [DecidableEq α]
    (p : α → Bool) : ∀ l : List α, l.Nodup →
      (l.toFinset.filter (fun x => p x = true)).card = l.countP p
  | [], _ => by simp
  | a :: l, h => by
    rw [List.nodup_cons] at h
    have ih := toFinset_filter_card p l h.2
    have ha : a ∉ l.toFinset.filter (fun x => p x = true) := fun hm =>
      h.1 (List.mem_toFinset.mp (Finset.mem_filter.mp hm).1)
    by_cases hpa : p a = true
    · have hset : (a :: l).toFinset.filter (fun x => p x = true) =
          insert a (l.toFinset.filter (fun x => p x = true)) := by
        ext x
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hp⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hx, hp⟩
        · rintro (rfl | ⟨hx, hp⟩)
          · exact ⟨Or.inl rfl, hpa⟩
          · exact ⟨Or.inr hx, hp⟩
      rw [hset, Finset.card_insert_of_notMem ha, ih, List.countP_cons_of_pos hpa, add_comm]
    · have hset : (a :: l).toFinset.filter (fun x => p x = true) =
          l.toFinset.filter (fun x => p x = true) := by
        ext x
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons]
        constructor
        · rintro ⟨rfl | hx, hp⟩
          · exact absurd hp hpa
          · exact ⟨hx, hp⟩
        · rintro ⟨hx, hp⟩
          exact ⟨Or.inr hx, hp⟩
      rw [hset, ih, List.countP_cons_of_neg (by simpa using hpa)]

private lemma card_rowCfg_eq_countP (p : RowCfg → Bool) :
    ((Finset.univ : Finset RowCfg).filter (fun cfg => p cfg = true)).card =
      (List.finRange 32).countP (fun n => p (cfgOfFin n)) := by
  have hbij :
      ((Finset.univ : Finset RowCfg).filter (fun cfg => p cfg = true)).card =
        ((Finset.univ : Finset (Fin 32)).filter (fun n => p (cfgOfFin n) = true)).card := by
    refine Finset.card_bij (fun cfg _ => finOfCfg cfg) ?_ ?_ ?_
    · intro cfg hcfg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcfg ⊢
      rwa [cfgOfFin_finOfCfg]
    · intro c₁ _ c₂ _ h
      have := congrArg cfgOfFin h
      rwa [cfgOfFin_finOfCfg, cfgOfFin_finOfCfg] at this
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
      exact ⟨cfgOfFin n, by simp [hn], finOfCfg_cfgOfFin n⟩
  have huniv : (List.finRange 32).toFinset = (Finset.univ : Finset (Fin 32)) := by
    ext x
    simp
  rw [hbij, ← huniv, toFinset_filter_card _ _ (List.nodup_finRange 32)]

private lemma card_step_T (s t : Fin 5) :
    (((Finset.univ : Finset RowCfg).filter
      (fun cfg => outStateOpt s cfg = some t)).card : ℤ) = T s t := by
  have h := congrFun (congrFun check_T_aux s) t
  dsimp at h
  rw [← h]
  congr 1
  convert card_rowCfg_eq_countP (fun cfg => outStateOpt s cfg == some t) using 2
  ext cfg
  simp

private lemma card_step_M_mid (s t : Fin 5) :
    (((Finset.univ : Finset RowCfg).filter
      (fun cfg => outStateOpt s cfg = some t ∧ colDeg s cfg 1 = 2)).card : ℤ) = M_mid s t := by
  have h := congrFun (congrFun check_M_mid_aux s) t
  dsimp at h
  rw [← h]
  congr 1
  convert card_rowCfg_eq_countP
    (fun cfg => outStateOpt s cfg == some t && (colDeg s cfg 1 == 2)) using 2
  ext cfg
  simp

/-! Part 3: Step A — Walks Biject to Connected {0, 2}-Degree Grid Edge Subgraphs -/

private abbrev SiteF (H : ℕ) := Fin H × Fin 3

private def adjF {H : ℕ} (u v : SiteF H) : Bool :=
  Nat.dist u.1.1 v.1.1 + Nat.dist u.2.1 v.2.1 == 1

private def isWalkF (H : ℕ) (hH : 0 < H) (w : List (SiteF H)) : Prop :=
  w.head? = some (⟨0, hH⟩, 0) ∧
    w.getLast? = some (⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2) ∧
    w.Nodup ∧ List.IsChain (fun a b => adjF a b = true) w

private lemma isChain_pmap_walk {n : ℕ} :
    ∀ (l : List OMA.S_oeis_a333686.Site)
      (hl : ∀ p ∈ l, p.1 < 2 * n + 1 ∧ p.2 < 3),
      List.IsChain OMA.S_oeis_a333686.adjacent l →
      List.IsChain (fun a b : SiteF (2 * n + 1) => adjF a b = true)
        (l.pmap (fun p hp => (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)) hl)
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: t, hl, hc => by
    rw [List.isChain_cons_cons] at hc
    simp only [List.pmap_cons, List.isChain_cons_cons]
    refine ⟨?_, isChain_pmap_walk (b :: t) (fun p hp => hl p (by simp [hp])) hc.2⟩
    simpa [adjF, OMA.S_oeis_a333686.adjacent] using hc.1

private lemma isChain_map_walk {n : ℕ} :
    ∀ l : List (SiteF (2 * n + 1)),
      List.IsChain (fun a b => adjF a b = true) l →
      List.IsChain OMA.S_oeis_a333686.adjacent (l.map (fun p => (p.1.1, p.2.1)))
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: t, hc => by
    rw [List.isChain_cons_cons] at hc
    simp only [List.map_cons, List.isChain_cons_cons]
    refine ⟨?_, isChain_map_walk (b :: t) hc.2⟩
    simpa [adjF, OMA.S_oeis_a333686.adjacent] using hc.1

private def walk_equiv_walkF (n : ℕ) :
    {w : List OMA.S_oeis_a333686.Site //
      OMA.S_oeis_a333686.isWalk (2 * n + 1) 3 (0, 0) (2 * n, 2) w ∧ (n, 1) ∈ w} ≃
      {w : List (SiteF (2 * n + 1)) //
        isWalkF (2 * n + 1) (Nat.succ_pos _) w ∧ (⟨n, by omega⟩, (1 : Fin 3)) ∈ w} where
  toFun := fun ⟨w, hw, hmid⟩ =>
    ⟨w.pmap (fun p hp => (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)) hw.2.2.2.2,
      ⟨by
        cases w with
        | nil => simp [OMA.S_oeis_a333686.isWalk] at hw
        | cons a l =>
          have ha : a = (0, 0) := Option.some.inj hw.1
          simp [ha],
       by
        have hne : w ≠ [] := fun h => by simp [h, OMA.S_oeis_a333686.isWalk] at hw
        rw [List.getLast?_eq_some_getLast (by simp [hne])]
        have hgl : w.getLast hne = (2 * n, 2) := by
          have := hw.2.1
          rw [List.getLast?_eq_some_getLast hne] at this
          exact Option.some.inj this
        simp only [List.getLast_pmap, Option.some.injEq]
        ext <;> simp [hgl],
       List.Nodup.pmap (fun a ha b hb h => Prod.ext (congrArg (fun t => t.1.1) h)
         (congrArg (fun t => t.2.1) h)) hw.2.2.1,
       isChain_pmap_walk w hw.2.2.2.2 hw.2.2.2.1⟩,
      List.mem_pmap.mpr ⟨(n, 1), hmid, rfl⟩⟩
  invFun := fun ⟨w, hw, hmid⟩ =>
    ⟨w.map (fun p => (p.1.1, p.2.1)),
      ⟨by
        cases w with
        | nil => simp [isWalkF] at hw
        | cons a l =>
          have ha : a = (⟨0, Nat.succ_pos _⟩, 0) := Option.some.inj hw.1
          simp [ha],
       by
        have hne : w ≠ [] := fun h => by simp [h, isWalkF] at hw
        rw [List.getLast?_eq_some_getLast (by simp [hne])]
        have hgl : w.getLast hne = (⟨2 * n, by omega⟩, 2) := by
          have := hw.2.1
          rw [List.getLast?_eq_some_getLast hne] at this
          simpa using Option.some.inj this
        simp only [List.getLast_map, Option.some.injEq, hgl]
        rfl,
       hw.2.2.1.map fun a b h => Prod.ext (Fin.ext (congrArg Prod.fst h))
         (Fin.ext (congrArg Prod.snd h)),
       isChain_map_walk w hw.2.2.2,
       fun p hp => by
        rcases List.mem_map.mp hp with ⟨q, _, rfl⟩
        exact ⟨q.1.2, q.2.2⟩⟩,
      List.mem_map.mpr ⟨(⟨n, by omega⟩, 1), hmid, rfl⟩⟩
  left_inv := fun ⟨w, _, _⟩ => by
    ext1
    simp only [List.map_pmap, List.pmap_eq_map]
    exact List.map_id' _
  right_inv := fun ⟨w, _, _⟩ => by
    ext1
    simp only [List.pmap_map]
    exact List.pmap_eq_self.mpr fun _ _ => rfl

private structure GridEdges (H : ℕ) where
  he : Fin H → Fin 2 → Bool
  ve : Fin H → Fin 3 → Bool
  deriving DecidableEq

private lemma GridEdges.ext' {H : ℕ} {g₁ g₂ : GridEdges H}
    (h1 : g₁.he = g₂.he) (h2 : g₁.ve = g₂.ve) : g₁ = g₂ := by
  cases g₁; cases g₂; cases h1; cases h2; rfl

private instance (H : ℕ) : Fintype (GridEdges H) :=
  Fintype.ofEquiv ((Fin H → Fin 2 → Bool) × (Fin H → Fin 3 → Bool))
    ⟨fun p => ⟨p.1, p.2⟩, fun g => ⟨g.he, g.ve⟩,
     fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

private def topCutG {H : ℕ} (g : GridEdges H) (r : Fin H) (c : Fin 3) : Bool :=
  if h : r.1 = 0 then c == 0 else g.ve ⟨r.1 - 1, by omega⟩ c

private def siteDeg {H : ℕ} (g : GridEdges H) (r : Fin H) (c : Fin 3) : ℕ :=
  (topCutG g r c).toNat + (g.ve r c).toNat +
    match c with
    | 0 => (g.he r 0).toNat
    | 1 => (g.he r 0).toNat + (g.he r 1).toNat
    | 2 => (g.he r 1).toNat

private def hasEdge {H : ℕ} (g : GridEdges H) (u v : SiteF H) : Bool :=
  if u.1 = v.1 then
    if (u.2 == 0 && v.2 == 1) || (u.2 == 1 && v.2 == 0) then g.he u.1 0
    else if (u.2 == 1 && v.2 == 2) || (u.2 == 2 && v.2 == 1) then g.he u.1 1
    else false
  else if u.2 = v.2 then
    if u.1.1 + 1 = v.1.1 then g.ve u.1 u.2
    else if v.1.1 + 1 = u.1.1 then g.ve v.1 u.2
    else false
  else false

private lemma hasEdge_symm {H : ℕ} (g : GridEdges H) (u v : SiteF H) :
    hasEdge g u v = hasEdge g v u := by
  rcases u with ⟨r₁, c₁⟩
  rcases v with ⟨r₂, c₂⟩
  unfold hasEdge
  by_cases hr : r₁ = r₂
  · subst hr
    fin_cases c₁ <;> fin_cases c₂ <;> simp
  · have hr' : r₂ ≠ r₁ := Ne.symm hr
    by_cases hc : c₁ = c₂
    · subst hc
      simp only [hr, hr', ↓reduceIte]
      by_cases h1 : r₁.1 + 1 = r₂.1 <;> by_cases h2 : r₂.1 + 1 = r₁.1
      · omega
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [hr, hr', hc, Ne.symm hc]

private lemma hasEdge_adj {H : ℕ} {g : GridEdges H} {u v : SiteF H}
    (h : hasEdge g u v = true) : adjF u v = true := by
  rcases u with ⟨r₁, c₁⟩
  rcases v with ⟨r₂, c₂⟩
  unfold hasEdge at h
  by_cases hr : r₁ = r₂
  · subst hr
    fin_cases c₁ <;> fin_cases c₂ <;> simp_all [adjF, Nat.dist]
  · simp only [hr, ↓reduceIte] at h
    by_cases hc : c₁ = c₂
    · subst hc
      simp only [↓reduceIte] at h
      by_cases h1 : r₁.1 + 1 = r₂.1
      · simp only [adjF, Nat.dist, beq_iff_eq]; omega
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : r₂.1 + 1 = r₁.1
        · simp only [adjF, Nat.dist, beq_iff_eq]; omega
        · simp [h2] at h
    · simp [hc] at h

private lemma hasEdge_ne {H : ℕ} {g : GridEdges H} {u v : SiteF H}
    (h : hasEdge g u v = true) : u ≠ v := by
  intro heq
  subst heq
  have := hasEdge_adj h
  simp [adjF, Nat.dist] at this

private def topSite {H : ℕ} (hH : 0 < H) : SiteF H := (⟨0, hH⟩, 0)

private def botSite {H : ℕ} (hH : 0 < H) : SiteF H :=
  (⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2)

private def GoodEdges (H : ℕ) (hH : 0 < H) (g : GridEdges H) : Prop :=
  (∀ c : Fin 3, g.ve ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ c = (c == 2)) ∧
  (∀ r : Fin H, ∀ c : Fin 3, siteDeg g r c = 0 ∨ siteDeg g r c = 2) ∧
  (∀ u : SiteF H, siteDeg g u.1 u.2 = 2 →
    Relation.ReflTransGen (fun a b => hasEdge g a b = true) (topSite hH) u)

private lemma card_nbrs_eq {H : ℕ} (hH : 0 < H) (g : GridEdges H)
    (hlast : ∀ c : Fin 3, g.ve ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ c = (c == 2))
    (u : SiteF H) :
    ((Finset.univ : Finset (SiteF H)).filter (fun v => hasEdge g u v = true)).card +
      (if u = topSite hH then 1 else 0) + (if u = botSite hH then 1 else 0) =
      siteDeg g u.1 u.2 := by
  rcases u with ⟨r, c⟩
  let S := (Finset.univ : Finset (SiteF H)).filter (fun v => hasEdge g (r, c) v = true)
  have hsplit :
      S.card =
        (S.filter (fun v => v.1 = r)).card + (S.filter (fun v => v.1 ≠ r)).card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hrow :
      (S.filter (fun v => v.1 = r)).card =
        match c with
        | 0 => (g.he r 0).toNat
        | 1 => (g.he r 0).toNat + (g.he r 1).toNat
        | 2 => (g.he r 1).toNat := by
    have hinj :
        (S.filter (fun v => v.1 = r)).card =
          ((Finset.univ : Finset (Fin 3)).filter (fun c' => hasEdge g (r, c) (r, c') = true)).card := by
      refine Finset.card_bij (fun v _ => v.2) ?_ ?_ ?_
      · intro v hv
        dsimp [S] at hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have heq : (r, v.2) = v := Prod.ext hv.2.symm rfl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [heq]; exact hv.1⟩
      · intro v₁ hv₁ v₂ hv₂ hvc
        dsimp [S] at hv₁ hv₂
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
        exact Prod.ext (hv₁.2.trans hv₂.2.symm) hvc
      · intro c' hc'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        exact ⟨(r, c'), by simp [S, hc'], rfl⟩
    rw [hinj, Finset.card_filter, Fin.sum_univ_three]
    fin_cases c <;> simp [hasEdge] <;> cases g.he r 0 <;> cases g.he r 1 <;> rfl
  have hcol :
      (S.filter (fun v => v.1 ≠ r)).card +
        (if (r, c) = topSite hH then 1 else 0) + (if (r, c) = botSite hH then 1 else 0) =
        (topCutG g r c).toNat + (g.ve r c).toNat := by
    have hinj :
        (S.filter (fun v => v.1 ≠ r)).card =
          ((Finset.univ : Finset (Fin H)).filter
            (fun r' => r' ≠ r ∧ hasEdge g (r, c) (r', c) = true)).card := by
      refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
      · intro v hv
        dsimp [S] at hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hvc : v.2 = c := by
          have := hv.1
          unfold hasEdge at this
          simp only [Ne.symm hv.2, ↓reduceIte] at this
          by_cases hc : c = v.2
          · exact hc.symm
          · simp [hc] at this
        have hv_eq : (v.1, c) = v := Prod.ext rfl hvc.symm
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2, ?_⟩
        rw [hv_eq]
        exact hv.1
      · intro v₁ hv₁ v₂ hv₂ hvr
        dsimp [S] at hv₁ hv₂
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
        have hc1 : v₁.2 = c := by
          have := hv₁.1
          unfold hasEdge at this
          simp only [Ne.symm hv₁.2, ↓reduceIte] at this
          by_cases hc : c = v₁.2 <;> simp_all
        have hc2 : v₂.2 = c := by
          have := hv₂.1
          unfold hasEdge at this
          simp only [Ne.symm hv₂.2, ↓reduceIte] at this
          by_cases hc : c = v₂.2 <;> simp_all
        exact Prod.ext hvr (hc1.trans hc2.symm)
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
        exact ⟨(r', c), by simp [S, hr'.1, hr'.2], rfl⟩
    rw [hinj]
    have hpred :
        ∀ r' : Fin H,
          (r' ≠ r ∧ hasEdge g (r, c) (r', c) = true) ↔
            ((r.1 + 1 = r'.1 ∧ g.ve r c = true) ∨
             (r'.1 + 1 = r.1 ∧ g.ve ⟨r.1 - 1, by omega⟩ c = true)) := by
      intro r'
      have := r.2
      have := r'.2
      unfold hasEdge
      by_cases hr' : r' = r
      · subst hr'
        simp only [ne_eq, not_true_eq_false, false_and, false_iff, not_or, not_and]
        constructor <;> omega
      · have hr1 : r ≠ r' := Ne.symm hr'
        simp only [hr1, ↓reduceIte, ne_eq, hr', not_false_eq_true, true_and]
        by_cases h1 : r.1 + 1 = r'.1
        · have h2 : ¬ r'.1 + 1 = r.1 := by omega
          simp [h1, h2]
        · by_cases h2 : r'.1 + 1 = r.1
          · have hrm : (⟨r.1 - 1, by omega⟩ : Fin H) = r' := Fin.ext (by dsimp; omega)
            simp [h1, h2, hrm]
          · simp [h1, h2]
    have hcard_up_down :
        ((Finset.univ : Finset (Fin H)).filter
          (fun r' => r' ≠ r ∧ hasEdge g (r, c) (r', c) = true)).card =
          (if r.1 + 1 < H then (g.ve r c).toNat else 0) +
            (if r.1 = 0 then 0 else (g.ve ⟨r.1 - 1, by omega⟩ c).toNat) := by
      have hset :
          ((Finset.univ : Finset (Fin H)).filter
            (fun r' => r' ≠ r ∧ hasEdge g (r, c) (r', c) = true)) =
            (if h1 : r.1 + 1 < H ∧ g.ve r c = true then ({⟨r.1 + 1, h1.1⟩} : Finset (Fin H))
              else ∅) ∪
            (if h0 : r.1 ≠ 0 ∧ g.ve ⟨r.1 - 1, by omega⟩ c = true then
              ({⟨r.1 - 1, by omega⟩} : Finset (Fin H)) else ∅) := by
        ext r'
        have := r.2
        have := r'.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpred, Finset.mem_union]
        constructor
        · rintro (⟨h1, hv⟩ | ⟨h2, hv⟩)
          · left
            have hlt : r.1 + 1 < H := h1 ▸ r'.2
            simp only [hlt, hv, and_self, ↓reduceDIte, Finset.mem_singleton]
            exact Fin.ext h1.symm
          · right
            have hne : r.1 ≠ 0 := by omega
            simp only [hne, hv, ne_eq, not_false_eq_true, and_self, ↓reduceDIte,
              Finset.mem_singleton]
            exact Fin.ext (by dsimp; omega)
        · rintro (h | h)
          · split_ifs at h with h1
            · rw [Finset.mem_singleton] at h
              left
              exact ⟨congrArg Fin.val h ▸ rfl, h1.2⟩
            · simp at h
          · split_ifs at h with h0
            · rw [Finset.mem_singleton] at h
              right
              have hval := congrArg Fin.val h
              dsimp at hval
              exact ⟨by omega, h0.2⟩
            · simp at h
      have hdisj :
          Disjoint
            (if h1 : r.1 + 1 < H ∧ g.ve r c = true then ({⟨r.1 + 1, h1.1⟩} : Finset (Fin H))
              else ∅)
            (if h0 : r.1 ≠ 0 ∧ g.ve ⟨r.1 - 1, by omega⟩ c = true then
              ({⟨r.1 - 1, by omega⟩} : Finset (Fin H)) else ∅) := by
        rw [Finset.disjoint_left]
        intro r' hr1 hr2
        split_ifs at hr1 hr2 with h1 h0 <;> simp at hr1 hr2
        subst hr1
        have := congrArg Fin.val hr2
        dsimp at this
        omega
      rw [hset, Finset.card_union_of_disjoint hdisj]
      have hA :
          (if h1 : r.1 + 1 < H ∧ g.ve r c = true then ({⟨r.1 + 1, h1.1⟩} : Finset (Fin H))
            else ∅).card = if r.1 + 1 < H then (g.ve r c).toNat else 0 := by
        by_cases hlt : r.1 + 1 < H <;> cases hv : g.ve r c <;> simp [hlt]
      have hB :
          (if h0 : r.1 ≠ 0 ∧ g.ve ⟨r.1 - 1, by omega⟩ c = true then
            ({⟨r.1 - 1, by omega⟩} : Finset (Fin H)) else ∅).card =
            if r.1 = 0 then 0 else (g.ve ⟨r.1 - 1, by omega⟩ c).toNat := by
        by_cases hz : r.1 = 0 <;> cases hv : g.ve ⟨r.1 - 1, by omega⟩ c <;> simp [hz]
      rw [hA, hB]
    rw [hcard_up_down]
    have htop :
        (if (r, c) = topSite hH then 1 else 0) +
            (if r.1 = 0 then 0 else (g.ve ⟨r.1 - 1, by omega⟩ c).toNat) =
          (topCutG g r c).toNat := by
      unfold topSite topCutG
      by_cases hr0 : r.1 = 0
      · have hreq : r = ⟨0, hH⟩ := Fin.ext hr0
        fin_cases c <;> simp [hreq]
      · have hne : (r, c) ≠ (⟨0, hH⟩, 0) := fun h => hr0 (congrArg (fun t => t.1.1) h)
        simp [hr0, hne]
    have hbot :
        (if r.1 + 1 < H then (g.ve r c).toNat else 0) +
            (if (r, c) = botSite hH then 1 else 0) =
          (g.ve r c).toNat := by
      unfold botSite
      have := r.2
      by_cases hrH : r.1 + 1 < H
      · have hne : (r, c) ≠ (⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2) := fun h => by
          have := congrArg (fun t => t.1.1) h
          dsimp at this
          omega
        simp [hrH, hne]
      · have hrEq : r = ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ := Fin.ext (by dsimp; omega)
        subst hrEq
        have hnot : ¬ (H - 1 + 1 < H) := by omega
        rw [hlast c]
        fin_cases c <;> simp [hnot]
    have hbot_deg : (topCutG g r c).toNat + (g.ve r c).toNat =
        (if (r, c) = topSite hH then 1 else 0) + (if r.1 = 0 then 0 else (g.ve ⟨r.1 - 1, by omega⟩ c).toNat) +
          ((if r.1 + 1 < H then (g.ve r c).toNat else 0) + (if (r, c) = botSite hH then 1 else 0)) := by
      rw [htop, hbot]
    omega
  rw [hsplit, hrow]
  unfold siteDeg
  dsimp only at *
  omega

private def pairsOf {α : Type*} (w : List α) : List (α × α) := w.zip w.tail

private def memEdge {α : Type*} (w : List α) (u v : α) : Prop :=
  (u, v) ∈ pairsOf w ∨ (v, u) ∈ pairsOf w

private instance {α : Type*} [DecidableEq α] (w : List α) (u v : α) :
    Decidable (memEdge w u v) :=
  inferInstanceAs (Decidable ((u, v) ∈ pairsOf w ∨ (v, u) ∈ pairsOf w))

private lemma getLast?_mem {α : Type*} : ∀ {l : List α} {x : α}, l.getLast? = some x → x ∈ l
  | [], _, h => by simp at h
  | [a], x, h => by simp only [List.getLast?_singleton, Option.some.injEq] at h; simp [h]
  | a :: b :: t, x, h => by
    have h' : (b :: t).getLast? = some x := by simpa using h
    exact List.mem_cons_of_mem a (getLast?_mem h')

private lemma mem_of_memEdge {α : Type*} {w : List α} {u v : α} (h : memEdge w u v) :
    u ∈ w ∧ v ∈ w := by
  rcases h with h | h
  · have hz := List.of_mem_zip h
    exact ⟨hz.1, List.mem_of_mem_tail hz.2⟩
  · have hz := List.of_mem_zip h
    exact ⟨List.mem_of_mem_tail hz.2, hz.1⟩

private lemma memEdge_symm {α : Type*} {w : List α} {u v : α} (h : memEdge w u v) :
    memEdge w v u := h.symm

private lemma memEdge_cons_cons {α : Type*} (a b : α) (tl : List α) (u v : α) :
    memEdge (a :: b :: tl) u v ↔
      ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∨ memEdge (b :: tl) u v := by
  simp only [memEdge, pairsOf, List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
  tauto

private lemma memEdge_singleton {α : Type*} (a u v : α) : ¬ memEdge [a] u v := by
  simp [memEdge, pairsOf]

private lemma memEdge_ne {α : Type*} :
    ∀ {w : List α}, w.Nodup → ∀ {u v : α}, memEdge w u v → u ≠ v
  | [], _, _, _, h => by simp [memEdge, pairsOf] at h
  | [a], _, _, _, h => absurd h (memEdge_singleton a _ _)
  | a :: b :: tl, hnd, u, v, h => by
    rw [memEdge_cons_cons] at h
    rw [List.nodup_cons] at hnd
    rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | h
    · exact fun heq => hnd.1 (by simp [heq])
    · exact fun heq => hnd.1 (by simp [heq])
    · exact memEdge_ne hnd.2 h

private lemma card_filter_memEdge {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ {w : List α} {h l : α}, w.head? = some h → w.getLast? = some l → h ≠ l → w.Nodup →
      ∀ u : α, ((Finset.univ : Finset α).filter (fun v => memEdge w u v)).card =
        if u ∉ w then 0 else if u = h ∨ u = l then 1 else 2
  | [], _, _, hh, _, _, _, _ => by simp at hh
  | [a], h, l, hh, hl, hne, _, _ => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    exact absurd (hh.symm.trans hl) hne
  | a :: b :: tl, h, l, hh, hl, hne, hnd, u => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [List.nodup_cons] at hnd
    have ha_not : a ∉ b :: tl := hnd.1
    cases tl with
    | nil =>
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      by_cases hua : u = a
      · subst hua
        have hset : (Finset.univ : Finset α).filter (fun v => memEdge [u, b] u v) = {b} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro (h | h)
            · simp only [pairsOf, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
                List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
              exact h.2
            · simp only [pairsOf, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
                List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
              exact absurd h.2 hne
          · rintro rfl
            exact Or.inl (by simp [pairsOf])
        simp [hset]
      · by_cases hub : u = b
        · subst hub
          have hset : (Finset.univ : Finset α).filter (fun v => memEdge [a, u] u v) = {a} := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro (h | h)
              · simp only [pairsOf, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
                  List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
                exact absurd h.1 hua
              · simp only [pairsOf, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
                  List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
                exact h.1
            · rintro rfl
              exact Or.inr (by simp [pairsOf])
          simp [hset, hua]
        · have hu_not : u ∉ [a, b] := by simp [hua, hub]
          have hset : (Finset.univ : Finset α).filter (fun v => memEdge [a, b] u v) = ∅ := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hm
            exact hu_not (mem_of_memEdge hm).1
          simp [hset, hua, hub]
    | cons c tl' =>
      have hl' : (b :: c :: tl').getLast? = some l := by
        simpa using hl
      have hbl : b ≠ l := by
        intro heq
        subst heq
        have hnd' := hnd.2
        rw [List.nodup_cons] at hnd'
        have hlmem : b ∈ c :: tl' := by
          have h' : (c :: tl').getLast? = some b := by simpa using hl'
          exact getLast?_mem h'
        exact hnd'.1 hlmem
      have hal : a ≠ l := hne
      have ih := card_filter_memEdge rfl hl' hbl hnd.2
      by_cases hua : u = a
      · subst hua
        have hset :
            (Finset.univ : Finset α).filter (fun v => memEdge (u :: b :: c :: tl') u v) = {b} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          rw [memEdge_cons_cons]
          constructor
          · rintro ((⟨_, rfl⟩ | ⟨h1, _⟩) | hm)
            · rfl
            · exact absurd (h1 ▸ List.mem_cons_self : u ∈ b :: c :: tl') ha_not
            · exact absurd (mem_of_memEdge hm).1 ha_not
          · rintro rfl
            exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        simp [hset]
      · by_cases hub : u = b
        · subst hub
          have hih := ih u
          have ha_not_f : a ∉ (Finset.univ : Finset α).filter (fun v => memEdge (u :: c :: tl') u v) :=
            fun hm => ha_not (mem_of_memEdge (Finset.mem_filter.mp hm).2).2
          have hset :
              (Finset.univ : Finset α).filter (fun v => memEdge (a :: u :: c :: tl') u v) =
                insert a ((Finset.univ : Finset α).filter (fun v => memEdge (u :: c :: tl') u v)) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            rw [memEdge_cons_cons]
            constructor
            · rintro ((⟨h1, _⟩ | ⟨_, h2⟩) | hm)
              · exact absurd h1 hua
              · exact Or.inl h2
              · exact Or.inr hm
            · rintro (rfl | hm)
              · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
              · exact Or.inr hm
          rw [hset, Finset.card_insert_of_notMem ha_not_f, hih]
          have hmem : u ∈ u :: c :: tl' := by simp
          simp [hmem, hua, hbl]
        · have hset :
              (Finset.univ : Finset α).filter (fun v => memEdge (a :: b :: c :: tl') u v) =
                (Finset.univ : Finset α).filter (fun v => memEdge (b :: c :: tl') u v) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [memEdge_cons_cons]
            constructor
            · rintro ((⟨h1, _⟩ | ⟨h1, _⟩) | hm)
              · exact absurd h1 hua
              · exact absurd h1 hub
              · exact hm
            · exact Or.inr
          rw [hset, ih u]
          by_cases hu_mem : u ∈ b :: c :: tl'
          · simp [hu_mem, hua, hub]
          · simp [hu_mem, hua]

private def toEdges {H : ℕ} (_hH : 0 < H) (w : List (SiteF H)) : GridEdges H where
  he r c := decide (if c = 0 then memEdge w (r, 0) (r, 1) else memEdge w (r, 1) (r, 2))
  ve r c :=
    if h : r.1 + 1 < H then decide (memEdge w (r, c) (⟨r.1 + 1, h⟩, c)) else c == 2

private lemma hasEdge_toEdges {H : ℕ} (hH : 0 < H) {w : List (SiteF H)}
    (hw : isWalkF H hH w) (u v : SiteF H) :
    hasEdge (toEdges hH w) u v = true ↔ memEdge w u v := by
  have hchain : ∀ {a b : SiteF H}, memEdge w a b → adjF a b = true := by
    have hc := hw.2.2.2
    clear hw
    intro a b hab
    induction w with
    | nil => simp [memEdge, pairsOf] at hab
    | cons x l ih =>
      cases l with
      | nil => exact absurd hab (memEdge_singleton x _ _)
      | cons y t =>
        rw [List.isChain_cons_cons] at hc
        rw [memEdge_cons_cons] at hab
        rcases hab with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hab
        · exact hc.1
        · have := hc.1
          simpa [adjF, Nat.dist_comm, add_comm] using this
        · exact ih hc.2 hab
  rcases u with ⟨r₁, c₁⟩
  rcases v with ⟨r₂, c₂⟩
  constructor
  · intro he
    unfold hasEdge at he
    by_cases hr : r₁ = r₂
    · subst hr
      simp only [↓reduceIte] at he
      fin_cases c₁ <;> fin_cases c₂ <;> simp [toEdges] at he
      · exact he
      · exact memEdge_symm he
      · exact he
      · exact memEdge_symm he
    · simp only [hr, ↓reduceIte] at he
      by_cases hc : c₁ = c₂
      · subst hc
        simp only [↓reduceIte] at he
        by_cases h1 : r₁.1 + 1 = r₂.1
        · have hlt : r₁.1 + 1 < H := h1 ▸ r₂.2
          have hreq : (⟨r₁.1 + 1, hlt⟩ : Fin H) = r₂ := Fin.ext h1
          simp only [h1, ↓reduceIte, toEdges] at he
          simpa [hreq] using he
        · simp only [h1, ↓reduceIte] at he
          by_cases h2 : r₂.1 + 1 = r₁.1
          · have hlt : r₂.1 + 1 < H := h2 ▸ r₁.2
            have hreq : (⟨r₂.1 + 1, hlt⟩ : Fin H) = r₁ := Fin.ext h2
            simp only [h2, ↓reduceIte, toEdges] at he
            have he' : memEdge w (r₂, c₁) (r₁, c₁) := by simpa [hreq] using he
            exact memEdge_symm he'
          · simp [h2] at he
      · simp [hc] at he
  · intro hm
    have hadj := hchain hm
    unfold adjF at hadj
    simp only [beq_iff_eq] at hadj
    unfold hasEdge toEdges
    by_cases hr : r₁ = r₂
    · subst hr
      have hdc : Nat.dist c₁.1 c₂.1 = 1 := by simpa [Nat.dist] using hadj
      fin_cases c₁ <;> fin_cases c₂ <;> simp_all [Nat.dist, memEdge_symm]
    · have hc : c₁ = c₂ := by
        have hne : r₁.1 ≠ r₂.1 := fun h => hr (Fin.ext h)
        have hd1 : 1 ≤ Nat.dist r₁.1 r₂.1 := Nat.dist_pos_of_ne hne
        have hd2 : Nat.dist c₁.1 c₂.1 = 0 := by omega
        unfold Nat.dist at hd2
        exact Fin.ext (by omega)
      subst hc
      have hdc : Nat.dist c₁.1 c₁.1 = 0 := Nat.dist_self _
      have hdr : Nat.dist r₁.1 r₂.1 = 1 := by omega
      have hdr_cases : r₁.1 + 1 = r₂.1 ∨ r₂.1 + 1 = r₁.1 := by
        unfold Nat.dist at hdr
        by_cases h : r₁.1 ≤ r₂.1 <;> omega
      rcases hdr_cases with h1 | h2
      · simp only [hr, ↓reduceIte, h1, r₂.2, ↓reduceDIte, decide_eq_true_eq]
        exact hm
      · have h1 : ¬ r₁.1 + 1 = r₂.1 := by omega
        simp only [hr, ↓reduceIte, h1, h2, r₁.2, ↓reduceDIte, decide_eq_true_eq]
        exact memEdge_symm hm

private lemma siteDeg_toEdges {H : ℕ} (hH : 0 < H) {w : List (SiteF H)}
    (hw : isWalkF H hH w) (u : SiteF H) :
    siteDeg (toEdges hH w) u.1 u.2 = if u ∈ w then 2 else 0 := by
  have hlast : ∀ c : Fin 3, (toEdges hH w).ve ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ c = (c == 2) := by
    intro c
    simp [toEdges, show ¬ H - 1 + 1 < H by omega]
  rw [← card_nbrs_eq hH (toEdges hH w) hlast u]
  have hf :
      ((Finset.univ : Finset (SiteF H)).filter (fun v => hasEdge (toEdges hH w) u v = true)).card =
        ((Finset.univ : Finset (SiteF H)).filter (fun v => memEdge w u v)).card :=
    congrArg Finset.card (Finset.ext fun v => by simp [hasEdge_toEdges hH hw])
  rw [hf]
  have hne : topSite hH ≠ botSite hH := fun h => by
    have := congrArg Prod.snd h
    simp [topSite, botSite] at this
  rw [card_filter_memEdge hw.1 hw.2.1 hne hw.2.2.1 u]
  dsimp only [topSite, botSite] at *
  by_cases huw : u ∈ w
  · simp only [huw, ↓reduceIte]
    by_cases hut : u = ((⟨0, hH⟩, 0) : SiteF H)
    · subst hut
      have hne' : ((⟨0, hH⟩, 0) : SiteF H) ≠ ((⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2) : SiteF H) :=
        hne
      simp [hne']
    · by_cases hub : u = ((⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2) : SiteF H)
      · subst hub
        have hne' : ((⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2) : SiteF H) ≠ ((⟨0, hH⟩, 0) : SiteF H) :=
          Ne.symm hne
        simp [hne']
      · simp [hut, hub]
  · have hut : u ≠ ((⟨0, hH⟩, 0) : SiteF H) := fun h => huw (h ▸ List.mem_of_mem_head? hw.1)
    have hub : u ≠ ((⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩, 2) : SiteF H) := fun h =>
      huw (h ▸ getLast?_mem hw.2.1)
    simp [huw, hut, hub]

private lemma toEdges_good {H : ℕ} (hH : 0 < H) {w : List (SiteF H)} (hw : isWalkF H hH w) :
    GoodEdges H hH (toEdges hH w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    simp [toEdges, show ¬ H - 1 + 1 < H by omega]
  · intro r c
    rw [siteDeg_toEdges hH hw (r, c)]
    split_ifs <;> simp
  · intro u hu
    rw [siteDeg_toEdges hH hw u] at hu
    have huw : u ∈ w := by
      by_contra h
      simp [h] at hu
    have hreach : ∀ {l : List (SiteF H)} {a : SiteF H},
        l.head? = some a → List.IsChain (fun x y => memEdge w x y) l →
        ∀ x ∈ l, Relation.ReflTransGen (fun p q => hasEdge (toEdges hH w) p q = true) a x := by
      intro l
      induction l with
      | nil => simp
      | cons hd tl ih =>
        intro a hhd hc x hx
        simp only [List.head?_cons, Option.some.injEq] at hhd
        subst hhd
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Relation.ReflTransGen.refl
        · cases tl with
          | nil => simp at hx'
          | cons nxt tl' =>
            rw [List.isChain_cons_cons] at hc
            have hstep : hasEdge (toEdges hH w) hd nxt = true :=
              (hasEdge_toEdges hH hw hd nxt).mpr hc.1
            have hsub := ih rfl hc.2 x hx'
            exact Relation.ReflTransGen.head hstep hsub
    have hcw : List.IsChain (fun x y => memEdge w x y) w := by
      have hsub : ∀ l : List (SiteF H),
          (∀ p ∈ pairsOf l, memEdge w p.1 p.2) →
          List.IsChain (fun x y => memEdge w x y) l := by
        intro l hl
        induction l with
        | nil => simp
        | cons a l ih =>
          cases l with
          | nil => simp
          | cons b t =>
            rw [List.isChain_cons_cons]
            refine ⟨hl (a, b) (by simp [pairsOf]), ih fun p hp => hl p ?_⟩
            simp only [pairsOf, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp ⊢
            exact Or.inr hp
      exact hsub w fun p hp => Or.inl hp
    exact hreach hw.1 hcw u huw

private lemma GridEdges.ext_edges {H : ℕ} (hH : 0 < H) {g₁ g₂ : GridEdges H}
    (hedge : ∀ u v : SiteF H, hasEdge g₁ u v = hasEdge g₂ u v)
    (hlast : ∀ c : Fin 3, g₁.ve ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ c =
      g₂.ve ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ c) :
    g₁ = g₂ := by
  refine GridEdges.ext' ?_ ?_
  · funext r c
    fin_cases c
    · have := hedge (r, 0) (r, 1)
      simpa [hasEdge] using this
    · have := hedge (r, 1) (r, 2)
      simpa [hasEdge] using this
  · funext r c
    by_cases hr : r.1 + 1 < H
    · have := r.2
      have hne : r ≠ ⟨r.1 + 1, hr⟩ := fun h => by
        have h1 := congrArg Fin.val h; dsimp at h1; omega
      simpa [hasEdge, hne] using hedge (r, c) (⟨r.1 + 1, hr⟩, c)
    · have := r.2
      have hreq : r = ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ := Fin.ext (by dsimp; omega)
      rw [hreq]
      exact hlast c

private def siteList (H : ℕ) : List (SiteF H) :=
  (List.finRange H).flatMap fun r => (List.finRange 3).map fun c => (r, c)

private lemma mem_siteList {H : ℕ} (u : SiteF H) : u ∈ siteList H := by
  rcases u with ⟨r, c⟩
  simp [siteList]

private def startNbr {H : ℕ} (hH : 0 < H) (g : GridEdges H) : SiteF H :=
  ((siteList H).find? (fun v => hasEdge g (topSite hH) v)).getD (topSite hH)

private def greedyNext {H : ℕ} (g : GridEdges H) (prev cur : SiteF H) : SiteF H :=
  ((siteList H).find? (fun v => hasEdge g cur v && v != prev)).getD cur

private def orbit {H : ℕ} (hH : 0 < H) (g : GridEdges H) : ℕ → SiteF H × SiteF H
  | 0 => (topSite hH, startNbr hH g)
  | k + 1 => ((orbit hH g k).2, greedyNext g (orbit hH g k).1 (orbit hH g k).2)

private def pt {H : ℕ} (hH : 0 < H) (g : GridEdges H) (k : ℕ) : SiteF H :=
  if k = 0 then topSite hH else (orbit hH g (k - 1)).2

private lemma top_active_good {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    siteDeg g (topSite hH).1 (topSite hH).2 = 2 := by
  have h1 : 1 ≤ siteDeg g (topSite hH).1 (topSite hH).2 := by
    simp [siteDeg, topCutG, topSite]
    omega
  rcases hg.2.1 (topSite hH).1 (topSite hH).2 with h0 | h2
  · omega
  · exact h2

private lemma card_nbrs_top {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    ((Finset.univ : Finset (SiteF H)).filter (fun v => hasEdge g (topSite hH) v = true)).card = 1 := by
  have hc := card_nbrs_eq hH g hg.1 (topSite hH)
  have hne : topSite hH ≠ botSite hH := fun h => by
    have := congrArg Prod.snd h
    simp [topSite, botSite] at this
  have h2 := top_active_good hH hg
  simp only [↓reduceIte, hne, h2] at hc
  omega

private lemma startNbr_spec {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    hasEdge g (topSite hH) (startNbr hH g) = true ∧
      ∀ v : SiteF H, hasEdge g (topSite hH) v = true ↔ v = startNbr hH g := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [card_nbrs_top hH hg]; exact Nat.one_pos)
  rw [Finset.mem_filter] at hu
  have hne : (siteList H).find? (fun v => hasEdge g (topSite hH) v) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    exact hnone u (mem_siteList u) hu.2
  cases hf : (siteList H).find? (fun v => hasEdge g (topSite hH) v) with
  | none => exact absurd hf hne
  | some s =>
    have hs : hasEdge g (topSite hH) s = true := List.find?_some hf
    have hsn : startNbr hH g = s := by simp [startNbr, hf]
    rw [hsn]
    refine ⟨hs, fun v => ⟨fun hv => ?_, fun hv => hv ▸ hs⟩⟩
    have hc1 : ({s, v} : Finset (SiteF H)).card ≤ 1 := by
      rw [← card_nbrs_top hH hg]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [Finset.mem_filter, hs, hv]
    by_contra hvne
    rw [Finset.card_pair (Ne.symm hvne)] at hc1
    omega

private lemma greedyNext_spec {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g)
    {prev cur : SiteF H} (hpc : hasEdge g prev cur = true)
    (htop : cur ≠ topSite hH) (hbot : cur ≠ botSite hH) :
    hasEdge g cur (greedyNext g prev cur) = true ∧
      greedyNext g prev cur ≠ prev ∧
      ∀ v : SiteF H, hasEdge g cur v = true ↔ v = prev ∨ v = greedyNext g prev cur := by
  have hcur_deg : siteDeg g cur.1 cur.2 = 2 := by
    have hpos : 0 < ((Finset.univ : Finset (SiteF H)).filter
        (fun v => hasEdge g cur v = true)).card :=
      Finset.card_pos.mpr ⟨prev, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rw [hasEdge_symm]; exact hpc⟩⟩
    have hc := card_nbrs_eq hH g hg.1 cur
    rcases hg.2.1 cur.1 cur.2 with h0 | h2
    · omega
    · exact h2
  have hc2 : ((Finset.univ : Finset (SiteF H)).filter (fun v => hasEdge g cur v = true)).card = 2 := by
    have hc := card_nbrs_eq hH g hg.1 cur
    simp [htop, hbot, hcur_deg] at hc
    exact hc
  let S := (Finset.univ : Finset (SiteF H)).filter (fun v => hasEdge g cur v = true)
  have hprev_mem : prev ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by rw [hasEdge_symm]; exact hpc⟩
  have herase : (S.erase prev).card = 1 := by
    rw [Finset.card_erase_of_mem hprev_mem, hc2]
  obtain ⟨nxt, hnxt_eq⟩ := Finset.card_eq_one.mp herase
  have hnxt_mem : nxt ∈ S.erase prev := hnxt_eq ▸ Finset.mem_singleton_self nxt
  rw [Finset.mem_erase, Finset.mem_filter] at hnxt_mem
  have hne : (siteList H).find? (fun v => hasEdge g cur v && v != prev) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    exact hnone nxt (mem_siteList nxt) (by simp [hnxt_mem.2.2, hnxt_mem.1])
  cases hf : (siteList H).find? (fun v => hasEdge g cur v && v != prev) with
  | none => exact absurd hf hne
  | some s =>
    have hs := List.find?_some hf
    simp only [Bool.and_eq_true, bne_iff_ne] at hs
    have hgn : greedyNext g prev cur = s := by simp [greedyNext, hf]
    rw [hgn]
    have hsnxt : s = nxt := by
      have hm : s ∈ S.erase prev := Finset.mem_erase.mpr
        ⟨hs.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1⟩⟩
      rw [hnxt_eq, Finset.mem_singleton] at hm
      exact hm
    refine ⟨hs.1, hs.2, fun v => ?_⟩
    constructor
    · intro hv
      by_cases hvp : v = prev
      · exact Or.inl hvp
      · have hm : v ∈ S.erase prev := Finset.mem_erase.mpr
          ⟨hvp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
        rw [hnxt_eq, Finset.mem_singleton] at hm
        exact Or.inr (hm.trans hsnxt.symm)
    · rintro (rfl | rfl)
      · rw [hasEdge_symm]; exact hpc
      · exact hs.1

private lemma pt_succ_orbit {H : ℕ} (hH : 0 < H) (g : GridEdges H) (k : ℕ) :
    orbit hH g k = (pt hH g k, pt hH g (k + 1)) := by
  cases k <;> rfl

private lemma pt_add_two {H : ℕ} (hH : 0 < H) (g : GridEdges H) (k : ℕ) :
    pt hH g (k + 2) = greedyNext g (pt hH g k) (pt hH g (k + 1)) := by
  have h1 := congrArg Prod.snd (pt_succ_orbit hH g (k + 1))
  dsimp only [orbit] at h1
  rw [pt_succ_orbit hH g k] at h1
  exact h1.symm

private lemma pt_inj_of_no_bot {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g)
    (M : ℕ) (hnb : ∀ r : ℕ, 1 ≤ r → r < M → pt hH g r ≠ botSite hH) :
    ∀ i j : ℕ, i < j → j ≤ M → pt hH g i ≠ pt hH g j := by
  intro i j hij hjM heq
  have hex : ∃ j : ℕ, j ≤ M ∧ ∃ i : ℕ, i < j ∧ pt hH g i = pt hH g j := ⟨j, hjM, i, hij, heq⟩
  classical
  let j₀ := Nat.find hex
  have hj₀ : j₀ ≤ M ∧ ∃ i : ℕ, i < j₀ ∧ pt hH g i = pt hH g j₀ := Nat.find_spec hex
  have hmin : ∀ r : ℕ, r < j₀ → ∀ i : ℕ, i < r → pt hH g i ≠ pt hH g r := fun r hr i hir h =>
    Nat.find_min hex hr ⟨by omega, i, hir, h⟩
  obtain ⟨i₀, hi₀j, hi₀eq⟩ := hj₀.2
  have hstep : ∀ r : ℕ, r < j₀ →
      hasEdge g (pt hH g r) (pt hH g (r + 1)) = true ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ r → pt hH g t ≠ topSite hH) ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ r → pt hH g t ≠ botSite hH) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨(startNbr_spec hH hg).1, fun t ht1 ht0 => by omega, fun t ht1 ht0 => by omega⟩
    | succ r ih =>
      intro hr
      have ihr := ih (by omega)
      have hrtop : pt hH g (r + 1) ≠ topSite hH := (hmin (r + 1) hr 0 (Nat.succ_pos r)).symm
      have hrbot : pt hH g (r + 1) ≠ botSite hH := hnb (r + 1) (by omega) (by omega)
      have hgn := greedyNext_spec hH hg ihr.1 hrtop hrbot
      rw [← pt_add_two hH g r] at hgn
      refine ⟨hgn.1, fun t ht1 htr => ?_, fun t ht1 htr => ?_⟩
      · rcases eq_or_lt_of_le htr with rfl | hlt
        · exact hrtop
        · exact ihr.2.1 t ht1 (by omega)
      · rcases eq_or_lt_of_le htr with rfl | hlt
        · exact hrbot
        · exact ihr.2.2 t ht1 (by omega)
  have hj₀pos : 0 < j₀ := by omega
  have hej : hasEdge g (pt hH g (j₀ - 1)) (pt hH g j₀) = true := by
    have := (hstep (j₀ - 1) (by omega)).1
    rwa [show j₀ - 1 + 1 = j₀ by omega] at this
  by_cases hi₀0 : i₀ = 0
  · subst hi₀0
    have hj_nbr : hasEdge g (topSite hH) (pt hH g (j₀ - 1)) = true := by
      have htop_eq : pt hH g 0 = topSite hH := rfl
      rw [hasEdge_symm, ← hi₀eq, htop_eq] at hej
      exact hej
    have hj1 : pt hH g (j₀ - 1) = pt hH g 1 := ((startNbr_spec hH hg).2 _).mp hj_nbr
    have hj_gt2 : 2 < j₀ := by
      by_contra hle
      have hj2 : j₀ = 2 := by
        have : j₀ ≠ 1 := by
          intro h1
          have := h1 ▸ hi₀eq
          exact hasEdge_ne (startNbr_spec hH hg).1 this
        omega
      have hi₀eq2 : pt hH g 0 = pt hH g 2 := by simpa [hj2] using hi₀eq
      have hgn := greedyNext_spec hH hg (startNbr_spec hH hg).1
        (hmin 1 (by omega) 0 (by omega)).symm (hnb 1 le_rfl (by omega))
      have hpt0 : pt hH g 0 = topSite hH := rfl
      have hpt1 : pt hH g 1 = startNbr hH g := rfl
      have hpt2 := pt_add_two hH g 0
      rw [hpt0, hpt1] at hpt2
      rw [← hpt2] at hgn
      exact hgn.2.1 hi₀eq2.symm
    exact hmin (j₀ - 1) (by omega) 1 (by omega) hj1.symm
  · have hi₀_top : pt hH g i₀ ≠ topSite hH :=
      (hstep (j₀ - 1) (by omega)).2.1 i₀ (by omega) (by omega)
    have hi₀_bot : pt hH g i₀ ≠ botSite hH :=
      (hstep (j₀ - 1) (by omega)).2.2 i₀ (by omega) (by omega)
    have hei : hasEdge g (pt hH g (i₀ - 1)) (pt hH g i₀) = true := by
      have := (hstep (i₀ - 1) (by omega)).1
      rwa [show i₀ - 1 + 1 = i₀ by omega] at this
    have hgn := greedyNext_spec hH hg hei hi₀_top hi₀_bot
    have hpt_succ : pt hH g (i₀ + 1) = greedyNext g (pt hH g (i₀ - 1)) (pt hH g i₀) := by
      have h2 := pt_add_two hH g (i₀ - 1)
      rwa [show i₀ - 1 + 2 = i₀ + 1 by omega, show i₀ - 1 + 1 = i₀ by omega] at h2
    rw [← hpt_succ] at hgn
    have hj_nbr : hasEdge g (pt hH g i₀) (pt hH g (j₀ - 1)) = true := by
      rw [hasEdge_symm, ← hi₀eq] at hej
      exact hej
    rcases (hgn.2.2 (pt hH g (j₀ - 1))).mp hj_nbr with hp | hn
    · exact hmin (j₀ - 1) (by omega) (i₀ - 1) (by omega) hp.symm
    · have hj_ne1 : j₀ ≠ i₀ + 1 := fun h1 => by
        have hed := hasEdge_adj (hstep i₀ (by omega)).1
        rw [← h1, ← hi₀eq] at hed
        simp [adjF, Nat.dist] at hed
      by_cases hj_eq : j₀ = i₀ + 2
      · have hi₀eq2 : pt hH g i₀ = pt hH g (i₀ + 2) := by simpa [hj_eq] using hi₀eq
        have hgn2 := greedyNext_spec hH hg hgn.1
          (hmin (i₀ + 1) (by omega) 0 (by omega)).symm (hnb (i₀ + 1) (by omega) (by omega))
        rw [← pt_add_two hH g i₀] at hgn2
        exact hgn2.2.1 hi₀eq2.symm
      · exact hmin (j₀ - 1) (by omega) (i₀ + 1) (by omega) hn.symm

private lemma pt_reaches_bot {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 3 * H ∧ pt hH g r = botSite hH := by
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  have hnb : ∀ r : ℕ, 1 ≤ r → r < 3 * H + 1 → pt hH g r ≠ botSite hH := fun r hr1 hrm =>
    hnone r hr1 (by omega)
  let l := (List.range (3 * H + 1)).map (pt hH g)
  have hnd : l.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    have ha := a.2; have hb := b.2
    have hlen : l.length = 3 * H + 1 := by simp [l]
    dsimp [l] at hab
    simp only [List.getElem_map, List.getElem_range] at hab
    rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exact absurd hab (pt_inj_of_no_bot hH hg (3 * H + 1) hnb a.1 b.1 hlt (by omega))
    · exact Fin.ext heq
    · exact absurd hab.symm (pt_inj_of_no_bot hH hg (3 * H + 1) hnb b.1 a.1 hgt (by omega))
  have hle := hnd.length_le_card
  have hcard : Fintype.card (SiteF H) = 3 * H := by
    simp [SiteF, mul_comm]
  have hlen : l.length = 3 * H + 1 := by simp [l]
  omega

private noncomputable def toWalk {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    List (SiteF H) :=
  let K := Nat.find (pt_reaches_bot hH hg)
  (List.range (K + 1)).map (pt hH g)

private lemma toWalk_isWalkF {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    isWalkF H hH (toWalk hH hg) := by
  classical
  let K := Nat.find (pt_reaches_bot hH hg)
  have hK := Nat.find_spec (pt_reaches_bot hH hg)
  have hmin : ∀ r : ℕ, 1 ≤ r → r < K → pt hH g r ≠ botSite hH := fun r hr1 hrK heq =>
    Nat.find_min (pt_reaches_bot hH hg) hrK ⟨hr1, by omega, heq⟩
  have hnd : (toWalk hH hg).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    have hlen : (toWalk hH hg).length = K + 1 := by simp [toWalk, K]
    have ha : a.1 < K + 1 := hlen ▸ a.2
    have hb : b.1 < K + 1 := hlen ▸ b.2
    have hget : ∀ (j : ℕ) (hj : j < (toWalk hH hg).length), (toWalk hH hg)[j] = pt hH g j := by
      intro j hj
      dsimp only [toWalk] at hj ⊢
      simp only [List.getElem_map, List.getElem_range]
    dsimp only at hab
    rw [hget a.1 a.2, hget b.1 b.2] at hab
    rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exact absurd hab (pt_inj_of_no_bot hH hg K hmin a.1 b.1 hlt (by omega))
    · exact Fin.ext heq
    · exact absurd hab.symm (pt_inj_of_no_bot hH hg K hmin b.1 a.1 hgt (by omega))
  have hhead : (toWalk hH hg).head? = some (topSite hH) := by
    have hne : (List.range (K + 1)).map (pt hH g) ≠ [] := by simp
    dsimp [toWalk]
    rw [List.head?_eq_some_head hne, List.head_eq_getElem]
    simp only [Option.some.injEq]
    rw [List.getElem_map, List.getElem_range]
    rfl
  have hlast : (toWalk hH hg).getLast? = some (botSite hH) := by
    dsimp [toWalk]
    have hne : (List.range (K + 1)).map (pt hH g) ≠ [] := by simp
    rw [List.getLast?_eq_some_getLast hne, List.getLast_map]
    simp only [List.getLast_range, Option.some.injEq, Nat.add_sub_cancel]
    exact hK.2.2
  have hchain : List.IsChain (fun a b => adjF a b = true) (toWalk hH hg) := by
    have hedge : ∀ r : ℕ, r < K → hasEdge g (pt hH g r) (pt hH g (r + 1)) = true := by
      intro r
      induction r with
      | zero => intro _; exact (startNbr_spec hH hg).1
      | succ r ih =>
        intro hr
        have ihr := ih (by omega)
        have htop : pt hH g (r + 1) ≠ topSite hH := fun heq =>
          pt_inj_of_no_bot hH hg K hmin 0 (r + 1) (Nat.succ_pos r) (by omega) heq.symm
        have hbot : pt hH g (r + 1) ≠ botSite hH := hmin (r + 1) (by omega) hr
        have hgn := greedyNext_spec hH hg ihr htop hbot
        rw [← pt_add_two hH g r] at hgn
        exact hgn.1
    rw [List.isChain_iff_getElem]
    intro i hi
    have hlen : (toWalk hH hg).length = K + 1 := by simp [toWalk, K]
    have hiK : i < K := by omega
    have hget : ∀ (j : ℕ) (hj : j < (toWalk hH hg).length), (toWalk hH hg)[j] = pt hH g j := by
      intro j hj
      dsimp only [toWalk] at hj ⊢
      simp only [List.getElem_map, List.getElem_range]
    rw [hget i _, hget (i + 1) _]
    exact hasEdge_adj (hedge i hiK)
  exact ⟨hhead, hlast, hnd, hchain⟩

private lemma toEdges_toWalk {H : ℕ} (hH : 0 < H) {g : GridEdges H} (hg : GoodEdges H hH g) :
    toEdges hH (toWalk hH hg) = g := by
  classical
  let w := toWalk hH hg
  let K := Nat.find (pt_reaches_bot hH hg)
  have hK := Nat.find_spec (pt_reaches_bot hH hg)
  have hmin : ∀ r : ℕ, 1 ≤ r → r < K → pt hH g r ≠ botSite hH := fun r hr1 hrK heq =>
    Nat.find_min (pt_reaches_bot hH hg) hrK ⟨hr1, by omega, heq⟩
  have hwf := toWalk_isWalkF hH hg
  have hpt_mem : ∀ r : ℕ, r ≤ K → pt hH g r ∈ w := fun r hr => by
    dsimp [w, toWalk]
    exact List.mem_map.mpr ⟨r, List.mem_range.mpr (by omega), rfl⟩
  have hedge_pt : ∀ r : ℕ, r < K → hasEdge g (pt hH g r) (pt hH g (r + 1)) = true := by
    intro r
    induction r with
    | zero => intro _; exact (startNbr_spec hH hg).1
    | succ r ih =>
      intro hr
      have ihr := ih (by omega)
      have htop : pt hH g (r + 1) ≠ topSite hH := fun heq =>
        pt_inj_of_no_bot hH hg K hmin 0 (r + 1) (Nat.succ_pos r) (by omega) heq.symm
      have hbot : pt hH g (r + 1) ≠ botSite hH := hmin (r + 1) (by omega) hr
      have hgn := greedyNext_spec hH hg ihr htop hbot
      rw [← pt_add_two hH g r] at hgn
      exact hgn.1
  have hpair_pt : ∀ r : ℕ, r < K → memEdge w (pt hH g r) (pt hH g (r + 1)) := fun r hr => by
    have hw_len : w.length = K + 1 := by simp [w, toWalk, K]
    have hmem_zip : (pt hH g r, pt hH g (r + 1)) ∈ pairsOf w := by
      rw [pairsOf, List.mem_iff_getElem]
      refine ⟨r, by simp only [List.length_zip, List.length_tail, hw_len]; omega, ?_⟩
      simp only [List.getElem_zip, List.getElem_tail, w, toWalk, List.getElem_map,
        List.getElem_range]
    exact Or.inl hmem_zip
  have hclosed : ∀ {u v : SiteF H}, u ∈ w → hasEdge g u v = true → memEdge w u v := by
    intro u v huw huv
    dsimp [w, toWalk] at huw
    rcases List.mem_map.mp huw with ⟨r, hr, rfl⟩
    rw [List.mem_range] at hr
    have hrK_le : r ≤ K := by dsimp [K] at hr ⊢; omega
    by_cases hr0 : r = 0
    · subst hr0
      have hv1 : v = pt hH g 1 := ((startNbr_spec hH hg).2 v).mp huv
      rw [hv1]
      exact hpair_pt 0 hK.1
    · by_cases hrK : r = K
      · subst hrK
        have hbot : pt hH g K = botSite hH := hK.2.2
        have hbot_deg : siteDeg g (botSite hH).1 (botSite hH).2 = 2 := by
          have h1 : 1 ≤ siteDeg g (botSite hH).1 (botSite hH).2 := by
            unfold siteDeg botSite
            rw [hg.1 2]
            simp
            omega
          rcases hg.2.1 (botSite hH).1 (botSite hH).2 with h0 | h2
          · omega
          · exact h2
        have hc1 : ((Finset.univ : Finset (SiteF H)).filter
            (fun x => hasEdge g (botSite hH) x = true)).card = 1 := by
          have hc := card_nbrs_eq hH g hg.1 (botSite hH)
          have hne : botSite hH ≠ topSite hH := fun h => by
            have := congrArg Prod.snd h
            simp [topSite, botSite] at this
          simp [hne, hbot_deg] at hc
          omega
        have hp_nbr : hasEdge g (botSite hH) (pt hH g (K - 1)) = true := by
          rw [← hbot, hasEdge_symm]
          have := hedge_pt (K - 1) (by omega)
          rwa [show K - 1 + 1 = K by omega] at this
        have hv_nbr : hasEdge g (botSite hH) v = true := by rwa [← hbot]
        have hcard_le : ({v, pt hH g (K - 1)} : Finset (SiteF H)).card ≤ 1 := by
          refine le_trans (Finset.card_le_card fun x hx => ?_) (le_of_eq hc1)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_nbr⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp_nbr⟩
        have hveq : v = pt hH g (K - 1) := by
          by_contra hne
          rw [Finset.card_pair hne] at hcard_le
          omega
        rw [hveq]
        exact memEdge_symm (by simpa [show K - 1 + 1 = K by omega] using hpair_pt (K - 1) (by omega))
      · have htop : pt hH g r ≠ topSite hH := fun heq =>
          pt_inj_of_no_bot hH hg K hmin 0 r (by omega) (by omega) heq.symm
        have hbot : pt hH g r ≠ botSite hH := hmin r (by omega) (by omega)
        have hprev : hasEdge g (pt hH g (r - 1)) (pt hH g r) = true := by
          have := hedge_pt (r - 1) (by omega)
          rwa [show r - 1 + 1 = r by omega] at this
        have hgn := greedyNext_spec hH hg hprev htop hbot
        have hpt_succ : pt hH g (r + 1) = greedyNext g (pt hH g (r - 1)) (pt hH g r) := by
          have h2 := pt_add_two hH g (r - 1)
          rwa [show r - 1 + 2 = r + 1 by omega, show r - 1 + 1 = r by omega] at h2
        rw [← hpt_succ] at hgn
        rcases (hgn.2.2 v).mp huv with rfl | rfl
        · exact memEdge_symm (by simpa [show r - 1 + 1 = r by omega] using hpair_pt (r - 1) (by omega))
        · exact hpair_pt r (by omega)
  have hall_active : ∀ u : SiteF H, siteDeg g u.1 u.2 = 2 → u ∈ w := by
    intro u hu
    have hreach := hg.2.2 u hu
    clear hu
    induction hreach with
    | refl => exact hpt_mem 0 (Nat.zero_le K)
    | @tail y z _ hyz ih => exact (mem_of_memEdge (hclosed ih hyz)).2
  refine GridEdges.ext_edges hH (fun u v => ?_) (fun c => ?_)
  · rw [Bool.eq_iff_iff, hasEdge_toEdges hH hwf]
    constructor
    · intro hm
      dsimp [w, toWalk] at hm
      rcases hm with h | h
      · obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h
        simp only [pairsOf, List.length_zip, List.length_map, List.length_range,
          List.length_tail] at hi
        simp only [pairsOf, List.getElem_zip, List.getElem_tail, List.getElem_map,
          List.getElem_range] at heq
        have hu : u = pt hH g i := (Prod.ext_iff.mp heq).1.symm
        have hv : v = pt hH g (i + 1) := (Prod.ext_iff.mp heq).2.symm
        rw [hu, hv]
        exact hedge_pt i (by dsimp [K] at hi ⊢; omega)
      · obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h
        simp only [pairsOf, List.length_zip, List.length_map, List.length_range,
          List.length_tail] at hi
        simp only [pairsOf, List.getElem_zip, List.getElem_tail, List.getElem_map,
          List.getElem_range] at heq
        have hv : v = pt hH g i := (Prod.ext_iff.mp heq).1.symm
        have hu : u = pt hH g (i + 1) := (Prod.ext_iff.mp heq).2.symm
        rw [hu, hv, hasEdge_symm]
        exact hedge_pt i (by dsimp [K] at hi ⊢; omega)
    · intro huv
      have hu_act : siteDeg g u.1 u.2 = 2 := by
        have hpos : 0 < ((Finset.univ : Finset (SiteF H)).filter
            (fun x => hasEdge g u x = true)).card :=
          Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩⟩
        have hc := card_nbrs_eq hH g hg.1 u
        rcases hg.2.1 u.1 u.2 with h0 | h2
        · omega
        · exact h2
      exact hclosed (hall_active u hu_act) huv
  · have h1 := hg.1 c
    have h2 : (toEdges hH w).ve ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ c = (c == 2) := by
      simp [toEdges, show ¬ H - 1 + 1 < H by omega]
    rw [h1, h2]

private lemma toWalk_toEdges {H : ℕ} (hH : 0 < H) {w : List (SiteF H)} (hw : isWalkF H hH w) :
    toWalk hH (toEdges_good hH hw) = w := by
  classical
  let g := toEdges hH w
  let hg := toEdges_good hH hw
  have hlen : 2 ≤ w.length := by
    by_contra hlt
    cases w with
    | nil => simp [isWalkF] at hw
    | cons a l =>
      cases l with
      | nil =>
        have ha : a = topSite hH := Option.some.inj hw.1
        have hb : a = botSite hH := Option.some.inj hw.2.1
        have := congrArg Prod.snd (ha.symm.trans hb)
        simp [topSite, botSite] at this
      | cons _ _ => simp at hlt
  have hpt : ∀ k : ℕ, (hk : k < w.length) → pt hH g k = w[k] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases m with _ | k
      · have := hw.1
        cases w with
        | nil => simp at hlen
        | cons a l => exact (Option.some.inj this).symm
      · by_cases hk0 : k = 0
        · subst hk0
          have he01 : hasEdge g (topSite hH) w[1] = true := by
            rw [hasEdge_toEdges hH hw]
            have h0 : w[0] = topSite hH := by
              have := hw.1
              cases w with
              | nil => simp at hlen
              | cons a l => exact Option.some.inj this
            rw [← h0]
            have hm1 : (w[0], w[1]) ∈ pairsOf w := by
              rw [pairsOf, List.mem_iff_getElem]
              exact ⟨0, by simp; omega, by simp [List.getElem_zip, List.getElem_tail]⟩
            exact Or.inl hm1
          have h1 : pt hH g 1 = startNbr hH g := rfl
          rw [h1]
          exact (((startNbr_spec hH hg).2 w[1]).mp he01).symm
        · have ihk := ih k (by omega) (by omega)
          have ihk1 : pt hH g (k - 1) = w[k - 1] := ih (k - 1) (by omega) (by omega)
          have hprev : hasEdge g (pt hH g (k - 1)) (pt hH g k) = true := by
            rw [ihk, ihk1, hasEdge_toEdges hH hw]
            have hm1 : (w[k - 1], w[k]) ∈ pairsOf w := by
              rw [pairsOf, List.mem_iff_getElem]
              refine ⟨k - 1, by simp; omega, ?_⟩
              simp [List.getElem_zip, List.getElem_tail, show k - 1 + 1 = k by omega]
            exact Or.inl hm1
          have htop : pt hH g k ≠ topSite hH := by
            rw [ihk]
            have h0 : w[0] = topSite hH := by
              cases w with
              | nil => simp at hlen
              | cons a l => exact Option.some.inj hw.1
            rw [← h0]
            intro heq
            have heq' : (fun i : Fin w.length => w[i.1]) ⟨k, by omega⟩ =
                (fun i : Fin w.length => w[i.1]) ⟨0, by omega⟩ := heq
            have hfin := List.nodup_iff_injective_getElem.mp hw.2.2.1 heq'
            have := congrArg Fin.val hfin
            dsimp at this
            omega
          have hbot : pt hH g k ≠ botSite hH := by
            rw [ihk]
            have hlast : w[w.length - 1] = botSite hH := by
              have := hw.2.1
              rw [List.getLast?_eq_some_getLast (by intro h; simp [h] at hlen),
                List.getLast_eq_getElem] at this
              exact Option.some.inj this
            rw [← hlast]
            intro heq
            have heq' : (fun i : Fin w.length => w[i.1]) ⟨k, by omega⟩ =
                (fun i : Fin w.length => w[i.1]) ⟨w.length - 1, by omega⟩ := heq
            have hfin := List.nodup_iff_injective_getElem.mp hw.2.2.1 heq'
            have := congrArg Fin.val hfin
            dsimp at this
            omega
          have hgn := greedyNext_spec hH hg hprev htop hbot
          have hpt_succ : pt hH g (k + 1) = greedyNext g (pt hH g (k - 1)) (pt hH g k) := by
            have h2 := pt_add_two hH g (k - 1)
            rwa [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at h2
          have he_next : hasEdge g (pt hH g k) w[k + 1] = true := by
            rw [ihk, hasEdge_toEdges hH hw]
            have hm1 : (w[k], w[k + 1]) ∈ pairsOf w := by
              rw [pairsOf, List.mem_iff_getElem]
              exact ⟨k, by simp; omega, by simp [List.getElem_zip, List.getElem_tail]⟩
            exact Or.inl hm1
          have hne_prev : w[k + 1] ≠ pt hH g (k - 1) := by
            rw [ihk1]
            intro heq
            have heq' : (fun i : Fin w.length => w[i.1]) ⟨k + 1, hm⟩ =
                (fun i : Fin w.length => w[i.1]) ⟨k - 1, by omega⟩ := heq
            have hfin := List.nodup_iff_injective_getElem.mp hw.2.2.1 heq'
            have := congrArg Fin.val hfin
            dsimp at this
            omega
          rcases (hgn.2.2 w[k + 1]).mp he_next with h | h
          · exact absurd h hne_prev
          · rw [hpt_succ, h]
  have hKeq : Nat.find (pt_reaches_bot hH hg) = w.length - 1 := by
    have hbot_w : pt hH g (w.length - 1) = botSite hH := by
      rw [hpt (w.length - 1) (by omega)]
      have := hw.2.1
      rw [List.getLast?_eq_some_getLast (by intro h; simp [h] at hlen),
        List.getLast_eq_getElem] at this
      exact Option.some.inj this
    have hle_K : Nat.find (pt_reaches_bot hH hg) ≤ w.length - 1 := by
      refine Nat.find_min' (pt_reaches_bot hH hg) ⟨by omega, ?_, hbot_w⟩
      have hcard := hw.2.2.1.length_le_card
      have hfc : Fintype.card (SiteF H) = 3 * H := by simp [SiteF, mul_comm]
      omega
    by_contra hne
    have hlt : Nat.find (pt_reaches_bot hH hg) < w.length - 1 := lt_of_le_of_ne hle_K hne
    have hspec := Nat.find_spec (pt_reaches_bot hH hg)
    rw [hpt _ (by omega)] at hspec
    have hlast : w[w.length - 1] = botSite hH := by
      have := hw.2.1
      rw [List.getLast?_eq_some_getLast (by intro h; simp [h] at hlen),
        List.getLast_eq_getElem] at this
      exact Option.some.inj this
    have heq' : (fun i : Fin w.length => w[i.1]) ⟨Nat.find (pt_reaches_bot hH hg), by omega⟩ =
        (fun i : Fin w.length => w[i.1]) ⟨w.length - 1, by omega⟩ :=
      hspec.2.2.trans hlast.symm
    have hfin := List.nodup_iff_injective_getElem.mp hw.2.2.1 heq'
    have := congrArg Fin.val hfin
    dsimp at this
    omega
  refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
  · simp [toWalk, hKeq]
    omega
  · simp only [toWalk, List.getElem_map, List.getElem_range]
    exact hpt i hi2

private noncomputable def walkF_equiv_goodEdges (n : ℕ) :
    {w : List (SiteF (2 * n + 1)) //
      isWalkF (2 * n + 1) (Nat.succ_pos _) w ∧ (⟨n, by omega⟩, (1 : Fin 3)) ∈ w} ≃
      {g : GridEdges (2 * n + 1) //
        GoodEdges (2 * n + 1) (Nat.succ_pos _) g ∧
        siteDeg g ⟨n, by omega⟩ 1 = 2} :=
  { toFun := fun ⟨w, hw, hmid⟩ =>
      ⟨toEdges (Nat.succ_pos _) w, toEdges_good (Nat.succ_pos _) hw, by
        have := siteDeg_toEdges (Nat.succ_pos _) hw (⟨n, by omega⟩, (1 : Fin 3))
        simpa [hmid] using this⟩
    invFun := fun ⟨g, hg, hmid⟩ =>
      ⟨toWalk (Nat.succ_pos _) hg, toWalk_isWalkF (Nat.succ_pos _) hg, by
        have hdeg := siteDeg_toEdges (Nat.succ_pos _) (toWalk_isWalkF (Nat.succ_pos _) hg)
          (⟨n, by omega⟩, (1 : Fin 3))
        rw [toEdges_toWalk (Nat.succ_pos _) hg, hmid] at hdeg
        by_contra hnot
        simp [hnot] at hdeg⟩
    left_inv := fun ⟨w, hw, _⟩ => Subtype.ext (toWalk_toEdges (Nat.succ_pos _) hw)
    right_inv := fun ⟨g, hg, _⟩ => Subtype.ext (toEdges_toWalk (Nat.succ_pos _) hg) }

/-! Part 4: Step B — Prefix 5-State Transfer Matrix Equivalence -/

private abbrev PGNode (R : ℕ) := SiteF (R + 1) ⊕ Unit ⊕ Fin 3

private def topNode {R : ℕ} : PGNode R := Sum.inr (Sum.inl ())

private def botPort {R : ℕ} (c : Fin 3) : PGNode R := Sum.inr (Sum.inr c)

private def pgAdj {R : ℕ} (g : GridEdges (R + 1)) : PGNode R → PGNode R → Prop
  | Sum.inl u, Sum.inl v => hasEdge g u v = true
  | Sum.inr (Sum.inl ()), Sum.inl u => u = (⟨0, Nat.succ_pos R⟩, 0)
  | Sum.inl u, Sum.inr (Sum.inl ()) => u = (⟨0, Nat.succ_pos R⟩, 0)
  | Sum.inr (Sum.inr c), Sum.inl u =>
      u = (⟨R, Nat.lt_succ_self R⟩, c) ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ c = true
  | Sum.inl u, Sum.inr (Sum.inr c) =>
      u = (⟨R, Nat.lt_succ_self R⟩, c) ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ c = true
  | _, _ => False

private lemma pgAdj_symm {R : ℕ} (g : GridEdges (R + 1)) {x y : PGNode R}
    (h : pgAdj g x y) : pgAdj g y x := by
  rcases x with u | ⟨⟩ | c <;> rcases y with v | ⟨⟩ | d <;> simp only [pgAdj] at h ⊢
  · rw [hasEdge_symm]; exact h
  · exact h
  · exact h
  · exact h
  · exact h

private def pgReach {R : ℕ} (g : GridEdges (R + 1)) (x y : PGNode R) : Prop :=
  Relation.ReflTransGen (pgAdj g) x y

private lemma pgReach_symm {R : ℕ} {g : GridEdges (R + 1)} {x y : PGNode R}
    (h : pgReach g x y) : pgReach g y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih => exact Relation.ReflTransGen.head (pgAdj_symm g hab) ih

private lemma pgReach_inl_iff {R : ℕ} (g : GridEdges (R + 1)) (u v : SiteF (R + 1)) :
    pgReach g (Sum.inl u) (Sum.inl v) ↔
      Relation.ReflTransGen (fun a b => hasEdge g a b = true) u v := by
  constructor
  · intro h
    have hin : ∀ y : PGNode R, pgReach g (Sum.inl u) y →
        match y with
        | Sum.inl w => Relation.ReflTransGen (fun a b => hasEdge g a b = true) u w
        | Sum.inr (Sum.inl ()) =>
            Relation.ReflTransGen (fun a b => hasEdge g a b = true) u (⟨0, Nat.succ_pos R⟩, 0)
        | Sum.inr (Sum.inr c) =>
            Relation.ReflTransGen (fun a b => hasEdge g a b = true) u
              (⟨R, Nat.lt_succ_self R⟩, c) ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ c = true := by
      intro y hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b _ hab ih =>
        rcases a with x | ⟨⟩ | c <;> rcases b with z | ⟨⟩ | d <;> simp only [pgAdj] at hab
        · exact ih.tail hab
        · subst hab; exact ih
        · rw [hab.1] at ih; exact ⟨ih, hab.2⟩
        · subst hab; exact ih
        · rw [hab.1]; exact ih.1
    exact hin (Sum.inl v) h
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih => exact ih.tail hab

private def PrefCutOK (R : ℕ) (g : GridEdges (R + 1)) : Prop :=
  (∀ r : Fin (R + 1), ∀ c : Fin 3, siteDeg g r c = 0 ∨ siteDeg g r c = 2) ∧
  (∀ u : SiteF (R + 1), siteDeg g u.1 u.2 = 2 →
    pgReach g (Sum.inl u) topNode ∨
      ∃ c : Fin 3, g.ve ⟨R, Nat.lt_succ_self R⟩ c = true ∧ pgReach g (Sum.inl u) (botPort c))

private def StateConn (R : ℕ) (s : Fin 5) (g : GridEdges (R + 1)) : Prop :=
  match s with
  | 0 => pgReach g topNode (botPort 0)
  | 1 => pgReach g topNode (botPort 1)
  | 2 => pgReach g topNode (botPort 2)
  | 3 => pgReach g topNode (botPort 2) ∧ pgReach g (botPort 0) (botPort 1) ∧
          ¬ pgReach g topNode (botPort 0) ∧ ¬ pgReach g topNode (botPort 1)
  | 4 => pgReach g topNode (botPort 0) ∧ pgReach g (botPort 1) (botPort 2) ∧
          ¬ pgReach g topNode (botPort 1) ∧ ¬ pgReach g topNode (botPort 2)

private def IsValidPrefix (R : ℕ) (s : Fin 5) (g : GridEdges (R + 1)) : Prop :=
  g.ve ⟨R, Nat.lt_succ_self R⟩ = topCut s ∧ PrefCutOK R g ∧ StateConn R s g

private lemma fin5_cases : ∀ t : Fin 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
  decide

private lemma topCut2_eq : ∀ c : Fin 3, (c == 2) = topCut 2 c := by
  decide

private lemma goodEdges_iff_validPrefix2 (n : ℕ) (g : GridEdges (2 * n + 1)) :
    GoodEdges (2 * n + 1) (Nat.succ_pos _) g ↔ IsValidPrefix (2 * n) 2 g := by
  constructor
  · intro hg
    refine ⟨?_, ⟨hg.2.1, fun u hu => ?_⟩, ?_⟩
    · funext c
      have hidx : (⟨2 * n + 1 - 1, Nat.sub_lt (Nat.succ_pos _) Nat.one_pos⟩ :
          Fin (2 * n + 1)) = ⟨2 * n, Nat.lt_succ_self (2 * n)⟩ := Fin.ext (by dsimp)
      have h1 := hg.1 c
      rw [hidx] at h1
      rw [h1, topCut2_eq c]
    · left
      have hr := (pgReach_inl_iff g (topSite (Nat.succ_pos _)) u).mpr (hg.2.2 u hu)
      have htop : pgReach g topNode (Sum.inl (topSite (Nat.succ_pos _))) :=
        Relation.ReflTransGen.single (by simp [pgAdj, topSite, topNode])
      exact pgReach_symm (htop.trans hr)
    · have hbot_deg : siteDeg g ⟨2 * n, by omega⟩ 2 = 2 := by
        have hidx : (⟨2 * n + 1 - 1, Nat.sub_lt (Nat.succ_pos _) Nat.one_pos⟩ :
            Fin (2 * n + 1)) = ⟨2 * n, by omega⟩ := Fin.ext (by dsimp)
        have h2n : g.ve ⟨2 * n, by omega⟩ 2 = true := by
          rw [← hidx, hg.1 2]; rfl
        have h1 : 1 ≤ siteDeg g ⟨2 * n, by omega⟩ 2 := by
          unfold siteDeg
          simp [h2n]
          omega
        rcases hg.2.1 ⟨2 * n, by omega⟩ 2 with h0 | h2
        · omega
        · exact h2
      have hr := (pgReach_inl_iff g (topSite (Nat.succ_pos _)) (botSite (Nat.succ_pos _))).mpr
        (hg.2.2 (botSite (Nat.succ_pos _)) hbot_deg)
      have htop : pgReach g topNode (Sum.inl (topSite (Nat.succ_pos _))) :=
        Relation.ReflTransGen.single (by simp [pgAdj, topSite, topNode])
      have hbot : pgReach g (Sum.inl (botSite (Nat.succ_pos _))) (botPort 2) :=
        Relation.ReflTransGen.single ⟨rfl, by simpa using hg.1 2⟩
      exact (htop.trans hr).trans hbot
  · rintro ⟨hve, ⟨hdeg, hreach⟩, hconn⟩
    refine ⟨?_, hdeg, fun u hu => ?_⟩
    · intro c
      have hidx : (⟨2 * n + 1 - 1, Nat.sub_lt (Nat.succ_pos _) Nat.one_pos⟩ :
          Fin (2 * n + 1)) = ⟨2 * n, Nat.lt_succ_self (2 * n)⟩ := Fin.ext (by dsimp)
      rw [hidx, hve]
      exact (topCut2_eq c).symm
    · have htop_u : pgReach g (topNode) (Sum.inl u) := by
        rcases hreach u hu with hu1 | ⟨c, hvc, huc⟩
        · exact pgReach_symm hu1
        · have hc2 : c = 2 := by
            rw [hve] at hvc
            fin_cases c <;> simp [topCut] at hvc; rfl
          subst hc2
          exact hconn.trans (pgReach_symm huc)
      by_cases hu0 : u = topSite (Nat.succ_pos _)
      · subst hu0
        exact Relation.ReflTransGen.refl
      · rw [← pgReach_inl_iff]
        rcases Relation.ReflTransGen.cases_head htop_u with heq | ⟨y, hstep, htail⟩
        · simp [topNode] at heq
        · rcases y with y_site | ⟨⟩ | c
          · simp only [pgAdj, topNode] at hstep
            have : y_site = topSite (Nat.succ_pos _) := hstep
            rwa [← this]
          · simp [pgAdj, topNode] at hstep
          · simp [pgAdj, topNode] at hstep

private def cfgOfGrid0 (g : GridEdges 1) : RowCfg :=
  ⟨g.he 0 0, g.he 0 1, g.ve 0 0, g.ve 0 1, g.ve 0 2⟩

private def grid0OfCfg (cfg : RowCfg) : GridEdges 1 where
  he _ c := if c = 0 then cfg.h01 else cfg.h12
  ve _ c := botCut cfg c

private lemma grid0OfCfg_cfgOfGrid0 (g : GridEdges 1) : grid0OfCfg (cfgOfGrid0 g) = g := by
  refine GridEdges.ext' ?_ ?_
  · funext r c
    fin_cases r; fin_cases c <;> rfl
  · funext r c
    fin_cases r; fin_cases c <;> rfl

private lemma cfgOfGrid0_grid0OfCfg (cfg : RowCfg) : cfgOfGrid0 (grid0OfCfg cfg) = cfg := by
  cases cfg; rfl

private def embed0 : Fin 7 → PGNode 0
  | 0 => Sum.inl (0, 0)
  | 1 => Sum.inl (0, 1)
  | 2 => Sum.inl (0, 2)
  | 3 => topNode
  | 4 => botPort 0
  | 5 => botPort 1
  | 6 => botPort 2

private lemma symAdj0_iff (g : GridEdges 1) (u v : Fin 7) :
    symAdj 0 (cfgOfGrid0 g) u v = true ↔ pgAdj g (embed0 u) (embed0 v) := by
  fin_cases u <;> fin_cases v <;>
    simp [symAdj, pgAdj, embed0, topNode, botPort, hasEdge, cfgOfGrid0, Fin.ext_iff]

private lemma pgReach0_iff (g : GridEdges 1) (u v : Fin 7) :
    pgReach g (embed0 u) (embed0 v) ↔ symReach 0 (cfgOfGrid0 g) u v = true := by
  rw [symReach_iff_reflTransGen]
  constructor
  · intro h
    have hin : ∀ y : PGNode 0, pgReach g (embed0 u) y →
        ∃ w : Fin 7, y = embed0 w ∧
          Relation.ReflTransGen (fun a b => symAdj 0 (cfgOfGrid0 g) a b = true) u w := by
      intro y hy
      induction hy with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | @tail a b _ hab ih =>
        obtain ⟨w, rfl, hpath⟩ := ih
        have hbw : ∃ w' : Fin 7, b = embed0 w' := by
          rcases b with ⟨r, c⟩ | ⟨⟩ | c
          · fin_cases r; fin_cases c
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
          · fin_cases c
            · exact ⟨4, rfl⟩
            · exact ⟨5, rfl⟩
            · exact ⟨6, rfl⟩
        obtain ⟨w', rfl⟩ := hbw
        exact ⟨w', rfl, hpath.tail ((symAdj0_iff g w w').mpr hab)⟩
    obtain ⟨w, hw, hpath⟩ := hin (embed0 v) h
    have heq : v = w := by
      fin_cases v <;> fin_cases w <;> simp [embed0, topNode, botPort] at hw <;> rfl
    rwa [heq]
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih => exact ih.tail ((symAdj0_iff g a b).mp hab)

private lemma pref0_cutOK_iff (g : GridEdges 1) :
    PrefCutOK 0 g ↔ rowDegOk 0 (cfgOfGrid0 g) = true ∧ exitsOk 0 (cfgOfGrid0 g) = true := by
  have hdeg_eq : ∀ c : Fin 3, siteDeg g 0 c = colDeg 0 (cfgOfGrid0 g) c := by
    intro c
    fin_cases c <;> simp [siteDeg, colDeg, topCutG, topCut, botCut, cfgOfGrid0]
  constructor
  · intro ⟨hd, hr⟩
    have hrow : rowDegOk 0 (cfgOfGrid0 g) = true := by
      have h0 := hd 0 0; have h1 := hd 0 1; have h2 := hd 0 2
      rw [hdeg_eq 0] at h0; rw [hdeg_eq 1] at h1; rw [hdeg_eq 2] at h2
      unfold rowDegOk
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨h0, h1⟩, h2⟩
    have hex : exitsOk 0 (cfgOfGrid0 g) = true := by
      have hc : ∀ c : Fin 3, colDeg 0 (cfgOfGrid0 g) c = 2 →
          symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 3 = true ∨
          ((cfgOfGrid0 g).v0 = true ∧ symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 4 = true) ∨
          ((cfgOfGrid0 g).v1 = true ∧ symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 5 = true) ∨
          ((cfgOfGrid0 g).v2 = true ∧ symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 6 = true) := by
        intro c hcol
        rw [← hdeg_eq c] at hcol
        have hmem := hr (0, c) hcol
        have hcemb : (Sum.inl (0, c) : PGNode 0) = embed0 ⟨c.1, by omega⟩ := by
          fin_cases c <;> rfl
        rw [hcemb] at hmem
        rcases hmem with ht | ⟨k, hvk, hkb⟩
        · left
          exact (pgReach0_iff g ⟨c.1, by omega⟩ 3).mp ht
        · right
          fin_cases k
          · left; exact ⟨hvk, (pgReach0_iff g ⟨c.1, by omega⟩ 4).mp hkb⟩
          · right; left; exact ⟨hvk, (pgReach0_iff g ⟨c.1, by omega⟩ 5).mp hkb⟩
          · right; right; exact ⟨hvk, (pgReach0_iff g ⟨c.1, by omega⟩ 6).mp hkb⟩
      have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
      unfold exitsOk
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · by_cases h : colDeg 0 (cfgOfGrid0 g) 0 = 2
        · right
          rcases h0 h with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (Or.inl (Or.inl ha))
          · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
          · exact Or.inl (Or.inr ⟨ha, hb⟩)
          · exact Or.inr ⟨ha, hb⟩
        · left; exact h
      · by_cases h : colDeg 0 (cfgOfGrid0 g) 1 = 2
        · right
          rcases h1 h with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (Or.inl (Or.inl ha))
          · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
          · exact Or.inl (Or.inr ⟨ha, hb⟩)
          · exact Or.inr ⟨ha, hb⟩
        · left; exact h
      · by_cases h : colDeg 0 (cfgOfGrid0 g) 2 = 2
        · right
          rcases h2 h with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (Or.inl (Or.inl ha))
          · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
          · exact Or.inl (Or.inr ⟨ha, hb⟩)
          · exact Or.inr ⟨ha, hb⟩
        · left; exact h
    exact ⟨hrow, hex⟩
  · rintro ⟨hrow, hex⟩
    refine ⟨fun r c => ?_, fun ⟨r, c⟩ hc => ?_⟩
    · have hr0 : r = 0 := Fin.ext (Nat.lt_one_iff.mp r.2)
      subst hr0
      rw [hdeg_eq c]
      unfold rowDegOk at hrow
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrow
      fin_cases c
      · exact hrow.1.1
      · exact hrow.1.2
      · exact hrow.2
    · have hr0 : r = 0 := Fin.ext (Nat.lt_one_iff.mp r.2)
      subst hr0
      rw [hdeg_eq c] at hc
      unfold exitsOk at hex
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hex
      have hcemb : (Sum.inl (0, c) : PGNode 0) = embed0 ⟨c.1, by omega⟩ := by
        fin_cases c <;> rfl
      rw [hcemb]
      have hcase : symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 3 = true ∨
          ((cfgOfGrid0 g).v0 = true ∧ symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 4 = true) ∨
          ((cfgOfGrid0 g).v1 = true ∧ symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 5 = true) ∨
          ((cfgOfGrid0 g).v2 = true ∧ symReach 0 (cfgOfGrid0 g) ⟨c.1, by omega⟩ 6 = true) := by
        fin_cases c
        · rcases hex.1.1 with h | h
          · exact absurd hc h
          · rcases h with ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · left; exact h
            · right; left; exact ⟨h1, h2⟩
            · right; right; left; exact ⟨h1, h2⟩
            · right; right; right; exact ⟨h1, h2⟩
        · rcases hex.1.2 with h | h
          · exact absurd hc h
          · rcases h with ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · left; exact h
            · right; left; exact ⟨h1, h2⟩
            · right; right; left; exact ⟨h1, h2⟩
            · right; right; right; exact ⟨h1, h2⟩
        · rcases hex.2 with h | h
          · exact absurd hc h
          · rcases h with ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · left; exact h
            · right; left; exact ⟨h1, h2⟩
            · right; right; left; exact ⟨h1, h2⟩
            · right; right; right; exact ⟨h1, h2⟩
      rcases hcase with h | ⟨hv, h⟩ | ⟨hv, h⟩ | ⟨hv, h⟩
      · left; exact (pgReach0_iff g ⟨c.1, by omega⟩ 3).mpr h
      · right; exact ⟨0, hv, (pgReach0_iff g ⟨c.1, by omega⟩ 4).mpr h⟩
      · right; exact ⟨1, hv, (pgReach0_iff g ⟨c.1, by omega⟩ 5).mpr h⟩
      · right; exact ⟨2, hv, (pgReach0_iff g ⟨c.1, by omega⟩ 6).mpr h⟩

private lemma validPrefix0_iff (g : GridEdges 1) (t : Fin 5) :
    IsValidPrefix 0 t g ↔ outStateOpt 0 (cfgOfGrid0 g) = some t := by
  set cfg := cfgOfGrid0 g
  have hve : g.ve 0 = topCut t ↔ cfg.v0 = topCut t 0 ∧ cfg.v1 = topCut t 1 ∧ cfg.v2 = topCut t 2 := by
    constructor
    · intro h; refine ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
    · intro ⟨h0, h1, h2⟩
      dsimp [cfg, cfgOfGrid0] at h0 h1 h2
      funext c; fin_cases c <;> simp [h0, h1, h2]
  constructor
  · rintro ⟨hvet, hok, hconn⟩
    obtain ⟨hrow, hex⟩ := (pref0_cutOK_iff g).mp hok
    have hve' := hve.mp hvet
    have hrow' : rowDegOk 0 cfg = true := hrow
    have hex' : exitsOk 0 cfg = true := hex
    change outStateOpt 0 cfg = some t
    unfold outStateOpt
    simp only [hrow', hex', Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases fin5_cases t with rfl | rfl | rfl | rfl | rfl
    · simp only [topCut] at hve'
      have h34 : symReach 0 cfg 3 4 = true := (pgReach0_iff g 3 4).mp hconn
      simp [hve', h34]
    · simp only [topCut] at hve'
      have h35 : symReach 0 cfg 3 5 = true := (pgReach0_iff g 3 5).mp hconn
      simp [hve', h35]
    · simp only [topCut] at hve'
      have h36 : symReach 0 cfg 3 6 = true := (pgReach0_iff g 3 6).mp hconn
      simp [hve', h36]
    · simp only [topCut] at hve'
      have h36 : symReach 0 cfg 3 6 = true := (pgReach0_iff g 3 6).mp hconn.1
      have h45 : symReach 0 cfg 4 5 = true := (pgReach0_iff g 4 5).mp hconn.2.1
      simp [hve', h36, h45]
    · simp only [topCut] at hve'
      have h34 : symReach 0 cfg 3 4 = true := (pgReach0_iff g 3 4).mp hconn.1
      have h56 : symReach 0 cfg 5 6 = true := (pgReach0_iff g 5 6).mp hconn.2.1
      have hdisj := state4_disjoint 0 cfg hrow' h34 h56
      simp [hve', h34, h56, hdisj.2]
  · intro hout
    change outStateOpt 0 cfg = some t at hout
    have hboth : rowDegOk 0 cfg = true ∧ exitsOk 0 cfg = true := by
      cases hr : rowDegOk 0 cfg <;> cases hx : exitsOk 0 cfg <;> simp [outStateOpt, hr, hx] at hout
      exact ⟨rfl, rfl⟩
    have hok := (pref0_cutOK_iff g).mpr hboth
    unfold outStateOpt at hout
    simp only [hboth.1, hboth.2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hout
    cases hv0 : cfg.v0 <;> cases hv1 : cfg.v1 <;> cases hv2 : cfg.v2 <;>
      simp [hv0, hv1, hv2] at hout
    · rcases hout with ⟨h36, rfl⟩
      exact ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, (pgReach0_iff g 3 6).mpr h36⟩
    · rcases hout with ⟨h35, rfl⟩
      exact ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, (pgReach0_iff g 3 5).mpr h35⟩
    · rcases hout with ⟨h34, rfl⟩
      exact ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, (pgReach0_iff g 3 4).mpr h34⟩
    · split_ifs at hout with h36 h34
      · obtain rfl := Option.some.inj hout
        have hdisj := state3_disjoint 0 cfg hboth.1 h36.1 h36.2
        refine ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, ?_⟩
        refine ⟨(pgReach0_iff g 3 6).mpr h36.1, (pgReach0_iff g 4 5).mpr h36.2, ?_, ?_⟩
        · change ¬ pgReach g (embed0 3) (embed0 4)
          rw [pgReach0_iff]; simpa [cfg] using hdisj.1
        · change ¬ pgReach g (embed0 3) (embed0 5)
          rw [pgReach0_iff]; simpa [cfg] using hdisj.2
      · obtain rfl := Option.some.inj hout
        have hdisj := state4_disjoint 0 cfg hboth.1 h34.1 h34.2
        refine ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, ?_⟩
        refine ⟨(pgReach0_iff g 3 4).mpr h34.1, (pgReach0_iff g 5 6).mpr h34.2, ?_, ?_⟩
        · change ¬ pgReach g (embed0 3) (embed0 5)
          rw [pgReach0_iff]; simpa [cfg] using hdisj.1
        · change ¬ pgReach g (embed0 3) (embed0 6)
          rw [pgReach0_iff]; simpa [cfg] using hdisj.2

private def snoc {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg) : GridEdges (R + 2) where
  he i c := if h : i.1 < R + 1 then g.he ⟨i.1, h⟩ c else if c = 0 then cfg.h01 else cfg.h12
  ve i c := if h : i.1 < R + 1 then g.ve ⟨i.1, h⟩ c else botCut cfg c

private def restrict {R : ℕ} (g' : GridEdges (R + 2)) : GridEdges (R + 1) where
  he i c := g'.he i.castSucc c
  ve i c := g'.ve i.castSucc c

private def lastCfg {R : ℕ} (g' : GridEdges (R + 2)) : RowCfg :=
  ⟨g'.he ⟨R + 1, Nat.lt_succ_self _⟩ 0, g'.he ⟨R + 1, Nat.lt_succ_self _⟩ 1,
   g'.ve ⟨R + 1, Nat.lt_succ_self _⟩ 0, g'.ve ⟨R + 1, Nat.lt_succ_self _⟩ 1,
   g'.ve ⟨R + 1, Nat.lt_succ_self _⟩ 2⟩

private lemma restrict_snoc {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg) :
    restrict (snoc g cfg) = g := by
  refine GridEdges.ext' ?_ ?_ <;> funext i c <;>
    simp only [restrict, snoc, Fin.val_castSucc, i.2, ↓reduceDIte]

private lemma lastCfg_snoc {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg) :
    lastCfg (snoc g cfg) = cfg := by
  cases cfg
  simp [lastCfg, snoc, botCut]

private lemma snoc_restrict {R : ℕ} (g' : GridEdges (R + 2)) :
    snoc (restrict g') (lastCfg g') = g' := by
  refine GridEdges.ext' ?_ ?_ <;> funext i c
  · by_cases h : i.1 < R + 1
    · simp only [snoc, h, ↓reduceDIte, restrict]; rfl
    · have hi : i = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := i.2; dsimp; omega)
      subst hi
      fin_cases c <;> simp [snoc, lastCfg]
  · by_cases h : i.1 < R + 1
    · simp only [snoc, h, ↓reduceDIte, restrict]; rfl
    · have hi : i = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := i.2; dsimp; omega)
      subst hi
      fin_cases c <;> simp [snoc, lastCfg, botCut]

private lemma siteDeg_snoc_lt {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg)
    (i : Fin (R + 1)) (c : Fin 3) :
    siteDeg (snoc g cfg) i.castSucc c = siteDeg g i c := by
  unfold siteDeg topCutG
  have hi_lt : i.1 < R + 1 := i.2
  by_cases hi0 : i.1 = 0
  · have hi0' : i = ⟨0, Nat.succ_pos R⟩ := Fin.ext hi0
    subst hi0'
    fin_cases c <;> simp [snoc]
  · have hm : i.1 - 1 < R + 1 := by omega
    fin_cases c <;>
      simp only [Fin.val_castSucc, hi0, snoc, hm, hi_lt, ↓reduceDIte]

private lemma siteDeg_snoc_last {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg)
    {s : Fin 5} (hve : g.ve ⟨R, Nat.lt_succ_self R⟩ = topCut s) (c : Fin 3) :
    siteDeg (snoc g cfg) ⟨R + 1, Nat.lt_succ_self _⟩ c = colDeg s cfg c := by
  unfold siteDeg topCutG colDeg
  have hlt : R < R + 1 := Nat.lt_succ_self R
  have hbot : ∀ k : Fin 3, (snoc g cfg).ve ⟨R + 1, Nat.lt_succ_self _⟩ k = botCut cfg k := by
    intro k; simp [snoc]
  have htop : ∀ k : Fin 3, (snoc g cfg).ve ⟨R, Nat.lt_succ_of_lt hlt⟩ k = topCut s k := by
    intro k
    simp only [snoc, hlt, ↓reduceDIte]
    exact congrFun hve k
  have hhe : ∀ k : Fin 2, (snoc g cfg).he ⟨R + 1, Nat.lt_succ_self _⟩ k =
      if k = 0 then cfg.h01 else cfg.h12 := by
    intro k; simp [snoc]
  fin_cases c <;> simp [hbot, htop, hhe]

private lemma hasEdge_snoc_lt_lt {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg)
    (u v : SiteF (R + 1)) :
    hasEdge (snoc g cfg) (u.1.castSucc, u.2) (v.1.castSucc, v.2) = hasEdge g u v := by
  rcases u with ⟨r₁, c₁⟩
  rcases v with ⟨r₂, c₂⟩
  have hr1 : r₁.1 < R + 1 := r₁.2
  have hr2 : r₂.1 < R + 1 := r₂.2
  unfold hasEdge
  by_cases hr : r₁ = r₂
  · subst hr
    simp only [↓reduceIte, snoc, Fin.val_castSucc, hr1, ↓reduceDIte]
  · have hrc : r₁.castSucc ≠ r₂.castSucc := fun h =>
      hr (Fin.ext (by simpa [Fin.val_castSucc] using congrArg Fin.val h))
    simp only [hr, hrc, Fin.val_castSucc, ↓reduceIte]
    by_cases hc : c₁ = c₂
    · subst hc
      simp only [↓reduceIte]
      by_cases h1 : r₁.1 + 1 = r₂.1
      · simp only [h1, ↓reduceIte, snoc, Fin.val_castSucc, hr1, ↓reduceDIte]
      · by_cases h2 : r₂.1 + 1 = r₁.1
        · simp only [h1, h2, ↓reduceIte, snoc, Fin.val_castSucc, hr2, ↓reduceDIte]
        · simp [h1, h2]
    · simp [hc]

private lemma restrict_prefCutOK {R : ℕ} (g' : GridEdges (R + 2))
    (h : PrefCutOK (R + 1) g') : PrefCutOK R (restrict g') := by
  let g := restrict g'
  let cfg := lastCfg g'
  have hg' : g' = snoc g cfg := (snoc_restrict g').symm
  refine ⟨fun i c => ?_, fun u hu => ?_⟩
  · have hd := h.1 i.castSucc c
    rwa [hg', siteDeg_snoc_lt] at hd
  · have hu' : siteDeg g' u.1.castSucc u.2 = 2 := by
      rw [hg', siteDeg_snoc_lt]; exact hu
    rcases h.2 (u.1.castSucc, u.2) hu' with htop | ⟨c, hvc, hbot⟩
    · have hin : ∀ y : PGNode (R + 1), pgReach g' (Sum.inl (u.1.castSucc, u.2)) y →
          (∃ w : SiteF (R + 1), y = Sum.inl (w.1.castSucc, w.2) ∧
            pgReach g (Sum.inl u) (Sum.inl w)) ∨
          pgReach g (Sum.inl u) topNode ∨
          ∃ k : Fin 3, g.ve ⟨R, Nat.lt_succ_self R⟩ k = true ∧
            pgReach g (Sum.inl u) (botPort k) := by
        intro y hy
        induction hy with
        | refl => exact Or.inl ⟨u, rfl, Relation.ReflTransGen.refl⟩
        | @tail a b _ hab ih =>
          rcases ih with ⟨w, rfl, hreach⟩ | ht | hb
          · rcases b with ⟨r, c⟩ | ⟨⟩ | k
            · by_cases hr : r.1 < R + 1
              · have he : hasEdge g w (⟨r.1, hr⟩, c) = true := by
                  have := hab
                  simp only [pgAdj] at this
                  have hr_eq : ((⟨r.1, hr⟩ : Fin (R + 1)).castSucc, c) = (r, c) :=
                    Prod.ext (Fin.ext rfl) rfl
                  rw [← hr_eq, hg', hasEdge_snoc_lt_lt g cfg w (⟨r.1, hr⟩, c)] at this
                  exact this
                exact Or.inl ⟨(⟨r.1, hr⟩, c), rfl, hreach.tail he⟩
              · have hrEq : r = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := r.2; dsimp; omega)
                subst hrEq
                simp only [pgAdj] at hab
                have hadj : w.1.1 = R ∧ w.2 = c ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ c = true := by
                  unfold hasEdge at hab
                  have hne : w.1.castSucc ≠ ⟨R + 1, Nat.lt_succ_self _⟩ := fun h => by
                    have := congrArg Fin.val h
                    simp [Fin.val_castSucc] at this
                    have := w.1.2
                    omega
                  simp only [hne, Fin.val_castSucc, ↓reduceIte] at hab
                  have hc : w.2 = c := by by_contra hnc; simp [hnc] at hab
                  have h1 : w.1.1 = R := by
                    by_contra hn1
                    have hn2 : ¬ (R + 1 + 1 = w.1.1) := by have := w.1.2; omega
                    simp [hc, hn1, hn2] at hab
                  have hwR : w.1 = ⟨R, Nat.lt_succ_self R⟩ := Fin.ext h1
                  have hve : g.ve ⟨R, Nat.lt_succ_self R⟩ w.2 = true := by
                    have := hab
                    simp only [hc, h1, ↓reduceIte] at this
                    simpa [g, restrict, hwR, hc] using this
                  exact ⟨h1, hc, hc ▸ hve⟩
                exact Or.inr (Or.inr ⟨c, hadj.2.2, hreach.tail
                  ⟨Prod.ext (Fin.ext hadj.1) hadj.2.1, hadj.2.2⟩⟩)
            · simp only [pgAdj] at hab
              have hw0_1 : w.1 = ⟨0, Nat.succ_pos R⟩ :=
                Fin.ext (by simpa [Fin.val_castSucc] using congrArg (fun t => t.1.1) hab)
              have hw0_2 : w.2 = 0 := congrArg Prod.snd hab
              have hw0 : w = (⟨0, Nat.succ_pos R⟩, 0) := Prod.ext hw0_1 hw0_2
              exact Or.inr (Or.inl (hreach.tail (by simp [pgAdj, hw0]; rfl)))
            · simp only [pgAdj] at hab
              have := congrArg (fun t => t.1.1) hab.1
              simp at this
              have := w.1.2
              omega
          · exact Or.inr (Or.inl ht)
          · exact Or.inr (Or.inr hb)
      rcases hin topNode htop with ⟨w, hw, _⟩ | ht | hb
      · simp [topNode] at hw
      · left; exact ht
      · right; exact hb
    · have hin : ∀ y : PGNode (R + 1), pgReach g' (Sum.inl (u.1.castSucc, u.2)) y →
          (∃ w : SiteF (R + 1), y = Sum.inl (w.1.castSucc, w.2) ∧
            pgReach g (Sum.inl u) (Sum.inl w)) ∨
          pgReach g (Sum.inl u) topNode ∨
          ∃ k : Fin 3, g.ve ⟨R, Nat.lt_succ_self R⟩ k = true ∧
            pgReach g (Sum.inl u) (botPort k) := by
        intro y hy
        induction hy with
        | refl => exact Or.inl ⟨u, rfl, Relation.ReflTransGen.refl⟩
        | @tail a b _ hab ih =>
          rcases ih with ⟨w, rfl, hreach⟩ | ht | hb
          · rcases b with ⟨r, c'⟩ | ⟨⟩ | k
            · by_cases hr : r.1 < R + 1
              · have he : hasEdge g w (⟨r.1, hr⟩, c') = true := by
                  have := hab
                  simp only [pgAdj] at this
                  have hr_eq : ((⟨r.1, hr⟩ : Fin (R + 1)).castSucc, c') = (r, c') :=
                    Prod.ext (Fin.ext rfl) rfl
                  rw [← hr_eq, hg', hasEdge_snoc_lt_lt g cfg w (⟨r.1, hr⟩, c')] at this
                  exact this
                exact Or.inl ⟨(⟨r.1, hr⟩, c'), rfl, hreach.tail he⟩
              · have hrEq : r = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := r.2; dsimp; omega)
                subst hrEq
                simp only [pgAdj] at hab
                have hadj : w.1.1 = R ∧ w.2 = c' ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ c' = true := by
                  unfold hasEdge at hab
                  have hne : w.1.castSucc ≠ ⟨R + 1, Nat.lt_succ_self _⟩ := fun h => by
                    have := congrArg Fin.val h
                    simp [Fin.val_castSucc] at this
                    have := w.1.2
                    omega
                  simp only [hne, Fin.val_castSucc, ↓reduceIte] at hab
                  have hc : w.2 = c' := by by_contra hnc; simp [hnc] at hab
                  have h1 : w.1.1 = R := by
                    by_contra hn1
                    have hn2 : ¬ (R + 1 + 1 = w.1.1) := by have := w.1.2; omega
                    simp [hc, hn1, hn2] at hab
                  have hwR : w.1 = ⟨R, Nat.lt_succ_self R⟩ := Fin.ext h1
                  have hve : g.ve ⟨R, Nat.lt_succ_self R⟩ w.2 = true := by
                    have := hab
                    simp only [hc, h1, ↓reduceIte] at this
                    simpa [g, restrict, hwR, hc] using this
                  exact ⟨h1, hc, hc ▸ hve⟩
                exact Or.inr (Or.inr ⟨c', hadj.2.2, hreach.tail
                  ⟨Prod.ext (Fin.ext hadj.1) hadj.2.1, hadj.2.2⟩⟩)
            · simp only [pgAdj] at hab
              have hw0_1 : w.1 = ⟨0, Nat.succ_pos R⟩ :=
                Fin.ext (by simpa [Fin.val_castSucc] using congrArg (fun t => t.1.1) hab)
              have hw0_2 : w.2 = 0 := congrArg Prod.snd hab
              have hw0 : w = (⟨0, Nat.succ_pos R⟩, 0) := Prod.ext hw0_1 hw0_2
              exact Or.inr (Or.inl (hreach.tail (by simp [pgAdj, hw0]; rfl)))
            · simp only [pgAdj] at hab
              have := congrArg (fun t => t.1.1) hab.1
              simp at this
              have := w.1.2
              omega
          · exact Or.inr (Or.inl ht)
          · exact Or.inr (Or.inr hb)
      rcases hin (botPort c) hbot with ⟨w, hw, _⟩ | ht | hb
      · simp [botPort] at hw
      · left; exact ht
      · right; exact hb

private def liftNode {R : ℕ} : PGNode R → PGNode (R + 1)
  | Sum.inl (i, c) => Sum.inl (i.castSucc, c)
  | Sum.inr (Sum.inl ()) => topNode
  | Sum.inr (Sum.inr c) => Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, c)

private lemma pgAdj_lift {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg) {x y : PGNode R}
    (h : pgAdj g x y) : pgAdj (snoc g cfg) (liftNode x) (liftNode y) := by
  rcases x with ⟨r, c⟩ | ⟨⟩ | c <;> rcases y with ⟨r', c'⟩ | ⟨⟩ | c' <;>
    simp only [pgAdj] at h
  · exact (hasEdge_snoc_lt_lt g cfg (r, c) (r', c')).trans h
  · simp only [liftNode, pgAdj, topNode, Prod.ext_iff, Fin.ext_iff] at h ⊢
    exact h
  · simp only [liftNode, pgAdj]
    have hr : r = ⟨R, Nat.lt_succ_self R⟩ := congrArg Prod.fst h.1
    have hc : c = c' := congrArg Prod.snd h.1
    subst hr hc
    unfold hasEdge
    have hne : (⟨R, Nat.lt_succ_self R⟩ : Fin (R + 1)).castSucc ≠ ⟨R + 1, Nat.lt_succ_self _⟩ := by
      intro h'
      have := congrArg Fin.val h'
      simp at this
    simp only [hne, Fin.val_castSucc, ↓reduceIte, Nat.lt_succ_self, ↓reduceDIte, snoc]
    exact h.2
  · simp only [liftNode, pgAdj, topNode, Prod.ext_iff, Fin.ext_iff] at h ⊢
    exact h
  · simp only [liftNode, pgAdj]
    have hr : r' = ⟨R, Nat.lt_succ_self R⟩ := congrArg Prod.fst h.1
    have hc : c' = c := congrArg Prod.snd h.1
    subst hr hc
    unfold hasEdge
    have hne : (⟨R + 1, Nat.lt_succ_self _⟩ : Fin (R + 2)) ≠
        (⟨R, Nat.lt_succ_self R⟩ : Fin (R + 1)).castSucc := by
      intro h'
      have := congrArg Fin.val h'
      simp at this
    have hne1 : ¬ (R + 1 + 1 = R) := by omega
    simp only [hne, hne1, Fin.val_castSucc, ↓reduceIte, Nat.lt_succ_self, ↓reduceDIte, snoc]
    exact h.2

private lemma pgReach_lift {R : ℕ} (g : GridEdges (R + 1)) (cfg : RowCfg) {x y : PGNode R}
    (h : pgReach g x y) : pgReach (snoc g cfg) (liftNode x) (liftNode y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih => exact ih.tail (pgAdj_lift g cfg hab)

private def embed {R : ℕ} : Fin 7 → PGNode (R + 1)
  | 0 => Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, 0)
  | 1 => Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, 1)
  | 2 => Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, 2)
  | 3 => topNode
  | 4 => botPort 0
  | 5 => botPort 1
  | 6 => botPort 2

private lemma symReach_step' {s : Fin 5} {cfg : RowCfg} {u v w : Fin 7}
    (h1 : symReach s cfg u v = true) (h2 : symAdj s cfg v w = true) :
    symReach s cfg u w = true := by
  rw [symReach_iff_reflTransGen] at h1 ⊢
  exact h1.tail h2

private lemma symReach_trans {s : Fin 5} {cfg : RowCfg} {u v w : Fin 7}
    (h1 : symReach s cfg u v = true) (h2 : symReach s cfg v w = true) :
    symReach s cfg u w = true := by
  rw [symReach_iff_reflTransGen] at h1 h2 ⊢
  exact h1.trans h2

private lemma symReach_symm {s : Fin 5} {cfg : RowCfg} {u v : Fin 7}
    (h : symReach s cfg u v = true) : symReach s cfg v u = true := by
  rw [symReach_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih =>
    exact Relation.ReflTransGen.head (by rwa [symAdj_symm]) ih

private def portToFin : Unit ⊕ Fin 3 → Fin 7
  | Sum.inl () => 3
  | Sum.inr c => ⟨c.1, by omega⟩

private lemma stateConn_port_sym {R : ℕ} {s : Fin 5} {g : GridEdges (R + 1)}
    (hs : IsValidPrefix R s g) (cfg : RowCfg) {p q : Unit ⊕ Fin 3}
    (hp : p = Sum.inl () ∨ ∃ c : Fin 3, topCut s c = true ∧ p = Sum.inr c)
    (hq : q = Sum.inl () ∨ ∃ c : Fin 3, topCut s c = true ∧ q = Sum.inr c)
    (hpq : pgReach g (Sum.inr p) (Sum.inr q)) :
    symReach s cfg (portToFin p) (portToFin q) = true := by
  rcases hs with ⟨hve, _, hconn⟩
  have hdisj_self : ∀ c : Fin 3, topCut s c = true →
      symReach s cfg ⟨c.1, by omega⟩ ⟨c.1, by omega⟩ = true := fun c _ => symReach_refl s cfg _
  rcases hp with rfl | ⟨c, hpc, rfl⟩ <;> rcases hq with rfl | ⟨d, hqd, rfl⟩
  · exact symReach_refl s cfg 3
  · fin_cases s
    · fin_cases d <;> simp [topCut] at hqd
      exact (symReach_iff_reflTransGen 0 cfg 3 0).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases d <;> simp [topCut] at hqd
      exact (symReach_iff_reflTransGen 1 cfg 3 1).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases d <;> simp [topCut] at hqd
      exact (symReach_iff_reflTransGen 2 cfg 3 2).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases d
      · exact absurd hpq hconn.2.2.1
      · exact absurd hpq hconn.2.2.2
      · exact (symReach_iff_reflTransGen 3 cfg 3 2).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases d
      · exact (symReach_iff_reflTransGen 4 cfg 3 0).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
      · exact absurd hpq hconn.2.2.1
      · exact absurd hpq hconn.2.2.2
  · apply symReach_symm
    have hqp := pgReach_symm hpq
    fin_cases s
    · fin_cases c <;> simp [topCut] at hpc
      exact (symReach_iff_reflTransGen 0 cfg 3 0).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases c <;> simp [topCut] at hpc
      exact (symReach_iff_reflTransGen 1 cfg 3 1).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases c <;> simp [topCut] at hpc
      exact (symReach_iff_reflTransGen 2 cfg 3 2).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases c
      · exact absurd hqp hconn.2.2.1
      · exact absurd hqp hconn.2.2.2
      · exact (symReach_iff_reflTransGen 3 cfg 3 2).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
    · fin_cases c
      · exact (symReach_iff_reflTransGen 4 cfg 3 0).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
      · exact absurd hqp hconn.2.2.1
      · exact absurd hqp hconn.2.2.2
  · fin_cases s
    · fin_cases c <;> fin_cases d <;> simp [topCut] at hpc hqd
      exact symReach_refl 0 cfg 0
    · fin_cases c <;> fin_cases d <;> simp [topCut] at hpc hqd
      exact symReach_refl 1 cfg 1
    · fin_cases c <;> fin_cases d <;> simp [topCut] at hpc hqd
      exact symReach_refl 2 cfg 2
    · fin_cases c <;> fin_cases d
      · exact symReach_refl 3 cfg 0
      · exact (symReach_iff_reflTransGen 3 cfg 0 1).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
      · exact absurd (hconn.1.trans (pgReach_symm hpq)) hconn.2.2.1
      · exact (symReach_iff_reflTransGen 3 cfg 1 0).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
      · exact symReach_refl 3 cfg 1
      · exact absurd (hconn.1.trans (pgReach_symm hpq)) hconn.2.2.2
      · exact absurd (hconn.1.trans hpq) hconn.2.2.1
      · exact absurd (hconn.1.trans hpq) hconn.2.2.2
      · exact symReach_refl 3 cfg 2
    · fin_cases c <;> fin_cases d
      · exact symReach_refl 4 cfg 0
      · exact absurd (hconn.1.trans hpq) hconn.2.2.1
      · exact absurd (hconn.1.trans hpq) hconn.2.2.2
      · exact absurd (hconn.1.trans (pgReach_symm hpq)) hconn.2.2.1
      · exact symReach_refl 4 cfg 1
      · exact (symReach_iff_reflTransGen 4 cfg 1 2).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
      · exact absurd (hconn.1.trans (pgReach_symm hpq)) hconn.2.2.2
      · exact (symReach_iff_reflTransGen 4 cfg 2 1).mpr (Relation.ReflTransGen.single (by simp [symAdj]))
      · exact symReach_refl 4 cfg 2

private lemma gluing_pgReach_iff {R : ℕ} {s : Fin 5} {g : GridEdges (R + 1)}
    (hs : IsValidPrefix R s g) (cfg : RowCfg) (u v : Fin 7) :
    pgReach (snoc g cfg) (embed u) (embed v) ↔ symReach s cfg u v = true := by
  have hve := hs.1
  have hok := hs.2.1
  have hconn := hs.2.2
  constructor
  · intro hreach
    let g' := snoc g cfg
    have hin : ∀ y : PGNode (R + 1), pgReach g' (embed u) y →
        match y with
        | Sum.inl (r, c) =>
            if hr : r.1 < R + 1 then
              ∃ p : Unit ⊕ Fin 3,
                (p = Sum.inl () ∨ ∃ k : Fin 3, topCut s k = true ∧ p = Sum.inr k) ∧
                pgReach g (Sum.inl (⟨r.1, hr⟩, c)) (Sum.inr p) ∧
                symReach s cfg u (portToFin p) = true
            else symReach s cfg u ⟨c.1, by omega⟩ = true
        | Sum.inr (Sum.inl ()) => symReach s cfg u 3 = true
        | Sum.inr (Sum.inr k) => symReach s cfg u ⟨k.1 + 4, by omega⟩ = true := by
      intro y hy
      induction hy with
      | refl =>
        fin_cases u <;> simp [embed, topNode, botPort, symReach_refl]
      | @tail a b _ hab ih =>
        rcases a with ⟨ra, ca⟩ | ⟨⟩ | ka
        · by_cases hra : ra.1 < R + 1
          · simp only [hra, ↓reduceDIte] at ih
            obtain ⟨p, hp, hpa, hpu⟩ := ih
            rcases b with ⟨rb, cb⟩ | ⟨⟩ | kb
            · by_cases hrb : rb.1 < R + 1
              · simp only [hrb, ↓reduceDIte]
                have he : hasEdge g (⟨ra.1, hra⟩, ca) (⟨rb.1, hrb⟩, cb) = true := by
                  have := hab
                  simp only [pgAdj] at this
                  have ha_eq : ((⟨ra.1, hra⟩ : Fin (R + 1)).castSucc, ca) = (ra, ca) :=
                    Prod.ext (Fin.ext rfl) rfl
                  have hb_eq : ((⟨rb.1, hrb⟩ : Fin (R + 1)).castSucc, cb) = (rb, cb) :=
                    Prod.ext (Fin.ext rfl) rfl
                  rw [← ha_eq, ← hb_eq, hasEdge_snoc_lt_lt g cfg (⟨ra.1, hra⟩, ca) (⟨rb.1, hrb⟩, cb)] at this
                  exact this
                exact ⟨p, hp, (pgReach_symm (Relation.ReflTransGen.single (by simp [pgAdj, he]))).trans hpa, hpu⟩
              · have hrbEq : rb = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := rb.2; dsimp; omega)
                subst hrbEq
                simp only [hrb, ↓reduceDIte]
                simp only [pgAdj] at hab
                have hstep : ra.1 = R ∧ ca = cb ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ cb = true := by
                  unfold hasEdge at hab
                  have hne : ra ≠ ⟨R + 1, Nat.lt_succ_self _⟩ := fun h => by
                    have := congrArg Fin.val h; dsimp at this; omega
                  simp only [hne, ↓reduceIte] at hab
                  have hc : ca = cb := by by_contra hnc; simp [hnc] at hab
                  have h1 : ra.1 = R := by
                    by_contra hn1
                    have hn2 : ¬ (R + 1 + 1 = ra.1) := by omega
                    simp [hc, hn1, hn2] at hab
                  have haEq : ra = ⟨R, by omega⟩ := Fin.ext h1
                  have hve_eq : g.ve ⟨R, Nat.lt_succ_self R⟩ cb = true := by
                    have := hab
                    simp only [hc, h1, ↓reduceIte] at this
                    simpa [g', snoc, haEq, hc] using this
                  exact ⟨h1, hc, hve_eq⟩
                have htop_cb : topCut s cb = true := by rw [← hve]; exact hstep.2.2
                have hbot_a : pgReach g (Sum.inr (Sum.inr cb)) (Sum.inl (⟨ra.1, hra⟩, ca)) :=
                  Relation.ReflTransGen.single ⟨Prod.ext (Fin.ext hstep.1) hstep.2.1, hstep.2.2⟩
                have hpr := hbot_a.trans hpa
                have hps := stateConn_port_sym hs cfg
                  (Or.inr ⟨cb, htop_cb, rfl⟩) hp hpr
                exact symReach_trans hpu (symReach_symm hps)
            · simp only [pgAdj] at hab
              have htop_a : pgReach g (Sum.inr (Sum.inl ())) (Sum.inl (⟨ra.1, hra⟩, ca)) :=
                Relation.ReflTransGen.single (by
                  simp only [pgAdj, Prod.ext_iff, Fin.ext_iff] at hab ⊢
                  exact hab)
              have hpr := htop_a.trans hpa
              have hps := stateConn_port_sym hs cfg (Or.inl rfl) hp hpr
              exact symReach_trans hpu (symReach_symm hps)
            · simp only [pgAdj] at hab
              have := congrArg (fun t => t.1.1) hab.1
              dsimp at this
              omega
          · have hraEq : ra = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := ra.2; dsimp; omega)
            subst hraEq
            simp only [hra, ↓reduceDIte] at ih
            rcases b with ⟨rb, cb⟩ | ⟨⟩ | kb
            · by_cases hrb : rb.1 < R + 1
              · simp only [hrb, ↓reduceDIte]
                simp only [pgAdj] at hab
                have hstep : rb.1 = R ∧ cb = ca ∧ g.ve ⟨R, Nat.lt_succ_self R⟩ ca = true := by
                  unfold hasEdge at hab
                  have hne : (⟨R + 1, Nat.lt_succ_self _⟩ : Fin (R + 2)) ≠ rb := fun h => by
                    have := congrArg Fin.val h; dsimp at this; omega
                  simp only [hne, ↓reduceIte] at hab
                  have hc : cb = ca := by by_contra hnc; simp [Ne.symm hnc] at hab
                  have h2 : rb.1 = R := by
                    by_contra hn2
                    have hn1 : ¬ (R + 1 + 1 = rb.1) := by omega
                    simp [hc, hn1, hn2] at hab
                  have hbEq : rb = ⟨R, by omega⟩ := Fin.ext h2
                  have hve_eq : g.ve ⟨R, Nat.lt_succ_self R⟩ ca = true := by
                    have := hab
                    have hn3 : ¬ (R + 1 + 1 = R) := by omega
                    simp only [hc, h2, hn3, ↓reduceIte] at this
                    simpa [g', snoc, hbEq, hc] using this
                  exact ⟨h2, hc, hve_eq⟩
                have htop_ca : topCut s ca = true := by rw [← hve]; exact hstep.2.2
                have hreach_b : pgReach g (Sum.inl (⟨rb.1, hrb⟩, cb)) (Sum.inr (Sum.inr ca)) :=
                  Relation.ReflTransGen.single ⟨Prod.ext (Fin.ext hstep.1) hstep.2.1, hstep.2.2⟩
                exact ⟨Sum.inr ca, Or.inr ⟨ca, htop_ca, rfl⟩, hreach_b, ih⟩
              · have hrbEq : rb = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := rb.2; dsimp; omega)
                subst hrbEq
                simp only [hrb, ↓reduceDIte]
                simp only [pgAdj] at hab
                have hadj : symAdj s cfg ⟨ca.1, by omega⟩ ⟨cb.1, by omega⟩ = true := by
                  unfold hasEdge at hab
                  fin_cases ca <;> fin_cases cb <;> simp [g', snoc] at hab <;> simp [symAdj, hab]
                exact symReach_step' ih hadj
            · simp only [pgAdj] at hab
              have := congrArg (fun t => t.1.1) hab
              dsimp at this
              omega
            · simp only [pgAdj] at hab
              have hcb : ca = kb := congrArg Prod.snd hab.1
              have hvk : botCut cfg kb = true := by
                simpa [g', snoc] using hab.2
              subst hcb
              have hadj : symAdj s cfg ⟨ca.1, by omega⟩ ⟨ca.1 + 4, by omega⟩ = true := by
                fin_cases ca <;> simp [symAdj] <;> simpa [botCut] using hvk
              exact symReach_step' ih hadj
        · rcases b with ⟨rb, cb⟩ | ⟨⟩ | kb
          · simp only [pgAdj] at hab
            have hrb0 : rb.1 = 0 ∧ cb = 0 := ⟨congrArg (fun t => t.1.1) hab, congrArg Prod.snd hab⟩
            have hrb_lt : rb.1 < R + 1 := by omega
            simp only [hrb_lt, ↓reduceDIte]
            exact ⟨Sum.inl (), Or.inl rfl, Relation.ReflTransGen.single (by
              simp only [pgAdj, Prod.ext_iff]; exact ⟨Fin.ext hrb0.1, hrb0.2⟩), ih⟩
          · simp [pgAdj] at hab
          · simp [pgAdj] at hab
        · rcases b with ⟨rb, cb⟩ | ⟨⟩ | kb
          · simp only [pgAdj] at hab
            have hrb : rb = ⟨R + 1, Nat.lt_succ_self _⟩ := congrArg Prod.fst hab.1
            have hcb : cb = ka := congrArg Prod.snd hab.1
            have hvk : botCut cfg ka = true := by simpa [g', snoc] using hab.2
            subst hrb hcb
            have hnot : ¬ (R + 1 < R + 1) := lt_irrefl _
            simp only [hnot, ↓reduceDIte]
            have hadj : symAdj s cfg ⟨cb.1 + 4, by omega⟩ ⟨cb.1, by omega⟩ = true := by
              fin_cases cb <;> simp [symAdj] <;> simpa [botCut] using hvk
            exact symReach_step' ih hadj
          · simp [pgAdj] at hab
          · simp [pgAdj] at hab
    have := hin (embed v) hreach
    fin_cases v <;> simp [embed, topNode, botPort] at this ⊢ <;> exact this
  · intro hsym
    rw [symReach_iff_reflTransGen] at hsym
    induction hsym with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      refine ih.trans ?_
      have hlift_top : ∀ c : Fin 3,
          ((s = 0 ∧ c = 0) ∨ (s = 1 ∧ c = 1) ∨ (s = 2 ∧ c = 2) ∨
            (s = 3 ∧ c = 2) ∨ (s = 4 ∧ c = 0)) →
          pgReach (snoc g cfg) topNode (Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, c)) := by
        intro c hc
        have hbot : pgReach g topNode (botPort c) := by
          rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hconn
          · exact hconn
          · exact hconn
          · exact hconn.1
          · exact hconn.1
        exact pgReach_lift g cfg hbot
      have hlift_01 : s = 3 → pgReach (snoc g cfg) (embed 0) (embed 1) := fun hs3 => by
        subst hs3; exact pgReach_lift g cfg hconn.2.1
      have hlift_12 : s = 4 → pgReach (snoc g cfg) (embed 1) (embed 2) := fun hs4 => by
        subst hs4; exact pgReach_lift g cfg hconn.2.1
      have hadj : pgReach (snoc g cfg) (embed a) (embed b) := by
        rcases symAdj_spec s cfg a b hab with
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), (h01 | rfl)⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), (h12 | rfl)⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hs04⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hs23⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hv0⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hv1⟩ |
          ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hv2⟩
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, hasEdge, snoc, h01])
        · exact hlift_01 rfl
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, hasEdge, snoc, h01])
        · exact pgReach_symm (hlift_01 rfl)
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, hasEdge, snoc, h12])
        · exact hlift_12 rfl
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, hasEdge, snoc, h12])
        · exact pgReach_symm (hlift_12 rfl)
        · exact hlift_top 0 (by rcases hs04 with rfl | rfl <;> tauto)
        · exact pgReach_symm (hlift_top 0 (by rcases hs04 with rfl | rfl <;> tauto))
        · exact hlift_top 1 (by tauto)
        · exact pgReach_symm (hlift_top 1 (by tauto))
        · exact hlift_top 2 (by rcases hs23 with rfl | rfl <;> tauto)
        · exact pgReach_symm (hlift_top 2 (by rcases hs23 with rfl | rfl <;> tauto))
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, snoc, botCut, botPort, hv0])
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, snoc, botCut, botPort, hv0])
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, snoc, botCut, botPort, hv1])
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, snoc, botCut, botPort, hv1])
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, snoc, botCut, botPort, hv2])
        · exact Relation.ReflTransGen.single (by simp [embed, pgAdj, snoc, botCut, botPort, hv2])
      exact hadj

private lemma snoc_prefCutOK_iff {R : ℕ} {s : Fin 5} {g : GridEdges (R + 1)}
    (hs : IsValidPrefix R s g) (cfg : RowCfg) :
    PrefCutOK (R + 1) (snoc g cfg) ↔ rowDegOk s cfg = true ∧ exitsOk s cfg = true := by
  let g' := snoc g cfg
  have hve := hs.1
  have hok := hs.2.1
  have hdeg_last : ∀ c : Fin 3, siteDeg g' ⟨R + 1, Nat.lt_succ_self _⟩ c = colDeg s cfg c :=
    siteDeg_snoc_last g cfg hve
  constructor
  · intro ⟨hd, hr⟩
    have hrow : rowDegOk s cfg = true := by
      have h0 := hd ⟨R + 1, Nat.lt_succ_self _⟩ 0
      have h1 := hd ⟨R + 1, Nat.lt_succ_self _⟩ 1
      have h2 := hd ⟨R + 1, Nat.lt_succ_self _⟩ 2
      rw [hdeg_last 0] at h0; rw [hdeg_last 1] at h1; rw [hdeg_last 2] at h2
      unfold rowDegOk
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨h0, h1⟩, h2⟩
    have hex : exitsOk s cfg = true := by
      have hc : ∀ c : Fin 3, colDeg s cfg c = 2 →
          symReach s cfg ⟨c.1, by omega⟩ 3 = true ∨
          (cfg.v0 = true ∧ symReach s cfg ⟨c.1, by omega⟩ 4 = true) ∨
          (cfg.v1 = true ∧ symReach s cfg ⟨c.1, by omega⟩ 5 = true) ∨
          (cfg.v2 = true ∧ symReach s cfg ⟨c.1, by omega⟩ 6 = true) := by
        intro c hcol
        rw [← hdeg_last c] at hcol
        have hmem := hr (⟨R + 1, Nat.lt_succ_self _⟩, c) hcol
        have hcemb : (Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, c) : PGNode (R + 1)) =
            embed ⟨c.1, by omega⟩ := by
          fin_cases c <;> rfl
        rw [hcemb] at hmem
        rcases hmem with ht | ⟨k, hvk, hkb⟩
        · left; exact (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 3).mp ht
        · right
          have hkbot : botCut cfg k = true := by simpa [g', snoc] using hvk
          fin_cases k
          · left; exact ⟨hkbot, (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 4).mp hkb⟩
          · right; left; exact ⟨hkbot, (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 5).mp hkb⟩
          · right; right; exact ⟨hkbot, (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 6).mp hkb⟩
      have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
      unfold exitsOk
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · by_cases h : colDeg s cfg 0 = 2
        · right
          rcases h0 h with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (Or.inl (Or.inl ha))
          · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
          · exact Or.inl (Or.inr ⟨ha, hb⟩)
          · exact Or.inr ⟨ha, hb⟩
        · left; exact h
      · by_cases h : colDeg s cfg 1 = 2
        · right
          rcases h1 h with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (Or.inl (Or.inl ha))
          · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
          · exact Or.inl (Or.inr ⟨ha, hb⟩)
          · exact Or.inr ⟨ha, hb⟩
        · left; exact h
      · by_cases h : colDeg s cfg 2 = 2
        · right
          rcases h2 h with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (Or.inl (Or.inl ha))
          · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
          · exact Or.inl (Or.inr ⟨ha, hb⟩)
          · exact Or.inr ⟨ha, hb⟩
        · left; exact h
    exact ⟨hrow, hex⟩
  · rintro ⟨hrow, hex⟩
    have hex' : ∀ c : Fin 3, colDeg s cfg c = 2 →
        pgReach g' (embed ⟨c.1, by omega⟩) topNode ∨
        ∃ k : Fin 3, g'.ve ⟨R + 1, Nat.lt_succ_self _⟩ k = true ∧
          pgReach g' (embed ⟨c.1, by omega⟩) (botPort k) := by
      intro c hc
      unfold exitsOk at hex
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hex
      have hcase : symReach s cfg ⟨c.1, by omega⟩ 3 = true ∨
          (cfg.v0 = true ∧ symReach s cfg ⟨c.1, by omega⟩ 4 = true) ∨
          (cfg.v1 = true ∧ symReach s cfg ⟨c.1, by omega⟩ 5 = true) ∨
          (cfg.v2 = true ∧ symReach s cfg ⟨c.1, by omega⟩ 6 = true) := by
        fin_cases c
        · rcases hex.1.1 with h | h
          · exact absurd hc h
          · rcases h with ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · left; exact h
            · right; left; exact ⟨h1, h2⟩
            · right; right; left; exact ⟨h1, h2⟩
            · right; right; right; exact ⟨h1, h2⟩
        · rcases hex.1.2 with h | h
          · exact absurd hc h
          · rcases h with ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · left; exact h
            · right; left; exact ⟨h1, h2⟩
            · right; right; left; exact ⟨h1, h2⟩
            · right; right; right; exact ⟨h1, h2⟩
        · rcases hex.2 with h | h
          · exact absurd hc h
          · rcases h with ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · left; exact h
            · right; left; exact ⟨h1, h2⟩
            · right; right; left; exact ⟨h1, h2⟩
            · right; right; right; exact ⟨h1, h2⟩
      rcases hcase with h | ⟨hv, h⟩ | ⟨hv, h⟩ | ⟨hv, h⟩
      · left; exact (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 3).mpr h
      · right; exact ⟨0, by simp [g', snoc, botCut, hv],
          (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 4).mpr h⟩
      · right; exact ⟨1, by simp [g', snoc, botCut, hv],
          (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 5).mpr h⟩
      · right; exact ⟨2, by simp [g', snoc, botCut, hv],
          (gluing_pgReach_iff hs cfg ⟨c.1, by omega⟩ 6).mpr h⟩
    refine ⟨fun r c => ?_, fun ⟨r, c⟩ hc => ?_⟩
    · by_cases hr : r.1 < R + 1
      · have hr_eq : (⟨r.1, hr⟩ : Fin (R + 1)).castSucc = r := Fin.ext rfl
        rw [← hr_eq, siteDeg_snoc_lt]
        exact hok.1 ⟨r.1, hr⟩ c
      · have hrEq : r = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := r.2; dsimp; omega)
        rw [hrEq, hdeg_last c]
        unfold rowDegOk at hrow
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrow
        fin_cases c
        · exact hrow.1.1
        · exact hrow.1.2
        · exact hrow.2
    · by_cases hr : r.1 < R + 1
      · have hr_eq : ((⟨r.1, hr⟩ : Fin (R + 1)).castSucc, c) = (r, c) := Prod.ext (Fin.ext rfl) rfl
        rw [← hr_eq, siteDeg_snoc_lt] at hc
        rcases hok.2 (⟨r.1, hr⟩, c) hc with htop | ⟨k, hvk, hbot⟩
        · left
          exact pgReach_lift g cfg htop
        · have htc : topCut s k = true := by rw [← hve]; exact hvk
          have hcol_pos : 1 ≤ colDeg s cfg k := by
            unfold colDeg; rw [htc]; simp; omega
          have hcol2 : colDeg s cfg k = 2 := by
            unfold rowDegOk at hrow
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrow
            rcases fin3_cases k with rfl | rfl | rfl
            · rcases hrow.1.1 with h | h <;> omega
            · rcases hrow.1.2 with h | h <;> omega
            · rcases hrow.2 with h | h <;> omega
          have hl := pgReach_lift g cfg hbot
          have hkemb : liftNode (botPort k : PGNode R) = embed ⟨k.1, by omega⟩ := by
            fin_cases k <;> rfl
          rw [hkemb] at hl
          rcases hex' k hcol2 with ht | ⟨m, hvm, hbm⟩
          · left; exact hl.trans ht
          · right; exact ⟨m, hvm, hl.trans hbm⟩
      · have hrEq : r = ⟨R + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := r.2; dsimp; omega)
        subst hrEq
        rw [hdeg_last c] at hc
        have hcemb : (Sum.inl (⟨R + 1, Nat.lt_succ_self _⟩, c) : PGNode (R + 1)) =
            embed ⟨c.1, by omega⟩ := by
          fin_cases c <;> rfl
        rw [hcemb]
        exact hex' c hc

private lemma snoc_validPrefix_iff {R : ℕ} {s : Fin 5} {g : GridEdges (R + 1)}
    (hs : IsValidPrefix R s g) (cfg : RowCfg) (t : Fin 5) :
    IsValidPrefix (R + 1) t (snoc g cfg) ↔ outStateOpt s cfg = some t := by
  let g' := snoc g cfg
  have hve : g'.ve ⟨R + 1, Nat.lt_succ_self _⟩ = topCut t ↔
      cfg.v0 = topCut t 0 ∧ cfg.v1 = topCut t 1 ∧ cfg.v2 = topCut t 2 := by
    constructor
    · intro h
      refine ⟨by simpa [g', snoc, botCut] using congrFun h 0,
        by simpa [g', snoc, botCut] using congrFun h 1,
        by simpa [g', snoc, botCut] using congrFun h 2⟩
    · intro ⟨h0, h1, h2⟩
      funext c
      fin_cases c <;> simp [g', snoc, botCut, h0, h1, h2]
  constructor
  · rintro ⟨hvet, hok, hconn⟩
    obtain ⟨hrow, hex⟩ := (snoc_prefCutOK_iff hs cfg).mp hok
    have hve' := hve.mp hvet
    unfold outStateOpt
    simp only [hrow, hex, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases fin5_cases t with rfl | rfl | rfl | rfl | rfl
    · simp only [topCut] at hve'
      have h34 := (gluing_pgReach_iff hs cfg 3 4).mp hconn
      simp [hve', h34]
    · simp only [topCut] at hve'
      have h35 := (gluing_pgReach_iff hs cfg 3 5).mp hconn
      simp [hve', h35]
    · simp only [topCut] at hve'
      have h36 := (gluing_pgReach_iff hs cfg 3 6).mp hconn
      simp [hve', h36]
    · simp only [topCut] at hve'
      have h36 := (gluing_pgReach_iff hs cfg 3 6).mp hconn.1
      have h45 := (gluing_pgReach_iff hs cfg 4 5).mp hconn.2.1
      simp [hve', h36, h45]
    · simp only [topCut] at hve'
      have h34 := (gluing_pgReach_iff hs cfg 3 4).mp hconn.1
      have h56 := (gluing_pgReach_iff hs cfg 5 6).mp hconn.2.1
      have hdisj := state4_disjoint s cfg hrow h34 h56
      simp [hve', h34, h56, hdisj.2]
  · intro hout
    have hboth : rowDegOk s cfg = true ∧ exitsOk s cfg = true := by
      cases hr : rowDegOk s cfg <;> cases hx : exitsOk s cfg <;> simp [outStateOpt, hr, hx] at hout
      exact ⟨rfl, rfl⟩
    have hok := (snoc_prefCutOK_iff hs cfg).mpr hboth
    unfold outStateOpt at hout
    simp only [hboth.1, hboth.2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hout
    cases hv0 : cfg.v0 <;> cases hv1 : cfg.v1 <;> cases hv2 : cfg.v2 <;>
      simp [hv0, hv1, hv2] at hout
    · rcases hout with ⟨h36, rfl⟩
      exact ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, (gluing_pgReach_iff hs cfg 3 6).mpr h36⟩
    · rcases hout with ⟨h35, rfl⟩
      exact ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, (gluing_pgReach_iff hs cfg 3 5).mpr h35⟩
    · rcases hout with ⟨h34, rfl⟩
      exact ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, (gluing_pgReach_iff hs cfg 3 4).mpr h34⟩
    · split_ifs at hout with h36 h34
      · obtain rfl := Option.some.inj hout
        have hdisj := state3_disjoint s cfg hboth.1 h36.1 h36.2
        refine ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, ?_⟩
        refine ⟨(gluing_pgReach_iff hs cfg 3 6).mpr h36.1,
          (gluing_pgReach_iff hs cfg 4 5).mpr h36.2, ?_, ?_⟩
        · change ¬ pgReach (snoc g cfg) (embed 3) (embed 4)
          rw [gluing_pgReach_iff hs cfg]; simp [hdisj.1]
        · change ¬ pgReach (snoc g cfg) (embed 3) (embed 5)
          rw [gluing_pgReach_iff hs cfg]; simp [hdisj.2]
      · obtain rfl := Option.some.inj hout
        have hdisj := state4_disjoint s cfg hboth.1 h34.1 h34.2
        refine ⟨hve.mpr ⟨hv0, hv1, hv2⟩, hok, ?_⟩
        refine ⟨(gluing_pgReach_iff hs cfg 3 4).mpr h34.1,
          (gluing_pgReach_iff hs cfg 5 6).mpr h34.2, ?_, ?_⟩
        · change ¬ pgReach (snoc g cfg) (embed 3) (embed 5)
          rw [gluing_pgReach_iff hs cfg]; simp [hdisj.1]
        · change ¬ pgReach (snoc g cfg) (embed 3) (embed 6)
          rw [gluing_pgReach_iff hs cfg]; simp [hdisj.2]

private lemma exists_unique_state_of_prefCutOK :
    ∀ (R : ℕ) (g : GridEdges (R + 1)), PrefCutOK R g → ∃! s : Fin 5, IsValidPrefix R s g
  | 0, g, hok => by
    obtain ⟨hrow, hex⟩ := (pref0_cutOK_iff g).mp hok
    have hsome := check_always_five 0 (cfgOfGrid0 g) hrow hex
    cases hout : outStateOpt 0 (cfgOfGrid0 g) with
    | none => simp [hout] at hsome
    | some t =>
      refine ⟨t, (validPrefix0_iff g t).mpr hout, fun t' ht' => ?_⟩
      have hout' := (validPrefix0_iff g t').mp ht'
      rw [hout] at hout'
      exact (Option.some.inj hout').symm
  | R + 1, g', hok => by
    have hok_r := restrict_prefCutOK g' hok
    obtain ⟨s, hs, huniq⟩ := exists_unique_state_of_prefCutOK R (restrict g') hok_r
    have hg' : g' = snoc (restrict g') (lastCfg g') := (snoc_restrict g').symm
    have hok' : PrefCutOK (R + 1) (snoc (restrict g') (lastCfg g')) := by rwa [← hg']
    obtain ⟨hrow, hex⟩ := (snoc_prefCutOK_iff hs (lastCfg g')).mp hok'
    have hsome := check_always_five s (lastCfg g') hrow hex
    cases hout : outStateOpt s (lastCfg g') with
    | none => simp [hout] at hsome
    | some t =>
      refine ⟨t, ?_, fun t' ht' => ?_⟩
      · rw [hg']
        exact (snoc_validPrefix_iff hs (lastCfg g') t).mpr hout
      · rw [hg'] at ht'
        have hout' := (snoc_validPrefix_iff hs (lastCfg g') t').mp ht'
        rw [hout] at hout'
        exact (Option.some.inj hout').symm

private noncomputable def VPref (R n : ℕ) (s : Fin 5) : Finset (GridEdges (R + 1)) :=
  letI := Classical.decPred (fun g : GridEdges (R + 1) =>
    IsValidPrefix R s g ∧ ∀ hn : n ≤ R, siteDeg g ⟨n, Nat.lt_succ_of_le hn⟩ 1 = 2)
  Finset.univ.filter (fun g =>
    IsValidPrefix R s g ∧ ∀ hn : n ≤ R, siteDeg g ⟨n, Nat.lt_succ_of_le hn⟩ 1 = 2)

private lemma mem_VPref {R n : ℕ} {s : Fin 5} {g : GridEdges (R + 1)} :
    g ∈ VPref R n s ↔
      IsValidPrefix R s g ∧ ∀ hn : n ≤ R, siteDeg g ⟨n, Nat.lt_succ_of_le hn⟩ 1 = 2 := by
  unfold VPref
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma VPref_card_lt (R n : ℕ) (hRn : R < n) (s : Fin 5) :
    ((VPref R n s).card : ℤ) = (T ^ (R + 1)) 0 s := by
  induction R generalizing s with
  | zero =>
    have hbij :
        (VPref 0 n s).card =
          ((Finset.univ : Finset RowCfg).filter (fun cfg => outStateOpt 0 cfg = some s)).card := by
      refine Finset.card_bij (fun g _ => cfgOfGrid0 g) ?_ ?_ ?_
      · intro g hg
        rw [mem_VPref] at hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (validPrefix0_iff g s).mp hg.1
      · intro g₁ _ g₂ _ heq
        have := congrArg grid0OfCfg heq
        rwa [grid0OfCfg_cfgOfGrid0, grid0OfCfg_cfgOfGrid0] at this
      · intro cfg hcfg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcfg
        refine ⟨grid0OfCfg cfg, mem_VPref.mpr ⟨(validPrefix0_iff _ s).mpr ?_, fun hn => by omega⟩,
          cfgOfGrid0_grid0OfCfg cfg⟩
        simpa [cfgOfGrid0_grid0OfCfg] using hcfg
    rw [hbij, card_step_T 0 s, pow_one]
  | succ R ih =>
    have ih' := ih (by omega)
    let P := (Finset.univ : Finset (Fin 5)).sigma
      (fun u => VPref R n u ×ˢ (Finset.univ : Finset RowCfg).filter
        (fun cfg => outStateOpt u cfg = some s))
    have hbij : (VPref (R + 1) n s).card = P.card := by
      refine Finset.card_bij (fun g' hg' =>
        let hok := (mem_VPref.mp hg').1.2.1
        ⟨Classical.choose (exists_unique_state_of_prefCutOK R (restrict g') (restrict_prefCutOK g' hok)),
          (restrict g', lastCfg g')⟩) ?_ ?_ ?_
      · intro g' hg'
        rw [mem_VPref] at hg'
        have hok_r := restrict_prefCutOK g' hg'.1.2.1
        let u := Classical.choose (exists_unique_state_of_prefCutOK R (restrict g') hok_r)
        have hu : IsValidPrefix R u (restrict g') :=
          (Classical.choose_spec (exists_unique_state_of_prefCutOK R (restrict g') hok_r)).1
        have hg_eq : g' = snoc (restrict g') (lastCfg g') := (snoc_restrict g').symm
        have hout : outStateOpt u (lastCfg g') = some s := by
          rw [← snoc_validPrefix_iff hu (lastCfg g') s, ← hg_eq]
          exact hg'.1
        have hmem_r : restrict g' ∈ VPref R n u :=
          mem_VPref.mpr ⟨hu, fun hn => by omega⟩
        simp only [P, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
          true_and]
        exact ⟨hmem_r, hout⟩
      · intro g₁ hg₁ g₂ hg₂ heq
        have h1 : restrict g₁ = restrict g₂ := congrArg (fun x => x.2.1) heq
        have h2 : lastCfg g₁ = lastCfg g₂ := congrArg (fun x => x.2.2) heq
        rw [← snoc_restrict g₁, ← snoc_restrict g₂, h1, h2]
      · intro ⟨u, ⟨g, cfg⟩⟩ hx
        simp only [P, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
          true_and] at hx
        rcases hx with ⟨hg, hcfg⟩
        rw [mem_VPref] at hg
        have hvalid : IsValidPrefix (R + 1) s (snoc g cfg) :=
          (snoc_validPrefix_iff hg.1 cfg s).mpr hcfg
        have hmem : snoc g cfg ∈ VPref (R + 1) n s :=
          mem_VPref.mpr ⟨hvalid, fun hn => by omega⟩
        have hok_r := restrict_prefCutOK (snoc g cfg) hvalid.2.1
        let u' := Classical.choose (exists_unique_state_of_prefCutOK R (restrict (snoc g cfg)) hok_r)
        have hu' : IsValidPrefix R u' (restrict (snoc g cfg)) :=
          (Classical.choose_spec (exists_unique_state_of_prefCutOK R (restrict (snoc g cfg)) hok_r)).1
        have huniq := (exists_unique_state_of_prefCutOK R g hg.1.2.1).unique
          (by rwa [restrict_snoc] at hu') hg.1
        refine ⟨snoc g cfg, hmem, ?_⟩
        exact Sigma.ext huniq (heq_of_eq (by dsimp; rw [restrict_snoc, lastCfg_snoc]))
    have hP_card : (P.card : ℤ) =
        ∑ u : Fin 5, ((VPref R n u).card : ℤ) * T u s := by
      simp only [P, Finset.card_sigma, Finset.card_product, Nat.cast_sum, Nat.cast_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [card_step_T u s]
    rw [hbij, hP_card]
    simp_rw [ih']
    rw [pow_succ T (R + 1), Matrix.mul_apply]

private lemma VPref_card_ge (R n : ℕ) (hnR : n ≤ R) (s : Fin 5) :
    ((VPref R n s).card : ℤ) = (T ^ n * M_mid * T ^ (R - n)) 0 s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnR
  induction d generalizing s with
  | zero =>
    have h0 : n + 0 - n = 0 := by omega
    rw [h0, pow_zero, Matrix.mul_one]
    change ((VPref n n s).card : ℤ) = (T ^ n * M_mid) 0 s
    cases n with
    | zero =>
      have hbij :
          (VPref 0 0 s).card =
            ((Finset.univ : Finset RowCfg).filter
              (fun cfg => outStateOpt 0 cfg = some s ∧ colDeg 0 cfg 1 = 2)).card := by
        refine Finset.card_bij (fun g _ => cfgOfGrid0 g) ?_ ?_ ?_
        · intro g hg
          rw [mem_VPref] at hg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨(validPrefix0_iff g s).mp hg.1, ?_⟩
          have hd := hg.2 le_rfl
          simpa [siteDeg, colDeg, topCutG, topCut, botCut, cfgOfGrid0] using hd
        · intro g₁ _ g₂ _ heq
          have := congrArg grid0OfCfg heq
          rwa [grid0OfCfg_cfgOfGrid0, grid0OfCfg_cfgOfGrid0] at this
        · intro cfg hcfg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcfg
          refine ⟨grid0OfCfg cfg, mem_VPref.mpr ⟨(validPrefix0_iff _ s).mpr ?_, fun _ => ?_⟩,
            cfgOfGrid0_grid0OfCfg cfg⟩
          · simpa [cfgOfGrid0_grid0OfCfg] using hcfg.1
          · simpa [siteDeg, colDeg, topCutG, topCut, botCut, grid0OfCfg] using hcfg.2
      rw [hbij, card_step_M_mid 0 s, pow_zero, Matrix.one_mul]
    | succ m =>
      let P := (Finset.univ : Finset (Fin 5)).sigma
        (fun u => VPref m (m + 1) u ×ˢ (Finset.univ : Finset RowCfg).filter
          (fun cfg => outStateOpt u cfg = some s ∧ colDeg u cfg 1 = 2))
      have hbij : (VPref (m + 1) (m + 1) s).card = P.card := by
        refine Finset.card_bij (fun g' hg' =>
          let hok := (mem_VPref.mp hg').1.2.1
          ⟨Classical.choose (exists_unique_state_of_prefCutOK m (restrict g') (restrict_prefCutOK g' hok)),
            (restrict g', lastCfg g')⟩) ?_ ?_ ?_
        · intro g' hg'
          rw [mem_VPref] at hg'
          have hok_r := restrict_prefCutOK g' hg'.1.2.1
          let u := Classical.choose (exists_unique_state_of_prefCutOK m (restrict g') hok_r)
          have hu : IsValidPrefix m u (restrict g') :=
            (Classical.choose_spec (exists_unique_state_of_prefCutOK m (restrict g') hok_r)).1
          have hg_eq : g' = snoc (restrict g') (lastCfg g') := (snoc_restrict g').symm
          have hout : outStateOpt u (lastCfg g') = some s := by
            rw [← snoc_validPrefix_iff hu (lastCfg g') s, ← hg_eq]
            exact hg'.1
          have hdeg1 : colDeg u (lastCfg g') 1 = 2 := by
            have := hg'.2 le_rfl
            rw [hg_eq, siteDeg_snoc_last (restrict g') (lastCfg g') hu.1 1] at this
            exact this
          have hmem_r : restrict g' ∈ VPref m (m + 1) u :=
            mem_VPref.mpr ⟨hu, fun hn => by omega⟩
          simp only [P, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
            true_and]
          exact ⟨hmem_r, hout, hdeg1⟩
        · intro g₁ hg₁ g₂ hg₂ heq
          have h1 : restrict g₁ = restrict g₂ := congrArg (fun x => x.2.1) heq
          have h2 : lastCfg g₁ = lastCfg g₂ := congrArg (fun x => x.2.2) heq
          rw [← snoc_restrict g₁, ← snoc_restrict g₂, h1, h2]
        · intro ⟨u, ⟨g, cfg⟩⟩ hx
          simp only [P, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
            true_and] at hx
          rcases hx with ⟨hg, hcfg, hdeg1⟩
          rw [mem_VPref] at hg
          have hvalid : IsValidPrefix (m + 1) s (snoc g cfg) :=
            (snoc_validPrefix_iff hg.1 cfg s).mpr hcfg
          have hmem : snoc g cfg ∈ VPref (m + 1) (m + 1) s :=
            mem_VPref.mpr ⟨hvalid, fun _ => by
              rw [siteDeg_snoc_last g cfg hg.1.1 1]; exact hdeg1⟩
          have hok_r := restrict_prefCutOK (snoc g cfg) hvalid.2.1
          let u' := Classical.choose
            (exists_unique_state_of_prefCutOK m (restrict (snoc g cfg)) hok_r)
          have hu' : IsValidPrefix m u' (restrict (snoc g cfg)) :=
            (Classical.choose_spec
              (exists_unique_state_of_prefCutOK m (restrict (snoc g cfg)) hok_r)).1
          have huniq := (exists_unique_state_of_prefCutOK m g hg.1.2.1).unique
            (by rwa [restrict_snoc] at hu') hg.1
          refine ⟨snoc g cfg, hmem, ?_⟩
          exact Sigma.ext huniq (heq_of_eq (by dsimp; rw [restrict_snoc, lastCfg_snoc]))
      have hP_card : (P.card : ℤ) =
          ∑ u : Fin 5, ((VPref m (m + 1) u).card : ℤ) * M_mid u s := by
        simp only [P, Finset.card_sigma, Finset.card_product, Nat.cast_sum, Nat.cast_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [card_step_M_mid u s]
      rw [hbij, hP_card]
      simp_rw [VPref_card_lt m (m + 1) (Nat.lt_succ_self m)]
      rw [Matrix.mul_apply]
  | succ d ih =>
    let R := n + d
    have ih' : ∀ u : Fin 5, ((VPref R n u).card : ℤ) = (T ^ n * M_mid * T ^ (R - n)) 0 u :=
      fun u => ih u (by omega)
    let P := (Finset.univ : Finset (Fin 5)).sigma
      (fun u => VPref R n u ×ˢ (Finset.univ : Finset RowCfg).filter
        (fun cfg => outStateOpt u cfg = some s))
    have hbij : (VPref (R + 1) n s).card = P.card := by
      refine Finset.card_bij (fun g' hg' =>
        let hok := (mem_VPref.mp hg').1.2.1
        ⟨Classical.choose (exists_unique_state_of_prefCutOK R (restrict g') (restrict_prefCutOK g' hok)),
          (restrict g', lastCfg g')⟩) ?_ ?_ ?_
      · intro g' hg'
        rw [mem_VPref] at hg'
        have hok_r := restrict_prefCutOK g' hg'.1.2.1
        let u := Classical.choose (exists_unique_state_of_prefCutOK R (restrict g') hok_r)
        have hu : IsValidPrefix R u (restrict g') :=
          (Classical.choose_spec (exists_unique_state_of_prefCutOK R (restrict g') hok_r)).1
        have hg_eq : g' = snoc (restrict g') (lastCfg g') := (snoc_restrict g').symm
        have hout : outStateOpt u (lastCfg g') = some s := by
          rw [← snoc_validPrefix_iff hu (lastCfg g') s, ← hg_eq]
          exact hg'.1
        have hmem_r : restrict g' ∈ VPref R n u := mem_VPref.mpr ⟨hu, fun hn => by
          have hdeg : siteDeg (snoc (restrict g') (lastCfg g'))
              (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (R + 1)).castSucc 1 = 2 := by
            simpa [← hg_eq] using hg'.2 (by omega)
          rwa [siteDeg_snoc_lt] at hdeg⟩
        simp only [P, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
          true_and]
        exact ⟨hmem_r, hout⟩
      · intro g₁ hg₁ g₂ hg₂ heq
        have h1 : restrict g₁ = restrict g₂ := congrArg (fun x => x.2.1) heq
        have h2 : lastCfg g₁ = lastCfg g₂ := congrArg (fun x => x.2.2) heq
        rw [← snoc_restrict g₁, ← snoc_restrict g₂, h1, h2]
      · intro ⟨u, ⟨g, cfg⟩⟩ hx
        simp only [P, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, Finset.mem_filter,
          true_and] at hx
        rcases hx with ⟨hg, hcfg⟩
        rw [mem_VPref] at hg
        have hvalid : IsValidPrefix (R + 1) s (snoc g cfg) :=
          (snoc_validPrefix_iff hg.1 cfg s).mpr hcfg
        have hmem : snoc g cfg ∈ VPref (R + 1) n s := mem_VPref.mpr ⟨hvalid, fun hn => by
          have h1 : siteDeg g ⟨n, Nat.lt_succ_of_le (by omega)⟩ 1 = 2 := hg.2 (by omega)
          have h2 : siteDeg (snoc g cfg)
              (⟨n, Nat.lt_succ_of_le (by omega)⟩ : Fin (R + 1)).castSucc 1 = 2 := by
            rw [siteDeg_snoc_lt]; exact h1
          exact h2⟩
        have hok_r := restrict_prefCutOK (snoc g cfg) hvalid.2.1
        let u' := Classical.choose
          (exists_unique_state_of_prefCutOK R (restrict (snoc g cfg)) hok_r)
        have hu' : IsValidPrefix R u' (restrict (snoc g cfg)) :=
          (Classical.choose_spec
            (exists_unique_state_of_prefCutOK R (restrict (snoc g cfg)) hok_r)).1
        have huniq := (exists_unique_state_of_prefCutOK R g hg.1.2.1).unique
          (by rwa [restrict_snoc] at hu') hg.1
        refine ⟨snoc g cfg, hmem, ?_⟩
        exact Sigma.ext huniq (heq_of_eq (by dsimp; rw [restrict_snoc, lastCfg_snoc]))
    have hP_card : (P.card : ℤ) =
        ∑ u : Fin 5, ((VPref R n u).card : ℤ) * T u s := by
      simp only [P, Finset.card_sigma, Finset.card_product, Nat.cast_sum, Nat.cast_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [card_step_T u s]
    rw [show n + (d + 1) = R + 1 by omega, hbij, hP_card]
    simp_rw [ih']
    rw [show R + 1 - n = d + 1 by omega, show R - n = d by omega, pow_succ T d,
      ← Matrix.mul_assoc, Matrix.mul_apply]

private lemma count_eq_b (n : ℕ) : OMA.S_oeis_a333686.count n = b n := by
  unfold OMA.S_oeis_a333686.count
  have he1 := (walk_equiv_walkF n).trans (walkF_equiv_goodEdges n)
  have he2 :
      {g : GridEdges (2 * n + 1) //
        GoodEdges (2 * n + 1) (Nat.succ_pos _) g ∧ siteDeg g ⟨n, by omega⟩ 1 = 2} ≃
        {g : GridEdges (2 * n + 1) // g ∈ VPref (2 * n) n 2} :=
    { toFun := fun ⟨g, hg, hm⟩ => ⟨g, mem_VPref.mpr
        ⟨(goodEdges_iff_validPrefix2 n g).mp hg, fun _ => hm⟩⟩
      invFun := fun ⟨g, hg⟩ => ⟨g, (goodEdges_iff_validPrefix2 n g).mpr (mem_VPref.mp hg).1,
        (mem_VPref.mp hg).2 (by omega)⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  have hcard :
      Nat.card {w : List OMA.S_oeis_a333686.Site //
        OMA.S_oeis_a333686.isWalk (2 * n + 1) 3 (0, 0) (2 * n, 2) w ∧ (n, 1) ∈ w} =
        (VPref (2 * n) n 2).card := by
    rw [Nat.card_congr (he1.trans he2), Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard]
  have hv := VPref_card_ge (2 * n) n (by omega) 2
  rw [show 2 * n - n = n by omega, ← B_eq_pow n] at hv
  exact hv

end Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a333686.main := by
  have hcount : OMA.S_oeis_a333686.count = b := funext count_eq_b
  rw [hcount]
  exact ⟨b_ogf, b_rec⟩

