import OMAStatements.S_arxiv_2603_17029

open OMA.S_arxiv_2603_17029

namespace OMA.P_arxiv_2603_17029

/-! ### 1. The 48-vertex Neumaier graph on `Fin 48 ≃ Fin 3 × Fin 4 × Fin 4` -/

private def om (a b : ℕ) : ℕ := if a / 2 = b / 2 then 0 else 1

private def pIdx (a b : ℕ) : ℕ := 2 * om a b + (a + b) % 2

private def p2Idx (a b : ℕ) : ℕ := 2 * om a b + (a + b + a / 2) % 2

private def adjBool (u v : Fin 48) : Bool :=
  let k1 := u.val / 16
  let a1 := (u.val % 16) / 4
  let b1 := u.val % 4
  let k2 := v.val / 16
  let a2 := (v.val % 16) / 4
  let b2 := v.val % 4
  if k1 == k2 then (a1 == a2) != (b1 == b2)
  else if (k1 + 1) % 3 == k2 then pIdx a1 b1 == p2Idx a2 b2
  else p2Idx a1 b1 == pIdx a2 b2

private lemma adjBool_irrefl (u : Fin 48) : adjBool u u = false := by
  simp [adjBool]

private lemma nat_beq_comm (a b : ℕ) : (a == b) = (b == a) := by
  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact eq_comm

private lemma adjBool_symm (u v : Fin 48) : adjBool u v = adjBool v u := by
  dsimp only [adjBool]
  have hk1 : u.val / 16 < 3 := by omega
  have hk2 : v.val / 16 < 3 := by omega
  by_cases h12 : u.val / 16 = v.val / 16
  · simp [h12, nat_beq_comm]
  · have hne1 : (u.val / 16 == v.val / 16) = false := beq_false_of_ne h12
    have hne2 : (v.val / 16 == u.val / 16) = false := beq_false_of_ne (Ne.symm h12)
    rw [hne1, hne2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hstep : (u.val / 16 + 1) % 3 = v.val / 16
    · have hstep' : (v.val / 16 + 1) % 3 ≠ u.val / 16 := by omega
      rw [beq_iff_eq.mpr hstep, beq_false_of_ne hstep']
      simp only [↓reduceIte, Bool.false_eq_true, nat_beq_comm]
    · have hstep' : (v.val / 16 + 1) % 3 = u.val / 16 := by omega
      rw [beq_false_of_ne hstep, beq_iff_eq.mpr hstep']
      simp only [Bool.false_eq_true, ↓reduceIte, nat_beq_comm]

private def G48 : SimpleGraph (Fin 48) where
  Adj u v := adjBool u v = true
  symm := ⟨fun u v h => by rw [adjBool_symm]; exact h⟩
  loopless := ⟨fun u h => by rw [adjBool_irrefl] at h; exact Bool.false_ne_true h⟩

local instance : DecidableRel G48.Adj := fun u v => inferInstanceAs (Decidable (adjBool u v = true))

/-! ### 2. The 9-relation equitable partition `relIdx` -/

private def relIdx (u v : Fin 48) : Fin 9 :=
  let k1 := u.val / 16
  let a1 := (u.val % 16) / 4
  let b1 := u.val % 4
  let k2 := v.val / 16
  let a2 := (v.val % 16) / 4
  let b2 := v.val % 4
  if k1 == k2 then
    if u == v then 0
    else if om a1 b1 == om a2 b2 then
      if adjBool u v then 1
      else if (pIdx a1 b1 == pIdx a2 b2) && (p2Idx a1 b1 == p2Idx a2 b2) then 2
      else 3
    else if adjBool u v then 4 else 5
  else
    if adjBool u v then 6
    else if om a1 b1 == om a2 b2 then 7 else 8

private lemma relIdx_eq_zero_iff (u v : Fin 48) : relIdx u v = 0 ↔ u = v := by
  constructor
  · intro h
    dsimp only [relIdx] at h
    split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8
    · exact beq_iff_eq.mp h2
    all_goals exact absurd h (by decide)
  · rintro rfl
    simp [relIdx]

/-! ### 3. Transitive automorphisms preserving `adjBool` and `relIdx` -/

private def mkV (k a b : ℕ) (hk : k < 3) (ha : a < 4) (hb : b < 4) : Fin 48 :=
  ⟨16 * k + 4 * a + b, by omega⟩

private lemma mkV_coords {k a b : ℕ} (hk : k < 3) (ha : a < 4) (hb : b < 4) :
    (mkV k a b hk ha hb).val / 16 = k ∧
    ((mkV k a b hk ha hb).val % 16) / 4 = a ∧
    (mkV k a b hk ha hb).val % 4 = b := by
  dsimp only [mkV]; omega

private def xor1 (x : ℕ) : ℕ := if x % 2 = 0 then x + 1 else x - 1
private def xor2 (x : ℕ) : ℕ := if x < 2 then x + 2 else x - 2
private def xor3 (x : ℕ) : ℕ := 3 - x

private lemma xor1_lt {x : ℕ} (hx : x < 4) : xor1 x < 4 := by interval_cases x <;> decide
private lemma xor2_lt {x : ℕ} (hx : x < 4) : xor2 x < 4 := by interval_cases x <;> decide
private lemma xor3_lt {x : ℕ} (hx : x < 4) : xor3 x < 4 := by interval_cases x <;> decide

private def shiftKFun (u : Fin 48) : Fin 48 :=
  mkV ((u.val / 16 + 1) % 3) ((u.val % 16) / 4) (u.val % 4) (by omega) (by omega) (by omega)

private def flipA1Fun (u : Fin 48) : Fin 48 :=
  mkV (u.val / 16) (xor1 ((u.val % 16) / 4)) (u.val % 4) (by omega) (xor1_lt (by omega)) (by omega)

private def flipB1Fun (u : Fin 48) : Fin 48 :=
  mkV (u.val / 16) ((u.val % 16) / 4) (xor1 (u.val % 4)) (by omega) (by omega) (xor1_lt (by omega))

private def flipB2Fun (u : Fin 48) : Fin 48 :=
  mkV (u.val / 16) ((u.val % 16) / 4) (xor2 (u.val % 4)) (by omega) (by omega) (xor2_lt (by omega))

private def flipA2Fun (u : Fin 48) : Fin 48 :=
  let k := u.val / 16
  let a := (u.val % 16) / 4
  let b := u.val % 4
  if k = 0 then mkV 0 (xor2 a) (xor2 b) (by omega) (xor2_lt (by omega)) (xor2_lt (by omega))
  else if k = 1 then u
  else mkV 2 (xor2 a) (xor3 b) (by omega) (xor2_lt (by omega)) (xor3_lt (by omega))

private lemma shiftK_adj (u v : Fin 48) : adjBool (shiftKFun u) (shiftKFun v) = adjBool u v := by
  dsimp only [adjBool, shiftKFun, mkV]
  have hu : u.val < 48 := u.isLt; have hv : v.val < 48 := v.isLt
  have h1 : (16 * ((u.val / 16 + 1) % 3) + 4 * (u.val % 16 / 4) + u.val % 4) / 16 = (u.val / 16 + 1) % 3 := by omega
  have h2 : (16 * ((u.val / 16 + 1) % 3) + 4 * (u.val % 16 / 4) + u.val % 4) % 16 / 4 = u.val % 16 / 4 := by omega
  have h3 : (16 * ((u.val / 16 + 1) % 3) + 4 * (u.val % 16 / 4) + u.val % 4) % 4 = u.val % 4 := by omega
  have h4 : (16 * ((v.val / 16 + 1) % 3) + 4 * (v.val % 16 / 4) + v.val % 4) / 16 = (v.val / 16 + 1) % 3 := by omega
  have h5 : (16 * ((v.val / 16 + 1) % 3) + 4 * (v.val % 16 / 4) + v.val % 4) % 16 / 4 = v.val % 16 / 4 := by omega
  have h6 : (16 * ((v.val / 16 + 1) % 3) + 4 * (v.val % 16 / 4) + v.val % 4) % 4 = v.val % 4 := by omega
  rw [h1, h2, h3, h4, h5, h6]
  have heq1 : ((u.val / 16 + 1) % 3 == (v.val / 16 + 1) % 3) = (u.val / 16 == v.val / 16) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
  have heq2 : (((u.val / 16 + 1) % 3 + 1) % 3 == (v.val / 16 + 1) % 3) = ((u.val / 16 + 1) % 3 == v.val / 16) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
  rw [heq1, heq2]

private lemma shiftK_inj : Function.Injective shiftKFun := by
  intro u v h
  have hv := congrArg Fin.val h
  dsimp only [shiftKFun, mkV] at hv
  exact Fin.ext (by omega)

private lemma shiftK_rel (u v : Fin 48) : relIdx (shiftKFun u) (shiftKFun v) = relIdx u v := by
  dsimp only [relIdx]
  rw [shiftK_adj]
  have hu : u.val < 48 := u.isLt; have hv : v.val < 48 := v.isLt
  have h1 : (shiftKFun u).val / 16 = (u.val / 16 + 1) % 3 := by dsimp [shiftKFun, mkV]; omega
  have h2 : (shiftKFun u).val % 16 / 4 = u.val % 16 / 4 := by dsimp [shiftKFun, mkV]; omega
  have h3 : (shiftKFun u).val % 4 = u.val % 4 := by dsimp [shiftKFun, mkV]; omega
  have h4 : (shiftKFun v).val / 16 = (v.val / 16 + 1) % 3 := by dsimp [shiftKFun, mkV]; omega
  have h5 : (shiftKFun v).val % 16 / 4 = v.val % 16 / 4 := by dsimp [shiftKFun, mkV]; omega
  have h6 : (shiftKFun v).val % 4 = v.val % 4 := by dsimp [shiftKFun, mkV]; omega
  rw [h1, h2, h3, h4, h5, h6]
  have heq1 : ((u.val / 16 + 1) % 3 == (v.val / 16 + 1) % 3) = (u.val / 16 == v.val / 16) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
  have heq2 : (shiftKFun u == shiftKFun v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact shiftK_inj.eq_iff
  rw [heq1, heq2]

private lemma two_mul_add_mod2_beq (x1 y1 x2 y2 : ℕ) :
    ((2 * x1 + (y1 + 1) % 2) == (2 * x2 + (y2 + 1) % 2)) =
    ((2 * x1 + y1 % 2) == (2 * x2 + y2 % 2)) := by
  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega

private lemma two_mul_one_sub_beq {x1 x2 : ℕ} (h1 : x1 ≤ 1) (h2 : x2 ≤ 1) (y1 y2 : ℕ) :
    ((2 * (1 - x1) + y1 % 2) == (2 * (1 - x2) + y2 % 2)) =
    ((2 * x1 + y1 % 2) == (2 * x2 + y2 % 2)) := by
  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega

private lemma om_le_one (x y : ℕ) : om x y ≤ 1 := by
  dsimp only [om]; split_ifs <;> omega

private lemma xor1_invol {x : ℕ} (hx : x < 4) : xor1 (xor1 x) = x := by interval_cases x <;> rfl
private lemma xor2_invol {x : ℕ} (hx : x < 4) : xor2 (xor2 x) = x := by interval_cases x <;> rfl
private lemma xor3_invol {x : ℕ} (hx : x < 4) : xor3 (xor3 x) = x := by interval_cases x <;> rfl

private lemma xor1_inj_iff {x y : ℕ} (hx : x < 4) (hy : y < 4) :
    (xor1 x == xor1 y) = (x == y) := by interval_cases x <;> interval_cases y <;> rfl

private lemma xor2_inj_iff {x y : ℕ} (hx : x < 4) (hy : y < 4) :
    (xor2 x == xor2 y) = (x == y) := by interval_cases x <;> interval_cases y <;> rfl

private lemma xor3_inj_iff {x y : ℕ} (hx : x < 4) (hy : y < 4) :
    (xor3 x == xor3 y) = (x == y) := by interval_cases x <;> interval_cases y <;> rfl

private lemma om_xor1_left {a b : ℕ} (ha : a < 4) (hb : b < 4) : om (xor1 a) b = om a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma om_xor1_right {a b : ℕ} (ha : a < 4) (hb : b < 4) : om a (xor1 b) = om a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma om_xor2_right {a b : ℕ} (ha : a < 4) (hb : b < 4) : om a (xor2 b) = 1 - om a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma om_xor2_both {a b : ℕ} (ha : a < 4) (hb : b < 4) : om (xor2 a) (xor2 b) = om a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma om_xor2_xor3 {a b : ℕ} (ha : a < 4) (hb : b < 4) : om (xor2 a) (xor3 b) = om a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma pIdx_xor1_left {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    pIdx (xor1 a) b = 2 * om a b + (a + b + 1) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma p2Idx_xor1_left {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    p2Idx (xor1 a) b = 2 * om a b + (a + b + a / 2 + 1) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma pIdx_xor1_right {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    pIdx a (xor1 b) = 2 * om a b + (a + b + 1) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma p2Idx_xor1_right {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    p2Idx a (xor1 b) = 2 * om a b + (a + b + a / 2 + 1) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma pIdx_xor2_right {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    pIdx a (xor2 b) = 2 * (1 - om a b) + (a + b) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma p2Idx_xor2_right {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    p2Idx a (xor2 b) = 2 * (1 - om a b) + (a + b + a / 2) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma pIdx_xor2_both {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    pIdx (xor2 a) (xor2 b) = pIdx a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma p2Idx_xor2_both {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    p2Idx (xor2 a) (xor2 b) = 2 * om a b + (a + b + a / 2 + 1) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma pIdx_xor2_xor3 {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    pIdx (xor2 a) (xor3 b) = 2 * om a b + (a + b + 1) % 2 := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma p2Idx_xor2_xor3 {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    p2Idx (xor2 a) (xor3 b) = p2Idx a b := by
  interval_cases a <;> interval_cases b <;> rfl

private lemma fin48_ext_coords {u v : Fin 48}
    (hk : u.val / 16 = v.val / 16) (ha : u.val % 16 / 4 = v.val % 16 / 4) (hb : u.val % 4 = v.val % 4) :
    u = v := Fin.ext (by omega)

private lemma shiftK_coords (u : Fin 48) :
    (shiftKFun u).val / 16 = (u.val / 16 + 1) % 3 ∧
    (shiftKFun u).val % 16 / 4 = u.val % 16 / 4 ∧
    (shiftKFun u).val % 4 = u.val % 4 :=
  mkV_coords _ _ _

private lemma flipA1_coords (u : Fin 48) :
    (flipA1Fun u).val / 16 = u.val / 16 ∧
    (flipA1Fun u).val % 16 / 4 = xor1 (u.val % 16 / 4) ∧
    (flipA1Fun u).val % 4 = u.val % 4 :=
  mkV_coords _ _ _

private lemma flipA1_invol (u : Fin 48) : flipA1Fun (flipA1Fun u) = u := by
  obtain ⟨h1, h2, h3⟩ := flipA1_coords u
  obtain ⟨g1, g2, g3⟩ := flipA1_coords (flipA1Fun u)
  exact fin48_ext_coords (by rw [g1, h1]) (by rw [g2, h2, xor1_invol (by omega)]) (by rw [g3, h3])

private lemma flipA1_adj (u v : Fin 48) : adjBool (flipA1Fun u) (flipA1Fun v) = adjBool u v := by
  dsimp only [adjBool]
  obtain ⟨hu1, hu2, hu3⟩ := flipA1_coords u
  obtain ⟨hv1, hv2, hv3⟩ := flipA1_coords v
  rw [hu1, hu2, hu3, hv1, hv2, hv3]
  by_cases hk : u.val / 16 = v.val / 16
  · rw [beq_iff_eq.mpr hk]; simp only [↓reduceIte]
    rw [xor1_inj_iff (by omega) (by omega)]
  · rw [beq_false_of_ne hk]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [pIdx_xor1_left (by omega) (by omega), p2Idx_xor1_left (by omega) (by omega),
        pIdx_xor1_left (by omega) (by omega), p2Idx_xor1_left (by omega) (by omega)]
    by_cases hs : (u.val / 16 + 1) % 3 = v.val / 16
    · rw [beq_iff_eq.mpr hs]; simp only [↓reduceIte]; exact two_mul_add_mod2_beq _ _ _ _
    · rw [beq_false_of_ne hs]; simp only [Bool.false_eq_true, ↓reduceIte]; exact two_mul_add_mod2_beq _ _ _ _

private lemma flipA1_rel (u v : Fin 48) : relIdx (flipA1Fun u) (flipA1Fun v) = relIdx u v := by
  dsimp only [relIdx]; rw [flipA1_adj]
  obtain ⟨hu1, hu2, hu3⟩ := flipA1_coords u
  obtain ⟨hv1, hv2, hv3⟩ := flipA1_coords v
  rw [hu1, hu2, hu3, hv1, hv2, hv3, om_xor1_left (by omega) (by omega), om_xor1_left (by omega) (by omega),
      pIdx_xor1_left (by omega) (by omega), pIdx_xor1_left (by omega) (by omega),
      p2Idx_xor1_left (by omega) (by omega), p2Idx_xor1_left (by omega) (by omega)]
  have heq : (flipA1Fun u == flipA1Fun v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨fun h => by rw [← flipA1_invol u, ← flipA1_invol v, h], fun h => by rw [h]⟩
  rw [heq, two_mul_add_mod2_beq, two_mul_add_mod2_beq]
  rfl

private lemma flipB1_coords (u : Fin 48) :
    (flipB1Fun u).val / 16 = u.val / 16 ∧
    (flipB1Fun u).val % 16 / 4 = u.val % 16 / 4 ∧
    (flipB1Fun u).val % 4 = xor1 (u.val % 4) :=
  mkV_coords _ _ _

private lemma flipB1_invol (u : Fin 48) : flipB1Fun (flipB1Fun u) = u := by
  obtain ⟨h1, h2, h3⟩ := flipB1_coords u
  obtain ⟨g1, g2, g3⟩ := flipB1_coords (flipB1Fun u)
  exact fin48_ext_coords (by rw [g1, h1]) (by rw [g2, h2]) (by rw [g3, h3, xor1_invol (by omega)])

private lemma flipB1_adj (u v : Fin 48) : adjBool (flipB1Fun u) (flipB1Fun v) = adjBool u v := by
  dsimp only [adjBool]
  obtain ⟨hu1, hu2, hu3⟩ := flipB1_coords u
  obtain ⟨hv1, hv2, hv3⟩ := flipB1_coords v
  rw [hu1, hu2, hu3, hv1, hv2, hv3]
  by_cases hk : u.val / 16 = v.val / 16
  · rw [beq_iff_eq.mpr hk]; simp only [↓reduceIte]
    rw [xor1_inj_iff (by omega) (by omega)]
  · rw [beq_false_of_ne hk]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [pIdx_xor1_right (by omega) (by omega), p2Idx_xor1_right (by omega) (by omega),
        pIdx_xor1_right (by omega) (by omega), p2Idx_xor1_right (by omega) (by omega)]
    by_cases hs : (u.val / 16 + 1) % 3 = v.val / 16
    · rw [beq_iff_eq.mpr hs]; simp only [↓reduceIte]; exact two_mul_add_mod2_beq _ _ _ _
    · rw [beq_false_of_ne hs]; simp only [Bool.false_eq_true, ↓reduceIte]; exact two_mul_add_mod2_beq _ _ _ _

private lemma flipB1_rel (u v : Fin 48) : relIdx (flipB1Fun u) (flipB1Fun v) = relIdx u v := by
  dsimp only [relIdx]; rw [flipB1_adj]
  obtain ⟨hu1, hu2, hu3⟩ := flipB1_coords u
  obtain ⟨hv1, hv2, hv3⟩ := flipB1_coords v
  rw [hu1, hu2, hu3, hv1, hv2, hv3, om_xor1_right (by omega) (by omega), om_xor1_right (by omega) (by omega),
      pIdx_xor1_right (by omega) (by omega), pIdx_xor1_right (by omega) (by omega),
      p2Idx_xor1_right (by omega) (by omega), p2Idx_xor1_right (by omega) (by omega)]
  have heq : (flipB1Fun u == flipB1Fun v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨fun h => by rw [← flipB1_invol u, ← flipB1_invol v, h], fun h => by rw [h]⟩
  rw [heq, two_mul_add_mod2_beq, two_mul_add_mod2_beq]
  rfl

private lemma flipB2_coords (u : Fin 48) :
    (flipB2Fun u).val / 16 = u.val / 16 ∧
    (flipB2Fun u).val % 16 / 4 = u.val % 16 / 4 ∧
    (flipB2Fun u).val % 4 = xor2 (u.val % 4) :=
  mkV_coords _ _ _

private lemma flipB2_invol (u : Fin 48) : flipB2Fun (flipB2Fun u) = u := by
  obtain ⟨h1, h2, h3⟩ := flipB2_coords u
  obtain ⟨g1, g2, g3⟩ := flipB2_coords (flipB2Fun u)
  exact fin48_ext_coords (by rw [g1, h1]) (by rw [g2, h2]) (by rw [g3, h3, xor2_invol (by omega)])

private lemma flipB2_adj (u v : Fin 48) : adjBool (flipB2Fun u) (flipB2Fun v) = adjBool u v := by
  dsimp only [adjBool]
  obtain ⟨hu1, hu2, hu3⟩ := flipB2_coords u
  obtain ⟨hv1, hv2, hv3⟩ := flipB2_coords v
  rw [hu1, hu2, hu3, hv1, hv2, hv3]
  by_cases hk : u.val / 16 = v.val / 16
  · rw [beq_iff_eq.mpr hk]; simp only [↓reduceIte]
    rw [xor2_inj_iff (by omega) (by omega)]
  · rw [beq_false_of_ne hk]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [pIdx_xor2_right (by omega) (by omega), p2Idx_xor2_right (by omega) (by omega),
        pIdx_xor2_right (by omega) (by omega), p2Idx_xor2_right (by omega) (by omega)]
    have ho1 := om_le_one (u.val % 16 / 4) (u.val % 4)
    have ho2 := om_le_one (v.val % 16 / 4) (v.val % 4)
    by_cases hs : (u.val / 16 + 1) % 3 = v.val / 16
    · rw [beq_iff_eq.mpr hs]; simp only [↓reduceIte]; exact two_mul_one_sub_beq ho1 ho2 _ _
    · rw [beq_false_of_ne hs]; simp only [Bool.false_eq_true, ↓reduceIte]; exact two_mul_one_sub_beq ho1 ho2 _ _

private lemma flipB2_rel (u v : Fin 48) : relIdx (flipB2Fun u) (flipB2Fun v) = relIdx u v := by
  dsimp only [relIdx]; rw [flipB2_adj]
  obtain ⟨hu1, hu2, hu3⟩ := flipB2_coords u
  obtain ⟨hv1, hv2, hv3⟩ := flipB2_coords v
  rw [hu1, hu2, hu3, hv1, hv2, hv3,
      om_xor2_right (by omega) (by omega), om_xor2_right (by omega) (by omega),
      pIdx_xor2_right (by omega) (by omega), pIdx_xor2_right (by omega) (by omega),
      p2Idx_xor2_right (by omega) (by omega), p2Idx_xor2_right (by omega) (by omega)]
  have ho1 := om_le_one (u.val % 16 / 4) (u.val % 4)
  have ho2 := om_le_one (v.val % 16 / 4) (v.val % 4)
  have heq : (flipB2Fun u == flipB2Fun v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨fun h => by rw [← flipB2_invol u, ← flipB2_invol v, h], fun h => by rw [h]⟩
  have hom : (1 - om (u.val % 16 / 4) (u.val % 4) == 1 - om (v.val % 16 / 4) (v.val % 4)) =
      (om (u.val % 16 / 4) (u.val % 4) == om (v.val % 16 / 4) (v.val % 4)) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; omega
  rw [heq, hom, two_mul_one_sub_beq ho1 ho2, two_mul_one_sub_beq ho1 ho2]
  rfl

private lemma flipA2_coords (u : Fin 48) :
    (flipA2Fun u).val / 16 = u.val / 16 ∧
    (flipA2Fun u).val % 16 / 4 = (if u.val / 16 = 1 then u.val % 16 / 4 else xor2 (u.val % 16 / 4)) ∧
    (flipA2Fun u).val % 4 = (if u.val / 16 = 0 then xor2 (u.val % 4)
      else if u.val / 16 = 1 then u.val % 4 else xor3 (u.val % 4)) := by
  have hu : u.val < 48 := u.isLt
  dsimp only [flipA2Fun]
  by_cases h0 : u.val / 16 = 0
  · rw [if_pos h0, if_neg (by omega), if_pos h0, h0]
    exact mkV_coords _ _ _
  · by_cases h1 : u.val / 16 = 1
    · rw [if_neg h0, if_pos h1, if_pos h1, if_neg h0, if_pos h1]
      exact ⟨rfl, rfl, rfl⟩
    · have h2 : u.val / 16 = 2 := by omega
      rw [if_neg h0, if_neg h1, if_neg h1, if_neg h0, if_neg h1, h2]
      exact mkV_coords _ _ _

private lemma flipA2_invol (u : Fin 48) : flipA2Fun (flipA2Fun u) = u := by
  obtain ⟨h1, h2, h3⟩ := flipA2_coords u
  obtain ⟨g1, g2, g3⟩ := flipA2_coords (flipA2Fun u)
  rw [h1] at g1 g2 g3
  have ha : u.val % 16 / 4 < 4 := by omega
  have hb : u.val % 4 < 4 := by omega
  refine fin48_ext_coords g1 ?_ ?_
  · rw [g2, h2]
    by_cases k1 : u.val / 16 = 1
    · rw [if_pos k1, if_pos k1]
    · rw [if_neg k1, if_neg k1, xor2_invol ha]
  · rw [g3, h3]
    by_cases k0 : u.val / 16 = 0
    · rw [if_pos k0, if_pos k0, xor2_invol hb]
    · by_cases k1 : u.val / 16 = 1
      · rw [if_neg k0, if_pos k1, if_neg k0, if_pos k1]
      · rw [if_neg k0, if_neg k1, if_neg k0, if_neg k1, xor3_invol hb]

private lemma flipA2_k (u : Fin 48) : (flipA2Fun u).val / 16 = u.val / 16 :=
  (flipA2_coords u).1

private lemma flipA2_om (u : Fin 48) :
    om ((flipA2Fun u).val % 16 / 4) ((flipA2Fun u).val % 4) = om (u.val % 16 / 4) (u.val % 4) := by
  obtain ⟨_, h2, h3⟩ := flipA2_coords u
  rw [h2, h3]
  by_cases h0 : u.val / 16 = 0
  · rw [if_neg (by omega), if_pos h0]; exact om_xor2_both (by omega) (by omega)
  · by_cases h1 : u.val / 16 = 1
    · rw [if_pos h1, if_neg h0, if_pos h1]
    · rw [if_neg h1, if_neg h0, if_neg h1]; exact om_xor2_xor3 (by omega) (by omega)

private lemma flipA2_pIdx (u : Fin 48) :
    pIdx ((flipA2Fun u).val % 16 / 4) ((flipA2Fun u).val % 4) =
      if u.val / 16 = 2 then
        2 * om (u.val % 16 / 4) (u.val % 4) + (u.val % 16 / 4 + u.val % 4 + 1) % 2
      else pIdx (u.val % 16 / 4) (u.val % 4) := by
  have hu : u.val < 48 := u.isLt
  obtain ⟨_, h2, h3⟩ := flipA2_coords u
  rw [h2, h3]
  by_cases h0 : u.val / 16 = 0
  · rw [if_neg (by omega), if_pos h0, if_neg (by omega)]; exact pIdx_xor2_both (by omega) (by omega)
  · by_cases h1 : u.val / 16 = 1
    · rw [if_pos h1, if_neg h0, if_pos h1, if_neg (by omega)]
    · rw [if_neg h1, if_neg h0, if_neg h1, if_pos (by omega)]; exact pIdx_xor2_xor3 (by omega) (by omega)

private lemma flipA2_p2Idx (u : Fin 48) :
    p2Idx ((flipA2Fun u).val % 16 / 4) ((flipA2Fun u).val % 4) =
      if u.val / 16 = 0 then
        2 * om (u.val % 16 / 4) (u.val % 4) + (u.val % 16 / 4 + u.val % 4 + u.val % 16 / 4 / 2 + 1) % 2
      else p2Idx (u.val % 16 / 4) (u.val % 4) := by
  have hu : u.val < 48 := u.isLt
  obtain ⟨_, h2, h3⟩ := flipA2_coords u
  rw [h2, h3]
  by_cases h0 : u.val / 16 = 0
  · rw [if_neg (by omega), if_pos h0, if_pos h0]; exact p2Idx_xor2_both (by omega) (by omega)
  · by_cases h1 : u.val / 16 = 1
    · rw [if_pos h1, if_neg h0, if_pos h1, if_neg h0]
    · rw [if_neg h1, if_neg h0, if_neg h1, if_neg h0]; exact p2Idx_xor2_xor3 (by omega) (by omega)

private lemma flipA2_adj (u v : Fin 48) : adjBool (flipA2Fun u) (flipA2Fun v) = adjBool u v := by
  dsimp only [adjBool]
  rw [flipA2_k u, flipA2_k v, flipA2_pIdx u, flipA2_pIdx v, flipA2_p2Idx u, flipA2_p2Idx v]
  have hu : u.val < 48 := u.isLt; have hv : v.val < 48 := v.isLt
  by_cases hk : u.val / 16 = v.val / 16
  · rw [beq_iff_eq.mpr hk]; simp only [↓reduceIte]
    obtain ⟨_, hua, hub⟩ := flipA2_coords u
    obtain ⟨_, hva, hvb⟩ := flipA2_coords v
    rw [hua, hub, hva, hvb, ← hk]
    by_cases h0 : u.val / 16 = 0
    · simp only [h0, show (0 : ℕ) ≠ 1 from by decide, ↓reduceIte]
      rw [xor2_inj_iff (by omega) (by omega), xor2_inj_iff (by omega) (by omega)]
    · by_cases h1 : u.val / 16 = 1
      · simp only [h1, show (1 : ℕ) ≠ 0 from by decide, ↓reduceIte]
      · simp only [h0, h1, ↓reduceIte]
        rw [xor2_inj_iff (by omega) (by omega), xor3_inj_iff (by omega) (by omega)]
  · rw [beq_false_of_ne hk]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hcases : u.val / 16 = 0 ∨ u.val / 16 = 1 ∨ u.val / 16 = 2 := by omega
    have hcases' : v.val / 16 = 0 ∨ v.val / 16 = 1 ∨ v.val / 16 = 2 := by omega
    rcases hcases with hu | hu | hu <;> rcases hcases' with hv | hv | hv
    all_goals try omega
    all_goals simp only [hu, hv, Nat.zero_add, Nat.reduceAdd, Nat.reduceMod,
      beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      show (1 == 2) = false from rfl, show (2 == 0) = false from rfl, show (0 == 1) = false from rfl,
      OfNat.zero_ne_ofNat, show (2 : ℕ) ≠ 0 from by decide, show (1 : ℕ) ≠ 2 from by decide]
    all_goals try exact two_mul_add_mod2_beq _ _ _ _
    all_goals rfl

private lemma flipA2_rel (u v : Fin 48) : relIdx (flipA2Fun u) (flipA2Fun v) = relIdx u v := by
  dsimp only [relIdx]
  rw [flipA2_adj, flipA2_k u, flipA2_k v, flipA2_om u, flipA2_om v,
      flipA2_pIdx u, flipA2_pIdx v, flipA2_p2Idx u, flipA2_p2Idx v]
  have heq : (flipA2Fun u == flipA2Fun v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
    exact ⟨fun h => by rw [← flipA2_invol u, ← flipA2_invol v, h], fun h => by rw [h]⟩
  rw [heq]
  by_cases hk : u.val / 16 = v.val / 16
  · rw [beq_iff_eq.mpr hk]; simp only [↓reduceIte]
    rw [hk]
    have hp : ((if v.val / 16 = 2 then 2 * om (u.val % 16 / 4) (u.val % 4) + (u.val % 16 / 4 + u.val % 4 + 1) % 2
                else pIdx (u.val % 16 / 4) (u.val % 4)) ==
               (if v.val / 16 = 2 then 2 * om (v.val % 16 / 4) (v.val % 4) + (v.val % 16 / 4 + v.val % 4 + 1) % 2
                else pIdx (v.val % 16 / 4) (v.val % 4))) =
              (pIdx (u.val % 16 / 4) (u.val % 4) == pIdx (v.val % 16 / 4) (v.val % 4)) := by
      by_cases h2 : v.val / 16 = 2
      · rw [if_pos h2, if_pos h2]; exact two_mul_add_mod2_beq _ _ _ _
      · rw [if_neg h2, if_neg h2]
    have hp2 : ((if v.val / 16 = 0 then 2 * om (u.val % 16 / 4) (u.val % 4) + (u.val % 16 / 4 + u.val % 4 + u.val % 16 / 4 / 2 + 1) % 2
                 else p2Idx (u.val % 16 / 4) (u.val % 4)) ==
                (if v.val / 16 = 0 then 2 * om (v.val % 16 / 4) (v.val % 4) + (v.val % 16 / 4 + v.val % 4 + v.val % 16 / 4 / 2 + 1) % 2
                 else p2Idx (v.val % 16 / 4) (v.val % 4))) =
               (p2Idx (u.val % 16 / 4) (u.val % 4) == p2Idx (v.val % 16 / 4) (v.val % 4)) := by
      by_cases h0 : v.val / 16 = 0
      · rw [if_pos h0, if_pos h0]; exact two_mul_add_mod2_beq _ _ _ _
      · rw [if_neg h0, if_neg h0]
    rw [hp, hp2]
  · rw [beq_false_of_ne hk]; simp only [Bool.false_eq_true, ↓reduceIte]

private def shiftKInvFun (u : Fin 48) : Fin 48 :=
  mkV ((u.val / 16 + 2) % 3) ((u.val % 16) / 4) (u.val % 4) (by omega) (by omega) (by omega)

private lemma shiftK_left_inv (u : Fin 48) : shiftKInvFun (shiftKFun u) = u := by
  have hu : u.val < 48 := u.isLt
  obtain ⟨h1, h2, h3⟩ := shiftK_coords u
  obtain ⟨g1, g2, g3⟩ := mkV_coords (k := ((shiftKFun u).val / 16 + 2) % 3)
    (a := (shiftKFun u).val % 16 / 4) (b := (shiftKFun u).val % 4) (by omega) (by omega) (by omega)
  exact fin48_ext_coords (by change (mkV _ _ _ _ _ _).val / 16 = _; rw [g1, h1]; omega)
    (by change (mkV _ _ _ _ _ _).val % 16 / 4 = _; rw [g2, h2])
    (by change (mkV _ _ _ _ _ _).val % 4 = _; rw [g3, h3])

private lemma shiftK_right_inv (u : Fin 48) : shiftKFun (shiftKInvFun u) = u := by
  have hu : u.val < 48 := u.isLt
  obtain ⟨h1, h2, h3⟩ := mkV_coords (k := (u.val / 16 + 2) % 3)
    (a := u.val % 16 / 4) (b := u.val % 4) (by omega) (by omega) (by omega)
  obtain ⟨g1, g2, g3⟩ := shiftK_coords (shiftKInvFun u)
  exact fin48_ext_coords (by rw [g1]; change ((mkV _ _ _ _ _ _).val / 16 + 1) % 3 = _; rw [h1]; omega)
    (by rw [g2]; exact h2) (by rw [g3]; exact h3)

private def shiftKEquiv : Equiv.Perm (Fin 48) :=
  ⟨shiftKFun, shiftKInvFun, shiftK_left_inv, shiftK_right_inv⟩

private def flipA1Equiv : Equiv.Perm (Fin 48) :=
  ⟨flipA1Fun, flipA1Fun, flipA1_invol, flipA1_invol⟩

private def flipB1Equiv : Equiv.Perm (Fin 48) :=
  ⟨flipB1Fun, flipB1Fun, flipB1_invol, flipB1_invol⟩

private def flipB2Equiv : Equiv.Perm (Fin 48) :=
  ⟨flipB2Fun, flipB2Fun, flipB2_invol, flipB2_invol⟩

private def flipA2Equiv : Equiv.Perm (Fin 48) :=
  ⟨flipA2Fun, flipA2Fun, flipA2_invol, flipA2_invol⟩

private def step1Equiv (x : Fin 48) : Equiv.Perm (Fin 48) :=
  if x.val / 16 = 0 then Equiv.refl _
  else if x.val / 16 = 1 then shiftKEquiv.trans shiftKEquiv
  else shiftKEquiv

private def step2Equiv (x : Fin 48) : Equiv.Perm (Fin 48) :=
  if (x.val % 16) / 4 < 2 then Equiv.refl _ else flipA2Equiv

private def step3Equiv (x : Fin 48) : Equiv.Perm (Fin 48) :=
  if ((x.val % 16) / 4) % 2 = 0 then Equiv.refl _ else flipA1Equiv

private def step4Equiv (x : Fin 48) : Equiv.Perm (Fin 48) :=
  if x.val % 4 < 2 then Equiv.refl _ else flipB2Equiv

private def step5Equiv (x : Fin 48) : Equiv.Perm (Fin 48) :=
  if (x.val % 4) % 2 = 0 then Equiv.refl _ else flipB1Equiv

private def toZero (x : Fin 48) : Equiv.Perm (Fin 48) :=
  let e1 := step1Equiv x
  let x1 := e1 x
  let e2 := step2Equiv x1
  let x2 := e2 x1
  let e3 := step3Equiv x2
  let x3 := e3 x2
  let e4 := step4Equiv x3
  let x4 := e4 x3
  let e5 := step5Equiv x4
  ((((e1.trans e2).trans e3).trans e4).trans e5)

private lemma step1_k (y : Fin 48) : (step1Equiv y y).val / 16 = 0 := by
  have hy : y.val < 48 := y.isLt
  unfold step1Equiv
  by_cases k0 : y.val / 16 = 0
  · rw [if_pos k0]; exact k0
  · by_cases k1 : y.val / 16 = 1
    · rw [if_neg k0, if_pos k1]
      change (shiftKFun (shiftKFun y)).val / 16 = 0
      rw [(shiftK_coords _).1, (shiftK_coords _).1, k1]
    · rw [if_neg k0, if_neg k1]
      change (shiftKFun y).val / 16 = 0
      rw [(shiftK_coords _).1]; omega

private lemma step2_ka (y : Fin 48) (hy : y.val / 16 = 0) :
    (step2Equiv y y).val / 16 = 0 ∧ (step2Equiv y y).val % 16 / 4 < 2 := by
  unfold step2Equiv
  by_cases ha : y.val % 16 / 4 < 2
  · rw [if_pos ha]; exact ⟨hy, ha⟩
  · rw [if_neg ha]
    change (flipA2Fun y).val / 16 = 0 ∧ (flipA2Fun y).val % 16 / 4 < 2
    obtain ⟨c1, c2, _⟩ := flipA2_coords y
    rw [c1, c2, hy, if_neg (by omega)]
    exact ⟨rfl, by dsimp [xor2]; rw [if_neg ha]; omega⟩

private lemma step3_ka (y : Fin 48) (hy1 : y.val / 16 = 0) (hy2 : y.val % 16 / 4 < 2) :
    (step3Equiv y y).val / 16 = 0 ∧ (step3Equiv y y).val % 16 / 4 = 0 := by
  unfold step3Equiv
  by_cases ha : (y.val % 16 / 4) % 2 = 0
  · rw [if_pos ha, Equiv.refl_apply]; exact ⟨hy1, by omega⟩
  · rw [if_neg ha]
    change (flipA1Fun y).val / 16 = 0 ∧ (flipA1Fun y).val % 16 / 4 = 0
    obtain ⟨c1, c2, _⟩ := flipA1_coords y
    rw [c1, c2, hy1]
    exact ⟨rfl, by dsimp [xor1]; rw [if_neg ha]; omega⟩

private lemma step4_kab (y : Fin 48) (hy1 : y.val / 16 = 0) (hy2 : y.val % 16 / 4 = 0) :
    (step4Equiv y y).val / 16 = 0 ∧ (step4Equiv y y).val % 16 / 4 = 0 ∧ (step4Equiv y y).val % 4 < 2 := by
  unfold step4Equiv
  by_cases hb : y.val % 4 < 2
  · rw [if_pos hb, Equiv.refl_apply]; exact ⟨hy1, hy2, hb⟩
  · rw [if_neg hb]
    change (flipB2Fun y).val / 16 = 0 ∧ (flipB2Fun y).val % 16 / 4 = 0 ∧ (flipB2Fun y).val % 4 < 2
    obtain ⟨c1, c2, c3⟩ := flipB2_coords y
    rw [c1, c2, c3, hy1, hy2]
    exact ⟨rfl, rfl, by dsimp [xor2]; rw [if_neg hb]; omega⟩

private lemma step5_zero (y : Fin 48) (hy1 : y.val / 16 = 0) (hy2 : y.val % 16 / 4 = 0) (hy3 : y.val % 4 < 2) :
    step5Equiv y y = 0 := by
  unfold step5Equiv
  by_cases hb : (y.val % 4) % 2 = 0
  · rw [if_pos hb, Equiv.refl_apply]; exact fin48_ext_coords hy1 hy2 (by omega)
  · rw [if_neg hb]
    change flipB1Fun y = 0
    obtain ⟨c1, c2, c3⟩ := flipB1_coords y
    exact fin48_ext_coords (by rw [c1, hy1]; rfl) (by rw [c2, hy2]; rfl)
      (by rw [c3]; dsimp [xor1]; rw [if_neg hb]; omega)

private lemma toZero_self (x : Fin 48) : toZero x x = 0 := by
  unfold toZero
  dsimp only [Equiv.trans_apply]
  have hx1 := step1_k x
  obtain ⟨hx2k, hx2a⟩ := step2_ka _ hx1
  obtain ⟨hx3k, hx3a⟩ := step3_ka _ hx2k hx2a
  obtain ⟨hx4k, hx4a, hx4b⟩ := step4_kab _ hx3k hx3a
  exact step5_zero _ hx4k hx4a hx4b

private lemma ite_pres {P : Equiv.Perm (Fin 48) → Prop} (c : Prop) [Decidable c]
    {e1 e2 : Equiv.Perm (Fin 48)} (h1 : P e1) (h2 : P e2) : P (if c then e1 else e2) := by
  by_cases hc : c <;> simp [hc, h1, h2]

private lemma toZero_adj (x u v : Fin 48) : adjBool (toZero x u) (toZero x v) = adjBool u v := by
  let P : Equiv.Perm (Fin 48) → Prop := fun e => ∀ a b, adjBool (e a) (e b) = adjBool a b
  have htrans : ∀ {e f}, P e → P f → P (e.trans f) := fun he hf a b => by
    rw [Equiv.trans_apply, Equiv.trans_apply]; exact (hf _ _).trans (he _ _)
  have hr : P (Equiv.refl _) := fun _ _ => rfl
  have hs : P shiftKEquiv := shiftK_adj
  have ha2 : P flipA2Equiv := flipA2_adj
  have ha1 : P flipA1Equiv := flipA1_adj
  have hb2 : P flipB2Equiv := flipB2_adj
  have hb1 : P flipB1Equiv := flipB1_adj
  have h1 : ∀ y, P (step1Equiv y) := fun y => ite_pres _ hr (ite_pres _ (htrans hs hs) hs)
  have h2 : ∀ y, P (step2Equiv y) := fun y => ite_pres _ hr ha2
  have h3 : ∀ y, P (step3Equiv y) := fun y => ite_pres _ hr ha1
  have h4 : ∀ y, P (step4Equiv y) := fun y => ite_pres _ hr hb2
  have h5 : ∀ y, P (step5Equiv y) := fun y => ite_pres _ hr hb1
  exact (htrans (htrans (htrans (htrans (h1 _) (h2 _)) (h3 _)) (h4 _)) (h5 _)) u v

private lemma toZero_rel (x u v : Fin 48) : relIdx (toZero x u) (toZero x v) = relIdx u v := by
  let P : Equiv.Perm (Fin 48) → Prop := fun e => ∀ a b, relIdx (e a) (e b) = relIdx a b
  have htrans : ∀ {e f}, P e → P f → P (e.trans f) := fun he hf a b => by
    rw [Equiv.trans_apply, Equiv.trans_apply]; exact (hf _ _).trans (he _ _)
  have hr : P (Equiv.refl _) := fun _ _ => rfl
  have hs : P shiftKEquiv := shiftK_rel
  have ha2 : P flipA2Equiv := flipA2_rel
  have ha1 : P flipA1Equiv := flipA1_rel
  have hb2 : P flipB2Equiv := flipB2_rel
  have hb1 : P flipB1Equiv := flipB1_rel
  have h1 : ∀ y, P (step1Equiv y) := fun y => ite_pres _ hr (ite_pres _ (htrans hs hs) hs)
  have h2 : ∀ y, P (step2Equiv y) := fun y => ite_pres _ hr ha2
  have h3 : ∀ y, P (step3Equiv y) := fun y => ite_pres _ hr ha1
  have h4 : ∀ y, P (step4Equiv y) := fun y => ite_pres _ hr hb2
  have h5 : ∀ y, P (step5Equiv y) := fun y => ite_pres _ hr hb1
  exact (htrans (htrans (htrans (htrans (h1 _) (h2 _)) (h3 _)) (h4 _)) (h5 _)) u v

/-! ### 4. Fast Nat helpers and Neumaier graph verification `(48, 14, 2; 1, 4)` -/

private def adjNat (u v : ℕ) : Bool :=
  let k1 := u / 16
  let a1 := (u % 16) / 4
  let b1 := u % 4
  let k2 := v / 16
  let a2 := (v % 16) / 4
  let b2 := v % 4
  if k1 == k2 then (a1 == a2) != (b1 == b2)
  else if (k1 + 1) % 3 == k2 then pIdx a1 b1 == p2Idx a2 b2
  else p2Idx a1 b1 == pIdx a2 b2

private lemma adjNat_eq (u v : Fin 48) : adjNat u.val v.val = adjBool u v := rfl

private lemma card_filter_range (n : ℕ) (p : ℕ → Bool) :
    ((Finset.range n).filter (fun z => p z = true)).card = (List.range n).countP p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, List.range_succ, List.countP_append, List.countP_cons, List.countP_nil,
      Finset.filter_insert]
    have hnot : n ∉ (Finset.range n).filter (fun z => p z = true) := by simp
    cases hp : p n
    · simp [ih]
    · simp [Finset.card_insert_of_notMem hnot, ih]

private lemma card_filter_fin48 (p : ℕ → Bool) :
    (Finset.univ.filter (fun z : Fin 48 => p z.val = true)).card = (List.range 48).countP p := by
  have h1 : (Finset.univ.filter (fun z : Fin 48 => p z.val = true)).card =
      ((Finset.range 48).filter (fun z => p z = true)).card := by
    refine Finset.card_bij (fun z _ => z.val) ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨Finset.mem_range.mpr z.isLt, hz.2⟩
    · intro z1 _ z2 _ h; exact Fin.ext h
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      exact ⟨⟨n, hn.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn.2⟩, rfl⟩
  rw [h1, card_filter_range]

private lemma deg_at_0 :
    (Finset.univ.filter (fun w : Fin 48 => adjBool 0 w = true)).card = 14 := by
  have h := card_filter_fin48 (fun w => adjNat 0 w)
  have heq : (Finset.univ.filter (fun w : Fin 48 => adjBool 0 w = true)) =
      Finset.univ.filter (fun w : Fin 48 => adjNat 0 w.val = true) := by
    ext w
    have ha : adjBool 0 w = adjNat 0 w.val := rfl
    simp [ha]
  rw [heq, h]
  decide

private lemma deg_all (v : Fin 48) :
    (Finset.univ.filter (fun w : Fin 48 => adjBool v w = true)).card = 14 := by
  let e := toZero v
  have hbij : (Finset.univ.filter (fun w : Fin 48 => adjBool v w = true)).card =
      (Finset.univ.filter (fun w : Fin 48 => adjBool 0 w = true)).card := by
    refine Finset.card_bij (fun w _ => e w) ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← toZero_self v, toZero_adj]; exact hw.2
    · intro w1 _ w2 _ h; exact e.injective h
    · intro w hw
      rw [Finset.mem_filter] at hw
      refine ⟨e.symm w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply w⟩
      have := hw.2
      rw [← toZero_self v, ← e.apply_symm_apply w, toZero_adj] at this
      exact this
  rw [hbij, deg_at_0]

private lemma lam_at_0_check :
    (List.range 48).all (fun v => !adjNat 0 v ||
      ((List.range 48).countP (fun w => adjNat 0 w && adjNat v w) == 2)) = true := by
  decide

private lemma lam_at_0 :
    ∀ v : Fin 48, adjBool 0 v = true →
      (Finset.univ.filter (fun w : Fin 48 => adjBool 0 w = true ∧ adjBool v w = true)).card = 2 := by
  intro v hv
  have hfilt : (Finset.univ.filter (fun w : Fin 48 => adjBool 0 w = true ∧ adjBool v w = true)) =
      Finset.univ.filter (fun w : Fin 48 => (adjNat 0 w.val && adjNat v.val w.val) = true) := by
    ext w
    have h0w : adjBool 0 w = adjNat 0 w.val := rfl
    have hvw : adjBool v w = adjNat v.val w.val := rfl
    simp [h0w, hvw]
  rw [hfilt, card_filter_fin48 (fun w => adjNat 0 w && adjNat v.val w)]
  have h := lam_at_0_check
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h v.val v.isLt with h0 | h2
  · have h0v : adjNat 0 v.val = adjBool 0 v := rfl
    rw [h0v] at h0; exact absurd hv (by rw [h0]; decide)
  · exact h2

private lemma lam_all (u v : Fin 48) (huv : adjBool u v = true) :
    (Finset.univ.filter (fun w : Fin 48 => adjBool u w = true ∧ adjBool v w = true)).card = 2 := by
  let e := toZero u
  have h0v : adjBool 0 (e v) = true := by
    rw [← toZero_self u, toZero_adj]; exact huv
  have hbij : (Finset.univ.filter (fun w : Fin 48 => adjBool u w = true ∧ adjBool v w = true)).card =
      (Finset.univ.filter (fun w : Fin 48 => adjBool 0 w = true ∧ adjBool (e v) w = true)).card := by
    refine Finset.card_bij (fun w _ => e w) ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← toZero_self u, toZero_adj]; exact hw.2.1
      · rw [toZero_adj]; exact hw.2.2
    · intro w1 _ w2 _ h; exact e.injective h
    · intro w hw
      rw [Finset.mem_filter] at hw
      refine ⟨e.symm w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, e.apply_symm_apply w⟩
      · have h1 := hw.2.1; rw [← toZero_self u, ← e.apply_symm_apply w, toZero_adj] at h1; exact h1
      · have h2 := hw.2.2; rw [← e.apply_symm_apply w, toZero_adj] at h2; exact h2
  rw [hbij, lam_at_0 (e v) h0v]

private lemma dist_le2_check :
    (List.range 48).all (fun v => (v == 0) || adjNat 0 v ||
      (List.range 48).any (fun w => adjNat 0 w && adjNat w v)) = true := by
  decide

private lemma dist_le2_from_0 :
    ∀ v : Fin 48, v = 0 ∨ adjBool 0 v = true ∨ ∃ w : Fin 48, adjBool 0 w = true ∧ adjBool w v = true := by
  intro v
  have h := dist_le2_check
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, Bool.and_eq_true] at h
  rcases h v.val v.isLt with (hv0 | h1) | ⟨w, hwlt, hw1, hw2⟩
  · left; exact Fin.ext hv0
  · right; left; exact h1
  · right; right; exact ⟨⟨w, hwlt⟩, hw1, hw2⟩

private lemma G48_connected : G48.Connected := by
  refine ⟨fun u v => ?_⟩
  have hreach0 : ∀ x : Fin 48, G48.Reachable 0 x := by
    intro x
    rcases dist_le2_from_0 x with rfl | h1 | ⟨w, hw1, hw2⟩
    · exact SimpleGraph.Reachable.refl 0
    · exact SimpleGraph.Adj.reachable h1
    · exact (SimpleGraph.Adj.reachable hw1).trans (SimpleGraph.Adj.reachable hw2)
  exact (hreach0 u).symm.trans (hreach0 v)

private def cliqueC : Finset (Fin 48) := {0, 1, 2, 3}

private lemma cliqueC_nexus_check :
    (List.range 48).all (fun v => (v < 4) ||
      (([0, 1, 2, 3] : List ℕ).countP (fun w => adjNat v w) == 1)) = true := by
  decide

private lemma G48_isNeumaier : @IsNeumaierGraph 48 G48 inferInstance := by
  refine ⟨by omega, G48_connected, ⟨0, 5, by decide, by decide⟩,
    ⟨14, 2, by omega, ?_, ?_⟩, ⟨cliqueC, 1, by decide, ?_, ?_⟩⟩
  · intro v; exact deg_all v
  · intro u v huv; exact lam_all u v huv
  · intro u hu v hv hne
    have : ∀ a ∈ cliqueC, ∀ b ∈ cliqueC, a ≠ b → adjBool a b = true := by decide
    exact this u hu v hv hne
  · intro v hv
    have hv4 : ¬ (v.val < 4) := by
      intro hlt
      apply hv
      simp only [cliqueC, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    have hchk := cliqueC_nexus_check
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    have hc1 : ([0, 1, 2, 3] : List ℕ).countP (fun w => adjNat v.val w) = 1 :=
      (hchk v.val v.isLt).resolve_left hv4
    have hcard : (cliqueC.filter (G48.Adj v)).card =
        ([0, 1, 2, 3] : List ℕ).countP (fun w => adjNat v.val w) := by
      rw [Finset.card_filter, cliqueC]
      have h01 : (0 : Fin 48) ∉ ({1, 2, 3} : Finset (Fin 48)) := by decide
      have h12 : (1 : Fin 48) ∉ ({2, 3} : Finset (Fin 48)) := by decide
      have h23 : (2 : Fin 48) ∉ ({3} : Finset (Fin 48)) := by decide
      rw [Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_insert h23, Finset.sum_singleton]
      simp only [List.countP_cons, List.countP_nil]
      change (if adjNat v.val 0 = true then 1 else 0) +
        ((if adjNat v.val 1 = true then 1 else 0) +
         ((if adjNat v.val 2 = true then 1 else 0) +
          (if adjNat v.val 3 = true then 1 else 0))) = _
      cases adjNat v.val 0 <;> cases adjNat v.val 1 <;> cases adjNat v.val 2 <;> cases adjNat v.val 3 <;> rfl
    rw [hcard, hc1]

/-! ### 5. The `9 × 9` equitable relation matrix `M` and minimal polynomial -/

private def M9 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 2, 0, 0, 4, 0, 8, 0, 0;
     1, 0, 1, 0, 2, 2, 0, 8, 0;
     0, 2, 0, 0, 0, 4, 8, 0, 0;
     0, 0, 0, 2, 2, 2, 4, 4, 0;
     1, 1, 0, 2, 1, 1, 0, 0, 8;
     0, 1, 1, 2, 1, 1, 0, 0, 8;
     1, 0, 1, 2, 0, 0, 2, 4, 4;
     0, 2, 0, 2, 0, 0, 4, 2, 4;
     0, 0, 0, 0, 2, 2, 2, 2, 6]

private def M9Nat (i j : Fin 9) : ℕ := (M9 i j).toNat

private lemma M9_nonneg (i j : Fin 9) : (M9Nat i j : ℤ) = M9 i j := by
  fin_cases i <;> fin_cases j <;> rfl

private def rel0Nat (v : ℕ) : ℕ :=
  let k2 := v / 16
  let a2 := (v % 16) / 4
  let b2 := v % 4
  if k2 == 0 then
    if v == 0 then 0
    else if om a2 b2 == 0 then
      if adjNat 0 v then 1
      else if (pIdx a2 b2 == 0) && (p2Idx a2 b2 == 0) then 2
      else 3
    else if adjNat 0 v then 4 else 5
  else
    if adjNat 0 v then 6
    else if om a2 b2 == 0 then 7 else 8

private lemma rel0Nat_eq (v : Fin 48) : rel0Nat v.val = (relIdx 0 v).val := by
  dsimp only [rel0Nat, relIdx]
  have hk0 : (0 : Fin 48).val / 16 = 0 := rfl
  have ha0 : (0 : Fin 48).val % 16 / 4 = 0 := rfl
  have hb0 : (0 : Fin 48).val % 4 = 0 := rfl
  have hom0 : om 0 0 = 0 := rfl
  have hp0 : pIdx 0 0 = 0 := rfl
  have hp20 : p2Idx 0 0 = 0 := rfl
  have hadj0 : adjBool 0 v = adjNat 0 v.val := rfl
  rw [hk0, ha0, hb0, hom0, hp0, hp20, hadj0]
  have h1 : (0 == v.val / 16) = (v.val / 16 == 0) := nat_beq_comm _ _
  have h2 : ((0 : Fin 48) == v) = (v.val == 0) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Fin.ext_iff]; exact eq_comm
  have h3 : (0 == om (v.val % 16 / 4) (v.val % 4)) = (om (v.val % 16 / 4) (v.val % 4) == 0) := nat_beq_comm _ _
  have h4 : (0 == pIdx (v.val % 16 / 4) (v.val % 4)) = (pIdx (v.val % 16 / 4) (v.val % 4) == 0) := nat_beq_comm _ _
  have h5 : (0 == p2Idx (v.val % 16 / 4) (v.val % 4)) = (p2Idx (v.val % 16 / 4) (v.val % 4) == 0) := nat_beq_comm _ _
  rw [h1, h2, h3, h4, h5]
  split_ifs <;> rfl

private def M9NatRow : List (List ℕ) :=
  [[0, 2, 0, 0, 4, 0, 8, 0, 0],
   [1, 0, 1, 0, 2, 2, 0, 8, 0],
   [0, 2, 0, 0, 0, 4, 8, 0, 0],
   [0, 0, 0, 2, 2, 2, 4, 4, 0],
   [1, 1, 0, 2, 1, 1, 0, 0, 8],
   [0, 1, 1, 2, 1, 1, 0, 0, 8],
   [1, 0, 1, 2, 0, 0, 2, 4, 4],
   [0, 2, 0, 2, 0, 0, 4, 2, 4],
   [0, 0, 0, 0, 2, 2, 2, 2, 6]]

private lemma M9NatRow_eq (i j : Fin 9) :
    (M9NatRow.getD i.val []).getD j.val 0 = M9Nat i j := by
  revert i j; decide

private def checkEquitRange (lo len : ℕ) : Bool :=
  (List.range len).all fun off =>
    let y := lo + off
    let row := M9NatRow.getD (rel0Nat y) []
    let nbrRels := ((List.range 48).filter (fun z => adjNat y z)).map rel0Nat
    (List.range 9).all fun j =>
      (nbrRels.countP (fun r => r == j)) == row.getD j 0

private lemma checkEquit_0 : checkEquitRange 0 16 = true := by decide
private lemma checkEquit_1 : checkEquitRange 16 16 = true := by decide
private lemma checkEquit_2 : checkEquitRange 32 16 = true := by decide

private lemma countP_and_eq_map_filter (l : List ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) (j : ℕ) :
    l.countP (fun z => p z && (f z == j)) = ((l.filter p).map f).countP (fun r => r == j) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.countP_cons, List.filter_cons]
    cases hp : p x
    · simp [ih]
    · simp [List.map_cons, List.countP_cons, ih]

private lemma equitable_at_0 (y : Fin 48) (j : Fin 9) :
    (Finset.univ.filter (fun z : Fin 48 => adjBool y z = true ∧ relIdx 0 z = j)).card =
      M9Nat (relIdx 0 y) j := by
  have hfilt : (Finset.univ.filter (fun z : Fin 48 => adjBool y z = true ∧ relIdx 0 z = j)) =
      Finset.univ.filter (fun z : Fin 48 => (adjNat y.val z.val && (rel0Nat z.val == j.val)) = true) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq,
      adjNat_eq, rel0Nat_eq, Fin.ext_iff]
  rw [hfilt, card_filter_fin48 (fun z => adjNat y.val z && (rel0Nat z == j.val)),
      countP_and_eq_map_filter, ← M9NatRow_eq (relIdx 0 y) j, ← rel0Nat_eq y]
  have hchk : ∀ lo len, checkEquitRange lo len = true → lo ≤ y.val → y.val < lo + len →
      (((List.range 48).filter (fun z => adjNat y.val z)).map rel0Nat).countP (fun r => r == j.val) =
        (M9NatRow.getD (rel0Nat y.val) []).getD j.val 0 := by
    intro lo len h hlo hhi
    unfold checkEquitRange at h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have hy := h (y.val - lo) (by omega) j.val j.isLt
    rwa [show lo + (y.val - lo) = y.val by omega] at hy
  by_cases h1 : y.val < 16
  · exact hchk 0 16 checkEquit_0 (by omega) (by omega)
  · by_cases h2 : y.val < 32
    · exact hchk 16 16 checkEquit_1 (by omega) (by omega)
    · exact hchk 32 16 checkEquit_2 (by omega) (by omega)

private lemma equitable_all (x y : Fin 48) (j : Fin 9) :
    (Finset.univ.filter (fun z : Fin 48 => adjBool y z = true ∧ relIdx x z = j)).card =
      M9Nat (relIdx x y) j := by
  let e := toZero x
  have hrel_xy : relIdx 0 (e y) = relIdx x y := by
    rw [← toZero_self x, toZero_rel]
  have hbij : (Finset.univ.filter (fun z : Fin 48 => adjBool y z = true ∧ relIdx x z = j)).card =
      (Finset.univ.filter (fun z : Fin 48 => adjBool (e y) z = true ∧ relIdx 0 z = j)).card := by
    refine Finset.card_bij (fun z _ => e z) ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [toZero_adj]; exact hz.2.1
      · rw [← toZero_self x, toZero_rel]; exact hz.2.2
    · intro z1 _ z2 _ h; exact e.injective h
    · intro z hz
      rw [Finset.mem_filter] at hz
      refine ⟨e.symm z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, e.apply_symm_apply z⟩
      · have h1 := hz.2.1; rw [← e.apply_symm_apply z, toZero_adj] at h1; exact h1
      · have h2 := hz.2.2; rw [← toZero_self x, ← e.apply_symm_apply z, toZero_rel] at h2; exact h2
  rw [hbij, equitable_at_0 (e y) j, hrel_xy]

private def Rmat (j : Fin 9) : Matrix (Fin 48) (Fin 48) ℝ :=
  Matrix.of fun x y => if relIdx x y = j then 1 else 0

private def A48 : Matrix (Fin 48) (Fin 48) ℝ := G48.adjMatrix ℝ

private lemma Rmat_zero : Rmat 0 = 1 := by
  ext x y
  simp [Rmat, Matrix.one_apply, relIdx_eq_zero_iff]

private lemma G48_adjMatrix_ite (a b : Fin 48) :
    (if G48.Adj a b then (1 : ℝ) else 0) = if adjBool a b = true then 1 else 0 := by
  by_cases h : adjBool a b = true
  · have h' : G48.Adj a b := h
    simp [h, h']
  · have h' : ¬ G48.Adj a b := h
    simp [h, h']

private lemma Rmat_mul_A48 (j : Fin 9) :
    Rmat j * A48 = ∑ i : Fin 9, (M9 i j : ℝ) • Rmat i := by
  ext x y
  simp only [Matrix.mul_apply, Rmat, Matrix.of_apply, A48, SimpleGraph.adjMatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, G48_adjMatrix_ite]
  have hlhs : (∑ z : Fin 48, (if relIdx x z = j then (1 : ℝ) else 0) *
      (if adjBool z y = true then (1 : ℝ) else 0)) =
      ((Finset.univ.filter (fun z : Fin 48 => adjBool y z = true ∧ relIdx x z = j)).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [adjBool_symm z y]
    by_cases h1 : adjBool y z = true <;> by_cases h2 : relIdx x z = j <;> simp [h1, h2]
  have hrhs : (∑ i : Fin 9, (M9 i j : ℝ) * (if relIdx x y = i then (1 : ℝ) else 0)) =
      (M9 (relIdx x y) j : ℝ) := by
    rw [Finset.sum_eq_single (relIdx x y)]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hlhs, hrhs, equitable_all x y j]
  have hnn := M9_nonneg (relIdx x y) j
  exact_mod_cast hnn

private lemma A48_pow_eq (d : ℕ) :
    A48 ^ d = ∑ i : Fin 9, (((M9 ^ d) i 0 : ℤ) : ℝ) • Rmat i := by
  induction d with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single (0 : Fin 9)]
    · simp [Rmat_zero]
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ d ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have hstep : ∀ j : Fin 9,
        ((((M9 ^ d) j 0 : ℤ) : ℝ) • Rmat j) * A48 =
          ∑ i : Fin 9, (((M9 i j * (M9 ^ d) j 0 : ℤ) : ℝ)) • Rmat i := by
      intro j
      rw [Matrix.smul_mul, Rmat_mul_A48 j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, Int.cast_mul, mul_comm]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [pow_succ', Matrix.mul_apply]
    push_cast
    rfl

private def mv0 : Fin 9 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
private def mv1 : Fin 9 → ℤ := ![0, 1, 0, 0, 1, 0, 1, 0, 0]
private def mv2 : Fin 9 → ℤ := ![14, 2, 10, 6, 2, 2, 2, 6, 4]
private def mv3 : Fin 9 → ℤ := ![28, 80, 28, 52, 64, 60, 80, 52, 48]
private def mv4 : Fin 9 → ℤ := ![1056, 720, 1040, 880, 720, 720, 720, 880, 800]
private def mv5 : Fin 9 → ℤ := ![10080, 12016, 10080, 11040, 11376, 11360, 12016, 11040, 10880]

private lemma M9_mul_mv0 : M9.mulVec mv0 = mv1 := by ext i; revert i; decide
private lemma M9_mul_mv1 : M9.mulVec mv1 = mv2 := by ext i; revert i; decide
private lemma M9_mul_mv2 : M9.mulVec mv2 = mv3 := by ext i; revert i; decide
private lemma M9_mul_mv3 : M9.mulVec mv3 = mv4 := by ext i; revert i; decide
private lemma M9_mul_mv4 : M9.mulVec mv4 = mv5 := by ext i; revert i; decide

private lemma M9_pow_col0_step (d : ℕ) : (fun i => (M9 ^ (d + 1)) i 0) = M9.mulVec (fun i => (M9 ^ d) i 0) := by
  ext i; rw [pow_succ', Matrix.mul_apply]; rfl

private lemma M9_col0_0 : (fun i => (1 : Matrix (Fin 9) (Fin 9) ℤ) i 0) = mv0 := by ext i; revert i; decide
private lemma M9_col0_1 : (fun i => M9 i 0) = mv1 := by ext i; revert i; decide
private lemma M9_col0_2 : (fun i => (M9 ^ 2) i 0) = mv2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, M9_pow_col0_step, pow_one, M9_col0_1, M9_mul_mv1]
private lemma M9_col0_3 : (fun i => (M9 ^ 3) i 0) = mv3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, M9_pow_col0_step, M9_col0_2, M9_mul_mv2]
private lemma M9_col0_4 : (fun i => (M9 ^ 4) i 0) = mv4 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, M9_pow_col0_step, M9_col0_3, M9_mul_mv3]
private lemma M9_col0_5 : (fun i => (M9 ^ 5) i 0) = mv5 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, M9_pow_col0_step, M9_col0_4, M9_mul_mv4]

private lemma M9_minpoly_col0 (i : Fin 9) :
    (M9 ^ 5) i 0 - 14 * (M9 ^ 4) i 0 - 40 * (M9 ^ 3) i 0 +
      560 * (M9 ^ 2) i 0 + 144 * M9 i 0 - 2016 * (1 : Matrix (Fin 9) (Fin 9) ℤ) i 0 = 0 := by
  rw [congrFun M9_col0_5 i, congrFun M9_col0_4 i, congrFun M9_col0_3 i,
      congrFun M9_col0_2 i, congrFun M9_col0_1 i, congrFun M9_col0_0 i]
  revert i; decide

private lemma A48_minpoly :
    A48 ^ 5 - (14 : ℝ) • A48 ^ 4 - (40 : ℝ) • A48 ^ 3 +
      (560 : ℝ) • A48 ^ 2 + (144 : ℝ) • A48 - (2016 : ℝ) • (1 : Matrix (Fin 48) (Fin 48) ℝ) = 0 := by
  have h0 := A48_pow_eq 0
  have h1 := A48_pow_eq 1
  have h2 := A48_pow_eq 2
  have h3 := A48_pow_eq 3
  have h4 := A48_pow_eq 4
  have h5 := A48_pow_eq 5
  simp only [pow_zero, pow_one] at h0 h1
  rw [h5, h4, h3, h2, h1, h0]
  ext x y
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.zero_apply, smul_eq_mul]
  have hcombine : ∀ (f5 f4 f3 f2 f1 f0 : Fin 9 → ℝ),
      (∑ i, f5 i) - 14 * (∑ i, f4 i) - 40 * (∑ i, f3 i) + 560 * (∑ i, f2 i) +
        144 * (∑ i, f1 i) - 2016 * (∑ i, f0 i) =
      ∑ i, (f5 i - 14 * f4 i - 40 * f3 i + 560 * f2 i + 144 * f1 i - 2016 * f0 i) := by
    intro f5 f4 f3 f2 f1 f0
    simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcombine]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hmi : ((M9 ^ 5) i 0 : ℝ) - 14 * ((M9 ^ 4) i 0 : ℝ) - 40 * ((M9 ^ 3) i 0 : ℝ) +
      560 * ((M9 ^ 2) i 0 : ℝ) + 144 * (M9 i 0 : ℝ) - 2016 * ((1 : Matrix (Fin 9) (Fin 9) ℤ) i 0 : ℝ) = 0 := by
    exact_mod_cast M9_minpoly_col0 i
  calc ((M9 ^ 5) i 0 : ℝ) * Rmat i x y - 14 * (((M9 ^ 4) i 0 : ℝ) * Rmat i x y) -
        40 * (((M9 ^ 3) i 0 : ℝ) * Rmat i x y) + 560 * (((M9 ^ 2) i 0 : ℝ) * Rmat i x y) +
        144 * ((M9 i 0 : ℝ) * Rmat i x y) - 2016 * (((1 : Matrix (Fin 9) (Fin 9) ℤ) i 0 : ℝ) * Rmat i x y)
      = (((M9 ^ 5) i 0 : ℝ) - 14 * ((M9 ^ 4) i 0 : ℝ) - 40 * ((M9 ^ 3) i 0 : ℝ) +
          560 * ((M9 ^ 2) i 0 : ℝ) + 144 * (M9 i 0 : ℝ) - 2016 * ((1 : Matrix (Fin 9) (Fin 9) ℤ) i 0 : ℝ)) *
          Rmat i x y := by ring
    _ = 0 * Rmat i x y := by rw [hmi]
    _ = 0 := zero_mul _

private lemma mulVec_pow_eig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (μ : ℝ)
    (h : A.mulVec v = μ • v) (d : ℕ) : (A ^ d).mulVec v = (μ ^ d) • v := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, mul_comm, ← pow_succ']

private lemma eigenvalue_mem_five {μ : ℝ} (hμ : μ ∈ @AdjacencyEigenvalues 48 G48 inferInstance) :
    μ ∈ ({14, 6, 2, -2, -6} : Finset ℝ) := by
  obtain ⟨v, hv, hmul⟩ := hμ
  change A48.mulVec v = μ • v at hmul
  have hsmul_mv : ∀ (c : ℝ) (M : Matrix (Fin 48) (Fin 48) ℝ), (c • M).mulVec v = c • M.mulVec v := by
    intro c M; ext k
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hp0 : (A48 ^ 5 - (14 : ℝ) • A48 ^ 4 - (40 : ℝ) • A48 ^ 3 +
      (560 : ℝ) • A48 ^ 2 + (144 : ℝ) • A48 - (2016 : ℝ) • (1 : Matrix (Fin 48) (Fin 48) ℝ)).mulVec v = 0 := by
    rw [A48_minpoly, Matrix.zero_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, hsmul_mv, Matrix.one_mulVec,
    mulVec_pow_eig A48 v μ hmul, hmul] at hp0
  have hsmul : (μ ^ 5 - 14 * μ ^ 4 - 40 * μ ^ 3 + 560 * μ ^ 2 + 144 * μ - 2016) • v = 0 := by
    ext i
    have hi := congrFun hp0 i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    linarith
  have hpoly : μ ^ 5 - 14 * μ ^ 4 - 40 * μ ^ 3 + 560 * μ ^ 2 + 144 * μ - 2016 = 0 := by
    rcases smul_eq_zero.mp hsmul with h | h
    · exact h
    · exact absurd h hv
  have hfac : (μ - 14) * (μ - 6) * (μ - 2) * (μ + 2) * (μ + 6) = 0 := by linarith [hpoly]
  simp only [mul_eq_zero] at hfac
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hfac with ((((h | h) | h) | h) | h)
  · left; linarith
  · right; left; linarith
  · right; right; left; linarith
  · right; right; right; left; linarith
  · right; right; right; right; linarith

/-! ### 6. Explicit integer eigenvectors for `14, 6, 2, -2, -6` -/

private lemma eig_of_intVec (vec : ℕ → ℤ) (lam : ℤ) (u0 : Fin 48) (hne : vec u0.val ≠ 0)
    (heq : (List.range 48).all (fun u =>
      ((List.range 48).map (fun v => if adjNat u v then vec v else 0)).sum == lam * vec u) = true) :
    (lam : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at heq
  refine ⟨fun u => (vec u.val : ℝ), ?_, ?_⟩
  · intro h
    have h0 := congrFun h u0
    simp only [Pi.zero_apply, Int.cast_eq_zero] at h0
    exact hne h0
  · ext u
    simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, G48_adjMatrix_ite,
      Pi.smul_apply, smul_eq_mul]
    have hsum : (∑ v : Fin 48, (if adjBool u v = true then (1 : ℝ) else 0) * (vec v.val : ℝ)) =
        (((List.range 48).map (fun v => if adjNat u.val v then vec v else 0)).sum : ℝ) := by
      have h1 : (∑ v : Fin 48, (if adjBool u v = true then (1 : ℝ) else 0) * (vec v.val : ℝ)) =
          ((∑ v : Fin 48, if adjNat u.val v.val then vec v.val else 0 : ℤ) : ℝ) := by
        push_cast
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [adjNat_eq u v]
        cases adjBool u v <;> simp
      rw [h1]
      congr 1
    rw [hsum, heq u.val u.isLt]
    push_cast
    rfl

private lemma eig_14 : (14 : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), ?_⟩
  ext u
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, G48_adjMatrix_ite,
    Pi.smul_apply, smul_eq_mul, mul_one]
  have hsum : (∑ v : Fin 48, if adjBool u v = true then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun v : Fin 48 => adjBool u v = true)).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : adjBool u v = true <;> simp [h]
  rw [hsum, deg_all u]
  norm_num

private def ev6 : ℕ → ℤ := fun u =>
  if om ((u % 16) / 4) (u % 4) == 0 then 1 else -1

private lemma eig_6 : (6 : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  simpa using eig_of_intVec ev6 6 0 (by decide) (by decide)

private lemma eig_of_sparse (supp : List (ℕ × ℤ)) (lam : ℤ) (u0 : Fin 48)
    (hnodup : (supp.map Prod.fst).Nodup)
    (hlt : ∀ p ∈ supp, p.1 < 48)
    (hne : ((supp.filter (fun p => p.1 == u0.val)).map Prod.snd).sum ≠ 0)
    (heq : (List.range 48).all (fun u =>
      ((supp.map (fun p => if adjNat u p.1 then p.2 else 0)).sum ==
        lam * ((supp.filter (fun p => p.1 == u)).map Prod.snd).sum)) = true) :
    (lam : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  let vec : ℕ → ℤ := fun u => ((supp.filter (fun p => p.1 == u)).map Prod.snd).sum
  refine eig_of_intVec vec lam u0 hne ?_
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at heq ⊢
  intro u hu
  rw [← heq u hu]
  have hsum : ∀ (l : List (ℕ × ℤ)), (l.map Prod.fst).Nodup → (∀ p ∈ l, p.1 < 48) →
      ((List.range 48).map (fun v => if adjNat u v then
        ((l.filter (fun p => p.1 == v)).map Prod.snd).sum else 0)).sum =
      (l.map (fun p => if adjNat u p.1 then p.2 else 0)).sum := by
    intro l
    induction l with
    | nil =>
      intro _ _
      simp
    | cons hd tl ih =>
      intro hnd hlt'
      have hhd_lt : hd.1 < 48 := hlt' hd (List.mem_cons_self ..)
      have htl_nd : (tl.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      have htl_lt : ∀ p ∈ tl, p.1 < 48 := fun p hp => hlt' p (List.mem_cons_of_mem _ hp)
      rw [List.map_cons, List.sum_cons, ← ih htl_nd htl_lt]
      have hsplit : ∀ v : ℕ,
          (if adjNat u v then (((hd :: tl).filter (fun p => p.1 == v)).map Prod.snd).sum else 0) =
          (if hd.1 = v then (if adjNat u hd.1 then hd.2 else 0) else 0) +
          (if adjNat u v then ((tl.filter (fun p => p.1 == v)).map Prod.snd).sum else 0) := by
        intro v
        by_cases he : hd.1 = v
        · subst he
          simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
          cases adjNat u hd.1 <;> simp
        · have hbf : (hd.1 == v) = false := beq_false_of_ne he
          simp only [List.filter_cons, hbf, Bool.false_eq_true, ↓reduceIte, he, zero_add]
      have hmap : ((List.range 48).map (fun v =>
          if adjNat u v then (((hd :: tl).filter (fun p => p.1 == v)).map Prod.snd).sum else 0)).sum =
          ((List.range 48).map (fun v => if hd.1 = v then (if adjNat u hd.1 then hd.2 else 0) else 0)).sum +
          ((List.range 48).map (fun v => if adjNat u v then
            ((tl.filter (fun p => p.1 == v)).map Prod.snd).sum else 0)).sum := by
        have hadd : ∀ (xs : List ℕ) (f g : ℕ → ℤ),
            (xs.map (fun v => f v + g v)).sum = (xs.map f).sum + (xs.map g).sum := by
          intro xs f g; induction xs with
          | nil => simp
          | cons a as iha => simp only [List.map_cons, List.sum_cons, iha]; ring
        rw [← hadd]
        congr 1
        exact List.map_congr_left (fun v _ => hsplit v)
      rw [hmap]
      congr 1
      have hone : ∀ (n k : ℕ) (c : ℤ), k < n →
          ((List.range n).map (fun v => if k = v then c else 0)).sum = c := by
        intro n k c hkn
        induction n with
        | zero => omega
        | succ n ihn =>
          rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
          by_cases hkn' : k = n
          · subst hkn'
            have hz : ((List.range k).map (fun v => if k = v then c else 0)).sum = 0 := by
              apply List.sum_eq_zero
              intro z hz
              rcases List.mem_map.mp hz with ⟨v, hv, rfl⟩
              have hvlt : v < k := List.mem_range.mp hv
              simp [show k ≠ v by omega]
            simp [hz]
          · simp [hkn', ihn (by omega)]
      exact hone 48 hd.1 _ hhd_lt
  exact hsum supp hnodup hlt

private def supp2 : List (ℕ × ℤ) :=
  [(1, -1), (2, -1), (3, -1), (4, 1), (8, 1), (12, 1)]

private def suppm2 : List (ℕ × ℤ) :=
  [(0, 1), (1, 1), (2, -1), (3, -1), (4, -1), (5, -1), (6, 1), (7, 1)]

private def suppm6 : List (ℕ × ℤ) :=
  [(10, 1), (11, -1), (14, -1), (15, 1), (16, -1), (17, 1),
   (20, 1), (21, -1), (32, 1), (33, -1), (36, -1), (37, 1)]

private lemma eig_2 : (2 : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  simpa using eig_of_sparse supp2 2 4 (by decide) (by decide) (by decide) (by decide)

private lemma eig_m2 : (-2 : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  simpa using eig_of_sparse suppm2 (-2) 0 (by decide) (by decide) (by decide) (by decide)

private lemma eig_m6 : (-6 : ℝ) ∈ @AdjacencyEigenvalues 48 G48 inferInstance := by
  simpa using eig_of_sparse suppm6 (-6) 10 (by decide) (by decide) (by decide) (by decide)

private lemma main_proof :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (inst : DecidableRel G.Adj),
      @IsNeumaierGraph n G inst ∧
      ∃ S : Finset ℝ, S.card = 5 ∧ (S : Set ℝ) = @AdjacencyEigenvalues n G inst := by
  refine ⟨48, G48, inferInstance, G48_isNeumaier, {14, 6, 2, -2, -6}, ?_, ?_⟩
  · have h1 : (14 : ℝ) ∉ ({6, 2, -2, -6} : Finset ℝ) := by norm_num
    have h2 : (6 : ℝ) ∉ ({2, -2, -6} : Finset ℝ) := by norm_num
    have h3 : (2 : ℝ) ∉ ({-2, -6} : Finset ℝ) := by norm_num
    have h4 : (-2 : ℝ) ∉ ({-6} : Finset ℝ) := by norm_num
    simp [Finset.card_insert_of_notMem, h1, h2, h3, h4]
  · ext μ
    simp only [Finset.mem_coe]
    constructor
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact eig_14
      · exact eig_6
      · exact eig_2
      · exact eig_m2
      · exact eig_m6
    · exact eigenvalue_mem_five

end OMA.P_arxiv_2603_17029

theorem OMA.solution : type_of% @OMA.S_arxiv_2603_17029.main :=
  OMA.P_arxiv_2603_17029.main_proof
