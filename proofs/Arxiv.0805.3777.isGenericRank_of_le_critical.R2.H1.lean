import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2
import Mathlib

-- Credit: @kumagi

/-!
The five-slice family has four base cases, certified by binary Jacobian minors
whose row elimination is checked by the kernel. In the induction step,
the expected rank increases by five when both long dimensions increase by two.
Old points indexed by a five-vertex multigraph and five new points span the
mixed and new coordinates. Nonvanishing of polynomial determinants combines
this witness with the old tangent-space witness.
-/

namespace FriedlandFiveSliceInduction

private def expectedRank (m : ℕ) : ℕ := 5 * m * (m + 1) ⌈/⌉ (5 + m + (m + 1) - 2)

private lemma ceil_eq_of_bounds {D N q : ℕ} (hD : 0 < D)
    (hlo : D * q < N) (hhi : N ≤ D * (q + 1)) : N ⌈/⌉ D = q + 1 := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hD).mpr hhi)
  by_contra! hn
  exact (not_lt_of_ge ((ceilDiv_le_iff_le_mul hD).mp (show N ⌈/⌉ D ≤ q by omega))) hlo

theorem expectedRank_odd (k : ℕ) : expectedRank (2 * (k + 2) + 1) = 5 * k + 11 := by
  unfold expectedRank
  rw [show 5 + (2 * (k + 2) + 1) + (2 * (k + 2) + 1 + 1) - 2 = 4 * k + 14 by omega,
    show 5 * k + 11 = (5 * k + 10) + 1 by omega]
  exact ceil_eq_of_bounds (by omega) (by nlinarith) (by nlinarith)

theorem expectedRank_even (k : ℕ) : expectedRank (2 * (k + 4)) = 5 * k + 18 := by
  unfold expectedRank
  rw [show 5 + 2 * (k + 4) + (2 * (k + 4) + 1) - 2 = 4 * k + 20 by omega,
    show 5 * k + 18 = (5 * k + 17) + 1 by omega]
  exact ceil_eq_of_bounds (by omega) (by nlinarith) (by nlinarith)

theorem expectedRank_add_two {m : ℕ} (hm : 7 ≤ m) :
    expectedRank (m + 2) = expectedRank m + 5 := by
  by_cases h : m % 2 = 0
  · let k := (m - 8) / 2
    have hk : m = 2 * (k + 4) := by dsimp [k]; omega
    rw [hk, show 2 * (k + 4) + 2 = 2 * ((k + 1) + 4) by omega,
      expectedRank_even, expectedRank_even]
    omega
  · let k := (m - 5) / 2
    have hk : m = 2 * (k + 2) + 1 := by dsimp [k]; omega
    rw [hk, show 2 * (k + 2) + 1 + 2 = 2 * ((k + 1) + 2) + 1 by omega,
      expectedRank_odd, expectedRank_odd]
    omega

private def Spans (m r : ℕ) : Prop :=
  ∃ x : Fin r → Fin 5 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m + 1) → ℂ,
    ∀ T : Fin 5 → Fin m → Fin (m + 1) → ℂ, ∃ u : Fin r → Fin 5 → ℂ,
      ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m + 1) → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (y t j * z t k) + x t i * (v t j * z t k) +
          x t i * (y t j * w t k))

/-- Four finite Jacobian rank tests. -/
def H1 : Prop :=
  Spans 5 11 ∧ Spans 6 14 ∧ Spans 7 16 ∧ Spans 8 18

/-- A width-two extension of the witness with five additional points. -/
def H2 : Prop :=
  ∀ m : ℕ, 7 ≤ m → Spans m (expectedRank m) → Spans (m + 2) (expectedRank m + 5)

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2.H1 := by
  intro hseed hstep m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    change Spans m (expectedRank m)
    by_cases hsmall : m ≤ 8
    · obtain ⟨h5, h6, h7, h8⟩ := hseed
      interval_cases m
      · exact h5
      · exact h6
      · exact h7
      · exact h8
    · have hprev : 7 ≤ m - 2 := by omega
      have hEq : m - 2 + 2 = m := by omega
      have hRank : expectedRank (m - 2) + 5 = expectedRank m := by
        rw [← expectedRank_add_two hprev, hEq]
      have hw : Spans (m - 2) (expectedRank (m - 2)) :=
        ih (m - 2) (by omega) (by omega)
      have hh := hstep (m - 2) hprev hw
      rw [hEq, hRank] at hh
      exact hh

end FriedlandFiveSliceInduction

namespace FriedlandFiveSlice

/-- A square minor of an integral matrix with nonzero determinant modulo a prime
gives a right inverse for its complex matrix. -/
theorem surjective_of_modular_minor {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {p : ℕ} [Fact (Nat.Prime p)] (A : Matrix ι κ ℤ) (select : ι → κ)
    (h : ((A.submatrix id select).map (Int.castRingHom (ZMod p))).det ≠ 0) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  classical
  let M := (A.submatrix id select).map (Int.castRingHom ℂ)
  have hInt : (A.submatrix id select).det ≠ 0 := by
    intro hz
    apply h
    change ((Int.castRingHom (ZMod p)).mapMatrix (A.submatrix id select)).det = 0
    rw [← RingHom.map_det, hz, map_zero]
  have hM : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    change ((Int.castRingHom ℂ).mapMatrix (A.submatrix id select)).det ≠ 0
    rw [← RingHom.map_det]
    intro hh
    change (((A.submatrix id select).det : ℤ) : ℂ) = 0 at hh
    exact hInt (by exact_mod_cast hh)
  let E : Matrix κ ι ℂ := fun j i => if j = select i then 1 else 0
  have hAM : A.map (Int.castRingHom ℂ) * E = M := by
    ext i j
    rw [Matrix.mul_apply]
    simp [E, M, mul_ite]
  intro b
  refine ⟨E.mulVec (M⁻¹.mulVec b), ?_⟩
  rw [Matrix.mulVec_mulVec, hAM, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM]
  simp

end FriedlandFiveSlice


namespace FriedlandBinarySeeds

private def bitValue {R : Type} [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

private lemma bitValue_and {R : Type} [Semiring R] (x y : Bool) :
    (bitValue (x && y) : R) = bitValue x * bitValue y := by
  cases x <;> cases y <;> simp [bitValue]

private lemma bitValue_ite {R : Type} [Zero R] [One R] (p : Prop) [Decidable p]
    (b : Bool) : (bitValue (if p then b else false) : R) = if p then bitValue b else 0 := by
  by_cases h : p <;> simp [h, bitValue]

private lemma bitValue_xor (x y : Bool) :
    (bitValue (Bool.xor x y) : ZMod 2) = bitValue x + bitValue y := by
  cases x <;> cases y <;> decide


private def pack : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => Nat.bit (f 0) (pack n (fun j => f j.succ))

private theorem pack_bit {n : ℕ} (f : Fin n → Bool) (j : Fin n) :
    (pack n f).testBit j.val = f j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [pack, Fin.val_zero, Nat.testBit_bit_zero]
    · rw [pack, Fin.val_succ, Nat.testBit_bit_succ, ih]

private def dotPacked : (n : ℕ) → ℕ → (Fin n → ZMod 2) → ZMod 2
  | 0, _, _ => 0
  | n + 1, a, v =>
    bitValue (a.testBit 0) * v 0 + dotPacked n (a >>> 1) (fun j => v j.succ)

private theorem dotPacked_eq_sum {n : ℕ} (a : ℕ) (v : Fin n → ZMod 2) :
    dotPacked n a v = ∑ j, bitValue (a.testBit j.val) * v j := by
  induction n generalizing a with
  | zero => simp [dotPacked]
  | succ n ih =>
    rw [dotPacked, Fin.sum_univ_succ, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.testBit_shiftRight, Fin.val_succ, Nat.add_comm]

private theorem dotPacked_xor {n : ℕ} (a b : ℕ) (v : Fin n → ZMod 2) :
    dotPacked n (a ^^^ b) v = dotPacked n a v + dotPacked n b v := by
  simp only [dotPacked_eq_sum, Nat.testBit_xor, bitValue_xor, add_mul, Finset.sum_add_distrib]

private def pivotRow : List ℕ → Option (ℕ × List ℕ)
  | [] => none
  | a :: rows =>
    if a.testBit 0 then some (a, rows)
    else (pivotRow rows).map fun (p, rest) => (p, a :: rest)

private lemma pivot_properties {rows : List ℕ} {p : ℕ} {rest : List ℕ}
    (h : pivotRow rows = some (p, rest)) :
    p.testBit 0 = true ∧ p ∈ rows ∧ ∀ a ∈ rest, a ∈ rows := by
  induction rows generalizing p rest with
  | nil => simp [pivotRow] at h
  | cons a rows ih =>
    by_cases ha : a.testBit 0 = true
    · simp [pivotRow, ha] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ha, .head _, fun b hb => .tail _ hb⟩
    · simp only [pivotRow, ha] at h
      cases hp : pivotRow rows with
      | none => simp [hp] at h
      | some data =>
        obtain ⟨q, tail⟩ := data
        simp [hp] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hq, hmem, htail⟩ := ih hp
        refine ⟨hq, .tail _ hmem, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact .head _
        · exact .tail _ (htail _ hb)

private def clearLowBit (p a : ℕ) : ℕ :=
  (if a.testBit 0 then a ^^^ p else a) >>> 1

private theorem clear_preserves_equation {n : ℕ} (p a : ℕ) (v : Fin (n + 1) → ZMod 2)
    (hp : p.testBit 0 = true) (h1 : dotPacked (n + 1) p v = 0)
    (h2 : dotPacked (n + 1) a v = 0) :
    dotPacked n (clearLowBit p a) (fun j => v j.succ) = 0 := by
  by_cases ha : a.testBit 0 = true
  · have h : dotPacked (n + 1) (a ^^^ p) v = 0 := by rw [dotPacked_xor, h1, h2, add_zero]
    simp only [dotPacked, Nat.testBit_xor, hp, ha, Bool.xor_self,
      bitValue, Bool.false_eq_true, if_false, zero_mul, zero_add] at h
    simpa only [clearLowBit, ha, if_true] using h
  · have hf : a.testBit 0 = false := Bool.eq_false_iff.mpr ha
    simp only [dotPacked, hf, bitValue, Bool.false_eq_true, if_false, zero_mul, zero_add] at h2
    simpa only [clearLowBit, hf, Bool.false_eq_true, if_false] using h2

private def elimination : ℕ → List ℕ → Bool
  | 0, _ => true
  | n + 1, rows =>
    match pivotRow rows with
    | none => false
    | some (p, rest) => elimination n (rest.map (clearLowBit p))

private theorem elimination_sound {n : ℕ} (rows : List ℕ) (v : Fin n → ZMod 2)
    (hc : elimination n rows = true) (hv : ∀ a ∈ rows, dotPacked n a v = 0) : v = 0 := by
  induction n generalizing rows with
  | zero =>
    funext j
    exact j.elim0
  | succ n ih =>
    cases hp : pivotRow rows with
    | none => simp [elimination, hp] at hc
    | some data =>
      obtain ⟨p, rest⟩ := data
      obtain ⟨hpBit, hpMem, hrest⟩ := pivot_properties hp
      have hc' : elimination n (rest.map (clearLowBit p)) = true := by
        simpa only [elimination, hp] using hc
      have tail0 := ih (rest.map (clearLowBit p)) (fun j => v j.succ) hc' (by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        exact clear_preserves_equation p a v hpBit (hv p hpMem) (hv a (hrest _ ha)))
      have hpDot := hv p hpMem
      rw [dotPacked, hpBit, tail0] at hpDot
      simp [bitValue, dotPacked_eq_sum] at hpDot
      funext j
      exact Fin.cases hpDot (fun k => congrFun tail0 k) j

private theorem det_nonzero_of_elimination {n : ℕ} (a : Fin n → Fin n → Bool)
    (hcert : elimination n (List.ofFn fun i => pack n (a i)) = true) :
    (Matrix.of (fun i j => (bitValue (a i j) : ZMod 2))).det ≠ 0 := by
  let A : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun i j => bitValue (a i j)
  apply isUnit_iff_ne_zero.mp
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  change Function.Injective (Matrix.mulVecLin A)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply elimination_sound _ v hcert
  intro k hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
  rw [dotPacked_eq_sum]
  simpa only [pack_bit, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, Matrix.of_apply, Pi.zero_apply]
    using congrFun hv i

-- Store sixteen fixed-width values in each natural number of the table.
private def tableEntry (width : ℕ) (chunks : List ℕ) (index : ℕ) : ℕ :=
  (chunks[index / 16]! >>> (width * (index % 16))) &&& (2 ^ width - 1)

private abbrev TensorIndex (m : ℕ) := (Fin 5 × Fin m) × Fin (m + 1)
private abbrev Column (m r : ℕ) := Fin r × (Fin 5 ⊕ (Fin m ⊕ Fin (m + 1)))

private def rowIndex (m : ℕ) : TensorIndex m ≃ Fin (5 * m * (m + 1)) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

private def pitch (m : ℕ) : ℕ := 5 + m + (m + 1)

private def colAt {m r : ℕ} (hr : 0 < r) (raw : ℕ) : Column m r :=
  let j := raw % pitch m
  ⟨⟨raw / pitch m % r, Nat.mod_lt _ hr⟩,
    if h : j < 5 then .inl ⟨j, h⟩
    else if h' : j < 5 + m then .inr (.inl ⟨j - 5, by omega⟩)
    else .inr (.inr ⟨j - (5 + m), by
      have hj := Nat.mod_lt raw (by unfold pitch; omega : 0 < pitch m)
      dsimp [j, pitch] at *
      omega⟩)⟩

private def factorBit (m : ℕ) (source t k : ℕ) : Bool :=
  source.testBit (t * pitch m + k)

private def jacBit {m r : ℕ} (source : ℕ) (row : TensorIndex m) (col : Column m r) : Bool :=
  let t := col.1.val
  let i := row.1.1
  let j := row.1.2
  let k := row.2
  match col.2 with
  | .inl c => if c = i then factorBit m source t (5 + j) && factorBit m source t (5 + m + k) else false
  | .inr (.inl c) => if c = j then factorBit m source t i && factorBit m source t (5 + m + k) else false
  | .inr (.inr c) => if c = k then factorBit m source t i && factorBit m source t (5 + j) else false

private def selected {m r : ℕ} (hr : 0 < r) (cols : Fin (5 * m * (m + 1)) → ℕ)
    (j : Fin (5 * m * (m + 1))) : Column m r :=
  colAt hr (cols j)

private def jacobian (m r source : ℕ) : Matrix (Fin (5 * m * (m + 1))) (Column m r) ℤ :=
  Matrix.of fun row col => bitValue (jacBit source ((rowIndex m).symm row) col)

private lemma dot_eq_tensor {m r : ℕ} (source : ℕ) (s : Column m r → ℂ)
    (i : Fin 5) (j : Fin m) (k : Fin (m + 1)) :
    ((jacobian m r source).map (Int.castRingHom ℂ)).mulVec s (rowIndex m ((i, j), k)) =
      ∑ t : Fin r, (s (t, .inl i) *
        (bitValue (factorBit m source t (5 + j)) * bitValue (factorBit m source t (5 + m + k))) +
        bitValue (factorBit m source t i) * (s (t, .inr (.inl j)) *
          bitValue (factorBit m source t (5 + m + k))) +
        bitValue (factorBit m source t i) *
          (bitValue (factorBit m source t (5 + j)) * s (t, .inr (.inr k)))) := by
  have hbit (b : Bool) : ((bitValue b : ℤ) : ℂ) = bitValue b := by
    cases b <;> simp [bitValue]
  simp only [Matrix.mulVec, dotProduct, jacobian, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom,
    Equiv.symm_apply_apply, hbit, Fintype.sum_prod_type, Fintype.sum_sum_type, jacBit]
  apply Finset.sum_congr rfl
  intro t _
  simp only [bitValue_ite, bitValue_and, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ac_rfl

def Spans (m r : ℕ) : Prop :=
    ∃ x : Fin r → Fin 5 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m+1) → ℂ,
      ∀ T : Fin 5 → Fin m → Fin (m+1) → ℂ, ∃ u : Fin r → Fin 5 → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

theorem seed_witness {m r : ℕ} (hr : 0 < r) (source : ℕ)
    (cols : Fin (5 * m * (m + 1)) → ℕ)
    (h : elimination (5 * m * (m + 1)) (List.ofFn fun i => pack (5 * m * (m + 1))
      (fun j => jacBit source ((rowIndex m).symm i) (selected hr cols j))) = true) :
    Spans m r := by
  let J := jacobian m r source
  let P := selected (m := m) hr cols
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hM : ((J.submatrix id P).map (Int.castRingHom (ZMod 2))).det ≠ 0 := by
    have he : (J.submatrix id P).map (Int.castRingHom (ZMod 2)) =
        Matrix.of (fun i j => bitValue (jacBit source ((rowIndex m).symm i) (P j))) := by
      ext i j
      change ((bitValue (jacBit source ((rowIndex m).symm i) (P j)) : ℤ) : ZMod 2) =
        bitValue (jacBit source ((rowIndex m).symm i) (P j))
      cases hbit : jacBit source ((rowIndex m).symm i) (P j) <;> simp [bitValue]
    rw [he]
    exact det_nonzero_of_elimination _ h
  have hRange := FriedlandFiveSlice.surjective_of_modular_minor J P hM
  refine ⟨fun t i => bitValue (factorBit m source t i),
    fun t j => bitValue (factorBit m source t (5 + j)),
    fun t k => bitValue (factorBit m source t (5 + m + k)), ?_⟩
  intro T
  obtain ⟨w, hw⟩ := hRange (fun v =>
    T ((rowIndex m).symm v).1.1 ((rowIndex m).symm v).1.2 ((rowIndex m).symm v).2)
  refine ⟨fun t i => w (t, .inl i), fun t j => w (t, .inr (.inl j)),
    fun t k => w (t, .inr (.inr k)), ?_⟩
  intro i j k
  have hc := congrFun hw (rowIndex m ((i, j), k))
  change ((jacobian m r source).map (Int.castRingHom ℂ)).mulVec w (rowIndex m ((i, j), k)) = _ at hc
  rw [dot_eq_tensor] at hc
  simpa only [Equiv.symm_apply_apply] using hc.symm


private def factors5 : ℕ := 58985757262743404556485100749327236424947689533194815
private def selected5 (k : Fin 150) : ℕ := tableEntry 10 [
  24285530594307950966011544559525809328113058816,
  50001103288102181863211668076496753948666907666,
  75716674619439016422737045696944809060092384292,
  101432245950774551641636339527952944573779598390,
  128576460132520422588054969017449256546538170441,
  154292031465186485144603202548933577488536268891,
  180007602796522020362263346233091049976225708141,
  207151816979597119304466891595492294909170418816,
  234294636003638614403186531356663419383360670866,
  193842983176673445] k.val

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem cert5 :
    elimination (5 * 5 * (5 + 1)) (List.ofFn fun i =>
      pack (5 * 5 * (5 + 1)) (fun j => jacBit factors5 ((rowIndex 5).symm i)
        (selected (r := 11) (by decide) selected5 j))) = true := by
  decide +kernel

theorem witness5 : Spans 5 11 := seed_witness (m := 5) (r := 11) (by decide) factors5 selected5 cert5

private def factors6 : ℕ := 6715851444442719590906302707960593931043368629587561714645285363337708174141
private def selected6 (k : Fin 210) : ℕ := tableEntry 10 [
  22856889105027082921006912607684273669136188416,
  48572460436362618138667056291841746155750837266,
  74288031767698153355089259936713838367466361892,
  100003603099033688572749403620871310854081010742,
  125719174430369223790409547305028783340695659592,
  151434745761704759008069690989186255827310308442,
  181436242923342893384623614268977866748792517740,
  208580459830008754376330971588076645384076788864,
  234296031162673517589776031146291973436071891091,
  260011602492679824811651258957545638862406195365,
  287155816677086750434609338211127343627807940791,
  314300030860163148721153997587237011332415040714,
  347156026128141610885969440694593272726145956061,
  252149] k.val

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem cert6 :
    elimination (5 * 6 * (6 + 1)) (List.ofFn fun i =>
      pack (5 * 6 * (6 + 1)) (fun j => jacBit factors6 ((rowIndex 6).symm i)
        (selected (r := 14) (by decide) selected6 j))) = true := by
  decide +kernel

theorem witness6 : Spans 6 14 := seed_witness (m := 6) (r := 14) (by decide) factors6 selected6 cert6

private def factors7 : ℕ := 922949162401687030309954235421728185033744979820740502288809818927896959633857691427393090308175
private def selected7 (k : Fin 280) : ℕ := tableEntry 10 [
  22856889105027081652118372340169491897533858816,
  48572460435032090799778966444516024699785858066,
  74286636608663250169738910292783026936732487715,
  98574960247292825506340768007489877286472177717,
  124290531578628360724000911690494428268479979590,
  150006102909963895940421905228955285133608445016,
  178578959944781157293376410326009415154863811690,
  204294531276116692511037764117732171493165628542,
  230010102607450928386832673865599061354969449616,
  254297031087046899879949414690921140677842734242,
  280012602418382433828719809181744216763680347316,
  305728173749717969046379952865901689250294996165,
  331442349922018602346340347134357751802878976215,
  357157921253354137564000490818515223188908255465,
  381446244891983712900602348532069153134626468091,
  407161816223319248118261282109815390274655106316,
  432877387554654782067032885526458079889081007390,
  373428168199593414411568] k.val

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem cert7 :
    elimination (5 * 7 * (7 + 1)) (List.ofFn fun i =>
      pack (5 * 7 * (7 + 1)) (fun j => jacBit factors7 ((rowIndex 7).symm i)
        (selected (r := 16) (by decide) selected7 j))) = true := by
  decide +kernel

theorem witness7 : Spans 7 16 := seed_witness (m := 7) (r := 16) (by decide) factors7 selected7 cert7

private def factors8 : ℕ := 101599676397516270018199090086002137671823260559081334334142468609058347414568747314833292741473718173938626825511908541
private def selected8 (k : Fin 360) : ℕ := tableEntry 10 [
  22856889105025783577903738633262359273451553792,
  48571065277327714952078766608625554450117838865,
  72859388915957290288680624323332404799857528867,
  98574960247292825505101617860640340160380195892,
  124289136419593457537411411900867000115675601990,
  148577460058221733530908885533587780319123170392,
  172864388537817705024025627539501480359407757417,
  198579959869153240241685771222504904340922298491,
  224295531200488774190456164532736359708273816716,
  248582459680083447609358271649997257903039478942,
  274298031011418982827017206408335115760479421616,
  298584959491013654977030774439826901405079374017,
  324300530822349190194690916942238704669182611667,
  350016102153683426069246677726154648130937918692,
  374303030633279397562363419732067221170729245942,
  400018601964613633436919179334238622410466403592,
  424305530444209604930035921340152322449676200217,
  450021101775545140147696063842564125714854228267,
  475736673106879376022251824626480069175534744892,
  501450849279181307396426852601843263252690451790,
  525739172917810881464138959941471176080220325216,
  551453349090111514764099354209927238631730563441,
  465606638497062240784771] k.val

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem cert8 :
    elimination (5 * 8 * (8 + 1)) (List.ofFn fun i =>
      pack (5 * 8 * (8 + 1)) (fun j => jacBit factors8 ((rowIndex 8).symm i)
        (selected (r := 18) (by decide) selected8 j))) = true := by
  decide +kernel

theorem witness8 : Spans 8 18 := seed_witness (m := 8) (r := 18) (by decide) factors8 selected8 cert8

end FriedlandBinarySeeds

theorem FriedlandBinarySeeds.seeds : FriedlandFiveSliceInduction.H1 :=
  ⟨FriedlandBinarySeeds.witness5, FriedlandBinarySeeds.witness6,
    FriedlandBinarySeeds.witness7, FriedlandBinarySeeds.witness8⟩

namespace FriedlandWidthTwo

open Matrix MvPolynomial

private theorem square_right_inverse {K ι κ : Type} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] (A : Matrix ι κ K)
    (h : Function.Surjective A.mulVec) :
    ∃ E : Matrix κ ι K, A * E = 1 := by
  choose v hv using fun i : ι => h (fun j => if j = i then 1 else 0)
  refine ⟨Matrix.of fun k i => v i k, ?_⟩
  ext i j
  have H := congrFun (hv j) i
  change ∑ k, A i k * v j k = (if i = j then 1 else 0) at H
  simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using H

private theorem surjective_of_product_det {K ι κ : Type} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] (A : Matrix ι κ K) (E : Matrix κ ι K)
    (h : (A * E).det ≠ 0) : Function.Surjective A.mulVec := by
  intro b
  refine ⟨E.mulVec ((A * E)⁻¹.mulVec b), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)]
  simp

/-- A finite family of polynomial matrices, each of which has full row rank
somewhere, has full row rank simultaneously at one common specialization. -/
theorem simultaneous_surjectivity {K σ τ : Type} [Field K] [Infinite K] [Fintype τ]
    {ι κ : τ → Type} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)] [∀ t, Fintype (κ t)]
    (A : ∀ t, Matrix (ι t) (κ t) (MvPolynomial σ K))
    (h : ∀ t, ∃ x : σ → K, Function.Surjective ((A t).map (MvPolynomial.eval x)).mulVec) :
    ∃ x : σ → K, ∀ t, Function.Surjective ((A t).map (MvPolynomial.eval x)).mulVec := by
  classical
  choose x hx using h
  choose E hE using fun t => square_right_inverse _ (hx t)
  let P (t : τ) : Matrix (ι t) (ι t) (MvPolynomial σ K) :=
    Matrix.of fun i j => ∑ k, A t i k * MvPolynomial.C (E t k j)
  let cert (t : τ) : MvPolynomial σ K := (P t).det
  have hCert (t : τ) (a : σ → K) :
      MvPolynomial.eval a (cert t) =
        (((A t).map (MvPolynomial.eval a)) * E t : Matrix (ι t) (ι t) K).det := by
    calc
      _ = ((MvPolynomial.eval a).mapMatrix (P t)).det := (MvPolynomial.eval a).map_det _
      _ = _ := by
        congr 1
        ext i j
        simp only [P, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
          map_sum, map_mul, MvPolynomial.eval_C]
  have hne (t : τ) : cert t ≠ 0 := by
    intro hz
    have he := hCert t (x t)
    rw [hz, map_zero, hE t, Matrix.det_one] at he
    exact zero_ne_one he
  have hprod : (∏ t, cert t) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hne t
  obtain ⟨a, ha⟩ : ∃ a : σ → K, MvPolynomial.eval a (∏ t, cert t) ≠ 0 := by
    by_contra! hall
    apply hprod
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero] using hall a
  refine ⟨a, fun t => surjective_of_product_det _ (E t) ?_⟩
  rw [← hCert]
  rw [map_prod] at ha
  exact Finset.prod_ne_zero_iff.mp ha t (Finset.mem_univ _)

end FriedlandWidthTwo


namespace FriedlandWidthTwo

open Matrix

private abbrev Row (b c : ℕ) := Fin 5 × Fin b × Fin c

private abbrev Direction (b c : ℕ) := Fin 5 ⊕ (Fin b ⊕ Fin c)

private abbrev Col (b c r : ℕ) := Fin r × Direction b c

private abbrev Variables (m r : ℕ) := Col m (m + 1) r ⊕ Col (m + 2) (m + 3) 5

private abbrev Outside (m : ℕ) :=
  {a : Row (m + 2) (m + 3) // ¬ (a.2.1.val < m ∧ a.2.2.val < m + 1)}

private def entryMatrix {R : Type} [Mul R] [Zero R] {b c r : ℕ}
    (p : Col b c r → R) : Matrix (Row b c) (Col b c r) R :=
  Matrix.of fun (i, j, k) (t, q) =>
    match q with
    | .inl i' =>
      if i' = i then p (t, .inr (.inl j)) * p (t, .inr (.inr k)) else 0
    | .inr (.inl j') =>
      if j' = j then p (t, .inl i) * p (t, .inr (.inr k)) else 0
    | .inr (.inr k') =>
      if k' = k then p (t, .inl i) * p (t, .inr (.inl j)) else 0

private theorem entryMatrix_map {R S : Type} [Semiring R] [Semiring S] (f : R →+* S)
    {b c r : ℕ} (p : Col b c r → R) :
    (entryMatrix p).map f = entryMatrix (fun j => f (p j)) := by
  ext a d
  rcases a with ⟨i, j, k⟩
  rcases d with ⟨t, q⟩
  rcases q with i' | (j' | k')
  all_goals simp [entryMatrix, apply_ite f]

private def splitCol {m r : ℕ} (j : Col (m + 2) (m + 3) (r + 5)) :
    Option (Variables m r) :=
  if h : j.1.val < r then
    let t : Fin r := ⟨j.1.val, h⟩
    match j.2 with
    | .inl i => some (Sum.inl (t, .inl i))
    | .inr (.inl i) =>
      if hi : i.val < m then some (Sum.inl (t, .inr (.inl ⟨i.val, hi⟩))) else none
    | .inr (.inr i) =>
      if hi : i.val < m + 1 then some (Sum.inl (t, .inr (.inr ⟨i.val, hi⟩))) else none
  else
    some (Sum.inr (⟨j.1.val - r, by have := j.1.isLt; omega⟩, j.2))

private def oldMatrix {R : Type} [Mul R] [Zero R] {m r : ℕ} (p : Variables m r → R) :
    Matrix (Row m (m + 1)) (Col m (m + 1) r) R :=
  entryMatrix (p ∘ Sum.inl)

private def enlarge {R : Type} [Zero R] {m r : ℕ} (p : Variables m r → R)
    (d : Col (m + 2) (m + 3) (r + 5)) : R :=
  (splitCol d).elim 0 p

private def allMatrix {R : Type} [Mul R] [Zero R] {m r : ℕ} (p : Variables m r → R) :
    Matrix (Row (m + 2) (m + 3)) (Col (m + 2) (m + 3) (r + 5)) R :=
  entryMatrix (enlarge p)

private def outsideMatrix {R : Type} [Mul R] [Zero R] {m r : ℕ} (p : Variables m r → R) :
    Matrix (Outside m) (Col (m + 2) (m + 3) (r + 5)) R :=
  (allMatrix p).submatrix Subtype.val id

private theorem outsideMatrix_map {R S : Type} [Semiring R] [Semiring S] (f : R →+* S)
    {m r : ℕ} (p : Variables m r → R) :
    (outsideMatrix p).map f = outsideMatrix (fun j => f (p j)) := by
  change ((entryMatrix (enlarge p)).submatrix _ _).map f = _
  rw [← Matrix.submatrix_map, entryMatrix_map]
  congr 3
  funext j
  unfold enlarge
  cases splitCol j <;> simp

private theorem oldMatrix_map {R S : Type} [Semiring R] [Semiring S] (f : R →+* S)
    {m r : ℕ} (p : Variables m r → R) :
    (oldMatrix p).map f = oldMatrix (fun j => f (p j)) :=
  entryMatrix_map f _

private def oldRow {m : ℕ} (a : Row m (m + 1)) : Row (m + 2) (m + 3) :=
  (a.1, Fin.castAdd 2 a.2.1, Fin.castAdd 2 a.2.2)

private def embedCol {m r : ℕ} (d : Col m (m + 1) r) : Col (m + 2) (m + 3) (r + 5) :=
  (Fin.castAdd 5 d.1, d.2.map id (Sum.map (Fin.castAdd 2) (Fin.castAdd 2)))

private theorem restrict_old {m r : ℕ} (p : Variables m r → ℂ) (a : Row m (m + 1))
    (d : Col m (m + 1) r) : allMatrix p (oldRow a) (embedCol d) = oldMatrix p a d := by
  rcases a with ⟨i, j, k⟩
  rcases d with ⟨t, q⟩
  have hk : k.val ≤ m := by omega
  rcases q with i' | (j' | k')
  all_goals simp [allMatrix, oldMatrix, entryMatrix, oldRow, embedCol, enlarge, splitCol,
    t.isLt, j.isLt, hk]

private theorem restrict_outside {m r : ℕ} (p : Variables m r → ℂ) (a : Outside m)
    (d : Col m (m + 1) r) : allMatrix p a.val (embedCol d) = 0 := by
  rcases a with ⟨⟨i, j, k⟩, ha⟩
  rcases d with ⟨t, q⟩
  rcases q with i' | (j' | k')
  · by_cases hj : j.val < m <;> by_cases hk : k.val ≤ m
    · exact (ha ⟨hj, Nat.lt_succ_of_le hk⟩).elim
    all_goals simp [allMatrix, entryMatrix, embedCol, enlarge, splitCol, t.isLt, hj, hk]
  · by_cases h : Fin.castAdd 2 j' = j
    · subst j
      have hk : ¬ k.val ≤ m := fun h => ha ⟨j'.isLt, Nat.lt_succ_of_le h⟩
      simp [allMatrix, entryMatrix, embedCol, enlarge, splitCol, t.isLt, hk]
    · simp [allMatrix, entryMatrix, embedCol, h]
  · by_cases h : Fin.castAdd 2 k' = k
    · subst k
      have hj : ¬ j.val < m := fun h => ha ⟨h, k'.isLt⟩
      simp [allMatrix, entryMatrix, embedCol, enlarge, splitCol, t.isLt, hj]
    · simp [allMatrix, entryMatrix, embedCol, h]

private theorem assemble {m r : ℕ} (p : Variables m r → ℂ)
    (hOld : Function.Surjective (oldMatrix p).mulVec)
    (hOutside : Function.Surjective (outsideMatrix p).mulVec) :
    Function.Surjective (allMatrix p).mulVec := by
  classical
  let J := allMatrix p
  let E : Matrix (Col (m + 2) (m + 3) (r + 5)) (Col m (m + 1) r) ℂ :=
    Matrix.of fun d c => if d = embedCol c then 1 else 0
  have hJE : J * E = J.submatrix id embedCol := by
    ext a d
    simp [J, E, Matrix.mul_apply, mul_ite]
  intro T
  obtain ⟨u, hu⟩ := hOutside (fun a => T a.val)
  let w := J.mulVec u
  obtain ⟨v, hv⟩ := hOld (fun a => T (oldRow a) - w (oldRow a))
  refine ⟨u + E.mulVec v, ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hJE]
  funext a
  change w a + (J.submatrix id embedCol).mulVec v a = T a
  by_cases ha : a.2.1.val < m ∧ a.2.2.val < m + 1
  · let a₀ : Row m (m + 1) := (a.1, ⟨a.2.1.val, ha.1⟩, ⟨a.2.2.val, ha.2⟩)
    have he : oldRow a₀ = a := by rcases a with ⟨i, j, k⟩; rfl
    have hRow : (J.submatrix id embedCol) a = oldMatrix p a₀ := by
      funext d
      simpa only [J, Matrix.submatrix_apply, id_eq, he] using restrict_old p a₀ d
    rw [Matrix.mulVec, hRow, ← Matrix.mulVec, congrFun hv a₀, he, add_sub_cancel]
  · let a₀ : Outside m := ⟨a, ha⟩
    have hRow : (J.submatrix id embedCol) a = 0 := by
      funext d
      exact restrict_outside p a₀ d
    have hAt : w a = T a := congrFun hu a₀
    rw [Matrix.mulVec, hRow, zero_dotProduct, add_zero, hAt]


private theorem combine_witnesses {m r : ℕ}
    (hOld : ∃ p : Variables m r → ℂ, Function.Surjective (oldMatrix p).mulVec)
    (hOutside : ∃ p : Variables m r → ℂ, Function.Surjective (outsideMatrix p).mulVec) :
    ∃ p : Variables m r → ℂ, Function.Surjective (allMatrix p).mulVec := by
  classical
  let ι (t : Bool) : Type := if t then Row m (m + 1) else Outside m
  let κ (t : Bool) : Type := if t then Col m (m + 1) r else Col (m + 2) (m + 3) (r + 5)
  let (t : Bool) : Fintype (ι t) := by cases t <;> dsimp [ι] <;> infer_instance
  let (t : Bool) : DecidableEq (ι t) := Classical.decEq _
  let (t : Bool) : Fintype (κ t) := by cases t <;> dsimp [κ] <;> infer_instance
  let A (t : Bool) : Matrix (ι t) (κ t) (MvPolynomial (Variables m r) ℂ) :=
    match t with
    | true => oldMatrix MvPolynomial.X
    | false => outsideMatrix MvPolynomial.X
  have hNonempty (t : Bool) : ∃ p : Variables m r → ℂ,
      Function.Surjective ((A t).map (MvPolynomial.eval p)).mulVec := by
    cases t
    · change ∃ p : Variables m r → ℂ,
        Function.Surjective ((outsideMatrix MvPolynomial.X).map (MvPolynomial.eval p)).mulVec
      simpa only [outsideMatrix_map, MvPolynomial.eval_X] using hOutside
    · change ∃ p : Variables m r → ℂ,
        Function.Surjective ((oldMatrix MvPolynomial.X).map (MvPolynomial.eval p)).mulVec
      simpa only [oldMatrix_map, MvPolynomial.eval_X] using hOld
  obtain ⟨p, hp⟩ := simultaneous_surjectivity A hNonempty
  have hOld' := hp true
  have hOutside' := hp false
  change Function.Surjective ((oldMatrix MvPolynomial.X).map (MvPolynomial.eval p)).mulVec at hOld'
  change Function.Surjective ((outsideMatrix MvPolynomial.X).map (MvPolynomial.eval p)).mulVec at hOutside'
  simp only [oldMatrix_map, MvPolynomial.eval_X] at hOld'
  simp only [outsideMatrix_map, MvPolynomial.eval_X] at hOutside'
  exact ⟨p, assemble p hOld' hOutside'⟩

private def Spans (m r : ℕ) : Prop :=
  ∃ x : Fin r → Fin 5 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m+1) → ℂ,
    ∀ T : Fin 5 → Fin m → Fin (m+1) → ℂ, ∃ u : Fin r → Fin 5 → ℂ,
      ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m+1) → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

private def fromThree {b c r : ℕ} (x : Fin r → Fin 5 → ℂ) (y : Fin r → Fin b → ℂ)
    (z : Fin r → Fin c → ℂ) : Col b c r → ℂ
  | (t, .inl i) => x t i
  | (t, .inr (.inl j)) => y t j
  | (t, .inr (.inr k)) => z t k

private theorem entry_mulVec {b c r : ℕ} (p u : Col b c r → ℂ)
    (i : Fin 5) (j : Fin b) (k : Fin c) :
    (entryMatrix p).mulVec u (i, j, k) =
      ∑ t, (u (t, .inl i) * (p (t, .inr (.inl j)) * p (t, .inr (.inr k))) +
      p (t, .inl i) * (u (t, .inr (.inl j)) * p (t, .inr (.inr k))) +
      p (t, .inl i) * (p (t, .inr (.inl j)) * u (t, .inr (.inr k)))) := by
  simp only [Matrix.mulVec, dotProduct, entryMatrix, Matrix.of_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ac_rfl

private theorem old_of_spans {m r : ℕ} (h : Spans m r) :
    ∃ p : Variables m r → ℂ, Function.Surjective (oldMatrix p).mulVec := by
  obtain ⟨x, y, z, hs⟩ := h
  refine ⟨Sum.elim (fromThree x y z) (fun _ => 0), ?_⟩
  intro T
  obtain ⟨u, v, w, hw⟩ := hs (fun i j k => T (i, j, k))
  refine ⟨fromThree u v w, ?_⟩
  funext a
  rcases a with ⟨i, j, k⟩
  change (entryMatrix (fromThree x y z)).mulVec (fromThree u v w) (i, j, k) = T (i, j, k)
  rw [entry_mulVec]
  exact (hw i j k).symm

private theorem spans_of_entryMatrix {m r : ℕ} {p : Col m (m + 1) r → ℂ}
    (h : Function.Surjective (entryMatrix p).mulVec) : Spans m r := by
  refine ⟨fun t i => p (t, .inl i), fun t j => p (t, .inr (.inl j)),
    fun t k => p (t, .inr (.inr k)), ?_⟩
  intro T
  obtain ⟨u, hu⟩ := h fun a => T a.1 a.2.1 a.2.2
  refine ⟨fun t i => u (t, .inl i), fun t j => u (t, .inr (.inl j)),
    fun t k => u (t, .inr (.inr k)), ?_⟩
  intro i j k
  have he := congrFun hu (i, j, k)
  rw [entry_mulVec] at he
  exact he.symm

/-- The two-degree extension follows from a witness for the mixed and new rows. -/
theorem spans_add_two_of_outside_witness {m r : ℕ}
    (hOutside : ∃ p : Variables m r → ℂ, Function.Surjective (outsideMatrix p).mulVec)
    (h : Spans m r) : Spans (m + 2) (r + 5) := by
  obtain ⟨p, hp⟩ := combine_witnesses (old_of_spans h) hOutside
  exact spans_of_entryMatrix hp

end FriedlandWidthTwo


/- Vandermonde calculations for the explicit width-two tangent construction. -/

namespace FriedlandWidthTwo

open Matrix

private def scalar (i : Fin 5) : ℂ := (i.val : ℂ)

private theorem scalar_injective : Function.Injective scalar := by
  intro i j h
  apply Fin.ext
  unfold scalar at h
  exact_mod_cast h

/-- The four off-diagonal new-point directions distinguish the two last
coordinates in the old third factor and the last coordinate in the old
second factor, together with the remaining new-new component. -/
theorem new_directions_independent (i : Fin 5) {x y z w : ℂ}
    (h : ∀ t : Fin 5, t ≠ i →
      (scalar t - scalar i) * ((scalar t ^ 2 - scalar i ^ 2) * x +
        (scalar t ^ 3 - scalar i ^ 3) * y + (scalar t ^ 4 - scalar i ^ 4) * z) +
        (scalar t - scalar i)^2 * w = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  let a := scalar i
  let f : Fin 4 → ℂ := scalar ∘ i.succAbove
  let v : Fin 4 → ℂ := ![w + a * x + a ^ 2 * y + a ^ 3 * z,
    x + a * y + a ^ 2 * z, y + a * z, z]
  have hf : Function.Injective f := scalar_injective.comp Fin.succAbove_right_injective
  have he (j : Fin 4) : (∑ k : Fin 4, f j ^ k.val * v k) = 0 := by
    have h' := h (i.succAbove j) (Fin.succAbove_ne _ _)
    have hd : f j - a ≠ 0 := sub_ne_zero.mpr
      (fun hh => Fin.succAbove_ne i j (scalar_injective hh))
    have hh : (f j - a)^2 * (∑ k : Fin 4, f j ^ k.val * v k) = 0 := by
      change (f j - a) * ((f j ^ 2 - a ^ 2) * x +
          (f j ^ 3 - a ^ 3) * y + (f j ^ 4 - a ^ 4) * z) +
          (f j - a)^2 * w = 0 at h'
      simp only [v, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.val_zero, Fin.val_succ, pow_zero, one_mul, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      linear_combination h'
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 hd)
  have hv : v = 0 := Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hf he
  have h3 := congrFun hv (3 : Fin 4)
  have h2 := congrFun hv (2 : Fin 4)
  have h1 := congrFun hv (1 : Fin 4)
  have h0 := congrFun hv (0 : Fin 4)
  simp [v] at h3
  simp [v, h3] at h2
  simp [v, h2, h3] at h1
  simp [v, h1, h2, h3] at h0
  exact ⟨h1, h2, h3, h0⟩

private noncomputable def unit {n : ℕ} (j : Fin n) : Fin n → ℂ := Pi.single j 1

private lemma eval_sum_units {n : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] ℂ) (v : Fin n → ℂ) :
    φ v = ∑ j, v j * φ (unit j) := by
  have he : (∑ j, v j • unit j) = v := by
    ext i
    simp [unit, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hφ := congrArg φ he
  simpa only [map_sum, map_smul, smul_eq_mul] using hφ.symm

/-- Moment vectors on d distinct scalars, together with the standard basis
vectors in the final n-d coordinates, span the whole coordinate space. -/
theorem moments_and_tail {d n : ℕ} (h : d ≤ n)
    {f : Fin d → ℂ} (hf : Function.Injective f)
    {φ : (Fin n → ℂ) →ₗ[ℂ] ℂ}
    (hMoments : ∀ t : Fin d, φ (fun j => f t ^ j.val) = 0)
    (hTail : ∀ j : Fin n, d ≤ j.val → φ (unit j) = 0) :
    φ = 0 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  let v : Fin d → ℂ := fun j => φ (unit (Fin.castAdd e j))
  have he (t : Fin d) : (∑ j, f t ^ j.val * v j) = 0 := by
    have hM := hMoments t
    rw [eval_sum_units, Fin.sum_univ_add] at hM
    have hlast : (∑ j : Fin e, f t ^ (Fin.natAdd d j).val * φ (unit (Fin.natAdd d j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hTail _ (by simp), mul_zero]
    rw [hlast, add_zero] at hM
    exact hM
  have hv := Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hf he
  apply LinearMap.ext
  intro w
  change φ w = 0
  rw [eval_sum_units, Fin.sum_univ_add]
  have hfirst : (∑ j : Fin d, w (Fin.castAdd e j) * φ (unit (Fin.castAdd e j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [show φ (unit (Fin.castAdd e j)) = 0 from congrFun hv j, mul_zero]
  have hlast : (∑ j : Fin e, w (Fin.natAdd d j) * φ (unit (Fin.natAdd d j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hTail _ (by simp), mul_zero]
  change (∑ j : Fin d, w (Fin.castAdd e j) * φ (unit (Fin.castAdd e j))) +
    (∑ j : Fin e, w (Fin.natAdd d j) * φ (unit (Fin.natAdd d j))) = 0
  rw [hfirst, hlast, add_zero]

end FriedlandWidthTwo


namespace FriedlandWidthTwo

private abbrev Vec (n : ℕ) := Fin n → ℂ

private def extendVec {n : ℕ} (v : Vec n) (s t : ℂ) : Vec (n + 2) := fun j =>
  if h : j.val < n then v ⟨j.val, h⟩ else if j.val = n then s else t

@[simp] private lemma extendVec_zero {n : ℕ} :
    extendVec (0 : Vec n) 0 0 = 0 := by
  funext j
  simp [extendVec]

private lemma extendVec_add {n : ℕ} (v w : Vec n) (s t a b : ℂ) :
    extendVec (v + w) (s + a) (t + b) = extendVec v s t + extendVec w a b := by
  funext j
  by_cases h : j.val < n <;> by_cases hj : j.val = n <;> simp [extendVec, h, hj]

private lemma extendVec_smul {n : ℕ} (a : ℂ) (v : Vec n) (s t : ℂ) :
    extendVec (a • v) (a * s) (a * t) = a • extendVec v s t := by
  funext j
  simp only [extendVec, Pi.smul_apply, smul_eq_mul]
  split <;> simp_all

private lemma extendVec_sub {n : ℕ} (v w : Vec n) (s t a b : ℂ) :
    extendVec (v - w) (s - a) (t - b) = extendVec v s t - extendVec w a b := by
  funext j
  by_cases h : j.val < n <;> by_cases hj : j.val = n <;> simp [extendVec, h, hj]

private lemma extendVec_all {n : ℕ} (v : Vec (n + 2)) :
    v = extendVec (fun i => v (Fin.castAdd 2 i)) (v ⟨n, by omega⟩) (v ⟨n + 1, by omega⟩) := by
  funext j
  unfold extendVec
  split
  · rfl
  · split
    · rename_i hj
      exact congrArg v (Fin.ext hj)
    · have hj : j.val = n + 1 := by omega
      exact congrArg v (Fin.ext hj)

private def tensorOutside {m : ℕ} (a : Vec 5) (b : Vec (m + 2)) (c : Vec (m + 3)) :
    Outside m → ℂ := fun i => a i.val.1 * (b i.val.2.1 * c i.val.2.2)

private noncomputable def contraction {m : ℕ} (φ : (Outside m → ℂ) →ₗ[ℂ] ℂ) (i : Fin 5) :
    Vec (m + 2) →ₗ[ℂ] Vec (m + 3) →ₗ[ℂ] ℂ where
  toFun b :=
    { toFun := fun c => φ (tensorOutside (unit i) b c)
      map_add' := by
        intro c d
        rw [← map_add]
        congr 1
        funext j
        simp only [tensorOutside, Pi.add_apply]
        ring
      map_smul' := by
        intro a c
        rw [← map_smul]
        congr 1
        funext j
        simp only [tensorOutside, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro b c
    apply LinearMap.ext
    intro d
    change φ _ = φ _ + φ _
    rw [← map_add]
    congr 1
    funext j
    simp only [tensorOutside, Pi.add_apply]
    ring
  map_smul' := by
    intro a b
    apply LinearMap.ext
    intro c
    change φ _ = a • φ _
    rw [← map_smul]
    congr 1
    funext j
    simp only [tensorOutside, Pi.smul_apply, smul_eq_mul]
    ring

private lemma contraction_def {m : ℕ} (φ : (Outside m → ℂ) →ₗ[ℂ] ℂ) (i : Fin 5)
    (b : Vec (m + 2)) (c : Vec (m + 3)) :
    contraction φ i b c = φ (tensorOutside (unit i) b c) :=
  rfl

private lemma contraction_old {m : ℕ} (φ : (Outside m → ℂ) →ₗ[ℂ] ℂ) (i : Fin 5)
    (b : Vec m) (c : Vec (m + 1)) :
    contraction φ i (extendVec b 0 0) (extendVec c 0 0) = 0 := by
  rw [contraction_def, ← map_zero φ]
  congr 1
  funext a
  have ha := a.property
  by_cases h : a.val.2.1.val < m
  · have hc : ¬ a.val.2.2.val < m + 1 := fun hc => ha ⟨h, hc⟩
    simp [tensorOutside, extendVec, h, hc]
  · simp [tensorOutside, extendVec, h]

private lemma directions_annihilated {m r : ℕ} (p : Variables m r → ℂ)
    (φ : (Outside m → ℂ) →ₗ[ℂ] ℂ)
    (hφ : ∀ u, φ ((outsideMatrix p).mulVec u) = 0) (t : Fin (r + 5))
    (a : Vec 5) (b : Vec (m + 2)) (c : Vec (m + 3)) :
    let data := enlarge p
    let x := fun i => data (t, .inl i)
    let y := fun j => data (t, .inr (.inl j))
    let z := fun k => data (t, .inr (.inr k))
    φ (tensorOutside a y z) = 0 ∧ φ (tensorOutside x b z) = 0 ∧
      φ (tensorOutside x y c) = 0 := by
  let data := enlarge p
  let x := fun i => data (t, .inl i)
  let y := fun j => data (t, .inr (.inl j))
  let z := fun k => data (t, .inr (.inr k))
  let changeAt (u : Vec 5) (v : Vec (m + 2)) (w : Vec (m + 3)) :
      Col (m + 2) (m + 3) (r + 5) → ℂ := fun d =>
    if d.1 = t then fromThree (fun _ => u) (fun _ => v) (fun _ => w) d else 0
  have eqDir (u : Vec 5) (v : Vec (m + 2)) (w : Vec (m + 3)) :
      (outsideMatrix p).mulVec (changeAt u v w) =
        tensorOutside u y z + tensorOutside x v z + tensorOutside x y w := by
    funext row
    rcases row with ⟨⟨i, j, k⟩, hrow⟩
    change (entryMatrix data).mulVec (changeAt u v w) (i, j, k) = _
    rw [entry_mulVec]
    rw [Finset.sum_eq_single t]
    · simp [changeAt, fromThree, tensorOutside, x, y, z]
    · intro j hj hne
      simp [changeAt, hne]
    · simp
  have ha := hφ (changeAt a 0 0)
  have hb := hφ (changeAt 0 b 0)
  have hc := hφ (changeAt 0 0 c)
  rw [eqDir] at ha hb hc
  have hfirst (b : Vec (m + 2)) (c : Vec (m + 3)) : tensorOutside 0 b c = 0 := by
    funext i
    simp [tensorOutside]
  have hsecond (a : Vec 5) (c : Vec (m + 3)) : tensorOutside a 0 c = 0 := by
    funext i
    simp [tensorOutside]
  have hthird (a : Vec 5) (b : Vec (m + 2)) : tensorOutside a b 0 = 0 := by
    funext i
    simp [tensorOutside]
  exact ⟨by simpa only [hsecond, hthird, add_zero] using ha,
    by simpa only [hfirst, hthird, zero_add, add_zero] using hb,
    by simpa only [hfirst, hsecond, zero_add] using hc⟩

private theorem contraction_ext {m : ℕ} {φ : (Outside m → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ i, contraction φ i = 0) : φ = 0 := by
  apply LinearMap.ext
  intro f
  have hDecomp : f = ∑ w : Outside m, f w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [hDecomp, map_sum, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro w _
  rw [map_smul]
  have heq : tensorOutside (unit w.val.1) (unit w.val.2.1) (unit w.val.2.2) =
      Pi.single w (1 : ℂ) := by
    funext u
    by_cases hu : u = w
    · subst u
      simp [tensorOutside, unit]
    · have hne : u.val ≠ w.val := fun h => hu (Subtype.ext h)
      have h' : u.val.1 ≠ w.val.1 ∨ u.val.2.1 ≠ w.val.2.1 ∨ u.val.2.2 ≠ w.val.2.2 := by
        by_contra! hh
        exact hne (Prod.ext hh.1 (Prod.ext hh.2.1 hh.2.2))
      rcases h' with h' | h' | h'
      all_goals simp [tensorOutside, unit, Pi.single_eq_of_ne, hu, h']
  rw [← heq, ← contraction_def, h, LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]

end FriedlandWidthTwo

namespace FriedlandWidthTwo

private def oldEmbed {n : ℕ} : Vec n →ₗ[ℂ] Vec (n + 2) where
  toFun v := extendVec v 0 0
  map_add' v w := by simpa only [add_zero] using extendVec_add v w 0 0 0 0
  map_smul' a v := by simpa only [RingHom.id_apply, mul_zero] using extendVec_smul a v 0 0

private def lastNew (n : ℕ) : Vec (n + 2) := extendVec (0 : Vec n) 0 1

private lemma extendVec_decomp {n : ℕ} (α b : Vec n) (x s t : ℂ) :
    extendVec b s t =
      s • extendVec α 1 x + (oldEmbed (b - s • α) + (t - x * s) • lastNew n) := by
  rw [← extendVec_smul, mul_one]
  change _ = _ + (extendVec _ 0 0 + (t - x * s) • extendVec (0 : Vec n) 0 1)
  rw [← extendVec_smul, smul_zero, mul_zero, mul_one, ← extendVec_add, add_zero, add_zero,
    zero_add, ← extendVec_add, add_zero, add_sub_cancel]
  congr 1
  ring

private lemma slice_formula {m : ℕ} (φ : (Outside m → ℂ) →ₗ[ℂ] ℂ) (i : Fin 5)
    (α : Vec m) (β : Vec (m + 1)) (x : ℂ)
    (hB : ∀ c, contraction φ i (extendVec α 1 x) c = 0)
    (hC : ∀ b, contraction φ i b (extendVec β 1 x) = 0)
    (b : Vec m) (c : Vec (m + 1)) (s t u v : ℂ) :
    let L := contraction φ i
    let F := (L.flip (lastNew (m + 1))).comp oldEmbed
    let G := (L (lastNew m)).comp oldEmbed
    L (extendVec b s t) (extendVec c u v) =
       (v - x * u) * F (b - s • α) + (t - x * s) * G (c - u • β) +
         (t - x * s) * (v - x * u) * L (lastNew m) (lastNew (m + 1)) := by
  let L := contraction φ i
  change L _ _ = _
  rw [extendVec_decomp α b x s t, extendVec_decomp β c x u v]
  simp only [L, LinearMap.map_add, LinearMap.map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.comp_apply, hB, hC,
    smul_eq_mul, mul_zero, add_zero, zero_add]
  have hz : contraction φ i (oldEmbed (b - s • α)) (oldEmbed (c - u • β)) = 0 :=
    contraction_old φ i _ _
  rw [hz]
  ring

private lemma edge_two_equations {a b F G : ℂ} (h : a ≠ b)
    (h₁ : F + G = 0) (h₂ : -a * F + -b * G = 0) : F = 0 ∧ G = 0 := by
  have he : (a - b) * F = 0 := by linear_combination -h₂ - b * h₁
  have hz := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h)
  exact ⟨hz, by simpa only [hz, zero_add] using h₁⟩

private lemma surj_of_no_annihilator {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (f : A →ₗ[ℂ] B)
    (h : ∀ φ : B →ₗ[ℂ] ℂ, (∀ x, φ (f x) = 0) → φ = 0) :
    Function.Surjective f := by
  apply LinearMap.dualMap_injective_iff.mp
  intro φ ψ he
  apply sub_eq_zero.mp
  apply h
  intro x
  exact sub_eq_zero.mpr (LinearMap.congr_fun he x)

end FriedlandWidthTwo

/- The old tangent points in the width-two construction correspond to edges
of a five-vertex multigraph of degree m or m - 1. -/

namespace FriedlandWidthTwo

open FriedlandFiveSliceInduction

private abbrev Edge := Fin 5 × Fin 5

private def cycle : List Edge := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
private def oddExtra : List Edge := [(0, 1)]
private def evenExtra : List Edge := [(0, 1), (0, 2), (3, 4)]

private def repeatCycle : ℕ → List Edge
  | 0 => []
  | n + 1 => cycle ++ repeatCycle n

private def degree (g : List Edge) (i : Fin 5) : ℕ :=
  (g.filter fun e => decide (i = e.1 ∨ i = e.2)).length

private lemma degree_append (g h : List Edge) (i : Fin 5) :
    degree (g ++ h) i = degree g i + degree h i := by
  simp [degree]

private lemma degree_cycle (i : Fin 5) : degree cycle i = 2 := by
  fin_cases i <;> decide

private lemma degree_repeatCycle (n : ℕ) (i : Fin 5) :
    degree (repeatCycle n) i = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeatCycle, degree_append, degree_cycle, ih]
    omega

private lemma length_repeatCycle (n : ℕ) : (repeatCycle n).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [repeatCycle, ih, cycle]
    omega

private lemma repeatCycle_ne (n : ℕ) : ∀ e ∈ repeatCycle n, e.1 ≠ e.2 := by
  induction n with
  | zero => simp [repeatCycle]
  | succ n ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · have hCycle : ∀ e ∈ cycle, e.1 ≠ e.2 := by decide
      exact hCycle e he
    · exact ih e he

private lemma oddExtra_degree (i : Fin 5) : degree oddExtra i = 0 ∨ degree oddExtra i = 1 := by
  fin_cases i <;> decide

private lemma evenExtra_degree (i : Fin 5) : degree evenExtra i = 1 ∨ degree evenExtra i = 2 := by
  fin_cases i <;> decide

/-- An edge list of the required length and degrees. The rank parameter is
written as the same ceiling expression as in the associated reduction. -/
theorem edges_for_extension (m : ℕ) (hm : 7 ≤ m) :
    ∃ g : List Edge,
      g.length = 5 * m * (m + 1) ⌈/⌉ (5 + m + (m + 1) - 2) ∧
      (∀ e ∈ g, e.1 ≠ e.2) ∧ ∀ i, degree g i = m - 1 ∨ degree g i = m := by
  by_cases h : m % 2 = 0
  · let k := (m - 8) / 2
    have hk : m = 2 * (k + 4) := by dsimp [k]; omega
    refine ⟨repeatCycle (k + 3) ++ evenExtra, ?_, ?_, ?_⟩
    · rw [hk]
      have hr := expectedRank_even k
      change 5 * (2 * (k + 4)) * (2 * (k + 4) + 1) ⌈/⌉
        (5 + 2 * (k + 4) + (2 * (k + 4) + 1) - 2) = _ at hr
      rw [hr]
      simp [length_repeatCycle, evenExtra]
      omega
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact repeatCycle_ne _ e he
      · exact (by decide : ∀ e ∈ evenExtra, e.1 ≠ e.2) e he
    · intro i
      rw [degree_append, degree_repeatCycle]
      rcases evenExtra_degree i with h' | h' <;> rw [h'] <;> omega
  · let k := (m - 7) / 2
    have hk : m = 2 * (k + 3) + 1 := by dsimp [k]; omega
    refine ⟨repeatCycle (k + 3) ++ oddExtra, ?_, ?_, ?_⟩
    · rw [hk]
      have hr := expectedRank_odd (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega] at hr
      change 5 * (2 * (k + 3) + 1) * (2 * (k + 3) + 1 + 1) ⌈/⌉
        (5 + (2 * (k + 3) + 1) + (2 * (k + 3) + 1 + 1) - 2) = _ at hr
      rw [hr]
      simp [length_repeatCycle, oddExtra]
      omega
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact repeatCycle_ne _ e he
      · exact (by decide : ∀ e ∈ oddExtra, e.1 ≠ e.2) e he
    · intro i
      rw [degree_append, degree_repeatCycle]
      rcases oddExtra_degree i with h' | h' <;> rw [h'] <;> omega

end FriedlandWidthTwo


namespace FriedlandWidthTwo

private lemma card_incident (g : List Edge) (i : Fin 5) :
    Fintype.card {t : Fin g.length // i = (g.get t).1 ∨ i = (g.get t).2} = degree g i := by
  rw [Fintype.card_subtype]
  induction g with
  | nil => simp [degree]
  | cons e g ih =>
    let P (x : Fin (g.length + 1)) := i = ((e :: g).get x).1 ∨ i = ((e :: g).get x).2
    change (Finset.univ.filter P).card = degree (e :: g) i
    rw [Fin.card_filter_univ_succ' P]
    dsimp only [P]
    have he : (e :: g).get 0 = e := rfl
    have ht (t : Fin g.length) : (e :: g).get t.succ = g.get t := rfl
    simp only [he, ht]
    rw [ih]
    by_cases h : i = e.1 ∨ i = e.2 <;> simp [degree, h, Nat.add_comm]

private def moment (n t : ℕ) : Vec n := fun i => (t : ℂ) ^ i.val

private def penultimate {m : ℕ} (hm : 0 < m) : Fin (m + 1) := ⟨m - 1, by omega⟩

private def finalOld {m : ℕ} (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

private noncomputable def newOldLeft {m : ℕ} (hm : 0 < m) (i : Fin 5) : Vec m :=
  scalar i ^ 2 • unit (finalOld hm)

private noncomputable def newOldRight {m : ℕ} (hm : 0 < m) (i : Fin 5) : Vec (m + 1) :=
  scalar i ^ 3 • unit (penultimate hm) + scalar i ^ 4 • unit (Fin.last m)

private noncomputable def pointVariables {m : ℕ} (hm : 0 < m) (g : List Edge) :
    Variables m g.length → ℂ :=
  Sum.elim
    (fromThree (fun t => unit (g.get t).1 + unit (g.get t).2)
      (fun t => moment m t.val) (fun t => moment (m + 1) t.val))
    (fromThree unit (fun i => extendVec (newOldLeft hm i) 1 (scalar i))
      (fun i => extendVec (newOldRight hm i) 1 (scalar i)))

private lemma old_point_factors {m : ℕ} (hm : 0 < m) (g : List Edge) (t : Fin g.length) :
    (fun i => enlarge (pointVariables hm g) (Fin.castAdd 5 t, .inl i)) =
      unit (g.get t).1 + unit (g.get t).2 ∧
    (fun j => enlarge (pointVariables hm g) (Fin.castAdd 5 t, .inr (.inl j))) =
      extendVec (moment m t.val) 0 0 ∧
    (fun k => enlarge (pointVariables hm g) (Fin.castAdd 5 t, .inr (.inr k))) =
      extendVec (moment (m + 1) t.val) 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    simp [enlarge, splitCol, pointVariables, fromThree, t.isLt]
  · funext j
    by_cases hj : j.val < m <;> simp [enlarge, splitCol, pointVariables, fromThree, t.isLt,
      extendVec, hj]
  · funext k
    by_cases hk : k.val ≤ m
    · have hk' := Nat.lt_succ_of_le hk
      simp [enlarge, splitCol, pointVariables, fromThree, t.isLt, extendVec, hk']
    · have hk' : ¬ k.val < m + 1 := fun h => hk (Nat.le_of_lt_succ h)
      simp [enlarge, splitCol, pointVariables, t.isLt, extendVec, hk']

private lemma new_point_factors {m : ℕ} (hm : 0 < m) (g : List Edge) (t : Fin 5) :
    (fun i => enlarge (pointVariables hm g) (Fin.natAdd g.length t, .inl i)) = unit t ∧
    (fun j => enlarge (pointVariables hm g) (Fin.natAdd g.length t, .inr (.inl j))) =
      extendVec (newOldLeft hm t) 1 (scalar t) ∧
    (fun k => enlarge (pointVariables hm g) (Fin.natAdd g.length t, .inr (.inr k))) =
      extendVec (newOldRight hm t) 1 (scalar t) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;>
    simp [enlarge, splitCol, pointVariables, fromThree]

end FriedlandWidthTwo

namespace FriedlandWidthTwo

private lemma contraction_sum {m : ℕ} (φ : (Outside m → ℂ) →ₗ[ℂ] ℂ) (i j : Fin 5)
    (b : Vec (m + 2)) (c : Vec (m + 3)) :
    φ (tensorOutside (unit i + unit j) b c) = contraction φ i b c + contraction φ j b c := by
  simp only [contraction_def, ← map_add]
  congr 1
  funext row
  simp only [tensorOutside, Pi.add_apply]
  ring

private theorem outside_witness_from_graph {m : ℕ} (hm : 0 < m) (g : List Edge)
    (hloop : ∀ e ∈ g, e.1 ≠ e.2)
    (hdeg : ∀ i, degree g i = m - 1 ∨ degree g i = m) :
    Function.Surjective (outsideMatrix (pointVariables hm g)).mulVec := by
  apply surj_of_no_annihilator (outsideMatrix (pointVariables hm g)).mulVecLin
  intro φ hφ
  change ∀ u, φ ((outsideMatrix (pointVariables hm g)).mulVec u) = 0 at hφ

  let L := contraction φ
  let F (i : Fin 5) := ((L i).flip (lastNew (m + 1))).comp oldEmbed
  let G (i : Fin 5) := (L i (lastNew m)).comp oldEmbed
  let remainingScalar (i : Fin 5) := L i (lastNew m) (lastNew (m + 1))
  let α := newOldLeft hm
  let β := newOldRight hm
  have newB (i : Fin 5) (c : Vec (m + 3)) : L i (extendVec (α i) 1 (scalar i)) c = 0 := by
    have h := (directions_annihilated _ φ hφ (Fin.natAdd g.length i) 0 0 c).2.2
    obtain ⟨hx, hy, _⟩ := new_point_factors hm g i
    rw [hx, hy] at h
    exact h
  have newC (i : Fin 5) (b : Vec (m + 2)) : L i b (extendVec (β i) 1 (scalar i)) = 0 := by
    have h := (directions_annihilated _ φ hφ (Fin.natAdd g.length i) 0 b 0).2.1
    obtain ⟨hx, _, hz⟩ := new_point_factors hm g i
    rw [hx, hz] at h
    exact h
  have formula (i : Fin 5) (b : Vec m) (c : Vec (m + 1)) (s t u v : ℂ) :
      L i (extendVec b s t) (extendVec c u v) =
        (v - scalar i * u) * F i (b - s • α i) + (t - scalar i * s) * G i (c - u • β i) +
          (t - scalar i * s) * (v - scalar i * u) * remainingScalar i :=
    slice_formula φ i (α i) (β i) (scalar i) (newB i) (newC i) b c s t u v

  have killMoments (t : Fin g.length) :
      (F (g.get t).1 (moment m t.val) = 0 ∧ F (g.get t).2 (moment m t.val) = 0) ∧
      (G (g.get t).1 (moment (m + 1) t.val) = 0 ∧ G (g.get t).2 (moment (m + 1) t.val) = 0) := by
    let i := (g.get t).1
    let j := (g.get t).2
    have hij : scalar i ≠ scalar j :=
      fun he => hloop (g.get t) (List.get_mem g t) (scalar_injective he)
    obtain ⟨hx, hy, hz⟩ := old_point_factors hm g t
    have hF (q w : ℂ) :
        (w - scalar i * q) * F i (moment m t.val) +
          (w - scalar j * q) * F j (moment m t.val) = 0 := by
      have h := (directions_annihilated _ φ hφ (Fin.castAdd 5 t) 0 0
        (extendVec (0 : Vec (m + 1)) q w)).2.2
      rw [hx, hy, contraction_sum] at h
      change L i _ _ + L j _ _ = 0 at h
      rw [formula, formula] at h
      simpa only [mul_zero, sub_zero, zero_smul, zero_mul, add_zero] using h
    have hG (q w : ℂ) :
        (w - scalar i * q) * G i (moment (m + 1) t.val) +
          (w - scalar j * q) * G j (moment (m + 1) t.val) = 0 := by
      have h := (directions_annihilated _ φ hφ (Fin.castAdd 5 t) 0
        (extendVec (0 : Vec m) q w) 0).2.1
      rw [hx, hz, contraction_sum] at h
      change L i _ _ + L j _ _ = 0 at h
      rw [formula, formula] at h
      simpa only [mul_zero, sub_zero, zero_smul, zero_mul, add_zero, zero_add] using h
    change (F i (moment m t.val) = 0 ∧ F j (moment m t.val) = 0) ∧
      (G i (moment (m + 1) t.val) = 0 ∧ G j (moment (m + 1) t.val) = 0)
    exact ⟨edge_two_equations hij (by simpa using hF 0 1) (by simpa using hF 1 0),
      edge_two_equations hij (by simpa using hG 0 1) (by simpa using hG 1 0)⟩

  have killTail (i : Fin 5) :
      F i (unit (finalOld hm)) = 0 ∧ G i (unit (penultimate hm)) = 0 ∧
        G i (unit (Fin.last m)) = 0 ∧ remainingScalar i = 0 := by
    apply new_directions_independent i
    intro t ht
    obtain ⟨_, hy, hz⟩ := new_point_factors hm g t
    have h := (directions_annihilated _ φ hφ (Fin.natAdd g.length t) (unit i) 0 0).1
    rw [hy, hz] at h
    change L i (extendVec (α t) 1 (scalar t)) (extendVec (β t) 1 (scalar t)) = 0 at h
    rw [formula] at h
    simp only [mul_one, one_smul, α, β, newOldLeft, newOldRight, map_sub, map_smul, map_add,
      smul_eq_mul] at h
    linear_combination h

  apply contraction_ext
  intro i
  let Inc := {t : Fin g.length // i = (g.get t).1 ∨ i = (g.get t).2}
  let d := Fintype.card Inc
  let e : Fin d ≃ Inc := (Fintype.equivFin Inc).symm
  let f (t : Fin d) : ℂ := ((e t).val.val : ℂ)
  have hd : d = m - 1 ∨ d = m := by
    change Fintype.card Inc = m - 1 ∨ Fintype.card Inc = m
    unfold Inc
    rw [card_incident]
    exact hdeg i
  have hf : Function.Injective f := by
    intro a b hab
    have he : (e a).val.val = (e b).val.val := by
      change ((e a).val.val : ℂ) = ((e b).val.val : ℂ) at hab
      exact_mod_cast hab
    exact e.injective (Subtype.ext (Fin.ext he))
  have hF : F i = 0 := by
    apply moments_and_tail (d := d) (by omega) hf
    · intro t
      change F i (moment m (e t).val.val) = 0
      obtain ⟨hfirst, hsecond⟩ := (killMoments (e t).val).1
      rcases (e t).property with hi | hi
      · simpa only [hi] using hfirst
      · simpa only [hi] using hsecond
    · intro j hj
      have he : j = finalOld hm := by
        apply Fin.ext
        change j.val = m - 1
        have := j.isLt
        omega
      exact he ▸ (killTail i).1
  have hG : G i = 0 := by
    apply moments_and_tail (d := d) (by omega) hf
    · intro t
      change G i (moment (m + 1) (e t).val.val) = 0
      obtain ⟨hfirst, hsecond⟩ := (killMoments (e t).val).2
      rcases (e t).property with hi | hi
      · simpa only [hi] using hfirst
      · simpa only [hi] using hsecond
    · intro j hj
      by_cases hh : j.val = m
      · have he : j = Fin.last m := Fin.ext hh
        exact he ▸ (killTail i).2.2.1
      · have he : j = penultimate hm := by
          apply Fin.ext
          change j.val = m - 1
          have := j.isLt
          omega
        exact he ▸ (killTail i).2.1
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro c
  change L i b c = 0
  conv_lhs =>
    arg 2
    rw [extendVec_all c]
  conv_lhs =>
    arg 1
    rw [extendVec_all b]
  rw [formula]
  simp [hF, hG, (killTail i).2.2.2]

end FriedlandWidthTwo

theorem FriedlandWidthTwo.extension : FriedlandFiveSliceInduction.H2 := by
  intro m hm hw
  obtain ⟨g, hg, hloop, hdeg⟩ := FriedlandWidthTwo.edges_for_extension m hm
  let r := 5 * m * (m + 1) ⌈/⌉ (5 + m + (m + 1) - 2)
  have hOutside : ∃ p : FriedlandWidthTwo.Variables m r → ℂ,
      Function.Surjective (FriedlandWidthTwo.outsideMatrix p).mulVec := by
    change g.length = r at hg
    rw [← hg]
    exact ⟨_, FriedlandWidthTwo.outside_witness_from_graph (by omega) g hloop hdeg⟩
  exact FriedlandWidthTwo.spans_add_two_of_outside_witness hOutside hw

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2.H1 :=
  FriedlandFiveSliceInduction.main FriedlandBinarySeeds.seeds FriedlandWidthTwo.extension
