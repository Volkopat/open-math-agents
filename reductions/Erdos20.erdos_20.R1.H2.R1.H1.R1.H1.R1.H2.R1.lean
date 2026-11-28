import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

-- Reduction Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.H2.R1 of step Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.H2

/-!
# Splitting tree compression into four-site wire packets and planar map compression

Splits the tree-compression step `Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.H2` along the two
independent stages of OpenAI (Nov 24, 2026), *Euclidean geometry in the asymptotic spectrum of
tensors* (`SiteTensor.exists_tree_wire_packet`, `ChordGraph.straighten_classes`,
`UniformDecorations.grid_compress_of_rounds`, and `PlaneCompression` / `PlaneSizeGap`):

- `H1` (spectral comparison on four sites): if every finite-site complex spectral point has a tree
  wire metric, then for every tolerance `σ > 0` there is a packet width `m > 0` such that the
  four-site crossing matching on `2^m`-bit wires decomposes as a sum of at most `2^(σ * m)` local
  linear restrictions of products of the two noncrossing matchings whose widths sum to `m`.
- `H2` (planar map straightening and compilation): given such four-site wire packets for every
  `σ > 0`, for every contraction base `a ≥ 2` there exists a recursive table-cost bound satisfying
  the `10 * w` width-growth / `n / a` vertex-shrinkage recurrence that pins and computes every
  bipartite independent-set polynomial on `m + k = N` vertices via an arithmetic circuit.
- `main` iterates the compression recurrence and chooses `a` with `2 * log_a 10 < δ` to derive
  the stretched-subexponential circuit upper bound `2 ^ (N ^ δ)` uniformly over all bipartite
  graphs of order `N`.
-/

namespace OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1_H2_R1

def H1 : Prop :=
 (∀ (J : Type) [Fintype J] [DecidableEq J], let S := Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ; ∀ Φ : S → ℝ,
 (∀ X, 0 ≤ Φ X) → Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 → (∀ X : S, (∀ z, X.2 z = 0) → Φ X = 0) →
 (∀ X Y : S, ((∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y ∧
 Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩) else if h' : ∀ j, X.1 j ≤ z j then
 Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y) →
 ∀ a b c e : J, let w := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩);
 w a b + w c e ≤ max (w a c + w b e) (w a e + w b c)) →
 ∀ σ : ℝ, 0 < σ → ∃ (m L : ℕ), 0 < m ∧ (L : ℝ) ≤ (2 : ℝ) ^ (σ * m) ∧
 ∃ (u v : Fin L → ℕ), (∀ l, u l + v l = m) ∧
 ∃ (A0 A1 A2 A3 : ∀ l : Fin L, Fin (2 ^ m) → Fin (2 ^ u l) → Fin (2 ^ v l) → ℂ),
 ∀ x : Fin 4 → Fin (2 ^ m), (if x 0 = x 2 ∧ x 1 = x 3 then (1 : ℂ) else 0) =
 ∑ l : Fin L, ∑ a : Fin (2 ^ u l), ∑ b : Fin (2 ^ u l), ∑ c : Fin (2 ^ v l), ∑ d : Fin (2 ^ v l),
 A0 l (x 0) a c * A1 l (x 1) a d * A2 l (x 2) b d * A3 l (x 3) b c

def H2 : Prop :=
 (∀ σ : ℝ, 0 < σ → ∃ (m L : ℕ), 0 < m ∧ (L : ℝ) ≤ (2 : ℝ) ^ (σ * m) ∧
 ∃ (u v : Fin L → ℕ), (∀ l, u l + v l = m) ∧
 ∃ (A0 A1 A2 A3 : ∀ l : Fin L, Fin (2 ^ m) → Fin (2 ^ u l) → Fin (2 ^ v l) → ℂ),
 ∀ x : Fin 4 → Fin (2 ^ m), (if x 0 = x 2 ∧ x 1 = x 3 then (1 : ℂ) else 0) =
 ∑ l : Fin L, ∑ a : Fin (2 ^ u l), ∑ b : Fin (2 ^ u l), ∑ c : Fin (2 ^ v l), ∑ d : Fin (2 ^ v l),
 A0 l (x 0) a c * A1 l (x 1) a d * A2 l (x 2) b d * A3 l (x 3) b c) →
 ∀ a : ℕ, 2 ≤ a → ∃ (cost : ℕ → ℕ → ℝ) (pinC gateC widthC : ℝ),
 0 ≤ pinC ∧ 0 ≤ gateC ∧ 0 ≤ widthC ∧
 (∀ w : ℕ, 0 < w → cost 1 w ≤ (2 : ℝ) ^ (gateC * (w + Real.log 2))) ∧
 (∀ n w : ℕ, 1 < n → 0 < w → ∃ w' : ℕ, 0 < w' ∧ (w' : ℝ) ≤ 10 * w + widthC * Real.log (2 * n) ∧
 cost n w ≤ (2 : ℝ) ^ (gateC * (w + Real.log (2 * n))) + cost (max 1 (n / a)) w') ∧
 ∀ᶠ N : ℕ in Filter.atTop, ∀ (m k : ℕ) (E : Fin m → Fin k → Bool), m + k = N →
 ∃ W : ℕ, 0 < W ∧ (W : ℝ) ≤ widthC * Real.log (2 * ((m * k + 2 * N : ℕ) : ℝ)) ∧
 let R := MvPolynomial ((Fin m ⊕ Fin k) × Bool) ℂ; ∃ (s : ℕ) (g : Fin s → R),
 (s : ℝ) ≤ (2 : ℝ) ^ (pinC * Real.log (2 * ((m * k + 2 * N : ℕ) : ℝ))) + cost (m * k + 2 * N) W ∧
 (∀ i, ∃ p q : R, (p.totalDegree ≤ 1 ∨ ∃ j < i, p = g j) ∧ (q.totalDegree ≤ 1 ∨ ∃ j < i, q = g j) ∧ (g i = p + q ∨ g i = p * q)) ∧
 ∃ i, MvPolynomial.homogeneousComponent N (g i) = ∑ b : (Fin m → Bool) × (Fin k → Bool), if ∀ x y, E x y = true → b.1 x = true → b.2 y ≠ true
 then (∏ x, (MvPolynomial.X (Sum.inl x, b.1 x) : R)) * ∏ y, MvPolynomial.X (Sum.inr y, b.2 y) else 0

lemma compressedVertexBound_succ {a : ℕ} (ha : 1 < a) (N j : ℕ) :
    max 1 (N / a ^ (j + 1)) = max 1 (max 1 (N / a ^ j) / a) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  by_cases h : N / a ^ j = 0
  · simp [h, Nat.div_eq_of_lt ha]
  · rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr h)]

lemma compressedVertexBound_clog {a : ℕ} (ha : 1 < a) (N : ℕ) :
    max 1 (N / a ^ Nat.clog a N) = 1 :=
  max_eq_left (Nat.div_le_of_le_mul (by simpa using Nat.le_pow_clog ha N))

lemma ten_pow_rounds_le {a N : ℕ} (ha : 1 < a) (hN : 1 ≤ N) :
    (10 : ℝ) ^ Nat.clog a N ≤ 10 * (N : ℝ) ^ Real.logb a 10 := by
  have ha' : (1 : ℝ) < a := by exact_mod_cast ha
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Nat.ceil_lt_add_one (Real.logb_nonneg ha' hN')
  rw [Real.natCeil_logb_natCast] at h
  calc
    (10 : ℝ) ^ Nat.clog a N = (10 : ℝ) ^ ((Nat.clog a N : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (10 : ℝ) ^ (Real.logb a N + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h.le
    _ = 10 * (N : ℝ) ^ Real.logb a 10 := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 10), Real.rpow_one, mul_comm]
      congr 1
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10),
        Real.rpow_def_of_pos (zero_lt_one.trans_le hN')]
      congr 1
      unfold Real.logb
      ring

lemma compressedWidth {w : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) {L : ℕ}
    (hu : ∀ i, i < L → w (i + 1) ≤ 10 * w i + B) (j : ℕ) (hj : j ≤ L) :
    w j + B ≤ (10 : ℝ) ^ j * (w 0 + B) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hu j (by omega)
    have g := ih (by omega)
    rw [pow_succ]
    linarith only [h, g, hB]

lemma iterated_compression_size {a N : ℕ} (ha : 1 < a) (hN : 1 ≤ N)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w cost : ℕ → ℝ)
    (init : w 0 ≤ B * Real.log (2 * N))
    (width : ∀ j, j < Nat.clog a N → w (j + 1) ≤ 10 * w j + B * Real.log (2 * N))
    (gates : ∀ j, j ≤ Nat.clog a N → cost j ≤ (2 : ℝ) ^ (A * (w j + Real.log (2 * N)))) :
    ∑ j ∈ Finset.range (Nat.clog a N + 1), cost j ≤
      (2 : ℝ) ^ ((10 / Real.log 2 + A * (20 * B + 1)) * ((N : ℝ) ^ Real.logb a 10 * Real.log (2 * N))) := by
  let L := Nat.clog a N
  let P := (N : ℝ) ^ Real.logb a 10
  let b := Real.log (2 * N)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.log 2 ≤ b := Real.log_le_log (by norm_num) (show (2 : ℝ) ≤ 2 * N by linarith)
  have hP : 1 ≤ P := Real.one_le_rpow hN' (Real.logb_nonneg (by exact_mod_cast ha) (by norm_num))
  have hL := ten_pow_rounds_le ha hN
  change (10 : ℝ) ^ L ≤ 10 * P at hL
  have hmax (j : ℕ) (hj : j ≤ L) : w j + b ≤ (20 * B + 1) * (P * b) := by
    have hc := compressedWidth (mul_nonneg hB (hlog.le.trans hb)) width j hj
    have hi : (10 : ℝ) ^ j ≤ 10 * P := (pow_le_pow_right₀ (by norm_num) hj).trans hL
    have hh : (10 : ℝ) ^ j * (w 0 + B * b) ≤ (10 * P) * (2 * B * b) := by
      apply (mul_le_mul_of_nonneg_left (show w 0 + B * b ≤ 2 * B * b by linarith [init]) (by positivity)).trans
      exact mul_le_mul_of_nonneg_right hi (mul_nonneg (by positivity) (hlog.le.trans hb))
    change w j + B * b ≤ (10 : ℝ) ^ j * (w 0 + B * b) at hc
    have hPb : b ≤ P * b := le_mul_of_one_le_left (hlog.le.trans hb) hP
    linarith only [hc, hh, hPb, mul_nonneg hB (hlog.le.trans hb)]
  let G := (2 : ℝ) ^ (A * ((20 * B + 1) * (P * b)))
  have allcost (j : ℕ) (hj : j < L + 1) : cost j ≤ G :=
    (gates j (by omega)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (hmax j (by omega)) hA))
  have hround : (L : ℝ) ≤ 10 / Real.log 2 * (P * b) := by
    have hn : (L : ℝ) ≤ (10 : ℝ) ^ L := by exact_mod_cast (Nat.lt_pow_self (a := 10) (n := L) (by decide)).le
    apply (hn.trans hL).trans
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 10 * P by positivity)
    apply (le_div_iff₀ hlog).mpr at hh
    convert hh using 1
    ring
  calc
    ∑ j ∈ Finset.range (L + 1), cost j ≤ ∑ _j ∈ Finset.range (L + 1), G :=
      Finset.sum_le_sum fun j hj => allcost j (Finset.mem_range.mp hj)
    _ = ((L + 1 : ℕ) : ℝ) * G := by simp
    _ ≤ (2 : ℝ) ^ (L : ℝ) * G := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      rw [Real.rpow_natCast]
      exact_mod_cast (show L + 1 ≤ 2 ^ L from Nat.lt_two_pow_self)
    _ ≤ (2 : ℝ) ^ (10 / Real.log 2 * (P * b)) * G :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hround)
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((10 / Real.log 2 + A * (20 * B + 1)) * (P * b)) := by
      dsimp only [G]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

lemma planar_size_of_compression_step {a N W : ℕ} (ha : 1 < a) (hN : 1 ≤ N) (hW : 0 < W)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (cost : ℕ → ℕ → ℝ)
    (initial : (W : ℝ) ≤ B * Real.log (2 * N))
    (base : ∀ w : ℕ, 0 < w → cost 1 w ≤ (2 : ℝ) ^ (A * (w + Real.log 2)))
    (step : ∀ n w : ℕ, 1 < n → 0 < w → ∃ w' : ℕ, 0 < w' ∧
      (w' : ℝ) ≤ 10 * w + B * Real.log (2 * n) ∧
      cost n w ≤ (2 : ℝ) ^ (A * (w + Real.log (2 * n))) + cost (max 1 (n / a)) w') :
    cost N W ≤ (2 : ℝ) ^ ((10 / Real.log 2 + A * (20 * B + 1)) *
      ((N : ℝ) ^ Real.logb a 10 * Real.log (2 * N))) := by
  let n : ℕ → ℕ := fun j => max 1 (N / a ^ j)
  have hpos (j : ℕ) : 1 ≤ n j := le_max_left _ _
  have hle (j : ℕ) : n j ≤ N := max_le hN (Nat.div_le_self _ _)
  have hlog (j : ℕ) : Real.log (2 * n j) ≤ Real.log (2 * N) :=
    Real.log_le_log (by positivity [show (0 : ℝ) < n j by exact_mod_cast hpos j]) (by
      gcongr
      exact hle j)
  have hlogN : 0 ≤ Real.log (2 * N) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith)
  let Width := {w : ℕ // 0 < w}
  have hs (j : ℕ) (w : Width) : ∃ v : Width, (v.val : ℝ) ≤ 10 * w.val + B * Real.log (2 * N) ∧
      cost (n j) w.val ≤ (2 : ℝ) ^ (A * (w.val + Real.log (2 * N))) + cost (n (j + 1)) v.val := by
    by_cases hj : 1 < n j
    · obtain ⟨v, hvpos, hv, hc⟩ := step (n j) w.val hj w.property
      refine ⟨⟨v, hvpos⟩, hv.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hlog j) hB) _), hc.trans ?_⟩
      rw [show n (j + 1) = max 1 (n j / a) from compressedVertexBound_succ ha N j]
      gcongr
      · norm_num
      · exact hle j
    · have heq : n j = 1 := le_antisymm (by omega) (hpos j)
      have heq' : n (j + 1) = 1 := by
        rw [show n (j + 1) = max 1 (n j / a) from compressedVertexBound_succ ha N j, heq, Nat.div_eq_of_lt ha]
        rfl
      refine ⟨w, ?_, ?_⟩
      · nlinarith only [mul_nonneg hB hlogN, Nat.cast_nonneg (α := ℝ) w.val]
      · rw [heq, heq']
        linarith only [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (A * (w.val + Real.log (2 * N)))]
  choose next hw hc using hs
  let v (j : ℕ) : Width := Nat.rec (motive := fun _ => Width) ⟨W, hW⟩ next j
  let w (j : ℕ) : ℕ := (v j).val
  let G (j : ℕ) := (2 : ℝ) ^ (A * (w j + Real.log (2 * N)))
  have hc' (j : ℕ) : cost (n j) (w j) ≤ G j + cost (n (j + 1)) (w (j + 1)) := hc j (v j)
  have total (j : ℕ) : cost N W ≤ ∑ i ∈ Finset.range j, G i + cost (n j) (w j) := by
    induction j with
    | zero => simp [n, w, v, max_eq_right hN]
    | succ j ih =>
      have h := hc' j
      rw [Finset.sum_range_succ]
      linarith only [h, ih]
  let L := Nat.clog a N
  have hbase : cost (n L) (w L) ≤ G L := by
    rw [show n L = 1 from compressedVertexBound_clog ha N]
    apply (base _ (v L).property).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hA
    apply add_le_add_right
    apply Real.log_le_log (by norm_num)
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  calc
    cost N W ≤ ∑ i ∈ Finset.range L, G i + G L := (total L).trans (add_le_add_right hbase _)
    _ = ∑ i ∈ Finset.range (L + 1), G i := (Finset.sum_range_succ ..).symm
    _ ≤ _ := iterated_compression_size ha hN A B hA hB (fun j => w j) G initial
      (fun j _ => hw j (v j)) (fun _ _ => le_rfl)

lemma exists_base_two_logb_ten_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, 2 ≤ a ∧ 2 * Real.logb a 10 < δ := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
    (2 * Real.log 10 / δ)
  obtain ⟨a, ha, hlarge⟩ := ((Filter.eventually_ge_atTop (2 : ℕ)).and hlog).exists
  have ha' : (1 : ℝ) < a := by exact_mod_cast Nat.lt_of_succ_le ha
  refine ⟨a, ha, ?_⟩
  rw [Real.logb, ← mul_div_assoc, div_lt_iff₀ (Real.log_pos ha')]
  simpa only [Function.comp_apply, mul_comm δ] using (div_lt_iff₀ hδ).mp hlarge

lemma bipartite_grid_size_le {u v n : ℕ} (h : u + v = n) :
    ((u * v + 2 * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 2 * n := by
  subst n
  push_cast
  nlinarith [sq_nonneg ((u : ℝ) - v)]

theorem main : H1 → H2 → OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro h1 h2 htree δ hδ
  obtain ⟨a, ha, hgap⟩ := exists_base_two_logb_ten_lt hδ
  obtain ⟨cost, pinC, gateC, widthC, hpin, hgate, hwidth, hbase, hstep, hgrid⟩ := h2 (h1 htree) a ha
  have ha1 : 1 < a := Nat.lt_of_succ_le ha
  have ha' : (1 : ℝ) < a := by exact_mod_cast ha1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C0 : ℝ := 10 / Real.log 2 + gateC * (20 * widthC + 1)
  have hC0 : 0 < C0 := add_pos_of_pos_of_nonneg (div_pos (by norm_num) hlog2)
    (mul_nonneg hgate (by linarith))
  let C : ℝ := C0 + pinC + (Real.log 2)⁻¹
  have hC : 0 < C := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hC0 hpin)
    (inv_nonneg.mpr hlog2.le)
  let p : ℝ := Real.logb a 10
  have hp : 0 ≤ p := Real.logb_nonneg ha' (by norm_num)
  have hsmall := ((isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).const_mul_left
    (2 * C)).comp_tendsto tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < ‖(N : ℝ) ^ (δ - 2 * p)‖ := by
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  filter_upwards [hgrid, Filter.eventually_ge_atTop 8,
    hsmall.eventuallyLT_norm_of_eventually_pos hpos] with N hNgrid hN8 hlogN
  intro m k E hmk
  obtain ⟨W, hWpos, hW, s, g, hs, hgates, hout⟩ := hNgrid m k E hmk
  refine ⟨s, g, ?_, hgates, hout⟩
  let M : ℕ := m * k + 2 * N
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hN8' : (8 : ℝ) ≤ N := by exact_mod_cast hN8
  have hNpos : (0 : ℝ) < N := by linarith
  have hMle : (M : ℝ) ≤ (N : ℝ) ^ 2 / 4 + 2 * N := bipartite_grid_size_le hmk
  have hM2 : 2 * (M : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [hMle, mul_nonneg hNpos.le (sub_nonneg.mpr hN8')]
  have hMN2 : (M : ℝ) ≤ (N : ℝ) ^ 2 := by linarith
  let ℓ : ℝ := Real.log (2 * M)
  let P : ℝ := (M : ℝ) ^ p * ℓ
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith)
  have hP : ℓ ≤ P := le_mul_of_one_le_left (hlog2.le.trans hℓ)
    (Real.one_le_rpow (by exact_mod_cast hM1) hp)
  have hP0 : 0 ≤ P := (hlog2.le.trans hℓ).trans hP
  have hcost : cost M W ≤ (2 : ℝ) ^ (C0 * P) :=
    planar_size_of_compression_step ha1 hM1 hWpos hgate hwidth cost hW hbase hstep
  have hpin' : pinC * ℓ ≤ (C0 + pinC) * P := by
    linarith only [mul_le_mul_of_nonneg_left hP hpin, mul_nonneg hC0.le hP0]
  have htab' : C0 * P ≤ (C0 + pinC) * P := by linarith only [mul_nonneg hpin hP0]
  have h1P : 1 ≤ (Real.log 2)⁻¹ * P := by
    rw [← div_eq_inv_mul, le_div_iff₀ hlog2, one_mul]
    exact hℓ.trans hP
  have hsC : (s : ℝ) ≤ (2 : ℝ) ^ (C * P) := by
    calc
      (s : ℝ) ≤ (2 : ℝ) ^ (pinC * ℓ) + cost M W := hs
      _ ≤ (2 : ℝ) ^ ((C0 + pinC) * P) + (2 : ℝ) ^ ((C0 + pinC) * P) := add_le_add
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpin')
        (hcost.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) htab'))
      _ = (2 : ℝ) ^ ((C0 + pinC) * P + 1) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        ring
      _ ≤ (2 : ℝ) ^ (C * P) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp only [C]
        linarith only [h1P]
  have hMpow : (M : ℝ) ^ p ≤ (N : ℝ) ^ (2 * p) := by
    convert Real.rpow_le_rpow hMpos.le hMN2 hp using 1
    exact Real.rpow_natCast_mul hNpos.le 2 p
  have hMlog : ℓ ≤ 2 * Real.log N := by
    simpa only [ℓ, Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) hMpos) hM2
  have hlogN' : 2 * C * Real.log N < (N : ℝ) ^ (δ - 2 * p) := by
    change ‖2 * C * Real.log N‖ < ‖(N : ℝ) ^ (δ - 2 * p)‖ at hlogN
    have hnlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hlogN
    exact hlogN
  have hCP : C * P < (N : ℝ) ^ δ := by
    calc
      C * P = C * (M : ℝ) ^ p * ℓ := by dsimp only [P]; ring
      _ ≤ C * (M : ℝ) ^ p * (2 * Real.log N) := by gcongr
      _ ≤ C * (N : ℝ) ^ (2 * p) * (2 * Real.log N) := by
        have hnlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
        gcongr
      _ = (N : ℝ) ^ (2 * p) * (2 * C * Real.log N) := by ring
      _ < (N : ℝ) ^ (2 * p) * (N : ℝ) ^ (δ - 2 * p) :=
        mul_lt_mul_of_pos_left hlogN' (Real.rpow_pos_of_pos hNpos _)
      _ = (N : ℝ) ^ δ := by rw [← Real.rpow_add hNpos]; congr 1; ring
  exact hsC.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hCP.le)

end OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1_H2_R1
