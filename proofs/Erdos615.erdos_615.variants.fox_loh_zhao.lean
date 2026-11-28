import FormalConjectures.ErdosProblems.«615»
import Mathlib

/-!
Self-contained proof of `Erdos615.erdos_615.variants.fox_loh_zhao`:
for sufficiently large `n`, constructs a `K₄`-free graph on `Fin n` with at least `n^2 / 8`
edges and independence number `O(n * (log log n)^(3/2) / (log n)^(1/2))`, via:
1. Discrete `d`-dimensional Prékopa–Leindler on `[-d, d]^d` (`d = ⌊log n / (3 log log n)⌋`);
2. Sharp block-summed Fejér anti-concentration (no logarithmic loss in the Fourier cutoff);
3. Direct unweighted Bollobás–Erdős twin seed on `Fin n` with `|A| ≤ (2d+1)^d ≤ n^(1/3)`;
4. Deterministic greedy vertex-replacement densification pushing edge count to `≥ n^2 / 8`.
-/

open Filter SimpleGraph BigOperators
open scoped Classical

namespace Erdos615FLZ

noncomputable section

private lemma floor_mul_ge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b - a - b ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by
  by_cases ha1 : a ≤ 1
  · have h1 : a * b - a - b ≤ 0 := by nlinarith
    have h2 : (0 : ℝ) ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by positivity
    linarith
  · by_cases hb1 : b ≤ 1
    · have h1 : a * b - a - b ≤ 0 := by nlinarith
      have h2 : (0 : ℝ) ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by positivity
      linarith
    · push Not at ha1 hb1
      have hfa : a - 1 ≤ (Nat.floor a : ℝ) := le_of_lt (Nat.sub_one_lt_floor a)
      have hfb : b - 1 ≤ (Nat.floor b : ℝ) := le_of_lt (Nat.sub_one_lt_floor b)
      have ha' : 0 ≤ a - 1 := by linarith
      have hb' : 0 ≤ b - 1 := by linarith
      nlinarith


private def ip {d : ℕ} (x y : Fin d → ℤ) : ℝ :=
  ∑ r : Fin d, (x r : ℝ) * (y r : ℝ)

private def normSq {d : ℕ} (x : Fin d → ℤ) : ℝ :=
  ∑ r : Fin d, (x r : ℝ) ^ 2

private lemma normSq_eq_ip {d : ℕ} (x : Fin d → ℤ) : normSq x = ip x x := by
  simp only [normSq, ip, sq]

private lemma normSq_nonneg {d : ℕ} (x : Fin d → ℤ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma normSq_neg {d : ℕ} (x : Fin d → ℤ) : normSq (-x) = normSq x := by
  simp [normSq]

private lemma ip_comm {d : ℕ} (x y : Fin d → ℤ) : ip x y = ip y x := by
  simp only [ip]
  refine Finset.sum_congr rfl fun r _ => mul_comm _ _

private lemma ip_neg_right {d : ℕ} (x y : Fin d → ℤ) : ip x (-y) = -ip x y := by
  simp only [ip, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

private lemma ip_add_left {d : ℕ} (x₁ x₂ y : Fin d → ℤ) :
    ip (x₁ + x₂) y = ip x₁ y + ip x₂ y := by
  simp only [ip, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private lemma ip_add_right {d : ℕ} (x y₁ y₂ : Fin d → ℤ) :
    ip x (y₁ + y₂) = ip x y₁ + ip x y₂ := by
  simp only [ip, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

private lemma ip_sq_le_normSq_mul {d : ℕ} (x y : Fin d → ℤ) :
    (ip x y) ^ 2 ≤ normSq x * normSq y := by
  simpa [ip, normSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r : Fin d => (x r : ℝ))
      (fun r : Fin d => (y r : ℝ)))

private lemma normSq_triangle_bound {d : ℕ} (x y z : Fin d → ℤ) (C : ℝ)
    (hxy : normSq (x + y) ≤ 4 * C ^ 2)
    (hyz : normSq (y + z) ≤ 4 * C ^ 2)
    (hzx : normSq (z + x) ≤ 4 * C ^ 2) :
    normSq x ≤ 9 * C ^ 2 := by
  have hcoord : ∀ r : Fin d,
      4 * (x r : ℝ) ^ 2 ≤
        3 * ((x r + y r : ℝ) ^ 2 + (y r + z r : ℝ) ^ 2 + (z r + x r : ℝ) ^ 2) := by
    intro r
    nlinarith [sq_nonneg ((x r : ℝ) - (z r : ℝ)),
               sq_nonneg ((x r : ℝ) + (y r : ℝ) + (y r : ℝ) + (z r : ℝ)),
               sq_nonneg ((x r : ℝ) - (y r : ℝ)),
               sq_nonneg ((y r : ℝ) + (z r : ℝ) + (z r : ℝ) + (x r : ℝ)),
               sq_nonneg (2 * (y r : ℝ) + (x r : ℝ) + (z r : ℝ))]
  have hsum : 4 * normSq x ≤ 3 * (normSq (x + y) + normSq (y + z) + normSq (z + x)) := by
    simp only [normSq, Pi.add_apply, Int.cast_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => hcoord r
  linarith


/- ### Module 3A: Elementary 1D and d-D Discrete Prékopa–Leindler on `[-M, M]^d` -/

private def segLen (p q : ℝ) (k : ℤ) : ℝ :=
  min q (max p ((k : ℝ) + 1)) - min q (max p (k : ℝ))

private lemma segLen_nonneg (p q : ℝ) (k : ℤ) : 0 ≤ segLen p q k := by
  unfold segLen
  have h1 : max p (k : ℝ) ≤ max p ((k : ℝ) + 1) := max_le_max_left p (by linarith)
  linarith [min_le_min_left q h1]

private lemma clamp_add (p r q t : ℝ) (hpr : p ≤ r) (hrq : r ≤ q) :
    min q (max p t) = min r (max p t) + min q (max r t) - r := by
  by_cases ht1 : t ≤ p
  · rw [max_eq_left ht1, max_eq_left (ht1.trans hpr), min_eq_right (hpr.trans hrq),
        min_eq_right hpr, min_eq_right hrq]
    ring
  · push Not at ht1
    by_cases ht2 : t ≤ r
    · rw [max_eq_right ht1.le, max_eq_left ht2, min_eq_right (ht2.trans hrq),
          min_eq_right ht2, min_eq_right hrq]
      ring
    · push Not at ht2
      by_cases ht3 : t ≤ q
      · rw [max_eq_right ht1.le, max_eq_right ht2.le, min_eq_right ht3, min_eq_left ht2.le]
        ring
      · push Not at ht3
        rw [max_eq_right ht1.le, max_eq_right ht2.le, min_eq_left ht3.le, min_eq_left ht2.le]
        ring

private lemma segLen_add (p r q : ℝ) (hpr : p ≤ r) (hrq : r ≤ q) (k : ℤ) :
    segLen p r k + segLen r q k = segLen p q k := by
  unfold segLen
  have h1 := clamp_add p r q ((k : ℝ) + 1) hpr hrq
  have h2 := clamp_add p r q (k : ℝ) hpr hrq
  linarith

private lemma segLen_le_one (p q : ℝ) (_hpq : p ≤ q) (k : ℤ) : segLen p q k ≤ 1 := by
  unfold segLen
  have h1 : min q (max p ((k : ℝ) + 1)) ≤ min q (max p (k : ℝ) + 1) := by
    apply min_le_min_left
    exact max_le (by linarith [le_max_left p (k : ℝ)]) (by linarith [le_max_right p (k : ℝ)])
  have h2 : min q (max p (k : ℝ) + 1) ≤ min q (max p (k : ℝ)) + 1 := by
    rcases le_total q (max p (k : ℝ)) with h | h
    · rw [min_eq_left (by linarith : q ≤ max p (k : ℝ) + 1), min_eq_left h]
      linarith
    · rw [min_eq_right h]
      exact min_le_right _ _
  linarith

private lemma segLen_pos_imp {p q : ℝ} {k : ℤ} (h : 0 < segLen p q k) :
    p < (k : ℝ) + 1 ∧ (k : ℝ) < q := by
  unfold segLen at h
  constructor
  · by_contra hle
    push Not at hle
    have h1 : max p ((k : ℝ) + 1) = p := max_eq_left hle
    have h2 : max p (k : ℝ) = p := max_eq_left (by linarith)
    rw [h1, h2] at h
    linarith
  · by_contra hle
    push Not at hle
    have h1 : min q (max p (k : ℝ)) = q := min_eq_left (hle.trans (le_max_right p (k : ℝ)))
    have h2 : min q (max p ((k : ℝ) + 1)) = q :=
      min_eq_left (by linarith [le_max_right p ((k : ℝ) + 1)])
    rw [h1, h2] at h
    linarith

private lemma sum_Icc_segLen (p q : ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, segLen p q k =
      min q (max p ((b : ℝ) + 1)) - min q (max p (a : ℝ)) := by
  obtain ⟨n, hn⟩ := Int.exists_add_of_le hab
  subst hn
  induction n with
  | zero =>
    simp [segLen]
  | succ n ih =>
    have hle : a ≤ a + (n : ℤ) := by omega
    have hIcc : Finset.Icc a (a + ((n + 1 : ℕ) : ℤ)) =
        insert (a + ((n + 1 : ℕ) : ℤ)) (Finset.Icc a (a + (n : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : a + ((n + 1 : ℕ) : ℤ) ∉ Finset.Icc a (a + (n : ℤ)) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot, ih hle]
    unfold segLen
    push_cast
    simp only [add_assoc]
    ring

private def stepInt (S : Finset ℤ) (c : ℤ → ℝ) (p q : ℝ) : ℝ :=
  ∑ k ∈ S, c k * segLen p q k

private lemma stepInt_nonneg (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k) (p q : ℝ) :
    0 ≤ stepInt S c p q :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (segLen_nonneg p q k)

private lemma stepInt_add (S : Finset ℤ) (c : ℤ → ℝ) (p r q : ℝ)
    (hpr : p ≤ r) (hrq : r ≤ q) :
    stepInt S c p r + stepInt S c r q = stepInt S c p q := by
  unfold stepInt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, segLen_add p r q hpr hrq k]

private lemma stepInt_mono (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (p₁ p₂ q₂ q₁ : ℝ) (hp : p₁ ≤ p₂) (h2 : p₂ ≤ q₂) (hq : q₂ ≤ q₁) :
    stepInt S c p₂ q₂ ≤ stepInt S c p₁ q₁ := by
  have h1 := stepInt_add S c p₁ p₂ q₁ hp (h2.trans hq)
  have h2' := stepInt_add S c p₂ q₂ q₁ h2 hq
  have hn1 := stepInt_nonneg S c hc p₁ p₂
  have hn2 := stepInt_nonneg S c hc q₂ q₁
  linarith

private lemma stepInt_le_sum (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (p q : ℝ) (hpq : p ≤ q) :
    stepInt S c p q ≤ ∑ k ∈ S, c k := by
  unfold stepInt
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left (segLen_le_one p q hpq k) (hc k)
  linarith

private lemma stepInt_ge_mul_sub (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (p q M : ℝ) (hpq : p ≤ q) (_hM : 0 ≤ M)
    (hbound : ∀ k : ℤ, p < (k : ℝ) + 1 → (k : ℝ) < q → k ∈ S ∧ M ≤ c k) :
    M * (q - p) ≤ stepInt S c p q := by
  let a : ℤ := Int.floor p
  let b : ℤ := Int.floor q
  have hab : a ≤ b := Int.floor_mono hpq
  have ha_le : (a : ℝ) ≤ p := Int.floor_le p
  have hq_lt : q < (b : ℝ) + 1 := Int.lt_floor_add_one q
  have hsum_len : ∑ k ∈ Finset.Icc a b, segLen p q k = q - p := by
    rw [sum_Icc_segLen p q a b hab]
    have h1 : max p (a : ℝ) = p := max_eq_left ha_le
    have h2 : min q p = p := min_eq_right hpq
    have h3 : max p ((b : ℝ) + 1) = (b : ℝ) + 1 := max_eq_right (hpq.trans hq_lt.le)
    have h4 : min q ((b : ℝ) + 1) = q := min_eq_left hq_lt.le
    rw [h1, h2, h3, h4]
  have hterm : ∀ k ∈ Finset.Icc a b,
      M * segLen p q k ≤ if k ∈ S then c k * segLen p q k else 0 := by
    intro k _
    by_cases hpos : 0 < segLen p q k
    · obtain ⟨h1, h2⟩ := segLen_pos_imp hpos
      obtain ⟨hkS, hMc⟩ := hbound k h1 h2
      simp only [hkS, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right hMc hpos.le
    · have hzero : segLen p q k = 0 := le_antisymm (not_lt.mp hpos) (segLen_nonneg p q k)
      simp [hzero]
  have hstep1 : M * (q - p) ≤ ∑ k ∈ Finset.Icc a b, if k ∈ S then c k * segLen p q k else 0 := by
    rw [← hsum_len, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hstep2 : (∑ k ∈ Finset.Icc a b, if k ∈ S then c k * segLen p q k else 0) ≤
      ∑ k ∈ S, c k * segLen p q k := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.mp hk).2) ?_
    intro k _ _
    exact mul_nonneg (hc k) (segLen_nonneg p q k)
  exact hstep1.trans hstep2

private inductive ValidSegs : ℝ → ℝ → List (ℝ × ℝ × ℝ) → Prop
  | nil {p q : ℝ} (hpq : p ≤ q) : ValidSegs p q []
  | cons {p q x y a : ℝ} {rest : List (ℝ × ℝ × ℝ)}
      (hpx : p ≤ x) (hxy : x < y) (ha : 0 < a) (hrest : ValidSegs y q rest) :
      ValidSegs p q ((x, y, a) :: rest)

private lemma ValidSegs.le {p q : ℝ} {L : List (ℝ × ℝ × ℝ)} (h : ValidSegs p q L) : p ≤ q := by
  induction h with
  | nil hpq => exact hpq
  | cons hpx hxy _ _ ih => linarith

private def segMass : List (ℝ × ℝ × ℝ) → ℝ
  | [] => 0
  | (x, y, a) :: rest => a * (y - x) + segMass rest

private lemma am_gm_step (m a b : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b) :
    m ≤ Real.sqrt (a * b) * ((m / a + m / b) / 2) := by
  have hsq : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have hab : 2 * Real.sqrt (a * b) ≤ a + b := by
    rw [Real.sqrt_mul ha.le]
    nlinarith [Real.mul_self_sqrt ha.le, Real.mul_self_sqrt hb.le]
  have hpos : 0 < a * b := mul_pos ha hb
  have hmul : 2 * (a * b) ≤ Real.sqrt (a * b) * (a + b) := by
    have h1 := mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg (a * b))
    have h2 : Real.sqrt (a * b) * (2 * Real.sqrt (a * b)) = 2 * (a * b) := by
      have := Real.mul_self_sqrt hpos.le
      linarith
    linarith
  have hdiv : (1 : ℝ) ≤ Real.sqrt (a * b) * ((1 / a + 1 / b) / 2) := by
    have hrew : (1 / a + 1 / b) / 2 = (a + b) / (2 * (a * b)) := by field_simp; ring
    rw [hrew, ← mul_div_assoc, one_le_div (by positivity)]
    exact hmul
  have := mul_le_mul_of_nonneg_left hdiv hm
  have hrew2 : m * (Real.sqrt (a * b) * ((1 / a + 1 / b) / 2)) =
      Real.sqrt (a * b) * ((m / a + m / b) / 2) := by ring
  linarith

private lemma step_pl_aux (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∀ (n : ℕ) (pF qF pG qG : ℝ) (F G : List (ℝ × ℝ × ℝ)),
      F.length + G.length ≤ n →
      ValidSegs pF qF F → ValidSegs pG qG G →
      segMass F = segMass G →
      (∀ sF ∈ F, ∀ sG ∈ G, ∀ k : ℤ,
        (sF.1 + sG.1) / 2 < (k : ℝ) + 1 → (k : ℝ) < (sF.2.1 + sG.2.1) / 2 →
        k ∈ S ∧ Real.sqrt (sF.2.2 * sG.2.2) ≤ c k) →
      segMass F ≤ stepInt S c ((pF + pG) / 2) ((qF + qG) / 2) := by
  intro n
  induction n with
  | zero =>
    intro pF qF pG qG F G hlen _ _ _ _
    have hF : F = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hF, segMass]
    exact stepInt_nonneg S c hc _ _
  | succ n ih =>
    intro pF qF pG qG F G hlen hVF hVG hmass hpt
    cases F with
    | nil =>
      rw [segMass]
      exact stepInt_nonneg S c hc _ _
    | cons sF F' =>
      cases G with
      | nil =>
        rw [hmass, segMass]
        exact stepInt_nonneg S c hc _ _
      | cons sG G' =>
        rcases sF with ⟨x, y, a⟩
        rcases sG with ⟨u, v, b⟩
        cases hVF with
        | cons hpx hxy ha hVF' =>
          cases hVG with
          | cons hpu huv hb hVG' =>
            let mF := a * (y - x)
            let mG := b * (v - u)
            have hmF_pos : 0 < mF := mul_pos ha (sub_pos.mpr hxy)
            have hmG_pos : 0 < mG := mul_pos hb (sub_pos.mpr huv)
            have hyq : y ≤ qF := hVF'.le
            have hvq : v ≤ qG := hVG'.le
            by_cases hle : mF ≤ mG
            · -- Peel off sF completely, split sG at u' = u + mF / b
              let u' := u + mF / b
              have hu_lt : u < u' := by
                have : 0 < mF / b := div_pos hmF_pos hb
                linarith
              have hu'_le : u' ≤ v := by
                have h1 : mF / b ≤ v - u := (div_le_iff₀ hb).mpr (by dsimp [mG] at hle; linarith)
                linarith
              let mid := (y + u') / 2
              have hp_le : (pF + pG) / 2 ≤ (x + u) / 2 := by linarith
              have hstart_le : (x + u) / 2 ≤ mid := by dsimp only [mid]; linarith
              have hmid_le : mid ≤ (qF + qG) / 2 := by dsimp only [mid]; linarith
              have hseg1 : mF ≤ stepInt S c ((x + u) / 2) mid := by
                have hbound : ∀ k : ℤ, (x + u) / 2 < (k : ℝ) + 1 → (k : ℝ) < mid →
                    k ∈ S ∧ Real.sqrt (a * b) ≤ c k := by
                  intro k h1 h2
                  have h2' : (k : ℝ) < (y + v) / 2 := by dsimp only [mid] at h2; linarith
                  exact hpt (x, y, a) (List.mem_cons.mpr (Or.inl rfl)) (u, v, b) (List.mem_cons.mpr (Or.inl rfl))
                    k h1 h2'
                have hst := stepInt_ge_mul_sub S c hc ((x + u) / 2) mid (Real.sqrt (a * b))
                  hstart_le (Real.sqrt_nonneg _) hbound
                have ham := am_gm_step mF a b hmF_pos.le ha hb
                have hlen_eq : mid - (x + u) / 2 = (mF / a + mF / b) / 2 := by
                  have hya : y - x = mF / a := by
                    dsimp [mF]; field_simp
                  have hub : u' - u = mF / b := by dsimp [u']; ring
                  dsimp [mid]; linarith
                rw [hlen_eq] at hst
                linarith
              have hseg2 : segMass F' ≤ stepInt S c mid ((qF + qG) / 2) := by
                by_cases huv' : u' = v
                · have hVG'' : ValidSegs u' qG G' := by rwa [huv']
                  have hm' : segMass F' = segMass G' := by
                    have hmeq : mF = mG := by
                      have : mF / b = v - u := by dsimp [u'] at huv'; linarith
                      have : mF = b * (v - u) := by
                        have := (div_eq_iff hb.ne').mp this
                        linarith
                      exact this
                    simp only [segMass] at hmass
                    linarith
                  have hlen' : F'.length + G'.length ≤ n := by
                    simp only [List.length_cons] at hlen; omega
                  exact ih y qF u' qG F' G' hlen' hVF' hVG'' hm' fun tF htF tG htG k h1 h2 =>
                    hpt tF (List.mem_cons_of_mem _ htF) tG (List.mem_cons_of_mem _ htG) k h1 h2
                · have hu'_lt_v : u' < v := lt_of_le_of_ne hu'_le huv'
                  have hVG'' : ValidSegs u' qG ((u', v, b) :: G') :=
                    ValidSegs.cons le_rfl hu'_lt_v hb hVG'
                  have hm' : segMass F' = segMass ((u', v, b) :: G') := by
                    simp only [segMass] at hmass ⊢
                    have hb_mul : b * (v - u') = mG - mF := by
                      dsimp [u', mG]; field_simp; ring
                    linarith
                  have hlen' : F'.length + ((u', v, b) :: G').length ≤ n := by
                    simp only [List.length_cons] at hlen ⊢; omega
                  refine ih y qF u' qG F' ((u', v, b) :: G') hlen' hVF' hVG'' hm' ?_
                  intro tF htF tG htG k h1 h2
                  rcases List.mem_cons.mp htG with rfl | htG'
                  · have h1' : (tF.1 + u) / 2 < (k : ℝ) + 1 := by linarith
                    exact hpt tF (List.mem_cons_of_mem _ htF) (u, v, b) (List.mem_cons.mpr (Or.inl rfl))
                      k h1' h2
                  · exact hpt tF (List.mem_cons_of_mem _ htF) tG (List.mem_cons_of_mem _ htG')
                      k h1 h2
              have hcomb : segMass ((x, y, a) :: F') ≤ stepInt S c ((x + u) / 2) ((qF + qG) / 2) := by
                rw [← stepInt_add S c ((x + u) / 2) mid ((qF + qG) / 2) hstart_le hmid_le]
                simp only [segMass]
                linarith
              exact hcomb.trans (stepInt_mono S c hc _ _ _ _ hp_le (hstart_le.trans hmid_le) le_rfl)
            · -- Symmetric: mG < mF, peel off sG completely, split sF at x' = x + mG / a
              push Not at hle
              let x' := x + mG / a
              have hx_lt : x < x' := by
                have : 0 < mG / a := div_pos hmG_pos ha
                linarith
              have hx'_lt : x' < y := by
                have h1 : mG / a < y - x := (div_lt_iff₀ ha).mpr (by dsimp [mF] at hle; linarith)
                linarith
              let mid := (x' + v) / 2
              have hp_le : (pF + pG) / 2 ≤ (x + u) / 2 := by linarith
              have hstart_le : (x + u) / 2 ≤ mid := by dsimp only [mid]; linarith
              have hmid_le : mid ≤ (qF + qG) / 2 := by dsimp only [mid]; linarith
              have hseg1 : mG ≤ stepInt S c ((x + u) / 2) mid := by
                have hbound : ∀ k : ℤ, (x + u) / 2 < (k : ℝ) + 1 → (k : ℝ) < mid →
                    k ∈ S ∧ Real.sqrt (a * b) ≤ c k := by
                  intro k h1 h2
                  have h2' : (k : ℝ) < (y + v) / 2 := by dsimp only [mid] at h2; linarith
                  exact hpt (x, y, a) (List.mem_cons.mpr (Or.inl rfl)) (u, v, b) (List.mem_cons.mpr (Or.inl rfl))
                    k h1 h2'
                have hst := stepInt_ge_mul_sub S c hc ((x + u) / 2) mid (Real.sqrt (a * b))
                  hstart_le (Real.sqrt_nonneg _) hbound
                have ham := am_gm_step mG a b hmG_pos.le ha hb
                have hlen_eq : mid - (x + u) / 2 = (mG / a + mG / b) / 2 := by
                  have hxa : x' - x = mG / a := by dsimp [x']; ring
                  have hvb : v - u = mG / b := by dsimp [mG]; field_simp
                  dsimp [mid]; linarith
                rw [hlen_eq] at hst
                linarith
              have hVF'' : ValidSegs x' qF ((x', y, a) :: F') :=
                ValidSegs.cons le_rfl hx'_lt ha hVF'
              have hm' : segMass ((x', y, a) :: F') = segMass G' := by
                simp only [segMass] at hmass ⊢
                have ha_mul : a * (y - x') = mF - mG := by
                  dsimp [x', mF]; field_simp; ring
                linarith
              have hlen' : ((x', y, a) :: F').length + G'.length ≤ n := by
                simp only [List.length_cons] at hlen ⊢; omega
              have hseg2 : segMass ((x', y, a) :: F') ≤ stepInt S c mid ((qF + qG) / 2) := by
                refine ih x' qF v qG ((x', y, a) :: F') G' hlen' hVF'' hVG' hm' ?_
                intro tF htF tG htG k h1 h2
                rcases List.mem_cons.mp htF with rfl | htF'
                · have h1' : (x + tG.1) / 2 < (k : ℝ) + 1 := by linarith
                  exact hpt (x, y, a) (List.mem_cons.mpr (Or.inl rfl)) tG (List.mem_cons_of_mem _ htG)
                    k h1' h2
                · exact hpt tF (List.mem_cons_of_mem _ htF') tG (List.mem_cons_of_mem _ htG)
                    k h1 h2
              have hcomb : segMass ((x, y, a) :: F') ≤ stepInt S c ((x + u) / 2) ((qF + qG) / 2) := by
                rw [← stepInt_add S c ((x + u) / 2) mid ((qF + qG) / 2) hstart_le hmid_le]
                simp only [segMass] at hseg2 ⊢
                have ha_mul : a * (y - x') = mF - mG := by
                  dsimp [x', mF]; field_simp; ring
                linarith
              exact hcomb.trans (stepInt_mono S c hc _ _ _ _ hp_le (hstart_le.trans hmid_le) le_rfl)

private def buildSegs (f : ℤ → ℝ) : List ℤ → List (ℝ × ℝ × ℝ)
  | [] => []
  | i :: rest =>
    if 0 < f i then ((i : ℝ), (i : ℝ) + 1, f i) :: buildSegs f rest
    else buildSegs f rest

private lemma buildSegs_valid (f : ℤ → ℝ) :
    ∀ (L : List ℤ) (p q : ℝ),
      L.Pairwise (· < ·) →
      (∀ i ∈ L, p ≤ (i : ℝ) ∧ (i : ℝ) + 1 ≤ q) →
      p ≤ q →
      ValidSegs p q (buildSegs f L) := by
  intro L
  induction L with
  | nil =>
    intro p q _ _ hpq
    exact ValidSegs.nil hpq
  | cons i rest ih =>
    intro p q hpw hbd hpq
    rw [List.pairwise_cons] at hpw
    have hi := hbd i (List.mem_cons.mpr (Or.inl rfl))
    unfold buildSegs
    split_ifs with hf
    · refine ValidSegs.cons hi.1 (by linarith) hf ?_
      refine ih ((i : ℝ) + 1) q hpw.2 ?_ hi.2
      intro j hj
      have hij : i < j := hpw.1 j hj
      have hjbd := hbd j (List.mem_cons_of_mem _ hj)
      have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hij)
      exact ⟨hij', hjbd.2⟩
    · exact ih p q hpw.2 (fun j hj => hbd j (List.mem_cons_of_mem _ hj)) hpq

private lemma buildSegs_mass (f : ℤ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∀ L : List ℤ, segMass (buildSegs f L) = (L.map f).sum := by
  intro L
  induction L with
  | nil => simp [buildSegs, segMass]
  | cons i rest ih =>
    unfold buildSegs
    split_ifs with hpos
    · simp only [segMass, List.map_cons, List.sum_cons, ih]
      ring
    · have h0 : f i = 0 := le_antisymm (not_lt.mp hpos) (hf i)
      simp [ih, h0]

private lemma buildSegs_mem (f : ℤ → ℝ) :
    ∀ (L : List ℤ) (s : ℝ × ℝ × ℝ),
      s ∈ buildSegs f L → ∃ i ∈ L, s = ((i : ℝ), (i : ℝ) + 1, f i) := by
  intro L
  induction L with
  | nil => simp [buildSegs]
  | cons i rest ih =>
    intro s hs
    unfold buildSegs at hs
    split_ifs at hs with hpos
    · rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih s hs'
        exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ih s hs
      exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩

private lemma int_mem_Icc_of_mid_close {M : ℕ} {i j k : ℤ}
    (hi : i ∈ Finset.Icc (-(M : ℤ)) M) (hj : j ∈ Finset.Icc (-(M : ℤ)) M)
    (hk : |i + j - 2 * k| ≤ 1) :
    k ∈ Finset.Icc (-(M : ℤ)) M := by
  rw [Finset.mem_Icc] at hi hj ⊢
  rw [abs_le] at hk
  omega

private lemma discrete_PL_1d (M : ℕ) (f g h : ℤ → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) (hh : ∀ k, 0 ≤ h k)
    (hpl : ∀ i ∈ Finset.Icc (-(M : ℤ)) M, ∀ j ∈ Finset.Icc (-(M : ℤ)) M,
      ∀ k : ℤ, |i + j - 2 * k| ≤ 1 → Real.sqrt (f i * g j) ≤ h k) :
    Real.sqrt ((∑ i ∈ Finset.Icc (-(M : ℤ)) M, f i) *
               (∑ j ∈ Finset.Icc (-(M : ℤ)) M, g j)) ≤
      ∑ k ∈ Finset.Icc (-(M : ℤ)) M, h k := by
  let I := Finset.Icc (-(M : ℤ)) M
  let A := ∑ i ∈ I, f i
  let B := ∑ j ∈ I, g j
  change Real.sqrt (A * B) ≤ ∑ k ∈ I, h k
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hf i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => hg j
  by_cases hA : A = 0
  · rw [hA, zero_mul, Real.sqrt_zero]
    exact Finset.sum_nonneg fun k _ => hh k
  by_cases hB : B = 0
  · rw [hB, mul_zero, Real.sqrt_zero]
    exact Finset.sum_nonneg fun k _ => hh k
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
  let f' : ℤ → ℝ := fun i => f i / A
  let g' : ℤ → ℝ := fun j => g j / B
  let h' : ℤ → ℝ := fun k => h k / Real.sqrt (A * B)
  have hf' : ∀ i, 0 ≤ f' i := fun i => div_nonneg (hf i) hApos.le
  have hg' : ∀ j, 0 ≤ g' j := fun j => div_nonneg (hg j) hBpos.le
  have hh' : ∀ k, 0 ≤ h' k := fun k => div_nonneg (hh k) (Real.sqrt_nonneg _)
  let L : List ℤ := (List.range (2 * M + 1)).map (fun (n : ℕ) => (n : ℤ) - (M : ℤ))
  have hL_pw : L.Pairwise (· < ·) := by
    dsimp [L]
    rw [List.pairwise_map]
    refine List.Pairwise.imp (fun {a b : ℕ} (hab : a < b) => by omega) List.pairwise_lt_range
  have hL_nodup : L.Nodup := hL_pw.imp ne_of_lt
  have hL_mem : ∀ i : ℤ, i ∈ L ↔ i ∈ I := by
    intro i
    simp only [L, I, List.mem_map, List.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨n, hn, rfl⟩; omega
    · intro ⟨h1, h2⟩
      exact ⟨(i + M).toNat, by omega, by omega⟩
  have hL_toFinset : L.toFinset = I := by
    ext i; rw [List.mem_toFinset, hL_mem]
  have hlist_sum : ∀ (K : List ℤ) (φ : ℤ → ℝ), K.Nodup → (K.map φ).sum = ∑ i ∈ K.toFinset, φ i := by
    intro K φ
    induction K with
    | nil => intro _; simp
    | cons a t ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.sum_cons, List.toFinset_cons,
          Finset.sum_insert (by rw [List.mem_toFinset]; exact hnd.1), ih hnd.2]
  have hL_sum : ∀ φ : ℤ → ℝ, (L.map φ).sum = ∑ i ∈ I, φ i := by
    intro φ
    rw [← hL_toFinset, hlist_sum L φ hL_nodup]
  have hL_bd : ∀ i ∈ L, (-(M : ℝ)) ≤ (i : ℝ) ∧ (i : ℝ) + 1 ≤ (M : ℝ) + 1 := by
    intro i hi
    have hI := (hL_mem i).mp hi
    rw [Finset.mem_Icc] at hI
    constructor <;> [exact_mod_cast hI.1; exact_mod_cast (by omega : i + 1 ≤ (M : ℤ) + 1)]
  have hpq : (-(M : ℝ)) ≤ (M : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  let F := buildSegs f' L
  let G := buildSegs g' L
  have hVF : ValidSegs (-(M : ℝ)) ((M : ℝ) + 1) F := buildSegs_valid f' L _ _ hL_pw hL_bd hpq
  have hVG : ValidSegs (-(M : ℝ)) ((M : ℝ) + 1) G := buildSegs_valid g' L _ _ hL_pw hL_bd hpq
  have hmassF : segMass F = 1 := by
    rw [buildSegs_mass f' hf' L, hL_sum]
    simp [f', ← Finset.sum_div, A, div_self hApos.ne']
  have hmassG : segMass G = 1 := by
    rw [buildSegs_mass g' hg' L, hL_sum]
    simp [g', ← Finset.sum_div, B, div_self hBpos.ne']
  have hpt : ∀ sF ∈ F, ∀ sG ∈ G, ∀ k : ℤ,
      (sF.1 + sG.1) / 2 < (k : ℝ) + 1 → (k : ℝ) < (sF.2.1 + sG.2.1) / 2 →
      k ∈ I ∧ Real.sqrt (sF.2.2 * sG.2.2) ≤ h' k := by
    intro sF hsF sG hsG k h1 h2
    obtain ⟨i, hiL, rfl⟩ := buildSegs_mem f' L sF hsF
    obtain ⟨j, hjL, rfl⟩ := buildSegs_mem g' L sG hsG
    have hiI : i ∈ I := (hL_mem i).mp hiL
    have hjI : j ∈ I := (hL_mem j).mp hjL
    have h1Z : i + j < 2 * k + 2 := by
      have : ((i + j : ℤ) : ℝ) < ((2 * k + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    have h2Z : 2 * k < i + j + 2 := by
      have : ((2 * k : ℤ) : ℝ) < ((i + j + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    have habs : |i + j - 2 * k| ≤ 1 := by
      rw [abs_le]; omega
    refine ⟨int_mem_Icc_of_mid_close hiI hjI habs, ?_⟩
    have hplk := hpl i hiI j hjI k habs
    dsimp only [f', g', h']
    have hdiv : f i / A * (g j / B) = (f i * g j) / (A * B) := by ring
    rw [hdiv, Real.sqrt_div (mul_nonneg (hf i) (hg j))]
    exact div_le_div_of_nonneg_right hplk (Real.sqrt_nonneg _)
  have hstep := step_pl_aux I h' hh' (F.length + G.length) _ _ _ _ F G le_rfl hVF hVG
    (hmassF.trans hmassG.symm) hpt
  rw [hmassF] at hstep
  have hle_sum : stepInt I h' ((-(M : ℝ) + -(M : ℝ)) / 2) (((M : ℝ) + 1 + ((M : ℝ) + 1)) / 2) ≤
      ∑ k ∈ I, h' k :=
    stepInt_le_sum I h' hh' _ _ (by linarith)
  have h1 : 1 ≤ (∑ k ∈ I, h k) / Real.sqrt (A * B) := by
    have : ∑ k ∈ I, h' k = (∑ k ∈ I, h k) / Real.sqrt (A * B) := by
      simp [h', ← Finset.sum_div]
    linarith
  exact (one_le_div (Real.sqrt_pos.mpr (mul_pos hApos hBpos))).mp h1

private def box (d M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) M)

private lemma mem_box_iff {d M : ℕ} {x : Fin d → ℤ} :
    x ∈ box d M ↔ ∀ r : Fin d, -(M : ℤ) ≤ x r ∧ x r ≤ (M : ℤ) := by
  simp [box, Fintype.mem_piFinset, Finset.mem_Icc]

private lemma sum_box_succ {d M : ℕ} (φ : (Fin (d + 1) → ℤ) → ℝ) :
    ∑ x ∈ box (d + 1) M, φ x =
      ∑ a ∈ Finset.Icc (-(M : ℤ)) M, ∑ x' ∈ box d M, φ (Fin.cons a x') := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun x _ => (x 0, Fin.tail x)) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_product, Finset.mem_Icc, mem_box_iff]
    rw [mem_box_iff] at hx
    exact ⟨hx 0, fun r => hx r.succ⟩
  · intro x₁ _ x₂ _ h
    have h0 : x₁ 0 = x₂ 0 := congrArg Prod.fst h
    have ht : Fin.tail x₁ = Fin.tail x₂ := congrArg Prod.snd h
    ext r
    refine Fin.cases h0 (fun i => congrFun ht i) r
  · intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, mem_box_iff] at hp
    refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
    · rw [mem_box_iff]
      intro r
      exact Fin.cases hp.1 hp.2 r
    · ext
      · simp
      · simp
  · intro x _
    congr 1
    exact (Fin.cons_self_tail x).symm

private lemma discrete_PL_nd (d M : ℕ) :
    ∀ (f g h : (Fin d → ℤ) → ℝ),
      (∀ x, 0 ≤ f x) → (∀ y, 0 ≤ g y) → (∀ z, 0 ≤ h z) →
      (∀ x ∈ box d M, ∀ y ∈ box d M, ∀ z ∈ box d M,
        (∀ r : Fin d, |x r + y r - 2 * z r| ≤ 1) → Real.sqrt (f x * g y) ≤ h z) →
      Real.sqrt ((∑ x ∈ box d M, f x) * (∑ y ∈ box d M, g y)) ≤ ∑ z ∈ box d M, h z := by
  induction d with
  | zero =>
    intro f g h _ _ _ hpl
    have hbox0 : box 0 M = {Fin.elim0} := by
      ext x
      simp only [mem_box_iff, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ r => Fin.elim0 r⟩
    rw [hbox0, Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton]
    have hmem : Fin.elim0 ∈ box 0 M := by rw [hbox0]; simp
    exact hpl Fin.elim0 hmem Fin.elim0 hmem Fin.elim0 hmem (fun r => Fin.elim0 r)
  | succ d ih =>
    intro f g h hf hg hh hpl
    let F : ℤ → ℝ := fun a => ∑ x' ∈ box d M, f (Fin.cons a x')
    let G : ℤ → ℝ := fun b => ∑ y' ∈ box d M, g (Fin.cons b y')
    let H : ℤ → ℝ := fun c => ∑ z' ∈ box d M, h (Fin.cons c z')
    have hF : ∀ a, 0 ≤ F a := fun a => Finset.sum_nonneg fun x' _ => hf _
    have hG : ∀ b, 0 ≤ G b := fun b => Finset.sum_nonneg fun y' _ => hg _
    have hH : ∀ c, 0 ≤ H c := fun c => Finset.sum_nonneg fun z' _ => hh _
    have hpl1 : ∀ a ∈ Finset.Icc (-(M : ℤ)) M, ∀ b ∈ Finset.Icc (-(M : ℤ)) M,
        ∀ c : ℤ, |a + b - 2 * c| ≤ 1 → Real.sqrt (F a * G b) ≤ H c := by
      intro a ha b hb c habc
      have hc : c ∈ Finset.Icc (-(M : ℤ)) M := int_mem_Icc_of_mid_close ha hb habc
      refine ih (fun x' => f (Fin.cons a x')) (fun y' => g (Fin.cons b y'))
        (fun z' => h (Fin.cons c z')) (fun _ => hf _) (fun _ => hg _) (fun _ => hh _) ?_
      intro x' hx' y' hy' z' hz' hclose
      have hx : Fin.cons a x' ∈ box (d + 1) M := by
        rw [mem_box_iff]; intro r
        exact Fin.cases (Finset.mem_Icc.mp ha) (mem_box_iff.mp hx') r
      have hy : Fin.cons b y' ∈ box (d + 1) M := by
        rw [mem_box_iff]; intro r
        exact Fin.cases (Finset.mem_Icc.mp hb) (mem_box_iff.mp hy') r
      have hz : Fin.cons c z' ∈ box (d + 1) M := by
        rw [mem_box_iff]; intro r
        exact Fin.cases (Finset.mem_Icc.mp hc) (mem_box_iff.mp hz') r
      refine hpl _ hx _ hy _ hz fun r => ?_
      exact Fin.cases habc hclose r
    rw [sum_box_succ f, sum_box_succ g, sum_box_succ h]
    exact discrete_PL_1d M F G H hF hG hH hpl1

/- ### Module 3B: Truncated discrete Gaussian, moments, Chebyshev, Fejér anti-concentration -/

private lemma cos_bounds {a : ℝ} (ha : |a| ≤ 1) :
    1 / 2 ≤ Real.cos a ∧ Real.cos a ≤ 1 - a ^ 2 / 3 := by
  constructor
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := a)
    have h2 : a ^ 2 ≤ 1 := by nlinarith [abs_le.mp ha]
    linarith
  · have hcos_abs : Real.cos a = Real.cos |a| := by
      rcases le_total 0 a with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, Real.cos_neg]
    rw [hcos_abs]
    have ha0 : 0 ≤ |a| := abs_nonneg a
    by_cases h0 : |a| = 0
    · rw [h0, Real.cos_zero]
      have : a = 0 := abs_eq_zero.mp h0
      rw [this]; norm_num
    · have hpos : 0 < |a| / 2 := by positivity
      have hsin := Real.sin_gt_sub_cube hpos
      have hsin_ge : (5 / 6) * (|a| / 2) ≤ Real.sin (|a| / 2) := by
        have hle1 : |a| ^ 2 ≤ 1 := by nlinarith [abs_nonneg a]
        nlinarith
      have hdouble : Real.cos |a| = 1 - 2 * Real.sin (|a| / 2) ^ 2 := by
        have h2 : Real.cos (2 * (|a| / 2)) = 1 - 2 * Real.sin (|a| / 2) ^ 2 := by
          rw [Real.cos_two_mul]
          nlinarith [Real.sin_sq_add_cos_sq (|a| / 2)]
        have h3 : 2 * (|a| / 2) = |a| := by ring
        rwa [h3] at h2
      rw [hdouble]
      have hsq : ((5 / 6) * (|a| / 2)) ^ 2 ≤ Real.sin (|a| / 2) ^ 2 := by
        nlinarith [Real.sin_gt_sub_cube hpos]
      have habs_sq : |a| ^ 2 = a ^ 2 := sq_abs a
      nlinarith

private lemma exp_neg_half_ge : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
  have h1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h3 : Real.exp (1 / 2) < 2 := by
    nlinarith [Real.exp_pos (1 / 2)]
  calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    _ ≤ (Real.exp (1 / 2))⁻¹ := inv_anti₀ (Real.exp_pos (1 / 2)) h3.le
    _ = Real.exp (-1 / 2) := by rw [← Real.exp_neg]; congr 1; ring

private lemma sum_sq_Icc_ge (n : ℕ) :
    (n : ℝ) ^ 3 / 3 ≤ ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) =
        insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : ((n + 1 : ℕ) : ℤ) ∉ Finset.Icc (1 : ℤ) (n : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

private def w1 (σ : ℕ) (k : ℤ) : ℝ :=
  Real.exp (-((k : ℝ) ^ 2) / (2 * (σ : ℝ) ^ 2))

private def Z1 (σ : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, w1 σ k

private def p1 (σ : ℕ) (k : ℤ) : ℝ :=
  w1 σ k / Z1 σ

private def v1 (σ : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ k * (k : ℝ) ^ 2

private lemma w1_pos (σ : ℕ) (k : ℤ) : 0 < w1 σ k := Real.exp_pos _

private lemma w1_neg (σ : ℕ) (k : ℤ) : w1 σ (-k) = w1 σ k := by
  simp [w1]

private lemma Z1_pos (σ : ℕ) : 0 < Z1 σ := by
  unfold Z1
  refine Finset.sum_pos (fun k _ => w1_pos σ k) ?_
  exact ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

private lemma p1_nonneg (σ : ℕ) (k : ℤ) : 0 ≤ p1 σ k :=
  div_nonneg (w1_pos σ k).le (Z1_pos σ).le

private lemma p1_neg (σ : ℕ) (k : ℤ) : p1 σ (-k) = p1 σ k := by
  simp [p1, w1_neg]

private lemma sum_p1 (σ : ℕ) : ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ k = 1 := by
  simp only [p1, ← Finset.sum_div]
  exact div_self (Z1_pos σ).ne'

private lemma v1_bounds (σ : ℕ) (hσ : 1 ≤ σ) :
    (σ : ℝ) ^ 2 / 9 ≤ v1 σ ∧ v1 σ ≤ (σ : ℝ) ^ 2 ∧
    ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ k * (k : ℝ) ^ 4 ≤ (σ : ℝ) ^ 4 := by
  let I := Finset.Icc (-(σ : ℤ)) σ
  have hσR : (1 : ℝ) ≤ (σ : ℝ) := Nat.one_le_cast.mpr hσ
  have hσpos : (0 : ℝ) < (σ : ℝ) := by linarith
  have hw1_ge : ∀ k ∈ I, (1 / 2 : ℝ) ≤ w1 σ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk2 : (k : ℝ) ^ 2 ≤ (σ : ℝ) ^ 2 := by
      have h1 : -(σ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      have h2 : (k : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hk.2
      nlinarith
    have hexp : (-1 / 2 : ℝ) ≤ -((k : ℝ) ^ 2) / (2 * (σ : ℝ) ^ 2) := by
      have hden : (0 : ℝ) < 2 * (σ : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ (by norm_num) hden]
      nlinarith
    exact exp_neg_half_ge.trans (Real.exp_le_exp.mpr hexp)
  have hw1_le : ∀ k ∈ I, w1 σ k ≤ 1 := by
    intro k _
    unfold w1
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hZ1_le : Z1 σ ≤ 3 * (σ : ℝ) := by
    have hcard : (I.card : ℝ) = 2 * (σ : ℝ) + 1 := by
      have hc : I.card = 2 * σ + 1 := by
        dsimp [I]
        rw [Int.card_Icc]
        omega
      exact_mod_cast hc
    calc Z1 σ = ∑ k ∈ I, w1 σ k := rfl
      _ ≤ ∑ _k ∈ I, (1 : ℝ) := Finset.sum_le_sum hw1_le
      _ = (I.card : ℝ) := by simp
      _ = 2 * (σ : ℝ) + 1 := hcard
      _ ≤ 3 * (σ : ℝ) := by linarith
  have hnum_ge : (σ : ℝ) ^ 3 / 3 ≤ ∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2 := by
    have h1 : (1 / 2 : ℝ) * (∑ k ∈ I, (k : ℝ) ^ 2) ≤ ∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hw1_ge k hk) (sq_nonneg _)
    let Ipos := Finset.Icc (1 : ℤ) (σ : ℤ)
    let Ineg := Finset.Icc (-(σ : ℤ)) (-1 : ℤ)
    have hdisj : Disjoint Ipos Ineg := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      rw [Finset.mem_Icc] at hk1 hk2; omega
    have hsub : Ipos ∪ Ineg ⊆ I := by
      intro k hk
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]; omega
    have hneg_eq : ∑ k ∈ Ineg, (k : ℝ) ^ 2 = ∑ k ∈ Ipos, (k : ℝ) ^ 2 := by
      refine Finset.sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
      · intro a _ b _ h; omega
      · intro k hk; exact ⟨-k, by rw [Finset.mem_Icc] at hk ⊢; omega, neg_neg k⟩
      · intro k _; simp
    have hsum2 : (2 / 3 : ℝ) * (σ : ℝ) ^ 3 ≤ ∑ k ∈ I, (k : ℝ) ^ 2 := by
      calc (2 / 3 : ℝ) * (σ : ℝ) ^ 3
          = (σ : ℝ) ^ 3 / 3 + (σ : ℝ) ^ 3 / 3 := by ring
        _ ≤ (∑ k ∈ Ipos, (k : ℝ) ^ 2) + (∑ k ∈ Ipos, (k : ℝ) ^ 2) :=
            add_le_add (sum_sq_Icc_ge σ) (sum_sq_Icc_ge σ)
        _ = (∑ k ∈ Ipos, (k : ℝ) ^ 2) + (∑ k ∈ Ineg, (k : ℝ) ^ 2) := by rw [hneg_eq]
        _ = ∑ k ∈ Ipos ∪ Ineg, (k : ℝ) ^ 2 := (Finset.sum_union hdisj).symm
        _ ≤ ∑ k ∈ I, (k : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hv1_eq : v1 σ = (∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2) / Z1 σ := by
      simp only [v1, p1, div_mul_eq_mul_div, ← Finset.sum_div]; rfl
    rw [hv1_eq, le_div_iff₀ (Z1_pos σ)]
    calc (σ : ℝ) ^ 2 / 9 * Z1 σ
        ≤ (σ : ℝ) ^ 2 / 9 * (3 * (σ : ℝ)) :=
          mul_le_mul_of_nonneg_left hZ1_le (by positivity)
      _ = (σ : ℝ) ^ 3 / 3 := by ring
      _ ≤ ∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2 := hnum_ge
  · calc v1 σ = ∑ k ∈ I, p1 σ k * (k : ℝ) ^ 2 := rfl
      _ ≤ ∑ k ∈ I, p1 σ k * (σ : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (p1_nonneg σ k)
          rw [Finset.mem_Icc] at hk
          have h1 : -(σ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          have h2 : (k : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hk.2
          nlinarith
      _ = (∑ k ∈ I, p1 σ k) * (σ : ℝ) ^ 2 := by rw [← Finset.sum_mul]
      _ = (σ : ℝ) ^ 2 := by rw [sum_p1 σ, one_mul]
  · calc ∑ k ∈ I, p1 σ k * (k : ℝ) ^ 4
        ≤ ∑ k ∈ I, p1 σ k * (σ : ℝ) ^ 4 := by
          refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (p1_nonneg σ k)
          rw [Finset.mem_Icc] at hk
          have h1 : -(σ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          have h2 : (k : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hk.2
          have hsq : (k : ℝ) ^ 2 ≤ (σ : ℝ) ^ 2 := by nlinarith
          nlinarith [sq_nonneg (k : ℝ)]
      _ = (∑ k ∈ I, p1 σ k) * (σ : ℝ) ^ 4 := by rw [← Finset.sum_mul]
      _ = (σ : ℝ) ^ 4 := by rw [sum_p1 σ, one_mul]

private def pd (d σ : ℕ) (x : Fin d → ℤ) : ℝ :=
  ∏ r : Fin d, p1 σ (x r)

private lemma pd_nonneg (d σ : ℕ) (x : Fin d → ℤ) : 0 ≤ pd d σ x :=
  Finset.prod_nonneg fun _ _ => p1_nonneg σ _

private lemma pd_neg (d σ : ℕ) (x : Fin d → ℤ) : pd d σ (-x) = pd d σ x := by
  simp [pd, p1_neg]

private lemma pd_eq_exp_div (d σ : ℕ) (x : Fin d → ℤ) :
    pd d σ x = Real.exp (-normSq x / (2 * (σ : ℝ) ^ 2)) / (Z1 σ) ^ d := by
  unfold pd p1 w1 normSq
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

-- Direct elementary proof of product factorization over `box d σ` by induction on `d`
private lemma sum_box_prod (d σ : ℕ) (f : Fin d → ℤ → ℝ) :
    ∑ x ∈ box d σ, (∏ r : Fin d, f r (x r)) =
      ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, f r a := by
  induction d with
  | zero =>
    have hbox0 : box 0 σ = {Fin.elim0} := by
      ext x
      simp only [mem_box_iff, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ r => Fin.elim0 r⟩
    simp [hbox0]
  | succ d ih =>
    rw [sum_box_succ]
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ih (fun r => f r.succ)]

private lemma sum_box_pd (d σ : ℕ) : ∑ x ∈ box d σ, pd d σ x = 1 := by
  unfold pd
  rw [sum_box_prod]
  simp [sum_p1]

private lemma sum_box_single (d σ : ℕ) (r : Fin d) (g : ℤ → ℝ) :
    ∑ x ∈ box d σ, pd d σ x * g (x r) = ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g a := by
  have hrew : ∀ x : Fin d → ℤ,
      pd d σ x * g (x r) = ∏ i : Fin d, (p1 σ (x i) * if i = r then g (x i) else 1) := by
    intro x
    unfold pd
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp_rw [hrew]
  rw [sum_box_prod d σ (fun i a => p1 σ a * if i = r then g a else 1)]
  have h1 : ∀ i : Fin d,
      (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * if i = r then g a else 1) =
        if i = r then ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g a else 1 := by
    intro i
    by_cases h : i = r
    · simp [h]
    · simp [h, sum_p1]
  simp_rw [h1]
  rw [Finset.prod_ite_eq']
  simp

private lemma sum_box_pair (d σ : ℕ) (r s : Fin d) (hrs : r ≠ s) (g₁ g₂ : ℤ → ℝ) :
    ∑ x ∈ box d σ, pd d σ x * (g₁ (x r) * g₂ (x s)) =
      (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g₁ a) *
      (∑ b ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ b * g₂ b) := by
  have hrew : ∀ x : Fin d → ℤ,
      pd d σ x * (g₁ (x r) * g₂ (x s)) =
        ∏ i : Fin d, (p1 σ (x i) * (if i = r then g₁ (x i) else 1) *
          (if i = s then g₂ (x i) else 1)) := by
    intro x
    unfold pd
    simp_rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp [mul_assoc]
  simp_rw [hrew]
  rw [sum_box_prod d σ (fun i a => p1 σ a * (if i = r then g₁ a else 1) * (if i = s then g₂ a else 1))]
  have h1 : ∀ i : Fin d,
      (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
        p1 σ a * (if i = r then g₁ a else 1) * (if i = s then g₂ a else 1)) =
      (if i = r then ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g₁ a else 1) *
      (if i = s then ∑ b ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ b * g₂ b else 1) := by
    intro i
    by_cases hr : i = r
    · subst hr
      simp [hrs]
    · by_cases hs : i = s
      · subst hs
        simp [hrs.symm]
      · simp [hr, hs, sum_p1]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp

private lemma chebyshev_shell (d σ : ℕ) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    1 - 324 / (d : ℝ) ≤
      ∑ x ∈ (box d σ).filter (fun x => (d : ℝ) / 2 * v1 σ ≤ normSq x), pd d σ x := by
  let B := box d σ
  let A := B.filter (fun x => (d : ℝ) / 2 * v1 σ ≤ normSq x)
  let Ac := B.filter (fun x => ¬ ((d : ℝ) / 2 * v1 σ ≤ normSq x))
  have hsplit : ∑ x ∈ A, pd d σ x + ∑ x ∈ Ac, pd d σ x = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_box_pd]
  obtain ⟨hv1_lo, _, hm4_hi⟩ := v1_bounds σ hσ
  have hvar : ∑ x ∈ B, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 ≤ (d : ℝ) * (σ : ℝ) ^ 4 := by
    let f : ℤ → ℝ := fun a => (a : ℝ) ^ 2 - v1 σ
    have hmean0 : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * f a = 0 := by
      simp only [f, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_p1, one_mul]
      unfold v1; ring
    have hsq_mean : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (f a) ^ 2 ≤ (σ : ℝ) ^ 4 := by
      have h1 : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (f a) ^ 2 =
          (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (a : ℝ) ^ 4) - (v1 σ) ^ 2 := by
        have hterm : ∀ a : ℤ, p1 σ a * (f a) ^ 2 =
            p1 σ a * (a : ℝ) ^ 4 - 2 * v1 σ * (p1 σ a * (a : ℝ) ^ 2) +
            p1 σ a * (v1 σ) ^ 2 := by
          intro a; dsimp [f]; ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, sum_p1, one_mul]
        unfold v1; ring
      rw [h1]
      linarith [sq_nonneg (v1 σ)]
    have hexpand : ∀ x : Fin d → ℤ,
        (normSq x - (d : ℝ) * v1 σ) ^ 2 =
          ∑ r : Fin d, ∑ s : Fin d, f (x r) * f (x s) := by
      intro x
      have h1 : normSq x - (d : ℝ) * v1 σ = ∑ r : Fin d, f (x r) := by
        simp only [normSq, f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [h1, sq, Finset.sum_mul_sum]
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap : ∑ r : Fin d, ∑ x ∈ B, ∑ s : Fin d, pd d σ x * (f (x r) * f (x s)) =
        ∑ r : Fin d, ∑ s : Fin d, ∑ x ∈ B, pd d σ x * (f (x r) * f (x s)) :=
      Finset.sum_congr rfl fun r _ => Finset.sum_comm
    rw [hswap]
    have hdiag : ∀ r : Fin d,
        (∑ s : Fin d, ∑ x ∈ B, pd d σ x * (f (x r) * f (x s))) ≤ (σ : ℝ) ^ 4 := by
      intro r
      have hoff : ∀ s : Fin d, s ≠ r →
          ∑ x ∈ B, pd d σ x * (f (x r) * f (x s)) = 0 := by
        intro s hsr
        rw [sum_box_pair d σ r s hsr.symm f f, hmean0, zero_mul]
      rw [Finset.sum_eq_single r (fun s _ hsr => hoff s hsr) (by simp)]
      have hsq : ∀ x : Fin d → ℤ, pd d σ x * (f (x r) * f (x r)) = pd d σ x * (f (x r)) ^ 2 := by
        intro x; ring
      simp_rw [hsq]
      rw [sum_box_single d σ r (fun a => (f a) ^ 2)]
      exact hsq_mean
    calc ∑ r : Fin d, ∑ s : Fin d, ∑ x ∈ B, pd d σ x * (f (x r) * f (x s))
        ≤ ∑ _r : Fin d, (σ : ℝ) ^ 4 := Finset.sum_le_sum fun r _ => hdiag r
      _ = (d : ℝ) * (σ : ℝ) ^ 4 := by simp
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hσpos : (0 : ℝ) < (σ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hv1_nn : 0 ≤ v1 σ := by nlinarith
  have hAc_bound : ((d : ℝ) / 2 * v1 σ) ^ 2 * (∑ x ∈ Ac, pd d σ x) ≤
      ∑ x ∈ B, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ x ∈ Ac, ((d : ℝ) / 2 * v1 σ) ^ 2 * pd d σ x
        ≤ ∑ x ∈ Ac, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hlt : normSq x < (d : ℝ) / 2 * v1 σ := not_le.mp (Finset.mem_filter.mp hx).2
          have hpos : 0 ≤ (d : ℝ) / 2 * v1 σ := mul_nonneg (by positivity) hv1_nn
          have hsq : ((d : ℝ) / 2 * v1 σ) ^ 2 ≤ (normSq x - (d : ℝ) * v1 σ) ^ 2 := by nlinarith
          nlinarith [pd_nonneg d σ x]
      _ ≤ ∑ x ∈ B, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ B)
            (fun x _ _ => mul_nonneg (pd_nonneg d σ x) (sq_nonneg _))
  have hden_ge : (d : ℝ) ^ 2 * (σ : ℝ) ^ 4 / 324 ≤ ((d : ℝ) / 2 * v1 σ) ^ 2 := by
    have h1 : (d : ℝ) * (σ : ℝ) ^ 2 / 18 ≤ (d : ℝ) / 2 * v1 σ := by nlinarith
    have h2 : 0 ≤ (d : ℝ) * (σ : ℝ) ^ 2 / 18 := by positivity
    nlinarith
  have hAc_le : ∑ x ∈ Ac, pd d σ x ≤ 324 / (d : ℝ) := by
    have hnn : 0 ≤ ∑ x ∈ Ac, pd d σ x := Finset.sum_nonneg fun x _ => pd_nonneg d σ x
    have h1 : (d : ℝ) ^ 2 * (σ : ℝ) ^ 4 / 324 * (∑ x ∈ Ac, pd d σ x) ≤ (d : ℝ) * (σ : ℝ) ^ 4 := by
      calc (d : ℝ) ^ 2 * (σ : ℝ) ^ 4 / 324 * (∑ x ∈ Ac, pd d σ x)
          ≤ ((d : ℝ) / 2 * v1 σ) ^ 2 * (∑ x ∈ Ac, pd d σ x) :=
            mul_le_mul_of_nonneg_right hden_ge hnn
        _ ≤ (d : ℝ) * (σ : ℝ) ^ 4 := hAc_bound.trans hvar
    have hpos4 : (0 : ℝ) < (d : ℝ) * (σ : ℝ) ^ 4 := by positivity
    have h2 : (d : ℝ) / 324 * (∑ x ∈ Ac, pd d σ x) ≤ 1 := by
      have : (d : ℝ) * (σ : ℝ) ^ 4 * ((d : ℝ) / 324 * (∑ x ∈ Ac, pd d σ x)) ≤
          (d : ℝ) * (σ : ℝ) ^ 4 * 1 := by linarith
      exact le_of_mul_le_mul_left this hpos4
    rw [le_div_iff₀ hdpos]
    linarith
  linarith

private lemma sum_Icc_sin_eq_zero (σ : ℕ) (θ : ℝ) :
    ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * Real.sin (θ * (a : ℝ)) = 0 := by
  let I := Finset.Icc (-(σ : ℤ)) σ
  have hneg : ∑ a ∈ I, p1 σ a * Real.sin (θ * (a : ℝ)) =
      -(∑ a ∈ I, p1 σ a * Real.sin (θ * (a : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun a _ => -a) ?_ ?_ ?_ ?_
    · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
    · intro a _ b _ h; omega
    · intro a ha; exact ⟨-a, by rw [Finset.mem_Icc] at ha ⊢; omega, neg_neg a⟩
    · intro a _
      rw [p1_neg]
      simp [Real.sin_neg]
  linarith

private lemma sum_box_cos (d σ : ℕ) (α : ℝ) :
    ∀ x : Fin d → ℤ,
      ∑ y ∈ box d σ, pd d σ y * Real.cos (α * ip x y) =
        ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (α * (x r : ℝ) * (a : ℝ)) := by
  induction d with
  | zero =>
    intro x
    have hbox0 : box 0 σ = {Fin.elim0} := by
      ext y
      simp only [mem_box_iff, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ r => Fin.elim0 r⟩
    simp [hbox0, pd, ip]
  | succ d ih =>
    intro x
    rw [sum_box_succ]
    have hstep : ∀ (a : ℤ) (y' : Fin d → ℤ),
        pd (d + 1) σ (Fin.cons a y') * Real.cos (α * ip x (Fin.cons a y')) =
          p1 σ a * Real.cos (α * (x 0 : ℝ) * (a : ℝ)) *
            (pd d σ y' * Real.cos (α * ip (Fin.tail x) y')) -
          p1 σ a * Real.sin (α * (x 0 : ℝ) * (a : ℝ)) *
            (pd d σ y' * Real.sin (α * ip (Fin.tail x) y')) := by
      intro a y'
      have hpd : pd (d + 1) σ (Fin.cons a y') = p1 σ a * pd d σ y' := by
        simp [pd, Fin.prod_univ_succ]
      have hip : ip x (Fin.cons a y') = (x 0 : ℝ) * (a : ℝ) + ip (Fin.tail x) y' := by
        simp [ip, Fin.sum_univ_succ, Fin.tail]
      rw [hpd, hip, mul_add, Real.cos_add]
      ring
    simp_rw [hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [sum_Icc_sin_eq_zero σ (α * (x 0 : ℝ)), zero_mul, sub_zero]
    rw [ih (Fin.tail x), Fin.prod_univ_succ]
    rfl

private def fejer (N : ℕ) (h s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s)) ^ 2 +
  (∑ j ∈ Finset.range N, Real.sin ((j : ℝ) * h * s)) ^ 2

private lemma fejer_nonneg (N : ℕ) (h s : ℝ) : 0 ≤ fejer N h s :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma fejer_expand (N : ℕ) (h s : ℝ) :
    fejer N h s = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      Real.cos (((j : ℝ) - (k : ℝ)) * h * s) := by
  unfold fejer
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ((j : ℝ) - (k : ℝ)) * h * s = (j : ℝ) * h * s - (k : ℝ) * h * s := by ring
  rw [h1, Real.cos_sub]

private lemma fejer_ge_of_small (N : ℕ) (h E s : ℝ) (hN : 1 ≤ N) (hE : 0 < E)
    (hh : h = 1 / ((N : ℝ) * E)) (hs : |s| ≤ E) :
    (N : ℝ) ^ 2 / 4 ≤ fejer N h s := by
  have hcos_sum : (N : ℝ) / 2 ≤ ∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s) := by
    calc (N : ℝ) / 2 = ∑ _j ∈ Finset.range N, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjlt : (j : ℝ) < (N : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
        have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
        have habs : |(j : ℝ) * h * s| ≤ 1 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg j), hh,
            abs_of_pos (by positivity : (0 : ℝ) < 1 / ((N : ℝ) * E))]
          have h1 : (j : ℝ) * (1 / ((N : ℝ) * E)) * |s| ≤
              (N : ℝ) * (1 / ((N : ℝ) * E)) * E := by
            have hstep1 : (j : ℝ) * (1 / ((N : ℝ) * E)) ≤ (N : ℝ) * (1 / ((N : ℝ) * E)) :=
              mul_le_mul_of_nonneg_right hjlt.le (by positivity)
            exact mul_le_mul hstep1 hs (abs_nonneg s) (by positivity)
          have h2 : (N : ℝ) * (1 / ((N : ℝ) * E)) * E = 1 := by field_simp
          linarith
        exact (cos_bounds habs).1
  unfold fejer
  have hsq : ((N : ℝ) / 2) ^ 2 ≤ (∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  nlinarith [sq_nonneg (∑ j ∈ Finset.range N, Real.sin ((j : ℝ) * h * s))]



/- ### Module 3C: Sharp block-summed Fejér anti-concentration (no `C0` factor) -/

private lemma sum_geom_half_le_two (N : ℕ) :
    ∑ b ∈ Finset.range N, ((1 / 2 : ℝ) ^ b) ≤ 2 := by
  have h := geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num) N
  rw [h]
  have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
  have hdiv : ((1 / 2 : ℝ) ^ N - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2 : ℝ) ^ N := by ring
  linarith

private lemma exp_neg_nat_le_half_pow (b : ℕ) :
    Real.exp (-(b : ℝ)) ≤ (1 / 2 : ℝ) ^ b := by
  have h1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos 1) (by norm_num)).mpr (by linarith)
  have h2 : Real.exp (-(b : ℝ)) = (Real.exp (-1 : ℝ)) ^ b := by
    rw [← Real.exp_nat_mul]
    congr 1; ring
  rw [h2]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h1 b

private lemma card_fiber_natAbs_div (N j L b : ℕ) (hL : 1 ≤ L) :
    ((Finset.range N).filter (fun k : ℕ => Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b)).card ≤ 2 * L := by
  let S : Finset ℕ := (Finset.range N).filter (fun k : ℕ => Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b)
  let I1 : Finset ℤ := Finset.Ico ((j : ℤ) + (b * L : ℕ)) ((j : ℤ) + ((b + 1) * L : ℕ))
  let I2 : Finset ℤ := Finset.Ioc ((j : ℤ) - ((b + 1) * L : ℕ)) ((j : ℤ) - (b * L : ℕ))
  have hsub : S.image (fun k : ℕ => (k : ℤ)) ⊆ I1 ∪ I2 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    have hdiv : Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b := (Finset.mem_filter.mp hk).2
    have hlo : b * L ≤ Int.natAbs ((j : ℤ) - (k : ℤ)) := by
      have := Nat.div_mul_le_self (Int.natAbs ((j : ℤ) - (k : ℤ))) L
      rwa [hdiv] at this
    have hhi : Int.natAbs ((j : ℤ) - (k : ℤ)) < (b + 1) * L := by
      have h1 := Nat.lt_mul_div_succ (Int.natAbs ((j : ℤ) - (k : ℤ))) (by omega : 0 < L)
      rw [hdiv] at h1
      nlinarith
    rw [Finset.mem_union]
    by_cases hjk : (j : ℤ) ≤ (k : ℤ)
    · left
      rw [Finset.mem_Ico]
      have habs : ((Int.natAbs ((j : ℤ) - (k : ℤ)) : ℕ) : ℤ) = (k : ℤ) - (j : ℤ) := by omega
      omega
    · right
      rw [Finset.mem_Ioc]
      have habs : ((Int.natAbs ((j : ℤ) - (k : ℤ)) : ℕ) : ℤ) = (j : ℤ) - (k : ℤ) := by omega
      omega
  have hinj : (S.image (fun k : ℕ => (k : ℤ))).card = S.card :=
    Finset.card_image_of_injective S Int.ofNat_injective
  have hcard1 : I1.card = L := by
    dsimp [I1]
    rw [Int.card_Ico]
    have h1 : (j : ℤ) + ((b : ℤ) + 1) * (L : ℤ) - ((j : ℤ) + (b : ℤ) * (L : ℤ)) = (L : ℤ) := by ring
    rw [h1]; exact Int.toNat_natCast L
  have hcard2 : I2.card = L := by
    dsimp [I2]
    rw [Int.card_Ioc]
    have h1 : (j : ℤ) - (b : ℤ) * (L : ℤ) - ((j : ℤ) - ((b : ℤ) + 1) * (L : ℤ)) = (L : ℤ) := by ring
    rw [h1]; exact Int.toNat_natCast L
  calc S.card = (S.image (fun k : ℕ => (k : ℤ))).card := hinj.symm
    _ ≤ (I1 ∪ I2).card := Finset.card_le_card hsub
    _ ≤ I1.card + I2.card := Finset.card_union_le I1 I2
    _ = 2 * L := by omega

private lemma fejer_anticoncentration_sharp
    (d σ N : ℕ) (ε : ℝ)
    (hd : 1 ≤ d) (hσ : 1 ≤ σ) (hN : 1 ≤ N)
    (hε : 0 < ε)
    (hsmall : 9 ≤ ε * Real.sqrt (d : ℝ))
    (x : Fin d → ℤ) (hx_box : x ∈ box d σ)
    (hx_norm : (d : ℝ) / 2 * v1 σ ≤ normSq x) :
    let E := ε * v1 σ * Real.sqrt (d : ℝ)
    ∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y ≤
      48 * ε + 16 / (N : ℝ) := by
  intro E
  obtain ⟨hv1_lo, _, _⟩ := v1_bounds σ hσ
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hσpos : (0 : ℝ) < (σ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hv1_pos : 0 < v1 σ := by nlinarith
  have hE_pos : 0 < E := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  let h : ℝ := 1 / ((N : ℝ) * E)
  have hh_pos : 0 < h := by dsimp [h]; positivity
  have hmarkov : (N : ℝ) ^ 2 / 4 *
      (∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y) ≤
      ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) := by
    rw [Finset.mul_sum]
    calc ∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), (N : ℝ) ^ 2 / 4 * pd d σ y
        ≤ ∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y * fejer N h (ip x y) := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hfe := fejer_ge_of_small N h E (ip x y) hN hE_pos rfl (Finset.mem_filter.mp hy).2
          nlinarith [pd_nonneg d σ y]
      _ ≤ ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun y _ _ => mul_nonneg (pd_nonneg d σ y) (fejer_nonneg N h (ip x y)))
  have hexp_fejer : ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)) := by
    simp_rw [fejer_expand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_box_cos d σ (((j : ℝ) - (k : ℝ)) * h) x
  have hterm_le : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N,
      (∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
        p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ))) ≤
      Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) := by
    intro j hj k hk
    have hjk_lt : |(j : ℝ) - (k : ℝ)| ≤ (N : ℝ) := by
      have hj' : (j : ℝ) < (N : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
      have hk' : (k : ℝ) < (N : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hk)
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j, Nat.cast_nonneg (α := ℝ) k]
    have hcoord : ∀ r : Fin d,
        0 ≤ ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)) ∧
        (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ))) ≤
        Real.exp (-(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2) := by
      intro r
      have hxr : |(x r : ℝ)| ≤ (σ : ℝ) := by
        have h1 := mem_box_iff.mp hx_box r
        rw [abs_le]
        exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
      have hang_le : ∀ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          |((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)| ≤ 1 := by
        intro a ha
        have ha_le : |(a : ℝ)| ≤ (σ : ℝ) := by
          rw [Finset.mem_Icc] at ha
          rw [abs_le]
          exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh_pos]
        have hstep1 : |(j : ℝ) - (k : ℝ)| * h * |(x r : ℝ)| * |(a : ℝ)| ≤
            (N : ℝ) * h * (σ : ℝ) * (σ : ℝ) := by
          have hA : |(j : ℝ) - (k : ℝ)| * h ≤ (N : ℝ) * h :=
            mul_le_mul_of_nonneg_right hjk_lt hh_pos.le
          have hB : |(j : ℝ) - (k : ℝ)| * h * |(x r : ℝ)| ≤ (N : ℝ) * h * (σ : ℝ) :=
            mul_le_mul hA hxr (abs_nonneg _) (mul_nonneg hNpos.le hh_pos.le)
          exact mul_le_mul hB ha_le (abs_nonneg _) (mul_nonneg (mul_nonneg hNpos.le hh_pos.le) hσpos.le)
        have hstep2 : (N : ℝ) * h * (σ : ℝ) * (σ : ℝ) = (σ : ℝ) ^ 2 / E := by
          dsimp [h]; field_simp
        have hstep3 : (σ : ℝ) ^ 2 / E ≤ 1 := by
          rw [div_le_one hE_pos]
          dsimp [E]
          have h9 : (σ : ℝ) ^ 2 ≤ 9 * v1 σ := by linarith
          calc (σ : ℝ) ^ 2 ≤ 9 * v1 σ := h9
            _ ≤ (ε * Real.sqrt (d : ℝ)) * v1 σ := mul_le_mul_of_nonneg_right hsmall hv1_pos.le
            _ = ε * v1 σ * Real.sqrt (d : ℝ) := by ring
        linarith
      constructor
      · refine Finset.sum_nonneg fun a ha => mul_nonneg (p1_nonneg σ a) ?_
        linarith [(cos_bounds (hang_le a ha)).1]
      · let θ := ((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)
        have hsum_le : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * Real.cos (θ * (a : ℝ)) ≤
            1 - (v1 σ / 3) * θ ^ 2 := by
          calc ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * Real.cos (θ * (a : ℝ))
              ≤ ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (1 - (θ * (a : ℝ)) ^ 2 / 3) :=
                Finset.sum_le_sum fun a ha =>
                  mul_le_mul_of_nonneg_left (cos_bounds (hang_le a ha)).2 (p1_nonneg σ a)
            _ = (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a) -
                (θ ^ 2 / 3) * (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (a : ℝ) ^ 2) := by
                have hrew : ∀ a : ℤ,
                    p1 σ a * (1 - (θ * (a : ℝ)) ^ 2 / 3) =
                      p1 σ a - (θ ^ 2 / 3) * (p1 σ a * (a : ℝ) ^ 2) := by intro a; ring
                simp_rw [hrew, Finset.sum_sub_distrib, ← Finset.mul_sum]
            _ = 1 - (v1 σ / 3) * θ ^ 2 := by
                rw [sum_p1 σ]; unfold v1; ring
        have hexp_le : 1 - (v1 σ / 3) * θ ^ 2 ≤ Real.exp (-(v1 σ / 3) * θ ^ 2) := by
          linarith [Real.add_one_le_exp (-(v1 σ / 3) * θ ^ 2)]
        exact hsum_le.trans hexp_le
    calc ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ))
        ≤ ∏ r : Fin d, Real.exp (-(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2) :=
          Finset.prod_le_prod (fun r _ => (hcoord r).1) (fun r _ => (hcoord r).2)
      _ = Real.exp (∑ r : Fin d, -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have hsum_eq : ∑ r : Fin d, -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2 =
              -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x := by
            unfold normSq
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => by ring
          rw [hsum_eq]
          have hcoeff : 0 ≤ (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) := by positivity
          have h1 : (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * ((d : ℝ) / 2 * v1 σ) ≤
              (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x :=
            mul_le_mul_of_nonneg_left hx_norm hcoeff
          have h2 : (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * ((d : ℝ) / 2 * v1 σ) =
              ((j : ℝ) - (k : ℝ)) ^ 2 / (6 * (N : ℝ) ^ 2 * ε ^ 2) := by
            have hEsq : E ^ 2 = ε ^ 2 * (v1 σ) ^ 2 * (d : ℝ) := by
              dsimp [E]
              rw [mul_pow, mul_pow, Real.sq_sqrt hdpos.le]
            have hhsq : h ^ 2 = 1 / ((N : ℝ) ^ 2 * E ^ 2) := by
              dsimp [h]; field_simp
            rw [hhsq, hEsq]
            field_simp [hNpos.ne', hε.ne', hv1_pos.ne', hdpos.ne']
            ring
          have hneg1 : -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x =
              -(v1 σ / 3 * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x) := by ring
          have hneg2 : -(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2) =
              -(((j : ℝ) - (k : ℝ)) ^ 2 / (6 * (N : ℝ) ^ 2 * ε ^ 2)) := by ring
          linarith
  let L : ℕ := Nat.ceil (3 * (N : ℝ) * ε)
  have hL_ge : 3 * (N : ℝ) * ε ≤ (L : ℝ) := Nat.le_ceil _
  have hL_lt : (L : ℝ) < 3 * (N : ℝ) * ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hL_pos : 1 ≤ L := by
    have : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (by positivity) hL_ge
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp this)
  have hrow_le : ∀ j ∈ Finset.range N,
      ∑ k ∈ Finset.range N,
        Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) ≤ 4 * (L : ℝ) := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hmaps : ∀ k ∈ Finset.range N, Int.natAbs ((j : ℤ) - (k : ℤ)) / L ∈ Finset.range N := by
      intro k hk
      have hkN : k < N := Finset.mem_range.mp hk
      rw [Finset.mem_range]
      have habs : Int.natAbs ((j : ℤ) - (k : ℤ)) < N := by omega
      exact lt_of_le_of_lt (Nat.div_le_self _ L) habs
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ b ∈ Finset.range N,
            ∑ k ∈ (Finset.range N).filter (fun k : ℕ => Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b),
              Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2))
        ≤ ∑ b ∈ Finset.range N, (2 * (L : ℝ)) * ((1 / 2 : ℝ) ^ b) := by
          refine Finset.sum_le_sum fun b _ => ?_
          calc ∑ k ∈ (Finset.range N).filter (fun k : ℕ => Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b),
                  Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2))
              ≤ ∑ _k ∈ (Finset.range N).filter (fun k : ℕ => Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b),
                  ((1 / 2 : ℝ) ^ b) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hdiv : Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b := (Finset.mem_filter.mp hk).2
                have hloN : b * L ≤ Int.natAbs ((j : ℤ) - (k : ℤ)) := by
                  have := Nat.div_mul_le_self (Int.natAbs ((j : ℤ) - (k : ℤ))) L
                  rwa [hdiv] at this
                have hloR : (b : ℝ) * (L : ℝ) ≤ |(j : ℝ) - (k : ℝ)| := by
                  have h1 : ((b * L : ℕ) : ℝ) ≤ (Int.natAbs ((j : ℤ) - (k : ℤ)) : ℝ) := by
                    exact_mod_cast hloN
                  have h2 : ((Int.natAbs ((j : ℤ) - (k : ℤ)) : ℕ) : ℝ) = |(j : ℝ) - (k : ℝ)| := by
                    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
                  push_cast at h1; linarith
                have hsq : (b : ℝ) * (6 * (N : ℝ) ^ 2 * ε ^ 2) ≤ ((j : ℝ) - (k : ℝ)) ^ 2 := by
                  have hb_sq : (b : ℝ) ≤ (b : ℝ) ^ 2 := by
                    have : b ≤ b * b := Nat.le_mul_self b
                    have hR : (b : ℝ) ≤ ((b * b : ℕ) : ℝ) := by exact_mod_cast this
                    push_cast at hR; nlinarith
                  have hLsq : 6 * (N : ℝ) ^ 2 * ε ^ 2 ≤ (L : ℝ) ^ 2 := by
                    have h3 : (3 * (N : ℝ) * ε) ^ 2 ≤ (L : ℝ) ^ 2 := by
                      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hε.le]
                    nlinarith [sq_nonneg ((N : ℝ) * ε)]
                  have hmul : (b : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ |(j : ℝ) - (k : ℝ)| ^ 2 := by
                    have hbl : 0 ≤ (b : ℝ) * (L : ℝ) := by positivity
                    have := mul_le_mul hloR hloR hbl (abs_nonneg _)
                    linarith
                  rw [sq_abs] at hmul
                  have h6nn : 0 ≤ 6 * (N : ℝ) ^ 2 * ε ^ 2 := by positivity
                  have hstep : (b : ℝ) * (6 * (N : ℝ) ^ 2 * ε ^ 2) ≤ (b : ℝ) ^ 2 * (L : ℝ) ^ 2 :=
                    mul_le_mul hb_sq hLsq h6nn (sq_nonneg _)
                  linarith
                have hden : 0 < 6 * (N : ℝ) ^ 2 * ε ^ 2 := by positivity
                have hexp1 : -(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2) ≤ -(b : ℝ) := by
                  rw [div_le_iff₀ hden]
                  linarith
                exact (Real.exp_le_exp.mpr hexp1).trans (exp_neg_nat_le_half_pow b)
            _ = (((Finset.range N).filter (fun k : ℕ => Int.natAbs ((j : ℤ) - (k : ℤ)) / L = b)).card : ℝ) *
                  ((1 / 2 : ℝ) ^ b) := by simp
            _ ≤ (2 * (L : ℝ)) * ((1 / 2 : ℝ) ^ b) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                have hc := card_fiber_natAbs_div N j L b hL_pos
                exact_mod_cast hc
      _ = (2 * (L : ℝ)) * ∑ b ∈ Finset.range N, ((1 / 2 : ℝ) ^ b) := by rw [← Finset.mul_sum]
      _ ≤ (2 * (L : ℝ)) * 2 := mul_le_mul_of_nonneg_left (sum_geom_half_le_two N) (by positivity)
      _ = 4 * (L : ℝ) := by ring
  have htotal : (N : ℝ) ^ 2 / 4 *
      (∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y) ≤
      (N : ℝ) * (4 * (L : ℝ)) := by
    calc (N : ℝ) ^ 2 / 4 * (∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y)
        ≤ ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) := hmarkov
      _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
              p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)) := hexp_fejer
      _ ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm_le j hj k hk
      _ ≤ ∑ _j ∈ Finset.range N, (4 * (L : ℝ)) := Finset.sum_le_sum hrow_le
      _ = (N : ℝ) * (4 * (L : ℝ)) := by simp
  have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 / 4 := by positivity
  have hrhs : (N : ℝ) * (4 * (L : ℝ)) ≤ ((N : ℝ) ^ 2 / 4) * (48 * ε + 16 / (N : ℝ)) := by
    have h1 : (N : ℝ) * (4 * (L : ℝ)) ≤ (N : ℝ) * (4 * (3 * (N : ℝ) * ε + 1)) := by nlinarith
    have h2 : ((N : ℝ) ^ 2 / 4) * (48 * ε + 16 / (N : ℝ)) =
        (N : ℝ) * (4 * (3 * (N : ℝ) * ε + 1)) := by
      field_simp [hNpos.ne']; ring
    linarith
  nlinarith

private lemma discrete_gaussian_indep_bound (d : ℕ) (hd : 1 ≤ d) (C : ℝ) (_hC : 0 ≤ C)
    (I : Finset (Fin d → ℤ)) (hI_sub : I ⊆ box d d)
    (hI_sep : ∀ x ∈ I, ∀ y ∈ I, 4 * C ^ 2 < normSq (x + y)) :
    ∑ x ∈ I, pd d d x ≤ Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) := by
  let f : (Fin d → ℤ) → ℝ := fun x =>
    if x ∈ I then Real.exp (-normSq x / (2 * (d : ℝ) ^ 2)) else 0
  let g : (Fin d → ℤ) → ℝ := fun y =>
    if -y ∈ I then Real.exp (-normSq y / (2 * (d : ℝ) ^ 2)) else 0
  let h : (Fin d → ℤ) → ℝ := fun z =>
    Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) *
      Real.exp (-normSq z / (2 * (d : ℝ) ^ 2))
  have hf : ∀ x, 0 ≤ f x := fun x => by dsimp [f]; split_ifs <;> positivity
  have hg : ∀ y, 0 ≤ g y := fun y => by dsimp [g]; split_ifs <;> positivity
  have hh : ∀ z, 0 ≤ h z := fun z => by dsimp [h]; positivity
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpl : ∀ x ∈ box d d, ∀ y ∈ box d d, ∀ z ∈ box d d,
      (∀ r : Fin d, |x r + y r - 2 * z r| ≤ 1) → Real.sqrt (f x * g y) ≤ h z := by
    intro x _ y _ z hz hclose
    by_cases hxin : x ∈ I
    · by_cases hyin : -y ∈ I
      · simp only [f, g, h, hxin, hyin, ↓reduceIte]
        rw [← Real.exp_add, ← Real.exp_half, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hsep : 4 * C ^ 2 < normSq (x + (-y)) := hI_sep x hxin (-y) hyin
        have hcoord : ∀ r : Fin d,
            (x r : ℝ) ^ 2 + (y r : ℝ) ^ 2 ≥
              2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 - 2 * (d : ℝ) := by
          intro r
          let e : ℝ := (x r : ℝ) + (y r : ℝ) - 2 * (z r : ℝ)
          have he : |e| ≤ 1 := by
            have h1 := abs_le.mp (hclose r)
            rw [abs_le]
            exact ⟨by dsimp [e]; exact_mod_cast h1.1, by dsimp [e]; exact_mod_cast h1.2⟩
          have hzr : |(z r : ℝ)| ≤ (d : ℝ) := by
            have h1 := mem_box_iff.mp hz r
            rw [abs_le]
            exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
          have hcross : -(d : ℝ) ≤ (z r : ℝ) * e := by
            have h1 : |(z r : ℝ) * e| ≤ (d : ℝ) := by
              rw [abs_mul]
              calc |(z r : ℝ)| * |e| ≤ (d : ℝ) * 1 :=
                mul_le_mul hzr he (abs_nonneg _) hdpos.le
                _ = (d : ℝ) := mul_one _
            exact (abs_le.mp h1).1
          have hid : (x r : ℝ) ^ 2 + (y r : ℝ) ^ 2 =
              2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 +
              2 * ((z r : ℝ) * e) + e ^ 2 / 2 := by
            dsimp [e]; ring
          nlinarith [sq_nonneg e]
        have hsum_norm : normSq x + normSq y ≥
            2 * normSq z + normSq (x + (-y)) / 2 - 2 * (d : ℝ) ^ 2 := by
          have h1 : ∑ r : Fin d, ((x r : ℝ) ^ 2 + (y r : ℝ) ^ 2) ≥
              ∑ r : Fin d, (2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 - 2 * (d : ℝ)) :=
            Finset.sum_le_sum fun r _ => hcoord r
          have hL : ∑ r : Fin d, ((x r : ℝ) ^ 2 + (y r : ℝ) ^ 2) = normSq x + normSq y := by
            simp only [normSq, Finset.sum_add_distrib]
          have hR : ∑ r : Fin d,
              (2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 - 2 * (d : ℝ)) =
              2 * normSq z + normSq (x + (-y)) / 2 - 2 * (d : ℝ) ^ 2 := by
            simp only [normSq, Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg,
              Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hsub : ∀ r : Fin d, ((x r : ℝ) + -(y r : ℝ)) ^ 2 = ((x r : ℝ) - (y r : ℝ)) ^ 2 := by
              intro r; ring
            simp_rw [hsub]; ring
          linarith
        have hden : 0 < 4 * (d : ℝ) ^ 2 := by positivity
        have hmain : -(normSq x + normSq y) / (4 * (d : ℝ) ^ 2) ≤
            (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) + (-normSq z / (2 * (d : ℝ) ^ 2)) := by
          have h1 : 2 * normSq z + 2 * C ^ 2 - 2 * (d : ℝ) ^ 2 ≤ normSq x + normSq y := by linarith
          have h2 : -(normSq x + normSq y) / (4 * (d : ℝ) ^ 2) ≤
              -(2 * normSq z + 2 * C ^ 2 - 2 * (d : ℝ) ^ 2) / (4 * (d : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) hden.le
          have h3 : -(2 * normSq z + 2 * C ^ 2 - 2 * (d : ℝ) ^ 2) / (4 * (d : ℝ) ^ 2) =
              (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) + (-normSq z / (2 * (d : ℝ) ^ 2)) := by
            field_simp [hdpos.ne']; ring
          linarith
        have hrew : (-normSq x / (2 * (d : ℝ) ^ 2) + -normSq y / (2 * (d : ℝ) ^ 2)) / 2 =
            -(normSq x + normSq y) / (4 * (d : ℝ) ^ 2) := by ring
        linarith
      · simp [g, hyin]; exact hh z
    · simp [f, hxin]; exact hh z
  have hpl_res := discrete_PL_nd d d f g h hf hg hh hpl
  have hf_sum : ∑ x ∈ box d d, f x = ∑ x ∈ I, Real.exp (-normSq x / (2 * (d : ℝ) ^ 2)) := by
    simp only [f, ← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hI_sub hx, hx⟩⟩
  have hg_sum : ∑ y ∈ box d d, g y = ∑ x ∈ I, Real.exp (-normSq x / (2 * (d : ℝ) ^ 2)) := by
    rw [← hf_sum]
    refine Finset.sum_bij (fun y _ => -y) ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_box_iff] at hy ⊢
      intro r; have := hy r; simp only [Pi.neg_apply]; omega
    · intro a _ b _ hab; exact neg_inj.mp hab
    · intro x hx
      refine ⟨-x, ?_, neg_neg x⟩
      rw [mem_box_iff] at hx ⊢
      intro r; have := hx r; simp only [Pi.neg_apply]; omega
    · intro y _
      simp [f, g, normSq_neg]
  have hh_sum : ∑ z ∈ box d d, h z =
      Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) *
        ∑ z ∈ box d d, Real.exp (-normSq z / (2 * (d : ℝ) ^ 2)) := by
    simp only [h, ← Finset.mul_sum]
  rw [hf_sum, hg_sum, hh_sum, Real.sqrt_mul_self (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)]
    at hpl_res
  have hZd_pos : 0 < (Z1 d) ^ d := pow_pos (Z1_pos d) d
  have hZd_eq : ∑ z ∈ box d d, Real.exp (-normSq z / (2 * (d : ℝ) ^ 2)) = (Z1 d) ^ d := by
    have h1 := sum_box_pd d d
    simp_rw [pd_eq_exp_div, ← Finset.sum_div] at h1
    exact (div_eq_one_iff_eq hZd_pos.ne').mp h1
  rw [hZd_eq] at hpl_res
  have hI_pd : ∑ x ∈ I, pd d d x =
      (∑ x ∈ I, Real.exp (-normSq x / (2 * (d : ℝ) ^ 2))) / (Z1 d) ^ d := by
    simp_rw [pd_eq_exp_div, ← Finset.sum_div]
  rw [hI_pd, div_le_iff₀ hZd_pos]
  exact hpl_res



/- ### Module 4: Direct unweighted Bollobás–Erdős seed on `Fin n` -/

set_option maxHeartbeats 600000 in
private lemma exists_seed_on_fin
    {d : ℕ} (A : Finset (Fin d → ℤ)) (w : (Fin d → ℤ) → ℝ)
    (C E η δ : ℝ) (n : ℕ)
    (hn : 6 ≤ n) (hE : 0 < E) (hCE : C ^ 2 ≤ E)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hw0 : ∀ x ∈ A, 0 ≤ w x)
    (hw1 : ∑ x ∈ A, w x = 1)
    (hnorm : ∀ x ∈ A, 9 * C ^ 2 < normSq x)
    (hind : ∀ I ⊆ A, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → 4 * C ^ 2 < normSq (x + y)) →
      ∑ x ∈ I, w x ≤ δ)
    (hcross : 1 / 2 - η ≤ ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0) :
    ∃ (G : SimpleGraph (Fin n)) (side : Fin n → Bool),
      G.CliqueFree 4 ∧
      (∀ b : Bool, ∀ s : Finset (Fin n), (∀ v ∈ s, side v = b) → ¬ G.IsNClique 3 s) ∧
      (∀ b : Bool, n ≤ 3 * (Finset.univ.filter fun v : Fin n => side v = b).card) ∧
      (G.indepNum : ℝ) ≤ δ * (n : ℝ) + 2 * (A.card : ℝ) + 1 ∧
      (n : ℝ) ^ 2 / 8 - η / 4 * (n : ℝ) ^ 2 - (n : ℝ) / 4 - (n : ℝ) * (A.card : ℝ) ≤
        G.edgeFinset.card := by
  let n0 : ℕ := n / 2
  have hn0_le : n0 ≤ n := Nat.div_le_self n 2
  have h2n0 : 2 * n0 ≤ n := Nat.mul_div_le n 2
  have hn_le_2n0 : n ≤ 2 * n0 + 1 := by omega
  let c : {x // x ∈ A} → ℕ := fun x => Nat.floor ((n0 : ℝ) * w x.1)
  let m0 : ℕ := ∑ x : {x // x ∈ A}, c x
  have hc_le : ∀ x : {x // x ∈ A}, (c x : ℝ) ≤ (n0 : ℝ) * w x.1 := fun x =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg n0) (hw0 x.1 x.2))
  have hc_ge : ∀ x : {x // x ∈ A}, (n0 : ℝ) * w x.1 - 1 ≤ (c x : ℝ) := fun x =>
    le_of_lt (Nat.sub_one_lt_floor ((n0 : ℝ) * w x.1))
  have hsum_sub : ∑ x : {x // x ∈ A}, w x.1 = 1 := by
    rw [Finset.univ_eq_attach, Finset.sum_attach A w, hw1]
  have hm0_le_n0 : m0 ≤ n0 := by
    have hR : (m0 : ℝ) ≤ (n0 : ℝ) := by
      have h1 : (m0 : ℝ) = ∑ x : {x // x ∈ A}, (c x : ℝ) := by simp [m0]
      rw [h1]
      calc ∑ x : {x // x ∈ A}, (c x : ℝ)
          ≤ ∑ x : {x // x ∈ A}, (n0 : ℝ) * w x.1 := Finset.sum_le_sum fun x _ => hc_le x
        _ = (n0 : ℝ) * ∑ x : {x // x ∈ A}, w x.1 := by rw [← Finset.mul_sum]
        _ = (n0 : ℝ) := by rw [hsum_sub, mul_one]
    exact_mod_cast hR
  have hm0_ge : (n0 : ℝ) - (A.card : ℝ) ≤ (m0 : ℝ) := by
    have h1 : (m0 : ℝ) = ∑ x : {x // x ∈ A}, (c x : ℝ) := by simp [m0]
    rw [h1]
    have hcard_sub : (Fintype.card {x // x ∈ A} : ℝ) = (A.card : ℝ) := by
      simp [Fintype.card_coe]
    calc (n0 : ℝ) - (A.card : ℝ)
        = (n0 : ℝ) * (∑ x : {x // x ∈ A}, w x.1) - ∑ _x : {x // x ∈ A}, (1 : ℝ) := by
            rw [hsum_sub, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard_sub]
      _ = ∑ x : {x // x ∈ A}, ((n0 : ℝ) * w x.1 - 1) := by
            rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ x : {x // x ∈ A}, (c x : ℝ) := Finset.sum_le_sum fun x _ => hc_ge x
  let T := Σ x : {x // x ∈ A}, Fin (c x)
  have hTcard : Fintype.card T = m0 := by simp [T, m0, Fintype.card_sigma]
  let eT : Fin m0 ≃ T := (Fintype.equivFinOfCardEq hTcard).symm
  let π : Fin m0 → {x // x ∈ A} := fun i => (eT i).1
  let side : Fin n → Bool := fun v => decide (n0 ≤ v.1)
  let tag : Fin n → Option (Bool × {x // x ∈ A}) := fun v =>
    if h1 : v.1 < m0 then some (false, π ⟨v.1, h1⟩)
    else if h2 : n0 ≤ v.1 ∧ v.1 - n0 < m0 then some (true, π ⟨v.1 - n0, h2.2⟩)
    else none
  have htag_side : ∀ v b x, tag v = some (b, x) → side v = b := by
    intro v b x htv
    dsimp [tag] at htv
    split_ifs at htv with h1 h2
    · cases htv; dsimp [side]; simp [show ¬ n0 ≤ v.1 by omega]
    · cases htv; dsimp [side]; simp [h2.1]
  let G : SimpleGraph (Fin n) :=
    { Adj := fun u v =>
        match tag u, tag v with
        | some (false, x), some (false, y) => x ≠ y ∧ normSq (x.1 + y.1) ≤ 4 * C ^ 2
        | some (true, x), some (true, y) => x ≠ y ∧ normSq (x.1 + y.1) ≤ 4 * C ^ 2
        | some (false, x), some (true, y) => E < ip x.1 y.1
        | some (true, x), some (false, y) => E < ip y.1 x.1
        | _, _ => False
      symm := ⟨by
        intro u v huv
        cases hu : tag u with
        | none => simp [hu] at huv
        | some pu =>
          cases hv : tag v with
          | none => simp [hu, hv] at huv
          | some pv =>
            rcases pu with ⟨bu, xu⟩
            rcases pv with ⟨bv, xv⟩
            cases bu <;> cases bv <;> simp [hu, hv] at huv ⊢
            · exact ⟨Ne.symm huv.1, by rw [add_comm]; exact huv.2⟩
            · exact huv
            · exact huv
            · exact ⟨Ne.symm huv.1, by rw [add_comm]; exact huv.2⟩⟩
      loopless := ⟨by
        intro u huu
        cases hu : tag u with
        | none => simp [hu] at huu
        | some pu =>
          rcases pu with ⟨bu, xu⟩
          cases bu <;> simp [hu] at huu⟩ }
  have hno_tri_A : ∀ x y z : {x // x ∈ A},
      normSq (x.1 + y.1) ≤ 4 * C ^ 2 →
      normSq (y.1 + z.1) ≤ 4 * C ^ 2 →
      normSq (z.1 + x.1) ≤ 4 * C ^ 2 → False := by
    intro x y z h1 h2 h3
    have hb := normSq_triangle_bound x.1 y.1 z.1 C h1 h2 h3
    linarith [hnorm x.1 x.2]
  have htri : ∀ b : Bool, ∀ s : Finset (Fin n), (∀ v ∈ s, side v = b) → ¬ G.IsNClique 3 s := by
    intro b s hsb hs
    obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, h12, h13, h23⟩ :=
      Finset.two_lt_card_iff.mp (by rw [hs.card_eq]; omega : 2 < s.card)
    have ha12 := hs.1 hu₁ hu₂ h12
    have ha23 := hs.1 hu₂ hu₃ h23
    have ha31 := hs.1 hu₃ hu₁ h13.symm
    cases ht1 : tag u₁ with
    | none => simp [G, ht1] at ha12
    | some p1 =>
      cases ht2 : tag u₂ with
      | none => simp [G, ht1, ht2] at ha12
      | some p2 =>
        cases ht3 : tag u₃ with
        | none => simp [G, ht2, ht3] at ha23
        | some p3 =>
          rcases p1 with ⟨b1, x1⟩
          rcases p2 with ⟨b2, x2⟩
          rcases p3 with ⟨b3, x3⟩
          have hb1 : b1 = b := (htag_side u₁ b1 x1 ht1).symm.trans (hsb u₁ hu₁)
          have hb2 : b2 = b := (htag_side u₂ b2 x2 ht2).symm.trans (hsb u₂ hu₂)
          have hb3 : b3 = b := (htag_side u₃ b3 x3 ht3).symm.trans (hsb u₃ hu₃)
          subst hb1 hb2 hb3
          cases b3 <;> simp [G, ht1, ht2, ht3] at ha12 ha23 ha31
          · exact hno_tri_A x1 x2 x3 ha12.2 ha23.2 ha31.2
          · exact hno_tri_A x1 x2 x3 ha12.2 ha23.2 ha31.2
  have hcf : G.CliqueFree 4 := by
    intro s hs
    let sL := s.filter (fun u : Fin n => side u = false)
    let sR := s.filter (fun u : Fin n => side u = true)
    have hsplit : sL.card + sR.card = 4 := by
      have h1 : sL.card + sR.card = s.card := by
        have hrew : sR = s.filter (fun u : Fin n => ¬ side u = false) := by
          ext u; simp [sR]
        rw [hrew]
        simp only [sL, Finset.card_eq_sum_ones]
        exact Finset.sum_filter_add_sum_filter_not s (fun u : Fin n => side u = false) (fun _ => 1)
      rw [h1, hs.card_eq]
    by_cases hL3 : 3 ≤ sL.card
    · obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hL3
      have hts : t ⊆ s := ht_sub.trans (Finset.filter_subset _ _)
      have hcl : G.IsNClique 3 t := ⟨hs.isClique.subset hts, ht_card⟩
      exact htri false t (fun v hv => (Finset.mem_filter.mp (ht_sub hv)).2) hcl
    · by_cases hR3 : 3 ≤ sR.card
      · obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hR3
        have hts : t ⊆ s := ht_sub.trans (Finset.filter_subset _ _)
        have hcl : G.IsNClique 3 t := ⟨hs.isClique.subset hts, ht_card⟩
        exact htri true t (fun v hv => (Finset.mem_filter.mp (ht_sub hv)).2) hcl
      · have hL2 : 1 < sL.card := by omega
        have hR2 : 1 < sR.card := by omega
        obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ := Finset.one_lt_card.mp hL2
        obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Finset.one_lt_card.mp hR2
        have hu₁s := (Finset.mem_filter.mp hu₁).1
        have hu₂s := (Finset.mem_filter.mp hu₂).1
        have hv₁s := (Finset.mem_filter.mp hv₁).1
        have hv₂s := (Finset.mem_filter.mp hv₂).1
        have hu₁L := (Finset.mem_filter.mp hu₁).2
        have hu₂L := (Finset.mem_filter.mp hu₂).2
        have hv₁R := (Finset.mem_filter.mp hv₁).2
        have hv₂R := (Finset.mem_filter.mp hv₂).2
        have hne_uv : ∀ u v, side u = false → side v = true → u ≠ v := by
          intro u v hu hv heq; rw [heq, hv] at hu; cases hu
        have ha_u := hs.1 hu₁s hu₂s hu12
        have ha_v := hs.1 hv₁s hv₂s hv12
        have h11 := hs.1 hu₁s hv₁s (hne_uv _ _ hu₁L hv₁R)
        have h12 := hs.1 hu₁s hv₂s (hne_uv _ _ hu₁L hv₂R)
        have h21 := hs.1 hu₂s hv₁s (hne_uv _ _ hu₂L hv₁R)
        have h22 := hs.1 hu₂s hv₂s (hne_uv _ _ hu₂L hv₂R)
        cases htu1 : tag u₁ with
        | none => simp [G, htu1] at ha_u
        | some pu1 =>
          cases htu2 : tag u₂ with
          | none => simp [G, htu1, htu2] at ha_u
          | some pu2 =>
            cases htv1 : tag v₁ with
            | none => simp [G, htv1] at ha_v
            | some pv1 =>
              cases htv2 : tag v₂ with
              | none => simp [G, htv1, htv2] at ha_v
              | some pv2 =>
                rcases pu1 with ⟨bu1, a1⟩; rcases pu2 with ⟨bu2, a2⟩
                rcases pv1 with ⟨bv1, b1⟩; rcases pv2 with ⟨bv2, b2⟩
                have hbu1 : bu1 = false := (htag_side _ _ _ htu1).symm.trans hu₁L
                have hbu2 : bu2 = false := (htag_side _ _ _ htu2).symm.trans hu₂L
                have hbv1 : bv1 = true := (htag_side _ _ _ htv1).symm.trans hv₁R
                have hbv2 : bv2 = true := (htag_side _ _ _ htv2).symm.trans hv₂R
                subst hbu1 hbu2 hbv1 hbv2
                simp [G, htu1, htu2, htv1, htv2] at ha_u ha_v h11 h12 h21 h22
                have hsum4 : 4 * E < ip (a1.1 + a2.1) (b1.1 + b2.1) := by
                  rw [ip_add_left, ip_add_right, ip_add_right]; linarith
                have hcs := ip_sq_le_normSq_mul (a1.1 + a2.1) (b1.1 + b2.1)
                have hsq_lt : (4 * E) ^ 2 < (ip (a1.1 + a2.1) (b1.1 + b2.1)) ^ 2 := by nlinarith
                have hmul_le : normSq (a1.1 + a2.1) * normSq (b1.1 + b2.1) ≤
                    (4 * C ^ 2) * (4 * C ^ 2) :=
                  mul_le_mul ha_u.2 ha_v.2 (normSq_nonneg _) (by positivity)
                have hC4 : (4 * C ^ 2) * (4 * C ^ 2) ≤ (4 * E) ^ 2 := by nlinarith [sq_nonneg C]
                linarith
  have hcard_false : (Finset.univ.filter fun v : Fin n => side v = false).card = n0 := by
    have hbij : (Finset.univ.filter fun v : Fin n => side v = false).card =
        (Finset.univ : Finset (Fin n0)).card := by
      refine Finset.card_bij (fun v hv => (⟨v.1, by
        have := (Finset.mem_filter.mp hv).2
        dsimp [side] at this; simp at this; exact this⟩ : Fin n0)) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin n0 → ℕ) h)
      · intro i _
        refine ⟨⟨i.1, lt_of_lt_of_le i.2 hn0_le⟩, ?_, rfl⟩
        rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        dsimp [side]; simp [not_le.mpr i.2]
    simpa using hbij
  have hbal : ∀ b : Bool, n ≤ 3 * (Finset.univ.filter fun v : Fin n => side v = b).card := by
    intro b
    cases b
    · omega
    · have hcomp : (Finset.univ.filter fun v : Fin n => side v = false).card +
          (Finset.univ.filter fun v : Fin n => side v = true).card = n := by
        have hrew : (Finset.univ.filter fun v : Fin n => side v = true) =
            (Finset.univ.filter fun v : Fin n => ¬ side v = false) := by ext v; simp
        rw [hrew]
        simp only [Finset.card_eq_sum_ones]
        rw [Finset.sum_filter_add_sum_filter_not]
        simp
      omega
  have hfiber_card : ∀ x : {x // x ∈ A},
      (Finset.univ.filter (fun i : Fin m0 => π i = x)).card = c x := by
    intro x
    let S := Finset.univ.filter (fun i : Fin m0 => π i = x)
    have hbij : (Finset.univ : Finset (Fin (c x))).card = S.card := by
      refine Finset.card_bij (fun j _ => eT.symm ⟨x, j⟩) ?_ ?_ ?_
      · intro j _; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp [π]⟩
      · intro j1 _ j2 _ h
        have h1 : (⟨x, j1⟩ : T) = ⟨x, j2⟩ := eT.symm.injective h
        exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2
      · intro i hi
        have hpi : (eT i).1 = x := (Finset.mem_filter.mp hi).2
        refine ⟨hpi ▸ (eT i).2, Finset.mem_univ _, ?_⟩
        apply eT.injective
        simp only [Equiv.apply_symm_apply]
        exact Sigma.ext hpi.symm (by cases hpi; rfl)
    simpa using hbij.symm
  have hindG : (G.indepNum : ℝ) ≤ δ * (n : ℝ) + 2 * (A.card : ℝ) + 1 := by
    obtain ⟨I, hIind, hIcard⟩ := G.exists_isNIndepSet_indepNum
    rw [← hIcard]
    let IL_v := I.filter (fun v : Fin n => v.1 < m0)
    let IR_v := I.filter (fun v : Fin n => n0 ≤ v.1 ∧ v.1 - n0 < m0)
    let IN_v := I.filter (fun v : Fin n => ¬ v.1 < m0 ∧ ¬ (n0 ≤ v.1 ∧ v.1 - n0 < m0))
    have hI_cov : I ⊆ IL_v ∪ (IR_v ∪ IN_v) := by
      intro v hv
      simp only [Finset.mem_union, Finset.mem_filter, IL_v, IR_v, IN_v]
      by_cases h1 : v.1 < m0
      · exact Or.inl ⟨hv, h1⟩
      · by_cases h2 : n0 ≤ v.1 ∧ v.1 - n0 < m0
        · exact Or.inr (Or.inl ⟨hv, h2⟩)
        · exact Or.inr (Or.inr ⟨hv, h1, h2⟩)
    have hcard_split : I.card ≤ IL_v.card + IR_v.card + IN_v.card := by
      calc I.card ≤ (IL_v ∪ (IR_v ∪ IN_v)).card := Finset.card_le_card hI_cov
        _ ≤ IL_v.card + (IR_v ∪ IN_v).card := Finset.card_union_le _ _
        _ ≤ IL_v.card + (IR_v.card + IN_v.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = IL_v.card + IR_v.card + IN_v.card := by omega
    have hIN_le : (IN_v.card : ℝ) ≤ 2 * (A.card : ℝ) + 1 := by
      let P1 := Finset.univ.filter fun v : Fin n => v.1 < m0
      let P2 := Finset.univ.filter fun v : Fin n => n0 ≤ v.1 ∧ v.1 - n0 < m0
      let P3 := Finset.univ.filter fun v : Fin n => ¬ v.1 < m0 ∧ ¬ (n0 ≤ v.1 ∧ v.1 - n0 < m0)
      have hsubN : IN_v ⊆ P3 := Finset.filter_subset_filter _ (Finset.subset_univ I)
      have htot : P1.card + P2.card + P3.card = n := by
        have hd12 : Disjoint P1 P2 := by
          rw [Finset.disjoint_left]; intro v h1 h2
          simp only [P1, P2, Finset.mem_filter] at h1 h2; omega
        have hd123 : Disjoint (P1 ∪ P2) P3 := by
          rw [Finset.disjoint_left]; intro v h12 h3
          simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter] at h12 h3; tauto
        have hun : (P1 ∪ P2) ∪ P3 = Finset.univ := by
          ext v; simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          tauto
        have hc := congrArg Finset.card hun
        rw [Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12, Finset.card_univ, Fintype.card_fin] at hc
        exact hc
      have hP1 : P1.card = m0 := by
        have hbij : P1.card = (Finset.univ : Finset (Fin m0)).card := by
          refine Finset.card_bij (fun v hv => (⟨v.1, (Finset.mem_filter.mp hv).2⟩ : Fin m0)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin m0 → ℕ) h)
          · intro i _
            refine ⟨⟨i.1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩, rfl⟩
        simpa using hbij
      have hP2 : P2.card = m0 := by
        have hbij : P2.card = (Finset.univ : Finset (Fin m0)).card := by
          refine Finset.card_bij (fun v hv => (⟨v.1 - n0, (Finset.mem_filter.mp hv).2.2⟩ : Fin m0)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a ha b hb h
            have ha' := (Finset.mem_filter.mp ha).2.1
            have hb' := (Finset.mem_filter.mp hb).2.1
            have hval : a.1 - n0 = b.1 - n0 := congrArg (Fin.val : Fin m0 → ℕ) h
            exact Fin.ext (by omega)
          · intro i _
            refine ⟨⟨n0 + i.1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right n0 i.1, by
              change n0 + i.1 - n0 < m0; omega⟩, ?_⟩
            exact Fin.ext (Nat.add_sub_cancel_left n0 i.1)
        simpa using hbij
      have hIN_nat : IN_v.card ≤ n - 2 * m0 := by
        have := Finset.card_le_card hsubN; omega
      have hIN_R : (IN_v.card : ℝ) ≤ (n : ℝ) - 2 * (m0 : ℝ) := by
        have h1 : (IN_v.card : ℝ) + 2 * (m0 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (by omega : IN_v.card + 2 * m0 ≤ n)
        linarith
      have hn_R : (n : ℝ) ≤ 2 * (n0 : ℝ) + 1 := by exact_mod_cast hn_le_2n0
      linarith
    have hIL_le : (IL_v.card : ℝ) ≤ (n0 : ℝ) * δ := by
      by_cases hm0z : m0 = 0
      · have hemp : IL_v = ∅ := by
          ext v; simp only [IL_v, Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
        rw [hemp, Finset.card_empty, Nat.cast_zero]
        positivity
      · have hm0pos : 0 < m0 := Nat.pos_of_ne_zero hm0z
        let fL : Fin n → Fin d → ℤ := fun v =>
          if h : v.1 < m0 then (π ⟨v.1, h⟩).1 else 0
        let JL : Finset (Fin d → ℤ) := IL_v.image fL
        have hJL_sub : JL ⊆ A := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
          have hlt : v.1 < m0 := (Finset.mem_filter.mp hv).2
          simp only [fL, hlt, ↓reduceDIte]
          exact (π ⟨v.1, hlt⟩).2
        have hJL_sep : ∀ x ∈ JL, ∀ y ∈ JL, x ≠ y → 4 * C ^ 2 < normSq (x + y) := by
          intro x hx y hy hxy
          rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
          rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
          have huI := (Finset.mem_filter.mp hu).1
          have hvI := (Finset.mem_filter.mp hv).1
          have hu1 := (Finset.mem_filter.mp hu).2
          have hv1 := (Finset.mem_filter.mp hv).2
          simp only [fL, hu1, hv1, ↓reduceDIte] at hxy ⊢
          have huv : u ≠ v := fun heq => by subst heq; exact hxy rfl
          have hna := hIind huI hvI huv
          have htu : tag u = some (false, π ⟨u.1, hu1⟩) := by simp [tag, hu1]
          have htv : tag v = some (false, π ⟨v.1, hv1⟩) := by simp [tag, hv1]
          have hne_sub : π ⟨u.1, hu1⟩ ≠ π ⟨v.1, hv1⟩ := fun h => hxy (congrArg Subtype.val h)
          by_contra hle; push Not at hle
          exact hna (by simp [G, htu, htv, hne_sub, hle])
        have hcardL : (IL_v.card : ℝ) ≤ ∑ x ∈ JL, (n0 : ℝ) * w x := by
          have hfib := Finset.card_eq_sum_card_fiberwise (f := fL) (s := IL_v) (t := JL)
            (fun v hv => Finset.mem_image_of_mem fL hv)
          rw [hfib, Nat.cast_sum]
          refine Finset.sum_le_sum fun x hx => ?_
          have hxA : x ∈ A := hJL_sub hx
          have hle_c : (IL_v.filter (fun v => fL v = x)).card ≤ c ⟨x, hxA⟩ := by
            rw [← hfiber_card ⟨x, hxA⟩]
            let g : Fin n → Fin m0 := fun v => if h : v.1 < m0 then ⟨v.1, h⟩ else ⟨0, hm0pos⟩
            refine Finset.card_le_card_of_injOn g ?_ ?_
            · intro v hv
              have hvIL := (Finset.mem_filter.mp hv).1
              have hfx := (Finset.mem_filter.mp hv).2
              have hvlt : v.1 < m0 := (Finset.mem_filter.mp hvIL).2
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, g, hvlt, ↓reduceDIte]
              simp only [fL, hvlt, ↓reduceDIte] at hfx
              exact Subtype.ext hfx
            · intro u hu v hv huv
              have hu1 : u.1 < m0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
              have hv1 : v.1 < m0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
              simp only [g, hu1, hv1, ↓reduceDIte] at huv
              exact Fin.ext (congrArg (Fin.val : Fin m0 → ℕ) huv)
          exact (Nat.cast_le.mpr hle_c).trans (hc_le ⟨x, hxA⟩)
        calc (IL_v.card : ℝ) ≤ ∑ x ∈ JL, (n0 : ℝ) * w x := hcardL
          _ = (n0 : ℝ) * ∑ x ∈ JL, w x := by rw [← Finset.mul_sum]
          _ ≤ (n0 : ℝ) * δ := mul_le_mul_of_nonneg_left (hind JL hJL_sub hJL_sep) (Nat.cast_nonneg n0)
    have hIR_le : (IR_v.card : ℝ) ≤ (n0 : ℝ) * δ := by
      by_cases hm0z : m0 = 0
      · have hemp : IR_v = ∅ := by
          ext v; simp only [IR_v, Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
        rw [hemp, Finset.card_empty, Nat.cast_zero]
        positivity
      · have hm0pos : 0 < m0 := Nat.pos_of_ne_zero hm0z
        let fR : Fin n → Fin d → ℤ := fun v =>
          if h : n0 ≤ v.1 ∧ v.1 - n0 < m0 then (π ⟨v.1 - n0, h.2⟩).1 else 0
        let JR : Finset (Fin d → ℤ) := IR_v.image fR
        have hJR_sub : JR ⊆ A := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
          have hlt := (Finset.mem_filter.mp hv).2
          simp only [fR, dif_pos hlt]
          exact (π ⟨v.1 - n0, hlt.2⟩).2
        have hJR_sep : ∀ x ∈ JR, ∀ y ∈ JR, x ≠ y → 4 * C ^ 2 < normSq (x + y) := by
          intro x hx y hy hxy
          rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
          rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
          have huI := (Finset.mem_filter.mp hu).1
          have hvI := (Finset.mem_filter.mp hv).1
          have hu2 := (Finset.mem_filter.mp hu).2
          have hv2 := (Finset.mem_filter.mp hv).2
          simp only [fR, dif_pos hu2, dif_pos hv2] at hxy ⊢
          have huv : u ≠ v := fun heq => by subst heq; exact hxy rfl
          have hna := hIind huI hvI huv
          have htu : tag u = some (true, π ⟨u.1 - n0, hu2.2⟩) := by
            have hnot1 : ¬ u.1 < m0 := by omega
            simp [tag, hnot1, hu2]
          have htv : tag v = some (true, π ⟨v.1 - n0, hv2.2⟩) := by
            have hnot1 : ¬ v.1 < m0 := by omega
            simp [tag, hnot1, hv2]
          have hne_sub : π ⟨u.1 - n0, hu2.2⟩ ≠ π ⟨v.1 - n0, hv2.2⟩ := fun h => hxy (congrArg Subtype.val h)
          by_contra hle; push Not at hle
          exact hna (by simp [G, htu, htv, hne_sub, hle])
        have hcardR : (IR_v.card : ℝ) ≤ ∑ x ∈ JR, (n0 : ℝ) * w x := by
          have hfib := Finset.card_eq_sum_card_fiberwise (f := fR) (s := IR_v) (t := JR)
            (fun v hv => Finset.mem_image_of_mem fR hv)
          rw [hfib, Nat.cast_sum]
          refine Finset.sum_le_sum fun x hx => ?_
          have hxA : x ∈ A := hJR_sub hx
          have hle_c : (IR_v.filter (fun v => fR v = x)).card ≤ c ⟨x, hxA⟩ := by
            rw [← hfiber_card ⟨x, hxA⟩]
            let g : Fin n → Fin m0 := fun v =>
              if h : n0 ≤ v.1 ∧ v.1 - n0 < m0 then ⟨v.1 - n0, h.2⟩ else ⟨0, hm0pos⟩
            refine Finset.card_le_card_of_injOn g ?_ ?_
            · intro v hv
              have hvIR := (Finset.mem_filter.mp hv).1
              have hfx := (Finset.mem_filter.mp hv).2
              have hv2 := (Finset.mem_filter.mp hvIR).2
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, g, hv2, ↓reduceDIte]
              simp only [fR, dif_pos hv2] at hfx
              exact Subtype.ext hfx
            · intro u hu v hv huv
              have hu2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
              have hv2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
              simp only [g, dif_pos hu2, dif_pos hv2] at huv
              have hval : u.1 - n0 = v.1 - n0 := congrArg (Fin.val : Fin m0 → ℕ) huv
              exact Fin.ext (by omega)
          exact (Nat.cast_le.mpr hle_c).trans (hc_le ⟨x, hxA⟩)
        calc (IR_v.card : ℝ) ≤ ∑ x ∈ JR, (n0 : ℝ) * w x := hcardR
          _ = (n0 : ℝ) * ∑ x ∈ JR, w x := by rw [← Finset.mul_sum]
          _ ≤ (n0 : ℝ) * δ := mul_le_mul_of_nonneg_left (hind JR hJR_sub hJR_sep) (Nat.cast_nonneg n0)
    have hsplitR : (I.card : ℝ) ≤ (IL_v.card : ℝ) + (IR_v.card : ℝ) + (IN_v.card : ℝ) := by
      exact_mod_cast hcard_split
    have h2n0R : 2 * (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n0
    nlinarith
  have hedgeG : (n : ℝ) ^ 2 / 8 - η / 4 * (n : ℝ) ^ 2 - (n : ℝ) / 4 - (n : ℝ) * (A.card : ℝ) ≤
      G.edgeFinset.card := by
    let Pcross : Finset (Fin m0 × Fin m0) :=
      Finset.univ.filter fun p => E < ip (π p.1).1 (π p.2).1
    let toEdge : Fin m0 × Fin m0 → Sym2 (Fin n) :=
      fun p => s(⟨p.1.1, by omega⟩, ⟨n0 + p.2.1, by omega⟩)
    have hinj_e : Function.Injective toEdge := by
      intro p q hpq
      dsimp [toEdge] at hpq
      rw [Sym2.eq_iff] at hpq
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hp1 : p.1.1 = q.1.1 := congrArg (Fin.val : Fin n → ℕ) h1
        have hp2 : n0 + p.2.1 = n0 + q.2.1 := congrArg (Fin.val : Fin n → ℕ) h2
        exact Prod.ext (Fin.ext hp1) (Fin.ext (by omega))
      · have hp1 : p.1.1 = n0 + q.2.1 := congrArg (Fin.val : Fin n → ℕ) h1
        omega
    have hsub_e : Pcross.image toEdge ⊆ G.edgeFinset := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
      rw [SimpleGraph.mem_edgeFinset]
      have hip : E < ip (π p.1).1 (π p.2).1 := (Finset.mem_filter.mp hp).2
      have ht1 : tag ⟨p.1.1, by omega⟩ = some (false, π p.1) := by
        simp [tag, p.1.2]
      have ht2 : tag ⟨n0 + p.2.1, by omega⟩ = some (true, π p.2) := by
        have hnot : ¬ (n0 + p.2.1) < m0 := by omega
        have hcond : n0 ≤ n0 + p.2.1 ∧ n0 + p.2.1 - n0 < m0 := ⟨by omega, by omega⟩
        have hfin : (⟨n0 + p.2.1 - n0, hcond.2⟩ : Fin m0) = p.2 := Fin.ext (Nat.add_sub_cancel_left n0 p.2.1)
        simp only [tag, dif_neg hnot, dif_pos hcond, hfin]
      show G.Adj ⟨p.1.1, by omega⟩ ⟨n0 + p.2.1, by omega⟩
      simp [G, ht1, ht2, hip]
    have hPcard : (Pcross.card : ℝ) =
        ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
          if E < ip x.1 y.1 then (c x : ℝ) * (c y : ℝ) else 0 := by
      have hnat : Pcross.card =
          ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            if E < ip x.1 y.1 then c x * c y else 0 := by
        have h1 : Pcross.card = ∑ p : Fin m0 × Fin m0, if E < ip (π p.1).1 (π p.2).1 then 1 else 0 := by
          dsimp [Pcross]; rw [Finset.card_filter]
        rw [h1, Fintype.sum_prod_type]
        have hfib1 : ∀ f : Fin m0 → ℕ, ∑ i : Fin m0, f i =
            ∑ x : {x // x ∈ A}, ∑ i ∈ Finset.univ.filter (fun i : Fin m0 => π i = x), f i := by
          intro f
          exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) f).symm
        rw [hfib1]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hstep1 : ∀ i ∈ Finset.univ.filter (fun i : Fin m0 => π i = x),
            (∑ j : Fin m0, if E < ip (π i).1 (π j).1 then 1 else 0) =
            ∑ y : {x // x ∈ A}, if E < ip x.1 y.1 then c y else 0 := by
          intro i hi
          have hpi : π i = x := (Finset.mem_filter.mp hi).2
          rw [hpi, hfib1]
          refine Finset.sum_congr rfl fun y _ => ?_
          have hstep2 : ∑ j ∈ Finset.univ.filter (fun j : Fin m0 => π j = y),
              (if E < ip x.1 (π j).1 then (1 : ℕ) else 0) =
              ∑ _j ∈ Finset.univ.filter (fun j : Fin m0 => π j = y),
              (if E < ip x.1 y.1 then (1 : ℕ) else 0) :=
            Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
          rw [hstep2, Finset.sum_const, hfiber_card y, smul_eq_mul]
          split_ifs <;> simp
        rw [Finset.sum_congr rfl hstep1, Finset.sum_const, hfiber_card x, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
      rw [hnat, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp
    have hP_ge : (n0 : ℝ) ^ 2 * (1 / 2 - η) - 2 * (n0 : ℝ) * (A.card : ℝ) ≤ (Pcross.card : ℝ) := by
      rw [hPcard]
      have hterm : ∀ x : {x // x ∈ A}, ∀ y : {x // x ∈ A},
          (if E < ip x.1 y.1 then (n0 : ℝ) * w x.1 * ((n0 : ℝ) * w y.1) else 0) -
            ((n0 : ℝ) * w x.1 + (n0 : ℝ) * w y.1) ≤
          if E < ip x.1 y.1 then (c x : ℝ) * (c y : ℝ) else 0 := by
        intro x y
        have hwx : 0 ≤ (n0 : ℝ) * w x.1 := mul_nonneg (Nat.cast_nonneg n0) (hw0 x.1 x.2)
        have hwy : 0 ≤ (n0 : ℝ) * w y.1 := mul_nonneg (Nat.cast_nonneg n0) (hw0 y.1 y.2)
        split_ifs
        · have hf := floor_mul_ge ((n0 : ℝ) * w x.1) ((n0 : ℝ) * w y.1) hwx hwy
          dsimp [c]; linarith
        · linarith
      have hsum_ge := Finset.sum_le_sum (s := (Finset.univ : Finset {x // x ∈ A})) fun x _ =>
        Finset.sum_le_sum (s := (Finset.univ : Finset {x // x ∈ A})) fun y _ => hterm x y
      have hcross_sub :
          ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A}, (if E < ip x.1 y.1 then w x.1 * w y.1 else 0) =
          ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0 := by
        simp_rw [Finset.univ_eq_attach]
        rw [Finset.sum_attach A (fun x => ∑ y ∈ A.attach, if E < ip x y.1 then w x * w y.1 else 0)]
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_attach A (fun y => if E < ip x y then w x * w y else 0)
      have hmain_eq : ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            (if E < ip x.1 y.1 then (n0 : ℝ) * w x.1 * ((n0 : ℝ) * w y.1) else 0) =
          (n0 : ℝ) ^ 2 * (∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0) := by
        rw [← hcross_sub, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
      have herr_eq : ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            ((n0 : ℝ) * w x.1 + (n0 : ℝ) * w y.1) = 2 * (n0 : ℝ) * (A.card : ℝ) := by
        have hcard_sub : (Fintype.card {x // x ∈ A} : ℝ) = (A.card : ℝ) := by simp [Fintype.card_coe]
        simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_sub,
          ← Finset.mul_sum, hsum_sub, mul_one]
        ring
      have hsub_split : ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            ((if E < ip x.1 y.1 then (n0 : ℝ) * w x.1 * ((n0 : ℝ) * w y.1) else 0) -
              ((n0 : ℝ) * w x.1 + (n0 : ℝ) * w y.1)) =
          (n0 : ℝ) ^ 2 * (∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0) -
            2 * (n0 : ℝ) * (A.card : ℝ) := by
        simp_rw [Finset.sum_sub_distrib]
        rw [hmain_eq, herr_eq]
      rw [hsub_split] at hsum_ge
      have hmul_cr := mul_le_mul_of_nonneg_left hcross (sq_nonneg (n0 : ℝ))
      linarith
    have hcard_e : (Pcross.card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      have h1 : Pcross.card = (Pcross.image toEdge).card := (Finset.card_image_of_injective Pcross hinj_e).symm
      have h2 : (Pcross.image toEdge).card ≤ G.edgeFinset.card := Finset.card_le_card hsub_e
      exact_mod_cast (h1 ▸ h2)
    have h2n0R : 2 * (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n0
    have hn_leR : (n : ℝ) ≤ 2 * (n0 : ℝ) + 1 := by exact_mod_cast hn_le_2n0
    have hn0_sq_ge : (n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 ≤ (n0 : ℝ) ^ 2 := by nlinarith
    have hn0_sq_le : (n0 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by nlinarith
    have hη_term : -η / 4 * (n : ℝ) ^ 2 ≤ -η * (n0 : ℝ) ^ 2 := by nlinarith
    have hA_term : 2 * (n0 : ℝ) * (A.card : ℝ) ≤ (n : ℝ) * (A.card : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
    linarith
  exact ⟨G, side, hcf, htri, hbal, hindG, hedgeG⟩

/- ### Module 5: Asymptotic parameter tuning and final theorem for `Erdos615` -/

private lemma box_card_eq (d σ : ℕ) : (box d σ).card = (2 * σ + 1) ^ d := by
  dsimp [box]
  rw [Fintype.card_piFinset_const, Int.card_Icc]
  have : (σ : ℤ) + 1 - -(σ : ℤ) = ((2 * σ + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

private lemma eventually_erdos615_base (εg ε_raw : ℝ) (_hεg : 0 < εg) (hε_raw : 0 < ε_raw) :
    ∀ᶠ n : ℕ in atTop,
      let L := Real.log (n : ℝ)
      let LL := Real.log L
      1000 ≤ n ∧
      (10 : ℝ) ≤ LL ∧
      (4000 : ℝ) * LL ^ 2 ≤ L ∧
      (max 200 (200 / εg)) ^ 2 ≤ L / (4 * LL) ∧
      (n : ℝ) / 4 + (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ (ε_raw / 2) * (n : ℝ) ^ 2 := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, 1000 ≤ n := eventually_ge_atTop 1000
  have h2 : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
    hll.eventually (eventually_ge_atTop 10)
  have h3 : ∀ᶠ n : ℕ in atTop, (4000 : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 ≤ Real.log (n : ℝ) := by
    have hpow := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have hbound := hpow.bound (show (0 : ℝ) < 1 / 100 by norm_num)
    have hev := hlog.eventually hbound
    filter_upwards [hev, h2, eventually_ge_atTop 10] with n hn hll10 hn10
    have hnR10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
    have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    simp only [Real.norm_eq_abs, abs_of_pos (show 0 < Real.log (Real.log (n : ℝ)) by linarith),
      abs_of_pos (Real.rpow_pos_of_pos hLpos _)] at hn
    have hsq : (Real.log (Real.log (n : ℝ))) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 * ((Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
      have : (0 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by linarith
      nlinarith
    have hrpow : ((Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = Real.log (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
    rw [hrpow] at hsq
    nlinarith
  have h4 : ∀ᶠ n : ℕ in atTop,
      (max 200 (200 / εg)) ^ 2 ≤ Real.log (n : ℝ) / (4 * Real.log (Real.log (n : ℝ))) := by
    set M : ℝ := (max 200 (200 / εg)) ^ 2
    have hM_nn : 0 ≤ M := sq_nonneg _
    have hll_big : ∀ᶠ n : ℕ in atTop, M / 1000 ≤ Real.log (Real.log (n : ℝ)) :=
      hll.eventually (eventually_ge_atTop (M / 1000))
    filter_upwards [h2, h3, hll_big] with n hll10 hLge hllM
    have hllpos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log (Real.log (n : ℝ)))]
    nlinarith
  have h5 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 4 + (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ (ε_raw / 2) * (n : ℝ) ^ 2 := by
    obtain ⟨K, hK⟩ := exists_nat_ge ((4 / ε_raw) ^ 3 + 1000)
    filter_upwards [eventually_ge_atTop (max K 1000)] with n hn
    have hnK : K ≤ n := le_trans (le_max_left _ _) hn
    have hn1000 : 1000 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1000
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hn_ge_cub : (4 / ε_raw) ^ 3 ≤ (n : ℝ) := by
      have : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnK
      linarith
    have hrpow_ge : 4 / ε_raw ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      have h1 : ((4 / ε_raw) ^ 3) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hn_ge_cub (by norm_num)
      have h2 : ((4 / ε_raw) ^ 3) ^ (1 / 3 : ℝ) = 4 / ε_raw := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4 / ε_raw)]
        norm_num
      linarith
    have hn13_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have h23 : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hnpos]; norm_num
    have h23_ge : 4 / ε_raw ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by nlinarith
    have hmul : (4 / ε_raw) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) := by
      have h1 : (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) := by
        rw [← Real.rpow_add hnpos]; norm_num
      have h2 := mul_le_mul_of_nonneg_right h23_ge (Real.rpow_nonneg hnpos.le (1 / 3 : ℝ))
      linarith
    have hclear : 4 * (n : ℝ) ^ (1 / 3 : ℝ) ≤ ε_raw * (n : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hmul hε_raw.le
      have h2 : ε_raw * ((4 / ε_raw) * (n : ℝ) ^ (1 / 3 : ℝ)) = 4 * (n : ℝ) ^ (1 / 3 : ℝ) := by
        field_simp [hε_raw.ne']
      linarith
    have hmain : (n : ℝ) * (2 * (n : ℝ) ^ (1 / 3 : ℝ)) ≤ (ε_raw / 2) * (n : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  filter_upwards [h1, h2, h3, h4, h5] with n hn1 hn2 hn3 hn4 hn5
  exact ⟨hn1, hn2, hn3, hn4, hn5⟩

set_option maxHeartbeats 600000 in
private lemma erdos615_flz_proof :
    type_of% @Erdos615.erdos_615.variants.fox_loh_zhao := by
  intro f hf hfo ε_raw hε_raw
  let εg : ℝ := min (ε_raw / 100) (1 / 1000)
  have hεg_pos : 0 < εg := lt_min (by positivity) (by norm_num)
  have hεg_le_raw : εg ≤ ε_raw / 100 := min_le_left _ _
  have hεg_le_small : εg ≤ 1 / 1000 := min_le_right _ _
  have hfo_ev : ∀ᶠ n : ℕ in atTop,
      |f n / Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))| < εg / 100 := by
    have hball := Metric.tendsto_nhds.mp hfo (εg / 100) (by positivity)
    filter_upwards [hball] with n hn
    rwa [Real.dist_eq, sub_zero] at hn
  filter_upwards [eventually_erdos615_base εg ε_raw hεg_pos hε_raw, hfo_ev] with n hn hfn_o
  rcases hn with ⟨hn1000, hLL10, hL_ge, hM_le, hedge_err⟩
  have hn6 : 6 ≤ n := by omega
  set L : ℝ := Real.log (n : ℝ)
  set LL : ℝ := Real.log L
  have hLL_pos : 0 < LL := by linarith
  have hL_pos : 0 < L := by nlinarith only [hL_ge, hLL10]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnR1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1000
  let d : ℕ := Nat.floor (L / (3 * LL))
  have hd_real_le : (d : ℝ) ≤ L / (3 * LL) := Nat.floor_le (by positivity)
  have hd_real_gt : L / (3 * LL) - 1 < (d : ℝ) := Nat.sub_one_lt_floor _
  have hd_ge_quarter : L / (4 * LL) ≤ (d : ℝ) := by
    have hdiff : L / (3 * LL) - L / (4 * LL) = L / (12 * LL) := by
      field_simp [hLL_pos.ne']; ring
    have h12 : (1 : ℝ) ≤ L / (12 * LL) := by
      rw [one_le_div (by positivity : (0 : ℝ) < 12 * LL)]
      nlinarith only [hL_ge, hLL10]
    linarith only [hd_real_gt, hdiff, h12]
  have hM_le_d : (max 200 (200 / εg)) ^ 2 ≤ (d : ℝ) := le_trans hM_le hd_ge_quarter
  have hsqrt_d_ge_M : max 200 (200 / εg) ≤ Real.sqrt (d : ℝ) := by
    have hMnn : 0 ≤ max (200 : ℝ) (200 / εg) := by positivity
    calc max 200 (200 / εg) = Real.sqrt ((max 200 (200 / εg)) ^ 2) := (Real.sqrt_sq hMnn).symm
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hM_le_d
  have hsqrt_d_ge_200 : (200 : ℝ) ≤ Real.sqrt (d : ℝ) := le_trans (le_max_left _ _) hsqrt_d_ge_M
  have hsqrt_d_ge_div : 200 / εg ≤ Real.sqrt (d : ℝ) := le_trans (le_max_right _ _) hsqrt_d_ge_M
  have hd_ge_650 : (650 : ℝ) ≤ (d : ℝ) := by
    have h1 : (200 : ℝ) ^ 2 ≤ (max 200 (200 / εg)) ^ 2 := by
      have : (200 : ℝ) ≤ max 200 (200 / εg) := le_max_left _ _
      nlinarith only [this]
    linarith only [h1, hM_le_d]
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) ≤ (d : ℝ) := by linarith only [hd_ge_650]
    exact Nat.one_le_cast.mp this
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hεg_sqrt_ge : (200 : ℝ) ≤ εg * Real.sqrt (d : ℝ) := by
    have h1 := (div_le_iff₀ hεg_pos).mp hsqrt_d_ge_div
    linarith only [h1]
  have hsmall : 9 ≤ εg * Real.sqrt (d : ℝ) := by linarith only [hεg_sqrt_ge]
  have h18ε : 18 * εg < Real.sqrt (d : ℝ) := by linarith only [hεg_le_small, hsqrt_d_ge_200]
  -- Bound f n in terms of sqrt d and L
  have hsqrt_ratio_pos : 0 < Real.sqrt (L / LL) := Real.sqrt_pos.mpr (div_pos hL_pos hLL_pos)
  have hfn_le_ratio : f n ≤ (εg / 100) * Real.sqrt (L / LL) := by
    have h1 : f n / Real.sqrt (L / LL) < εg / 100 := (abs_lt.mp hfn_o).2
    have h2 := (div_lt_iff₀ hsqrt_ratio_pos).mp h1
    linarith only [h2]
  have hsqrt_ratio_le_2d : Real.sqrt (L / LL) ≤ 2 * Real.sqrt (d : ℝ) := by
    have h1 : L / LL ≤ 4 * (d : ℝ) := by
      have h2 : L / (4 * LL) = (L / LL) / 4 := by ring
      linarith only [hd_ge_quarter, h2]
    have h2 : Real.sqrt (L / LL) ≤ Real.sqrt (4 * (d : ℝ)) := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (4 * (d : ℝ)) = 2 * Real.sqrt (d : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [this]
    linarith only [h2, h3]
  have hfn_le_d : f n ≤ (εg / 50) * Real.sqrt (d : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hsqrt_ratio_le_2d (by positivity : 0 ≤ εg / 100)
    linarith only [hfn_le_ratio, hm]
  have hfn_le_L3 : f n ≤ L / 3 := by
    have hL1 : (1 : ℝ) ≤ L := by nlinarith only [hL_ge, hLL10]
    have hratio_le_L : L / LL ≤ L ^ 2 := by
      have h1 : L / LL ≤ L := div_le_self hL_pos.le (by linarith only [hLL10])
      nlinarith only [h1, hL1]
    have hsqrt_le_L : Real.sqrt (L / LL) ≤ L := by
      calc Real.sqrt (L / LL) ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt hratio_le_L
        _ = L := Real.sqrt_sq hL_pos.le
    have hm := mul_le_mul_of_nonneg_left hsqrt_le_L (by positivity : 0 ≤ εg / 100)
    nlinarith only [hfn_le_ratio, hm, hεg_le_small, hL_pos]
  -- Choose N for sharp Fejér anti-concentration: 16 / N ≤ εg
  let N : ℕ := Nat.ceil (16 / εg) + 1
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN_bd : 16 / (N : ℝ) ≤ εg := by
    have h1 : 16 / εg ≤ (N : ℝ) := by
      have := Nat.le_ceil (16 / εg)
      dsimp [N]; push_cast; linarith
    have h2 : 16 ≤ (N : ℝ) * εg := (div_le_iff₀ hεg_pos).mp h1
    exact (div_le_iff₀ hNpos).mpr (by linarith only [h2])
  -- Define shell A, weights w, thresholds E, C_thr
  obtain ⟨hv1_lo, hv1_hi, _⟩ := v1_bounds d hd1
  have hv1_pos : 0 < v1 d := by nlinarith only [hv1_lo, hdpos]
  let E : ℝ := εg * v1 d * Real.sqrt (d : ℝ)
  have hE_pos : 0 < E := by positivity
  let C_thr : ℝ := Real.sqrt E
  have hC_nn : 0 ≤ C_thr := Real.sqrt_nonneg E
  have hC_sq : C_thr ^ 2 = E := Real.sq_sqrt hE_pos.le
  let A : Finset (Fin d → ℤ) := (box d d).filter (fun x => (d : ℝ) / 2 * v1 d ≤ normSq x)
  let pA : ℝ := ∑ x ∈ A, pd d d x
  have hpA_ge : 1 / 2 ≤ pA := by
    have hcheb := chebyshev_shell d d hd1 hd1
    have h324 : 324 / (d : ℝ) ≤ 1 / 2 := by rw [div_le_iff₀ hdpos]; linarith only [hd_ge_650]
    linarith only [hcheb, h324]
  have hpA_pos : 0 < pA := by linarith only [hpA_ge]
  let w : (Fin d → ℤ) → ℝ := fun x => pd d d x / pA
  have hw0 : ∀ x ∈ A, 0 ≤ w x := fun x _ => div_nonneg (pd_nonneg d d x) hpA_pos.le
  have hw1 : ∑ x ∈ A, w x = 1 := by
    simp only [w, ← Finset.sum_div]; exact div_self hpA_pos.ne'
  have hnorm : ∀ x ∈ A, 9 * C_thr ^ 2 < normSq x := by
    intro x hx
    have hx_n : (d : ℝ) / 2 * v1 d ≤ normSq x := (Finset.mem_filter.mp hx).2
    rw [hC_sq]; dsimp [E]
    have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hdpos.le
    have h2 : 18 * εg * Real.sqrt (d : ℝ) < (d : ℝ) := by
      have := mul_lt_mul_of_pos_right h18ε hsqrt_d_pos
      linarith only [this, hsq]
    nlinarith only [hx_n, h2, hv1_pos]
  have hA_card_le : (A.card : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hsub : A.card ≤ (box d d).card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [box_card_eq d d] at hsub
    have hsubR : (A.card : ℝ) ≤ ((2 * d + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast hsub
    have h2d1_le_L : ((2 * d + 1 : ℕ) : ℝ) ≤ L := by
      push_cast
      have h1 : 2 * (d : ℝ) ≤ 2 * (L / (3 * LL)) := by linarith only [hd_real_le]
      have h3 : 2 * L / (3 * LL) ≤ L / 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * LL) (by norm_num)]
        nlinarith only [hLL10, hL_pos]
      have h4 : 2 * (L / (3 * LL)) = 2 * L / (3 * LL) := by ring
      have hL2 : (2 : ℝ) ≤ L := by nlinarith only [hL_ge, hLL10]
      linarith only [h1, h3, h4, hL2]
    have h2d1_pos : (0 : ℝ) < ((2 * d + 1 : ℕ) : ℝ) := by positivity
    have hlog_bd : (d : ℝ) * Real.log ((2 * d + 1 : ℕ) : ℝ) ≤ L / 3 := by
      have hlog_le : Real.log ((2 * d + 1 : ℕ) : ℝ) ≤ LL := Real.log_le_log h2d1_pos h2d1_le_L
      have h2d1_ge1 : (1 : ℝ) ≤ ((2 * d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * d + 1)
      have hmul : (d : ℝ) * Real.log ((2 * d + 1 : ℕ) : ℝ) ≤ (L / (3 * LL)) * LL :=
        mul_le_mul hd_real_le hlog_le (Real.log_nonneg h2d1_ge1) (by positivity)
      have heq : (L / (3 * LL)) * LL = L / 3 := by field_simp [hLL_pos.ne']
      linarith only [hmul, heq]
    have hexp_eq : ((2 * d + 1 : ℕ) : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log ((2 * d + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos h2d1_pos]; ring_nf
    have hn13_eq : (n : ℝ) ^ (1 / 3 : ℝ) = Real.exp (L / 3) := by
      rw [Real.rpow_def_of_pos hn_pos]; dsimp [L]; ring_nf
    rw [hexp_eq] at hsubR
    rw [hn13_eq]
    exact hsubR.trans (Real.exp_le_exp.mpr hlog_bd)
  -- Independence bound: δ := (1 / 2) * Real.exp (-f n)
  let δ : ℝ := (1 / 2) * Real.exp (-f n)
  have hδ_pos : 0 < δ := by positivity
  have hind : ∀ I ⊆ A, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → 4 * C_thr ^ 2 < normSq (x + y)) →
      ∑ x ∈ I, w x ≤ δ := by
    intro I hIA hIsep
    have hI_all : ∀ x ∈ I, ∀ y ∈ I, 4 * C_thr ^ 2 < normSq (x + y) := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst hxy
        have hnx : 9 * C_thr ^ 2 < normSq x := hnorm x (hIA hx)
        have h2x : normSq (x + x) = 4 * normSq x := by
          simp only [normSq, Pi.add_apply, Int.cast_add, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => by ring
        rw [h2x]; linarith [sq_nonneg C_thr]
      · exact hIsep x hx y hy hxy
    have hI_box : I ⊆ box d d := hIA.trans (Finset.filter_subset _ _)
    have hpl := discrete_gaussian_indep_bound d hd1 C_thr hC_nn I hI_box hI_all
    have hexp_le : Real.exp (1 / 2 - C_thr ^ 2 / (2 * (d : ℝ) ^ 2)) ≤ (1 / 4) * Real.exp (-f n) := by
      have h1 : (εg / 18) * Real.sqrt (d : ℝ) ≤ C_thr ^ 2 / (2 * (d : ℝ) ^ 2) := by
        rw [hC_sq]; dsimp [E]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ 2)]
        have h2 : (εg / 18) * (2 * (d : ℝ) ^ 2) ≤ εg * v1 d := by nlinarith only [hv1_lo, hεg_pos]
        have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (d : ℝ))
        linarith only [h3]
      have hlog4 : Real.log 4 ≤ 2 := by
        have h4 : (4 : ℝ) ≤ Real.exp 2 := by
          have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith only [he1, he2]
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
        rwa [Real.log_exp] at this
      have hgap : 1 / 2 + Real.log 4 + f n ≤ (εg / 18) * Real.sqrt (d : ℝ) := by
        linarith only [hlog4, hfn_le_d, hεg_sqrt_ge]
      have h3 : 1 / 2 - C_thr ^ 2 / (2 * (d : ℝ) ^ 2) ≤ -Real.log 4 + (-f n) := by
        linarith only [h1, hgap]
      calc Real.exp (1 / 2 - C_thr ^ 2 / (2 * (d : ℝ) ^ 2))
          ≤ Real.exp (-Real.log 4 + (-f n)) := Real.exp_le_exp.mpr h3
        _ = Real.exp (-Real.log 4) * Real.exp (-f n) := Real.exp_add _ _
        _ = (1 / 4) * Real.exp (-f n) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4), one_div]
    have hsum_w : ∑ x ∈ I, w x = (∑ x ∈ I, pd d d x) / pA := by
      simp only [w, ← Finset.sum_div]
    rw [hsum_w, div_le_iff₀ hpA_pos]
    calc ∑ x ∈ I, pd d d x ≤ Real.exp (1 / 2 - C_thr ^ 2 / (2 * (d : ℝ) ^ 2)) := hpl
      _ ≤ (1 / 4) * Real.exp (-f n) := hexp_le
      _ = δ * (1 / 2) := by dsimp [δ]; ring
      _ ≤ δ * pA := mul_le_mul_of_nonneg_left hpA_ge hδ_pos.le
  -- Cross edge bound with η := 98 * εg
  let η : ℝ := 98 * εg
  have hη_pos : 0 < η := by positivity
  have hcross : 1 / 2 - η ≤ ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0 := by
    have hper_x : ∀ x ∈ A, 1 / 2 - η ≤ ∑ y ∈ A, if E < ip x y then w y else 0 := by
      intro x hx
      have hx_box : x ∈ box d d := (Finset.mem_filter.mp hx).1
      have hx_norm : (d : ℝ) / 2 * v1 d ≤ normSq x := (Finset.mem_filter.mp hx).2
      have hfejer := fejer_anticoncentration_sharp d d N εg hd1 hd1 hN1 hεg_pos hsmall x hx_box hx_norm
      have hmid_le : ∑ y ∈ A.filter (fun y => |ip x y| ≤ E), w y ≤ η := by
        have hsub : A.filter (fun y => |ip x y| ≤ E) ⊆ (box d d).filter (fun y => |ip x y| ≤ E) :=
          Finset.filter_subset_filter _ (Finset.filter_subset _ _)
        have h1 : ∑ y ∈ A.filter (fun y => |ip x y| ≤ E), pd d d y ≤ 49 * εg := by
          have h2 := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => pd_nonneg d d y)).trans hfejer
          linarith only [h2, hN_bd]
        simp only [w, ← Finset.sum_div]
        rw [div_le_iff₀ hpA_pos]
        calc ∑ y ∈ A.filter (fun y => |ip x y| ≤ E), pd d d y
            ≤ 49 * εg := h1
          _ = η * (1 / 2) := by dsimp [η]; ring
          _ ≤ η * pA := mul_le_mul_of_nonneg_left hpA_ge hη_pos.le
      have hsym : ∑ y ∈ A.filter (fun y => E < ip x y), w y =
          ∑ y ∈ A.filter (fun y => ip x y < -E), w y := by
        refine Finset.sum_bij (fun y _ => -y) ?_ ?_ ?_ ?_
        · intro y hy
          rw [Finset.mem_filter] at hy ⊢
          rcases hy with ⟨hyA, hyip⟩
          rw [Finset.mem_filter] at hyA ⊢
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [mem_box_iff]; intro r; have := mem_box_iff.mp hyA.1 r
            simp only [Pi.neg_apply]; omega
          · rw [normSq_neg]; exact hyA.2
          · rw [ip_neg_right]; linarith
        · intro a _ b _ hab; exact neg_inj.mp hab
        · intro y hy
          rw [Finset.mem_filter] at hy
          rcases hy with ⟨hyA, hyip⟩
          rw [Finset.mem_filter] at hyA
          refine ⟨-y, ?_, neg_neg y⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
          · rw [mem_box_iff]; intro r; have := mem_box_iff.mp hyA.1 r
            simp only [Pi.neg_apply]; omega
          · rw [normSq_neg]; exact hyA.2
          · rw [ip_neg_right]; linarith
        · intro y _; simp [w, pd_neg]
      have hpart : (∑ y ∈ A.filter (fun y => E < ip x y), w y) +
          (∑ y ∈ A.filter (fun y => ip x y < -E), w y) +
          (∑ y ∈ A.filter (fun y => |ip x y| ≤ E), w y) = 1 := by
        rw [← hw1]
        have hrew : ∀ y ∈ A, w y =
            (if E < ip x y then w y else 0) +
            (if ip x y < -E then w y else 0) +
            (if |ip x y| ≤ E then w y else 0) := by
          intro y _
          by_cases h1 : E < ip x y
          · have h2 : ¬ (ip x y < -E) := by linarith
            have h3 : ¬ (|ip x y| ≤ E) := by intro hab; linarith [(abs_le.mp hab).2]
            simp [h1, h2, h3]
          · by_cases h2 : ip x y < -E
            · have h3 : ¬ (|ip x y| ≤ E) := by intro hab; linarith [(abs_le.mp hab).1]
              simp [h1, h2, h3]
            · have h3 : |ip x y| ≤ E := by rw [abs_le]; constructor <;> linarith
              simp [h1, h2, h3]
        simp_rw [Finset.sum_filter]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact (Finset.sum_congr rfl hrew).symm
      rw [← Finset.sum_filter]
      linarith only [hsym, hpart, hmid_le, hη_pos]
    calc 1 / 2 - η = (∑ x ∈ A, w x) * (1 / 2 - η) := by rw [hw1, one_mul]
      _ = ∑ x ∈ A, w x * (1 / 2 - η) := by rw [Finset.sum_mul]
      _ ≤ ∑ x ∈ A, w x * (∑ y ∈ A, if E < ip x y then w y else 0) :=
          Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hper_x x hx) (hw0 x hx)
      _ = ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases h : E < ip x y <;> simp [h]
  -- Build direct seed on Fin n (no densification needed!)
  obtain ⟨G0, _, hcf0, _, _, hind0, hedge0⟩ :=
    exists_seed_on_fin A w C_thr E η δ n hn6 hE_pos hC_sq.le hη_pos.le hδ_pos.le
      hw0 hw1 hnorm hind hcross
  refine ⟨G0, hcf0, ?_, ?_⟩
  · -- Independence bound: δ * n + 2 * A.card + 1 ≤ n * exp (-f n)
    have hexp_ge : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ Real.exp (-f n) := by
      have h1 : (n : ℝ) ^ (-(1 / 3 : ℝ)) = Real.exp (-(L / 3)) := by
        rw [Real.rpow_def_of_pos hn_pos]; dsimp [L]; ring_nf
      rw [h1]
      exact Real.exp_le_exp.mpr (by linarith only [hfn_le_L3])
    have hn23_eq : (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [show (2 / 3 : ℝ) = 1 + (-(1 / 3 : ℝ)) by norm_num, Real.rpow_add hn_pos, Real.rpow_one]
    have hn13_ge10 : (10 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      have h1 : (10 : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) := by linarith only [hnR1000]
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h3 : ((10 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = 10 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]; norm_num
      linarith only [h2, h3]
    have h2A1_le : 2 * (A.card : ℝ) + 1 ≤ (1 / 2) * (n : ℝ) ^ (2 / 3 : ℝ) := by
      have hprod : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hn_pos]; norm_num
      nlinarith only [hA_card_le, hn13_ge10, hprod]
    have hhalf_ge : (1 / 2) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (1 / 2) * (n : ℝ) * Real.exp (-f n) := by
      have hm := mul_le_mul_of_nonneg_left hexp_ge (by positivity : 0 ≤ (1 / 2) * (n : ℝ))
      nlinarith only [hm, hn23_eq]
    have hδeq : δ * (n : ℝ) = (1 / 2) * (n : ℝ) * Real.exp (-f n) := by dsimp [δ]; ring
    linarith only [hind0, hδeq, h2A1_le, hhalf_ge]
  · -- Edge bound: (1/8 - ε_raw) * n^2 ≤ G0.edgeFinset.card
    have hη_le : η / 4 ≤ ε_raw / 4 := by dsimp [η]; linarith only [hεg_le_raw, hε_raw]
    have h1 : (η / 4) * (n : ℝ) ^ 2 ≤ (ε_raw / 4) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hη_le (sq_nonneg (n : ℝ))
    have h2 : (n : ℝ) * (A.card : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hA_card_le hn_pos.le
    have h3 : (1 / 8 - ε_raw) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 / 8 - ε_raw * (n : ℝ) ^ 2 := by ring
    linarith only [hedge0, h1, h2, hedge_err, h3, mul_nonneg hε_raw.le (sq_nonneg (n : ℝ))]

end

end Erdos615FLZ

theorem OMA.solution : type_of% @Erdos615.erdos_615.variants.fox_loh_zhao :=
  Erdos615FLZ.erdos615_flz_proof
