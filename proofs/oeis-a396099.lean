import OMAStatements.S_oeis_a396099
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a396099

open OMA.S_oeis_a396099

/-- Target mod-4 series `f(x) = (x + x^2 + 2x^3) / (1 + x^2)` in `(ZMod 4)[[x]]`. -/
private def fMod : ℕ → ZMod 4
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n => if n % 4 = 2 ∨ n % 4 = 3 then 1 else 3

/-- Series `1 + x^2` in `(ZMod 4)[[x]]`. -/
private def qMod : ℕ → ZMod 4 := fun n => if n = 0 ∨ n = 2 then 1 else 0

/-- Series `x + x^2 + 2x^3` in `(ZMod 4)[[x]]`. -/
private def pMod : ℕ → ZMod 4 := fun n =>
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else 0

/-- Series `x + 2x^2` in `(ZMod 4)[[x]]`. -/
private def gMod : ℕ → ZMod 4 := fun n =>
  if n = 1 then 1 else if n = 2 then 2 else 0

/-- Series `x + 3x^2 + 2x^3` in `(ZMod 4)[[x]]`. -/
private def rMod : ℕ → ZMod 4 := fun n =>
  if n = 1 then 1 else if n = 2 then 3 else if n = 3 then 2 else 0

/-- Unit series `1` in `R[[x]]`. -/
private def oneSeq {R : Type*} [CommRing R] : ℕ → R := fun n => if n = 0 then 1 else 0

private lemma mulSeq_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u v : ℕ → R) (n : ℕ) :
    φ (mulSeq u v n) = mulSeq (fun i => φ (u i)) (fun i => φ (v i)) n := by
  simp only [mulSeq, map_sum, map_mul]

private lemma powSeq_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ℕ → R) :
    ∀ k n : ℕ, φ (powSeq g k n) = powSeq (fun i => φ (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; dsimp [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

private lemma comp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (comp f g n) = comp (fun i => φ (f i)) (fun i => φ (g i)) n := by
  simp only [comp, map_sum, map_mul, powSeq_map]

private lemma iterComp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℕ → R) :
    ∀ r n : ℕ, φ (iterComp f r n) = iterComp (fun i => φ (f i)) r n := by
  intro r
  induction r with
  | zero => intro n; dsimp [iterComp]; split_ifs <;> simp
  | succ r ih =>
    intro n
    simp only [iterComp, comp_map]
    have hfun : (fun i => φ (iterComp f r i)) = iterComp (fun i => φ (f i)) r := by
      ext i; exact ih i
    rw [hfun]

private lemma powSeq_congr {R : Type*} [CommRing R] {g1 g2 : ℕ → R} {N : ℕ}
    (hg : ∀ i ≤ N, g1 i = g2 i) : ∀ k n : ℕ, n ≤ N → powSeq g1 k n = powSeq g2 k n := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hg i (le_trans hin hn), ih (n - i) (by omega)]

private lemma comp_congr {R : Type*} [CommRing R] {f1 f2 g1 g2 : ℕ → R} {N : ℕ}
    (hf : ∀ i ≤ N, f1 i = f2 i) (hg : ∀ i ≤ N, g1 i = g2 i) :
    ∀ n ≤ N, comp f1 g1 n = comp f2 g2 n := by
  intro n hn
  simp only [comp]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hf k (le_trans hkn hn), powSeq_congr hg k n hn]

private lemma iterComp_congr {R : Type*} [CommRing R] {f1 f2 : ℕ → R} {N : ℕ}
    (hf : ∀ i ≤ N, f1 i = f2 i) : ∀ r n : ℕ, n ≤ N → iterComp f1 r n = iterComp f2 r n := by
  intro r
  induction r with
  | zero => intro n _; rfl
  | succ r ih =>
    intro n hn
    exact comp_congr hf (fun i hi => ih i hi) n hn

private lemma powSeq_zero_of_lt {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k n : ℕ, n < k → powSeq g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst hi0; simp [hg0]
    · rw [ih (n - i) (by omega), mul_zero]

private lemma iterComp_zero {R : Type*} [CommRing R] {f : ℕ → R} (hf0 : f 0 = 0) :
    ∀ r : ℕ, iterComp f r 0 = 0 := by
  intro r
  induction r with
  | zero => simp [iterComp]
  | succ r _ => simp [iterComp, comp, powSeq, hf0]

private lemma mulSeq_comm {R : Type*} [CommRing R] (u v : ℕ → R) :
    mulSeq u v = mulSeq v u := by
  ext n
  simp only [mulSeq]
  refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro i1 h1 i2 h2 heq; simp only [Finset.mem_range] at h1 h2; omega
  · intro j hj; simp only [Finset.mem_range] at hj ⊢; exact ⟨n - j, by omega, by omega⟩
  · intro i hi; simp only [Finset.mem_range] at hi; rw [Nat.sub_sub_self (by omega), mul_comm]

private lemma mulSeq_assoc {R : Type*} [CommRing R] (u v w : ℕ → R) :
    mulSeq (mulSeq u v) w = mulSeq u (mulSeq v w) := by
  ext n
  simp only [mulSeq, Finset.sum_mul, Finset.mul_sum]
  have h1 : ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), u j * v (i - j) * w (n - i) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if j ≤ i then u j * v (i - j) * w (n - i) else 0 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i _ => i - j) ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
  · intro i1 h1 i2 h2 heq; simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨k + j, by omega, by omega⟩
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi
    rw [show n - j - (i - j) = n - i by omega, mul_assoc]

private lemma mulSeq_add_left {R : Type*} [CommRing R] (u v w : ℕ → R) :
    mulSeq (fun n => u n + v n) w = fun n => mulSeq u w n + mulSeq v w n := by
  ext n; simp only [mulSeq, add_mul, Finset.sum_add_distrib]

private lemma mulSeq_add_right {R : Type*} [CommRing R] (u v w : ℕ → R) :
    mulSeq u (fun n => v n + w n) = fun n => mulSeq u v n + mulSeq u w n := by
  ext n; simp only [mulSeq, mul_add, Finset.sum_add_distrib]

private lemma mulSeq_one_left {R : Type*} [CommRing R] (u : ℕ → R) :
    mulSeq oneSeq u = u := by
  ext n
  simp only [mulSeq, oneSeq]
  rw [Finset.sum_range_succ']
  simp

private lemma mulSeq_cancel_left {R : Type*} [CommRing R] {q u v : ℕ → R}
    (hq0 : q 0 = 1) (h : mulSeq q u = mulSeq q v) : u = v := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congr_fun h n
    simp only [mulSeq] at hn
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hn
    simp only [hq0, one_mul, Nat.sub_zero] at hn
    have hrest : ∑ k ∈ Finset.range n, q (k + 1) * u (n - (k + 1)) =
        ∑ k ∈ Finset.range n, q (k + 1) * v (n - (k + 1)) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkn : k < n := Finset.mem_range.mp hk
      rw [ih (n - (k + 1)) (by omega)]
    rw [hrest] at hn
    exact add_left_cancel hn

private lemma powSeq_succ_eq_mulSeq {R : Type*} [CommRing R] (g : ℕ → R) (k : ℕ) :
    powSeq g (k + 1) = mulSeq g (powSeq g k) := rfl

private lemma powSeq_add {R : Type*} [CommRing R] (g : ℕ → R) :
    ∀ a b : ℕ, powSeq g (a + b) = mulSeq (powSeq g a) (powSeq g b) := by
  intro a
  induction a with
  | zero =>
    intro b; rw [zero_add]
    have : powSeq g 0 = oneSeq := rfl
    rw [this, mulSeq_one_left]
  | succ a ih =>
    intro b
    rw [Nat.succ_add, powSeq_succ_eq_mulSeq, ih, powSeq_succ_eq_mulSeq, mulSeq_assoc]

private lemma mulSeq_qMod (u : ℕ → ZMod 4) (n : ℕ) :
    mulSeq qMod u n = u n + if 2 ≤ n then u (n - 2) else 0 := by
  simp only [mulSeq, qMod]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (if i = 0 ∨ i = 2 then (1 : ZMod 4) else 0) * u (n - i) =
      (if i = 0 then u n else 0) + (if i = 2 then u (n - 2) else 0) := by
    intro i _
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases h2 : i = 2
      · subst h2; simp
      · simp [h0, h2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ 0, Finset.sum_ite_eq' _ 2,
    if_pos (Finset.mem_range.mpr (Nat.succ_pos n))]
  by_cases hn : 2 ≤ n
  · rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos hn]
  · rw [if_neg (by simp only [Finset.mem_range]; omega), if_neg hn]

private lemma mulSeq_qMod_fMod : mulSeq qMod fMod = pMod := by
  ext n
  rw [mulSeq_qMod]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hge : 2 ≤ n + 6 := by omega
    rw [if_pos hge]
    have hsub : n + 6 - 2 = n + 4 := by omega
    rw [hsub]
    dsimp [fMod, pMod]
    have hm : (n + 6) % 4 = 0 ∨ (n + 6) % 4 = 1 ∨ (n + 6) % 4 = 2 ∨ (n + 6) % 4 = 3 := by omega
    rcases hm with h | h | h | h
    · have h2 : (n + 4) % 4 = 2 := by omega
      simp [h, h2]; decide
    · have h2 : (n + 4) % 4 = 3 := by omega
      simp [h, h2]; decide
    · have h2 : (n + 4) % 4 = 0 := by omega
      simp [h, h2]; decide
    · have h2 : (n + 4) % 4 = 1 := by omega
      simp [h, h2]; decide

/-- Key identity: `comp (qMod * u) g = (1 + g^2) * comp u g` whenever `g 0 = 0`. -/
private lemma comp_mulSeq_qMod {u g : ℕ → ZMod 4} (hg0 : g 0 = 0) :
    comp (mulSeq qMod u) g = mulSeq (fun n => oneSeq n + powSeq g 2 n) (comp u g) := by
  ext n
  rw [mulSeq_add_left, mulSeq_one_left]
  simp only [comp]
  have h1 : ∑ k ∈ Finset.range (n + 1), mulSeq qMod u k * powSeq g k n =
      (∑ k ∈ Finset.range (n + 1), u k * powSeq g k n) +
      (∑ k ∈ Finset.range (n + 1), (if 2 ≤ k then u (k - 2) * powSeq g k n else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mulSeq_qMod]; split_ifs <;> ring
  rw [h1]
  congr 1
  -- Show second sum equals `mulSeq (powSeq g 2) (comp u g) n`.
  have h2 : ∑ k ∈ Finset.range (n + 1), (if 2 ≤ k then u (k - 2) * powSeq g k n else 0) =
      ∑ j ∈ Finset.range (n + 1), if j + 2 ≤ n then u j * powSeq g (j + 2) n else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_bij (fun k _ => k - 2) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
    · intro k1 h1 k2 h2 heq; simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨j + 2, by omega, by omega⟩
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk
      rw [Nat.sub_add_cancel hk.2]
  rw [h2]
  have h3 : ∑ j ∈ Finset.range (n + 1), (if j + 2 ≤ n then u j * powSeq g (j + 2) n else 0) =
      ∑ j ∈ Finset.range (n + 1), u j * powSeq g (j + 2) n := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j + 2 ≤ n
    · rw [if_pos hj]
    · rw [if_neg hj, powSeq_zero_of_lt hg0 (j + 2) n (by omega), mul_zero]
  rw [h3]
  have h4 : ∑ j ∈ Finset.range (n + 1), u j * powSeq g (j + 2) n =
      ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
        powSeq g 2 i * (u j * powSeq g j (n - i)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hpow : powSeq g (j + 2) n = mulSeq (powSeq g 2) (powSeq g j) n := by
      rw [add_comm, powSeq_add]
    rw [hpow, mulSeq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [h4, Finset.sum_comm]
  simp only [mulSeq, comp]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← Finset.mul_sum]
  congr 1
  have htrim : ∑ j ∈ Finset.range (n + 1), u j * powSeq g j (n - i) =
      ∑ j ∈ Finset.range (n - i + 1), u j * powSeq g j (n - i) := by
    have hsub : Finset.range (n - i + 1) ⊆ Finset.range (n + 1) :=
      Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    intro j hj1 hj2
    simp only [Finset.mem_range] at hj1 hj2
    rw [powSeq_zero_of_lt hg0 j (n - i) (by omega), mul_zero]
  exact htrim

private lemma comp_pMod (g : ℕ → ZMod 4) (hg0 : g 0 = 0) :
    comp pMod g = fun n => g n + powSeq g 2 n + 2 * powSeq g 3 n := by
  ext n
  have h1 : powSeq g 1 n = g n := by
    simp only [powSeq]
    have ht : ∀ i ∈ Finset.range (n + 1), g i * (if n - i = 0 then (1 : ZMod 4) else 0) =
        if i = n then g n else 0 := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases h : i = n
      · subst h; simp
      · simp [h, show n - i ≠ 0 by omega]
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ n,
      if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
  simp only [comp, pMod]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (if k = 1 then (1 : ZMod 4) else if k = 2 then 1 else if k = 3 then 2 else 0) * powSeq g k n =
      (if k = 1 then g n else 0) + (if k = 2 then powSeq g 2 n else 0) +
      (if k = 3 then 2 * powSeq g 3 n else 0) := by
    intro k _
    by_cases h1k : k = 1
    · subst h1k; simp [h1]
    · by_cases h2k : k = 2
      · subst h2k; simp
      · by_cases h3k : k = 3
        · subst h3k; simp
        · simp [h1k, h2k, h3k]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ 1, Finset.sum_ite_eq' _ 2, Finset.sum_ite_eq' _ 3]
  rcases n with _ | _ | _ | n
  · simp [hg0, powSeq_zero_of_lt hg0]
  · simp [powSeq_zero_of_lt hg0]
  · simp [powSeq_zero_of_lt hg0]
  · simp only [Finset.mem_range, show 1 < n + 3 + 1 by omega, show 2 < n + 3 + 1 by omega,
      show 3 < n + 3 + 1 by omega, ↓reduceIte]

/-- Bound on support of `mulSeq`: if `u` vanishes past `a` and `v` past `b`, `mulSeq u v` vanishes past `a + b`. -/
private lemma mulSeq_eq_zero_of_gt {R : Type*} [CommRing R] {u v : ℕ → R} {a b : ℕ}
    (hu : ∀ i, a < i → u i = 0) (hv : ∀ j, b < j → v j = 0) :
    ∀ n, a + b < n → mulSeq u v n = 0 := by
  intro n hn
  simp only [mulSeq]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hia : a < i
  · rw [hu i hia, zero_mul]
  · rw [hv (n - i) (by omega), mul_zero]

private lemma comp_fMod_fMod : comp fMod fMod = gMod := by
  have h1 : mulSeq (fun n => oneSeq n + powSeq fMod 2 n) (comp fMod fMod) =
      fun n => fMod n + powSeq fMod 2 n + 2 * powSeq fMod 3 n := by
    rw [← comp_mulSeq_qMod (by decide : fMod 0 = 0), mulSeq_qMod_fMod, comp_pMod fMod (by decide)]
  -- Show `(1 + f^2) * gMod = f + f^2 + 2 f^3` by multiplying both sides by `qMod^3`!
  have h2 : mulSeq (fun n => oneSeq n + powSeq fMod 2 n) gMod =
      fun n => fMod n + powSeq fMod 2 n + 2 * powSeq fMod 3 n := by
    have hq0 : qMod 0 = 1 := by decide
    refine mulSeq_cancel_left hq0 (mulSeq_cancel_left hq0 (mulSeq_cancel_left hq0 ?_))
    -- Simplify `q^3 * LHS` and `q^3 * RHS` using `q * f = p`!
    have hqf : mulSeq qMod fMod = pMod := mulSeq_qMod_fMod
    have hf2 : powSeq fMod 2 = mulSeq fMod fMod := by
      rw [powSeq_succ_eq_mulSeq]
      congr 1; ext n; simp only [powSeq]
      have ht : ∀ i ∈ Finset.range (n + 1), fMod i * (if n - i = 0 then (1 : ZMod 4) else 0) =
          if i = n then fMod n else 0 := by
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases h : i = n
        · subst h; simp
        · simp [h, show n - i ≠ 0 by omega]
      rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ n,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
    have hf3 : powSeq fMod 3 = mulSeq fMod (mulSeq fMod fMod) := by
      rw [powSeq_succ_eq_mulSeq, hf2]
    have hq2f2 : mulSeq (mulSeq qMod qMod) (powSeq fMod 2) = mulSeq pMod pMod := by
      rw [hf2]
      calc mulSeq (mulSeq qMod qMod) (mulSeq fMod fMod)
          = mulSeq qMod (mulSeq qMod (mulSeq fMod fMod)) := mulSeq_assoc _ _ _
        _ = mulSeq qMod (mulSeq (mulSeq qMod fMod) fMod) := by rw [mulSeq_assoc]
        _ = mulSeq qMod (mulSeq pMod fMod) := by rw [hqf]
        _ = mulSeq qMod (mulSeq fMod pMod) := by rw [mulSeq_comm pMod fMod]
        _ = mulSeq (mulSeq qMod fMod) pMod := by rw [mulSeq_assoc]
        _ = mulSeq pMod pMod := by rw [hqf]
    have hq3f3 : mulSeq qMod (mulSeq qMod (mulSeq qMod (powSeq fMod 3))) =
        mulSeq pMod (mulSeq pMod pMod) := by
      rw [hf3]
      calc mulSeq qMod (mulSeq qMod (mulSeq qMod (mulSeq fMod (mulSeq fMod fMod))))
          = mulSeq qMod (mulSeq qMod (mulSeq (mulSeq qMod fMod) (mulSeq fMod fMod))) := by
            rw [mulSeq_assoc]
        _ = mulSeq qMod (mulSeq qMod (mulSeq pMod (mulSeq fMod fMod))) := by rw [hqf]
        _ = mulSeq qMod (mulSeq qMod (mulSeq (mulSeq fMod fMod) pMod)) := by
            rw [mulSeq_comm pMod (mulSeq fMod fMod)]
        _ = mulSeq qMod (mulSeq (mulSeq qMod (mulSeq fMod fMod)) pMod) := by
            rw [← mulSeq_assoc qMod (mulSeq fMod fMod) pMod]
        _ = mulSeq (mulSeq qMod (mulSeq qMod (mulSeq fMod fMod))) pMod := by
            rw [← mulSeq_assoc qMod (mulSeq qMod (mulSeq fMod fMod)) pMod]
        _ = mulSeq (mulSeq (mulSeq qMod qMod) (powSeq fMod 2)) pMod := by
            congr 1; rw [← mulSeq_assoc, ← hf2]
        _ = mulSeq (mulSeq pMod pMod) pMod := by rw [hq2f2]
        _ = mulSeq pMod (mulSeq pMod pMod) := mulSeq_assoc _ _ _
    have h2scale : ∀ u : ℕ → ZMod 4, mulSeq qMod (fun n => 2 * u n) = fun n => 2 * mulSeq qMod u n := by
      intro u; ext n; simp only [mulSeq, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
    -- Rewrite LHS = `mulSeq (q^2 + p^2) (q * g)` and RHS = `q^2 * p + q * p^2 + 2 * p^3`!
    have hlhs : mulSeq qMod (mulSeq qMod (mulSeq qMod (mulSeq (fun n => oneSeq n + powSeq fMod 2 n) gMod))) =
        mulSeq (fun n => mulSeq qMod qMod n + mulSeq pMod pMod n) (mulSeq qMod gMod) := by
      calc mulSeq qMod (mulSeq qMod (mulSeq qMod (mulSeq (fun n => oneSeq n + powSeq fMod 2 n) gMod)))
          = mulSeq (mulSeq qMod qMod) (mulSeq qMod (mulSeq (fun n => oneSeq n + powSeq fMod 2 n) gMod)) := by
            rw [mulSeq_assoc]
        _ = mulSeq (mulSeq qMod qMod) (mulSeq (fun n => oneSeq n + powSeq fMod 2 n) (mulSeq qMod gMod)) := by
            rw [← mulSeq_assoc qMod (fun n => oneSeq n + powSeq fMod 2 n) gMod,
                mulSeq_comm qMod (fun n => oneSeq n + powSeq fMod 2 n),
                mulSeq_assoc (fun n => oneSeq n + powSeq fMod 2 n) qMod gMod]
        _ = mulSeq (mulSeq (mulSeq qMod qMod) (fun n => oneSeq n + powSeq fMod 2 n)) (mulSeq qMod gMod) := by
            rw [← mulSeq_assoc]
        _ = mulSeq (fun n => mulSeq qMod qMod n + mulSeq pMod pMod n) (mulSeq qMod gMod) := by
            rw [mulSeq_add_right, mulSeq_comm _ oneSeq, mulSeq_one_left, hq2f2]
    have hrhs : mulSeq qMod (mulSeq qMod (mulSeq qMod (fun n => fMod n + powSeq fMod 2 n + 2 * powSeq fMod 3 n))) =
        fun n => mulSeq qMod (mulSeq qMod pMod) n + mulSeq qMod (mulSeq pMod pMod) n +
          2 * mulSeq pMod (mulSeq pMod pMod) n := by
      simp only [mulSeq_add_right, h2scale, hqf, hq3f3]
      have ha : mulSeq qMod (mulSeq qMod (mulSeq qMod (powSeq fMod 2))) = mulSeq qMod (mulSeq pMod pMod) := by
        rw [← hq2f2, mulSeq_assoc qMod qMod (powSeq fMod 2)]
      rw [ha]
    rw [hlhs, hrhs]
    ext n
    -- Both sides vanish for `n > 9`!
    have hq_gt : ∀ i, 2 < i → qMod i = 0 := fun i hi => by dsimp [qMod]; split_ifs <;> first | rfl | omega
    have hp_gt : ∀ i, 3 < i → pMod i = 0 := fun i hi => by dsimp [pMod]; split_ifs <;> first | rfl | omega
    have hg_gt : ∀ i, 2 < i → gMod i = 0 := fun i hi => by dsimp [gMod]; split_ifs <;> first | rfl | omega
    by_cases hn : 10 < n
    · have hl0 : mulSeq (fun n => mulSeq qMod qMod n + mulSeq pMod pMod n) (mulSeq qMod gMod) n = 0 := by
        refine mulSeq_eq_zero_of_gt (a := 6) (b := 4) ?_ ?_ n (by omega)
        · intro i hi
          have h1 := mulSeq_eq_zero_of_gt hq_gt hq_gt i (by omega)
          have h2 := mulSeq_eq_zero_of_gt hp_gt hp_gt i (by omega)
          simp [h1, h2]
        · exact mulSeq_eq_zero_of_gt hq_gt hg_gt
      have hr1 := mulSeq_eq_zero_of_gt hq_gt (mulSeq_eq_zero_of_gt hq_gt hp_gt) n (by omega)
      have hr2 := mulSeq_eq_zero_of_gt hq_gt (mulSeq_eq_zero_of_gt hp_gt hp_gt) n (by omega)
      have hr3 := mulSeq_eq_zero_of_gt hp_gt (mulSeq_eq_zero_of_gt hp_gt hp_gt) n (by omega)
      simp [hl0, hr1, hr2, hr3]
    · interval_cases n <;> decide
  have h10 : (fun n => oneSeq n + powSeq fMod 2 n) 0 = 1 := by
    simp [oneSeq, powSeq, fMod]
  exact mulSeq_cancel_left h10 (h1.trans h2.symm)

private lemma mulSeq_qMod_iter3 : mulSeq qMod (comp fMod gMod) = rMod := by
  have hg0 : gMod 0 = 0 := by decide
  have hg2 : powSeq gMod 2 = fun n => if n = 2 then 1 else 0 := by
    ext n
    have hg_gt : ∀ i, 2 < i → gMod i = 0 := fun i hi => by dsimp [gMod]; split_ifs <;> first | rfl | omega
    have hpow2 : powSeq gMod 2 = mulSeq gMod gMod := by
      rw [powSeq_succ_eq_mulSeq]
      congr 1; ext m; simp only [powSeq]
      have ht : ∀ i ∈ Finset.range (m + 1), gMod i * (if m - i = 0 then (1 : ZMod 4) else 0) =
          if i = m then gMod m else 0 := by
        intro i hi
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases h : i = m
        · subst h; simp
        · simp [h, show m - i ≠ 0 by omega]
      rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ m,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_self m))]
    rw [hpow2]
    by_cases hn : 4 < n
    · rw [mulSeq_eq_zero_of_gt hg_gt hg_gt n hn, if_neg (by omega)]
    · interval_cases n <;> decide
  have hg3 : powSeq gMod 3 = fun n => if n = 3 then 1 else if n = 4 then 2 else 0 := by
    ext n
    rw [powSeq_succ_eq_mulSeq, hg2]
    have hg_gt : ∀ i, 2 < i → gMod i = 0 := fun i hi => by dsimp [gMod]; split_ifs <;> first | rfl | omega
    have h2_gt : ∀ i, 2 < i → (if i = 2 then (1 : ZMod 4) else 0) = 0 := fun i hi => if_neg (by omega)
    by_cases hn : 4 < n
    · rw [mulSeq_eq_zero_of_gt hg_gt h2_gt n hn, if_neg (by omega), if_neg (by omega)]
    · interval_cases n <;> decide
  have h1q : (fun n => oneSeq n + powSeq gMod 2 n) = qMod := by
    ext n; rw [hg2]; dsimp [oneSeq, qMod]
    by_cases h0 : n = 0
    · subst h0; decide
    · by_cases h2 : n = 2
      · subst h2; decide
      · simp [h0, h2]
  have hcomp := comp_mulSeq_qMod (u := fMod) hg0
  rw [mulSeq_qMod_fMod, comp_pMod gMod hg0, h1q] at hcomp
  rw [← hcomp]
  ext n
  rw [hg2, hg3]
  dsimp [gMod, rMod]
  by_cases h1 : n = 1
  · subst h1; decide
  · by_cases h2 : n = 2
    · subst h2; decide
    · by_cases h3 : n = 3
      · subst h3; decide
      · by_cases h4 : n = 4
        · subst h4; decide
        · simp [h1, h2, h3, h4]

private lemma powSeq_x (m n : ℕ) :
    powSeq (fun j => if j = 1 then (1 : ZMod 4) else 0) m n = if n = m then 1 else 0 := by
  induction m generalizing n with
  | zero => simp [powSeq]
  | succ m ihm =>
    simp only [powSeq]
    have hsub : ∑ i ∈ Finset.range (n + 1),
        (if i = 1 then (1 : ZMod 4) else 0) * powSeq (fun j => if j = 1 then 1 else 0) m (n - i) =
        ∑ i ∈ Finset.range (n + 1), if i = 1 ∧ n = m + 1 then 1 else 0 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [ihm (n - i)]
      by_cases h1 : i = 1
      · subst h1
        by_cases h2 : n = m + 1
        · subst h2; simp
        · have hne : n - 1 ≠ m := by omega
          simp [h2, hne]
      · simp [h1]
    rw [hsub]
    by_cases hnm : n = m + 1
    · subst hnm
      simp only [and_true, Finset.sum_ite_eq', Finset.mem_range, show 1 < m + 1 + 1 by omega, ↓reduceIte]
    · simp [hnm]

private lemma fMod_fixed_point :
    ∀ n : ℕ, fMod n = (if n = 1 then 1 else 0) + mulSeq (iterComp fMod 2) (iterComp fMod 3) n := by
  have hi2 : iterComp fMod 2 = gMod := by
    have h1 : iterComp fMod 1 = fMod := by
      ext n; simp only [iterComp, comp]
      have ht : ∀ k ∈ Finset.range (n + 1),
          fMod k * powSeq (fun m => if m = 1 then (1 : ZMod 4) else 0) k n =
          if k = n then fMod n else 0 := by
        intro k _
        rw [powSeq_x k n]
        by_cases h : k = n
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ n,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
    change comp fMod (iterComp fMod 1) = gMod
    rw [h1, comp_fMod_fMod]
  have hi3 : iterComp fMod 3 = comp fMod gMod := by
    change comp fMod (iterComp fMod 2) = comp fMod gMod
    rw [hi2]
  -- Prove `fMod = x + gMod * comp fMod gMod` by multiplying by `qMod`!
  have hfeq : fMod = fun n => (if n = 1 then 1 else 0) + mulSeq gMod (comp fMod gMod) n := by
    refine mulSeq_cancel_left (by decide : qMod 0 = 1) ?_
    rw [mulSeq_qMod_fMod, mulSeq_add_right]
    have hqg : mulSeq qMod (mulSeq gMod (comp fMod gMod)) = mulSeq gMod rMod := by
      rw [← mulSeq_assoc, mulSeq_comm qMod gMod, mulSeq_assoc, mulSeq_qMod_iter3]
    rw [hqg]
    ext n
    have hq_gt : ∀ i, 2 < i → qMod i = 0 := fun i hi => by dsimp [qMod]; split_ifs <;> first | rfl | omega
    have hx_gt : ∀ i, 1 < i → (if i = 1 then (1 : ZMod 4) else 0) = 0 := fun i hi => if_neg (by omega)
    have hg_gt : ∀ i, 2 < i → gMod i = 0 := fun i hi => by dsimp [gMod]; split_ifs <;> first | rfl | omega
    have hr_gt : ∀ i, 3 < i → rMod i = 0 := fun i hi => by dsimp [rMod]; split_ifs <;> first | rfl | omega
    by_cases hn : 5 < n
    · have hp0 : pMod n = 0 := by dsimp [pMod]; split_ifs <;> first | rfl | omega
      have h1 := mulSeq_eq_zero_of_gt hq_gt hx_gt n (by omega)
      have h2 := mulSeq_eq_zero_of_gt hg_gt hr_gt n (by omega)
      simp [hp0, h1, h2]
    · interval_cases n <;> decide
  intro n
  rw [hi2, hi3]
  exact congr_fun hfeq n

private lemma prove_a396099 (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (harec : ∀ n : ℕ, a n = (if n = 1 then 1 else 0) + mulSeq (iterComp a 2) (iterComp a 3) n)
    (n : ℕ) (hn : 3 ≤ n) : a n ≡ (if n % 4 = 2 ∨ n % 4 = 3 then 1 else 3) [ZMOD 4] := by
  let φ : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  have hmod : ∀ m : ℕ, φ (a m) = fMod m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [ha0, fMod]
      · rw [harec m, map_add, mulSeq_map]
        have ha'0 : φ (a 0) = 0 := by simp [ha0]
        have hterm : mulSeq (fun i => φ (iterComp a 2 i)) (fun i => φ (iterComp a 3 i)) m =
            mulSeq (iterComp fMod 2) (iterComp fMod 3) m := by
          simp only [mulSeq]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [iterComp_map, iterComp_map]
          by_cases hi0 : i = 0
          · subst hi0; rw [iterComp_zero ha'0, iterComp_zero (by decide : fMod 0 = 0), zero_mul, zero_mul]
          · by_cases him' : i = m
            · subst him'; rw [Nat.sub_self, iterComp_zero ha'0, iterComp_zero (by decide : fMod 0 = 0), mul_zero, mul_zero]
            · rw [iterComp_congr (N := m - 1) (fun j hj => ih j (by omega)) 2 i (by omega),
                  iterComp_congr (N := m - 1) (fun j hj => ih j (by omega)) 3 (m - i) (by omega)]
        rw [hterm]
        have h1 : φ (if m = 1 then 1 else 0) = (if m = 1 then (1 : ZMod 4) else 0) := by
          split_ifs <;> simp
        rw [h1, ← fMod_fixed_point m]
  have hval : (a n : ZMod 4) = ((if n % 4 = 2 ∨ n % 4 = 3 then (1 : ℤ) else 3 : ℤ) : ZMod 4) := by
    have := hmod n
    rcases n with _ | _ | _ | n
    · omega
    · omega
    · omega
    · simp only [fMod] at this
      have hcast : (a (n + 3) : ZMod 4) =
          if (n + 3) % 4 = 2 ∨ (n + 3) % 4 = 3 then 1 else 3 := by
        simpa [φ] using this
      rw [hcast]
      split_ifs <;> simp
  exact (ZMod.intCast_eq_intCast_iff (a n) (if n % 4 = 2 ∨ n % 4 = 3 then 1 else 3) 4).mp hval

end OMA.P_oeis_a396099

theorem OMA.solution : type_of% @OMA.S_oeis_a396099.main :=
  OMA.P_oeis_a396099.prove_a396099
