import OMAStatements.S_oeis_a284814
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Original mathematical construction and complete Lean proof: @pmaster.
-- Same-day immutable source: https://github.com/pmaster/open-math-agents/blob/b1a719c6ada8b2d50fe94b1b12b10756ba1651c7/proofs/oeis-a284814.lean
-- Assembly, independent argument review, and pinned-version verification: @CubeJerry.
-- uses note #108723

/-!
Proof of Max Alekseyev's decimal remainder conjecture for A284814.
Proof by @pmaster with Codex.
For large n, the remainders modulo 40 and 50 force two neighboring decimal
digits to be even. Smaller lengths are excluded by checked modular interval
certificates. The entire calculation is evaluated by the Lean kernel.
-/

namespace OMA.S_oeis_a284814

lemma matches_odd {n k : ℕ} (hn : 1 ≤ n) (h : MatchesDigits n k) : k % 2 = 1 := by
  obtain ⟨hlo, hhi, digits⟩ := h
  have hstep : n = n-1+1 := by omega
  have hpow : 10^n = 10^(n-1)*10 := by
    calc
      10^n = 10^(n-1+1) := congrArg (fun t : ℕ => 10^t) hstep
      _ = _ := pow_succ _ _
  have hp : 0 < (10:ℕ)^(n-1) := Nat.pow_pos (by decide)
  have hh := digits (n-1) (by omega)
  rw [show n+1-(n-1) = 2 by omega] at hh
  have hupper : k / 10^(n-1) < 10 :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [hpow, Nat.mul_comm] using hhi)
  have hlower : 0 < k / 10^(n-1) := Nat.div_pos hlo hp
  rw [Nat.mod_eq_of_lt hupper] at hh
  omega

lemma matches_residue {n k m : ℕ} (h : MatchesDigits n k)
    (hm : 2 ≤ m) (hmn : m ≤ n+1) : k % m < 10 := by
  have hd := h.2.2 (n+1-m) (by omega)
  rw [show n+1-(n+1-m) = m by omega] at hd
  omega

def DigitOK (n L s i d : ℕ) : Bool :=
  let w := 10^(n+1-i)
  let g := Nat.gcd L (10*w)
  decide (w ∣ L → (d*w + s%w)%g = s%g)

lemma digitOK_of_matches {n k L i : ℕ} (h : MatchesDigits n k)
    (hi : 2 ≤ i) (hi' : i ≤ n+1) : DigitOK n L (k%L) i (k%i) = true := by
  apply decide_eq_true
  let w := 10^(n+1-i)
  let g := Nat.gcd L (10*w)
  change w ∣ L → (k % i * w + k % L % w) % g = k % L % g
  intro hdvd
  have hd := h.2.2 (n+1-i) (by omega)
  rw [show n+1-(n+1-i) = i by omega] at hd
  change k / w % 10 = k % i at hd
  rw [Nat.mod_mod_of_dvd k hdvd, Nat.mod_mod_of_dvd k (Nat.gcd_dvd_left L (10*w)), ← hd]
  have hb : k / w % 10 * w + k % w = k % (10*w) := by
    calc
      _ = k % w + w * (k / w % 10) := by rw [Nat.add_comm, Nat.mul_comm]
      _ = k % (w*10) := Nat.mod_mul.symm
      _ = k % (10*w) := by rw [Nat.mul_comm w 10]
  rw [hb, Nat.mod_mod_of_dvd k (Nat.gcd_dvd_right L (10*w))]

lemma even_length_impossible {n k : ℕ} (hn : 19 ≤ n) (he : n % 2 = 0)
    (h : MatchesDigits n k) : False := by
  have odd := matches_odd (by omega) h
  have h20 := matches_residue (m := 20) h (by decide) (by omega)
  have d1 := h.2.2 1 (by omega)
  simp only [Nat.add_one_sub_one, pow_one] at d1
  have hmod := Nat.mod_mod_of_dvd k (Nat.dvd_of_mod_eq_zero he)
  omega

lemma tail_case {n k : ℕ} (hn : 49 ≤ n) (h : MatchesDigits n k) : False := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · exact even_length_impossible (by omega) he h
  have odd := matches_odd (by omega) h
  have h40 := matches_residue (m := 40) h (by decide) (by omega)
  have h50 := matches_residue (m := 50) h (by decide) (by omega)
  have d2 := h.2.2 2 (by omega)
  have hmod := Nat.mod_mod_of_dvd k
    (show 2 ∣ (n+1-2) from Nat.dvd_of_mod_eq_zero (by omega))
  norm_num at d2
  omega

end OMA.S_oeis_a284814

namespace OMA.S_oeis_a284814

structure Column where
  prime : ℕ
  coeff : ℕ
  co : ℕ
  indices : List ℕ
deriving Repr

structure TestData where
  n : ℕ
  modulus : ℕ
  smallMod : ℕ
  smallCoef : ℕ
  smooth : List ℕ
  radices : List ℕ
  leftCols : List Column
  rightCols : List Column
deriving Repr

def baseTerm (d : TestData) (s : ℕ) : ℕ :=
  d.smallCoef * s + (d.smooth.map (fun i => (s % i) * 10 ^ (d.n + 1 - i))).sum

def dotTerm (cols : List Column) (t : ℕ → ℕ) : ℕ :=
  (cols.map (fun c => c.coeff * t c.prime)).sum

def smallOK (d : TestData) (s : ℕ) : Bool :=
  s%2 == 1 && d.smooth.all fun i => s%i < 10 && DigitOK d.n d.smallMod s i (s%i)

def digitChoices (d : TestData) (s : ℕ) (c : Column) : List ℕ :=
  (List.range 10).filter (fun x =>
    x%c.co == s%c.co && c.indices.all (fun i => DigitOK d.n d.smallMod s i x))

def possibleSmall (d : TestData) : List ℕ → List ℕ
  | [] => [0]
  | f :: fs =>
    let m := fs.prod
    let mods := d.smooth.filter (fun i => i ∣ f*m)
    ((possibleSmall d fs).flatMap (fun a => (List.range f).map (fun j => a + m*j))).filter
      (fun a => mods.all (fun i => a%i < 10))

private theorem small_mem (d : TestData) (s : ℕ)
    (hs : ∀ i ∈ d.smooth, s%i < 10) (fs : List ℕ) (hpos : 0 < fs.prod) :
    s%fs.prod ∈ possibleSmall d fs := by
  induction fs with
  | nil => simp [possibleSmall, Nat.mod_one]
  | cons f fs ih =>
    rw [List.prod_cons] at hpos ⊢
    have hf : 0 < f := Nat.pos_of_mul_pos_right hpos
    have hm : 0 < fs.prod := Nat.pos_of_mul_pos_left hpos
    have hlt := Nat.mod_lt s hpos
    have hq : (s%(f*fs.prod))/fs.prod < f := (Nat.div_lt_iff_lt_mul hm).mpr hlt
    have hr := Nat.mod_mod_of_dvd s (show fs.prod ∣ f*fs.prod from dvd_mul_left _ _)
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨s%fs.prod, ih hm, List.mem_map.mpr ⟨_, List.mem_range.mpr hq, ?_⟩⟩
      rw [← hr, Nat.mod_add_div]
    · apply List.all_eq_true.mpr
      intro i hi
      obtain ⟨hi, hi'⟩ := List.mem_filter.mp hi
      simp only [decide_eq_true_eq] at hi' ⊢
      rw [Nat.mod_mod_of_dvd s hi']
      exact hs _ hi



def rowWeight (n i : ℕ) := 10 ^ (n+1-i)
def columnWeight (d : TestData) (c : Column) := (c.indices.map (rowWeight d.n)).sum
def columnShift (d : TestData) (c : Column) :=
  (c.coeff + d.modulus - columnWeight d c % d.modulus) % d.modulus

def columnValid (d : TestData) (c : Column) : Prop :=
  10 ≤ c.prime ∧ c.prime ≤ d.n+1 ∧ c.co ∣ d.smallMod ∧
  c.co ∣ (c.indices.map (fun i => i/c.prime)).foldr Nat.lcm 1 ∧
  (∀ i ∈ c.indices, 2 ≤ i ∧ i ≤ d.n+1 ∧ c.prime ∣ i) ∧
  c.coeff % d.modulus = (columnWeight d c + columnShift d c) % d.modulus ∧
  d.modulus ∣ columnShift d c * c.prime

def bridgeValid (d : TestData) : Prop :=
  0 < d.n ∧ 2 ∣ d.smallMod ∧
  (∀ i ∈ d.smooth, 2 ≤ i ∧ i ≤ d.n+1 ∧ i ∣ d.smallMod) ∧
  (∀ c ∈ d.leftCols ++ d.rightCols, columnValid d c) ∧
  (d.smooth ++ (d.leftCols ++ d.rightCols).flatMap Column.indices).Perm (List.range' 2 d.n) ∧
  d.modulus ∣ d.smallCoef * d.smallMod ∧
  (1 + d.smallCoef + ((d.leftCols ++ d.rightCols).map (columnShift d)).sum) % d.modulus = 0

instance (d : TestData) (c : Column) : Decidable (columnValid d c) := by
  unfold columnValid
  infer_instance

instance (d : TestData) : Decidable (bridgeValid d) := by
  unfold bridgeValid
  infer_instance

private lemma decimal_expansion {n k : ℕ} (h : MatchesDigits n k) :
    ((List.range' 2 n).map (fun i => k % i * rowWeight n i)).sum = k := by
  have step (m : ℕ) (hm : m ≤ n) :
      ((List.range' (n+2-m) m).map (fun i => k % i * rowWeight n i)).sum = k % 10^m := by
    induction m with
    | zero => simp; omega
    | succ m ih =>
      have h1 : n+2-(m+1)+1 = n+2-m := by omega
      have h2 : n+2-(m+1) = n+1-m := by omega
      have h3 : n+1-(n+1-m) = m := by omega
      rw [List.range'_succ, List.map_cons, List.sum_cons, h1, ih (by omega), h2,
        rowWeight, h3, ← h.2.2 m (by omega), pow_succ, Nat.mod_mul]
      ac_rfl
  simpa [Nat.mod_eq_of_lt h.2.1] using step n (by omega)

private lemma position_same {d : TestData} {k : ℕ} (h : MatchesDigits d.n k) {c : Column}
    (hc : columnValid d c) {i : ℕ} (hi : i ∈ c.indices) : k % i = k % c.prime := by
  obtain ⟨hp, _, _, _, hinds, _⟩ := hc
  obtain ⟨hlo,hhi,hd⟩ := hinds i hi
  have hlt := matches_residue h hlo hhi
  rw [← Nat.mod_mod_of_dvd k hd, Nat.mod_eq_of_lt (show k % i < c.prime by omega)]

private lemma common_congruence {a b : ℕ} (l : List ℕ)
    (h : ∀ i ∈ l, Nat.ModEq i a b) : Nat.ModEq (l.foldr Nat.lcm 1) a b := by
  induction l with
  | nil => exact Nat.modEq_one
  | cons x xs ih =>
    exact Nat.mod_lcm (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

private lemma bridge_eligibility {d : TestData} {k : ℕ} (h : MatchesDigits d.n k)
    (v : bridgeValid d) :
    smallOK d (k % d.smallMod) = true ∧
    ∀ c ∈ d.leftCols ++ d.rightCols, k % c.prime ∈ digitChoices d (k % d.smallMod) c := by
  obtain ⟨hn, htwo, hs, hc, _⟩ := v
  constructor
  · simp only [smallOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    refine ⟨(Nat.mod_mod_of_dvd k htwo).trans (matches_odd hn h), ?_⟩
    intro i hi
    obtain ⟨hlo,hhi,hd⟩ := hs i hi
    rw [Nat.mod_mod_of_dvd k hd]
    exact ⟨matches_residue h hlo hhi, digitOK_of_matches h hlo hhi⟩
  · intro c hmem
    have hv := hc c hmem
    obtain ⟨hp,hpn,hco,hcd,hinds,_⟩ := hv
    simp only [digitChoices, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true]
    refine ⟨matches_residue h (by omega) hpn, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd k hco]
      apply Nat.ModEq.of_dvd hcd
      apply common_congruence
      intro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      rw [← position_same h (hc c hmem) hi]
      exact Nat.ModEq.of_dvd (Nat.div_dvd_of_dvd (hinds i hi).2.2) (Nat.mod_modEq _ _)
    · intro i hi
      rw [← position_same h (hc c hmem) hi]
      exact digitOK_of_matches h (hinds i hi).1 (hinds i hi).2.1


private lemma sum_scaled (l : List ℕ) (a : ℕ) :
    (l.map (fun x => a*x)).sum = a*l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private lemma scaled_modEq {M b c : ℕ} (k : ℕ) (hd : M ∣ c*b) :
    Nat.ModEq M (c*(k%b)) (c*k) :=
  Nat.ModEq.of_dvd hd ((Nat.mod_modEq k b).mul_left' c)

private lemma cols_congruence {d : TestData} {k : ℕ} (h : MatchesDigits d.n k)
    (cs : List Column) (hv : ∀ c ∈ cs, columnValid d c) :
    Nat.ModEq d.modulus (dotTerm cs (fun p => k%p))
      (((cs.flatMap Column.indices).map (fun i => k % i * rowWeight d.n i)).sum +
       (cs.map (columnShift d)).sum * k) := by
  induction cs with
  | nil => simp [dotTerm, Nat.ModEq]
  | cons c cs ih =>
    have hc := hv c (by simp)
    have ih' := ih (fun z hz => hv z (by simp [hz]))
    have allsame : (c.indices.map (fun i => k % i * rowWeight d.n i)).sum =
        (k % c.prime) * columnWeight d c := by
      unfold columnWeight
      rw [← sum_scaled, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply, position_same h hc hi]
    have a : Nat.ModEq d.modulus (c.coeff * (k%c.prime))
        ((k%c.prime)*columnWeight d c + columnShift d c*k) := by
      have eqc : Nat.ModEq d.modulus c.coeff (columnWeight d c + columnShift d c) :=
        hc.2.2.2.2.2.1
      calc
        _ ≡ (columnWeight d c+columnShift d c)*(k%c.prime) [MOD d.modulus] :=
          eqc.mul_right _
        _ = (k%c.prime)*columnWeight d c + columnShift d c*(k%c.prime) := by ring
        _ ≡ _ [MOD d.modulus] := (scaled_modEq k hc.2.2.2.2.2.2).add_left _
    change Nat.ModEq d.modulus (c.coeff * (k%c.prime) + dotTerm cs (fun p=>k%p)) _
    refine (a.add ih').trans ?_
    apply congrArg (fun x : ℕ => x % d.modulus)
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, Nat.add_mul, allsame]
    ac_rfl

lemma match_bridge {d : TestData} {k : ℕ} (v : bridgeValid d) (h : MatchesDigits d.n k) :
    smallOK d (k % d.smallMod) = true ∧
    (∀ c ∈ d.leftCols ++ d.rightCols, k % c.prime ∈ digitChoices d (k % d.smallMod) c) ∧
    (baseTerm d (k % d.smallMod) + dotTerm d.leftCols (fun p=>k%p) +
      dotTerm d.rightCols (fun p=>k%p)) % d.modulus = 0 := by
  obtain ⟨ha,hb⟩ := bridge_eligibility h v
  refine ⟨ha,hb,?_⟩
  obtain ⟨_,_,hs,hc,hperm,hsm,hzero⟩ := v
  let cs := d.leftCols ++ d.rightCols
  let f := fun i => k % i * rowWeight d.n i
  have hsize : (d.smooth.map f).sum + ((cs.flatMap Column.indices).map f).sum = k := by
    rw [← List.sum_append, ← List.map_append]
    exact ((hperm.map f).sum_eq).trans (decimal_expansion h)
  have smooth_eq :
      (d.smooth.map (fun i => k%d.smallMod%i * 10^(d.n+1-i))).sum =
        (d.smooth.map f).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    exact congrArg (fun u => u * rowWeight d.n i) (Nat.mod_mod_of_dvd k (hs i hi).2.2)
  have b : Nat.ModEq d.modulus (baseTerm d (k%d.smallMod))
      (d.smallCoef*k + (d.smooth.map f).sum) := by
    unfold baseTerm
    rw [smooth_eq]
    exact (scaled_modEq k hsm).add_right _
  have hd : dotTerm cs (fun p=>k%p) = dotTerm d.leftCols (fun p=>k%p) +
      dotTerm d.rightCols (fun p=>k%p) := by
    simp [dotTerm, cs]
  have hz : Nat.ModEq d.modulus (1 + d.smallCoef + (cs.map (columnShift d)).sum) 0 := by
    simpa [Nat.ModEq, cs] using hzero
  have full : Nat.ModEq d.modulus
      (baseTerm d (k%d.smallMod) + dotTerm cs (fun p=>k%p)) 0 := by
    calc
      _ ≡ (d.smallCoef*k + (d.smooth.map f).sum) +
          (((cs.flatMap Column.indices).map f).sum + (cs.map (columnShift d)).sum*k)
            [MOD d.modulus] := b.add (cols_congruence h cs hc)
      _ = ((d.smooth.map f).sum + ((cs.flatMap Column.indices).map f).sum) +
            (d.smallCoef*k + (cs.map (columnShift d)).sum*k) := by ac_rfl
      _ = (1 + d.smallCoef + (cs.map (columnShift d)).sum)*k := by rw [hsize]; ring
      _ ≡ 0 [MOD d.modulus] := by simpa using hz.mul_right k
  rw [Nat.add_assoc, ← hd]
  exact Nat.modEq_zero_iff_dvd.mp full |> Nat.mod_eq_zero_of_dvd

structure GapWitness where
  residue : ℕ
  multiplier : ℕ
  ends : ℕ

def gapAnchor (d : TestData) (r : GapWitness) (c : Column) : ℕ :=
  let ds := digitChoices d r.residue c
  let x := if r.ends / 2^c.prime % 2 = 1 then ds.getLastD 0 else ds.headD 0
  (r.multiplier * c.coeff * x) % d.modulus

def gapOffset (d : TestData) (r : GapWitness) (c : Column) (x : ℕ) : ℕ :=
  (r.multiplier * c.coeff * x + d.modulus - gapAnchor d r c) % d.modulus

def gapWidth (d : TestData) (r : GapWitness) (c : Column) : ℕ :=
  ((digitChoices d r.residue c).map (gapOffset d r c)).foldr max 0

def gapBound (d : TestData) (r : GapWitness) (cs : List Column) : ℕ × ℕ :=
  ((cs.map (gapAnchor d r)).sum, (cs.map (gapWidth d r)).sum)

def gapRowOK (d : TestData) (r : GapWitness) : Bool :=
  let cs := d.leftCols ++ d.rightCols
  cs.any (fun c => (digitChoices d r.residue c).isEmpty) ||
    let b := gapBound d r cs
    let lo := (r.multiplier * baseTerm d r.residue + b.1) % d.modulus
    decide (0 < lo ∧ lo + b.2 < d.modulus)

def gapCertificate (d : TestData) (rows : List GapWitness) : Bool :=
  (((possibleSmall d d.radices).filter (smallOK d)) == rows.map GapWitness.residue) &&
    rows.all (gapRowOK d)

private lemma gap_mem_le {x : ℕ} {xs : List ℕ} (h : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private lemma gap_bound_sound (d : TestData) (r : GapWitness) (t : ℕ → ℕ)
    (hm : 0 < d.modulus) (cs : List Column)
    (ht : ∀ c ∈ cs, t c.prime ∈ digitChoices d r.residue c) :
    ∃ v, v ≤ (gapBound d r cs).2 ∧
      Nat.ModEq d.modulus (r.multiplier * dotTerm cs t) ((gapBound d r cs).1 + v) := by
  induction cs with
  | nil => exact ⟨0, by simp [gapBound], by simp [gapBound, dotTerm, Nat.ModEq]⟩
  | cons c cs ih =>
    obtain ⟨v,hv,hmod⟩ := ih (fun a h => ht a (.tail _ h))
    let z := gapOffset d r c (t c.prime)
    have hz : z ≤ gapWidth d r c :=
      gap_mem_le (List.mem_map.mpr ⟨_, ht _ (.head _), rfl⟩)
    refine ⟨z+v, Nat.add_le_add hz hv, ?_⟩
    have ha : gapAnchor d r c < d.modulus := Nat.mod_lt _ hm
    have hid : Nat.ModEq d.modulus (r.multiplier * c.coeff * t c.prime)
        (gapAnchor d r c + z) := by
      unfold Nat.ModEq
      dsimp only [z, gapOffset]
      rw [Nat.add_mod_mod]
      rw [show gapAnchor d r c + (r.multiplier*c.coeff*t c.prime+d.modulus-gapAnchor d r c)
           = r.multiplier*c.coeff*t c.prime+d.modulus by omega, Nat.add_mod_right]
    change Nat.ModEq d.modulus (r.multiplier*(c.coeff*t c.prime+dotTerm cs t))
      (gapAnchor d r c + (gapBound d r cs).1 + (z+v))
    rw [Nat.mul_add, ← Nat.mul_assoc]
    convert hid.add hmod using 1; omega

theorem gap_certificate_excludes {d : TestData} {rows : List GapWitness}
    (checked : gapCertificate d rows = true)
    (hL : d.radices.prod = d.smallMod) (hM : 0 < d.modulus)
    {s : ℕ} (hslt : s < d.smallMod) (hsmall : smallOK d s = true)
    {t : ℕ → ℕ} (hcol : ∀ c ∈ d.leftCols ++ d.rightCols, t c.prime ∈ digitChoices d s c)
    (he : (baseTerm d s + dotTerm d.leftCols t + dotTerm d.rightCols t)%d.modulus = 0) :
    False := by
  have hz : ∀ i ∈ d.smooth, s%i < 10 := by
    intro i hi
    have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hsmall).2 i hi
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hlist := small_mem d s hz d.radices (by omega)
  rw [hL, Nat.mod_eq_of_lt hslt] at hlist
  obtain ⟨hcover, hcheck⟩ := Bool.and_eq_true_iff.mp checked
  have hr := List.mem_filter.mpr ⟨hlist, hsmall⟩
  rw [eq_of_beq hcover] at hr
  obtain ⟨r, hrr, rfl⟩ := List.mem_map.mp hr
  let cs := d.leftCols ++ d.rightCols
  have hgood := List.all_eq_true.mp hcheck r hrr
  have hne : cs.any (fun c => (digitChoices d r.residue c).isEmpty) = false := by
    apply List.any_eq_false.mpr
    intro c h
    intro heq
    have hc := hcol c h
    rw [List.isEmpty_iff.mp heq] at hc
    exact List.not_mem_nil hc
  change (cs.any _ || _) = true at hgood
  rw [hne, Bool.false_or] at hgood
  obtain ⟨hpos, hlt⟩ := of_decide_eq_true hgood
  change 0 < (r.multiplier * baseTerm d r.residue + (gapBound d r cs).1) % d.modulus at hpos
  change (r.multiplier * baseTerm d r.residue + (gapBound d r cs).1) % d.modulus + (gapBound d r cs).2 < d.modulus at hlt
  obtain ⟨v,hv,hmod⟩ := gap_bound_sound d r t hM cs hcol
  have hd : dotTerm cs t = dotTerm d.leftCols t + dotTerm d.rightCols t := by
    simp [dotTerm, cs]
  have hem : Nat.ModEq d.modulus (baseTerm d r.residue + dotTerm cs t) 0 := by
    simpa [Nat.ModEq, hd, Nat.add_assoc] using he
  have hzero := (hmod.add_left (r.multiplier*baseTerm d r.residue)).symm.trans
    (show Nat.ModEq d.modulus (r.multiplier*baseTerm d r.residue+r.multiplier*dotTerm cs t) 0 by
      simpa [Nat.mul_add] using hem.mul_left r.multiplier)
  change (r.multiplier*baseTerm d r.residue + ((gapBound d r cs).1+v))%d.modulus = 0 at hzero
  rw [← Nat.add_assoc, ← Nat.mod_add_mod] at hzero
  rw [Nat.mod_eq_of_lt (by omega)] at hzero
  omega

def test15 : TestData := ⟨15, 720720, 5040, 473759, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16], [7, 5, 9, 16], [⟨13, 444520, 1, [13]⟩], [⟨11, 624160, 1, [11]⟩]⟩

def test16 : TestData := ⟨16, 12252240, 5040, 9843119, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16], [7, 5, 9, 16], [⟨13, 1894960, 1, [13]⟩, ⟨17, 7207201, 1, [17]⟩], [⟨11, 6569200, 1, [11]⟩]⟩

def test17 : TestData := ⟨17, 12252240, 5040, 9843119, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18], [7, 5, 9, 16], [⟨13, 1984960, 1, [13]⟩, ⟨17, 7207210, 1, [17]⟩], [⟨11, 3316960, 1, [11]⟩]⟩

def test18 : TestData := ⟨18, 232792560, 5040, 144617759, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18], [7, 5, 9, 16], [⟨17, 68468500, 1, [17]⟩, ⟨11, 142325920, 1, [11]⟩], [⟨13, 162164080, 1, [13]⟩, ⟨19, 49008961, 1, [19]⟩]⟩

def test19 : TestData := ⟨19, 232792560, 5040, 144617759, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20], [7, 5, 9, 16], [⟨17, 68469400, 1, [17]⟩, ⟨11, 111155680, 1, [11]⟩], [⟨13, 171164080, 1, [13]⟩, ⟨19, 49008970, 1, [19]⟩]⟩

def test21 : TestData := ⟨21, 232792560, 5040, 144617759, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21], [7, 5, 9, 16], [⟨19, 49009960, 1, [19]⟩, ⟨13, 229993840, 1, [13]⟩], [⟨17, 68568400, 1, [17]⟩, ⟨11, 174317681, 2, [11, 22]⟩]⟩

def test23 : TestData := ⟨23, 5354228880, 5040, 5266054079, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24], [7, 5, 9, 16], [⟨19, 281901520, 1, [19]⟩, ⟨13, 2388288880, 1, [13]⟩], [⟨17, 4734319600, 1, [17]⟩, ⟨23, 698377690, 1, [23]⟩, ⟨11, 4628177300, 2, [11, 22]⟩]⟩

def test25 : TestData := ⟨25, 26771144400, 25200, 26682969599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25], [7, 25, 9, 16], [⟨23, 22115294200, 1, [23]⟩, ⟨17, 5724319600, 1, [17]⟩], [⟨19, 5646030400, 1, [19]⟩, ⟨11, 7708275200, 2, [11, 22]⟩, ⟨13, 18481776401, 2, [13, 26]⟩]⟩

def test27 : TestData := ⟨27, 80313433200, 75600, 53454113999, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28], [7, 25, 27, 16], [⟨23, 48886537600, 1, [23]⟩, ⟨17, 24410886400, 1, [17]⟩], [⟨19, 60178319200, 1, [19]⟩, ⟨13, 48333008900, 2, [13, 26]⟩, ⟨11, 21235476800, 2, [11, 22]⟩]⟩

def test29 : TestData := ⟨29, 2329089562800, 75600, 1659722777999, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30], [7, 25, 27, 16], [⟨23, 1012657636000, 1, [23]⟩, ⟨17, 2053694432800, 1, [17]⟩, ⟨29, 2248776129610, 1, [29]⟩], [⟨19, 1203252950800, 1, [19]⟩, ⟨13, 1614585605600, 2, [13, 26]⟩, ⟨11, 1240099914800, 2, [11, 22]⟩]⟩

def test31 : TestData := ⟨31, 144403552893600, 151200, 64545140973599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32], [7, 25, 27, 32], [⟨29, 34856030009800, 1, [29]⟩, ⟨19, 139203178904800, 1, [19]⟩, ⟨13, 31746187985600, 2, [13, 26]⟩, ⟨31, 111796299014410, 1, [31]⟩], [⟨23, 94177230148000, 1, [23]⟩, ⟨17, 23152436308000, 1, [17]⟩, ⟨11, 40162767219200, 2, [11, 22]⟩]⟩

def test33 : TestData := ⟨33, 144403552893600, 151200, 64545140973599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32], [7, 25, 27, 32], [⟨31, 111796299015400, 1, [31]⟩, ⟨23, 94276230148000, 1, [23]⟩, ⟨13, 31064531722400, 2, [13, 26]⟩], [⟨29, 34856030108800, 1, [29]⟩, ⟨19, 118378308649600, 1, [19]⟩, ⟨17, 106718704192001, 2, [17, 34]⟩, ⟨11, 117380793792810, 6, [11, 22, 33]⟩]⟩

def test35 : TestData := ⟨35, 144403552893600, 151200, 64545140973599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36], [7, 25, 27, 32], [⟨31, 111796299114400, 1, [31]⟩, ⟨23, 104176230148000, 1, [23]⟩, ⟨17, 87939424763300, 2, [17, 34]⟩, ⟨11, 41391594899400, 6, [11, 22, 33]⟩], [⟨29, 34856040008800, 1, [29]⟩, ⟨19, 57541023640000, 1, [19]⟩, ⟨13, 107302458296000, 2, [13, 26]⟩]⟩

def test37 : TestData := ⟨37, 5342931457063200, 151200, 786562905441599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36], [7, 25, 27, 32], [⟨31, 689410520588800, 1, [31]⟩, ⟨23, 2393808206190400, 1, [23]⟩, ⟨11, 4716773701514400, 6, [11, 22, 33]⟩, ⟨37, 2599263952084810, 1, [37]⟩, ⟨19, 3937657672338401, 2, [19, 38]⟩], [⟨29, 3500542299455200, 1, [29]⟩, ⟨17, 3119732280275600, 2, [17, 34]⟩, ⟨13, 2243760105699200, 2, [13, 26]⟩]⟩

def test39 : TestData := ⟨39, 5342931457063200, 151200, 786562905441599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40], [7, 25, 27, 32], [⟨37, 2599263952085800, 1, [37]⟩, ⟨29, 3500641299455200, 1, [29]⟩, ⟨19, 1482115517884100, 2, [19, 38]⟩, ⟨11, 1499401929878400, 6, [11, 22, 33]⟩], [⟨31, 689411510588800, 1, [31]⟩, ⟨23, 5221041979052800, 1, [23]⟩, ⟨17, 3340363860732800, 2, [17, 34]⟩, ⟨13, 2027863010597610, 6, [13, 26, 39]⟩]⟩

def test41 : TestData := ⟨41, 219060189739591200, 151200, 107645192046705599, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42], [7, 25, 27, 32], [⟨37, 136172550378764800, 1, [37]⟩, ⟨29, 30225198584771200, 1, [29]⟩, ⟨19, 199391211008699600, 2, [19, 38]⟩, ⟨13, 114011439927018600, 6, [13, 26, 39]⟩, ⟨41, 160287943711896010, 1, [41]⟩], [⟨31, 134262796937168800, 1, [31]⟩, ⟨23, 218486310323471200, 1, [23]⟩, ⟨17, 52118179191768800, 2, [17, 34]⟩, ⟨11, 48424495303639200, 6, [11, 22, 33]⟩]⟩

def test43 : TestData := ⟨43, 9419588158802421600, 151200, 983885951005070399, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42], [7, 25, 27, 32], [⟨41, 3446190789805765000, 1, [41]⟩, ⟨31, 9115740476260408000, 1, [31]⟩, ⟨23, 3571391723204706400, 1, [23]⟩, ⟨13, 1695092508855357600, 6, [13, 26, 39]⟩, ⟨43, 4381203794791824010, 1, [43]⟩, ⟨11, 4185268961145146401, 12, [11, 22, 33, 44]⟩], [⟨37, 2545834637524168000, 1, [37]⟩, ⟨29, 6822081080512098400, 1, [29]⟩, ⟨19, 119938671272208800, 2, [19, 38]⟩, ⟨17, 212091235708563200, 2, [17, 34]⟩]⟩

def test45 : TestData := ⟨45, 9419588158802421600, 151200, 983885951005070399, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45], [7, 25, 27, 32], [⟨43, 4381203794791825000, 1, [43]⟩, ⟨37, 2545834638514168000, 1, [37]⟩, ⟨29, 6921081080512098400, 1, [29]⟩, ⟨13, 8651668481371329600, 6, [13, 26, 39]⟩, ⟨23, 3699842709753690401, 2, [23, 46]⟩, ⟨11, 4065017127208089700, 12, [11, 22, 33, 44]⟩], [⟨41, 3446190789805864000, 1, [41]⟩, ⟨31, 9116730476260408000, 1, [31]⟩, ⟨19, 3565814564081871200, 2, [19, 38]⟩, ⟨17, 5694507779887625600, 2, [17, 34]⟩]⟩

def test47 : TestData := ⟨47, 442720643463713815200, 151200, 434284941255916463999, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48], [7, 25, 27, 32], [⟨43, 51479144588804032000, 1, [43]⟩, ⟨37, 11965422896316589600, 1, [37]⟩, ⟨29, 101597374509733892800, 1, [29]⟩, ⟨17, 120635106892882472000, 2, [17, 34]⟩, ⟨47, 386203114510899285610, 1, [47]⟩, ⟨11, 39137774527514527600, 12, [11, 22, 33, 44]⟩], [⟨41, 248355482918678725600, 1, [41]⟩, ⟨31, 414258021304764536800, 1, [31]⟩, ⟨23, 365069703240341689700, 2, [23, 46]⟩, ⟨19, 84404935398580306400, 2, [19, 38]⟩, ⟨13, 214490681475242606400, 6, [13, 26, 39]⟩]⟩

def rows15 : List GapWitness := [
  ⟨1041, 1336, 0⟩,
  ⟨2481, 1336, 0⟩,
  ⟨3201, 1336, 0⟩,
  ⟨3921, 1336, 0⟩,
  ⟨4641, 1336, 0⟩,
  ⟨801, 1336, 0⟩,
  ⟨1521, 1336, 0⟩,
  ⟨2241, 1336, 0⟩,
  ⟨2961, 1336, 0⟩,
  ⟨4401, 1336, 0⟩,
  ⟨561, 1336, 0⟩,
  ⟨1281, 1336, 0⟩,
  ⟨2721, 1336, 0⟩,
  ⟨4161, 1336, 0⟩,
  ⟨4881, 1336, 0⟩,
  ⟨885, 2993, 8192⟩,
  ⟨1605, 2993, 8192⟩,
  ⟨2325, 1336, 0⟩,
  ⟨3045, 1336, 0⟩,
  ⟨4485, 1336, 0⟩,
  ⟨645, 1336, 0⟩,
  ⟨1365, 1336, 0⟩,
  ⟨2805, 1336, 0⟩,
  ⟨4245, 1336, 0⟩,
  ⟨4965, 1336, 0⟩,
  ⟨1125, 2993, 8192⟩,
  ⟨2565, 1336, 0⟩,
  ⟨3285, 1336, 0⟩,
  ⟨4005, 1336, 0⟩,
  ⟨4725, 1336, 0⟩,
  ⟨169, 1336, 0⟩,
  ⟨889, 1336, 0⟩,
  ⟨2329, 1336, 0⟩,
  ⟨3769, 1336, 0⟩,
  ⟨4489, 2993, 8192⟩,
  ⟨649, 1336, 0⟩,
  ⟨2089, 1336, 0⟩,
  ⟨2809, 1336, 0⟩,
  ⟨3529, 2993, 8192⟩,
  ⟨4249, 2993, 8192⟩,
  ⟨409, 1336, 0⟩,
  ⟨1129, 1336, 0⟩,
  ⟨1849, 1336, 0⟩,
  ⟨2569, 1336, 0⟩,
  ⟨4009, 2993, 8192⟩
]

def rows16 : List GapWitness := [
  ⟨577, 6595, 10240⟩,
  ⟨1297, 6595, 10240⟩,
  ⟨2017, 6595, 10240⟩,
  ⟨2737, 6595, 10240⟩,
  ⟨4177, 6595, 10240⟩,
  ⟨17, 6595, 10240⟩,
  ⟨737, 6595, 10240⟩,
  ⟨1457, 6595, 10240⟩,
  ⟨2177, 6595, 10240⟩,
  ⟨3617, 6595, 10240⟩,
  ⟨593, 6595, 10240⟩,
  ⟨2033, 6595, 10240⟩,
  ⟨2753, 6595, 10240⟩,
  ⟨3473, 6595, 10240⟩,
  ⟨4193, 6595, 10240⟩,
  ⟨33, 6595, 10240⟩,
  ⟨1473, 6595, 10240⟩,
  ⟨2193, 6595, 10240⟩,
  ⟨2913, 6595, 10240⟩,
  ⟨3633, 6595, 10240⟩,
  ⟨337, 6595, 10240⟩,
  ⟨1057, 6595, 10240⟩,
  ⟨2497, 6595, 10240⟩,
  ⟨3937, 6595, 10240⟩,
  ⟨4657, 6595, 10240⟩,
  ⟨353, 6595, 10240⟩,
  ⟨1073, 6595, 10240⟩,
  ⟨1793, 6595, 10240⟩,
  ⟨2513, 6595, 10240⟩,
  ⟨3953, 6595, 10240⟩,
  ⟨497, 6595, 10240⟩,
  ⟨1937, 13287, 8192⟩,
  ⟨3377, 6595, 10240⟩,
  ⟨4097, 6595, 10240⟩,
  ⟨4817, 6595, 10240⟩,
  ⟨513, 6595, 10240⟩,
  ⟨1233, 6595, 10240⟩,
  ⟨1953, 6595, 10240⟩,
  ⟨3393, 6595, 10240⟩,
  ⟨4833, 6595, 10240⟩,
  ⟨817, 6595, 10240⟩,
  ⟨2257, 6595, 10240⟩,
  ⟨2977, 6595, 10240⟩,
  ⟨3697, 6595, 10240⟩,
  ⟨4417, 6595, 10240⟩,
  ⟨113, 6595, 10240⟩,
  ⟨833, 6595, 10240⟩,
  ⟨2273, 6595, 10240⟩,
  ⟨3713, 6595, 10240⟩,
  ⟨4433, 6595, 10240⟩,
  ⟨257, 13287, 8192⟩,
  ⟨1697, 6595, 10240⟩,
  ⟨2417, 6595, 10240⟩,
  ⟨3137, 6595, 10240⟩,
  ⟨3857, 6595, 10240⟩,
  ⟨273, 6595, 10240⟩,
  ⟨1713, 6595, 10240⟩,
  ⟨3153, 6595, 10240⟩,
  ⟨3873, 6595, 10240⟩,
  ⟨4593, 6595, 10240⟩,
  ⟨1011, 6595, 10240⟩,
  ⟨1731, 6595, 10240⟩,
  ⟨2451, 13287, 8192⟩,
  ⟨3171, 6595, 10240⟩,
  ⟨4611, 6595, 10240⟩,
  ⟨435, 6595, 10240⟩,
  ⟨1155, 6595, 10240⟩,
  ⟨2595, 6595, 10240⟩,
  ⟨4035, 6595, 10240⟩,
  ⟨4755, 6595, 10240⟩,
  ⟨579, 6595, 10240⟩,
  ⟨2019, 6595, 10240⟩,
  ⟨2739, 6595, 10240⟩,
  ⟨3459, 6595, 10240⟩,
  ⟨4179, 6595, 10240⟩,
  ⟨19, 6595, 10240⟩,
  ⟨1459, 6595, 10240⟩,
  ⟨2179, 13287, 8192⟩,
  ⟨2899, 6595, 10240⟩,
  ⟨3619, 6595, 10240⟩,
  ⟨451, 6595, 10240⟩,
  ⟨1171, 6595, 10240⟩,
  ⟨1891, 6595, 10240⟩,
  ⟨2611, 6595, 10240⟩,
  ⟨4051, 6595, 10240⟩,
  ⟨51, 6595, 10240⟩,
  ⟨771, 13287, 8192⟩,
  ⟨1491, 6595, 10240⟩,
  ⟨2931, 6595, 10240⟩,
  ⟨4371, 6595, 10240⟩,
  ⟨915, 6595, 10240⟩,
  ⟨2355, 6595, 10240⟩,
  ⟨3075, 6595, 10240⟩,
  ⟨3795, 6595, 10240⟩,
  ⟨4515, 6595, 10240⟩,
  ⟨339, 6595, 10240⟩,
  ⟨1059, 6595, 10240⟩,
  ⟨1779, 6595, 10240⟩,
  ⟨2499, 6595, 10240⟩,
  ⟨3939, 6595, 10240⟩,
  ⟨211, 6595, 10240⟩,
  ⟨931, 6595, 10240⟩,
  ⟨2371, 6595, 10240⟩,
  ⟨3811, 6595, 10240⟩,
  ⟨4531, 6595, 10240⟩,
  ⟨499, 13287, 8192⟩,
  ⟨1219, 6595, 10240⟩,
  ⟨1939, 6595, 10240⟩,
  ⟨3379, 6595, 10240⟩,
  ⟨4819, 6595, 10240⟩,
  ⟨99, 6595, 10240⟩,
  ⟨819, 6595, 10240⟩,
  ⟨2259, 6595, 10240⟩,
  ⟨3699, 6595, 10240⟩,
  ⟨4419, 6595, 10240⟩,
  ⟨1251, 6595, 10240⟩,
  ⟨2691, 6595, 10240⟩,
  ⟨3411, 6595, 10240⟩,
  ⟨4131, 13287, 8192⟩,
  ⟨4851, 6595, 10240⟩,
  ⟨675, 6595, 10240⟩,
  ⟨1395, 6595, 10240⟩,
  ⟨2115, 6595, 10240⟩,
  ⟨2835, 6595, 10240⟩,
  ⟨4275, 6595, 10240⟩,
  ⟨259, 6595, 10240⟩,
  ⟨1699, 6595, 10240⟩,
  ⟨3139, 6595, 10240⟩,
  ⟨3859, 6595, 10240⟩,
  ⟨4579, 6595, 10240⟩,
  ⟨691, 6595, 10240⟩,
  ⟨2131, 6595, 10240⟩,
  ⟨2851, 6595, 10240⟩,
  ⟨3571, 6595, 10240⟩,
  ⟨4291, 6595, 10240⟩,
  ⟨1013, 6595, 10240⟩,
  ⟨2453, 6595, 10240⟩,
  ⟨3173, 6595, 10240⟩,
  ⟨3893, 6595, 10240⟩,
  ⟨4613, 6595, 10240⟩,
  ⟨437, 6595, 10240⟩,
  ⟨1157, 6595, 10240⟩,
  ⟨1877, 6595, 10240⟩,
  ⟨2597, 6595, 10240⟩,
  ⟨4037, 6595, 10240⟩,
  ⟨453, 6595, 10240⟩,
  ⟨1893, 6595, 10240⟩,
  ⟨2613, 6595, 10240⟩,
  ⟨3333, 6595, 10240⟩,
  ⟨4053, 6595, 10240⟩,
  ⟨37, 6595, 10240⟩,
  ⟨757, 6595, 10240⟩,
  ⟨1477, 6595, 10240⟩,
  ⟨2917, 6595, 10240⟩,
  ⟨4357, 6595, 10240⟩,
  ⟨773, 6595, 10240⟩,
  ⟨1493, 6595, 10240⟩,
  ⟨2213, 6595, 10240⟩,
  ⟨2933, 6595, 10240⟩,
  ⟨4373, 6595, 10240⟩,
  ⟨197, 6595, 10240⟩,
  ⟨917, 6595, 10240⟩,
  ⟨2357, 13287, 8192⟩,
  ⟨3797, 6595, 10240⟩,
  ⟨4517, 6595, 10240⟩,
  ⟨213, 6595, 10240⟩,
  ⟨933, 6595, 10240⟩,
  ⟨1653, 6595, 10240⟩,
  ⟨2373, 6595, 10240⟩,
  ⟨3813, 6595, 10240⟩,
  ⟨1237, 6595, 10240⟩,
  ⟨2677, 6595, 10240⟩,
  ⟨3397, 6595, 10240⟩,
  ⟨4117, 6595, 10240⟩,
  ⟨4837, 6595, 10240⟩,
  ⟨533, 6595, 10240⟩,
  ⟨1253, 6595, 10240⟩,
  ⟨2693, 6595, 10240⟩,
  ⟨4133, 6595, 10240⟩,
  ⟨4853, 6595, 10240⟩,
  ⟨677, 6595, 10240⟩,
  ⟨2117, 6595, 10240⟩,
  ⟨2837, 6595, 10240⟩,
  ⟨3557, 6595, 10240⟩,
  ⟨4277, 6595, 10240⟩,
  ⟨693, 6595, 10240⟩,
  ⟨2133, 6595, 10240⟩,
  ⟨3573, 6595, 10240⟩,
  ⟨4293, 6595, 10240⟩,
  ⟨5013, 6595, 10240⟩,
  ⟨997, 6595, 10240⟩,
  ⟨1717, 6595, 10240⟩,
  ⟨2437, 6595, 10240⟩,
  ⟨3157, 6595, 10240⟩,
  ⟨4597, 6595, 10240⟩,
  ⟨871, 6595, 10240⟩,
  ⟨1591, 6595, 10240⟩,
  ⟨2311, 6595, 10240⟩,
  ⟨3031, 6595, 10240⟩,
  ⟨4471, 6595, 10240⟩,
  ⟨439, 6595, 10240⟩,
  ⟨1879, 6595, 10240⟩,
  ⟨2599, 13287, 8192⟩,
  ⟨3319, 6595, 10240⟩,
  ⟨4039, 6595, 10240⟩,
  ⟨759, 6595, 10240⟩,
  ⟨1479, 6595, 10240⟩,
  ⟨2199, 6595, 10240⟩,
  ⟨2919, 6595, 10240⟩,
  ⟨4359, 6595, 10240⟩,
  ⟨471, 6595, 10240⟩,
  ⟨1191, 6595, 10240⟩,
  ⟨1911, 6595, 10240⟩,
  ⟨3351, 6595, 10240⟩,
  ⟨4791, 6595, 10240⟩,
  ⟨1335, 6595, 10240⟩,
  ⟨2775, 6595, 10240⟩,
  ⟨3495, 6595, 10240⟩,
  ⟨4215, 6595, 10240⟩,
  ⟨4935, 6595, 10240⟩,
  ⟨199, 6595, 10240⟩,
  ⟨919, 6595, 10240⟩,
  ⟨1639, 6595, 10240⟩,
  ⟨2359, 6595, 10240⟩,
  ⟨3799, 6595, 10240⟩,
  ⟨631, 6595, 10240⟩,
  ⟨1351, 6595, 10240⟩,
  ⟨2791, 6595, 10240⟩,
  ⟨4231, 6595, 10240⟩,
  ⟨4951, 6595, 10240⟩,
  ⟨231, 6595, 10240⟩,
  ⟨1671, 6595, 10240⟩,
  ⟨3111, 6595, 10240⟩,
  ⟨3831, 6595, 10240⟩,
  ⟨4551, 6595, 10240⟩,
  ⟨1095, 6595, 10240⟩,
  ⟨1815, 6595, 10240⟩,
  ⟨2535, 6595, 10240⟩,
  ⟨3255, 6595, 10240⟩,
  ⟨4695, 6595, 10240⟩,
  ⟨519, 6595, 10240⟩,
  ⟨1239, 6595, 10240⟩,
  ⟨2679, 6595, 10240⟩,
  ⟨4119, 6595, 10240⟩,
  ⟨4839, 6595, 10240⟩,
  ⟨1111, 6595, 10240⟩,
  ⟨2551, 6595, 10240⟩,
  ⟨3271, 6595, 10240⟩,
  ⟨3991, 6595, 10240⟩,
  ⟨4711, 6595, 10240⟩,
  ⟨679, 6595, 10240⟩,
  ⟨2119, 6595, 10240⟩,
  ⟨3559, 6595, 10240⟩,
  ⟨4279, 13287, 8192⟩,
  ⟨4999, 6595, 10240⟩,
  ⟨135, 6595, 10240⟩,
  ⟨855, 6595, 10240⟩,
  ⟨1575, 6595, 10240⟩,
  ⟨3015, 6595, 10240⟩,
  ⟨4455, 6595, 10240⟩,
  ⟨999, 6595, 10240⟩,
  ⟨2439, 6595, 10240⟩,
  ⟨3159, 6595, 10240⟩,
  ⟨3879, 6595, 10240⟩,
  ⟨4599, 6595, 10240⟩,
  ⟨1431, 6595, 10240⟩,
  ⟨2151, 13287, 8192⟩,
  ⟨2871, 6595, 10240⟩,
  ⟨3591, 6595, 10240⟩,
  ⟨5031, 6595, 10240⟩,
  ⟨873, 6595, 10240⟩,
  ⟨2313, 13287, 8192⟩,
  ⟨3033, 6595, 10240⟩,
  ⟨3753, 6595, 10240⟩,
  ⟨4473, 6595, 10240⟩,
  ⟨457, 6595, 10240⟩,
  ⟨1177, 6595, 10240⟩,
  ⟨1897, 6595, 10240⟩,
  ⟨3337, 6595, 10240⟩,
  ⟨4777, 6595, 10240⟩,
  ⟨1193, 6595, 10240⟩,
  ⟨1913, 6595, 10240⟩,
  ⟨2633, 6595, 10240⟩,
  ⟨3353, 6595, 10240⟩,
  ⟨4793, 6595, 10240⟩,
  ⟨617, 6595, 10240⟩,
  ⟨1337, 6595, 10240⟩,
  ⟨2777, 6595, 10240⟩,
  ⟨4217, 6595, 10240⟩,
  ⟨4937, 6595, 10240⟩,
  ⟨633, 13287, 8192⟩,
  ⟨1353, 6595, 10240⟩,
  ⟨2073, 6595, 10240⟩,
  ⟨2793, 6595, 10240⟩,
  ⟨4233, 6595, 10240⟩,
  ⟨217, 6595, 10240⟩,
  ⟨1657, 6595, 10240⟩,
  ⟨3097, 6595, 10240⟩,
  ⟨3817, 6595, 10240⟩,
  ⟨4537, 6595, 10240⟩,
  ⟨233, 6595, 10240⟩,
  ⟨953, 6595, 10240⟩,
  ⟨1673, 6595, 10240⟩,
  ⟨3113, 6595, 10240⟩,
  ⟨4553, 6595, 10240⟩,
  ⟨1097, 6595, 10240⟩,
  ⟨2537, 6595, 10240⟩,
  ⟨3257, 6595, 10240⟩,
  ⟨3977, 6595, 10240⟩,
  ⟨4697, 6595, 10240⟩,
  ⟨393, 6595, 10240⟩,
  ⟨1113, 6595, 10240⟩,
  ⟨2553, 6595, 10240⟩,
  ⟨3993, 13287, 8192⟩,
  ⟨4713, 6595, 10240⟩,
  ⟨1417, 6595, 10240⟩,
  ⟨2137, 6595, 10240⟩,
  ⟨2857, 6595, 10240⟩,
  ⟨3577, 6595, 10240⟩,
  ⟨5017, 6595, 10240⟩,
  ⟨857, 6595, 10240⟩,
  ⟨1577, 6595, 10240⟩,
  ⟨2297, 6595, 10240⟩,
  ⟨3017, 6595, 10240⟩,
  ⟨4457, 6595, 10240⟩,
  ⟨1433, 6595, 10240⟩,
  ⟨2873, 6595, 10240⟩,
  ⟨3593, 6595, 10240⟩,
  ⟨4313, 6595, 10240⟩,
  ⟨5033, 6595, 10240⟩
]

def rows17 : List GapWitness := [
  ⟨1, 68583, 141312⟩,
  ⟨721, 68583, 141312⟩,
  ⟨2161, 97273, 139264⟩,
  ⟨3601, 68583, 141312⟩,
  ⟨4321, 68583, 141312⟩,
  ⟨369, 68583, 141312⟩,
  ⟨1809, 68583, 141312⟩,
  ⟨2529, 68583, 141312⟩,
  ⟨3249, 68583, 141312⟩,
  ⟨3969, 68583, 141312⟩,
  ⟨817, 97273, 139264⟩,
  ⟨2257, 68583, 141312⟩,
  ⟨2977, 68583, 141312⟩,
  ⟨3697, 68583, 141312⟩,
  ⟨4417, 68583, 141312⟩,
  ⟨1265, 68583, 141312⟩,
  ⟨2705, 68583, 141312⟩,
  ⟨3425, 68583, 141312⟩,
  ⟨4145, 97273, 139264⟩,
  ⟨4865, 136265, 131072⟩,
  ⟨273, 204848, 139264⟩,
  ⟨1713, 68583, 141312⟩,
  ⟨3153, 68583, 141312⟩,
  ⟨3873, 68583, 141312⟩,
  ⟨4593, 97273, 139264⟩,
  ⟨3, 68583, 141312⟩,
  ⟨723, 68583, 141312⟩,
  ⟨1443, 68583, 141312⟩,
  ⟨2163, 68583, 141312⟩,
  ⟨3603, 97273, 139264⟩,
  ⟨451, 97273, 139264⟩,
  ⟨1171, 136265, 131072⟩,
  ⟨1891, 68583, 141312⟩,
  ⟨2611, 68583, 141312⟩,
  ⟨4051, 68583, 141312⟩,
  ⟨99, 68583, 141312⟩,
  ⟨819, 68583, 141312⟩,
  ⟨2259, 97273, 139264⟩,
  ⟨3699, 68583, 141312⟩,
  ⟨4419, 68583, 141312⟩,
  ⟨547, 68583, 141312⟩,
  ⟨1267, 68583, 141312⟩,
  ⟨2707, 68583, 141312⟩,
  ⟨4147, 97273, 139264⟩,
  ⟨4867, 97273, 139264⟩,
  ⟨5, 68583, 141312⟩,
  ⟨1445, 68583, 141312⟩,
  ⟨2165, 68583, 141312⟩,
  ⟨2885, 97273, 139264⟩,
  ⟨3605, 97273, 139264⟩,
  ⟨453, 68583, 141312⟩,
  ⟨1893, 68583, 141312⟩,
  ⟨2613, 68583, 141312⟩,
  ⟨3333, 97273, 139264⟩,
  ⟨4053, 97273, 139264⟩,
  ⟨901, 68583, 141312⟩,
  ⟨2341, 97273, 139264⟩,
  ⟨3061, 97273, 139264⟩,
  ⟨3781, 68583, 141312⟩,
  ⟨4501, 68583, 141312⟩,
  ⟨549, 68583, 141312⟩,
  ⟨1269, 68583, 141312⟩,
  ⟨1989, 68583, 141312⟩,
  ⟨2709, 68583, 141312⟩,
  ⟨4149, 97273, 139264⟩,
  ⟨997, 136265, 131072⟩,
  ⟨1717, 97273, 139264⟩,
  ⟨2437, 68583, 141312⟩,
  ⟨3157, 68583, 141312⟩,
  ⟨4597, 68583, 141312⟩,
  ⟨7, 68583, 141312⟩,
  ⟨1447, 68583, 141312⟩,
  ⟨2887, 204848, 139264⟩,
  ⟨3607, 97273, 139264⟩,
  ⟨4327, 68583, 141312⟩,
  ⟨183, 68583, 141312⟩,
  ⟨903, 68583, 141312⟩,
  ⟨2343, 97273, 139264⟩,
  ⟨3783, 68583, 141312⟩,
  ⟨4503, 68583, 141312⟩,
  ⟨631, 68583, 141312⟩,
  ⟨1351, 68583, 141312⟩,
  ⟨2791, 68583, 141312⟩,
  ⟨4231, 505037, 8192⟩,
  ⟨4951, 97273, 139264⟩,
  ⟨999, 68583, 141312⟩,
  ⟨2439, 136265, 131072⟩,
  ⟨3159, 97273, 139264⟩,
  ⟨3879, 68583, 141312⟩,
  ⟨4599, 68583, 141312⟩,
  ⟨9, 68583, 141312⟩,
  ⟨729, 68583, 141312⟩,
  ⟨1449, 68583, 141312⟩,
  ⟨2889, 97273, 139264⟩,
  ⟨4329, 68583, 141312⟩,
  ⟨457, 68583, 141312⟩,
  ⟨1177, 68583, 141312⟩,
  ⟨1897, 68583, 141312⟩,
  ⟨3337, 97273, 139264⟩,
  ⟨4777, 68583, 141312⟩,
  ⟨185, 68583, 141312⟩,
  ⟨905, 68583, 141312⟩,
  ⟨1625, 97273, 139264⟩,
  ⟨2345, 97273, 139264⟩,
  ⟨3785, 68583, 141312⟩,
  ⟨633, 68583, 141312⟩,
  ⟨1353, 68583, 141312⟩,
  ⟨2073, 97273, 139264⟩,
  ⟨2793, 97273, 139264⟩,
  ⟨4233, 68583, 141312⟩,
  ⟨1081, 68583, 141312⟩,
  ⟨1801, 68583, 141312⟩,
  ⟨2521, 68583, 141312⟩,
  ⟨3241, 68583, 141312⟩,
  ⟨4681, 97273, 139264⟩
]

def rows18 : List GapWitness := [
  ⟨577, 1508962, 2048⟩,
  ⟨1297, 1508962, 2048⟩,
  ⟨2017, 1508962, 2048⟩,
  ⟨2737, 1508962, 2048⟩,
  ⟨4177, 1508962, 2048⟩,
  ⟨513, 1508962, 2048⟩,
  ⟨1233, 1508962, 2048⟩,
  ⟨1953, 1508962, 2048⟩,
  ⟨3393, 1508962, 2048⟩,
  ⟨4833, 1508962, 2048⟩,
  ⟨817, 1508962, 2048⟩,
  ⟨2257, 1508962, 2048⟩,
  ⟨2977, 1508962, 2048⟩,
  ⟨3697, 1508962, 2048⟩,
  ⟨4417, 1508962, 2048⟩,
  ⟨113, 1508962, 2048⟩,
  ⟨833, 1508962, 2048⟩,
  ⟨2273, 1508962, 2048⟩,
  ⟨3713, 1508962, 2048⟩,
  ⟨4433, 1508962, 2048⟩,
  ⟨257, 2617000, 8192⟩,
  ⟨1697, 1508962, 2048⟩,
  ⟨2417, 1508962, 2048⟩,
  ⟨3137, 1508962, 2048⟩,
  ⟨3857, 1508962, 2048⟩,
  ⟨273, 1508962, 2048⟩,
  ⟨1713, 1508962, 2048⟩,
  ⟨3153, 1508962, 2048⟩,
  ⟨3873, 1508962, 2048⟩,
  ⟨4593, 1508962, 2048⟩,
  ⟨1011, 1508962, 2048⟩,
  ⟨1731, 1508962, 2048⟩,
  ⟨2451, 1508962, 2048⟩,
  ⟨3171, 1508962, 2048⟩,
  ⟨4611, 1508962, 2048⟩,
  ⟨435, 1508962, 2048⟩,
  ⟨1155, 1508962, 2048⟩,
  ⟨2595, 1508962, 2048⟩,
  ⟨4035, 1508962, 2048⟩,
  ⟨4755, 1508962, 2048⟩,
  ⟨579, 1508962, 2048⟩,
  ⟨2019, 1508962, 2048⟩,
  ⟨2739, 1508962, 2048⟩,
  ⟨3459, 1508962, 2048⟩,
  ⟨4179, 1508962, 2048⟩,
  ⟨19, 1508962, 2048⟩,
  ⟨1459, 1508962, 2048⟩,
  ⟨2179, 1508962, 2048⟩,
  ⟨2899, 1508962, 2048⟩,
  ⟨3619, 1508962, 2048⟩,
  ⟨451, 2617000, 8192⟩,
  ⟨1171, 1508962, 2048⟩,
  ⟨1891, 1508962, 2048⟩,
  ⟨2611, 1508962, 2048⟩,
  ⟨4051, 1508962, 2048⟩,
  ⟨99, 2617000, 8192⟩,
  ⟨819, 1508962, 2048⟩,
  ⟨2259, 1508962, 2048⟩,
  ⟨3699, 1508962, 2048⟩,
  ⟨4419, 2617000, 8192⟩,
  ⟨1251, 1508962, 2048⟩,
  ⟨2691, 1508962, 2048⟩,
  ⟨3411, 2617000, 8192⟩,
  ⟨4131, 1508962, 2048⟩,
  ⟨4851, 1508962, 2048⟩,
  ⟨675, 1508962, 2048⟩,
  ⟨1395, 1508962, 2048⟩,
  ⟨2115, 1508962, 2048⟩,
  ⟨2835, 1508962, 2048⟩,
  ⟨4275, 1508962, 2048⟩,
  ⟨259, 203350711, 139264⟩,
  ⟨1699, 1508962, 2048⟩,
  ⟨3139, 1508962, 2048⟩,
  ⟨3859, 1508962, 2048⟩,
  ⟨4579, 1508962, 2048⟩,
  ⟨691, 1508962, 2048⟩,
  ⟨2131, 1508962, 2048⟩,
  ⟨2851, 1508962, 2048⟩,
  ⟨3571, 1508962, 2048⟩,
  ⟨4291, 1508962, 2048⟩,
  ⟨1013, 1508962, 2048⟩,
  ⟨2453, 1508962, 2048⟩,
  ⟨3173, 1508962, 2048⟩,
  ⟨3893, 1508962, 2048⟩,
  ⟨4613, 1508962, 2048⟩,
  ⟨437, 1508962, 2048⟩,
  ⟨1157, 1508962, 2048⟩,
  ⟨1877, 1508962, 2048⟩,
  ⟨2597, 1508962, 2048⟩,
  ⟨4037, 1508962, 2048⟩,
  ⟨453, 1508962, 2048⟩,
  ⟨1893, 1508962, 2048⟩,
  ⟨2613, 1508962, 2048⟩,
  ⟨3333, 1508962, 2048⟩,
  ⟨4053, 1508962, 2048⟩,
  ⟨37, 1508962, 2048⟩,
  ⟨757, 1508962, 2048⟩,
  ⟨1477, 1508962, 2048⟩,
  ⟨2917, 1508962, 2048⟩,
  ⟨4357, 1508962, 2048⟩,
  ⟨693, 1508962, 2048⟩,
  ⟨2133, 1508962, 2048⟩,
  ⟨3573, 2617000, 8192⟩,
  ⟨4293, 1508962, 2048⟩,
  ⟨5013, 1508962, 2048⟩,
  ⟨997, 1508962, 2048⟩,
  ⟨1717, 1508962, 2048⟩,
  ⟨2437, 1508962, 2048⟩,
  ⟨3157, 1508962, 2048⟩,
  ⟨4597, 1508962, 2048⟩,
  ⟨871, 1508962, 2048⟩,
  ⟨1591, 1508962, 2048⟩,
  ⟨2311, 1508962, 2048⟩,
  ⟨3031, 1508962, 2048⟩,
  ⟨4471, 1508962, 2048⟩,
  ⟨439, 1508962, 2048⟩,
  ⟨1879, 1508962, 2048⟩,
  ⟨2599, 1508962, 2048⟩,
  ⟨3319, 1508962, 2048⟩,
  ⟨4039, 1508962, 2048⟩,
  ⟨759, 1508962, 2048⟩,
  ⟨1479, 1508962, 2048⟩,
  ⟨2199, 1508962, 2048⟩,
  ⟨2919, 1508962, 2048⟩,
  ⟨4359, 1508962, 2048⟩,
  ⟨471, 1508962, 2048⟩,
  ⟨1191, 1508962, 2048⟩,
  ⟨1911, 1508962, 2048⟩,
  ⟨3351, 1508962, 2048⟩,
  ⟨4791, 1508962, 2048⟩,
  ⟨1335, 1508962, 2048⟩,
  ⟨2775, 1508962, 2048⟩,
  ⟨3495, 1508962, 2048⟩,
  ⟨4215, 1508962, 2048⟩,
  ⟨4935, 1508962, 2048⟩,
  ⟨199, 1508962, 2048⟩,
  ⟨919, 2617000, 8192⟩,
  ⟨1639, 2617000, 8192⟩,
  ⟨2359, 1508962, 2048⟩,
  ⟨3799, 1508962, 2048⟩,
  ⟨631, 1508962, 2048⟩,
  ⟨1351, 1508962, 2048⟩,
  ⟨2791, 1508962, 2048⟩,
  ⟨4231, 1508962, 2048⟩,
  ⟨4951, 2617000, 8192⟩,
  ⟨135, 1508962, 2048⟩,
  ⟨855, 1508962, 2048⟩,
  ⟨1575, 1508962, 2048⟩,
  ⟨3015, 1508962, 2048⟩,
  ⟨4455, 2617000, 8192⟩,
  ⟨999, 1508962, 2048⟩,
  ⟨2439, 1508962, 2048⟩,
  ⟨3159, 1508962, 2048⟩,
  ⟨3879, 1508962, 2048⟩,
  ⟨4599, 1508962, 2048⟩,
  ⟨1431, 1508962, 2048⟩,
  ⟨2151, 1508962, 2048⟩,
  ⟨2871, 1508962, 2048⟩,
  ⟨3591, 1508962, 2048⟩,
  ⟨5031, 1508962, 2048⟩,
  ⟨873, 1508962, 2048⟩,
  ⟨2313, 1508962, 2048⟩,
  ⟨3033, 1508962, 2048⟩,
  ⟨3753, 1508962, 2048⟩,
  ⟨4473, 1508962, 2048⟩,
  ⟨457, 1508962, 2048⟩,
  ⟨1177, 1508962, 2048⟩,
  ⟨1897, 1508962, 2048⟩,
  ⟨3337, 1508962, 2048⟩,
  ⟨4777, 1508962, 2048⟩,
  ⟨1193, 2617000, 8192⟩,
  ⟨1913, 1508962, 2048⟩,
  ⟨2633, 1508962, 2048⟩,
  ⟨3353, 1508962, 2048⟩,
  ⟨4793, 1508962, 2048⟩,
  ⟨617, 1508962, 2048⟩,
  ⟨1337, 1508962, 2048⟩,
  ⟨2777, 1508962, 2048⟩,
  ⟨4217, 1508962, 2048⟩,
  ⟨4937, 1508962, 2048⟩,
  ⟨633, 1508962, 2048⟩,
  ⟨1353, 1508962, 2048⟩,
  ⟨2073, 2617000, 8192⟩,
  ⟨2793, 1508962, 2048⟩,
  ⟨4233, 1508962, 2048⟩,
  ⟨217, 1508962, 2048⟩,
  ⟨1657, 1508962, 2048⟩,
  ⟨3097, 2617000, 8192⟩,
  ⟨3817, 1508962, 2048⟩,
  ⟨4537, 1508962, 2048⟩
]

def rows19 : List GapWitness := [
  ⟨1, 507820, 532480⟩,
  ⟨721, 1903061, 139264⟩,
  ⟨2161, 507820, 532480⟩,
  ⟨3601, 1903061, 139264⟩,
  ⟨4321, 507820, 532480⟩,
  ⟨289, 507820, 532480⟩,
  ⟨1009, 507820, 532480⟩,
  ⟨1729, 4323404, 131072⟩,
  ⟨3169, 507820, 532480⟩,
  ⟨4609, 1903061, 139264⟩,
  ⟨801, 1903061, 139264⟩,
  ⟨1521, 1903061, 139264⟩,
  ⟨2241, 507820, 532480⟩,
  ⟨2961, 1903061, 139264⟩,
  ⟨4401, 507820, 532480⟩,
  ⟨225, 1903061, 139264⟩,
  ⟨945, 1903061, 139264⟩,
  ⟨2385, 1903061, 139264⟩,
  ⟨3825, 507820, 532480⟩,
  ⟨4545, 507820, 532480⟩,
  ⟨369, 507820, 532480⟩,
  ⟨1809, 1903061, 139264⟩,
  ⟨2529, 507820, 532480⟩,
  ⟨3249, 507820, 532480⟩,
  ⟨3969, 4287912, 524288⟩,
  ⟨241, 507820, 532480⟩,
  ⟨961, 4323404, 131072⟩,
  ⟨1681, 507820, 532480⟩,
  ⟨2401, 507820, 532480⟩,
  ⟨3841, 1903061, 139264⟩,
  ⟨1249, 1903061, 139264⟩,
  ⟨1969, 1903061, 139264⟩,
  ⟨2689, 507820, 532480⟩,
  ⟨3409, 507820, 532480⟩,
  ⟨4849, 1903061, 139264⟩,
  ⟨1265, 507820, 532480⟩,
  ⟨2705, 1903061, 139264⟩,
  ⟨3425, 507820, 532480⟩,
  ⟨4145, 1903061, 139264⟩,
  ⟨4865, 1903061, 139264⟩,
  ⟨129, 1903061, 139264⟩,
  ⟨849, 1903061, 139264⟩,
  ⟨1569, 507820, 532480⟩,
  ⟨2289, 507820, 532480⟩,
  ⟨3729, 3298302, 133120⟩,
  ⟨561, 1903061, 139264⟩,
  ⟨1281, 507820, 532480⟩,
  ⟨2721, 1903061, 139264⟩,
  ⟨4161, 507820, 532480⟩,
  ⟨4881, 1903061, 139264⟩,
  ⟨705, 507820, 532480⟩,
  ⟨2145, 1903061, 139264⟩,
  ⟨2865, 507820, 532480⟩,
  ⟨3585, 507820, 532480⟩,
  ⟨4305, 1903061, 139264⟩,
  ⟨3, 1903061, 139264⟩,
  ⟨723, 507820, 532480⟩,
  ⟨1443, 1903061, 139264⟩,
  ⟨2163, 1903061, 139264⟩,
  ⟨3603, 507820, 532480⟩,
  ⟨1027, 1903061, 139264⟩,
  ⟨2467, 507820, 532480⟩,
  ⟨3187, 507820, 532480⟩,
  ⟨3907, 1903061, 139264⟩,
  ⟨4627, 1903061, 139264⟩,
  ⟨243, 1903061, 139264⟩,
  ⟨1683, 507820, 532480⟩,
  ⟨2403, 507820, 532480⟩,
  ⟨3123, 1903061, 139264⟩,
  ⟨3843, 507820, 532480⟩,
  ⟨547, 507820, 532480⟩,
  ⟨1267, 1903061, 139264⟩,
  ⟨2707, 507820, 532480⟩,
  ⟨4147, 1903061, 139264⟩,
  ⟨4867, 1903061, 139264⟩,
  ⟨5, 507820, 532480⟩,
  ⟨1445, 1903061, 139264⟩,
  ⟨2165, 1903061, 139264⟩,
  ⟨2885, 507820, 532480⟩,
  ⟨3605, 507820, 532480⟩,
  ⟨21, 1903061, 139264⟩,
  ⟨1461, 1903061, 139264⟩,
  ⟨2901, 507820, 532480⟩,
  ⟨3621, 507820, 532480⟩,
  ⟨4341, 1903061, 139264⟩,
  ⟨885, 1903061, 139264⟩,
  ⟨1605, 1903061, 139264⟩,
  ⟨2325, 507820, 532480⟩,
  ⟨3045, 507820, 532480⟩,
  ⟨4485, 1903061, 139264⟩,
  ⟨309, 1903061, 139264⟩,
  ⟨1029, 1903061, 139264⟩,
  ⟨2469, 1903061, 139264⟩,
  ⟨3909, 507820, 532480⟩,
  ⟨4629, 507820, 532480⟩,
  ⟨901, 1903061, 139264⟩,
  ⟨2341, 1903061, 139264⟩,
  ⟨3061, 1903061, 139264⟩,
  ⟨3781, 507820, 532480⟩,
  ⟨4501, 507820, 532480⟩,
  ⟨469, 507820, 532480⟩,
  ⟨1909, 1903061, 139264⟩,
  ⟨3349, 3298302, 133120⟩,
  ⟨4069, 1903061, 139264⟩,
  ⟨4789, 507820, 532480⟩,
  ⟨261, 1903061, 139264⟩,
  ⟨981, 1903061, 139264⟩,
  ⟨1701, 507820, 532480⟩,
  ⟨3141, 3298302, 133120⟩,
  ⟨4581, 507820, 532480⟩,
  ⟨1125, 507820, 532480⟩,
  ⟨2565, 1903061, 139264⟩,
  ⟨3285, 1903061, 139264⟩,
  ⟨4005, 507820, 532480⟩,
  ⟨4725, 3298302, 133120⟩,
  ⟨549, 507820, 532480⟩,
  ⟨1269, 1903061, 139264⟩,
  ⟨1989, 1903061, 139264⟩,
  ⟨2709, 507820, 532480⟩,
  ⟨4149, 1903061, 139264⟩,
  ⟨421, 1903061, 139264⟩,
  ⟨1141, 1903061, 139264⟩,
  ⟨2581, 4287912, 524288⟩,
  ⟨4021, 507820, 532480⟩,
  ⟨4741, 507820, 532480⟩,
  ⟨709, 507820, 532480⟩,
  ⟨1429, 1903061, 139264⟩,
  ⟨2149, 1903061, 139264⟩,
  ⟨3589, 1903061, 139264⟩,
  ⟨5029, 507820, 532480⟩,
  ⟨7, 507820, 532480⟩,
  ⟨1447, 1903061, 139264⟩,
  ⟨2887, 507820, 532480⟩,
  ⟨3607, 1903061, 139264⟩,
  ⟨4327, 4287912, 524288⟩,
  ⟨183, 507820, 532480⟩,
  ⟨903, 507820, 532480⟩,
  ⟨2343, 507820, 532480⟩,
  ⟨3783, 1903061, 139264⟩,
  ⟨4503, 1903061, 139264⟩,
  ⟨1207, 1903061, 139264⟩,
  ⟨1927, 507820, 532480⟩,
  ⟨2647, 507820, 532480⟩,
  ⟨3367, 1903061, 139264⟩,
  ⟨4807, 507820, 532480⟩,
  ⟨423, 1903061, 139264⟩,
  ⟨1143, 507820, 532480⟩,
  ⟨1863, 507820, 532480⟩,
  ⟨2583, 4287912, 524288⟩,
  ⟨4023, 507820, 532480⟩,
  ⟨9, 1903061, 139264⟩,
  ⟨729, 1903061, 139264⟩,
  ⟨1449, 507820, 532480⟩,
  ⟨2889, 1903061, 139264⟩,
  ⟨4329, 507820, 532480⟩,
  ⟨441, 1903061, 139264⟩,
  ⟨1881, 3298302, 133120⟩,
  ⟨3321, 507820, 532480⟩,
  ⟨4041, 507820, 532480⟩,
  ⟨4761, 1903061, 139264⟩,
  ⟨1305, 1903061, 139264⟩,
  ⟨2025, 1903061, 139264⟩,
  ⟨2745, 507820, 532480⟩,
  ⟨3465, 507820, 532480⟩,
  ⟨4905, 507820, 532480⟩,
  ⟨169, 1903061, 139264⟩,
  ⟨889, 1903061, 139264⟩,
  ⟨2329, 507820, 532480⟩,
  ⟨3769, 507820, 532480⟩,
  ⟨4489, 507820, 532480⟩,
  ⟨1321, 507820, 532480⟩,
  ⟨2761, 1903061, 139264⟩,
  ⟨3481, 507820, 532480⟩,
  ⟨4201, 1903061, 139264⟩,
  ⟨4921, 1903061, 139264⟩,
  ⟨185, 507820, 532480⟩,
  ⟨905, 1903061, 139264⟩,
  ⟨1625, 507820, 532480⟩,
  ⟨2345, 507820, 532480⟩,
  ⟨3785, 1903061, 139264⟩,
  ⟨201, 507820, 532480⟩,
  ⟨1641, 3298302, 133120⟩,
  ⟨2361, 507820, 532480⟩,
  ⟨3081, 1903061, 139264⟩,
  ⟨3801, 1903061, 139264⟩,
  ⟨345, 1903061, 139264⟩,
  ⟨1065, 1903061, 139264⟩,
  ⟨1785, 507820, 532480⟩,
  ⟨3225, 1903061, 139264⟩,
  ⟨4665, 507820, 532480⟩,
  ⟨1209, 507820, 532480⟩,
  ⟨2649, 1903061, 139264⟩,
  ⟨3369, 507820, 532480⟩,
  ⟨4089, 1903061, 139264⟩,
  ⟨4809, 1903061, 139264⟩,
  ⟨1081, 507820, 532480⟩,
  ⟨1801, 1903061, 139264⟩,
  ⟨2521, 1903061, 139264⟩,
  ⟨3241, 507820, 532480⟩,
  ⟨4681, 1903061, 139264⟩,
  ⟨649, 1903061, 139264⟩,
  ⟨2089, 507820, 532480⟩,
  ⟨2809, 1903061, 139264⟩,
  ⟨3529, 1903061, 139264⟩,
  ⟨4249, 507820, 532480⟩
]

def rows21 : List GapWitness := [
  ⟨2961, 121607, 532480⟩,
  ⟨945, 121607, 532480⟩,
  ⟨3969, 121607, 532480⟩,
  ⟨3425, 121607, 532480⟩,
  ⟨4145, 121607, 532480⟩,
  ⟨2289, 121607, 532480⟩,
  ⟨1281, 121607, 532480⟩,
  ⟨4305, 378211, 655360⟩,
  ⟨2163, 121607, 532480⟩,
  ⟨3843, 121607, 532480⟩,
  ⟨2165, 121607, 532480⟩,
  ⟨2885, 378211, 655360⟩,
  ⟨21, 121607, 532480⟩,
  ⟨3045, 121607, 532480⟩,
  ⟨1029, 121607, 532480⟩,
  ⟨1701, 121607, 532480⟩,
  ⟨4725, 121607, 532480⟩,
  ⟨2709, 121607, 532480⟩,
  ⟨903, 121607, 532480⟩,
  ⟨2583, 121607, 532480⟩,
  ⟨1449, 121607, 532480⟩,
  ⟨441, 121607, 532480⟩,
  ⟨3465, 121607, 532480⟩,
  ⟨905, 121607, 532480⟩,
  ⟨1625, 121607, 532480⟩,
  ⟨3801, 121607, 532480⟩,
  ⟨1785, 121607, 532480⟩,
  ⟨4809, 121607, 532480⟩
]

def rows23 : List GapWitness := [
  ⟨1, 254035, 141312⟩,
  ⟨721, 13949220, 10240⟩,
  ⟨1809, 13109053, 534528⟩,
  ⟨2529, 13109053, 534528⟩,
  ⟨3969, 254035, 141312⟩,
  ⟨1681, 254035, 141312⟩,
  ⟨2401, 13695185, 524288⟩,
  ⟨129, 13949220, 10240⟩,
  ⟨849, 254035, 141312⟩,
  ⟨2289, 254035, 141312⟩,
  ⟨3, 254035, 141312⟩,
  ⟨723, 254035, 141312⟩,
  ⟨2163, 13109053, 534528⟩,
  ⟨1683, 254035, 141312⟩,
  ⟨2403, 254035, 141312⟩,
  ⟨3843, 104245647, 8912896⟩,
  ⟨5, 13109053, 534528⟩,
  ⟨2165, 254035, 141312⟩,
  ⟨2885, 254035, 141312⟩,
  ⟨7, 254035, 141312⟩,
  ⟨4327, 13949220, 10240⟩,
  ⟨2647, 13109053, 534528⟩,
  ⟨3367, 254035, 141312⟩,
  ⟨9, 13109053, 534528⟩,
  ⟨1449, 254035, 141312⟩,
  ⟨4329, 254035, 141312⟩,
  ⟨4201, 254035, 141312⟩,
  ⟨4921, 13109053, 534528⟩,
  ⟨2649, 13109053, 534528⟩,
  ⟨3369, 13109053, 534528⟩,
  ⟨4809, 254035, 141312⟩,
  ⟨2521, 254035, 141312⟩,
  ⟨3241, 13109053, 534528⟩
]

def rows25 : List GapWitness := [
  ⟨4327, 1150328, 8388608⟩,
  ⟨15127, 1150328, 8388608⟩,
  ⟨12727, 1150328, 8388608⟩,
  ⟨23527, 1150328, 8388608⟩
]

def rows27 : List GapWitness := [
  ⟨12609, 0, 0⟩,
  ⟨67203, 0, 0⟩,
  ⟨50409, 0, 0⟩
]

def rows29 : List GapWitness := [
  ⟨27729, 90778167, 131072⟩,
  ⟨52929, 90778167, 131072⟩,
  ⟨36129, 90778167, 131072⟩,
  ⟨15125, 90778167, 131072⟩,
  ⟨47525, 90778167, 131072⟩,
  ⟨58325, 90778167, 131072⟩,
  ⟨15127, 90778167, 131072⟩,
  ⟨73927, 90778167, 131072⟩,
  ⟨15129, 90778167, 131072⟩,
  ⟨73929, 90778167, 131072⟩,
  ⟨65529, 90778167, 131072⟩
]

def rows31 : List GapWitness := [
  ⟨47525, 9888874322, 545267712⟩,
  ⟨90725, 9888874322, 545267712⟩,
  ⟨133925, 9888874322, 545267712⟩,
  ⟨90727, 9888874322, 545267712⟩,
  ⟨73927, 9888874322, 545267712⟩,
  ⟨90729, 30483296258, 141312⟩,
  ⟨141129, 9888874322, 545267712⟩,
  ⟨73929, 9888874322, 545267712⟩
]

def rows33 : List GapWitness := [
  ⟨52929, 0, 0⟩,
  ⟨103329, 0, 0⟩,
  ⟨36129, 0, 0⟩,
  ⟨47525, 0, 0⟩,
  ⟨90725, 0, 0⟩,
  ⟨133925, 0, 0⟩,
  ⟨90727, 0, 0⟩,
  ⟨73927, 0, 0⟩,
  ⟨90729, 0, 0⟩,
  ⟨141129, 0, 0⟩,
  ⟨73929, 0, 0⟩
]

def rows35 : List GapWitness := []

def rows37 : List GapWitness := [
  ⟨52929, 151480213837, 2147485696⟩,
  ⟨103329, 151480213837, 2147485696⟩,
  ⟨90725, 119666349459, 545259520⟩,
  ⟨90727, 151480213837, 2147485696⟩,
  ⟨90729, 151480213837, 2147485696⟩,
  ⟨141129, 151480213837, 2147485696⟩
]

def rows39 : List GapWitness := [
  ⟨1, 0, 0⟩,
  ⟨60481, 0, 0⟩,
  ⟨113409, 0, 0⟩,
  ⟨52929, 0, 0⟩,
  ⟨12609, 0, 0⟩,
  ⟨103329, 0, 0⟩,
  ⟨3, 0, 0⟩,
  ⟨60483, 0, 0⟩,
  ⟨5, 0, 0⟩,
  ⟨90725, 0, 0⟩,
  ⟨7, 0, 0⟩,
  ⟨90727, 0, 0⟩,
  ⟨9, 0, 0⟩,
  ⟨90729, 0, 0⟩,
  ⟨50409, 0, 0⟩,
  ⟨141129, 0, 0⟩,
  ⟨98281, 0, 0⟩,
  ⟨37801, 0, 0⟩
]

def rows41 : List GapWitness := [
  ⟨52929, 302201086894, 2692876288⟩,
  ⟨103329, 2235198270553, 2148009984⟩,
  ⟨90725, 294697075269, 139595481088⟩,
  ⟨90727, 2235198270553, 2148009984⟩,
  ⟨90729, 2235198270553, 2148009984⟩,
  ⟨141129, 2235198270553, 2148009984⟩
]

def rows43 : List GapWitness := [
  ⟨52929, 1323727805715251, 2339155091456⟩,
  ⟨103329, 1418633781541164, 137439092736⟩,
  ⟨90725, 696792999531165, 137447473152⟩,
  ⟨90727, 1418633781541164, 137439092736⟩,
  ⟨90729, 1323727805715251, 2339155091456⟩,
  ⟨141129, 1323727805715251, 2339155091456⟩
]

def rows45 : List GapWitness := []

def rows47 : List GapWitness := [
  ⟨1, 0, 0⟩,
  ⟨60481, 0, 0⟩,
  ⟨3, 0, 0⟩,
  ⟨60483, 0, 0⟩,
  ⟨5, 0, 0⟩,
  ⟨90725, 10781896869685107, 8798248894464⟩,
  ⟨7, 0, 0⟩,
  ⟨90727, 43865003665939973, 536879104⟩,
  ⟨9, 0, 0⟩,
  ⟨90729, 43865003665939973, 536879104⟩,
  ⟨50409, 0, 0⟩,
  ⟨141129, 26222735616978401, 10995116810240⟩
]


private theorem gap_impossible {d : TestData} {rows : List GapWitness}
    (v : bridgeValid d) (hL : d.radices.prod = d.smallMod) (hpos : 0 < d.smallMod)
    (hM : 0 < d.modulus) (cert : gapCertificate d rows = true) {k : ℕ}
    (h : MatchesDigits d.n k) : False := by
  obtain ⟨hs,hc,he⟩ := match_bridge v h
  exact gap_certificate_excludes cert hL hM (Nat.mod_lt k hpos) hs hc he

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem finite_case {n k : ℕ} (hn : 15 ≤ n) (hc : n ≤ 48) (h : MatchesDigits n k) : False := by
  by_cases hev : 19 ≤ n ∧ n % 2 = 0
  · exact even_length_impossible hev.1 hev.2 h
  have hcases : n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 21 ∨ n = 23 ∨ n = 25 ∨ n = 27 ∨ n = 29 ∨ n = 31 ∨ n = 33 ∨ n = 35 ∨ n = 37 ∨ n = 39 ∨ n = 41 ∨ n = 43 ∨ n = 45 ∨ n = 47 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gap_impossible (d := test15) (rows := rows15) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test16) (rows := rows16) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test17) (rows := rows17) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test18) (rows := rows18) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test19) (rows := rows19) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test21) (rows := rows21) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test23) (rows := rows23) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test25) (rows := rows25) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test27) (rows := rows27) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test29) (rows := rows29) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test31) (rows := rows31) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test33) (rows := rows33) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test35) (rows := rows35) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test37) (rows := rows37) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test39) (rows := rows39) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test41) (rows := rows41) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test43) (rows := rows43) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test45) (rows := rows45) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h
  · exact gap_impossible (d := test47) (rows := rows47) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) h

end OMA.S_oeis_a284814

open OMA.S_oeis_a284814

theorem OMA.solution : type_of% @OMA.S_oeis_a284814.main := by
  intro n k hn h
  by_cases hsmall : n ≤ 48
  · exact finite_case hn hsmall h
  · exact tail_case (by omega) h
