import OMAStatements.S_oeis_a061641

-- Douglas Shaw discusses the density in The Fibonacci Quarterly 44 (2006), Corollary 5.1.
-- The proof below controls the contribution of long witnesses by counting first returns.
open OMA.S_oeis_a061641

open Filter Topology Finset Function

namespace PureProof

noncomputable def cnt (P : ℕ → Prop) : ℕ → ℕ := @Nat.count P (Classical.decPred P)
noncomputable def freq (P : ℕ → Prop) (n : ℕ) : ℝ := (cnt P n : ℝ) / n

def Reg (P : ℕ → Prop) : Prop :=
  ∃ m > 0, ∃ Q : ℕ → Prop, ∀ᶠ n : ℕ in atTop, P n ↔ Q (n % m)

lemma reg_congr {P Q : ℕ → Prop} (h : ∀ᶠ n in atTop, P n ↔ Q n) (hq : Reg Q) : Reg P := by
  obtain ⟨m, hm, R, hR⟩ := hq
  exact ⟨m, hm, R, h.and hR |>.mono fun _ h => h.1.trans h.2⟩

lemma reg_const (p : Prop) : Reg (fun _ => p) :=
  ⟨1, by decide, fun _ => p, Eventually.of_forall fun _ => Iff.rfl⟩

lemma reg_or {P Q : ℕ → Prop} (hp : Reg P) (hq : Reg Q) : Reg (fun n => P n ∨ Q n) := by
  obtain ⟨a,ha,R,hR⟩ := hp
  obtain ⟨b,hb,S,hS⟩ := hq
  refine ⟨a*b, by positivity, fun r => R (r%a) ∨ S (r%b), ?_⟩
  filter_upwards [hR,hS] with n hn hn'
  simpa [Nat.mod_mod_of_dvd, hn, hn']

lemma reg_ex (P : ℕ → ℕ → Prop) (m : ℕ) (h : ∀ i < m, Reg (P i)) :
    Reg (fun n => ∃ i < m, P i n) := by
  induction m with
  | zero => simpa using reg_const False
  | succ m ih =>
    apply reg_congr _ (reg_or (ih fun i hi => h i (by omega)) (h m (by omega)))
    exact Eventually.of_forall fun n => by grind

lemma cnt_close {P Q : ℕ → Prop} (h : ∀ᶠ n in atTop, P n ↔ Q n) :
    ∃ C : ℝ, ∀ n, |(cnt P n : ℝ) - cnt Q n| ≤ C := by
  classical
  obtain ⟨M,hM⟩ := eventually_atTop.1 h
  refine ⟨M, fun n => ?_⟩
  have hp := Nat.count_le P (n := min n M)
  have hq := Nat.count_le Q (n := min n M)
  by_cases hn : n ≤ M
  · simp [min_eq_left hn] at hp hq
    dsimp [cnt]
    rw [abs_le]
    constructor <;> linarith [show (Nat.count P n:ℝ) ≤ M by exact_mod_cast hp.trans hn, show (Nat.count Q n:ℝ) ≤ M by exact_mod_cast hq.trans hn, Nat.cast_nonneg (α:=ℝ) (Nat.count P n), Nat.cast_nonneg (α:=ℝ) (Nat.count Q n)]
  · simp [min_eq_right (by omega : M ≤ n)] at hp hq
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : M ≤ n)
    have he : (fun j => P (M+j)) = fun j => Q (M+j) := funext fun j => propext (hM _ (by omega))
    dsimp [cnt]
    rw [Nat.count_add, Nat.count_add]
    have hcnt := congrArg (fun R => cnt R k) he
    change cnt _ k = cnt _ k at hcnt
    simp only [cnt] at hcnt
    rw [hcnt]
    push_cast
    rw [abs_le]
    constructor <;> linarith [show (Nat.count P M:ℝ) ≤ M by exact_mod_cast hp, show (Nat.count Q M:ℝ) ≤ M by exact_mod_cast hq, Nat.cast_nonneg (α:=ℝ) (Nat.count P M), Nat.cast_nonneg (α:=ℝ) (Nat.count Q M)]

lemma tendsto_freq_error {P : ℕ → Prop} {d C : ℝ}
    (h : ∀ n, |(cnt P n : ℝ) - n * d| ≤ C) : Tendsto (freq P) atTop (𝓝 d) := by
  have hz := tendsto_const_div_atTop_nhds_zero_nat (C := C)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hz.eventually_lt_const hε, eventually_gt_atTop 0] with n hn hn'
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn'
  rw [Real.dist_eq, freq, div_sub' (by positivity : (n:ℝ) ≠ 0), abs_div, abs_of_pos hn0]
  exact ((div_le_div_iff_of_pos_right hn0).2 (by simpa [mul_comm] using h n)).trans_lt hn

lemma mod_error (m : ℕ) (hm : m > 0) (Q : ℕ → Prop) :
    ∃ C : ℝ, ∀ n, |(cnt (fun j => Q (j%m)) n : ℝ) - n * freq (fun j => Q (j%m)) m| ≤ C := by
  classical
  let P := fun j : ℕ => Q (j%m)
  have blocks (k : ℕ) : cnt P (m*k) = k * cnt P m := by
    induction k with
    | zero => simp [cnt]
    | succ k ih =>
      rw [Nat.mul_succ, show cnt P (m*k+m) = cnt P (m*k) + cnt P m by
        simp [cnt, Nat.count_add P (m*k) m, P, Nat.add_mod], ih, Nat.succ_mul]
  refine ⟨2*m, fun n => ?_⟩
  have hdiv := Nat.mod_add_div n m
  let r := n % m
  let k := n / m
  have eqn : n = m*k+r := by dsimp [k,r]; omega
  have hc : cnt P n = k * cnt P m + cnt P r := by
    conv_lhs => rw [eqn]
    simpa [cnt, Nat.count_add, P, Nat.add_mod] using congrArg (· + cnt P r) (blocks k)
  have hr : r < m := Nat.mod_lt _ hm
  have hd0 : 0 ≤ freq P m := by unfold freq; positivity
  have hd1 : freq P m ≤ 1 := by
    rw [freq, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast Nat.count_le P
  have he : (m:ℝ) * freq P m = cnt P m := by
    rw [freq, mul_div_cancel₀ _ (by exact_mod_cast hm.ne' : (m:ℝ) ≠ 0)] <;> ring
  change |(cnt P n : ℝ) - n * freq P m| ≤ _
  rw [hc]
  have hne : (n:ℝ) = (m:ℝ)*k+r := by exact_mod_cast eqn
  push_cast
  rw [hne, add_mul, mul_right_comm, he]
  have hrc : cnt P r ≤ r := Nat.count_le _
  rw [abs_le]
  constructor <;> nlinarith [show (r:ℝ) < m by exact_mod_cast hr, show (cnt P r:ℝ) ≤ r by exact_mod_cast hrc, Nat.cast_nonneg (α:=ℝ) (cnt P r), show (r:ℝ) * freq P m ≤ r by nlinarith, show 0 ≤ (r:ℝ)*freq P m by positivity]

lemma mod_limit (m : ℕ) (hm : 0 < m) (Q : ℕ → Prop) :
    Tendsto (freq (fun j => Q (j%m))) atTop (𝓝 (freq (fun j => Q (j%m)) m)) := by
  obtain ⟨C,h⟩ := mod_error m hm Q
  exact tendsto_freq_error h

lemma reg_limit {P : ℕ → Prop} (h : Reg P) : ∃ d, Tendsto (freq P) atTop (𝓝 d) := by
  obtain ⟨m,hm,Q,hQ⟩ := h
  obtain ⟨A,hA⟩ := cnt_close hQ
  obtain ⟨B,hB⟩ := mod_error m hm Q
  refine ⟨freq (fun j => Q (j%m)) m, tendsto_freq_error (C := A+B) fun n => ?_⟩
  exact (abs_sub_le _ _ _).trans (add_le_add (hA n) (hB n))


def Short (K n : ℕ) := ∃ k < K, ∃ r < n, collatz^[k] r = n

lemma full_affine (k r : ℕ) : ∃ a > 0, ∀ h, collatz^[k] (r + 2^k*h) = collatz^[k] r + a*h := by
  induction k with
  | zero => exact ⟨1, by decide, by simp⟩
  | succ k ih =>
    obtain ⟨a,ha,hA⟩ := ih
    let v := collatz^[k] r
    have lift (h : ℕ) : collatz^[k+1] (r+2^(k+1)*h) = collatz (v+a*(2*h)) := by
      rw [pow_succ, mul_assoc, iterate_succ_apply', hA]
    rw [iterate_succ_apply']
    change ∃ a > 0, ∀ h, _ = collatz v + a*h
    by_cases hv : v%2=0
    · refine ⟨a, ha, fun h => ?_⟩
      rw [lift, show a*(2*h) = 2*(a*h) by ring]
      simp [collatz, Nat.add_mod, hv, Nat.add_mul_div_left]
    · refine ⟨6*a, by positivity, fun h => ?_⟩
      rw [lift, show a*(2*h) = 2*(a*h) by ring]
      simp [collatz, Nat.add_mod, hv]
      ring

lemma prog_reg (r b v a : ℕ) (ha : 0 < a) :
    Reg (fun n => ∃ h, n = v + a*h ∧ r + b*h < n) := by
  let ok := b < a ∨ (b = a ∧ r < v)
  refine ⟨a,ha,fun j => j = v%a ∧ ok, ?_⟩
  filter_upwards [eventually_ge_atTop (v + a*(r+v+1))] with n hn
  have stable (h : ℕ) (hh : r+v < h) : r+b*h < v+a*h ↔ ok := by
    dsimp [ok]
    rcases lt_trichotomy b a with hb|hb|hb
    · have := Nat.mul_le_mul_right h (show b+1 ≤ a by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    · subst b; omega
    · have := Nat.mul_le_mul_right h (show a+1 ≤ b by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
  constructor
  · rintro ⟨h,rfl,hh⟩
    have hle : r+v+1 ≤ h := (Nat.le_of_mul_le_mul_left (by omega : a*(r+v+1) ≤ a*h) ha)
    exact ⟨by simp [Nat.add_mod], (stable h (by omega)).1 hh⟩
  · rintro ⟨hmod,hok⟩
    have dv := Nat.mod_add_div n a
    have dv' := Nat.mod_add_div v a
    have hvn : v ≤ n := by omega
    have hvq := Nat.div_le_div_right (c := a) hvn
    let h := n/a - v/a
    have eqn : n = v+a*h := by
      dsimp [h]
      rw [Nat.mul_sub]
      have := Nat.mul_le_mul_left a hvq
      omega
    have hl : r+v+1 ≤ h := Nat.le_of_mul_le_mul_left (by omega : a*(r+v+1) ≤ a*h) ha
    exact ⟨h,eqn,eqn ▸ (stable h (by omega)).2 hok⟩

-- On each starting residue the endpoint and start are affine in the quotient.
lemma short_reg (K : ℕ) : Reg (Short K) := by
  apply reg_ex
  intro k hk
  let P := fun i n : ℕ => ∃ h, collatz^[k] (i+2^k*h) = n ∧ i+2^k*h < n
  apply reg_congr _ (reg_ex P (2^k) ?_)
  · apply Eventually.of_forall
    intro n
    constructor
    · rintro ⟨r,hr,he⟩
      refine ⟨r%2^k,Nat.mod_lt _ (by positivity),r/2^k,?_⟩
      simpa only [Nat.mod_add_div] using And.intro he hr
    · rintro ⟨i,hi,h,he,hr⟩
      exact ⟨_,hr,he⟩
  · intro i hi
    obtain ⟨a,ha,hA⟩ := full_affine k i
    apply reg_congr _ (prog_reg i (2^k) (collatz^[k] i) a ha)
    exact Eventually.of_forall fun n => by simp [P,hA,eq_comm]


def T (n : ℕ) := if n%2=0 then n/2 else (3*n+1)/2
def w (n : ℕ) : ℕ := if n%2=0 then 1 else 3
def amp : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k+1, r => amp k r * w (T^[k] r)

lemma T_shift (x z : ℕ) : T (x+2*z) = T x + w x*z := by
  unfold T w
  split_ifs <;> omega

lemma amp_data (k r : ℕ) : amp k r % 2 = 1 ∧ ∀ h,
    amp k (r+2^k*h) = amp k r ∧ T^[k] (r+2^k*h) = T^[k] r + amp k r*h := by
  induction k generalizing r with
  | zero => simp [amp]
  | succ k ih =>
    obtain ⟨ho,hi⟩ := ih r
    constructor
    · simp [amp,w]; split <;> omega
    · intro h
      rw [pow_succ, mul_assoc]
      obtain ⟨h1,h2⟩ := hi (2*h)
      rw [show amp k r * (2*h) = 2*(amp k r*h) by ring] at h2
      constructor
      · simp [amp,h1,h2,w,Nat.add_mod]
      · rw [iterate_succ_apply',iterate_succ_apply' T k r,h2,T_shift,amp]
        ring

-- The two lifts have opposite next parities and share the preceding multiplier.
lemma amp_pair (k r : ℕ) :
    Real.sqrt (amp (k+1) r) + Real.sqrt (amp (k+1) (r+2^k)) =
      (1+Real.sqrt 3) * Real.sqrt (amp k r) := by
  obtain ⟨ho,hi⟩ := amp_data k r
  obtain ⟨h1,h2⟩ := hi 1
  simp only [mul_one] at h1 h2
  simp only [amp, h1, h2, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  unfold w
  have hh := Nat.mod_lt (T^[k] r) (by decide : 0 < 2)
  rw [Nat.add_mod,ho]
  split_ifs <;> norm_num at * <;> first | omega | ring

lemma moment (k : ℕ) : ∑ r ∈ range (2^k), Real.sqrt (amp k r) = (1+Real.sqrt 3)^k := by
  induction k with
  | zero => simp [amp]
  | succ k ih =>
    rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
    simp_rw [add_comm (2^k), amp_pair, ← mul_sum, ih, pow_succ]
    ring

def Bad (K r : ℕ) := ∀ i ≤ K, r ≤ 4*collatz^[i] r

lemma shortcut_full (k r : ℕ) : ∃ i ≤ 2*k, T^[k] r = collatz^[i] r := by
  induction k with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ k ih =>
    obtain ⟨i,hi,he⟩ := ih
    rw [iterate_succ_apply',he]
    let v := collatz^[i] r
    by_cases hv : v%2=0
    · exact ⟨i+1,by omega,by rw [iterate_succ_apply']; change T v = collatz v; simp [T,collatz,hv]⟩
    · refine ⟨i+2,by omega,?_⟩
      rw [iterate_succ_apply',iterate_succ_apply']
      change T v = collatz (collatz v)
      have hv' : (3*v+1)%2=0 := by omega
      simp [T,collatz,hv,hv']

def Heavy (k r : ℕ) := 2^k ≤ 4*amp k r

lemma bad_heavy (k : ℕ) : ∀ᶠ n in atTop, Bad (2*k) n → Heavy k (n%2^k) := by
  let m := 2^k
  let L := ∑ r ∈ range m, T^[k] r
  filter_upwards [eventually_ge_atTop (m*(4*L+1))] with n hn hb
  let r := n%m
  let h := n/m
  have hr : r < m := Nat.mod_lt _ (by positivity : 0 < 2^k)
  have hq : 4*L+1 ≤ h := (Nat.le_div_iff_mul_le (by positivity : 0 < 2^k)).2 (by simpa [mul_comm] using hn)
  have hl : T^[k] r ≤ L := single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 hr)
  have he : r+m*h = n := Nat.mod_add_div _ _
  obtain ⟨i,hi,hi'⟩ := shortcut_full k n
  have hb' := hb i hi
  rw [← hi', ← he, ((amp_data k r).2 h).2] at hb'
  by_contra! hf
  change ¬ m ≤ 4*amp k r at hf
  have hprod := Nat.mul_le_mul_right h (show 4*amp k r+1 ≤ m by omega)
  nlinarith

lemma heavy_frac (k : ℕ) :
    freq (fun j => Heavy k (j%2^k)) (2^k) ≤
      2 * ((1+Real.sqrt 3)/(2*Real.sqrt 2))^k := by
  classical
  let m := 2^k
  let P := fun j => Heavy k (j%m)
  have hsum : (cnt P m : ℝ) * Real.sqrt (m:ℝ) ≤ 2 * (1+Real.sqrt 3)^k := by
    rw [← moment, Finset.mul_sum]
    change (Nat.count P m : ℝ) * _ ≤ _
    rw [Nat.count_eq_card_filter_range]
    calc
      _ = ∑ j ∈ (range m).filter P, Real.sqrt (m:ℝ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ (range m).filter P, 2 * Real.sqrt (amp k j) := by
        apply sum_le_sum
        intro j hj
        obtain ⟨hj,hp⟩ := mem_filter.1 hj
        change 2^k ≤ 4*amp k (j%m) at hp
        rw [Nat.mod_eq_of_lt (mem_range.1 hj)] at hp
        have h' : (m:ℝ) ≤ 4*(amp k j:ℝ) := by exact_mod_cast hp
        have hh := Real.sqrt_le_sqrt h'
        rw [Real.sqrt_mul (by norm_num)] at hh
        norm_num at hh
        exact hh
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  have hm : (0:ℝ) < m := by dsimp [m]; positivity
  change (cnt P m : ℝ) / m ≤ _
  rw [div_pow,mul_pow]
  have hs : Real.sqrt (m:ℝ) = (Real.sqrt 2)^k := by
    clear hsum hm P
    dsimp [m]; push_cast
    clear m
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [hs] at hsum
  have hm' : (m:ℝ) = 2^k := by simp [m]
  rw [hm', div_le_iff₀ (by positivity), mul_right_comm]
  field_simp at * <;> nlinarith


lemma freq_mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (n : ℕ) : freq P n ≤ freq Q n := by
  classical
  unfold freq
  gcongr
  exact Nat.count_mono_left (fun j _ => h j)

lemma bad_small (ε : ℝ) (hε : 0 < ε) : ∃ K, ∀ᶠ n in atTop, freq (Bad K) n < ε := by
  let q := (1+Real.sqrt 3)/(2*Real.sqrt 2)
  have hq : q < 1 := by
    apply (div_lt_one (by positivity)).2
    have a := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have b := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have ha : Real.sqrt 3 < 7/4 := by rw [Real.sqrt_lt' (by positivity)]; norm_num
    have hb : 11/8 < Real.sqrt 2 := by rw [Real.lt_sqrt (by positivity)]; norm_num
    linarith
  have hz := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ q by dsimp [q]; positivity) hq
  obtain ⟨k,hk⟩ := (hz.eventually_lt_const (show 0 < ε/4 by positivity)).exists
  let Q := fun j => Heavy k (j%2^k)
  obtain ⟨C,hC⟩ := cnt_close (P := Bad (2*k)) (Q := fun n => Bad (2*k) n ∧ Q n)
    ((bad_heavy k).mono fun _ hi => ⟨fun h => ⟨h,hi h⟩,And.left⟩)
  have hlim := mod_limit (2^k) (by positivity) (Heavy k)
  have hμ : freq Q (2^k) < ε/2 := (heavy_frac k).trans_lt (by change 2*q^k < ε/2; linarith)
  refine ⟨2*k,?_⟩
  filter_upwards [hlim.eventually_lt_const hμ,
    (tendsto_const_div_atTop_nhds_zero_nat (C:=C)).eventually_lt_const (show 0 < ε/2 by positivity),
    eventually_gt_atTop 0] with n hn hn' hn0
  have hle := freq_mono (P:=fun j => Bad (2*k) j ∧ Q j) (Q:=Q) (fun _ => And.right) n
  have hnn : (0:ℝ) < n := by exact_mod_cast hn0
  have hx := (abs_le.1 (hC n)).2
  have hh : freq (Bad (2*k)) n ≤ freq (fun j => Bad (2*k) j ∧ Q j) n + C/n := by
    unfold freq
    rw [← add_div, div_le_div_iff_of_pos_right hnn]
    linarith
  change freq Q n < _ at hn
  linarith


noncomputable def ret (r : ℕ) := sInf {t : ℕ | 0 < t ∧ collatz^[t] r ≤ r}

-- Before the first return to or below r, every shortest witness has all its
-- interior points at least n. A good endpoint is within B steps of that return.
lemma cover {B K n : ℕ} (hi : ¬ IsPure n) (hs : ¬ Short (K+1) n) (hb : ¬ Bad B n) :
    ∃ r < n, Bad K r ∧ ∃ j ≤ B, collatz^[ret r - j] r = n := by
  classical
  have hex : ∃ k, ∃ r < n, collatz^[k] r = n := by
    unfold IsPure at hi
    push Not at hi
    obtain ⟨r,hr,k,he⟩ := hi
    exact ⟨k,r,hr,he⟩
  let k := Nat.find hex
  obtain ⟨r,hr,he⟩ := Nat.find_spec hex
  change collatz^[k] r = n at he
  have hmin (j : ℕ) (hj : j < k) : ¬ ∃ a < n, collatz^[j] a = n := Nat.find_min hex hj
  have hk : K < k := by
    by_contra! h
    exact hs ⟨k,by omega,r,hr,he⟩
  have inner (i : ℕ) (hi : 0 < i) (hik : i ≤ k) : n ≤ collatz^[i] r := by
    by_contra! hh
    apply hmin (k-i) (by omega)
    refine ⟨_,hh,?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel hik, he]
  have hn4 : n ≤ 4*r := by
    have h1 := inner 1 (by decide) (by omega)
    simpa only [iterate_one] using h1.trans (show collatz r ≤ 4*r by unfold collatz; split <;> omega)
  have hbad : Bad K r := by
    intro i hi
    by_cases h : i=0
    · subst i; simp; omega
    · have := inner i (by omega) (by omega)
      omega
  unfold Bad at hb
  push Not at hb
  obtain ⟨i,hi,hd⟩ := hb
  have hreturn : 0 < i+k ∧ collatz^[i+k] r ≤ r := by
    rw [iterate_add_apply,he]
    omega
  let S := {t : ℕ | 0 < t ∧ collatz^[t] r ≤ r}
  have hne : S.Nonempty := ⟨_,hreturn⟩
  have hret : ret r ∈ S := Nat.sInf_mem hne
  have hu : ret r ≤ i+k := Nat.sInf_le (s:=S) hreturn
  obtain ⟨hp,hl⟩ := hret
  have hkret : k ≤ ret r := by
    by_contra! hh
    have := inner _ hp (by omega)
    omega
  exact ⟨r,hr,hbad,ret r-k,by omega,by simpa only [show ret r - (ret r-k) = k by omega] using he⟩

lemma count_cover (B K N : ℕ) : cnt (fun n => ¬ IsPure n) N ≤ cnt (Short (K+1)) N +
    cnt (Bad B) N + (B+1)*cnt (Bad K) N := by
  classical
  let A := (range N).filter (Short (K+1))
  let D := (range N).filter (Bad B)
  let E := (range N).filter (Bad K)
  let F := (E ×ˢ range (B+1)).image (fun p => collatz^[ret p.1-p.2] p.1)
  have sub : (range N).filter (fun n => ¬ IsPure n) ⊆ A ∪ D ∪ F := by
    intro n hn
    obtain ⟨hn,hi⟩ := mem_filter.1 hn
    by_cases ha : Short (K+1) n
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hn,ha⟩))
    by_cases hd : Bad B n
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hn,hd⟩))
    obtain ⟨r,hr,hb,j,hj,he⟩ := cover hi ha hd
    exact mem_union_right _ (mem_image.2 ⟨(r,j),mem_product.2
      ⟨mem_filter.2 ⟨mem_range.2 (hr.trans (mem_range.1 hn)),hb⟩,mem_range.2 (by omega)⟩,he⟩)
  simp only [cnt,Nat.count_eq_card_filter_range]
  change _ ≤ A.card + D.card + (B+1)*E.card
  have hF : F.card ≤ E.card*(B+1) := by
    apply card_image_le.trans
    simp
  have hh := card_le_card sub
  have hu := card_union_le (A ∪ D) F
  have hud := card_union_le A D
  rw [mul_comm (B+1)]
  convert hh.trans (hu.trans (add_le_add hud hF)) using 1
  all_goals congr!

lemma freq_cover (B K N : ℕ) : freq (fun n => ¬ IsPure n) N ≤ freq (Short (K+1)) N +
    freq (Bad B) N + (B+1:ℝ)*freq (Bad K) N := by
  simp only [freq,← mul_div_assoc,← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast count_cover B K N


lemma impure_limit : ∃ d, Tendsto (freq (fun n => ¬ IsPure n)) atTop (𝓝 d) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨B,hB⟩ := bad_small (ε/8) (by positivity)
  obtain ⟨K,hK⟩ := bad_small (ε/(8*(B+1:ℝ))) (by positivity)
  obtain ⟨d,hd⟩ := reg_limit (short_reg (K+1))
  have near : ∀ᶠ n in atTop, |freq (fun j => ¬ IsPure j) n - d| < ε/2 := by
    filter_upwards [hB,hK, (Metric.tendsto_nhds.1 hd) (ε/8) (by positivity)] with n hb hk hn
    have h1 := freq_cover B K n
    have h2 := freq_mono (P:=Short (K+1)) (Q:=fun j => ¬ IsPure j) (fun j h hj => by
      obtain ⟨k,_,r,hr,he⟩ := h
      exact hj ⟨r,hr,k,he⟩) n
    rw [lt_div_iff₀ (by positivity)] at hk
    rw [Real.dist_eq, abs_lt] at hn
    rw [abs_lt]
    constructor <;> nlinarith
  obtain ⟨N,hN⟩ := eventually_atTop.1 near
  exact ⟨N, fun m hm n hn => by
    rw [Real.dist_eq,abs_lt]
    obtain ⟨a,b⟩ := abs_lt.1 (hN m hm)
    obtain ⟨c,e⟩ := abs_lt.1 (hN n hn)
    constructor <;> linarith⟩

lemma three_pure {n : ℕ} (hn : n%3=0) : IsPure n := by
  rintro ⟨r,hr,k,he⟩
  suffices ∀ (i r : ℕ), (collatz^[i] r)%3=0 → collatz^[i] r ≤ r by
    have hh := this k r (by simpa [he] using hn)
    omega
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro r h
    rw [iterate_succ_apply'] at *
    unfold collatz at h ⊢
    split at h <;> rename_i hh
    · rw [if_pos hh]
      change collatz^[i] r % 2 = 0 at hh
      change (collatz^[i] r / 2) % 3 = 0 at h
      have eqx : collatz^[i] r = 2*(collatz^[i] r / 2) := by omega
      have hx : collatz^[i] r % 3 = 0 := by
        calc
          _ = (2*(collatz^[i] r / 2))%3 := congrArg (· % 3) eqx
          _ = 0 := by rw [Nat.mul_mod,h]
      exact (Nat.div_le_self _ _).trans (ih r hx)
    · omega

lemma enumeration : ∃ C : ℝ, Tendsto (fun n : ℕ => (Nat.nth IsPure n : ℝ) / n) atTop (𝓝 C) := by
  classical
  obtain ⟨d,hd⟩ := impure_limit
  have hc (n : ℕ) : cnt IsPure n + cnt (fun j => ¬ IsPure j) n = n := by
    induction n with
    | zero => simp [cnt]
    | succ n ih =>
      simp only [cnt,Nat.count_succ] at *
      split_ifs <;> omega
  have hp : Tendsto (freq IsPure) atTop (𝓝 (1-d)) := by
    apply (tendsto_const_nhds.sub hd).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Pi.sub_apply,freq]
    have h0 : (n:ℝ) ≠ 0 := by positivity
    field_simp
    have hc' : (cnt IsPure n:ℝ) + cnt (fun j => ¬ IsPure j) n = n := by exact_mod_cast hc n
    linarith
  let Q := fun j : ℕ => j % 3 = 0
  have h3 := mod_limit 3 (by decide) (fun j => j=0)
  have h3v : freq Q 3 = 1/3 := by
    change (cnt Q 3 : ℝ) / 3 = 1/3
    have c : cnt Q 3 = 1 := by norm_num [cnt,Q,Nat.count_succ, show (3:ℕ) = 2+1 by decide, show (2:ℕ) = 1+1 by decide,Nat.count_one]
    rw [c]; norm_num
  have hpos : (0:ℝ) < 1-d := by
    have h := le_of_tendsto_of_tendsto' h3 hp (freq_mono (P:=Q) (Q:=IsPure) fun _ => three_pure)
    change freq Q 3 ≤ 1-d at h
    rw [h3v] at h
    linarith
  have hinf : (Set.ofPred IsPure).Infinite := Set.infinite_of_forall_exists_gt (fun a =>
    ⟨3*(a+1),three_pure (by omega),by omega⟩)
  have hnth := (Nat.nth_strictMono hinf).tendsto_atTop
  refine ⟨(1-d)⁻¹,?_⟩
  have h := (hp.comp hnth).inv₀ hpos.ne'
  apply h.congr
  intro n
  simp only [comp_apply,freq,cnt,Nat.count_nth_of_infinite hinf,inv_div]

end PureProof


theorem OMA.solution : type_of% @OMA.S_oeis_a061641.main := by
  exact PureProof.enumeration
