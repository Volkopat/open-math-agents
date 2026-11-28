import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1_H2_R1
import Mathlib
/- Adapted from OpenAI, openai/math 3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. -/
namespace OAI
namespace LargePrimeGaps
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)
noncomputable def qi4 (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter fun m =>
    (∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h) ∧
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q
theorem qmG {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, w i * u i) ^ 2 ≤
      (∑ i ∈ s with 0 < u i, w i) * (∑ i ∈ s, w i * u i ^ 2) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    split_ifs
    · exact hw i hi
    · exact le_rfl
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    by_cases hui : 0 < u i
    · simp only [if_pos hui]
      nlinarith [sq_nonneg (w i * u i)]
    · have huzero : u i = 0 := le_antisymm (le_of_not_gt hui) (hu i hi)
      simp [huzero]
theorem qkA {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hvone : ∀ i ∈ s, 0 < v i → 1 ≤ v i) :
    (∑ i ∈ s with 0 < u i, w i) ≤
      (∑ i ∈ s with 0 < u i ∧ v i = 0, w i) + ∑ i ∈ s, w i * v i := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hui : 0 < u i
  · by_cases hvi : v i = 0
    · simp [hui, hvi]
    · simp only [hui, hvi, and_false, ite_false, ite_true, zero_add]
      exact le_mul_of_one_le_right (hw i hi) (hvone i hi (lt_of_le_of_ne (hv i hi) (Ne.symm hvi)))
  · simp only [hui, false_and, ite_false, zero_add]
    exact mul_nonneg (hw i hi) (hv i hi)
theorem qm2 {ι : Type*} [DecidableEq ι] (s t : Finset ι) (w : ι → ℝ)
    (ht : t ⊆ s) :
    (∑ i ∈ t, w i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ s, w i ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) w
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  refine hc.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => sq_nonneg _)
theorem qlR {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w u v : ι → ℝ) (X a K b M : ℝ)
    (hX : 0 < X) (ha : 0 < a) (hK : 0 < K) (hM : 0 < M)
    (hb : b < a ^ 2 / K)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hvone : ∀ i ∈ s, 0 < v i → 1 ≤ v i)
    (hfirst : a * X ≤ ∑ i ∈ s, w i * u i)
    (hdetect : (∑ i ∈ s, w i * u i ^ 2) ≤ K * X)
    (hsuppress : (∑ i ∈ s, w i * v i) ≤ b * X)
    (hsecond : (∑ i ∈ s, w i ^ 2) ≤ M * X) :
    (a ^ 2 / K - b) ^ 2 / M * X ≤
      ((s.filter fun i => 0 < u i ∧ v i = 0).card : ℝ) := by
  classical
  let A := s.filter fun i => 0 < u i
  let T := s.filter fun i => 0 < u i ∧ v i = 0
  have hAnonneg : 0 ≤ ∑ i ∈ A, w i :=
    Finset.sum_nonneg fun i hi => hw i (Finset.mem_filter.mp hi).1
  have hAsq := qmG s w u hw hu
  have hfirstsq := mul_self_le_mul_self (le_of_lt (mul_pos ha hX)) hfirst
  have hAsq' : (a ^ 2 * X) * X ≤ ((∑ i ∈ A, w i) * K) * X := by
    calc
      _ = (a * X) * (a * X) := by ring
      _ ≤ (∑ i ∈ s, w i * u i) * (∑ i ∈ s, w i * u i) := hfirstsq
      _ = (∑ i ∈ s, w i * u i) ^ 2 := by ring
      _ ≤ (∑ i ∈ A, w i) * (∑ i ∈ s, w i * u i ^ 2) := hAsq
      _ ≤ (∑ i ∈ A, w i) * (K * X) := mul_le_mul_of_nonneg_left hdetect hAnonneg
      _ = _ := by ring
  have hAlower : a ^ 2 / K * X ≤ ∑ i ∈ A, w i := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    exact (mul_le_mul_iff_left₀ hX).mp (by nlinarith only [hAsq'])
  have hremoved := qkA s w u v hw hv hvone
  have hTlower : (a ^ 2 / K - b) * X ≤ ∑ i ∈ T, w i := by
    dsimp [A] at hAlower
    dsimp [T]
    linarith
  have hTnonneg : 0 ≤ (a ^ 2 / K - b) * X := mul_nonneg (sub_nonneg.mpr hb.le) hX.le
  have hTfirstsq := mul_self_le_mul_self hTnonneg hTlower
  have hTsq := qm2 s T w (Finset.filter_subset _ s)
  have hTcardnonneg : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hTbound : (a ^ 2 / K - b) ^ 2 * X * X ≤ (T.card : ℝ) * M * X := by
    calc
      _ = ((a ^ 2 / K - b) * X) * ((a ^ 2 / K - b) * X) := by ring
      _ ≤ (∑ i ∈ T, w i) * (∑ i ∈ T, w i) := hTfirstsq
      _ = (∑ i ∈ T, w i) ^ 2 := by ring
      _ ≤ (T.card : ℝ) * (∑ i ∈ s, w i ^ 2) := hTsq
      _ ≤ (T.card : ℝ) * (M * X) := mul_le_mul_of_nonneg_left hsecond hTcardnonneg
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  exact (mul_le_mul_iff_left₀ hX).mp hTbound
noncomputable def theta (n : ℕ) : ℝ := if Nat.Prime n then Real.log n else 0
noncomputable def qj (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc X (2 * X), f m) / (X : ℝ)
noncomputable def q8 (X : ℕ) (B : Finset ℕ) (m : ℕ) : ℝ :=
  (∑ b ∈ B, theta (m + b)) / Real.log (X : ℝ)
noncomputable def qb (lam : ℝ) (X : ℕ) : ℕ :=
  ⌊lam * Real.log (X : ℝ)⌋₊
theorem qw {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))
theorem qc8 (n : ℕ) : 0 ≤ theta n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, if_pos hn]
    exact (qw hn.two_le).le
  · simp [theta, hn]
theorem qmT (n : ℕ) : 0 < theta n ↔ Nat.Prime n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, hn, iff_true]
    exact qw hn.two_le
  · simp [theta, hn]
theorem qgP {X : ℕ} (hX : 2 ≤ X) (B : Finset ℕ) (m : ℕ) :
    0 ≤ q8 X B m :=
  div_nonneg (Finset.sum_nonneg fun _ _ => qc8 _) (qw hX).le
theorem qgd {X : ℕ} (hX : 2 ≤ X) (B : Finset ℕ) (m : ℕ) :
    0 < q8 X B m ↔ ∃ b ∈ B, Nat.Prime (m + b) := by
  rw [q8, div_pos_iff_of_pos_right (qw hX),
    Finset.sum_pos_iff_of_nonneg (fun _ _ => qc8 _)]
  simp only [qmT]
theorem qmH {X m : ℕ} (hX : 2 ≤ X) (hm : X < m)
    (B : Finset ℕ) (hv : 0 < q8 X B m) : 1 ≤ q8 X B m := by
  obtain ⟨b, hb, hp⟩ := (qgd hX B m).mp hv
  have hlog : Real.log (X : ℝ) ≤ theta (m + b) := by
    rw [theta, if_pos hp]
    apply Real.log_le_log (by exact_mod_cast (show 0 < X by omega))
    exact_mod_cast (show X ≤ m + b by omega)
  have hsum := Finset.single_le_sum (fun q (_ : q ∈ B) => qc8 (m + q)) hb
  rw [q8, le_div_iff₀ (qw hX), one_mul]
  exact hlog.trans hsum
theorem qkB {X : ℕ} (hX : 2 ≤ X) (h m : ℕ) :
    0 < q8 X (Finset.Ioc 0 h) m ↔
      ∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h := by
  rw [qgd hX]
  constructor
  · rintro ⟨b, hb, hp⟩
    obtain ⟨hb0, hbh⟩ := Finset.mem_Ioc.mp hb
    exact ⟨m + b, hp, by omega, by omega⟩
  · rintro ⟨p, hp, hmp, hph⟩
    refine ⟨p - m, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · simpa [Nat.add_sub_of_le hmp.le] using hp
theorem qjz {X : ℕ} (hX : 2 ≤ X) (h m : ℕ) :
    q8 X (Finset.Ioc h (2 * h)) m = 0 ↔
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q := by
  have hnonneg := qgP hX (Finset.Ioc h (2 * h)) m
  have heq : q8 X (Finset.Ioc h (2 * h)) m = 0 ↔
      ¬ 0 < q8 X (Finset.Ioc h (2 * h)) m := by
    constructor <;> intro nh <;> linarith
  rw [heq, qgd hX]
  constructor
  · intro hnone q hqlo hqhi hp
    apply hnone
    refine ⟨q - m, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · simpa [Nat.add_sub_of_le (show m ≤ q by omega)] using hp
  · intro hnone
    rintro ⟨b, hb, hp⟩
    obtain ⟨hblo, hbhi⟩ := Finset.mem_Ioc.mp hb
    exact hnone (m + b) (by omega) (by omega) hp
theorem qhp {X : ℕ} (hX : 2 ≤ X) (h : ℕ) :
    qi4 X h = (Finset.Ioc X (2 * X)).filter fun m =>
      0 < q8 X (Finset.Ioc 0 h) m ∧ q8 X (Finset.Ioc h (2 * h)) m = 0 := by
  classical
  ext m
  simp only [qi4, Finset.mem_filter, qkB hX,
    qjz hX]
theorem qib {X h : ℕ} (hX : 2 ≤ X) (w : ℕ → ℝ)
    (a K b M : ℝ) (ha : 0 < a) (hK : 0 < K) (hM : 0 < M) (hb : b < a ^ 2 / K)
    (hw : ∀ m ∈ Finset.Ioc X (2 * X), 0 ≤ w m)
    (hfirst : a ≤ qj X (fun m => w m * q8 X (Finset.Ioc 0 h) m))
    (hdetect : qj X (fun m => w m * q8 X (Finset.Ioc 0 h) m ^ 2) ≤ K)
    (hsuppress : qj X (fun m => w m * q8 X (Finset.Ioc h (2 * h)) m) ≤ b)
    (hsecond : qj X (fun m => w m ^ 2) ≤ M) :
    (a ^ 2 / K - b) ^ 2 / M * (X : ℝ) ≤ ((qi4 X h).card : ℝ) := by
  classical
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [qhp hX]
  apply qlR _ w _ _ (X : ℝ) a K b M hXpos ha hK hM hb hw
  · intro m _
    exact qgP hX _ m
  · intro m _
    exact qgP hX _ m
  · intro m hm hv
    exact qmH hX (Finset.mem_Ioc.mp hm).1 _ hv
  · exact (le_div_iff₀ hXpos).mp hfirst
  · exact (div_le_iff₀ hXpos).mp hdetect
  · exact (div_le_iff₀ hXpos).mp hsuppress
  · exact (div_le_iff₀ hXpos).mp hsecond
open Filter
theorem qcx {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (qb lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (qw hX).le)
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
noncomputable def q1 {ι : Type*} (X : ℕ) (d : ι → ℕ) : ι → ℝ :=
  fun i => Real.log (d i : ℝ) / Real.log (X : ℝ)
noncomputable def qg {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) : ℝ :=
  (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) * F (q1 X d)
noncomputable def qd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (m : ℕ) (b : ι → ℕ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => (m + b i).divisors), qg X F d
def qV {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) (rho : ℝ) : Prop :=
  ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → rho < ∑ i, v i → F v = 0
theorem qas {ι : Type*} [Fintype ι]
    {X : ℕ} {F : (ι → ℝ) → ℝ} {d : ι → ℕ} :
    qg X F d ≠ 0 ↔
      (∀ i, Squarefree (d i)) ∧ F (q1 X d) ≠ 0 := by
  simp only [qg, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_true_left, Int.cast_ne_zero,
    ArithmeticFunction.moebius_ne_zero_iff_squarefree]
theorem qbB {ι : Type*} {X : ℕ} (hX : 2 ≤ X)
    {d : ι → ℕ} (hd : ∀ i, 0 < d i) (i : ι) : 0 ≤ q1 X d i := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd i)) (qw hX).le
theorem qdP {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : qV F rho) {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hF : F (q1 X d) ≠ 0) :
    ((∏ i, d i : ℕ) : ℝ) ≤ Real.exp (rho * Real.log (X : ℝ)) := by
  have hsum : ∑ i, q1 X d i ≤ rho := by
    by_contra! hgt
    exact hF (hbudget _ (qbB hX hd) hgt)
  have hlog : ∑ i, Real.log (d i : ℝ) ≤ rho * Real.log (X : ℝ) := by
    apply (div_le_iff₀ (qw hX)).mp
    simpa only [q1, Finset.sum_div] using hsum
  calc
    ((∏ i, d i : ℕ) : ℝ) = Real.exp (∑ i, Real.log (d i : ℝ)) := by
      rw [Real.exp_sum, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (Real.exp_log (by exact_mod_cast hd i)).symm
    _ ≤ Real.exp (rho * Real.log (X : ℝ)) := Real.exp_le_exp.mpr hlog
theorem qeV {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : qV F rho) {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hF : F (q1 X d) ≠ 0) (i : ι) :
    d i ≤ ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  have hprod : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  have hle : d i ≤ ∏ i, d i := Nat.le_of_dvd hprod (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    ((by exact_mod_cast hle : (d i : ℝ) ≤ ((∏ i, d i : ℕ) : ℝ)).trans
      (qdP hX hbudget hd hF))
theorem qeD {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) :
    |qg X F d| ≤ |F (q1 X d)| := by
  rw [qg, abs_mul, Finset.abs_prod]
  have hp : (∏ i, |(ArithmeticFunction.moebius (d i) : ℝ)|) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact abs_nonneg _
    · intro i _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d i))
  simpa using mul_le_mul_of_nonneg_right hp (abs_nonneg (F (q1 X d)))
theorem qk1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : qV F rho) (m : ℕ) (hm : 0 < m) (b : ι → ℕ) :
    qd X F m b =
      ∑ d ∈ (Fintype.piFinset (fun _ : ι =>
        Finset.Icc 1 ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊)).filter
          (fun d => ∀ i, d i ∣ m + b i), qg X F d := by
  classical
  unfold qd
  symm
  apply Finset.sum_subset
  · intro d hd
    have hdbox := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1
    have hddiv := (Finset.mem_filter.mp hd).2
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Nat.mem_divisors.mpr ⟨hddiv i, by omega⟩
  · intro d hd hdnot
    by_contra hne
    have hdpos : ∀ i, 0 < d i := by
      intro i
      have hdmem := Fintype.mem_piFinset.mp hd i
      exact Nat.pos_of_mem_divisors hdmem
    have hF := (qas.mp hne).2
    apply hdnot
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), fun i => ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hdpos i, qeV hX hbudget hdpos hF i⟩
    · exact (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hd i)).1
def qQ (X q c : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun m => m % q = c
theorem qeW (X : ℕ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    |((qQ X q c).card : ℝ) - (X : ℝ) / (q : ℝ)| ≤ 2 := by
  have hupper : (qQ X q c).card ≤
      (Finset.Icc (X / q) ((2 * X) / q)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m / q)
    · intro m hm
      obtain ⟨hmrange, hmc⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hmrange
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hmlo.le, Nat.div_le_div_right hmhi⟩
    · intro m hm n hn heq
      have hmc := (Finset.mem_filter.mp hm).2
      have hnc := (Finset.mem_filter.mp hn).2
      have hmdiv := Nat.div_add_mod m q
      have hndiv := Nat.div_add_mod n q
      change m / q = n / q at heq
      rw [heq, hmc] at hmdiv
      rw [hnc] at hndiv
      omega
  have hlower : (Finset.Ioo (X / q) ((2 * X) / q)).card ≤
      (qQ X q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q * k + c)
    · intro k hk
      obtain ⟨hklo, hkhi⟩ := Finset.mem_Ioo.mp hk
      have hrX := Nat.mod_lt X hq
      have hr2X := Nat.mod_lt (2 * X) hq
      have hXdiv := Nat.div_add_mod X q
      have h2Xdiv := Nat.div_add_mod (2 * X) q
      change q * k + c ∈ qQ X q c
      simp only [qQ, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hh := Nat.mul_le_mul_left q (show X / q + 1 ≤ k by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      · have hh := Nat.mul_le_mul_left q (show k + 1 ≤ (2 * X) / q by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  rw [Nat.card_Icc] at hupper
  rw [Nat.card_Ioo] at hlower
  have hord : X / q ≤ (2 * X) / q := Nat.div_le_div_right (by omega)
  have hu : (qQ X q c).card + X / q ≤ (2 * X) / q + 1 := by omega
  have hl : (2 * X) / q ≤ (qQ X q c).card + X / q + 1 := by omega
  have hrX := Nat.mod_lt X hq
  have hr2X := Nat.mod_lt (2 * X) hq
  have hXdiv := Nat.div_add_mod X q
  have h2Xdiv := Nat.div_add_mod (2 * X) q
  have hupperN : (qQ X q c).card * q ≤ X + 2 * q := by
    have hh := Nat.mul_le_mul_left q hu
    rw [Nat.mul_comm]
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hlowerN : X ≤ (qQ X q c).card * q + 2 * q := by
    have hh := Nat.mul_le_mul_left q hl
    rw [Nat.mul_comm]
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hupperR : ((qQ X q c).card : ℝ) * q ≤ (X : ℝ) + 2 * q := by
    exact_mod_cast hupperN
  have hlowerR : (X : ℝ) ≤ ((qQ X q c).card : ℝ) * q + 2 * q := by
    exact_mod_cast hlowerN
  have hu' : ((qQ X q c).card : ℝ) ≤ (X : ℝ) / q + 2 := by
    have hh := (le_div_iff₀ hqR).mpr hupperR
    simpa [add_div, hqR.ne'] using hh
  have hl' : (X : ℝ) / q ≤ ((qQ X q c).card : ℝ) + 2 := by
    apply (div_le_iff₀ hqR).mpr
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩
def qm {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ := Finset.univ.lcm d
theorem qbE {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) : 0 < qm d := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun i _ => (hd i).ne'
theorem qdQ {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    qm d ∣ ∏ i, d i :=
  Finset.lcm_dvd fun _ hi => Finset.dvd_prod_of_mem d hi
theorem qlq {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) : qm d ≤ ∏ i, d i :=
  Nat.le_of_dvd (Finset.prod_pos fun i _ => hd i) (qdQ d)
theorem qmU {ι : Type*} (s : Finset ι) (d : ι → ℕ) (m c : ℕ) :
    Nat.ModEq (s.lcm d) m c ↔ ∀ i ∈ s, Nat.ModEq (d i) m c := by
  classical
  constructor
  · intro h i hi
    exact h.of_dvd (Finset.dvd_lcm hi)
  · induction s using Finset.induction_on with
    | empty => intro _; exact Nat.modEq_one
    | @insert a s ha ih =>
      intro h
      rw [Finset.lcm_insert]
      exact Nat.mod_lcm (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem qbN {ι : Type*} [Fintype ι]
    (d b : ι → ℕ) {c : ℕ} (hc : ∀ i, d i ∣ c + b i) (m : ℕ) :
    (∀ i, d i ∣ m + b i) ↔ Nat.ModEq (qm d) m c := by
  rw [qm, qmU]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro hm i
    apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl (b i))
    exact (Nat.modEq_zero_iff_dvd.mpr (hm i)).trans (Nat.modEq_zero_iff_dvd.mpr (hc i)).symm
  · intro hm i
    exact ((hm i |>.add_right (b i)).dvd_iff (dvd_refl (d i))).mpr (hc i)
def qa4 {ι : Type*} [Fintype ι] (d b : ι → ℕ) : Prop :=
  ∃ c < qm d, ∀ i, d i ∣ c + b i
theorem qfR {ι : Type*} [Fintype ι] {d b : ι → ℕ}
    (hd : ∀ i, 0 < d i) {m : ℕ} (hm : ∀ i, d i ∣ m + b i) : qa4 d b := by
  refine ⟨m % qm d, Nat.mod_lt _ (qbE hd), ?_⟩
  apply (qbN d b hm _).mpr
  simp [Nat.ModEq]
def qdy {ι : Type*} [Fintype ι] (d b : ι → ℕ) : Prop :=
  ∀ p, Nat.Prime p → p ∣ qm d →
    ∀ i j, p ∣ d i → p ∣ d j → Nat.ModEq p (b i) (b j)
theorem qcQ {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (h : qa4 d b) : qdy d b := by
  obtain ⟨c, _, hc⟩ := h
  intro p _ _ i j hpi hpj
  apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl c)
  exact (Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hc i))).trans
    (Nat.modEq_zero_iff_dvd.mpr (hpj.trans (hc j))).symm
theorem qd7 {n k : ℕ} (hn : Squarefree n)
    (h : ∀ p, Nat.Prime p → p ∣ n → p ∣ k) : n ∣ k := by
  by_cases hk : k = 0
  · simp [hk]
  rw [← Nat.prod_primeFactors_of_squarefree hn, Nat.prod_primeFactors_dvd_iff hk]
  intro p hp
  obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hpp, h p hpp hpn, hk⟩
theorem qcR {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (hd : ∀ i, Squarefree (d i)) (h : qdy d b) :
    qa4 d b := by
  classical
  have hdpos : ∀ i, 0 < d i := fun i => Nat.pos_of_ne_zero (hd i).ne_zero
  let P := {p : ℕ // p ∈ (qm d).primeFactors}
  have hp : ∀ p : P, Nat.Prime p.val := fun p => Nat.prime_of_mem_primeFactors p.property
  have hit : ∀ p : P, ∃ i, p.val ∣ d i := by
    intro p
    have hpq := (Nat.mem_primeFactors.mp p.property).2.1
    obtain ⟨i, _, hi⟩ := ((hp p).prime.dvd_finsetProd_iff d).mp
      (hpq.trans (qdQ d))
    exact ⟨i, hi⟩
  choose idx hidx using hit
  let a : P → ℕ := fun p => (p.val - b (idx p) % p.val) % p.val
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset a (fun p : P => p.val) Finset.univ
    (fun p _ => (hp p).ne_zero) (by
      intro p _ q _ hpq
      exact (Nat.coprime_primes (hp p) (hp q)).mpr fun heq => hpq (Subtype.ext heq))
  apply qfR hdpos (m := c)
  intro i
  apply qd7 (hd i)
  intro p hpp hpi
  have hpq : p ∣ qm d := hpi.trans (Finset.dvd_lcm (Finset.mem_univ i))
  let p' : P := ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hpq, (qbE hdpos).ne'⟩⟩
  have hshift : Nat.ModEq p (b (idx p')) (b i) := h p hpp hpq (idx p') i (hidx p') hpi
  have hres : Nat.ModEq p c (a p') := hc p' (Finset.mem_univ _)
  have hb : b (idx p') % p < p := Nat.mod_lt _ hpp.pos
  have hzero : Nat.ModEq p (a p' + b (idx p')) 0 := by
    change (((p - b (idx p') % p) % p + b (idx p')) % p) = 0 % p
    rw [Nat.zero_mod, Nat.add_mod, Nat.mod_mod]
    calc
      ((p - b (idx p') % p) % p + b (idx p') % p) % p =
          ((p - b (idx p') % p) + b (idx p') % p) % p := by
            rw [Nat.add_mod (p - b (idx p') % p) (b (idx p') % p) p,
              Nat.mod_eq_of_lt hb]
      _ = 0 := by rw [Nat.sub_add_cancel hb.le, Nat.mod_self]
  exact Nat.modEq_zero_iff_dvd.mp ((hres.add hshift.symm).trans hzero)
theorem qcH {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (hd : ∀ i, Squarefree (d i)) :
    qa4 d b ↔ qdy d b :=
  ⟨qcQ, qcR hd⟩
noncomputable def qbl {ι : Type*} [Fintype ι] (X : ℕ) (d b : ι → ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun m => ∀ i, d i ∣ m + b i
theorem qdR {ι : Type*} [Fintype ι] (X : ℕ)
    (d b : ι → ℕ) {c : ℕ} (hc : c < qm d) (hsol : ∀ i, d i ∣ c + b i) :
    qbl X d b = qQ X (qm d) c := by
  classical
  ext m
  simp only [qbl, qQ, Finset.mem_filter]
  rw [qbN d b hsol, Nat.ModEq, Nat.mod_eq_of_lt hc]
theorem qcB {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) (h : ¬ qa4 d b) :
    qbl X d b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  exact h (qfR hd (Finset.mem_filter.mp hm).2)
theorem qkC {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) (h : qa4 d b) :
    |((qbl X d b).card : ℝ) - (X : ℝ) / (qm d : ℝ)| ≤ 2 := by
  obtain ⟨c, hc, hsol⟩ := h
  rw [qdR X d b hc hsol]
  exact qeW X (qbE hd) hc
theorem qdr {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : Squarefree (qm d) := by
  have hq : 0 < qm d := qbE fun i => Nat.pos_of_ne_zero (hd i).ne_zero
  apply Squarefree.squarefree_of_dvd (y := primorial (qm d))
  · apply Finset.lcm_dvd
    intro i _
    apply qd7 (hd i)
    intro p hp hpi
    apply hp.dvd_primorial_iff.mpr
    exact Nat.le_of_dvd hq (hpi.trans (Finset.dvd_lcm (Finset.mem_univ i)))
  · exact squarefree_primorial _
theorem qhq {m c a q : ℕ} (hq : 0 < q)
    (hmc : Nat.ModEq q m c) (hcop : ¬ Nat.Coprime (c + a) q) (hlt : q < m + a) :
    ¬ Nat.Prime (m + a) := by
  intro hp
  have hnq : Nat.Coprime (m + a) q := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hq hlt)
  apply hcop
  rw [Nat.coprime_iff_gcd_eq_one, ← (hmc.add_right a).gcd_eq]
  exact hnq.gcd_eq_one
noncomputable def qbs {ι : Type*} [Fintype ι] (d b : ι → ℕ) : ℝ := by
  classical
  exact if qa4 d b then (qm d : ℝ)⁻¹ else 0
theorem qi5 {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) :
    |((qbl X d b).card : ℝ) - (X : ℝ) * qbs d b| ≤ 2 := by
  classical
  by_cases h : qa4 d b
  · simpa [qbs, h, div_eq_mul_inv] using qkC X hd h
  · simp [qbs, h, qcB X hd h]
theorem qiE {ι : Type*} [Fintype ι]
    (X : ℕ) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ) :
    (∑ m ∈ Finset.Ioc X (2 * X), ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) =
      ∑ d ∈ s, A d * ((qbl X d b).card : ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp only [qbl, Finset.sum_const, nsmul_eq_mul, mul_comm]
theorem qjA {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 0 < X) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ)
    (b : ι → ℕ) (hs : ∀ d ∈ s, ∀ i, 0 < d i) :
    |qj X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) -
        ∑ d ∈ s, A d * qbs d b| ≤
      2 / (X : ℝ) * ∑ d ∈ s, |A d| := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp : qj X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) -
      ∑ d ∈ s, A d * qbs d b =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * (((qbl X d b).card : ℝ) -
        (X : ℝ) * qbs d b) := by
    unfold qj
    rw [qiE]
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    field_simp [hXR.ne']
  rw [hexp, abs_mul, abs_of_pos (inv_pos.mpr hXR)]
  have he : |∑ d ∈ s, A d * (((qbl X d b).card : ℝ) -
        (X : ℝ) * qbs d b)| ≤ 2 * ∑ d ∈ s, |A d| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [abs_mul, mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (qi5 X (hs d hd)) (abs_nonneg _)
  calc
    _ ≤ (X : ℝ)⁻¹ * (2 * ∑ d ∈ s, |A d|) := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXR.le)
    _ = _ := by ring
def qau (n Y : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)).filter fun d => ∏ i, d i ≤ Y
theorem qge (n Y : ℕ) :
    ((qau (n + 1) Y).card : ℝ) ≤
      (Y : ℝ) * (harmonic Y : ℝ) ^ n := by
  classical
  let B := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)
  let A : (Fin n → ℕ) → Finset (Fin (n + 1) → ℕ) :=
    fun e => (Finset.Icc 1 (Y / ∏ i, e i)).image fun v => Fin.cons v e
  have hsubset : qau (n + 1) Y ⊆ B.biUnion A := by
    intro d hd
    obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp hd
    have hemem : Fin.tail d ∈ B := Fintype.mem_piFinset.mpr
      fun i => (Fintype.mem_piFinset.mp hbox) i.succ
    have hdpos : ∀ i, 0 < d i := fun i => (Finset.mem_Icc.mp
      (Fintype.mem_piFinset.mp hbox i)).1
    have hepos : 0 < ∏ i : Fin n, Fin.tail d i := Finset.prod_pos fun i _ => hdpos i.succ
    refine Finset.mem_biUnion.mpr ⟨Fin.tail d, hemem, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨d 0, Finset.mem_Icc.mpr ⟨hdpos 0, ?_⟩, Fin.cons_self_tail d⟩
    apply (Nat.le_div_iff_mul_le hepos).mpr
    simpa only [Fin.prod_univ_succ, Fin.tail] using hprod
  have hcard : (qau (n + 1) Y).card ≤
      ∑ e ∈ B, Y / ∏ i, e i := by
    calc
      _ ≤ (B.biUnion A).card := Finset.card_le_card hsubset
      _ ≤ ∑ e ∈ B, (A e).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ B, (Finset.Icc 1 (Y / ∏ i, e i)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = _ := by simp only [Nat.card_Icc, Nat.add_sub_cancel]
  calc
    ((qau (n + 1) Y).card : ℝ) ≤
        ∑ e ∈ B, ((Y / ∏ i, e i : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ e ∈ B, (Y : ℝ) / ((∏ i, e i : ℕ) : ℝ) :=
      Finset.sum_le_sum fun _ _ => Nat.cast_div_le
    _ = (Y : ℝ) * ∑ e ∈ B, ∏ i, (e i : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib, Finset.mul_sum]
    _ = (Y : ℝ) * (harmonic Y : ℝ) ^ n := by
      congr 1
      dsimp only [B]
      rw [Finset.sum_prod_piFinset _ (fun (_ : Fin n) (a : ℕ) => (a : ℝ)⁻¹)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
theorem qeX (n Y : ℕ) :
    ((qau (n + 1) Y).card : ℝ) ≤
      (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n := by
  apply (qge n Y).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Y)
  apply pow_le_pow_left₀ (by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  exact harmonic_le_one_add_log Y
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
theorem qdJ {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : qV F rho)
    (m : ℕ) (hm : 0 < m) (b : Fin n → ℕ) :
    qd X F m b =
      ∑ d ∈ qau n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if ∀ i, d i ∣ m + b i then qg X F d else 0 := by
  classical
  rw [qk1 hX hbudget m hm b, ← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    exact ⟨(Finset.mem_filter.mp hd.1).1, hd.2⟩
  · intro d hd hdnot
    by_contra hne
    simp only [Finset.mem_filter] at hd
    obtain ⟨hbox, hdiv⟩ := hd
    have hdpos : ∀ i, 0 < d i := fun i =>
      (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hbox i)).1
    have hF := (qas.mp hne).2
    have hp : ∏ i, d i ≤ ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr (qdP hX hbudget hdpos hF)
    exact hdnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbox, hp⟩, hdiv⟩)
noncomputable def qbF {n : ℕ} (X : ℕ) (F : (Fin n → ℝ) → ℝ)
    (rho : ℝ) (b : Fin n → ℕ) : ℝ :=
  ∑ d ∈ qau n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
    qg X F d * qbs d b
theorem qi6 {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin (n + 1) → ℝ) → ℝ} {rho M : ℝ} (hbudget : qV F rho)
    (hM : 0 ≤ M) (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M)
    (b : Fin (n + 1) → ℕ) :
    |qj X (fun m => qd X F m b) - qbF X F rho b| ≤
      2 * M / (X : ℝ) * ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ *
       (1 + Real.log (⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ : ℝ)) ^ n := by
  classical
  let Y : ℕ := ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊
  let s := qau (n + 1) Y
  have hs : ∀ d ∈ s, ∀ i, 0 < d i := by
    intro d hd i
    exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i)).1
  have heq : qj X (fun m => qd X F m b) =
      qj X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then qg X F d else 0) := by
    unfold qj
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    exact qdJ hX hbudget m
      (lt_trans (by omega : 0 < X) (Finset.mem_Ioc.mp hm).1) b
  rw [heq]
  have he := qjA (by omega : 0 < X) s (qg X F) b hs
  have he' : |qj X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then qg X F d else 0) -
      qbF X F rho b| ≤ 2 / (X : ℝ) * ∑ d ∈ s, |qg X F d| := by
    convert he using 1
    congr 2
    unfold qj
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  apply he'.trans
  have habs : ∑ d ∈ s, |qg X F d| ≤ (s.card : ℝ) * M := by
    calc
      _ ≤ ∑ _d ∈ s, M := Finset.sum_le_sum fun d hd =>
        (qeD X F d).trans (hbound _ (qbB hX (hs d hd)))
      _ = _ := by simp
  have hcard := qeX n Y
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  calc
    2 / (X : ℝ) * ∑ d ∈ s, |qg X F d| ≤
        2 / (X : ℝ) * ((s.card : ℝ) * M) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ 2 / (X : ℝ) * (((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hM) (by positivity)
    _ = _ := by ring
theorem qeM {n X : ℕ} (hX : 2 ≤ X)
    (hlog : 1 ≤ Real.log (X : ℝ)) {F : (Fin (n + 1) → ℝ) → ℝ} {rho M : ℝ}
    (hrho : 0 ≤ rho) (hbudget : qV F rho) (hM : 0 ≤ M)
    (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M) (b : Fin (n + 1) → ℕ) :
    |qj X (fun m => qd X F m b) - qbF X F rho b| ≤
      (2 * M * (1 + rho) ^ n) * (Real.log (X : ℝ)) ^ n *
        Real.exp (-(1 - rho) * Real.log (X : ℝ)) := by
  let L := Real.log (X : ℝ)
  let Y : ℕ := ⌊Real.exp (rho * L)⌋₊
  have hL : 0 ≤ L := le_trans (by norm_num) hlog
  have hY : 1 ≤ Y := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa using Real.one_le_exp_iff.mpr (mul_nonneg hrho hL))
  have hYR : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hfloor : (Y : ℝ) ≤ Real.exp (rho * L) := Nat.floor_le (Real.exp_pos _).le
  have hlogY : Real.log (Y : ℝ) ≤ rho * L := by
    simpa only [Real.log_exp] using Real.log_le_log hYR hfloor
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hlogbound : 1 + Real.log (Y : ℝ) ≤ (1 + rho) * L := by nlinarith
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply (qi6 hX hbudget hM hbound b).trans
  calc
    2 * M / (X : ℝ) * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n ≤
        2 * M / (X : ℝ) * Real.exp (rho * L) * ((1 + rho) * L) ^ n := by
      gcongr
    _ = (2 * M * (1 + rho) ^ n) * L ^ n * Real.exp (-(1 - rho) * L) := by
      rw [show -(1 - rho) * L = rho * L - L by ring, Real.exp_sub, Real.exp_log hXR]
      rw [mul_pow]
      ring
def qcy (n Y q : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)).filter
    fun d => (∀ i, Squarefree (d i)) ∧ qm d = q
theorem qic {q : ℕ} (hq : Squarefree q) :
    q.divisors.card = 2 ^ q.primeFactors.card := by
  rw [Nat.card_divisors hq.ne_zero]
  calc
    _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have h := Nat.mem_primeFactors.mp hp
      rw [Nat.factorization_eq_one_of_squarefree hq h.1 h.2.1]
    _ = _ := by simp
theorem qgQ (n Y q : ℕ) (hq : 0 < q) :
    (qcy n Y q).card ≤ (q.divisors.card) ^ n := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin n => q.divisors)).card := by
      apply Finset.card_le_card
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Nat.mem_divisors.mpr
      exact ⟨hd'.2 ▸ Finset.dvd_lcm (Finset.mem_univ i), hq.ne'⟩
    _ = _ := by simp
theorem qfD (n Y q : ℕ) (hq : Squarefree q) :
    (qcy n Y q).card ≤ (2 ^ n) ^ q.primeFactors.card := by
  have h := qgQ n Y q (Nat.pos_of_ne_zero hq.ne_zero)
  rw [qic hq, ← pow_mul, Nat.mul_comm, pow_mul] at h
  exact h
def qbh {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : Prop :=
  ∃ c < qm d, (∀ i, d i ∣ c + b i) ∧ Nat.Coprime (c + a) (qm d)
noncomputable def qae {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : ℝ := by
  classical
  exact if qbh d b a then ((qm d).totient : ℝ)⁻¹ else 0
noncomputable def qan (X H q : ℕ) : NNReal :=
  ((Finset.range (H + 1)) ×ˢ (Finset.range q)).sup fun ac =>
    if Nat.Coprime (ac.2 + ac.1) q then
      NNReal.mk (|(∑ m ∈ qQ X q ac.2, theta (m + ac.1)) - (X : ℝ) / q.totient|)
        (abs_nonneg _) else 0
theorem qlS {X H q a c : ℕ} (ha : a ≤ H) (hc : c < q)
    (hcop : Nat.Coprime (c + a) q) :
    |(∑ m ∈ qQ X q c, theta (m + a)) - (X : ℝ) / q.totient| ≤
      (qan X H q : ℝ) := by
  have hm : (a, c) ∈ (Finset.range (H + 1)) ×ˢ (Finset.range q) := by simp; omega
  have h := Finset.le_sup (f := fun ac : ℕ × ℕ =>
    if Nat.Coprime (ac.2 + ac.1) q then
      NNReal.mk (|(∑ m ∈ qQ X q ac.2, theta (m + ac.1)) -
        (X : ℝ) / q.totient|) (abs_nonneg _) else 0) hm
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [Prod.fst, Prod.snd, if_pos hcop, NNReal.coe_mk, qan] using hr
theorem qc4 {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a c : ℕ} (hc : c < qm d)
    (hsol : ∀ i, d i ∣ c + b i) :
    qbh d b a ↔ Nat.Coprime (c + a) (qm d) := by
  constructor
  · rintro ⟨c', hc', hsol', hcop'⟩
    have hmod := (qbN d b hsol c').mp hsol'
    change c' % qm d = c % qm d at hmod
    rw [Nat.mod_eq_of_lt hc', Nat.mod_eq_of_lt hc] at hmod
    simpa [hmod] using hcop'
  · intro hcop
    exact ⟨c, hc, hsol, hcop⟩
theorem qeE {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a : ℕ} (h : qbh d b a) : qa4 d b := by
  obtain ⟨c, hc, hs, _⟩ := h
  exact ⟨c, hc, hs⟩
theorem qi7 {ι : Type*} [Fintype ι]
    {X H a : ℕ} {d b : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hmod : qm d ≤ X) (ha : a ≤ H) :
    |(∑ m ∈ qbl X d b, theta (m + a)) - (X : ℝ) * qae d b a| ≤
      (qan X H (qm d) : ℝ) := by
  classical
  by_cases h : qa4 d b
  · obtain ⟨c, hc, hsol⟩ := h
    by_cases hcop : Nat.Coprime (c + a) (qm d)
    · rw [qdR X d b hc hsol, qae,
        if_pos ((qc4 hc hsol).mpr hcop)]
      simpa only [div_eq_mul_inv] using qlS (X := X) ha hc hcop
    · have hr : ¬ qbh d b a :=
        fun hr => hcop ((qc4 hc hsol).mp hr)
      have hz : ∑ m ∈ qbl X d b, theta (m + a) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        obtain ⟨hmX, hmdiv⟩ := Finset.mem_filter.mp hm
        have hmX' := (Finset.mem_Ioc.mp hmX).1
        have hn := qhq (qbE hd)
          ((qbN d b hsol m).mp hmdiv) hcop (by omega)
        simp [theta, hn]
      simp only [hz, qae, if_neg hr, mul_zero, sub_zero, abs_zero]
      exact NNReal.coe_nonneg _
  · rw [qcB X hd h]
    have hr : ¬ qbh d b a := fun hr => h (qeE hr)
    simp only [Finset.sum_empty, qae, if_neg hr, mul_zero, sub_zero, abs_zero]
    exact NNReal.coe_nonneg _
def qgr {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : Prop :=
  qdy d b ∧ ∀ p, Nat.Prime p → p ∣ qm d →
    ∀ i, p ∣ d i → ¬ Nat.ModEq p (b i) a
theorem qdl {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a : ℕ} (hd : ∀ i, Squarefree (d i)) :
    qbh d b a ↔ qgr d b a := by
  constructor
  · intro h
    refine ⟨qcQ (qeE h), ?_⟩
    obtain ⟨c, _, hsol, hcop⟩ := h
    intro p hp hpq i hpi hba
    have hcb : Nat.ModEq p (c + b i) 0 := Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hsol i))
    have hca : p ∣ c + a := Nat.modEq_zero_iff_dvd.mp ((hba.add_left c).symm.trans hcb)
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hca hpq) hcop
  · rintro ⟨hlocal, hexcl⟩
    obtain ⟨c, hc, hsol⟩ := qcR hd hlocal
    refine ⟨c, hc, hsol, ?_⟩
    by_contra hcop
    obtain ⟨p, hp, hpca, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨i, _, hpi⟩ := (hp.prime.dvd_finsetProd_iff d).mp
      (hpq.trans (qdQ d))
    apply hexcl p hp hpq i hpi
    have hcb : Nat.ModEq p (c + b i) 0 := Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hsol i))
    have hca : Nat.ModEq p (c + a) 0 := Nat.modEq_zero_iff_dvd.mpr hpca
    exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl c) (hcb.trans hca.symm)
theorem qiF {ι : Type*} [Fintype ι]
    (X a : ℕ) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ) :
    (∑ m ∈ Finset.Ioc X (2 * X),
      (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) =
      ∑ d ∈ s, A d * ∑ m ∈ qbl X d b, theta (m + a) := by
  classical
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl
theorem qgE {ι : Type*} [Fintype ι]
    {X H a : ℕ} (hX : 0 < X) (ha : a ≤ H)
    (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ)
    (hs : ∀ d ∈ s, (∀ i, 0 < d i) ∧ qm d ≤ X) :
    |qj X (fun m =>
        (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) -
      ∑ d ∈ s, A d * qae d b a| ≤
      (X : ℝ)⁻¹ * ∑ d ∈ s, |A d| * (qan X H (qm d) : ℝ) := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp : qj X (fun m =>
      (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) -
        ∑ d ∈ s, A d * qae d b a =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * ((∑ m ∈ qbl X d b, theta (m + a)) -
        (X : ℝ) * qae d b a) := by
    unfold qj
    rw [qiF]
    let T : (ι → ℕ) → ℝ := fun d => ∑ m ∈ qbl X d b, theta (m + a)
    change (∑ d ∈ s, A d * T d) / X - (∑ d ∈ s, A d * qae d b a) =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * (T d - (X : ℝ) * qae d b a)
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    field_simp [hXR.ne']
  rw [hexp, abs_mul, abs_of_pos (inv_pos.mpr hXR)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hXR.le)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (qi7 (hs d hd).1 (hs d hd).2 ha)
    (abs_nonneg _)
theorem qfE (n Y : ℕ) (s : Finset (Fin n → ℕ))
    (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (hbox : ∀ d ∈ s, ∀ i, d i ∈ Finset.Icc 1 Y)
    (hsq : ∀ d ∈ s, ∀ i, Squarefree (d i))
    (hmod : ∀ d ∈ s, qm d ≤ Y) :
    (∑ d ∈ s, E (qm d)) ≤
      ∑ q ∈ Finset.Icc 1 Y, if Squarefree q then
        (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) * E q else 0 := by
  classical
  have hmap : ∀ d ∈ s, qm d ∈ Finset.Icc 1 Y := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨qbE
      (fun i => (Finset.mem_Icc.mp (hbox d hd i)).1), hmod d hd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro q _hqY
  let T := s.filter fun d => qm d = q
  have hT : T ⊆ qcy n Y q := by
    intro d hd
    obtain ⟨hds, hdq⟩ := Finset.mem_filter.mp hd
    simp only [qcy, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨hbox d hds, hsq d hds, hdq⟩
  have heq : (∑ d ∈ T, E (qm d)) = (T.card : ℝ) * E q := by
    calc
      _ = ∑ _d ∈ T, E q := Finset.sum_congr rfl fun d hd => by
        rw [(Finset.mem_filter.mp hd).2]
      _ = _ := by simp
  change (∑ d ∈ T, E (qm d)) ≤ _
  rw [heq]
  by_cases hq : Squarefree q
  · rw [if_pos hq]
    have hcard := (Finset.card_le_card hT).trans (qfD n Y q hq)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hE q)
  · rw [if_neg hq]
    have hT0 : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hds, hdq⟩ := Finset.mem_filter.mp hd
      exact hq (hdq ▸ qdr (hsq d hds))
    simp [hT0]
def qds (n Y : ℕ) : Finset (Fin n → ℕ) :=
  (qau n Y).filter fun d => ∀ i, Squarefree (d i)
theorem qef {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : qV F rho)
    (m : ℕ) (hm : 0 < m) (b : Fin n → ℕ) :
    qd X F m b =
      ∑ d ∈ qds n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if ∀ i, d i ∣ m + b i then qg X F d else 0 := by
  classical
  rw [qdJ hX hbudget m hm b]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hz : qg X F d = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hd, (qas.mp hne).1⟩)
  simp only [hz, ite_self]
noncomputable def qb2 {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ) (b : Fin n → ℕ) (a : ℕ) : ℝ :=
  ∑ d ∈ qds n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
    qg X F d * qae d b a
theorem ql8 {X : ℕ} (hX : 2 ≤ X) {rho : ℝ} (hrho1 : rho ≤ 1) :
    ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ ≤ X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply Nat.floor_le_of_le
  calc
    Real.exp (rho * Real.log (X : ℝ)) ≤ Real.exp (Real.log (X : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [qw hX]
    _ = _ := Real.exp_log hXR
theorem qj6 {n X H a : ℕ} (hX : 2 ≤ X) (ha : a ≤ H)
    {F : (Fin n → ℝ) → ℝ} {rho M : ℝ} (hrho1 : rho ≤ 1)
    (hbudget : qV F rho) (hM : 0 ≤ M)
    (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M) (b : Fin n → ℕ) :
    |qj X (fun m => qd X F m b * theta (m + a)) -
      qb2 X F rho b a| ≤
      M / (X : ℝ) * ∑ q ∈ Finset.Icc 1 ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if Squarefree q then (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) *
          (qan X H q : ℝ) else 0 := by
  classical
  let Y : ℕ := ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊
  let s := qds n Y
  have hbox : ∀ d ∈ s, ∀ i, d i ∈ Finset.Icc 1 Y := by
    intro d hd i
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1 i
  have hpos : ∀ d ∈ s, ∀ i, 0 < d i := fun d hd i => (Finset.mem_Icc.mp (hbox d hd i)).1
  have hsq : ∀ d ∈ s, ∀ i, Squarefree (d i) := fun d hd => (Finset.mem_filter.mp hd).2
  have hmod : ∀ d ∈ s, qm d ≤ Y := by
    intro d hd
    exact (qlq (hpos d hd)).trans (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
  have hs : ∀ d ∈ s, (∀ i, 0 < d i) ∧ qm d ≤ X :=
    fun d hd => ⟨hpos d hd, (hmod d hd).trans (ql8 hX hrho1)⟩
  have he := qgE (by omega : 0 < X) ha s (qg X F) b hs
  have hexp : qj X (fun m => qd X F m b * theta (m + a)) =
      qj X (fun m => (∑ d ∈ s, if ∀ i, d i ∣ m + b i then
        qg X F d else 0) * theta (m + a)) := by
    unfold qj
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    dsimp only
    rw [qef hX hbudget m (by
      have := (Finset.mem_Ioc.mp hm).1
      omega) b]
  rw [hexp]
  have he' : |qj X (fun m => (∑ d ∈ s, if ∀ i, d i ∣ m + b i then
        qg X F d else 0) * theta (m + a)) - qb2 X F rho b a| ≤
      (X : ℝ)⁻¹ * ∑ d ∈ s, |qg X F d| *
        (qan X H (qm d) : ℝ) := by
    convert he using 1
    congr 2
    unfold qj
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  apply he'.trans
  have hcoeff : ∑ d ∈ s, |qg X F d| *
      (qan X H (qm d) : ℝ) ≤
      M * ∑ d ∈ s, (qan X H (qm d) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact mul_le_mul_of_nonneg_right
      ((qeD X F d).trans (hbound _ (qbB hX (hpos d hd))))
      (NNReal.coe_nonneg _)
  have hgroup := qfE n Y s
    (fun q => (qan X H q : ℝ)) (fun q => NNReal.coe_nonneg _) hbox hsq hmod
  calc
    (X : ℝ)⁻¹ * ∑ d ∈ s, |qg X F d| *
        (qan X H (qm d) : ℝ) ≤
      (X : ℝ)⁻¹ * (M * ∑ d ∈ s, (qan X H (qm d) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ ≤ (X : ℝ)⁻¹ * (M * ∑ q ∈ Finset.Icc 1 Y, if Squarefree q then
        (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) * (qan X H q : ℝ) else 0) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgroup hM) (by positivity)
    _ = _ := by ring
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
def qdx {j : ℕ} (t : Fin j → ℝ) : ℝ := ∑ i, t i
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def qcI (lambda : ℝ) (j : ℕ) : ℝ := lambda^j / j.factorial
noncomputable def qad {j : ℕ} (f : (Fin (j+1) → ℝ) → ℝ)
    (t : Fin j → ℝ) : ℝ := ∫ u : ℝ, f (Fin.snoc t u)
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def q7 {j : ℕ} (f : (Fin j → ℝ) → ℝ) : ℝ := ∫ t, f t^2
noncomputable def qcp (lambda : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), qcI lambda j * q7 (f j)
noncomputable def qmm (lambda : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : ℝ :=
  lambda * ∑ j ∈ Finset.range (k+1), qcI lambda j *
    q7 (fun t => f j t + qad (f (j+1)) t)
@[simp] theorem qnf (j : ℕ) : q7 (0 : (Fin j → ℝ) → ℝ) = 0 := by
  simp [q7]
@[simp] theorem qm6 (j : ℕ) :
    qad (0 : (Fin (j+1) → ℝ) → ℝ) = 0 := by
  funext t
  simp [qad]
def qat {j : ℕ} (f : (Fin j → ℝ) → ℝ) : Prop :=
  ∀ (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f (t ∘ e) = f t
def qe (j : ℕ) (tau : ℝ) : Set (Fin j → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ qdx t < tau}
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
theorem qeY {j : ℕ} {f : (Fin (j+1) → ℝ) → ℝ}
    (hf : Function.support f ⊆ {t | ∀ i, 0 < t i}) (t : Fin j → ℝ) :
    qad f t = ∫ u in Ici (0:ℝ), f (Fin.snoc t u) := by
  unfold qad
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Ici (0:ℝ)
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    by_contra hn
    apply hu
    change 0 ≤ u
    simpa only [Fin.snoc_last] using (hf hn (Fin.last j)).le
def qL (tau : ℝ) (k : ℕ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : Prop :=
  0 < k ∧
  (∀ j, j ≤ k → ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j) ⊆ qe j tau ∧ qat (f j)) ∧
  (∀ j, k < j → f j = 0)
def qap (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n
theorem qj7 (k : ℕ) : qap k 1 = 1 := by
  exact (ArithmeticFunction.isMultiplicative_zeta.pow).1
theorem qeZ (k n : ℕ) :
    qap (k+1) n = ∑ d ∈ n.divisors, qap k d := by
  simp only [qap, pow_succ, ArithmeticFunction.mul_zeta_apply]
theorem qi8 (k : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    qap k p = k := by
  induction k with
  | zero => simp [qap, hp.ne_one]
  | succ k ih =>
    rw [qeZ, hp.divisors]
    simp [hp.ne_one.symm, qj7, ih, Nat.add_comm]
theorem qgR (k : ℕ) {q : ℕ} (hq : Squarefree q) :
    qap k q = k ^ q.primeFactors.card := by
  rw [qap, ← ArithmeticFunction.IsMultiplicative.prod_primeFactors
    (ArithmeticFunction.isMultiplicative_zeta.pow) hq]
  calc
    _ = ∏ p ∈ q.primeFactors, k := Finset.prod_congr rfl fun p hp =>
      qi8 k (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp
theorem qi9 (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]
theorem qeN (k Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (qap k q : ℝ) / (q : ℝ)) ≤
      (harmonic Q : ℝ) ^ k := by
  induction k with
  | zero =>
    by_cases hQ : Q = 0
    · subst Q; simp
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      simp [qap, ArithmeticFunction.one_apply, ite_div, hQ1]
  | succ k ih =>
    have h := qi9 (fun n => (qap k n : ℝ))
      (fun n => Nat.cast_nonneg _) Q
    simp only [qeZ, Nat.cast_sum] at ⊢
    apply h.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right ih (by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
theorem qcS (T Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (T : ℝ)^q.primeFactors.card / q else 0) ≤
      (harmonic Q : ℝ)^T := by
  classical
  apply (Finset.sum_le_sum (g := fun q => (qap T q : ℝ)/(q:ℝ)) ?_).trans
    (qeN T Q)
  intro q _
  split_ifs with hq
  · rw [qgR T hq, Nat.cast_pow]
  · positivity
theorem qjB {q : ℕ} (hq : Squarefree q) :
    q ≤ 2 ^ q.primeFactors.card * q.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hq,
    Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]
  calc
    q = ∏ p ∈ q.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hq).symm
    _ ≤ ∏ p ∈ q.primeFactors, 2 * (p-1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
theorem qid (K Q : ℕ) (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    {X L : ℝ} (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hb : ∀ q ∈ Finset.Icc 1 Q, Squarefree q →
      E q ≤ X/(q:ℝ) * (L + 2^q.primeFactors.card)) :
    (∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (K:ℝ)^q.primeFactors.card * E q else 0)^2 ≤
      (∑ q ∈ Finset.Icc 1 Q, E q) * X *
        (L * (harmonic Q : ℝ)^(K^2) + (harmonic Q : ℝ)^(2*K^2)) := by
  classical
  let s := Finset.Icc 1 Q
  let w : ℕ → ℝ := fun q => if Squarefree q then (K:ℝ)^q.primeFactors.card else 0
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun q => Real.sqrt (E q))
    (fun q => w q * Real.sqrt (E q))
  have heq1 : ∀ q, Real.sqrt (E q) * (w q * Real.sqrt (E q)) = w q * E q := by
    intro q
    calc
      _ = w q * (Real.sqrt (E q))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hE q)]
  simp only [heq1, mul_pow, Real.sq_sqrt (hE _)] at hcs
  have hsecond : (∑ q ∈ s, w q ^ 2 * E q) ≤
      X * (L * (harmonic Q : ℝ)^(K^2) + (harmonic Q : ℝ)^(2*K^2)) := by
    have hterm : ∀ q ∈ s, w q^2 * E q ≤
        X * (L * (if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card / q else 0) +
          (if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card / q else 0)) := by
      intro q hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      by_cases hsq : Squarefree q
      · simp only [w, if_pos hsq]
        calc
          _ ≤ ((K:ℝ)^q.primeFactors.card)^2 * (X/(q:ℝ) * (L+2^q.primeFactors.card)) :=
            mul_le_mul_of_nonneg_left (hb q hq hsq) (sq_nonneg _)
          _ = _ := by
            rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_pow, ← pow_mul, Nat.mul_comm,
              pow_mul]
            ring
      · simp [w, hsq]
    calc
      _ ≤ ∑ q ∈ s, X * (L *
          (if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card / q else 0) +
          (if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card / q else 0)) :=
        Finset.sum_le_sum hterm
      _ = X * (L * (∑ q ∈ s, if Squarefree q then ((K^2:ℕ):ℝ)^q.primeFactors.card/q else 0) +
          ∑ q ∈ s, if Squarefree q then ((2*K^2:ℕ):ℝ)^q.primeFactors.card/q else 0) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (qcS (K^2) Q) hL)
          (qcS (2*K^2) Q)) hX
  have hsumE : 0 ≤ ∑ q ∈ s, E q := Finset.sum_nonneg fun q _ => hE q
  have h := hcs.trans (mul_le_mul_of_nonneg_left hsecond hsumE)
  simp only [w, ite_mul, zero_mul] at h
  simpa only [mul_assoc] using h
theorem qjC {X H q a c : ℕ} (hX : 1 ≤ X) (hq : 0 < q)
    (hqX : q ≤ X) (ha : a ≤ H) (hc : c < q) (hsq : Squarefree q) :
    |(∑ m ∈ qQ X q c, theta (m+a)) - (X:ℝ)/q.totient| ≤
      (X:ℝ)/(q:ℝ) * (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hXq : (1:ℝ) ≤ (X:ℝ)/q := (le_div_iff₀ hqR).mpr (by simpa using (show (q:ℝ) ≤ X by exact_mod_cast hqX))
  have hboundpos : (1:ℝ) ≤ 2*X+H := by exact_mod_cast (show 1 ≤ 2*X+H by omega)
  have hlog : 0 ≤ Real.log (2*X+H) := Real.log_nonneg hboundpos
  have htheta : ∀ m ∈ qQ X q c, theta (m+a) ≤ Real.log (2*X+H) := by
    intro m hm
    have hmhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2
    by_cases hp : Nat.Prime (m+a)
    · rw [theta, if_pos hp]
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show m+a ≤ 2*X+H by omega))
    · simpa [theta, hp]
  have hsum : (∑ m ∈ qQ X q c, theta (m+a)) ≤
      3 * ((X:ℝ)/q) * Real.log (2*X+H) := by
    calc
      _ ≤ ∑ m ∈ qQ X q c, Real.log (2*X+H) := Finset.sum_le_sum htheta
      _ = ((qQ X q c).card:ℝ) * Real.log (2*X+H) := by simp
      _ ≤ ((X:ℝ)/q+2) * Real.log (2*X+H) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have hh := (abs_le.mp (qeW X hq hc)).2
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlog
  have htot : (X:ℝ)/q.totient ≤ (X:ℝ)/q * (2:ℝ)^q.primeFactors.card := by
    have ht : (q:ℝ) ≤ (2:ℝ)^q.primeFactors.card * q.totient := by
      exact_mod_cast qjB hsq
    apply (div_le_iff₀ hphi).mpr
    have hx := mul_le_mul_of_nonneg_left ht (show 0 ≤ (X:ℝ)/q by positivity)
    field_simp at hx ⊢
    nlinarith
  calc
    _ ≤ (∑ m ∈ qQ X q c, theta (m+a)) + (X:ℝ)/q.totient := by
      have hs0 : 0 ≤ ∑ m ∈ qQ X q c, theta (m+a) :=
        Finset.sum_nonneg fun m _ => qc8 (m+a)
      have ht0 : 0 ≤ (X:ℝ)/q.totient := by positivity
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ ≤ 3 * ((X:ℝ)/q) * Real.log (2*X+H) + (X:ℝ)/q * 2^q.primeFactors.card :=
      add_le_add hsum htot
    _ = _ := by ring
theorem qlT {X H q : ℕ} (hX : 1 ≤ X) (hq : 0 < q)
    (hqX : q ≤ X) (hsq : Squarefree q) :
    (qan X H q : ℝ) ≤
      (X:ℝ)/(q:ℝ) * (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
  have hnonneg : 0 ≤ (X:ℝ)/(q:ℝ) *
      (3 * Real.log (2*X+H) + 2^q.primeFactors.card) := by
    have : 0 ≤ Real.log (2*X+H) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H by omega))
    positivity
  change qan X H q ≤ NNReal.mk _ hnonneg
  apply Finset.sup_le
  rintro ⟨a,c⟩ hac
  have ha : a ≤ H := by simpa using (Finset.mem_product.mp hac).1
  have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hac).2
  dsimp only
  split_ifs
  · exact qjC hX hq hqX ha hc hsq
  · exact zero_le
noncomputable def qX (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n
noncomputable def qbM (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  qX f 0 Y q c
theorem qcT (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) (q c : ℕ) :
    qbM f U q c - qbM f L q c = qX f L U q c := by
  classical
  have hunion : Finset.Ioc 0 U = Finset.Ioc 0 L ∪ Finset.Ioc L U := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_union]
    omega
  have hd : Disjoint ((Finset.Ioc 0 L).filter fun n => n % q = c)
      ((Finset.Ioc L U).filter fun n => n % q = c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hl := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    have hu := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    omega
  simp only [qbM, qX, hunion, Finset.filter_union, Finset.sum_union hd]
  ring
theorem qie (f : ℕ → ℝ) (X q a : ℕ) {c : ℕ} (hc : c < q) :
    (∑ m ∈ qQ X q c, f (m+a)) =
      qX f (X+a) (2*X+a) q ((c+a)%q) := by
  classical
  apply Finset.sum_bij (fun m _ => m+a)
  · intro m hm
    obtain ⟨hm,hmc⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlo,hmhi⟩ := Finset.mem_Ioc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hh : Nat.ModEq q m c := by
      change m % q = c % q
      rw [hmc, Nat.mod_eq_of_lt hc]
    exact hh.add_right a
  · intro m _ n _ heq
    omega
  · intro n hn
    obtain ⟨hn,hnc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo,hnhi⟩ := Finset.mem_Ioc.mp hn
    have ha : a ≤ n := by omega
    refine ⟨n-a, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩,
      Nat.sub_add_cancel ha⟩
    have hh : Nat.ModEq q ((n-a)+a) (c+a) := by
      change ((n-a)+a) % q = (c+a) % q
      simpa only [Nat.sub_add_cancel ha] using hnc
    have hhc := Nat.ModEq.add_right_cancel' a hh
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hc] using hhc
  · intro m _
    rfl
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
theorem qgS (n : ℕ) : theta n ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : Nat.Prime n
  · simp [theta, hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [theta, hn]
theorem qja (Y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Y, (ArithmeticFunction.vonMangoldt n - theta n)) =
      Chebyshev.psi Y - Chebyshev.theta Y := by
  simp only [Finset.sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast,
    theta, Finset.sum_filter]
theorem qhH (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (L U q c : ℕ) :
    0 ≤ qX f L U q c := Finset.sum_nonneg fun n _ => hf n
theorem qhr {U : ℕ} (hU : 1 ≤ U) (L q c : ℕ) :
    |qX ArithmeticFunction.vonMangoldt L U q c - qX theta L U q c| ≤
      2 * Real.sqrt U * Real.log U := by
  have hdiff : 0 ≤ qX ArithmeticFunction.vonMangoldt L U q c -
      qX theta L U q c := by
    rw [qX, qX, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun n _ => sub_nonneg.mpr (qgS n)
  rw [abs_of_nonneg hdiff, qX, qX, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 U, (ArithmeticFunction.vonMangoldt n - theta n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnL,hnU⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, hnU⟩
      · intro n _ _
        exact sub_nonneg.mpr (qgS n)
    _ = Chebyshev.psi U - Chebyshev.theta U := qja U
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hU)
theorem qgs {L U bound : ℕ} (hU : U ≤ bound) (hb : 1 ≤ bound)
    (q c : ℕ) : qX theta L U q c ≤ (U-L:ℕ) * Real.log bound := by
  have hlog : 0 ≤ Real.log (bound:ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), Real.log bound := by
      apply Finset.sum_le_sum
      intro n hn
      have hnU := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      by_cases hp : Nat.Prime n
      · rw [theta, if_pos hp]
        exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hnU.trans hU)
      · simpa [theta, hp]
    _ = (((Finset.Ioc L U).filter (fun n => n % q = c)).card:ℝ) * Real.log bound := by simp
    _ ≤ (U-L:ℕ) * Real.log bound := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast (Finset.card_filter_le (Finset.Ioc L U) (fun n => n % q = c)).trans_eq
        (Nat.card_Ioc L U)
theorem qgT {X H a : ℕ} (hX : 1 ≤ X) (ha : a ≤ H) (q c : ℕ) :
    |qX theta (X+a) (2*X+a) q c - qX theta X (2*X) q c| ≤
      2*(H:ℝ) * Real.log (2*X+H) := by
  have hid : qX theta (X+a) (2*X+a) q c - qX theta X (2*X) q c =
      qX theta (2*X) (2*X+a) q c - qX theta X (X+a) q c := by
    rw [← qcT theta (by omega), ← qcT theta (by omega),
      ← qcT theta (by omega), ← qcT theta (by omega)]
    ring
  rw [hid]
  have hA := qgs (L := 2*X) (U := 2*X+a) (bound := 2*X+H)
    (by omega) (by omega) q c
  have hB := qgs (L := X) (U := X+a) (bound := 2*X+H)
    (by omega) (by omega) q c
  simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hA hB
  have hA0 := qhH theta qc8 (2*X) (2*X+a) q c
  have hB0 := qhH theta qc8 X (X+a) q c
  have haR : (a:ℝ) ≤ H := by exact_mod_cast ha
  have hlog : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X+H by omega))
  have hah := mul_le_mul_of_nonneg_right haR hlog
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
noncomputable def qaq (x : ℝ) (q : ℕ) : NNReal :=
  (Finset.range q).sup fun c => if Nat.Coprime c q then
    NNReal.mk (|qbM ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x/q.totient|)
      (abs_nonneg _) else 0
theorem qgt (X : ℕ) {q c : ℕ} (hc : c < q) (hcop : Nat.Coprime c q) :
    |qbM ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient| ≤
      (qaq X q : ℝ) := by
  have h := Finset.le_sup (f := fun c => if Nat.Coprime c q then
    NNReal.mk (|qbM ArithmeticFunction.vonMangoldt ⌊(X:ℝ)⌋₊ q c -
      (X:ℝ)/q.totient|) (abs_nonneg _) else 0) (Finset.mem_range.mpr hc)
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [if_pos hcop, NNReal.coe_mk, Nat.floor_natCast, qaq] using hr
def qN : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊,
        (qaq x q : ℝ)) ≤ M*x*(Real.log x)^(-A)
theorem qej (X : ℕ) {q c : ℕ}
    (hc : c < q) (hcop : Nat.Coprime c q) :
    |qX ArithmeticFunction.vonMangoldt X (2*X) q c - (X:ℝ)/q.totient| ≤
      (qaq (2*X:ℕ) q : ℝ) + (qaq X q : ℝ) := by
  rw [← qcT _ (by omega)]
  have hid : qbM ArithmeticFunction.vonMangoldt (2*X) q c -
      qbM ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient =
      (qbM ArithmeticFunction.vonMangoldt (2*X) q c - ((2*X:ℕ):ℝ)/q.totient) -
      (qbM ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient) := by
    push_cast
    ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add (qgt (2*X) hc hcop)
    (qgt X hc hcop))
theorem qfF {X H q a c : ℕ} (hX : 1 ≤ X)
    (ha : a ≤ H) (hc : c < q) (hcop : Nat.Coprime (c+a) q) :
    |(∑ m ∈ qQ X q c, theta (m+a)) - (X:ℝ)/q.totient| ≤
      (qaq (2*X:ℕ) q : ℝ) + (qaq X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) := by
  let r := (c+a)%q
  have hq : 0 < q := by omega
  have hr : r < q := Nat.mod_lt _ hq
  have hrcop : Nat.Coprime r q := by
    change Nat.gcd ((c+a)%q) q = 1
    rw [← Nat.gcd_rec q (c+a), Nat.gcd_comm]
    exact hcop
  rw [qie theta X q a hc]
  have hs := qgT hX ha q r
  have hp := qhr (U := 2*X) (by omega) X q r
  have he := qej X hr hrcop
  have htri := abs_sub_le (qX theta (X+a) (2*X+a) q r)
    (qX theta X (2*X) q r) ((X:ℝ)/q.totient)
  have htri' := abs_sub_le (qX theta X (2*X) q r)
    (qX ArithmeticFunction.vonMangoldt X (2*X) q r) ((X:ℝ)/q.totient)
  rw [abs_sub_comm (qX ArithmeticFunction.vonMangoldt _ _ _ _)] at hp
  norm_cast at hp
  simpa only [r] using (show |qX theta (X+a) (2*X+a) q r - (X:ℝ)/q.totient| ≤
      (qaq (2*X:ℕ) q : ℝ) + (qaq X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) by
    push_cast at hp
    linarith)
theorem qhs {X H q : ℕ} (hX : 1 ≤ X) :
    (qan X H q : ℝ) ≤
      (qaq (2*X:ℕ) q : ℝ) + (qaq X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) := by
  have hlog : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X by omega))
  have hlog' : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X+H by omega))
  have hnonneg : 0 ≤ (qaq (2*X:ℕ) q : ℝ) + (qaq X q : ℝ) +
      2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
      2*(H:ℝ) * Real.log (2*X+H) := by positivity
  change qan X H q ≤ NNReal.mk _ hnonneg
  apply Finset.sup_le
  rintro ⟨a,c⟩ hac
  have ha : a ≤ H := by simpa using (Finset.mem_product.mp hac).1
  have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hac).2
  dsimp only
  split_ifs with hcop
  · exact qfF hX ha hc hcop
  · exact zero_le
theorem qfS {X : ℕ} (hX : 1 ≤ X) (H Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (qan X H q : ℝ)) ≤
      (∑ q ∈ Finset.Icc 1 Q, (qaq (2*X:ℕ) q : ℝ)) +
      (∑ q ∈ Finset.Icc 1 Q, (qaq X q : ℝ)) +
      (Q:ℝ) * (2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H)) := by
  apply (Finset.sum_le_sum (fun q _ => qhs (H:=H) (q:=q) hX)).trans_eq
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul]
  ring
noncomputable def qaM (rho : ℝ) (X : ℕ) : ℕ := ⌊(X:ℝ)^rho⌋₊
theorem qif {rho : ℝ} (hrho : rho < 1/2) (b : ℝ) :
    ∀ᶠ x : ℝ in atTop, x^rho ≤ x^(1/2:ℝ) * (Real.log x)^(-b) := by
  have h := (isLittleO_log_rpow_rpow_atTop b (show (0:ℝ) < 1/2-rho by linarith)).bound
    (show (0:ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL b)).mpr
  calc
    _ ≤ x^rho * x^(1/2-rho) := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
theorem qjb (x : ℝ) (Q : ℕ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 Q, (qaq x q : ℝ) := by positivity
theorem qfT (hBV : qN) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) {k : ℕ} (hk : 1 ≤ k) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((∑ q ∈ Finset.Icc 1 (qaM rho X), (qaq (k*X:ℕ) q : ℝ)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  obtain ⟨b,hb,M,hM,x₀,hx₀,hest⟩ := hBV (A+1) (by positivity)
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hXlim : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hkXlim : Tendsto (fun X : ℕ => ((k*X:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using hXlim.const_mul_atTop hkR
  have hLlim : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hXlim
  have hlim : Tendsto (fun X : ℕ => (M*(k:ℝ)) / Real.log (X:ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hLlim).const_mul (M*(k:ℝ))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (div_nonneg (qjb _ _) (Nat.cast_nonneg _))
      (pow_nonneg (qw hX).le _)
  · filter_upwards [eventually_ge_atTop 2, hkXlim.eventually (eventually_ge_atTop x₀),
        hkXlim.eventually (qif hrhohalf b)] with X hX hx hcut
    have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
    have hLX : 0 < Real.log (X:ℝ) := qw hX
    have hkX0 : (0:ℝ) < ((k*X:ℕ):ℝ) := by positivity
    have hXkX : (X:ℝ) ≤ ((k*X:ℕ):ℝ) := by exact_mod_cast (Nat.le_mul_of_pos_left X hk)
    have hLle : Real.log (X:ℝ) ≤ Real.log ((k*X:ℕ):ℝ) := Real.log_le_log hX0 hXkX
    have hQ : qaM rho X ≤
        ⌊(((k*X:ℕ):ℝ))^(1/2:ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-b)⌋₊ :=
      Nat.floor_le_floor ((Real.rpow_le_rpow hX0.le hXkX hrho).trans hcut)
    have hsum : (∑ q ∈ Finset.Icc 1 (qaM rho X),
        (qaq (k*X:ℕ) q : ℝ)) ≤
        M * ((k*X:ℕ):ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) := by
      apply le_trans _ (hest _ hx)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hQ)
      intro q _ _
      exact NNReal.coe_nonneg _
    have hlogpow : (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) ≤
        (Real.log (X:ℝ))^(-(A+1:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLX hLle (by have := Nat.cast_nonneg (α:=ℝ) A; linarith)
    calc
      _ ≤ (M * ((k*X:ℕ):ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) / X) *
          (Real.log (X:ℝ))^A :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsum hX0.le) (by positivity)
      _ ≤ (M * ((k*X:ℕ):ℝ) * (Real.log (X:ℝ))^(-(A+1:ℝ)) / X) *
          (Real.log (X:ℝ))^A := by gcongr
      _ = (M*(k:ℝ)) / Real.log (X:ℝ) := by
        rw [Real.rpow_neg hLX.le]
        have hnat : (A:ℝ)+1 = ((A+1:ℕ):ℝ) := by push_cast; rfl
        rw [hnat, Real.rpow_natCast, pow_succ, Nat.cast_mul]
        field_simp
theorem qd8 (H : ℕ → ℕ) {D B : ℝ}
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) :
    ∀ᶠ X : ℕ in atTop, H X ≤ X := by
  have hlim : Tendsto (fun X : ℕ => D * ((Real.log (X:ℝ))^B / (X:ℝ)))
      atTop (nhds 0) := by
    have hh := ((isLittleO_log_rpow_rpow_atTop B (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_one, Function.comp_def, mul_zero] using hh.const_mul D
  filter_upwards [hH, hlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop 1] with X hHX hsmall hX
  have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hh : D*(Real.log (X:ℝ))^B ≤ (X:ℝ) := by
    rw [← mul_div_assoc] at hsmall
    exact (div_lt_one hX0).mp hsmall |>.le
  exact_mod_cast hHX.trans hh
theorem qgU {X H : ℕ} (hX : 3 ≤ X) (hH : H ≤ X) :
    Real.log (2*(X:ℝ)+H) ≤ 2 * Real.log (X:ℝ) := by
  have hX3 : (3:ℝ) ≤ X := by exact_mod_cast hX
  have hHle : (H:ℝ) ≤ X := by exact_mod_cast hH
  have hX0 : (0:ℝ)<X := by linarith
  calc
    _ ≤ Real.log ((X:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num
theorem qig {x L : ℝ} (hx : 0<x) (rho b : ℝ) :
    x^rho * x^b * L / x = L / x^(1-rho-b) := by
  rw [div_eq_mul_inv L, ← Real.rpow_neg hx.le]
  have he : -(1-rho-b) = rho+b-1 := by ring
  rw [he, Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_one]
  ring
theorem qgF (H : ℕ → ℕ) {rho D B : ℝ}
    (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((qaM rho X:ℝ) *
        (2*Real.sqrt (2*(X:ℝ))*Real.log (2*(X:ℝ)) +
          2*(H X:ℝ)*Real.log (2*(X:ℝ)+H X)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  have hlim1 : Tendsto (fun X : ℕ =>
      (Real.log (X:ℝ))^((A:ℝ)+1) / (X:ℝ)^(1/2-rho)) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_rpow_atTop ((A:ℝ)+1) (by linarith)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun X : ℕ =>
      (Real.log (X:ℝ))^(B+(A:ℝ)+1) / (X:ℝ)^(1-rho)) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_rpow_atTop (B+(A:ℝ)+1) (by linarith)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
  have hlim := (hlim1.const_mul 8).add (hlim2.const_mul (4*D))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 3] with X hX
    have hlog1 : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X by omega))
    have hlog2 : 0 ≤ Real.log (2*(X:ℝ)+H X) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H X by omega))
    have hlog : 0 ≤ Real.log (X:ℝ) := (qw (by omega)).le
    positivity
  · filter_upwards [hH, qd8 H hH,
      eventually_ge_atTop 3] with X hHX hHX' hX
    have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hL : 0<Real.log (X:ℝ) := qw (by omega)
    have hlog1 : Real.log (2*(X:ℝ)) ≤ 2*Real.log (X:ℝ) := by
      simpa only [Nat.cast_zero, add_zero] using qgU (H:=0) hX (Nat.zero_le X)
    have hlog2 := qgU hX hHX'
    have hlog1' : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X by omega))
    have hlog2' : 0 ≤ Real.log (2*(X:ℝ)+H X) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H X by omega))
    have hroot : Real.sqrt (2*(X:ℝ)) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [Real.sq_sqrt hX0.le]
    have hQ : (qaM rho X:ℝ) ≤ (X:ℝ)^rho :=
      Nat.floor_le (Real.rpow_nonneg hX0.le _)
    calc
      _ ≤ ((X:ℝ)^rho *
          (2*(2*(X:ℝ)^(1/2:ℝ))*(2*Real.log (X:ℝ)) +
            2*(D*(Real.log (X:ℝ))^B)*(2*Real.log (X:ℝ))) / X) *
          (Real.log (X:ℝ))^A := by gcongr
      _ = 8*((Real.log (X:ℝ))^((A:ℝ)+1)/(X:ℝ)^(1/2-rho)) +
          (4*D)*((Real.log (X:ℝ))^(B+(A:ℝ)+1)/(X:ℝ)^(1-rho)) := by
        have hLA : (Real.log (X:ℝ))^((A:ℝ)+1) = (Real.log (X:ℝ))^A * Real.log (X:ℝ) := by
          rw [Real.rpow_add hL, Real.rpow_natCast, Real.rpow_one]
        have hLBA : (Real.log (X:ℝ))^(B+(A:ℝ)+1) =
            (Real.log (X:ℝ))^B * (Real.log (X:ℝ))^A * Real.log (X:ℝ) := by
          rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_natCast, Real.rpow_one]
        rw [hLA, hLBA]
        have h1 := qig (L:=Real.log (X:ℝ)) hX0 rho (1/2)
        have h2 := qig (L:=Real.log (X:ℝ)) hX0 rho 0
        simp only [Real.rpow_zero, mul_one, sub_zero] at h2
        have hex : (1:ℝ)-rho-1/2 = 1/2-rho := by ring
        rw [hex] at h1
        calc
          _ = 8 * (Real.log (X:ℝ))^A *
                ((X:ℝ)^rho*(X:ℝ)^(1/2:ℝ)*Real.log (X:ℝ)/(X:ℝ)) +
              (4*D)*(Real.log (X:ℝ))^B*(Real.log (X:ℝ))^A *
                ((X:ℝ)^rho*Real.log (X:ℝ)/(X:ℝ)) := by ring
          _ = _ := by rw [h1,h2]; ring
theorem qiG (hBV : qN) (H : ℕ → ℕ)
    {rho D B : ℝ} (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((∑ q ∈ Finset.Icc 1 (qaM rho X), (qan X (H X) q : ℝ)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  have h1 := qfT hBV hrho hrhohalf (k:=1) (by norm_num) A
  have h2 := qfT hBV hrho hrhohalf (k:=2) (by norm_num) A
  have htail := qgF H hrhohalf hD hH A
  have hlim := (h2.add h1).add htail
  simp only [add_zero, one_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := (qw hX).le
    positivity
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (qfS (X:=X) (by omega)
        (H X) (qaM rho X)) (show (0:ℝ)≤X by positivity))
      (pow_nonneg (qw hX).le A)
    convert hh using 1 <;> try rfl
    ring
theorem qeg (Q : ℕ) : 0 ≤ (harmonic Q : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  positivity
theorem qk2 {Q X : ℕ} (hQX : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (harmonic Q : ℝ) ≤ 2 * Real.log (X:ℝ) := by
  have hmono : (harmonic Q : ℝ) ≤ (harmonic X : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hQX) (by intros; positivity)
  have hh := harmonic_le_one_add_log X
  linarith
theorem qmI {rho : ℝ} (hrho : rho ≤ 1) {X : ℕ} (hX : 1 ≤ X) :
    qaM rho X ≤ X := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hh := Real.rpow_le_rpow_of_exponent_le hX1 hrho
  rw [Real.rpow_one] at hh
  have hfloor := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) rho)
  exact_mod_cast hfloor.trans hh
theorem qiH (K : ℕ) {X H Q : ℕ}
    (hX : 3 ≤ X) (hH : H ≤ X) (hQ : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    3*Real.log (2*(X:ℝ)+H)*(harmonic Q:ℝ)^(K^2) +
      (harmonic Q:ℝ)^(2*K^2) ≤
    (6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)) * (Real.log (X:ℝ))^(2*K^2+1) := by
  have hL0 : 0 ≤ Real.log (X:ℝ) := by linarith
  have hhar := qk2 hQ hL
  have hlog := qgU hX hH
  have hpow1 : (Real.log (X:ℝ))^(K^2+1) ≤ (Real.log (X:ℝ))^(2*K^2+1) :=
    pow_le_pow_right₀ hL (by omega)
  have hpow2 : (Real.log (X:ℝ))^(2*K^2) ≤ (Real.log (X:ℝ))^(2*K^2+1) :=
    pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ (3*(2*Real.log (X:ℝ)))*(2*Real.log (X:ℝ))^(K^2) +
        (2*Real.log (X:ℝ))^(2*K^2) := by
      apply add_le_add
      · apply mul_le_mul
        · linarith
        · exact pow_le_pow_left₀ (qeg Q) hhar _
        · exact pow_nonneg (qeg Q) _
        · positivity
      · exact pow_le_pow_left₀ (qeg Q) hhar _
    _ = 6*(2:ℝ)^(K^2)*(Real.log (X:ℝ))^(K^2+1) +
        (2:ℝ)^(2*K^2)*(Real.log (X:ℝ))^(2*K^2) := by rw [mul_pow, mul_pow, pow_succ]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow1 (show (0:ℝ)≤6*2^(K^2) by positivity),
      mul_le_mul_of_nonneg_left hpow2 (show (0:ℝ)≤2^(2*K^2) by positivity)]
noncomputable def qbG (K X H Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (K:ℝ)^q.primeFactors.card *
    (qan X H q : ℝ) else 0
theorem qfq (K X H Q : ℕ) : 0 ≤ qbG K X H Q := by
  classical
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> positivity
theorem qjc (K : ℕ) {X H Q : ℕ}
    (hX : 3 ≤ X) (hH : H ≤ X) (hQ : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (qbG K X H Q)^2 ≤
      (∑ q ∈ Finset.Icc 1 Q, (qan X H q : ℝ)) * X *
      ((6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)) * (Real.log (X:ℝ))^(2*K^2+1)) := by
  have hlog : 0 ≤ 3 * Real.log (2*(X:ℝ)+H) := by
    have hh : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H by omega))
    positivity
  apply (qid K Q (fun q => (qan X H q : ℝ))
    (fun q => NNReal.coe_nonneg _) (Nat.cast_nonneg X) hlog ?_).trans
  · apply mul_le_mul_of_nonneg_left (qiH K hX hH hQ hL)
    positivity
  · intro q hq hsq
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    exact qlT (by omega) hq1 (hqQ.trans hQ) hsq
theorem qiI (hBV : qN) (K : ℕ) (H : ℕ → ℕ)
    {rho D B : ℝ} (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ => (qbG K X (H X) (qaM rho X) / X) *
      (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  let c : ℝ := 6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlim := (qiG hBV H hrho hrhohalf hD hH
    (2*K^2+1+2*A)).const_mul c
  simp only [mul_zero] at hlim
  have hsqrt := hlim.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  have hLlim : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hsqrt
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (div_nonneg (qfq _ _ _ _) (Nat.cast_nonneg _))
      (pow_nonneg (qw hX).le _)
  · filter_upwards [eventually_ge_atTop 3, qd8 H hH,
      hLlim.eventually (eventually_ge_atTop 1)] with X hX hHX hLX
    have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hs := qjc K hX hHX
      (qmI (by linarith : rho ≤ 1) (by omega)) hLX
    have hh : ((qbG K X (H X) (qaM rho X) / X) *
        (Real.log (X:ℝ))^A)^2 ≤
        c * (((∑ q ∈ Finset.Icc 1 (qaM rho X), (qan X (H X) q : ℝ)) / X) *
          (Real.log (X:ℝ))^(2*K^2+1+2*A)) := by
      have hm := mul_le_mul_of_nonneg_right hs
        (show 0 ≤ (Real.log (X:ℝ))^(2*A)/(X:ℝ)^2 by positivity)
      dsimp only [c]
      convert hm using 1 <;> try rfl
      · rw [mul_pow, div_pow, ← pow_mul, Nat.mul_comm A 2]
        ring
      · rw [pow_add]
        field_simp
    have hnonneg : 0 ≤ (qbG K X (H X) (qaM rho X) / X) *
        (Real.log (X:ℝ))^A := by
      apply mul_nonneg (div_nonneg (qfq _ _ _ _) hX0.le)
      exact pow_nonneg (by linarith) _
    have hh' := Real.sqrt_le_sqrt hh
    simpa only [Real.sqrt_sq hnonneg] using hh'
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
def qax (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image fun a => a % (p:ℤ)).card
noncomputable def qR (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (qax H p : ℝ)/(p:ℝ)) / (1 - 1/(p:ℝ))^H.card
noncomputable def qay (H : Finset ℤ) : ℝ :=
  ∏' p : Nat.Primes, qR H p
noncomputable def qdz (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, qR H p
theorem qgV (H : Finset ℤ) (p : ℕ) : qax H p ≤ H.card :=
  Finset.card_image_le
theorem qkD (s : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (1-u)^s - (1-(s:ℝ)*u) ∧
    (1-u)^s - (1-(s:ℝ)*u) ≤ (s:ℝ)^2*u^2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hid : (1-u)^(s+1) - (1-((s+1:ℕ):ℝ)*u) =
        (1-u)*((1-u)^s-(1-(s:ℝ)*u))+(s:ℝ)*u^2 := by
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hid]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) ih.1) (by positivity)
    · have hh := mul_le_mul_of_nonneg_left ih.2 (by linarith : 0≤1-u)
      have hpos : 0 ≤ (s:ℝ)^2*u^2 := by positivity
      have hsm : (1-u)*((s:ℝ)^2*u^2) ≤ (s:ℝ)^2*u^2 := by nlinarith
      push_cast
      nlinarith [sq_nonneg u, Nat.cast_nonneg (α:=ℝ) s]
theorem qhI (s : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    |(1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s - 1| ≤
      ((s:ℝ)^2 * (2:ℝ)^s) / (p:ℝ)^2 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hu0 : 0 ≤ (1:ℝ)/p := by positivity
  have hu1 : (1:ℝ)/p ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) hpR)
  have hs := qkD s hu0 (by linarith)
  have hm : (s:ℝ)*(1/(p:ℝ))=(s:ℝ)/(p:ℝ) := by ring
  rw [hm] at hs
  have hd0 : 0 < (1-(1:ℝ)/p)^s := pow_pos (by linarith) _
  have hdp : (1/2:ℝ)^s ≤ (1-1/(p:ℝ))^s :=
    pow_le_pow_left₀ (by norm_num) (by linarith) s
  have hnum : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s ≤ 1 := by
    apply (div_le_one hd0).mpr
    nlinarith [hs.1]
  rw [abs_of_nonpos (by linarith : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s-1≤0)]
  calc
    _ = ((1-1/(p:ℝ))^s - (1-(s:ℝ)/(p:ℝ))) / (1-1/(p:ℝ))^s := by simp only [sub_div, div_self hd0.ne']; ring
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1-1/(p:ℝ))^s := by
      apply div_le_div_of_nonneg_right _ hd0.le
      exact hs.2
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1/2:ℝ)^s :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdp
    _ = _ := by simp only [div_pow, one_pow]; field_simp
theorem qht (H : Finset ℤ) {p : ℕ}
    (hp : 2 * H.sup Int.natAbs < p) : qax H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hab)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hlt : (a-b).natAbs < p := by
    have h1 := Finset.le_sup (f:=Int.natAbs) ha
    have h2 := Finset.le_sup (f:=Int.natAbs) hb
    have h3 := Int.natAbs_sub_le a b
    omega
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdN hlt))
theorem qih (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hlarge : 2 * H.sup Int.natAbs < p) :
    |qR H p - 1| ≤ ((H.card:ℝ)^2 * (2:ℝ)^H.card) / (p:ℝ)^2 := by
  simpa only [qR, qht H hlarge] using
    qhI H.card hp
theorem qhQ (H : Finset ℤ) :
    Summable (fun p : ℕ => if p.Prime then qR H p - 1 else 0) := by
  have hh : Summable (fun p : ℕ => ((H.card:ℝ)^2 * (2:ℝ)^H.card) / (p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)).mul_left
        ((H.card:ℝ)^2 * (2:ℝ)^H.card))
  apply hh.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max 2 (2*H.sup Int.natAbs+1))] with p hp
  split_ifs with hprime
  · rw [Real.norm_eq_abs]
    exact qih H (by omega) (by omega)
  · simp only [norm_zero]
    positivity
theorem qii (H : Finset ℤ) :
    Multipliable (fun p : Nat.Primes => qR H p) := by
  apply (Nat.Primes.multipliable_iff_multipliable_ite (qR H)).mpr
  have hh := Real.multipliable_one_add_of_summable (qhQ H)
  apply hh.congr
  intro p
  split_ifs <;> ring
def qaz (H : Finset ℤ) : ℕ :=
  ∏ a ∈ H, ∏ b ∈ H.erase a, (a-b).natAbs
theorem qgu (H : Finset ℤ) : 0 < qaz H := by
  classical
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hba.symm)
theorem qeh {H : Finset ℤ} {p : ℕ}
    {a b : ℤ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hmod : a % (p:ℤ) = b % (p:ℤ)) : p ∣ qaz H := by
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact hdN.trans ((Finset.dvd_prod_of_mem (fun b => (a-b).natAbs)
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)).trans
    (Finset.dvd_prod_of_mem (fun a => ∏ b ∈ H.erase a, (a-b).natAbs) ha))
theorem qgG (H : Finset ℤ) {p : ℕ}
    (hp : ¬p ∣ qaz H) : qax H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  by_contra hne
  exact hp (qeh ha hb hne hab)
theorem qlr (H : Finset ℤ) {M : ℕ}
    (hM : ∀ a ∈ H, ∀ b ∈ H, (a-b).natAbs ≤ M) :
    qaz H ≤ M^(H.card*(H.card-1)) := by
  classical
  calc
    _ ≤ ∏ a ∈ H, M^(H.card-1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro a ha
      calc
        _ ≤ ∏ _b ∈ H.erase a, M := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun b hb =>
          hM a ha b (Finset.mem_erase.mp hb).2
        _ = _ := by simp [Finset.card_erase_of_mem ha]
    _ = _ := by simp [← pow_mul, Nat.mul_comm]
theorem qek {x : ℝ} (hx : 1/2 ≤ x) :
    |Real.log x| ≤ 2*|x-1| := by
  have hx0 : 0<x := by linarith
  by_cases hx1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)]
    linarith [Real.log_le_sub_one_of_pos hx0]
  · have hx1' : x ≤ 1 := le_of_not_ge hx1
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1'), abs_of_nonpos (by linarith)]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
    rw [Real.log_inv] at hh
    have hi : x⁻¹-1 ≤ 2*(1-x) := by
      have hh : (1:ℝ) / x ≤ 2*(1-x)+1 := (div_le_iff₀ hx0).mpr (by nlinarith)
      simpa only [one_div] using (sub_le_iff_le_add).mpr hh
    linarith
theorem qij {u : ℝ} (hu0 : 0≤u) (hu1 : u≤1/2) :
    |Real.log (1-u)| ≤ 2*u := by
  have hh := qek (x:=1-u) (by linarith)
  simpa only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hu0] using hh
theorem qgv (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2 * H.card ≤ p) : 1/2 ≤ qR H p := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (qax H p:ℝ) ≤ H.card := by exact_mod_cast qgV H p
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hd0 : 0 ≤ 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  have hd1 : 1-(1:ℝ)/p ≤ 1 := sub_le_self _ (by positivity)
  have hpow : (1-(1:ℝ)/p)^H.card ≤ 1 := pow_le_one₀ hd0 hd1
  have hn0 : 1/2 ≤ 1-(qax H p:ℝ)/p := by
    have hh : (qax H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  unfold qR
  have hdpos : 0 < 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  exact hn0.trans (le_div_self (by linarith) (pow_pos hdpos _) hpow)
theorem qjd (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) (hdiv : ¬p ∣ qaz H) :
    |Real.log (qR H p)| ≤
      2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
  have h1 := qek (qgv H hp hps)
  have h2 : |qR H p-1| ≤ ((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
    simpa only [qR, qgG H hdiv] using
      qhI H.card hp
  calc
    _ ≤ 2*|qR H p-1| := h1
    _ ≤ 2*(((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2) := by gcongr
    _ = _ := by ring
theorem qj8 (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) :
    |Real.log (qR H p)| ≤ 4*(H.card:ℝ)/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (qax H p:ℝ) ≤ H.card := by exact_mod_cast qgV H p
  have hn0 : 0 ≤ (qax H p:ℝ)/p := by positivity
  have hn1 : (qax H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hq1 : (1:ℝ)/p ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpR
  have hlog1 := qij hn0 hn1
  have hlog2 := qij (by positivity : 0≤(1:ℝ)/p) hq1
  rw [qR, Real.log_div (by linarith : (1-(qax H p:ℝ)/p) ≠ 0)
    (pow_ne_zero _ (by linarith : (1-(1:ℝ)/p) ≠ 0)), Real.log_pow]
  calc
    _ ≤ |Real.log (1-(qax H p:ℝ)/p)| +
          |(H.card:ℝ)*Real.log (1-(1:ℝ)/p)| := abs_sub _ _
    _ = |Real.log (1-(qax H p:ℝ)/p)| +
          (H.card:ℝ)*|Real.log (1-(1:ℝ)/p)| := by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ H.card from Nat.cast_nonneg _)]
    _ ≤ 2*((qax H p:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hn hp0.le
      calc
        _ ≤ 2*((H.card:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
        _ = _ := by ring
theorem qgW {S : Finset ℕ} {y : ℕ} (hy : 0 < y)
    (hS : ∀ n ∈ S, y < n) : (∑ n ∈ S, (1:ℝ)/(n:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp
  let N := S.sup id
  have hsub : S ⊆ Finset.Ico y (N+1) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨(hS n hn).le, Nat.lt_succ_iff.mpr (Finset.le_sup (f:=id) hn)⟩
  have hN : y ≤ N+1 := by
    obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    exact (Finset.mem_Ico.mp (hsub hn)).1.trans (Finset.mem_Ico.mp (hsub hn)).2.le
  have htel : (∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
      1/(y:ℝ)-1/(N+1:ℕ) := by
    rw [Finset.sum_Ico_eq_sub _ hN]
    have hh (k : ℕ) : (∑ n ∈ Finset.range k, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
        (1:ℝ)/(0:ℕ)-1/(k:ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Finset.sum_range_sub' (fun n : ℕ => (1:ℝ)/(n:ℝ)) k
    rw [hh, hh]
    ring
  have hstep (n : ℕ) (hn : y < n) :
      (1:ℝ)/(n:ℝ)^2 ≤ (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) := by
    have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hid : (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) = 1/((n:ℝ)*((n:ℝ)-1)) := by
      field_simp [show (n:ℝ) ≠ 0 by linarith, show (n:ℝ)-1 ≠ 0 by linarith]
      ring
    rw [hid]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

  let T := S.image (fun n => n-1)
  have hi : Set.InjOn (fun n : ℕ => n-1) ↑S := by
    intro n hn m hm he
    have := hS n hn
    have := hS m hm
    change n-1=m-1 at he
    omega
  have he : (∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ))) =
      ∑ n ∈ T, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_sub (by have := hS n hn; omega), Nat.cast_one]
    congr 2
    ring
  calc
    _ ≤ ∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ)) :=
      Finset.sum_le_sum fun n hn => hstep n (hS n hn)
    _ = _ := he
    _ ≤ ∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have := hS n hn
        have hsup : n ≤ N := Finset.le_sup (f:=id) hn
        simp only [Finset.mem_Ico]
        change y ≤ n-1 ∧ n-1<N+1
        omega
      · intro n hn _
        have hn0 : (0:ℝ)<n := by exact_mod_cast (hy.trans_le (Finset.mem_Ico.mp hn).1)
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hn0 (by linarith))
    _ = 1/(y:ℝ)-1/(N+1:ℕ) := htel
    _ ≤ _ := sub_le_self _ (by positivity)
theorem qgH {D y : ℕ} (hD : 0 < D) (hy : 1 < y)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p ∧ p ∣ D) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Real.log D / ((y:ℝ)*Real.log y) := by
  have hy0 : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hy1 : (1:ℝ)<y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos hy1
  have hsub : S ⊆ D.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2.2, hD.ne'⟩
  have hprod : (∏ p ∈ S, p) ≤ D := Nat.le_of_dvd hD
    ((Finset.prod_dvd_prod_of_subset S D.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd D))
  have hprodpos : (0:ℝ) < ∏ p ∈ S, (p:ℝ) := Finset.prod_pos fun p hp => by
    exact_mod_cast (hS p hp).1.pos
  have hlogs : (∑ p ∈ S, Real.log (p:ℝ)) ≤ Real.log D := by
    rw [← Real.log_prod (s:=S) (f:=fun p : ℕ => (p:ℝ))
      (fun p hp => (ne_of_gt (by exact_mod_cast (hS p hp).1.pos : (0:ℝ)<p)))]
    exact Real.log_le_log hprodpos (by
      simpa only [Nat.cast_prod] using (show ((∏ p ∈ S, p : ℕ):ℝ) ≤ (D:ℝ) by exact_mod_cast hprod))
  calc
    _ ≤ ∑ p ∈ S, Real.log (p:ℝ) / ((y:ℝ)*Real.log y) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpy : (y:ℝ)≤p := by exact_mod_cast (hS p hp).2.1.le
      have hlogp := Real.log_le_log hy0 hpy
      calc
        _ ≤ 1/(y:ℝ) := one_div_le_one_div_of_le hy0 hpy
        _ = Real.log (y:ℝ)/((y:ℝ)*Real.log y) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hlogp (by positivity)
    _ = (∑ p ∈ S, Real.log (p:ℝ))/((y:ℝ)*Real.log y) := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hlogs (by positivity)
noncomputable def qbe (H : Finset ℤ) (y : ℕ) : ℝ :=
  2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(y:ℝ) +
    4*(H.card:ℝ)*Real.log (qaz H)/((y:ℝ)*Real.log y)
theorem qik (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p) :
    (∑ p ∈ S, |Real.log (qR H p)|) ≤ qbe H y := by
  classical
  let K : ℝ := 2*((H.card:ℝ)^2*(2:ℝ)^H.card)
  have hK : 0≤K := by dsimp [K]; positivity
  have hsum : (∑ p ∈ S, |Real.log (qR H p)|) ≤
      (∑ p ∈ S, K*(1/(p:ℝ)^2)) +
      ∑ p ∈ S.filter (fun p => p ∣ qaz H), 4*(H.card:ℝ)*(1/(p:ℝ)) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hd : p ∣ qaz H
    · simp only [hd, ite_true]
      have hh := qj8 H (hS p hp).1.two_le (hys.trans (hS p hp).2.le)
      calc
        _ ≤ 4*(H.card:ℝ)/(p:ℝ) := hh
        _ ≤ K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)) := by
          have h0 : 0≤K*(1/(p:ℝ)^2) := by positivity
          simpa only [mul_one_div] using
            (le_add_of_nonneg_left h0 : 4*(H.card:ℝ)*(1/(p:ℝ)) ≤
              K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)))
    · simp only [hd, ite_false, add_zero]
      simpa only [K, mul_one_div] using
        qjd H (hS p hp).1.two_le (hys.trans (hS p hp).2.le) hd
  have hinv := qgW (show 0<y by omega) (fun p hp => (hS p hp).2)
  have hdiv := qgH (qgu H) hy
    (S.filter (fun p => p ∣ qaz H)) (by
      intro p hp
      obtain ⟨hpS, hd⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hpS).1, (hS p hpS).2, hd⟩)
  calc
    _ ≤ _ := hsum
    _ = K*(∑ p ∈ S, 1/(p:ℝ)^2) +
        4*(H.card:ℝ)*(∑ p ∈ S.filter (fun p => p ∣ qaz H), 1/(p:ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ K*(1/(y:ℝ)) + 4*(H.card:ℝ)*(Real.log (qaz H)/((y:ℝ)*Real.log y)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinv hK)
        (mul_le_mul_of_nonneg_left hdiv (by positivity))
    _ = _ := by unfold qbe K; ring
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def qaf (H : Finset ℤ) (y p : ℕ) : ℝ :=
  if p.Prime ∧ y<p then qR H p else 1
noncomputable def qcC (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏' p : ℕ, qaf H y p
theorem qfU (H : Finset ℤ) {y : ℕ} (hys : 2*H.card ≤ y) (p : ℕ) :
    0 < qaf H y p := by
  unfold qaf
  split_ifs with h
  · have hh := qgv H h.1.two_le (hys.trans h.2.le)
    linarith
  · norm_num
theorem qdm (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    Summable (fun p : ℕ => Real.log (qaf H y p)) ∧
    |∑' p : ℕ, Real.log (qaf H y p)| ≤ qbe H y := by
  have hfin (S : Finset ℕ) :
      (∑ p ∈ S, |Real.log (qaf H y p)|) ≤ qbe H y := by
    have hh := qik H hy hys (S.filter (fun p => p.Prime ∧ y<p))
      (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa only [Finset.sum_filter, qaf, apply_ite Real.log,
      Real.log_one, apply_ite abs, abs_zero] using hh
  have hs := summable_of_sum_le (fun p => abs_nonneg (Real.log (qaf H y p))) hfin
  refine ⟨summable_abs_iff.mp hs, ?_⟩
  calc
    _ ≤ ∑' p : ℕ, |Real.log (qaf H y p)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f:=fun p : ℕ => Real.log (qaf H y p)) (by
        simpa only [Real.norm_eq_abs] using hs)
    _ ≤ _ := hs.tsum_le_of_sum_le hfin
theorem qgX (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    0 < qcC H y ∧ |Real.log (qcC H y)| ≤ qbe H y := by
  have hs := qdm H hy hys
  have he : qcC H y = Real.exp (∑' p : ℕ, Real.log (qaf H y p)) :=
    (Real.rexp_tsum_eq_tprod (qfU H hys) hs.1).symm
  rw [he, Real.log_exp]
  exact ⟨Real.exp_pos _, hs.2⟩
theorem ql9 (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (hsmall : qbe H y ≤ 1) :
    |qcC H y - 1| ≤ 2*qbe H y := by
  obtain ⟨hpos, hlog⟩ := qgX H hy hys
  have he := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log hpos] at he
  exact he.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
theorem qeO (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    qay H = qdz H y * qcC H y := by
  classical
  let head : ℕ → ℝ := fun p => if p ∈ Nat.primesLE y then qR H p else 1
  have hh : HasProd head (qdz H y) := by
    have hh : HasProd head (∏ p ∈ Nat.primesLE y, head p) :=
      hasProd_prod_of_ne_finset_one (s:=Nat.primesLE y) (f:=head)
      (fun p hp => if_neg hp)
    simpa only [head, qdz, Finset.prod_ite_mem, Finset.inter_self] using hh
  have ht := Real.hasProd_of_hasSum_log (qfU H hys)
    (qdm H hy hys).1.hasSum
  have hp : (fun p => head p * qaf H y p) =
      (fun p : ℕ => if p.Prime then qR H p else 1) := by
    funext p
    simp only [head, qaf, Nat.mem_primesLE]
    split_ifs <;> first | omega | simp_all
  have htt : HasProd (qaf H y) (qcC H y) := by
    simpa only [qcC, ← ht.tprod_eq] using ht
  have hfull := hh.mul htt
  rw [hp] at hfull
  simpa only [qay, Nat.Primes.tprod_eq_tprod_ite] using hfull.tprod_eq
noncomputable def qbm {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) : ℝ :=
  ∑ x : ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0
noncomputable def qO {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) : ℝ :=
  ((q:ℝ)/q.totient)^s * qbm a / q
theorem qma (q : ℕ) [NeZero q] :
    (∑ x : ZMod q, if IsUnit x then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have he : (Finset.univ.filter fun x : ZMod q => IsUnit x) =
      Finset.univ.image (fun x : (ZMod q)ˣ => (x:ZMod q)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    change IsUnit x ↔ ∃ u : (ZMod q)ˣ, (u:ZMod q) = x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, rfl⟩
      exact u.isUnit
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
    ZMod.card_units_eq_totient]
theorem qiJ {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if IsUnit (x-a) then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have hh := (Equiv.subLeft x).sum_comp (fun a : ZMod q => if IsUnit a then (1:ℝ) else 0)
  exact hh.trans (qma q)
theorem qmJ (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, qbm a) = (q:ℝ)*(q.totient:ℝ)^s := by
  classical
  unfold qbm
  rw [Finset.sum_comm]
  have hf (x : ZMod q) :
      (∑ a : Fin s → ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0) =
      (q.totient:ℝ)^s := by
    calc
      _ = ∏ _i : Fin s, ∑ b : ZMod q, if IsUnit (x-b) then (1:ℝ) else 0 :=
        (Fintype.prod_sum (fun (_i : Fin s) (b : ZMod q) =>
          if IsUnit (x-b) then (1:ℝ) else 0)).symm
      _ = _ := by simp only [qiJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hf]
  simp
theorem qje (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, qO a) = (q:ℝ)^s := by
  classical
  have hq : (q:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ht : (q.totient:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold qO
  rw [← Finset.sum_div, ← Finset.mul_sum, qmJ]
  rw [div_pow]
  field_simp
theorem qmK {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    qbm a =
      qbm (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      qbm (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  classical
  let e := ZMod.chineseRemainder hcop
  have hu (y : ZMod (m*n)) : IsUnit y ↔ IsUnit (e y) := by
    constructor
    · intro hy
      exact hy.map e.toMonoidHom
    · intro hy
      have hh := hy.map e.symm.toMonoidHom
      change IsUnit (e.symm (e y)) at hh
      simpa only [e.symm_apply_apply] using hh
  have hi (x : ZMod (m*n)) (i : Fin s) :
      (if IsUnit (x-a i) then (1:ℝ) else 0) =
      (if IsUnit ((e x).1-(e (a i)).1) then (1:ℝ) else 0) *
      (if IsUnit ((e x).2-(e (a i)).2) then (1:ℝ) else 0) := by
    simp only [hu, e.map_sub, Prod.isUnit_iff, Prod.fst_sub, Prod.snd_sub]
    split_ifs <;> first | omega | simp_all
  unfold qbm
  simp_rw [hi, Finset.prod_mul_distrib]
  have he := e.toEquiv.sum_comp (fun x : ZMod m × ZMod n =>
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0))
  change _ = _ at he
  calc
    _ = ∑ x : ZMod m × ZMod n,
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0) := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun x : ZMod m => ∏ i : Fin s, if IsUnit (x-(e (a i)).1) then (1:ℝ) else 0)
        (fun x : ZMod n => ∏ i : Fin s, if IsUnit (x-(e (a i)).2) then (1:ℝ) else 0)).symm
theorem qjf {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    qO a =
      qO (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      qO (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  rw [qO, qmK hcop, Nat.totient_mul hcop]
  simp only [qO, Nat.cast_mul, mul_div_mul_comm, mul_pow]
  ring
theorem qmo (s : ℕ) (P : Fin s → Prop) [DecidablePred P] :
    (∏ i : Fin s, if P i then (1:ℝ) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
theorem qmp {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    qbm a = (p:ℝ) - (Finset.univ.image a).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have he : (Finset.univ.filter fun x : ZMod p => ∀ i, x ≠ a i) =
      Finset.univ \ Finset.univ.image a := by
    ext x
    simp [eq_comm]
  unfold qbm
  simp_rw [isUnit_iff_ne_zero, sub_ne_zero, qmo]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub]
  · simp [ZMod.card]
  · exact Finset.card_le_card (Finset.subset_univ _)
theorem qil {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    qO a =
      (1 - ((Finset.univ.image a).card:ℝ)/(p:ℝ)) / (1-1/(p:ℝ))^s := by
  classical
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [qO, qmp hp, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hd : (1:ℝ)-1/p = ((p:ℝ)-1)/p := by field_simp
  rw [hd]
  simp only [div_pow]
  field_simp
noncomputable def qao {s : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  if h : q=0 then 0 else
    let _ : NeZero q := ⟨h⟩
    qO (fun i => (a i : ZMod q))
theorem qcq {s q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    qao a q = qO (fun i => (a i : ZMod q)) := by
  simp only [qao, dif_neg (NeZero.ne q)]
theorem qmL {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ℤ) :
    qao a (m*n) = qao a m * qao a n := by
  simp only [qcq]
  rw [qjf hcop]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]
theorem qmM {s : ℕ} (a : Fin s → ℤ) : qao a 1 = 1 := by
  classical
  have hu (x : ZMod 1) : IsUnit x := by
    convert isUnit_one (M:=ZMod 1) using 1
    exact Subsingleton.elim _ _
  simp only [qcq, qO, qbm, hu, ite_true]
  simp
theorem qlU {s : ℕ} (a : Fin s → ℤ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    qao a (∏ p ∈ P, p) = ∏ p ∈ P, qao a p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [qmM]
  | @insert p P hp ih =>
    have hpP := hP p (Finset.mem_insert_self p P)
    have hP' (q) (hq : q ∈ P) := hP q (Finset.mem_insert_of_mem hq)
    let hp0 : NeZero p := ⟨hpP.ne_zero⟩
    let hprod0 : NeZero (∏ q ∈ P, q) := ⟨Finset.prod_ne_zero_iff.mpr
      (fun q hq => (hP' q hq).ne_zero)⟩
    have hc : p.Coprime (∏ q ∈ P, q) := Nat.Coprime.prod_right fun q hq => by
      apply hpP.coprime_iff_not_dvd.mpr
      intro hd
      have he := ((hP' q hq).dvd_iff_eq hpP.ne_one).mp hd
      exact hp (he.symm ▸ hq)
    simp only [Finset.prod_insert hp]
    rw [qmL hc, ih hP']
theorem qim {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ qbm a := by
  unfold qbm
  positivity
theorem qmQ {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    qbm a ≤ (q:ℝ) := by
  classical
  calc
    _ ≤ ∑ _x : ZMod q, (1:ℝ) := by
      unfold qbm
      apply Finset.sum_le_sum
      intro x _
      exact Finset.prod_le_one (fun _ _ => by positivity) (fun _ _ => by split_ifs <;> norm_num)
    _ = _ := by simp
theorem qcr {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ qO a :=
  div_nonneg (mul_nonneg (by positivity) (qim a)) (Nat.cast_nonneg _)
theorem qjD {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    qO a ≤ (q:ℝ)^s := by
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have ht : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : (q:ℝ)/q.totient ≤ q := (div_le_self hq.le ht)
  unfold qO
  calc
    _ ≤ (q:ℝ)^s * q / q := div_le_div_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hdiv s) (qmQ a)
        (qim a) (by positivity)) hq.le
    _ = _ := mul_div_cancel_right₀ _ hq.ne'
theorem qjg (H : Finset ℤ) {q : ℕ} [NeZero q] :
    qax H q = (H.image fun a : ℤ => (a : ZMod q)).card := by
  classical
  have he : (H.image fun a => a % (q:ℤ)).image (fun a : ℤ => (a : ZMod q)) =
      H.image (fun a : ℤ => (a : ZMod q)) := by
    rw [Finset.image_image]
    congr 1
    funext a
    exact ZMod.intCast_mod a q
  rw [← he]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
  have hh := (ZMod.intCast_eq_intCast_iff _ _ q).mp heq
  change (a' % (q:ℤ)) % (q:ℤ) = (b' % (q:ℤ)) % (q:ℤ) at hh
  simpa only [Int.emod_emod] using hh
theorem qls {s p : ℕ} (hp : Nat.Prime p) (a : Fin s → ℤ)
    (ha : Function.Injective a) :
    qao a p = qR (Finset.univ.image a) p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [qcq, qil hp, qR,
    qjg, Finset.image_image,
    Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  rfl
theorem qjE {s y : ℕ} (a : Fin s → ℤ) (ha : Function.Injective a) :
    qao a (∏ p ∈ Nat.primesLE y, p) = qdz (Finset.univ.image a) y := by
  rw [qlU a _ (fun p hp => (Nat.mem_primesLE.mp hp).2)]
  exact Finset.prod_congr rfl fun p hp => qls (Nat.mem_primesLE.mp hp).2 a ha
def qe0 (h q c : ℕ) : Finset ℕ := (Finset.range h).filter fun n => n%q=c
theorem qjF (h : ℕ) {q c : ℕ} (hq : 0<q) (hc : c<q) :
    h/q ≤ (qe0 h q c).card ∧ (qe0 h q c).card ≤ h/q+1 := by
  have hlo : (Finset.range (h/q)).card ≤ (qe0 h q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q*k+c)
    · intro k hk
      have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      have hh' : q*k+q ≤ q*(h/q) := by simpa only [Nat.mul_succ] using hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        change q*k+c<h
        have hd : q*(h/q) ≤ h := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self h q
        omega), ?_⟩
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  have hup : (qe0 h q c).card ≤ (Finset.range (h/q+1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n/q)
    · intro n hn
      have hh : n/q ≤ h/q := Nat.div_le_div_right (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
      exact Finset.mem_range.mpr (by dsimp only; omega)
    · intro n hn m hm heq
      have hnmod := (Finset.mem_filter.mp hn).2
      have hmmod := (Finset.mem_filter.mp hm).2
      have hnform := Nat.div_add_mod n q
      have hmform := Nat.div_add_mod m q
      change n/q=m/q at heq
      rw [heq, hnmod] at hnform
      rw [hmmod] at hmform
      omega
  simpa only [Finset.card_range] using And.intro hlo hup
noncomputable def qew (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) : Finset (Fin h) :=
  Finset.univ.filter fun n => (a:ZMod q)+(n:ℕ)=r
theorem qfr (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) :
    h/q ≤ (qew a h q r).card ∧ (qew a h q r).card ≤ h/q+1 := by
  classical
  have hpred (n : ℕ) : (a:ZMod q)+(n:ZMod q)=r ↔ n%q=(r-(a:ZMod q)).val := by
    rw [← eq_sub_iff_add_eq']
    constructor
    · intro he
      simpa only [ZMod.val_natCast] using congrArg ZMod.val he
    · intro he
      apply ZMod.val_injective q
      simpa only [ZMod.val_natCast] using he
  have hc : (qew a h q r).card = (qe0 h q (r-(a:ZMod q)).val).card := by
    apply Finset.card_bij (fun (n : Fin h) _ => (n:ℕ))
    · intro n hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.isLt, ?_⟩
      exact (hpred n).mp (Finset.mem_filter.mp hn).2
    · intro n _ m _ he
      exact Fin.ext he
    · intro n hn
      obtain ⟨hn, hmod⟩ := Finset.mem_filter.mp hn
      refine ⟨⟨n, Finset.mem_range.mp hn⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpred n).mpr hmod⟩
  rw [hc]
  exact qjF h (NeZero.pos q) (ZMod.val_lt _)
noncomputable def qa5 {s h q : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ZMod q :=
  fun i => (a i:ZMod q)+(n i:ℕ)
theorem qj9 {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (r : Fin s → ZMod q) :
    (Finset.univ.filter fun n : Fin s → Fin h => qa5 a n = r).card =
      ∏ i : Fin s, (qew (a i) h q (r i)).card := by
  classical
  have he : (Finset.univ.filter fun n : Fin s → Fin h => qa5 a n = r) =
      Fintype.piFinset (fun i => qew (a i) h q (r i)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      qew, funext_iff, qa5]
  rw [he, Fintype.card_piFinset]
theorem qka {s h q : ℕ} [NeZero q] (a : Fin s → ℤ)
    (f : (Fin s → ZMod q) → ℝ) (hf : ∀ r, 0≤f r) :
    ((h/q:ℕ):ℝ)^s * (∑ r, f r) ≤ (∑ n : Fin s → Fin h, f (qa5 a n)) ∧
    (∑ n : Fin s → Fin h, f (qa5 a n)) ≤ ((h/q+1:ℕ):ℝ)^s * (∑ r, f r) := by
  classical
  have he : (∑ n : Fin s → Fin h, f (qa5 a n)) =
      ∑ r : Fin s → ZMod q,
        ((Finset.univ.filter fun n : Fin s → Fin h => qa5 a n = r).card:ℝ) * f r := by
    rw [← Finset.sum_fiberwise Finset.univ (qa5 (q:=q) a) (fun n => f (qa5 a n))]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = ∑ _n ∈ Finset.univ.filter (fun n : Fin s → Fin h => qa5 a n = r), f r := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ = _ := by simp
  rw [he]
  have hcard (r : Fin s → ZMod q) : ((h/q:ℕ):ℝ)^s ≤
      ((Finset.univ.filter fun n : Fin s → Fin h => qa5 a n = r).card:ℝ) ∧
      ((Finset.univ.filter fun n : Fin s → Fin h => qa5 a n = r).card:ℝ) ≤
        ((h/q+1:ℕ):ℝ)^s := by
    rw [qj9, Nat.cast_prod]
    constructor
    · calc
        _ = ∏ _i : Fin s, ((h/q:ℕ):ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
          exact_mod_cast (qfr (a i) h q (r i)).1
    · calc
        _ ≤ ∏ _i : Fin s, ((h/q+1:ℕ):ℝ) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
            exact_mod_cast (qfr (a i) h q (r i)).2
        _ = _ := by simp
  simp only [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).1 (hf r),
    Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).2 (hf r)⟩
def qt {s h : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ℤ :=
  fun i => a i + (n i:ℕ)
theorem qjG {s h : ℕ} (a : Fin s → ℤ) {i j : Fin s} (hij : i≠j) :
    (Finset.univ.filter fun n : Fin s → Fin h => qt a n i = qt a n j).card ≤
      h^(s-1) := by
  classical
  have hc : Fintype.card {k : Fin s // k ≠ j} = s-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ ≤ (Finset.univ : Finset ({k : Fin s // k ≠ j} → Fin h)).card := by
      apply Finset.card_le_card_of_injOn (fun n k => n k.val)
      · intro n _
        exact Finset.mem_univ _
      · intro n hn m hm he
        have hi := congrFun he ⟨i, hij⟩
        have hn' := (Finset.mem_filter.mp hn).2
        have hm' := (Finset.mem_filter.mp hm).2
        funext k
        by_cases hk : k=j
        · subst k
          unfold qt at hn' hm'
          have hci : (n i:ℕ)=(m i:ℕ) := congrArg Fin.val hi
          apply Fin.ext
          omega
        · exact congrFun he ⟨k, hk⟩
    _ = _ := by simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hc]
theorem qiK {s h : ℕ} (a : Fin s → ℤ) :
    (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (qt a n)).card ≤
      s^2 * h^(s-1) := by
  classical
  let pairs : Finset (Fin s × Fin s) := Finset.univ.filter fun ij => ij.1 ≠ ij.2
  let bad (ij : Fin s × Fin s) := Finset.univ.filter fun n : Fin s → Fin h =>
    qt a n ij.1 = qt a n ij.2
  have hsub : (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (qt a n)) ⊆
      pairs.biUnion bad := by
    intro n hn
    have hni := (Finset.mem_filter.mp hn).2
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨i, j, he, hne⟩ := hni
    exact Finset.mem_biUnion.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  calc
    _ ≤ (pairs.biUnion bad).card := Finset.card_le_card hsub
    _ ≤ pairs.card * h^(s-1) := Finset.card_biUnion_le_card_mul pairs bad _ fun ij hij =>
      qjG a (Finset.mem_filter.mp hij).2
    _ ≤ s^2 * h^(s-1) := Nat.mul_le_mul_right _ (by
      calc
        pairs.card ≤ (Finset.univ : Finset (Fin s × Fin s)).card := Finset.card_filter_le _ _
        _ = _ := by simp [pow_two])
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def qh {s h : ℕ} (a : Fin s → ℤ) : Finset (Fin s → Fin h) :=
  Finset.univ.filter fun n => Function.Injective (qt a n)
noncomputable def qb3 {s h : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  (∑ n : Fin s → Fin h, qao (qt a n) q)/(h:ℝ)^s
noncomputable def q9 {s h : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  (∑ n ∈ qh (h:=h) a, qao (qt a n) q)/(h:ℝ)^s
noncomputable def qaH {s h : ℕ} (a : Fin s → ℤ) : ℝ :=
  (∑ n ∈ qh (h:=h) a, qay (Finset.univ.image (qt a n)))/(h:ℝ)^s
theorem qlt {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (n : Fin s → Fin h) :
    qao (qt a n) q = qO (qa5 (q:=q) a n) := by
  rw [qcq]
  congr 1
  funext i
  simp only [qt, qa5, Int.cast_add, Int.cast_natCast]
theorem qfs {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    (1-(q:ℝ)/h)^s ≤ qb3 (h:=h) a q ∧
    qb3 (h:=h) a q ≤ (1+(q:ℝ)/h)^s := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hqR : (q:ℝ)≤h := by exact_mod_cast hq
  have hdiv : ((h/q:ℕ):ℝ)*(q:ℝ) ≤ h := by exact_mod_cast Nat.div_mul_le_self h q
  have hfloor : (h:ℝ)-(q:ℝ) ≤ ((h/q:ℕ):ℝ)*(q:ℝ) := by
    have he := Nat.div_add_mod h q
    have hm := Nat.mod_lt h (NeZero.pos q)
    have heR : ((h/q:ℕ):ℝ)*(q:ℝ)+(h%q:ℕ)=h := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using he : h/q*q+h%q=h)
    have hmR : ((h%q:ℕ):ℝ)<q := by exact_mod_cast hm
    linarith
  have hb := qka (h:=h) a (@qO s q _) qcr
  rw [qje] at hb
  simp_rw [← qlt] at hb
  unfold qb3
  constructor
  · calc
      _ = ((h:ℝ)-(q:ℝ))^s/(h:ℝ)^s := by rw [← div_pow]; congr 1; field_simp
      _ ≤ (((h/q:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr hqR) hfloor s) (by positivity)
      _ ≤ _ := by rw [mul_pow]; exact div_le_div_of_nonneg_right hb.1 (by positivity)
  · calc
      _ ≤ (((h/q+1:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := by
        rw [mul_pow]; exact div_le_div_of_nonneg_right hb.2 (by positivity)
      _ ≤ ((h:ℝ)+(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by push_cast; nlinarith) s) (by positivity)
      _ = _ := by rw [← div_pow]; congr 1; field_simp
theorem qd9 {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    q9 (h:=h) a q ≤ qb3 (h:=h) a q := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n _ _
  rw [qcq]
  exact qcr _
theorem qgf {s h q : ℕ} [NeZero q] (hh : 0<h)
    (a : Fin s → ℤ) :
    qb3 (h:=h) a q - q9 (h:=h) a q ≤
      (s:ℝ)^2*(q:ℝ)^s/(h:ℝ) := by
  classical
  by_cases hs : s=0
  · subst s
    have hall : qh (h:=h) a = Finset.univ := by
      ext n
      simp [qh, Function.Injective]
    simp [qb3, q9, hall]
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin s → Fin h))
    (fun n => Function.Injective (qt a n)) (fun n => qao (qt a n) q)
  have hb : (∑ n ∈ Finset.univ.filter (fun n : Fin s → Fin h => ¬Function.Injective (qt a n)),
      qao (qt a n) q) ≤ (s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s := by
    calc
      _ ≤ ((Finset.univ.filter fun n : Fin s → Fin h => ¬Function.Injective (qt a n)).card:ℝ) *
          (q:ℝ)^s := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ ((q:ℝ)^s) (fun n _ => by
          rw [qcq]
          exact qjD _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast qiK (h:=h) a)
        (by positivity)
  unfold qb3 q9 qh
  rw [← sub_div]
  calc
    _ ≤ ((s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s)/(h:ℝ)^s := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hsum]
    _ = _ := by
      have hp : (h:ℝ)^s=(h:ℝ)^(s-1)*(h:ℝ) := by
        rw [← pow_succ]; congr 1; omega
      rw [hp]
      field_simp
noncomputable def qbo (s h q : ℕ) : ℝ :=
  |(1-(q:ℝ)/h)^s-1| + |(1+(q:ℝ)/h)^s-1| + (s:ℝ)^2*(q:ℝ)^s/h
theorem qgY {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    |q9 (h:=h) a q-1| ≤ qbo s h q := by
  have hb := qfs hh hq a
  have hd := qgf (q:=q) hh a
  have hle := qd9 (q:=q) (h:=h) a
  unfold qbo
  apply abs_le.mpr
  constructor
  · have hl := neg_abs_le ((1-(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1+(q:ℝ)/h)^s-1)
    linarith
  · have hu := le_abs_self ((1+(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1-(q:ℝ)/h)^s-1)
    have hnn : 0≤(s:ℝ)^2*(q:ℝ)^s/h := by positivity
    linarith
noncomputable def qG (s M y : ℕ) : ℝ :=
  2*((s:ℝ)^2*(2:ℝ)^s)/(y:ℝ) +
    4*(s:ℝ)*((s*(s-1):ℕ):ℝ)*Real.log M/((y:ℝ)*Real.log y)
theorem qhR {s M y : ℕ} (a : Fin s → ℤ)
    (ha : Function.Injective a) (hy : 1<y)
    (hd : ∀ i j, (a i-a j).natAbs ≤ M) :
    qbe (Finset.univ.image a) y ≤ qG s M y := by
  have hc : (Finset.univ.image a).card=s := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  have hb := qlr (Finset.univ.image a) (M:=M) (by
    intro x hx z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    exact hd i j)
  rw [hc] at hb
  have hl : Real.log (qaz (Finset.univ.image a)) ≤
      ((s*(s-1):ℕ):ℝ)*Real.log M := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast qgu (Finset.univ.image a)
    · exact_mod_cast hb
  unfold qbe qG
  rw [hc]
  apply add_le_add le_rfl
  calc
    _ ≤ 4*(s:ℝ)*(((s*(s-1):ℕ):ℝ)*Real.log M)/((y:ℝ)*Real.log y) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity))
        (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))))
    _ = _ := by ring
def qcs {s h : ℕ} (a : Fin s → ℤ) (M : ℕ) : Prop :=
  ∀ (n : Fin s → Fin h) i j, (qt a n i-qt a n j).natAbs ≤ M
theorem qgI (s : ℕ) {M y : ℕ} (hM : 0<M) (hy : 1<y) :
    0 ≤ qG s M y := by
  have hlogM : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlogy : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))
  unfold qG
  positivity
theorem qgZ {s h M y : ℕ} (a : Fin s → ℤ)
    (hy : 1<y) (hys : 2*s≤y) (hd : qcs (h:=h) a M)
    (hB : qG s M y≤1) :
    |qaH (h:=h) a-q9 (h:=h) a (primorial y)| ≤
      2*qG s M y*q9 (h:=h) a (primorial y) := by
  classical
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hpoint (n : Fin s → Fin h) (hn : n∈qh a) :
      |qay (Finset.univ.image (qt a n))-qao (qt a n) (primorial y)| ≤
      2*qG s M y*qao (qt a n) (primorial y) := by
    have hi := (Finset.mem_filter.mp hn).2
    have hc : (Finset.univ.image (qt a n)).card=s := by
      rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
    have hut := qhR (qt a n) hi hy (hd n)
    have ht := ql9 (Finset.univ.image (qt a n)) hy (by simpa only [hc] using hys)
      (hut.trans hB)
    have hp : 0 ≤ qao (qt a n) (primorial y) := by
      rw [qcq]
      exact qcr _
    rw [qeO _ hy (by simpa only [hc] using hys),
      ← qjE _ hi, ← primorial_eq_prod_primesLE]
    calc
      _ = qao (qt a n) (primorial y)*|qcC (Finset.univ.image (qt a n)) y-1| := by
        rw [← mul_sub_one, abs_mul, abs_of_nonneg hp]
      _ ≤ qao (qt a n) (primorial y)*(2*qG s M y) :=
        mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hut (by norm_num))) hp
      _ = _ := by ring
  unfold qaH q9
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : 0≤(h:ℝ)^s), ← Finset.sum_sub_distrib]
  calc
    _ ≤ (∑ n ∈ qh a, |qay (Finset.univ.image (qt a n))-
        qao (qt a n) (primorial y)|)/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (∑ n ∈ qh a, 2*qG s M y*
        qao (qt a n) (primorial y))/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring
theorem qk3 {s h M y : ℕ} (a : Fin s → ℤ) (hh : 0<h)
    (hM : 0<M) (hy : 1<y) (hys : 2*s≤y) (hd : qcs (h:=h) a M)
    (hB : qG s M y≤1) (hq : primorial y≤h) :
    |qaH (h:=h) a-1| ≤ qbo s h (primorial y) +
      2*qG s M y*(1+(primorial y:ℝ)/h)^s := by
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hb := qgI s hM hy
  calc
    _ ≤ |qaH (h:=h) a-q9 (h:=h) a (primorial y)| +
        |q9 (h:=h) a (primorial y)-1| := abs_sub_le _ _ _
    _ ≤ 2*qG s M y*q9 (h:=h) a (primorial y) +
        qbo s h (primorial y) := add_le_add
      (qgZ a hy hys hd hB) (qgY hh hq a)
    _ ≤ 2*qG s M y*(1+(primorial y:ℝ)/h)^s +
        qbo s h (primorial y) := add_le_add_left
      (mul_le_mul_of_nonneg_left ((qd9 (q:=primorial y) a).trans (qfs hh hq a).2)
        (show 0 ≤ 2*qG s M y from mul_nonneg (by norm_num) hb)) _
    _ = _ := by ring
noncomputable def qaX (s : ℕ) : ℝ := 2*((s:ℝ)+1)*Real.log 4
noncomputable def q2 (s h : ℕ) : ℕ := ⌊Real.log h/qaX s⌋₊
theorem qbQ (s : ℕ) : 0<qaX s := by
  unfold qaX
  positivity
theorem qcz (s : ℕ) : Tendsto (q2 s) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const (qbQ s)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
theorem qhS (s : ℕ) :
    Tendsto (fun h : ℕ => (q2 s h:ℝ)/Real.log h) atTop (𝓝 (1/qaX s)) := by
  have hh := (tendsto_nat_floor_mul_div_atTop (a:=1/qaX s)
    (one_div_nonneg.mpr (qbQ s).le)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  simpa only [q2, one_div_mul_eq_div, Function.comp_def] using hh
theorem qg0 (s : ℕ) :
    Tendsto (fun h : ℕ => Real.log h/(q2 s h:ℝ)) atTop (𝓝 (qaX s)) := by
  simpa only [inv_div, one_div, inv_inv] using (qhS s).inv₀
    (one_div_ne_zero (qbQ s).ne')
theorem qe1 (s : ℕ) {h : ℕ} (hh : 0<h) :
    (primorial (q2 s h):ℝ)^(s+1) ≤ (h:ℝ)^(1/2:ℝ) := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hlog : 0≤Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hfloor := Nat.floor_le (div_nonneg hlog (qbQ s).le)
  change (q2 s h:ℝ) ≤ Real.log h/qaX s at hfloor
  have hb := (le_div_iff₀ (qbQ s)).mp hfloor
  have hexp : ((q2 s h:ℝ)*((s:ℝ)+1))*Real.log 4 ≤ Real.log h*(1/2) := by
    unfold qaX at hb
    nlinarith
  calc
    _ ≤ ((4:ℝ)^(q2 s h))^(s+1) := pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast primorial_le_four_pow (q2 s h)) _
    _ = Real.exp (((q2 s h:ℝ)*((s:ℝ)+1))*Real.log 4) := by
      rw [← pow_mul, ← Real.exp_log (by norm_num : (0:ℝ)<4), ← Real.exp_nat_mul]
      rw [Real.log_exp]
      push_cast
      congr 1
    _ ≤ _ := by rw [Real.rpow_def_of_pos hhR]; exact Real.exp_le_exp.mpr hexp
theorem qco (s r : ℕ) (hr : r ≤ s+1) :
    Tendsto (fun h : ℕ => (primorial (q2 s h):ℝ)^r/(h:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun h : ℕ => (h:ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun h => by positivity
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    calc
      _ ≤ (primorial (q2 s h):ℝ)^(s+1)/(h:ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast (Nat.pow_le_pow_right
          (primorial_pos (q2 s h)) hr)) hhR.le
      _ ≤ (h:ℝ)^(1/2:ℝ)/(h:ℝ) := div_le_div_of_nonneg_right
        (qe1 s (by omega)) hhR.le
      _ = _ := by
        have he := Real.rpow_sub hhR (1/2:ℝ) 1
        norm_num only [Real.rpow_one, show (1/2:ℝ)-1=-(1/2) by norm_num] at he
        exact he.symm
theorem qbH (s : ℕ) :
    Tendsto (fun h : ℕ => (primorial (q2 s h):ℝ)/(h:ℝ)) atTop (𝓝 0) := by
  simpa only [pow_one] using qco s 1 (by omega)
theorem qfG (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => Real.log (K*h:ℕ)/(q2 s h:ℝ)) atTop (𝓝 (qaX s)) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (qcz s)
  have hz : Tendsto (fun h : ℕ => Real.log (K:ℝ)/(q2 s h:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Pi.inv_apply, Function.comp_apply] using hy.inv_tendsto_atTop.const_mul (Real.log (K:ℝ))
  have ht := hz.add (qg0 s)
  rw [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hK.ne') (by exact_mod_cast (show h≠0 by omega)), add_div]
theorem qc9 (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => qG s (K*h) (q2 s h)) atTop (𝓝 0) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (qcz s)
  have hl := Real.tendsto_log_atTop.comp hy
  have ht := (hy.inv_tendsto_atTop.const_mul (2*((s:ℝ)^2*(2:ℝ)^s))).add
    (((qfG s hK).mul hl.inv_tendsto_atTop).const_mul
      (4*(s:ℝ)*((s*(s-1):ℕ):ℝ)))
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  ext h
  unfold qG
  simp only [div_eq_mul_inv, mul_inv_rev, Pi.inv_apply, Function.comp_apply]
  ring
theorem qiL (s : ℕ) :
    Tendsto (fun h : ℕ => qbo s h (primorial (q2 s h))) atTop (𝓝 0) := by
  have hq := qbH s
  have hl := ((tendsto_const_nhds (x:=(1:ℝ)).sub hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hu := ((tendsto_const_nhds (x:=(1:ℝ)).add hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hd := (qco s s (by omega)).const_mul ((s:ℝ)^2)
  have ht := (hl.abs.add hu.abs).add hd
  simp only [sub_zero, one_pow, sub_self, add_zero, abs_zero, mul_zero] at ht
  convert ht using 1
  ext h
  unfold qbo
  ring
noncomputable def qjH (s K h : ℕ) : ℝ :=
  qbo s h (primorial (q2 s h)) +
    2*qG s (K*h) (q2 s h)*
      (1+(primorial (q2 s h):ℝ)/h)^s
theorem qjI (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (qjH s K) atTop (𝓝 0) := by
  have ht := (qiL s).add
    (((qc9 s hK).const_mul 2).mul
      ((tendsto_const_nhds (x:=(1:ℝ))).add (qbH s) |>.pow s))
  simp only [mul_zero, zero_mul, add_zero] at ht
  exact ht
theorem qgg (s : ℕ) {K : ℕ} (hK : 0<K) :
    ∀ᶠ h : ℕ in atTop, ∀ a : Fin s → ℤ, qcs (h:=h) a (K*h) →
      |qaH (h:=h) a-1| ≤ qjH s K h := by
  have hB := (qc9 s hK).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hq := (qbH s).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 1, (qcz s).eventually_ge_atTop 2,
      (qcz s).eventually_ge_atTop (2*s), hB, hq] with h hh hy hys hB hq
  intro a hd
  have hqh : primorial (q2 s h) ≤ h := by
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    have ht := (div_lt_one hhR).mp hq
    exact_mod_cast ht.le
  exact qk3 a (by omega) (Nat.mul_pos hK (by omega)) (by omega) hys hd hB.le hqh
theorem qkb (s : ℕ) {K : ℕ} (hK : 0<K) {ε : ℝ} (hε : 0<ε) :
    ∃ h₀ : ℕ, ∀ h≥h₀, ∀ a : Fin s → ℤ, qcs (h:=h) a (K*h) →
      |qaH (h:=h) a-1| < ε := by
  have he := (qjI s hK).eventually (gt_mem_nhds hε)
  have hb := (qgg s hK).and he
  obtain ⟨h₀, hh₀⟩ := Filter.eventually_atTop.mp hb
  exact ⟨h₀, fun h hh a hd => ((hh₀ h hh).1 a hd).trans_lt (hh₀ h hh).2⟩
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
theorem qca (s : ℝ) (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n) := by
  positivity
theorem qg1 (s : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n) ≤ 1/(n:ℝ)^s := by
  by_cases hn : n≤1
  · interval_cases n <;> simp
    positivity
  have hnR : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos hnR
  have hpow : 0<(n:ℝ)^s := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ ≤ Real.log (n:ℝ)/((n:ℝ)^s*Real.log n) :=
      div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (mul_pos hpow hlog).le
    _ = _ := by field_simp
theorem qin (X : ℕ) {s : ℝ} (hs : 1<s) :
    (∑ p ∈ Nat.primesLE X, 1/(p:ℝ)^s) ≤ Real.log (riemannZeta (s:ℂ)).re := by
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n)) :=
    (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
      (qca s) (qg1 s)
  rw [log_riemannZeta_eq hs]
  calc
    _ = ∑ p ∈ Nat.primesLE X, ArithmeticFunction.vonMangoldt p / ((p:ℝ)^s*Real.log p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      have hl : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast hpP.one_lt)).ne'
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpP]
      field_simp
    _ ≤ _ := Summable.sum_le_tsum _ (fun n _ => qca s n) hsum
theorem qkc (X : ℕ) (hX : 2≤X) :
    (∑ p ∈ Nat.primesLE X, (1:ℝ)/p) ≤
      Real.exp 1*Real.log (riemannZeta ((1+1/Real.log X:ℝ):ℂ)).re := by
  have hlog : 0<Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hs : 1<(1:ℝ)+1/Real.log X := lt_add_of_pos_right 1 (one_div_pos.mpr hlog)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE X, Real.exp 1*(1/(p:ℝ)^(1+1/Real.log X)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      have hpX := (Nat.mem_primesLE.mp hp).1
      have hp0 : (0:ℝ)<p := by exact_mod_cast hpP.pos
      have hpY : Real.log (p:ℝ)≤Real.log (X:ℝ) := Real.log_le_log hp0 (by exact_mod_cast hpX)
      have he : (p:ℝ)^(1/Real.log X:ℝ) ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos hp0]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div] using (div_le_one hlog).mpr hpY
      calc
        _ = (p:ℝ)^(1/Real.log X:ℝ)/(p:ℝ)^(1+1/Real.log X:ℝ) := by
          rw [Real.rpow_add hp0, Real.rpow_one]
          field_simp
        _ ≤ Real.exp 1/(p:ℝ)^(1+1/Real.log X:ℝ) := div_le_div_of_nonneg_right he (by positivity)
        _ = _ := by ring
    _ = Real.exp 1*(∑ p ∈ Nat.primesLE X, 1/(p:ℝ)^(1+1/Real.log X:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (qin X hs) (Real.exp_pos _).le
theorem qc5 :
    ∀ᶠ X : ℕ in atTop, (∑ p ∈ Nat.primesLE X, (1:ℝ)/p) ≤
      Real.exp 1*(1+Real.log (Real.log X)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hx : Tendsto (fun X : ℕ => (1:ℝ)+1/Real.log X) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [one_div, add_zero, Pi.inv_apply, Function.comp_def] using tendsto_const_nhds.add hlog.inv_tendsto_atTop
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos (by exact_mod_cast hX)))
  have hζ : Tendsto (fun s : ℝ => Real.log (riemannZeta (s:ℂ)).re + Real.log (s-1))
      (𝓝[>] 1) (𝓝 0) :=
    log_riemannZeta_add_log_sub_isLittleO_ofReal.tendsto_zero_of_tendsto tendsto_const_nhds
  have hb := (hζ.comp hx).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hb, eventually_ge_atTop 2] with X hζX hX
  have he : Real.log (riemannZeta ((1+1/Real.log X:ℝ):ℂ)).re ≤ 1+Real.log (Real.log X) := by
    dsimp only [Function.comp_apply] at hζX
    rw [add_sub_cancel_left, one_div, Real.log_inv] at hζX
    simp only [one_div] at *
    linarith
  exact (qkc X hX).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
open Asymptotics
theorem qkE :
    ∃ c>0, ∃ ε>0, ∀ z : ℂ, z≠0 → ‖z‖<ε →
      ‖z*riemannZeta (1+z)-1‖ ≤ c*‖z‖ := by
  obtain ⟨c,hc,hbound⟩ := (differentiable_riemannZeta₁ 1).isBigO_sub.exists_pos
  have hb := hbound.bound
  rw [Metric.eventually_nhds_iff] at hb
  obtain ⟨ε,hε,hεb⟩ := hb
  refine ⟨c,hc,ε,hε,fun z hz hze => ?_⟩
  have hs : (1:ℂ)+z≠1 := by simpa using hz
  have ht := @hεb (1+z) (by simpa only [dist_eq_norm, add_sub_cancel_left] using hze)
  have he : z*riemannZeta (1+z) = riemannZeta₁ (1+z) := by
    rw [riemannZeta_eq_inv_sub_mul hs, add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  simpa only [riemannZeta₁_one, add_sub_cancel_left, he] using ht
theorem qhJ :
    ∃ c>0, ∃ ε>0, ∀ z : ℂ, z≠0 → ‖z‖<ε →
      ‖z*riemannZeta (1+z)-1‖ ≤ c*‖z‖ ∧
      1/2 ≤ ‖z*riemannZeta (1+z)‖ ∧ ‖z*riemannZeta (1+z)‖ ≤ 3/2 := by
  obtain ⟨c,hc,ε,hε,hb⟩ := qkE
  refine ⟨c,hc,min ε (1/(2*c)), lt_min hε (by positivity), fun z hz hze => ?_⟩
  have he := hb z hz (hze.trans_le (min_le_left _ _))
  have hzbound : c*‖z‖<1/2 := by
    have hh := hze.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0<2*c by positivity)).mp hh
    nlinarith
  refine ⟨he,?_,?_⟩
  · have ht := norm_sub_norm_le (1:ℂ) (z*riemannZeta (1+z))
    rw [norm_one, norm_sub_rev] at ht
    linarith
  · have ht := norm_sub_norm_le (z*riemannZeta (1+z)) (1:ℂ)
    rw [norm_one] at ht
    linarith
theorem qdS {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (B e : ι → ℝ) (hB : ∀ i∈s, 1≤B i)
    (hf : ∀ i∈s, ‖f i‖≤B i) (hg : ∀ i∈s, ‖g i‖≤B i)
    (he : ∀ i∈s, ‖f i-g i‖≤e i) :
    ‖(∏ i∈s, f i)-(∏ i∈s, g i)‖ ≤ (∏ i∈s, B i)*(∑ i∈s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hBas : ∀ i∈s, 1≤B i := fun i hi => hB i (Finset.mem_insert_of_mem hi)
    have hfs : ∀ i∈s, ‖f i‖≤B i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i∈s, ‖g i‖≤B i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hes : ∀ i∈s, ‖f i-g i‖≤e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hBa := hB a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hea := he a (Finset.mem_insert_self _ _)
    have hea0 : 0≤e a := (norm_nonneg _).trans hea
    have hprod0 : 0≤∏ i∈s, B i := Finset.prod_nonneg (fun i hi => (hBas i hi).trans' zero_le_one)
    have hsum0 : 0≤∑ i∈s, e i := Finset.sum_nonneg fun i hi => (norm_nonneg _).trans (hes i hi)
    have hprod : ‖∏ i∈s, f i‖≤∏ i∈s, B i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) hfs
    have hi := ih hBas hfs hgs hes
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = ‖(f a-g a)*(∏ i∈s, f i)+g a*((∏ i∈s, f i)-(∏ i∈s, g i))‖ := by congr 1; ring
      _ ≤ ‖f a-g a‖*‖∏ i∈s, f i‖+‖g a‖*‖(∏ i∈s, f i)-(∏ i∈s, g i)‖ := by
        simpa only [norm_mul] using norm_add_le ((f a-g a)*(∏ i∈s, f i)) (g a*((∏ i∈s, f i)-(∏ i∈s, g i)))
      _ ≤ e a*(∏ i∈s, B i)+B a*((∏ i∈s, B i)*(∑ i∈s, e i)) := by
        gcongr
      _ ≤ (B a*(∏ i∈s, B i))*(e a+∑ i∈s, e i) := by
        nlinarith [mul_nonneg hea0 hprod0, mul_nonneg (sub_nonneg.mpr hBa) (mul_nonneg hea0 hprod0)]
theorem qlu {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {B e : ℝ} (hB : 1≤B) (hf : ∀ i∈s, ‖f i‖≤B) (he : ∀ i∈s, ‖f i-1‖≤e) :
    ‖(∏ i∈s, f i)-1‖ ≤ B^s.card*(s.card*e) := by
  simpa only [Finset.prod_const, Finset.sum_const, nsmul_eq_mul, Finset.prod_const_one, one_pow]
    using qdS s f (fun _ => 1) (fun _ => B) (fun _ => e)
      (fun _ _ => hB) hf (by simpa using fun _ _ => hB) he
noncomputable def qaI {ι : Type*} (s : Finset ι) : Finset (Finset ι) := by
  classical
  exact s.powerset.erase ∅
theorem qey {ι : Type*} {s S : Finset ι} :
    S∈qaI s ↔ S.Nonempty ∧ S⊆s := by
  classical
  simp [qaI, Finset.nonempty_iff_ne_empty]
theorem qjJ {ι : Type*} {s : Finset ι} (hs : s.Nonempty) :
    (∑ S∈qaI s, (-1:ℤ)^S.card) = -1 := by
  classical
  have h := Finset.sum_erase_add s.powerset (fun S => (-1:ℤ)^S.card) (Finset.empty_mem_powerset s)
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hs] at h
  simpa only [Finset.card_empty, pow_zero, add_eq_zero_iff_eq_neg, qaI] using h
theorem qkw {ι : Type*} (s : Finset ι) (f : ι → ℤ) {c : ℂ} (hc : c≠0) :
    (∏ i∈s, c^(f i)) = c^(∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]
noncomputable def qc6 {ι : Type*} (s : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ S∈qaI s, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))
theorem qlV {a : ℂ} (ha : 1/2≤‖a‖) : ‖a⁻¹-1‖≤2*‖a-1‖ := by
  have ha0 : a≠0 := norm_pos_iff.mp (by linarith)
  have he : a⁻¹-1 = -(a-1)/a := by field_simp; ring
  rw [he, norm_div, norm_neg]
  apply (div_le_iff₀ (by linarith : 0<‖a‖)).mpr
  nlinarith [norm_nonneg (a-1)]
noncomputable def qz (u : ℝ) : ℂ := 1+Complex.I*(u:ℂ)
@[simp] theorem qlO (u : ℝ) : (qz u).re=1 := by simp [qz]
theorem qkx (u : ℝ) : ‖qz u‖≤1+|u| := by
  simpa [qz] using norm_add_le (1:ℂ) (Complex.I*(u:ℂ))
theorem qmN {ι : Type*} (S : Finset ι) (u : ι → ℝ) :
    (∑ i∈S, qz (u i)).re=(S.card:ℝ) := by simp
theorem qft {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (u : ι → ℝ) :
    1≤‖∑ i∈S, qz (u i)‖ := by
  have hc : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hr := Complex.re_le_norm (∑ i∈S, qz (u i))
  rw [qmN] at hr
  exact hc.trans hr
theorem qei {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (u : ι → ℝ) :
    ∑ i∈S, qz (u i)≠0 :=
  norm_pos_iff.mp ((by norm_num : (0:ℝ)<1).trans_le (qft hS u))
theorem qfu {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    {U : ℝ} (hu : ∀ i∈S, |u i|≤U) :
    ‖∑ i∈S, qz (u i)‖ ≤ S.card*(1+U) := by
  calc
    _ ≤ ∑ i∈S, ‖qz (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i∈S, (1+U) := Finset.sum_le_sum fun i hi => (qkx _).trans (by linarith [hu i hi])
    _ = _ := by simp; ring
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
theorem qiM {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {e : ℝ} (he : 0≤e) (hf : ∀ i∈s, ‖f i‖≤2) (hd : ∀ i∈s, ‖f i-1‖≤e) :
    ‖(∏ i∈s, f i)-1-(∑ i∈s, (f i-1))‖ ≤ (s.card:ℝ)^2*2^s.card*e^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i∈s, ‖f i‖≤2 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hds : ∀ i∈s, ‖f i-1‖≤e := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hda := hd a (Finset.mem_insert_self _ _)
    have hi := ih hfs hds
    have hsum : ‖∑ i∈s, (f i-1)‖≤ s.card*e := by
      exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum hds)
    have hcard : 0≤(s.card:ℝ) := Nat.cast_nonneg _
    have hpow : (1:ℝ)≤2^s.card := one_le_pow₀ (by norm_num)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ = ‖f a*((∏ i∈s, f i)-1-(∑ i∈s, (f i-1)))+(f a-1)*(∑ i∈s, (f i-1))‖ := by congr 1; ring
      _ ≤ ‖f a‖*‖(∏ i∈s, f i)-1-(∑ i∈s, (f i-1))‖+‖f a-1‖*‖∑ i∈s, (f i-1)‖ := by
        simpa only [norm_mul] using norm_add_le (f a*((∏ i∈s, f i)-1-(∑ i∈s, (f i-1)))) ((f a-1)*(∑ i∈s, (f i-1)))
      _ ≤ 2*((s.card:ℝ)^2*2^s.card*e^2)+e*(s.card*e) := by gcongr
      _ ≤ ((s.card:ℝ)+1)^2*(2^s.card*2)*e^2 := by
        have hcoeff : (s.card:ℝ)≤(4*(s.card:ℝ)+2)*2^s.card := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg e)]
theorem qdA {a : ℂ} {r : ℝ} (ha : ‖a‖≤r) :
    1-r≤‖1-a‖ := by
  have hh := norm_sub_norm_le (1:ℂ) a
  rw [norm_one] at hh
  linarith
theorem qb8 {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-1‖≤2*r := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := qdA ha
  have hn : 1-a≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simpa only [zpow_one, sub_sub_cancel_left, norm_neg] using ha.trans (by linarith : r≤2*r)
  · rw [zpow_neg_one]
    have hid : (1-a)⁻¹-1=a/(1-a) := by field_simp; ring
    rw [hid, norm_div]
    apply (div_le_iff₀ (by linarith : 0<‖1-a‖)).mpr
    nlinarith
theorem qjK {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-1+(σ:ℂ)*a‖≤2*r^2 := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := qdA ha
  have hn : 1-a≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simp; positivity
  · simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    have hid : (1-a)⁻¹-1+-a=a^2/(1-a) := by field_simp; ring
    rw [hid, norm_div, norm_pow]
    apply (div_le_iff₀ (by linarith : 0<‖1-a‖)).mpr
    nlinarith [sq_nonneg r, norm_nonneg a, sq_nonneg (r-‖a‖)]
noncomputable def qcb {ι : Type*} (s : Finset ι) (σ : ι → ℤ)
    (a : ι → ℂ) (ρ : ℝ) : ℂ :=
  (1+(ρ:ℂ)*(∑ i∈s, (σ i:ℂ)*a i))*(∏ i∈s, (1-a i)^(σ i))
theorem qiN {ι : Type*} (s : Finset ι) (σ : ι → ℤ)
    (a : ι → ℂ) {ρ r : ℝ} (hr0 : 0≤r) (hr : r≤1/2)
    (hρ0 : 0≤ρ) (hρ : ρ≤2) (hρ1 : |ρ-1|≤2*r)
    (hσ : ∀ i∈s, σ i=1 ∨ σ i= -1) (ha : ∀ i∈s, ‖a i‖≤r) :
    ‖qcb s σ a ρ-1‖ ≤
      ((1+s.card)*(4*(s.card:ℝ)^2*2^s.card+2*s.card)+2*s.card+2*(s.card:ℝ)^2)*r^2 := by
  classical
  let A : ℂ := ∑ i∈s, (σ i:ℂ)*a i
  let T : ℂ := ∏ i∈s, (1-a i)^(σ i)
  have hsig (i : ι) (hi : i∈s) : ‖(σ i:ℂ)‖=1 := by
    rcases hσ i hi with hh | hh <;> simp [hh]
  have hA : ‖A‖≤ s.card*r := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i∈s, r := Finset.sum_le_sum fun i hi => by rw [norm_mul, hsig i hi, one_mul]; exact ha i hi
      _ = _ := by simp
  have he : ‖T-1+A‖≤(4*(s.card:ℝ)^2*2^s.card+2*s.card)*r^2 := by
    have hf : ∀ i∈s, ‖(1-a i)^(σ i)‖≤2 := by
      intro i hi
      have hh := qb8 hr (ha i hi) (hσ i hi)
      have hn := norm_sub_norm_le ((1-a i)^(σ i)) (1:ℂ)
      rw [norm_one] at hn
      linarith
    have hprod := qiM s (fun i => (1-a i)^(σ i)) (by positivity : 0≤2*r)
      hf (fun i hi => qb8 hr (ha i hi) (hσ i hi))
    have herr : ‖∑ i∈s, ((1-a i)^(σ i)-1+(σ i:ℂ)*a i)‖≤ s.card*(2*r^2) := by
      exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (fun i hi => qjK hr (ha i hi) (hσ i hi)))
    have hid : T-1+A = (T-1-(∑ i∈s, ((1-a i)^(σ i)-1)))+
        (∑ i∈s, ((1-a i)^(σ i)-1+(σ i:ℂ)*a i)) := by
      rw [Finset.sum_add_distrib]; dsimp [A]; ring
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add hprod herr).trans (by ring_nf; rfl))
  have hP : ‖1+(ρ:ℂ)*A‖≤1+s.card := by
    calc
      _ ≤ 1+ρ*‖A‖ := by simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using norm_add_le (1:ℂ) ((ρ:ℂ)*A)
      _ ≤ 1+2*(s.card*r) := by gcongr
      _ ≤ 1+s.card := by nlinarith [Nat.cast_nonneg (α:=ℝ) s.card]
  have hid : qcb s σ a ρ-1 =
      (1+(ρ:ℂ)*A)*(T-1+A)+((ρ:ℂ)-1)*A-(ρ:ℂ)*A^2 := by dsimp [qcb, A, T]; ring
  rw [hid]
  calc
    _ ≤ ‖1+(ρ:ℂ)*A‖*‖T-1+A‖+‖(ρ:ℂ)-1‖*‖A‖+‖(ρ:ℂ)‖*‖A‖^2 := by
      have h1 := norm_sub_le ((1+(ρ:ℂ)*A)*(T-1+A)+((ρ:ℂ)-1)*A) ((ρ:ℂ)*A^2)
      have h2 := norm_add_le ((1+(ρ:ℂ)*A)*(T-1+A)) (((ρ:ℂ)-1)*A)
      simp only [norm_mul, norm_pow] at h1 h2
      linarith

    _ ≤ (1+s.card)*((4*(s.card:ℝ)^2*2^s.card+2*s.card)*r^2)+(2*r)*(s.card*r)+2*(s.card*r)^2 := by
      have hρn : ‖(ρ:ℂ)‖≤2 := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ
      have hρd : ‖(ρ:ℂ)-1‖≤2*r := by exact_mod_cast hρ1
      gcongr
    _ = _ := by ring
theorem qgh {z : ℂ} (hz : z.re≤0) :
    ‖Complex.exp z-1‖ ≤ ‖z‖ := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*z))
      (Complex.exp ((t:ℂ)*z)*z) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp
  have hb (t : ℝ) (ht : t∈Set.Ico (0:ℝ) 1) :
      ‖Complex.exp ((t:ℂ)*z)*z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_exp]
    have he : Real.exp ((t:ℂ)*z).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    exact mul_le_of_le_one_left (norm_nonneg z) he
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero] using norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hd t).hasDerivWithinAt) hb
noncomputable def qr {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) : ℂ :=
  Complex.exp (-(Real.log p : ℂ)*(∑ i∈S, z i))
theorem qgw {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖qr p z S‖ ≤ 1 := by
  rw [qr, Complex.norm_exp, Real.exp_le_one_iff]
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hs : 0≤∑ i∈S, (z i).re := Finset.sum_nonneg hz
  simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
    using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hs
theorem qgx {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖qr p z S-1‖ ≤ Real.log p*(∑ i∈S, ‖z i‖) := by
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hexp : (-(Real.log p : ℂ)*(∑ i∈S, z i)).re≤0 := by
    have hs : 0≤∑ i∈S, (z i).re := Finset.sum_nonneg hz
    simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
      using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hs
  calc
    _ ≤ ‖-(Real.log p : ℂ)*(∑ i∈S, z i)‖ := qgh hexp
    _ = Real.log p*‖∑ i∈S, z i‖ := by rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hlog
@[simp] theorem qcD {ι : Type*} (p : ℕ) (S : Finset ι) :
    qr p (fun _ => (0:ℂ)) S = 1 := by simp [qr]
noncomputable def qbt {ι : Type*} (p δ : ℕ) (A : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  1+((p:ℂ)-δ)⁻¹*(∑ S∈A, (-1:ℂ)^S.card*qr p z S)
noncomputable def qa1 {ι : Type*} (p δ : ℕ) (A B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  qbt p δ A z * ∏ S∈B, (1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card)
theorem qdB (n : ℕ) : (-1:ℤ)^n=1 ∨ (-1:ℤ)^n= -1 := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow
theorem qby {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖(p:ℂ)⁻¹*qr p z S‖ ≤ (p:ℝ)⁻¹ := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_of_le_one_right (by positivity) (qgw hp z S hz)
theorem qe2 {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1) :
    0<(p:ℝ)-δ ∧ ((p:ℝ)-δ)⁻¹≤2*(p:ℝ)⁻¹ ∧
      0≤(p:ℝ)/((p:ℝ)-δ) ∧ (p:ℝ)/((p:ℝ)-δ)≤2 ∧
        |(p:ℝ)/((p:ℝ)-δ)-1|≤2*(p:ℝ)⁻¹ := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hdR : (δ:ℝ)≤1 := by exact_mod_cast hδ
  have hd0 : (0:ℝ)≤δ := by positivity
  have hp0 : (0:ℝ)<p := by linarith
  have hpd : (0:ℝ)<p-δ := by linarith
  refine ⟨hpd,?_,by positivity,?_,?_⟩
  · rw [inv_eq_one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hpd hp0).mpr
    linarith
  · exact (div_le_iff₀ hpd).mpr (by linarith)
  · have hid : (p:ℝ)/(p-δ)-1 = δ/(p-δ) := by field_simp; ring
    rw [hid, abs_of_nonneg (by positivity)]
    change (δ:ℝ)/((p:ℝ)-δ)≤2/(p:ℝ)
    apply (div_le_div_iff₀ hpd hp0).mpr
    nlinarith
theorem qmq {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) :
    qa1 p δ A A z = qcb A
      (fun S => (-1:ℤ)^S.card) (fun S => (p:ℂ)⁻¹*qr p z S)
      ((p:ℝ)/((p:ℝ)-δ)) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hpd : (p:ℂ)-(δ:ℂ)≠0 := by exact_mod_cast (qe2 hp hδ).1.ne'
  unfold qa1 qbt qcb
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  field_simp
theorem qg2 {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈A, ∀ i∈S, 0≤(z i).re) :
    ‖qa1 p δ A A z-1‖ ≤
      ((1+A.card)*(4*(A.card:ℝ)^2*2^A.card+2*A.card)+2*A.card+2*(A.card:ℝ)^2)/(p:ℝ)^2 := by
  rw [qmq hp hδ]
  have hd := qe2 hp hδ
  have hr : (p:ℝ)⁻¹≤1/2 := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0<p)) (by norm_num)).mpr
    have hh : (2:ℝ)≤p := by exact_mod_cast hp
    linarith
  simpa only [inv_pow, div_eq_mul_inv] using
    qiN A (fun S => (-1:ℤ)^S.card)
      (fun S => (p:ℂ)⁻¹*qr p z S) (by positivity) hr hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
      (fun S _ => qdB S.card)
      (fun S hS => qby (by omega) z S (hz S hS))
theorem qk4 {a b : ℂ} (ha : ‖a‖≤1/2) (hb : ‖b‖≤1/2)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-(1-b)^σ‖≤4*‖a-b‖ := by
  have hla := qdA ha
  have hlb := qdA hb
  have hna : 1-a≠0 := norm_pos_iff.mp (by linarith)
  have hnb : 1-b≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simp only [zpow_one]
    have hid : (1-a)-(1-b)= -(a-b) := by ring
    rw [hid, norm_neg]
    nlinarith [norm_nonneg (a-b)]
  · simp only [zpow_neg_one]
    have hid : (1-a)⁻¹-(1-b)⁻¹=(a-b)/((1-a)*(1-b)) := by field_simp; ring
    rw [hid, norm_div, norm_mul]
    have hp : 1/4≤‖1-a‖*‖1-b‖ := by nlinarith
    apply (div_le_iff₀ (by positivity : 0<‖1-a‖*‖1-b‖)).mpr
    nlinarith [norm_nonneg (a-b)]
theorem qcU {p : ℕ} (hp : 2≤p) : (p:ℝ)⁻¹≤1/2 := by
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0<p)) (by norm_num)).mpr
  have hh : (2:ℝ)≤p := by exact_mod_cast hp
  linarith
theorem qk5 {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈A, ∀ i∈S, 0≤(z i).re) :
    ‖qbt p δ A z‖ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹) := by
  have hsum : ‖∑ S∈A, (-1:ℂ)^S.card*qr p z S‖≤A.card := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _S∈A, (1:ℝ) := Finset.sum_le_sum fun S hS => by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          using qgw (by omega) z S (hz S hS)
      _ = _ := by simp
  have hd := qe2 hp hδ
  have hn : ‖((p:ℂ)-δ)⁻¹‖≤2*(p:ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast δ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
    exact hd.2.1
  calc
    _ ≤ 1+‖((p:ℂ)-δ)⁻¹‖*‖∑ S∈A, (-1:ℂ)^S.card*qr p z S‖ := by
      simpa only [qbt, norm_one, norm_mul] using norm_add_le (1:ℂ)
        (((p:ℂ)-δ)⁻¹*(∑ S∈A, (-1:ℂ)^S.card*qr p z S))
    _ ≤ 1+(2*(p:ℝ)⁻¹)*A.card := by gcongr
    _ = 2*A.card*(p:ℝ)⁻¹+1 := by ring
    _ ≤ _ := Real.add_one_le_exp _
theorem qk6 {ι : Type*} {p : ℕ} (hp : 2≤p)
    (B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈B, ∀ i∈S, 0≤(z i).re) :
    ‖∏ S∈B, (1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card)‖ ≤
      Real.exp (2*B.card*(p:ℝ)⁻¹) := by
  have hb (S : Finset ι) (hS : S∈B) :
      ‖(1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    have hh := qb8 (qcU hp)
      (qby (by omega) z S (hz S hS)) (qdB S.card)
    have hn := norm_sub_norm_le ((1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card)) (1:ℂ)
    rw [norm_one] at hn
    exact (show _ ≤ 2*(p:ℝ)⁻¹+1 by linarith).trans (Real.add_one_le_exp _)
  calc
    _ ≤ ∏ _S∈B, Real.exp (2*(p:ℝ)⁻¹) := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hb
    _ = Real.exp (2*B.card*(p:ℝ)⁻¹) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
theorem qk7 {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖qa1 p δ A B z‖ ≤ Real.exp (2*(A.card+B.card)*(p:ℝ)⁻¹) := by
  rw [qa1, norm_mul]
  calc
    _ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹)*Real.exp (2*B.card*(p:ℝ)⁻¹) :=
      mul_le_mul (qk5 hp hδ A z (fun _ _ i _ => hz i))
        (qk6 hp B z (fun _ _ i _ => hz i)) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
theorem qkd {ι : Type*} [Fintype ι] {p δ : ℕ}
    (hp : 2≤p) (hδ : δ≤1) (A : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖qbt p δ A z-qbt p δ A (fun _ => 0)‖ ≤
      2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖) := by
  classical
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hs (S : Finset ι) : ∑ i∈S, ‖z i‖≤∑ i, ‖z i‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  have he (S : Finset ι) : ‖qr p z S-1‖≤Real.log p*(∑ i, ‖z i‖) :=
    (qgx (by omega) z S (fun i _ => hz i)).trans (mul_le_mul_of_nonneg_left (hs S) hlog)
  have hd := qe2 hp hδ
  have hn : ‖((p:ℂ)-δ)⁻¹‖≤2*(p:ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast δ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
    exact hd.2.1
  have hid : qbt p δ A z-qbt p δ A (fun _ => 0) =
      ((p:ℂ)-δ)⁻¹*∑ S∈A, (-1:ℂ)^S.card*(qr p z S-1) := by
    simp only [qbt, qcD, mul_one, Finset.sum_sub_distrib, mul_sub]
    ring
  rw [hid, norm_mul]
  have hsum : ‖∑ S∈A, (-1:ℂ)^S.card*(qr p z S-1)‖≤
      A.card*(Real.log p*(∑ i, ‖z i‖)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _S∈A, Real.log p*(∑ i, ‖z i‖) := Finset.sum_le_sum fun S _ => by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using he S
      _ = _ := by simp
  calc
    _ ≤ (2*(p:ℝ)⁻¹)*(A.card*(Real.log p*(∑ i, ‖z i‖))) := by gcongr
    _ = _ := by ring
theorem qke {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : 2≤p) (B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖(∏ S∈B, (1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card)) -
      (∏ S∈B, (1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card))‖ ≤
      Real.exp (2*B.card*(p:ℝ)⁻¹)*(4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
  classical
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hs (S : Finset ι) : ∑ i∈S, ‖z i‖≤∑ i, ‖z i‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  have he (S : Finset ι) : ‖qr p z S-1‖≤Real.log p*(∑ i, ‖z i‖) :=
    (qgx (by omega) z S (fun i _ => hz i)).trans (mul_le_mul_of_nonneg_left (hs S) hlog)
  have hbn (w : ι → ℂ) (hw : ∀ i, 0≤(w i).re) (S : Finset ι) :
      ‖(1-(p:ℂ)⁻¹*qr p w S)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    have hh := qb8 (qcU hp)
      (qby (by omega) w S (fun i _ => hw i)) (qdB S.card)
    have hn := norm_sub_norm_le ((1-(p:ℂ)⁻¹*qr p w S)^((-1:ℤ)^S.card)) (1:ℂ)
    rw [norm_one] at hn
    exact (show _ ≤ 2*(p:ℝ)⁻¹+1 by linarith).trans (Real.add_one_le_exp _)
  have hg (S : Finset ι) : ‖(1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    simpa only [qcD, mul_one] using hbn (fun _ => 0) (by simp) S
  have hd (S : Finset ι) :
      ‖(1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card)-(1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card)‖≤
        4*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖) := by
    have ha := (qby (by omega : 1≤p) z S (fun i _ => hz i)).trans (qcU hp)
    have hb : ‖(p:ℂ)⁻¹‖≤1/2 := by simpa only [norm_inv, Complex.norm_natCast] using qcU hp
    calc
      _ ≤ 4*‖(p:ℂ)⁻¹*qr p z S-(p:ℂ)⁻¹‖ := qk4 ha hb (qdB S.card)
      _ = 4*(p:ℝ)⁻¹*‖qr p z S-1‖ := by
        rw [← mul_sub_one, norm_mul, norm_inv, Complex.norm_natCast, mul_assoc]
      _ ≤ 4*(p:ℝ)⁻¹*(Real.log p*(∑ i, ‖z i‖)) := mul_le_mul_of_nonneg_left (he S) (by positivity)
      _ = _ := by ring
  have hh := qdS B
    (fun S => (1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card))
    (fun S => (1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card))
    (fun _ => Real.exp (2*(p:ℝ)⁻¹)) (fun _ => 4*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))
    (fun _ _ => Real.one_le_exp (by positivity)) (fun S _ => hbn z hz S)
    (fun S _ => hg S) (fun S _ => hd S)
  have ht : ∏ _S∈B, Real.exp (2*(p:ℝ)⁻¹)=Real.exp (2*B.card*(p:ℝ)⁻¹) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [ht] at hh
  convert hh using 1
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring
theorem qkf {ι : Type*} [Fintype ι] {p δ : ℕ}
    (hp : 2≤p) (hδ : δ≤1) (A B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖qa1 p δ A B z-qa1 p δ A B (fun _ => 0)‖ ≤
      Real.exp (2*(A.card+B.card)*(p:ℝ)⁻¹)*
        ((2*A.card+4*B.card)*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
  let T := fun w : ι → ℂ => ∏ S∈B, (1-(p:ℂ)⁻¹*qr p w S)^((-1:ℤ)^S.card)
  have hT := qk6 hp B z (fun _ _ i _ => hz i)
  have hdT : ‖T z-T (fun _ => 0)‖≤
      Real.exp (2*B.card*(p:ℝ)⁻¹)*(4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
    simpa only [T, qcD, mul_one] using qke hp B z hz
  have hp0 := qk5 hp hδ A (fun _ => 0) (by simp)
  have hPd := qkd hp hδ A z hz
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hAe : 1≤Real.exp (2*A.card*(p:ℝ)⁻¹) := Real.one_le_exp (by positivity)
  have hid : qa1 p δ A B z-qa1 p δ A B (fun _ => 0) =
      (qbt p δ A z-qbt p δ A (fun _ => 0))*T z +
        qbt p δ A (fun _ => 0)*(T z-T (fun _ => 0)) := by dsimp [qa1, T]; ring
  rw [hid]
  calc
    _ ≤ ‖qbt p δ A z-qbt p δ A (fun _ => 0)‖*‖T z‖ +
        ‖qbt p δ A (fun _ => 0)‖*‖T z-T (fun _ => 0)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((qbt p δ A z-qbt p δ A (fun _ => 0))*T z)
        (qbt p δ A (fun _ => 0)*(T z-T (fun _ => 0)))
    _ ≤ (2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹)+
        Real.exp (2*A.card*(p:ℝ)⁻¹)*(Real.exp (2*B.card*(p:ℝ)⁻¹)*
          (4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))) := by gcongr
    _ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹)*
        ((2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹))+
        Real.exp (2*A.card*(p:ℝ)⁻¹)*(Real.exp (2*B.card*(p:ℝ)⁻¹)*
          (4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))) := by
      have hnn : 0 ≤ (2*(A.card:ℝ)*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹) := by positivity
      exact add_le_add (le_mul_of_one_le_left hnn hAe) le_rfl
    _ = _ := by
      rw [show 2*((A.card:ℝ)+B.card)*(p:ℝ)⁻¹=2*A.card*(p:ℝ)⁻¹+2*B.card*(p:ℝ)⁻¹ by ring,
        Real.exp_add]
      ring
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
noncomputable def qx {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) : Finset (Finset ι) := by
  classical
  exact R.biUnion fun r => qaI (Finset.univ.filter fun i => b i=r)
theorem qcJ {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (S : Finset ι) :
    S∈qx b R ↔ S.Nonempty ∧ ∃ r∈R, ∀ i∈S, b i=r := by
  classical
  simp only [qx, Finset.mem_biUnion, qey]
  constructor
  · rintro ⟨r,hr,hS,hsub⟩
    exact ⟨hS,r,hr,fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩
  · rintro ⟨hS,r,hr,hsub⟩
    exact ⟨r,hr,hS,fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub i hi⟩⟩
theorem qdn {ι α : Type*} [Fintype ι] (b : ι → α)
    {r s : α} (hrs : r≠s) :
    Disjoint (qaI (Finset.univ.filter fun i => b i=r))
      (qaI (Finset.univ.filter fun i => b i=s)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hSr hSs
  rcases qey.mp hSr with ⟨hS,hR⟩
  have hT := (qey.mp hSs).2
  rcases hS with ⟨i,hi⟩
  exact hrs ((Finset.mem_filter.mp (hR hi)).2.symm.trans (Finset.mem_filter.mp (hT hi)).2)
theorem qcL {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    (∑ S∈qx b R, (-1:ℤ)^S.card) = -(R.card:ℤ) := by
  classical
  rw [qx, Finset.sum_biUnion]
  · have hs (r : α) (hr : r∈R) : (Finset.univ.filter fun i => b i=r).Nonempty := by
      rcases hR r hr with ⟨i,hi⟩
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    calc
      _ = ∑ _r∈R, (-1:ℤ) := Finset.sum_congr rfl (fun r hr => qjJ (hs r hr))
      _ = _ := by simp
  · intro r _ s _ hrs
    exact qdn b hrs
theorem qH {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α)
    (S : Finset ι) :
    S∈qx b (Finset.univ.image b) ↔
      S.Nonempty ∧ ∀ i∈S, ∀ j∈S, b i=b j := by
  classical
  rw [qcJ]
  constructor
  · rintro ⟨hS,r,_,hb⟩
    exact ⟨hS,fun i hi j hj => (hb i hi).trans (hb j hj).symm⟩
  · rintro ⟨hS,hb⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩,b i,Finset.mem_image_of_mem _ (Finset.mem_univ _),fun j hj => hb j hj i hi⟩
theorem qjL {ι α : Type*} [Fintype ι]
    (p δ : ℕ) (b : ι → α) (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    qbt p δ (qx b R) (fun _ => 0) =
      1-((p:ℂ)-δ)⁻¹*(R.card:ℂ) := by
  have hs : (∑ S∈qx b R, (-1:ℂ)^S.card) = -(R.card:ℂ) := by
    exact_mod_cast qcL b R hR
  simp only [qbt, qcD, mul_one, hs]
  ring
theorem qel {ι α β : Type*} [Fintype ι]
    (p δ : ℕ) (b : ι → α) (R : Finset α) (c : ι → β) (T : Finset β)
    (hR : ∀ r∈R, ∃ i, b i=r) (hT : ∀ t∈T, ∃ i, c i=t)
    (hp : 1-(p:ℂ)⁻¹≠0) :
    qa1 p δ (qx b R) (qx c T) (fun _ => 0) =
      (1-((p:ℂ)-δ)⁻¹*(R.card:ℂ))*(1-(p:ℂ)⁻¹)^(-(T.card:ℤ)) := by
  rw [qa1, qjL p δ b R hR]
  simp only [qcD, mul_one]
  rw [qkw _ _ hp, qcL c T hT]
noncomputable def qJ {ι : Type*} [Fintype ι] (b : ι → ℤ) : Finset (Finset ι) :=
  qx b (Finset.univ.image b)
noncomputable def qam {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) : Finset (Finset ι) :=
  qx (fun i => b i%(p:ℤ)) (Finset.univ.image fun i => b i%(p:ℤ))
noncomputable def qS {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) : Finset (Finset ι) :=
  qx (fun i => b i%(p:ℤ)) ((Finset.univ.image fun i => b i%(p:ℤ)).erase (a%(p:ℤ)))
theorem qcm {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) (S : Finset ι) :
    S∈qS b p a ↔ S.Nonempty ∧
      (∀ i∈S, ∀ j∈S, b i%(p:ℤ)=b j%(p:ℤ)) ∧ ∀ i∈S, b i%(p:ℤ)≠a%(p:ℤ) := by
  rw [qS, qcJ]
  constructor
  · rintro ⟨hS,r,hr,hb⟩
    exact ⟨hS,(fun i hi j hj => (hb i hi).trans (hb j hj).symm),fun i hi =>
      (hb i hi) ▸ (Finset.mem_erase.mp hr).1⟩
  · rintro ⟨hS,hb,ha⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩, b i%(p:ℤ),Finset.mem_erase.mpr ⟨ha i hi,
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,fun j hj => hb j hj i hi⟩
theorem qdT {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ)
    (h : ∀ i j, b i%(p:ℤ)=b j%(p:ℤ) → b i=b j) : qam b p=qJ b := by
  apply Finset.ext
  intro S
  constructor
  · intro hs
    rcases (qH (fun i => b i%(p:ℤ)) S).mp hs with ⟨hn,he⟩
    exact (qH b S).mpr ⟨hn,fun i hi j hj => h i j (he i hi j hj)⟩
  · intro hs
    rcases (qH b S).mp hs with ⟨hn,he⟩
    exact (qH (fun i => b i%(p:ℤ)) S).mpr
      ⟨hn,fun i hi j hj => congrArg (fun a => a%(p:ℤ)) (he i hi j hj)⟩
theorem qfH {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ)
    (h : ∀ i j, b i%(p:ℤ)=b j%(p:ℤ) → b i=b j) (ha : ∀ i, b i%(p:ℤ)≠a%(p:ℤ)) :
    qS b p a=qJ b := by
  rw [qS]
  have hn : a%(p:ℤ)∉(Finset.univ.image fun i => b i%(p:ℤ)) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨i,_,hi⟩
    exact ha i hi
  rw [Finset.erase_eq_of_notMem hn]
  exact qdT b p h
theorem qcX {p : ℕ} (hp : 2≤p) : 1-(p:ℂ)⁻¹≠0 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hr : 1-(p:ℝ)⁻¹≠0 := by
    have := (inv_lt_one₀ (by linarith : 0<(p:ℝ))).mpr (by linarith : 1<(p:ℝ))
    linarith
  have hc : ((1-(p:ℝ)⁻¹:ℝ):ℂ)≠0 := by exact_mod_cast hr
  simpa using hc
theorem qlv {ι : Type*} [Fintype ι] (b : ι → ℤ) {p : ℕ} (hp : 2≤p) :
    qa1 p 0 (qam b p) (qJ b) (fun _ => 0) =
      (qR (Finset.univ.image b) p : ℂ) := by
  rw [qam, qJ, qel p 0 _ _ _ _
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (qcX hp)]
  simp only [Nat.cast_zero, sub_zero, zpow_neg, zpow_natCast, qR, qax,
    Finset.image_image, Function.comp_def]
  push_cast
  simp only [div_eq_mul_inv]
  ring
theorem qkF (H : Finset ℤ) (p : ℕ) (a : ℤ) :
    qax (insert a H) p = ((H.image fun b => b%(p:ℤ)).erase (a%(p:ℤ))).card+1 := by
  unfold qax
  rw [Finset.image_insert]
  have h := Finset.card_erase_add_one (Finset.mem_insert_self (a%(p:ℤ))
    (H.image fun b => b%(p:ℤ)))
  simpa only [Finset.erase_insert_eq_erase] using h.symm
theorem qmb {ι : Type*} [Fintype ι] (b : ι → ℤ) (a : ℤ)
    (ha : ∀ i, b i≠a) {p : ℕ} (hp : 2≤p) :
    qa1 p 1 (qS b p a) (qJ b) (fun _ => 0) =
      (qR (insert a (Finset.univ.image b)) p : ℂ) := by
  have ha' : a∉Finset.univ.image b := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] using ha
  rw [qS, qJ, qel p 1 _ _ _ _
    (fun r hr => by
      rcases Finset.mem_image.mp (Finset.mem_erase.mp hr).2 with ⟨i,_,hi⟩
      exact ⟨i,hi⟩)
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (qcX hp)]
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hp1 : (p:ℂ)-1≠0 := by
    intro he
    have hh : (p:ℂ)=1 := sub_eq_zero.mp he
    have : p=1 := by exact_mod_cast hh
    omega
  have hpinv := qcX hp
  simp only [Nat.cast_one, zpow_neg, zpow_natCast, qR,
    qkF, Finset.card_insert_of_notMem ha', Finset.image_image, Function.comp_def]
  push_cast
  rw [pow_succ]
  field_simp
  ring
theorem qa2 {ι : Type*} {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) : Multipliable f := by
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hf
theorem qeF {ι : Type*} {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    ‖(∏' i, f i)-1‖≤Real.exp (∑' i, ‖f i-1‖)-1 := by
  have hm := qa2 hf
  apply le_of_tendsto ((hm.hasProd.sub_const 1).norm)
  filter_upwards [] with S
  calc
    _ ≤ Real.exp (∑ i∈S, ‖f i-1‖)-1 := by
      simpa only [add_sub_cancel] using Finset.norm_prod_one_add_sub_one_le S (fun i => f i-1)
    _ ≤ _ := sub_le_sub_right (Real.exp_le_exp.mpr (hf.sum_le_tsum S (fun _ _ => norm_nonneg _))) 1
theorem qfV {ι : Type*} (S : Finset ι) {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    (∏' i, f i) = (∏ i∈S, f i)*(∏' i : {i // i∉S}, f i) := by
  classical
  have hs := qa2 (hf.subtype (fun i => i∈S))
  have ht := qa2 (hf.subtype (fun i => i∉S))
  have hh := hs.tprod_mul_tprod_compl ht
  rw [Finset.tprod_subtype'] at hh
  exact hh.symm
theorem qfW {ι : Type*} (S : Finset ι) {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    ‖(∏' i, f i)-(∏ i∈S, f i)‖ ≤
      ‖∏ i∈S, f i‖*(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1) := by
  rw [qfV S hf, ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (qeF (hf.subtype (fun i => i∉S))) (norm_nonneg _)
theorem qkg {ι : Type*} (S : Finset ι) {f g : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) (hg : Summable (fun i => ‖g i-1‖))
    (B e : ι → ℝ) (hB : ∀ i∈S, 1≤B i)
    (hfn : ∀ i∈S, ‖f i‖≤B i) (hgn : ∀ i∈S, ‖g i‖≤B i)
    (he : ∀ i∈S, ‖f i-g i‖≤e i) :
    ‖(∏' i, f i)-(∏' i, g i)‖ ≤ (∏ i∈S, B i)*
      ((∑ i∈S, e i)+(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1)+
        (Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1)) := by
  have hpf : ‖∏ i∈S, f i‖≤∏ i∈S, B i := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfn
  have hpg : ‖∏ i∈S, g i‖≤∏ i∈S, B i := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hgn
  have hdf := qfW S hf
  have hdg := qfW S hg
  have hp := qdS S f g B e hB hfn hgn he
  have hfp : 0≤Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (tsum_nonneg fun _ => norm_nonneg _))
  have hgp : 0≤Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (tsum_nonneg fun _ => norm_nonneg _))
  have htri := norm_sub_le_norm_sub_add_norm_sub (∏' i, f i) (∏ i∈S, f i) (∏' i, g i)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (∏ i∈S, f i) (∏ i∈S, g i) (∏' i, g i)
  rw [norm_sub_rev (∏ i∈S, g i)] at htri'
  calc
    _ ≤ ‖(∏' i, f i)-(∏ i∈S, f i)‖+‖(∏ i∈S, f i)-(∏ i∈S, g i)‖+
        ‖(∏' i, g i)-(∏ i∈S, g i)‖ := by linarith
    _ ≤ (∏ i∈S, B i)*(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1)+
        (∏ i∈S, B i)*(∑ i∈S, e i)+
        (∏ i∈S, B i)*(Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1) := by
      exact add_le_add (add_le_add (hdf.trans (mul_le_mul_of_nonneg_right hpf hfp)) hp)
        (hdg.trans (mul_le_mul_of_nonneg_right hpg hgp))
    _ = _ := by ring
theorem qg3 {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i∈S, y<n i) :
    (∑ i∈S, (1:ℝ)/(n i:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  rw [← Finset.sum_image (f := fun k : ℕ => (1:ℝ)/(k:ℝ)^2) (fun _ _ _ _ h => hn h)]
  apply qgW hy
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨i,hi,rfl⟩
  exact hl i hi
theorem qc7 {ι : Type*} (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i, y<n i)
    (f : ι → ℝ) {K : ℝ} (hK : 0≤K) (hf : ∀ i, 0≤f i)
    (hbound : ∀ i, f i≤K/(n i:ℝ)^2) :
    Summable f ∧ (∑' i, f i)≤K/(y:ℝ) := by
  have hh (S : Finset ι) : (∑ i∈S, f i)≤K/(y:ℝ) := by
    calc
      _ ≤ ∑ i∈S, K/(n i:ℝ)^2 := Finset.sum_le_sum fun i _ => hbound i
      _ = K*(∑ i∈S, (1:ℝ)/(n i:ℝ)^2) := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
      _ ≤ K*(1/(y:ℝ)) := mul_le_mul_of_nonneg_left
        (qg3 S n hn hy (fun i _ => hl i)) hK
      _ = _ := by ring
  exact ⟨summable_of_sum_le hf hh, Real.tsum_le_of_sum_le hf hh⟩
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
section FourierNormalization
open scoped FourierTransform SchwartzMap
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
noncomputable def qi2 : V ≃L[ℝ] V :=
  Units.mk0 ((2*Real.pi)⁻¹) (inv_ne_zero (by positivity)) • ContinuousLinearEquiv.refl ℝ V
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem qfv (u : V) :
    qi2 u = (2*Real.pi)⁻¹ • u := rfl
noncomputable def qaL (G : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  (((2*Real.pi)^Module.finrank ℝ V)⁻¹ : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ qi2 (𝓕⁻ G)
theorem qkh (G : SchwartzMap V ℂ) (v : V) :
    (∫ u : V, qaL G u * Complex.exp (-Complex.I*(inner ℝ u v : ℂ))) = G v := by
  let A : ℝ := 2*Real.pi
  have hA : 0<A := by dsimp [A]; positivity
  let f := fun u : V => (𝓕⁻ G) u * Complex.exp (-Complex.I*((A*inner ℝ u v : ℝ):ℂ))
  have hscale : (∫ u : V, f (A⁻¹ • u)) = A^Module.finrank ℝ V • ∫ u : V, f u := by
    simpa only [inv_pow, inv_inv] using Measure.integral_comp_smul_of_nonneg volume f A⁻¹ (hR:= (inv_pos.mpr hA).le)
  have hinv : (∫ u : V, f u) = G v := by
    have hh := congrArg (fun H : SchwartzMap V ℂ => H v) (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap V ℂ) G)
    rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [f, A]
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring_nf
  calc
    _ = ∫ u : V, (A^Module.finrank ℝ V)⁻¹ • f (A⁻¹ • u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [qaL, smul_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        qfv]
      dsimp only [f, A]
      rw [real_inner_smul_left]
      have ht : 2*Real.pi*((2*Real.pi)⁻¹*inner ℝ u v) = inner ℝ u v := by field_simp
      rw [ht]
      simp only [Complex.real_smul, mul_assoc]
    _ = (A^Module.finrank ℝ V)⁻¹ • ∫ u : V, f (A⁻¹ • u) := integral_smul _ _
    _ = (A^Module.finrank ℝ V)⁻¹ • (A^Module.finrank ℝ V • G v) := by rw [hscale, hinv]
    _ = G v := by rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hA.ne'), one_smul]
noncomputable def qdC (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  (show HasCompactSupport (fun v => Complex.exp (ℓ v : ℂ)*F v) from hF.mul_left).toSchwartzMap
    (((Complex.ofRealCLM.contDiff.comp ℓ.contDiff).cexp).mul hFs)
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem qgy (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    qdC ℓ F hF hFs v = Complex.exp (ℓ v : ℂ)*F v := rfl
noncomputable def qq (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  qaL (qdC ℓ F hF hFs)
theorem qdt (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, qq ℓ F hF hFs u *
      Complex.exp (-(ℓ v : ℂ)-Complex.I*(inner ℝ u v : ℂ))) = F v := by
  calc
    _ = Complex.exp (-(ℓ v : ℂ)) *
        ∫ u : V, qq ℓ F hF hFs u *
          Complex.exp (-Complex.I*(inner ℝ u v : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [sub_eq_add_neg, Complex.exp_add]
      ring_nf
    _ = Complex.exp (-(ℓ v : ℂ)) * (Complex.exp (ℓ v : ℂ)*F v) := by
      rw [qq, qkh, qgy]
    _ = F v := by rw [← mul_assoc, ← Complex.exp_add]; simp
end FourierNormalization
def qaK (y : ℕ) : Finset Nat.Primes := (Nat.primesLE y).subtype Nat.Prime
@[simp] theorem qdD (y : ℕ) (p : Nat.Primes) :
    p∈qaK y ↔ (p:ℕ)≤y := by
  exact (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE y) (a := p)).trans
    (by rw [Nat.mem_primesLE]; exact and_iff_left p.property)
noncomputable def qav {ι : Type*} (δ : ℕ) (A : ℕ → Finset (Finset ι))
    (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏' p : Nat.Primes, qa1 p δ (A p) B z
noncomputable def qM (m : ℕ) : ℝ :=
  (1+m)*(4*(m:ℝ)^2*2^m+2*m)+2*m+2*(m:ℝ)^2
theorem qbp (m : ℕ) : 0≤qM m := by
  unfold qM
  positivity
theorem qcK {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    Summable (fun p : Nat.Primes => ‖qa1 p δ (A p) B z-1‖) := by
  apply (qaK y).summable_compl_iff.mp
  apply (qc7
    (fun p : {p : Nat.Primes // p∉qaK y} => (p.val:ℕ))
    (fun _ _ he => Subtype.ext (Subtype.ext he)) hy
    (fun p => by have := p.property; simp only [qdD, not_le] at this; exact this)
    (fun p => ‖qa1 p.val δ (A p.val) B z-1‖)
    (qbp B.card) (fun _ => norm_nonneg _) ?_).1
  intro p
  have hp : y<(p.val:ℕ) := by
    have := p.property
    simpa only [qdD, not_le] using this
  rw [hgen p.val hp]
  exact qg2 p.val.property.two_le hδ B z (fun _ _ i _ => hz i)
theorem qg4 {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    (∑' p : {p : Nat.Primes // p∉qaK y}, ‖qa1 p.val δ (A p.val) B z-1‖) ≤
      qM B.card/(y:ℝ) := by
  apply (qc7
    (fun p : {p : Nat.Primes // p∉qaK y} => (p.val:ℕ))
    (fun _ _ he => Subtype.ext (Subtype.ext he)) hy
    (fun p => by have := p.property; simp only [qdD, not_le] at this; exact this)
    (fun p => ‖qa1 p.val δ (A p.val) B z-1‖)
    (qbp B.card) (fun _ => norm_nonneg _) ?_).2
  intro p
  have hp : y<(p.val:ℕ) := by
    have := p.property
    simpa only [qdD, not_le] using this
  rw [hgen p.val hp]
  exact qg2 p.val.property.two_le hδ B z (fun _ _ i _ => hz i)
noncomputable def qC (y : ℕ) : ℝ :=
  ∑ p∈qaK y, (p:ℝ)⁻¹
theorem qkG {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖qav δ A B z-qav δ A B (fun _ => 0)‖ ≤
      Real.exp (4*R*qC y)*
        (Real.exp (2*R)*6*R*Real.log y*(∑ i, ‖z i‖)*qC y+
          2*(Real.exp (qM B.card/(y:ℝ))-1)) := by
  let Z : ℝ := ∑ i, ‖z i‖
  have hZ : 0≤Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hy0 : 0<y := by omega
  have hyR : (0:ℝ)<y := by exact_mod_cast hy0
  have hly : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hf := qcK hδ A B z hz hy0 hgen
  have hg := qcK hδ A B (fun _ => 0) (by simp) hy0 hgen
  let b : Nat.Primes → ℝ := fun p => Real.exp (4*R*(p:ℝ)⁻¹)
  let e : Nat.Primes → ℝ := fun p => Real.exp (2*R)*6*R*Real.log y*Z*(p:ℝ)⁻¹
  have hbn (p : Nat.Primes) : 1≤b p := Real.one_le_exp (by positivity)
  have hnorm (w : ι → ℂ) (hw : ∀ i, 0≤(w i).re) (p : Nat.Primes) :
      ‖qa1 p δ (A p) B w‖≤b p := by
    apply (qk7 p.property.two_le hδ (A p) B w hw).trans
    apply Real.exp_le_exp.mpr
    have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
    have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
    have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
    nlinarith
  have hd (p : Nat.Primes) (hp : p∈qaK y) :
      ‖qa1 p δ (A p) B z-qa1 p δ (A p) B (fun _ => 0)‖≤e p := by
    have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
    have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
    have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hpl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_le)
    have hpu : Real.log (p:ℝ)≤Real.log (y:ℝ) :=
      Real.log_le_log hp0 (by exact_mod_cast (qdD y p).mp hp)
    have hp2 : (p:ℝ)⁻¹≤1/2 := qcU p.property.two_le
    have hpe : 2*((A p).card+B.card)*(p:ℝ)⁻¹≤2*R := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ)≤R) (sub_nonneg.mpr hp2),
        mul_nonneg (show 0≤(p:ℝ)⁻¹ by positivity) (show (0:ℝ)≤2*R-((A p).card+B.card) by linarith)]
    have hpc : (2*(A p).card+4*B.card:ℝ)≤6*R := by linarith
    calc
      _ ≤ Real.exp (2*((A p).card+B.card)*(p:ℝ)⁻¹)*
          ((2*(A p).card+4*B.card)*(p:ℝ)⁻¹*Real.log p*Z) :=
        qkf p.property.two_le hδ (A p) B z hz
      _ ≤ Real.exp (2*R)*((6*R)*(p:ℝ)⁻¹*Real.log y*Z) := by gcongr
      _ = e p := by dsimp only [e]; ring
  have hh := qkg (qaK y) hf hg b e
    (fun p _ => hbn p) (fun p _ => hnorm z hz p)
    (fun p _ => hnorm (fun _ => 0) (by simp) p) hd
  have hbprod : (∏ p∈qaK y, b p) = Real.exp (4*R*qC y) := by
    dsimp only [b, qC]
    rw [← Real.exp_sum, Finset.mul_sum]
  have hesum : (∑ p∈qaK y, e p) =
      Real.exp (2*R)*6*R*Real.log y*Z*qC y := by
    simp only [e, qC, Finset.mul_sum]
  have htf := qg4 hδ A B z hz hy0 hgen
  have htg := qg4 hδ A B (fun _ => 0) (by simp) hy0 hgen
  rw [hbprod, hesum] at hh
  calc
    _ ≤ Real.exp (4*R*qC y)*
        (Real.exp (2*R)*6*R*Real.log y*Z*qC y+
          (Real.exp (qM B.card/(y:ℝ))-1)+
          (Real.exp (qM B.card/(y:ℝ))-1)) := by
      apply hh.trans
      gcongr
    _ = _ := by dsimp only [Z]; ring
theorem qdH {a b : ℤ} {D p : ℕ}
    (ha : a.natAbs≤D) (hb : b.natAbs≤D) (hp : 2*D<p)
    (hab : a%(p:ℤ)=b%(p:ℤ)) : a=b := by
  have hd : (p:ℤ)∣a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hab)
  have hdN : p∣(a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hlt : (a-b).natAbs<p := by have := Int.natAbs_sub_le a b; omega
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdN hlt))
theorem qg5 {ι : Type*} [Fintype ι] (b : ι → ℤ)
    {D p : ℕ} (hb : ∀ i, (b i).natAbs≤D) (hp : 2*D<p) :
    qam b p=qJ b :=
  qdT b p (fun i j he => qdH (hb i) (hb j) hp he)
theorem qe3 {ι : Type*} [Fintype ι] (b : ι → ℤ)
    (a : ℤ) (ha : ∀ i, b i≠a) {D p : ℕ} (hb : ∀ i, (b i).natAbs≤D)
    (haD : a.natAbs≤D) (hp : 2*D<p) :
    qS b p a=qJ b :=
  qfH b p a
    (fun i j he => qdH (hb i) (hb j) hp he)
    (fun i he => ha i (qdH (hb i) haD hp he))
theorem qcY {ι : Type*} [Fintype ι] (S : Finset (Finset ι)) :
    S.card≤2^Fintype.card ι := by
  classical
  simpa only [Fintype.card_finset] using Finset.card_le_univ S
theorem qea (H : Finset ℤ) :
    HasProd (fun p : Nat.Primes => (qR H p : ℂ)) (qay H : ℂ) := by
  exact (qii H).hasProd.map Complex.ofRealHom.toMonoidHom
    Complex.continuous_ofReal
theorem qjh {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    qav 0 (qam b) (qJ b) (fun _ => 0) =
      (qay (Finset.univ.image b) : ℂ) := by
  rw [qav]
  exact ((qea _).congr_fun fun p =>
    qlv b p.property.two_le).tprod_eq
theorem qki {ι : Type*} [Fintype ι] (b : ι → ℤ) (a : ℤ)
    (ha : ∀ i, b i≠a) :
    qav 1 (fun p => qS b p a) (qJ b) (fun _ => 0) =
      (qay (insert a (Finset.univ.image b)) : ℂ) := by
  rw [qav]
  exact ((qea _).congr_fun fun p =>
    qmb b a ha p.property.two_le).tprod_eq
theorem qmc {ι : Type*} {p : ℕ} (hp : 0<p)
    (z : ι → ℂ) (S : Finset ι) :
    (p:ℂ)^(-(1+∑ i∈S, z i)) = (p:ℂ)⁻¹*qr p z S := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  rw [show (Real.log p : ℂ)*(-(1+∑ i∈S, z i)) =
    -(Real.log p : ℂ)+(-(Real.log p : ℂ)*(∑ i∈S, z i)) by ring,
    Complex.exp_add, Complex.exp_neg, Complex.natCast_log, Complex.exp_log hp0]
  simp only [qr, Complex.natCast_log]
noncomputable def qb4 {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, riemannZeta (1+∑ i∈S, z i)^((-1:ℤ)^S.card)
theorem qjM {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) :
    HasProd (fun p : Nat.Primes =>
      ∏ S∈B, (1-(p:ℂ)⁻¹*qr p z S)^(-((-1:ℤ)^S.card)))
      (qb4 B z) := by
  apply hasProd_prod
  intro S hS
  have hs : 1<(1+∑ i∈S, z i).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.re_sum]
    exact lt_add_of_pos_right _ (Finset.sum_pos (fun i _ => hz i) (hB S hS))
  have he := riemannZeta_eulerProduct_hasProd hs
  have hc (p : Nat.Primes) : (p:ℂ)^(-(1+∑ i∈S, z i)) =
      (p:ℂ)⁻¹*qr p z S := qmc p.property.pos z S
  rcases qdB S.card with hp | hn
  · simpa only [hp, zpow_neg_one, zpow_one, hc] using he
  · have he' := he.inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)
    simpa only [hn, neg_neg, zpow_one, zpow_neg_one, inv_inv, hc] using he'
theorem qji {ι : Type*} {p : ℕ} (hp : 2≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    1-(p:ℂ)⁻¹*qr p z S ≠ 0 := by
  have hpR : (1:ℝ)<p := by exact_mod_cast (by omega : 1<p)
  have hb := (qby (by omega) z S hz).trans_lt
    ((inv_lt_one₀ (by positivity : (0:ℝ)<p)).mpr hpR)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hb
  exact hb.false
theorem qlw {ι : Type*} {p : ℕ} (hp : 2≤p) (δ : ℕ)
    (A B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    qbt p δ A z = qa1 p δ A B z *
      ∏ S∈B, (1-(p:ℂ)⁻¹*qr p z S)^(-((-1:ℤ)^S.card)) := by
  rw [qa1, mul_assoc, ← Finset.prod_mul_distrib]
  have he : (∏ S∈B, (1-(p:ℂ)⁻¹*qr p z S)^((-1:ℤ)^S.card) *
      (1-(p:ℂ)⁻¹*qr p z S)^(-((-1:ℤ)^S.card))) = 1 := by
    apply Finset.prod_eq_one
    intro S _
    rw [← zpow_add₀ (qji hp z S (fun i _ => hz i)), add_neg_cancel,
      zpow_zero]
  rw [he, mul_one]
theorem qmR {ι : Type*} (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) {H : ℂ}
    (hH : HasProd (fun p : Nat.Primes => qa1 p δ (A p) B z) H) :
    HasProd (fun p : Nat.Primes => qbt p δ (A p) z) (H*qb4 B z) := by
  exact (hH.mul (qjM B z hB hz)).congr_fun fun p =>
    qlw p.property.two_le δ (A p) B z (fun i => (hz i).le)
abbrev q4 {κ : Type*} (A : κ → Type*) :=
  Σ P : Finset κ, (p : P) → A p
noncomputable def qaS {κ : Type*} {A : κ → Type*}
    (w : (p : κ) → A p → ℂ) (c : q4 A) : ℂ :=
  ∏ p : c.1, w p (c.2 p)
noncomputable def qaT {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (p : κ) : ℝ := ∑ a, ‖w p a‖
theorem qbw {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (p : κ) : 0≤qaT w p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem qg6 {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (P : Finset κ) :
    (∑ c : (p : P) → A p, ‖qaS w ⟨P,c⟩‖) = ∏ p∈P, qaT w p := by
  classical
  simp only [qaS, norm_prod, qaT]
  rw [← Fintype.prod_sum (fun (p : P) (a : A p) => ‖w p a‖)]
  exact Finset.prod_coe_sort P (fun p => ∑ a, ‖w p a‖)
theorem qmO {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (P : Finset κ) :
    (∑ c : (p : P) → A p, qaS w ⟨P,c⟩) = ∏ p∈P, ∑ a, w p a := by
  classical
  simp only [qaS]
  rw [← Fintype.prod_sum (fun (p : P) (a : A p) => w p a)]
  exact Finset.prod_coe_sort P (fun p => ∑ a, w p a)
theorem qcZ {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (qaT w)) :
    Summable (fun c : q4 A => ‖qaS w c‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp_rw [tsum_fintype, qg6]
  exact summable_finsetProd_of_summable_nonneg (qbw w) hw
theorem qlx {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (qaT w)) :
    HasProd (fun p => 1+∑ a, w p a) (∑' c : q4 A, qaS w c) := by
  classical
  have hs := (qcZ w hw).of_norm
  apply hasProd_one_add_of_hasSum_prod
  exact hs.hasSum.sigma fun P => by
    simpa only [qmO] using
      hasSum_fintype (fun c : (p : P) → A p => qaS w ⟨P,c⟩)
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
theorem qjj {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (qaT w)) :
    (∑' c : q4 A, ‖qaS w c‖) ≤ Real.exp (∑' p, qaT w p) := by
  classical
  have hc := qcZ w hw
  rw [hc.tsum_sigma]
  simp_rw [tsum_fintype, qg6]
  have hs := summable_finsetProd_of_summable_nonneg (qbw w) hw
  apply hs.tsum_le_of_sum_le
  intro T
  calc
    _ ≤ ∑ s∈(T.biUnion id).powerset, ∏ p∈s, qaT w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.mpr
        (Finset.subset_biUnion_of_mem id hs))
        (fun s _ _ => Finset.prod_nonneg fun _ _ => qbw w _)
    _ = ∏ p∈T.biUnion id, (1+qaT w p) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p∈T.biUnion id, qaT w p) :=
      Real.prod_one_add_le_exp_sum _ (qbw w)
    _ ≤ _ := Real.exp_le_exp.mpr (hw.sum_le_tsum _ fun p _ => qbw w p)
theorem qiO {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {ε : ℝ} (hε : 0≤ε)
    (hz : ∀ i∈S, ε≤(z i).re) :
    ‖qr p z S‖ ≤ (p:ℝ)^(-ε) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  obtain ⟨i,hi⟩ := hS
  have hs : ε≤∑ j∈S, (z j).re := (hz i hi).trans
    (Finset.single_le_sum (fun j hj => hε.trans (hz j hj)) hi)
  rw [qr, Complex.norm_exp, Real.rpow_def_of_pos hpR]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
  nlinarith
noncomputable def qcV {ι : Type*} (δ : ℕ) (z : ι → ℂ)
    (p : Nat.Primes) (S : Finset ι) : ℂ :=
  ((p:ℂ)-δ)⁻¹*((-1:ℂ)^S.card*qr p z S)
theorem qhT {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (z : ι → ℂ) (p : Nat.Primes) (S : Finset ι) (hS : S.Nonempty)
    {ε : ℝ} (hε : 0≤ε) (hz : ∀ i∈S, ε≤(z i).re) :
    ‖qcV δ z p S‖ ≤ 2/(p:ℝ)^(1+ε) := by
  have hd := qe2 p.property.two_le hδ
  have he' : ‖(p:ℂ)-δ‖ = (p:ℝ)-δ := by
    have h := Complex.norm_of_nonneg hd.1.le
    simpa using h
  have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
  calc
    _ = ((p:ℝ)-δ)⁻¹*‖qr p z S‖ := by
      simp only [qcV, norm_mul, norm_inv, he', norm_pow, norm_neg,
        norm_one, one_pow, one_mul]
    _ ≤ (2*(p:ℝ)⁻¹)*(p:ℝ)^(-ε) :=
      mul_le_mul hd.2.1 (qiO p.property.one_le z S hS hε hz)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_neg hp0.le, Real.rpow_add hp0, Real.rpow_one]; field_simp
theorem qhU {s : ℝ} (hs : 1<s) :
    (∑' p : Nat.Primes, 1/(p:ℝ)^s) ≤ Real.log (riemannZeta (s:ℂ)).re := by
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n)) :=
    (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
      (qca s) (qg1 s)
  have hprime := (Real.summable_one_div_nat_rpow.mpr hs).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have he (p : Nat.Primes) :
      ArithmeticFunction.vonMangoldt (p:ℕ)/((p:ℝ)^s*Real.log (p:ℝ)) = 1/(p:ℝ)^s := by
    have hl : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.property]
    field_simp
  rw [log_riemannZeta_eq hs]
  apply hprime.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p:ℕ)) (fun _ _ => Subtype.ext)
    (fun n _ => qca s n) (fun p => (he p).symm.le) hsum
noncomputable def qbq {ι : Type*} (δ : ℕ) (A : ℕ → Finset (Finset ι))
    (z : ι → ℂ) (p : Nat.Primes) (S : {S // S∈A p}) : ℂ := qcV δ z p S
theorem qem {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0≤ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) (p : Nat.Primes) :
    qaT (qbq δ A z) p ≤ (2*R)/(p:ℝ)^(1+ε) := by
  classical
  have hb : ∀ S : {S // S∈A p}, ‖qbq δ A z p S‖ ≤ 2/(p:ℝ)^(1+ε) :=
    fun S => qhT hδ z p S (hA p S S.property) hε (fun _ _ => hz _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun S _ => hb S)
  have hs : ((A p).card:ℝ) ≤ R := by exact_mod_cast hR p
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] at hh
  exact hh.trans (by calc
    _ ≤ (R:ℝ)*(2/(p:ℝ)^(1+ε)) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring)
theorem qb5 {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    Summable (qaT (qbq δ A z)) := by
  have hs := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1<1+ε)).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have hs' : Summable (fun p : Nat.Primes => (2*R)/(p:ℝ)^(1+ε)) := by
    simpa only [Function.comp_def, mul_one_div] using hs.mul_left (2*R:ℝ)
  exact hs'.of_nonneg_of_le (qbw _) (qem hδ A z
    hε.le hA hR hz)
theorem qjk {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    HasProd (fun p : Nat.Primes => qbt p δ (A p) z)
      (∑' c : q4 (fun p : Nat.Primes => {S // S∈A p}),
        qaS (qbq δ A z) c) := by
  apply (qlx _ (qb5 hδ A z hε hA hR hz)).congr_fun
  intro p
  simp only [qbt, qbq, qcV, ← Finset.mul_sum,
    ]
  congr 2
  exact (Finset.sum_coe_sort (A p) (fun S => (-1:ℂ)^S.card*qr p z S)).symm
theorem qg7 {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    (∑' c : q4 (fun p : Nat.Primes => {S // S∈A p}),
        ‖qaS (qbq δ A z) c‖) ≤
      Real.exp ((2*R)*Real.log (riemannZeta ((1+ε:ℝ):ℂ)).re) := by
  have hsum := qb5 hδ A z hε hA hR hz
  refine (qjj _ hsum).trans (Real.exp_le_exp.mpr ?_)
  have hs := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1<1+ε)).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have hs' : Summable (fun p : Nat.Primes => (2*R)/(p:ℝ)^(1+ε)) := by
    simpa only [Function.comp_def, mul_one_div] using hs.mul_left (2*R:ℝ)
  calc
    _ ≤ ∑' p : Nat.Primes, (2*R)/(p:ℝ)^(1+ε) :=
      hsum.tsum_le_tsum (qem hδ A z hε.le hA hR hz) hs'
    _ = (2*R:ℝ)*(∑' p : Nat.Primes, 1/(p:ℝ)^(1+ε)) := by
      simp only [← tsum_mul_left, mul_one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (qhU (by linarith)) (by positivity)
noncomputable def qai {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) : Finset ι := by
  classical
  exact if hp : p∈c.1 then (c.2 ⟨p,hp⟩).val else ∅
@[simp] theorem qbc {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∈c.1) :
    qai c p = (c.2 ⟨p,hp⟩).val := by simp [qai, hp]
@[simp] theorem qdu {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∉c.1) :
    qai c p = ∅ := by simp [qai, hp]
noncomputable def qag {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (i : ι) : ℕ := by
  classical
  exact ∏ p∈c.1.filter (fun p => i∈qai c p), (p:ℕ)
theorem qc0 {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    Squarefree (qag c i) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p _ q _ hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes p.property q.property).mpr
      (fun he => hpq (Subtype.ext he)))
  · intro p _
    exact p.property.prime.squarefree
theorem qe4 {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) (i : ι) :
    (p:ℕ) ∣ qag c i ↔ i∈qai c p := by
  classical
  rw [qag, p.property.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q,hq,hpq⟩
    have he : p=q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hpq)
    simpa [he] using (Finset.mem_filter.mp hq).2
  · intro hi
    have hp : p∈c.1 := by
      by_contra hn
      simp [qdu c hn] at hi
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,hi⟩,dvd_refl _⟩
noncomputable def qaZ {ι : Type*} [Fintype ι] (d : ι → ℕ) : Finset Nat.Primes := by
  classical
  exact (Finset.univ.biUnion fun i => (d i).primeFactors).subtype Nat.Prime
theorem qgz {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i≠0) (p : Nat.Primes) : p∈qaZ d ↔ ∃ i, (p:ℕ)∣d i := by
  classical
  refine (Finset.mem_subtype (a := (⟨p.val,p.property⟩ : {n : ℕ // Nat.Prime n}))).trans ?_
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Nat.mem_primeFactors,
    p.property, true_and]
  constructor
  · rintro ⟨i,hi,_⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,hi,hd i⟩
noncomputable def qK {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (p:ℕ)∣d i
@[simp] theorem qly {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) (i : ι) : i∈qK d p ↔ (p:ℕ)∣d i := by
  classical
  simp [qK]
theorem qcj {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : ∀ i, d i≠0) (p : Nat.Primes) :
    (qK d p).Nonempty ↔ p∈qaZ d := by
  rw [qgz hd]
  simp [Finset.Nonempty]
theorem qhV {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes)
    (h : (qai c p).Nonempty) : qai c p∈A p := by
  classical
  by_cases hp : p∈c.1
  · rw [qbc c hp]
    exact (c.2 ⟨p,hp⟩).property
  · simp [qdu c hp] at h
theorem qe5 {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) :
    qK (qag c) p = qai c p := by
  ext i
  simp [qe4]
theorem qlW {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) :
    qaZ (qag c) = c.1 := by
  classical
  ext p
  rw [← qcj _ (fun i => (qc0 c i).ne_zero),
    qe5]
  by_cases hp : p∈c.1
  · simp only [hp, iff_true, qbc c hp]
    exact hA p _ (c.2 ⟨p,hp⟩).property
  · simp [hp]
theorem qmz {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    {c e : q4 (fun p : Nat.Primes => {S // S∈A p})}
    (h : ∀ p, qai c p = qai e p) : c=e := by
  classical
  have hc (p : Nat.Primes) : p∈c.1 ↔ (qai c p).Nonempty := by
    by_cases hp : p∈c.1
    · simp only [hp, true_iff, qbc c hp]
      exact hA p _ (c.2 ⟨p,hp⟩).property
    · simp [hp]
  have he (p : Nat.Primes) : p∈e.1 ↔ (qai e p).Nonempty := by
    by_cases hp : p∈e.1
    · simp only [hp, true_iff, qbc e hp]
      exact hA p _ (e.2 ⟨p,hp⟩).property
    · simp [hp]
  have hce : c.1=e.1 := Finset.ext fun p => by rw [hc,he,h]
  rcases c with ⟨P,c⟩
  rcases e with ⟨Q,e⟩
  dsimp only at hce
  subst Q
  congr 1
  funext p
  apply Subtype.ext
  simpa only [qbc ⟨P,c⟩ p.property,
    qbc ⟨P,e⟩ p.property] using h p
def qB {ι : Type*} [Fintype ι] (A : ℕ → Finset (Finset ι)) :=
  {d : ι → ℕ // (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (qK d p).Nonempty → qK d p∈A p}
noncomputable def qdU {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : qB A) : q4 (fun p : Nat.Primes => {S // S∈A p}) :=
  ⟨qaZ d.val, fun p => ⟨qK d.val p,
    d.property.2 p ((qcj d.val
      (fun i => (d.property.1 i).ne_zero) p).mpr p.property)⟩⟩
theorem qhK {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : qB A) (p : Nat.Primes) :
    qai (qdU d) p = qK d.val p := by
  classical
  by_cases hp : p∈qaZ d.val
  · exact qbc (qdU d) hp
  · rw [qdu (qdU d) hp]
    apply Eq.symm
    exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hp
      ((qcj d.val (fun i => (d.property.1 i).ne_zero) p).mp h))
theorem qio {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : qB A) : qag (qdU d) = d.val := by
  funext i
  apply (Nat.Squarefree.ext_iff (qc0 _ i) (d.property.1 i)).mpr
  intro p hp
  let p' : Nat.Primes := ⟨p,hp⟩
  exact (qe4 (qdU d) p' i).trans
    ((Iff.of_eq (congrArg (fun S : Finset ι => i∈S) (qhK d p'))).trans
      (qly d.val p' i))
noncomputable def qm3 {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) : qB A :=
  ⟨qag c, qc0 c, fun p h => by
    rw [qe5] at h ⊢
    exact qhV c p h⟩
noncomputable def qdI {ι : Type*} [Fintype ι]
    (A : ℕ → Finset (Finset ι)) (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) :
    q4 (fun p : Nat.Primes => {S // S∈A p}) ≃ qB A where
  toFun := qm3
  invFun := qdU
  left_inv c := by
    apply qmz hA
    intro p
    rw [qhK]
    exact qe5 c p
  right_inv d := Subtype.ext (qio d)
theorem qip {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    {M : Type*} [CommMonoid M]
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (f : Nat.Primes → ι → M) :
    (∏ i, ∏ p∈c.1.filter (fun p => i∈qai c p), f p i) =
      ∏ p∈c.1, ∏ i∈qai c p, f p i := by
  classical
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp
theorem qkH {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    ArithmeticFunction.moebius (qag c i) =
      ∏ _p∈c.1.filter (fun p => i∈qai c p), (-1:ℤ) := by
  classical
  unfold qag
  rw [ArithmeticFunction.IsMultiplicative.map_prod (fun p : Nat.Primes => (p:ℕ))
    ArithmeticFunction.isMultiplicative_moebius _ (fun p _ q _ hpq =>
      (Nat.coprime_primes p.property q.property).mpr (fun h => hpq (Subtype.ext h)))]
  apply Finset.prod_congr rfl
  intro p _
  exact ArithmeticFunction.moebius_apply_prime p.property
theorem qiq {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) :
    (∏ i, ArithmeticFunction.moebius (qag c i)) =
      ∏ p∈c.1, (-1:ℤ)^(qai c p).card := by
  classical
  simp_rw [qkH]
  rw [qip c (fun _ _ => (-1:ℤ))]
  simp only [Finset.prod_const]
theorem qmd {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    Real.log (qag c i) =
      ∑ p∈c.1.filter (fun p => i∈qai c p), Real.log (p:ℕ) := by
  classical
  rw [qag, Nat.cast_prod]
  exact Real.log_prod (fun p _ => by exact_mod_cast p.property.ne_zero)
theorem qjN {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) :
    qr p z S = ∏ i∈S, Complex.exp (-(Real.log p : ℂ)*z i) := by
  rw [qr, Finset.mul_sum, Complex.exp_sum]
theorem qlX {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (z : ι → ℂ) :
    (∏ p∈c.1, qr p z (qai c p)) =
      Complex.exp (-∑ i, (Real.log (qag c i) : ℂ)*z i) := by
  classical
  simp_rw [qjN]
  rw [← qip c (fun p i => Complex.exp (-(Real.log (p:ℕ) : ℂ)*z i)),
    ← Finset.sum_neg_distrib, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_sum, qmd, Complex.ofReal_sum]
  congr 1
  simp only [Finset.sum_mul, ← Finset.sum_neg_distrib, neg_mul]
noncomputable def qaA {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ) : ℂ :=
  ∏ p∈qaZ d, ((p:ℂ)-δ)⁻¹
noncomputable def qk {ι : Type*} [Fintype ι] (δ : ℕ)
    (d : ι → ℕ) (z : ι → ℂ) : ℂ :=
  qaA δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
    Complex.exp (-∑ i, (Real.log (d i):ℂ)*z i)
theorem qbA {ι : Type*} [Fintype ι]
    {A : ℕ → Finset (Finset ι)} (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (δ : ℕ) (c : q4 (fun p : Nat.Primes => {S // S∈A p})) (z : ι → ℂ) :
    qaS (qbq δ A z) c =
      qk δ (qag c) z := by
  classical
  have hcast : (∏ i, (ArithmeticFunction.moebius (qag c i):ℂ)) =
      ∏ p∈c.1, (-1:ℂ)^(qai c p).card := by
    exact_mod_cast qiq c
  rw [qk, qaA, qlW hA c, hcast,
    ← qlX c z, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold qaS qbq qcV
  rw [← Finset.prod_coe_sort c.1]
  apply Finset.prod_congr rfl
  intro p _
  rw [← qbc c p.property]
  ring
theorem qcM {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    Summable (fun d : qB A => ‖qk δ d.val z‖) := by
  apply (qdI A hA).summable_iff.mp
  change Summable (fun c => ‖qk δ (qag c) z‖)
  simp_rw [← qbA hA δ]
  exact qcZ _ (qb5 hδ A z hε hA hR hz)
theorem qlz {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    HasProd (fun p : Nat.Primes => qbt p δ (A p) z)
      (∑' d : qB A, qk δ d.val z) := by
  rw [← (qdI A hA).tsum_eq
    (fun d => qk δ d.val z)]
  change HasProd _ (∑' c, qk δ (qag c) z)
  simp_rw [← qbA hA δ]
  exact qjk hδ A z hε hA hR hz
theorem qjl {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    (∑' d : qB A, ‖qk δ d.val z‖) ≤
      Real.exp ((2*R)*Real.log (riemannZeta ((1+ε:ℝ):ℂ)).re) := by
  rw [← (qdI A hA).tsum_eq
    (fun d => ‖qk δ d.val z‖)]
  change (∑' c, ‖qk δ (qag c) z‖) ≤ _
  simp_rw [← qbA hA δ]
  exact qg7 hδ A z hε hA hR hz
theorem qkI {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re)
    (hB : ∀ S∈B, S.Nonempty) {H : ℂ}
    (hH : HasProd (fun p : Nat.Primes => qa1 p δ (A p) B z) H) :
    (∑' d : qB A, qk δ d.val z) =
      H*qb4 B z := by
  exact (qlz hδ A z hε hA hR hz).unique
    (qmR δ A B z hB (fun i => hε.trans_le (hz i)) hH)
theorem qlA {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    {p : ℕ} (hp : Nat.Prime p) : p∣s.lcm d ↔ ∃ i∈s, p∣d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @insert i s hi ih =>
    rw [Finset.lcm_insert]
    change p∣Nat.lcm (d i) (s.lcm d) ↔ _
    simp only [hp.dvd_lcm, ih, Finset.mem_insert, exists_eq_or_imp]
theorem qdV {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i≠0) :
    qaZ d = (qm d).primeFactors.subtype Nat.Prime := by
  ext p
  change p∈qaZ d ↔
    (⟨p.val,p.property⟩ : {n : ℕ // Nat.Prime n})∈(qm d).primeFactors.subtype Nat.Prime
  rw [qgz hd p, Finset.mem_subtype, Nat.mem_primeFactors]
  have hq0 : Finset.univ.lcm d ≠ 0 :=
    (qbE (fun i => Nat.pos_of_ne_zero (hd i))).ne'
  simp only [p.property, true_and, qm, qlA _ _ p.property,
    Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h,hq0⟩, fun h => h.1⟩
theorem qfX {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : qm d = ∏ p∈qaZ d, (p:ℕ) := by
  rw [qdV (fun i => (hd i).ne_zero)]
  change qm d = Finset.prod ((qm d).primeFactors.subtype Nat.Prime)
    (fun p : {n : ℕ // Nat.Prime n} => p.val)
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => p)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  exact (Nat.prod_primeFactors_of_squarefree (qdr hd)).symm
theorem qfY {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) :
    (qm d).totient = ∏ p∈qaZ d, ((p:ℕ)-1) := by
  rw [qdV (fun i => (hd i).ne_zero)]
  change (qm d).totient = Finset.prod ((qm d).primeFactors.subtype Nat.Prime)
    (fun p : {n : ℕ // Nat.Prime n} => p.val-1)
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => p-1)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.prod_primeFactors_of_squarefree (qdr hd),
    Nat.div_self (qbE (fun i => Nat.pos_of_ne_zero (hd i).ne_zero)), one_mul]
theorem qkJ {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : qaA 0 d = (qm d : ℂ)⁻¹ := by
  simp only [qaA, Nat.cast_zero, sub_zero, Finset.prod_inv_distrib]
  rw [qfX hd, Nat.cast_prod]
theorem qk8 {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : qaA 1 d = ((qm d).totient : ℂ)⁻¹ := by
  simp only [qaA, Nat.cast_one, Finset.prod_inv_distrib]
  rw [qfY hd, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  simp only [Nat.cast_sub p.property.one_le, Nat.cast_one]
open scoped ContDiff
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
noncomputable def qf (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, EuclideanSpace.proj i
@[simp] theorem qcN {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    qf ι v = ∑ i, v i := by simp [qf]
noncomputable def qba {ι : Type*} (L : ℝ) (d : ι → ℕ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.log (d i)/L)
@[simp] theorem qkK {ι : Type*} (L : ℝ) (d : ι → ℕ) (i : ι) :
    qba L d i = Real.log (d i)/L := rfl
noncomputable def qab {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (1+Complex.I*(u i : ℂ))/(L:ℂ)
@[simp] theorem qna {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) :
    (qab L u i).re = L⁻¹ := by
  simp [qab, Complex.div_ofReal_re]
theorem qeP {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (z w : ι → ℂ) (h : ∀ i, (z i).re=(w i).re) :
    ‖qk δ d z‖ = ‖qk δ d w‖ := by
  simp only [qk, norm_mul, Complex.norm_exp, Complex.neg_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, h]
theorem qbI {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (L : ℝ) (u : EuclideanSpace ℝ ι) :
    ‖qk δ d (qab L u)‖ =
      ‖qk δ d (fun _ => (L⁻¹:ℝ))‖ := by
  apply qeP
  intro i
  simp
theorem qb7 {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ ι => qk δ d (qab L u)) := by
  unfold qk qab
  fun_prop
theorem qme {ι : Type*} [Fintype ι] (L : ℝ) (d : ι → ℕ)
    (u : EuclideanSpace ℝ ι) :
    (∑ i, (Real.log (d i):ℂ)*qab L u i) =
      (qf ι (qba L d) : ℂ) +
        Complex.I*(inner ℝ u (qba L d) : ℂ) := by
  simp only [qcN, Complex.ofReal_sum, PiLp.inner_apply,
    Real.inner_apply, qkK, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [qab, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring
theorem qen {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    (∫ u : EuclideanSpace ℝ ι, qq (qf ι) F hF hFs u *
      qk δ d (qab L u)) =
    qaA δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      F (qba L d) := by
  simp only [qk, qme, neg_add_rev]
  rw [← qdt (qf ι) F hF hFs (qba L d),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sub_eq_add_neg]
  ring_nf
theorem qd4 {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * qk δ d (qab L u)) := by
  apply Φ.integrable.mul_bdd (qb7 δ d L).aestronglyMeasurable
  filter_upwards [] with u
  exact (qbI δ d L u).le
noncomputable def qbU {ι : Type*} [Fintype ι] (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : ℂ :=
  ∑' d : qB A,
    qaA δ d.val * (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      F (qba L d.val)
theorem qeb {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    qbU δ A L F =
      ∫ u : EuclideanSpace ℝ ι, qq (qf ι) F hF hFs u *
        ∑' d : qB A, qk δ d.val (qab L u) := by
  let : Countable (qB A) := by unfold qB; infer_instance
  let Φ := qq (qf ι) F hF hFs
  have hs := qcM hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL)
    hA hR (fun _ => le_rfl)
  have hint (d : qB A) :
      Integrable (fun u => Φ u * qk δ d.val (qab L u)) :=
    qd4 δ d.val L Φ
  have hsum : Summable (fun d : qB A =>
      ∫ u : EuclideanSpace ℝ ι, ‖Φ u*qk δ d.val (qab L u)‖) := by
    simp_rw [norm_mul, qbI, integral_mul_const]
    exact hs.mul_left _
  have he := (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq
  simp only [qen, Φ] at he
  rw [qbU, he]
  apply integral_congr_ae
  filter_upwards [] with u
  exact tsum_mul_left
theorem qdj {ι : Type*} [Fintype ι] (d b : ι → ℕ) :
    (∀ p : Nat.Primes, (qK d p).Nonempty →
      qK d p∈qam (fun i => (b i:ℤ)) p) ↔ qdy d b := by
  constructor
  · intro h p hp _ i j hi hj
    have hm := h ⟨p,hp⟩ ⟨i,by simp [qK,hi]⟩
    rw [qam, qH] at hm
    have he := hm.2 i (by simp [qK,hi]) j (by simp [qK,hj])
    change b i % p = b j % p
    exact_mod_cast he
  · intro h p hp
    rw [qam, qH]
    refine ⟨hp,?_⟩
    intro i hi j hj
    have hi' : p.val∣d i := by simpa [qK] using hi
    have hj' : p.val∣d j := by simpa [qK] using hj
    have hq : p.val∣qm d := hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))
    have he : b i % p.val=b j % p.val := h p.val p.property hq i j hi' hj'
    exact_mod_cast he
theorem qeo {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) :
    (∀ p : Nat.Primes, (qK d p).Nonempty →
      qK d p∈qS (fun i => (b i:ℤ)) p a) ↔
      qgr d b a := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · apply (qdj d b).mp
      intro p hp
      have hm := (qcm _ _ _ _).mp (h p hp)
      rw [qam,qH]
      exact ⟨hm.1,hm.2.1⟩
    · intro p hp _ i hi he
      have hm := (qcm _ _ _ _).mp
        (h ⟨p,hp⟩ ⟨i,by simp [qK,hi]⟩)
      apply hm.2.2 i (by simp [qK,hi])
      change b i % p=a % p at he
      exact_mod_cast he
  · rintro ⟨h,hmark⟩ p hp
    rw [qcm]
    have hu := (qdj d b).mpr h p hp
    rw [qam,qH] at hu
    refine ⟨hu.1,hu.2,?_⟩
    intro i hi he
    have hi' : p.val∣d i := by simpa [qK] using hi
    apply hmark p.val p.property (hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))) i hi'
    change b i % p.val=a % p.val
    exact_mod_cast he
theorem qgi {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    qbU 0 (qam (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((qg X F d * qbs d b : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (qK d p).Nonempty →
      qK d p∈qam (fun i => (b i:ℤ)) p
  change (∑' d : {d // P d}, qaA 0 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (qba (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => qaA 0 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (qba (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), qkJ hd.1]
    have hc := (qcH hd.1).mpr ((qdj d b).mp hd.2)
    simp only [qg,qbs,if_pos hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change (qm d : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (q1 X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : qg X F d * qbs d b = 0 := by
      by_contra hv
      have hf := (qas.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : qa4 d b := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [qbs,hc])
      exact hd ⟨hf,(qdj d b).mpr
        ((qcH hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]
theorem qg8 {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) (a : ℕ) :
    qbU 1 (fun p => qS (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((qg X F d * qae d b a : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (qK d p).Nonempty →
      qK d p∈qS (fun i => (b i:ℤ)) p a
  change (∑' d : {d // P d}, qaA 1 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (qba (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => qaA 1 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (qba (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), qk8 hd.1]
    have hc := (qdl hd.1).mpr ((qeo d b a).mp hd.2)
    simp only [qg,qae,if_pos hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change ((qm d).totient : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (q1 X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : qg X F d * qae d b a = 0 := by
      by_contra hv
      have hf := (qas.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : qbh d b a := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [qae,hc])
      exact hd ⟨hf,(qeo d b a).mpr
        ((qdl hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]
theorem qep {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : qV F rho)
    {d : Fin n → ℕ} (hd : qg X F d≠0) :
    d ∈ qau n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  obtain ⟨hsq,hF⟩ := qas.mp hd
  have hp : ∀ i, 0<d i := fun i => Nat.pos_of_ne_zero (hsq i).ne_zero
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,?_⟩
  · intro i
    exact Finset.mem_Icc.mpr ⟨hp i,qeV hX hbudget hp hF i⟩
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr (qdP hX hbudget hp hF)
theorem qeQ {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : qV F rho) (b : Fin n → ℕ) :
    qbU 0 (qam (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (qbF X F rho b : ℂ) := by
  rw [qgi,qbF,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : qg X F d=0 := by
    by_contra hc
    exact hd (qep hX hbudget hc)
  simp only [hc,zero_mul,Complex.ofReal_zero]
theorem qfk {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : qV F rho) (b : Fin n → ℕ) (a : ℕ) :
    qbU 1 (fun p => qS (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (qb2 X F rho b a : ℂ) := by
  rw [qg8,qb2,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : qg X F d=0 := by
    by_contra hc
    exact hd (Finset.mem_filter.mpr ⟨qep hX hbudget hc,
      (qas.mp hc).1⟩)
  simp only [hc,zero_mul,Complex.ofReal_zero]
theorem qhW {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (K : EuclideanSpace ℝ ι → ℂ)
    {R B : ℝ} (hR : 0<R) (hB : 0≤B) (hKm : AEStronglyMeasurable K volume)
    (hK : ∀ u, ‖K u‖≤B) (k : ℕ) :
    ‖∫ u in {u | R<‖u‖}, Φ u*K u‖ ≤
      (B/R^k) * ∫ u, ‖u‖^k*‖Φ u‖ := by
  let S : Set (EuclideanSpace ℝ ι) := {u | R<‖u‖}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hp : Integrable (fun u => Φ u*K u) :=
    Φ.integrable.mul_bdd hKm (Filter.Eventually.of_forall hK)
  have ht : Integrable (fun u : EuclideanSpace ℝ ι => ‖u‖^k*‖Φ u‖) :=
    SchwartzMap.integrable_pow_mul volume Φ k
  have hm : ∀ᵐ u ∂volume.restrict S,
      ‖Φ u*K u‖ ≤ (B/R^k)*(‖u‖^k*‖Φ u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hpow : R^k≤‖u‖^k := pow_le_pow_left₀ hR.le hu.le k
    rw [norm_mul]
    have hpower : 1≤‖u‖^k/R^k := (one_le_div (pow_pos hR k)).mpr hpow
    calc
      ‖Φ u‖*‖K u‖ ≤ ‖Φ u‖*B := mul_le_mul_of_nonneg_left (hK u) (norm_nonneg _)
      _ ≤ (‖Φ u‖*B)*(‖u‖^k/R^k) := le_mul_of_one_le_right (by positivity) hpower
      _ = (B/R^k)*(‖u‖^k*‖Φ u‖) := by ring
  calc
    _ ≤ ∫ u in S, ‖Φ u*K u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      integral_mono_ae hp.integrableOn.norm ((ht.const_mul _).integrableOn) hm
    _ ≤ ∫ u, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      setIntegral_le_integral (ht.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := integral_const_mul _ _
theorem qdW {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) :
    Continuous (fun u : EuclideanSpace ℝ ι =>
      ∑' d : qB A, qk δ d.val (qab L u)) := by
  refine continuous_tsum (fun d => qb7 δ d.val L)
    (qcM hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL) hA hR
      (fun _ => by simp)) ?_
  intro d u
  exact (qbI δ d.val L u).le
theorem qdX {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (u : EuclideanSpace ℝ ι) :
    ‖∑' d : qB A, qk δ d.val (qab L u)‖ ≤
    Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) := by
  exact (norm_tsum_le_tsum_norm (qcM hδ A _ (inv_pos.mpr hL)
    hA hR (by intro i; simp))).trans
    (qjl hδ A _ (inv_pos.mpr hL) hA hR (by intro i; simp))
theorem qiP {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L U : ℝ} (hL : 0<L) (hU : 0<U)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    ‖∫ u in {u | U<‖u‖}, Φ u *
      (∑' d : qB A, qk δ d.val (qab L u))‖ ≤
      (Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k) *
        ∫ u, ‖u‖^k*‖Φ u‖ := by
  apply qhW Φ _ hU (Real.exp_pos _).le
    (qdW hδ A hL hA hR).aestronglyMeasurable
    (qdX hδ A hL hA hR)
theorem qgj :
    ∃ L₀>0, ∀ L : ℝ, L₀≤L → ∀ R : ℕ,
      Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) ≤ ((3/2)*L)^(2*R) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := qhJ
  refine ⟨1+ε⁻¹,by positivity,fun L hL R => ?_⟩
  have hL0 : 0<L := lt_of_lt_of_le (by positivity) hL
  have heL : L⁻¹<ε := (inv_lt_comm₀ hL0 hε).mpr (by linarith)
  have hnorm : ‖(L⁻¹:ℂ)‖=L⁻¹ := by
    rw [show (L⁻¹:ℂ)=((L⁻¹:ℝ):ℂ) by simp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hL0)]
  have hb := (hpole (L⁻¹:ℂ) (inv_ne_zero (by exact_mod_cast hL0.ne')) (by rw [hnorm]; exact heL)).2.2
  rw [norm_mul,hnorm] at hb
  have hz : (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re ≤ (3/2)*L := by
    have hcast : ((1+L⁻¹:ℝ):ℂ)=1+(L⁻¹:ℂ) := by simp
    rw [hcast]
    apply (Complex.re_le_norm _).trans
    calc
      _ = L * (L⁻¹ * ‖riemannZeta (1+(L⁻¹:ℂ))‖) := by field_simp
      _ ≤ L*(3/2) := mul_le_mul_of_nonneg_left hb hL0.le
      _ = _ := by ring
  have hzpos : 0<(riemannZeta ((1+L⁻¹:ℝ):ℂ)).re :=
    riemannZeta_re_pos_of_one_lt (by linarith [inv_pos.mpr hL0])
  calc
    _ = (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re^(2*R) := by
      rw [show (2:ℝ)*R=((2*R:ℕ):ℝ) by norm_cast,Real.exp_nat_mul,Real.exp_log hzpos]
    _ ≤ _ := pow_le_pow_left₀ hzpos.le hz _
theorem qjm {ι : Type*} (i : ι) :
    qaI {i} = {{i}} := by
  classical
  ext S
  simp [qaI,Finset.subset_singleton_iff]
  aesop
theorem qlB {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) :
    qaI {i,j} = {{i},{j},{i,j}} := by
  classical
  ext S
  simp only [qaI, Finset.mem_erase, Finset.mem_powerset,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hne,he⟩
    have h : S=∅ ∨ S={i} ∨ S={j} ∨ S={i,j} := by
      have hp := Finset.mem_powerset.mpr he
      simp [Finset.powerset_insert] at hp
      aesop
    exact h.resolve_left (hne)
  · rintro (rfl|rfl|rfl) <;> simp
theorem qk9 {ι : Type*} (i : ι) (w : ι → ℂ) :
    qc6 {i} w = w i := by
  simp [qc6,qjm]
theorem qmA {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) (w : ι → ℂ) :
    qc6 {i,j} w = w i*w j/(w i+w j) := by
  rw [qc6,qlB hij]
  have h1 : ({j} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij]
  have h2 : ({i} : Finset ι)≠{j} := by simp [hij]
  have h3 : ({i} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij.symm]
  simp [h1,h2,h3,hij,div_eq_mul_inv]
  ring
@[simp] theorem qe6 (y : ℕ) :
    qC y = ∑ p∈Nat.primesLE y, (1:ℝ)/p := by
  simp only [qC,qaK,one_div]
  exact Finset.sum_subtype_of_mem (fun p : ℕ => (p:ℝ)⁻¹) (fun p hp => (Nat.mem_primesLE.mp hp).2)
theorem qeG : Monotone qM := by
  intro m n hmn
  unfold qM
  gcongr
  norm_num
theorem qct (y : ℕ) : 0≤qC y := by
  unfold qC
  exact Finset.sum_nonneg (fun _ _ => by positivity)
theorem qkL {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    Real.exp x-1≤2*x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x:=x) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx] at h
  have hh := (abs_le.mp h).2
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
noncomputable def qaN (R : ℕ) (s : ℝ) (y : ℕ) : ℝ :=
  Real.exp (4*R*qC y)*
    (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*qC y+
      2*(Real.exp (qM R/(y:ℝ))-1))
theorem qjn {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) {s : ℝ}
    (hzsmall : ∑ i, ‖z i‖ ≤ (y:ℝ)^(-s)) :
    ‖qav δ A B z-qav δ A B (fun _ => 0)‖ ≤ qaN R s y := by
  apply (qkG hδ A B z hz hy hA hB hgen).trans
  unfold qaN
  have hlog : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hr := qct y
  have hK := qeG hB
  gcongr
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
theorem qck (a : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => (Real.log (y:ℝ))^a/(y:ℝ)^s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop a hs).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
theorem qjo (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (qaN R s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp a
  let K : ℝ := qM R
  let E₁ : ℕ → ℝ := fun y => (M*Real.exp (2*R)*6*R*c)*
    ((Real.log (y:ℝ))^(a+2)/(y:ℝ)^s)
  let E₂ : ℕ → ℝ := fun y => (4*M*K)*((Real.log (y:ℝ))^a/(y:ℝ))
  have h₁ : Tendsto E₁ atTop (𝓝 0) := by
    simpa only [mul_zero,E₁] using (qck (a+2) hs).const_mul _
  have h₂ : Tendsto E₂ atTop (𝓝 0) := by
    simpa only [mul_zero,Real.rpow_one,E₂] using
      (qck a (s:=1) zero_lt_one).const_mul (4*M*K)
  have he : ∀ᶠ y : ℕ in atTop, 0≤qaN R s y ∧
      qaN R s y ≤ E₁ y+E₂ y := by
    have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [qc5, ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (max K 1)] with y hr hl hy
    change 1 ≤ Real.log (y:ℝ) at hl
    have hy0 : (0:ℝ)<y := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hy)
    have hK0 : 0≤K := qbp R
    have hKy : K/(y:ℝ)≤1 := (div_le_one hy0).mpr ((le_max_left _ _).trans hy)
    have hp0 := qct y
    have hr' : qC y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [qe6,c] using hr
    have hr'' : qC y ≤ c*Real.log y := by
      apply hr'.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith [Real.log_le_sub_one_of_pos (show 0<Real.log (y:ℝ) by linarith)]
    have hp : Real.exp (4*R*qC y) ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))) := by gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos (show 0<Real.log (y:ℝ) by linarith)]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    have hex : Real.exp (K/(y:ℝ))-1 ≤ 2*(K/(y:ℝ)) :=
      qkL (by positivity) hKy
    have hnonneg : 0≤Real.exp (K/(y:ℝ))-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
    constructor
    · unfold qaN
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
    · calc
        _ ≤ (M*(Real.log (y:ℝ))^a)*
              (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*(c*Real.log y)+4*K/(y:ℝ)) := by
            unfold qaN
            apply mul_le_mul hp ?_ (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
              (by positivity)
            gcongr
            calc
              _ ≤ 2*(2*(K/(y:ℝ))) := mul_le_mul_of_nonneg_left hex (by norm_num)
              _ = _ := by ring
        _ = E₁ y+E₂ y := by
          dsimp only [E₁,E₂]
          rw [Real.rpow_neg hy0.le,Real.rpow_add (show 0<Real.log (y:ℝ) by linarith),Real.rpow_two]
          ring
  apply squeeze_zero'
  · exact he.mono (fun _ => And.left)
  · exact he.mono (fun _ => And.right)
  · simpa only [add_zero] using h₁.add h₂
section FourierDerivative
open scoped FourierTransform SchwartzMap ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open LineDeriv
theorem qkj (G : SchwartzMap V ℂ) (m u : V) :
    qaL (∂_{m} G) u = -Complex.I*(inner ℝ u m:ℂ)*qaL G u := by
  have hg : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp only [qaL,SchwartzMap.fourierInv_lineDerivOp_eq,
    smul_apply,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    qfv,SchwartzMap.smulLeftCLM_apply hg,real_inner_smul_left,
    smul_eq_mul,Complex.real_smul]
  push_cast
  field_simp
theorem qmr (G H : SchwartzMap V ℂ) (u : V) :
    qaL (G+H) u = qaL G u+qaL H u := by
  simp only [qaL, FourierTransform.fourierInv_add, map_add, smul_add, add_apply]
theorem qfw (c : ℂ) (G : SchwartzMap V ℂ) (u : V) :
    qaL (c • G) u = c*qaL G u := by
  simp only [qaL, FourierTransform.fourierInv_smul, map_smul, smul_apply,Complex.real_smul,smul_eq_mul]
  ring
noncomputable def qda (ℓ : V →L[ℝ] ℝ) (m : V) (G : SchwartzMap V ℂ) :
    SchwartzMap V ℂ := (ℓ m : ℂ) • G + (-1:ℂ) • (∂_{m} G)
theorem qg9 (ℓ : V →L[ℝ] ℝ) (m : V)
    (G : SchwartzMap V ℂ) (u : V) :
    qaL (qda ℓ m G) u =
      ((ℓ m : ℂ)+Complex.I*(inner ℝ u m:ℂ))*qaL G u := by
  rw [qda, qmr, qfw,
    qfw, qkj]
  ring
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qkM (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m v : V) :
    qda ℓ m (qdC ℓ F hF hFs) v =
      Complex.exp (ℓ v : ℂ)*(-fderiv ℝ F v m) := by
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp v ℓ.hasFDerivAt
  have he := hlin.cexp
  have hf := he.mul ((hFs.differentiable (by simp)).differentiableAt.hasFDerivAt (x := v))
  simp only [qda, add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, qgy]
  change (ℓ m:ℂ)*(Complex.exp (ℓ v:ℂ)*F v) +
    -1*(fderiv ℝ (fun v => Complex.exp (ℓ v:ℂ)*F v) v m) = _
  have hd := congrArg (fun A : V →L[ℝ] ℂ => A m) hf.fderiv
  simp only [Function.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul] at hd
  change (fderiv ℝ (fun x => Complex.exp (ℓ x:ℂ)*F x) v) m =
    Complex.exp (ℓ v:ℂ)*fderiv ℝ F v m + F v*(Complex.exp (ℓ v:ℂ)*(ℓ m:ℂ)) at hd
  rw [hd]
  ring
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qdb (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) (m : V) :
    ContDiff ℝ ∞ (fun v => -fderiv ℝ F v m) := by
  exact (hFs.fderiv_right (by simp)).clm_apply contDiff_const |>.neg
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qgk (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m : V) :
    qda ℓ m (qdC ℓ F hF hFs) =
      qdC ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (qdb F hFs m) := by
  ext v
  exact qkM ℓ F hF hFs m v
theorem qhu (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m u : V) :
    qq ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (qdb F hFs m) u =
      ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ))*qq ℓ F hF hFs u := by
  unfold qq
  rw [← qgk, qg9]
noncomputable def qI (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qbJ (ms : List V) (F : V → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (qI ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qbR (ms : List V) (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (qI ms F) := by
  induction ms with
  | nil => exact hFs
  | cons m ms ih => exact qdb _ ih m
theorem qdE (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (u : V) :
    qq ℓ (qI ms F) (qbJ ms F hF)
        (qbR ms F hFs) u =
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
        qq ℓ F hF hFs u := by
  induction ms with
  | nil => simp [qI]
  | cons m ms ih =>
    change qq ℓ (fun v => -fderiv ℝ (qI ms F) v m) _ _ u = _
    rw [qhu ℓ (qI ms F)
      (qbJ ms F hF) (qbR ms F hFs),ih]
    simp only [List.map_cons,List.prod_cons,mul_assoc]
theorem qcW (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, qq ℓ F hF hFs u *
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
      Complex.exp (-(ℓ v:ℂ)-Complex.I*(inner ℝ u v:ℂ))) = qI ms F v := by
  rw [← qdt ℓ (qI ms F)
    (qbJ ms F hF) (qbR ms F hFs) v]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [qdE,mul_comm (qq ℓ F hF hFs u)]
end FourierDerivative
noncomputable def qaj {ι : Type*} (B : Finset (Finset ι)) (w : ι → ℂ) : ℂ :=
  ∏ S∈B, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))
noncomputable def qbC {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, ((∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i))^((-1:ℤ)^S.card)
theorem qlY {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (w : ι → ℂ) :
    qaj (qx b R) w =
      ∏ r∈R, qc6 (Finset.univ.filter fun i => b i=r) w := by
  classical
  unfold qaj qx qc6
  rw [Finset.prod_biUnion]
  intro r _ s _ hrs
  exact qdn b hrs
theorem qjO {ι : Type*} (B : Finset (Finset ι))
    (w : ι → ℂ) {c : ℂ} (hc : c≠0) {t : ℕ}
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    qaj B (fun i => c*w i) = c^t*qaj B w := by
  classical
  unfold qaj
  simp_rw [← Finset.mul_sum,mul_zpow]
  rw [Finset.prod_mul_distrib,qkw _ _ hc,Finset.sum_neg_distrib,ht,
    neg_neg,zpow_natCast]
theorem qha {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hz : ∀ S∈B, ∑ i∈S, z i≠0) :
    qb4 B z=qaj B z*qbC B z := by
  classical
  unfold qb4 qaj qbC
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  rw [mul_zpow,← mul_assoc,← zpow_add₀ (hz S hS),neg_add_cancel,zpow_zero,one_mul]
theorem qhX {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {U : ℝ} (hU : 0≤U) (hu : ∀ i, |u i|≤U) :
    ‖qaj B (fun i => qz (u i))‖ ≤
      ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ)^B.card := by
  have hbase : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ)*(1+U) := by
    have h : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ) := by exact_mod_cast le_max_right _ _
    nlinarith
  rw [qaj,norm_prod]
  calc
    _ ≤ ∏ _S∈B, ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro S hS
      rcases neg_one_pow_eq_or ℤ S.card with h | h
      · rw [h,zpow_neg_one,norm_inv]
        exact (inv_le_one_of_one_le₀ (qft (hB S hS) u)).trans hbase
      · rw [h,neg_neg,zpow_one]
        apply (qfu S u (fun i _ => hu i)).trans
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_univ S).trans (le_max_left _ _)
    _ = _ := by simp
theorem qir {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hz : ∀ S∈B,
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)-1‖≤c*ε ∧
      1/2≤‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖ ∧
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖≤3/2) :
    ‖qbC B z-1‖ ≤ 2^B.card*(B.card*(2*c*ε)) := by
  apply qlu _ _ (by norm_num : (1:ℝ)≤2)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      linarith [(hz S hS).2.2]
    · rw [h,zpow_neg_one,norm_inv]
      exact (inv_le_comm₀ (by linarith [(hz S hS).2.1] :
        0<‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖) (by norm_num)).mpr
        (by simpa only [one_div] using (hz S hS).2.1)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      nlinarith [(hz S hS).1]
    · rw [h,zpow_neg_one]
      exact (qlV (hz S hS).2.1).trans (by nlinarith [(hz S hS).1])
theorem qhY :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] (B : Finset (Finset ι)),
      (∀ S∈B, S.Nonempty) → ∀ u : ι → ℝ, ∀ {L U : ℝ}, 0<L → 0≤U →
      (∀ i, |u i|≤U) → (Fintype.card ι:ℝ)*(1+U)/L<ε →
      ‖qbC B (fun i => qz (u i)/(L:ℂ))-1‖ ≤
        2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := qhJ
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ B hB u L U hL hU hu hsmall
  apply qir B _ hc (by positivity)
  intro S hS
  have hsum : (∑ i∈S, qz (u i)/(L:ℂ)) =
      (∑ i∈S, qz (u i))/(L:ℂ) := (Finset.sum_div _ _ _).symm
  have hnz : (∑ i∈S, qz (u i)/(L:ℂ))≠0 := by
    rw [hsum]
    exact div_ne_zero (qei (hB S hS) u) (by exact_mod_cast hL.ne')
  have hn : ‖∑ i∈S, qz (u i)/(L:ℂ)‖ ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
    rw [hsum,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    apply (qfu S u (fun i _ => hu i)).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) (by positivity)
  have hp := hpole _ hnz (hn.trans_lt hsmall)
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_left hn hc.le), hp.2⟩
theorem qeR {ι : Type*}
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*qb4 B (fun i => qz (u i)/(L:ℂ)) =
      qaj B (fun i => qz (u i))*
        qbC B (fun i => qz (u i)/(L:ℂ)) := by
  have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hnz : ∀ S∈B, ∑ i∈S, qz (u i)/(L:ℂ)≠0 := by
    intro S hS
    rw [← Finset.sum_div]
    exact div_ne_zero (qei (hB S hS) u) hLc
  have hk : qaj B (fun i => qz (u i)/(L:ℂ)) =
      (L:ℂ)⁻¹^t*qaj B (fun i => qz (u i)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      qjO B (fun i => qz (u i)) (inv_ne_zero hLc) ht
  rw [qha _ _ hnz,hk,inv_pow,← mul_assoc,← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero t hLc),one_mul]
noncomputable def q0 (R y : ℕ) : ℝ :=
  Real.exp (4*R*qC y+qM R/(y:ℝ))
theorem qhL {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 0<y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖qav δ A B z‖ ≤ q0 R y := by
  have hf := qcK hδ A B z hz hy hgen
  have ht := qeF (hf.subtype (fun p => p∉qaK y))
  have htail := qg4 hδ A B z hz hy hgen
  have hpref : ‖∏ p∈qaK y, qa1 p δ (A p) B z‖ ≤
      Real.exp (4*R*qC y) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ p∈qaK y, Real.exp (4*R*(p:ℝ)⁻¹) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro p _
        apply (qk7 p.property.two_le hδ (A p) B z hz).trans
        apply Real.exp_le_exp.mpr
        have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
        have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
        have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
        nlinarith
      _ = _ := by rw [← Real.exp_sum]; congr 1; simp [qC,Finset.mul_sum]
  have hn : ‖∏' p : {p : Nat.Primes // p∉qaK y}, qa1 p.val δ (A p.val) B z‖ ≤
      Real.exp (qM R/(y:ℝ)) := by
    have hh := norm_le_norm_sub_add (∏' p : {p : Nat.Primes // p∉qaK y},
      qa1 p.val δ (A p.val) B z) 1
    rw [norm_one] at hh
    have he : Real.exp (∑' p : {p : Nat.Primes // p∉qaK y},
      ‖qa1 p.val δ (A p.val) B z-1‖) ≤ Real.exp (qM R/(y:ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply htail.trans
      exact div_le_div_of_nonneg_right (qeG hB) (by positivity)
    linarith
  unfold qav
  rw [qfV (qaK y) hf,norm_mul]
  apply (mul_le_mul hpref hn (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  exact (Real.exp_add _ _).symm
theorem qfZ {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (hB : ∀ S∈B, S.Nonempty) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B)
    (u : ι → ℝ) {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*(∑' d : qB A,
      qk δ d.val (fun i => qz (u i)/(L:ℂ))) =
      qav δ A B (fun i => qz (u i)/(L:ℂ))*
      qaj B (fun i => qz (u i))*
      qbC B (fun i => qz (u i)/(L:ℂ)) := by
  have hz (i : ι) : (qz (u i)/(L:ℂ)).re = 1/L := by
    simp [qz,Complex.div_re]
  have hn (i : ι) : 0≤(qz (u i)/(L:ℂ)).re := by rw [hz]; positivity
  have hH := qa2
    (qcK hδ A B _ hn hy hgen)
  rw [qkI hδ A B _ (by positivity : 0<1/L) hA hR
    (fun i => (hz i).ge) hB hH.hasProd]
  have he := qeR B hB u ht hL
  change (L:ℂ)^t*(qav δ A B _*_) = _
  calc
    _ = qav δ A B _*((L:ℂ)^t*qb4 B _) := by ring
    _ = _ := by rw [he]; ring
theorem qlZ {H H₀ K N : ℂ} {E M Z : ℝ}
    (hE : ‖H-H₀‖≤E) (hM : ‖H₀‖≤M) (hZ : ‖N-1‖≤Z) :
    ‖H*K*N-H₀*K‖ ≤ ‖K‖*(E*(1+Z)+M*Z) := by
  have he0 : 0≤E := (norm_nonneg _).trans hE
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hN : ‖N‖≤1+Z := by
    have := norm_le_norm_sub_add N 1
    rw [norm_one] at this
    linarith
  calc
    _ = ‖K*((H-H₀)*N+H₀*(N-1))‖ := by congr 1; ring
    _ ≤ ‖K‖*(‖H-H₀‖*‖N‖+‖H₀‖*‖N-1‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [norm_mul] using (norm_add_le ((H-H₀)*N) (H₀*(N-1)))) (norm_nonneg _)
    _ ≤ _ := by gcongr
theorem qhb :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (∑ i, ‖qz (u i)/(L:ℂ)‖)≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : qB A,
        qk δ d.val (fun i => qz (u i)/(L:ℂ))) -
        qav δ A B (fun _ => 0)*qaj B (fun i => qz (u i))‖ ≤
      ‖qaj B (fun i => qz (u i))‖*
        (qaN R s y*(1+2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))+
         q0 R y*(2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := qhY
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  rw [qfZ hδ A B hA hR hB (by omega) hgen u ht hL]
  apply qlZ
  · exact qjn hδ A B _
      (fun i => by simp [qz,Complex.div_re]; positivity) hy hR hBR hgen hzsmall
  · exact qhL hδ A B _ (by simp) (by omega) hR hBR hgen
  · exact hpole B hB u hL hU hu hsmall
noncomputable def qW {ι : Type*} (B : Finset (Finset ι))
    (u : EuclideanSpace ℝ ι) : ℂ := qaj B (fun i => qz (u i))
theorem qe7 {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) : Continuous (qW B) := by
  unfold qW qaj
  apply continuous_finsetProd
  intro S hS
  apply Continuous.zpow₀
  · apply continuous_finsetSum
    intro i _
    unfold qz
    fun_prop
  · intro u
    exact Or.inl (qei (hB S hS) (fun i => u i))
theorem qdK {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : EuclideanSpace ℝ ι) :
    ‖qW B u‖ ≤ ((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1)*(1+‖u‖^B.card) := by
  apply (qhX B hB (fun i => u i) (norm_nonneg _)
    (fun i => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i)).trans
  rw [mul_pow,mul_assoc]
  gcongr
  simpa only [one_pow] using add_pow_le (by norm_num : (0:ℝ)≤1) (norm_nonneg u) B.card
theorem qeq {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    Integrable (fun u => ‖Φ u‖*(1+‖u‖^k)) := by
  have hi := Φ.integrable.norm.add (SchwartzMap.integrable_pow_mul volume Φ k)
  apply hi.congr
  filter_upwards [] with u
  dsimp; ring
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
theorem qbW {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) :
    Integrable (fun u => Φ u*qW B u) := by
  have hm := (qeq Φ B.card).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hm.mono' ((Φ.continuous.mul (qe7 B hB)).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [norm_mul]
  calc
    _ ≤ ‖Φ u‖*(((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1)*(1+‖u‖^B.card)) :=
      mul_le_mul_of_nonneg_left (qdK B hB u) (norm_nonneg _)
    _ = _ := by ring
noncomputable def qE {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℂ :=
  ∫ u, Φ u*qW B u
noncomputable def qbX {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℝ :=
  ∫ u, ‖Φ u*qW B u‖
theorem qjP {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty)
    (S : Set (EuclideanSpace ℝ ι)) (hS : MeasurableSet S)
    (f : EuclideanSpace ℝ ι → ℂ) (hf : IntegrableOn (fun u => Φ u*f u) S)
    (H : ℂ) {E : ℝ} (hE : 0≤E)
    (he : ∀ u∈S, ‖f u-H*qW B u‖≤‖qW B u‖*E) :
    ‖(∫ u in S, Φ u*f u)-H*(∫ u in S, Φ u*qW B u)‖ ≤
      qbX Φ B*E := by
  have hi := qbW Φ B hB
  have hH : IntegrableOn (fun u => Φ u*(H*qW B u)) S := by
    simpa only [mul_left_comm] using (hi.const_mul H).integrableOn (s:=S)
  have hiH : H*(∫ u in S, Φ u*qW B u) =
      ∫ u in S, Φ u*(H*qW B u) := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hiH,← integral_sub hf hH]
  calc
    _ ≤ ∫ u in S, ‖Φ u*f u-Φ u*(H*qW B u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, ‖Φ u*qW B u‖*E := by
      apply integral_mono_ae (hf.sub hH).norm (hi.norm.mul_const E).integrableOn
      filter_upwards [ae_restrict_mem hS] with u hu
      simp only [Pi.sub_apply]
      rw [← mul_sub,norm_mul,norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (he u hu) (norm_nonneg (Φ u))]
    _ ≤ ∫ u, ‖Φ u*qW B u‖*E :=
      setIntegral_le_integral (hi.norm.mul_const E) (by filter_upwards [] with u; positivity)
    _ = qbX Φ B*E := by rw [integral_mul_const]; rfl
theorem qcE (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => q0 R y/(y:ℝ)^s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp (a+qM R)
  have hlim := (qck a hs).const_mul M
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using hlim)
  · filter_upwards [] with y
    unfold q0
    positivity
  · have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [qc5,
      ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 1] with y hr hl hy
    change 1≤Real.log (y:ℝ) at hl
    have hly : 0<Real.log (y:ℝ) := by linarith
    have hr' : qC y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [qe6,c] using hr
    have hK : qM R/(y:ℝ)≤qM R :=
      div_le_self (qbp R) hy
    have hb : q0 R y ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))+qM R) := by
          unfold q0
          gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos hly]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      _ ≤ (M*(Real.log (y:ℝ))^a)/(y:ℝ)^s :=
        div_le_div_of_nonneg_right hb (Real.rpow_nonneg (by positivity) _)
      _ = M*((Real.log (y:ℝ))^a/(y:ℝ)^s) := by ring
noncomputable def qbr (R : ℕ) (c s : ℝ) (y : ℕ) : ℝ :=
  qaN R s y*(1+(2^R*(R*(2*c)))*(y:ℝ)^(-s))+
    q0 R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)
theorem qjQ (R : ℕ) (c : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (qbr R c s) atTop (𝓝 0) := by
  have hy : Tendsto (fun y : ℕ => (y:ℝ)^(-s)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₁ := (qjo R hs).mul
    ((tendsto_const_nhds (x:=(1:ℝ))).add (hy.const_mul (2^R*(R*(2*c)))))
  have h₂ := (qcE R hs).mul_const (2^R*(R*(2*c)))
  have he : (fun y : ℕ => q0 R y/(y:ℝ)^s*(2^R*(R*(2*c)))) =
      (fun y : ℕ => q0 R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)) := by
    ext y
    rw [Real.rpow_neg (by positivity : (0:ℝ)≤y)]
    ring
  rw [he] at h₂
  unfold qbr
  simpa only [zero_mul,mul_zero,add_zero,zero_add] using h₁.add h₂
theorem qd5 {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ) :
    Integrable (fun u => ‖u‖^k*‖Φ u*qW B u‖) := by
  have hi := ((SchwartzMap.integrable_pow_mul volume Φ k).add
    (SchwartzMap.integrable_pow_mul volume Φ (k+B.card))).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hi.mono' ((continuous_norm.pow k).mul
    ((Φ.continuous.mul (qe7 B hB)).norm)).aestronglyMeasurable
  filter_upwards [] with u
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity),norm_mul]
  calc
    _ ≤ ‖u‖^k*(‖Φ u‖*((((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1))*(1+‖u‖^B.card))) := by
      gcongr; exact qdK B hB u
    _ = _ := by rw [pow_add]; ring
theorem qiQ {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℂ)
    (hf : Integrable f μ) (k : ℕ) (hk : Integrable (fun u => ‖u‖^k*‖f u‖) μ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, f u ∂μ‖ ≤ (∫ u, ‖u‖^k*‖f u‖ ∂μ)/U^k := by
  let S : Set V := {u | U<‖u‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hbound : ∀ᵐ u ∂μ.restrict S, ‖f u‖≤(U^k)⁻¹*(‖u‖^k*‖f u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hp : U^k≤‖u‖^k := pow_le_pow_left₀ hU.le hu.le k
    have hdiv : 1≤(U^k)⁻¹*‖u‖^k := by
      rw [← div_eq_inv_mul]
      exact (one_le_div (pow_pos hU k)).mpr hp
    calc
      _ ≤ ((U^k)⁻¹*‖u‖^k)*‖f u‖ := by nlinarith [norm_nonneg (f u)]
      _ = _ := by ring
  calc
    _ ≤ ∫ u in S, ‖f u‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      integral_mono_ae hf.integrableOn.norm ((hk.const_mul _).integrableOn) hbound
    _ ≤ ∫ u, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      setIntegral_le_integral (hk.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := by rw [integral_const_mul]; ring
theorem qiR {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, Φ u*qW B u‖ ≤
      (∫ u, ‖u‖^k*‖Φ u*qW B u‖)/U^k :=
  qiQ volume _ (qbW Φ B hB) k
    (qd5 Φ B hB k) hU
theorem qe8 (R : ℕ) (s : ℝ) {y : ℕ} (hy : 1≤y) :
    0≤qaN R s y := by
  have hl : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy)
  have hp := qct y
  have he : 0≤Real.exp (qM R/(y:ℝ))-1 :=
    sub_nonneg.mpr (Real.one_le_exp (by
      exact div_nonneg (qbp R) (by positivity)))
  unfold qaN
  positivity
theorem qkk (R : ℕ) {c : ℝ} (hc : 0≤c) (s : ℝ)
    {y : ℕ} (hy : 1≤y) : 0≤qbr R c s y := by
  have he := qe8 R s hy
  have hm : 0≤q0 R y := (Real.exp_pos _).le
  unfold qbr
  positivity
theorem qiS {ι : Type*} [Fintype ι] (u : ι → ℝ)
    {L U : ℝ} (hL : 0<L) (hu : ∀ i, |u i|≤U) :
    (∑ i, ‖qz (u i)/(L:ℂ)‖) ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
  calc
    _ ≤ ∑ _i : ι, (1+U)/L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      apply div_le_div_of_nonneg_right _ hL.le
      exact (qkx (u i)).trans (by linarith [hu i])
    _ = _ := by simp; ring
theorem qez :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : qB A,
        qk δ d.val (fun i => qz (u i)/(L:ℂ))) -
        qav δ A B (fun _ => 0)*qaj B (fun i => qz (u i))‖ ≤
      ‖qaj B (fun i => qz (u i))‖*qbr R c s y := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := qhb
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  apply (hcore hδ A B hA hR hB hBR hy hgen u ht hL hU hu hsmall
    ((qiS u hL hu).trans hzsmall)).trans
  have hE := qe8 R s (show 1≤y by omega)
  have hCB : (B.card:ℝ)≤R := by exact_mod_cast hBR
  have h2 : (2:ℝ)^B.card≤2^R := pow_le_pow_right₀ (by norm_num) hBR
  have hζ : 2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) ≤
      (2^R*(R*(2*c)))*(y:ℝ)^(-s) := by
    calc
      _ ≤ 2^R*(R*(2*c*(y:ℝ)^(-s))) := by gcongr
      _ = _ := by ring
  unfold qbr
  have hM : 0≤q0 R y := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hζ hM
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add_right hζ 1) hE
  · calc
      _ ≤ q0 R y*((2^R*(R*(2*c)))*(y:ℝ)^(-s)) := hmul
      _ = _ := by ring
theorem qgl {ι : Type*} [Fintype ι] {δ R : ℕ}
    (hδ : δ≤1) (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * (∑' d : qB A,
      qk δ d.val (qab L u))) := by
  exact Φ.integrable.mul_bdd
    (qdW hδ A hL hA hR).aestronglyMeasurable
    (Filter.Eventually.of_forall (qdX hδ A hL hA hR))
theorem qjR {V : Type*} [MeasurableSpace V]
    (μ : Measure V) (f g : V → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (S : Set V) (hS : MeasurableSet S) (H : ℂ) {E : ℝ}
    (he : ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖≤E) :
    ‖(∫ u, f u ∂μ)-H*(∫ u, g u ∂μ)‖ ≤
      E + ‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖ := by
  rw [← integral_add_compl hS hf,← integral_add_compl hS hg]
  calc
    _ = ‖((∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)) +
      ((∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ))‖ := by congr 1; ring
    _ ≤ ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖ +
      ‖(∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ)‖ := norm_add_le _ _
    _ ≤ E + (‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖) := by
      apply add_le_add he
      simpa only [norm_mul] using norm_sub_le (∫ u in Sᶜ, f u ∂μ)
        (H*(∫ u in Sᶜ, g u ∂μ))
    _ = _ := by ring
theorem qfl :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) {t : ℕ},
      (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0<U →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) → ∀ k₁ k₂ : ℕ,
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : qB A,
        qk δ d.val (qab L u))) -
        qav δ A B (fun _ => 0)*qE Φ B‖ ≤
      qbX Φ B*qbr R c s y +
      L^t*(Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k₁)*
        (∫ u, ‖u‖^k₁*‖Φ u‖) +
      q0 R y*(∫ u, ‖u‖^k₂*‖Φ u*qW B u‖)/U^k₂ := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := qez
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen Φ t ht L U s hL hU hsmall hysmall k₁ k₂
  let T := fun u : EuclideanSpace ℝ ι => ∑' d : qB A,
    qk δ d.val (qab L u)
  let S : Set (EuclideanSpace ℝ ι) := {u | ‖u‖≤U}
  have hS : MeasurableSet S := measurableSet_le continuous_norm.measurable measurable_const
  have hSc : Sᶜ={u | U<‖u‖} := by ext u; simp [S]
  have hT : Integrable (fun u => Φ u*T u) := qgl hδ A hL hA hR Φ
  have hcT : Integrable (fun u => Φ u*((L:ℂ)^t*T u)) := by
    simpa only [mul_left_comm] using hT.const_mul ((L:ℂ)^t)
  have hK := qbW Φ B hB
  have hpoint : ∀ u∈S, ‖(L:ℂ)^t*T u-qav δ A B (fun _ => 0)*
      qW B u‖≤‖qW B u‖*qbr R c s y := by
    intro u hu
    have hui : ∀ i, |u i|≤U := by
      intro i
      have hh : |u i|≤‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
      exact hh.trans hu
    exact hcore hδ A B hA hR hB hBR hy hgen (fun i => u i) ht hL hU.le hui hsmall hysmall
  have he := qjP Φ B hB S hS (fun u => (L:ℂ)^t*T u)
    hcT.integrableOn (qav δ A B (fun _ => 0))
    (qkk R hc.le s (y:=y) (by omega)) hpoint
  have hall := qjR volume (fun u => Φ u*((L:ℂ)^t*T u))
    (fun u => Φ u*qW B u) hcT hK S hS
    (qav δ A B (fun _ => 0)) he
  have hid : ∀ D : Set (EuclideanSpace ℝ ι),
      (∫ u in D, Φ u*((L:ℂ)^t*T u)) = (L:ℂ)^t*∫ u in D, Φ u*T u := by
    intro D
    rw [← integral_const_mul]
    congr 1; ext u; ring
  have hidall : (∫ u, Φ u*((L:ℂ)^t*T u))=(L:ℂ)^t*∫ u, Φ u*T u := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hidall,hid,hSc] at hall
  apply hall.trans
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply add_le_add
  · apply add_le_add_right
    have hb := qiP hδ A hL hU hA hR Φ k₁
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (pow_nonneg hL.le t)
  · have hH := qhL hδ A B (fun _ => (0:ℂ)) (by intro i; simp)
      (y:=y) (by omega) hR hBR hgen
    have hb := qiR Φ B hB k₂ hU
    calc
      _ ≤ q0 R y*((∫ u, ‖u‖^k₂*‖Φ u*qW B u‖)/U^k₂) :=
        mul_le_mul hH hb (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
noncomputable def qar (b : ℕ) (L : ℝ) : ℕ := ⌊L^b⌋₊
noncomputable def qaY (b : ℕ) : ℝ := (4*(b:ℝ))⁻¹
theorem qfx {b : ℕ} (hb : 0<b) : 0<qaY b := by
  unfold qaY
  positivity
theorem qdY {b : ℕ} (hb : 0<b) :
    Tendsto (qar b) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_pow_atTop (by omega : b≠0))
theorem qla (C : ℝ) {L : ℝ} (hL : 0<L) :
    C*(1+Real.sqrt L)/L = C*(L^(-1:ℝ)+L^(-(1/2):ℝ)) := by
  have hp : L^(1/2:ℝ)/L = L^(-(1/2):ℝ) := by
    calc
      _ = L^(1/2:ℝ)/L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^((1/2:ℝ)-1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  rw [Real.sqrt_eq_rpow,Real.rpow_neg_one,← hp]
  ring
theorem qkN (C : ℝ) :
    Tendsto (fun L : ℝ => C*(1+Real.sqrt L)/L) atTop (𝓝 0) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (qla C hL).symm
theorem qkO (C : ℝ) {L : ℝ} (hL : 0<L) :
    (C*(1+Real.sqrt L)/L)/(L^(-(1/4):ℝ)) =
      C*(L^(-(3/4):ℝ)+L^(-(1/4):ℝ)) := by
  rw [qla C hL,mul_div_assoc,add_div,← Real.rpow_sub hL,← Real.rpow_sub hL]
  norm_num
theorem qgJ (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C*(1+Real.sqrt L)/L≤L^(-(1/4):ℝ) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  filter_upwards [hh.eventually_lt_const zero_lt_one,eventually_gt_atTop (0:ℝ)] with L h hL
  apply (div_le_one (Real.rpow_pos_of_pos hL _)).mp
  rw [qkO C hL]
  exact h.le
theorem qkP {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 1≤L) :
    L^(-(1/4):ℝ) ≤ (qar b L:ℝ)^(-qaY b) := by
  have hLb : 1≤L^b := one_le_pow₀ hL
  have hy : 0<(qar b L:ℝ) := by
    have : 1≤qar b L := (Nat.one_le_floor_iff _).mpr hLb
    exact_mod_cast (show 0<qar b L by omega)
  have hyle : (qar b L:ℝ)≤L^b := Nat.floor_le (by positivity)
  have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have hexp : (b:ℝ)*(-qaY b)=-(1/4:ℝ) := by
    unfold qaY
    field_simp
  calc
    _ = L^((b:ℝ)*(-qaY b)) := by rw [hexp]
    _ = (L^b)^(-qaY b) := by
      rw [Real.rpow_mul (by linarith),Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hy hyle (by
      have := qfx hb; linarith)
theorem qhv {b : ℕ} (hb : 0<b) (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧ 2≤qar b L ∧
      C*(1+Real.sqrt L)/L<ε ∧
      C*(1+Real.sqrt L)/L≤(qar b L:ℝ)^(-qaY b) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (qdY hb).eventually (eventually_ge_atTop 2),
    (qkN C).eventually_lt_const hε,
    qgJ C] with L hL hy hεL hbound
  exact ⟨by linarith,hy,hεL,hbound.trans (qkP hb hL)⟩
theorem qhZ (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ y : ℕ in atTop, a y≤y := by
  filter_upwards [ha.eventually_lt_const zero_lt_one,eventually_ge_atTop 1] with y h hy
  exact ((div_le_one (by exact_mod_cast hy : 0<(y:ℝ))).mp h.le)
theorem qe9 (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0))
    {b : ℕ} (hb : 0<b) :
    ∀ᶠ L : ℝ in atTop, a (qar b L)≤L^b := by
  filter_upwards [(qdY hb).eventually (qhZ a ha),
    eventually_ge_atTop (0:ℝ)] with L h hL
  exact h.trans (Nat.floor_le (pow_nonneg hL b))
theorem qlP {L : ℝ} (hL : 0≤L) (n : ℕ) :
    (Real.sqrt L)^(2*n) = L^n := by rw [pow_mul,Real.sq_sqrt hL]
theorem qkQ {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (R t : ℕ)
    (hZ : Z≤((3/2:ℝ)*L)^(2*R)) :
    L^t*(Z/(Real.sqrt L)^(2*(2*R+t+1)))*I≤((3/2:ℝ)^(2*R)*I)/L := by
  rw [qlP hL.le]
  calc
    _ ≤ L^t*((((3/2:ℝ)*L)^(2*R))/L^(2*R+t+1))*I := by gcongr
    _ = _ := by rw [mul_pow,pow_add,pow_add,pow_one]; field_simp
theorem qkR {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (b : ℕ)
    (hZ : Z≤L^b) :
    Z*I/(Real.sqrt L)^(2*(b+1))≤I/L := by
  rw [qlP hL.le]
  calc
    _ ≤ L^b*I/L^(b+1) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp
theorem qcc {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι))
    (hB : ∀ S∈B, S.Nonempty) (R t b : ℕ) (hBR : B.card≤R) (hb : 0<b)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ δ : ℕ, δ≤1 → ∀ A : ℕ → Finset (Finset ι),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ p : Nat.Primes, qar b L<(p:ℕ) → A p=B) →
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : qB A,
        qk δ d.val (qab L u))) -
        qav δ A B (fun _ => 0)*qE Φ B‖ ≤ E L := by
  obtain ⟨c,hc,ε,hε,hformula⟩ := qfl
  obtain ⟨L₀,hL₀,hz⟩ := qgj
  let I₁ : ℝ := (3/2:ℝ)^(2*R)*(∫ u, ‖u‖^(2*(2*R+t+1))*‖Φ u‖)
  let I₂ : ℝ := ∫ u, ‖u‖^(2*(b+1))*‖Φ u*qW B u‖
  let E : ℝ → ℝ := fun L => qbX Φ B*
    qbr R c (qaY b) (qar b L) + I₁/L + I₂/L
  refine ⟨E,?_,?_⟩
  · have hcore := ((qjQ R c (qfx hb)).comp
      (qdY hb)).const_mul (qbX Φ B)
    have h₁ : Tendsto (fun L : ℝ => I₁/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h₂ : Tendsto (fun L : ℝ => I₂/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa only [mul_zero,add_zero,Function.comp_def,E] using (hcore.add h₁).add h₂
  · have hM : Tendsto (fun y : ℕ => q0 R y/(y:ℝ)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using qcE R zero_lt_one
    filter_upwards [qhv hb (Fintype.card ι:ℝ) hε,
      qe9 (q0 R) hM hb,
      eventually_ge_atTop L₀] with L hscale hmajor hLL₀
    intro δ hδ A hA hR hgen
    obtain ⟨hL,hy,hsmall,hysmall⟩ := hscale
    have hbound := hformula hδ A B hA hR hB hBR hy hgen Φ ht hL
      (Real.sqrt_pos.mpr hL) hsmall hysmall (2*(2*R+t+1)) (2*(b+1))
    apply hbound.trans
    apply add_le_add
    · apply add_le_add_right
      exact qkQ hL (integral_nonneg (fun _ => by positivity)) R t (hz L hLL₀ R)
    · exact qkR hL (integral_nonneg (fun _ => by positivity)) b hmajor
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
section FourierLaplace
open scoped FourierTransform SchwartzMap ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
noncomputable def qv (ℓ : V →L[ℝ] ℝ) (m u : V) : ℂ :=
  (ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem qhM (ℓ : V →L[ℝ] ℝ) (m u : V) :
    (qv ℓ m u).re = ℓ m := by simp [qv]
noncomputable def qaQ {α : Type*} [Fintype α] (m : α → V) (y : α → ℝ) : V :=
  ∑ i, y i • m i
noncomputable def qD (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α => volume.restrict (Ioi 0))
instance {α : Type*} [Fintype α] : SigmaFinite (qD α) := by
  unfold qD
  infer_instance
theorem qaO (α : Type*) [Fintype α] :
    qD α = volume.restrict (Set.pi univ (fun _ : α => Ioi (0:ℝ))) := by
  rw [volume_pi,Measure.restrict_pi_pi]
  rfl
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qkS {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    (∏ i, Complex.exp (-qv ℓ (m i) u * (y i:ℂ))) =
      Complex.exp (-(ℓ (qaQ m y):ℂ)-Complex.I*(inner ℝ u (qaQ m y):ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [qaQ,map_sum,map_smul,smul_eq_mul,inner_sum,inner_smul_right,
    Complex.ofReal_sum,Complex.ofReal_mul]
  rw [← Finset.sum_neg_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold qv
  ring
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qjS {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    ‖∏ i, Complex.exp (-qv ℓ (m i) u * (y i:ℂ))‖ =
      ∏ i, Real.exp (-ℓ (m i) * y i) := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [Complex.norm_exp,qv]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qh0 {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    (∫ y, ∏ i, Complex.exp (-qv ℓ (m i) u * (y i:ℂ))
      ∂qD α) = ∏ i, (qv ℓ (m i) u)⁻¹ := by
  rw [qD,integral_fintype_prod_eq_prod
    (fun i (y : ℝ) => Complex.exp (-qv ℓ (m i) u * (y:ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  simpa using integral_exp_mul_complex_Ioi (a:=-qv ℓ (m i) u)
    (by simp [hm i]) 0
theorem qfm {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    Integrable (fun z : V × (α → ℝ) => Ψ z.1 *
      ∏ i, Complex.exp (-qv ℓ (m i) z.1 * (z.2 i:ℂ)))
      (volume.prod (qD α)) := by
  have he : Integrable (fun y : α → ℝ => ∏ i, Real.exp (-ℓ (m i)*y i))
      (qD α) := by
    exact Integrable.fintype_prod (f := fun i y => Real.exp (-ℓ (m i)*y))
      (μ := fun _ => volume.restrict (Ioi 0))
      (fun i => integrableOn_exp_mul_Ioi (by linarith [hm i]) 0)
  have hb := (Ψ.integrable (μ := volume)).norm.mul_prod he
  apply hb.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (Ψ.continuous.comp continuous_fst)
    apply continuous_finsetProd
    intro i _
    unfold qv
    fun_prop
  · filter_upwards [] with z
    rw [norm_mul,qjS]
theorem qfa {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, Ψ u*(∏ i, (qv ℓ (m i) u)⁻¹)) =
      ∫ y, (∫ u : V, Ψ u *
        Complex.exp (-(ℓ (qaQ m y):ℂ)-Complex.I*(inner ℝ u (qaQ m y):ℂ)))
        ∂qD α := by
  calc
    _ = ∫ u : V, ∫ y, Ψ u*(∏ i, Complex.exp (-qv ℓ (m i) u * (y i:ℂ)))
        ∂qD α := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul,qh0 ℓ m hm]
    _ = ∫ y, (∫ u : V, Ψ u*(∏ i, Complex.exp (-qv ℓ (m i) u * (y i:ℂ))))
        ∂qD α :=
      integral_integral_swap (qfm Ψ ℓ m hm)
    _ = _ := by simp only [qkS]
theorem qhw {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (F : V → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, qq ℓ F hF hFs u*(∏ i, (qv ℓ (m i) u)⁻¹)) =
      ∫ y, F (qaQ m y) ∂qD α := by
  rw [qfa _ ℓ m hm]
  simp only [qdt]
theorem qdc {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, qq ℓ F hF hFs u *
      (ms.map (fun m => qv ℓ m u)).prod *
      (∏ i, (qv ℓ (m i) u)⁻¹)) =
      ∫ y, qI ms F (qaQ m y) ∂qD α := by
  rw [← qhw ℓ (qI ms F)
    (qbJ ms F hF) (qbR ms F hFs) m hm]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [qdE ℓ ms F hF hFs u]
  simp only [qv,mul_comm (qq ℓ F hF hFs u)]
end FourierLaplace
theorem qkl {ι : Type*} (S : Finset ι) (hS : S.card≤2) (w : ι → ℂ) :
    qc6 S w = (∏ i∈S, w i)*if S.card=2 then (∑ i∈S, w i)⁻¹ else 1 := by
  classical
  have hc : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hc with hc|hc|hc
  · have hs : S=∅ := Finset.card_eq_zero.mp hc
    subst S
    simp [qc6,qaI]
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    simp [qk9]
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simp [qmA hij,hij,div_eq_mul_inv]
theorem qeH {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2) (w : ι → ℂ) :
    qaj (qx b R) w =
      (∏ i, w i)*(∏ r∈R.filter (fun r => (Finset.univ.filter fun i => b i=r).card=2),
        (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹) := by
  classical
  rw [qlY]
  calc
    _ = ∏ r∈R, (∏ i∈Finset.univ.filter (fun i => b i=r), w i)*
        (if (Finset.univ.filter (fun i => b i=r)).card=2 then
          (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹ else 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact qkl _ (hcard r hr) w
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_fiberwise_of_maps_to (fun i _ => hR i)]
      congr 1
      exact (Finset.prod_filter ..).symm
section SmallFiberCoefficient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
noncomputable def q3 (ι : Type*) [Fintype ι] :
    List (EuclideanSpace ℝ ι) := by
  classical
  exact Finset.univ.toList.map (fun i => EuclideanSpace.single i (1:ℝ))
noncomputable def qbi {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) : Finset α := by
  classical
  exact R.filter (fun r => (Finset.univ.filter (fun i => b i=r)).card=2)
noncomputable def qcO {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) : EuclideanSpace ℝ ι := by
  classical
  exact ∑ i∈Finset.univ.filter (fun i => b i=r), EuclideanSpace.single i (1:ℝ)
@[simp] theorem qis {ι : Type*} [Fintype ι]
    (i : ι) (u : EuclideanSpace ℝ ι) :
    qv (qf ι) (EuclideanSpace.single i (1:ℝ)) u =
      qz (u i) := by
  classical
  simp [qv,qz,qcN,EuclideanSpace.inner_single_right]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem qlC {α : Type*} (ℓ : V →L[ℝ] ℝ) (S : Finset α)
    (m : α → V) (u : V) :
    qv ℓ (∑ i∈S, m i) u = ∑ i∈S, qv ℓ (m i) u := by
  simp [qv,map_sum,inner_sum,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_add_distrib]
@[simp] theorem qeI {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (u : EuclideanSpace ℝ ι) :
    qv (qf ι) (qcO b r) u =
      ∑ i∈Finset.univ.filter (fun i => b i=r), qz (u i) := by
  classical
  simp [qcO,qlC]
@[simp] theorem qbT {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) :
    ((q3 ι).map (fun m => qv (qf ι) m u)).prod =
      ∏ i, qz (u i) := by
  classical
  simp [q3,List.map_map,Function.comp_def]
theorem qms {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (r : qbi b R) :
    0 < qf ι (qcO b r.val) := by
  classical
  have hr : (Finset.univ.filter (fun i => b i=r.val)).card=2 :=
    (Finset.mem_filter.mp r.property).2
  have h := congrArg Complex.re (qeI b r.val (0 : EuclideanSpace ℝ ι))
  simp only [qhM,Complex.re_sum,qlO,Finset.sum_const] at h
  rw [h,hr]
  norm_num
theorem qiT {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    qE (qq (qf ι) F hF hFs) (qx b R) =
      ∫ y, qI (q3 ι) F
        (qaQ (fun r : qbi b R => qcO b r.val) y)
          ∂qD (qbi b R) := by
  classical
  rw [← qdc (qf ι) (q3 ι)
    F hF hFs (fun r : qbi b R => qcO b r.val) (qms b R)]
  unfold qE
  apply integral_congr_ae
  filter_upwards [] with u
  rw [qW,qeH b R hR hcard,qbT]
  simp only [qeI]
  have hp := Finset.prod_coe_sort (s := qbi b R)
    (f := fun r : α => (∑ i∈Finset.univ.filter (fun i => b i=r), qz (u i))⁻¹)
  rw [hp,mul_assoc]
  rfl
end SmallFiberCoefficient
theorem qhc {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    ∀ S∈qJ b, S.Nonempty := by
  intro S hS
  exact ((qcJ b (Finset.univ.image b) S).mp hS).1
theorem qkT {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) :
    ∀ S∈qam b p, S.Nonempty := by
  intro S hS
  exact ((qcJ _ _ S).mp hS).1
theorem qh1 {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) :
    ∀ S∈qS b p a, S.Nonempty := by
  intro S hS
  exact ((qcm b p a S).mp hS).1
theorem qlD {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    (∑ S∈qJ b, (-1:ℤ)^S.card) = -((Finset.univ.image b).card:ℤ) := by
  apply qcL
  intro r hr
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
  exact ⟨i,hi⟩
theorem qdN {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, qJ b=B → ∀ D : ℕ,
      (∀ i, (b i).natAbs≤D) → 2*D≤qar β L →
      ‖(L:ℂ)^t*qbU 0 (qam b) L F -
        (qay (Finset.univ.image b):ℂ)*
          qE (qq (qf ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := qcc
    (qq (qf ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (qcY B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb D hD hDL
  have hA := fun p : Nat.Primes => qkT b p
  have hR := fun p : Nat.Primes => qcY (qam b p)
  have hgen : ∀ p : Nat.Primes, qar β L<(p:ℕ) → qam b p=B := by
    intro p hp
    exact (qg5 b hD (hDL.trans_lt hp)).trans hb
  have h := hbound 0 (by omega) (qam b) hA hR hgen
  rw [← qeb (by omega) (qam b) hL hA hR F hF hFs] at h
  rw [← hb,qjh] at h
  simpa only [hb] using h
theorem qd6 {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, qJ b=B → ∀ a : ℤ,
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, (b i).natAbs≤D) → a.natAbs≤D →
      2*D≤qar β L →
      ‖(L:ℂ)^t*qbU 1 (fun p => qS b p a) L F -
        (qay (insert a (Finset.univ.image b)):ℂ)*
          qE (qq (qf ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := qcc
    (qq (qf ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (qcY B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb a ha D hD haD hDL
  have hA := fun p : Nat.Primes => qh1 b p a
  have hR := fun p : Nat.Primes => qcY (qS b p a)
  have hgen : ∀ p : Nat.Primes, qar β L<(p:ℕ) → qS b p a=B := by
    intro p hp
    exact (qe3 b a ha hD haD (hDL.trans_lt hp)).trans hb
  have h := hbound 1 (by omega) (fun p => qS b p a) hA hR hgen
  rw [← qeb (by omega) (fun p => qS b p a)
    hL hA hR F hF hFs] at h
  rw [← hb,qki b a ha] at h
  simpa only [hb] using h
theorem qfn {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin (n+1)))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin (n+1) → ℕ,
      qJ (fun i => (b i:ℤ))=B → ∀ D : ℕ,
      (∀ i, b i≤D) → 2*D≤qar β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(qj X (fun m => qd X F m b):ℂ) -
        (qay (Finset.univ.image fun i => (b i:ℤ)):ℂ)*
          qE (qq (qf (Fin (n+1)))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := qdN
    (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℝ → ℝ := fun L => (2*M*(1+rho)^n)*L^(n+t)*Real.exp (-(1-rho)*L)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (n+t:ℕ) (1-rho) (by linarith)).const_mul (2*M*(1+rho)^n)
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err (Real.log X)+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using (herr.comp hlog).add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hEX hX hL
  intro b hb D hD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have hden := hEX (fun i => (b i:ℤ)) hb D hb' hDL
  rw [qeQ hX hbudget b] at hden
  have hcomp : ‖(Real.log X:ℂ)^t*(qj X (fun m => qd X F m b):ℂ)-
      (Real.log X:ℂ)^t*(qbF X F rho b:ℂ)‖ ≤ err (Real.log X) := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log X)]
    have hh := mul_le_mul_of_nonneg_left
      (qeM hX hL hrho hbudget hM hbound b)
      (pow_nonneg (by linarith : 0≤Real.log X) t)
    convert hh using 1
    all_goals first | rfl | (simp only [err,pow_add]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(qj X (fun m => qd X F m b):ℂ))
    ((Real.log X:ℂ)^t*(qbF X F rho b:ℂ)) _)
theorem qf0 (hBV : qN) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin n))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    (H : ℕ → ℕ) {D₀ B₀ : ℝ} (hD₀ : 0<D₀)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ)≤D₀*(Real.log (X:ℝ))^B₀) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin n → ℕ,
      qJ (fun i => (b i:ℤ))=B → ∀ a : ℕ, a≤H X →
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, b i≤D) → a≤D →
      2*D≤qar β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(qj X (fun m => qd X F m b*theta (m+a)):ℂ) -
        (qay (insert (a:ℤ) (Finset.univ.image fun i => (b i:ℤ))):ℂ)*
          qE (qq (qf (Fin n))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := qd6
    (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℕ → ℝ := fun X => M*(qbG (2^n) X (H X) (qaM rho X)/X)*
    (Real.log (X:ℝ))^t
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (qiI hBV (2^n) H hrho hrhohalf hD₀ hH t).const_mul M
    simpa only [mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err X+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using herr.add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2] with X hEX hX
  intro b hb a haH ha D hD haD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have ha' : ∀ i, (b i:ℤ)≠(a:ℤ) := fun i he => ha i (by exact_mod_cast he)
  have hden := hEX (fun i => (b i:ℤ)) hb a ha' D hb'
    (by simpa only [Int.natAbs_natCast] using haD) hDL
  rw [qfk hX hbudget b a] at hden
  have hXR : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hY : ⌊Real.exp (rho*Real.log (X:ℝ))⌋₊ = qaM rho X := by
    unfold qaM
    rw [Real.rpow_def_of_pos hXR,mul_comm rho]
  have he := qj6 hX haH (by linarith : rho≤1) hbudget hM hbound b
  rw [hY] at he
  have he' : |qj X (fun m => qd X F m b*theta (m+a))-
      qb2 X F rho b a| ≤
      M/X*qbG (2^n) X (H X) (qaM rho X) := by
    simpa only [qbG,Nat.cast_pow] using he
  have hcomp : ‖(Real.log X:ℂ)^t*(qj X (fun m => qd X F m b*theta (m+a)):ℂ)-
      (Real.log X:ℂ)^t*(qb2 X F rho b a:ℂ)‖ ≤ err X := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (qw hX).le]
    have hh := mul_le_mul_of_nonneg_left he' (pow_nonneg (qw hX).le t)
    convert hh using 1
    all_goals first | rfl | (simp only [err]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(qj X (fun m => qd X F m b*theta (m+a)):ℂ))
    ((Real.log X:ℂ)^t*(qb2 X F rho b a:ℂ)) _)
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def qdd {ι : Type*} [Fintype ι] (T : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, -T≤x i ∧ x i≤0}
theorem qc1 {ι : Type*} [Fintype ι] (T : ℝ) :
    IsCompact (qdd (ι:=ι) T) := by
  have h := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := -T) (b := (0:ℝ)))).image
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨x.ofLp, ?_, ?_⟩
    · simpa only [qdd, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hx
    · rfl
  · rintro ⟨y, hy, rfl⟩
    change ∀ i, -T≤y i ∧ y i≤0
    simpa only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hy
noncomputable def qbf {ι : Type*} [Fintype ι] (T : ℝ) : EuclideanSpace ℝ ι → ℝ :=
  (qdd T).indicator (fun _ => 1)
theorem qgA {ι : Type*} [Fintype ι] (T : ℝ) :
    HasCompactSupport (qbf (ι:=ι) T) := by
  apply (qc1 T).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (qc1 T).isClosed
  exact Set.support_indicator_subset
theorem qcd {ι : Type*} [Fintype ι] (T : ℝ) :
    Integrable (qbf (ι:=ι) T) := by
  apply (integrable_indicator_iff (qc1 T).measurableSet).mpr
  exact continuous_const.continuousOn.integrableOn_compact (qc1 T)
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def qbd {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) : EuclideanSpace ℝ ι → ℝ :=
  qbf T ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f
theorem qit {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (qbd T f) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) (qgA T) hf
theorem qiU {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (qbd T f) :=
  hf.contDiff_convolution_right _ (qcd T).locallyIntegrable hfs
noncomputable def qh2 {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y in {y | ∀ i, v i≤y i}, f y
theorem qjT {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    qbd T f v = qh2 f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold qbd qh2
  rw [convolution_def]
  change (∫ t, qbf T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => qbf T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈qdd T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [qbf,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉qdd T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [qbf,Set.indicator_of_notMem hcube]
section GeneralDirections
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
noncomputable def qT (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F
theorem qcu (ms : List V) (F : V → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (qT ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const |>.neg
theorem qdL (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) : HasCompactSupport (qT ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg
theorem qdZ (ms : List V) (F : W → ℂ)
    (hF : ContDiff ℝ ∞ F) (A : V →L[ℝ] W) (c : W) :
    qT ms (fun v => F (c+A v)) =
      fun v => qT (ms.map A) F (c+A v) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hd := qcu (ms.map A) F hF
    have hA (v : V) : HasFDerivAt (fun v => c+A v) A v := by
      simpa using (A.hasFDerivAt (x := v)).const_add c
    ext v
    change -fderiv ℝ (qT ms (fun v => F (c+A v))) v m = _
    rw [ih]
    have he := ((hd.differentiable (by simp) (c+A v)).hasFDerivAt.comp v (hA v)).fderiv
    simp only [Function.comp_def] at he
    rw [he]
    rfl
theorem qhd (ms : List V) (F : V → ℂ) :
    tsupport (qT ms F) ⊆ tsupport F := by
  induction ms with
  | nil => exact Set.Subset.rfl
  | cons m ms ih =>
    change tsupport (fun v => - fderiv ℝ (qT ms F) v m) ⊆ _
    change tsupport (-(fun v => fderiv ℝ (qT ms F) v m)) ⊆ _
    rw [tsupport_neg]
    exact (tsupport_fderiv_apply_subset ℝ m).trans ih
end GeneralDirections
noncomputable def qde (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
    { toFun := fun x => Fin.cons 0 x
      map_add' := by intros; ext i; cases i using Fin.cases <;> simp
      map_smul' := by intros; ext i; cases i using Fin.cases <;> simp }
  A.toContinuousLinearMap
@[simp] theorem qm8 (n : ℕ) (x : Fin n → ℝ) :
    qde n x = Fin.cons 0 x := rfl
noncomputable def qbg (n : ℕ) : List (Fin n → ℝ) :=
  (List.finRange n).map (fun i => Pi.single i 1)
theorem ql0 (n : ℕ) (i : Fin n) :
    qde n (Pi.single i 1) = Pi.single i.succ 1 := by
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Pi.single_apply,Fin.succ_inj]
theorem qmf (n : ℕ) :
    qbg (n+1) = Pi.single 0 1 :: (qbg n).map (qde n) := by
  simp only [qbg,List.finRange_succ,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (ql0 n i).symm
theorem qhe {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    Fin.cons a x = Pi.single 0 a + qde n x := by
  ext i
  cases i using Fin.cases <;> simp
theorem qjU (n : ℕ) (a : ℝ) :
    IsClosedEmbedding (fun x : Fin n → ℝ => (Fin.cons a x : Fin (n+1) → ℝ)) := by
  have h : Function.Injective (qde n) := by
    intro x y hxy
    ext i
    have := congrFun hxy i.succ
    simpa using this
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hc := (Homeomorph.addLeft (Pi.single 0 a : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  funext x
  exact qhe a x
theorem qhx (n : ℕ) (y : Fin n → ℝ) :
    IsClosedEmbedding (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : IsClosedEmbedding (fun a : ℝ => a • (Pi.single 0 1 : Fin (n+1) → ℝ)) :=
    isClosedEmbedding_smul_left (by intro h; have := congrFun h 0; simp at this)
  have hc := (Homeomorph.addRight (Fin.cons 0 y : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  ext a i
  cases i using Fin.cases <;> simp
noncomputable def qaB {n : ℕ} (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => volume.restrict (Ioi (v i)))
instance {n : ℕ} (v : Fin n → ℝ) : SigmaFinite (qaB v) := by
  unfold qaB
  infer_instance
instance {n : ℕ} (v : Fin n → ℝ) : IsFiniteMeasureOnCompacts (qaB v) := by
  unfold qaB
  infer_instance
theorem qlE {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℂ) (hf : Integrable f (qaB v)) :
    (∫ x, f x ∂qaB v) =
      ∫ y, (∫ a in Ioi (v 0), f (Fin.cons a y)) ∂qaB (fun i => v i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ioi (v i))) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  dsimp only [e] at he
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioi (v 0))).prod (qaB (fun i => v i.succ))) := by
    have hh := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    simpa only [Fin.zero_succAbove,he,Function.comp_def,qaB] using hh
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂((volume.restrict (Ioi (v 0))).prod (qaB (fun i => v i.succ))) := by
      have hh := hm.symm.integral_comp' f
      simpa only [Fin.zero_succAbove,he,qaB] using hh.symm
    _ = _ := integral_prod_symm _ hprod
theorem qhf {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    Fin.cons a y = a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y := by
  ext i
  cases i using Fin.cases <;> simp
theorem ql1 {n : ℕ} (y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) (Pi.single 0 1) a := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => qhf a y)
  rw [he]
  simpa using ((hasDerivAt_id a).smul_const (Pi.single 0 1 : Fin (n+1) → ℝ)).add_const
    (Fin.cons 0 y)
theorem qlF {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => qhf a y)
  rw [he]
  fun_prop
theorem qlG {n : ℕ} (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  simp_rw [qhe]
  fun_prop
theorem qiu (n : ℕ) (F : (Fin n → ℝ) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : Fin n → ℝ) :
    (∫ x, qT (qbg n) F x ∂qaB v) = F v := by
  induction n with
  | zero =>
    simp only [qbg,List.finRange_zero,List.map_nil,qT,List.foldr_nil]
    unfold qaB
    rw [Measure.pi_of_empty (x := v)]
    exact integral_dirac F v
  | succ n ih =>
    rw [qmf]
    let ms := (qbg n).map (qde n)
    let H := qT ms F
    have hHc : HasCompactSupport H := qdL ms F hF
    have hHs : ContDiff ℝ ∞ H := qcu ms F hFs
    have hfull : Integrable (qT (Pi.single 0 1 :: ms) F) (qaB v) :=
      (qcu _ F hFs).continuous.integrable_of_hasCompactSupport
        (qdL _ F hF)
    rw [qlE v _ hfull]
    have hinner (y : Fin n → ℝ) :
        (∫ a in Ioi (v 0), qT (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          H (Fin.cons (v 0) y) := by
      have hc : HasCompactSupport (fun a : ℝ => H (Fin.cons a y)) :=
        hHc.comp_isClosedEmbedding (qhx n y)
      have hs : ContDiff ℝ ∞ (fun a : ℝ => H (Fin.cons a y)) :=
        hHs.comp (qlF y)
      have hd (a : ℝ) : deriv (fun a : ℝ => H (Fin.cons a y)) a =
          fderiv ℝ H (Fin.cons a y) (Pi.single 0 1) := by
        exact ((hHs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a
          (ql1 y a)).deriv
      have he : (fun a : ℝ => qT (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          fun a => -deriv (fun a : ℝ => H (Fin.cons a y)) a := by
        funext a
        rw [hd]
        rfl
      rw [he,integral_neg,HasCompactSupport.integral_Ioi_deriv_eq (hs.of_le (by simp)) hc,neg_neg]
    simp_rw [hinner]
    let G : (Fin n → ℝ) → ℂ := fun y => F (Fin.cons (v 0) y)
    have hGc : HasCompactSupport G := hF.comp_isClosedEmbedding (qjU n (v 0))
    have hGs : ContDiff ℝ ∞ G := hFs.comp (qlG (v 0))
    have hg : (fun y : Fin n → ℝ => H (Fin.cons (v 0) y)) = qT (qbg n) G := by
      have he := qdZ (qbg n) F hFs (qde n)
        (Pi.single 0 (v 0))
      simpa only [← qhe] using he.symm
    rw [hg,ih G hGc hGs (fun i => v i.succ)]
    dsimp only [G]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl
noncomputable def q5 {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : EuclideanSpace ℝ ι → ℂ :=
  qbf T ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] F
theorem qfI {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (q5 T F) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (qgA T) hF
theorem qf1 {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (q5 T F) :=
  hF.contDiff_convolution_right _ (qcd T).locallyIntegrable hFs
theorem qgK {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : ∀ y, F y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    q5 T F v = ∫ y in {y | ∀ i, v i≤y i}, F y := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i))
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold q5
  rw [convolution_def]
  change (∫ t, qbf T t • F (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => qbf T t • F (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hFy : F y=0
  · simp [Set.indicator,hFy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈qdd T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hF y hFy i,hv i,hy i]
      simp [qbf,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉qdd T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [qbf,Set.indicator_of_notMem hcube]
theorem qiv {ι : Type*} [Fintype ι]
    (T : ℝ) (ms : List (EuclideanSpace ℝ ι)) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    qI ms (q5 T F) =
      q5 T (qI ms F) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    ext v
    change -fderiv ℝ (qI ms (q5 T F)) v m = _
    rw [ih]
    have hc := qbJ ms F hF
    have hs := qbR ms F hFs
    unfold q5
    rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (qcd T).locallyIntegrable (hs.of_le (by simp)) v).fderiv]
    rw [convolution_precompR_apply _ (qcd T).locallyIntegrable
      (hc.fderiv ℝ) (hs.continuous_fderiv (by simp))]
    simp only [convolution_def,ContinuousLinearMap.lsmul_apply,
      qI,List.foldr_cons,smul_neg,integral_neg]
noncomputable def qaD (n : ℕ) : List (EuclideanSpace ℝ (Fin n)) :=
  (qbg n).map (EuclideanSpace.equiv (Fin n) ℝ).symm
theorem qfJ (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x in {x | ∀ i, v i≤x i}, qI (qaD n) F x) = F v := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hc : HasCompactSupport (fun x => F (e x)) :=
    hF.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hs : ContDiff ℝ ∞ (fun x => F (e x)) := hFs.comp e.contDiff
  have hFTC := qiu n (fun x => F (e x)) hc hs v.ofLp
  have ha := qdZ (qbg n) F hFs e.toContinuousLinearMap 0
  simp only [zero_add] at ha
  have htail : qaB v.ofLp = volume.restrict (Ici v.ofLp) := by
    unfold qaB
    rw [← Measure.restrict_pi_pi]
    exact Measure.restrict_congr_set (Measure.univ_pi_Ioi_ae_eq_Ici (μ := fun _ => volume))
  change qT (qbg n) (fun x => F (e x)) =
    fun x => qI (qaD n) F (e x) at ha
  rw [htail,ha] at hFTC
  have he := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (qI (qaD n) F) {x | ∀ i, v i≤x i}
  convert he.symm.trans hFTC using 1
  exact congrArg F (by simp [e])
@[simp] theorem qf2 (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ((qaD n).map
      (fun m => qv (qf (Fin n)) m u)).prod =
      ∏ i, qz (u i) := by
  simp only [qaD,qbg,List.map_map]
  change ((List.finRange n).map (fun i =>
    qv (qf (Fin n)) (EuclideanSpace.single i (1:ℝ)) u)).prod = _
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  convert qis i u using 1
  congr 2
  exact Subsingleton.elim _ _
theorem qfK (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    qI (q3 (Fin n)) F =
      qI (qaD n) F := by
  ext v
  rw [← qcW (qf (Fin n))
    (q3 (Fin n)) F hF hFs v,
    ← qcW (qf (Fin n))
    (qaD n) F hF hFs v]
  apply integral_congr_ae
  filter_upwards [] with u
  change qq _ F hF hFs u *
    ((q3 (Fin n)).map (fun m => qv _ m u)).prod * _ =
    qq _ F hF hFs u *
    ((qaD n).map (fun m => qv _ m u)).prod * _
  rw [qbT,qf2]
theorem qeA (n : ℕ) (T : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) (hT : ∀ y∈tsupport F, ∀ i, y i≤T)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    qI (q3 (Fin n)) (q5 T F) v =
      F v := by
  rw [qfK n _ (qfI T F hF)
    (qf1 T F hF hFs),qiv T _ F hF hFs]
  rw [qgK T _ _ v hv]
  · exact qfJ n F hF hFs v
  · intro y hy i
    exact hT y (qhd (qaD n) F
      (subset_tsupport _ hy)) i
theorem qf3 {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) :
    q5 T (fun y => (f y:ℂ)) =
      fun v => (qbd T f v:ℂ) := by
  ext v
  simp only [q5,qbd,convolution_def,
    ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',
    Complex.real_smul,← Complex.ofReal_mul,integral_complex_ofReal]
noncomputable def qa {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun v => qbd tau (fun y => f y.ofLp) (WithLp.toLp 2 v)
theorem qac {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (qa tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  exact (qit tau _ hfc).comp_isClosedEmbedding
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isClosedEmbedding
theorem qak {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (qa tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  exact (qiU tau _ hfc hF).comp
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff
theorem qfb {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ qe n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le
theorem q6 {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ qe n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    qa tau f v = ∫ y in Ici v, f y := by
  unfold qa
  rw [qjT tau _ _ _ hv]
  · unfold qh2
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact qfb hf y.ofLp (subset_tsupport f hy) i
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qaV {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ qe n tau) : qV (qa tau f) tau := by
  intro v hv hsum
  rw [q6 tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤qdx y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2
theorem qcl {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ qe n tau)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    qI (q3 (Fin n))
      (fun y : EuclideanSpace ℝ (Fin n) => (qa tau f y.ofLp:ℂ)) v =
      (f v.ofLp:ℂ) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    (hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
      Complex.ofReal_zero
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
  have hT : ∀ y∈tsupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)),
      ∀ i, y i≤tau := by
    intro y hy i
    have hsub := tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) Complex.ofReal_zero
      (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp)
    have hp := tsupport_comp_subset_preimage f (EuclideanSpace.equiv (Fin n) ℝ).continuous
    exact qfb hsupp y.ofLp (hp (hsub hy)) i
  have hh := qeA n tau _ hfc hF hT v hv
  rw [qf3] at hh
  convert hh using 1
  congr 2
noncomputable def qbD (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n+m) → ℝ) :=
  (Fin.appendHomeomorph n m).toMeasurableEquiv
@[simp] theorem qec (n m : ℕ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    qbD n m p = Fin.append p.1 p.2 := rfl
theorem qcg (n m : ℕ) :
    MeasurePreserving (qbD n m) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv)
  have he : qbD n m=e := by
    ext p i
    change Fin.append p.1 p.2 i = e p i
    cases i using Fin.addCases with
    | left i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
    | right i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
  rw [he]
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin m => ℝ))
noncomputable def qi {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin (n+m) → ℝ) : ℝ :=
  f (fun i => v (i.castAdd m)) * g (fun i => v (i.natAdd n))
@[simp] theorem qa6 {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    qi f g (Fin.append v w)=f v*g w := by
  simp [qi]
theorem qn {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (qi f g) := by
  have hk : IsCompact ((tsupport f) ×ˢ (tsupport g)) := hf.isCompact.prod hg.isCompact
  have hh : HasCompactSupport (fun p : (Fin n → ℝ) × (Fin m → ℝ) => f p.1*g p.2) := by
    apply hk.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hk.isClosed
    intro p hp
    have hm := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport f hm.1,subset_tsupport g hm.2⟩
  exact hh.comp_isClosedEmbedding (Fin.appendHomeomorph n m).symm.isClosedEmbedding
theorem qs {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (qi f g) := by
  unfold qi
  exact (hf.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.castAdd m)))).mul
    (hg.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.natAdd n))))
theorem qU {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ qe n a) (hg : tsupport g ⊆ qe m b) :
    tsupport (qi f g) ⊆ qe (n+m) (a+b) := by
  intro v hv
  have hleft : (fun i : Fin n => v (i.castAdd m)) ∈ tsupport f := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin n => x (i.castAdd m)) f
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_left hv)
  have hright : (fun i : Fin m => v (i.natAdd n)) ∈ tsupport g := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin m => x (i.natAdd n)) g
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_right hv)
  refine ⟨?_,?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i => exact (hf hleft).1 i
    | right i => exact (hg hright).1 i
  · change (∑ i, v i)<a+b
    rw [Fin.sum_univ_add]
    exact add_lt_add (hf hleft).2 (hg hright).2
theorem qmg {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    (∫ y in Ici (Fin.append v w), qi f g y) =
      (∫ y in Ici v, f y)*(∫ y in Ici w, g y) := by
  have hd : (qbD n m) ⁻¹' Ici (Fin.append v w) = (Ici v) ×ˢ (Ici w) := by
    ext p
    change (∀ i, Fin.append v w i≤Fin.append p.1 p.2 i) ↔ _
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
  have hm := (qcg n m).setIntegral_preimage_emb
    (qbD n m).measurableEmbedding (qi f g) (Ici (Fin.append v w))
  rw [hd] at hm
  rw [← hm]
  simp only [qec,qa6]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g
theorem qdf {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ qe n a) (hg : tsupport g ⊆ qe m b)
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0≤v i) (hw : ∀ i, 0≤w i) :
    qa (a+b) (qi f g) (Fin.append v w) =
      qa a f v*qa b g w := by
  rw [q6 (a+b) _ (qU f g hf hg),
    q6 a f hf _ hv,q6 b g hg _ hw,qmg]
  intro i
  cases i using Fin.addCases with
  | left i => simpa using hv i
  | right i => simpa using hw i
@[simp] theorem qlb (X : ℕ) {n m : ℕ}
    (d : Fin n → ℕ) (e : Fin m → ℕ) :
    q1 X (Fin.append d e)=Fin.append (q1 X d) (q1 X e) := by
  ext i
  cases i using Fin.addCases <;> simp [q1]
@[simp] theorem qjp (X : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (d : Fin n → ℕ) (e : Fin m → ℕ) :
    qg X (qi F G) (Fin.append d e)=
      qg X F d*qg X G e := by
  simp only [qg,qlb,qa6,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]
  ring
theorem qfL (X M : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (b : Fin n → ℕ) (c : Fin m → ℕ) :
    qd X (qi F G) M (Fin.append b c)=
      qd X F M b*qd X G M c := by
  classical
  unfold qd
  rw [Finset.sum_mul_sum, ←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.appendEquiv n m)
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.appendEquiv_apply]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
  · intro p _
    exact (qjp X F G p.1 p.2).symm
theorem qce {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2≤X) (M : ℕ) (b : ι → ℕ) (F G : (ι → ℝ) → ℝ)
    (hFG : ∀ v, (∀ i, 0≤v i) → F v=G v) : qd X F M b=qd X G M b := by
  apply Finset.sum_congr rfl
  intro d hd
  unfold qg
  congr 1
  apply hFG
  apply qbB hX
  intro i
  exact Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
theorem qbO {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ qe n a) (hg : tsupport g ⊆ qe m b)
    {X : ℕ} (hX : 2≤X) (M : ℕ) (s : Fin n → ℕ) (t : Fin m → ℕ) :
    qd X (qa (a+b) (qi f g)) M (Fin.append s t)=
      qd X (qa a f) M s*qd X (qa b g) M t := by
  rw [←qfL]
  apply qce hX
  intro v hv
  let v1 : Fin n → ℝ := fun i => v (i.castAdd m)
  let v2 : Fin m → ℝ := fun i => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by ext i; cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,qa6]
  exact qdf f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)
@[simp] theorem ql2 (X : ℕ) {n : ℕ} (d : Fin n → ℕ) (e : ℕ) :
    q1 X (Fin.snoc d e) = Fin.snoc (q1 X d) (Real.log e/Real.log X) := by
  ext i
  cases i using Fin.lastCases <;> simp [q1]
theorem qiw (X : ℕ) {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (d : Fin n → ℕ) :
    qg X F (Fin.snoc d 1)=
      qg X (fun v => F (Fin.snoc v 0)) d := by
  simp [qg,ql2,Fin.prod_univ_castSucc]
theorem qfM {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (F : (Fin (n+1) → ℝ) → ℝ) {rho : ℝ} (hrho : rho<1) (hb : qV F rho)
    (d : Fin n → ℕ) (hd : ∀ i, 0<d i) : qg X F (Fin.snoc d (M+a))=0 := by
  have hp : 0<M+a := by omega
  have hcoord := qbB hX (d := Fin.snoc d (M+a)) (by
    intro i; cases i using Fin.lastCases <;> simp [hp,hd])
  have hs : rho<∑ i,q1 X (Fin.snoc d (M+a)) i := by
    apply hrho.trans
    apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => hcoord i) (Finset.mem_univ (Fin.last n)))
    simp only [q1,Fin.snoc_last]
    apply (lt_div_iff₀ (qw hX)).mpr
    simpa only [one_mul] using Real.log_lt_log (by exact_mod_cast (by omega : 0<X))
      (by exact_mod_cast hM)
  rw [qg,hb _ hcoord hs,mul_zero]
theorem qmP (X M : ℕ) {n : ℕ} (F : (Fin (n+1) → ℝ) → ℝ)
    (b : Fin n → ℕ) (a : ℕ) :
    qd X F M (Fin.snoc b a)=
      ∑ r∈(M+a).divisors, ∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
        qg X F (Fin.snoc d r) := by
  classical
  unfold qd
  rw [←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ℕ))
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.snocEquiv]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.lastCases with
      | last => simpa using h1
      | cast i => simpa using h2 i
    · intro h
      exact ⟨by simpa using h (Fin.last n),fun i => by simpa using h i.castSucc⟩
  · intro p _
    rfl
theorem qfy {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (hp : Nat.Prime (M+a)) (F : (Fin (n+1) → ℝ) → ℝ)
    {rho : ℝ} (hrho : rho<1) (hb : qV F rho) (b : Fin n → ℕ) :
    qd X F M (Fin.snoc b a)=qd X (fun v => F (Fin.snoc v 0)) M b := by
  rw [qmP,hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm),Finset.sum_singleton]
  have hz : (∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
      qg X F (Fin.snoc d (M+a)))=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact qfM hX hM F hrho hb d
      (fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i))
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  exact qiw X F d
@[simp] theorem qlc {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (i : ι) : qcO b r i=if b i=r then 1 else 0 := by
  classical
  simp [qcO,WithLp.ofLp_sum,Finset.sum_apply]
theorem qkU {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (y : qbi b R → ℝ) (hy : ∀ r, 0≤y r) (i : ι) :
    0≤qaQ (fun r : qbi b R => qcO b r.val) y i := by
  classical
  simp only [qaQ,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,qlc]
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hy r) (by split_ifs <;> norm_num))
theorem qjV {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (i : ι)
    (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (y : qbi b R → ℝ) :
    qaQ (fun r : qbi b R => qcO b r.val) y i=0 := by
  classical
  simp only [qaQ,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,qlc]
  apply Finset.sum_eq_zero
  intro r _
  have hr : b i≠r.val := by
    intro he
    have hh := (Finset.mem_filter.mp r.property).2
    rw [←he,hi] at hh
    norm_num at hh
  simp [hr]
theorem qeS {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ qe n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (qa tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (qa tau f v.ofLp:ℂ))) :
    qE (qq (qf (Fin n))
      (fun v => (qa tau f v.ofLp:ℂ)) hF hFs) (qx b R) =
      ∫ y, (f (qaQ (fun r : qbi b R => qcO b r.val) y).ofLp:ℂ)
        ∂qD (qbi b R) := by
  rw [qiT b R hR hcard]
  apply integral_congr_ae
  rw [qaO]
  filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
  exact qcl tau f hf hfs hsupp _
    (qkU b R y (fun r => (hy r (Set.mem_univ r)).le))
theorem qer {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ qe n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (i : Fin n) (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (qa tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (qa tau f v.ofLp:ℂ))) :
    qE (qq (qf (Fin n))
      (fun v => (qa tau f v.ofLp:ℂ)) hF hFs) (qx b R)=0 := by
  rw [qeS f hf hfs hsupp b R hR hcard]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hz : f (qaQ (fun r : qbi b R => qcO b r.val) y).ofLp=0 := by
    by_contra hne
    have hh := (hsupp (subset_tsupport f hne)).1 i
    have he := qjV b R i hi y
    change 0<qaQ (fun r : qbi b R => qcO b r.val) y i at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  simp [hz]
@[simp] theorem qm9 {n : ℕ} {α : Type*} (y z : Fin n → α) (i : Fin n) :
    Fin.append y z (i.addNat n)=z i := by
  rw [←Fin.natAdd_eq_addNat,Fin.append_right]
def qhg (n : ℕ) : Fin (n+n) → Fin n := Fin.append id id
theorem qjq {n : ℕ} (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => qhg n i=r), w i)=w (r.castAdd n)+w (r.natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [qhg]
@[simp] theorem qmV {n : ℕ} (r : Fin n) :
    (Finset.univ.filter fun i => qhg n i=r).card=2 := by
  simpa using qjq r (fun _ => (1:ℕ))
theorem qf4 {n : ℕ} (i j : Fin n) : i.castAdd n ≠ j.addNat n := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_addNat] at hval
  omega
theorem qkV {n : ℕ} (i j : Fin n) : i.addNat n ≠ j.castAdd n :=
  (qf4 j i).symm
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
def qex {ι : Type*} (r : Setoid ι) (α : Type*) :=
  {b : ι → α // Setoid.ker b = r}
noncomputable def qia {ι α : Type*} {r : Setoid ι} (b : qex r α) :
    Quotient r → α :=
  Quotient.lift b.val (by
    intro i j hij
    rw [←b.property] at hij
    exact hij)
@[simp] theorem qne {ι α : Type*} {r : Setoid ι} (b : qex r α) (i : ι) :
    qia b (Quotient.mk r i)=b.val i := rfl
theorem qld {ι α : Type*} {r : Setoid ι} (b : qex r α) :
    Function.Injective (qia b) := by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j =>
      intro h
      apply Quotient.sound
      rw [←b.property]
      exact h
noncomputable def qY {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) : Finset (ι → α) := Finset.univ.filter (fun b => Setoid.ker b=r)
@[simp] theorem qcv {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (b : ι → α) : b∈qY r ↔ Setoid.ker b=r := by
  simp [qY]
noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))
theorem qhh {ι α K : Type*} [Fintype ι] [Fintype α] [AddCommMonoid K]
    (f : (ι → α) → K) :
    (∑ r : Setoid ι, ∑ b∈qY (α:=α) r, f b)=∑ b : ι → α, f b := by
  classical
  simp only [qY]
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
theorem qfc {ι α β : Type*} [Fintype ι]
    (a : ι → α) (b : ι → β) (hab : ∀ i j, a i=a j ↔ b i=b j) :
    qx a (Finset.univ.image a)=qx b (Finset.univ.image b) := by
  classical
  ext S
  simp only [qH]
  constructor <;> rintro ⟨hS,h⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mp (h i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mpr (h i hi j hj)⟩
theorem qmt {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card=
      (Finset.univ.filter fun i => a i=r).card+(Finset.univ.filter fun i => b i=r).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
theorem qjW {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a) (hb : Function.Injective b) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card≤2 := by
  classical
  rw [qmt]
  have h1 : (Finset.univ.filter fun i => a i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ha ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have h2 : (Finset.univ.filter fun i => b i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hb ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  omega
theorem qle {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a)
    (i : Fin m) (hi : a i∉Set.range b) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n))=
      {i.castAdd n} := by
    ext j
    cases j using Fin.addCases with
    | left j => simp [ha.eq_iff]
    | right j =>
      have hn : b j≠a i := fun h => hi ⟨j,h⟩
      have hne : Fin.natAdd m j≠i.castAdd n := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
  rw [he,Finset.card_singleton]
theorem qkW {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (hb : Function.Injective b)
    (i : Fin n) (hi : b i∉Set.range a) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m))=
      {i.natAdd m} := by
    ext j
    cases j using Fin.addCases with
    | left j =>
      have hn : a j≠b i := fun h => hi ⟨j,h⟩
      have hne : j.castAdd n≠Fin.natAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
    | right j => simp [hb.eq_iff]
  rw [he,Finset.card_singleton]
theorem qch {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ qe m tau) (hsg : tsupport g ⊆ qe n tau)
    {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a≠Set.range b)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (qa (tau+tau) (qi f g) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (qa (tau+tau) (qi f g) v.ofLp:ℂ))) :
    qE (qq (qf (Fin (m+n)))
      (fun v => (qa (tau+tau) (qi f g) v.ofLp:ℂ)) hF hFs)
      (qx (Fin.append a b) (Finset.univ.image (Fin.append a b)))=0 := by
  classical
  have hh : ∃ i : Fin (m+n),
      (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b i).card=1 := by
    by_cases hsub : Set.range a⊆Set.range b
    · have hnot : ¬Set.range b⊆Set.range a := fun h => hab (Set.Subset.antisymm hsub h)
      obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hnot
      exact ⟨i.natAdd m,qkW a b hb i hi⟩
    · obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hsub
      exact ⟨i.castAdd n,qle a b ha i hi⟩
  obtain ⟨i,hi⟩ := hh
  exact qer (qi f g)
    (qn f g hf hg) (qs f g hfs hgs)
    (qU f g hsf hsg) (Fin.append a b) _
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (fun r _ => qjW a b ha hb r) i hi hF hFs
noncomputable def qmB {ι α : Type*} {r : Setoid ι} (b : qex r α) :
    Quotient r ↪ α := ⟨qia b,qld b⟩
noncomputable def qmC {ι α : Type*} (r : Setoid ι) (e : Quotient r ↪ α) :
    qex r α := ⟨fun i => e (Quotient.mk r i),by
  apply Setoid.ext
  intro i j
  change e (Quotient.mk r i)=e (Quotient.mk r j) ↔ r i j
  rw [e.injective.eq_iff,Quotient.eq]⟩
noncomputable def qlf {ι α : Type*} (r : Setoid ι) :
    qex r α ≃ (Quotient r ↪ α) where
  toFun := qmB
  invFun := qmC r
  left_inv b := by apply Subtype.ext; rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    induction x using Quotient.inductionOn with | h i => rfl
noncomputable def qmu {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    {b // b∈qY (α:=α) r} ≃ (Quotient r ↪ α) :=
  (Equiv.subtypeEquivRight (fun b => qcv r b)).trans (qlf r)
theorem qc2 {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => (qb lam X:ℝ)/Real.log X) atTop (𝓝 lam) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hlo : Tendsto (fun X : ℕ => lam-(Real.log (X:ℝ))⁻¹) atTop (𝓝 lam) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := qw hX
    apply (le_div_iff₀ hL).mpr
    have hh := (Nat.lt_floor_add_one (lam*Real.log (X:ℝ))).le
    dsimp [qb]
    have he : (lam-(Real.log (X:ℝ))⁻¹)*Real.log X=lam*Real.log X-1 := by
      field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact (div_le_iff₀ (qw hX)).mpr (qcx hlam hX)
theorem qbV {lam : ℝ} (hlam : 0<lam) :
    Tendsto (qb lam) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hlam)
theorem qcF {lam : ℝ} (hlam : 0≤lam) (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, K*qb lam X≤qar 2 (Real.log X) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop ((K:ℝ)*lam)] with X hX hL
  apply (Nat.le_floor_iff (by positivity : 0≤(Real.log (X:ℝ))^2)).mpr
  push_cast
  have hh := qcx hlam hX
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K),
    mul_le_mul_of_nonneg_right hL (qw hX).le]
theorem qdo (s : ℕ) {K : ℕ} (hK : 0<K)
    (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ) (hH : Tendsto H atTop atTop)
    (hdiam : ∀ᶠ X : ℕ in atTop, qcs (h:=H X) (a X) (K*H X)) :
    Tendsto (fun X => qaH (h:=H X) (a X)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨h₀,hh₀⟩ := qkb s hK hε
  filter_upwards [hH.eventually_ge_atTop h₀,hdiam] with X hX hd
  exact (by simpa only [Real.dist_eq] using hh₀ (H X) hX (a X) hd)
noncomputable def qp {ι : Type*} [Fintype ι] (r : Setoid ι) : ι → ℕ :=
  fun i => (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val
theorem qcG {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (qp r)=r := by
  apply Setoid.ext
  intro i j
  change (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val=
    (Fintype.equivFin (Quotient r) (Quotient.mk r j)).val ↔ r i j
  rw [Fin.val_inj,(Fintype.equivFin (Quotient r)).injective.eq_iff,Quotient.eq]
theorem qdp {s h : ℕ} (a : ℤ) (n : Fin s → Fin h) :
    Function.Injective (qt (fun _ => a) n) ↔ Function.Injective n := by
  constructor
  · intro hn i j he
    apply hn
    simp [qt,he]
  · intro hn i j he
    apply hn
    have hv : (n i:ℕ)=(n j:ℕ) := by
      exact_mod_cast (add_left_cancel he : (n i:ℤ)=(n j:ℤ))
    exact Fin.ext hv
noncomputable def qa0 {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    {b // b∈qY (α:=Fin h) r} ≃
    {n // n∈qh (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a)} :=
  (qmu r).trans
    ((Equiv.embeddingCongr (Fintype.equivFin (Quotient r)) (Equiv.refl (Fin h))).trans
      ((Equiv.subtypeInjectiveEquivEmbedding _ _).symm.trans
        (Equiv.subtypeEquivRight (fun n => by
          simp only [qh,Finset.mem_filter,Finset.mem_univ,true_and,
            qdp]))))
@[simp] theorem qkm {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈qY (α:=Fin h) r}) (j : Fin (Fintype.card (Quotient r))) :
    (qa0 r h a b).val j=
      qia ⟨b.val,(qcv r b.val).mp b.property⟩
        ((Fintype.equivFin (Quotient r)).symm j) := rfl
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qix {ι α β : Type*} (b : ι → α) (f : α → β) (hf : Function.Injective f) :
    Setoid.ker (f∘b)=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  exact hf.eq_iff
theorem qkX {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (fun i => (qp r i:ℤ))=r := by
  have h := qix (qp r) (fun n : ℕ => (n:ℤ)) (by intro m n hm; exact_mod_cast (show (m:ℤ)=(n:ℤ) from hm))
  exact h.trans (qcG r)
theorem qlg {ι : Type*} [Fintype ι] (b c : ι → ℤ)
    (h : Setoid.ker b=Setoid.ker c) : qJ b=qJ c := by
  classical
  ext S
  simp only [qJ,qH]
  have hc (i j : ι) : b i=b j ↔ c i=c j := by
    change (Setoid.ker b) i j ↔ (Setoid.ker c) i j
    rw [h]
  constructor <;> rintro ⟨hS,he⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mp (he i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mpr (he i hi j hj)⟩
noncomputable def qbj {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Finset (Finset ι) := qJ (fun i => (qp r i:ℤ))
theorem qhN (X M : ℕ) (F : (Fin 0 → ℝ) → ℝ) (b : Fin 0 → ℕ) :
    qd X F M b=F 0 := by
  classical
  have h : Fintype.piFinset (fun i => (M+b i).divisors)={(0 : Fin 0 → ℕ)} := by
    ext d
    simp [funext_iff]
  rw [qd,h,Finset.sum_singleton]
  simp only [qg,Fin.prod_univ_zero,one_mul]
  congr 1
  ext i
  exact Fin.elim0 i
theorem qhy {X M b : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hp : Nat.Prime (M+b)) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : qV G rho) :
    qd X G M (fun _ => b)=G 0 := by
  have ht : (fun _ : Fin 1 => b)=Fin.snoc (0 : Fin 0 → ℕ) b := by ext i; fin_cases i; rfl
  rw [ht,qfy hX hM hp G hrho hbudget,qhN]
  congr 1
theorem qf5 {X M b Y : ℕ} (hX : 2≤X) (hY : M+b≤Y) (hYP : 1≤Y) :
    theta (M+b)/Real.log X≤Real.log Y/Real.log X := by
  apply div_le_div_of_nonneg_right _ (qw hX).le
  by_cases hp : Nat.Prime (M+b)
  · rw [theta,if_pos hp]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hY)
  · rw [theta,if_neg hp]
    exact Real.log_nonneg (by exact_mod_cast hYP)
theorem qiV {X M b Y : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hY : M+b≤Y) (hYP : 1≤Y) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : qV G rho) (hG : G 0=1) :
    theta (M+b)/Real.log X≤(Real.log Y/Real.log X)*qd X G M (fun _ => b)^2 := by
  by_cases hp : Nat.Prime (M+b)
  · rw [qhy hX hM hp G hrho hbudget,hG,one_pow,mul_one]
    exact qf5 hX hY hYP
  · rw [theta,if_neg hp,zero_div]
    exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hYP))
      (qw hX).le) (sq_nonneg _)
theorem qiy {α : Type*} [DecidableEq α]
    (B : Finset α) (f : α → ℝ) :
    (∑ b∈B,f b)^2=(∑ b∈B,f b^2)+∑ b∈B,∑ c∈B.erase b,f b*f c := by
  rw [pow_two,Finset.sum_mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←Finset.sum_erase_add B (fun c => f b*f c) hb]
  ring
theorem qjX {X M Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ b∈B, X<M+b) (hY : ∀ b∈B, M+b≤Y)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : qV G rho) (hG : G 0=1) :
    q8 X B M^2≤(Real.log Y/Real.log X)*q8 X B M+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        qd X G M (fun _ => b)^2*qd X G M (fun _ => c)^2 := by
  classical
  let t := fun b => theta (M+b)/Real.log X
  let q := Real.log Y/Real.log X
  let D := fun b => qd X G M (fun _ => b)
  have ht (b : ℕ) : 0≤t b := div_nonneg (qc8 _) (qw hX).le
  have hq : 0≤q := div_nonneg (Real.log_nonneg (by exact_mod_cast hYP)) (qw hX).le
  have he : q8 X B M=∑ b∈B,t b := by rw [q8,Finset.sum_div]
  have hupper (b : ℕ) (hb : b∈B) : t b≤q := qf5 hX (hY b hb) hYP
  have hmajor (b : ℕ) (hb : b∈B) : t b≤q*(D b)^2 :=
    qiV hX (hM b hb) (hY b hb) hYP G hrho hbudget hG
  rw [he,qiy,Finset.mul_sum,Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b hb
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hupper b hb) (ht b)
  · apply Finset.sum_le_sum
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    have hcB := Finset.mem_of_mem_erase hc
    have hh := mul_le_mul (hmajor b hb) (hmajor c hcB) (ht c)
      (mul_nonneg hq (sq_nonneg (D b)))
    dsimp [q,D] at hh
    nlinarith
noncomputable def qA {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h) : Fin n → ℕ :=
  fun i => a (p i)+(u (p i):ℕ)
theorem qfz {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h)
    (hu : u∈qh (fun j => (a j:ℤ))) :
    qJ (fun i => (qA p a u i:ℤ))=
      qJ (fun i => ((p i).val:ℤ)) := by
  apply qlg
  apply Setoid.ext
  intro i j
  have hi := (Finset.mem_filter.mp hu).2
  change ((qA p a u i:ℤ)=(qA p a u j:ℤ)) ↔
    ((p i).val:ℤ)=((p j).val:ℤ)
  have he (i : Fin n) : (qA p a u i:ℤ)=qt (fun j => (a j:ℤ)) u (p i) := by
    simp only [qA,qt,Nat.cast_add]
  rw [he,he,hi.eq_iff]
  constructor
  · intro h; rw [h]
  · intro h; apply Fin.ext; exact_mod_cast h
theorem qf6 {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin s → ℕ) (u : Fin s → Fin h) :
    (Finset.univ.image fun i => (qA p a u i:ℤ))=
      Finset.univ.image (qt (fun j => (a j:ℤ)) u) := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p i,by simp only [qt,qA,Nat.cast_add]⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,rfl⟩ := hp j
    exact ⟨i,by simp only [qt,qA,Nat.cast_add]⟩
theorem qdq {n s : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) :
    (∑ S∈qJ (fun i => ((p i).val:ℤ)),(-1:ℤ)^S.card)=-(s:ℤ) := by
  classical
  rw [qlD]
  have he : (Finset.univ.image fun i => ((p i).val:ℤ))=
      Finset.univ.image (fun j : Fin s => (j.val:ℤ)) := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨p i,rfl⟩
    · rintro ⟨j,rfl⟩; obtain ⟨i,rfl⟩ := hp j; exact ⟨i,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij; apply Fin.ext; exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)
theorem qkY {s h : ℕ} (a : Fin s → ℤ)
    (f g : (Fin s → Fin h) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (herr : ∀ u∈qh a, ‖(L:ℂ)^s*f u-g u‖≤E) :
    ‖(∑ u∈qh a,f u)-(∑ u∈qh a,g u)/(L:ℂ)^s‖≤((h:ℝ)/L)^s*E := by
  classical
  have hb : ‖∑ u∈qh a,((L:ℂ)^s*f u-g u)‖≤(h:ℝ)^s*E := by
    calc
      _ ≤ ∑ _u∈qh (h:=h) a,E := norm_sum_le_of_le _ herr
      _ = ((qh (h:=h) a).card:ℝ)*E := by simp
      _ ≤ (h:ℝ)^s*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        have hc := Finset.card_le_card (show qh (h:=h) a⊆Finset.univ from Finset.subset_univ _)
        simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
          (show ((qh (h:=h) a).card:ℝ)≤(Fintype.card (Fin s → Fin h):ℝ) from by exact_mod_cast hc)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hb
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ u∈qh a,f u)-(∑ u∈qh a,g u)/(L:ℂ)^s=
      ((L:ℂ)^s*(∑ u∈qh a,f u)-∑ u∈qh a,g u)/(L:ℂ)^s := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans hb
  apply le_of_eq
  rw [div_pow]
  field_simp
theorem qed (s : ℕ) (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ)
    (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (Fin s → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop,0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ u∈qh (a X),‖(L X:ℂ)^s*f X u-g X u‖≤E X) :
    Tendsto (fun X => (∑ u∈qh (a X),f X u)-
      (∑ u∈qh (a X),g X u)/(L X:ℂ)^s) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun X => ((H X:ℝ)/L X)^s*|E X|)
  · filter_upwards [hL,herr] with X hLX hX
    exact qkY (a X) (f X) (g X) hLX (abs_nonneg _) (fun u hu =>
      (hX u hu).trans (le_abs_self _))
  · simpa only [abs_zero,mul_zero] using (hHL.pow s).mul hE.abs
theorem qfd {s h K : ℕ} (a : Fin s → ℕ) (ha : ∀ j,a j≤K*h) :
    qcs (h:=h) (fun j => (a j:ℤ)) ((K+1)*h) := by
  intro u i j
  dsimp [qt]
  have hi := (u i).isLt
  have hj := (u j).isLt
  have hai := ha i
  have haj := ha j
  have hk : K*h+h=(K+1)*h := by ring
  omega
theorem qes {n s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (p : Fin (n+1) → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*qb lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈qh (h:=qb lam X) (fun j => (a X j:ℤ)),
      (qj X (fun m => qd X F m (qA p (a X) u)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^s*qE
        (qq (qf (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (qJ (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := qJ (fun i => ((p i).val:ℤ))
  let c := qE (qq (qf (Fin (n+1)))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := qb lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin s → Fin (H X)) =>
    (qj X (fun m => qd X F m (qA p (a X) u)):ℂ)
  let g := fun X (u : Fin s → Fin (H X)) =>
    (qay (Finset.univ.image (qt (az X) u)):ℂ)*c
  obtain ⟨E,hE,herr⟩ := qfn F rho hrho hrho1 hbudget
    hF hFs M hM hbound B (qhc _) s 2 (by omega)
    (qdq p hp)
  have herror : ∀ᶠ X in atTop, ∀ u∈qh (az X),
      ‖(Real.log X:ℂ)^s*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,qcF hlam.le (2*(K+1))]
      with X hX haX hcut
    intro u hu
    have hb (i : Fin (n+1)) : qA p (a X) u i≤(K+1)*H X := by
      have hi := (u (p i)).isLt
      have hh := haX (p i)
      dsimp [H] at hi
      dsimp [qA,H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (qA p (a X) u) (qfz p (a X) u hu)
       ((K+1)*H X) hb (by simpa only [Nat.mul_assoc] using hcut)
    rw [qf6 p hp] at hz
    exact hz
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact qw hX
  have hHL := qc2 hlam.le
  have he := qed s H az (fun X => Real.log X) E lam f g hL hHL hE herror
  have hmean : Tendsto (fun X => qaH (h:=H X) (az X)) atTop (𝓝 1) := by
    apply qdo s (K:=K+1) (by omega) H az (qbV hlam)
    filter_upwards [ha] with X hX
    exact qfd (a X) hX
  have hmain : Tendsto (fun X => (∑ u∈qh (az X),g X u)/(Real.log X:ℂ)^s)
      atTop (𝓝 ((lam:ℂ)^s*c)) := by
    have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
    have hh' := hh.mul_const c
    simp only [Complex.ofReal_one,mul_one] at hh'
    apply hh'.congr'
    filter_upwards [hL,(qbV hlam).eventually_ge_atTop 1] with X hLX hHX
    have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (qaH (h:=H X) (az X):ℂ)*c =
      (∑ u∈qh (az X),g X u)/(Real.log X:ℂ)^s
    simp only [g,←Finset.sum_mul,←Complex.ofReal_sum,qaH,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
    rw [div_pow]
    field_simp
  have h := he.add hmain
  simp only [sub_add_cancel,zero_add] at h
  exact h
theorem qmh {X : ℕ} (f g : ℕ → ℝ)
    (h : ∀ m∈Finset.Ioc X (2*X),f m≤g m) : qj X f≤qj X g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg X)
theorem qm4 (X : ℕ) (f g : ℕ → ℝ) :
    qj X (fun m => f m+g m)=qj X f+qj X g := by
  rw [qj,Finset.sum_add_distrib,add_div]
  rfl
theorem qbx (X : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    qj X (fun m => c*f m)=c*qj X f := by
  simp only [qj,←Finset.mul_sum,mul_div_assoc]
theorem qaF {α : Type*} (X : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    qj X (fun m => ∑ i∈S,f i m)=∑ i∈S,qj X (f i) := by
  unfold qj
  rw [Finset.sum_comm,Finset.sum_div]
theorem qf7 {X Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, X < m+b)
    (hY : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, m+b ≤ Y)
    (W : ℕ → ℝ) (hW : ∀ m∈Finset.Ioc X (2*X),0≤W m)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : qV G rho) (hG : G 0=1) :
    qj X (fun m => W m*q8 X B m^2)≤
      (Real.log Y/Real.log X)*qj X (fun m => W m*q8 X B m)+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        qj X (fun m => W m*qd X G m (fun _ => b)^2*
          qd X G m (fun _ => c)^2) := by
  classical
  have hh := qmh (X:=X) (fun m => W m*q8 X B m^2)
    (fun m => W m*((Real.log Y/Real.log X)*q8 X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        qd X G m (fun _ => b)^2*qd X G m (fun _ => c)^2)) (by
      intro m hm
      exact mul_le_mul_of_nonneg_left (qjX hX hYP B
        (hM m hm) (hY m hm) G hrho hbudget hG) (hW m hm))
  have he : (fun m => W m*((Real.log Y/Real.log X)*q8 X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        qd X G m (fun _ => b)^2*qd X G m (fun _ => c)^2))=
      (fun m => (Real.log Y/Real.log X)*(W m*q8 X B m)+
        (Real.log Y/Real.log X)^2*(∑ b∈B,∑ c∈B.erase b,
          W m*qd X G m (fun _ => b)^2*qd X G m (fun _ => c)^2)) := by
    funext m
    have hs : (∑ b∈B,∑ c∈B.erase b,
        W m*qd X G m (fun _ => b)^2*qd X G m (fun _ => c)^2)=
        W m*(∑ b∈B,∑ c∈B.erase b,
          qd X G m (fun _ => b)^2*qd X G m (fun _ => c)^2) := by
      simp only [Finset.mul_sum,mul_assoc]
    rw [hs]
    ring
  rw [he,qm4,qbx,qbx,
    qaF] at hh
  simpa only [qaF] using hh
theorem qet {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => Real.log (2*X+2*qb lam X)/Real.log X) atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun X : ℕ => (Real.log (X:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hH : Tendsto (fun X : ℕ => (qb lam X:ℝ)/(X:ℝ)) atTop (𝓝 0) := by
    have hlogratio : Tendsto (fun X : ℕ => Real.log (X:ℝ)/(X:ℝ)) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    apply squeeze_zero' (Eventually.of_forall (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact div_le_div_of_nonneg_right (qcx hlam hX) (Nat.cast_nonneg X)
    · simpa only [mul_div_assoc,mul_zero] using hlogratio.const_mul lam
  have harg : Tendsto (fun X : ℕ => 2+2*(qb lam X:ℝ)/(X:ℝ)) atTop (𝓝 2) := by
    simpa only [mul_zero,add_zero,mul_div_assoc] using tendsto_const_nhds.add (hH.const_mul 2)
  have hh := ((Real.continuousAt_log (by norm_num : (2:ℝ)≠0)).tendsto.comp harg).mul hinv
  have hh' := (tendsto_const_nhds (x := (1:ℝ))).add hh
  simp only [mul_zero,add_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXP : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hL := qw hX
  have hA : 0<2+2*(qb lam X:ℝ)/(X:ℝ) := by positivity
  have he : (2*(X:ℝ)+2*qb lam X)=(X:ℝ)*(2+2*(qb lam X:ℝ)/(X:ℝ)) := by
    field_simp
  simp only [Function.comp_apply]
  rw [he,Real.log_mul hXP.ne' hA.ne',add_div,div_self hL.ne']
  rfl
theorem qfo {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆qe 1 tau ∧ (∀ v,0≤f v) ∧ (∫ v,f v)=1 := by
  have hopen : IsOpen (qe 1 tau) := by
    have he : qe 1 tau=(fun v : Fin 1 → ℝ => v 0) ⁻¹' Ioo 0 tau := by
      ext v
      simp [qe,qdx,Fin.forall_fin_one]
    rw [he]
    exact isOpen_Ioo.preimage (continuous_apply 0)
  have hmem : (fun _ : Fin 1 => tau/2)∈qe 1 tau := by
    simp only [qe,Set.mem_ofPred_eq,qdx,Fin.sum_univ_one]
    constructor
    · intro i; positivity
    · linarith
  obtain ⟨f,hs,hc,hf,h01,h1⟩ := exists_contDiff_tsupport_subset (n:=(⊤:ℕ∞)) (hopen.mem_nhds hmem)
  have hn : ∀ v,0≤f v := fun v => (h01 (Set.mem_range_self v)).1
  let A := ∫ v,f v
  have hA : 0<A := integral_pos_of_integrable_nonneg_nonzero hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hc) hn (by rw [h1]; norm_num)
  let g := fun v => f v/A
  have hgc : HasCompactSupport g := hc.comp_left (g:=fun x : ℝ => x/A) (by simp)
  have hgs : tsupport g⊆qe 1 tau :=
    (tsupport_comp_subset (g:=fun x : ℝ => x/A) (by simp) f).trans hs
  refine ⟨g,hf.div_const A,hgc,hgs,fun v => div_nonneg (hn v) hA.le,?_⟩
  rw [show g=(fun v => f v/A) from rfl,integral_div]
  exact div_self hA.ne'
theorem qkn {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆qe 1 tau ∧
      qV (qa tau f) tau ∧
      ContDiff ℝ ∞ (qa tau f) ∧
      HasCompactSupport (qa tau f) ∧
      qa tau f 0=1 := by
  obtain ⟨f,hf,hc,hs,_hn,h1⟩ := qfo htau
  refine ⟨f,hf,hc,hs,qaV tau f hs,
    qak tau f hc hf,qac tau f hc,?_⟩
  rw [q6 tau f hs 0 (fun _ => le_rfl)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,h1]
  intro v hv
  by_contra hne
  apply hv
  intro i
  exact (hs (subset_tsupport f hne)).1 i |>.le
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qjr {s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*qb lam X) (c : ℂ) :
    Tendsto (fun X : ℕ =>
      (∑ u∈qh (h:=qb lam X) (fun j => (a X j:ℤ)),
        (qay (Finset.univ.image (qt (fun j => (a X j:ℤ)) u)):ℂ)*c)/
        (Real.log X:ℂ)^s) atTop (𝓝 ((lam:ℂ)^s*c)) := by
  classical
  let H := qb lam
  let az := fun X j => (a X j:ℤ)
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact qw hX
  have hHL := qc2 hlam.le
  have hmean : Tendsto (fun X => qaH (h:=H X) (az X)) atTop (𝓝 1) := by
    apply qdo s (K:=K+1) (by omega) H az (qbV hlam)
    filter_upwards [ha] with X hX
    exact qfd (a X) hX
  have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
  have hh' := hh.mul_const c
  simp only [Complex.ofReal_one,mul_one] at hh'
  apply hh'.congr'
  filter_upwards [hL,(qbV hlam).eventually_ge_atTop 1] with X hLX hHX
  have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
  have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
  change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (qaH (h:=H X) (az X):ℂ)*c = _
  simp only [←Finset.sum_mul,←Complex.ofReal_sum,qaH,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  dsimp only [az,H]
  dsimp only [H] at hHC
  rw [div_pow]
  field_simp [hHC]
theorem qmD {s h : ℕ} (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈qh (fun j => (a j:ℤ))) :
    (fun j : Fin s => u j.castSucc)∈qh (fun j : Fin s => (a j.castSucc:ℤ)) := by
  classical
  simp only [qh,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
  exact hu.comp (Fin.castSucc_injective s)
theorem qjY {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈qh (fun j => (a j:ℤ))) (i : Fin n) :
    qA p (fun j => a j.castSucc) (fun j => u j.castSucc) i≠
      a (Fin.last s)+(u (Fin.last s):ℕ) := by
  intro he
  have hj : qt (fun j => (a j:ℤ)) u (p i).castSucc=
      qt (fun j => (a j:ℤ)) u (Fin.last s) := by
    dsimp only [qA] at he
    dsimp only [qt]
    exact_mod_cast he
  have hi := (Finset.mem_filter.mp hu).2 hj
  exact Fin.castSucc_ne_last (p i) hi
theorem qhz {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h) :
    insert ((a (Fin.last s)+(u (Fin.last s):ℕ):ℕ):ℤ)
      (Finset.univ.image fun i => (qA p (fun j => a j.castSucc)
        (fun j => u j.castSucc) i:ℤ))=
      Finset.univ.image (qt (fun j => (a j:ℤ)) u) := by
  classical
  rw [qf6 p hp]
  ext x
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨Fin.last s,by simp only [qt,Nat.cast_add]⟩
    · exact ⟨j.castSucc,rfl⟩
  · rintro ⟨j,rfl⟩
    cases j using Fin.lastCases with
    | last => left; simp only [qt,Nat.cast_add]
    | cast j => exact Or.inr ⟨j,rfl⟩
theorem qfe (hBV : qN) {n s K : ℕ}
    {lam : ℝ} (hlam : 0<lam) (p : Fin n → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin (s+1) → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*qb lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈qh (h:=qb lam X) (fun j => (a X j:ℤ)),
      (qj X (fun m => qd X F m
        (qA p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
        theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(s+1)*qE
        (qq (qf (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (qJ (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := qJ (fun i => ((p i).val:ℤ))
  let c := qE (qq (qf (Fin n))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := qb lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin (s+1) → Fin (H X)) =>
    (qj X (fun m => qd X F m
      (qA p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
      theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)
  let g := fun X (u : Fin (s+1) → Fin (H X)) =>
    (qay (Finset.univ.image (qt (az X) u)):ℂ)*c
  have hD : (0:ℝ)<(K+1:ℕ)*lam := mul_pos (by positivity) hlam
  have hH : ∀ᶠ X : ℕ in atTop, (((K+1)*H X:ℕ):ℝ)≤((K+1:ℕ):ℝ)*lam*(Real.log X)^(1:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    simpa only [Nat.cast_mul,Real.rpow_one,mul_assoc] using
      mul_le_mul_of_nonneg_left (qcx hlam.le hX) (Nat.cast_nonneg (K+1))
  obtain ⟨E,hE,herr⟩ := qf0 hBV F rho hrho hrhohalf hbudget
    hF hFs M hM hbound B (qhc _) s 2 (by omega)
    (qdq p hp) (fun X => (K+1)*H X) hD hH
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact qw hX
  have herror : ∀ᶠ X in atTop, ∀ u∈qh (az X),
      ‖(Real.log X:ℂ)^(s+1)*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,hL,qcF hlam.le (2*(K+1))]
      with X hX haX hLX hcut
    intro u hu
    have hb (j : Fin (s+1)) : a X j+(u j:ℕ)≤(K+1)*H X := by
      have hi := (u j).isLt
      have hh := haX j
      dsimp [H] at hi
      dsimp [H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (qA p (fun j => a X j.castSucc) (fun j => u j.castSucc))
      (qfz p _ _ (qmD (a X) u hu))
      (a X (Fin.last s)+(u (Fin.last s):ℕ)) (hb (Fin.last s))
      (qjY p (a X) u hu) ((K+1)*H X)
      (fun i => hb (p i).castSucc) (hb (Fin.last s))
      (by simpa only [Nat.mul_assoc] using hcut)
    rw [qhz p hp] at hz
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    convert hz using 1
    dsimp [f,g,c,az]
    congr 1
    rw [pow_succ]
    field_simp
  have he := qed (s+1) H az (fun X => Real.log X) E lam f g
    hL (qc2 hlam.le) hE herror
  have hmain : Tendsto (fun X => (∑ u∈qh (az X),g X u)/(Real.log X:ℂ)^(s+1))
      atTop (𝓝 ((lam:ℂ)^(s+1)*c)) := by
    simpa only [g,az,H,←Finset.sum_mul] using qjr hlam a ha c
  have hh := he.add hmain
  simp only [sub_add_cancel,zero_add] at hh
  exact hh
noncomputable def qaC {ι : Type*} [Fintype ι] (r : Setoid ι) :
    ι → Fin (Fintype.card (Quotient r)) :=
  fun i => Fintype.equivFin (Quotient r) (Quotient.mk r i)
theorem qbK {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Function.Surjective (qaC r) := by
  intro j
  obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
  refine ⟨i,?_⟩
  simp only [qaC,hi,Equiv.apply_symm_apply]
theorem qbk {n : ℕ} (r : Setoid (Fin n)) (h a : ℕ)
    (b : {b // b∈qY (α:=Fin h) r}) :
    qA (qaC r) (fun _ => a)
      (qa0 r h a b).val=(fun i => a+(b.val i:ℕ)) := by
  funext i
  simp only [qA,qaC,qkm,Equiv.symm_apply_apply]
  rfl
theorem qiW {n : ℕ} (r : Setoid (Fin n)) (h a X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈qY (α:=Fin h) r,
      (qj X (fun m => qd X F m (fun i => a+(b i:ℕ))):ℂ))=
    ∑ u∈qh (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => (a:ℤ)),
      (qj X (fun m => qd X F m (qA (qaC r) (fun _ => a) u)):ℂ) := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (qa0 r h a)
  intro b
  rw [qbk]
theorem qkZ {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+1))) (a : ℕ → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop,a X≤K*qb lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈qY (α:=Fin (qb lam X)) r,
      (qj X (fun m => qd X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 ((lam:ℂ)^Fintype.card (Quotient r)*qE
        (qq (qf (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (qJ (fun i => (qp r i:ℤ))))) := by
  have hh := qes hlam (qaC r) (qbK r)
    (fun X _ => a X) (ha.mono (fun _ h _ => h)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  have he : (fun X : ℕ => ∑ b∈qY (α:=Fin (qb lam X)) r,
      (qj X (fun m => qd X F m (fun i => a X+(b i:ℕ))):ℂ))=
      (fun X : ℕ => ∑ u∈qh (h:=qb lam X) (fun _ => (a X:ℤ)),
        (qj X (fun m => qd X F m (qA (qaC r) (fun _ => a X) u)):ℂ)) := by
    funext X
    exact qiW r _ _ _ F
  rw [he]
  exact hh
theorem qgm {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*qb lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℂ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+1) → Fin (qb lam X),
      k (Setoid.ker b)*(qj X (fun m => qd X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),k r*((lam:ℂ)^Fintype.card (Quotient r)*qE
        (qq (qf (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (qJ (fun i => (qp r i:ℤ)))))) := by
  classical
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (qkZ hlam r a ha F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+1)), k r*∑ b∈qY (α:=Fin (qb lam X)) r,
        (qj X (fun m => qd X F m (fun i => a X+(b i:ℕ))):ℂ)) =
        ∑ r : Setoid (Fin (n+1)), ∑ b∈qY (α:=Fin (qb lam X)) r,
          k (Setoid.ker b)*(qj X (fun m => qd X F m (fun i => a X+(b i:ℕ))):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(qcv r b).mp hb]
      _ = _ := qhh _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)
def qo {n : ℕ} (e : Equiv.Perm (Fin n)) : Fin (n+n) → Fin n := Fin.append id e
theorem qff {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => qo e i=r), w i)=w (r.castAdd n)+w ((e.symm r).natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [qo,←Equiv.eq_symm_apply]
@[simp] theorem qeJ {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    (Finset.univ.filter fun i => qo e i=r).card=2 := by
  simpa using qff e r (fun _ => (1:ℕ))
theorem qdF {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => qo e i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => qo e i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
theorem qlh {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin (n+n) → ℂ) :
    qaj (qx (qo e) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w ((e.symm i).natAdd n))⁻¹) := by
  rw [qeH (qo e) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [qdF,qeJ])]
  simp only [qdF,qeJ,Finset.filter_true,
    qff]
noncomputable def qb9 {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) : EuclideanSpace ℝ (Fin (n+n)) :=
  EuclideanSpace.single (i.castAdd n) 1+EuclideanSpace.single ((e.symm i).natAdd n) 1
theorem qgB {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    qv (qf (Fin (n+n))) (qb9 e i) u =
      qz (u (i.castAdd n))+qz (u ((e.symm i).natAdd n)) := by
  unfold qb9
  simp only [qv,map_add,inner_add_right,Complex.ofReal_add,
    qcN]
  simp [qz,EuclideanSpace.inner_single_right]
  ring
theorem qlH {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    0<qf (Fin (n+n)) (qb9 e i) := by
  have h := congrArg Complex.re (qgB e i 0)
  simp only [qhM,Complex.add_re,qlO] at h
  rw [h]
  norm_num
theorem qdG {n : ℕ} (e : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (qaQ (qb9 e) y).ofLp=Fin.append y (y ∘ e) := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [qaQ,qb9,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,qf4]
  | right i =>
    have he (x : Fin n) : i=e.symm x ↔ x=e i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    simp [qaQ,qb9,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,qkV,he]
theorem qfA {n : ℕ} (e : Equiv.Perm (Fin n))
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    qE (qq (qf (Fin (n+n))) F hF hFs)
      (qx (qo e) Finset.univ) =
      ∫ y, qI (q3 (Fin (n+n))) F (qaQ (qb9 e) y)
        ∂qD (Fin n) := by
  rw [←qdc (qf (Fin (n+n)))
    (q3 (Fin (n+n))) F hF hFs (qb9 e) (qlH e)]
  unfold qE
  apply integral_congr_ae
  filter_upwards [] with u
  rw [qW,qlh,qbT]
  simp only [qgB,mul_assoc]
theorem qf8 {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ qe n tau) (hsym : qat f)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (qa (tau+tau) (qi f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (qa (tau+tau) (qi f f) v.ofLp:ℂ))) :
    qE (qq (qf (Fin (n+n)))
      (fun v => (qa (tau+tau) (qi f f) v.ofLp:ℂ)) hF hFs)
      (qx (qo e) Finset.univ) = (q7 f:ℂ) := by
  rw [qfA]
  have he : (∫ y, qI (q3 (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (qa (tau+tau) (qi f f) v.ofLp:ℂ)) (qaQ (qb9 e) y)
      ∂qD (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂qD (Fin n) := by
    apply integral_congr_ae
    rw [qaO]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [qcl (tau+tau) (qi f f)
      (qn f f hf hf) (qs f f hfs hfs)
      (qU f f hsupp hsupp)]
    · rw [qdG,qa6,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [qdG]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,qaO]
  congr 1
  unfold q7
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]
def qmi {ι α : Type*} (e : Equiv.Perm ι) : (ι → α) ≃ (ι → α) where
  toFun f := f ∘ e
  invFun f := f ∘ e.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp
theorem qc3 {n : ℕ} {α : Type*}
    (a b : Fin n → α) (hb : Function.Injective b)
    (hab : Set.range a=Set.range b) : ∃ e : Equiv.Perm (Fin n), b=a ∘ e := by
  classical
  have hs : ∀ i,∃ j,a j=b i := by
    intro i
    have : b i ∈ Set.range a := hab.symm ▸ Set.mem_range_self i
    exact this
  choose e he using hs
  have hei : Function.Injective e := by
    intro i j hij
    apply hb
    rw [←he i,←he j,hij]
  exact ⟨Equiv.ofBijective e ⟨hei,Finite.surjective_of_injective hei⟩,by funext i; exact (he i).symm⟩
noncomputable def qu {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h, k (Setoid.ker b)*qd X F m (fun i => a+(b i:ℕ))
noncomputable def ql {n p : ℕ}
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) : Setoid (Fin (n+p)) → ℝ :=
  fun r => k (Setoid.comap (Fin.castAdd p) r)*l (Setoid.comap (Fin.natAdd n) r)
@[simp] theorem qhi {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]
@[simp] theorem qgn {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]
theorem qfN {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    qu X h a F k m * qu X h a G l m =
    qu X h a (qi F G) (ql k l) m := by
  classical
  unfold qu
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [ql,qhi,qgn]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,qfL]
  ring
theorem qli (X h a : ℕ) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    qj X (qu X h a F k)=
    ∑ b : Fin n → Fin h, k (Setoid.ker b)*qj X (fun m => qd X F m (fun i => a+(b i:ℕ))) := by
  unfold qu
  rw [qaF]
  simp only [qbx]
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qiz {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*qb lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℝ) :
    Tendsto (fun X : ℕ => (qj X (qu X (qb lam X) (a X) F k):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),(k r:ℂ)*((lam:ℂ)^Fintype.card (Quotient r)*qE
        (qq (qf (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (qJ (fun i => (qp r i:ℤ)))))) := by
  simpa only [qli,Complex.ofReal_sum,Complex.ofReal_mul] using
    qgm hlam a ha F rho hrho hrho1 hbudget hF hFs M hM hbound
      (fun r => (k r:ℂ))
theorem qmW {X : ℕ} (hX : X≠0) (c : ℝ) : qj X (fun _ => c)=c := by
  unfold qj
  simp only [Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul]
  rw [show 2*X-X=X by omega]
  simp [hX]
@[simp] theorem qmj (X h a m : ℕ)
    (F : (Fin 0 → ℝ) → ℝ) (k : Setoid (Fin 0) → ℝ) :
    qu X h a F k m=k ⊥*F 0 := by
  unfold qu
  simp only [qhN]
  have he (b : Fin 0 → Fin h) : Setoid.ker b=⊥ := by
    apply Setoid.ext
    intro i
    exact Fin.elim0 i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul]
theorem qgL {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*qb lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => qj X (qu X (qb lam X) (a X) F k))
      atTop (𝓝 c) := by
  cases n with
  | zero =>
    refine ⟨k ⊥*F 0,?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    have he : qu X (qb lam X) (a X) F k=(fun _ => k ⊥*F 0) :=
      funext (fun m => qmj X _ _ m F k)
    rw [he,qmW (by omega : X≠0)]
  | succ n =>
    have hc : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin (n+1)) ℝ).toHomeomorph.isClosedEmbedding).comp_left
        Complex.ofReal_zero
    have hs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hFs.comp (EuclideanSpace.equiv (Fin (n+1)) ℝ).contDiff)
    obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
    have hM0 : 0≤M := (norm_nonneg (F 0)).trans (hM 0)
    have hh := qiz hlam a ha F rho hrho hrho1 hbudget hc hs M hM0
      (fun v _ => by simpa only [Real.norm_eq_abs] using hM v) k
    exact ⟨_,Complex.continuous_re.continuousAt.tendsto.comp hh⟩
theorem qV.tensor {n p : ℕ} {F : (Fin n → ℝ) → ℝ} {G : (Fin p → ℝ) → ℝ}
    {a b : ℝ} (hF : qV F a) (hG : qV G b) :
    qV (qi F G) (a+b) := by
  intro v hv hsum
  unfold qi
  rw [Fin.sum_univ_add] at hsum
  by_cases hf : a<∑ i : Fin n,v (i.castAdd p)
  · rw [hF _ (fun i => hv (i.castAdd p)) hf,zero_mul]
  · rw [hG _ (fun i => hv (i.natAdd n)) (by linarith),mul_zero]
theorem qhj {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*qb lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho4 : 4*rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => qj X
      (fun m => qu X (qb lam X) (a X) F k m^4)) atTop (𝓝 c) := by
  let F2 := qi F F
  let k2 := ql k k
  have hc2 := qn F F hF hF
  have hs2 := qs F F hFs hFs
  obtain ⟨c,hc⟩ := qgL hlam a ha (qi F2 F2)
    ((rho+rho)+(rho+rho)) (by positivity) (by linarith)
    ((hbudget.tensor hbudget).tensor (hbudget.tensor hbudget))
    (qn F2 F2 hc2 hc2) (qs F2 F2 hs2 hs2)
    (ql k2 k2)
  refine ⟨c,?_⟩
  convert hc using 1
  ext X
  congr 1
  funext m
  rw [←qfN,←qfN]
  ring
theorem ql3 {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∑ i∈S,f i)^4≤(S.card:ℝ)^3*∑ i∈S,f i^4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=f)
  have h2 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=fun i => f i^2)
  have h3 := mul_self_le_mul_self (sq_nonneg (∑ i∈S,f i)) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (S.card:ℝ))
  simp only [←pow_mul] at h3 h4
  nlinarith only [h3,h4]
noncomputable def qc (n : ℕ) (r : Setoid (Fin n)) : ℝ :=
  if r=⊥ then (n.factorial:ℝ)⁻¹ else 0
noncomputable def qb0 (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), qu X (qb lam X) (qb lam X+1)
    (qa tau (f j)) (qc j) m
theorem qcA {lam : ℝ} (hlam : 0<lam) :
    ∀ᶠ X : ℕ in atTop,qb lam X+1≤2*qb lam X := by
  filter_upwards [(qbV hlam).eventually_ge_atTop 1] with X hX
  omega
theorem qko {α : Type*} [Fintype α]
    (f : α → ℕ → ℕ → ℝ)
    (h : ∀ j,∃ c : ℝ,Tendsto (fun X => qj X (fun m => f j X m^4)) atTop (𝓝 c)) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      qj X (fun m => (∑ j,f j X m)^4)≤M := by
  classical
  choose c hc using h
  let C := (Fintype.card α:ℝ)^3*∑ j,c j
  have ht : Tendsto (fun X => (Fintype.card α:ℝ)^3*∑ j,qj X (fun m => f j X m^4))
      atTop (𝓝 C) := (tendsto_finsetSum Finset.univ (fun j _ => hc j)).const_mul _
  refine ⟨|C|+1,by positivity,?_⟩
  filter_upwards [(tendsto_order.mp ht).2 (|C|+1) (by linarith [le_abs_self C])] with X hX
  apply le_trans ?_ hX.le
  calc
    _ ≤ qj X (fun m => (Fintype.card α:ℝ)^3*∑ j,f j X m^4) :=
      qmh _ _ (fun m _ => by
        simpa only [Finset.card_univ] using
          (ql3 Finset.univ (fun j => f j X m)))
    _ = _ := by rw [qbx,qaF]
theorem qiX {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      qj X (fun m => qb0 tau lam k f X m^4)≤M := by
  apply qko
  intro j
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact qhj hlam (fun X => qb lam X+1)
    (qcA hlam) (qa tau (f j)) tau htau htau4
    (qaV tau (f j) hfj.2.2.1)
    (qac tau (f j) hfj.2.1)
    (qak tau (f j) hfj.2.1 hfj.1) (qc j)
noncomputable def qF {n : ℕ} (e : Equiv.Perm (Fin n)) : Setoid (Fin (n+n)) :=
  Setoid.ker (qo e)
@[simp] theorem qhO {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.castAdd n) (qF e)=⊥ := by
  apply Setoid.ext
  intro i j
  change qo e (i.castAdd n)=qo e (j.castAdd n) ↔ i=j
  simp [qo]
@[simp] theorem qhk {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.natAdd n) (qF e)=⊥ := by
  apply Setoid.ext
  intro i j
  change qo e (i.natAdd n)=qo e (j.natAdd n) ↔ i=j
  simp [qo]
theorem qjZ {n : ℕ} : Function.Injective (@qF n) := by
  intro e f hef
  apply Equiv.ext
  intro i
  have he : (qF e) ((e i).castAdd n) (i.natAdd n) := by
    change qo e ((e i).castAdd n)=qo e (i.natAdd n)
    simp [qo]
  rw [hef] at he
  change qo f ((e i).castAdd n)=qo f (i.natAdd n) at he
  simpa [qo] using he
theorem qd0 {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Fintype.card (Quotient (qF e))=n := by
  have hs : Function.Surjective (qo e) := by
    intro j
    exact ⟨j.castAdd n,by simp [qo]⟩
  have eqv : Quotient (qF e) ≃ Fin n :=
    Setoid.quotientKerEquivOfSurjective (qo e) hs
  exact (Fintype.card_congr eqv).trans (Fintype.card_fin n)
theorem qfg {α β : Type*} (f : α → β) :
    Setoid.ker f=⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    change (Setoid.ker f) x y at hxy
    rw [h] at hxy
    exact hxy
  · intro h
    apply Setoid.ext
    intro x y
    exact h.eq_iff
theorem qbb {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.castAdd n) r=⊥) :
    Function.Injective (fun i : Fin m => qp r (i.castAdd n)) := by
  apply (qfg _).mp
  have he : Setoid.ker (fun i : Fin m => qp r (i.castAdd n))=
      Setoid.comap (Fin.castAdd n) (Setoid.ker (qp r)) := rfl
  rw [he,qcG,h]
theorem qa7 {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.natAdd m) r=⊥) :
    Function.Injective (fun i : Fin n => qp r (i.natAdd m)) := by
  apply (qfg _).mp
  have he : Setoid.ker (fun i : Fin n => qp r (i.natAdd m))=
      Setoid.comap (Fin.natAdd m) (Setoid.ker (qp r)) := rfl
  rw [he,qcG,h]
theorem qgC {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a=Set.range b) : m=n := by
  have e : Fin m ≃ Fin n := (Equiv.ofInjective a ha).trans
    ((Equiv.setCongr hab).trans (Equiv.ofInjective b hb).symm)
  simpa using Fintype.card_congr e
theorem qhP {n : ℕ} (r : Setoid (Fin (n+n)))
    (hleft : Setoid.comap (Fin.castAdd n) r=⊥)
    (hright : Setoid.comap (Fin.natAdd n) r=⊥)
    (hrange : Set.range (fun i : Fin n => qp r (i.castAdd n))=
      Set.range (fun i : Fin n => qp r (i.natAdd n))) :
    ∃ e : Equiv.Perm (Fin n),r=qF e := by
  let a := fun i : Fin n => qp r (i.castAdd n)
  let b := fun i : Fin n => qp r (i.natAdd n)
  have ha : Function.Injective a := qbb r hleft
  have hb : Function.Injective b := qa7 r hright
  obtain ⟨e,he⟩ := qc3 a b hb hrange
  refine ⟨e,?_⟩
  rw [←qcG r]
  have hf : qp r=a ∘ qo e := by
    funext i
    cases i using Fin.addCases with
    | left i => simp [a,qo]
    | right i => simpa [b,qo] using congrFun he i
  rw [hf,qix _ _ ha]
  rfl
theorem qlj {n : ℕ} (e : Equiv.Perm (Fin n)) :
    qbj (qF e)=qx (qo e) Finset.univ := by
  classical
  have hi : Finset.univ.image (qo e)=Finset.univ := by
    ext j
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    exact ⟨j.castAdd n,by simp [qo]⟩
  rw [←hi]
  unfold qbj qJ
  ext S
  simp only [qH]
  have he (i j : Fin (n+n)) :
      (qp (qF e) i:ℤ)=(qp (qF e) j:ℤ) ↔
        qo e i=qo e j := by
    change (Setoid.ker (fun x => (qp (qF e) x:ℤ))) i j ↔
      (qF e) i j
    rw [qkX]
  simp_rw [he]
theorem qhl {n : ℕ} (c : ℂ) (A : Setoid (Fin (n+n)) → ℂ)
    (hzero : ∀ r,r∉Set.range (@qF n) → A r=0)
    (hvalue : ∀ e : Equiv.Perm (Fin n),A (qF e)=c) :
    (∑ r,A r)=(n.factorial:ℂ)*c := by
  classical
  calc
    _ = ∑ r∈Finset.univ.image (@qF n),A r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      apply hzero r
      rintro ⟨e,rfl⟩
      exact hr (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    _ = ∑ e : Equiv.Perm (Fin n),A (qF e) :=
      Finset.sum_image (fun _ _ _ _ h => qjZ h)
    _ = _ := by simp [hvalue,Fintype.card_perm]
theorem qaw {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
    Complex.ofReal_zero
theorem qaE {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hF.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
noncomputable def qP {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (r : Setoid (Fin n)) : ℂ :=
  qE (qq (qf (Fin n))
    (fun v => (qa tau f v.ofLp:ℂ))
    (qaw _ (qac tau f hf))
    (qaE _ (qak tau f hf hs))) (qbj r)
theorem qeK {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe m tau) (hsg : tsupport g⊆qe n tau)
    (r : Setoid (Fin (m+n)))
    (hl : Setoid.comap (Fin.castAdd n) r=⊥) (hr : Setoid.comap (Fin.natAdd m) r=⊥)
    (hne : Set.range (fun i : Fin m => qp r (i.castAdd n))≠
      Set.range (fun i : Fin n => qp r (i.natAdd m))) :
    qP (tau+tau) (qi f g)
      (qn f g hf hg) (qs f g hfs hgs) r=0 := by
  let a := fun i : Fin m => qp r (i.castAdd n)
  let b := fun i : Fin n => qp r (i.natAdd m)
  have ha := qbb r hl
  have hb := qa7 r hr
  have he : Fin.append a b=qp r := by
    funext i
    cases i using Fin.addCases <;> simp [a,b]
  have hfamily : qbj r=
      qx (Fin.append a b) (Finset.univ.image (Fin.append a b)) := by
    unfold qbj qJ
    ext S
    simp only [qH,he,Int.natCast_inj]
  unfold qP
  rw [hfamily]
  convert qch f g hf hg hfs hgs hsf hsg a b ha hb hne
    (qaw _ (qac _ _ (qn f g hf hg)))
    (qaE _ (qak _ _
      (qn f g hf hg) (qs f g hfs hgs))) using 1
  congr 2
  ext x
  simp
theorem qkp {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆qe n tau) (hsym : qat f)
    (e : Equiv.Perm (Fin n)) :
    qP (tau+tau) (qi f f)
      (qn f f hf hf) (qs f f hfs hfs) (qF e)=
      (q7 f:ℂ) := by
  unfold qP
  rw [qlj]
  exact qf8 e f hf hfs hsf hsym _ _
theorem qdM {n : ℕ} {tau : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆qe n tau) (hsym : qat f) :
    (∑ r : Setoid (Fin (n+n)),
      (ql (qc n) (qc n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f f)
          (qn f f hf hf) (qs f f hfs hfs) r))=
      (qcI lam n*q7 f:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (ql (qc n) (qc n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f f)
          (qn f f hf hf) (qs f f hfs hfs) r)
  have hz : ∀ r,r∉Set.range (@qF n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => qp r (i.castAdd n))≠
            Set.range (fun i : Fin n => qp r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := qhP r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,qeK f f hf hf hfs hfs hsf hsf r hl hr' hne,mul_zero]
      · simp only [A,ql,qc,if_neg hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,ql,qc,if_neg hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (qF e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*(q7 f:ℂ)) := by
    intro e
    simp only [A,ql,qhO,qhk,qc,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      qd0,qkp f hf hfs hsf hsym e,pow_two]
  have hh := qhl _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [qcI,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp
theorem qd1 {m n : ℕ} (hmn : m≠n) {tau : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe m tau) (hsg : tsupport g⊆qe n tau) :
    (∑ r : Setoid (Fin (m+n)),
      (ql (qc m) (qc n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => qp r (i.castAdd n))≠
          Set.range (fun i : Fin n => qp r (i.natAdd m)) := by
        intro he
        exact hmn (qgC _ _ (qbb r hl)
          (qa7 r hr) he)
      rw [qeK f g hf hg hfs hgs hsf hsg r hl hr hne,mul_zero,mul_zero]
    · simp only [ql,qc,if_neg hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [ql,qc,if_neg hl,zero_mul,Complex.ofReal_zero]
theorem qiA {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ)
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    qu X h a F k m=qu X h a G k m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [qce hX m _ F G hFG]
theorem qh3 {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆qe n tau) (hg : tsupport g⊆qe p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    qu X h a (qa tau f) k m*
      qu X h a (qa tau g) l m=
    qu X h a (qa (tau+tau) (qi f g)) (ql k l) m := by
  rw [qfN]
  apply qiA hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,qa6]
  exact (qdf f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm
@[simp] theorem qmX {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆qe 0 tau) (v : Fin 0 → ℝ) :
    qa tau f v=f 0 := by
  rw [q6 tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0
@[simp] theorem qnc (f : (Fin 0 → ℝ) → ℝ) : q7 f=f 0^2 := by
  unfold q7
  have he : (fun x => f x^2)=(fun _ : Fin 0 → ℝ => f 0^2) := by
    funext x
    rw [Subsingleton.elim x 0]
  rw [he,Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qcf {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hsupp : tsupport f⊆qe n tau)
    (hsym : qat f) (e : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    qa tau f (v ∘ e)=qa tau f v := by
  change qa tau f (fun i => v (e i))=qa tau f v
  rw [q6 tau f hsupp _ (fun i => hv (e i)),
    q6 tau f hsupp _ hv]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq : MeasurePreserving q volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq_apply (x : Fin n → ℝ) : q x=x ∘ e := by
    funext i
    simp [q,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have he : q ⁻¹' {x : Fin n → ℝ | ∀ i,v (e i)≤x i}={x : Fin n → ℝ | ∀ i,v i≤x i} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hq_apply,Function.comp_apply]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  have hh := hq.integral_comp' (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f x)
  have hefun : (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f (q x))=
      ({x : Fin n → ℝ | ∀ i,v i≤x i}).indicator f := by
    funext x
    have hx : (∀ i,v (e i)≤q x i) ↔ ∀ i,v i≤x i := by
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq] using
        (Set.ext_iff.mp he x)
    have hm : q x∈{x : Fin n → ℝ | ∀ i,v (e i)≤x i} ↔ x∈{x : Fin n → ℝ | ∀ i,v i≤x i} := hx
    by_cases hvx : x∈{x : Fin n → ℝ | ∀ i,v i≤x i}
    · rw [Set.indicator_of_mem (hm.mpr hvx),Set.indicator_of_mem hvx,hq_apply,hsym]
    · rw [Set.indicator_of_notMem (fun h => hvx (hm.mp h)),Set.indicator_of_notMem hvx]
  rw [hefun,integral_indicator (by measurability), integral_indicator (by measurability)] at hh
  exact hh.symm
theorem qdv {n X m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v)
    (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    qd X F m (b ∘ e)=qd X F m b := by
  classical
  unfold qd
  symm
  apply Finset.sum_equiv (qmi e)
  · intro d
    simp only [Fintype.mem_piFinset,qmi,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d hd
    change qg X F d=qg X F (d ∘ e)
    unfold qg
    have hp : ∀ i,0<d i := fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
    have he : q1 X (d ∘ e)=(q1 X d) ∘ e := rfl
    rw [he,hF e _ (qbB hX hp)]
    congr 1
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
noncomputable def qy {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) : Fin n ↪ Fin h :=
  S.1.orderEmbOfFin S.2 |>.toEmbedding
theorem qdw {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Finset.univ.image (qy S)=S.1 := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro hx
    refine ⟨(S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩,?_⟩
    change ((S.1.orderIsoOfFin S.2) ((S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩)).val=x
    simp
noncomputable def qbu {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    {b : Fin n → Fin h // Function.Injective b} :=
  ⟨qy t.1 ∘ t.2,(qy t.1).injective.comp t.2.injective⟩
theorem qdk {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    Finset.univ.image (qbu t).val=t.1.1 := by
  classical
  rw [←qdw t.1]
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,qbu,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨t.2 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨t.2.symm i,by simpa using hi⟩
theorem qfB (h n : ℕ) :
    Function.Bijective (qbu (h:=h) (n:=n)) := by
  classical
  constructor
  · rintro ⟨S,e⟩ ⟨T,d⟩ he
    have hST : S=T := by
      apply Subtype.ext
      rw [←qdk (S,e),←qdk (T,d),he]
    subst T
    have hed : e=d := by
      apply Equiv.ext
      intro i
      apply (qy S).injective
      exact congrFun (congrArg Subtype.val he) i
    subst d
    rfl
  · intro b
    let S : {S : Finset (Fin h) // S.card=n} :=
      ⟨Finset.univ.image b.val,by rw [Finset.card_image_of_injective _ b.2]; simp⟩
    have he : Set.range (qy S)=Set.range b.val := by
      ext x
      have hh := Finset.ext_iff.mp (qdw S) x
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,S,Set.mem_range] using hh
    obtain ⟨e,he⟩ := qc3 (qy S) b.val b.2 he
    exact ⟨(S,e),Subtype.ext he.symm⟩
noncomputable def qbP {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    qd X F m (fun i => a+(qy S i:ℕ))
theorem qiY {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    qu X h a F (qc n) m=qbP X h a F m := by
  classical
  unfold qu
  have he : (∑ b : Fin n → Fin h, qc n (Setoid.ker b)*
      qd X F m (fun i => a+(b i:ℕ)))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*qd X F m (fun i => a+(b.val i:ℕ)) := by
    simp only [qc,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective qbu (qfB h n))
    (fun t => (n.factorial:ℝ)⁻¹*qd X F m (fun i => a+((qbu t).val i:ℕ)))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold qbP
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      qd X F m (fun i => a+((qbu (S,e)).val i:ℕ))=
      qd X F m (fun i => a+(qy S i:ℕ)) :=
    qdv hX F hsym e (fun i => a+(qy S i:ℕ))
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
noncomputable def qaU (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), qbP X (qb lam X) (qb lam X+1)
    (qa tau (f j)) m
theorem qcP {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (hX : 2≤X) (m : ℕ) : qb0 tau lam k f X m=qaU tau lam k f X m := by
  unfold qb0 qaU
  apply Finset.sum_congr rfl
  intro j _
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact qiY hX _ (qcf _ hfj.2.2.1 hfj.2.2.2)
theorem qh4 {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      qj X (fun m => qaU tau lam k f X m^4)≤M := by
  obtain ⟨M,hM,h⟩ := qiX f hf htau htau4 hlam
  refine ⟨M,hM,?_⟩
  filter_upwards [h,eventually_ge_atTop 2] with X hX hX2
  simpa only [qcP f hf hX2] using hX
noncomputable def qaa (s h : ℕ) : Fin (s+1) → ℕ :=
  Fin.snoc (fun _ => h+1) 1
theorem qj0 {s h : ℕ} (u : Fin s → Fin h) (c : Fin h) :
    Fin.snoc u c∈qh (fun j => (qaa s h j:ℤ)) ↔
      u∈qh (fun _ : Fin s => ((h+1:ℕ):ℤ)) := by
  classical
  simp only [qh,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu i j hij
    have he : qt (fun j => (qaa s h j:ℤ)) (Fin.snoc u c) i.castSucc=
        qt (fun j => (qaa s h j:ℤ)) (Fin.snoc u c) j.castSucc := by
      simpa [qt,qaa] using hij
    exact Fin.castSucc_injective s (hu he)
  · intro hu i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
        have hj := (u j).isLt
        have hc := c.isLt
        simp only [qt,qaa,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        have hi := (u i).isLt
        have hc := c.isLt
        simp only [qt,qaa,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
      | cast j =>
        congr 1
        apply hu
        simpa [qt,qaa] using hij
noncomputable def qmv (s h : ℕ) :
    ({u // u∈qh (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h) ≃
    {u // u∈qh (s:=s+1) (h:=h) (fun j => (qaa s h j:ℤ))} where
  toFun t := ⟨Fin.snoc t.1.1 t.2,(qj0 t.1.1 t.2).mpr t.1.2⟩
  invFun v := (⟨Fin.init v.1,by
      have hv : Fin.snoc (Fin.init v.1) (v.1 (Fin.last s))=v.1 := Fin.snoc_init_self v.1
      exact (qj0 _ _).mp (hv.symm ▸ v.2)⟩,v.1 (Fin.last s))
  left_inv t := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [Fin.init]
    · simp
  right_inv v := by
    apply Subtype.ext
    exact Fin.snoc_init_self v.1
theorem qlI {s h : ℕ} (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈qh (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),∑ c : Fin h,F (Fin.snoc u c))=
      ∑ v∈qh (s:=s+1) (h:=h) (fun j => (qaa s h j:ℤ)),F v := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  calc
    _ = ∑ t : {u // u∈qh (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h,
      F (Fin.snoc t.1.val t.2) := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (qmv s h) _ _ (fun _ => rfl)
theorem qjs {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈qY (α:=Fin h) r,∑ c : Fin h,
      (qj X (fun m => qd X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ))=
    ∑ v∈qh (s:=Fintype.card (Quotient r)+1) (h:=h)
      (fun j => (qaa (Fintype.card (Quotient r)) h j:ℤ)),
      (qj X (fun m => qd X F m
        (qA (qaC r) (fun j => qaa _ h j.castSucc)
          (fun j => v j.castSucc))*
        theta (m+(qaa (Fintype.card (Quotient r)) h (Fin.last (Fintype.card (Quotient r)))+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←qlI]
  simp only [qaa,Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (qa0 r h ((h+1:ℕ):ℤ))
  intro b
  have he := qbk r h (h+1) b
  simp only [he]
theorem qiB {lam : ℝ} (hlam : 0<lam) (s : ℕ) :
    ∀ᶠ X : ℕ in atTop,∀ j,qaa s (qb lam X) j≤2*qb lam X := by
  filter_upwards [qcA hlam] with X hX j
  cases j using Fin.lastCases with
  | last => simp only [qaa,Fin.snoc_last]; omega
  | cast j => simpa only [qaa,Fin.snoc_castSucc] using hX
theorem qlJ (hBV : qN) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈qY (α:=Fin (qb lam X)) r,∑ c : Fin (qb lam X),
      (qj X (fun m => qd X F m (fun i => qb lam X+1+(b i:ℕ))*
        theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*qE
        (qq (qf (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (qJ (fun i => (qp r i:ℤ))))) := by
  have hh := qfe hBV hlam (qaC r) (qbK r)
    (fun X => qaa _ (qb lam X)) (qiB hlam _)
    F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (qjs r _ X F).symm
noncomputable def qaJ (X h m : ℕ) : ℝ :=
  (∑ c : Fin h,theta (m+(1+(c:ℕ))))/Real.log X
theorem qmy (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    qj X (fun m => f m/a)=qj X f/a := by
  simpa only [div_eq_mul_inv,mul_comm] using qbx X a⁻¹ f
theorem qhA {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (qj X (fun m => qu X h (h+1) F k m*qaJ X h m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,
        (qj X (fun m => qd X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  have he (m : ℕ) : qu X h (h+1) F k m*qaJ X h m=
      ∑ b : Fin n → Fin h,∑ c : Fin h,
        k (Setoid.ker b)*(qd X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ))))/Real.log X := by
    unfold qu qaJ
    rw [←mul_div_assoc,Finset.sum_mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_assoc]
  simp only [he,qaF,qmy,qbx,
    Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum,mul_div_assoc]
theorem qjt (hBV : qN) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : qV F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (qj X (fun m =>
      qu X (qb lam X) (qb lam X+1) F k m*
        qaJ X (qb lam X) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*qE
        (qq (qf (Fin n))
          (fun v => (F v.ofLp:ℂ)) (qaw F hF) (qaE F hFs))
        (qbj r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (qlJ hBV hlam r F rho hrho hrhohalf hbudget
      (qaw F hF) (qaE F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [qhA]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈qY (α:=Fin (qb lam X)) r,
        ∑ c : Fin (qb lam X),
        (qj X (fun m => qd X F m (fun i => qb lam X+1+(b i:ℕ))*
          theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)) =
        ∑ r : Setoid (Fin n),∑ b∈qY (α:=Fin (qb lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (qb lam X),
            (qj X (fun m => qd X F m (fun i => qb lam X+1+(b i:ℕ))*
              theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(qcv r b).mp hb]
      _ = _ := qhh _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)
theorem qd2 (hBV : qN) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau) :
    Tendsto (fun X : ℕ => (qj X (fun m =>
      qu X (qb lam X) (qb lam X+1) (qa tau f) (qc n) m*
      qu X (qb lam X) (qb lam X+1) (qa tau g) (qc p) m*
      qaJ X (qb lam X) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))) := by
  have hh := qjt hBV hlam
    (qa (tau+tau) (qi f g)) (tau+tau) (by positivity) (by linarith)
    (qaV _ _ (qU f g hsf hsg))
    (qac _ _ (qn f g hf hg))
    (qak _ _ (qn f g hf hg) (qs f g hfs hgs))
    (ql (qc n) (qc p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 2
  funext m
  rw [qh3 hX _ _ m f g hsf hsg _ _]
theorem qhm (hBV : qN) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆qe n tau) (hsym : qat f) :
    Tendsto (fun X : ℕ => qj X (fun m =>
      qu X (qb lam X) (qb lam X+1) (qa tau f) (qc n) m^2*
      qaJ X (qb lam X) m))
      atTop (𝓝 (lam*qcI lam n*q7 f)) := by
  have hh := qd2 hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [qdM lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'
theorem qhB (hBV : qN) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau) :
    Tendsto (fun X : ℕ => qj X (fun m =>
      qu X (qb lam X) (qb lam X+1) (qa tau f) (qc n) m*
      qu X (qb lam X) (qb lam X+1) (qa tau g) (qc p) m*
      qaJ X (qb lam X) m))
      atTop (𝓝 0) := by
  have hh := qd2 hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [qd1 hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qiZ (hBV : qN) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => qj X (fun m => qb0 tau lam k f X m^2*
      qaJ X (qb lam X) m))
      atTop (𝓝 (lam*qcp lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => qu X (qb lam X) (qb lam X+1)
       (qa tau (f j)) (qc j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => qj X (fun m => H i X m*H j X m*qaJ X (qb lam X) m)) atTop
        (𝓝 (if i=j then lam*qcI lam i*q7 (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using qhm hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [if_neg hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact qhB hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : qj X (fun m => qb0 tau lam k f X m^2*qaJ X (qb lam X) m)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),qj X (fun m => H i X m*H j X m*qaJ X (qb lam X) m) := by
    unfold qb0
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,qaF]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*qcI lam i*q7 (f i))=lam*qcp lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => qcI lam j*q7 (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)
theorem qfC {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (qad f) := by
  let K := (fun v : Fin (n+1) → ℝ => -v (Fin.last n)) '' tsupport f
  have hK : IsCompact K := hf.isCompact.image (continuous_apply _ |>.neg)
  let g : (Fin n → ℝ) → ℝ → ℝ := fun t u => f (Fin.snoc t (-u))
  have hgs : ∀ t u,t∈(Set.univ : Set (Fin n → ℝ)) → u∉K → g t u=0 := by
    intro t u _ hu
    by_contra hn
    apply hu
    refine ⟨Fin.snoc t (-u),subset_tsupport f hn,?_⟩
    simp
  have hsm : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 (-p.2) : Fin (n+1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    cases i using Fin.lastCases with
    | last => simpa using contDiff_snd.neg
    | cast i => simpa [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hh := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ:=volume) (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hK hgs
    (f:=fun _ : ℝ => (1:ℝ)) (continuous_const.locallyIntegrable) (hfs.comp hsm).contDiffOn
  have hg : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ =>
      ((fun _ : ℝ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g p.1) p.2) := by
    rwa [Set.univ_prod_univ,contDiffOn_univ] at hh
  have H := hg.comp (contDiff_id.prodMk (contDiff_const (c:=(0:ℝ))))
  change ContDiff ℝ ∞ (fun x => ∫ t : ℝ, f (Fin.snoc x t))
  simpa only [Function.comp_def,convolution_def,ContinuousLinearMap.mul_apply',one_mul,
    zero_sub,g,neg_neg,qad,id_eq] using H
theorem qdg {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) :
    tsupport (qad f) ⊆
      (fun v : Fin (n+1) → ℝ => fun i : Fin n => v i.castSucc) '' tsupport f := by
  have hk := hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))
  apply closure_minimal _ hk.isClosed
  intro t ht
  by_contra hn
  apply ht
  unfold qad
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_contra hfu
  exact hn ⟨Fin.snoc t u,subset_tsupport f hfu,by ext i; simp⟩
theorem qfh {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (qad f) := by
  exact (hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))).of_isClosed_subset
    (isClosed_tsupport _) (qdg f hf)
theorem qbY {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hs : tsupport f⊆qe (n+1) tau) :
    tsupport (qad f) ⊆qe n tau := by
  intro t ht
  obtain ⟨v,hv,rfl⟩ := qdg f hf ht
  have hv' := hs hv
  refine ⟨fun i => hv'.1 i.castSucc,?_⟩
  have hh : qdx v=qdx (fun i : Fin n => v i.castSucc)+v (Fin.last n) := by
    exact Fin.sum_univ_castSucc (fun i => v i)
  have hp := hv'.1 (Fin.last n)
  linarith [hv'.2]
noncomputable def qk0 {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)
@[simp] theorem qm7 {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    qk0 e i.castSucc=(e i).castSucc := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)))=Fin.castAdd 1 (e i)
  simp
@[simp] theorem qnb {n : ℕ} (e : Equiv.Perm (Fin n)) :
    qk0 e (Fin.last n)=Fin.last n := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))))=Fin.natAdd n (0 : Fin 1)
  simp
theorem qi0 {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hs : qat f) : qat (qad f) := by
  intro e t
  unfold qad
  apply integral_congr_ae
  filter_upwards [] with u
  have he : Fin.snoc (t ∘ e) u=(Fin.snoc t u : Fin (n+1) → ℝ) ∘ qk0 e := by
    ext i
    cases i using Fin.lastCases <;> simp
  rw [he,hs]
theorem qky {n : ℕ} (v : Fin n → ℝ) :
    Measure.pi (fun i => volume.restrict (Ici (v i)))=volume.restrict (Ici v) := by
  rw [←Measure.restrict_pi_pi]
  congr 1
  ext x
  simp
theorem qmw {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : IntegrableOn f (Ici v)) :
    (∫ x in Ici v,f x)=∫ y in Ici (fun i : Fin n => v i.castSucc),
      ∫ a in Ici (v (Fin.last n)),f (Fin.snoc y a) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ici (v i))) (Fin.last n)
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p=Fin.snoc p.2 p.1 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  have hfi : Integrable f (Measure.pi (fun i => volume.restrict (Ici (v i)))) := by
    rw [qky]
    exact hf
  have hh := hm.symm.integral_comp' f
  have hi := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hfi
  dsimp only [e] at he
  simp only [Fin.succAbove_last_apply,he,Function.comp_def,qky] at hh hi
  rw [←hh]
  exact integral_prod_symm _ hi
theorem qhC {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) (hs : tsupport f⊆qe (n+1) tau)
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    qa tau f (Fin.snoc v 0)=qa tau (qad f) v := by
  have hs' := qbY f hf hs
  rw [q6 tau f hs,q6 tau _ hs' _ hv]
  · rw [qmw _ _ (hfs.continuous.integrable_of_hasCompactSupport hf).integrableOn]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    apply setIntegral_congr_fun measurableSet_Ici
    intro t _
    exact (qeY (fun _ h => (hs (subset_tsupport f h)).1) t).symm
  · intro i
    cases i using Fin.lastCases <;> simp [hv]
noncomputable def qci (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (j : ℕ) (t : Fin j → ℝ) : ℝ := f j t+qad (f (j+1)) t
theorem qL.all_properties {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f) (j : ℕ) :
    ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j)⊆qe j tau ∧ qat (f j) := by
  by_cases hj : j≤k
  · exact hf.2.1 j hj
  · rw [hf.2.2 j (by omega)]
    refine ⟨contDiff_const,HasCompactSupport.zero,by simp,?_⟩
    intro e v
    rfl
theorem qdh {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f) :
    qL tau k (qci f) := by
  refine ⟨hf.1,?_,?_⟩
  · intro j _
    obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
    obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
    refine ⟨hjs.add (qfC _ hnc hns),
      hjc.add (qfh _ hnc),?_,?_⟩
    · exact (tsupport_add (f j) (qad (f (j+1)))).trans
        (Set.union_subset hjt (qbY _ hnc hnt))
    · intro e v
      exact congrArg₂ (·+·) (hjy e v) (qi0 _ hny e v)
  · intro j hj
    have h1 := hf.2.2 j hj
    have h2 := hf.2.2 (j+1) (by omega)
    ext t
    simp [qci,h1,h2]
theorem qgM {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f)
    (j : ℕ) (v : Fin j → ℝ) (hv : ∀ i,0≤v i) :
    qa tau (qci f j) v=
      qa tau (f j) v+qa tau (f (j+1)) (Fin.snoc v 0) := by
  obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
  obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
  have hg := (qdh hf).all_properties j
  rw [qhC _ hnc hns hnt v hv,
    q6 tau _ hg.2.2.1 _ hv,q6 tau _ hjt _ hv,
    q6 tau _ (qbY _ hnc hnt) _ hv]
  exact integral_add (hjs.continuous.integrable_of_hasCompactSupport hjc).integrableOn
    ((qfC _ hnc hns).continuous.integrable_of_hasCompactSupport
      (qfh _ hnc)).integrableOn
theorem qmS {n : ℕ} (X M : ℕ) (F G : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    qd X (F+G) M b=qd X F M b+qd X G M b := by
  simp only [qd,qg,Pi.add_apply,mul_add,Finset.sum_add_distrib]
theorem qf9 {tau : ℝ} {k X M a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f)
    (htau : tau<1) (hX : 2≤X) (hM : X<M+a) (hp : Nat.Prime (M+a))
    (j : ℕ) (b : Fin j → ℕ) :
    qd X (qa tau (f j)) M b+
      qd X (qa tau (f (j+1))) M (Fin.snoc b a)=
      qd X (qa tau (qci f j)) M b := by
  have hn := hf.all_properties (j+1)
  rw [qfy hX hM hp _ htau (qaV tau _ hn.2.2.1)]
  rw [←qmS]
  apply qce hX
  intro v hv
  exact (qgM hf j v hv).symm
theorem qiC (X h m : ℕ) :
    qaJ X h m=q8 X (Finset.Ioc 0 h) m := by
  unfold qaJ q8
  congr 1
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(1+c))) h
theorem qcw (hBV : qN) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => qj X (fun m => qaU tau lam k f X m^2*
      q8 X (Finset.Ioc 0 (qb lam X)) m))
      atTop (𝓝 (lam*qcp lam k f)) := by
  apply (qiZ hBV f hf htau htau2 hlam).congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [qcP f hf hX,qiC]
noncomputable def qfp (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (S : Finset (Fin h)) : ℝ :=
  qd X (F S.card) M (fun i => a+(qy ⟨S,rfl⟩ i:ℕ))
theorem qbS {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Set.range (qy S)=(S.val : Set (Fin h)) := by
  ext x
  have hh := Finset.ext_iff.mp (qdw S) x
  simpa only [Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_coe] using hh
theorem qju {X M h a n : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) (hn : S.card=n) (b : Fin n → Fin h)
    (hb : Function.Injective b) (hr : Set.range b=(S:Set (Fin h))) :
    qfp F X M h a S=qd X (F n) M (fun i => a+(b i:ℕ)) := by
  subst n
  obtain ⟨e,he⟩ := qc3 (qy ⟨S,rfl⟩) b hb
    ((qbS ⟨S,rfl⟩).trans hr.symm)
  rw [he]
  exact (qdv hX (F S.card) (hF S.card) e
    (fun i => a+(qy ⟨S,rfl⟩ i:ℕ))).symm
theorem qgo {h : ℕ} (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    Function.Injective (Fin.snoc (qy ⟨S,rfl⟩) c) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hj : qy ⟨S,rfl⟩ j∈S := by
        have hh : qy ⟨S,rfl⟩ j∈Set.range (qy ⟨S,rfl⟩) := ⟨j,rfl⟩
        rwa [qbS] at hh
      exact False.elim (hc (hij.symm ▸ hj))
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hi : qy ⟨S,rfl⟩ i∈S := by
        have hh : qy ⟨S,rfl⟩ i∈Set.range (qy ⟨S,rfl⟩) := ⟨i,rfl⟩
        rwa [qbS] at hh
      exact False.elim (hc (hij ▸ hi))
    | cast j =>
      simp only [Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc ((qy ⟨S,rfl⟩).injective hij)
theorem qh5 {h : ℕ} (S : Finset (Fin h)) (c : Fin h) :
    Set.range (Fin.snoc (qy ⟨S,rfl⟩) c)=↑(insert c S : Finset (Fin h)) := by
  ext x
  simp only [Set.mem_range,Finset.mem_coe,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      right
      simp only [Fin.snoc_castSucc]
      have hh : qy ⟨S,rfl⟩ i∈Set.range (qy ⟨S,rfl⟩) := ⟨i,rfl⟩
      rwa [qbS] at hh
  · rintro (rfl | hx)
    · exact ⟨Fin.last _,by simp⟩
    · have hx' : x∈Set.range (qy ⟨S,rfl⟩) := by rwa [qbS]
      obtain ⟨i,rfl⟩ := hx'
      exact ⟨i.castSucc,by simp⟩
theorem qjv {X M h a : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    qfp F X M h a (insert c S)=
      qd X (F (S.card+1)) M
        (Fin.snoc (fun i => a+(qy ⟨S,rfl⟩ i:ℕ)) (a+(c:ℕ))) := by
  rw [qju hX F hF _ (Finset.card_insert_of_notMem hc)
    _ (qgo S hc) (qh5 S c)]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp
noncomputable def qa8 (tau : ℝ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (B : Finset (Fin h)) : ℝ :=
  ∑ S∈B.powerset,qfp (fun j => qa tau (f j)) X M h a S
theorem qgN {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f)
    (htau : tau<1) (hX : 2≤X) (c : Fin h) (hM : X<M+(a+(c:ℕ)))
    (hp : Nat.Prime (M+(a+(c:ℕ)))) :
    qa8 tau f X M h a Finset.univ=
      qa8 tau (qci f) X M h a (Finset.univ.erase c) := by
  classical
  have hsym : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) →
      qa tau (f j) (v ∘ e)=qa tau (f j) v := by
    intro j
    have hj := hf.all_properties j
    exact qcf _ hj.2.2.1 hj.2.2.2
  have he : (Finset.univ : Finset (Fin h))=insert c (Finset.univ.erase c) := by simp
  unfold qa8
  conv_lhs => rw [he,Finset.sum_powerset_insert (Finset.notMem_erase c Finset.univ),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hc : c∉S := fun h => Finset.notMem_erase c Finset.univ ((Finset.mem_powerset.mp hS) h)
  rw [qjv hX _ hsym S hc]
  exact qf9 hf htau hX hM hp S.card _
theorem qgD {X M h a n : ℕ}
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (S : Finset (Fin h)) (hn : S.card=n) :
    qfp F X M h a S=
      qd X (F n) M (fun i => a+(qy ⟨S,hn⟩ i:ℕ)) := by
  subst n
  rfl
theorem qlK (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),qfp F X M h a S)=
      qbP X h a (F n) M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold qbP
  apply Finset.sum_congr rfl
  intro S _
  exact qgD F S.val S.property
@[simp] theorem qga (tau : ℝ) (n : ℕ) :
    qa tau (0 : (Fin n → ℝ) → ℝ)=0 := by
  ext v
  simp [qa,qbd,convolution_def]
@[simp] theorem qnd (X M : ℕ) {n : ℕ} (b : Fin n → ℕ) :
    qd X (0 : (Fin n → ℝ) → ℝ) M b=0 := by
  simp [qd,qg]
@[simp] theorem ql4 (X h a M n : ℕ) :
    qbP X h a (0 : (Fin n → ℝ) → ℝ) M=0 := by
  simp [qbP]
theorem qeB {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f) (hk : k≤h) :
    qa8 tau f X M h a Finset.univ=
      ∑ j : Fin (k+1),qbP X h a (qa tau (f j)) M := by
  unfold qa8
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,qlK]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => qbP X h a (qa tau (f j)) M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,qga,ql4]
theorem qeT {tau lam : ℝ} {k X M : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f)
    (hk : k≤qb lam X) :
    qaU tau lam k f X M=
      qa8 tau f X M (qb lam X) (qb lam X+1) Finset.univ := by
  exact (qeB hf hk).symm
noncomputable def qaG {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    if S.val⊆B then qd X F m (fun i => a+(qy S i:ℕ)) else 0
noncomputable def qZ {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (A : Setoid (Fin n) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h,A (Setoid.ker b)*
    (if ∀ i,b i∈B then qd X F m (fun i => a+(b i:ℕ)) else 0)
theorem qj1 {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) (e : Equiv.Perm (Fin n)) (B : Finset (Fin h)) :
    (∀ i,(qbu (S,e)).val i∈B) ↔ S.val⊆B := by
  constructor
  · intro hi x hx
    rw [←qdk (S,e)] at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hi i
  · intro hS i
    apply hS
    rw [←qdk (S,e)]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
theorem qh6 {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h))
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    qZ X h a F (qc n) B m=qaG X h a F B m := by
  classical
  unfold qZ
  have he : (∑ b : Fin n → Fin h,qc n (Setoid.ker b)*
      (if ∀ i,b i∈B then qd X F m (fun i => a+(b i:ℕ)) else 0))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*(if ∀ i,b.val i∈B then qd X F m (fun i => a+(b.val i:ℕ)) else 0) := by
    simp only [qc,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective qbu (qfB h n))
    (fun t => (n.factorial:ℝ)⁻¹*(if ∀ i,(qbu t).val i∈B then
      qd X F m (fun i => a+((qbu t).val i:ℕ)) else 0)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold qaG
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      qd X F m (fun i => a+((qbu (S,e)).val i:ℕ))=
      qd X F m (fun i => a+(qy S i:ℕ)) :=
    qdv hX F hsym e (fun i => a+(qy S i:ℕ))
  simp only [hd,qj1,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [←mul_assoc, mul_inv_cancel₀ hn,one_mul]
theorem qiD (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (B : Finset (Fin h)) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),
      if S⊆B then qfp F X M h a S else 0)=
      qaG X h a (F n) B M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold qaG
  apply Finset.sum_congr rfl
  intro S _
  rw [qgD F S.val S.property]
@[simp] theorem qhD (X h a M n : ℕ) (B : Finset (Fin h)) :
    qaG X h a (0 : (Fin n → ℝ) → ℝ) B M=0 := by
  simp [qaG]
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qeu {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f) (hk : k≤h)
    (B : Finset (Fin h)) :
    qa8 tau f X M h a B=
      ∑ j : Fin (k+1),qaG X h a (qa tau (f j)) B M := by
  classical
  unfold qa8
  have he : B.powerset=(Finset.univ.powerset : Finset (Finset (Fin h))).filter (fun S => S⊆B) := by
    ext S
    simp
  rw [he,Finset.sum_filter,Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,qiD]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => qaG X h a (qa tau (f j)) B M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,qga,qhD]
noncomputable def qb6 (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) (c : Fin (qb lam X)) : ℝ :=
  ∑ j : Fin (k+1),qZ X (qb lam X) (qb lam X+1)
    (qa tau (f j)) (qc j) (Finset.univ.erase c) m
theorem qeC {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f)
    (hX : 2≤X) (hk : k≤qb lam X) (c : Fin (qb lam X)) :
    qb6 tau lam k f X m c=
      qa8 tau f X m (qb lam X) (qb lam X+1) (Finset.univ.erase c) := by
  rw [qeu hf hk]
  unfold qb6
  apply Finset.sum_congr rfl
  intro j _
  have hj := hf.all_properties j
  exact qh6 hX _ _ (qcf _ hj.2.2.1 hj.2.2.2)
theorem qh7 {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : qL tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤qb lam X) (hm : X < m)
    (c : Fin (qb lam X)) (hp : Nat.Prime (m+(qb lam X+1+(c:ℕ)))) :
    qaU tau lam k f X m=qb6 tau lam k (qci f) X m c := by
  rw [qeT hf hk,
    qeC (qdh hf) hX hk]
  exact qgN hf htau hX c (by omega) hp
theorem qlk {s h : ℕ} (a : ℤ) (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈qh (s:=s) (h:=h) (fun _ => a),∑ c : Fin h,
       if ∀ j,u j≠c then F (Fin.snoc u c) else 0)=
      ∑ v∈qh (s:=s+1) (h:=h) (fun _ => a),F v := by
  classical
  simp only [qh,Finset.sum_filter,qdp]
  have he (u : Fin s → Fin h) :
      (if Function.Injective u then ∑ c : Fin h,if ∀ j,u j≠c then F (Fin.snoc u c) else 0 else 0)=
        ∑ c : Fin h,if Function.Injective u ∧ c∉Set.range u then F (Fin.snoc u c) else 0 := by
    by_cases hu : Function.Injective u <;> simp [hu,Set.mem_range]
  simp only [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t : Fin h × (Fin s → Fin h),
        if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (s+1) => Fin h))
      intro t
      change (if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0)=
        (if Function.Injective (Fin.snoc t.2 t.1) then F (Fin.snoc t.2 t.1) else 0)
      exact if_congr Fin.snoc_injective_iff.symm rfl rfl
theorem qkq {n h : ℕ} (r : Setoid (Fin n)) (a : ℕ)
    (b : {b // b∈qY (α:=Fin h) r}) (c : Fin h) :
    (∀ i,b.val i≠c) ↔ ∀ j,(qa0 r h a b).val j≠c := by
  constructor
  · intro hb j
    obtain ⟨i,hi⟩ := (qbK r) j
    have he := congrFun (qbk r h a b) i
    simp only [qA,hi] at he
    have hv : (qa0 r h a b).val j=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb i
  · intro hb i
    have he := congrFun (qbk r h a b) i
    simp only [qA] at he
    have hv : (qa0 r h a b).val (qaC r i)=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb (qaC r i)
theorem qfi {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈qY (α:=Fin h) r,∑ c : Fin h,if ∀ i,b i≠c then
      (qj X (fun m => qd X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
      else 0)=
    ∑ v∈qh (s:=Fintype.card (Quotient r)+1) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      (qj X (fun m => qd X F m
        (qA (qaC r) (fun _ => h+1) (fun j => v j.castSucc))*
        theta (m+(h+1+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←qlk]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (qa0 r h ((h+1:ℕ):ℤ))
  intro b
  rw [qbk r h (h+1) b]
  apply Finset.sum_congr rfl
  intro c _
  simp only [←qkq r (h+1) b c]
theorem qgO (hBV : qN) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈qY (α:=Fin (qb lam X)) r,∑ c : Fin (qb lam X),
      if ∀ i,b i≠c then (qj X (fun m => qd X F m (fun i => qb lam X+1+(b i:ℕ))*
        theta (m+(qb lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*qE
        (qq (qf (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (qJ (fun i => (qp r i:ℤ))))) := by
  have ha : ∀ᶠ X : ℕ in atTop,∀ _j : Fin (Fintype.card (Quotient r)+1),
      qb lam X+1≤2*qb lam X := by
    filter_upwards [qcA hlam] with X hX j
    exact hX
  have hh := qfe hBV hlam (qaC r) (qbK r)
    (fun X _ => qb lam X+1) ha F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (qfi r _ X F).symm
noncomputable def qah (X h : ℕ) (H : ℕ → Fin h → ℝ) : ℝ :=
  qj X (fun m => ∑ c : Fin h,H m c*theta (m+(h+1+(c:ℕ)))/Real.log X)
theorem qgp {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (qah X h (fun m c => qZ X h (h+1) F k (Finset.univ.erase c) m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,if ∀ i,b i≠c then
        (qj X (fun m => qd X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
        else 0 := by
  classical
  unfold qah qZ
  simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.sum_mul,Finset.sum_div,
    qaF,Complex.ofReal_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hb : ∀ i,b i≠c
  · simp only [if_pos hb]
    simp only [←mul_div_assoc,qmy]
    simp only [mul_assoc,qbx,Complex.ofReal_div,Complex.ofReal_mul]
  · simp only [if_neg hb,mul_zero,zero_mul,zero_div]
    simp [qj]
theorem qh8 (hBV : qN) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : qV F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (qah X (qb lam X) (fun m c =>
      qZ X (qb lam X) (qb lam X+1) F k (Finset.univ.erase c) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*qE
        (qq (qf (Fin n))
          (fun v => (F v.ofLp:ℂ)) (qaw F hF) (qaE F hFs))
        (qbj r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (qgO hBV hlam r F rho hrho hrhohalf hbudget
      (qaw F hF) (qaE F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [qgp]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈qY (α:=Fin (qb lam X)) r,
        ∑ c : Fin (qb lam X),if ∀ i,b i≠c then
        (qj X (fun m => qd X F m (fun i => qb lam X+1+(b i:ℕ))*
          theta (m+(qb lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) =
        ∑ r : Setoid (Fin n),∑ b∈qY (α:=Fin (qb lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (qb lam X),if ∀ i,b i≠c then
            (qj X (fun m => qd X F m (fun i => qb lam X+1+(b i:ℕ))*
              theta (m+(qb lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(qcv r b).mp hb]
      _ = _ := qhh _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)
theorem ql5 {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    qZ X h a F k B m*qZ X h a G l B m=
      qZ X h a (qi F G) (ql k l) B m := by
  classical
  unfold qZ
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [ql,qhi,qgn]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,qfL]
  have hc : (∀ i,Fin.append bc.1 bc.2 i∈B) ↔ (∀ i,bc.1 i∈B) ∧ (∀ j,bc.2 j∈B) := by
    simp only [Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  simp only [hc]
  split_ifs <;> simp_all
  all_goals ring
theorem qhE {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (B : Finset (Fin h))
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    qZ X h a F k B m=qZ X h a G k B m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [qce hX m _ F G hFG]
theorem qhn {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆qe n tau) (hg : tsupport g⊆qe p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    qZ X h a (qa tau f) k B m*
      qZ X h a (qa tau g) l B m=
    qZ X h a (qa (tau+tau) (qi f g)) (ql k l) B m := by
  rw [ql5]
  apply qhE hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,qa6]
  exact (qdf f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm
theorem qlL {X h : ℕ} {H G : ℕ → Fin h → ℝ}
    (he : ∀ m c,H m c=G m c) : qah X h H=qah X h G := by
  unfold qah
  congr 1
  funext m
  exact Finset.sum_congr rfl fun c _ => by rw [he]
theorem qjw {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → Fin h → ℝ) :
    qah X h (fun m c => ∑ i∈S,H i m c)=∑ i∈S,qah X h (H i) := by
  unfold qah
  simp only [Finset.sum_mul,Finset.sum_div,qaF]
  rw [Finset.sum_comm]
theorem qdi (hBV : qN) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau) :
    Tendsto (fun X : ℕ => (qah X (qb lam X) (fun m c =>
      qZ X (qb lam X) (qb lam X+1) (qa tau f) (qc n) (Finset.univ.erase c) m*
      qZ X (qb lam X) (qb lam X+1) (qa tau g) (qc p) (Finset.univ.erase c) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))) := by
  have hh := qh8 hBV hlam
    (qa (tau+tau) (qi f g)) (tau+tau) (by positivity) (by linarith)
    (qaV _ _ (qU f g hsf hsg))
    (qac _ _ (qn f g hf hg))
    (qak _ _ (qn f g hf hg) (qs f g hfs hgs))
    (ql (qc n) (qc p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*qP (tau+tau) (qi f g)
          (qn f g hf hg) (qs f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  apply congrArg (fun z : ℝ => (z:ℂ))
  symm
  apply qlL
  intro m c
  exact qhn hX _ _ m f g hsf hsg _ _ _
theorem qfO (hBV : qN) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆qe n tau) (hsym : qat f) :
    Tendsto (fun X : ℕ => qah X (qb lam X) (fun m c =>
      qZ X (qb lam X) (qb lam X+1) (qa tau f) (qc n) (Finset.univ.erase c) m^2))
      atTop (𝓝 (lam*qcI lam n*q7 f)) := by
  have hh := qdi hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [qdM lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'
theorem qgb (hBV : qN) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau) :
    Tendsto (fun X : ℕ => qah X (qb lam X) (fun m c =>
      qZ X (qb lam X) (qb lam X+1) (qa tau f) (qc n) (Finset.univ.erase c) m*
      qZ X (qb lam X) (qb lam X+1) (qa tau g) (qc p) (Finset.univ.erase c) m))
      atTop (𝓝 0) := by
  have hh := qdi hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [qd1 hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh
theorem qhF (hBV : qN) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => qah X (qb lam X) (fun m c => qb6 tau lam k f X m c^2))
      atTop (𝓝 (lam*qcp lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m (c : Fin (qb lam X)) =>
    qZ X (qb lam X) (qb lam X+1)
      (qa tau (f j)) (qc j) (Finset.univ.erase c) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => qah X (qb lam X) (fun m c => H i X m c*H j X m c)) atTop
        (𝓝 (if i=j then lam*qcI lam i*q7 (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using qfO hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [if_neg hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact qgb hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : qah X (qb lam X) (fun m c => qb6 tau lam k f X m c^2)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),qah X (qb lam X) (fun m c => H i X m c*H j X m c) := by
    simp only [qb6,pow_two,Finset.sum_mul,Finset.mul_sum,qjw]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*qcI lam i*q7 (f i))=lam*qcp lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => qcI lam j*q7 (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)
theorem qmY (X h m : ℕ) :
    q8 X (Finset.Ioc h (2*h)) m=
      (∑ c : Fin h,theta (m+(h+1+(c:ℕ))))/Real.log X := by
  unfold q8
  congr 1
  have he : Finset.Ioc h (2*h)=Finset.Ico (h+1) (h+1+h) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  symm
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(h+1+c))) h
theorem qev {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤qb lam X) :
    qj X (fun m => qaU tau lam k f X m^2*
      q8 X (Finset.Ioc (qb lam X) (2*qb lam X)) m)=
      qah X (qb lam X) (fun m c => qb6 tau lam k (qci f) X m c^2) := by
  classical
  unfold qah qj
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [qmY,←mul_div_assoc,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : Nat.Prime (m+(qb lam X+1+(c:ℕ)))
  · rw [qh7 hf htau hX hk (Finset.mem_Ioc.mp hm).1 c hp]
  · simp [theta,hp]
theorem qeU (hBV : qN) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => qj X (fun m => qaU tau lam k f X m^2*
      q8 X (Finset.Ioc (qb lam X) (2*qb lam X)) m))
      atTop (𝓝 (qmm lam k f)) := by
  have hh := qhF hBV (qci f) (qdh hf)
    htau htau2 hlam
  change Tendsto _ _ (𝓝 (qmm lam k f)) at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,(qbV hlam).eventually_ge_atTop k] with X hX hk
  exact (qev f hf (by linarith) hX hk).symm
theorem qdO {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ qe n tau) (hsym : ∀ y, f (y ∘ e)=f y)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (qa (tau+tau) (qi f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (qa (tau+tau) (qi f f) v.ofLp:ℂ))) :
    qE (qq (qf (Fin (n+n)))
      (fun v => (qa (tau+tau) (qi f f) v.ofLp:ℂ)) hF hFs)
      (qx (qo e) Finset.univ) = (q7 f:ℂ) := by
  rw [qfA]
  have he : (∫ y, qI (q3 (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (qa (tau+tau) (qi f f) v.ofLp:ℂ)) (qaQ (qb9 e) y)
      ∂qD (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂qD (Fin n) := by
    apply integral_congr_ae
    rw [qaO]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [qcl (tau+tau) (qi f f)
      (qn f f hf hf) (qs f f hfs hfs)
      (qU f f hsupp hsupp)]
    · rw [qdG,qa6,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [qdG]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,qaO]
  congr 1
  unfold q7
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]
theorem qlQ {n d : ℕ} (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ) :
    q7 (qi f g)=q7 f*q7 g := by
  unfold q7
  rw [←(qcg n d).integral_comp
    (qbD n d).measurableEmbedding]
  simp only [qec,qa6,mul_pow]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => f x^2) (fun y => g y^2)
noncomputable def qb1 {n : ℕ} (e : Equiv.Perm (Fin n)) (d : ℕ) : Equiv.Perm (Fin (n+d)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin d))).trans finSumFinEquiv)
@[simp] theorem qkz {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    qb1 e d (i.castAdd d)=(e i).castAdd d := by
  simp [qb1]
@[simp] theorem qj2 {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin d) :
    qb1 e d (i.natAdd n)=i.natAdd n := by
  simp [qb1]
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qj3 {n d : ℕ} (e : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ)
    (hf : ∀ y,f (y ∘ e)=f y) (v : Fin (n+d) → ℝ) :
    qi f g (v ∘ qb1 e d)=qi f g v := by
  simp only [qi,Function.comp_apply,qkz,qj2]
  congr 1
  exact hf (fun i => v (i.castAdd d))
noncomputable def qbv {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ) :
    Fin (n+d) → α ⊕ Fin d := Fin.append (Sum.inl ∘ a) Sum.inr
@[simp] theorem qfP {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin n) :
    qbv a d (i.castAdd d)=Sum.inl (a i) := by simp [qbv]
@[simp] theorem qfj {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin d) :
    qbv a d (i.natAdd n)=Sum.inr i := by simp [qbv]
theorem qgc {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ)
    (ha : Function.Injective a) : Function.Injective (qbv a d) := by
  intro i j h
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp only [qfP,qfj,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  · exact congrArg (Fin.castAdd d) (ha h)
  · exact congrArg (Fin.natAdd n) h
theorem qll {n p : ℕ} {α : Type*} (a : Fin n → α) (b : Fin p → α)
    (d : ℕ) (hab : Set.range a≠Set.range b) :
    Set.range (qbv a d)≠Set.range (qbv b d) := by
  intro he
  apply hab
  ext x
  have hh : ∀ {n : ℕ} (a : Fin n → α), Sum.inl x∈Set.range (qbv a d) ↔ x∈Set.range a := by
    intro n a
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.addCases with
      | left i => exact ⟨i,by simpa using hi⟩
      | right i => simp at hi
    · rintro ⟨i,rfl⟩; exact ⟨i.castAdd d,by simp⟩
  rw [←hh a,←hh b,he]
noncomputable def qbn {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → ℕ ⊕ Fin d :=
  Fin.append (qbv (fun i : Fin n => qp r (i.castAdd p)) d)
    (qbv (fun i : Fin p => qp r (i.natAdd n)) d)
noncomputable def qbz {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Finset (Finset (Fin ((n+d)+(p+d)))) := by
  classical
  exact qx (qbn r d) (Finset.univ.image (qbn r d))
theorem qfQ {n d : ℕ} (i : Fin n) (j : Fin d) : i.castAdd d≠j.natAdd n := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega
theorem qi3 {n d : ℕ} (i : Fin d) (j : Fin n) : i.natAdd n≠j.castAdd d :=
  (qfQ j i).symm
theorem qkr {n d : ℕ} (e : Equiv.Perm (Fin n)) :
    qbz (n:=n) (p:=n) (qF e) d=
      qx (qo (qb1 e d)) Finset.univ := by
  classical
  have he := qfc (qbn (n:=n) (p:=n) (qF e) d)
    (qo (qb1 e d))
  have hh : ∀ i j, qbn (n:=n) (p:=n) (qF e) d i=qbn (n:=n) (p:=n) (qF e) d j ↔
      qo (qb1 e d) i=qo (qb1 e d) j := by
    intro i j
    have hr (i j : Fin (n+n)) : qp (qF e) i=qp (qF e) j ↔
        qo e i=qo e j := by
      change (Setoid.ker (qp (qF e))) i j ↔ _
      rw [qcG]
      rfl
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [qbn,Fin.append_left,Fin.append_right,qo] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [qfP,qfj,qkz,qj2,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        hr,qo,Fin.append_left,Fin.append_right,Function.id_def,Equiv.apply_eq_iff_eq,
        qfQ,qi3]
  have he' : qbz (qF e) d=
      qx (qo (qb1 e d))
        (Finset.univ.image (qo (qb1 e d))) := by
    ext S
    simpa only [qbz,qH] using Finset.ext_iff.mp (he hh) S
  rw [he']
  congr 1
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
  exact ⟨i.castAdd (n+d),by simp [qo]⟩
noncomputable def qbL {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ) :
    (Fin ((n+d)+(p+d)) → ℝ) → ℝ := qi (qi f w) (qi g w)
theorem qaW {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w) :
    HasCompactSupport (qbL f g w) :=
  qn _ _ (qn f w hf hw) (qn g w hg hw)
theorem qcn {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (qbL f g w) :=
  qs _ _ (qs f w hf hw) (qs g w hg hw)
noncomputable def qa9 {n p d : ℕ} (tau sigma : ℝ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (r : Setoid (Fin (n+p))) : ℂ :=
  qE (qq (qf (Fin ((n+d)+(p+d))))
    (fun v => (qa ((tau+sigma)+(tau+sigma)) (qbL f g w) v.ofLp:ℂ))
    (qaw _ (qac _ _ (qaW f g w hf hg hw)))
    (qaE _ (qak _ _
      (qaW f g w hf hg hw) (qcn f g w hfs hgs hws))))
      (qbz r d)
theorem qeL {n p d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau)
    (hsw : tsupport w⊆qe d sigma)
    (r : Setoid (Fin (n+p)))
    (hl : Setoid.comap (Fin.castAdd p) r=⊥) (hr : Setoid.comap (Fin.natAdd n) r=⊥)
    (hne : Set.range (fun i : Fin n => qp r (i.castAdd p))≠
      Set.range (fun i : Fin p => qp r (i.natAdd n))) :
    qa9 tau sigma f g w hf hg hw hfs hgs hws r=0 := by
  unfold qa9
  convert qch (qi f w) (qi g w)
    (qn f w hf hw) (qn g w hg hw)
    (qs f w hfs hws) (qs g w hgs hws)
    (qU f w hsf hsw) (qU g w hsg hsw)
    (qbv _ d) (qbv _ d)
    (qgc _ d (qbb r hl))
    (qgc _ d (qa7 r hr))
    (qll _ _ d hne)
    (qaw _ (qac _ _ (qaW f g w hf hg hw)))
    (qaE _ (qak _ _ (qaW f g w hf hg hw)
      (qcn f g w hfs hgs hws))) using 1
  congr 2
  ext x
  simp only [qbz,qbn,qH]
theorem qks {n d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆qe n tau) (hsw : tsupport w⊆qe d sigma)
    (hsym : qat f) (e : Equiv.Perm (Fin n)) :
    qa9 tau sigma f f w hf hf hw hfs hfs hws (qF e)=
      (q7 f*q7 w:ℂ) := by
  unfold qa9
  rw [qkr]
  have hh := qdO (qb1 e d) (qi f w)
    (qn f w hf hw) (qs f w hfs hws)
    (qU f w hsf hsw) (qj3 e f w (fun y => hsym e y))
    (qaw _ (qac _ _ (qaW f f w hf hf hw)))
    (qaE _ (qak _ _ (qaW f f w hf hf hw)
      (qcn f f w hfs hfs hws)))
  rw [qlQ,Complex.ofReal_mul] at hh
  convert hh using 1
  rfl
noncomputable def qal (s d h : ℕ) : Fin (s+d) → ℕ :=
  Fin.append (fun _ => h+1) (fun _ => 1)
theorem qmk {s d h : ℕ} (u : Fin s → Fin h) (v : Fin d → Fin h) :
    Fin.append u v∈qh (fun j => (qal s d h j:ℤ)) ↔
      u∈qh (fun _ => ((h+1:ℕ):ℤ)) ∧ v∈qh (fun _ => (1:ℤ)) := by
  classical
  simp only [qh,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu
    constructor
    · intro i j hij
      have he : qt (fun k => (qal s d h k:ℤ)) (Fin.append u v) (i.castAdd d)=
          qt (fun k => (qal s d h k:ℤ)) (Fin.append u v) (j.castAdd d) := by
        simpa [qt,qal] using hij
      exact Fin.castAdd_inj.mp (hu he)
    · intro i j hij
      have he : qt (fun k => (qal s d h k:ℤ)) (Fin.append u v) (i.natAdd s)=
          qt (fun k => (qal s d h k:ℤ)) (Fin.append u v) (j.natAdd s) := by
        simpa [qt,qal] using hij
      have he' := congrArg Fin.val (hu he)
      simp only [Fin.val_natAdd] at he'
      exact Fin.ext (Nat.add_left_cancel he')
  · rintro ⟨hu,hv⟩ i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        congr 1
        apply hu
        simpa [qt,qal] using hij
      | right j =>
        have hi := (u i).isLt
        have hj := (v j).isLt
        simp only [qt,qal,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have hi := (v i).isLt
        have hj := (u j).isLt
        simp only [qt,qal,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
      | right j =>
        congr 1
        apply hv
        simpa [qt,qal] using hij
noncomputable def qmZ (s d h : ℕ) :
    ({u // u∈qh (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈qh (s:=d) (h:=h) (fun _ => (1:ℤ))}) ≃
    {u // u∈qh (s:=s+d) (h:=h) (fun j => (qal s d h j:ℤ))} where
  toFun t := ⟨Fin.append t.1.1 t.2.1,(qmk t.1.1 t.2.1).mpr ⟨t.1.2,t.2.2⟩⟩
  invFun v := by
    let v1 := fun i : Fin s => v.1 (i.castAdd d)
    let v2 := fun i : Fin d => v.1 (i.natAdd s)
    have he : Fin.append v1 v2=v.1 := by
      funext i
      cases i using Fin.addCases <;> simp [v1,v2]
    have hv : v1∈qh (fun _ => ((h+1:ℕ):ℤ)) ∧ v2∈qh (fun _ => (1:ℤ)) :=
      (qmk v1 v2).mp (he.symm ▸ v.2)
    exact (⟨v1,hv.1⟩,⟨v2,hv.2⟩)
  left_inv t := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i using Fin.addCases <;> simp
theorem qmE {s d h : ℕ} {K : Type*} [AddCommMonoid K]
    (F : (Fin (s+d) → Fin h) → K) :
    (∑ u∈qh (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      ∑ v∈qh (s:=d) (h:=h) (fun _ => (1:ℤ)),F (Fin.append u v))=
      ∑ w∈qh (s:=s+d) (h:=h) (fun j => (qal s d h j:ℤ)),F w := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]; arg 2; ext u; rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  calc
    _ = ∑ t : {u // u∈qh (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈qh (s:=d) (h:=h) (fun _ => (1:ℤ))},F (Fin.append t.1.val t.2.val) :=
        (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (qmZ s d h) _ _ (fun _ => rfl)
theorem qkt {lam : ℝ} (hlam : 0<lam) (s d : ℕ) :
    ∀ᶠ X : ℕ in atTop,∀ j,qal s d (qb lam X) j≤2*qb lam X := by
  filter_upwards [qcA hlam] with X hX j
  cases j using Fin.addCases with
  | left j => simpa only [qal,Fin.append_left] using hX
  | right j => simp only [qal,Fin.append_right]; omega
noncomputable def qa3 {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → Fin (Fintype.card (Quotient r)+d) :=
  Fin.append
    (Fin.append (fun i : Fin n => (qaC r (i.castAdd p)).castAdd d) (Fin.natAdd _))
    (Fin.append (fun i : Fin p => (qaC r (i.natAdd n)).castAdd d) (Fin.natAdd _))
theorem qjx {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Function.Surjective (qa3 r d) := by
  intro i
  cases i using Fin.addCases with
  | left i =>
    obtain ⟨j,hj⟩ := qbK r i
    cases j using Fin.addCases with
    | left j => exact ⟨(j.castAdd d).castAdd (p+d),by simp [qa3,hj]⟩
    | right j => exact ⟨(j.castAdd d).natAdd (n+d),by simp [qa3,hj]⟩
  | right i => exact ⟨(i.natAdd n).castAdd (p+d),by simp [qa3]⟩
noncomputable def qbZ {n p d h : ℕ} (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    Fin ((n+d)+(p+d)) → ℕ :=
  Fin.append
    (Fin.append (fun i : Fin n => h+1+(b (i.castAdd p):ℕ)) (fun i => 1+(c i:ℕ)))
    (Fin.append (fun i : Fin p => h+1+(b (i.natAdd n):ℕ)) (fun i => 1+(c i:ℕ)))
theorem qmx {n p d h : ℕ} (r : Setoid (Fin (n+p)))
    (b : {b // b∈qY (α:=Fin h) r}) (c : Fin d → Fin h) :
    qA (qa3 r d) (qal _ d h)
      (Fin.append (qa0 r h (h+1) b).val c)=qbZ b.val c := by
  funext i
  have hb := qbk r h (h+1) b
  cases i using Fin.addCases <;> rename_i i <;> cases i using Fin.addCases <;>
    simp only [qa3,qbZ,Fin.append_left,Fin.append_right,qA,
      qal,Fin.append_left,Fin.append_right]
  · exact congrFun hb _
  · exact congrFun hb _
theorem qj4 {n p d h X : ℕ} (r : Setoid (Fin (n+p)))
    (F : (Fin ((n+d)+(p+d)) → ℝ) → ℝ) :
    (∑ b∈qY (α:=Fin h) r,∑ c∈qh (s:=d) (h:=h) (fun _ => (1:ℤ)),
      (qj X (fun m => qd X F m (qbZ b c)):ℂ))=
    ∑ v∈qh (s:=Fintype.card (Quotient r)+d) (h:=h)
      (fun j => (qal _ d h j:ℤ)),
      (qj X (fun m => qd X F m (qA (qa3 r d)
        (qal _ d h) v)):ℂ) := by
  classical
  rw [←qmE]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (qa0 r h ((h+1:ℕ):ℤ))
  intro b
  apply Finset.sum_congr rfl
  intro c _
  have he := qmx r b c
  convert congrArg (fun sh => (qj X (fun m => qd X F m sh):ℂ)) he.symm using 1
  norm_cast
theorem qj5 {n d : ℕ} {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆qe n tau) (hsym : qat f)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆qe d sigma) :
    (∑ r : Setoid (Fin (n+n)),
      (ql (qc n) (qc n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qa9 tau sigma f f w hf hf hw hfs hfs hws r))=
      (qcI lam n*q7 f*q7 w:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (ql (qc n) (qc n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qa9 tau sigma f f w hf hf hw hfs hfs hws r)
  have hz : ∀ r,r∉Set.range (@qF n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => qp r (i.castAdd n))≠
            Set.range (fun i : Fin n => qp r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := qhP r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,qeL f f w hf hf hw hfs hfs hws hsf hsf hsw r hl hr' hne,mul_zero]
      · simp only [A,ql,qc,if_neg hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,ql,qc,if_neg hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (qF e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*((q7 f:ℂ)*(q7 w:ℂ))) := by
    intro e
    simp only [A,ql,qhO,qhk,qc,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      qd0,qks f w hf hw hfs hws hsf hsw hsym e,Complex.ofReal_mul,pow_two]
  have hh := qhl _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [qcI,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp
theorem qku {m n d : ℕ} (hmn : m≠n) {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe m tau) (hsg : tsupport g⊆qe n tau)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆qe d sigma) :
    (∑ r : Setoid (Fin (m+n)),
      (ql (qc m) (qc n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qa9 tau sigma f g w hf hg hw hfs hgs hws r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => qp r (i.castAdd n))≠
          Set.range (fun i : Fin n => qp r (i.natAdd m)) := by
        intro he
        exact hmn (qgC _ _ (qbb r hl)
          (qa7 r hr) he)
      rw [qeL f g w hf hg hw hfs hgs hws hsf hsg hsw r hl hr hne,mul_zero,mul_zero]
    · simp only [ql,qc,if_neg hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [ql,qc,if_neg hl,zero_mul,Complex.ofReal_zero]
theorem qlm {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    qJ (fun i => ((qa3 r d i).val:ℤ))=qbz r d := by
  classical
  have he : ∀ i j, (qa3 r d i).val=(qa3 r d j).val ↔
      qbn r d i=qbn r d j := by
    intro i j
    rw [Fin.val_inj]
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [qbn,qa3,Fin.append_left,Fin.append_right] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [Fin.append_left,Fin.append_right,qfP,qfj,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        qfQ,qi3,qp,qaC,Fin.val_inj]
  ext S
  simp only [qJ,qbz,qH,Int.natCast_inj,he]
theorem ql6 {n p d : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+p)))
    (F : (Fin ((n+(d+1))+(p+(d+1))) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈qY (α:=Fin (qb lam X)) r,
      ∑ c∈qh (s:=d+1) (h:=qb lam X) (fun _ => (1:ℤ)),
        (qj X (fun m => qd X F m (qbZ b c)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*qE
        (qq (qf (Fin ((n+(d+1))+(p+(d+1)))))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (qbz r (d+1)))) := by
  have hh := qes hlam (qa3 r (d+1))
    (qjx r (d+1)) (fun X => qal _ (d+1) (qb lam X))
    (qkt hlam _ (d+1)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  convert hh using 1
  · funext X
    exact qj4 r F
  · congr 3
    exact (qlm (n:=n) (p:=p) r (d+1)).symm
noncomputable def qaP {d : ℕ} (X h : ℕ) (H : ℕ → ℝ)
    (W : (Fin d → ℝ) → ℝ) : ℝ :=
  qj X (fun m => ∑ c∈qh (s:=d) (h:=h) (fun _ => (1:ℤ)),
    H m * qd X W m (fun i => 1+(c i:ℕ))^2)
theorem qkv {d : ℕ} {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → ℝ) (W : (Fin d → ℝ) → ℝ) :
    qaP X h (fun m => ∑ i∈S,H i m) W=∑ i∈S,qaP X h (H i) W := by
  unfold qaP
  simp only [Finset.sum_mul,qaF]
  rw [Finset.sum_comm]
theorem qln {n p d X h : ℕ} {tau sigma : ℝ} (hX : 2≤X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau)
    (hsw : tsupport w⊆qe d sigma)
    (M : ℕ) (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    qd X (qa ((tau+sigma)+(tau+sigma)) (qbL f g w)) M (qbZ b c)=
      qd X (qa tau f) M (fun i => h+1+(b (i.castAdd p):ℕ))*
      qd X (qa tau g) M (fun i => h+1+(b (i.natAdd n):ℕ))*
      qd X (qa sigma w) M (fun i => 1+(c i:ℕ))^2 := by
  unfold qbL qbZ
  rw [qbO _ _ (qU f w hsf hsw)
    (qU g w hsg hsw) hX,
    qbO f w hsf hsw hX,
    qbO g w hsg hsw hX]
  ring
theorem qlo {n p d X : ℕ} {tau sigma : ℝ} (hX : 2≤X) (h : ℕ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau)
    (hsw : tsupport w⊆qe d sigma)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    (qaP X h (fun m => qu X h (h+1) (qa tau f) k m*
      qu X h (h+1) (qa tau g) l m) (qa sigma w):ℂ)=
      ∑ b : Fin (n+p) → Fin h,(ql k l (Setoid.ker b):ℂ)*
        ∑ c∈qh (s:=d) (h:=h) (fun _ => (1:ℤ)),
        (qj X (fun m => qd X (qa ((tau+sigma)+(tau+sigma))
          (qbL f g w)) m (qbZ b c)):ℂ) := by
  have he (m : ℕ) (c : Fin d → Fin h) :
      qu X h (h+1) (qa tau f) k m*
      qu X h (h+1) (qa tau g) l m*
      qd X (qa sigma w) m (fun i => 1+(c i:ℕ))^2=
      ∑ b : Fin (n+p) → Fin h,ql k l (Setoid.ker b)*
        qd X (qa ((tau+sigma)+(tau+sigma)) (qbL f g w)) m (qbZ b c) := by
    simp only [qu,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm,←Finset.sum_product']
    apply Finset.sum_equiv (Fin.appendEquiv n p)
    · intro bc; simp
    intro bc _
    rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl,
      qln hX f g w hsf hsg hsw]
    simp only [ql,qhi,qgn,Fin.append_left,Fin.append_right]
    ring
  unfold qaP
  simp only [he,qaF,qbx,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
theorem ql7 {n p d : ℕ} {lam : ℝ} (hlam : 0<lam)
    (F : (Fin ((n+(d+1))+(p+(d+1))) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : qV F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+p)) → ℝ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+p) → Fin (qb lam X),(k (Setoid.ker b):ℂ)*
      ∑ c∈qh (s:=d+1) (h:=qb lam X) (fun _ => (1:ℤ)),
        (qj X (fun m => qd X F m (qbZ b c)):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+p)),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*qE
        (qq (qf (Fin ((n+(d+1))+(p+(d+1)))))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (qbz r (d+1))))) := by
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (ql6 hlam r F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+p)),(k r:ℂ)*∑ b∈qY (α:=Fin (qb lam X)) r,
        ∑ c∈qh (s:=d+1) (h:=qb lam X) (fun _ => (1:ℤ)),
          (qj X (fun m => qd X F m (qbZ b c)):ℂ)) =
        ∑ r : Setoid (Fin (n+p)),∑ b∈qY (α:=Fin (qb lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c∈qh (s:=d+1) (h:=qb lam X) (fun _ => (1:ℤ)),
          (qj X (fun m => qd X F m (qbZ b c)):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(qcv r b).mp hb]
      _ = _ := qhh _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem qee {n p d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆qe (d+1) sigma) :
    Tendsto (fun X : ℕ => (qaP X (qb lam X) (fun m =>
      qu X (qb lam X) (qb lam X+1) (qa tau f) (qc n) m*
      qu X (qb lam X) (qb lam X+1) (qa tau g) (qc p) m)
      (qa sigma w):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
        (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qa9 tau sigma f g w hf hg hw hfs hgs hws r))) := by
  let P := qbL f g w
  have hPc : HasCompactSupport P := qaW f g w hf hg hw
  have hPs : ContDiff ℝ ∞ P := qcn f g w hfs hgs hws
  have hPb : tsupport P⊆qe _ ((tau+sigma)+(tau+sigma)) :=
    qU _ _ (qU f w hsf hsw) (qU g w hsg hsw)
  let F := qa ((tau+sigma)+(tau+sigma)) P
  have hFc := qac ((tau+sigma)+(tau+sigma)) P hPc
  have hFs := qak ((tau+sigma)+(tau+sigma)) P hPc hPs
  obtain ⟨M,hMb⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  have hh := ql7 (n:=n) (p:=p) (d:=d) hlam F ((tau+sigma)+(tau+sigma))
    (by positivity) (by linarith) (qaV _ P hPb)
    (qaw F hFc) (qaE F hFs)
    (max 0 M) (le_max_left _ _) (fun v _ => by simpa only [Real.norm_eq_abs] using (hMb v).trans (le_max_right 0 M))
    (ql (qc n) (qc p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*qa9 tau sigma f g w hf hg hw hfs hgs hws r)) =
      (lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*qa9 tau sigma f g w hf hg hw hfs hgs hws r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_add]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (ql (qc n) (qc p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*qa9 tau sigma f g w hf hg hw hfs hgs hws r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (qlo hX _ f g w hsf hsg hsw _ _).symm
theorem qhG {n d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆qe n tau) (hsym : qat f)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆qe (d+1) sigma) :
    Tendsto (fun X : ℕ => qaP X (qb lam X) (fun m =>
      qu X (qb lam X) (qb lam X+1) (qa tau f) (qc n) m^2)
      (qa sigma w)) atTop
      (𝓝 (lam^(d+1)*qcI lam n*q7 f*q7 w)) := by
  have hh := qee htau hsigma hbudget hlam f f hf hf hfs hfs hsf hsf w hw hws hsw
  rw [qj5 lam f hf hfs hsf hsym w hw hws hsw] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,←Complex.ofReal_pow,Complex.mul_re,←pow_two,mul_assoc] using hh'
theorem qh9 {n p d : ℕ} (hnp : n≠p) {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆qe n tau) (hsg : tsupport g⊆qe p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆qe (d+1) sigma) :
    Tendsto (fun X : ℕ => qaP X (qb lam X) (fun m =>
      qu X (qb lam X) (qb lam X+1) (qa tau f) (qc n) m*
      qu X (qb lam X) (qb lam X+1) (qa tau g) (qc p) m)
      (qa sigma w)) atTop (𝓝 0) := by
  have hh := qee htau hsigma hbudget hlam f g hf hg hfs hgs hsf hsg w hw hws hsw
  rw [qku hnp lam f g hf hg hfs hgs hsf hsg w hw hws hsw,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh
theorem qjy {tau sigma lam : ℝ} {k d : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆qe (d+1) sigma) :
    Tendsto (fun X : ℕ => qaP X (qb lam X) (fun m => qb0 tau lam k f X m^2)
      (qa sigma w)) atTop (𝓝 (lam^(d+1)*q7 w*qcp lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => qu X (qb lam X) (qb lam X+1)
       (qa tau (f j)) (qc j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => qaP X (qb lam X) (fun m => H i X m*H j X m)
        (qa sigma w)) atTop
        (𝓝 (if i=j then lam^(d+1)*qcI lam i*q7 (f i)*q7 w else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using qhG htau hsigma hbudget hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2 w hw hws hsw
    · simp only [if_neg hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact qh9 hne htau hsigma hbudget hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1 w hw hws hsw
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : qaP X (qb lam X) (fun m => qb0 tau lam k f X m^2)
      (qa sigma w)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),qaP X (qb lam X) (fun m => H i X m*H j X m)
        (qa sigma w) := by
    unfold qb0
    simp only [pow_two,Finset.sum_mul_sum,qkv]
    rfl
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam^(d+1)*qcI lam i*q7 (f i)*q7 w)=
      lam^(d+1)*q7 w*qcp lam k f := by
    have he : ∀ i : Fin (k+1),lam^(d+1)*qcI lam i*q7 (f i)*q7 w=
        (lam^(d+1)*q7 w)*(qcI lam i*q7 (f i)) := fun _ => by ring
    simp only [he,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => qcI lam j*q7 (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)
theorem qlM {h : ℕ} (b : Fin 2 → Fin h) :
    b∈qh (fun _ => (1:ℤ)) ↔ b 0≠b 1 := by
  simp only [qh,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hb he
    have hh : qt (fun _ => (1:ℤ)) b 0=qt (fun _ => (1:ℤ)) b 1 := by simp only [qt,he]
    have hi := hb hh
    exact (by decide : (0:Fin 2)≠1) hi
  · intro hb i j hij
    have he : b i=b j := by
      apply Fin.ext
      exact_mod_cast (add_left_cancel (show (1:ℤ)+(b i:ℤ)=1+(b j:ℤ) from hij))
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hb he)
    · exact False.elim (hb he.symm)
    · rfl
theorem qlN {h : ℕ} (F : Fin h → Fin h → ℝ) :
    (∑ v∈qh (s:=2) (h:=h) (fun _ => (1:ℤ)),F (v 0) (v 1))=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F b c else 0 := by
  classical
  have he : qh (s:=2) (h:=h) (fun _ => (1:ℤ))=Finset.univ.filter (fun b => b 0≠b 1) := by
    ext b
    simp only [qlM,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he,Finset.sum_filter]
  calc
    _ = ∑ bc : Fin h × Fin h, if bc.1≠bc.2 then F bc.1 bc.2 else 0 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin h)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _
theorem qml (h : ℕ) (F : ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,F b)=∑ b : Fin h,F (1+b) := by
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext b
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Finset.sum_range]
theorem qlp (h : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F (1+b) (1+c) else 0 := by
  classical
  have he (b : ℕ) : (∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ c∈Finset.Ioc 0 h,if b≠c then F b c else 0 := by
    rw [←Finset.filter_ne,Finset.sum_filter]
  simp_rw [he,qml]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [ne_eq,Nat.add_left_cancel_iff,Fin.val_inj]
theorem qi1 {tau : ℝ} {X : ℕ} (hX : 2≤X) (h : ℕ)
    (H : ℕ → ℝ) (g : (Fin 1 → ℝ) → ℝ)
    (hgs : tsupport g⊆qe 1 tau) :
    qaP X h H (qa (tau+tau) (qi g g))=
      ∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,
        qj X (fun m => H m*qd X (qa tau g) m (fun _ => b)^2*
          qd X (qa tau g) m (fun _ => c)^2) := by
  classical
  have hd (m : ℕ) (v : Fin 2 → Fin h) :
      qd X (qa (tau+tau) (qi g g)) m (fun i => 1+(v i:ℕ))=
        qd X (qa tau g) m (fun _ => 1+(v 0:ℕ))*
        qd X (qa tau g) m (fun _ => 1+(v 1:ℕ)) := by
    convert qbO g g hgs hgs hX m
      (fun _ => 1+(v 0:ℕ)) (fun _ => 1+(v 1:ℕ)) using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold qaP
  simp_rw [hd,mul_pow,←mul_assoc]
  rw [qaF]
  rw [qlN (fun b c : Fin h => qj X (fun m =>
    H m*qd X (qa tau g) m (fun _ => 1+(b:ℕ))^2*
      qd X (qa tau g) m (fun _ => 1+(c:ℕ))^2)),
    qlp]
theorem qgq {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆qe 1 tau) :
    Tendsto (fun X : ℕ => qaP X (qb lam X)
      (fun m => qaU tau lam k f X m^2)
      (qa (tau+tau) (qi g g)))
      atTop (𝓝 (lam^2*q7 g^2*qcp lam k f)) := by
  have hh := qjy f hf htau (by linarith : 0≤tau+tau)
    (by linarith : 2*(tau+(tau+tau))<1) hlam (d:=1) (qi g g)
    (qn g g hgc hgc) (qs g g hgs hgs)
    (qU g g hgt hgt)
  rw [qlQ,←pow_two] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [qcP f hf hX]
theorem qho (hBV : qN) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : qL tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (hw : 0<qcp lam k f)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆qe 1 tau) (hg0 : qa tau g 0=1) :
    ∀ᶠ X : ℕ in atTop,
      qj X (fun m => qaU tau lam k f X m^2*
        q8 X (Finset.Ioc 0 (qb lam X)) m^2)≤
      (lam+lam^2*q7 g^2+1)*qcp lam k f := by
  let q := fun X : ℕ => Real.log (2*X+2*qb lam X)/Real.log X
  let Z := qaU tau lam k f
  let E := fun X : ℕ => qaP X (qb lam X) (fun m => Z X m^2)
    (qa (tau+tau) (qi g g))
  have hlim := ((qet hlam.le).mul
    (qcw hBV f hf htau (by linarith) hlam)).add
    (((qet hlam.le).pow 2).mul
      (qgq f hf htau hbudget hlam g hgc hgs hgt))
  simp only [one_mul,one_pow] at hlim
  have hlim' : Tendsto (fun X : ℕ => q X*qj X (fun m => Z X m^2*
      q8 X (Finset.Ioc 0 (qb lam X)) m)+q X^2*E X)
      atTop (𝓝 ((lam+lam^2*q7 g^2)*qcp lam k f)) := by
    convert hlim using 1
    congr 1
    ring
  have hstrict : (lam+lam^2*q7 g^2)*qcp lam k f<
      (lam+lam^2*q7 g^2+1)*qcp lam k f := by nlinarith
  have hu := hlim'.eventually_lt_const hstrict
  filter_upwards [eventually_ge_atTop 2,hu] with X hX hU
  apply le_trans _ hU.le
  have hh := qf7 (X:=X) (Y:=2*X+2*qb lam X)
    hX (by omega) (Finset.Ioc 0 (qb lam X))
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (fun m => Z X m^2) (fun _ _ => sq_nonneg _) (qa tau g)
    (by linarith : tau<1) (qaV tau g hgt) hg0
  rw [←qi1 hX (qb lam X) (fun m => Z X m^2) g hgt] at hh
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,q,E] using hh
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def qmF (T : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤T then f n else 0,by simp⟩
@[simp] theorem qm5 (T n : ℕ) (f : ArithmeticFunction ℝ) :
    qmF T f n=if n≤T then f n else 0 := rfl
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
noncomputable def qmn (x : ℝ) : ℂ := Complex.exp (Complex.I*(2*Real.pi*x:ℝ))
@[simp] theorem qng : qmn 0=1 := by simp [qmn]
@[simp] theorem qnh (x : ℝ) : ‖qmn x‖=1 := by simp [qmn,Complex.norm_exp]
@[simp] theorem qni (m : ℤ) : qmn m=1 := by
  unfold qmn
  have he : Complex.I * ((2*Real.pi*(m:ℝ):ℝ):ℂ)=(m:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
noncomputable def qaR {q : ℕ} (X : ℕ) (f : ArithmeticFunction ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Icc 1 X,(f n:ℂ)*χ (n:ZMod q)
@[simp] theorem qm0 {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    qaR X (f+g) χ=qaR X f χ+qaR X g χ := by
  simp [qaR,ArithmeticFunction.add_apply,add_mul,Finset.sum_add_distrib]
@[simp] theorem qm1 {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    qaR X (f-g) χ=qaR X f χ-qaR X g χ := by
  unfold qaR
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change ((f n-g n:ℝ):ℂ)*χ (n:ZMod q)=_
  push_cast
  ring
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open Asymptotics
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
open scoped ComplexOrder in
open scoped ComplexOrder in
open scoped ComplexOrder in
open Complex Filter Topology Finset Set MeasureTheory
open Complex Finset ArithmeticFunction
open scoped ComplexOrder
def qd3 (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)
lemma qd3.refl (p : ℕ) (f : ArithmeticFunction ℂ) : qd3 p f f := fun _ => rfl
lemma qd3.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : qd3 p f f') (hg : qd3 p g g') : qd3 p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
open scoped ComplexOrder in
end
section
open Complex Finset ArithmeticFunction
end
section
open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexOrder in
end
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset
end
open Complex Filter Topology Finset
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
end LargePrimeGaps
end OAI
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
open Complex Real Set MeasureTheory Filter Topology
end LargePrimeGaps
end OAI
open Filter OAI.LargePrimeGaps
open scoped Classical
theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1_H2_R1.H2 := by
  intro hBV prof C hC
  let tau : ℝ := 1/8
  let lam : ℝ := C+1
  have htau : 0<tau := by norm_num [tau]
  have hlam : 0<lam := by dsimp [lam]; linarith
  obtain ⟨g,hgs,hgc,hgt,_hgb,_hGc,_hGcompact,hg0⟩ := qkn htau
  let D := lam+lam^2*q7 g^2+1
  have hD : 0<D := by dsimp [D]; positivity
  let eps := lam^2/(16*D)
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨k,f,hf,_hf0,hw,hv⟩ := prof lam tau eps hlam htau heps
  let w := qcp lam k f
  have hw' : 0<w := hw
  let a := lam*w/2
  let K := D*w
  let b := 2*(eps*w)
  have ha : 0<a := by dsimp [a]; positivity
  have hK : 0<K := mul_pos hD hw'
  have hab : a^2/K=4*(eps*w) := by
    dsimp [a,K,eps]
    field_simp
    ring
  have hb : b<a^2/K := by
    rw [hab]
    dsimp [b]
    nlinarith [mul_pos heps hw']
  obtain ⟨M,hM,hfourth⟩ := qh4 f hf htau.le
    (by norm_num [tau] : 4*tau<1) hlam
  let delta := (a^2/K-b)^2/M
  refine ⟨delta, div_pos (sq_pos_of_pos (sub_pos.mpr hb)) hM, ?_⟩
  have aux
    (W : ℕ → ℕ → ℝ) (a K b M : ℝ)
    (ha : 0<a) (hK : 0<K) (hM : 0<M) (hb : b<a^2/K)
    (hw : ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Ioc X (2*X), 0≤W X m)
    (hfirst : ∀ᶠ X : ℕ in atTop,
      a≤qj X (fun m => W X m*q8 X (Finset.Ioc 0 (qb (C+1) X)) m))
    (hdetect : ∀ᶠ X : ℕ in atTop,
      qj X (fun m => W X m*q8 X (Finset.Ioc 0 (qb (C+1) X)) m^2)≤K)
    (hsuppress : ∀ᶠ X : ℕ in atTop,
      qj X (fun m => W X m*q8 X
        (Finset.Ioc (qb (C+1) X) (2*qb (C+1) X)) m)≤b)
    (hsecond : ∀ᶠ X : ℕ in atTop, qj X (fun m => W X m^2)≤M) :
      ∀ᶠ X : ℕ in atTop, ((a^2/K-b)^2/M)*(X:ℝ)≤((qi4 X (qb (C+1) X)).card:ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hw,hfirst,hdetect,hsuppress,hsecond]
      with X hX hW hF hD hS hQ
    exact qib hX (W X) a K b M ha hK hM hb hW hF hD hS hQ
  refine aux
    (fun X m => qaU tau lam k f X m^2) a K b M ha hK hM hb ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun _ _ _ => sq_nonneg _
  · have hlim := qcw hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hlt : a<lam*qcp lam k f := by
      change lam*w/2<lam*w
      nlinarith [mul_pos hlam hw']
    exact Eventually.mono ((tendsto_order.mp hlim).1 a hlt) fun _ h => h.le
  · exact qho hBV f hf htau.le
      (by norm_num [tau] : 6*tau<1) hlam hw g hgc hgs hgt hg0
  · have hlim := qeU hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hV : qmm lam k f≤eps*w := (div_le_iff₀ hw).mp hv
    have hlt : qmm lam k f<b := by
      dsimp [b]
      nlinarith [mul_pos heps hw']
    exact Eventually.mono ((tendsto_order.mp hlim).2 b hlt) fun _ h => h.le
  · filter_upwards [hfourth] with X hX
    simpa only [←pow_mul] using hX

