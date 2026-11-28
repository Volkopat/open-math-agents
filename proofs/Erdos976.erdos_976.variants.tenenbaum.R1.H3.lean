import OMAReductions.R_Erdos976_erdos_976_variants_tenenbaum_R1
import Mathlib

/-! Erdős–Schinzel's transfer from divisors in (n/2,n] to a large prime factor.
We prove the sharp root-weighted Mertens upper bound by averaging norm determinants
over an integral box. A Vandermonde matrix counts every simultaneous root with its
multiplicity in the determinant, and bounded residue representatives control the
boundary loss. The factorial comparison uses the credited Nagell–Ricci lemmas below.
Reference: Erdős and Schinzel, Acta Arith. 55 (1990), 191–200, Theorem 3. -/

section
/- The next four polynomial growth and factorial lemmas are from Lane C's
merged Nagell–Ricci proof, contributed by @koolkao to open-math-agents.
The aggregate estimate below is the same elementary factorial comparison. -/
namespace OMA.Growth976
open Finset Real Polynomial Filter
theorem eval_ne_zero {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (k : ℤ) :
    f.eval k ≠ 0 := by
  intro h
  have hdvd : X - C k ∣ f := dvd_iff_isRoot.mpr h
  obtain ⟨g, hg⟩ := hdvd
  rcases hf.isUnit_or_isUnit hg with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at this; exact one_ne_zero this
  · have h0 : g ≠ 0 := by rintro rfl; simp at hg; exact hf.ne_zero hg
    have := natDegree_eq_zero_of_isUnit hu
    have h2 := congrArg natDegree hg
    rw [natDegree_mul (X_sub_C_ne_zero k) h0, natDegree_X_sub_C, this] at h2
    omega

/-- `|f(k)| ≤ S k^d` for `k ≥ 1`. -/
theorem natAbs_eval_le (f : ℤ[X]) : ∃ S : ℕ, 1 ≤ S ∧ ∀ k : ℕ, 1 ≤ k →
    (f.eval ((k : ℕ) : ℤ)).natAbs ≤ S * k ^ f.natDegree := by
  refine ⟨∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs + 1, by omega, fun k hk ↦ ?_⟩
  have h1 : (f.eval ((k : ℕ) : ℤ)).natAbs ≤ ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs * k ^ i := by
    rw [eval_eq_sum_range]
    refine (Int.natAbs_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  refine h1.trans ?_
  calc ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs * k ^ i
      ≤ ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs * k ^ f.natDegree :=
        Finset.sum_le_sum fun i hi ↦ Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = (∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs) * k ^ f.natDegree := by
        rw [Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- `d log k - C ≤ log |f(k)|` for all `k ≥ 1`. -/
theorem log_abs_eval_ge {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → f.natDegree * Real.log k - C ≤ Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
  set fR := f.map (Int.castRingHom ℝ)
  have hlead : fR.leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff_map_of_injective (RingHom.injective_int _)]; rfl
  have hdeg : fR.natDegree = f.natDegree := natDegree_map_eq_of_injective (RingHom.injective_int _) _
  have ha : (f.leadingCoeff : ℝ) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr hf.ne_zero
  have hequiv := Polynomial.isEquivalent_atTop_lead fR
  rw [hlead, hdeg] at hequiv
  have hz : ∀ᶠ x : ℝ in atTop, (f.leadingCoeff : ℝ) * x ^ f.natDegree ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_ne_zero ha (pow_ne_zero _ hx.ne')
  have htend := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hequiv
  have hev : ∀ᶠ x : ℝ in atTop, 1 / 2 ≤ fR.eval x / (f.leadingCoeff * x ^ f.natDegree) := by
    have := htend.eventually (Ici_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    filter_upwards [this] with x hx
    simpa using hx
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 1))
  set k0 := ⌈x0⌉₊
  have hla : 1 ≤ |(f.leadingCoeff : ℝ)| := by
    have : (1 : ℝ) ≤ |f.leadingCoeff| := by exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hf.ne_zero)
    simpa using this
  refine ⟨f.natDegree * Real.log (k0 + 1) + Real.log 2, fun k hk ↦ ?_⟩
  have hfk : (1 : ℝ) ≤ |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (eval_ne_zero hf hd (k : ℤ))
  have hlogf : 0 ≤ Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := Real.log_nonneg hfk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hkk : (k : ℝ) < x0
  · have : Real.log k ≤ Real.log (k0 + 1) := by
      apply Real.log_le_log (by linarith)
      have := Nat.le_ceil x0; linarith
    have hd0 : (0 : ℝ) ≤ f.natDegree := by positivity
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num), mul_le_mul_of_nonneg_left this hd0]
  · push Not at hkk
    obtain ⟨h1, -⟩ := hx0 k hkk
    have hpos : 0 < (k : ℝ) ^ f.natDegree := by positivity
    have heval : fR.eval (k : ℝ) = ((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ) := by
      simp [fR, eval_map]
    rw [heval] at h1
    have h2 : |(f.leadingCoeff : ℝ)| * (k : ℝ) ^ f.natDegree / 2 ≤ |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
      set F := ((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)
      set A := (f.leadingCoeff : ℝ) * (k : ℝ) ^ f.natDegree
      have hA : A ≠ 0 := mul_ne_zero ha hpos.ne'
      have e1 : |F| = |F / A| * |A| := by
        rw [abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hA)]
      have e2 : 1 / 2 ≤ |F / A| := le_trans h1 (le_abs_self _)
      have e3 : |A| = |(f.leadingCoeff : ℝ)| * (k : ℝ) ^ f.natDegree := by
        rw [abs_mul, abs_of_pos hpos]
      rw [e1, ← e3]
      nlinarith [abs_nonneg A]
    have h4 : (k : ℝ) ^ f.natDegree / 2 ≤ |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
      refine le_trans ?_ h2
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    have h5 := Real.log_le_log (by positivity) h4
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h5
    have : 0 ≤ f.natDegree * Real.log (k0 + 1) := by
      have : (0 : ℝ) ≤ Real.log (k0 + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k0; linarith)
      positivity
    linarith

theorem log_factorial_ge (n : ℕ) : n * Real.log n - n ≤ Real.log (n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hf] at h
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at this
  linarith


theorem total {f : Polynomial ℤ} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ D : ℝ, ∀ n : ℕ, (f.natDegree:ℝ)*n*log n-D*n ≤
      ∑ k ∈ Icc 1 n, log ((f.eval (k:ℤ)).natAbs : ℝ) := by
  obtain ⟨C,hC⟩ := log_abs_eval_ge hf hd
  refine ⟨f.natDegree+C, fun n => ?_⟩
  have cmp := sum_le_sum (s:=Icc 1 n) (fun k hk => hC k (mem_Icc.mp hk).1)
  have fac : ∑ k ∈ Icc 1 n, log (k:ℝ) = log n.factorial := by
    have iset : Icc 1 n = Ico 1 (n+1) := by ext; simp only [mem_Icc,mem_Ico]; omega
    rw [←Real.log_prod (fun k hk => by have := (mem_Icc.mp hk).1; positivity),
      ←Nat.cast_prod,iset,Finset.prod_Ico_id_eq_factorial]
  rw [sum_sub_distrib, ←Finset.mul_sum,fac] at cmp
  simp only [sum_const, Nat.card_Icc, Nat.add_one_sub_one, nsmul_eq_mul] at cmp
  have e : ∀ k : ℕ, (((f.eval (k:ℤ)).natAbs:ℕ):ℝ) = |((f.eval (k:ℤ):ℤ):ℝ)| := by
    intro k
    rw [←Int.cast_abs, ←Int.natCast_natAbs,Int.cast_natCast]
  simp_rw [e]
  nlinarith [mul_le_mul_of_nonneg_left (log_factorial_ge n) (Nat.cast_nonneg (α:=ℝ) f.natDegree)]
end OMA.Growth976
end

section
/- Large prime factors of a polynomial value. A divisor in the upper half
of [1,n] takes the place of one of the large prime factors, including multiplicity. -/
namespace OMA.Split976
open Nat

def big (B m : ℕ) : List ℕ := m.primeFactorsList.filter (B < ·)
def small (B m : ℕ) : ℕ := (m.primeFactorsList.filter (· ≤ B)).prod

theorem split (B m : ℕ) (hm : m ≠ 0) : small B m * (big B m).prod = m := by
  unfold small big
  conv_rhs => rw [← Nat.prod_primeFactorsList hm]
  generalize m.primeFactorsList = l
  change (l.filter (· ≤ B)).prod * (l.filter (B < ·)).prod = l.prod
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a ≤ B
    · simp [h,not_lt.mpr h,mul_assoc,ih]
    · simpa [h,Nat.lt_of_not_ge h,List.filter_cons,mul_left_comm,mul_assoc] using
        congrArg (a * ·) ih

theorem small_pos (B m : ℕ) (hm : 0 < m) : 0 < small B m :=
  Nat.pos_of_ne_zero fun h => by have := split B m hm.ne'; rw [h,zero_mul] at this; omega

theorem divisor_small {B m t : ℕ} (hm : 0 < m) (ht : t ∣ m) (hle : t ≤ B) :
    t ∣ small B m := by
  obtain ⟨q,rfl⟩ := ht
  have ht0 : 0 < t := Nat.pos_of_mul_pos_right hm
  have hq : 0 < q := Nat.pos_of_mul_pos_left hm
  have e := ((Nat.perm_primeFactorsList_mul ht0.ne' hq.ne').filter
    (fun x => decide (x ≤ B))).prod_eq
  have hfilter : t.primeFactorsList.filter (· ≤ B) = t.primeFactorsList := by
    refine List.filter_eq_self.mpr fun p hp => ?_
    exact decide_eq_true <| (Nat.le_of_dvd ht0 (Nat.dvd_of_mem_primeFactorsList hp)).trans hle
  simpa only [small,List.filter_append,List.prod_append,hfilter,Nat.prod_primeFactorsList ht0.ne'] using
    (show t ∣ ((t*q).primeFactorsList.filter (· ≤ B)).prod from by
      rw [e,List.filter_append,List.prod_append,hfilter,Nat.prod_primeFactorsList ht0.ne']
      exact dvd_mul_right ..)

theorem large_count {S n d m : ℕ} (hS : 1 ≤ S) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hm : 0 < m) (hu : m ≤ S*n^d) :
    (big (2*S*n) m).length ≤ d-1 ∧
    (∀ t : ℕ, n/2 < t → t ≤ n → t ∣ m → (big (2*S*n) m).length ≤ d-2) := by
  let B := 2*S*n
  let l := big B m
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hl : B^l.length ≤ l.prod := by
    apply List.pow_card_le_prod
    intro p hp
    exact le_of_lt (of_decide_eq_true (List.mem_filter.mp hp).2)
  have hs : small B m * l.prod = m := split B m hm.ne'
  have hsmall := small_pos B m hm
  have upper (j : ℕ) (hj : j ≤ l.length) :
      small B m * ((2*S)^j * n^j) ≤ S*n^d := by
    rw [← mul_pow]
    exact (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right hB hj).trans hl)).trans (hs.le.trans hu)
  constructor
  · by_contra! h
    have E := upper d (by change _ ≤ (big (2*S*n) m).length; omega)
    have s : 2*S ≤ (2*S)^d := by
      simpa using Nat.pow_le_pow_right (show 1 ≤ 2*S by omega) (show 1 ≤ d by omega)
    have w : S < small B m * (2*S)^d := by
      have z := Nat.mul_le_mul_right ((2*S)^d) hsmall
      simp only [Nat.succ_eq_add_one,zero_add,one_mul] at z
      omega
    have v := Nat.mul_lt_mul_of_pos_right w (show 0 < n^d by positivity)
    nlinarith only [v,E]
  · intro t ht htn htm
    have hnb : n ≤ B := by dsimp [B]; nlinarith
    have hts := Nat.le_of_dvd hsmall (divisor_small hm htm (htn.trans hnb))
    by_contra! h
    have E := upper (d-1) (by change _ ≤ (big (2*S*n) m).length; omega)
    have s : 2*S ≤ (2*S)^(d-1) := by
      simpa using Nat.pow_le_pow_right (show 1 ≤ 2*S by omega) (show 1 ≤ d-1 by omega)
    have w : S*n < small B m * (2*S)^(d-1) := by
      have h2 : n < 2*t := by omega
      nlinarith [Nat.mul_lt_mul_of_pos_left h2 (by omega : 0 < S),
        Nat.mul_le_mul hts s]
    have v := Nat.mul_lt_mul_of_pos_right w (show 0 < n^(d-1) by positivity)
    rw [show n^d = n^(d-1)*n by rw [←pow_succ]; congr 1; omega] at E
    nlinarith only [v,E]

end OMA.Split976
end

section
open Finset Real

namespace OMA.Split976

theorem all_small {m B : ℕ} (hm : 0 < m)
    (h : ∀ p ∈ m.primeFactorsList, p ≤ B) : small B m = m := by
  unfold small
  rw [List.filter_eq_self.mpr (fun p hp => decide_eq_true (h p hp)),
    Nat.prod_primeFactorsList hm.ne']

theorem log_bound {S n d m P : ℕ} (hS : 1 ≤ S) (hn : 1 ≤ n)
    (hd : 2 ≤ d) (hm : 0 < m) (_hP : 1 ≤ P) (hu : m ≤ S*n^d)
    (hle : ∀ p ∈ m.primeFactorsList, p ≤ P) (hit : Prop) [Decidable hit]
    (hh : hit → ∃ t : ℕ, n/2 < t ∧ t ≤ n ∧ t ∣ m) :
    log (m:ℝ) ≤ log (small (2*S*n) m) +
      ((d:ℝ) - 1 - (if hit then 1 else 0)) * log P := by
  let l := big (2*S*n) m
  obtain ⟨h1,h2⟩ := large_count hS hn hd hm hu
  have hl : l.prod ≤ P^l.length := List.prod_le_pow_card _ _ fun p hp =>
    hle p (List.mem_filter.mp hp).1
  have hs := split (2*S*n) m hm.ne'
  have hlpos : 0 < l.prod := Nat.pos_of_mul_pos_left (hs.symm ▸ hm)
  have hx : (l.prod:ℝ) ≤ (P:ℝ)^l.length := by exact_mod_cast hl
  have hlog := Real.log_le_log (by exact_mod_cast hlpos) hx
  rw [Real.log_pow] at hlog
  have eq : log (m:ℝ) = log (small (2*S*n) m) + log (l.prod:ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast (small_pos _ _ hm).ne') (by exact_mod_cast hlpos.ne')]
    simpa only [Nat.cast_mul] using congrArg (fun a : ℕ => log (a:ℝ)) hs.symm
  have bound : (l.length:ℝ) ≤ (d:ℝ)-1-(if hit then 1 else 0) := by
    by_cases h : hit
    · obtain ⟨t,ht,htn,htm⟩ := hh h
      have E : l.length+2 ≤ d := by have := h2 t ht htn htm; dsimp [l]; omega
      have E' : (l.length:ℝ)+2 ≤ d := by exact_mod_cast E
      simp only [if_pos h]; linarith
    · have E : l.length+1 ≤ d := by dsimp [l]; omega
      have E' : (l.length:ℝ)+1 ≤ d := by exact_mod_cast E
      simp only [if_neg h]; linarith
  rw [eq]
  linarith [mul_le_mul_of_nonneg_right bound (Real.log_natCast_nonneg P)]

theorem sum_bound {S n d P : ℕ} (hS : 1 ≤ S) (hn : 1 ≤ n)
    (hd : 2 ≤ d) (hP : 1 ≤ P) (m : ℕ → ℕ) (hit : ℕ → Prop) [DecidablePred hit]
    (hm : ∀ k ∈ Icc 1 n, 0 < m k) (hu : ∀ k ∈ Icc 1 n, m k ≤ S*n^d)
    (hle : ∀ k ∈ Icc 1 n, ∀ p ∈ (m k).primeFactorsList, p ≤ P)
    (hh : ∀ k ∈ Icc 1 n, hit k → ∃ t : ℕ, n/2 < t ∧ t ≤ n ∧ t ∣ m k) :
    ∑ k ∈ Icc 1 n, log (m k : ℝ) ≤ ∑ k ∈ Icc 1 n, log (small (2*S*n) (m k)) +
      (((d:ℝ)-1)*n - (((Icc 1 n).filter hit).card:ℝ))*log P := by
  calc
    _ ≤ ∑ k ∈ Icc 1 n, (log (small (2*S*n) (m k)) +
        ((d:ℝ)-1-(if hit k then 1 else 0))*log P) :=
      Finset.sum_le_sum fun k hk => log_bound hS hn hd (hm k hk) hP (hu k hk) (hle k hk) _ (hh k hk)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
      simp [mul_comm]
      exact Or.inl (by ring)

theorem transfer {n d P : ℕ} (hn : 0 < n) (hd : 0 < d) (hits : ℕ) (A D : ℝ)
    (hdom : (n:ℝ) * exp (max 0 (A+D)) ≤ P)
    (hbudget : (d:ℝ)*n*log n - D*n ≤ n*log n+A*n+(((d:ℝ)-1)*n-hits)*log P) :
    (n:ℝ) * exp (log n * hits / (d*n)) ≤ P := by
  have nn : 0 < (n:ℝ) := by exact_mod_cast hn
  have dd : 0 < (d:ℝ) := by exact_mod_cast hd
  have e : 1 ≤ exp (max 0 (A+D)) := Real.one_le_exp (le_max_left ..)
  have np : (n:ℝ) ≤ P := (le_mul_of_one_le_right nn.le e).trans hdom
  have pp : 0 < (P:ℝ) := nn.trans_le np
  have lnp := log_le_log nn np
  have la := log_le_log (mul_pos nn (exp_pos _)) hdom
  rw [log_mul nn.ne' (exp_pos _).ne', log_exp] at la
  have absorb : A+D ≤ log P-log n := by linarith [le_max_right 0 (A+D)]
  have h : log n * hits ≤ ((d:ℝ)*n)*(log P-log n) := by
    nlinarith [mul_le_mul_of_nonneg_right absorb nn.le,
      mul_le_mul_of_nonneg_right lnp (Nat.cast_nonneg (α:=ℝ) hits)]
  have hdiv := (div_le_iff₀ (mul_pos dd nn)).mpr (by linarith only [h] : log n * hits ≤ (log P-log n)*((d:ℝ)*n))
  rw [← exp_log nn, ← exp_add, ← exp_log pp]
  apply exp_le_exp.mpr
  simpa only [exp_log nn,exp_log pp] using (by linarith : log n + log n * hits / ((d:ℝ)*n) ≤ log P)

end OMA.Split976
end

section
/- Erdős–Schinzel's transfer for the hits in the upper half of the divisor range.
The large-prime product loses one factor at each hit. The fixed cutoff 2 S n
absorbs the constant in the global polynomial growth bound. -/

namespace OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H3_R1
open Filter Finset Real OMA.Split976
open scoped Classical

/-- Nagell's small-prime estimate, with the full coefficient one of n log n. -/
def H1 : Prop := ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree →
  ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, ∑ k ∈ Icc 1 n, log (small n (f.eval (k:ℤ)).natAbs) ≤
    n * log n + A*n

/-- The primes between n and any fixed multiple of n contribute O(n) in total. -/
def H2 : Prop := ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree → ∀ C : ℕ, 1 ≤ C →
  ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, ∑ k ∈ Icc 1 n, log (small (C*n) (f.eval (k:ℤ)).natAbs) ≤
    (∑ k ∈ Icc 1 n, log (small n (f.eval (k:ℤ)).natAbs)) + A*n

theorem main : H1 → H2 → OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1.H3 := by
  intro sharp middle f hf hd
  let d := f.natDegree
  let m (k : ℕ) := (f.eval (k:ℤ)).natAbs
  let P (n : ℕ) := Erdos976.F f n
  have hm (k : ℕ) : 0 < m k :=
    Int.natAbs_pos.mpr (OMA.Growth976.eval_ne_zero hf hd _)
  have hle (n k : ℕ) (hk : k ∈ Icc 1 n) (p : ℕ) (hp : p ∈ (m k).primeFactorsList) :
      p ≤ P n := by
    let prod := ∏ j ∈ Icc 1 n, f.eval (j:ℤ)
    have hprod : prod ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => OMA.Growth976.eval_ne_zero hf hd _
    apply Nat.le_maxPrimeFac (Int.natAbs_ne_zero.mpr hprod) (Nat.prime_of_mem_primeFactorsList hp)
    apply (Nat.dvd_of_mem_primeFactorsList hp).trans
    exact Int.natAbs_dvd_natAbs.mpr <| Finset.dvd_prod_of_mem _ hk
  obtain ⟨D,htotal⟩ := OMA.Growth976.total hf hd
  obtain ⟨S,hS,hpoly⟩ := OMA.Growth976.natAbs_eval_le f
  obtain ⟨A₀,ha⟩ := sharp f hf hd
  have capped (C : ℕ) (hC : 1 ≤ C) : ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ∑ k ∈ Icc 1 n, log (small (C*n) (m k)) ≤ n*log n + A*n := by
    obtain ⟨B,hb⟩ := middle f hf hd C hC
    refine ⟨A₀+B, ?_⟩
    filter_upwards [ha,hb] with n h1 h2
    dsimp [m] at *
    linarith
  have grows (C : ℕ) (hC : 1 ≤ C) : ∀ᶠ n : ℕ in atTop, C*n < P n := by
    obtain ⟨A,cut⟩ := capped C hC
    have lim := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (max 0 (A+D))
    filter_upwards [cut,lim,eventually_ge_atTop (1:ℕ)] with n upper hl hn
    change max 0 (A+D) < log n at hl
    by_contra! h
    have eq : ∀ k ∈ Icc 1 n, small (C*n) (m k) = m k := fun k hk =>
      all_small (hm k) (fun p hp => (hle n k hk p hp).trans h)
    have sumEq := sum_congr rfl (fun k hk => congrArg (fun a : ℕ => log (a:ℝ)) (eq k hk))
    rw [sumEq] at upper
    have low := htotal n
    change (d:ℝ)*n*log n - D*n ≤ ∑ k ∈ Icc 1 n, log (m k : ℝ) at low
    have nn : (0:ℝ) < n := by exact_mod_cast hn
    have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_lt_mul_of_pos_right ((le_max_right 0 (A+D)).trans_lt hl) nn,
      mul_le_mul_of_nonneg_right hdR (mul_nonneg nn.le (Real.log_natCast_nonneg n))]
  obtain ⟨A,cut⟩ := capped (2*S) (by omega)
  let C := ⌈exp (max 0 (A+D))⌉₊+1
  filter_upwards [cut,grows C (by dsimp [C]; omega),eventually_ge_atTop (1:ℕ)] with n upper hg hn
  have hP : 1 ≤ P n := by omega
  let hit (k : ℕ) := 0 < ((Ioc (n/2) n).filter (fun t : ℕ => (t:ℤ) ∣ f.eval (k:ℤ))).card
  have hh (k : ℕ) (_ : k ∈ Icc 1 n) (h : hit k) : ∃ t : ℕ, n/2 < t ∧ t ≤ n ∧ t ∣ m k := by
    obtain ⟨t,ht⟩ := Finset.card_pos.mp h
    obtain ⟨he,hdvd⟩ := mem_filter.mp ht
    exact ⟨t,(mem_Ioc.mp he).1,(mem_Ioc.mp he).2,Int.natCast_dvd.mp hdvd⟩
  have hu (k : ℕ) (hk : k ∈ Icc 1 n) : m k ≤ S*n^d :=
    (hpoly k (mem_Icc.mp hk).1).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (mem_Icc.mp hk).2 _))
  have bound := sum_bound hS hn hd hP m hit (fun k _ => hm k) hu (hle n) hh
  have dom : (n:ℝ) * exp (max 0 (A+D)) ≤ P n := by
    have hc : exp (max 0 (A+D)) ≤ (C:ℝ) := by
      dsimp [C]; push_cast; linarith [Nat.le_ceil (exp (max 0 (A+D)))]
    have e : (C:ℝ)*n ≤ P n := by exact_mod_cast hg.le
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α:=ℝ) n)]
  apply transfer (by omega) (d:=d) (by dsimp [d]; omega) _ A D dom
  have tot := htotal n
  change (d:ℝ)*n*log n-D*n ≤ ∑ k ∈ Icc 1 n, log (m k:ℝ) at tot
  exact tot.trans (bound.trans (add_le_add_left upper _))

end OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H3_R1
end

section
namespace OMA.Companion975

open Polynomial Finset

def vEval {R : Type*} [CommRing R] {d : ℕ} (r : R) (b : Fin d → ℤ) : R :=
  ∑ i, (b i : R) * r ^ i.val

/-- Columns of multiplication by the integral element aX on the original power coordinates. -/
def column (f : ℤ[X]) (i j : Fin f.natDegree) : ℤ :=
  if i.val + 1 < f.natDegree then (if j.val = i.val + 1 then f.leadingCoeff else 0)
  else - f.coeff j.val

def T (f : ℤ[X]) (b : Fin f.natDegree → ℤ) (j : Fin f.natDegree) : ℤ :=
  ∑ i, b i * column f i j

def matrix (f : ℤ[X]) (b : Fin f.natDegree → ℤ) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ :=
  fun i j => (T f)^[j.val] b i

private lemma eval_column {R : Type*} [CommRing R] (f : ℤ[X]) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0) (i : Fin f.natDegree) :
    vEval r (column f i) = (f.leadingCoeff : R) * r ^ (i.val + 1) := by
  classical
  by_cases hi : i.val + 1 < f.natDegree
  · let t : Fin f.natDegree := ⟨i.val + 1, hi⟩
    have ee (j : Fin f.natDegree) : (j.val = i.val + 1) ↔ j = t :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp [vEval, column, hi, ee, t, ite_mul]
  · have he : i.val + 1 = f.natDegree := by omega
    rw [eval₂_eq_sum_range, sum_range_succ, ← Fin.sum_univ_eq_sum_range] at hr
    simp only [Int.coe_castRingHom, coeff_natDegree] at hr
    simp only [vEval, column, if_neg hi, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [he]
    linear_combination -hr

lemma eval_T {R : Type*} [CommRing R] (f : ℤ[X]) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0) (b : Fin f.natDegree → ℤ) :
    vEval r (T f b) = ((f.leadingCoeff : R) * r) * vEval r b := by
  classical
  simp only [vEval, T, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (b i : R) * vEval r (column f i) = _
  rw [eval_column f r hr, pow_succ]
  ring

lemma eval_iterate {R : Type*} [CommRing R] (f : ℤ[X]) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0) (b : Fin f.natDegree → ℤ) (j : ℕ) :
    vEval r ((T f)^[j] b) = ((f.leadingCoeff : R) * r) ^ j * vEval r b := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', eval_T f r hr, ih, pow_succ']; ring

private lemma eval_coeffs_zero {R : Type*} [Field R] [Algebra ℚ R] {d : ℕ} (r : R)
    (basis : LinearIndependent ℚ (fun i : Fin d => r ^ i.val)) (b : Fin d → ℤ)
    (zero : vEval r b = 0) : b = 0 := by
  apply _root_.funext
  intro i
  have hz := (Fintype.linearIndependent_iff.mp basis) (fun j => (b j : ℚ))
  have zero' : ∑ j : Fin d, (b j : ℚ) • r ^ j.val = 0 := by
    simpa [Algebra.smul_def, vEval] using zero
  exact_mod_cast hz zero' i

private lemma eval_lincomb {R : Type*} [CommRing R] {d : ℕ} (r : R)
    (M : Matrix (Fin d) (Fin d) ℤ) (g : Fin d → ℤ) :
    vEval r (∑ i, g i • M.col i) = ∑ i, (g i : R) * vEval r (M.col i) := by
  classical
  simp only [vEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma det_ne_zero (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    (b : Fin f.natDegree → ℤ) (hb : b ≠ 0) : (matrix f b).det ≠ 0 := by
  classical
  let F := f.map (Int.castRingHom ℚ)
  have irr : Irreducible F :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd)).mp hf
  let : Fact (Irreducible F) := ⟨irr⟩
  let r := AdjoinRoot.root F
  have hr : f.eval₂ (Int.castRingHom (AdjoinRoot F)) r = 0 := by
    have heq : (AdjoinRoot.of F).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AdjoinRoot F) := Subsingleton.elim _ _
    simpa only [F, Polynomial.eval₂_map, heq] using AdjoinRoot.eval₂_root F
  have e : F.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) _
  have hlin : LinearIndependent ℚ (fun i : Fin F.natDegree => r ^ i.val) := by
    let pb := AdjoinRoot.powerBasis irr.ne_zero
    have heq : (fun i : Fin F.natDegree => r ^ i.val) = pb.basis :=
      _root_.funext fun i => (pb.basis_eq_pow i).symm
    rw [heq]
    exact pb.basis.linearIndependent
  have basis : LinearIndependent ℚ (fun i : Fin f.natDegree => r ^ i.val) := by
    exact hlin.comp (Fin.cast e.symm) (Fin.cast_injective _)
  have vne : vEval r b ≠ 0 := fun z => hb (eval_coeffs_zero r basis b z)
  rw [← Matrix.nonsingular_iff_det_ne_zero, ← Matrix.linearIndependent_col_iff,
    Fintype.linearIndependent_iff]
  intro g hg i
  have hzero := congrArg (vEval r) hg
  rw [eval_lincomb] at hzero
  have hcol (j : Fin f.natDegree) :
      vEval r ((matrix f b).col j) = ((f.leadingCoeff : AdjoinRoot F) * r) ^ j.val * vEval r b :=
    eval_iterate f r hr b j.val
  simp only [hcol, ← mul_assoc, ← Finset.sum_mul] at hzero
  have heval0 : vEval r (0 : Fin f.natDegree → ℤ) = 0 := by simp [vEval]
  rw [heval0] at hzero
  have hz := (mul_eq_zero.mp hzero).resolve_right vne
  let coeff (j : Fin f.natDegree) := g j * f.leadingCoeff ^ j.val
  have rel : vEval r coeff = 0 := by
    simpa [vEval, coeff, mul_pow, mul_assoc] using hz
  have hc := congrFun (eval_coeffs_zero r basis coeff rel) i
  exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf.ne_zero))

/-- One common bound on the column sums of multiplication by aX. -/
private def stepSize (f : ℤ[X]) : ℕ :=
  1 + ∑ j, ∑ i, (column f i j).natAbs

private lemma step_bound (f : ℤ[X]) (t : ℕ) (b : Fin f.natDegree → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ t) (j : Fin f.natDegree) : (T f b j).natAbs ≤ stepSize f * t := by
  have hcol := Finset.single_le_sum (f := fun j : Fin f.natDegree => ∑ i, (column f i j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  calc
    (T f b j).natAbs ≤ ∑ i, (b i * column f i j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ i, (column f i j).natAbs * t := Finset.sum_le_sum fun i _ => by
      rw [Int.natAbs_mul, mul_comm]; exact Nat.mul_le_mul_left _ (hb i)
    _ ≤ stepSize f * t := by
      rw [← Finset.sum_mul]
      exact Nat.mul_le_mul_right _ (le_trans hcol (by unfold stepSize; omega))

private lemma iterate_bound (f : ℤ[X]) (t : ℕ) (b : Fin f.natDegree → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ t) (j : ℕ) (i : Fin f.natDegree) :
    ((T f)^[j] b i).natAbs ≤ stepSize f ^ j * t := by
  induction j generalizing i with
  | zero => simpa using hb i
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact step_bound f _ _ ih i

lemma determinant_bound (f : ℤ[X]) :
    ∃ K : ℕ, ∀ (t : ℕ) (b : Fin f.natDegree → ℤ), (∀ i, (b i).natAbs ≤ t) →
      (matrix f b).det.natAbs ≤ K * t ^ f.natDegree := by
  classical
  let d := f.natDegree
  let A := stepSize f ^ d
  refine ⟨Fintype.card (Equiv.Perm (Fin d)) * A ^ d, ?_⟩
  intro t b hb
  have entry (i j : Fin d) : ((matrix f b) i j).natAbs ≤ A * t := by
    apply (iterate_bound f t b hb j.val i).trans
    have hpos : 0 < stepSize f := by unfold stepSize; omega
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hpos j.isLt.le)
  rw [Matrix.det_apply]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (A * t) ^ d := Finset.sum_le_sum fun σ _ => by
      rw [Units.smul_def, smul_eq_mul, Int.natAbs_mul, Int.units_natAbs, one_mul]
      change Int.natAbsHom (∏ i, (matrix f b) (σ i) i) ≤ _
      rw [map_prod]
      exact (Finset.prod_le_prod' (fun i _ => entry (σ i) i)).trans_eq (by simp)
    _ = _ := by simp [d, mul_pow, mul_assoc]

lemma columns_divisible (f : ℤ[X]) (q r : ℕ) (b : Fin f.natDegree → ℤ)
    (hroot : (q : ℤ) ∣ f.eval (r : ℤ))
    (hzero : ∑ i, (b i : ZMod q) * (r : ZMod q) ^ i.val = 0) (j : Fin f.natDegree) :
    (q : ℤ) ∣ ∑ i, (r : ℤ) ^ i.val * matrix f b i j := by
  have hr : f.eval₂ (Int.castRingHom (ZMod q)) (r : ZMod q) = 0 := by
    have h := Polynomial.eval₂_at_apply (p := f) (Int.castRingHom (ZMod q)) (r : ℤ)
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      h.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hroot)
  have ev := eval_iterate f (r : ZMod q) hr b j.val
  change vEval (r : ZMod q) b = 0 at hzero
  rw [hzero, mul_zero] at ev
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  simpa [vEval, matrix, mul_comm] using ev

end OMA.Companion975
end

section
/- Each distinct root at which a coefficient vector vanishes forces a separate
factor of p in its norm determinant. A Vandermonde matrix separates the roots. -/
namespace OMA.Charge976
open Finset Matrix Polynomial

theorem rows_dvd {d p : ℕ} (M : Matrix (Fin d) (Fin d) ℤ) (s : Finset (Fin d))
    (h : ∀ i ∈ s, ∀ j, (p:ℤ) ∣ M i j) : (p:ℤ)^s.card ∣ M.det := by
  classical
  let a (i : Fin d) : ℤ := if i ∈ s then p else 1
  let N : Matrix (Fin d) (Fin d) ℤ := fun i j =>
    if hi : i ∈ s then (h i hi j).choose else M i j
  have eq : M = diagonal a * N := by
    ext i j
    simp only [diagonal_mul]
    by_cases hi : i ∈ s
    · simpa [a,N,hi] using (h i hi j).choose_spec
    · simp [a,N,hi]
  rw [eq,det_mul,det_diagonal]
  have prod : (∏ i, a i) = (p:ℤ)^s.card := by
    simp [a]
  rw [prod]
  exact dvd_mul_right _ _

theorem root_charge {d p : ℕ} (hp : p.Prime) (hdp : d ≤ p)
    (A : Matrix (Fin d) (Fin d) ℤ) (s : Finset ℕ)
    (hs : s ⊆ range p) (hsd : s.card ≤ d)
    (hz : ∀ r ∈ s, ∀ j, (p:ℤ) ∣ ∑ i : Fin d, (r:ℤ)^i.val * A i j) :
    p^s.card ∣ A.det.natAbs := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,hst,htp,htd⟩ := exists_subsuperset_card_eq hs hsd (by simpa using hdp : d ≤ (range p).card)
  let e := (t.equivFinOfCardEq htd).symm
  let v (i : Fin d) : ℤ := (e i).val
  let V := vandermonde v
  let I := univ.filter fun i : Fin d => (e i).val ∈ s
  have hI : I.card = s.card := by
    apply card_bij (fun i _ => (e i).val)
    · intro i hi; exact (mem_filter.mp hi).2
    · intro i _ j _ he; exact e.injective (Subtype.ext he)
    · intro r hr
      let i := e.symm ⟨r,hst hr⟩
      have hi : e i = ⟨r,hst hr⟩ := e.apply_symm_apply _
      exact ⟨i, mem_filter.mpr ⟨mem_univ _,by rw [hi]; exact hr⟩, congrArg Subtype.val hi⟩
  have hr : ∀ i ∈ I, ∀ j : Fin d, (p:ℤ) ∣ (V*A) i j := by
    intro i hi j
    exact hz (e i).val (mem_filter.mp hi).2 j
  have div := rows_dvd (V*A) I hr
  rw [hI,det_mul] at div
  have hn : ¬ p ∣ V.det.natAbs := by
    intro h
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd V.det p).mpr (Int.natCast_dvd.mpr h)
    have eq : (V.det : ZMod p) = (vandermonde fun i => ((e i).val : ZMod p)).det := by
      rw [Int.cast_det]; congr 1; ext i j; simp [V,v,vandermonde_apply]
    rw [eq] at z
    apply (det_vandermonde_ne_zero_iff (v:=fun i : Fin d => ((e i).val : ZMod p))).mpr ?_ z
    intro i j he
    apply e.injective
    apply Subtype.ext
    have hi : (e i).val < p := mem_range.mp (htp (e i).property)
    have hj : (e j).val < p := mem_range.mp (htp (e j).property)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using congrArg ZMod.val he
  have dnat : p^s.card ∣ V.det.natAbs*A.det.natAbs := by
    rw [←Int.natAbs_mul,←Int.natCast_dvd]
    simpa only [Nat.cast_pow] using div
  exact ((hp.coprime_iff_not_dvd.mpr hn).pow_left _).dvd_of_dvd_mul_left dnat

end OMA.Charge976
end

section
/- Short evaluation vectors and the size of their integer boxes. -/

namespace OMA.Box975
open Finset
open scoped BigOperators

/-- The largest integer side length whose d-th power fits in q. -/
def radius (d q : ℕ) := Nat.findGreatest (fun n => n^d ≤ q) q

theorem radius_pow {d q : ℕ} (hd : 0 < d) : (radius d q)^d ≤ q :=
  Nat.findGreatest_spec (P := fun n => n^d ≤ q) (Nat.zero_le q) (by simp [hd.ne'])

theorem radius_pos {d q : ℕ} (hq : 0 < q) : 1 ≤ radius d q :=
  Nat.le_findGreatest (P := fun n => n^d ≤ q) hq (by simpa using (show 1 ≤ q from hq))

theorem lt_succ_radius_pow {d q : ℕ} (hd : 0 < d) : q < (radius d q+1)^d := by
  by_contra! he
  have hle : radius d q+1 ≤ q := (le_self_pow₀ (by omega : 1 ≤ radius d q+1) hd.ne').trans he
  have h := Nat.le_findGreatest (P := fun n => n^d ≤ q) hle he
  change radius d q + 1 ≤ radius d q at h
  omega

/-- Two vectors in the positive box have the same value modulo q. Subtract them
to obtain a nonzero vector in the centered box. -/
theorem short_vector {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (r : ℕ) :
    ∃ b : Fin d → ℤ, b ≠ 0 ∧ (∀ i, (b i).natAbs ≤ radius d q) ∧
      (∑ i, (b i : ZMod q) * (r : ZMod q)^i.val) = 0 := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let t := radius d q
  let E (u : Fin d → Fin (t+1)) := ∑ i, ((u i).val : ZMod q) * (r : ZMod q)^i.val
  have hcard : Fintype.card (ZMod q) < Fintype.card (Fin d → Fin (t+1)) := by
    simpa [Fintype.card_pi_const, ZMod.card, t] using lt_succ_radius_pow (q:=q) hd
  obtain ⟨u,v,huv,he⟩ := Fintype.exists_ne_map_eq_of_card_lt E hcard
  let b (i : Fin d) : ℤ := ((u i).val : ℤ) - (v i).val
  refine ⟨b, ?_, ?_, ?_⟩
  · intro hb
    apply huv
    funext i
    apply Fin.ext
    have h := congrFun hb i
    change ((u i).val : ℤ) - (v i).val = 0 at h
    omega
  · intro i
    have hu := (u i).isLt
    have hv := (v i).isLt
    change (((u i).val : ℤ) - (v i).val).natAbs ≤ t
    omega
  · change (∑ i, ((((u i).val : ℤ) - (v i).val : ℤ) : ZMod q) * _) = 0
    simpa only [Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib,
      sub_eq_zero] using he

def box (d t : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Icc (-(t:ℤ)) (t:ℤ))

theorem mem_box {d t : ℕ} {b : Fin d → ℤ} (hb : ∀ i, (b i).natAbs ≤ t) : b ∈ box d t := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have := hb i
  apply mem_Icc.mpr
  omega

theorem card_box {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    (box d (radius d N)).card ≤ 3^d * N := by
  let t := radius d N
  have ht : 1 ≤ t := radius_pos hN
  have hc : (Icc (-(t:ℤ)) (t:ℤ)).card = 2*t+1 := by rw [Int.card_Icc]; omega
  calc
    (box d t).card = (2*t+1)^d := by simp [box, hc]
    _ ≤ (3*t)^d := Nat.pow_le_pow_left (by omega) _
    _ ≤ 3^d*N := by rw [mul_pow]; exact Nat.mul_le_mul_left _ (radius_pow hd)

end OMA.Box975
end

section
/- Small representatives for all residue classes in the polynomial evaluation lattice. -/


namespace OMA.ShortRep976

open Finset Polynomial
open OMA.Companion975

/-- Round in a rational basis to land in its fundamental parallelotope. -/
theorem round {d B : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (nonsing : A.det ≠ 0)
    (small : ∀ i j, (A i j).natAbs ≤ B) (v : Fin d → ℤ) :
    ∃ c : Fin d → ℤ, ∀ i, (v i - ∑ j, A i j * c j).natAbs ≤ d*B := by
  classical
  let M : Matrix (Fin d) (Fin d) ℚ := A.map (Int.castRingHom ℚ)
  have hdet : M.det ≠ 0 := by
    rw [show M.det = (A.det : ℚ) from ((Int.castRingHom ℚ).map_det A).symm]
    exact_mod_cast nonsing
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨q,hq⟩ := hs (fun i => (v i : ℚ))
  let c (i : Fin d) : ℤ := ⌊q i⌋
  refine ⟨c,fun i => ?_⟩
  have he : ((v i - ∑ j, A i j * c j : ℤ) : ℚ) =
      ∑ j, (A i j : ℚ) * (q j - (c j : ℚ)) := by
    have eq := congrFun hq i
    change ∑ j, (A i j : ℚ) * q j = _ at eq
    simp only [Int.cast_sub,Int.cast_sum,Int.cast_mul,mul_sub,Finset.sum_sub_distrib,eq]
  have bound : |((v i - ∑ j, A i j * c j : ℤ) : ℚ)| ≤ (d : ℚ)*B := calc
    _ = |∑ j, (A i j : ℚ) * (q j - (c j : ℚ))| := congrArg abs he
    _ ≤ ∑ j, |(A i j : ℚ) * (q j - (c j : ℚ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, (B : ℚ) := by
      apply sum_le_sum
      intro j _
      have le : (c j : ℚ) ≤ q j := Int.floor_le _
      have lt : q j < (c j : ℚ)+1 := Int.lt_floor_add_one _
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr le)]
      calc
        _ ≤ |(A i j : ℚ)| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ ≤ B := by
          rw [mul_one, ← Int.cast_abs, ← Int.natCast_natAbs]
          exact_mod_cast small i j
    _ = _ := by simp
  rw [← Int.cast_abs, ← Int.natCast_natAbs] at bound
  exact_mod_cast bound

theorem representatives (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree) :
    ∃ C : ℕ, 0 < C ∧ ∀ (q : ℕ) (_ : 0 < q) (r : ZMod q),
      f.eval₂ (Int.castRingHom _) r = 0 → ∀ u : ZMod q,
      ∃ w : Fin f.natDegree → ℤ, (∀ i, (w i).natAbs ≤ C * Box975.radius f.natDegree q) ∧
        vEval r w = u := by
  classical
  let d := f.natDegree
  let K := OMA.Companion975.stepSize f ^ d
  have hstep : 0 < OMA.Companion975.stepSize f := by unfold OMA.Companion975.stepSize; omega
  have hk : 0 < K := pow_pos hstep _
  refine ⟨d*K,Nat.mul_pos hd hk,?_⟩
  intro q hq r hr u
  let : NeZero q := ⟨hq.ne'⟩
  let t := Box975.radius d q
  obtain ⟨b,hb,bnd,zero⟩ := Box975.short_vector hd hq r.val
  have bzero : vEval r b = 0 := by simpa only [vEval,ZMod.natCast_zmod_val] using zero
  let A := matrix f b
  have hbnd (i j : Fin d) : (A i j).natAbs ≤ K*t :=
    (OMA.Companion975.iterate_bound f t b bnd j.val i).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hstep j.isLt.le))
  have colzero (j : Fin d) : vEval r (A.col j) = 0 := by
    change vEval r ((T f)^[j.val] b) = 0
    rw [eval_iterate f r hr,bzero,mul_zero]
  let j₀ : Fin d := ⟨0,hd⟩
  let v (i : Fin d) : ℤ := if j₀ = i then u.val else 0
  have val : vEval r v = u := by simp [vEval,v,ite_mul,j₀]
  obtain ⟨c,roundBound⟩ := round A (det_ne_zero f hf hd.ne' b hb) hbnd v
  let w (i : Fin d) := v i - ∑ j, A i j*c j
  refine ⟨w,fun i => (roundBound i).trans_eq (Nat.mul_assoc ..).symm,?_⟩
  have hz : (∑ i, ∑ j, (c j : ZMod q) * ((A i j : ZMod q)*r^i.val)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    change (∑ j, (c j : ZMod q)*vEval r (A.col j))=0
    simp [colzero]
  unfold vEval at val ⊢
  simp only [w,Int.cast_sub,Int.cast_sum,Int.cast_mul,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [val,sub_eq_self]
  simpa only [mul_left_comm,mul_assoc,mul_comm] using hz

end OMA.ShortRep976
end

section
/- A centered box small enough to survive every residue-dependent shift gives
a lower bound on the number of coefficient vectors evaluating to zero. -/

namespace OMA.Occupancy976
open Finset Polynomial OMA.Companion975

/-- Integer coefficients chosen independently from `1,…,t`. -/
def box (d t : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Icc 1 (t : ℤ))

@[simp] theorem mem_box {d t : ℕ} {v : Fin d → ℤ} :
    v ∈ box d t ↔ ∀ i, 1 ≤ v i ∧ v i ≤ (t : ℤ) := by
  simp only [box,Fintype.mem_piFinset,mem_Icc]

@[simp] theorem card_box (d t : ℕ) : (box d t).card = t^d := by
  simp [box,Fintype.card_piFinset,Int.card_Icc]

theorem nonzero {d t : ℕ} (hd : 0 < d) {v : Fin d → ℤ} (hv : v ∈ box d t) : v ≠ 0 := by
  rintro rfl
  have h := ((mem_box.mp hv) ⟨0,hd⟩).1
  simp at h

/-- The interior box embeds in the zero fiber times the residue ring. -/
theorem shaved {d q : ℕ} (hq : 0 < q) (r : ZMod q) (R t : ℕ)
    (rep : ∀ u : ZMod q, ∃ w : Fin d → ℤ, (∀ i, (w i).natAbs ≤ R) ∧ vEval r w=u) :
    (t-2*R)^d ≤ q*((box d t).filter (fun v => vEval r v=0)).card := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  choose w bound right using rep
  let mid (v : Fin d → ℤ) (i : Fin d) := v i + R
  let res (v : Fin d → ℤ) := vEval r (mid v)
  let adjust (v : Fin d → ℤ) (i : Fin d) := mid v i - w (res v) i
  let target := (box d t).filter (fun v => vEval r v=0)
  have embed : (box d (t-2*R)).card ≤ ((univ : Finset (ZMod q)) ×ˢ target).card := by
    apply card_le_card_of_injOn (fun v => (res v,adjust v))
    · intro v hv
      refine mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_box.mpr ?_,?_⟩⟩
      · intro i
        obtain ⟨vlo,vhi⟩ := mem_box.mp hv i
        have b := bound (res v) i
        change 1 ≤ v i + (R:ℤ) - w (res v) i ∧ v i + (R:ℤ) - w (res v) i ≤ (t:ℤ)
        omega
      · simp only [adjust,vEval,Int.cast_sub,sub_mul,Finset.sum_sub_distrib]
        change res v - vEval r (w (res v)) = 0
        rw [right,sub_self]
    · intro v _ u _ eq
      have e := congrArg Prod.fst eq
      change res v = res u at e
      have h := congrArg Prod.snd eq
      ext i
      have eqi := congrFun h i
      change v i+R-w (res v) i = u i+R-w (res u) i at eqi
      rw [e] at eqi
      omega
  simpa [target,card_product,ZMod.card] using embed

/-- Bernoulli's inequality bounds the loss of at most `2R` layers in each dimension. -/
private theorem boundary {d t R : ℕ} (hd : 0 < d) (ht : 0 < t) :
    1 - (2*d:ℝ)*R/t ≤ (((t-2*R:ℕ):ℝ)/(t:ℝ))^d := by
  have tp : 0 < (t : ℝ) := by exact_mod_cast ht
  by_cases fits : 2*R ≤ t
  · rw [Nat.cast_sub fits,Nat.cast_mul,Nat.cast_ofNat]
    have le : (2:ℝ)*R/t ≤ 1 := (div_le_iff₀ tp).mpr (by exact_mod_cast (by simpa using fits : 2*R ≤ 1*t))
    have b := one_add_mul_le_pow (a := -((2:ℝ)*R/t)) (by linarith : -2 ≤ -((2:ℝ)*R/t)) d
    calc
      _ = 1 + (d:ℝ) * -(2*(R:ℝ)/t) := by ring
      _ ≤ _ := b
      _ = _ := by rw [sub_div,div_self tp.ne']; rfl
  · have hover : (t:ℝ) ≤ 2*R := by exact_mod_cast (by omega : t ≤ 2*R)
    have big : (t:ℝ) ≤ (2*(d:ℝ))*R := by
      have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [mul_nonneg (sub_nonneg.mpr hd') (show (0:ℝ) ≤ R by positivity)]
    exact (sub_nonpos.mpr ((le_div_iff₀ tp).mpr (by simpa using big))).trans (by positivity)

theorem fiber_lower (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree) :
    ∃ C : ℕ, 0 < C ∧ ∀ (q : ℕ) (_ : 0 < q) (r : ZMod q),
      f.eval₂ (Int.castRingHom _) r = 0 → ∀ t : ℕ, 0 < t →
      (1 - (C : ℝ)*Box975.radius f.natDegree q/t)/q ≤
        (((box f.natDegree t).filter (fun v => vEval r v=0)).card : ℝ)/(t:ℝ)^f.natDegree := by
  obtain ⟨K,hK,represent⟩ := ShortRep976.representatives f hf hd
  let d := f.natDegree
  refine ⟨2*d*K,by dsimp [d]; positivity,?_⟩
  intro q hq r hr t ht
  let R := K * Box975.radius d q
  let count := ((box d t).filter (fun v => vEval r v=0)).card
  have card : (((t-2*R:ℕ):ℝ))^d ≤ (q:ℝ)*count := by
    exact_mod_cast shaved hq r R t (represent q hq r hr)
  have qr : (0:ℝ)<q := by exact_mod_cast hq
  have tr : (0:ℝ)<t := by exact_mod_cast ht
  have h := boundary (R:=R) hd ht
  rw [div_pow] at h
  change (1 - ((2*d*K:ℕ):ℝ)*Box975.radius d q/t)/q ≤ (count:ℝ)/t^d
  apply (div_le_iff₀ qr).mpr
  calc
    _ = 1 - (2*(d:ℝ))*(R:ℝ)/t := by simp [R]; ring
    _ ≤ _ := h
    _ ≤ _ := by rw [div_mul_eq_mul_div, mul_comm (count:ℝ) (q:ℝ)]; exact div_le_div_of_nonneg_right card (by positivity)

end OMA.Occupancy976
end

section
namespace OMA.Kummer975

open Polynomial NumberField Ideal
open scoped NumberField

open Filter
open scoped Topology

end OMA.Kummer975
end

section
namespace OMA.Field975

open Polynomial NumberField
open scoped NumberField

private lemma original_isRoot_cast (f : ℤ[X]) (p r : ℕ) :
    (f.map (Int.castRingHom (ZMod p))).IsRoot (r : ZMod p) ↔
      (p : ℤ) ∣ f.eval (r : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.IsRoot, eval_map]
  have he := eval₂_at_apply (p := f) (Int.castRingHom (ZMod p)) (r : ℤ)
  simpa only [Int.coe_castRingHom, Int.cast_natCast] using congrArg (· = 0) he |>.to_iff

theorem root_count (f : ℤ[X]) (p : ℕ) [NeZero p] :
    Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p =
      Nat.card {r : ZMod p // (f.map (Int.castRingHom (ZMod p))).IsRoot r} := by
  classical
  rw [Nat.count_eq_card_fintype]
  have aux (A : Type) (i : Fintype A) : @Fintype.card A i = Nat.card A :=
    (@Nat.card_eq_fintype_card A i).symm
  rw [aux]
  apply Nat.card_congr
  exact {
    toFun := fun r => ⟨r.val, (original_isRoot_cast f p r.val).mpr r.property.2⟩
    invFun := fun r => ⟨r.val.val, ZMod.val_lt _, (original_isRoot_cast f p _).mp
      (by simpa only [ZMod.natCast_zmod_val] using r.property)⟩
    left_inv := fun r => Subtype.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt r.property.1])
    right_inv := fun r => Subtype.ext (ZMod.natCast_zmod_val _)
  }

end OMA.Field975
end

section
/- The ordinary root-counting function is multiplicative by the Chinese remainder
theorem.  Away from the leading coefficient, its prime values are bounded by the degree. -/
namespace OMA.RootsEuler975

open Polynomial

noncomputable def rho (f : ℤ[X]) : ArithmeticFunction ℝ :=
  ⟨fun n => (Nat.count (fun r : ℕ => (n:ℤ) ∣ f.eval (r:ℤ)) n : ℝ), by simp⟩

@[simp] theorem rho_apply (f : ℤ[X]) (n : ℕ) : rho f n =
    (Nat.count (fun r : ℕ => (n:ℤ) ∣ f.eval (r:ℤ)) n : ℝ) := rfl

@[simp] theorem rho_one (f : ℤ[X]) : rho f 1 = 1 := by simp [Nat.count_succ]

private abbrev Root (f : ℤ[X]) (n : ℕ) :=
  {x : ZMod n // (f.map (Int.castRingHom (ZMod n))).IsRoot x}

private lemma commute {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (f : ℤ[X]) (x : R) :
    g ((f.map (Int.castRingHom R)).eval x) = (f.map (Int.castRingHom S)).eval (g x) := by
  simp only [eval_map, hom_eval₂]
  congr 1
  exact Subsingleton.elim ..

private noncomputable def rootsCRT (f : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    Root f (m*n) ≃ Root f m × Root f n := by
  let e := ZMod.chineseRemainder h
  let g : ZMod (m*n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let q : ZMod (m*n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  refine (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change (f.map _).eval x = 0 ↔ (f.map _).eval (g x) = 0 ∧ (f.map _).eval (q x) = 0
  rw [← commute g, ← commute q]
  constructor
  · intro hz; simp [hz]
  · intro hz
    apply e.injective
    rw [map_zero]
    exact Prod.ext hz.1 hz.2

theorem multiplicative (f : ℤ[X]) : (rho f).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨rho_one f, ?_⟩
  intro m n hm hn cop
  let : NeZero m := ⟨hm⟩
  let : NeZero n := ⟨hn⟩
  simp only [rho_apply, Field975.root_count]
  exact_mod_cast (Nat.card_congr (rootsCRT f cop)).trans (Nat.card_prod ..)

theorem prime_le_degree (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (good : (f.leadingCoeff : ZMod p) ≠ 0) : rho f p ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have nz : F ≠ 0 := by
    intro h
    apply good
    simpa only [F,coeff_map,coeff_natDegree,Int.coe_castRingHom,coeff_zero] using
      congrArg (fun q : (ZMod p)[X] => q.coeff f.natDegree) h
  have e : Root f p ≃ ↥F.roots.toFinset :=
    Equiv.subtypeEquivRight fun x => by simp [F,mem_roots nz]
  rw [rho_apply,Field975.root_count]
  have card : Nat.card (Root f p) ≤ f.natDegree := calc
    _ = Nat.card ↥F.roots.toFinset := Nat.card_congr e
    _ = F.roots.toFinset.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ _ := f.card_roots_map_le_natDegree
  exact_mod_cast card

theorem prime_le_degree_of_not_dvd (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (h : ¬ (p:ℤ) ∣ f.leadingCoeff) : rho f p ≤ f.natDegree :=
  prime_le_degree f p hp fun he => h ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp he)

end OMA.RootsEuler975
end

section
/- Charge all simultaneous polynomial-root incidences to a single integer
determinant by summing its prime factorization. -/
namespace OMA.Budget976
open Finset Real Polynomial OMA.Companion975
open scoped Classical

def rows (f : ℤ[X]) (p : ℕ) : Finset ℕ :=
  (range p).filter fun r => (p:ℤ) ∣ f.eval (r:ℤ)

def zeros (f : ℤ[X]) (p : ℕ) (v : Fin f.natDegree → ℤ) : Finset ℕ :=
  (rows f p).filter fun r => vEval (r:ZMod p) v = 0

theorem rows_count (f : ℤ[X]) (p : ℕ) : ((rows f p).card:ℝ) = OMA.RootsEuler975.rho f p := by
  rw [OMA.RootsEuler975.rho_apply,Nat.count_eq_card_filter_range]; rfl

theorem zeros_dvd (f : ℤ[X]) (p : ℕ) (hp : p.Prime) (hdp : f.natDegree ≤ p)
    (hlc : (f.leadingCoeff:ZMod p) ≠ 0) (v : Fin f.natDegree → ℤ) :
    p^(zeros f p v).card ∣ (matrix f v).det.natAbs := by
  apply OMA.Charge976.root_charge hp hdp
  · exact (filter_subset ..).trans (filter_subset ..)
  · apply (card_le_card (show zeros f p v ⊆ rows f p from filter_subset ..)).trans
    have h := OMA.RootsEuler975.prime_le_degree f p hp hlc
    rw [←rows_count] at h
    exact_mod_cast h
  · intro r hr j
    obtain ⟨hm,hz⟩ := mem_filter.mp hr
    exact columns_divisible f p r v (mem_filter.mp hm).2 hz j

theorem factor_sum {D : ℕ} (hne : D ≠ 0) (G : Finset ℕ) (k : ℕ → ℕ)
    (hp : ∀ p ∈ G, p.Prime) (hdiv : ∀ p ∈ G, p^(k p) ∣ D) :
    ∑ p ∈ G, (k p:ℝ)*log p ≤ log D := by
  classical
  let F (p : ℕ) : ℝ := D.factorization p * log p
  have h : ∀ p ∈ G, (k p:ℝ) * log p ≤ F p := by
    intro p hpg
    have e := ((hp p hpg).pow_dvd_iff_le_factorization hne).mp (hdiv p hpg)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast e) (log_natCast_nonneg _)
  apply (sum_le_sum h).trans
  rw [log_nat_eq_sum_factorization]
  change ∑ p ∈ G, F p ≤ ∑ p ∈ D.factorization.support, F p
  calc
    _ ≤ ∑ p ∈ G ∪ D.factorization.support, F p :=
      sum_le_sum_of_subset_of_nonneg subset_union_left
        (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))
    _ = _ := by
      symm
      apply sum_subset subset_union_right
      intro p _ hp
      simp [F,Finsupp.notMem_support_iff.mp hp]

theorem budget {f : ℤ[X]} (hf : Irreducible f) (hd : 0 < f.natDegree) :
    ∃ K : ℕ, 0 < K ∧ ∀ (G : Finset ℕ),
    (∀ p ∈ G, p.Prime ∧ f.natDegree ≤ p ∧ (f.leadingCoeff:ZMod p) ≠ 0) →
    ∀ t : ℕ, 0 < t → ∀ v ∈ OMA.Occupancy976.box f.natDegree t,
      (∑ p ∈ G, ((zeros f p v).card:ℝ)*log p) ≤ log (K * t^f.natDegree : ℕ) := by
  obtain ⟨K,bound⟩ := determinant_bound f
  refine ⟨K+1,by omega,?_⟩
  intro G hG t ht v hv
  have hdet := det_ne_zero f hf hd.ne' v (OMA.Occupancy976.nonzero hd hv)
  have h0 : 0 < (matrix f v).det.natAbs := Int.natAbs_pos.mpr hdet
  have E := factor_sum h0.ne' G (fun p => (zeros f p v).card)
    (fun p hp => (hG p hp).1) (fun p hp =>
      zeros_dvd f p (hG p hp).1 (hG p hp).2.1 (hG p hp).2.2 v)
  have hD := bound t v (fun i => by
    have e := OMA.Occupancy976.mem_box.mp hv i
    omega)
  apply E.trans (log_le_log (by exact_mod_cast h0) ?_)
  exact_mod_cast hD.trans (Nat.mul_le_mul_right _ (Nat.le_succ K))

end OMA.Budget976
end

section
/- Average the norm determinant over a box to bound the weighted number
of roots modulo primes, retaining the additive boundary error. -/
namespace OMA.Average976
open Finset Real Polynomial OMA.Companion975 OMA.Occupancy976 OMA.Budget976
open scoped Classical

theorem switch (f : ℤ[X]) (p : ℕ) (V : Finset (Fin f.natDegree → ℤ)) :
    (∑ r ∈ rows f p, ((V.filter fun v => vEval (r:ZMod p) v=0).card:ℝ)) =
    ∑ v ∈ V, ((zeros f p v).card:ℝ) := by
  classical
  simp only [zeros,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [sum_comm]

theorem averaged (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree) :
    ∃ C K : ℕ, 0 < K ∧ ∀ G : Finset ℕ,
    (∀ p ∈ G, p.Prime ∧ f.natDegree ≤ p ∧ (f.leadingCoeff:ZMod p) ≠ 0) →
    ∀ t : ℕ, 0 < t → (∑ p ∈ G, OMA.RootsEuler975.rho f p*(log p/p)*
      (1-(C:ℝ)*OMA.Box975.radius f.natDegree p/t)) ≤ log (K*t^f.natDegree : ℕ) := by
  obtain ⟨K,hK,upper⟩ := budget hf hd
  obtain ⟨C,_,occ⟩ := fiber_lower f hf hd
  refine ⟨C,K,hK,?_⟩
  intro G hG t ht
  let V := box f.natDegree t
  let T := (t:ℝ)^f.natDegree
  have hT : 0 < T := by dsimp [T]; positivity
  have mass : (V.card : ℝ) = T := by simp [V,T]
  let loss (p : ℕ) := 1-(C:ℝ)*OMA.Box975.radius f.natDegree p/t
  have one (p : ℕ) (hp : p∈G) : OMA.RootsEuler975.rho f p*(log p/p)*loss p ≤
      ∑ v ∈ V, ((zeros f p v).card:ℝ)*log p/T := by
    have pp := (hG p hp).1
    have corr (r : ℕ) (hr : r ∈ rows f p) :
        loss p/p ≤ ((V.filter fun v => vEval (r:ZMod p) v=0).card:ℝ)/T := by
      have e := Polynomial.eval₂_at_apply (p:=f) (Int.castRingHom (ZMod p)) (r:ℤ)
      have he := e.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (mem_filter.mp hr).2)
      apply occ p pp.pos (r:ZMod p) _ t ht
      simpa only [Int.coe_castRingHom,Int.cast_natCast] using he
    have combined := sum_le_sum (s:=rows f p) corr
    simp only [sum_const,nsmul_eq_mul,←Finset.sum_div] at combined
    rw [switch] at combined
    have mul := mul_le_mul_of_nonneg_right combined (log_natCast_nonneg p)
    rw [←rows_count,←Finset.sum_div,←Finset.sum_mul]
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using mul
  calc
    _ ≤ ∑ p ∈ G, ∑ v ∈ V, ((zeros f p v).card:ℝ)*log p/T := sum_le_sum one
    _ = ∑ v ∈ V, (∑ p ∈ G, ((zeros f p v).card:ℝ)*log p)/T := by
      rw [sum_comm]; simp only [sum_div]
    _ ≤ ∑ _v ∈ V, log (K*t^f.natDegree:ℕ)/T := sum_le_sum (fun v hv =>
      div_le_div_of_nonneg_right (upper G hG t ht v hv) hT.le)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,mass]; field_simp

end OMA.Average976
end

section
/- A weighted form of the elementary Chebyshev bound by splitting at half the
current scale. The constant is finite for every strictly positive exponent. -/

open Finset
namespace OMA.Weighted976

theorem estimate (s : ℝ) (hs : 0<s) (hs' : s≤1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      (∑ p ∈ n.primesLE, Real.log p * (p:ℝ)^(s-1)) ≤ A*(n:ℝ)^s := by
  let A := 2*Real.log 4/((2:ℝ)^s-1)
  have hs2 : 1 < (2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hh : 0 ≤ A := div_nonneg (by positivity) (by linarith)
  have hA : A+2*Real.log 4 = A*2^s := by
    have e : A*((2:ℝ)^s-1) = 2*Real.log 4 := div_mul_cancel₀ _ (by linarith)
    linarith
  refine ⟨A,hh,fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hs.ne']
    let P := n.primesLE
    let Q := (n/2).primesLE
    have QP : Q ⊆ P := Nat.primesLE_mono (Nat.div_le_self n 2)
    let x := (n:ℝ)/2
    have xpos : 0 < x := by dsimp [x]; positivity
    have hd : ((n/2:ℕ):ℝ) ≤ x := by simpa [x] using (Nat.cast_div_le (m:=n) (n:=2) (α:=ℝ))
    have low : (∑ p ∈ Q,Real.log p*(p:ℝ)^(s-1)) ≤ A*x^s :=
      (ih (n/2) (Nat.div_lt_self hn (by decide))).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hd hs.le) hh)
    have interval (p : ℕ) (hp : p∈P\Q) : x ≤ p := by
      obtain ⟨hP,hQ⟩ := mem_sdiff.mp hp
      have pp := Nat.prime_of_mem_primesLE hP
      have h : n/2 < p := lt_of_not_ge (fun hz => hQ (Nat.mem_primesLE.mpr ⟨hz,pp⟩))
      dsimp [x]
      apply (div_le_iff₀ (by norm_num)).mpr
      exact_mod_cast (show n ≤ p*2 by omega)
    have w (p : ℕ) (hp : p∈P\Q) : Real.log p*(p:ℝ)^(s-1) ≤ Real.log p*x^(s-1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos xpos (interval p hp) (by linarith))
        (Real.log_natCast_nonneg _)
    have θ : (∑ p ∈ P\Q,Real.log p) ≤ Real.log 4*n := by
      refine (sum_le_sum_of_subset_of_nonneg (sdiff_subset (s:=P) (t:=Q))
        (fun p _ _ => Real.log_natCast_nonneg p)).trans ?_
      rw [show P=n.primesLE from rfl,←Chebyshev.theta_eq_sum_primesLE_log]
      exact Chebyshev.theta_le_log4_mul_x (by positivity)
    have nx : (n:ℝ) = 2*x := by dsimp [x]; ring
    have up : (∑ p ∈ P\Q,Real.log p*(p:ℝ)^(s-1)) ≤ 2*Real.log 4*x^s := by
      refine (sum_le_sum w).trans ?_
      rw [←sum_mul]
      refine (mul_le_mul_of_nonneg_right θ (Real.rpow_nonneg xpos.le _)).trans ?_
      apply le_of_eq
      rw [nx,Real.rpow_sub_one xpos.ne']
      field_simp
    change (∑ p ∈ P,_) ≤ _
    rw [←sum_sdiff QP,nx,Real.mul_rpow (by norm_num) xpos.le,←mul_assoc,←hA,add_mul]
    linarith

end OMA.Weighted976

namespace OMA.Weighted976

theorem radius (d : ℕ) (hd : 0<d) (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ p : ℕ, p.Prime → r p ≤ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      (∑ p ∈ n.primesLE,r p*(Real.log p/(p:ℝ))*OMA.Box975.radius d p) ≤
        K*(n:ℝ)^(1/(d:ℝ)) := by
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  obtain ⟨A,hA,est⟩ := estimate (1/(d:ℝ)) (by positivity)
    (div_le_one_of_le₀ (by exact_mod_cast hd) dp.le)
  refine ⟨U*A,mul_nonneg hU hA,fun n => ?_⟩
  have each (p : ℕ) (hp : p∈n.primesLE) :
      r p*(Real.log p/(p:ℝ))*Box975.radius d p ≤
        U*(Real.log p*(p:ℝ)^(1/(d:ℝ)-1)) := by
    have pp := Nat.prime_of_mem_primesLE hp
    have ppos : (0:ℝ)<p := by exact_mod_cast pp.pos
    have R : (Box975.radius d p:ℝ) ≤ (p:ℝ)^(1/(d:ℝ)) := by
      rw [one_div,Real.le_rpow_inv_iff_of_pos (by positivity) ppos.le dp,Real.rpow_natCast]
      exact_mod_cast Box975.radius_pow (q:=p) hd
    rw [Real.rpow_sub_one ppos.ne']
    calc _ ≤ (U*(Real.log p/p))*(p:ℝ)^(1/(d:ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hr p pp) (by positivity)) R
            (by positivity) (by positivity)
         _ = _ := by ring
  calc _ ≤ _ := sum_le_sum each
       _ = U*(∑ p ∈ n.primesLE,Real.log p*(p:ℝ)^(1/(d:ℝ)-1)) := by rw [mul_sum]
       _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (est n) hU

end OMA.Weighted976
end

section
/- Sum the loss from the boundary of the coefficient box at the scale
`1 + floor(n^(1/d))`. Its total contribution is bounded independently of n. -/

namespace OMA.Scalar976
open Finset Real

theorem mertens (d C K : ℕ) (hd : 0 < d) (hK : 0 < K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 0 < n → ∀ G ⊆ n.primesLE, ∀ ρ : ℕ → ℝ,
      (∀ p ∈ G, ρ p ≤ d) →
      (∀ t : ℕ, 0 < t →
        ∑ p ∈ G, ρ p*(log p/(p:ℝ))*(1-(C:ℝ)*Box975.radius d p/t) ≤ log (K*t^d : ℕ)) →
      ∑ p ∈ G, ρ p*(log p/(p:ℝ)) ≤ log n + B := by
  obtain ⟨A,hA,weight⟩ := Weighted976.radius d hd (fun _ => (d:ℝ)) d
    (by positivity) (fun _ _ => le_rfl)
  let L := K*2^d
  have lp : 0 < L := Nat.mul_pos hK (by positivity)
  refine ⟨log (L:ℝ)+(C:ℝ)*A,add_nonneg (Real.log_natCast_nonneg _) (by positivity),?_⟩
  intro n hn G sub ρ rh avg
  let R := Box975.radius d n
  let t := R+1
  have tp : 0 < t := Nat.succ_pos _
  have tr : (0:ℝ) < t := by exact_mod_cast tp
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have rootle : (n:ℝ)^(1/(d:ℝ)) ≤ t := by
    rw [one_div,Real.rpow_inv_le_iff_of_pos (by positivity) tr.le dp,Real.rpow_natCast]
    exact_mod_cast (Box975.lt_succ_radius_pow (q:=n) hd).le
  let w (p : ℕ) := ρ p * (log p/(p:ℝ))
  have hpartial : (∑ p ∈ G, w p*Box975.radius d p) ≤ A*t := calc
    _ ≤ ∑ p ∈ G, (d:ℝ)*(log p/(p:ℝ))*Box975.radius d p := by
      apply sum_le_sum
      exact fun p hp => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (rh p hp)
        (by positivity)) (by positivity)
    _ ≤ ∑ p ∈ n.primesLE, (d:ℝ)*(log p/(p:ℝ))*Box975.radius d p :=
      sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => by positivity)
    _ ≤ _ := (weight n).trans (mul_le_mul_of_nonneg_left rootle hA)
  have err : (∑ p ∈ G, w p*Box975.radius d p) * ((C:ℝ)/t) ≤ C*A := by
    exact (mul_le_mul_of_nonneg_right hpartial (by positivity : 0 ≤ (C:ℝ)/t)).trans_eq
      (by field_simp)
  have logBound : log (K*t^d : ℕ) ≤ log n + log (L:ℝ) := by
    have rpos : 1 ≤ R := Box975.radius_pos hn
    have sz : t ≤ 2*R := by dsimp only [t]; omega
    have sq : t^d ≤ 2^d*n :=
      (Nat.pow_le_pow_left sz d).trans (by rw [mul_pow]; exact Nat.mul_le_mul_left _ (Box975.radius_pow hd))
    have kl : K*t^d ≤ L*n := (Nat.mul_le_mul_left K sq).trans_eq (Nat.mul_assoc ..).symm
    have H := Real.log_le_log (by exact_mod_cast Nat.mul_pos hK (pow_pos tp d) : 0 < ((K*t^d : ℕ):ℝ)) (by exact_mod_cast kl : ((K*t^d:ℕ):ℝ) ≤ (L*n:ℕ))
    simpa [Nat.cast_mul,Real.log_mul (by exact_mod_cast lp.ne' : (L:ℝ) ≠ 0)
        (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0),add_comm] using H
  have split : (∑ p ∈ G, w p*(1-(C:ℝ)*Box975.radius d p/t)) =
      (∑ p ∈ G, w p) - (∑ p ∈ G,w p*Box975.radius d p)*((C:ℝ)/t) := by
    rw [sum_mul, ←sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  have bound := avg t tp
  change (∑ p ∈ G, w p*(1-(C:ℝ)*Box975.radius d p/t)) ≤ _ at bound
  rw [split] at bound
  change ∑ p ∈ G, w p ≤ _
  linarith

end OMA.Scalar976
end

section
/- The finitely many small primes and primes dividing the leading coefficient
contribute a fixed amount to the logarithmic root sum. -/

open Finset Filter Polynomial Real OMA.RootsEuler975
namespace OMA.Sharp976

theorem close (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree)
    (averaged : ∃ C K : ℕ, 0 < K ∧ ∀ G : Finset ℕ,
      (∀ p ∈ G, p.Prime ∧ f.natDegree ≤ p ∧ (f.leadingCoeff : ZMod p) ≠ 0) →
      ∀ t : ℕ, 0 < t → (∑ p ∈ G, rho f p*(log p/p)*(1-(C:ℝ)*Box975.radius f.natDegree p/t)) ≤
        log (K*t^f.natDegree : ℕ)) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ n.primesLE, rho f p*(log p/(p:ℝ)) ≤ log n + A := by
  classical
  obtain ⟨C,K,hK,avg⟩ := averaged
  obtain ⟨B,_,est⟩ := Scalar976.mertens f.natDegree C K hd hK
  let S := range f.natDegree ∪ f.leadingCoeff.natAbs.primeFactors
  let w (p : ℕ) := rho f p*(log p/(p:ℝ))
  refine ⟨B + ∑ p ∈ S,w p,?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  let G := n.primesLE \ S
  have good (p : ℕ) (hp : p ∈ G) : p.Prime ∧ f.natDegree ≤ p ∧
      (f.leadingCoeff : ZMod p) ≠ 0 := by
    obtain ⟨mem,ns⟩ := mem_sdiff.mp hp
    have prime := Nat.prime_of_mem_primesLE mem
    obtain ⟨big,bad⟩ := not_or.mp (fun h => ns (mem_union.mpr h))
    refine ⟨prime,by simpa using big,fun h => bad ?_⟩
    apply Nat.mem_primeFactors.mpr
    exact ⟨prime,Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h),
      Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero)⟩
  have gBound : (∑ p ∈ G, w p) ≤ log n + B := est n hn G sdiff_subset (rho f)
    (fun p hp => prime_le_degree f p (good p hp).1 (good p hp).2.2) (avg G good)
  have subset : n.primesLE \ G ⊆ S := by
    intro p hp
    obtain ⟨h,hg⟩ := mem_sdiff.mp hp
    exact Classical.byContradiction (fun ns => hg (mem_sdiff.mpr ⟨h,ns⟩))
  have extra : (∑ p ∈ n.primesLE \ G, w p) ≤ ∑ p ∈ S,w p :=
    sum_le_sum_of_subset_of_nonneg subset (fun p _ _ => by dsimp [w,rho_apply]; positivity)
  change (∑ p ∈ n.primesLE,w p) ≤ _
  rw [← sum_sdiff (s₁:=G) (s₂:=n.primesLE) sdiff_subset]
  linarith

end OMA.Sharp976
end

section
/- Integral Bézout and Taylor estimates for counts of polynomial roots modulo prime powers. -/

open Polynomial Finset

namespace OMA.Local975

theorem resultant_nonzero (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    f.resultant f.derivative ≠ 0 := by
  let φ := Int.castRingHom ℚ
  have hφ : Function.Injective φ := Int.cast_injective
  have hirr : Irreducible (f.map φ) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd)).mp hf
  have hcop : IsCoprime (f.map φ) ((f.derivative).map φ) := by
    rw [← Polynomial.derivative_map]
    exact hirr.separable
  have hn := Polynomial.resultant_ne_zero _ _ hcop
  intro he
  apply hn
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map, he, map_zero]

theorem derivative_not_dvd (f : ℤ[X]) (hd : f.natDegree ≠ 0) {p : ℕ} [Fact p.Prime]
    (hn : f.resultant f.derivative ≠ 0) {k : ℕ} {r : ℤ}
    (hk : padicValInt p (f.resultant f.derivative) < k) (hr : (p:ℤ)^k ∣ f.eval r) :
    ¬ (p:ℤ)^(padicValInt p (f.resultant f.derivative)+1) ∣ f.derivative.eval r := by
  let D := f.resultant f.derivative
  let w := padicValInt p D
  obtain ⟨a,b,_,_,hab⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl le_rfl (Or.inl hd)
  have hev : f.eval r * a.eval r + f.derivative.eval r * b.eval r = D := by
    simpa [D] using congrArg (fun P : ℤ[X] => P.eval r) hab
  intro hder
  have hroot : (p:ℤ)^(w+1) ∣ f.eval r := dvd_trans (pow_dvd_pow _ hk) hr
  have hD : (p:ℤ)^(w+1) ∣ D := hev ▸ dvd_add (dvd_mul_of_dvd_left hroot _) (dvd_mul_of_dvd_left hder _)
  have hbad := ((padicValInt_dvd_iff (p:=p) _ _).mp hD).resolve_left hn
  change w+1 ≤ w at hbad
  omega

/-- In a fixed residue class modulo p^(w+1), two roots agree modulo p^(k-w).
Only the bound on the valuation of the derivative at the first root is needed. -/
theorem root_separation (f : ℤ[X]) {p : ℕ} [Fact p.Prime] {k w : ℕ} {r s : ℤ}
    (hr : (p:ℤ)^k ∣ f.eval r) (hs : (p:ℤ)^k ∣ f.eval s)
    (hder : ¬ (p:ℤ)^(w+1) ∣ f.derivative.eval r)
    (hclose : (p:ℤ)^(w+1) ∣ s-r) : (p:ℤ)^(k-w) ∣ s-r := by
  by_cases heq : s-r=0
  · simp [heq]
  obtain ⟨c,hc⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add r (s-r)
  rw [add_sub_cancel] at hc
  let b := f.derivative.eval r + c*(s-r)
  have hprod : (p:ℤ)^k ∣ (s-r)*b := by
    rw [show (s-r)*b = f.eval s-f.eval r by dsimp [b]; linarith only [hc]]
    exact dvd_sub hs hr
  have hnd : ¬ (p:ℤ)^(w+1) ∣ b := by
    intro hb
    apply hder
    have h := dvd_sub hb (dvd_mul_of_dvd_right hclose c)
    simpa [b] using h
  have hb : b≠0 := fun e => hnd (by rw [e]; exact dvd_zero _)
  have hval : padicValInt p b ≤ w := by
    by_contra! h
    exact hnd ((padicValInt_dvd_iff _ _).mpr (Or.inr h))
  have hle := ((padicValInt_dvd_iff _ _).mp hprod).resolve_left (mul_ne_zero heq hb)
  rw [padicValInt.mul heq hb] at hle
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))

theorem count (f : ℤ[X]) (hd : f.natDegree ≠ 0) (hD : f.resultant f.derivative ≠ 0)
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    Nat.count (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ)) (p^k) ≤
      p^(2*padicValInt p (f.resultant f.derivative)+1) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let w := padicValInt p (f.resultant f.derivative)
  change _ ≤ p^(2*w+1)
  by_cases hk : k≤2*w+1
  · exact (Nat.count_le _).trans (Nat.pow_le_pow_right hp.pos hk)
  let a := p^(w+1)
  let b := p^(k-w)
  let S := (range (p^k)).filter (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ))
  let key (r : ℕ) := (r%a, r/b)
  have hpa : 0<a := pow_pos hp.pos _
  have hpb : 0<b := pow_pos hp.pos _
  have hb : p^k = p^w*b := by dsimp [b]; rw [← pow_add]; congr 1; omega
  rw [Nat.count_eq_card_filter_range]
  change S.card ≤ _
  suffices S.card ≤ ((range a) ×ˢ (range (p^w))).card by
    simpa [a,Finset.card_product,← pow_add,show w+1+w=2*w+1 by omega] using this
  apply Finset.card_le_card_of_injOn key
  · intro r hr
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt r hpa), Finset.mem_range.mpr ?_⟩
    apply (Nat.div_lt_iff_lt_mul hpb).mpr
    rw [← hb]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  · intro r hr s hs he
    have hr' : (p:ℤ)^k ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
    have hs' : (p:ℤ)^k ∣ f.eval (s:ℤ) := by simpa using (Finset.mem_filter.mp hs).2
    have hrem : r ≡ s [MOD a] := congrArg Prod.fst he
    have hquot : r/b = s/b := congrArg Prod.snd he
    have hcl : (p:ℤ)^(w+1) ∣ (s:ℤ)-r := by
      simpa [a] using (Int.natCast_modEq_iff.mpr hrem).dvd
    have hsep := root_separation f hr' hs'
      (derivative_not_dvd f hd hD (show w<k by omega) hr') hcl
    change (p:ℤ)^(k-w) ∣ (s:ℤ)-r at hsep
    have hfin : r ≡ s [MOD b] := by
      apply Int.natCast_modEq_iff.mp
      exact Int.modEq_of_dvd (by simpa only [b,Nat.cast_pow] using hsep)
    have e : r%b=s%b := hfin
    calc r = r%b+b*(r/b) := (Nat.mod_add_div _ _).symm
         _ = s := by rw [e,hquot,Nat.mod_add_div]

theorem bounded (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ k : ℕ,
      Nat.count (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ)) (p^k) ≤ B :=
  ⟨_, count f hd (resultant_nonzero f hf hd) p hp⟩

/-- A simple root modulo p^k, k positive, lifts to the next power. The new
base-p digit is solved in the field Z/pZ. -/
theorem lift (f : ℤ[X]) {p k r : ℕ} [hp : Fact p.Prime] (hk : 0<k)
    (hrange : r < p^k) (hr : (p:ℤ)^k ∣ f.eval (r:ℤ))
    (hsimple : ¬ (p:ℤ) ∣ f.derivative.eval (r:ℤ)) :
    ∃ s : ℕ, s < p^(k+1) ∧ (p:ℤ)^(k+1) ∣ f.eval (s:ℤ) ∧ s % (p^k) = r := by
  obtain ⟨u,hu⟩ := hr
  let d := f.derivative.eval (r:ℤ)
  have hd : (d : ZMod p) ≠ 0 := fun e => hsimple ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e)
  let t : ZMod p := -(u:ZMod p)/(d:ZMod p)
  have h0 : (u:ZMod p) + (d:ZMod p)*t = 0 := by
    dsimp [t]; field_simp; ring
  have hdiv : (p:ℤ) ∣ u+d*(t.val:ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using h0
  let s := r+p^k*t.val
  have hpk : 0<p^k := pow_pos hp.out.pos k
  refine ⟨s, ?_, ?_, ?_⟩
  · have ht := t.val_lt
    have h : p^k*(t.val+1) ≤ p^k*p := Nat.mul_le_mul_left _ ht
    dsimp [s]; rw [pow_succ]; nlinarith
  · obtain ⟨c,hc⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add (r:ℤ) ((p:ℤ)^k*t.val)
    have hs : (s:ℤ) = (r:ℤ)+(p:ℤ)^k*t.val := by simp [s]
    rw [hs, ← hc, hu]
    change (p:ℤ)^(k+1) ∣ c*((p:ℤ)^k*t.val)^2+d*((p:ℤ)^k*t.val)+(p:ℤ)^k*u
    have hv : (p:ℤ) ∣ (p:ℤ)^k := dvd_pow_self _ hk.ne'
    obtain ⟨v,hv'⟩ := hdiv
    obtain ⟨w,hw⟩ := hv
    refine ⟨v + c*w*(t.val:ℤ)^2, ?_⟩
    calc c*((p:ℤ)^k*t.val)^2 + d*((p:ℤ)^k*t.val) + (p:ℤ)^k*u =
            (p:ℤ)^k * ((u+d*t.val) + c*(p:ℤ)^k*(t.val:ℤ)^2) := by ring
         _ = _ := by simp only [hv',pow_succ (p:ℤ) k,hw]; ring
  · simp [s,Nat.add_mod, Nat.mod_eq_of_lt hrange, Nat.mul_mod_right]

private noncomputable def residues (f : ℤ[X]) (q : ℕ) : Finset ℕ :=
  (range q).filter fun r : ℕ => (q:ℤ) ∣ f.eval (r:ℤ)

theorem hensel (f : ℤ[X]) (hd : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime)
    (hgood : ¬ (p:ℤ) ∣ f.resultant f.derivative) (k : ℕ) (hk : 0 < k) :
    Nat.count (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ)) (p^k) =
      Nat.count (fun r : ℕ => (p:ℤ) ∣ f.eval (r:ℤ)) p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hD : f.resultant f.derivative ≠ 0 := fun e => hgood (e ▸ dvd_zero _)
  have hw : padicValInt p (f.resultant f.derivative) = 0 := by
    by_contra! e
    apply hgood
    have h := (padicValInt_dvd_iff (p:=p) 1 (f.resultant f.derivative)).mpr (Or.inr (by omega))
    simpa using h
  have simple {m r : ℕ} (hm : 0 < m) (hr : (p:ℤ)^m ∣ f.eval (r:ℤ)) :
      ¬ (p:ℤ) ∣ f.derivative.eval (r:ℤ) := by
    simpa only [hw, zero_add, pow_one] using derivative_not_dvd f hd hD (hw ▸ hm) hr
  have step (m : ℕ) (hm : 0 < m) : (residues f (p^(m+1))).card = (residues f (p^m)).card := by
    let big := residues f (p^(m+1))
    let small := residues f (p^m)
    let red (r : ℕ) := r % p^m
    have red_mem (r : ℕ) (hr : r∈big) : red r∈small := by
      have hmpos : 0<p^m := pow_pos hp.pos _
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hmpos), ?_⟩
      have hr' : (p:ℤ)^(m+1) ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
      have hroot : (p:ℤ)^m ∣ f.eval (r:ℤ) := (pow_dvd_pow _ (Nat.le_succ m)).trans hr'
      have hmod : red r ≡ r [MOD p^m] := Nat.mod_modEq _ _
      have hh := (Int.natCast_modEq_iff.mpr hmod.symm).dvd.trans
        (Polynomial.sub_dvd_eval_sub (red r:ℤ) (r:ℤ) f)
      have hroot' : ((p^m:ℕ):ℤ) ∣ f.eval (r:ℤ) := by simpa only [Nat.cast_pow] using hroot
      simpa using dvd_add hh hroot'
    have eq : big.image red = small := by
      apply Finset.Subset.antisymm
      · exact Finset.image_subset_iff.mpr red_mem
      · intro r hr
        have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
        have hr' : (p:ℤ)^m ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
        obtain ⟨s,hs,hs',hsr⟩ := lift f hm hrange hr' (simple hm hr')
        exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs,
          by simpa only [Nat.cast_pow] using hs'⟩,hsr⟩
    have inj : Set.InjOn red big := by
      intro r hr s hs he
      have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hsrange := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      have hr' : (p:ℤ)^(m+1) ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
      have hs' : (p:ℤ)^(m+1) ∣ f.eval (s:ℤ) := by simpa using (Finset.mem_filter.mp hs).2
      have hmod : r ≡ s [MOD p^m] := he
      have hpmod : r ≡ s [MOD p] := hmod.of_dvd (dvd_pow_self p hm.ne')
      have hcl := (Int.natCast_modEq_iff.mpr hpmod).dvd
      have hsep := root_separation (w:=0) f hr' hs'
        (by simpa using simple (Nat.succ_pos m) hr') (by simpa using hcl)
      have hstrong : r ≡ s [MOD p^(m+1)] :=
        Int.natCast_modEq_iff.mp (Int.modEq_of_dvd (by simpa only [Nat.cast_pow,Nat.sub_zero] using hsep))
      exact hstrong.eq_of_lt_of_lt hrange hsrange
    calc big.card = (big.image red).card := (Finset.card_image_of_injOn inj).symm
         _ = small.card := congrArg Finset.card eq
  rw [Nat.count_eq_card_filter_range,Nat.count_eq_card_filter_range]
  change (residues f (p^k)).card = (residues f p).card
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m hm ih => exact (step m hm).trans ih

end OMA.Local975
end

section
namespace OMA.IdealEuler975

open Finset NumberField Ideal ArithmeticFunction
open scoped NumberField Classical

noncomputable def atom (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ n = d then 1 else 0, by simp⟩

lemma atom_mul (b : ArithmeticFunction ℝ) {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (atom d * b) n = if d ∣ n then b (n / d) else 0 := by
  classical
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal fun i j => atom d i * b j]
  have h (i : ℕ) : atom d i * b (n / i) = if i = d then b (n / d) else 0 := by
    by_cases hi : i = d <;> simp [atom, hi, hd.ne']
  simp_rw [h]
  simp [Nat.mem_divisors, hn.ne']

variable (K : Type*) [Field K] [NumberField K]

noncomputable def fiber (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq n).toFinset

lemma mem_fiber {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ fiber K n ↔ I.absNorm = n := by
  simp [fiber]

noncomputable def avoid (S : Finset (Ideal (𝓞 K))) (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (fiber K n).filter fun I => ∀ P ∈ S, ¬P ∣ I

lemma mem_avoid {n : ℕ} {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))} :
    I ∈ avoid K S n ↔ I.absNorm = n ∧ ∀ P ∈ S, ¬P ∣ I := by
  simp [avoid, mem_fiber]

noncomputable def countAvoid (S : Finset (Ideal (𝓞 K))) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (avoid K S n).card, by simp⟩

private lemma countAvoid_apply (S : Finset (Ideal (𝓞 K))) (n : ℕ) :
    countAvoid K S n = if n = 0 then (0 : ℝ) else ((avoid K S n).card : ℝ) := rfl

noncomputable abbrev a := countAvoid K ∅

private lemma norm_pos {P : Ideal (𝓞 K)} (hP : Prime P) : 0 < P.absNorm :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)

private lemma insert_count {S : Finset (Ideal (𝓞 K))} {P : Ideal (𝓞 K)} (hP : Prime P)
    (hPS : P ∉ S) (hs : ∀ Q ∈ S, Prime Q) :
    countAvoid K (insert P S) = (1 - atom P.absNorm) * countAvoid K S := by
  classical
  ext n
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · simp
  rw [sub_mul, one_mul]
  change (countAvoid K (insert P S)) n = (countAvoid K S) n - (atom P.absNorm * countAvoid K S) n
  rw [atom_mul _ (norm_pos K hP) hn]
  have split : avoid K (insert P S) n = (avoid K S n).filter (fun I => ¬ P ∣ I) := by
    ext I; simp [mem_avoid]; tauto
  simp only [countAvoid_apply, if_neg hn.ne', split]
  by_cases hd : P.absNorm ∣ n
  · have hdiv : 0 < n / P.absNorm := Nat.div_pos (Nat.le_of_dvd hn hd) (norm_pos K hP)
    simp only [if_pos hd, if_neg hdiv.ne']
    have bij : (avoid K S (n / P.absNorm)).card =
        ((avoid K S n).filter (fun I => P ∣ I)).card := by
      apply card_nbij (fun J => P * J)
      · intro J hJ
        obtain ⟨hjn, hjs⟩ := (mem_avoid K).mp hJ
        apply mem_filter.mpr
        refine ⟨(mem_avoid K).mpr ⟨by rw [map_mul, hjn, Nat.mul_div_cancel' hd], ?_⟩, dvd_mul_right _ _⟩
        intro Q hQ h
        rcases (hs Q hQ).dvd_or_dvd h with h | h
        · exact hPS (associated_iff_eq.mp ((hs Q hQ).irreducible.associated_of_dvd hP.irreducible h) ▸ hQ)
        · exact hjs Q hQ h
      · exact fun J _ J' _ hh => mul_left_cancel₀ hP.ne_zero hh
      · intro I hI
        obtain ⟨hI, J, rfl⟩ := mem_filter.mp hI
        obtain ⟨hjn, hjs⟩ := (mem_avoid K).mp hI
        refine ⟨J, (mem_avoid K).mpr ?_, rfl⟩
        refine ⟨?_, fun Q hQ h => hjs Q hQ (dvd_mul_of_dvd_right h P)⟩
        rw [← hjn, map_mul, Nat.mul_div_cancel_left _ (norm_pos K hP)]
    have cnt := (avoid K S n).card_filter_add_card_filter_not (fun I => P ∣ I)
    rw [← bij] at cnt
    linarith only [show (((avoid K S (n / P.absNorm)).card : ℝ) +
      (((avoid K S n).filter fun I => ¬P ∣ I).card : ℝ)) = (avoid K S n).card by exact_mod_cast cnt]
  · simp only [if_neg hd, sub_zero]
    norm_cast
    congr 1
    apply filter_true_of_mem
    intro I hI h
    apply hd
    rw [← ((mem_avoid K).mp hI).1]
    exact map_dvd Ideal.absNorm h

noncomputable def euler (S : Finset (Ideal (𝓞 K))) : ArithmeticFunction ℝ :=
  ∏ P ∈ S, (1 - atom P.absNorm)

private lemma sieve (S : Finset (Ideal (𝓞 K))) (hs : ∀ P ∈ S, Prime P) :
    euler K S * a K = countAvoid K S := by
  induction S using Finset.induction_on with
  | empty => simp [euler, a]
  | @insert P S hp ih =>
    rw [insert_count K (hs P (mem_insert_self ..)) hp (fun Q hQ => hs Q (mem_insert_of_mem hQ))]
    rw [← ih (fun Q hQ => hs Q (mem_insert_of_mem hQ)), ← mul_assoc]
    simp [euler, hp]

noncomputable def smallPrimes (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le n).toFinset.filter Prime

lemma mem_small {P : Ideal (𝓞 K)} {n : ℕ} :
    P ∈ smallPrimes K n ↔ P.absNorm ≤ n ∧ Prime P := by simp [smallPrimes]

private lemma no_large_change (S T : Finset (Ideal (𝓞 K))) (hST : S ⊆ T) {n : ℕ} (hn : 0 < n)
    (exclude : ∀ P ∈ T \ S, Prime P ∧ ¬P.absNorm ∣ n) :
    (euler K T) n = (euler K S) n := by
  have main (U : Finset (Ideal (𝓞 K))) (hU : ∀ P ∈ U, Prime P ∧ ¬P.absNorm ∣ n) :
      (euler K U * euler K S) n = euler K S n := by
    induction U using Finset.induction_on with
    | empty => simp [euler]
    | @insert P U hp ih =>
      have hP := hU P (mem_insert_self ..)
      rw [show euler K (insert P U) = (1 - atom P.absNorm) * euler K U by simp [euler, hp],
        mul_assoc, sub_mul, one_mul]
      change (euler K U * euler K S) n - (atom P.absNorm * _) n = _
      rw [atom_mul _ (norm_pos K hP.1) hn, if_neg hP.2, sub_zero]
      exact ih (fun Q hQ => hU Q (mem_insert_of_mem hQ))
  rw [← show euler K (T \ S) * euler K S = euler K T from Finset.prod_sdiff hST]
  exact main _ exclude

noncomputable def mu : ArithmeticFunction ℝ :=
  ⟨fun n => euler K (smallPrimes K n) n, by simp⟩

lemma mu_eq {n N : ℕ} (hn : n ≤ N) :
    (mu K) n = euler K (smallPrimes K N) n := by
  rcases Nat.eq_zero_or_pos n with rfl|hn'
  · simp
  symm
  exact no_large_change K _ _ (fun P hP => (mem_small K).mpr
    ⟨((mem_small K).mp hP).1.trans hn, ((mem_small K).mp hP).2⟩) hn' (by
      intro P hP
      obtain ⟨hPN,hnP⟩ := mem_sdiff.mp hP
      have hp := ((mem_small K).mp hPN).2
      exact ⟨hp, fun h => hnP ((mem_small K).mpr ⟨Nat.le_of_dvd hn' h, hp⟩)⟩)

lemma inverse : a K * mu K = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · simp
  rw [mul_comm]
  have h : (mu K * a K) n = (euler K (smallPrimes K n) * a K) n := by
    simp only [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mu_eq K (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hx))]
  rw [h, sieve K _ (fun P hP => ((mem_small K).mp hP).2), countAvoid_apply, if_neg hn.ne',
    ArithmeticFunction.one_apply]
  by_cases h1 : n = 1
  · subst n
    have hsingleton : avoid K (smallPrimes K 1) 1 = {1} := by
      ext I
      rw [mem_avoid, mem_singleton, Ideal.absNorm_eq_one_iff, Ideal.one_eq_top]
      refine ⟨fun h => h.1, ?_⟩
      rintro rfl
      exact ⟨rfl, fun P hP => Ideal.one_eq_top (R:=𝓞 K) ▸ ((mem_small K).mp hP).2.not_dvd_one⟩
    simp [hsingleton]
  · rw [if_neg h1]
    suffices avoid K (smallPrimes K n) n = ∅ by simp [this]
    apply eq_empty_iff_forall_notMem.mpr
    intro I hI
    obtain ⟨he, hnop⟩ := (mem_avoid K).mp hI
    have hnunit : ¬IsUnit I := fun h => h1 (he.symm.trans (Ideal.absNorm_eq_one_iff.mpr
      (Ideal.isUnit_iff.mp h)))
    have hne : I ≠ 0 := fun e => hn.ne' (by simp [← he,e])
    obtain ⟨P, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnunit hne
    exact hnop P ((mem_small K).mpr ⟨Nat.le_of_dvd hn (he ▸ map_dvd Ideal.absNorm dvd),
      UniqueFactorizationMonoid.irreducible_iff_prime.mp irr⟩) dvd

private lemma prime_dvd_factor {p n j : ℕ} (hp : p.Prime) (hn : n ≠ 1) (h : n ∣ p^j) : p ∣ n := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp h
  exact dvd_pow_self _ (by intro hk; simp [hk] at hn)

private lemma factor_mult {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    (1 - atom (p^e)).IsMultiplicative := by
  let t := p^e
  have ht : 1 < t := one_lt_pow₀ hp.one_lt he.ne'
  have hval (k : ℕ) : (1 - atom t : ArithmeticFunction ℝ) k =
      (if k = 1 then 1 else 0) - (if k = t then 1 else 0) := by
    change (if k = 1 then (1:ℝ) else 0) - (if k ≠ 0 ∧ k = t then 1 else 0) = _
    by_cases h : k = t <;> simp [h, Nat.ne_zero_of_lt (zero_lt_one.trans ht)]
  have hone : (1 - atom t : ArithmeticFunction ℝ) 1 = 1 := by simp [hval, ht.ne]
  refine ⟨hone, ?_⟩
  intro m n hmn
  change (1 - atom t : ArithmeticFunction ℝ) (m*n) =
    (1 - atom t : ArithmeticFunction ℝ) m * (1 - atom t : ArithmeticFunction ℝ) n
  by_cases hm : m = 1
  · simp [hm, hone]
  by_cases hn : n = 1
  · simp [hn, hone]
  have nc : ¬(p ∣ m ∧ p ∣ n) := fun h => hp.not_dvd_one (hmn ▸ Nat.dvd_gcd h.1 h.2)
  have ne : m*n ≠ t := by
    intro eq
    exact nc ⟨prime_dvd_factor hp hm (eq ▸ dvd_mul_right m n),
      prime_dvd_factor hp hn (eq ▸ dvd_mul_left n m)⟩
  have n1 : m*n ≠ 1 := fun h => hm (Nat.dvd_one.mp (h ▸ dvd_mul_right m n))
  change (1 - atom t : ArithmeticFunction ℝ) (m*n) =
    (1 - atom t : ArithmeticFunction ℝ) m * (1 - atom t : ArithmeticFunction ℝ) n
  simp only [hval, if_neg ne, if_neg n1, if_neg hm, if_neg hn, sub_self, zero_sub, neg_mul_neg]
  by_cases h : m = t
  · have hn' : n ≠ t := fun h' => nc ⟨h ▸ dvd_pow_self _ he.ne', h' ▸ dvd_pow_self _ he.ne'⟩
    simp [hn']
  · simp [h]

lemma multiplicative : (mu K).IsMultiplicative := by
  have fm (N : ℕ) : (euler K (smallPrimes K N)).IsMultiplicative := by
    apply ArithmeticFunction.isMultiplicative_finsetProd
    intro P hP
    have hp := ((mem_small K).mp hP).2
    have : P.IsPrime := Ideal.isPrime_of_prime hp
    have : P.IsMaximal := this.isMaximal hp.ne_zero
    obtain ⟨p, d, hd, _, hprime, eq⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [eq]
    exact factor_mult hprime hd
  refine ⟨(mu_eq K (le_refl 1)).trans (fm 1).1, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [mu_eq K (le_refl (m*n)), mu_eq K (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hn)),
    mu_eq K (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm))]
  exact (fm (m*n)).2 hmn

open Polynomial

end OMA.IdealEuler975
end

section
/- Uniform bounds for the prime-power coefficients of the root-counting function
and its correction by the inverse ideal-counting function. -/
namespace OMA.CoeffBound975
open Polynomial Finset ArithmeticFunction
open RootsEuler975

theorem roots_uniform (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime → ∀ j : ℕ, |rho f (p^j)| ≤ B := by
  classical
  let D := (f.resultant f.derivative).natAbs * f.leadingCoeff.natAbs
  have Dpos : 0 < D := Nat.mul_pos (Int.natAbs_pos.mpr (Local975.resultant_nonzero f hf hd))
    (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero))
  let b (p : ℕ) := if h : p.Prime then (Local975.bounded f hf hd p h).choose else 0
  have hb (p : ℕ) (hp : p.Prime) (j : ℕ) : rho f (p^j) ≤ b p := by
    dsimp only [b]
    rw [dif_pos hp,rho_apply]
    exact_mod_cast (Local975.bounded f hf hd p hp).choose_spec j
  let C := f.natDegree + 1 + ∑ p ∈ D.primeFactors, b p
  refine ⟨C, by positivity, fun p hp j => ?_⟩
  have pos : 0 ≤ rho f (p^j) := Nat.cast_nonneg _
  rw [abs_of_nonneg pos]
  by_cases bad : p ∣ D
  · have sub := single_le_sum (fun q (_ : q ∈ D.primeFactors) => Nat.zero_le (b q))
      (Nat.mem_primeFactors.mpr ⟨hp,bad,Dpos.ne'⟩)
    exact (hb p hp j).trans (by exact_mod_cast (show b p ≤ C by dsimp [C]; omega))
  · have hR : ¬(p:ℤ) ∣ f.resultant f.derivative :=
      fun h => bad (dvd_mul_of_dvd_left (Int.natAbs_dvd_natAbs.mpr h) _)
    have hL : ¬(p:ℤ) ∣ f.leadingCoeff :=
      fun h => bad (dvd_mul_of_dvd_right (Int.natAbs_dvd_natAbs.mpr h) _)
    cases j with
    | zero =>
      rw [pow_zero,rho_one]
      exact_mod_cast (show 1 ≤ C by dsimp [C]; omega)
    | succ j =>
      have eq : rho f (p^(j+1)) = rho f p := by
        simp only [rho_apply]
        rw [Local975.hensel f hd p hp hR _ (by omega)]
      rw [eq]
      exact (prime_le_degree_of_not_dvd f p hp hL).trans
        (by exact_mod_cast (show f.natDegree ≤ C by dsimp [C]; omega))

open scoped NumberField

end OMA.CoeffBound975
end

section
/- The logarithm of the small-prime part of the polynomial values, by counting
roots in residue classes modulo prime powers. -/

namespace OMA.Small976
open Finset Polynomial Filter RootsEuler975

theorem log_small (m B : ℕ) :
    Real.log (Split976.small B m) =
      ∑ p ∈ Nat.primesLE B, (m.factorization p : ℝ) * Real.log p := by
  let l := m.primeFactorsList.filter (· ≤ B)
  have hsub : l.toFinset ⊆ Nat.primesLE B := by
    intro a ha
    obtain ⟨hp,hB⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
    exact Nat.mem_primesLE.mpr ⟨of_decide_eq_true hB,Nat.prime_of_mem_primeFactorsList hp⟩
  change Real.log (l.prod : ℝ) = _
  rw [prod_list_count_of_subset l _ hsub,Nat.cast_prod,Real.log_prod]
  · apply sum_congr rfl
    intro p hp
    have hple := Nat.le_of_mem_primesLE hp
    have hcount : l.count p = m.factorization p :=
      (List.count_filter (p := fun t : ℕ => decide (t ≤ B)) (decide_eq_true hple)).trans
        Nat.primeFactorsList_count_eq
    simp [hcount,Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero

/-- Separate an index into its quotient and its root residue modulo q. -/
theorem count_mod (f : ℤ[X]) (n q : ℕ) (hq : 0 < q) :
    (((Icc 1 n).filter (fun k : ℕ => (q:ℤ) ∣ f.eval (k:ℤ))).card : ℝ) ≤
      (n/(q:ℝ)+1) * rho f q := by
  let R := (range q).filter (fun k : ℕ => (q:ℤ) ∣ f.eval (k:ℤ))
  let T := (Icc 1 n).filter (fun k : ℕ => (q:ℤ) ∣ f.eval (k:ℤ))
  have sub : T.card ≤ ((range (n/q+1)) ×ˢ R).card := by
    apply card_le_card_of_injOn (fun k : ℕ => (k/q,k%q))
    · intro k hk
      obtain ⟨hk,hf⟩ := mem_filter.mp hk
      refine mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (mem_Icc.mp hk).2)),mem_filter.mpr ⟨mem_range.mpr
          (Nat.mod_lt _ hq),?_⟩⟩
      have hm : k % q ≡ k [MOD q] := Nat.mod_modEq _ _
      have diff := dvd_trans (Int.natCast_modEq_iff.mpr hm).dvd
        (sub_dvd_eval_sub (k:ℤ) ((k%q:ℕ):ℤ) f)
      simpa using dvd_sub hf diff
    · intro a _ b _ he
      have d := congrArg Prod.fst he
      have r := congrArg Prod.snd he
      dsimp at d r
      simpa [d,r] using (Nat.mod_add_div a q).symm.trans
        (show a%q + q*(a/q) = b from by rw [d,r,Nat.mod_add_div])
  rw [card_product,card_range] at sub
  change (T.card:ℝ) ≤ _
  rw [rho_apply,Nat.count_eq_card_filter_range]
  calc _ ≤ ((n/q : ℕ)+1 : ℝ)*R.card := by exact_mod_cast sub
       _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add_left Nat.cast_div_le _) (Nat.cast_nonneg _)

/-- Total p-adic valuation, summing over positive exponents before summing over k. -/
theorem prime_weight (f : ℤ[X]) (p n H : ℕ) (hp : p.Prime) (hH : 0 < H)
    (hsize : ∀ k ∈ Icc 1 n, 0 < (f.eval (k:ℤ)).natAbs ∧ (f.eval (k:ℤ)).natAbs ≤ H)
    (b : ℝ) (hb : 0 ≤ b) (roots : ∀ j : ℕ, 0 < j → rho f (p^j) ≤ b) :
    (∑ k ∈ Icc 1 n, ((f.eval (k:ℤ)).natAbs.factorization p : ℝ)) * Real.log p ≤
      b * (n*Real.log p/((p:ℝ)-1)+Real.log H) := by
  let J := Nat.log p H
  have expcount (k : ℕ) (hk : k ∈ Icc 1 n) :
      ((f.eval (k:ℤ)).natAbs.factorization p : ℝ) =
        ∑ j ∈ Icc 1 J, if ((p^j:ℕ):ℤ) ∣ f.eval (k:ℤ) then (1:ℝ) else 0 := by
    have Hlt := (hsize k hk).2.trans_lt (Nat.lt_pow_succ_log_self hp.one_lt H)
    have v := Nat.factorization_eq_card_pow_dvd_of_lt hp (hsize k hk).1 Hlt
    have sets : (Ico 1 (J+1)).filter (fun j => p^j ∣ (f.eval (k:ℤ)).natAbs) =
        (Icc 1 J).filter (fun j => ((p^j:ℕ):ℤ) ∣ f.eval (k:ℤ)) := by
      ext j
      simp only [mem_filter,mem_Ico,mem_Icc,Nat.lt_succ_iff]
      rw [←Int.natAbs_dvd_natAbs,Int.natAbs_natCast]
    rw [v,sets,←sum_filter]
    simp
  have block (j : ℕ) (hj : j ∈ Icc 1 J) :
      (∑ k ∈ Icc 1 n, if ((p^j:ℕ):ℤ) ∣ f.eval (k:ℤ) then (1:ℝ) else 0) ≤
        (n/(p:ℝ)^j+1)*b := by
    rw [←sum_filter]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    have h := count_mod f n (p^j) (pow_pos hp.pos _)
    calc _ ≤ (n/((p^j:ℕ):ℝ)+1)*rho f (p^j) := h
         _ = (n/(p:ℝ)^j+1)*rho f (p^j) := by rw [Nat.cast_pow]
         _ ≤ _ := by gcongr; exact roots j (mem_Icc.mp hj).1
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have geom (z : ℕ) : (∑ j ∈ Icc 1 z, 1/(p:ℝ)^j) ≤ 1/((p:ℝ)-1) := by
    have exactSum (t : ℕ) : ((p:ℝ)-1)*(∑ j ∈ Icc 1 t, 1/(p:ℝ)^j) =
        1-1/(p:ℝ)^t := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [sum_Icc_succ_top (by omega : 1 ≤ t+1),mul_add,ih,pow_succ]
        field_simp
        ring
    apply (le_div_iff₀ (by linarith)).mpr
    rw [mul_comm,exactSum]
    linarith [show 0 ≤ 1/(p:ℝ)^z by positivity]
  have sum_bound : (∑ k ∈ Icc 1 n, ((f.eval (k:ℤ)).natAbs.factorization p : ℝ)) ≤
      b*(n/((p:ℝ)-1)+J) := by
    rw [sum_congr rfl expcount,sum_comm]
    refine (sum_le_sum block).trans ?_
    rw [←sum_mul,sum_add_distrib]
    simp only [div_eq_mul_inv,←mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,
      nsmul_eq_mul,mul_one]
    rw [mul_comm b]
    gcongr
    simpa only [one_div] using geom J
  have logJ : (J:ℝ)*Real.log p ≤ Real.log H := by
    have h := Nat.pow_log_le_self p hH.ne'
    have hc : (p:ℝ)^J ≤ H := by exact_mod_cast h
    simpa [Real.log_pow] using Real.log_le_log (by positivity) hc
  have h := mul_le_mul_of_nonneg_right sum_bound (Real.log_natCast_nonneg p)
  refine h.trans ?_
  calc b*(n/((p:ℝ)-1)+J)*Real.log p =
        b*(n*Real.log p/((p:ℝ)-1)+J*Real.log p) := by ring
       _ ≤ _ := by gcongr

/-- Finite Euler estimate. The error for complete prime-power periods is bounded
by the contribution of the finitely many ramified primes. Incomplete periods
cost one polynomial-height logarithm per prime. -/
theorem finite (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ U E : ℝ, 0 ≤ U ∧ 0 ≤ E ∧ ∀ B n H : ℕ, 0 < H →
      (∀ k ∈ Icc 1 n, 0 < (f.eval (k:ℤ)).natAbs ∧ (f.eval (k:ℤ)).natAbs ≤ H) →
      (∑ k ∈ Icc 1 n, Real.log (Split976.small B (f.eval (k:ℤ)).natAbs)) ≤
        n*((∑ p ∈ Nat.primesLE B, rho f p * (Real.log p / ((p:ℝ)-1)))+E) +
          (Nat.primeCounting B:ℝ)*U*Real.log H := by
  obtain ⟨U,hU,hu⟩ := CoeffBound975.roots_uniform f hf hd
  let D := (f.resultant f.derivative).natAbs
  have hD : D ≠ 0 := Int.natAbs_ne_zero.mpr (Local975.resultant_nonzero f hf hd)
  let w (p : ℕ) := Real.log p / ((p:ℝ)-1)
  have wpos (p : ℕ) (hp : p.Prime) : 0 ≤ w p :=
    div_nonneg (Real.log_natCast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hp.one_le))
  let E := ∑ p ∈ D.primeFactors,U*w p
  refine ⟨U,E,hU,sum_nonneg (fun p hp => mul_nonneg hU (wpos _ (Nat.prime_of_mem_primeFactors hp))),
    fun B n H hH hsize => ?_⟩
  let bad (p : ℕ) := if p ∈ D.primeFactors then U*w p else 0
  have each (p : ℕ) (hp : p ∈ B.primesLE) :
      (∑ k ∈ Icc 1 n, ((f.eval (k:ℤ)).natAbs.factorization p : ℝ)*Real.log p) ≤
        (n:ℝ)*(rho f p*w p+bad p)+U*Real.log H := by
    rw [←sum_mul]
    have pp := Nat.prime_of_mem_primesLE hp
    have hr : 0 ≤ rho f p := Nat.cast_nonneg _
    have wur := wpos p pp
    have wh : (n:ℝ)*Real.log p/((p:ℝ)-1) = n*w p := by dsimp [w]; ring
    by_cases hbad : p ∈ D.primeFactors
    · have z := prime_weight f p n H pp hH hsize U hU (fun j _ =>
        (le_abs_self _).trans (hu p pp j))
      rw [wh] at z
      simpa only [bad,if_pos hbad] using z.trans (show U*(n*w p+Real.log H) ≤
        n*(rho f p*w p+U*w p)+U*Real.log H by
          nlinarith only [mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hr wur)])
    · have good : ¬ (p:ℤ) ∣ f.resultant f.derivative := fun hpD =>
        hbad (Nat.mem_primeFactors.mpr ⟨pp,Int.natAbs_dvd_natAbs.mpr hpD,hD⟩)
      have heq (j : ℕ) (hj : 0 < j) : rho f (p^j) = rho f p := by
        simp only [rho_apply]
        rw [Local975.hensel f hd p pp good j hj]
      have z := prime_weight f p n H pp hH hsize (rho f p) hr (fun j hj => (heq j hj).le)
      rw [wh] at z
      have hpU : rho f p ≤ U := (le_abs_self _).trans (by simpa using hu p pp 1)
      simpa only [bad,if_neg hbad,add_zero] using z.trans (show
        rho f p*(n*w p+Real.log H) ≤ n*(rho f p*w p)+U*Real.log H by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hpU) (Real.log_natCast_nonneg H)])
  have badsum : (∑ p ∈ Nat.primesLE B,bad p) ≤ E := by
    dsimp only [bad]
    rw [←sum_filter]
    apply sum_le_sum_of_subset_of_nonneg (fun p h => (mem_filter.mp h).2)
    exact fun p hp _ => mul_nonneg hU (wpos _ (Nat.prime_of_mem_primeFactors hp))
  simp_rw [log_small]
  rw [sum_comm]
  refine (sum_le_sum each).trans ?_
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting]
  dsimp only [w] at *
  nlinarith only [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr badsum)]

/-- An irreducible polynomial of degree at least two never vanishes on
integers, and its values on the interval have polynomial height. -/
theorem height (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ S : ℕ, 0 < S ∧ ∀ k n : ℕ, 1 ≤ k → k ≤ n →
      0 < (f.eval (k:ℤ)).natAbs ∧ (f.eval (k:ℤ)).natAbs ≤ S*n^f.natDegree := by
  let s := ∑ i ∈ range (f.natDegree+1),(f.coeff i).natAbs
  refine ⟨s+1,by omega,fun k n hk hkn => ⟨Int.natAbs_pos.mpr ?_,?_⟩⟩
  · intro hz
    have ass := (irreducible_X_sub_C (k:ℤ)).associated_of_dvd hf (dvd_iff_isRoot.mpr hz)
    have de := natDegree_le_of_dvd ass.symm.dvd (X_sub_C_ne_zero (k:ℤ))
    rw [natDegree_X_sub_C] at de
    omega
  · rw [eval_eq_sum_range]
    refine (Int.natAbs_sum_le _ _).trans ?_
    calc _ ≤ ∑ i ∈ range (f.natDegree+1),(f.coeff i).natAbs*n^f.natDegree :=
              sum_le_sum (fun i hi => by
                rw [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
                exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hkn i).trans
                  (Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hi; omega))))
         _ ≤ _ := by rw [←sum_mul]; exact Nat.mul_le_mul_right _ (Nat.le_succ s)

theorem reduce (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (mertens : ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, (∑ p ∈ Nat.primesLE n,
      rho f p * (Real.log p / ((p:ℝ)-1))) ≤ Real.log n + A)
    (C : ℕ) (hC : 1 ≤ C) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Icc 1 n, Real.log (Split976.small (C*n) (f.eval (k:ℤ)).natAbs)) ≤
        (n:ℝ)*Real.log n + K*n := by
  obtain ⟨U,E,hU,_,fin⟩ := finite f hf (by omega)
  obtain ⟨S,hS,size⟩ := height f hf hd
  obtain ⟨A,ha⟩ := mertens
  have top : Tendsto (fun n : ℕ => C*n) atTop atTop := tendsto_atTop.2 fun z =>
    (eventually_ge_atTop z).mono fun n hn =>
      hn.trans (Nat.le_mul_of_pos_left n (by omega))
  have piev := (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one).filter_mono
    (tendsto_natCast_atTop_atTop.comp top)
  refine ⟨Real.log C+A+E+(Real.log 4+1)*C*U*(f.natDegree+1),?_⟩
  filter_upwards [top.eventually ha,piev,eventually_ge_atTop S,eventually_ge_atTop 2] with
    n hm hpi hSn hn
  have cn : n ≤ C*n := Nat.le_mul_of_pos_left n (by omega)
  have hSpos : (0:ℝ)<S := by exact_mod_cast hS
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hCpos : (0:ℝ)<C := by exact_mod_cast (show 0<C by omega)
  have lpos : 0 < Real.log (C*n : ℕ) := Real.log_pos (by exact_mod_cast (show 1<C*n by omega))
  have hpi' : (Nat.primeCounting (C*n):ℝ)*Real.log (C*n:ℕ) ≤ (Real.log 4+1)*(C*n:ℕ) := by
    apply (le_div_iff₀ lpos).mp
    change (⌊((C*n:ℕ):ℝ)⌋₊.primeCounting:ℝ) ≤
      (Real.log 4+1)*((C*n:ℕ):ℝ)/Real.log (C*n:ℕ) at hpi
    simpa only [Nat.floor_natCast] using hpi
  have lh : Real.log (S*n^f.natDegree : ℕ) ≤ ((f.natDegree:ℝ)+1)*Real.log (C*n:ℕ) := by
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul hSpos.ne' (pow_ne_zero _ hnpos.ne'),Real.log_pow]
    have a := Real.log_le_log hSpos (by exact_mod_cast (hSn.trans cn) : (S:ℝ) ≤ (C*n:ℕ))
    have b := Real.log_le_log hnpos (by exact_mod_cast cn : (n:ℝ) ≤ (C*n:ℕ))
    linarith [mul_le_mul_of_nonneg_left b (Nat.cast_nonneg f.natDegree)]
  have pe : (Nat.primeCounting (C*n):ℝ)*U*Real.log (S*n^f.natDegree:ℕ) ≤
      ((Real.log 4+1)*C*U*(f.natDegree+1))*n := by
    refine (mul_le_mul_of_nonneg_left lh (mul_nonneg (Nat.cast_nonneg _) hU)).trans ?_
    push_cast at hpi' ⊢
    nlinarith only [mul_le_mul_of_nonneg_right hpi'
      (mul_nonneg hU (by positivity : (0:ℝ) ≤ f.natDegree+1))]
  have z := fin (C*n) n (S*n^f.natDegree) (by positivity)
    (fun k hk => size k n (mem_Icc.mp hk).1 (mem_Icc.mp hk).2)
  change (∑ p ∈ (C*n).primesLE, _) ≤ Real.log (C*n:ℕ)+A at hm
  rw [Nat.cast_mul,Real.log_mul hCpos.ne' hnpos.ne'] at hm
  linarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n)]

/-- Replacing p by p−1 in the denominators costs only a bounded sum, because
log(p)/(p(p−1)) is dominated by 4/p^(3/2). -/
theorem shift (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ T : ℝ, ∀ N : ℕ,
      (∑ p ∈ N.primesLE, rho f p * (Real.log p/((p:ℝ)-1))) ≤
        (∑ p ∈ N.primesLE, rho f p * (Real.log p/(p:ℝ))) + T := by
  obtain ⟨U,hU,hu⟩ := CoeffBound975.roots_uniform f hf hd
  let g (p : ℕ) := 1/(p:ℝ)^(3/2:ℝ)
  have gs : Summable g := Real.summable_one_div_nat_rpow.mpr (by norm_num)
  refine ⟨(4*U)*∑' p : ℕ,g p,fun N => ?_⟩
  have leTerm (p : ℕ) (hp : p∈N.primesLE) : rho f p*(Real.log p/((p:ℝ)-1)) ≤
      rho f p*(Real.log p/(p:ℝ))+4*U*g p := by
    have pp := Nat.prime_of_mem_primesLE hp
    have p2 : (2:ℝ) ≤ p := by exact_mod_cast pp.two_le
    have p0 : (0:ℝ) < p := by linarith
    have p1 : (0:ℝ) < (p:ℝ)-1 := by linarith
    have id : Real.log p/((p:ℝ)-1) = Real.log p/p + Real.log p/((p:ℝ)*(p-1)) := by
      field_simp; ring
    have frac : Real.log p/((p:ℝ)*(p-1)) ≤ 4*g p := by
      have a := Real.log_natCast_le_rpow_div p (by norm_num : (0:ℝ)<1/2)
      have half : (p:ℝ)^(1/2:ℝ)*(p:ℝ)^(3/2:ℝ) = (p:ℝ)^2 := by
        rw [←Real.rpow_add p0]; norm_num
      have h := mul_le_mul_of_nonneg_right a (Real.rpow_nonneg p0.le (3/2))
      dsimp only [g]
      rw [mul_one_div,div_le_div_iff₀ (mul_pos p0 p1) (Real.rpow_pos_of_pos p0 _)]
      nlinarith only [h,half,mul_nonneg p0.le (sub_nonneg.mpr p2)]
    rw [id,mul_add]
    apply add_le_add_right
    have hru : rho f p ≤ U := (le_abs_self _).trans (by simpa using hu p pp 1)
    calc _ ≤ U*(4*g p) := mul_le_mul hru frac (by positivity) hU
         _ = _ := by ring
  refine (sum_le_sum leTerm).trans ?_
  rw [sum_add_distrib,←mul_sum]
  gcongr
  exact gs.sum_le_tsum _ (fun p _ => by dsimp [g]; positivity)

/-- The only analytic input is the sharp, additive-error Mertens estimate on
the distinct root-ideals with prime norm up to n. -/
theorem of_mertens (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (mertens : ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, (∑ p ∈ Nat.primesLE n,
      rho f p * (Real.log p / (p:ℝ))) ≤ Real.log n + A)
    (C : ℕ) (hC : 1 ≤ C) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Icc 1 n, Real.log (Split976.small (C*n) (f.eval (k:ℤ)).natAbs)) ≤
        (n:ℝ)*Real.log n + K*n := by
  apply reduce f hf hd _ C hC
  obtain ⟨A,ha⟩ := mertens
  obtain ⟨T,ht⟩ := shift f hf (by omega)
  refine ⟨A+T,?_⟩
  filter_upwards [ha] with n hn
  linarith [ht n]

end OMA.Small976

namespace OMA.Small976
open Finset Filter Polynomial RootsEuler975

/-- The portion supported on primes strictly between n and Cn is already O(n),
without any sharp Mertens hypothesis. -/
theorem medium (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (C : ℕ) (hC : 1 ≤ C) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Icc 1 n, Real.log (Split976.small (C*n) (f.eval (k:ℤ)).natAbs)) ≤
      (∑ k ∈ Icc 1 n, Real.log (Split976.small n (f.eval (k:ℤ)).natAbs)) + K*n := by
  obtain ⟨U,hU,hu⟩ := CoeffBound975.roots_uniform f hf (by omega)
  obtain ⟨S,hS,size⟩ := height f hf hd
  let D := U*((f.natDegree:ℝ)+2)
  have hD : 0 ≤ D := mul_nonneg hU (by positivity)
  refine ⟨(Real.log 4+1)*C*D,?_⟩
  have top : Tendsto (fun n : ℕ => ((C*n:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop.2 fun z : ℕ =>
      (eventually_ge_atTop z).mono fun n hn => hn.trans
        (Nat.le_mul_of_pos_left n (by omega)))
  filter_upwards [top.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one),
    eventually_ge_atTop S,eventually_ge_atTop 2] with n hpi hSn hn
  let N := C*n
  have hnN : n ≤ N := Nat.le_mul_of_pos_left n (by omega)
  have npos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have spos : (0:ℝ) < S := by exact_mod_cast hS
  have logN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have piN : (N.primeCounting:ℝ)*Real.log N ≤ (Real.log 4+1)*N := by
    apply (le_div_iff₀ logN).mp
    change (⌊(N:ℝ)⌋₊.primeCounting:ℝ) ≤ (Real.log 4+1)*N/Real.log N at hpi
    simpa only [Nat.floor_natCast] using hpi
  let H := S*n^f.natDegree
  have heightN : Real.log H ≤ ((f.natDegree:ℝ)+1)*Real.log N := by
    change Real.log ((S*n^f.natDegree:ℕ):ℝ) ≤ _
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul spos.ne' (pow_ne_zero _ npos.ne'),Real.log_pow]
    have a := Real.log_le_log spos (by exact_mod_cast (hSn.trans hnN) : (S:ℝ) ≤ N)
    have b := Real.log_le_log npos (by exact_mod_cast hnN : (n:ℝ) ≤ N)
    linarith [mul_le_mul_of_nonneg_left b (Nat.cast_nonneg f.natDegree)]
  let W := fun p : ℕ => ∑ k ∈ Icc 1 n, ((f.eval (k:ℤ)).natAbs.factorization p : ℝ)*Real.log p
  have localWeight (p : ℕ) (hp : p∈N.primesLE\n.primesLE) : W p ≤ D*Real.log N := by
    obtain ⟨hpN,hpn⟩ := mem_sdiff.mp hp
    obtain ⟨hpN,pp⟩ := Nat.mem_primesLE.mp hpN
    have np : n<p := lt_of_not_ge (fun h => hpn (Nat.mem_primesLE.mpr ⟨h,pp⟩))
    have one : (1:ℝ) < p := by exact_mod_cast pp.one_lt
    have num : (n:ℝ) ≤ (p:ℝ)-1 := by
      have e : (n:ℝ)+1 ≤ p := by exact_mod_cast np
      linarith
    have first : n*Real.log p/((p:ℝ)-1) ≤ Real.log N := by
      refine le_trans (b:=Real.log p) ((div_le_iff₀ (by linarith)).mpr ?_)
        (Real.log_le_log (by linarith) (by exact_mod_cast hpN))
      nlinarith only [mul_le_mul_of_nonneg_right num (Real.log_natCast_nonneg p)]
    have est := prime_weight f p n H pp (Nat.mul_pos hS (pow_pos (by omega) _))
      (fun k hk => size k n (mem_Icc.mp hk).1 (mem_Icc.mp hk).2) U hU
      (fun j _ => (le_abs_self _).trans (hu p pp j))
    dsimp only [W,D]
    rw [←sum_mul]
    refine est.trans ((mul_le_mul_of_nonneg_left (add_le_add first heightN) hU).trans ?_)
    ring_nf
    exact le_rfl
  have QP := Nat.primesLE_mono hnN
  have total (b : ℕ) : (∑ k ∈ Icc 1 n,Real.log (Split976.small b (f.eval (k:ℤ)).natAbs)) =
      ∑ p ∈ b.primesLE,W p := by simp_rw [log_small]; rw [sum_comm]
  rw [total,total,←sum_sdiff QP]
  apply add_le_of_le_sub_left
  have delta := (sum_le_sum localWeight).trans (sum_le_sum_of_subset_of_nonneg
    (sdiff_subset (s:=N.primesLE) (t:=n.primesLE)) (fun p _ _ => mul_nonneg hD logN.le))
  simp only [sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting] at delta
  have pif := mul_le_mul_of_nonneg_right piN hD
  dsimp [N] at pif
  push_cast at pif
  dsimp only [N] at delta ⊢
  push_cast at delta
  linarith

end OMA.Small976
end

section
namespace OMA.Finish976

theorem result : OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1.H3 := by
  apply OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H3_R1.main
  · intro f hf hd
    have pos : 0 < f.natDegree := by omega
    have mertens := OMA.Sharp976.close f hf pos (OMA.Average976.averaged f hf pos)
    simpa only [one_mul] using OMA.Small976.of_mertens f hf hd mertens 1 (by omega)
  · exact OMA.Small976.medium

end OMA.Finish976
end

theorem OMA.solution : OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1.H3 := OMA.Finish976.result
