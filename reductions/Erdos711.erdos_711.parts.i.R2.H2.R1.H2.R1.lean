import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1
import Mathlib

/-! A small set of common multiples can serve as centres for all the requested
divisors. Separate the centres modulo K, then map d to its centre plus or
minus K times d, choosing the side with enough room. Each residue class
hosts an injective assignment. The remaining Hall obstruction requires
strictly more than floor(n^(δ/4)) centres. -/

open Finset Filter
namespace OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1

def H1 : Prop := ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → ∀ᶠ n : ℕ in atTop,
  let q := ⌊(n:ℝ)^δ⌋₊
  let b := ⌊(n:ℝ)^(δ/4)⌋₊
  ∀ r : ℕ, ∀ C ⊆ Icc (r+1) (r+n*q), C.card ≤ b →
    ∃ K : ℕ, 0 < K ∧ 2*K ≤ q ∧ Set.InjOn (fun c : ℕ => c%K) (C : Set ℕ)

def H2 : Prop := ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → ∀ᶠ n : ℕ in atTop,
  let q := ⌊(n:ℝ)^δ⌋₊
  let b := ⌊(n:ℝ)^(δ/4)⌋₊
  ∀ r : ℕ, n^2 < r → r < (Icc 1 n).lcm id → ∀ U : Finset ℕ,
    (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
    (∃ y ∈ Icc (r+1) (r+n*q), q < (U.filter (· ∣ y)).card) →
    (∀ C ⊆ Icc (r+1) (r+n*q), C.card ≤ b → ∃ d ∈ U, ∀ c ∈ C, ¬d ∣ c) →
    U.card ≤ ((Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card

/-! The divisor estimate in the next namespace is from LAPRAI's verified
proof of Erdos711.erdos_711.parts.i.R2.H2.R1.H1. -/
open Filter Finset Real
open scoped Topology

namespace DivisorGrowth

private theorem pointwise (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 0 < y →
      (y.divisors.card : ℝ) ≤ C*(y:ℝ)^ε := by
  have grow : Tendsto (fun p : ℕ => (p:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK⟩ := eventually_atTop.mp (grow.eventually_ge_atTop (2:ℝ))
  let b := (2:ℝ)^ε-1
  have bp : 0 < b := by
    dsimp [b]
    have h := rpow_lt_rpow_of_exponent_lt (show (1:ℝ)<2 by norm_num) he
    simpa using h
  let C := 1+b⁻¹
  have C1 : 1 ≤ C := le_add_of_nonneg_right (inv_nonneg.mpr bp.le)
  have Cb : 1 ≤ C*b := by
    dsimp [C]
    rw [add_mul,one_mul,inv_mul_cancel₀ bp.ne']
    linarith
  refine ⟨C^K,pow_pos (zero_lt_one.trans_le C1) _,?_⟩
  intro y hy
  let P := y.primeFactors
  let W (p : ℕ) := (p:ℝ)^ε
  let u (p : ℕ) : ℝ := if p<K then C else 1
  have hb (p : ℕ) (hp : p ∈ P) : (2:ℝ)^ε ≤ W p :=
    rpow_le_rpow (by norm_num) (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) he.le
  have term (p : ℕ) (hp : p ∈ P) :
      (y.factorization p : ℝ)+1 ≤ u p*(W p)^y.factorization p := by
    have Wp : 0 ≤ W p := by dsimp [W]; positivity
    have hbig := hb p hp
    have bern := one_add_mul_sub_le_pow (show -1 ≤ W p by linarith) (y.factorization p)
    have ep : (0:ℝ) ≤ y.factorization p := by positivity
    by_cases small : p<K
    · rw [show u p = C by simp [u,small]]
      have hh : 1 ≤ C*(W p-1) := Cb.trans (mul_le_mul_of_nonneg_left
        (show b ≤ W p-1 by dsimp [b]; linarith) (zero_le_one.trans C1))
      have eHH := mul_le_mul_of_nonneg_left hh ep
      have eBern := mul_le_mul_of_nonneg_left bern (zero_le_one.trans C1)
      nlinarith only [C1,eHH,eBern]
    · simp only [u, if_neg small, one_mul]
      have ht : 2 ≤ W p := hK p (le_of_not_gt small)
      nlinarith only [bern,mul_nonneg ep (show 0 ≤ W p-2 by linarith)]
  have uj : ∏ p ∈ P, u p ≤ C^K := by
    let small := P.filter (fun p => p<K)
    have hh : small ⊆ range K := fun p hp => mem_range.mpr (mem_filter.mp hp).2
    have hc : small.card ≤ K := by simpa using card_le_card hh
    calc
      _ = ∏ _p ∈ small, C := by
        symm
        exact prod_filter (s := P) (fun p => p<K) (fun _ => C)
      _ = C^small.card := prod_const _
      _ ≤ C^K := pow_le_pow_right₀ C1 hc
  have wprod : (∏ p ∈ P, (W p)^y.factorization p) = (y:ℝ)^ε := by
    trans ∏ p ∈ P, ((p:ℝ)^y.factorization p)^ε
    · apply prod_congr rfl
      intro p _
      exact rpow_pow_comm (show (0:ℝ) ≤ p by positivity) _ _
    rw [finsetProd_rpow _ _ (fun _ _ => by positivity)]
    have eq : (∏ p ∈ P, (p:ℝ)^y.factorization p) = (y:ℝ) := by
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hy.ne').symm
    rw [eq]
  calc
    (y.divisors.card:ℝ) = ∏ p ∈ P, ((y.factorization p:ℝ)+1) := by
      rw [Nat.card_divisors hy.ne']
      push_cast
      rfl
    _ ≤ ∏ p ∈ P, u p*(W p)^y.factorization p :=
      prod_le_prod (fun _ _ => by positivity) term
    _ = (∏ p ∈ P,u p)*(y:ℝ)^ε := by rw [prod_mul_distrib,wprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right uj (rpow_nonneg (by positivity) _)

theorem uniform (δ : ℝ) (hd : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℕ, 0 < y → y ≤ n^3 →
    (y.divisors.card : ℝ) ≤ (n:ℝ)^δ := by
  let ε := δ/6
  have he : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,hb⟩ := pointwise ε he
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C] with n hn y hy hyn
  have hpow : (y:ℝ) ≤ (n:ℝ)^3 := by exact_mod_cast hyn
  have hp : ((n:ℝ)^3)^ε = (n:ℝ)^(δ/2) := by
    rw [← rpow_natCast, ← rpow_mul (by positivity)]
    congr 1
    dsimp [ε]
    ring
  calc
    _ ≤ C*(y:ℝ)^ε := hb y hy
    _ ≤ C*((n:ℝ)^3)^ε := mul_le_mul_of_nonneg_left
      (rpow_le_rpow (by positivity) hpow he.le) hC.le
    _ = C*(n:ℝ)^(δ/2) := by rw [hp]
    _ ≤ (n:ℝ)^(δ/2)*(n:ℝ)^(δ/2) := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by
      rw [← rpow_add' (by positivity) (by linarith : δ/2+δ/2 ≠ 0), show δ/2+δ/2=δ by ring]

end DivisorGrowth


namespace CentreModuli

lemma exists_modulus (C : Finset ℕ) (B : ℕ)
    (bound : ∀ c ∈ C, ∀ e ∈ C, ((e-c).divisors).card ≤ B) :
    ∃ K : ℕ, 0 < K ∧ K ≤ C.card*(C.card*B)+1 ∧
      Set.InjOn (fun c : ℕ => c%K) (C : Set ℕ) := by
  classical
  let row (c : ℕ) := C.biUnion fun e => (e-c).divisors
  let D := C.biUnion row
  have cardRow (c : ℕ) (hc : c ∈ C) : (row c).card ≤ C.card*B := by
    exact card_biUnion_le.trans ((sum_le_sum (fun e he => bound c hc e he)).trans_eq (by simp))
  have cardD : D.card ≤ C.card*(C.card*B) := by
    exact card_biUnion_le.trans ((sum_le_sum cardRow).trans_eq (by simp))
  have many : D.card < (Icc 1 (C.card*(C.card*B)+1)).card := by
    rw [Nat.card_Icc]; omega
  obtain ⟨K,mem,avoid⟩ := exists_mem_notMem_of_card_lt_card many
  refine ⟨K,(mem_Icc.mp mem).1,(mem_Icc.mp mem).2,?_⟩
  have no {a b : ℕ} (ha : a∈C) (hb : b∈C) (h : a<b) (eq : a ≡ b [MOD K]) : False := by
    apply avoid
    exact mem_biUnion.mpr ⟨a,ha,mem_biUnion.mpr ⟨b,hb,Nat.mem_divisors.mpr
      ⟨eq.dvd',Nat.sub_ne_zero_of_lt h⟩⟩⟩
  intro a ha b hb same
  rcases lt_trichotomy a b with h|h|h
  · exact (no ha hb h same).elim
  · exact h
  · exact (no hb ha h same.symm).elim

lemma modulus_growth : ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → ∀ᶠ n : ℕ in atTop,
    let q := ⌊(n:ℝ)^δ⌋₊
    let b := ⌊(n:ℝ)^(δ/4)⌋₊
    ∀ r : ℕ, ∀ C ⊆ Icc (r+1) (r+n*q), C.card ≤ b →
    ∃ K : ℕ, 0 < K ∧ 2*K ≤ q ∧ Set.InjOn (fun c : ℕ => c%K) (C : Set ℕ) := by
  intro δ hd half
  have hd4 : 0 < δ/4 := by positivity
  have grow : Tendsto (fun n : ℕ => (n:ℝ)^(δ/4)) atTop atTop :=
    (tendsto_rpow_atTop hd4).comp tendsto_natCast_atTop_atTop
  filter_upwards [DivisorGrowth.uniform _ hd4,grow.eventually_ge_atTop 3,eventually_ge_atTop (2:ℕ)]
    with n divisor large hn
  let b := ⌊(n:ℝ)^(δ/4)⌋₊
  let q := ⌊(n:ℝ)^δ⌋₊
  change ∀ r : ℕ, ∀ C ⊆ Icc (r+1) (r+n*q), C.card ≤ b → _
  intro r C inside size
  have nb : 3 ≤ b := Nat.le_floor (by exact_mod_cast large)
  have small : q ≤ n := by
    have hi := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega) : 1 ≤ (n:ℝ))
      (show δ ≤ 1 by linarith)
    rw [Real.rpow_one] at hi
    exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ (n:ℝ)^δ)).trans hi
  have Bbound (c) (hc : c ∈ C) (d) (he : d ∈ C) : (d-c).divisors.card ≤ b := by
    by_cases zero : d-c=0
    · simp [zero]
    apply Nat.le_floor
    apply divisor _ (by omega)
    have lo := (mem_Icc.mp (inside hc)).1
    have hi := (mem_Icc.mp (inside he)).2
    have diff : d-c ≤ n*q := by omega
    exact diff.trans ((Nat.mul_le_mul_left n small).trans (by nlinarith [Nat.mul_le_mul_left (n*n) (show 1≤n by omega)] : n*n ≤ n^3))
  obtain ⟨K,positive,hK,res⟩ := exists_modulus C b Bbound
  refine ⟨K,positive,?_,res⟩
  have hh : C.card * (C.card*b) ≤ b*(b*b) :=
    Nat.mul_le_mul size (Nat.mul_le_mul_right b size)
  have low : 2 ≤ b*(b*b) := by
    have h := Nat.mul_le_mul nb (Nat.mul_le_mul nb nb)
    omega
  have enough := Nat.mul_le_mul_right (b*(b*b)) nb
  have cost : 2*K ≤ b^4 := by nlinarith
  apply cost.trans
  apply Nat.le_floor
  have floor := Nat.floor_le (by positivity : 0 ≤ (n:ℝ)^(δ/4))
  calc
    ((b^4 : ℕ):ℝ) = (b:ℝ)^4 := by norm_cast
    _ ≤ ((n:ℝ)^(δ/4))^4 := pow_le_pow_left₀ (by positivity) floor 4
    _ = (n:ℝ)^δ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
      congr 1
      norm_num

end CentreModuli

lemma small_centres_separate : H1 := CentreModuli.modulus_growth

lemma fixed_interval {r n q K : ℕ} (U C : Finset ℕ) (hk : 0 < K) (room : 2*K ≤ q)
    (size : ∀ d ∈ U, d ≤ n) (inside : C ⊆ Icc (r+1) (r+n*q))
    (cover : ∀ d ∈ U, ∃ c ∈ C, d ∣ c)
    (separate : Set.InjOn (fun c : ℕ => c%K) (C : Set ℕ)) :
    U.card ≤ ((Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  let center (d : ℕ) := if h : d ∈ U then (cover d h).choose else 0
  have spec (d) (hd : d∈U) : center d ∈ C ∧ d ∣ center d := by
    simpa [center,hd] using (cover d hd).choose_spec
  let f (d : ℕ) := if center d+K*n ≤ r+n*q then center d+K*d else center d-K*d
  have width : 2*(K*n) ≤ n*q := by
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left n room
  have base (d) (hd : d∈U) := mem_Icc.mp (inside (spec d hd).1)
  have scale (d) (hd : d∈U) := Nat.mul_le_mul_left K (size d hd)
  have good (d) (hd : d∈U) : f d ∈ Icc (r+1) (r+n*q) ∧ d ∣ f d ∧ f d ≡ center d [MOD K] := by
    obtain ⟨lo,hi⟩ := base d hd
    have bound := scale d hd
    have dvd := (spec d hd).2
    dsimp only [f]
    split_ifs with h
    · exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩, dvd_add dvd (dvd_mul_left ..),
        by simp [Nat.ModEq,Nat.add_mod]⟩
    · have sub : K*d ≤ center d := by omega
      have div : K ∣ center d - (center d-K*d) := by
        rw [Nat.sub_sub_self sub]
        exact dvd_mul_right .. 
      exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩, Nat.dvd_sub dvd (dvd_mul_left ..),
        (Nat.modEq_iff_dvd' (Nat.sub_le ..)).mpr div⟩
  apply card_le_card_of_injOn f
  · intro d hd
    exact mem_filter.mpr ⟨(good d hd).1,d,hd,(good d hd).2.1⟩
  · intro a ha b hb same
    have ra := (good a ha).2.2
    have rb := (good b hb).2.2
    rw [same] at ra
    have eq := separate (spec a ha).1 (spec b hb).1 (ra.symm.trans rb)
    have sa := scale a ha
    have sb := scale b hb
    have inter := base b hb
    unfold f at same
    rw [eq] at same
    split_ifs at same with h
    · exact Nat.eq_of_mul_eq_mul_left hk (Nat.add_left_cancel same)
    · apply Nat.eq_of_mul_eq_mul_left hk
      omega


theorem main : H1 → H2 → OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1.H2 := by
  classical
  intro moduli residual δ hd half
  filter_upwards [moduli δ hd half,residual δ hd half] with n mod enough
  dsimp only at mod enough ⊢
  intro r lo hi U spec crowded _
  by_cases can : ∃ C ⊆ Icc (r+1) (r+n*⌊(n:ℝ)^δ⌋₊), C.card ≤ ⌊(n:ℝ)^(δ/4)⌋₊ ∧
      ∀ d ∈ U, ∃ c ∈ C, d ∣ c
  · obtain ⟨C,inside,small,cover⟩ := can
    obtain ⟨K,hK,room,sep⟩ := mod r C inside small
    exact fixed_interval U C hK room (fun d hd => (spec d hd).2.1) inside cover sep
  · apply enough r lo hi U spec crowded
    intro C inside small
    by_contra! all
    exact can ⟨C,inside,small,all⟩

end OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1
