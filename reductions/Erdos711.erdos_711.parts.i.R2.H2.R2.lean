import OMAReductions.R_Erdos711_erdos_711_parts_i_R2
import Mathlib

/-!
A divisor joining two distinct points divides their nonzero difference. Counting
ordered pairs of multiples gives a Hall bound that is uniform in the shift:
a family with |U| D ≤ q(q−1) expands even when single points are crowded.
Here q and D are the integer parts of n^δ and n^(δ/2). Thus a remaining
obstruction must have size strictly greater than q(q−1)/D, of order n^(3δ/2).

The periodic reduction, the sparse and common-center estimates, and the Hall
matching argument are adapted from Steve Digital’s first reduction of this step (PR #5001).
The divisor-growth estimate is LAPRAI's proof of its first hypothesis (PR #5254).
-/

namespace OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R2

open Filter Finset

/-- Double-count ordered pairs of different multiples of each divisor. -/
def H1 : Prop :=
  ∀ (U Y : Finset ℕ) (q D : ℕ),
    (∀ d ∈ U, q ≤ (Y.filter (d ∣ ·)).card) →
    (∀ x ∈ Y, ∀ y ∈ Y, x < y → (y - x).divisors.card ≤ D) →
    U.card * (q * (q - 1)) ≤ Y.card * (Y.card - 1) * D

/-- Hall expansion for large families in a crowded window without a common multiple. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ᶠ n : ℕ in atTop,
    let q := ⌊(n : ℝ) ^ δ⌋₊
    let D := ⌊(n : ℝ) ^ (δ / 2)⌋₊
    ∀ r : ℕ, n ^ 2 < r → r < (Finset.Icc 1 n).lcm id →
      ∀ U : Finset ℕ, (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
        (∃ y ∈ Finset.Icc (r + 1) (r + n * q), q < (U.filter (· ∣ y)).card) →
        (¬ ∃ z ∈ Finset.Icc (r + 1) (r + n * q), ∀ d ∈ U, d ∣ z) →
        q * (q - 1) < U.card * D →
        U.card ≤ ((Finset.Icc (r + 1) (r + n * q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card

theorem small_family_hall (pairs : H1) (U Y : Finset ℕ) (q D : ℕ) (hD : 0 < D)
    (multiples : ∀ d ∈ U, q ≤ (Y.filter (d ∣ ·)).card)
    (diffs : ∀ x ∈ Y, ∀ y ∈ Y, x < y → (y - x).divisors.card ≤ D)
    (small : U.card * D ≤ q * (q - 1)) : U.card ≤ Y.card := by
  by_contra! h
  have hp := pairs U Y q D multiples diffs
  have hl : Y.card * (Y.card - 1) < U.card * U.card := by
    exact Nat.mul_lt_mul_of_le_of_lt h.le ((Nat.sub_le _ _).trans_lt h) (by omega)
  have := (Nat.mul_lt_mul_of_pos_right hl hD).trans_le
    (show U.card * U.card * D ≤ U.card * (q * (q-1)) by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ small)
  omega


namespace DivisorGrowth

open Real
open scoped Topology

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


/-- Each divisor has at least q distinct multiples in a window of length nq. -/
lemma many_multiples (r n q : ℕ) (U : Finset ℕ)
    (hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n) :
    ∀ d ∈ U, q ≤ (((Finset.Icc (r+1) (r+n*q)).filter
      (fun y => ∃ k ∈ U, k ∣ y)).filter (d ∣ ·)).card := by
  classical
  let I := Finset.Icc (r+1) (r+n*q)
  intro d hd
  change q ≤ ((I.filter (fun y => ∃ k ∈ U, k ∣ y)).filter (d ∣ ·)).card
  obtain ⟨hd0, hdn⟩ := hU d hd
  let g (j : ℕ) := (r / d + 1 + j) * d
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) hij
    omega
  rw [← Finset.card_range q, ← Finset.card_image_of_injective _ hg]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  have hjq := Finset.mem_range.mp hj
  have hdiv : d ∣ g j := dvd_mul_left _ _
  have hlo := Nat.mod_lt r (by omega : 0 < d)
  have heq := Nat.mod_add_div r d
  rw [Nat.mul_comm d (r/d)] at heq
  have hmul : (j+1)*d ≤ q*n := Nat.mul_le_mul (by omega) hdn
  have hin : g j ∈ I := by
    apply Finset.mem_Icc.mpr
    dsimp [g]
    rw [show r/d+1+j = r/d+(j+1) by omega, Nat.add_mul]
    rw [Nat.mul_comm q n] at hmul
    constructor
    · have := Nat.mul_le_mul_right d (show 1 ≤ j+1 by omega)
      simp only [one_mul] at this
      omega
    · omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hin, d, hd, hdiv⟩, hdiv⟩

lemma sparse_hall (r n q : ℕ) (hq : 0 < q) (U : Finset ℕ)
    (hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n)
    (hdeg : ∀ y ∈ Finset.Icc (r+1) (r+n*q), (U.filter (· ∣ y)).card ≤ q) :
    U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  let I := Finset.Icc (r+1) (r+n*q)
  let Y := I.filter (fun y => ∃ d ∈ U, d ∣ y)
  change U.card ≤ Y.card
  apply Nat.le_of_mul_le_mul_right _ hq
  apply Finset.card_mul_le_card_mul (fun d y : ℕ => d ∣ y)
  · exact many_multiples r n q U hU
  · intro y hy
    exact hdeg y (Finset.mem_filter.mp hy).1

lemma center_hall (r n q : ℕ) (hq : 3 ≤ q) (U : Finset ℕ)
    (hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n) (z : ℕ)
    (hz : z ∈ Finset.Icc (r+1) (r+n*q)) (hall : ∀ d ∈ U, d ∣ z) :
    U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hz
  by_cases h : z+n ≤ r+n*q
  · apply Finset.card_le_card_of_injOn (fun d => z+d)
    · intro d hd
      have := hU d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩, d, hd,
        dvd_add (hall d hd) (dvd_refl d)⟩
    · intro a ha b hb hab
      exact Nat.add_left_cancel hab
  · have hnq := Nat.mul_le_mul_left n hq
    apply Finset.card_le_card_of_injOn (fun d => z-d)
    · intro d hd
      have := hU d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩, d, hd,
        Nat.dvd_sub (hall d hd) (dvd_refl d)⟩
    · intro a ha b hb hab
      have := hU a ha
      have := hU b hb
      dsimp at hab
      omega
lemma match_residue (n r q : ℕ)
    (hHall : ∀ U : Finset ℕ,
      (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
      U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card) :
    ∃ a : Fin n → ℕ,
      Set.InjOn a {i | ∃ p : ℕ, p.Prime ∧ p ∣ (i.val+1) ∧ Nat.sqrt n < p} ∧
      ∀ i : Fin n, (∃ p : ℕ, p.Prime ∧ p ∣ (i.val+1) ∧ Nat.sqrt n < p) →
        r < a i ∧ a i ≤ r+n*q ∧ (i.val+1) ∣ a i := by
  classical
  let R := {i : Fin n | ∃ p : ℕ, p.Prime ∧ p ∣ (i.val+1) ∧ Nat.sqrt n < p}
  let val (i : R) := i.val.val+1
  have hval : Function.Injective val := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_right_cancel hij
  let I := Finset.Icc (r+1) (r+n*q)
  let T (i : R) := I.filter (val i ∣ ·)
  have hex : ∀ t : Finset R, t.card ≤ (t.biUnion T).card := by
    intro t
    let U := t.image val
    have hU : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), i.val.isLt, i.property⟩
    have hc : U.card = t.card := Finset.card_image_of_injective t hval
    rw [← hc]
    apply (hHall U hU).trans
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hyI,d,hd,hdy⟩ := Finset.mem_filter.mp hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_biUnion.mpr ⟨i,hi, Finset.mem_filter.mpr ⟨hyI,hdy⟩⟩
  obtain ⟨f, hf, ht⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hex
  let a (i : Fin n) := if hi : i ∈ R then f ⟨i,hi⟩ else 0
  refine ⟨a, ?_, ?_⟩
  · intro i hi j hj hij
    change i ∈ R at hi
    change j ∈ R at hj
    have he : f ⟨i,hi⟩ = f ⟨j,hj⟩ := by simpa [a, hi, hj] using hij
    exact congrArg Subtype.val (hf he)
  · intro i hi
    change i ∈ R at hi
    obtain ⟨hI,hd⟩ := Finset.mem_filter.mp (ht ⟨i,hi⟩)
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hI
    simpa [a,hi,val] using (show r < f ⟨i,hi⟩ ∧ f ⟨i,hi⟩ ≤ r+n*q ∧ (i.val+1) ∣ f ⟨i,hi⟩
      from ⟨hl,hu,hd⟩)

theorem main : H1 → H2 → OMA.R_Erdos711_erdos_711_parts_i_R2.H2 := by
  classical
  intro hpairs hrem ε hε
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hhalf : δ ≤ 1/2 := min_le_right _ _
  have hε' : δ + δ ≤ ε := by have := min_le_left (ε/2) (1/2 : ℝ); dsimp [δ]; linarith
  have hg : Tendsto (fun n : ℕ => (n : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [DivisorGrowth.uniform (δ/2) (by positivity), hrem δ hδ hhalf, hg.eventually_ge_atTop 3,
    eventually_ge_atTop (2 : ℕ)] with n hτ hcase hgrow hn m
  let q := ⌊(n : ℝ)^δ⌋₊
  let D := ⌊(n : ℝ)^(δ/2)⌋₊
  have hq : 3 ≤ q := Nat.le_floor (by exact_mod_cast hgrow)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0:ℝ) < n := by linarith
  have hqR : (q:ℝ) ≤ (n:ℝ)^δ := Nat.floor_le (by positivity)
  have hqn : q ≤ n := by
    have hb := Real.rpow_le_rpow_of_exponent_le hnR (show δ ≤ 1 by linarith)
    rw [Real.rpow_one] at hb
    exact_mod_cast hqR.trans hb
  have hD : 0 < D := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow hnR (by positivity : 0 ≤ δ/2))
  have hDq : D ≤ q := Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le hnR (by linarith : δ/2 ≤ δ))
  have hwidth : n*q ≤ n^3 := by
    calc n*q ≤ n*n := Nat.mul_le_mul_left _ hqn
         _ ≤ n^3 := by nlinarith [Nat.mul_le_mul_left (n*n) (show 1 ≤ n by omega)]
  let M := (Finset.Icc 1 n).lcm id
  have hM : 0 < M := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro x hx
    have := (Finset.mem_Icc.mp hx).1
    exact Nat.ne_of_gt this
  let r := m % M
  have hr : r < M := Nat.mod_lt _ hM
  have hshift : r + M*(m/M) = m := Nat.mod_add_div _ _
  have hh : ∀ U : Finset ℕ,
      (∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
      U.card ≤ ((Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
    intro U hU
    have hb d (hd : d ∈ U) := And.intro (hU d hd).1 (hU d hd).2.1
    by_cases hc : ∃ z ∈ Finset.Icc (r+1) (r+n*q), ∀ d ∈ U, d ∣ z
    · obtain ⟨z,hz,h⟩ := hc
      exact center_hall r n q hq U hb z hz h
    by_cases hd : ∃ y ∈ Finset.Icc (r+1) (r+n*q), q < (U.filter (· ∣ y)).card
    · by_cases hs : r ≤ n^2
      · obtain ⟨y,hy,hcrowd⟩ := hd
        obtain ⟨hylo,hyhi⟩ := Finset.mem_Icc.mp hy
        have hyn : y ≤ n^3 := by
          have hmul := Nat.mul_le_mul_left n hqn
          have hpow := Nat.mul_le_mul_left (n*n) hn
          simp only [pow_succ, pow_zero, one_mul] at hs ⊢
          omega
        have hyt := Nat.le_floor (hτ y (by omega) hyn)
        have hsub : U.filter (· ∣ y) ⊆ y.divisors := by
          intro d h
          exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp h).2, by omega⟩
        exact False.elim ((not_lt_of_ge (((Finset.card_le_card hsub).trans hyt).trans hDq)) hcrowd)
      · by_cases small : U.card * D ≤ q * (q - 1)
        · let Y := (Finset.Icc (r+1) (r+n*q)).filter (fun y => ∃ d ∈ U, d ∣ y)
          apply small_family_hall hpairs U Y q D hD (many_multiples r n q U hb) _ small
          intro x hx y hy hxy
          have hxI := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
          have hyI := Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1
          exact Nat.le_floor (hτ (y-x) (by omega) ((show y-x ≤ n*q by omega).trans hwidth))
        · exact hcase r (by omega) hr U hU hd hc (Nat.lt_of_not_ge small)
    · push Not at hd
      exact sparse_hall r n q (by omega) U hb hd
  obtain ⟨a,ha,hw⟩ := match_residue n r q hh
  refine ⟨n*q+1, ?_, fun i => a i + M*(m/M), ?_, ?_⟩
  · push_cast
    have hone : 1 ≤ (n:ℝ) * (n:ℝ)^δ := by nlinarith
    calc
      (n:ℝ)*q + 1 ≤ 2 * ((n:ℝ) * (n:ℝ)^δ) := by nlinarith [mul_le_mul_of_nonneg_left hqR hnpos.le]
      _ ≤ (n:ℝ)^δ * ((n:ℝ) * (n:ℝ)^δ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (n:ℝ)^(1 + (δ + δ)) := by rw [Real.rpow_add hnpos, Real.rpow_add hnpos, Real.rpow_one]; ring
      _ ≤ (n:ℝ)^(1+ε) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  · intro i hi j hj hij
    exact ha hi hj (Nat.add_right_cancel hij)
  · intro i hi
    obtain ⟨hl,hu,hd⟩ := hw i hi
    have hMdiv : i.val+1 ∣ M := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega,i.isLt⟩)
    change m < a i + M*(m/M) ∧ a i + M*(m/M) < m + (n*q+1) ∧ _
    exact ⟨by omega, by omega, dvd_add hd (dvd_mul_of_dvd_left hMdiv _)⟩

end OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R2
