import OMAStatements.S_oeis_a078841
import Mathlib

/-! Stable initial ranks in the rows of integers with exactly m prime factors. -/
namespace Deldor14.AlmostPrimeRanks
open Nat Finset ArithmeticFunction
private def P (m x : ℕ) : Prop := 1 ≤ x ∧ x.primeFactorsList.length=m
private instance (m : ℕ) : DecidablePred (P m) := fun x => inferInstanceAs (Decidable (1 ≤ x ∧ x.primeFactorsList.length=m))
private def c (m j : ℕ) := 2^(m-j)*3^j
private lemma mono (m : ℕ) : StrictMono (c m) := by
  apply strictMono_nat_of_lt_succ
  intro j
  by_cases hj : j < m
  · have e : m-j=(m-(j+1))+1 := by omega
    simp only [c,e,pow_succ]
    have hp : 0 < 2^(m-(j+1))*3^j := by positivity
    nlinarith
  · have ha : m-j=0 := by omega
    have hb : m-(j+1)=0 := by omega
    simp only [c,ha,hb,pow_zero,one_mul,pow_succ]
    have : 0 < 3^j := by positivity
    omega
private lemma member_c {j m : ℕ} (hj : j ≤ m) : P m (c m j) := by
  refine ⟨by change 0 < 2^(m-j)*3^j;positivity,?_⟩
  change cardFactors (2^(m-j)*3^j)=m
  rw [cardFactors_mul (by positivity) (by positivity),cardFactors_apply_prime_pow prime_two,
      cardFactors_apply_prime_pow (by decide : Nat.Prime 3)]
  omega
private lemma enough {k m : ℕ} (hk : k ≤ m) : k < count (P m) (c m k+1) := by
  rw [count_eq_card_filter_range]
  have sub : (range (k+1)).image (c m) ⊆ (range (c m k+1)).filter (P m) := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    have jk : j ≤ k := by simpa using hj
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((mono m).monotone jk)),member_c (jk.trans hk)⟩
  have b := card_le_card sub
  rw [Finset.card_image_of_injective _ (mono m).injective,card_range] at b
  exact b
private lemma admissible {k m : ℕ} (hk : k ≤ m) (hf : (Set.ofPred (P m)).Finite) : k < hf.toFinset.card :=
  (enough hk).trans_le (Nat.count_le_card hf _)
private lemma odd_bound (k : ℕ) (hp : 0 < k) (ho : ¬2 ∣ k) : 3^(cardFactors k) ≤ k := by
  have prod_bound (l : List ℕ) (h : ∀ p ∈ l, 3 ≤ p) : 3^l.length ≤ l.prod := by
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.length_cons,List.prod_cons,pow_succ']
      exact Nat.mul_le_mul (h x (by simp)) (ih (fun p hp => h p (by simp [hp])))
  rw [cardFactors_apply]
  calc
    3^k.primeFactorsList.length ≤ k.primeFactorsList.prod := prod_bound _ ?_
    _ = k := Nat.prod_primeFactorsList hp.ne'
  intro p mem
  have low := (Nat.prime_of_mem_primeFactorsList mem).two_le
  have dvd := Nat.dvd_of_mem_primeFactorsList mem
  by_contra! h
  have : p=2 := by omega
  exact ho (this ▸ dvd)
private lemma double (m x : ℕ) : P (m+1) (2*x) ↔ P m x := by
  by_cases hx : x=0
  · subst x; simp [P]
  change (1 ≤ 2*x ∧ cardFactors (2*x)=m+1) ↔ (1 ≤ x ∧ cardFactors x=m)
  rw [cardFactors_mul (by decide) hx,cardFactors_apply_prime prime_two];omega
private lemma count_double (m t : ℕ) (ht : 2*t ≤ 3^(m+1)) :
    count (P (m+1)) (2*t) = count (P m) t := by
  simp only [count_eq_card_filter_range]
  have e : (range (2*t)).filter (P (m+1)) = ((range t).filter (P m)).image (fun x => 2*x) := by
    ext y
    constructor
    · intro hy
      obtain ⟨yl,yp⟩ := mem_filter.mp hy
      have lt := mem_range.mp yl
      have even : 2 ∣ y := by
        by_contra no
        have bounds := odd_bound y yp.1 no
        have fact : cardFactors y = m+1 := yp.2
        rw [fact] at bounds
        omega
      obtain ⟨x,rfl⟩ := even
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_range.mpr (by omega),(double m x).mp yp⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      obtain ⟨xt,xp⟩ := mem_filter.mp hx
      have l := mem_range.mp xt
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),(double m x).mpr xp⟩
  rw [e,Finset.card_image_of_injective _ (fun x y h => by omega)]
/-- For every row m, the first m+1 entries of the next row double exactly. -/
theorem stable_rank (m k : ℕ) (hk : k ≤ m) : nth (P (m+1)) k=2*nth (P m) k := by
  let t := nth (P m) k
  have tb : t ≤ 3^m := by
    have q := nth_lt_of_lt_count (enough hk)
    have last := (mono m).monotone hk
    change c m k ≤ 2^(m-m)*3^m at last
    simp only [Nat.sub_self,pow_zero,one_mul] at last
    dsimp [t];omega
  have lt : 2*t ≤ 3^(m+1) := by rw [pow_succ];omega
  have mem : P m t := nth_mem _ (admissible hk)
  have cc : count (P (m+1)) (2*t)=k := (count_double m t lt).trans (count_nth (admissible hk))
  have eq := nth_count ((double m t).mpr mem)
  rw [cc] at eq
  exact eq
/-- The ratio a(n+1)/a(n) is always strictly greater than 2. -/
theorem strict_diagonal (n : ℕ) : 2*nth (P n) n < nth (P (n+1)) (n+1) := by
  rw [←stable_rank n n le_rfl]
  exact nth_lt_nth' (show n < n+1 by omega) (admissible le_rfl)
private noncomputable def b (n : ℕ) : ℝ := (nth (P n) n : ℝ)/2^n
private lemma bpos (n : ℕ) : 0 < b n := by
  have hi := (nth_mem n (admissible (m:=n) le_rfl)).1
  unfold b
  positivity
private lemma bmono : StrictMono b := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := strict_diagonal n
  dsimp [b]
  rw [pow_succ,div_lt_div_iff₀ (by positivity) (by positivity)]
  have hc : (2:ℝ)*nth (P n) n < nth (P (n+1)) (n+1) := by exact_mod_cast hs
  nlinarith [mul_lt_mul_of_pos_right hc (by positivity : (0:ℝ) < 2^n)]
private lemma realizes (m x : ℕ) (h : P m x) (hx : x ≤ 3^m) :
    ∃ j, b j=(x:ℝ)/2^m := by
  let r:=count (P m) x
  have lift (t : ℕ) : count (P (m+t)) (2^t*x) = r ∧ P (m+t) (2^t*x) ∧ 2^t*x ≤ 3^(m+t) := by
    induction t with
    | zero => simp only [Nat.add_zero,pow_zero,one_mul];exact ⟨rfl,h,hx⟩
    | succ t ih =>
      rw [show m+(t+1)=(m+t)+1 by omega,show 2^(t+1)*x=2*(2^t*x) by ring]
      have limit : 2*(2^t*x) ≤ 3^(m+t+1) := by rw [pow_succ];omega
      exact ⟨(count_double (m+t) (2^t*x) limit).trans ih.1,(double _ _).mpr ih.2.1,limit⟩
  have stretch (t : ℕ) : nth (P (r+t)) r=2^t*nth (P r) r := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show r+(t+1)=(r+t)+1 by omega,stable_rank _ _ (by omega),ih,pow_succ];ring
  have v := lift r
  have equal := nth_count v.2.1
  rw [v.1,add_comm m r,stretch] at equal
  refine ⟨r,?_⟩
  unfold b
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  exact_mod_cast (show nth (P r) r*2^m = x*2^r by simpa [Nat.mul_comm] using equal)
private lemma grid (i j : ℕ) : ∃ k, b k=(3/2:ℝ)^i*(5/2:ℝ)^j := by
  let d:=i+3*j
  let x:=3^i*20^j
  have cx : cardFactors x=d := by
    dsimp [x,d]
    rw [cardFactors_mul (by positivity) (by positivity),cardFactors_apply_prime_pow (by decide : Nat.Prime 3),cardFactors_pow]
    have h20 : cardFactors 20=3 := by
      rw [show (20:ℕ) = 2^2*5 by decide,cardFactors_mul (by decide) (by decide),
        cardFactors_apply_prime_pow Nat.prime_two,cardFactors_apply_prime (by decide : Nat.Prime 5)]
    rw [h20];omega
  have small : x ≤ 3^d := by
    dsimp [x,d]
    rw [pow_add,pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 20 ≤ 3^3) _)
  obtain ⟨k,eq⟩ := realizes d x ⟨by change 0 < 3^i*20^j;positivity,cx⟩ small
  refine ⟨k,eq.trans ?_⟩
  dsimp [x,d]
  push_cast
  rw [pow_add,pow_mul,div_pow,div_pow]
  norm_num
  field_simp
  ring_nf
  rw [←mul_pow,←mul_pow]
  norm_num

end Deldor14.AlmostPrimeRanks

namespace Deldor14.LogGrid
open Filter
open scoped Topology
/-- Positive numbers u < v produce, above a threshold, an additive mesh
with gaps at most v-u using nonnegative integer coefficients. -/
private lemma mesh (u v : ℝ) (hu : 0 < u) (hv : u < v) :
    ∃ K : ℕ, ∀ x : ℝ, K*u ≤ x → ∃ i j : ℕ, x < i*u+j*v ∧ i*u+j*v ≤ x+(v-u) := by
  let d:=v-u
  have hd : 0 < d := sub_pos.mpr hv
  obtain ⟨K,hK⟩ := exists_nat_gt (u/d+1)
  refine ⟨K,fun x hx => ?_⟩
  have xpos : 0 ≤ x := (mul_nonneg (Nat.cast_nonneg _) hu.le).trans hx
  let m:=⌊x/u⌋₊
  have hlo : (m:ℝ)*u ≤ x := (le_div_iff₀ hu).mp (Nat.floor_le (div_nonneg xpos hu.le))
  have hhi : x < ((m:ℝ)+1)*u := (div_lt_iff₀ hu).mp (Nat.lt_floor_add_one _)
  have km : K ≤ m := Nat.le_floor ((le_div_iff₀ hu).mpr hx)
  let j:=⌊(x-m*u)/d⌋₊+1
  have jhi : (x-m*u) < (j:ℝ)*d := by
    apply (div_lt_iff₀ hd).mp
    simpa [j] using Nat.lt_floor_add_one ((x-m*u)/d)
  have jlo : ((j:ℝ)-1)*d ≤ x-m*u := by
    apply (le_div_iff₀ hd).mp
    simpa [j] using Nat.floor_le (div_nonneg (sub_nonneg.mpr hlo) hd.le)
  have jK : j ≤ K := by
    have a : ((j:ℝ)-1)*d < u := by linarith
    have h := (lt_div_iff₀ hd).mpr a
    exact_mod_cast (show (j:ℝ) ≤ K by linarith)
  have jm := jK.trans km
  refine ⟨m-j,j,?_⟩
  rw [Nat.cast_sub jm]
  dsimp [d] at *
  constructor <;> nlinarith
/-- An increasing sequence containing grids with arbitrarily small positive
mesh has consecutive differences tending to zero. -/
theorem gaps {s : ℕ → ℝ} (mono : StrictMono s)
    (pairs : ∀ e : ℝ, 0 < e → ∃ u v : ℝ, 0 < u ∧ u < v ∧ v-u < e ∧
      ∀ i j : ℕ, ∃ n, s n=i*u+j*v) : Tendsto (fun n => s (n+1)-s n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨u,v,hu,hv,close,covered⟩ := pairs e he
  obtain ⟨K,grid⟩ := mesh u v hu hv
  obtain ⟨N,hN⟩ := covered K 0
  simp only [Nat.cast_zero,zero_mul,add_zero] at hN
  apply eventually_atTop.mpr
  refine ⟨N,fun n hn => ?_⟩
  have start := mono.monotone hn
  rw [hN] at start
  obtain ⟨i,j,above,near⟩ := grid (s n) start
  obtain ⟨k,hk⟩ := covered i j
  rw [←hk] at above near
  have idx := mono.lt_iff_lt.mp above
  have step := mono.monotone (show n+1 ≤ k by omega)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (sub_nonneg.mpr (mono.monotone (by omega)))]
  linarith
end Deldor14.LogGrid

namespace Deldor14.LogGrid
open Real
private lemma independent (k j : ℕ) (hk : 0 < k) :
    (k:ℝ)*log (5/2:ℝ) ≠ (j:ℝ)*log (3/2:ℝ) := by
  intro h
  rw [←log_pow,←log_pow] at h
  have eq := log_injOn_pos (show 0 < (5/2:ℝ)^k by positivity) (show 0 < (3/2:ℝ)^j by positivity) h
  rw [div_pow,div_pow,div_eq_div_iff (by positivity) (by positivity)] at eq
  have e : (5:ℕ)^k*2^j=3^j*2^k := by exact_mod_cast eq
  have dd : 5 ∣ 5^k := dvd_pow_self _ (Nat.ne_of_gt hk)
  have hd : 5 ∣ 3^j*2^k := e ▸ dvd_mul_of_dvd_left dd _
  have prime : Nat.Prime 5 := by decide
  rcases prime.dvd_mul.mp hd with h3|h2
  · exact (by decide : ¬5 ∣ 3) (prime.dvd_of_dvd_pow h3)
  · exact (by decide : ¬5 ∣ 2) (prime.dvd_of_dvd_pow h2)
private lemma close_multiples (A B e : ℝ) (ha : 0 < A) (hb : A < B) (he : 0 < e) :
    ∃ k j : ℕ, 0 < k ∧ 0 < j ∧ |(k:ℝ)*B-(j:ℝ)*A|<e := by
  obtain ⟨M,hm⟩ := exists_nat_one_div_lt (lt_min (div_pos he ha) zero_lt_one)
  have tighter : (1:ℝ)/((M+1:ℕ)+1) ≤ 1/((M:ℝ)+1) := by push_cast;gcongr <;> linarith
  obtain ⟨j,k,kp,_,approx⟩ := exists_int_int_abs_mul_sub_le (B/A) (Nat.succ_pos M)
  have bd := approx.trans_lt (tighter.trans_lt hm)
  have bd1 := bd.trans_le (min_le_right _ _)
  have bde := bd.trans_le (min_le_left _ _)
  have kl : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
  have ba : 1 < B/A := (one_lt_div ha).mpr hb
  have big : 1 < (k:ℝ)*(B/A) := lt_of_lt_of_le ba (by nlinarith [mul_nonneg (sub_nonneg.mpr kl) (le_of_lt (lt_trans zero_lt_one ba))])
  have jp : 0 < j := by
    have h := (abs_lt.mp bd1).2
    exact_mod_cast (show (0:ℝ) < j by linarith)
  refine ⟨k.toNat,j.toNat,by omega,by omega,?_⟩
  have castk : (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg kp.le
  have castj : (j.toNat:ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg jp.le
  rw [castk,castj]
  have h := (lt_div_iff₀ ha).mp bde
  calc
    |(k:ℝ)*B-(j:ℝ)*A| = |((k:ℝ)*(B/A)-j)*A| := by congr 1;field_simp
    _ = |(k:ℝ)*(B/A)-j| * A := by rw [abs_mul,abs_of_pos ha]
    _ < e := h

theorem logarithmic_pairs {s : ℕ → ℝ}
    (grid : ∀ i j : ℕ, ∃ n, s n=i*log (3/2:ℝ)+j*log (5/2:ℝ))
    (e : ℝ) (he : 0 < e) : ∃ u v : ℝ, 0 < u ∧ u < v ∧ v-u < e ∧
      ∀ i j : ℕ, ∃ n, s n=i*u+j*v := by
  let A:=log (3/2:ℝ)
  let B:=log (5/2:ℝ)
  have ha : 0 < A := log_pos (by norm_num)
  have hab : A < B := log_lt_log (by norm_num) (by norm_num)
  obtain ⟨k,j,hk,hj,close⟩ := close_multiples A B e ha hab he
  have ne : (k:ℝ)*B ≠ (j:ℝ)*A := independent k j hk
  have pa : 0 < (j:ℝ)*A := mul_pos (by exact_mod_cast hj) ha
  have pb : 0 < (k:ℝ)*B := mul_pos (by exact_mod_cast hk) (ha.trans hab)
  rcases lt_or_gt_of_ne ne with less | more
  · refine ⟨k*B,j*A,pb,less,by linarith [(abs_lt.mp close).1],?_⟩
    intro l r
    obtain ⟨n,h⟩ := grid (r*j) (l*k)
    exact ⟨n,h.trans (by push_cast;dsimp [A,B];ring)⟩
  · refine ⟨j*A,k*B,pa,more,(abs_lt.mp close).2,?_⟩
    intro l r
    obtain ⟨n,h⟩ := grid (l*j) (r*k)
    exact ⟨n,h.trans (by push_cast;dsimp [A,B];ring)⟩
end Deldor14.LogGrid

namespace Deldor14.AlmostPrimeRanks
open Real Filter OMA.S_oeis_a078841
open scoped Topology
theorem wilson : type_of% @OMA.S_oeis_a078841.main := by
  let s (n:ℕ) := log (b n)
  have hs : StrictMono s := fun i j ij => log_lt_log (bpos _) (bmono ij)
  have cover (i j : ℕ) : ∃ n, s n = i*log (3/2:ℝ)+j*log (5/2:ℝ) := by
    obtain ⟨n,hn⟩ := grid i j
    refine ⟨n,?_⟩
    dsimp [s];rw [hn,log_mul (by positivity) (by positivity),log_pow,log_pow]
  have gaps := Deldor14.LogGrid.gaps hs (Deldor14.LogGrid.logarithmic_pairs cover)
  have lim := ((Real.continuous_exp.tendsto 0).comp gaps).const_mul 2
  simp only [exp_zero,mul_one] at lim
  refine lim.congr (fun n => ?_)
  change 2*exp (log (b (n+1))-log (b n))= _
  rw [exp_sub,exp_log (bpos _),exp_log (bpos _)]
  change 2*(((a (n+1):ℝ)/2^(n+1))/((a n:ℝ)/2^n)) = _
  rw [pow_succ]
  field_simp
end Deldor14.AlmostPrimeRanks
theorem OMA.solution : type_of% @OMA.S_oeis_a078841.main := Deldor14.AlmostPrimeRanks.wilson
