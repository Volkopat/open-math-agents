import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib

/-! Classify higher-power successors and discharge the higher-power step with threshold zero. -/
/- The effective bound refines the argument of @MrSeizy in #23442, commit f7262ba898537178015c15584f3cf24431c39961. The new window has length B^12, the cells have width B^2, and the approximation order is 146t. -/
/-
# Finiteness of the even exceptions for Erdős 889

For an exceptional starting value, every prime up to P that does not divide n
has a distinct first multiple in (n,n+P] whose prime factors are all at most P.
The first-hit argument uses the two-prime observation of @rorcores in the
merged sibling proof OMA.E889.one_lt_v₀_of_two_primes.

Take P to be a sufficiently large fixed power of the binary logarithmic
scale of n. Discard the few hits with large residual cofactor. A prime power
above P can occur at only one hit, so many of the remaining hits are small
multiples of a single large prime power. Grouping their bases and exponents
would give two nearby weighted powers that the polynomial estimate excludes.
-/

namespace Erdos889.EffectiveBound
open Finset Polynomial

/-- Each step multiplies the coefficient at degree j by j minus the selected degree. -/
private noncomputable def strip (s : ℕ) (f : ℤ[X]) : ℕ → ℤ[X]
  | 0 => f
  | i+1 => X * (strip s f i).derivative - C ((s : ℤ)+i) * strip s f i

private lemma strip_coeff (s j : ℕ) (f : ℤ[X]) (i : ℕ) :
    (strip s f i).coeff j = f.coeff j * ∏ l ∈ range i, ((j : ℤ) - (s+l)) := by
  induction i with
  | zero => simp [strip]
  | succ i ih =>
    simp only [strip, coeff_sub, coeff_C_mul, prod_range_succ]
    have h (g : ℤ[X]) : (X * g.derivative).coeff j = j * g.coeff j := by
      cases j with
      | zero => simp
      | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
    rw [h, ih]
    ring

private lemma strip_dvd (s i b : ℕ) (g f : ℤ[X]) (h : g ^ (b+i) ∣ f) :
    g ^ b ∣ strip s f i := by
  induction i generalizing b with
  | zero => simpa [strip] using h
  | succ i ih =>
    obtain ⟨w, hw⟩ := ih (b+1) (by rwa [show b+1+i = b+(i+1) by omega])
    rw [strip, hw, derivative_mul, derivative_pow_succ]
    refine dvd_sub ?_ ?_
    · apply dvd_mul_of_dvd_right
      apply dvd_add
      · apply dvd_mul_of_dvd_left; apply dvd_mul_of_dvd_left; exact dvd_mul_left _ _
      · exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _) _


private lemma binomial_tail (N b u h : ℕ) (hb : b ≤ N) :
    ∑ j ∈ Ico b (N+1), h^j * u^(N-j) * N.choose j ≤
      N^b * h^b * (h+u)^(N-b) := by
  rw [add_pow, mul_sum, sum_Ico_eq_sum_range, show N+1-b=N-b+1 by omega]
  apply sum_le_sum
  intro j hj
  have hc : N.choose (b+j) ≤ N^b * (N-b).choose j := calc
    _ ≤ N.choose (b+j) * (b+j).choose b := Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega))
    _ = _ := by rw [Nat.choose_mul (by omega : b ≤ b+j), Nat.add_sub_cancel_left]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
  rw [pow_add]
  calc
    _ ≤ (h^b*h^j) * u^(N-(b+j)) * (N^b*(N-b).choose j) := Nat.mul_le_mul_left _ hc
    _ = _ := by rw [Nat.sub_sub]; simp only [Nat.cast_id]; ring

/-- Apply the Euler operators at degrees d+1 through 2d to the binomial of
degree a+d. Its evaluation at h is divisible by (u+h)^a. The terms through
degree d are divisible by u^a, and all remaining nonzero terms are positive.
The first and last estimates on this tail give the integer separation below. -/
private lemma nearby_power_approx (a d u h : ℕ) (ha : d+1 ≤ a) (hu : 0 < u) (hh : 0 < h) :
    ∃ U V E : ℤ,
      ((u+h : ℕ) : ℤ)^a * V - (u : ℤ)^a * U = E ∧
      (u : ℤ)^(a-d-1) ≤ E ∧
      E ≤ ((a+d : ℕ) : ℤ)^(d+(2*d+1)) * (h : ℤ)^(2*d+1) *
        ((u+h : ℕ) : ℤ)^(a-d-1) ∧
      |V| ≤ (((a+d)*(u+h) : ℕ) : ℤ)^d := by
  let N := a+d
  let b := 2*d+1
  let v := u+h
  have hb : b ≤ N := by dsimp [N,b]; omega
  let f := strip (d+1) ((X+C (u : ℤ))^N) d
  let w (j : ℕ) := ∏ l ∈ range d, ((j : ℤ) - ((d+1 : ℕ)+ (l:ℤ)))
  let T (j : ℕ) := (h : ℤ)^j * (u : ℤ)^(N-j) * (N.choose j : ℤ) * w j
  have hf (j : ℕ) : f.coeff j * (h : ℤ)^j = T j := by
    simp only [f, strip_coeff, coeff_X_add_C_pow, w, T]; ring
  have hdeg : f.natDegree ≤ N := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp only [f, strip_coeff, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, mul_zero, zero_mul]
  obtain ⟨g,hg⟩ := strip_dvd (d+1) d a (X+C (u:ℤ)) ((X+C (u:ℤ))^N) (dvd_refl _)
  let V := g.eval (h:ℤ)
  have hs : (v:ℤ)^a * V = ∑ j ∈ range (N+1), T j := by
    calc
      _ = f.eval (h:ℤ) := by simp [f,hg,V,v,add_comm]
      _ = _ := by rw [eval_eq_sum_range' (by omega : f.natDegree < N+1)]; simp_rw [hf]
  have low : (u:ℤ)^a ∣ ∑ j ∈ range b, T j := by
    apply dvd_sum
    intro j hj
    have hj' := mem_range.mp hj
    by_cases hjd : j ≤ d
    · have he : a ≤ N-j := by dsimp [N]; omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow _ he) _) _) _
    · have hz : w j = 0 := by
        apply prod_eq_zero (i := j-(d+1)) (mem_range.mpr ?_)
        · have he : j-(d+1)+(d+1) = j := by omega
          exact_mod_cast (show (j:ℤ)-((d+1:ℕ)+(↑(j-(d+1)):ℤ))=0 by omega)
        · dsimp [b] at hj'; omega
      simp [T,hz]
  obtain ⟨U,hU⟩ := low
  let E := ∑ j ∈ Ico b (N+1), T j
  have hsplit := sum_range_add_sum_Ico T (by omega : b ≤ N+1)
  have hw (j : ℕ) (hj : j ≤ N) : |w j| ≤ (N:ℤ)^d := by
    dsimp only [w]; rw [abs_prod]
    have hh₁ : ∀ l ∈ range d, |(j:ℤ)-((d+1:ℕ)+(l:ℤ))| ≤ N := by
      intro l hl
      have := mem_range.mp hl
      dsimp [b] at hb
      exact abs_le.mpr ⟨by omega, by omega⟩
    simpa using prod_le_prod (fun l _ => abs_nonneg _) hh₁
  have hwpos (j : ℕ) (hj : b ≤ j) : 1 ≤ w j := by
    apply Finset.one_le_prod
    intro l hl
    have := mem_range.mp hl
    dsimp [b] at hj
    omega
  have hwT (j : ℕ) (hj : j ≤ N) :
      |T j| ≤ (N:ℤ)^d * ((h:ℤ)^j * (u:ℤ)^(N-j) * N.choose j) := by
    simp only [T, abs_mul, abs_pow, abs_of_nonneg (Int.natCast_nonneg _)]
    rw [mul_comm ((N:ℤ)^d)]
    exact mul_le_mul_of_nonneg_left (hw j hj) (by positivity)
  have htail₀ (j : ℕ) (hj : b ≤ j) (hj' : j ≤ N) : (u:ℤ)^(N-j) ≤ T j := by
    have hc : (1:ℤ) ≤ N.choose j := by exact_mod_cast Nat.choose_pos hj'
    have hh' : (1:ℤ) ≤ (h:ℤ)^j := one_le_pow₀ (by exact_mod_cast hh)
    dsimp [T]
    calc
      _ = 1 * (u:ℤ)^(N-j) * 1 * 1 := by ring
      _ ≤ _ := by gcongr; exact hwpos _ hj
  refine ⟨U,V,E,?_,?_,?_,?_⟩
  · change (v:ℤ)^a * V - (u:ℤ)^a * U = E
    dsimp [E]; omega
  · have hsingle := single_le_sum (f := T) (fun i hi => (by positivity : 0 ≤ (u:ℤ)^(N-i)).trans
        (htail₀ i (mem_Ico.mp hi).1 (by have := (mem_Ico.mp hi).2; omega))) (mem_Ico.mpr ⟨le_rfl, (show b < N+1 by omega)⟩)
    simpa [N,b, show a+d-(2*d+1) = a-d-1 by omega] using (htail₀ b le_rfl hb).trans hsingle
  · calc
      E ≤ ∑ j ∈ Ico b (N+1), (N:ℤ)^d * ((h:ℤ)^j * (u:ℤ)^(N-j) * N.choose j) :=
        sum_le_sum fun j hj => (le_abs_self _).trans (hwT _ (by have := (mem_Ico.mp hj).2; omega))
      _ = _ := (mul_sum ..).symm
      _ ≤ (N:ℤ)^d * ((N:ℤ)^b * (h:ℤ)^b * ((h+u:ℕ):ℤ)^(N-b)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); exact_mod_cast binomial_tail N b u h hb
      _ = _ := by rw [show N-b=a-d-1 by dsimp [N,b]; omega, Nat.add_comm h u, pow_add]; dsimp [N,b]; ring
  · have hsum : |(v:ℤ)^a * V| ≤ (N:ℤ)^d * (v:ℤ)^N := by
      rw [hs]
      calc
        _ ≤ _ := abs_sum_le_sum_abs _ _
        _ ≤ _ := sum_le_sum (fun j hj => hwT j (by have := mem_range.mp hj; omega))
        _ = _ := by rw [← mul_sum]; congr 1; simp [v, Nat.cast_add, add_comm (u:ℤ), add_pow]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (v:ℤ)^a)] at hsum
    have H : (v:ℤ)^a * |V| ≤ (v:ℤ)^a * ((N:ℤ)*(v:ℤ))^d := by
      convert hsum using 1; dsimp [N]; rw [pow_add,mul_pow]; ring
    exact (le_of_mul_le_mul_left H (by dsimp [v]; positivity))

/-- A sufficiently close pair would give a positive multiple of c*u^a strictly
below c*u^a, using the integer coefficients of the approximation. -/
private lemma short_power_gap (B d a u h c e : ℕ)
    (hB : 2 ≤ B) (ha : (5*d+6)/2 ≤ a) (hN : a+d ≤ B)
    (hu : B^11 ≤ u) (hv : u+h ≤ B^12) (hh : 0 < h) (hsmall : h ≤ B^2)
    (hc : 0 < c) (he : 0 < e) (hc' : c ≤ B^(2*d)) (he' : e ≤ B^(2*d)) :
    ¬ |(c*u^a : ℕ) - ((e*(u+h)^a : ℕ) : ℤ)| ≤ (B:ℤ)^12 := by
  intro hclose
  let v := u+h
  let N := a+d
  let b := 2*d+1
  let r := a-d-1
  have har : a = r+(d+1) := by dsimp [r]; omega
  have h4 : 4 ≤ B^2 := by nlinarith
  have hbig : 4*c*e*N^(d+b)*h^b < v^(d+1) := calc
    _ ≤ B^2*B^(2*d)*B^(2*d)*B^(d+b)*(B^2)^b := by gcongr
    _ = B^(2+2*d+2*d+(d+b)+2*b) := by simp only [pow_add,pow_mul]
    _ < (B^11)^(d+1) := by rw [← pow_mul]; apply Nat.pow_lt_pow_right (by omega); dsimp [b]; omega
    _ ≤ _ := Nat.pow_le_pow_left (by dsimp [v]; omega) _
  have hlow : 4*c*(N*v)^d*B^12 < u^r := calc
    _ ≤ B^2*B^(2*d)*(B*B^12)^d*B^12 := by gcongr
    _ = B^(2+2*d+(1+12)*d+12) := by simp only [pow_add,pow_mul,pow_one]
    _ < (B^11)^r := by rw [← pow_mul]; apply Nat.pow_lt_pow_right (by omega); dsimp [r]; omega
    _ ≤ _ := Nat.pow_le_pow_left hu _
  have hupos : 0 < u := lt_of_lt_of_le (pow_pos (by omega : 0 < B) _) hu
  obtain ⟨U,V,E,hid,hEₗ,hEᵤ,hV⟩ := nearby_power_approx a d u h (by omega) hupos hh
  change (v:ℤ)^a*V - (u:ℤ)^a*U = E at hid
  change (u:ℤ)^r ≤ E at hEₗ
  change E ≤ (N:ℤ)^(d+b)*(h:ℤ)^b*(v:ℤ)^r at hEᵤ
  push_cast at hV hclose
  change |V| ≤ ((N:ℤ)*(v:ℤ))^d at hV
  change |(c:ℤ)*(u:ℤ)^a - (e:ℤ)*(v:ℤ)^a| ≤ (B:ℤ)^12 at hclose
  have hl : 4*(c:ℤ)*|V| *(B:ℤ)^12 < (u:ℤ)^r := by
    apply lt_of_le_of_lt _ (by exact_mod_cast hlow : (4:ℤ)*c*((N:ℤ)*v)^d*(B:ℤ)^12 < (u:ℤ)^r)
    gcongr
  have hbE : 4*(c:ℤ)*e*E < (v:ℤ)^a := calc
    _ ≤ 4*(c:ℤ)*e*((N:ℤ)^(d+b)*(h:ℤ)^b*(v:ℤ)^r) := by gcongr
    _ = (4*(c:ℤ)*e*(N:ℤ)^(d+b)*(h:ℤ)^b)*(v:ℤ)^r := by ring
    _ < (v:ℤ)^(d+1)*(v:ℤ)^r := by
      apply mul_lt_mul_of_pos_right _ (by dsimp [v]; positivity); exact_mod_cast hbig
    _ = _ := by rw [← pow_add]; congr 1; omega
  have hur : (u:ℤ)^r ≤ (u:ℤ)^a := pow_le_pow_right₀ (by exact_mod_cast hupos) (by omega)
  have hc1 : (1:ℤ) ≤ c := by exact_mod_cast hc
  have he1 : (1:ℤ) ≤ e := by exact_mod_cast he
  let x : ℤ := c*(u:ℤ)^a
  let y : ℤ := e*(v:ℤ)^a
  let M : ℤ := (c:ℤ)*e*E
  let err : ℤ := (c:ℤ)*V*(x-y)
  have hx : (u:ℤ)^a ≤ x := le_mul_of_one_le_left (by positivity) hc1
  have hy : (v:ℤ)^a ≤ y := le_mul_of_one_le_left (by positivity) he1
  have hM : E ≤ M := le_mul_of_one_le_left (le_trans (by positivity) hEₗ)
    (one_le_mul_of_one_le_of_one_le hc1 he1)
  have herr : |err| ≤ (c:ℤ)*|V| *(B:ℤ)^12 := by
    dsimp [err]; simp only [abs_mul, abs_of_nonneg (Int.natCast_nonneg c)]
    exact mul_le_mul_of_nonneg_left hclose (by positivity)
  have hdist : (B:ℤ)^12 < x := by
    have hnv : 0 < (N*v)^d := pow_pos (Nat.mul_pos (by dsimp [N]; omega) (by dsimp [v]; omega)) _
    have hh' : B^12 < u^r := by
      apply lt_of_le_of_lt _ hlow
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact (by exact_mod_cast hh' : (B:ℤ)^12 < (u:ℤ)^r).trans_le (hur.trans hx)
  change |x-y| ≤ _ at hclose
  have hid' : x * (c*V - e*U) = M+err := by
    dsimp [M,err,x,y]; rw [← hid]; ring
  have hstrict : 0 < M+err ∧ M+err < x := by
    have hse : -|err| ≤ err := neg_abs_le _
    have hse' := le_abs_self err
    have hd := abs_le.mp hclose
    have hm4 : 4*M < (v:ℤ)^a := by dsimp [M]; linarith only [hbE]
    have he4 : 4*((c:ℤ)*|V| *(B:ℤ)^12) < (u:ℤ)^r := by linarith only [hl]
    constructor <;> omega
  have hz : 1 ≤ (c:ℤ)*V-e*U := by
    by_contra! H
    have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by omega) (show (c:ℤ)*V-e*U ≤ 0 by omega)
    omega
  have := le_mul_of_one_le_right (show 0 ≤ x by omega) hz
  omega

private def giants (P x : ℕ) := P.primesLE.filter (fun q => P < q ^ x.factorization q)
private def smallExp (P x q : ℕ) := if q ^ x.factorization q ≤ P then x.factorization q else 0
private def residue (P x : ℕ) := ∏ q ∈ P.primesLE, q ^ smallExp P x q

private lemma residue_pos (P x : ℕ) : 0 < residue P x :=
  prod_pos fun _ hq => pow_pos (Nat.mem_primesLE.mp hq).2.pos _

private lemma split_residue {P x : ℕ} (hx : x ≠ 0) (hs : x.primeFactors ⊆ P.primesLE) :
    residue P x * (∏ q ∈ giants P x, q ^ x.factorization q) = x := by
  have hd : residue P x = ∏ q ∈ P.primesLE with ¬ P < q ^ x.factorization q, q ^ x.factorization q := by
    simp [residue, smallExp, prod_filter]
  rw [hd, mul_comm, giants, prod_filter_mul_prod_filter_not]
  rw [← prod_subset hs (fun q _ hq => by
    have : x.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    simp [this])]
  exact Nat.prod_factorization_pow_eq_self hx

private lemma interval_count {P n m : ℕ} (hm : 0 < m) (hmP : m ≤ P) :
    ((Ioc n (n+P)).filter fun x => m ∣ x).card ≤ P/m+1 := by
  have hsub : (Ioc 0 n).filter (fun x => m ∣ x) ⊆ (Ioc 0 (n+P)).filter (fun x => m ∣ x) := by
    intro x hx
    simp only [mem_filter,mem_Ioc] at hx ⊢; omega
  have he : (Ioc n (n+P)).filter (fun x => m ∣ x) =
      ((Ioc 0 (n+P)).filter fun x => m ∣ x) \ ((Ioc 0 n).filter fun x => m ∣ x) := by
    ext x
    simp only [mem_filter, mem_Ioc, mem_sdiff]; omega
  rw [he,card_sdiff_of_subset hsub, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.add_div hm]
  have := Nat.div_pos hmP hm
  split <;> omega

private lemma residual_exp_le {P n q : ℕ} (hP : P ≠ 0) (hq : q.Prime) (S : Finset ℕ)
    (hS : S ⊆ Ioc n (n+P)) :
    ∑ x ∈ S, smallExp P x q ≤ P.factorial.factorization q + Nat.log q P := by
  let L := Nat.log q P
  have he (x : ℕ) : smallExp P x q ≤ L := by
    dsimp [smallExp]; split
    · exact Nat.le_log_of_pow_le hq.one_lt ‹_›
    · omega
  have hex (x : ℕ) : smallExp P x q = ∑ i ∈ Ico 1 (L+1), if i ≤ smallExp P x q then 1 else 0 := by
    rw [sum_boole]
    have H : (Ico 1 (L+1)).filter (fun i => i ≤ smallExp P x q) = Ico 1 (smallExp P x q+1) := by
      ext i; simp only [mem_filter,mem_Ico]; have := he x; omega
    simp [H,Nat.card_Ico]
  rw [sum_congr rfl (fun x _ => hex x)]
  rw [sum_comm,Nat.factorization_factorial hq (Nat.lt_succ_self L)]
  have ones : (∑ _i ∈ Ico 1 (L+1), (1:ℕ))=L := by simp [Nat.card_Ico]
  change _ ≤ _ + L
  conv_rhs => rhs; rw [← ones]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  rw [sum_boole]
  have hsub : S.filter (fun x => i ≤ smallExp P x q) ⊆ (Ioc n (n+P)).filter (fun x => q^i ∣ x) := by
    intro x hx
    obtain ⟨hxS,he⟩ := mem_filter.mp hx
    have hxI := mem_Ioc.mp (hS hxS)
    apply mem_filter.mpr ⟨hS hxS, (hq.pow_dvd_iff_le_factorization (by omega)).mpr ?_⟩
    dsimp [smallExp] at he
    split at he <;> omega
  apply (card_le_card hsub).trans
  apply interval_count (pow_pos hq.pos _)
  have := (mem_Ico.mp hi).2
  exact (Nat.pow_le_pow_right hq.pos (by omega : i ≤ L)).trans (Nat.pow_log_le_self _ hP)

/-- For each prime, count its powers up to P across the interval. A modulus
m ≤ P has at most floor(P/m)+1 multiples there. Legendre's formula supplies the
factorial term, leaving at most one extra power q^floor(log_q P) for that prime. -/
private lemma residual_product {P n : ℕ} (hP : P ≠ 0) (S : Finset ℕ) (hS : S ⊆ Ioc n (n+P)) :
    ∏ x ∈ S, residue P x ≤ P.factorial*P^P.primesLE.card := by
  simp only [residue, prod_comm (s := S) (t := P.primesLE), Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ ∏ q ∈ P.primesLE, q ^ (P.factorial.factorization q + Nat.log q P) := by
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro q hq
      exact Nat.pow_le_pow_right (Nat.mem_primesLE.mp hq).2.pos (residual_exp_le hP (Nat.mem_primesLE.mp hq).2 S hS)
    _ ≤ _ := by
      simp only [pow_add,prod_mul_distrib]
      apply Nat.mul_le_mul
      · apply le_of_eq
        have hsub : P.factorial.primeFactors ⊆ P.primesLE := by
          intro q hq
          obtain ⟨hqp,hqd,_⟩ := Nat.mem_primeFactors.mp hq
          exact Nat.mem_primesLE.mpr ⟨(hqp.dvd_factorial.mp hqd), hqp⟩
        rw [← prod_subset hsub (fun q _ hq => by
          have h : P.factorial.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
          simp [h])]
        exact Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero _)


      · calc
          _ ≤ ∏ _q ∈ P.primesLE, P :=
            prod_le_prod (fun _ _ => Nat.zero_le _) (fun q _ => Nat.pow_log_le_self q hP)
          _ = _ := by simp

private def smoothHits (n P : ℕ) :=
  (Ioc n (n+P)).filter (fun x => x.primeFactors ⊆ P.primesLE)

private lemma card_hits {n P : ℕ} (hnP : P^2 < n)
    (hwin : ∀ k : ℕ, 1 ≤ k → k^2 < n →
      ((n+k).primeFactors.filter fun q => k < q).card ≤ 1) :
    P.primesLE.card ≤ (smoothHits n P).card + n.primeFactors.card := by
  classical
  let D := P.primesLE.filter (fun p => ¬ p ∣ n)
  let k (p : ℕ) := p - n%p
  have hhit (p : ℕ) (hp : p ∈ D) :
      n+k p ∈ smoothHits n P ∧ p ∣ n+k p ∧ k p < p := by
    obtain ⟨hmem,hnd⟩ := mem_filter.mp hp
    obtain ⟨hpP,hprime⟩ := Nat.mem_primesLE.mp hmem
    have hrem := Nat.mod_lt n hprime.pos
    have hrem₁ : n%p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hk : 0 < k p ∧ k p < p := by dsimp [k]; omega
    have hplus : n+k p = p*(n/p+1) := by
      rw [Nat.mul_add,Nat.mul_one]; dsimp [k]; have := Nat.mod_add_div n p; omega
    have hpd : p ∣ n+k p := hplus ▸ dvd_mul_right _ _
    have hc := hwin (k p) hk.1 ((Nat.pow_le_pow_left (by omega : k p ≤ P) 2).trans_lt hnP)
    have hpm : p ∈ (n+k p).primeFactors.filter (fun r => k p < r) := mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hprime,hpd,by omega⟩, hk.2⟩
    refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,?_⟩,hpd,hk.2⟩
    intro q hq
    apply Nat.mem_primesLE.mpr ⟨?_,(Nat.mem_primeFactors.mp hq).1⟩
    by_contra! H
    have := card_le_one.mp hc p hpm q (mem_filter.mpr ⟨hq,by omega⟩)
    omega
  have hcard := card_le_card_of_injOn (s := D) (t := smoothHits n P) (fun p => n+k p)
    (fun p hp => (hhit p hp).1) (by
      intro p hp q hq heq
      have hpc := (hhit p hp).2; have hqc := (hhit q hq).2
      have hP := Nat.mem_primesLE.mp (mem_filter.mp hp).1
      have hQ := Nat.mem_primesLE.mp (mem_filter.mp hq).1
      change n+k p = n+k q at heq
      have hk : k p = k q := by omega
      have hkp : 0 < k p := by dsimp [k]; have := Nat.mod_lt n hP.2.pos; omega
      have hc := hwin (k p) hkp ((Nat.pow_le_pow_left (by omega : k p ≤ P) 2).trans_lt hnP)
      rw [← hk] at hqc
      exact card_le_one.mp hc p (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hP.2,hpc.1,by omega⟩,hpc.2⟩)
        q (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hQ.2,hqc.1,by omega⟩,hqc.2⟩))
  have HD : P.primesLE \ D ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := mem_sdiff.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp hp₁).2, by simpa [D,hp₁] using hp₂, by omega⟩
  have := card_le_card HD
  rw [card_sdiff_of_subset (show D ⊆ P.primesLE from filter_subset ..)] at this
  omega

private lemma primeFactors_count {n : ℕ} (hn : n ≠ 0) : n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by decide)
  calc
    2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := prod_le_prod (fun _ _ => by decide) (fun _ hp => (Nat.mem_primeFactors.mp hp).1.two_le)
    _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)

private lemma disjoint_giants {P n x y : ℕ} (hx : x ∈ Ioc n (n+P)) (hy : y ∈ Ioc n (n+P))
    (hne : x ≠ y) : Disjoint (giants P x) (giants P y) := by
  rw [disjoint_left]
  intro q hqx hqy
  obtain ⟨hxp,hxg⟩ := mem_filter.mp hqx
  obtain ⟨_,hyg⟩ := mem_filter.mp hqy
  have hq := (Nat.mem_primesLE.mp hxp).2
  obtain ⟨hx₁,hx₂⟩ := mem_Ioc.mp hx; obtain ⟨hy₁,hy₂⟩ := mem_Ioc.mp hy
  let m := min (x.factorization q) (y.factorization q)
  have hxD : q^m ∣ x := (hq.pow_dvd_iff_le_factorization (by omega)).mpr (min_le_left ..)
  have hyD : q^m ∣ y := (hq.pow_dvd_iff_le_factorization (by omega)).mpr (min_le_right ..)
  have hlarge : P < q^m := by
    dsimp [m]; rcases le_total (x.factorization q) (y.factorization q) with he|he
    · simpa [min_eq_left he] using hxg
    · simpa [min_eq_right he] using hyg
  rcases lt_or_gt_of_ne hne with h|h
  · have := Nat.le_of_dvd (by omega : 0 < y-x) (Nat.dvd_sub hyD hxD); omega
  · have := Nat.le_of_dvd (by omega : 0 < x-y) (Nat.dvd_sub hxD hyD); omega

private lemma giant_budget {P n : ℕ} (S : Finset ℕ) (hS : S ⊆ Ioc n (n+P)) :
    ∑ x ∈ S, (giants P x).card ≤ P.primesLE.card := by
  rw [← card_biUnion (fun x hx y hy hne => disjoint_giants (hS hx) (hS hy) hne)]
  exact card_le_card (biUnion_subset.mpr fun _ _ => filter_subset ..)

private lemma primes_lower (L : ℕ) (hL : 0 < L) :
    2^L ≤ L*(2^L).primesLE.card+(L+1) := by
  let P := (2:ℕ)^L
  have hP : 1 < P := Nat.one_lt_two_pow hL.ne'
  have hc := Chebyshev.pi_ge P
  have hl : 0 < Real.log (P:ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hc' := (div_le_iff₀ hl).mp hc
  have hlog : Real.log (P:ℝ) = L*Real.log 2 := by simp [P,Real.log_pow]
  have hlog' : Real.log (P+1:ℝ) ≤ Real.log (P:ℝ) + Real.log 2 := by
    rw [← Real.log_mul (by positivity : (P:ℝ) ≠ 0) (by norm_num)]
    apply Real.log_le_log (by positivity); have : (1:ℝ) ≤ P := by exact_mod_cast hP.le
    linarith
  have h₂ := Real.log_pos (by norm_num : (1:ℝ) < 2)
  rw [hlog] at hlog' hc'
  rw [← Nat.primesLE_card_eq_primeCounting] at hc'
  change P ≤ L*P.primesLE.card + (L+1)
  have h : (P:ℝ)*Real.log 2 ≤ ((L:ℝ)*P.primesLE.card + (L+1))*Real.log 2 := by
    linarith only [hc',hlog']
  exact_mod_cast (le_of_mul_le_mul_right h h₂)

private def base (P x : ℕ) := (giants P x).sup id

private lemma base_single {P x : ℕ} (h : (giants P x).card = 1) :
    giants P x = {base P x} := by
  obtain ⟨q,hq⟩ := card_eq_one.mp h
  simp [base,hq]

/-- A singleton hit with large base is determined by its exponent and the
quotient of its base by B^2. The separation lemma proves injectivity. -/
private lemma singles_bound {B t d n : ℕ} (hB : 2 ≤ B) (hBt : B=2^t)
    (hlo : 2^B ≤ n) (hhi : n+B^12 < 2^(3*B)) (hN : 4*d ≤ B)
    (hexp : t*(2*d)+12*t*(((5*d+6)/2)) < B)
    (T : Finset ℕ) (hT : T ⊆ smoothHits n (B^12))
    (hres : ∀ x ∈ T, residue (B^12) x ≤ B^(2*d))
    (hone : ∀ x ∈ T, (giants (B^12) x).card = 1) :
    T.card ≤ B^11+(B^10+1)*(3*B+1) := by
  classical
  let P := B^12
  let q := base P
  let a (x : ℕ) := x.factorization (q x)
  let c := residue P
  have hxI {x : ℕ} (hx : x ∈ T) := (mem_filter.mp (hT hx)).1
  have qmem {x : ℕ} (hx : x ∈ T) : q x ∈ giants P x := by
    rw [base_single (hone x hx)]; exact mem_singleton_self _
  have hrepr {x : ℕ} (hx : x ∈ T) : c x * q x ^ a x = x := by
    have hlo' := (mem_Ioc.mp (hxI hx)).1
    have H := split_residue (by omega : x ≠ 0) (mem_filter.mp (hT hx)).2
    rw [base_single (hone x hx), prod_singleton] at H
    exact H
  have qbound {x : ℕ} (hx : x ∈ T) := Nat.mem_primesLE.mp (mem_filter.mp (qmem hx)).1
  have hqa {x : ℕ} (hx : x ∈ T) : a x ≤ 3*B := by
    have hpow : 2^a x ≤ q x ^ a x := Nat.pow_le_pow_left (qbound hx).2.two_le _
    have hrepr' := hrepr hx
    have hc := residue_pos P x
    have hu := (mem_Ioc.mp (hxI hx)).2
    have hxle : 2^a x ≤ x := hpow.trans ((Nat.le_mul_of_pos_left _ hc).trans_eq hrepr')
    by_contra! H
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3*B ≤ a x)
    omega
  have hqa' {x : ℕ} (hx : x ∈ T) : ((5*d+6)/2) ≤ a x := by
    by_contra! h
    have hP : P = 2^(12*t) := by dsimp [P]; rw [hBt,← pow_mul]; congr 1; omega
    have hle : x ≤ 2^(t*(2*d)+12*t*(((5*d+6)/2))) := calc
      _ = c x * q x ^ a x := (hrepr hx).symm
      _ ≤ B^(2*d) * P ^ (((5*d+6)/2)) := by
        apply Nat.mul_le_mul (hres x hx)
        exact (Nat.pow_le_pow_left (qbound hx).1 _).trans (Nat.pow_le_pow_right (by dsimp [P]; positivity) h.le)
      _ = _ := by simp only [hP,hBt,pow_add,pow_mul]
    have ht := Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
    have := (mem_Ioc.mp (hxI hx)).1
    omega
  have hinj {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T) (heq : q x = q y) : x=y := by
    by_contra h
    exact (disjoint_left.mp (disjoint_giants (hxI hx) (hxI hy) h) (qmem hx)) (heq ▸ qmem hy)
  let S := T.filter (fun x => q x < B^11)
  have hsm : S.card ≤ B^11 := by
    rw [← card_range (B^11)]
    apply card_le_card_of_injOn q (fun x hx => mem_range.mpr (mem_filter.mp hx).2)
    intro x hx y hy; exact hinj (mem_filter.mp hx).1 (mem_filter.mp hy).1
  let R := T \ S
  let H := B^2
  let key (x : ℕ) := (q x / H, a x)
  have hR {x : ℕ} (hx : x ∈ R) : x ∈ T ∧ B^11 ≤ q x := by
    obtain ⟨hx,hn⟩ := mem_sdiff.mp hx
    exact ⟨hx,by simpa [S,hx] using hn⟩
  have hcoll {x y : ℕ} (hxR : x ∈ R) (hyR : y ∈ R) (hkey : key x = key y) :
      ¬ q x < q y := by
    intro hlt
    obtain ⟨hx,hqx⟩ := hR hxR
    obtain ⟨hy,_⟩ := hR hyR
    have hj : q x / H = q y / H := congrArg Prod.fst hkey
    have he : a x = a y := congrArg Prod.snd hkey
    let h := q y - q x
    have hadd : q x + h = q y := by dsimp [h]; omega
    have hh : h ≤ H := by
      have h₁ := Nat.mod_add_div (q x) H; have h₂ := Nat.mod_add_div (q y) H
      rw [hj] at h₁
      have := Nat.mod_lt (q y) (show 0 < H by dsimp [H]; positivity)
      dsimp [h]; omega
    have q16 : 16 ≤ q x := by
      have z := Nat.pow_le_pow_left hB 11
      norm_num at z
      omega
    have power4 : 2^(4*a x) ≤ x := calc
      _ = 16^(a x) := by rw [pow_mul]; rfl
      _ ≤ (q x)^(a x) := Nat.pow_le_pow_left q16 _
      _ ≤ c x * (q x)^(a x) := Nat.le_mul_of_pos_left _ (residue_pos _ _)
      _ = _ := hrepr hx
    have close := (mem_Ioc.mp (hxI hx)).2
    have ax : 4*a x < 3*B := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (power4.trans_lt (close.trans_lt hhi))
    have hgap := short_power_gap B d (a x) (q x) h (c x) (c y) hB (hqa' hx)
      (by omega) hqx (hadd ▸ (qbound hy).1) (by dsimp [h]; omega) hh
      (residue_pos _ _) (residue_pos _ _) (hres x hx)
      (hres y hy)
    rw [hadd,hrepr hx,he,hrepr hy] at hgap
    have hxi := mem_Ioc.mp (hxI hx); have hyi := mem_Ioc.mp (hxI hy)
    apply hgap
    have H₁ : (x:ℤ) ≤ n+(B:ℤ)^12 := by exact_mod_cast hxi.2
    have H₂ : (y:ℤ) ≤ n+(B:ℤ)^12 := by exact_mod_cast hyi.2
    exact abs_le.mpr ⟨by omega,by omega⟩
  have hcard : R.card ≤ ((range (B^10+1)) ×ˢ (range (3*B+1))).card := by
    apply card_le_card_of_injOn key
    · intro x hx
      have hp := (qbound (hR hx).1).1
      have hdiv : q x / H ≤ B^10 := by
        apply (Nat.div_le_div_right hp).trans
        dsimp [P,H]; rw [show B^12 = B^10 * B^2 by ring, Nat.mul_div_cancel _ (by positivity)]
      exact mem_product.mpr ⟨mem_range.mpr (by dsimp [key]; omega), mem_range.mpr (Nat.lt_succ_of_le (hqa (hR hx).1))⟩
    · intro x hx y hy he
      exact hinj (hR hx).1 (hR hy).1 (by have := hcoll hx hy he; have := hcoll hy hx he.symm; omega)
  rw [card_product,card_range,card_range] at hcard
  have ht : R.card = T.card - S.card := card_sdiff_of_subset (filter_subset ..)
  omega

/-- The length of the interval is the twelfth power of the scale. -/
private lemma exclude_large (t n : ℕ) (ht : 21 ≤ t)
    (hhuge : 4672*t^2+36*t < 2^t)
    (hlo : 2^(2^t) ≤ n) (hhi : n < 2^(2*2^t))
    (hwin : ∀ k : ℕ, 1 ≤ k → k^2 < n →
      ((n+k).primeFactors.filter fun q => k < q).card ≤ 1) : False := by
  classical
  let B := 2^t
  let L := 12*t
  let P := B^12
  let d := 146*t
  have hP : P = 2^L := by dsimp [P,L,B]; rw [← pow_mul]; congr 1; omega
  have ht2 : 21*t ≤ t^2 := by nlinarith only [Nat.mul_le_mul_right t ht]
  have hB : 100 ≤ B := by change _ < B at hhuge; omega
  have hx : t*(2*d)+12*t*(((5*d+6)/2)) < B := by
    change _ < B at hhuge
    dsimp [d]
    rw [show (5*(146*t)+6)/2 = 365*t+3 by omega]
    nlinarith only [hhuge]
  have hLB : 2190*L < B := by dsimp [L]; change _ < B at hhuge; omega
  have hsmallP : P^2 < n := by
    apply lt_of_lt_of_le _ hlo
    rw [hP,← pow_mul]; apply Nat.pow_lt_pow_right (by decide); omega
  have hsum : n+P < 2^(3*B) := by
    have hle : P ≤ 2^(2*B) := hP ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have hle' := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2*B+1 ≤ 3*B)
    rw [pow_succ] at hle'; change n < 2^(2*B) at hhi; omega
  have hN : 4*d ≤ B := by
    dsimp [d]
    change _ < B at hhuge
    omega
  let S := smoothHits n P
  let D := S.filter (fun x => B^(2*d) < residue P x)
  let G := S \ D
  let T := G.filter (fun x => (giants P x).card = 1)
  have hSI : S ⊆ Ioc n (n+P) := filter_subset ..
  have hDS : D ⊆ S := filter_subset ..
  have hGS : G ⊆ S := sdiff_subset
  have hTG : T ⊆ G := filter_subset ..
  have hres {x : ℕ} (hx : x ∈ G) : residue P x ≤ B^(2*d) := by
    obtain ⟨hxS,hxD⟩ := mem_sdiff.mp hx; simpa [D,hxS] using hxD
  have htc := singles_bound (by omega : 2 ≤ B) (rfl : B=2^t) hlo hsum hN hx T
    (hTG.trans hGS) (fun _ hx => hres (hTG hx)) (fun _ hx => (mem_filter.mp hx).2)
  have hdcount : (t*(2*d))*D.card ≤ L*(P+P.primesLE.card) := by
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp
    calc
      2^((t*(2*d))*D.card) = ∏ _x ∈ D, B^(2*d) := by simp [B,pow_mul]
      _ ≤ ∏ x ∈ D, residue P x := prod_le_prod (fun _ _ => Nat.zero_le _) (fun _ hx => (mem_filter.mp hx).2.le)
      _ ≤ P.factorial*P^P.primesLE.card := residual_product (by dsimp [P,B]; positivity) D (hDS.trans hSI)
      _ ≤ P^P*P^P.primesLE.card := Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
      _ = 2^(L*(P+P.primesLE.card)) := by
        rw [← pow_add]
        rw [pow_mul 2 L (P+P.primesLE.card)]
        exact congrArg (fun x : ℕ => x^(P+P.primesLE.card)) hP
  have hpos {x : ℕ} (hxG : x ∈ G) : 0 < (giants P x).card := by
    have hxS := hGS hxG
    have hxI := mem_Ioc.mp (hSI hxS)
    by_contra! H
    have he := card_eq_zero.mp (Nat.eq_zero_of_le_zero H)
    have hr := split_residue (by omega : x ≠ 0) (mem_filter.mp hxS).2
    rw [he,prod_empty,mul_one] at hr
    have hm := hres hxG
    rw [hr] at hm
    have hrB : B^(2*d)=2^(t*(2*d)) := (pow_mul 2 t (2*d)).symm
    rw [hrB] at hm
    exact (not_lt_of_ge (hm.trans ((Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : t*(2*d) ≤ B)).trans hlo))) hxI.1
  have hgb : 2*G.card ≤ P.primesLE.card + T.card := calc
    _ = ∑ _x ∈ G, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ G, ((giants P x).card + if (giants P x).card=1 then 1 else 0) := by
      apply sum_le_sum
      intro x hxG
      have := hpos hxG
      split <;> omega
    _ = (∑ x ∈ G, (giants P x).card) + T.card := by rw [sum_add_distrib,sum_boole]; rfl
    _ ≤ _ := Nat.add_le_add_right (giant_budget G (hGS.trans hSI)) _
  have hw : n.primeFactors.card ≤ 2*B := by
    have hn : n ≠ 0 := by have hh := pow_pos (by decide : 0 < 2) B; omega
    exact (primeFactors_count hn).trans (Nat.log_lt_of_lt_pow hn hhi).le
  have hch := card_hits hsmallP hwin
  change P.primesLE.card ≤ S.card+n.primeFactors.card at hch
  have hgcard : G.card = S.card-D.card := card_sdiff_of_subset hDS
  have hpcount : P.primesLE.card ≤ 2*D.card+(4*B+B^11+(B^10+1)*(3*B+1)) := by omega
  have hpl := primes_lower L (by dsimp [L]; omega)
  rw [← hP] at hpl
  have hbad : 73*L*D.card ≤ 36*(P+P.primesLE.card) := by
    have hh : t*(73*L*D.card) ≤ t*(36*(P+P.primesLE.card)) := by
      dsimp [L,d] at hdcount ⊢
      have h1 : 3*(t*(2*(146*t))*D.card) = t*(73*(12*t)*D.card) := by ring
      have h2 : 3*((12*t)*(P+P.primesLE.card)) = t*(36*(P+P.primesLE.card)) := by ring
      simpa only [h1,h2] using Nat.mul_le_mul_left 3 hdcount
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  have h1 : B ≤ B^11 := by simpa using (Nat.pow_le_pow_right (by omega : 0 < B) (by decide : 1 ≤ 11))
  have h11 : 1 ≤ B^10 := one_le_pow₀ (by omega)
  have h12 : 1 ≤ B^11 := one_le_pow₀ (by omega)
  have hrest : 4*B+B^11+(B^10+1)*(3*B+1) ≤ 13*B^11 := calc
    _ ≤ 4*B^11+B^11+(B^10+B^10)*(3*B+B) := by gcongr; omega
    _ = _ := by ring
  have hnum : 146*(L*(4*B+B^11+(B^10+1)*(3*B+1))+(L+1)) < P := by
    have lpos : 0 < L := by dsimp [L]; omega
    have slack : L+1 ≤ 2*L*B^11 := by
      have := Nat.mul_le_mul_left (2*L) h12
      omega
    calc
      _ ≤ 146*(L*(13*B^11)+2*L*B^11) := by gcongr
      _ = (2190*L)*B^11 := by ring
      _ < B*B^11 := Nat.mul_lt_mul_of_pos_right hLB (by positivity)
      _ = P := by dsimp [P]; ring
  have hfinal := Nat.mul_le_mul_left L hpcount
  have ratio := Nat.mul_le_mul_right P.primesLE.card (show 144 ≤ L by dsimp [L]; omega)
  nlinarith only [hpl,hbad,hnum,hfinal,ratio]

private theorem polynomial_scale {t : ℕ} (ht : 21 ≤ t) : 4672*t^2+36*t < 2^t := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ht
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 21+(k+1)=(21+k)+1 by omega]
    have grow : 4672*(21+k+1)^2+36*(21+k+1) ≤ 2*(4672*(21+k)^2+36*(21+k)) := by
      ring_nf
      omega
    calc
      _ ≤ 2*(4672*(21+k)^2+36*(21+k)) := grow
      _ < 2*2^(21+k) := Nat.mul_lt_mul_of_pos_left (ih (by omega)) (by decide)
      _ = _ := by rw [pow_succ 2 (21+k),Nat.mul_comm]

theorem below_cutoff_of_window {n : ℕ} (hnpos : 0 < n)
    (hwin : ∀ k : ℕ, 1 ≤ k → k ^ 2 < n →
      ((n + k).primeFactors.filter (fun p ↦ k < p)).card ≤ 1) :
    n < 2^(2^21) := by
  let s : ℕ := 21
  have hs : 21 ≤ s := le_rfl
  change n < 2^(2^s)
  by_contra! H
  let l := Nat.log 2 n
  let t := Nat.log 2 l
  have hl : 2^s ≤ l := Nat.le_log_of_pow_le (by decide) H
  have ht : s ≤ t := Nat.le_log_of_pow_le (by decide) hl
  have hlo : 2^(2^t) ≤ n :=
    (Nat.pow_le_pow_right (by decide) (Nat.pow_log_le_self 2 (by
      have := pow_pos (by decide : 0 < 2) s; omega : l ≠ 0))).trans (Nat.pow_log_le_self _ hnpos.ne')
  have hhi : n < 2^(2*2^t) := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) l
    change l < 2^(t+1) at hh
    rw [pow_succ] at hh
    exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).trans_le
      (Nat.pow_le_pow_right (by decide) (show l+1 ≤ 2*2^t by omega))
  exact exclude_large t n (hs.trans ht) (polynomial_scale (hs.trans ht)) hlo hhi hwin


end Erdos889.EffectiveBound

/-- Every positive solution has at most 2,097,152 binary digits. -/
theorem Erdos889.effective_binary_cutoff {n : ℕ} (h : Erdos889.v_l 1 n=1) : n<2^(2^21) := by
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · exact pow_pos (by decide : 0<(2:ℕ)) _
  · apply Erdos889.EffectiveBound.below_cutoff_of_window hn
    intro k hk _
    rw [←OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.v_as_card]
    exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.offset_le_one h hk

namespace Erdos889.Missing
open Finset

lemma fresh_iff {n k p : ℕ} (hp : 0 < p) (hd : p ∣ n+k) :
    (∀ i ∈ range k, ¬p ∣ n+i) ↔ k < p := by
  constructor
  · intro h
    by_contra! hle
    have hdiff : n + (k-p) = n+k-p := by omega
    exact h (k-p) (mem_range.mpr (by omega)) (hdiff ▸ Nat.dvd_sub hd (dvd_refl p))
  · intro h i hi hdiv
    have hi' := mem_range.mp hi
    have hsub : n+k-(n+i) = k-i := by omega
    have hd' : p ∣ k-i := hsub ▸ Nat.dvd_sub hd hdiv
    have := Nat.le_of_dvd (by omega : 0 < k-i) hd'
    omega

theorem v_as_card (n k : ℕ) :
    v n k = ((n+k).primeFactors.filter (k < ·)).card := by
  unfold v
  congr 1
  ext p
  simp only [mem_filter]
  exact and_congr_right fun h => fresh_iff (Nat.prime_of_mem_primeFactors h).pos
    (Nat.dvd_of_mem_primeFactors h)

-- BEGIN MISSING WITNESS
/-- Absence of a two-prime witness exactly bounds every count at the predecessor, and offset one attains the bound. -/
theorem predecessor_solution_of_missing {N : ℕ} (big : 1 < N)
    (none : ¬ ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ N+d ∧ s ∣ N+d) : v_l 1 (N-1)=1 := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    have bound : v (N-1) k ≤ 1 := by
      rw [v_as_card,Finset.card_le_one]
      intro q hq s hs
      obtain ⟨cq,bq⟩ := Finset.mem_filter.mp hq
      obtain ⟨cs,bs⟩ := Finset.mem_filter.mp hs
      have eq : N+(k-1)=(N-1)+k := by omega
      by_contra ne
      exact none ⟨k-1,q,s,Nat.prime_of_mem_primeFactors cq,Nat.prime_of_mem_primeFactors cs,ne,
        by omega,by omega,eq ▸ Nat.dvd_of_mem_primeFactors cq,eq ▸ Nat.dvd_of_mem_primeFactors cs⟩
    exact_mod_cast bound
  · obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show N≠1 by omega)
    have eq : N-1+1=N := by omega
    have first : 1 ≤ v (N-1) 1 := by
      rw [v_as_card,eq]
      exact Finset.card_pos.mpr ⟨q,Finset.mem_filter.mpr ⟨pq.mem_primeFactors dq (by omega),pq.one_lt⟩⟩
    exact (show (1 : ℕ∞) ≤ (v (N-1) 1 : ℕ∞) by exact_mod_cast first).trans
      (le_iSup_of_le 1 (le_iSup_of_le (by decide : 1≤1) le_rfl))
-- END MISSING WITNESS

end Erdos889.Missing


namespace Erdos889.BoundedPair
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
private def catalog (q : ℕ) : Bool :=
  decide (q < 512) && (0x208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac : ℕ).testBit q

private theorem catalog_sound {q : ℕ} (h : catalog q = true) : q.Prime := by
  simp only [catalog,Bool.and_eq_true,decide_eq_true_eq] at h
  have checkedPrimes : ∀ i : Fin 512, (0x208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac : ℕ).testBit i.val = true → i.val.Prime := by
    decide +kernel
  exact checkedPrimes ⟨q,h.1⟩ h.2

private def fastPow (a e q : ℕ) : ℕ :=
  if catalog q then
    if e=0 then 1%q else if a%q=0 then 0 else (a%q)^(e%(q-1)) % q
  else a^e % q

private theorem fastPow_eq (a e q : ℕ) : fastPow a e q = a^e % q := by
  by_cases yes : catalog q = true
  · have pq := catalog_sound yes
    simp only [fastPow,yes,if_true]
    by_cases ee : e=0
    · simp [ee]
    · simp only [if_neg ee]
      by_cases d : a%q=0
      · simp only [if_pos d]
        have z : Nat.ModEq q a 0 := by simpa [Nat.ModEq] using d
        simpa [Nat.ModEq,zero_pow ee] using (z.pow e).symm
      · simp only [if_neg d]
        have cp : a.Coprime q := (pq.coprime_iff_not_dvd.mpr (fun h => d (Nat.mod_eq_zero_of_dvd h))).symm
        exact ((Nat.mod_modEq a q).pow _).trans
          (pow_cycle (Nat.ModEq.pow_card_sub_one_eq_one pq cp) e).symm
  · simp [fastPow,yes]

private def repeated (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | a+1 => let z := repeated m a; z ||| (z <<< (m*2^a))

private theorem repeated_sound {i m a : ℕ} (h : (repeated m a).testBit i = true) : m ∣ i := by
  induction a generalizing i with
  | zero => simpa only [repeated,Nat.testBit_one_eq_true_iff_self_eq_zero] using
      (show m ∣ i from (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h) ▸ dvd_zero _)
  | succ a ih =>
    simp only [repeated,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftLeft,Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with hh | ⟨hi,hh⟩
    · exact ih hh
    · simpa only [Nat.sub_add_cancel hi] using dvd_add (ih hh) (dvd_mul_right m (2^a))

private def strip (mask hi m k : ℕ) : ℕ :=
  let pat := (repeated m ((hi/m+1).log2+1)) <<< (k%m)
  mask ^^^ (mask &&& pat)

private theorem strip_sound {i mask hi m k : ℕ} (_hm : 0 < m) (h : mask.testBit i = true) :
    (strip mask hi m k).testBit i = true ∨ Nat.ModEq m i k := by
  let pat := (repeated m ((hi/m+1).log2+1)) <<< (k%m)
  by_cases hp : pat.testBit i = true
  · right
    simp only [pat,Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq] at hp
    obtain ⟨t,ht⟩ := repeated_sound hp.2
    have eq : i = k%m+m*t := by omega
    change i%m=k%m
    rw [eq,Nat.add_mul_mod_self_left,Nat.mod_mod]
  · left
    change (mask ^^^ (mask &&& pat)).testBit i = true
    simp [h,hp]

private def rootRes (b q : ℕ) := fastPow 2 b q + q - 1
private def base (v : Bool) (c q : ℕ) := if v then 2 else rootRes c q
private def val (v : Bool) (c t q : ℕ) :=
  if v then fastPow (rootRes t q) c q else fastPow (rootRes c q) t q
private def period (v : Bool) (c m q : ℕ) : Bool :=
  base v c q % q == 0 || fastPow (base v c q) m q == 1

private theorem cycle {q a m i j : ℕ} (hq : 1 < q) (hi : 0 < i) (hj : 0 < j)
    (h : a%q = 0 ∨ fastPow a m q = 1) (ij : Nat.ModEq m i j) :
    Nat.ModEq q (a^i) (a^j) := by
  rcases h with z|p
  · have ha : Nat.ModEq q a 0 := by simpa [Nat.ModEq] using z
    simpa [zero_pow hi.ne',zero_pow hj.ne'] using (ha.pow i).trans
      (show Nat.ModEq q (0^i) (a^j) by
        simpa [zero_pow hi.ne',zero_pow hj.ne'] using (ha.pow j).symm)
  · have per : Nat.ModEq q (a^m) 1 := by
      rwa [Nat.ModEq,Nat.mod_eq_of_lt hq,← fastPow_eq]
    have e : i%m=j%m := ij
    exact (pow_cycle per i).trans (e ▸ (pow_cycle per j).symm)

private theorem root_congr {p i q : ℕ} (hq : 0 < q) (e : Nat.ModEq q (p+1) (2^i)) :
    Nat.ModEq q p (rootRes i q) := by
  apply Nat.ModEq.add_right_cancel' 1
  rw [rootRes,Nat.sub_add_cancel (by omega : 1 ≤ fastPow 2 i q+q),fastPow_eq]
  exact Nat.modEq_add_modulus_iff.mpr (e.trans (Nat.mod_modEq _ _).symm)

private theorem val_congr {v : Bool} {c i j p q m : ℕ} (pq : q.Prime) (hi : 0 < i)
    (hj : 0 < j) (bp : p+1=2^(if v then i else c)) (per : period v c m q = true)
    (ij : Nat.ModEq m i j) :
    Nat.ModEq q (p^(if v then c else i)) (val v c j q) := by
  simp only [period,Bool.or_eq_true,beq_iff_eq] at per
  cases v with
  | false =>
    have root := root_congr pq.pos (p:=p) (i:=c) (by exact bp ▸ Nat.ModEq.refl _)
    simp only [val,Bool.false_eq_true,if_false,fastPow_eq]
    exact ((root.pow i).trans (cycle pq.one_lt hi hj per ij)).trans (Nat.mod_modEq _ _).symm
  | true =>
    have e : Nat.ModEq q (p+1) (2^j) := bp ▸ cycle pq.one_lt hi hj per ij
    simp only [val,if_true,fastPow_eq]
    exact ((root_congr pq.pos e).pow c).trans (Nat.mod_modEq _ _).symm

private def valid (v : Bool) (c lo m k q s : ℕ) : Bool :=
  if s = 0 then decide (m=q ∧ 1 < q ∧ q < lo ∧ k%m=0)
  else
    let j := k%m+m
    let u := val v c j q
    let w := val v c j s
    let d := (q-u)%q
    decide (0 < m ∧ catalog q = true ∧ catalog s = true ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
      (u+d)%q=0 ∧ (w+d)%s=0) && period v c m q && period v c m s

private theorem valid_sound {v : Bool} {c lo m k q s p n i : ℕ}
    (h : valid v c lo m k q s = true) (pi : i.Prime) (loi : lo ≤ i)
    (bp : p+1=2^(if v then i else c)) (nr : n+1=p^(if v then c else i))
    (ij : Nat.ModEq m i k) : v_l 1 n ≠ 1 := by
  by_cases sz : s=0
  · simp only [valid,sz,if_pos,decide_eq_true_eq] at h
    obtain ⟨rfl,big,small,zero⟩ := h
    have di : m ∣ i := Nat.dvd_of_mod_eq_zero (show i%m=0 from Eq.trans ij zero)
    rcases (Nat.dvd_prime pi).mp di with w|w <;> omega
  · simp only [valid,if_neg sz,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨⟨mp,pq,ps,ne,hq,hs,dq,ds⟩,cq⟩,cs⟩ := h
    let j := k%m+m
    let d := (q-val v c j q)%q
    have hj : 0 < j := by dsimp [j]; omega
    have ij' : Nat.ModEq m i j := by
      change i%m=(k%m+m)%m
      simpa using (show i%m=k%m from ij)
    have pass {a : ℕ} (pa : a.Prime) (ca : period v c m a = true)
        (dv : (val v c j a+d)%a = 0) : a ∣ n+(d+1) := by
      have res := (val_congr pa pi.pos hj bp ca ij').add_right d
      rw [← nr] at res
      apply Nat.dvd_of_mod_eq_zero
      change (n+1+d)%a=(val v c j a+d)%a at res
      rw [show n+(d+1)=n+1+d by omega,res,dv]
    exact two_primes (k:=d+1) (by omega) (catalog_sound pq) (catalog_sound ps) ne hq hs
      (pass (catalog_sound pq) cq dq) (pass (catalog_sound ps) cs ds)

private def initial (lo hi : ℕ) : ℕ :=
  [2,3,5,7,11,13,17,19].foldl (fun z a => strip z hi a 0)
    ((2^(hi+1-lo)-1) <<< lo)

private theorem initial_sound {lo hi i : ℕ} (pw : i.Prime) (big : 19 < lo)
    (low : lo ≤ i) (high : i ≤ hi) : (initial lo hi).testBit i = true := by
  have aux (xs : List ℕ) (hxs : ∀ w ∈ xs, 1 < w ∧ w < lo) (z : ℕ) (h : z.testBit i=true) :
      (xs.foldl (fun Z a => strip Z hi a 0) z).testBit i=true := by
    induction xs generalizing z with
    | nil => exact h
    | cons a xs ih =>
      have ap := hxs a (List.mem_cons_self ..)
      apply ih (fun w hw => hxs w (List.mem_cons_of_mem _ hw))
      rcases strip_sound (m:=a) (k:=0) (by omega) h with h|h
      · exact h
      · rcases (Nat.dvd_prime pw).mp (Nat.modEq_zero_iff_dvd.mp h) with w|w <;> omega
  apply aux
  · intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    omega
  · simp [Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,low,show i-lo < hi+1-lo by omega]

private def verify (v : Bool) (c lo hi : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, mask => mask == 0
  | a+1, code, mask =>
    let m := code%65536
    let word := code/65536
    let k := word%m
    let rest := word/m
    let q := rest%512
    let s := (rest/512)%512
    (decide (0 < m) && valid v c lo m k q s) &&
      verify v c lo hi a (rest/262144) (strip mask hi m k)

private theorem verify_sound {v : Bool} {c lo hi p n i : ℕ}
    (pi : i.Prime) (loi : lo ≤ i)
    (bp : p+1=2^(if v then i else c)) (nr : n+1=p^(if v then c else i))
    (a mask code : ℕ) (hit : mask.testBit i = true)
    (h : verify v c lo hi a code mask=true) : v_l 1 n ≠ 1 := by
  induction a generalizing mask code with
  | zero => simp only [verify,beq_iff_eq] at h; simp [h] at hit
  | succ a ih =>
    simp only [verify,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases strip_sound (hi:=hi) (k:=(code/65536)%(code%65536)) h.1.1 hit with kept|hit'
    · exact ih _ _ kept h.2
    · exact valid_sound h.1.2 pi loi bp nr hit'

/-- A row certificate verifies the entire interval of prime indices. When
`v` is true the base index varies, and otherwise the power exponent varies. -/
theorem row_sound (v : Bool) (c lo hi a code : ℕ)
    (h : verify v c lo hi a code (initial lo hi) = true)
    {p n i : ℕ} (pi : i.Prime) (big : 19 < lo) (low : lo ≤ i) (high : i ≤ hi)
    (bp : p+1=2^(if v then i else c)) (nr : n+1=p^(if v then c else i)) : v_l 1 n ≠ 1 :=
  verify_sound pi low bp nr a _ code (initial_sound pi big low high) h

private def rowClaim (v : Bool) (c lo hi : ℕ) : Prop :=
  ∀ {p n i : ℕ}, i.Prime → lo ≤ i → i ≤ hi →
    p+1=2^(if v then i else c) → n+1=p^(if v then c else i) → v_l 1 n ≠ 1

private theorem checked (v : Bool) (c lo hi a code : ℕ)
    (h : verify v c lo hi a code (initial lo hi) = true) (big : 19 < lo) : rowClaim v c lo hi :=
  fun pi low high bp nr => row_sound v c lo hi a code h pi big low high bp nr

end Erdos889.BoundedPair

namespace Erdos889.BoundedPair
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_3 : rowClaim false 3 23 1048576 :=
  checked _ _ _ _ 245 0x1f5666dd0a0a28009eb20248b59ecceed6843ef6fb788e7eed78eb84a372bdad0350b5c3976b70ca499d8a53527fd21d30903b52a21b1c4ea031be35b629f7e589a82c9626e9e2e35700eb986786975182263c31ea81d59331d99467c344114620b429a65b5f29c74864f39b056d5083438e1453a0d293166f823eba4a72a27794cd753e1c3fe90f5019d1e4669e6ac566326092b13ad1619020105efc3216b24793ad343fbc1b82e1a0a872b7e788b168a34593da4cb8c2f405be8bd2f864659c36eace89efe00d345968a0bfab77a58435a4bc584ea5c6bdf509f9f306547226f4fd1c4715f79e64685aaab3d1b298c9ad7bf57fa6d85fae5c83791b4495006a0b766af25d893516b0be5873519395f0426def22774ab9447c59cb76c50b47d0dc3139ecaa503340edd48d480c21c89e800363247bf718fbb072c8aadf4a7fe1e46e477e192290912c61dfb369f6043451d9b42b88aeed610d2c3c8e3072e4caa9cafe7a32b5996e57118e09d2ebb2667bee05bf5a56853af93de7be52aa96d84d5c3649a756baca686e3d4b89a5a616f35fec4ca70a41b3b81c1fbe6c95900aa2f522836bb7d1a91ca2493be16f2e25de30593e44c707fc0eaf98406521643a4d70cc70dff56c32bbc35a537571b4d1dfbee7b290bf11f2c36b3cb0eef57fdb80762c89727e1d02b9edfd122e3c34f126f3d2dea964980289c44df53064b2506c91225abd7b8ab2060d32a198762ac5fa78bb848f6a81252e68d5336926b17757c7ce3f07903748b813507572b321e544186505d3475bd0340f817f181022407db8bb111f62e931b648cc3c6d0168293b4ff79d5b798b83c6a8293b404cd2a2ef0ed354506b09fed9da518a88164dffe7409a19b81cbf62df0e8c46a058b32be08bf357e74636b7dab5f82ffbf4cf778bae71f10d615ef455a0a7e7fff06449e9081c69d8bca28c5916a1c3752836787dc4f95caea0432a01013c9630e64f6777097f203cc45075d41e8448b1393d3f4430c17a18fcfac877e4dd1063447aee16fcb84a417d07d0a487950e5c656f6c50549819f0080a7a7e13f54f0af62d764a38423e3c37f98cc17f6469e3c1ceebcfcc612b0298e4300d303dd14f5270e9f1b6fb203a1bf1290da72d1e4d6f2e539a1a9fb813f9c0b16c37d3a11314773738966d151b9ec337215430f47ef6ada680bec114b3f9a0096b5ddd273bca8a6b5b4762414649e5c3f1f935adf3b402d04056d55d4223db50b97ea764a176341419f9d0045d49e9dd9297b4ef7ce82ff69bafca6deab026465d09dcbd495050282fb3932ad4093676fd654d2bcf53883f73e7f69a124039cbfb6120b4b06405bb0f6d9649f4dfbb234102da61692c700efc132c1b8e2df38df2d626da906f3129b671324418d04cd118d666c4c26d6093fe5363d8c98a5c1162029cec7798cefc9c575d13dd0f60db4a5d47545faf930e4fd3c83702ab05966966f23a066c9c3eba241aeb2781c84cf3d48c6ea89d92ddb5f260efbd034dd8855ca8560454d53b79cbdab7afb2b0535e902dfae142fe183d910145196e788040e29140321732e156f9ac7bbd24193ff5e28d1cb61b4bb857c440b5f581fc3ca5ff61278cb22ca32e8c5b8d2d64b9eb747252096eb2d08011d8ee1fd4a10d50fef6f6360f864644d4dcea7a1404d57ea05cdf3e7365b2a7c78b699163e62932c0a45b87c10d82b438af6669edd6f4f41f23be58bbe98155db612f15cb8ac42e57c6477140f46f9295608fd0809125817d3a002ec9cd9807686018eb0fc249d098f8cfbb6841be1b73815efdf190046 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_5 : rowClaim false 5 23 524288 :=
  checked _ _ _ _ 262 0x1acfc59104ff0a40876eda61635266d6a6df868409d2c72785c33be2b5f74879d413dc8dcf3cf3a9d07ac4700e80ca0f88d797e386ca1694af233597d56e7917637adba7a4bdcd5fdb024c504cea4cbcb936c5799e278438eba73eb7a95f6c9c63245218a2d0d8bac0d8c2978a05552bc8ba7e41abca2c826eed5689ac31ebc23f558d67e7134cea6a7603ec575ed462dfb817e86d74282f04f8fc8085f3cd4666f43b0af952c105464ec7371cc2f58600ea4cdef1f8792e744f008a89f5378d30d1def568974c110070cb6a93085215a7cf19f50a53d56fcb85e5713b6ed4131df10685ba50eb4db67d0388d593d1ddea24b887afe9c71ce37114db7cd202543becdc526631081566ca0eedb617493290c0a6e626bf3fd80ea53e2b63bd0b69d009c38d6f8c041a1ea99b89adf1b5cb28e1583ce6315a0ac29a5003741dfd8d3a683ac82d8b798ccc08bf5034e657f9ba3f357b700d9c663472cfcc727c2cc13c7fa597d5667878a0b65655c672e9506f8ed863c62d9b1ef7def5ba2a3953e8a10dff237e945720b0c2ded119e980640324a91cc07186a8435da4df1e047c158927a5b128eaadf22f6cbd9c11461a24ca733f16497aa68836461481da4dc198b8fec41e00623213f39b94535de9f130b1f6253b26c40fbdec415cd9b4e6ad4d31e0e7f270e9e5eaf320bdc25bf5fb6c8df260cec61bb67855e250e0e98ba0812021c695c28c38ece7e49f1cead08cb50c2ee6a845a6cdfabbd4758d6c464399c9937328d5bf531a8986b53781cb8f5b21e52911bdcfaa66556565f1497284f1731678f1d714fdf5e102b1b8ec9aeaec92025fdf8068ba6150960ba6260bb59ca764e35165eeb424fa450f4dae16932b6ce3b7410f3b2f54688efc3c5066f14bd18feae6da08c43f48ef0cb7ccead81ce066046e1e00ae93b6aa817bf276db07b0322926c71c74a397d0b3e78769186d7534f15bc4e1a27831fb6b3d90125fee314da98f8272e0aa439219ecc7e7e5295ffb79165d553421abcc771d0c41b66ccece5313c2bc14c7ab1192c62cac1c319199ff71b637373dd97d7da317810a4211d5be2791b6c3e2c2e6ed43dda4ba79885e488ba7c1e93255dd4ef741c5cc28ce288f5085f225ccaf78085f298c2ac5dd3a3de1a6fbc779e5d0327642a214cff8c9700094a23b2ce8666e57bfd55689c4b8ad4f2e97a2d34238d1f263b13f0cd6ae3a658207ab5cc25d0feebd2b4ce3961cfda152191b9ad00cc3a3f9214657d6404547458e49c6ba0c25f37a3b9cda6b0fd9f0fb82315d11ee69cea38cf51c21f7b22bcbfeb2c72403e37806802ee4d912c5629b8ba8082564e01deafe8b4b1631db06f02bd8759d881671b8e8d85e09ef1408673a44ba90e4b45fc7ee8faa347d78e5ea3158089c2aa5b2601e0a3d9efe68eb4b3d8dbfbe530b38eb2230c00495bae0aab48b8886dac833c81454cc68111e3a830657fc23a1a9530c027f6006758f3018fc06c3c56239a4ce872a5c4ef79740b2d5046161fead7d0edd90089b1457d5f6613206968c9df95d4f1de18982191cf6cda7dc5bb7bf714c33cc1dba1c366469d01d1a999ae2b503fedd6bb9827af534c65a856bb2e7371fae8ee51ff7bc78046ac690125360414124b2d56a840f4aaa869bb222b130eb56f71658dd2c9276f75cdeab62035beaa42008572e3deabf0eeb093260ec7aab22471f4f64fc779b720538d8a352124b24cd1ccae8fcb6046a63cf64958658c26b36d59e83b1fba54c894777203576c95e4e801f6294ada5e514d0f5e81f7769057799ff9fb3c9ed9cab862c0a4f5d686002f3b1d8991acea450f98359652ac0c3b1fdcd4402a44ed96958ef567775e948195507ff0597eff20062b9fb84eddc70b522b73c06081bc9379458481e4400c7078f955d7b05e6307ff97aec23921900404b456abc00f0723470030 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_7 : rowClaim false 7 23 349525 :=
  checked _ _ _ _ 139 0x13eb91b7a2accfa38fa7e5193c768c9c0bb0f0d4183cb20041a4dbfda2320223d007c5be3e93084a2cad24f310839bdf016a1ce9ec07a10a0aeb9b21ad6deb77881c9bfe719676ef07e1e3b1b9f0880e6306d72c20ddf27b7b0d8ab5079c21189c7597fe32746d5c379decdba5221c26e4437ca5cd4bb5ebd92a476642eb45e672182c6ac6c4b780eee7e3e744f7569f81b859bcf96708942aaa8610961842edd7435882a84eec3ed0f9ed88b555f71a80ed0a2391598cb059129ad03effff39af76f1604085f038e60f5a473518148d1dc3f936be3298f9dc5a31c2c6554c800cf4c61b38a24ea023e66129ee14a0f5a62b6fdd3290cd6691d9530fb8d90f19cdd0c2d7d7e2e70acba29aeec300be4a6fdffe42e9008f3276460dbdb9583c9b71d6838561114fd3ba64d96b44add0c36966c330d12dd240a48b10981967634c6cc66c06f24ffe6c2b3453fd10f4e060913514898931dcb48c9ade58d030acfd05d010f024fce6632be54af918cf523157ba87886695c410d32129a6c7abe79d861177562674165602336a0655b42124c95983b3335065d88e54e85331b39bf842119478da390954b1cb50c55f17b845862ef18d43fd515116eeb5f17878ad2e86cea6f453f86e55e534708567be21d5f664567afcab4c2185fe39ab4f2ba587845fa81fa4c184beaa370fd07328c125d12431dd26acc943edbd03b25667c78b1019d04bebae94a77521908edce48750b62a37d60393fc2fe1dd20271462069d9ab82fdc99412baa937ca224b0d25e53f39002d9b32c3609942698db54bf1593ce8e96c8e55bb6f8742e0950e653e15ff0ff88393ed16aea52b946f1197cdc69cbaa5a03ab5fcb1353784fd42b7fd952aa1dca147287e19294db293e9545f58cd54f1ea795f211245ca1f94216d3bd2d3e42634147dd503a1240abe08711fe3a9849fe28415f04493d3c4c2a029fdf7d08a3f1e9cb51c533d4732cb02b5d211e903bb96c537a1d90fa9d5043924b9300b461ace003c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_11 : rowClaim false 11 23 209715 :=
  checked _ _ _ _ 1 0xb2170001 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_13 : rowClaim false 13 23 174762 :=
  checked _ _ _ _ 159 0x959868a4decef9d656ae561bf72b38c773b572cdfae5d66fa41a708d9b1439f03636b8987cae4404504e056e65c2650ee851e1ff4ea467c49179e3b837ed6a981c3007c94f5c131ffc9d345851012191d169ce706b4f788f124d0aab9c8f1a3024b15ba0311021f74fd8880eb2fa57d7de59d7e88bf273c3ae4f8a0b3b84d39a2ea78230f25358465f91d2dc4141a68f170ce38b55195328481665b7cc02a2b8dacc911a813a137e510cae0e315c437695236b392134c1f107b8f60eaf78f22e3b8da0573c59495e9ce21a62316a9f3b4bee8efdaf249c0bebd7702288ee0224e038c699f49cde3e29d6067784c66aa07b8504b9c4c6e0e5429607ab458036bae819fa56c4be26f24af1c357304037d5628ec81f74270ac4854d90605f9062241d072f3f15b0896a59eaa73b04aed0e213783f3741adf6dc49865808c3d30364e2387ef914e668dc95b0ed85a176776556765b69455511077009adde394c602215f4151beb2577f2bc1023847685d24670e223ec947e0468ce3b88667f7ca7cb0717554d15c40ad2f9ba16e09c059a23544ae6a493eaa8ac3d6dd67829e5471b44a3c4d9e9380f62a6cb15fb448688b8e95310c76d15bc6ce4ee0b1a79765285704b5ac471c232c77f1b3bcacb1a77e43314be05ae0eb566fe3ae35cb1c2c07fb722a8d3dc41ccb373c2e85546a35bd96279decb28eeb200056f194f4c63a5dd73a36cc3e5b0ed7f140cd4a17beb814e1ca5cd136df9fc7b2006fd185ac1e1cbd8d655e1c37444b4a393ed7e7a06d439dc07f9734d537f7e1b5e3ab9ed686a933a9d75b4ab72a187bb38ec91a0beffba7cff3e063418988c3b7a9ac64addd11b8b4883e353ae293100f47ee2bdad1f145c5112097acf509e35bc7ca7566e8a7771ce319605548179496a7d1d683ed009045c417c16e3d8ed3958dde518dd572d31e905bbf3a3a232ff7889afbb4d8c77908765cb0cde847c3ed971560ad1f0967a5b347c50c0bfd1016c89a52e3e7970a97a71115e0f4854d12e2d7d57e8ca040075db28b3e8156d8204d99e3b69bf9f2e3150ba2642ca5c93c959357a633a24390c1308a0a45690ee3acc1212833ccba63bd6678537c570f3ac82feb577d57ba8347c304b6e6157c81e76f185b3934106eff0b1980fcde663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_17 : rowClaim false 17 23 131072 :=
  checked _ _ _ _ 176 0xe2da997473f04e9886b06e3ad36ae8dcf56a77be1a3b7b8a36ee8ec7e4898befdeecfdca406dcbf1ed5a8109f320b779318fc3e4651ff61731d1fd3034cee09f02c873f82770fc368fc5ba8a3733294f527a8f6607c194c20c1f771251f2592f64673a847222c21c4038922ef5990753e77e84e2cdcaa9de757f27d2dc86f87e056be22777f552b5afbb742b7a9e61d5efc2f90dc83728e9ee3fc8a834e9f4ff0b1bb5af2f6972aa76d34658b072db9c059aedfbcb113eb1de9c06b6259aa9ae4a28b20d3c2a78ee9c3373c0e1a3117fd8f4c266d6c5c035d7ed20d2de3134eb661c56220a8916b8325062f0d133607b4c34d3a0cd1f7cf1ce98e4ae1e0c4edbcd30a56950926363bd2db80cf3e3542d7911ac26405288de883e308c33627c71088d3671019090ef46ca9a2c0af736c85756131d1a78ce2874024c54cf4f0265884e3414b9dfc1797ff9f97c419c6fba9c734db2f5d5c45db3d690f60785030004d8b07afe6e0a2b95ce0f59f50e4a47037cfc9dc9dd5b4e136000239f96730e104fcb7a2bf427e2a4b325a53107459a3596ac6e719dedeea7378566523c311c86ef2b568a1422e7ef026266b00a26061a4740d9a7f9cd39c2802a76422aa0f2ecfacd99416cdbba61cc6c0b3797fc91ca1daeb11f4b5b691ed90e69a7abdad4261dab5664cfc9dc6e5a924de63977339bf5fb8484371240b3cdda717f6c5fdc246c268a27d5651952587ce757f51751a969067abcc3bb9e362592b75c890ae6576cc93c76a461272293d106c78a7b7f6d28ca1b224d1dd84ddd3b48246021ce75c81492a2201a669e99fbe271b0e3e40e34a08120ab98b9d5d5913a07a8ff160e55f9d532c785b0c13b93efe802f8e13ec66c999c6951472bc1a4206acbb66e4150780b6ca7728ca57aee67db9896a09be320a0bdd6dcfa60a145d3f4029bc1c7d25e557a6b266cc4f35f8136035c3318ab3e73561d5fa4c8d43835a5c64434436e5f73252aac77536536ee18c6df5f1cef155b2ab6830fea8ebdae10c5a613a0732a135399d08c869f0c19cd10d8e224de057849ddb766afff79461ac52b85a9ce3e1aa469a804a2b004fcb7bddee6af20ce2cb5325e82c0e7b55953c99ba720fb2880b497ef5b50ef0bd11edbca50ce93f09d4d1cde6c0e1d3218cd661ae6be9f1784d73f18e66ae805145ce55402a7e6b6dacb877ddcf022ea3e2932b5e6f3ef253a002d083c8a720ae07f0caa45c3ba9ef058c68548cf824b43c88af91f2f2bcd84f63b1267fe43783b4201d9620d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_19 : rowClaim false 19 23 116508 :=
  checked _ _ _ _ 200 0x13ee9f06352d5054ee4a4264f8e2770036217706b7c664bcc0c85564a8e6fff40013af2cdb19ff6c02d05e8a5b24333c907b69d49f90af60ff14ba818e4d9c10e0984181a16cfc8cc8128d9b40ae8c410cf2f071a82bad78f675744a3a299962ae007c25ecd9ded31b8c916dbabe1fb5a79de5adad0e02c208ce336dec251269dfec5760c3d2bfbc87d249ff7b314a0d1159cd4aafbc656abf2613753cf6bbf32e9645ca87a4f5e6850cd210578e03beaa0b3f7d8e7f41d7593fcfd4be62c1c00abc8be964d908edbddc8db94a661577f3dea5a093d19b9ef0387f06f1b862411ca5221dfb17fb48fe4317f0ac79cc49c2e173e87148ecff571cd5b695cc25520b08f4b2ad22beab1311d1af929c6da24da6d768e2c90ed33bf2aea2193b251c1775577c4920a44826fb5b1314f7606f99218ddaa8dd1ad3d002c2d6664da045499014d6233d03c9b13bf42f790402b34bd1aecddb6e0f8ff21e6e939d53964e48fd8a7c07c1d98b2a232885bc41966ba4f6a0e5d64190351727cc9e7e469a5f5b7b1d2b84ec1a7c8bdc4c0c6c42cb7c0b7f6951dc50704aeb92ea02db2d2b34474d913628d8dc9820bc9862ed19126d0cb6f1df9bf4609df8511137ee5edbc743acaf911fddac1effb01cd0e7ff8b92fa9e44036574032809b6f64d2861ed04946c634b87d5f0bb2f2bc249023c63699ad66beed3f308fe7681aa2055f36d7bbb815a75b3a6c92eb441287e41f719e60a11e9171665c80517d53d3a803a75e7a0b9833259a407947c220f9e8bc6f5215b23a92717f60a31910dcfbd7a6df2e8bd5cb497eae4ed44bbd13b4d35be3a7f42b33b175cc0c79616a429874445d5b2ece984cfdada9d1e24173816cda60c29101ea96c10a9c85674e9fa04f6e742d51257cb10c1300c6ae6a048240d4595762a67b8030697d42bb0bb63b9cff88820cffa3aab216e78102922075c6f12732629c01a9071d04a5807ca584df67b52e0bb4f64fd192a1a2a3989fc27314cd0893ce368950fc35ec80a546202f9fc32dc1c6eb7dce77b2604e0acde101726f340ac0fea470506177137e0a13b9c39e1dffff566151804214db66fcd0ecb19a957548a23146d4ba1b9eed40664f5b0dc9945341d6a394245dca8b0edd30b65d9fef81ce3143581d82e50032cbe6910ba1c44f29adb58511f4ce3bc967a0ec4700d5fac05827ceb8066afc058f8e92deb969796c43d9840fee1aed45605b309551a3e42f01f1e29a51438f524f05eedd5eeef611e0a3700ee54da62c950bcd0910ed13500e6875ceee99a9a2af547b9e36ebd7d311cd2d2c2c31dbec3921488bf9f3e6bcefd2643ca3982f616eeb7e92ac913010521da0ea9f910ded23145667de5aa172c72c840433fc04762b800eaa58cd64889881627ec521ffba9542f8ec9c30e315ed3fc2d6962f6538fbfee1e6148843df204895644100031489c5264c7fc8140f94a6fc0063 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_23 : rowClaim false 23 23 95325 :=
  checked _ _ _ _ 52 0x1d1a990452f53d885454c60ca57eae3c6ecdfc2f562160915d0204fe7a63c1c8e62e67032a78ac126462974f9e373f0fa6dbddebdc0831a5d6b2de85e6747b2949525bb04cbb8b5a7cd5b85b7c5dd88d7c305bdfe2883159b01445b63d34418c310bf8f64200a3a88b1514111c6f720a852cac3981b061bf439af9b598b1141671ba0307535eb2bc8498a15f6d8f41e95217a570389209785daa33d8c9c37d93f806239a4172d6fb28bbd93411da0b83531c3a53ff113621ac60ff9d570338eb47f93ba87d524e5824ff26373ac297a4a45f66df99b374abf0780ea110c3514c24fccd5654777960aa074b0e6c1972c94b593527e153e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_29 : rowClaim false 29 23 74898 :=
  checked _ _ _ _ 65 0xeca972c6ba76fa3dd261d2dae7d67072975d546dbe60e369c507bb633b7f2867cb91f1853871fe58803fd9e0d9338dd79e6f53848b9fb952306c068dec0d1391760053d7db2fcfe19b3fe22e4b35180b5ea51254f85208e27171b43e161aafff20a16b3f536c92f6f2e4987cdc823260acec80f1f3fd6f462909bfeef3e571b570a0204d64683613fa5fa98be585afb731e93c7ba89f21bfdca9c571c15342db00dc7c92509777132ea4d10865f81304b29a41904c6b7ac04c83c7c09544752a6012f4aece09262d8f2f6f8249b197e36d3ccd0470b7cd230c3012aec5c84747ba7fe48809bfce055fd8243dc7d8b03311a8a34e2f71e6740fc04970790cbb4eaba4255b5c5a2aec9830542ae779873398a0b55a99f034adec3f2599c3f1f0f06e81258811c6837ada28c84d5930ab0ca38a97e8259e4001402c0bee15cdf630eb277ab945dd22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_31 : rowClaim false 31 23 69905 :=
  checked _ _ _ _ 116 0x30d43242ebc666e7bc6e4fbeefe87c2bc489c82792b9ce9bfef5fadd06bc41160c6c6641a672f962efa0eea1f087975953e643c7486ae356bf8a92dc0d1a997bd0b52cdb871063eab601c5c4cb6bed65873a90ce5b50c4391a257017cbfa103c63a1f401581a5b39ba92574a3e50f0d7eb5929e04151845fd06a5bcdc98758f92c18278161cb23f33c120f8bd1edaadf7f62c968e7db58ca8fc0a9b538afd1d33d25892475c6cdda1e8627c328c8cf18d956b1c3d670e2111f4072d8cf273f0d6e26f6bb74e085eed11a3b18f73e93cf6e72ecc5f450a3839893309277e7903da7658233038c5e92ac8c6995c61e8a44c6e07814eed894bd5d13cacb59c113d7691a38fadfcd55462390295e2fba88d85edf6262ee66f05be47879ec0be6b53f0e31a4b8c2495e908bd978e2e083afc917aa20f3eaa701fef9628802bc61f5e4ce9ca2c4d3fe39d14b2c33b4f84816eaa2bdcfc28a14caf815ccf1cad7d3f9099290582b70c518b9ed000821af3de7fd45fa92c8cafd4dfeb61e676b3836ea08be737502a4eb871cc770324d0fb93f1764a65f6991e73040f28aa2c1bb322f8280d14a80bd1b4b82c3b2bab485771537fe4e33410fd5e17f7aa738d0dd606a3d12130d45ab07aba12b244c21bea5b7aeca01313d33e75b6cc705355d529e4fd48a0e07bc3fb5225e861428e9fea305cd2ae7f4b32e0aa2c7d341365c381616c418a69bac0541ba54bbd10525eec326bf20b1b289b8a5af5cd36fbdb3df1fac37de05b3e1bf9f7f1420be994b0b82dc34637fb59a28abf051710afd09830456a021f9434100783d83d800c09c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_37 : rowClaim false 37 23 58254 :=
  checked _ _ _ _ 555 0x2e10f683cabcc662b54966eac1a209ea21e31d5f339f75d4fe5ee0b3aa02e2336a7c1cf570c82677673d4f75940bc95a1689e19903b23696ac11cf95d108ed5d90bf8fb73f6601d34aa04531df592615064020dd49f6f1672a747a6a949358f8a67831f3ef7eb43df90176ac790cf67e3ed1028112b1a3b029657db64465be094a885daeeb2be6ad4ddcfffe19616b63709e424fc340cbfe7f583006e5c7bf67745afcb1b507c3f85b157686cecbb53cd92671958decda2b3df1b0035fb57c81cb51130e07965aab97e1955485b6ef788f5d0f69321fcb91fa473e01156938fe2bdd4ea717e41cf7088043aa547c33a84ada55bff9b0ebc12a21209ec10aef0576ae34d4048ccbf47ad5bdc854589099f01bf9f90df48406c60841c8a06eb35cc5a02c28a1266b9e5aaeb889f21af722a9f27278a6264d329aa1a082062e6008fdfe1d2a17edaf5d42bbfa7ad56aa285b43df96321165863519b5be9af7d8a1369f9897fbd0f043090b05a5ff2f6da3f05fab37b1b55f6e7552dce9bea3d2d406b0e7585d189dddaf8ba5a6db5edf85536c442a72fcaaa424dfb79bd184a83d2cfe61c59eef42e1825ea0c834075b569ac677aa4e48ce452268542d97abbc31e50faa989d21b65b0643f206d7a3256b7a7d52004308ae72e904eb6830340879613cdca4b8ecb2f5455d263b7c361cc414e55edd98dcec7b05b61852eed79a17d308437a270b541946d00982f337c7a307c8342acfe531586a21102c7ab083f4bb0dad483b2d2cff13f114b3edb26658d0af19f76548f8e4b9cf957801c08fa9b3a00f5030fd82a6db16cca31cf43e1a69fe38d94bab54485260cdcafcf70f0879ab6f348b1494a3c3abf16929147b8f13e7032d5941162108ef4b2ce0246ea95c03742058b0ef015d6405db59a08f3481d8bb00931ea8c305392df24bbc13dbbe7f682aa794600ba73dbc3ee2bf9c82afa3af9d7887d490d7e35ba842b94233c0c80f23a53c5ff3dd0b70f91891a6b673c980b5dadd501a8b3297af87c5cf40e49bb745322494641a55b54a84c8953fd0695d806ed0226f548c5d6e4a3809d8dd353d76465f5e3b8dac0bcadc67bee164590bfbfb0074646707c24d576b5d9ba9006984b1945feefe824b4ab8376ccb313ecaeb1d08e24bf2bcb505200aa39a2c7fa55ee550d3cde6a44714c78bf77c8c9e3c2b9e5fc9be41a786ba26a676dbfc5e38a57f26c0102ae0610fee030bf59d34d37d84714b6bac01b385c0a1be23bafd6e224308d2e5f8a9404ce7e4092994ace5f92abd76063ed7ef7eb7622fc226b544270eca394ee25255c062c755af2740187acfecbf0ad7519a7176410ef22f1cd5a8b5f960cef8b3339e8c08d79c8b2a71040101a0a7959ca4483f1f8ee6e62eb725f44b70046e2e61139d356d1f1667814236a3b94bae708f5fd673d49eda65e2b6ad328ada2e7ccf61fc063e4e6d7546083d6dede23db1d20e02f4e5ce7af96ba66db6e30355148a02c4c11051986da4a5cb992175839f1f9f6da7cff7d067cfc8eff2904093bf957fd24762070962f24694a10b399a6b78a65a3624af5cbe6f54e30bbb98dfc1e57eafcce812500e98be0df3e29e96bde58ec0f718f73486f7c2d9baed69aa31051bfa4790742367495fe194024adc944291b6caade6e8db693ddae38abfedc35697342fd0cc54839e9cc7425d8e219ff6f7c1a9a1dab316f606417949b2daa7e4c4eabf33f4b07149d7560ed9e4a9933abbb24c2742c0a424e150bb6fefab0e1b4cc9e08d1fb6d34f8dd139e3a94596b740c70860448a1d93d99ef348693ea64cfda6e6071f7173ec093f26e9f9d850a33bb8894391cf19eecf35826e3c6db441a2e0113c5dc3179e9820ffd7a929a0d5f57d6149e3b6518cbfc37e446988a7ae4d884dbbf663e1bdd34999399767d3f4d28f44af0910cd50ae204fd4a87648911afe116ace889b1065cfdb9c41ccffc845c6c22a725f0d6259ad55fcc69758a4ae6d4b01526ac9e86fb4b1e2ba7d9071a5fd18a91d9648c2747572e74a0e22fb9c6127e3d3c9cc8b3531487abfaef659fe29c132a326e4b1ed9de3f4411fec05b407ebc38e7cc1ded956836a30e0cc828b84dac1634826c344d0f9f372478a7f623651a92e1653d78ded080f48a4125bf62e43c3a6b99643de9d44f8193371596138eb49c44b45ebb552e996e6350d3f7cca68f5528ecc5cf54b11bb6e7e2aa5f5ffa0217aa7a3f222679ff50521d09cf25b8adcc5da5ad3036831a1ec4f15a3e00ef9dd4dbd2e0dded0e3c2e793d4264fa4b902756bb1c537330df55def3adb8b9a6fe7026d2c987c20529c63c679c29c3e9ece4518314cd171decc3cc5c1424eea069ca87a4d48ff46df328671daa388c600478bd777f2a920595aee361a49cbbce4d02b43a8a25a2494da6c893c4d23358b582c4f7c9aad7b2388ae0fc3abab4b0952c95966488edc15d2fccc0d84f64b2d9d8f684faa187b6fee67bbb0cb0735f442d16ad63b932c0e11523532f2e696970cab40caf5aacd1498434f29bd2f53a52dddf59c899931433cb72e78964e82fa86fd605af28c2fe2a284ba49f082b974b14b858a3bfc1df791570a5c06bbc13a36e30738dc8d6cc364d468e6a43659cac36654b9e6f38e50cc6d16145f63719fa7c6aba84f907b0c095279e926a55a6d803d1c4fd6f5270de92f98930a4ff5b676f6d1077369ec5d589999f78aa63e96a49b52b586ada390bb0126d12d20a89b20905ad5153231fcc47b657cc96c355fd78d55b31d866016a299c266e9b594ed2e420409cbeea776b0fec293af8a98a3356217885b3fc36d758e9533361a03ad280a2a9a2d8acdd1ad4cad0e90610f51609e8f3f6de40898082032be3ed532e1e61e3d9e0a87062731182feeb37d929abb91638110ab87e211056ab3cda247938d1164b3a540948a75a040df150856615e68513a741856613af7d7064457d498c3036541895adcf996e73d57db55805a9e10ffa75d746181c552667e5234eff3673947d94278de18831624f177b0731d842f2d576b0620f58f09805c4cc8c08b2707a65b8faefb38541ea46fefb14aa248b3c638a1517233c4b0bdbf7fa7c1ccfb66f1fd1146183fc92604638f68f12d8fa08a0b0fb4798d496f76801ca0bad3539b1065463398f4f3598e2f30a131dc10ca7d8dacae763e3a3708836b552ae678e133cb540e75415981c8f815e52603369b29bb7c6943fb6092c9dc06611e65fe2e6a4e97f8de0babfde3dee0c864831fc8e5c370f17b409607adb4889ca2fa905d4e6a0e94b4e84db7fd653417dbe6a7e560088d609c0071a52cc1a22f443aac5508dcc733178c82266bb7a1d9e9b4a89bc8ad1fca41c90e60fd30b029f20b4796d4260fa05faa97b2e0ccc0c7274cdd566ec8a3db15a062754d0484e22eea477c499dcec555576815e2fe79d499cb5b831d7445e5dbac6b4272da132775e8313b701d59788a249ddf39c645c8d5a083e92bbe3abe392ab7c775cb1bcfe8d862c97bbde537003255434b902c9b3185b0f96e4a31ecbc490cd9628ad8dc09255d656b58ddabcd1a3095a2096007c9cba164b7fe143d707288faa2e2dbff6ed2c8dc32b1a40361d1d4232a70d8dc14470b36aad5a189391d904ef1593049e7ae4e6a4800f77e01208ae176bf1cd239b237582155b9ec8c7a2b9141516939ea88b36b3d3ebded8535404064ee17a62121f2dc291dbca970f48ff3d0a6955bddf23c2499c558b272a5010f2f94b4247774979708fd884917f5f6f35a6f598e738e114c829ef0d02e89710149850123d79f0bc40f1c628e80984cd66b5aebdf29479c0f7399b2ad9bcba916fc1fd4c2874c2a5326340454b60aa96586157f32648192b9fef8e9b4c1857cc8c1a127cdef1a378095c48fbfb605c72e71159700ea905e677aa17cc17ac20d3e188109c0840b0e330e1d23cb3f87383f966326e42d0d072bd3ee96c277e5ce51fdc02d39677460549d503eca13250489a3f44a5d706e61024b8cc0b785fa7529379c749398703be113534f7068b4428b47628689ba390f6e2569970bbd279c87540e5dff42d8c6abc078e41873081a26625c7e6e671ce5442ad99a06df4bf236e1715a1f319da2b468bb84521eb8daadca5f7a8840f1141d3f8aaf95a4b01dedd297c2384930c728ef94dad2a7629811ecf9aef04d128348a9233f8be21981b5892fc21f6afdcb4e3296c211df3e996e153016c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_41 : rowClaim false 41 23 52428 :=
  checked _ _ _ _ 170 0x2104d74ad6d91231a6ad990ce58aa34b912c4084ed194871f6ecfc18ef63b0955602bbb7df7ec3a4eb28d0c3a4e0387980ab31ca7479e27207681238de779c62ac24934146eedcda49367f45b3ee8a061adb52060105ea573d61d6743e86a1ce7fe4bd9ec260e2cf1c856e550428c9cb566d9a903c3ef514671a73f142fabe81aa6b663f767b9039707e33c8071abd8933922ede9f6259fb738adb07a59e1623262e6f03416099866062e6f89b6fc20ade8a24da81547f988e34276d832f87e8874ed1c5279ce120725bc35624ca038b30c126ac64a5c2d109ca1e7fbd50b961eec8764fcb4ee798ab02a15cc12b862f82060cde4b525d08840d4e1e93d82ae7d8a5298cc2e72ccb7cfa54bda675bbfedda553bd4061694dc74f4d221ff63418811a9daf133551368fd706355d4d285286fa4d950a9ba076d01e9c793020c17518249f8d6475bc92f12b47ab0e075ccf8a33d2f51c92c70448f4fdc327020350a028e909ccedf98572f823b9681da9efa3a3851338c72868cea35f044db511acb624f847fd670e05a7d43dea5763b6cc2092661237eef055997719be579cff55d20423d0a62da58f5326612f8fb59d8a6afa31e721f340e30ebb3a4d05b9f74e48968a324b374be154eb7aae60cad420c927e02c2b96ad9ccac5abc1ccf45da2e5f09fe556d0c9fc0df73aad274630c3068f28a4bd98c5bebb968f95f9ea2f9df9656c23a2d508a16f4cd64a1e2a599aef8fea4f22028b14b2194a85366a62734f14e209ad9cf9271233df6ec5aab82ff2a2f63c296fc40d275ea58a2e0e77b3f525fdafe742029d6f00b8c2d189aef89cbd880eb397c2b8ee3734aefe8d2f67264d73301c516b3e87a0feb0384529eb2984f32f007c7e260db6148ddd9ac9bb1e07381db3dc54bceaae4aa130d6ce1de4105cf088895b25feb6869edc409bfcc1f168b0de7d35706125600166562417b4a0f5b47a35e3e7dd1745f1c0b36280792cdff0fe25fe5d4c73b8525fc8649714b3cefecf29922d29f314266834a2759cf6518cf9285252952106bc328f10ee1fddde650dadf1a91cd69b19a034a82094ec34b039b039bc77f2d744c96e9ebf15925a6e21803be068ca43229ede41db05fc6b1ee55ead6b18147dc6a38be15530dd29acdc568a257ecc8652fb126007b59f6113a25236440b94842b6b44eddd4a9d1a89d4a891da7af83ec988ca77b63cacdd6fb4af08bc71ef85c31814875964e034b3d092a88111de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_43 : rowClaim false 43 23 49932 :=
  checked _ _ _ _ 95 0x3d8f074379c9c45d6c926641ca98644477d9b340d092e87695481b2415bd6b404fe313d9cdc09b697c4296a4872073fa0ed78890a9febfd0798b0a4e4b1450ec0e4383479acc70d34cae2be0aff93a439085358d15eec31e4f83ff24243d302ca943b6899b35c0665978af0d4e3eac9348ecb06592ab83c238313d18021bae419a84db546dd10e5716566111366fdeab5fe245ac51dfffd05b105a71f5dde5b3aa412325227894ddf3fe7530dd65127a9bf8e2513161a4025788583df8f6e6534560f22eac456b6fe030377d622a3abbaa918e2cfe130ac24302eeaa733383cb610465875d09ad3c86ee96f2a33f48ef0fcac14be21c8ae723941a2638d77eb5d5a803f542a4c72a11657e95cd3a1b89ddf5e04b96dc95489ad967dd1a424b128254414b5abc4a9bbfe769fc0025f38c0312d6f87fa14c3adb2d8a077758cade9f08abb173d7101fe238c53cc781ceaa42d0c863a23e32c95517906cde49fda60b85fad63da8f3e6728c47b78cfc75f276546df30053b0e5df3cbe89983d598d66b3d87b12a67addf566354ce9cbb1dbd9d732442f70b61e17d0cfb62e7d14fb932b95cd9697cfba681c228fd967a921c8d61738e91e445a743277985420c664d853690a41b1d3b1c95c3864d8ae22e8b2806c49e5ebf53c38f2549ceded708339ce731809630d61001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_47 : rowClaim false 47 23 45590 :=
  checked _ _ _ _ 56 0x2b308e4c36b1e81809ddd6b34d4e253ce695261902fbb7630e7f1a4e736c60ba5959bf41040d9b982e8e22c5b0a30abca697e2bb23eb89fe97269a3889f465c995cd4dbcae1d6c6378b5c90601a2995d473c58f2d4f55c09d226ea9d20c40dd136bef06f5d1e4d2b62f43060cf83e60b80e7d6e4605f94f4c89e9edab423df30f5c5f0377dd3f81fed047b84d6546ce5d003c891c888ca72276779976df49e72a9dd8e1284dfff9dfe37803a06a63795089d24aeff18fc55d6f1d29262d2efad8572ad2b0e880e5dc6e53c4bf3644a0ad3586b56996d6ef803bcc9e4faae12404b51438ce418666838606b747aadfd70efde56b985bc01d166d18854004cfe3202411a62d722203931615e80780dc3a800a40423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_53 : rowClaim false 53 23 40329 :=
  checked _ _ _ _ 108 0x775b12895a5d78893cc207bd6f94ded7f85679498f257c9efec8ceb9bb9ad32c8d40f6dd38411429ef9ee386f0112475380130ebcc5801b9854590c29d92a50e99e88534f250167cfb31d904b4c5aab35f96a4fa16305240450b4ebe61dda689372ad65c9cf971897da9bc2ebe98fec316b1adac2de60dd20c21e1b10b0bacf8dc27f10ad4980bae3cdb6c47157214758ce173aabe48aba4304ff33a2120bd30585ea11b52f79c74d996a93475ba2c59acc9168ee9111ead3a4a67a6b5a53e4388e3ce7618bbcbeaa0617e06e0efff027df8da69907f4dd03aaba2de935a62a9fe07fa61263593a7d0fddd45ea3981a0298d26c879da6f9fd92013f783063136000241e7fd7cadebd200162c4579a4ba3ae32d7fbcecdc1c3f7b3b9ccb263c45dd6423207f909cca6c7eee47ff833a09ead88deea1a34f68650294544cd3246f850f44608befd5ca0e490982bbb7fec2755e5bedf9d704607adeebb9d158e1fff255802c95095caea64bc30adffbc74831b1937a0cc918636e785099849674ce924969a478312a7c9f71157b6938207e5cc0c216ef1b5b20a51fe4d284899050f2087c63ff401d1f3fb703066b2cb168d38e0ff77fdf523fae036c27b9fb6d6a1bbd289fafca3d2ba5557fdd3df143621fa74284e61d6f7b4e9b147130018b0283abdff4bdf9c2481ea8f4cfd0f04e0929ddf7b898604304c14b34bfd4d14ede856dbddafb14dd048d5647571897ccc93bcf066b204add6888222b72912a104dac21045680443004c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_59 : rowClaim false 59 23 36157 :=
  checked _ _ _ _ 8 0xc65f7e2d987e0478e130d2a144fb72daae14d400a96a8467dc83e81c274565001e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_61 : rowClaim false 61 23 34952 :=
  checked _ _ _ _ 498 0x25c8aa4934a47e9258dd51a2a8c83a5fd36917d0d0dd1a9d8038e507d5dc322dbcf0ff84579b16209113df7350916258651d423306080be0a4d2aa544cb8d2581e010e84a6c4f12404b2e83e294b07a92bd404d33922bfbc95e3ae095d92ca3516d5bd2829479d95f97784a4db23c7d61674aceb50cf42d8cfbffc5099be402a73f610fa9146efc3aacd525724554161218e41a2a6b16fb0341c1bf8148479871123b42113371c646ee8d8fe5979ca5b6e612af8052e538d31dea8d8b976d88f2ee0e73518cfc65e9d04d6c8dca8f43b7e91ae69e806bc284482213fa09d5f9ec75d0fa36ffc818187ac3d9ac071ddf096058d19d281aafa504a52ffd6b49766ea5b8149e8eb528b76ca0dcccf0950f6fa89a4ec3446fa41657458cbb877c349418a5c16596bf9a9c155c22e55e2d4bc04bc2f10c1c860203a96a273dd0c3389e11e1436a4c6b9036687b59a5336654e267e811502f971f8b5497a5b757a794bf02e1f7fd191b0fb6f64012c2ce66538b3a4c00cd41347f4dd6a5c4133c9664f8442b52335f1d123592db6bc05ef396633e2eb643c586c6d4dc755427c87ac4239bdb41c35e331dc59c2cfc5288ffb0605b57724b4f9928463f640fd765d113d2adfbb7dd63d7027098dd4a9c91dbff89694469a2bbfb9ac2357d0f7ea2aacffd4d7ce1c134185e03b683701fc353f51e18a8ea8a0081d6fa822dbbb4a0a86a3f36d9a6b45f6840f347d009281b3516899652d90199a76ae70b735bef18d970a8e674f6092bce3085e47d89e9fd3fbca807314d79fc897a13829502c9f1b62967f51b336c838f33aeb8bbbd152c56143c4c51ab3ae71bb6534704c7332261e29ab822dcf505f6f1b427acca187ccabae1e7675085c802dc0ff59cdbe3c792cb9710eafea2a9207d55e98a4d733095192e9887699763f431538d755aadebb036e92e77e729e9132a0e07f876a3623984bdaa16506ddb55d6169ea7e00aaf841a2fd74f047227f79549b1e1698ae905e0509300ca032060f47ea3342a12274b2c08d84cf0d5da0b475efe7a6c17e3eef3945d73bbd31782fafe2331518d34db38ac49b0ecd766bfb5320da7631196f49c03a8ecaf0159c9bf37aa9d9c3e45ff95e1d882fbcf39653e23a1796add2eac96e2ec4e3a8404c5ad7720866ec103ff12f22540843a9ca04d29d4d98ce06a6ae15684c67850ae2456ef73e4fe7699f2c2a17867d293426c7e5e2fdc176db089316615ad66c2f708be0e08862201844b0662715df47f3fb114a8e6d7a0caa3a7c8fffeee892527a3944b81a44ff22c2e9cc7e74a28fe468942398e55aa45514381cc938549081e0805555282eb4fb12f8fb397db1f8db0e2b7b5754aba3f3cbe0179f330e852f7229c814aa48f69745af573b94f5ea5e0e736431166e60f3c78b88bd06ba15e1df4b031cdc2c83e98a3818be90ad67a8ddd0f31756560e9d874b058115ffd112fef072898ee9b5438ed935fa445a1c61471ed9778f29779ffa7ad45cff5c02b8058f99415bf81bb6f5bc2861f6cecb415c1b6a6b3bfdf01557745ef898e24cfc04d59cead5859ce29aa3170596a6cdce2d43121efaba589c7870813bdea06cdf81815e533019110c0bf59119bed5970323f8c9833a8516053909be3d19f00077f2c4fec78987a1e432aab6d916837a747b8d67d68ecd4ac8f91aff57bee0ade27f2b6ca4da382d592c17ee4a1d2538051e0a9df1d722fa40e6d71ab8c89f3d16cf49c4987679df6d1b2ab9fb0abd6e17d6b1a9f827c2ee09f15799782cf4293bd118805734c853ecc19cf7e687000a8df73b31d532def6f7d30b76d17fe23d4f60587dcf51e7e6bc24211b38abbf55a41230a600d222c8761a80a74e4ab8b8d028fb7762f698ee580884a027477eee8538b6072e4cb97068ed9cbcda8a60c0d2d7f4c862831df8d8ea4fc6444e64f6cd6afcf4dec62a4e75709250936f70008f1b939b738965ebc43ce83e82367e1abb2d83f5a66c9028b5a90606e64bad3cd5adf667e7f21068bb14a910c8252caa7a5876a5b98cd8d9ca5a4fd7a897058b0e97a29c70f6049b60f29f5012aa38e0dbe37b769b697a8767b4ef9469fc5591a5fd16008c7f10a3edd9bc7efd39cd9c96f59c6cb64eb7f270cb84699a23c334f46e236cc361c808960751d17546c0d94cd47162927e909883a7a6a00a55997576ed2d3493e2f96ff7c31ef25f5b1268b12eda115e817fc32888c1de6276c4b31d37b35c4376b9813abeb44471c12d8aa9a48429dd7f673712316672a1b32e7af2fca299e07536abe5571850bdad6c0dd293aaf9023fbe569737b39b53d4b0a667a6d0afb41433605f591404f2a12f8f1add0b2a4423d09184a909146d0608779afe871f54c883332506b610b1de5fb192698d63e4d2fbd20078313e722458dfbe70230dc7eecb8c76250143af4f8be240da48ab0be368b7f8ebbf63ca4341021af7ee4dbf73e82c613e0f01d7eba3911cd1141952657bd6d63d95b14dc39b2524be4231d5cb16afba59155227fc2a2997afd59bb6392cb4c66a6f66e22c1698032bdb21f830e73490bf19a390d5a2e04d4df792ffeea26879ffc64c8b52c5c43b8e609e411f835fd2686f7c54ae1363c41debca438d7af0135ec3a247c42438479045b8995c4498e7492a782db4c045250e91bf4861bc8d3f39ca67c79a2c5fd8ee0209ca491418787665cb7e47099d0b39db519792471fa0721f95005391cd952d058bd11356d6b381ae684bfeba2ac176c02a0ce21dc02d66e959a82fdb2acd2abacffa3cf52307dcdad1665ceda9ccc4d9c2e721cef21cf643c344b020bf30525a4983ecabe26e36478e72255fb129bb47c5f5cdb8203af61d9fa8916ecfca7c5072766713dd3762a913fd3ea153dcedf740fca61cb17f47f555669f3e51c04919a46c98de84b061ab600456a362f42fa0a3f5369a7dfee31d0cb6be1366a104df811b21923d69d378ba097067076fbd8e51512100a873115a555721086087ae4b96cfb18bc6d85dfc135a0a2f8fed9ded8423c55c516276dcef0a0a037946b965f1b0e619ae0c6982ba79000bb82efcdb16bcc74954d8ac2736582272c253d620b89c71f4c035b3e66ba637d723a1493c908d74f64aefb3482ab525627da9558e79f5d7c3f908b2fa1eef4cc1a09ef2fc7f96c2f3937e65c7fad378945a4a913ec26723c0a240c7e78253ee4308aa546119efe3b3afde68db8903312e493ca665843e465b672b419a8b73796d791e1360e2de6b3382052c2b0ad56553ed9a7f1cb50a480a42bf50e28b2e7974bd7adb6844a2a63e23a57fd393e045367028cfa73a94337890a7a8fc4aa653d0123e479985e5096a3fc4aa5fac4befd4d06a283b64f557129d6da8badcdd91465226457dda66ba671044da01a22e433a0d836d993dc4a00ab0e3f1ce9f03625a89960e3c0a89d6916b963a947dee60f185ee5b1cda950f566b3a578142b481966c287cc51c17c5b3849f1c64d7590ad9c5a60ae22b77a65fb8b5975d701abadce5e022e1dafea4b3767bd9018bb3e3cb53798863bc4980224ce56fe54a0b46aa640396c28be55c3017da08e730bc0a48ac33452617b9b12fc86db7d08c829c3dd03e755ef89b6d825453a2b96376af15af94f31e94a027a87197eb7cb250a236684457fee5f2c21c29ad71111b795880b0791fb9fc447f99660980c3bfee153c984a9cebc8092d1211699862c9832f8e4ac8aed313a01f6507590a2e360a15996fa841c5ceb055980bc7bed8fc8cf7ca40d7d3ad4f2e1b68e48164e3e93d37ff0058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_67 : rowClaim false 67 23 31775 :=
  checked _ _ _ _ 124 0xea5afee5a07e80020299efbc6240526e3cff2e523a126e08c6d0fc4947c55e308bd6c609a3fdb52bbeafdc02448a73ccc8f6ab5f9a4aac99e0a7bf7303cb81a8185e37051bd70a3081fc0bd508c6b1212bb4af83bc1d6511e56ac34d3ed907f45a4da54127299a171642157552c5886825ed1080f221f9918c7fb73086905f0eaef6c71cfe6f763f51981512702796c5c6a7087480a5ca674056546dd4ad65852e64c02bf7da54a2b228ef93194c4e75c4d46c39d6c72a169841fef7f39c68dc1a542a4dc7be3191da12481e3ba0ee1de086d028b94d553bd21a891c9dd683f9bb4710220a5f21bee145d9432a89252725078c4af3b079dc8bea720a32c1561dcd1220b600485d99e1ac03b38224bc973e5eb8f143017d330a6232ea6af397c2a5cb633a8253a53ed7e4d6879a4ed6305e0d00346c7e3e35470229b1f1e59f37b13e5cd439dabc785c69d45af351316e19f08dddb888b20db17966db2221d7feb9d54e8e6cf559a2c5d33fdbabc19752623bfa4c6ebb9a52296af85bf0b4df47a10b213288041fe4a2cdeac294d67fcf6b9c7cbe5578e59edd183240e40005e412b4a4ab69e30746c436b9a834ec491a9f376ea9decb7ad528710f289ce660da8a78f1daef43a111079b948a9dff432d3ad67b0f3e9da596759fcce9d342be00a9e96028203379fb602aef63fa4fc8bd7f97e1a2126f3d0b0c2a76f883c53e382363b7800fff3250a468083a3ae9301cfe81de44c73f0054b90a8cd1b577d42485e7cc3c85ed56a6b66317b71ea863f7388b347eab2e280cefcf50a56730027742a076e3dbc96e73f1740064337ea54fe5cd84493af6520d431746150536ddfe773a6b3aa3690dc710f0e7b58e08d12539c90a59b861e03f0fa236a75b1a20815c1fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_71 : rowClaim false 71 23 29959 :=
  checked _ _ _ _ 88 0x9561ad9c3327187f60bd3101fffd2cebe9f061868d5361f5a0308fcce0b0ece44a7034a6bae795dd2741bfcb8805fdbcdcf5c34c373ae49b211354e191d2b1de28ebf7dfe24cbe7209a957b8363620923fa178da861a5feb0ad1adc198d11569d55ca56831c405f2e30f1cc324718ab621214a56e96527c349b0089004fb8c638bfb50c01db220c2d4b0233f2483269f809578b6e802d218af809b652189de7b3085628d703bddaac1f55cc72577c3cc9b3ab0878b6bd99072c06da90741d48d37bf15046553e24a3f49d038e531e6d6427b81dad6332b561f876c95f62fa73f34e713324db77606e875882faa2b329af8853c2b3fc6c48c5257352d4a98ae47dac1c8f42e056f78316f7d6a683115a1d3df6a5a467854933703fb6bd3f40799d22297ae0142a2f3a96fdec32efa2ec809d284b353a2c4b2182269e1f10e7f496fc5d10eb3f0da363e767623147d93072adf677f133a6d5c84ac4473ae22fe21fead3969e09ff92b1f7c6153d53b15fce668213528cb5ff06ddb3b97cbb4b221018c4d7e19737a44ff7468053c333adc8c1cf8b2c06c0e4b7b78f21bf4da9bf4700b2a7fac7878a45854d4a7ea2ca5d78bc09e336b360238576660118cb11a00381102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_73 : rowClaim false 73 23 29127 :=
  checked _ _ _ _ 354 0x12653e6ffac3516a7c30ddbf662e0032b1d959e65ec08eddf5c23b37a0051f09535cb0ff158269e196a7a756e5c01f8d17b8bffbc64a3c37be8a8f2dcc84f34ae9238f9daa5e810c4cfe234039c9b7a284f8fd73c7c2128eb43b8139fb2ede1c756adc9a74e0041067eaf62d106c460f0e88fdc32e5f33b8c0ed6846398faf221d1d51770e9525907d784109455cdd16a78d737fea90b20ddb213f2c1b3b979ee9b61fd0d6a1043f9a85251d2d8e469586e281976342c09f8e9fd34ddef903780c0cc8a20ae21334cd9f6d162efac070e2310372e3695d556f18929188b7d8c9f6277be4bd8f077dd38a4c5f671c041a906822a3bed0e490b3ff92cbff3eed44c26162c4d2b4ebd7a509657d009a84e5980acb7e5e41c96c8cb1e5114c3b23a426ed7b67c1d8bfba458995ffd667b92fe133e4e4d34b96b122054c8fb856eb81b81e4288b94d121a8f5cd7f3f943cc119dd4a06dbe88c0b46220434438dc505fc0a3ed27919a7836db78b145066ff3b72039dbc67645708075d584951e943ef49626a9c94123a59509d819c4d413c17413b794a1288a98a0668b099184e78b564c2f4932246628493348929e6e56bebc58455debba83a77f8c1625d50b06a07bf0b5551c8fe1d96cf981a847c348e76ba9febc6e92ebe58fbfcd0e43fe22eaa946a4b600e01eae9f96040d8d40987f47ce45666b66a1569a5ce1053abfb2c67d54bed575b3e8d794940e30d361478cf5db006f7c56d7b9be618b5ba3b797fca803ec28a2d3e91f1a6395b61ea0680ef719e806450c8f6b2cc97da4c2ee9ae32188fcf811941e12e807cfe1bfd5d4f3328bca1d45d3da6fb13ad3d1b39577d20d8da1007da97ed3ff30fb035ea23838982002fe1b0a4c264a8075ed7f8dde8962d373386274d995a72d336927e9703dbb5e2bbba014f953a1ecbbc635db3df5ab7b4a37b28bdbbb809f5c8c7de6c1e83d82e62138753b55cfd442379ccb7d47a072f29905004eeda4343808748b39b99600215d6913d90c8b417ced44340f7d0685cdce7d76f04f3a43a911ec8f9010a235c9520cac84bba392cdd0fcb213ebdaebdb10f4e3c6aca40fec637f58fa3e387ef76e820629b3c9ae1551edf79ff5c6f051537609fa129b36aa1cc9b9d95871a206ea44798e636c3c6e45216b0f484c6db16db8c799793e44b63186ba76aa589002b214ea8c4f436649d854cc108c6d7585ec6fa4c1372abf9273d3d8a6b7f5a1192f0abb50d2d3e982c5f0c0a4b7e8d17c5bf6f91a4b1af18a1ba3f6fd92b768d1527bd8fa504d5fdd636a5b46f382399369f1633516509083b3bcd8c1a7e66caf6d0ecee6f1d1333ce569a81f1cd27316d4da98070b4d629202c053e25ce5110f968c58d8f7c438aa8929f8087ca9dcba327864f0385e05ccad52a7f491bf81369bd7911470de213683eb414f007e47f950ef3fe3a2da4ec0b5426f720ff6b6f54f13678438876501223ca341b226973242e05c9d5f4d58a1181b50fb90b5f52abcbd3ce4b7e87f99d5a48923b3981f84d28a33569181ca709506b72392e834eac3e954834d7443d6c491fab34de469a022fbfde00ed3d755962703881676849eb3db376e28425ea2c319de7001fdb0c688db5402670df8d6613e4e85fe5fa33c864a6be95f0a0d5dcaf05e6e306ab2d8226449b4f611116fa51b0129aa7ea43a36d5762c4e286f573959c3880af7d0bdd695bef5b2024aa785565504a4ca56b57ac026374a7d51aa8780a31c730e436a90235c460ff2e62aee20eb49d5744f36c17850a752eebbd84e5f823910e9ee340b27d6370bd2d6d223deab166faf54c0afe662b3afe5a4bb7b03367149778f5b3ce87a52e1381f9c315b5c4312134e33711dd323f1708f23dd836db93a0464e59e70dab9aa40173b2fcd727365285ba16a800e35fa5b25cb27d574fed21f314a820cfb54ee64dce80001d716e152a8371b6f8dcae14e76fb69c6fbea22708412a785ed8855bf503356ce4b92f00e93410b702a83abe90dd7d29a4e8e57ea7db752f0d04de9c0c78aab56f1018278ca7e876b478e1d30f2c8115c237c1ffc173a6ce172cc8f0a32bdba71fcb4f343e01e415a5be8724a001ec2b42a6b75b9c62dd41d453238cad9966c34ae58ff98b788881f2a60fc1878c8748c48c4cf93693f5830d2b1c4b83c157ae225d800aa38c7421fc4ce923da96e48d4e7db4ace380233eb7cc2522b311f389f8c2fc04a0bbaf8ce60bd15a4d0fab30bc79e4a6e2ea6203fdd5fa16de5670894f96892850ddc12e36eafc9ae2d191af75cbf07cbb82b32d62ae8cf13900fe8c7eb8735fa08b050bb7104a0a9597b27a5271d56cceb0d0c8f4b7a6cae87febeaae7773c248785d7edbf9163d6453b4f1d5cbbdd6c339234c7db8985a9d69e449064fada9966429f1788d1ca1ea01dc457335dbc7f23912b9f832a95702a9219ec3b31ec0906853fcc8feab6598525e1037e3d8f1ff42d72b99e2cea076fdf51f6c94d3247cb2c52577291052dbb050b03abfe1a40d338627953c273c280358c152b84d8968ece2d03274175ce9b623e0bbb900fac22ac086f20d4486c3ea7d3223b641f284431e30e5240fc9619f7daf115a18a6135318729011dac75decebe628795a318c85421ff4f8515ab476fb0be8ff9941ee4d588126e20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_79 : rowClaim false 79 23 26886 :=
  checked _ _ _ _ 67 0x461abb1fa4ae576a9dd2323c68dc04510d0c64ed17f071134726d4531c9e304a6cf3acdcff2f73c005665a90cb87ccbb475b797fa7794b33184e30a40f5b87bb7753b7aba1731c20e52d31444f39f4817b1095aeb72854c5f38032744a1f571061e1c5d5ebce883aa85f9f08b6742a08d9057e555884ef354fe6e7b022333fc3a464190fe9a2b7be220f4c01b250297522aa5795d69080fbb044948fe7d75ae8d387fea2ebe3ea5f60a8096636464c05771aef516dcaf9025e19dd7cdfce0cf94cfc6651c3fccf65f0fed967229701340e833b2e3a28635006556477e94c1e1eeae165eb5f80f5a8ef5c3de5b6ecfbb34ae89fb904bbbd548a070a815cacdf5749b2aeaa30255fab3d207c67dc38a256928fc855f0014933118a6dc7dfdc06473b1cc2b8173112baba0bb5fe38b73a853d56f34ec31a5feb2ec9ee08482f897c560490a8e7e810812cc1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_83 : rowClaim false 83 23 25575 :=
  checked _ _ _ _ 28 0x186e282839d8990432c0f53bfce33b09b14b3fd1e3477f3ff8d5497a22b7fa71cdde577c6cf6c4dfff1c90f313283275f6ff471aa8d6291c80c74a81b192673972ef065cc24eac43abe18f13a00611bff7b72d727c0dbda150572cde3b9c275029e3e272a5bf6cc77372217ee593119c03c4263bc120ec55ea3be8186296b85d01c252947003c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_89 : rowClaim false 89 23 23831 :=
  checked _ _ _ _ 10 0xdbe7cc525a9e3212c226d06590ba9e72fd1ee6c8bd3d578a8ddc2108f2905a78a4bd8d7856446622d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_97 : rowClaim false 97 23 21845 :=
  checked _ _ _ _ 136 0x1cb3dd53790255478c4e236f5ba4699dd1a3f09aec3a27df8faf85aefa2eea23ac8ba1baeaf066a3aa1073baa65ffb928e592bf332cbd239ccc502911e215c9e343e72f8398b01359a8c1829d29ce2505f26b2e6e7e714d78b9eb76bab38d659ebe70c59c4b45cc9275d12f94a21d5f77398f0e7fede5d57461c2311b2c6f9c27d9727181cd28de9e8bf072eb0820ab9dba012acdde025df19e115df250fd0929aad54995f16f180f987a9730a59fd3e2f356c86bac9a39bd8ed94795277b9514851870f470187c2e10872ab43cc5b3baa8dd9c3cd5f4f2aadeba50fec608ee5f0c0abeb490d2c4a661123409ec97942e6c6565e372b25f5d245cebef7a011b4e369f62099e24b6514d9329b2bc16abcce0364f81f29fe7f0dd1cf95db177e928acf4944ea3d068ef4fc87fa92b080ae2840249017e76eb3243c2f57aa593b3145e2c22ad35cc18c32acbb3073fed0ee5fca1fa07c9661f3d0014dde1be8bccc2d8a3dc8c8fe078d76162ced19e8dd80863bfe29c42c2d72419d5902fef9d2f45e26d9313d99a7217c80293b922eee0055d5f81746a93ad2ffcd77d1bf0b18b5f7f92da6a98708c930ad9b39cb58b94f43d63f25a8f3b0f2a3ff43d8fc61f5a42ef64fd4430951704d01cf36b71ede49b2849cbc81bedd1f1949c5f314351d1f7170a79f361a8ddd95cc1c06942c9cd70722d3d1826c33f7761c007a42179723a3f2a71ff68d530b4380709e60dca787e5ecf195307a7f54d5d206a11afce9c5b348727b2d757cec4dec80bab742e0f93348f4460de6440d54a86982130cccd0ad05b2778f841cdddb0dfac7c6ac3892af12aafe0a7ddf8f5631093bf10c1bd27a17c88102b695c27d9b50c6694d04c3a811f4db83f996ae9b67939eb15ef48d84f45a784a0ae4bde4fb8f15453ca24ae25d14d0d2b611f79c78f02305687764e460997f22a734bd5ef46a5267918cd1c80df91b037ef0a2255abd89a24aa63c61b52e80cbde663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_101 : rowClaim false 101 23 20971 :=
  checked _ _ _ _ 149 0x138eaed2586ba955a9e5f21229fcca006dc7773560c191eb352d40497e1a4668cd46bbaeed10ec4916a4932eaba8c3dfec1558c4ac1addea6cc637666426a8c692019bffc0c02575050fa24f255d94b5055f72754d675e60da36593661c337f5c7139b7d176101b588ab85a1dac05a542b37281051274c93eecccbeb276256139114fe263f0ebfe9183e45ec6ab903fdb3df29e11d6ab6b63622e540500866542ee67101f566ecb407110c70ed6145d97bd6c55ab7fcef9fbf5dd3c091ab2b30406c2a993084b3789fe7bf30f76bf0714bdbf1dc7b56c9b8aabf1eb313101d0df198516a15b6463dcf97632cf56e3147f355116b7e38496d0f49e56c8fe7dae28e88031fb0fdd7a0fa51f425d2265f5c6628569c96013c55ad41579a33249d29f8f911f4f44b928d7fec3e6d26df56fd2054757e5cbe1f71ddacfa734c135edeecfcd6082e0627c775d36437ca832d0ea5a8157381cd6073862cf106a067c9144bf010f9c7201904b7eadbe8114ab00c2c49135a5f40252dee371d99ef2069b5fe9a6ddb13274fe74616b6255bca0ae81a782a01843471ab361df39df14cb8aeb005b1b29a59546310d0e94bdf03fd29221d916d1ab0768a7a2907dfbceb2290263d1189f4ef62f4d7e1f89551cec93af93ec5dbeec050228b6eb6d13613c402df8403e3724fbd390ae266b2d9c4fdc085ff7b166b99848f58a3d74eecc11d57e65052168da4e2bb90e9e9dd629f082ed698024b9256ff9cc98a225355b0817197f8ff24ea29253e265751ffade0e1a31327573279722750bdad8654d8e46c0a980318e8d848530f2150a572d76206d6b40f99ec5b14fde54893b39524e04a4ab7e8ad98c7d51fbfe708080d3c1ad342f73de0133f00fa4e5264980b76fb2a9609d8902d94d9faf638694719372aa13d2fff9056c5424ac846395f399b1e099196f5058381224cdba20819d8cd6220bedddb3364e270c36b03cee85c8e83ce80474f1bad092a60959eee402fcebe120ccf3098d29a0686eb6e5c8a401fc34753348fab48495a642ce4622ceee881776e13a31e96dfc774e9587547c58d78c7a80bde20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_103 : rowClaim false 103 23 20560 :=
  checked _ _ _ _ 59 0x17e4c2c15941de43fbe3b2a165014909e50beca31f21c5c978245ad586b229952950d35b654d337795416940d9299209bf974cdfb50267c6e756de50fef7af9ebdf693b341ee07581d632c55a6ba7c60186a23fcff5eee43a176af0c20535fb85c18dcff8870325ef4a92fee6a700e352568d5b02994bf3f700dfd92931522fbabaf7b855fe1f1c28bb2b3508d66bae0bd2bb43e12e6ffb67eb9487917ef21385c1d8a605a7dff68bcbf073975303a1410c3bf3fd29fcf91c8b0eb99aa507caa4a4affb13ca584e77bd4e837124545c28c341bfce4b7d181ab387b36ac1669a6672cedc14bcb98e6a209858f59f2acc8de5ffeba550b57bfbdb6fdd04b26d998824ac8269e348224850447fcbe7fbdfe5ea9ae754f7ee26b0fd021025b77c920064370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_107 : rowClaim false 107 23 19784 :=
  checked _ _ _ _ 42 0x10b696afbdec49dd200dc30e14615fa34317fd00ea3815ddce3981067f17a23dd7dec0e4f1102fe611f727c9d8f7e2061b37c2f6bf8035bdcce2ce84014feac3d5e9b1712b5d6de1807b82eca67c0394d52d207f6d6a0ed6f064624586eee778e8670c12aebe3569e75e203a028f2d40b767d548ddd71f392840273de952dc8c429fc32d4ecf85dbd2925f9e34898f922c18a8909607ac5f52c0ac4ec50f472418a0e287fbae4c9ca2c0375882506604d907820732910ce11a184003d020b567b10e77c688c8feee6bcb832bcdf3d005a0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_109 : rowClaim false 109 23 19418 :=
  checked _ _ _ _ 109 0xba2d0b285105398052d4630651c30914b6f9f89a80dce1c6367cd3d2871cf6fc139ec938351f46969dbaf9ae30481330f7c442b3c2fb21d15b16e223688048120f7e7635c9fc3d98838b8838c61b06761b04841b5bda8101cb7f68ebb7461d751c0e0282fa4ade62bbc89de3ce73c425fbfe728b2762a2fc53fa0010d2455c73167cecb69e4a8c92f3391a0c551d86a66bfa7080fc6f61c17742c1e6b8e1f5974a2c5a632dfcc9ff56bb5d7261e3398dd288a41d3bd6143deed16d9a64f8cdc999348d9362faf08dad04b13bdc53c448e76eb04cb4121d5e75a26d6e5d61bfd37303c1a13c005d019badd93962faa827225aa75d783b466df0a71564ca16bdaab07a814e48241573dd07fa7e2302633870d97e2f2d4578f63d4f8b39063d3c61520c008c52b54012b866b139db4e45eb1326f584935d0f7a0d5be6c58b91c940c3a2a781be14fd83c8e3d4b10e7f1b46731ccf20f3983b93aaaa75c130d74f0979c843501aa43f700c9c1742590f0e0f9c73ed1c6178782f0dc0a65ef592aac111bb50b32a21b9ea2a9dd93671ecba10ca938f94e811fc5aa05b224a9292ba54761e945c6ddbf1a957fca3bd63592022d78dc32858ba8c6577e946858e44a067f677d296ea0575d27ab2b0b0096d383b4e655edd9555071f4c3098c2b0d5afa81ccbe4e8f5afe736ae1ae9077b527458216e7ea4d38fa64e8c3837cbd9fee25ef359a735d8257f656691764577f850ec346610bd0d5573f2d5b94d6213a7f4ef55cd0bc0a26ed8e1effafc8ac4ec1111ca85d11708d01169b7c3006c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_113 : rowClaim false 113 23 18724 :=
  checked _ _ _ _ 129 0x1d1aa6d45685f5c26ae0dfb50e3014854e1ebeb23e214b90517b3de9990cfd1570e6350e85c25bcfb3b93040dfd939259fbaf1c030b354f0c3acea5520c120dd3d4c5024ff97e0031fac301da9d9302bac0653b53eb034c217b60599605039ef89dc32bc2715e37374f7ae9f66f7ca7e347e68222658859cc5e1d4c4e48405602de6a4b8d22777ee8d9c3d099d490c4a491390393ddbe87790883d8a2fc50c41d8d0ebda187225e49bcb8ae261e06c3b368fee6c9112ed7ebdc37ca6571e49b6638471b691076d2bcf689d59ea7523515d05d256e18b6c30e9061728c2f1188ab2c5a2203df5b16289dbfc5323e0fd66b61ec5929dd59fc63852e28c015d0aac5d32e9aa62c0befd55f6b276983bd1fdddf972b53915470558ece627f9da9815587a5432c0be30aa76ddd9d57a6ca9118ee06501b42be1816caaa199a3261f487a98f72f045453506149e23ef0db1c1eadbcbf0ad7bdff9b8b2a9bd50dcc2d84e4fb0bf8d4bccae6f74b67152c1cc85ea85825c02209d4b625dd69856e5259b353fb8628e4cdb19a8be8698a621c27ed7a045bb367828efce21866e59a21b09a4e2397be47e79d5096485e9c001e98d9d30dd318e4d50be77a29040728067f2c38f83130bf53fb6e74b86e37ec6ccaf52d6da4903cdcf9a481d8f9ed3f33cd11ad37410649eac80a8fbb114a8350b1ae1dace59aceb33011e44180bb5388a6b4ae8e6e8f10de825a2c45de914170c9ee801a755e82cc6ddfd614c5e6763c04fffd630a8fdcb6e1af4cf24bd1d4dcce93afda235e41951550a705b3ead0c1247c7b01e5441697b6ab08e14b193635d3c0f0188d11c99445efedd431ee00265b1734954043a7204065cf964fa2435b67fe9571a701ccf4429d17e9b3588fa80c52a2bd0f930363ecd0ca992e644ec7e90e6f840f1ce77809039489002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_127 : rowClaim false 127 23 16644 :=
  checked _ _ _ _ 78 0x250ba20322645228129f4f0e62f121f11df410721377a863742df4c6ba875b9de9c5d00536e21af134fc419923a30fae8d4aac6aa12fcf60ac8ad3d18fc11db744eaeab6ba1cb9b5f65eedd433391167cf539c4fd3cb2ea541e53fe58a77975db90f6efdc5c4437d6aec9e26a1336233922fbcd40b73e356e9a8f9f1d68d57a49a4f7fce27c5eefafb2178a2edb3ad470a280f08c6f56276545408ee656939d40daa1218cb9d4cf00a424ffeab94f6ccdf8587c5e3bd43e5fa07eea4e7fd2ea05b6a6d8235f21aac7ec9c0d141cf3b6f5e47dcb3785ec44d7351054b87ac5469e9262a7a0cd8fb2e8ec3205c5018b1d0ab15c0ff5ac3bc0f701ff2656de73f73e903dd637f7cdcfc31b4b91e24466dfff6c81b63060bac53c493e72931c0151eba60f4d44f9804981e27859c00175c081e541a6e1bb23b78080be3d8785309afcf3dbd90b3c4b89b9c93127b30e8faefb5fad2d501a06e124aa057fb2d0766fcbd9129bc5b64b8fc9bc51e806a7de42d3d08110f2d7170ec6e25433a4851032a4c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_131 : rowClaim false 131 23 16131 :=
  checked _ _ _ _ 45 0xbc7513f9f66e047f87ce5e8c265bb537ef144c17c0f11a418ccfe0a177ab6572ae437a249df8d939ddd0c2a0d29137b2e160384ff8e650c11d60afddcdf9274fa581c0707d9e61712f75353f69ce9294748355dc151f6e3525e285062a77365070c837a669a4c8b2bde7db76f84da9c84897c526a4fcd04d3c8849509ad8872301a3834cfe16639cd724afcf3fb79468554114efc6d0f871956488b957c32935881bbed829eafc06eedc296c82ea74c3da2d2aed3a4064f0b2bb31aef469d65ea5dabd3926f84cb23094f95767574728a7684a5b825a9be1b00c6559e300240a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_137 : rowClaim false 137 23 15420 :=
  checked _ _ _ _ 104 0xfd142edd2fddd047ab13b7b073c7c3583644775720038c0b54eb01e8e405359e909750b18fe7f9e14cc792979a370efdd181beaaaaafd4ad27c07f447ecba50e4711e542022913ea208f825262d3d59129af95b8e82dbf813f7d1e243a970ed024c815680848e8ee480d97295e726ebb4928d2fc2a8b15a7575314441e45daa7db7ad8d2b7d848376d716f8652ee7899a80ae481df805b06c32ad6a5f89db89d50504355b6f4ea73d8b720e752d16ea40f850176b390f7baa43871ef6c2ca71ef7f7d66ce12a45d852a720bffafeac80df97ec30070342ea6bfed73280b7e964bb6ce81285c00bc308465cf9fb5ee836d754e4d3a0e0698778971ca6c6402cd19e458f6519c15d911ba354644b9d96daf0582edd4a17aeb4a02dd9c112250b5247f3fe69d2c5e501de4a6dea5e8c86a27be6b5beeb40cfb7d2c7ead42c49164f7efbea8ddcf3a1798a5fc4442954212c1da7bfda0d04156d1ae95cb52869d7677c9bd6856cfa678ad9770808ed6e6f368c36d057d14703b4d876d345779d9b2909c1855bc05b53febca7745220cd6fa13c162031971253b76bf5df3b7fa35ef84ee474fb68234a07a482d6b94d689ba032eb041704012595350072155f5a503856f6106b609852835f18df2c8d5e638d69916d6fcad44a235cefc232875738a6f746d991256d8c3afed40141faeb02395a05277f41fcd61f0252e9382d8fb4fd749ec9f5054c636b8e6f2a059e7878201190967f0028 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_139 : rowClaim false 139 23 15196 :=
  checked _ _ _ _ 40 0x53763d5cb2d0d9cbf3ca60fa25197132e121bcf655dd1a729ce252275d36ecee9bb881cb7cc8339de715a9f39c1246273b1c1c4f373e880982efe5b969c4dbe0ed31de0a64bfede24729a6a9f5695124a4df569e61ccc8b20b187abdb535448ee6166235d3b99b14ab53709bd4e5275b7863c87feac50ac9334f5a1b5581de70ff90a97ad57773b40be558c53fddb29344cc8de546d777c4e346c20ac2400421111dadea360e16ae39c5c746a756fb173607b12a6ba892dba059484a4e2ae425387ba08023de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_149 : rowClaim false 149 23 14169 :=
  checked _ _ _ _ 27 0xee1e3c1f018d661af2d963cbd7987640bda4514be8d012364bbc63e5c650935cd2cdec87b604fe91c3bc59f4d80b8a0c0e77106fdefb6eadd9697d1289516f92d76b97e51858cca7b7c72b835f5e5acbadc7c4e0830e419a48d543f7725284e19024da0831bb0b0780e73bf5cf9a8e86a6a3f1553c976cdf630eb277ab945dd22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_151 : rowClaim false 151 23 13981 :=
  checked _ _ _ _ 80 0x497c2482ae503a1ce9a591aa87c8ef886f81fde659d1db23f5eaf36c2cc6e37536e241bea2b8a02e83636d3a2d6264f01b817dddbb4036e6fe7f3e6a57e0f2ce6d0ef13f2f3e570bd07eeb4ded804b26a2c4aa521d466ff85bd9db53b8992a8b88556ab0e8af0e090db8f3131f5cd76486fcf17d4a1d027ee9881c834af804ad602925b139c7be4af96e96d778ec6ac71234851fb5ea548959bbff8349088391d6b09717c7acccdc7ceab998987026b1645b2c6034866426da9f5c86a354be3838b727a8648bef2b5235e657e287c3e167168c62bde29b4562f7f288b7e3b032ea8ee05a359579d6ec882a7a3dbed48c352a7a64b594f3f71674209436369b18ba43ca9c3de8158fa836cf80ccfde29132e28325855e9beeac667e609f45105eea42bb66a753a484a09692813e17c5a3008939b953d69651c616eae97a3c1cd495815425acc04497c0fa8e0a8bf55a04a40248c4c64e66b2ffb2289e6ae4619db981d2903da03b9d25625afbf669f1d5789facce35879a75d432135b2a719c0dae9e15f7b4f6200d87b07b00181383d000c30967a00401102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_157 : rowClaim false 157 23 13443 :=
  checked _ _ _ _ 91 0x63964711631b68f54639be9409b8684d3258ea6df44758fb9be242e019ed3b2eb65ceb4bde2a2e79d39dfc5920970ecafb42409525f27a44d2b21fc070232463f3974d7290b74a235ebdb632a05c52ca2fa5840f45dc21c3363772d30e09cda51cb67e3397896b66043e1b1b3a9834bdaad890906ae87b072c8bef435c6b193e73031777168c6dd7f111396b306d1afe1215057d69716c892a79c45b88d018f7cc01f00686d42f303d16e8bcce59ed98427544edfb427aba4c4978f0535e34d75a10fabc17eea675dc4a85bfa305aff38e03fffe9bb00754038bfc7c7c43df0a28efb6e836537db97bb35b9b08fab8633f9c25c02cedc34c4ab4cfaadf12d1a9957f59a91adac7e9f376b9945f749a8b49c9798b32a3ebcadb61f36b3a06bb5690f00534eb5dad2c4c59489299e5db3b8269669ff6e7dffc3ddd68f44fc5c3a9e51e6fa9681be642d30acccb9ee129ee71a909b101cc4fe8f18cde163c87b1c1b3b7903940d97720607263abb71aae170f26b88e8270dd5d053ef8461fd33ca5943990939ed28533c5c9993b7def9261fb66696f28f6684608f4dc5eac1b04a378fb001c8407b06f19025da2bf609cce4ff48734df268d6134fe2fa8f519f1a64cdbc2ded1cc7ae563bd67bf1436c0b813b60d5b0012 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_163 : rowClaim false 163 23 12945 :=
  checked _ _ _ _ 98 0xd808926495fe92955fd739620725bf681c3e297b409d3a2272a6c42169151370950d4480bcd1cbc1f9c4e2c93aab4b6aed77132bbc86c0142ef91abad17eb53a9a8ac399566da820d95d2807cde12bc0a416a7db46e2e5536b2c0654f1eb363f4b68a45130942944ae148168a2b445e78db6299887110f2f2805924182c141a898ab8d8267f838b70c394852419f3e69a68f282214e99d8d507a794c8e74c9d47a678cc6838a966f1d685b79a1420ff039bbe9516d5c7992f0028d82e7b0d2681369e045472e3ae15d0d753d6c0a4636c369a2f40754a058aed6d19b74abc8b6de25ea82f5181b1d999b753257be9070b4c9f3c6ea4ba4c53c9f6fb628ca621e47ffd03dc3fd1c8c264f5245c2db2af348a225c32f2ce1bb2a91547747f62d525f9cb810c8e7359b6854b962caea47fe533dbab30d81e6db2842d4982313f805fea3be8375bd86bb3a4531228b0f179b06da7ad8eb111a9976268dcb31f1999b3f42da6cb1667bae2fbf3765eb2bf02086270751dd017c4c5c54b922ea0bc26c9f995137a4cda4a40996b3e0af2b62f169626f82f4a7ae725573c450d16c689c2a8bad54b26c5f32e8a5e2fcb59358571c0a2d9f33a4953ac6e4ca318679536b57dbfa7904f4aa134e42ddd5194e8beab8f42e9e18b85c3f5b3c9e488774e303b926baba60a1c2c77363acaaf49c88ea6ce731809630d61001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_167 : rowClaim false 167 23 12633 :=
  checked _ _ _ _ 27 0x23c1a8dfe6304b9a6e5e71afd2f969a925ac2876a7a062b69fae0579884a353a9ca8783691b8e548133679a0a3e2443883a95ab85ef49e719bd8a3cd2f86b95ffafee1b4c0689bdd23204ece5359c04d363f2fec27902cef5d391a6929933e3cd12d0abaae5ad5f531af561b1df0d4d53e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_173 : rowClaim false 173 23 12192 :=
  checked _ _ _ _ 84 0x1e5b34098ca793f832ebc5ef6b26f7ad6ac644ca36c53ce449f018ee6ea31bbadce407b4d9f7d26ad3906174f184afe88718c7b48a762b502b746dc198d57986493714db02bce399947487aec4426c67f436ddaee6ff3cc29c53a57d3f8b4381afdf74c985850d23bb2597dddc0f1ccef661d50d5046245abb3a771e1703eb0fce6f2accc27b982ea46a7e2f88fded82bf1109eeeff8e809362b8f4acf71488245abbae31cc3eef41b4a762340d8df3f030ff4db4b8218e0c11a9cfe9968db88366a04612764ec95e47171bd7fb5b859cb4965574ef18b9b379432d731f1a3e06a37c26a6bd146106feb8a2c5d1f18a8aadbe7656500843e79313bf8b761bfebdfc624781f694088c46a9e1d46df00f3d9b369df3c51710e998378596b7ef420ffe5a533976f387f2bc7c8c370aa8522c801b34e4304c8e546e9718cb57cb48a42e6a24e56b4518e26044b2cc429b3a6835e29018cbb2c1be7af8a0ad4c0b5ba425e40c1ff7099e4bc680ece257e2d8dcb9446f730afa745b02cce78e05088bc3b409fcb8b4724eed4f2165b4931a62ff43d33c2de0d054638bf15c3688d2ab76d010645eee0064611ef0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_179 : rowClaim false 179 23 11781 :=
  checked _ _ _ _ 21 0x7408ac666762e5c2531a9db7be1236166b0c605c218366cee71bbfe61f5f9d1c70c775d7ba5893ea157ccd42b6218790c3b6a7c3a4920900a28634ceb5293180e2bc7a4c1f0e5c02971f439fd00087a72a9749d3d0b98d982aca23ee810e74565001e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_181 : rowClaim false 181 23 11650 :=
  checked _ _ _ _ 256 0x1592605444b89f9529f6f26141c4ad2a53f966a162decd7484add41ba77f26bc272872ed799904dafb3a634bce7ea33ea379c1657e6bf4092de2adcbb81f448f82f1f5b22f67c514fca1900ac7b6a1035285460ba4717398938fa285fe4ae0d79ed13d59a0fc6dd45589ebe610778bda078366a134a5715c4ef7e41534ffee5ffc51bdc0761218295d234a4739a7e349065c5bbf92b7e878e8a4c34ce00f761a21bfb13c6be889f20eabe889ef366f18e1cf1f4bacd13741837da0d5afea413e8c62497c66d985741a932e88cd67a9909c95def2eea18830be27ce8c42ef4aab05484c3178a7c8d24ee50181df2000300a3db35803835450dbf18161fe2dcda20826f7b09be5c5f21b3ab80cf06f1c903d44c8b84eec9f9a19685cb8a261f8ad8769f0583920d2a6ea56c2f40bf45dc7f87a53d3a8c997eab530ae443ddcde012ea4a0ad3191f56b641a6c8bc4d106ff81086678f6e6d19550fec8221b677ce7c6073aa2c67296c86a79b9c9fe9e94ce9bea8b684fca8c19bb98b8644d3cc1926bc32c039954131749dd05cd442040bb6244dc97b6733e6237833bb2af2e4808509f58939b588e89233278e4a0b8f8e4cc9e61b0ad2133533a6e86a00d96e59dc45baef38ef842ece9bbfde72250b734d604d417fecb27826f998166ba51dda9353a38cdc0e38f59d8dd1282555000d0fb5cb94a375c1bf5fc69bdcfd78d12f9d5965890e0a0068b2866f030cc9cc3d1a681f183a01102f7ebd0aa6564136caab035ec777abdbe12f8fcb66870d7db4df2e59fb973b426b2e6c08d1b17713c929b797f019de7e360f63a03e652378184fb7ecb1b72c0be6867a9cd6291fb42410cbdeec9e22511aa9429e983a27e51cc43445c7757fc970bd1d342a1ea20b8939e6195208ecddffd15427a0f44aa52a3a651e43a7bdfe63cd48717de038e45f9b3b04c7a56ebce3f52164cb87ae718122911f47e5655136c4744cd06e3c102b67ee6d3f304086837165fb811dda8db309187465cf3ebf41b801487332f10f0d6efdf44bb24959dd632705b24ecc19f1c653b765b567016cdb4f969b25c796e6acd7686e87c820f51ac15c7137a539e4f3a1435f5191a47a77f02a7ea7b6244bdef86ede96a2f5be430e6b58def4e5f245728c9e243093e93b7061a1b37b93f4ea15a674b4d00583fc9ede1fe97eac2e8cdc40c9bba03c0017c00809c05ea7b9ddc919a405102809fec39aa68a85ca6bfe8fe525ab5724a695d0bc3a1b9a8ba45e95cfb8ccdb7f2e94ed1a212bde2920a0d780c2ea00451d594b250b2bd54611c09d4a3631ca3ba688e5d20b582d3226855b3d9f5eae53d8b5bb320c1d25a7f8ee672e0fe281545a71c5366b8f3d3417a64a4448f00ef466933973c48a010f5fdeccdc62a69ec196d89d89760fb34aea2cc3269e8538c53ae39d3af04266636ea8e1ab18a3d2bd616b1178084b36b252e734c65098b578f6dcb96ea833d3d08e8683802dbd27e9d61afa3b58e94a85954e492c55dd743d6e528afbbf9718fc670ac80f5afd6895d06a4a06f53f55bae814438216cc61be4af733c08a2849576a9b1e7c268604ee6f45ad1367cd4b4c11f49555f94e88c78ec4df3cdccab50214039356369eac5a53c1414a7977bf83a758822b9bb432efaaa8a3a6669750ddac3138158ada2326e33e7b4e26a9d238a269557708bde383d53ef628fdac204f65e5dfc695f4a845bd86e9f317ac39ed02426bbe46d6d17a63049c62eda7c0ae02f3f66f4970eb843681c20ce4062d737df8187b336cc52caba5ab2415a7a915743d55f1b2afb4d4e333f79284829074d25ed0cb2efec70cd42c6971facae3277077e8d94f4e539f10971184037a019d27bcc0a7c5c17659fcb77b042cb0d60e94a557237edd556dd11d0bc3671bf11458b8e315027f310b2ffde5e7a3401c29dda089881c7de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_191 : rowClaim false 191 23 11037 :=
  checked _ _ _ _ 65 0xfe44c9e6bcc2e7fcbdc9c6a3bf079cb26766379ac077580eea2979a9d408bb92dbeeb33c497726461554eff92a38713c680a1a76b8f79a85095ad44312901a3b828f11173524b70314a0b8ff48df3c545f0d1498c00cc41c727ccc9a61d3d1fc58a2d44e753889b0ccdb4ddb9e4a24d86ab23121df9e13d1f8ac06ce89da3100b5bca86490eeda0b88961a5ad8b946d0204327ea9aaa99a9c823a3e080a5b4663b01af49d7faf2ba6354b37993541744ab41f7f00958df48956ec16d899f765b90b048f3bc4a5d6e98edbf64c5898b638828605480d35995aa3728c6c3f548c4f75d2c8ed33831e2f450a10d62db937c851fa4068834afad1f52456297507157ad763f58063bd6c06483cd0eeae2f557777ee4061a7ee7a924069d8fc865b0227b05cc7abfcc86495cc4d6970b964827c668788def4b00d26686680144c43a800a40423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_193 : rowClaim false 193 23 10922 :=
  checked _ _ _ _ 143 0x1e55e338caa8c33ba4bbdf889b3d122f59af2e840e19d5ea04e306854e4d27e140af260fb76ebda2eaff13ca3e86c99d2e5c43928a725939da08e585f321801d3b10283fef08dcc9a2e21c2376eebfc13213bfcbeef3b902bed345c538202b7779ef50eda2ad43290a152f6f341597828fd22ba94babed5b4920f014c18c5d81a144f43527274f77aadf7ba0fbb87d48de2e32f6652c0e05f37f1fe6318ef8ed060726a2eea695023a643a939555951a52c7b8cd38e614cda0451a54fd6e420dbe9aacf22579f2b4f5071a4bb1af9ab3e3abcaed464edcbb94817cdbe989fec7759c4f3c8969b55eafcfa52416e8a5a21857cc9afe4606166ced51491a0ca6f8fdaf38488508040dcb4229a2e25a3d58324934f0045126766e76815a9c36e90bde589ef208b00a37b26656217d1dfe2ae85bcbaa25c3b92e720c694468fee6b02a300743f2552416d1b77b1347670236e2ab999e9d65c229dda6d9e78cca2c25a056fa4d3232acb10ec0e757483acdd10d1053e178fa28fc26d5f337460c7ac648e948028c325ccbf7e66a4276b92910b7d803ce2536ad332d32d1c58bb61527b0fdf551377e05a7f6b073b8999b0a50a17a402992218ef35f8b9989377f12f0a278e09be96a6abc41697d084ed7625ace0f033d02736d4c4b5ac7770986a493c69214549ff8361a1717df8dd52f2065fb05dda5c14cc34d518f37d12f93207bf1b8f6d4c92644350d1ebecd0c6829391b11df55334ba896a8bdc6c518d6576335ffc47fa7587df46998a318c82f6d6b419f2a00539c2b6b673443efcd11a725d1ec8f84af2153b1a7c55ee068cfa2172d77d2ef42b4269247609a2522c5257f205296ade91cd21a6c4d04257b4d14253040cd5aae44ffc402751ae0545a7eaf71a9b00474e3ea6d2c40a6fd2029776e313600c24b18dc1e6c704e95211bfc5398ae1e4a88e4486d5eef1a4d046bb947350595ba1ae300ee60c1d5fdd4d7c71db5c54d9926b8dd54142948afd6059983617ce4daeb243e65572fdee6a530c4c9f282fa1fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_197 : rowClaim false 197 23 10699 :=
  checked _ _ _ _ 114 0x10fe45bd5faca0e270486b9fb232d6673af54d95d4361373cbae872d78a77e07274ef1570661f808a1cb1ebca41db3b731c9688cfb234add7bb038471e352ab39112c25015c81afc920ffa203298a818cea09c84e1a199d294141bf1414848ecfd6d89e69d35b5d6891e62daccc53829b46aacf4194d97c1073c8ff785b079b0e74117c4d63802b002096641d8d93a37e5e5ab434a063dcebfd050aadb14227e271aa8d162b7824d86522d593a33b335a5e2d7e121be254ca615b085652cc6c5ed94fd67523853fbd54c05d35b3432f4edfc64cb8e02d0ba2acc970b99c407e7d528199a5e818ac0b3b37d400d4a7a3686b9a3ee0d4f57d9aacc7f46b624f06185b341ffeda6227e89109c6cfe133264938e74aa73bfeeec3d65a17dfb87e4f8a5cc71110eaf342caa57c7bad73d1ab582db4a2ce8e2d1946943d50c4375f49e52f96f38c7a6653cbba178ca94f57d7c1eae39f1a73057d3da74cd985cdd6d73b22bead865cef7c1c3e6f03a05ad03deaee9cab6efb7533cce6293bae8e7ba625483aa798f0577ec04757098845cf3625d6a59cfd790201b8af975634d9c5185b4991826ef728b180aff42ee6e9c8b664cb51b8833fcf9b9faa4413682dbda0e0fd7377c5545d216db4c161203f7553ecaa4bd5ee514ea6ddc7940257a42c6d681ba6b39bf3cd4e4073c13808f84c3173d4b7b4334d87b53c851474c456c46cad095d48a55cb1cd5603e42229bc4785736115bb5533741d379a2db87494f72d0d5d550b88df7992a495c8bfc4ca2fedb365e18cb761bd5e43e6cf557e884d309c9807c2404758d90e74e227036005003009c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_199 : rowClaim false 199 23 10591 :=
  checked _ _ _ _ 45 0x25c0e58e73a1b5232a9ee9bf75cce3baa9397ea11f34a3a5beecfd701326910bf0446b06287c2f47cbf6bbdae57c47e0d1067f3b91d8708f98fe0d76e2fe730458dc0c7acab87f653f777856d43b84b8e9a1bbbcb964f695a6eaed7e5f397d74b9e3d7d2f590080f065967815af944ce34c6f8bfd689bc2c7281bedb29303937ee23db7976edbee6186ed9ce775dbaeaa08a3d56f9d0b3bd05a0ed80a4f44ac09838c222b6af3c445919778e2849f240d47f7b3e77313a4376ef5ab41efcd2c690c9b69d77ab4ad97624e1b8f0a954d11967e810812cc1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_211 : rowClaim false 211 23 9986 :=
  checked _ _ _ _ 140 0x237189df4091d06c1764092a700cc0809a049d2b45ec0cbdf5c283ca8425c3f0461faf8eebf7cd0f104877f5ecdcc4d93a82fc302982993debf7ec20bae00ebc80f31d771ab688ec15ad982d3f3201db1b3b5d04f962901d5f1777138371cc5ea22f29756597551693d48a9d38ba475f6bb0b69520302a00ace60dd9bd851849ebad2a4acc57acd97473675f551db9931ae403713f404ffbc3c43d40f2c25336c2675602039d6d94d834a3c2c670a67e82ee6c02fdeae90e2dc964c1f0e41b8c0de254105ce2957e9aa18cf9067d793ac2ba0d414a47635fbad1a9de8901ebd3f2981ff85cd112f9d596aaedba336df69f0b06745a6518ea17dfe43659d41e2e405217dc7bdbc2f55579620abc2afe96102abdf175135289d9fb41cf5ecb3ef0e4d29173a53dd5b5d52ef98ee525073c00208f4efe5f43c8bcacfac0146649f313433d041a8a64ec2c3aa27562414de1a263fc64222406077806b3b9806cbaf0d85784bbddbd61031a3766ed4118f0931e9e7e33f667db2c032cfa983ffa64f06051a296ec0f222ad91ed7c5a8f3a761ed940a12a7b986caa26c0615273795367cbed02489a34bc313162c79ebbbebe4aaea46f4337f3aec1093059f8b4c0646c9fd24e68522574a136a0409e1c9bb57ba501330f57bc7af2889284a09e07cad3823fc2b59c86176e2be41d2a3a11375bdd1249e2626eb5bb17edbf51a0c3aa6ce6d4434a70e4f106ea4a95c32c58346705f8874a8d67329528d462c443145db7506bb529f38a7250f16bea6887c6088b9f372caccd1273f82e2357f34e4f1bee25960914f0d7262713b14915569d66c023af5a23419c154bef5d209171e32d3d990e163fe6d8a8870205c4242a5e1e18a29989b0afa892a15833cfe9e87c1c99d1bcfc3cb1479746d128910c5dc1ecc90c50b57be4eed00640939c2e4dce470a999d4247cf68b63a29298bac287750d20e970b419ddeb474f97d53adfa8d0478e8280ebe3e59dc700b0b139f44ef86220f0a8d81e9117a22d19e944bef6c102e2 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_223 : rowClaim false 223 23 9446 :=
  checked _ _ _ _ 44 0xb6e6eb20266c19510076bc4def97667310ab5f8f5c1e1ca707347dcc97a4b6f0266ef9114dac03d93604fe0cd9836a2b9fcb613c9a68778d4c5082a21d2d7edbf51c22332749eea6e0ae40899ffc6c5e4126773344ccfb978be499d2febe68908e5a280f300c4701ac7665033a0014487b735c0ea649fe783ad74f5ab90b3737f2a86b9db30e97ebdfc3c77f2b033372d7a7f8f8d23dc4f700ecf73287f6131bb4bc89b1022ce74ddf8ede5838b78fa9492dcd6881defc127853c5a878ee10acbcc624429c3e575c0be4d99a801509c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_227 : rowClaim false 227 23 9279 :=
  checked _ _ _ _ 37 0x21d8c4baea3f671114fb91512b32bde3b037403ef210b7447454d69152f5f50cd43710ae795e902fabb3567f705a0aca50efea923345871ed1bc91e4cf1d104d8c3ebf1de89e1d221512c86744b8dca9b002906c4da68183c991bc0838463abf67d1cacc95f8cd4b1ee02318514603c1a57f461f049d9cff608b954047fd189730b462103bb5302a65a1251499b21aa260c422604425e035a25a2ed146d135b25f8e7624526a19055789853f2ceee81602282300360a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_229 : rowClaim false 229 23 9198 :=
  checked _ _ _ _ 85 0x17d1773b717a6c912c6442d1e2419cf8320e113e8a8831c50859b806658b9123d41fde86aea8c0605000e7e0956d8bb81320009e36cbe82753e40675137f137b664227387e4d7f0f9ebb1975d897685452cedc711c42f865f602a5cac7f6cd04d6ddb0cfdecc908180f28c54463bb915592c93e63f687c009f4446534cadc25995322f7693d2bf52ab80abaec6aa8a1d2ff0a67431615ffbe3447c5737f6a1bc7a5a77fec0c95a5778b1fa14a2324e5e9d471cd48256ec1d4212207fdda24ee9e412812ca703d5c2618fe2346ae811c1b2385c65ca45ee1db49162d4cd7065e7648cefff727bbfb59ae28f5779620aad3ccb3054ca22ecc1988681f04ac4dc7f71372bedf653a352ff2d6aef15c0b1e853083ec827d80099fde10a998912bb52cac9d73bae8aa9092119b2ae6d58ff5b637d6008a734936cb41fffe93a569bdd9dfcffa028f625a8263ccea44f96532771b0ddd8f6b982b0389650cb5a41330f46c7e041da0e42b97ffcd42632ccab1c37069708fdf5d42ba9036003f5a8483d05a4210d33da2d381c9511cf87ff1ffb87ab0c485de0166a3de964d90ce527466e51db086138f69ee15a0fdd4cd326887580e5caefd005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_233 : rowClaim false 233 23 9039 :=
  checked _ _ _ _ 81 0xb1312117fd5d1377018fa25c5972d2766d90c04abaa1d64df14fb43cd39f1d57514c309fcb2d8eaa08ce96a8a3527fee7f1f19ae25b833e7ddc819bfd79085182ae300add76d357cb6063582676184e4cdd0d3840855b6398b704c163595858ab631747ed012cc9f3a638938c4471da7864cc0bf86501c20c68f03638b25a3310731e9a4c637c7cc25d6594ea92b485a2553b16253938962d6b5d34db672bb8603776209ab907ae0fabcf5bd9c1c7c611e91b93ca8d216400b8ffd98089ec9746a9964eb2660cea94578e9c54eee1e24a5e3fa521978607f18290cb840c2e9515bdc996f3c3cf07ae9a94e111514c94d2b318e7c2601a01e4c5e3b198b61e1460460fc3bc59b02d4d4ca49238d2992bc918f65d8591544149b163eb4b86d0011f17aa854bb098f8ddf654a479a2c7ccab2293711ced645aa2a76e896bbcb249fe465a304f1cc50ef20546431e7024cc04932901923a3db29224268538bd24d72b37640e68b18509c5bc272e7687a2b3be657b582ef8d8d76e9795d5aaad8f0cf089f90a5fb1eefd84b2104c53d36b265e34e6c377090f2eaef013570a53002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_239 : rowClaim false 239 23 8811 :=
  checked _ _ _ _ 9 0xb5127b3839a42d88bb6bbcc667d7cdcfd7dc7f53511f82a464bdc8096c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_241 : rowClaim false 241 23 8738 :=
  checked _ _ _ _ 156 0x1c37bc334ce5f50a20230e73dfee86e9795eb899e6acc075d6212da97fe0a4902546810831077cdd94b92c7d9f9c1155a9edf93f78f0d1b85d8ab1f8cc4f62b20bde3e007dd23e02034f36ba5e1c4e6079255d0691573310ed6fb3f54defbf0bbb82a18357f89d727aa7dfab157fbf0671b38755d4972a61957f310b0cb6462de9d761b096739610eba6cb3fba874d442130be3bdad149c5f4e082011cf70dbf35c6c77c1faa85130b681183b7d5681a221685f71cdffe4bfb864f659b3458a44396a6701806feadc3c435b50fca70da5a1b6b0f3f73b06a71c8c3133d7347b81d0e82b8650694929419f4513c12d8e2186d9baded3d272f2c9882239c9cb83afecf66d9ca1ba5d802a37ee09758ae20b19d42313034379de536e3c8e4050a282f1c6d785f2d1973690029790a49d7f33809cc6773705d009f795a7970d783dd36432e22ff4da18f2840c9b95c15048067f58c36734b72446ccaff743c00d67443ea21bd00aad2297c1978e83f5d2f3465fe8af4b8b0cd4ed54eda3cd0098e7e98c18aa9b7dc394b53fb514759b0cfb9a4156472ef4f9a233c99abe732ff6c22f1929d1fbeff39ee6f238df1984e51ed3198f17fc898b73d204fe6d4a514fbb3a6f229431a3e05e93026dc276c654d7322dc1523e0df330bdcfd1b30225e7ecd7f6c7b065e3d2c92cc5cd8a4c030be78e7b518e8510ca15eade7931b6a6242b790c7a2b24aad21f8e1a7842d87237695fdb1d34e4feae1fc61e1dda999d9318288256b62d11bfd8455f2e22182d4a01ca24fd889ba25eef928b1a028cf914d190b3d984405b6224c220d9430592071d52484c87d8bc31ca610f11b45687a7d6ea6600093f19dd2c2ea9fddfce545c0cea219b0bde1a32a50f538f4ddd27bd6dc14e6ed7827b3d43c43bfc77d717f4d129509821b21f3f00db11886c2b3dfd987ffe8df30781db860949e7b42567845e7eca1d244405016f7b913a25123ff24d35790d6b1830a13529f2f94bdb39021f4eb9dc21e1da8155e1f355d08f3cc52ab1c0b112eb96b84a8e77a7f80c6295a1c3c9f8738efa62eee3730bf4b5fb9ef96a4e46baccc5aa4a6f480b38df8dfab1b7c2cfaf2a55dcb8272fd72a16139b99978079deb10a7cca85d53b738355b2207009af8de3001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_251 : rowClaim false 251 23 8388 :=
  checked _ _ _ _ 35 0x1601b3429c55e5346cbc68fe633ef8cbacf9e2fd5377830a02aa8588bd818b1f3625c9f2db81c8fa9b0dd1d4871944cb160b059d4f75b3e0f8e0478a414211a43eea5f19ebda1d2efcd4b1e9007006d57dfef7a75617197e0471394ec7695f25bb051b7b83c152a018b9bc72dc42a86c6c86858ac0157988958b61e421952a42648dd3fd23699b027b2ed897567289bea42a02d919bba9d892a385a7bd1115f9500004ed327a700900a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_257 : rowClaim false 257 23 8192 :=
  checked _ _ _ _ 114 0x165721af100916d378b8efc3515f8f750e42ed0b5094d2c46d73ff2072a0bb7d5edf155d786ef3253249a2b45eb2dde059287d4addc79dfbf276f821e21b6121f4cb35347925be270a17fc0431d2ffda7cf2bc28a2d3cd884ba7ec9aceaf641276cddf830e58eee0f5e28c93c639e294930a7305472b9b0f31b0fb8acd5fdd7b94e34404716f35a3f4275f4e069ef5bccdf6cd89d2d753ec9303925b13ca69accc990643b5539de3734913b8029fab37bee36a87aa6124204c93f60223ac4a3833d4b58b024258db50ef57b760411dfc3520626cd46a1f715b6190fc52eda2d02de04eaf572830a2b090671be82803949727396c7f99036330bb52e1bf385e0f7dfb454d35b166c02a9330b17fbf8caec64f8d69439e5de89920090d371ae803d530c0826d325ce632314b172c835cb16c6b6cd200f82c864187971ee8a89e4e69b4bb1f00986c3e7b9e5d859af568c7217bc481f66eaacb8a4e344fe8da6d91c5b89fce612246e47dba9b5ed6f7b923692bf4a8f4b0d777bdea98b9b5965027c0203c59a337a7992d8938781a94e027d0ed8c409113eb32540a4a912923ea364830bdbfa8d0eaf47a87ab6d05256ce37ce2374bc7d401e0fe42d8613ad6793db7ed6aa44f4a595499da708f2315cc2af86d326c51bd9e65d03cf842e5cd5f68190f58e70021172624dc65ec2afc39781c5b66c3533b59a468ef98332745e7a7f8c53dad3f3c2669b26bcf4df8216f21dd8bbcfdf96ed52e65ee5546941a45d47127c4a02bbb9b9b3d8c6e9d3e13d420008fd3b1894c51987f5ad0466a3ec693a60e237d45f0b0709ca0c3003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_263 : rowClaim false 263 23 8004 :=
  checked _ _ _ _ 27 0x244a0824db56a219ce67f95c7df30f366d08501d056152beac2664ba54a11860ab25cc84a767a52ed4c898cab03f04ec9e0ed1aeae1523c7fec08b3dcd7087460f57fe1b5cb8211d0f9026b791f4bd76188b4c27015dd5af566f318bdbdc7fa5cd38fcc482abb714040b2097dee2e59328e5747757bb9e0ced15d2a0258370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_269 : rowClaim false 269 23 7825 :=
  checked _ _ _ _ 31 0x426e254608c560218c69b8ec5e677e226503c4e34c26f528f738df3921bfacba80d9e29fcb88550d6b5fcea7a8db7e78e63ffcaf1b340c4e809b1c3abc0e78e50b93e51713befbc5dd727aa8192ab20c15bf08ae6e597c148830ff586a8a5349574b7395b4661153606f3eb4e14ff3719f716fb7fc888566e90883b1b101ce1e1156e0cc37e35c29cb7287a67bbe82cdc314a2d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_271 : rowClaim false 271 23 7767 :=
  checked _ _ _ _ 74 0x528cb28d83e84bf0ba992af85ff2dd2c52ad6512a153d6fd7dc7a26567ed4447771268b2b68b20cec096c9aef2fad7e056735e089d24480e1e40d4f84cf3dcdd4df1b6c1d17ec60039b7e08841782b4c4f7235a0e5b902844a2e6f9f3019e3d2729521f3af655ec9b5e3498ce9ab3cec7a21dcae5e9c895ab763c1e8e353554ff43ec9a6acd1e5572e463229ea3cab3d6e9734705711fe4b75ffcb5d1664706b6e9251c8b1fb6ea95735ec32af6f686ca36a4dca7b76841da778b855f0965e155f3781177ded14c95fdf9df80a629d3d9481d4d4ebfbe7df0ac1dcd8972883dd708e3aab54ddc73ca01323386ca64eef49259e84ad9d7f7f8a44290340b5599d9c2aa49272a696d01cdcf69a42412bdd70c95f6e8b902ccf10f8ea07c40161237eee41a45ed568bf4a9cceae54e5e85633e84d123a9075afd10619baad19c132f5c176d200d0fb7578fd394f115e2702e059722e70b010807f3fe42bf0d9435260ff39434100783d83d800c09c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_277 : rowClaim false 277 23 7598 :=
  checked _ _ _ _ 158 0x293092c422a0078a7e4447310e1f15bfe6bec04af00611b94454849cdc1af0d5e17276095c1d74b00d871d9e9fc114a7a84aca228bf4b25ae23ca1c956591ddcfb94fd277fe171c4cd6fccde10ea7a88fd603b709a7c2b772ac9e28ae778630d570fe2af7fe0511c75fb7593f47cad6cf491c17edbb5f90c449ad119c78f11aed25aaa325029e3cea9ea3730d664d2d840b1d1998e4a8a84e2926bc32a0dbbd72953503771a557861c3d7f3c765ff64163e33d650553bacc0b2c21ae8882fbda774177e62ce11ae9b09ca7f5e72d03120f1929864bb9bd6733214d156a6a044a7251c6107add03e89b0fb4a78ef71a727e867f7b5291fa493d6d960d6e802b6307c974c73fdf73e433ce69f9b98fe29a4c2258175d020facf26c62235a9cb3bc48220949b5747580be960f0b51c1ec79d91f35d5930ce895a6f8bb213dec3ff940e78ad362e3615b35c260556cf3d2a09125e83ea58f3851131da9c40a961175a59fd81b1b75c28a5d64b505e95dc3e4a350916deeb515d1b76478e5359528f4585c77aab2bb59d7484082c0a39ab43a8c01f23e7065a6cd78b4e8e5ed4724c143b7020d68479e4d30f80d2f7095896d69eef8e4b662332f6a8556b7e46ae0891512f123eadcea15cd81eda1557609a8d79f00513c76c0ccf19355cce52bfa524228a2acb174091d67403eee5eb5ff31da0a448e54c0182c8145145f79337cc260708f0e0432bd04756b9b5ad4effb9b5d8ade20a5dcd41cc9488de12e91ba61bd742902982bb2d8fbe24beff4e5bb14c9f7bf8f3ac358b51567a9a4908255c183074080c26234118644ad4bec348d12044536ec3adac5e9cbd2e6c08715f27eb9015eca89863053d2fae91b87aa3a66b1e8feaa52f07b435404eddb34e2a9730d8ae03b6652da17be0540de5bc318ec80ebdc2ff490083de14615e185e35eda346da4c9994b6523a76f623feee0b48e2b501f5f705ab7abc60f284db3b171b80e95ee7aa3719b693b5ac861dbd5885e49924a918ba5983a7cb2cc349159983e10ddb361e8e5c37da20a14f1c47e12c7babc9773833855406db4c733fe22a9712796c1683d89f876ec73edcc61ea5ae7664294a9e38ad4f090063117040142b7ff2ce7043c1ca0d2b9b1bea7c2be1708681c594bc3b2009bd014a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_281 : rowClaim false 281 23 7489 :=
  checked _ _ _ _ 176 0x32a572d614a9af9ccba8d248bb69a8a08957b3b039e3bb622f2281b28811b907460b59c4c6423a387327ab444cf08d68c2e2198287f988f27a006bd5f9f2a072925dafb9c43465700a845f73bdd953d95c72dc4caba6c73d563cbeb8931a8a3d82cedbc6c8eb826482406ad2e840cb9aa519aaddb9dbdaf64bd361cc1b84aa9dac4c11a265f9a6a6f2b9dcb7361e43cff881a2754fdde18258c6bec563838b4374b0fc008a7d1a03c846a96cce91ae28f25a5494d263fd2ed04d07e807e91d85d5396e54c4a7179043716d8445b5cb87ed78b362e518bf7b128a55c8b76054b794f7e7c9b147fdcc61ddbb4f1d592d834297ed5892ea29337a157abd533d7578cb06f86d7a8cbf2e152b8bea2dbb5f216324aa3207bdaa9d5f777e6c9e131852c8596f6f60d0895a52bcd2e0241ad2b85e8e204b0b7ab7dcf5627c3cecd792d4ed5085c28c9ff2bc8c9d9257a8fef8e67cfe51fb8f9b4b0a098ff8064c7e9b47a232f4254feac5138078f0de27939a9321c34eb81ec20f82c169e5e75e5ed9c12e8a9fdd608f1b6bf945bb6e93b0d3835eba6db63463b3d927dec01a9781a886d2a1f9b3f9e8054172d8ad0e90e325fd278b1e07b52224f01d1c907df1fc9fa657a140b3dc25d88a5714aa3153023fe8556c8411d76a0cfd12e297b89a7931700551d5943d24d4b1a4a5481b0e9648864471adebe3c18f95a998e6eded8635f303fa73360b139689530aac7d0ef5927037acbc154896b9c2726d94ebed9f99c656f1bc9557f6eb301a1b9d19db2f0ccf139dc2e53812117a39a08ec462cf299638085423028297447a50be170a240db370aeb3446d1d5dfc7f102f5b741225b479baa22e9204b79a2e58d9e515d190ed80ca079d570482775e11e99fdecdd7e17ecc4e4ddec54890d18d845d928393014d918fc1989215838121e80e1755ac3ff97f3a62f3757ddfcf197535f5ee4af3497ba7d121caa19806d8bad04af49cad6244a7b4594fbaef8bf50e74d6abd2fca5f9624e813baeab25d738993b12bd1c5f995ac9d3ee25c13f14ef297191e7c4915f5dbdbdbc94df1e481034ed9946b4a70a0528b7194e2e5297d32da448a9929f11a65385c4895a9e8f053b4b8efc25b18809a290e44d3fd6d11dc421b769d24176746f5e85e5f1559872a985819a8f7aa9eceb00913eb5de15c979ead0b4e8c864fb20157a75a556a15c7e963e92e57fd18cd0c370bae24756ed2ad007f349b2537543ef517941a609be59f1cc9fc899a99e3058b87990cca6029deb6553acf9874a81773cfbffb7c3970475c9b23003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_283 : rowClaim false 283 23 7436 :=
  checked _ _ _ _ 30 0x308ab0119d0eadd34d6a0d9a2fb0135ac8305fe003331785c7cc94958cccfa2b1eb90ae8d025a275f74901c62e2de5ccf3041fd46484ae4b2c1242152b50999540a528fa276ad5add6ab5a12c401785ba76fcd2d96bff9f069eb2daa9faaf2abcc1168a6c800fbe6a21af1ae3875bb2373de33fc38dcfcea818d35ae7bc8b407f051ef8dd235c80a50f7782a37bdea805a60d5b0012 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_293 : rowClaim false 293 23 7182 :=
  checked _ _ _ _ 46 0xcd2244d72c6b90852b2a5f2da0649840915d05ad5ff7a94aaae7a300afaf781ee511060864cd3eac7f68d1a6de3a574ddde7d9c2386d10a7880008b026783ce2f888968b76ba762ac7e4ffee9bbb16591569ac1b901906e3059b46d36fd31b53f4b36c67f5e70bc3acab22791509a886231f33fd284df9661a7d9d38c0c780c9ac4563b93e881c114ea14e880067047a2ef8351dfd905a37c0518946f8b56a52306a7716ae8956328e287beb446f480b66a30a2d9a5f4a2e4b45f13f727261a27b5ede2c33deb73847c2e12f6a1be2c829e164508ca6a08dd23433581274072f802ade663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_307 : rowClaim false 307 23 6853 :=
  checked _ _ _ _ 43 0x479f687047d9b0b42b2f9be8d042370bc69a01097861404213246c8f647f2e983eab3d25cc062b65a380302abbaa4999ca4eae56ded972da11697f37872e1a25fe7e029c546ee6003c05bd390ba5f49c7b25bb646f6bbd57e527459073919706a8a2e51b3fc2240170e29adf185ed3753607ab28a33141765d313535464ba6a286a48e994c8105a6844c6f918ceadfed8717c4c3b4b6a9223fd53a25edd774aa3a358656863e8f29c9f30b9e4ec0118080a2118a83bc08c257aa09e71cd58e91d1ed9690345a9d925dca9db9c1aad9103804dde663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_311 : rowClaim false 311 23 6765 :=
  checked _ _ _ _ 24 0x59b63e1b92938670909837fb1da72e72859607f06f481fa6f5ab36624cea4de21d325f95d23ad047a86f44bdd7821129698a2bbf92017e404417efe518f8d4db9d6a94a95076ab33762f31c1482557078a3f1411cdd9001623a046574e4254fbf53e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_313 : rowClaim false 313 23 6721 :=
  checked _ _ _ _ 117 0x1e34f57bb6d920d5524540adc8a6cca781abd27cbc2f8ec56e2bd3cf09944a90cf55dd558d3352d9441f2fb3a1b2677b689ba861250f702e5ce6f85613034c777c0f3da1295e17b5f7e4d53a3269b14e8df69ef32e26e4843f6549aedfc225ad49f7981b1bd8abf215b20060ab727b94f259c74545721412c363198462324c8fb420a47bbd16fa8070310775079ec8faaa724f9b1ee747661e0387e0210de97c9e17911bef268af62f957fdb480f868a0535b1dc2e18558a349470dbd85437078d056c86035408d2ff16c0fed98682016b85c5557e60fab96e195d513edfeda9ff3906560230ec150ae677fc4e6631492f60c7bfbaf67b9dcf4692307a2a53c4c556f4da97891684c5f8cf3963be375b58740a93fd162a43e8442bd47da6cf90862f3ef54acb71ee563e575818208efb31a1cdc589dc97db6ffd8c061e867fe7689f9cc9e46a1091db943e672f8c09bd3c52c64e2fa29192d6af927ef39e1daf661773a0f7a3a248851cee9cc5a623af59319561abb05888f074fa61b95971220bf2a6157e3e5cebb401ee7ab22198d8eba8d44d7c3739f85ab114b7cb5dbb27593526d013b7e58417ff3e81ca393b4b4d7eed700a8e29011de3c12055d69c41f4926a1d409042c9c5a30ec30857f2e8ac025e4582c043dcf2398024422206e57d5d20d9bafaa0d7e86d0202e702403daa9250dddeb0c6565bdcd77a04d6f63361a113e6376f5a0b8f65839fcea447129aec85709fcc409f2e9c10a821c11667f346414759e616401aee5964a3ee25614e4d8d4b77361babb64adc4cbb9f6fa09385cbb125da8f857b31b5a4305d6c242cab9a8c87f085fe5032d2f5b9c0242467c70030 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_317 : rowClaim false 317 23 6636 :=
  checked _ _ _ _ 107 0x6ceda81849bc4bb5535696709da13d7cac96469622f2074f3e0cf141d909138e0e8878d8b86b0ffd05490134908c2c7d1bbe52f3925e904bd49271b0bc33efc5293a763bde89969fbab9a0b9a216e095abd555b58b4e7e9401ac6e6d17ac83be747ec69d3e743ca80ae767c2f3cc07bf74c056985ebd8f7a0f3393752fed4e87c46627d98b248436dcaf7336d50261414d3162fc6d198458fc27f2980d897b5e1d0e37fb15e62759ac55e11dbc773108f11291c4c25f40fce26167d98da81972732472fa078e60f571c88b2c8623a734911c8fbccdda599ba6261b823ac3defaab199d08f2383e3ff2db5ae0b541a1a242c87cfc155ff14452075dc3e23367a75795b6f74f9218d71458f37a7dd0d177d95cc805c067713872b669faa095cdd54d91cabc843dc30e9a0453c133c63064b13de00992ded112081afe7b632e3cfc94df1c35a095eb6fe026f0c846cf27d3470f7144eadd659b6739eeded5f506984d7aedeecf75e8d0a6e38269ce496a8c1ac58b93300df4822a4ea110cb7f844ca83bbb58702eaccd42927a05cdf4a18df435f1ba2f6025164c0c8a2de8967981810eb86269313ea282f4961d6b475c984b5b21e1aff1746e9992e5dc8814c8bfb900308f4c27eb4fa0234483d342da9107491629ed1d3c45aa1dd5fef79c5640dcf2af72243fbd2adedd2328e12403a6e67c6e62d1642b402fea6665745c203e65aba2e1b5a61b5bcd5000a29292cdf52d35378959dcc32c9d0d0cf10397dfd57bd1e1e15afb0134 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_331 : rowClaim false 331 23 6355 :=
  checked _ _ _ _ 104 0x30fd55875e3c2ff046d21aef9aa1c083c880c781fda44f040d466fddb737feeb4bd1d6100d6ab5d476a7aa2d4f2bb3e0cf46527b793ffe4e67b85f2ade02ff81199f06d658b8fedf9b96209c7cbe1607768b5b888616c4dbfc26c6ad1b216c6e4b53eea968c82eaa15485a2f40fca06e0e1f98c1f92ec703ac5161346717256716aec30e5b29d24120e01acf391aa3a5ceca36a7558af892be30527eb6cb734e205dba451bed24fe3dea7f67e2e9465f6d51d9158b45b3c18a150a1c3e2abd036afd5d556b508fb40e6e3038371bd4a4d8c493721579af5ec0fcd64a219365ec926c51c3bdabd3aba419d84a172f00e5fa34056d1bebd2458b4fc08d07437f589b5a1f715a3ec9260c048cc30f0d8fc52df8ba78a77d24acf0aeba27ec4f9f21bf0051fd5873894ecafd461d57e47cea886375ad15a3f8e026bcde7eaf39ae341f10c33fd40f6d969cf7880bdcc8b4e6055c00aba46b38be9d2ec751a247f7be8f5df94d1ce3f448d1a5297ec8b0ab5667c6f151ff4abadae7290033e5ade49bcbb3c22fdc0243784bfc8374cf65ed7b26176823270661c747d4950766b483c74532a6cf8ed7cb14786be27b4a52d0561f55e467622f0f33481a3f02f86eaffd1eea247b1f81ecf6209c3d5d1eedc4507810e5700264dd0b33dcaa191310d422f76e7d1fc55414881efe5d736f0daa5bec41748241afd75aac1f97ad340d6c5d117cdccbb8e55073c7f4548a4de0576dd248a8a7b56381a11fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_337 : rowClaim false 337 23 6241 :=
  checked _ _ _ _ 208 0xa97cb89ea83091e38a4135def1a60200e4545b5c8c93173da6125e83e89d5cebbebf93db5917b346f44be069de3e59ddf07459f2947c420830f1aedd30fa6e812e5dcd3f266f129e5f8f0a2ffd36890677b8eab4dbe5a2214c8504a25b2991c0b000823c91efe2d1007fc4645c3d51bcb82430875e4e0fccb1714a4eee2a338f0c1c8b99aef4e3275388383244d037c602a46d599fa3b065a77e8130d082d31276cae8d83e9dcfe41df3a7a82fcc908f25b6588ebfccc58eed3a8f7eff5fd8e92f07886eea4740c472f4505716765b1fbf8640b707ac5733ca400116b362cc87898ad543acc764c56b317ff9431abcff181aac73c9eb276d6610066e23ab8dc038a5540d7fb7b594992365e8c7f843544109be5357bfc5d502aaabc7f75d308ecc3af7a61da235ec7a814a2aa86e55719c1ec34d8ad592e286abf3d67457b09f2ef3f48a1faaa75f03197c6c666ae83dc81ad79226b021cfa2b70c958e62fb9eb1bf1123b8741bfadc230dd92825272ac39c5a35588c4aecd500b1348e10d8519a008b68bf0221634aa710fba3c2cd04336ae5b2ef37b55cdce6f4151cae8425c6a3ef091544d65fddaee9559638524f7bf14921ef5566a0200c1bdbda8b181157bd1be1412025801e840061a241ca84c8ce5a0098e3ed6209c2ec651d36694ba8be589081b1469b4b5a901417d4def6c3e5e474acdac40d419f40339c1c4b27dcde369cf135765a1ef54717a362126da5dab5c1dd014fc898040938a499b752a0eb3e471fb676d06e3b887c769fa8bbc0f5ac50f640a9ee2af2384a34b157634a43e2ecbe293235a05cc38b759f9ca50eb45504af8a0c77ce43759574046152249dd8a467a79ba033868da55ba9d545146136b006e20d9211f002fa997e47d8dac360a657ab45e3db3bee68bebc51b0f4a11e1dcf401adc1507a50931eef136463d0f0ee54fdee93ba170dc7c7c9ae990169723bb793fa1e54931faaad52794dd83a2511a83d21a9738dc84caad05274815183e9bf10ae92722a6c43353aaac5efba022b67f22d5744b7f39d95317377c53bcb61506df27a0ef74e3d56206083c5dcd2f251c2218e5d3195d2b0a719d27acf1b6930f8b0a1d5acc3f7167494b4b73fa2346ac5652828ecfac1301c4d82c01cab55ee85310ccb82c14e236548aa5a41dd1725c64813fbc85dbfdbce38d9679110e08c0ce10aada1ac6934251ed20720eaa8e7ecd2fb045076f60d5505d16891f5155101e0a402044987b4fd4aaf2a0b65b493c5f517a703f8dcbdd2ae64d3656e9786052a4cf18ecf9a75438b0842c90a5589a3e4a8035b47f0720606175e79b43c9133528d0bba25a799146a9ed4e46bfa4a7ff747ef368ffff92e285de1d1cc9f9d987a0923cab3de3533a67d7b61c7c14acf0f514bcfd22096e8c7a1b0edfab28ff3163ce8ed685b7fd0f3bd7711b894551fb365b6778f75c45388f6ca46a271c28cc080d7a85cee2c7ab36d16514420fc4ad57fd1dd166089859c60bccd4b13c4bc8bc7568e70b807bb291783f4c5b132e3ef9ead33fd8f25a24bca7f5005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_347 : rowClaim false 347 23 6061 :=
  checked _ _ _ _ 30 0x2d702c60e5b1785f6bffbeb45ebf04480ed915801fc94d18bc6b24e317903c43f20f0d9a5465ddeac4c9a0ef5612787df0389c9f3702f427693241ad3f099b0cf8c6f97301f9783ee1b0acccc7cef453136960e561a47564e2906030d9c3bc63b8bd9cd71786ee40fe23e9a1239dc1b9c9b70c10cfa10b1ad86e7143c8b9d32dd63fc4a518907a188551793102be559e300240a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_349 : rowClaim false 349 23 6026 :=
  checked _ _ _ _ 42 0x43f259dee864ddca5034a689b57f0b248f503a636cf11516d141a31de9c8e56779e5497130b5d575e5c1f3d4d1a9518b3082dcfcf07d71224a2d14e67f158cd0c917d5afb094a8f8554385eead4d7d1911282cb7174e0301da490096126962f4d0da6ddcda03076a497a76a4b3ff57cabc411a49fb1b82e0b95330cd5b03bbb1f258b0f2cbbe22ba515fdb8628619acd53ce6a332d6028038578260a04b8dfa2301b1119d7b4cf97d2b6c3ad3831099236f110bcf4b6712268ad8a360fae81475443b0000604ec73d2499e420d87ba08023de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_353 : rowClaim false 353 23 5957 :=
  checked _ _ _ _ 74 0xe5b20f869446b8023467c8b3e76820a1401151ec2b8e988d18bf7d0c63b8518763c4b8bbab48daf025d8ed1ef3941f8d75f7e947e96ee3590f083f08b96fbb8008277cbe4968f8b3f903bf15726d78e81ccfd03483c8d18d604fc163c4ff3393167d66b4e46cf9d413b12c38566e731771eb3729ac3fc3de960db256df6979d4884075aed2a0e7d7c271c7d650dfcdc9f6c5f063fa397a6e04efe67fde8eeff13b82df794ceaa5eaea90411dd30d7008c44aeda38bc9ac648db522bd6da96bdb2a573d94b5cd5367f7a116c51b381b6170813d889c0f63bd996577c26df3da9836492b227191f25baace98964a395d2e26eafe8e6fbce561b4ff2ad8994aa8af7e84754e8c411524cd54bbee1d09452a8f9292e2fad65052df891b157793d5a3ebb1a09abf61f2536440eac107d4944e12049669251ae50a6f2e90175dcedd3146a8cae6eded75e566c4f361150dd27cb790b8b40acc53260f501d52f03a6ed5c9ff4e592bffdf5215e92d8c9f7f1c58d78c7a80bde20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_359 : rowClaim false 359 23 5857 :=
  checked _ _ _ _ 26 0x4a2c48be0aeff8535994656fe6b8928d09bb87c3324ab1d82d3a465d5e5f6f31122f6993fc6d1e76365d187b973acc64d571191299adfdf329e9d7ddb19ee4decbe0fd27b6e25a67a2f2e97ba1e58d8e0684fefa2cde7fe48b0871f27ee44c2896c9dcb786ebfa1e283de5e97b4c6b328ff28177c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_367 : rowClaim false 367 23 5729 :=
  checked _ _ _ _ 42 0x351ad4115251489db4d9d847c1f1da65d18aea92ad58ecc019ff14b166984832ada9c70b375eda09af50c489de7d16d832c2e02e91343dc6db9860b01f9501a8860a56e11c729fad2579263fb5a03130136b585625454915d56e22f70d10880faddd4c588c0a9e5c4a16d23b0b103db705353d36c14f8d1aa5d2c2743c285ebccb8ea8bc0f5535b8ced9683f68ceb6ea21546fa074827b53e012ffbdcda5fbf7a0b27193922438a8e299febc7e2c80e09ac24c06b1e3f2860dd0d558f71301444c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_373 : rowClaim false 373 23 5637 :=
  checked _ _ _ _ 109 0x3be922d9403b453f0039b620f2c9bf43a69c2c0ecc4272c4a57dedebd17533c93cb98130d940267c2b0e8884ae78feefb09fd1744134c7386d6dea64dd9e4e4ee1d040aa93a7b1e32afeb5b9027cc074d9a97906a7080bd925259e8d8a0fb6e69aa955961c9aed39ee3ebee3a2aea5afd6777ff99e31e255b4213ec81af3431408f826dc5dde9e098b0903ae243c9b2e49b7c75f94bc056c96a0bcaded4c716640f8f1ee6ad46f7d3776c5d335f9ed8d9f38ba7a147003e88e2f0f10363828a0aab85ede09ee8842722a05191e69bab0fc20ebcf500c4b0653d21981f1dedc4f237754d57a187c1ae4dcecb8282ecc63b95530a662cf54de36a9550137d1e2bd9f62a1121df101e10242b57241f886477d67ef0ac34f28f733a1162bda2a5c0fc356486c4233fc4c482285924ad19553d66cef0c66c27590627a622e4f84c2bf2daa6197950bc1ef386ccb48375db9105c62bc4c59b75112978a8edf36fa4cdc689fa67ce7c50fdcacf193c553bb18182c6b11bceeaf04c060f1234c2bbb39e9a33d3cf63943dba069807b46c9fa7a7fc7686303ebbe257b39d58ca2f921bab719c5fa9858ea96d92c884158b727e488191f09b0c5295d0972bf3622923eb78aacba12b41de3008eea6c7e0b4a0f1ee3a1642531762a77693bd6d8c285b4cb3ec8e6bb27d72a1bb2f35e4131fcb94298991ef114632455438e79e45f9e65079bf7438bf4553b92618baeab868b2cf97dfa4099debc16158c7fa2c11273af03879177c154b4d065ffb15af83e2ceb8e8c7ebdc95023a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_379 : rowClaim false 379 23 5548 :=
  checked _ _ _ _ 76 0x33072078aff035b22d40e1d20b3e44cd8fc423ff834fd801287fdc21b0e61bf65aedbd152f7830f04338d1a6a508d9a0c5b4df8cf90ce14c80f32047352ad7eeb0dc670a9c176edd91dec356bdeb1d8eb14990f1f060c4c150e19856c2761899b2a8ff4ec56ac2ef72da0075b6e06ca83135780136344dc08b9090a75df116c8dc182f7d303912dbb42c05f2893fd7ee09b555d74715a6e0335be0ab9da60754d633ec72bf75ca7bafec3a6d98606ea921869031f3bd6e4ee39e13d78febc90abeee3ef19a6ed52153d66f73e0150920bbff3a41db11c6d28cd4d6113f87bf81e0674a5dbcebd2bde9d4ed971fdb3673b83a40fd50e8c9897805b39d16e99ed6c5642eed6b3458345d52efed6542911b4f81d4a24eb19031685e5851069e8f8d35fe49c8f1bcc22b204f9d24fe9accef9e056aa15d1f7c80ce94a97ae85af40b377332bb68679c2efaf4a049b285f49ffe1cb8a873a3653c167ed0f829077c8e646dd8ee14ecdf8d1fe35423c61811b3fc6da201429ad0dfc1271f4565bdf58807939489002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_383 : rowClaim false 383 23 5489 :=
  checked _ _ _ _ 15 0x10958bb9e075786f08165efb5027bd92f1b31563b6449696a00d646e76c7fb386bc3d0f8367217e20fdc2f8bf548a8fe85478a66681e194f5b009814abe003c3914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_389 : rowClaim false 389 23 5405 :=
  checked _ _ _ _ 25 0xaa6f0bc6cfec9b37178de50f699f84ce93addfb4b8c6d4dc6a180ce947cab903f78f71e3da08fc71e5ba5d3786eeeec01705350ecfbaff522af1284a22117d62602d74b87dd62639e440fe59174d1381754de2696b420d3c2d3d4d342cc6caf480f259e4001402c0bee15cdf630eb277ab945dd22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_397 : rowClaim false 397 23 5295 :=
  checked _ _ _ _ 166 0x93e238244820a33060d190e6f8e2148ddc9d82577e877920c565137192d5fce24b3e8ee8ea7eb90eda8757eb100e58c7ec704fe9661843f1ddcc6d4d1298c00badf6052bed6226ef8493547571be5851b8e64f4f5f25f6c5f707c018c47c3a24915f36d836585d5f85e851d73752126c33bc0fac47422db9dca8e436c3be35780a7b32b20b7c7dc114f545258ba0284e48bd6e65d15560d024db011e624204bebe564f0d86165318bb7a2bdd4645eb46e48f2bbf897bcdb1b365cb15c237069f3083ae4be135e294534288ee4ba4b03e2ab2001743474ed90c4d0f01dbda75cc354cdc522582a35fd66214884c2d3b7e08dabe4efae31758235a1d8d99aed821d3c2a53cdfa7e100aa08e687c2665565c02bdb1034a7469801fb7e39394886bfaca5cd9ff59466d86ed103fed2c048f5a572dfd686b74da6c54532a09a94213b0422e8cac11ea23df71ad001b5691cb5f61478f939605e171dc2ee52498af3be63d16c37c5db84b359c36167f857562e7a1556777007be09529fe84278a15697a4e0141315eb6bf54562ff50f3da4ffe7564e6893e3a9c9c996884d774c9f76f844287bf658285a1e0e0425ff737531918f0ac8b9c01005e8cf4288d716f76737eb9dc26f832279397442518254ae3ef68350d1e07769e634d480b87d97fe61fb0d5c8cfb8454062eb79e436a582b3cb05adc39985739b102a6b20814c0d116fa01cf831e84e4069692eb8e26d07c779f8873fc0f6f8cceabbe81b053217afbef830206cd7ef961d876acc241c819c279de1d013412d03a20dfd70764bf089fc456cfc83d9c1bf087f89ab0908f09b725743f984c99f0d731adb36da2a5e54d75c55711658783b11957703bad603dba4aa4359744e1e375e16b56962ec7d0bd9aa5f320666fe9c2785d9486cb6679abdd9dd9e53b62a567a0300e1cccd8262342bdd7408a1ba06320d269b0f4f5045d8fe24baaf7f074cf9be07868bc3b7e874928b29e3e2c4d9cd5d45addc29e76c2b5fe1413f6c3dafd329b7e72311984dc7fef1d558f70134623b170b6e7f3d90ab965edef6a988bb2c81f41926d93d2a90f9674b61f058dad7cb714e3cbed0164e21a005f80110c590ac8a0aa8336787344cc357e048861b4c1bf32fdff0e270ee7fbb1c5c6001ad8b22e91fc6a77abbca75166c16cb7635320b54c8421f7b3f9cb39a47a54657cf109172bc2a6b6195121071b8a0201190967f0028 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_401 : rowClaim false 401 23 5242 :=
  checked _ _ _ _ 142 0x3fa61cb75e4d29abda35abc752023438df52928ca13b8fbbca48338487a693a7595d1919c64ad30aabbdbd750ecb91a0b00f1b25618b796a90da8ee1010a152450942268aee0ce50903858206ac11625549ac56c0b8c2b0c879f97b1de29f55aed4c0071ea624d8f4068933e047bac1e7f47cbe0e9491bf8e21dfe64e1855918d0c62880fa508d213ccd037696845763e138f349a743dfe2eeb8b72563528534ba972d940f3bf66ace59a8c16f71abece6ee0ed2e1f5c30d7237edabc61986f40efdc632368adda84feea3c1b29cac843b2e072a2cd72d5a8a064686accb7848b94ac85645c63ec89c863d227dcc59e40bb3b9b3ad2764f1e505a785b141dbb68810de9456e611d74ee1aa835eaf128c949ff852075a7e5d30cfd4ca0a2373503524c644540665dd1a3aa31afb3e3a73a6ef55982a18813acd12842f0ccb35dd7510dff8d5862e8cfcab1f7f0907ea6f4897fd5eba3befeda9eb0f2589172f414d7a1019926f44b7892b74038702a910abee79753c6ad927ad4ed1edbcdf6a8c2d4ee6100e7b0c08bdbe08a5911848068101a1c555407719253a7a48970260e9db306b0f5aa850c6340b47c8844c8b3deec82627045067ce5f950d4ae794dfb9f7ca94fcef2df34a3aaf52104e8befb2d7b650c08bc6e30642658e211d9411ecd1078754d2d4dd9c78e42aaf3b5b004cd956cdd67995b83187f37e8795def6b6aa9044000f4f5e858f9b0795a80b868f3d01c68ea01ba1d76222e9c433d88524d5c6d19ed1e451c5c9a22d5760f17f29a877b97bf2e724d706a1da1a257e93e6927485de66d0a7cfdda14e76526b3e324cabea2c1ffd16a8e03c2a622169fadc02a7325f2a99ffb9e0651858256e0f8ab03743c67c31797ebbb22f6c3ebff9c95a964ff8871d778c2d0a3d1fb4b031d0bd9d8c83130b5f8ce6d61ae5d6313eafd2bc5902f223733bc32dc93c065788040f1e070c0d29c8af3c7518295228eb4b9e215f0fc859dc4edbffdb9e8d87e00e1989b42b966802ccfc5534b8750f7864e6350367c9b23003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_409 : rowClaim false 409 23 5140 :=
  checked _ _ _ _ 55 0x10302fdb658c0a8db4cf3536f79187c9d5aa4eb3c50dd62b7b94a950cc7fe2febb0242cd950a999be2789eb0809e3bdb9d444cfaa7ba1ba8e2183563505de10ea40fd48ff0c04b3d66f6cafa345dce3acb8402fa3d77079d258b3252f9e82bddabaf0b91565273b6b5f35819dea6689c098b5bf747067776cd59e324047f5060016e501d3df524029e29a188be4edc154fcf96961894fb1948ec320eb2d05a8e1a26f0f45aceab5dfa21aec3fed6a91b64d53f291489fc2bab781023ccdd2950a8620b2babd63384e86c72faa1e44398a001abb224737fe7fa3328664d47c9a45d2428e8f022ae14ba85c29b8aae210ad4f462277f0228a95e126b46fcee29a4679fc9f9374b0cdf1cfe1fc6ab9cc5dc2a3ae817802d60d5b0012 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_419 : rowClaim false 419 23 5017 :=
  checked _ _ _ _ 8 0xc65f7e2d987e0478e130d2a144fb72daae14d400a96a8467dc83e81c274565001e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_421 : rowClaim false 421 23 4993 :=
  checked _ _ _ _ 243 0x2c25f8e35d7c11947380a21a817d44c201dc8437712e8df9386f8e7ee3baddd7d04fc24387438f26dffe71dcf5869e35be1953b52d081301ee033f20c4182cc277863a2f8f93ef6ad15bbd9b368f1c7a046c74ea83bd39b9df29c2c175585c804e8406d53af1fb30037c1298214710820a2c2c157d4b7758bab591f4a646359c0fd27b6ab308370495c1c7f83958394321ed8249d726166bd2d81e115b1d6bf10e5d8fadbc7bb505ad7c02edcd3fc5e9c220deef56b0a9505484923b5ee70c7bd945bd16190f2bf72a9b52700788ce6921e0879bd876e481f1bed7dc6491cc2bbc267430147301304e5b2a99918256b241ea7feea17bd169fa07195ec43eb950ec01bd951e5bbfdda6b9e565815d2732f82fdfb58e46c72044a05825e7091f5a144fc31be3fb0ace38a142d48199ae54172a9ffd9e8a2fceed817a327ce847cdac22fb946da295a1fcaf574d67bb40a72b5fe75420821718cd1cba5c4af53eea14aaf8f59c000d7d0b4088f586040bd1fb47900d922fd0e494dcbf178dd030cc5e1a83fc06afbb4554630dca294b1b62b3b63c71e59f2c6edfa81719383fe66f83b1d0038b03b31a19f0448c12c85fc67e986532f1395c7bf54620b2801c5681528e965617afa18f6ba0f0933ce3b49028fc226f43239930f7ab988fcc0f3a2a8a4286432236ee20191b374251f263fd107686a440e5eb6f1a41589a81c07041f00bb13c15766db38824f56a57ea14d0bba6a556723bbd894efcf910e04f77af1e62879e8fee9fa8a42fca2c51b6b576195a865ad90458f92076febc988af103f206887a493c11db42c2b0c5e5687700f00d28304763ff248bc98dd182752f2306509fccc5517f5ed389456e0e4a9cb084811c20fd1b37099c40716b2ff65bdfae020dd72edfccf3af1e486e79a121b06718b2e6651a972c40b249a34e565200a66999747c803771be5bf197febaf32c7a7161002262a46d9b818bd0d0f465a19244941616124edc16a36efebdcfde39106700ff8d03c040987ba5368c311d6d9fadcf2d905f0ea67541519aa1ddb47568987de79c52ae3bbb59889edc93111a97d958e7901616978abba805f7f50ad67266947855396bc36994564219f81cd5b5d82822b9aa6cd026e04299a5291e45afdd781705193fcd032383bb04cd509ee65cafbcd2060bcfa6e4568022b33f0b32d6425ca6a24a42c67005688eeec59e2be087348f42c9c47fe08a00359963a9a0bad74bb07b3fce3235e3780a664ff29116b998dad0515f83026e5d045078d002eb564f1f25fd219383f8f9471ce6c708f329f44ced57714cf9dfa025622badd1b8c100f7309bd913ae61c11d0d7cfa6033c576a35e251a4b31ba6db42c1a6bbc267e933675c94199293ea347b74e1979741594ad5cfb14f7e11e08b873644585047825bf7b396b60f3f9e899d7370d9a5730de5e8bab48de5d2d2624857d32e0933338b4766c2f50350143e3cde7c1cb8f563b267651b2d964b99fc43a60fc3cacd8744e75724e4f1312d136bd068a2861eb27c0a4a2a422604b43469bfa64461af01e653dde6c92ba7f376f46f8913779213e7bb9a7bc3b2ac12a282c3bf296b67b8fd57fa934b3360c0a191e7cafd4158ef8c1b8d405e497680f25f9fb185768c760e4544a270ee8203b44ae8dba7bff78a2235d3b37e8ccca884c2d3b2181aa9990640427744d928cd592175ff0e1ec810c277fb9967ab5b80633ce550cdee5198afa84aa48a51dd9eb5359f01363ca85c202f9f555a8739f81affe96cdee6a2ab7c606eac9a0886d9cb28dafdc3b69a056dad3dc153e855c9d3671f0399f64047648132d4fcb62e599dce0debcfb05c4 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_431 : rowClaim false 431 23 4877 :=
  checked _ _ _ _ 37 0x6e05fb20c571a63b03d1c2f090588abafdababda63e6d7e6c835460b1a6a2b64db368d65dc8f4e4abb1321cec792dead7788893c6b44298e9accd1ca64ec0982f7d43322c610128f0b486b0be0cfa11a8882b744c6d168f95de2d13ab0f6f27f5a3511dd0c6c8f6f663287ccefbe8d09c7761bc93393208be01c149ea583b68a07d01cbc01a4b32ccf2e1d5af8e1d963aa7ec872af3b6abb28e14c4c2c2a91819835699005a6686680144c43a800a40423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_433 : rowClaim false 433 23 4854 :=
  checked _ _ _ _ 97 0x8e4d28a520e1e05e8a535483ab99b0acb1733e988c19527f816c70a66c346d7bb10d40f218146847f2e5a83f315955eb20b33919d1956ab5c1cd3643a6eb8a397bb88375525348d1640636cbae3ff6172deb5530500a745fff7a91dd990719646840fe80105343a6f24a2c712b7da756f3bf5d3a9edd7ea34673940456fb52099b866e548a550150a3a01d445a34fd53156d97e725a832f3f1968f20e7c706365adf9e44b8c585ff1acafec51c4f6a717e660037f9eadaab377c85e98d892786d55e61228922fb297e51934192b03d3e399a2dc2a391cb8dcc1b126273074f1696a4ef8b95274a4397ff87a3a814bba305aa9b99234b62240a1612aa1ab950038f071aecb148062e17c418119c6b685aac2669cef4c8bf58d332b435899ba7feb93626c012f4e438a8dcd74ac81e8b2b41949c09c1dd0ce12fcb7fcba61019062c49b1bfa01cadbc1de3e1f6f8926a2ddb8d19b91fc74f889aa0a5804c805a0dabeb027038b6d5575782af2866c2e95d364c7ab193d8087ff3b70bafdd4945ab28dad78b596e966e1fb2fbf4b98c6bc7268f1d8b726d28375ba746e00f75412abdc1051dd09d2e07afc7642644ebda1b943ee31f0bd99cd8b5742579627dc8530de02276bb58c5f973d418e28ec073ea43062bf560aa77610ca84e896ed5b44c211e3ea76fda91b17d12af7b7182038508c142a143a1e601705e663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_439 : rowClaim false 439 23 4788 :=
  checked _ _ _ _ 29 0x64fbbb96a62fa608c141f8c986c2e7ad23cc39c3bb831242e08250baa1e5dda60a7c9be3dfe3c2f5fe155c4c2b8bfd2d6a2dacb1a3bb32d1464e977b31d142d768b6c5d4d7e474d6e9b073d27a05a08e3162f12e963f77953b0baae5c3ac2bac5b070902dac96348785fb30330f0803bf58079e8500875dce5d305456af4fa28113c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_443 : rowClaim false 443 23 4744 :=
  checked _ _ _ _ 19 0x735363e7b603d6cdf6ff0753da963eb59325408b6e12963e152af8f0bca8858788eb0eb7d26da2df8e0b9bf72413fbf924cfe2e847a8dbb875f40f9bb37f98ed835bb8d77601015e9fdf0be8358189a606b85d01c252947003c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_449 : rowClaim false 449 23 4681 :=
  checked _ _ _ _ 27 0x5ec8f6ad48a6e12a9e07d8367ad54c8978ab1b16121591d34b5d792fb5bb2eb48b1bd70ecb1c0e659f751235c8d864052928123823f82e3f5acba44c5fd5f7d4d87af6e56a1565f3bdb680b4d3a31dbfbaaa5cc00cdfd985e5378aa2a44bb00a6671fbced881fce628dd2b7e7d42e8e42c294fd59f87854e38adb3a3978a9fe2d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_457 : rowClaim false 457 23 4599 :=
  checked _ _ _ _ 164 0x7328e93be1e2f042d3bc934fb1674583a80e00059368936d5df132a20582aef7add93abe6a5215e54421661d3838f7a4800a444acf867860118e2a96b62bf20a345d2d7ca168a6b78520cb6c709b41b0201b079f0756b4d7da5307efa1db5fe6dd3edef57bec14002e881e5c851c3964fe0a4e94b4d54536481a6dcfd86072bbb4de2752e9d2497e6ed1d6de70f356d602ee205411a35e5947d844c0fe3eaf3137dea464965a07b6a278aebb9977c507791c782f717d3b71b6244fa6ab21c4bac7080413f4f639d02974b44440b43deb622176bf041801575390979eb12dfe0347fb762f17890e707079a3dc2e7e8c0861abbfa91d2ea8b7adfce76306e53eaeb8aa20e9a3a846443771ae96c5d7ba078c0c0ccc9ccf4b8cf5a30be44d0501115f23d7748bce546246e6e65a573c2a9bd3a4faa84e07076f19863d67316390b2ef2cc1630677c891a3f7e4d9d4671ae93c5cd3ce464a04d024baccc262604a21cc710d9f9fb14b4d5a06d68e77309f79ddde1f5a629c2a7bd1a1b0a2aba53b386de4cce8dad802bf2f40acbc5cdc96cd80208cac8d8095369ce86baf2aa98b3a792f545285bddce6e80945c33e399a2074e4279d48b8cdb8ed82ef8440315ac2342a176d32b5f002ac01d68ee8faaf2f25df4ce47313532c2ade8acb173c8c1e6b41742c14303c20b85d976486232ba20c3c6892cd76dbb760f58ae25665d9f13bf2ed3bdf36983ef68ef8ffd64940fef26dd415a76a2a897bd608b619770d8e207fc300eab782ea3f910ca0b93e9658d4fbcace7b6a6262dc3ca69c7567159a234a1ebf3e31e01d2c709fe886ba6057cb3fe3dff64ee31846a23c898bfdcd14d2962a829f392b12e66306c6e303dd65517484c3c7b7db3f6abec32c8989bbd5c48e4f4fdc2fa4e8086178e6380f89c4106ae80edb1a2a795e1392bd7cd7df5dd10bfe0c5c549df7cd57224c6c6f9e3ab9ab78a6e37b7d38d370b7b53df16d37d236bceee5e71213efdf00e136e2895550fd83f82d4443a838a38963885f890a0f7aa04d26ab1e148fc6e0b18c408421a56410fa7890e3ea60b2feca1a47743f53f35a9ac6307da65a8de08a082b355b8fbb35e492d50bb77b8ca79a6ead01f6560e63720c15db49f5a0a0d59ce1906c55257334700c0c448d2413ba14b4be836d1e416e9795681a5b998ea206a53f790ade1e38678da00e57f3897a2187d37ff0058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_461 : rowClaim false 461 23 4559 :=
  checked _ _ _ _ 51 0x8b6bc2efc6f10f9a604551664ffdf8637b2dce7cc973a8803cb979273fbdc253261496c6d5b9a047675076cf7d83354afa9c4ef9f80c446adc7c0d39f0cd04c6429f5f0abb37c1420c03e6ce417768ea2a0d21d99b48cc13eafda71fae69f5b259712701ee802a01607c9af87699420200ac0747c8042015319a50a3c93dec3d9f9183aecd4ceb3ed2884823d13d4800f91124b81b185bae5ae87d8b348255dcafc91e4e59538a0835ace9e44194164f253e5e665edced920eb80a8f2607e3eeb373b6c82ce872be79b49550f3313e028b52c5bac939965c1c2d8a1e3f03a906ae8bf5eef6db6808b1ca6737b6d9690345a9d925dca9db9c1aad9103804dde663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_463 : rowClaim false 463 23 4539 :=
  checked _ _ _ _ 30 0x6242c201061d4f51beee16e82afde000e9ba1cd5ac891b0908209957c58914cc782d6181d686e984fe7be63813450607044e3cd33b43c59d7e85ab59c80ba3154c6fa4682c9f77ff1165b29921b77430576220c4fbf321bbb248d974617f593ff78e460f2bfdfb0246ed305b4ec07c6308c96a5a3dba95dc9413a20f9e407be3853301b04c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_467 : rowClaim false 467 23 4500 :=
  checked _ _ _ _ 40 0x9fecf5be028ea1d39f785effd10021f30ff8f91ec3ed370f5d6c7f984dcbbd5ef5f378d5048fc746d05591e27ff16ddc470a4b8d3b1ebc2ee9d6070541f022096d597f3b1a188a22bdd5a3d18571f3ca8889d50507c4278dfaab723923d1d935d89434000b4bdf1e97acd78ea109b5644ccc8a180e276f505539a6f28ce30f6c7a8dac08819300a09914a906b79fecd156ecc9b41dac2873c06c5a469b6e46ee35708415d87820732910ce11a184003d020b567b10e77c688c8feee6bcb832bcdf3d005a0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_479 : rowClaim false 479 23 4387 :=
  checked _ _ _ _ 22 0x3cbc2dcd41f257072cde24c51fbb2855a58a44d3593d5f41947176083597516514679bdfbdd5e6bc2d126847c20578a8c67615f5797c731cb32bedfe7e720d7165d15c4de13a557d2dcebfa6dadf3f71ee78e88fd04f9d5b2c87420aa68177c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_487 : rowClaim false 487 23 4315 :=
  checked _ _ _ _ 39 0x14b0a638531e19819c31609f3a1134f8dffdcdce3bf3369f245502355b11b8c55d3959d5b2c8ed9c39b202f3d40628a5edf941f0e5dbddab76d89eb9990ad5b86ea79fabd078b03c233c86677842128433b8f109b11fcea9a1ebc9c5fe7162d862664e4dfc34cb8f9345eb84ed952ac01f39b3dc6b5255dd0c5c31f7b741eead387b7bfd365d8f0b3ab4b6882eabafd65d9bc86e34dd74dd98586c5551eb8b9f8ffcdf749a1e9309da7e89bdf75fd481f2649dcfa9d5043924b9300b461ace003c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_491 : rowClaim false 491 23 4279 :=
  checked _ _ _ _ 42 0x2ab8318c980cbda7875806183cfbd35f53fd0708278ea9dba6c559a14a0e3fadd4191e08bf5149e8ac6078bd83e09773555a1f8567f0a9d4b85a73dc6d2a12b4ca254470c372365db7a5fe2e97c629361346501ab986ccc980b4a6b2f2fff69bad94bed99fed5ae09bbad1a06d84ffd264a630c0b5abb7cf9fa809c4827bb963401a72e4af16f567005be881bd4a3b3b40bba3accc237f2bb15c3fcc31ec35141d88046a89fc152b6c607c0ca7e10d37cb204964098f61aeb07ea8f63179719fc4d42951d92f0ee9907d304ec559e300240a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_499 : rowClaim false 499 23 4211 :=
  checked _ _ _ _ 44 0x465100305506e49f002e2d92e7d44790722f53c2139bf9ca077bb3bcfa22597f2beed19e79f9e7969df78c01c3b2cead7a0e9d858f29c6947a8673c877e47329f29a0ffab0df13fcf4be83c1e7c5be68219f723ffa54fedbab8b4697184c0911e7998a04b8a97b1bb118e8108f4b91ea7ccb9c3ba356f60a2f255cfd8956118ed1499675692eb5ef0df00e46d7fbea123871ec15a9c0908b35949617742674e95203b3c6b4030388c712ebf70362e3b08cd2686450a7e42fa9d96b7e9d99a9993beb2a63fdfabb17f026a8418d796f37360dd85493c172e1806a9f0d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_503 : rowClaim false 503 23 4177 :=
  checked _ _ _ _ 23 0xc6444539ec691c1003ebd0cb619da581e172c28ff9870bdb56ee2d1620a1876fe0098dc4849ba0bb425e49c9cdaaa59934f8dca02563f740dd389956e86dbdc962b53f2e69ad2f1f0b76f98ae0bebe481c3e19fc4f65cfc5e741c9a488bb6801501f2affde008c370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_509 : rowClaim false 509 23 4128 :=
  checked _ _ _ _ 17 0x5516395a7eec9d4eb9e3af5cc2296e29f2ab822ba4a933a822e62837690da8f7928317bbe1c5ad13b90e7ce7089eeea98e8e430a5673bf5cf9a8e86a6a3f1553c976cdf630eb277ab945dd22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_521 : rowClaim false 521 23 4032 :=
  checked _ _ _ _ 75 0x20912fdf68968f23811f3e4e6b096debfa84f3b99a71ccba6930b31d741114bd8aec458c6d8f7e61eb7345ade8376984bc29e0540eccafbb9c39bccf82f272f6eb768b25e348a085a7a2788a95654a18559a51e82a20c3e0e93d3a64b1038284063d8eba9488cf2c7060330f9fd6a1e3f295cdc0e3989319c604ffe7b8f46ec0dee9a1c2d3db8cda40b7a858f8adc2e7ff5a6a2b5140a61e8db1f15554f376e98f5ba7b272165c028e64af911906c12686b8b848b492293d00bff77a62952d9d12dcdc58b77e68f145db845a2c6db11c6de4792fb5bf79a501c087ba5aaaef4e535d24e1505c947476f8ad75a5c2a01a8ec475c7f2daf3dab2446dceb95e75a18db661a22a007d11f4ce5bb6fc70cbc7f7e24cebd70df7f93d0918fbdbc4824ed56de655395ec939475561c3e694d37500dcaf3d4debd4de65dda7d54567075d5681a80e52c7347fa728d1e461dd37441f219f12dbfce6b281e0f6495f08c68a9430559a454b5f0b007bef42a94e9b8af5f6ad06de09bbd65c24e2880ae20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_523 : rowClaim false 523 23 4017 :=
  checked _ _ _ _ 50 0x2d31c8b33045fc67376984ef6886d605a7edfea845dc763d3ed0395dc5191e2ac4bc2ed61e41aa7496470ffb9726946ef8b8c4bb515c7e86f952ef779dfba91ec8485af25c75f4ae027e1ddde553d997bb2fc938fb43fcae46e404246029f6321a54a07f1fd465dba5a73f9ae59cc9ae200a8e3ff1e6bf1907ab9ed5d6e5cd0197bac563e3f2eb7d80c1e02c869ca68a501bfb234b41df73374c6b403221b8970b6459a5fccc2860c9e4df51bbc34b06f5863475db9d7d939151a41f639ba3a32cdfc6366a9fd3e2dba072067556f0e7338f6bd467c8f562f9d5a20c5c420a6330826d4811fb4ac8512a9035d3dc43f974609a5ece731809630d61001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_541 : rowClaim false 541 23 3883 :=
  checked _ _ _ _ 262 0x44bfe50c7ecede9bbf6a84ea5f4d116f5f36ac359a1df3f936f9fc4412eda1eb1cc7b047d11af82eb9a4f80000a91af59c8696f43db284e661232261a661ac29859456dd16ba21e0572bb2eadc1f61ed05c1dbfb37504228a396173c07eb8c16f421a7eee8ce1011b8eb382d323c396dc12379cace0448227eb511c8eb4e076d00c7f1ce53e05ece7aa59a3ab5ca8a04f6ee2a305f37d91be2da7ebd769f420fed76870d48c94db9555e7da3c078498ac632d8418a8592a8379adc5e966a80ff8bd00d4f1e2b3787fc93e108bae74c3803327baab327919066b4c2a43da80b78587c331376e8479e1267b26154ec6c0d8643c93d94122a4b800fb7ad85f01029ba09d34ff7c6f53f7f2b187928094400f7c453465e73192f5bd156c5ad52b924799cfd5a7b885f3e6e732ce592222a6108e74cebaeca7ba669a1454bb9150967a23f3dfec729b7dc70f8079ea21eab7fdbf9122a6cd69a89993a850378eca761ebaab99191f111dd662122d339cb03223eea2df9896ce81eaed1b24546014dd94992a16f3effd0d46c0b577b7eddf7593376149254801961cc2656d26cfdc78443605837e7d15b1eb3d5d3a3fd878e2209dd7aa2362c22ac3b8cecc910a0a1cba617046d232e14c08a37657ec66b1c207775d44ef5722fb60afe0788b583987fcff804a0911252f5dfc217de76fc563df45b712b54db1ce389329eacb535d220bb4066882f88fe28a34eb2cc774b31803094f641aedeb9d8f139bced6f0a6f594e009b48666b1cab5d65f57b53e552a4afd5f6674c5b550d4ac19dfcc164bd48a093b01c1bd541c8cf213caf5404585058f4f9ebf9f3fb31f0bbf22932ee49d64ad309ce397d34fb33cbcfc2a3b6c0bb637439fa9196be4729d36f4db65a4fa04dece43b3cb942f465bf267cf57272bc7b065af56c571bd61cbd0b057454f1715dbac60fcb8c06b5da0b7e13e67a472b5b9a1d230287ec793b137a0f653045b99e5d16b93b797a66fad2ad4701a83064a1c01986b0d1d1d69bfc77b1ce11be701dc30ff6ce62923c802c5d84d6e946d1db9cbc02851ca3c62f5a4326d8d13199a8e7975fe7d683810a652f467863ac568c6bb22ff88de8d8cda9717e2790cb43039c9e96af59eb31068af9f21d2d71a2d1c69cfd98c324ea88ab976cd65fe4cd32b22aa8ac731924c0579749af31b69a5d927fdf6a406a3d69172c6c57e6aabff0ee12a6c19f57efbd47ea093403bcf7ae4698124a222d0408a911ffeff3c64f9a9d216d167de15cc3caaec7b98ee1ebfd867f4e923b4277a46f1279ea9b8329b051308b20d763f2e1d1ba24d35b56b83964ce47bdb217de4e1b73cdeae2ee7a79e1898c8bb1a5fb6f498ff69e34e9f8053fd3d5f3133f302740220913fb1788ba89f4e020bfc92a1444863f364c319b88165d4f69cb5edd12dd6beb3e1e478a799d9d5d05cae441cb5bbf870e06073fac905a75b2baabac9b6e29d563f4522e48e4de38ce19c72e9ee35b2c963edeef72566a6a25456265ba5d0989410382a0dba0453129cc5c03789c671745ab731c4eebba4f48b9037915325c4e7265161072c1d4bc31cb81826fa201f9d458079e8317170b352d446caae037ee9352cfa461137e9e71c045e310ec1d1eed49836924bae652851d8e610c2e1dde8e0215cf01edca5d1405826a356cc0a56da412e0cbd282e33c634df6a9c0bb011422168452838a1ef0d1faa7991be1f822ad70c26d980fd487e26c1a460cab2fd93d030ea9c09d900a3fabda79fe43bb59992a375db61805a977a1d2f0c3cc0334f660b93b1aa7db4aeda2a6e1a19f44fea5299aef2ccf3cb15721c245aa695985ba1ad567f1c06d1a6f8639f595d4986775973dbb910ff561580515ed2ebae0a7e06cde4b0abe991f7735e6cddae39db2470fde02fbce8b3a84421af2d461ba1005dcb26076a33a2409c4942679c86622a3cf710ee7ad7f049bcaafccb0b501388ab0570040 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_547 : rowClaim false 547 23 3840 :=
  checked _ _ _ _ 63 0x9d9bfa465feadceb56b594fafda79520e86ab61b131d2ce9f78e92dd407b8491fcbf402f118bb261c0d492ed69c217c9edc2ba355a6eb0281a4571b9b77136aceb4b5e63aed432665e000358a2f418b48194d8469602616dbdd75e1d66a7c4076b35cc0961cd2375e4eda4e6a158ad192d70f9a5e22d28b467e49ad867d01dd01238462eb283deb6a285508f43bc171bfd12514678c12ed0ce96d1f55d19d7e9e130448d2b0e10070ebb31b151f199db23b14cd1eb453b6fbd982d34b27d1b13dff17b735a979abef9ea3666393e5e5b40de4686b499d6c2855be9c0d2ffcb81aee7a074334ec52ec8f26de0a35aa652dd1206f04a645189633fde90ea07ddd2e771c9e4c041b64d20e338a54d1286046d3694e8f606806459bb913588f0f70f0c642198ce5d81728dfa2ce99843c153f01b200004e7f040a9deec8648277a07f5005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_557 : rowClaim false 557 23 3771 :=
  checked _ _ _ _ 66 0x21997f38020ccf9220919b499897c3b916052b3f0d45eb50c90e2571bf3286c7310890ac989e352783378f04fa9c4d404a30488a004eb2cb99051b857b6f86a42bef1fe059d457956b9c2e79061613bcb6f557d26b593837765ade09c1e4a8362465957dba0079d5bf63704626397a0fb0ab29a6c8f9440dbdd66c7f3365d88d977fe589172cf98cefd6467e4169a763dc5892b5788ee4f84001d365906187783b1c5e449714b61234c5dccc12e6896edb58af552b4f81b4c93ed34cb15c0b512fabb6988e04d9770451aa790cfac54bd193e653932ac0d71c5f793ca281217479aec915b2db4a2a256b8bacedd573e2ed873eb4ddaaaeb46976aff3d4335af2f7bd9f994f5217f7619215a4963d018a0acc87c1c94b2ee537be81828bd89448295c9c1223b02843a432e505fde378102dc663e49e91ae574cb911360bdb93e339cbc111b235e963b0417b9fabc700b0 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_563 : rowClaim false 563 23 3731 :=
  checked _ _ _ _ 30 0x225a7b5879e12e3a4d80aebef6cd7fe6368d2e2d6f221579d9f3b3453cde4c3f67d95bf4bac613ac2608b647189a20b609435e984b6d8f54f40e1e573d601ce0a2d4f80aceba3f7ca3e5b4682d79d081647722c11f4d7e0310a902b98de01e67039fb6e34865e52185bc36c84192fef1c696ee9e75cbda6391eee79496c396d6b6108e4486565832b73b6b010e559e300240a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_569 : rowClaim false 569 23 3692 :=
  checked _ _ _ _ 25 0x1b5225b1a984e11b96ee9dfa362cc6b061000ec98f3249110b7d8ba6eba1d447ac967447b0588923c00580d1178cd3fde14a6a86f47a38616783ecf2d0e6d111d9f0ad2b6f5789fb5a5bd9513a419c5588df375e02d163ce35ad3e03aeaff848c8ebf249e7ab364ba0372075f75aec46b02ccece81a2d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_571 : rowClaim false 571 23 3679 :=
  checked _ _ _ _ 51 0x6e8de32e5cd4fd3f204b372d8d33ba219c078ee102c9594742c13e631fb489f145877abfeee8174a233f1f233b16572f229b87a8f96e1a34aadd2c406d54f6b164768da5218c6f64c66f64f8af3252e61eef5265918723fa7bd7f9c0aa02fe78f5d9d7deee6c837ae5927cd966acf0875686cb9e08d876d950896215221466ef182dcc8461741a60e7f72fa2472f342b5b9515d47e24149ffa0211c502ed0dae843e9f6bfc29c4bcd4be56eba30e03d62c0de2514620c9cd51dedefd509a8493e5960c0b7827cbb011509a757664b21af46d83ea15a73eff9b5c156aefb91e1d286ddca8ce0cdd60ab917c95a6ff77cd9abcbc6af64b514022cc2a03a54589f00a8 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_577 : rowClaim false 577 23 3640 :=
  checked _ _ _ _ 131 0x2ec6fc9fe0dcfc4330c54d3d25285f6038c7248ef60be1eb35fd91591bf1d1d2e92491c22ddbc021aa8bb755f185f82e9a82706251d6d106c877ccd07e62c90ec7228fdfaf9ccb3590e0d2f651d7aa34acfcafc662e571590a7e4fe2017910d31281ab1ce9b91403a6292fdf8c41fcf5febd662b96ccff5a61dff484ff527e87751e0ae36de9fc77a7112f693c66c89cde7e8cd9d2c880c80c21ed4b66d61ce2e4816a12532311dc10aef01e0d0c68df951848d904b4c10cd49037d1d1de2eadb2a5f9e92ebc18c530c63249c9088866fc7d16a35860327239a1c42ee636f731a45fa3ab10e13431cd755d4eaff70d5d5e9f8880fb5bdd69a7d5f1a5d356ef647ef14a8e4456b50749706f7c1db17ddc50e9e2142d1f8772638edf2a57ecf27df408cc74e51a6cc119d522d7daa11a44d3796202317f30932de125a155983a3e33e72ec296246fd94f113fa9b5038451596b3ad9f87cacedb5acdbd615df2fc995cc354874b80f78eaacd69a1ac0a7c6635dd063cc64d71ee8526501184de8efd6cf54b42200d2bf9ffef82c1ab0ed14a819c005d3107955d66dde6a7d4970447c633327f5fae7664055db56d4f966132eee8933a96a84078ea2e5fa3d79242879ee8a811f8b874a4a042a4f915d9c19a442a0ab175e2690c0766b98011b02da5be0035864b4e7a39e63487abb2484739bc4312a0c3206934d95632d0fb5a4fc98cc18e0f152443224f66e15879c8f616f56cb3fa4a67e6296eaa6cbfe868b0bd8f0b021075962a85bdbc8e5455904c2bd2b9641894f777117544e3463a1b1be618208839242d63411d9a0d4d55a555f9a333699c97f424f642f14e98bc5aa57deae1a046ac093fa7e37f5b5eaee35223685cfb2f4fcde56db50b38e0b745e916a84527c7efc33a0520cb16e84c204cf29b4d2a31a56d8b07c6994bd9505a22285c575406056fea6c582dfe20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_587 : rowClaim false 587 23 3578 :=
  checked _ _ _ _ 29 0x108f3e194504ad679bcf9f102bb8843a0722e89e53a151930e9e882a16b1718a592d03ef37053fba28992bec7fa35fb4e98359ef83220186c12c00d8d64ecc657ddfceed97b149bf411bb2d9ee3a2d86cecd14f71d3ab87c6027de42b73bc056bc7f0ef64c02591576d7dff1c2e28afcec6d04105968158f4f6e4fc3657437eea1ba5ca1f897fcdf3d005a0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_593 : rowClaim false 593 23 3542 :=
  checked _ _ _ _ 36 0xb075d660cd684c20f29a7f93c202b105c3b2a61ed6716e2cda8e2a8f2240ebdc72112b0f26ea69a2158843d8dde3a782514aa1a68e6ef0355aec2ed69b470d32d087b6d3a102c06eb06f22a954bbaade1ddc8b80134711b2f7b9e42593daaafe17f490a0a21dcdb0c5fe8065369a4da410b5aa43dbe79ff3025c7ad80cbdbdbf0411b2e9df46cb9358e462b85d24038727390d4bd5545f352c0b3dc178126629570c954593efb25a8a011661501d6a858b0054 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_599 : rowClaim false 599 23 3506 :=
  checked _ _ _ _ 9 0x10f9bb8d44f54b21e3f20f4c667d7cdcfd7dc7f53511f82a464bdc8096c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_601 : rowClaim false 601 23 3495 :=
  checked _ _ _ _ 111 0x381084996c8cc9ebdee812388bad40ae29d0b39d19dc5ab748baa6a957dbd8d9a65c29e337a31b635f745c43b333c9e87fb773f7f323cc0eeb605b00f3140fddc79c2aff3958fe0120db567ee2298f5b38ee006e51bff027f3c2f1d61ebcae0c50bae751fe029d596f636440df22148e59f338bfde584b17be85c87fbb43f9b3bce37bef69ae16401228bc6d910fdff7f344d7add2480cc4f99830c01c8ba10d15a21f298b0ddfecaf549061c87e6d66916661f0d4419e8263daea05e3e85faeb0d2ea501f951b6d6339b87e0031444f8be873c69a3065cb18dc8901225ba843fac1cf32d4d0c2213be9f51133bd57b28d387f83df9c1ddd0ae2e4008f3976a92aaf97d1d68654119f9531cec3047cab7b09922faccb851d13a2c896e10e718053f467b9f9f54f472af4bd0bbf90e70247c894ffed243068d9112fe021cb518c1ec605d749e253681203497fb515141c1fe10c8454217351d79c005eb5d2d156b59f19999f3317e8d8c60f762456ec9853ebc0fd4cced3faad85700d1bb3564a134e5d8c236f94779dd603e2589e684d2ed6143587a22ac141ff53123596b1b0409f6c97b3c64a933599d8d7b97bee1f133ef63258e7f75149d66c5f07f85de958ad62289d49edec2f2a0cc1e82b110c5ee6f2e7de6f54a7a42bdfb35f7c9cdf29f1313b4b3ae8a639dc2a671e42c3c061dda05fa0116a4dd0b5eeea3ed3b3bd797ef546e50863519063300bf308d33d38b968b52d6833e687c1693bdb4687af98d86d9db0ab360821a50c9879d1de221a1805f69b7b5ebc9104604cc9daa05275bfd44552fa48341de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_607 : rowClaim false 607 23 3460 :=
  checked _ _ _ _ 41 0x12619dbebc38fc1ba9cdfc7fe978fa33ac8c5b4d5540b302ed3a8e0ca539463c17a9643dd8de3c83439f043f1b6b8db93b3e5be8c299561ff943c867d0d91fe085d8d185ba7c1d470d7c43deb806c3bff5a38cdeb9e8c98a19789dcb44b2c87aba9abbea20401fea1fff0adf774a0265694bc47399ab0ce97b7ceb1e1b743a2eb464bcacffd5384d081752a22b1a210d2c9f5b2630103a6c973cdb794c825ea913797e2bd5c67710af3c4d61080f73f5ae99328d6c6c8b1bed89502764c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_613 : rowClaim false 613 23 3426 :=
  checked _ _ _ _ 106 0xb2ef54a3dc04d5071d7706317d0db26eab31693bb24203799999d9690435225bdee2f5b6d56ac85dad55a0b83636a2265606d6fbcab0924f7d761365b25f37a49e957a8a99e82a480e84bdad477e19757683847a026ec7f9d59ee7aa904ca5a23a3c21058c9324397a7501fa136458119b747ab5e8d557ba4ed1f0c95e25e38fbbae319e99c64c2d621e22571d28dd173d8842bda5f7a7a3335e685d0b3dfae089b89ab13548d43129d79aa06802fcee58f6317c8db1000d52d22b93589cfc0f72769ba32a8976281f6c8f76c55c5210d18c9bb8c55c265109edf200c07c107f413f73ad7d46ddf166a738821da09e04a0376d7a36dc6d99f187413a7c81662950fc65a0fcf01faf023441f83e115354b98c8bd2334948a7f4b85e40c13a3c8b31befb46a7017999a35203cd69b3441f73db56c58c5da1e4c0115fc35fe8f9aab6ba9e289e2faa84f93485bc995b2896037fe615db1c358ad74b8bf1b58ba9b24f8b1271d0a2be1f69a9e0524d0c72f16c895d090993f09d9ffa2f6911ce86ddfa36c01d73921e0be20814ce3db132abe0981d709063473d01a7b99d83f5522c4682073bc5bee86fdc7955a321a85b06063f2e9a6db8af6904879bd315613d59fad6ff33eb1bef9cbdc87435790d2392526537bfe1ef6df14333c11ae7b3de1e1b274681303bb670e056b9d013d17ed918330a83e5dbe85904f273a070a8a816893d485fbd95931bcfa4b0cd48b86d5a61212eaa9ecbe4324fddb68dcc9a13c2b5169804ea00a5 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_617 : rowClaim false 617 23 3404 :=
  checked _ _ _ _ 110 0x14de6ceb68559e719c0aa843f1289661b5a5fc259a7fe042bbbeb7a9e58088595489ffa433aed6dfa0f69071549fb6169347c0c20de8c5ae62ff5ef629f0dccef6d875b4e698b4c21b9d74af34e75efa05f6327019db54a372cb992e2c8f1b583158691e548b3ca550bd642ab7457dd9e8ee4982c9d3531b0077ca8355185bb8cc97b4fc6e54fa3f9edc59ae983a33c7d3dbff5a6264a4596be2bc57d90f2e3d2852cd8701c4490c1cd2e53729ee32fd4eb8f66faf209b549d9f5f5a782fdd4f9302544618bef49a4016a10f070e096e3b6ff04130932dfafa5d65c88b13cf96c4b72015aff94e2887f7053dcaaf472054b3a0cb08ca64ec0a6590979f52ff7bd8b5aa008233e80445faad6b0edeae9af940c83ee189880195d8de5278b1098a1741620b305f522c765a52d56c7442e389942f503bf399c876b2a0d29443add3c8ef562ef7a2f17498180a11437ebc2ed427882e32f647937db9a559e9affbff078e0a28ca34a3f9274cd67d82613795d426dd3965ea4112abd7f0f8431a1988eebb3dbc795661f0f8b749ee16c470fa39a1a8e70a45bf12f3d3950b8b355666cae00da2a5af7a06264fcf4d416884d4686e37847f406ff4d45cfbe58c450bdf41534e0a57c54c8bd80ed6ffc66fc3117c55931a0317036c8aee402180c084055f34602d5be6f21a931246778e5d79e9f2f0dd4a54f24a241f0308217006646bf960f7c213c2c8e1b8f14581fa628e23a1032c32141abc56bc40ae8328afc9e8960136ab77619abee88a0911b02c9e9f190f87b0a611d95fe5df05ddca0c3003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_619 : rowClaim false 619 23 3393 :=
  checked _ _ _ _ 34 0xdccee01530d3b2093797b466e308fa823a72c494224d905a5fb08e371b7466cfafb5b7a6ddbe7baf94a20cb94a0e2bcbec48462eba605c331018bf46d0ba331e37ef24d2097613676e9220568b67ff9bf2d5f946367e290c205a7881afafa218426b108b8c87e23b0dd78ab514beb1fd27faab7860a4f18ec29550c25b2227b81a1e597e34c580b08f73fd353b20f98300d218256064429c717433d26184801172e1806998639002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_631 : rowClaim false 631 23 3328 :=
  checked _ _ _ _ 59 0x1d5fa72e62c19ff7186b6e350649b435c04667fe53c9e543c63071dcd26575c550345e707f65951eacd8594ecc9bf3fc0643946f94c2b99a88fbbc1c3ba98dd47dc3f964d5164b6ba8f1e937af7b3055a48309034cd2bc4ffa2cacc2dbc67a00765223555ef819e98497a602361bf1733165136e3c50bb99ce55e39a89d2e768a1bf5f33a7514c9f6063fae20889458f7c12850aee46ffa8cd55cd210722e4497ded9ef4e669c11a7b08bd415652d0783af86c6524603337dac314b1e2c6fd7c00a38b9abafbd2addcb3830974afdf68553720c129be33f543f2a953bdf3c15890e99b1ac62890de7cc71835db99d29fd30c6abf07b2776feccb3c33b2e7649c1f48249fb90d2a22b9d539ec088266163e5315509f58d38d8f435b1c0d26ba6ba01511135600a8cb11a00381102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_641 : rowClaim false 641 23 3276 :=
  checked _ _ _ _ 79 0x7086731e6eb7be447c95ee6d41163b1a6bb03171db5de9dab03203804a35f9aa22a237b6c6fdcabcbe1123480429253cd71d3f697ef29a5e1dbb4a0d8d18ad0654f45833411eb65a184fdda55afec5f2c904e27018099876e930d5318a362c98bb61df6363d334579c0c496698df0d6d44baf798b21a329dc83cb5be4b17a9fd172cb5a1fe52bff97b86afce8fbf12f0d47fa398921842d0f919727cc61d4b42d7f23342d80f915253e869c173cc1d56a614af885ec01a2d48f0aee3de3cb9a6d52a872377593a34334eaf4604fead1a0d2a244afd43a0e5da59f232abd5723bfc66b03603c9c3d6c760561637a61b0c525703e5b53eb6d283e7a765eaefa66970c6592d8c8ae261256beaf6247bdd5a844269ec0018576d6328e7632269f7c566457195ebfda59588cf1a2b546442b369a962de36bf5ea7784d2ce593ece50188aab32c23137883246fa5350ef88e3822fe9a9de91109c9a739b242cd2a022ce8604158151f27d7a036aad80be053e74232579f1c6307a93ee07696d50b3c435395fcf61e56ad01cf3fb1b7008820502b808d1fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_643 : rowClaim false 643 23 3266 :=
  checked _ _ _ _ 33 0x7044ab7119d5e503c0548a8ab8b608b6823ba4bfb4a9805cb1cfd7c035dec87fa5cf3539d84c6b4946d131d37a6038ab53b7fed0832168d6431bbb42e1f168737c814517283671acc203c3eb72f987fea7df455f2033f7a67672d52481ee4dfabb5a957b812e8093e6b85a372a09036dfddd5506c09cd06cd347919ac41bda0909f7a44b00659c13f83409dc2b07be194dab08d2044465b6748a81c76057d8046de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_647 : rowClaim false 647 23 3246 :=
  checked _ _ _ _ 31 0xe448e579151b3472464b3ebe2106b5512ff45f37671ac88fecedd08c78a67f9c127c1e05efa1f9ea9a920d6162ff02d2caf9c88f7404595277f8d9d7107b5ac39b719135fa00373002b212fb4ba660a00dee8af9600b9fb2f7a9f1336a0db521a1fee52638e7aa1cef061a260650a8c96130859ff69134db2286ab15722d79d60c81732000363ab4bea647f0d040600e233f7e003c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_653 : rowClaim false 653 23 3216 :=
  checked _ _ _ _ 49 0x44b86ec79afc445924bf339a061af5e511f04ece9697656800cc870c9ec8305c1085171de55c6d81a8d9d54a3ecc28728e8b5c14cba8f54ce8df3e38945214162e1548b1419ff450911351999a24396019c2e5565f79a8f6964a036fd50198d94b2c3d7b5f9884aebc60f46d29b405e8f5a18987b63a49fefbfee52cf31b3c6fcbe0a16b5fd9f2e47e0fc0f45b926c96e03a58c452f568e804d58280db47fb5bf9367fecda8164d777f0b229c158644b830ee64d14e76e77b2f1540a642d291bd0bbdbcba1a470080e4b3884658040579d2b20864841e59fd7e70d94bf7ae48c0f2a17375892a81683fd57e01e0b71d20018611ef0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_659 : rowClaim false 659 23 3187 :=
  checked _ _ _ _ 14 0x149c3d56b2cce58de6b122776344685113b0f6ab79b4aaec3bad8d8bddc69b7f7fb870cc2c5c01b3080c1dc0120c50fca8e2ff9da41a3ac91680a574565001e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_661 : rowClaim false 661 23 3177 :=
  checked _ _ _ _ 130 0x4993f430d2dfdbd63a5852d1c36c721090a399b93ca119ab51fb54c9e5443e2d2bd4a14a7f041b1abe87240039f5bce4bd409a847a3f68c37d35c1697e6bc0cfe944286ba502f1126cf80792c20f921b6050339ac8d7ef4e5092238f340aa3f320d2c74ffb571e0f3abd23241df37eb9257cdc78d3470b29f11c54385c72643c144f58f8ff9e9fc36cd89835e34b2d12e5f780ca73c60e28ad4cd74e27b7971fb1bb1b70372c19fc598234c6aa69236b07a593169cbb7ad64719fd0d6bdd168adf3cc8069be658a38f165bc4120dd783f6840b934fe4821961562479722c2edd5298064268809b2688502b84c5ef75db598154f3fcee6c8dc1f7c94f804e80368a9112480b78608d1373b1fbaae21d5169ec0d09aded90028e5cbd6c26b54cd88cfd08ba10bf6d03d3fba41de458eba5ad87f0744c73ebae2cdeb110f28a4ad42093e57c9041f771868bbb2360408c343d59b19708d638cea7ff1c5e22328108ea534a2abe9f5581de526628abcab012d42dd8d5d54f8a16cf2b86c7b9b2cd8a81ecff35880b2489319450f0135066985f63a5bf1817fe35b352b722ff26f9f4036988d77b192a88cfd6e87ce1e92f2f3d8d6f45efe64b5378d9b7ace13f8ececbbd3522f0c9bdeb6ec69f3bd0aba7f231a98216620b463b28116a21b12edcb2ac8cc33861b276239e883ff9eeb7cc88f16f786971c7980d0274852a54578fb39948915754fa549ac72c7e82d83806456349ea48118419a249a7fedf0ea7510ddd86e6fc26ec2a7520f0e38cce4e295f43ab7bba142e64e2e03006d45cc223808f0aa8d3daac322fcbf0906848a338c08614f57db865d08217684bf7d8842ddc572db059045cb1561407862814a00977632ef4fa95fa166f7e563f8376d843e73962070d0ef779074473f5ac5a4aeda78293313154ec42ae933d646b50314f101df5e98be428cc840260d5b0012 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_673 : rowClaim false 673 23 3120 :=
  checked _ _ _ _ 148 0x12de60682254c2f57798abec11c7b3348efb3f874fb649dc98faf6443d9b6daf52f54202fc8a0fa378906c87428bdbfbe9332a69d9a16a806c097c45e7514568645aab2bc018d6b5859bd46a2d3cc92b8fa6f5c31fbddeb9429d2a3c5ddccbab9d60251ab50a57546188c81bfeffdb627cacc2fd085bf904dc1adb4252092b6e5d25f86dbd95103027effd8ffe082b97c282a9da24914e8ba55deaf58a853e63f702ace904ea5f27dd5d300d6db9cc9845b961343ef037d83c7ff495d89a052f95b73acc41c0017e09f28349df1ec81f660d1aee2698aefb952495489ba88a4c831c23575718e339a9e66fbe1e5ff0a68d257679e7cce5c7e24013ca9f52f947538c506199e6169c37b91fe734da88c67a05c2432c31a61d9aa8f48682ae2ac2ddd28aab1de9a27a9d22a975efaaa5cc0290f1e8fb7768832e67a3d3fa2b1fcecdc667e34b374447c2cd4c9c7c6b747e034e5712228bafdd76643693d8f6fb2468e235a5a231b7bdffa6619eed50d4eac927955cec3879c8f940afecd612effe622d8c060d502451b34643a75bb70cf29544d9d5162021ce646372c611641be633d1fd8d674572b5377df7eec4b7b671952310ce1e87b70910eef4b38688c510306cfb9a08ba7ef8a7897381c30a38939ed8b6ac73063e4e1067dced079cba2a9975629a7d61203da2ad355721137e0bfb052d430d8043fe62f335a4fcde304a342fa5f22d4fbdaf2a9dd686387748079f938ccbef5a7a73e1523d3b5f4e8159c6d7c303362b84317645e9fea1185cf4f0d4f1838636cfe09abd9598b9c33d66a37de2e7ed6e56d4b9666511e24d78ac3e6c015ef678876dc28c8099c4d14da2f0a014c055b045296b27bbe56e6d32de2067e9552143bb2ea7e22a3cdfa5f9d9d3bbfa03634b29b1ea86300b2fee0c35dfe6b936880e19e22f93a57827863c451d15bd7dd5fdfdf61c167558420a8d9f4d7148b4fe3f22e70d54e7e41fabfbc3dc72b76b532d34e1b2b63fec9ab30f8f7e0cb8cd4273423f85f6839999e723b04450b1f11f19452ea9f543093ab991a7a6832d2afe851c3862055d2826e1f80d07dde698c13d4be97239f1956d2d007e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_677 : rowClaim false 677 23 3102 :=
  checked _ _ _ _ 60 0x2ead829b7fa8ba8bba0187298396b4d00f11e919bbee3da9d0417ddd563629764e3ddeffbb6d6736c15e19be739b7d5454108607320620ba79561dc1306fd14c22392ba561a006d9ca4f0d4294fd76380cf59d825396cabfa823f5562126f49a4c9e84f78e675971bb9cfbe7c47f4f23418f7488809ec57f83fe0b5892fcb513306bec25a7f56676fdf0effff79b07f953e0949a8420532eda9b45c4a560648f07216e0ffc53c2c2f1f36a2a9f6b5187ce93edb8969c1c8bca0274499d7d5a8226ec29f0d82134ed810358b05c0df85c557b46d290c80400fb559270c9332b33ba56424b6ec233458f7dbc734e45f5d69105ca2aef29395d9136208c533baefa68b21bba9b0f6b7df957a8a9b5040ee75cfb929b5ff5a7427fd15003f2d24d9b4f1c2ea5cb61cc2a51f8b8265937bd002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_683 : rowClaim false 683 23 3075 :=
  checked _ _ _ _ 29 0xee6dd371d00a6e66a32d9e50f79e81b53c01aa765c7980d0aff068ab8b5658718265425c6acf367f566b717f944a0ec4f5a9b63495a6dfd85f2520097cc6486e61affe1ac3a182da6c2013528414da1173644a83a98e91c3f0e4e2a0c8fe33f7dd2b010f285894787f4569b0a60e7fbd65b15772b7dc0065ae12e577c6db4358189a606b85d01c252947003c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_691 : rowClaim false 691 23 3039 :=
  checked _ _ _ _ 71 0x1e5f7206932969adb8f4ab2d729f3c6d033f024baa96299dfdee19fd4fbf990ac355199147ac4bcb583230e3c284fa1232db4c49e34c8dc90e2a630935c528521c6a97b890790866f1d09a8ba82dff388f756d1a162ff4918b1d16aa763b08eed7170740725249da98937c3efb7d08eac0ee4c19b3b4731cac6c0a69d729619dfdb54abcd1a40b9a2cf8e310a4558259a6400d3021076593fc0cb3d12996945074ffaa199c6cdcde6798020e7f08620260daf235cca960e2d6bb7c6178dbfb5630f059f4d54d861d6dd80a2eb1f7b847463166e489f89091d1125778395b5db9ae147548a5403628903399d3fe7a4541a5fcc25d1a620c3096a2c03a47653d0bd90187365591540b6339e0ffe0b516e00c7a84d7b30931855d0581dcc5033a5ea2c1e84a18c845c87e20c21be89f367ea589dfa4914773692b0eec6c11345a83b9dccd925b80550b4228e0421d1d64c2596057b3372d89c7178c05fbc3bf5e5947494031524c13c36e0e0023 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_701 : rowClaim false 701 23 2995 :=
  checked _ _ _ _ 99 0x1c8ff4b542b6d5de27c98a12e15a1eb4cf6e46fc27bed43f49cb989e4e929bfb4bf253ac4d2bd191ffd7d78c39f260dd7c00efa917853b5c36955af473912eaaf14c1eb3c9929bdddfcc421d7470331a2c1a412b105c12de88a3a4f3a5b0f77f3126aac156afd11ea5c753ed27bf6a0752ac9f68e88d402190592463ea09408625d53913d1d8d58079777aa9282965101746d3cc430c82bdfdf0b8f42327b16b23febc8dea466f020a8bea0742480e3e7d467a6d8d5c60c69a733fbc32ebdfafe24542d7f052a67ed88a171dc46da5f68388e333f2839eb76fabde2f03065e5f284cf0e16162ff0a1e9fdb611397653852abdb97d7957aa2898f5b8b2176e4a92fdccf6ad07430e9b46b14cee10767353dd20908bc41f3bf3fa6051d642e65d017de17f419851f5a246f4e5b60200f908760ddfe5b787edcdd4b350912f99d04bb8ce810c4818dabd540700abd1f819bd0f029d94e8167665a7236edd86ba3c350167f96e666c4d82ac4175924df645fc4192a90f80cfc5612ba2d8f816d613d8e66c3d786a3ca5b8c82e3bb165be4d5bc31bdc9006cb4f373016d94cf26849a5c679de60c4a14a76b8e7eb27fd5fd04e3be1c7787daa315a07e6d6a1f3827211f89170cd5056945490412ac2ce83d0af602097a47826ad6126f90121ea13e8226287a8da2fd7575c789e09390902f811ddf35cca942c2ff19d58378d4969079fc9b23003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_709 : rowClaim false 709 23 2962 :=
  checked _ _ _ _ 42 0x30448cbef1ae39425fc7cee50217698fb5a6b095725646be3fe880ea53b9074fd69c328afd5f5adf6dc141fb7546df3fce20edb27f59b2d8484774c45d0d9e75b232be8c960eb77ee467651e6898e6d046156207e947dfbda3c0b40c8d47e84fa710b265c1113e14fa0fbd594cc463c36b34a9121033ad0185ecb35cf1818ed15d553165646ffc2a94d72870f015200fdec3bf7d9006600a50d786ee721f1b832ed2b62c63c5cf483694843b03326c15c6881862092e3e26c3e71b657690f86cd6271ae43231b32835d680186c81aff459836e5de49014a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_719 : rowClaim false 719 23 2920 :=
  checked _ _ _ _ 20 0x9e70498166a0db5138e5c8940436893162ba06db6a35230eee7745caef4c076ca6ed9f3004004804a41edb64a1bbfbff6b3351e96124dc4da071f27ee44c2896c9dcb786ebfa1e283de5e97b4c6b328ff28177c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_727 : rowClaim false 727 23 2888 :=
  checked _ _ _ _ 25 0x1869129c8f0563a742c7e40fd5a2c5adf82b8226365e9bc83a282fcc8085c301c0bb1fd27b3ec6984e44f172dcf7578d33c28b315d34cb7481b9dbc8405cbb8e54193dee5bd43b3e06961e0546fddb4109216490da432b7a0f0356793d467fe7c7383fce4f4e3cc964d1801b027724b9300b461ace003c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_733 : rowClaim false 733 23 2864 :=
  checked _ _ _ _ 64 0x1a530ec83da4e497be8b506d5e398dd636584c69a60c318840560e4a9bc86989bd46601a875c455efb58ed4e250765a9664467b55bf9acba16c7ddaa998703ff2eda4d2124efe811510d9e82dd76ade6897fdd20e294c41c24905a6eb7a4564b157f836d7b44ee39865c1b1d613f32faa20e14a1efb984d93b750627adbe17d57fddfdb18f3677cb82345c7d55f2c4bd241d61a59719f1f70622fba86de4799660ab3e48b01189ed8f8e51750d2b7999100f3bfad46de237245afb181664abdb344cdff14e55c251b12a7ad639a4d16bd340d64a6b39562bdc62a636223056dd3658f224f672fb217acf26942a1ed3a72d6b78de511f1c59fa470b0a5e8d9633bc8560c0c029ce0a635132f33032ac73a6585a274f84857e6cf5612cc3ab954329c7fc8b567568a15448e9357a26210ff0e570ffa236e7985d176acc4a66ddc596f103a95906b0034 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_739 : rowClaim false 739 23 2841 :=
  checked _ _ _ _ 57 0x3c88c17cb8fa61d237fed80a68b7936adf88685b8a20280795ca0d1f310ecf3a1c244b74a17c0b3fc516b1756032dfbb7643416914129c5d86d98d72a5f8493e46900de410c9d243e3ea071824a6f680e551d5be26ed94f7c52db0a636ecccf929707ca5c11cf0d05b96579dae059e65f0f30414472c4db9021f1984bf9661cd3a27b690e3eeb15d00a33933159d680b291a293e3eb2902995f1a09c7b7059a30a99708ada9212ce1947d7e3e54a1657fb351f48f13adc1228f9daa076fe277f6ca03d8f9a73063b2253ac824cb17c228518cb398187f00e37810ef09376718260faeeca107b06c19f340609072fc2187c6137ae1d1ae20bdeeec4118f395d016f2edc899f655e43fdefbbd873ff518cc3acc6e3897b1e77c265071541e530032fcb370014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_743 : rowClaim false 743 23 2826 :=
  checked _ _ _ _ 21 0x26fe7ec815bafcb3d73b0c867d70913ecd7988a3aad64509881ff96252c23098f8a581c71e29606b86d51e65385de2e4495fb7a4816d91efa60369ab7e883fab292e1d6a1baa71d920a86ab2fc80ea219352b53e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_751 : rowClaim false 751 23 2796 :=
  checked _ _ _ _ 44 0x50037e06b37297c94e2ccd91272c0646628f3ca03e5c8f6bd02b9101ef00d0a22296923e1d2590c7d665a8c2bc6b1e4c50441f70fa02ec9862834df9e2242b2ae2de9a562d053f0521caed91f1ac9a30fe423a9e93136fb53ecc7f3072b7bc4e9969389f2a535db89dced3149dd40d6704f5c69e44ca4e2fc034345edfb8aaaba92fa7d70129d68a83d938c2d4fad5895580644d583c65d9eb4efd8d3fb6b3b802cc7d64910d2bcee61b4ee370c12f84b17454ee8bd177a3f98a46ad03b392e79322d30456a021f9434100783d83d800c09c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_757 : rowClaim false 757 23 2774 :=
  checked _ _ _ _ 142 0x2c7140ea07a884a9fc5e5b531b3e7f3925b9d8bc2e295937b51998b9dff538ecf399e9f5e2dc9d7f640016dce22b5094acb709d2a2d9e96426bbcd53626a3406989cfb4b253aafaab1a5cdd9764e41c5c8fe2a1b803cd7948df00d6df5ba0d12c5d6805ddcbae257e82866bb8ba3c1cf4cd86597bb4391f574d11b6cdc0fa726f46cb10905951101399b0dd513bca4e012514d6a1ae1f59f887dbfc63255fd86625e7808adc5e7ec78817acc438a2bae4b154f84382b8c589b3aba23f0e98d786be885e9d9e634318ad221241777028398c7b67fb5a867474c61a71176491617ac4c04180ab696489d4b1addfd6e7b372d0c9a8e253f5ef001ef2a0ec6dea3b405d623a1c50430d4134a79cbb1d25d686208d76061677f467059614802e687fcca3cc652cd73961d3232154e6541cf30aa6f1a08970f44948356f5cb45d040162e505d8a6b60e6c43cfbdb78f620f309b9e8f82abfbe22f80475b18320c7ad2f5d9d09629dd518f329c2d1aa77878878a1dd33754708be267a044cdd1271919abeacf6d7ca31157ad91ab7fdcbd62decc094557aabeaa069f3de365a647c6bde7792f70d7ec63fb0603dc668334977df0831fdd940f121acef1bfad9cec578665979f68bba68460a5ce7f46da049da5222ae50ab17e640f173cf3ae83c96843c82afb93ff5aafb6b74a289bfc464e655ecbb88382537f1f60ddc6328605de31a7dbeb00c1389d281d1c483e762dab5bdd07e623a80577d7b0ecefc8c84675c3c346c3330ba199843fde1d39e253368b187a8d6cf7494cf2352e41fb1fceae67e3a94cdbc341c2725f3b2c7b522ac9322b93d490e6b6d3bdfbbf3fe9e8287b6d1ad31fcbd2b073b644c7e1e0b42328b5afe438dc2132f05ebb05cb3e093f5e32dc4300fe9907ce65a9a6de943c0d01272f83b177c295b702a6851335c61f35da9717ce325e033cb28b7f5496b4cf456871a94114ed28b9b5b307a82c3fa202d20ae2a5ddc954d7530c8cababd31cb0c3c74a3cca85f7c066b79e682be66c895cf66480486d278b84251fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_761 : rowClaim false 761 23 2759 :=
  checked _ _ _ _ 99 0x927d9b9f1276af23f9b9e8a7d8c40ac6722163a251d67b8ebb72e19f07a084178c285f777ad99f3108b18437fab574d1706fb38a3ae45c6e082b805b8a47d052d7af45f3d2d32e211bc5e83a869fdd85e495d0680be111ee1e2154148812bda6bde09d9f0ce918c5487f4cf07863a236598678c1148eee8d01bae62ee440e86901b15af1455bef442dae7b6078817f9928bd273a2f5dbbedf72e00c9e2340d69a8e8e7c5cd307616434b20aeed746301cb93caf1eb2c3aa9065bfbf3ed1d2ed9a30092282508dc46279ac8ee68d7ac6f4e8dcf19bae14034aa0a55587d84bbbbcd015992c7493a01980b339a21a9c13ab0938ca142034014c2161c457f2f8045ec7a920c78da11e89db566543278e6147967cf838e02ac0ac2eb20c17273d525399c83117cace89c801efd6a36a9f7795dcc0244d47da3c17701e9a2965458aa86dcf095e03fd836d6320f5697fe6734ede642e9a6d20a6e0c57dbe4636a5c618d7a23f8c5a0f2250b5d6530d6c872e4e1a4e70bdab35ad5b71a5c65de5d41086428ab93dba78b02fabe88a7e0075c69674305a918813ad77f485de636689776700fcddf3517fa15e0cc5a21b07d9e9a0644be8d3ac1f36c24c9354ae565afee1e04ef3358d97085ed8de6d13888eebac0de752b1cf6672db1e1221ca9de789065f4395f03eeff22288dd4e6c8e97228012929bef2b963c30b03f570a53002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_769 : rowClaim false 769 23 2730 :=
  checked _ _ _ _ 28 0x7ccff3e6712d1472b4144eea43ceb6a7f76df062a4df6b17317ca8f9a1de4457ce89ff9d040f279ab57442d3065fe3c589b0bbcbb822f0f957cc13b9366f3dd2a79409cb046028986135bf86e0749e92ca16e3743461f7ac8fed36b61714c908aff9247a21272c5226cbf37f55fc7da4b45acd12ebfe9ea36f01ce2aa1ea9a40c107ba08023de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_773 : rowClaim false 773 23 2716 :=
  checked _ _ _ _ 33 0x3a910869d91825f8d618f45c740d38f9daf47609ce64ff8c156f0eaae66a49f45b5cc2062db3fc61da22f6f85b038255478cb88965f971fcc66f4d0912e7b782234be14c1cddb354f9fcfb628ff34c233ed960d78457c901d3b4502299812a6a4f8ef429c89691e593cfceebc37258bb052d50c9d2d05732c26f993943d674c5c6f255926ebd406b2100f9299e6539666c7d140ee6ce5ba9488a2e4d588126e20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_787 : rowClaim false 787 23 2668 :=
  checked _ _ _ _ 42 0x2d713547563d9500db34a996434a5728826599816dd232188e04dad697b3e5a81d548a97e43031d197ccb21dbe6f850da9c4526281905277e059d6573d0be173c0096df5ec4b3b0382f59f615e96184ca6177e45bbfbc1fa83c57b3e742cd7ff7b19bce9d352f94d184d95412d4f3d1762142fdf2d9669ba590e8a950cf062885e7051454a14e06c89a59096f851a155a013cedd726a9301bf839a486033254c3d4fd1b14e10b48443df22f2fc328ea2b4047057534c3265166173e761bc91ec6705fbc3bd0faa99c93b5bc4f808760d5b0012 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_797 : rowClaim false 797 23 2634 :=
  checked _ _ _ _ 29 0x1fd52ac05e47dce0e96167cfb70c4b24ce028474ae00a2e72d1f22f6560295ac1676e0a75fb1e422974e77e532f9b9fa147a80c063d571df4374f1e2db273ac56396f9bd31ef62052b5864b4dba2f5deab87d34fe6a5862e410f5c619ff79b18e30bce8c4e9377cedb76b1f691928387ff22db2931e8e0263cb98a9c1e15240888c76c950e8392b65a380b6de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_809 : rowClaim false 809 23 2595 :=
  checked _ _ _ _ 21 0x11a6eeaea6ed6bfdf002fe4c91493f7ffaa7c2acdf2e1a75f53b8c5145ee92e9026d87c71113990a3c9951d2e659742ab14c004de14dc4a4da9ec4069c9a7b4919ba959803e21220947c6c32a693fdcb28aebe3c90675dfb328344383e92c80fa2d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_811 : rowClaim false 811 23 2589 :=
  checked _ _ _ _ 44 0x127fbab73f01774cd335b3600d08bdb44eb28ec4511e2c6cc5d7e359bac1ade42729b9f75386f455d73d47695f4eae02757fc5e31110ef0e4492c016f02614e9697e05003d2df8d9c9f06b461106a78447176b4c0f4d6049af5b512ab5e3a9597575250a1319359a210ad95744bfac73285b61b2890379c14b58921206aadf3156a413f760718274d06b2bd3213d52a892f1d18e34a7a371bf79b140d3d87a9b2f12991228103ba32f6cce73ee58a0319608a3336e6d072900db1ce5c68308fc76542a9ba8cd6b9850bcaef6c4ec16b3d3cf2ac5938fbfe80bdde663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_821 : rowClaim false 821 23 2557 :=
  checked _ _ _ _ 104 0x143210a979b5da61be3a316354dad2a5d14c7f37d7184b46784d4e7c882f63fbc1f05cf3a15639bbabea235f101b6b68bb9390fdb422bd51aad9b0721e5af90f7a07f98677980e5ca02b7643a9b10d4ace5456ab420e2b0bed521a276707111a23a3fac56ddd1044d516d2d4ab93b03cbc6696572afb05b6fd4f6839dcbce0aa055a46c52fa67bcea6bca7bb26f4c2bac930aa16d93d957b7e3412c2e37b27310dd95b006f118aa99be68013cacb4cf5217857c34ec24975b87c75acc392c5d42c2c624b32eec99bc61d824a25c08fe3d8e8171d3085c1a9147cc190f90fc181a7187d2f829d6dbfa7bbe76f50b8e9bf2633a7ddad490fa59306a1b9b617c6e2c039bb23c7b7c11c8c6595e8689397630ec3366da239d8eec7915d0d7d22e354969f3210627a7238a91d02ec1de59e9e15abf2d45bc4a28eba371dc90ad1466e82c1567399f5af97a26df769b33b408ee6990573b7f1204efba0a643e23ad49ab0bd852538b98c5e8ef5356348a097636150b920a81558dd4c1c3fdd8bcb197dd7aa4baa5a6a04cd29c5e99542d71f3607fba5e0543b02ba37fe26ae8377b9d9db6baf5fbf69d7a929afce8be6c50e44abef8007ea7e5933cde3c5693c8d8d068001465e35aff999a8d733e4038f68738ee64fb532ba45f1d7736ed55423dc233a85f837324192823b89c84e8d1599f1ce4775366e129eb0f98ac1d28c090b8b6845c1e5feb3f578c32730eee6f60364a743ae6430c3760c9b23003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_823 : rowClaim false 823 23 2551 :=
  checked _ _ _ _ 33 0xe10253598b18ddc6054a1059cb43ec19aa81a0f5d698bf4c3d9d7a54e24df944b46f64c41f0314992b5696492c0c68d182b042fa67712c002d197d9e18bb9f9ade6cc32d49175b83f0b8e2c15d137197abfb3a1c49671a9d1f66dae4eee8e10ec20285c190111e38bc850a226ca666e0c57b39aeb3cd3580fa558024c8e207260450de758b93fa779de22a2d0b05e2f0c3b15fc68e02d0c32620078370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_827 : rowClaim false 827 23 2538 :=
  checked _ _ _ _ 29 0x3a225c3d5a6305c92e173e496f90e8b61024b54119a56fe25f709c708572010c738ff0d190bfadd02c4d46384c4c1fa57479bac5c784abfe44bbb5a5cf5ba7af12e67e6376cf536a12b7eb8d5e523949462ef3f5ac4cfed347ee0a3f4ef6059d9e9158f2cc33818a07830245eb5a12beffb6348616b99a7d5cf720ba613e14b9843ca0345b00be309a700540a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_829 : rowClaim false 829 23 2532 :=
  checked _ _ _ _ 50 0x586d69edc8fbe1c377791fca9b789dc13f51688b7f8c902a2a98c6651cce04c701543de105e007eceac6e9babd56f3a626d69e7a86e40fab2b0708f57ecb5cab6b40a30a2405c224dd7b5a40854ea09fbe47fe5bc9c394f283cc20debf6436b2cd99cd56945943a20cca21bf7d0eab6ed784b10604d4a09a7594ee5d479cc9b98c558463cf8991f575a14b050c8d561103c452c06a6831d7cf52d2ffb9184a9011e9616c87b954ccf21e29ae3deec06a42c4813c139752517608ff6d97c163055d454977d2764afcbc48560718bc2e66f8c521f9781059724b20b819fee1c9def9d0fd7182393b16f85bdfbc6b85396e50f4cf906dcdac628972e18069e20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_839 : rowClaim false 839 23 2502 :=
  checked _ _ _ _ 16 0x3e6df080608aaec35c3f7afbce6b6dcddff38c8fcecc3d0fbb8f1e3cf5e5f346989f276d06f10bf3fd952b0aa5de2af991e5a49ecdcc21afaa64375dc00780afc1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_853 : rowClaim false 853 23 2461 :=
  checked _ _ _ _ 45 0x4104f5fd45d2924efdbfeef57beedf8ff71833cb214c4acbbc48256c349d632521dde0fa2c48b3d818e8b0d1e0b5912ac92f5b0eeeee9ff33e089cab60524f71e7b7bbef600bea824a0698831184a8466f19675e6b27c1bb754f542469ce1b072f27e529b0fcf703f6112e495941d082e8a0786b281cd77c93b2b34bb8ae8b8eacdc385c2a83bfefdfcf6d65e2d38850a740758f5038cfb0c65980d37869067bfa4d16c17a57b50972cb3f62410916a1b81dac15c5d5e859115ca76e78a5ec220b02292932d97a5182d20217017509925898717182038508c142a143a1e601705e663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_857 : rowClaim false 857 23 2449 :=
  checked _ _ _ _ 50 0x69bfc5092c11e895d87f2e16540e1b33e89ce0bb8427230b6c957af8dd562665d05137f8530c4ebb0001eb4ab74e07ea2b923a2ec4990a10caeda37696fff83e8bb173b83a9d6475ec524c7c5427ffaa9c0e6c2c89b9e9a8dd130da757c2665eee1006cb2cb3938e3f7f27666ae4718492e05868b9017e58f76832592c37280d09879528f7d767e743c0b420b0c4971d4a5b50f13229b47103eeb205c4ed663be7b05e8106579711ec5458b0347995324b260994c65492e6055530cf759e13952fd2b237b23164d8c5e86eeb8d589aa610a35822667c0cd65a6bbdb1ade7e7f9531862cdf8378b075f18b04ca67765024a2c3b4f8c7a80bde20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_859 : rowClaim false 859 23 2444 :=
  checked _ _ _ _ 39 0x384027a3fd2b4fd3b0048908309f07c4b5310c00ae94bd3cca8c3df6b995e853102c03e1629491b1d52d62521ec40a6a0ffbf01ee80d12c544d6d6a2b9daa337d1d1962ad4607666775727733eee6239eef0b1fee9d95480c6d589c92fec81eaad770b2fa8b87eee0bd40135c93f8f1015cdca5c7954d51d6aabb600a6e0fc4afdd2d95b3a3acdc5b0eb9a9bd39491dbb7ad280ad07f48ed0edd2de8d26302cf50edcf57b6f2370ff264ed24266aa53867bb27b866833b971900e09b5f0f01a0a5b4b00a4 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_863 : rowClaim false 863 23 2432 :=
  checked _ _ _ _ 23 0x188124173d630ecd62ce39375c242a26cb5a8df6fb0f5c2ba7574c44903de0f8c1f639dac83c5808c171f15ba101b5ff04849db9e88396062c32d008850ba3c326da4b88f7fd1fe6ac45f6af7d3c3da220dea7e18604543eac5586d111184c18196b810e744a8801e40423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_877 : rowClaim false 877 23 2394 :=
  checked _ _ _ _ 94 0x430797f47d05f983efb895b9a2199d3bb74fe62f8c187ac1f3c9f0891acc3ef197353d63f0a4461ebdfc971506096d670e0c466d019f6d3306492f9a2739a5a119e8fb5d70006d5d782ad6fbf2a5b25edf6588970073f11f3e476e9ad01b10936c985ec15b639b4bed856b21376366a8f493f10b8fe0ddaad8f928ac934e0959f259a0a5ece81e598ceb6d1d33ef0ddfd1aa93c0789aa3ad2b599813590772d66c59cd356207434fd42ee8fe7c6f48a7f3308b3f8a056261d5daac5f173028bfa21aa9d8aeb0ff9b2ba3c943b8e0addf3bf2bca9710cd1b02b05ec398312cbf5aa59c04f7f283e602244a1e5865bd47ff6662e0230e6399a3864e7f36d96cbf394f32e95c8d308413e519e2487638d2a89989beb7398949c85149fc38605cae52b2fc9e49228dd6e8372e406aa149e74cf126e23f6d6097573567c9112d540de8fbfc6c94124085a9ed4acf6f91da671cd0bcdb794c929533ca9cfbb5912ddcf69b0a6b8cd8b9b7b09e9b85f955612a6fe7e02d698dfedcebef70ccb0e825eda9b6f31fcb73ed9c54307ad5788ff85348e2de3f23c432c5be183ae76efa174ff451f0a6cad8cb782dffb8ca309a5c69b30dbf67db0e7eeb3551ffdba5392476277f87079cfd5b0bcf1a2975f730de81ba3384d4e7ebe16156d9214265b106900c22c88658ca7f5005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_881 : rowClaim false 881 23 2383 :=
  checked _ _ _ _ 44 0x4bd296b235779ac477180de9b7dc08411e3dda2f3d41dd56d4c2d305616578ffc4e3929f99ea66829b7ad0b6e931aa9bdc6691f29ee6026a0ff1ef290c71c215adb44e64c6656b579d68b40168a12808ce1f6ffe0e1dc685f3ec94e109811c8b63cc84ec2f5edf691a0930b9344f34d93002774cded834419c495bf715260502f108737eb82f5a7c8a922845f550f7792631cfc54765b1d296e90d3609a019c6ec0857ce66277aa184030609ed27df1dcaae9f1cc88d98ea9ec6999d525f911e9173e59bf6516ada415d619635bcab42aabf5845c9691e4f767b815ede663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_883 : rowClaim false 883 23 2377 :=
  checked _ _ _ _ 50 0x2bf73aba61be9a5e7cb5c65145e2cf0468c02b36d71f9d7b7189ffb53480f59ceee55e0b2034dd62c9e9e3ff8b81f333eee7cb7a881bb20ab2ac833452f857691af74921272772592d8adfb3ea391fd8b6ed863eff447e17caeb6b5c59bf0ba415319c4a221a8a6cafa5ef98ce31b52141cad30484da6bafcbcfca5ead706e3a164ad658c85b7261cc7e3dd680b84b9ae8c856fd71f2bbd3b0e700eeefa57d5b8436e8e5a1b6a7169bacc5356918a64e43d083a1976c39d3197db4bed14638ab1394feb586e8fd5a6da483082fea25ef34c0591c118dfd5add50164b846922b847955023bf6dd2556877870d4bebe3c273449482ce731809630d61001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_887 : rowClaim false 887 23 2366 :=
  checked _ _ _ _ 20 0xf6d23aac1c62ef95e13791ee86a60df29828a435784793818d53a8c2dda0d62358617f6e5823ddfc1e29e875c05e8e3fbc13d8657a617051092a53ea76524af1383a1994c129172ac6092f7953e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_907 : rowClaim false 907 23 2314 :=
  checked _ _ _ _ 43 0x1011807d8c26b89ea730e6f3791843737a28a94479791438b5464adc925671637c20f014090e750235ef62051b8d1a2a4b9010378209892786c2d1a464f5ee27d9886944c636475aa73325c6c759ca5fa3ec77c3cc91ec0e3f34c598dfccd12ad031307269d876f71f5d41b0908da22e99caac80a75b34df90f5e18ea55147875bc2f5a076336a2b09ae61a09fe1644e5b765ecd7153136896c28d0775db56d8f2b949c3810fe2cd02eb63d9df9be9054787861057d4da69a598ab296bc52079fe6966617e3e2efef9ba130d5668bfb57cad8d82a4a07f5005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_911 : rowClaim false 911 23 2304 :=
  checked _ _ _ _ 36 0x806eff558970f3e606abbd3d7c11e0e57ef797c41b0c320671a6afa741a4a606fb71a8b9bb4dfcc28b505cac38892a4dc7e6b1c0a907b4b39f000d1499713fd3aaa5127f44c4dd5425917e1928e6f74c45d3389d5faa51490a37ec18ca275dd94d1a795b33f232d425298e0e36618fa46098d0782dd3aec6f5e1a6a4bc12da467e9cfceff214651ae3a4569f2edc3618dfd62762f5c4197708e2c088c43bc700f06686680144c43a800a40423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_919 : rowClaim false 919 23 2284 :=
  checked _ _ _ _ 33 0x8d5cde90fb59f556f7b597f5707dc8c47bfa96b66f2046618b3ca0d3bb73cc994bbf8822accadee5e80e99f361841fa4ffde6ec3e6cb6c53ba3f1439e4b2f20710ac7e0a2835698d35629c039aa11603c50f878dc55a5b13952e1d3a3180cbea4bf386ee828c4b43b3afc901b5d00348f389a107581659207c7ff1eb1e7c028120269f84889ab2c3aed0fe30e4de7269fb1a607e810812cc1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_929 : rowClaim false 929 23 2259 :=
  checked _ _ _ _ 22 0xdb3870ee539c6fb2bb97c574d906ee4f3185f4fa08c67fbfe1736799932655df1d4efc71ac454af97b9b2715e2f4e27a24381b86b21acba5bc772e0b55ada8cc74f9bd6dda726e257e919397ba97ae299a16c0de6299ae9c7d95396e50f4cf8296c40462822d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_937 : rowClaim false 937 23 2240 :=
  checked _ _ _ _ 60 0x346a0c7c39eb03dbf1626ed3e6ac93be0505a0599c23883254f5e1c06793e648ecc9ba7d76b7dcfd7da66c705872ccce79ca2e22d255435ae195ecb0bdaa15de2537399d0c3fbac6322d27d22f0ee0e2463ccbc448339f07972cc45e3222ac664042005f69d2fd9ab5cea95974eb311699395eeb4bdcc86b31075bc9375b840e89288ba323b39e04e4aba5a12f0419e3b04c0575a7cce4b21a321bb02a77857fba51604469c8e2d8d98c4ef5396e3b61e3e1d16e18599a225fdaf7de851f273bbd82032322b0acf3bca9e470ee7374fcee08a8f91c432b617412fbb08d18d2b390777079759b50e44aa0230775f50ccba8c7dd0f3420abe1e09936e9ab28874f4468b43a3b7da84c832945bb1c360cb2efa87b907796fe05e08b72bfc09b4f6dbf334ccf93a7b5f5cded0044c777ddee1585a7d1d8188de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_941 : rowClaim false 941 23 2231 :=
  checked _ _ _ _ 52 0x5b4039c65cdb41e005d52255ad13a88078bd335d7d85c2e7d6f1a1cde4104bd5ac520facd85c17210ce3bda055c88bc48908083dc6e52c2964c521c93d2d643c8021beb8a6d89c07741ad37cb62e90b6481f23078caaaff8cff6a183dce187872a9b026ad45da0cf460cb7670583c76b5be9b37d65fa6d44c08adbb1782662412ebe84847eda1823dfd6057786c0002c8e821f2e8bff2421e289534cc3a5c96023729fcf3ec5a1666836697643542df4700ce9e15414d5062cc139b852b88699bd048e0465ab963ac632e7bdd951fd515ee1706c07eae4292cfa02b808eac95504cd135b1dfc3547d655c9d5dacf42325d91593024431ba959f32f8da83b3a666a807ee20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_947 : rowClaim false 947 23 2216 :=
  checked _ _ _ _ 31 0x97d6bddf268d3e42b5c74476fa474e057af33067ed3964e3191b365034e7044cfbb9cbac67a5cb37e3eeded4fe0795dbff352fcd710b362e2c79f6ea61476727c5e2708cf21cfbe60fef80c2cbe10ee8b65b43cbc12569bad56a31241ad365438ef48b5f77fba7158651b941e387c52bb9eda695b02cd6aae294fa063446d011eab9e0157b44186c7cd39a5aff75ca1f897fcdf3d005a0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_953 : rowClaim false 953 23 2202 :=
  checked _ _ _ _ 54 0xf6c92c85ea8981d6f4082152cc40b6808d53ad14304f66f03876350b5d17cd2df443fd5ee64e28a1f8c270c06aac36716c14fba3f0e4ff04c8258970fe35d9cf01ec6b78b94ab0a1ad4a0e8db4e6c7f5c752617a1458232be9dde5d0162a34181504d2566ea17a4532dd565e42bbdc3715ff0ee4272f21c80e0a7ca7778f4356aa297d7fcf920df89e4e2072216dab60a7771e575fa5ccd6e8906be11e06d799f271c519371a73ad2fb88f115b115d377781f205753b86caa2441a8860a1664aa117d321d36138083174148fdf13c1940ee73cfc0062105f8ebab50afda27f32946d4721237a096c854d5bec52b68ab53a5f988deee2ea5697199054cd5d75e92022c032fa4220d4d29465a25b0581c11d3006c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_967 : rowClaim false 967 23 2170 :=
  checked _ _ _ _ 32 0x149567344c040900ef493a27313e236fef1f545971595dce70cb5f02ecbd438c98a887f69cf000b0779e49426acc76228d2344dd9772b13384d9b2f2a5000a83c0c7303a93c664bf43b5bbef3e04ff9bfd37a8f73fb4dd6b59ff9e593a2d56c5a84b3b1853fb521324b0e72b9a7539ff3311b194e61615a1706356d3f52455f8118d02ef12b05c106de1d7a28fb890fad02d6d6a9f0085e9c02002c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_971 : rowClaim false 971 23 2162 :=
  checked _ _ _ _ 23 0x4a100cf698257bea4c7d4199700311b807f41889b253e51a28224bcf0a50cc6bb58cb71c7eff8feaf74749d21edbceae193440884d51d1393c5569bb99702ae69518241957dca00897aa77637852d4f997e96daa56db4deb9634335e851e894386a89417763b6847220981007e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_977 : rowClaim false 977 23 2148 :=
  checked _ _ _ _ 55 0x543890090af10f5ca47701503d5220cb5ea3a0beed3eb3c3090ecba762320b2c6364c0a87e3fb397520fbd84c5b8fd578c18384a7821cff21051bac101e5802bc8f6780de9fb5d22bfe7a152dc4f4d0eed318d938603090c3b4de2040fba777c7d33b3e4e5a6ce131c07523bc64adc4b6cfa062fe0bc90bf1092650e0532ef0ac7991720b589c6a23d89bcf4a5de621f090a09fb472f07e22f441c0bbda35a8e6507309072578b6464c4030c822cd81c5d2670de62c9f5c510d85835789e4c4fbd396809caf12ef27f83fb9be7f2fdfdc9cdf099fe602fe0e2ead0118edc9f97078a9183a68c743ef5dc621cf089782cf8c9d995463a13841d869e03b1e3351392c39e983033c6c8e119cc325c70296634330085d5d57000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_983 : rowClaim false 983 23 2135 :=
  checked _ _ _ _ 20 0x1f1650c97a74278ceeea515eb4eaf3fb2afb811b09ad56d152c6bc1b52f777f8d73926a184c7b1f002b64a94518880f7070da8bace1cf0826018918f0133ae91bdd4f6c40d88aeae0be02afefb1a86f13ac3e30fda2d3d9021cc1ac200241102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_991 : rowClaim false 991 23 2118 :=
  checked _ _ _ _ 47 0x9c5ef4052cac664fd01ec14332f525f46c7b0bb03a72cd56547294d206d83082dd9532bdd3d18d4b19dd45754eda23dcbad3e87b12f7af91effdc5204f25fe83528d2b0c48408cafb982597a9b19a6aa3f37e0d5552acc02c76757acdf5cdcb814e2e7bfcfbb29fb317d8135ce0d9f11a998e55a16772474874897fcc5e516e1c097709224ead19d3df4653535fa21d42f4c6a2cb8dcf19f239d0f76ae3eb42c17aae241d9e56871f99e2f2a8e0518ad817c2b6e0b1bb0dc98c35e14a8feb9d0f5d8b221c81e05007578c8d59cd3f10433bd713a73ebef7629439434100783d83d800c09c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_997 : rowClaim false 997 23 2105 :=
  checked _ _ _ _ 77 0x6537cea9c7c0a03b5d0e6d97aa19a00b58514edcb27d1453df40bd642ea1ec8e27e1be3b20adfbed2234a94ec3de5aa8303dec2b3caf015e0e5919d9115ea646c05408cf2575d29afa6f5274a6707e44599e2bcd60febf5ec21acb83979786a68d68cab388535e875328a16b162298df7b4adb8632d649ed06cbc1f31b081d6f4f66a8021e0a3f0b63188909a7e7b94481fbc1a917258b8bbb53cce6418066d494e57462d0ac3fe41e11e36ff8d55bdcdd9653c80c7d8d91ff92c45de474e68678edd6e170635006841ce76f6326f36dcc26ddebc0216827d94755ff366fba36d34fa1fa824f6a7817d0d893c53052bf82e47a0e6cbf0bda8f6423917c6b3a465f63f91dcb59c5157eb994c3a1457535bcb557c338690bc94ff5083636cc662605cbc0391403ae062bd0af7f65825f1e41e4b74f8e5e69616e398b9d66b51773d1c02cf8bb27e3940e0d6c0a06a3f55c69483e13a596f7f981acb2689739d59254ed8c9a1f763012519e25025ad02dff22e1d6d5f0604fcb7c66116876499a1a7aea6c582dfe20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1009 : rowClaim false 1009 23 2080 :=
  checked _ _ _ _ 69 0x48f424262bf5810dc173d1b37ba5358b769fa77c061c9a008ac55300c5acc24665731603e879952c70518845b345ab5b30397770b4fe6cfcb002cbcc250b5602492ba25e8f82edfb078e31124fa6c6e30ea574f832072349dd3d7a31fcf345b5d15c7f80b83d6c85ca994ad7a517a775c2652da9adf709ac6842c97c711c4c75bdd1f851932fb7786aa21cf1f80f45b21d30c5e3a26821cf181f4e5d70c9be285ae8fc2d4b3a86ee7c70506f875dc58fc21bb652e3d67d2d8365d904d80197b40261351c985361d03e418468f6fd8bcde4266d44a6b8ec374aa8e212e4deb0096366e59442563015ad1bd9ac8e41b213e7273afa7f17f3b77a5dc5cfda54798770d9d2cf672c161b76eab8f97d6fc619be3725fc423e89963a81c91ae4823b6eab3a4aae69c27f4251d2943328ba2772d6c353daf6e3503bf1b35957ebc075448ab9286b7cef5567257269a4505c9c2c9ac1b52b9d359c425d601f02cc194fd30fec51b814d534350082 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1013 : rowClaim false 1013 23 2072 :=
  checked _ _ _ _ 37 0x4f034b29056e3f7c454bc210a283cd2374131bd15b7f31828313195de869980cf50f52e39ec7a2981f61d006b6a1c8391382d1bf267eddc99875c7c84242e11ad979712ce4648928933d41ebff9abe6de417b5f2dbeb673cc7d3a498eecb560310cffaab5d35fb8cc1b470c6a1a97fa4b4dc695183e65f2a1afa804bd265038ba45224823509aa8b3b6349ca2c6f6fe332881e58cbc632cbf84db9134df1be218d1efed238f17eeda23660a91cedac043c4aaec0090723470030 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1019 : rowClaim false 1019 23 2060 :=
  checked _ _ _ _ 15 0x7eac25b0e6bb095d97c1884d2248703a11592552e7c0b08ff947d17a9c6187fa514d7eac03e3e032ef02be8fce0a9c9dcfaf5c629749d3d0b98d982a6d40f2810e74565001e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1021 : rowClaim false 1021 23 2056 :=
  checked _ _ _ _ 60 0x272426c0f066f150d847b6d03fefc79a05a9cd1c6a8814debdba7b2912183eb19437e70eff7f00753bfbf05f10f85f46ab8ad0cc3212e008d07aa045d72db7ca5053d9166e20e6f6dee8e109924b99a4af2b00fa7dcd130bba839a2edadacafc196c3b1bf65ca35236651fde7e46c6d1d5c79a4f6bd412e4ca85b52b683e99449404f446e8d079a68e5a994b895986099514eb8fb80302080aeb3270b49e1eae873447cd765f65ba4772d71478c2083754b13d6915395654f35fdf1b7e87e043ccc11d573c2dbd732dc2c7a3f01fb720a517de07a7793ae3fb322fbf7a0294b7689655e244242d961d4bd2823400a0135b0712814bb15c19b605c74e0e8acf40da0daa3ddcf3dba2dbf7f19dc9f10c8b4195eb6ef83f6e032410300a6bfac627a0e83a09173ee73650c71f0df0b1980fcde663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1031 : rowClaim false 1031 23 2036 :=
  checked _ _ _ _ 16 0x3efd609fcd547264baa066f69b0f1923895acb90431957b897a4a52f0d81b79218243c2d1908b3bc809f872179ecd93edfeb4fab593527e153e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1033 : rowClaim false 1033 23 2032 :=
  checked _ _ _ _ 67 0x423c975d4b66a8c741f827869d77523ae0d057d223362332a5efb7781a511f0a81effbb0d60575e10460ff7866c38efa565560ab55be6786ea4870e1d19ea0fc454f3ba3fbbe5dfbe1e95ed65a133024f2968b0fb4c4f4783d8257cc1489f921f92968d09f85c3d994e019151e1aa4ca9858575989aa567453551acb1251a762972a2e268aa0394e8ec14769c7564cfad9291f8ae59f94032ece297675637dd5195b2c4361714db3f10da084b162d69fb00d69fc81dc020ca38c024550a2f5d05943686a7fb67a7511a8265215ae0139d025a76e80a56b54c3b75ef407aeffbc62193d26508fee77415aca6b03ebd00cb171deb1a429db23e7ed55048cf1ba34c2d540fb29f7880aecee3ff4f05b3bc7546647b699679fed1d6703c7ce97590862ba573cc0f9a75d09dd2b47891a9651deee93552e351753c8db06c018a6cf10f47d4cb93e32d79bcb4390063dc57a8010b81001fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1039 : rowClaim false 1039 23 2020 :=
  checked _ _ _ _ 17 0x2421c5ced313fc4cdee74f94f83892ed05aebb021fd20b35e316dda309704b6becefb012a08b2471a8c89d68734d21d23101d52ba8935b8288ac1d3fe066d5c469ba6f180e1c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1049 : rowClaim false 1049 23 2001 :=
  checked _ _ _ _ 12 0x14d84cce6ce01408caae0910e840684fecc25d4eb4923f743a718b990847277afdb768eca41815feb1037250b75f55c17007ba08023de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1051 : rowClaim false 1051 23 1997 :=
  checked _ _ _ _ 60 0x2b2d905a28745672f7f93edef5e9e4874ca108c46ee1c5a82cb55988c094ed9fda0c6dea2b6e4a3b349cb13be713398da634c2294789e7b00185fa37110da55ec7b7aea9981a7559b2f4fe7cd51e840c40a8ca2aa88879845da1246874523efe0c9c32016c969e93a36e029377598df8781abe4bb97b79f2731844c6450b5126e15426a4685e87e988bd8d6abc9481d3a0af74b93a61b76f322d29c54bf5fdd22bb249e1ebccad2a1fed462cf42b4c2cf889bd9c3a4728ca7a0254ef361b4d466091cfe9efbd308659870741821c3cf58fdf8ac925b02af761143aac8096e956df2a96e8254f529fa62f61eece514408889182784c399a35d0b9bebce60b9898ab095004b0e20f4609f822451650d6528509327ff0f28972729d0b313af16ca00bb3736adaa3361214b9c1e026bd37ff0058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1061 : rowClaim false 1061 23 1978 :=
  checked _ _ _ _ 73 0x1da503ce74ab538be7516043f902e93d0f4a7fe5d3774aa7c362942b6d6dd9905875f32b41f1bc16773103845b219a48705b7d8a0843d7c136f6965de614bef6d2439e7acb1a838dd7c2b91b59eb4f5360e8fef6bbe5c976ce1bc07cc29f59be81417fa52ef55d93f6ac1c5adc43a4a86bfcb4f1f26c8abf25b8b0fa72098032309f367480a8cf3999f941fb76a3425162e624ad18fb86b47bc27ae6b7ee61cdc23f8255bd0be14e03226c4c360adabb7b135c97bf2928292872114cc2c86a9574027995d9753ddad3ec3f3b0008cc4262fda3a9679591b63d95bcf964cae229609acc245d7e2593bb415d5645d7d5ac2047135c85a2357f82e5113c61cb0f3b1e74bf31fa2f1edb7a3ac4edd7a50ad529e6f93c13ff04c5a19cc6d3e471decb8fd368fefeccf35e2bb9f478a483999c5085c33cbc2d69f6f029ee4ea2bc068774dfa4ecbc0f45fd3d9326a6b560427fe4d1ef60e8bd9923373bb4165d7c5d6effc7b772c64996c4511e36ea5486c3cfadf406dcc9b23003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1063 : rowClaim false 1063 23 1974 :=
  checked _ _ _ _ 28 0x1ae08b616ed9dd92f3416e5bac4380ee53677588037b3395fecf968efc21fc6d55697822109ebf28004a24c5ec5562f03920ac88640bf5d5a66f5bf6b21208700e8a4929796f72c17dfe773bd580fb929a115eebc60131d9a16155d50f9f912b75b4023ac4072c09f54ec2d64ca95dd1f027067bd79056947781001201a4c32620078370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1069 : rowClaim false 1069 23 1963 :=
  checked _ _ _ _ 56 0x25fa1690433c161b6d75513eca2a743067106b5c9830cadc2c5352e35efc176e9811085ca149e74c7cf5f9809d6709abf022d25c4c1cc2355b1a6509d3a96f2ae9c78ebe32daa66749a72050f52b4c617e6f2f21e3df7fd437ab4877d809fd70f181b4ff25b9fbbb31360150bf46682a6e7b23840c7a134c1d3ac44da1eba46ea5dabc21a73cc414bda344ab05b81b699d3cf872c5fdaf74e17a973a9e376bfce1520dc0d96d61943dc71d9e8fcf745e99a6ac7d634fc6797d86808ef7d460907d0aa26f0fa23c5bcea8bfd876804746a43e4da4c75dbbf3dc8643d9791d90d79cdc186354cfb86cc3306a2da67a2188f1c0675b1995f81025b77ff19484a74b3628ae119eeea86213d6e76fa2bf65d601f02cc194fd30fec51b81485e3d50082 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1087 : rowClaim false 1087 23 1931 :=
  checked _ _ _ _ 37 0x49a4aa7e73767064fd8cd15c3b0069a588f29814e505926a361616eb383e6655ea7a359b5175dae7ffcbb9ec239b6d46614c9b9c1dca1295df96edfdf460399ca75ed50585e122e45a8f67a604626d960c13a7d6f3a3af0dc19ee1b87f775d217f836ee78aeeb416940e738941c03b1c5fd3c7a8ca5d6b5b193563ba0a04e07e1561c80a34a1a0fec8d059aeda9de2425ad68538120f6a68768f62e0f44e635c4d2b138f71301444c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1091 : rowClaim false 1091 23 1923 :=
  checked _ _ _ _ 28 0x2ef8a8bf60c0d32ba16dd6307b3ef1b30d9ac4a63f9732213b61e0226cf0e94f70d1684d11c226fdbd44e46b2a497304c9ce0a051b5593d09d0786d5eda86d5019839cc8b4cf776ddfece30ac1a52733f6ffb2bcd412f9f789f18d7d67990dfb63e7597f8bb4b3220b497ffb603bf5e363f3b9de5bdbc08fd9c2a4fecf3400048751aeb00840a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1093 : rowClaim false 1093 23 1920 :=
  checked _ _ _ _ 101 0xae91425b3c5222e421af810549ba4f0cfa902a5a579da85a62ddd1f9d3de72dd75177c81fff9e5c7e5c348d723cfbd815e1c103e3dd59838e03669e1176c9c438cc5ec4216e84f8460956578700d480a66f8193b613d230c3aeb919e2f5028bf585abce1e14c8775c39784ececa0ee5ff59bb29f4c5207bc7e481157a6d0929262aa2b9c414ee6b6767d60fda972a76048bb49210225c1aa2e5e40c0bfd4476654028fbf213f15040ae240de7492288d1f9ff1cee8a3d9edfcd3217f6c6c14d2edc6614bc7ff57095479f80bc374a54ea14e809ec43c1dfaf0a50e0541956eda425e27f2a190469452fbab7777157b95b815edff7d43fc1eb3655ae77f2b5ff3f9dc3df8f61289fbb8d1d22d2e8144107e4f3c68f23c23a7a989327f1101eb0cdda6771e97247c5d7447f54f5f96b494eca0ae2df7290c60d5d6bf0bcdeb11714ea005bb80989acef17a980a8bc382870aa9c31186b1aa25509a931a69130fce050384e55ef4c507f24d98744547cb861a0f3178cc27e9910eeab975e540489f57071c4d0491e1290dfe1b4799af50b5a916abdf8539e5c88bacf842d52f9e1446f72257b58f99f4eaeea0a4ce82133174da098bb72059e0183b56621ccb2959b7aa4d2872e552f1e17d7b556242431992e63e202c1709ebb94900b3082f7fd34d2ef460fb06ae49348c0f27d800b76d6f612fff42b3b334fd097a76f1e2da09d5f4885752920eb713d4a1198409e3b0094 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1097 : rowClaim false 1097 23 1913 :=
  checked _ _ _ _ 38 0x42f8fa4f1de7592759fecd3904d6069f45692a3fca434be42ab05d2c047e344edb9d997410b32d435f9e9dd343f55e9d66d7c03f3f61e2d1e355908b77600922b02fa3d42429beb3e4770bb5d4a54e179bcd2881eaf983a806a5fe8468a8f4f27da9c714ee599a0f8ce7e7c1ca562ca17ba4670b4391e8fc385c25384032567a6e478fe436a0308f98cc2b653ba2425086e4420354416dc405e797b2e4577536ef2ec42b10aa830821bedda6fdc7cc1ee45f02b4b3adf00a5274dc6a503ec60075 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1103 : rowClaim false 1103 23 1903 :=
  checked _ _ _ _ 13 0xf1c52866a59e9f7215fe967307a5c553cfcd4ef26f9b638589b33e3dbb7d9f0897bcbc862dd6b925fb53e7703d1dc08a0144ab3ae00483914200181102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1109 : rowClaim false 1109 23 1892 :=
  checked _ _ _ _ 14 0x3a303dc1892c1256e7781f78492d88471d93557ba15c5991c73dc5da4a09702a31aa0d1ab382d55b9011ef3149cc5e35c29cb7287a67bbe82cdc314a2d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1117 : rowClaim false 1117 23 1879 :=
  checked _ _ _ _ 96 0xa0f932878e57d25e1986a6d71fe3343e4cfb4568a89bf8faee31439535effe44d62d73f682267e3be431fefee2b22cec87f8d43cce684bc061f3318b66226f83d1a6eab14c87bc19332a3365b2133c6ccd00148383b8c8bf20f444717cc5c3bc3bd3f30d75131cdcda5fe3e1d47224ae1947d6c70cc1b596c0af09f41488325d0787b7a3c7541b0fdfc7d602ddd1f2a718360ca0812c81e83dcf735382138489a3b1b8ae8d7f5f30916eea373ae8705997957337acc17530cb6bc0174e2c89bcc57441a686bf07dd224c82831f90f3af322e64d3643901a7a319b086702c88297715a08e2fa45db67dcecfb235218c6d1be6d7d7c01f4f1a63ec1aa9d49c1639f313806a29b60e8b4e7f4e33071a1f2f3feca3f7994da48643fda7e5b5c03a853fb7eeaefbe13fdf0e720d3864f687ab10a89c7da7403413bdd8b551bede46561293e13263811ac456c28e6848b873765b7c9bb0ddb44ee8cdf8b5d25853e5292d81d613ca5645fd8c77f40e286e2b0a337b2ab730bf7b6317b2a494f6aae4a088410efbde469102ca3b7369ce8ae08cc367977dcbc5ac3e45271e0962de7b5aed9e5593c7a60d32ffb82924063713f53adfbf07bf03c69d5569c64b93df9de42990a20373f32a134cdee31c0a5ed7fabfc3bf2c777895b3db6ee23dfe8cb4daa1204821efb81a1263ea72a0a2a1e026bd37ff0058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1123 : rowClaim false 1123 23 1869 :=
  checked _ _ _ _ 35 0x25a4178aa9d64b234a5e06917ffe63beacbf81d568afeb141e5165878af05f6a4cf407cd1b568b7018bf7919ad97677f51228d499f42daed64b6b54c64f78300ffce9915cad703edbfa76cbc7ab549be896442a91bfc75803d758401e3c4f1cb91cf2d0485a65e6f120e3b096a18b60d0da6b65a9f6f77100645bb81ee486c0c9cb5f3447e5bfd317eee6afb58f75fbb8ae29a9d1300227a02bc6071c15fe43e63275a1d98b6dce731809630d61001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1129 : rowClaim false 1129 23 1859 :=
  checked _ _ _ _ 59 0x1089150ea1a90d2d7575cfd706b9af7db3c1f75fdaa893dd68e1c2abe758a3a0b7ac54f74142d53d593cae5a4774b8ad1340fd3523f36bb4e98fe087636e5bcffc44db7aa6d64e3d78da8228489e38edfc5c381d15a2f205abe5b1f430a298fef25a11b5314bcde73bc2e1e738a19de89ead24d76662028e83cdb444a9e5c2307af343790e7f7541453ec4ef5fe233981227aaa841287bf06f33ea28d47d360b496fb481b64d39d77649d9d4d3fb2b285a0d686ce0314fb31cf56d49ce052242d1d439f77b4fa1a1d296585d5e9e4c74fa373b834882e43c1b369b51c96d2f723b99d5168f54f3267ebf6c31dd2e1ef987a1f47aa5ae470d39f61b5e34032de37798ea61c41056fb276bb6948649c1704146ed6aaf865db0dcfbf69171db086138f69ee15a0fdd4cd326887580e5caefd005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1151 : rowClaim false 1151 23 1823 :=
  checked _ _ _ _ 26 0x18973d7dfaff9533b95591ec792f6f8fe1fa00dd0ee99d1619afc1ed96295f772062025b112fe7145bebf2faaca9eab921a2d682c3ab7659394d3ea8b0997bb90df2d6f12f29ccb3cda8d8042df298d361477eeb257871dc9420877a3eaf3b6abb28e14c4c2c2a91819835699005a6686680144c43a800a40423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1153 : rowClaim false 1153 23 1820 :=
  checked _ _ _ _ 85 0x57947585114b126e3367d7b1a23dc59697a249724931eaebfce3f5b80663caac80e5c4d0e8ea4a55cf66626f422f16cce4fee261c6ca159efa8d320d691e8c774fb92b33a44c172e0ef7162fb40cc866bd822f3d0d1e0cf4881daad4b6ab19c4916913da40987cf723ba631918ee2f62a65fd8edc43a7e587fd83849aea8524c9b7dec4fb60ae92aa68f26bd4d83889570a0ae7b031fd15def6fb911f6e21a5ce9f1d8deb611c1808065df121da168cc3d7259c9dc7146cdfd4ac4da04126b0a5ee4a85c717d0f2634cd25b791f9e1c6119097e76b5aace2f579877d599ee9797228aa9bbf1fd1e0cba857e423524e9207c6a86531aeb3fa170c5a58c99837339a3f452a00fe2067a2efa69d4002a7fca6dc8353950653b2719e0e2e23f5ee1722e3fe16a2f8eafea0f6e6c9c894ad591ed0aff151ddbc6d55e8294009551e1443843637bd632427b58e437956ded3809d6fc762ffa622807a53c7705e8f9156bfc568353fb7d5eb266e49b00c7148909a328c26401ad428b16de9899a82acf9786a13ba34cd710a60cac5d27222b72e0e8828a5a413d47c9f00bc08b6d65171de807009b7e26f170c314d12baf238d9d470746cd7cce7eb026b9a0bbb8c900be (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1163 : rowClaim false 1163 23 1804 :=
  checked _ _ _ _ 19 0x9c8abc85724070a57626838560e02451b3d0ab2bb7a580a230fa131f5c0860d833a9708fa8d257affe8cc8784d743e1310e312143bca758dfbed84aecbb37882e917a9aa8967964649d71e94c5996f7ead09018652947003c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1171 : rowClaim false 1171 23 1792 :=
  checked _ _ _ _ 55 0x1b16a99f15348f9391099fc8ffe568b0bd49ed0db5a54341b85e94a19a2e3e70ed5bf96b4d376f633fd714f841658ae079c4265e760f9927bafc00370cbd47ccc1ee83beb15c430fb5feeeebfe6f94b3dc5694937d38e292d528dfb761827dc570dde3e1cfcbab7c2ea0d9cdd24a6f472425440cad2acc626cb1dfb0fe4b78f5aacf67e41bb983e42113a28ceb1ea629a4296294526e1f32594ece6ce6bdd676d1a20be200b7b8fd3a3e4f892dff48e2fc242f211c79d84ef3fa65dbe7e870f7888ee9445862baf77419a66d45c4a4b44ecb73a1971b1b448cae40a679c1d669c09727dd8a91ea6091d8cccf01a2b741af0e86f723d55febbfdbca9f96898d05c9951728d81c2a73171f4841ed2528f2d682701fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1181 : rowClaim false 1181 23 1777 :=
  checked _ _ _ _ 75 0x4f95bb49675819639830954556939d1b5bb1bdce4c747a7a080982b9fc7e033c4661fb18c1ee9a84331518fd28a56971c9bd1d5ad6b1683be96d34c78b4ae74836f5f3426abf138e4316d806108e5282a04dc8b585a1dce4b09b004bae1e09484e02e6f7ee7a2bada94d4ba0dab69aeb6eae1470658f287973b2ca9fc20510ea81b49af4a463b62827a30e3e7f35715c7c25cf35e672de6be080d7f582d375bb5602b4b6ae3ff5ebedf8159c2fa21d8a424ec56ebea52fe0d4fa321b9b139252d6410eb6d997d65898e2b33e797abd73c47eaa81970095ffa70075064b6de57c02035f231d2155cbdbc3dc4b013de562525abb792714dae0d516e0fed57083cfa547158199eaf4af483f8216836a20373aa582d306375e42aba778414084a18351e1c8a561ae590959bbd83d53b4903ff760fca1a1c7078adf78198f73dc58f343bc97845bf7ee81e0acbf059dd78e0f96fa909a0b6094f4be4db5245561ac4792c62b7e5496361a78a7344c21e6a207ce74118b1be4dd167767ffcf04edc9b23003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1187 : rowClaim false 1187 23 1768 :=
  checked _ _ _ _ 27 0xb706b7a41395e22b32d42888d2fc6a099cdb4839d7ee9091e8524831b827bd745c871aff05d8ee7f204bc801b8f326318682487af78511795e6004cd8f44a5f359f509b924ea3ba653c85d69bf7f51df0e40a220f0ff7764c6f68c09ee6488640f6802b07feb2a2184c370ed12b4978ae70842379c726c8731816ddea0300420a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1193 : rowClaim false 1193 23 1759 :=
  checked _ _ _ _ 39 0xe5b02f9ec4226519fb9a105b560ffeeb63f6e6ac5f8d28cddbc146932853e828f27a4b82933fd6f492011b2da5efe0d71ccb23a34a0247b4090975b77fe0e9e50651373b820e27212123dd1bbfd1c7cb7e657696744ec0a965fb84dfbd65a76a49d981af2b19cf469746eec64389929b04254756eed7a77a1e746c1fa3cec9e9ca37a4b6a87ccd6175d39d42e7f34e4426c6d8621bc66239e4fd676cbf7688331e611ad443650b80fcd5ed84be306b9062b1ba959dc14ff683b3a666a807ee20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1201 : rowClaim false 1201 23 1747 :=
  checked _ _ _ _ 125 0x99badf12d4e2dc4e1c3db11097b663346f79065f9e89948edff1dbb52538108a376c1fb80dc2a818d845e31d55895017f211d04d87fd9355ef4e60f957ecdddf4b10a11216ef0f665ec7a017db341c172f9b01b785bf1e96fa789b2645d7924505e505a1bb1b4984891aaea32f4b28d6c9d5dd806916ddbd8f9bfcc0d7b5dbd30502fdd4194096591b55dbc4df2071d20fdefcfdc89e2212d58cc6e86b627e6f85645d813361f9ce65210bc0f8817de53841371875721d83f038f9f64a0837d454187f8315d06fa67e03f24d803304428d5ed6db532a555798788970973fb6a83765696bdafc174ff902dd6605c629ed7ce96b16249e53980e052101e47b5d9f38108c6b6b3676c5e86212a289cd2c0a93a503d2438b22f43337068b0ec97acd85b2bf4eb6a3eb26cbd3cf26b453635b6c44826ba6a346885164973d9928ed34cca76a6e06de430e23f6c80a74c12a103212c0915f30af4795bd11eeb322c8605ba5f720f4de5d5cb5a398803d41d8edb84787ae9a20548a671923e36912841cac0537d1d95648dc4b4b87bedc9b5cd7c405a118af1a8da1b4b84b8a540609eff8d5c4c20e7832b082b9b9ee0e822c96b5e1853234f35e00ea12a54b3e8e4bec323f5458af7bf0bcadee334acf2bc657ec80f843cdf0b9ca35602633eb17e56caff210819e4e85591977f9d58e491f4838e5e7db2fd3f320cb1e0fefae8e39571aab58bce700a358e852e863f6e1e8c5764fbb9976803ff5cf918afa7ac45abc212dadec3e3adf310f38f77f90596eaa66964497191e22ec616608c2fa5724b9d11575bddbb63b210235b92bbf621088a67ddebb06c6e3aca766a4523395598a84b8364250eea39a3b8d73ad0e0791eb4225e0bda3a8002372b8d6a2887dd80f783f65eeec8eff898f0a71e159a040424e5d8730577cb5d02ca (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1213 : rowClaim false 1213 23 1730 :=
  checked _ _ _ _ 66 0x5ae698bcd9f30b7e3bcf41aac59559e97bae0465aea49b02d7d04d294c6491cd26717ec17a8141929ac0104063588e59b4eec7de9f085e4eefb6f680e4f30c627974d53d08e13d27762b22c5a42eec98dd20995515957b3fd67d28c9e9b6a79c10b2559c96b05f5896f959b85f9922ed0046f2718a6d4af91776866ba8d24924a99c4e6e42d22fd7c9bcc0832ac32273039153c695f3116007640887483762a6ed67c775fe30b36805b57808481e87fe434584d45f4a223cb73baa30b00eefd85475e54c41cd121d09f86cdee12cdb6c28cf85d558e2defdb199a4f0a85a1c6d0628731cb83eef95ae2d662c6dd6d0ad3b20fd4eb3c84ac438932fa0028cc28503436f57ed74cbd0bac37557aace6b301ad7b3567b965898ae3a20cf7184f60a14a9899bbb21ae5ae288e501d4c4939af816219e687cb40bfa7bf551bd540fa473d21777c910242387a70521649af53f0078 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1217 : rowClaim false 1217 23 1724 :=
  checked _ _ _ _ 29 0x42d11da3cbcea228fcf930f1cfa31273f67ffd5dabc561c2a95c65d94bce914c38de89185abe772082fd1a084e379aa1e63675a56dcc9f699ea49b88b12ca562c997cf0521621e8695575026052e78efd5abbb80acedac45caceb27d69462286ef2d89b64fddce892eaf7f3c67a6886ca747e1b9dfd84c2bfafdaf6dd74ed9410697f820af486e743e2b815ede663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1223 : rowClaim false 1223 23 1716 :=
  checked _ _ _ _ 15 0x129d39d85d63a64f0ca511e6004ec3804bd1ae4dd78a0ae80e8a300c83054d54484ac971e0fd77cec9a2f9a6963c37b93c7c1638e50fda5aa11038777c920064370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1229 : rowClaim false 1229 23 1707 :=
  checked _ _ _ _ 14 0xcdaaef92990465eae6ff8ca9bd679e757db8ee4be4c1ba8ae9d38b7a25219b40d9745d66cca47bfc423a9c5f2740b59eed9e71c8aadccb3b043c44fc22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1231 : rowClaim false 1231 23 1705 :=
  checked _ _ _ _ 21 0x21896348f105cb8ab1feb52fd21afd5faf4718193e19c59df351f3c1fa4f284a572bbbdf4b0df7e73f35b30825a5c933f8299cb44f937370059c8ed63c2772dfdeb415aa02fa96b749145598280e9dea2d00423d83d800c09c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1237 : rowClaim false 1237 23 1696 :=
  checked _ _ _ _ 95 0x123a72beb8898bfa3e0f4289ab465408b25540ef90ac8b830a02258a13b2f28afd2ba52d8eaa9db6ef9f8da50a77901bb6e8c2210dbf6555931b70995114efb0c8ba549554c31f98bd5fe3a6dd68e3020a16ace132bda518ba3458a70cacfaf9acc4d4f69e8aadcdfbf8ad98c177718d83546ae747f4107fffe4f4e6a0afbd93c6eeeae730dcf92239b652d13ebe5bcdf66ac249cf78c1711f4bff60166e6de0e431146a922b2f8a60f16b151cc8d4b380b190cecd206f14e49edcadaa0b16bfed2c9a6f81a19ac074f4af4faa6b4f9d3ddba287b9f0a03149164652a4aa20e55275ed9ffaecc914088bda0a4d2bd10b4b57bf79e12f6d29eced83003c0129ed79e04a9cee943f3819f14e5afb11d0b005c2f7b1587571eb2415ab6dd82d7abd7ff80f4a210749872c4e70600e43932845c05d0d88681f0cab27d4589c9db88a728e13bc4be5e2711d9c363417377bf84e5912aff67f9b9fe3f02217b65d9440585df956a37e9431613ab55a5dec58657b722c23b2dc8486552d14570b1130df853127bef69de57374d70ffcb0426d4ca2bac915437275ead4ecd3bdd811b8b383acbe53369d5e0df7a758c0ec1632b0c3a705a51b9c085d5e8db7003fe093e75641dcf5068d91fe973a13863ab562d5d30bf0cc7c1b1d35187131cb2debe99ab32cde468e909da8dbaca7f5005a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1249 : rowClaim false 1249 23 1680 :=
  checked _ _ _ _ 37 0xd1d1cedfc11e7c3ad282eb727968e2143ed7daad14b088ac7772f4ca1dd3087dcf6233e2075680a470a9a16abbee404ea38b21d597556f142d10d62f3c996794fc692f4bf205c89f99e2541eb4bb886f871b589a08fe0278d6bdfa795221ee5c5961572ee1f4a0f574db27b66fa1f1ca263933bdf7814d8f246bdf3182df0edc7b84cfdb6cdfd7837de097df895c1e575e14ed4d008538e81551150e69e56b8692809854f6b9bc6b85396e50f4cf906dcdac628972e18069e20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1259 : rowClaim false 1259 23 1667 :=
  checked _ _ _ _ 15 0x19ba6a8aa38a372e3253b33a2ce020c7125c9733ccf8a9fda427879b73fe8379344b046587e9af32348977a2d4655594a19da0654944b98d982aca23ee810e74565001e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1277 : rowClaim false 1277 23 1643 :=
  checked _ _ _ _ 50 0x4e9f7bb7eaf4e2b3aedf86700e3d3bf8daa1608d62ae1b8dcd415402677d976b949481a595ada184945b1ce61319d0ba2cc58bba227b6259c62e606884397579f71f1eff8a5bf74c29e210ef9740a8740a3484bc164f6160af482b780d9a3a85c31fde61f3aa811198de3041f9b7c75a0ae9f1836134aa2b86026b19c92cbed1be6ac56824137ba1a309bc3a29a5b50b66483a97c94a8677bec4e9011be6460cac4eddbdb083990a19f54cddd7f46709afe23037ce3d27ac1c77b539f9ad0f8214125619a6bc05f269ab7944a1dc7622517a3b787d65779b4355360cd9888a35908c40857821f10a12c2837b384c62c05b96e94ae3b4201d9620d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1279 : rowClaim false 1279 23 1640 :=
  checked _ _ _ _ 30 0x51e6769eb11355a33786e7726ea92b71d8840243ebaa62cee3c386c46648aba435152b0054e9c71c7145c5d890a46d83a0d6daed1d081e23e9bd90d263d8978f181121b329be16dd356101ed91b1b1600411e3c29ce30647f8f3563f52bdfe0e96071a0d79dc43c1b2c44a9f025f2c59b44d9f0c3722725f13d03b844f8cf30c50f3e7e810812cc1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1283 : rowClaim false 1283 23 1635 :=
  checked _ _ _ _ 23 0x7c40b6407bd4831a202ee48c630980cb9547b2e8e37f1c917fb13d96634302fc76182943dabc14cd137364c8a93e04be490c986bc44cdc372b68f67732c89ed34fc3a9855e0deee1b008e2220f535c13be720106d8c2c1a6768e8755c26b6108e4486565832b73b6b010e559e300240a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1289 : rowClaim false 1289 23 1628 :=
  checked _ _ _ _ 15 0x7dc0df6745bc16ba7f2b0b8e0c9c6bfdbd2c2768223c80fc665ab15a8a05229a71fc57dd34760d221b1c33b74d25d38c7b17099a49b1d35c8bfe1434817c6a2a433a22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1291 : rowClaim false 1291 23 1625 :=
  checked _ _ _ _ 34 0x140c4c6575698432b8030ac50bd4fdc53efbe743f51a0c0969660b26c1ddd672e58ae8ff5ed680fd7628b02d6ff9645daf6e4b345cc147ceb9d6175ec78c2034b269bf0b8cbb2aa53eb32d289f974a1e1b4f7d3946828482d6c3d3eba90acb9981b5d7be58f77263db21fe70a9ae317ccbd5d6706586f9da0905e696178aa0dbde5ac49ae02f816dcfe4b4e659ff9ee0c8809acb697d4bc251b0ce7f1911d38d4531d4c81c260d5b0012 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1297 : rowClaim false 1297 23 1618 :=
  checked _ _ _ _ 100 0x1047ea87318525b8a6b22ea9ea258bb4048c1a49012d55ae857d1c0106eb97d16c3de4c2b27c69b6389345c1860cb56d3470a95efb72ad8409a2a451e4fac4b0afa1b144ed7c6bbb7afcf0de401ccae34dd35c0b635e8f86691d4a83186af566abd19b6e04d71fd3bc44fcde2a907d8be868a452431c76926dd55e1c4dabc2268ca0167c58201e3e92330cb192204adccf342d76f3fcbf3cc517111f3989146bd354f43dba461ae650118c6096aa386923bdc5d325afed979545bf7b087c21b4499cc0fe4c5647ae0951f04b0ee72fb6626aa16b421b4fec5fec8ec8c8745d8ea1d454c1c1b1d21a2c3f132cdf7a90aa9de60e903fd9cd0ed34b43ebc8d5ecc783805627fb5abd95101e532b8b2146c93e32a38618a154aa6b34434169fbcea5d92929fa703522d2899e343a0369980d0d2b8e788ef142420e02c592eba6fa98bb3eb11a5e1e1e8e9d0f71dd7d0a714013b11a87912eb6dc0022cfd253e2e334ca4bb981f25b5a3e8711480985715e5721563d11107b921d6089a2c1834ae28cb77e2db1a83fe7f6d66dddecd6ed336fa1a057e24b8ac17d36db23a2ca41e1ca691e828de05215fe46658e1d5d7bbb335c172d655110151447fdfd26c4148453a7c94d4b563656fe4469cf4e124202ecd931738a5d95a87bd21f0e80e925ccbc296b934d4934c508814c9f71e5dba89362ce4bed4914169b51bba1ad37902a67ae28063dc57a8010b81001fc89002e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1301 : rowClaim false 1301 23 1613 :=
  checked _ _ _ _ 37 0xd19b1dbae3cada886e0a054b364d651a5350591c0c007c8768f80d5562087bedcd976c18991ecccee9bbf8747e6c8777c702301872577a9c12dcb8b14ca42d58626a4efa87c751d2726ccf49b1ddbb80979f05bac7e8be5ba23bfb998c5031df245786610eb0b1712f0782eb50c70cea5aa92deba5eab0f7f58aa7e50e4c24ab5305012ca7f076021a0490c8fe2cfca1b398fad5ee51f257652d73d3cdc0afd5200977635fb8e5ae284bac64dad590caf654e98134de663000e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1303 : rowClaim false 1303 23 1610 :=
  checked _ _ _ _ 29 0x178e1e420f91dcf562b92a917bfb09fc5df3ed8eb9d76422c32c1954d7e7fab456ae66da8c3c8f833388e75ac8140266b8c0cd1c21ba2944ba83fb49e0d0a850881eaf0fc1f382e640a1dac7297c7bd42b4247955a5e0525041701681a47d7706c398620fda735bb01703fc2d2ea36b82f0832abfd33d0a9d4bebf34d7c1955fc68e02d0c32620078370da00281102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1307 : rowClaim false 1307 23 1605 :=
  checked _ _ _ _ 27 0x43ccd983c801464bdb5adadcdbd770861412fceb8a7e60dd0f4f17d2fc941dae5dc6fed4a55104c6ce5c43c1383732a3ad5c4a970b33a9865b8c6e666101cce42ffb392ed2aa1f626d7b0847c26472aa3bdf6eac438494a41b31305c97a785840577b5300722ca39632e6a45cbdba17002554cdfd4f3f2a504c96b38763cdf3d005a0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1319 : rowClaim false 1319 23 1591 :=
  checked _ _ _ _ 11 0x2ee19151c7f9edc5f257c261edf10b704104cc2994c667d7cdcfd7dc7f53511f82a464bdc8096c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1321 : rowClaim false 1321 23 1588 :=
  checked _ _ _ _ 156 0x135c32767c8022d184600a2d5616fed455b59b01895be6750b6fad1a4959f0c1712a3dcdd72c5134f386476a7a95204667bac4c76d416d40d274ee129bb205f7793ca488832926951e5e24152e094cc189168786253b5fe6e64933485e40741dc75c0536a1bf5cb5f250bde21451de823970e678f202978c62eff6770168d077798d138b1acf37c0f0746a92150d2e2004c9de66a6096b9f2bb75613d32317acaa3a3fb3ee2d3700a0a394a1232e359a96ba650420ba60d884c07230a610b888d2b49beb884b6c557412dac0bf51ac3799a273fc4d16393b5ee3e91a94f4f44b414c8cdad806e73d652332e5226d1f3f0392a9a543e13f0f009771ecc456880a436b0ebbf6efb790053fcdd1b0e0a6ac96e2407c2293427c5b45e736e29e2133ec271993021d342304402f838f3be79294f115b3619da3a56513b6e5651be2b8954b1ffdc0f6afa31e8c4891e90d726719372adb7983234f57288f56ac59620b188e1cbbaedaf47b57fbb4c97301ba8c798f25c0d5bc6fb84ba9a7283b989d3095ec5dc011977017414fd9cd80868a0c54b1ea714488c48c5976729ee031e0956ff6775d971042fd02ec366fa3bd78cd38868964f9afb7d32b1541dff77524c3c2975068b87a52f7e373f2bbdd5325010a18342438798f58b6b6926e7bb0238a48d7e64d3963cead61fadba14668425153084aeade08c5548f86d52aff633af8e7c9452077226924233e288dda6f82951029c89ceb3958b4a532e03a2e3f061339c3065e7e723185f0f66fa9190c23828247ea55eee77df3be5c8ca6b2e0a4bb6f6b49b1f32f34e48a45c21ca282439465aab19cb1876727ed6282df845864d7d6cb930d53be9e7e604a06a6430b0ba73daa9d6eeb1eadf86480abcbb0dfd0267adffbc18642e13231911c31b14869952b6622a72327537f473b4a2188ac3e903b11dc9d4505d23b2d30b75a2513de69d099e7cd9c6cc36ba7950ae5d94efcb31bc3f35db61d471e1eae736d48a60be5ed98a18b91603be213756e561d16cdfe8a33ae1b83eb60e391524082ff1bbf98521fcf58bec8f1c84296839c1b101793c132f4d793616eddc2dcc1945dbcd07987e72dd2f69dc9e1bee97eb3fabcd38ecc03c491c9c6f2732aefc354b2ecb42bc57201fc113de86c1108c824a1ec5b4563dd38ef01f8 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1327 : rowClaim false 1327 23 1581 :=
  checked _ _ _ _ 25 0x13854ddd9398a8a3a5dc8de3e21ff0c1fbc45b184924bfdcc979ce79ab11d8a601bc51afe26246e434152e56840890822e390fb705e67c4f32dc6f3232d8cb2aa227f37a085de4213d7d6ba507dc1ec6227d9099710af3c4d61080f73f5ae99328d6c6c8b53f343d02764c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1361 : rowClaim false 1361 23 1542 :=
  checked _ _ _ _ 49 0x38a8b9d5c6cbfddafdbf9758c916d4dc7700e7d2c7794569fe5b2ac67a23e1044a31009724617cf41e1bb513658531aefeeddb9d5c0d4f992314f432c436839902858576f8e15999d0f99c049ac7ca013121b2e5285233cdd5c519dfca31caeddef246291012dc3fc41c6e34237ba1407a7e304ea26a19bf3d0e2aaea7dddc2e44e63ce6792dff45f79b833b65f130a48e357bcdb17c5605b9b3a92d10b306316235fbf43b32895125d2789670768b23f6dd72d551007e86ba27761a7609bcf28ca15f46e068d8c348104a21ac65810631f64c71390ea064d1db0e7db04f1a2dd08d8874588e2ffcb95ab338c7547c58d78c7a80bde20d9002a (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1367 : rowClaim false 1367 23 1535 :=
  checked _ _ _ _ 17 0x194b2794c1f723342d6154370a0c874c702d40eb7167b2da717b328ec72b9d016e57ee2c3b536642ef8d71b1b5ac8a0796dd2b333bbdd245c340f01bd5999daacd8e4c78987a42b9010f33f7e003c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1373 : rowClaim false 1373 23 1528 :=
  checked _ _ _ _ 35 0x3067a48a6c6e5621e0d27bc13efba120c2a1218c4499817397e014d011060533fb28c75bfa7aef20d2a7b4cc19aaed0f77a5642eb4b21afe5e888fe188429bc2bd01db3ef9084082e9b3b252c5f6fd5f64d562c3936b8867b372a72ae4bb0cbb86983fd4ca19f7dbff97c433e23474a8f2ae0a04242a15718f7f5db03c5077c18f7c3251bfeee2741231413c6d7002b540119612c9bc03a43b32a9b224cd41b07ccca58600b4b71d20018611ef0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1381 : rowClaim false 1381 23 1519 :=
  checked _ _ _ _ 91 0xf5339c13b049d575bf55c4f70bbed8257399ce9b626521063e35a0cd1fc30a92716d8784fa7c19f737f8db1c9ef14e7663fc2a167864f2544a512d9c0308ecb4e5c9df5d7aa5f5cdc133beeccdccb34119abb230c4dc744af0a97cfe3ce32fe8140591b2e02d7f6ca8c62b27fe73bbb85ac7c58ea1df1a24badda4812b4e49cdd047759709689520f8342f7c645b36b2ff89e4b53a0b7c7ee9379dcefa5be93112f12626c09f9cac0b7676f09499c6830cb1f045a71a7aaf5ede1d1ff490afde2c6baf0864b2d604b31da16c5d1c3b5fc1a9c471f5d0572e21a032ac6ac29a85ea15948392b1a9f82f4220101165b77ffb4a3da3e4f8b33da20c26420cf4ba66eb038d73036a1cf6b96dd3b98add835ce4a01c0843bef82221414f93757d06e88ac3651d2c64da4cb67a437868e66ea5e63d7425184ac9e9d68d655da481029b3551731c8b18c22c5dc3fbb9e335ce59f5e1e7d81fc1a11978927f0957bb719d6ad3ff666cea9a2d0f0fdcd770e7bc36f5b8a69498435caaa15e8a6ed6a422fe19b9cb68bca172259b553551ca2da133d48af26b6d4824ea7a94de2dc99165e725c1cf3b03a0a9a605d26062d26a6ce21a9c63cfaace7903f3a9f0e8cf8605a55b295129c5ccf133ebadbe10072917de5c194f2e68205afd37ff0058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1399 : rowClaim false 1399 23 1500 :=
  checked _ _ _ _ 23 0xa6c9df3af645cde3c424fe18148fd26dbb70d15057b4fa4e61028a07cb7db51e4b6b7cb3205959ee75572dfec819edb873b4330ae7fd122013432d69de805f1a8ffc3f93f3ea52039776d3c489e40f6b64fb5e40cc2202b69fde4a052a8c3f91c00780afc1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1409 : rowClaim false 1409 23 1489 :=
  checked _ _ _ _ 13 0x522830f5135e74a5a9eac992e402381d59944f8ac6431d835662f707c2548211904eb8277b8b571ad93c88bb9f47bd341851001bfde46be22d7c804fda5c9001e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1423 : rowClaim false 1423 23 1474 :=
  checked _ _ _ _ 27 0xd44021c935dd69adc3dadc4119bea874858502dfba9e3bfe586bd6cdcb8f15b383b6c44f96b5f25f27d709861a9c04d1873009990d71dd7801aaacae9f8073f4c5123a604823c118f2e06f7a3766a8722791e3ef3ce97399d5f540cadb3197cc9eb93407ddd819463ff89542c4916dadbad02524c9ed802409c1e800640423a00201102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1427 : rowClaim false 1427 23 1470 :=
  checked _ _ _ _ 15 0x146de8a31375d983fa114fdd122f34fb61e34124a77e3fa646b4976ee904c492870def8f0d91e8773d49b62337e3617631d0eb1e7d74dca59d45557356601b9559e300240a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1429 : rowClaim false 1429 23 1468 :=
  checked _ _ _ _ 42 0x1a863accbd086340ab89714f9c7c746e29a211d58d76756678174dabb11a964aa73db51f0616676626a8ffc783b3a1b98d96054a3aa776a1f6721c26403af41c53d25e2b8dc4152bf17f89ce0ec1b9e6a9b1fa6f8a855a13b2d1f847f17ac467fc1c023f789ee12335f21f3fcc06a575d28c624c6410cd148be263ba9d553bd31b0ffb13328dc0107b41f93dd0ccfa6bbc89a469974385bcd5bb70f9f885ede5e81cce87d964d9e5da5e042a19bc556adcce7b8a085cc2fc4e1ba643193fd5c253967091c542f352276193ebe69553ff205042245153018c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1433 : rowClaim false 1433 23 1464 :=
  checked _ _ _ _ 45 0x3fa66700d2bb7ab2e7d678076457730f6bb3a5a5f0b477f4f2d06375acf47d2a3601dcf86ac0e7f978cbf551b96f95df6273258a0d568acdfedc0747008df2715aa53a87692b03b8f33b23f298fc4f89ab53286c2257bc0eeaa67d8f07422e7abc5fe179d7724b953143b4ddd2127671a21568ebaf3b543bc2f1908c8548e8396cf8614aae5662222de6f3ee4382c67a6b2ca59da7cb119cb342b403d69f82a73b38c178d147bbed164862b935d54e002f046a4135041f2361ef71556ebd7712797848053e75dccf3ad41a798d93eb9994d67d2cbe408b6184c44e3ad80a4e0a390036 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1439 : rowClaim false 1439 23 1458 :=
  checked _ _ _ _ 18 0x1522462f0006b8c24271ed1c2f5fbd8290b84e1a54d40ecbc7e40afdcac30f7856cc52bbd3993a6622c5923a08d13d88071f27ee44c2896c9dcb786ebfa1e283de5e97b4c6b328ff28177c1e4900324d8ee00141102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem exponent_1447 : rowClaim false 1447 23 1450 :=
  checked _ _ _ _ 27 0x170dff859ffa0a14b33d5a8116abb97e253e1a273ebd0903355f7788334eb14940ed5e2cbaceba32658e9b8452560541df5ed39529c5f4f5d2a93c9a98f2799a65340c71f0935723f5cab192f2fefbc1ac603fa59c65e816bca181b3c991af9bc3d818019124490f5346d4954eed356cf43a2600fa9d5043924b9300b461ace003c1102f0008 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_23 : rowClaim true 23 1451 91181 :=
  checked _ _ _ _ 304 0x3495cb0d94ea45163895c54f597ce8668597b91f8977eeb56129c19ab3bbbd4b9f9568d6b44a8bc3062f5c8f8221554e05d7ec2aff8c5d680d5f809cbbe24acb656e93cf3f821bc69f247c2eec7ff20277d20197c332cf1776cc0b4e2972413f72665f509166060020f26e81e9ce975f093e223b938f8101e3c2ba227f73f79048d74331b1ebb71c688726c45d3616d12a67f3b529e2e7cb20feb862b98244c14938f7b372dfae2cd5ec159a7b0589f80a6f06dad7d872ef0bb5e9d33c13eb31a98be504c1d7e21f6a08a0465487d48b3c08c4a4d9b8afe957f251f3da06394f494f583e19989c5769eba3198dd0886f38aed345bcbe0b03f7ae0c2216297b057e1c5f0d7ae8b481564f346e3cef13b3327a6ad511d319b904e7904b00fa313c746f6012d5c5834828b183f35a2819394961689833e9915d9ab740c69392a6527e52cd17108acfc3a9cad8f0d51d8c62035be3bc2d9d33b58fc1e7cb9a3ab490affe2c5040c1cda40aa848c8b1a9d892ae9c66430619a6722bfef1b2489757be21644418a7870e9c03f8bff35c207f43002a2daa986e89cf0ff3b575a0139faca5a241139d8e381d15cec183fb5b86a7f4458e503b2b8ca47b88ffd457da66abcde6c11adf2b1ebf1c283544d089dd17e252f893ced8552b33ed88f14a8d789e342ba6c430b2018f081f73e0e6a560ea9302c002b8de3a79a08ed18696eb8a5ad900f9a01d7c3d2fbb1bbc87dd9472bf73bc594aae1a0a0f24832e94e135888615c7d0a85c246389f17879855748d5d9391f1e6549136ee7d690fb0b43483eeab36a14f1be4dc4d9cef7cc52d1e879e65ae11b472a135eb43acac2f8303a2e2b37020d32d6ce2c0b2d11fa3867b49ab1f3911bae27d0f4b016032d5e49da0fba1897c6cd8d6c60f2fea7a82443a098874e73664ac04652509db3c3432e87fd0b062405d8959634102e1f8c33cfddc87579ce969d740222d6772e829a397c13f1f09a4746ef44e8a634678a1f853669eae5bff8fad9c171e146a0baa1bb31fe46ed1a9b840cf465befe3c21d212fb5351e40e74c2f45fc264daa13bc39dbaa0f2e787927e9620a6fb3d2e0e50d7ba5d44c8fa1d51e2016e94dd9ffd44ebac0bc2ee6eb120c56a0b9de80e38eb820df22270d67f6c757f8bcfa279a156d0fdf0cd37e3d52623e3ffd5622e56e8c357f644ef204d7200cce94256466a63f35fb37ed6bebe926cf162af5f42565c3a2a54ac109f06fc36b96684c4e512fa48de6a2090f1b84872ca464194c0d1051dfe986ee1febea9b01d7a3255447cf0a403aaf6ee241c694c30b612b1637f9c3b3119f82d930b694e4cb32a9871e719fa7ef3f4cc58e42d215bba8383a334c5650844c53e7a0a9b576c4982bbda5eae2ef7161561a445e32aebbe86c832b170ae582c03d91ce490dade40fda863f279dfc83acad3418965db88c795b86689841908c7e5bbbb9b4a0042e94a1e6fae10291b01abf4ff7bd76963cc4cccd2582bde950f9fa92e7bc6500226bf4d39b65edbe2bf60a9c734ce5203d7eb8b6d50bda86c7143d36faa1b8b4254de08558def58afb9680dfd7e6ddac63a4aea9d82d8d73596b74c0f18c1789f0dcc6c75cfdeb24dbe40597897f1f3808399158ccf27ebdaa0aa188036ea674d3cf25f277668f20e1261f20a8e45c0d9bf84e9873811c48d8d34f0a7e87814039570a9ea2f42982750485c2b9d947ec85dfb48e00eaefdaa9a4113fc8c7cecf66bccd8013988939c3b2c98b9f5da23f76321531d14aaeed0c98ca8860e64d0d4b1381d5f97eb935d7db87c1e86b33a91e428eb9f9a211882055d749ca463eb82c6f8e78b527980b692809fe655c32c7fa5afbff081e6d8a333a5bae29ca2b5baa6d7271e4b1b2677c3a1f40b9df9f8f45051dc5a348a61ca42bd27997ef0ffe7efb01a7913b08bedfa527c46cd698f46ff2b897e11cfdef127fd2e091b3a8743148d71031dde02f4bfdae72783108ac111396797959611f7214ae9de34774963f157dc62dea46b1c001936c59839847faee6137d330750c92dff87cb4571d2904b09bd47d6327b982824d70332d5e0ce2a3939f6b6e2cf838cb24a340e1f22a509f105adfa5fb055164a880073189e09a077f345fbd0592032f83010c1fc1e12f35eaee4fdbb38abfdeb91fa0f6ef2afffc3c50c7d0797ff701cdd345f01b8be91ca53f88d853d866a7bf5dfe7838436ccdfdf0ed83a4cb40b7d8280662d6d3063e0ce154db7f0961ebd9b631163104f347fad39bfd114e7b4f3cb73d34bddbbd0c221d626a2e118cce1ac31a04b5500690a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_29 : rowClaim true 29 1451 72316 :=
  checked _ _ _ _ 333 0x155f8533f749b7db6cb8b9df52c5aaa15fc35671c4bd07507fb8ccd3b4d1f82dbd864888790b77bc13075278c3fec5f3869d9290975be5d77ec5af4de5995c3e899738595fcfcfa8abb45dbd04ed35e14cce477513081912eec210454a79c859b9ee94fdfb3503cba6e1e96ebeb15e36106a4b364cd7d5258b087f8075242d394d117655c80867fb6af86b484a03b9e5fe98fe8616fbaab0be8b8b1f921963de2176582d2a3f596a3982a73eeaa33bf68d55b7e885d0cd1f745e6522c0527608f2fd4a7ed52bf718236f656c36d085564a032f904e8d0a641a7a72e25dc554d80360db84a91b77cd77ec7c88c6b801e2482b52f2863307c0148012e8a8af80730a14577dc31bf742840da280a70046e1226d46cf42b8779a959bbbc3246f0ff5e27609f0258de00f92ccad2d25b2e180a61257b1047e1362ef95f596a1291f6a804a7922c5dbef9c50074b78342efc12f8f9bf830695a10394121da3ecae7cd9a3bc478116837357835506827efc023cabbdab1d5148e3cddc3898d5033968554741a7b162184b9e755d05b65f1616697f3a944430fa4316f245b9432396912954335ec7658f961d7722816012114a94c96733f3ae4d6c1543707de816ab09a4dc5609b4baffc8b90d2b13ce7381517e636cfbe5219222e6f390ec38273c1ab8c6eeda5baa484bf0fee6d7c8b27123de4395e96efc05ccb967a97ef6dcc078327dfe643a1aee7e597d7c582f6b5e21ca326aa01d8633600be5e6930e2ff93b5ff5faeaa659620c925cefe436d0f06e71d381191b830f7744739f517fa4ca0efe1122f32202e4fa133ea1263d78f4405767491ea24cb90beb3eef73f6f1a698ccd39ea9a319b7f74b2eace9fc2972b1e4e19b2a8629d48e9e2c150f94f60352bc4c307c586e79665ae91efc3ef241ab3ab6765acedfe6c61f0439c8774bf2e941b2253edacee395c5ac8d465c18f03ed26134f29ce4f6caa7ae5cbd45ff465387a9f15cc5e87088b557bc49134ca6e4699987bc92848a1f6598e7d1dbfbc342c603dbabeee3769fd5817d2435cfe4a3edf758b37f2f8a7df627d5b1495e1ffba77c5731bcbd3ea242e6e0a6510bd008ef7106fe737b49c43d3d0dce283bc3116b198f1f69e79e04e328ccc313ef933b75b948c7179980a2a4cf477d4aac2a9490cc2666ff4dcc3762b67cf992ad0540b206f782261a75357ec91fd0239e5d2b4fdbeed28781eadb600d47b3a9c64b05c5b740663a2cb85c7bfd21d4dcc8120d6899134811e1fa6ac86f9de6c1d977990d99250333cf9676fd255e3fa6f9c470d0283ade6ef483db570d105bd9c13b9b3990887ea371e0c53e1350f68539e88ef37fc4c3d34481c2675b70579f798ed17de3c621a1d6018620ede5ee4dde09d70d43f828a96263eee6caf5f68b5fe4df943f97970897deaaf65f94249567560a466a2373b5ca41fd0d05ed53ceb1ad1501733367abb9204bb337c0cc1b33547a09c169c299a040ebbbec007e9b96b9900b42ac2d829825c738b28125276140301c37be16ed7add0a7dbe07db796411117c6fda21803cf87fb6fffbe055b7eec86b27fb29630d51aaa8de390fd640c4face8e7fda6f337e27b1914a79cdac868a0757ed9613f30bd0cd8cd92c024a93c8f302fbe311069b496663a47b95581ce5f94a64982dd0e80f6b77b0f0184635fadf2a4ce4de7b77aa324cb1c411295356c49110eb642a9c2512bbf2ea2606f857a5b9c5ee73409f6b73bb42ce598d2715c39a61d180450ba4acc10ec42f900a7abf646b985d2b2cfd0b7a6bd31747b72c1aa5e6e2c585bc3f1a334d9c5e438f03c0c061973bd0a1922d9ffdc3f0e7f8303d501c56758cfe1b8b803c1321747251b3827209e090bb21762d2f5555ebef81e62c8b9245dec8243e79318ff623d4d5cb77a09f9351a74b0a533ae6d7cb2771e62ff0dd86e79a201776dd3720ea5acac4e98b8f6ce018c999fea6b1f46c8634dea6c843065c6da0fa62dcda46f559127b1ef9620a8987b1a050cab91eb45a6e8df58952a509575cce071161e33fd9b98d3224789e10aa99849d4a41c2e535bf6f4e6cf81b6b1ac78873c70424e73be91ebadc794a8dedf9f5b8bc0565f48347b57e9d6a31b3e1a3bb3b3ba2f87fdc0d7503f01098541176b023196b511b0f452eb2941e51770515daeee652d199387a1faae041e67332f3d44537a27ef9462ac5bdc21aa104f5b403df58b2eb71cdb150e576e26d6741c51c32041d5cec3c5cea5a30fd528627d5adf35d3ec167ddd9960d9608aa1967b44733513d8ce195632dd205dd0a65b43353ad7c8d2c11c13793cfbd48b4c4a7343fec06c5e295c876fc99f48f31bc783a202b66eb43fd16058826d1015ff030f3ab482ea4d0388d406cd83d76f91fd15a0a59b457606ce4b6906c35d83dc653431d813fdbc26f34c2f522498303fbffcd3fcea51f52eddac86005c93df7d19ba87a5d3860e2d37b8b60f65ff1ede15e97e9d341c9c14841a3a3cb92cec6d9a3835ce2c3587c18c7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_31 : rowClaim true 31 1451 67651 :=
  checked _ _ _ _ 370 0x77493852c876154a8180948a234274289c94f5336f78a8af33a6e3a50e85275ffa308c651901c8c3638b2afb4687ecb093cb389cb97252f9535409ddf9e9d342c8068e347dc648b513dc8d42278ab07c9e48cd3f3598670a5c9a13de6d70abc371f209e9beee56dc25aacf9a8659f71688237a50c91c7a67bdb8e7b34ac3740c80440746834eadd2d08dc5314975f52eb42c971faae8b9761380b83a29d7ef31c4cd977208d406ccbb6d376038582263dfc2af4f0a6afe0c8ca317f04f6adde861f80caaa542fb262989440e93c692fa3354cabbbf47bf351f0987fef1e8b013bc5249e91d8ded6bc93a8563040f593958e027f43c9cb63d073e6cbc3b7681683d6ff74dd6aab55e9f5eb21395cbdbd366f0da013670b46c92cfba78e210bc7820a129c7811b32260148b56a2dd35bb46c8c573a7c44aa042da8a4163fd0c69dc76e0327719737dde2c2026c84cddea0e437a3b012bab46ae3b0b2ae9629920f98ab9d893b7de7474ba9c9c44236878baebc3bd799f7a0956d1d6c5aa6a548d217b41263aa11701a7e5e9a78cf820e6aa7706560d7291c05f9b23fcfe73f7054899191c42d94f361de16eb09ce08ac2db888634b82ca7c22aad10c6c68a2c708c29208089cfa2f6ae8c31f47186781d9ddfba1d930bb90074942c32abc9e6e2cc6b12b4b33e5970b59e9659a05a83c8848598ec6d72cfb4f4274c3020a7c61b65cd7db1c7aa64599aea2ebaaa7a2b2d9055cb18beaf33a6fb04404743f475498012dc9e20ea64a2ec19f62753758fc804d8386adf76f2f6892ba34699e94491a257fe341738496237a5b17b74cbb9c008b06e76ab280d89242126d3b13601f5e80ab3a329d6771a0758c053f85445be4733a6482b920d362d469c8010a1d7aa34f4fa5281350e21c17c565ca69114198bb04aa94ae7b84eb91b1677510fe2da9394895945e977ff16ec6ebf2c3659db8f7452f15615aee387f2e933311aefee2bea58781fd648e6bb9df95cef0064c7b7e76fd4b6939313be1a1778cfbe83fe40e6799d5636659b59f95598e0f650c14483401ebbbbbe965d5a415f62aecd99bf02bd5475ed7e112aa5fd39de52f8944ed173312b7a185acbcf4b4d3656f22eea58121870a66eab32175b28a39660e52cf3e13da7e1bef096d062c1c59ff1640b899ab95b46bc498431acb2e0fdb576907a96b7db0037d24bdba0732e85523ad08337135c1484f833f0b1a3716209bd7eb1e1416d01ed0cb644583ef5605074a6c1330d456326e67450f41e63dccbe4b515377c27bdbd4d705cee961c51c8de094deeed7f880632b5a4a0332a14371271119af2ccdec2856ea3d7c9bba01f94d058251db340fdd0ac1988be83663931f88801efe033525846c67bb42c8bd1c269c68e7253ba3545870dfdec23eca439b6f48a35c949fcfe5907d85bfa4b8968737f17cd7abe897529390ff4f717f6fa38d83012377f133057e54172ed8ce31e7f1f24402725179bb41c58803defff835b31893b12d7ec4d6ce0cd3b7c55c0af1902e224a4302b0905586acb7ba8240a0e84ad3c930b107a4d9da37fc02c99d671f565d1ac5f81ad1b3ffa674b1afe7c423806c914e0c24731242ab14debf1619d8eb50fb04c939459817886822483b1ddbb530f311e9b9ea37bc67d87edd723dfa69faf6c26d87758ac9df596c7fa7942fe31a751c6dfac810eb1b0fc368e7aba28ce1c5c5ba2fcf855faf58244c3ac66d01b5cbce9ed3953570b73b60a798184835623ad36f19c042ad7f3b5da8f6d76ac221f7417f9bdf3fc5ef4e16b82cae27c3e5d24fc9e4d5b486e007cf4c5997e33cd48596416ec00e540f3879e3fb53fe3d115a20853bf1179b144456ed9818e343e59011e693f43ce101020dd02aca5ef99a40ea0e8e6e176043f98d346cd260b89fd2e20181829cd1f8e8121bfc40b1e6ec3d356bb2ed2bcc0b1b3b08f0155adff4142a9f6c36f05b1acc7f24683bf302766072f9ac9fb29ea705bcac78e54070e3ac307e2c06a8c74da4d517894c4748ff6fcf2a03235a0eeb32cfec4c69f9bdc799f8446c2d0d1d5d6a48365f67ef56a771fc3c6d45f002f1e19c48783537531eef0ce14266df1f6ac72f9ab2dd901a419af3f4c32c6bce5b0731d4f7e190f08320a870df38be9da3ff610a195b39cc9bb66839547478c5b832198e1e7fa20955c4156d6eedbedceda5318f639a0729c28e215557e978d60acbd183fad3a83d4492850ae2e389f41a6c4eafddbbd65f2c5550543750d702f049fda6aaea596e12cc2cf2832df12866f4056e5d0c6a4b2dd8b069d6e5f47d953831a58aa2fc499291eb440ffc593a0c40a5434bba66e272ebab72f05f0e3909d64dd79264581333530672a64b364815264b40284222ec79c6d9169c67d076f2bb7fa80c0e900730b24dbb47758573179026e4e32488a164d60465e1dbfcfe52d5ba6b7d70e71c3018a3392eb4eafe325ef0392b5fcfcccb0a7a4d8c90f47af673578700fe222a249384728f4776ff6a0e9ba2d84399345150f2ca37a74605871b5e8df78e100c0795da9993120f925e406f8bfd9e850ea45a7726003a82362ebaacc5550c2d9c9814a9d37bbf4c70c9a42f6aeaef149e94d08348e177ecdd786a958604d80622abbd7112154f45a672066ce0aeb4a7c2be5970b1f3dba26bf570652cb1e40dc10fdba5628f7a9cb1d7aac7e7ed86b6046dad6de1cf692436ce872e9937240f13b10777adf17b068e0abae0963ab8287ec090d04d649f396ca014988834b186736142dd258c4e6c1ef7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_37 : rowClaim true 37 1451 56680 :=
  checked _ _ _ _ 218 0x762b447ea51771d7d181915a93ed32acc14a0bd057de3f698ae82bccb3f162c867467b01b40fb66dca97e84f36a635629572d4331cf893cab797daf1ea8ef3571fa76c05075225d00c793da9027d66a54b5be98b65f3b39a87e511711a523f4bad4c1771a6d21b90235d73ca27181c31ed16d6ea39f2cbf9af85f788eb734654d15eb4393729a58a438a0f7a38f96558665ca43f626bae5304c2f9205db944c1ad420f55ce909eb4e562024fe724f61653b494c9ce71737db0f965ee1a4fcb3ee8e27d24d6d72c3efa834fd77c20446c82d7476c6a76e5c9577e93cf042014b91273b9165aadb06605abe40f26a61d99455c43647563f95dbe1ab91e72ae556dad372c5a8121e2099e1d5a80329f3f6f4987f7ed3c163d170bdbdb8b5503933430f2ffd5c0b03d80d0c4cfe708a2e083c9cfd31db8f55ea0ba434b610bd216899d853520a8e7e1a8fbb18bf0ab3274686d347449f456fa4f6e61ba403393d4107e5fdbafc876dbf10eff3d1a0db4712d93e5e1991f785f2dfa4dfb5908942ec0e00fceb9952e2e4251296d8d6b5d1a864bbf9cf9567a71b07b58b2f3d993f81268b4aacdf5cfc7cf847461570e6a1e8f0f04e55f17a5307dc957ada3af022d2c0074691f8b1a52a6ce99df5b71214501626a6a5704208bf8f9631ea5b6985e3776a3641d1da74bc776070b70ffc67b892a02d54299c330c27468f9f876e65f4c8614ca0188a3cf733f4c9c6621d60f66fdd6606af93d648a9451a3ceac5727d3c7be9cac6194d57088bd9dc2a1756495c33050e554b5d7b3a0f688fb2a1221240ec97a0ac83bbc7193306e99e7d1a3fcc54e8118f96cc78776328ac77f4fdd6b80bc95af62d82edebfb37d169cc619015297272f865522b10c45e695c61ab69315d1543b18d9ca55121d24da67aab83e104ac0a32f27f01446c1a4392bac9a636351da869c9c48849e9bbef307ca41d8791ebccc952aea2c4ba77c527d85bfad56a6101ffebaf4d407064aa1d403bd1aca9f24faabe407a9d37906183e5ae0f2e932f9108ffe04dc3f842febd5783ce9a772e8f1a8ca6c207e1cbb7fc2e0f3ffa99860fb2dfb5a55046929fa9240d5f3d0d127bd5c143fd30c46f6d740c7d2910634c8bd465e7630c9f6153dfe745ba0c77bc818e46cde07d15833ee4e4de25b8c975cb8f1a47fe01b8bb221c2cb5d86d89f0dce6dd7d9c240b1d70b1820f4d1a358725d6db1be8126005d6861f27d8ce667b6a70936b699c365f96386abced169051fc13834dfdc68d93bd427cbc8ae82de3514e00ad04f0189c1a5d8804eca2fb8708709ff98ed590e950a212c754dbdb6dfb4cc3b61b907e8430c1df073aeedf32b835ed638c09191f16d09df4773f398f06917f2479a2f5a35e90f0396164d912e065316b78390cd3b0e39fc72325ccdc6253ecaf48e09b9b70cab8e4576fb876dd7c082a3e0aef37acb6ad7b236086f17936c18d163cf774cfd0a776ac119a4727e721f89d48c9eedbd9694fb94d332ec60a526f290f306a17480a24e037a2c203198c65576281077e4e634dace921a488391154a4c55dd6f5d805f7ab3e501780506293e43289db7af6d4c62b678e79a3560652509508b6c828694a1a724224df053c630118968a3001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_41 : rowClaim true 41 1451 51151 :=
  checked _ _ _ _ 283 0xd40fe204cb5918941b39824b2d449b3452a7b09d02a83270c38aead5c6886dff7c918bcfb1605b8eb986a0c7479d024a3e98c616bd6404dd6fc1ea0874d851bdb612974543d4a0a97e0d6d185d756dd85cabaae010382a24d5d0043ea2f9b40e475c1a625b15fd36bcc95d68020cbc5bb655ca22f17dfcd8078080e34d5af3a66a990c8ec550b8c4ceeb07b8e112cdcee1074074a55efd77a3c6a4ca92291bd76556cd527768d27adcc08698381b9c17942cce3ada75031d947d5d6ba4e7ca09ae46bde420c969fdee798e09dcbd78f042f1802ec31907d41575d7df2e6e0a2aa0f918ebc0ce0972a3232f81e0cd1ee4f179f05a8a4911d4447c32970e9d7852fea8444d4f9ea2300ed250dbfded56b3c078fe52d1dfbd1529eac8d5fdd97a1fc719b2c3cc7725ecb0254743c6da9ac16ecc86264e574065336f6eba1a3b9bc14dd106195411bcd45b6871bd27311609963d76e90031d00d07bd220379252cca5bb79b229f94133aa562c6e325f14c44820305be9e51d38410dafd72ca8b0a90e4e3aa3aee3d47859541da51b5e0179b859453e002bc79a258013b48c59436bfdbdc815f351b9061754ac0666c7763762b2b97cfa1bed412eb5aa8d77b452ab649228c8ebf70a4c7745750e207d1574683c261407e8643b5546c1e4080acdb87e3e8b5a075203996e0b35c737478bf0043eebe2374ed554e1d72acd6ff27d5442bb3466104b934fdf7c9a20ecf7b03d7c940f4a60c3a90190ad2ff964abca19f6ba71db12303449468e0dfdbe0f4426aa1038871d6a485941ef2abdb48f19377ca2aacfc36a04d5288f92391896e7c99f3559c4b66131b52fbe5e3c505428d2d379cb646e4e4eaf74930c999310185d6ba46c54fe6f650531831d827db0a490d37041e9be636d8cea77941dc65984738fc4563f30abf2bebd8586ab853d6d818468633826c8ca0ce1f980725f8632a3fd9bffc789316e09b1e1c8ab2c2bd55f052e27ae0f660462264f6f00cb18dc5185b2d750a4be6bacfb72e6578876b31da2d67a8567c1f08962776b66a8300125001dfe2cca22cb10090289fecb74578e9a78d3ea5ce49681ef672fd30eddb3dd9818561dbf367eeadcc0e7b97a69b5cf42d9577f64a426827ac76dca88a93f4a0d5affb8bb4244503e674eb99e69b2bace6ee6534535311f9ff46061dd78d1c423cbbcac7b10ad57fb1f0ffba5a4162097f753b5b058a795280f25f45467777bd3b647c274860a4096b514c7f9aaee4be8493504834e4f89699e3cd0642024b43ab75d912236d0f7b012c52e61a3d012a278fb65e8813066558e54b3ff561d3bcc3bfbe57bc3a653b59bfa96715efc8a8894f57706ae0338e1d0e5f74cf5df262551313b37e308b99f69e7aec591aebf5ac10f3b5d5a9fb85ae0b911c7c629714f081999de6e18db86adb57fbfa8c5804b7d30ac1c8fe135cfaff2351ebdb36984b8c81858a1f07a844b4a5dcd6231052c806dc298152a3da5f26a69865c64899eb309a2840aa8fa6f1570d040bc5a8d4d89aae7bcb0f4363590b3aa6c87f96efe3b60f753396b18e7ebcf2bea576c463e1bf0edc193052c1d33bd483eeea0d65b97d932b1026b96a63f4ba9f4c7610eca60f3dc36e7cf40c087f713a125e5c9f1e52fa541abb070c09d8584237fee3977a746b2e6b30b7492f1ec01c991cae4a665013243c4a075ae1f8850d3adac84b81b807d9cf77bf0cb29d5870efc6f59c3a0ade7008e343c99a9a40a57c6b330d21b96bb9e18837e8d585f4fde8dbb74cf8ea40f20811f2c1298da6295cbbc8c4273afd446861d12fe693d40ab8fb0a878496d9756194b0aded50ac8f9a494501cf54a1488fdfba4fc3e8d8e906dc7d63304e5d1a37d7f7feb76fe216e6a7eeb1737e3849a519eb5863668feda9ded8c22610243588adc729ba328856455429c5ed2783afaa702a65577bf7b84010bcf39b9f52a3a9b6172ad57c697a26a41cb103e3c5e76f4e861a14d216fee967ee47dfdac341279bb898451805bca03426289979a9485e4701ffb8bc1bd86358b7b1ec38284ad6be300c75fca8a571cf4a8a900e8b6e6fef48868da2c7c01491fde0c9ed23dff271873106ed31e4198af1ea26cc7c1ba7bcac09ffa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_43 : rowClaim true 43 1451 48771 :=
  checked _ _ _ _ 282 0x7cf09bf7ae26657a7c78aa5d2eb3d5196c4aa031967dc1181569d963ce2ddba5df7efcbd7d71ba083cc1bf28a3fe9f1e18c8c8df701dae77856c0c281b12eb00f940f7693fdef97b2b9606a4c696ad95153be7e165e8c1b05fddc8bf7dac92584c0782c135a28aedbba57b2705c4fa3f0a87203c43e351adde5688315bbbd5f91fe86aad12ae0d430f37fa34661cab3d2df19539c3f4024ddecaf41dac956d1416e6cf40f0014063db1c9f1256642db3edb620b7bdebafad2f4a78fac82984b582d45e2b15eea177c08d1556955591149f63b8d13b8e1a19c256295f894886a42a1ca487c48f7b540ca7b1033dd830597a198c6cb6fe6819875ddd761a6f6c97f6e5f87cfb6b9822f8bedcada10daae440e94d51ea79bc59861a97ae1b36d6edba4ba53466deda9666b12a2f4422d478a180068406bea8c3cbec0824ca251e5512779ddb196bc591c0e45b95cb2d404c45ef1da7ecc08eb267b2d015623bc30fdff7fa6f21d335db46ca1ec5d2708100bd680b7640b2993e94abbff9f470735fe309f83f445bf2ddd05d60fe1dc050d26ffd7824f56f47832d2804016f215983ea3d5586468890febf7a8025a25fe8863f38cfa9bcbdf4af7adea4d2f8b05d2d7aa524968b907a0be8ef03ae0804ea86f1100f76276894128797ef4fcbf0923dce6b254f5db58cf52b4c5ebc5c68bc0b055a7dcc03b284395cfe1cfa8b01136f0293128ad19baf71fa7bf7b93e482fde8aa0b43bfac6f6068a7fb2b5f4a7780cd31c2954e3fed446586a60415bd793b730e9e9ccfd1bec3603cc9981464b6c877c4ba3907b41378e859f90652201abe63b891d10947d2a7c509ccde35291b444b6b0b10918726b27922216c2701068be023a7713fe236c43aad5f4ee8a1dab0dd5a6c1e0bb29f8e1ab12b39f1583d392741e969f3a082f90fdb95e658fffd93393287bf61c617237bde6575b68b733f3809d828efa2ca8f64f20a817ac200c46ebab212bde4e040ae31fe2ac935ff35584553636e53a6d45983155d2862ec3f69c82ba80aa5181f992b715d59b91e00e2ff0b79209d6c524d5748599689266650648af3dc1ef8f43152ec6aff7b6003ec6b3891cbb4f260d815edc6a2441ed90f8e5f67f590577f32ff4a086fc799fa2a129700a4cba22ed7fe14222b22fe66526c2fe96cff146a2a01b33fb90fd55c223366cea39bcecb1b76de5eec84daba347891cfe6be1d6eadb92352dce329297024f90662375133928cd407cb3a631a8bf646bfe26e053f5b01faa9b5863fa88df1a01002b5c962066f0341fbffc6f47574f80cb1cb4b8f2ff0d4456d5f16e759766f37d2e9fb4ea46950720117a45c4682a6b257376bf629a86dd987898b4991146f536d9283ffbf51d7b37aaf6609960de0838f03320dd49bc63f7ae0e2be2683b4483079cc6a7183a6f17356026b151361752dcc4cde4817f8987252f52705d1f5f80665871ca65a09f1d3a50d5c1c7b67efdd3a4413377db000d3f89313547c6aa4579aa420535aea044cf7c090073c2b9eff59c58a461008caa8ffbd568c27c6d07553b516b9bd048d124225d19b98801e32ab76a21b279d30f329d34416e0040e3e3148c5f547d70951cf0634f7f6ec29bfefa6997c23b295d200a6ae51dec6c0258033ac1613adc67cbd14249259de48c4b0690cc9316f035c525640225ed9f0fdb6e42a2c569868f8b24808383fb508a4ece338e1a194212289caf4c1d1c6ef9c830cc2c842f6507bb8e0d87559028728a4a663ea36ad3ad5b9c6f7820621f89329f29ff587ffe1ecdd98e4d8e1e19762a0c8a7a1f7cbc8a303dc000e4bd2127154c86af93e652d67fdb7adbf0d4631f12298b37f913597f02c33708bf83c72c5636455ac08d89ce3e6a66a7ac883c5e8f2737828e700c6fecd7ed0f4c64bf6d3fc24216a1abac3eb4fa12bbf322d682e27a6ac335e19175e7e7d8f6166f0488861e051398bc2fe2278adc1c5ee4cb4f0a0f7613ee6919d8215e899d462224c50e52274a8007665facbaff2801107f5f669f320b6073d1568b36b88732902a72a3ef04516e50cfb97c39b097ea4a662a7eb241f3d6ca5b004cad922142d6d8c0911b188cc70dbe6f594060ba707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_47 : rowClaim true 47 1451 44621 :=
  checked _ _ _ _ 224 0x4de71b18080b4076f723d2bd19ddd20a4038cd99fa4777a4deaad64cf2b36101745b08c2974b39e409965a28dd1f13a2a11b9daa549767d0c56b423f50ca077fbb9fb42d0aeea89bf01fc5b120b2d6427b49c66e1536bf4bd4545ca4816390901ae26cb07ec5dd95487ec7e034eaabf0c7cd28a88a59c9a2ec8d2ddf8a81fdbcf49975dafb7f817fac87cc61456a4c33ab2d3f546684aee00f1b016efc46dd9375250ba1fa39e1b59317cca6cbad4a21213b13f6beed6d1878da0d859edf5909b6f4b995950e3ef39c8f7400165f487e802db23bd19dc3b8400fa8a8675741fd062118f1b33fa830a6e79f22ce00f4192b5ae9fa12e7a0bc765777eed680eeb68f38e81dc7b903094f14adcc27983a2103c720ca79a457447939d91827a341a791d2c65c9db9c74da94a28095656e02b45d0f3835c1a6eae403686118184288c43db3e1da336d77ec4d4ecad3ae09187aea3418a740306c31a0a9a3c6014db33ea398ef5ba66e04bfa68b4816984b5d10a4e3c5c403d568d2d96112f98d993d06914591ca90b62a9beab55efb016859b6db2774df2e4f551136f266369e0fb366971a48de7410f198e1ac1e92138489a7ee649c4fcbdf611bfbe2c20f58b50c7acc43414cdfc5b6a1b123dc265dce4ad2175f8ee3931c357167d6ed75a694cb3d05fcab502e3f5da30c04828c0bdf484b38006f359975a7828663c423a4745656cf09427fdb7408671635d91cb770b8ea0943f68d1145181c5851539df611b9fa477366ee19ab344d7df7010b323d5f0e72f6915810166b9a2ed69e21480ef18568127795cac973a7bb2a2db8d8f01a7d50b5abeb3a7c5d13e28e39dfcdffa393da4bc237bf695cbbf96a6041f631f77595f668964befa61d37908b80614aac11e7adb615e92dc71ffb75a6d8adf7c91f4ff4dc943ee84c1f095d4eb5384baff14945b1acdd42250ee5017346dd4c6881f66acf0c2e012c905c1cb4150a7271ada99b650e68ad68d6f950e76c99bdea6cc1956b8c9264d118b7d207b6bd9620d1fa2eef23a810720e509c2c92fa8d60fcd221a6b9b01bcd6354607a99a77a63c6619fd2ef90e8a0c2b4d878c027333aa55bbfa993d86ed4f32c08ed737bf6b761f0bb4469f15c9f661278aaecda50e8541cea889ccd66ff2d6a436495fd575d62c61934779bea1a421854372e16ca13a435de34a23ded71e894e32e0392679955e77df96b1a2ae1ce11c06052e71c85def3ebe896aefa28178a8ab0a375b3b038110cfdc84ce661e71735c397a70377f9e6ad0bab8a90e81a004a217b463312ec3384ce2c884273b5fe6ecef396e5a34ebc55bb88d9c8fca51f4284ccd9d00b5a1c4337d5e68009df4a5b98f4c7af513a3d2e68ce128a3e7e7c05ed98357323f3cf9ad961544d66043b9139c47ae0d5c08398f87d5c93cd225d30d7afd1da00f3e24b9dd593391dd861f8d546a349e5b56371b43550ea024dbf2d825a141f5210198f9ee7f2e2218fdc05abdfb7ca98fcea18c484dd9ee2a9e2852d27eb121457b6d5edab9086182424d52debb9ac12b013437376b10ebe0c37b272631e9c79f4365f215ccf3815220c69445fc26ea9118bb40e0cbb476f98b8ed9ae6f16b85de8485cd6eda6a4cc4d46eb459d811147918eff18f90bcf1126419e9ea131f2564e07b16cf5f00d80a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_53 : rowClaim true 53 1451 39569 :=
  checked _ _ _ _ 228 0x4d8ca37d0b5ea6d309196f6dc2c95ceee2019c6e3bbd44e66fb3089ee13a57095bbac909de0004bc03a4ee2037f6dc6db6c28700ac9a4cdfce9dd3916271313ec4c0c8bff2c8bd37b315342ebc205eef04f5a34e5d39527a41ec6efd07c87a23f678cff9f6b68a82f1f56ca9bc20c7c15c9457423d0ae4520c8b317ec9554efc26f5ffe6eb4c291e9c5f0eef7c884da98de118880a83bda282418acdde652e82441c23c1439f1227f8bdb6e081036177cec09f955e5faf637ee193d66ae350e9ccd3ff9b0604939b1df801663392ec49c39f439261c934ce9f5d86c21803c4dedbb39184ec2a861a2e87fa88133b2640b26b735abb95123f4ead4f62ed7d7eda0dc2e8cc70411211be3f926a895c022b2e7f437de95cdbd86f876d557b9ee1adca505f8c45addeb2bf680408bc486f42885d009bddfe2bb35c5e4e4ab0d7df1298e8cc45760aac082bd290270864615ddd6a2a302dea420b8d85a7ce01b1c0e08a1d940cf72754c11c0e4b8dbbfbe082d387d5e32fbb69a8034298ef273d32218f4732a719c0ad2e86fb4d9d563218ed496621665822ab872203ffa51712ce5acaed1903d98f45ddf690b5eaaa823ea19553d9f91c5f815ca2a256a9ff1680337c3947ccf2be391d068ce40e5bca2f929d5dc91a7937fa465b7f8b40461db9e1aac10740a0f68746a75e9e29cf84a1b7aae9fbc757c3b18cf6b5d479c2b37584c746c8a09d6e028daceae998e7103dd2d6e269202398e0cf7db99395c56190e3bc9902a6b76149ca33a009b9122ee8d9e296d73a070ebb1a3a8473780102dc84ab0b90a7fed784a0f097d1c804aa9d35f0c15fc74f7dbb7268675ac8386d659a3603aef85d99f07e5de1c37796e7531fefe9fe331c682ea5880bf2df350282df1005e2540d556b5f2f40c4db60c13a92de82db7ddd32f88c232b8c5d0fb543fa677aea1cc183bbd40f70a094f71bb8663079f0b18dd8d095a858622917f31d8943323908617cbdfca2f1eb2de8de46075a3af0d13804ef9f2f775162633efaace38671f2bed62bb237b4c2c05d1e2ce5dbaf0b43cfb607c8ef56357fb1456c25748bd06532e3c611cbef3b10293c2cc98f782f130e9fda473a1a43f4a37428e29f5968c4da5a025e8a5d24ce88f0148bab59838f2654b41c7a026138f15fd98ef9ad57b145325bac131202251aab3e5f663ff21848711ca5416f29529af8071dcac44ab56d5cac840cbe853d18bbb800310708686f9cb62710465de6e799914ede33cfab33582cc70cc18a59c34605f6e491f295f2130f50a5afe81735d062b84a24d7d01400d27c61bff80d01012f41e6836277f11c5501e1ea881efde667913e27b2ec2364514c711e7655999546c26d9784e5c95489fc8a0ac48081926bda7b538846e8803a6de1879d3b6b4455cd11458ecba3c00678fb0cbdb6b7907ddd1cc695878e31f4e842fabc588ab457596e1f7a38382e7c2b8a75aef4c6e1d725286bbc0bb8d2244a4c81b25f1797b23acee8da064b73367f7b8c5c7cc809bf1072197f410f433f23ec92bb728c858159fe93bebd9cc3bb725dd7ba407be65b9f12f68c9c2a63e32d8af7d6313cd1ebb450065c56065384fa27fad4b0813db853aaae9be12d8b5d085126b0573be1fbd01c9a184d9aa687a95ff9eaabf46466ea8bdb7f6f76fe28c78fd1ae7a0ce86763fe1366a9750407cda080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_59 : rowClaim true 59 1451 35545 :=
  checked _ _ _ _ 294 0x3f5615360e261f68813a423a57abb68fa00e062b87317b9505d00274d47cdbfb643faf0a9ba19d8542e30a97282862767074bb9e203019167088705004db5c8769d1a72c86749cc9e91c620c862da2e1c2ed85bd2099593abb80a6510fe684cb95070d6c6e0764ad6b091bd72ee64597aad4582edfb1cbe908435349681931814e490b810749c0cee0db4d6fb2df2c450dc8e690eefd1b50907e08900c155193c1262746c37ea1c6c389b9ebda52f9e11be248a7f17f5cd5ff8abe100864e1d554a036f6a0fc4bdb55dffb890d6042e23735c8d5748952ccd19b26f6fadb2e01c117546ffab15191d14a58da80956fabd15437e03c267a405c45b6448799f0bbb7d3dee99cd6ac68302f3ca06cdc2d201d15aac6c4eae1b33345ae0ea1b3e6cd789929c8707115796d6c82fc837ee30273a1050d99d7f4d05eb4743e8d23e612a9bcb90ec7189dc8e80e0e5fce12f8ec8427b6d63f46f25128ba09ed5a957212e7675f461491b5571659b19d06178653bd3f177b6e95360f6ad8baf4ea6f681886ade567f65b553f829c330423bfa959970f99f6c6167058ff01e9a5289d09589366a9e6a957fb50c82c9bdeea95c05a619e8e5eb39e3e928bc34f9382ff18cedbf61522854afec9452c7cf5d1dfa0b07a00331f9f4dc803c342558e88bc78cf058cc9402338b34148683adf8e11e47b2e70a58af376b3cd493aca362c5aa6665d8d9319a0b9879dc8edc58c0041b2ade4b0af47a7c72ac5767836221c774f59e40757c6b483ca0f02b92f3ddd987ec530cf30a76b8828424cb19dfa80092a4a52f0e2b02b2c4fd71ecd0f5f8cce7d061eed644b1fe6ccb07168a5bd69bbd4df7a8122642c12b010f6733246a9ca57c740b231c396695d3d9a373e8829e06f092d3c2536b279359d82c4dd5c94b00443526e111a8e03054f955d7d0775cc9f5a8b4f9c0130e27cf80863e6027cd6ed27e153b5c995aa8679b9a857438dbe5e4202e2b0a1dacb6251cc7c2d6127220ac7520a97ad9513d9475f57139000954346213ef25912c2d914322a5538436b9e5b8f2ee4c86d0cbe86906e1f685ed652a17a0e72b2dbf5b1a8528f286aba0da5c9e3f52866bcb1fc7846cd5353460092482ca30c0c8ebe148644a02700760b709bf842708eb74a83cc8c32ef4e03d1416ac9ab2a1ed524bc7fbfb2bda2b80816b99f310d6f6c1af58b6b9d188e35a6102f8f55ed4d15b0ae7425460cc2befa8e35bebdad1231b5ca3a2b8ea3eae72d4c335eec3f70c0a4e537addde07a4e423d4ac5931d37cc2f3a8eee013fe3b20d124ed2d2af24f26fd6b1f914c20d6fe44265214923acee025205448270db674f6d3c5f1080594720d4b408bd28835b094840baeadb650c351781d1199122a52939c10e8bd65edeb77e163ee2a9872f1bf13b8a73812207abbf70655a36bd6e85a575159af5c8aeaa42df5aa065ed8efd0217b336005451faa851d60fe0f348e82deed8b3f4a2247a39518d07c805e9395482d9ab02dcaa794ba791978e5932e3a86b9e87cd86dd344003d3b6c16fd2deaa52a4229d11a267bb7c5c4623614b752d3bb74ef3c39c7eae695127ca0439d968d6498815b327fa07b65de1a15ca2afc028b98c609afe8ef1567d4833cdc0593f8dc58b108b4ce2e322bf82d133e35a60d217079f7c2c9bcc47cae90a96d0b8865603c9a0da4c8ca06ffe380bda6cc6262156275dcb017b813739bdfca9cc460d8991a0318c6f91bf232b3f3c44ed2648842212322c089e0af22d5670bd3735eaf28415b9ddaa3dafd3eac439a1eb90f9e5fb1b39421a676fc03495e45f4d6e2f3079d5a79135103e83594d46070fe6e43712a0088b3b8587192f54978a04976a3e3c194290e7a766dd0b5000a2f65d2d6a83c19ad0cdcbef74d6ac53b47372a068fd6c9a8683e6019ca41c6e1bd811e3731e673568cd07bf9848fd576573d0b92d48e813c7c8d0ed4971ccfe23031f79cd0d1007e3114aec888a4c3df59af96407ee4cefa99d885978482046afe5f1f76a34319fc616949f3ab8a8f44e7001f8c1be460bc176ca2532839e03c5ab0a9b65b8bef68e7584d73a66d37d1e3a5a78f1f96707a7754be518c0f0f5457f4d3f10db2064a7c262d40eca4d7327d9ca31185ef9dd03148b5eef3c8069293113898686e2fc639ab58849e775c570e470475c3962de65ab82d8fbf6f959d7a8102b20a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_61 : rowClaim true 61 1451 34380 :=
  checked _ _ _ _ 260 0x1706bc7329cbb720302e939ced56a677e27275715a0a8d6c05fe0b19bdd2a8bbe8752481222b33bd943d8d5c43be49a8deefad6e8e6ffcf173fc917e08ae35355e2d95dc538a05ba124b81a025b951af26d5f3a045fbca671507a78e22a204df170db6ba75a302e56f45b13e3bff6b41a0dbe33440bc8586e7e8691d34ed8341e88b34a66b8e411341959a4fa766b69dbf9bc2988f60278dac073bf274f34269308cbd58303ebee8df4377cd298c862ae3e20d8d0b9c968fed56ba9459890669280724ed53d7caee3426254a29fee7890a29174b06e07ab86f22c65eff11628ca2a1a81fff7e24a8f79fec5a507c1934ee925a022a2ad3606cb37c9df3ab8236bbcc7418b22896e8bc646ae480cc98434e96a8dd234c08c80803344396a2c126f982557a218252ebd555b0ce5da3a06d0bf833895ed48f5c558ebde072866cc383d017da08f545878a71dc7a6c22c93d4cbcefd78455618937d1a72564a39e532e239c3b6bdd062d42dc517eeff2e468bf439cfe7b46f1ad468cfc63a905d1e13698f6ac4877ce595ce30e31bd365586515c618a4eb2c332dc3ede2598c759e63a626edb28491f2e0e0b5eb94d696cef31c523eb63bd25be97a350365a365e77e054498c4a24ed46610fe184b4e2ecb2c8d4dc977d1f373a50a94cbad2ac3439e3a0cf0b949240d2974c566aee83273371024fa61cd74054793ca15ad602ed6822bac0907c987bf5318fea7e574f954116e5bdeeda157bb08b2df72e1d97ee02fd76775a1d9c85d371099ff75eb8e41e13ffb7b6053e49739de0198dbf12b308a165c4ed133491436a1f23a2f81cd2241c15ec5842e306c6f0641dd889a6ae74f786619ae9d735fb94b619b76f8aed66affedb490536bf35aa0d643cf07fae71580102235064a82ed910294232f1c7c6d6384b6c5348141aeb664cf9af3f77a2338c5cfe0bacb3079d6cd834fafa8e6c0bfd1d20d38b7d9d48369b40ddf1cb23a594a668298fc3e1021c494abe2b74d9c9817fe9475372b7b69905dabb2695b34d950f1f2949612f5b9dfa1137fa8487319906b74452c52e7c46af676db3008fa8c166f85f1e7e9301450197fc74c2d1605bfdb98e95c55c9b110adad2729863a872a40abfbc2ea5f3fd446ff7d3943f95713ec9eaeab3cc3963aafeace47c2fc9bd2623f70205cdd200137cc37bfec34cb02f2725e6116f97ad36cdc84152722200a8638eff7d3b5c9880f1f047695791e791e3745eebd6bba81465c0b8aacefa34d72bd8e25d9fc430408afdcde1ba28b1f05f933d31569e1c45f9f62e198412ce11acb9b11ac4196e7cd08324794d3df3ac439d0e5ee6a729d44ede1e89042a1f7f645bff15533b43ae11fb8a59de404cb8e073e4ad46694b5400ee932d1651af9406931b5477ad61653317b77f1aff0fedd4deadecd5b69bbd9d9bc52033e0020024757f9c0384cd5d2fe9e1ef6ec79506ae0fa4a316b4556504bcc9c6d618a43a421d54317fbb498dd8f1c9ddc55afea3b21a227c114308302fc7d0293b7b7994c661c59fcfbe44be09dc382d0e26104b1430adb1387800a2c795eb48cfd352c812163f7dab92534809d3497b7cecf95da12325357c2584bfe2cccc6177ca461b8d5cf5deb35b32383547dbce67fe4210c2a13c22fd791e7ece8e669f27f1076d68c8c4e9eb14be985b0047a0ba2284a5a83c6448e9c0690d46990293d5c1d30194bc26461496d427754f624f905d6f03ed813104ea28c4d37a4052d158168da2c51f0150def104db6d6b7f3a06f2cd0825f38539f9738edf24a8b79400775ff6905575e66cd6162c03a2f949e32cbbb65526505646d324538fa98e621082e93b9bef866b853b2c4186811f0d793ed68cd00401c06e6c1cd4c4be7c432642bace58b4e5f2299048e783e25f43c4b9e632bbe8a6872507d761a05fd39a144dc4136f2933308746d657003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_67 : rowClaim true 67 1451 31301 :=
  checked _ _ _ _ 248 0x3a697c0dd8e0f74f54bfc5e01fcd31a06875efd1e095e8f4f477a0f6fe755eae09347a0e0e173f4b8015220215c68983037c340edfe76b9fbc82bdc5b09e5301897096143bfec0c2b2b65aca0578864bf0d72a6a75c18057ff28f112804de42e48a14884f4b8550a9b54eb003411edb12d942d5547064ef3b003bd6aa34ee4ddcd95bb8965f92405ba627065e6855fe99c3c68b117ebafc3203804d21df9bd1f8ff7541ea3566b12089de9529a7be26ccf76a169708d92182d801a11f8ff30d23fbd727e9082974429ef0a4cc1b915797ec1dbe6272cc951b06205449ce485cd4f3f9e8386002d1210d88efc3afb99f83faba18f0143ba582ecdcf02700ce1e8e5f5d2e077f71a11f678a3ecacc8d3260026e0dc57d559d90538bdaf92bfd919c8370b026986b2a61ba01d2378d9b899125950ac93a84a6593e81e5b0e56ded46213486248c1250ee163e53d433f0a5dcdfae2e9ddd26720a90c8fdc186094fefbbdee43867bcd89e5724e03bd943d8bf83272880115f6be6c1a2f25b9d2ba1bb1404223abd275fb5cb6996fd35fda9c01468d8e48153cb29c81e852520a718bea5f673c252399f5bf8ab003a3c4f158baf79c374c611e2ecca5078a6b7bf01e08bb8d7f02bc9ea09b79b8c3dedeb81c866b45de32fd2b90ebbec61beca71778499dd32c5680c9e8197a39b47dda56476255f71bf256ad9a719bf7e3634960209a99c683895dbf537bb9e55acae89bf1b6eae611ecda5da81578c8e492e902871c31742dbf3ad6625faf7b89bd3a20ef6b0e6407a07b15819610733cbec1ca793bc112a361195441b8362ec28f6267f52033998e6b93d1b77584c7df90f6971503ba6891eda743c0f6d56e1d97f716f66687bb0c0881d0bba97c6cb36d91737113049af69728ee6a90fe95bce1492d17867369f53ec6dee815b411c6af2a38e9a294bf21dbae6f9386e2c52d31ebac0e71703e47282ea327adc5f2e91fc173da7394c6b9b3603d9662ded2a5e26fb19de57ee09a5269e5addb2a99b215f88038e8c3eb3cd375e5bc735b926505c9a8ae4a961c1ef1841c3c72b340c2ec12cbb54100953c2dfaf2354d380ecd5a1cf3f6ae79e37ce78ff941463f53028ef02ec9f343aa7f0972c970e87aa8d937bdeac7e6e1ff8ac25e9cdb506b11738c9c24b94753a4aa1d50fd34384571d0883da4070bf502c734934842b11f9bb8dc7d5df8c74fce9d06ef5888648c47f76cf5e46a11ac3a2e3c8ef325ad59b1155f470f45cc076d0b5abe302b809fa5b621f415edcc9efa3823f28f6e884d7befab1cf4cfa0eb96cf94a4c5a8ab4a61e0a53df1f9ab1e533f8c9d1d834895a01776d986318a524dddd51ce0e3384eb8db332c14b07d055428bd97d44c1dd0da377c9bf118dd06e94850bfca4eb9bc426793d6662ed2258b13bc94305c4ac102384a6a488aed074ac914ef6dca99944744a50520fda8dd75417d84534176df9a1563b55cec799d61368b2e0dba40ed882b2bdaf7a0c4629131c421d97804364f4f3940d3e141748e078e74cdc434e215244e22f2384e02662b069e1536a738ae4cafd187becaa05dcb1021b2c3d09e89749a7d0e9d13e7d436543557c271ce33176598f3888345af4be109a7b8b07babcb7e7b7a1b4cfab61a2704cadc10ae63804a0ce82ba4921d204da73eadc24e2564940a769ba2c8e8aadd91f77f1461f71a90d39a8f9bfb1f5617f72a59e84c606fedbebaeb27a24477283ad4bf1723e1f6857db5eb33bbdad6a918af9373ccb5321048e047ad917f3323b1bf821171723cea92cae76983be02aa7d356339373faef86a35fa6d3da08e6b8211691db343aa059428ae7985d0c0caed2abb0090 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_71 : rowClaim true 71 1451 29538 :=
  checked _ _ _ _ 155 0x4783cc3b1220fec75e2734a270fd83ab37fc6da6cce3a3f30cb0832146f1d9ffe96bcee6a9167fb4c983ea60fa418692ab97070fd44169226e62edf4130e1106db38f16744423f3643d0ae095854402319005581f7d8301bad7a41d25e893a258fac0e7d8fb654e5ce7b6dbbebc9ee851f214103ff331fc102a8178ef35b3ec09bd231918a54ac90dce22e34b335fd59687c2ca55b0b29f963dfeb4af904c03e78c536dc3051b257386afaeb652778289a115cf51c8b743708c3f8cd13e229ce1bf58bf6dbc8a7fbf0feb73250f6e4062b36824075e486f943543f9d1dc9f79f883e001b58e5cf75c786b6abc6d43d5920f86ff09f056c06e8eb8d080a4f13a0e314e51bb6da6b55dc60d4e69d53e137545a4f72bee916d98cedbdb80e648dc5fd5bc588d36bc6f970fb16f516de49b2f68347345a742d6d266f08965df7dcd66fb139e33b76fb85a138f7a9cd3803665bcbc0556afd1f4930656e256ae662bfc5207f84dcfb37ac592b43fef6a70d8d883b8d2b0a0e0107e4e40c49c745fdc0067d13d1870d1d5874aacfb87fd070bc2d51e9db280c72f39059a8675cca81080706ec6f820b20e8773fb9e423602718d0e35ae8655c34b31dbe8fcf2329df592924a338d33bc0ac3e29e43ecdc5be76638f2c777be4ad9c14f90fbcec07d484a16c6f3fd21e2ead9d93bd8fb901c119b7f54ed3384c097dea2c2ed3490282a3b5f8d5b854edd9c66636cbffcbb3d70e036d985d731e883bc65febc1da2b4a136b58968529faf7ac41c46da0934ee321468a9d4872d748fc6c5a14db8a7d856b98b277b5617ec0cddc9a0639be9ea73b419dbafae48d21cf24c1b089e51bfec837d7336e40017835fed948ab38cf899f7310837b1b728b7715ddb823534ad41c1ec8e59d76b66f10475b36b36b7a4c682682e458856e319f81ccc6146891998f9f03c7b399110f65fd4432d2e3f87877fb5a9c07f758e6a5b85944acd52116af2e1ff3c6c446753960354a8bbad7a486b44f638d8001a6f73015d357fe4a66e2cb3a69eb169a59d2f7e44f45ff577db6624c5649ed03445a1cb88d39de5cffb00ee34a6e39993cadb27a771114210d80ee334808cde14c4ec3d6b25780469725cf3a1c7b6024cf23cfd300bec41cf00540a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_73 : rowClaim true 73 1451 28729 :=
  checked _ _ _ _ 137 0x48672cc805c005b180243150f16d5ec6692652857c9618acd2d059966b508fe6ad5b37238a46896ba87f99771c3020e036e475b66b6b7b9b557d60911869e7c57df411be53165bc8c3b298277607b36b0a62a8fea2eb6de6f27dbce4d3e9532542ab775d23a10e48c74f4b46b86a0fd04a05bfc793fbb6985f69cfb5b7af3f1ace92064a25817450e0420c7ad973d751128bd30c70fde43781bd054eb7ca025b0842dbd5cf1eb0896337df4114e4554e23e35f93e453cd79d2e427a53a42926ce5b6740ff8ce27b1ac23c5131d9e50cd287fce2dd8879742ae6c8a6b7f844e5d398b545fdebfc6b08b2f361bf163ff87be4693bb2301b4fe00b2ee97c5d3f1507ac94237c97cafe9a1dc780f2ca3fa1cbdc96afa6f5b98c560a73974b0246e91c231307891d9f0d079e3ea64ba7b238cd26314f3085e45fb287acb6c50d6133410989dabde25d64add576a7f74ab3f7d679275616cf470d488b3b82515e32bbd60110d02814427d7a59bfb83bcabcd62ce8b505a7d3cac97a1bec01ef74f0eab189d81be4f4849645a511486369fd6050b88b52dfcd515684e8e119bcde4f9d8e1ddc8ce7fe3dfcf88f80fc16b4d0659b1e7607e78edc13e5e180c214e729ce81f7428434d515454b8b227d051e574e9f40bae7793989526ef02924fd1cf50a6f9724af359694fe5307f65e39623ebb59cb76c257ce4c42cc5384b20a9848e8380af60a52021e9143c6fcf2a7fccb3738d9799cade1c6d4ec1735ff7ba43d15481da9ab2dab9294595b4514690d372b63c7c97775d0b20c19052ebb35918fa7039be8ba5943e960ad83cb2d54356fdba593d6554b3f030721655d41fa0d54a9887dd3e09963bc731a624a68f83cdf4ba19f52e137138840f779b4a66cd52ee10bd90212627da74761486b4298978f773d8cd950677df72cf2525f28955606fb1cc67799c3804a9d15b5b2c94c02cea20c610c2d96381a0aec5b2e8232b1493f6ead7a8c68301de5c9fd64d7b7f31419d9a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_79 : rowClaim true 79 1451 26547 :=
  checked _ _ _ _ 180 0x580b0c4a1dacc96c044afb822b3d8e84bddf4fab0770e96cb597c9df10e75a81f173e4a74d6f19468b10448b2cbc0a14857b0645856b0fc058b3c929283295fcd7f08ce0c2e3b0488e02e4677350b9bee92a82b3e2f70d52aa3f1b732fe75bab9182b71b9397c6142c9c031cfa3706ab011590500bbb62bc3514a542adfea695de9441fa29f248935dfd230470702ef26610cd6e89247890b6d93b68747e2aa56dc450854c5a43e16e5ccef64aeb8d6efa3e3940045ddacf77142869d65f919d3d21b40075c4b582bdbfb90c996f00d3dc31953f4882742919fb8b1be5c09961efdcf79a3be436763a8645fdec985e77bdf9e1a869b74dd5091d3694a859000245bd4d0d2de1fa38ab2c2b9d8be6d92c7e1c24e71aa1959b646092a41a999bbbdff8c4022c022f7f9a7d0735bba12dff36c1f0dc4af0d3579113ced481142820326a3546cace6fcb4d6a64b00b4ae9e478030956faa8468b65ecf329065c04be1de9919bf00e54b8190ecd03bc5b7c5f1c27ce7a05b35b68dd4dde0bf1f88e9f07a48d914eb3165fc11ecb7e0e5ebb7b4d2044cda34494b9f8884f4c7b5915f110aa49433c5a7fc251df3ecd01f553f7bcb514a1731bb4c945c4d680d8917194e59d93c43e9fdb334badcc963c3b2cc07562a7333dc7a53d82be7fecdfdf6360e548fdb0efcc9368232904e7c138cec7464800347f392844fb699b120660b5abcd10fd47a624b684a8997b76ee25e78b0fcd65655eea51612f980ea1216f8c3fdaea4d27836a26a2db7b1c5ecfcc0d248f86f2212bb033e76f28badc008be19230f628a3424f72641773d0cff6d4267467d87fc1c8d6f5e6cbf2021a05c22b95c7f95b7b30c7cc83974191269096dbf2a06058f953e6060da25036dd271544e320585675903f2a4f68352ff30045adda42d7e0b14172004e4169947fee9b9128c3a2b3bd7f0fc0d20aabc0c97451f329e2a6e0cd7aa09fddcae5d4c5a78d3e5ceb1b02c418a04840329e8bbdeade18387f2696474cee729b6f8da385879d12de38fecf0ac3d9af35621b9cf9b6a0b61d9da4f866a0092b6bf7e8edf25e9ec64d9647b9446a30796f65aae6e0e4b3d705ebcb0060377aec6dc1ce49cb6dc65b4905cf85dc2677de939ad9b02e4b217c41dab89075c206670d6c66c13c82359bc60b730dcef6eb82b02eac739e8b027bddaa5edde107ffcfab1cba1804b6f8f57e3ad92664bb7e937b593cb94c08a89daece45f8090be97233b2c397e6563dd06117fe4990d8f31cf7936744a1116f636308e1d02da656ad8d6ff96847511f278d35701c7e6d8f7ae151690e803763c66b73f099f067f16b007e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_83 : rowClaim true 83 1451 25267 :=
  checked _ _ _ _ 170 0x28e6a99119420afe65ca5e23a31dbacf30107da2aaff365efe766cdb3f0f5d1e87a188351164a1b12f9624715f8f92a9e34e5d34dec89b39ad2d2619a09a44a94c901fda25dbda7810fb7a0b195fc83dc83dd5db7141b0518679c0138f0f9b041cc591b5ad671225fae462709fac6259a3f8323bd007ad6d70420451c65859083f8eb8bc9da1d4796d90cba4557fa0aa53ee01f7ba15cd968172deb52b35b93c595adcbbb383fb564fb9cfaf8eb44671e453a8fadebfa2a6577be77958c1a577e83a0f9f762065ddf5e765ed0b519a190a14749b8f5bcf893232ba38fd3ad4fce957e3c2d4257220ae661f70eeb8438089aa1f0ed7ba407438279b956b9717e7809263d31f999d17ddb0c162f85260f2963ea07e1e0bd32953c4517964ab5e770809fe3f67928eec8506e339feb30c1dfa43c4e589cca8eebb90df706b4bfc21bf73e1b3069eafa11e1c7f6767faf0a8b8d479e6882bbc9bd6d86b367c367dd577862e8c6dab75c5b6d6ad47f6407821cc3d4655f2499c2462ebcf568c4f2cc146e5a2751c5e6f6bfdf6f0e8ffa5944dc0e1d56913fecbeb230abff098878cb802e03209c7a2366059dc8ef2c66bfaed8c7b30f90b6971fb96b9ae22ab3a6c18310012398b03fec6adbc240cfb09ecd2a41fc41be5c080bb23742e2becce93315a642cea327998acf45a462f94e0d00755a15718824a32b2eea417ebec7720cf6a79189aa5b81e4ac831c4152b8f1176942ad257651cdefb8f52f680907c4383f209244ccc333fdacbe4589d2d8f91e1baf458409523c6e69b01541f84a4dd173f75a02099838025532de33aee292ad08675f9c660155aabae974f44f9284590f2318db8c534a190e8d65daf61cf92669e3024bb58d9d885e9aced6a079a58f0aebc57a62c7d7f015f7374f8cbd6a5aa78b094bc694978d41c4c3042bc1d2b3caf1c1255d3924f65f660f969b1a787c1dd137e703a9afea6a40f198ec30e801681831d282a5f9c385617c5679fe08698390c5ed5892f1b113b84ffa492edfecad42eb125a0cd4709d31fc3140f87af9cf85c3069160c755d793b54b78fc84b5907e5df5cf902def4cb89e74befbc1e7e91eb0f284e77ca01cae5a1f81fc5b60b3abb4ceacf57c6364146bad1edf12e803b5ebc5d93d59db9aaa964474a6778f2a082bb5f926f08f1c20c28484c79367c445f6009edd32b5c0ae3ac90f7d2d6516c4ecc87f661ba651cbb0d5973df3277e74849193fd0836ed40f00e40a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_89 : rowClaim true 89 1451 23564 :=
  checked _ _ _ _ 160 0x49f9b8ff172f9e39423a04728be9e71d45624ef3be03cba4ca3fd469e43578b2a7e6ca2224e4cc36db0493b2fee690c35712eb76e0f460400351f2201e661f2daf8ae04894d5586047849b8fb93437b3addf4ba488d6b50711a593cd27c44505d7405f300d69aae5336cafc47204ed1439533b27738c33ecba3fd4bed9ab15c1e80d0e41e501228c871f70e3679248c6eb113bee941ca3ade5e097225bb774ce4747a02332c1e888718cd8d67acca764b1a5846ae4b9c34bcb228b0e8747c7dca6c4f0016edf9da1fd5b935a8ce02e31e41ef1aefc02d91d269d5360db358ce03fe353801443197b7713792c8b840a01bc86c0c8c89b2a1a782514e5d1ec496f151edaf5f51c5c96a26b03d490dd10d8bdc42cac32d0dc4c68fa39252fa82b60a863ed0287c5bf6b209a3bcc4f6cab17332ec4c608d066a678d86eaca677ca82ebc6d5f6bd209ed9fab51ab23d9a2f9e6f5ff0b0c5c5690e4d550712faaeeacacaa8f07dea06e43b89a6aa0b2d751fb22edfac0d48837f757b7b1fa95e8449adbbcacbec94c9e3c3bbd9cad139a37fe7ee402b3db0f2bf0d4c5e1ff62366c6bb39b39aeeb96b51cb32a52b7c4670546ba705bc15b0cec5ee468c5c936097e70c57e70051df57213a9e0e48455af3c38be30140189f917c9446065462080af802c3a60e0249da5f3c7c1c963307a1566653fc12415f7934d287bf3dee2b42abf3084cf66a81c20547aed8ae06f07224469bc4eb5459affc354f8e5b9cf6df465f2f726f80f921ee47ead1836b345f008c8dba982b1341f8121d38ddfa808eb7d8127a34c0bba3801096c658d015cef331ff96835df3b95928a00a7a2d7b13930770aa8960ec51dd0a2c4578e3957f6386479c5709292c5eea7118a900960786eefee36eae402cd5a76c74137060555ebc563e09da0bdb73f16b076c23513a86607e6804393cc06efbb4bdb9c69a44a24f34a34826825f3f6e0dc4a3ca01be888a4f576992aeab47c93c4bb8bdf68646515921648f0dadc4d63bf17be2b9463a1ed1f1058d5f7c5fdd51b3005b17b804bf96ac31fecc7c5def06dcbd3eaf8ed5323084727a92241e3559f30a6c002195987e0db094e5df9c0fef4574fed1cf2d2ba20703f3f4a991d42c4f82f301745b0e22dc083e4d621510358b2af4d63b33bfeca109bf063bb33d2e6c4f3a7b4b020d6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_97 : rowClaim true 97 1451 21621 :=
  checked _ _ _ _ 116 0x2a272571dadc0990bf266c3a64aa4935030b49395f533645c48e9e2718ae2b77a1d61168bc68bd08119a6836a1a31c275ec24e149b58c2b6a1e760f180c191ba18f11a4d7ce947948d1890299a6c3b899029c032c0934e19327208343f76c24ec38e15ac6175999601ecc5715f02ba011ea1ae24f01965037d9fa8032e7ff5a6d82371d62af26b140812dd71fc8096db59c7942d064c0c45d6dcf951b2a698ee9123c48fb5eca1c45f0dfdf49084faacb0b1cf8051e62e3ec5297b0af8fe17de106e0e0051cd263d5644b0d949266c7c18be6264ff811f76cddb4e1487e8637ad84b00336f278b51baaa083b47dfccda222594ab2e32c88cde5a68ed75191c345b587dcab55199b2947b05f61d761b47dcb0b5b78be01a93a0d0077e11536617cd6db9a26464b99828b1567791702400017a18cf61e837ca07547ff339ad9ce47a0e5410a17a566dedfc2baa4c6f4ee89e68a6a5c50a6a33e1aa669e57e1bcde0b4ae543f5d195be505e1880812d306b34a6e1b81b5b8c777a94060ff5a9e8f4f8289fef881afdfec9f4b52da1ac76b0a2251e2d4ac9d85528c2b51716d2c6bfd268ecccc42c1ba29705abfe4c77df63b6b52ab99900d6b490eb7723d2601cb1f8eb20c072672f553bce1f13a79fd2df3471c6603b21d718d8d79166b293815e474a0d2e0f52ff5f67e03cbff6d76c39ee730e8b269b2aa29d3779bd677374d3fdff4b1eb3c9c879f81953c50e2c4944c0ceac63984eeb009b0d1ce8a0672bbcf76ddd0c2060c0220bf608a734dbf9fe0e91ec88af575fd17ee25b19ba5efdea6e1b11a2d28482eb76aaefc17499f743227392ea080f92ab71c06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_101 : rowClaim true 101 1451 20764 :=
  checked _ _ _ _ 252 0x12d27467e1731db08d55f6ece409099c8de7cd825f061fd3a65a4e1bdb47c03adc817721c7347a3cae3f13366f22f6b3867236d2389555b2b78118b129b108583240fac77503bc7b2b2969cff0ccc3673beed53988432c280de1403e94577552ac13eee84d9ceb68aa6a7fc1d637e7ea3839f01d792b405369026a1f5894b4450bd9451fbe0c474a5f68953a79a073541f6cdedaf690d9eb3aa1e8fbe02e82057c54c58eb47aa1dd452b3c29279028a9e2129a2b320c3991400173bd28e1b18a775439cca1835256b41b28a6cc61c931e22a3c8cf46d5d090c0d84f47ea8db877738ad8d3c69c7f78ddf8b0fe58dc8c3506f29dc9d84d6666571c1f2ba38dd9896bf22232d036aae520f9c64edc02578415bca51bad86e158d7c9da4cae01becb3e32885e4a9baa788b9a9617b5a312357fa2166b3c238d0443e40749275d3db6fab7a3d63d102769944f6994a06ff8e8914fe540f8ff445d20b01987dc2ce82b6daf45979d412dada547d3b9146ffc797ef16df58c8cddd88e68ed9280ae19784b4f8d7b3cc65fd9da588cbaa204a1d0690082fc0aad0be759038265bdd9284ca9b3451c37b8fbddbc01dc8ba2aad7fe81523a143d0f62810a88cbe099d3b8346bf7f3dede0d78ae1a814200f64feb552271fd647497dc25a9125ad21515e08ba6988d20104779f199d9d97a852e9de5772dda9078a5e0eb092a7d1a90479a358a3c34875b430f177f9e0d5d34fae35592bda7e85b8dc4b8828200091b7f53d84b8ccae1ddf1513c2f1460742bab70f6bf8b5eb6e84b901ea372dced5305dd45c2ee6808b40e31b7303fb53c6c65189917f0c9de6a82552df2640800492a6aa172ceae9deb1b50d0c047fea790b4ff1e13d05c9d744ea85612b5029ebac304d95729cd82a5cdd957701f23c374ed1161c4584bf65592af1ef1dd0f4aa8a92580ec4ddfd16318b994d5d9757ae43b51ae7908b3fd2a7a2c6c2a8729bd0aad246dc1ca665e461c5069bc7bbc985b24cb058e4ff2dd9f681826b45a8c725c32cc3a1eabd16a9f83a568207d719393de11fee464815c51e35799b7246ef16ab8c2f820a3441c21e5a9e28dbde2b91ff9cb07553e0eb2a013b8cdfe7af0dcaddc96305d78aefb0d5da3fa336b4768472713de3d3dcbc04818fa9cb968a38823f4146ecafc5c28befe3adf233a81098d53fec7eb897c0614a9e8a4ff22d65682b82f0d66f369f4a8a8f755ce667739a4bc5a8816dfb27a91fe1abfda0034e4b4a25e49ccd355e00276b9d46022162b9d46bb8470f52c285fdca918d9b31cd4b733ab3630b52af0a7bd53528ad155ea9db9169791b3b0718728d701fdc87149710b9385e58b43f95291f111ec7c6f70b4590e5c2adf5c26138ca8c96e60ce1a36282b8709866c44123934c40cb91ad4b02f711a1ce2e879f6f4f5f6a6b1df5c93f5630ed278e2718582dff4aff1870668e92f074c2cf055882c21f7d6df28c7965ce9d0d37e237f88aaa240020ef344dee8511c65a6e0ea1a8732e9336f2af64522f23ffaac7380b2a465d906f6f3f9bb9a6fbbfc35e8503ade5ab4c3d897b3038484519953e77948c1f354b9e94a9384ea6970777045fadf54074afd1f7f00067c05ad8581d067dbf42abbc1153ba9d9e82274dc4b9b03211ee3200179081d561e6ff48aa2ca57c866f9a3f733974d27bf2603ebe25404fa1a266265069082ae6d439acd2e7141c66495fc2aa0efb0fc7aa5d70d7774d362841de9dc1752921a3a88c183e2f6c0b9e277880f86d76b8db5554fedb61919099ffa6d59a7dda3461d4f734b7248405f690c4e5fc2227364adc3563adad991bdaae94ba2ebaa566b0ca2b7a576ccb05fadf9374e30cb8f9ae150be860654ab4d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_103 : rowClaim true 103 1451 20361 :=
  checked _ _ _ _ 234 0xda25f14ee5e90b87bb25d41d2075559d052a7031493fbeeb4d15be7db5cbf082bba286e08edadfd63109d244a4f63110aed53f1462877dc0345d4cc2793fd288cbfd828cd76191eaf0f850f6c73a49dec06cb26e65e6faf40e78d0099f8a4fe5343c5ea0207f9fb1612f03b5cd20d2b5e2ce766e0e910688ee218cc3b47e291e97e32a4518d56aa040fd44fe82e4d3327d556d978340d1178c56be6ed557c00c26e271d8e1929b0dd840756d1b786008fc25ac2259b2c4b4743ccb0a0b80bdd782a406b31927f7b05d64d375a4aa47b4d3eced4b14e53e103fb67fc54d6fefef7a9143ea81de4aba4d92ea29c4866e43e2602f929be71f25e468d5e509d1a856ab2ab8e8784720c9ff56dd9ed8857888b16667ca7f5d6275e3d9f783eee8cb16dff517121b70444179797287d94464904a248c7bd4477a17dc91fc5310f218751ff7baa1bc6de4c06afe815d4eebcf6bc1102c00eb34e024386213038abb239aec13d5e46c6bf96f6f0a0eda1defca2ede8800498b450bb60ee895363b3f546660f6627b334162bbe3d5e14289c06c4161f56f794bf0ca8e35b906ca02192afd8f74838cd7c75e84a6e9576415978cfe24bcf3805f8845db9e7433e9d54528b93249812fc8d2c48393f06a621c9e967db0d211aee2f2930b3b372afa8d11e56a4228868e3df79112f653a3336f3c531a87ef155f152e8a38d00d1c6e76b3c1cc92f318eb4867ee917586faf1e4b285dc8fa52b9429f91709512375bbc767a2136b41bc8c7a833e503d68eb7916c9c3144d726af11bea78f95a394d6cd97d0ef3e44c5371f7dc7e39ca6406d9ed8d6b8650147c01a0473c89cb14528a2a2b3666a8b16b2c4d659af46cbe444bb52030b4f154d255a2abc5e9c2d1f1f4536d937902aad596d106ca896b4f2319aa5f3fbc71b49f965e07166471465f1d39ba1feaf3034ab7f4b0b9151f623da094e477b51bb21ae5993f51254696be8cb3e46dde1995ee804c6b85675397fa931d716e6ba9d2afa063f946b0e09083d446fb9dd7468a61c74376a47f81be9099411dad2b378049dac21f08b968d1c7607ae7bf931858c7d4e7c439c0fb2367798239050e28a5cd7c787409f9e68fba9bb204fd395c5a2f2fd74054d5153c09309ff35a1a943c30b13c3953a6d189332d6f1a56530ae786baea986a5d9abb88301594ae5d82ddec269f659da7431eb712baf9b949207841a4998d6351c681ad9c8a7443f91acfb7360a8e59b2194efe75a77ab8cfbb70fa646734ba6237e0c7de3fc2eaee48137c43c7cf06b62cec1109785ea8185c4e26554baf51e3376bf93cec8743a20a6644281338fcba092188f0d4ba078c0d1ee9a8fdb33a5e7e44f09bff28f2076cd0251eef0a12787d73b4c2688bbc4a12e7172275bed6708812d00fa8847e8e69b1576e793123c30413e7da0d3975e75656a24f500ab6294525714a974db1dc2c8a2691ff7ff3f724d231e396c3641b75e44c05980a5592698b868d1748502b4b98030edbadf03897b46d79f3c5161d1c7b6003355d5b87f276bea51fb336ab24b6d763760f1b95395d9ef61cbbac89228cd2164cf16ed5e580becf5545f30e9dd129ec6092db9335296468f78f4f5337e61b98cda41226831693ff5bd62f6f879f2e541051bcf02079edae6e34cb8b64510e2a359c805309c1762a908dd13ee06737e8d7f3aa08127b8fa9d69a34f278dcd2d6d31539c566650a4a5d6d5b11bd309a6b121141446d34db0090 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_107 : rowClaim true 107 1451 19600 :=
  checked _ _ _ _ 151 0x14ec44fb59ddb02aa7caa43bac4db663a1b5313e393ed42dca7c4e8a93ffbfc6f1fc71e0936f84b814cbeab08e53b9bc40568dbb4e342f9d086e2d89a5de60afe3b6fbda81e5f67180ee070ec3e89f4961ed2ee0bdeb53601060caf9ee389b832bbc7d1af800802a7492f01787c634bf8604fdf6b02cc6d25f4fed58ce7577a8400699ab4688764230d9fcc6fc9a3d913341c13a25755a96a22a232c5a4d5bb05661326a07eec57fd4765d59ac6021d899ffcf3262fb9bb0f06eeaf0af2d968a638cb55c06b0e8b7b53701ef05ee75be9ee8c6919a39137a0832f5514698cf46598ac920c4495b14b06bae3a3c40dbba7da8ec05c2aa43394613d7e3a425f827f619a2c14c341de32d892cbcd4920ded35334debbf68981914bdf2f1d2b704a606ce941e502b43f46340d552bab5f329d14c42f9b28f7a435e517f5d8d52c4e2ce8115d3b769ef307baa789e4ef70f1fe9065f0d9de2795fcdb1e6045e98f11c682686ffbac0d68c1cdde6e9d47cad3d9d1d72beabc08d6deddc7741018846c27f08665b2166a50121c62d460c9dea531d5febb4fc0ef529068dc96f6802dfb9bdabe7d93156ae31d8df66d83a21361ee5f37d9fea28c5f91418566f14e53c838c66f5da57d55bf0a29b79d4bf98dd97e649f410bdef24939633cbcfd32acede41f846ebb5aeea30c8a5e01496d68d1fad17090106d7f15264a6201c2822b8b58e047496da827e22a1cb4770841e53976d75e452e9bc3fb2177180d006f2be232ae6f2f42b3345ad40403b792c318cf49822f55187af85f1e563998ed2b10fa529281c514fef4e7bf78af202d43478407a9ebc0d99c55f6e3b7ad3208d962e1e38fac0030fb204c527402087c00230e8958df20ef5bda906d8f08bdba96cd66ac95b19115e892260ca51a13610ec7fa404f0734bfb91748141faf8578dab292d8d3e78922ccc2a8652b6d80bec5082b894c3f5c9754fc4ea4ca1086fdc3532b0d8b342d30c6b441b31e1181b27c8eac52ae12c2b0b3ce0668d6af037217e817f0d458bbfca2fd2a9950d1b0a508b1c54cc79e88527cce5992e2e910ada61d7a0bdbb1c3c2de38a0d1299af90cde794ea27d620ef491427851fdec1137a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_109 : rowClaim true 109 1451 19240 :=
  checked _ _ _ _ 160 0x3fb6f23a1dcacd86bf1be1c58cbe12c083edb7624ce385892b213e0fc1c6682d76d8dfbe2e938082cbb7beb4302900098bca17ce08d328aaa0a4bef6c0d9a7bf307727dce9b714cf2388eaf74ded83c795c77502a81b7b68bce65e111dda28fb02553a2c7d70c09879c4016a1350390db04a8a3f0d57aea4a70785a6e1d81326080368dd6b2e1caa4d146b123f9f9b734419818aeb4098321d85c7e7d5629b543a7bc20907068ba2fc30d3f7dd1c962533bee348eb7eea5098c941c357efdb333750bedb7d8e6b1e559cc3fb44de03a1d5c91373e0df09afaf425c49bfb866d0007d44522b97d2262c4bd456757d36ef7c9971653b7561511dfed33ea6e7ec3a35daa4c54d7dea2e260841572d020a5b3265f598f1a64756cc27899d7ad9b2d054ae4c982f52f8034faa1adf2ded772ce391b9fcb4e5c1077fd8c7eba6adfa1ed7117a5fa30abd51e8b293f20f6e4a6533c570eb90de7ac49ceecf3a0cde6a86811f5c6571f14a7f45099fa392218904b82b6fc5e5c0104d15f6d0a1fb61a71aa80478a7d8441f9c0e43e92794ab4f595074b4c5e852e2bb8e37ad61dfbaf7b70b880ad7eec1316aad0650845252c3fb310f516f4be3b59cd1a94ef4d94fd516c925513fec593f867c8ea03104bbd71f4714472f96ee34393a881c9ba8169638a4428b62a29b049c40309afd9d47d093b4c61c5dfd13880e79d78e0f5223e1b092520e56bb0aecfedee97042768207cb42c717e2a735d63202a0a91f49be07c7e3b5a393eee685c980390cfd555dc5eaff5afc0111087acd5229bd01c67a1de1255312512d7b9e6070969e69b42bccf90ae136ba5e76520f6db21367718404ca7efd92fb9d08aab2c5d96d606215579e1514a303de952e63493a81cc81c78d0766e34d1a4216c32ecd75ff181ebfca5491d4e3ae009318dbbe984d9cdd74041198b50c48ed8797aa38b5fb695c69c26914c2a3e1317f18107c88dde69034fbf922445b2b517fd83048a1e1f2f63855843e014c0ed31837db274f53b0ea42e4d574e7388b5c222a3284c09d18a9ca2bf9e4bc573a11a57b8d12e3891ff40e3016bcee52e428d65a35f6a37a85eb199162850db7cb80e2c1fcf49e271e3c443ed19876bc5c55b58122477fd1bafd66193b6f6a34db4dc348f9b268127c70b446df45c7f19754c540733c04d7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_113 : rowClaim true 113 1451 18559 :=
  checked _ _ _ _ 167 0x8ac661515a7e2adb3d9517f8a67f41341a297bbc8d1918d328a9a3c5fbda766300c455a1b6c676a49a92a3f8a2d05f7d153afb2fe52467f0dd6c64a4d632e4ae990cf31e30ef6eb04980896d79d4c67bcedc898ae2c13f7e0d3f42c026ce64657c3867203a3da3ad5ebb439becb7abbc1cf65e59dbeacf30e82b2606e539e997dfb0c24a59967b934d94e4b1bac8570c9cfadfc623513e9036772f1d3b67f9051742e39e9766f7f53ae3f56ce643c80e0753b6405e2b1ff226933fd2484e99dd86fada36eedbc044f2e54b4f5e6ac51d84d5e883c0c10216660a37c5c31eeb8fd64d890de8837cb117bb14ee356d1bc7723aac5c41f6678a5c58a8ff6bd9e35eeb3c7a8a4e9d3acf8d68c6ff318a3d637d53c38d066ab915125306e3333a1b9452eb11c579b69015147d97954738c15c875b7ce3a6209cba01d923c23be1ac2e9fe8eeb80f9180e55ae03a4bcd3ce7b8b2a69f8a3d44ce89108e622bf6175013503a4eaf17047083ad8322f72761ffe8edce8cecac801d4b5111ddf1a615051c7ee11d59ea224a7300b557fb592a99e63ee08d6e024f28839b0625a0e81d6c9adb3b92b052e0c3b2d70471f2bed75ab88de88ddb42e878eae8cae5a6ca12c2876ea0ac8276bb8868deb7eaddf6f1e8699aa84a408be9ad8979d210d63f241e1363dae631430b3eb2d91b9e29e4a1094f72cc149867c769d84e35d536d5211fde01ab0ccb7b821a59c568a8e266dc84bb4168e464276d75843a2cf14a72c1ed9ac1db635beb9cab0a2d0d3b00b088c5a29b015d7374aaa58b7e42820b5b0fc85579969923681f2f7fc8d195bd65bd0aa6fd530146f790d39af8b6c743f008ac4b61010370d15aea5d6cfaeaefa0fc214d0ca98cda72b559a1efb191ce85c48acc2065e0cf752deb08d93989a9db5d141f381aceda22ec54cdf71d3e7b43523370aea401b0142b38ec2d80055d105c1519461a89a26eb2cadc898fb58275148aad9686fab0a022577aac14b62cd58e725321e02bcc60950bc87f9ea09157fd5f03d1be48e5ac468466559a79f14174ed714cf06c4708722d2d1585ae256fb6cd8070aa18dc7b28887e0625a149ac0ea34e75ec1c2b83a7b817324ea96bfe8bba9713361d21cfb70e44803055e68c0a481939b64cad8abe537bea3647b7fcd152f4d5b487ff489dd1d780467171fd0b4d378e97608109749ae387a5cd64f50f842af6fb73e0e4040bb067400c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_127 : rowClaim true 127 1451 16514 :=
  checked _ _ _ _ 137 0x323bfcd2454d75af8e0265dac12e5f443ce6831e4a7b3fa402fdfb2d5a116088a6f8302003c46326853857365a86c4b98cd3ce59f0ef1ac46645e9ab066e4724081662f0c061b79ab7d60b65aefc586cf0fcd9accf997bacc7bfaf5c161f57301ad9416c09dfcd88c8e9646081b8913555bd0f94771b4b7cbc1ad359ea0a910f724cdf1193f6132cf437017114d3a350aa3d25cd6988ad3afdd942f6761bd95364b103b05a6cebb95f074f359659e91362fcd5ae073e3c0e1b2bdcd2b87a1113540cbe4902fcf564ed6520488d1ab0bda6561187381aa17e9d0483a59328c3df6792e5a96242ce8ad9baf31abcace6a28d2e09c5f31227c8422010228d363ed3015bfa6b11416a5839d4fd6ef6e1dd380dc4a2afb86c6322db497e76ebb0dbdabe7f08e406155811cce5209a37ca05f345f718b92e0c62be579f09384e6a84b24368930781253cb7ea114be9ca377e93dc8d6a84f4106dd11cab478762b596e6051818bc3c4d2289f36a9314fdadc6a55e78886895b871bfe9a9e51d17618a26d13a4bab9732679a0385a578110035fca7b5495bbfa6b7342feef0469a35b76af676524c93bee73a681771ad0eb3e3eaaf3694d377ba4b6ebea18f8b44eb4699069cd6b61e428cee9bbeed7b749d79470c57e07e248bbe674210f9b3f83d058fb3408372ce113e7b371463772b2a187b12aaad85aa3db97fc92b422e409c9cfe4f8c49361954fcc7ce58d025731dbb324611eb650a78e7ec422936ecf0e7a2850db9b9d7530259e13c229b70237c69c55ce63f577559b1c26125675f044f9adcc4b32449a79b5f7dc0fb15b68ec0337a04e7ec174cce525f2ff2db9c8a1fcfeb0093778e55af2f0279f829b08df936e98ce3b958c91d79e6cbd768f7146f826cbfac20bd390c7ec5237299af1b0d0f482b7352d922d552c480f1f9adb0fb34d92ed3e46ffa8a030d85736b0a84dee4edaf0b7a6a0ab497013a1667e621289e4e101416078c1c205bf057288777002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_131 : rowClaim true 131 1451 16009 :=
  checked _ _ _ _ 204 0x2e94a8cbbf88211717b5e14d50781e85b15cda4486e14001c644d4283a5fcebdbdfb08ed49bc7993fab4f1d38703ac245a78fbcb18a1b09d67201ce2de07ccb6d0d3428c3e01ab120421cc8291c32fb5836379c085cfb4ae7d3a35dd990d6cae7ed67153ba717a4ce6b593ac42841bc2dc963b8f46aeabae056bbf65dfaa42562f15561a8d28ef875ec9c444654b04068f36c22fa55e4329d11a17cb91c0af7f847c603bb298d14ae62e7ba03aea3322a318f0584a7b7df6dce4cb13d77157e6da7d9f9670b77430fc163ad2fc54489ad875a7929556483c488482eb3ee2dcef8048d8a7d33d548cb3738bee6c93ac6d2872c4099eb69ffb69b4a5da17274d4817ac7713d8c731ade3be92d7ab0639af69bd5697eb71b1d72d8f9eda6be5de032123234a01bda69d0927faf091f1c9d7a0636c5eb94760875ee30193898eca1ee0d93e4137eb2c49b0b852643cb376f9964c2514cdd9f579dcf75fdb383459908ab6c35b3e20d16c4360f568558bbad14ae1319cf2dab5f6afffdf4921060ded2a26c298257ca3632e312e05fb74323ee1da5182767c5347f08c8c07c69f8b3aae77e1c290ab1ef00879d01d76754b3ed3cd359366af3e00d6855e1a389dee7d42cb592d2088dc6a1eddd3f7199c2662194845d4a4edb1a8203d957314a2e990c8b86fca2155774286d87c8c1d9c4c5677d3b32b63e7b9d888e6d208b8283ca37d7d52a39e944553c27ee093a077748929a0e9f8e628dffd23187f47ee9e7a35dd9caac500de765c76a45e53c1038c9ca21741fb845c760c2c7338d05854cdfa38a17346c657fc8dab1a0a793f328aee151282031e02ea5fd4e10d576badfc04b5d21c0002068cf539816bc237a40e291f7735d5b38e1d26aafb9734136032e6dcefe90b5909ced774072d2317746e88d97c804fbda65565fa4558bc1f4963688f4b243af1313cf3ae749f1e3ed3e1d2577a52182f38b270e02085c3576253cf6c53aca8d34a635280534d4db08ce2b1bf0e5f46bc14025fc9dcac2c869c72716bea16dfeb30a80e94dd08a504e76bc7c5adf49bd3c730cb5ce908b69fe49893d32b84c14cdd6c7a16175a2245444d1fa2b879c024df8b700191601ead6c6d835c2d2575c67e2537ac6e566cffd653b4fa9d512fff6a7c334ceb1fa02cd4329ee7d3117503bc826a20a7df951dcf09800b345ac5db9547e558885b622aa2460975f453f7b1b190b8693d59fbe301ce42c456a995e655aecb2a6e7842683daf240c6cbe19cc48d3aa38a503c61db42e79f2125fd235741b75d759385432f0132b2681ccbeefdbc7150786ab1508cf77881d4f34b502c0bd9f95ad9d4fced2f3bda104bc11cc50d0364a374fdc09a1e1d647457ed005c8ba5dc97d820a4ed1e2d41ef70db859bf5dee2c5927931915bbf317e4727cceb81edf7f08af4d569ed1b19c345bb99e31ff8ab3ef0a16b4b7872afb35a6f4a1d7e13aae3348679aa8e42ae281ef53e2c3d60d2807962c937ce16c9c14a7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_137 : rowClaim true 137 1451 15308 :=
  checked _ _ _ _ 136 0xd4f5abbe4ab4497f94f9c74b390d6bda5b613f01fb41cc33ccd27f9e50a0e01af03119a05ef8480698c9468a4121d76ab9033c136ff4ffcff4d40968c68e24f3add88de890e9dc1c77f573ee90d3ee94e816f52d9a2017a0e6ba4e88ae3d8e9180dbcb03f8b12ff24803b89de759b88567e73a2826a09bd547f6268a08b2fbbc2c17a14a081231ca273f1b0ab1b9b415b8e470eba8815d1bb01e4df5a5ff1039bfbad8dae9ed4da94bf8e0441f0f779537c50ecb88bb0422d79f652eead5e8c1f20f0c7ef53317decfd8bed725a86a8182ae1eb5dbd6df6003a0ca4c834b9ca163493983047ef091d5c14e49f71f72c8a9b9176ad097c6c057449a7d1df10af07be690fd187d1aaa212a7db41a408e4287de149ae5146e9539f738fdb9c75b7f813521ef8d49d683ad8cc7ac8672db90456c21ac5a80f0c6b6cbed72cb9d11a74d1b7a966e048282920e42fc8969fd135b87a435cacdd5b54d8fa17e93efd6fa538087bf6e44b57925aecb114c6f54024fe27f72e9c37cf194cc0a9fddb0696bb40aefce8f80a3525600418cbee3daa8af9ba244f1914f1d75ace75505212d7502803d3fdbdd6317f5d752fcb0688dbddde174f5a06b8d91e5f583f0f4c82fc35b2ffae57bc3f661af8d9dff3aeb1e15f0e7249ef351e7f857a436ea29587f31fbae13e9e8c2fbaf437ef465074158c2e6e8f4a5bd6cdacd8d6e605b411fab7594aa572a17afa450e0a2811c7c605051d99c1e8c5ca33de96a0e680b38a06192c118e552d49f9f6337ed3a5b69560c94164edc6ac56d75dfe3f85f8337fd783440e7cd7e2dfd54e0f026603de97d1fb9be3ea76d0700d7d07da4b7ea8e88067fa4b2c128c44bb0d53b82e30ebde25346f63019786ea03892e68ee0584c1c27086abb9b36f95c8677e670074ba8bca81f1a0b56210ca8e34a111407bd90883aa45c9f6162ef4f6360b964c6c51c852b96c02f7dba04a8acb014a34fd36615a286434d3706d8000e16686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_139 : rowClaim true 139 1451 15088 :=
  checked _ _ _ _ 165 0xaab3a5a52f226af4cf8b33ca1ae5e2ccc265cdd5e0654cd75175fe45b3e901f5fac24829c0e7f87d751997cedd8585857d79410e339ae24d4844ea5818337b241fd2c8b3ec2ad688b74cf032e1b005901005e9797ec337cc7f14e6082d617ba0ce6cb7fcaec71d60378801c8792eab64be80a65ce8d53692ea1a40f9b37bbed93ca3d2f03cafd3ffc8a3728260590f3963cc8871902cc8591a79b56fdf6ffcb8f131d08d773b0538ce8700bf68531aba0cde917ea14bb754af388b2733c25359de9402abfb662b0812ad570ef6e5724811d5267101b11d10c74fdb454b48d4c242e33fc4c1c92b9e8563dcbc7ac91884c37a70e554293408900a51a009143da52444f0040fd3d5c44d52d26bba28b0eca6aa17494d8db9abca26268d1dfa39cb510af497c96a59c05ad787c82a4588a09c211683ec93bd024283aa2d193d2d1d9ab64045800ad7ef4efdc36dbc89ad5671ef198a230679f8812dffeb5edd2091a9b6ebc1f52862be737bfc65fd7410bf52882c1f33d97807e3b236b22ce2a66648410f432d1d91f5e8554c67933a4953fcdfb1b2b9e29bfff33b93e5753d28bc9eeeaf311d81777fead5516fe9f3603189b50bfd5d6d74b0c300496ab7509617e1247a0a90699380959964ff9a64bb975836501ce5d9fbd2a25238a6cc52705b3f7afe728dddc89cd6ab9609cf4c8991d0c7aa77d7be86aee242fbe336d74b83fb9993cfa718259d5034605f274bb428987f7254fb7c21918f81e2a91e3bd7fce3e6291bdd99d6e44af50c29dd5a37d4789a9af60ee502ab7f0e2ff3383d0cff4cc7058e15ac6fdf854001d03b875603b332a48c9ba19b6199cd0c9765c7e09665b04fdbbf7073a7ae854adaed13b1723cb14d2fddf08c03de8872f42701dd4bd13bba5db62634c9b3610453093ce69217e049f42a024ed9ea67195bb9833730aa0041e4ea5edaf8adafa7f324e74cc76fa76aa904c0c2bbfd7715013bb3511d05e86b44b741af6b8405613395deaccf5177e579461bf6009c47af6217144df84f041767859308fd28fa09e656d5287425854c881904c0babd135e58c7e0d4e48aff5944cb581e7b5e38a2332af15c3e44d5e27f7d8c9e8e87ec954063c1dd5ce86fec5d94fdf94869e4a409e7dcd36b6ceecc8dc7e53c6b2247f3a8b665463ea20ea87325d681a27f1aca6e27a723d338e813569a54ebe62d114425d955818ab49c4837a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_149 : rowClaim true 149 1451 14075 :=
  checked _ _ _ _ 151 0x5ceba7cc23f7fbce214e039f4d241fd4bc440da36612de15eccb90ceb7dd8cd9d596acc920934fb27d5c2cf5b042d4d203149ff257dab46f86a157c8ddcfaba441b8b22465f1a79e27e12ad4986c7a5b5239b0a77172715f8ee686caead99f4e7282cdb6b79db0fa25c643e51c9ec0be04a8624c32fe76c7c242315eac1929786e57fe88aa192858b8120ebb89a7903da5ab777e8fe46f98073ef07b9b109edfe7d178848ea443de2ad4d367b7b47c7202a9555e018662ec6196dd5801265d70bc6506f2def4302a797b237550d1d04032fe843fc88d11ce4f6d55d5039c6b383a407a2ca6bb81dad12821b8daa94153d9a2948d431fc9694aa091b8f9db570e1bf9c2fdc0aa30f75a719c2075fbb5766d6d10acf3ed4203061470cd03f9bac977b4e513ee6f5a40c4fefb12b3eec7280ec1802f60abe2bf50e01f3a842ea45a7ee44dfdc2ab32a1747dea12ae1b68ad159dfcd997e4924ee4ad78d338a9293c9c044aa886d277160150b3c0b214ae58061362404a39f922980eccfb0d09da54353a661c20ad793ffa8fbc815c6bca43003f7b04c3d536f2810af2a2cb95667df7c9dba2229ef2dccc48588e9595be7b9d185b500f19e628abcbf50ad3612915dbbd3950c9bcf5831866ad926d7094b9c22dfe26f6b84baf358ccacee810f380f8ee4536e6ce7a6b5f56a8d9bf8a448d4e03cadbe7ffb80cc6faea76f637b9d00631c1fc27f3af8b5aadc535089c34478f7c777225f67a2bd48d2f1f8c98aff2c95533ba9c65bcd426dc1a6264308ad6508ad5dd6a61e91b25a068e1e2ae913c58a949451424532f0829eb758a6a08a1415b94eb804517ad7bf6535266e78657f8f12d82513a466d246fe5295257aefcc8854f31c86fdc1519bd4b06870ea2cca881516e3ce4b7151baf1552e3aaa77aaa056e23881e6e0070c31745503b47261d4f9b4d23c76766739ba85442db61c63cfc982331c5bb54cfd52b2414c1ed769d3ddb369b5c7cb690030d5abde0b5fa9c8f1583ac59480369e62d7e2c2d615846c5e9e2ec9bf12c1dee65eaf12d4ea6d36b4cde2a0fa1d4d778e12b81be025a1f34241c5b9ec10d9fe27abf854d20aad0e717e0c6f2b1e30058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_151 : rowClaim true 151 1451 13889 :=
  checked _ _ _ _ 124 0x168fd8457439e8139d0d94fcdbe2aaf04f7093227b6ab41bab24192debfe7356e0e775972a3af0403c6b9ec48b9dfddaf474f3378eb345faf9a47fd4e5c1101f86e6964ad1623a5264a9a336a55d651911354d87c0cb9f4784754bb276fa698b4768acfeb67f701420a70b100c50b6ca30dfa190069a2563be668712ee848d62779bde06d362585ed4ad3abe81a66b791a697c9d0d5033aa032bbe5bcef0c00fbc41b8edcc41da1bdbe6a503c15841048d52b6af393e863f4ffbaf55056209a952aa304ddecafe45077cb58bb339fb9d4d7ee96684fbfd1e68c8b4690c8cdc5b1d20c317861d0bc12fa85c1583c497c24dfb6e753f375e0b65aad81a5c1092081aa5fbe2b5a59715904c8bca0cbdab4e1329ed8b587ec043d606e102ca5e45ea743607a5079f8dc797afa5246b6db3d1ff1f398821fd48790067afa658888dff5a22069cb02559f616f476e74e66b7d100b516031d564d7d6138f22161d180bc46c4944b37dc1e4ae3f6ef56982eb4e68e421984b82e6c9e83941b801aa7ace39f13d9fba75b6b43a674e96649b64451cd485dc957b277ba3b4e832a99cc5af137226f7b3742f739a9f70cca394ca47740cdc7b00023f54e89e85074680ac44a6dcacd5720ca1778cd633d13d69e82e134f02b89e938e13ab36a22db406e94493feb7e02c46e2a91ec14422ce24834b412c3c306d392037fe8a18025d413439a9e7c04fab60827c4091e18306f3fbe6c824017b085a28e52c136fd1cee2c45df37b304d0c98e415d52c7b5bbc690c98b8814844e6256b001b6b6978da799a6db76bcc846f7c9acd0e38d00ff08a4020d405ee07e16a4de9820cb4398bbee2c5d1adfea8789a6efe09fa3780769e73c076cbac0f2de566314e98289ef17c305ec4780fc2947a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_157 : rowClaim true 157 1451 13358 :=
  checked _ _ _ _ 143 0x18e8eb7bbc4aa1df7d5b587604c9b6a495acdb1f2778ab488c7902d4b1425997b939ebb8613f28ada64590d36cadba0be47416d55b44e57c7312052a137c4862dc179068e1e3ce86e8815b5c832755eab153aa6e9e316a32f20d2f6cb90ba97d0e2985bfcf403a34ae3b0196d1880b0defd534b766e0fb7ebfad7d3ad0b78bd2aec98a2c9a1f5e7abce89e154e805550f54999bfad8cab4b4a2e1eef24d7ab4b23e86190710f7f1b5bb6e15c85f7c355f510a33c946ad04172bb5ba529454eba6ab928db756bd797ddd6397e07362b3677615baf1cb9fa79016efaae5c2ecea5342b2d9cbea562697ed1d83ac04efdb8290e3418d274751f079ac5e8e7c346f2da1f7ff18fc6cc0b3b7cae7c91729e1e88869e6867cfa86fbb8172df3e7dbc81de42c3feb974e7e57be6c76f67ad3a1723fba916e7014b5af1980ce490830fc94fd80a5503bce52122dcd555780876140a0f412d280e09b13cb49e15f77446f21261bb98808637e867ae800f454db3c3498a6426edf76e53240f678f33825d69cb04cd19532d004ba036746e779ec9544b54611b91ea3f82ba028bb1a0eafbe75fbae6161212278b5517a1373da9ec09048b9a351f0566f69db6da2f6b1bc4831fe4436c456af87f114e683a21e57dc1cda5a8d1ef5730a2abd78d3cee5182f8a642373a7fd447a2f01fc79beb243881ec2a7eb2579a601fa80704a1e8b1053c9b67e0f7fa6ca66cdc0c489d70deb99f61fe0182541ece065e551b4fcec1cb4886441fce13b6eed5c3f076b1dc39ae82b29b8ac0b705a7b806896edf4801e3f74a32a982e42353739ebc8a78524b631fd30df879b4ed7317368cc8898df78d50c3344beb1d7df4a01ecb188cba8fc8aaf7ce8cc998a4a3406ac7cb0983cb740413d4952d3006a1b67003065b95c7c98129983b570c2d1aa4de182eacba8371cd19d8123fa3565658363cb1aacf091a5b890ed5fd537a02834ec72c1300917efa2eaf71f612ce620d9c4b01118ac1a2262ba2db73ce519514a213f6599adcd024f8e1688dbe8b8ee35e29a835b2f02687e907002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_163 : rowClaim true 163 1451 12866 :=
  checked _ _ _ _ 162 0x138e7f1a5dabcb89024642370d5dae5d663c307188ead7b6f739487145a42d7bd63444736e6dbd9f743be258d4ecb6aad2b900d44418ed6cb89e6186d2eb26b04fce7c6d6d971b3255c2667cae594783278daf3a070ec9aaa95b8de9dc1d00b8fdf14068e84599221987257f0248be1fe721f8811da751a78017cdc31e06169e9d0873ea93a379492a3454020929ef92e07d330a6d81532984a17573598a9b41ec697ff2102136f8fe96e5d62e3ce83d77bd47e70bd5cbf156f09adc295862910291ad15334d4ab572d60386c69d2d1c448ade3da03f60f4d74cd7e73918e488bea74a4ea4878f651077a75aadf9e1cd6d4e441a61a138c713f3c71e013db8c77a89b13252ea5cb734a1f9423dda1db6eae6c32e9f324486559a8e1f9c69b915999bc9de5b40f1526f4152dfa2a67a6f48bc932541157ddaa2811e38b214e60cae16e88437a0f1353877bd4cc3b882193dc35da5632dd92b57be8d22f7a0983ae2af85dc2c31b9c7680d499a49676d71de17138fc48019bfc04293274456ce043750c05554ca2041c9baa915be633ddf9a825cd920076df47dd1b73703264551703d42451e479ad0cf8f4a950581fc940570d8f3077d145e23e866595151a40ac6bea2a3e618d06117b34ab91bf2ebbccde3e437b43784c1b4cb103cc7001a6a5e72949e91b8237e47e6fcd131faaf6514092f600c7a0d506642a133eecf4e2106c440433f781425d283fe4ccf89bb9a766689b4e08087f463c242cfcf09ed557ef09317cdacd1dacaf463e671f6e94bee668f37a495c25ffdf6e80663942cca2040b016e5a240e7d7dcf31242a1de75756bc668fd5aaee0a5d5c931e0d1b85ff46820cd8a8ce1cacde32c263f4402946ba4c1cf2252cd23c229881b213063a5c6fe4da7c053880ecb1619a73a21d91ddd7f48fb606ef989db360758c11f30873f49826ad26489536afeefba1ee3c02044c5ec03c06314887c5258aa906eab7f60305b8162ef6f9f36b5e4755d870b319205cec5762fa3f7863b70e6b5758fd0db441e7019672c530b029ec1daab7620c64dcc3aebe63aedf95b4e6569199a0261bda58079fd6e01d0eefaf1182e8661223e26e176a9c702ed2b73ffa85ebbe9b0739723b5f587b647dea6bcdbca1e09a68d6a71e92b807d474cc0ac8688cad82c346dc56d57429fd45c1343bc2b57a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_167 : rowClaim true 167 1451 12558 :=
  checked _ _ _ _ 127 0xb9a4601633020f07273d1ce7baca5a760e1747a02b306ca97b3a8d89196c50c825c273b1cb6aa91beb9fe31eaf256c0d2165ff33f6a8ab33cf74c574270beadf4e4dcf3d6edd93060ca1b2a1b710a7de5d9455840ab0e9cf0445f3282c77202c12d3118c0db60cba04bf9b52eb661eb6217cf4f0115ee12ff304cd6f1e6d7c27077415252602285978bbecf20eff83c642c1685dbc4b017caa3cbfcc6513b44e0fda2bc6d9528d45bceca6b80f110892fed6017c131e9da0190b720933a3f79762448ce01d2ca92d316090f0c4858ae50d39de3c3e58cdf26bf289a26ef4d31e51e1f812d614f81ab64aae97392847e3dea5d1df440d9d84203590e08997b701fbd55b74d49b0841323fac4193bf210aee2d4190120e6c9751968648efab0441d4d661a8bcaaddb596f8fa641fa0be548c7dfaa3eb1469a4e7caaec81ea2e68d3ad79a9256df7b6c8c79174e777d5f86e2459dd8121a829b9fe99d3a6073b0e36ab9e6b19a88ea0a8f19c3a213b8fd58b6e14ebb895da0e7c72b549f1781da1442f7b92246ce9391cb47145c8d16594086576ad9a0867846acdcd42c3d2970d9c69e6707fe13832a49d6aa69cd22ca9b47363f56ede545c56472646652799246b2f7a3b4f6e9f2b856be0817c925013d511923583f8d09b1b37a7905843477ee9af78594c8f29cba0c4a586222c0b79ac38e3235e3def2dd4847faa4b481d972fc771d68c4087aa37406ffdc4c11aa2575386c67ad87c86281b5c90acd013a58fed69e2955cfb27c9a4c3a0596115b3c02961b6d29bb438020f540e5ef0e9db450e1ffa19c39ee4ad6a4bce4f3d19d137c2e191affcfa11bc04f99b971148ba0298c2a29036dd0193a4ba8af2fbc88e2267d7b00e8b11652b266c20f0030cc80330865715d85aadfa40c8c92fa323c6a13156cf5f00d80a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_173 : rowClaim true 173 1451 12123 :=
  checked _ _ _ _ 141 0x2bf8ba84b8dc7a50229d3cc702de7a71311da75903329f533a822bb94a873c2cde474ba63868a2b8a0aff6e8b952487aab6d73bf7f71f1316f9c5ea74dd42b728844fc3a6772dfa9b257515064dfbf0dacb53905efd390c5d17f7410ce9ce3b784a940e53aa1733a6a012c996081fdb35e5428315c56688b681f425705ac80462bb2eab1428a7e78effb813dcdff6a7140c777880355a313db851b4e692c13a78e581059494bb1661ae1fc8a64cda2179a291af44d64d06e7137f7c42c53fe7cb8752a94087fa3791152df9133d65008a707f366489a82c4b78fd87384b33ce58782d175a80026aa74c539dc030514c66666f99b73a09fdab2ab0e30037c4552d4e88294accef5e40958ab008ef81bd3c9ed2cc7c198435acdff5c5b9c27581826888a5298ea9970bbbe7a2f03a04d68f556b9b18d6db9f677812adef9fc89ef9e4b772de6e95f6c1d0c9988a135caac1dbc0be6176af6d0463c20fd53445f05aa332cd6310bcb3e67bc10bdd62843cea2d79b140a4cdbef3a8d56318614c67fcd979cd15f70464ad09545b0fdcb3d1c0086ffb5380427d9a7d35cd9e7925f2e189457af8e9e8b1c89c04170f6c2130e94cc66d96acc7e463a996c2a348a387e5cacd65de8df1dafc49d942020da5448379201d194a5757b5220251642ad1aa2fe407c77a74f2897ea5fbfe05c6cbabcf30a8978f20bee01a2041d48183cdb02e1ada1672beeffa3e414f7c15937658c353f46f73f48a5595da139e06e494099124fa28984ae9e4a1c461001279a3c79decc07db1712bf36e11457ee0686eef08722aaf6819b10d9082042bb676f8906903df033d3450b40fb8796467401118dd8657f88fcaada1a5dfb77fe30b5a588a52ae06169b74d791fac1af441ec507b9a8b1c1f48d6c7089016bb1a02f9f68eb89d58749b878027ddb7964c4430ab2924052ab50fcf14a61fd1c55a6a4e06ea6a4421926c26049cb06d1198ecc2156087b247832ef18b07643c9f3c55e3bd8b67cf068f8b13d9921df680ca9ce2f1a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_179 : rowClaim true 179 1451 11716 :=
  checked _ _ _ _ 113 0x309168ec82ba05800ae95ffaaa09c107633f29389a01229b527435bf2edc2caf384cb87f0cae46ce1aa6e7d30668cb52335bc3eb5900d057e9efdff8a2b8b6ff2a9325e2c7cacc57d5dbc6fbb27c4c75a6f0520ceb430c4afabb29ac5692cba6bf3851eebad798116f94f904c171d25f2987eef2d64010f7fd140f2a6118383d95471c46c7fb6d6523500fddfd6481a40530a3b9028a007e1a3b1090662cf666427f85769b81cfc5ac2abdfbc8ccce63ec81114987b8a7d28ee982975662bd90eeb846f3d12f7c42991851e0e50c790a33bff4d06b88dd69a8473caf5c3131fd885bcd7ca7b04f2fa0f6877f9529857893c911f00f5737ddccd1e030726888b2d81c20ce3dbe12d11c82a34af6bddd90b7118f56916e91dceea9b3957179c4b0a41d4b1c9b72d794e06834378edef5b0a60a3e1210bc338578f8a14636ae3e39053a75d5ac9fe352586a6074788b787ea7c8e228afd425a411c4e789fa023a1f3ac1ef1662f5977ff433ca6075210b105d27a8429c59b6ba56eb81059415037591075a90a4031610886978602b6e266e58cc8d1acdaaaae0f8050a0581f0fa51fb70c70c4b20c60ea79189a2d22a89e32ee3aec1521110e57e31f22aeea0835b1e1f9eb431c5750e922230b92bc4ad2fd3b68eb92aa0ddf07f80e0aff1e09a14fa6f898eedc04f226fe7a11c6b5671b488be4c1d99e7f5758d53bedfd10e0721fea17b16c9a14a30f5f33b9bc846d5a10178103aaaaa10f9e0a36bd9b14d904123d0f9df68c15669993f26e47798113d9891a4e5f6a616bddc295082ddfcd54461279477324107b1ecd706f00a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_181 : rowClaim true 181 1451 11587 :=
  checked _ _ _ _ 139 0xfd911acd8882998b7669f316fc46850dff6be396bdddf114c3d75b30c56596322aa1d5a7286ae3f993d348101563102523f7568f21335d2eb03703e0a1f1d5156f75af084c4d8d16fe63acdda37b256b8f7c8ce6d152bec8b5d91dd482053a6f09e3198fa195f71e49f11789c0b566f4a75da50e4acda5445608d3f2aed1142c31f53f4187d4ddd41bc7a0e674c7a84349c975b18f7693c4e53c50d87aa0bc99037f41651f2bcecf0adad3ea1cc1a4cb9db312237e13cea98182c32ad1e563f8c18fa9096ec2e1cddae620e318d341afeabfa4f62123b7a566a055d2899a8fc2e644b48f08c0db1e8ac16ebbb19df2871841f5e4d0bb2c98a54fbf3d02beff367c433497af84d6ccb90e2d2654eb084601986d4cffcd7c64b1485b37f5feb93ed997ad2bf5a8ee062776e43b58d5ac9a2adb1799872bf0109a816e1aa89e7a991596bd67999f0156e871f38b728bb5b6f738b7b60856e051e0f6a46cc4c2734fd5c311ed6934bf17b3cf913b17506ea70c55b451b1c07a823632ee7322ad75b23bd4a7559d34fcd5be56c94b5b5efe608b882776f3c83f14a0fd7f295edef3b80ac2d51262a2d1a79454cb0a1a65c8e489f94e4dc19a1cfa0dad375821d0e35d084d57e20795942d1253f2e9545941ba692c50eda53aacc22a9b64c161ebfd1ef1495512fd37224acb8a6c123467ae4c0581771812b7b8a9d71a34620b677437b42ec57c416e7421ed2154dd1276b733d15bf021ee9985eefcfebac3d2b0ed6d4374d11387e06cb08bee30e79798194887aef19983d9faebd2d40c286e6a9d06f004b434906190766d40ed9d2707d2a4a84d209bb0a93635ad4bfef55d88b788be1f1dd35803c5c183991a5db11b6159b8827cb2344dba270d9654e8bccaf2b92d720b36eadfd7e503940d42d332ba41338ce7cafccea2644cf88fb4163d8d915a90c5a518770276a2d0aaa7b33f4e57060e0cc5a4c1a99635379b1bf236f8fae614fb9174d71f7440c6aadf71949dc3e413661cbdb00d0 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_191 : rowClaim true 191 1451 10980 :=
  checked _ _ _ _ 105 0x52636f6af61c5bd293508b1c2898ec4292b497f8cb28b8602faf1d54f2973a282b86a859e6a61d22ee32794851c1072a7f79c82928d1703b9ce21fc53993aa9a03e074d37bb406810711d8cc76eff1b5724dc96788b7a84d1abac7193d44e8fccbe1e117b5a8e946cdff9ac803e8339af8df2989611e39e05c1031cba03ea0d0cc7c84678efc594fc777621b98d73fc333ca583d70bece814ff39960d2c93a0a264cffc0876e66c7242d702ddf92e8f28347ed9cdfa8cfc4c65d9ad2d1e6b0694750fcd01017ccc45ce5925317e12401ef5cfbfc624cabd059a8b96eed1958c66fce6b22e6e3f0b5549b4958404ee9b328948abcbb9c29b034ce0c31ae34b8f0c1d769517ea53030db48a608c32b1f4d22dabd28c9f4e3cb4543abce0685d6e97621eb08970a92b7d97a63f50ca6c1d7a91b76eaaf59daab76a477b19ba84aec1ff6cf7a7f34b00569ecc89a1b6c76c36be01acd104bb0608d1143c1d1c356d7a9040bd2bb2ef3ba98759f44a1011cf8026c169377d3ba0ef09640e40ee68d0aea3e0b4b17a91a1cac2d971ef4eaa6ee902368b1cc1e49de2078c6ce5c3752cd53e60be3bb480b0e804edfa53e9c61ab11001ef5a66cb6726a53151ce63baecc7d933238e65c3193178efcfe0b7b2e1b5ae0a982905c2b77434fb1585e7d09dc72db9dbcc32a68be7f1847765bb7a4d7974ab7d54a2febd4f1106f33ece29a70341d30a6080a5b87fb883a6ede0954bc0904a7770c29deebe1898081fc1010e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_193 : rowClaim true 193 1451 10867 :=
  checked _ _ _ _ 75 0x65d7dc6d77f7526971f305e520b48833a8312d9fe1716305fff8b9c5623467a9eea19ac03b8fea2e3470d800e92c7469b04d3f506230434ea89acd75c25adb00057c8220b94692d3973527a082e11f733486c553d4e29365a6a032066f7c9e5300ad765d76cfeed7016f915c52cfc525dccb275cc0845a03458f97891f869a6d5eec5bf74c6ec3d713ef64c4219d9c715f4dab2182a720a800965e126b1163c7b4e5cad305b76778a84d3ee89daf39ae831159b86469f656b4fbd42bbe851a404b01e6562d463192ef161f10378bc17700c60a80c0f07772d614eb956fb233e914440279c4ecae7b7e039b3e4dd79905652b98b020346b51567048c18cd5bbcffed89ebee485c75d387b3566b05b1021b4a62cb24a29ea45f82d71d80041cc8bc360625ccbad72dea1ba0285907d34174d7b60faf17215eae1494134bf7585198eec8432592817b133335b3159a9705a10b5398099593fb0377377d641fd7f2203a2536110895736f5e466104923f13d9b99f2d870bd944b51288ce08a2b02f000c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_197 : rowClaim true 197 1451 10646 :=
  checked _ _ _ _ 127 0x4f49bbb8a6b06cdc77659bcddcfec693ec3c3913ddce8362d88c20658af041c7d1fa64a59a344005f130f7dad3ae9dcc9df630e5124add24389eb425032f64f6ea2e182ffc5fec9d2fa04e34028433e6c27024faf611782e3acce9444c2adf3c77ffe244b803be1d2a3d5ee0cb6c729e26091499dff350dfea243d1dc6a50898c5228fbd18123a6dfc9a4e2b4ddc176d6a9c018a96b2432d03f91393211842bb43bf533591f66a99f1108a6d94297bcc48fd0deefdc9fb496e4ab9e33f7cb5ad78ea6d27c098ff664989c89545a2ac877e160331b7eb1e3e0ff0096c5717a1209274fc0443496c935925a914c62415efc3aaccb865b3e7ee329bbd165b811ddd2d04458ee2b322dab8c3dc78a986d98ce64a73b29c1bfad015471a42119f4ecc7bac84e311b6ebe45ebe9b800025569ac80e2b21a4110e32d50e104702e124c4710306f5fd801eb0d8ba2c80b9de633bfd12a9ff33eb5bf8c2c2503c546c339e28f99098f0cf39e19ab32a0a0a4e2a677c5e83d6f6760588d88df7e47a3fe0aee4a2dc3498ec57da747b7a44b12fe0b30f02f9c9c8d89cf5931703baf1ae3d5b039a77664d49b453b03351a847a0db36d87c8d09d89a2d4e1bec503fb4459fb274636140f08534d9c5ac1cbf293962e16c7fede512fe19c9977b365c1931284d23b49d39e6a3619ad889d49f26f7541c7e2ec96d9b38d4f0aff2c4b289c7e527e30a483c9a4635f032556a5e44c8b648630dba3b149ea48411014b4c93c262b331a1b95b3c2f8275f99eb57b9d25d564d2b8280f6fa8679ef84cf3a3dff0b92314c9bbd77ea51d9de08921dc1d2a27aedbfe123eac2d01eb544d98f0f5f2bca32b9eff0a5db043e7aaaea13acca3849fed6302e9a5fec809bb82c1c889d534d4118212675aa28a0f49f743227392ea080f86a0ddc06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_199 : rowClaim true 199 1451 10539 :=
  checked _ _ _ _ 130 0x29316a4a358dca190d388e2e42e7e9c9abf278511c067947512d13c6b18f01874fee0f06df065fbeed7053d0df2aa27bcc744ca2597be56f691965d5144df27e32ec25fdd8a5c4b0681646964f26067b089306fbf28e85a804a7e04535aba6f606538f149ba3fdcd46fb5834e131b2a42a9b66e4181756db2c64e8334b7929b8ec57f65f307985603ecb5831a957baf1a1455d843573c20e260b18136f522cc9d5905016056fdd6f57aff0daa4897d0862e6dccc32a0d222c0246d8017637fbee4f28d6d7f5c1d8f1954874671e8cdb0541f55a7428e25c7476c4cc46862a5bb2ed14b0986265fbd9eed4b34a80e36be71b6c6328f944bf94d3cdd2355a1239c26481d191be2d039cb6c26c44ed878f967c74894e6f42e640a61031706f4fd0b9eda1937ba7d85b47cc1131dcd5ac195cd864c5235493a445332601ac81b160a2c80577a4199ae4cfb5d0972df9475933934b086b9284bd1ad5dfa55557a00a296e9721a52d0e297805136e38f0d84477b284c07d09ee986fcf73923c41479ed071783b5fc31eefc43f7aee05eaba02677c03d4be293c3edcc2b52a54e9409f199d0a8b6fc002d38433d8ab6f41ce8fa883663e5dda9297dda5b745ef13173d02ea002db39687429012ac55064f330f6683efd0ca27f720751468c2b8180f575a625bb7a29e1643fb28c2e4f2a48a74477c9ea739fb431db4242d8e3b2dacd9b1d894ba79b0a130d9bbd9094c89bb259db8d17e030c67d684087f8a08f12464c696a6a2153176f9d0b61169be0386613a8ad062d7af7e347f7c630ddaf62713c45205294beb5f490738e53df28553ece2fd50243a518f4cdb2c57197a309ade733c2e3e61ce223faf09d985e794f4f9a1878f0d368369e232b8fe820d2ef3fffc2a421541471b42a4171823a26356ccaab4377950a321cc48804f7612d2dc9e0c15a06c7b88d1260654ab4d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_211 : rowClaim true 211 1451 9940 :=
  checked _ _ _ _ 143 0x3046ea6e4338c2ef5ba5f82fe96da9fb89b0c21e9a3e6c9cdd22aba2247ef4a4c337ce58f1774b6a184b58b21d1215e38ad1fa25aee7a44ad385e0a9f7ffa8913422179c26bbf1a3918a9c846b77917d477b3420b654af25ac88186136407a2420baafa39861b76dd2c0bd6251ca97a4d2b2549cad29d3d8234bb5f882a97136afe702fc587a917eecd5a5bdeeba04b4a47c1f103301cdc6596a34e207089590da2df66ac1aee5c8de604d28d2dd37d8d199660160b27f73e260ea88efba05ed35693187560fc82d7e3136a6ae2d9d4770ab5d54735ad916e73452e55139ea36ceb289b174bc3bc6326cfb20c0757f761e3c5dc98a850ce62db781bf6299db02914b0a1468254f6b4a3cad2592db9dcd2a3e00ec401de26fb0e0dffa528942ecb48267d2fceb496b123b44897ef3af832952d84aad004ce179828bfe416161a8c13b9ee0a422dd69105ec23af4b64bf1790d7e2fece51b7aa72144adba04154778f8a725bf18dcf359d43ca3ef77e74d89e58f8cbbe8d9fd45cd63a53799d0a8244184cf4d4ec5797efbd10f599c8e9a3883a6fed0f090dd532ce4c850d6c1ce82fe2ab0b42cb97c0306b50d1d34ae0008ddba66baac783f2b3a7b4ab65af07dfca7372110185eb70b0bc54bdc8203566234c53dd0c7197e19b362c0acc4d9358732e96925d571cc1d194a1f97483cc1bd0fabe8d81bea98e8c90c25c0f5c3f0f1654becb56ff50941a53aa2a80cfdc97d9756bce63013109897e88465e4a74b7c89db3ce63b18fe44db71a26aec3d80ef51c3f764c41b460519f52d29736ef5b093303d0a07b8b57815113db475d6a01575b31b59e45652b427b3ef3d2c1233202bbb04627537dc758ae19af1a0a5be0aa6c36604314884783ffdf2d51aed45d7b15f7587d37b7d84e4dd9a1b9c9a2633401c0d59c2ef4bca4bd431380ee5455f69519706653480daee8b6a2769f6add5a44bcc19867b0038dee72e6cef937d625627b7395b5e7036c2b23371b7114c375a28b416cc74cdae0962df77265355727cc435a8a1073e8ae30349ca1a7003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_223 : rowClaim true 223 1451 9405 :=
  checked _ _ _ _ 142 0x12df0275f069f82c778030299750cd5e29418f523291ab8b61cc6c9a09b6cca3b6968cc97b47407fd39f6fc23f88cf124002ad0c4e79aeaf2af370caf44bbdb3518626d39524a63ea4fc94d1d340d7254aae48ce4e184a382c84837738d47b7097f3e72e4738567faaff5eb818b31d963b2da2ea8d775d3dc6c38f18d64b30276885d070eb6717909a26872dac23c361ae9491361f6bd006989c050ec98a6a7574f57e615b9b2474812fb81ab7a20779163cb1136d3fb127f4467dc3a397c0f2ef90bea78ac2b0f68a40431e8825850ebefbf6b96f07c2f7fc4b45b24bd56ee9af9f721a20852ee0aaffbdc9672936a70736d0de9b45ce54418835c0a5de8c39d8d0764bc7ac1350ec493ee1770b20e9ea1930e0b818e01b9c348d9502af617f700c900449ddcfc2cccb5843138ffac0abdf5a8a4b15a137c0135d6c3da1eab7fa592af9e7ee55c8738d97db4385d80aa70afb1c768afdde2f24fde0451db8c5dc5b127a47f3f9958d1353f9a3f6cc68728d1056f5bb0ce59d1a3abe948dc60964e860b6e573b5e37758ff4514e570fd1842560fb3be376c44ce9fbe334f1b4a0f6f15a55ab816f8d56fd0f5fed36c02f283677e65c4ee244348aea092197781deb177109bdbfd21b62774118d18c933f35722b47fd6d0c6017bc263edadc99bdf26f9fcac7b7f887f07a61a1b1831b4de2f58ba831af59d9c31afb21cdfe24e1a21ebaae7c2c13a22de523d8ae06c4f28f9f1bb3c56587d2d4fb481aa424004fd0f12e0ce91ebf03f330e8332d1aadbd93ef5d5af7a76fccfdfc92c0e6efe0300a57edb3cb63470a2f6823681a83fd9c1518194302db9e047e33e747d3c5f8a66d95eb744db937e34f73a54f78a96873726dff6e6dec2622c4ec9c0a1a0adb27a8537b2e470d76701ea1a075b43caa47e0509c94970030e591e5994712916ce163df59b469a73d61750b40558b80a9eb666c375bb22a2767c45111ceb86d9e345c4d64105482d132c62dd09f089530fab281050b274cd459236e05fbe68578072b97a68f2ef37287f260063 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_227 : rowClaim true 227 1451 9239 :=
  checked _ _ _ _ 105 0x44a5bbf4c6daf17277cfb11d68da12eeb81979f2bcc5fc20bc8e0c5e02ea5662e3f6bfe957ad4bce53343476a27db45fe6f84f85f3877f3c5864d21499a1108ebb683d330087022ae29b301e8f88ae17b11194231ce8079baa6ead70bdbda2a412b21a40c0906e50220efebfcb8edebd4d7bf87f14ec264b0eb4674d0b61d2c8e1266a696748d961597f0b3c2c16eb7605c1e94933d8a6043792eddb2104868b9fd6025c8c6702d5ed9e4bfb5ef08eaf2d77f298c3c5980aa57d6c5e98b4db118a6977eaad4375486c0be0d1fd3df249f0e8890bdfd97bc50bc2ed8210b6d228d2fd7f59c400243afb8b6f8fa32ad6c2ebcbae60c5c0a4a35468c574e26fffa3902d2b26f5552644f62d900bf2665e8eed703363f55abed8d2320cad22e5f0280e686687ad6f58e0558818283301f577a3af8ff165893b9b3b1a5ae2f403ce4e9ade7ad2b271acae949a44538b80e3c45a5b4d20dc1b6ac1890619245b1514b350069ef7dcb0eee6708a68e3beb2fb66e38aeabf1398f3004613784cbdb11a3f904f66476f15fabde34f66775ccd5a263d73226e841b1a4ec75dea998d2f1183c53f1bdff2e3643025590d5e47a792a6873176f43318986a810a03ffc5219a96a1294f36bac9b969194a1247d377cdd4a252ee38bf9d6d4ace0d563eefa958a1822b46768ace6d11e30e897754a60f868eda5fa2b58b776baa3dd7974e70c261aebe458ef62bb3f6019c9368d205c54007f708dc4e3c6529ce05eaddf4d1ed3ea457afa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_229 : rowClaim true 229 1451 9158 :=
  checked _ _ _ _ 113 0x30da3b99b9ec2cd25d194b1488b17ea7f69820b9d0c787f8542df3dfdeb53ae57ba77fc5e86c20060b1726e4cb004b7d42a4cc50260a019f8ecf9fa7dde676222e55903be1af34ccd927d743a48e32fb932306cc2f386652fca4ed0aa1fe75b0a0952fc9ff5ff33931b30fd0328eeae87b33eee7b440391db9b458430f6e00d7b3e47e6cd4de2240e4826eea35607f9692005b71cd63b9e2a1df9ca085e5e8995457012760b0765d9c686ac6411f1bf9de4af8100922d4ef5ae65b74f43838e3bab4b4b9973d22abc7ad32006053702d14602761cc810a0c13c003cbe1e014b825c22b1cb04bc5e16ccb717edd31e15da716d57a3e02b1bd6f2711ca59581b25c04c4acc0554a26701ad68ac3783bfb612bc26ce6d3ad246fde4edd4f9fb89b4c1b817ad02d131d5e9d2b17d8011353e532d9347c1d5ca01cde8bf17123beaa6bd272890ba6a5a7ecc4fdf2a4b71a32fddf1a98460733142d9c486f44616ac9634dd965e534ab7e52afad47a0fc6f52c75cfaf8fe19400d92729e8efbe6935a8b57a6e7d2499116d5df3d654e13232bb888699b7607ff3ed59b2d7d95832d968302c39b0a8e0bb128c0ed1a7c1d1590ddb2820a1b746a3c12470f573ccb1f72183c37874856a7891a2cfa5591049d6272bdc97d9cc08db6321f80f657a88c1e3ac121367eaeb055e2127deb33cc5b20ed14790f9302752c62d939a50ad8dc7034cebe861dc5439ba14d2af17d44a3a66019392e2e1b97db92c4b8014b37973f2002c9114a7ce436a0496368f3cbbc11c3476a9378e34176ef2f151ff3c1126fc8dfe8f2355ecd74c0a57a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_233 : rowClaim true 233 1451 9001 :=
  checked _ _ _ _ 103 0x8fd37c96974bf3756a38257967e617326cbf68987cd43389a70c97dcaa6d6a869523108f3000381dff601511ad8100bc79758f5f69bcf10addd80bda477ff1707c68512c21d3844c3c673d224708a470e8fdc5e714ecc8a01a2e52ff85c00c694341e0f0c34e6841c27aa4e9996bf653b9c470ffbf84d522aeed59723f58ee13e91937afb0dc82bedb68c5cb01a227ed57d904574538245d5c58ba67f5ef03a241165345d251ebae4f069427cd9118d98e773dd6320df4dfdf01816765ffed1d95b4b47a77ecaa6c8726040b834f6ebc16bb99eb9c332f05ed2c4c04c763bfb953bc75adaa0765fdc5d3b85e82bbd8f56afc2429f44527a2068b85aee0e1d8f1b7afe9c3f001858f7a5221fcf371ab685d496f1a80ca31365b231e9f1f9b4b458bf9cf2380c62fdc74c785a6ef487bf449bdbcf5d58f2f69724298071b65c527216cc097694c7221cdb68636677874df2ff5e47ca10ddaa4672a3e2647921ea7901a4c3af3bf33215ddcdb443e6069203e5c0aeb2617e1a15758f4a3fa674f9413a9391ec9200bb59f929e56f2506e9d670dc7c84d7974f374de0cfbfb57e4b915602cd133fcb595b9a048ace7c02dfb9ae6990a9bf22485b125031caebd1784a28e4a4e5888dd6f66f0dffe029ba2b95a791d47bfc837051ee2f314a9eb0939d2fda394c9e65ab26fc9309a6be074c0a461d4b3dd1ae3491c3522a0b4df3cdcdbcf3ba3859d5c4338dac8d2058ef00e300c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_239 : rowClaim true 239 1451 8775 :=
  checked _ _ _ _ 107 0x1fc7ecd6e1d4ce1c4bfd34f716c4bffe84b21d6e768b4a92bf9fbea48eef22c2795931d07de3b6704abb789c5cc8ed5c4cee3b20b77ded970ef4214880c9d9ff196fde598f4ee71ecdd6f4999aebfb56e068fcb527a9ff685730112040b5e0289c7ebccba9acf871e40be04550ae9f110f4159608ab2bbf63c7509a2f4c38720b1c4b80727e0c89e0c9ebad401ff2d6116f98c7207d43bf2b1ec39029b2544ac0ad640fa835e5fb0b9831d350e266e1d3a3549a65c754699b629dcfd5af7a4c2d5f6c25335f6c973e41801c033de05e09238b5c29fa3bf9404702f9e272fce16a69c11a3872844a46f8175dfa18dbd114f03d71a78122b7537de390aeddedf7b3cf1477e1ee5ea7aab2f0c52d8f7098ec0a200005e45507797f10359d6b15da49f17ef52fb106a1d8b7b3e676ec87b4d0f7f2f1bc6b863c9c00f4acda47fa39752d4bbac8a45d7dfc3887e26ef6804e44e2b7a24661a364590cb876bb528a06ac730da0cfe70e99305ec1b056df23e9540eaccf31800d48e213c5c3a8a4962090ac9134e75f06538673dc1cd4025064eb3f02dbbfea896f737231b14ab42404ca92d2b79f138d01a9ded24e75f661154cdbee8cd66de112c2b154968114785c0b6622a31a5f992f873c081ae4d77b1c8a62da0a0678937e28f61f75e9cc7fa686415d4e0a25e526d1395d433fe1151a870ebd5760c2e6fb787c9ccfa45ad1bf6f57d39130e583c250a600437af32e1c15fb735292cd08842e7386955b18b95fb5dc76067b4bbc9e6fdc04d7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_241 : rowClaim true 241 1451 8702 :=
  checked _ _ _ _ 93 0x2478b82f279ddfd68f45fc6dc1c332c86434c5200d5bcf2e3718ed4062ab8c0becb2f28c8108b949d9812ae3c0b73ea19705811b69b437dcaf6257b6a165a220ea8a5c77aabb2145b28f74b991c6a47e31ee009b8ab6c755d2f2c6a69c87ad801ab64302c6d2281a0bc68bf7f9971ce1d7e455b36d8b49a46f9aac073f320dfbf0694f0918ea65ebcd76f1595a12dbb6ebcad42f2b2c08585ebdf2f4e9de639d15090376118f05c2319d4aa641bfa8d8d37734a33c7f76940a23012f749c482b71b9e1784a87eb456903abf769e4df137e66535f2094883b89695928e50fea8d22e2370a1b4e0a7a90ccccc0fe1fe2ca2bcc6818f24ef71eda124a1508393c79c9da2de31b5d59358f78453a9838a0323f52a358281ef6f719e987586cf0603425d03571b7ed3a20e014070d8e8701e114b4679779f0ab16266468f1ba087b534fb890be421ecea24954746f6a13963509ff832bbc64327dc5a4eceadef4a5e0b0d9acbe903bf54fe75ca5c355732e534be1b6c9a7b98bead49fc5b563831d0462867aab74982c1978601e207266ac02221bef95d9509ac165fe5a1dcf6b290fafce17d5b80e0c2cdf3356647b696c24a1e7ecf89c168079da39d486c51c401d885a18deb2e54eae627982db4be17399415396b48b761c2cb593809c44885c0427a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_251 : rowClaim true 251 1451 8356 :=
  checked _ _ _ _ 126 0x89f5498833db9b2fd8adc8e0df092881e95dc3bf538033d537c293a7072fc951e414a6c2b9da0f568421b372837507966e239c0667fe91cd0c4063e6398e4a9c27f83c03283d3394819290dacf7ad8148a54e610b8e2c5ab70980186a8a09b9cfaf2239e1e528146bddbbf002fdb2ec82f418da9fb23dd63240568d5453429fc2cd18fa61dc5b9176ab5e8bd6848ad96fe0e3d0cd6932cb52e981466ee3968ffdf30d9538fab56cf319a6c5fc438c7dec2d9af2a130dfa0e56daeea40a36fed9008e64a122cc21b853d78bd2a4d869bab240315a4597fecb7a75ff75dd0572ef704550b8ed803266a6f3b3feae978d69045905dbaab3bbb5b6eac82eb0394288d59a93e67ce408d6e0656f8b91e56aa5dc3d1ff56d5166fe1fa0b0ae8b50bc81b522284c7eca6245dd64000755c19784cb4a9e98920ae03de3f5075c20abfbb159d770605667a70b89176927bf53da52bd6265315b1c444f6b54a6c9c24cedf86683e8514d140bdf048864acae9c33330a60fd57eaeba079a35d44a356dacb1de4bf481e45126706aa0fd32b3061980f85cfacf0bda0792101d2ea844187f3090a1511601c1b0129c92804235db8ba7adab361f5a2eb3f5214716092048eda3308e61d031218ef50f5bafee51f52683e19ff750dad886d4044754d02d612d0b191403f8d4b70afcdb619a51993b5112718bf134b67f26dae4c708f422a2445286c5c320376e4b2b98ee82fba2aac4c364b72c9292b159d9ed12cfca212bc2a1e1767b90d3481e0ecda724e9df6aee48e5a0f141fa03ce382bc17edf995e016515e961061a5b777f6a8bc9618a08862b95a1c4900957fe0ea4247830be11486960acba1c5d24fbe1bb24dc8ddd16efcf40ad76e8c7878cd5e1629aa189b69e7ea38118c725de327af13465b48227c2cb7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_257 : rowClaim true 257 1451 8161 :=
  checked _ _ _ _ 96 0x51825551f1b88c4b490c14d065ef16bd995763c443df415eb6df00db89cc9f76db2c1d654d8442cb28ec8887e25b862a30b140d2119968b13e28bf593723c4616baf7dd4e58bc7249d0802a8e2a1aad9e4bd038a45f3b91ddd64fe636c25bfaea4632a7e7b1b1daef600078efe9c5c1f7f584e80ab572aa0cfe46d47238102d9d6963b1ac0c8a6efb20441db957df1498d3010e7082560df6b1cc592ad9ea32e4bd61607fb6b8d292714e0a3200f1d51d6061fe65f4149eb0d8c4b9912a91d1fcf93239a55336b4323e531ec3ab1e3d39b834e97f52a1aacbc71340ff26bc936d92f9e33f793accddd9b071c02cb010bc1958b5c319114d6ba90cea3c6520adcb048740bfd3f934b51580fc6ed44a5f8dc4f517e99c287c39d2bcf8f3a1a23e43a5a760b06e77af32d9d63e5f53a6d4e22bd6e3b0c837ac62abaa384c8a2af144e06ce9aa2606b2c6297fc8d85869de129f318c9b3ebc77c1420510ca17667fbe2289d7f5c0cc8f34f1ecc483fd845c2404e25031a7d6b6f06e16cb7516aa752da0d1214596c22c943c688087d1173ef17f6cbbd3f219b0e53fa86fe2574ed696ea2ce12a21c4ec0b8bb5235995280f930b42dcfbf6bfa419ca5642fe008e3c0ef4f0480d3916223788530764b078bc7d3482e3df58fdea62fc24d72abed50efc3cab306b954a1daf1791d64ac59501f46686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_263 : rowClaim true 263 1451 7974 :=
  checked _ _ _ _ 90 0x833122e8dbf95cc615835f4531dcb9ef538cad34e3f4eedc745d234a32da2e5193b840dd504c8b229d4efce78da975e09e7520b6276717df1656f75461211cbcc12ff02d705194115822bf95f89d0864bba11c58c7c75f2c8928d9c99d3e0e948c4cf6af14b0dc10560bffd0a044198e042efb0299c896d083683bd037f6a27c87c6c280be5bf67f683766924c554508ca94d38d444ef16c8d8d3784e2d098840f3903f7bf897330c3014ded7e55f24c5a7611b6a8260b270ea597a2623f607a3053ed08902422d394649ac06a772b792f3c544ef702e6b6119b26dcc5addcb3b28c9afc0b46d944e07ad701ed3cfb39305d60f0e51054650c10cabc940e464eb08dfc6ed4a46a2e4d3b6a3f68537b20109ee077fd616c8bf9cec1efbf1d8039faa10d958b28017d29a3eb4761b816a65cdc9a6e4d681e851426bd3b27a4700d185404d8104f6ed2fe0e1cb3d9f2a9d723c36b78e4b919bb0054533658691dfa80ff12a44d34f099f34016cbe54fd044b2fb32266e87590e0b83e618949426391b279f6e832515675f2e4a902afcb2bdc0cc66157079623ad713d88ed42a0c5a74f9de652c4f367ecc433d19f75bdafb108f86645ee39eb61b0c88411b58b631a0fbaba218b072d178ac416c1ef7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_269 : rowClaim true 269 1451 7797 :=
  checked _ _ _ _ 110 0x8d07b4d4f84237364ea972cd4f9d3504968e8e28508c8f7ee97d6d3940486fdc2dab4c7934e334ac2b24cf43bf9c983941478bb20c6667ed63a27eeba9d4aa3a718b44322d436e22206875d37e620901f560daf5e8e79dd5ff47c94b039d441f0e37bb857309ac5fc06b5a7ba6970299f11ed9f30e6c84ac34a3b659f64b0a52675d641a90115cf2d6487c764fe8d723db998cc7e26e9c4b348e6900cd1f7c30a264a3cdda5869db5378470ba5c7d1f53c9741cb6a2809ab4c7e043ff33d99dbef1ae0a5b52fe6bf51528bdb3426a5b6347317a888549c44aca914a21a73658e8d56d8fb827f6d5427a04620298b2d4c68287faee327f87a8c389c9b222f0b3c209464465ee74e15622e7780c65ab6cdaf69c3f5372528c2e87e50b162727dab1469b4538b6561958484a036e7e355416e473cf1a75d1124b09ed9e3ce6a7b7ffe3f97753ab0ae56cae55d9c762f6151bfa80db299dae3a7d24812c74cf34d51883281ca89872653473e0c65524691172db22fe16f6a876fb1f7a0eeba64d387326dce3908263f5a3af756ff5746f26ee9ad2e28b90a0d2bcfe915b25fbe15cbaf6eaa1dc80cace292941cc2800aa3003039c11f57916753c7e4d6b7a90779bfad4c64932553bc28a916087bc9a3daaf64ee92b114ef40b5f3529b7f121d7824cba2b2e88e73c1bc8e1e1e02f38da3aaf1bdbf039c2fad59ad1e724f60ed945c122d9de44a55238fae092cd06bbdc31ee566d9cd0e44d75250f9465988c69ddbd22fb40230135ba3e9910a61ccf4f509a0a75f4042757cfe01b0331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_271 : rowClaim true 271 1451 7739 :=
  checked _ _ _ _ 124 0x9c464d01f157ae3ed90235e1d0bca20e8a8f3280766a8586fdb95365a56df1576568afd1eb67cf5a46b14fd8d2267391335a6f4e4292eff846c5885aff73cc5179bee28de24e09884aad9f25daea659db1d993a3db366c44f0f1a50f8793bf36b78234974f103e48927352b8d3b99270dadd8848ac5f0a89ac6f1fc5b5821c27b1382b5885b9cd05b7b211a80c32ce9b16080e188d68fec638feb81922ca8502c711b684130d1d80b2e9a746aaba400853448e6a86e198f7c1a6e336e5d221e4b92bc7b1f4e58104bc6e032d94407f4f82efc06a13125307d0a26c285f0880c050572a33abd0cc29ef012eb71dd74687630ed3b11e32811fc91f1ace55e4f2355f99ab42d787e765361971e137aa5689dab7249a535bea9061e7bef0b507fa2404e4b24ef156c9e87fc94cd61fd1eea497cc01b9cbcd0cd56e82e000483bd7f53781411479f3ce7870879dc60abaea3648c20b4a3cea06017be8d752bd751bfb629d643bd2e12026f2127e74e19e84e6b5d49bd9555615dea72efa6307bc64a1275e21bb4560dd059c363c63e74425956bda3e617e56d8c5e8f2f8bf0d1be4ae8cf353d1666720a232301cd1a9d14475174b3363d6efe11e4ca3127c8af1bfe8335f0520e293be2a9480cb4ae41ae895a6d64b4fe8e8e4ba15a389279b7099160e3c13701d01de19ace9e2ab9021737a72c6e807f234ecc5d9398a3195cc2b7ff62ee47ffc71a7661ceb66b4137688f5b5329d49f24e2fbdc3a60930dce34ee0c33ef996e88dde88e6a37226d83c4ec56a54a1c841a8e8a7e4d888d44aaa491cf192a1f081f617bd51dd9fb0d35d724ca62317451992a1d9f268f9c5bdd983bcfa5ebfee7744128d2f6aedaa2be00b6685a5f2bceca2653ac53836142dd0fc0ae0c1ef7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_277 : rowClaim true 277 1451 7571 :=
  checked _ _ _ _ 82 0x11c8e328fa5d260500a34b15d806d2afe3cc75203854b61c53eb4fc9a47451428df92386dc2af8b638ef256fb6fc6b23e38736ce90e1879f4c7a69b3dca264d1a7c3954b6ef8b923830f1cd0eab6fd4506b13c4831a0299af8552866c713ca68c3a141b02ba680eecaecd6de52b2550a3a38e92008ced24acf6589a9c13ec97fc903ce27e1bef62069eb2c9a130d474e62c8140a29b96e052a49db9969bdf6baf3e93733550027e8a7ffa0cc60597c5fddd9fb7c8d5d575b258cb58548650051d78aff8237bcdc514c6a548f3bcfe6058286579cd503ef71035cd9390014acdc24f60a5ce14aa750b5816c312072c8b542f115ce8762bf4cb3a091710312c56db99d2e676c3499aa113d2405be3af05db22dfa2fddb302a30bf76f43c0d980e0efd91f10a0f9dc9935bd75ff10383fcab81b21c0c84655ed098c58e0a745d345680544aa98835550e1f0bdde1a124b98e3584963522fde981414592ad65324ca06ad49205da0968a60ba9041422123f9548de04cda985e335acf8e38e4576b96269a67eb6090c462cef0a1fdff03b766657004d972a9a86d93fbd3498d1c95c30f1f03c83100301a5c9937003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_281 : rowClaim true 281 1451 7464 :=
  checked _ _ _ _ 135 0x729d56b270c434306fe44be08d7d44c5470f2b43624b95e673481ea65c92255e445d420e0e3869a4846ce74ce6bfa1b3f4aa336402778f2b98c1c45fba1fbdb490c94aa734de7ca00ed3df0b7f8ce48423160fb53c0a844d5848024a7076a9be59c5b68f2a13198c3aff27fc7374ec2094edfee0179f52632d359a2404e9d33a235b118f7fe5419379b4cdd2eea17608a7ab5bd9219f491c375f28671ea51b11243a092a8dede4d9fc2b91154d4a8c32841a0e464f8e540187c29e6d6e6896878ea6aad218bd64525480449a2c9a6d4fcd86dee31ccb82d5a0911eb1f2e44c212bd41f66d2e8d70f770b8c2b063c731f82f3346af1745d36cf0f68c7ed37b75404f75b68f0131b3a2c98a1e5282fb68ff4e827f1254dbbfcee8fb3fe57b93ab85be94d4a5cbdb11c7c2bd5c3c0c4ab53a30ed58aa3b763e1822ea80aa1649441840fed2a733c77f321e714771f566c60eebc8d68e618c4669bcdfabcb88133ae6c94e35aafb8cda55964b562f9ae23b42dcd5cd2d2e79ee7c8b9d7f022500ca2e24ce74c9577c2f8d46a4502898d3ac567463c973defe358d4645164327469fa6d710cef7deec3ea1dd5df6d6b7246eea44d27fd1df24d53889589d53f9a3ef1d759ab95320cf854f44a1f2bc5f6095804ce68eec9675c6e68c04991528582723cbcf69230049de66715f30b566eec26b106cc99ff1f7e3fa405b62e2085a5189ecd8422a36a40a750869bf5b28bc7c5586373b85521a73babf3a20d9efad828ef5966d6a05aaba343ca29a8d63990027ae424c5cb2cbc557840d7439f7f9a5e1570eb02de683f84a175339f8b96365dafd6de6ba6f981e79eab924cac4c0d3d5f9aa6b3f70304c3f21ae9839f341ffe7a736d8e768be45ac0ce73a1794d432e2e0449a221b9b0749916f8aa56ebd8d5fe9f3ebc9660155ad3081fd2708b2912c4ff2de0b29049444520714f4a0dcca565df5862db4ef6b34e0c19017c6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_283 : rowClaim true 283 1451 7411 :=
  checked _ _ _ _ 103 0x5a7f5addeb57f0c072b55bf2f7ac9bb8f7a543b41d57251d1f80c727528d1418d65dfa737acd0b49917d0544bb7dee9cd42655e7f48e353d9dafca84a32d3d9d5838899eecfcd4195b8e2a8075bccf089a32c727d6bb5d8221e47f7f136d7d707f2f57656f0d24c9efb8bed5e9b47cd05df8e31be343d1d7567ee9c2c8e66d0dd3470d7cf202f97be4ab35356954612f3223e62e7f11d927be8fd385a47571d55ba22b05585a4fad37c8738e18b0a133446b1cba81dcc05f91ae64653e8ccdbce02572f8b01a8c04af4c9cf22fd2bcc9ee92d5656df418eb36c7c394703b4395459a2b46f3612d55084a8c7fbe867f3ad1c9473379eef8e2f313e914bddbed6d248595664f66492b6e54a81ce039c1b530d071525c290beadf47bbec8f85d0ce0111d2d149fec0b13aff347d1470afde4d53cf8c2b06886fb5cc82758afa69c9afa100b15fd7c2d078a5c84847c533a9e735cc6e23ffa24e2d973c9773643ac586fc49cca027542001f167638f0eca1b782c7fcf0bad2ac08548d9745bb6b47a729bc6e0ec5165e256c4de2111e4c704d2fd0ba6c18877cbee351eeb456732cf37fddc927f2b3163ce0721103136a1d515a6cb37ac4d16040800242e108c3e2de4340638f9c8f0dec16806b32c4280eb9bf90ec2f31bb2318753e6074c2076a2cfdc5341479a142d58cf310db31d596f144cc54cd6ae37328af22b77f284db6cea41d3c6edecc27d738ef21e9632d7d8b594060ba707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_293 : rowClaim true 293 1451 7158 :=
  checked _ _ _ _ 117 0x1addc0c978dda4f9577627184252411d7df2a62f8b77b3a35f837c7a074ba734874fb3d463c851e576c710a6a5bf797ba197982657a9e64dfc7204795101221c6c6e2e271d14c21eacbcd1ee5643bc8c89f3661619ba24b55f098babb76f735b837d06f08eb8e659877bf36054f3624e660b16668fc53df146273b72cf095715a18875cc294b3a752f45230dac41c4a0e7f797e1a7c9c35810967a6653f4d82cbf60cb3a780e7a76cde5632a88f08b0b64b1a4c49c8f707fa6d7ea4ec447a2b69c4fa8422f4a9810986cafd0d8e72884b0c9c87d070ba97e7a151a558c90bcdf637b2924c58d6077e1261db8fb773a63ff233d073865cdce22480b09022c3142d408eda3dbbe2e2c1189f1baad79a40d1111e2e36d6d4c0d25aea9206cab2df60a04dcfd45a2aaa28353de58fbe1bd6a6f5df9e9acbd24c85e6425084eb32e4fbb8abab090964b457ee862a47be5b3a24b46a76aec8abe456a110775a1467bec1baf3942efbb1d6eb1e65bf9616f3f784c1fa88875a0f5c5846ff9b11f104921cf75713f73f9047bc50277695761391f820e70298e5d3f5c105a99b9fae4e1e0fc32fb14e47c03e4d2e0a9cc9b5d543c3e94e8635c0127ad7daef4a4ec8334ef606d7c50f1b2b751a8f985474b4e9567643a6c2f9253efb06f7fc5c8f950fe1f085fa6c3fb62c50f91140a4e8ed23a45c8d0683149b08a53697ab6268e50a99cb90516333b79343771d3d434345f63329e62622a69ff469d40d9c0c0ec055d970c91645c91aa108ff7399e4ae8c122358dade3659222a64867b272b38e6a916ff63e29756a3f02582ca40d0e0e1bdf92b67b86c356cbd21a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_307 : rowClaim true 307 1451 6832 :=
  checked _ _ _ _ 98 0x443841054e6e42b273bcedea3104ea22f256e4196ae7860eebab8ceecaca01097e965b3e089186fff5a4b7ed38ff3a5a0125284dc48bb293b3f5e81504e4edea5644e441472eb61291664efda6b89347b24535b33b24e25ef79d886f44a91e0c0e7dcfbad16cb879ecca7e59aa2d9e229c0f1b70522f551ce5195b5e3a5dd501b270c43c56f0bfc844c461f5416e21c379e09c6c38b820a9178b0989268e9c870b840167cc726cdf026a6b903ae32ddf424f8a8ac18bdee7e14eac829a18182ba5a7b294fc97dfe8a987fa2fd8cec839ee9d0a616d8616d24ba490582458f9847ccf39d18fb50f9cea2cc4e31622b6e4abc127acf9c50a3911a19ed06723dc5ee18742e63d7c4d55bd5ad92efec1825d430d41a7fcbc59c6ecbd36db8103f702c4eee21ce0552efa6419f7f599420ab2d52f8f478319105ffb848f76631a1bf8f84de229784d08e88d5b2d37d909b49b20dc4acf4220aee6e6a34dcdf14dab404791155dc05a25372c3c9255db547068d73fa1d06ddbf46e30765d25d5f750d5f0ba469d511d8118f4571ee3312034d17192e99735e998fc3075f203c8635fa41dbe44a34eed5c5c98b3fa02861c24ccb0c7cd4e838e4c31ca735dcb97ed05d5053b0d99ae40ea72a2c34572276a585d3b1b415b00e280290c712ad1ab017a415b516deb1a0b0af45d33f69b7feaf4aecd267c62b27dc2317a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_311 : rowClaim true 311 1451 6744 :=
  checked _ _ _ _ 97 0x11780f4a32c8f97ca03099c30479f3273c04f536758cfc4106dcacd0e9c4741c019b38f49fd8a8b0c4ede895e5e0e329de7dc8bcf47be39ede3b9a15a27f330be405588c552193ccd746f3770e5999e396e105775b3498077e5e5f52ef53577caa230af7a6443f0886c9da2e13c344099e9f609157b66ecf7ecf7bed1e0a23256545f7c5cb9e1156cdff15764639aba3b79b06e103e306866f1c61acab622d8c80e273cca035e4cc3fe4c08b93482a8b879bf5d32369692b45217621776ba7e225f2797006cfd821d050a57d48ebdfa5c695aed9f96daf5029293d21ec39eaef109b04032a706df345d401b6b067cfa407e723f11a69b7f203283ab68a3635ed243f75229d81903572f69aa2ac7502647ba73e521029f01b1996dfad0ed4d8c4f139bd396f35a4d085954b694aac97ac96f89e6911c0ec243b2f3b9f641277eb3b49206eb0b4fe89a8e4273bb11de958bd6a16b97109d8e7a992f59391fc5ac7be2890ab1490295668158ccb557042e1a0c25ea9acc33836ee32f9414b9ffdd55832065ad9eadde1e2425cfc2820d5eb061f8721d14ad8626e82ada121b494d21a7465ab2d05beea93d3c2d6f043a2b0ee70d039605539616d88f945f87f5cdbabd16d97d76918d6938c294718be38a886ec3048d3c8451ccad9e4d4ee0b07eed82a44a4c6453eeb6627b71f560709d181f00780a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_313 : rowClaim true 313 1451 6701 :=
  checked _ _ _ _ 62 0x375d96c7917e9ef67f89b9ba8c26891146f6f661b022390e4afeb665406d5513dea7bba63ed3727d483e8fb9d1f45d0e6490c87fea179c900e78ba08c2f722668040d59325790dbec85b645038f4a436884ddd671f6da81af0801b0ce767556cc909900240234ae9e3ef46cda6cd72d3123ff8a1bb54ed45af9a2667678e6dbbfe05a4a4126976560a2305f034a9107322eb1ada2f69fe8fbfc3c16d5c03cf7e3fe004b3f971d2dc792224000d4a44e61196fb00122d75e1d5fef49ed64cbfcf3a99e5b801c642a7b1e0b972861466ab29c90545e342bf858d1fbe0d5402f7ac07fb93376ad39f768f5671df9cd9207ca55a343eed64b731fce6f215d4255f89a67e4e0a34e8ddb1003358289c500e8d1de63262cc1597e38cf71264affece310ddae93c1f4c28a2aa582e9cf261e1e79149cb8c2ab058ef00e300c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_317 : rowClaim true 317 1451 6616 :=
  checked _ _ _ _ 86 0x9fcd0ae3d3ea3fa6f85566bdc2fe1cba60894c64b2b47d4786e6ea4efd8136481ae9190a8eb12a5eb98935fe1ea85bf4b2d5dbb400d97eaf28ec3678a8f2097a2c99f540b7ebcc1bf6cf723382a10823ddf5543e2bc55280eaf74a2d187017d52d59fa3c0c2d405b615e5044b0ef60a9f54151170ecba47fd3440a3ffae16e43d71c59ffb9582ad3d1dafd62a9cccf4b6ee1c12ac219ecebf2a63c9c97a3a4796351cd28a39cbbd6c1d5692b2de4e70d63b8712a91732e4fd912b393a590255782b729b3cf6acafaf28fe73f5779b7e244dc1245830857563ed33833ae5046b2c89f693d657b314f8fdeed50a34eab7d3ec7a2dd6093f7474ea7dd27c194e507412ac5465aee192e8124dfe979aa443be789e4b6b6ba40e1de169487e1a11080bb58460289f98b8b95f731f51decfd9ee5690bdc033163a7eab057b8bb4e7c278267c98c197b9a2bcb62f9def8787beff423546fcff2604ce84430cd92d8c0b06513c7b669a1899829da063066d248cc7643c23e116d1b00c61e331d81d72159c6aeead4746799adee172f997b61579ac0aefb479af9034444f485fb6bddff280a45ed439f0e3ce90ecfc09a54bf840498064b4ca4c3587c18c7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_331 : rowClaim true 331 1451 6336 :=
  checked _ _ _ _ 79 0x226a2b6b43c602e1e252ea00037a4a3cdf1c4afc52fae9de3fcff082d652d855742705fabb1d16b28355c9b22a962f525b172048f4bd61323f2a62e47a39df5a8dfe93c5a5e58fa75a68bc501d2647cd138aeb8e3d21f2f34c0357e60c36b542bdb7cee37edaa193c7d2c62d0d60f14feaa4713cd5937e284481f6d069ca440020c15b227bbc3981c5d5ec32e930aa0c4e974ccb71972824175fbe0148e49755aaf0a3ef1ca45b30e4cb010b588a60aeca8060c9d1e9f5a888a77db547990566ef24def22333effa051b88a78038640a616bfeb5e183fad78bffd1759d6aec4ecadc3125cbd78ad1d68f498e16be8437f32fbe5393c30c98a90024b77a13c263535e67459ca414afc28b1cbb35f8caa16a7cda519b79a7d21be0a1bfb156b1419a2ad0b4830b6cca0b3f07a47ce3cda596936c4212d29fc876520675aecce529a9b89d8c6df95f1dd36f08e05f8ea73b1d22440a93fcb93e796ae43ac1875b4ef42c83438f2c28c483d4f72e1ed2acb6ab03893ef1abf752e1d005ef2c748b05c37b5287f83a3db40f23568264a18e4b7f2f4064b2d3eb0038 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_337 : rowClaim true 337 1451 6224 :=
  checked _ _ _ _ 61 0x175a046f2c3ce6dcc089119b7b73af572a5c52c870e4f2bce752275148d0920d4a6de1f4ea847090bb2df6f10d479d49d83994a202e9a6b8e3770782820ed181b11f6b3e3d6fd842909d0f5c9ad721fcbdcbf947c3eacef119b021b1674f66084daed9c9c1d986a5c69883d5dcd1b0698e97777f57cacf7a517d4dddd833ed0da50511dc8534c3543379546cfbb5d1555db112eb3f518a28b9d3abc24c89833500f21d407df5dda76dddecf944ab2e854027ab3067403251ed6e025e03e52bf50f99504f4252db547fc724899b6911f04d630411f0a85d3d7e2d2cf184bcff2f7303fc4017e7144abb4ed54e032c1ff0ca287d7d82bc41e960cb246a55082646750d84a3a12c3364a915a9b2342bc21602f32014d9d557e99601c2bb50efe2c4322eced0e275bc6aae277fd8a632b0fcb8e2faab71c06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_347 : rowClaim true 347 1451 6044 :=
  checked _ _ _ _ 87 0x8965584210ae121648da594eaa6f2e170c1197805988efa996640645b6ffa033bf8846847c1d4b173578ae8b840cf14c6f267d588a0e5759c8393e2455ae7b8050c4371b255a1b5f4447a1c48d7f586358e3a6aa8206ad274b174fc4aaa50acf16cc236e751cceb752a6ddf4f9771b6a7a8ce451947731ba0ae8656dfdc687116f69778ebc6ca8eace30fa72811f230869358303e7e38d10ebef1cf23b0bba784e91fd067c412ce6eca841aa7862a7eb10735235947a64fead13a7166fbcb0cdd14e603287ad5afd05bf18df877b5051caedfb5b1140db3d90411407bce35271863ec96b1f94b6d567290c7a57b55563ba008824f32e28207f28012253c7ba3849dc678a5d63de29bf139d07f0ae3fa91ecd1d631ba8e847b8ba5867006ee9931978812d707be2a23f4d363a7bf89a52d64aaaf1df9f843b5b19ae353f4bc0712a969527ae48f015b4c4966f901e2249e82edc5d35b784719c08db550eea52fc644d9c4f7c41996dca9bb523a1a713af308ea56531f905413eac6581730c3a51001e995a765bd15a44408c4636c9aa5b7acf3dd0f4d5030b28810909f45bbbc13e1d89937c94a4e381748563f4a207c5f052bf05b7901ade163d33e695bb7024c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_349 : rowClaim true 349 1451 6010 :=
  checked _ _ _ _ 69 0x1656a7eeaf4928083d8852a88a618d4c2c579c2d7e9e361577b23380593bc7d0861d143c4d61c20a370b8e048c904e8ef9aae01630797003ad50dd6365a1175474191bf58e1d970de8e77a98c43094fa277c141e58356ade778f78da7a54659aaa82a6c171cb6841c3e325f6c7e5da5869a5317e6a3d47701e7028e5ca065ea626e34479443e908163bd30b76e9092ea174b156aec1c05e563ee4001d79969461045f6b2bbef9141cd6e4777c02b75656d77a1e73d34121a024e3ecbca6caad42789137db44c394dfd0e510b3d7d24f3597537095a9e6f21cf061a6e4166c3e0158b6585d5c65ffe9183af474b4910ee7b65b99484c5fedd29cb1dcb9f4a6ebc52c66694f3618c457559c8f98ea3b9a8e071edffdbdcfc118b11abd4192d22dd8f5c7fdf40be0452710887eac3668d3d875511b7cce1ee3ae751ae4ede222f4655c132f9eba7e079c7ad6e170e696ffabc5d8aef65f4a863efdc204eed0dc0d17a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_353 : rowClaim true 353 1451 5941 :=
  checked _ _ _ _ 79 0x35b3c65d93f9e736bee9521e15c67da1d497d1ee0312a86748bfa53f133acdaafb2c429a3bc23ad292f3a2438c2beef0f25f30f4dc6a1530a2ec625dbef969dc04497a96b9e6ae9cc49a6e621129b4f3ea359f580c8da567ea3ef6205d132a689d012e92b1682b52b94d3537070bc9ea075ee89d8089687c526db54d415b3d60e29622c07956071df223f80f566de6ca137d29c3bca0ac65777633396cc510cb891c5fd1350428a89563a20c9d4ab5ee2b2a9e648911d33f27dd9888058124ea7dcc3151aebf8ab04e1f79e430bbd819b4e10035e13af13f583ad66d70cfd1671af5032d41c5e5bda11afd24277707f5d6a6d3f0c1a3924fe47d0f7d396ebb0221b1f1df80e3156b8cc2c7a9d02823eb0595ac62221f5a965969c15e3f676d203bdf47e965e2185fdf46e5ef1c3b68864453ddd0e91f508d2f178edbb56a01ff53309fd21da1fb881cb433d41a95ab79f60a2604a615789cd06ceffc34b523879f711b0b6f60da30e7f809fc4cc16b9ae6d58654f4d02267a362a13ffea7bfe5f56b25b143966949a94570b09ad73d07b02f000c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_359 : rowClaim true 359 1451 5842 :=
  checked _ _ _ _ 63 0x102126228215bad6fc1f7bf11f9d6b1d0e777befd9a1d1b4062c178ecc671a3e47f6dbc8428367b7d3a760d136e42205ecb12a609e219a5d1e1ff2e08ed9a9b7ff788758d25f8a0b0555249f6f2c0942cc9a7357a40da8d8a2ff6db6b2c9a41d307426b131ac552020c916915c01de77cf31646e14923a58e3576140c37a170cca00fc3534c52814d1961dfdb650b9aca89430352d9af76ea98768d83083a99a584054dc1f744ec74f33d59870576c63837adcc99c8aa533586fda1ff7de14dcf165114fe6d86a445afc4672a335691fc773acffb19ca6bb9b80ec1d1be013cdb3c90640f9171b9249ca66cf322927290364a951be870a5871c5869c71ee4bb3a6836738afb6200a25f8a8d98c7e2f94bac58ac0713c527182e708252495048c575c1ed06c808395b8306a1bff28dc050f4c622f822d234d105d40e406a5ec0637a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_367 : rowClaim true 367 1451 5715 :=
  checked _ _ _ _ 92 0xff11fd19760660711cb93b1481986220fa7de1e625d8e931da5662f854fd2ade6500510bbdab01d4035eefa87b4b13aa56b8c3c1edc5c57849e1f8d72e99bc579da7dd121eb3a21e1247afae60b03ccb59039d854177457a187bb91553d0218b94a49364af52f8521390b550b84e4123279b347b46fb37acc70edae771c7f44708e7832da04d9011c8e99279545b8f478dcd172dbf12709d3f2a8d6e0f4913e75171704713d504991fcb69faab2349bfc57ef805920ed9b2f1579bb720e97c5ada7b1433897d6338c66c76baf4e6b4904763e956fb68fe5c98b42a7fe250ccf25f95d07271f9a071a0a067815c6911e0afc2ba1220ac51304a2ebccf721b3784bdaebddc576a4c9e18d1766bd5d7cb71414fa4947ffef68af749887bb0a3dce94c96ade237290eec0a3e476ee94bc096975cf7cfa820709a983d580d605ea63e049df1cd7630520007db91f7132305bb5c58d4dfdbde7638032c6d5f00e8435b8b8eb8d496757bccc6d48fed901091ab1b2939400a9313abf49f1ae52c9c6c7e4bf507f01364f77bd9215b4b8eaf1ff5ad6adfc960f1702126e754f2dc8158c3ddfb28b771605a6a98fe74ef01d2446ec8de9019882840e0e1ed7454d6715c9209075907856a8c67f5aa06353978793a42211cfa3be1dc4f0fd86d2ef00b4 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_373 : rowClaim true 373 1451 5623 :=
  checked _ _ _ _ 59 0x43dced90b9b5b75a7a6e96a7a943885e77d07c36c82315bb810bba76871d72383ff2a86a43cac0dbfed66fb3f1e5ab99132aac84062ba717f8ad5d07ca43fe5d0214f8bcdc0a2a2f468d4d2b9cd661b61db4887fe4de2c39213e2cff826250c4d227a472d637d20f490f24ffea0e8ee05072adbdc7cb25f816a1b1433167a9617d3ff632ab3c1a27f6c64ef4bdc5cf01f28c1bdffe7bcf6584f4fa701fdc8957b437513d4389f281580ed296b4c5f187cdc430234b8affe2c6cd5a52d47b3806b01a75250dbceda7590ee89fc032c62c617e341c1fe4bf9defa6298bf88842df52f1ca9fba2038690110c26936284b7816c124673ab3c13899c8e280586f2f8f0869c23d8f545691f3978145a4134300f4b62d9ce3cc839260de11985e1e288a5c9fd64d7b7f31419d9a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_379 : rowClaim true 379 1451 5534 :=
  checked _ _ _ _ 92 0x12076904c4a9f9b3f25d6fb654ef762d20a7b426fa380635eba69fbcef76719feeedb4925c278782e9d7bf6abe8e419788ff0aafa00f4b92c9dc2be975831ba302b20e6b975bea777b14aca9493e4c3b095f68c4531475ac976677b383286491bf3b6318b2efb38c4cbc9f61f4dd4d51d95a84e15011f9bcf69e488d26458fa40179f0915d50fdb14d68f92bebe44a1aa5d7f71dae0c2ad6139b1948786e37f2fe5b63f66da21a3e2a9089f9d2437fe1e5248faeb35af1f65e2c061b6f708225003f86df5a2ede5f0b3767b4628ac1b4a811e79430d8e9bf10f4a29b10e51bbb33859a5d883d964e1f88c8d5e27d3ef100449143c4ff25291b5c127715478ffb85937fec39ce7973600a9b5ee777adf8f1ca05a76db66b404792ee47739b387ce7a4c345fb6aa9b1eb3185a432d0c50864cb09b9fd5ebda1b13bc6d74c837b138a1c31c727d039a921a13e5925532be8c20df1f1265385dfca92f2d8ddd5e055e1eed93b0de1d96b1d71590ee8be1aba49cfff4a05e9c7fe2f23522e08c113e5b80080692b3e706f77a3601f392539e088baa1a73f03c8360960d7aec2f050141337cd5ab93d6a8a73009b67bc53eb7d4a017bc24aca6b815c1471c50f70f86d21bd107b92adf78fd7d2df831e2409a94125047e44e04ee914d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_383 : rowClaim true 383 1451 5476 :=
  checked _ _ _ _ 94 0x43cdbaf110b765611d9f1154c7f4c381525e5d062d9dd6d2eca8c546081dad14ffcc3dac01da85b1ee727feef43ad5b051d7c76a9506799bf6ab336c1cf89189fa1ec8e729ae6a07179ff25ac6628486029918446dbb88eab7702a6b4fdda4d69f0a7f90d368dd715818f1e2cebf6c5147d3fa1f5c502942b0208395d5df618352d73f17b5383c2ae7ac80aa209080add8a5c97a7bc4e1f77cba4f0ad1faf4f22d3bc6941e9cbaef4d8e48a832747022034837da9401184793a61839413252ef2a0d02c6bed8b6651a62288473a3a005fb1846015c9617ded275d3e4251865fca38bfa8d866ef86f4f729c76bf4b555ced3fd6da39a8f69d227766e734c7cfa5885397a1aa4438317087f5ef158a281658f4cb5906c5a5b67256a11c01e530a8a07dbf9b2e16b527c66664ffd558714554f48624ad543ccb7419071427b1505d11fc7754546693f30615552f7d633b5eb8a54633dff6f94c2c17b8f170bd06e5af8c3749b698a78865b9cb5d05383290c97d1a98957c1cc1da768525e95c47678250e287c1490b3dbb0d673d590136bbc014a9301b7dccaee0d38f1d84c346fdad5d6f63744827937b66d22ade4c78461fb56dc15d4511c247ff54b2eba372a705fa6656a4c38da4b2f4788b867e4fec559af5dee9775800f3295ab9630fbda80857149c0c67a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_389 : rowClaim true 389 1451 5392 :=
  checked _ _ _ _ 83 0x7a3b2fa49fa268ae09feed297d1d412caf422d76f513d6751622263fc09c043dd90cf50130d6e43e459fe08764840951070b64a62f534b58b057b7497ad290b052886fba9b4801dbf1796af5b8b4dac3397cd32d95a4ae22edc2450bd0d2aee35b0c3c3a61a536aa1cd1036452876ced4bf9a7e2756ef88b62b73bc069df00e3adc9eecc767bd737f441b2bc541e101700c6ae9c2468fd2f531d0d8d3ac2efa2bfa95694219215f8aafe15f7be6a37bc3d3a9e454e6f0986bedd18555a62f656475aef1aca3fe10e164914e4163fb95d027db25de3afa0c8d3c09aa3fb317e4d7f043491e5760043482e1de74527b1ab02817bc7eff9b7c62bfd577d532c62e3e4166ad19802ee401a519f3aede49eb70d953efab300b79de0ba6a40dd4227ed2943af5f25f774976e59fdd33eef068e107bbe76c6659772594e8723508ece334be255c3ef2cbf84ad101f23e4f7934e9ec9c5701a54b1e8cb6513f22dfd32fd724d983eb4480a0ef04f6d64f6b556b85637c2cb66dfd2b054101e0a964b41ca65be07477a3bc1551c4ca8357bcdc8741fa193f99b248721cb41ba24e30bfdd9d7188cd13da2d58d20414ab4d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_397 : rowClaim true 397 1451 5283 :=
  checked _ _ _ _ 75 0xa62cd38ad4e9c58883e32d1da3ffe815cc1d1c164ed319b6fd3212314a282c66cb5f4e39f7cd889e9c39735da92b77df065485c979648bcafb375f3b2dd47281a4c277b60dfe23f46b9ea426a9c34de4c6c8cd877cb2a045730dfe1641b1858b487c06233abcd59ce1992c6f006fa1a7a94ca306c546fee11b2f11e5d1d8f61c737ede3c332053877a01d3b333338706df950586945f3ef1326abfbaaaad93e29d2ac3e4e6894e1ebafe332e03f25ba583b9978f7ac412b88a8e7c77e90f8360211b16f0cfb0c5d60235e3b6c10565e65e3402311c4304c926b0f059350210a21c54045b76df3848e6fe8114b11527d76ae67b590e9be84e02d838867a949b46ec2e5556aed1ba52b0ae35b2b3844b97ee79efd6f832b0888f5b321fa798a65c21a37819e3b560b980726e43efe37022cd5b9d0989a767fae26b30bb2ad9ff8f6659cbe315a476616649992ef40d72d5bc2d0737b85aa202f1a87bba0968bb8df25118ddeb049d6d29de7bdfa0e87e2b2c699335448fe8cbe8402cecd49330ec5c9937003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_401 : rowClaim true 401 1451 5230 :=
  checked _ _ _ _ 80 0x702ddd786f7fbf0611384ae439501d059d528af2e8519efc67f78427b257b6a4f28e607a9965c678def90763b9e2a6c85cb7c99f2534b657bb507b53a13a78201fe4ce3786fccafa93b23ca01182c67830b1db179b56b7b3a05e0001f1d14c367eda17d067b917c3df82dadf28c23714da5702ea1f9412cfe06729b875e568b9b810e5a8c7e2cbc5d6a6ba622d2629d8b61781e1abd15c5c6b68739d9d108381bbf447e023e8eeadee29d1cc0312e8bea5502c8251c9a9dc273f0446d13d9e1919a73e69ccd55a06c94e1b192d71524481b9a3d7e882785b7fddc6ec01f0105e2770baf71206af6c87abff2c73f79d8c75715e48be217a6505673557d6b2073ce6805d3af39bcac480a9f734b7e56fe13749bd6023f8f380808c5c4f88c6d491471aaa9a5240c977bdd46468016a1811e45bbb6ebba105f01828fcdf36373138157bad4dbbe863389efba387a282461b68af21d1c5040e745a47c2975c895fb609815e8fda7cfe90d2d900adcbc9e2951b9091c893c41f5abb9e7c5dffcf30b305ae94d7b0bab0fa9b2a8b5b03ad294e957fcad91d01f46686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_409 : rowClaim true 409 1451 5128 :=
  checked _ _ _ _ 54 0x2ff892342a1a65e660954bb5bac8310b981acfb0842f0afb45aa21f70fd79312a80917560fe7bb5b0dec8c965956ed78d81c9cacae628b71acd90e784b7df6ed049e0d2fb11450554815cd0b9f3a193f4c80f2c42b90a75feaa7d35974ab146dd2492392aeb66c7ab14220e91316f4df71fd9c6ddff5daf07f2c778dac8e993b12e18417323cafa15c9528c9b2f9318230e43ff437e1ed943e3250a8deec67512d1eb65d85adb55f675ec148565cd54121c33b919f440a89d6f8dc2586dd368240b025b6aed70628c0e5404e50b33e7dd14ff6f0b409d7cd556d6898ad8063e1099bd617bcccb15edc422513f8bdc46146d2a33a9ade38c19b24c1c89346320f48b1677104ab20dc811e2e057bf83a101186686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_419 : rowClaim true 419 1451 5006 :=
  checked _ _ _ _ 108 0x4d68d8b0ce3e7c321592c15a0f8b046ddcc61a101a8fa9706b5f6da439ef02e33aca80b7d1cf1703577901c8bf6075e71e4b6d0ab18dc1bb376b33ec01de4d64db7a428382a3209377b528986962c2d4ecad4c0a8fcdc0bd40bda03033aef52387c3b02d1c2497d1f399612834b54cd0a345e50ffb84d39f86d1e9c6f8ca05110583e96e7ea437f65705b47f2f81e0dff519e312144f30ff1e58ea8f9d00af66825468482f94597ecc99ab41282fa3d103bca475349c4843b30a0801bbcbed23f392f34a51c393a2024a54a81194022284d30a6bdb3adbbc6a2e5a6c892713f37c288d8163c393cec4903b9f5328d75e5f9922b1428f0c9ff1fa0bff16fcca0cd020670263fda5e5adaa1234996b91f54796ac0b676346d3fce34386dce1a420df7ef2cb1e3cf3e8e615939bf7e1593cc82944f9d98e6b228c3c298998b07d9ff99972d7139e598b53d81090b8ae47f774fd40700bdefc0ea8a22bc4d4630a963613579d57a4e02ba51c731e0f41aed8cbc022264656362ddffe6a2a385e09851d688ce848f3d413d9b4569fc99d8448d20a9fbffbaa3485b1370f46c246e639a70fe99f1837585a5728fc0959bb5a8c45437fd05ecc7cdad7ca07f4fda0ead7d50a1ceb87f5f584ed26b60510c405db57fd4d15e955e7f6d0eaf91dbae73d87fc58636da67f436e1d0e17b08cd9f8f1d5cc13a844afadc6600b77915c48ea74200a434cb2ddbb6714dcf717a2eef6a52c1d068df3107210d582506952d8c33b939a8c771dbb36867131b95227d34486703480a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_421 : rowClaim true 421 1451 4982 :=
  checked _ _ _ _ 95 0xf82c8fb463aec15492a1f9b117a1d46d58a73e26517b19ce4da34e9f4900cbbf8a6499eae3ed9f61574ffae0c03c42d911a45dfccc9c1df7775784bde089854b5efdb153d3203b981de4ae721c9d8ca386fd02abbb72f1b7fcfe5400645a6a03eaad205dcc6113e9ba0083d859412ef62105870d6bbe3efabadc9c9b9f39a396002122cba110bd4ab478713b2cda7b56eebcb22813adb40f97676398971cf545dec4a46dbdd1ca2369e4d0edba750c190a3ac0828e831cca65d2998bb1adafd1ab02588d40aded50452d7fe4a5522d553730e9a7fda6e408cc30d3447cb200eda544d660a4abc847585698f5ad2f11e156b9feae001e3a99f21f6bc7bc529446f83932ea0579bd788b2e47d61a90b8135ae810eae91ec8fda780d91001134969d851ded1863544c41537787aaad15bd07b7b245a34e22c453fb84c91214872a02dd2bcde8cba589dc3920bcf973b16b21e7f1aa0754ff0f576e3f6c90e77962ae4589c9c56cefa7b135ae0a1d60a1a178ad770cfbe97916f730cefd91a382a5e68e2522907c580588df606c60ffd47a1dac9bf2dd1dd174539d2df638aff14c3134613ebd19cdf5f1ceda9b7d76ffd830c2f08bf5dcabb26b4c1eec9b240d5030e2f9abb79ba25a1d4ecfaf6d7c9f119f8c8e2cd8ca5841695fbaae85c768989521882ea06fd5c52703187e907002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_431 : rowClaim true 431 1451 4866 :=
  checked _ _ _ _ 68 0x12dbd3199e77d7ad36693ebf60b5575aa9e92d2e9bcb3d93cbb80b4a91eed76902a430e05dbbdf0b56dc4f5f060898e905ea4e6addadbd837759907553371876a7d88c3ecebe7d917dc172115cbc9b2ab536b52ebf9371aea490b5987b629c0bfb4b8539f155fcc1924f12ac637a9e2e4766122eda22499dc7d7b1ea63eaf22309954c30b6d742f58e9d1b5129075c8a024cb680c998aebdc351b3241364e216e8e5484e8195399813ded333a0e688c7fb4a1dce3fac5bbade1ec46554269b6cef1fc5a0f02bda9a0e32042e63d44d27fe0cb2c0e75bd6e90b99375dd3afa150e6ecf4bd7b6e75a148c68028d6e4d603f5d7b6a13680548a430999066dc71899d232298c0fdf1fce469575077cc4ad7e804716efb0e5b8a543e6be0eec33e96c61e06283c5668b86318a6f00e276de378d03cf0848f0f6680d12577b2dbad7cefca87a56f20c7bf0c42212cd6dc2f6746ada9d7d00f8c16f3006c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_433 : rowClaim true 433 1451 4844 :=
  checked _ _ _ _ 43 0x20eaf53a5b8033aa290668068dd019031e286720711545b7184727d6735b8576dcd521ff1962e6b60505e575ae301eecec7b8a9d80d6c7b8dad891b6fdf44e8e38a757a4d75df4b508f0766c77db220f8aa8471603a9a542e92d2496e883a1d0d03ea44fb4bf612da7a77d691b7cb06a8e234da25d2598f233471ac2c228826989051bf876b53e299e75e5f85f18e1f9f720dd92e0d30b4462ed8d4a8eaa9d9d673205deb0eba6906c6138629ed06f1143f0d558712ae09e64a42bd6ba9ce33a0c42f7742ddff0f103e44b51288ce08a2b02f000c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_439 : rowClaim true 439 1451 4778 :=
  checked _ _ _ _ 81 0x306faef3e4cbbc8ca0fa9850c7577ca4759e089bd0b34de8ca68b54901e3b3ac8379ea274f40d505cdfca247f2ad16e0d6d65f100c5ea37f6e4a331867802b67611747c4f5c3536180fa23ad0935d9ba33c1a724c1ee0fb380500f57ba68455b51dee9c0e2848253bf3c5f3b0997d7749f1732f2b132ca58f84bacf81f235a021a34ce1f705a81e644e3d2e801ab31f9f68da1990d7656c164601d6dc5a094bb37eefe714b6fbd9f414acdcad628b889356a4d845181a663df3100b01e6cd7bc05c42e6ed47137aba1bcc0b69b4dd0bfbce0f648f68f43942c88ea61c2a1bba8325b56a002f2a3cbf53aa21a6206dece5358990e4c502ba797b1f8c7bc163a76a5aaca5fac8a0ba8cfcea39ff6725538a6184b97e6689e21a1c6668ca2cdf6844e8415fd29c1de18b5d7f704b562cf020424c5179329ce01da5ebc77bd45a78aed7a6da92e019d7b8eac80d62ec473d3f96af9ef546fe9f73ae94d89c9dcb5e903cd77665ee7530d1914fd0390606f3aad1cf6e8ddd967b3929b0b19da1a85154b53f79c0d2fba6c94395e9c2ccee091428a309c81644e39e9f6876427bf61248593a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_443 : rowClaim true 443 1451 4734 :=
  checked _ _ _ _ 61 0x70599df9f41a46eb1bfee41742ec41f0c0367622a16f94f23acd38da3517e8a520d72133584b69237744f0d758c9fd006ef0af2c5b94296f4653580ddd240110ca195a474a71a7aa47f0271d8a75acc3ad6aa5a091a232d2fe7aa4be57f51935dedab2341bb1ef7e34ad8a185c810a7276f2838f71cb0cb1c9c459de0a935078ce5cfdf6657db51763e7df8a5e15a08388b5e68f6c3b797ac5fa469010ae5de1b3456b10f43a1827fdc3e7f1ee6823b1c25c1b6eae37da8e548aff7c4ac7ffa4b62f758747ec24b71343b690d137fa464a8289816d489e160a2084ebbda4ece7e349c0c178aa3f3146e902d46fe10935ac144347bf04f1f82addac70fb46cea4317fb50b1649cff3b1130b6b20d9d16dc239e563b6f63c462ac8086008c1c543b8d3db9cde68973fa3caf7e91422f913cb09e901e60a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_449 : rowClaim true 449 1451 4671 :=
  checked _ _ _ _ 60 0x2343b118422b4b9516a9091235f417b2a6d9816bb4fe228c0caf934c797d343b21f733477df37d8b743d29ae6a629e96122cec1d588e4b92dab25cc3e13c99078027cf7ef6b3f97c52b31e67eb8adc2b5e3bc428b6cdd111bd38cf98496871239117c98b919d44313eb8afdd5a4e2a1ecb07d4917ed6c570f69e812f2ed88cdcd5132930def521195969fddcf4676832249374afc939efcdecb5d70a3cbb0299282a278869a2624966361ead94d25f1da4ad19d8aed8b9f5c59c7ceaab1181cf0a5a7fb744a4d8a9ba2e3c602ebcf58e78b64d9b072c303b2b96981dea52e883e0452fdb5d7615e440da8d74ba3694af951e0ff8fd45fcc6fc357d698a961d849cb59ef65f31f67d3ce5f12faed600f1b3e29909e03817e3dbb6c5a03c1c78e33a925c1f1f743227392ea080f86a0ddc06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_457 : rowClaim true 457 1451 4589 :=
  checked _ _ _ _ 61 0x1c23ffc27ddfe79f9a136724c379845b8fc8a3c2c5f7f7036aae3fff0d042d7785a7df04209a29ec3be361776a30f0d935639cb0f12601677a8b85487e22a0e5719479c514de0a94e993bafa969adf2cc7be78d27beeb1b5167aaaca2e56a677566e6ed4dba95ee14e82c9c8bc543a70f438f090f1910244817177f5aac791cec586cd631c545d61b6c6bb44d3085e0fc6c0d772e08d0c5e3ec981c047678d5d27c95be27f00787f271c643a67859a89c49000d4257381edab73404cfb72357137e56c44c1a782ca1aedc381ff4fa9a54d42f0b9945162b8da6bda9f93ea7555ecf77e0cf532690df368dfd58da2d33699fece5dbe331de16fecbcf23635b43430e4ef43bce8a3fa3f6e2d7d1f528fec943f6b17a5e0cd6d8f7eef894d3e21d84bab2eeb46014595bb36863d75f6a027be23a101186686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_461 : rowClaim true 461 1451 4550 :=
  checked _ _ _ _ 71 0x7688708d899ab2f85c47ccb086edbd23be550c36a8bc0f32afde40cf4e62e3c408b469fcf1e70797b2528d4b81de6e13e2985c6d62ad84a19df9a4a5636ee149f4ab5572cac45c55fd99346666e4c94db81d2c8dfd203b035e9867ce23b943b8cf1475bd55e2502f77271d7e333a7977882123febd0267eae04ffa698c09b8f93668a79357cadf498b4306d409ab203bda4714100cb62c544ec048021587661a3b99b1d47d11e84b5911c8824981cf5daa2cb6aaa2a7e1ffd1d9ec4fb062ea3fd7a9573965ad84c595db81b54e327540558435ef8676c6addf27b1980c306dc2727958befad4c2f4a3bb88ab2296e10ce46eeaddaa143e409a3dc30f3ab98fbe40fd515b08e3e6b13302f2135c86bc09722a78439c2f2d603eb3f6f2b6b4fdd36f00e2ce3fbd932c820310b2831f009c973fac2b810adf1b25266761a12ac914314e8916fc5651bf71795a9978ee0f300548055a9dbb92feedbc6ef5ad088cfe32856e431b0c7c640f7fa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_463 : rowClaim true 463 1451 4530 :=
  checked _ _ _ _ 81 0x22d0b9c60c16e4616e97f084768a223f335e32aefad8393d6372b1052d1ed36fa68f6517b179a2957c636b0a9711dcbfd795e802ec6c1f8c83baabbc22848273d8ca58d2cb230d3e83de4dc5c952649d5e17435e0b4de61c4ef5557a6920820c4b603375d6d8286d5ec141f2208fdd4ae4b91b512475efd9e7395a4c724c61a8137b46070a6e31718846ecbba987aa4e4634a905186a3be41b072f4db17e6387ef0784297ac462b83d2c3d3aba9712bdc16177b4c2142fc7c5355f76f0652ae077b29b66f3894bcc3b341fc5582e9ace1abc537d0c1f6d8a8a2c875f60da89012716ed3355109bfe8a28fc7d6b18399f69de998607ddb9dc453addb1f0c586e403b9c34c91f86606819e41f276b9be02948d7935236c6a6dfba1a73fc5e6aee709dad079645f6d94c3d76068ecefcc4e88180ec19f3f8a3795fa8698a43eb57c85549f9f080058efdeca4a870ff2245c0b76c8f8f7396cea29c37523a7e269da27be5ec08c001919f70032fa0e608dee8fb77bd68aa8fd9e0cdccd86f37bd2916ea33cf2cafa6419fad329f4eab13cacca6180ba30c34cd449456e0c7013cea9df0024 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_467 : rowClaim true 467 1451 4491 :=
  checked _ _ _ _ 79 0x1744793fbdf988e5c9e349dcc7f2b0e58d14ef878ea74c09b51ad4647583745f79b7ed024f83e25aca7e5e87dfb9ce879f45d9dd9fb34375436aedb773b4669a79e705118ff561b7061e28840e1ebb507a4437e38e5834e01a8ca7fd9557bd1831294a67cae8ad560b96bb26ac5a0d8a4138c1086b8f0110bf3a84d275be0d149bd0d0881d0ffacdb96a02ff72ce2bd5fdda2fbdbf1544b0b9b78929ce86e92e4241c636a51725a3b4899e2e8375755f6c321a28ecb94b91d5f9ceb46406eb024b8c8ccc5f4b4dd0533cad302eb0203358357450f33c37b8b41e7825330643f8ca5b2daf3777871720112d10b9f46b276d64ba26f2428ff9d2ef3f14c9732848036801b235ac1100afceab607036685b2341d3e1054f649359349a63883e87029c706ba0b57a2d4a8ecddf7b0e3835143cd735f58d328592348018e42a10204fc0e0bce6380fdb3120069e081f9f35adbfcb4ab9754c933908397827fe5c9fc18946a28694866f80d35bab30cc78521f79bb7a82bb43d48ba4d465e8bc7656fef4bc7506fdb4f15c163d5dec1331af0d57acff705640a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_479 : rowClaim true 479 1451 4379 :=
  checked _ _ _ _ 65 0x12c845100842c944d49739aae1822420bc422f2aae5f3e03e936db98eaf99dd712c4121ca08e93a78f10c3ca9c413df72f7688cdeee200a25016fe4060729c65d51f4ef8a002536ce86eb40a72c62292ae3ffbacfbc00276159b6a17fd60d80e8b383b295e0dff9b4874a4e91d5da0edd8212571457ae153d56c06b3bb71781b31acf454d65c17fd368a41f563db41c2dc01f88b08147c4aeea6100b36ed8c9da2966cc657281ca3a2ba5fdaf22cb22a853ad83be77ff5c225f25fa44c369a676486d12833f06e905f50b44ace7a64c5797f4f3d95bb21d0f12815e49c7c345b64075e52339ca8538a9dd02f95900224034ebfbfe7285c629beb1fecbed6a493cd586b237d4bfed9417631a7cf8ceb6cce53a237a14c6899ce58ffab73ee839876657744201ed6193da0f55bca5f1027f9fc111443185bed05d2d85aadfa40c8c92fcddd7c3132bc3223021c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_487 : rowClaim true 487 1451 4307 :=
  checked _ _ _ _ 75 0x696289cba3264fd190d7bb6da88df87582b578e8f439f1d6f6d40aa0fa0d6c1eee7f5b1ec9c3dace4725c733fc13a5ce60e4c774958420d8d059cadca39dacb19e801ed5dd56b0c9dad1c44915d35f4ee0663836cd731dae1f46fc9484d0d0228696c58183a59df1b0d027c3fda84e6be90c473306abe80b5d9b9beb277681a2a925b35e8f9c3c057ef89ad73f8f17a604210f2152ebddaafe2bd52afda99c697cd85213c91c03db80a80b2e9c55686fb02a1a47ea5aba7137a5280203152e2c66dcedbab318d36561631818611bc61d1f1f915bc2e8039d471e340d5448f8c34bae08a76015742b237d7fb51cf248413978b579587a464b78c11749aac29fa9d76c354c71dfcb591b9517ef7d941159de356e8abefdc84f8bf000f2d995fcd1396e888315b625f40b120550440c3ad3044130e16cb3c55511738c126b22abd5cebef5ab7242c31a5802cb5e9243f81a53a7fbbf53a56a64c184b500cb70991c4fa505f13afac0c3f7d16b0cb14a739d2fcd0752d8a22cdc8b0428aecbc7c2c8122e0002d (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_491 : rowClaim true 491 1451 4272 :=
  checked _ _ _ _ 93 0x4ebf9a133ac480a13539e6d8b392eaa0a46fe47754c2bc1c3127fcc739389318ad10704ea9d185021a63fd2637cd859374fe0690f56a53068640ebe26c66a75c2152afd923bc58c1bc60604cfaa73da4861cdba3a36b3926985aee36c0a5a0eaff8a7611cf8f6be703fdc74b893ebe3a81cde2fb1830c1a280e968ff3c1d97f91b0e645d299e1c89945741d092a3692526196458ece9c1d7eb950aadf7d7862658d33a1f8a6aba29331d3d3a5812f1bd459e655d735e2ffab2697e27f8c89367c8a2d6153102ecd5fb198c9b7caf56ea4653b087c96a59f697a49058e4a33730289a53f808ec3f7dbfccba92b5596bb1524f1debd56410ba8eefd2e581d4cbcac5aedd53b66d0dd37f818088a4bab4a375c384b09025155a8f8822034c557718c54cdf4f29c217c57c9331ca8d1d1804b5cfd1ad4d79a7f167dd4bcdec5037cf478b39ad5372567cbf3ba5545aa55f9b779019b997c453b5417f036a6ac2c4f3f7c302fadfbc0613689bfa0339b29c168578fc0c81a2064c3503ce73ab6d99f0b8c395f92c09398cdf212bce4929733808d990b817faf5a5eea3ad11d934908dba6b5e3c707093210c528a43412f87b3afc59b68e19359b3096947b42c3e6e0b6a8a3abb2136a069e59ff4928e924e04298f1ca0e0efbd80e844849e6fdc04d7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_499 : rowClaim true 499 1451 4203 :=
  checked _ _ _ _ 87 0x14e8cbf6dd18e1a456dffe9b7567785bdda71ae2bec48d1af35247d9315b57e33cf0cc7527d32f4c061a3b73ee96ef3f16171433cb82d1577f8362d75f2cc7ffa068da9c72ad00c0bfb2a835b104409ff73b46dc3b98467a0fa674d8e7aaeac425b70a6a5319cbc421352e21104b9a107677696c32f1053d9cfaf797ca5e4df8c22e3a9f20b498c4fd3a72c586e91c2a267ac8e448404305e07c8ba6ab1ffd5cedcfef02105e914d87c455935a130a8646c48f7b01e3c185c49b08755cc6ea00e606aa4d96a50ba9a98f9200eb4b0a959ba36a9ef02fffeccc5e83761a6379f21be8ccf40bc4691df5e54f7b7988c44826a43ffb7732ff1b7ab2dedf3ecf867a2f7499992677233bef43fd10bfab27991e86ca198e04e5cf3f37791ca8d3bbf526a98cb014fc477d71ed6dfa308c2674376485e055e7217a8947b9face3b89185d8f55052f6ff49b6a8e80800dc1bc672474da1c13938b44413677da36579c2ee70d9ada961720224b0f60d80651193f2bd395cbfe5452d2cba7816f176a617321a9e1d0e47d62ee9ae3da0a2c628c946111131769accb01249fdbc12fa8ccfd4bf9e9c739ed4cee4c26c8ee5996da6747fc2a317d22f4bde1d4717ddc2b4488a17f16b007e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_503 : rowClaim true 503 1451 4170 :=
  checked _ _ _ _ 67 0x9a00fb075853baed73f0fc848c52e47af00e3ba66840c84c64bf5d5fa102b0ba43ef093df515af5e3c6d878800751dc6818f64297e4c959a6beb525684fd4e28c890e8e023eefd7bb3d771ed95f43100328bd823edf05aa43f54052234ade54e00e8353099fd034bff328844619f95a92102b9b501982879372aae17fb9bd7731eee10a2ccd41586306ad5f69691127c45dd88fc0113bb187b84d8ba77550d6fa0a4abc907f069f09f8964f53253e62ecbd198fd297ace202f0452e0531227966209dd473fb9f00b7707e85b7cc757d2f5351d75cccee4bf8ba2c0386007440f19bc271e1d7053fbaad8a045cfc8bf828b1b85a24e81714f07bc9d19ad74dc96ccb020566ec5aef06d8109723769d21b188d5e9cbc661266d09d64d7d6563f7ef01e8c99a090f88563266fc7c1b3a52ea615bf87fb81bb709f466433d0d4429a949ccc713497684ffaefde199a3105d40e406a5ec0637a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_509 : rowClaim true 509 1451 4121 :=
  checked _ _ _ _ 75 0x2ea47295339a6748a9fefe51f7ace49f73c643b4766a00d11f614af0c26249bab95c82cda45571eef23098a68978aaa9c5533a2110403b8601d140cc9982ea0cc177eafc88d664246c11834ea7eff79b1f5fe61976cc70d17bbfb2eeceed9b61141e02b1d2b772c5c8afa02c4331edbd6d7bfbabaee971e1e8a75f4cd565628133c2212d8b20a9375cec7ca269c80ea0b9fdfbaf751874523c27e947e7896acf95c7e99de1c33e5a3a54ca5cf3b867a8b95183f3ae6c36842db28008d9f5340740fa3dbc232cd743d9d90b16ae15508ede90e6cee3637c9c8cdc3eef38825c05bd8e6d3f9f54474db49a8d7c42a476ec7427621a352be65a9c1b6a3767b99ee56efca235564738a08c1a436dd95e05c6b83e84485a9b96ee0da0e48bb4b94193198fe028d1c31cb7ec1149e3d77399df43fab5c44fb971c9c25caa3ba995a42d63c91e3540f03e71e953cf5c41b469f7d0d45f109f614340fbae190e397c8187ec83d97d6e55f2d4d75092f93f067f2a704ef65f4a704fe361dc9da81e01c8331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_521 : rowClaim true 521 1451 4026 :=
  checked _ _ _ _ 79 0x8ce5a79810b9e124d0dde38304180ac0df6a60f0efcd6a4f6cf698f7f1ad36da434fc65c17aadb26b6d3d2b0a1a0a4961592b22e3bb6e6ba607aabe20420ee73568e8d8806bcce4a66989b5cebb976e4c47ed127dc2e7ae5b05cef5115308df4578900b777c71af9266bbdc0176c714a697b8f4e188b6fadc0811897928d936ba08ddb3084f9627446e85818d64e60580aeb78c92219a3a3cad2a2deffb2de107644df9ea5346754e9d72cc4a764077ee0c3cd7cb34a42d182a6b5eeb84eba4d1360c08ce86bf66aecedb827ec3ab3d10f98141ff00f4b78ee922ff2ff49a8dcb84b82a6a9a22f253f24af44818696c771c8d58ccd5b9d3dcb5c34ebaaf289cdd05c03a533b12e172f3591f0a70995ac5e9eb66b04ee8c695d2618775a7b6ef184897d50eba0de6ff531a5ebed8392703b632f218e623433961a0ff95c9b38cb7a1e1ecb2d2eaa671b39705a288333d97c687ba9a43d380cda0d5357942a8dd4c584106124630178a6e0a60ca4b425f8860ff097e069b03770c1239667ab21d64fa7ccdb407ab2775f6a0279f83a101186686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_523 : rowClaim true 523 1451 4010 :=
  checked _ _ _ _ 87 0x549e1ce7c991b9b158a140766cce6da58c05de3dd55643b695c402f43cde34e769d38773a14e86ac5fdda80c991f3771b402942c410f1d839b1f7ecfe2ec159b5d5cef5eebcdb38d0a2e411822b58afecf9ad610b85a11b17faf222cb2831f4ea5c817c2fd3df79b3609f05278fc6267a48c20bce6ca77539843b20edf20d52cc5588235527825f7c4765034c8abf6a88c39ad3455c224510a93108310ee3d364eacc1bfc25895a9fbcf11b95baa8d951477d51f4ea7aaaeed1fbf94a28ab86a927948c613fe9de998667e56e2c6cb8883a1cc44725bc7c196e1cfb8e4ce4474ee1a110b5992cb631eb2e5936a2868b85578e1d5fdf7d96507631e6818fac2cb9e15e878fc51c7a851aaa152def77eff349efe9f114bcb9f5d802995b94ba512e85d1ea7cefc06c4a0dc36d071ef6af2247af16f657568d2963dc3e9d2673a456fdea3f26effd532f8b5acf86bf097e0cbf844fbc6035cc07508279574e2b769f380b396fecb76ee063db2d78183a0b7ddaf03f57459dff73c9bba12f5782ba496aaf01e4ded4f1971b465273e90d53d632def9f738a43dc49faf7e3474508a67647b6eeeedd80f3fc3fd0e481d1dc4ca2c5adcc0fef0dba4be661c170a0088777002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_541 : rowClaim true 541 1451 3877 :=
  checked _ _ _ _ 78 0x54cf8373395208bf080a39e194816e19c653c63d4bd194381bc527c672b6497595609c5b8b7f3ece34a2ad8ff2058cb6fce583b3d753f31cfc2532be37345342070b19f4bbf8b5b540582fffa71bc7c5b68ca0026cfd100119573f7dc90d1d2bc7d9d0d8e579fd0f08c947f821a2eb40506677fb2796641849fcd74012e79ccc22c44748797295d5fc98de2103698b5070d96cbe6f4134f2e0309725a8d5e6a4e48248aff7df47803b64426ed98853a14bfc4cb1faaf41541f4578308a7ac49b4c76c6f72f7594d58cf208a2dc786e35dc670a2d7ef7865fae3dfdca7b3e87706e548640b4f48d50e92557ca6117a06a1e996cab1461e34322fb48b878ff4125161baf0d5bb47d93c320bb0cd8fc5b0997649d124c62ecf081cf3994af1f46360f0b3d9ef4e78e5cf7af2ae251f5b90890f2a8668d31612189584c4451cfcb9ab4f1c910b5fc3b1bc3df0124d8eafdead0e590104e26371325e258ddf694154e145bc34e9264c3ff6242d816d306914bb8349061a4f5c609b39795290e0540dfdb4597d1fa4fb1fcb78f77444b06e4968a3001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_547 : rowClaim true 547 1451 3834 :=
  checked _ _ _ _ 57 0x9f7f379b6f32c671fe15504e9fd6cd39d3eb07427828be38b0d32004bdcaf7243d13dc17513564734e29a9699fdaed54ae23c6c717fc060e766072273297ecc07cdd866b119565c488270a18be7ca5a7e1cde33c796756d29ae2f9f877c3877ecd867f144d714c690c190710a68f44df196d39c7d616a866bbb770d27aed4ac049c20a62bbb68d98818fca5d1f9180fc83bc69bf9e53bafab3ca13690bc42e8d965a6f8d0c843cfbc37fb2c883e0bde8431b4abb5eaaebdcc72eabce7b6aea12c3050995395b23799d31e916c57812450b63384a7ba6e64c62ac6636cd2413bb56ac438c21232607cd4efa64af7fca5cd0acae748fa2ac493cc5174e8768cedee78c7057bef6391dadc58f5bc661ad45bbde0df3c4636e9a7ad815caeecbc09a7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_557 : rowClaim true 557 1451 3766 :=
  checked _ _ _ _ 61 0x258798ebed775813679bda0a9a6ebf39154897cd043dba2fcdcc37a4f4b1c17aa8e0b9cb5af7a8db4126a161f30c4fe9c0bb6223603e2e2ef0d9634791793bd32eb7c1840a02d3dc7e47faf071f893fec9b9b7170adccb162d6d2e067d4ed45f8805373f620bb8f67c32ed864619073d09b21a22d04d85d9c3aae5a551cee20ffd72df6e459cb02c362be71eee5da8956002cb5f8f11265faf901ac076aaf477805b34f6a11c943e90e9ae9983952d4a780c2be7bff2bf5d50d555f5f9f809a4de4640292d8295f41afb432ff81539bee4bba7f7e737ff64785f07e58358a91d82ac74b206229558e82c05fd6777281435c815f1aec5c937b8c007f0b68568ac20253e960538b0a2bbd856bc882336142fe41f57bf5bc2aac012c51c2997ae2183cde9a1088c6042eea27d620ef491427851fdec1137a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_563 : rowClaim true 563 1451 3725 :=
  checked _ _ _ _ 79 0x4e506fcf8961e95c2f8efda066a726f10fc8b49b1d7f4e5dcfd4bc8a844cda62c1739a042ecc19be6884feaa4a9fc22b4266ec585d65c879f7ce459d25545d1efc5fce6e63d8e3590543b343f409433a9721b881a398b6a40335fda2f320e3c87fb4e054404e515701152bc439637230e5b3edce05c958379a191226c7577b64f18ac3a8f1817c6131853e1f1d3715dcb3637ea33b5080ab7115bb6d8f004e00f92502afe5f682745def7e53148edb459129c5a4a5d1b99fd0ae4269f9b3c208a18e34ac444db64c52eadbc5510fae116d9888759a84b5901c9e591b8ab65467556f68cab4fac297763fe9a27e06ba1bdc4a5f4a74e9086421b6e194b91f7e04aac6c21afb2636f3ea49de1b7f3fd14f02e08a3446f2f3514c8d26b3f29177c32069db554d994ddc8941df0a2f62b3b2a580e97334d2dd1f71332de6d7e6d14df7e3427acec1cac6ac8c47f085d3e819ee049bfaee802f6a730571615b2d18b51248d63320cd45a849d36fe8f091889c5c6830e2eeddc6f38fbf3aa482a5789ae94e53a6499e4ce060fba90ef0646eb64a0376b7030c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_569 : rowClaim true 569 1451 3686 :=
  checked _ _ _ _ 44 0xb2e3505504f43f493209e75dd5ef7f43ceb2fc730722a530a820e1c7ce9d620265ce5bdb9adc33ab2dab74fc5ac97739ef77320e31352d533080f56cbbc0743c2d560cf294b93f45f1838199782e64217002fa032363bbec9098d9528b2767c4e0b7a3f5e86fa0b81038bcc0a70997107cedea5b252c1b5526f64388500da0164d83254acedefa6ed04f3ecfefc63b67a63888918da76c45c35348f22b48c455942e32ea8abcd8fb87ff2d31651900c78d8fe802734cac808730418b678a6c997606b3937ffdc34741d87a1255c72abf07db198004a4725526ab819c3de7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_571 : rowClaim true 571 1451 3673 :=
  checked _ _ _ _ 60 0x63323b64b225baae82865972fd7e38b77a3dcd96326f4b377038a4701d9b8e8acc5b2754ab3b2934342a04e2e8b64002f4af0559727051d452306ec925f18295234110e64f861925d1f7fa246b762e69b5ade58caa4e21f3c1171036978c9f0cc769b0ae40d105cc97bcfe3d4a244e357721c1eade0b698fe2338cd363eefda07a7fc07493009001a18c537261c8a8138ae74daee1642c97397ab6a602728d8c01285c95886484dd4bcc8b16436b286f83d87b9b2a2b11756e0f88ebe9e99989e4044c5e6497b03316df6c76c7a4e7f5bc91e4ec8c080bda84b9957b044adcb69644386c774d38870fb54e7e9b8ac97c02482289b24fda5b8b5309afde54a065ce49a2c14a9445a45a4ad3ef6af2631ac2c263d1be61556af1bf69e01ab8852513a0304fae71f37271f75b9132b141213a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_577 : rowClaim true 577 1451 3635 :=
  checked _ _ _ _ 46 0x1b09bf0e8b723deabd7aa3f17c44fc1ccae2137885cdae4d077676f45212bf5f19f5c1b0130b47bc59730d67b1079a6565b1e1dd20134778fe2a1462f2f461b9da45f5f95d91fdccb83d0fff8c75c8c7f57a0d1440403ec1a650cbf5920a1661d2afd3ac9cfc4f4c1c5f2684d4bf1ab396060ad4b26ae8ab82af0831c677a30f637c7c8743fb100e08e487e989fe5308fa6d3201960e68f0d295e725f4203102fa3670882dcb578e3ea2984259bcba986a68121294b75aa8d1f09b1987899b429dcd7faf64b20ba209be3267142115136b405db02b188105ce1d1757a49b6e18e31b60af859008c6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_587 : rowClaim true 587 1451 3573 :=
  checked _ _ _ _ 61 0xbf1385d074f11960a6bd037e4884beb5ed98ba6defbbe1a94603e25d47ecf106c5436c123f70cc6c4ca0c69c4dcdffd95cca793b76ed34f9ee8ec173e7cb5cbd9f860b278f27d61c65a7f970fb828553804264bf3d2e1b2711363125c05daf17668076a9e4bbb43adfa9976943c97f3e71ba7ad07330038404fb1aba1381f1ca409091019bbd60e83a71c96e56264c9fd90972341b522fbe4c536e9e987a72c6df3b51472952986a282ed43990e6bbd3ab6586917fa7180ccc9d925b801f3debdf1ce4795987622e6495b114b3fc6eee480a2fe1342de823cb7db3112b26d7dbab77a8ac375505d0f3a08c2252158db8ff1b95b19277cb0edc34825b50df02296d4c71a224731af5ae060a1beb3eefe9df28ff632126ac818a5fdf3f4d8c4dcc622648fb93bb1623d2ba0c8c92fcddd7c31323dee13021c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_593 : rowClaim true 593 1451 3537 :=
  checked _ _ _ _ 55 0x55b77792dcd614ec892d166ba7c7a0a44025ce279ecd119b566edff8d57cef5cdc19ca663172a6e8417d93bc2bc23378200ccdccce5d5e38716c785ea991233810b45e24b2fe29e2436899dd0dbfb1e2e2e5dd3cbdeb31f1c47ee9f4570ffe60dd05fa8cd25abafae0936a288f1022d21c6cb377af2d29c5d346ace2708543e68f10bbd5e87aef916461129efddfc142449d00b0379c6515a879c7f20e0fab57081a99391f7ad0ad109ace1c6cb41cf10f49b8e3ee219ee0ea2fb25bdcc5857189fabb0e36f250853a9dc89263d17eeb8be9968adec500307404946d72371d3059bb0e7735ac8e060994cb663879c36f3664816d06136c4c521fd4751245b7c3514b50f253e5e889a7a5c529750407cda080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_599 : rowClaim true 599 1451 3502 :=
  checked _ _ _ _ 62 0xb23da3dcde444f9bfc184994e60bc1000b716fe9aab5f76864c349d41977f1a9237d9c98da83ab047e0832538f957ce3545e17707f3eb3910c345443f87e7253b172ea6086414c712af0390529e77d9130f8f3b28056932dc509c9f31cf8a60c5bab1c58d33918f8fee9c32c06132feb8b9621fb3318768ebc46efcb470e6ba393e89bd53cbd2e00b3876a8d91e629abd844c4b0b041d6765aa12fa34ae046c59741492787fc2e7845416cb871e6034d85e66e01947856ab90ec7bba084bf1bbefcf2df72e4bb42e0607318285401e00149d2584f2ae1bc29580bdbf568442705409f7b7ea2d327ffc18a53e917a56dee588d4fde24f1d290b5a3a02cd050ec3f1d47e7660fb065624a262bed58c18ecd114a00eacfe7b8aec27d712c26b73c946c45676c8a35ce0a0d482881bcb5b67caad2c9d64973bbf100bd0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_601 : rowClaim true 601 1451 3490 :=
  checked _ _ _ _ 57 0x3a78d111ee421cce61d99f73a85c400697987e1006e3581ad8552d2868520c701440646537990c63e88cbd3700960873c3f2c5a680d17905e3d54532103cc6d1c9180ee46a9a9527554d1ad9a17c2edaa38992cb70ac6e5beac2cb3361e31d28e91eec2be915e958e5384e18886d2644f9fe2249d2042e2252d54ea45343c15bc26bf8e84acba3048e92c883ea85ff4b266a38ef05dd7f69f12155416d43c6d834d1b3e935ba9a79eddfb2af30e0dacadd53ddbb2148a11e5c492a524cf955cdcb3ee6ae9ba0bb344948b539e3d0b82a4459b68345e869bb822b470902197511093d4f7596803788d2b673a85776603ee292534ecb264c9dcabf3ceb373d0ede3ae7161210bb27158a168b71d6d7c90276f82aefc17564f491427852a9cc1137a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_607 : rowClaim true 607 1451 3455 :=
  checked _ _ _ _ 75 0x249ddc4ba74af97a11cae7dc8436e140252509f9a1529bf425a25bfdd1be194a3802adf42106fd512126db20d1792de2ba10ce0a20aa1d5868e34ddea6c8cf7bf06331d30a5417694fa5e517757949c99f8c7c8f946b5180a7146caf5ff62dd80f7ba7fe2de5eb7027629bd401ae62831e6bfc9ebd32bfa065bc797e24a3762d27f68935dd3ca41d47d30e74cb6bbd47086cec5656eca3acd11220a60f10bac9b60e4964dc5d6a7ef455c0cc201dff8fc45704bb6b9ae0f078fe1975fd9bd916a25a8cc041360f63ad66b454658c4e9ff91353a15ff912a285d3bf39b5ca19f5f94e74ef70f1d7e75c4d5010612e825d99532a0a3fe580c32b7f018df9b2d228bed7fe2dc22de89284a52e3da70098612d0db10c5e2091b8c8b7820cf7ba2c5f2d31a02d497593047488b563028506abcb2e47d5721acd9b206344782a447ff8b5f51d8896236d04b0e7f06278f43bbbe849042dc75dc10de891d2ad1ccb579609b049e7445ffac0d1950a9ea71e1fbbb5fd1fac368fc66bee4eccef8186460a1f2d3eb0038 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_613 : rowClaim true 613 1451 3422 :=
  checked _ _ _ _ 43 0xbf8e0748db308ec628a245d36359b4097fdf3b89d2bba8f2ea874fe139ffd76bf79cb3e9e9399ff3f0e2f9cb606f7a3c1051998c113cbaa184d921099a692049a45989558c82eb4f242df1c9ca2564574ec714c689cbadf08b4abb320edf3178f7195399b24090cdbe36d66b93278a6e4dd605c4142f5c1eaedd5efa9f142a6d87b5a1cac0e4317bf26f8becaa49ccdf3b67b2f1f6c7b74d8a0681857c408998ed2430ab017dd11b7d58a2c61d33fd2822edc5352b8bdf42b450cefb1ae5386bfd1b3c53f323b2a3e01de5c9fd64d7b7f31419d9a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_617 : rowClaim true 617 1451 3399 :=
  checked _ _ _ _ 48 0x381c4c1b53207cfbffa5325894faf3f1a59b2283836a0312f9676acadd0c20b1f00cb14582fbf68a96ce0c6f3ba7e207cd5a97fd1c723006511d56ae7c4e71db6dd97d95434e831b50b84b6e9cfc25cfaf9fdcfaa656fe068a6073bc98ee8d51f65fade4b125d900309b07e9d6d930513d292bacbd61a4e18ab60e5ac34a7f2028b3444fdee459b4e9646c8bedcf3c12967c4dcbc4c7342ec4cfed97ad2eec24caac5d564d53c6f38f9e3352b3f77c2fbd88d8e64b4f3f15da5fba8e87d6db682969dcccba5581db2929e39821f5e9bb87f724866d431ce3a87c5a03d2a5f5afd9d7ae9454efaa303767c328543291c4b92502bc6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_619 : rowClaim true 619 1451 3388 :=
  checked _ _ _ _ 70 0x136e4236ecf75d38c65038e0910a3a880e82b8924aa9b99f4a5afe6827ff2f1cb3812e29e88c34ed178e866fdd91d53b9e1ac89ddebb574affd41e136b2646143c95a1c0587837413b263772c270126938c20e7e1eb5f0fdd89c0bc619a84394dc5b5074427ef63dd5688efa9a600a7a381cb749d23518d6fad8b01472fbd7cbeeb1c3723bfbad55d022e28b037c79dfecf729c12c026f09e69002886304e2863ae398875667536bd6dd5ad72f703150fbebdda8a6fbed78766150e262fda0e73a2759bc0c2238f281fd6b2835e512c12e281047fe1df9365b4623e419d4f068a9b64a4372a0aa2c2f656d8320fd99de819789b7ebcd54b42cde3751f6436b7a361eb36091c37b11f053cb273ea7753bc0b5c27c99b5d5f1ad7f36f0accd2b4454aa38e24fdaa36a9e1342298940d1b571b5a16a75e430b141e03e885ca08462bef9d5f0519d544845033dc04b0951348efb8d73d529b819192604689b882816bb50a10e2914d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_631 : rowClaim true 631 1451 3324 :=
  checked _ _ _ _ 67 0x5d1b04b401415509ece835178cf67a09c47e01a36eba8adf6bdcf1b739428cfb360551057282f52251d17bab0d6dc5d2354a64a76f0af7f9e3f3be6507dafe66a4ca86934d3f5d39c4f35aaaa24aad8af3d0bec7bb7b7ef7cd4c7eef7d51825c4417ddcc8bc75332b3f2101d960aabf46a25ebde60cdc3ba495ba4c72cc6c795534ec4229d86f7ad9c1dec741dcbe93b4f3bfa047baed516ecf569cde71c8bbfc2b676c49d363f0c6324772b771430487d1061e55cf6422760a9b9a154545d71918ea9e8f0823f5bd41ca006f1a617f3d179f13d8d9ed3edfbaece914297b61b83396a2a52e5761d38693ced21728ee088a726848d39c91b9d646e33cfe41c9902fd7d7133172f9368360f896dc8c399991b0e661c6c4f27cc5022f26ad7cc537e4e4679131835f813f5dc954de02e159a319bac91bc378ddc49f339e75186fb4d0fc545142a248554968004a2e43e63d678111e9606e52d3eb0038 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_641 : rowClaim true 641 1451 3272 :=
  checked _ _ _ _ 57 0x569a34feb5f02b242739f93e196137a25a5f59cb22b8d54619d09b95a7269c2fa8d343c62e90143466dc346fce1adaf375d4abd39c68542bb21523ee995eb7ec91ee5e2a5bbbe38e2dc4515ef2d8d30b15ad1b04f91ae3717dacf752c98c80078122ce94b2118d9435b0c37b0df12aaf32da071363225ac818b3378007a0696bacb031620d5b3b0301c40ee7d2d6c3fc57594252ce633d5bedd43b9b8f227954ae4c11c53526752f7c7e3597ea301a07413b01e1c7f5ed2ca736d8d43948c8d128313ea2b900d4da177cb3ebff77913988303e47782015f13daed897a2ee1abcc0409c5645d134e5d9b58334b2f0adaaddcc13404a188d40e92903fba9297de86788375377b504bd61fc3c6e9e65326bd7b6f8c8bfa123499d052df9701c26686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_643 : rowClaim true 643 1451 3262 :=
  checked _ _ _ _ 75 0xb0af5cdaf1c3e49917ee79a49dc8c840c97cfe0a39565492c787695a1a570142d3a4355851d270641abb34702b35809b6db97db02a212091e64203b697e7ec07ff014a00088e54c84ec21e34d8c74a29057489dd10a928fd2d32169dccc291ccb49b40d5103b4849cd6103e7be7a770835ac4e25542bbb1c265dba6db4340a276519187dde63105636107fd9322aa33f81150bb301503b5faf242ec86f805dd3512cf44fef2941da3de74c6cfe3303cc6a2e68a5470147ddc902979675b8e143128ca775d68dee49e31b1576d8d31f9025c6757cae1af8a3fd613f559edc6006246f4105e5b85151d7491fd5842dc14c2a701e78ad8a800cbf7c88464be2c7f701f88206504de596ceb0bc254b7c4130e503f27828bbf545d86fb03225e3b4d90a05d8b808d8e90916b137d68f0f8727afa421f934dc16b678dda4fbf5c441f8382881ff4aeb977943dc039091fe5f3c895b4beff9c0fd848754a9a17bb55ed7aa481722c1b55d57a8a160e4a3705bfdbc1e885cff3f4d6acac476ec16ced2abb0090 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_647 : rowClaim true 647 1451 3242 :=
  checked _ _ _ _ 44 0x2611989309c56fc35b6fd4ad0dca71d9e645dcbf7c454c4769aef7b3efe9ed7626deb1a191797f0093c5f866298fae693488f52a5324708c3f142d45d624bd71ed73c4b1cb3718cd0a7da4f06666b53529d4df415b657da149bdb1b318d11a9f89b229d28f3bb27b119a6546741fd92ad989d6f393ae56b6d878c2eeed66f5bd14dcb60b1629c301284503aeb73d27a626a25304d6a93c48f039e5c186f6063b92f714aa32fbb141e97ffe398465e671ec33daa895d23b441efe856f32b8675e14b35df72a3d052c7b050f4c622f822d234d105d40e406a5ec0637a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_653 : rowClaim true 653 1451 3212 :=
  checked _ _ _ _ 62 0x5840e086fbcd93d0670a4cee7561dfc6e9efb86b4d5ca902b794be7979557ce153bb343d0680493043376cf696a13ffd706c1f19646d9bd7c0cd65b2e7822d7bfa628dae9ec1aa48fd6b38761a1cfd05b8db7edfa2373893aeb5920c57d997692dbeaab9d868033004d1314b063a8547f93fa66f0aba03100202c03f1a86d30bed261bf6dd55dd8f7b428a161013f457a867065bf252c22deefbcbbd841256db2ab436547df0fd8d5aab0517d0244c0e15b636d9b45fa1050d821076c9cdf8c20a6398c4f90b399ade886ba458c278169d252ff766cc0796d09cb0308c4952d5830e0010f967f14cc97d911da3fa59ba8e1f495f9ff75866adc43cd96458b8fdff8579546f3f89f11bc58d8ed3bb22d9905e8edfbfe1aca3328209ada324cb3539ecd90d11b5734700d44b0a16f78c0d28f826d6e0e12675760078331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_659 : rowClaim true 659 1451 3183 :=
  checked _ _ _ _ 54 0x5b13662c83870be548ca4078372f9a7558fcff4a3722b03f0921f92ee8c111f59eb1a6bf6af3e5479a08968147995a74e0a0eaf3bcbe33dd55f3f3bf847895f3a49fe3a984a18e5e0ee6ce5e8df8e192c21f18cc97ccdcd97bb23a7a84f81e7e9711b23ba8d1b220d562f1f3b4b2a966b26fd999040eda7c177251ffef955af5331049ecf6a38c475a5f4d96a3b902efa5e72094cc0b7c541f0a9e11b604bafc114df0d967732989d33f3d677385db325110d167e5124324508e086043054feadea7099927eaa9bb32d465da20225a24378d497da60e6b8549c17755e088d28b68cfa5577c06e6f2c54debfc9d29f385eba2f4496da4e2741ad8004815ee70385e809be788c6d10767842b69e6fdc04d7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_661 : rowClaim true 661 1451 3173 :=
  checked _ _ _ _ 59 0xb0a3c85f92b710cedf51de3eb6070263bde699006d18e1fc16a7722da7d1b0cd8708db2d9b8e1c11c0bee599bf4cc4d9d367f8a2eb69e79c8a7e4fcb71c6026462a57c0ffffad38440f626719e052e1388f3cd208331a1c16ceceb4b3a7eb47ef396348f9286b1fc2d1c7bb97524d2d8f80a4376e3a361dfd4a643b408bf21d35f72bd36680aa83710e6f1eebf4aa30af1f3dea0b1b7555ed4c23590e16d2c89a4333489fb9d1602c3fa90abdea19830777971cbbc15daa6d487a60f70ec3dbde01ccc16dccb123f4d9595a6819bd56c8dec9bf71c92672b24935df7ac63d01420fdd5181c3cee57a20bff5499c0f3aceb91d4586066949e7e2e9f5df822786425af135909a3b0039a9e41735b10880f89976f1b859880220994f33518a7436ce997f464f2264a244b04786d657003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_673 : rowClaim true 673 1451 3117 :=
  checked _ _ _ _ 43 0x190cc81be18955091faab20aae1d5f84ad7cb501b8ef5222a0a3aa460249d05267d082b642db152a416540dcf143eac25487d9e5d25738b083e7fbf22f7fbff702542aa03edbd2bfa47daaf9cbbbc4a8ccfe19f86881c493bf5e654d9e3b6020d95c7a547a0f9be3656648eb6dac9c9460af5ba863e25f44f390df758f333d10d18db34e98d432b152c2c7c3d01d9c190b0ee43c3cbc23fb3580831ade24d6f1ef1d69c1d8eaf517ceb79fe12825f87b35d04a3454059dbae98ed8279d062b29decf367ea582e9cf261e1e79149cb8c2ab058ef00e300c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_677 : rowClaim true 677 1451 3098 :=
  checked _ _ _ _ 63 0x2f3be833de2633323b0e2fb72c12b1fe8328c72a529be30a64d11f18eac0008cfdc448be92cceb8d937de18879c36ed9f63ce10b466796f8fa1d1f9f9f05a8afd703c83545ae1a87cccb948d42e05517385e716c8e23e85a5c80e0bca07ccd93b9be776f5f085cd623a9068c50d11df53c1fe369d2bad3d91dcf1b51d09052757a197747658c06b56f78ad2fe53b12f3fe9c1bb3fe960c6710f8bb8881b7b2d17b008186fc781f836c9c5c25e854368609f8e6f3e3e6c539776a513247b49d75934ce86382ae0c50b573ef895ae00d9a2b41a960c5fbd1e6c50079fc975ae78ad9805b342d9181dfabe044050b7b810f60c1929f768f1a910775ca850559bf7331bfbb9e62e5dc8de279f084f1da1b5f8cd7adf1cc9b083187dc0fae1b8c731dd93ea9094ac9c8cbcaef7adada07825f86ccf81f35379969ef5da208cefca8b0259c9937003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_683 : rowClaim true 683 1451 3071 :=
  checked _ _ _ _ 54 0x2719eb4fa2206eee5914f5a857402d13a71f4e5be01f4943e1d21b002ff0a97ab3c9406524c75f1ca1276ff3e250a3fea0c1c29b36d0bd9e38a03a500284e3dc11a7da96d7b8e49589ae0d7ff883829591117df8dfd410341b6007ca0e344d0f8fe657e7e0742d2b74bc4727f28c7e0506447b553524f3dbb32d26614e5967b61476ac12a8610d2405a8822e980421ce54ab7d81fc18c86faefb8d664553b392125c82167068a966e274f6c856e9955a186f805f176b5e841c94f0448662776c8571981481ad3a1e869c820421c3e1d3f42dc90ad2b07244b355f07d83c33e8baa81983500d747ddefaeb269c05033843726fabd16569f60800bad0704f63eb12b43f5d9e768230b2289b8826201fc1010e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_691 : rowClaim true 691 1451 3035 :=
  checked _ _ _ _ 56 0xf416200405c7c867644c19d269d36bcc68d98f55cf5009c36914a7df053122888a3603625ed412c3fcf24dc25724a459889da62ade654394469f2775c2ce548516a128c87f9eb575cee3a2f8e1f61b975e012c0429791dcbde8570b2c639230de50175c87119b780990899a9fe2ad788afca6a6060a863ba61315bb58a42ece9cb097227e5bb21b93666e853b4668fbf506f0486c80befbf642540c994d7d069d8c00b7bb6b947164c2e01e7f963c22b7a39854f1955885269bcf7690454b2072982221f4a00af2edf5e9617edd2a4d1eba0f4e4ae3f24a4acdbc06b31c5c1e327f789d4742c31e5424a6123126362316bd238ddb5ce591d66fa25e99b1bf94afc83d3b263affa01a6a3bee11b50e9ac26bc3e3efdc204eed0dc0d17a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_701 : rowClaim true 701 1451 2992 :=
  checked _ _ _ _ 61 0x4e5c68912119542784cf0a7ed3ab6fdb5d5b8384d49cc5dd8726d5020cfac8581b159d7f4fb30b49d011e7c0f291f9e2e8ec16bd9fcbca592e5c14725b7a172a46c41c38f3a0e758f7da66c8072c93ab8408328cb554b01b1c5943b3a2cf58c96c6a3097bd68f44366ae0cea793ce03a50a955156cfda7c8755f352cf278a383e1143a7fa38540ef83de2a730fd3611924c4e47c858e9b8fc6022a742a80ed2d7a5d182761bbaf84068b0e0352ad8f0c56a6ec95592c70724b2327aa09efd689c0431080d934d84afb4ceeb592d6f6497c932094ad843b62dced56d85c3ea8881e26417f45cef3a600d67e42a2eaa9c1d3942bd91cdfc1f23932e7d497a3717b6d749a9e5cbabd724fca7af3644e2893d9614249190677e1453017d53e668bd25a742ba817b3047f97c23334620ba81e75d949c0c67a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_709 : rowClaim true 709 1451 2958 :=
  checked _ _ _ _ 45 0x87ff052eb1a87eb7e901b5dcfafc2dc644a9a2fbc4c2b172ac74be1ef1a5cbb7be9b91ef4c8c1a62f209452da54e32de8bc0e35f7727ea46a3648cee90b76434dc30927904bf07f2160ab08666dbe1f26d0eda31d3773fe9da48deaacf0694a15c2a9164d7d4ca2b9f99fd41956a292512c1229ee5aa4f690cbfa4cf12e40b723626d69372ef6337fca16d8cb7f3e770b6f8e57852fe50aff28c9d54718a04affb37b1d366d6cd85c481fd14eac37b18dfd4f5137744af60e645db110b2aaecf1735925e3603082c55df495c830c41f26ea0837e6163f1dc88b3b6def20472af1d301f8968a3001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_719 : rowClaim true 719 1451 2917 :=
  checked _ _ _ _ 44 0x8f4395842620de58d0f0c4bc0de962cc7fbbbe8c139eb8626485a7cdb26d3673174dbcde4c631db8df61e4bb7d4c4352185f6427202b58fd81d5fb350b707c7e6ca4e44628290a490548e231fdbc201042a6f3d8d063f73346c20289218dd387c645b2cae8025e7f629aa3dfbea53a5ed6d35f4cb9b06b20dea32a3263a9a2ca73b7e7167b1fdc4749367db842ea5871deb87c894f6965931ff5e4a02a6e98aeae795670f2ddb114689b27f5da8da7eba31daa600de7bd31ab4cd6ee299b75aec7e712a6d2c2ff20739eac1179e224c833d3d426829d7d00f8c16f3006c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_727 : rowClaim true 727 1451 2885 :=
  checked _ _ _ _ 44 0x18850a09be4b1ab322ab9695b556929b744e191157f855f175787b3bd1005d5f45149e358f3571a027018a46674dae69fb99adcc5fcafdfc245d6ac252aa3f85c0adce3355b313dba291b064dc09fe12dda7bb29016ae33bc1d51718f1442682f4d3f44f89d51fd983e6a2a5d4fef9b5c2aec22f7809a72745b08bf9e510a5f9ee8b142099bb50e6748d93dd446653d6da297cb8f6cc72bce7ce936fd7874df47fb06c60f8fe9ebc38459f55342f0a7d8bfaf4b2bca9f73e2300e160ed91cc4f8fdc7420b56f20a588015dc21edbcf3d12b319b78b44de660e9086296dff50046 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_733 : rowClaim true 733 1451 2862 :=
  checked _ _ _ _ 39 0x13f6a75e61e182fb024562ebfe1458223987215c5a453a8e8d8b3959c302d0b0144d70d48421cae75d37017c38ad82603b8e84b62292dfb3c65f45181dfe998ec53869a25c6f93a4920c152d7a87282d9e3c8b1fca7fce51e3a145cdfc26ebdd5daaeeac9db2caf8837bf17ae02b7243acc8b5140a65ef666dac1346d557a7352a83aa83c5f70f401b92ef5aed18f69d99308d3740bc5896505a046f4c306a538fa2a8503c1b48738e735052ead1e525e1e288a5c9fd64d7b7f31419d9a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_739 : rowClaim true 739 1451 2838 :=
  checked _ _ _ _ 48 0x1270da52acf98600432a873a131000873ee0e4fbef53cc955a5db1afa93b9c1fc520bdb04fbd187dbac704f3a4d0cb6a4ba67b34f028538eb53b3d25cc96c462492a1adce8b70ea86798de02a1db66ce8c3a9345ae440037dc6731ea918f30392a8975c43ef3974c7979d257c39b260ffcc2747b13008010c5df961f244dcbc39b3c3c708a0cb2c7c523ae29cda08543935845036406cb4aea559d6d06dd387f5ad4d032afc6f75a34ba2d178f4046893181d5e08334cabf05006063fe7288af92cbf13d02119171427323f87df1ab59f7d5a78f195a4ac68992fb94bc30f677e52022e53aaf038b884358c3bbf5e04efd54d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_743 : rowClaim true 743 1451 2823 :=
  checked _ _ _ _ 53 0x480d6a00c4d98ac8ec3839632ee6b961eb9b5eaa59d26e665676172660af612eba04f9f3a93f83679ca105c146a94b8730426a5ccd677193e744c71e7d4ab1744913fb48790d5841057bc24840b94bdca38432dd669a57448906c75895a202787cb3b4ba1226da5e18d03b85b9202f76473b2e061895f03d6048e414df0af24c86d5141c9d60a702e63a0c55dc5071e241ac94d4e12efcc56580108c8b9981740a77d5de52bd2f5c62f326ee19b2862d4b16ae1fd6f5558ae11c544e83500f5c482298e82e2e971ae3fd6f49003b6c0a13a858a6cbf9812b2803b7f1970dfdd4cf0dcd9ba90ac2ef50949934ae65ee3177b1e42b9f000674591e40c276ea2a07b03712c39f513b1c41cf00540a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_751 : rowClaim true 751 1451 2793 :=
  checked _ _ _ _ 50 0x14e431cac63f4070565da56926e0ea636784fa9c401ed7d57e223c2812f068ef635794483b35fe2ff315ef10f28219cc9d5cc7a4f300e30cfb46d1ecb757191392049e12246b2b3a3e46053d5fa32323af87c9a2140b98742ca5a4f4f5c86e0cda9296ee249aa6f1f7e7f1c6ef4c305ac3f2ac8b1eb278fb3555304509665447c48c458e4c484f77976fa1742b79052a731bae03c644f92fa26c09578453fefb32e204b858b2002b69089722e926904442660498b704750d60fdfc96708dcf335d20de6f4060f500f6316e14de2b0ddec20616dbf9ec421a3bb802380d55fba299ff93860f608da5c2306b7b68b24e3b1031b9a0dfd9aa01a0edc932c7f260063 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_757 : rowClaim true 757 1451 2771 :=
  checked _ _ _ _ 41 0x820e1b584bd690328a10a05674447e2f0ebd711b3ccf6d38277e8870ad2c22ae93562805d9635ca1acad5505b1a55499d99225fd10e835d8817df9750b0c350c76b8de65a42825649c847b417b92c1365116a5009b14fd58ed9d185718689f1331bf95c1d444db7ece5535f880c107548a377a8c6144a8c11eafb8d5efc891ec05ed78936e6db9c41f93dd1e2626e4c114a24f398d6245c7ea54a7616fee111b9fabe4d5d922fca2354fc41bdcf7ef4fe266a6b29c0a6867a4cd10e81c8907544eedc2d9ca05e96a0ddc06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_761 : rowClaim true 761 1451 2756 :=
  checked _ _ _ _ 55 0x5665efc12521a0462db108da243824cd6d980fdf5ee07b158fa8693eccffe0befe283b64f525c28632628b6c3e11803e0f52ff0efb1959830ecfa77edc4de54ab9cf7bf991af53b5a6644a927d49fabac4c01fc22589a15c91a840488aeb21e2039a57bfe31cd273942330c1588746b12f41a46bfade795fc072e236227aafb3b6e4e33caea1083b9f0ac16e89e1ea334b1dee5d862d3e8b255be641a4c4cbd43076c5a93f1336259e455d36e98713e937837f5a605733b7b6a6d45487ca545cc8c451478ca5aa945f24844257dafac4ed045687d7d91373c44fc9e67012991738852b29954bcd177c0b4409fcfb03d9c5b9703b6fcd829599ba3848f73311a1b4b69266d92e7410f58356d93cdf94d87e8eed03846686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_769 : rowClaim true 769 1451 2728 :=
  checked _ _ _ _ 27 0x3d3577dc2b8ad1c7d1cbea073ca99f811c31241fbb4f12f981022d9ad0082e2f0b8261d4be707f2bd69e191d24998b3d56637e750ff32a6d4d659e10aa9abeeb5405f850fe01a2f397cea1c78b2bf67c2e737c3fa99b4fef834717d0690fc448635c3ad6a38ff26928eca1aaa30b308d17f4bf75031d41ea856a0706d8226ea0ddc06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_773 : rowClaim true 773 1451 2714 :=
  checked _ _ _ _ 51 0x1a220dba0215d2af6580422bbed134764ea717f09e1ab6c81f1ea8425c321b518cf750af2277126efa11cfa1476f45182fa69095900ba757559ecc32ec34c7e721b447c41409245ba8e6453ed7ed1b1fa39f34a66cb176af074342f76d28b2de5348b97e11edbc704db83673086c3975a3585f74fb0d5b75aecd18beea8e76e45382e956855243773a47765617d5d9babfa38d42d2b0981406c95522de4f10177d8b8736e25d2b7e682fa41da0d78234542dbc0542dfb10ba8b64d238be2a3f2d944d48b0235b1c6c29d57d3ec55d4d0a2595f43bd19bf52c778b342f7b8f278f2e75e4778fe827f5b1ef07a8bf818f0547cd23db5d6347067b01989b03100b4a68bf0024 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_787 : rowClaim true 787 1451 2665 :=
  checked _ _ _ _ 55 0x45a812aec1b8dea14da34c95036838eb114dae058d79d241f090fbd1b58295b4882ed9ab8c087ab870d25e4a10e337d65c6d76d27b7a92bfdd60a7afb33a7e8508544adfc8089d371e2fb7094b1294af2948dd087ffc6f8eb4786688cd33c0f444d745bbc4599fe4f0f982fd1581bf1d77abcd5cbbe16fca8bcd6b19ba0e254a079131f953f3d993989ae6fc9b7925b97e50c4d463366692d67519094673ecfd82b6b8e3d4f39752397c064b06c4f2602b62a8507c14cb3ed74de451a6fd6f9868bd4ec158a2592886e3d31ae3f246a04aac3e34f7e564359205f3e591f347a8a0446c9ed560ddcf701bb9a69438c7fc1aa96e510c9d7675b428a733569ce17abe9a37c495e8a7c282e953dc5317a65ee1743032bea9df0024 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_797 : rowClaim true 797 1451 2632 :=
  checked _ _ _ _ 51 0x95635ba0ec0ba3aa0c5c6ca55e0d60eb9a1a79722e6fcf9372ab8c29c9d3205802c159c191ef32bff28c1fb221da75ed4e84aa3dd8aab0f819405f74c7f2f10d852a4a73b35079c846850c6631d9846a0478fbdbce67156b6d8daa3cf212a2dbad8dfa6e67ef7d21a51f547d1af9f62ff88a8558ffa609d1558fca3c24bfa0022de02048050fca528e9da968c09ad490cbb2f824d702da01174979e316e36e2fdad74d7db5e71d15139770c4a08ba97163040c632896caefffd568bda064e70bc59db64c0084aab11a338a0c593652c85a1c4ef24dee9c68ec8a859a54201988adc9fa06e340ad9643f9c79bb8a863f54cfa4032324be8c8f1a84c1e107ae0360331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_809 : rowClaim true 809 1451 2593 :=
  checked _ _ _ _ 35 0x3f02a0837dd3ebc71ac19db25c5ac23aa809a7e150ca636974a8e32977749fc90076897481da6296fe504727b15fed7ea263194c1c8c82bd167b7268fddf1c4012f128ced1762e69af4f43e9b5cfb9352a5a8412b91b5af6ea679b7b2c38738fcb1a4aabccf690621fc7e36ddaa9f5e97e66385d8fdfeeb065b6ec088b57eada90655cb3f76d6eaface9cbd837eb97e6b1aa7423867640a9df40778f11b83c9a33b254084f99a6e89064dabb2d02bc6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_811 : rowClaim true 811 1451 2586 :=
  checked _ _ _ _ 40 0x217b0f094dc4e96fabd9d09d7193e30720a6de6154793d96c9fc1546ec43935015e0422c1581bb8fd2441d7713aaf1ff3c0356d61f166b81279613c6419f731b52814518ab9688d603f625a848feeb60d9bf89aa4b3a60068d05dc89f84edc9c499154eb861b93178f8d1c74791c31f5c73d090dd1f75e11c80aba4b82b841a04296d1a7b48c04d3c3cec13642564b54ad6f9529ac8fdcd603fab4cf50dcfa8e5a10b4e6eb1c60fe469a9f3864c69cc95a0dca06013020eda690e5921b703cc830b8d6cbc09a7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_821 : rowClaim true 821 1451 2555 :=
  checked _ _ _ _ 50 0x2a122f2a1130980701290657f636898a31a768f3c43e231dfe890b7bd465ff8c90b7b78b8574264a64556d91eb62886428276b77c9f5e3117bfa767dc484113bd0d7d04ec3fef5e37b9f94519837dadc8e880d053009a1eebeba4788b74b16d93a7de55de4445203310cea08ff23d7273f7ddcf65c21c9f998066cbcc0a37f61e9879630df4970a25d1a127dfe5c9017562d281581487afa3840956429e6d86307ca05b0d477cd9b17946849a2c682dbcb792d8ea92c38753652eedf7139cfbf739cd521ab59c4a575ec05f75780eb00a73d7c08a6cd0d4e8c2716bc9b016df89edb8322a78d64acb1f8d387d8a3613a8c153185b0ed8c7c640f7fa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_823 : rowClaim true 823 1451 2549 :=
  checked _ _ _ _ 42 0x4c75599ffd14c22e941c355c0569a97b50a510bd784497244b265f25df1cd446efa625b24931a7d9e8a384b4b997dca21e9f23710e3ea4745ea951707dfafc0ad09bb996b8f31c85dcb9e89798edf023acd84e43ba0a182997cbe4e0462421f0f78cecdbfbaa54e337df79983442891793fa3bd66d79905386087ee863ec3841b9be9356b72abf9becdf740d11874c67f2ce4239ef5dbd55de7f202ab3886751448054cb1073beee89abfb5fee14a3b0d781b1dcbda7fafd6783e89d25bc1a1e8cc2761887e30c5461b5b394b24694813cba707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_827 : rowClaim true 827 1451 2536 :=
  checked _ _ _ _ 42 0xade7abcdd3fd37a440455164a4f30204af71398a1d09019553dadf3708ce6d208391c048030ab6589b142c75c728636d6ff8fa22361f93616640f2ca2058c7661717f60e6c840c93b4615cc37c4fccf68ae6b73c855e3a6d5c5801673cc839b38bd021305fc1343adf8605cecfa37251daced012fc8b9a310ab4769da9d2142a76620439fee2c7315a7541ab3506fb582d06040762062b045a18ff36777c634ea3d12e8c65fd30d9cfca69638248987f4f6c2200247100f3dbcf453675d16e10214070a3a84f6c1df3cfd300bec41cf00540a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_829 : rowClaim true 829 1451 2530 :=
  checked _ _ _ _ 44 0x9e9ff71f566fdf491d2803f63f963270eb592bc09f6601dcc5de98c0acaabca647718e2a0d508b52f1687297b9271adc307d244dd90377af1a59826483a523a93393bf1ecf200a09324b8c8afc80a5f6395ba68e0072e23e004e439b02dab4e31da8394c136df909760b96ca81117fe1ca8bf0b8b0baee2aecab5764761378e86613d6122cccf620ba7fdd03b925a65baf8b7fd3b8489bf68fe24d6e6fa9eca0a31dc803e6326c2bbd5ff4da2bbdef5cc5ad20b806e13c431dea5e75e4b3a08325fda6ed39a835c261b1843a4996fe495a4069c3c505b9597ebf059e42c1300cc (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_839 : rowClaim true 839 1451 2500 :=
  checked _ _ _ _ 36 0x5eb1344d1539438dfeab3728b86f96623bd8595a31dea4eae9fa4d07793f957ee6ac46447e2d9b946890485f20bef23c7bb7486e0a18c514a2fa15fa5c4fe13d7d4c0d528e3d96426a297989298b4627955a4b6e788d57dfac34ba605e584840aa71272f3662f021af8a1144e7a3947a9b4612b767293210881075e9eacd2907fe6e56d61319f4769e59cd4d1673b6a9d264aee5ca3b499e84a17285611db6864fcb7f66f7298c98d1c94b95bbb43b784b5500690a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_853 : rowClaim true 853 1451 2459 :=
  checked _ _ _ _ 28 0x411208187731b1810416d37cbced443c569c54f7df2f7ad005bfaa0a625832ab219c7ffb5e240c0d37b050a87f80ab619750490ed5ef1e268b3eba11e07dcc7dea2954c773c89317739143cfdcd66b54417c3add274fe8819f72ecf8250d318ddcab1db5f7c271a9ab7aa2d9797f741fb26556336c530fcfe292a6b94e8cdf8be182ed1c304814cdf5870042 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_857 : rowClaim true 857 1451 2448 :=
  checked _ _ _ _ 38 0x458ac6ee7c5ae7150b6fdbb3f4cb2854e56623652572a3e5795ba8dc4a6cb50e13181c1d2afed4e93eb41fee56aba11a54952bf41efc5da5c41b913264e933fe9d012e335e1dd7c8452ce24e06912013ff86d5dbb38dd46d81287e13bc85eb5bd619f9bdfb39ec5aaefe2e96605c2fd3fb175b90c76f99f9d56f70d8d30a4e072370ed0921fd5893a8c6f881ccf93f3b6d484f320079317094659ca3235b68540cdb95e19d829a51e6d871b749b2e96be778257fc9d83744aa2a0007c3a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_859 : rowClaim true 859 1451 2442 :=
  checked _ _ _ _ 53 0xbb3abf636fd2d7912411b97578de95502905cfc6369f37624c5490c6b9be4a3677207a7c7ad69026f4c31e2596cd4ec6a3101cc238597d12d401f04633cbbf745efe75ef2803047181950beaec7a1af763977b8fde5ae5e60d364f6cb2a711be40db8f3831013f00f97c1986aee19b55bb9c68e6bfab99f575a60a1c17332ff3bf1111db6eca57bd5d8f64fd2d747cb970deba217a54d3211e8230511c3c42919e78b778de1fa7612e96118107f70b0d71814fd533bd94afcf4a7f508de3d522d8f5ca33391f9da3a44a0357f010153fcf2ff7c82ed9afa3821492567baeced07b2143ea31e159e2e0f9924f234a14b3b7eb2a0acbcd780db6313edaf2abd0f4790c90250054f183e7990993bd473001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_863 : rowClaim true 863 1451 2431 :=
  checked _ _ _ _ 39 0x99495d41eba3e400e875718b8b68f699cdc38868af96f7328ac0610e6df09d218bd57c2ff1ee1569b8b53663b8592cdfff89385946f87001df19e642c3fd8a6080b2cb52c5a2cd3f962781b516eb56e41a55ad01d42aee57110132c4c7a961c80bd58f5d3a839a2aa89102e4296b016f4f79a7a09375257f92c794173c9e46570afc5337db9680708aaa7a5545f84d2ae29385927cb9c0643b085e1e1aaf887513ec7a5cbe2c1c419bbbed8ceabfd656c663868265307e53f7a9d7d00f8c16f3006c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_877 : rowClaim true 877 1451 2392 :=
  checked _ _ _ _ 38 0x72bb59808a2a48868d394abb0a84ffb1c8568a3eb3f2af32eb71d032d9a757131f98d013215e660acbba8352210542f21f8957b236de0e4ad8fbf4fa5d401b2b1de1ca2f5cab066482c70cf7a59296eff19ade80e2a794f92c8b4de0c6b293ade30efb4373141d78bd96ab3830e9f81ff971e978e037731cd6ebff6d4283c6d992c0f468bee2527e546aa59f266061ca5e099b0d3989cd6b5dd9c5f1ca754bdfbfc8ab2cdaade2f0628f80bb826eac3147eec7b6474a5363a18b594060ba707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_881 : rowClaim true 881 1451 2381 :=
  checked _ _ _ _ 41 0x112e7c714094ef5054886dce58a0dd3591166bf8677f293a6504305606d45ea369adeff0c14e8ec7d97f6a4aeebbb93408ac17fe94e67bd95473a92e6eb24d08d408770df69e6f297b80a68643b4bc49d0cd6603a41863b94bba50427cb3d8eef30d70a3f7babb4a1257baf753cc6eb9bf10226b1d22df39faa8542e8baf159d24221a88f6fa414267bd763be134431464a0ac9131b076b2e360d7bc965478cf4a918cc674d337e3f819d4eb6f2f5cade7f992d934fa60fe1dd3c46bd094b11b407ab2775f6a0279f83a101186686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_883 : rowClaim true 883 1451 2376 :=
  checked _ _ _ _ 53 0x2e0414b57872e589081e43c1baaa59bb394c9f9257a83304185c833f08a1e42f2ac6818c97eed3d304f7df047fcfbb93c8f9ff065ab8109f6daf387a98b6e4bf0136b1cc23192e93adc91acbd143b632637190ad08618a3bc05517b8b422e9583da69339a325141649514820b2c0f2c625a2792d07960a8c66a301de2e24c4d25296961b4ee30542520b38bb353d5e30578d10d19abba076d1c58f450a39e77f0e711fd6e87fd02b821db7265428b3dad9292a443279744b0f7a85438268c360a4a88c45bdf9bae72f12cfc128f054f71ff460a2ea4eafa68957c8bf9a2373e10bc865177c83ba145fed173657ab65906f994ad939491ff0d7a82afd8e37418936c8ad1347c97eeea234365c7f260063 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_887 : rowClaim true 887 1451 2365 :=
  checked _ _ _ _ 34 0x27bdcc26066377bc53a212d02159689a4ec8c29bf932a804e6e5b8c4ae04114f616db14f301239da9b25703e9e0e2e2f06048ec2ad4534257a2f0c8b1ca2fd015c054b61acfd29ccd06e24350f9494dcce966e0a49ee4865c690c514b754fb48a494cbe91c93cfdd4a9323faa098dc677def1c72207a46cc29617e410ec5ea317c976dc070db00fe54f42be2782a50cf2fa59725cfd406531f7abb62b86baae0cb6917e4e8c1c0c67a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_907 : rowClaim true 907 1451 2313 :=
  checked _ _ _ _ 39 0x1e869de1582c8eb8336c4526609363d91c0cf841c016779fe809d6777783143b9518a279626aaa03f06e4e0355d04b3c69671ef30f202b9c02e3cc8ea421389f759cf43323b238ea0741ee77a7b44a11db30df3a8c7e525121c9b718ad15cf1f2eb9cffbf696ec9676f48901d46aa42d7251641c3efb902676a4aa6fa315afa20a328989e4e08e22350f5643d9859cd0bdd72393e0e3ea287d31a768fe42281e6058215953deb88c3a9cf2591b02044795344d2e109696e41a73a530e4c0be860656914d30048 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_911 : rowClaim true 911 1451 2303 :=
  checked _ _ _ _ 36 0x2254b20690056f9977aaea426268bdc34ea96dc5db503c1358a663483ac0f14db84a5acaf3d8360d77699cd612cf6dfa8ed42c75aad6b521d992dae470fe0f4cc7f1116dd0987d05aee4630915ae66f1c40bf98eb6cf1d1cae9662479e2a7d12a7b90099ef3428ae14e35476c6732c41f98e5589b60c6c111463c15e7d20b8fc57f1a13bb7fb8878b4ae02a6dafeedade04848da751aeb105e8d2238962bad7f8aa27fbdc46086f6c0767842b69e6fdc04d7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_919 : rowClaim true 919 1451 2282 :=
  checked _ _ _ _ 32 0xdc8864ee48def51c777e969520bcd0ce148f616730b6e9cdd78e957bc1c94b94fb171310307e34c3f5083043b8127c15266efb1f3b3599cd4a1669ca7932a5283f2378c41753740aab2aafbfd4de65fe920f1e1058d45693be11c99ff02323bc559d88678844aeeace57a8c7ce39792679b6030a53777e249bf307b9cda0980f908c871c9c37133865f3046331b4b7c8cfd0218a9cd525ebb437034c88777002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_929 : rowClaim true 929 1451 2258 :=
  checked _ _ _ _ 36 0x4168d573cae1314111efa7ed1652d774f466b8474b683d55803d4dac21fdcdf99b92c4d68e938feb45dd8144b756464e25329242e9555d690cb430e6fe9f3afca94b9f34e59b025045e5974bc727be1898db82ab0b38a5ff5b1d9eb2bb5093711d12086504eab3eb73ff3727c6e64c34fa0540c3d9950edb80ace1bc2f0d8801392aa27760a18834d636075d121ab3fe7fd23766d3bf3e604654c7e0fb14a6fef129d9fd3bdfd936209b32075471a72d9a98d900c86686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_937 : rowClaim true 937 1451 2239 :=
  checked _ _ _ _ 31 0x1ad821c65526af2273878edb87a2ec22cb79ed73c1393527c588f834688966b4ad1edf22e59fa0fa682e2dc33088dbde495063b2d2de8faf8bcbdd2b2705d73adc2f360a65b4228c37d2d4223319c80422f8d4809b80151b57e274e3c92698b0dbf7931305906a16e67f6c3ade69e3c043074e206865291c8d5fdba81276442613742d99208dba5332c6abe917e9857a272bd145c2b020d6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_941 : rowClaim true 941 1451 2229 :=
  checked _ _ _ _ 44 0x4056a27dd04d5f95d976ab502a234c9552bb03cea02aadb10b3b433c0b6c49c453ba5cd0b3fa08c309244d717571493a8f6e219fb1c3a3c83a9b30696c896a696c5c254904ef54d6f19fe435d3797f57f752b22b8dc21c5e858584e84eaec2a8dc747c82e4806179f652a5d958ffa4a9d226f18a1418e9e0fac86b179fa7505f3869c6a517f90dd6762067bc50c927268c076c5be496cc66358fe73db0f83874fe58307fea23cdc263f1f5f7474dde4abd79096f3606231bbef7369493d33b9149a7f3a0f0e7d41e06942cfb00b7259d9fc2a22e483a66107ae0360331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_947 : rowClaim true 947 1451 2215 :=
  checked _ _ _ _ 34 0x3752219acd0ce64fe970d9e3e92515271be260eda532d9fd1eaa99fe58038eedd4ecc6698d2227e6fd0c090dacb00669d5d018ea8812057d9c619a83f9419738091d14f6a6b109f74cdbeaa0df2897ea13c7a1f171e26d23b56aba5b89b9292878f2505e49af3ca95704759a288e3a70e21d26d67acaf890372397baa7c2e94a97306346f88db48b24a1d7168a6a8cdcf21f33d3e574c1bd69b142ff7668247c07cf7c80ab601b30a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_953 : rowClaim true 953 1451 2201 :=
  checked _ _ _ _ 39 0x40403d60c44589ce65fa792c7446536b8bc828ae126db8de2ea230711736d6da433c6684a521d05fa6e8018c3dacbc77bc26be2f75ffccab6c74ff9afbab14eacfc08367e4bb335024bf9ec6331579fc4dc353abb399525ee5696f6e349c7b028ce023b695ef32a1f090dd77f5a25581709b8ff7389d19c8db2f8e07ae48aa9cf9d724ad68efa6f33db981cd5f9e528a567a8d8ec4595e0239db92669bbf51b4ae49da720adcfb89f5a83ff1f36a4d16b087524b835c927854d9e9750407cda080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_967 : rowClaim true 967 1451 2169 :=
  checked _ _ _ _ 37 0x89c1e657269d8a9543a5760cfa52655a1f54465dbad12853bd89fe40214df49ca44565291e2628c762e93be17f7368b290409cf56c2d7fd454fb2787d4f40ec9e40e25ca86bcf397e626c457d7f6190e7d86f28b1e32f76669c654814907507c07d0e57732752e5d3bcd8e1cd1e185cd9be8f8d62f8ca2102f2beb6361209c28fed87a180dd43e9145afe4effde4e8e9c3cb2ff3ba5a06e378d3acb80a2ba9de9edf4dab437799d72b110830485d02af8c669e373c041bdfa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_971 : rowClaim true 971 1451 2160 :=
  checked _ _ _ _ 39 0x18bc4ecfc59212748d19fb7e9b225e6636bb8ee01e090c1dc9561b279e137910427adb3febe9060ae280253d8acfe599208b810b60285ecb089e22c89c936cf8c33ebf0996955c73cf75c82b710e4086d0e60b167db5f4787a141170ba1ebd6323e1a7ff1554c4947e06d1e8f05786e31ee1a6890e7e5d78f219c9c91e36808ff802e8223a76fa9fe34dccf32fddedf3f7b1bad398fbe6473fb2fc13caafed2c802ce46df6fa5a6ad2ade018abdb0be77f94d617e95c0a58198d7862057a8102b20a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_977 : rowClaim true 977 1451 2147 :=
  checked _ _ _ _ 29 0x50c6e33bdfda2efce13d2fe4edccb47a49f14c29eb56ca1e052a1613694eb2919cde9b53c84d4a69cd98b053fdb7d00ab7b901242aa67a2b30e5c6ac9bb1c71ece1e79ab3899e6dc2ff1ed067d09ffcd992206dd9e5bc5de2e41ce39f53ae46d29a3bc61bb11d1471915df9914293046ab804b4cf457bc94796254bfbddf6275d575c5045bfe76163ba9f3c8cf7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_983 : rowClaim true 983 1451 2134 :=
  checked _ _ _ _ 34 0x19a646a86cb254c481dac98dd0486e1d84ca1510e7be6a7f5518a4a233f8712664ba37fc5b4238902c352e7312fd034bf19be9f1cfb61a41019789e228b15ed1f927fac8f7d64aaf2d048e277a2f8bc156d7cf70b86d67095f225e1ca760789a3ce30f1acb823862675367956b0c6143e49eb4378a1b478f7fa3136a4d1aec45c2b9950dc071033f4acf75d68c11cf3a784a171457fbe8af7ce910996be18807ad8482bd175007e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_991 : rowClaim true 991 1451 2117 :=
  checked _ _ _ _ 35 0xdeb9405f788256085ce05456cb16811853559ceffffd1d9066467617cea1833fe49cf94588502f780bf721394d0757a786b45969d060f59fb02acd49d8cc651b3a52bb8c9a254badcd1b4169afabd351fcc951112b8d7dce8c84adfeec9643e53173e645615cb07bfe498932cd693fba954b4d49b0ff2881243c03913370696673fd5f2a51ade0f40a1b2b06ab7fe8d1389995c242c4c5619055184b771d635d547fa5025295480f84de0b2cfd6030058 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_997 : rowClaim true 997 1451 2104 :=
  checked _ _ _ _ 27 0xbf4f7122e2726ff40e277f6e32f57e4311f3ba126d5135f5795ed802955513c2db7b94265158e16505fddc49438f9a099e1d8340a29cea127ef5af39195a2a09b94650df5caae41c3b647bb5bb8a6392cefe1062740e8ac77a5e762c66540bf6bea1ff742c64933a770144b7ae4f1a5655aefc17499f743227392ea080f86a0ddc06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1009 : rowClaim true 1009 1451 2079 :=
  checked _ _ _ _ 23 0x2f63f90ef5dde34b78e6dc1240aeabc8fa5deb6ba6385d2feabd53191a6ecdbc8a2dcfea69469fc766d6da28d9f4532dd079a994735d263d73e9c8460c97feab04c80cf9d7f352816fe0e2f3f0cda623af3819d374d3bcd66218dec02b4bf75031d41ea856a0706d8226ea0ddc06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1013 : rowClaim true 1013 1451 2071 :=
  checked _ _ _ _ 39 0x391079f8bd9f685251d86adca379c63093f73d95424c1015447eb30570f2cce9e24aaa366b6f93782f303779e5a94ffbe38fcdeee2d923e412f963cf08bcb1df4607c0440f01bd54252e0abd0422294efeacbf6ced5ac87e2ac67f866d9b0c2e08ed5ad2f0e5dea4e7175e99907164d1ccd50e2c5d3ea6f884adff98c1d32582851b2893f2187ce25a5887436a1a2bb60e645bc6dad2aed36afc369aea3fd9a2ae0fcce7ebae081a3eee96608c887d2d3bf602302a51bf2e413386b0c5669b1d01a935c5b0054 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1019 : rowClaim true 1019 1451 2059 :=
  checked _ _ _ _ 29 0x8e578b739e8d66c55d7da3b04c96dab198661b1c6c095234680490678d8bf7c53cdbd6358f1f7ccfe8fbef1a30faa6f222e05f804664e7561665316bc0a9f01fa9b821edd92bcbadced67a53076139f0c933c20f5fdd3c5452a7c212a77f81463f45eadef0e286e1b5dfec6d46bff5d293049c8c3e2765e2c33a459679cb462f4a75f39accb553a891d59ef5fc1fa7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1021 : rowClaim true 1021 1451 2055 :=
  checked _ _ _ _ 35 0x14215868118a923896097e0f84da8e9ddaca5eb93a417a1fb8769d9ee5405e502eed0224ed60d831b9ba0f9a646f5f8a5e9d5880df0aa408d90eeef54c6ca94b92fb32460a6b5d7cf7a58695acd0068c04e079214225e099fda1ff5e3842d0c65cc81d5c82dfc1d67e38676c602d8aaaa540aaa6dc623c339194c699a2cf9701b673578cd108e9b8550f2f43624103ecdfe9ebef7b0b8fae4d9381cb55a1f052c4fb65a2ce6ef79bdc84694813cba707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1031 : rowClaim true 1031 1451 2035 :=
  checked _ _ _ _ 29 0x3317b6f7a73ee6829523e505b9e9870571a2dd56eec902256aa7f7976a5dd894df35f6f392d0b0e753796bbed0e391e5f54e32596fa84cfeb5f1bffedf257b94f1481e2322e0b0851fe8f77b58bc63571f09df6776bfbc94f4ab141f8b345ccc9a04be5ec7e7152c614bd2c4243ce8f836f8301830571b69ca7b7c03195223f4969caf0d57dcb98673aab71c06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1033 : rowClaim true 1033 1451 2031 :=
  checked _ _ _ _ 20 0xc15a7e60befab964bc594b91c14fa465c9408992c7ceb1de73a84e420fcbb65ba80eeab1a2ca012948c6ce443318f0beee2ed59f140bc83c9c0ed8b178190f4a289a73b882d31a3712b9d75cb21f3129a291bc98d177a9750407cda080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1039 : rowClaim true 1039 1451 2019 :=
  checked _ _ _ _ 35 0x5b86296060bf5fbd2d00d5a9df5b8f1f484aa15d3bff523b573b19ac3108f55e4c446ef065c5f4d79fb3095e877e8bb222c53aa502fd7c1f16e2b429fdf0650c793a1cf00280388eef9b12a4d71cfb11c76815841d3ace081daa26f052aa02ea325e05390c2fe10c1f112f827859633997799dc417d0afd29c9d416c6862eb151844a01d599b32975af229e7895d68873f13b52c5c441737fb99de1d7f7900da04843fbd8b702efaf4ff9c8dc64c2c3c50023 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1049 : rowClaim true 1049 1451 2000 :=
  checked _ _ _ _ 19 0xc30b93c2f0a6ff1de0f3d845d9b14e4855610b8c784a66c2f34a146f444ebd6e8fec4186a95587dcdf3f929603df714b82677d73ed6d92f1ed42fa7331ad712325639bb486977cecef50f83485ea27d653b36585a6c443cbb00966686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1051 : rowClaim true 1051 1451 1996 :=
  checked _ _ _ _ 33 0x1bccc0c0d0d50729bdd1c3fc88bf0253a0adfd24f4c46114b60d1983ed2ec082304b4f6a2ac0ca9e62a576dad28da40d5cdd192a39b0e694e317d6d237fc1ea310be5e257fd49c98a0dba61b22f0e68b1fa9d77697d85dc52806ae2810560c0b9a2a2916e99ebcdff0e6acc154256e79755e3fc7854522eecd252edf23d85c3fff7c90e0ab5ed983d0a3510f2b9acee82f07415b62393e0c4edea75e9932170b17083288777002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1061 : rowClaim true 1061 1451 1977 :=
  checked _ _ _ _ 31 0x13f90bc8ad4e49d0e40063a8fecfce556046ecb34b27a8032c94414deb50a7e1f9ffc1444a06ffd0957a4921009b6d7933898ec93c3fca3df69f3ead89db3bd3af4e625d73bb7011d37c002d9c1ed88b3f1b88dd53fbbe0ba31f38bdb80cc08b6d3a4cc4bd045e8b4546958483ed84ea02f346957eff18244824d46c9af72a98d53c9c86a5d9470397c31b6c70d242cf3a530e5d760b10654a68bf0024 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1063 : rowClaim true 1063 1451 1973 :=
  checked _ _ _ _ 33 0x3ade0e808e98a892ef92e7cd85b09c4418cc81ab395ce69f80c6d4c891b3da9cd6e318119b26905c8bd0d26207e46c03f5384bae6b22f5cc97dd03adbdeb1be446a6cecfc8b6f200338ed6239aedabbd48f61cacf42e9db035141d17800d3fd996cef2d61aca0afdfa3b3b12b1b130c5e138bd1aade875fa5c7f03d50af510899ffc0d88c585cb1c6900d97f703c88857291c4cab0542ffaaf5030407f952201fc430fa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1069 : rowClaim true 1069 1451 1962 :=
  checked _ _ _ _ 31 0x1d012201a070718a6c709a72723e656e5aea178324730e05f34ba3ae0046559417872cbe212ea199a139335fe0bf094bceb76ebce8f04438155124965c817f9d11a4ee1eb9d562d7079575b79ba518013309e199a2e45304d3d610d5ed0f3aa5fddc6d9b0c74e2f2f558270e4992fc500dd87dd63ed04a192f204c0d06f0253a118c37feadb5aa65d0cd178888b47563aa6884271828e39900d50b0198 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1087 : rowClaim true 1087 1451 1930 :=
  checked _ _ _ _ 22 0x46fbe4f8c60fde66414b4e28ed0a2bedf9c8bf414cecf97b49fab121550ce8701166c415911a048266755388d4a85f8d5381fa9023d0633b2ae41203c638dec2d619877d6d8f82e6788f9e3ba62a02b968e75b4eb1e2eb2f0ca63ef576c570d840a8e9222f2c7c640f7fa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1091 : rowClaim true 1091 1451 1923 :=
  checked _ _ _ _ 35 0x8cc62736d6956420b993b6205c296ee2fd3c888ed12a3f475e23027a357af3b01d888c1a4fc3eb67f5cfd93d181efd188ede9b6f5e861011dbd960f41a23b9bbd428f98c79100e6d87a746519a4a003f7524111bbc189949ae2772776b10e6e13671e7a5724ea6c69bfceb5db7ad20148c4bdee750bb18b9a8906447527200e9c12eda97ed8f65e31d54b7a817beb7c8401bb2f6b49494c71d3e954fb44857da16d422648eebe1898081fc1010e0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1093 : rowClaim true 1093 1451 1919 :=
  checked _ _ _ _ 27 0x337072fe6aa4cd472211d92406311443eaf8b520831d3cd9c0b46acfdf1b1c74afa56744cf223df4108185bb07229faf73d4959146c8daf2e6fba2d039898ed383dcfc5ac8754c75d5ea498b2e26b1838fd93dd7544ef0f185a98c94d250c1f0e3e7f3ee7aa741c883cbb934ea3709ac1dd03c3ff7586d93fbbc34cd44940cf455c13ee93f9003f (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1097 : rowClaim true 1097 1451 1912 :=
  checked _ _ _ _ 25 0x1c3a0001d42912b1bf08b5eccbeffd62b948c51051817e08aa747ac6cfe6cb52aa56e54c838d3c74922ef0650c885d78828fa625bb9ea77f1d8f799f8e00b016e1d38b659f25903da7e26bd95c0ea4797144900d3179aa596d6a74f532ec2af4a8f371e000d230d307929e8c0d8ae1b08151d24463ab2e0c1ef7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1103 : rowClaim true 1103 1451 1902 :=
  checked _ _ _ _ 31 0x1136b8d2c152185f2b9b2d2606bc1813ab241fbae8c489f919ba356f3298bdc61699e1a3692ba13c87f5162e8a1a8df8e5159cd599e20ab62726a2df54097b52605c89f6ea608f2187ff00817ca5c5a57114a2444788dbfcb23207beaea7835c2e8db7f4aff9c601ddc42c56e68b3b6bfa8f0a73e717a7170808c7b0dd55a1fea72d543cbac04da5ff14c55f0b02b5ab97019cc3a3bbf100bd0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1109 : rowClaim true 1109 1451 1892 :=
  checked _ _ _ _ 30 0x18f6e55e37a4570b39f04e8ae31909afe530fcc4ca165bfe062d43d785d75375d4d53328292c35941773595215ce0de876c5a1215ee7b886450c2a036853e8530e09480b41ecc0827c9efb0ab965306dfb2a328b7e8f41e1593a339e2589573a0784d46a0c36619187f3e342898617913f73a80828724c493ee9c06b2ec8ba7b921871fd1066f092c3057c2035268982ed0dc0d17a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1117 : rowClaim true 1117 1451 1878 :=
  checked _ _ _ _ 22 0x7fba81e970b2f95a579aaeb5d085a6ba8e205f74ef44533a1a3db14f6e769e8bb9bef7fb02ed75c849c1e60483c68a8e55fdeb0361d0a2e791180ad7d9eac5db2c8fd68e8b6802162f5b96f551b09b7d29d6e58e0cb2a5c88f8fac81bf063be042ca9d49eb3100301a5c9937003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1123 : rowClaim true 1123 1451 1868 :=
  checked _ _ _ _ 32 0x19e7e8dc033a3611da964cd38f56a1a151067368198dd3aec9c1c7746f274ed724cc508308c6d385e778ea873c5549a3ff6ca41281986d75104ffe3ca3c0317e8409bfb61048f1bbdc8d4891e626af724c2c7eff06d0590cdc4fe724a0874a748214e5c59a70fe8d9a394b1b10908652d29fd285a2dee213b33979ab47fc75690df00cfba305b2496b5bf60607cf2c73026790552c3c7c0ee74ad28069c1086b0060 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1129 : rowClaim true 1129 1451 1858 :=
  checked _ _ _ _ 18 0xdbcf6c30bb639ccd81ca47cb15c88828ab9c4189c3873245026106c22a125c6c28b6b9a673f07ffdb6a5e8623e98891316d7a875ab8f29b0ce19c0080ff2e5d6f1c16f03f3d6ac28f7b8794703cc83053c6cbc09a7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1151 : rowClaim true 1151 1451 1823 :=
  checked _ _ _ _ 20 0x9af5b3201d1ab6aa460b6b98cc63a4014a8134e9fbd67b08206710ccd9c8c28e68d5756ff28ef4d0cb62985e342dc09c10618cdb4deb5013676933ef7b0906d2b59dffccc4e2601f854303b3a2570236b16c623b14ff421105d40e406a5ec0637a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1153 : rowClaim true 1153 1451 1819 :=
  checked _ _ _ _ 20 0x9d99f7ad78d3365aac8cc1bee597fba504f911cbbdda4b08dde73a9eac6e29b5e43f940a5eb44b0b49a8fb828a160325c3504416263092b4804d33219178239c52b111f45489258527f2408a1714c5e1e288a5c9fd64d7b7f31419d9a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1163 : rowClaim true 1163 1451 1804 :=
  checked _ _ _ _ 22 0x1dd85f6b7624e3b0fc752b1ea7a2d248b6f4133e218a6e3150b04e71c7a45b9cbdafeec32e56a2e4e4b95f056b4a9a8a67a0bdb504a4619e0a15afc95feaa111bdf8d2eadee58d1305471875c42019171b2012815c8b4a34123d2ebf07b94d8698767842b69e6fdc04d7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1171 : rowClaim true 1171 1451 1791 :=
  checked _ _ _ _ 24 0x2421ff1f4f06f21ac90d8d14e357090e1e32d7b395226f6c5ee35b405f7f4d2bd7a630669d205e0adcce29c277055c14bdb1d5927e8eba28f367f47f4cc4d712550d88ae3fd6b884e50cd475f43db817d985363d4cf2c0ad893d34554618b38af87c6f0b28d7b8a2c6adbaaac797350c781270a8dca1a7003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1181 : rowClaim true 1181 1451 1776 :=
  checked _ _ _ _ 29 0x450d4e3f009874a445bcac9106131573621e85cfc97d99e59b62fc05bd24468c18c4c067c3d8539a2a694e92bfd9ab05709659eb2359b9d672722cafc27c22126da6be457e713cc643e51f15d3b2899929f719573f14d47ab758a7d0a18522dfaf40ba32506faed1d68fe86d89f3c4a544531ee4a3269b95f810ba329051fa26d2e8d88478a9d0bcc33cb0c03f82021c331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1187 : rowClaim true 1187 1451 1767 :=
  checked _ _ _ _ 23 0x541f0da766ec790594f98154154a1036d5e362fdfcb208d50b64c284002045ad68aa1dc59eecaec3736b1d401a7a79ba2cda12e5976fff5c3ae58c9e9c511d97619c53e748c59a1a8d99ff3685174d65ec41fd02851b8471cbb2d48216d44bc80c3f65c9cb1edac9a3a40ddd1b941bdfa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1193 : rowClaim true 1193 1451 1758 :=
  checked _ _ _ _ 24 0x526457c1a2ad02f2ecb9f8b4599a48c4baaf7adf7cc0bae2a40dc9e0e6fa5f690faf398c777f9663baad20352cf6b5c9fe7b9cc9f870a5b6c558353ea4bedc1e12add02db5588408fc6d5fc33e1a52008724ef86fa302fbbcaaa11efdefd945d3094e2c6d25b854d1c5951532c0d3100c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1201 : rowClaim true 1201 1451 1747 :=
  checked _ _ _ _ 18 0x98ccc3168aa65a4e3e4231b9cc4593b9be95e2bc8cd6ba63bc9d7fe5e8570406615484429f6fe698da99f11f03b0058bf6b499de5680787f62c4d30564e25517c63b2deb61c2f6512d44a23bc0a1f60bc61f83900786686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1213 : rowClaim true 1213 1451 1729 :=
  checked _ _ _ _ 18 0x64d7a72d39ca78b450ed22eafbf3d41cad32cb64123d5e88cd05b3a63db8dd46a4b7a39346ef2a6e66ed1bae2f345ca0f0f83ef22fe86cd4b5f1ce320a9827ce11f224ef6f776500e9c43bc3afb5013dcde5f008c968a3001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1217 : rowClaim true 1217 1451 1724 :=
  checked _ _ _ _ 17 0x3dbb6c58b9337910ff359c756bb87b59736a99423bee796e3d728bec1b528e048ac2e96016322abfb89fcb6979cc5e5b56697785673433d04668084d6ce143749b2e96be778257fc9d83744aa2a0007c3a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1223 : rowClaim true 1223 1451 1715 :=
  checked _ _ _ _ 20 0x577686d2148e679552ffac82888393be39600ac4047a641e61f5a105f6c6ed75e7a49343358b09218ba39832a10c0e0f5cfea3e49bc0e3e8b86041794071b4c845d10110bec8b9ff2f09c75e003307bdfac65c385ee229d7d00f8c16f3006c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1229 : rowClaim true 1229 1451 1707 :=
  checked _ _ _ _ 22 0x1eb807adff55af03cf87daae07c96e5b3db26c8635209abb229b255bdd04146e1e714e0f564389d7981d85eec395f774e9ee2cbd1b15024c222ef75ae88e5550f2b5ae45cf076b54b52b8020d982e8341b661eba388e07677be9ce09c2cd079e5dc55ef89a5144d58c1817a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1231 : rowClaim true 1231 1451 1704 :=
  checked _ _ _ _ 21 0xd16f264d0686df63802ede117a86dd87916bf5ce05dd83eaecffd994190cb04e37775fe5354de40f5ae8f45b3a434b3e5678c9d401e030f88d5bf49338d6358ecb449775e123b0cc023331489e4bcfb43df9ace6ed4221e1a5b05b83efdc204eed0dc0d17a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1237 : rowClaim true 1237 1451 1696 :=
  checked _ _ _ _ 18 0x193b4598f689c2870e50aa2323d05f9a6957c989af0810ff77d732713c75685f983599aed30386c76504e9093df936027e5d03477136ff306f3fe2e18eecafa3891ebaf027a8841b027e9b30ad12784e697cfca8b0259c9937003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1249 : rowClaim true 1249 1451 1680 :=
  checked _ _ _ _ 14 0x1f947411e14069e12a516e320460ec193af4d6d6ed1b6737537ce58ff1353f9a3b85cbbddc050ce2339d5cd3f95283f14c0bdf4aa4b84750b1de01c3a98d900c86686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1259 : rowClaim true 1259 1451 1666 :=
  checked _ _ _ _ 16 0xe4a29cd959ff2591484cab25a6e16f9a273f160b6ea697ec18233237a6447311831033c42ccc2516513783d27746c16162699b34b297c041f00c782a3d5f1dc88b3b6def204c10cbbf01f80a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1277 : rowClaim true 1277 1451 1643 :=
  checked _ _ _ _ 17 0xa05ef5406bdf50ec337ca5f3887d0ad143f293642303428f1dbe8cf5127e360f34d8bd1e6277be60d34ff23fb4295b8f6bc71e203c5cb0458ea47d668bc7ea99f48064649811a26e20993a40760438331430018 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1279 : rowClaim true 1279 1451 1640 :=
  checked _ _ _ _ 19 0x9b6204ba8d8e75d6f9d08d68f946e0f428d6f9f9fe92f167d268f48bdb5e023fc4206f821fc923be5659e47122d21548fc92f1499d47de27887ff57832f7eaee2ec105c8ce1170070b117716c7ecc2bcafa6ba1ce7571863a04ed2d3eb0038 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1283 : rowClaim true 1283 1451 1635 :=
  checked _ _ _ _ 16 0x8094f80effbfca82d0fd8948bb9d81f7deb6da09a39938b1856f41b283ba837e8802ee3a899a8a4aaf2b9a34cd2e42e37d203a0e370188bc4897a6bb839cecb6375da0353bd96c39a634060ba707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1289 : rowClaim true 1289 1451 1627 :=
  checked _ _ _ _ 15 0x792777df8ac8d8caee0cf96c878f44f11c6e6dfd5b7953661affad633a322cb6181e0ead45e54137e14c82ee615ba63717e3afa66938581df7e9b30f744cf7a6a4c208e907086686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1291 : rowClaim true 1291 1451 1625 :=
  checked _ _ _ _ 16 0xa9b286a970358b354a5787abb5a0795ff4cbb2574884099828d46129446f1943abd9fbdcd5167cee7670f29af087fbf6d3ef00ead4377323b2c2a04bb1da15f659db79b3a1b0377318d097fca1a7003c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1297 : rowClaim true 1297 1451 1617 :=
  checked _ _ _ _ 14 0x434c8ca18e2ebf39b3aac50ffb574d118951b154c9c8ea3f0d8680195e5a933890ac276cb1c26ee7f1c145b981fc7bd490f9249949b62baa8d8abfaab71c06e7a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1301 : rowClaim true 1301 1451 1612 :=
  checked _ _ _ _ 18 0x16055d87b5f2dc6cc9b780eb6719b5c3ea2618ec8524cf16b1f494cde9e4ca65fb033d8842734e5f46712e599b687a8957b1bd5156f9ab6f7026f84cd9f79849237cbe006949e90a893f9b474e2c809471c4aa73044c7e907002c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1303 : rowClaim true 1303 1451 1610 :=
  checked _ _ _ _ 18 0x4cba880c95a15f584f16cbcb794bfbf68eefba302fa3216392c34766f09701639f79b7ba417a19b8332a3a29bfc7216a7250f6738f1d1d2db8754fc409c220803049bf4f1544fe8ecd3983ee64e6f9845f8085201eb2d3eb0038 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1307 : rowClaim true 1307 1451 1605 :=
  checked _ _ _ _ 15 0x54b87daeb4eb51283f927cb7d37612e7b0efbc1c211f01c28529c9d05eea0ab781ab298a10f1e4ade03c3c8c67f6ae7ff23c08fbc8e8bf493f2d8ae1af482c1cb462e1fed807c3a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1319 : rowClaim true 1319 1451 1590 :=
  checked _ _ _ _ 11 0x135d64db71cf416ba2ebf298bcf9f175c789f292799b35d56046f9fb07e45c096c65488d2d9a0f3cc143fe16b5a82aab4073fa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1321 : rowClaim true 1321 1451 1588 :=
  checked _ _ _ _ 12 0x16caac821a6ca16f2a146914348cdbe6240b1979053a0ca2ccdbe9a562cc83f7dc14b395c29070468e9e86d9cac5a66f44591041101db6686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1327 : rowClaim true 1327 1451 1581 :=
  checked _ _ _ _ 13 0x25ba264ebb93ff737528eefe842cffcba28aed1c5d5bcb6b5aba6698520db8689680f29b1276b253cd70fc962e8668425fe33e2303e71bf4250cc6937a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1361 : rowClaim true 1361 1451 1541 :=
  checked _ _ _ _ 14 0x173687f90c7e8c888aa6283a557e8d8d572ad8fbf16490113336c1773e6a1a9eaeba846b02281a6f1fd55e1d655a8b9579314c795ac4ca0e42d7828b41ecc7c640f7fa707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1367 : rowClaim true 1367 1451 1535 :=
  checked _ _ _ _ 8 0x4eee2feee57d272668d7c6a0739eac1179e224c833d3d426829d7d00f8c16f3006c0a847000c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1373 : rowClaim true 1373 1451 1528 :=
  checked _ _ _ _ 10 0x2e2236ce61ec5f64e667eb9ccaf7043127687ded5847e20498f3f64ae9210ca721c1e3d6fc146d01e1a080c0377a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1381 : rowClaim true 1381 1451 1519 :=
  checked _ _ _ _ 11 0x309115ca9ac850d13db0a42cc8c4c883c7334169f7af9fef6edf8b3f797defa94656d219037f883291cd5abe6f37bbb038e968a3001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1399 : rowClaim true 1399 1451 1500 :=
  checked _ _ _ _ 8 0x1b58fb0c501d32441f3526582f259d018d033f2d6680f48f870cb2271233eb422d0c35ec3c50023 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1409 : rowClaim true 1409 1451 1489 :=
  checked _ _ _ _ 7 0x1892e6617a6dfa34826ba154c8cce460b076207f548d3e639da98d900c86686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1423 : rowClaim true 1423 1451 1474 :=
  checked _ _ _ _ 5 0x22c55ed22bfe52a00a6e47329b26935f3f099f067f16b007e (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1427 : rowClaim true 1427 1451 1470 :=
  checked _ _ _ _ 4 0x6d59a0f3d07bb8298bb1297b3c3027a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1429 : rowClaim true 1429 1451 1468 :=
  checked _ _ _ _ 4 0xe0f2e4b3ad5c5f0c17f6cd74c0a57a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1433 : rowClaim true 1433 1451 1464 :=
  checked _ _ _ _ 4 0x3168c4b7ba38040bb067400c8d00646686f0014 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1439 : rowClaim true 1439 1451 1458 :=
  checked _ _ _ _ 3 0x7f105d40e406a5ec0637a707000b (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_1447 : rowClaim true 1447 1451 1450 :=
  checked _ _ _ _ 0 0x0 (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_17 : rowClaim true 17 23 123362 :=
  checked _ _ _ _ 370 0x174a3971fa78428ab5598bb6cff8f47de3f94e354f057d455a93f041e142fe2661d8e24272cdf502db6f0517f60828eee599653b19d71ea75da88eed374ade3023ccbff4db8329364f6acfe4d3e71f5319a9028c3daf1b71b6ebd184544b462d94651a9fe639ab1707e09e467e45c95539d1a5025092e1b70fc8b1c9adb6d8c458bd2b79bf8663ca666cfe2fcc294e363ba359ee3e5933031858454bd93f1fc4e9458f7972c60facb575975604f3c453bdd1d813998c3fccd98af733dd7f5762e65d7e828e66452a26f17dff0d6b2abd2f7f85df974bb23f77cce728144b9005f6b9babcc7b020b60f3c6881854bfa6bc423c97e4ac859bacab5ffcda6153d438062e82c220a0959f1c1f9ca39df64ea32ebdd1181da234aed61d72c96674879f1fff0e7bf84708861cdb6919583ff6729d7100541bf2f0220429d6e52a2c115d4f57c3b6f64d0b949178242b58257631eae1f3788499a49c96963d447c5b1105ac7e5b32afc8c3fafa7c1c9da025d239658f0e5f84e3cc93228e8d279be4256cd7785064e40ace5f2dbd7fcf20ad501eea998dc1655d40f4b960542d97bcda22f84847750c011e3c9dcd4bcabf51656ba3ab201646fd405681e678341415354e4243d46e1733bf89133da9557d7cca12144f3b2851f2cc85220654188fa67dc4f9a4879cdb3978645f702353e83e5c1ce718ed8c33c9182ca6eb3bb89896dcb89c0413dfd035baf6e33dfab88637aa0c152b14375eefd483f02d37b1092e995092bdfd6e6b85dda37754c82ac3442d4b4f90d9fbf890afe480155c347647dbe581b3eac15b356971e7225d80a6cb0b0fa52b392994743bbc8aa09d6188158b59c070fbcc8a3aec8d6e4d761371a4d292fbd63c28dfd7cc2e562da5b67a62dbb1d87c1c95ac6783a6ae01c6d4e93cc07338008211418ba0071048b0ac48319691128333145a5eec1111401a3e88b6ce2ae4e9e74828bb41436bcfc2f68a33e3126423275dba03f6bb32f925f50f80b0224932aa8c816046f081580216355563284b2ccb4fc1a36fca8511d4ef69481a47138ca46190ef26412e3f23342ba375ee2aa96d96fbffd4636ce84ba9720711ab8ad19c6775744187686ef615d562ae8a6c70295b77f08e382e2b802dd918172c376c20dd3d533f95b285655279e074906417037dc7e2aed5322a23973fa3b8d7c5cc68d26eb00e3a8f737e8cf636198e46bb5d46ff7225c45f03119b64ccaf37591494c024f167b36ed9ce329594cf1c7c8bea52c76f6cbbbda8145ef2b1a1c256e910bc981bd77948d0e2fc0fac59af83526e74ef3a5ac2c7407d2ded6f7f57ce88e366963fadd0726c8893fa487d176ce187c7cf2828a723374b22d14b6390a4fe70ef80e749f76e59463febd5070340f3d51dc236dae6c3308737cff246dabcaca8a02d732ce099dcfd362f506ea96d0f629b115da4338eea20c37c29eadfc9de4ad8cd9df67af89090d83121bfb54adbb3376e56760cd4e3e47653a93c51199fde2bba0545e753447daae00325e3462119bd9993a633f7c28da9eb134010a93762399fc9c9a21d5bdcb0c23d867d99ff33ff1838daa08610e801134958084b294e7dd318a5d028f707c9fb9200fc4860534965f9d60dd56fdee71a0b933ac93dc0a3743461eccf9d06051a8c853b382e6d61af27609e47cf3e05bdca7a76c96874e7afb42b5df9566c424dcd006ea13681e454a9ec73109f29a476be791ea174806b9ff58c00075426d35d15a245abbbc38e5d41b53c286d2d1215f21684034074e6a9aff43f901b3c7e2cf167fe07d8db40724392362e3f2e1e5f7925ab97d99cdb8efe3f581a4fce16688a3e39cf859a3f46ada370b6121a07ce03c818524b006991385571b2415fff0965d175b02ddeefc8ca1207fc651803413a7075a31de4f1e436cb9963e02cd530f2eb777d915b0e1d251dc9c369853a1603462b19dab9e24489d9fc25bec28f3f287726ee48f00ec225e934bf1982f47188672e7db2d77f14556df2b57f05b92c5db84a9d61cf7f11dcce34efef8e25fdcf54273a1153ba840ef5dbb79fa526ea4473d7092b04afb39e0d3c4aaabfeaa11ae31db2bc1324d6e496d33cbe027e234142e735583d4fe06115785ac789e49aa2451b22a85fa7abc622d6ec3b16004f3f227a06710a7d58d9d7945c87203adec611ffb9eaf0bfe32d1b0fcd944b4afef065bc1bf4ecd19924100eef9154a452ef9352b1ff52666456e60f9e554c6d110adb3422a51733ec436edf615aafcb66211f49621090202d66fb0d72b34402b66b8686c9a5bbc6a1b2a20b5c8a0d190f53dc6efc5efd08e3feb9725bee1d0a6e0821e2bea7fc1d301a327f2268aef0ac2da94d93fc827e46bbdecca826f93efe83276a2a81eb808e3eae020b7ce49e5cc1175cd5f0a1390d13542135d853e9134955a4e3bd55bc552370343e525c95cbb30ab6c2cc8ef68c6296001b07e302cc8fd65716ec7489e680b688e28c79dc52108b4b306633a9ac2713f0f01a4cb57fb78e621059777340350587aafda7c4c71445d4f0dc00a408d605325e0ea01b04cc4ce88e8bc4ed3201171ea8785e3d3f39abd9371d577cead2c20846a0acc3e1f608002fd25d68952ea4900c6f2fc1b1ce0fc0fa925fec20d35bbb9bb3e5eecb132ade7012110c5d577e6fa7e02ede5cc674b15ed6039dcfe041e59c5144172fe9b1accaa7779903855c2dd65175c54d7293a1edcf32207a36457fc199d341807455be56c7fc86e78d2badcf41f8866d74d7a83f90462d5e51ebde7619d0e2807adce1547e417b098db302396815f0f74100478bb43001c (by decide +kernel) (by decide)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem base_index_19 : rowClaim true 19 23 110377 :=
  checked _ _ _ _ 464 0xec6073053c0fdf40d6d241fd13ba714cbbeaa2cb21e3e9bb6f9a853490a38a5891faf3890301b516d28da66782c33085dda7524169ba418dcfc652b5df586c654c652985c119bf3c1831e70b27abbe0d23749189010e6fff94386f8afb207695a06c13431c0162da83f19c5fa98c4e9c6b9a1c11ea3a754e50e5b1eaffc527aeda91eddf78c8193f2462e9695f9847eb92e3084f06f0d73fc1eb109eb4f7e3bb85291e8eea464e31b6d39bd3916b893f5f8beb0d6969fcb863cd2f5b3dcca543aeb97ba5d672d5d886263b63352d2df201e3090c65f29e18a91df55111dd05a0529bc2f9003cc1de0c2eb5617b5376e84c53e428c8c72af08b2975c92e6b74d1a4b2e3f09678458f55e8905830f9893f404de604d1c465fed1912177ec77d66da81499b8a8575d5117f16347c5976991c8a77184c10939871893bfaf58faeca7bba2c3fd9bfc2568da6659ac7ac630bc5d61212bd18bd239ca4e71b91932a4363ab1c26ccf21838db13c332ad89aea37dc45b15b10b5532609164c6b80ca4b10f61925090496f0ceb159306cead90e49c1bd0d5e527d56adcb4296c4583c9ec14ad2022ab872d50a759bae87c252077b49bd7c23dfcabe2e0565329bcb58ca1cf56e48285762bd2bc680e001641f713beabe8df191f015c6b913099f8a239b403d7d2f11d1131ce8226ce0a22c920ff254b7ed0bfa7617cee3b59e378908a289382bf72682682ec5629bc444719ed570dcdb6cc81c86876d649d8a44af5c909eafa57ecae0f706c65c005df720b4ec07d9fcec63e6288d5284d2d51e0dc1f1f111047cee1f801e8f0febf5a844030ac2d95bbd212e511fd470a118aeef782e415c960472414253e85355f48215f71d274d037cb2cb642c49824a35220127b3a1503b190f112d8db7fa7e55ff016cf6e0358b06ef0d4dc75d97c5183207c8c19db0452697af8d26ce4e477f3a62251feedc627c1bf3b06afdf2cfdedb2ecd8e457a954da5df87884119b39f722fe600ebd6d002151a8ea18bdd90f2dc8f7cc5051b0278234f60c133f22cc034ced1bcb1a059a684e4e3fa9c1398ad79a47407deb24b2dcea5ee94bb23b62fa3885c6927cf7bd0e6dbe0ec4802f2677d9f0d34d681b5fef460bbd837a898f2fc603d3ad2c5feefb4977fe674f9b406bc49c9cc95f9645883bc4869741b9666b5afd53717ed814d771e0de862bde8af2fcd25cac5ac3cc90c6a3f8e91e62baea72887cb136e2322d983fb1d6ccb1328a14cb683989a10dea08587ad21c419c4a6ee021c996775745ceca85cfe44c53080336c1dfcce49a47da00bf77978147a0754a4fb01201d706797602f3e58ded487992f66a86cda9a5f8ecd7db4a1c579ef058a6ebbb1a5cb11fb09cfbf0d5d9ca661697487115b2491b0d71045ff8bc1cae6e87ba30be53946db977c475069605f9dee564403fff54dda5941fadb95caa204ac8d1c059ceb4ef9daf9ff894c10f5e699b436d2c5dcc3009f3d62b5bdbc5da6a51cf80982e28de53397e8ffc964a758cf24975a2620c4d5909c0ceaca1bdaac9dbb403df0384be983930228b7a6a8c3ffefacec464e25f8e0b03ed75b27d11ce27ddfc2e0e3c50acd2e217605860d081d5a634720f7672cf43bc7b208ab9e55da3320e4f106f42c5a0e0469f0205fabe3ef69602ae47fb065229237be1641a1c627d982ca327f9d63fd669f591d92aa4893772ddd4e613a0c51c6fd01c09d70ac21f2aef7ff65a3bf0913c79850daf8b107059650fecda6aeb795145ed6c5afcbf736d8a800a29d3972a8951c8974c1fd6565f8c4c010533ee68c6ab7570a6509575525dd5f0c11b4629e480a5df051bd61bbabc241173682cc485a81fee8112cce5515322fc783bd6aeebbf4f6f66ce6b540c6e13a16944056bdf28c21483900c24c018df325408cdfa12c85552cc7d4061b815f501c2ce6eb21ded565c5a1c298df1efbec66c454fef353c31d6c0ea9f0444bcf2bc66c02852e1c504c8a1e159e44af56d8e615656140e0b0fbd5e77bcd4f64c7a9bf6cbfb95505fdf6c57355946aa97cf43bed9415002daa573ce6a0390184916834e799fc989ad0dd11cd8073262ffcf05919e33dc2352b25a65cd3743a3d82decc0f58e5d1ab9f03f39c2b54dd7c10f0e99c8d54ff5792be7c8862649657fb7b62408616d3d4e4ff902920aa8bd21d6b09a1e4a7169708a90354081b5a5fc59a0edab2decbe267eaa83ada9b42ab0ac18df965ad26bc6dcd5a23dc51f049d122017f647f1e199743b30922dc8cb47828cd70d165cc75caf7f1bc4c763def1b8b49e4dcda0bd030be9e8d2c26d11450f86ddcc741613a827d5151e0343da51e972b6c8c76ff7ffedaf8c055122de8f42db9cc7f68a0227a9b0e00245fdc0288ada5a65a7d64eabc20a7ae7d692779f04f54c2ca3e6f5bbe39633d307de62acfe2a8ed50f3f3f7e2848a2b605086c4e4f1e930fb64aa4eeb9d8c53cc0610226eac5a04c0423f4399b326f4931b929f1ebd879815d63cc599ed1171116b2c389a9a167bf9837b95278faff30e5a1d1c5c28e479636db8e459b24cca234ee89794c7b24dc79355002f09e3a811275bad5f8965cc7665c2d49e6fc569c3ec465a1a51758a9513ced3bdb3cb26b730152bf72d71ad03a89d869d08efc441cca15078c459689ea5e47cc4e223afe13bb7641c6b0d2657b9028fce5bf2d48b4aff3c3db3d88f8ca56f81f04856f39a039ff445b352a0398db5fa41c19f62ccdf8f08e00bfd0f6787eb7aa679385b40d598add91e892959c8b0fcd59e959c910387ad81373a5b22f7d46b5bf5a021411f9be341d88d9e491953a73652284f3f4c8d0b8b028afc842318caa718b20999bc9a7909d555e7a7f8e3e7ba3c70fb9a5c05d700b93e005f67f36930c5c4ac99745ec6c298bf576a4078f1e1861a5d633c1ef0d1847336de28e8f51aef4b8d6c8b940d986bcd49e45e1d8cd6c64c1d15ce5734daf2d846419343db5ee4c94548392f5a5d78f44301989f243d1aaa2e38e888eeeed3ed6b427549554891165df019d3919b3b9630e2ee6731c16ad68f8d014be8405b75c4d6d27668d5e4aee14834b9deeafcbce4233f9240e8b29d61223cd2c70bc09af25fbac7e345db1a4713c8b8cfcc02cae2a3889b1c8eee309d9d30d05b831d25678164f02f4b6cc4d86d88c721eb05d5803d56785d9d7cc1759ec366c1fac070e645e52092da7daf9915f4e12e9028a2523e11d0e897037c5abac40343e23e71f0abdb0b1474089c967e182eafd724258548d5b0ea22e071b41e6b6b6b923a43264551305ff6e221e2c2645c5618e630bdffc98f9135638a9c54575648f831f7d77a0b5ac0b80bbe0dbf2cc4becba77089cabf80388ee1fb5cef7c9d7392084ae874bcde202e9baf1bc5958362791164f6bdf9ff01541654ae3a40e83e0d60254f6196f97207b00ab34140bc182894efc1980014c42e11e499fe460d121f59cc309a30b65fcaeed2dc9138a370856e91ff25165315896e2e6306d11353932f80ac6e46a1fe45af9009733b23003c (by decide +kernel) (by decide)

private def smallAllowed (c : ℕ) : Bool :=
  [2,3,5,7,11,13,17,19,23,29,31,37].all (fun p => c == p || c%p != 0)

private theorem prime_allowed {c : ℕ} (pc : c.Prime) : smallAllowed c = true := by
  apply List.all_eq_true.mpr
  intro p mem
  have one : 1 < p := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
  by_cases d : p ∣ c
  · rcases (Nat.dvd_prime pc).mp d with h|h
    · omega
    · simp [h]
  · have z : c%p ≠ 0 := fun e => d (Nat.dvd_of_mod_eq_zero e)
    simp [z]

private theorem inBin (P : ℕ → Prop) (l h : ℕ) (xs : List ℕ)
    (test : ((List.range (h+1-l)).all fun j => !smallAllowed (l+j) || xs.contains (l+j)) = true)
    (rows : ∀ x ∈ xs, P x) {c : ℕ} (pc : c.Prime) (low : l ≤ c) (high : c ≤ h) : P c := by
  have eq : l+(c-l)=c := by omega
  have h := List.all_eq_true.mp test (c-l) (List.mem_range.mpr (by omega))
  rw [eq,prime_allowed pc] at h
  exact rows c (by simpa using h)

private def powerIndex (c : ℕ) : Prop :=
  rowClaim false c 23 (2097152/(c-1))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin0 {c : ℕ} (pc : c.Prime) (lo : 3 ≤ c) (hi : c ≤ 99) : powerIndex c :=
  inBin powerIndex 3 99 [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_3,exponent_5,exponent_7,exponent_11,exponent_13,exponent_17,exponent_19,exponent_23,exponent_29,exponent_31,exponent_37,exponent_41,exponent_43,exponent_47,exponent_53,exponent_59,exponent_61,exponent_67,exponent_71,exponent_73,exponent_79,exponent_83,exponent_89,exponent_97,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin1 {c : ℕ} (pc : c.Prime) (lo : 100 ≤ c) (hi : c ≤ 199) : powerIndex c :=
  inBin powerIndex 100 199 [101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_101,exponent_103,exponent_107,exponent_109,exponent_113,exponent_127,exponent_131,exponent_137,exponent_139,exponent_149,exponent_151,exponent_157,exponent_163,exponent_167,exponent_173,exponent_179,exponent_181,exponent_191,exponent_193,exponent_197,exponent_199,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin2 {c : ℕ} (pc : c.Prime) (lo : 200 ≤ c) (hi : c ≤ 299) : powerIndex c :=
  inBin powerIndex 200 299 [211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_211,exponent_223,exponent_227,exponent_229,exponent_233,exponent_239,exponent_241,exponent_251,exponent_257,exponent_263,exponent_269,exponent_271,exponent_277,exponent_281,exponent_283,exponent_293,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin3 {c : ℕ} (pc : c.Prime) (lo : 300 ≤ c) (hi : c ≤ 399) : powerIndex c :=
  inBin powerIndex 300 399 [307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_307,exponent_311,exponent_313,exponent_317,exponent_331,exponent_337,exponent_347,exponent_349,exponent_353,exponent_359,exponent_367,exponent_373,exponent_379,exponent_383,exponent_389,exponent_397,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin4 {c : ℕ} (pc : c.Prime) (lo : 400 ≤ c) (hi : c ≤ 499) : powerIndex c :=
  inBin powerIndex 400 499 [401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_401,exponent_409,exponent_419,exponent_421,exponent_431,exponent_433,exponent_439,exponent_443,exponent_449,exponent_457,exponent_461,exponent_463,exponent_467,exponent_479,exponent_487,exponent_491,exponent_499,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin5 {c : ℕ} (pc : c.Prime) (lo : 500 ≤ c) (hi : c ≤ 599) : powerIndex c :=
  inBin powerIndex 500 599 [503,509,521,523,541,547,557,563,569,571,577,587,593,599] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_503,exponent_509,exponent_521,exponent_523,exponent_541,exponent_547,exponent_557,exponent_563,exponent_569,exponent_571,exponent_577,exponent_587,exponent_593,exponent_599,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin6 {c : ℕ} (pc : c.Prime) (lo : 600 ≤ c) (hi : c ≤ 699) : powerIndex c :=
  inBin powerIndex 600 699 [601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_601,exponent_607,exponent_613,exponent_617,exponent_619,exponent_631,exponent_641,exponent_643,exponent_647,exponent_653,exponent_659,exponent_661,exponent_673,exponent_677,exponent_683,exponent_691,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin7 {c : ℕ} (pc : c.Prime) (lo : 700 ≤ c) (hi : c ≤ 799) : powerIndex c :=
  inBin powerIndex 700 799 [701,709,719,727,733,739,743,751,757,761,769,773,787,797] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_701,exponent_709,exponent_719,exponent_727,exponent_733,exponent_739,exponent_743,exponent_751,exponent_757,exponent_761,exponent_769,exponent_773,exponent_787,exponent_797,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin8 {c : ℕ} (pc : c.Prime) (lo : 800 ≤ c) (hi : c ≤ 899) : powerIndex c :=
  inBin powerIndex 800 899 [809,811,821,823,827,829,839,853,857,859,863,877,881,883,887] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_809,exponent_811,exponent_821,exponent_823,exponent_827,exponent_829,exponent_839,exponent_853,exponent_857,exponent_859,exponent_863,exponent_877,exponent_881,exponent_883,exponent_887,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin9 {c : ℕ} (pc : c.Prime) (lo : 900 ≤ c) (hi : c ≤ 999) : powerIndex c :=
  inBin powerIndex 900 999 [907,911,919,929,937,941,947,953,967,971,977,983,991,997] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_907,exponent_911,exponent_919,exponent_929,exponent_937,exponent_941,exponent_947,exponent_953,exponent_967,exponent_971,exponent_977,exponent_983,exponent_991,exponent_997,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin10 {c : ℕ} (pc : c.Prime) (lo : 1000 ≤ c) (hi : c ≤ 1099) : powerIndex c :=
  inBin powerIndex 1000 1099 [1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_1009,exponent_1013,exponent_1019,exponent_1021,exponent_1031,exponent_1033,exponent_1039,exponent_1049,exponent_1051,exponent_1061,exponent_1063,exponent_1069,exponent_1087,exponent_1091,exponent_1093,exponent_1097,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin11 {c : ℕ} (pc : c.Prime) (lo : 1100 ≤ c) (hi : c ≤ 1199) : powerIndex c :=
  inBin powerIndex 1100 1199 [1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_1103,exponent_1109,exponent_1117,exponent_1123,exponent_1129,exponent_1151,exponent_1153,exponent_1163,exponent_1171,exponent_1181,exponent_1187,exponent_1193,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin12 {c : ℕ} (pc : c.Prime) (lo : 1200 ≤ c) (hi : c ≤ 1299) : powerIndex c :=
  inBin powerIndex 1200 1299 [1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_1201,exponent_1213,exponent_1217,exponent_1223,exponent_1229,exponent_1231,exponent_1237,exponent_1249,exponent_1259,exponent_1277,exponent_1279,exponent_1283,exponent_1289,exponent_1291,exponent_1297,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin13 {c : ℕ} (pc : c.Prime) (lo : 1300 ≤ c) (hi : c ≤ 1399) : powerIndex c :=
  inBin powerIndex 1300 1399 [1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_1301,exponent_1303,exponent_1307,exponent_1319,exponent_1321,exponent_1327,exponent_1361,exponent_1367,exponent_1373,exponent_1381,exponent_1399,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem powerIndexBin14 {c : ℕ} (pc : c.Prime) (lo : 1400 ≤ c) (hi : c ≤ 1450) : powerIndex c :=
  inBin powerIndex 1400 1450 [1409,1423,1427,1429,1433,1439,1447] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨exponent_1409,exponent_1423,exponent_1427,exponent_1429,exponent_1433,exponent_1439,exponent_1447,by simp⟩) pc lo hi
private theorem powerIndex_all {c : ℕ} (pc : c.Prime) (lo : 3 ≤ c) (hi : c ≤ 1450) : powerIndex c := by
  by_cases test99 : c ≤ 99
  · exact powerIndexBin0 pc (by omega) test99
  by_cases test199 : c ≤ 199
  · exact powerIndexBin1 pc (by omega) test199
  by_cases test299 : c ≤ 299
  · exact powerIndexBin2 pc (by omega) test299
  by_cases test399 : c ≤ 399
  · exact powerIndexBin3 pc (by omega) test399
  by_cases test499 : c ≤ 499
  · exact powerIndexBin4 pc (by omega) test499
  by_cases test599 : c ≤ 599
  · exact powerIndexBin5 pc (by omega) test599
  by_cases test699 : c ≤ 699
  · exact powerIndexBin6 pc (by omega) test699
  by_cases test799 : c ≤ 799
  · exact powerIndexBin7 pc (by omega) test799
  by_cases test899 : c ≤ 899
  · exact powerIndexBin8 pc (by omega) test899
  by_cases test999 : c ≤ 999
  · exact powerIndexBin9 pc (by omega) test999
  by_cases test1099 : c ≤ 1099
  · exact powerIndexBin10 pc (by omega) test1099
  by_cases test1199 : c ≤ 1199
  · exact powerIndexBin11 pc (by omega) test1199
  by_cases test1299 : c ≤ 1299
  · exact powerIndexBin12 pc (by omega) test1299
  by_cases test1399 : c ≤ 1399
  · exact powerIndexBin13 pc (by omega) test1399
  exact powerIndexBin14 pc (by omega) hi

private def baseIndex (c : ℕ) : Prop :=
  rowClaim true c 1451 (1+2097152/c)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin0 {c : ℕ} (pc : c.Prime) (lo : 23 ≤ c) (hi : c ≤ 99) : baseIndex c :=
  inBin baseIndex 23 99 [23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_23,base_index_29,base_index_31,base_index_37,base_index_41,base_index_43,base_index_47,base_index_53,base_index_59,base_index_61,base_index_67,base_index_71,base_index_73,base_index_79,base_index_83,base_index_89,base_index_97,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin1 {c : ℕ} (pc : c.Prime) (lo : 100 ≤ c) (hi : c ≤ 199) : baseIndex c :=
  inBin baseIndex 100 199 [101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_101,base_index_103,base_index_107,base_index_109,base_index_113,base_index_127,base_index_131,base_index_137,base_index_139,base_index_149,base_index_151,base_index_157,base_index_163,base_index_167,base_index_173,base_index_179,base_index_181,base_index_191,base_index_193,base_index_197,base_index_199,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin2 {c : ℕ} (pc : c.Prime) (lo : 200 ≤ c) (hi : c ≤ 299) : baseIndex c :=
  inBin baseIndex 200 299 [211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_211,base_index_223,base_index_227,base_index_229,base_index_233,base_index_239,base_index_241,base_index_251,base_index_257,base_index_263,base_index_269,base_index_271,base_index_277,base_index_281,base_index_283,base_index_293,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin3 {c : ℕ} (pc : c.Prime) (lo : 300 ≤ c) (hi : c ≤ 399) : baseIndex c :=
  inBin baseIndex 300 399 [307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_307,base_index_311,base_index_313,base_index_317,base_index_331,base_index_337,base_index_347,base_index_349,base_index_353,base_index_359,base_index_367,base_index_373,base_index_379,base_index_383,base_index_389,base_index_397,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin4 {c : ℕ} (pc : c.Prime) (lo : 400 ≤ c) (hi : c ≤ 499) : baseIndex c :=
  inBin baseIndex 400 499 [401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_401,base_index_409,base_index_419,base_index_421,base_index_431,base_index_433,base_index_439,base_index_443,base_index_449,base_index_457,base_index_461,base_index_463,base_index_467,base_index_479,base_index_487,base_index_491,base_index_499,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin5 {c : ℕ} (pc : c.Prime) (lo : 500 ≤ c) (hi : c ≤ 599) : baseIndex c :=
  inBin baseIndex 500 599 [503,509,521,523,541,547,557,563,569,571,577,587,593,599] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_503,base_index_509,base_index_521,base_index_523,base_index_541,base_index_547,base_index_557,base_index_563,base_index_569,base_index_571,base_index_577,base_index_587,base_index_593,base_index_599,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin6 {c : ℕ} (pc : c.Prime) (lo : 600 ≤ c) (hi : c ≤ 699) : baseIndex c :=
  inBin baseIndex 600 699 [601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_601,base_index_607,base_index_613,base_index_617,base_index_619,base_index_631,base_index_641,base_index_643,base_index_647,base_index_653,base_index_659,base_index_661,base_index_673,base_index_677,base_index_683,base_index_691,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin7 {c : ℕ} (pc : c.Prime) (lo : 700 ≤ c) (hi : c ≤ 799) : baseIndex c :=
  inBin baseIndex 700 799 [701,709,719,727,733,739,743,751,757,761,769,773,787,797] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_701,base_index_709,base_index_719,base_index_727,base_index_733,base_index_739,base_index_743,base_index_751,base_index_757,base_index_761,base_index_769,base_index_773,base_index_787,base_index_797,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin8 {c : ℕ} (pc : c.Prime) (lo : 800 ≤ c) (hi : c ≤ 899) : baseIndex c :=
  inBin baseIndex 800 899 [809,811,821,823,827,829,839,853,857,859,863,877,881,883,887] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_809,base_index_811,base_index_821,base_index_823,base_index_827,base_index_829,base_index_839,base_index_853,base_index_857,base_index_859,base_index_863,base_index_877,base_index_881,base_index_883,base_index_887,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin9 {c : ℕ} (pc : c.Prime) (lo : 900 ≤ c) (hi : c ≤ 999) : baseIndex c :=
  inBin baseIndex 900 999 [907,911,919,929,937,941,947,953,967,971,977,983,991,997] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_907,base_index_911,base_index_919,base_index_929,base_index_937,base_index_941,base_index_947,base_index_953,base_index_967,base_index_971,base_index_977,base_index_983,base_index_991,base_index_997,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin10 {c : ℕ} (pc : c.Prime) (lo : 1000 ≤ c) (hi : c ≤ 1099) : baseIndex c :=
  inBin baseIndex 1000 1099 [1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_1009,base_index_1013,base_index_1019,base_index_1021,base_index_1031,base_index_1033,base_index_1039,base_index_1049,base_index_1051,base_index_1061,base_index_1063,base_index_1069,base_index_1087,base_index_1091,base_index_1093,base_index_1097,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin11 {c : ℕ} (pc : c.Prime) (lo : 1100 ≤ c) (hi : c ≤ 1199) : baseIndex c :=
  inBin baseIndex 1100 1199 [1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_1103,base_index_1109,base_index_1117,base_index_1123,base_index_1129,base_index_1151,base_index_1153,base_index_1163,base_index_1171,base_index_1181,base_index_1187,base_index_1193,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin12 {c : ℕ} (pc : c.Prime) (lo : 1200 ≤ c) (hi : c ≤ 1299) : baseIndex c :=
  inBin baseIndex 1200 1299 [1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_1201,base_index_1213,base_index_1217,base_index_1223,base_index_1229,base_index_1231,base_index_1237,base_index_1249,base_index_1259,base_index_1277,base_index_1279,base_index_1283,base_index_1289,base_index_1291,base_index_1297,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin13 {c : ℕ} (pc : c.Prime) (lo : 1300 ≤ c) (hi : c ≤ 1399) : baseIndex c :=
  inBin baseIndex 1300 1399 [1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_1301,base_index_1303,base_index_1307,base_index_1319,base_index_1321,base_index_1327,base_index_1361,base_index_1367,base_index_1373,base_index_1381,base_index_1399,by simp⟩) pc lo hi
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem baseIndexBin14 {c : ℕ} (pc : c.Prime) (lo : 1400 ≤ c) (hi : c ≤ 1450) : baseIndex c :=
  inBin baseIndex 1400 1450 [1409,1423,1427,1429,1433,1439,1447] (by decide +kernel) (by
    simp only [List.forall_mem_cons]
    exact ⟨base_index_1409,base_index_1423,base_index_1427,base_index_1429,base_index_1433,base_index_1439,base_index_1447,by simp⟩) pc lo hi
private theorem baseIndex_all {c : ℕ} (pc : c.Prime) (lo : 23 ≤ c) (hi : c ≤ 1450) : baseIndex c := by
  by_cases test99 : c ≤ 99
  · exact baseIndexBin0 pc (by omega) test99
  by_cases test199 : c ≤ 199
  · exact baseIndexBin1 pc (by omega) test199
  by_cases test299 : c ≤ 299
  · exact baseIndexBin2 pc (by omega) test299
  by_cases test399 : c ≤ 399
  · exact baseIndexBin3 pc (by omega) test399
  by_cases test499 : c ≤ 499
  · exact baseIndexBin4 pc (by omega) test499
  by_cases test599 : c ≤ 599
  · exact baseIndexBin5 pc (by omega) test599
  by_cases test699 : c ≤ 699
  · exact baseIndexBin6 pc (by omega) test699
  by_cases test799 : c ≤ 799
  · exact baseIndexBin7 pc (by omega) test799
  by_cases test899 : c ≤ 899
  · exact baseIndexBin8 pc (by omega) test899
  by_cases test999 : c ≤ 999
  · exact baseIndexBin9 pc (by omega) test999
  by_cases test1099 : c ≤ 1099
  · exact baseIndexBin10 pc (by omega) test1099
  by_cases test1199 : c ≤ 1199
  · exact baseIndexBin11 pc (by omega) test1199
  by_cases test1299 : c ≤ 1299
  · exact baseIndexBin12 pc (by omega) test1299
  by_cases test1399 : c ≤ 1399
  · exact baseIndexBin13 pc (by omega) test1399
  exact baseIndexBin14 pc (by omega) hi

/-- The two exponent indices of a Mersenne successor cannot both satisfy
the effective product bound when its prime power exponent is at least 23. -/
theorem bounded_mersenne_witness {p n b r : ℕ} (pb : b.Prime) (pr : r.Prime)
    (bo : 3 ≤ b) (ro : 23 ≤ r) (limit : (b-1)*r ≤ 2097152)
    (bp : p+1=2^b) (nr : n+1=p^r) : v_l 1 n ≠ 1 := by
  by_cases small : b ≤ 1450
  · have bound : r ≤ 2097152/(b-1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using limit)
    exact powerIndex_all pb bo small pr ro bound bp nr
  · have smallr : r ≤ 1450 := by
      by_contra! large
      have largeProduct : 1450*1451 ≤ (b-1)*r := Nat.mul_le_mul (by omega) (by omega)
      omega
    have bound : b-1 ≤ 2097152/r := (Nat.le_div_iff_mul_le (by omega)).mpr limit
    exact baseIndex_all pr ro smallr pb (by omega) (by omega) bp nr


private theorem lower_indices {b r n p : ℕ} (pb : b.Prime) (small : b ≤ 22)
    (lo : 3 ≤ b) (ro : r=17 ∨ r=19) (bp : p+1=2^b) (nr : n+1=p^r) : v_l 1 n ≠ 1 := by
  have bb : b ∈ ([3,5,7,11,13,17,19] : List ℕ) := by
    have catalog : ∀ j : Fin 23, j.val.Prime → 3 ≤ j.val → j.val ∈ ([3,5,7,11,13,17,19] : List ℕ) := by
      decide +kernel
    exact catalog ⟨b,by omega⟩ pb lo
  have cert : ∃ m q s : ℕ, valid true r 3 m b q s = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at bb
    rcases ro with rfl|rfl <;> rcases bb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨35,71,127,by decide +kernel⟩
    · exact ⟨60,41,61,by decide +kernel⟩
    · exact ⟨20,5,11,by decide +kernel⟩
    · exact ⟨11,23,89,by decide +kernel⟩
    · exact ⟨161,47,127,by decide +kernel⟩
    · exact ⟨9,7,73,by decide +kernel⟩
    · exact ⟨10,11,31,by decide +kernel⟩
    · exact ⟨36,19,109,by decide +kernel⟩
    · exact ⟨66,7,67,by decide +kernel⟩
    · exact ⟨88,17,23,by decide +kernel⟩
    · exact ⟨11,23,89,by decide +kernel⟩
    · exact ⟨55,23,31,by decide +kernel⟩
    · exact ⟨72,73,433,by decide +kernel⟩
    · exact ⟨10,11,31,by decide +kernel⟩

  obtain ⟨m,q,s,pass⟩ := cert
  exact valid_sound pass pb lo bp nr (Nat.ModEq.refl b)

/-- The effective product bound rules out every prime power exponent at
least seventeen in the Mersenne successor branch. -/
theorem bounded_mersenne_from_seventeen {p n b r : ℕ} (pb : b.Prime) (pr : r.Prime)
    (bo : 3 ≤ b) (ro : 17 ≤ r) (limit : (b-1)*r ≤ 2097152)
    (bp : p+1=2^b) (nr : n+1=p^r) : v_l 1 n ≠ 1 := by
  by_cases large : 23 ≤ r
  · exact bounded_mersenne_witness pb pr bo large limit bp nr
  have rt : r=17 ∨ r=19 := by
    have smallPrimes : ∀ j : Fin 23, 17 ≤ j.val → j.val.Prime → j.val=17 ∨ j.val=19 := by decide
    exact smallPrimes ⟨r,by omega⟩ ro pr
  by_cases small : b ≤ 22
  · exact lower_indices pb small bo rt bp nr
  have ub : b-1 ≤ 2097152/r := (Nat.le_div_iff_mul_le (by omega)).mpr limit
  rcases rt with rfl|rfl
  · exact base_index_17 pb (by omega) (by norm_num1 at ub; omega) bp nr
  · exact base_index_19 pb (by omega) (by norm_num1 at ub; omega) bp nr

end Erdos889.BoundedPair
namespace Erdos889.PowerPairs

open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem bounded_indices {n x b r : ℕ} (cap : n<2^(2^21)) (eq : n+1=x^r)
    (base : x+1=2^b) (hp : 0<b) : (b-1)*r≤2097152 := by
  have hi := Nat.succ_le_of_lt cap
  change n+1≤_ at hi
  rw [eq] at hi
  have two : 2^(b-1)≤x := by
    have e : b=b-1+1 := by omega
    rw [e,pow_succ] at base
    have := @Nat.one_le_two_pow (b-1)
    omega
  have le := (Nat.pow_le_pow_left two r).trans hi
  rw [←pow_mul] at le
  have result := (Nat.pow_le_pow_iff_right (n:=(b-1)*r) (m:=2^21) (by decide : 1<2)).mp le
  simpa only [show (2:ℕ)^21=2097152 by decide] using result

theorem high_powers_from_bounded_tests (minimum : ℕ) (lm : 5 ≤ minimum)
    (cap : ∀ {n : ℕ}, Erdos889.v_l 1 n=1 → n<2^(2^21))
    (checked : ∀ {n p b r : ℕ}, b.Prime → r.Prime → 3≤b → minimum≤r → (b-1)*r≤2097152 →
      p+1=2^b → n+1=p^r → Erdos889.v_l 1 n≠1)
    {n x r : ℕ} (hx : 1<x) (pr : r.Prime) (hr : minimum≤r) (eq : n+1=x^r) : Erdos889.v_l 1 n≠1 := by
  intro sol
  have big : 32≤x^r := (by decide : 32≤2^5).trans
    ((Nat.pow_le_pow_right (by decide : 0<2) (by omega : 5≤r)).trans
    (Nat.pow_le_pow_left (show 2≤x by omega) r))
  have ox : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro ex
    have dd : 2 ∣ x^r := (even_iff_two_dvd.mp ex).trans (dvd_pow_self x (by omega))
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  obtain ⟨b,base⟩ := odd_power_root_neighbor ox hx (pr.odd_of_ne_two (by omega)) (by omega) eq sol
  have pure := prime_power_succ (n:=n) (by omega) sol
  rw [eq,isPrimePow_pow_iff (by omega : r≠0)] at pure
  obtain ⟨p,e,pp,pe,he⟩ := (isPrimePow_nat_iff _).mp pure
  have op := pp.odd_of_ne_two (by
    rintro rfl
    have div := dvd_pow_self (2:ℕ) pe.ne'
    rw [he] at div
    exact (Nat.not_even_iff_odd.mpr ox) (even_iff_two_dvd.mpr div))
  have one := mersenne_power_exponent op pp.one_lt pe (he.symm ▸ base)
  rw [one,pow_one] at he
  subst x
  have b1 : 1<b := by by_contra! low; interval_cases b <;> norm_num at base <;> omega
  have eb : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (eb ▸ pp)).2
  by_cases small : b=2
  · rw [small] at base
    have ep : p=3 := by norm_num at base; omega
    rw [ep] at eq
    have greater := Nat.pow_le_pow_right (by decide : 0<3) (by omega : 5≤r)
    rcases (three_successor_solution (by omega) eq).mp sol with h|h|h|h <;> omega
  have idx := bounded_indices (cap sol) eq base (by omega)
  exact checked pb pr (by omega) hr idx base eq sol

/-- Complete list of higher-power successors once the modular prime-index certificate is supplied. -/
theorem higher_power_list_from_seventeen
    (high : ∀ {n x r : ℕ}, 1<x → r.Prime → 17≤r → n+1=x^r → Erdos889.v_l 1 n≠1)
    {n x e : ℕ} (hx : 1<x) (he : 3≤e) (eq : n+1=x^e) :
    Erdos889.v_l 1 n=1 ↔ n∈[7,15,26,80] := by
  have ep : 0<e := by omega
  have lower : 8≤x^e := (by decide : 8≤2^3).trans
    ((Nat.pow_le_pow_right (by decide : 0<2) he).trans (Nat.pow_le_pow_left hx e))
  constructor
  · intro sol
    rcases Nat.even_or_odd x with even|odd
    · have d : 2∣x^e := (even_iff_two_dvd.mp even).trans (dvd_pow_self x ep.ne')
      have on : Odd n := by rw [Nat.odd_iff]; omega
      rcases (odd_classification on).mp sol with h|h|h|h <;> simp only [List.mem_cons,List.not_mem_nil,or_false] <;> omega
    by_cases four : 4∣e
    · obtain ⟨k,hk⟩ := four
      have kp : 0<k := by omega
      let y := x^k
      have ly : 1<y := one_lt_pow' hx kp.ne'
      have oy : Odd y := odd.pow
      have shape : n+1=y^4 := by rw [eq,hk,Nat.mul_comm,pow_mul]
      by_cases large : 3<y
      · obtain ⟨q,s,pq,ps,ne,hq,hs,dq,ds⟩ := fourth_power_witness oy large
        have off : n+5=y^4+4 := by omega
        exact (two_primes (k:=5) (by decide) pq ps ne hq hs (off ▸ dq) (off ▸ ds) sol).elim
      · have yy : y=3 := by obtain ⟨i,hi⟩ := oy; omega
        rw [yy] at shape
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        omega
    obtain ⟨q,pq,dq,lq⟩ : ∃ q : ℕ, q.Prime ∧ q∣e ∧ 2<q := by
      by_contra! only
      have powr : e=2^e.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd ep.ne' (by
        intro q pq dq
        have := only q pq dq
        have := pq.two_le
        omega)
      have two : 2≤e.primeFactorsList.length := by
        by_contra! low
        have cap := Nat.pow_le_pow_right (by decide : 0<2) (show e.primeFactorsList.length≤1 by omega)
        omega
      exact four (powr ▸ pow_dvd_pow 2 two)
    obtain ⟨k,hk⟩ := dq
    have kp : 0<k := by
      by_contra! low
      have zero : k=0 := by omega
      rw [zero,mul_zero] at hk
      omega
    let y := x^k
    have ly : 1<y := one_lt_pow' hx kp.ne'
    have shape : n+1=y^q := by rw [eq,hk,Nat.mul_comm,pow_mul]
    by_cases three : q=3
    · subst q
      have which := (cube_classification (odd.pow (n:=k)) ly shape).mp sol
      simp [which]
    by_cases bigq : 17≤q
    · exact (high ly pq bigq shape sol).elim
    · have small : q=5 ∨ q=7 ∨ q=11 ∨ q=13 := by
        interval_cases q <;> first | omega | norm_num at pq
      exact (fifth_seventh_eleventh_thirteenth_exclusion ly small shape sol).elim
  · intro mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

/-- Above 330 only prime or prime-square successors survive the higher-power classification. -/
theorem prime_or_prime_square_from_seventeen
    (high : ∀ {n x r : ℕ}, 1<x → r.Prime → 17≤r → n+1=x^r → Erdos889.v_l 1 n≠1)
    {n : ℕ} (big : 330<n) (sol : Erdos889.v_l 1 n=1) :
    (n+1).Prime ∨ ∃ p : ℕ, p.Prime ∧ n+1=p^2 := by
  obtain ⟨p,e,pp,ep,h⟩ := (isPrimePow_nat_iff _).mp (prime_power_succ (by omega) sol)
  by_cases large : 3≤e
  · have mem := (higher_power_list_from_seventeen high pp.one_lt large h.symm).mp sol
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
  · interval_cases e
    · left
      simpa only [←h,pow_one] using pp
    · exact Or.inr ⟨p,pp,h.symm⟩

end Erdos889.PowerPairs

namespace Erdos889.PowerPairs

/-- Every prime exponent from seventeen onward supplies an obstruction at the predecessor. -/
theorem excluded_high_power {n x r : ℕ} (hx : 1<x) (pr : r.Prime) (hr : 17≤r)
    (eq : n+1=x^r) : v_l 1 n ≠ 1 :=
  high_powers_from_bounded_tests 17 (by decide) Erdos889.effective_binary_cutoff
    Erdos889.BoundedPair.bounded_mersenne_from_seventeen hx pr hr eq

/-- Exact list of all solutions whose successor is a power with exponent at least three. -/
theorem higher_power_successors {n x e : ℕ} (hx : 1<x) (he : 3≤e) (eq : n+1=x^e) :
    v_l 1 n = 1 ↔ n ∈ [7,15,26,80] :=
  higher_power_list_from_seventeen excluded_high_power hx he eq

/-- Two distinct fresh primes exist at some positive shift of every such predecessor. -/
theorem higher_power_witness {x r : ℕ} (hx : 1<x) (pr : r.Prime) (hr : 17≤r) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ x^r+d ∧ s ∣ x^r+d := by
  by_contra none
  have big : 1 < x^r := Nat.one_lt_pow (by omega) hx
  exact excluded_high_power hx pr hr (Nat.sub_add_cancel (by omega : 1 ≤ x^r))
    (Erdos889.Missing.predecessor_solution_of_missing big none)

theorem zero_threshold : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H3 := by
  refine ⟨0,?_⟩
  intro p r _ _ hp pr hr _ _ _
  exact higher_power_witness (by omega) pr hr

end Erdos889.PowerPairs

theorem Erdos889.PowerPairs.large_successor {n : ℕ} (big : 330<n) (sol : Erdos889.v_l 1 n=1) :
    (n+1).Prime ∨ ∃ p : ℕ, p.Prime ∧ n+1=p^2 :=
  prime_or_prime_square_from_seventeen excluded_high_power big sol


namespace Erdos889.CompletedReduction
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem witness_above_bound {N : ℕ} (high : 2^(2^21)<N) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1<q ∧ d+1<s ∧ q∣N+d ∧ s∣N+d := by
  by_contra none
  have big : 1<N := lt_of_le_of_lt (@Nat.one_le_two_pow (2^21)) high
  have sol := Erdos889.Missing.predecessor_solution_of_missing big none
  exact (Nat.not_lt_of_ge (Nat.le_sub_one_of_lt high)) (Erdos889.effective_binary_cutoff sol)

theorem prime_step : H1 := by
  refine ⟨2^(2^21),?_⟩
  intro p _ _ high _ _
  exact witness_above_bound high

theorem square_step : H2 := by
  refine ⟨2^(2^21),?_⟩
  intro p _ _ high _ _
  exact witness_above_bound high

theorem higher_power_step : H3 := Erdos889.PowerPairs.zero_threshold

theorem finite_all : type_of% @Erdos889.erdos_889.variants.v1_eq_1_finite :=
  OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.main prime_step square_step higher_power_step

end Erdos889.CompletedReduction
theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H3 :=
  Erdos889.PowerPairs.zero_threshold
