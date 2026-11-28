import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib

/-! Discharge the prime-successor step of the merged reduction using the effective bound. -/
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


namespace Erdos889.PellValuation

-- BEGIN PELL VALUATION
private theorem pell_expansion_remainder {d : ℤ} (z : Pell.Solution₁ d) (n : ℕ) :
    ∃ L K : ℤ, (z^(n+1)).x=z.x^(n+1)+d*L ∧
      (z^(n+1)).y=z.y*((n+1 : ℕ)*(z.x^n)+d*K) := by
  induction n with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨L,K,hx,hy⟩ := ih
    refine ⟨L*z.x+(z^(n+1)).y*z.y,L+K*z.x,?_,?_⟩
    · change (z^(n+1)*z).x=z.x^(n+1+1)+d*(L*z.x+(z^(n+1)).y*z.y)
      rw [Pell.Solution₁.x_mul,hx,pow_succ z.x (n+1)]
      ring
    · change (z^(n+1)*z).y=z.y*((n+1+1:ℕ)*z.x^(n+1)+d*(L+K*z.x))
      rw [Pell.Solution₁.y_mul,hx,hy,pow_succ z.x n]
      push_cast
      ring

private theorem pell_prime_multiplier {D l q : ℕ} (z : Pell.Solution₁ (D:ℤ))
    (pl : l.Prime) (pq : q.Prime) (dq : q^2∣D) :
    ∃ k : ℕ, (z^l).y.natAbs=z.y.natAbs*k ∧ k≠0 ∧ k.factorization q=l.factorization q := by
  let _ : Fact q.Prime := ⟨pq⟩
  obtain ⟨_,K,_,hy⟩ := pell_expansion_remainder z (l-1)
  rw [Nat.sub_add_cancel pl.one_le] at hy
  obtain ⟨h,dh⟩ := dq
  have dint : (D:ℤ)=(q:ℤ)^2*h := by exact_mod_cast dh
  have zd : (D:ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr (dh ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by decide : (2:ℕ)≠0)) h)
  have xz : (z.x:ZMod q)≠0 := by
    intro zero
    have f := congrArg (fun v:ℤ => (v:ZMod q)) z.prop
    push_cast at f
    rw [zd,zero,zero_pow two_ne_zero,zero_mul,sub_zero] at f
    exact zero_ne_one f
  let a := z.x^(l-1)
  have an : (a:ZMod q)≠0 := by dsimp [a]; push_cast; exact pow_ne_zero _ xz
  have no {c : ℤ} (hc : (c:ZMod q)≠0) : ¬q∣c.natAbs :=
    fun dd => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr dd))
  by_cases same : l=q
  · subst l
    let c := a+(q:ℤ)*h*K
    have cn : ¬q∣c.natAbs := no (by simpa [c] using an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    have yq : (z^q).y=z.y*((q:ℤ)*c) := by
      rw [hy]
      dsimp only [a,c]
      linear_combination z.y*K*dint
    refine ⟨q*c.natAbs,?_,mul_ne_zero pq.ne_zero nc,?_⟩
    · rw [yq]; simp only [Int.natAbs_mul,Int.natAbs_natCast]
    · rw [Nat.factorization_mul pq.ne_zero nc,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd cn,add_zero]
  · have nl : ¬q∣l := fun h => same ((Nat.prime_dvd_prime_iff_eq pq pl).mp h).symm
    have lv : (l:ZMod q)≠0 := fun h => nl ((ZMod.natCast_eq_zero_iff _ _).mp h)
    let c := (l:ℤ)*a+(D:ℤ)*K
    have cn : ¬q∣c.natAbs := no (by
      dsimp only [c]
      push_cast
      rw [zd,zero_mul,add_zero]
      exact mul_ne_zero lv an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    refine ⟨c.natAbs,?_,nc,?_⟩
    · rw [hy,Int.natAbs_mul]
    · rw [Nat.factorization_eq_zero_of_not_dvd cn,Nat.factorization_eq_zero_of_not_dvd nl]

/-- At a prime whose square divides D, the imaginary coordinate of a Pell power gains exactly the exponent's valuation. -/
theorem pell_factorization_y_pow {D q n : ℕ} (eps : Pell.Solution₁ (D : ℤ))
    (pq : q.Prime) (dq : q^2∣D) (hn : 0<n) :
    (eps^n).y.natAbs.factorization q = (n*eps.y.natAbs).factorization q := by
  by_cases hzero : eps.y=0
  · obtain ⟨_,_,_,hy⟩ := pell_expansion_remainder eps (n-1)
    rw [Nat.sub_add_cancel hn,hzero,zero_mul] at hy
    simp [hy,hzero]
  have base : eps.y.natAbs≠0 := fun h => hzero (Int.natAbs_eq_zero.mp h)
  have all : ∀ j : ℕ, j≠0 → (eps^j).y.natAbs≠0 ∧
      (eps^j).y.natAbs.factorization q=(j*eps.y.natAbs).factorization q := by
    apply induction_on_primes
    · simp
    · simp [base]
    · intro l a pl ih nz
      have ap : a≠0 := fun e => nz (by rw [e,mul_zero])
      obtain ⟨nonzero,ihv⟩ := ih ap
      obtain ⟨k,mult,kpos,kv⟩ := pell_prime_multiplier (eps^a) pl pq dq
      have e : eps^(l*a)=(eps^a)^l := by rw [←pow_mul,Nat.mul_comm]
      rw [e,mult]
      refine ⟨mul_ne_zero nonzero kpos,?_⟩
      rw [Nat.factorization_mul nonzero kpos,Finsupp.add_apply,kv,ihv,Nat.mul_assoc,
        Nat.factorization_mul pl.ne_zero (mul_ne_zero ap base),Finsupp.add_apply,Nat.add_comm]
  exact (all n hn.ne').2
-- END PELL VALUATION

end Erdos889.PellValuation

namespace Erdos889.PellValuation

private theorem y_dvd_y_pow {D : ℤ} (z : Pell.Solution₁ D) (n : ℕ) : z.y ∣ (z^n).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Pell.Solution₁.y_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

/-- An imaginary-coordinate zero modulo q at any fixed index h bounds the
q-adic valuation at every positive index by that of n times this coordinate. -/
theorem pell_factorization_y_le {D q n h : ℕ} (eps : Pell.Solution₁ (D:ℤ)) (pq : q.Prime)
    (hn : 0<n) (hp : 0<h) (hx : 0<eps.x) (hy : 0<eps.y)
    (hit : q∣(eps^h).y.natAbs) :
    ((eps^n).y.natAbs).factorization q ≤ (n*(eps^h).y.natAbs).factorization q := by
  let w := eps^h
  let M := w.y.natAbs
  have pos : 0<w.y := by
    obtain ⟨k,ek⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    change 0<(eps^h).y
    rw [ek]
    exact Pell.Solution₁.y_pow_succ_pos hx hy k
  have mp : 0<M := Int.natAbs_pos.mpr pos.ne'
  have castM : (M:ℤ)=w.y := Int.natAbs_of_nonneg pos.le
  let D' := D*M^2
  let u : Pell.Solution₁ (D':ℤ) := Pell.Solution₁.mk w.x 1 (by
    dsimp only [D']
    push_cast
    rw [castM]
    simpa only [one_pow,mul_one] using w.prop)
  have lift (i : ℕ) : (w^i).x=(u^i).x ∧ (w^i).y=w.y*(u^i).y := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ,pow_succ]
      simp only [Pell.Solution₁.x_mul,Pell.Solution₁.y_mul,ih.1,ih.2]
      change _ = (u^i).x*w.x+(D':ℤ)*((u^i).y*1) ∧ _ = w.y*((u^i).x*1+(u^i).y*w.x)
      dsimp only [D']
      push_cast
      constructor
      · linear_combination -(D:ℤ)*(u^i).y*(w.y+(M:ℤ))*castM
      · ring
  have imag : ((eps^h)^n).y.natAbs=M*(u^n).y.natAbs := by rw [(lift n).2,Int.natAbs_mul]
  have md : q^2∣D' := dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hit 2) D
  have lte := pell_factorization_y_pow u pq md hn
  have un : (u^n).y.natAbs≠0 := by
    obtain ⟨k,ek⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have posU : 0<u.x := Pell.Solution₁.x_pow_pos hx h
    exact Int.natAbs_ne_zero.mpr (ek ▸ (Pell.Solution₁.y_pow_succ_pos posU (by change (0:ℤ)<1; decide) k).ne')
  have big : (((eps^h)^n).y).natAbs ≠ 0 := by rw [imag]; exact mul_ne_zero mp.ne' un
  have dv : (eps^n).y.natAbs∣((eps^h)^n).y.natAbs := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    exact Int.natAbs_dvd_natAbs.mpr (y_dvd_y_pow (eps^n) h)
  have ns : 0<(eps^n).y := by
    obtain ⟨k,ek⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [ek]
    exact Pell.Solution₁.y_pow_succ_pos hx hy k
  have le := (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr ns.ne') big).mpr dv q
  rw [imag,Nat.factorization_mul mp.ne' un,Finsupp.add_apply,lte] at le
  change _ ≤ _ + (n*1).factorization q at le
  rw [Nat.factorization_mul hn.ne' mp.ne',Finsupp.add_apply]
  simpa only [mul_one,Nat.add_comm] using le

end Erdos889.PellValuation

namespace Erdos889.SevenSmooth

private theorem pell_growth {D : ℤ} (eps : Pell.Solution₁ D) (hx : 1 < eps.x)
    (hy : 0 < eps.y) (n : ℕ) : (2:ℤ)^n*eps.y ≤ (eps^(n+1)).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have sx := Pell.Solution₁.x_pow_pos (show 0 < eps.x by omega) (n+1)
    have sy := Pell.Solution₁.y_pow_succ_pos (show 0 < eps.x by omega) hy n
    have grow := mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ eps.x by omega) sy.le
    rw [pow_succ, show n+1+1=(n+1)+1 by rfl, pow_succ eps (n+1),Pell.Solution₁.y_mul]
    nlinarith [mul_pos sx hy]


private structure Row where
  d : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq

private def rows : List Row := [
  ⟨2,3,2⟩,⟨3,2,1⟩,⟨5,9,4⟩,⟨6,5,2⟩,⟨7,8,3⟩,⟨10,19,6⟩,⟨14,15,4⟩,⟨15,4,1⟩,
  ⟨21,55,12⟩,⟨30,11,2⟩,⟨35,6,1⟩,⟨42,13,2⟩,⟨70,251,30⟩,⟨105,41,4⟩,⟨210,29,2⟩]

private def factors : List (ℕ × ℕ) := [(2,4),(3,4),(5,2),(7,2)]

private def coord (r : Row) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | k+1 =>
    let v := coord r k
    (v.1*r.a+r.d*v.2*r.b,v.1*r.b+v.2*r.a)

private theorem row_ok : ∀ r ∈ rows, 1<r.a ∧ 0<r.b ∧ r.a^2=r.d*r.b^2+1 := by decide +kernel

private theorem row_min : ∀ r ∈ rows, ∀ a ∈ List.range (r.a+1), ∀ b ∈ List.range (r.b+1),
    1<a → 0<b → a^2=r.d*b^2+1 → a=r.a ∧ b=r.b := by decide +kernel

private theorem row_hit : ∀ r ∈ rows, ∀ v ∈ factors, ∃ h : Fin 9, 0 < h.val ∧
    v.1∣(coord r h.val).2 ∧ ¬v.1^(v.2+1)∣(coord r h.val).2 := by decide +kernel

private theorem index_check : ∀ r ∈ rows, ∀ k : Fin 33, (coord r k.val).2∣k.val*1587600 →
    (coord r k.val).1≤8749 := by decide +kernel

private theorem row_unit {r : Row} (hr : r∈rows) :
    ∃ g : Pell.Solution₁ (r.d:ℤ), Pell.IsFundamental g ∧ g.x=(r.a:ℤ) ∧ g.y=(r.b:ℤ) := by
  obtain ⟨ha,hb,eq⟩ := row_ok r hr
  have e : (r.a:ℤ)^2=(r.d:ℤ)*(r.b:ℤ)^2+1 := by exact_mod_cast eq
  let u : Pell.Solution₁ (r.d:ℤ) := Pell.Solution₁.mk r.a r.b (by linarith)
  have ux : 1<u.x := by change 1<(r.a:ℤ); exact_mod_cast ha
  have uy : 0<u.y := by change 0<(r.b:ℤ); exact_mod_cast hb
  obtain ⟨g,hg⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (Pell.Solution₁.d_pos_of_one_lt_x ux) (Pell.Solution₁.d_nonsquare_of_one_lt_x ux)
  have gx := hg.1
  have gy := hg.2.1
  have leA := hg.x_le_x ux
  have leB := hg.y_le_y ux uy
  change g.x≤(r.a:ℤ) at leA
  change g.y≤(r.b:ℤ) at leB
  have norm : g.x.toNat^2=r.d*g.y.toNat^2+1 := by
    zify
    rw [Int.toNat_of_nonneg (by omega),Int.toNat_of_nonneg (by omega)]
    linarith [g.prop]
  have hit := row_min r hr g.x.toNat (List.mem_range.mpr (by omega)) g.y.toNat
    (List.mem_range.mpr (by omega)) (by omega) (by omega) norm
  exact ⟨g,hg,by omega,by omega⟩

private theorem coord_eq {r : Row} (g : Pell.Solution₁ (r.d:ℤ)) (ga : g.x=(r.a:ℤ))
    (gb : g.y=(r.b:ℤ)) (i : ℕ) :
    (g^i).x=((coord r i).1:ℤ) ∧ (g^i).y=((coord r i).2:ℤ) := by
  induction i with
  | zero => simp [coord]
  | succ i ih =>
    rw [pow_succ]
    simp only [Pell.Solution₁.x_mul,Pell.Solution₁.y_mul,ih.1,ih.2,ga,gb,coord,Nat.cast_add,Nat.cast_mul]
    simp [mul_assoc]

private theorem smooth_y_dvd {r : Row} (hr : r∈rows) (g : Pell.Solution₁ (r.d:ℤ))
    (hg : Pell.IsFundamental g) (ga : g.x=(r.a:ℤ)) (gb : g.y=(r.b:ℤ)) (i : ℕ) (hi : 0 < i)
    (smooth : ∀ p : ℕ, p.Prime → p∣(g^i).y.natAbs → p≤7) : (g^i).y.natAbs∣i*1587600 := by
  have nonzero (k : ℕ) (hk : 0<k) : (g^k).y.natAbs≠0 := by
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact Int.natAbs_ne_zero.mpr (ht ▸ (Pell.Solution₁.y_pow_succ_pos hg.x_pos hg.2.1 t).ne')
  apply (Nat.factorization_le_iff_dvd (nonzero i hi) (Nat.mul_pos hi (by decide)).ne').mp
  intro p
  by_cases yes : p.Prime ∧ p∣(g^i).y.natAbs
  · obtain ⟨pp,dp⟩ := yes
    have small := smooth p pp dp
    have pick : ∀ j : Fin 8, j.val.Prime → j.val ∈ factors.map Prod.fst := by decide +kernel
    obtain ⟨⟨q,e⟩,row,same⟩ := List.mem_map.mp (pick ⟨p,by omega⟩ pp)
    change q=p at same
    subst q
    obtain ⟨h,hh,dv,nd⟩ := row_hit r hr (p,e) row
    have Y : (g^h.val).y.natAbs=(coord r h.val).2 := by rw [(coord_eq g ga gb h.val).2]; rfl
    change p ∣ (coord r h.val).2 at dv
    change ¬p^(e+1)∣(coord r h.val).2 at nd
    rw [←Y] at dv nd
    have le := Erdos889.PellValuation.pell_factorization_y_le g pp hi hh hg.x_pos hg.2.1 dv
    have ee : ((g^h.val).y.natAbs).factorization p ≤ e := by
      rw [pp.pow_dvd_iff_le_factorization (nonzero h.val hh)] at nd
      omega
    have power : ∀ v ∈ factors, v.1^v.2∣1587600 := by decide +kernel
    have EC := (pp.pow_dvd_iff_le_factorization (by decide : (1587600:ℕ)≠0)).mp (power (p,e) row)
    rw [Nat.factorization_mul hi.ne' (nonzero h.val hh),Finsupp.add_apply] at le
    rw [Nat.factorization_mul hi.ne' (by decide),Finsupp.add_apply]
    omega
  · by_cases pp : p.Prime
    · have nd : ¬p∣(g^i).y.natAbs := fun d => yes ⟨pp,d⟩
      simp [Nat.factorization_eq_zero_of_not_dvd nd]
    · simp [Nat.factorization_eq_zero_of_not_prime _ pp]

private theorem linear_exp (k : ℕ) : 1587600*(k+33) < 2^(k+32) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k+1+32=(k+32)+1 by omega,pow_succ]
    omega

private theorem seven_pell {r : Row} (hr : r∈rows) {x y : ℕ} (hx : 1 < x) (hy : 0 < y)
    (eq : x^2=r.d*y^2+1) (smooth : ∀ p : ℕ, p.Prime → p∣y → p≤7) : x≤8749 := by
  obtain ⟨g,hg,ga,gb⟩ := row_unit hr
  have e : (x:ℤ)^2=(r.d:ℤ)*(y:ℤ)^2+1 := by exact_mod_cast eq
  let w : Pell.Solution₁ (r.d:ℤ) := Pell.Solution₁.mk x y (by linarith)
  obtain ⟨i,hi⟩ := hg.eq_pow_of_nonneg (a:=w) (by change 0<(x:ℤ); omega) (by change 0≤(y:ℤ); positivity)
  have xx : (g^i).x=(x:ℤ) := by rw [←hi]; rfl
  have yy : (g^i).y=(y:ℤ) := by rw [←hi]; rfl
  have yi : (g^i).y.natAbs=y := by rw [yy]; rfl
  have ip : 0 < i := by
    by_contra! low
    have zi : i=0 := by omega
    rw [zi,pow_zero,Pell.Solution₁.y_one] at yy
    omega
  have dv := smooth_y_dvd hr g hg ga gb i ip (by rwa [yi])
  have le := Nat.le_of_dvd (Nat.mul_pos ip (by decide)) dv
  rw [yi] at le
  have i32 : i≤32 := by
    by_contra! high
    obtain ⟨k,ek⟩ := Nat.exists_eq_add_of_le (show 33 ≤ i by omega)
    have growth := pell_growth g hg.1 hg.2.1 (k+32)
    rw [show k+32+1=i by omega,yy,gb] at growth
    have gN : 2^(k+32)*r.b≤y := by exact_mod_cast growth
    have bb := (row_ok r hr).2.1
    have small := linear_exp k
    have lower := Nat.le_mul_of_pos_right (2^(k+32)) bb
    rw [Nat.mul_comm i 1587600] at le
    omega
  have coords := coord_eq g ga gb i
  have xc : (coord r i).1=x := by omega
  have yc : (coord r i).2=(g^i).y.natAbs := by rw [coords.2]; rfl
  have bound := index_check r hr ⟨i,by omega⟩ (yc ▸ dv)
  simpa only [xc] using bound


/-- The smaller member of a pair of consecutive 7-smooth positive integers
is at most 4374. The endpoint is attained by 4374 and 4375. -/
theorem consecutive_smooth_seven (a : ℕ) (smooth : ∀ p : ℕ, p.Prime → p∣a*(a+1) → p≤7) :
    a≤4374 := by
  by_cases az : a=0
  · omega
  have ap : 0 < a := Nat.pos_of_ne_zero az
  obtain ⟨D,z,dp,zp,fac,free⟩ := Nat.sq_mul_squarefree_of_pos (Nat.mul_pos ap (by omega : 0<a+1))
  have divD : D∣a*(a+1) := by rw [←fac]; exact dvd_mul_left _ _
  have d210 : D∣210 := by
    rw [←Nat.prod_primeFactors_of_squarefree free,Nat.prod_primeFactors_dvd_iff (by decide)]
    intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    have small := smooth p pp ((Nat.dvd_of_mem_primeFactors hp).trans divD)
    have cert : ∀ k : Fin 8, k.val.Prime → k.val∣210 := by decide +kernel
    exact pp.mem_primeFactors (cert ⟨p,by omega⟩ pp) (by decide)
  have pell : (2*a+1)^2=D*(2*z)^2+1 := by nlinarith [fac]
  have dn : D≠1 := by
    intro one
    rw [one,one_mul] at pell
    have a1 : 2*z<2*a+1 := by nlinarith
    have a2 : 2*z+1≤2*a+1 := by omega
    have bad := Nat.pow_le_pow_left a2 2
    nlinarith
  have good : ∀ i : Fin 211, i.val∣210 → i.val≠1 → i.val∈rows.map Row.d := by decide +kernel
  have cap := Nat.le_of_dvd (by decide : 0<210) d210
  obtain ⟨r,hr,same⟩ := List.mem_map.mp (good ⟨D,by omega⟩ d210 dn)
  change r.d=D at same
  have sup (p : ℕ) (pp : p.Prime) (dv : p∣2*z) : p≤7 := by
    rcases pp.dvd_mul.mp dv with two|hit
    · have := Nat.le_of_dvd (by decide : 0<2) two; omega
    · apply smooth p pp
      rw [←fac]
      exact dvd_mul_of_dvd_left (hit.trans (dvd_pow_self z (by decide : (2:ℕ)≠0))) D
  have result := seven_pell hr (x:=2*a+1) (y:=2*z) (by omega) (by omega)
    (by rwa [same]) sup
  omega


end Erdos889.SevenSmooth


/- First-five-offset exclusions for the prime-successor branch of Erdős 889. -/


/- Exclusions for offsets at the first multiple of seven. -/
namespace Erdos889.PrimeSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
private theorem large_neighbour {z : ℕ} (large : 4375 < z) (smooth : ∀ p : ℕ, p.Prime → p∣z → p≤7) :
    (∃ p : ℕ, p.Prime ∧ 7<p ∧ p∣z-1) ∧ (∃ p : ℕ, p.Prime ∧ 7<p ∧ p∣z+1) := by
  constructor
  · by_contra missing
    have bound := Erdos889.SevenSmooth.consecutive_smooth_seven (z-1) (by
      intro p pp d
      rcases pp.dvd_mul.mp d with dv|dv
      · by_contra! high
        exact missing ⟨p,pp,high,dv⟩
      · exact smooth p pp (by rwa [show z-1+1=z by omega] at dv))
    omega
  · by_contra missing
    have bound := Erdos889.SevenSmooth.consecutive_smooth_seven z (by
      intro p pp d
      rcases pp.dvd_mul.mp d with dv|dv
      · exact smooth p pp dv
      · by_contra! high
        exact missing ⟨p,pp,high,dv⟩)
    omega
private theorem two_factor_support {m p q : ℕ} (mp : 0 < m) (pp : p.Prime)
    (pool : ∀ r : ℕ, r.Prime → r∣m → r=p ∨ r=q) :
    ∃ a b : ℕ, m=p^a*q^b := by
  let k := m/p^m.factorization p
  have pos : 0<k := Nat.ordCompl_pos p mp.ne'
  have no : ¬p∣k := Nat.not_dvd_ordCompl pp mp.ne'
  have form : p^m.factorization p*k=m := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : k=q^k.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd pos.ne' (by
    intro r pr dr
    exact (pool r pr (dr.trans (Nat.ordCompl_dvd m p))).resolve_left (by rintro rfl; exact no dr))
  exact ⟨_,_,by rw [←pure]; exact form.symm⟩


theorem first_multiple_shape {n j x : ℕ} (jpos : 0<j) (jl : j<7) (pos : 0<n) (px : x.Prime)
    (all : ∀ p : Fin 7, p.val.Prime → p.val≤j → p.val∣n+j → p.val=x)
    (seven : 7∣n+j) (sol : v_l 1 n=1) : ∃ a b : ℕ, n+j=x^a*7^b := by
  apply two_factor_support (by omega) px
  intro p pp dp
  by_cases low : p ≤ j
  · exact Or.inl (all ⟨p,by omega⟩ pp low dp)
  · by_contra! bad
    exact two_primes jpos pp (by decide : Nat.Prime 7) bad.2 (by omega) jl dp seven sol

theorem no_four {n : ℕ} (big : 1000000000000<n) (thirty : 30∣n)
    (seven : 7∣n+4) (sol : v_l 1 n=1) : False := by
  obtain ⟨a,b,eq⟩ := first_multiple_shape (j:=4) (by decide) (by decide) (by omega)
    (by decide : Nat.Prime 2) (by
      intro p pp low d
      have t : ∀ q : Fin 7, q.val.Prime → q.val≤4 → q.val=2 ∨ q.val=3 := by decide
      exact (t p pp low).resolve_right (by intro e; rw [e] at d; omega)) seven sol
  have m3 := congrArg (fun z : ℕ => z%3) eq
  have m5 := congrArg (fun z : ℕ => z%5) eq
  have cycle {x t m k : ℕ} (h : Nat.ModEq m (x^t) 1) : Nat.ModEq m (x^k) (x^(k%t)) := by
    calc
      x^k=x^(k%t)*(x^t)^(k/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
      _ ≡ x^(k%t)*1^(k/t) [MOD m] := (h.pow _).mul_left _
      _ = _ := by simp
  have e3 := @cycle 2 2 3 a (by decide)
  have f3 := @cycle 7 1 3 b (by decide)
  have h3 := e3.mul f3
  change (2^a*7^b)%3=(2^(a%2)*7^(b%1))%3 at h3
  have e5 := @cycle 2 4 5 a (by decide)
  have f5 := @cycle 7 4 5 b (by decide)
  have h5 := e5.mul f5
  change (2^a*7^b)%5=(2^(a%4)*7^(b%4))%5 at h5
  simp only [Nat.mod_one,pow_zero,mul_one] at h3
  have tab : ∀ i j : Fin 4, 2^(i.val%2)%3=1 → (2^i.val*7^j.val)%5=4 →
      i.val%2=0 ∧ j.val%2=0 := by decide +kernel
  have ev := tab ⟨a%4,by omega⟩ ⟨b%4,by omega⟩
  change 2^(a%4%2)%3=1 → (2^(a%4)*7^(b%4))%5=4 → a%4%2=0 ∧ b%4%2=0 at ev
  rw [Nat.mod_mod_of_dvd a (by decide : 2∣4),Nat.mod_mod_of_dvd b (by decide : 2∣4)] at ev
  change (n+4)%3=(2^a*7^b)%3 at m3
  change (n+4)%5=(2^a*7^b)%5 at m5
  obtain ⟨evenA,evenB⟩ := ev (by omega) (by omega)
  let z := 2^(a/2)*7^(b/2)
  have sq : n+4=z^2 := by
    dsimp only [z]; rw [mul_pow,←pow_mul,←pow_mul,show a/2*2=a by omega,show b/2*2=b by omega]; exact eq
  have high : 4375<z := by by_contra! low; have := Nat.pow_le_pow_left low 2; omega
  have smooth (p : ℕ) (pr : p.Prime) (dv : p∣z) : p≤7 := by
    rcases pr.dvd_mul.mp dv with e|e
    · exact (Nat.le_of_dvd (by decide : 0<2) (pr.dvd_of_dvd_pow e)).trans (by decide)
    · exact Nat.le_of_dvd (by decide : 0<7) (pr.dvd_of_dvd_pow e)
  obtain ⟨⟨p,pp,hp,dp⟩,⟨q,pq,hq,dq⟩⟩ := large_neighbour high smooth
  have ne : p≠q := by
    rintro rfl
    have dd : p∣2 := (Nat.dvd_add_iff_right dp).mpr (show p∣(z-1)+2 by rwa [show z-1+2=z+1 by omega])
    have := Nat.le_of_dvd (by decide : 0<2) dd
    omega
  have h : n+3=(z-1)*(z+1) := by
    have zz : z=(z-1)+1 := by omega
    nlinarith [congrArg (fun t : ℕ => t*z) zz]
  exact two_primes (by decide : 0<3) pp pq ne (by omega) (by omega)
    (h ▸ dvd_mul_of_dvd_left dp _) (h ▸ dvd_mul_of_dvd_right dq _) sol

theorem no_twelfth {n j z : ℕ} (hj : 0<j) (small : j≤6) (big : 1<z)
    (shape : n+j=j*z^12) (sol : v_l 1 n=1) : False := by
  let t := z^4
  let B := (t-1)^2+(t-1)+1
  have tlarge : 15<t := Nat.pow_le_pow_left big 4
  have Bpos : 1<B := by dsimp only [B]; omega
  have identity : B+t = t^2+1 := by
    have tz : t-1+1=t := by omega
    dsimp only [B]; nlinarith [congrArg (fun i : ℕ => i*(t-1)) tz,congrArg (fun i : ℕ => i*t) tz]
  have mul : (t+1)*B=z^12+1 := by
    have te : t^3=z^12 := by dsimp only [t]; rw [←pow_mul]
    rw [←te]; nlinarith [congrArg (fun w : ℕ => w*t) identity]
  have classifyA (p : ℕ) (pp : p.Prime) (low : p≤12) (dp : p∣t+1) : p=2 := by
    have tab : ∀ q : Fin 13, q.val.Prime → ∀ u : Fin q.val, (u.val^4+1)%q.val=0 → q.val=2 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    exact tab ⟨p,by omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp))
  obtain ⟨p,pp,hp,dp⟩ : ∃ p : ℕ, p.Prime ∧ 12<p ∧ p∣t+1 := by
    by_contra miss
    have pow2 := Nat.eq_prime_pow_of_unique_prime_dvd (show t+1≠0 by omega) (fun {p} pp dp =>
      classifyA p pp (by by_contra! hi; exact miss ⟨p,pp,hi,dp⟩) dp)
    let e := (t+1).primeFactorsList.length
    change t+1=2^e at pow2
    have ee : 2≤e := by by_contra! low; have := Nat.pow_le_pow_right (by decide : 0<2) (show e≤1 by omega); omega
    have dv : 4∣t+1 := pow2 ▸ pow_dvd_pow 2 ee
    have m := ((Nat.mod_modEq z 4).pow 4).add_right 1
    have bad := m.trans (Nat.modEq_zero_iff_dvd.mpr dv)
    have tab : ∀ i : Fin 4, (i.val^4+1)%4≠0 := by decide
    exact tab ⟨z%4,by omega⟩ bad
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show B≠1 by omega)
  have hq : 12<q := by
    by_contra! low
    have tab : ∀ q : Fin 13, q.val.Prime → ∀ u : Fin q.val, ¬Nat.ModEq q.val (u.val^4) (u.val^8+1) := by decide +kernel
    have m := (Nat.modEq_zero_iff_dvd.mpr dq).add_right t
    rw [identity,zero_add] at m
    have zt : t^2=z^8 := by dsimp only [t]; rw [←pow_mul]
    rw [zt] at m
    have du := Nat.mod_modEq z q
    exact tab ⟨q,by omega⟩ pq ⟨z%q,Nat.mod_lt _ pq.pos⟩ ((du.pow 4).trans (m.symm.trans ((du.pow 8).add_right 1).symm))
  have ne : p≠q := by
    rintro rfl
    have e : B+3*(t+1)=(t+1)^2+3 := by nlinarith
    have left := dvd_add dq (dvd_mul_of_dvd_right dp 3)
    rw [e] at left
    have dd := (Nat.dvd_add_iff_right (dp.trans (dvd_pow_self _ (by decide : 2≠0)))).mpr left
    have := Nat.le_of_dvd (by decide : 0<3) dd; omega
  have h : n+(j+j)=j*((t+1)*B) := by rw [mul,Nat.mul_add,mul_one]; omega
  exact two_primes (by omega : 0<j+j) pp pq ne (by omega) (by omega)
    (h ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _) (h ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _) sol

end Erdos889.PrimeSeven





/- Modular exclusions for a offset 2 supported on 2 and seven. -/
namespace Erdos889.PrimeSevenTwo

private structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

private abbrev Stable (m : ℕ) := 0 < m ∧ 2^241%m=2%m ∧ 7^241%m=7%m

private theorem cycle {p m : ℕ} (one : Nat.ModEq m (p^241) p) (e : ℕ) (he : 0<e) :
    Nat.ModEq m (p^e) (p^(240+e%240)) := by
  have step (v : ℕ) (hv : 0<v) : Nat.ModEq m (p^(v+240)) (p^v) := by
    have one' := one.mul_right (p^(v-1))
    rw [←pow_add,show 241+(v-1)=v+240 by omega] at one'
    simpa only [←pow_succ',Nat.sub_add_cancel hv] using one'
  have steps (v : ℕ) (hv : 0<v) (j : ℕ) : Nat.ModEq m (p^(v+240*j)) (p^v) := by
    induction j with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ j ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (step _ (by omega)).trans ih
  calc
    p^e ≡ p^(e+240) [MOD m] := (step e he).symm
    _ = p^((240+e%240)+240*(e/240)) := by rw [Nat.add_assoc,Nat.mod_add_div,Nat.add_comm]
    _ ≡ _ [MOD m] := steps _ (by omega) _

private def residue (m k a b : ℕ) := (2^(240+a)*7^(240+b)+k+2*m-2)%m

private theorem residue_eq {n a b : ℕ} (eq : n+2=2^a*7^b) (ha : 0<a) (hb : 0<b)
    {m : ℕ} (stable : Stable m) (k : ℕ) :
    (n+k)%m=residue m k (a%240) (b%240) := by
  obtain ⟨mp,c3,c5⟩ := stable
  let w := 2^(240+a%240)*7^(240+b%240)+k
  have d : Nat.ModEq m (n+k+2) w := by
    rw [show n+k+2=(n+2)+k by omega,eq]
    exact ((cycle c3 a ha).mul (cycle c5 b hb)).add_right k
  have add : Nat.ModEq m w (w+2*m) := by
    change w%m=(w+2*m)%m
    rw [Nat.mul_comm 2 m,Nat.add_mul_mod_self_left]
  have strong := Nat.ModEq.add_right_cancel' 2
    (show Nat.ModEq m (n+k+2) (w+2*m-2+2) by rw [Nat.sub_add_cancel (by omega)]; exact d.trans add)
  exact strong

private abbrev RowOK (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable r.q ∧ Stable r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  ∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true

private abbrev CellOK (r : Row) (i j : ℕ) :=
  residue r.q r.k i j=0 ∧ r.mask.testBit (residue r.m r.k i j)=false ∧
  ∀ p : Fin (r.k+1), p.val.Prime → p.val∉r.pool → Stable p.val ∧ residue p.val r.k i j≠0

private theorem smooth {r : Row} (h : RowOK r) (t : ℕ) :
    0<t → (∀ p : ℕ, p.Prime → p∣t → p∈r.pool) → r.mask.testBit (t%r.m)=true := by
  induction t using induction_on_primes with
  | zero => omega
  | one => exact fun _ _ => h.2.2.2.2.2.2.1
  | prime_mul p t pp ih =>
    intro pos sup
    have tt : 0<t := Nat.pos_of_mul_pos_left pos
    have pt := sup p pp (dvd_mul_right p t)
    have good := ih tt (fun q pq d => sup q pq (dvd_mul_of_dvd_right d p))
    have final := h.2.2.2.2.2.2.2 ⟨t%r.m,Nat.mod_lt _ h.2.2.2.2.2.1.1⟩ good p pt
    simpa only [Nat.mod_mul_mod,Nat.mul_comm t p] using final

private theorem exclude {n a b : ℕ} (eq : n+2=2^a*7^b) (ha : 0<a) (hb : 0<b)
    (sol : Erdos889.v_l 1 n=1) {r : Row} (h : RowOK r) (cell : CellOK r (a%240) (b%240)) : False := by
  have qd := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb h.2.2.2.2.1 r.k).trans cell.1)
  have support (p : ℕ) (pp : p.Prime) (dp : p∣n+r.k) : p∈r.pool := by
    by_contra outside
    have ne : r.q≠p := by intro e; exact outside (e ▸ h.2.2.2.1)
    by_cases early : p≤r.k
    · obtain ⟨st,nd⟩ := cell.2.2 ⟨p,by omega⟩ pp outside
      exact nd ((residue_eq eq ha hb st r.k).symm.trans (Nat.mod_eq_zero_of_dvd dp))
    · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes h.2.1 h.1 pp ne h.2.2.1 (by omega) qd dp sol
  have prop := smooth h (n+r.k) (by have := h.2.1; omega) support
  rw [residue_eq eq ha hb h.2.2.2.2.2.1,cell.2.1] at prop
  contradiction

private def rows : List Row := [
  ⟨11,3,[3, 11],17,0x1fffe⟩,
  ⟨11,3,[3, 11],35,0x228033a1a⟩,
  ⟨11,5,[5, 11],25,0x210863⟩,
  ⟨11,5,[5, 11],39,0x102510d36⟩,
  ⟨11,5,[5, 11],51,0x21a0022996832⟩,
  ⟨11,5,[5, 11],63,0x4490014002800922⟩,
  ⟨11,5,[5, 11],221,0x2900202819b811869100040a74100020003208000c20818830108a2⟩,
  ⟨11,5,[5, 11],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  ⟨11,6,[2, 3, 11],17,0x1fffe⟩,
  ⟨11,6,[2, 3, 11],41,0x1fffffffffe⟩,
  ⟨11,6,[2, 3, 11],63,0x46578332bc51b5e⟩,
  ⟨11,6,[2, 3, 11],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  ⟨11,6,[2, 3, 11],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  ⟨11,6,[2, 3, 11],697,0x1ef6a9b7320e38ac786556e07e432690fa00a48c88f2f111bee4852874f70c56ab304403249717d34242e877b85d090b2fa3a49300883355a8c3bcb852849df6223d3c44c494017c259309f81daa9878d471c133b655bde⟩,
  ⟨11,6,[2, 3, 11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  ⟨11,6,[2, 3, 11],1105,0x1eb628e47212f080ad601c23ad0710162399a4000a81242a629c41a848101cb5242a0b4e219144101262150c30947624e1225a85804e6210961048004a862cc861c03235067982b1300e184cd18548004821a42119c8068569121c91b8a430c2a11920208a2611cb415092b4e020485608e5195092054000966711a02382d710e01ad4043d21389c51b5e⟩,
  ⟨11,7,[11],5,0x2⟩,
  ⟨13,9,[3, 7, 13],9,0x9b⟩,
  ⟨13,9,[3, 7, 13],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  ⟨13,9,[3, 7, 13],495,0x4021140a41060104a0410804086c32124484c36810000c201308a20021100844200b41809320241a4412094102d061104028120301805308949825329a⟩,
  ⟨13,10,[2, 5, 13],17,0x1fffe⟩,
  ⟨13,10,[2, 5, 13],41,0x1fffffffffe⟩,
  ⟨13,10,[2, 5, 13],61,0x1ffffffffffffffe⟩,
  ⟨13,10,[2, 5, 13],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  ⟨17,3,[3, 17],13,0x161a⟩,
  ⟨17,3,[3, 17],35,0x228033a1a⟩,
  ⟨17,4,[2, 17],91,0x6880c110a40602508830116⟩,
  ⟨17,6,[2, 3, 17],41,0x1fffffffffe⟩,
  ⟨17,6,[2, 3, 17],45,0x55898f135e⟩,
  ⟨17,6,[2, 3, 17],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨17,6,[2, 3, 17],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  ⟨17,6,[2, 3, 17],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩,
  ⟨17,10,[2, 5, 17],61,0x1ffffffffffffffe⟩,
  ⟨17,10,[2, 5, 17],75,0x116026c145829b0536⟩,
  ⟨17,10,[2, 5, 17],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  ⟨17,10,[2, 5, 17],671,0x4112107420c52556a305d00b5361936222c9d4b1066e314458e770a2942d21b79491d0da083e2759f0251382cf84f0765602794a96b2f018c5d973018f70d42cb3b83619312f744f38951954fad1d7b37d7fe⟩,
  ⟨17,10,[2, 5, 17],1001,0x1b383a506a21c915a220315a93095c8f3424215428098e225938430cdb8742b8289020d5304899803200020a12f02021cb492b04807846c78a3a00e981322b5132065c0171478d88780483524b4e10103d214100013006644832ac102450750b876cc308726911c64050aa1090b3c4ea43256a301116a24e11582970736⟩,
  ⟨17,11,[11, 17],93,0x124c345b00221100368b0c92⟩,
  ⟨17,11,[11, 17],123,0x25841b08a0002932122d968a6034c12⟩,
  ⟨17,11,[11, 17],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  ⟨17,11,[11, 17],819,0x40904001001020008009008044001040008244000000001000001000000000800005000049005104000004a00000040000008000100000020000005200000208a00920000a0000100000000080000080000000022410002080022010090010004080080020902⟩,
  ⟨17,11,[17],9,0x102⟩,
  ⟨17,15,[3, 5, 17],63,0x5c49ea700e57923a⟩,
  ⟨17,15,[3, 5, 17],175,0x22a033e3a4d02674349a00ef8e93509df0d22a13ba3a⟩,
  ⟨17,15,[3, 5, 17],671,0x4112107420c52556a305d00b5361936222c9d4b1066e314458e770a2942d21b79491d0da083e2759f0251382cf84f0765602794a96b2f018c5d973018f70d42cb3b83619312f744f38951954fad1d7b37d7fe⟩,
  ⟨17,15,[3, 5, 17],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  ⟨17,15,[3, 5, 17],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  ⟨17,15,[3, 5, 17],1271,0x1021508163300c5176c1a1b4445b123423e2ca4029903cf647175339b52495e600d4eec1cb1c934110dc3c2540fb0ae7d246b476f224b0bc38e2359659223e86c5400a275f9b9e552a1da12f4971f71070650b7a45ab518622051badf55c9e83aa65965398e342f29bb091921db418ae00fd5bc1c4e77d32c72c7480d4ff9842db526315151d9083f66afd2cb83bd23725ddd07a3c9171cff31976f57bf7e⟩,
  ⟨17,15,[3, 5, 17],1287,0x5d49fc5c1807d25b89f8ef610d7c8926176cd14622154cace91904926a58d68ba513830cc9a9b656fbc68b9c5ec7612b1061ec7e0bcaf846e670813e02946bc5732c79ad4da2bb429a3814386c474a81008152e2361c281c5942dd45b2b59e34cea3d629407c810e67621f53d07e378608d486e37a39d163df6a6d959330c1c8a5d16b1a56492098973532a844628b36e864913eb086f71f91da4be0183a3f92ba⟩,
  ⟨31,13,[13, 31],595,0x30983034811a841235e92046548d283180450008231e818080021a00342831d427890a1888a2846a428034052a310cd2386e6942e0218e1b54c5a12620c8111ca40012650827281c12252⟩,
  ⟨31,14,[2, 31],15,0x116⟩,
  ⟨31,23,[7, 19, 23, 31],41,0x1fffffffffe⟩,
  ⟨31,23,[7, 19, 23, 31],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  ⟨31,23,[7, 19, 23, 31],1037,0x29c4012000802006083840220180b02088863006005ed0a9e1054a0809020011134414b0d80009a5321d130102208008003304200480431a00150ec038a0502030002470a0600114120082001180008460106812200008812c00191c880010800c91480802e0e812c000002032200440aa28a4140980c46808410429130a1892082⟩,
  ⟨41,7,[41],5,0x2⟩,
  ⟨41,10,[2, 5, 41],119,0x141324470b0970652b11cb15977e⟩,
  ⟨41,11,[11, 41],61,0x1434026619900b0a⟩,
  ⟨41,23,[7, 19, 23, 41],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩]
set_option maxHeartbeats 4500000 in
set_option maxRecDepth 8192 in
private theorem good : ∀ r ∈ rows, RowOK r := by decide +kernel
private def primes : List ℕ := [17, 31, 41, 241]
private theorem pg : ∀ q ∈ primes, q.Prime ∧ q≤1000 ∧ Stable q := by decide +kernel
private def packed : ℕ → ℕ
  | 1 => 0x700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002c00000700000500000e00001400001b00000900000500001200001400001500000800000100000e00001400001e00000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002600000700000500000e00001400001b00000900000500001000001400001500000900000100000e000014000000
  | 3 => 0x200001b00000600000000000c00001400002e00000000000500000e00000200000000000600000100001000000000001b00000600000500000000000200001c00000300000000000c00001400003000000000000100001d00000200000000000600000400000e00000000002100000600000500000000000200001d00000600000000000c00001400001b00000000000500000e00000200000000000600000400000e000000000023000006000001000000000
  | 5 => 0xe00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001700000600000500001000001400002600000600000500000e00001400001b00000600000100000e00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e00001400001700000600000500001600001400002900000600000500000e00001400001b000006000001
  | 7 => 0x900000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000800000100000000001400001d00000700000000000c00001400000200000000000500000f00001400000000000800000100000300000000000200000700000500000000001400001b00000900000000000c00001400000200000000000100000e00001400000000000700000400000d000000000002000008000005000000000014000015000
  | 9 => 0x2500000600000100001100001400001900000600000500000e00001400001600000600000500000e00001400003800000600000100001200001400001800000600000500000e00001400001e00000600000500000e00001400002900000600000100001000001400001900000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001a00000600000500000e00001400003600000600000500000e000014
  | 11 => 0xc00001400001b00000000000100000e00001400000000000200000400001100000000002000000700000500000000001400001b00000200000000000c00001400001700000000000500001000001400000000000200000400000e00000000001b00000800000100000000001400001600000200000000000c00001400000300000000000500000e00001400000000000200000100000e00000000001700000800000500000000001400001d000002000000000
  | 13 => 0x500001200001400001500000600000100000e00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003d00000600000500000e000014000018000006
  | 15 => 0x1600000000000200000e00001400000000000600000100001000000000001b00000600000200000000001400001600000600000000000c00001400003100000000000100001200001400000000000600000400000e00000000001600000600000200000000001400001d00000600000000000c00001400001b00000000000200000e00001400000000000600000400000e00000000001f00000600000100000000001400001b00000600000000000c000014000
  | 17 => 0x1400001e00000700000500000e00001400001b00000b00000100000e00001400001700000900000500001000001400002500000700000500000e00001400001b00000a00000100000e00001400001700000900000500001700001400003600000700000500000e00001400001800000800000100000e00001400001700000900000500001600001400002900000700000500000e00001400001b00000b00000100000e000014000017000008000005000010
  | 19 => 0x500000e00000300000000000600000400000200000000001500000600000100000000001400001d00000600000000000200001400001b00000000000500001300001400000000000600000100000200000000002100000600000500000000001400001b00000600000000000200001400001500000000000100000e00001400000000000600000400000200000000001b00000600000500000000001400001500000600000000000200001400002e000000000
  | 21 => 0x900000500000e00001400002900000a00000500000e00001400003900000700000100002d00001400001800000800000500000e00001400001e00000b00000500000e00001400002900000700000100001000001400001b00000900000500000e00001400002600000800000500000e00001400001e00000700000100001000001400001b00000900000500000e00001400003600000a00000500000e00001400002700000700000100001100001400001b
  | 23 => 0x200000000000600000400001100000000002000000600000500000000000200001b00000300000000000c00001400001700000000000500001000000200000000000600000400000e00000000001b00000600000100000000000200001700000600000000000c00001400003000000000000500000e00000200000000000600000100000e00000000001700000600000500000000000200001d00000600000000000c00001400001b00000000000100000e000
  | 25 => 0xe00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003a00000600000500000e000014000018000006000005000013000014000015000006000001
  | 27 => 0x700000100000d00000000000200000800000500000000001400001600000b00000000000c00001400000200000000000100000f00001400000000000800000400000300000000000200000800000500000000001400001d00000700000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000700000100000000001400001b00000900000000000c00001400000200000000000500000e000014000000000
  | 29 => 0x1b00000600000100000e00001400001700000600000500001000001400002400000600000500000e00001400001900000600000100000e00001400001600000600000500001700001400003600000600000500000e00001400001800000600000100000e00001400001700000600000500001100001400002900000600000500000e00001400001900000600000100000e00001400001600000600000500001000001400001e00000600000500000e000014
  | 31 => 0x1000000000001500000800000100000000001400001d00000200000000000c00001400001b00000000000500001200001400000000000200000100000e00000000002100000700000500000000001400001b00000200000000000c00001400000300000000000100000e00001400000000000200000400000e00000000001b00000800000500000000001400001500000200000000000c00001400002e00000000000500000e000014000000000002000004000
  | 33 => 0x500000e00001400003700000600000100001100001400001800000600000500000e00001400001600000600000500000e00001400002900000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400002800000600000100003500001400001b00000600000500000e000014000016000006
  | 35 => 0x1f00000600000200000000001400001b00000600000000000c00001400001600000000000200001000001400000000000600000400000e00000000001b00000600000100000000001400001600000600000000000c00001400003200000000000200000e00001400000000000600000100000e00000000001600000600000200000000001400001d00000600000000000c00001400001b00000000000100000e000014000000000006000004000017000000000
  | 37 => 0x1400001b00000900000500001100001400001500000800000100000e00001400001e00000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002500000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400003c00000700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002a00000700000500000e
  | 39 => 0x500000000001400001600000600000000000200001400003300000000000100001200001400000000000600000400000200000000001600000600000500000000001400001d00000600000000000200001400001a00000000000500000e00001400000000000600000400000200000000002200000600000100000000001400001a00000600000000000200001400001600000000000500000e00000300000000000600000100000200000000001a000006000
  | 41 => 0x900000500001000001400002700000700000500000e00001400001b00000a00000100000e00001400001700000900000500001200001400003600000700000500000e00001400001800000800000100000e00001400001700000900000500001100001400002900000700000500000e00001400001b00000b00000100000e00001400001700000800000500001000001400001e00000700000500000e00001400001b00000b00000100000e000014000017
  | 43 => 0x200001d00000300000000000c00001400001b00000000000500001200000200000000000600000100000e00000000002100000600000500000000000200001b00000600000000000c00001400001500000000000100000e00000200000000000600000400000e00000000001b00000600000500000000000200001500000600000000000c00001400002e00000000000500000e000002000000000006000004000010000000000015000006000001000000000
  | 45 => 0x1100001400001800000600000500000e00001400001e00000600000500000e00001400002900000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001b00000600000500000e00001400003600000600000500000e00001400002700000600000100001200001400001b00000600000500000e00001400001600000600000500000e000014000039000006000001
  | 47 => 0xa00000000000c00001400000200000000000500000f00001400000000000700000400000300000000000200000800000100000000001400001600000900000000000c00001400000200000000000500000e00001400000000000800000100000d00000000000200000800000500000000001400001d00000700000000000c00001400000200000000000100000e00001400000000000800000400000d00000000000200000700000500000000001400001b000
  | 49 => 0x1500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002500000600000500000e00001400001900000600000500001000001400001500000600000100000e00001400003b00000600000500000e00001400001800000600000500001100001400001500000600000100000e00001400002b00000600000500000e000014000019000006000005000013000014
  | 51 => 0xc00001400002f00000000000100001d00001400000000000200000400000e00000000002100000800000500000000001400001d00000200000000000c00001400000300000000000500000e00001400000000000200000400000e00000000002200000700000100000000001400001b00000200000000000c00001400002e00000000000500000e00001400000000000200000100001000000000001b000008000005000000000014000016000002000000000
  | 53 => 0x500000e00001400001b00000600000100000e00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e00001400001600000600000500001200001400002900000600000500000e00001400001b00000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e000014000016000006000005000010000014000026000006
  | 55 => 0x1b00000000000200001300001400000000000600000100000e00000000001f00000600000200000000001400001b00000600000000000c00001400001500000000000100000e00001400000000000600000400000e00000000001b00000600000200000000001400001500000600000000000c00001400002e00000000000200000e00001400000000000600000400001000000000001500000600000100000000001400001d00000600000000000c000014000
  | 57 => 0x1400001e00000b00000500000e00001400002900000700000100001000001400001b00000900000500000e00001400002500000800000500000e00001400001e00000700000100001000001400001b00000900000500000e00001400003600000a00000500000e00001400002500000700000100001100001400001b00000900000500000e00001400002900000a00000500000e00001400003800000700000100001100001400001800000800000500000e
  | 59 => 0x500001000001400000000000600000400000200000000001b00000600000100000000001400001600000600000000000200001400003400000000000500000e00001400000000000600000100000200000000001600000600000500000000001400001d00000600000000000200001400001b00000000000100000e00000300000000000600000400000200000000002000000600000500000000001400001b000006000000000002000014000016000000000
  | 61 => 0x700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002600000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400000000000700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002c00000700000500000e00001400001b00000900000500001200001400001500000800000100000e00001400001e
  | 63 => 0x200000000000600000400000e00000000002100000600000500000000000200001d00000600000000000c00001400001b00000000000500000e00000200000000000600000400000e00000000002300000600000100000000000200001b00000600000000000c00001400002e00000000000500000e00000200000000000600000100001000000000001b00000600000500000000000200001c00000300000000000c00001400003000000000000100001d000
  | 65 => 0xe00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e00001400001700000600000500001600001400002900000600000500000e00001400001b00000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001700000600000500001000001400002600000600000500000e00001400001b000006000001
  | 67 => 0x800000100000300000000000200000700000500000000001400001b00000900000000000c00001400000200000000000100000e00001400000000000700000400000d00000000000200000800000500000000001400001500000900000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000800000100000000001400001d00000700000000000c00001400000200000000000500000f000014000000000
  | 69 => 0x2900000600000100001000001400001900000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001a00000600000500000e00001400003600000600000500000e00001400002500000600000100001100001400001900000600000500000e00001400001600000600000500000e00001400003800000600000100001200001400001800000600000500000e00001400001e00000600000500000e000014
  | 71 => 0xe00000000001b00000800000100000000001400001600000200000000000c00001400000300000000000500000e00001400000000000200000100000e00000000001700000800000500000000001400001d00000200000000000c00001400001b00000000000100000e00001400000000000200000400001100000000002000000700000500000000001400001b00000200000000000c000014000017000000000005000010000014000000000002000004000
  | 73 => 0x500001000001400001500000600000100000e00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003d00000600000500000e00001400001800000600000500001200001400001500000600000100000e00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b000006
  | 75 => 0x1600000600000200000000001400001d00000600000000000c00001400001b00000000000200000e00001400000000000600000400000e00000000001f00000600000100000000001400001b00000600000000000c00001400001600000000000200000e00001400000000000600000100001000000000001b00000600000200000000001400001600000600000000000c00001400003100000000000100001200001400000000000600000400000e000000000
  | 77 => 0x1400003600000700000500000e00001400001800000800000100000e00001400001700000900000500001600001400002900000700000500000e00001400001b00000b00000100000e00001400001700000800000500001000001400001e00000700000500000e00001400001b00000b00000100000e00001400001700000900000500001000001400002500000700000500000e00001400001b00000a00000100000e000014000017000009000005000017
  | 79 => 0x500000000001400001b00000600000000000200001400001500000000000100000e00001400000000000600000400000200000000001b00000600000500000000001400001500000600000000000200001400002e00000000000500000e00000300000000000600000400000200000000001500000600000100000000001400001d00000600000000000200001400001b000000000005000013000014000000000006000001000002000000000021000006000
  | 81 => 0x900000500000e00001400002600000800000500000e00001400001e00000700000100001000001400001b00000900000500000e00001400003600000a00000500000e00001400002700000700000100001100001400001b00000900000500000e00001400002900000a00000500000e00001400003900000700000100002d00001400001800000800000500000e00001400001e00000b00000500000e00001400002900000700000100001000001400001b
  | 83 => 0x200001700000600000000000c00001400003000000000000500000e00000200000000000600000100000e00000000001700000600000500000000000200001d00000600000000000c00001400001b00000000000100000e00000200000000000600000400001100000000002000000600000500000000000200001b00000300000000000c00001400001700000000000500001000000200000000000600000400000e00000000001b000006000001000000000
  | 85 => 0xe00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003a00000600000500000e00001400001800000600000500001300001400001500000600000100000e00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b000006000005000010000014000015000006000001
  | 87 => 0x700000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000700000100000000001400001b00000900000000000c00001400000200000000000500000e00001400000000000700000100000d00000000000200000800000500000000001400001600000b00000000000c00001400000200000000000100000f00001400000000000800000400000300000000000200000800000500000000001400001d000
  | 89 => 0x1800000600000100000e00001400001700000600000500001100001400002900000600000500000e00001400001900000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001700000600000500001000001400002400000600000500000e00001400001900000600000100000e00001400001600000600000500001700001400003600000600000500000e000014
  | 91 => 0xc00001400000300000000000100000e00001400000000000200000400000e00000000001b00000800000500000000001400001500000200000000000c00001400002e00000000000500000e00001400000000000200000400001000000000001500000800000100000000001400001d00000200000000000c00001400001b00000000000500001200001400000000000200000100000e00000000002100000700000500000000001400001b000002000000000
  | 93 => 0x500000e00001400001e00000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400002800000600000100003500001400001b00000600000500000e00001400001600000600000500000e00001400003700000600000100001100001400001800000600000500000e00001400001600000600000500000e00001400002900000600000100001000001400001b00000600000500000e000014000016000006
  | 95 => 0x3200000000000200000e00001400000000000600000100000e00000000001600000600000200000000001400001d00000600000000000c00001400001b00000000000100000e00001400000000000600000400001700000000001f00000600000200000000001400001b00000600000000000c00001400001600000000000200001000001400000000000600000400000e00000000001b00000600000100000000001400001600000600000000000c000014000
  | 97 => 0x1400001b00000900000500001000001400001500000900000100000e00001400003c00000700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002a00000700000500000e00001400001b00000900000500001100001400001500000800000100000e00001400001e00000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002500000700000500000e
  | 99 => 0x500000e00001400000000000600000400000200000000002200000600000100000000001400001a00000600000000000200001400001600000000000500000e00000300000000000600000100000200000000001a00000600000500000000001400001600000600000000000200001400003300000000000100001200001400000000000600000400000200000000001600000600000500000000001400001d00000600000000000200001400001a000000000
  | 101 => 0x900000500001100001400002900000700000500000e00001400001b00000b00000100000e00001400001700000800000500001000001400001e00000700000500000e00001400001b00000b00000100000e00001400001700000900000500001000001400002700000700000500000e00001400001b00000a00000100000e00001400001700000900000500001200001400003600000700000500000e00001400001800000800000100000e000014000017
  | 103 => 0x200000000000600000400000e00000000001b00000600000500000000000200001500000600000000000c00001400002e00000000000500000e00000200000000000600000400001000000000001500000600000100000000000200001d00000300000000000c00001400001b00000000000500001200000200000000000600000100000e00000000002100000600000500000000000200001b00000600000000000c00001400001500000000000100000e000
  | 105 => 0x1000001400001b00000600000500000e00001400003600000600000500000e00001400002700000600000100001200001400001b00000600000500000e00001400001600000600000500000e00001400003900000600000100001100001400001800000600000500000e00001400001e00000600000500000e00001400002900000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400001e000006000001
  | 107 => 0x800000100000d00000000000200000800000500000000001400001d00000700000000000c00001400000200000000000100000e00001400000000000800000400000d00000000000200000700000500000000001400001b00000a00000000000c00001400000200000000000500000f00001400000000000700000400000300000000000200000800000100000000001400001600000900000000000c00001400000200000000000500000e000014000000000
  | 109 => 0x1500000600000100000e00001400003b00000600000500000e00001400001800000600000500001100001400001500000600000100000e00001400002b00000600000500000e00001400001900000600000500001300001400001500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002500000600000500000e000014000019000006000005000010000014
  | 111 => 0xe00000000002200000700000100000000001400001b00000200000000000c00001400002e00000000000500000e00001400000000000200000100001000000000001b00000800000500000000001400001600000200000000000c00001400002f00000000000100001d00001400000000000200000400000e00000000002100000800000500000000001400001d00000200000000000c00001400000300000000000500000e000014000000000002000004000
  | 113 => 0x500000e00001400001b00000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001600000600000500001000001400002600000600000500000e00001400001b00000600000100000e00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e000014000016000006000005000012000014000029000006
  | 115 => 0x1b00000600000200000000001400001500000600000000000c00001400002e00000000000200000e00001400000000000600000400001000000000001500000600000100000000001400001d00000600000000000c00001400001b00000000000200001300001400000000000600000100000e00000000001f00000600000200000000001400001b00000600000000000c00001400001500000000000100000e00001400000000000600000400000e000000000
  | 117 => 0x1400003600000a00000500000e00001400002500000700000100001100001400001b00000900000500000e00001400002900000a00000500000e00001400003800000700000100001100001400001800000800000500000e00001400001e00000b00000500000e00001400002900000700000100001000001400001b00000900000500000e00001400002500000800000500000e00001400001e00000700000100001000001400001b00000900000500000e
  | 119 => 0x500000000001400001d00000600000000000200001400001b00000000000100000e00000300000000000600000400000200000000002000000600000500000000001400001b00000600000000000200001400001600000000000500001000001400000000000600000400000200000000001b00000600000100000000001400001600000600000000000200001400003400000000000500000e000014000000000006000001000002000000000016000006000
  | 121 => 0x700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002c00000700000500000e00001400001b00000900000500001200001400001500000800000100000e00001400001e00000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002600000700000500000e00001400001b00000900000500001000001400001500000900000100000e000014000000
  | 123 => 0x200001b00000600000000000c00001400002e00000000000500000e00000200000000000600000100001000000000001b00000600000500000000000200001c00000300000000000c00001400003000000000000100001d00000200000000000600000400000e00000000002100000600000500000000000200001d00000600000000000c00001400001b00000000000500000e00000200000000000600000400000e000000000023000006000001000000000
  | 125 => 0xe00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001700000600000500001000001400002600000600000500000e00001400001b00000600000100000e00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e00001400001700000600000500001600001400002900000600000500000e00001400001b000006000001
  | 127 => 0x900000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000800000100000000001400001d00000700000000000c00001400000200000000000500000f00001400000000000800000100000300000000000200000700000500000000001400001b00000900000000000c00001400000200000000000100000e00001400000000000700000400000d000000000002000008000005000000000014000015000
  | 129 => 0x2500000600000100001100001400001900000600000500000e00001400001600000600000500000e00001400003800000600000100001200001400001800000600000500000e00001400001e00000600000500000e00001400002900000600000100001000001400001900000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001a00000600000500000e00001400003600000600000500000e000014
  | 131 => 0xc00001400001b00000000000100000e00001400000000000200000400001100000000002000000700000500000000001400001b00000200000000000c00001400001700000000000500001000001400000000000200000400000e00000000001b00000800000100000000001400001600000200000000000c00001400000300000000000500000e00001400000000000200000100000e00000000001700000800000500000000001400001d000002000000000
  | 133 => 0x500001200001400001500000600000100000e00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003d00000600000500000e000014000018000006
  | 135 => 0x1600000000000200000e00001400000000000600000100001000000000001b00000600000200000000001400001600000600000000000c00001400003100000000000100001200001400000000000600000400000e00000000001600000600000200000000001400001d00000600000000000c00001400001b00000000000200000e00001400000000000600000400000e00000000001f00000600000100000000001400001b00000600000000000c000014000
  | 137 => 0x1400001e00000700000500000e00001400001b00000b00000100000e00001400001700000900000500001000001400002500000700000500000e00001400001b00000a00000100000e00001400001700000900000500001700001400003600000700000500000e00001400001800000800000100000e00001400001700000900000500001600001400002900000700000500000e00001400001b00000b00000100000e000014000017000008000005000010
  | 139 => 0x500000e00000300000000000600000400000200000000001500000600000100000000001400001d00000600000000000200001400001b00000000000500001300001400000000000600000100000200000000002100000600000500000000001400001b00000600000000000200001400001500000000000100000e00001400000000000600000400000200000000001b00000600000500000000001400001500000600000000000200001400002e000000000
  | 141 => 0x900000500000e00001400002900000a00000500000e00001400003900000700000100002d00001400001800000800000500000e00001400001e00000b00000500000e00001400002900000700000100001000001400001b00000900000500000e00001400002600000800000500000e00001400001e00000700000100001000001400001b00000900000500000e00001400003600000a00000500000e00001400002700000700000100001100001400001b
  | 143 => 0x200000000000600000400001100000000002000000600000500000000000200001b00000300000000000c00001400001700000000000500001000000200000000000600000400000e00000000001b00000600000100000000000200001700000600000000000c00001400003000000000000500000e00000200000000000600000100000e00000000001700000600000500000000000200001d00000600000000000c00001400001b00000000000100000e000
  | 145 => 0xe00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003a00000600000500000e000014000018000006000005000013000014000015000006000001
  | 147 => 0x700000100000d00000000000200000800000500000000001400001600000b00000000000c00001400000200000000000100000f00001400000000000800000400000300000000000200000800000500000000001400001d00000700000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000700000100000000001400001b00000900000000000c00001400000200000000000500000e000014000000000
  | 149 => 0x1b00000600000100000e00001400001700000600000500001000001400002400000600000500000e00001400001900000600000100000e00001400001600000600000500001700001400003600000600000500000e00001400001800000600000100000e00001400001700000600000500001100001400002900000600000500000e00001400001900000600000100000e00001400001600000600000500001000001400001e00000600000500000e000014
  | 151 => 0x1000000000001500000800000100000000001400001d00000200000000000c00001400001b00000000000500001200001400000000000200000100000e00000000002100000700000500000000001400001b00000200000000000c00001400000300000000000100000e00001400000000000200000400000e00000000001b00000800000500000000001400001500000200000000000c00001400002e00000000000500000e000014000000000002000004000
  | 153 => 0x500000e00001400003700000600000100001100001400001800000600000500000e00001400001600000600000500000e00001400002900000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400002800000600000100003500001400001b00000600000500000e000014000016000006
  | 155 => 0x1f00000600000200000000001400001b00000600000000000c00001400001600000000000200001000001400000000000600000400000e00000000001b00000600000100000000001400001600000600000000000c00001400003200000000000200000e00001400000000000600000100000e00000000001600000600000200000000001400001d00000600000000000c00001400001b00000000000100000e000014000000000006000004000017000000000
  | 157 => 0x1400001b00000900000500001100001400001500000800000100000e00001400001e00000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002500000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400003c00000700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002a00000700000500000e
  | 159 => 0x500000000001400001600000600000000000200001400003300000000000100001200001400000000000600000400000200000000001600000600000500000000001400001d00000600000000000200001400001a00000000000500000e00001400000000000600000400000200000000002200000600000100000000001400001a00000600000000000200001400001600000000000500000e00000300000000000600000100000200000000001a000006000
  | 161 => 0x900000500001000001400002700000700000500000e00001400001b00000a00000100000e00001400001700000900000500001200001400003600000700000500000e00001400001800000800000100000e00001400001700000900000500001100001400002900000700000500000e00001400001b00000b00000100000e00001400001700000800000500001000001400001e00000700000500000e00001400001b00000b00000100000e000014000017
  | 163 => 0x200001d00000300000000000c00001400001b00000000000500001200000200000000000600000100000e00000000002100000600000500000000000200001b00000600000000000c00001400001500000000000100000e00000200000000000600000400000e00000000001b00000600000500000000000200001500000600000000000c00001400002e00000000000500000e000002000000000006000004000010000000000015000006000001000000000
  | 165 => 0x1100001400001800000600000500000e00001400001e00000600000500000e00001400002900000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001b00000600000500000e00001400003600000600000500000e00001400002700000600000100001200001400001b00000600000500000e00001400001600000600000500000e000014000039000006000001
  | 167 => 0xa00000000000c00001400000200000000000500000f00001400000000000700000400000300000000000200000800000100000000001400001600000900000000000c00001400000200000000000500000e00001400000000000800000100000d00000000000200000800000500000000001400001d00000700000000000c00001400000200000000000100000e00001400000000000800000400000d00000000000200000700000500000000001400001b000
  | 169 => 0x1500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002500000600000500000e00001400001900000600000500001000001400001500000600000100000e00001400003b00000600000500000e00001400001800000600000500001100001400001500000600000100000e00001400002b00000600000500000e000014000019000006000005000013000014
  | 171 => 0xc00001400002f00000000000100001d00001400000000000200000400000e00000000002100000800000500000000001400001d00000200000000000c00001400000300000000000500000e00001400000000000200000400000e00000000002200000700000100000000001400001b00000200000000000c00001400002e00000000000500000e00001400000000000200000100001000000000001b000008000005000000000014000016000002000000000
  | 173 => 0x500000e00001400001b00000600000100000e00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e00001400001600000600000500001200001400002900000600000500000e00001400001b00000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e000014000016000006000005000010000014000026000006
  | 175 => 0x1b00000000000200001300001400000000000600000100000e00000000001f00000600000200000000001400001b00000600000000000c00001400001500000000000100000e00001400000000000600000400000e00000000001b00000600000200000000001400001500000600000000000c00001400002e00000000000200000e00001400000000000600000400001000000000001500000600000100000000001400001d00000600000000000c000014000
  | 177 => 0x1400001e00000b00000500000e00001400002900000700000100001000001400001b00000900000500000e00001400002500000800000500000e00001400001e00000700000100001000001400001b00000900000500000e00001400003600000a00000500000e00001400002500000700000100001100001400001b00000900000500000e00001400002900000a00000500000e00001400003800000700000100001100001400001800000800000500000e
  | 179 => 0x500001000001400000000000600000400000200000000001b00000600000100000000001400001600000600000000000200001400003400000000000500000e00001400000000000600000100000200000000001600000600000500000000001400001d00000600000000000200001400001b00000000000100000e00000300000000000600000400000200000000002000000600000500000000001400001b000006000000000002000014000016000000000
  | 181 => 0x700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002600000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400000000000700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002c00000700000500000e00001400001b00000900000500001200001400001500000800000100000e00001400001e
  | 183 => 0x200000000000600000400000e00000000002100000600000500000000000200001d00000600000000000c00001400001b00000000000500000e00000200000000000600000400000e00000000002300000600000100000000000200001b00000600000000000c00001400002e00000000000500000e00000200000000000600000100001000000000001b00000600000500000000000200001c00000300000000000c00001400003000000000000100001d000
  | 185 => 0xe00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e00001400001700000600000500001600001400002900000600000500000e00001400001b00000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001700000600000500001000001400002600000600000500000e00001400001b000006000001
  | 187 => 0x800000100000300000000000200000700000500000000001400001b00000900000000000c00001400000200000000000100000e00001400000000000700000400000d00000000000200000800000500000000001400001500000900000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000800000100000000001400001d00000700000000000c00001400000200000000000500000f000014000000000
  | 189 => 0x2900000600000100001000001400001900000600000500000e00001400001600000600000500000e00001400001e00000600000100001000001400001a00000600000500000e00001400003600000600000500000e00001400002500000600000100001100001400001900000600000500000e00001400001600000600000500000e00001400003800000600000100001200001400001800000600000500000e00001400001e00000600000500000e000014
  | 191 => 0xe00000000001b00000800000100000000001400001600000200000000000c00001400000300000000000500000e00001400000000000200000100000e00000000001700000800000500000000001400001d00000200000000000c00001400001b00000000000100000e00001400000000000200000400001100000000002000000700000500000000001400001b00000200000000000c000014000017000000000005000010000014000000000002000004000
  | 193 => 0x500001000001400001500000600000100000e00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003d00000600000500000e00001400001800000600000500001200001400001500000600000100000e00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b000006
  | 195 => 0x1600000600000200000000001400001d00000600000000000c00001400001b00000000000200000e00001400000000000600000400000e00000000001f00000600000100000000001400001b00000600000000000c00001400001600000000000200000e00001400000000000600000100001000000000001b00000600000200000000001400001600000600000000000c00001400003100000000000100001200001400000000000600000400000e000000000
  | 197 => 0x1400003600000700000500000e00001400001800000800000100000e00001400001700000900000500001600001400002900000700000500000e00001400001b00000b00000100000e00001400001700000800000500001000001400001e00000700000500000e00001400001b00000b00000100000e00001400001700000900000500001000001400002500000700000500000e00001400001b00000a00000100000e000014000017000009000005000017
  | 199 => 0x500000000001400001b00000600000000000200001400001500000000000100000e00001400000000000600000400000200000000001b00000600000500000000001400001500000600000000000200001400002e00000000000500000e00000300000000000600000400000200000000001500000600000100000000001400001d00000600000000000200001400001b000000000005000013000014000000000006000001000002000000000021000006000
  | 201 => 0x900000500000e00001400002600000800000500000e00001400001e00000700000100001000001400001b00000900000500000e00001400003600000a00000500000e00001400002700000700000100001100001400001b00000900000500000e00001400002900000a00000500000e00001400003900000700000100002d00001400001800000800000500000e00001400001e00000b00000500000e00001400002900000700000100001000001400001b
  | 203 => 0x200001700000600000000000c00001400003000000000000500000e00000200000000000600000100000e00000000001700000600000500000000000200001d00000600000000000c00001400001b00000000000100000e00000200000000000600000400001100000000002000000600000500000000000200001b00000300000000000c00001400001700000000000500001000000200000000000600000400000e00000000001b000006000001000000000
  | 205 => 0xe00001400002600000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400003a00000600000500000e00001400001800000600000500001300001400001500000600000100000e00001400002b00000600000500000e00001400001b00000600000500001100001400001500000600000100000e00001400001e00000600000500000e00001400001b000006000005000010000014000015000006000001
  | 207 => 0x700000000000c00001400000200000000000500000e00001400000000000800000400000d00000000000200000700000100000000001400001b00000900000000000c00001400000200000000000500000e00001400000000000700000100000d00000000000200000800000500000000001400001600000b00000000000c00001400000200000000000100000f00001400000000000800000400000300000000000200000800000500000000001400001d000
  | 209 => 0x1800000600000100000e00001400001700000600000500001100001400002900000600000500000e00001400001900000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001700000600000500001000001400002400000600000500000e00001400001900000600000100000e00001400001600000600000500001700001400003600000600000500000e000014
  | 211 => 0xc00001400000300000000000100000e00001400000000000200000400000e00000000001b00000800000500000000001400001500000200000000000c00001400002e00000000000500000e00001400000000000200000400001000000000001500000800000100000000001400001d00000200000000000c00001400001b00000000000500001200001400000000000200000100000e00000000002100000700000500000000001400001b000002000000000
  | 213 => 0x500000e00001400001e00000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400002800000600000100003500001400001b00000600000500000e00001400001600000600000500000e00001400003700000600000100001100001400001800000600000500000e00001400001600000600000500000e00001400002900000600000100001000001400001b00000600000500000e000014000016000006
  | 215 => 0x3200000000000200000e00001400000000000600000100000e00000000001600000600000200000000001400001d00000600000000000c00001400001b00000000000100000e00001400000000000600000400001700000000001f00000600000200000000001400001b00000600000000000c00001400001600000000000200001000001400000000000600000400000e00000000001b00000600000100000000001400001600000600000000000c000014000
  | 217 => 0x1400001b00000900000500001000001400001500000900000100000e00001400003c00000700000500000e00001400001800000800000500001100001400001500000900000100000e00001400002a00000700000500000e00001400001b00000900000500001100001400001500000800000100000e00001400001e00000700000500000e00001400001b00000900000500001000001400001500000900000100000e00001400002500000700000500000e
  | 219 => 0x500000e00001400000000000600000400000200000000002200000600000100000000001400001a00000600000000000200001400001600000000000500000e00000300000000000600000100000200000000001a00000600000500000000001400001600000600000000000200001400003300000000000100001200001400000000000600000400000200000000001600000600000500000000001400001d00000600000000000200001400001a000000000
  | 221 => 0x900000500001100001400002900000700000500000e00001400001b00000b00000100000e00001400001700000800000500001000001400001e00000700000500000e00001400001b00000b00000100000e00001400001700000900000500001000001400002700000700000500000e00001400001b00000a00000100000e00001400001700000900000500001200001400003600000700000500000e00001400001800000800000100000e000014000017
  | 223 => 0x200000000000600000400000e00000000001b00000600000500000000000200001500000600000000000c00001400002e00000000000500000e00000200000000000600000400001000000000001500000600000100000000000200001d00000300000000000c00001400001b00000000000500001200000200000000000600000100000e00000000002100000600000500000000000200001b00000600000000000c00001400001500000000000100000e000
  | 225 => 0x1000001400001b00000600000500000e00001400003600000600000500000e00001400002700000600000100001200001400001b00000600000500000e00001400001600000600000500000e00001400003900000600000100001100001400001800000600000500000e00001400001e00000600000500000e00001400002900000600000100001000001400001b00000600000500000e00001400001600000600000500000e00001400001e000006000001
  | 227 => 0x800000100000d00000000000200000800000500000000001400001d00000700000000000c00001400000200000000000100000e00001400000000000800000400000d00000000000200000700000500000000001400001b00000a00000000000c00001400000200000000000500000f00001400000000000700000400000300000000000200000800000100000000001400001600000900000000000c00001400000200000000000500000e000014000000000
  | 229 => 0x1500000600000100000e00001400003b00000600000500000e00001400001800000600000500001100001400001500000600000100000e00001400002b00000600000500000e00001400001900000600000500001300001400001500000600000100000e00001400001e00000600000500000e00001400001b00000600000500001000001400001500000600000100000e00001400002500000600000500000e000014000019000006000005000010000014
  | 231 => 0xe00000000002200000700000100000000001400001b00000200000000000c00001400002e00000000000500000e00001400000000000200000100001000000000001b00000800000500000000001400001600000200000000000c00001400002f00000000000100001d00001400000000000200000400000e00000000002100000800000500000000001400001d00000200000000000c00001400000300000000000500000e000014000000000002000004000
  | 233 => 0x500000e00001400001b00000600000100000e00001400001600000600000500001000001400001e00000600000500000e00001400001b00000600000100000e00001400001600000600000500001000001400002600000600000500000e00001400001b00000600000100000e00001400001600000600000500001100001400003600000600000500000e00001400001800000600000100000e000014000016000006000005000012000014000029000006
  | 235 => 0x1b00000600000200000000001400001500000600000000000c00001400002e00000000000200000e00001400000000000600000400001000000000001500000600000100000000001400001d00000600000000000c00001400001b00000000000200001300001400000000000600000100000e00000000001f00000600000200000000001400001b00000600000000000c00001400001500000000000100000e00001400000000000600000400000e000000000
  | 237 => 0x1400003600000a00000500000e00001400002500000700000100001100001400001b00000900000500000e00001400002900000a00000500000e00001400003800000700000100001100001400001800000800000500000e00001400001e00000b00000500000e00001400002900000700000100001000001400001b00000900000500000e00001400002500000800000500000e00001400001e00000700000100001000001400001b00000900000500000e
  | 239 => 0x500000000001400001d00000600000000000200001400001b00000000000100000e00000300000000000600000400000200000000002000000600000500000000001400001b00000600000000000200001400001600000000000500001000001400000000000600000400000200000000001b00000600000100000000001400001600000600000000000200001400003400000000000500000e000014000000000006000001000002000000000016000006000
  | _ => 0
private def ix (i j : ℕ) := ((packed i) >>> (6*j))%64
private def qFor (i j : ℕ) := primes[ix i j]?.getD 0
private def rowFor (i j : ℕ) := rows[ix i j-primes.length]?.getD default
private abbrev Test (i j : ℕ) := residue 30 0 i j=0 → (i%12≠1 ∨ j%12≠0) →
    (ix i j<primes.length ∧ residue (qFor i j) 1 i j=0) ∨
    (ix i j-primes.length<rows.length ∧ CellOK (rowFor i j) i j)
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block0 : ∀ i∈List.range' 0 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block1 : ∀ i∈List.range' 10 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block2 : ∀ i∈List.range' 20 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block3 : ∀ i∈List.range' 30 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block4 : ∀ i∈List.range' 40 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block5 : ∀ i∈List.range' 50 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block6 : ∀ i∈List.range' 60 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block7 : ∀ i∈List.range' 70 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block8 : ∀ i∈List.range' 80 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block9 : ∀ i∈List.range' 90 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block10 : ∀ i∈List.range' 100 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block11 : ∀ i∈List.range' 110 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block12 : ∀ i∈List.range' 120 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block13 : ∀ i∈List.range' 130 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block14 : ∀ i∈List.range' 140 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block15 : ∀ i∈List.range' 150 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block16 : ∀ i∈List.range' 160 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block17 : ∀ i∈List.range' 170 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block18 : ∀ i∈List.range' 180 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block19 : ∀ i∈List.range' 190 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block20 : ∀ i∈List.range' 200 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block21 : ∀ i∈List.range' 210 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block22 : ∀ i∈List.range' 220 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block23 : ∀ i∈List.range' 230 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
private theorem cover {i j : ℕ} (hi : i<240) (hj : j<240) : Test i j := by
  by_cases h0 : i<10
  · exact block0 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h1 : i<20
  · exact block1 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h2 : i<30
  · exact block2 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h3 : i<40
  · exact block3 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h4 : i<50
  · exact block4 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h5 : i<60
  · exact block5 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h6 : i<70
  · exact block6 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h7 : i<80
  · exact block7 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h8 : i<90
  · exact block8 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h9 : i<100
  · exact block9 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h10 : i<110
  · exact block10 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h11 : i<120
  · exact block11 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h12 : i<130
  · exact block12 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h13 : i<140
  · exact block13 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h14 : i<150
  · exact block14 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h15 : i<160
  · exact block15 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h16 : i<170
  · exact block16 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h17 : i<180
  · exact block17 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h18 : i<190
  · exact block18 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h19 : i<200
  · exact block19 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h20 : i<210
  · exact block20 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h21 : i<220
  · exact block21 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h22 : i<230
  · exact block22 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  exact block23 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩

theorem residues {n a b : ℕ} (large : 1000<n) (prime : (n+1).Prime)
    (eq : n+2=2^a*7^b) (ha : 0<a) (hb : 0<b) (div : 30∣n) (sol : Erdos889.v_l 1 n=1) :
    a%12=1 ∧ b%12=0 := by
  by_contra! bad
  have cell := cover (show a%240<240 by omega) (show b%240<240 by omega)
  have z30 := residue_eq eq ha hb (by decide : Stable 30) 0
  have test := cell (by omega)
  rw [Nat.mod_mod_of_dvd a (by decide : 12∣240),Nat.mod_mod_of_dvd b (by decide : 12∣240)] at test
  rcases test (by omega) with ⟨pi,zero⟩|⟨ri,ok⟩
  · have mem : qFor (a%240) (b%240) ∈ primes := by
      simp only [qFor,List.getElem?_eq_getElem pi,Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨pq,small,st⟩ := pg _ mem
    have dv := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb st 1).trans zero)
    have := (Nat.prime_dvd_prime_iff_eq pq prime).mp dv
    omega
  · have mem : rowFor (a%240) (b%240) ∈ rows := by
      simp only [rowFor,List.getElem?_eq_getElem ri,Option.getD_some]
      exact List.getElem_mem _
    exact exclude eq ha hb sol (good _ mem) ok
end Erdos889.PrimeSevenTwo


/- Modular exclusions for a third offset supported on three and seven. -/
namespace Erdos889.PrimeSevenThree

private structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

private abbrev Stable (m : ℕ) := 0 < m ∧ 3^61%m=3%m ∧ 7^61%m=7%m

private theorem cycle {p m : ℕ} (one : Nat.ModEq m (p^61) p) (e : ℕ) (he : 0<e) :
    Nat.ModEq m (p^e) (p^(60+e%60)) := by
  have step (v : ℕ) (hv : 0<v) : Nat.ModEq m (p^(v+60)) (p^v) := by
    have one' := one.mul_right (p^(v-1))
    rw [←pow_add,show 61+(v-1)=v+60 by omega] at one'
    simpa only [←pow_succ',Nat.sub_add_cancel hv] using one'
  have steps (v : ℕ) (hv : 0<v) (j : ℕ) : Nat.ModEq m (p^(v+60*j)) (p^v) := by
    induction j with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ j ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (step _ (by omega)).trans ih
  calc
    p^e ≡ p^(e+60) [MOD m] := (step e he).symm
    _ = p^((60+e%60)+60*(e/60)) := by rw [Nat.add_assoc,Nat.mod_add_div,Nat.add_comm]
    _ ≡ _ [MOD m] := steps _ (by omega) _

private def residue (m k a b : ℕ) := (3^(60+a)*7^(60+b)+k+3*m-3)%m

private theorem residue_eq {n a b : ℕ} (eq : n+3=3^a*7^b) (ha : 0<a) (hb : 0<b)
    {m : ℕ} (stable : Stable m) (k : ℕ) :
    (n+k)%m=residue m k (a%60) (b%60) := by
  obtain ⟨mp,c3,c5⟩ := stable
  let w := 3^(60+a%60)*7^(60+b%60)+k
  have d : Nat.ModEq m (n+k+3) w := by
    rw [show n+k+3=(n+3)+k by omega,eq]
    exact ((cycle c3 a ha).mul (cycle c5 b hb)).add_right k
  have add : Nat.ModEq m w (w+3*m) := by
    change w%m=(w+3*m)%m
    rw [Nat.mul_comm 3 m,Nat.add_mul_mod_self_left]
  have strong := Nat.ModEq.add_right_cancel' 3
    (show Nat.ModEq m (n+k+3) (w+3*m-3+3) by rw [Nat.sub_add_cancel (by omega)]; exact d.trans add)
  exact strong

private abbrev RowOK (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable r.q ∧ Stable r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  ∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true

private abbrev CellOK (r : Row) (i j : ℕ) :=
  residue r.q r.k i j=0 ∧ r.mask.testBit (residue r.m r.k i j)=false ∧
  ∀ p : Fin (r.k+1), p.val.Prime → p.val∉r.pool → Stable p.val ∧ residue p.val r.k i j≠0

private theorem smooth {r : Row} (h : RowOK r) (t : ℕ) :
    0<t → (∀ p : ℕ, p.Prime → p∣t → p∈r.pool) → r.mask.testBit (t%r.m)=true := by
  induction t using induction_on_primes with
  | zero => omega
  | one => exact fun _ _ => h.2.2.2.2.2.2.1
  | prime_mul p t pp ih =>
    intro pos sup
    have tt : 0<t := Nat.pos_of_mul_pos_left pos
    have pt := sup p pp (dvd_mul_right p t)
    have good := ih tt (fun q pq d => sup q pq (dvd_mul_of_dvd_right d p))
    have final := h.2.2.2.2.2.2.2 ⟨t%r.m,Nat.mod_lt _ h.2.2.2.2.2.1.1⟩ good p pt
    simpa only [Nat.mod_mul_mod,Nat.mul_comm t p] using final

private theorem exclude {n a b : ℕ} (eq : n+3=3^a*7^b) (ha : 0<a) (hb : 0<b)
    (sol : Erdos889.v_l 1 n=1) {r : Row} (h : RowOK r) (cell : CellOK r (a%60) (b%60)) : False := by
  have qd := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb h.2.2.2.2.1 r.k).trans cell.1)
  have support (p : ℕ) (pp : p.Prime) (dp : p∣n+r.k) : p∈r.pool := by
    by_contra outside
    have ne : r.q≠p := by intro e; exact outside (e ▸ h.2.2.2.1)
    by_cases early : p≤r.k
    · obtain ⟨st,nd⟩ := cell.2.2 ⟨p,by omega⟩ pp outside
      exact nd ((residue_eq eq ha hb st r.k).symm.trans (Nat.mod_eq_zero_of_dvd dp))
    · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes h.2.1 h.1 pp ne h.2.2.1 (by omega) qd dp sol
  have prop := smooth h (n+r.k) (by have := h.2.1; omega) support
  rw [residue_eq eq ha hb h.2.2.2.2.2.1,cell.2.1] at prop
  contradiction

private def rows : List Row := [
  ⟨11,2,[2, 11],7,0x16⟩,
  ⟨11,4,[2, 11],39,0x102510d36⟩,
  ⟨11,4,[2, 11],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  ⟨11,4,[2, 11],465,0x1a25248921865208201a00b08825125060004a2010132c02020034884c30c844b0010100d32020114800182922904434016010412986124492916⟩,
  ⟨11,4,[2, 11],793,0x1a342980230a1004202c12310c000490640032c0082068091290011044c20800e08100152822810012052404a240420808631840410809148092812002051052a002041c00410c8822002522405810400d300098248000c23120d010802143100650b16⟩,
  ⟨11,5,[5, 11],25,0x210863⟩,
  ⟨11,5,[5, 11],39,0x102510d36⟩,
  ⟨11,5,[5, 11],56,0x88a80082002a22⟩,
  ⟨11,6,[2, 3, 11],16,0x1b5f⟩,
  ⟨11,6,[2, 3, 11],31,0x7ffffffe⟩,
  ⟨11,6,[2, 3, 11],244,0xf5b1573199951d115951d993315393b939519933715351171533319d51b5e⟩,
  ⟨11,7,[11],5,0x2⟩,
  ⟨11,8,[2, 11],7,0x16⟩,
  ⟨11,9,[3, 11],35,0x228033a1a⟩,
  ⟨11,10,[2, 5, 7, 11],31,0x7ffffffe⟩,
  ⟨11,10,[2, 5, 7, 11],48,0x1109b2514db6⟩,
  ⟨11,10,[2, 5, 7, 11],400,0x351399bfd37155dd7bb73d1199bbd37917ddffb73d53993bf37157ddfb973551993ff37955ddff973d5399bff37917dd7fb7⟩,
  ⟨11,10,[2, 5, 7, 11],488,0x3513b93ddf531d515975399f1bf11333bb51b5993f79f9fdb3f5dd3913bf27157fd799b1759151d317ddb5fb55737ff15f1dd7b3dbdb9f7b1997d57fb6⟩,
  ⟨13,2,[2, 13],28,0x5113116⟩,
  ⟨13,4,[2, 13],16,0x2737⟩,
  ⟨13,5,[5, 13],175,0x280024220d02040041a00080883400500102a002022⟩,
  ⟨13,5,[5, 13],183,0x4406824020400020424880000112420400020402416022⟩,
  ⟨13,6,[2, 3, 13],61,0x1ffffffffffffffe⟩,
  ⟨13,6,[2, 3, 13],80,0x5511415110b19d05335e⟩,
  ⟨13,7,[13],4,0x2⟩,
  ⟨13,12,[2, 3, 13],31,0x7ffffffe⟩,
  ⟨13,12,[2, 3, 13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨13,12,[2, 3, 13],280,0x10101030ca50805215045990162447185411102301141410ac195045110950d45335e⟩,
  ⟨31,4,[2, 31],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  ⟨31,5,[5, 31],56,0x88a80082002a22⟩,
  ⟨31,7,[31],5,0x2⟩,
  ⟨31,8,[2, 31],273,0x1a24349068860800a25240a01300041264309920800320140929140041845824b0916⟩,
  ⟨31,11,[11, 31],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  ⟨31,12,[2, 3, 31],88,0x30da95967e131cb95977e⟩,
  ⟨31,12,[2, 3, 31],112,0xf59161ab1d034ee58171ab0d135e⟩,
  ⟨31,13,[13, 31],55,0x12081594076396⟩,
  ⟨31,13,[13, 31],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  ⟨31,19,[17, 19, 31],84,0x8000800220828a0822⟩,
  ⟨31,21,[3, 17, 19, 31],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩,
  ⟨31,22,[2, 11, 17, 19, 31],168,0x1109104901321869b0932514914094536582db0d36⟩,
  ⟨31,23,[17, 19, 23, 31],84,0x8000800220828a0822⟩,
  ⟨31,28,[2, 17, 19, 23, 31],15,0x116⟩]
set_option maxHeartbeats 1800000 in
private theorem good : ∀ r ∈ rows, RowOK r := by decide +kernel
private def primes : List ℕ := [11, 13, 31, 61]
private theorem pg : ∀ q ∈ primes, q.Prime ∧ q≤100 ∧ Stable q := by decide +kernel
private def packed : ℕ → ℕ
  | 0 => 0x400001400003c00000400000000003000000400003c0000400000000000300000140000040000400000000000
  | 1 => 0x400001500001100000b00001600000400001c00001100000b00001c00000400001500001100000a000000
  | 2 => 0x1400003c00000800000000003800006400003c00004000000000003800001800003c00004000000000000c0
  | 3 => 0x400001300001100000b00001700000400001300001100000a00001e00000400001300001100000a00001b000
  | 4 => 0x1400003c0000040000000000300000040000080000400000000000300000140000040000400000000000040000
  | 5 => 0x1200001100000900001600000400001500001100000900001c000004000015000011000009000024000004
  | 6 => 0x3c00004000000000003800001800003c00004000000000000c00000800003c0000400000000000380000140
  | 7 => 0x1300001100000900001700000400001300001100000900001f00000400001300001100000900001a000004000
  | 8 => 0x3c00000400000000003000000400003c0000400000000000300000140000040000400000000000040000140000
  | 9 => 0x1100000900001600000400001500001100000900001c00000400002700001100000900002c000004000015
  | 10 => 0x4000000000000c00001800003c00004000000000003800001c00003c00004000000000003800001400003c0
  | 11 => 0x1100000b00001700000400001300001100000a00001e00000400001300001100000a00001b000004000013000
  | 12 => 0x400000000003000000400003c00000800000000003000001400000400004000000000000400001400003c0000
  | 13 => 0xb00001600000400001400001100000b00001c00000400001400001100000a00002b000004000014000011
  | 14 => 0x3800001c00003c00004000000000003800001800000800004000000000000c00001400003c0000400
  | 15 => 0x900001700000400001200001100000900001e00000400001300001100000900001b000004000013000011000
  | 16 => 0x3000000400003c00004000000000003000001400000400004000000000000400000800003c0000040000
  | 17 => 0x1600000400001400001100000900001c000004000014000011000009000020000004000014000011000009
  | 18 => 0x800001800003c00004000000000000c00001800003c00004000000000003800001400003c0000400000000
  | 19 => 0x1700000400001300001100000900001f00000400001300001100000900001a000004000013000011000009000
  | 20 => 0x3000000400003c00004000000000003000001400000400004000000000000400001400003c0000040000000000
  | 21 => 0x400001500001100000b00001c00000400002500001100000a00002a00000400001500001100000b000016
  | 22 => 0x1800003c00004000000000003800001c00003c00000800000000003800001400003c00004000000000000c0
  | 23 => 0x400001300001100000a00001e00000400001300001100000a00001b00000400001300001100000b000017000
  | 24 => 0x400003c0000400000000000300000140000040000400000000000040000140000080000040000000000300000
  | 25 => 0x1c00001100000900001c000004000012000011000009000000000004000015000011000009000016000004
  | 26 => 0x3c00004000000000003800001800003c00004000000000000c00001400003c0000400000000000340000080
  | 27 => 0x1300001100000900001e00000400001300001100000900001b000004000013000011000009000017000004000
  | 28 => 0x3c00004000000000000800001400000400004000000000000400001400003c0000040000000000300000040000
  | 29 => 0x1100000900001c000004000015000011000009000022000004000016000011000009000016000004000015
  | 30 => 0x4000000000000c00001800003c00004000000000003800001400003c00004000000000003800001800003c0
  | 31 => 0x1100000a00001e00000400001300001100000a00001a00000400001300001100000b000017000004000013000
  | 32 => 0x4000000000003000001400000400004000000000000400001400003c00000400000000003000000400003c0000
  | 33 => 0xb00001c00000400001400001100000a00002800000400001400001100000b000016000004000014000011
  | 34 => 0x3800002000003c00004000000000003800001400003c00004000000000000c0000180000080000400
  | 35 => 0x900001d00000400001300001100000900001b000004000012000011000009000017000004000013000011000
  | 36 => 0x3000000800000400004000000000000400001400003c00000400000000003000000400003c0000400000
  | 37 => 0x1c00000400001400001100000900002d000004000014000011000009000016000004000014000011000009
  | 38 => 0x3800001800003c00004000000000000800001400003c00004000000000003800006400003c0000400000000
  | 39 => 0x1f00000400001300001100000900001b000004000013000011000009000017000004000013000011000009000
  | 40 => 0x3000001400000400004000000000000400001400003c00000400000000003000000400003c0000400000000000
  | 41 => 0x400001500001100000a00002900000400001600001100000b00001600000400001500001100000b00001c
  | 42 => 0x1800003c00004000000000003800001400003c00004000000000003800001800003c00000800000000000c0
  | 43 => 0x400001300001100000a00001a00000400001300001100000b00001700000400001300001100000a00001f000
  | 44 => 0x1400000400004000000000000400001400003c00000400000000003000000400003c0000400000000000300000
  | 45 => 0x2c00001100000900002600000400001500001100000900001600000400001200001100000900001c000004
  | 46 => 0x3c00004000000000003400000800003c00004000000000000c00001800003c00004000000000003800001c0
  | 47 => 0x1300001100000900001b00000400001300001100000900001700000400001300001100000900001f000004000
  | 48 => 0x400004000000000000400001400003c00000400000000000800000400003c0000400000000000300000140000
  | 49 => 0x1100000900000000000400001500001100000900001600000400001c00001100000900001c000004000015
  | 50 => 0x4000000000000c00001400003c00004000000000003800006000003c00004000000000003800001800003c0
  | 51 => 0x1100000a00001b00000400001300001100000b00001700000400001300001100000a00001e000004000013000
  | 52 => 0x800000000000400001400003c00000400000000003000000400003c0000400000000000300000140000040000
  | 53 => 0xa00002100000400001400001100000b00001600000400001400001100000b00001c000004000014000011
  | 54 => 0x3800001400000800004000000000003800001800003c00004000000000000c00001800003c0000400
  | 55 => 0x900001a00000400001300001100000900001700000400001300001100000900001f000004000012000011000
  | 56 => 0x400001400003c00000400000000003000000400003c0000400000000000300000140000040000400000
  | 57 => 0x2300000400001400001100000900001600000400001400001100000900001c000004000014000011000009
  | 58 => 0x3800001400003c00004000000000000c00001800003c00004000000000000800002000003c0000400000000
  | 59 => 0x1b00000400001300001100000900001700000400001300001100000900001f000004000013000011000009000
  | _ => 0
private def ix (i j : ℕ) := ((packed i) >>> (6*j))%64
private def qFor (i j : ℕ) := primes[ix i j]?.getD 0
private def rowFor (i j : ℕ) := rows[ix i j-primes.length]?.getD default
private abbrev Test (i j : ℕ) := residue 2 0 i j=0 → residue 3 0 i j=0 → residue 5 0 i j=0 → (i%12≠1 ∨ j%12≠0) →
    (ix i j<primes.length ∧ residue (qFor i j) 1 i j=0) ∨
    (ix i j-primes.length<rows.length ∧ CellOK (rowFor i j) i j)
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block0 : ∀ i∈List.range' 0 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block1 : ∀ i∈List.range' 5 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block2 : ∀ i∈List.range' 10 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block3 : ∀ i∈List.range' 15 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block4 : ∀ i∈List.range' 20 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block5 : ∀ i∈List.range' 25 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block6 : ∀ i∈List.range' 30 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block7 : ∀ i∈List.range' 35 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block8 : ∀ i∈List.range' 40 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block9 : ∀ i∈List.range' 45 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block10 : ∀ i∈List.range' 50 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
private theorem block11 : ∀ i∈List.range' 55 5, ∀ j : Fin 60, Test i j.val := by decide +kernel
private theorem cover {i j : ℕ} (hi : i<60) (hj : j<60) : Test i j := by
  by_cases h0 : i<5
  · exact block0 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h1 : i<10
  · exact block1 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h2 : i<15
  · exact block2 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h3 : i<20
  · exact block3 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h4 : i<25
  · exact block4 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h5 : i<30
  · exact block5 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h6 : i<35
  · exact block6 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h7 : i<40
  · exact block7 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h8 : i<45
  · exact block8 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h9 : i<50
  · exact block9 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h10 : i<55
  · exact block10 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  exact block11 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩

theorem third_residues {n a b : ℕ} (large : 100<n) (prime : (n+1).Prime)
    (eq : n+3=3^a*7^b) (ha : 0<a) (hb : 0<b) (div : 30∣n) (sol : Erdos889.v_l 1 n=1) :
    a%12=1 ∧ b%12=0 := by
  by_contra! bad
  have cell := cover (show a%60<60 by omega) (show b%60<60 by omega)
  have z2 := residue_eq eq ha hb (by decide : Stable 2) 0
  have z3 := residue_eq eq ha hb (by decide : Stable 3) 0
  have z5 := residue_eq eq ha hb (by decide : Stable 5) 0
  have test := cell (by omega) (by omega) (by omega)
  rw [Nat.mod_mod_of_dvd a (by decide : 12∣60),Nat.mod_mod_of_dvd b (by decide : 12∣60)] at test
  rcases test (by omega) with ⟨pi,zero⟩|⟨ri,ok⟩
  · have mem : qFor (a%60) (b%60) ∈ primes := by
      simp only [qFor,List.getElem?_eq_getElem pi,Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨pq,small,st⟩ := pg _ mem
    have dv := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb st 1).trans zero)
    have := (Nat.prime_dvd_prime_iff_eq pq prime).mp dv
    omega
  · have mem : rowFor (a%60) (b%60) ∈ rows := by
      simp only [rowFor,List.getElem?_eq_getElem ri,Option.getD_some]
      exact List.getElem_mem _
    exact exclude eq ha hb sol (good _ mem) ok
end Erdos889.PrimeSevenThree



/- Modular exclusions for a offset 5 supported on 5 and seven. -/
namespace Erdos889.PrimeSevenFive

private structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

private abbrev Stable (m : ℕ) := 0 < m ∧ 5^241%m=5%m ∧ 7^241%m=7%m

private theorem cycle {p m : ℕ} (one : Nat.ModEq m (p^241) p) (e : ℕ) (he : 0<e) :
    Nat.ModEq m (p^e) (p^(240+e%240)) := by
  have step (v : ℕ) (hv : 0<v) : Nat.ModEq m (p^(v+240)) (p^v) := by
    have one' := one.mul_right (p^(v-1))
    rw [←pow_add,show 241+(v-1)=v+240 by omega] at one'
    simpa only [←pow_succ',Nat.sub_add_cancel hv] using one'
  have steps (v : ℕ) (hv : 0<v) (j : ℕ) : Nat.ModEq m (p^(v+240*j)) (p^v) := by
    induction j with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ j ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (step _ (by omega)).trans ih
  calc
    p^e ≡ p^(e+240) [MOD m] := (step e he).symm
    _ = p^((240+e%240)+240*(e/240)) := by rw [Nat.add_assoc,Nat.mod_add_div,Nat.add_comm]
    _ ≡ _ [MOD m] := steps _ (by omega) _

private def residue (m k a b : ℕ) := (5^(240+a)*7^(240+b)+k+5*m-5)%m

private theorem residue_eq {n a b : ℕ} (eq : n+5=5^a*7^b) (ha : 0<a) (hb : 0<b)
    {m : ℕ} (stable : Stable m) (k : ℕ) :
    (n+k)%m=residue m k (a%240) (b%240) := by
  obtain ⟨mp,c3,c5⟩ := stable
  let w := 5^(240+a%240)*7^(240+b%240)+k
  have d : Nat.ModEq m (n+k+5) w := by
    rw [show n+k+5=(n+5)+k by omega,eq]
    exact ((cycle c3 a ha).mul (cycle c5 b hb)).add_right k
  have add : Nat.ModEq m w (w+5*m) := by
    change w%m=(w+5*m)%m
    rw [Nat.mul_comm 5 m,Nat.add_mul_mod_self_left]
  have strong := Nat.ModEq.add_right_cancel' 5
    (show Nat.ModEq m (n+k+5) (w+5*m-5+5) by rw [Nat.sub_add_cancel (by omega)]; exact d.trans add)
  exact strong

private abbrev RowOK (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable r.q ∧ Stable r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  ∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true

private abbrev CellOK (r : Row) (i j : ℕ) :=
  residue r.q r.k i j=0 ∧ r.mask.testBit (residue r.m r.k i j)=false ∧
  ∀ p : Fin (r.k+1), p.val.Prime → p.val∉r.pool → Stable p.val ∧ residue p.val r.k i j≠0

private theorem smooth {r : Row} (h : RowOK r) (t : ℕ) :
    0<t → (∀ p : ℕ, p.Prime → p∣t → p∈r.pool) → r.mask.testBit (t%r.m)=true := by
  induction t using induction_on_primes with
  | zero => omega
  | one => exact fun _ _ => h.2.2.2.2.2.2.1
  | prime_mul p t pp ih =>
    intro pos sup
    have tt : 0<t := Nat.pos_of_mul_pos_left pos
    have pt := sup p pp (dvd_mul_right p t)
    have good := ih tt (fun q pq d => sup q pq (dvd_mul_of_dvd_right d p))
    have final := h.2.2.2.2.2.2.2 ⟨t%r.m,Nat.mod_lt _ h.2.2.2.2.2.1.1⟩ good p pt
    simpa only [Nat.mod_mul_mod,Nat.mul_comm t p] using final

private theorem exclude {n a b : ℕ} (eq : n+5=5^a*7^b) (ha : 0<a) (hb : 0<b)
    (sol : Erdos889.v_l 1 n=1) {r : Row} (h : RowOK r) (cell : CellOK r (a%240) (b%240)) : False := by
  have qd := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb h.2.2.2.2.1 r.k).trans cell.1)
  have support (p : ℕ) (pp : p.Prime) (dp : p∣n+r.k) : p∈r.pool := by
    by_contra outside
    have ne : r.q≠p := by intro e; exact outside (e ▸ h.2.2.2.1)
    by_cases early : p≤r.k
    · obtain ⟨st,nd⟩ := cell.2.2 ⟨p,by omega⟩ pp outside
      exact nd ((residue_eq eq ha hb st r.k).symm.trans (Nat.mod_eq_zero_of_dvd dp))
    · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes h.2.1 h.1 pp ne h.2.2.1 (by omega) qd dp sol
  have prop := smooth h (n+r.k) (by have := h.2.1; omega) support
  rw [residue_eq eq ha hb h.2.2.2.2.2.1,cell.2.1] at prop
  contradiction

private def rows : List Row := [
  ⟨11,2,[2, 11],16,0x1b5f⟩,
  ⟨11,2,[2, 11],17,0x1fffe⟩,
  ⟨11,2,[2, 11],39,0x102510d36⟩,
  ⟨11,2,[2, 11],61,0x1ffffffffffffffe⟩,
  ⟨11,2,[2, 11],117,0x10000010800100100410916⟩,
  ⟨11,2,[2, 11],136,0x1953111d1d1b135905515755131f555b5e⟩,
  ⟨11,2,[2, 11],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  ⟨11,2,[2, 11],241,0x1a246480a08200027002003000005430a8000030010039000104140498916⟩,
  ⟨11,2,[2, 11],244,0x5111151111111111111111111111113119111111111111111111111511916⟩,
  ⟨11,2,[2, 11],248,0x5d535715111d571159135551591d130b1b511f1d5f191511575b135b551f5e⟩,
  ⟨11,3,[3, 11],17,0x1fffe⟩,
  ⟨11,3,[3, 11],31,0x7ffffffe⟩,
  ⟨11,3,[3, 11],36,0xa0a802a0a⟩,
  ⟨11,3,[3, 11],61,0x1434026619900b0a⟩,
  ⟨11,3,[3, 11],68,0x802200828aa02a8a⟩,
  ⟨11,3,[3, 11],91,0x50f01092600000649080f0a⟩,
  ⟨11,3,[3, 11],124,0xa8a202a080a882000822a020a808a2a⟩,
  ⟨11,3,[3, 11],181,0x1717e2151bcfb266b4947840878a4b59937cf62a11fa3a⟩,
  ⟨11,4,[2, 11],7,0x16⟩,
  ⟨11,6,[2, 3, 11],13,0x1ffe⟩,
  ⟨11,6,[2, 3, 11],17,0x1fffe⟩,
  ⟨11,6,[2, 3, 11],32,0xb4f1b5f⟩,
  ⟨11,6,[2, 3, 11],63,0x46578332bc51b5e⟩,
  ⟨11,6,[2, 3, 11],272,0x141110d01030151015103450105114100191301111d19130905015511131b451b5e⟩,
  ⟨11,6,[2, 3, 11],488,0x5511470119150d01494149130153030919411903514341070503110d41054f4b05431909414105051d091305190b031509130705050141531309451b5e⟩,
  ⟨11,6,[2, 3, 11],496,0x19531305111d031109030151191d030b1b410b0d1b191101134b035b010f0a4d03471101095701591355014909130b0b111f194f090511471b130b551b5e⟩,
  ⟨11,6,[2, 3, 11],656,0x109034b0305194519050b190b491b130143091b01550941015713430955030f190313050b4b094f0a1119131b5311091109111f091f190f035113190b05015d11510307131d01131b4d1347115b1b5d1b5e⟩,
  ⟨11,7,[11],5,0x2⟩,
  ⟨11,8,[2, 11],7,0x16⟩,
  ⟨11,9,[3, 11],8,0xa⟩,
  ⟨11,10,[2, 5, 11],39,0x102510d36⟩,
  ⟨11,10,[2, 5, 11],192,0x9a2414ca61009b2514cb60109a2414da61109b2514db6⟩,
  ⟨11,10,[2, 5, 11],448,0xd9e954c3113b728da90187453f26c8f944c3002b629db81187552e36d8e955c3103b728da80186453e26c9f945c3012b629db91186552f36⟩,
  ⟨11,10,[2, 5, 11],816,0x1001100020101004100840001005100b01001a0014c12000130410032110182404500110910114410000112514124100110010500100900010d040101200148041008105144040101904141100101101101000009a2114194110110010494110102510d36⟩,
  ⟨11,10,[2, 5, 11],992,0xfdf357a591bdc6114923e571f81da3ab9a612e0d5e993501d76b035bc48f6eede347b481acd7005933f561e90db3aa8b713f1c4f882511c77a134ad59e7efcf356a590bdc7114823e471f91da2ab9b612f0d5f993401d66b025bc58f6eede247b581add7015932f560e90cb3ab8b703f1d4f892510c77b134bd59f7e⟩,
  ⟨11,10,[2, 5, 11],1008,0x101000101000001000101000000000100800001000109000101000008000001000140000001000100000001004100220001a00100000100804100020009221100100001100001000001101100000001800100000009000100001009000104040000100145000101000100000001220040b0110100010084110102510d36⟩,
  ⟨11,10,[2, 5, 11],1271,0x1021508163300c5176c1a1b4445b123423e2ca4029903cf647175339b52495e600d4eec1cb1c934110dc3c2540fb0ae7d246b476f224b0bc38e2359659223e86c5400a275f9b9e552a1da12f4971f71070650b7a45ab518622051badf55c9e83aa65965398e342f29bb091921db418ae00fd5bc1c4e77d32c72c7480d4ff9842db526315151d9083f66afd2cb83bd23725ddd07a3c9171cff31976f57bf7e⟩,
  ⟨11,10,[2, 5, 11],1281,0x1b2c22d16032c948a0402c22820986136404900526d021224021020b40b40869b09104921900049864a28901345820248101301840201228840368805240a24a2906180810834c245a48004101921b04b4836126020800496890cb04204061825149140928045b00845120100860320204901068b20245149864800261248224365840b40b4102100912102d928024809b2186410510d008144a4d301a2d10d36⟩,
  ⟨11,10,[2, 5, 11],1344,0x8004100221009a00004040100804144820009221008100001220048a0100110104084000082410c260109004001220008a00104040000904144820108220109000101320048b0000000014084100182500c360009004100221009a00104040000804144820009221108100000220049a0100110114084000182410c260009004100220009a00105040000904045820009220108000001320048b0010100014084110182510d36⟩,
  ⟨11,10,[2, 5, 11],1632,0x100020101000000840001000100a01001a0004812000020010022110182004500010800014400000112500124000000010500100900000d040101200148041008101100000101804101000101101001000008a20101841101100104900100020109220001001100020100004100800001005100b00001a0010c020001304000320100824001001109101000100001020141201001100101000009000109000101200108000008004144040101900141100101000101000009a2104190010100010084110102510d36⟩,
  ⟨11,10,[2, 5, 11],1984,0xfdf357a591bdc6114923e571f81ca3ab9a612e0d5e993501d76a035bc48f6eede346b481acd6005933f461e90db3aa8b713f1c4f882511c77a124ad59e7efcf356a590bdc7104823e470f91da2aa9b612f0d5f993401d66b025bc58f6eece247b581add7015832f560e80cb3ab8b703f1d4e892510c67b134bd49f7efdf257a591bcc6114922e571f81da3ab9a602e0d5e983501d76b035bc48e6eede347b481acd7005933f561e90db2aa8b713e1c4f882411c77a134ad59e7efcf356a490bdc7114823e471f91da2ab9b612f0c5f993400d66b025ac58f6eede247b580add7015932f560e90cb3ab8a703f1d4f892510c77b134bd59f7e⟩,
  ⟨13,3,[3, 13],9,0x9b⟩,
  ⟨13,3,[3, 13],41,0x1fffffffffe⟩,
  ⟨13,3,[3, 13],61,0x1713e6940a59f23a⟩,
  ⟨13,3,[3, 13],63,0xc028940844220a⟩,
  ⟨13,3,[3, 13],68,0x802200828aa02a8a⟩,
  ⟨13,3,[3, 13],80,0xa08800220a⟩,
  ⟨13,3,[3, 13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  ⟨13,3,[3, 13],181,0x20602001300926224004000870a4248013cc42a01e22a⟩,
  ⟨13,6,[2, 3, 13],72,0x1a15721b11f05335f⟩,
  ⟨13,6,[2, 3, 13],153,0x100c140685589040a610988f120910d05335e⟩,
  ⟨13,6,[2, 3, 13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨13,6,[2, 3, 13],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  ⟨13,7,[13],4,0x2⟩,
  ⟨13,9,[3, 13],9,0x9b⟩,
  ⟨13,9,[3, 13],17,0x1fffe⟩,
  ⟨13,9,[3, 13],61,0x1713e6940a59f23a⟩,
  ⟨13,9,[3, 13],80,0xa08800220a⟩,
  ⟨13,9,[3, 13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  ⟨13,10,[2, 5, 13],41,0x1fffffffffe⟩,
  ⟨13,10,[2, 5, 13],61,0x1ffffffffffffffe⟩,
  ⟨13,10,[2, 5, 13],112,0x131050301332215211107152736⟩,
  ⟨13,10,[2, 5, 13],204,0x130510132112112504532134114114510030516534136512536⟩,
  ⟨13,10,[2, 5, 13],244,0x7553717517135511113571575331533373117551773131357335157153776⟩,
  ⟨13,10,[2, 5, 13],724,0x1131151111111311715311117117131115333115131111111551111531151111115175171513111331571131131151115133513111115111151351515153311111131111353171157111733711111155353131555311177153776⟩,
  ⟨13,10,[2, 5, 13],732,0x514110510110510110114110132110114110510112110110130514114110014132110110114110114114510110132130134512510112530110110112502110512516130110112130134110530130110110512130114130116112536⟩,
  ⟨13,11,[11, 13],17,0x1fffe⟩,
  ⟨13,11,[11, 13],31,0x7ffffffe⟩,
  ⟨13,11,[11, 13],35,0x228033a1a⟩,
  ⟨13,12,[2, 3, 7, 13],72,0x9e3d72df19f2d73df⟩,
  ⟨13,12,[2, 3, 7, 13],272,0x943310d2dab03f9a5d16745838ff56bce1953211d3dbb13e9a5c17755939fe57bde⟩,
  ⟨13,12,[2, 3, 7, 13],352,0xf79d49f91341d56b21279aa3d919bd4705812f3563cee78d59e90341c57b31378ab3c909ad5705913f2573de⟩,
  ⟨13,12,[2, 3, 7, 13],992,0x943b305650d23b1bd9301d10dad470b6fd1cb8dab29d1a123dbe77b313f8a4d17f751215967e1f9c7458549f9034f2b858fd9ef7d95b5678fa32f756bce1953a315751d33a1ad8311c11dbd570b7fc1db9dbb39c1b133cbf76b212f9a5d07e741314977f1e9d7559559e9134f3b959fc9ff6d85a5779fb33f657bde⟩,
  ⟨13,12,[2, 3, 7, 13],1640,0x5515c1515043350511041105c55106d50589019841010551d011910901d4d111051144412d01414c108541094ab511415908c1a16303404105ab53105521074140178145511411016571020131017154010043311225056d11446511050114059941414075054f69d487252519c2f3014913c44511c5434213112429087595091108031547039871bd650950050d6101543335014306250907218c03158d19500589854010c705014304c7b1c3391c55090311121535c30384910909495461154569124119e97304959d2573de⟩,
  ⟨17,2,[2, 17],16,0x117⟩,
  ⟨17,2,[2, 17],32,0x30117⟩,
  ⟨17,2,[2, 17],36,0x510130116⟩,
  ⟨17,2,[2, 17],91,0x6880c110a40602508830116⟩,
  ⟨17,8,[2, 17],31,0x7ffffffe⟩,
  ⟨17,8,[2, 17],32,0x30117⟩,
  ⟨17,8,[2, 17],61,0x1ffffffffffffffe⟩,
  ⟨17,8,[2, 17],64,0x2000700030117⟩,
  ⟨17,8,[2, 17],91,0x6880c110a40602508830116⟩,
  ⟨17,8,[2, 17],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨17,8,[2, 17],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  ⟨17,10,[2, 5, 17],41,0x1fffffffffe⟩,
  ⟨17,10,[2, 5, 17],61,0x1ffffffffffffffe⟩,
  ⟨17,10,[2, 5, 17],208,0x131271105150331211323132215253305110107253503370736⟩,
  ⟨17,10,[2, 5, 17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  ⟨17,10,[2, 5, 17],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  ⟨17,10,[2, 5, 17],528,0x10120130520012500110412030104110130012102102114032522030112032122110530030124112114010006130110010524112516002500132136030506132536⟩,
  ⟨17,10,[2, 5, 17],671,0x4112107420c52556a305d00b5361936222c9d4b1066e314458e770a2942d21b79491d0da083e2759f0251382cf84f0765602794a96b2f018c5d973018f70d42cb3b83619312f744f38951954fad1d7b37d7fe⟩,
  ⟨17,10,[2, 5, 17],964,0x5151133151775511511357351313715113335115115515511155731515711351113715151111111111513331511331315371715115553311133155113315733131311577117153535331131351111151131131113737171111711175151357733155355315115111135351331717513153355571713331536⟩,
  ⟨17,10,[2, 5, 17],1271,0x1021508163300c5176c1a1b4445b123423e2ca4029903cf647175339b52495e600d4eec1cb1c934110dc3c2540fb0ae7d246b476f224b0bc38e2359659223e86c5400a275f9b9e552a1da12f4971f71070650b7a45ab518622051badf55c9e83aa65965398e342f29bb091921db418ae00fd5bc1c4e77d32c72c7480d4ff9842db526315151d9083f66afd2cb83bd23725ddd07a3c9171cff31976f57bf7e⟩,
  ⟨31,3,[3, 31],9,0x9b⟩,
  ⟨31,4,[2, 31],32,0xd1010117⟩,
  ⟨31,4,[2, 31],63,0x6880800180010116⟩,
  ⟨31,8,[2, 31],41,0x1b382b50736⟩,
  ⟨31,8,[2, 31],64,0x5101000180010117⟩,
  ⟨31,8,[2, 31],119,0x141324470b0970652b11cb15977e⟩,
  ⟨31,11,[11, 31],56,0x88a80082002a22⟩,
  ⟨31,16,[2, 31],41,0x1b382b50736⟩,
  ⟨31,16,[2, 31],48,0x190014116⟩,
  ⟨31,16,[2, 31],63,0x6880800180010116⟩,
  ⟨31,17,[17, 31],16,0x8002⟩,
  ⟨31,17,[17, 31],96,0x800080020002⟩,
  ⟨31,17,[17, 31],123,0x25841b08a0002932122d968a6034c12⟩,
  ⟨31,18,[2, 3, 31],56,0xf59171ab1d135e⟩,
  ⟨31,20,[2, 5, 19, 31],336,0x109004901221869a0832504814094436582cb0d261109104901320869b0932514914084536582db0d36⟩,
  ⟨31,20,[2, 5, 19, 31],544,0x253b0d6501d31f9189a9532dabf7c903e2616f493105875bc5cdfd1779eba38d57a6352b1d7511c30f8189b9433dbbe7d913f2717f592115974bd5cded0769fbb39d47b6⟩,
  ⟨31,20,[2, 5, 19, 31],624,0xdb4532932584c10d24114192502120d92d900b29b00369261908048305005961065349828945a6cb4522832594c10d34014182402130c92d801b29a01369360908149305104961064349929945b6⟩,
  ⟨31,22,[2, 11, 19, 31],168,0x1109104901321869b0932514914094536582db0d36⟩,
  ⟨31,26,[2, 7, 13, 19, 23, 31],1448,0x35339d3553f11fb9393f5f99b1dfd751177b3ddd135d51597519db7f711531b9939dbd7f1f5bf953b11719f31333b359b7bb13f951f5b57d1d93991b3fbb7571d9bf79f9fdf3bddd3177bbf7d5db1995f5393915bb53ff3d933f27177d97117b55bfd7d7b1bddf59b9315533f79995719151d315d9f3b355175fdd7d9f93b5b1fbd17f5535db75737f71df3ff57bd15b1f13959d7dd5f7bff31359dfb3dbdb9b7f9997533ffb3919f5dd1b17d7d51ff17bb79d77b6⟩,
  ⟨31,26,[2, 7, 13, 19, 23, 31],1804,0x3513193513633d993bb5369d95f3515327f57519051cf95b7b1157051939b1179497dd39151babd912b3b1da7f593b57354f11931b37301b197b9d596da1b93fd1b8531d597315c1b9311177fc5f51f3b13ec71d7fb9f37c1d5f137b3f6f99959d93b8d79331cb150b751d95b79a39df99d11d65d15999f334fbd49b77538d55599bd5d0311533f139e9151d1131f2815f531f31a1113fbf755a9bd739b975ad5d913d56583d99d13d75ef7175b797f0bb53b15d31259d5707f59455dbf17913cbd1fb1d75faf39df1353d09f8fdbb3312771fb31b59c339553dd17617db79f77b6⟩,
  ⟨31,27,[3, 19, 23, 31],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩,
  ⟨31,27,[3, 19, 23, 31],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  ⟨31,28,[2, 19, 23, 31],15,0x116⟩,
  ⟨31,29,[19, 23, 29, 31],91,0x30b96010868aa16e3d90272⟩,
  ⟨41,9,[3, 41],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  ⟨41,9,[3, 41],427,0x5040001000400820000040010000001400020008000200800000000000001004000100040002800000080020000041002000800020a⟩,
  ⟨41,10,[2, 5, 41],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  ⟨41,23,[19, 23, 41],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  ⟨61,14,[2, 61],8,0x37⟩,
  ⟨241,10,[2, 5, 241],252,0x516116010114520112110110130430132104130110110110014510102510536⟩]
set_option maxHeartbeats 4500000 in
set_option maxRecDepth 8192 in
private theorem good : ∀ r ∈ rows, RowOK r := by decide +kernel
private def primes : List ℕ := [11, 13, 17, 31, 41, 61, 241]
private theorem pg : ∀ q ∈ primes, q.Prime ∧ q≤1000 ∧ Stable q := by decide +kernel
private def packed : ℕ → ℕ
  | 1 => 0x2419232201001b09133c021923032500010b1405241923222500020801042419232226001c091332011902032600200d144b2419012225001a0e02542419232201001d091104241923030200010b14052419232225001b0901430219232229001c091332011923032700020814042419012225001a0c035f2419022201001d09133c241923032500010b02052419232225001d0901042419232202001c0913320119230326001b0d14490219012225001a0c035824192322010002081304241923032500010b14052419022225001d0901432419232228001c0902320119230327001e0c11042419012202001a060300
  | 3 => 0x1c07113c2419232202000107134d2405232225001b070103020423222b001d0714060119232203000207134b2419012225001a0714032419022201001c07143c2404232203000107024d2405232225001c0701032419232202001d0714330119232203001b0713490204012225001a0714032419232201000207143c2419232203000107134e2405022225001c070103240423222b001d0702330119232203001c07114b2419012202001a0714032419232201001b07143c0204232203000107134e24052322250002070103241923222b001d0714330119022203001c07134b2404012225001a070203241923220100
  | 5 => 0x23222500010d024e2419230525001c0901450319230402001f091430011923222a001b0b12490219012225001a0b13550319232201000208143c241923042500010c124d2406020525001c0901470319232227001e0902300119232226001c0b114b2419010402001a0b13690319232201001b09143c021923222500010c124d241923052500020801470319230426001e091430011902222a001c0b124b2419012225001a0b02520319232201001c09113c241923040200010d124e2419230525001b0901450219232227001f0914300119232226000208124b2419010425001a0b13630319022201001c09143c2419
  | 7 => 0x144c2419022225001d070144240323222f001c070234011923222b000307114b2419012202001a0714802403232201001b07133c0219232225000107144c24192322250002070144240323222d001c071335011902222c000307154b2419012225001a0702512403230601001d07113c2419232202000107144c2419232225001b070144020323222e001c071335011923222b000207164b2419012225001a07145e2403022201001d07133c2419232225000107024c2419232225001d0701442403232202001c071335011923222c00030715490219012225001a0714592403232201000207133c2419232225000107
  | 9 => 0x2500020501462419032228001c0414330119022227001d03134b2419012225001a0b02532419032201001d09113c241923220200010313762419232225001b0501450219032226001c0914330119232226000203134b2419012225001a0415622419022201001d09143c241923222500010302532419232225001e0501452419032202001c0414330119232227001b0313490219012225001a0b15592419032201000208143c2419232225000103134d241902222500200501462419032226001c0902330119232226001d03114b2419012202001a04177b2419032201001b09143c0219232225000103134d24192322
  | 11 => 0x21923032b001e071504011923222b000207034b2419012225001a07135e2419020301001c07153c241923222500010702042419232225001c0701052419230302001e071630011923222b001b0703490219012225001a0713042419230301000207163c2419232225000107034e2419022225001c070105241923032b001f070204011923222b001c07034b2419012202001a07136b2419230301001b07153c0219232225000107030424192322250002060105241923032b001f071530011902222b001c07034b2419012225001a0702042419230301001c07113c2419232202000107034d2419232225001b070105
  | 13 => 0x1d0913360104232226001b0e14030219012225001a0c14562419232201000208133c241923222500010b14032404022225001c0901482405232203001d0902340119232228001c0c11032419012202001a0e146e2404232201001b09133c021923222500010b1403241923222500020801482405232203001d0913360104022226001c0e14032419012225001a0e02522419232201001c09113c241923220200010b14032404232225001b0901450205232203001d091336011923222a00020814032419012225001a0c14602404022201001c091306241923222500010b02032419232225001c090145240523220200
  | 15 => 0x23042c001d07114b0306012202001a0717742419232201001b07123c0219232225000107135503192304250002070144241923052b001c071232011902222c001d07134b0319012225001a0702512419230401001d07113c2419232202000107134d0319232225001b070144021923052d001c071232011923042c000207134b0319012225001a07155e2419022201001d07123c2419232225000107024d031923042500200701442419230502001c071232011923222c001b0713490219012225001a0715592419230401000207123c241923222500010713600319022225001e070144241923052d001c0702320119
  | 17 => 0x154b2403012225001a0b02532419232201000309113c241923220200010d14502403232225001b090145021923062900030915300119232227000208164b2403012225001a0b13602419022201000309143c241923222500010d02502403232225001d090145241923220200030916300119232226001b0b15490203012225001a0b13582419232201000208143c241923222500010c144d2403022225001d090146241923222800030902300119232227001d0b114b2403012202001a0b13712419232201000309143c021923222500010c144d24032322250002080146241923222600030915300119022226001d0b
  | 19 => 0x25001a07145e2419022201001c03133c2419232225000107024c2419032225001c0401442419232202001d031332011923222b001b0714490219012225001a0714592419232201000203133c2419232225000107144c2419022225001c0701442419232240001d030232011923222b001c04114b2419012202001a07147a2419232201001b03133c0219232225000107144c24190322250002040144241923222b001d031332011902222b001c07144b2419012225001a0702512419232201001c03113c2419232202000107144c2419032225001b0701440219232240001d031332011923222b000204144b24190122
  | 21 => 0x2419232201000208033c241923222500010b134d2419020325001c0901042419232227001d0902050119232226001c0b114a2419010302001a0b14662419232201001b090304021923222500010b134d241923032500020801462419232226001d0903050119022229001c0b13042419010325001a0602522419232201001c09033c241923220200010b134e2419230325001b0901040219232227001d0903050119232226000208134a2419010325001a0b145c2419022201001c090304241923222500010b024e2419230325001c0901452419232202001d0903050119232229001b0b13040219010325001a0b1456
  | 23 => 0x1b0714030219232225000107144f24192322030002070144240423222d001c071503010502222c001d07154b2419012203001a0702512419232201001f0711032404232202000107144d2419232203001b070144021923222e001c071503010523222b000207164b2404012203001a07135e2419022201001e0714032419232225000107024d2419232203001d0701442404232202001c071603010523222c001b0715490219012203001a071359241923220100020714032404232225000107144f2419022203001d070144241923222f001c070203010523222b001d07114b2404012202001a07137c241923220100
  | 25 => 0x23220200010b144c2419232225001b0901450219230426001c0913370119230526000208144b2419012225001a0c12602419022201001d09133c031923042500010b024c2419232225001d0901452419232202001c0913370119230527001b0d14490219010425001a0c12592419232201000208133c031923222500010b144c2419022225001d0901462419230426001c0902340119230526001e0c114b2419012202001a0e12722419232201001b09133c021923042500010b144c240623222500020801462419232228001c091337011902052700210d144b2419010425001a0e02542419232201001d09113c0319
  | 27 => 0x24d241923222500030701442419232202001d071432010323222e001b071349021901222500030715572419232201000207163c2403232225000107134e24190222250003070144241923222b001d070232010323222b001c07114b241901220200030717652419232201001b07153c0203232225000107134e24192322250002070144241923222b001d071432010302222e001c07134b241901222500030702512419232201001c07113c2403232202000107134d24192322250003070144021923222b001d071432010323222b000207134b2419012225000307155e2419020601001c07153c2403232225000107
  | 29 => 0x25001c0301472419232226001e0402300119032228001c05114b2419012202001a0313762419232201001b09143c0219032225000104154d241923222500020301472419232227001e0915300119022226001c05144b2419012225001a0302522419232201001c09113c241903220200010f164e2419232225001b0301450219232226001f041530011903222a000205144b2419012225001a0313602419022201001c09143c2419032225000104024e2419232225001c0301452419232202001f0916300119032226001b0514490219012225001a0313562419232201000208143c241903222500010c154d24190222
  | 31 => 0x241923222c001c0713040119020338001e0714052419012225001a0702512419232201001d07113c241923030200010714042419232225001b060144021923222c001c071332011923033800020714052419012225001a0703042419022201001d07133c2419230325000107024c2419232225001d0701422419232202001c0713040119230338001b0714050219012225001a0703592419232201000207133c241923032500010714042419022225001d070144241923222c001c070232011923033800210711052419012202001a0703042419232201001b07133c0219230325000107144c24192322250002070142
  | 33 => 0x1c0914330104232203000208134b2405012225001a0b15032419022201001d09143c241923220300010b024f2404232225001e0901032419232202001c0914330119232203001b0b13490205012225001a0b150324042322010002081406241923220300010b134d2419022225001f0901032419232228001c0902330104232203001d0b114b2405012202001a0b17032419232201001b09143c021923220300010b134d240423222500020801032419232226001c0914330119022203001d0b134b2405012225001a0b02032404232201001d09113c241923220200010b134f2419232225001b090103021923222900
  | 35 => 0x23042b001b0712490219010525001a0713550319232201000207143c2419232225000107124e2419020425001c070144031923222c001f070230011923222b001c07114b2419010502001a0713680319230401001b07143c0219232225000107124e24192322250002070144031923222b001f071430011902042b001c07124b2406010525001a0702510319232201001c07113c2419232202000107124d2419230425001b070144021923222c001e071430011923222b000207124b2419010525001a07135e0319020401001c07143c2419232225000107024d2419232225001c0701440319232202001e0714300119
  | 37 => 0x114b2419012202001a0e17772403232201001b09133c021923222500010b154c241923222500020801462403232226001d091331011902222900030d144b2419012225001a0e02522403232201001c09113c241923220200010b164c2419232225001b0901450203232227001d0913370119232226000208144b2419012225001a0c15602403022201001c09133c241923222500010b024c2419232225001c0901452403230602001d091331011923222900030d14490219012225001a0c15562403232201000208133c241923222500010b154c2419022225001c0901462403232227001d090234011923222600030c
  | 39 => 0x25001a0502512419032201001d07113c2419232202000103134d2419232225001b040144021903222c001c071432011923222c000203134b2419012225001a05145e2419022201001d04143c2419232225000103024d2419232225001f0701442419032202001c071432011923222c001b0313490219012225001a0514592419032201000207143c2419232225000103134f2419022225001e040144241903222c001c070232011923222c001d03114b2419012202001a05147b2419032201001b04143c0219232225000103134f24192322250002070144241903222b001c071432011902222c001d03134b24190122
  | 41 => 0x2419020301001f09153c241923222500010f02502419232225001d0901042419230302001c0916300119232227001b0b03490219012225001a0b130524192303010002081604241923222500010c034d2419022225001d0901462419230326001c0902300119232226001d0b03042419012202001a0b13052419230301001b09153c021923222500010c034d241923222500020801042419230328001c0915300119022227001d0b034b2419012225001a0b02052419230301001e091104241923220200010e03812419232225001b0901450219230326001c091530011923222600020803042419012225001a061305
  | 43 => 0x207133c241923222500010714032419022225001c0701442404232203001d070206011923222b001c0711032419012202001a07186c2405232201001b07133c02042322250001071403241923222500020701442419232203001d071335011902222e001c0714032404012225001a0702512405232201001c07113c241923220200010714032419232225001b0701440204232203001d071335011923222b00020714032419012225001a07155e2405022201001c07133c240423222500010702032419232225001c0701442419232202001d071335011923222e001b0714030204012225001a071558240523220100
  | 45 => 0x23222500010b134d031923222500020801462419230427001d0912330119022226001c0a134b0319012225001a0b02522419230501001c09113c241923040200010b134e0306232225001b0901450219232226001d0912330119232229000208134b0319010425001a0b14602419020501001c09123c241923222500010b024e0319232225001c0901452419230402001d0912330119232226001b0a13490219012225001a0b14562419230501000208123c241923042500010b134d0319022225001c0901462419232226001d0902330119232228001c0a114b0319010402001a0b14732419230501001b09123c0219
  | 47 => 0x164d2403232225001b070144021923222b0003071430011923222b000207144b2403012225001a07135e2419022201000307153c2419232225000107024d2403232225001d07014424192322020003071430011923223b001b0714490203012225001a0713592419230601000207163c2419232225000107154f2403022225001d070144241923222b0003070230011923222b001d07114b2403012202001a07136f2419232201000307153c0219232225000107154f24032322250002070144241923222b00030714300119022239001d07144b2403012225001a0702512419232201000307113c2419232202000107
  | 49 => 0x25001d0901452419232202001c0313370119232226001b1014490219012225001a0c15582419232201000203133c2419232225000104144c2419022225001d0901472419232228001c0302340119232227001e0c114b2419012202001a0417792419232201001b03133c021923222500010b144c241903222500020801472419232226001c0313370119022226002010144b2419012225001a0e02542419232201001d03113c2419232202000104144c2419032225001b0901450219232229001c0313370119232227000208144b2419012225001a0415602419022201001d03133c241923222500010b024c24190322
  | 51 => 0x241923222c001d070204011923222b001c07114a2419010302001a0714662419232201001b0703050219232225000107130424192303250002070144241923222c001d070332011902222b001c07134a2419010325001a0702042419232201001c0703052419232202000107134d2419230325001b070142021923222c001d070304011923222b000207134a2419010325001a07145e2419022201001c070305241923222500010702042419230325001c0601442419232202001d070332011923222b001b0713490219010325001a071404241923220100020703052419232225000107134e2419020325001c070142
  | 53 => 0x1e0914030104022229001c0b144b2419012203001a0b02522419232201001c091103240523220200010d164e2404232203001b0901450219232227001f0914030119232226000208144b2419012203001a0b13602404022201001c091503240523222500010d024e2419232203001c0901452419232202001f0914030104232229001b0b14490219012203001a0b135624192322010002081603240523222500010c154d2404022203001c0901462419232227001e0902030119232226001c0b114b2419012202001a0b137c2404232201001b091503020523222500010c154d24192322030002080146241923222600
  | 55 => 0x23042c000207144b2406012225001a07125e2419022201001d07133c0319230525000107024c2419230425001d0701442419232202001c071332011923222c001b0714490219012225001a0712592419230401000207133c0319230525000107144c2419022225001d070144241923222b001c070232011923042c001f07114b2419012202001a0712722419232201001b07133c0219230525000107144c24192304250002070144241923222c001c071332011902222c001e07144b2419012225001a0702512419230401001d07113c0319230502000107144c2419232225001b070144021923222b001c0713320119
  | 57 => 0x1349021901222500030b14592419232201000208143c240323222500010b134d241902222500030901472419230626001c0902310103232226001d0b114b241901220200030b14652419232201001b09143c020323222500010b134d241923222500020801472419232228001c0915320103022227001d0b134b241901222500030b02532419232201001d09113c240323220200010b1350241923222500030901450219232226001c0915310103232226000208134b241901222500030b14602419022201001d09143c240323222500010b0250241923222500030901452419232202001c0916320103232227001b0b
  | 59 => 0x2001a0313762419232201001b07153c0219032225000105144e24192322250002030144241923223e001f071430011902222b001c07154b2419012225001a0302512419232201001c04113c2419032202000105144d2419232225001b030144021923222b001e071430011903222b000204164b2419012225001a03135e2419022201001c07153c2419032225000105024d2419232225001c0301442419232202001e071430011903222b001b0715490219012225001a0313582419232201000204163c2419032225000105144e2419022225001c030144241923222b001f070230011903222b001c04114b24190122
  | 61 => 0x2419232201001c09113c241923030200010b14052419232225001b0901040219232226001d091332011923032a000208144b2419012225001a0c035c2419022201001c091304241923032500010b02052419232225001c0901432419232202001d0913320119230326001b0d14040219012225001a0603562419232201000208133c241923032500010b14052419022225001c0901042419232226001d0902320119230328001c0c114b2419012202001a0e037f2419232201001b091304021923032500010b1405241923222500020801432419232227001d0913320119020326001c0d14042419012225001a0e0252
  | 63 => 0x1d07143c2419232203000107024d2405232225001f0701032404232202001c0714330119232203001b0713490219012225001a0714032419232201000207143c240423220300010713612405022225001e070103241923222b001c0702330119232203001d07114b2404012202001a0714032419232201001b07143c0219232203000107135024052322250002070103240423222b001c0714060119022203001d07134b2419012225001a0702032419232201001d07113c2404232202000107134d2405232225001b070103021923222b001c0714330119232203000207134b2404012225001a071403241902220100
  | 65 => 0x23222500010c124d2419020525001d0901470319230428001c0902300119232227001d0b114b2419012202001a0b13680319232201001b09143c021923042500010c124d241923052500020801470319232226001c0914300119022226001d0b124b2419010425001a0b02530319232201001e09113c241923220200010d124f2419230525001b0901450219230429001c0914300119232227000208124b2419012225001a0b13640319022201001f09143c241923042500010d024f2406230525001d0901450319232202001c0914300119232226001b0b12490219010425001a0b13550319232201000208143c2419
  | 67 => 0x144c24192322250002070144240323223e001d071335011902222b000307154b2419012225001a0702512403232201001c07113c2419232202000107144c2419232225001b070144020323223f001d071335011923222c000207164b2419012225001a07145e2403022201001c07133c2419232225000107024c2419232225001c0701442403232202001d071335011923222b00030715490219012225001a0714592403232201000207133c2419232225000107144c2419022225001c070144240323223f001d070234011923222c000307114b2419012202001a0714782403230601001b07133c0219232225000107
  | 69 => 0x25001b0501450219032227001d0414330119232226000203134b2419012225001a0b15622419022201001c09143c2419232225000103024e2419232225001c0501452419032202001d0914330119232229001b0313490219012225001a0415562419032201000208143c2419232225000103134d2419022225001c0501462419032227001d0402330119232226001c03114b2419012202001a0b177b2419032201001b09143c0219232225000103134d241923222500020501462419032226001d0914330119022229001c03134b2419012225001a0402522419032201001c09113c2419232202000103134e24192322
  | 71 => 0x2419230302001c071604011923222b001b0703490219012225001a0713592419230301000207163c241923222500010703042419022225001d060105241923032b001c070230011923222b001d07034b2419012202001a0713042419230301001b07153c0219232225000107034f24192322250002070105241923032b001c071504011902222b001d07034b2419012225001a0702512419230301001f07113c241923220200010703042419232225001b070105021923032b001c071530011923222b000207034b2419012225001a0713042419020301001e07153c2419232225000107024d2419232225001d070105
  | 73 => 0x1c0902340104232226001e0c11032419012202001a0e146e2419232201001b09133c021923222500010b1403240423222500020801482405232203001c0913360119022227001f0f14032419012225001a0e02542404232201001d091106241923220200010b14032419232225001b0901450205232203001c091336010423222600020814032419012225001a0c14602419022201001d09133c241923222500010b02032404232225001d0901452405232202001c0913360119232227001b0e14030219012225001a0c14592404232201000208133c241923222500010b14032419022225001d090148240523220300
  | 75 => 0x2042c001c07134b0319012225001a0702512419232201001c07113c2419232202000107134d0319230425001b070144021923052b001d071232011923222c000207134b0319012225001a07155e2419020401001c07123c2419232225000107024d0319232225001c0701442419230502001d071232011923042c001b0713490206012225001a0715582419232201000207123c2419232225000107134e0319020425001c070144241923052b001d070232011923222c001c07114b0319012202001a0717752419230401001b07123c0219232225000107134e03192322250002070144241923053d001d0712320119
  | 77 => 0x164b2403012225001a0b13602419022201000309143c241923222500010d024e2403232225001c090145241923220200030916300119232226001b0b15490203012225001a0b13562419232201000208143c241923222500010c144d2403022225001c090146241923222600030902300119232228001c0b114b2403012202001a0b13702419232201000309143c021923222500010c144d24032322250002080146241923062700030915300119022226001c0b154b2403012225001a0b02522419232201000309113c241923220200010d144e2403232225001b090145021923222600030915300119232229000208
  | 79 => 0x25001a0714592419232201000203133c2419232225000107144c2419022225001d040144241923222b001c030232011923222b001f07114b2419012202001a07147a2419232201001b03133c0219232225000107144c24190322250002070144241923223e001c031332011902222b001e04144b2419012225001a0702512419232201001d03113c2419232202000107144c2419032225001b040144021923222b001c031332011923222b000207144b2419012225001a07145e2419022201001d03133c2419232225000107024c2419032225001d0701442419232202001c031332011923222b001b04144902190122
  | 81 => 0x2419232201001b09033c021923222500010b134d241923032500020801042419232226001c0903050119022226001d0b134a2419010325001a0b02532419232201001d090304241923220200010b134f2419230325001b0901450219232229001c090305011923222700020813042419010325001a0b145f2419022201001d09033c241923222500010b024f2419230325001e0901042419232202001c0903050119232226001b0b13490219010325001a0b145824192322010002080304241923222500010b134d2419020325001f0901462419232228001c0902050119232227001d0b11042419010302001a061467
  | 83 => 0x1c0711032419232202000107144d2419232203001b070144020423223f001e071503010523222c000207164b2419012203001a07135e2419022201001c0714032404232225000107024d2419232203001c0701442419232202001e071603010523222b001b0715490204012203001a071359241923220100020714032419232225000107144e2419022203001c070144240423223f001f070203010523222c001c07114b2419012202001a07137c2419232201001b0714030204232225000107144e24192322030002070144241923223e001f071503010502222b001c07154b2404012203001a070251241923220100
  | 85 => 0x23222500010b024c2419232225001c0901452419230402001d0913370119230529001b0d14490219012225001a0c12562419232201000208133c031923042500010b144c2406022225001c0901462419232227001d0902340119230526001c0c114b2419010402001a0e12722419232201001b09133c021923222500010b144c241923222500020801462419230426001d0913370119020529001c0d144b2419012225001a0e02522419232201001c09113c031923040200010b144c2419232225001b0901450219232227001d0913370119230526000208144b2419010425001a0c12602419022201001c09133c0319
  | 87 => 0x134f24190222250003070144241923222b001c070232010323223a001d07114b241901220200030717652419232201001b07153c0203232225000107134f24192322250002070144241923222b001c071432010302222b001d07134b241901222500030702512419230601001d07113c2403232202000107134d24192322250003070144021923222b001c071432010323223a000207134b2419012225000307155e2419022201001d07153c2403232225000107024d241923222500030701442419232202001c071432010323222b001b071349021901222500030715572419232201000207163c2403232225000107
  | 89 => 0x2500020301472419232228001c0415300119022227001d05144b2419012225001a0302532419232201001e09113c2419032202000104164f2419232225001b0301450219232226001c0915300119032226000205144b2419012225001a0313602419022201001f09143c241903222500010e024f2419232225001d0301452419232202001c0416300119032227001b0514490219012225001a0313592419232201000208143c2419032225000104154d2419022225001d0301472419232226001c0902300119032226001d05114b2419012202001a0313762419232201001b09143c021903222500010c154d24192322
  | 91 => 0x21923222c001d071304011923032d00020714052419012225001a07035d2419022201001c07133c241923032500010702042419232225001c0701442419232202001d071332011923032e001b0714050219012225001a0703042419232201000207133c2419230325000107144c2419022225001c070142241923222c001d070204011923032d001c0711052419012202001a07037e2419232201001b07133c0219230325000107140424192322250002060144241923222c001d071332011902032e001c0714052419012225001a0702042419232201001c07113c2419230302000107144c2419232225001b070142
  | 93 => 0x1d0914330104232203001b0b13490205012225001a0b15032419232201000208143c241923220300010b134d2404022225001c0901032419232226001d0902330119232203001c0b114b2405012202001a0b17032404232201001b09143c021923220300010b134d241923222500020801032419232227001d0914330104022203001c0b134b2405012225001a0b02032419232201001c09113c241923220200010b134e2404232225001b0901030219232226001d0914330119232203000208134b2405012225001a0b15032404022201001c091406241923220300010b024e2419232225001c090103241923220200
  | 95 => 0x23042b001d07114b2406010502001a0713680319232201001b07143c0219232225000107125b24192304250002070144031923222c001c071430011902222b001d07124b2419010525001a0702510319230401001f07113c2419232202000107124d2419232225001b070144021923222b001c071430011923042b000207124b2419010525001a07135e0319022201001e07143c2419232225000107024d2419230425001d0701440319232202001c071430011923222b001b0712490219010525001a0713550319230401000207143c241923222500010712612419022225001d070144031923222b001c0702300119
  | 97 => 0x144b2419012225001a0e02542403232201001d09113c241923220200010b164c2419232225001b0901450203230641001c0913310119232227000208144b2419012225001a0c15602403022201001d09133c241923222500010b024c2419232225001d0901452403232202001c091337011923222600030d14490219012225001a0c15582403232201000208133c241923222500010b154c2419022225001d0901462403232228001c090231011923222700030c114b2419012202001a0e17772403232201001b09133c021923222500010b154c241923222500020801462403232226001c091337011902222600030d
  | 99 => 0x25001a05145e2419022201001c07143c2419232225000103024d2419232225001c0401442419032202001d071432011923222c001b0313490219012225001a0514592419032201000204143c2419232225000103134e2419022225001c070144241903222b001d070232011923222c001c03114b2419012202001a05147b2419032201001b07143c0219232225000103134e24192322250002040144241903222c001d071432011902222c001c03134b2419012225001a0502512419032201001c04113c2419232202000103134d2419232225001b070144021903222b001d071432011923222c000203134b24190122
  | 101 => 0x2419230301000208163c241923222500010c034d2419022225001c0901042419230327001e0902300119232226001c0b034b2419012202001a0b13052419230301001b091504021923222500010c034d241923222500020801462419230326001e0915300119022229001c0b03042419012225001a0602052419230301001c09113c241923220200010f034e2419232225001b0901040219230327001f0915300119232226000208034b2419012225001a0b13052419020301001c091504241923222500010e024e2419232225001c0901452419230302001f0916300119232229001b0b03040219012225001a0b1305
  | 103 => 0x1b07133c02192322250001071403241923222500020701442404232203001c071335011902222b001e0714032419012225001a0702512405232201001d07113c240423220200010714032419232225001b0701440219232203001c071335011923223800020714032404012225001a07155e2405022201001d07133c241923222500010702032419232225001d0701442404232202001c071306011923222b001b0714030219012225001a0715592405232201000207133c240423222500010714032419022225001d0701442419232203001c0702340119232238001f0711032404012202001a07186d240523220100
  | 105 => 0x23220200010b134f0319232225001b0901450219230426001c0912330119232226000208134b0319012225001a0b14602419020501001d09123c241923042500010b024f0319232225001e0901452419232202001c0912330119232227001b0a13490219010425001a0b14592419230501000208123c241923222500010b134d031902222500210901462419230426001c0902330119232226001d0a114b0319012202001a0b14732419230501001b09123c021923042500010b134d030623222500020801462419232228001c0912330119022227001d0a134b0319010425001a0b02532419230501001d09113c2419
  | 107 => 0x24d2403232225001c07014424192322020003071430011923222b001b0714490203012225001a0713582419232201000207163c2419232225000107154e2403022225001c070144241923222b0003070230011923222d001c07114b2403012202001a07136f2419232201000307153c0219232225000107154e24032322250002070144241923222b0003071430011902222b001c07144b2403012225001a0702512419232201000307113c2419232202000107164d2403232225001b070144021923222b0003071430011923222d000207144b2403012225001a07135e2419020601000307153c2419232225000107
  | 109 => 0x25001c0901472419232226001d0302340119232228001c0c114b2419012202001a0e17792419232201001b03133c0219232225000104144c241903222500020801472419232227001d0313370119022226001c10144b2419012225001a0402522419232201001c03113c241923220200010b144c2419032225001b0901450219232226001d031337011923222a000208144b2419012225001a0c15602419022201001c03133c2419232225000104024c2419032225001c0901452419232202001d0313370119232226001b0e14490219012225001a0415562419232201000203133c241923222500010b144c24190222
  | 111 => 0x241923222c001c070304011902222b001d07134a2419010325001a0702512419232201001d070305241923220200010713042419230325001b060144021923222c001c070332011923222b000207134a2419010325001a0714042419022201001d0703052419232225000107024d241923032500210701422419232202001c070304011923222b001b0713490219010325001a07145924192322010002070305241923222500010713042419020325001e070144241923222c001c070232011923222b001d07114a2419010302001a0714042419232201001b0703050219232225000107135a24192303250002070142
  | 113 => 0x1c0914030104232227000208144b2419012203001a0b13602419022201001f091503240523222500010d02502404232203001d0901452419232202001c0914030119232226001b0b14490219012203001a0b135824042322010002081603240523222500010c154d2419022203001d0901462419232228001c0902030104232227001d0b114b2419012202001a0b137c2419232201001b091503020523222500010c154d240423220300020801462419232226001c0914030119022226001d0b144b2419012203001a0b02532404232201001e091103240523220200010d16502419232203001b090145021923222a00
  | 115 => 0x23042c001b0714490219012225001a0712592419232201000207133c0319230525000107144c2419020425001c070144241923222c001d070232011923222c001c07114b2419012202001a0712722419230401001b07133c0219230525000107144c24192322250002070144241923222b001d071332011902042c001c07144b2406012225001a0702512419232201001c07113c0319230502000107144c2419230425001b070144021923222c001d071332011923222c000207144b2419012225001a07125e2419020401001c07133c0319230525000107024c2419232225001c0701442419232202001d0713320119
  | 117 => 0x114b241901220200030b14652419232201001b09143c020323222500010b134d241923222500020801472419232226001d091531010302223a001c0b134b241901222500030b02522419232201001c09113c240323220200010b134e241923222500030901450219232227001d0915320103232226000208134b241901222500030b14602419022201001c09143c240323222500010b024e241923222500030901452419230602001d091631010323223a001b0b1349021901222500030b14562419232201000208143c240323222500010b134d241902222500030901472419232227001d0902320103232226001c0b
  | 119 => 0x25001a0302512419232201001f07113c2419032202000105144d2419232225001b030144021923222e001c071430011903222b000207164b2419012225001a03135e2419022201001e04153c2419032225000105024d2419232225001d0301442419232202001c071430011903222b001b0415490219012225001a0313592419232201000207163c241903222500010514502419022225001d030144241923222f001c070230011903222b001d07114b2419012202001a0313762419232201001b04153c0219032225000105145024192322250002030144241923222b001c071430011902222b001d04154b24190122
  | 121 => 0x2419022201001d09133c241923032500010b02052419232225001d0901042419232202001c0913320119230327001b0d14490219012225001a0c035924192322010002081304241923032500010b14052419022225001d0901432419232226001c0902320119230326001e0c11042419012202001a0e03822419232201001b09133c021923032500010b1405241923222500020801042419232228001c091332011902032700200d144b2419012225001a0e02542419232201001d091104241923030200010b14052419232225001b0901430219232226001c091332011923032600020814042419012225001a060360
  | 123 => 0x207143c2419232203000107134e2405022225001c070103240423222b001d0702060119232203001c07114b2419012202001a0714032419232201001b07143c0204232203000107134e24052322250002070103241923222b001d0714330119022203001c07134b2404012225001a0702032419232201001c07113c2419232202000107134d2405232225001b070103020423222b001d0714330119232203000207134b2419012225001a0714032419022201001c07143c2404232203000107024d2405232225001c0701032419232202001d0714330119232203001b0713490204012225001a071403241923220100
  | 125 => 0x23222500010c124d241923052500020801470319230427001e0914300119022226001c0b124b2419012225001a0b02520319232201001c09113c241923040200010d124e2406230525001b0901450219232226001f091430011923222a000208124b2419010425001a0b13630319022201001c09143c241923222500010d024e2419230525001c0901450319230402001f0914300119232226001b0b12490219012225001a0b13550319232201000208143c241923042500010c124d2419020525001c0901470319232226001e0902300119232228001c0b114b2419010402001a0b136a0319232201001b09143c0219
  | 127 => 0x144c2419232225001b070144020323222d001c071335011923222b000207164b2419012225001a07145e2403022201001d07133c2419232225000107024c2419232225001d0701442403232202001c071335011923222c00030715490219012225001a0714592403230601000207133c2419232225000107144c2419022225001d070144240323222d001c070234011923222b000307114b2419012202001a0714802403232201001b07133c0219232225000107144c24192322250002070144240323222f001c071335011902222c000307154b2419012225001a0702512403232201001d07113c2419232202000107
  | 129 => 0x25001e0501452419032202001c0414330119232226001b0313490219012225001a0b15582419032201000208143c2419232225000103134d241902222500200501462419032228001c0902330119232227001d03114b2419012202001a04177b2419032201001b09143c0219232225000103134d241923222500020501462419032226001c0414330119022226001d03134b2419012225001a0b02532419032201001d09113c241923220200010313762419232225001b050145021903222a001c0914330119232227000203134b2419012225001a0415622419022201001d09143c2419232225000103025324192322
  | 131 => 0x241923032b001f070204011923222b001c07034b2419012202001a07136b2419230301001b07153c0219232225000107030424192322250002070105241923032b001f071530011902222b001c07034b2419012225001a0702042419230301001c07113c2419232202000107034d2419232225001b070105021923032b001e071504011923222b000207034b2419012225001a07135e2419020301001c07153c241923222500010702042419232225001c0601052419230302001e071630011923222b001b0703490219012225001a0713042419230301000207163c2419232225000107034e2419022225001c070105
  | 133 => 0x1d091336010402222a001c0e14032419012225001a0e02522419232201001c09113c241923220200010b14032404232225001b0901450205232203001d091336011923222600020814032419012225001a0c14602404022201001c09133c241923222500010b02032419232225001c0901452405232202001d091336010423222a001b0e14030219012225001a0c14562419232201000208133c241923222500010b14032404022225001c0901482405232203001d0902340119232226001c0c11032419012202001a0e146e2404232201001b091306021923222500010b140324192322250002080148240523220300
  | 135 => 0x23042c000207134b0306012225001a07155e2419022201001d07123c2419232225000107024d031923042500200701442419230502001c071232011923222c001b0713490219012225001a0715592419230401000207123c241923222500010713600319022225001e070144241923052f001c070232011923042c001d07114b0319012202001a0717742419232201001b07123c0219232225000107135503192304250002070144241923052b001c071232011902222c001d07134b0319012225001a0702512419230401001d07113c2419232202000107134d0319232225001b070144021923052e001c0712320119
  | 137 => 0x15490203012225001a0b13592419232201000208143c241923222500010c144d2403022225001d090146241923062600030902300119232226001d0b114b2403012202001a0b13712419232201000309143c021923222500010c144d24032322250002080146241923222800030915300119022227001d0b154b2403012225001a0b02532419232201000309113c241923220200010d14502403232225001b090145021923222600030915300119232226000208164b2403012225001a0b13602419022201000309143c241923222500010d02502403232225001d090145241923220200030916300119232227001b0b
  | 139 => 0x2001a07147a2419232201001b03133c0219232225000107144c24190322250002040144241923222b001d031332011902222b001c07144b2419012225001a0702512419232201001c03113c2419232202000107144c2419032225001b0701440219232240001d031332011923222b000204144b2419012225001a07145e2419022201001c03133c2419232225000107024c2419032225001c0401442419232202001d031332011923222b001b0714490219012225001a0714582419232201000203133c2419232225000107144c2419022225001c0701442419232240001d030232011923222b001c04114b24190122
  | 141 => 0x2419232201001c09033c241923220200010b134e2419230325001b0901040219232226001d0903050119232229000208134a2419010325001a0b145c2419022201001c090304241923222500010b024e2419230325001c0901452419232202001d0903050119232226001b0b13040219010325001a0614562419232201000208033c241923222500010b134d2419020325001c0901042419232226001d0902050119232228001c0b114a2419010302001a0b14662419232201001b090304021923222500010b134d241923032500020801462419232227001d0903050119022226001c0b13042419010325001a0b0252
  | 143 => 0x1e0714032419232225000107024d2419232203001d0701442404232202001c071603010523222c001b0715490219012203001a071359241923220100020714032404232225000107144f2419022203001d070144241923222d001c070203010523222b001d07114b2404012202001a07137c2419232201001b0714030219232225000107144f24192322030002070144240423222f001c071503010502222c001d07154b2419012203001a0702512419232201001f0711032404232202000107144d2419232203001b070144021923222d001c071503010523222b000207164b2404012203001a07135e241902220100
  | 145 => 0x23222500010b144c2419022225001d0901462419230428001c0902340119230527001e0c114b2419012202001a0e12722419232201001b09133c021923042500010b144c241923222500020801462419232226001c091337011902052600210d144b2419010425001a0e02542419232201001d09113c031923220200010b144c2419232225001b0901450219230429001c0913370119230527000208144b2419012225001a0c12602419022201001d09133c031923042500010b024c2406232225001d0901452419232202001c0913370119230526001b0d14490219010425001a0c12582419232201000208133c0319
  | 147 => 0x134e24192322250002070144241923222b001d071432010302222d001c07134b241901222500030702512419232201001c07113c2403232202000107134d24192322250003070144021923222b001d071432010323222b000207134b2419012225000307155e2419022201001c07153c2403232225000107024d241923222500030701442419232202001d071432010323222d001b071349021901222500030715572419232201000207163c2403232225000107134e24190222250003070144241923222b001d070232010323222b001c07114b241901220200030717652419230601001b07153c0203232225000107
  | 149 => 0x25001b0301450219232227001f0415300119032226000205144b2419012225001a0313602419022201001c09143c2419032225000104024e2419232225001c0301452419232202001f091630011903222a001b0514490219012225001a0313562419232201000208143c241903222500010c154d2419022225001c0301472419232227001e0402300119032226001c05114b2419012202001a0313762419232201001b09143c0219032225000104154d241923222500020301472419232226001e091530011902222a001c05144b2419012225001a0302522419232201001c09113c241903220200010e164e24192322
  | 151 => 0x2419232202001c0713040119230338001b0714050219012225001a0703592419232201000207133c241923032500010714042419022225001d060144241923222c001c070232011923033800210711052419012202001a0703042419232201001b07133c0219230325000107144c24192322250002070142241923222c001c0713040119020338001e0714052419012225001a0702512419232201001d07113c241923030200010714042419232225001b070144021923222c001c071332011923033800020714052419012225001a0703042419022201001d07133c2419230325000107024c2419232225001d070142
  | 153 => 0x1c0902330104232203001d0b114b2405012202001a0b17032419232201001b09143c021923220300010b134d240423222500020801032419232228001c0914330119022203001d0b134b2405012225001a0b02032404232201001d091106241923220200010b134f2419232225001b0901030219232226001c0914330104232203000208134b2405012225001a0b15032419022201001d09143c241923220300010b024f2404232225001e0901032419232202001c0914330119232203001b0b13490205012225001a0b15032404232201000208143c241923220300010b134d2419022225001f090103241923222600
  | 155 => 0x2042b001c07124b2419010525001a0702510319232201001c07113c2419232202000107124d2419230425001b070144021923222c001e071430011923222b000207124b2419010525001a07135e0319020401001c07143c2419232225000107024d2419232225001c0701440319232202001e071430011923042b001b0712490206010525001a0713550319232201000207143c2419232225000107124e2419020425001c070144031923222c001f070230011923222b001c07114b2419010502001a0713680319230401001b07143c0219232225000107124e24192322250002070144031923222b001f0714300119
  | 157 => 0x144b2419012225001a0c15602403022201001c09133c241923222500010b024c2419232225001c0901452403232202001d091331011923222600030d14490219012225001a0c15562403232201000208133c241923222500010b154c2419022225001c0901462403232226001d090234011923222800030c114b2419012202001a0e17772403232201001b09133c021923222500010b154c241923222500020801462403230627001d091331011902222600030d144b2419012225001a0e02522403232201001c09113c241923220200010b164c2419232225001b0901450203232226001d0913370119232229000208
  | 159 => 0x25001a0514592419032201000207143c2419232225000103134f2419022225001e040144241903222c001c070232011923222c001d03114b2419012202001a05147b2419032201001b04143c0219232225000103134f24192322250002070144241903222b001c071432011902222c001d03134b2419012225001a0502512419032201001d07113c2419232202000103134d2419232225001b040144021903222c001c071432011923222c000203134b2419012225001a05145e2419022201001d04143c2419232225000103024d2419232225001f0701442419032202001c071432011923222c001b03134902190122
  | 161 => 0x2419230301001b09153c021923222500010c034d241923222500020801042419230326001c0915300119022226001d0b034b2419012225001a0b02052419230301001e091104241923220200010e03812419232225001b090145021923032a001c091530011923222700020803042419012225001a0b13052419020301001f09153c241923222500010f02502419232225001d0901042419230302001c0916300119232226001b0b03490219012225001a0b130524192303010002081604241923222500010c034d2419022225001d0901462419230328001c0902300119232227001d0b03042419012202001a061305
  | 163 => 0x1c07113c241923220200010714032419232225001b0701440204232203001d071306011923222b00020714032419012225001a07155e2405022201001c07133c240423222500010702032419232225001c0701442419232202001d071335011923222d001b0714030204012225001a0715592405232201000207133c241923222500010714032419022225001c0701442404232203001d070234011923222b001c0711032419012202001a07186c2405232201001b07133c02042322250001071403241923222500020701442419232203001d071335011902222d001c0714032404012225001a070251240523220100
  | 165 => 0x23222500010b024e0319232225001c0901452419230402001d0912330119232229001b0a13490219012225001a0b14562419230501000208123c241923042500010b134d0306022225001c0901462419232227001d0902330119232226001c0a114b0319010402001a0b14732419230501001b09123c021923222500010b134d031923222500020801462419230426001d0912330119022229001c0a134b0319012225001a0b02522419230501001c09113c241923040200010b134e0319232225001b0901450219232227001d0912330119232226000208134b0319010425001a0b14602419020501001c09123c2419
  | 167 => 0x154f2403022225001d070144241923222b0003070230011923222b001d07114b2403012202001a07136f2419232201000307153c0219232225000107154f24032322250002070144241923222b00030714300119022239001d07144b2403012225001a0702512419230601000307113c2419232202000107164d2403232225001b070144021923222b0003071430011923222b000207144b2403012225001a07135e2419022201000307153c2419232225000107024d2403232225001d07014424192322020003071430011923223b001b0714490203012225001a0713592419232201000207163c2419232225000107
  | 169 => 0x2500020801472419232228001c0313370119022227002010144b2419012225001a0e02542419232201001d03113c2419232202000104144c2419032225001b0901450219232226001c0313370119232226000208144b2419012225001a0415602419022201001d03133c241923222500010b024c2419032225001d0901452419232202001c0313370119232227001b1014490219012225001a0c15592419232201000203133c2419232225000104144c2419022225001d0901472419232226001c0302340119232226001e0c114b2419012202001a0417792419232201001b03133c021923222500010b144c24190322
  | 171 => 0x21923222c001d070304011923222b000207134a2419010325001a07145e2419022201001c070305241923222500010702042419230325001c0701442419232202001d070332011923222b001b0713490219010325001a071404241923220100020703052419232225000107134e2419020325001c070142241923222c001d070204011923222b001c07114a2419010302001a0714662419232201001b0703050219232225000107130424192303250002060144241923222c001d070332011902222b001c07134a2419010325001a0702042419232201001c0703052419232202000107134d2419230325001b070142
  | 173 => 0x1f0914030104232226001b0b14490219012203001a0b135624192322010002081603240523222500010c154d2404022203001c0901462419232226001e0902030119232228001c0b114b2419012202001a0b137c2404232201001b091503020523222500010c154d241923220300020801462419232227001e0914030104022226001c0b144b2419012203001a0b02522419232201001c091103240523220200010d164e2404232203001b0901450219232226001f0914030119232229000208144b2419012203001a0b13602404022201001c091503240523222500010d024e2419232203001c090145241923220200
  | 175 => 0x23042c001f07114b2406012202001a0712722419232201001b07133c0219230525000107144c24192304250002070144241923222c001c071332011902222c001e07144b2419012225001a0702512419230401001d07113c0319230502000107144c2419232225001b070144021923222b001c071332011923042c000207144b2419012225001a07125e2419022201001d07133c0319230525000107024c2419230425001d0701442419232202001c071332011923222c001b0714490219012225001a0712592419230401000207133c0319230525000107144c2419022225001d070144241923222b001c0702320119
  | 177 => 0x134b241901222500030b02532419232201001d09113c240323220200010b1350241923222500030901450219230629001c0915310103232227000208134b241901222500030b14602419022201001d09143c240323222500010b0250241923222500030901452419232202001c0916320103232226001b0b1349021901222500030b14582419232201000208143c240323222500010b134d241902222500030901472419232228001c0902310103232227001d0b114b241901220200030b14652419232201001b09143c020323222500010b134d241923222500020801472419232226001c0915320103022226001d0b
  | 179 => 0x25001a03135e2419022201001c07153c2419032225000105024d2419232225001c0301442419232202001e071430011903222b001b0715490219012225001a0313592419232201000204163c2419032225000105144e2419022225001c030144241923222b001f070230011903222b001c04114b2419012202001a0313762419232201001b07153c0219032225000105144e24192322250002030144241923223e001f071430011902222b001c07154b2419012225001a0302512419232201001c04113c2419032202000105144d2419232225001b030144021923222b001e071430011903222b000204164b24190122
  | 181 => 0x2419232201000208133c241923032500010b14052419022225001c0901042419232227001d0902320119230326001c0c114b2419012202001a0e037f2419232201001b091304021923032500010b1405241923222500020801432419232226001d091332011902032a001c0d14042419012225001a0602522419232201001c09113c241923030200010b14052419232225001b0901040219232227001d0913320119230326000208144b2419012225001a0c035c2419022201001c091304241923032500010b02052419232225001c0901432419232202001d091332011923032a001b0d14040219012225001a0c0356
  | 183 => 0x1b07143c0219232203000107135024052322250002070103240423222b001c0714330119022203001d07134b2419012225001a0702032419232201001d07113c2404232202000107134d2405232225001b070103021923222b001c0714330119232203000207134b2404012225001a0714032419022201001d07143c2419232203000107024d2405232225001f0701032404232202001c0714060119232203001b0713490219012225001a0714032419232201000207143c240423220300010713612405022225001e070103241923222b001c0702330119232203001d07114b2404012202001a071403241923220100
  | 185 => 0x23220200010d124f2419230525001b0901450219230426001c0914300119232226000208124b2419012225001a0b13640319022201001f09143c241923042500010d024f2419230525001d0901450319232202001c0914300119232227001b0b12490219010425001a0b13550319232201000208143c241923222500010c124d2419020525001d0901470319230426001c0902300119232226001d0b114b2419012202001a0b13680319232201001b09143c021923042500010c124d240623052500020801470319232228001c0914300119022227001d0b124b2419010425001a0b02530319232201001e09113c2419
  | 187 => 0x24c2419232225001c0701442403232202001d071335011923222b00030715490219012225001a0714582403232201000207133c2419232225000107144c2419022225001c070144240323223f001d070234011923222c000307114b2419012202001a0714782403232201001b07133c0219232225000107144c24192322250002070144240323223e001d071335011902222b000307154b2419012225001a0702512403232201001c07113c2419232202000107144c2419232225001b070144020323223f001d071335011923222c000207164b2419012225001a07145e2403020601001c07133c2419232225000107
  | 189 => 0x25001c0501462419032226001d0402330119232228001c03114b2419012202001a0b177b2419032201001b09143c0219232225000103134d241923222500020501462419032227001d0914330119022226001c03134b2419012225001a0402522419032201001c09113c2419232202000103134e2419232225001b0501450219032226001d0414330119232229000203134b2419012225001a0b15622419022201001c09143c2419232225000103024e2419232225001c0501452419032202001d0914330119232226001b0313490219012225001a0415562419032201000208143c2419232225000103134d24190222
  | 191 => 0x241923032b001c071504011902222b001d07034b2419012225001a0702512419230301001f07113c241923220200010703042419232225001b060105021923032b001c071530011923222b000207034b2419012225001a0713042419020301001e07153c2419232225000107024d2419232225001d0701052419230302001c071604011923222b001b0703490219012225001a0713592419230301000207163c241923222500010703042419022225001d070105241923032b001c070230011923222b001d07034b2419012202001a0713042419230301001b07153c0219232225000107034f24192322250002070105
  | 193 => 0x1c091336010423222700020814032419012225001a0c14602419022201001d09133c241923222500010b02032404232225001d0901452405232202001c0913360119232226001b0f14030219012225001a0c145824042322010002081306241923222500010b14032419022225001d0901482405232203001c0902340104232227001e0c11032419012202001a0e146e2419232201001b09133c021923222500010b1403240423222500020801482405232203001c0913360119022226001f0e14032419012225001a0e02542404232201001d09113c241923220200010b14032419232225001b090145020523220300
  | 195 => 0x23042c001b0713490219012225001a0715592419232201000207123c2419232225000107134e0319020425001c070144241923052b001d070232011923222c001c07114b0319012202001a0717752419230401001b07123c0219232225000107134e03192322250002070144241923053d001d071232011902042c001c07134b0306012225001a0702512419232201001c07113c2419232202000107134d0319230425001b070144021923052b001d071232011923222c000207134b0319012225001a07155e2419020401001c07123c2419232225000107024d0319232225001c0701442419230502001d0712320119
  | 197 => 0x114b2403012202001a0b13702419232201000309143c021923222500010c144d24032322250002080146241923222600030915300119022229001c0b154b2403012225001a0b02522419232201000309113c241923220200010d144e2403232225001b090145021923222700030915300119232226000208164b2403012225001a0b13602419022201000309143c241923222500010d024e2403232225001c090145241923060200030916300119232229001b0b15490203012225001a0b13562419232201000208143c241923222500010c144d2403022225001c090146241923222700030902300119232226001c0b
  | 199 => 0x25001a0702512419232201001d03113c2419232202000107144c2419032225001b040144021923222b001c031332011923222b000207144b2419012225001a07145e2419022201001d03133c2419232225000107024c2419032225001d0701442419232202001c031332011923222b001b0414490219012225001a0714592419232201000203133c2419232225000107144c2419022225001d040144241923222b001c030232011923222b001f07114b2419012202001a07147a2419232201001b03133c0219232225000107144c24190322250002070144241923222d001c031332011902222b001e04144b24190122
  | 201 => 0x2419022201001d09033c241923222500010b024f2419230325001e0901042419232202001c0903050119232227001b0b13490219010325001a0b145924192322010002080304241923222500010b134d2419020325001f0901462419232226001c0902050119232226001d0b11042419010302001a0b14672419232201001b09033c021923222500010b134d241923032500020801042419232228001c0903050119022227001d0b134a2419010325001a0b02532419232201001d090304241923220200010b134f2419230325001b0901450219232226001c090305011923222600020813042419010325001a061460
  | 203 => 0x20714032419232225000107144e2419022203001c070144240423223f001f070203010523222c001c07114b2419012202001a07137c2419232201001b0714030204232225000107144e24192322030002070144241923223e001f071503010502222b001c07154b2404012203001a0702512419232201001c0711032419232202000107144d2419232203001b070144020423223f001e071503010523222c000207164b2419012203001a07135e2419022201001c0714032404232225000107024d2419232203001c0701442419232202001e071603010523222b001b0715490204012203001a071358241923220100
  | 205 => 0x23222500010b144c241923222500020801462419230427001d0913370119020526001c0d144b2419012225001a0e02522419232201001c09113c031923040200010b144c2406232225001b0901450219232226001d0913370119230529000208144b2419010425001a0c12602419022201001c09133c031923222500010b024c2419232225001c0901452419230402001d0913370119230526001b0d14490219012225001a0c12562419232201000208133c031923042500010b144c2419022225001c0901462419232226001d0902340119230528001c0c114b2419010402001a0e12722419232201001b09133c0219
  | 207 => 0x134d24192322250003070144021923222b001c071432010323223a000207134b2419012225000307155e2419022201001d07153c2403232225000107024d241923222500030701442419232202001c071432010323222b001b071349021901222500030715572419230601000207163c2403232225000107134f24190222250003070144241923222b001c070232010323223a001d07114b241901220200030717652419232201001b07153c0203232225000107134f24192322250002070144241923222b001c071432010302222b001d07134b241901222500030702512419232201001d07113c2403232202000107
  | 209 => 0x25001d0301452419232202001c0416300119032226001b0514490219012225001a0313582419232201000208143c2419032225000104154d2419022225001d0301472419232228001c0902300119032227001d05114b2419012202001a0313762419232201001b09143c021903222500010c154d241923222500020301472419232226001c0415300119022226001d05144b2419012225001a0302532419232201001e09113c2419032202000104164f2419232225001b030145021923222a001c0915300119032227000205144b2419012225001a0313602419022201001f09143c241903222500010f024f24192322
  | 211 => 0x241923222c001d070204011923032f001c0711052419012202001a07037d2419232201001b07133c0219230325000107140424192322250002070144241923222c001d071332011902032d001c0714052419012225001a0702042419232201001c07113c2419230302000107144c2419232225001b070142021923222c001d071304011923032e00020714052419012225001a07035d2419022201001c07133c241923032500010702042419232225001c0601442419232202001d071332011923032d001b0714050219012225001a0703042419232201000207133c2419230325000107144c2419022225001c070142
  | 213 => 0x1d0914330104022203001c0b134b2405012225001a0b02032419232201001c09113c241923220200010b134e2404232225001b0901030219232227001d0914330119232203000208134b2405012225001a0b15032404022201001c09143c241923220300010b024e2419232225001c0901032419232202001d0914330104232203001b0b13490205012225001a0b15032419232201000208143c241923220300010b134d2404022225001c0901032419232227001d0902330119232203001c0b114b2405012202001a0b17032404232201001b091406021923220300010b134d24192322250002080103241923222600
  | 215 => 0x23042b000207124b2406010525001a07135e0319022201001e07143c2419232225000107024d2419230425001d0701440319232202001c071430011923222b001b0712490219010525001a0713550319230401000207143c241923222500010712612419022225001d070144031923222b001c070230011923042b001d07114b2419010502001a0713680319232201001b07143c0219232225000107125b24192304250002070144031923222c001c071430011902222b001d07124b2419010525001a0702510319230401001f07113c2419232202000107124d2419232225001b070144021923222b001c0714300119
  | 217 => 0x14490219012225001a0c15592403232201000208133c241923222500010b154c2419022225001d0901462403230626001c090231011923222600030c114b2419012202001a0e17772403232201001b09133c021923222500010b154c241923222500020801462403232228001c091337011902222700030d144b2419012225001a0e02542403232201001d09113c241923220200010b164c2419232225001b0901450203232226001c0913310119232226000208144b2419012225001a0c15602403022201001d09133c241923222500010b024c2419232225001d0901452403232202001c091337011923222700030d
  | 219 => 0x2001a05147b2419032201001b07143c0219232225000103134e24192322250002040144241903222c001d071432011902222c001c03134b2419012225001a0502512419032201001c04113c2419232202000103134d2419232225001b070144021903222b001d071432011923222c000203134b2419012225001a05145e2419022201001c07143c2419232225000103024d2419232225001c0401442419032202001d071432011923222c001b0313490219012225001a0514582419032201000204143c2419232225000103134e2419022225001c070144241903222b001d070232011923222c001c03114b24190122
  | 221 => 0x2419230301001c09113c241923220200010f034e2419232225001b0901040219230326001f0915300119232229000208034b2419012225001a0b13052419020301001c091504241923222500010e024e2419232225001c0901452419230302001f0916300119232226001b0b03040219012225001a0613052419230301000208163c241923222500010c034d2419022225001c0901042419230326001e0902300119232228001c0b034b2419012202001a0b13052419230301001b091504021923222500010c034d241923222500020801462419230327001e0915300119022226001c0b03042419012225001a0b0205
  | 223 => 0x1d07133c241923222500010702032419232225001d0701442404232202001c071335011923222b001b0714030219012225001a0715592405232201000207133c240423222500010714032419022225001d0701442419232203001c0702340119232238001f0711032404012202001a07186d2405232201001b07133c02192322250001071403241923222500020701442404232203001c071306011902222b001e0714032419012225001a0702512405232201001d07113c240423220200010714032419232225001b0701440219232203001c071335011923223800020714032404012225001a07155e240502220100
  | 225 => 0x23222500010b134d031902222500210901462419230428001c0902330119232227001d0a114b0319012202001a0b14732419230501001b09123c021923042500010b134d031923222500020801462419232226001c0912330119022226001d0a134b0319010425001a0b02532419230501001d09113c241923220200010b134f0319232225001b090145021923042a001c0912330119232227000208134b0319012225001a0b14602419020501001d09123c241923042500010b024f0306232225001e0901452419232202001c0912330119232226001b0a13490219010425001a0b14582419230501000208123c2419
  | 227 => 0x154e24032322250002070144241923222b0003071430011902222b001c07144b2403012225001a0702512419232201000307113c2419232202000107164d2403232225001b070144021923222b0003071430011923222e000207144b2403012225001a07135e2419022201000307153c2419232225000107024d2403232225001c07014424192322020003071430011923222b001b0714490203012225001a0713592419232201000207163c2419232225000107154e2403022225001c070144241923222b00030702300119232239001c07114b2403012202001a07136f2419230601000307153c0219232225000107
  | 229 => 0x25001b0901450219232227001d0313370119232226000208144b2419012225001a0c15602419022201001c03133c2419232225000104024c2419032225001c0901452419232202001d031337011923222a001b1014490219012225001a0415562419232201000203133c241923222500010b144c2419022225001c0901472419232227001d0302340119232226001c0c114b2419012202001a0e17792419232201001b03133c0219232225000104144c241903222500020801472419232226001d031337011902222a001c0e144b2419012225001a0402522419232201001c03113c241923220200010b144c24190322
  | 231 => 0x2419232202001c070304011923222b001b0713490219010325001a07145924192322010002070305241923222500010713042419020325001e060144241923222c001c070232011923222b001d07114a2419010302001a0714042419232201001b0703050219232225000107135a24192303250002070142241923222c001c070304011902222b001d07134a2419010325001a0702512419232201001d070305241923220200010713042419230325001b070144021923222c001c070332011923222b000207134a2419010325001a0714042419022201001d0703052419232225000107024d24192303250021070142
  | 233 => 0x1c0902030104232226001d0b114b2419012202001a0b137c2419232201001b091503020523222500010c154d240423220300020801462419232228001c0914030119022227001d0b144b2419012203001a0b02532404232201001e091103240523220200010d16502419232203001b0901450219232226001c0914030104232226000208144b2419012203001a0b13602419022201001f091503240523222500010d02502404232203001d0901452419232202001c0914030119232227001b0b14490219012203001a0b135924042322010002081603240523222500010c154d2419022203001d090146241923222600
  | 235 => 0x2042c001c07144b2419012225001a0702512419232201001c07113c0319230502000107144c2419230425001b070144021923222c001d071332011923222c000207144b2419012225001a07125e2419020401001c07133c0319230525000107024c2419232225001c0701442419232202001d071332011923042c001b0714490206012225001a0712582419232201000207133c0319230525000107144c2419020425001c070144241923222c001d070232011923222c001c07114b2419012202001a0712722419230401001b07133c0219230525000107144c24192322250002070144241923222b001d0713320119
  | 237 => 0x134b241901222500030b14602419022201001c09143c240323222500010b024e241923222500030901452419232202001d0916310103232226001b0b1349021901222500030b14562419232201000208143c240323222500010b134d241902222500030901472419232226001d0902320103232228001c0b114b241901220200030b14652419232201001b09143c020323222500010b134d241923222500020801472419230627001d0915310103022226001c0b134b241901222500030b02522419232201001c09113c240323220200010b134e241923222500030901450219232226001d091532010323223a000208
  | 239 => 0x25001a0313592419232201000207163c241903222500010514502419022225001d030144241923222d001c070230011903222b001d07114b2419012202001a0313762419232201001b04153c0219032225000105145024192322250002030144241923222b001c071430011902222b001d04154b2419012225001a0302512419232201001f07113c2419032202000105144d2419232225001b030144021923222d001c071430011903222b000207164b2419012225001a03135e2419022201001e04153c2419032225000105024d2419232225001d0301442419232202001c071430011903222b001b04154902190122
  | _ => 0
private def ix (i j : ℕ) := ((packed i) >>> (8*j))%256
private def qFor (i j : ℕ) := primes[ix i j]?.getD 0
private def rowFor (i j : ℕ) := rows[ix i j-primes.length]?.getD default
private abbrev Test (i j : ℕ) := residue 30 0 i j=0 → (i%12≠1 ∨ j%12≠0) →
    (ix i j<primes.length ∧ residue (qFor i j) 1 i j=0) ∨
    (ix i j-primes.length<rows.length ∧ CellOK (rowFor i j) i j)
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block0 : ∀ i∈List.range' 0 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block1 : ∀ i∈List.range' 10 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block2 : ∀ i∈List.range' 20 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block3 : ∀ i∈List.range' 30 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block4 : ∀ i∈List.range' 40 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block5 : ∀ i∈List.range' 50 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block6 : ∀ i∈List.range' 60 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block7 : ∀ i∈List.range' 70 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block8 : ∀ i∈List.range' 80 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block9 : ∀ i∈List.range' 90 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block10 : ∀ i∈List.range' 100 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block11 : ∀ i∈List.range' 110 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block12 : ∀ i∈List.range' 120 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block13 : ∀ i∈List.range' 130 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block14 : ∀ i∈List.range' 140 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block15 : ∀ i∈List.range' 150 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block16 : ∀ i∈List.range' 160 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block17 : ∀ i∈List.range' 170 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block18 : ∀ i∈List.range' 180 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block19 : ∀ i∈List.range' 190 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block20 : ∀ i∈List.range' 200 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block21 : ∀ i∈List.range' 210 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block22 : ∀ i∈List.range' 220 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem block23 : ∀ i∈List.range' 230 10, ∀ j : Fin 240, Test i j.val := by decide +kernel
private theorem cover {i j : ℕ} (hi : i<240) (hj : j<240) : Test i j := by
  by_cases h0 : i<10
  · exact block0 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h1 : i<20
  · exact block1 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h2 : i<30
  · exact block2 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h3 : i<40
  · exact block3 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h4 : i<50
  · exact block4 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h5 : i<60
  · exact block5 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h6 : i<70
  · exact block6 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h7 : i<80
  · exact block7 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h8 : i<90
  · exact block8 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h9 : i<100
  · exact block9 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h10 : i<110
  · exact block10 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h11 : i<120
  · exact block11 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h12 : i<130
  · exact block12 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h13 : i<140
  · exact block13 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h14 : i<150
  · exact block14 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h15 : i<160
  · exact block15 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h16 : i<170
  · exact block16 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h17 : i<180
  · exact block17 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h18 : i<190
  · exact block18 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h19 : i<200
  · exact block19 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h20 : i<210
  · exact block20 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h21 : i<220
  · exact block21 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases h22 : i<230
  · exact block22 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  exact block23 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩

theorem residues {n a b : ℕ} (large : 1000<n) (prime : (n+1).Prime)
    (eq : n+5=5^a*7^b) (ha : 0<a) (hb : 0<b) (div : 30∣n) (sol : Erdos889.v_l 1 n=1) :
    a%12=1 ∧ b%12=0 := by
  by_contra! bad
  have cell := cover (show a%240<240 by omega) (show b%240<240 by omega)
  have z30 := residue_eq eq ha hb (by decide : Stable 30) 0
  have test := cell (by omega)
  rw [Nat.mod_mod_of_dvd a (by decide : 12∣240),Nat.mod_mod_of_dvd b (by decide : 12∣240)] at test
  rcases test (by omega) with ⟨pi,zero⟩|⟨ri,ok⟩
  · have mem : qFor (a%240) (b%240) ∈ primes := by
      simp only [qFor,List.getElem?_eq_getElem pi,Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨pq,small,st⟩ := pg _ mem
    have dv := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb st 1).trans zero)
    have := (Nat.prime_dvd_prime_iff_eq pq prime).mp dv
    omega
  · have mem : rowFor (a%240) (b%240) ∈ rows := by
      simp only [rowFor,List.getElem?_eq_getElem ri,Option.getD_some]
      exact List.getElem_mem _
    exact exclude eq ha hb sol (good _ mem) ok
end Erdos889.PrimeSevenFive

namespace Erdos889.PrimeSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem close_from_residues {n j a b : ℕ} (big : 1000<n)
    (hj : 0<j) (small : j≤6) (eq : n+j=j^a*7^b) (ha : a%12=1) (hb : b%12=0)
    (sol : v_l 1 n=1) : False := by
  let z := j^(a/12)*7^(b/12)
  have ident : n+j=j*z^12 := by
    change n+j=j*(j^(a/12)*7^(b/12))^12
    have A : a=(a/12)*12+1 := by omega
    have B : b=(b/12)*12 := by omega
    calc
      n+j=j^a*7^b := eq
      _ = j^(a/12*12+1)*7^(b/12*12) := congrArg₂ _ (congrArg (j^·) A) (congrArg (7^·) B)
      _ = _ := by rw [mul_pow,←pow_mul,←pow_mul,pow_succ]; ring
  have high : 1<z := by
    by_contra! low
    have := Nat.pow_le_pow_left low 12
    have zz : z^12≤1 := by omega
    have := Nat.mul_le_mul_left j zz
    omega
  exact no_twelfth hj small high ident sol

private theorem positivity_exps {n j a b : ℕ} (eq : n+j=j^a*7^b) (pj : j.Prime)
    (small : j<7) (hd : j∣n+j) (ds : 7∣n+j) : 0<a ∧ 0<b := by
  constructor
  · by_contra! h
    rw [show a=0 by omega,pow_zero,one_mul] at eq
    rw [eq] at hd
    have := (Nat.prime_dvd_prime_iff_eq pj (by decide : Nat.Prime 7)).mp (pj.dvd_of_dvd_pow hd)
    omega
  · by_contra! h
    rw [show b=0 by omega,pow_zero,mul_one] at eq
    rw [eq] at ds
    have := Nat.le_of_dvd pj.pos ((by decide : Nat.Prime 7).dvd_of_dvd_pow ds)
    omega

theorem no_two_three_five {n j : ℕ} (large : 1000000000000<n) (div : 30∣n)
    (prime : (n+1).Prime) (js : j=2 ∨ j=3 ∨ j=5)
    (seven : 7∣n+j) (sol : v_l 1 n=1) : False := by
  have pj : j.Prime := by rcases js with rfl|rfl|rfl <;> decide
  have small : j<7 := by omega
  obtain ⟨a,b,h⟩ := first_multiple_shape pj.pos small (by omega) pj (by
    intro p pp lo d
    have tab : ∀ u : Fin 7, u.val.Prime → u.val≤5 → u.val=2 ∨ u.val=3 ∨ u.val=5 := by decide
    have opts := tab p pp (by omega)
    rcases opts with h|h|h <;> rw [h] at d ⊢ <;> omega) seven sol
  have hd : j∣n+j := by rcases js with rfl|rfl|rfl <;> omega
  obtain ⟨ha,hb⟩ := positivity_exps h pj small hd seven
  refine close_from_residues (by omega) pj.pos (by omega) h ?_ ?_ sol
  all_goals
    rcases js with rfl|rfl|rfl
    · have t := Erdos889.PrimeSevenTwo.residues (by omega) prime h ha hb div sol; omega
    · have t := Erdos889.PrimeSevenThree.third_residues (by omega) prime h ha hb div sol; omega
    · have t := Erdos889.PrimeSevenFive.residues (by omega) prime h ha hb div sol; omega

/-- For prime successors, a missing seven can occur only six steps after n. -/
theorem only_sixth_offset {n : ℕ} (big : 1000000000000<n) (div : 30∣n)
    (prime : (n+1).Prime) (sol : v_l 1 n=1) (missing : ¬7∣n) : 7∣n+6 := by
  have r : n%7<7 := Nat.mod_lt _ (by decide)
  by_contra sixth
  have options : 7∣n+1 ∨ 7∣n+2 ∨ 7∣n+3 ∨ 7∣n+4 ∨ 7∣n+5 := by
    have nz : n%7≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using missing
    have choices : n%7=1 ∨ n%7=2 ∨ n%7=3 ∨ n%7=4 ∨ n%7=5 ∨ n%7=6 := by omega
    rcases choices with h|h|h|h|h|h <;> simp [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,h] at sixth ⊢
  rcases options with h|h|h|h|h
  · have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) prime).mp h
    omega
  · exact no_two_three_five big div prime (Or.inl rfl) h sol
  · exact no_two_three_five big div prime (Or.inr (Or.inl rfl)) h sol
  · exact no_four big div h sol
  · exact no_two_three_five big div prime (Or.inr (Or.inr rfl)) h sol

end Erdos889.PrimeSeven



/- A modular certificate for the sixth offset supported on two, three and seven. -/
namespace Erdos889.PrimeSixth

private structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  other : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

private abbrev Stable (L m : ℕ) :=
  0 < m ∧ 2^(L+1)%m=2%m ∧ 3^(L+1)%m=3%m ∧ 7^(L+1)%m=7%m

private theorem cycle {L p m : ℕ} (hL : 0<L) (one : Nat.ModEq m (p^(L+1)) p) (e : ℕ)
    (he : 0<e) : Nat.ModEq m (p^e) (p^(L+e%L)) := by
  have step (v : ℕ) (hv : 0<v) : Nat.ModEq m (p^(v+L)) (p^v) := by
    have one' := one.mul_right (p^(v-1))
    rw [←pow_add,show L+1+(v-1)=v+L by omega] at one'
    simpa only [←pow_succ',Nat.sub_add_cancel hv] using one'
  have steps (v : ℕ) (hv : 0<v) (j : ℕ) : Nat.ModEq m (p^(v+L*j)) (p^v) := by
    induction j with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ j ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (step _ (by omega)).trans ih
  calc
    p^e ≡ p^(e+L) [MOD m] := (step e he).symm
    _ = p^((L+e%L)+L*(e/L)) := by rw [Nat.add_assoc,Nat.mod_add_div,Nat.add_comm]
    _ ≡ _ [MOD m] := steps _ (by omega) _

private def residue (L m k a b c : ℕ) :=
  (((2^(L+a)%m)*(3^(L+b)%m)%m)*(7^(L+c)%m)%m+k+6*m-6)%m

private structure H (n a b c : ℕ) : Prop where
  shape : n+6=2^a*3^b*7^c
  ha : 0<a
  hb : 0<b
  hc : 0<c
  big : 1600<n
  d5 : 5∣n
  prime : (n+1).Prime
  sol : Erdos889.v_l 1 n=1

private theorem residue_eq {n a b c L m : ℕ} (h : H n a b c) (hL : 0<L)
    (st : Stable L m) (k : ℕ) : (n+k)%m=residue L m k (a%L) (b%L) (c%L) := by
  obtain ⟨mp,c2,c3,c7⟩ := st
  let w := ((2^(L+a%L)%m)*(3^(L+b%L)%m)%m)*(7^(L+c%L)%m)%m+k
  have d : Nat.ModEq m (n+k+6) w := by
    rw [show n+k+6=(n+6)+k by omega,h.shape]
    apply Nat.ModEq.add_right k
    change _ % m = _ % m
    rw [Nat.mod_mod, ←Nat.mul_mod (2^(L+a%L)) (3^(L+b%L)), ←Nat.mul_mod]
    exact ((cycle hL c2 a h.ha).mul (cycle hL c3 b h.hb)).mul (cycle hL c7 c h.hc)
  have add : Nat.ModEq m w (w+6*m) := by
    change w%m=(w+6*m)%m
    rw [Nat.mul_comm 6 m,Nat.add_mul_mod_self_left]
  exact Nat.ModEq.add_right_cancel' 6
    (show Nat.ModEq m (n+k+6) (w+6*m-6+6) by rw [Nat.sub_add_cancel (by omega)]; exact d.trans add)

private abbrev RowOK (L : ℕ) (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable L r.q ∧ Stable L r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  (∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true) ∧
  (∀ p∈r.other, Stable L p) ∧
  (∀ p : Fin (r.k+1), p.val.Prime → p.val∈r.pool ∨ p.val∈r.other)

private abbrev CellOK (L : ℕ) (r : Row) (i j k : ℕ) :=
  residue L r.q r.k i j k=0 ∧ r.mask.testBit (residue L r.m r.k i j k)=false ∧
  ∀ p∈r.other, residue L p r.k i j k≠0

private theorem killRow {n a b c L : ℕ} (h : H n a b c) (hL : 0<L)
    {r : Row} (valid : RowOK L r) (cell : CellOK L r (a%L) (b%L) (c%L)) : False := by
  obtain ⟨pq,kpos,klt,qin,sq,sm,one,closed,others,small⟩ := valid
  have qd := Nat.dvd_of_mod_eq_zero ((residue_eq h hL sq r.k).trans cell.1)
  have support (p : ℕ) (pp : p.Prime) (dp : p∣n+r.k) : p∈r.pool := by
    by_contra outside
    have ne : r.q≠p := by intro e; exact outside (e ▸ qin)
    by_cases early : p≤r.k
    · have po := (small ⟨p,by omega⟩ pp).resolve_left outside
      exact cell.2.2 p po ((residue_eq h hL (others p po) r.k).symm.trans (Nat.mod_eq_zero_of_dvd dp))
    · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes kpos pq pp ne klt (by omega) qd dp h.sol
  have smooth (t : ℕ) : 0<t → (∀ p : ℕ, p.Prime → p∣t → p∈r.pool) → r.mask.testBit (t%r.m)=true := by
    induction t using induction_on_primes with
    | zero => omega
    | one => exact fun _ _ => one
    | prime_mul p t pp ih =>
      intro pos sup
      have tt : 0<t := Nat.pos_of_mul_pos_left pos
      have pt := sup p pp (dvd_mul_right p t)
      have good := ih tt (fun q pq d => sup q pq (dvd_mul_of_dvd_right d p))
      have final := closed ⟨t%r.m,Nat.mod_lt _ sm.1⟩ good p pt
      simpa only [Nat.mod_mul_mod,Nat.mul_comm t p] using final
  have final := smooth (n+r.k) (by omega) support
  rw [residue_eq h hL sm,cell.2.1] at final
  contradiction

private inductive Rule where
  | target | five | prime (q : ℕ) | pool (r : Row)
  deriving Inhabited

private def Valid (L : ℕ) : Rule → Prop
  | .target => 12∣L
  | .five => Stable L 5
  | .prime q => q.Prime ∧ q≤1600 ∧ Stable L q
  | .pool r => RowOK L r

private instance (L : ℕ) (r : Rule) : Decidable (Valid L r) := by
  cases r <;> unfold Valid <;> infer_instance

private abbrev Target (a b c : ℕ) := a%12=1 ∧ b%12=1 ∧ c%12=0

private def Hit (L i j k : ℕ) : Rule → Prop
  | .target => Target i j k
  | .five => residue L 5 0 i j k≠0
  | .prime q => residue L q 1 i j k=0
  | .pool r => CellOK L r i j k

private instance (L i j k : ℕ) (r : Rule) : Decidable (Hit L i j k r) := by
  cases r <;> unfold Hit <;> infer_instance

private theorem kill {n a b c L : ℕ} (h : H n a b c) (hL : 0<L) (bad : ¬Target a b c)
    (r : Rule) (v : Valid L r) (hit : Hit L (a%L) (b%L) (c%L) r) : False := by
  cases r with
  | target =>
    apply bad
    simpa only [Hit,Target,Nat.mod_mod_of_dvd _ v] using hit
  | five =>
    apply hit
    rw [←residue_eq h hL v]
    exact Nat.mod_eq_zero_of_dvd h.d5
  | prime q =>
    obtain ⟨pq,small,st⟩ := v
    have d := Nat.dvd_of_mod_eq_zero ((residue_eq h hL st 1).trans hit)
    have e := (Nat.prime_dvd_prime_iff_eq pq h.prime).mp d
    have := h.big
    omega
  | pool r => exact killRow h hL v hit

private structure Keys where
  count : ℕ
  bits : ℕ
  data : ℕ

private def coord (keys : Keys) (i d : ℕ) :=
  (keys.data >>> (keys.bits*(3*i+d))) % 2^keys.bits

private abbrev Match (t a b c : ℕ) (keys : Keys) :=
  ∃ i<keys.count, a%t=coord keys i 0 ∧ b%t=coord keys i 1 ∧ c%t=coord keys i 2

private structure Stage where
  t : ℕ
  s : ℕ
  old : Keys
  next : Keys
  rules : List Rule
  bits : ℕ
  codes : ℕ

private def pick (g : Stage) (i x y z : ℕ) :=
  (g.codes >>> (g.bits*(((i*g.s+x)*g.s+y)*g.s+z))) % 2^g.bits

private abbrev Test (g : Stage) (i x y z : ℕ) : Prop :=
  let u := coord g.old i 0 + g.t*x
  let v := coord g.old i 1 + g.t*y
  let w := coord g.old i 2 + g.t*z
  let code := pick g i x y z
  if code<g.rules.length then Hit (g.t*g.s) u v w g.rules[code]!
  else let j := code-g.rules.length
       j<g.next.count ∧ u=coord g.next j 0 ∧ v=coord g.next j 1 ∧ w=coord g.next j 2

private theorem refine {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c)
    (g : Stage) (ht : 0<g.t) (hs : 0<g.s) (valid : ∀r∈g.rules, Valid (g.t*g.s) r)
    (tested : ∀ i<g.old.count, ∀ x y z : Fin g.s, Test g i x y z)
    (old : Match g.t a b c g.old) : Match (g.t*g.s) a b c g.next := by
  obtain ⟨i,hi,eA,eB,eC⟩ := old
  let L := g.t*g.s
  have hL : 0<L := Nat.mul_pos ht hs
  let digit (d : ℕ) : Fin g.s := ⟨d%L/g.t,(Nat.div_lt_iff_lt_mul ht).2 (by
    rw [Nat.mul_comm]; exact Nat.mod_lt d hL)⟩
  have split (d : ℕ) : d%g.t+g.t*(digit d).val=d%L := by
    change d%g.t+g.t*(d%L/g.t)=d%L
    have dv : g.t∣L := dvd_mul_right g.t g.s
    simpa only [Nat.mod_mod_of_dvd _ dv] using Nat.mod_add_div (d%L) g.t
  have cell := tested i hi (digit a) (digit b) (digit c)
  dsimp only [Test] at cell
  rw [←eA,←eB,←eC,split a,split b,split c] at cell
  split at cell
  next hcode =>
    rw [getElem!_pos g.rules _ hcode] at cell
    exact False.elim (kill h hL bad _ (valid _ (List.getElem_mem hcode)) cell)
  next => exact ⟨_,cell⟩


private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨179,4,0x8bb0bb7ab3ab69b87b47bb6b36b25b43b03bb2b72ba1b1bab9a39aa8a68a97ab5a75a64a24a53a71a31aa0a20aab96b95a91a9499679279969169059a39239929529819bb89981988884887789585584480483385181188080088b74b7ba73a7297477077b67767a578370377273276179b6b96796686286576756356a46246136b16316a066066b52b59a51a5095a75275965565855a356355251254157b4994594484084374554154844044b349141148044044b30b3ba37a3a93873073763363653833433b233232135b2792392a82282172b52352a42642932b12712602202ab12b19a15a1891a716715611614516312319211213b0590190880080b70950150840440730910510400000⟩
private def rows12 : List Rule := [
  .five,
  .pool ⟨13,3,[13,3],[2],35,0x228033a1a⟩,
  .pool ⟨13,11,[13,11],[2,3,5,7],35,0x228033a1a⟩,
  .pool ⟨13,7,[13],[2,3,5,7],35,0x28002002⟩,
  .pool ⟨13,2,[13,2],[],105,0x1a2120482010830420104812116⟩,
  .pool ⟨13,9,[13,3],[2,5,7],35,0x228033a1a⟩,
  .prime 13,
  .pool ⟨13,4,[13,2],[3],105,0x1a2120482010830420104812116⟩,
  .target]
private def step12 : Stage := ⟨1,12,keys1,keys12,rows12,8,0xbb00000002000000ba01000000b9000000b80000000007000000b7000000060000000005000000040000000300000000b6000000b500000002b400000001000000b3000000000600000007000000b2000000000300000005000000040000000002000000b1000000b0af000000ae0000000100000000ad0000000600000007000000000400000003000000050000000600000007000000ac00000000030000000500000004ab00000002000000aa00000000a9000000a80000000100000000a7000000060000000700000000040000000300000005a6000000a5000000020000000001000000a4000000a30000000007000000a2000000060000000005000000040000000302000000a1000000a0000000009f000000010000009e0000009d0000009c0000000200000000010000009b0000009a000000000700000099000000060300000005000000040000000002000000980000009700000000960000000100000095000000000600000007000000940400000003000000050000000093000000020000009200000000910000009000000001000000008f00000006000000070500000004000000030000008e000000060000000700000000040000000300000005000000008d000000020000008c000000008b0000008a000000010700000089000000060000000005000000040000000300000000880000008700000002000000000100000086000000850600000007000000840000000003000000050000000400000000020000008300000082000000008100000001000000800000007f0000007e000000027d000000010000007c0000000006000000070000007b0000000003000000050000000400000000020000007a000000797800000077000000010000000076000000060000000700000000040000000300000005000000007500000002000000740100000073000000720000000007000000710000000600000000050000000400000003000000700000000600000007000000000400000003000000056f0000006e0000000200000000010000006d0000006c00000000070000006b0000000600000000050000000400000003020000006a0000006900000000680000000100000067000000000600000007000000660000000003000000050000000465000000020000006400000000630000006200000001000000020000006100000060000000005f000000010000005e0000000006000000070000005d040000000300000005000000005c000000020000005b000000005a000000590000000100000000580000000600000007050000000400000003000000005700000056000000020000000001000000550000005400000000070000005300000006030000000500000004000000070000005200000006000000000500000004000000030000000051000000500000000200000000010000004f0000004e06000000070000004d0000000003000000050000000400000000020000004c0000004b000000004a0000000100000049480000000600000007000000000400000003000000050000000047000000020000004600000000450000004400000001000000020000004300000042410000004000000001000000003f000000060000000700000000040000000300000005000000003e000000020000003d010000003c0000003b00000000070000003a000000060000000005000000040000000300000000390000003800000002370000000100000036000000000600000007000000350000000003000000050000000400000007000000340000000600000000050000000400000003020000003300000032000000003100000001000000300000000006000000070000002f000000000300000005000000042e000000020000002d000000002c0000002b00000001000000002a00000006000000070000000004000000030000000529000000280000000200000000010000002700000026000000250000000200000024000000002300000022000000010000000021000000060000000705000000040000000300000000200000001f0000000200000000010000001e0000001d00000000070000001c0000000603000000050000000400000000020000001b0000001a00000000190000000100000018000000000600000007000000080400000003000000050000000600000007000000170000000003000000050000000400000000020000001600000015000000001400000001000000131200000006000000070000000004000000030000000500000000110000000200000010000000000f0000000e00000001070000000d0000000600000000050000000400000003000000000c0000000b0000000200000000010000000a00000009⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid 12 r := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine h bad step12 (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨624,6,0xb3bef82fbe3b8d45e320b8e0ed7e175ec2d71ee5deb7b1adbeab637a18d2b57dad2f34bb6a9ee677b39dec247b0a9bf2d639a98c2a6369d8ce4636b55cea5709d5f24576b52c2d4bca92e674b127ef46fba0fec03fb90fbf03d78b1eca67be8decac6fb99bca66f88dbeec635998ca3635818d6c578a55fa657b8d5fac4b8992d634b363e998e20635b15d656be897fae53ead1fae6bb95aeeb5fba14ee86b8957e28538894e2e478adacae5f2a17ca5532891ca8e9bab17a4c5bb71627c558714a75beb59ee74fb910ee7678853e2d438859d6a4f5853d6743591cca7c189bc7a9c1e83c6e6cdb8f06ecf128304a0a4ea9e89d15e44e6da21b7456d715b5026da39850861115874261d21550855a1555c255d392505497092442497b72764c9a8725adf99b7872dc9635e40779905e40179035b4ca6d91db4c16d93584c761611870161335570755605570d4961d240149eb3b6e9ed283b62ce15a786e0e1bb32629c9e5a878679819b5436d21986c655519257ef8bd7e0b5f88cbe3beec5fbb2fbec5d7b0b2ec2fb53bbd48d752f2d45cb52fec88ef20b5c8ecb209b78b6db15b60e6d521b48655e13df81ebe2b4f8df7b2baec4d3b37de07f7813ae0dd38077d44c7215a6c475e05a78d5de35a54a5d51da4845d2344083cfb333e09c38033c8b3b4e0bd35234dc8eba234d08c70addf2877095dda2773b9ae6b6b6a1ac226b3ad7c285f9897f2b539a14ce253cad1dab473a11f224702bdf07f7913de4aeb61facc4eb91f4d84d3bc6acad77585dfa16b8857ca153b851df9931b1df697778ddea077481deac6b7a5ac636bd81ad2c5fa8d7c635f7817f6c534b14ea9531814ea04727bdad8f6857dadeeab63a958ea257ab92de26f4a1ec62631b95c62d5dab55e7c97935521c9487846dd51ab246ab8485df6a77a9daead77481cf6c67d8d9f695bd8d0f697378dcde0677b16de6437b1cd29674996d2043499cc63671a50c60431a36762d9aaf65e5d94bb6463c1182ef5697d4e2f53bb75a2dd6bb1725c598b165bb5c2dd58b6902d764b5132d140845552778d75b29d60775511d78d69835a54a6921da78a5db1d74875d811760a51535160a45229178745b111629dd59b74a3dd48fd5e3dd18f474c75125d5c67540dd5cc69119a7436913176865d70d768c51a1945065110d450c45d19168345d0115f8f44d7d2b8dcde310fae86dfa037e8cd3a271e8ceb7277dc6d370f1dcceb41bad03df4034d00eb1337c49d31034c46c7105a50045d251683457311506451239f48cfd0b3f4ec3d2fce8edb7179d0ecf42f0d0ee71233c45c3115c68841a39c5c241721c50e4d42d05004112091c2fa9ee8735a1cca573e89cd6e67b959fa2678899d655b8b93ca84fe953d654fb893cae43ba10e25435890d4de7e376c8dc30379d84e73079ead7349dcf61734b59f67677859f6d5b79d6de15b1856ded4faa93c674fa853c6d43a9d0f64434850d0ce71279dcccf4273e80cf1330f49c34030db683399cf26676996c264fc8d3e6643a7bc9dbf2157cb52f244bc91ee616f9a95e674b9b5edaa576915da14b6b5ece77b391bced573a92cedd569bb720ed9a7b5a3ed3b3b4295fcb11e6c776a5ada353699dce36b3b14ce677081dc2c6b0994c25e9c8b772ee99af766bf56a3a5a5dd6b3a4e5909a13e6b4f3953c224308a8f1ba397a8cd3bbc42bf1ca3c54b71221c6c271e2d954b65b2195426582d654859815678259b39348b4de2136024db2d0608412090467f1d93c5ead949f6464d91ab3767cda9335118da05c50165a35674159705344141066c67bf00fb9278e46d7927ed83e36035d83fb3338cc3e33275cc6cb029558c55c2527096191956434990d54004900ce305f7c23dd82f733bacc4f3c079f0ddbc1f0f0df392b9e47c39070e47f362b9d84e76076d8ac362bcc01f301f9c04db0370c0b41935670759905658a59311640⟩
private def rows60 : List Rule := [
  .pool ⟨11,5,[11,5],[2,3],13,0x1ffe⟩,
  .prime 11,
  .pool ⟨11,3,[11,3],[2],35,0x228033a1a⟩,
  .pool ⟨11,2,[11,2],[],7,0x16⟩,
  .pool ⟨11,8,[11,2],[3,5,7],39,0x102510d36⟩,
  .pool ⟨11,8,[11,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨11,5,[11,5],[2,3],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .pool ⟨11,5,[11,5],[2,3],25,0x210863⟩,
  .pool ⟨11,8,[11,2],[3,5,7],465,0x1a25248921865208201a00b08825125060004a2010132c02020034884c30c844b0010100d32020114800182922904434016010412986124492916⟩,
  .pool ⟨13,10,[13,2,5],[3,7],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  .pool ⟨11,8,[11,2],[3,5,7],793,0x1a342980230a1004202c12310c000490640032c0082068091290011044c20800e08100152822810012052404a240420808631840410809148092812002051052a002041c00410c8822002522405810400d300098248000c23120d010802143100650b16⟩,
  .pool ⟨13,10,[13,2,5],[3,7],275,0x120915d60763b62c103b280fcf6c58a457505f8e589140eeb0bf3cb16291d961767b6⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩,
  .pool ⟨11,9,[11,3],[2,5,7],35,0x228033a1a⟩,
  .pool ⟨11,10,[11,2,5],[3,7],39,0x102510d36⟩,
  .pool ⟨11,4,[11,2],[3],7,0x16⟩,
  .pool ⟨11,7,[11],[2,3,5,7],5,0x2⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨11,10,[11,2,5],[3,7],31,0x7ffffffe⟩,
  .pool ⟨31,14,[31,2],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨13,8,[13,2],[3,5,7],775,0x6884c020a0000850880000005084220084c004000040100026008024190810408120a40040210041400430000300001418280000c0000c20028200840200250481020810982401006400080200002003210044210a000000110a10000504032116⟩,
  .pool ⟨13,8,[13,2],[3,5,7],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨13,8,[13,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨11,10,[11,2,5],[3,7],175,0x120d50f36241aa1e6c583543cd8906ac79b122d50f36⟩,
  .pool ⟨31,3,[31,3],[2],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,13,[31,7,13],[2,3,5,11],55,0x12081594076396⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,4,[61,2],[3],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  .pool ⟨61,4,[61,2],[3],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .prime 31,
  .pool ⟨13,10,[13,2,5],[3,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨11,5,[11,5],[2,3],31,0x7ffffffe⟩,
  .pool ⟨61,25,[61,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨13,8,[13,2],[3,5,7],31,0x7ffffffe⟩,
  .pool ⟨13,8,[13,2],[3,5,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],273,0x1a24349068860800a25240a01300041264309920800320140929140041845824b0916⟩,
  .pool ⟨31,26,[31,2,17,19,23],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨31,8,[31,2],[3,5,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,7,[31],[2,3,5,7],5,0x2⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨31,8,[31,2],[3,5,7],33,0x1a2030116⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,8,[31,2],[3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,23,[61,17,19,23],[2,3,5,7,11,13],77,0x129974700330038ba652⟩,
  .pool ⟨31,22,[31,2,17,19],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨11,5,[11,5],[2,3],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,28,[31,2,17,19,23],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],33,0x1a2030116⟩,
  .pool ⟨31,13,[31,7],[2,3,5,11,13],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩,
  .pool ⟨61,8,[61,2],[3,5,7],39,0x102510d36⟩,
  .pool ⟨61,13,[61,7],[2,3,5,11,13],65,0x12402802010050092⟩,
  .pool ⟨31,13,[31,7],[2,3,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],273,0x1a24349068860800a25240a01300041264309920800320140929140041845824b0916⟩,
  .pool ⟨61,14,[61,2],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],33,0x1a2030116⟩,
  .pool ⟨31,11,[31],[2,3,5,7,11],3,0x2⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],77,0x129974700330038ba652⟩,
  .pool ⟨31,4,[31,2],[3],33,0x1a2030116⟩,
  .prime 61,
  .pool ⟨13,12,[13,2,3],[5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,4,[61,2],[3],39,0x102510d36⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,13,[31,7,13],[2,3,5,11],61,0x1ffffffffffffffe⟩]
private def step60 : Stage := ⟨12,5,keys12,keys60,rows60,10,0xdac41003c0e0380d0441003c0f0380d044100400f0380d0cab00400f0380d03c0e0343f0401003c0e034110441003c0e0340d0641003c0e0380d0fc1003eaf0400f0380d034110400f0380e034110400f03c0e036ae0401003c0e036ad0380dab01003c0f0380d044100400f0380d046ab0400f0380d036aa0400f0381003c0e0343e0f81003c0e0340d0f81003c0e0380d0f81003c0f0380d0f8100380d0541003c0f0380d054100400f0380d054150400f0380d034400400f0381003c0e034150541003c0e0340d0541003c0e0380d0541003c0f0380d05010034150400f0380e034150400f03c0e034150401003c0e034150501003c0e0340f0380d058100400f0380d058160400f0380d034160400f0380e034160400f0581003c0e0340d0581003c0e0380d0581003c0f0380d058100400f0380d05802004300241e00c02004070201e00c020040702c0800c1e004010780800c020141e0080102c07014030080100406078030081e004070140300c020041e0140101c09078020080101c0800c03008010181e020030780101c1e020030080107802004070240800c02006a901c1e00c020040101c0800c1e008010780800c070141e008010040b0140300802004070780300c1e004310140500c020041e0000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c0d0981003c170480daa01003c0f05c0d0ac100400f05c0d09c130400f0a80d03c17034260401003c12036a70a01003c170340d09c1003c1705c0d04c1003c260400f05c0d036a60400f04817036a50400f03c13034270401003c17034130b80d0981003c0f0480da90100400f05c0d0ac270400f05c0d034130400f05c1003c1703426a8c1003c120340d0a01003c2705c0d09c1003c0f05c0d04c1003c12034160401003c0e034160581003c0e0340d0581003c0e0380d0881003c160400f0480d034160400f0380e034160400f03c0e034160401003c0e034220480d0581003c0f0380d058100400f0380d058160400f0380d034220400f0381003c12034160581003c0e0340d0581003c0e0380d0581003c0f0380d08810034160400f0480e034160400f03c0e034160401003c0e034160881003c0e0340d0441003c0e0380d0941003c0f0380d044100400f0380d044240400f0380d03c0e034110401003c0e034250441003c0e0340d0441003c0e0380d0901003c110400f0380d034250400f0380e034110400f03c0e034110401003c0e034240380d0441003c0f0380d094100400f0380d044110400f0380d034240400f0381003c0e034110941003c0e0340d0441003c0e0380d0441003c0f0380d0901000400078030f41e004000100300c3d0041e010040783d004000000400c3d0043d008010001e0103d078010001e0103d00801004000101e00802004000103d0001e00c02004010003d00c1e008010783d00c1e008010003d0f40300801000020043d0780300c1e0043d0100400c020041e0f40407802004010f40400c0207803008010000001003078010041e0100300802004000101e00c020040001002004070200300c02004060280a00c0200407a880a00c020040101c0800c0201403008010180701403008010040701403008020040b0140300c0200407014010180800c020080101c0900c030080108009024030080101c07020030080100c02004070200900c02004070800900c020040101c0900c02008010f00800c070200300801004060240300802004070240300c02004070240800c020040b034410400f05c17036a10400f03ea00369f0401003c170369e0601003c170340f05c0d0cc100400f05c0da74330400f05c0d0341b0400f05c1a034180400fa701003c170340da6c1003e9a05c0da641003c0f05c0da60100400f05c0d06017036970400f03c17036960401003c1703695a501003c180340d0601003c170400fa4c0da4a910400f05c0d036900400f05c170341b0400f03c17034180400f0380d050100400f0380da3e8e0400f0380d0368d0400f0380e034150400f0501003c0e0340d0501003c0e0380d0501003c0f0380d050100400f0380d0540e034140400f03c0e034140401003c0e034140501003c0e0340d0541003c0e0400f0380d058160400f0380d034160400f0380e034160400f03c0e034160400d0581003c0e0380d0581003c0f0380d058100400f0380d058160400f0380d034110400f0380e034130400f03c0e034110401003c120368c0441003c0e0340f0380d044100400f0380d04c110400f0380d0368b0400f0480e034110400f0441003c0e0340d04c1003c0e0380d0441003c0f0480d0a4100400f0380d0440e034110400f03c0e034130401003c0e03411a281003c120340d0441003c0e0400f0380d044130400f0380d034110400f038120342d0400f03c0e03411040030f40101c05014030f40101807014030f40100407014030f43d004060140301c080f40200401018080f4020080101c0a0f43d00801018080283d0080101c02004060f40300c02004070f43d00c02004070183d00c020040101c3d00c0201403008010f43d01403008010043d01403008020043d0140300c020043d0140101c0500c020080101c0500c030080102c05014030080101c060140300801004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c020040001039036890400f03c17034240401003c1703688a1c1003c170340d0dc1003c170400f05c0da18240400f05c0d036850400fa1017036830400f03c17034370400da081003c1705c0d0901003c0f05c0da04100400f05c0da00370400f9fc0d03c170367e0401003e7d034249f01003c170340d9ec1003c1705c0d0dc1003e7a0400f05c0d034240400f05c17036790400f03c3a036780401003c1703437034130400f05c2e034260400f03c12036770401003c170342b09c1003c170340f05c0d04c100400f05c0d0b02d0400f0480d034280400f09c17034270400f04c1003c2a0340d0981003c170480d9d81003c0f05c0d0ac100400f05c0d09c17034130400f03c17034260401003c12036759d01003c170340d09c1003c170400f05c0d04c260400f05c0d034290400f04817034280400f03c13034270400e034240400f03c0e034110401003c0e034250441003c0e0340d0441003c0e0400f0380d090110400f0380d034250400f0380e034110400f03c0e034110400d0901003c0e0380d0441003c0f0380d094100400f0380d044110400f0380d03c0e034240401003c0e034110941003c0e0340d0441003c0e0380d0441003c240400f0380d034110400f0380e034250400f03c0e034110401003c0e0341103c0e034220401003c12034150541003c0e0340d0501003c0e0380d0501003c220400f0380d034150400f0480e034150400f03c0e034140401003c0e034130380d0881003c0f0480d058100400f0380d058160400f0380d034160400f0381003c0e0342208c1003c120340d08c1003c0e0380d08c1003c0f0380d08c10034220400f03812034160400f03c0e034160401003c0e034160581003c0e034030080107c05014030080101c070140300801004200140300802004070140302c0800c020040101c0800c02008010180a00c030080101c0a028030080101c02004070140300c02004070140500c020040601c0500c02004010840500c02014030080101c060140300801004070140300802004070140300c020040b0140101c0800c02008010180800c030080101c1f07c03008010800707c0300801004000100300802004000780300c1e004000100400c020041e000040780200403008010000407803008010000001003078010041e0100300802004000101e0000400c02004010001e00c02078010000400c0300801078040101e0080100002004000100300c02004000780400c1e004000780400c0200401000040780201003008010000007803008010040001003078020041e01003078020040001017034180400f03c17036730401003c17036729c41003c170340d9c01003c180400f05c0d0626f0400f9b80d0366d0400f05c170366c0400f03c170341b0400d0601003c1705c0d9ac1003c0f05c0d9a8100400f9a40d9a2670400f05c0d03c1a034180401003c17034190741003c170340d0701003c1705c0d06c1003c180400f05c0d036660400f05e65036640400f03c17036630401003c17036620400f0380d058160400f0380d034160400f0380e034160400f03c0e034160400d0541003c0e0380d9841003c0f0380d050100400f0380d050140400f0380d03c0e034160401003c0e034160581003c0e0340d0581003c0e0380d0581003c150400f0380d034140400f0380e034140400f03c0e034140401003c0e034140380d0541003c0f0380d050100400f0380d050140400f0380d034140400f0380e034110400f03c0e034110401003c0e034130441003c0e0340d9801003c120400f0380d044110400f0380d034130400f0380e034110400f03c120365f0400d0441003c0e0380d0441003c0f0380d04c100400f0380d0465e0400f0480d03c0e034110401003c0e0341104c1003c0e0340d0441003c0e0480d9741003c110400f0380d034110400f0380e034130400f03c0e034110401003c120365c00c02004070280800c020040601c0800c02004010300a00c020080101c0800c060280300801004070200300802004070200300c020040b0280800c0200407008010180900c030080101c08020030080101807024030080100407020030080500c020040701c0500c02004010180500c020080101c0500c030080101805004070140300802004060140300c02004070140500c02004070180500c02004010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c03008010000405c0d0dc1003c0f05c0d0ec100400f96c0d0903b0400f05c0d0343b0400f05c1003c17034379681003c170340d0901003c1705c0d9641003c0f0e80d96010034370400f05c39036570400f03c17034240401003c17036569541003c170340f05c0d0dc100400f05c0d950240400f05c0d036530400f94817036510400f0dc1003e500340d0e01003c1705c0d0901003c0f05c0d0e0100400f05c0d0e01003c0e034150541003c0e0340d0541003c0e0380d0541003c0f0380d05010034160400f0380e034160400f03c0e034160401003c0e034160581003c0e0340f0380d054100400f0380d054150400f0380d034150400f0380e0364f0400f0541003c0e0340d0541003c0e0380d0541003c0f0380d054100400f0380d0500e034160400f03c0e034160401003c0e034160581003c0e0340d0581003c0e0380d9381003c0f0380d044100400f0380d044320400f0380d0364d0400f0381003c0e0364c0441003c0e0340d0441003c0e0380d92c1003c0f0380d92810034350400f0380e034110400f03c0e034110401003c0e034360d41003c0e0340f0380d0cc100400f0380d044110400f0380d034320400f0380e034340400f9241003c0e0340d0441003c0e0380d0441003c0f0380d0c8100400f0380d92002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c020040007802004070140500c020064701c1e00c020040101c0500c1e008010780500c070141e008010040b0140300802004070780300c1e004310140500c020041e008010c005078030080101c05078030080101c0b01403078010041e0140300805078020040b01c0500c02004010181e00c020780101c0500c030080107805004070241e00802004070200300c020042f0780800c1e004070780800c020041003c0e034160881003c0e0340d0581003c120380d0581003c0f0380d05810034160400f0380e034220400f03c12034160401003c0e034160581003c0e0340f0380d058100400f0380d088160400f0480d034160400f0380e034160400f0581003c0e0340d0881003c0e0480d0581003c0f0380d058100400f0380d0580e034160400f03c0e034220401003c12034160581003c0e0340d0581003c0e0380d0441003c0f0380d090100400f0380d044250400f0380d034110400f0381003c0e034110901003c0e0340d0441003c0e0380d0941003c0f0380d04410034110400f0380e034240400f03c0e034110401003c0e034250441003c0e0340f0380d044100400f0380d090110400f0380d034250400f0380e034110400f0441003c0e0340d0901003c0e0380d0441003c0f0380d094100400f0380d044030080102c05014030080101c060140300801004070140300802004070140301c0900c020040101c0800c02008010180800c030080101c09024030080108002004070240300c020043c0200800c020040701c0900c02004010800900c02024030080101c0b0200300801004070200300802004060240300c0200407024019180a00c020080101c0800c030080101c080280300801018070280300801004000101e00802004000103d0f40200400078040f41e00400078040f4020041e008010003d0f40300801000000780300801004000f403078020041e0f4030f40407802004010f40400c02008010f41e00c03078010f404010030080107802004000101e00c02004000101e00c02004000000400c1e004010780400c020101e0f40100000010030f40100400078030f41e004000100300c3d0041e010170341b0400f03c1a034180401003c17034339141003c170340d0cc1003c170400f05c0d910180400f05c0d036430400f05e42036410400f03c17036400400d8fc1003c1805c0d0601003c0f05c0d8f8100400f05c0d8f63c0400f05c0d03c170341b0401003c17034188ec1003e3a0340d8e41003c1705c0d8e01003e370400f05c0d034180400f05c17034410400f03c17036360401003e35036340400f0380d050150400f0380d034140400f0380e034140400f03c0e034140400d0501003c0e0380d0541003c0f0380d050100400f0380d050140400f0380d03c0e034160401003c0e034160581003c0e0340d0581003c0e0380d0581003c160400f0380d034160400f0380e034160400f03c0e034160401003c0e034160380d8cc1003c0f0380d054100400f0380d052320400f0380d036310400f03812036300400f03c0e034110401003c0e0341104c1003c0e0340d0441003c0e0400f0480d0a4110400f0380d034110400f0380e034130400f03c0e034110400d8bc1003c120380d0441003c0f0380d044100400f0380d04c110400f0380d03c120342d0401003c0e034110441003c0e0340d04c1003c0e0380d0441003e2e0400f0480d034110400f0380e034110400f03c0e034130401003c0e03411008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c03008010000401003008010003d00801018080283d0080101c070203d00801004060203d00802004070283d0183d00c020040101c3d00c02008010183d00c030080101c3d0f4030080101c020043d0140300c020043d0140500c020043d0f40500c02004010f40500c02014030080101c060140300801004070140300802004070140300c020040b0140101c0500c3d0f4010180500c030f40101c05014030f40101807014030f40105c0d8b41003c0f05c0d0dc100400f05c0d8b0240400f05c0d0362b0400f8a81003c17036290dc1003e280340d89c1003c1705c0d0901003c0f05c0d89810036250400f05c17034370400f03c17036240401003e23034248881003c170340f0e80d884100400f05c0d0de200400f05c0d034240400f05c170361f0400f8781003c170340d0dc1003c170e40d8741003c0f05c0d090100400f05c0d8700f0380d0fc100400f0380d0fc110400f0380d034110400f0380e034190400f86c1003c0e0340d8681003c0e0380d0441003c0f0380d044100400f0380d8640e036180400f03c0e036170401003c0e034110441003c0e0340d8581003c0e0400f0380d0f83e0400f0380d0343e0400f0380e0343e0400f03c0e0343e0400d8541003c0e0380d8501003c0f0380d044100400f0380d044320400f0380d0400f0380d050150400f0380d034150400f0380e034150400f03c0e034150400d0501003c0e0380d0541003c0f0380d054100400f0380d054150400f0380d03c0e034160401003c0e034160581003c0e0340d0581003c0e0380d0581003c160400f0380d034160400f0380e034160400f03c0e034160401003c0e034160380d1001003c0f0380d054100400f0380d054150400f0380d034150400f0380500c020041e02c05078020040101c0500c02008010181e00c030780101c050041e0200300802004070241e00c02004070201e00c020040601c0800c1e0040300801078080241e0080101e13020030080100407078030081e00407020030780500c020040101c05078020080102c0500c030080101c1e01403078010c4020041e0200307802004300240800c020040701c1e00c020040102c0800c1e008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c03008010000401003008010000f05c0d04c100400f05c0d09a120400f0480d034280400f05c17034270400f04c1003c170340d0981003c170480d8441003c0f05c0d840100400f04c0d09c17034130400f03c2e034260401003c120360f0ac1003c170340d09c1003c170400f05c0d04c260400f05c0d0360e0400f04827034280400f03c17034270400d04c1003c2a05c0d0981003c0f0480d834100400f05c0d0ac270400f05c0d03c170360c0401003c170341b0601003c170340d82c1003e0a05c0d8241003e080400f81c0d036060400f05c17034180400f03c17036050401003c170360405c0d0701003c0f05c0d06c100400f0680d060190400f05c0d0341d0400f05c1003c17036038081003c170340d0601003c1705c0d8041003c0f8000d7fc10035fe0400f05c18035fd0400f03c17034180401003c17035fc7ec1003c170340f0380d044100400f0480d7e8110400f0380d034110400f0380e034130400f0441003c0e0340d7e41003c120380d0441003c0f0380d044100400f0380d04c0e034110400f03c12035f80401003c0e034110441003c0e0340d04c1003c0e0400f0380d045f70400f0480d034110400f0380e034110400f03c0e034130400d0441003c0e0480d7d81003c0f0380d044100400f0380d044130400f0380d0400f0380d050140400f0380d034150400f0380e035f50400f03c0e034140400d0581003c0e0380d0581003c0f0380d058100400f0380d058160400f0380d03c0e034140401003c0e034140541003c0e0340d0501003c0e0380d0501003c140400f0380d034140400f0380e034150400f03c0e034140401003c0e034140380d0581003c0f0380d058100400f0380d058160400f0380d034160400f0380a00c020040b01c0800c02004010180a00c020080101c0800c030080101c08004070240300802004070200300c02004060240800c02004070180800c02004030080101c050140300801018070140300801004070140300802004060140301c0500c02004010180500c020080101c0500c030080101805014030080101c020040c0280300c02004070200a00c02004070180800c020040101c0800c02008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c03008010000401003008010000f05c0d7d0100400f0e80d7cc370400f05c0d035f20400f05c17034240400f7c41003c170340d7c01003c1705c0d0dc1003c0f0e40d7bc100400f05c0d091ee035ed0400f03c17035ec0401003c17034377ac1003c170340d0901003c170400f05c0d0e0380400f05c0d034370400f7a817034380400f03c17034240400d0ec1003c1705c0d0ec1003c0f05c0d0dc100400f05c0d0ec240400f7a40d0581003c0e0340d0581003c0e0380d0581003c0f0380d058100400f0380d0580e034150400f03c0e035e80401003c0e034150541003c0e0340d0541003c0e0400f0380d054140400f0380d034150400f0380e034150400f03c0e034150400d0581003c0e0380d0581003c0f0380d058100400f0380d058160400f0380d03c0e034150401003c0e034140541003c0e0340d0541003c0e0380d0541003c0f0380d79c100400f0380d799e50400f0380d034110400f0380e034110400f0d81003c0e0340d0d41003c0e0380d0d41003c0f0380d044100400f0380d0440e034320400f03c0e034340401003c0e034330441003c0e0340d0441003c0e0400f0380d0c9e40400f0380d035e30400f0380e034110400f03c0e034110400d0c81003c0e0380d7881003c0f0380d784100400f0380d044110400f0380d01403078010c41e0140300801004070141e008020040b0140300c02004070780102c0500c1e008010780500c1e008010c005014030080101c07078030080100c1e004070140500c020041e02c05078020040101c0500c02008010181e00c0702003078010041e0200300802004070241e00c02004070201e00c020042f0780101c0500c0300801078050141e0080101de00140300801004070780300802004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c020040003c17034270401003c17034130b01003c170340d0b41003c1209c0d0a01003c270400f05c0d034130400f0a817034260400f03c12035df0401003c170342b05c0d09c1003c0f05c0d04c100400f05c0d099de0400f0480d035dd0400f05c1003c130342704c1003c170340d0981003c170480d0a41003c0f05c0d0a010034270400f05c17034130400f03c2e034260401003c12035dc0ac1003c17034130400f0380d034220400f03812034150400f03c0e034150401003c0e034140380d0581003c0f0380d088100400f0480d058160400f0380d034160400f0381003c0e034230881003c0e0340d08c1003c120380d08c1003c0f0380d08c10034160400f0380e034220400f03c12034160401003c0e034160581003c0e0340f0380d050100400f0380d088150400f0480d034150400f0380e034140400f03c0e034110401003c0e034240441003c0e0340d0941003c0e0380d0441003c110400f0380d034240400f0380e034110400f03c0e034250401003c0e034110380d0441003c0f0380d090100400f0380d044250400f0380d034110400f0381003c0e034110901003c0e0340d0441003c0e0380d0941003c0f0380d04410034110400f0380e034240400f03c0e034110401003c0e034250441003c0e0341e008010000401003008010000007803008010040001003078020041e010030000407802004010000400c02008010001e00c030780100004010030080107802004000101e00c02004000101e00c02004000000400c1e004010780400c020101e0080100000010030080100400078030081e004000100300c020041e010010000407802008010000400c03008010001e01003078010001e0100300801028030080101c0b0200300801004070200300802004060280300c0200407028010840500c020080101c0500c030080101c05014030080101807014030080100c020040b0140500c02004070180500c020040101c0500c020080101c0500c0707c0300801004070200300802004060200300c020040707c1f00c02004200080101c0500c030080107c05014030080101c0701403008010042001403008140400f0380d034140400f0380e034140400f03c0e034150401003c0e034140380d0581003c0f0380d058100400f0380d058160400f0380d034160400f0381003c0e034160581003c0e0340d0581003c0e0380d0581003c0f0380d05810035db0400f0380e035da0400f03c0e035d90401003c0e034150501003c0e0340f0380d050100400f0380d050140400f0380d034150400f0380e034140400f03c0e034130401003c0e034110a41003c120340d0441003c0e0380d0441003c130400f0380d034110400f03812035d80400f03c0e034110401003c0e034110380d04c1003c0f0380d044100400f0480d0b4110400f0380d034110400f0381003c0e034130441003c0e0340d75c1003c120380d0441003c0f0380d04410034130400f0380e034110400f03c12035d60401003c0e034110441003c0e034030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c03008010000401003008010000001003008010f4030080101c070f40300801004060f40300802004070f40300c02004060f4010f40500c02008010f40500c03008010f40501403008010f43d014030080100c02004070140500c020040b01c0500c02004010180500c020080101c0500c06014030f40100407014030f43d004070140300c3d004060140500c3d0040700801018080f43d0080101c0a0203d00801018070283d00801004070203d0080f05c0d090100400f05c0d755d40400f05c0d034370400f74c17035d20400f0901003dd10340d7401003c1705c0d73c1003c0f05c0d0dc100400f05c0d73817034240400f03c17035cd0401003c3a035cc0dc1003c170340d72c1003c170400f05c0d091ca0400f05c0d035c90400f05c17034370400f03c39035c80400d0901003c1771c0d7181003c0f05c0d714100400f05c0d0ddc40400f05c0d0541003c0e0340d0541003c0e0380d0501003c0f0380d054100400f0380d0540e034160400f03c0e034160401003c0e034160581003c0e0340d0581003c0e0400f0380d058160400f0380d034160400f0380e034160400f03c0e034160400d0541003c0e0380d0541003c0f0380d100100400f0380d054150400f0380d03c0e034150401003c0e034150501003c0e0340d0541003c0e0380d0541003c0f0380d044100400f0380d70dc20400f0380d035c10400f0380e034110400f0441003c0e0340d7001003c0e0380d6fc1003c0f0380d6f8100400f0380d0440e0343e0400f03c0e0343e0401003c0e0343e0f81003c0e0340d0f81003c0e0400f0380d044320400f0380d035bd0400f0380e035bc0400f03c0e034110400d0441003c0e0380d0641003c0f0380d0fc100400f0380d0fc110400f0380d0181e00c020040101c0800c1e008010780800c1e0080101c09020030080101c02004070780300c1e004070200800c020041e01c0907802004016ec0800c02078030080101c3101403078010041e0140300802004070141e00c020040b0140101c1e00c020780102c0800c0300801078080241e008010c007020030080100c02004060780500c1e004070780500c020040102c05078020080101c0500c030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c03008010000401003008010000001003008010400f05c0d6e8270400f04c0d034130400f05c17034260400f03c12035b90400d0ac1003c1705c0d09c1003c0f05c0d04c100400f0b80d099b80400f0480d03c27034280401003c170342704c1003c170340d0981003c170480d6dc1003c2b0400f05c0d034270400f05c2a034130400f03c17034260401003c12035b605c0d0a01003c0f05c0d09c100400f05c0d04c260400f05c0d035b50400f0481003c0e034110441003c0e0340d0901003c0e0380d0441003c0f0380d09410034110400f0380e034110400f03c0e034240401003c0e034110941003c0e0340f0380d044100400f0380d044240400f0380d034110400f0380e034250400f0441003c0e0340d0441003c0e0380d0901003c0f0380d044100400f0380d0940e034110400f03c0e034110401003c0e034240441003c0e0340d0941003c0e0581003c0e0340d0581003c0e0380d0881003c0f0480d058100400f0380d0580e034160400f03c0e034160401003c0e034220581003c120340d0581003c0e0400f0380d058160400f0380d034220400f03812034160400f03c0e034160400d0581003c0e0380d0581003c0f0380d088100400f0480d058160400f0380d03c0e034160401003c0e034160881003c0e0340d0581003c120380d0581003c200240300801004070240300802004070200300c02004060200900c0200407008010800900c030080101c0902003008010f007020030080100407024030080900c020040701c0900c020040102c0800c020080101c0800c030080101809004070280300802005b40280300c02004070200800c02004070180a00c02004030080101c05014030080102c070140300801004060140300802004070140300c020041e0f43d07802004000003d00c02004010001e00c02078010003d00c1e01003008010043d0101e008020043d0100300c020043d0780400c1e0043d008010780400c1e0080100004010030080100000078030080100400010030780400c3d0041e000040783d004010000400c3d0f4010001e00c0307801000040041e0103d00802004000101e0f402004000101e0f40200400000040f41e0041003c17035b36c81003c170340d0601003c1705c0d6c41003c0f6c00d6bc10035ae0400f05c18035ad0400f03c17034180401003c17035ac6ac1003c170340f05c0d6a8100400f05c0d06c180400f05c0d035a90400f6a017035a70400f6981003da50340d6901003c1705c0d0601003c0f05c0d104100400f05c0d68c17034330400f03c170341b0401003c1a034180cc1003c170340d6881003c170400f0e40d684240400f05c0d035a00400f05c170359f0400f03c17034370400d6781003c1705c0d0901003c0f6740d670100400f05c0d66c370400f05c0d03c17034380401003c17034240e01003c170340d0e01003c176680d0dc1003c3b0400f05c0d034240400f664170343b0400f03c170343b0401003c170343705c0d6601003c0f05c0d090100400f05c0d65d960400f0e80d034370400f05c0d0541003c0e0380d0541003c0f0380d054100400f0380d654150400f0380d03c0e034150401003c0e034150541003c0e0340d0501003c0e0380d0541003c160400f0380d034160400f0380e034160400f03c0e034160401003c0e034160380d0541003c0f0380d054100400f0380d054140400f0380d034150400f0381003c0e034160581003c0e0340d0581003c0e0380d0581003c0f0380d058100400f0380d044110400f0380d034360400f0380e034350400f03c0e034350400d0441003c0e0380d0441003c0f0380d0c8100400f0380d0d0330400f0380d03c0e034110401003c0e034110c81003c0e0340d6501003c0e0380d64c1003c110400f0380d034110400f0380e034320400f03c0e035920401003c0e035910380d0441003c0f0380d044100400f0380d6418f0400f0380d0358e0400f03807014030080100407078030081e0040b0140300c020041e0140507802004300080101c0500c03008010181e014030780101c1e01403008010040b0141e0080800c02004070bc1e00c020040101c0800c1e008010780800c1e0080101c090058d0140300802004070780300c1e004070140500c020041e01c0507802004030080102c05078030080101c3101403078010041e0140300802004070141e00c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c020041003c120358c0ac1003c170340d09c1003c170a80d04c1003c0f05c0d098100358b0400f048170358a0400f03c17034270401003c17034130981003c170340f0480d0a4100400f05c0d0a0270400f04c0d034130400f05c17034260400f6241003c120340d0ac1003c1705c0d09c1003c0f05c0d04c100400f0b80d098120342d0400f03c27034280401003c170342704c1003c170340d0b01003c17034160400f0380e034160400f03c0e034160401003c0e034220581003c120340f0380d08c100400f0380d08c230400f0380d034220400f03812034230400f0581003c0e0340d0581003c0e0380d0581003c0f0380d088100400f0480d0580e034150400f03c0e034140401003c0e034140881003c0e0340d0541003c120400f0380d054140400f0380d034130400f0380e034220400f03c12034150401003c0e034250441003c0e0340d0441003c0e0380d0901003c0f0380d04410034250400f0380e034110400f03c0e034110401003c0e034240441003c0e0340f0380d094100400f0380d044110400f0380d034240400f0380e034110400f0941003c0e0340d0441003c0e0380d0441003c0f0380d090100400f0380d0440e034250400f03c0e034110401003c0e034110901003c0e0340d0441003c0e01003078010001e0100300801004000101e00802004000100300c0200400078010000400c1e008010780400c1e0080100004010030080100000078030080100c1e004000100400c020041e0000407802004010000400c02008010001e00c0001003078010041e0100300802004000101e00c02004000101e00c0200400078010000400c0300801078040101e008010000001003008010040007803008060140300801004070140300802004210140300c02004070140500c02004070080101c0500c030080101c05014030080102c07014030080100406014030081f00c02004070801f00c020040101c1f00c020080101c0800c030080101808004070140300802004200140300c02004070140500c020041f01c0500c0200403008010180a028030080101c0702803008010040b020030080200407020030400f05c0d621870400f6180d035850400f05c17034180400f03c17035840400d0741003c1705c0d0701003c0f05c0d06c100400f0680d060190400f05c0d03d83035820401003c17035816001003c170340d0601003c1705c0d5fc1003d7e0400f05c0d0357d0400f05c180357c0400f03c17034180401003c170357b05c0d5e81003c0f05c0d5e4100400f05c0d06c180400f05c0d035780400f5dc130400f0380d034110400f03812035760400f03c0e034110401003c0e034110380d04c1003c0f0380d044100400f0480d5d4110400f0380d034110400f0381003c0e034130441003c0e0340d5d01003c120380d0441003c0f0380d04410034130400f0380e034110400f03c12035730401003c0e034110441003c0e0340f0380d04c100400f0380d045720400f0480d034110400f0380e034110400f034160400f0380e034160400f03c0e034160401003c0e034160581003c0e0340f0380d050100400f0380d050140400f0380d034150400f0380e034140400f0501003c0e0340d0501003c0e0380d0501003c0f0380d054100400f0380d0500e034160400f03c0e034160401003c0e034160581003c0e0340d0581003c0e0400f0380d050140400f0380d034140400f0380e034150400f03c0e03571040010180800c020080101c0900c030080101c08024030080101807020030080100c02004060140500c02004070180500c020040101c0500c020080101c0500c070140300801004070140300802004060140300c02004070140500c02004060080101c0800c03008010300a020030080101c07028030080100406020030080800c020040702c0a00c020040101c0800c02008010180a00c030080101c080100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080d0581003c0e0380d0581003c0f0380d058100400f0380d058160400f0380d03c0e034160401003c0e034160581003c0e0340d0581003c0e0380d0581003c150400f0380d034150400f0380e034150400f03c0e034150401003c0e034400380d0541003c0f0380d054100400f0380d054150400f0380d034140400f0381003c0e034150541003c0e0340d0541003c0e0380d0541003c0f0380d050100400f0380d5c0110400f0380d034110400f0380e0356f0400f03c0e0356e0400d0f81003c0e0380d0f81003c0f0380d0f8100400f0380d0f83e0400f0380d03c0e0356d0401003c0e034110441003c0e0340d0c81003c0e0380d5b01003c3f0400f0380d034110400f0380e034110400f03c0e034190401003c0e0343f0380d5ac1003c0f0380d044100400f0380d0456a0400f0380d035690400f0380400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c0201c0907802004015a00800c020080101c1e00c030780101c08020030080107802004070141e00c020040b0141e00c02004070c40500c1e004010780500c020241e008010c007020030080100407078030081e0040b0200300c020041e0200102c05078020080101c0500c03008010181e014030780101c1e014030080107802004070240800c02004070181e00c020040101c0800c1e008010780800c1003c2e0342659c1003c120340d0ac1003c1705c0d09c1003c0f05c0d04c10034260400f05c12035660400f03c27034280401003c170342704c1003c170340f05c0d098100400f0480d5942b0400f05c0d034270400f05c2a034130400f0981003c170340d5901003c1205c0d0a01003c0f05c0d09c100400f05c0d04c17034260400f03c12035630401003c170356209c1003c130340d04c1003c170441003c0e0340d0941003c0e0380d0441003c0f0380d044100400f0380d0900e034110400f03c0e034250401003c0e034110441003c0e0340d0901003c0e0400f0380d044250400f0380d034110400f0380e034110400f03c0e034240400d0441003c0e0380d0941003c0f0380d044100400f0380d044240400f0380d03c0e034110401003c0e034250441003c0e0340d0441003c0e0380d0901003c0d0581003c120380d0581003c0f0380d058100400f0380d058220400f0380d03c12034160401003c0e034160581003c0e0340d0581003c0e0380d0881003c160400f0480d034160400f0380e034160400f03c0e034160401003c0e034220480d0581003c0f0380d058100400f0380d058160400f0380d034220400f0381003c12034160581003c0e0340d0581003c0e0380d0581003c0f0380d08810004070200300802004070240300c02004200240900c02004070f00800c02004030080101c0802403008010180702403008010040702403008020040b0200301c0800c02004010180a00c020080101c0a00c03008015840a020030080101c02004060140300c02004070140500c020040702c0500c020040101c0500c020200300801018070240300801004200240300802004070240300c02004070201e00c020043d0f40400c1e004010780400c02008010f40407803008010f40400400078030081e004000100300c020041e0100407802004000000400c02004030f4010001e01003078010001e010030f401004000101e0f43d00400010030001e0f40200401000040f41e00801078040f41e00801000040103d0080100002004000780300c1e004000f43d00c020041e0003d07802004010003d00c025801003c170340d57c1003c1705c0d5781003c0f0600d574100400f05c0d0615c0355b0400f03c170355a0401003c170355906c1003c170340d0601003c170400f05c0d105580400f05c0d035570400f55817035550400f03c17034180400d0cc1003c1705c0d5501003c0f05c0d0cc100400f05c0d06c180400f0680d03c17035530401003d52035515401003c170340d53c1003c1705c0d0601003c0e034160400f03c0e034160401003c0e034160581003c0e0340d0581003c0e0400f0380d058160400f0380d034160400f0380e034160400f03c0e034160400d0501003c0e0380d5381003c0f0380d534100400f0380d530150400f0380d03c0e034140401003c0e034140501003c0e0340d0501003c0e0380d0541003c140400f0380d034140400f0380e034140400f03c0e034140401003c0e034150441003c0e0340d04c1003c0e0380d0441003c0f0480d52c100400f0380d0440e034110400f03c0e034130401003c0e034110b41003c120340d0441003c0e0400f0380d044130400f0380d034110400f038120354a0400f03c0e034110400d0441003c0e0380d04c1003c0f0380d044100400f0480d524110400f0380d03c0e034110401003c0e034130441003c0e0340d0a41003c120380d0441003c010f40500c02008010f40500c03008010f40501403008010f43d014030080100c02004070140500c020040702c0500c020040101c0500c02008010180500c07014030f40100406014030f43d004070140300c3d004070140500c3d004060080101c080f43d00801018080283d0080101c060203d00801004070283d0083d00c020040601c3d00c020040101c3d00c02008010183d00c030080101c3d0100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c03008010000401003008010000001003008010040001003009480400f05c0d034240400f51c17035460400f03c17035450401003c170343705c0d5101003c0f05c0d090100400f05c0d50d420400f0e80d034370400f05c1003c39035410901003c170340d5001003c1705c0d4fc1003c0f05c0d0dc100353e0400f05c17034240400f03d3d0353c0401003c170353b0dc1003c170340f05c0d4e8100400f05c0d091390400f05c0d035380400f05d37034370400f04c1003c170340d0981003c170480d4d81003c0f05c0d4d4100400f05c0d09c17034130400f03c17034260401003c12034290a01003c170340d09c1003c130400f05c0d04c260400f0b80d035340400f048170342b0400f03c17034270400d04c1003c1705c0d0b01003c0f0480d0b4100400f09c0d0a0270400f05c0d03c2a034130401003c17034264cc1003c120340d0ac1003c1705c0d09c1003c0e034220400f03c12034230401003c0e0342308c1003c0e0340d08c1003c0e0400f0380d088160400f0480d034160400f0380e034160400f03c0e034160400d0881003c0e0480d0541003c0f0380d054100400f0380d050140400f0380d03c0e034220401003c12034150541003c0e0340d0501003c0e0380d04c1003c220400f0380d034160400f0480e034160400f03c0e034160401003c0e034160901003c0e0340d0441003c0e0380d0941003c0f0380d044100400f0380d0440e034240400f03c0e034110401003c0e034250441003c0e0340d0441003c0e0400f0380d090110400f0380d034250400f0380e034110400f03c0e034110400d0901003c0e0380d0441003c0f0380d094100400f0380d044110400f0380d03c0e034240401003c0e034110941003c0e0340d0441003c0e0380d0441003c0101c0500c02008010180500c030080101c05014030080101c0b014030080100c02004070200800c020040601c1f00c02004010801f00c020080101c1f00c1f0140300801004070140300802004070140300c02004200140500c02004070080102c0800c030080101c08028030080101807028030080100407028030080500c020040701c0500c02004010180500c020080101c0500c03008010840501003008010000007803008010040001003078020041e010030780200400010010000400c02008010001e00c0307801000040100300801078000101e0080100c02004000101e00c02004000000400c1e004010780400c02008010000407800010030080100400078030081e004000100300c020041e010040780200400008010000400c03008010001e01003078010001e0100300801004000101e008180400f0680d034190400f05c170341d0400f03c170341c0401003c170341b05c0d0601003c0f05c0d4c8100400f4c40d4c12f0400f05c0d0352e0400f05c1003c17034184b41003c170340d4b01003c1705c0d4ac1003c0f0600d4a810034180400f05d29035280400f03c17035270401003c170352606c1003c170340f05c0d060100400f05c0d495240400f05c0d035230400f48817035210400f0380d0541003c0f0380d050100400f0380d050140400f0380d034140400f0381003c0e034150501003c0e0340d0501003c0e0380d0501003c0f0380d05010034160400f0380e034160400f03c0e034160401003c0e034160581003c0e0340f0380d054100400f0380d480140400f0380d034140400f0380e034140400f0581003c0e0340d0581003c0e0380d0581003c0f0380d058100400f0380d058110400f0380d034110400f0380e034130400f03c0e034110401003c120351f0380d0441003c0f0380d044100400f0380d04c110400f0380d0351e0400f0481003c0e034110441003c0e0340d04c1003c0e0380d0441003c0f0480d47410034110400f0380e034110400f03c0e034130401003c0e034114701003c120340f0380d044100400f0380d044130400f0380d034110400f038120351b0400f0000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c0101c0500c020080101c0500c030080101805014030080101c06014030080100c02004070140500c020040601c0500c020040101c0500c02008010180500c070280300801004060200300802004070200300c020040c0280800c0200407008010180a00c030080101c08020030080101c0b028030080100407020030080900c020040601c0800c02004010180800c020080101c0900c030080101c08034370400f05c170351a0400f03c17034240401003d190351845c1003c170340f4580d0dc100400f05c0d0e0240400f05c0d034380400f05c17034380400f0dc1003c170340d0ec1003c174540d0901003c0f05c0d0ec100400f05c0d0ec17034370400f03c17035140401003c170342444c1003c170340d4481003c3a0400f05c0d0dd110400f0e40d034240400f05c17035100400f03c170350f0400d0cc1003c0e0380d0441003c0f0380d044100400f0380d0c8340400f0380d03c0e0350e0401003c0e034110441003c0e0340d0c81003c0e0380d4341003d0c0400f0380d034110400f0380e034110400f03c0e034320401003c0e0350b0380d4281003c0f0380d044100400f0380d045090400f0380d035080400f0381003c0e034350441003c0e0340d0441003c0e0380d0d81003c0f0380d0d4100380d0541003c0f0380d054100400f0380d054150400f0380d034140400f0381003c0e034160581003c0e0340d0581003c0e0380d0581003c0f0380d05810034150400f0380e034150400f03c0e034150401003c0e034150501003c0e0340f0380d058100400f0380d058160400f0380d034160400f0380e034160400f0541003c0e0340d0541003c0e0380d0541003c0f0380d054100400f0380d41c020040b0141e00c02004070141e00c020040601c0500c1e004010780500c020241e0080101c0702003008010042f078030081e004070200300c020041e0200101c0507802008014180500c030080101c1e014030780101c1e014030080107802004070140500c020040b01c1e00c02004010c40500c1e008010780500c300141e00801004070140300802004070780300c1e0040b0140500c020041e0000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c0e034160400f03c0e034220401003c12034160581003c0e0340d0581003c0e0400f0380d058220400f0380d034160400f0480e034160400f03c0e034160400d0581003c0e0380d0881003c0f0480d058100400f0380d058160400f0380d03c0e034160401003c0e034220581003c120340d0581003c0e0380d0581003c160400f0380d034220400f03812034160400f03c0e034160401003c0e034160441003c0e0340d0901003c0e0380d0441003c0f0380d094100400f0380d0440e034110400f03c0e034240401003c0e034110941003c0e0340d0441003c0e0400f0380d044240400f0380d034110400f0380e034250400f03c0e034110400d0441003c0e0380d0901003c0f0380d044100400f0380d094110400f0380d03c0e034110401003c0e034240441003c0e0340d0941003c0e0380d0441003c02004070240300c020040b0200800c02004070180900c020040101c0900c020280300801414070200300801004070200300802004060280300c02004070280102c0500c020080101c0500c030080101805014030080101c07014030080100c02004070240800c02004070180800c020040101c0900c02008010800900c0702403008010043c0200300802004070200300c02004070240900c02004200000407802004010000400c02008010001e00c03078010000401003008010783d004000101e00c3d004000101e00c3d004000000400c1e004010780400c3d0101e00801000000103d00801004000783d0081e004000103d0f4020041e010010003d07802008010003d00c03008010001e0f403078010001e0f40300801078020043d0100400c020043d0f41e00c02004010f40400c1e008010780400c0d06c1003c1705c0d0601003c0f4100d40c100400f05c0d409010400f05c0d03c17035000401003c17034181041003c170340d3fc1003c173f80d3f41003c1b0400f05c0d034180400f06817034330400f03c17034fc0401003c170343305c0d3ec1003c0f05c0d060100400f05c0d3e8f90400f3e00d034f70400f05c1003c18034f60601003c170340d3d41003c1705c0d3d01003c0f05c0d3cc100342d0400f0480e034110400f03c0e034110401003c0e034130441003c0e0340f0480d3c8100400f0380d044110400f0380d034130400f0380e034110400f3c41003c120340d0441003c0e0380d0441003c0f0380d04c100400f0380d04412034290400f03c0e034110401003c0e0341104c1003c0e0340d0441003c0e0400f0480d3c0110400f0380d034110400f0380e034130400f03c0e034110400e034160400f03c0e034160401003c0e034160581003c0e0340d0581003c0e0400f0380d3bc150400f0380d034140400f0380e034ee0400f03c0e034ed0400d0501003c0e0380d0541003c0f0380d050100400f0380d050140400f0380d03c0e034140401003c0e034150501003c0e0340d0501003c0e0380d0501003c160400f0380d034160400f0380e034160400f03c0e034160401003c0e034160080101c0500c030080101805014030080101c0701403008010040b014030080500c3d004070180500c3d0040101c0500c3d0f4010180500c030f40101c05004060203d00802004070283d0f40200407020080f4020040601c0a0f40200403008010183d0f4030080101c060f40300801004070f40300802004070f4030f40500c02004010f40500c02008010f40500c03008010f40501403008010f4000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c0200403008010000401003008010000001003008010040001003008020040001003034ec0400f0e817034370400f03c17034eb0401003c17034243a81003c170340f05c0d3a4100400f05c0d0dce80400f0e40d034240400f05c17034e70400f3981003c170340d0dc1003c1705c0d3941003c0f05c0d090100400f3900d38c17034e20400f03ce1034370401003c17034e00901003c170340d37c1003c170400f05c0d378370400f05c0d034dd0400f05cdc034240400f03c17034db0400f0380d058100400f0380d058160400f0380d034160400f0380e034160400f1001003c0e0340d0541003c0e0380d0541003c0f0380d054100400f0380d0540e034140400f03c0e034150401003c0e034150541003c0e0340d0541003c0e0400f0380d050150400f0380d034150400f0380e034150400f03c0e034150400d0581003c0e0380d0581003c0f0380d058100400f0380d058160400f0380d0343e0400f0380e0343e0400f03c0e0343e0401003c0e0343e0f81003c0e0340f0380d368100400f0380d364110400f0380d034110400f0380e034320400f0fc1003c0e0340d0fc1003c0e0380d0441003c0f0380d044100400f0380d0640e034d80400f03c0e034d70401003c0e034110441003c0e0340d3581003c0e0400f0380d354d40400f0380d034110400f0380e034110400f03c0e034d3040010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004008010780500c1e0080101c05014030080102c07078030080100431014030780800c020041e0c009078020040101c0800c020080101c1e00c030780102c080041e01403008020040b0141e00c02004070141e00c020040601c0500c1e0040300801078080241e0080101c07020030080100406078030081e00407020030780800c020040101c0907802008013480800c030080101c1e020030780101c0d04c1003c1705c0d0981003c0f0480d344100400f09c0d0a0270400f05c0d03c2a034130401003c17034263401003c120340d0ac1003c1705c0d09c1003c130400f05c0d034260400f05c12034cf0400f03c17034280401003c170342705c0d04c1003c0f05c0d098100400f0480d338cd0400f05c0d034270400f04c1003c17034130981003c2e0340d3301003c1205c0d0ac1003c0f05c0d09c10034cb0400f05c17034ca0400f03c17034180401003c17034c93201003cc70340f05c0d318100400f0600d314180400f05c0d034c40400f05c17034c30400f3081003c170340d06c1003c1705c0d0601003c0f3040d300100400f05c0d2fcbe034bd0400f03c17034bc0401003c17034182ec1003c170340d2e81003c170400f05c0d0701b0400f05c0d034180400f06817034190400f03c170341d0400f0380d050100400f0380d050150400f0380d034140400f0380e034140400f0581003c0e0340d0581003c0e0380d0581003c0f0380d058100400f0380d0580e034140400f03c0e034140401003c0e034152e41003c0e0340d0501003c0e0400f0380d058160400f0380d034160400f0380e034160400f03c0e034160400d0501003c0e0380d0501003c0f0380d054100400f0380d050140400f0380d034110400f03812034b80400f03c0e034110401003c0e0341104c1003c0e0340f0380d044100400f0480d2dc110400f0380d034110400f0380e034130400f0441003c0e0340d2d81003c120380d0441003c0f0380d044100400f0380d04c0e034110400f03c12034b50401003c0e034110441003c0e0340d04c1003c0e0400f0380d044b40400f0480d034110400f0380e034110400f03c0e03413040010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c0300801000040080101c0500c030080101805014030080101c06014030080100407014030080a00c020040c01c0800c020040101c0a00c02008010180800c030080101c080040b0280300802004070200300c02004060280800c020040701c0800c02004030080101c09020030080101c060240300801004070200300802004060200301c0500c02004010180500c020080101c0500c030080101c0501403008010180d0e01003c1705c0d0e01003c0f2cc0d0dc100400f05c0d0e0240400f05c0d03c170343b0401003c170343b0dc1003c170340d0ec1003c172c80d0901003cb10400f05c0d034b00400f0e817034370400f03c17034af0401003c170342405c0d2b81003c0f05c0d2b4100400f05c0d0dcac0400f0e40d034240400f05c1003cab034aa2a41003c170340d0dc1003c1705c0d2a01003c0f05c0d090100380d0c81003c0f0380d29c100400f0380d298110400f0380d034110400f0381003c0e034322941003c0e0340d2901003c0e0380d0441003c0f0380d04410034a30400f0380e034a20400f03c0e034a10401003c0e034110441003c0e0340f0380d0d8100400f0380d0d4350400f0380d034110400f0380e034110400f0c81003c0e0340d0d01003c0e0380d0cc1003c0f0380d044100400f0380d0440f0380d058100400f0380d058160400f0380d034160400f0380e034160400f0541003c0e0340d0501003c0e0380d0541003c0f0380d054100400f0380d0540e034160400f03c0e034160401003c0e034160581003c0e0340d0581003c0e0400f0380d054a00400f0380d034150400f0380e034150400f03c0e034150400d0541003c0e0380d0501003c0f0380d054100400f0380d054150400f0380d00c1e004070200800c020041e01c09078020040101c0800c02008010bc1e00c0701403078010041e0140300802004070141e00c020049f0141e00c0200407078010c40500c0300801078050141e0080101c0b014030080100407078030080500c1e0040b0780500c02004010c005078020080101c0500c030080101c1e0040701403078020041e01403078020040b0140500c02004070181e00c02004010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c03008010000404c0d09c1003c0f05c0d04c100400f05c0d098290400f0480d034280400f05c1003c170342704c1003c170340d0981003c2e0480d2781003c0f05c0d0ac10034270400f05c17034130400f03c170342c0401003c120342d0a01003c270340f05c0d09c100400f0a80d04c260400f05c0d0349d0400f048170342b0400f09c1003c170340d04c1003c1705c0d0981003c0f0480d270100400f05c0d26c1003c0e034160881003c0e0340d0581003c120380d0581003c0f0380d05810034140400f0380e034220400f03c12034150401003c0e034150501003c0e0340f0380d04c100400f0380d088150400f0480d034150400f0380e034140400f0581003c0e0340d0881003c0e0480d0581003c0f0380d058100400f0380d0580e034230400f03c0e034220401003c120342308c1003c0e0340d08c1003c0e0380d0441003c0f0380d090100400f0380d044250400f0380d034110400f0381003c0e034110901003c0e0340d0441003c0e0380d0941003c0f0380d04410034110400f0380e034240400f03c0e034110401003c0e034250441003c0e0340f0380d044100400f0380d090110400f0380d034250400f0380e034110400f0441003c0e0340d0901003c0e0380d0441003c0f0380d094100400f0380d044030080101c1f020030080101c0602003008010040707c03008020042007c0301c0500c020040107c0500c020080101c0500c030080101c05014030080108002004070280300c020040b0200800c02004070180a00c020040101c0a00c020140300801084070140300801004070140300802004060140300c02004070140102c0500c020080101c0500c030080101805014030080101c070140300801004000101e00802004000100300c02004000780400c1e004000780400c020041e008010000401003008010000007803008010040001003078020041e010030000407802004010000400c02008010001e00c030780100004010030080107802004000101e00c02004000101e00c02004000000400c1e004010780400c020101e0080100000010030080100400078030081e004000100300c020041e0100e034130400f03c0e034110401003c120349a0441003c0e0340d0441003c0e0400f0380d04c110400f0380d034990400f0480e034110400f03c0e034110400d04c1003c0e0380d0441003c0f0480d0a4100400f0380d044110400f0380d03c0e034130401003c0e034112601003c120340d0441003c0e0380d0441003c130400f0380d034110400f038120342d0400f03c0e034110401003c0e0341103c0e034970401003c0e034962541003c0e0340d0541003c0e0380d0501003c140400f0380d034140400f0380e034140400f03c0e034150401003c0e034140380d0501003c0f0380d050100400f0380d050150400f0380d034140400f0381003c0e034160581003c0e0340d0581003c0e0380d0581003c0f0380d05810034160400f0380e034160400f03c0e034160401003c0e034160581003c0e034030f40101805014030f40101c07014030f40100406014030f43d0040701403018080f4020040101c0a0f40200801018080f43d0080101c0a0203d0080101c02004070f40300c02004070f43d00c020040601c3d00c02004010183d00c0201403008010f43d01403008010043d01403008020043d0140300c020043d0140101c0500c020080102c0500c030080101c050140300801018070140300801004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c030080100004010030080100002004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c020040001017034240400f03c17034940401003c17034930dc1003c170340d2481003c390400f05c0d090910400f2400d0348f0400f05c17034370400f03c170348e0400d0901003c1705c0d2341003c0f05c0d230100400f22c0d0dc8a0400f05c0d03c89034240401003c170348821c1003c170340d0dc1003c1705c0d2181003c240400f05c0d034850400f05c3a034840400f03c17034370401003c17034830400f0380d054150400f0380d034400400f0380e034150400f03c0e034150400d0541003c0e0380d0541003c0f0380d050100400f0380d054150400f0380d03c0e034150401003c0e034150501003c0e0340d0541003c0e0380d0541003c160400f0380d034160400f0380e034160400f03c0e034160401003c0e034160380d0581003c0f0380d058100400f0380d058160400f0380d034160400f0380e034110400f03c0e034320401003c0e034822041003c0e0340d0441003c0e0400f0380d044190400f0380d0343f0400f0380e0343f0400f03c0e034110400d0441003c0e0380d2001003c0f0380d1fc100400f0380d1f8110400f0380d03c0e034110401003c0e0347d1f01003c0e0340d1ec1003c0e0380d0441003c3e0400f0380d0343e0400f0380e0343e0400f03c0e0343e0401003c0e0343e00c02004070780800c1e0040b0780800c02004010c009078020080101c0800c0607803008010040701403078020041e01403078020040b0140500c0200407008010181e00c030780101c080200300801078070241e0080100407020030081e00c020040701c0800c1e004010780800c020080101c0907803008011e80800407078030081e004310140300c020041e01405078020040702c0500c02004010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c03008010000405c0d0ac1003c0f05c0d09c100400f0a80d04c260400f05c0d034790400f0481003c170342809c1003c170340d04c1003c1705c0d0981003c0f0480d1e010034770400f05c13034270400f03c17034130401003c17034261d81003c120340f05c0d0ac100400f05c0d09c130400f05c0d034260400f0b812034750400f0a01003c270340d09c1003c1705c0d04c1003c0f05c0d098100400f0480d1d01003c0e034160581003c0e0340d0881003c0e0480d0581003c0f0380d05810034160400f0380e034160400f03c0e034220401003c12034160581003c0e0340f0380d058100400f0380d058220400f0380d034160400f0480e034160400f0581003c0e0340d0581003c0e0380d0881003c0f0480d058100400f0380d0580e034160400f03c0e034160401003c0e034220581003c120340d0581003c0e0380d0441003c0f0380d044100400f0380d090110400f0380d034250400f0381003c0e034110441003c0e0340d0901003c0e0380d0441003c0f0380d09410034110400f0380e034110400f03c0e034240401003c0e034110941003c0e0340f0380d044100400f0380d044240400f0380d034110400f0380e034250400f0441003c0e0340d0441003c0e0380d0901003c0f0380d044100400f0380d0943d0041e010030783d004000100400c3d004000001e00c3d004010000400c1e0103d00801078000101e00801004000103d00802004000783d0f41e00400010010783d00c02008010003d07803008010003d0780300801000000f4030780100c020041e01004078020043d0f40400c02004010f41e00c02078010f40400c1e0100300801004000101e00802004000100300c02004000780400c1e0040000c02004070280a00c020047301c0800c020040101c0800c02008010180a00c0701403008010040b0140300802004070140300c02004060140500c0200407008010800900c030080101c09020030080101c06020030080100407024030080900c020042001c0900c02004010f00800c020080101c0800c030080101c09004070240300802004070240300c020040b0200800c02004070180900c02004170343b0400f03c72034240401003c170343b0ec1003c170340d0dc1003c170400f05c0d1c4240400f05c0d034700400f05c3a0346f0400f03c17034370400d1b81003c3905c0d0901003c0f05c0d1b4100400f05c0d1b0370400f05c0d03c170346b0401003c17034241a81003c690340d1a01003c1705c0d0dc1003c380400f05c0d034240400f05c17034380400f03c17034380401003c67034370400f0380d054150400f0380d034150400f0380e034140400f03c0e034150400d0581003c0e0380d0581003c0f0380d058100400f0380d058160400f0380d03c0e034150401003c0e034150541003c0e0340d1981003c0e0380d0541003c150400f0380d034150400f0380e034150400f03c0e034140401003c0e034150380d0581003c0f0380d058100400f0380d058160400f0380d034160400f0380e034110400f03c0e034110401003c0e034321941003c0e0340d1901003c0e0400f0380d044110400f0380d034630400f0380e034620400f03c0e034610400d0441003c0e0380d0441003c0f0380d0d8100400f0380d0d4350400f0380d03c0e034110401003c0e034110c81003c0e0340d0d01003c0e0380d0cc1003c110400f0380d034110400f0380e034320400f03c0e034600401003c0e0345f008010000400c030080100004010030080100000010030080100400010030080400c02004000000400c02004010000400c02008010000400c030080100004004000100300802004000100300c02004000100400c02004000000400c02004030080100004010030080100000010030080100400010030080200400010030000400c02004010000400c02008010000400c0300801000040100300801000030080117805078030080101c0701403078010041e0140300802004070141e02c0500c020040101c1e00c02078010c40500c0300801078050141e0080101c02004070140300c02004070780500c1e0040b0780500c02004010c00507802014030080101c0607803008010040701403078020041e01403078020040b0140101c0800c02008010bc1e00c030780101c080200300801078070241e0080103c120345d0401003c170342b09c1003c170340d04c1003c170b80d0981003c2d0400f0480d034280400f09c17034270400f03c17034130401003c170342c0480d1701003c0f05c0d0ac100400f05c0d09c130400f0a80d034260400f05c1003c120345b1681003c170340d09c1003c1705c0d04c1003c0f05c0d09810034290400f04817034280400f03c13034270401003c17034130981003c170340f0380d094100400f0380d044110400f0380d034240400f0380e034110400f0941003c0e0340d0441003c0e0380d0441003c0f0380d090100400f0380d0440e034250400f03c0e034110401003c0e034110901003c0e0340d0441003c0e0400f0380d094110400f0380d034110400f0380e034240400f03c0e034110400d0941003c0e0380d0441003c0f0380d044100400f0380d090110400f0380d0400f0380d054140400f0380d034140400f0380e034220400f03c12034150400d0541003c0e0380d0501003c0f0380d04c100400f0380d088150400f0480d03c0e034160401003c0e034160581003c0e0340d0881003c0e0480d0581003c230400f0380d034230400f0380e034230400f03c0e034220401003c12034230380d0581003c0f0380d058100400f0380d058220400f0380d034160400f0480500c02004070800500c020040101c0500c020080107c0500c030080101c05004060280300802004070280300c02004070280800c020040b01c0800c02004030080101805014030080101c210140300801004070140300802004070140301c0500c020040101c0500c020080102c0500c030080101c050140300801018020040707c0300c020042007c1f00c020040701c0800c02004010180800c02078010000400c0300801078040101e0080100000010030080100400078030080400c1e004000780400c02004010000407802008010000400c03008010001e0040001003078020041e0100307802004000100400c02004000001e00c020040307801000040100300801078000101e0080100400010030080200400078030000400c1e004010780400c02008010000407803008010000407803008010000f05c0d164100400f05c0d160570400f0600d034180400f05c17034560400f1541003c170340d1501003c1705c0d06c1003c0f05c0d060100400f14c0d14817034510400f03c500344f0401003c170344e0601003c170340d1341003c170400f05c0d0741c0400f05c0d0341b0400f05c1a034180400f03c17034190400d1301003c4b05c0d1281003c0f05c0d124100400f05c0d060480400f05c0d0581003c0e0340d0581003c0e0380d0581003c0f0380d058100400f0380d0580e034140400f03c0e034140401003c0e034140541003c0e0340d11c1003c0e0400f0380d058160400f0380d034160400f0380e034160400f03c0e034160400d0501003c0e0380d0501003c0f0380d050100400f0380d054140400f0380d03c0e034140401003c0e034140501003c0e0340d0541003c0e0380d0501003c0f0380d04c100400f0380d044460400f0480d034110400f0380e034110400f04c1003c0e0340d0441003c0e0480d1141003c0f0380d044100400f0380d0440e034130400f03c0e034110401003c12034440441003c0e0340d0441003c0e0400f0380d04c110400f0380d034430400f0480e034110400f03c0e034110400d04c1003c0e0380d0441003c0f0480d108100400f0380d044110400f0380d020030080101c0c0280300801004070200300802004070280300c02004060200101c0800c020080102c0a00c030080101c08028030080101807020030080100c02004060200900c020040701c0800c02004010180900c020080101c0800c060140300801004070140300802004060140300c02004070140500c02004070080101c0500c030080101c050140300801018070140300801004060140300802004000100300c02004000100400c02004000000400c02004010000400c020100300801000000100300801004000100300802004000100300c0200400010010000400c02008010000400c030080100004010030080100000010030080100c02004000100400c02004000000400c02004010000400c02008010000400c000100300801004000100300802004000100300c02004000100400c0200400⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid 60 r := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_16 : ∀ i ∈ List.range' 16 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_24 : ∀ i ∈ List.range' 24 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_32 : ∀ i ∈ List.range' 32 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_40 : ∀ i ∈ List.range' 40 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_48 : ∀ i ∈ List.range' 48 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_56 : ∀ i ∈ List.range' 56 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_64 : ∀ i ∈ List.range' 64 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_72 : ∀ i ∈ List.range' 72 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_80 : ∀ i ∈ List.range' 80 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_88 : ∀ i ∈ List.range' 88 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_96 : ∀ i ∈ List.range' 96 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_104 : ∀ i ∈ List.range' 104 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_112 : ∀ i ∈ List.range' 112 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_120 : ∀ i ∈ List.range' 120 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_128 : ∀ i ∈ List.range' 128 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_136 : ∀ i ∈ List.range' 136 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_144 : ∀ i ∈ List.range' 144 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_152 : ∀ i ∈ List.range' 152 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_160 : ∀ i ∈ List.range' 160 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_168 : ∀ i ∈ List.range' 168 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test60_176 : ∀ i ∈ List.range' 176 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine h bad step60 (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 179 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h8 : i < 16
  · exact test60_8 i (by simp only [List.mem_range'_1]; omega)
  by_cases h16 : i < 24
  · exact test60_16 i (by simp only [List.mem_range'_1]; omega)
  by_cases h24 : i < 32
  · exact test60_24 i (by simp only [List.mem_range'_1]; omega)
  by_cases h32 : i < 40
  · exact test60_32 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 48
  · exact test60_40 i (by simp only [List.mem_range'_1]; omega)
  by_cases h48 : i < 56
  · exact test60_48 i (by simp only [List.mem_range'_1]; omega)
  by_cases h56 : i < 64
  · exact test60_56 i (by simp only [List.mem_range'_1]; omega)
  by_cases h64 : i < 72
  · exact test60_64 i (by simp only [List.mem_range'_1]; omega)
  by_cases h72 : i < 80
  · exact test60_72 i (by simp only [List.mem_range'_1]; omega)
  by_cases h80 : i < 88
  · exact test60_80 i (by simp only [List.mem_range'_1]; omega)
  by_cases h88 : i < 96
  · exact test60_88 i (by simp only [List.mem_range'_1]; omega)
  by_cases h96 : i < 104
  · exact test60_96 i (by simp only [List.mem_range'_1]; omega)
  by_cases h104 : i < 112
  · exact test60_104 i (by simp only [List.mem_range'_1]; omega)
  by_cases h112 : i < 120
  · exact test60_112 i (by simp only [List.mem_range'_1]; omega)
  by_cases h120 : i < 128
  · exact test60_120 i (by simp only [List.mem_range'_1]; omega)
  by_cases h128 : i < 136
  · exact test60_128 i (by simp only [List.mem_range'_1]; omega)
  by_cases h136 : i < 144
  · exact test60_136 i (by simp only [List.mem_range'_1]; omega)
  by_cases h144 : i < 152
  · exact test60_144 i (by simp only [List.mem_range'_1]; omega)
  by_cases h152 : i < 160
  · exact test60_152 i (by simp only [List.mem_range'_1]; omega)
  by_cases h160 : i < 168
  · exact test60_160 i (by simp only [List.mem_range'_1]; omega)
  by_cases h168 : i < 176
  · exact test60_168 i (by simp only [List.mem_range'_1]; omega)
  exact test60_176 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨1652,7,0xe91fbb817dfa4776e05bb71deff4777dc7747d1da341de9dc774d0772f71d97d11e9ac174f4472eb0597b5a7b9ed3ded2dee796f7b5a5d9ed2eed2d76796bb0da75c25bac3695f096af55a6fe65b7d56947996a3e5a63b65b1f96916d968b7d37b8223ddf4d76088bb4d96fe2537d36547894a3ad66f9ab37eb1dbe68edfad6519ab28eb1d4668ea39536f8e237e54d46388a335c69d66b4cd712f59a97959698ecb4e529a6394d39594b8eca5e5292e394977d669823b4df592e08e977dc63826b1df711609a8bdd963b2cb1f7298ec94c7dd945b2ca2f72916c948bc5663a63b1f1591698e8b792fb801fdde4b76007bb492f5e01fad24b5f807af8d57b8aabde319ee28cf78d55d8aaaee3197628cbbed27bba1bdfb4976e86bbd5575ae33af5555eb8caf45275de1bad1495f786af2d56fd2337cb554748ca32cf6fd2037cb3d47480a3d5269ae1b4f5492eb8697edb63ba631fb6d16e988bbd563a2331ef551688c8ba526396931e90d8e586c7a524596922e90d165868bab7ef19477aadf44651a27b7e901bf49ea3a4051d27b7cb01be59ea32c051968b6fb09b7da29fec24ff68b6dd09b6ea29f7424fbaeb3fb399fdba93ece49f6eb3dd399eeba9374e49bad36f52db7ab49fd4b4fead36d72db6bb49f5cb4faebb3f52127aaecf5c849ae439ef5d57790e745755a2a36ef153f7a8db4454fa2a33e3159f1a8938c549c6a33c5159e2a893145498a8b0e309871a2878c243c68b0c509862a287142438ae706f370b7b9c144dc2a2b70691f834ad85a47c2d2b704b1f825ad852c7c296e38f5354fab8e35cd53ae9aff5117faa683d4441ea9afd7117eba6835c441ae832ef05977a08fbc147de832d105968a08f44147a2e2fef357f7b883bcd41dee2fd1357e8b88344d41a2532e9651f494cb2d947963afe9590748ebf2d64196afb7b1bdbdabb1ec6d8f6afb5d1bdaeabb1746d8ba4ef7b6303d93bd758c0ba96f750f7baa581d43c0ea96f570f7aba5815c3c0aedfb6333631b7ed14cd88a09d74c073a42755b01cad51774e443a545d5b910ad39474d82ba4e515b60aad21174cc13a48455b304adc9d6ea8737727542a1ca12176ecc437485d43310a18146e84a376015ba10add8145084a2860154210aa1e116eb48b77809bad04dde1150b48a8780942d04a1e1768b4bb47821a2d10d1e174ab4ba578212ad10959976890bb46621a2410d19974a90ba566212a41095c9468a8a347215a2a0ad1c944aa8a2572152aa0a9539168d81344e452b6049521462cc2b148511330a8939162d81314e451360489adcfa9a6fd6b737269bb965ce2ee6f1597313b9b8931c7ad46bd4c717351ab9c107aa483d7005ea902f5c105ca482e700572902b97907a8083d5e05ea002f57905c8082e5e0572002b979c7480e3a5e35d201ae979c5680e2b5e355a01aad910748c0ba64415a302ad49c6ee06b752714381aa1d906eb08377605bac02ddd9050b0828760542c02a119c68c86b446712b21a9561668ec3b458592bb0e95a9068980b46a412a60295d9c62b0e3176358ac1ac5d9c44b0e22763512c1a89a9662983b16a591260e8901062bc0b1404112f0289d58f4ae4fa75635ab93adbdbeea26776f6f42899a12d8eed24f74b6343493a1e957ab8abd7a19eae0cf5e955cb8aae7a1972e0cb9b9574a033a6e555a80cad8956e88ab76219ba20cdd8955088aa862194220ca1d1568ac33474552ab0c95a156294ab168198a50cc5a154494aa268191250c89a7dfa1777d29f7705ddb8d74fa2fa7d3597e8bcbf4d74dc2fa6e359770bcbb877df47777a1df759dddac171f44717a05c7591c5ac8fde80bef423bba02ddd08fdca0bee523bb282dd94771e2771711dc711dc5885ba74695ba16e959a56ac73a68755b41ce929d56940f9fa4357d03e7710d5b8573fa6727d15cf719c9b8e7cf437e7a39b7d0ddbe8e7cd637e6b39b758ddbac279ee4f57709e7413d5a02b9745153a0ae559454ac9bc7a116bd26f17045ab8e367a353bd38d970d4eb8cb668293b432d928a4e94b39621dcb12ca988754c4b39441dca22ca91075488972f40f97a258fd03c7e8972d60f96b258f583c7ac7f2e2031f11fcb100c788517e7e4473d45f2791193217e1cc470c85f0f3118705a79be5bcc1696ef96b705479be2bcc1516ef8ab7ad7739a439eb5d56690ab95a6d8e5b6e5693e3969f7d76d82bb6df21b6090db7d74f82ba7df213e0909f4d16de2136d3453f8849fdda67b2d33f72d9ec96cfdda49b2d24f72d26c9693c5767a6433f15d2699093ada619a5b0eb690e696871d761ca430c75d0f29087c13f9a427cf04f6e909b7a96f3983f9ea5b5660fab913f38c279e44f56309abc16e7a43f3f05b2690f93a5079960bce9416e582b74506dde0b6d1413f7829f8d0678a833e3059e282cf8d0498a824e30526282935d061ea0b0d7410fa828785b7986dbce131e6198f385b5b86dade1316e198b76d879f24bcdb616fc92b79cf799203ce73d6e480b755b73e6639d56d57998ab85273861b9e14956186abe4f73b67b9f901ced80e7e4f55b67aaf90156d80ab9db6d92636e76d3e4989fcd26daa1b6f3493ea869fb4f6d9e7b6ed01b6780dbb4f4f9e7a7ed013e7809f55867e64b3d5612799293d37f92dbfcb4a3e4b51f2d37db2dbedb4a36cb51b6bb4f921a7cae97e484bf2bb4db21a6dae976c84bb62b7f3514798adf55451aa134f3452f984d35514baabbde121770aef70c85d86eb4e139a70ba9784e4bc2eb4c339a61ba970ce4b863f16d5b1368fc53d6c49e274674f2b389d1253ca9287167078b3a1899c1c4ce87149078a4a189241c492e746137a30b99584dcac2e744337a21b9950cdca8683cf9056fca0f36c15bb6cbcf329e79b2b7cca5be6cbcd529e6ab2b754a5baa7bbf90167c9eef6c059b692ff90d07ca4bf6c341b67b8ed01c769ea7b4053da7b8cf01c679ea73c0539edb5ed31af6b69bb4c4ddadb5cf31ae7b69b3cc4d9edbbe731df3b6b39cc59cedbbc931de4b6b324c5992c38e725c73b0a79c953cec38c925c64b0a72495392abbe119df0aab384659c2abbc319de1aab30c65986938e10d4f0a4e30c35386bf5792333cafd56c8ccb68f5730bab9a399cc2cce68f5550baaaa399542ccaa05df8be77c41776af9db51d1f8ca17c47476b285b5adde09a7706b770a69d85d9a78b0d3c762de2c16f1d9a5ab0d2d762d6ac16b5a9a72985b96a6952616a979a6c80d365e2db2016d979a4e80d275e2d3a0169dc1a66a4d33702d9a916cdc1a48a4d24702d229169191a608c5b064690a31685e9c78b86bc7a716ae1ab5d1978accbc7429e2b14f1d195aaccad74296ab14b5b9678a0b3c6e1de280ef1b965aa0b2d6e1d6a80eb529378d023c4a4d6b408b5e9c72b8e397a35cae1ae5e9c54b8e2a7a3552e1aa9b9c72a0e396e35ca81ae5b9c54a0e2a6e355281aa9a197294cb96829ca514e5a195494caa682952514a911672c43b944595310ea9e996cb85367a653ae149d1166cc43b644593b10e9d29c60d06b04a710b41a8511960c453044650b11485e9660b83b07a590ae0e8559360e8230564d0ba0885b52ec9e1f66d4b3a7879d0d2e6c21f3434b2308791b15789cabc6c19e270cf1b155a9caad6c196a70cb599278901bc66496a406b539b72d86394e6d53618a9815728433960555210ca969272f01b95a4953c06a981b6c84636606d3a1189dc956ca833672553aa0c9db126c9c9366c0db2706d9b124e9c9276c0d3a7069dc9566a8ab372199aa0ccdc9548a8aa4721922a0c919956690ab366199a40ccd9954890aa466192240c9181266841b36049221069169560f03305a550bc0c85c9260a8930720d82a06c1c9242a8921720d0aa0685577ec6747615df399d19ce77e037bf039a380dd1c0e77c237be139a308dd184df3f2339f93793c8cc9e4df3d4339ea379350cc9a84f6ec633f613db398cf9caf9e61bcf32bab986d5ccaf9c81bce42bab206d590073e63f27301cf20fc990df6e0333f037db08ccf84c73e02727031cf089c984c3072250b930c150942a8ab060190b02ac1086428476ff87707c1dbf69dc1b42f8e6534f30be3214d3905efe66b07317bf21ac190bf2e0239702f8f808c7c0bf2c2239612f8f088c784a3b721563928ed50558a88af6c097b62281b0240d88af4e097a72281382409cbbb66216332eed2085890eb266391b33ac920e46907af60010301ebd0804084a57779643be95d66590b38d4778aa3be315de28aef8d4598aa2ce3156628ab3ed177ba13bfb4566e84b32dd71d2738cb754f49ca745d65de732d1751f79c8f75465f62b2dd511fd8a8fd5165ae8b2f50996b84cbd5147ae8a3f5091eb848f5d75fea42fd75d07a9083bd45fa2a2fef157e88abfbd441a2a20ef150688a83a515f9612fe945065848329cf1d06f8ca734f41ba7e9cebb86f5fa7336e1b9bcdc77aae3bf335dea9aefcdc59aae2cf33566a9ab325677ce3bbc9596738eb3e5077b60bbf94166d82b39dc71926b8e7714e49aa7b50719e838ed05c6782e3b50539e829ed054e782a7e5c6bb66b5f97136d9a9b0d06bc20b5c341370829bcd965aa532f3651ea948f55065e60b2d5411f9828f85c5f866afe1710619a8399bf190678e66f4e419a7998e5904f2e6631e4138f81bdf8466fe06f0611983698dff04efda6307c13831d577ca33bc7556728cb3dd571b2ab8f719c6c8ce3dd553b2aa9f7194ec8ca73556bd6335cd553758c9b7d56582332df551e08c8fcbdf729efbb2bbdca5deecbdd929eecb2bb64a5db2b3af71dd7bacafdc757eeb3ad91dd6cacaf64757b29bdf111ef8a6bbc445de29bdd311ee9a6bb4c45da6b31f11d8f8ac8bc4745e2b31d31d8e9ac8b4c745a66bdeb717759af735c5d9a831eb058f5a08bac145d6831cd058e6a08b341459a6b4e5712f29ad31dc4b8ecb1e529172b2c71ca458e97a650f5b2a5e91c3d68edfa5f33d2fb7ad7ccd6bedfa4133d20b7ad04cd682c39eb25cf5b0abac955d6c39cd25ce6b0ab349559a1b3eb4927586cf352499aabce519e72aab79465bcaabcc719e63aab71c65b8e939e50dcf2a4ab94355ca939c70dce3a4ab1c3558e03cdf3d6ef80f304f5b82db9df3156fb6e704c558217677473bb85d9651ceb2ef9713b538bbe54ced4a6d76712fb38b59dc4bcee2d76532fb29b59d4cbcea6bf96b23cb5afa9ac8d4d6bf94d23ca6afa9348d49ad32e52d1f2b4cb1cb478ea32df1596fa88f7c547bea32c115960a88f04547828d7f68a47b635f62291b1d57f0ae478755f4ab91a5a1a76945bb686962516b18977688bbb6221da210ed8975888bac622162210b1d1176ac13b744562b04b1e9a70b8d387a2dc2e16e1e9a52b8d297a2d4ae16a5a1a7094d38682dc2516e1a1a5294d29682d4a516a559770e8438565d4ba10a541a6adc5b550693371699a176a94bb56821aa510d5a174c94ba66821325109989a6488d32622d92216c989a4688d23622d1a2168d71764f44325c5d1bd108d59a5ee85af566903a16814175edc42f505d03710818915e8812f624502204810d3eac2275434f3308999e56e4b63f2795b1ad8f8d553e4e6272554f1b9898dc9076a883b7205daa02edc9058a882c720562a02b199070908386605c2402e1990529082966054a402a5e106ab40b5784132d0299b10649c8326c0592702c9b10469c8236c051a7028d0905ec00af4241030028107df03f77801f748fdda4374f0572f80dd3495cba4977ea0fbf525a3a83d1d4977cc0fbe625a3303d1984f4e4632f213d3198cb8c5346a652b514d13194a98db47631a3b3695d8c4aecdb45831a2c369560c4ab0c37702543830dd48950a41b1704913806c549244a40315e3d12f00c500f44802fcf6536fb0bf3614dbb0bfcea23e752fb7a88dbd4bfccc23e662fb7308db9827bf64f67b09ef613d9b0cf8f02b4f833e348ad3a486ff0077f82183c01c1e086fd2077e92183481c1a4b7bea1f6752def307d9989f8ea134f527e3304d398b78de1fc6f2da7787d3bcb78c01fc602da7007d3808356a0533520d53014c989b55e1132f26d50044c80⟩
private def rows120 : List Rule := [
  .pool ⟨13,12,[13,2,3],[5,7,11],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨41,26,[41,2,17,19,23],[3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .prime 41,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨41,38,[41,2,13,17,19,23,29,37],[3,5,7,11,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨13,8,[13,2],[3,5,7],451,0x688580269400082c82200000008448a0800c0810005000001001903060c09800800000a00081030010512210000000441341000296401a116⟩,
  .pool ⟨13,8,[13,2],[3,5,7],41,0x1fffffffffe⟩,
  .pool ⟨31,13,[31,7,13],[2,3,5,11],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨41,4,[41,2],[3],105,0x1a2120482010830420104812116⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨11,10,[11,2,5],[3,7],1281,0x1b2c22d16032c948a0402c22820986136404900526d021224021020b40b40869b09104921900049864a28901345820248101301840201228840368805240a24a2906180810834c245a48004101921b04b4836126020800496890cb04204061825149140928045b00845120100860320204901068b20245149864800261248224365840b40b4102100912102d928024809b2186410510d008144a4d301a2d10d36⟩,
  .pool ⟨11,10,[11,2,5],[3,7],1271,0x1021508163300c5176c1a1b4445b123423e2ca4029903cf647175339b52495e600d4eec1cb1c934110dc3c2540fb0ae7d246b476f224b0bc38e2359659223e86c5400a275f9b9e552a1da12f4971f71070650b7a45ab518622051badf55c9e83aa65965398e342f29bb091921db418ae00fd5bc1c4e77d32c72c7480d4ff9842db526315151d9083f66afd2cb83bd23725ddd07a3c9171cff31976f57bf7e⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨41,14,[41,2],[3,5,7,11,13],33,0x1a2030116⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨41,8,[41,2],[3,5,7],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,4,[41,2],[3],31,0x121d47b6⟩,
  .pool ⟨41,27,[41,3,7,17,19,23],[2,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,10,[31,2,5],[3,7],1001,0x1b383a506a21c915a220315a93095c8f3424215428098e225938430cdb8742b8289020d5304899803200020a12f02021cb492b04807846c78a3a00e981322b5132065c0171478d88780483524b4e10103d214100013006644832ac102450750b876cc308726911c64050aa1090b3c4ea43256a301116a24e11582970736⟩,
  .pool ⟨31,10,[31,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨41,8,[41,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨11,5,[11,5],[2,3],861,0x1305261109068344b0422400d200021944b05b01841b2d304048b2ca09924064225105921040a09161029004141001b60a49204044800048808124941b60020a08025021a2414082126822910980926414d34480832d360860368348a6100012c009108348b0582422192832⟩,
  .pool ⟨31,13,[31,7],[2,3,5,11,13],205,0x60111860280e10524000005100001520414841a008080011282⟩,
  .pool ⟨13,8,[13,2],[3,5,7],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨31,26,[31,2,13,17,19,23],[3,5,7,11],41,0x1fffffffffe⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],1281,0x1024024000100908a00000208000001104009004240000204000000300140041000000900000001800220800040000000100200000200200040320004040200220001008008100001048004001000000840000020008004820000204004020001100100808001300800100100000100200000000800041100060000000240000020800a0030000000810000090802400822000000410000014424020000900902⟩,
  .pool ⟨41,14,[41,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨11,5,[11,5],[2,3],1281,0x1b2c22d16032c948a0402c22820986136404900526d021224021020b40b40869b09104921900049864a28901345820248101301840201228840368805240a24a2906180810834c245a48004101921b04b4836126020800496890cb04204061825149140928045b00845120100860320204901068b20245149864800261248224365840b40b4102100912102d928024809b2186410510d008144a4d301a2d10d36⟩,
  .pool ⟨41,21,[41,3,17,19],[2,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],77,0x129974700330038ba652⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],41,0x1fffffffffe⟩,
  .pool ⟨41,28,[41,2,17,19,23],[3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,21,[41,3,17,19],[2,5,7,11,13],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨31,22,[31,2,11,17,19],[3,5,7,13],41,0x1fffffffffe⟩,
  .pool ⟨41,7,[41],[2,3,5,7],5,0x2⟩,
  .pool ⟨41,5,[41,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨41,2,[41,2],[],105,0x1a2120482010830420104812116⟩,
  .pool ⟨41,16,[41,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨31,24,[31,2,3,17,19,23],[5,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨11,10,[11,2,5],[3,7],41,0x1fffffffffe⟩,
  .pool ⟨41,16,[41,2],[3,5,7,11,13],105,0x1a2120482010830420104812116⟩,
  .pool ⟨41,10,[41,2,5],[3,7],31,0x121d47b6⟩,
  .pool ⟨41,5,[41,5],[2,3],25,0x210863⟩,
  .pool ⟨41,10,[41,2,5],[3,7],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨41,10,[41,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨41,3,[41,3],[2],61,0x141002040810020a⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],21,0x130032⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],341,0x10005e2024580224044800c418080600000c000180000060000c000018040608c0048809100689011e8002⟩,
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨61,13,[61,7,13],[2,3,5,11],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨41,9,[41,3],[2,5,7],385,0x1eb22c242294609120621880b146080c7405a0210a160442790881a142101680b8c0418a34046118122418a51090d135e⟩,
  .pool ⟨31,13,[31,7,13],[2,3,5,11],41,0x1fffffffffe⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨61,8,[61,2],[3,5,7],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨61,8,[61,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨31,20,[31,2,5,7,17,19],[3,11,13],41,0x1fffffffffe⟩]
private def step120 : Stage := ⟨60,2,keys60,keys120,rows120,11,0xd01a0000000d01a000d68000006b3d64000006b1001ac357800001abb5680002e0000001702e000000170000dc1b8000000dc1b800071ab355838071aab5483802e0000001702e00000017d50000006a7d4c000006a503c0580b01e03c0580b01ed49a8f516a1d41a7f4f69d06da734d83606da6b4c83606ba634b83506ba5b4a83502804c0981402804c098140660d01a0330660d01a033d280dc1be93d240dc1be9103c0780f01e03c0780f01e0740d41a83a0740d41a83a01202c0580901202c058090680cc198340680cc19834d2002404e8fd1c02404e8d0760cc1983b0760cc1983b00e01c0380700e01c0380706fa334583706fa2b448370740d41a83a0740d41a83ad11a1f43685d09a0f41681d0002404e7fcfc02404e7d00f9f33d80700f9eb3c807cf19df3b675ce99cf39671ce00e01c66fcdc0e01c66d0120d41a8090120d41a8090160d01a00b0160d01a00bcd80f01e66bcd40f01e669cd199f33665cc998f31661cc00d41ae5fcbc0d41ae5d00a0140280500a014028050120600c0090120600c00900a0140280500a01402805cb80000065bcb40000065906d9632b83606d95b2a8360000d01a0000000d01a0000320640c8190320640c819ca994f29651ca193f2764dc980e01c64bc940e01c6490320dc1b8190320dc1b819c900e01c647c8c0e01c64501602c0580b01602c0580b06b9132183506b90b208350320640c8190320640c81906b9031f83506b8fb1e8350660d01a0330660d01a03306b8f31d83506b8eb1c8350320e41c8190320e41c8190140280500a0140280500a0680cc198340680cc19834c700dc1be37c6c0dc1be35c680d41ae33c640d41ae31c600dc1be2fc5c0dc1be2dc598af15629c5189f1362504e0a01402704e0a014027c4809813623c4409813621c4187f0f61dc3986f0d6190280500a0140280500a0140540c41882a0540c41882ac3185f0b615c2984f09611c2183f0760dc1982f056090120ac158090120ac1580900e01c0380700e01c038070160c01800b0160c01800bc1181f03605c0980f01601c000ac15dffbfc0ac15dfd00f7f2fd80700f7eafc807bf00b8175f7bec0b8175f501602c0580b01602c0580b06009c1383006009c138300540240482a0540240482a04e01c0382704e01c038270140280500a0140280500a0540c81902a0540c81902abe97cef95f1be17bef75edbd97aef55e9bd179ef35e500a0140280500a014028050000a0140000000a0140000000000000000000000000bc8000005e3bc4000005e1bc177eef5ddbb976eed5d9000000000000000000000001402c0580a01402c0580abb00b8175d7bac0b8175d505e0a81502f05e0a81502fba974ee95d1ba173ee75cd03209c1381903209c13819b9972ee55c9b9171ee35c5b8970ee15c1b816fedf5bd0320a8150190320a8150190596f2dd82c0596eadc82c05a02c0582d05a02c0582d0576e2db82b0576dada82b0140280500a0140280500a0520600c0290520600c029b696ced95b1b616bed75ad0016b2d58000016aad4800000000000000000000000000005c0b80000005c0b800b5169ed35a5b4968ed15a1b400000059fb3c0000059d000000000000000000000002c0780f01602c0780f01602c0780f01602c0780f01607c0fc1f83e07c0fc1f83e013672cd80901366acc80900f662cb80700f65aca8070160f41e80b0160f41e80b03f652c981f03f64ac881f045642c782204563ac6822b180801058bb140801058900f622c380700f61ac2807b0960ec1581b015febf57daf95eebd579af15debb575ae95ceb9571ae15beb756dad95aeb5569ad159eb3565ac958eb1561ac157eaf55d041572ad82004156aac82001207c0f80901207c0f809041562ab82004155aaa820013552a980901354aa88090800e81d0400800e81d040030014028180300140281800a0600c00500a0600c0050300600c0180300600c018aa008410d4fa9c08410d4d0000000000000000000000001532a580000152aa4800041522a382004151aa28200320640c8190320640c819a8950ea1541a814fe9f53da794ee9d539a714de9b535a694ce99531a614be9752d04802c0582404802c058240320640c8190320640c819a580801052ba540801052903f4a29381f03f49a9281f0320640c8190320640c8190160280500b0160280500ba4948e91521a4147e8f51d0454728d82204546a8c8220414628b82004145a8a820a2808c11d13a2408c11d11a2143e8750da1942e85509a100640cd07a0c0640cd0504b4128182504b40a808250000000000000000000000a00000004ff9fc000004fd00000000000000000000009f8000004fb9f4000004f90433e27b8210433da7a82100000000000000000000000000801000000008010000000000000000000000000002c0580b01602c0580b0169e93ce794f19e13be774ed9d8080104eb9d4080104e902604c0981302604c098139d139e734e59c938e714e19c007c0fcdf9bc07c0fcdd9b936e6d4d99b135e6b4d59a8038074d39a4038074d19a133e674cd99932e654c901603c0780b01603c0780b010040080080100400800801b3226380d01b31a6280d01402c0580a01402c0580a012008010090120080100900e01c0380700e01c0380701d3126180e01d30a6080e9812fe5f4bd9792ee5d4b9012020040090120200400900e01c0380700e01c0380701402c0580a01402c0580a00403006002004030060020200440881002004408810012024048090120240480900401c0380200401c038020252e25b8120252da5a81200000801000000008010000032d2598010032ca5880100000000000000000000000012c2578000012ba56800006010020030060100200300a0180300500a018030050040700e0020040700e0020372b25581b0372aa5481b03b2a25381d03b29a5281d94928e514a194127e4f49d0100540a8080100540a8080340640c81a0340640c81a0160080100b0160080100b0220540a8110220540a81101d2724d80e01d26a4c80e0040640c8020040640c8020160280500b0160280500b0160280500b0160280500b0312624b81803125a4a81892805c0bc9392405c0bc9100000000000000000000009200000048f91c0000048d000008010000000080100091800400c8b91400400c8991121e4348590920e41481000000000000000000000002c0580b01602c0580b0169011fe3f47d8f91ee3d47902a0440881502a0440881502804c0981402804c098148f003c07c778ec03c07c7500a0140280500a014028050120600c0090120600c00900a0140280500a014028050000d01a0000000d01a0000011d2398000011ca3880006d1c23783606d1ba3683606b1b23583506b1aa348350680cc198340680cc1983406b1a23383506b19a328350320640c8190320640c8190140280500a0140280500a0680cc198340680cc198348c80dc1bc638c40dc1bc610720640c8390720640c8398c00dc1bc5f8bc0dc1bc5d8b916e2d4598b115e2b45506b1522983506b14a288358a113e2744d89912e254498900e01c44788c0e01c4450320640c8190320640c81901602c0580b01602c0580b8880e01c4438840e01c44106b1021f83506b0fa1e8350320dc1b8190320dc1b81902e0000001702e0000001706e0000003706e000000378780000043b8740000043902e0000001702e000000178700000043786c000004358680e01c4338640e01c4318600000042f85c0000042d068000000340680000003403c0580b01e03c0580b01e02804c0981402804c098148580d41ac2b8540d41ac290660d01a0330660d01a03306f0a21383706f09a1283784908e1142184107e0f41d06d0720d83606d06a0c83603c0780f01e03c0780f01e83105e0b41582904e094110130420780901303a0680900e01c0380700e01c038070740d41a83a0740d41a83a8180dc1bc0b8140dc1bc090710220383807101a028380120d41a8090120d41a80980801c03c0380401c03c01800ffdff3fd7f8fedfd3f97f00d41abf77ec0d41abf57e80f01e3f37e40f01e3f106802c0583406802c058347e0fbdf73ed7d8fadf53e90660d01a0330660d01a03301202c0580901202c05809012fa1f3809012f99f280906a0e81d03506a0e81d0350760cc1983b0760cc1983b03209c1381903209c138197c8f8df13e17c0f7def3dd7b8f6ded3d97b0f5deb3d50540640c82a0540640c82a0160b41680b0160b41680b058f51e982c058f49e882c056f41e782b056f39e682b0140280500a0140280500a01402c0580a01402c0580a7980b8173cb7940b8173c905e0a81502f05e0a81502f790f1de33c5788f0de13c10520600c0290520600c0290000000000000000000000000f01df800000ef9de800000ef1dd800000ee9dc800770edddb3b5768ecdd93b100005c0b80000005c0b800760ebdd73ad758eadd53a9000000000000000000000003c0580b01e03c0580b01e750098133a774c098133a5748e8dd13a1740e7dcf39d0280500a0140280500a01405009c1382805009c138287380b81739b7340b81739904e0c01802704e0c01802701602c0580b01602c0580b0540240482a0540240482a73001c03b9772c01c03b950140280500a0140280500a0540c81902a0540c81902a728e4dc9391720e3dc738d718e2dc5389710e1dc338500e09c1380700e09c13807708e0dc1381700dfdbf37d6f8dedbd3796f0dddbb3750120ac158090120ac158090620a8150310620a8150316e8dcdb93716e0dbdb736d6d80ac15b6b6d40ac15b6900e01c0380700e01c0380706002c0583006002c058306d0000003676cc000003656c8d8db13616c0d7daf35d00000000000000000000000000a0140000000a014000000000000000000000000000a0140280500a01402805042d71ad821042d69ac8210000000000000000000000000d61ab800000d59aa800000000000000000000000004000000020040000000206a8000003536a4000003510000000000000000000000000000000000000000000002c0580b01602c0580b0166a0d3da734d698d2da534969007c0fb4768c07c0fb45688d0da1341680cfd9f33d678ced9d339670cdd9b335668080103336640801033102604c0981302604c0981303c0580b01e03c0580b01e66001c03b2f65c01c03b2d658cad95329650c9d93325648c8d91321640c7d8f31d040c718d820040c698c820630c5d8b315628c4d89311620c3d8730d618c2d85309610c1d83305608c0d81301040c017f820040bf97e8205f8080102fb5f4080102f90741002003a0741002003a012be17b809012bd97a80903e0240481f03e0240481f07c0fc1f83e07c0fc1f83e00ebd17980700ebc9788070160f41e80b0160f41e80b03ebc17781f03ebb97681f5d8088112eb5d4088112e9012ba173809012b997280900a0600c00500a0600c0050300600c0180300600c01800a0600c00500a0600c00500000000000000000000005c8000002e35c4000002e1042b816f821042b796e8210320640c8190320640c8190160280500b0160280500b5b8b6d6d2d95b0b5d6b2d55a807c0fad35a407c0fad1040b4167820040b396682059808c11acb59408c11ac9044b2163822044b19628225880640cac35840640cac158009412abf57c09412abd578aed5d2b9570add5b2b50320640c8190320640c819568acd592b1560abd572ad558aad552a9550a9d532a5548080102a3544080102a10320640c8190320640c819040a814f820040a794e820538a6d4d299530a5d4b29504802c0582404802c0582402a0440881502a0440881502804c0981402804c0981401ea514980f01ea494880f520a3d4728d518a2d4528900e01c0380700e01c0380701402c0580a01402c0580a0040300600200403006002510a1d43285508a0d41281010024048080100240480800e0080100700e00801007024a013f8120249f93e8120220400801102204008011012024048090120240480901e02c0580f01e02c0580f4f89ed3d2794f09dd3b275010040080080100400800801c9d13980e01c9c93880e00e01c0380700e01c038074e00380726f4dc0380726d4d803406a6b4d403406a690160280500b0160280500b004024048020040240480200a0180300500a0180300500000000000000000000004d0000002674cc0000026500800c0180400800c0180400000801000000008010004c800400a634c400400a610040640c8020040640c80200402c0580200402c0580202a0440881502a0440881501c9812f80e01c9792e80e01402c0580a01402c0580a01402c0580a01402c0580a03a9712d81d03a9692c81d0040700e0020040700e0020369612b81b0369592a81b0320680d0190320680d0194a894d292514a093d2724d02a0200401502a0200401549800400a4b49400400a490040000000200400000002000000000000000000000049091d2324548890d212414800000023f47c0000023d47805c0ba3b47405c0ba3900000000000000000000004700600c23746c0600c23502c0580b01602c0580b01603c0780f01e03c0780f01e0160d01a00b0160d01a00b4680f01e2334640f01e2314608bd1722d4588ad152294500d41aa2744c0d41aa2501289111809012889108090740d41a83a0740d41a83a01202c0580901202c058090680cc198340680cc198340760cc1983b0760cc1983b0128810f8090128790e80900e01c0380700e01c0380706e8710d83706e8690c8370740d41a83a0740d41a83a43085d0b21542884d092110120d41a8090120d41a80900e8410780700e8390680741882d0520941081d032054080e01c2034040e01c201000800ff8000007f8fe8003f80d81b1fb3f40d81b1f90000d01a0000000d01a00000a0140280500a0140280500a0140280500a0140280503002404818030024048183f07dcfb1f53e87ccf91f106a7c0f783506a7b8f68353d80dc1b9eb3d40dc1b9e93d00e01c1e73cc0e01c1e50320640c8190320640c8193c878cf11e13c077cef1dd3b80d41a9db3b40d41a9d90320dc1b8190320dc1b81901602c0580b01602c0580b070760eb838070758ea8380680cc198340680cc198343a80d41a9d33a40d41a9d10320640c8190320640c81906a740e783506a738e68353980dc1b9cb3940dc1b9c90320e41c8190320e41c8190140280500a0140280500a0660d01a0330660d01a033390000001c738c000001c5068000000340680000003406e0000003706e00000037388000001c3384000001c102e0000001702e00000017380000001bf37c000001bd0706f0dd8380706e8dc83800005c0b80000005c0b80003c0580b01e03c0580b01e06e6e0db83706e6d8da8373686ccd91b13606bcd71ad06c6b0d583606c6a8d48363500d41a9a734c0d41a9a502804c0981402804c098140660d01a0330660d01a03334868cd11a134067ccf19d33866ccd19933065ccb19500e09c1380700e09c138070540c81902a0540c81902a0140280500a0140280500a32864cc919132063cc718d0120ac158090120ac158090540c41882a0540c41882a31862cc518931061cc3185056610c182b056608c082b0160c01800b0160c01800b00e01c0380700e01c038073005fcbf17d2f85ecbd17901602c0580b01602c0580b04e0c01802704e0c0180270540240482a0540240482a00e5e0bb80700e5d8ba8072e80b8171732e40b81717100a0140280500a0140280500000000000000000000000000a0140000000a01400000000000000000000000002e00000016f2dc0000016d2d85acb51692d059cb31650140280500a0140280500a01402c0580a01402c0580a0540bc1782a0540bc1782a2c858cb11612c057caf15d05c570ad82e05c568ac82e2b055cab1552a854ca91512a053ca714d29852ca514903209c1381903209c138190160b41680b0160b41680b058520a382c058518a282c2880ac159432840ac159410320a8150190320a81501900000000000000000000000005009f8000004f89e8002780000013b274000001392704dc9b1352684cc9913102e0000001702e000000172604bc9712d2584ac9512900000000000000000000000300a4148180300a41481802c0780f01602c0780f01604e0a01402704e0a0140272500981312724c0981312524848c9112124047c8f11d0280500a0140280500a0142380000011b234000001192300841091722c08410915000000000000000000000000a0600c00500a0600c0050300600c0180300600c0180300140281803001402818228094129132240941291122043c8710d21842c851092100640c90720c0640c90520840c811012003fc7f0fd1f83ec7d0f91f03dc7b0f50403d0798200403c8788200320640c8190320640c8190403c0778200403b8768201d83ac750e91d039c730e504802c0582404802c058240320640c8190320640c81901402c0580a01402c0580a1c838c710e11c037c6f0dd03e3706d81f03e3686c81f0320640c8190320640c8190463606b8230463586a82304435069822044348688221a0080100cf19c080100cd040000000200400000002000000000000000000000000000000000000000000000000000000000000000000000033065800000328648000000000000000000000000190000000c718c000000c5042310618210423086082102c0580b01602c0580b0161802fc5f0bd1782ec5d0b91702dc5b0b51682cc590b102604c0981302604c09813160080100af15c080100ad1582ac550a915029c530a503e2905181f03e2885081f03c0580b01e03c0580b01e01402c0580a01402c0580a03a2804f81d03a2784e81d0040700e0020040700e0020362704d81b0362684c81b0320680d0190320680d01913025c4b09512824c4909102a0200401502a020040150040640c8020040640c8020220540a8110220540a81100402c0580200402c0580201c2404780e01c2384680e0160280500b0160280500b030230458180302284481811021c4308510820c41081000000000000000000000010005c0b87f0fc05c0b87d00000000000000000000000001f03d8000001e83c80000400000002004000000020021e03b8010021d83a80102c0580b01602c0580b01601e1d03980f01e1c83880f0e01bc3706d0d81ac3506902a0440881502a044088150260500a0130260500a0130241a033812024198328120220400801102204008011012024048090120240480900401c0380200401c0380202002004010020020040100c8038070630c40380706101603c0780b01603c0780b0c017c2f05d0b816c2d0590b0038070570ac0380705501402c0580a01402c0580a0a8034068530a403406851004024048020040240480200e01c0380700e01c038070180080100c0180080100c01402c0580a01402c0580a0a013c2704d09812c25049010024048080100240480800e01c0380700e01c0380700a0180300500a01803005006010020030060100200300000801000000008010000900040084708c0040084500000000000000000000000880000004308400000041⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid 120 r := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 125, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test120_125 : ∀ i ∈ List.range' 125 125, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test120_250 : ∀ i ∈ List.range' 250 125, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test120_375 : ∀ i ∈ List.range' 375 125, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test120_500 : ∀ i ∈ List.range' 500 124, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine h bad step120 (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 624 at hi
  by_cases h0 : i < 125
  · exact test120_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h125 : i < 250
  · exact test120_125 i (by simp only [List.mem_range'_1]; omega)
  by_cases h250 : i < 375
  · exact test120_250 i (by simp only [List.mem_range'_1]; omega)
  by_cases h375 : i < 500
  · exact test120_375 i (by simp only [List.mem_range'_1]; omega)
  exact test120_500 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨976,8,0xd5c7e2d5c76a5dc7a65dc72e94c9e194c9691cc9a51cc92d40c9d5b851d540c95db8515d048dd57c15d5048d5d7c155db8c999405199b8c9214051217c8d990415997c8d2104152134bdd53445d534bd5d34455de881d57081d5e809d57009d5e8815d70815de8095d70095dacbd99ac4599acbd21ac4521e88199708199e80999700999e88121708121e80921700921ac5dc9ac5d51e899c97021c9e89951702151345d8d345d1570998de8218d709915e82115c4d5c94c5dc9c4d5514c5d518899c91021c98899511021514cd58dc45d8d4cd515c45d1510998d88218d109915882115a0c9c928c9c9a051c92851c9a0c95128c951a05151285151dc8dc9648dc9dc15c96415c9dc8d51648d51dc1551641551a0c98d28c98da0518d28518da0c91528c915a05115285115dc8d8d648d8ddc158d64158ddc8d15648d15dc15156415151cbdc99445c91cbd51944551d081c95809c9d0815158095194bd8d1c458d94bd151c451558818dd0098d588115d0091510c9bd10c945c48dbdc48d4588c98188c9094c8d814c8d09aaebbd3273bdaaeb4532734532eb81aa738132eb09aa730990e9ed1871ed90e97518717554aded54ad7518e9b19071b118e939907139ccadb1ccad3960b9edd841ed60b975d84175247ded9c05ed247d759c0575d8b9b16041b1d8b9396041399c7db12405b19c7d3924053900b9ed7841ed00b975784175b47dedb47d7578b9b10041b178b9390041393c7db13c7d3978e9e10071e178e9690071693cade1b435e13cad69b4356978ade178ad6900e9a57871a500e92d78712db4ada53c35a5b4ad2d3c352d00ada500ad2d48b9e1c041e148b969c041690c7de18405e10c7d69840569c0b9a54841a5c0b92d48412d847da50c05a5847d2d0c052d9ce9d52471d59ce95d24715d60add5d835d560ad5dd8355d24e9999c719924e9219c7121d8ad99603599d8ad2160352130b9d5a841d530b95da8415de47dd5e47d5da8b999304199a8b9213041216c7d996c7d21cc41c9cc415154418d54411530e9bda871bd30e945a87145e4adbd6c35bde4ad456c3545a8e981307181a8e9093071096cad81e435816cad09e4350900b9bd7841bd00b945784145b47dbdb47d4578b98100418178b9090041093c7d813c7d09e2dbe16a63e1e2db696a6369a69fe12e27e1a69f692e27696adba5e263a56adb2de2632d2e9fa5a627a52e9f2da6272dd6e7d55e6fd5d6e75d5e6f5d9aabd52233d59aab5d22335d5ee799d66f995ee721d66f2122ab999a339922ab219a332174cdedec55ed74cd75ec55753891edb019ed389175b01975eccdb17455b1eccd39745539b091b13819b1b091393819395ccde1d455e15ccd69d455692091e19819e1209169981969d4cda55c55a5d4cd2d5c552d9891a52019a598912d20192d44cdd544cd5d0891d58019d508915d80195dbccd99bccd218091990819998091210819212c91c92c9151a4918da4911514cdbd14cd45c891bd5019bdc891455019458ccd818ccd09509181c81981509109c8190915dde08d65e015dd688d6568c9a1e05129e0c9a1685129688ddda41565a48ddd2c15652c51a1a4c929a451a12cc9292c0d9fba0d9f42859f7e859f0686bfe90e47e986bf710e47714a83e9c20be94a8371c20b710ebfad8647ad0ebf35864735c283ad4a0badc283354a0b3556efb9ce77b956ef41ce77411ab3b91ab341ceef7d56777dceef0556770592b37d92b30530e1e9a869e930e171a86971e4a5e96c2de9e4a5716c2d71a8e1ad3069ada8e1353069356ca5ade42dad6ca535e42d3554e1ddcc69dd54e165cc696518a5dd18a565cce1a15469a1cce12954692990a5a190a529b4a5d1b4a5593ca5953ca51dd8e1c56069c5d8e14d60694d9ca5c5242dc59ca54d242d4d60e189d8698960e111d8691124a5899c2d8924a5119c2d11c0e1b94869b9c0e14148694184a5b984a54148e17dc0697d48e105c069050ca57d0ca5052cdde9a465e92cdd71a46571e0a1e96829e9e0a171682971a4ddad2c65ada4dd352c653568a1ade029ad68a135e02935d495e9d41de9d49571d41d715c95ad5c1dad5c95355c1d35b0e9dd3871ddb0e96538716574adddec35dd74ad65ec356538e9a1b071a138e929b07129ecada17435a1ecad2974352920e9dd9871dd20e965987165d4addd5c35ddd4ad655c356598e9a12071a198e9292071295cada1d435a15cad29d435298cdddd14dddd8c65dd1465dd8cdd6514dd658c6565146565c8a1dd50a1ddc829dd5029ddc8a16550a165c829655029658cdda114dda18c65a11465a18cdd2914dd298c6529146529c8a1a150a1a1c829a15029a1c8a12950a129c8292950292908d1dd8059dd08d165805965bc95dd441dddbc9565441d6580d1a10859a180d1290859294495a1bc1da1449529bc1d29ecddd17465d1ecdd597465593829d138295974dd95ec659574dd1dec651db02995b0291dbca1b9bca14144a17d44a1055ac3d1d24bd15ac359d24b591e87d1960fd11e8759960f59d2c3955a4b95d2c31d5a4b1d9687951e0f9596871d1e0f1d1ccde99455e91ccd71945571d091e95819e9d0917158197194cdad1c55ad94cd351c55355891add019ad589135d019354cc1e9c449e94cc171c44971c4c1ad4c49adc4c1354c4935b855ddb855650491dd7c19dd0491657c19654055a14055297c91a10419a17c91290419296455d1645559dc5595dc551dd0c1d15849d1d0c1595849599485d11c0dd19485591c0d5958c195d0499558c11dd0491d1c8595940d951c851d940d1ddc55c5dc554d645589645511c4cdc54c55c5c4cd4d4c554d8891c51019c588914d10194d4ccd89c455894ccd11c455111091898819891091118819117c85c57c854d0485890485113455b93455417091b9e819b9709141e81941ac557dac5505e8917d70197de891057019056449b9644941a0c1b92849b9a0c1412849416485b9dc0db9648541dc0d41a085b9a08541dc497ddc490528c17da0497d28c105a04905dc857d640d7ddc8505640d0528857d2885053db5b8b53db83db540b53d400179b87901b8017940790140b5b57c3d3d7cb5b5043d3d0479797c01017c797904010104e9b3cee9b35671b39271b31a46d7e5be5fe546d76dbe5f6d8223e582236dbed7a9465fa9bed731465f310a23a90a2331c8e1e55069e5c8e16d50696d50e1a9c869a950e131c86931bcd5e5445de5bcd56d445d6d8099e50821e580996d08216d44d5a9bc5da944d531bc5d310899a98021a9089931802131b0e1d9b0e16174a5d9ec2dd974a561ec2d6138e19d38e125eca59d742d9deca525742d2550e1d9c869d950e161c86961c8e19d50699dc8e1255069256899d9e021d9689961e02161e0999d68219de0992568212598e1cd98e1555ca5cdd42dcd5ca555d42d5520e19120e119d4a5915c2d91d4a5195c2d198cd5cd145dcd8cd555145d55c821cdc8215514d5918c5d9114d5198c5d1950219150211980e1c10869c180e14908694944a5c1bc2dc144a549bc2d4908e18580698508e10d80690dbca585442d85bca50d442d0d385dc1385d49ec21c1ec2149b05d85b05d0d74218574210d2c69b52c693d68a5b568a53da46979a46901e0a579e0a50106c7cd7e4fcd06c7557e4f55ba8bcd4213cdba8b554213557ec791064f917ec719064f19428b91ba1391428b19ba1319ead3c1725bc1ead349725b49ae97c1361fc1ae9749361f4972d385ea5b8572d30dea5b0d369785ae1f8536970dae1f0da0b9e52841e5a0b96d28416d28b9a9a041a928b931a041311041d91041614c7dd9c405d94c7d61c4056188419d884125c47d9d4c059dc47d254c052570b9cde841cd70b955e84155347dcdac05cd347d55ac0555e8b991704191e8b919704119ac7d91340591ac7d1934051958b9c1d041c158b949d041491c7dc19405c11c7d49940549d0b985584185d0b90d58410d947d851c0585947d0d1c050d7cb9b57cb93db805b5b8053d04b97904b90140057940050129c9cca151cc29c954a15154dd8dcc6515ccdd8d54651554a1c990295190a1c918295118658d90dd1590658d18dd1518⟩
private def rows240 : List Rule := [
  .pool ⟨13,12,[13,2,3],[5,7,11],935,0x1021409022104c3114808160530a00a024625854194062c45720e1198410188500d6579082785226002c334412808b120227a5c11b84613c685310610129580634000a339622bc254910c3bd03308096900500ce54a5a352447098015818e525c50190c2b8c72b10712cec5212c534ab12d85335e⟩,
  .pool ⟨17,2,[17,2],[],91,0x6880c110a40602508830116⟩,
  .pool ⟨17,5,[17,5],[2,3],75,0x116026c145829b0536⟩,
  .pool ⟨17,7,[17],[2,3,5,7],13,0x161a⟩,
  .pool ⟨17,10,[17,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨17,5,[17,5],[2,3],241,0x11a0115e923660112012414509d84703886e428a0920122019b125ea20162⟩,
  .pool ⟨17,5,[17,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨17,5,[17,5],[2,3],341,0x1391b3318285d2b537d8ff0032d85325c10430f154528aa3c30820e93286d3003fc6fb2b52e85063336272⟩,
  .pool ⟨17,5,[17,5],[2,3],217,0x1530503d00a30404202c9942104008210a64d01080831402f02832a⟩,
  .pool ⟨17,10,[17,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨13,8,[13,2],[3,5,7],17,0x1a316⟩,
  .pool ⟨17,16,[17,2],[3,5,7,11,13],91,0x6880c110a40602508830116⟩,
  .pool ⟨17,13,[17,7,13],[2,3,5,11],1205,0x12d130e3139c1295e210d027a0c823504299a27956f389004b9c75a98f4242b62dcc6094d79d4423124505c138d2f3b86c51d02311250894e0006a0a5285804b590035390f38d2703445311223288b0392c73c272b0026b480685294158001ca4429223102e28d8773d2c720e828923108ae7aca418ced1b5090bc656b8e74802473daa791665082b104c17902c211ea520e7231c322d2⟩,
  .pool ⟨17,12,[17,2,3],[5,7,11],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨41,20,[41,2,5,7,19],[3,11,13,17],31,0x121d47b6⟩,
  .pool ⟨17,12,[17,2,3],[5,7,11],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨17,13,[17,7,13],[2,3,5,11],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨61,32,[61,2,19,23,29],[3,5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨241,31,[241,19,23,29],[2,3,5,7,11,13,17,31],91,0x30b96010868aa16e3d90272⟩,
  .pool ⟨41,25,[41,5,19,23],[2,3,7,11,13,17],51,0x21a0022996832⟩,
  .pool ⟨241,5,[241,5],[2,3],25,0x210863⟩,
  .pool ⟨241,7,[241],[2,3,5,7],5,0x2⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],17,0x1fffe⟩,
  .pool ⟨61,29,[61,19,23,29],[2,3,5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨17,12,[17,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨241,12,[241,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨241,5,[241,5],[2,3],217,0x1530503d00a30404202c9942104008210a64d01080831402f02832a⟩,
  .pool ⟨17,13,[17,7,13],[2,3,5,11],55,0x12081594076396⟩,
  .pool ⟨17,16,[17,2],[3,5,7,11,13],33,0x1a2030116⟩,
  .pool ⟨41,20,[41,2,5,7,19],[3,11,13,17],1275,0x4016100122816500102580d94522d22110416410d368105a29361324949b6080812420124522c240304b20b2884520432880c821a6d060b4d24d260929b6c109005844248245940060960365948b40864101b0430db0c149a4d84c165265801204b08849040b0900812c86cb2116910ca20b60861b6182914934992ca6cb0424092110122916520182590596522922114416c10d36c105a6936932594db6⟩,
  .pool ⟨17,12,[17,2,3],[5,7,11],671,0x4112107420c52556a305d00b5361936222c9d4b1066e314458e770a2942d21b79491d0da083e2759f0251382cf84f0765602794a96b2f018c5d973018f70d42cb3b83619312f744f38951954fad1d7b37d7fe⟩,
  .pool ⟨241,14,[241,2],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨17,14,[17,2],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],175,0x22a033e3a4d02674349a00ef8e93509df0d22a13ba3a⟩,
  .pool ⟨17,8,[17,2],[3,5,7],91,0x6880c110a40602508830116⟩,
  .pool ⟨17,4,[17,2],[3],91,0x6880c110a40602508830116⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],217,0x1530503d00a30404202c9942104008210a64d01080831402f02832a⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],671,0x4112107420c52556a305d00b5361936222c9d4b1066e314458e770a2942d21b79491d0da083e2759f0251382cf84f0765602794a96b2f018c5d973018f70d42cb3b83619312f744f38951954fad1d7b37d7fe⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],31,0x7ffffffe⟩,
  .pool ⟨31,20,[31,2,5,7,19],[3,11,13,17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨31,25,[31,5,19,23],[2,3,7,11,13,17],91,0x30b96010868aa16e3d90272⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  .pool ⟨17,3,[17,3],[2],35,0x228033a1a⟩,
  .pool ⟨17,9,[17,3],[2,5,7],35,0x228033a1a⟩,
  .prime 17,
  .pool ⟨17,11,[17,11],[2,3,5,7],35,0x228033a1a⟩,
  .pool ⟨41,30,[41,2,3,5,19,23,29],[7,11,13,17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨241,21,[241,3,19],[2,5,7,11,13,17],61,0x1713e6940a59f23a⟩,
  .pool ⟨241,2,[241,2],[],41,0x1b382b50736⟩,
  .pool ⟨241,10,[241,2,5],[3,7],119,0x141324470b0970652b11cb15977e⟩,
  .pool ⟨11,10,[11,2,5],[3,7],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨41,21,[41,3,11,19],[2,5,7,13,17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨241,10,[241,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨241,21,[241,3,19],[2,5,7,11,13,17],385,0x1eb22c242294609120621880b146080c7405a0210a160442790881a142101680b8c0418a34046118122418a51090d135e⟩,
  .pool ⟨17,13,[17,7,13],[2,3,5,11],31,0x7ffffffe⟩,
  .pool ⟨61,13,[61,7,13],[2,3,5,11],1205,0x12d130e3139c1295e210d027a0c823504299a27956f389004b9c75a98f4242b62dcc6094d79d4423124505c138d2f3b86c51d02311250894e0006a0a5285804b590035390f38d2703445311223288b0392c73c272b0026b480685294158001ca4429223102e28d8773d2c720e828923108ae7aca418ced1b5090bc656b8e74802473daa791665082b104c17902c211ea520e7231c322d2⟩,
  .pool ⟨241,2,[241,2],[],91,0x6880c110a40602508830116⟩,
  .pool ⟨241,10,[241,2,5],[3,7],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  .pool ⟨241,24,[241,2,3,19,23],[5,7,11,13,17],143,0x42148073495103e1b21836746511bad53de⟩,
  .pool ⟨41,37,[41,19,23,29,37],[2,3,5,7,11,13,17,31],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .prime 241,
  .pool ⟨31,22,[31,2,11,19],[3,5,7,13,17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨241,16,[241,2],[3,5,7,11,13],41,0x1b382b50736⟩,
  .pool ⟨241,22,[241,2,11,19],[3,5,7,13,17],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨241,22,[241,2,19],[3,5,7,11,13,17],15,0x116⟩,
  .pool ⟨241,8,[241,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨241,4,[241,2],[3],91,0x6880c110a40602508830116⟩]
private def step240 : Stage := ⟨120,2,keys120,keys240,rows240,11,0x5c0000002e05c0000002e05c0000002e05c0000002e0000b8170000000b8170000000b8170000000b8170000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b41680005a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0480801002404808010024048080100240480801002404009012020040090120200400901202004009012020042080100210420801002104408c1182204408c11822046088110230460881102304208010021042080100210400841082004008410820046088110230460881102304408c1182204408c11822040084108200400841082004408c1182204408c118220400901202004009012020048080100240480801002404408c1182204408c118220460881102304608811023048080100240480801002404009012020040090120200460881102304608811023042080100210420801002104408c1182204408c11822046088110230460881102304208010021042080100210400841082004008410820046088110230460881102304408c1182204408c118220400841082004008410820048080100240480801002404408c1182204408c11822046088110230460881102304808010024048080100240400901202004009012020046088110230460881102304408c1182204408c1182204009012020040090120208280801002982608010029052080100290520801002904104814820041044148200400a4148200400a41482004408c1182204408c118220460881102304608811023046088110230460881102304408c1182204408c11822042080100210420801002104208010021042080100210400841082004008410820040084108200400841082004608811023046088110230560801002b0560801002b0400ac158200400ac15820046088110230460881102304408c1182204408c118220400ac158200400ac158200560801002b0560801002b04408c1182204408c1182204608811023046088110230540801002a0540801002a0400a8150200400a815020046088110230460881102304408c1182204408c118220400a8150200400a8150200540801002a0540801002a04408c1182204408c1182200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084108000000841080004200000021042000000210000000000000000000000000000000000000000000004200000021042000000210000841080000008410800000000000000000000000004e0801002704e0801002704e0801002704e0801002704009c1382004009c1382004009c1382004009c13820042080100210420801002104408c1182204408c11822046088110230460881102304208010021042080100210400841082004008410820046088110230460881102304408c1182204408c11822040084108200400841082004c0801002604c0801002604408c1182204408c11822046088110230460881102304c0801002604c080100260400981302004009813020046088110230460881102304408c1182204408c118220400981302004009813020046088110230460881102304c0801002604c080100260400981302004009813020046088110230460881102304408c1182204408c11822040098130200400981302004c0801002604c0801002604408c1182204408c11822042080100210420801002104008410820040084108200400841082004008410820042080100210420801002104a0801002504a080100250400941282004009412820040094128200400941282004a0801002504a080100250000000000000000000000042000000210420000002100008410800000084108000000000000000000000000000000000000000000000000008410800000084108000420000002104200000021000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000901200000009012000000000000000000000000000000000000000000000000000901200000009012000048000000240480000002400000000000000000000000000000000000000000000048000000240480000002400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000540600c02a0540600c02a0300a8150180300a8150180300a8150180300a8150180540600c02a0540600c02a07002c0583807002c058380160e01c00b0160e01c00b0160e01c00b0160e01c00b07002c0583807002c0583882002c0580c81e02c0580c0160300600b0160300600b0170380600b0170340600b01802c0580c01802c0580c01802c0580c01802c0580c01604c0600b01604c0600b0160300600b0160300600b02602c0580c02602c0580c0300a8150180300a8150180300a8150180300a8150180540600c02a0540600c02a0540600c02a0540600c02a07002c0583807002c058380160e01c00b0160e01c00b0160e01c00b0160e01c00b07002c0583807002c0583801b0320580d01b02a0480d01802c0580c01802c0580c01604c0600b01604c0600b01b0220380d01b01a0280d80803406c0380403406c010160300600b0160300600b02602c0580c02602c0580c80003406bff7fc03406bfd0160400800b0160400800b082ff020bfb082fe820bf97f0fddfb3f57e8fcdf93f10160400800b0160400800b02002c0581002002c058107e0105f78417dc105f68417d8fadf53e97d0f9df33e502002c0581002002c058100160e01c00b0160e01c00b01a101f200d01a101f180d7c403406be17c003406bdf0160e01c00b0160e01c00b07002c0583807002c0583808003406bde08003406bdd01af71ed80d01af69ec80d07002c0583807002c058387b003406bd77ac03406bd503806c0d81c03806c0d81c0360700e01b0360700e01b7a803406bd37a403406bd101af41e780d01af39e680d0360700e01b0360700e01b03806c0d81c03806c0d81c01af31e580d01af29e480d0160400800b0160400800b790f1de33c5788f0de13c1780efddf3bd778eeddd3b90160400800b0160400800b02002c0581002002c05810770edddb3b5768ecdd93b1760ebdd73ad758eadd53a902002c0581002002c0581001aea1d380d01ae99d280d74803406ba374403406ba174003406b9f73c03406b9d01ae71cd80d01ae69cc80d01ae601c80d01ae5c1c80d72c0340683972a03406839728034068397260340683901ae481c80d01ae441c80d0540600c02a0540600c02a0300a8150180300a8150180300a8150180300a8150180540600c02a0540600c02a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000007200580b38f71c0580b38d02c1102181602c1102181602ce31c581602ce29c48160880580b0430880580b04371003406b8770c03406b8501ae102080d01ae0c2080d01ae09c080d01ae01bf80d6fc034068416fa03406841030df1bd818030de9bc81802002c0581002002c058100160400800b0160400800b030de1bb818030dd9ba8186e80600c3736e40600c3710160400800b0160400800b02002c0581002002c058106e00600c36f6dc0600c36d03806c0d81c03806c0d81c01adb1b580d01ada9b480d6d0034068426ce0340684203806c0d81c03806c0d81c0360700e01b0360700e01b6cc03406b656c803406b6301ad882100d01ad842100d0360700e01b0360700e01b01802c0580c01802c0580c6c003406b5f6bc03406b5d01ad71ad80d01ad69ac80d6b002c0580c6ae02c0580c0160300600b0160300600b01ad59aa80d01ad51a980d6a403406b516a003406b4f016d380600b016d340600b030d31a5818030d29a4818030d21a3818030d19a28186880600c3436840600c3416800600c33f67c0600c33d67802c05b3b67402c05b39016ce19b80b016cd99a80b016cd19980b016cc99880b66002c05b2f65c02c05b2d0160380600b0160380600b030cb195818030ca9948186500600c04064e0600c0400160300700b0160300700b01c02c0580c01c02c0580c64c0600c3256480600c323030c8820018030c842001801802c0580e01802c0580e02602c0580c02602c0580c0160300980b0160300980b01604c0600b01604c0600b01802c0581301802c0581303005c0b81803005c0b81802e0600c01702e0600c01702e0600c01702e0600c01703005c0b81803005c0b8180160319000b0160318f80b0160300600b0160300600b01802c05b1e01802c05b1d01802c0580c01802c0580c0160400800b0160400800b03cc718d81e03cc698c81e6300780f31762c0780f3150160400800b0160400800b02002c0581002002c058106280780f3136240780f31103cc418781e03cc398681e02002c0581002002c058100160740e80b0160740e80b0160740e80b0160740e80b03a02c0581d03a02c0581d03a02c0581d03a02c0581d030c3185818030c29848186100600c04160e0600c04160c0600c3056080600c303030c0820818030c04208186000580b2ff5fc0580b2fd5f80580b2fb5f40580b2f902cbe17b81602cbd97a81602cbd17981602cbc9788165e00580b2ef5dc0580b2ed5d80580b2eb5d40580b2e902cba17381602cb997281602cb917181602cb89708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022b816f811022b796e81102002c0581002002c058100160400800b0160400800b022b716d811022b696c8115b004408ad75ac04408ad50160400800b0160400800b02002c0581002002c058105a804408ad35a404408ad101ab416780d01ab396680d01ab316580d01ab296480d59003406ac758c03406ac558803406ac358403406ac101ab002000d01aafc2000d01802c0580e01802c0580e0160300700b0160300700b01aaf95e80d01aaf15d80d57403406840572034068400160300700b0160300700b01802c0580e01802c0580e57003406ab756c03406ab50160300600b0160300600b016ad00600b016acc0600b01802c0580c01802c0580c56402c0580c56202c0580c0160300600b0160300600b01aac01f80d01aabc1f80d55c03406aad55803406aab0160300980b0160300980b01802c0580c01802c0580c5540340683f5520340683f01aaa15380d01aa995280d01802c0581301802c0581300400c0180200400c0180200400c0180200400c0180200600801003006008010030060080100300600801003008004008040080040080400a00c0180700a00c01807006014028030060140280300800400804008004008040020100200100201002001006014038030060140380300a00c0180500a00c01805002010020010020100200100c00c0180600c00c018060060180300300601803003006018030030060180300300c00c0180600c00c0180600400c0180200400c018020060080100300600801003006008010030060080100300400c0180200400c01802008004008040080040080400a00c0180600a00c01806006014028030060140280300800400804008004008040020100200100201002001006014030030060140300300a00c0180500a00c018050020100200100201002001006020040030060200400301000c0180801000c0180801000c0180801000c018080060200400300602004003006008010030060080100300400c0180200400c0180200400c0180200400c0180200600801003006008010030020000000100200000001000004008000000040080000000400800000004008000020000000100200000001002010020010020100200100800400804008004008040080040080400800400804002010020010020100200100400c0180200400c018020060080100300600801003006008010030060080100300400c0180200400c01802012004008090120040080900400c0180200400c01802006008010030060080100301200400809012004008090020240480100202404801006008010030060080100300400c0180200400c01802002024048010020240480101000c0180801000c018080060200400300602004003006020040030060200400301000c0180801000c01808014a915180a014a895080a5400280529f53c0280529d5380280529b53402805299014a614b80a014a594a80a00601c0280300601c0280300601c0280300601c0280300e00c0180500e00c0180500e00c0180500e00c01805002000000010020000000100200000001002000000010000040080000000400800000004008000000040080000a00c0180600a00c0180600a00c0180500a00c018050060140300300601403003006014028030060140280301000c0180801000c018080020000000100200000001000004008000000040080001000c0180801000c018080060200400300602004003000004008000000040080000200000001002000000010060200400300602004003012004008090120040080900400c0180200400c01802006008010030060080100301200400809012004008090020240480100202404801006008010030060080100300400c0180200400c0180200202404801002024048010060200400300602004003006020040030060200400301000c0180801000c0180801000c0180801000c0180805a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81703e05e0b81703e05c0bc1782e05c0bc1782e07c0b41f02c07c0b41f02c05a0b01602d05a0b01602d05c0bc1f02e05c0bc1f02e05e0b81702f05e0b81702f05a0f81603e05a0f81603e0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b4168000000b8170000000b8170000000b8170000000b81700005c0000002e05c0000002e05c0000002e05c0000002e0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05c0f81782e05c0f81782e05c0bc1782e05c0bc1782e07c0b81702f07c0b81702f0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05c0bc1f02e05c0bc1f02e05e0b81702f05e0b81702f05e0b81703e05e0b81703e05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c046088110230460881102304c0801002604c080100260400981302004009813020046088110230460881102304408c1182204408c11822040098130200400981302004c0801002604c0801002604408c1182204408c11822046088110230460881102304c0801002604c080100260400981302004009813020046088110230460881102304408c1182204408c11822040098130200400981302004c0801002604c0801002604408c1182204408c11822042080100210420801002104008410820040084108200400841082004008410820042080100210420801002104a0801002504a080100250400941282004009412820040094128200400941282004a0801002504a0801002504009c1382004009c1382004009c1382004009c1382004e0801002704e0801002704e0801002704e0801002704408c1182204408c118220400841082004008410820042080100210420801002104408c1182204408c1182204608811023046088110230420801002104208010021040084108200400841082004608811023046088110230000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004200000021042000000210000000000000000000000000000000000000000000004200000021042000000210000841080000008410800000000000000000000000000000000000000000000000000841080000008410800000000000000000000000004800000024048000000240000901200000009012000000000000000000000000000000000000000000000000000901200000009012000048000000240480000002400000000000000000000000480801002404808010024048080100240480801002404009012020040090120200400901202004009012020046088110230460881102304208010021042080100210400841082004008410820046088110230460881102304408c1182204408c118220400841082004008410820042080100210420801002104408c1182204408c1182204208010021042080100210420801002104208010021040084108200400841082004008410820040084108200460881102304608811023046088110230460881102304408c1182204408c1182204408c1182204408c1182204608811023046088110230560801002b0560801002b0400ac158200400ac15820046088110230460881102304408c1182204408c118220400ac158200400ac158200560801002b0560801002b04408c1182204408c118220400a8150200400a815020046088110230460881102304408c1182204408c118220400a8150200400a8150200540801002a0540801002a04408c1182204408c1182204608811023046088110230540801002a0540801002a0400901202004009012020046088110230460881102304408c1182204408c118220400901202004009012020048080100240480801002404408c1182204408c11822046088110230460881102304808010024048080100240400841082004008410820046088110230460881102304408c1182204408c118220400841082004008410820042080100210420801002104408c1182204408c11822046088110230460881102304208010021042080100210400901202004009012020046088110230460881102304408c1182204408c118220400901202004009012020048080100240480801002404408c1182204408c11822046088110230460881102304808010024048080100240400a41e8200400a41e820040a5014820040a4c148200520801003d0520801003d524080100295220801002900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084108000000841080004200000021042000000210000000000000000000000000000000000000000000004200000021042000000210000841080000008410800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005200580b28f51c0580b28d02ca314581602ca294481602ca214381602ca19428165080580b2835040580b28102ca013f81602c9f93e81602c9f01e01602c9ec1e0164f40580b2794f00580b2774ec0580b03c4ea0580b03c0160380700b0160380700b01a9d13980d01a9c93880d4e003406a6f4dc03406a6d0160380600b0160380600b01c02c0580e01c02c0580e4d803406a6b4d403406a6901a9a13380d01a9993280d01c02c0580c01c02c0580c0169913180b0169893080b0169800600b01697c0600b4bc02c05a5d4b802c05a5b4b402c0580c4b202c0580c01604c0600b01604c0600b01a0d81900d01a0d81900d4b0034068374ae0340683701604c0600b01604c0600b02602c0580c02602c0580c06c0340683206c0340683201a9581b80d01a9541b80d02602c0580c02602c0580c4a804408a534a404408a510160400800b0160400800b02002c0581002002c058104a004408a4f49c04408a4d022931258110229292481102002c0581002002c058100160400800b0160400800b022921238110229192281148803406a4348403406a414800340683047e0340683001a8f91e80d01a8f11d80d01a8e81800d01a8e41800d0160e01c00b0160e01c00b0160e01c00b0160e01c00b07002c0583807002c0583807002c0583807002c058380160300980b0160300980b01a8e11b80d01a8d91a80d46803406a3346403406a310160300980b0160300980b01802c0581301802c0581346003406a2f45c03406a2d01a8b11580d01a8a91480d01802c0581301802c058130160400800b0160400800b0740cc1d03b0740cc1d03b4500dd1383744c0dd128370160400800b0160400800b02002c0581002002c058100660e81d83a0660e81d83a06e8901ba2306e8881ba2102002c0581002002c058100300a8150180300a8150180540600c02a0540600c02a0540600c02a0540600c02a0300a8150180300a8150180360700e01b0360700e01b44003406a1f43c03406a1d01a8710d80d01a8690c80d0360700e01b0360700e01b03806c0d81c03806c0d81c01a8610b80d01a8590a80d42803406a1342403406a1103806c0d81c03806c0d81c0160e01c00b0160e01c00b01a8410780d01a8390680d41803406a0b41403406a090160e01c00b0160e01c00b07002c0583807002c0583841003406a0740c03406a0501a8110180d01a8090080d07002c0583807002c058380160400800b0160400800b4007fcff1fd3f87ecfd1f93f07dcfb1f53e87ccf91f10160400800b0160400800b02002c0581002002c058103e07bcf71ed3d87acf51e93d079cf31e53c878cf11e102002c0581002002c0581001a780ef80d01a778ee80d3b8034069db3b4034069d93b0034069d73ac034069d501a750e980d01a748e880d3a0034069cf39c034069cd072034069cc072034069cb01a728e480d01a720e380d01a0e4e300d01a0e4e280d0540600c02a0540600c02a0300a8150180300a8150180300a8150180300a8150180540600c02a0540600c02a0160e01c00b0160e01c00b07002c0583807002c0583807002c0583807002c058380160e01c00b0160e01c00b0160301900b0160301900b38802c0580c38602c0580c01802c0583201802c058320167080600b0167040600b02602c0581302602c0581302602c0580c02602c0580c01604c0980b01604c0980b01604c0600b01604c0600b0540600c02a0540600c02a0300a8150180300a8150180300a8150180300a8150180540600c02a0540600c02a02c700df81602c6f8de81602c6f0dd81602c6e8dc8163700580b1b736c0580b1b53680580b1b33640580b1b100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160300700b0160300700b0306c0d78180306b8d68183580600c1ab3540600c1a90160380700b0160380700b01802c0580e01802c0580e3500600c1a734c0600c1a5030690d1818030688d081801c02c0580e01c02c0580e016680cf80b016678ce80b0160300600b0160300600b33802c0599b33402c0599901802c0580c01802c0580c03005c0b81803005c0b81802e0600c01702e0600c01702e0600c01702e0600c01703005c0b81803005c0b818016030cc00b016030cb80b016658ca80b016650c980b01802c0599201802c0599132002c0598f31c02c0598d01604c0980b01604c0980b02602c0580c02602c0580c02602c0581302602c0581301604c0600b01604c0600b0160300600b0160300600b0160740e80b0160740e80b01802c0580c01802c0580c03a02c0581d03a02c0581d06e0600c18c06e0600c18b06c0600c03206c0600c0320300dcc50180300dcc48180300d8190180300d8190183100780f18730c0780f1850160400800b0160400800b02002c0581002002c058103080780f1833040780f18103c600bf81e03c5f8be81e02002c0581002002c058100160400800b0160400800b03c5f0bd81e03c5e8bc81e01a0d4bc00d01a0d4bb80d0680701a01b0680701a01b03806c0d81c03806c0d81c01a0d01903401a0d01903406a0340697606a034069750380d00d8340380d00d8340360700e01b0360700e01b0680341a0320680341a0322e80600c1732e40600c1710160400800b0160400800b02002c0581002002c058102e00600c16f2dc0600c16d0305b0b58180305a8b481802002c0581002002c058100160400800b0160400800b0305a0b3818030598b281806603406832066034068322c8034068312c60340683101a0cc1900d01a0cc1900d01a5881880d01a5841880d0600600c1600600600c15f030578ae818030570ad8180300c0ad0180300c0ac8182b00600c1572ac0600c15501802c0595401802c059532a4034069512a00340694f01a538a680d01a530a580d29402c0580c29202c0580c016030a400b016030a380b01a518a280d01a510a180d284034069412800340693f0164f80600b0164f40600b006020040030060200400301000c0180801000c0180801000c0180801000c01808006020040030060200400300400c0180200400c018020020240480100202404801012004008090120040080900400c0180200400c0180200600801003006008010030120040080901200400809002024048010020240480100600801003006008010030020100200100201002001006018028030060180280300a00c0180500a00c018050020100200100201002001008004008040080040080400c00c0180500c00c0180500601402803006014028030080040080400800400804006020040030060200400301000c0180801000c0180801000c0180801000c0180800602004003006020040030020100200100201002001006014028030060140280300a00c0180500a00c018050020100200100201002001008004008040080040080400a00c0180500a00c0180500601402803006014028030080040080400800400804006008010030060080100300400c0180200400c0180200400c0180200400c01802006008010030060080100300400c0180200400c0180200400c0180200400c018020060080100300600801003006008010030060080100300c00c0180600c00c0180600a00c0180500a00c018050060180300300601803003006014028030060140280300000400800000004008000000040080000000400800002000000010020000000100200000001002000000010060080100300600801003006008010030060080100300400c0180200400c0180200400c0180200400c01802006020040030060200400301000c0180801000c0180801000c0180801000c018080060200400300602004003006008010030060080100300400c0180200400c0180200400c0180200400c018020060080100300600801003002010020010020100200100800400804008004008040080040080400800400804002010020010020100200100400c0180200400c018020020240480100202404801012004008090120040080900400c0180200400c01802006008010030060080100301200400809012004008090020240480100202404801006008010030060080100300a00c0180600a00c0180600a00c0180600a00c0180600601403003006014030030060140300300601403003000004008000000040080001000c0180801000c01808006020040030060200400300000400800000004008000020000000100200000001006020040030060200400301000c0180801000c018080020000000100200000001000004008000000040080000000400800000004008000020000000100200000001002000000010020000000100601c0380300601c03803006014028030060140280300e00c0180700e00c0180700a00c0180500a00c018050144f09d80a0144e89c80a0144e09b80a0144d89a80a26802805133264028051312600280512f25c0280512d05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05c0bc1782e05c0bc1782e05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c0000b8170000000b8170000000b8170000000b81700005c0000002e05c0000002e05c0000002e05c0000002e0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b41680005a0000002d05a0000002d05a0000002d05a0000002d0000b4168000000b4168000580b41682c0580b41682c05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c05a0b01602d05a0b01602d05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05a0b01602d05a0b01602d0580b41682c0580b41682c05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e0580b41682c0580b41682c05c0bc1782e05c0bc1782e05e0b81702f05e0b81702f05e0b81702f05e0b81702f05c0bc1782e05c0bc1782e05a0b01602d05a0b01602d05a0b01602d05a0b01602d0580b41682c0580b41682c0580b41682c0580b41682c0400ac158200400ac15820046088110230460881102304408c1182204408c118220400ac158200400ac158200560801002b0560801002b04408c1182204408c1182204608811023046088110230560801002b0560801002b0400a8150200400a815020046088110230460881102304408c1182204408c118220400a8150200400a8150200540801002a0540801002a04408c1182204408c1182204608811023046088110230540801002a0540801002a0400841082004008410820046088110230460881102304408c1182204408c118220400841082004008410820042080100210420801002104408c1182204408c118220460881102304608811023042080100210420801002104408c1182204408c118220400901202004009012020048080100240480801002404408c1182204408c1182204608811023046088110230480801002404808010024040090120200400901202004608811023046088110230400a4148200400a414820258080100282560801002805208010029052080100290404a8140200404a41402004408c1182204408c118220400901202004009012020048080100240480801002404408c1182204408c11822046088110230460881102304808010024048080100240400901202004009012020046088110230460881102304408c1182204408c118220460881102304608811023046088110230460881102304408c1182204408c11822042080100210420801002104208010021042080100210400841082004008410820040084108200400841082000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000841080000008410800000000000000000000000000000000000000000000000000841080000008410800042000000210420000002100000000000000000000000000000000000000000000042000000210420000002104408c1182204408c118220400841082004008410820042080100210420801002104408c1182204408c11822046088110230460881102304208010021042080100210400841082004008410820046088110230460881102304009c1382004009c1382004e0801002704e0801002704e0801002704e0801002704009c1382004009c1382004408c1182204408c11822040098130200400981302004c0801002604c0801002604408c1182204408c11822046088110230460881102304c0801002604c080100260400981302004009813020046088110230460881102304408c1182204408c11822040098130200400981302004c0801002604c0801002604408c1182204408c11822046088110230460881102304c0801002604c0801002604009813020040098130200460881102304608811023040084108200400841082004208010021042080100210420801002104208010021040084108200400841082004a0801002504a0801002504a0801002504a08010025040094128200400941282004009412820040094128200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000420000002104200000021000084108000000841080000000000000000000000000000000000000000000000000084108000000841080004200000021042000000210000000000000000000000000000000000000000000004800000024048000000240000901200000009012000000000000000000000000000000000000000000000000000901200000009012000048000000240480000002400000000000000000000000480801002404808010024048080100240480801002404009012020040090120200400901202004009012020042080100210420801002104408c1182204408c11822046088110230460881102304208010021042080100210400841082004008410820046088110230460881102304408c1182204408c11822040084108200400841082002c4a09381602c4989281602c07c9201602c07c918162440580b1212400580b11f03e0580b11e03e0580b11d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000002380600c11b2340600c1190280600c0150280600c0150304608b8180304588a8180300500a8180300500a8182280780f1132240780f1110160400800b0160400800b02002c0581002002c058102200780f10f21c0780f10d03c4308581e03c4288481e02002c0581002002c058100160400800b0160400800b03c4208381e03c4188281e03a02c0580c03a02c0580c03a02c0580c03a02c0580c0160740600b0160740600b0160740600b0160740600b02002c0581002002c058102080600c0122060600c012030408808180304007f81802002c0581002002c058100160400800b0160400800b0303f8090180303f4090181f80600c0fb1f40600c0f90160400800b0160400800b01a3e07b80d01a3d87a80d0360700e01b0360700e01b03806c0d81c03806c0d81c01a0500a80d01a0500a80d1e8034068f31e4034068f103806c0d81c03806c0d81c0360700e01b0360700e01b0280340681502803406815034034068150340340681501a3c07780d01a3b87680d01a0680a80d01a0680a80d1d8034068eb1d4034068e91d00600c0191ce0600c01903039872818030390718180303880c8180303840c8181c00600c0df1bc0600c0dd01802c0580c01802c0580c1b8034068db1b4034068d901a0486c00d01a0486b80d01802c0580c01802c0580c0160300600b0160300600b01a3586a80d01a3506980d024034068d2024034068d10160300600b0160300600b01802c0580e01802c0580e1a00600c0cf19c0600c0cd030330658180303286481801c02c0580c01c02c0580c0160300700b0160300700b03032063818030318628181880600c0c31840600c0c10160380600b0160380600b01802c058c001802c058bf0160305f00b0160305e80b0160305e00b0160305d80b01802c058ba01802c058b901802c058b801802c058b70162d80600b0162d40600b0160305a00b0160305980b16402c0580c16202c0580c02602c0580c02602c0580c01604c0600b01604c0600b01604c0600b01604c0600b02602c0580c02602c0580c03005c0b81803005c0b81803005c0b81803005c0b81802e0600c01702e0600c01702e0600c01702e0600c01702c2c05781602c2b8568161580580b0ab1540580b0a91500580b0a714c0580b0a502c2905181602c288508161400580b09f13c0580b09d1380580b09b1340580b09902c2604b81602c2584a81602c2504981602c24848816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001802c0580c01802c0580c1200340688f11c0340688d01a0540a00d01a0540a00d02602c0581302602c058130160300600b0160300600b01a2304580d01a2284480d02a0340681402a0340681401604c0980b01604c0980b02002c0581002002c058100240440888802404408887022218428110222104181102002c0581002002c058100160400800b0160400800b02204841011022048408111000440887f0fc0440887d0160400800b0160400800b01a1f03d80f01a1e83c80f01a1e03b80d01a1d83a80d0e8034078730e4034078710e00340686f0dc0340686d01a1b03580d01a1a83480d01c02c0580c01c02c0580c0160300700b0160300700b01a1a03380d01a1983280d0c8034068630c4034068610160380600b0160380600b01802c0580e01802c0580e0c00340685f0bc0340685d0b802c0580c0b602c0580c0160302d00b0160302c80b0161600600b01615c0600b01802c0585601802c05855006008010030060080100300400c0180200400c0180200400c0180200400c018020060080100300600801003002010020010020100200100800400804008004008040080040080400800400804002010020010020100200100400c0180200400c018020020240480100202404801012004008090120040080900400c0180200400c01802006008010030060080100301200400809012004008090020240480100202404801006008010030060080100301000c0180801000c018080060200400300602004003006020040030060200400301000c0180801000c018080141502980a0141482880a0a00280504f09c0280504d0980280504b094028050490141202380a0141182280a006020040030060200400300000400800000004008000020000000100200000001006020040030060200400301000c0180801000c018080020000000100200000001000004008000000040080001000c0180801000c018080060140280300601402803006014028030060140280300a00c0180500a00c0180500a00c0180500a00c018050000040080000000400800002000000010020000000100200000001002000000010000040080000000400800006014028030060140280300c00c0180500c00c0180500a00c0180500a00c018050060180280300601802803006020040030060200400301000c0180801000c0180801000c0180801000c01808006020040030060200400300400c0180200400c018020020240480100202404801012004008090120040080900400c0180200400c018020060080100300600801003012004008090120040080900202404801002024048010060080100300600801003006020040030060200400301000c0180801000c0180801000c0180801000c01808006020040030060200400300400c0180200400c0180200400c0180200400c018020060080100300600801003006008010030060080100300e00c0180700e00c018070020100200100201002001008004008040080040080400a00c0180700a00c0180700601c0380300601c0380300800400804008004008040020100200100201002001006014038030060140380300400c0180200400c0180200400c0180200400c018020060080100300600801003006008010030060080100300c00c0180500c00c0180500a00c0180500a00c0180500601802803006018028030060140280300601402803008004008040080040080400c00c0180600c00c01806006018028030060180280300800400804008004008040020100200100201002001006018030030060180300300c00c0180500c00c0180500201002001002010020010060080100300600801003006008010030060080100300400c0180200400c0180200400c0180200400c018020020000000100200000001002000000010020000000100000400800000004008000000040080000000400800⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid 240 r := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_125 : ∀ i ∈ List.range' 125 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_250 : ∀ i ∈ List.range' 250 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_375 : ∀ i ∈ List.range' 375 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_500 : ∀ i ∈ List.range' 500 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_625 : ∀ i ∈ List.range' 625 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_750 : ∀ i ∈ List.range' 750 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_875 : ∀ i ∈ List.range' 875 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_1000 : ∀ i ∈ List.range' 1000 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_1125 : ∀ i ∈ List.range' 1125 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_1250 : ∀ i ∈ List.range' 1250 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_1375 : ∀ i ∈ List.range' 1375 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_1500 : ∀ i ∈ List.range' 1500 125, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test240_1625 : ∀ i ∈ List.range' 1625 27, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine h bad step240 (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 1652 at hi
  by_cases h0 : i < 125
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h125 : i < 250
  · exact test240_125 i (by simp only [List.mem_range'_1]; omega)
  by_cases h250 : i < 375
  · exact test240_250 i (by simp only [List.mem_range'_1]; omega)
  by_cases h375 : i < 500
  · exact test240_375 i (by simp only [List.mem_range'_1]; omega)
  by_cases h500 : i < 625
  · exact test240_500 i (by simp only [List.mem_range'_1]; omega)
  by_cases h625 : i < 750
  · exact test240_625 i (by simp only [List.mem_range'_1]; omega)
  by_cases h750 : i < 875
  · exact test240_750 i (by simp only [List.mem_range'_1]; omega)
  by_cases h875 : i < 1000
  · exact test240_875 i (by simp only [List.mem_range'_1]; omega)
  by_cases h1000 : i < 1125
  · exact test240_1000 i (by simp only [List.mem_range'_1]; omega)
  by_cases h1125 : i < 1250
  · exact test240_1125 i (by simp only [List.mem_range'_1]; omega)
  by_cases h1250 : i < 1375
  · exact test240_1250 i (by simp only [List.mem_range'_1]; omega)
  by_cases h1375 : i < 1500
  · exact test240_1375 i (by simp only [List.mem_range'_1]; omega)
  by_cases h1500 : i < 1625
  · exact test240_1500 i (by simp only [List.mem_range'_1]; omega)
  exact test240_1625 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨8,10,0x5692e169004b80056988169006205a5695b0010056c5a5690100100404⟩
private def rows720 : List Rule := [
  .pool ⟨13,8,[13,2],[3,5,7],185,0x1a212048200482102040108304200810210480104812116⟩,
  .pool ⟨13,8,[13,2],[3,5,7],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨13,8,[13,2],[3,5,7],95,0x102450d207310b30d453b5e⟩,
  .pool ⟨13,8,[13,2],[3,5,7],703,0x4410302402041a100820000800241288020040840c1100010094010008200218c081104800002000806100a442024400000240008225010610000481480000090280a000800312402180010000014810100184412916⟩,
  .pool ⟨13,8,[13,2],[3,5,7],543,0x5321a0d028800b64008849045049b2d20410184d12182502526112092da0db61941344300068024b2530912d10c32504c36596902024d14d24ca6d900b6ca2d06832116⟩,
  .pool ⟨19,5,[19,5],[2,3],25,0x1394a73⟩,
  .pool ⟨19,18,[19,2,3],[5,7,11,13,17],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨19,14,[19,2],[3,5,7,11,13],15,0x116⟩,
  .pool ⟨17,13,[17,7,13],[2,3,5,11],365,0x29000821008c301e30a8411208159900000201906461100030000200070008108800982808004420a10010b2082⟩,
  .pool ⟨19,18,[19,2,3],[5,7,11,13,17],385,0x1eb22c242294609120621880b146080c7405a0210a160442790881a142101680b8c0418a34046118122418a51090d135e⟩,
  .pool ⟨19,5,[19,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,5,[19,5],[2,3],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨19,5,[19,5],[2,3],259,0x800014419080000001000400040000038040842c020000128305010420a0062⟩,
  .pool ⟨19,5,[19,5],[2,3],175,0x441090c0280233100510c24308a008cc401403090822⟩,
  .pool ⟨19,18,[19,2,3],[5,7,11,13,17],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,2,[19,2],[],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,25,[41,5,13,23],[2,3,7,11,17,19],525,0x1b29225820308b0430106812136d14912c100841a21008240929b6884892080c22d10c041244845b6524090402116084020d224a2db2120582030834430106912536⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨19,2,[19,2],[],143,0x42148073495103e1b21836746511bad53de⟩,
  .pool ⟨19,2,[19,2],[],31,0x121d47b6⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨31,20,[31,2,5,7],[3,11,13,17,19],1241,0x1b7cae9366e31868e5a3b0384e04f217f59f312e6c547a4097e41192f83119beb98a1fe82d0c63b4e2c0d9d1fa70810659aaa180080b4833bb11694c1e0a6aa32a5e13754aefe345228d1295a47b7896a522c5128b1fdd4abb21e953155941e0ca5a2377304b4040061556698204397e2e6c0d1cb718c2d05fe14675f662307d26209fa40978a8d9d233e6bfa13c81c87037169c58631d9b25d4fb6⟩,
  .pool ⟨41,25,[41,5,13,23],[2,3,7,11,17,19],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .prime 19,
  .prime 37,
  .pool ⟨19,9,[19,3],[2,5,7],85,0x20200ca0300000829028a⟩,
  .pool ⟨17,13,[17,7,13],[2,3,5,11],1147,0x349a3c32b10eb4b064dcbf02718e70b7d6df510a3410af97c4ec2f0194be3504499758548829e933f08be8ab361110800a9a060ea601cfa5399a3157b0982fdf8d2c39d49928989a6e6a366d4634b0e040ae6f01571a6634a087f9a8f17a6affee377932ac80ef033286aeed5651665de5382d63d0bc8dc100af7d3a765049402f10e719f02c0d9b2d28f5233c3a6d2⟩,
  .pool ⟨19,8,[19,2],[3,5,7],17,0x1a316⟩,
  .pool ⟨19,9,[19,3],[2,5,7],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨19,9,[19,3],[2,5,7],91,0x50f01092600000649080f0a⟩,
  .pool ⟨19,8,[19,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨19,9,[19,3],[2,5,7],61,0x1713e6940a59f23a⟩,
  .pool ⟨11,10,[11,2,5],[3,7],1159,0x6cb08e5484b9333084218a920a4e4e448130480390888249008825fd21b8206180121f1131d0100fc20081c081086082001081801c23aae209028fc0090028128555020842aa47425a42e255421040aaa14814009003f140904755c438018108004106108103810043f0080b8c88f8480186041d84bfa4110092411109c0120c8122727250495184210ccc9d212a710d36⟩,
  .pool ⟨11,10,[11,2,5],[3,7],969,0x1b2c22d061269944a00860b61a09849324000205a0122db01b24064a0192192930904410416000ca20101925228a28144a2c20c004a48261005a49304b4832496802190494800c10d148a0514512926020114c001a0820882432526126014980936036d120168100009324864161b41840148a6592182d10d36⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],95,0x102450d207310b30d453b5e⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],35,0x401090802⟩,
  .pool ⟨19,3,[19,3],[2],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨19,4,[19,2],[3],17,0x1a316⟩,
  .pool ⟨19,3,[19,3],[2],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨17,10,[17,2,5],[3,7],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨19,5,[19,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨11,10,[11,2,5],[3,7],1241,0x1b7cae9366e31868e5a3b0384e04f217f59f312e6c547a4097e41192f83119beb98a1fe82d0c63b4e2c0d9d1fa70810659aaa180080b4833bb11694c1e0a6aa32a5e13754aefe345228d1295a47b7896a522c5128b1fdd4abb21e953155941e0ca5a2377304b4040061556698204397e2e6c0d1cb718c2d05fe14675f662307d26209fa40978a8d9d233e6bfa13c81c87037169c58631d9b25d4fb6⟩,
  .pool ⟨19,5,[19,5],[2,3],219,0x21a40309b2d02820412400ca2122932886d905969a2d020261b4832⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],1105,0x1a34288062024000a1601020840510162018a4000801200240900088081008b024000a4220814410020001083000002080025801004202000210080042062c40218010100631802020061008d181080040210001010802006900041000003042000100208a04110940009034402040440024090012004000946011a022808410201a14000901180450b16⟩,
  .pool ⟨19,8,[19,2],[3,5,7],37,0x1ffffffffe⟩,
  .pool ⟨19,8,[19,2],[3,5,7],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨19,8,[19,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,8,[19,2],[3,5,7],241,0x1a246480a08200027002003000005430a8000030010039000104140498916⟩,
  .pool ⟨17,12,[17,2,3],[5,7,11],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨17,12,[17,2,3],[5,7,11],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,8,[19,2],[3,5,7],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],703,0x4410302402041a100820000800241288020040840c1100010094010008200218c081104800002000806100a442024400000240008225010610000481480000090280a000800312402180010000014810100184412916⟩,
  .pool ⟨37,24,[37,2,3,23],[5,7,11,13,17,19],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],1241,0x1b7cae9366e31868e5a3b0384e04f217f59f312e6c547a4097e41192f83119beb98a1fe82d0c63b4e2c0d9d1fa70810659aaa180080b4833bb11694c1e0a6aa32a5e13754aefe345228d1295a47b7896a522c5128b1fdd4abb21e953155941e0ca5a2377304b4040061556698204397e2e6c0d1cb718c2d05fe14675f662307d26209fa40978a8d9d233e6bfa13c81c87037169c58631d9b25d4fb6⟩,
  .pool ⟨19,2,[19,2],[],17,0x1a316⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],17,0x1a316⟩,
  .pool ⟨37,24,[37,2,3,23],[5,7,11,13,17,19],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨19,7,[19],[2,3,5,7],5,0x12⟩,
  .pool ⟨19,13,[19,7,13],[2,3,5,11],1037,0x29c4012000802006083840220180b02088863006005ed0a9e1054a0809020011134414b0d80009a5321d130102208008003304200480431a00150ec038a0502030002470a0600114120082001180008460106812200008812c00191c880010800c91480802e0e812c000002032200440aa28a4140980c46808410429130a1892082⟩,
  .pool ⟨19,17,[19],[2,3,5,7,11,13,17],3,0x2⟩,
  .pool ⟨19,13,[19,7,13],[2,3,5,11],365,0x29000821008c301e30a8411208159900000201906461100030000200070008108800982808004420a10010b2082⟩,
  .pool ⟨19,13,[19,7,13],[2,3,5,11],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],1295,0x4402421401c201803210047b40c1102d1004b09021411246a8a2014e50302450da252101124cf5192400d422046070d207898d48d08105230b826000a150c207300e78909724c431102531c70a1aa33028218604110b6250d09106528006b10b30c452bd48380a330c4e304c44200720d0b11ca950d6c10500489463314b009452b1e1014a92a80c315873a4c21a5641b16461009734a13a56a41d85389cd1b5e⟩,
  .pool ⟨19,2,[19,2],[],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],37,0x1ffffffffe⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],777,0x1a2124596090ca49a4020d029360921a60800060029904264868a44208205a60a01300141144a01001221a0c049121b48304b6122480c161120020148a20a00320141968104108945849908265001800041961241b2502c10096494c241a6892116⟩,
  .pool ⟨19,2,[19,2],[],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨19,10,[19,2,5],[3,7],31,0x121d47b6⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],19,0x7fffe⟩]
private def step720 : Stage := ⟨240,3,keys240,keys720,rows720,7,0x993264b972e6cd9b2e5cb9b366cc99326cd9b3264c972e5cd9b3664c992e5cb993264b972e6cd9b2e5cb9b366cc99325cb97366cd993264d9b3664c992e5cb993264b972e6cd9b3264c972e5cd9b365cb97366cd993264d9b3664c992e5cb3420408106841a1020d08342040810684083420d083420408106841a10684083420408106841a1020d08342040810684083420d08342041a10204083420d08106841a10204083420d08342040810684083420d08342041a10204083420d08341c3860c6859a1638d0e342c5870e6858b341cd07341831a162c3873418d060e6839a1c3858b341831a166859a0e1c58b341cd07341831a0e1c306342cd0b1c6871a162c387341831a166859a0e1cd0b161c39a0c68307341cd0e1c2c59a1c6871a162c387342c59a0e6839a1c38d070e1831a1668587341cd0e1c2c59a1c38d0b342cd070e6858b0e1cd063418d070e1831a166858e3438d0b161c39a162cd07341cd0e1c6858b0e1cd06341839a0e6870e162cd0e1c6859a1668387343870b166839a0e2cd0b341c3860c683873418d06342c5870e6871a1c6858b341830b166839a0e2cd0b341c3860c683873418d06342c59a1c3858b341cd07166859a0e1c306342cd0b341c3860c683873438d0e342c59a0c1858b341cd07166859a0e1c70e341c39a0c6831a162cd0e1c2c59a0e6839a1c3858b341cd07166859a0e1c306341c39a1c6871a162cd0e1c2c59a0e6838b342cd070e3871a0e1cd063418d0b161c39a1c6871a162cd0e1c2c59a0e6838b342cd070e1831a0a14d07341cd0e1c683871c38d05341431a0c682850e1cd1a66399b234c8d33646999a66c998e34cd91a0c6999a66c831a0c682850e1cd050a6839a0e6870e341c38e1c6829a0acd91a0c6999a66c8d331ccd91a64699b234ccd3364cc71a0e6839a0c18285343871a0a6829a0e1cd050a1c39a0c68333646831a66699b234cc733646991a66c8d3334cd9330c699b234c8d3334cc31a66c998e34c8d330c6999a66c99b234682850e1cd06341839a0e6870e0a14d060c6829a0a6838734142870e6831a0c1cd0734183050a6870e3414d05341c3b234ccd3364cc31a66c8d0634ccd33646998e66c8d3234cc31a66699b266c8d33646991a666998634cd9331c6991a661831a0a6829a0e1cd050a1c39a0c68307341cd0e1c1429a0e1cd0e3438d050a683060a14d07341c29a0a683871c38d1a66c99b23438d33646999a66199b234cc71a646999a66c829a0a683871c38d070e6871a1c6828534183050a6839a0ecc71a646999a66c8d3364cd91a1c699b234ccd330ccd91a6638d3234ccd3364699b266c8d0634cd91a666998666c8d1a1c38285341cd070a6829a0e1c306341c39a0c6831a0a14d070e3871a0a682863418d050a1c39a0a14d07341cd060cc8d3334cc733646998634c8d3334cd91a66c99b23418d33646999a66199b234cc71a646999a66c8d3364cd91a0c699870e6831a0c6828534387050a6839a0e14d05341c3860c68285341cd07341831a0e1c70e3414d050c6831a0a1438734699b266c8d0634cd91a666998e66c8d330c6991a66699b254a8d07341cd060c683871c38d2a34a871a1c6952a0e1cd0e3438d2a541c39a54a8d07341cd060c683871c38d2a34a831a0c6952a0e1cd2a546839a0e68306341c38e1c6951a54683870c18d2a34a831a0c6952a0e1cd2a546839a0e6870e341c38e1c6951a5418d0634a95070e6952a341cd07341832a546839a0e6870e341c3860c6951a5418d0634a95070e6839a0e6870e54a8d0e1c6951a546838734a95070e6831a0c6952a0e1cd06341839a0e6870e54a8d0e1c6951a546838734a95070e6831a0c1cd07343872a546830634a8d2a341c39a0c1952a341cd07546951a0e1c70e341c39a0c6831a54a830634a8d2a341c39a54a83873418d060e6839a1c3952a341c39a0c6831a54a8d060ca951a0e683aa34a8d070e3871a0e1cd23348cd2346691a3468cd2b34ad19a4668387468cd23348cd070e8d19a56acd23348cd2346691a3468cd07341d19a4668387468cd070e6919a46691a3348d1a3466959a56691a3468cd07341d19a4668387468cd2b566919a46691a3348d1a3466959a568cd23341c3a34668387348cd23348d1ab566919a46691a3348d1a3466839a0e8cd23341c3a34668387348cd23348d19a468d1a334acd2b466919a0e1d1a3348cd23341c3a346695ab348cd23348d19a468d1a3341cd07466919a468d5ab348d19a0e6839a468cd070e8d19a46691ab34acd23468d19a468cd23348cd070e691a30e1cd23348cd070e8d19a46691a3348cd2346ad59a468cd07341cd2346691a30e1cd23348d59a56691a3468cd23466919a4668387468cd07341cd234668387468cd23348d19a46691a356acd23466919a4668387348d1870e6919a46acd2b348d1a3466919a46691a356acd23466839a0e691a3341c3a3466919a46acd2b348d1a346691a3348cd23341c39a468c387348cd2334cd933646831a66c8d3334cc333646998e34c8d3334cd90c3430d070e1831a0e1cd063418d2c586870e162cd07341c31a0c6860c0e1cd2c586839a0e68306341c38e1c6859a16cc31a646999a66c8d3364cd91a0c699b234ccd331ccd91a6638d3234ccd3364699b266c8d0634cd91a666998666c8d1a1c3858b341cd07186861a0e1c306341c39a0c6831a58b0d070e3871a16685863418d0c181c39a58b0d07341cd060cc8d3334cc733646998634c8d3334cd91a66c99b23418d33341c3860c6861a1838d0e34b16070e6858b341cd07343873234ccd330ccd91a6638d3234ccd3364699b266c8d0e34cd91a66699b26618d33646871a66699b234cc733646991a663061a0e6839a0c18d070e3871a586960e3438d0b161c39a162cd07341cd0e1c683870c18d0c343071a1c6962c0e1cd1a66c99b23438d33646999a66199b234cc71a646999a66c8d331ccd91a64699b234ccd3364cc31a66c8d0e34ccd336438d0e342c5870e6860c341cd07341831a0e1c70e34b0d2c0e6839a0c1962c343871a166859a0e1cd0c181c39a0c68333646831a66699b234cc733646991a66c8d3334cd9330c699b234c8d3334cc31a66c998e34c8d330c6999a66c99b2346962c0e1cd06341839a0e6870e162cd060c6861a186838734306070e6831a0c1cd07341832c586870e342cd0b341c3b234ccd3364cc31a66c8d0634ccd33646998e66c8d3234cc31a66699b266c8d33646991a666998634cd9331c6991a661831a186861a0e1cd2c581c39a0c68307341cd0e1c2c59a1c6999a66c99b234cd91a646999a6638d3364cc31a646998e1c6961a5868387342c5870e6871a1c1cd07341830c18683873438d0e34b161a1c3858b341cd07186861a0e1c30634699b26638d3234cc71a66699b266c8d33646991a666998634cd9330c6991a6638d3334cd93364699b234c8d3334cc707341cd060c3061a1c38d2c34b0d070e6858b0e1cd0e343861a18683870c18d070e6871a1c6962c343870b166839a0ecd91a646999a6618d3364cc71a646998e34ccd3364cd91a34183050a6839a0e14d05341c38912683873424d09341429a0e1c3063414d05126849a0a14387341429a0e6839a12243873424d09341429a0c18285341cd070a6829a0e1c489341429a0e6839a1224d070e1831a0a682893424d050a1c39a0a14d07341cd060c683870c18d05341449a12682850e1cd063418d050a1c39a0a14d07341cd060c683871224d05341449a12682850e1cd050a6839a0e68306341c3860c6829a0a683871224d05341431a0c682850e1cd050a6839a0e6830634142870e6849a121cd0734244850a683063414d05341c389126829a0a6838734142870e6849a121cd0734183050a683063414d05341c39a0a143873424d090e6839a1224285341cd0734183050a684893414d05341c39a0a143873424d090e6839a0c18285342449a0a6829a0e1cd050a1c39a0c683053414d070e1831a0e1cd093424d050a683060a14d07341cd050a1c39a0c68307341cd060c1429a1224d053414d070e683060a14d07341c29a0a683870c18d070e6849a12682851224d053414d070e682850e1cd06341839a0e683060a14d07341cd060c1429a1224d053414d070e682850e1cd06341829a0a683871224d070e6831a0c6828534244850a6839a0e684890a14d07341c29a0a683871224d070e6831a0c682850a14d07341cd060c683870c18d05341449a12682850e1cd093424d050a1c39a0a14d07341cd060c683870c18d053414d070e1831a0a682893424d050a1c39a0a14d07341cd09121429a0e6839a1224d070e1831a0a682893424d050a1c39a423c79932652244864c99489120f1e85224483d08f3264ca448907a11e64c99423c79932652244864c99489120f1e85224483d08f3264ca11e3cc9932912243264ca4489078f4264c99489120f1e85224483d08f3264ca11e3cc9932912243264ca4489108f1e912241e3d09932647a11e64c99489120f1e84c9932912243264ca448907a11e91224423c79932647a11e64c9948912193265224488478f489120f1e84c993291224423c799326478f4264c9948912193265224483d08f8f1a3962c5a2c58a58b1620408469528810212a5462c58b458b163c78c58b16951a5162c588102058b1620408469528810212a5462c58b478d1cb162d162c52c58b10204234a9458b162040846952a2c58b1e3c62c58b4a8d28b162c408102c58b10204234a94408108f1e3162c5a5469458b168b162ca8d28b162d162c52c58b10204234a94408108f1e3162c58b162c40810951a510204234a9458b168f1e3162c5a2c58b1a54a2c58b102040b162c40810952a3458b163c68e58b168f1e3162c5a2c58a58b16204084a8d28810211a54a2c58b458b163c68e58b168d2a5162c588102058b16204084a9518810211e3472c58b469528b162d162c52c58b10204254a8c58b16204084a9518810211e3472c58b469528b162d162c58b162c38710b162d0e2432c58b102040b162c40810890e1962c5a2c58b0e2432040844870cb162d0e1c42c58b102040b162c40810890e1c58b161c38858b1687121962c58810210e1c42c58b102040b162d162c5871219020422438658b1687121962c588102058b162040844870e2c58b0e1c42c58b1020422438658b16870e2162c588102058b168b162c3890e2c58b0e1c42c58b43890cb162c408102c58b1020422438658b168b162c3890c81021121c32c58b438710b162c40810890e1962c588102058b16204084387122c58b0e2432c58b1020421c48658b16890e1962c588102058b168b162c387122c58b0e2432c58b44870cb162c408102c58b1020421c38858b168b162c38710810210e2432c58b44870cb162c408102c58b1020421c389162c587121962c5a2438658b162040844870cb162c408102c58b458b161c3884081087121962c5a2438658b1620408162c58810210e1c48b162c3890cb162c4081087121962c5a2438658b1620408162c5a2c58b0e1c444891478d1cb162d1a54a2c58b2244895ab568912256ad5962c59122451a3c7448914a9518b162cad5ab56ad5a244895ab568912256ad5a2448a3c68e58b168d2a5162c5912244ad5ab56ad5a24488b162c891228d1e3a2448a54a8c58b1656ad5ab56ad1224458b1644891468f1d122452a5462c58b22448a54a8c58b1656ad5ab56ad1224458b1644891468f1e54a8c58b16448912b56ad12244ad5ab44891468f1cb162c891228d2a5162c595ab56ad5ab44891162c59122451e34744891468f1cb162d2a5462c58b2244895ab568912256ad5962c59122451e34744891469528b162cad5ab56ad5a24488b162c891228f1a3a2448a34a9458b1656ad5ab56ad12244ad5ab56ad5a24488b162c891228f1a3a2448a34a9458b1620408488d20b162d1a3c72c58b499324b162c4081091223162c58810212244693264c78d1cb162d1a4482c58b102040b162c40810912231020424469058b168d1e3962c5a4c9931a4482c58b102040b162c40810912234993263c68e58b168d224162c5a4c99258b1620408489118810211e3472c58b4993264488c58b16911a4162c588102058b1620408468f1c810211e3472c58b469120b162d264c92c58b1020424488c58b1620408468f1e4c993224462c58b488d20b162c4081010204081020408102040810204081020e1c3870e1c3870e1c3870e1c3870e1c102040810204081020408102040810223c68e58b1693264962c58810211a44820408489118b162d264c98d1e3962c5a4488c58b1620408162c58810212234820408489118b162d1e3472c58b499324b162c408108d224162c58810212234893264c68f1cb162d224462c58b102040b162c40810911a41020423478e58b1691223162c5a4c993224462c58b102040b162c408108f1a3c993263489058b1691223162c5a4c99258b1620408488d20810211a3c72c58b4993263489058b1691223162c588102058b1620408478d1c4081020408102041c3870e1c3870e1c102040810204081020408102040810204081020408102041c3870e1c3870e1c2c58b1020421c389264c987121962c5a2438658b162040843890cb162c408102c58b4993262438640810870e2162c5a2438658b1620408162c58810210e1c493264c3890cb162c40810870e2162c5a1c48658b1620408162c5a4c993121c393264c3890cb162d121c32c58b102040b162c40810870e2162c5a4c993121c320408438710b162d0e2432c58b102040b162c40810870e24993261c48658b16890e1962c58810210e2432c58b102040b162d264c9890e19020421c38858b1693264c4870cb162d0e1c42c58b102040b162c4081087121962c5a4c9930e2432040844870cb162d0e1c42c58b102040b162c4081087121c993262438658b16870e2162c58810210e1c42c58b102040b162d264c9871219020422438658b16870e2162c588102058b162040843890e4c993121c32c58b1020422438658b16870e2162c588102058b1693264c3890e4c993121c32c58b438710b162c408102c58b1020421c48658b1693264c3890c81021121c32c58b438710b162c408101020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204083870e1c3870e1c3820408102040810204081020408102041c3870e1c3870e1c102040810204081020408102040810204081020408102041c3870e1c3870e1c10204081020408102040810204081020e1c3870e1c3870e081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020e1c3870e1c3870e0810204081020408102040810204081070e1c3870e1c3870e1c3870e1c3870e0810204081020408102040810204081070e1c3870e1c38704081020408102040810204081020408870e2162c588102058b162040843890e2c58b121c32c58b1020421c48658b16890e1962c588102058b168b162c387122c58b121c32c58b438710b162c408102c58b1020421c48658b168b162c38710810210e2432c58b44870cb162c408102c58b1020421c389162c587121962c5a2438658b162040844870cb162c408102c58b1020421c389162c587121962c58b162c40810890e1c58b161c38858b1687121962c58810210e2432c58b102040b162d162c5890e19020421c38858b1687121962c588102058b162040844870e2c58b0e1c42c58b1020421c38858b1687121962c588102058b168b162c4870e2c58b0e1c42c58b43890cb162c408102c58b1020422438658b162040844870e2c58b0e1c42c58b43890cb162c4081010204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040820408488d20b162d1a3c72c58b458b14b162c4081091223162c58810211a4488b162c78f18b162d223482c58b102040b162c40810912231020424469058b168d1e3962c5a2c58b223482c58b102040b162c408108d224458b163c78c58b16911a4162c5a2c58a58b1620408469120810211e3c62c58b458b164488c58b16911a4162c588102058b1620408468f1c810211e3c62c58b488d20b162d162c52c58b1020423489058b1620408468f1e2c58b224462c58b488d20b162c408108f1e3162c5a2c58a58b1620408488d20810211a4482c58b458b163478e58b1691223162c588102058b1620408488d20810211a4482c58b478f18b162d162c52c58b1020424469058b1620408488d222c58b1a3c72c58b489118b162c408102c58b10204244690408108d1e3962c5a4488c58b168b162c69120b162c408102c58b1020423c78d162c5911a4162c5a4488c58b168b162962c58810212234820408468f1cb162d162c5911a4162c5a3489058b1620408162c58810211e3c62c58b1020421c389162c587121962c5a2438658b162040843890cb162c408102c58b458b162438640810870e2162c5a2438658b1620408162c58810210e1c48b162c3890cb162c40810870e2162c5a1c48658b1620408162c5a2c58b121c38b162c38710b162d0e2432c58b102040b162c40810890e1962c5881021121c38b162c38710b162d0e2432c58b1020422c58b121c32c58b438710b162c408102c58b1020421c48658b168b162c3890c81021121c32c58b438710b162c408102c58b1020421c487162c5890e1962c5a1c38858b1620408438710b162c408102c58b458b161c48640810890e1962c5a1c38858b1620408162c58810210e2438b162c4870cb162d162c5890e1962c5a1c38858b1620408162c58810210e2430c6879a4891224349121a486921a1e18d24483c49a486921a48907863490d240c6879a4891224349121a486921a1e24d24483c49a4869206343cd24489121a4890d243490d0f0c9121a486921a1e24d24483c31a4869206343cd24489121a4890d243490d0f12692241e18d24349031a1e692244890d09343cd24489121a4890d243490d0f0c692241e18d24349031a1e692244890d24486921a4868789349120f0c6921a48692241e18d24349049a1e692244890d24486921a48687863491224486831a1e90d24343c4a448687863490d24349121a1e192243490d24486921a4890789349121a0c6879a48907863490d24349121a48912243418d0f486921a1e25224349121a0c6879a4890d0f0c9121a48692243490d24483c49a486921a1e19224343c31a486921a4890d24489121a12687a43490d24483c31a4890d06343cd2448687894890d243490d24489121a12687a43490d0f0c9121a1e18d243490d2448687894890d24349121a48692241e18d24486831a1e69224343c324486921a4890d24349120f12692243418d0f3491224486831a1e69224343c4a4486921a4890d24349120f0c692243418d0f349121a1e192243490d24486921a48907893490d24349120f0c692243418d0f349121a1e252243490d24486921a4890789349121a0c6879a4890d0f0c9121a486921a1e252243490d24486921a4890786349121a0c6879a4890d0f0c9121a48692243490d24483c49a4890d06343cd24489121a0c6879a4890d0f129121a48692243490d24483c31a4890d243490d0f12692241e18d24349031a1e692244890d0f126921a48692243491224486831a1e90d24343c324486831a1e692244890d24486921a4868789349120f0c6921a4890d24343c32448687893490d24349121a48912243418d0f349120f0c6921a4818d0f349122448692243490d24343c49a48912243418d0f486921a1e19224343c49a486921a48912243490d24343c49a48907863490d240c6879a4891224343c49a486921a4890d24489121a0c687a43490d0f0c9121a428509932650204064c994081021428502040850a13264ca040810a14264c99428509932650204064c994081021428502040850a13264ca14284c9932810203264ca040810a14264c994081021428502040850a13264ca14284c9932810203264ca040810a14281020428509932650a14264c9940810214284c9932810203264ca040810a14281020428509932650a14264c994081019326502040850a140810214284c993281020428509932650a14264c994081019326502040850a13264ca040810a14281020428509932650a14264c9940810214284c9932810203264ca040810a14281020428509932650a14264c994081019326502040850a140810214284c993281020428509932650a14264c994081019326502040850a140810214284c9932850a13264ca04080c9932810204285099326502040850a140810214284c9932850a13264ca04080c99328102042850a040810a14264c994285099326502040850a13264ca04080c99328102042850a040810a14264c99408101e3c78c993278f1e3264ca04080c9932810203c78f1932650204078f1e408101e3c78c993278f1e3264ca04080c9932810203c78f204080f1e3c64c993c78f1932650204078f1e3264ca04080c9932810203c78f204080f1e3c64c993e7cf9932650204064c99408101f3e7d020407cf9f3264ca04080f9f3e64c993e7cf9932650204064c99408101f3e7d020407cf9f3264c9f3e7cc9932810203264ca04080f9f3e64c99408101f3e7d020407cf9f3264c9f3e7cc9932810203c78f1932650204064c99408101e3c790204078f1e3264ca04080f1e3c64c993c78f1932650204064c99408101e3c790204078f1e3264c9e3c78c9932810203264ca04080f1e3c64c99408101e3c790204078f1e3264c9e3c78c9932810203264ca04080f9f3e810203e7cf993264f9f3e64c99408101f3e7cc9932810203264ca04080f9f3e810203e7cf993264f9f3e64c9940810193265020407cf9f408101f3e7cc9932810203e7cf993264f9f3e64c9940810193265020407cf9f3264ca040810a14281020428509932650a14264c9940810214284c9932810203264ca040810a142810204285099326502040850a13264ca14284c9932810203264ca040810a14264c994081021428502040850a13264ca14284c9932810203264ca040810a14281020428509932650a14264c9940810214284c9932810203264ca040810a142810204285099326502040850a13264ca14284c9932810203264ca040810a14264c994081021428502040850a13264ca14284c993281020428509932650204064c994081021428502040850a13264ca040810a14264c99428509932650204064c994081021428502040850a13264ca14284c9932810203264ca040810a14264c994081021428502040850a13264ca14284c9932810203264c8810204081020408102041932644081064c9910204081020c9932204083264c88102040810204081020419326440810204083264c881020c9932204083264c8810204081064c991020408102040810204083264c881020c993220408408101e3c78c993278f1e3264ca04080c9932810203c78f1932650204078f1e408101e3c78c993278f1e3264ca04080f9f3e64c9940810193265020407cf9f408101f3e7cc9932810203e7cf993264f9f3e64c9940810193265020407cf9f408101f3e7cc99327cf9f3264ca04080c9932810203e7cf993265020407cf9f408101f3e7cc99327cf9f3264ca04080f1e3c64c99408101932650204078f1e408101e3c78c9932810203c78f193264f1e3c64c99408101932650204078f1e3264ca04080f9f3e810203e7cf993264f9f3e64c99408101f3e7cc9932810203264ca04080f9f3e810203e7cf993264f9f3e64c9940810193265020407cf9f408101f3e7cc9932810203e7cf993264f9f3e64c9940810193265020407cf9f040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102850a13e7cfa04080f9f3e8102041830604080fdfbf7cf9f408101fbf7ef9f3e850a13e7cfa04080f9f3e81020418305f3e7d0204083060c08101fbf7ef9f3e850a13e7cfa040810a1427cf9f408101f3e7d0204083060c08101fbf7ef9f3e3264ca4489108f42912241e8509932650a11e64c994891221423cc9932912243264ca4489108f42912241e8509932650a11e64c994891219326522448847a1489120f4284c9932912241e8509932650a11e64c994891219326522448847a1489120f4284c99328508f3264ca44890c993291224423d0993265224488508f48912211e84c99323d0a13264ca44890c993291224423d0a448907a14264c9942847993265224483d0a13264ca44890c99329122442847a4489108f4264c9948912211e84c99323d0a13264ca44890c99329122442847993265224483d0a14891221423cc9932847a13264ca44890c99329122442847a4489108f4264c991e85099326522448847a13264ca44890c9932912241e850a448910a11e64c99423d09932652244864c99489120f4285224488508f3264ca448910a11e64c99423d09932652244864c99489120f4285224488508f3264ca11e84c9932912243264ca448907a14264c99489120f4285224488508f3264ca11e84c9932912243264ca448907a142912244284799326508f4264c994891221423cc9932912243264ca4489108f42912241e85099326508f4264c9948912193265224483d0a14891221423cc9932912241e8509932650a11e64c994891219326522448847a14891221423cc9932847a13264ca44890c9932912241e850993265224483d0a14891221423cc9932847a13264ca4489122448847a13264c8f4284c9932912243264ca448910a11e64c994891221423d22448847a13264c8f4284c9932912243264ca448910a11e91224423d09932647a14264c99489120f4284c9932912243264ca448910a11e91224423d09932647a14264c9948912193265224488508f48912211e84c993291224423d09932647a14264c9948912193265224488508f70e8d3534d4d152a689932a54d3934e0a9a2a69c3d264cd152a69d1a7069ab534e1c932668a9a2a4cd133454ab87a68a9a2a69c3d264cd387469a9a6a68a95344c9952a69c9a704cd133454ab87a68a9534e8d3834d5a9a70e49933454d15266899a2a55c393454a9a7469c1a6ad4d38724c99a2a68a9a70e49933454d156a69a9a2a55c3a3454a9a7269c1a264cd38724c99a2a68a93344cd152ae1c9a2a54d3a34e0d356a54a9a7269c1a264cd38724c99a2a68ab534d4d152ae1d1a264cd153454d387268a9570f4d13344dd1a7069ab52a54d3934e0d132654a9a264cd153454d387a68a9570e8d3534d5d1a7069ab52a54d132668a9a2a69c393454ab87a6899a2668a9570e8d3534d5c9a70689932a54d132668a9a2a69c3d3454ab87469a9a6ae4d38344c9952a689933454d1534e1c9a6ad4a9534e8d382a68a9a70e499334e1c9a266899a2a549933454d1534e1c9a2a55c3a34d4d357269c1a264ca9534e1c9a266899a2a54d356a54a9a7469c153454d38724c99a106841a102040834d8e1a3869e1a7670d08102041a10684083420d08102041a7670d1c34d8d3c38684081020d083420d08102041a10684083420d08102041a6c70d1c34f0d3b38684081020d08342041a10684081020d3b3868e1a6c69e1c6c70d1c34f0d3b38684081020d08342041a10684081020d083420d08102041a6c70d1c34f0d3b38684081020d083420e1a6c69e1c7670d08106841a10684083420408106841a1069d9c6c70d1c34f041a10684081020d08106841a10684083420408106841a1070d3634f0e3b38684083420d083420408106841a106840834ece363868e1a7820d08342040810684083420d08342041a10204083420d083869b1a7871d9c3470d3634f0e3b38684083420d08342041a10204083420d083454ab87469a9a6ae4d38344c9952a689933454d1534e1c932668a9a2a69c393454ab87469a9a6ae4d38344c9952a69c39344cd133454a9a264ca9534e4d382a68a9a70e9ab53454d1534e1d356a69c39344cd133454a9a264ca9534e4d3834e1bb56a68a9a2a4cd133454ab86e68a9534dcd38344c9952a69b9a7069ab534e1b932668a9a2a4cd133454ab86e68a9534dcd38344c99a70ddab53454d15266899a2a55c37344cd133454ab86e68a9534dcd3834d5a9a70dc9933454d15266899a2a55c373454a9a6e69c1a6ad4d386e4c99a2a68a9a70dc9933454d156a69a9a2a55c373454a9a6e69c1a264cd386e4c99a2a68a93344cd152ae1b9a2a54d3734e0d356a54a9a6e69c1a264cd386e4c99a2a68ab534d4d152ae1b9a264cd153454d386e68a9570dcd13344db9a7069ab52a54d386e6899a2668a95344c9952a69b9a7054d1534e1bb56a69b9a7069ab52a54d132668a9a2a69c373454ab86e6899a2654d1534e1bb56a69c37344cd133454a9a264ca9534dcd383454ab86e69a9a6adcd38344c9952a689933454d1534e1b9a6ad4a9534dcd382a68a9a70dc99334e1b9a266899a2a549933454d1534e1b9a2a55c3734d4d356e69c1a264ca9534e1b9a266899a2a54d356a54a9a6e69c153454d386e4c99a2a68a9a6cd899334d9b1a6a69a9a2a54d132654a9a6c69b1a264ca9534d8d362a68a9a6cd9ab534d9b1a266899a2a54d132654a9a6c69b153454d366c4c99a6cd8d3534d4d152ad9b1a266899a2a54d132654a9a6c69b153454d366cd5a9a6cd8d13344cd152a689932a54d3634d8a9a2a69b366ad4d153454d366cd5a9a6cd8d13344cd152a689932a54d3634d8d366cd5a9a2a68a93344cd152ad9b1a2a54d3634d8d132668a956cd8d3534d5b1a6c689932a54d132668a9a2a69b362a54d3634d8d132669b366ad4d15345499a2668a956cd8d132668a9a2a69b363454ab66c69a9a6ad8d36344c9952a6899a2668a956cd8d152a69b1a6c69ab534d9b132668a9a2a69b36264cd15345499a2668a956cd8d152a69b1a6c69ab55eb97a14284c9932850a13264cae5ebcc9932c58ae4285099326572f5e850a15ebd7214284c9932850a13264cb15cc4c9932c58ae42850af5cbd0a14264c994285099326572f5e850a13264cb15cc4c9932b97af42850af5eb90a14264c99428509932657ae5e64c995cc58a142857af5c850a13264caf5eb90a14264c99428509932658ae6264c995cbd7a142857af5c850a13264ca14284c9932bd72f3264cae62c50a14264c995cbd7a142857af5c850a13264ca14284c9932c5731428509932657af5c64c9962b98a1428572f5e850a13264cae5ebd0a14264c99428509932658b15c64c995eb97a1428572f5e850a13264ca14284c9932bd7ae3264cb15cc50a14264c995eb97a1428572f5e850a13264ca14284c9932c58ae3264cb15cc50a142b97af428509932650a14264c995ebd7214284c9932b98b13264caf5eb90a142bd72f428509932650a14264c995ebd71932658ae62850a15cbd7a14284c9932bd72f428509932650a14264c995cc589932657af5c850a15ebd7214284c9932850a13264caf5cbcc9932b98b1428509932659b264850b364c99a16684c9932cd0a13264cb266c8c9932b98b142850af5eb90a14264c99428509932657ae5ecd0a13264cb266c8c9932cd93242859b264cd0b34264c99428509932657af5c64c9962b98a1428572f5e850a13264cb364c90a16664c9942cd09932659326664c9964cd933428572f5e850a13264ca14284c9932bd7ae3264cb15cc50a14264c9964cd93342859b264850b33264ca16684c9932c99334489123468cc99328d1a33264ca24488c993289122468d1993265122448d1a34489123468cc99328d1a33264ca24488c993289122468d1a244891a34664c99468d1993265122448d1a33264ca24488c993289122468d1a244891a34664c99468d19932651224464c994489123468d122448d1a33264ca244891a34664c99468d19932651224464c994489123468d122448d1a33264ca3468cc9932891223264ca244891a34664c994489123468d122448d1a33264ca3468cc993289122468d19932651224464c994489123468d122448d1a33264ca244891a34664c99468d19932651224464c994489123468d122448d1a33264ca3468cc9932891223264ca244891a34664c994489123468d122448d1a33264ca3468cc9932891223264ca244891a34689122468d19932651a34664c994489123468cc9932891223264ca244891a34689122468d19932651a34664c9944891193265122448d1a34489123468cc993289122468d19932651a34664c9944891193265122448d1a3408101f3e7cc993278f1e3264ca04080c9932810203c78f193265020407cf9f408101e3c78c993278f1e3264ca04080c9932810203c78f204080f9f3e64c993c78f1932650204078f1e3264ca04080c9932810203e7cfa04080f1e3c64c993e7cf9932650204064c99408101f3e7d0204078f1e3264ca04080f9f3e64c993e7cf9932650204064c99408101e3c790204078f1e3264c9f3e7cc9932810203264ca04080f9f3e64c99408101e3c79020407cf9f3264c9f3e7cc9932810203c78f1932650204064c99408101e3c79020407cf9f3264ca04080f1e3c64c993c78f1932650204064c99408101f3e7d020407cf9f3264c9e3c78c9932810203264ca04080f1e3c64c99408101f3e7d0204078f1e3264c9e3c78c9932810203264ca04080f9f3e810203c78f193264f9f3e64c99408101f3e7cc9932810203264ca04080f1e3c810203e7cf993264f9f3e64c9940810193265020407cf9f408101e3c78c9932810203e7cf993264f9f3e64c99408101932650204078f1e3264cb266c999b36cd932366d9993264f333c64c9964c99993265a2e687cf9f5cbd79f3e7cc993278f1e3264caf5eb8f9f3e64c995cc589932657af5c7cf9f5eb979e3c78c99326d99b3264cb264ccc9932c99b2666cdb364c8f1e6664c993cccf1932659326664c9964cd933366d9b2646cdb33264c9e3c78c9932bd7ae3264cb45cd0f9f3eb97af3e7cf9932657ae5e78f1e3264c9f3e7cc9932b98b13264caf5eb8f9f3ecd9323c799993264db33664c9964c9999326593364ccd9b5eb979f3e7cc993278f1e3264cae5ebcc9932c58ae3c78f3364c8d9b6664c993cccf1932659326664c9964cd9333c78c9932c993336ccdb266c999e3c64c993c7999932659b26464c995ebd71f3e7d7ae5e78f1e3264c9e3c78c9932b9a343264cb162b8f1e3cbd72f3e7cf993264f1e3c64c995cbd799326593364ccf1e66c991b36ccc99327999e3264cb264ccf1e6664c9966c99193265932666d99b64cd9333c78c993278f1e3264cae68d0c9932bd7ae3e7cfaf5cbcf1e3c64c995ebd71f3e7cc993278f1e3264caf5cbcc9932b9a343e7cfb266c999b3664c993c7999932659b26464c9964c999b666cc9932cd932366d9b264ccf333c64c99666cd9932659336464c995cbd79f3e7d7af5c78f1e3264c9f3e7cc9932c57313264cae68d0f9f3ebd7ae3e7cf993264f1e3c64c995eb97993265932666d99b64cd933366cc993278f333264cb364c999b3664c9964cd91932659b2646cdb364c999e6678c99327cf9f3264cb15cc4c9932b97af3e7cfaf5eb8f1e3c64c996678f1932659336464c9966c991e3ccd932666d99b3264c9e3c78c9932bd72f3264cae62c4f1e3cbd7ae3e7cf99326572f5e78f1e3264c9e3c78c9932d1a2e3264caf5cbcf9f3ec99333cccf19326599e3c64c9964cd91932659b2646cdb364c999b666cc9932ccf1e3264cb266c8c9932cd9323c799af5eb8f9f3e64c993c78f1932657ae5e64c995cc589e3c78c9932bd72f3e7cfae5ebcf1e3c64c993c78f193265a345c64c9966c991b36cd932667999e3264cb33c78c9932c99b23e7cf9932657af5c64c995eb979e3c797316278f1e3264caf5cbcf9f3e64c993c78f19326572f5e64c9962c571e3c797316278f1e3264c9f3e7cc9932bd7ae3264caf5cbcf1e3c64c9962c571e3c797ae5e7cf9f3264c9e3c78c9932b97af3264cb162b8f9f3ebd72f3e7cf993264f1e3c64c995cbd79f3e7cc9932b98b13264caf5eb8f9f3ebd72f3c78f193264f1e3c64c995cbd79932658b15c7cf9f5eb979f3e7cc9932bd72f3c78f193264f9f3e64c995cc589932657af5c7cf9f3264cae5ebcf1e3cc58ae3c78f193264f9f3e64c995eb979e3c78c9932bd72f3264cae62c4f1e3cbd7ae3e7cf993264f9f3e64c995eb9799326572f5e78f1e62c571e3c78c9932bd7ae3e7cf993264f1e3c64c995eb979932657316278f1e5ebd71f3e7cc993278f1e3264caf5cbcc9932b98b13e7cf9932657ae5e7cf9f5cbd79e3c78c99327cf9f3264cb162b8c9932b98b13e7cfaf5eb8f9f3e64c993c78f1932657ae5e7cf9f3264cb162b8c9932bd72f3e7cfae5ebcf1e3c64c993c78f1932657af5c64c9960b981f3e7d72f5e7cf9f3264cae5ebcf1e3c64c993e7cf9932658305c64c995eb979f3e7d72f5e7cf9f3264c9e3c78c9932bd7ae3264cb05cc0f9f3e64c995eb979f3e7d72f5e78f1e3264c9f3e7cc9932c182e3c78f1932658305c64c995eb979f3e7d72f5e78f1e3264cae5ebcf1e3c64c993c78f1932658305c64c995eb979f3e7cc9932c182e3e7cfaf5cbcf9f3e64c993c78f19326572f5e7cf9f3264cb05cc0c9932b97af3e7cfaf5eb8f1e3c64c993c78f19326572f5e64c9960c171f3e7d7ae5e7cf9f3264caf5eb8f1e3c64c993e7cf99326582e6064c995cbd79f3e7cc9932b97af3e7cfaf5eb8f1e3c64c993c78f19326582e6078f1e3264cb05cc0c9932b97af3e7cfaf5eb8f1e3c64c993a74e9b366cc9932204083264c881020c9932204081020419326440810204083a74e9b366cc9932204083264c8810204081064c991020419326440810204083a74e9b366cc993274e9d366cd9932644081064c991020419326440810204081eb4d13343cd0f2a687911e54d2d343ca9a1e687ad1e44d0f2a6969a1e68793343d68f2268a9a1e44d0f343ca8f5a68a9a1e687ad1e44d0f5a6899a1e68795343c88f2a6969a1e44d0f343ca8f5a6879534b4d0f343c99a1eb47913454d0f343c98f2a6969a1e54d0f343d68f26687ad344cd0f343ca9a1eb47933454d0f266879a1e547ad343ca9a5a6879a1e4c7ad344cd0f343ca9a1e4c79534b4d0f2a6879a1eb4793343ca9a5a6879a1e4cd0f5a3c99a2a68793343cd0f2a3d69a1e44d15343cd0f5a687951eb4d11343d69a1e687931e54d2d343cd0f223ca9a1e44d15343cd0f5a687951eb4d13343d69a1e687931e54d0f2268a9a1e687ad343ca8f5a6889a1e687951eb4d13343d69a1e687911e54d0f2268a9a1e687ad343ca8f5a6899a1eb4d0f343c98f2a687933454d0f343d68f2668a9a1e687ad343ca8f5a6899a1eb4d0f343c98f2a687933454d0f343d69a1e547ad344cd0f5a6879a1e4c79534b4d0f343c98f2a687933454d0f343d69a1e547ad344cd0f0e1c3860c1952a541830654a95070e1d52a541c3870c1832a54a83870e183060e1c3860c1952a541830654a95070e1d52a541c3870c183070e1c3060ca952a0c1832a54a83870e1830654a95070e1d52a541c3870c183070e1c3060ca952a12244aa54a83870ea952a0e1c38912243870e2448954a95070e1c48912a952a12244aa54a83870ea952a0e1c38912243870e2448954a9509122552a541c38754a95070e1c48912a952a0e1c38912243870e2448954a9509122552a541c3870c1832a54a83870ea952a0e1c3860c183870e1830654a95070e1c3060ca952a0c1832a54a83870ea952a0e1c3860c183870e1830654a95060c1952a541c38754a95070e1c3060ca952a0e1c3860c183870e1830654a95060c1952a541c38754a95070e1c489121c38712244aa54a848912a952a0e1c389122552a541c38754a95070e1c489121c38712244aa54a848912a952a0e1c3aa54a83870e244890e1c389122552a541c38712244aa54a848912a952a0e1c3aa54a83870e2448910204081020408101ce1c387031c0a7040810204081020408102040810204080a70e1c381ce0638204081020408102040810204081020408102040810204080e70e1c3818e05382040810204081020408102040810204053870e1c0e7031c387039c0c7029c3820408102040810204081020408102041c0a7039c3870e06102040810204081020408102040810204081020408102041c381ce063814e1c10204081020408102040810204081020e05381ce1c387030810204081020408102040810204081070e05381ce0938704081020408102040810204081020408102040810204081070e05381ce09387040810204081020408102040810204083814e073870e1c0c20408102040810204081020408102041c0c7029c3870e073814e073870e1c0c20408102040810204081020408102041c0c7029c3870e071020408102040810204081020408102029c3870e073824e08102040810204081020408102040810204081020408102029c3870e073824e0810204081020408102040810204081014e1c387039c0c704081020408102040810204081020408387031c0a7039c38204081020408102040810204081020408102040810204080a70e1c381ce063820408102040810204081020408102041c3818e05381ce1c0e1c3860c182850a183060a142870e1c2850a1c3870c183050a143870e183060e1c3860c182850a183060a142870e1c3060c142850e1c3850a143870e183060e1c3860c182850a1c3870c183050a143060c142850e1c3850a143870e183060e1c38e1c3962c583870e162c5870e1c58b161c3871c3872c58b03870e3870e0e1c38e1c3858b163870e162c5870e1c58b161c3871c387070e1c70e1cb162c1c3870b162c3870e3870e162c5870e1d62c581c3871c387070e1c70e1c2c58b0c1830c18303870e2c58b0e1c3860c183870e18306162c5870e1c3060c3060c0c1830b162c3870e2c58b0e1c3860c183870e18306162c5860c1860c181c387162c5870e1c3060c2c58b0e1c3860c183870e1830618306060c1858b161c3871c3870b162c3870e2c58b0e1c38e1c383870e3870e58b16070e1c70e1c2c58b1c3870b162c3870eb162c0e1c38e1c383870e3870e58b160e1c3858b161c387162c5870e1c70e1cb162c0e1c38e1c383870e3870e162c58e1c3858b161c387162c5870e1c3060c1c3870c1830b162c3060c3060c0e1c3860c1858b161c387162c5870e1c3060c1c3870c1830c18303060c3060c0e1c38b162c3870e183060e1c3860c1858b161c3870c1830c18303060c2c58b0e1c38b162c3870e18306468d1ab56ad1a3461c387468d1a3468d1a3468d1a356ad5a3468d1a346ad5ab468d1ab56ad1a3461c387468d1a3468c3870e8d1a3468d1a3468d1a346ad5ab468d1ab56ad1a3468d1a356ad5a3468c3870e8d1a3468d1a3468d1a346ad5ab0e1c3860c1952a541830654a95070e1d52a541c3870c1832a54a83870e183060e1c3860c1952a541830654a95070e1d52a541c3870c183070e1c3060ca952a0c1832a54a83870e1830654a95070e1d52a541c3870c183070e1c3060ca952a1c3872a54a83870ea952a0e1c38e1c383870e3870e54a95070e1c70e1ca952a1c3872a54a83870ea952a0e1c38e1c383870e3870e54a950e1c3952a541c38754a95070e1c70e1ca952a0e1c38e1c383870e3870e54a950e1c3952a541c3870c1832a54a83870ea952a0e1c3860c183870e1830654a95070e1c3060ca952a0c1832a54a83870ea952a0e1c3860c183870e1830654a95060c1952a541c38754a95070e1c3060ca952a0e1c3860c183870e1830654a95060c1952a541c38754a95070e1c70e1c1c3871c3872a54a870e1ca952a0e1c38e1c3952a541c38754a95070e1c70e1c1c3871c3872a54a870e1ca952a0e1c3aa54a83870e3870e0e1c38e1c3952a541c3871c3872a54a870e1ca952a0e1c3aa54a83870e3870e0e1c3860c1858b1618306162c5870e1c58b161c3870c1830b162c3870e183060e1c3860c1858b1618306162c5870e1c3060c2c58b0e1c38b162c3870e183060e1c3860c1858b161c3870c1830b162c3060c2c58b0e1c38b162c3870e183060c1832a54a83870ea952a0e1c3860c183870e1830654a95070e1c3060ca952a0c1832a54a83870ea952a0e1c3860c183870e2448954a9509122552a541c38754a95070e1c48912a952a0e1c38912243870e2448954a9509122552a541c38754a95070e1c489121c38712244aa54a848912a952a0e1c389122552a541c38754a95070e1c489121c38712244aa54a952a541c3870c183070e1c3060ca952a0c1832a54a83870e1830654a95070e1d52a541c3870c183070e1c3060ca952a12244aa54a83870ea952a0e1c38912243870e2448954a95070e1c48912a952a12244aa54a83870ea952a0e1c38912243870e2448954a9509122552a541c38754a95070e1c48912a952a0e1c38912243870e2448954a9509122552a541c38710204081020408102040810204081020e1c0a7039c0c70e1c3814e073818e1c1020408102040810204081020408102048912142850e1c3850a143870e244890e1c38912242850a1c38712244850a1448912142850e1c3850a143870e244890e1c38912242850a244890a142870e1c2850a1c38712244850a143870e244890e1c38912242850a244890a142870e1c2850a1c3870c183070e1c3060c142850c183050a143870e183060a142870e1c2850a1c3870c183070e1c3060c142850c183050a143870e142850e1c3860c183870e183060a142870e1c3060c142850c183050a143870e142850e1c3860c18408102040810204073870e1c1c7029c10204081020408102040810204081020408102040810204073870e1c1c7029c10204081020408107029c0e70e1c3818408102040810204081020408102040810204081020408107029c0e70e1c38182850a1c38712244870e1c489121428512244850a143870e244890a142870e1c2850a1c38712244870e1c489121428512244850a143870e142850e1c38912243870e244890a142870e1c489121428512244850a143870e142850e1c38912243870e183060a142860c182850a1c3870a142870e1c3060c142850e1c3860c183870e183060a142860c182850a1c3870a142870e1c3060c1c3870c183050a143060c142850e1c3860c182850a1c3870a142870e1c3060c1c3870c183050a14e073838e1c38702881020408102040810204081020408102040810204081020e073838e1c3870288102040810204080408100020408100040800200082040800102081020200081000410204040800408101000400102000810204002040800102081020200082040800102040800204001000410204000810204002040808002081020204002040808002000810204001000410204000810408101000410204001d5520c0020408080020008100040810200102040c0290408103a80010204001d3520c0010200080020810200040820408080020c0290408103a4001020404001000408002040810008102020008002041020404080040810002041020404080020008204080810004001020008002041020404080040810002041020404080020008100040010208102020400204080010204080040810002041020404080020008100040010208102020400204080010208102074400300a40800200081040810100040010208102520c0020408003a00810202040010004080020008104081010200102040008104081039e0018052081020204001000408002000810408129060010204001ce4c993254a953a74e952a54e9d3a850a13a74e993264a952a74e9d3264c952a54c993254a953a74e952a54e9d3a850a12a54a9d3a750a14274e9d3264c952a54c993254a953a74e993264a952a74e9d2a54a9d3a750a14274e9d3264c952a5489120f1225224481830f4891224489122448912240c3c3244891224482448f48912061e19224483c3064891224489122448912240c3c324489078912912240c187a44891224483c30648912244891224489122412247a4489030f0c9122448912061e19224483c30648912244891224489122412247a44891224482448f48912061e19224483c3064891224489030f0c9122448912244891224483c3064891209123d22448912240c187a4489030f0c9122448912244891224483c4894891209123d22448187864891224489122448912241e183244891224483c48948912060c3d22448187864891224489030f0c9122448912244891224483c48948912060c3d22448912240c187a4489030f0c9122448912244891224483c4894284d193264d204064c994080d21348501a40690a13264ca03480d214264c994284d193264d204064c994080d21348501a40690a13264ca14268c9932690203264ca0406909a4264c994080d21348501a40690a13264ca14268c9932690203264c9a40810a1348101a42690993264d214264c9940690213484c99328101a3264ca03480d2142690204284d193264d214264c9940690193264d20408509a4080d213484c9932690204284d19326509a4264c994080d19326501a40690a1406901a4284c99328509a3264c9a4080c99328101a426909932650203484d21406901a4284c99328509a3264c9a4080c99328101a42690a03480d214264c994284d193264d20408509a3264c9a4080c99328101a42690a03480d214264c994284d193264d204064c994080d21348501a40690a13264ca03480d214264c994284d193264d204064c994080d21348501a40690a13264ca14268c9932690203264ca0406909a4264c994080d21348501a40690a13264ca14268c9932690203485099326501a4064c99348102142690203484d213264c9a40810a13464c99426909932650203464c99406901a42850203484d213264c9a4284c993280d203264c9a40810a13464c99406901a4284d20408509a3264ca13484c99328101a3264c9a40810a1348101a42690993264d214264c9940690213484c99328101a3264ca03480d2142690204284d193264d214264c9940690193264d20408509a4080d213484c9932690204284d19326509a4264c994080d19326501a40690a134810214268c993284d213264ca04068c993280d203485099326501a40690a134810214268c993284d213264ca0406909a4264c994080d19326501a40690a134810214268c993280d20348509932650a13464c99348101932650203484d2134810214268c993284d213264ca04068c993280d20348509932650203484d21406901a4284c99328509a3264c9a40810a13464c99348101932650203484d21406901a4284c993280d20348509932650a13464c99348101932650203484d213264c9a40810a1348101a42690993264d214264c99406901a4284c993280d203264c9a40810a1348101a42690993264d214264c9940690193264d20408509a4080d213484c99328101a42690993264d214264c9940690193264d20408509a4488d23348cc9932691a33264ca23488c993269122468cd19326511a44691a334891234668c99328cd233264ca24468c993269122468cd22446919a4664c99348d199326511a448cd233264ca24468c993288d22348d19a44891a33464c99468cd193264d224464c994488d23348d11a44691a33264ca23488d234664c99468cd193264d224464c994488d23348d11a44691a33264ca34668c9932691223264ca2446919a4664c994488d23348d11a44691a33264ca34668c99326912234810214268c993284d213264ca04068c993280d20348509932650203484d21406901a4284c99328509a3264c9a4080c993280d20348509a40810a13464c9942690993265020348509a3264c9a4080c99328101a42690a03480d214264c993485099326501a4064c99348102142690203484d213264ca0406909a4264c993485099326501a4064c99348102142690203484d213264c9a4284c993280d203264c9a40810a13464c99348102142690203484d213264c9a4284c993280d203264c9a40810a1348101a42690993264d214264c99406901a4284c993280d203264c9a40810a1348101a426909932650203484d213264c9a4284c993280d203264c9a40810a13464c99406901a4284d20408509a3264ca13484c99328101a3264c9a40810a1348101a42690993264d214264c9940690213484c99328101a3264ca03480d2142690204284d193264d20408509a3264ca13484c99328101a3264ca03480d214264c99406901a4284d20408509a3264ca13484c99328101a4284d193264d204064c994080d21348501a40690a13264ca03480d214264c994284d193264d204064c994080d21348501a40690a13264ca14268c9932690203264ca0406909a4264c994080d21348501a40690a13264ca14268c9932690203485099326501a4064c99348102142690203484d213264ca0406909a4264c993485099326501a4064c99348102142690203484d213264c9a4284c993280d203264c9a40810a13464c99348102142690203484d213264c9a4284c993280d20426909932650203464c99406901a4284d20408509a3264c9a40810a13464c99426909932650203464c99406901a4284c993280d20348509a40810a13464c9942690993265020348509a3264c9a4080c99328101a42690a03480d214264c99426909932650203464c99406901a4284d20408509a3264ca03480d214264c994284d193264d204064c994080d213484c99328101a42690a03480d214264c994284d193264d20408509a3264c9a4080c99328101a42690a03480d214264c993e7cd193264d204064c994080d1e347901a4068f1e3264ca03480d1f3e64c993c78d193264d204064c994080d1e347901a4068f1e3264c9f3e68c9932690203264ca04068f1a3c64c994080d1e347901a4068f9f3264c9e3c68c9932690203264ca04068f9a3e80d203478f193264f9f3464c99348101a3e7cc993280d203264c9a4080f1e348101a3e68f993264f9f3464c9934810193265020347cd1f406901a3c78c99328101a3e68f993264d1f3e64c9940690193264d204078f1a3264c9a4080f1e348101a3c68f193264d1f3e64c99406901e3478c99328101a3264ca03480d1e3c690203e7cd193264d1f3e64c9940690193264d204078f1a4080d1e3478c9932690203e7cd193264f1a3c64c994080d19326501a4068f1e348101e3c68c99327cd1f3264ca04068c993280d20347cf99326501a4068f1e348101f3e68c99327cd1f3264ca04068c993280d20347cf9a4080f1e3464c993e68f993265020347cd1f3264ca04068c993280d203478f1a4080f9f3464c993264c9a3874e1b342041a10684193264d1c3c64c993a68e1a3878c993274d1c3264c9a3874e1b342041a10684193264d08102041a3264c883420c99322041a3264c883420d081064c99106841a1020d08102041a3264c883420c99322041a106841a1020c993270f1a3264c9a3874c993270e9a3668e193264e1d346cd1c106841a1020c993270f1a3264c9a38744083464c99342041932644083420d08106841a1020c993220d08342041932644083464c99342041932644083420d083264c88106841a1020d08342041932644083464c9934204081068c9932684083264c88106841a1020d0834204193264e1e3464c993470e993264e1d346cd1c106841a1020c993220d0834204193264e1e3464c993470e993264e1d346cd1c34204081068c993220d083264c881068c993220d083420419326441a106840834204081068c993220d083264c881068c993274d1c3470d9a10204083464c993c68e193264e1d3478d1c3264c9c3a68c993274d1c3470d9a10204083464c991e3cb0f2a3cc0f1e5478f1e3cb8f2c3c7971e5878f1e3ca8f1e607961e5478f2c3c78f1e547971e3ca8f2e3c78f1e587971e5878f1e3ca8f1e587951e6078f2a3c78f1e5c7961e3ca8f2e3c78f1e5878f303cb0f2a3c7961e3c78f2a3cb8f1e547971e3c78f2c3c7971e587951e3cb0f1e3c7951e5c7961e3c78f2a3cb8f1e547971e3c78f2c3c7971e587951e3cb0f1e3c7951e5c78f2a3cb8f1e3c7961e3cb8f2c3ca8f1e3c7971e587951e3cb0f1e3c7951e5c78f2a3cb8f1e3c7961e3ca8f2e3cb0f1e5c78f1e3cb0f2a3c7961e5478f1e3cc0f2c3ca8f1e3c7971e3ca8f2e3cb0f1e6078f1e3cb0f2a3c7961e5478f1e3cc0f1e547971e5878f2e3c78f1e587951e6078f1e3cb0f2a3c7961e5478f1e3cb8f1e547971e5878f2e3c78f1e587951e3cb0f2a3c78f1e5c78f2a3cb8f2c3c7951e3c78f2e3cb0f1e5c7961e3c78f2a3c7961e547971e3c78f2a3cb8f2c3c7971e3c78f2c3ca8f1e587951e3c78f2e3c7961e547971e3ca8f1e3c7971e5878f2e3cb0f1e3c7951e3c88f283c90f1e4078f1e3c90f223c7921e4c78f1e3c80f243c88f1e3c7941e3c88f203c90f1e4078f1e3c90f263c7921e4c78f1e3c80f1e447941e4878f203c78f1e487911e4078f1e3c90f263c7921e4478f1e3ca0f1e447901e4878f283c78f1e487911e3c90f263c78f1e5078f223c80f243c78f1e447941e4878f283c78f1e487931e3c90f223c78f1e4078f223c80f243c7941e3c78f243c88f1e487931e3c78f283c90f223c78f1e4078f223ca0f243c7941e3c78f243c98f1e407921e3c78f223c7921e4c7901e3c88f1e3c7941e4878f223c80f1e3c7921e3c80f243c98f1e4878f1e3c88f283c88f1e3c7941e4878f203c90f1e3c7911e3c90f263c80f1e4878f1e3c88f283c7911e4078f1e3c90f1e407921e4c78f1e3c90f263ca0f1e4478f1e3c80f243c7941e4878f1e3c88f1e507921e4c78f243c78f1e447901e3c88f283c78f1e487941e4878f1e3c88f1e487931e5078f223c78f1e407921e3c88f283c78f1e4878f283c90f263c7921e3c78f223c80f0a142870e1c3060c1c3870c183050a1470e1c142850e1c3860c182850a1c3870a142870e1c3060c1c3871c387050a1470e1c142850e1c3850a143870e183060e1c3860c182850a1c3871c387050a143060c142850e1c3850a143870e183060e1c3860c182850a3870e0a142870e1c2850a1c3870c183050a143870e183060e1c38e1c382850a183060a142870e1c2850a1c3870c183070e1c3060c142851c387050a143870e183060a142870e1c2850a1c3870c183070e1c70e1c142850e1c38e1c3868d1a183061a346870e1c68d1a1c3870c1830d1a343870e183060e1c38e1c3868d1a183061a346870e1c68d1a1c3871c387070e1c70e1c3468d0c1830d1a343870e3870e1a346870e1c68d1a1c3871c387070e1c3060c3468d0c1830d1a343870e3468d0e1c38e1c383870e3870e1a346870e1c3060c3468d1c3870d1a343870e3468d0e1c38e1c383060c3468d0e1c38d1a343870e183060e1c38e1c3868d1a1c3871c3870d1a343060c3468d0e1c38d1a343870e183060e1c38e1c3868d1a183061a346870e1c68d1a1c3871c3870d1a343870e3870e0e1c3860c1868d1a3870e1a346870e1c68d1a1c3871c387070e1c70e1c3468d0c1830d1a343870e3870e1a346870e1c68d1a1c3871c387070e1c3060c3468d0e1c3860c1858b162448918306070e1c58b161c3870c1830b162c3870e183060e1c389122460c1818306162c5870e1c58b161c3870c183070e1c3060c2c58b122448c18303870e18306162c5870e1c58b161c3870c183070e1c489123060c0c1830b162c3870e3060c0e1c38912243870e24489162c5870e1c3060c2c58b122448c18303870e2c58b0e1c38912243870e24489162c5860c1858b161c38718306070e1c489122c58b0e1c38912243870e18306162c589122460c181c387122448c18303870e2c58b0e1c3860c183870e18306162c5870e1c489123060c0c1830b162c3870e2c58b0e1c3860c183870e18306162c589122460c181c387162c5870e1c3060c2c58b0e1c3860c183870e2448918306060c1858b161c38718306070e1c489121c387122448b162c3060c2c58b0e1c389122460c181c387162c5870e1c489121c3870c1830b162c3060c2c58b0e1c38c18303870e244890e1c389122458b161c3870c1830b162c489123060c0e1c38b162c3870e2448914285070e1c3060c1c3870c1830a1428489122850a0e1c3860c1850a141c38714285070e1c3060c1c387122448a1428489122850a0e1c38a14283870e183060e1c3860c1850a141c387122448a14283060c2850a0e1c38a14283870e183060e1c389122450a141830614285070e1c50a141c387122448a14283870e244890e1c3860c1850a142448914285070e1c50a141c38712244870e1c489122850a0c1830a14283870e2448914285070e1c50a141c38712244870e1c3060c2850a0e1c3860c1850a142448914285070e1c50a141c3870c1830a14283870e183060e1c389122450a141830614285070e1c50a141c3870c183070e1c3060c2850a122448a14283870e1830614285070e1c50a141c3870c183070e1c489122850a0c1830a14283870e2850a0e1c38912243870e2448914285070e1c3060c2850a122448a14283870e2850a0e1c38912243870e2448914285060c1850a141c38714285070e1c489122850a0e1c38912243870e183061428509122450a141c3871020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102048912142850e1c388102040810204080e1c3860c182850a1c3870c183050a1448912142850e1c3881020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204070e1c3060c1428512244850a143870e244890a142870e1c408102040810204070e1c3060c142850408103000000006000030010002040818000081020010000060010204000030408100060020000100000000182040818000081020010002040818000000030000180080010204100000000182040800300081020000182040800300100000600000000c102040008004081000004102040008002000020408003000c000020000000041020400080040810000041020400080020000300000000608102000400204080000200080040810000041020400180060000100000000208102000c00400001020400003040810400001020400003000c00204080000600200001000300001020400003040810300001020400003000c0000600200000810200001820408200000000304081030000102040000300100000800180000810200000820408080000810200000800200003000c0000408100000400100081020200002040800100081020600000000c003000c0000408100000410204040000408100000400100081020600000000c0000200080040810100001020400080⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid 720 r := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_37 : ∀ i ∈ List.range' 37 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_74 : ∀ i ∈ List.range' 74 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_111 : ∀ i ∈ List.range' 111 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_148 : ∀ i ∈ List.range' 148 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_185 : ∀ i ∈ List.range' 185 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_222 : ∀ i ∈ List.range' 222 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_259 : ∀ i ∈ List.range' 259 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_296 : ∀ i ∈ List.range' 296 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_333 : ∀ i ∈ List.range' 333 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_370 : ∀ i ∈ List.range' 370 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_407 : ∀ i ∈ List.range' 407 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_444 : ∀ i ∈ List.range' 444 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_481 : ∀ i ∈ List.range' 481 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_518 : ∀ i ∈ List.range' 518 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_555 : ∀ i ∈ List.range' 555 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_592 : ∀ i ∈ List.range' 592 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_629 : ∀ i ∈ List.range' 629 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_666 : ∀ i ∈ List.range' 666 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_703 : ∀ i ∈ List.range' 703 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_740 : ∀ i ∈ List.range' 740 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_777 : ∀ i ∈ List.range' 777 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_814 : ∀ i ∈ List.range' 814 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_851 : ∀ i ∈ List.range' 851 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_888 : ∀ i ∈ List.range' 888 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_925 : ∀ i ∈ List.range' 925 37, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test720_962 : ∀ i ∈ List.range' 962 14, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine h bad step720 (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 976 at hi
  by_cases h0 : i < 37
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h37 : i < 74
  · exact test720_37 i (by simp only [List.mem_range'_1]; omega)
  by_cases h74 : i < 111
  · exact test720_74 i (by simp only [List.mem_range'_1]; omega)
  by_cases h111 : i < 148
  · exact test720_111 i (by simp only [List.mem_range'_1]; omega)
  by_cases h148 : i < 185
  · exact test720_148 i (by simp only [List.mem_range'_1]; omega)
  by_cases h185 : i < 222
  · exact test720_185 i (by simp only [List.mem_range'_1]; omega)
  by_cases h222 : i < 259
  · exact test720_222 i (by simp only [List.mem_range'_1]; omega)
  by_cases h259 : i < 296
  · exact test720_259 i (by simp only [List.mem_range'_1]; omega)
  by_cases h296 : i < 333
  · exact test720_296 i (by simp only [List.mem_range'_1]; omega)
  by_cases h333 : i < 370
  · exact test720_333 i (by simp only [List.mem_range'_1]; omega)
  by_cases h370 : i < 407
  · exact test720_370 i (by simp only [List.mem_range'_1]; omega)
  by_cases h407 : i < 444
  · exact test720_407 i (by simp only [List.mem_range'_1]; omega)
  by_cases h444 : i < 481
  · exact test720_444 i (by simp only [List.mem_range'_1]; omega)
  by_cases h481 : i < 518
  · exact test720_481 i (by simp only [List.mem_range'_1]; omega)
  by_cases h518 : i < 555
  · exact test720_518 i (by simp only [List.mem_range'_1]; omega)
  by_cases h555 : i < 592
  · exact test720_555 i (by simp only [List.mem_range'_1]; omega)
  by_cases h592 : i < 629
  · exact test720_592 i (by simp only [List.mem_range'_1]; omega)
  by_cases h629 : i < 666
  · exact test720_629 i (by simp only [List.mem_range'_1]; omega)
  by_cases h666 : i < 703
  · exact test720_666 i (by simp only [List.mem_range'_1]; omega)
  by_cases h703 : i < 740
  · exact test720_703 i (by simp only [List.mem_range'_1]; omega)
  by_cases h740 : i < 777
  · exact test720_740 i (by simp only [List.mem_range'_1]; omega)
  by_cases h777 : i < 814
  · exact test720_777 i (by simp only [List.mem_range'_1]; omega)
  by_cases h814 : i < 851
  · exact test720_814 i (by simp only [List.mem_range'_1]; omega)
  by_cases h851 : i < 888
  · exact test720_851 i (by simp only [List.mem_range'_1]; omega)
  by_cases h888 : i < 925
  · exact test720_888 i (by simp only [List.mem_range'_1]; omega)
  by_cases h925 : i < 962
  · exact test720_925 i (by simp only [List.mem_range'_1]; omega)
  exact test720_962 i (by simp only [List.mem_range'_1]; omega)
private def keys7920 : Keys := ⟨0,13,0x0⟩
private def rows7920 : List Rule := [
  .prime 331,
  .pool ⟨13,8,[13,2],[3,5,7],23,0x5335e⟩,
  .pool ⟨13,8,[13,2],[3,5,7],335,0x104301644b10062c65308e1715013908b528665b0491a9422b427715070ad251818f730cd13d2d73de⟩,
  .prime 23,
  .pool ⟨13,8,[13,2],[3,5,7],199,0x12195692276883181d7e3d85d45e438147e73ee91bb69567b6⟩,
  .pool ⟨17,10,[17,2,5],[3,7],89,0x1b3c3b902a6b59502770f36⟩,
  .pool ⟨13,8,[13,2],[3,5,7],623,0x4214906249711284c60832b4203488571f42d54950e089b750d101f308180366e47aa7419b27321922750a8118183de3e7205f3474106ab0e54d143c0511e6c3db9212ed98d6a7512d38f4d3b5e⟩,
  .pool ⟨13,8,[13,2],[3,5,7],991,0x131b439a354b83c90a7235ded10eb08255893f490a23e7e9f25744ec8b549008622790c60ebf3093509c5d1bad3efd87aa0c627f6170fdb481cf6761d655559479190c7ed240f17901b9cfaa1e40834a2745c6f536f3028f9cf61bb9eff6d52ec8dd15b068183baf6d036e55bef28f748453b1af6c3e2d53a63d2736⟩,
  .pool ⟨13,8,[13,2],[3,5,7],881,0x1b3d2f9823bf1e41356a3ef95eb58159289de2207ab7ba19dba73cde50599b4862425e8ab0207111ab376cba2e301e0b8e7b61e96e82ceb5cd05da5e1b79c741e031d174dbb3562238103545e909184b666829ecf3976e6177b578111ee4526a06b5ea7df15ab209e3f71067d2f36⟩,
  .pool ⟨17,10,[17,2,5],[3,7],1191,0x116032c100b09a44200108a0196992034584004030594994102d26d829249005a2032d124044060041a4522c22096932102510da6092ca2904d86496086410132c80d105b4da2534930516124112804016506c82136590cb0490c04d228824b0806510d321204b2982914834db0d94d925021b2816d24922c00902d344244161b4db4c141b24204368a65b69948260b65821b0536⟩,
  .pool ⟨17,10,[17,2,5],[3,7],161,0x1b383e113ae108092a62b5195240421d7221f0736⟩,
  .pool ⟨17,10,[17,2,5],[3,7],871,0x120914924631961c25791b47866842b00d323f82179a306fc02869813158da1110e20a081feed54c536ec2dc1f153daeb05409952d93d4164a5663d5b28843470744b80915cc548007afada8e77724e1735e68e9f409b3a417ae03330bf29de89e15272151c786731db2d74fb6⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],335,0x104301644b10062c65308e1715013908b528665b0491a9422b427715070ad251818f730cd13d2d73de⟩]
private def step7920 : Stage := ⟨720,11,keys720,keys7920,rows7920,4,0x141082141430146161231442141231011141430211241a31411671731611441210611241408311b610173121702143151168163141120143121108161126021231810181431811221631411041431810481211401221414311471b12310421417306111414312112410314118218312114412062117410153114103121164063141162123121144101261184041231120121831216181431211021231410241431601421711011571414311481212304421416318114310114616104112814143114216173144714103121114043161184163141122103121144081281180141631108161231212161431710721a3140124171104141a31056161231212121431601681231011241430511421711411221414311481610314481402316111014318112418314116602318114012124210183121104143121164123141120123151104171621084141631188121231802161431011261230411541431811421211411261410311421802314212314116410316114218114116814043114210163144704123121114143161150163141102123121044181850124141231122191a3101612143021183160144151201124141631188181630218121431811261031411241431211461201411661014311420616314401412312111414316110412314102a191140121631405141231611141431a1024123140188163101144121621124141230162161231812121031211260531411541431611471011411220414351504312112012314118414312114202114117014143110612123144214163181014143120164123101186123061144181821184141231162121031711630411221631211441217a11741410311221808318161014312116217314116404312114016114110214143104212183144814163120114143101124140831611241731211b610315116702144112018163110816143121214143141086123140146123101142141021124141431167171a3144412103161173061142141121124141431182181031444120631211101531211741231811260231811201814411041216310481214318121414314012b123101147141024121231142171431607141431011521230411481631811421411211641410311621206314441012312110412316118418312112012312110618144408123121114163181180123121108163171072161440124121a311461614310181414304112617314114210312114714116118414043112210163146103141148123161148140181124101431166021831440121231811141a3171104123121056163160162121401124181231142171430512141431411231011221614411541612301421214318161410314112802314114218312114210112116404143112012123140417163151114163121084123180188121102121631444181831210141231501241a3101122193021186121441164121231142181031618140431411601631411421231211470411611501414361014314116616314114202312114014116110414143102a1912314441512316011416310112416302118818318112812144112416103114612043121123181162163121122121041154160531147101431612041431411221631411401231611051411a102414143018816123144412163101114123021124120164141431186121231044181830611141231211841031711621231211251504411841012311420214312101414314117212314110616318104214114016143121214143141102183141042163120148141101124141431122161630444121731211141031a11740831811221831211661014411640217314210183121104143121164123141120123151104171621084141631188121231802161431011261230411541431811421211411261410311421802314212314116410316114218114116814043114210163144704123121114143161150163141102123121044181850124141231122191a3101612143021183160144151201124141631188181630218121431811261031411241431211461201411661014311420616314401412312111414316110412314102a191140121631405141231611141431a1024123140188163101144121621124141230162161231812121031211260531411541431611471011411220414351504312112012314118414312114202114117014143110612123144214163181014143120164123101186123061144181821184141231162121031711630411221631211441217a11741410311221808318161014312116217314116404312114016114110214143104212183144814163120114143101124141082141430146161231442141231011141430211241a31411671731611441210611241408311b610173121702143151168163141120143121108161126021231810181431811221631411041431810481211401221414311471b12310421417306111414312112410314118218312114412062117410153114103121164063141162123121144101261184041231120121831216181431211021231410241431601421711011571414311481212304421416318114310114616104112814143114216173144714103121114043161184163141122103121144081281180141631108161231212161431710721a3140124171104141a310561612312121214316016812310112414305114217114112214143114816103144814023161110143181124183141166023181140121231011221614411541612301421214318161410314112802314114218312114210112116404143112012123140417163151114163121084123180188121102121631444181831210141231501241a3101122193021186121441164121231142181031618140431411601631411421231211470411611501414361014314116616314114202312114014116110414143102a1912314441512316011416310112416302118818318112812144112416103114612043121123181162163121122121041154160531147101431612041431411221631411401231611051411a102414143018816123144412163101114123021124120164141431186121231044181830611141231211841031711621231211251504411841012311420214312101414314117212314110616318104214114016143121214143141102183141042163120148141101124141431122161630444121731211141031a1174083181122183121166101441164021731140831611241731211b610315116702144112018163110816143121214143141086123140146123101142141021124141431167171a3144412103161173061142141121124141431182181031444120631211101531211741231811260231811201814411041216310481214318121414314012b123101147141024121231142171431607141431011521230411481631811421411211641410311621206314441012312110412316118418312112012312110618144408123121114163181180123121108163171072161440124121a311461614310181414304112617314114210312114714116118414043112210163146103141148123161148140181124101431166021831440121231811141a31711041231210561631601621214011241812311421714305121414314112216314114012316110514118102414143018816123144412163101114123021124123171162163121122121041184160831147101431612041431411231211251504411541012311420214312101414314117212314110616318104214112016414143115612123104417153061114123121184103181162121122161630444121831211141031a11740731511221731211661014411640217311401614312121414314110215314104216312014714110112414143214143141076123140146123101142141021124141431167171a31444121031611140731611241731211b610318116802144112018163110516143121123181126023151120151441104121631047121431512141431401281231011481730611421411211241414311921710314441206312111018312118412116414103116212063144410123121104123161174153121120123121106151441024121231142181431607141431011521230411471631711421411461614310151414304112617314114210312114814116118414043112210163144407123121114163171150123121108163181082161440124121a3114183181104123121056163160162121401124171231142171430512141431411261031411481231611471401a1124101431166021a3144012123181153121142101121164041431120121231404171631511141631210741231701571231011221614411841612301421214318161410314112c02314114214116412123114215103161a1404314116016314114212312114804116115014143110212163144417173121014123150124183101122183021186121444181231601141631011241630211751731a11271214411241610311461204312161014314116616314114202312114014116110414143102a19123141621612317121210312112608314118414316114710114112204143114012163140514123161114143181024123140188163101144121621124141230141431201641231011561230611441715211841412311621210318151504312112012314115414312114202114117014143110612123144214163181043121140161141102141431042121531447141631201141431011241630411221631211441218a1174141031122170731516101431211621731411640611241407311b610173121802143181168163141120143121105161141072141430146161231442141231011141430211241a31411671731611441210421417306111414312112410314119217312114412062118410183112602123181015143151122163141104143151047121140122141431148181231021231410241431601421811011571414311471212304421416317111410312116406314116212312114410126117404123112012153121615143121103121144071271150141631108161231212161431810821a314012414310114616104112514143114216173144814103121114043161184163141122101148161031447140231611101431a11241a314116602318114012128110414183105616123121212143160167123101124143051142171141122141432161431011261230411841431811421211411261410311421c023144210153121104143121164123141120123151104171621074141631157121231701631411021231210441717501241412311221818310161214302118212314116410316114215114116a140431142101631448041231211141431611501411661014311420616314401412312111414316110412314102a193160144181201124141631175171630217121431a11261031411241431211461201461614310151414304112617314114210312114814116118414043112210163144407123121114163171150123121108163181082161440124121a3114183181104123121056163160162121401124171231142171430512141431411261031411481231611471401a1124101431166021a3144012123181153121142101121164041431120121231404171631511141631210741231701571231011221614411841612301421214318161410314112c02314114214116412123114215103161a1404314116016314114212312114804116115014143110212163144417173121014123150124183101122183021186121444181231601141631011241630211751731a11271214411241610311461204312161014314116616314114202312114014116110414143102a1912314216314114012316110514118102414143018816123144412163101114123021124123171162163121122121041184160831147101431612041431411231211251504411541012311420214312101414314117212314110616318104214112016414143115612123104417153061114123121184103181162121122161630444121831211141031a11740731511221731211661014411640217311401614312121414314110215314104216312014714110112414143214143141076123140146123101142141021124141431167171a31444121031611140731611241731211b610318116802144112018163110516143121123181126023151120151441104121631047121431512141431401281231011481730611421411211241414311921710314441206312111018312118412116414103116212063144410123121104123161174153121120123121106151441024121231142181431607141431011521230411471631711421413121144071271150141631108161231212161431810821a314012414310114616104112514143114216173144814103121114043161184163141122101148161031447140231611101431a11241a314116602318114012128110414183105616123121212143160167123101124143051142171141122141432161431011261230411841431811421211411261410311421c023144210153121104143121164123141120123151104171621074141631157121231701631411021231210441717501241412311221818310161214302118212314116410316114215114116a140431142101631448041231211141431611501411661014311420616314401412312111414316110412314102a193160144181201124141631175171630217121431a11261031411241431211461201621612317121210312112608314118414316114710114112204143114012163140514123161114143181024123140188163101144121621124141230141431201641231011561230611441715211841412311621210318151504312112012314115414312114202114117014143110612123144214163181043121140161141102141431042121531447141631201141431011241630411221631211441218a1174141031122170731516101431211621731411640611241407311b610173121802143181168163141120143121105161141072141430146161231442141231011141430211241a3141167173161144121042141730611141431211241031411921731211441206211841018311260212318101514315112216314110414315104712114012214143114818123102123141024143160142181101157141431147121230442141631711141031211640631411621231211441012611740412311201215312161514312110⟩
set_option maxHeartbeats 5000000 in
private theorem valid7920 : ∀ r ∈ rows7920, Valid 7920 r := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_1 : ∀ i ∈ List.range' 1 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_2 : ∀ i ∈ List.range' 2 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_3 : ∀ i ∈ List.range' 3 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_4 : ∀ i ∈ List.range' 4 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_5 : ∀ i ∈ List.range' 5 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_6 : ∀ i ∈ List.range' 6 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem test7920_7 : ∀ i ∈ List.range' 7 1, ∀ x y z : Fin 11, Test step7920 i x y z := by decide +kernel
private theorem run7920 {n a b c : ℕ} (h : H n a b c) (bad : ¬Target a b c) (old : Match 720 a b c keys720) : Match 7920 a b c keys7920 := by
  apply refine h bad step7920 (by decide) (by decide) valid7920 _ old
  intro i hi
  change i < 8 at hi
  by_cases h0 : i < 1
  · exact test7920_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h1 : i < 2
  · exact test7920_1 i (by simp only [List.mem_range'_1]; omega)
  by_cases h2 : i < 3
  · exact test7920_2 i (by simp only [List.mem_range'_1]; omega)
  by_cases h3 : i < 4
  · exact test7920_3 i (by simp only [List.mem_range'_1]; omega)
  by_cases h4 : i < 5
  · exact test7920_4 i (by simp only [List.mem_range'_1]; omega)
  by_cases h5 : i < 6
  · exact test7920_5 i (by simp only [List.mem_range'_1]; omega)
  by_cases h6 : i < 7
  · exact test7920_6 i (by simp only [List.mem_range'_1]; omega)
  exact test7920_7 i (by simp only [List.mem_range'_1]; omega)

/-- In a prime-successor solution with the sixth offset supported on 2, 3 and 7,
the exponents force this offset to be six times a twelfth power. -/
theorem exponents {n a b c : ℕ} (hn : 1600<n) (d5 : 5∣n) (pp : (n+1).Prime)
    (sol : Erdos889.v_l 1 n=1) (shape : n+6=2^a*3^b*7^c) (ha : 0<a) (hb : 0<b)
    (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra bad
  have h : H n a b c := ⟨shape,ha,hb,hc,hn,d5,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  have h7920 := run7920 h bad h720
  obtain ⟨i,hi,_⟩ := h7920
  exact Nat.not_lt_zero i hi

end Erdos889.PrimeSixth

namespace Erdos889.PrimeSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem sixth_shape {n : ℕ} (d : 30∣n) (h7 : 7∣n+6) (sol : v_l 1 n=1) :
    ∃ a b c : ℕ, n+6=2^a*3^b*7^c ∧ 0<a ∧ 0<b ∧ 0<c := by
  let N := n+6
  have pos : 0<N := by dsimp [N]; omega
  have support (p : ℕ) (pp : p.Prime) (hd : p∣N) : p=2 ∨ p=3 ∨ p=7 := by
    by_cases low : p≤6
    · have small : ∀ t : Fin 7, t.val.Prime → t.val=2 ∨ t.val=3 ∨ t.val=5 := by decide
      rcases small ⟨p,by omega⟩ pp with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · change p∣n+6 at hd
        change p=5 at h
        rw [h] at hd
        omega
    · by_contra! bad
      exact two_primes (by decide : 0<6) pp (by decide : Nat.Prime 7) bad.2.2
        (by omega) (by decide) hd h7 sol
  let a := N.factorization 2
  let M := N/2^a
  have fac : 2^a*M=N := Nat.ordProj_mul_ordCompl_eq_self _ _
  have mp : 0<M := Nat.ordCompl_pos 2 pos.ne'
  have no2 : ¬2∣M := Nat.not_dvd_ordCompl Nat.prime_two pos.ne'
  obtain ⟨b,c,h⟩ := two_factor_support mp Nat.prime_three (q:=7) (by
    intro r pp hd
    have dv : r∣N := fac ▸ dvd_mul_of_dvd_right hd _
    exact (support r pp dv).resolve_left (by rintro rfl; exact no2 hd))
  have eq : n+6=2^a*3^b*7^c := by change N=_; rw [←fac,h,mul_assoc]
  have da : 2∣n+6 := by omega
  have db : 3∣n+6 := by omega
  rw [eq] at da db h7
  have ap : 0<a := by
    by_contra! z
    rw [show a=0 by omega,pow_zero,one_mul] at da
    rcases Nat.prime_two.dvd_mul.mp da with h|h
    · exact (by decide : ¬2∣3) (Nat.prime_two.dvd_of_dvd_pow h)
    · exact (by decide : ¬2∣7) (Nat.prime_two.dvd_of_dvd_pow h)
  have bp : 0<b := by
    by_contra! z
    rw [show b=0 by omega,pow_zero,mul_one] at db
    rcases Nat.prime_three.dvd_mul.mp db with h|h
    · exact (by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow h)
    · exact (by decide : ¬3∣7) (Nat.prime_three.dvd_of_dvd_pow h)
  have cp : 0<c := by
    by_contra! z
    rw [show c=0 by omega,pow_zero,mul_one] at h7
    have pp : Nat.Prime 7 := by decide
    rcases pp.dvd_mul.mp h7 with h|h
    · exact (by decide : ¬7∣2) (pp.dvd_of_dvd_pow h)
    · exact (by decide : ¬7∣3) (pp.dvd_of_dvd_pow h)
  exact ⟨a,b,c,eq,ap,bp,cp⟩

private theorem close_six {n a b c : ℕ} (big : 1600<n) (eq : n+6=2^a*3^b*7^c)
    (ha : a%12=1) (hb : b%12=1) (hc : c%12=0) (sol : v_l 1 n=1) : False := by
  let z := 2^(a/12)*3^(b/12)*7^(c/12)
  have shape : n+6=6*z^12 := by
    change n+6=6*(2^(a/12)*3^(b/12)*7^(c/12))^12
    have A : a=a/12*12+1 := by omega
    have B : b=b/12*12+1 := by omega
    have C : c=c/12*12 := by omega
    calc
      n+6=2^a*3^b*7^c := eq
      _=2^(a/12*12+1)*3^(b/12*12+1)*7^(c/12*12) :=
        congrArg₂ (·*·) (congrArg₂ (·*·) (congrArg (2^·) A) (congrArg (3^·) B)) (congrArg (7^·) C)
      _=_ := by simp only [mul_pow,←pow_mul,pow_succ]; ring
  have hi : 1<z := by
    by_contra! low
    have t := Nat.pow_le_pow_left low 12
    omega
  exact no_twelfth (by decide) (by decide) hi shape sol

/-- At a prime successor, every sufficiently large solution divisible by 30 is divisible by 210. -/
theorem prime_multiple_of_210 {n : ℕ} (big : 1000000000000<n) (d : 30∣n)
    (prime : (n+1).Prime) (sol : v_l 1 n=1) : 210∣n := by
  suffices 7∣n by omega
  by_contra miss
  have hit := only_sixth_offset big d prime sol miss
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := sixth_shape d hit sol
  obtain ⟨ra,rb,rc⟩ := Erdos889.PrimeSixth.exponents (by omega) (by omega) prime sol eq ha hb hc
  exact close_six (by omega) eq ra rb rc sol
end Erdos889.PrimeSeven

namespace Erdos889.PrimeSeven
theorem witness {p : ℕ} (prime : p.Prime) (high : 1000000000001<p)
    (bound : 2^(2^21)<p ∨ (30∣p-1 ∧ ¬210∣p-1)) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p+d ∧ s∣p+d := by
  by_contra none
  have sol := Erdos889.Missing.predecessor_solution_of_missing (by omega : 1<p) none
  rcases bound with large|⟨d,missing⟩
  · exact (Nat.not_lt_of_ge (Nat.le_sub_one_of_lt large)) (Erdos889.effective_binary_cutoff sol)
  · have eq : p-1+1=p := by omega
    exact missing (prime_multiple_of_210 (by omega) d (eq.symm ▸ prime) sol)
end Erdos889.PrimeSeven

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H1 := by
  refine ⟨max 1000000000001 (2^(2^21)),?_⟩
  intro p pp _ high _ _
  exact Erdos889.PrimeSeven.witness pp (lt_of_le_of_lt (Nat.le_max_left _ _) high)
    (Or.inl (lt_of_le_of_lt (Nat.le_max_right _ _) high))
